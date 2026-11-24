import RHDirect.Stage12SchurWeylLattices
import RHDirect.Stage10GeometryOfNumbers
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# RHDirect.Stage14M2_TotallyPosTrace

Field-2 Package M2 (Wave 1, Module 3 of 6): **Totally Positive Elements, AM–GM Trace Bounds,
Different-Ideal Dual Trace Integrality, Archimedean Frame Degree (`q_frame_degree`), and
Monomial Lattice `muMax` Upper Bounds (`monomial_lattice_muMax_le`)** in pure Mathlib `v4.33.1`.

Zero `sorry`, zero custom `axiom`s, zero `native_decide`, zero `opaque`.

## Contents

1. **Totally Positive Elements & AM–GM Trace Inequality**:
   - `IsTotallyPositive`, `TotallyPositiveElement`, real-embedding equivalence for
     `[IsTotallyReal F]`, closure under `1`, `+`, `*`, `⁻¹`, positive rational scaling, powers,
     positivity of norm and trace, and `am_gm_totally_positive_trace`:
     `[F : ℚ] * (N_{F/ℚ}(α))^{1/[F : ℚ]} ≤ Tr_{F/ℚ}(α)`.
2. **CM Hermitian Forms, Different Ideal, & `totally_positive_trace_ge_of_norm_discr`**:
   - `CMHermitianForm`, `dualSub`, `TrDual`, `LatT`, `bIdeal`, `one_le_norm_discr`, and
     `totally_positive_trace_ge_of_norm_discr` (`Tr_{E/ℚ}(α) ≥ [E : ℚ] * (q * |Δ_E|^2)^{-1/[E : ℚ]}`).
3. **Archimedean Gram Determinants & `q_frame_degree`**:
   - `majAt`, `gramJ`, `gramJ_self_det`, realification determinant `|det_R(M)| = ‖det M‖^2`,
     `NumberFieldHLat` frame transport, and `q_frame_degree`.
4. **Monomial Lattices, Orthogonal Decomposition & `monomial_lattice_muMax_le`**:
   - `muOK`, `muMaxOK`, `MonomialFrame`, single-line and orthogonal direct-sum `muMaxOK` bounds,
     fractional-ideal rescaling, and `monomial_lattice_muMax_le`.
-/

noncomputable section

open Module Submodule Finset Real NumberField IsDedekindDomain FractionalIdeal Matrix
open scoped BigOperators Matrix ComplexOrder InnerProductSpace nonZeroDivisors MeasureTheory Pointwise

namespace RHDirect.Stage14M2_TotallyPosTrace

/-! ## Section 1: Totally Positive Elements & AM–GM Trace Inequality -/

section TotallyPositive

/-- Predicate asserting that `α : F` is totally positive: every complex embedding `φ : F →+* ℂ`
maps `α` to a strictly positive real number. -/
def IsTotallyPositive {F : Type*} [Field F] [NumberField F] (α : F) : Prop :=
  ∀ φ : F →+* ℂ, ∃ c : ℝ, 0 < c ∧ φ α = (c : ℂ)

/-- Concrete bundled **totally positive element** in a number field `F`. -/
structure TotallyPositiveElement (F : Type*) [Field F] [NumberField F] where
  val : F
  pos_emb : IsTotallyPositive val

instance {F : Type*} [Field F] [NumberField F] : Coe (TotallyPositiveElement F) F :=
  ⟨TotallyPositiveElement.val⟩

theorem isTotallyPositive_iff_re_pos_im_zero {F : Type*} [Field F] [NumberField F] (α : F) :
    IsTotallyPositive α ↔ ∀ φ : F →+* ℂ, 0 < (φ α).re ∧ (φ α).im = 0 := by
  constructor
  · intro h φ
    obtain ⟨c, hc, he⟩ := h φ
    rw [he, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨hc, rfl⟩
  · intro h φ
    obtain ⟨hre, him⟩ := h φ
    refine ⟨(φ α).re, hre, ?_⟩
    apply Complex.ext <;> simp [him]

theorem isTotallyPositive_of_real_embeddings {F : Type*} [Field F] [NumberField F]
    [IsTotallyReal F] (α : F) (h : ∀ σ : F →+* ℝ, 0 < σ α) :
    IsTotallyPositive α := by
  intro φ
  have hreal : NumberField.ComplexEmbedding.IsReal φ :=
    NumberField.InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal (NumberField.InfinitePlace.mk φ))
  have him : ∀ x : F, (φ x).im = 0 := fun x =>
    Complex.conj_eq_iff_im.mp (by
      simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using
        RingHom.congr_fun (NumberField.ComplexEmbedding.isReal_iff.mp hreal) x)
  let σ : F →+* ℝ :=
    { toFun := fun x => (φ x).re
      map_one' := by simp
      map_mul' := fun x y => by
        rw [map_mul, Complex.mul_re, him x, him y, mul_zero, sub_zero]
      map_zero' := by simp
      map_add' := fun x y => by rw [map_add, Complex.add_re] }
  refine ⟨σ α, h σ, ?_⟩
  apply Complex.ext
  · rfl
  · simp [him α]

theorem isTotallyPositive_iff_real_embeddings {F : Type*} [Field F] [NumberField F]
    [IsTotallyReal F] (α : F) :
    IsTotallyPositive α ↔ ∀ σ : F →+* ℝ, 0 < σ α := by
  constructor
  · intro h σ
    obtain ⟨c, hc, he⟩ := h ((Complex.ofRealHom).comp σ)
    simp only [RingHom.comp_apply] at he
    have hc' : σ α = c := Complex.ofReal_injective he
    rwa [hc']
  · exact isTotallyPositive_of_real_embeddings α

namespace TotallyPositiveElement

variable {F : Type*} [Field F] [NumberField F]

@[ext]
theorem ext {α β : TotallyPositiveElement F} (h : α.val = β.val) : α = β := by
  cases α; cases β; simp only [mk.injEq]; exact h

/-- Multiplicative identity `1` as a totally positive element. -/
def one (F : Type*) [Field F] [NumberField F] : TotallyPositiveElement F where
  val := 1
  pos_emb := fun φ => ⟨1, one_pos, by simp⟩

/-- Sum of two totally positive elements. -/
def add (α β : TotallyPositiveElement F) : TotallyPositiveElement F where
  val := α.val + β.val
  pos_emb := fun φ => by
    obtain ⟨a, ha, hae⟩ := α.pos_emb φ
    obtain ⟨b, hb, hbe⟩ := β.pos_emb φ
    refine ⟨a + b, add_pos ha hb, ?_⟩
    rw [map_add, hae, hbe, Complex.ofReal_add]

/-- Product of two totally positive elements. -/
def mul (α β : TotallyPositiveElement F) : TotallyPositiveElement F where
  val := α.val * β.val
  pos_emb := fun φ => by
    obtain ⟨a, ha, hae⟩ := α.pos_emb φ
    obtain ⟨b, hb, hbe⟩ := β.pos_emb φ
    refine ⟨a * b, mul_pos ha hb, ?_⟩
    rw [map_mul, hae, hbe, Complex.ofReal_mul]

/-- Multiplicative inverse of a totally positive element. -/
def inv (α : TotallyPositiveElement F) : TotallyPositiveElement F where
  val := α.val⁻¹
  pos_emb := fun φ => by
    obtain ⟨a, ha, hae⟩ := α.pos_emb φ
    refine ⟨a⁻¹, inv_pos.mpr ha, ?_⟩
    rw [map_inv₀, hae, Complex.ofReal_inv]

/-- Positive rational scaling of a totally positive element. -/
def posRatSmul {q : ℚ} (hq : 0 < q) (α : TotallyPositiveElement F) :
    TotallyPositiveElement F where
  val := (q : F) * α.val
  pos_emb := fun φ => by
    obtain ⟨a, ha, hae⟩ := α.pos_emb φ
    refine ⟨(q : ℝ) * a, mul_pos (by exact_mod_cast hq) ha, ?_⟩
    rw [map_mul, hae]
    have hq' : φ (q : F) = ((q : ℝ) : ℂ) := by simp
    rw [hq', Complex.ofReal_mul]

/-- Natural power of a totally positive element. -/
def pow (α : TotallyPositiveElement F) (n : ℕ) : TotallyPositiveElement F where
  val := α.val ^ n
  pos_emb := fun φ => by
    obtain ⟨a, ha, hae⟩ := α.pos_emb φ
    refine ⟨a ^ n, pow_pos ha n, ?_⟩
    rw [map_pow, hae, Complex.ofReal_pow]

theorem ne_zero (α : TotallyPositiveElement F) : α.val ≠ 0 := by
  intro h0
  obtain ⟨φ⟩ := (inferInstance : Nonempty (F →+* ℂ))
  obtain ⟨c, hc, he⟩ := α.pos_emb φ
  rw [h0, map_zero] at he
  exact hc.ne' (Complex.ofReal_injective he.symm)

theorem re_pos (α : TotallyPositiveElement F) (φ : F →+* ℂ) : 0 < (φ α.val).re := by
  obtain ⟨c, hc, he⟩ := α.pos_emb φ
  rw [he, Complex.ofReal_re]
  exact hc

theorem norm_eq_prod_re (α : TotallyPositiveElement F) :
    ((Algebra.norm ℚ α.val : ℚ) : ℝ) = ∏ φ : F →+* ℂ, (φ α.val).re := by
  apply Complex.ofReal_injective
  have hcast : (((Algebra.norm ℚ α.val : ℚ) : ℝ) : ℂ) = algebraMap ℚ ℂ (Algebra.norm ℚ α.val) := by
    simp
  rw [hcast, Algebra.norm_eq_prod_embeddings ℚ ℂ α.val]
  have h3 : ∏ σ : F →ₐ[ℚ] ℂ, σ α.val = ∏ φ : F →+* ℂ, φ α.val :=
    Fintype.prod_equiv (RingHom.equivRatAlgHom (R := F) (S := ℂ)).symm _ _ fun _ => rfl
  rw [h3, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun φ _ => ?_
  obtain ⟨c, _, he⟩ := α.pos_emb φ
  rw [he, Complex.ofReal_re]

theorem abs_norm_eq_prod_re (α : TotallyPositiveElement F) :
    |((Algebra.norm ℚ α.val : ℚ) : ℝ)| = ∏ φ : F →+* ℂ, (φ α.val).re := by
  rw [← norm_eq_prod_re α, abs_of_pos]
  rw [norm_eq_prod_re α]
  exact Finset.prod_pos fun φ _ => α.re_pos φ

theorem norm_pos (α : TotallyPositiveElement F) : 0 < ((Algebra.norm ℚ α.val : ℚ) : ℝ) := by
  rw [norm_eq_prod_re α]
  exact Finset.prod_pos fun φ _ => α.re_pos φ

theorem trace_eq_sum_re (α : TotallyPositiveElement F) :
    ((Algebra.trace ℚ F α.val : ℚ) : ℝ) = ∑ φ : F →+* ℂ, (φ α.val).re := by
  apply Complex.ofReal_injective
  have hcast : (((Algebra.trace ℚ F α.val : ℚ) : ℝ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ F α.val) := by
    simp
  rw [hcast, trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := α.val)]
  have h3 : ∑ σ : F →ₐ[ℚ] ℂ, σ α.val = ∑ φ : F →+* ℂ, φ α.val :=
    Fintype.sum_equiv (RingHom.equivRatAlgHom (R := F) (S := ℂ)).symm _ _ fun _ => rfl
  rw [h3, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun φ _ => ?_
  obtain ⟨c, _, he⟩ := α.pos_emb φ
  rw [he, Complex.ofReal_re]

theorem trace_pos (α : TotallyPositiveElement F) : 0 < ((Algebra.trace ℚ F α.val : ℚ) : ℝ) := by
  rw [trace_eq_sum_re α]
  have hne : (Finset.univ : Finset (F →+* ℂ)).Nonempty := by
    rw [Finset.univ_nonempty_iff, ← Fintype.card_pos_iff, Embeddings.card]
    exact Module.finrank_pos
  exact Finset.sum_pos (fun φ _ => α.re_pos φ) hne

end TotallyPositiveElement

/-- **AM–GM Inequality for Totally Positive Elements (Embedding Sum Form)**:
for any totally positive `α` in a number field `F`,
`[F : ℚ] * (N_{F/ℚ}(α))^{1/[F : ℚ]} ≤ ∑ φ : F →+* ℂ, (φ α).re`. -/
theorem am_gm_totally_positive_sum_re {F : Type*} [Field F] [NumberField F]
    (α : TotallyPositiveElement F) :
    (Module.finrank ℚ F : ℝ) * ((Algebra.norm ℚ α.val : ℚ) : ℝ) ^ (1 / (Module.finrank ℚ F : ℝ)) ≤
      ∑ φ : F →+* ℂ, (φ α.val).re := by
  set d : ℝ := (Module.finrank ℚ F : ℝ) with hd
  have hcard : (Fintype.card (F →+* ℂ) : ℝ) = d := by rw [hd, Embeddings.card]
  have hd0 : 0 < d := by rw [hd]; exact_mod_cast Module.finrank_pos (R := ℚ) (M := F)
  have hgm := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (F →+* ℂ))
    (fun _ => 1 / d) (fun φ => (φ α.val).re) (fun _ _ => by positivity)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]; field_simp)
    (fun φ _ => (α.re_pos φ).le)
  rw [Real.finsetProd_rpow _ _ (fun φ _ => (α.re_pos φ).le), ← Finset.mul_sum,
    ← α.norm_eq_prod_re] at hgm
  calc d * ((Algebra.norm ℚ α.val : ℚ) : ℝ) ^ (1 / d)
      ≤ d * (1 / d * ∑ φ : F →+* ℂ, (φ α.val).re) := by gcongr
    _ = ∑ φ : F →+* ℂ, (φ α.val).re := by field_simp

/-- **AM–GM Trace Inequality for Totally Positive Elements**:
`Tr_{F/ℚ}(α) ≥ [F : ℚ] · (N_{F/ℚ}(α))^{1/[F : ℚ]}` for every totally positive `α` in any
number field `F`. -/
theorem am_gm_totally_positive_trace {F : Type*} [Field F] [NumberField F]
    (α : TotallyPositiveElement F) :
    (Module.finrank ℚ F : ℝ) * ((Algebra.norm ℚ α.val : ℚ) : ℝ) ^ (1 / (Module.finrank ℚ F : ℝ)) ≤
      ((Algebra.trace ℚ F α.val : ℚ) : ℝ) := by
  rw [α.trace_eq_sum_re]
  exact am_gm_totally_positive_sum_re α

/-- Real-embedding form of `am_gm_totally_positive_trace` for totally real number fields `F`. -/
theorem am_gm_totally_positive_trace_real {F : Type*} [Field F] [NumberField F]
    [IsTotallyReal F] (α : F) (hα : ∀ σ : F →+* ℝ, 0 < σ α) :
    (Module.finrank ℚ F : ℝ) * ((Algebra.norm ℚ α : ℚ) : ℝ) ^ (1 / (Module.finrank ℚ F : ℝ)) ≤
      ((Algebra.trace ℚ F α : ℚ) : ℝ) :=
  am_gm_totally_positive_trace ⟨α, isTotallyPositive_of_real_embeddings α hα⟩

/-- Lower bound on `Tr_{F/ℚ}(α)` given `1 ≤ |N_{F/ℚ}(α)| * X` (`X > 0`). -/
theorem totally_positive_trace_ge_of_norm_mul_ge {F : Type*} [Field F] [NumberField F]
    (α : TotallyPositiveElement F) {X : ℝ} (hX : 0 < X)
    (h1 : 1 ≤ |((Algebra.norm ℚ α.val : ℚ) : ℝ)| * X) :
    (Module.finrank ℚ F : ℝ) * X ^ (-(1 / (Module.finrank ℚ F : ℝ))) ≤
      ((Algebra.trace ℚ F α.val : ℚ) : ℝ) := by
  have hPX : X⁻¹ ≤ ((Algebra.norm ℚ α.val : ℚ) : ℝ) := by
    rw [inv_le_iff_one_le_mul₀ hX, mul_comm, ← abs_of_pos α.norm_pos]
    linarith
  have hmono : X ^ (-(1 / (Module.finrank ℚ F : ℝ))) ≤
      ((Algebra.norm ℚ α.val : ℚ) : ℝ) ^ (1 / (Module.finrank ℚ F : ℝ)) := by
    rw [Real.rpow_neg hX.le, ← Real.inv_rpow hX.le]
    exact Real.rpow_le_rpow (inv_nonneg.mpr hX.le) hPX (by positivity)
  calc (Module.finrank ℚ F : ℝ) * X ^ (-(1 / (Module.finrank ℚ F : ℝ)))
      ≤ (Module.finrank ℚ F : ℝ) *
          ((Algebra.norm ℚ α.val : ℚ) : ℝ) ^ (1 / (Module.finrank ℚ F : ℝ)) := by gcongr
    _ ≤ ((Algebra.trace ℚ F α.val : ℚ) : ℝ) := am_gm_totally_positive_trace α

end TotallyPositive

/-! ## Section 2: CM Hermitian Forms, Different Ideal & `totally_positive_trace_ge_of_norm_discr` -/

section CMHermitianAndDifferent

/-- Compatibility of a `StarRing` involution on `E` with complex conjugation on every embedding
`φ : E →+* ℂ`. -/
def CMStarCompat (E : Type*) [Field E] [StarRing E] : Prop :=
  ∀ (φ : E →+* ℂ) (a : E), φ (star a) = star (φ a)

/-- Real trace `Tr_{E/ℚ}(a)` computed as `(∑ σ : E →+* ℂ, σ a).re`. -/
def trR {E : Type*} [Field E] [NumberField E] (a : E) : ℝ :=
  (∑ σ : E →+* ℂ, σ a).re

theorem trR_eq {E : Type*} [Field E] [NumberField E] (a : E) :
    trR a = ((Algebra.trace ℚ E a : ℚ) : ℝ) := by
  have h2 := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := a)
  have h3 : ∑ σ : E →ₐ[ℚ] ℂ, σ a = ∑ φ : E →+* ℂ, φ a :=
    Fintype.sum_equiv (RingHom.equivRatAlgHom (R := E) (S := ℂ)).symm _ _ fun _ => rfl
  unfold trR
  rw [← h3, ← h2]
  simp

theorem trR_add {E : Type*} [Field E] [NumberField E] (a b : E) :
    trR (a + b) = trR a + trR b := by
  simp [trR, Finset.sum_add_distrib]

theorem trR_star {E : Type*} [Field E] [NumberField E] [StarRing E]
    (hσ : CMStarCompat E) (a : E) : trR (star a) = trR a := by
  unfold trR
  have hsum : ∑ σ : E →+* ℂ, σ (star a) = star (∑ σ : E →+* ℂ, σ a) := by
    rw [star_sum]
    exact Finset.sum_congr rfl fun σ _ => hσ σ a
  rw [hsum]
  simp

theorem trace_star {E : Type*} [Field E] [NumberField E] [StarRing E]
    (hσ : CMStarCompat E) (a : E) :
    Algebra.trace ℚ E (star a) = Algebra.trace ℚ E a := by
  apply (algebraMap ℚ ℝ).injective
  have h1 : (algebraMap ℚ ℝ) (Algebra.trace ℚ E (star a)) = trR (star a) := by
    simpa using (trR_eq (star a)).symm
  have h2 : (algebraMap ℚ ℝ) (Algebra.trace ℚ E a) = trR a := by
    simpa using (trR_eq a).symm
  rw [h1, h2, trR_star hσ]

/-- Restriction of `starRingEnd E` to the ring of integers `𝓞 E`. -/
def starO {E : Type*} [Field E] [NumberField E] [StarRing E] : 𝓞 E →+* 𝓞 E :=
  RingOfIntegers.mapRingHom (starRingEnd E)

theorem starO_coe {E : Type*} [Field E] [NumberField E] [StarRing E] (w : 𝓞 E) :
    ((starO w : 𝓞 E) : E) = star (w : E) := rfl

/-- Positive-definite `E`-valued Hermitian space `(V, hT)` over a CM number field `E`. -/
structure CMHermitianForm (E : Type*) [Field E] [NumberField E] [StarRing E] where
  V : Type*
  [addV : AddCommGroup V]
  [modV : Module E V]
  [modOV : Module (𝓞 E) V]
  [towV : IsScalarTower (𝓞 E) E V]
  hT : V → V → E
  hT_add_left : ∀ x x' y, hT (x + x') y = hT x y + hT x' y
  hT_add_right : ∀ x y y', hT x (y + y') = hT x y + hT x y'
  hT_smul_left : ∀ (c : E) x y, hT (c • x) y = star c * hT x y
  hT_smul_right : ∀ (c : E) x y, hT x (c • y) = c * hT x y
  hT_herm : ∀ x y, hT y x = star (hT x y)
  hT_pos : ∀ (φ : E →+* ℂ) (x : V), x ≠ 0 → ∃ c : ℝ, 0 < c ∧ φ (hT x x) = (c : ℂ)

attribute [instance] CMHermitianForm.addV CMHermitianForm.modV CMHermitianForm.modOV
  CMHermitianForm.towV

namespace CMHermitianForm

variable {E : Type*} [Field E] [NumberField E] [StarRing E]

/-- For every nonzero `x : S.V`, `S.hT x x` is a `TotallyPositiveElement E`. -/
def selfToTotallyPositive (S : CMHermitianForm E) {x : S.V} (hx : x ≠ 0) :
    TotallyPositiveElement E where
  val := S.hT x x
  pos_emb := fun φ => S.hT_pos φ x hx

theorem trR_self_pos (S : CMHermitianForm E) {x : S.V} (hx : x ≠ 0) :
    0 < trR (S.hT x x) := by
  rw [trR_eq]
  exact (S.selfToTotallyPositive hx).trace_pos

theorem hT_self_ne_zero (S : CMHermitianForm E) {x : S.V} (hx : x ≠ 0) :
    S.hT x x ≠ 0 := by
  intro h0
  have hp := S.trR_self_pos hx
  rw [h0] at hp
  simp [trR] at hp

end CMHermitianForm

/-- `𝓞 E`-dual submodule `L^# = { z ∈ V | ∀ l ∈ L, ⟨l, z⟩ ∈ 𝓞 E }` inside `S.V`. -/
def dualSub {E : Type*} [Field E] [NumberField E] [StarRing E]
    (S : CMHermitianForm E) (L : Submodule (𝓞 E) S.V) : Submodule (𝓞 E) S.V where
  carrier := { z | ∀ l ∈ L, S.hT l z ∈ (algebraMap (𝓞 E) E).range }
  add_mem' {z₁ z₂} hz₁ hz₂ l hl := by
    rw [S.hT_add_right]
    exact add_mem (hz₁ l hl) (hz₂ l hl)
  zero_mem' l _ := by
    have h0 : S.hT l 0 = 0 := by
      have := S.hT_smul_right 0 l 0
      simpa using this
    rw [h0]
    exact zero_mem _
  smul_mem' a z hz l hl := by
    rw [← algebraMap_smul E a z, S.hT_smul_right]
    obtain ⟨w, hw⟩ := hz l hl
    exact ⟨a * w, by rw [map_mul, hw]⟩

/-- `ℤ`-trace dual condition: `∀ l ∈ L, Tr_{E/ℚ}(S.hT l z) ∈ ℤ`. -/
def TrDual {E : Type*} [Field E] [NumberField E] [StarRing E]
    (S : CMHermitianForm E) (L : Submodule (𝓞 E) S.V) (z : S.V) : Prop :=
  ∀ l ∈ L, Algebra.trace ℚ E (S.hT l z) ∈ (algebraMap ℤ ℚ).range

/-- Lattice index hypothesis `LatT S q L`: the relative index of `L` in `dualSub S L` is `q`. -/
def LatT {E : Type*} [Field E] [NumberField E] [StarRing E]
    (S : CMHermitianForm E) (q : ℕ) (L : Submodule (𝓞 E) S.V) : Prop :=
  L.toAddSubgroup.relIndex (dualSub S L).toAddSubgroup = q

theorem mem_dual_one_iff {E : Type*} [Field E] [NumberField E] (x : E) :
    x ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔
      ∀ w : 𝓞 E, Algebra.trace ℚ E (x * (w : E)) ∈ (algebraMap ℤ ℚ).range := by
  rw [FractionalIdeal.mem_dual (I := (1 : FractionalIdeal (𝓞 E)⁰ E)) one_ne_zero]
  constructor
  · intro h w
    exact h _ ((FractionalIdeal.mem_one_iff _).2 ⟨w, rfl⟩)
  · intro h y hy
    obtain ⟨w, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hy
    exact h w

theorem hT_left_mem_dual {E : Type*} [Field E] [NumberField E] [StarRing E]
    (S : CMHermitianForm E) (L : Submodule (𝓞 E) S.V) (z : S.V) (hz : TrDual S L z)
    {l : S.V} (hl : l ∈ L) :
    S.hT l z ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  rw [mem_dual_one_iff]
  intro w
  have hm : (starO w) • l ∈ L := L.smul_mem _ hl
  have htr := hz _ hm
  rw [← algebraMap_smul E (starO w) l, S.hT_smul_left] at htr
  have e : star (algebraMap (𝓞 E) E (starO w)) * S.hT l z = S.hT l z * (w : E) := by
    rw [show algebraMap (𝓞 E) E (starO w) = star (w : E) from rfl, star_star, mul_comm]
  rwa [e] at htr

theorem hT_right_mem_dual {E : Type*} [Field E] [NumberField E] [StarRing E]
    (S : CMHermitianForm E) (hσ : CMStarCompat E)
    (L : Submodule (𝓞 E) S.V) (z : S.V) (hz : TrDual S L z)
    {l : S.V} (hl : l ∈ L) :
    S.hT z l ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  have hx := hT_left_mem_dual S L z hz hl
  rw [mem_dual_one_iff] at hx ⊢
  intro w
  have h1 := hx (starO w)
  have hsym : S.hT z l = star (S.hT l z) := S.hT_herm l z
  rw [hsym, ← trace_star hσ, star_mul, star_star, mul_comm]
  rwa [starO_coe] at h1

theorem dual_mul_differentIdeal {E : Type*} [Field E] [NumberField E] :
    FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) *
      ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) = 1 := by
  rw [coeIdeal_differentIdeal ℤ ℚ E (𝓞 E)]
  exact mul_inv_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero)

theorem diff_smul_mem_dualSub {E : Type*} [Field E] [NumberField E] [StarRing E]
    (S : CMHermitianForm E) (L : Submodule (𝓞 E) S.V) (z : S.V) (hz : TrDual S L z)
    {δ : 𝓞 E} (hδ : δ ∈ differentIdeal ℤ (𝓞 E)) :
    δ • z ∈ dualSub S L := by
  intro l hl
  have hx := hT_left_mem_dual S L z hz hl
  have hm : S.hT l z * (δ : E) ∈
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) *
        ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) :=
    FractionalIdeal.mul_mem_mul hx ((FractionalIdeal.mem_coeIdeal _).2 ⟨δ, hδ, rfl⟩)
  rw [dual_mul_differentIdeal, FractionalIdeal.mem_one_iff] at hm
  obtain ⟨w, hw⟩ := hm
  refine ⟨w, ?_⟩
  rw [← algebraMap_smul E δ z, S.hT_smul_right, hw, mul_comm]

/-- Conductor ideal `bIdeal S L z := (L : z) ∩ 𝔇_{E/ℚ}` in `𝓞 E`. -/
def bIdeal {E : Type*} [Field E] [NumberField E] [StarRing E]
    (S : CMHermitianForm E) (L : Submodule (𝓞 E) S.V) (z : S.V) : Ideal (𝓞 E) :=
  L.comap (LinearMap.toSpanSingleton (𝓞 E) S.V z) ⊓ differentIdeal ℤ (𝓞 E)

theorem relIndex_bIdeal {E : Type*} [Field E] [NumberField E] [StarRing E]
    (S : CMHermitianForm E) (q : ℕ) (L : Submodule (𝓞 E) S.V) (hL : LatT S q L) (hq : q ≠ 0)
    (z : S.V) (hz : TrDual S L z) :
    (bIdeal S L z).toAddSubgroup.relIndex (differentIdeal ℤ (𝓞 E)).toAddSubgroup ≤ q ∧
    (bIdeal S L z).toAddSubgroup.relIndex (differentIdeal ℤ (𝓞 E)).toAddSubgroup ≠ 0 := by
  set g : 𝓞 E →+ S.V := (LinearMap.toSpanSingleton (𝓞 E) S.V z).toAddMonoidHom with hg
  have hc : (L.comap (LinearMap.toSpanSingleton (𝓞 E) S.V z)).toAddSubgroup =
      L.toAddSubgroup.comap g := by
    ext w; rfl
  have hb : (bIdeal S L z).toAddSubgroup =
      (L.comap (LinearMap.toSpanSingleton (𝓞 E) S.V z)).toAddSubgroup ⊓
        (differentIdeal ℤ (𝓞 E)).toAddSubgroup := by
    ext w; rfl
  rw [hb, AddSubgroup.inf_relIndex_right, hc, AddSubgroup.relIndex_comap]
  have hle : (differentIdeal ℤ (𝓞 E)).toAddSubgroup.map g ≤ (dualSub S L).toAddSubgroup := by
    rintro _ ⟨δ, hδ, rfl⟩
    exact diff_smul_mem_dualSub S L z hz hδ
  have hq' : L.toAddSubgroup.relIndex (dualSub S L).toAddSubgroup ≠ 0 := by rw [hL]; exact hq
  refine ⟨hL ▸ AddSubgroup.relIndex_le_of_le_right hle hq', fun h => hq' ?_⟩
  exact AddSubgroup.relIndex_eq_zero_of_le_right hle h

theorem absNorm_bIdeal {E : Type*} [Field E] [NumberField E] [StarRing E]
    (S : CMHermitianForm E) (q : ℕ) (L : Submodule (𝓞 E) S.V) (hL : LatT S q L) (hq : q ≠ 0)
    (z : S.V) (hz : TrDual S L z) :
    Ideal.absNorm (bIdeal S L z) ≤ q * (NumberField.discr E).natAbs ∧
      Ideal.absNorm (bIdeal S L z) ≠ 0 := by
  obtain ⟨h1, h2⟩ := relIndex_bIdeal S q L hL hq z hz
  have hd : Ideal.absNorm (differentIdeal ℤ (𝓞 E)) = (NumberField.discr E).natAbs :=
    NumberField.absNorm_differentIdeal E (𝓞 E)
  have hd0 : (NumberField.discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero E)
  have hmul := AddSubgroup.relIndex_mul_index (H := (bIdeal S L z).toAddSubgroup)
    (K := (differentIdeal ℤ (𝓞 E)).toAddSubgroup) (fun _ hx => hx.2)
  rw [← Ideal.absNorm_eq_index, ← Ideal.absNorm_eq_index, hd] at hmul
  rw [← hmul]
  exact ⟨Nat.mul_le_mul_right _ h1, mul_ne_zero h2 hd0⟩

theorem one_le_norm_discr {E : Type*} [Field E] [NumberField E] [StarRing E]
    (S : CMHermitianForm E) (hσ : CMStarCompat E) (q : ℕ)
    (L : Submodule (𝓞 E) S.V) (hL : LatT S q L) (hq : q ≠ 0) (z : S.V) (hz : TrDual S L z)
    (hz0 : z ≠ 0) :
    1 ≤ |Algebra.norm ℚ (S.hT z z)| * ((q : ℚ) * ((NumberField.discr E).natAbs : ℚ) ^ 2) := by
  set a := S.hT z z
  have ha : a ≠ 0 := S.hT_self_ne_zero hz0
  set 𝔟 := bIdeal S L z
  set 𝔡 := differentIdeal ℤ (𝓞 E)
  obtain ⟨hbn, hb0⟩ := absNorm_bIdeal S q L hL hq z hz
  have hd : Ideal.absNorm 𝔡 = (NumberField.discr E).natAbs :=
    NumberField.absNorm_differentIdeal E (𝓞 E)
  have hd0 : (NumberField.discr E).natAbs ≠ 0 :=
    Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero E)
  have hle1 : FractionalIdeal.spanSingleton (𝓞 E)⁰ a * (𝔟 : FractionalIdeal (𝓞 E)⁰ E) ≤
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [FractionalIdeal.mul_le]
    intro i hi j hj
    obtain ⟨w, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hj
    have hwb : w * b ∈ 𝔟 := 𝔟.mul_mem_left w hb
    have hL' : (w * b) • z ∈ L := hwb.1
    have hm := hT_right_mem_dual S hσ L z hz hL'
    have e : S.hT z ((w * b) • z) = w • a * algebraMap (𝓞 E) E b := by
      rw [← algebraMap_smul E (w * b) z, S.hT_smul_right, Algebra.smul_def, map_mul]
      ring
    rwa [e] at hm
  have hJ : FractionalIdeal.spanSingleton (𝓞 E)⁰ a * (𝔟 : FractionalIdeal (𝓞 E)⁰ E) *
      (𝔡 : FractionalIdeal (𝓞 E)⁰ E) ≤ 1 :=
    (FractionalIdeal.mul_le.2 fun _ hi _ hj => FractionalIdeal.mul_mem_mul (hle1 hi) hj).trans
      dual_mul_differentIdeal.le
  have hJ0 : FractionalIdeal.spanSingleton (𝓞 E)⁰ a * (𝔟 : FractionalIdeal (𝓞 E)⁰ E) *
      (𝔡 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
    · rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
      intro h; apply hb0; change Ideal.absNorm 𝔟 = 0; rw [h, Ideal.absNorm_bot]
    · rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
      intro h; apply hd0; rw [← hd, h, Ideal.absNorm_bot]
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hJ
  have hI0 : I ≠ ⊥ := by
    intro h; apply hJ0; rw [← hI, h, FractionalIdeal.coeIdeal_bot]
  have hnI : (1 : ℚ) ≤ Ideal.absNorm I := by
    have : Ideal.absNorm I ≠ 0 := fun h => hI0 (Ideal.absNorm_eq_zero_iff.1 h)
    exact_mod_cast Nat.one_le_iff_ne_zero.2 this
  have hval : FractionalIdeal.absNorm
      (FractionalIdeal.spanSingleton (𝓞 E)⁰ a * (𝔟 : FractionalIdeal (𝓞 E)⁰ E) *
        (𝔡 : FractionalIdeal (𝓞 E)⁰ E)) =
      |Algebra.norm ℚ a| * Ideal.absNorm 𝔟 * Ideal.absNorm 𝔡 := by
    rw [map_mul, map_mul, FractionalIdeal.absNorm_span_singleton,
      FractionalIdeal.coeIdeal_absNorm, FractionalIdeal.coeIdeal_absNorm]
  rw [← hI, FractionalIdeal.coeIdeal_absNorm] at hval
  rw [hval, hd] at hnI
  have hbq : (Ideal.absNorm 𝔟 : ℚ) ≤ q * (NumberField.discr E).natAbs := by exact_mod_cast hbn
  have hN : 0 ≤ |Algebra.norm ℚ a| := abs_nonneg _
  have hD : (0 : ℚ) ≤ (NumberField.discr E).natAbs := by positivity
  calc (1 : ℚ) ≤ |Algebra.norm ℚ a| * Ideal.absNorm 𝔟 * (NumberField.discr E).natAbs := hnI
    _ ≤ |Algebra.norm ℚ a| * (q * (NumberField.discr E).natAbs) *
        (NumberField.discr E).natAbs := by gcongr
    _ = |Algebra.norm ℚ a| * ((q : ℚ) * ((NumberField.discr E).natAbs : ℚ) ^ 2) := by ring

/-- **Totally-Positive Trace Lower Bound from Norm & Discriminant**:
for any totally positive `α` in a number field `E` and `q ≥ 1` satisfying
`1 ≤ |N_{E/ℚ}(α)| * q * |Δ_E|^2`,
`Tr_{E/ℚ}(α) ≥ [E : ℚ] * (q * |Δ_E|^2)^{-1 / [E : ℚ]}`. -/
theorem totally_positive_trace_ge_of_norm_discr {E : Type*} [Field E] [NumberField E]
    (α : TotallyPositiveElement E) (q : ℕ) (hq : 0 < q)
    (h1 : 1 ≤ |Algebra.norm ℚ α.val| * ((q : ℚ) * ((NumberField.discr E).natAbs : ℚ) ^ 2)) :
    (Module.finrank ℚ E : ℝ) *
        ((q : ℝ) * ((NumberField.discr E).natAbs : ℝ) ^ 2) ^ (-(1 / (Module.finrank ℚ E : ℝ))) ≤
      ((Algebra.trace ℚ E α.val : ℚ) : ℝ) := by
  have hd0 : (NumberField.discr E).natAbs ≠ 0 :=
    Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero E)
  have hX : (0 : ℝ) < (q : ℝ) * ((NumberField.discr E).natAbs : ℝ) ^ 2 := by positivity
  have h1' : (1 : ℝ) ≤ |((Algebra.norm ℚ α.val : ℚ) : ℝ)| *
      ((q : ℝ) * ((NumberField.discr E).natAbs : ℝ) ^ 2) := by
    have hq1 := (Rat.cast_le (K := ℝ)).2 h1
    push_cast at hq1
    exact hq1
  exact totally_positive_trace_ge_of_norm_mul_ge α hX h1'

/-- **Dual-Lattice CM Hermitian Trace Lower Bound** (`PLemTLat.trR_dual_ge`):
if `z ≠ 0` lies in the `ℤ`-trace dual of `L` (`TrDual S L z`) and `[dualSub S L : L] = q ≠ 0`,
then `trR (S.hT z z) ≥ [E : ℚ] * (q * |Δ_E|^2)^{-1 / [E : ℚ]}`. -/
theorem trR_dual_ge_of_norm_discr {E : Type*} [Field E] [NumberField E] [StarRing E]
    (S : CMHermitianForm E) (hσ : CMStarCompat E) (q : ℕ) (hq : q ≠ 0)
    (L : Submodule (𝓞 E) S.V) (hL : LatT S q L) (z : S.V) (hz : TrDual S L z) (hz0 : z ≠ 0) :
    (Module.finrank ℚ E : ℝ) *
        ((q : ℝ) * ((NumberField.discr E).natAbs : ℝ) ^ 2) ^ (-(1 / (Module.finrank ℚ E : ℝ))) ≤
      trR (S.hT z z) := by
  rw [trR_eq]
  exact totally_positive_trace_ge_of_norm_discr (S.selfToTotallyPositive hz0) q
    (Nat.pos_of_ne_zero hq) (one_le_norm_discr S hσ q L hL hq z hz hz0)

/-- Covering-radius spanning lemma (`PLemTGeo.span_short_of_cover`): if every point of `W` is
within distance `μ > 0` of a lattice `Λ ⊂ W`, then `{ l ∈ Λ | ‖l‖ ≤ 3 * μ }` spans `W` over `ℝ`. -/
theorem span_short_of_cover {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (Λ : Submodule ℤ W) (μ : ℝ) (hμ : 0 < μ)
    (hcov : ∀ x : W, ∃ l ∈ Λ, ‖x - l‖ ≤ μ) :
    Submodule.span ℝ { l : W | l ∈ Λ ∧ ‖l‖ ≤ 3 * μ } = ⊤ := by
  set K := Submodule.span ℝ { l : W | l ∈ Λ ∧ ‖l‖ ≤ 3 * μ }
  by_contra hne
  have hKo : Kᗮ ≠ ⊥ := fun h => hne (Submodule.orthogonal_eq_bot_iff.mp h)
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hKo
  have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  set x : W := (2 * μ / ‖u‖) • u with hx
  have hxn : ‖x‖ = 2 * μ := by
    rw [hx, norm_smul, Real.norm_of_nonneg (by positivity)]
    field_simp
  have hxK : x ∈ Kᗮ := Submodule.smul_mem _ _ hu
  obtain ⟨l, hl, hd⟩ := hcov x
  have hln : ‖l‖ ≤ 3 * μ := by
    calc ‖l‖ = ‖x - (x - l)‖ := by congr 1; abel
      _ ≤ ‖x‖ + ‖x - l‖ := norm_sub_le _ _
      _ ≤ 2 * μ + μ := by linarith
      _ = 3 * μ := by ring
  have hlK : l ∈ K := Submodule.subset_span ⟨hl, hln⟩
  have horth : ⟪l, x⟫_ℝ = 0 := Submodule.inner_right_of_mem_orthogonal hlK hxK
  have hsq : ‖x - l‖ ^ 2 = ‖x‖ ^ 2 + ‖l‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_comm, horth]
    ring
  have h1 : ‖x - l‖ ^ 2 ≤ μ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
  nlinarith [sq_nonneg ‖l‖]

end CMHermitianAndDifferent

/-! ## Section 3: Archimedean Gram Determinants, Realification & `q_frame_degree` -/

section ArchimedeanFramesAndQFrameDegree

open RHDirect.ArakelovCovolume (rk covol degAr slope muMax
  discreteTopology_of_le covol_eq_sqrt_det_gram covol_pos rk_pos_of_ne_bot
  covol_le_of_le_same_rank gram_sum_smul_eq_transpose_mul gram_det_le
  bost_slope_inequality linearIndependent_coe_basis det_gram_basis_pos)
open RHDirect.Stage4ArakelovBost (IsSaturated projOrth quotLat
  discreteTopology_of_fin_basis_real_li discreteTopology_quotLat
  rk_add_quotLat covol_eq_mul_quotLat degAr_eq_add_quotLat)
open RHDirect.Stage10GeometryOfNumbers (basisOfZLattice covolume_eq_abs_det)
open RHDirect.Stage12SchurWeylLattices (vecAt fcoord normAt realizeHLat norm_sq_realizeHLat
  NumberFieldHLat euclideanSpaceCongr)

/-- Archimedean Hermitian pairing `majAt b X v x y` at infinite place `v : InfinitePlace K`. -/
def majAt {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x y : V) : ℂ :=
  ∑ i : ι, star (fcoord b X v x i) * fcoord b X v y i

theorem majAt_self {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x : V) :
    majAt b X v x x = ((normAt b X v x ^ 2 : ℝ) : ℂ) := by
  unfold majAt normAt
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem majAt_add_left {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x x' y : V) :
    majAt b X v (x + x') y = majAt b X v x y + majAt b X v x' y := by
  unfold majAt
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hadd : fcoord b X v (x + x') = fcoord b X v x + fcoord b X v x' := by
    unfold fcoord
    rw [← Matrix.mulVec_add]
    congr 1; funext j; simp [vecAt, map_add]
  rw [hadd, Pi.add_apply, star_add, add_mul]

theorem majAt_herm {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x y : V) :
    majAt b X v y x = star (majAt b X v x y) := by
  unfold majAt
  rw [star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_mul', star_star, mul_comm]

/-- Exact real inner product of `realizeHLat`:
`⟪realizeHLat b X x, realizeHLat b X y⟫_ℝ = ∑ v : InfinitePlace K, (majAt b X v x y).re`. -/
theorem inner_realizeHLat {K V ι : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (x y : V) :
    ⟪realizeHLat b X x, realizeHLat b X y⟫_ℝ =
      ∑ v : InfinitePlace K, (majAt b X v x y).re := by
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    ← map_add (realizeHLat b X), ← sq, ← sq, ← sq,
    norm_sq_realizeHLat, norm_sq_realizeHLat, norm_sq_realizeHLat]
  have h1 : ∀ v : InfinitePlace K,
      normAt b X v (x + y) ^ 2 - normAt b X v x ^ 2 - normAt b X v y ^ 2 =
        2 * (majAt b X v x y).re := by
    intro v
    have hxy := majAt_self b X v (x + y)
    have hx := majAt_self b X v x
    have hy := majAt_self b X v y
    have hexp : majAt b X v (x + y) (x + y) =
        majAt b X v x x + majAt b X v x y + majAt b X v y x + majAt b X v y y := by
      rw [majAt_add_left]
      have har : ∀ z, majAt b X v z (x + y) = majAt b X v z x + majAt b X v z y := fun z => by
        rw [majAt_herm, majAt_add_left, star_add, ← majAt_herm, ← majAt_herm]
      rw [har x, har y]
      ring
    rw [hxy, hx, hy, majAt_herm b X v x y] at hexp
    have hre := congrArg Complex.re hexp
    simp only [Complex.ofReal_re, Complex.add_re, Complex.star_def, Complex.conj_re] at hre
    linarith
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  have hsum : ∑ v : InfinitePlace K, (normAt b X v (x + y) ^ 2 - normAt b X v x ^ 2 -
      normAt b X v y ^ 2) = 2 * ∑ v : InfinitePlace K, (majAt b X v x y).re := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => h1 v
  rw [hsum]
  ring

/-- Archimedean Gram matrix `gramJ A e v` of a family `e : J → A.V` at place `v : InfinitePlace K`. -/
def gramJ {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    (A : NumberFieldHLat K) {J : Type*} (e : J → A.V) (v : InfinitePlace K) : Matrix J J ℂ :=
  Matrix.of fun i j => majAt A.b A.X v (e i) (e j)

/-- **Self-Gram Determinant Formula (`ClassMapArchimedean.gramJ_self_det`)**:
`(gramJ A A.b v).det.re = (‖(A.X v).det‖ ^ 2)⁻¹`. -/
theorem gramJ_self_det {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    (A : NumberFieldHLat K) (v : InfinitePlace K) :
    (gramJ A A.b v).det.re = (‖(A.X v).det‖ ^ 2)⁻¹ := by
  classical
  have h : ∀ i' : A.ι, (A.X v)⁻¹ *ᵥ vecAt A.b v (A.b i') = fun k => (A.X v)⁻¹ k i' := by
    intro i'
    funext k
    simp [vecAt, Matrix.mulVec, dotProduct, Basis.repr_self, Finsupp.single_apply]
  have he : gramJ A A.b v = ((A.X v)⁻¹)ᴴ * (A.X v)⁻¹ := by
    ext i j
    simp only [gramJ, Matrix.of_apply, majAt, fcoord, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [h, h]
  have hz : ∀ z : ℂ, (star z * z).re = ‖z‖ ^ 2 := fun z => by
    rw [show star z * z = ((Complex.normSq z : ℝ) : ℂ) by
      rw [Complex.normSq_eq_conj_mul_self]; rfl,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [he, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_nonsing_inv,
    Ring.inverse_eq_inv', hz, norm_inv, inv_pow]

section RealificationDet

/-- Real-linear map on `EuclideanSpace ℝ (ι × Fin 2)` induced by multiplication by a complex
matrix `M : Matrix ι ι ℂ`. -/
def complexToRealLin {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    EuclideanSpace ℝ (ι × Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (ι × Fin 2) where
  toFun x := WithLp.toLp 2 fun p =>
    let z : ι → ℂ := fun j => ⟨x (j, 0), x (j, 1)⟩
    if p.2 = 0 then ((M *ᵥ z) p.1).re else ((M *ᵥ z) p.1).im
  map_add' x y := by
    ext p
    have hz : (fun j => (⟨(x + y) (j, 0), (x + y) (j, 1)⟩ : ℂ)) =
        (fun j => ⟨x (j, 0), x (j, 1)⟩) + (fun j => ⟨y (j, 0), y (j, 1)⟩) := by
      funext j
      apply Complex.ext <;> simp
    change (if p.2 = 0 then ((M *ᵥ _ ) p.1).re else ((M *ᵥ _ ) p.1).im) =
      (if p.2 = 0 then ((M *ᵥ _ ) p.1).re else ((M *ᵥ _ ) p.1).im) +
      (if p.2 = 0 then ((M *ᵥ _ ) p.1).re else ((M *ᵥ _ ) p.1).im)
    rw [hz, Matrix.mulVec_add, Pi.add_apply, Complex.add_re, Complex.add_im]
    split_ifs <;> rfl
  map_smul' c x := by
    ext p
    have hz : (fun j => (⟨(c • x) (j, 0), (c • x) (j, 1)⟩ : ℂ)) =
        (c : ℂ) • (fun j => ⟨x (j, 0), x (j, 1)⟩) := by
      funext j
      apply Complex.ext <;> simp [smul_eq_mul]
    change (if p.2 = 0 then ((M *ᵥ _) p.1).re else ((M *ᵥ _) p.1).im) =
      c * (if p.2 = 0 then ((M *ᵥ _) p.1).re else ((M *ᵥ _) p.1).im)
    rw [hz, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im]
    split_ifs <;> ring

theorem complexToRealLin_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    complexToRealLin (1 : Matrix ι ι ℂ) = LinearMap.id := by
  ext x p
  change (if p.2 = 0 then (((1 : Matrix ι ι ℂ) *ᵥ fun j => ⟨x (j, 0), x (j, 1)⟩) p.1).re
    else (((1 : Matrix ι ι ℂ) *ᵥ fun j => ⟨x (j, 0), x (j, 1)⟩) p.1).im) = x p
  rw [Matrix.one_mulVec]
  rcases p with ⟨i, j⟩
  fin_cases j <;> rfl

theorem complexToRealLin_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N : Matrix ι ι ℂ) :
    complexToRealLin (M * N) = (complexToRealLin M).comp (complexToRealLin N) := by
  ext x p
  have hN : (fun j : ι => (⟨(complexToRealLin N x) (j, 0),
      (complexToRealLin N x) (j, 1)⟩ : ℂ)) =
      N *ᵥ (fun k => ⟨x (k, 0), x (k, 1)⟩) := by
    funext j
    apply Complex.ext <;> simp [complexToRealLin]
  change (if p.2 = 0 then (((M * N) *ᵥ fun k => ⟨x (k, 0), x (k, 1)⟩) p.1).re
    else (((M * N) *ᵥ fun k => ⟨x (k, 0), x (k, 1)⟩) p.1).im) =
    (if p.2 = 0 then ((M *ᵥ fun j => (⟨(complexToRealLin N x) (j, 0),
        (complexToRealLin N x) (j, 1)⟩ : ℂ)) p.1).re
    else ((M *ᵥ fun j => (⟨(complexToRealLin N x) (j, 0),
        (complexToRealLin N x) (j, 1)⟩ : ℂ)) p.1).im)
  rw [hN, Matrix.mulVec_mulVec]

theorem complexToRealLin_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) (x y : EuclideanSpace ℝ (ι × Fin 2)) :
    ⟪x, complexToRealLin M y⟫_ℝ = ⟪complexToRealLin Mᴴ x, y⟫_ℝ := by
  let zx : ι → ℂ := fun i => ⟨x (i, 0), x (i, 1)⟩
  let zy : ι → ℂ := fun j => ⟨y (j, 0), y (j, 1)⟩
  have hid : ∀ (u : EuclideanSpace ℝ (ι × Fin 2)) (w : ι → ℂ),
      (∑ p : ι × Fin 2, u p * (if p.2 = 0 then (w p.1).re else (w p.1).im)) =
        (∑ i : ι, (star (⟨u (i, 0), u (i, 1)⟩ : ℂ) * w i).re) := by
    intro u w
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fin.sum_univ_two]
    simp only [↓reduceIte, Fin.one_eq_zero_iff, Nat.reduceEqDiff, Complex.mul_re,
      Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct
  simp only [Pi.star_apply, star_trivial, complexToRealLin, LinearMap.coe_mk, AddHom.coe_mk,
    WithLp.ofLp_toLp]
  have hL : (∑ p : ι × Fin 2, (if p.2 = 0 then (M *ᵥ zy) p.1 |>.re else (M *ᵥ zy) p.1 |>.im) * x p) =
      (∑ i : ι, (star (zx i) * (M *ᵥ zy) i).re) := by
    simp_rw [mul_comm _ (x _)]
    exact hid x (M *ᵥ zy)
  have hR : (∑ p : ι × Fin 2, y p * (if p.2 = 0 then (Mᴴ *ᵥ zx) p.1 |>.re else (Mᴴ *ᵥ zx) p.1 |>.im)) =
      (∑ j : ι, (star (zy j) * (Mᴴ *ᵥ zx) j).re) :=
    hid y (Mᴴ *ᵥ zx)
  change (∑ p : ι × Fin 2, (if p.2 = 0 then (M *ᵥ zy) p.1 |>.re else (M *ᵥ zy) p.1 |>.im) * x p) =
    (∑ p : ι × Fin 2, y p * (if p.2 = 0 then (Mᴴ *ᵥ zx) p.1 |>.re else (Mᴴ *ᵥ zx) p.1 |>.im))
  rw [hL, hR]
  have hC : (∑ i : ι, star (zx i) * (M *ᵥ zy) i) =
      star (∑ j : ι, star (zy j) * (Mᴴ *ᵥ zx) j) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Finset.mul_sum, star_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [star_mul', star_star]
    ring
  have hCre := congrArg Complex.re hC
  simp only [Complex.re_sum, Complex.star_def, Complex.conj_re] at hCre
  exact hCre

theorem linearMap_det_adjoint_real {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : E →ₗ[ℝ] E) :
    LinearMap.det (LinearMap.adjoint T) = LinearMap.det T := by
  let b := stdOrthonormalBasis ℝ E
  rw [← LinearMap.det_toMatrix b.toBasis (LinearMap.adjoint T),
    ← LinearMap.det_toMatrix b.toBasis T, ← Matrix.det_transpose]
  congr 1
  ext i j
  rw [Matrix.transpose_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  have hrep : ∀ v (k : Fin (Module.finrank ℝ E)), b.toBasis.repr v k = ⟪b k, v⟫_ℝ := by
    intro v k
    conv_rhs => rw [← b.toBasis.sum_repr v]
    simp only [inner_sum, real_inner_smul_right]
    rw [Finset.sum_eq_single k]
    · have hk : ⟪b k, b.toBasis k⟫_ℝ = 1 := by
        simp [OrthonormalBasis.coe_toBasis, b.orthonormal.1 k]
      rw [hk, mul_one]
    · intro m _ hm
      have hmk : ⟪b k, b.toBasis m⟫_ℝ = 0 := by
        simp [OrthonormalBasis.coe_toBasis, b.orthonormal.2 hm.symm]
      rw [hmk, mul_zero]
    · intro hk; exact absurd (Finset.mem_univ k) hk
  rw [hrep, hrep, LinearMap.adjoint_inner_right, real_inner_comm]
  rfl

theorem complexToRealLin_adjoint {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    LinearMap.adjoint (complexToRealLin M) = complexToRealLin Mᴴ := by
  apply LinearMap.ext
  intro x
  apply ext_inner_left ℝ
  intro y
  rw [LinearMap.adjoint_inner_right, real_inner_comm, complexToRealLin_inner, real_inner_comm]

theorem complexToRealLin_diagonal_real {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) :
    LinearMap.det (complexToRealLin (Matrix.diagonal fun i => (d i : ℂ))) = (∏ i : ι, d i) ^ 2 := by
  let b := EuclideanSpace.basisFun (ι × Fin 2) ℝ
  rw [← LinearMap.det_toMatrix b.toBasis]
  have hmat : LinearMap.toMatrix b.toBasis b.toBasis
      (complexToRealLin (Matrix.diagonal fun i => (d i : ℂ))) =
      Matrix.diagonal (fun p : ι × Fin 2 => d p.1) := by
    ext p q
    rw [LinearMap.toMatrix_apply]
    have hbq : b.toBasis q = PiLp.single 2 q (1 : ℝ) := by
      ext r; simp [b, EuclideanSpace.basisFun_apply, PiLp.single_apply]
    have hev : complexToRealLin (Matrix.diagonal fun i => (d i : ℂ)) (b.toBasis q) =
        d q.1 • (b.toBasis q) := by
      rw [hbq]
      ext r
      simp only [complexToRealLin, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp,
        Matrix.mulVec_diagonal, PiLp.smul_apply, smul_eq_mul, PiLp.single_apply, Prod.ext_iff]
      rcases q with ⟨q1, q2⟩
      rcases r with ⟨r1, r2⟩
      by_cases hr1 : r1 = q1
      · subst hr1
        fin_cases q2 <;> fin_cases r2 <;> simp
      · simp [hr1]
    rw [hev, map_smul, Finsupp.smul_apply, smul_eq_mul, Matrix.diagonal_apply]
    have hrep : b.toBasis.repr (b.toBasis q) p = if p = q then 1 else 0 := by
      rw [Basis.repr_self, Finsupp.single_apply]
      simp only [eq_comm]
    rw [hrep]
    split_ifs with h
    · subst h; simp
    · simp
  rw [hmat, Matrix.det_diagonal, Fintype.prod_prod_type]
  simp_rw [Fin.prod_univ_two]
  rw [Finset.prod_mul_distrib, sq]

/-- **Exact Realification Determinant Theorem**: for any complex matrix `M : Matrix ι ι ℂ`,
`|det (complexToRealLin M)| = ‖M.det‖ ^ 2`. -/
theorem abs_det_complexToReal_eq_norm_det_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) :
    |LinearMap.det (complexToRealLin M)| = ‖M.det‖ ^ 2 := by
  have hsq : (LinearMap.det (complexToRealLin M)) ^ 2 = (‖M.det‖ ^ 2) ^ 2 := by
    have h1 : (LinearMap.det (complexToRealLin M)) ^ 2 =
        LinearMap.det (complexToRealLin (Mᴴ * M)) := by
      rw [sq]
      conv_lhs =>
        rhs
        rw [← linearMap_det_adjoint_real (complexToRealLin M), complexToRealLin_adjoint]
      rw [mul_comm, ← LinearMap.det_comp, ← complexToRealLin_mul]
    rw [h1]
    have hHerm : (Mᴴ * M).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self M
    let U : Matrix ι ι ℂ := (hHerm.eigenvectorUnitary : Matrix ι ι ℂ)
    let lam : ι → ℝ := hHerm.eigenvalues
    have hspec : Mᴴ * M = U * Matrix.diagonal (Complex.ofReal ∘ lam) * star U := by
      simpa [U, lam] using hHerm.spectral_theorem
    have hU : U * star U = 1 :=
      Matrix.mem_unitaryGroup_iff.mp hHerm.eigenvectorUnitary.prop
    have hdetU : LinearMap.det (complexToRealLin U) *
        LinearMap.det (complexToRealLin (star U)) = 1 := by
      rw [← LinearMap.det_comp, ← complexToRealLin_mul, hU,
        complexToRealLin_one, LinearMap.det_id]
    have hdetA : LinearMap.det (complexToRealLin (Mᴴ * M)) =
        (∏ i : ι, lam i) ^ 2 := by
      rw [hspec, complexToRealLin_mul, complexToRealLin_mul, LinearMap.det_comp,
        LinearMap.det_comp, mul_assoc,
        mul_comm (LinearMap.det (complexToRealLin (Matrix.diagonal _))),
        ← mul_assoc, hdetU, one_mul]
      simpa [Function.comp_def] using complexToRealLin_diagonal_real lam
    have hdetC : (((∏ i : ι, lam i : ℝ) : ℂ)) = ((Mᴴ * M).det) := by
      conv_rhs => rw [hspec]
      rw [Matrix.det_mul, Matrix.det_mul, mul_assoc, mul_comm (Matrix.diagonal _).det,
        ← mul_assoc, ← Matrix.det_mul, hU, Matrix.det_one, one_mul, Matrix.det_diagonal]
      simp
    have hdetM : ((Mᴴ * M).det) = ((‖M.det‖ ^ 2 : ℝ) : ℂ) := by
      rw [Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def,
        ← Complex.normSq_eq_norm_sq]
      apply Complex.ext <;> (simp [Complex.normSq_apply]; try ring)
    have hprod : ∏ i : ι, lam i = ‖M.det‖ ^ 2 :=
      Complex.ofReal_injective (hdetC.trans hdetM)
    rw [hdetA, hprod]
  have hsqrt := congrArg Real.sqrt hsq
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq (sq_nonneg _)] at hsqrt
  exact hsqrt

/-- Place-by-place block-diagonal real-linear map on
`EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)`. -/
def placeBlockLin {K ι : Type*} [Field K] [NumberField K] [Fintype ι] [DecidableEq ι]
    (T : InfinitePlace K → Matrix ι ι ℂ) :
    EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) →ₗ[ℝ]
      EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) where
  toFun x := WithLp.toLp 2 fun p =>
    complexToRealLin (T p.1) (WithLp.toLp 2 fun q => x (p.1, q)) p.2
  map_add' x y := by
    ext p
    have hxy : (WithLp.toLp 2 fun q : ι × Fin 2 => (x + y) (p.1, q)) =
        (WithLp.toLp 2 fun q => x (p.1, q)) + (WithLp.toLp 2 fun q => y (p.1, q)) := by
      ext q; rfl
    change (complexToRealLin (T p.1) _).ofLp p.2 =
      (complexToRealLin (T p.1) _).ofLp p.2 + (complexToRealLin (T p.1) _).ofLp p.2
    rw [hxy, map_add, PiLp.add_apply]
  map_smul' c x := by
    ext p
    have hcx : (WithLp.toLp 2 fun q : ι × Fin 2 => (c • x) (p.1, q)) =
        c • (WithLp.toLp 2 fun q => x (p.1, q)) := by
      ext q; rfl
    change (complexToRealLin (T p.1) _).ofLp p.2 =
      c * (complexToRealLin (T p.1) _).ofLp p.2
    rw [hcx, map_smul, PiLp.smul_apply, smul_eq_mul]

theorem placeBlockLin_one {K ι : Type*} [Field K] [NumberField K] [Fintype ι] [DecidableEq ι] :
    placeBlockLin (K := K) (fun _ => (1 : Matrix ι ι ℂ)) = LinearMap.id := by
  ext x p
  change (complexToRealLin (1 : Matrix ι ι ℂ) _).ofLp p.2 = x p
  rw [complexToRealLin_one, LinearMap.id_apply]

theorem placeBlockLin_mul {K ι : Type*} [Field K] [NumberField K] [Fintype ι] [DecidableEq ι]
    (T₁ T₂ : InfinitePlace K → Matrix ι ι ℂ) :
    placeBlockLin (K := K) (fun v => T₁ v * T₂ v) =
      (placeBlockLin T₁).comp (placeBlockLin T₂) := by
  ext x p
  change (complexToRealLin (T₁ p.1 * T₂ p.1) _).ofLp p.2 =
    (complexToRealLin (T₁ p.1) _).ofLp p.2
  rw [complexToRealLin_mul, LinearMap.comp_apply]
  rfl

theorem det_placeBlockLin {K ι : Type*} [Field K] [NumberField K] [Fintype ι] [DecidableEq ι]
    (T : InfinitePlace K → Matrix ι ι ℂ) :
    LinearMap.det (placeBlockLin (K := K) T) =
      ∏ v : InfinitePlace K, LinearMap.det (complexToRealLin (T v)) := by
  classical
  let b := EuclideanSpace.basisFun (InfinitePlace K × ι × Fin 2) ℝ
  let bV := EuclideanSpace.basisFun (ι × Fin 2) ℝ
  let eSwap : (InfinitePlace K × ι × Fin 2) ≃ ((ι × Fin 2) × InfinitePlace K) :=
    Equiv.prodComm _ _
  let bSwap := b.toBasis.reindex eSwap
  rw [← LinearMap.det_toMatrix bSwap]
  have hmat : LinearMap.toMatrix bSwap bSwap (placeBlockLin (K := K) T) =
      Matrix.blockDiagonal (fun v => LinearMap.toMatrix bV.toBasis bV.toBasis
        (complexToRealLin (T v))) := by
    ext p q
    rw [LinearMap.toMatrix_apply, Matrix.blockDiagonal_apply]
    simp only [bSwap, Basis.reindex_apply, Basis.repr_reindex_apply]
    have hbq : b.toBasis (eSwap.symm q) = PiLp.single 2 (eSwap.symm q) (1 : ℝ) := by
      ext r; simp [b, EuclideanSpace.basisFun_apply, PiLp.single_apply]
    by_cases hpq : p.2 = q.2
    · rw [if_pos hpq]
      have hev : (WithLp.toLp 2 fun r : ι × Fin 2 =>
          (b.toBasis (eSwap.symm q)) (q.2, r)) = bV.toBasis q.1 := by
        rw [hbq]
        ext r
        simp [bV, EuclideanSpace.basisFun_apply, PiLp.single_apply, Prod.ext_iff, eSwap]
      have heval : b.toBasis.repr (placeBlockLin (K := K) T (b.toBasis (eSwap.symm q)))
          (eSwap.symm p) =
          bV.toBasis.repr (complexToRealLin (T q.2) (bV.toBasis q.1)) p.1 := by
        have h1 : ∀ f : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2),
            b.toBasis.repr f (eSwap.symm p) = f (p.2, p.1) := fun f => by
          change b.toBasis.repr f (p.2, p.1) = f (p.2, p.1)
          simp [b, EuclideanSpace.basisFun_repr]
        have h2 : ∀ g : EuclideanSpace ℝ (ι × Fin 2),
            bV.toBasis.repr g p.1 = g p.1 := fun g => by
          simp [bV, EuclideanSpace.basisFun_repr]
        rw [h1, h2]
        change (complexToRealLin (T p.2) (WithLp.toLp 2 fun r =>
          (b.toBasis (eSwap.symm q)) (p.2, r))).ofLp p.1 = _
        rw [hpq, hev]
      rw [heval, hpq, LinearMap.toMatrix_apply]
    · rw [if_neg hpq]
      have hzero : (WithLp.toLp 2 fun r : ι × Fin 2 =>
          (b.toBasis (eSwap.symm q)) (p.2, r)) = 0 := by
        rw [hbq]
        ext r
        simp [Prod.ext_iff, hpq, eSwap]
      have h1 : b.toBasis.repr (placeBlockLin (K := K) T (b.toBasis (eSwap.symm q)))
          (eSwap.symm p) = 0 := by
        have hb : b.toBasis.repr (placeBlockLin (K := K) T (b.toBasis (eSwap.symm q)))
            (eSwap.symm p) = (placeBlockLin (K := K) T (b.toBasis (eSwap.symm q))) (p.2, p.1) := by
          change b.toBasis.repr _ (p.2, p.1) = _
          simp [b, EuclideanSpace.basisFun_repr]
        rw [hb]
        change (complexToRealLin (T p.2) (WithLp.toLp 2 fun r =>
          (b.toBasis (eSwap.symm q)) (p.2, r))).ofLp p.1 = 0
        rw [hzero, map_zero]
        rfl
      exact h1
  rw [hmat, Matrix.det_blockDiagonal]
  refine Finset.prod_congr rfl fun v _ => ?_
  exact LinearMap.det_toMatrix bV.toBasis (complexToRealLin (T v))

theorem abs_det_placeBlockLin {K ι : Type*} [Field K] [NumberField K] [Fintype ι] [DecidableEq ι]
    (T : InfinitePlace K → Matrix ι ι ℂ) :
    |LinearMap.det (placeBlockLin (K := K) T)| =
      ∏ v : InfinitePlace K, ‖(T v).det‖ ^ 2 := by
  rw [det_placeBlockLin, Finset.abs_prod]
  exact Finset.prod_congr rfl fun v _ => abs_det_complexToReal_eq_norm_det_sq (T v)

end RealificationDet

section CovolumeMapAndQFrameDegree

theorem discreteTopology_map_linearEquiv {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    (Λ : Submodule ℤ E₁) [DiscreteTopology Λ]
    (e : E₁ ≃ₗ[ℝ] E₂) :
    DiscreteTopology (Λ.map (e.toLinearMap.restrictScalars ℤ)) := by
  let Λ' := Λ.map (e.toLinearMap.restrictScalars ℤ)
  let eqZ : Λ ≃ₗ[ℤ] Λ' :=
    { toFun := fun x => ⟨e x.1, x.1, x.2, rfl⟩
      invFun := fun y => ⟨e.symm y.1, by
        rcases y.2 with ⟨x, hx, hxy⟩
        have hx' : e.symm y.1 = x := by rw [← hxy]; exact e.symm_apply_apply x
        rwa [hx']⟩
      map_add' := fun x y => Subtype.ext (map_add e x.1 y.1)
      map_smul' := fun c x => Subtype.ext (map_zsmul e c x.1)
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y.1) }
  refine DiscreteTopology.of_continuous_injective (f := eqZ.symm) ?_ eqZ.symm.injective
  exact Continuous.subtype_mk
    (e.symm.toLinearMap.continuous_of_finiteDimensional.comp continuous_subtype_val) _

theorem span_top_map_linearEquiv {E₁ E₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    (Λ : Submodule ℤ E₁) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (e : E₁ ≃ₗ[ℝ] E₂) :
    Submodule.span ℝ ((Λ.map (e.toLinearMap.restrictScalars ℤ)) : Set E₂) = ⊤ := by
  have h1 : Submodule.span ℝ ((Λ.map (e.toLinearMap.restrictScalars ℤ)) : Set E₂) =
      (Submodule.span ℝ (Λ : Set E₁)).map e.toLinearMap := by
    rw [Submodule.map_span]; rfl
  rw [h1, IsZLattice.span_top (K := ℝ) (L := Λ), Submodule.map_top, LinearEquiv.range]

/-- Covolume transformation of a full-rank `ℤ`-lattice `Λ` to any `ℤ`-lattice `Λ'` agreeing
with `e '' Λ` under an `ℝ`-linear automorphism `e`. -/
theorem covol_eq_abs_det_of_eq_image {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (Λ Λ' : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (e : E ≃ₗ[ℝ] E) (hmem : ∀ y : E, y ∈ Λ' ↔ ∃ x ∈ Λ, e x = y) :
    covol Λ' = |LinearMap.det e.toLinearMap| * covol Λ := by
  let eqZ : Λ ≃ₗ[ℤ] Λ' :=
    { toFun := fun x => ⟨e x.1, (hmem (e x.1)).mpr ⟨x.1, x.2, rfl⟩⟩
      invFun := fun y => ⟨e.symm y.1, by
        obtain ⟨x, hx, hxy⟩ := (hmem y.1).mp y.2
        rwa [show e.symm y.1 = x from by rw [← hxy]; exact e.symm_apply_apply x]⟩
      map_add' := fun x y => Subtype.ext (map_add e x.1 y.1)
      map_smul' := fun c x => Subtype.ext (map_zsmul e c x.1)
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y.1) }
  have hDisc : DiscreteTopology Λ' := by
    refine DiscreteTopology.of_continuous_injective (f := eqZ.symm) ?_ eqZ.symm.injective
    exact Continuous.subtype_mk
      (e.symm.toLinearMap.continuous_of_finiteDimensional.comp continuous_subtype_val) _
  have hsp' : Submodule.span ℝ (Λ' : Set E) = ⊤ := by
    have h1 : Submodule.span ℝ (Λ' : Set E) =
        (Submodule.span ℝ (Λ : Set E)).map e.toLinearMap := by
      apply le_antisymm
      · refine Submodule.span_le.mpr ?_
        intro y hy
        obtain ⟨x, hx, rfl⟩ := (hmem y).mp hy
        exact ⟨x, Submodule.subset_span hx, rfl⟩
      · refine Submodule.map_le_iff_le_comap.mpr (Submodule.span_le.mpr fun x hx => ?_)
        exact Submodule.subset_span ((hmem (e x)).mpr ⟨x, hx, rfl⟩)
    rw [h1, IsZLattice.span_top (K := ℝ) (L := Λ), Submodule.map_top, LinearEquiv.range]
  have : DiscreteTopology Λ' := hDisc
  have : IsZLattice ℝ Λ' := ⟨hsp'⟩
  have hrk : rk Λ = Module.finrank ℝ E := ZLattice.rank ℝ Λ
  let bΛ := (Module.finBasis ℤ Λ).reindex (finCongr hrk)
  let bΛ' := bΛ.map eqZ
  let u := (stdOrthonormalBasis ℝ E).toBasis
  let M : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun i j => u.repr (bΛ j : E) i
  have hM : ∀ j, (bΛ j : E) = ∑ i, M i j • u i := fun j => by
    have := (u.sum_repr (bΛ j : E)).symm
    simp only [M]
    exact this
  have hgramΛ : Matrix.gram ℝ (fun j => (bΛ j : E)) = Mᵀ * M := by
    ext i j
    simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply]
    rw [hM i, hM j, sum_inner]
    simp_rw [inner_sum, real_inner_smul_left, real_inner_smul_right]
    have horth : ∀ a b, ⟪u a, u b⟫_ℝ = if a = b then 1 else 0 := fun a b => by
      simp [u, OrthonormalBasis.inner_eq_ite]
    simp_rw [horth]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp
  let A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    LinearMap.toMatrix u u e.toLinearMap
  have hAM : ∀ j, ((bΛ' j : Λ') : E) = ∑ k, (A * M) k j • u k := fun j => by
    change e (bΛ j : E) = _
    rw [hM j, map_sum]
    simp_rw [map_smul]
    have heu : ∀ i, e (u i) = ∑ k, A k i • u k := fun i => by
      have := (u.sum_repr (e (u i))).symm
      simp only [A, LinearMap.toMatrix_apply]
      exact this
    simp_rw [heu, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    simp [Matrix.mul_apply, mul_comm]
  have hgramΛ' : Matrix.gram ℝ (fun j => ((bΛ' j : Λ') : E)) = (A * M)ᵀ * (A * M) := by
    ext i j
    simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply]
    rw [hAM i, hAM j, sum_inner]
    simp_rw [inner_sum, real_inner_smul_left, real_inner_smul_right]
    have horth : ∀ a b, ⟪u a, u b⟫_ℝ = if a = b then 1 else 0 := fun a b => by
      simp [u, OrthonormalBasis.inner_eq_ite]
    simp_rw [horth]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Matrix.mul_apply]
  rw [covol_eq_sqrt_det_gram Λ' bΛ', covol_eq_sqrt_det_gram Λ bΛ, hgramΛ', hgramΛ]
  simp only [Matrix.det_mul, Matrix.det_transpose]
  rw [show (A.det * M.det) * (A.det * M.det) = (A.det * M.det) ^ 2 by ring,
    Real.sqrt_sq_eq_abs, show M.det * M.det = M.det ^ 2 by ring, Real.sqrt_sq_eq_abs,
    abs_mul, LinearMap.det_toMatrix]

/-- Covolume transformation of a full-rank `ℤ`-lattice `Λ` under an `ℝ`-linear automorphism `e`. -/
theorem covol_map_linearEquiv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (e : E ≃ₗ[ℝ] E) :
    covol (Λ.map (e.toLinearMap.restrictScalars ℤ)) =
      |LinearMap.det e.toLinearMap| * covol Λ :=
  covol_eq_abs_det_of_eq_image Λ (Λ.map (e.toLinearMap.restrictScalars ℤ)) e
    (fun y => by simp only [Submodule.mem_map]; exact ⟨fun ⟨x, hx, hxy⟩ => ⟨x, hx, hxy⟩, fun ⟨x, hx, hxy⟩ => ⟨x, hx, hxy⟩⟩)

/-- Frame-changed `NumberFieldHLat K` with the same `(V, ι, b, L)` and a new invertible
archimedean frame `X'`. -/
def changeFrame {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    (A : NumberFieldHLat K) (X' : InfinitePlace K → Matrix A.ι A.ι ℂ)
    (hX' : ∀ v, IsUnit (X' v).det) : NumberFieldHLat K :=
  let T : InfinitePlace K → Matrix A.ι A.ι ℂ := fun v => (X' v)⁻¹ * A.X v
  let Tinv : InfinitePlace K → Matrix A.ι A.ι ℂ := fun v => (A.X v)⁻¹ * X' v
  let e : EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2) ≃ₗ[ℝ]
      EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2) :=
    { toLinearMap := placeBlockLin T
      invFun := placeBlockLin Tinv
      left_inv := fun x => by
        have h1 : (placeBlockLin Tinv).comp (placeBlockLin T) = LinearMap.id := by
          rw [← placeBlockLin_mul]
          convert placeBlockLin_one (K := K) (ι := A.ι) using 2
          funext v
          simp only [Tinv, T, Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (X' v) (X' v)⁻¹ (A.X v),
            Matrix.mul_nonsing_inv _ (hX' v), Matrix.one_mul,
            Matrix.nonsing_inv_mul _ (A.hX v)]
        exact LinearMap.congr_fun h1 x
      right_inv := fun x => by
        have h1 : (placeBlockLin T).comp (placeBlockLin Tinv) = LinearMap.id := by
          rw [← placeBlockLin_mul]
          convert placeBlockLin_one (K := K) (ι := A.ι) using 2
          funext v
          simp only [T, Tinv, Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (A.X v) (A.X v)⁻¹ (X' v),
            Matrix.mul_nonsing_inv _ (A.hX v), Matrix.one_mul,
            Matrix.nonsing_inv_mul _ (hX' v)]
        exact LinearMap.congr_fun h1 x }
  have hrealize : ∀ x : A.V, realizeHLat A.b X' x = e (realizeHLat A.b A.X x) := by
    intro x
    ext p
    have hmul : fcoord A.b X' p.1 x = (T p.1) *ᵥ fcoord A.b A.X p.1 x := by
      simp only [T, fcoord, Matrix.mulVec_mulVec, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (A.hX p.1), Matrix.mul_one]
    have hz : (fun j : A.ι => (⟨(realizeHLat A.b A.X x) (p.1, j, 0),
        (realizeHLat A.b A.X x) (p.1, j, 1)⟩ : ℂ)) =
        fcoord A.b A.X p.1 x := by
      funext j
      apply Complex.ext <;> simp [realizeHLat]
    change (if p.2.2 = 0 then (fcoord A.b X' p.1 x p.2.1).re
        else (fcoord A.b X' p.1 x p.2.1).im) =
      (if p.2.2 = 0 then ((T p.1 *ᵥ fun j => ⟨(realizeHLat A.b A.X x) (p.1, j, 0),
          (realizeHLat A.b A.X x) (p.1, j, 1)⟩) p.2.1).re
        else ((T p.1 *ᵥ fun j => ⟨(realizeHLat A.b A.X x) (p.1, j, 0),
          (realizeHLat A.b A.X x) (p.1, j, 1)⟩) p.2.1).im)
    rw [hz, ← hmul]
  have hsub : (A.L.restrictScalars ℤ).map (realizeHLat A.b X').toIntLinearMap =
      A.zRealize.map (e.toLinearMap.restrictScalars ℤ) := by
    ext y
    simp only [Submodule.mem_map, NumberFieldHLat.zRealize]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨realizeHLat A.b A.X x, ⟨x, hx, rfl⟩, (hrealize x).symm⟩
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, hrealize x⟩
  have hsp : Submodule.span ℝ
      (((A.L.restrictScalars ℤ).map (realizeHLat A.b X').toIntLinearMap) :
        Set (EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2))) = ⊤ := by
    rw [hsub]
    exact span_top_map_linearEquiv A.zRealize e
  { V := A.V
    ι := A.ι
    b := A.b
    X := X'
    hX := hX'
    L := A.L
    discReal := by
      rw [hsub]
      exact discreteTopology_map_linearEquiv A.zRealize e
    zlatReal := by
      let : DiscreteTopology ((A.L.restrictScalars ℤ).map (realizeHLat A.b X').toIntLinearMap) := by
        rw [hsub]; exact discreteTopology_map_linearEquiv A.zRealize e
      exact ⟨hsp⟩ }

/-- Standard-frame `NumberFieldHLat K` (`X = fun _ => 1`) associated to `A`. -/
def stdFrame {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    (A : NumberFieldHLat K) : NumberFieldHLat K :=
  changeFrame A (fun _ => 1) (fun _ => by simp)

theorem covol_changeFrame {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    (A : NumberFieldHLat K) (X' : InfinitePlace K → Matrix A.ι A.ι ℂ)
    (hX' : ∀ v, IsUnit (X' v).det) :
    covol (changeFrame A X' hX').zRealize =
      (∏ v : InfinitePlace K, ‖(A.X v).det‖ ^ 2 / ‖(X' v).det‖ ^ 2) * covol A.zRealize := by
  let T : InfinitePlace K → Matrix A.ι A.ι ℂ := fun v => (X' v)⁻¹ * A.X v
  let Tinv : InfinitePlace K → Matrix A.ι A.ι ℂ := fun v => (A.X v)⁻¹ * X' v
  let e : EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2) ≃ₗ[ℝ]
      EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2) :=
    { toLinearMap := placeBlockLin T
      invFun := placeBlockLin Tinv
      left_inv := fun x => by
        have h1 : (placeBlockLin Tinv).comp (placeBlockLin T) = LinearMap.id := by
          rw [← placeBlockLin_mul]
          convert placeBlockLin_one (K := K) (ι := A.ι) using 2
          funext v
          simp only [Tinv, T, Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (X' v) (X' v)⁻¹ (A.X v),
            Matrix.mul_nonsing_inv _ (hX' v), Matrix.one_mul,
            Matrix.nonsing_inv_mul _ (A.hX v)]
        exact LinearMap.congr_fun h1 x
      right_inv := fun x => by
        have h1 : (placeBlockLin T).comp (placeBlockLin Tinv) = LinearMap.id := by
          rw [← placeBlockLin_mul]
          convert placeBlockLin_one (K := K) (ι := A.ι) using 2
          funext v
          simp only [T, Tinv, Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (A.X v) (A.X v)⁻¹ (X' v),
            Matrix.mul_nonsing_inv _ (A.hX v), Matrix.one_mul,
            Matrix.nonsing_inv_mul _ (hX' v)]
        exact LinearMap.congr_fun h1 x }
  have hrealize : ∀ x : A.V, realizeHLat A.b X' x = e (realizeHLat A.b A.X x) := by
    intro x
    ext p
    have hmul : fcoord A.b X' p.1 x = (T p.1) *ᵥ fcoord A.b A.X p.1 x := by
      simp only [T, fcoord, Matrix.mulVec_mulVec, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (A.hX p.1), Matrix.mul_one]
    have hz : (fun j : A.ι => (⟨(realizeHLat A.b A.X x) (p.1, j, 0),
        (realizeHLat A.b A.X x) (p.1, j, 1)⟩ : ℂ)) =
        fcoord A.b A.X p.1 x := by
      funext j
      apply Complex.ext <;> simp [realizeHLat]
    change (if p.2.2 = 0 then (fcoord A.b X' p.1 x p.2.1).re
        else (fcoord A.b X' p.1 x p.2.1).im) =
      (if p.2.2 = 0 then ((T p.1 *ᵥ fun j => ⟨(realizeHLat A.b A.X x) (p.1, j, 0),
          (realizeHLat A.b A.X x) (p.1, j, 1)⟩) p.2.1).re
        else ((T p.1 *ᵥ fun j => ⟨(realizeHLat A.b A.X x) (p.1, j, 0),
          (realizeHLat A.b A.X x) (p.1, j, 1)⟩) p.2.1).im)
    rw [hz, ← hmul]
  have hcov := covol_eq_abs_det_of_eq_image A.zRealize (changeFrame A X' hX').zRealize e
    (fun y => by
      change y ∈ (A.L.restrictScalars ℤ).map (realizeHLat A.b X').toIntLinearMap ↔
        ∃ x ∈ A.zRealize, e x = y
      simp only [Submodule.mem_map, NumberFieldHLat.zRealize]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨realizeHLat A.b A.X x, ⟨x, hx, rfl⟩, (hrealize x).symm⟩
      · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, hrealize x⟩)
  rw [show e.toLinearMap = placeBlockLin T from rfl, abs_det_placeBlockLin] at hcov
  refine hcov.trans ?_
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  simp only [T, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', norm_mul, norm_inv,
    mul_pow, inv_pow]
  ring

theorem finrank_eq_two_mul_card_infinitePlace (K : Type) [Field K] [NumberField K]
    [IsTotallyComplex K] :
    Module.finrank ℚ K = 2 * Fintype.card (InfinitePlace K) := by
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank K
  have h2 := IsTotallyComplex.nrRealPlaces_eq_zero K
  have h3 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
  rw [h2, zero_add] at h1 h3
  rw [← h1, h3]

theorem rk_zRealize {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    (A : NumberFieldHLat K) :
    rk A.zRealize = Module.finrank ℚ K * Fintype.card A.ι := by
  unfold ArakelovCovolume.rk
  rw [ZLattice.rank ℝ A.zRealize,
    (euclideanSpaceCongr (Fintype.equivFin (InfinitePlace K × A.ι × Fin 2))).toLinearEquiv.finrank_eq,
    finrank_euclideanSpace_fin, Fintype.card_prod, Fintype.card_prod, Fintype.card_fin,
    finrank_eq_two_mul_card_infinitePlace K]
  ring

/-- **`q_frame_degree` (Arbitrary-Rank Frame Change Identity)**:
for any `A : NumberFieldHLat K`, changing from frame `A.X` to `X'` shifts `(rank A) * A.mu`
by `(1 / nPl K) * ∑ v, (log ‖(X' v).det‖^2 - log ‖(A.X v).det‖^2)`. -/
theorem mu_changeFrame {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    (A : NumberFieldHLat K) [Nonempty A.ι] (X' : InfinitePlace K → Matrix A.ι A.ι ℂ)
    (hX' : ∀ v, IsUnit (X' v).det) :
    (Fintype.card A.ι : ℝ) * (changeFrame A X' hX').mu =
      (Fintype.card A.ι : ℝ) * A.mu +
        (1 / (Fintype.card (InfinitePlace K) : ℝ)) *
          ∑ v : InfinitePlace K, (Real.log (‖(X' v).det‖ ^ 2) - Real.log (‖(A.X v).det‖ ^ 2)) := by
  have hrpos : (0 : ℝ) < (Fintype.card A.ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hnpos : (0 : ℝ) < (Fintype.card (InfinitePlace K) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hdK : (Module.finrank ℚ K : ℝ) = 2 * (Fintype.card (InfinitePlace K) : ℝ) := by
    exact_mod_cast finrank_eq_two_mul_card_infinitePlace K
  have hdetA : ∀ v, 0 < ‖(A.X v).det‖ ^ 2 := fun v =>
    pow_pos (norm_pos_iff.mpr (A.hX v).ne_zero) 2
  have hdetX' : ∀ v, 0 < ‖(X' v).det‖ ^ 2 := fun v =>
    pow_pos (norm_pos_iff.mpr (hX' v).ne_zero) 2
  have hcov := covol_changeFrame A X' hX'
  have hlog : Real.log (covol (changeFrame A X' hX').zRealize) =
      (∑ v : InfinitePlace K, (Real.log (‖(A.X v).det‖ ^ 2) - Real.log (‖(X' v).det‖ ^ 2))) +
        Real.log (covol A.zRealize) := by
    rw [hcov, Real.log_mul (Finset.prod_pos fun v _ => div_pos (hdetA v) (hdetX' v)).ne'
      (covol_pos A.zRealize).ne', Real.log_prod (fun v _ => (div_pos (hdetA v) (hdetX' v)).ne')]
    congr 1
    refine Finset.sum_congr rfl fun v _ => Real.log_div (hdetA v).ne' (hdetX' v).ne'
  unfold NumberFieldHLat.mu ArakelovCovolume.slope ArakelovCovolume.degAr
  rw [rk_zRealize A, rk_zRealize (changeFrame A X' hX')]
  change (Fintype.card A.ι : ℝ) * (2 * (-Real.log (covol (changeFrame A X' hX').zRealize) /
      ((Module.finrank ℚ K * Fintype.card A.ι : ℕ) : ℝ)) - Real.log 2 +
      NumberFieldHLat.logDiscDivDeg K) = _
  rw [hlog, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  push_cast
  rw [hdK]
  field_simp [hrpos.ne', hnpos.ne']
  ring

/-- **`q_frame_degree`** (`ClassMapArchimedean.q_frame_degree`):
for any `A : NumberFieldHLat K` with `Nonempty A.ι`,
`r * A.mu = r * (stdFrame A).mu + (1 / nPl K) * ∑ v, Real.log (‖(A.X v).det‖ ^ 2)`. -/
theorem q_frame_degree {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    (A : NumberFieldHLat K) [Nonempty A.ι] :
    (Fintype.card A.ι : ℝ) * A.mu =
      (Fintype.card A.ι : ℝ) * (stdFrame A).mu +
        (1 / (Fintype.card (InfinitePlace K) : ℝ)) *
          ∑ v : InfinitePlace K, Real.log (‖(A.X v).det‖ ^ 2) := by
  have h := mu_changeFrame A (fun _ => 1) (fun _ => by simp)
  simp only [Matrix.det_one, norm_one, one_pow, Real.log_one, zero_sub, Finset.sum_neg_distrib] at h
  change (Fintype.card A.ι : ℝ) * (stdFrame A).mu = _ at h
  linarith

/-- **`q_frame_degree` (Gram-Determinant Form)**:
`r * A.mu = r * (stdFrame A).mu - (1 / nPl K) * ∑ v, Real.log ((gramJ A A.b v).det.re)`. -/
theorem q_frame_degree_gramJ {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    (A : NumberFieldHLat K) [Nonempty A.ι] :
    (Fintype.card A.ι : ℝ) * A.mu =
      (Fintype.card A.ι : ℝ) * (stdFrame A).mu -
        (1 / (Fintype.card (InfinitePlace K) : ℝ)) *
          ∑ v : InfinitePlace K, Real.log ((gramJ A A.b v).det.re) := by
  rw [q_frame_degree A]
  have hsum : ∑ v : InfinitePlace K, Real.log ((gramJ A A.b v).det.re) =
      -∑ v : InfinitePlace K, Real.log (‖(A.X v).det‖ ^ 2) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [gramJ_self_det A v, Real.log_inv]
  rw [hsum]
  ring

end CovolumeMapAndQFrameDegree

end ArchimedeanFramesAndQFrameDegree

/-! ## Section 4: Monomial Lattices, Orthogonal Decomposition & `monomial_lattice_muMax_le` -/

section MonomialLatticeMuMax

open RHDirect.ArakelovCovolume (rk covol degAr slope muMax
  discreteTopology_of_le covol_eq_sqrt_det_gram covol_pos rk_pos_of_ne_bot
  covol_le_of_le_same_rank gram_sum_smul_eq_transpose_mul gram_det_le
  bost_slope_inequality det_gram_basis_pos)
open RHDirect.Stage4ArakelovBost (IsSaturated projOrth quotLat
  discreteTopology_of_fin_basis_real_li discreteTopology_quotLat
  rk_add_quotLat covol_eq_mul_quotLat degAr_eq_add_quotLat norm_projOrth_le)
open RHDirect.Stage10GeometryOfNumbers (basisOfZLattice covolume_eq_abs_det)
open RHDirect.Stage12SchurWeylLattices (vecAt fcoord normAt realizeHLat norm_sq_realizeHLat
  NumberFieldHLat euclideanSpaceCongr)

/-- Realized `ℤ`-lattice of any `𝓞 K`-submodule `L ≤ V` in frame `(b, X)`. -/
abbrev zRealizeMod {K : Type} {V ι : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (L : Submodule (𝓞 K) V) :
    Submodule ℤ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) :=
  (L.restrictScalars ℤ).map (realizeHLat b X).toIntLinearMap

/-- Normalized `𝓞 K`-submodule Arakelov slope `muOK` (matching `Formalism.HN.muDef`). -/
def muOK {K : Type} {V ι : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (N : Submodule (𝓞 K) V) : ℝ :=
  2 * ArakelovCovolume.slope (zRealizeMod b X N) - Real.log 2 + NumberFieldHLat.logDiscDivDeg K

/-- Normalized maximal `𝓞 K`-submodule slope `muMaxOK` (matching `Formalism.HN.muMaxDef`):
`sup { muOK b X N | 0 ≠ N ≤ L, N : Submodule (𝓞 K) V }`. -/
def muMaxOK {K : Type} {V ι : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (L : Submodule (𝓞 K) V) : ℝ :=
  sSup { t | ∃ N : Submodule (𝓞 K) V, N ≤ L ∧ N ≠ ⊥ ∧ muOK b X N = t }

theorem muOK_eq_mu {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    (A : NumberFieldHLat K) :
    muOK A.b A.X A.L = A.mu := by
  unfold muOK NumberFieldHLat.mu
  rfl

theorem muMaxOK_le_muMax {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    (A : NumberFieldHLat K) (hAne : A.L ≠ ⊥) :
    muMaxOK A.b A.X A.L ≤ A.muMax := by
  have hne : ∃ N : Submodule (𝓞 K) A.V, N ≤ A.L ∧ N ≠ ⊥ ∧ muOK A.b A.X N = A.mu :=
    ⟨A.L, le_rfl, hAne, muOK_eq_mu A⟩
  refine csSup_le ⟨A.mu, hne⟩ ?_
  rintro t ⟨N, hNL, hN0, rfl⟩
  have hsub : zRealizeMod A.b A.X N ≤ A.zRealize := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, hNL hx, rfl⟩
  have hNz : zRealizeMod A.b A.X N ≠ ⊥ := by
    intro hbot
    apply hN0
    rw [eq_bot_iff]
    intro x hx
    have hx0 : realizeHLat A.b A.X x = 0 := by
      have hmem : realizeHLat A.b A.X x ∈ zRealizeMod A.b A.X N := ⟨x, hx, rfl⟩
      rw [hbot, Submodule.mem_bot] at hmem
      exact hmem
    have hn0 : ∑ v : InfinitePlace K, normAt A.b A.X v x ^ 2 = 0 := by
      rw [← norm_sq_realizeHLat, hx0, norm_zero, sq, zero_mul]
    have hvn : ∀ v : InfinitePlace K, normAt A.b A.X v x = 0 := fun v => by
      have := Finset.sum_eq_zero_iff_of_nonneg (fun w _ => sq_nonneg (normAt A.b A.X w x)) |>.mp
        hn0 v (Finset.mem_univ v)
      exact sq_eq_zero_iff.mp this
    obtain ⟨v₀⟩ := (inferInstance : Nonempty (InfinitePlace K))
    have hf0 : fcoord A.b A.X v₀ x = 0 := by
      funext i
      have hsum0 := hvn v₀
      unfold normAt at hsum0
      rw [Real.sqrt_eq_zero (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at hsum0
      have hi := Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖fcoord A.b A.X v₀ x j‖)
        |>.mp hsum0 i (Finset.mem_univ i)
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hi)
    have hvec0 : vecAt A.b v₀ x = 0 := by
      have := congrArg (Matrix.mulVec (A.X v₀)) hf0
      simp only [fcoord, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (A.hX v₀),
        Matrix.one_mulVec, Matrix.mulVec_zero] at this
      exact this
    rw [Submodule.mem_bot, ← A.b.sum_repr x]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hi := congrFun hvec0 i
    simp only [vecAt, Pi.zero_apply, map_eq_zero] at hi
    rw [hi, zero_smul]
  have hle := ArakelovCovolume.slope_le_muMax A.zRealize (zRealizeMod A.b A.X N) hsub hNz
  unfold muOK NumberFieldHLat.muMax
  linarith

/-- Diagonal monomial frame `monX w` with metric weights `w : MonI → ℝ`. -/
def monX {K MonI : Type*} [Field K] [NumberField K] [DecidableEq MonI]
    (w : MonI → ℝ) : InfinitePlace K → Matrix MonI MonI ℂ :=
  fun _ => Matrix.diagonal fun m => (((Real.sqrt (w m))⁻¹ : ℝ) : ℂ)

theorem isUnit_det_monX {K MonI : Type*} [Field K] [NumberField K] [Fintype MonI] [DecidableEq MonI]
    (w : MonI → ℝ) (hw : ∀ m, 0 < w m) (v : InfinitePlace K) :
    IsUnit ((monX (K := K) w v).det) := by
  rw [monX, Matrix.det_diagonal]
  refine IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun m _ => ?_)
  exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_pos.mpr (hw m)).ne')

theorem normAt_monX_sq {K MonI : Type*} [Field K] [NumberField K] [Fintype MonI] [DecidableEq MonI]
    (w : MonI → ℝ) (hw : ∀ m, 0 < w m) (v : InfinitePlace K) (x : MonI → K) :
    normAt (Pi.basisFun K MonI) (monX (K := K) w) v x ^ 2 =
      ∑ m : MonI, w m * ‖v.embedding (x m)‖ ^ 2 := by
  unfold normAt
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hinv : (monX (K := K) w v)⁻¹ = Matrix.diagonal fun j => ((Real.sqrt (w j) : ℝ) : ℂ) := by
    apply Matrix.inv_eq_right_inv
    rw [monX, Matrix.diagonal_mul_diagonal]
    ext a b
    simp only [Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs with h
    · subst h
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ (Real.sqrt_pos.mpr (hw a)).ne', Complex.ofReal_one]
    · rfl
  have hfc : fcoord (Pi.basisFun K MonI) (monX (K := K) w) v x m =
      ((Real.sqrt (w m) : ℝ) : ℂ) * v.embedding (x m) := by
    unfold fcoord vecAt
    rw [hinv, Matrix.mulVec_diagonal]
    simp [Pi.basisFun_repr]
  rw [hfc, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (hw m).le]

/-- Standard monomial `𝓞 K`-lattice `⨆ m, 𝓞 K ∙ e_m` inside `MonI → K`. -/
def stdMonomialLat (K MonI : Type*) [Field K] [NumberField K] [Fintype MonI] [DecidableEq MonI] :
    Submodule (𝓞 K) (MonI → K) :=
  ⨆ m : MonI, Submodule.span (𝓞 K) {Pi.single m (1 : K)}

/-- `FractionalIdeal`-rescaled submodule `idealSmul I L := { ∑ i, a_i • x_i | a_i ∈ I, x_i ∈ L }`. -/
def idealSmul {K : Type*} {V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (I : Submodule (𝓞 K) K) (L : Submodule (𝓞 K) V) : Submodule (𝓞 K) V :=
  Submodule.span (𝓞 K) { y : V | ∃ a ∈ I, ∃ x ∈ L, y = a • x }

theorem idealSmul_stdMonomial_eq {K MonI : Type*} [Field K] [NumberField K]
    [Fintype MonI] [DecidableEq MonI] (I : Submodule (𝓞 K) K) :
    idealSmul I (stdMonomialLat K MonI) =
      ⨆ m : MonI, I.map ((LinearMap.toSpanSingleton K (MonI → K) (Pi.single m (1 : K))).restrictScalars (𝓞 K)) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro y ⟨a, ha, x, hx, rfl⟩
    have hcoord : ∀ m : MonI, x m ∈ (1 : Submodule (𝓞 K) K) := by
      let S : Submodule (𝓞 K) (MonI → K) :=
        { carrier := { z | ∀ m, z m ∈ (1 : Submodule (𝓞 K) K) }
          add_mem' := fun h1 h2 m => add_mem (h1 m) (h2 m)
          zero_mem' := fun _ => zero_mem _
          smul_mem' := fun r _ h m => smul_mem _ r (h m) }
      have hle : stdMonomialLat K MonI ≤ S := by
        refine iSup_le fun m => Submodule.span_le.mpr ?_
        rintro z hz m'
        rw [Set.mem_singleton_iff] at hz
        subst hz
        by_cases hm : m' = m
        · subst hm; simp
        · simp [hm]
      exact hle hx
    have hdec : a • x = ∑ m : MonI, (a * x m) • Pi.single m (1 : K) := by
      ext m'
      simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.single_apply]
      rw [Finset.sum_eq_single m']
      · simp
      · intro m _ hm; simp [Ne.symm hm]
      · intro hm; exact absurd (Finset.mem_univ m') hm
    rw [hdec]
    refine Submodule.sum_mem _ fun m _ => Submodule.mem_iSup_of_mem m ?_
    refine ⟨a * x m, ?_, rfl⟩
    obtain ⟨r, hr⟩ := (Submodule.mem_one (R := 𝓞 K) (A := K)).mp (hcoord m)
    have hr' : algebraMap (𝓞 K) K r = x m := hr
    have hmul : a * x m = r • a := by rw [← hr', Algebra.smul_def, mul_comm]
    rw [hmul]
    exact I.smul_mem r ha
  · refine iSup_le fun m => ?_
    rintro _ ⟨a, ha, rfl⟩
    exact Submodule.subset_span ⟨a, ha, Pi.single m 1,
      Submodule.mem_iSup_of_mem m (Submodule.mem_span_singleton_self _), rfl⟩

/-- `realizeHLat` injectivity for any `K`-basis and invertible frame `X`. -/
theorem realizeHLat_injective {K V ι : Type*} [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) :
    Function.Injective (realizeHLat b X) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hn0 : ∑ v : InfinitePlace K, normAt b X v x ^ 2 = 0 := by
    rw [← norm_sq_realizeHLat, hx, norm_zero, sq, zero_mul]
  obtain ⟨v₀⟩ := (inferInstance : Nonempty (InfinitePlace K))
  have hvn0 : normAt b X v₀ x = 0 := by
    have := Finset.sum_eq_zero_iff_of_nonneg (fun w _ => sq_nonneg (normAt b X w x)) |>.mp
      hn0 v₀ (Finset.mem_univ v₀)
    exact sq_eq_zero_iff.mp this
  have hf0 : fcoord b X v₀ x = 0 := by
    funext i
    unfold normAt at hvn0
    rw [Real.sqrt_eq_zero (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at hvn0
    have hi := Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖fcoord b X v₀ x j‖)
      |>.mp hvn0 i (Finset.mem_univ i)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hi)
  have hvec0 : vecAt b v₀ x = 0 := by
    have := congrArg (Matrix.mulVec (X v₀)) hf0
    simp only [fcoord, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hX v₀),
      Matrix.one_mulVec, Matrix.mulVec_zero] at this
    exact this
  rw [← b.sum_repr x]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hi := congrFun hvec0 i
  simp only [vecAt, Pi.zero_apply, map_eq_zero] at hi
  rw [hi, zero_smul]

section IdealCovolumeAndLines

/-- Fundamental-domain index scaling for covolume of finite-index full-rank sublattices
`M ≤ L` (`IsZLattice ℝ M`, `IsZLattice ℝ L`) in `EuclideanSpace ℝ (Fin d)`. -/
theorem zlattice_covolume_sublattice_eq_relIndex {d : ℕ}
    (L M : Submodule ℤ (EuclideanSpace ℝ (Fin d)))
    [DiscreteTopology L] [IsZLattice ℝ L]
    [DiscreteTopology M] [IsZLattice ℝ M]
    (hML : M ≤ L) :
    ZLattice.covolume M MeasureTheory.volume =
      (M.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) * ZLattice.covolume L MeasureTheory.volume := by
  classical
  let hbL := basisOfZLattice L
  let hbM := basisOfZLattice M
  let P : Matrix (Fin d) (Fin d) ℤ := fun i j => hbL.repr ⟨(hbM j : _), hML (hbM j).2⟩ i
  have hEq : (fun j => (hbM j : EuclideanSpace ℝ (Fin d))) =
      fun j => ∑ i, (P.map (Int.cast : ℤ → ℝ)) i j • (hbL i : EuclideanSpace ℝ (Fin d)) := by
    funext j
    have h := congrArg Subtype.val (hbL.sum_repr ⟨(hbM j : _), hML (hbM j).2⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.map_apply, Int.cast_smul_eq_zsmul]
  have hPne : P.det ≠ 0 := by
    intro h0
    have hdet : (Matrix.gram ℝ (fun j => (hbM j : EuclideanSpace ℝ (Fin d)))).det =
        ((P.det : ℤ) : ℝ) ^ 2 *
          (Matrix.gram ℝ (fun i => (hbL i : EuclideanSpace ℝ (Fin d)))).det := by
      rw [hEq, gram_sum_smul_eq_transpose_mul, Matrix.det_mul, Matrix.det_mul,
        Matrix.det_transpose, ← Int.cast_det]
      ring
    rw [h0, Int.cast_zero, zero_pow two_ne_zero, zero_mul] at hdet
    exact (det_gram_basis_pos M hbM).ne' hdet
  have hdvd : ∀ x ∈ L, P.det • x ∈ M := by
    have hbasis : ∀ k : Fin d, P.det • (hbL k : EuclideanSpace ℝ (Fin d)) ∈ M := by
      intro k
      have hmul : P * P.adjugate = P.det • (1 : Matrix (Fin d) (Fin d) ℤ) :=
        Matrix.mul_adjugate P
      have hsum : ∑ j : Fin d, P.adjugate j k • (hbM j : EuclideanSpace ℝ (Fin d)) =
          P.det • (hbL k : EuclideanSpace ℝ (Fin d)) := by
        have hM_int : ∀ j, (hbM j : EuclideanSpace ℝ (Fin d)) =
            ∑ i, P i j • (hbL i : EuclideanSpace ℝ (Fin d)) := fun j => by
          simpa [Matrix.map_apply, Int.cast_smul_eq_zsmul] using congrFun hEq j
        simp_rw [hM_int, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        have hfin : ∑ i : Fin d, ∑ j : Fin d, (P.adjugate j k * P i j) •
            (hbL i : EuclideanSpace ℝ (Fin d)) =
            ∑ i : Fin d, (P * P.adjugate) i k • (hbL i : EuclideanSpace ℝ (Fin d)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_smul]
          congr 1
          simp [Matrix.mul_apply, mul_comm]
        rw [hfin, hmul]
        simp [Matrix.smul_apply, Matrix.one_apply]
      rw [← hsum]
      exact Submodule.sum_mem M fun j _ => M.smul_mem _ (hbM j).2
    intro x hx
    have hxrepr := congrArg Subtype.val (hbL.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hxrepr
    rw [← hxrepr, smul_sum]
    refine Submodule.sum_mem M fun k _ => ?_
    rw [smul_comm]
    exact M.smul_mem _ (hbasis k)
  let Q := L.toAddSubgroup ⧸ M.toAddSubgroup.addSubgroupOf L.toAddSubgroup
  have hQfin : Finite Q := by
    let m : ℕ := P.det.natAbs
    have hm_pos : 0 < m := Int.natAbs_pos.mpr hPne
    let : NeZero m := ⟨hm_pos.ne'⟩
    let f : (Fin d → Fin m) → Q := fun c =>
      QuotientAddGroup.mk (∑ i : Fin d, (c i : ℤ) • hbL i)
    refine Finite.of_surjective f ?_
    intro q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    let c : Fin d → Fin m := fun i =>
      ⟨(hbL.repr x i % (m : ℤ)).toNat, by
        have hnn : 0 ≤ hbL.repr x i % (m : ℤ) :=
          Int.emod_nonneg _ (by exact_mod_cast hm_pos.ne')
        have hlt : hbL.repr x i % (m : ℤ) < (m : ℤ) :=
          Int.emod_lt_of_pos _ (by exact_mod_cast hm_pos)
        omega⟩
    refine ⟨c, ?_⟩
    rw [QuotientAddGroup.eq]
    have hdiff_in_M : (-(∑ i : Fin d, (c i : ℤ) • hbL i) + x : L.toAddSubgroup).1 ∈ M := by
      have h1 : ∀ i, hbL.repr x i - (c i : ℤ) =
          (m : ℤ) * (hbL.repr x i / (m : ℤ)) := by
        intro i
        have hc : (c i : ℤ) = hbL.repr x i % (m : ℤ) := by
          simp only [c]
          exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hm_pos.ne'))
        rw [hc]
        linarith [Int.mul_ediv_add_emod (hbL.repr x i) (m : ℤ)]
      have hxsum : (x : EuclideanSpace ℝ (Fin d)) =
          ∑ i : Fin d, hbL.repr x i • (hbL i : EuclideanSpace ℝ (Fin d)) := by
        have h := congrArg (Subtype.val : L → EuclideanSpace ℝ (Fin d)) (hbL.sum_repr x)
        simpa only [Submodule.coe_sum, SetLike.val_smul] using h.symm
      have hcoe : ((-(∑ i : Fin d, (c i : ℤ) • hbL i) + x : L.toAddSubgroup) :
          EuclideanSpace ℝ (Fin d)) =
          -(∑ i : Fin d, (c i : ℤ) • (hbL i : EuclideanSpace ℝ (Fin d))) +
            (x : EuclideanSpace ℝ (Fin d)) := by
        change (-(∑ i : Fin d, (c i : ℤ) • hbL i : L) + (x : L) : EuclideanSpace ℝ (Fin d)) = _
        simp only [Submodule.coe_sum, SetLike.val_smul]
      have hsub : ((-(∑ i : Fin d, (c i : ℤ) • hbL i) + x : L.toAddSubgroup) :
          EuclideanSpace ℝ (Fin d)) =
          ∑ i : Fin d, ((m : ℤ) * (hbL.repr x i / (m : ℤ))) •
            (hbL i : EuclideanSpace ℝ (Fin d)) := by
        rw [hcoe, hxsum, add_comm, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← sub_smul, h1 i]
      change ((-(∑ i : Fin d, (c i : ℤ) • hbL i) + x : L.toAddSubgroup) :
          EuclideanSpace ℝ (Fin d)) ∈ M
      rw [hsub]
      refine Submodule.sum_mem M fun i _ => ?_
      rw [mul_comm, ← smul_smul]
      have hm_z : ((m : ℤ) : ℤ) • (hbL i : EuclideanSpace ℝ (Fin d)) ∈ M := by
        rcases Int.natAbs_eq P.det with hpos | hneg
        · rw [← hpos]; exact hdvd _ (hbL i).2
        · have hne : (m : ℤ) • (hbL i : EuclideanSpace ℝ (Fin d)) =
              -(P.det • (hbL i : EuclideanSpace ℝ (Fin d))) := by
            rw [← neg_smul]; congr 1; omega
          rw [hne]; exact M.neg_mem (hdvd _ (hbL i).2)
      exact M.smul_mem _ hm_z
    exact hdiff_in_M
  let : Fintype Q := Fintype.ofFinite Q
  let s : Q → L.toAddSubgroup := Quotient.out
  have hs_mk : ∀ q : Q, QuotientAddGroup.mk (s q) = q := Quotient.out_eq
  let F_L := ZSpan.fundamentalDomain (hbL.ofZLatticeBasis ℝ)
  have fundL : MeasureTheory.IsAddFundamentalDomain L.toAddSubgroup F_L MeasureTheory.volume :=
    ZLattice.isAddFundamentalDomain hbL MeasureTheory.volume
  let S : Set (EuclideanSpace ℝ (Fin d)) := ⋃ q : Q, ((-(s q : EuclideanSpace ℝ (Fin d))) +ᵥ F_L)
  have hS_null : MeasureTheory.NullMeasurableSet S MeasureTheory.volume :=
    MeasureTheory.NullMeasurableSet.iUnion fun _ => fundL.nullMeasurableSet.vadd _
  have hS_fund : MeasureTheory.IsAddFundamentalDomain M.toAddSubgroup S MeasureTheory.volume := by
    refine ⟨hS_null, ?_, ?_⟩
    · filter_upwards [fundL.ae_covers] with x hx
      obtain ⟨g, hg⟩ := hx
      let q : Q := QuotientAddGroup.mk g
      have hdiff : g - s q ∈ M.toAddSubgroup.addSubgroupOf L.toAddSubgroup := by
        rw [sub_eq_neg_add, ← QuotientAddGroup.eq, hs_mk]
      let m : M.toAddSubgroup :=
        ⟨(g : EuclideanSpace ℝ (Fin d)) - (s q : EuclideanSpace ℝ (Fin d)), hdiff⟩
      refine ⟨m, Set.mem_iUnion.mpr ⟨q, Set.mem_vadd_set.mpr ⟨g +ᵥ x, hg, ?_⟩⟩⟩
      have hm_coe : (m : EuclideanSpace ℝ (Fin d)) =
          (g : EuclideanSpace ℝ (Fin d)) - (s q : EuclideanSpace ℝ (Fin d)) := rfl
      change (-(s q : EuclideanSpace ℝ (Fin d))) + ((g : EuclideanSpace ℝ (Fin d)) + x) =
        (m : EuclideanSpace ℝ (Fin d)) + x
      rw [hm_coe]
      abel
    · intro m₁ m₂ hm
      change MeasureTheory.volume (((m₁ : EuclideanSpace ℝ (Fin d)) +ᵥ S) ∩
        ((m₂ : EuclideanSpace ℝ (Fin d)) +ᵥ S)) = 0
      have hsub_union : ((m₁ : EuclideanSpace ℝ (Fin d)) +ᵥ S) ∩
          ((m₂ : EuclideanSpace ℝ (Fin d)) +ᵥ S) =
          ⋃ (q₂ : Q) (q₁ : Q),
            (((m₁ : EuclideanSpace ℝ (Fin d)) +ᵥ ((-(s q₁ : EuclideanSpace ℝ (Fin d))) +ᵥ F_L)) ∩
              ((m₂ : EuclideanSpace ℝ (Fin d)) +ᵥ ((-(s q₂ : EuclideanSpace ℝ (Fin d))) +ᵥ F_L))) := by
        simp only [S, Set.vadd_set_iUnion, Set.iUnion_inter, Set.inter_iUnion]
      rw [hsub_union]
      refine MeasureTheory.measure_iUnion_null fun q₂ =>
        MeasureTheory.measure_iUnion_null fun q₁ => ?_
      let g₁ : L.toAddSubgroup := ⟨(m₁ : EuclideanSpace ℝ (Fin d)) - (s q₁ : EuclideanSpace ℝ (Fin d)),
        sub_mem (hML m₁.2) (s q₁).2⟩
      let g₂ : L.toAddSubgroup := ⟨(m₂ : EuclideanSpace ℝ (Fin d)) - (s q₂ : EuclideanSpace ℝ (Fin d)),
        sub_mem (hML m₂.2) (s q₂).2⟩
      have hg_ne : g₁ ≠ g₂ := by
        intro heq
        have heqE : (m₁ : EuclideanSpace ℝ (Fin d)) - (s q₁ : EuclideanSpace ℝ (Fin d)) =
            (m₂ : EuclideanSpace ℝ (Fin d)) - (s q₂ : EuclideanSpace ℝ (Fin d)) :=
          congrArg Subtype.val heq
        have hmemM : (-s q₁ + s q₂) ∈ M.toAddSubgroup.addSubgroupOf L.toAddSubgroup := by
          change -(s q₁ : EuclideanSpace ℝ (Fin d)) + (s q₂ : EuclideanSpace ℝ (Fin d)) ∈ M
          have hsub2 : -(s q₁ : EuclideanSpace ℝ (Fin d)) + (s q₂ : EuclideanSpace ℝ (Fin d)) =
              (m₂ : EuclideanSpace ℝ (Fin d)) - (m₁ : EuclideanSpace ℝ (Fin d)) := by
            calc -(s q₁ : EuclideanSpace ℝ (Fin d)) + (s q₂ : EuclideanSpace ℝ (Fin d))
                = ((m₁ : EuclideanSpace ℝ (Fin d)) - (s q₁ : EuclideanSpace ℝ (Fin d))) -
                    (m₁ : EuclideanSpace ℝ (Fin d)) + (s q₂ : EuclideanSpace ℝ (Fin d)) := by abel
              _ = ((m₂ : EuclideanSpace ℝ (Fin d)) - (s q₂ : EuclideanSpace ℝ (Fin d))) -
                    (m₁ : EuclideanSpace ℝ (Fin d)) + (s q₂ : EuclideanSpace ℝ (Fin d)) := by rw [heqE]
              _ = (m₂ : EuclideanSpace ℝ (Fin d)) - (m₁ : EuclideanSpace ℝ (Fin d)) := by abel
          rw [hsub2]
          exact M.sub_mem m₂.2 m₁.2
        have hqeq : q₁ = q₂ := by
          rw [← hs_mk q₁, ← hs_mk q₂, QuotientAddGroup.eq]
          exact hmemM
        subst hqeq
        apply hm
        apply Subtype.ext
        exact sub_left_inj.mp heqE
      have h0 : MeasureTheory.volume
          (((g₁ : EuclideanSpace ℝ (Fin d)) +ᵥ F_L) ∩
            ((g₂ : EuclideanSpace ℝ (Fin d)) +ᵥ F_L)) = 0 :=
        fundL.aedisjoint hg_ne
      simpa only [vadd_vadd, sub_eq_add_neg, g₁, g₂] using h0
  have hvolS : MeasureTheory.volume S = (Fintype.card Q : ENNReal) * MeasureTheory.volume F_L := by
    rw [MeasureTheory.measure_iUnion₀]
    · simp_rw [MeasureTheory.measure_vadd]
      simp
    · intro q₁ q₂ hne
      have hg_ne : -s q₁ ≠ -s q₂ := fun heq => hne (by
        rw [← hs_mk q₁, ← hs_mk q₂, neg_inj.mp heq])
      have h0 : MeasureTheory.volume
          ((((-s q₁ : L.toAddSubgroup) : EuclideanSpace ℝ (Fin d)) +ᵥ F_L) ∩
            ((((-s q₂ : L.toAddSubgroup) : EuclideanSpace ℝ (Fin d)) +ᵥ F_L))) = 0 :=
        fundL.aedisjoint hg_ne
      change MeasureTheory.volume (((-(s q₁ : EuclideanSpace ℝ (Fin d))) +ᵥ F_L) ∩
        ((-(s q₂ : EuclideanSpace ℝ (Fin d))) +ᵥ F_L)) = 0
      simpa only [AddSubgroup.coe_neg] using h0
    · intro q; exact fundL.nullMeasurableSet.vadd _
  have hcovL : ENNReal.ofReal (ZLattice.covolume L MeasureTheory.volume) = MeasureTheory.volume F_L := by
    have hne_top : MeasureTheory.volume F_L ≠ ⊤ :=
      (ZSpan.fundamentalDomain_isBounded (hbL.ofZLatticeBasis ℝ)).measure_lt_top.ne
    rw [ZLattice.covolume_eq_measure_fundamentalDomain L MeasureTheory.volume fundL,
      MeasureTheory.Measure.real, ENNReal.ofReal_toReal hne_top]
  have hcovM : ENNReal.ofReal (ZLattice.covolume M MeasureTheory.volume) = MeasureTheory.volume S := by
    have hne_top : MeasureTheory.volume S ≠ ⊤ := by
      rw [hvolS]
      exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (ZSpan.fundamentalDomain_isBounded (hbL.ofZLatticeBasis ℝ)).measure_lt_top.ne
    rw [ZLattice.covolume_eq_measure_fundamentalDomain M MeasureTheory.volume hS_fund,
      MeasureTheory.Measure.real, ENNReal.ofReal_toReal hne_top]
  have hrel : M.toAddSubgroup.relIndex L.toAddSubgroup = Fintype.card Q := by
    rw [AddSubgroup.relIndex, AddSubgroup.index_eq_card, Nat.card_eq_fintype_card]
  have hcovL_nn : 0 ≤ ZLattice.covolume L MeasureTheory.volume := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain L MeasureTheory.volume fundL]
    exact MeasureTheory.measureReal_nonneg
  have hcovM_nn : 0 ≤ ZLattice.covolume M MeasureTheory.volume := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain M MeasureTheory.volume hS_fund]
    exact MeasureTheory.measureReal_nonneg
  rw [hrel]
  have hENN : ENNReal.ofReal (ZLattice.covolume M MeasureTheory.volume) =
      ENNReal.ofReal ((Fintype.card Q : ℝ) * ZLattice.covolume L MeasureTheory.volume) := by
    rw [hcovM, hvolS, ← hcovL, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  exact (ENNReal.ofReal_eq_ofReal_iff hcovM_nn (mul_nonneg (Nat.cast_nonneg _) hcovL_nn)).mp hENN

private def mixedSpaceToEucl (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] :
    NumberField.mixedEmbedding.mixedSpace K ≃ₗ[ℝ]
      EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2) where
  toFun x := WithLp.toLp 2 fun p =>
    if p.2.2 = 0 then (x.2 ⟨p.1, IsTotallyComplex.isComplex p.1⟩).re
    else (x.2 ⟨p.1, IsTotallyComplex.isComplex p.1⟩).im
  invFun y :=
    (fun ⟨w, hw⟩ => False.elim ((NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr
      (IsTotallyComplex.isComplex w)) hw),
     fun w => ⟨y (w.1, (), 0), y (w.1, (), 1)⟩)
  map_add' x y := by
    ext p
    simp only [Prod.snd_add, Pi.add_apply, Complex.add_re, Complex.add_im, PiLp.add_apply]
    split_ifs <;> rfl
  map_smul' c x := by
    ext p
    simp only [Prod.smul_snd, Pi.smul_apply, Complex.real_smul, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero,
      PiLp.smul_apply, RingHom.id_apply]
    split_ifs <;> rfl
  left_inv x := by
    ext ⟨w, hw⟩
    · exact False.elim ((NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr
        (IsTotallyComplex.isComplex w)) hw)
    · apply Complex.ext <;> simp
  right_inv y := by
    ext p
    rcases p with ⟨v, ⟨⟨⟩, j⟩⟩
    fin_cases j <;> simp

private def mixedSpaceToFinEucl (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] :
    NumberField.mixedEmbedding.mixedSpace K ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin (Fintype.card (InfinitePlace K × Unit × Fin 2))) :=
  (mixedSpaceToEucl K).trans
    (euclideanSpaceCongr (Fintype.equivFin (InfinitePlace K × Unit × Fin 2))).toLinearEquiv

private def mixedSpaceToFinPi (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] :
    NumberField.mixedEmbedding.mixedSpace K ≃ₗ[ℝ]
      (Fin (Fintype.card (InfinitePlace K × Unit × Fin 2)) → ℝ) :=
  (mixedSpaceToFinEucl K).trans
    (WithLp.linearEquiv 2 ℝ (Fin (Fintype.card (InfinitePlace K × Unit × Fin 2)) → ℝ))

open Classical in
private def mixedSpaceToFinPiMeasurable (K : Type) [Field K] [NumberField K]
    [IsTotallyComplex K] :
    NumberField.mixedEmbedding.mixedSpace K ≃ᵐ
      (Fin (Fintype.card (InfinitePlace K × Unit × Fin 2)) → ℝ) :=
  { toEquiv := (mixedSpaceToFinPi K).toEquiv
    measurable_toFun :=
      ((mixedSpaceToFinPi K).toLinearMap.continuous_of_finiteDimensional).measurable
    measurable_invFun :=
      ((mixedSpaceToFinPi K).symm.toLinearMap.continuous_of_finiteDimensional).measurable }

open Classical in
private lemma measurePreserving_mixedSpaceToFinPi (K : Type) [Field K] [NumberField K]
    [IsTotallyComplex K] :
    MeasureTheory.MeasurePreserving (mixedSpaceToFinPiMeasurable K)
      MeasureTheory.volume MeasureTheory.volume := by
  let d := Fintype.card (InfinitePlace K × Unit × Fin 2)
  let eι := Fintype.equivFin (InfinitePlace K × Unit × Fin 2)
  let f_pi := mixedSpaceToFinPiMeasurable K
  refine ⟨f_pi.measurable, ?_⟩
  rw [MeasureTheory.volume_pi]
  refine (MeasureTheory.Measure.pi_eq fun s hs => ?_).symm
  rw [MeasureTheory.Measure.map_apply f_pi.measurable (MeasurableSet.univ_pi hs)]
  have hpre : f_pi ⁻¹' Set.pi Set.univ s =
      (Set.univ : Set ({w : InfinitePlace K // w.IsReal} → ℝ)) ×ˢ
        Set.pi Set.univ (fun w : {w : InfinitePlace K // w.IsComplex} =>
          { z : ℂ | z.re ∈ s (eι (w.1, (), 0)) ∧ z.im ∈ s (eι (w.1, (), 1)) }) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_prod,
      true_and, Set.mem_ofPred_eq]
    constructor
    · intro h w
      have h0 := h (eι (w.1, (), 0))
      have h1 := h (eι (w.1, (), 1))
      have hval0 : f_pi x (eι (w.1, (), 0)) = (x.2 w).re := by
        simp [f_pi, mixedSpaceToFinPiMeasurable, mixedSpaceToFinPi, mixedSpaceToFinEucl,
          mixedSpaceToEucl, euclideanSpaceCongr, eι]
      have hval1 : f_pi x (eι (w.1, (), 1)) = (x.2 w).im := by
        simp [f_pi, mixedSpaceToFinPiMeasurable, mixedSpaceToFinPi, mixedSpaceToFinEucl,
          mixedSpaceToEucl, euclideanSpaceCongr, eι]
      exact ⟨hval0 ▸ h0, hval1 ▸ h1⟩
    · intro h q
      rcases hq : eι.symm q with ⟨v, ⟨⟨⟩, j⟩⟩
      have hq' : q = eι (v, (), j) := by rw [← hq, Equiv.apply_symm_apply]
      subst hq'
      have hw := h ⟨v, IsTotallyComplex.isComplex v⟩
      fin_cases j
      · simpa [f_pi, mixedSpaceToFinPiMeasurable, mixedSpaceToFinPi, mixedSpaceToFinEucl,
          mixedSpaceToEucl, euclideanSpaceCongr, eι] using hw.1
      · simpa [f_pi, mixedSpaceToFinPiMeasurable, mixedSpaceToFinPi, mixedSpaceToFinEucl,
          mixedSpaceToEucl, euclideanSpaceCongr, eι] using hw.2
  rw [hpre, MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
  have : IsEmpty {w : InfinitePlace K // w.IsReal} :=
    ⟨fun ⟨w, hw⟩ => (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr
      (IsTotallyComplex.isComplex w)) hw⟩
  have hreal1 : (MeasureTheory.volume : MeasureTheory.Measure ({w : InfinitePlace K // w.IsReal} → ℝ)) Set.univ = 1 := by
    rw [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_univ]
    simp
  rw [hreal1, one_mul, MeasureTheory.volume_pi, MeasureTheory.Measure.pi_pi]
  have hc : ∀ w : {w : InfinitePlace K // w.IsComplex},
      MeasureTheory.volume { z : ℂ | z.re ∈ s (eι (w.1, (), 0)) ∧ z.im ∈ s (eι (w.1, (), 1)) } =
        MeasureTheory.volume (s (eι (w.1, (), 0))) *
          MeasureTheory.volume (s (eι (w.1, (), 1))) := fun w => by
    have hpreC : { z : ℂ | z.re ∈ s (eι (w.1, (), 0)) ∧ z.im ∈ s (eι (w.1, (), 1)) } =
        Complex.measurableEquivRealProd ⁻¹' (s (eι (w.1, (), 0)) ×ˢ s (eι (w.1, (), 1))) := by
      ext z; simp [Complex.measurableEquivRealProd_apply]
    rw [hpreC, Complex.volume_preserving_equiv_real_prod.measure_preimage
      ((hs _).prod (hs _)).nullMeasurableSet, MeasureTheory.Measure.volume_eq_prod,
      MeasureTheory.Measure.prod_prod]
  simp_rw [hc]
  let e_sub : {w : InfinitePlace K // w.IsComplex} ≃ InfinitePlace K :=
    Equiv.subtypeUnivEquiv fun w => IsTotallyComplex.isComplex w
  rw [show (∏ w : {w : InfinitePlace K // w.IsComplex},
      MeasureTheory.volume (s (eι (w.1, (), 0))) *
        MeasureTheory.volume (s (eι (w.1, (), 1)))) =
      ∏ v : InfinitePlace K,
        MeasureTheory.volume (s (eι (v, (), 0))) *
          MeasureTheory.volume (s (eι (v, (), 1))) from
    Fintype.prod_equiv e_sub _ _ (fun _ => rfl)]
  rw [← Fintype.prod_equiv eι (fun p => MeasureTheory.volume (s (eι p)))
      (fun q => MeasureTheory.volume (s q)) (fun _ => rfl)]
  rw [Fintype.prod_prod_type]
  simp_rw [Fintype.prod_prod_type, Finset.univ_unique, Finset.prod_singleton, Fin.prod_univ_two]

private lemma isZLattice_single_one (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] :
    DiscreteTopology (zRealizeMod (Basis.singleton Unit K) (fun _ => 1) (1 : Submodule (𝓞 K) K)) ∧
      Submodule.span ℝ ((zRealizeMod (Basis.singleton Unit K) (fun _ => 1)
        (1 : Submodule (𝓞 K) K)) :
          Set (EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2))) = ⊤ := by
  let L_one := zRealizeMod (Basis.singleton Unit K) (fun _ => 1) (1 : Submodule (𝓞 K) K)
  let eqZ : NumberField.mixedEmbedding.integerLattice K ≃ₗ[ℤ] L_one :=
    { toFun := fun y =>
        ⟨mixedSpaceToEucl K y.1, by
          rcases y.2 with ⟨a, ha⟩
          refine ⟨(a : K), (Submodule.mem_one (R := 𝓞 K) (A := K)).mpr ⟨a, rfl⟩, ?_⟩
          ext p; rcases p with ⟨v, ⟨⟨⟩, j⟩⟩
          rw [← ha]
          simp [realizeHLat, fcoord, vecAt, mixedSpaceToEucl]⟩
      invFun := fun z =>
        ⟨(mixedSpaceToEucl K).symm z.1, by
          rcases z.2 with ⟨x, hx, hxz⟩
          obtain ⟨a, ha⟩ := (Submodule.mem_one (R := 𝓞 K) (A := K)).mp hx
          refine ⟨a, ?_⟩
          apply (mixedSpaceToEucl K).injective
          rw [LinearEquiv.apply_symm_apply, ← hxz]
          ext p; rcases p with ⟨v, ⟨⟨⟩, j⟩⟩
          simp [realizeHLat, fcoord, vecAt, mixedSpaceToEucl, ← ha]⟩
      map_add' := fun x y => Subtype.ext (map_add (mixedSpaceToEucl K) x.1 y.1)
      map_smul' := fun c x => Subtype.ext (map_zsmul (mixedSpaceToEucl K) c x.1)
      left_inv := fun x => Subtype.ext ((mixedSpaceToEucl K).symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext ((mixedSpaceToEucl K).apply_symm_apply y.1) }
  have hD : DiscreteTopology L_one := by
    refine DiscreteTopology.of_continuous_injective (f := eqZ.symm) ?_ eqZ.symm.injective
    exact Continuous.subtype_mk
      ((mixedSpaceToEucl K).symm.toLinearMap.continuous_of_finiteDimensional.comp
        continuous_subtype_val) _
  have hsp : Submodule.span ℝ (L_one : Set (EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2))) = ⊤ := by
    let bE := (NumberField.mixedEmbedding.latticeBasis K).map (mixedSpaceToEucl K)
    rw [eq_top_iff, ← bE.span_eq]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    rw [Basis.map_apply, NumberField.mixedEmbedding.latticeBasis_apply,
      NumberField.integralBasis_apply]
    exact Submodule.subset_span (eqZ ⟨NumberField.mixedEmbedding K
      ((NumberField.RingOfIntegers.basis K i : 𝓞 K) : K),
      ⟨NumberField.RingOfIntegers.basis K i, rfl⟩⟩).2
  exact ⟨hD, hsp⟩

/-- Exact covolume of `(1 : Submodule (𝓞 K) K)` inside
`EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2)`. -/
theorem covol_single_one_eq (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] :
    covol (zRealizeMod (Basis.singleton Unit K) (fun _ => 1) (1 : Submodule (𝓞 K) K)) =
      2 ^ (-(Fintype.card (InfinitePlace K) : ℝ)) *
        Real.sqrt |(NumberField.discr K : ℝ)| := by
  classical
  let eι : (InfinitePlace K × Unit × Fin 2) ≃ Fin (Fintype.card (InfinitePlace K × Unit × Fin 2)) :=
    Fintype.equivFin _
  let iso : EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (Fintype.card (InfinitePlace K × Unit × Fin 2))) :=
    euclideanSpaceCongr eι
  let Λ_one := zRealizeMod (Basis.singleton Unit K) (fun _ => 1) (1 : Submodule (𝓞 K) K)
  let Λ := Λ_one.map (iso.toLinearEquiv.toLinearMap.restrictScalars ℤ)
  obtain ⟨hD_one, hsp_one⟩ := isZLattice_single_one K
  have : DiscreteTopology Λ_one := hD_one
  have : IsZLattice ℝ Λ_one := ⟨hsp_one⟩
  have hDiscΛ : DiscreteTopology Λ := discreteTopology_map_linearEquiv Λ_one iso.toLinearEquiv
  have hIsZΛ : IsZLattice ℝ Λ := ⟨span_top_map_linearEquiv Λ_one iso.toLinearEquiv⟩
  let Ψ := mixedSpaceToFinEucl K
  have hmap_int : (NumberField.mixedEmbedding.integerLattice K).map
      ((mixedSpaceToEucl K).toLinearMap.restrictScalars ℤ) = Λ_one := by
    ext y
    simp only [Submodule.mem_map, Λ_one, zRealizeMod]
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      refine ⟨(a : K), (Submodule.mem_one (R := 𝓞 K) (A := K)).mpr ⟨a, rfl⟩, ?_⟩
      ext p; rcases p with ⟨v, ⟨⟨⟩, j⟩⟩
      simp [realizeHLat, fcoord, vecAt, mixedSpaceToEucl]
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨a, ha⟩ := (Submodule.mem_one (R := 𝓞 K) (A := K)).mp hx
      refine ⟨NumberField.mixedEmbedding K (a : K), ⟨a, rfl⟩, ?_⟩
      ext p; rcases p with ⟨v, ⟨⟨⟩, j⟩⟩
      simp [mixedSpaceToEucl, realizeHLat, fcoord, vecAt, ← ha]
  have hΛ_map : Λ = (NumberField.mixedEmbedding.integerLattice K).map
      (Ψ.toLinearMap.restrictScalars ℤ) := by
    dsimp only [Λ, Ψ, mixedSpaceToFinEucl]
    rw [← hmap_int]
    ext y
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨mixedSpaceToEucl K x, ⟨x, hx, rfl⟩, rfl⟩
  let bR : Module.Basis (Fin (Fintype.card (InfinitePlace K × Unit × Fin 2))) ℤ Λ :=
    basisOfZLattice Λ
  let eqZ_iso : Λ_one ≃ₗ[ℤ] Λ :=
    { toFun := fun x => ⟨iso x.1, x.1, x.2, rfl⟩
      invFun := fun y => ⟨iso.symm y.1, by
        rcases y.2 with ⟨x, hx, hxy⟩
        rwa [show iso.symm y.1 = x from by rw [← hxy]; exact iso.symm_apply_apply x]⟩
      map_add' := fun x y => Subtype.ext (map_add iso x.1 y.1)
      map_smul' := fun c x => Subtype.ext (map_zsmul iso c x.1)
      left_inv := fun x => Subtype.ext (iso.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (iso.apply_symm_apply y.1) }
  let bA := bR.map eqZ_iso.symm
  have hcov_eq : covol Λ_one = ZLattice.covolume Λ MeasureTheory.volume := by
    rw [covol_eq_sqrt_det_gram Λ_one bA, covolume_eq_abs_det Λ bR]
    let B : Matrix (Fin (Fintype.card (InfinitePlace K × Unit × Fin 2)))
        (Fin (Fintype.card (InfinitePlace K × Unit × Fin 2))) ℝ :=
      Matrix.of fun i j => ((bR i : Λ) : EuclideanSpace ℝ
        (Fin (Fintype.card (InfinitePlace K × Unit × Fin 2)))) j
    have hgram : Matrix.gram ℝ (fun i => ((bA i : Λ_one) :
        EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2))) = B * Bᵀ := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.transpose_apply, B, Matrix.of_apply]
      change ⟪((bA i : Λ_one) : EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2)),
        ((bA j : Λ_one) : EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2))⟫_ℝ = _
      have hmap : ∀ k, iso ((bA k : Λ_one) : EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2)) =
          ((bR k : Λ) : EuclideanSpace ℝ (Fin (Fintype.card (InfinitePlace K × Unit × Fin 2)))) :=
        fun k => by
          change iso (iso.symm (bR k : _)) = _; exact iso.apply_symm_apply _
      rw [← iso.inner_map_map, hmap i, hmap j, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
      refine Finset.sum_congr rfl fun k _ => by simp [mul_comm]
    rw [hgram, Matrix.det_mul, Matrix.det_transpose, ← sq, Real.sqrt_sq_eq_abs]
  have hmp_pi : MeasureTheory.MeasurePreserving (mixedSpaceToFinPiMeasurable K)
      MeasureTheory.volume MeasureTheory.volume :=
    measurePreserving_mixedSpaceToFinPi K
  have hmp_toLp : MeasureTheory.MeasurePreserving
      (WithLp.toLp 2 : (Fin (Fintype.card (InfinitePlace K × Unit × Fin 2)) → ℝ) →
        EuclideanSpace ℝ (Fin (Fintype.card (InfinitePlace K × Unit × Fin 2))))
      MeasureTheory.volume MeasureTheory.volume :=
    PiLp.volume_preserving_toLp (Fin (Fintype.card (InfinitePlace K × Unit × Fin 2)))
  let bInt := Module.finBasis ℤ (NumberField.mixedEmbedding.integerLattice K)
  have hcard_eq : Module.finrank ℤ (NumberField.mixedEmbedding.integerLattice K) =
      Fintype.card (InfinitePlace K × Unit × Fin 2) := by
    rw [ZLattice.rank ℝ (NumberField.mixedEmbedding.integerLattice K),
      Ψ.finrank_eq, finrank_euclideanSpace_fin]
  let bIntFin := bInt.reindex (finCongr hcard_eq)
  let eqZ_all : NumberField.mixedEmbedding.integerLattice K ≃ₗ[ℤ] Λ :=
    { toFun := fun x => ⟨Ψ x.1, by rw [hΛ_map]; exact ⟨x.1, x.2, rfl⟩⟩
      invFun := fun y => ⟨Ψ.symm y.1, by
        have hy : y.1 ∈ (NumberField.mixedEmbedding.integerLattice K).map
            (Ψ.toLinearMap.restrictScalars ℤ) := by
          rw [← hΛ_map]; exact y.2
        rcases hy with ⟨x, hx, hxy⟩
        rwa [show Ψ.symm y.1 = x from by rw [← hxy]; exact Ψ.symm_apply_apply x]⟩
      map_add' := fun x y => Subtype.ext (map_add Ψ x.1 y.1)
      map_smul' := fun c x => Subtype.ext (map_zsmul Ψ c x.1)
      left_inv := fun x => Subtype.ext (Ψ.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (Ψ.apply_symm_apply y.1) }
  let bΛ : Basis (Fin (Fintype.card (InfinitePlace K × Unit × Fin 2))) ℤ Λ :=
    bIntFin.map eqZ_all
  let bΛ_pi : Basis (Fin (Fintype.card (InfinitePlace K × Unit × Fin 2))) ℝ
      (Fin (Fintype.card (InfinitePlace K × Unit × Fin 2)) → ℝ) :=
    (bIntFin.ofZLatticeBasis ℝ).map (mixedSpaceToFinPi K)
  have fund_int : MeasureTheory.IsAddFundamentalDomain
      (NumberField.mixedEmbedding.integerLattice K).toAddSubgroup
      (ZSpan.fundamentalDomain (bIntFin.ofZLatticeBasis ℝ)) MeasureTheory.volume :=
    ZLattice.isAddFundamentalDomain bIntFin MeasureTheory.volume
  have fund_Λ : MeasureTheory.IsAddFundamentalDomain Λ.toAddSubgroup
      (ZSpan.fundamentalDomain (bΛ.ofZLatticeBasis ℝ)) MeasureTheory.volume :=
    ZLattice.isAddFundamentalDomain bΛ MeasureTheory.volume
  have hfd_pi_eq : ZSpan.fundamentalDomain bΛ_pi =
      (mixedSpaceToFinPiMeasurable K) '' ZSpan.fundamentalDomain (bIntFin.ofZLatticeBasis ℝ) := by
    exact (ZSpan.map_fundamentalDomain (bIntFin.ofZLatticeBasis ℝ) (mixedSpaceToFinPi K)).symm
  have hfd_pre : (WithLp.toLp 2 : (Fin (Fintype.card (InfinitePlace K × Unit × Fin 2)) → ℝ) →
        EuclideanSpace ℝ (Fin (Fintype.card (InfinitePlace K × Unit × Fin 2)))) ⁻¹'
      ZSpan.fundamentalDomain (bΛ.ofZLatticeBasis ℝ) = ZSpan.fundamentalDomain bΛ_pi := by
    ext y
    simp only [Set.mem_preimage, ZSpan.mem_fundamentalDomain]
    have hrepr : ∀ i, (bΛ.ofZLatticeBasis ℝ).repr (WithLp.toLp 2 y) i = bΛ_pi.repr y i := by
      intro i
      have hy : WithLp.toLp 2 y = ∑ j, bΛ_pi.repr y j • (bΛ.ofZLatticeBasis ℝ) j := by
        have hsum := (bΛ_pi.sum_repr y).symm
        have hmap := congrArg (WithLp.linearEquiv 2 ℝ
          (Fin (Fintype.card (InfinitePlace K × Unit × Fin 2)) → ℝ)).symm hsum
        rw [map_sum] at hmap
        simp_rw [map_smul] at hmap
        refine hmap.trans (Finset.sum_congr rfl fun j _ => ?_)
        congr 1
        ext k
        simp [Basis.ofZLatticeBasis_apply, bΛ, bΛ_pi, eqZ_all, mixedSpaceToFinPi, Ψ]
      rw [hy, map_sum]
      simp_rw [map_smul, Basis.repr_self, Finsupp.finsetSum_apply, Finsupp.smul_apply,
        Finsupp.single_apply, smul_eq_mul]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [hj]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    simp_rw [hrepr]
  have himg_eq : (mixedSpaceToFinPiMeasurable K) ''
      ZSpan.fundamentalDomain (bIntFin.ofZLatticeBasis ℝ) =
      (mixedSpaceToFinPiMeasurable K).symm ⁻¹'
        ZSpan.fundamentalDomain (bIntFin.ofZLatticeBasis ℝ) :=
    (mixedSpaceToFinPiMeasurable K).toEquiv.image_eq_preimage_symm _
  rw [hcov_eq, ZLattice.covolume_eq_measure_fundamentalDomain Λ MeasureTheory.volume fund_Λ,
    MeasureTheory.measureReal_def,
    ← hmp_toLp.measure_preimage (ZSpan.fundamentalDomain_measurableSet _).nullMeasurableSet,
    hfd_pre, hfd_pi_eq, himg_eq,
    hmp_pi.symm.measure_preimage (ZSpan.fundamentalDomain_measurableSet _).nullMeasurableSet,
    ← MeasureTheory.measureReal_def,
    ← ZLattice.covolume_eq_measure_fundamentalDomain (NumberField.mixedEmbedding.integerLattice K)
      MeasureTheory.volume fund_int,
    NumberField.mixedEmbedding.covolume_integerLattice K]
  have hnr : InfinitePlace.nrComplexPlaces K = Fintype.card (InfinitePlace K) := by
    have h := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
    rw [IsTotallyComplex.nrRealPlaces_eq_zero K, zero_add] at h
    exact h.symm
  rw [hnr, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast, inv_pow]

private lemma isZLattice_single_ideal (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) :
    DiscreteTopology (zRealizeMod (Basis.singleton Unit K) (fun _ => 1)
        ((J : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) ∧
      Submodule.span ℝ ((zRealizeMod (Basis.singleton Unit K) (fun _ => 1)
        ((J : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) :
          Set (EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2))) = ⊤ := by
  let L_one := zRealizeMod (Basis.singleton Unit K) (fun _ => 1) (1 : Submodule (𝓞 K) K)
  let L_J := zRealizeMod (Basis.singleton Unit K) (fun _ => 1)
    ((J : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
  obtain ⟨hD_one, hsp_one⟩ := isZLattice_single_one K
  have : DiscreteTopology L_one := hD_one
  have : IsZLattice ℝ L_one := ⟨hsp_one⟩
  have hsub_L : L_J ≤ L_one := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, _, rfl⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hx
    exact ⟨(a : K), (Submodule.mem_one (R := 𝓞 K) (A := K)).mpr ⟨a, rfl⟩, rfl⟩
  have hD : DiscreteTopology L_J := discreteTopology_of_le hsub_L
  obtain ⟨a, haJ, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  have haK0 : (a : K) ≠ 0 := Subtype.coe_ne_coe.mpr ha0
  let T_a : EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2) →ₗ[ℝ]
      EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2) :=
    placeBlockLin (fun v => Matrix.diagonal fun _ : Unit => v.embedding (a : K))
  let T_ainv : EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2) →ₗ[ℝ]
      EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2) :=
    placeBlockLin (fun v => Matrix.diagonal fun _ : Unit => (v.embedding (a : K))⁻¹)
  let e_a : EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2) ≃ₗ[ℝ]
      EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2) :=
    { toLinearMap := T_a
      invFun := T_ainv
      left_inv := fun x => by
        have h1 : T_ainv.comp T_a = LinearMap.id := by
          rw [← placeBlockLin_mul]
          convert placeBlockLin_one (K := K) (ι := Unit) using 2
          funext v; ext i j
          simp [inv_mul_cancel₀ ((map_ne_zero_iff v.embedding (RingHom.injective _)).mpr haK0)]
        exact LinearMap.congr_fun h1 x
      right_inv := fun x => by
        have h1 : T_a.comp T_ainv = LinearMap.id := by
          rw [← placeBlockLin_mul]
          convert placeBlockLin_one (K := K) (ι := Unit) using 2
          funext v; ext i j
          simp [mul_inv_cancel₀ ((map_ne_zero_iff v.embedding (RingHom.injective _)).mpr haK0)]
        exact LinearMap.congr_fun h1 x }
  have hTa_sub : L_one.map (e_a.toLinearMap.restrictScalars ℤ) ≤ L_J := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    obtain ⟨r, hr⟩ := (Submodule.mem_one (R := 𝓞 K) (A := K)).mp hx
    refine ⟨((r * a : 𝓞 K) : K),
      (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mpr ⟨r * a, J.mul_mem_left r haJ, rfl⟩, ?_⟩
    ext p; rcases p with ⟨v, ⟨⟨⟩, j⟩⟩
    simp only [T_a, e_a, placeBlockLin, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.coe_restrictScalars, realizeHLat, fcoord,
      inv_one, Matrix.one_mulVec, vecAt, Basis.singleton_repr]
    simp only [complexToRealLin, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp,
      Matrix.mulVec_diagonal, ← hr]
    fin_cases j
    · simp [map_mul, mul_comm, Complex.mul_re]
    · simp [map_mul, mul_comm, Complex.mul_im]
  have hsp : Submodule.span ℝ (L_J : Set (EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2))) = ⊤ := by
    have hsp1 : (⊤ : Submodule ℝ _) = (Submodule.span ℝ (L_one : Set _)).map e_a.toLinearMap := by
      rw [IsZLattice.span_top (K := ℝ) (L := L_one), Submodule.map_top, LinearEquiv.range]
    rw [eq_top_iff, hsp1]
    refine Submodule.map_le_iff_le_comap.mpr (Submodule.span_le.mpr fun y hy => ?_)
    exact Submodule.subset_span (hTa_sub ⟨y, hy, rfl⟩)
  exact ⟨hD, hsp⟩

/-- Exact `covol` of a nonzero integral ideal `J : Ideal (𝓞 K)` inside
`EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2)`. -/
theorem covol_single_ideal_eq (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) :
    covol (zRealizeMod (Basis.singleton Unit K) (fun _ => 1)
        ((J : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) =
      (Ideal.absNorm J : ℝ) *
        covol (zRealizeMod (Basis.singleton Unit K) (fun _ => 1) (1 : Submodule (𝓞 K) K)) := by
  classical
  let eι : (InfinitePlace K × Unit × Fin 2) ≃ Fin (Fintype.card (InfinitePlace K × Unit × Fin 2)) :=
    Fintype.equivFin _
  let iso : EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (Fintype.card (InfinitePlace K × Unit × Fin 2))) :=
    euclideanSpaceCongr eι
  let L_one := zRealizeMod (Basis.singleton Unit K) (fun _ => 1) (1 : Submodule (𝓞 K) K)
  let L_J := zRealizeMod (Basis.singleton Unit K) (fun _ => 1)
    ((J : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
  let Λ_one := L_one.map (iso.toLinearEquiv.toLinearMap.restrictScalars ℤ)
  let Λ_J := L_J.map (iso.toLinearEquiv.toLinearMap.restrictScalars ℤ)
  have hsub_L : L_J ≤ L_one := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, _, rfl⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hx
    exact ⟨(a : K), (Submodule.mem_one (R := 𝓞 K) (A := K)).mpr ⟨a, rfl⟩, rfl⟩
  have hsub_Λ : Λ_J ≤ Λ_one := Submodule.map_mono hsub_L
  obtain ⟨hDisc_one, hsp_one⟩ := isZLattice_single_one K
  obtain ⟨hDisc_J, hsp_J⟩ := isZLattice_single_ideal K J hJ
  have : DiscreteTopology L_one := hDisc_one
  have : IsZLattice ℝ L_one := ⟨hsp_one⟩
  have : DiscreteTopology L_J := hDisc_J
  have : IsZLattice ℝ L_J := ⟨hsp_J⟩
  have hiso_invar : ∀ (M : Submodule ℤ (EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2)))
      [DiscreteTopology M] [IsZLattice ℝ M],
      let M' := M.map (iso.toLinearEquiv.toLinearMap.restrictScalars ℤ)
      DiscreteTopology M' ∧
        Submodule.span ℝ (M' : Set (EuclideanSpace ℝ (Fin (Fintype.card (InfinitePlace K × Unit × Fin 2))))) = ⊤ ∧
        covol M = ZLattice.covolume M' MeasureTheory.volume := by
    intro M _ _ M'
    let eqZ : M ≃ₗ[ℤ] M' :=
      { toFun := fun x => ⟨iso x.1, x.1, x.2, rfl⟩
        invFun := fun y => ⟨iso.symm y.1, by
          rcases y.2 with ⟨x, hx, hxy⟩
          rwa [show iso.symm y.1 = x from by rw [← hxy]; exact iso.symm_apply_apply x]⟩
        map_add' := fun x y => Subtype.ext (map_add iso x.1 y.1)
        map_smul' := fun c x => Subtype.ext (map_zsmul iso c x.1)
        left_inv := fun x => Subtype.ext (iso.symm_apply_apply x.1)
        right_inv := fun y => Subtype.ext (iso.apply_symm_apply y.1) }
    have hD : DiscreteTopology M' := discreteTopology_map_linearEquiv M iso.toLinearEquiv
    have hsp' : Submodule.span ℝ (M' : Set (EuclideanSpace ℝ
        (Fin (Fintype.card (InfinitePlace K × Unit × Fin 2))))) = ⊤ := by
      convert span_top_map_linearEquiv M iso.toLinearEquiv
    have : DiscreteTopology M' := hD
    have : IsZLattice ℝ M' := ⟨hsp'⟩
    refine ⟨hD, hsp', ?_⟩
    let bR := basisOfZLattice M'
    let bA := bR.map eqZ.symm
    rw [covol_eq_sqrt_det_gram M bA, covolume_eq_abs_det M' bR]
    let B : Matrix (Fin (Fintype.card (InfinitePlace K × Unit × Fin 2)))
        (Fin (Fintype.card (InfinitePlace K × Unit × Fin 2))) ℝ :=
      Matrix.of fun i j => ((bR i : M') : EuclideanSpace ℝ
        (Fin (Fintype.card (InfinitePlace K × Unit × Fin 2)))) j
    have hgram : Matrix.gram ℝ (fun i => ((bA i : M) :
        EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2))) = B * Bᵀ := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.transpose_apply, B, Matrix.of_apply]
      change ⟪((bA i : M) : EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2)),
        ((bA j : M) : EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2))⟫_ℝ = _
      have hmap : ∀ k, iso ((bA k : M) : EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2)) =
          ((bR k : M') : EuclideanSpace ℝ (Fin (Fintype.card (InfinitePlace K × Unit × Fin 2)))) :=
        fun k => by
          change iso (iso.symm (bR k : _)) = _; exact iso.apply_symm_apply _
      rw [← iso.inner_map_map, hmap i, hmap j, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
      refine Finset.sum_congr rfl fun k _ => by simp [mul_comm]
    rw [hgram, Matrix.det_mul, Matrix.det_transpose, ← sq, Real.sqrt_sq_eq_abs]
  obtain ⟨hD1, hsp1, hc1⟩ := hiso_invar L_one
  obtain ⟨hDJ, hspJ, hcJ⟩ := hiso_invar L_J
  have : DiscreteTopology Λ_one := hD1
  have : IsZLattice ℝ Λ_one := ⟨hsp1⟩
  have : DiscreteTopology Λ_J := hDJ
  have : IsZLattice ℝ Λ_J := ⟨hspJ⟩
  have hrel : L_J.toAddSubgroup.relIndex L_one.toAddSubgroup = Ideal.absNorm J := by
    have hinj : Function.Injective (realizeHLat (Basis.singleton Unit K)
        (fun _ : InfinitePlace K => (1 : Matrix Unit Unit ℂ))) :=
      realizeHLat_injective _ _ (fun _ => by simp)
    let f : 𝓞 K →+ EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2) :=
      (realizeHLat (Basis.singleton Unit K) (fun _ => 1)).comp
        (algebraMap (𝓞 K) K).toAddMonoidHom
    have hf_inj : Function.Injective f := hinj.comp RingOfIntegers.coe_injective
    have hf_range : f.range = L_one.toAddSubgroup := by
      ext y
      simp only [AddMonoidHom.mem_range, f, AddMonoidHom.comp_apply, L_one, zRealizeMod,
        Submodule.mem_toAddSubgroup, Submodule.mem_map]
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨(a : K), (Submodule.mem_one (R := 𝓞 K) (A := K)).mpr ⟨a, rfl⟩, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨a, ha⟩ := (Submodule.mem_one (R := 𝓞 K) (A := K)).mp hx
        exact ⟨a, by rw [← ha]; rfl⟩
    have hf_map : J.toAddSubgroup.map f = L_J.toAddSubgroup := by
      ext y
      simp only [AddSubgroup.mem_map, f, AddMonoidHom.comp_apply, L_J, zRealizeMod,
        Submodule.mem_toAddSubgroup, Submodule.mem_map]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨(a : K), (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mpr ⟨a, ha, rfl⟩, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hx
        exact ⟨a, ha, rfl⟩
    have hidx : L_J.toAddSubgroup.relIndex L_one.toAddSubgroup = J.toAddSubgroup.index := by
      rw [AddSubgroup.relIndex, AddSubgroup.index_eq_card, AddSubgroup.index_eq_card]
      refine Nat.card_congr ?_
      have hmem : ∀ y : L_one.toAddSubgroup, ∃ a : 𝓞 K, f a = y.1 := fun y => by
        have hy : y.1 ∈ L_one.toAddSubgroup := y.2
        have hy' : y.1 ∈ f.range := by rw [hf_range]; exact hy
        exact hy'
      let eQuot : L_one.toAddSubgroup ≃ 𝓞 K :=
        { toFun := fun y => (hmem y).choose
          invFun := fun a => ⟨f a, by
            rw [← hf_range]; exact ⟨a, rfl⟩⟩
          left_inv := fun y => Subtype.ext (hmem y).choose_spec
          right_inv := fun a => hf_inj (hmem ⟨f a, by
            rw [← hf_range]; exact ⟨a, rfl⟩⟩).choose_spec }
      refine _root_.Quotient.congr eQuot fun a b => ?_
      rw [QuotientAddGroup.leftRel_apply, QuotientAddGroup.leftRel_apply]
      simp only [AddSubgroup.mem_addSubgroupOf, ← hf_map]
      have ha_spec : f (eQuot a) = a.1 := (hmem a).choose_spec
      have hb_spec : f (eQuot b) = b.1 := (hmem b).choose_spec
      constructor
      · intro h
        change -a.1 + b.1 ∈ AddSubgroup.map f J.toAddSubgroup at h
        rw [AddSubgroup.mem_map] at h
        rcases h with ⟨c, hc, hce⟩
        change -eQuot a + eQuot b ∈ J.toAddSubgroup
        have heq : f (-eQuot a + eQuot b) = f c := by
          rw [map_add, map_neg, ha_spec, hb_spec, hce]
        exact (hf_inj heq).symm ▸ hc
      · intro hsub_J
        change -eQuot a + eQuot b ∈ J.toAddSubgroup at hsub_J
        change -a.1 + b.1 ∈ AddSubgroup.map f J.toAddSubgroup
        rw [AddSubgroup.mem_map]
        exact ⟨-eQuot a + eQuot b, hsub_J, by rw [map_add, map_neg, ha_spec, hb_spec]⟩
    rw [hidx, ← Ideal.absNorm_eq_index]
  have hrelΛ : Λ_J.toAddSubgroup.relIndex Λ_one.toAddSubgroup =
      L_J.toAddSubgroup.relIndex L_one.toAddSubgroup := by
    rw [AddSubgroup.relIndex, AddSubgroup.relIndex, AddSubgroup.index_eq_card,
      AddSubgroup.index_eq_card]
    refine (Nat.card_congr ?_).symm
    let g : EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2) ≃+
        EuclideanSpace ℝ (Fin (Fintype.card (InfinitePlace K × Unit × Fin 2))) :=
      iso.toLinearEquiv.toAddEquiv
    let eQuot : L_one.toAddSubgroup ≃ Λ_one.toAddSubgroup :=
      { toFun := fun x => ⟨g x.1, ⟨x.1, x.2, rfl⟩⟩
        invFun := fun y => ⟨g.symm y.1, by
          rcases y.2 with ⟨x, hx, hxy⟩
          rw [show g.symm y.1 = x from by rw [← hxy]; exact g.symm_apply_apply x]
          exact hx⟩
        left_inv := fun x => Subtype.ext (g.symm_apply_apply x.1)
        right_inv := fun y => Subtype.ext (g.apply_symm_apply y.1) }
    refine _root_.Quotient.congr eQuot fun a b => ?_
    rw [QuotientAddGroup.leftRel_apply, QuotientAddGroup.leftRel_apply]
    simp only [AddSubgroup.mem_addSubgroupOf]
    change (-a.1 + b.1 ∈ L_J) ↔ (-g a.1 + g b.1 ∈ Λ_J)
    rw [← map_neg g, ← map_add g]
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨x, hx, hgx⟩ => by rw [← g.injective hgx]; exact hx⟩
  rw [hcJ, hc1, zlattice_covolume_sublattice_eq_relIndex Λ_one Λ_J hsub_Λ, hrelΛ, hrel]

private structure ClearedFrac (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (J : FractionalIdeal (𝓞 K)⁰ K) where
  a : 𝓞 K
  haK0 : (a : K) ≠ 0
  J₀ : Ideal (𝓞 K)
  hJ₀0 : J₀ ≠ ⊥
  hJ₀_eq : FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K) * J = (J₀ : FractionalIdeal (𝓞 K)⁰ K)
  e_a : EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2) ≃ₗ[ℝ]
    EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2)
  he_a_eq : e_a.toLinearMap =
    placeBlockLin (fun v => Matrix.diagonal fun _ : Unit => v.embedding (a : K))
  he_a_symm_eq : e_a.symm.toLinearMap =
    placeBlockLin (fun v => Matrix.diagonal fun _ : Unit => (v.embedding (a : K))⁻¹)
  hmap_inv :
    zRealizeMod (Basis.singleton Unit K) (fun _ => 1) (J : Submodule (𝓞 K) K) =
      (zRealizeMod (Basis.singleton Unit K) (fun _ => 1)
        ((J₀ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)).map
          (e_a.symm.toLinearMap.restrictScalars ℤ)

private noncomputable def mkClearedFrac (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (J : FractionalIdeal (𝓞 K)⁰ K) (hJ : J ≠ 0) : ClearedFrac K J := by
  classical
  let a := J.isFractional.choose
  have ha1 : a ∈ (𝓞 K)⁰ := J.isFractional.choose_spec.1
  have ha2 : ∀ b ∈ J, IsLocalization.IsInteger (𝓞 K) (a • b) := J.isFractional.choose_spec.2
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha1
  have haK0 : (a : K) ≠ 0 := Subtype.coe_ne_coe.mpr ha0
  let J₀ : Ideal (𝓞 K) :=
    { carrier := { b : 𝓞 K | ∃ x ∈ J, (a : K) * x = (b : K) }
      add_mem' := fun {b₁ b₂} ⟨x₁, hx₁, h1⟩ ⟨x₂, hx₂, h2⟩ =>
        ⟨x₁ + x₂, (J : Submodule (𝓞 K) K).add_mem hx₁ hx₂, by rw [mul_add, h1, h2]; rfl⟩
      zero_mem' := ⟨0, (J : Submodule (𝓞 K) K).zero_mem, by simp⟩
      smul_mem' := fun r {b} ⟨x, hx, hb⟩ =>
        ⟨r • x, (J : Submodule (𝓞 K) K).smul_mem r hx, by
          rw [← algebraMap_smul K r x, mul_comm, smul_mul_assoc, mul_comm, hb]
          simp⟩ }
  have hJ₀_eq : FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K) * J =
      (J₀ : FractionalIdeal (𝓞 K)⁰ K) := by
    apply le_antisymm
    · rw [FractionalIdeal.mul_le]
      intro u hu v hv
      obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hu
      obtain ⟨w, hw⟩ := ha2 v hv
      have hr : r • (a : K) * v = (a : K) * (r • v) := by
        rw [smul_mul_assoc, mul_comm (a : K), ← smul_mul_assoc]; ring
      rw [hr]
      have haw : (a : K) * (r • v) = ((r * w : 𝓞 K) : K) := by
        calc (a : K) * (r • v) = r • ((a : K) * v) := mul_smul_comm r (a : K) v
          _ = r • (a • v) := rfl
          _ = r • (w : K) := by rw [← hw]
          _ = ((r * w : 𝓞 K) : K) := by simp [Algebra.smul_def]
      exact (FractionalIdeal.mem_coeIdeal _).mpr ⟨r * w, ⟨r • v, (J : Submodule (𝓞 K) K).smul_mem r hv, haw⟩, haw.symm⟩
    · intro x hx
      obtain ⟨b, ⟨y, hy, hby⟩, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hx
      change ((b : 𝓞 K) : K) ∈ FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K) * J
      rw [← hby]
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hy
  have hJ₀0 : J₀ ≠ ⊥ := by
    intro hbot
    rw [hbot, FractionalIdeal.coeIdeal_bot] at hJ₀_eq
    have hsp0 : FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K) ≠ 0 := by
      rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact haK0
    exact mul_ne_zero hsp0 hJ hJ₀_eq
  let T_a : EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2) →ₗ[ℝ]
      EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2) :=
    placeBlockLin (fun v => Matrix.diagonal fun _ : Unit => v.embedding (a : K))
  let T_ainv : EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2) →ₗ[ℝ]
      EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2) :=
    placeBlockLin (fun v => Matrix.diagonal fun _ : Unit => (v.embedding (a : K))⁻¹)
  let e_a : EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2) ≃ₗ[ℝ]
      EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2) :=
    { toLinearMap := T_a
      invFun := T_ainv
      left_inv := fun x => by
        have h1 : T_ainv.comp T_a = LinearMap.id := by
          rw [← placeBlockLin_mul]
          convert placeBlockLin_one (K := K) (ι := Unit) using 2
          funext v; ext i j
          simp [inv_mul_cancel₀ ((map_ne_zero_iff v.embedding (RingHom.injective _)).mpr haK0)]
        exact LinearMap.congr_fun h1 x
      right_inv := fun x => by
        have h1 : T_a.comp T_ainv = LinearMap.id := by
          rw [← placeBlockLin_mul]
          convert placeBlockLin_one (K := K) (ι := Unit) using 2
          funext v; ext i j
          simp [mul_inv_cancel₀ ((map_ne_zero_iff v.embedding (RingHom.injective _)).mpr haK0)]
        exact LinearMap.congr_fun h1 x }
  have he_realize : ∀ x : K, e_a (realizeHLat (Basis.singleton Unit K) (fun _ => 1) x) =
      realizeHLat (Basis.singleton Unit K) (fun _ => 1) ((a : K) * x) := by
    intro x
    ext p; rcases p with ⟨v, ⟨⟨⟩, j⟩⟩
    change (complexToRealLin (Matrix.diagonal fun _ => v.embedding (a : K)) _).ofLp ((), j) = _
    simp only [complexToRealLin, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp,
      Matrix.mulVec_diagonal, realizeHLat, AddMonoidHom.coe_mk, ZeroHom.coe_mk, fcoord, inv_one,
      Matrix.one_mulVec, vecAt, Basis.singleton_repr]
    fin_cases j
    · simp [map_mul, Complex.mul_re]
    · simp [map_mul, Complex.mul_im]
  have hmap_inv :
      zRealizeMod (Basis.singleton Unit K) (fun _ => 1) (J : Submodule (𝓞 K) K) =
        (zRealizeMod (Basis.singleton Unit K) (fun _ => 1)
          ((J₀ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)).map
            (e_a.symm.toLinearMap.restrictScalars ℤ) := by
    ext y
    simp only [Submodule.mem_map, zRealizeMod]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨realizeHLat (Basis.singleton Unit K) (fun _ => 1) ((a : K) * x), ?_, ?_⟩
      · obtain ⟨w, hw⟩ := ha2 x hx
        have hw' : (a : K) * x = (w : K) := hw.symm
        refine ⟨(a : K) * x, (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mpr ⟨w, ⟨x, hx, hw'⟩, hw'.symm⟩, rfl⟩
      · change e_a.symm (realizeHLat _ _ ((a : K) * x)) = realizeHLat _ _ x
        rw [← he_realize x, e_a.symm_apply_apply]
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      obtain ⟨b, ⟨x, hx, hbx⟩, rfl⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hz
      refine ⟨x, hx, ?_⟩
      change realizeHLat _ _ x = e_a.symm (realizeHLat _ _ ((b : 𝓞 K) : K))
      rw [← hbx, ← he_realize x, e_a.symm_apply_apply]
  exact ⟨a, haK0, J₀, hJ₀0, hJ₀_eq, e_a, rfl, rfl, hmap_inv⟩

private lemma isZLattice_single_fractional (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (J : FractionalIdeal (𝓞 K)⁰ K) (hJ : J ≠ 0) :
    DiscreteTopology (zRealizeMod (Basis.singleton Unit K) (fun _ => 1) (J : Submodule (𝓞 K) K)) ∧
      Submodule.span ℝ ((zRealizeMod (Basis.singleton Unit K) (fun _ => 1)
        (J : Submodule (𝓞 K) K)) :
          Set (EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2))) = ⊤ := by
  let cf := mkClearedFrac K J hJ
  obtain ⟨hDisc_J₀, hsp_J₀⟩ := isZLattice_single_ideal K cf.J₀ cf.hJ₀0
  have : DiscreteTopology (zRealizeMod (Basis.singleton Unit K) (fun _ => 1)
      ((cf.J₀ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) := hDisc_J₀
  have : IsZLattice ℝ (zRealizeMod (Basis.singleton Unit K) (fun _ => 1)
      ((cf.J₀ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) := ⟨hsp_J₀⟩
  have hD : DiscreteTopology (zRealizeMod (Basis.singleton Unit K) (fun _ => 1)
      (J : Submodule (𝓞 K) K)) := by
    rw [cf.hmap_inv]; exact discreteTopology_map_linearEquiv _ cf.e_a.symm
  have hsp : Submodule.span ℝ ((zRealizeMod (Basis.singleton Unit K) (fun _ => 1)
      (J : Submodule (𝓞 K) K)) : Set (EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2))) = ⊤ := by
    rw [cf.hmap_inv]; exact span_top_map_linearEquiv _ cf.e_a.symm
  exact ⟨hD, hsp⟩

/-- Exact `covol` of any nonzero fractional ideal `J : FractionalIdeal (𝓞 K)⁰ K` inside
`EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2)`. -/
theorem covol_single_fractional_eq (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (J : FractionalIdeal (𝓞 K)⁰ K) (hJ : J ≠ 0) :
    covol (zRealizeMod (Basis.singleton Unit K) (fun _ => 1) (J : Submodule (𝓞 K) K)) =
      (FractionalIdeal.absNorm J : ℝ) *
        covol (zRealizeMod (Basis.singleton Unit K) (fun _ => 1) (1 : Submodule (𝓞 K) K)) := by
  classical
  let cf := mkClearedFrac K J hJ
  obtain ⟨hDisc_J₀, hsp_J₀⟩ := isZLattice_single_ideal K cf.J₀ cf.hJ₀0
  have : DiscreteTopology (zRealizeMod (Basis.singleton Unit K) (fun _ => 1)
      ((cf.J₀ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) := hDisc_J₀
  have : IsZLattice ℝ (zRealizeMod (Basis.singleton Unit K) (fun _ => 1)
      ((cf.J₀ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) := ⟨hsp_J₀⟩
  have hcov_J₀ := covol_single_ideal_eq K cf.J₀ cf.hJ₀0
  have hcov_inv := covol_map_linearEquiv (zRealizeMod (Basis.singleton Unit K) (fun _ => 1)
      ((cf.J₀ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) cf.e_a.symm
  rw [← cf.hmap_inv] at hcov_inv
  have hdet_inv : |LinearMap.det cf.e_a.symm.toLinearMap| =
      (|((Algebra.norm ℚ (cf.a : K) : ℚ) : ℝ)|)⁻¹ := by
    rw [cf.he_a_symm_eq, abs_det_placeBlockLin]
    have hnorm : |((Algebra.norm ℚ (cf.a : K) : ℚ) : ℝ)| =
        ∏ v : InfinitePlace K, ‖v.embedding (cf.a : K)‖ ^ 2 := by
      have hcast : |((Algebra.norm ℚ (cf.a : K) : ℚ) : ℝ)| =
          ((|Algebra.norm ℚ (cf.a : K)| : ℚ) : ℝ) := by
        exact_mod_cast (Rat.cast_abs (Algebra.norm ℚ (cf.a : K))).symm
      rw [hcast, ← NumberField.InfinitePlace.prod_eq_abs_norm (cf.a : K)]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [(IsTotallyComplex.isComplex v).mult_eq_two, NumberField.InfinitePlace.norm_embedding_eq]
    rw [hnorm, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [Matrix.det_diagonal, Fintype.prod_unique, norm_inv, inv_pow]
  have hnorm_mul : |((Algebra.norm ℚ (cf.a : K) : ℚ) : ℝ)| * (FractionalIdeal.absNorm J : ℝ) =
      (Ideal.absNorm cf.J₀ : ℝ) := by
    have h1 := congrArg FractionalIdeal.absNorm cf.hJ₀_eq
    rw [map_mul, FractionalIdeal.absNorm_span_singleton, FractionalIdeal.coeIdeal_absNorm] at h1
    have h2 := congrArg (Rat.cast : ℚ → ℝ) h1
    push_cast at h2
    exact h2
  have ha_norm_pos : 0 < |((Algebra.norm ℚ (cf.a : K) : ℚ) : ℝ)| := by
    rw [abs_pos]
    exact_mod_cast (Algebra.norm_ne_zero_iff.mpr cf.haK0)
  rw [hcov_inv, hdet_inv, hcov_J₀, ← hnorm_mul]
  field_simp [ha_norm_pos.ne']

/-- Exact `muOK` of a nonzero fractional ideal `J` on `K`:
`muOK ... J = -(2 * log (FractionalIdeal.absNorm J) / [K : ℚ])`. -/
theorem muOK_single_fractional_eq (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (J : FractionalIdeal (𝓞 K)⁰ K) (hJ : J ≠ 0) :
    muOK (Basis.singleton Unit K) (fun _ => 1) (J : Submodule (𝓞 K) K) =
      -(2 * Real.log (FractionalIdeal.absNorm J : ℝ) / (Module.finrank ℚ K : ℝ)) := by
  let L_J := zRealizeMod (Basis.singleton Unit K) (fun _ => 1) (J : Submodule (𝓞 K) K)
  obtain ⟨hD_J, hsp_J⟩ := isZLattice_single_fractional K J hJ
  have : DiscreteTopology L_J := hD_J
  have : IsZLattice ℝ L_J := ⟨hsp_J⟩
  have hcov := covol_single_fractional_eq K J hJ
  have hcov1 := covol_single_one_eq K
  have hJ_pos : (0 : ℝ) < (FractionalIdeal.absNorm J : ℝ) := by
    have hcov_Jpos : 0 < covol L_J := covol_pos L_J
    have hcov1_pos : 0 < covol (zRealizeMod (Basis.singleton Unit K) (fun _ => 1) (1 : Submodule (𝓞 K) K)) := by
      rw [hcov1]
      exact mul_pos (by positivity) (Real.sqrt_pos.mpr (abs_pos.mpr
        (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))))
    nlinarith
  have hdisc_pos : 0 < |(NumberField.discr K : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
  have hrk : rk L_J = Module.finrank ℚ K := by
    unfold ArakelovCovolume.rk
    rw [ZLattice.rank ℝ L_J,
      (euclideanSpaceCongr (Fintype.equivFin (InfinitePlace K × Unit × Fin 2))).toLinearEquiv.finrank_eq,
      finrank_euclideanSpace_fin, Fintype.card_prod, Fintype.card_prod,
      Fintype.card_unique (α := Unit), Fintype.card_fin,
      finrank_eq_two_mul_card_infinitePlace K]
    ring
  have hdK : (Module.finrank ℚ K : ℝ) = 2 * (Fintype.card (InfinitePlace K) : ℝ) := by
    exact_mod_cast finrank_eq_two_mul_card_infinitePlace K
  have hlog_cov : Real.log (covol L_J) =
      Real.log (FractionalIdeal.absNorm J : ℝ) -
        (Fintype.card (InfinitePlace K) : ℝ) * Real.log 2 +
        (1 / 2) * Real.log |(NumberField.discr K : ℝ)| := by
    rw [hcov, hcov1,
      Real.log_mul hJ_pos.ne' (mul_pos (by positivity) (Real.sqrt_pos.mpr hdisc_pos)).ne',
      Real.log_mul (by positivity) (Real.sqrt_pos.mpr hdisc_pos).ne',
      Real.log_rpow (by norm_num : (0 : ℝ) < 2), Real.sqrt_eq_rpow,
      Real.log_rpow hdisc_pos]
    ring
  unfold muOK ArakelovCovolume.slope ArakelovCovolume.degAr NumberFieldHLat.logDiscDivDeg
  rw [hrk, hlog_cov]
  have hn_ne : (Fintype.card (InfinitePlace K) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  rw [hdK]
  field_simp [hn_ne, two_ne_zero]
  ring

end IdealCovolumeAndLines

section LineBoundsAndOrthogonalISup

private lemma fractionalIdeal_absNorm_mono (K : Type) [Field K] [NumberField K]
    [IsTotallyComplex K] (I J : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) (hJ : J ≠ 0)
    (hle : (J : Submodule (𝓞 K) K) ≤ (I : Submodule (𝓞 K) K)) :
    (FractionalIdeal.absNorm I : ℝ) ≤ (FractionalIdeal.absNorm J : ℝ) := by
  let cf := mkClearedFrac K I hI
  let J_mul : FractionalIdeal (𝓞 K)⁰ K := FractionalIdeal.spanSingleton (𝓞 K)⁰ (cf.a : K) * J
  have hmul_le : (J_mul : Submodule (𝓞 K) K) ≤
      ((cf.J₀ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
    rw [← cf.hJ₀_eq, FractionalIdeal.coe_mul, FractionalIdeal.coe_mul]
    exact Submodule.mul_le.mpr fun x hx y hy => Submodule.mul_mem_mul hx (hle hy)
  let J₀ : Ideal (𝓞 K) :=
    { carrier := { r : 𝓞 K | (r : K) ∈ (J_mul : Submodule (𝓞 K) K) }
      add_mem' := fun {r s} hr hs => by
        change ((r + s : 𝓞 K) : K) ∈ (J_mul : Submodule (𝓞 K) K)
        push_cast
        exact Submodule.add_mem _ hr hs
      zero_mem' := by
        change ((0 : 𝓞 K) : K) ∈ (J_mul : Submodule (𝓞 K) K)
        simp
      smul_mem' := fun c {r} hr => by
        change ((c • r : 𝓞 K) : K) ∈ (J_mul : Submodule (𝓞 K) K)
        rw [smul_eq_mul]
        push_cast
        exact Submodule.smul_mem _ c hr }
  have hJ₀_eq : (J₀ : FractionalIdeal (𝓞 K)⁰ K) = J_mul := by
    apply FractionalIdeal.ext
    intro x
    simp only [FractionalIdeal.mem_coeIdeal]
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact hr
    · intro hx
      have hx' : x ∈ ((cf.J₀ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := hmul_le hx
      obtain ⟨r, _, hr⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hx'
      refine ⟨r, ?_, hr⟩
      change (r : K) ∈ (J_mul : Submodule (𝓞 K) K)
      change (r : K) = x at hr
      rwa [hr]
  have hJ₀_le : J₀ ≤ cf.J₀ := by
    intro r hr
    have hr' : (r : K) ∈ ((cf.J₀ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) :=
      hmul_le hr
    obtain ⟨s, hs, hrs⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hr'
    have hEq : r = s := Subtype.ext hrs.symm
    rwa [hEq]
  have hJ_mul_ne : J_mul ≠ 0 := by
    refine mul_ne_zero ?_ hJ
    simp [FractionalIdeal.spanSingleton_eq_zero_iff, cf.haK0]
  have hJ₀_ne : J₀ ≠ ⊥ := by
    intro hbot
    apply hJ_mul_ne
    rw [← hJ₀_eq, hbot, FractionalIdeal.coeIdeal_bot]
  have hidx_pos : 0 < J₀.toAddSubgroup.index := by
    rw [← Ideal.absNorm_eq_index]
    have hcov_pos : 0 < covol (zRealizeMod (Basis.singleton Unit K) (fun _ => 1)
        ((J₀ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) := by
      obtain ⟨hD, _⟩ := isZLattice_single_ideal K J₀ hJ₀_ne
      have : DiscreteTopology (zRealizeMod (Basis.singleton Unit K) (fun _ => 1)
          ((J₀ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) := hD
      exact ArakelovCovolume.covol_pos _
    rw [covol_single_ideal_eq K J₀ hJ₀_ne] at hcov_pos
    obtain ⟨hD1, _⟩ := isZLattice_single_one K
    have : DiscreteTopology (zRealizeMod (Basis.singleton Unit K) (fun _ => 1)
        (1 : Submodule (𝓞 K) K)) := hD1
    exact_mod_cast (mul_pos_iff_of_pos_right (ArakelovCovolume.covol_pos _)).mp hcov_pos
  have hmul_idx := AddSubgroup.relIndex_mul_index (show J₀.toAddSubgroup ≤ cf.J₀.toAddSubgroup from hJ₀_le)
  have hrel_pos : 0 < J₀.toAddSubgroup.relIndex cf.J₀.toAddSubgroup := by
    by_contra h0
    have h0' : J₀.toAddSubgroup.relIndex cf.J₀.toAddSubgroup = 0 := Nat.eq_zero_of_not_pos h0
    rw [h0', zero_mul] at hmul_idx
    exact hidx_pos.ne' hmul_idx.symm
  have hnorm_le_int : Ideal.absNorm cf.J₀ ≤ Ideal.absNorm J₀ := by
    rw [Ideal.absNorm_eq_index, Ideal.absNorm_eq_index, ← hmul_idx]
    exact Nat.le_mul_of_pos_left _ hrel_pos
  have hnorm_le_real : (Ideal.absNorm cf.J₀ : ℝ) ≤ (Ideal.absNorm J₀ : ℝ) := by
    exact_mod_cast hnorm_le_int
  have h1 : |((Algebra.norm ℚ (cf.a : K) : ℚ) : ℝ)| * (FractionalIdeal.absNorm I : ℝ) =
      (Ideal.absNorm cf.J₀ : ℝ) := by
    have h := congrArg FractionalIdeal.absNorm cf.hJ₀_eq
    rw [map_mul, FractionalIdeal.absNorm_span_singleton, FractionalIdeal.coeIdeal_absNorm] at h
    exact_mod_cast h
  have h2 : |((Algebra.norm ℚ (cf.a : K) : ℚ) : ℝ)| * (FractionalIdeal.absNorm J : ℝ) =
      (Ideal.absNorm J₀ : ℝ) := by
    have h := congrArg FractionalIdeal.absNorm hJ₀_eq
    rw [map_mul, FractionalIdeal.absNorm_span_singleton, FractionalIdeal.coeIdeal_absNorm] at h
    exact_mod_cast h.symm
  have ha_pos : 0 < |((Algebra.norm ℚ (cf.a : K) : ℚ) : ℝ)| := by
    rw [abs_pos]
    exact_mod_cast (Algebra.norm_ne_zero_iff.mpr cf.haK0)
  nlinarith

private lemma covol_eq_of_homothety
    {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    (L₁ : Submodule ℤ E₁) (L₂ : Submodule ℤ E₂)
    [DiscreteTopology L₁] [DiscreteTopology L₂]
    (e : L₁ ≃ₗ[ℤ] L₂) (c : ℝ) (hc : 0 < c)
    (hnorm : ∀ x : L₁, ‖((e x : L₂) : E₂)‖ = c * ‖((x : L₁) : E₁)‖) :
    ArakelovCovolume.rk L₂ = ArakelovCovolume.rk L₁ ∧
      ArakelovCovolume.covol L₂ = c ^ (ArakelovCovolume.rk L₁) * ArakelovCovolume.covol L₁ := by
  have hrk : ArakelovCovolume.rk L₂ = ArakelovCovolume.rk L₁ := by
    unfold ArakelovCovolume.rk
    exact LinearEquiv.finrank_eq e.symm
  refine ⟨hrk, ?_⟩
  let b₁ : Basis (Fin (ArakelovCovolume.rk L₁)) ℤ L₁ := Module.finBasis ℤ L₁
  let b₂ : Basis (Fin (ArakelovCovolume.rk L₁)) ℤ L₂ := b₁.map e
  rw [ArakelovCovolume.covol_eq_sqrt_det_gram L₁ b₁,
    ArakelovCovolume.covol_eq_sqrt_det_gram L₂ b₂]
  have hgram : Matrix.gram ℝ (fun i => ((b₂ i : L₂) : E₂)) =
      (c ^ 2) • Matrix.gram ℝ (fun i => ((b₁ i : L₁) : E₁)) := by
    ext i j
    simp only [Matrix.gram_apply, Matrix.smul_apply, smul_eq_mul]
    have hadd : ‖((e (b₁ i + b₁ j) : L₂) : E₂)‖ = c * ‖(((b₁ i + b₁ j : L₁) : E₁))‖ :=
      hnorm (b₁ i + b₁ j)
    have hadd' : ((e (b₁ i + b₁ j) : L₂) : E₂) =
        ((b₂ i : L₂) : E₂) + ((b₂ j : L₂) : E₂) := by
      rw [map_add, Submodule.coe_add]
      rfl
    have hbi : ((b₂ i : L₂) : E₂) = ((e (b₁ i) : L₂) : E₂) := rfl
    have hbj : ((b₂ j : L₂) : E₂) = ((e (b₁ j) : L₂) : E₂) := rfl
    have hi : ‖((b₂ i : L₂) : E₂)‖ = c * ‖((b₁ i : L₁) : E₁)‖ := hnorm (b₁ i)
    have hj : ‖((b₂ j : L₂) : E₂)‖ = c * ‖((b₁ j : L₁) : E₁)‖ := hnorm (b₁ j)
    rw [hadd'] at hadd
    have hsq := congrArg (fun t : ℝ => t ^ 2) hadd
    rw [norm_add_sq_real, mul_pow, Submodule.coe_add, norm_add_sq_real] at hsq
    rw [hi, hj] at hsq
    linarith
  rw [hgram, Matrix.det_smul, Fintype.card_fin, show (c ^ 2) ^ ArakelovCovolume.rk L₁ =
    (c ^ ArakelovCovolume.rk L₁) ^ 2 by ring, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (pow_nonneg hc.le _)]

private lemma slope_eq_sub_log_of_homothety
    {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    (L₁ : Submodule ℤ E₁) (L₂ : Submodule ℤ E₂)
    [DiscreteTopology L₁] [DiscreteTopology L₂]
    (hL₁ : L₁ ≠ ⊥) (e : L₁ ≃ₗ[ℤ] L₂) (c : ℝ) (hc : 0 < c)
    (hnorm : ∀ x : L₁, ‖((e x : L₂) : E₂)‖ = c * ‖((x : L₁) : E₁)‖) :
    ArakelovCovolume.slope L₂ = ArakelovCovolume.slope L₁ - Real.log c := by
  obtain ⟨hrk, hcov⟩ := covol_eq_of_homothety L₁ L₂ e c hc hnorm
  have hrk_pos : 0 < (ArakelovCovolume.rk L₁ : ℝ) := by
    exact_mod_cast ArakelovCovolume.rk_pos_of_ne_bot L₁ hL₁
  have hcov_pos : 0 < ArakelovCovolume.covol L₁ := ArakelovCovolume.covol_pos L₁
  unfold ArakelovCovolume.slope ArakelovCovolume.degAr
  rw [hrk, hcov, Real.log_mul (pow_pos hc _).ne' hcov_pos.ne', Real.log_pow]
  field_simp [hrk_pos.ne']
  ring

private lemma discreteTopology_idealSmul_stdMonomial (K MonI : Type)
    [Field K] [NumberField K] [IsTotallyComplex K] [Fintype MonI] [DecidableEq MonI]
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (w : MonI → ℝ) (hw : ∀ m, 0 < w m) :
    DiscreteTopology (zRealizeMod (Pi.basisFun K MonI) (monX (K := K) w)
      (idealSmul (I : Submodule (𝓞 K) K) (stdMonomialLat K MonI))) := by
  let L_I := zRealizeMod (Basis.singleton Unit K) (fun _ => 1) (I : Submodule (𝓞 K) K)
  obtain ⟨hD_I, _⟩ := isZLattice_single_fractional K I hI
  have : DiscreteTopology L_I := hD_I
  let L_M := zRealizeMod (Pi.basisFun K MonI) (monX (K := K) w)
    (idealSmul (I : Submodule (𝓞 K) K) (stdMonomialLat K MonI))
  let f_allLin : EuclideanSpace ℝ (InfinitePlace K × MonI × Fin 2) →ₗ[ℝ]
      (MonI → EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2)) :=
    { toFun := fun u m => WithLp.toLp 2 fun p => (Real.sqrt (w m))⁻¹ * u (p.1, m, p.2.2)
      map_add' := fun u₁ u₂ => by ext m p; simp [mul_add]
      map_smul' := fun c u => by ext m p; simp; ring }
  let f_all : EuclideanSpace ℝ (InfinitePlace K × MonI × Fin 2) →
      (MonI → EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2)) := f_allLin
  have hf_cont : Continuous f_all := f_allLin.continuous_of_finiteDimensional
  have hf_inj : Function.Injective f_all := by
    intro u₁ u₂ h
    ext p
    rcases p with ⟨v, m, j⟩
    have hm := congrArg (fun g => (g m).ofLp (v, (), j)) h
    simp only [f_all, f_allLin, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp] at hm
    exact mul_left_cancel₀ (inv_ne_zero (Real.sqrt_pos.mpr (hw m)).ne') hm
  have hf_mem : ∀ u : L_M, ∀ m : MonI, f_all u.1 m ∈ L_I := by
    rintro ⟨u, ⟨x, hx, rfl⟩⟩ m
    have hx' : x ∈ ⨆ m' : MonI, (I : Submodule (𝓞 K) K).map
        ((LinearMap.toSpanSingleton K (MonI → K) (Pi.single m' (1 : K))).restrictScalars (𝓞 K)) := by
      rwa [← idealSmul_stdMonomial_eq]
    have hx_m : x m ∈ (I : Submodule (𝓞 K) K) := by
      let S : Submodule (𝓞 K) (MonI → K) :=
        { carrier := { y : MonI → K | y m ∈ (I : Submodule (𝓞 K) K) }
          add_mem' := fun hy hz => Submodule.add_mem _ hy hz
          zero_mem' := Submodule.zero_mem _
          smul_mem' := fun c _ hy => Submodule.smul_mem _ c hy }
      have hle : (⨆ m' : MonI, (I : Submodule (𝓞 K) K).map
          ((LinearMap.toSpanSingleton K (MonI → K) (Pi.single m' (1 : K))).restrictScalars (𝓞 K))) ≤ S := by
        refine iSup_le fun m' => Submodule.map_le_iff_le_comap.mpr fun a ha => ?_
        simp only [Submodule.mem_comap, LinearMap.coe_restrictScalars, LinearMap.toSpanSingleton_apply]
        by_cases hmm : m = m'
        · subst hmm
          simpa [S] using ha
        · simp [S, hmm]
          exact Submodule.zero_mem _
      exact hle hx'
    refine ⟨x m, hx_m, ?_⟩
    ext p
    rcases p with ⟨v, ⟨⟨⟩, j⟩⟩
    have hw_ne : Real.sqrt (w m) ≠ 0 := (Real.sqrt_pos.mpr (hw m)).ne'
    have hfcoord_eq : fcoord (Pi.basisFun K MonI) (monX (K := K) w) v x m =
        (Real.sqrt (w m) : ℂ) * fcoord (Basis.singleton Unit K) (fun _ => 1) v (x m) () := by
      simp only [fcoord, inv_one, Matrix.one_mulVec, vecAt, Basis.singleton_repr]
      have hinv : (monX (K := K) w v)⁻¹ =
          Matrix.diagonal fun m' : MonI => ((Real.sqrt (w m') : ℝ) : ℂ) := by
        refine inv_eq_right_inv ?_
        rw [monX, Matrix.diagonal_mul_diagonal]
        ext i j
        by_cases hij : i = j
        · subst hij
          simp [(Real.sqrt_pos.mpr (hw i)).ne']
        · simp [hij]
      rw [hinv, Matrix.mulVec_diagonal]
      simp [vecAt]
    fin_cases j
    · simp [f_all, f_allLin, realizeHLat, hfcoord_eq, hw_ne]
    · simp [f_all, f_allLin, realizeHLat, hfcoord_eq, hw_ne]
  let g : L_M → (MonI → L_I) := fun u m => ⟨f_all u.1 m, hf_mem u m⟩
  refine DiscreteTopology.of_continuous_injective (f := g) ?_ ?_
  · refine continuous_pi fun m => Continuous.subtype_mk ?_ _
    exact (continuous_apply m).comp (hf_cont.comp continuous_subtype_val)
  · intro u₁ u₂ h
    apply Subtype.ext
    apply hf_inj
    funext m
    exact congrArg (fun k => (k m).1) h

/-- **Exact Slope Bound on Any Coordinate Line (`max_slope_line_neg_log`)**:
For any nonzero `𝓞_K`-submodule `N` contained in the `m`-th monomial coordinate line
`I · e_m` with weight `0 < c₀ ≤ w m`,
`muOK (Pi.basisFun K MonI) (monX w) N ≤ -Real.log c₀ - 2 * Real.log (absNorm I) / [K : ℚ]`. -/
theorem max_slope_line_neg_log (K MonI : Type)
    [Field K] [NumberField K] [IsTotallyComplex K] [Fintype MonI] [DecidableEq MonI]
    (w : MonI → ℝ) (hw : ∀ m, 0 < w m) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (m : MonI) (hcw : c₀ ≤ w m)
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (N : Submodule (𝓞 K) (MonI → K))
    (hN_le : N ≤ (I : Submodule (𝓞 K) K).map
      ((LinearMap.toSpanSingleton K (MonI → K) (Pi.single m (1 : K))).restrictScalars (𝓞 K)))
    (hN_ne : N ≠ ⊥) :
    muOK (Pi.basisFun K MonI) (monX (K := K) w) N ≤
      -Real.log c₀ - 2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ) := by
  let lineMap : K →ₗ[𝓞 K] (MonI → K) :=
    (LinearMap.toSpanSingleton K (MonI → K) (Pi.single m (1 : K))).restrictScalars (𝓞 K)
  have hN_ideal : N ≤ idealSmul (I : Submodule (𝓞 K) K) (stdMonomialLat K MonI) := by
    rw [idealSmul_stdMonomial_eq]
    exact hN_le.trans (le_iSup (fun m' : MonI => (I : Submodule (𝓞 K) K).map
      ((LinearMap.toSpanSingleton K (MonI → K) (Pi.single m' (1 : K))).restrictScalars (𝓞 K))) m)
  have : DiscreteTopology (zRealizeMod (Pi.basisFun K MonI) (monX (K := K) w)
      (idealSmul (I : Submodule (𝓞 K) K) (stdMonomialLat K MonI))) :=
    discreteTopology_idealSmul_stdMonomial K MonI I hI w hw
  have : DiscreteTopology (zRealizeMod (Pi.basisFun K MonI) (monX (K := K) w) N) :=
    ArakelovCovolume.discreteTopology_of_le (Submodule.map_mono (Submodule.restrictScalars_mono ℤ hN_ideal))
  let J_N : Submodule (𝓞 K) K := N.comap lineMap
  have hJ_N_le : J_N ≤ (I : Submodule (𝓞 K) K) := by
    intro a ha
    have hmem : a • Pi.single m (1 : K) ∈ N := ha
    obtain ⟨b, hb, hba⟩ := hN_le hmem
    have hcoord := congrArg (fun f : MonI → K => f m) hba
    simp only [LinearMap.coe_restrictScalars, LinearMap.toSpanSingleton_apply,
      Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one] at hcoord
    rwa [← hcoord]
  have hJ_N_frac : IsFractional (𝓞 K)⁰ J_N := by
    obtain ⟨d, hd, hIf⟩ := I.isFractional
    exact ⟨d, hd, fun x hx => hIf x (hJ_N_le hx)⟩
  let J : FractionalIdeal (𝓞 K)⁰ K := ⟨J_N, hJ_N_frac⟩
  have hJ_ne : J ≠ 0 := by
    intro h0
    apply hN_ne
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨a, ha, rfl⟩ := hN_le hx
    have ha_mem : a ∈ J_N := hx
    have ha0 : a = 0 := by
      have : a ∈ ((0 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
        rw [← h0]; exact ha_mem
      simpa using this
    simp [ha0]
  obtain ⟨hDJ, _⟩ := isZLattice_single_fractional K J hJ_ne
  have : DiscreteTopology (zRealizeMod (Basis.singleton Unit K) (fun _ => 1)
      (J : Submodule (𝓞 K) K)) := hDJ
  have hcoord_eq : ∀ x ∈ N, lineMap (x m) = x := by
    intro x hx
    obtain ⟨a, _, rfl⟩ := hN_le hx
    ext m'
    simp only [lineMap, LinearMap.coe_restrictScalars, LinearMap.toSpanSingleton_apply,
      Pi.smul_apply, smul_eq_mul]
    by_cases hm' : m' = m
    · subst hm'; simp
    · simp [hm']
  let L₁ := zRealizeMod (Basis.singleton Unit K) (fun _ => 1) (J : Submodule (𝓞 K) K)
  let L₂ := zRealizeMod (Pi.basisFun K MonI) (monX (K := K) w) N
  have hinj1 : Function.Injective (realizeHLat (Basis.singleton Unit K)
      (fun _ : InfinitePlace K => (1 : Matrix Unit Unit ℂ))) :=
    realizeHLat_injective _ _ (fun _ => by simp)
  have hinj2 : Function.Injective (realizeHLat (Pi.basisFun K MonI) (monX (K := K) w)) :=
    realizeHLat_injective _ _ (isUnit_det_monX w hw)
  have hL₁_ne : L₁ ≠ ⊥ := by
    intro h0
    apply hJ_ne
    apply FractionalIdeal.coeToSubmodule_injective
    change (J : Submodule (𝓞 K) K) = ((0 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
    rw [FractionalIdeal.coe_zero, eq_bot_iff]
    intro a ha
    have hmem : realizeHLat (Basis.singleton Unit K) (fun _ => 1) a ∈ L₁ := ⟨a, ha, rfl⟩
    rw [h0, Submodule.mem_bot] at hmem
    exact hinj1 (hmem.trans (map_zero _).symm)
  have hspec1 : ∀ u : L₁, realizeHLat (Basis.singleton Unit K) (fun _ => 1) u.2.choose = u.1 :=
    fun u => u.2.choose_spec.2
  have hspec2 : ∀ v : L₂, realizeHLat (Pi.basisFun K MonI) (monX (K := K) w) v.2.choose = v.1 :=
    fun v => v.2.choose_spec.2
  let e : L₁ ≃ₗ[ℤ] L₂ :=
    { toFun := fun u =>
        let a := u.2.choose
        ⟨realizeHLat (Pi.basisFun K MonI) (monX (K := K) w) (lineMap a),
          lineMap a, u.2.choose_spec.1, rfl⟩
      invFun := fun v =>
        let x := v.2.choose
        ⟨realizeHLat (Basis.singleton Unit K) (fun _ => 1) (x m),
          x m, by
            change lineMap (x m) ∈ N
            rw [hcoord_eq x v.2.choose_spec.1]
            exact v.2.choose_spec.1, rfl⟩
      map_add' := fun u₁ u₂ => by
        apply Subtype.ext
        let a₁ := u₁.2.choose
        let a₂ := u₂.2.choose
        let a₃ := (u₁ + u₂).2.choose
        have ha₃ : a₃ = a₁ + a₂ := hinj1 (by
          rw [hspec1 (u₁ + u₂), map_add]
          exact congrArg₂ (· + ·) (hspec1 u₁).symm (hspec1 u₂).symm)
        change realizeHLat _ _ (lineMap a₃) =
          realizeHLat _ _ (lineMap a₁) + realizeHLat _ _ (lineMap a₂)
        rw [ha₃, map_add, map_add]
      map_smul' := fun k u => by
        apply Subtype.ext
        let a := u.2.choose
        let ak := (k • u).2.choose
        have hak : ak = k • a := hinj1 (by
          rw [hspec1 (k • u), map_zsmul]
          exact congrArg (k • ·) (hspec1 u).symm)
        change realizeHLat _ _ (lineMap ak) = k • realizeHLat _ _ (lineMap a)
        rw [hak, map_zsmul, map_zsmul]
      left_inv := fun u => by
        apply Subtype.ext
        let a := u.2.choose
        let v₀ : L₂ := ⟨realizeHLat (Pi.basisFun K MonI) (monX (K := K) w) (lineMap a),
          ⟨lineMap a, u.2.choose_spec.1, rfl⟩⟩
        have hx_eq : v₀.2.choose = lineMap a := hinj2 (hspec2 v₀)
        have hxm : v₀.2.choose m = a := by
          rw [hx_eq]
          simp [lineMap]
        change realizeHLat (Basis.singleton Unit K) (fun _ => 1) (v₀.2.choose m) = u.1
        rw [hxm, hspec1 u]
      right_inv := fun v => by
        apply Subtype.ext
        let x := v.2.choose
        let u₀ : L₁ := ⟨realizeHLat (Basis.singleton Unit K) (fun _ => 1) (x m),
          ⟨x m, by change lineMap (x m) ∈ N; rw [hcoord_eq x v.2.choose_spec.1]; exact v.2.choose_spec.1,
            rfl⟩⟩
        have ha_eq : u₀.2.choose = x m := hinj1 (hspec1 u₀)
        change realizeHLat (Pi.basisFun K MonI) (monX (K := K) w) (lineMap u₀.2.choose) = v.1
        rw [ha_eq, hcoord_eq x v.2.choose_spec.1, hspec2 v] }
  have hc_pos : 0 < Real.sqrt (w m) := Real.sqrt_pos.mpr (hw m)
  have hnorm : ∀ u : L₁, ‖((e u : L₂) : EuclideanSpace ℝ (InfinitePlace K × MonI × Fin 2))‖ =
      Real.sqrt (w m) * ‖((u : L₁) : EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2))‖ := by
    intro u
    let a := u.2.choose
    have hu_eq : (u : EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2)) =
        realizeHLat (Basis.singleton Unit K) (fun _ => 1) a := (hspec1 u).symm
    have he_eq : ((e u : L₂) : EuclideanSpace ℝ (InfinitePlace K × MonI × Fin 2)) =
        realizeHLat (Pi.basisFun K MonI) (monX (K := K) w) (lineMap a) := rfl
    rw [← sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hc_pos.le (norm_nonneg _)),
      mul_pow, Real.sq_sqrt (hw m).le, he_eq, hu_eq, norm_sq_realizeHLat, norm_sq_realizeHLat,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hline : normAt (Pi.basisFun K MonI) (monX (K := K) w) v (lineMap a) ^ 2 =
        w m * ‖v.embedding a‖ ^ 2 := by
      rw [normAt_monX_sq w hw v (lineMap a), Finset.sum_eq_single m]
      · simp [lineMap]
      · intro m' _ hm'; simp [lineMap, hm']
      · intro hm'; exact absurd (Finset.mem_univ m) hm'
    have hsingle : normAt (Basis.singleton Unit K) (fun _ => 1) v a ^ 2 = ‖v.embedding a‖ ^ 2 := by
      simp [normAt, fcoord, vecAt]
    rw [hline, hsingle]
  have hslope := slope_eq_sub_log_of_homothety L₁ L₂ hL₁_ne e (Real.sqrt (w m)) hc_pos hnorm
  have hmu_eq : muOK (Pi.basisFun K MonI) (monX (K := K) w) N =
      muOK (Basis.singleton Unit K) (fun _ => 1) (J : Submodule (𝓞 K) K) - Real.log (w m) := by
    unfold muOK
    change 2 * ArakelovCovolume.slope L₂ - Real.log 2 + NumberFieldHLat.logDiscDivDeg K =
      2 * ArakelovCovolume.slope L₁ - Real.log 2 + NumberFieldHLat.logDiscDivDeg K - Real.log (w m)
    rw [hslope, Real.sqrt_eq_rpow, Real.log_rpow (hw m)]
    ring
  rw [hmu_eq, muOK_single_fractional_eq K J hJ_ne]
  have hnorm_mono := fractionalIdeal_absNorm_mono K I J hI hJ_ne hJ_N_le
  have hI_pos : 0 < (FractionalIdeal.absNorm I : ℝ) := by
    have hcovI_pos : 0 < covol (zRealizeMod (Basis.singleton Unit K) (fun _ => 1)
        (I : Submodule (𝓞 K) K)) := by
      obtain ⟨hDI, _⟩ := isZLattice_single_fractional K I hI
      have : DiscreteTopology (zRealizeMod (Basis.singleton Unit K) (fun _ => 1)
          (I : Submodule (𝓞 K) K)) := hDI
      exact ArakelovCovolume.covol_pos _
    obtain ⟨hD1, _⟩ := isZLattice_single_one K
    have : DiscreteTopology (zRealizeMod (Basis.singleton Unit K) (fun _ => 1)
        (1 : Submodule (𝓞 K) K)) := hD1
    rw [covol_single_fractional_eq K I hI] at hcovI_pos
    exact (mul_pos_iff_of_pos_right (ArakelovCovolume.covol_pos _)).mp hcovI_pos
  have hlog_I_le_J : Real.log (FractionalIdeal.absNorm I : ℝ) ≤
      Real.log (FractionalIdeal.absNorm J : ℝ) :=
    Real.log_le_log hI_pos hnorm_mono
  have hlog_c_le_w : Real.log c₀ ≤ Real.log (w m) := Real.log_le_log hc₀ hcw
  have hrank_pos : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hdiv_le : 2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ) ≤
      2 * Real.log (FractionalIdeal.absNorm J : ℝ) / (Module.finrank ℚ K : ℝ) := by
    gcongr
  linarith

private lemma fcoord_monX_apply (K MonI : Type)
    [Field K] [NumberField K] [Fintype MonI] [DecidableEq MonI]
    (w : MonI → ℝ) (hw : ∀ m, 0 < w m) (v : InfinitePlace K) (x : MonI → K) (m : MonI) :
    fcoord (Pi.basisFun K MonI) (monX (K := K) w) v x m =
      (Real.sqrt (w m) : ℂ) * v.embedding (x m) := by
  simp only [fcoord]
  have hinv : (monX (K := K) w v)⁻¹ =
      Matrix.diagonal fun m' : MonI => ((Real.sqrt (w m') : ℝ) : ℂ) := by
    refine inv_eq_right_inv ?_
    rw [monX, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij; simp [(Real.sqrt_pos.mpr (hw i)).ne']
    · simp [hij]
  rw [hinv, Matrix.mulVec_diagonal]
  simp [vecAt]

private def coordProj (K MonI : Type) [Field K] [NumberField K] [DecidableEq MonI]
    (m : MonI) : (MonI → K) →ₗ[𝓞 K] (MonI → K) where
  toFun x := Pi.single m (x m)
  map_add' x y := by
    ext m'
    simp only [Pi.add_apply, Pi.single_apply]
    split_ifs <;> simp
  map_smul' c x := by
    ext m'
    simp only [RingHom.id_apply, Pi.smul_apply, Pi.single_apply]
    split_ifs <;> simp

private def eCoordProj (K MonI : Type) [Field K] [NumberField K] [DecidableEq MonI]
    (m : MonI) : EuclideanSpace ℝ (InfinitePlace K × MonI × Fin 2) →ₗ[ℝ]
      EuclideanSpace ℝ (InfinitePlace K × MonI × Fin 2) where
  toFun u := WithLp.toLp 2 fun p => if p.2.1 = m then u p else 0
  map_add' u v := by
    ext p
    simp only [WithLp.ofLp_add, Pi.add_apply]
    split_ifs <;> simp
  map_smul' c u := by
    ext p
    simp only [RingHom.id_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp

private lemma eCoordProj_realizeHLat (K MonI : Type)
    [Field K] [NumberField K] [Fintype MonI] [DecidableEq MonI]
    (w : MonI → ℝ) (hw : ∀ m, 0 < w m) (m : MonI) (x : MonI → K) :
    eCoordProj K MonI m (realizeHLat (Pi.basisFun K MonI) (monX (K := K) w) x) =
      realizeHLat (Pi.basisFun K MonI) (monX (K := K) w) (coordProj K MonI m x) := by
  ext p
  rcases p with ⟨v, m', j⟩
  simp only [eCoordProj, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
  by_cases hm : m' = m
  · subst hm
    simp only [↓reduceIte, realizeHLat, AddMonoidHom.coe_mk, ZeroHom.coe_mk, WithLp.ofLp_toLp,
      fcoord_monX_apply K MonI w hw, coordProj, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_eq_same]
  · simp only [hm, ↓reduceIte, realizeHLat, AddMonoidHom.coe_mk, ZeroHom.coe_mk, WithLp.ofLp_toLp,
      fcoord_monX_apply K MonI w hw, coordProj, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.single_eq_of_ne hm, map_zero, mul_zero, Complex.zero_re, Complex.zero_im, ite_self]

private lemma norm_eCoordProj_le (K MonI : Type)
    [Field K] [NumberField K] [Fintype MonI] [DecidableEq MonI]
    (m : MonI) (u : EuclideanSpace ℝ (InfinitePlace K × MonI × Fin 2)) :
    ‖eCoordProj K MonI m u‖ ≤ ‖u‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  refine Finset.sum_le_sum fun p _ => ?_
  simp only [eCoordProj, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
  split_ifs
  · exact le_rfl
  · simp [sq_nonneg]

private lemma sum_eCoordProj (K MonI : Type)
    [Field K] [NumberField K] [Fintype MonI] [DecidableEq MonI]
    (u : EuclideanSpace ℝ (InfinitePlace K × MonI × Fin 2)) :
    ∑ m : MonI, eCoordProj K MonI m u = u := by
  ext p
  rcases p with ⟨v, m', j⟩
  rw [WithLp.ofLp_sum, Finset.sum_apply, Finset.sum_eq_single m']
  · simp [eCoordProj]
  · intro m _ hm; simp [eCoordProj, hm.symm]
  · intro hm'; exact absurd (Finset.mem_univ m') hm'

private lemma slope_le_of_contraction
    {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    (L₁ : Submodule ℤ E₁) (L₂ : Submodule ℤ E₂)
    [DiscreteTopology L₁] [DiscreteTopology L₂]
    (hL₁ : L₁ ≠ ⊥) (e : L₁ ≃ₗ[ℤ] L₂) (T : E₁ →ₗ[ℝ] E₂)
    (hT_eq : ∀ x : L₁, ((e x : L₂) : E₂) = T (x : E₁))
    (hT_norm : ∀ u : E₁, ‖T u‖ ≤ ‖u‖) :
    ArakelovCovolume.rk L₂ = ArakelovCovolume.rk L₁ ∧
      ArakelovCovolume.covol L₂ ≤ ArakelovCovolume.covol L₁ ∧
      ArakelovCovolume.degAr L₁ ≤ ArakelovCovolume.degAr L₂ ∧
      ArakelovCovolume.slope L₁ ≤ ArakelovCovolume.slope L₂ := by
  have hrk : ArakelovCovolume.rk L₂ = ArakelovCovolume.rk L₁ := by
    unfold ArakelovCovolume.rk
    exact LinearEquiv.finrank_eq e.symm
  let b₁ : Basis (Fin (ArakelovCovolume.rk L₁)) ℤ L₁ := Module.finBasis ℤ L₁
  let b₂ : Basis (Fin (ArakelovCovolume.rk L₁)) ℤ L₂ := b₁.map e
  have hcomp : ∀ c : Fin (ArakelovCovolume.rk L₁) → ℝ,
      ‖∑ i, c i • ((b₂ i : L₂) : E₂)‖ ≤ 1 * ‖∑ i, c i • ((b₁ i : L₁) : E₁)‖ := by
    intro c
    have hsum : ∑ i, c i • ((b₂ i : L₂) : E₂) = T (∑ i, c i • ((b₁ i : L₁) : E₁)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, ← hT_eq (b₁ i)]
      rfl
    rw [hsum, one_mul]
    exact hT_norm _
  have hdet := ArakelovCovolume.gram_det_le (fun i => ((b₁ i : L₁) : E₁))
    (fun i => ((b₂ i : L₂) : E₂)) 1 hcomp
  rw [one_pow, one_mul] at hdet
  have hcov : ArakelovCovolume.covol L₂ ≤ ArakelovCovolume.covol L₁ := by
    rw [ArakelovCovolume.covol_eq_sqrt_det_gram L₁ b₁,
      ArakelovCovolume.covol_eq_sqrt_det_gram L₂ b₂]
    exact Real.sqrt_le_sqrt hdet
  have hdeg : ArakelovCovolume.degAr L₁ ≤ ArakelovCovolume.degAr L₂ := by
    unfold ArakelovCovolume.degAr
    exact neg_le_neg (Real.log_le_log (ArakelovCovolume.covol_pos L₂) hcov)
  have hslope : ArakelovCovolume.slope L₁ ≤ ArakelovCovolume.slope L₂ := by
    unfold ArakelovCovolume.slope
    rw [hrk]
    have hrk_pos : (0 : ℝ) < (ArakelovCovolume.rk L₁ : ℝ) := by
      exact_mod_cast ArakelovCovolume.rk_pos_of_ne_bot L₁ hL₁
    exact div_le_div_of_nonneg_right hdeg hrk_pos.le
  exact ⟨hrk, hcov, hdeg, hslope⟩

private lemma discreteTopology_iSup_orthog (K MonI : Type)
    [Field K] [NumberField K] [IsTotallyComplex K] [Fintype MonI] [DecidableEq MonI]
    (w : MonI → ℝ) (hw : ∀ m, 0 < w m)
    (L : MonI → Submodule (𝓞 K) (MonI → K))
    (hL_line : ∀ m, L m ≤ (Submodule.span K {Pi.single m (1 : K)}).restrictScalars (𝓞 K))
    (hDiscL : ∀ m, DiscreteTopology (zRealizeMod (Pi.basisFun K MonI) (monX (K := K) w) (L m)))
    (s : Finset MonI) (R : Submodule (𝓞 K) (MonI → K)) (hR : R ≤ ⨆ m ∈ s, L m) :
    DiscreteTopology (zRealizeMod (Pi.basisFun K MonI) (monX (K := K) w) R) := by
  let S : Submodule (𝓞 K) (MonI → K) :=
    { carrier := { x | ∀ m : MonI, coordProj K MonI m x ∈ L m }
      add_mem' := fun hx hy m => by rw [map_add]; exact Submodule.add_mem _ (hx m) (hy m)
      zero_mem' := fun m => by rw [map_zero]; exact Submodule.zero_mem _
      smul_mem' := fun c _ hx m => by rw [map_smul]; exact Submodule.smul_mem _ c (hx m) }
  have hsup_le : (⨆ m ∈ s, L m) ≤ S := by
    refine iSup₂_le fun m₀ _ x hx m => ?_
    have hx_span : x ∈ Submodule.span K ({Pi.single m₀ (1 : K)} : Set (MonI → K)) := hL_line m₀ hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx_span
    by_cases hm : m = m₀
    · subst hm
      have heq : coordProj K MonI m (c • Pi.single m (1 : K)) = c • Pi.single m (1 : K) := by
        ext m'
        by_cases hm' : m' = m <;> simp [coordProj, hm']
      rw [heq]
      exact hx
    · have h0 : coordProj K MonI m (c • Pi.single m₀ (1 : K)) = 0 := by
        ext m'
        simp [coordProj, Pi.single_apply, hm]
      rw [h0]
      exact Submodule.zero_mem _
  let L_R := zRealizeMod (Pi.basisFun K MonI) (monX (K := K) w) R
  have he_mem : ∀ u : L_R, ∀ m : MonI,
      eCoordProj K MonI m u.1 ∈ zRealizeMod (Pi.basisFun K MonI) (monX (K := K) w) (L m) := by
    rintro ⟨u, x, hx, rfl⟩ m
    refine ⟨coordProj K MonI m x, hsup_le (hR hx) m, ?_⟩
    exact (eCoordProj_realizeHLat K MonI w hw m x).symm
  let f : L_R → ∀ m : MonI,
      zRealizeMod (Pi.basisFun K MonI) (monX (K := K) w) (L m) :=
    fun u m => ⟨eCoordProj K MonI m u.1, he_mem u m⟩
  refine DiscreteTopology.of_continuous_injective (f := f) ?_ ?_
  · refine continuous_pi fun m => Continuous.subtype_mk ?_ _
    exact ((eCoordProj K MonI m).continuous_of_finiteDimensional).comp continuous_subtype_val
  · intro u₁ u₂ h
    apply Subtype.ext
    rw [← sum_eCoordProj K MonI u₁.1, ← sum_eCoordProj K MonI u₂.1]
    refine Finset.sum_congr rfl fun m _ => ?_
    exact congrArg (fun g => (g m).1) h

/-- **Orthogonal `iSup` Slope Bound (`muMaxOK_orthog_iSup`)**:
If each `L m` lives on the `m`-th monomial line with `muOK ≤ θ` on all nonzero `𝓞_K`-submodules
of `L m`, then EVERY nonzero `𝓞_K`-submodule `R ≤ ⨆ m ∈ s, L m` satisfies `muOK ... R ≤ θ`. -/
theorem muMaxOK_orthog_iSup (K MonI : Type)
    [Field K] [NumberField K] [IsTotallyComplex K] [Fintype MonI] [DecidableEq MonI]
    (w : MonI → ℝ) (hw : ∀ m, 0 < w m)
    (L : MonI → Submodule (𝓞 K) (MonI → K))
    (hL_line : ∀ m, L m ≤ (Submodule.span K {Pi.single m (1 : K)}).restrictScalars (𝓞 K))
    (hDiscL : ∀ m, DiscreteTopology (zRealizeMod (Pi.basisFun K MonI) (monX (K := K) w) (L m)))
    (s : Finset MonI) (hs_ne : s.Nonempty) (θ : ℝ)
    (hbound : ∀ m ∈ s, ∀ N : Submodule (𝓞 K) (MonI → K), N ≤ L m → N ≠ ⊥ →
      muOK (Pi.basisFun K MonI) (monX (K := K) w) N ≤ θ)
    (R : Submodule (𝓞 K) (MonI → K)) (hR_le : R ≤ ⨆ m ∈ s, L m) (hR_ne : R ≠ ⊥) :
    muOK (Pi.basisFun K MonI) (monX (K := K) w) R ≤ θ := by
  let θ' : ℝ := (θ + Real.log 2 - NumberFieldHLat.logDiscDivDeg K) / 2
  have hmu_iff : ∀ M : Submodule (𝓞 K) (MonI → K),
      muOK (Pi.basisFun K MonI) (monX (K := K) w) M ≤ θ ↔
        ArakelovCovolume.slope (zRealizeMod (Pi.basisFun K MonI) (monX (K := K) w) M) ≤ θ' := by
    intro M
    unfold muOK
    dsimp only [θ']
    constructor <;> intro h <;> linarith
  induction s using Finset.induction_on generalizing R with
  | empty =>
    exact absurd hs_ne (by simp)
  | @insert m s' hm ih =>
    by_cases hs' : s' = ∅
    · subst hs'
      have hR_m : R ≤ L m := by
        intro x hx
        have hx' := hR_le hx
        simp only [Finset.mem_insert, Finset.notMem_empty, or_false, iSup_iSup_eq_left] at hx'
        exact hx'
      exact hbound m (Finset.mem_insert_self m ∅) R hR_m hR_ne
    · have hs'_ne : s'.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs'
      have hbound_s' : ∀ m' ∈ s', ∀ N : Submodule (𝓞 K) (MonI → K), N ≤ L m' → N ≠ ⊥ →
          muOK (Pi.basisFun K MonI) (monX (K := K) w) N ≤ θ :=
        fun m' hm' => hbound m' (Finset.mem_insert_of_mem hm')
      have hsup_eq : (⨆ i ∈ insert m s', L i) = L m ⊔ (⨆ i ∈ s', L i) := by
        rw [Finset.iSup_insert]
      let projM := coordProj K MonI m
      have hπ_s' : ∀ z ∈ ⨆ i ∈ s', L i, projM z = 0 := by
        intro z hz
        have hle : (⨆ i ∈ s', L i) ≤ LinearMap.ker projM := by
          refine iSup₂_le fun i hi y hy => ?_
          have hy_span : y ∈ Submodule.span K ({Pi.single i (1 : K)} : Set (MonI → K)) :=
            hL_line i hy
          obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy_span
          have him : i ≠ m := fun h => hm (h ▸ hi)
          ext m'
          simp [projM, coordProj, Pi.single_apply, him]
        exact hle hz
      have hπ_m : ∀ y ∈ L m, projM y = y := by
        intro y hy
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp (hL_line m hy)
        ext m'
        by_cases hm' : m' = m <;> simp [projM, coordProj, hm']
      let K_R : Submodule (𝓞 K) (MonI → K) := R ⊓ LinearMap.ker projM
      let Q_R : Submodule (𝓞 K) (MonI → K) := R.map projM
      have hQR_le : Q_R ≤ L m := by
        rintro _ ⟨x, hx, rfl⟩
        have hx' : x ∈ L m ⊔ (⨆ i ∈ s', L i) := hsup_eq ▸ hR_le hx
        obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx'
        rw [map_add, hπ_m y hy, hπ_s' z hz, add_zero]
        exact hy
      have hKR_le : K_R ≤ ⨆ i ∈ s', L i := by
        intro x ⟨hxR, hxK⟩
        have hx' : x ∈ L m ⊔ (⨆ i ∈ s', L i) := hsup_eq ▸ hR_le hxR
        obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx'
        have hπ0 : projM (y + z) = 0 := hxK
        rw [map_add, hπ_m y hy, hπ_s' z hz, add_zero] at hπ0
        rwa [hπ0, zero_add]
      by_cases hKR_bot : K_R = ⊥
      · have hQR_ne : Q_R ≠ ⊥ := by
          intro hQ0
          apply hR_ne
          rw [eq_bot_iff]
          intro x hx
          have hmem : projM x ∈ Q_R := ⟨x, hx, rfl⟩
          rw [hQ0, Submodule.mem_bot] at hmem
          have hxK : x ∈ K_R := ⟨hx, hmem⟩
          rwa [hKR_bot, Submodule.mem_bot] at hxK
        let L_R := zRealizeMod (Pi.basisFun K MonI) (monX (K := K) w) R
        let L_Q := zRealizeMod (Pi.basisFun K MonI) (monX (K := K) w) Q_R
        have : DiscreteTopology L_R :=
          discreteTopology_iSup_orthog K MonI w hw L hL_line hDiscL (insert m s') R hR_le
        have : DiscreteTopology L_Q :=
          ArakelovCovolume.discreteTopology_of_le (Submodule.map_mono (Submodule.restrictScalars_mono ℤ hQR_le))
        have hinj : Function.Injective (realizeHLat (Pi.basisFun K MonI) (monX (K := K) w)) :=
          realizeHLat_injective _ _ (isUnit_det_monX w hw)
        have hLR_ne : L_R ≠ ⊥ := by
          intro h0
          apply hR_ne
          rw [eq_bot_iff]
          intro x hx
          have hmem : realizeHLat (Pi.basisFun K MonI) (monX (K := K) w) x ∈ L_R := ⟨x, hx, rfl⟩
          rw [h0, Submodule.mem_bot] at hmem
          exact hinj (hmem.trans (map_zero _).symm)
        have hπ_inj : ∀ x₁ ∈ R, ∀ x₂ ∈ R, projM x₁ = projM x₂ → x₁ = x₂ := by
          intro x₁ hx₁ x₂ hx₂ hpi
          have hsub : x₁ - x₂ ∈ K_R :=
            ⟨Submodule.sub_mem R hx₁ hx₂, show projM (x₁ - x₂) = 0 by rw [map_sub, hpi, sub_self]⟩
          rw [hKR_bot, Submodule.mem_bot] at hsub
          exact sub_eq_zero.mp hsub
        have he_mem : ∀ u : L_R, eCoordProj K MonI m u.1 ∈ L_Q := by
          rintro ⟨u, x, hx, rfl⟩
          exact ⟨projM x, ⟨x, hx, rfl⟩, (eCoordProj_realizeHLat K MonI w hw m x).symm⟩
        have he_inv_mem : ∀ v : L_Q,
            realizeHLat (Pi.basisFun K MonI) (monX (K := K) w)
              (v.2.choose_spec.1.choose) ∈ L_R := by
          intro v
          exact ⟨v.2.choose_spec.1.choose, v.2.choose_spec.1.choose_spec.1, rfl⟩
        let e : L_R ≃ₗ[ℤ] L_Q :=
          { toFun := fun u => ⟨eCoordProj K MonI m u.1, he_mem u⟩
            invFun := fun v => ⟨realizeHLat (Pi.basisFun K MonI) (monX (K := K) w)
                v.2.choose_spec.1.choose, he_inv_mem v⟩
            map_add' := fun u₁ u₂ => Subtype.ext (map_add (eCoordProj K MonI m) u₁.1 u₂.1)
            map_smul' := fun k u => Subtype.ext (map_zsmul (eCoordProj K MonI m) k u.1)
            left_inv := fun u => by
              apply Subtype.ext
              rcases u with ⟨u, x, hx, rfl⟩
              let v : L_Q := ⟨eCoordProj K MonI m (realizeHLat _ _ x), he_mem ⟨_, x, hx, rfl⟩⟩
              let x' := v.2.choose_spec.1.choose
              have hx'_mem : x' ∈ R := v.2.choose_spec.1.choose_spec.1
              have hpi_x' : projM x' = v.2.choose := v.2.choose_spec.1.choose_spec.2
              have hv_eq : realizeHLat (Pi.basisFun K MonI) (monX (K := K) w) v.2.choose = v.1 :=
                v.2.choose_spec.2
              have hpi_eq : realizeHLat (Pi.basisFun K MonI) (monX (K := K) w) (projM x') =
                  realizeHLat (Pi.basisFun K MonI) (monX (K := K) w) (projM x) := by
                rw [hpi_x', hv_eq]
                exact eCoordProj_realizeHLat K MonI w hw m x
              have hx_eq : x' = x := hπ_inj x' hx'_mem x hx (hinj hpi_eq)
              change realizeHLat _ _ x' = realizeHLat _ _ x
              rw [hx_eq]
            right_inv := fun v => by
              apply Subtype.ext
              let x' := v.2.choose_spec.1.choose
              have hpi_x' : projM x' = v.2.choose := v.2.choose_spec.1.choose_spec.2
              change eCoordProj K MonI m (realizeHLat _ _ x') = v.1
              rw [eCoordProj_realizeHLat K MonI w hw m x', hpi_x']
              exact v.2.choose_spec.2 }
        have hslope := (slope_le_of_contraction L_R L_Q hLR_ne e (eCoordProj K MonI m)
          (fun _ => rfl) (norm_eCoordProj_le K MonI m)).2.2.2
        have hQ_bound := hbound m (Finset.mem_insert_self m s') Q_R hQR_le hQR_ne
        rw [hmu_iff] at hQ_bound ⊢
        exact hslope.trans hQ_bound
      · by_cases hQR_bot : Q_R = ⊥
        · have hR_sub : R ≤ ⨆ i ∈ s', L i := by
            intro x hx
            have hmem : projM x ∈ Q_R := ⟨x, hx, rfl⟩
            rw [hQR_bot, Submodule.mem_bot] at hmem
            exact hKR_le ⟨hx, hmem⟩
          exact ih hs'_ne hbound_s' R hR_sub hR_ne
        · let L_R := zRealizeMod (Pi.basisFun K MonI) (monX (K := K) w) R
          let M := zRealizeMod (Pi.basisFun K MonI) (monX (K := K) w) K_R
          let L_Q := zRealizeMod (Pi.basisFun K MonI) (monX (K := K) w) Q_R
          have : DiscreteTopology L_R :=
            discreteTopology_iSup_orthog K MonI w hw L hL_line hDiscL (insert m s') R hR_le
          have : DiscreteTopology M :=
            discreteTopology_iSup_orthog K MonI w hw L hL_line hDiscL s' K_R hKR_le
          have : DiscreteTopology L_Q :=
            ArakelovCovolume.discreteTopology_of_le
              (Submodule.map_mono (Submodule.restrictScalars_mono ℤ hQR_le))
          have hinj : Function.Injective (realizeHLat (Pi.basisFun K MonI) (monX (K := K) w)) :=
            realizeHLat_injective _ _ (isUnit_det_monX w hw)
          have hM_le : M ≤ L_R :=
            Submodule.map_mono (Submodule.restrictScalars_mono ℤ inf_le_left)
          have hM_ker : ∀ u ∈ Submodule.span ℝ (M : Set (EuclideanSpace ℝ (InfinitePlace K × MonI × Fin 2))),
              eCoordProj K MonI m u = 0 := by
            intro u hu
            have hle : Submodule.span ℝ (M : Set (EuclideanSpace ℝ (InfinitePlace K × MonI × Fin 2))) ≤
                LinearMap.ker (eCoordProj K MonI m) := by
              refine Submodule.span_le.mpr ?_
              rintro _ ⟨x, hxK, rfl⟩
              change eCoordProj K MonI m (realizeHLat _ _ x) = 0
              rw [eCoordProj_realizeHLat K MonI w hw m x]
              have h0 : projM x = 0 := hxK.2
              rw [h0, map_zero]
            exact hle hu
          have hSat : Stage4ArakelovBost.IsSaturated L_R M := by
            refine ⟨hM_le, fun u hu hu_span => ?_⟩
            rcases hu with ⟨x, hxR, rfl⟩
            have h0 := hM_ker _ hu_span
            change eCoordProj K MonI m (realizeHLat _ _ x) = 0 at h0
            rw [eCoordProj_realizeHLat K MonI w hw m x] at h0
            have hx0 : projM x = 0 := hinj (h0.trans (map_zero _).symm)
            exact ⟨x, ⟨hxR, hx0⟩, rfl⟩
          have hproj_eq : ∀ u ∈ L_R,
              eCoordProj K MonI m (Stage4ArakelovBost.projOrth M u) = eCoordProj K MonI m u := by
            intro u _
            have hsub := Stage4ArakelovBost.sub_projOrth_mem_span M u
            have h0 := hM_ker _ hsub
            rw [map_sub, sub_eq_zero] at h0
            exact h0.symm
          have hAdd := Stage4ArakelovBost.quotLat_exact_additivity hSat
          have : DiscreteTopology (Stage4ArakelovBost.quotLat L_R M) := hAdd.1
          have hM_ne : M ≠ ⊥ := by
            intro h0
            apply hKR_bot
            rw [eq_bot_iff]
            intro x hx
            have hmem : realizeHLat (Pi.basisFun K MonI) (monX (K := K) w) x ∈ M := ⟨x, hx, rfl⟩
            rw [h0, Submodule.mem_bot] at hmem
            exact hinj (hmem.trans (map_zero _).symm)
          have hLQ_ne : L_Q ≠ ⊥ := by
            intro h0
            apply hQR_bot
            rw [eq_bot_iff]
            intro y hy
            have hmem : realizeHLat (Pi.basisFun K MonI) (monX (K := K) w) y ∈ L_Q := ⟨y, hy, rfl⟩
            rw [h0, Submodule.mem_bot] at hmem
            exact hinj (hmem.trans (map_zero _).symm)
          have hQ_mem : ∀ q : Stage4ArakelovBost.quotLat L_R M,
              eCoordProj K MonI m q.1 ∈ L_Q := by
            intro q
            obtain ⟨u, hu, hqu⟩ := q.2
            rw [← hqu]
            change eCoordProj K MonI m (Stage4ArakelovBost.projOrth M u) ∈ L_Q
            rw [hproj_eq u hu]
            rcases hu with ⟨x, hx, rfl⟩
            exact ⟨projM x, ⟨x, hx, rfl⟩, (eCoordProj_realizeHLat K MonI w hw m x).symm⟩
          have hQ_inv_mem : ∀ v : L_Q,
              Stage4ArakelovBost.projOrth M (realizeHLat (Pi.basisFun K MonI) (monX (K := K) w)
                v.2.choose_spec.1.choose) ∈ Stage4ArakelovBost.quotLat L_R M := by
            intro v
            exact ⟨realizeHLat _ _ v.2.choose_spec.1.choose,
              ⟨v.2.choose_spec.1.choose, v.2.choose_spec.1.choose_spec.1, rfl⟩, rfl⟩
          let eqQ : Stage4ArakelovBost.quotLat L_R M ≃ₗ[ℤ] L_Q :=
            { toFun := fun q => ⟨eCoordProj K MonI m q.1, hQ_mem q⟩
              invFun := fun v => ⟨Stage4ArakelovBost.projOrth M
                (realizeHLat (Pi.basisFun K MonI) (monX (K := K) w) v.2.choose_spec.1.choose),
                hQ_inv_mem v⟩
              map_add' := fun q₁ q₂ => Subtype.ext (map_add (eCoordProj K MonI m) q₁.1 q₂.1)
              map_smul' := fun k q => Subtype.ext (map_zsmul (eCoordProj K MonI m) k q.1)
              left_inv := fun q => by
                apply Subtype.ext
                obtain ⟨u, hu, hqu⟩ := q.2
                change Stage4ArakelovBost.projOrth M (realizeHLat _ _ _) = q.1
                rw [← hqu]
                let v : L_Q := ⟨eCoordProj K MonI m q.1, hQ_mem q⟩
                let x' := v.2.choose_spec.1.choose
                have hx'R : x' ∈ R := v.2.choose_spec.1.choose_spec.1
                have hpi_x' : projM x' = v.2.choose := v.2.choose_spec.1.choose_spec.2
                have hv_eq : realizeHLat (Pi.basisFun K MonI) (monX (K := K) w) v.2.choose = v.1 :=
                  v.2.choose_spec.2
                rcases hu with ⟨x, hxR, rfl⟩
                have hdiff0 : eCoordProj K MonI m
                    (realizeHLat (Pi.basisFun K MonI) (monX (K := K) w) (x' - x)) = 0 := by
                  rw [map_sub, map_sub, eCoordProj_realizeHLat K MonI w hw m x', hpi_x', hv_eq]
                  change eCoordProj K MonI m q.1 -
                    eCoordProj K MonI m (realizeHLat (Pi.basisFun K MonI) (monX (K := K) w) x) = 0
                  rw [← hqu]
                  change eCoordProj K MonI m (Stage4ArakelovBost.projOrth M
                      ((realizeHLat (Pi.basisFun K MonI) (monX (K := K) w)).toIntLinearMap x)) -
                    eCoordProj K MonI m
                      ((realizeHLat (Pi.basisFun K MonI) (monX (K := K) w)).toIntLinearMap x) = 0
                  rw [hproj_eq _ ⟨x, hxR, rfl⟩, sub_self]
                rw [eCoordProj_realizeHLat K MonI w hw m (x' - x)] at hdiff0
                have hpi_diff : projM (x' - x) = 0 := hinj (hdiff0.trans (map_zero _).symm)
                have hsub_M : realizeHLat (Pi.basisFun K MonI) (monX (K := K) w) x' -
                    realizeHLat (Pi.basisFun K MonI) (monX (K := K) w) x ∈ M := by
                  rw [← map_sub]
                  exact ⟨x' - x, ⟨Submodule.sub_mem R hx'R hxR, hpi_diff⟩, rfl⟩
                have hzero := (Stage4ArakelovBost.projOrth_eq_zero_iff M _).mpr
                  (Submodule.subset_span hsub_M)
                rw [map_sub, sub_eq_zero] at hzero
                change Stage4ArakelovBost.projOrth M
                    (realizeHLat (Pi.basisFun K MonI) (monX (K := K) w) x') =
                  Stage4ArakelovBost.projOrth M
                    (realizeHLat (Pi.basisFun K MonI) (monX (K := K) w) x)
                exact hzero
              right_inv := fun v => by
                apply Subtype.ext
                let x' := v.2.choose_spec.1.choose
                have hx'R : x' ∈ R := v.2.choose_spec.1.choose_spec.1
                have hpi_x' : projM x' = v.2.choose := v.2.choose_spec.1.choose_spec.2
                change eCoordProj K MonI m (Stage4ArakelovBost.projOrth M
                  ((realizeHLat _ _).toIntLinearMap x')) = v.1
                rw [hproj_eq _ ⟨x', hx'R, rfl⟩]
                change eCoordProj K MonI m (realizeHLat _ _ x') = v.1
                rw [eCoordProj_realizeHLat K MonI w hw m x', hpi_x']
                exact v.2.choose_spec.2 }
          have hquot_ne : Stage4ArakelovBost.quotLat L_R M ≠ ⊥ := by
            intro h0
            apply hLQ_ne
            rw [eq_bot_iff]
            intro v hv
            have hq : eqQ.symm ⟨v, hv⟩ = 0 :=
              Subtype.ext ((Submodule.mem_bot ℤ).mp (h0 ▸ (eqQ.symm ⟨v, hv⟩).2))
            have hv0 := congrArg (fun x => (eqQ x).1) hq
            rw [eqQ.apply_symm_apply, map_zero] at hv0
            rw [Submodule.mem_bot]
            exact hv0
          obtain ⟨hrk_Q, _, hdeg_Q, _⟩ := slope_le_of_contraction (Stage4ArakelovBost.quotLat L_R M)
            L_Q hquot_ne eqQ (eCoordProj K MonI m) (fun _ => rfl) (norm_eCoordProj_le K MonI m)
          have hIH_K := ih hs'_ne hbound_s' K_R hKR_le hKR_bot
          have hQ_bound := hbound m (Finset.mem_insert_self m s') Q_R hQR_le hQR_bot
          rw [hmu_iff] at hIH_K hQ_bound ⊢
          have hrkM_pos : (0 : ℝ) < (ArakelovCovolume.rk M : ℝ) := by
            exact_mod_cast ArakelovCovolume.rk_pos_of_ne_bot M hM_ne
          have hrkQ_pos : (0 : ℝ) < (ArakelovCovolume.rk L_Q : ℝ) := by
            exact_mod_cast ArakelovCovolume.rk_pos_of_ne_bot L_Q hLQ_ne
          have hrkR_pos : (0 : ℝ) < (ArakelovCovolume.rk L_R : ℝ) := by
            have : (ArakelovCovolume.rk L_R : ℝ) = (ArakelovCovolume.rk M : ℝ) +
                (ArakelovCovolume.rk L_Q : ℝ) := by
              rw [hAdd.2.1, ← hrk_Q]; push_cast; ring
            linarith
          have hdegM : ArakelovCovolume.degAr M ≤ θ' * (ArakelovCovolume.rk M : ℝ) :=
            (div_le_iff₀ hrkM_pos).mp hIH_K
          have hdegQ : ArakelovCovolume.degAr L_Q ≤ θ' * (ArakelovCovolume.rk L_Q : ℝ) :=
            (div_le_iff₀ hrkQ_pos).mp hQ_bound
          have hdegR : ArakelovCovolume.degAr L_R ≤ θ' * (ArakelovCovolume.rk L_R : ℝ) := by
            calc ArakelovCovolume.degAr L_R
                = ArakelovCovolume.degAr M +
                    ArakelovCovolume.degAr (Stage4ArakelovBost.quotLat L_R M) := hAdd.2.2.2
              _ ≤ ArakelovCovolume.degAr M + ArakelovCovolume.degAr L_Q := by linarith
              _ ≤ θ' * (ArakelovCovolume.rk M : ℝ) + θ' * (ArakelovCovolume.rk L_Q : ℝ) := by linarith
              _ = θ' * (ArakelovCovolume.rk L_R : ℝ) := by
                rw [hAdd.2.1, ← hrk_Q]; push_cast; ring
          exact (div_le_iff₀ hrkR_pos).mpr hdegR

end LineBoundsAndOrthogonalISup

section PlaceRescalingAndMonomialMuMax

private lemma fcoord_smul_O {K V ι : Type*} [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (a : 𝓞 K) (x : V) :
    fcoord b X v (a • x) = v.embedding (a : K) • fcoord b X v x := by
  have hax : a • x = (a : K) • x := (IsScalarTower.algebraMap_smul K a x).symm
  rw [hax]
  unfold fcoord
  have hvec : vecAt b v ((a : K) • x) = v.embedding (a : K) • vecAt b v x := by
    ext i
    change v.embedding ((b.repr ((a : K) • x)) i) = v.embedding (a : K) * v.embedding ((b.repr x) i)
    rw [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [hvec, Matrix.mulVec_smul]

private lemma fcoord_placeScale {K V ι : Type*} [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (B : InfinitePlace K → ℝ) (hB : ∀ v, B v ≠ 0)
    (v : InfinitePlace K) (x : V) :
    fcoord b (fun w => (B w : ℂ) • X w) v x = (B v : ℂ)⁻¹ • fcoord b X v x := by
  unfold fcoord
  have hinv : ((B v : ℂ) • X v)⁻¹ = (B v : ℂ)⁻¹ • (X v)⁻¹ := by
    refine inv_eq_right_inv ?_
    rw [Algebra.smul_mul_assoc, Matrix.mul_smul, smul_smul,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (hB v)), one_smul,
      Matrix.mul_nonsing_inv _ (hX v)]
  rw [hinv, Matrix.smul_mulVec]

open Classical in
private def placeProj (K : Type*) {ι : Type*} [Field K] [NumberField K]
    (v₀ : InfinitePlace K) :
    EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) →ₗ[ℝ]
      EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) where
  toFun u := WithLp.toLp 2 fun p => if p.1 = v₀ then u p else 0
  map_add' u₁ u₂ := by
    ext p; simp only [WithLp.ofLp_add, Pi.add_apply]; split_ifs <;> simp
  map_smul' c u := by
    ext p; simp only [RingHom.id_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp

open Classical in
private def placeI (K : Type*) {ι : Type*} [Field K] [NumberField K]
    (v₀ : InfinitePlace K) :
    EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) →ₗ[ℝ]
      EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) where
  toFun u := WithLp.toLp 2 fun p =>
    if p.1 = v₀ then (if p.2.2 = 0 then -u (v₀, p.2.1, 1) else u (v₀, p.2.1, 0)) else 0
  map_add' u₁ u₂ := by
    ext p; simp only [WithLp.ofLp_add, Pi.add_apply]; split_ifs <;> ring
  map_smul' c u := by
    ext p; simp only [RingHom.id_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring

private def scalePlace (K : Type*) {ι : Type*} [Field K] [NumberField K]
    (B : InfinitePlace K → ℝ) :
    EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) →ₗ[ℝ]
      EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) where
  toFun u := WithLp.toLp 2 fun p => B p.1 * u p
  map_add' u₁ u₂ := by
    ext p; simp only [WithLp.ofLp_add, Pi.add_apply, mul_add]
  map_smul' c u := by
    ext p; simp only [RingHom.id_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]; ring

private def scalePlaceEquiv (K : Type*) {ι : Type*} [Field K] [NumberField K]
    (B : InfinitePlace K → ℝ) (hB : ∀ v, B v ≠ 0) :
    EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) ≃ₗ[ℝ]
      EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) where
  toFun := scalePlace K B
  invFun := scalePlace K (fun v => (B v)⁻¹)
  map_add' := map_add (scalePlace K B)
  map_smul' := map_smul (scalePlace K B)
  left_inv u := by ext p; simp only [scalePlace, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]; rw [← mul_assoc, inv_mul_cancel₀ (hB p.1), one_mul]
  right_inv u := by ext p; simp only [scalePlace, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]; rw [← mul_assoc, mul_inv_cancel₀ (hB p.1), one_mul]

private lemma scalePlace_realizeHLat {K V ι : Type*} [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (B : InfinitePlace K → ℝ) (hB : ∀ v, B v ≠ 0) (x : V) :
    scalePlace K (fun v => (B v)⁻¹) (realizeHLat b X x) =
      realizeHLat b (fun v => (B v : ℂ) • X v) x := by
  ext p
  rcases p with ⟨v, i, j⟩
  simp only [scalePlace, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp, realizeHLat,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, fcoord_placeScale b X hX B hB, Pi.smul_apply,
    smul_eq_mul, ← Complex.ofReal_inv, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  fin_cases j <;> rfl

private lemma sum_placeProj (K : Type*) {ι : Type*} [Field K] [NumberField K]
    [Fintype ι] [DecidableEq ι]
    (u : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) :
    ∑ v₀ : InfinitePlace K, placeProj K v₀ u = u := by
  ext p
  rcases p with ⟨v, i, j⟩
  rw [WithLp.ofLp_sum, Finset.sum_apply, Finset.sum_eq_single v]
  · simp [placeProj]
  · intro v₀ _ hv₀; simp [placeProj, hv₀.symm]
  · intro hv; exact absurd (Finset.mem_univ v) hv

private lemma scalePlace_eq_sum_placeProj (K : Type*) {ι : Type*} [Field K] [NumberField K]
    [Fintype ι] [DecidableEq ι]
    (B : InfinitePlace K → ℝ) (u : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) :
    scalePlace K B u = ∑ v₀ : InfinitePlace K, B v₀ • placeProj K v₀ u := by
  ext p
  rcases p with ⟨v, i, j⟩
  rw [WithLp.ofLp_sum, Finset.sum_apply, Finset.sum_eq_single v]
  · simp [scalePlace, placeProj]
  · intro v₀ _ hv₀; simp [placeProj, hv₀.symm]
  · intro hv; exact absurd (Finset.mem_univ v) hv

open Classical in
private lemma placeProj_and_placeI_mem_span {K : Type} {V ι : Type*} [Field K] [NumberField K]
    [IsTotallyComplex K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (M' : Submodule (𝓞 K) V) (v₀ : InfinitePlace K) :
    let W : Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) :=
      Submodule.span ℝ ((zRealizeMod b X M' : Submodule ℤ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) :
        Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)))
    (∀ u ∈ W, placeProj K v₀ u ∈ W) ∧ (∀ u ∈ W, placeI K v₀ u ∈ W) := by
  intro W
  let L₁ := zRealizeMod (Basis.singleton Unit K) (fun _ => 1) (1 : Submodule (𝓞 K) K)
  obtain ⟨_, hsp₁⟩ := isZLattice_single_one K
  have hsingle_coeff : ∀ j₀ : Fin 2, ∃ (s : Finset (𝓞 K)) (c : 𝓞 K → ℝ),
      (∀ v : InfinitePlace K,
        ∑ a ∈ s, c a * (v.embedding (a : K)).re = if v = v₀ ∧ j₀ = 0 then 1 else 0) ∧
      (∀ v : InfinitePlace K,
        ∑ a ∈ s, c a * (v.embedding (a : K)).im = if v = v₀ ∧ j₀ = 1 then 1 else 0) := by
    intro j₀
    let e₀ : EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2) :=
      WithLp.toLp 2 fun p => if p = (v₀, (), j₀) then 1 else 0
    have he₀ : e₀ ∈ Submodule.span ℝ (L₁ : Set (EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2))) := by
      rw [hsp₁]; exact Submodule.mem_top
    obtain ⟨f, hf_supp, hf_sum⟩ := Submodule.mem_span_set.mp he₀
    have ha_ex : ∀ y : EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2),
        y ∈ f.support → ∃ a : 𝓞 K, realizeHLat (Basis.singleton Unit K) (fun _ => 1) (a : K) = y := by
      intro y hy
      have hyL : y ∈ L₁ := hf_supp hy
      rcases hyL with ⟨x, hx, rfl⟩
      obtain ⟨a, ha⟩ := (Submodule.mem_one (R := 𝓞 K) (A := K)).mp hx
      have ha' : (a : K) = x := ha
      refine ⟨a, ?_⟩
      change realizeHLat (Basis.singleton Unit K) (fun _ => 1) (a : K) =
        realizeHLat (Basis.singleton Unit K) (fun _ => 1) x
      rw [ha']
    let aMap : EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2) → 𝓞 K :=
      fun y => if hy : y ∈ f.support then (ha_ex y hy).choose else 0
    let s : Finset (𝓞 K) := f.support.image aMap
    let c : 𝓞 K → ℝ := fun a => ∑ y ∈ f.support.filter (fun y => aMap y = a), f y
    refine ⟨s, c, ?_, ?_⟩
    · intro v
      have hev := congrArg (fun z : EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2) =>
        z (v, (), 0)) hf_sum
      rw [Finsupp.sum, WithLp.ofLp_sum, Finset.sum_apply] at hev
      have hlhs : ∑ a ∈ s, c a * (v.embedding (a : K)).re =
          ∑ y ∈ f.support, f y * (v.embedding (aMap y : K)).re := by
        simp only [c, Finset.sum_mul]
        rw [← Finset.sum_fiberwise_of_maps_to (fun y hy => Finset.mem_image_of_mem aMap hy)]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun y hy => ?_
        rw [(Finset.mem_filter.mp hy).2]
      rw [hlhs]
      have hterm : ∀ y ∈ f.support, f y * (v.embedding (aMap y : K)).re =
          (f y • y) (v, (), 0) := by
        intro y hy
        have hspec : realizeHLat (Basis.singleton Unit K) (fun _ => 1) (aMap y : K) = y := by
          dsimp only [aMap]; rw [dif_pos hy]; exact (ha_ex y hy).choose_spec
        rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
        congr 1
        conv_rhs => rw [← hspec]
        simp [realizeHLat, fcoord, vecAt]
      rw [Finset.sum_congr rfl hterm, hev]
      simp only [e₀]
      by_cases hv : v = v₀ <;> fin_cases j₀ <;> simp [hv]
    · intro v
      have hev := congrArg (fun z : EuclideanSpace ℝ (InfinitePlace K × Unit × Fin 2) =>
        z (v, (), 1)) hf_sum
      rw [Finsupp.sum, WithLp.ofLp_sum, Finset.sum_apply] at hev
      have hlhs : ∑ a ∈ s, c a * (v.embedding (a : K)).im =
          ∑ y ∈ f.support, f y * (v.embedding (aMap y : K)).im := by
        simp only [c, Finset.sum_mul]
        rw [← Finset.sum_fiberwise_of_maps_to (fun y hy => Finset.mem_image_of_mem aMap hy)]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun y hy => ?_
        rw [(Finset.mem_filter.mp hy).2]
      rw [hlhs]
      have hterm : ∀ y ∈ f.support, f y * (v.embedding (aMap y : K)).im =
          (f y • y) (v, (), 1) := by
        intro y hy
        have hspec : realizeHLat (Basis.singleton Unit K) (fun _ => 1) (aMap y : K) = y := by
          dsimp only [aMap]; rw [dif_pos hy]; exact (ha_ex y hy).choose_spec
        rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
        congr 1
        conv_rhs => rw [← hspec]
        simp [realizeHLat, fcoord, vecAt]
      rw [Finset.sum_congr rfl hterm, hev]
      simp only [e₀]
      by_cases hv : v = v₀ <;> fin_cases j₀ <;> simp [hv]
  have hProj_lat : ∀ x ∈ M', placeProj K v₀ (realizeHLat b X x) ∈ W := by
    intro x hx
    obtain ⟨s, c, hre, him⟩ := hsingle_coeff 0
    have heq : placeProj K v₀ (realizeHLat b X x) =
        ∑ a ∈ s, c a • realizeHLat b X (a • x) := by
      ext p; rcases p with ⟨v, i, j⟩
      rw [WithLp.ofLp_sum, Finset.sum_apply]
      have hre_v := hre v
      have him_v := him v
      have hsplit0 : (∑ a ∈ s, (c a • realizeHLat b X (a • x)) (v, i, 0)) =
          (∑ a ∈ s, c a * (v.embedding (a : K)).re) * (fcoord b X v x i).re -
            (∑ a ∈ s, c a * (v.embedding (a : K)).im) * (fcoord b X v x i).im := by
        simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, realizeHLat,
          AddMonoidHom.coe_mk, ZeroHom.coe_mk, ↓reduceIte, fcoord_smul_O, Complex.mul_re]
        simp_rw [mul_sub, ← mul_assoc]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
      have hsplit1 : (∑ a ∈ s, (c a • realizeHLat b X (a • x)) (v, i, 1)) =
          (∑ a ∈ s, c a * (v.embedding (a : K)).re) * (fcoord b X v x i).im +
            (∑ a ∈ s, c a * (v.embedding (a : K)).im) * (fcoord b X v x i).re := by
        simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, realizeHLat,
          AddMonoidHom.coe_mk, ZeroHom.coe_mk, Fin.isValue, Fin.one_eq_zero_iff,
          Nat.reduceEqDiff, ↓reduceIte, fcoord_smul_O, Complex.mul_im]
        simp_rw [mul_add, ← mul_assoc]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
      fin_cases j
      · change (placeProj K v₀ (realizeHLat b X x)).ofLp (v, i, 0) =
            ∑ a ∈ s, (c a • realizeHLat b X (a • x)).ofLp (v, i, 0)
        rw [hsplit0, hre_v, him_v]
        by_cases hv : v = v₀
        · subst hv; simp [placeProj, realizeHLat]
        · simp [placeProj, hv]
      · change (placeProj K v₀ (realizeHLat b X x)).ofLp (v, i, 1) =
            ∑ a ∈ s, (c a • realizeHLat b X (a • x)).ofLp (v, i, 1)
        rw [hsplit1, hre_v, him_v]
        by_cases hv : v = v₀
        · subst hv; simp [placeProj, realizeHLat]
        · simp [placeProj, hv]
    rw [heq]
    exact Submodule.sum_mem W fun a _ =>
      Submodule.smul_mem W (c a) (Submodule.subset_span ⟨a • x, M'.smul_mem a hx, rfl⟩)
  have hI_lat : ∀ x ∈ M', placeI K v₀ (realizeHLat b X x) ∈ W := by
    intro x hx
    obtain ⟨s, c, hre, him⟩ := hsingle_coeff 1
    have heq : placeI K v₀ (realizeHLat b X x) =
        ∑ a ∈ s, c a • realizeHLat b X (a • x) := by
      ext p; rcases p with ⟨v, i, j⟩
      rw [WithLp.ofLp_sum, Finset.sum_apply]
      have hre_v := hre v
      have him_v := him v
      have hsplit0 : (∑ a ∈ s, (c a • realizeHLat b X (a • x)) (v, i, 0)) =
          (∑ a ∈ s, c a * (v.embedding (a : K)).re) * (fcoord b X v x i).re -
            (∑ a ∈ s, c a * (v.embedding (a : K)).im) * (fcoord b X v x i).im := by
        simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, realizeHLat,
          AddMonoidHom.coe_mk, ZeroHom.coe_mk, ↓reduceIte, fcoord_smul_O, Complex.mul_re]
        simp_rw [mul_sub, ← mul_assoc]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
      have hsplit1 : (∑ a ∈ s, (c a • realizeHLat b X (a • x)) (v, i, 1)) =
          (∑ a ∈ s, c a * (v.embedding (a : K)).re) * (fcoord b X v x i).im +
            (∑ a ∈ s, c a * (v.embedding (a : K)).im) * (fcoord b X v x i).re := by
        simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, realizeHLat,
          AddMonoidHom.coe_mk, ZeroHom.coe_mk, Fin.isValue, Fin.one_eq_zero_iff,
          Nat.reduceEqDiff, ↓reduceIte, fcoord_smul_O, Complex.mul_im]
        simp_rw [mul_add, ← mul_assoc]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
      fin_cases j
      · change (placeI K v₀ (realizeHLat b X x)).ofLp (v, i, 0) =
            ∑ a ∈ s, (c a • realizeHLat b X (a • x)).ofLp (v, i, 0)
        rw [hsplit0, hre_v, him_v]
        by_cases hv : v = v₀
        · subst hv; simp [placeI, realizeHLat]
        · simp [placeI, hv]
      · change (placeI K v₀ (realizeHLat b X x)).ofLp (v, i, 1) =
            ∑ a ∈ s, (c a • realizeHLat b X (a • x)).ofLp (v, i, 1)
        rw [hsplit1, hre_v, him_v]
        by_cases hv : v = v₀
        · subst hv; simp [placeI, realizeHLat]
        · simp [placeI, hv]
    rw [heq]
    exact Submodule.sum_mem W fun a _ =>
      Submodule.smul_mem W (c a) (Submodule.subset_span ⟨a • x, M'.smul_mem a hx, rfl⟩)
  constructor
  · have hle : W ≤ W.comap (placeProj K v₀) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨x, hx, rfl⟩
      exact hProj_lat x hx
    exact fun u hu => hle hu
  · have hle : W ≤ W.comap (placeI K v₀) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨x, hx, rfl⟩
      exact hI_lat x hx
    exact fun u hu => hle hu

private lemma exists_K_basis_in_submodule {K V : Type*} [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [FiniteDimensional K V] (M' : Submodule (𝓞 K) V) :
    let U := Submodule.span K (M' : Set V)
    ∃ u : Fin (Module.finrank K U) → V,
      (∀ j, u j ∈ M') ∧ LinearIndependent K u ∧ Submodule.span K (Set.range u) = U := by
  intro U
  let s := Module.finrank K U
  let bu : Basis (Fin s) K U := Module.finBasis K U
  have hclear1 : ∀ x ∈ U, ∃ d : 𝓞 K, d ≠ 0 ∧ (d : K) • x ∈ M' := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
    | zero => exact ⟨1, one_ne_zero, by simp⟩
    | add x₁ x₂ _ _ hx₁ hx₂ =>
      obtain ⟨d₁, hd₁, hm₁⟩ := hx₁
      obtain ⟨d₂, hd₂, hm₂⟩ := hx₂
      refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
      have h1 : ((d₁ * d₂ : 𝓞 K) : K) • (x₁ + x₂) =
          d₂ • ((d₁ : K) • x₁) + d₁ • ((d₂ : K) • x₂) := by
        push_cast
        rw [smul_add, ← IsScalarTower.algebraMap_smul K d₂ ((d₁ : K) • x₁),
          ← IsScalarTower.algebraMap_smul K d₁ ((d₂ : K) • x₂), smul_smul, smul_smul,
          mul_comm (d₁ : K) (d₂ : K)]
      rw [h1]
      exact M'.add_mem (M'.smul_mem d₂ hm₁) (M'.smul_mem d₁ hm₂)
    | smul k x _ hx =>
      obtain ⟨d, hd, hm⟩ := hx
      obtain ⟨n, dk, hdk0, hnk⟩ := IsFractionRing.div_surjective (A := 𝓞 K) k
      have hdk_ne : (dk : 𝓞 K) ≠ 0 := nonZeroDivisors.ne_zero hdk0
      refine ⟨(dk : 𝓞 K) * d, mul_ne_zero hdk_ne hd, ?_⟩
      have h1 : (((dk : 𝓞 K) * d : 𝓞 K) : K) • (k • x) = n • ((d : K) • x) := by
        have hdkK : (algebraMap (𝓞 K) K dk) ≠ 0 :=
          (map_ne_zero_iff (algebraMap (𝓞 K) K) (IsFractionRing.injective (𝓞 K) K)).mpr hdk_ne
        have hmul : (algebraMap (𝓞 K) K dk * algebraMap (𝓞 K) K d) *
            (algebraMap (𝓞 K) K n / algebraMap (𝓞 K) K dk) =
            algebraMap (𝓞 K) K n * algebraMap (𝓞 K) K d := by
          field_simp [hdkK]
        change (algebraMap (𝓞 K) K (dk * d)) • (k • x) = n • ((d : K) • x)
        rw [map_mul, ← hnk, smul_smul, hmul, ← smul_smul, IsScalarTower.algebraMap_smul K n]
      rw [h1]
      exact M'.smul_mem n hm
  let dFun : Fin s → 𝓞 K := fun j => (hclear1 (bu j : V) (bu j).2).choose
  let d : 𝓞 K := ∏ j : Fin s, dFun j
  have hd_ne : d ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ =>
    (hclear1 (bu j : V) (bu j).2).choose_spec.1
  have hdK_ne : (d : K) ≠ 0 :=
    (map_ne_zero_iff (algebraMap (𝓞 K) K) (IsFractionRing.injective (𝓞 K) K)).mpr hd_ne
  refine ⟨fun j => (d : K) • (bu j : V), ?_, ?_, ?_⟩
  · intro j
    let d' : 𝓞 K := ∏ i ∈ Finset.univ.erase j, dFun i
    have hd_eq : d = d' * dFun j := by
      dsimp only [d]
      rw [← Finset.mul_prod_erase Finset.univ dFun (Finset.mem_univ j), mul_comm]
    have hmem : (d : K) • (bu j : V) = d' • ((dFun j : K) • (bu j : V)) := by
      rw [hd_eq]
      push_cast
      rw [← smul_smul, ← IsScalarTower.algebraMap_smul K d' ((dFun j : K) • (bu j : V))]
    change (d : K) • (bu j : V) ∈ M'
    rw [hmem]
    exact M'.smul_mem d' (hclear1 (bu j : V) (bu j).2).choose_spec.2
  · have hli_coe : LinearIndependent K (fun j => (bu j : V)) :=
      bu.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hc' : ∑ k : Fin s, (c k * (d : K)) • (bu k : V) = 0 := by
      simpa only [smul_smul] using hc
    have h0 := Fintype.linearIndependent_iff.mp hli_coe (fun k => c k * (d : K)) hc' j
    exact (mul_eq_zero.mp h0).resolve_right hdK_ne
  · apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨j, rfl⟩
      exact U.smul_mem (d : K) (bu j).2
    · intro x hx
      let c : Fin s → K := fun j => bu.repr ⟨x, hx⟩ j
      have hc : ∑ j, c j • (bu j : V) = x := by
        have hsub := congrArg Subtype.val (bu.sum_repr ⟨x, hx⟩)
        simpa only [Submodule.coe_sum, Submodule.coe_smul, c] using hsub
      have hx_eq : x = ∑ j, (c j * (d : K)⁻¹) • ((d : K) • (bu j : V)) := by
        rw [← hc]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_smul, mul_assoc, inv_mul_cancel₀ hdK_ne, mul_one]
      rw [hx_eq]
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- **Uniform Place-Rescaling Formula (`covol_placeScale_submodule`)**:
Rescaling `X v ↦ (B v : ℂ) • X v` (`B v > 0`) on any nonzero `𝓞_K`-submodule `M'`
shifts `muOK b X M'` by `+(2 / |Pl_∞(K)|) * ∑ v, log (B v)`. -/
theorem covol_placeScale_submodule {K V ι : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    (M' : Submodule (𝓞 K) V) (hM' : M' ≠ ⊥)
    [DiscreteTopology (zRealizeMod b X M')]
    (B : InfinitePlace K → ℝ) (hB : ∀ v, 0 < B v) :
    DiscreteTopology (zRealizeMod b (fun v => (B v : ℂ) • X v) M') ∧
      muOK b (fun v => (B v : ℂ) • X v) M' =
        muOK b X M' + (2 / (Fintype.card (InfinitePlace K) : ℝ)) * ∑ v : InfinitePlace K, Real.log (B v) := by
  classical
  let E := EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)
  let Λ := zRealizeMod b X M'
  let Λ_B := zRealizeMod b (fun v => (B v : ℂ) • X v) M'
  let S_inv := scalePlaceEquiv K (ι := ι) (fun v => (B v)⁻¹) (fun v => inv_ne_zero (hB v).ne')
  have hS_eq : ∀ y : E, y ∈ Λ_B ↔ ∃ x ∈ Λ, scalePlace K (fun v => (B v)⁻¹) x = y := by
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨realizeHLat b X x, ⟨x, hx, rfl⟩, scalePlace_realizeHLat b X hX B (fun v => (hB v).ne') x⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (scalePlace_realizeHLat b X hX B (fun v => (hB v).ne') x).symm⟩
  let eqZ_B : Λ ≃ₗ[ℤ] Λ_B :=
    { toFun := fun u => ⟨scalePlace K (fun v => (B v)⁻¹) u.1, (hS_eq _).mpr ⟨u.1, u.2, rfl⟩⟩
      invFun := fun v => ⟨scalePlace K B v.1, by
        obtain ⟨x, hx, hxy⟩ := (hS_eq v.1).mp v.2
        have hcomp : scalePlace K B (scalePlace K (fun v => (B v)⁻¹) x) = x := by
          ext p; simp only [scalePlace, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
          rw [← mul_assoc, mul_inv_cancel₀ (hB p.1).ne', one_mul]
        rwa [← hxy, hcomp]⟩
      map_add' := fun u₁ u₂ => Subtype.ext (map_add (scalePlace K (fun v => (B v)⁻¹)) u₁.1 u₂.1)
      map_smul' := fun k u => Subtype.ext (map_zsmul (scalePlace K (fun v => (B v)⁻¹)) k u.1)
      left_inv := fun u => Subtype.ext (by
        ext p; simp only [scalePlace, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
        rw [← mul_assoc, mul_inv_cancel₀ (hB p.1).ne', one_mul])
      right_inv := fun v => Subtype.ext (by
        ext p; simp only [scalePlace, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
        rw [← mul_assoc, inv_mul_cancel₀ (hB p.1).ne', one_mul]) }
  have hDisc_B : DiscreteTopology Λ_B := by
    refine DiscreteTopology.of_continuous_injective (f := eqZ_B.symm) ?_ eqZ_B.symm.injective
    exact Continuous.subtype_mk
      (((scalePlace K B).continuous_of_finiteDimensional).comp continuous_subtype_val) _
  refine ⟨hDisc_B, ?_⟩
  have hΛ_ne : Λ ≠ ⊥ := by
    intro h0
    apply hM'
    rw [eq_bot_iff]
    intro x hx
    have hmem : realizeHLat b X x ∈ Λ := ⟨x, hx, rfl⟩
    rw [h0, Submodule.mem_bot] at hmem
    exact realizeHLat_injective b X hX (hmem.trans (map_zero _).symm)
  let W := Submodule.span ℝ (Λ : Set E)
  have hW_proj : ∀ v₀ u, u ∈ W → placeProj K v₀ u ∈ W :=
    fun v₀ => (placeProj_and_placeI_mem_span b X M' v₀).1
  have hW_I : ∀ v₀ u, u ∈ W → placeI K v₀ u ∈ W :=
    fun v₀ => (placeProj_and_placeI_mem_span b X M' v₀).2
  have hW_scale : ∀ u ∈ W, scalePlace K (fun v => (B v)⁻¹) u ∈ W := by
    intro u hu
    rw [scalePlace_eq_sum_placeProj]
    exact Submodule.sum_mem W fun v₀ _ => Submodule.smul_mem W _ (hW_proj v₀ u hu)
  have hW_scale_inv : ∀ u ∈ W, scalePlace K B u ∈ W := by
    intro u hu
    rw [scalePlace_eq_sum_placeProj]
    exact Submodule.sum_mem W fun v₀ _ => Submodule.smul_mem W _ (hW_proj v₀ u hu)
  let scaleW : W ≃ₗ[ℝ] W :=
    { toFun := fun u => ⟨scalePlace K (fun v => (B v)⁻¹) u.1, hW_scale u.1 u.2⟩
      invFun := fun u => ⟨scalePlace K B u.1, hW_scale_inv u.1 u.2⟩
      map_add' := fun u₁ u₂ => Subtype.ext (map_add (scalePlace K (fun v => (B v)⁻¹)) u₁.1 u₂.1)
      map_smul' := fun c u => Subtype.ext (map_smul (scalePlace K (fun v => (B v)⁻¹)) c u.1)
      left_inv := fun u => Subtype.ext (by
        ext p; simp only [scalePlace, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
        rw [← mul_assoc, mul_inv_cancel₀ (hB p.1).ne', one_mul])
      right_inv := fun u => Subtype.ext (by
        ext p; simp only [scalePlace, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
        rw [← mul_assoc, inv_mul_cancel₀ (hB p.1).ne', one_mul]) }
  have : FiniteDimensional K V := Module.Finite.of_basis b
  let U := Submodule.span K (M' : Set V)
  let s := Module.finrank K U
  obtain ⟨u, huM', huli, husp⟩ := exists_K_basis_in_submodule M'
  let vecW : (Σ v₀ : InfinitePlace K, Fin s ⊕ Fin s) → W := fun ⟨v₀, k⟩ =>
    match k with
    | Sum.inl j => ⟨placeProj K v₀ (realizeHLat b X (u j)),
        hW_proj v₀ _ (Submodule.subset_span ⟨u j, huM' j, rfl⟩)⟩
    | Sum.inr j => ⟨placeI K v₀ (realizeHLat b X (u j)),
        hW_I v₀ _ (Submodule.subset_span ⟨u j, huM' j, rfl⟩)⟩
  have hvecW_place : ∀ (v₀ v₁ : InfinitePlace K) (k : Fin s ⊕ Fin s),
      placeProj K v₁ (vecW ⟨v₀, k⟩ : E) = if v₁ = v₀ then (vecW ⟨v₀, k⟩ : E) else 0 := by
    intro v₀ v₁ k
    ext p
    rcases p with ⟨v, i, j⟩
    cases k with
    | inl m =>
      simp only [vecW, placeProj, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
      split_ifs <;> simp_all
    | inr m =>
      simp only [vecW, placeProj, placeI, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp]
      split_ifs <;> simp_all
  have hvecW_li : LinearIndependent ℝ vecW := by
    rw [Fintype.linearIndependent_iff]
    intro c hc ⟨v₀, k₀⟩
    have hproj_sum : ∀ v₀' : InfinitePlace K,
        ∑ k : Fin s ⊕ Fin s, c ⟨v₀', k⟩ • (vecW ⟨v₀', k⟩ : E) = 0 := by
      intro v₀'
      have hcE := congrArg (fun z : W => placeProj K v₀' z.1) hc
      rw [Submodule.coe_sum, Submodule.coe_zero, map_sum, map_zero] at hcE
      simp_rw [Submodule.coe_smul, map_smul, Fintype.sum_sigma] at hcE
      rw [Finset.sum_eq_single v₀'] at hcE
      · refine (Finset.sum_congr rfl fun k _ => ?_).symm.trans hcE
        rw [hvecW_place v₀' v₀' k, if_pos rfl]
      · intro v₁ _ hv₁
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [hvecW_place v₁ v₀' k, if_neg hv₁.symm, smul_zero]
      · intro hv₀'; exact absurd (Finset.mem_univ v₀') hv₀'
    have hc0 := hproj_sum v₀
    let γ : Fin s → ℂ := fun j =>
      ⟨c ⟨v₀, Sum.inl j⟩, c ⟨v₀, Sum.inr j⟩⟩
    have hsumC : ∑ j : Fin s, γ j • vecAt b v₀ (u j) = 0 := by
      have hf0 : ∑ j : Fin s, γ j • fcoord b X v₀ (u j) = 0 := by
        ext i
        have hc_re := congrArg (fun z : E => z (v₀, i, 0)) hc0
        have hc_im := congrArg (fun z : E => z (v₀, i, 1)) hc0
        rw [WithLp.ofLp_sum, Finset.sum_apply, Fintype.sum_sum_type] at hc_re hc_im
        have hre_l : ∀ j, (c ⟨v₀, Sum.inl j⟩ • (vecW ⟨v₀, Sum.inl j⟩ : E)) (v₀, i, 0) =
            c ⟨v₀, Sum.inl j⟩ * (fcoord b X v₀ (u j) i).re := fun j => by
          rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
          simp [vecW, placeProj, realizeHLat]
        have hre_r : ∀ j, (c ⟨v₀, Sum.inr j⟩ • (vecW ⟨v₀, Sum.inr j⟩ : E)) (v₀, i, 0) =
            -(c ⟨v₀, Sum.inr j⟩ * (fcoord b X v₀ (u j) i).im) := fun j => by
          rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
          simp [vecW, placeI, realizeHLat]
        have him_l : ∀ j, (c ⟨v₀, Sum.inl j⟩ • (vecW ⟨v₀, Sum.inl j⟩ : E)) (v₀, i, 1) =
            c ⟨v₀, Sum.inl j⟩ * (fcoord b X v₀ (u j) i).im := fun j => by
          rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
          simp [vecW, placeProj, realizeHLat]
        have him_r : ∀ j, (c ⟨v₀, Sum.inr j⟩ • (vecW ⟨v₀, Sum.inr j⟩ : E)) (v₀, i, 1) =
            c ⟨v₀, Sum.inr j⟩ * (fcoord b X v₀ (u j) i).re := fun j => by
          rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
          simp [vecW, placeI, realizeHLat]
        simp_rw [hre_l, hre_r, Finset.sum_neg_distrib, WithLp.ofLp_zero, Pi.zero_apply] at hc_re
        simp_rw [him_l, him_r, WithLp.ofLp_zero, Pi.zero_apply] at hc_im
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        apply Complex.ext
        · simp only [Complex.re_sum, Complex.zero_re, Complex.mul_re, Finset.sum_sub_distrib]
          dsimp only [γ]; linarith [hc_re]
        · simp only [Complex.im_sum, Complex.zero_im, Complex.mul_im, Finset.sum_add_distrib]
          dsimp only [γ]; linarith [hc_im]
      have hmul := congrArg ((X v₀).mulVec) hf0
      rw [Matrix.mulVec_zero, Matrix.mulVec_sum] at hmul
      simp_rw [Matrix.mulVec_smul] at hmul
      have hxf : ∀ j, (X v₀) *ᵥ fcoord b X v₀ (u j) = vecAt b v₀ (u j) := fun j => by
        unfold fcoord
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hX v₀), Matrix.one_mulVec]
      simpa only [hxf] using hmul
    let U_sub := Submodule.span K (Set.range u)
    let bu : Basis (Fin s) K U_sub := Basis.span huli
    obtain ⟨C, hC⟩ := Submodule.exists_isCompl U_sub
    let pU : V →ₗ[K] U_sub := U_sub.projectionOnto C hC
    let r : V →ₗ[K] (Fin s → K) :=
      (Finsupp.lcoeFun : (Fin s →₀ K) →ₗ[K] (Fin s → K)).comp (bu.repr.toLinearMap.comp pU)
    have hr_u : ∀ j : Fin s, r (u j) = Pi.single j 1 := fun j => by
      have hu_mem : u j ∈ U_sub := Submodule.subset_span ⟨j, rfl⟩
      have hpU : pU (u j) = ⟨u j, hu_mem⟩ :=
        Submodule.projectionOnto_apply_left hC ⟨u j, hu_mem⟩
      have hbu : (⟨u j, hu_mem⟩ : U_sub) = bu j := by
        dsimp only [bu]; rw [Basis.span_apply]
      simp only [r, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hpU, hbu,
        Basis.repr_self, Finsupp.lcoeFun_apply]
      ext k
      simp only [Finsupp.single_apply, Pi.single_apply, eq_comm]
    let Mmat : Matrix ι (Fin s) K := fun i j => b.repr (u j) i
    let Nmat : Matrix (Fin s) ι K := fun j i => r (b i) j
    have hNM : Nmat * Mmat = 1 := by
      ext j k
      rw [Matrix.mul_apply, Matrix.one_apply]
      have hsum : (∑ i : ι, r (b i) j * b.repr (u k) i) = r (u k) j := by
        have hu_repr := (b.sum_repr (u k)).symm
        conv_rhs => rw [hu_repr, map_sum]
        rw [Finset.sum_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
      rw [hsum, hr_u k, Pi.single_apply, eq_comm]
    let M_C : Matrix ι (Fin s) ℂ := Mmat.map v₀.embedding
    let N_C : Matrix (Fin s) ι ℂ := Nmat.map v₀.embedding
    have hNM_C : N_C * M_C = 1 := by
      ext j k
      simp only [N_C, M_C, Matrix.mul_apply, Matrix.map_apply, ← map_mul, ← map_sum]
      have hjk := congrArg (fun M : Matrix (Fin s) (Fin s) K => v₀.embedding (M j k)) hNM
      rw [Matrix.mul_apply, Matrix.one_apply] at hjk
      rw [hjk]
      split_ifs with h <;> simp [Matrix.one_apply, h]
    have hM_mul : M_C *ᵥ γ = 0 := by
      ext i
      rw [Matrix.mulVec, dotProduct]
      have hi := congrArg (fun f : ι → ℂ => f i) hsumC
      rw [Finset.sum_apply] at hi
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
      rw [← hi]
      refine Finset.sum_congr rfl fun j _ => ?_
      change M_C i j * γ j = γ j * vecAt b v₀ (u j) i
      dsimp only [M_C]
      rw [Matrix.map_apply]
      simp [Mmat, vecAt, mul_comm]
    have hγ0 : γ = 0 := by
      calc γ = (1 : Matrix (Fin s) (Fin s) ℂ) *ᵥ γ := (Matrix.one_mulVec γ).symm
        _ = (N_C * M_C) *ᵥ γ := by rw [hNM_C]
        _ = N_C *ᵥ (M_C *ᵥ γ) := (Matrix.mulVec_mulVec γ N_C M_C).symm
        _ = 0 := by rw [hM_mul, Matrix.mulVec_zero]
    cases k₀ with
    | inl j => exact congrArg Complex.re (congrFun hγ0 j)
    | inr j => exact congrArg Complex.im (congrFun hγ0 j)
  have hvecW_sp : ⊤ ≤ Submodule.span ℝ (Set.range vecW) := by
    intro z _
    have hz_sum : z = ∑ v₀ : InfinitePlace K,
        ⟨placeProj K v₀ z.1, hW_proj v₀ z.1 z.2⟩ := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      exact (sum_placeProj K z.1).symm
    rw [hz_sum]
    refine Submodule.sum_mem _ fun v₀ _ => ?_
    have hspan_v₀ : ∀ (w : E) (hw : w ∈ W),
        (⟨placeProj K v₀ w, hW_proj v₀ w hw⟩ : W) ∈ Submodule.span ℝ (Set.range vecW) := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem y hy =>
        rcases hy with ⟨x, hxM', rfl⟩
        have hxU : x ∈ Submodule.span K (Set.range u) := by
          rw [husp]
          exact Submodule.subset_span hxM'
        let U_sub := Submodule.span K (Set.range u)
        let bu : Basis (Fin s) K U_sub := Basis.span huli
        let c : Fin s → K := fun j => bu.repr ⟨x, hxU⟩ j
        have hc : ∑ j : Fin s, c j • u j = x := by
          have hsub := congrArg Subtype.val (bu.sum_repr ⟨x, hxU⟩)
          simp only [Submodule.coe_sum, Submodule.coe_smul] at hsub
          have hbu : ∀ j : Fin s, (bu j : V) = u j := fun j =>
            congrArg Subtype.val (Basis.span_apply huli j)
          simpa only [hbu] using hsub
        have hproj_eq : (⟨placeProj K v₀ (realizeHLat b X x),
            hW_proj v₀ _ (Submodule.subset_span ⟨x, hxM', rfl⟩)⟩ : W) =
            ∑ j : Fin s, ((v₀.embedding (c j)).re • vecW ⟨v₀, Sum.inl j⟩ +
              (v₀.embedding (c j)).im • vecW ⟨v₀, Sum.inr j⟩) := by
          apply Subtype.ext
          rw [Submodule.coe_sum]
          ext p
          rcases p with ⟨v, i, k⟩
          rw [WithLp.ofLp_sum, Finset.sum_apply]
          have hfc : fcoord b X v x = ∑ j : Fin s, v.embedding (c j) • fcoord b X v (u j) := by
            rw [← hc]
            unfold fcoord
            have hvec : vecAt b v (∑ j, c j • u j) = ∑ j, v.embedding (c j) • vecAt b v (u j) := by
              ext i'
              simp only [vecAt, map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul,
                Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_mul]
            rw [hvec, Matrix.mulVec_sum]
            simp_rw [Matrix.mulVec_smul]
          by_cases hv : v = v₀
          · subst hv
            fin_cases k
            · change (placeProj K v (realizeHLat b X x)).ofLp (v, i, 0) =
                  ∑ j : Fin s, (((v.embedding (c j)).re • vecW ⟨v, Sum.inl j⟩ +
                    (v.embedding (c j)).im • vecW ⟨v, Sum.inr j⟩ : W) : E).ofLp (v, i, 0)
              simp only [placeProj, LinearMap.coe_mk, AddHom.coe_mk, realizeHLat,
                AddMonoidHom.coe_mk, ZeroHom.coe_mk, WithLp.ofLp_toLp, ↓reduceIte, hfc,
                Finset.sum_apply, Complex.re_sum, Pi.smul_apply]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul,
                WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_smul,
                Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
              simp [vecW, placeProj, placeI, realizeHLat]
              ring
            · change (placeProj K v (realizeHLat b X x)).ofLp (v, i, 1) =
                  ∑ j : Fin s, (((v.embedding (c j)).re • vecW ⟨v, Sum.inl j⟩ +
                    (v.embedding (c j)).im • vecW ⟨v, Sum.inr j⟩ : W) : E).ofLp (v, i, 1)
              simp only [placeProj, LinearMap.coe_mk, AddHom.coe_mk, realizeHLat,
                AddMonoidHom.coe_mk, ZeroHom.coe_mk, WithLp.ofLp_toLp, Fin.isValue,
                ↓reduceIte, hfc, Finset.sum_apply, Complex.im_sum, Pi.smul_apply]
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul,
                WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_smul,
                Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
              simp [vecW, placeProj, placeI, realizeHLat]
          · simp only [placeProj, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp, hv, ↓reduceIte]
            refine (Finset.sum_eq_zero fun j _ => ?_).symm
            rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul,
              WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_smul,
              Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
            simp [vecW, placeProj, placeI, hv]
        change (⟨placeProj K v₀ ((realizeHLat b X).toIntLinearMap x),
            hW_proj v₀ _ (Submodule.subset_span ⟨x, hxM', rfl⟩)⟩ : W) ∈ Submodule.span ℝ (Set.range vecW)
        change (⟨placeProj K v₀ (realizeHLat b X x),
            hW_proj v₀ _ (Submodule.subset_span ⟨x, hxM', rfl⟩)⟩ : W) ∈ Submodule.span ℝ (Set.range vecW)
        rw [hproj_eq]
        exact Submodule.sum_mem _ fun j _ => Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨v₀, Sum.inl j⟩, rfl⟩))
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨v₀, Sum.inr j⟩, rfl⟩))
      | zero =>
        have hz : (⟨placeProj K v₀ 0, hW_proj v₀ 0 W.zero_mem⟩ : W) = 0 :=
          Subtype.ext (map_zero (placeProj K v₀))
        rw [hz]
        exact Submodule.zero_mem _
      | add y₁ y₂ hy₁_mem hy₂_mem hy₁ hy₂ =>
        have hadd : (⟨placeProj K v₀ (y₁ + y₂), hW_proj v₀ _ (W.add_mem hy₁_mem hy₂_mem)⟩ : W) =
            ⟨placeProj K v₀ y₁, hW_proj v₀ y₁ hy₁_mem⟩ +
              ⟨placeProj K v₀ y₂, hW_proj v₀ y₂ hy₂_mem⟩ :=
          Subtype.ext (map_add (placeProj K v₀) y₁ y₂)
        rw [hadd]; exact Submodule.add_mem _ hy₁ hy₂
      | smul r y hy_mem hy =>
        have hsm : (⟨placeProj K v₀ (r • y), hW_proj v₀ _ (W.smul_mem r hy_mem)⟩ : W) =
            r • ⟨placeProj K v₀ y, hW_proj v₀ y hy_mem⟩ :=
          Subtype.ext (map_smul (placeProj K v₀) r y)
        rw [hsm]; exact Submodule.smul_mem _ r hy
    exact hspan_v₀ z.1 z.2
  let bW : Basis (Σ v₀ : InfinitePlace K, Fin s ⊕ Fin s) ℝ W := Basis.mk hvecW_li hvecW_sp
  have hdiag : LinearMap.toMatrix bW bW scaleW.toLinearMap =
      Matrix.diagonal fun p : (Σ v₀ : InfinitePlace K, Fin s ⊕ Fin s) => (B p.1)⁻¹ := by
    ext p q
    rw [LinearMap.toMatrix_apply, Matrix.diagonal_apply]
    have hsw : scaleW.toLinearMap (bW q) = (B q.1)⁻¹ • bW q := by
      apply Subtype.ext
      rw [Basis.mk_apply]
      change scalePlace K (fun v => (B v)⁻¹) (vecW q : E) = (B q.1)⁻¹ • (vecW q : E)
      ext r
      rcases r with ⟨v, i, j⟩
      have hp := congrArg (fun z : E => z (v, i, j)) (hvecW_place q.1 v q.2)
      by_cases hv : v = q.1
      · subst hv
        rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
        simp [scalePlace]
      · have hp' : (vecW q : E) (v, i, j) = 0 := by simpa [placeProj, hv] using hp
        change ((scalePlace K fun v ↦ (B v)⁻¹) ↑(vecW q)).ofLp (v, i, j) =
            ((B q.1)⁻¹ • (vecW q : E)).ofLp (v, i, j)
        rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
        simp only [scalePlace, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp, hp', mul_zero]
    rw [hsw, map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, bW.repr_self,
      Finsupp.single_apply]
    by_cases hpq : p = q
    · subst hpq; simp
    · simp [hpq, Ne.symm hpq]
  have hdet_W : LinearMap.det scaleW.toLinearMap =
      ∏ v : InfinitePlace K, ((B v)⁻¹) ^ (2 * s) := by
    rw [← LinearMap.det_toMatrix bW scaleW.toLinearMap, hdiag, Matrix.det_diagonal,
      Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun v _ => ?_
    change ∏ _ : Fin s ⊕ Fin s, (B v)⁻¹ = (B v)⁻¹ ^ (2 * s)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin, two_mul]
  let Λ_W : Submodule ℤ W := Λ.comap (W.subtype.restrictScalars ℤ)
  let Λ_BW : Submodule ℤ W := Λ_B.comap (W.subtype.restrictScalars ℤ)
  let eqW : Λ_W ≃ₗ[ℤ] Λ :=
    { toFun := fun x => ⟨x.1.1, x.2⟩
      invFun := fun y => ⟨⟨y.1, Submodule.subset_span y.2⟩, y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hΛ_BW_sub : ∀ y ∈ Λ_B, y ∈ W := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (hS_eq y).mp hy
    exact hW_scale x (Submodule.subset_span hx)
  let eqBW : Λ_BW ≃ₗ[ℤ] Λ_B :=
    { toFun := fun x => ⟨x.1.1, x.2⟩
      invFun := fun y => ⟨⟨y.1, hΛ_BW_sub y.1 y.2⟩, y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hD_W : DiscreteTopology Λ_W :=
    DiscreteTopology.of_continuous_injective (f := eqW)
      (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _) eqW.injective
  have hIsZ_W : IsZLattice ℝ Λ_W := ⟨Submodule.span_span_coe_preimage⟩
  have hD_BW : DiscreteTopology Λ_BW :=
    DiscreteTopology.of_continuous_injective (f := eqBW)
      (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _) eqBW.injective
  have hcov_W : covol Λ = covol Λ_W := by
    let bΛW := Module.finBasis ℤ Λ_W
    let bΛ := bΛW.map eqW
    rw [ArakelovCovolume.covol_eq_sqrt_det_gram Λ bΛ,
      ArakelovCovolume.covol_eq_sqrt_det_gram Λ_W bΛW]
    congr 1
  have hcov_BW : covol Λ_B = covol Λ_BW := by
    let bΛBW := Module.finBasis ℤ Λ_BW
    let bΛB := bΛBW.map eqBW
    rw [ArakelovCovolume.covol_eq_sqrt_det_gram Λ_B bΛB,
      ArakelovCovolume.covol_eq_sqrt_det_gram Λ_BW bΛBW]
    congr 1
  have hmem_W : ∀ y : W, y ∈ Λ_BW ↔ ∃ x ∈ Λ_W, scaleW x = y := by
    intro y
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := (hS_eq y.1).mp hy
      exact ⟨⟨x, Submodule.subset_span hx⟩, hx, Subtype.ext hxy⟩
    · rintro ⟨x, hx, rfl⟩
      exact (hS_eq (scaleW x).1).mpr ⟨x.1, hx, rfl⟩
  have hcov_rel : covol Λ_BW = |LinearMap.det scaleW.toLinearMap| * covol Λ_W :=
    covol_eq_abs_det_of_eq_image Λ_W Λ_BW scaleW hmem_W
  have hcov_B_eq : covol Λ_B = (∏ v : InfinitePlace K, ((B v)⁻¹) ^ (2 * s)) * covol Λ := by
    rw [hcov_BW, hcov_rel, hcov_W, hdet_W, abs_of_nonneg (Finset.prod_nonneg fun v _ =>
      pow_nonneg (inv_nonneg.mpr (hB v).le) _)]
  have hrk_eq : ArakelovCovolume.rk Λ = 2 * s * Fintype.card (InfinitePlace K) := by
    unfold ArakelovCovolume.rk
    rw [ArakelovCovolume.finrank_int_eq_finrank_real_span Λ, Module.finrank_eq_card_basis bW,
      Fintype.card_sigma, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Fintype.card_sum, Fintype.card_fin]
    ring
  have hrk_B_eq : ArakelovCovolume.rk Λ_B = ArakelovCovolume.rk Λ := by
    unfold ArakelovCovolume.rk
    exact LinearEquiv.finrank_eq eqZ_B.symm
  have hrk_pos : (0 : ℝ) < (ArakelovCovolume.rk Λ : ℝ) := by
    exact_mod_cast ArakelovCovolume.rk_pos_of_ne_bot Λ hΛ_ne
  have hs_ne : (s : ℝ) ≠ 0 := by
    intro hs0
    have : (ArakelovCovolume.rk Λ : ℝ) = 0 := by rw [hrk_eq]; push_cast; rw [hs0]; simp
    exact hrk_pos.ne' this
  have hnPl_ne : (Fintype.card (InfinitePlace K) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  have hprod_pos : 0 < ∏ v : InfinitePlace K, ((B v)⁻¹) ^ (2 * s) :=
    Finset.prod_pos fun v _ => pow_pos (inv_pos.mpr (hB v)) _
  have hslope_eq : ArakelovCovolume.slope Λ_B =
      ArakelovCovolume.slope Λ + (1 / (Fintype.card (InfinitePlace K) : ℝ)) *
        ∑ v : InfinitePlace K, Real.log (B v) := by
    unfold ArakelovCovolume.slope ArakelovCovolume.degAr
    rw [hrk_B_eq, hcov_B_eq, Real.log_mul hprod_pos.ne' (ArakelovCovolume.covol_pos Λ).ne',
      Real.log_prod (fun v _ => (pow_pos (inv_pos.mpr (hB v)) _).ne')]
    simp_rw [Real.log_pow, Real.log_inv]
    rw [hrk_eq]
    push_cast
    have hsum_neg : ∑ v : InfinitePlace K, (2 * (s : ℝ)) * -Real.log (B v) =
        -(2 * (s : ℝ)) * ∑ v : InfinitePlace K, Real.log (B v) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      ring
    rw [hsum_neg]
    field_simp [hs_ne, hnPl_ne]
    ring
  unfold muOK
  change 2 * ArakelovCovolume.slope Λ_B - Real.log 2 + NumberFieldHLat.logDiscDivDeg K =
    2 * ArakelovCovolume.slope Λ - Real.log 2 + NumberFieldHLat.logDiscDivDeg K +
      (2 / (Fintype.card (InfinitePlace K) : ℝ)) * ∑ v : InfinitePlace K, Real.log (B v)
  rw [hslope_eq]
  ring

private lemma exists_im_ne_zero_of_isComplex (K : Type) [Field K] [NumberField K]
    [IsTotallyComplex K] (v : InfinitePlace K) :
    ∃ γ : K, (v.embedding γ).im ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  have hreal : v.IsReal := NumberField.InfinitePlace.isReal_iff.mpr
    (NumberField.ComplexEmbedding.isReal_iff.mpr (by
      ext x
      exact Complex.conj_eq_iff_im.mpr (h x)))
  exact (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr
    (IsTotallyComplex.isComplex v)) hreal

private lemma norm_placeMat_le_of_normAt_le {K V ι MonI : Type}
    [Field K] [NumberField K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] [Fintype MonI] [DecidableEq MonI]
    (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    (v : InfinitePlace K) (T_v : Matrix MonI ι ℂ)
    (h_bound : ∀ x : V, ∑ m : MonI, ‖(T_v *ᵥ fcoord b X v x) m‖ ^ 2 ≤
      ∑ i : ι, ‖fcoord b X v x i‖ ^ 2) :
    ∀ z : ι → ℂ, ∑ m : MonI, ‖(T_v *ᵥ z) m‖ ^ 2 ≤ ∑ i : ι, ‖z i‖ ^ 2 := by
  intro z
  obtain ⟨γ, hγ⟩ := exists_im_ne_zero_of_isComplex K v
  let y : ι → ℂ := X v *ᵥ z
  let a : ι → ℝ := fun i => (y i).re - ((y i).im / (v.embedding γ).im) * (v.embedding γ).re
  let bC : ι → ℝ := fun i => (y i).im / (v.embedding γ).im
  have hy_decomp : ∀ i, (a i : ℂ) + (bC i : ℂ) * v.embedding γ = y i := fun i => by
    apply Complex.ext
    · simp [a, bC]
    · simp [a, bC, hγ]
  have hrat_seq : ∀ (r : ℝ) (n : ℕ), ∃ q : ℚ, |(q : ℝ) - r| < 1 / ((n : ℝ) + 1) := by
    intro r n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show r - 1 / ((n : ℝ) + 1) < r + 1 / ((n : ℝ) + 1) by linarith)
    exact ⟨q, abs_lt.mpr ⟨by linarith, by linarith⟩⟩
  let q_seq : ℕ → ι → ℚ := fun n i => (hrat_seq (a i) n).choose
  let r_seq : ℕ → ι → ℚ := fun n i => (hrat_seq (bC i) n).choose
  let x_seq : ℕ → V := fun n => ∑ i : ι, (((q_seq n i : K) + (r_seq n i : K) * γ)) • b i
  let z_seq : ℕ → ι → ℂ := fun n => fcoord b X v (x_seq n)
  have hvec_tendsto : ∀ i : ι, Filter.Tendsto (fun n => vecAt b v (x_seq n) i) Filter.atTop (nhds (y i)) := by
    intro i
    have hvec_eq : ∀ n, vecAt b v (x_seq n) i =
        ((q_seq n i : ℂ) + (r_seq n i : ℂ) * v.embedding γ) := fun n => by
      simp only [vecAt, x_seq, map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul,
        Finset.sum_apply, Pi.smul_apply, Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [hj]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    simp_rw [hvec_eq, ← hy_decomp i]
    have ht_inv : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have ht_q : Filter.Tendsto (fun n => (q_seq n i : ℝ)) Filter.atTop (nhds (a i)) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp ht_inv) ε hε
      refine ⟨N, fun n hn => ?_⟩
      have h1 : dist ((q_seq n i : ℝ)) (a i) < 1 / ((n : ℝ) + 1) := by
        rw [Real.dist_eq]; exact (hrat_seq (a i) n).choose_spec
      have h2 := hN n hn
      rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)] at h2
      linarith
    have ht_r : Filter.Tendsto (fun n => (r_seq n i : ℝ)) Filter.atTop (nhds (bC i)) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp ht_inv) ε hε
      refine ⟨N, fun n hn => ?_⟩
      have h1 : dist ((r_seq n i : ℝ)) (bC i) < 1 / ((n : ℝ) + 1) := by
        rw [Real.dist_eq]; exact (hrat_seq (bC i) n).choose_spec
      have h2 := hN n hn
      rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)] at h2
      linarith
    exact ((Complex.continuous_ofReal.continuousAt.tendsto.comp ht_q).add
      ((Complex.continuous_ofReal.continuousAt.tendsto.comp ht_r).mul tendsto_const_nhds))
  have hz_tendsto : Filter.Tendsto z_seq Filter.atTop (nhds z) := by
    have hz_eq : z = (X v)⁻¹ *ᵥ y := by
      simp [y, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hX v)]
    rw [hz_eq]
    refine tendsto_pi_nhds.mpr fun i => ?_
    simp only [z_seq, fcoord, Matrix.mulVec, dotProduct]
    exact tendsto_finsetSum _ fun j _ =>
      tendsto_const_nhds.mul (hvec_tendsto j)
  have hLHS : Filter.Tendsto (fun n => ∑ m : MonI, ‖(T_v *ᵥ z_seq n) m‖ ^ 2)
      Filter.atTop (nhds (∑ m : MonI, ‖(T_v *ᵥ z) m‖ ^ 2)) := by
    refine tendsto_finsetSum _ fun m _ => ?_
    refine (Filter.Tendsto.norm ?_).pow 2
    simp only [Matrix.mulVec, dotProduct]
    exact tendsto_finsetSum _ fun i _ =>
      tendsto_const_nhds.mul ((tendsto_pi_nhds.mp hz_tendsto) i)
  have hRHS : Filter.Tendsto (fun n => ∑ i : ι, ‖z_seq n i‖ ^ 2)
      Filter.atTop (nhds (∑ i : ι, ‖z i‖ ^ 2)) :=
    tendsto_finsetSum _ fun i _ => ((tendsto_pi_nhds.mp hz_tendsto) i).norm.pow 2
  exact le_of_tendsto_of_tendsto' hLHS hRHS (fun n => h_bound (x_seq n))

/-- **Monomial Lattice `muMaxOK` Upper Bound (`monomial_lattice_muMaxOK_le`)**:
For any `A : NumberFieldHLat K` (`A.L ≠ ⊥`) and any `K`-linear injection `φ : A.V →ₗ[K] (MonI → K)`
mapping `A.L` into `idealSmul I (stdMonomialLat K MonI)` with place-wise norm bound
`normAt (Pi.basisFun K MonI) (monX w) v (φ x) ≤ B v * normAt A.b A.X v x`,
`muMaxOK A.b A.X A.L ≤ -Real.log c₀ - 2 * Real.log (absNorm I) / [K : ℚ] + (2 / |Pl_∞(K)|) * ∑ v, Real.log (B v)`. -/
theorem monomial_lattice_muMaxOK_le {K MonI : Type}
    [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    [Fintype MonI] [DecidableEq MonI] [Nonempty MonI]
    (A : NumberFieldHLat K) (hAne : A.L ≠ ⊥)
    (w : MonI → ℝ) (hw : ∀ m, 0 < w m) (c₀ : ℝ) (hc₀ : 0 < c₀) (hcw : ∀ m, c₀ ≤ w m)
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (B : InfinitePlace K → ℝ) (hB : ∀ v, 0 < B v)
    (φ : A.V →ₗ[K] (MonI → K)) (hφ_inj : Function.Injective φ)
    (hφL : ∀ x ∈ A.L, φ x ∈ idealSmul (I : Submodule (𝓞 K) K) (stdMonomialLat K MonI))
    (hφ_norm : ∀ (v : InfinitePlace K) (x : A.V),
      normAt (Pi.basisFun K MonI) (monX (K := K) w) v (φ x) ≤ B v * normAt A.b A.X v x) :
    muMaxOK A.b A.X A.L ≤
      -Real.log c₀ - 2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ) +
        (2 / (Fintype.card (InfinitePlace K) : ℝ)) * ∑ v : InfinitePlace K, Real.log (B v) := by
  have hS_ne : { t | ∃ N : Submodule (𝓞 K) A.V, N ≤ A.L ∧ N ≠ ⊥ ∧ muOK A.b A.X N = t }.Nonempty :=
    ⟨A.mu, A.L, le_rfl, hAne, muOK_eq_mu A⟩
  refine csSup_le hS_ne ?_
  rintro t ⟨R, hRL, hRne, rfl⟩
  let X_B : InfinitePlace K → Matrix MonI MonI ℂ := fun v => (B v : ℂ) • monX (K := K) w v
  have hX_B : ∀ v, IsUnit (X_B v).det := fun v => by
    rw [Matrix.det_smul]
    exact (IsUnit.mk0 _ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (hB v).ne'))).mul
      (isUnit_det_monX w hw v)
  let M_φ : Matrix MonI A.ι K := fun m i => φ (A.b i) m
  let T_mat : InfinitePlace K → Matrix MonI A.ι ℂ :=
    fun v => (X_B v)⁻¹ * (M_φ.map v.embedding) * A.X v
  let φ_R : EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2) →ₗ[ℝ]
      EuclideanSpace ℝ (InfinitePlace K × MonI × Fin 2) :=
    { toFun := fun u => WithLp.toLp 2 fun p =>
        let z : A.ι → ℂ := fun i => ⟨u (p.1, i, 0), u (p.1, i, 1)⟩
        let wv : MonI → ℂ := T_mat p.1 *ᵥ z
        if p.2.2 = 0 then (wv p.2.1).re else (wv p.2.1).im
      map_add' := fun u₁ u₂ => by
        ext p
        rcases p with ⟨v, m, j⟩
        have hz : (fun i : A.ι => (⟨(u₁ + u₂) (v, i, 0), (u₁ + u₂) (v, i, 1)⟩ : ℂ)) =
            (fun i => ⟨u₁ (v, i, 0), u₁ (v, i, 1)⟩) + (fun i => ⟨u₂ (v, i, 0), u₂ (v, i, 1)⟩) := by
          ext i; apply Complex.ext <;> simp
        dsimp only
        rw [hz, Matrix.mulVec_add]
        simp only [WithLp.ofLp_add, Pi.add_apply]
        split_ifs <;> simp [Complex.add_re, Complex.add_im]
      map_smul' := fun c u => by
        ext p
        rcases p with ⟨v, m, j⟩
        have hz : (fun i : A.ι => (⟨(c • u) (v, i, 0), (c • u) (v, i, 1)⟩ : ℂ)) =
            (c : ℂ) • (fun i => ⟨u (v, i, 0), u (v, i, 1)⟩) := by
          ext i; apply Complex.ext <;> simp
        dsimp only
        rw [hz, Matrix.mulVec_smul]
        simp only [RingHom.id_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
        split_ifs <;> simp [Complex.mul_re, Complex.mul_im] }
  have hφ_R_realize : ∀ x : A.V,
      φ_R (realizeHLat A.b A.X x) = realizeHLat (Pi.basisFun K MonI) X_B (φ x) := by
    intro x
    ext p
    rcases p with ⟨v, m, j⟩
    have hz_eq : (fun i : A.ι => (⟨(realizeHLat A.b A.X x) (v, i, 0),
        (realizeHLat A.b A.X x) (v, i, 1)⟩ : ℂ)) = fcoord A.b A.X v x := by
      ext i; simp [realizeHLat]
    have hvec_phi : vecAt (Pi.basisFun K MonI) v (φ x) =
        (M_φ.map v.embedding) *ᵥ vecAt A.b v x := by
      ext m'
      have hx_eq : x = ∑ i : A.ι, A.b.repr x i • A.b i := (A.b.sum_repr x).symm
      calc vecAt (Pi.basisFun K MonI) v (φ x) m'
          = v.embedding (φ (∑ i, A.b.repr x i • A.b i) m') := by rw [← hx_eq]; rfl
        _ = v.embedding (∑ i, A.b.repr x i * M_φ m' i) := by
            congr 1; rw [map_sum, Finset.sum_apply]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [map_smul, Pi.smul_apply, smul_eq_mul]
        _ = ∑ i, v.embedding (M_φ m' i) * v.embedding (A.b.repr x i) := by
            rw [map_sum]; refine Finset.sum_congr rfl fun i _ => by rw [map_mul, mul_comm]
        _ = ((M_φ.map v.embedding) *ᵥ vecAt A.b v x) m' := rfl
    have hfc_phi : T_mat v *ᵥ fcoord A.b A.X v x =
        fcoord (Pi.basisFun K MonI) X_B v (φ x) := by
      dsimp only [T_mat]
      have hAx : A.X v *ᵥ fcoord A.b A.X v x = vecAt A.b v x := by
        unfold fcoord
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (A.hX v), Matrix.one_mulVec]
      rw [← Matrix.mulVec_mulVec, hAx, ← Matrix.mulVec_mulVec, ← hvec_phi]
      rfl
    simp only [φ_R, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp, hz_eq, hfc_phi]
    rfl
  have hT_bound : ∀ (v : InfinitePlace K) (x : A.V),
      ∑ m : MonI, ‖(T_mat v *ᵥ fcoord A.b A.X v x) m‖ ^ 2 ≤
        ∑ i : A.ι, ‖fcoord A.b A.X v x i‖ ^ 2 := by
    intro v x
    have hfc : T_mat v *ᵥ fcoord A.b A.X v x =
        (B v : ℂ)⁻¹ • fcoord (Pi.basisFun K MonI) (monX (K := K) w) v (φ x) := by
      have h1 : T_mat v *ᵥ fcoord A.b A.X v x =
          fcoord (Pi.basisFun K MonI) X_B v (φ x) := by
        have := congrArg (fun u : EuclideanSpace ℝ (InfinitePlace K × MonI × Fin 2) =>
          fun m : MonI => (⟨u (v, m, 0), u (v, m, 1)⟩ : ℂ)) (hφ_R_realize x)
        ext m
        have hm := congrFun this m
        simp only [φ_R, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp, realizeHLat,
          AddMonoidHom.coe_mk, ZeroHom.coe_mk, ↓reduceIte, Fin.isValue, Fin.one_eq_zero_iff,
          Nat.reduceEqDiff] at hm
        have hfc0 : (fun i : A.ι => (⟨(fcoord A.b A.X v x i).re,
            (fcoord A.b A.X v x i).im⟩ : ℂ)) = fcoord A.b A.X v x := by
          ext i; rfl
        rw [hfc0] at hm
        exact Complex.ext (congrArg Complex.re hm) (congrArg Complex.im hm)
      rw [h1, fcoord_placeScale (Pi.basisFun K MonI) (monX (K := K) w)
        (isUnit_det_monX w hw) B (fun v' => (hB v').ne') v (φ x)]
    rw [hfc]
    have hsq := sq_le_sq₀
      (Real.sqrt_nonneg _) (mul_nonneg (hB v).le (Real.sqrt_nonneg _)) |>.mpr (hφ_norm v x)
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), mul_pow,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at hsq
    have hsum : ∑ m : MonI, ‖((B v : ℂ)⁻¹ • fcoord (Pi.basisFun K MonI) (monX (K := K) w) v (φ x)) m‖ ^ 2 =
        (B v)⁻¹ ^ 2 * ∑ m : MonI, ‖fcoord (Pi.basisFun K MonI) (monX (K := K) w) v (φ x) m‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp [Pi.smul_apply, smul_eq_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (hB v), mul_pow]
    rw [hsum]
    have hBv_sq : (B v) ^ 2 > 0 := pow_pos (hB v) 2
    calc (B v)⁻¹ ^ 2 * ∑ m : MonI, ‖fcoord (Pi.basisFun K MonI) (monX (K := K) w) v (φ x) m‖ ^ 2
        ≤ (B v)⁻¹ ^ 2 * (B v ^ 2 * ∑ i : A.ι, ‖fcoord A.b A.X v x i‖ ^ 2) := by gcongr
      _ = ∑ i : A.ι, ‖fcoord A.b A.X v x i‖ ^ 2 := by
          rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ (hB v).ne', one_pow, one_mul]
  have hφ_R_norm : ∀ u : EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2),
      ‖φ_R u‖ ≤ ‖u‖ := by
    intro u
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.norm_sq_eq,
      EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun v _ => ?_
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    let z : A.ι → ℂ := fun i => ⟨u (v, i, 0), u (v, i, 1)⟩
    have hL : ∑ m : MonI, ∑ j : Fin 2, ‖φ_R u (v, m, j)‖ ^ 2 =
        ∑ m : MonI, ‖(T_mat v *ᵥ z) m‖ ^ 2 := by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Fin.sum_univ_two, Complex.sq_norm, Complex.normSq_apply]
      simp only [φ_R, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs,
        ↓reduceIte, Fin.isValue, Fin.one_eq_zero_iff, Nat.reduceEqDiff]
      dsimp only [z]
      ring
    have hR : ∑ i : A.ι, ∑ j : Fin 2, ‖u (v, i, j)‖ ^ 2 = ∑ i : A.ι, ‖z i‖ ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.sum_univ_two, Complex.sq_norm, Complex.normSq_apply]
      simp only [z, Real.norm_eq_abs, sq_abs]
      ring
    rw [hL, hR]
    exact norm_placeMat_le_of_normAt_le A.b A.X A.hX v (T_mat v) (hT_bound v) z
  let M' : Submodule (𝓞 K) (MonI → K) := R.map (φ.restrictScalars (𝓞 K))
  have hM'_ne : M' ≠ ⊥ := by
    intro h0
    apply hRne
    rw [eq_bot_iff]
    intro x hx
    have hm : φ x ∈ M' := ⟨x, hx, rfl⟩
    rw [h0, Submodule.mem_bot] at hm
    exact hφ_inj (hm.trans (map_zero φ).symm)
  have hM'_ideal : M' ≤ idealSmul (I : Submodule (𝓞 K) K) (stdMonomialLat K MonI) := by
    rintro _ ⟨x, hxR, rfl⟩
    exact hφL x (hRL hxR)
  have : DiscreteTopology (zRealizeMod (Pi.basisFun K MonI) (monX (K := K) w)
      (idealSmul (I : Submodule (𝓞 K) K) (stdMonomialLat K MonI))) :=
    discreteTopology_idealSmul_stdMonomial K MonI I hI w hw
  have : DiscreteTopology (zRealizeMod (Pi.basisFun K MonI) (monX (K := K) w) M') :=
    ArakelovCovolume.discreteTopology_of_le
      (Submodule.map_mono (Submodule.restrictScalars_mono ℤ hM'_ideal))
  obtain ⟨hDisc_XB, hcov_scale⟩ := covol_placeScale_submodule (Pi.basisFun K MonI)
    (monX (K := K) w) (isUnit_det_monX w hw) M' hM'_ne B hB
  have : DiscreteTopology (zRealizeMod (Pi.basisFun K MonI) X_B M') := hDisc_XB
  let L_R := zRealizeMod A.b A.X R
  let L_M' := zRealizeMod (Pi.basisFun K MonI) X_B M'
  have : DiscreteTopology L_R :=
    ArakelovCovolume.discreteTopology_of_le (Submodule.map_mono (Submodule.restrictScalars_mono ℤ hRL))
  have hL_R_ne : L_R ≠ ⊥ := by
    intro h0
    apply hRne
    rw [eq_bot_iff]
    intro x hx
    have hmem : realizeHLat A.b A.X x ∈ L_R := ⟨x, hx, rfl⟩
    rw [h0, Submodule.mem_bot] at hmem
    exact realizeHLat_injective A.b A.X A.hX (hmem.trans (map_zero _).symm)
  have hinjA := realizeHLat_injective A.b A.X A.hX
  have hinjM := realizeHLat_injective (Pi.basisFun K MonI) X_B hX_B
  have hmem_R : ∀ u : L_R, φ_R u.1 ∈ L_M' := by
    rintro ⟨u, x, hxR, rfl⟩
    change φ_R (realizeHLat A.b A.X x) ∈ L_M'
    rw [hφ_R_realize x]
    exact ⟨φ x, ⟨x, hxR, rfl⟩, rfl⟩
  have hinv_mem : ∀ w' : L_M',
      realizeHLat A.b A.X w'.2.choose_spec.1.choose ∈ L_R := fun w' =>
    ⟨w'.2.choose_spec.1.choose, w'.2.choose_spec.1.choose_spec.1, rfl⟩
  let e_R : L_R ≃ₗ[ℤ] L_M' :=
    { toFun := fun u => ⟨φ_R u.1, hmem_R u⟩
      invFun := fun w' => ⟨realizeHLat A.b A.X w'.2.choose_spec.1.choose, hinv_mem w'⟩
      map_add' := fun u₁ u₂ => Subtype.ext (map_add φ_R u₁.1 u₂.1)
      map_smul' := fun k u => Subtype.ext (map_zsmul φ_R k u.1)
      left_inv := fun u => by
        apply Subtype.ext
        rcases u with ⟨u, x, hxR, rfl⟩
        let w' : L_M' := ⟨φ_R (realizeHLat A.b A.X x), hmem_R ⟨_, x, hxR, rfl⟩⟩
        let x' := w'.2.choose_spec.1.choose
        have hphi_x' : φ x' = w'.2.choose := w'.2.choose_spec.1.choose_spec.2
        have hw'_eq : realizeHLat (Pi.basisFun K MonI) X_B w'.2.choose = w'.1 :=
          w'.2.choose_spec.2
        have hphi_eq : realizeHLat (Pi.basisFun K MonI) X_B (φ x') =
            realizeHLat (Pi.basisFun K MonI) X_B (φ x) := by
          rw [hphi_x', hw'_eq]
          exact hφ_R_realize x
        have hx_eq : x' = x := hφ_inj (hinjM hphi_eq)
        change realizeHLat A.b A.X x' = (realizeHLat A.b A.X).toIntLinearMap x
        rw [hx_eq]
        rfl
      right_inv := fun w' => by
        apply Subtype.ext
        let x' := w'.2.choose_spec.1.choose
        have hphi_x' : φ x' = w'.2.choose := w'.2.choose_spec.1.choose_spec.2
        change φ_R ((realizeHLat A.b A.X).toIntLinearMap x') = w'.1
        change φ_R (realizeHLat A.b A.X x') = w'.1
        rw [hφ_R_realize x', hphi_x']
        exact w'.2.choose_spec.2 }
  have hslope_R := (slope_le_of_contraction L_R L_M' hL_R_ne e_R φ_R (fun _ => rfl) hφ_R_norm).2.2.2
  have hmu_R_le : muOK A.b A.X R ≤ muOK (Pi.basisFun K MonI) X_B M' := by
    unfold muOK
    change 2 * ArakelovCovolume.slope L_R - Real.log 2 + NumberFieldHLat.logDiscDivDeg K ≤
      2 * ArakelovCovolume.slope L_M' - Real.log 2 + NumberFieldHLat.logDiscDivDeg K
    linarith
  let L_line : MonI → Submodule (𝓞 K) (MonI → K) := fun m =>
    (I : Submodule (𝓞 K) K).map
      ((LinearMap.toSpanSingleton K (MonI → K) (Pi.single m (1 : K))).restrictScalars (𝓞 K))
  have hL_line : ∀ m, L_line m ≤ (Submodule.span K {Pi.single m (1 : K)}).restrictScalars (𝓞 K) := by
    intro m x hx
    obtain ⟨a, _, rfl⟩ := hx
    exact Submodule.smul_mem _ a (Submodule.subset_span rfl)
  have hDisc_line : ∀ m, DiscreteTopology (zRealizeMod (Pi.basisFun K MonI) (monX (K := K) w) (L_line m)) := by
    intro m
    have hle : L_line m ≤ idealSmul (I : Submodule (𝓞 K) K) (stdMonomialLat K MonI) := by
      rw [idealSmul_stdMonomial_eq]
      exact le_iSup L_line m
    exact ArakelovCovolume.discreteTopology_of_le (Submodule.map_mono (Submodule.restrictScalars_mono ℤ hle))
  have hM'_sup : M' ≤ ⨆ m ∈ (Finset.univ : Finset MonI), L_line m := by
    rw [idealSmul_stdMonomial_eq] at hM'_ideal
    refine hM'_ideal.trans (iSup_le fun m => ?_)
    exact le_iSup₂ (f := fun m (_ : m ∈ (Finset.univ : Finset MonI)) => L_line m) m (Finset.mem_univ m)
  have hmu_M'_le : muOK (Pi.basisFun K MonI) (monX (K := K) w) M' ≤
      -Real.log c₀ - 2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ) := by
    refine muMaxOK_orthog_iSup K MonI w hw L_line hL_line hDisc_line Finset.univ
      Finset.univ_nonempty _ (fun m _ N hN_le hN_ne => ?_) M' hM'_sup hM'_ne
    exact max_slope_line_neg_log K MonI w hw c₀ hc₀ m (hcw m) I hI N hN_le hN_ne
  linarith

/-- **Monomial Lattice Arakelov Slope Upper Bound (`monomial_lattice_muMax_le`)**:
Combines `monomial_lattice_muMaxOK_le` with `muOK_eq_mu` to bound both `A.mu` and `muMaxOK A.b A.X A.L`
directly by `-Real.log c₀ - 2 * Real.log (absNorm I) / [K : ℚ] + (2 / |Pl_∞(K)|) * ∑ v, Real.log (B v)`. -/
theorem monomial_lattice_muMax_le {K MonI : Type}
    [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    [Fintype MonI] [DecidableEq MonI] [Nonempty MonI]
    (A : NumberFieldHLat K) (hAne : A.L ≠ ⊥)
    (w : MonI → ℝ) (hw : ∀ m, 0 < w m) (c₀ : ℝ) (hc₀ : 0 < c₀) (hcw : ∀ m, c₀ ≤ w m)
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (B : InfinitePlace K → ℝ) (hB : ∀ v, 0 < B v)
    (φ : A.V →ₗ[K] (MonI → K)) (hφ_inj : Function.Injective φ)
    (hφL : ∀ x ∈ A.L, φ x ∈ idealSmul (I : Submodule (𝓞 K) K) (stdMonomialLat K MonI))
    (hφ_norm : ∀ (v : InfinitePlace K) (x : A.V),
      normAt (Pi.basisFun K MonI) (monX (K := K) w) v (φ x) ≤ B v * normAt A.b A.X v x) :
    A.mu ≤
        -Real.log c₀ - 2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ) +
          (2 / (Fintype.card (InfinitePlace K) : ℝ)) * ∑ v : InfinitePlace K, Real.log (B v) ∧
      muMaxOK A.b A.X A.L ≤
        -Real.log c₀ - 2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ) +
          (2 / (Fintype.card (InfinitePlace K) : ℝ)) * ∑ v : InfinitePlace K, Real.log (B v) := by
  have hmax := monomial_lattice_muMaxOK_le A hAne w hw c₀ hc₀ hcw I hI B hB φ hφ_inj hφL hφ_norm
  refine ⟨?_, hmax⟩
  have hmu_le : A.mu ≤ muMaxOK A.b A.X A.L := by
    rw [← muOK_eq_mu A]
    refine le_csSup ?_ ⟨A.L, le_rfl, hAne, rfl⟩
    refine ⟨A.muMax,
      fun t ⟨N, hNL, hNne, ht⟩ => ?_⟩
    subst ht
    have hLN_ne : zRealizeMod A.b A.X N ≠ ⊥ := by
      intro h0
      apply hNne
      rw [eq_bot_iff]
      intro x hx
      have hmem : realizeHLat A.b A.X x ∈ zRealizeMod A.b A.X N := ⟨x, hx, rfl⟩
      rw [h0, Submodule.mem_bot] at hmem
      exact realizeHLat_injective A.b A.X A.hX (hmem.trans (map_zero _).symm)
    have hslope := ArakelovCovolume.slope_le_muMax A.zRealize
      (zRealizeMod A.b A.X N) (Submodule.map_mono (Submodule.restrictScalars_mono ℤ hNL)) hLN_ne
    unfold muOK NumberFieldHLat.muMax
    change 2 * ArakelovCovolume.slope (zRealizeMod A.b A.X N) - Real.log 2 +
        NumberFieldHLat.logDiscDivDeg K ≤
      2 * ArakelovCovolume.muMax A.zRealize - Real.log 2 + NumberFieldHLat.logDiscDivDeg K
    linarith
  exact hmu_le.trans hmax

end PlaceRescalingAndMonomialMuMax

end MonomialLatticeMuMax

end RHDirect.Stage14M2_TotallyPosTrace

