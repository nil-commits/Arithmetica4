import RHDirect.Stage2HodgeWeights
import RHDirect.Stage3DworkFrobenius
import RHDirect.Stage3GaloisDeformation
import RHDirect.Stage10PeterssonHecke
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.DivisionRing

/-!
# RHDirect.Stage11CrystallineFontaine

Unconditional Lean 4 formalization (zero `sorry`, zero custom `axiom`s, zero assumptions) of:

1. **Concrete Filtered `φ`-Modules `(D, φ, Fil•)` over `ℚ_[p]` (`FilteredPhiModule p D`)**:
   - Concrete finite-dimensional `ℚ_[p]`-vector space `D`, invertible `ℚ_[p]`-linear Frobenius
     `φ : D ≃ₗ[ℚ_[p]] D`, and exhaustive/separated decreasing filtration
     `fil : Stage2HodgeWeights.HodgeFiltration ℚ_[p] D`.
   - Exact Hodge number `t_H(M) = ∑ i, i * (dim Fil^i - dim Fil^{i+1})` and exact Newton number
     `t_N(M) = Padic.valuation (LinearMap.det φ.toLinearMap)`.
   - Weak admissibility (`IsWeaklyAdmissible`): `t_H(M) = t_N(M)` and `t_H(U) ≤ t_N(U)` for
     every `φ`-stable subspace `U ≤ D`.
   - Closure under short exact sequences (`weaklyAdmissible_sub_quot_exact`, plus subobject and
     quotient criteria), direct sums (`weaklyAdmissible_closed_under_directSum`), and duals
     (`weaklyAdmissible_closed_under_dual`).
   - Internal endomorphism module `endModule` (`End(D)`) and trace-zero adjoint `ad0Module` (`Ad⁰(D)`).

2. **2-Dimensional Crystalline Classification (`weaklyAdmissible_dim2_iff`) & Eigenforms `Δ₁₂..Δ₂₂`**:
   - Complete classification of weak admissibility for 2D filtered `φ`-modules of Hodge–Tate
     weights `{0, k - 1}` (`k ≥ 2`) and Frobenius characteristic polynomial `X² - a_p X + p^{k - 1}`:
     weakly admissible iff `‖a_p‖ ≤ 1` (i.e. `a_p ∈ ℤ_[p]`) and no slope-`< k - 1` eigenline
     coincides with the Hodge line `L` — in particular, for the canonical companion module
     `crystallineMod2D p k a_p`, `IsWeaklyAdmissible ↔ ‖a_p‖ ≤ 1`!
   - Ordinary (`‖a_p‖ = 1`, Hensel splitting into slopes `0` and `k - 1`) vs supersingular
     (`‖a_p‖ < 1`, irreducible when `k - 1` is odd and `v_p(a_p)` is large) dichotomy.
   - Direct unconditional weak admissibility verification for all five 1-dimensional eigenforms
     `Δ₁₂, Δ₁₆, Δ₁₈, Δ₂₀, Δ₂₂` at every prime `p`.

3. **Concrete Fontaine–Laffaille Modules over `ℤ_[p]` & Mazur's Theorem**:
   - `FontaineLaffailleModule p M`: finite free `ℤ_[p]`-module `M`, direct-summand filtration
     `M = Fil^0 ⊇ Fil^1 ⊇ ... ⊇ Fil^{p-1} = 0`, divided Frobenii `φ_i : Fil^i M → M` with
     `φ_i|_{Fil^{i+1}} = p · φ_{i+1}` and `∑_i im(φ_i) = M`.
   - Adapted graded basis theorem over the PID `ℤ_[p]` and automatic bijectivity of the
     associated graded Frobenius `Ψ : M ≃ₗ[ℤ_[p]] M` (`IsUnit (det Ψ)`).
   - **Mazur's / Laffaille's Theorem (`fontaineLaffaille_implies_weaklyAdmissible`)**:
     every `FontaineLaffailleModule p M` yields a weakly admissible `FilteredPhiModule p`, and
     satisfies the full Newton-above-Hodge polygon bound (`fontaineLaffaille_newton_above_hodge_polygon`)
     bridging directly into `Stage3DworkFrobenius.polygonLe_of_fredholmDet_hodge_bound` and
     `Stage2HodgeWeights.PolygonLe`.
   - Exactness of `toFilteredPhiModule` on `FontaineLaffailleSES` and explicit 2D Fontaine–Laffaille
     modules `fontaineLaffaille2D p k a_p` (`2 ≤ k ≤ p - 1`) for `Δ₁₂..Δ₂₂`.

4. **Concrete Crystalline Deformation Tangent Space `H¹_f(ℚ_p, Ad(D))` & `dim_crystalline_tangent_eq`**:
   - Bloch–Kato / Fontaine–Laffaille differential `δ_E : E → (E / Fil^0 E) × E`, `x ↦ (x̄, φ x - x)`.
   - General Bloch–Kato dimension formula:
     `dim H¹_f(E) = dim(E / Fil^0 E) + dim H⁰(E)`.
   - Concrete first-order crystalline deformation tangent-space isomorphism for regular 2D modules
     (paralleling `Stage3GaloisDeformation.mazurTangentLinearEquiv`).
   - Exact crystalline tangent dimension for every regular 2D filtered `φ`-module / Fontaine–Laffaille
     module (`0 < k - 1 < p - 1`):
     `dim H¹_f(Ad(D)) = 1 + dim H⁰(Ad(D))` and `dim H¹_f(Ad⁰(D)) = 1 + dim H⁰(Ad⁰(D))`
     (exact Taylor–Wiles local excess `dim H¹_f - dim H⁰ = 1 = [ℚ : ℚ]`), plus Schur's lemma
     (`dim H⁰(Ad⁰(D)) = 0`, `dim H¹_f(Ad⁰(D)) = 1`) for non-split Hodge lines.
-/

noncomputable section

open scoped BigOperators
open Polynomial Matrix Finset Module Submodule
open RHDirect RHDirect.Stage2HodgeWeights RHDirect.Stage3DworkFrobenius
  RHDirect.Stage8RamanujanDelta RHDirect.Stage10PeterssonHecke

namespace RHDirect
namespace Stage11CrystallineFontaine

/-! ## Section 1: Linear-Algebraic Determinant & `p`-adic Valuation Preliminaries -/

section LinearPadicPrelims

/-- Any injective endomorphism of a finite-dimensional vector space over a field is bijective,
yielding a canonical `LinearEquiv`. -/
def linearEquivOfInjectiveEndo {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] (f : V →ₗ[K] V) (hf : Function.Injective f) : V ≃ₗ[K] V :=
  LinearEquiv.ofBijective f ⟨hf, LinearMap.injective_iff_surjective.mp hf⟩

/-- The determinant of a linear equivalence over a field is nonzero. -/
theorem det_linearEquiv_ne_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (e : V ≃ₗ[K] V) : LinearMap.det e.toLinearMap ≠ 0 := by
  intro h
  have h1 : LinearMap.det (e.toLinearMap.comp e.symm.toLinearMap) = 1 := by
    have hcomp : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
      ext x; simp
    rw [hcomp, LinearMap.det_id]
  rw [LinearMap.det_comp, h, zero_mul] at h1
  exact zero_ne_one h1

/-- The determinant of `e.symm` is the inverse of the determinant of `e`. -/
theorem det_linearEquiv_symm {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (e : V ≃ₗ[K] V) :
    LinearMap.det e.symm.toLinearMap = (LinearMap.det e.toLinearMap)⁻¹ := by
  have hmul : LinearMap.det e.toLinearMap * LinearMap.det e.symm.toLinearMap = 1 := by
    rw [← LinearMap.det_comp]
    have hcomp : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
      ext x; simp
    rw [hcomp, LinearMap.det_id]
  exact eq_inv_of_mul_eq_one_right hmul

/-- Determinant is invariant under conjugation by any `LinearEquiv` `e : V ≃ₗ[K] W`. -/
theorem det_conj_linearEquiv {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    [AddCommGroup W] [Module K W] [Module.Finite K W]
    (e : V ≃ₗ[K] W) (f : V →ₗ[K] V) :
    LinearMap.det ((e.toLinearMap.comp f).comp e.symm.toLinearMap) = LinearMap.det f := by
  classical
  let b := Module.finBasis K V
  let b' := b.map e
  rw [← LinearMap.det_toMatrix b', ← LinearMap.det_toMatrix b]
  have hmat : LinearMap.toMatrix b' b' ((e.toLinearMap.comp f).comp e.symm.toLinearMap) =
      LinearMap.toMatrix b b f := by
    ext i j
    simp [b', LinearMap.toMatrix_apply]
  rw [hmat]

/-- Determinant of a dual map equals the determinant of the original endomorphism
on a finite-dimensional vector space over a field. -/
theorem det_dualMap_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] (f : V →ₗ[K] V) :
    LinearMap.det f.dualMap = LinearMap.det f := by
  classical
  let b := Module.finBasis K V
  rw [← LinearMap.det_toMatrix b.dualBasis, ← LinearMap.det_toMatrix b]
  have hmat : LinearMap.toMatrix b.dualBasis b.dualBasis f.dualMap =
      (LinearMap.toMatrix b b f)ᵀ := by
    ext i j
    rw [Matrix.transpose_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
    simp [Basis.dualBasis_repr, LinearMap.dualMap_apply]
  rw [hmat, Matrix.det_transpose]

/-- **Block-Triangular Multiplicativity of Determinants on Short Exact Sequences**:
if `0 → U →[i] V →[π] W → 0` is exact and `φ_U, φ_V, φ_W` commute with `i, π`,
then `det(φ_V) = det(φ_U) * det(φ_W)`. -/
theorem det_eq_mul_of_ses {K U V W : Type*} [Field K]
    [AddCommGroup U] [Module K U] [Module.Finite K U]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    [AddCommGroup W] [Module K W] [Module.Finite K W]
    (i : U →ₗ[K] V) (π : V →ₗ[K] W)
    (hi : Function.Injective i) (hπ : Function.Surjective π)
    (hexact : LinearMap.range i = LinearMap.ker π)
    (φU : U →ₗ[K] U) (φV : V →ₗ[K] V) (φW : W →ₗ[K] W)
    (hcommU : ∀ u : U, φV (i u) = i (φU u))
    (hcommW : ∀ v : V, π (φV v) = φW (π v)) :
    LinearMap.det φV = LinearMap.det φU * LinearMap.det φW := by
  classical
  obtain ⟨s, hs⟩ := π.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hπ)
  have hπs : ∀ w : W, π (s w) = w := fun w => LinearMap.congr_fun hs w
  let e : (U × W) ≃ₗ[K] V :=
    LinearEquiv.ofBijective
      (i.coprod s)
      (by
        constructor
        · intro ⟨u₁, w₁⟩ ⟨u₂, w₂⟩ h
          have heq : i u₁ + s w₁ = i u₂ + s w₂ := h
          have hw : w₁ = w₂ := by
            have h1 := congrArg π heq
            rw [map_add, map_add, hπs, hπs] at h1
            have hi1 : π (i u₁) = 0 := LinearMap.mem_ker.mp (hexact ▸ ⟨u₁, rfl⟩)
            have hi2 : π (i u₂) = 0 := LinearMap.mem_ker.mp (hexact ▸ ⟨u₂, rfl⟩)
            rw [hi1, hi2, zero_add, zero_add] at h1
            exact h1
          subst hw
          have hu : i u₁ = i u₂ := add_right_cancel heq
          exact Prod.ext (hi hu) rfl
        · intro v
          have hv : v - s (π v) ∈ LinearMap.ker π := by
            rw [LinearMap.mem_ker, map_sub, hπs, sub_self]
          rw [← hexact] at hv
          obtain ⟨u, hu⟩ := hv
          refine ⟨(u, π v), ?_⟩
          change i u + s (π v) = v
          rw [hu, sub_add_cancel])
  have he_inl : ∀ u : U, e (u, 0) = i u := fun u => by
    change i u + s 0 = i u
    simp
  have he_inr : ∀ w : W, e (0, w) = s w := fun w => by
    change i 0 + s w = s w
    simp
  have he_symm_i : ∀ u : U, e.symm (i u) = (u, 0) := fun u => by
    rw [← he_inl u, LinearEquiv.symm_apply_apply]
  have he_symm_snd : ∀ v : V, (e.symm v).2 = π v := fun v => by
    have hv : e (e.symm v) = v := e.apply_symm_apply v
    have h1 := congrArg π hv
    change π (i (e.symm v).1 + s (e.symm v).2) = π v at h1
    rw [map_add, hπs] at h1
    have hi0 : π (i (e.symm v).1) = 0 := LinearMap.mem_ker.mp (hexact ▸ ⟨_, rfl⟩)
    rw [hi0, zero_add] at h1
    exact h1
  let ψ : (U × W) →ₗ[K] (U × W) := (e.symm.toLinearMap.comp φV).comp e.toLinearMap
  have hdet : LinearMap.det ψ = LinearMap.det φV := by
    have := det_conj_linearEquiv e.symm φV
    simpa [ψ] using this
  rw [← hdet]
  let bU := Module.finBasis K U
  let bW := Module.finBasis K W
  let b := bU.prod bW
  rw [← LinearMap.det_toMatrix b, ← LinearMap.det_toMatrix bU, ← LinearMap.det_toMatrix bW]
  set M := LinearMap.toMatrix b b ψ
  let A : Matrix (Fin (finrank K U)) (Fin (finrank K U)) K :=
    fun r c => M (Sum.inl r) (Sum.inl c)
  let B : Matrix (Fin (finrank K U)) (Fin (finrank K W)) K :=
    fun r c => M (Sum.inl r) (Sum.inr c)
  let C : Matrix (Fin (finrank K W)) (Fin (finrank K U)) K :=
    fun r c => M (Sum.inr r) (Sum.inl c)
  let D : Matrix (Fin (finrank K W)) (Fin (finrank K W)) K :=
    fun r c => M (Sum.inr r) (Sum.inr c)
  have hM : M = Matrix.fromBlocks A B C D := by
    ext r c
    cases r <;> cases c <;> rfl
  have hA : A = LinearMap.toMatrix bU bU φU := by
    ext r c
    simp only [A, M, LinearMap.toMatrix_apply, b, Basis.prod_apply, Basis.prod_repr_inl,
      LinearMap.coe_inl, LinearMap.coe_inr, ψ, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    change (bU.repr (e.symm (φV (e (bU c, 0)))).1) r = (bU.repr (φU (bU c))) r
    rw [he_inl, hcommU, he_symm_i]
  have hC : C = 0 := by
    ext r c
    simp only [C, M, LinearMap.toMatrix_apply, Matrix.zero_apply, b, Basis.prod_apply,
      Basis.prod_repr_inr, LinearMap.coe_inl, ψ, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    change (bW.repr (e.symm (φV (e (bU c, 0)))).2) r = 0
    rw [he_inl, hcommU, he_symm_i, map_zero, Finsupp.zero_apply]
  have hD : D = LinearMap.toMatrix bW bW φW := by
    ext r c
    simp only [D, M, LinearMap.toMatrix_apply, b, Basis.prod_apply, Basis.prod_repr_inr,
      LinearMap.coe_inr, ψ, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    change (bW.repr (e.symm (φV (e (0, bW c)))).2) r = (bW.repr (φW (bW c))) r
    rw [he_symm_snd, he_inr, hcommW, hπs]
  rw [hM, hC, Matrix.det_fromBlocks_zero₂₁, hA, hD]

/-- Restriction of an invertible endomorphism `φ : V ≃ₗ[K] V` to a `φ`-stable subspace `U ≤ V`
is automatically a `LinearEquiv U ≃ₗ[K] U` (in finite dimensions). -/
def restrictEquiv {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    (φ : V ≃ₗ[K] V) (U : Submodule K V) (hU : ∀ x ∈ U, φ x ∈ U) : U ≃ₗ[K] U :=
  linearEquivOfInjectiveEndo
    (φ.toLinearMap.restrict hU)
    (fun _ _ hxy => Subtype.ext (φ.injective (congrArg Subtype.val hxy)))

@[simp] theorem restrictEquiv_apply {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] (φ : V ≃ₗ[K] V) (U : Submodule K V) (hU : ∀ x ∈ U, φ x ∈ U) (x : U) :
    (restrictEquiv φ U hU x : V) = φ x := rfl

/-- Quotient endomorphism induced by `φ : V ≃ₗ[K] V` on `V ⧸ U` for a `φ`-stable subspace `U ≤ V`. -/
def quotEquiv {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    (φ : V ≃ₗ[K] V) (U : Submodule K V) (hU : ∀ x ∈ U, φ x ∈ U) : (V ⧸ U) ≃ₗ[K] (V ⧸ U) :=
  let f : (V ⧸ U) →ₗ[K] (V ⧸ U) :=
    Submodule.mapQ U U φ.toLinearMap (fun x hx => hU x hx)
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective U q
    exact ⟨Submodule.mkQ U (φ.symm v), by simp [f]⟩
  LinearEquiv.ofBijective f ⟨LinearMap.injective_iff_surjective.mpr hsurj, hsurj⟩

@[simp] theorem quotEquiv_mkQ {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] (φ : V ≃ₗ[K] V) (U : Submodule K V) (hU : ∀ x ∈ U, φ x ∈ U) (v : V) :
    quotEquiv φ U hU (Submodule.mkQ U v) = Submodule.mkQ U (φ v) := rfl

/-- Determinant multiplicativity for a `φ`-stable subspace `U ≤ V`:
`det(φ) = det(φ|_U) * det(φ̄_{V/U})`. -/
theorem det_eq_det_restrict_mul_quot {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] (φ : V ≃ₗ[K] V) (U : Submodule K V) (hU : ∀ x ∈ U, φ x ∈ U) :
    LinearMap.det φ.toLinearMap =
      LinearMap.det (restrictEquiv φ U hU).toLinearMap *
        LinearMap.det (quotEquiv φ U hU).toLinearMap :=
  det_eq_mul_of_ses U.subtype (Submodule.mkQ U) Subtype.val_injective (Submodule.mkQ_surjective U)
    (by rw [Submodule.range_subtype, Submodule.ker_mkQ])
    (restrictEquiv φ U hU).toLinearMap φ.toLinearMap (quotEquiv φ U hU).toLinearMap
    (fun _ => rfl) (fun _ => rfl)

/-- If `U ≤ V` is `φ`-stable for `φ : V ≃ₗ[K] V` (finite-dimensional), then `U` is also
`φ⁻¹`-stable (`∀ x ∈ U, φ.symm x ∈ U`). -/
theorem phi_symm_mem_of_stable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] (φ : V ≃ₗ[K] V) (U : Submodule K V) (hU : ∀ x ∈ U, φ x ∈ U)
    {x : V} (hx : x ∈ U) : φ.symm x ∈ U := by
  let e := restrictEquiv φ U hU
  have heq : (e.symm ⟨x, hx⟩ : V) = φ.symm x := by
    apply φ.injective
    have h1 : φ (e.symm ⟨x, hx⟩ : V) = (e (e.symm ⟨x, hx⟩) : V) := rfl
    rw [h1, e.apply_symm_apply, φ.apply_symm_apply]
  rw [← heq]
  exact (e.symm ⟨x, hx⟩).2

/-- On a 2-dimensional vector space `D` over a field `K`, the determinant of `φ - λ · id` is
`λ² - tr(φ) · λ + det(φ)`. -/
theorem det_sub_smul_id_dim2 {K D : Type*} [Field K] [AddCommGroup D] [Module K D]
    [Module.Finite K D] (hdim : Module.finrank K D = 2) (φ : D →ₗ[K] D) (lam : K) :
    LinearMap.det (φ - lam • LinearMap.id) =
      lam ^ 2 - LinearMap.trace K D φ * lam + LinearMap.det φ := by
  classical
  let b : Basis (Fin 2) K D := (Module.finBasis K D).reindex (finCongr hdim)
  rw [← LinearMap.det_toMatrix b, ← LinearMap.det_toMatrix b, LinearMap.trace_eq_matrix_trace K b]
  set A := LinearMap.toMatrix b b φ
  have hsub : LinearMap.toMatrix b b (φ - lam • LinearMap.id) = A - lam • (1 : Matrix (Fin 2) (Fin 2) K) := by
    simp [A, map_sub, map_smul]
  rw [hsub, Matrix.det_fin_two, Matrix.det_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.one_apply_ne
    (by decide : (0 : Fin 2) ≠ 1), Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0),
    smul_eq_mul, mul_one, mul_zero, sub_zero]
  ring

/-! ### `p`-adic Valuation & Hensel Splitting Helpers -/

section PadicHelpers

variable {p : ℕ} [Fact p.Prime]

theorem padic_valuation_p_pow (n : ℕ) :
    Padic.valuation ((p : ℚ_[p]) ^ n) = (n : ℤ) := by
  induction n with
  | zero => simp [Padic.valuation_one]
  | succ n ih =>
    have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    rw [pow_succ, Padic.valuation_mul (pow_ne_zero n hp0) hp0, ih, Padic.valuation_p]
    push_cast
    ring

theorem padic_norm_le_one_iff_exists_padicInt (a : ℚ_[p]) :
    ‖a‖ ≤ 1 ↔ ∃ z : ℤ_[p], (z : ℚ_[p]) = a := by
  constructor
  · intro h; exact ⟨⟨a, h⟩, rfl⟩
  · rintro ⟨z, rfl⟩; exact z.2

theorem padic_valuation_nonneg_of_norm_le_one {a : ℚ_[p]} (ha : ‖a‖ ≤ 1) :
    0 ≤ Padic.valuation a := by
  by_cases h0 : a = 0
  · subst h0; simp [Padic.valuation_zero]
  · rw [Padic.norm_eq_zpow_neg_valuation h0] at ha
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have hle : (p : ℝ) ^ (-Padic.valuation a) ≤ (p : ℝ) ^ (0 : ℤ) := by simpa using ha
    have hexp := (zpow_le_zpow_iff_right₀ hp1).mp hle
    omega

theorem padic_norm_le_one_of_valuation_nonneg {a : ℚ_[p]} (hv : 0 ≤ Padic.valuation a) :
    ‖a‖ ≤ 1 := by
  by_cases h0 : a = 0
  · subst h0; simp
  · rw [Padic.norm_eq_zpow_neg_valuation h0]
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
    calc (p : ℝ) ^ (-Padic.valuation a) ≤ (p : ℝ) ^ (0 : ℤ) :=
          (zpow_le_zpow_iff_right₀ hp1).mpr (by omega)
      _ = 1 := zpow_zero _

theorem padic_norm_le_one_iff_valuation_nonneg (a : ℚ_[p]) :
    ‖a‖ ≤ 1 ↔ 0 ≤ Padic.valuation a :=
  ⟨padic_valuation_nonneg_of_norm_le_one, padic_norm_le_one_of_valuation_nonneg⟩

theorem padic_valuation_neg_of_one_lt_norm {a : ℚ_[p]} (ha : 1 < ‖a‖) :
    Padic.valuation a < 0 := by
  by_contra h
  push Not at h
  have := padic_norm_le_one_of_valuation_nonneg h
  linarith

theorem padic_valuation_padicInt_nonneg (z : ℤ_[p]) :
    0 ≤ Padic.valuation (z : ℚ_[p]) :=
  padic_valuation_nonneg_of_norm_le_one z.2

theorem padic_valuation_padicInt_unit (u : ℤ_[p]ˣ) :
    Padic.valuation ((u : ℤ_[p]) : ℚ_[p]) = 0 := by
  have h1 : 0 ≤ Padic.valuation ((u : ℤ_[p]) : ℚ_[p]) :=
    padic_valuation_padicInt_nonneg (u : ℤ_[p])
  have h2 : 0 ≤ Padic.valuation (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) :=
    padic_valuation_padicInt_nonneg ((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
  have hmul : ((u : ℤ_[p]) : ℚ_[p]) * (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) = 1 := by
    exact_mod_cast congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) u.mul_inv
  have hne1 : ((u : ℤ_[p]) : ℚ_[p]) ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hmul; exact zero_ne_one hmul
  have hne2 : (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hmul; exact zero_ne_one hmul
  have hv := congrArg Padic.valuation hmul
  rw [Padic.valuation_mul hne1 hne2, Padic.valuation_one] at hv
  omega

theorem padic_valuation_inv {a : ℚ_[p]} (ha : a ≠ 0) :
    Padic.valuation a⁻¹ = -Padic.valuation a := by
  have hmul : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  have hv := congrArg Padic.valuation hmul
  rw [Padic.valuation_mul ha (inv_ne_zero ha), Padic.valuation_one] at hv
  omega

theorem padic_norm_intCast_le_one (n : ℤ) : ‖(n : ℚ_[p])‖ ≤ 1 := by
  have h : (n : ℚ_[p]) = ((n : ℤ_[p]) : ℚ_[p]) := by simp
  rw [h]
  exact (n : ℤ_[p]).2

/-- **Universal Quadratic Hensel Splitting in `ℚ_[p]` (All Primes `p`, Including `p = 2`!)**:
For any `k ≥ 2` and any `a : ℚ_[p]` with `1 ≤ ‖a‖` (covering BOTH `‖a‖ > 1` non-integral traces
and `‖a‖ = 1` ordinary traces!), the polynomial `X² - a X + p^{k-1}` splits in `ℚ_[p]` with a
root `λ : ℚ_[p]` satisfying `‖λ‖ = ‖a‖` and `Padic.valuation λ = Padic.valuation a`! -/
theorem exists_quad_root_of_one_le_norm {k : ℕ} (hk : 2 ≤ k) {a : ℚ_[p]} (ha : 1 ≤ ‖a‖) :
    ∃ lam : ℚ_[p], lam ^ 2 - a * lam + (p : ℚ_[p]) ^ (k - 1) = 0 ∧
      ‖lam‖ = ‖a‖ ∧ Padic.valuation lam = Padic.valuation a := by
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha
    linarith
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpk_norm : ‖(p : ℚ_[p]) ^ (k - 1)‖ < 1 := by
    rw [norm_pow, Padic.norm_p]
    have hinv_lt : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp_gt1
    exact pow_lt_one₀ (inv_nonneg.mpr hp_pos.le) hinv_lt (by omega)
  have hc_norm : ‖(p : ℚ_[p]) ^ (k - 1) / a ^ 2‖ < 1 := by
    rw [norm_div]
    have ha2 : (1 : ℝ) ≤ ‖a ^ 2‖ := by rw [norm_pow]; nlinarith
    exact (div_le_self (norm_nonneg _) ha2).trans_lt hpk_norm
  let c : ℤ_[p] := ⟨(p : ℚ_[p]) ^ (k - 1) / a ^ 2, hc_norm.le⟩
  let F : Polynomial ℤ_[p] := Polynomial.X ^ 2 - Polynomial.X + Polynomial.C c
  have hF1 : F.eval 1 = c := by simp [F]
  have hF'1 : F.derivative.eval 1 = 1 := by
    have hd : F.derivative = Polynomial.C 2 * Polynomial.X - 1 := by
      simp [F, Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_pow,
        Polynomial.derivative_X, Polynomial.derivative_C]
    rw [hd]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_one]
    ring
  have haeval1 : Polynomial.aeval (1 : ℤ_[p]) F = c := by
    simpa [Polynomial.aeval_def, Polynomial.eval₂_id] using hF1
  have haeval'1 : Polynomial.aeval (1 : ℤ_[p]) F.derivative = 1 := by
    simpa [Polynomial.aeval_def, Polynomial.eval₂_id] using hF'1
  have hhensel_hyp : ‖F.eval 1‖ < ‖F.derivative.eval 1‖ ^ 2 := by
    rw [hF1, hF'1, norm_one, one_pow]
    exact hc_norm
  obtain ⟨y, hy0, hy1, _, _⟩ := hensels_lemma hhensel_hyp
  rw [haeval'1, norm_one] at hy1
  have hy_norm : ‖y‖ = 1 := by
    have hsub : ‖(1 : ℤ_[p]) - y‖ < 1 := by simpa [norm_sub_rev] using hy1
    by_contra hne
    have hy_lt : ‖y‖ < 1 := lt_of_le_of_ne y.2 hne
    have hsum : ‖y + (1 - y)‖ ≤ max ‖y‖ ‖(1 : ℤ_[p]) - y‖ :=
      IsUltrametricDist.norm_add_le_max y (1 - y)
    rw [add_sub_cancel, norm_one] at hsum
    have hmax : max ‖y‖ ‖(1 : ℤ_[p]) - y‖ < 1 := max_lt hy_lt hsub
    linarith
  have hy0_eval : F.eval y = 0 := by
    simpa [Polynomial.aeval_def, Polynomial.eval₂_id] using hy0
  have hy_val : (y : ℚ_[p]) ^ 2 - (y : ℚ_[p]) + (p : ℚ_[p]) ^ (k - 1) / a ^ 2 = 0 := by
    simp only [F, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C] at hy0_eval
    have h := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hy0_eval
    simp only [PadicInt.coe_add, PadicInt.coe_sub, PadicInt.coe_pow, PadicInt.coe_zero] at h
    exact h
  refine ⟨a * (y : ℚ_[p]), ?_, ?_, ?_⟩
  · have hmul := congrArg (fun t : ℚ_[p] => a ^ 2 * t) hy_val
    simp only [mul_zero] at hmul
    have hrew : a ^ 2 * ((y : ℚ_[p]) ^ 2 - (y : ℚ_[p]) + (p : ℚ_[p]) ^ (k - 1) / a ^ 2) =
        (a * (y : ℚ_[p])) ^ 2 - a * (a * (y : ℚ_[p])) + (p : ℚ_[p]) ^ (k - 1) := by
      field_simp [ha0]
    rwa [← hrew]
  · rw [norm_mul, show ‖(y : ℚ_[p])‖ = ‖y‖ from rfl, hy_norm, mul_one]
  · have hy0' : (y : ℚ_[p]) ≠ 0 := by
      intro hz
      have : ‖y‖ = 0 := by change ‖(y : ℚ_[p])‖ = 0; simp [hz]
      linarith
    have hy_v : Padic.valuation (y : ℚ_[p]) = 0 := by
      have hn : ‖(y : ℚ_[p])‖ = 1 := hy_norm
      rw [Padic.norm_eq_zpow_neg_valuation hy0'] at hn
      have h0 : (p : ℝ) ^ (-Padic.valuation (y : ℚ_[p])) = (p : ℝ) ^ (0 : ℤ) := by simpa using hn
      have hexp := zpow_right_injective₀ hp_pos hp_gt1.ne' h0
      omega
    rw [Padic.valuation_mul ha0 hy0', hy_v, add_zero]

/-- If `a, c : ℚ_[p]` satisfy `‖a‖ ≤ 1` and `‖c‖ ≤ 1`, then every root `λ : ℚ_[p]` of
`λ² - a λ + c = 0` is `p`-adically integral (`‖λ‖ ≤ 1`, equivalently `0 ≤ Padic.valuation λ`). -/
theorem norm_le_one_of_quad_root {a c lam : ℚ_[p]} (ha : ‖a‖ ≤ 1) (hc : ‖c‖ ≤ 1)
    (hroot : lam ^ 2 - a * lam + c = 0) : ‖lam‖ ≤ 1 := by
  by_contra hgt
  push Not at hgt
  have hsq : lam ^ 2 = a * lam - c := by linear_combination hroot
  have h1 : ‖a * lam‖ < ‖lam ^ 2‖ := by
    rw [norm_mul, norm_pow]
    have hpos : 0 < ‖lam‖ := lt_trans zero_lt_one hgt
    have hmul : ‖a‖ * ‖lam‖ ≤ 1 * ‖lam‖ := mul_le_mul_of_nonneg_right ha hpos.le
    have hlt : 1 * ‖lam‖ < ‖lam‖ * ‖lam‖ := mul_lt_mul_of_pos_right hgt hpos
    nlinarith
  have h2 : ‖c‖ < ‖lam ^ 2‖ := by
    rw [norm_pow]
    nlinarith
  have htri : ‖a * lam - c‖ ≤ max ‖a * lam‖ ‖c‖ := by
    simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max (a * lam) (-c)
  rw [← hsq] at htri
  have hmax : max ‖a * lam‖ ‖c‖ < ‖lam ^ 2‖ := max_lt h1 h2
  linarith

end PadicHelpers

end LinearPadicPrelims

/-! ## Section 2: Concrete Filtered `φ`-Modules `(D, φ, Fil•)` over `ℚ_[p]` -/

universe u

/-- **Concrete Filtered `φ`-Module over `ℚ_[p]`**:
on a finite-dimensional `ℚ_[p]`-vector space `D`, an invertible `ℚ_[p]`-linear Frobenius
`φ : D ≃ₗ[ℚ_[p]] D` together with an exhaustive, separated, decreasing filtration
`fil : Stage2HodgeWeights.HodgeFiltration ℚ_[p] D`. -/
structure FilteredPhiModule (p : ℕ) [Fact p.Prime] (D : Type u)
    [AddCommGroup D] [Module ℚ_[p] D] [Module.Finite ℚ_[p] D] where
  φ : D ≃ₗ[ℚ_[p]] D
  fil : HodgeFiltration ℚ_[p] D

namespace FilteredPhiModule

variable {p : ℕ} [Fact p.Prime]
variable {D D₁ D₂ D₃ : Type u}
  [AddCommGroup D] [Module ℚ_[p] D] [Module.Finite ℚ_[p] D]
  [AddCommGroup D₁] [Module ℚ_[p] D₁] [Module.Finite ℚ_[p] D₁]
  [AddCommGroup D₂] [Module ℚ_[p] D₂] [Module.Finite ℚ_[p] D₂]
  [AddCommGroup D₃] [Module ℚ_[p] D₃] [Module.Finite ℚ_[p] D₃]

/-- The **Hodge number** `t_H(M) := ∑ i, i * (finrank (Fil^i M) - finrank (Fil^{i+1} M)) ∈ ℤ`. -/
def tH (M : FilteredPhiModule p D) : ℤ := M.fil.tH

/-- Explicit sum formula for the Hodge number `t_H(M)` over `[botBound, topBound]`. -/
theorem tH_eq_sum (M : FilteredPhiModule p D) :
    M.tH = (Finset.Icc M.fil.botBound M.fil.topBound).sum
      (fun i => (M.fil.jump i : ℤ) * i) :=
  M.fil.tH_eq_sum_Icc le_rfl le_rfl

/-- The **Newton number** `t_N(M) := v_p(det φ) ∈ ℤ` (exact `p`-adic valuation of `det φ`). -/
def tN (M : FilteredPhiModule p D) : ℤ :=
  Padic.valuation (LinearMap.det M.φ.toLinearMap)

/-- A `ℚ_[p]`-subspace `U ≤ D` is `φ`-stable if `φ(U) ⊆ U`. -/
def IsPhiStable (M : FilteredPhiModule p D) (U : Submodule ℚ_[p] D) : Prop :=
  ∀ x ∈ U, M.φ x ∈ U

theorem top_isPhiStable (M : FilteredPhiModule p D) : M.IsPhiStable ⊤ :=
  fun _ _ => trivial

theorem bot_isPhiStable (M : FilteredPhiModule p D) : M.IsPhiStable ⊥ := by
  intro x hx
  rw [Submodule.mem_bot] at hx ⊢
  rw [hx, map_zero]

/-- Concrete sub-filtered `φ`-module `M.restrictSub U hU` on any `φ`-stable subspace `U ≤ D`,
with restricted invertible Frobenius `φ|_U` and induced filtration `Fil^i U = U ∩ Fil^i D`. -/
def restrictSub (M : FilteredPhiModule p D) (U : Submodule ℚ_[p] D) (hU : M.IsPhiStable U) :
    FilteredPhiModule p U where
  φ := restrictEquiv M.φ U hU
  fil := M.fil.inducedSub U

/-- Concrete quotient filtered `φ`-module `M.quotSub U hU` on `D ⧸ U` for any `φ`-stable
subspace `U ≤ D`, with induced Frobenius `φ̄` and quotient filtration. -/
def quotSub (M : FilteredPhiModule p D) (U : Submodule ℚ_[p] D) (hU : M.IsPhiStable U) :
    FilteredPhiModule p (D ⧸ U) where
  φ := quotEquiv M.φ U hU
  fil := M.fil.mapSurj (Submodule.mkQ U) (Submodule.mkQ_surjective U)

/-- **Fontaine Weak Admissibility**:
`t_H(M) = t_N(M)` AND for every `φ`-stable subspace `U ≤ D`, `t_H(U) ≤ t_N(U)`. -/
def IsWeaklyAdmissible (M : FilteredPhiModule p D) : Prop :=
  M.tH = M.tN ∧
    ∀ (U : Submodule ℚ_[p] D) (hU : M.IsPhiStable U),
      (M.restrictSub U hU).tH ≤ (M.restrictSub U hU).tN

theorem restrictSub_bot_tH (M : FilteredPhiModule p D) :
    (M.restrictSub ⊥ M.bot_isPhiStable).tH = 0 :=
  M.fil.inducedSub_bot_tH

theorem restrictSub_bot_tN (M : FilteredPhiModule p D) :
    (M.restrictSub ⊥ M.bot_isPhiStable).tN = 0 := by
  unfold tN restrictSub
  dsimp
  have hid : (restrictEquiv M.φ ⊥ M.bot_isPhiStable).toLinearMap = LinearMap.id :=
    Subsingleton.elim _ _
  rw [hid, LinearMap.det_id, Padic.valuation_one]

theorem restrictSub_top_tH (M : FilteredPhiModule p D) :
    (M.restrictSub ⊤ M.top_isPhiStable).tH = M.tH :=
  M.fil.inducedSub_top_tH

theorem restrictSub_top_tN (M : FilteredPhiModule p D) :
    (M.restrictSub ⊤ M.top_isPhiStable).tN = M.tN := by
  unfold tN restrictSub
  dsimp
  let e : (⊤ : Submodule ℚ_[p] D) ≃ₗ[ℚ_[p]] D := Submodule.topEquiv
  have hconj : ((e.toLinearMap.comp (restrictEquiv M.φ ⊤ M.top_isPhiStable).toLinearMap).comp
      e.symm.toLinearMap) = M.φ.toLinearMap := by
    ext x; rfl
  rw [← hconj, det_conj_linearEquiv]

theorem restrictSub_tN_congr (M : FilteredPhiModule p D) {U₁ U₂ : Submodule ℚ_[p] D}
    (h1 : M.IsPhiStable U₁) (h2 : M.IsPhiStable U₂) (heq : U₁ = U₂) :
    (M.restrictSub U₁ h1).tN = (M.restrictSub U₂ h2).tN := by
  subst heq
  rfl

/-! ### Strict Short Exact Sequences of Concrete Filtered `φ`-Modules -/

/-- A strict short exact sequence `0 → M₁ →[f] M₂ →[g] M₃ → 0` of concrete `FilteredPhiModule p`. -/
structure ExactSeq (M₁ : FilteredPhiModule p D₁) (M₂ : FilteredPhiModule p D₂)
    (M₃ : FilteredPhiModule p D₃) where
  ses : StrictFilteredSES ℚ_[p] M₁.fil M₂.fil M₃.fil
  comm_left : ∀ x : D₁, M₂.φ (ses.f x) = ses.f (M₁.φ x)
  comm_right : ∀ x : D₂, ses.g (M₂.φ x) = M₃.φ (ses.g x)

namespace ExactSeq

variable {M₁ : FilteredPhiModule p D₁} {M₂ : FilteredPhiModule p D₂}
  {M₃ : FilteredPhiModule p D₃}

theorem tH_add (E : ExactSeq M₁ M₂ M₃) : M₂.tH = M₁.tH + M₃.tH :=
  E.ses.tH_add

theorem tN_add (E : ExactSeq M₁ M₂ M₃) : M₂.tN = M₁.tN + M₃.tN := by
  unfold tN
  have hdet := det_eq_mul_of_ses E.ses.f E.ses.g E.ses.f_inj E.ses.g_surj E.ses.exact
    M₁.φ.toLinearMap M₂.φ.toLinearMap M₃.φ.toLinearMap E.comm_left E.comm_right
  rw [hdet, Padic.valuation_mul (det_linearEquiv_ne_zero M₁.φ) (det_linearEquiv_ne_zero M₃.φ)]

theorem comap_isPhiStable (E : ExactSeq M₁ M₂ M₃) {U : Submodule ℚ_[p] D₂}
    (hU : M₂.IsPhiStable U) : M₁.IsPhiStable (U.comap E.ses.f) := by
  intro x hx
  show E.ses.f (M₁.φ x) ∈ U
  rw [← E.comm_left x]
  exact hU (E.ses.f x) hx

theorem map_isPhiStable (E : ExactSeq M₁ M₂ M₃) {U : Submodule ℚ_[p] D₂}
    (hU : M₂.IsPhiStable U) : M₃.IsPhiStable (U.map E.ses.g) := by
  rintro _ ⟨v, hv, rfl⟩
  rw [← E.comm_right v]
  exact ⟨M₂.φ v, hU v hv, rfl⟩

theorem push_left_isPhiStable (E : ExactSeq M₁ M₂ M₃) {U₁ : Submodule ℚ_[p] D₁}
    (hU₁ : M₁.IsPhiStable U₁) : M₂.IsPhiStable (U₁.map E.ses.f) := by
  rintro _ ⟨u, hu, rfl⟩
  rw [E.comm_left u]
  exact ⟨M₁.φ u, hU₁ u hu, rfl⟩

theorem pull_right_isPhiStable (E : ExactSeq M₁ M₂ M₃) {U₃ : Submodule ℚ_[p] D₃}
    (hU₃ : M₃.IsPhiStable U₃) : M₂.IsPhiStable (U₃.comap E.ses.g) := by
  intro v hv
  show E.ses.g (M₂.φ v) ∈ U₃
  rw [E.comm_right v]
  exact hU₃ (E.ses.g v) hv

/-- **Exactness of Newton Numbers on Subobjects in an `ExactSeq`**:
for any `φ`-stable `U ≤ D₂`, `t_N(U) = t_N(U.comap f) + t_N(U.map g)`. -/
theorem sub_tN_add (E : ExactSeq M₁ M₂ M₃) (U : Submodule ℚ_[p] D₂) (hU : M₂.IsPhiStable U) :
    (M₂.restrictSub U hU).tN =
      (M₁.restrictSub (U.comap E.ses.f) (E.comap_isPhiStable hU)).tN +
        (M₃.restrictSub (U.map E.ses.g) (E.map_isPhiStable hU)).tN := by
  set U₁ := U.comap E.ses.f
  set U₃ := U.map E.ses.g
  let fU : U₁ →ₗ[ℚ_[p]] U :=
    { toFun := fun x => ⟨E.ses.f x.1, x.2⟩
      map_add' := fun x y => Subtype.ext (map_add E.ses.f x.1 y.1)
      map_smul' := fun c x => Subtype.ext (map_smul E.ses.f c x.1) }
  let gU : U →ₗ[ℚ_[p]] U₃ :=
    { toFun := fun y => ⟨E.ses.g y.1, ⟨y.1, y.2, rfl⟩⟩
      map_add' := fun x y => Subtype.ext (map_add E.ses.g x.1 y.1)
      map_smul' := fun c x => Subtype.ext (map_smul E.ses.g c x.1) }
  have hfU_inj : Function.Injective fU := fun x y hxy =>
    Subtype.ext (E.ses.f_inj (congrArg Subtype.val hxy))
  have hgU_surj : Function.Surjective gU := by
    rintro ⟨w, ⟨v, hv, rfl⟩⟩
    exact ⟨⟨v, hv⟩, rfl⟩
  have hexactU : LinearMap.range fU = LinearMap.ker gU := by
    ext ⟨v, hv⟩
    constructor
    · rintro ⟨⟨u, hu⟩, hEq⟩
      have hfv : E.ses.f u = v := congrArg Subtype.val hEq
      change gU ⟨v, hv⟩ = 0
      apply Subtype.ext
      change E.ses.g v = 0
      exact LinearMap.mem_ker.mp (E.ses.exact ▸ ⟨u, hfv⟩)
    · intro hker
      have hgv : E.ses.g v = 0 := congrArg Subtype.val hker
      obtain ⟨u, hu⟩ := E.ses.exact.symm ▸ (LinearMap.mem_ker.mpr hgv)
      exact ⟨⟨u, by show E.ses.f u ∈ U; rwa [hu]⟩, Subtype.ext hu⟩
  unfold tN restrictSub
  dsimp
  have hdet := det_eq_mul_of_ses fU gU hfU_inj hgU_surj hexactU
    (restrictEquiv M₁.φ U₁ (E.comap_isPhiStable hU)).toLinearMap
    (restrictEquiv M₂.φ U hU).toLinearMap
    (restrictEquiv M₃.φ U₃ (E.map_isPhiStable hU)).toLinearMap
    (fun x => Subtype.ext (E.comm_left x.1))
    (fun y => Subtype.ext (E.comm_right y.1))
  rw [hdet, Padic.valuation_mul (det_linearEquiv_ne_zero _) (det_linearEquiv_ne_zero _)]

/-- **Fontaine's Extension Theorem (`weaklyAdmissible_sub_quot_exact`)**:
if `0 → M₁ → M₂ → M₃ → 0` is a strict short exact sequence of concrete `FilteredPhiModule p`
with `M₁` and `M₃` weakly admissible, then `M₂` is weakly admissible! -/
theorem weaklyAdmissible_sub_quot_exact (E : ExactSeq M₁ M₂ M₃)
    (h₁ : M₁.IsWeaklyAdmissible) (h₃ : M₃.IsWeaklyAdmissible) :
    M₂.IsWeaklyAdmissible := by
  refine ⟨by rw [E.tH_add, E.tN_add, h₁.1, h₃.1], ?_⟩
  intro U hU
  set U₁ := U.comap E.ses.f
  set U₃ := U.map E.ses.g
  let fU : U₁ →ₗ[ℚ_[p]] U :=
    { toFun := fun x => ⟨E.ses.f x.1, x.2⟩
      map_add' := fun x y => Subtype.ext (map_add E.ses.f x.1 y.1)
      map_smul' := fun c x => Subtype.ext (map_smul E.ses.f c x.1) }
  let gU : U →ₗ[ℚ_[p]] U₃ :=
    { toFun := fun y => ⟨E.ses.g y.1, ⟨y.1, y.2, rfl⟩⟩
      map_add' := fun x y => Subtype.ext (map_add E.ses.g x.1 y.1)
      map_smul' := fun c x => Subtype.ext (map_smul E.ses.g c x.1) }
  have hfU_inj : Function.Injective fU := fun x y hxy =>
    Subtype.ext (E.ses.f_inj (congrArg Subtype.val hxy))
  have hgU_surj : Function.Surjective gU := by
    rintro ⟨w, ⟨v, hv, rfl⟩⟩
    exact ⟨⟨v, hv⟩, rfl⟩
  have hexactU : LinearMap.range fU = LinearMap.ker gU := by
    ext ⟨v, hv⟩
    constructor
    · rintro ⟨⟨u, hu⟩, hEq⟩
      have hfv : E.ses.f u = v := congrArg Subtype.val hEq
      change gU ⟨v, hv⟩ = 0
      apply Subtype.ext
      change E.ses.g v = 0
      exact LinearMap.mem_ker.mp (E.ses.exact ▸ ⟨u, hfv⟩)
    · intro hker
      have hgv : E.ses.g v = 0 := congrArg Subtype.val hker
      obtain ⟨u, hu⟩ := E.ses.exact.symm ▸ (LinearMap.mem_ker.mpr hgv)
      exact ⟨⟨u, by show E.ses.f u ∈ U; rwa [hu]⟩, Subtype.ext hu⟩
  let Fquot : HodgeFiltration ℚ_[p] U₃ := (M₂.fil.inducedSub U).mapSurj gU hgU_surj
  let sesU : StrictFilteredSES ℚ_[p] (M₁.fil.inducedSub U₁) (M₂.fil.inducedSub U) Fquot :=
    { f := fU
      g := gU
      f_inj := hfU_inj
      g_surj := hgU_surj
      exact := hexactU
      strict_sub := fun i => by
        ext ⟨u, hu⟩
        simp [HodgeFiltration.inducedSub, E.ses.strict_sub i, fU]
      strict_quot := fun _ => rfl }
  have htH_eq : (M₂.restrictSub U hU).tH =
      (M₁.restrictSub U₁ (E.comap_isPhiStable hU)).tH + Fquot.tH := sesU.tH_add
  have hquot_le : ∀ i : ℤ, Fquot.fil i ≤ (M₃.fil.inducedSub U₃).fil i := by
    intro i w hw
    rcases hw with ⟨⟨v, _⟩, hvfil, rfl⟩
    show E.ses.g v ∈ M₃.fil.fil i
    rw [E.ses.strict_quot i]
    exact ⟨v, hvfil, rfl⟩
  have htH_quot_le : Fquot.tH ≤ (M₃.restrictSub U₃ (E.map_isPhiStable hU)).tH :=
    HodgeFiltration.tH_le_of_fil_le hquot_le
  have hN_eq := E.sub_tN_add U hU
  have h1U := h₁.2 U₁ (E.comap_isPhiStable hU)
  have h3U := h₃.2 U₃ (E.map_isPhiStable hU)
  linarith

/-- Subobject criterion: if `M₂` is weakly admissible in an `ExactSeq` and `M₁.tH = M₁.tN`,
then `M₁` is weakly admissible. -/
theorem weaklyAdmissible_left (E : ExactSeq M₁ M₂ M₃)
    (h₂ : M₂.IsWeaklyAdmissible) (hEq₁ : M₁.tH = M₁.tN) :
    M₁.IsWeaklyAdmissible := by
  refine ⟨hEq₁, ?_⟩
  intro U₁ hU₁
  set U := U₁.map E.ses.f
  have hU := E.push_left_isPhiStable hU₁
  have hcomap : U.comap E.ses.f = U₁ := Submodule.comap_map_eq_of_injective E.ses.f_inj U₁
  have hmap_bot : U.map E.ses.g = ⊥ := by
    ext w
    simp only [Submodule.mem_map, Submodule.mem_bot]
    constructor
    · rintro ⟨v, ⟨u, _, rfl⟩, rfl⟩
      exact LinearMap.mem_ker.mp (E.ses.exact ▸ ⟨u, rfl⟩)
    · rintro rfl
      exact ⟨0, U.zero_mem, map_zero E.ses.g⟩
  let fR : U₁ →ₗ[ℚ_[p]] D₂ := E.ses.f.domRestrict U₁
  have hfR_inj : Function.Injective fR := fun x y hxy => Subtype.ext (E.ses.f_inj hxy)
  have hrange_fR : LinearMap.range fR = U := by
    ext v
    exact ⟨by rintro ⟨⟨u, hu⟩, rfl⟩; exact ⟨u, hu, rfl⟩,
      by rintro ⟨u, hu, rfl⟩; exact ⟨⟨u, hu⟩, rfl⟩⟩
  have hfil_eq : ∀ i : ℤ, (M₁.fil.inducedSub U₁).fil i = (M₂.fil.comapInj fR hfR_inj).fil i := by
    intro i; ext ⟨u, hu⟩
    simp [HodgeFiltration.inducedSub, HodgeFiltration.comapInj, E.ses.strict_sub i, fR]
  have htH_eq : (M₁.restrictSub U₁ hU₁).tH = (M₂.restrictSub U hU).tH := by
    change (M₁.fil.inducedSub U₁).tH = (M₂.fil.inducedSub U).tH
    have h1 := HodgeFiltration.tH_le_of_fil_le (fun i => le_of_eq (hfil_eq i))
    have h2 := HodgeFiltration.tH_le_of_fil_le (fun i => le_of_eq (hfil_eq i).symm)
    rw [le_antisymm h1 h2, M₂.fil.comapInj_tH_eq_inducedSub_range fR hfR_inj, hrange_fR]
  have hN_eq : (M₂.restrictSub U hU).tN = (M₁.restrictSub U₁ hU₁).tN := by
    rw [E.sub_tN_add U hU,
      M₁.restrictSub_tN_congr (E.comap_isPhiStable hU) hU₁ hcomap,
      M₃.restrictSub_tN_congr (E.map_isPhiStable hU) M₃.bot_isPhiStable hmap_bot,
      M₃.restrictSub_bot_tN, add_zero]
  rw [htH_eq, ← hN_eq]
  exact h₂.2 U hU

end ExactSeq

/-! ### Direct Sum of Filtered `φ`-Modules & Closure of Weak Admissibility -/

/-- Direct sum `M₁ ⊕ M₂` of two concrete filtered `φ`-modules over `ℚ_[p]`. -/
def directSum (M₁ : FilteredPhiModule p D₁) (M₂ : FilteredPhiModule p D₂) :
    FilteredPhiModule p (D₁ × D₂) where
  φ := M₁.φ.prodCongr M₂.φ
  fil :=
    { fil := fun i => (M₁.fil.fil i).prod (M₂.fil.fil i)
      antitone := fun _ _ hij => Submodule.prod_mono (M₁.fil.antitone hij) (M₂.fil.antitone hij)
      botBound := min M₁.fil.botBound M₂.fil.botBound
      topBound := max M₁.fil.topBound M₂.fil.topBound
      bot_le_top := le_trans (min_le_left _ _) (le_trans M₁.fil.bot_le_top (le_max_left _ _))
      eq_top_of_le := fun i hi => by
        rw [M₁.fil.eq_top_of_le i (le_trans hi (min_le_left _ _)),
          M₂.fil.eq_top_of_le i (le_trans hi (min_le_right _ _)), Submodule.prod_top]
      eq_bot_of_gt := fun i hi => by
        rw [M₁.fil.eq_bot_of_gt i (lt_of_le_of_lt (le_max_left _ _) hi),
          M₂.fil.eq_bot_of_gt i (lt_of_le_of_lt (le_max_right _ _) hi), Submodule.prod_bot] }

/-- Canonical split exact sequence `0 → M₁ → M₁ ⊕ M₂ → M₂ → 0`. -/
def directSumExactSeq (M₁ : FilteredPhiModule p D₁) (M₂ : FilteredPhiModule p D₂) :
    ExactSeq M₁ (directSum M₁ M₂) M₂ where
  ses :=
    { f := LinearMap.inl ℚ_[p] D₁ D₂
      g := LinearMap.snd ℚ_[p] D₁ D₂
      f_inj := fun _ _ h => congrArg Prod.fst h
      g_surj := fun y => ⟨(0, y), rfl⟩
      exact := by
        ext ⟨x, y⟩
        simp [LinearMap.mem_range, LinearMap.mem_ker, eq_comm]
      strict_sub := fun i => by
        ext x
        simp [directSum]
      strict_quot := fun i => by
        ext y
        simp only [directSum, Submodule.mem_map, Submodule.mem_prod, LinearMap.snd_apply]
        exact ⟨fun hy => ⟨(0, y), ⟨(M₁.fil.fil i).zero_mem, hy⟩, rfl⟩,
          by rintro ⟨⟨_, _⟩, ⟨_, hy⟩, rfl⟩; exact hy⟩ }
  comm_left x := by
    change (M₁.φ x, M₂.φ 0) = (M₁.φ x, 0)
    simp
  comm_right _ := rfl

theorem directSum_tH (M₁ : FilteredPhiModule p D₁) (M₂ : FilteredPhiModule p D₂) :
    (directSum M₁ M₂).tH = M₁.tH + M₂.tH :=
  (directSumExactSeq M₁ M₂).tH_add

theorem directSum_tN (M₁ : FilteredPhiModule p D₁) (M₂ : FilteredPhiModule p D₂) :
    (directSum M₁ M₂).tN = M₁.tN + M₂.tN :=
  (directSumExactSeq M₁ M₂).tN_add

/-- **Closure of Weak Admissibility under Direct Sums**:
if `M₁` and `M₂` are weakly admissible, then `M₁ ⊕ M₂` is weakly admissible! -/
theorem weaklyAdmissible_closed_under_directSum {M₁ : FilteredPhiModule p D₁}
    {M₂ : FilteredPhiModule p D₂}
    (h₁ : M₁.IsWeaklyAdmissible) (h₂ : M₂.IsWeaklyAdmissible) :
    (directSum M₁ M₂).IsWeaklyAdmissible :=
  (directSumExactSeq M₁ M₂).weaklyAdmissible_sub_quot_exact h₁ h₂

/-! ### Dual Filtered `φ`-Module `D*` & Closure of Weak Admissibility -/

/-- The annihilator of a subspace `U ≤ V` inside `Module.Dual K V`:
`U^⊥ = { f : V →ₗ[K] K | ∀ x ∈ U, f x = 0 }`. -/
def dualAnnihilator {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (U : Submodule K V) : Submodule K (Module.Dual K V) where
  carrier := { f | ∀ x ∈ U, f x = 0 }
  add_mem' hf hg x hx := by simp [hf x hx, hg x hx]
  zero_mem' _ _ := rfl
  smul_mem' c f hf x hx := by simp [hf x hx]

/-- The pre-annihilator of a subspace `W ≤ Module.Dual K V` inside `V`:
`^⊥ W = { x ∈ V | ∀ f ∈ W, f x = 0 }`. -/
def preAnnihilator {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (W : Submodule K (Module.Dual K V)) : Submodule K V where
  carrier := { x | ∀ f ∈ W, f x = 0 }
  add_mem' hx hy f hf := by simp [hx f hf, hy f hf]
  zero_mem' f _ := map_zero f
  smul_mem' c x hx f hf := by simp [hx f hf]

theorem finrank_dualAnnihilator {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] (U : Submodule K V) :
    Module.finrank K (dualAnnihilator U) + Module.finrank K U = Module.finrank K V := by
  let res : Module.Dual K V →ₗ[K] Module.Dual K U := U.subtype.dualMap
  have hker : LinearMap.ker res = dualAnnihilator U := by
    ext f
    change res f = 0 ↔ ∀ x ∈ U, f x = 0
    constructor
    · intro h x hx
      have := LinearMap.congr_fun h ⟨x, hx⟩
      simpa [res, LinearMap.dualMap_apply] using this
    · intro h
      ext ⟨x, hx⟩
      simpa [res, LinearMap.dualMap_apply] using h x hx
  have hsurj : Function.Surjective res := by
    intro g
    obtain ⟨C, hC⟩ := U.exists_isCompl
    let proj : V →ₗ[K] U := Submodule.projectionOnto U C hC
    refine ⟨g.comp proj, ?_⟩
    ext ⟨x, hx⟩
    change g (proj x) = g ⟨x, hx⟩
    rw [Submodule.projectionOnto_apply_left hC ⟨x, hx⟩]
  have hrank := LinearMap.finrank_range_add_finrank_ker res
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker, Subspace.dual_finrank_eq,
    Subspace.dual_finrank_eq] at hrank
  omega

/-- Dual Hodge filtration `Fil^i(D*) = (Fil^{1 - i} D)^⊥`. -/
def dualFiltration {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    (F : HodgeFiltration K V) : HodgeFiltration K (Module.Dual K V) where
  fil i := dualAnnihilator (F.fil (1 - i))
  antitone i j hij f hf x hx := hf x (F.antitone (by omega) hx)
  botBound := -F.topBound
  topBound := -F.botBound
  bot_le_top := by linarith [F.bot_le_top]
  eq_top_of_le i hi := by
    ext f
    change (∀ x ∈ F.fil (1 - i), f x = 0) ↔ True
    refine iff_true_intro fun x hx => ?_
    rw [F.eq_bot_of_gt (1 - i) (by omega), Submodule.mem_bot] at hx
    rw [hx, map_zero]
  eq_bot_of_gt i hi := by
    ext f
    change (∀ x ∈ F.fil (1 - i), f x = 0) ↔ f = 0
    constructor
    · intro hf
      ext x
      exact hf x (by rw [F.eq_top_of_le (1 - i) (by omega)]; trivial)
    · rintro rfl _ _; rfl

theorem dualFiltration_jump {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] (F : HodgeFiltration K V) (i : ℤ) :
    (dualFiltration F).jump i = F.jump (-i) := by
  have h1 := finrank_dualAnnihilator (F.fil (1 - i))
  have h2 := finrank_dualAnnihilator (F.fil (1 - (i + 1)))
  have heq1 : (1 - (i + 1) : ℤ) = -i := by omega
  have heq2 : (1 - i : ℤ) = -i + 1 := by omega
  rw [heq1] at h2
  rw [heq2] at h1
  change Module.finrank K (dualAnnihilator (F.fil (1 - i))) -
      Module.finrank K (dualAnnihilator (F.fil (1 - (i + 1)))) =
    Module.finrank K (F.fil (-i)) - Module.finrank K (F.fil (-i + 1))
  rw [heq1, heq2]
  omega

theorem dualFiltration_tH {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] (F : HodgeFiltration K V) :
    (dualFiltration F).tH = -F.tH := by
  rw [(dualFiltration F).tH_eq_sum_Icc le_rfl le_rfl, F.tH_eq_sum_Icc le_rfl le_rfl]
  change (Finset.Icc (-F.topBound) (-F.botBound)).sum
      (fun i => ((dualFiltration F).jump i : ℤ) * i) =
    -(Finset.Icc F.botBound F.topBound).sum (fun i => (F.jump i : ℤ) * i)
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_nbij' (fun i => -i) (fun j => -j) ?_ ?_ ?_ ?_ ?_
  · intro i hi; rw [Finset.mem_Icc] at hi ⊢; omega
  · intro j hj; rw [Finset.mem_Icc] at hj ⊢; omega
  · intro i _; omega
  · intro j _; omega
  · intro i _
    rw [dualFiltration_jump]
    ring

/-- **Dual Filtered `φ`-Module `M*`** over `ℚ_[p]`:
underlying space `Module.Dual ℚ_[p] D`, contragredient Frobenius `φ*(f) = f ∘ φ⁻¹`,
and dual filtration `Fil^i(D*) = (Fil^{1 - i} D)^⊥`. -/
def dual (M : FilteredPhiModule p D) : FilteredPhiModule p (Module.Dual ℚ_[p] D) where
  φ :=
    { toFun := M.φ.symm.toLinearMap.dualMap
      invFun := M.φ.toLinearMap.dualMap
      map_add' := map_add _
      map_smul' := map_smul _
      left_inv := fun f => by ext x; simp [LinearMap.dualMap_apply]
      right_inv := fun f => by ext x; simp [LinearMap.dualMap_apply] }
  fil := dualFiltration M.fil

theorem dual_tH (M : FilteredPhiModule p D) : (dual M).tH = -M.tH :=
  dualFiltration_tH M.fil

theorem dual_tN (M : FilteredPhiModule p D) : (dual M).tN = -M.tN := by
  unfold tN dual
  dsimp
  change Padic.valuation (LinearMap.det M.φ.symm.toLinearMap.dualMap) =
    -Padic.valuation (LinearMap.det M.φ.toLinearMap)
  rw [det_dualMap_eq, det_linearEquiv_symm, padic_valuation_inv (det_linearEquiv_ne_zero M.φ)]

/-- **Closure of Weak Admissibility under Duals (`weaklyAdmissible_closed_under_dual`)**:
if `M` is weakly admissible, then its dual `M*` is weakly admissible! -/
theorem weaklyAdmissible_closed_under_dual {M : FilteredPhiModule p D}
    (hM : M.IsWeaklyAdmissible) : (dual M).IsWeaklyAdmissible := by
  refine ⟨by rw [dual_tH, dual_tN, hM.1], ?_⟩
  intro W hW
  set U : Submodule ℚ_[p] D := preAnnihilator W
  have hU_stab : M.IsPhiStable U := by
    intro x hx f hf
    have hinv : (dual M).φ.symm f ∈ W := phi_symm_mem_of_stable (dual M).φ W hW hf
    exact hx ((dual M).φ.symm f) hinv
  let ψLin : W →ₗ[ℚ_[p]] Module.Dual ℚ_[p] (D ⧸ U) :=
    { toFun := fun f => Submodule.liftQ U f.1 (fun x hx => hx f.1 f.2)
      map_add' := fun f g => by ext x; rfl
      map_smul' := fun c f => by ext x; rfl }
  have hψ_inj : Function.Injective ψLin := by
    intro f g hfg
    apply Subtype.ext
    ext x
    have h := LinearMap.congr_fun hfg (Submodule.mkQ U x)
    exact h
  have hdim_pre : Module.finrank ℚ_[p] U + Module.finrank ℚ_[p] W = Module.finrank ℚ_[p] D := by
    let ev : D →ₗ[ℚ_[p]] Module.Dual ℚ_[p] W :=
      { toFun := fun x =>
          { toFun := fun f => f.1 x
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
        map_add' := fun x y => by ext f; exact map_add f.1 x y
        map_smul' := fun c x => by ext f; exact map_smul f.1 c x }
    have hker_ev : LinearMap.ker ev = U := by
      ext x
      change ev x = 0 ↔ ∀ f ∈ W, f x = 0
      constructor
      · intro h f hf; exact LinearMap.congr_fun h ⟨f, hf⟩
      · intro h; ext ⟨f, hf⟩; exact h f hf
    have hsurj_ev : Function.Surjective ev := by
      let evTop := Module.evalEquiv ℚ_[p] D
      intro g
      obtain ⟨C, hC⟩ := W.exists_isCompl
      let gExt : Module.Dual ℚ_[p] (Module.Dual ℚ_[p] D) :=
        g.comp (Submodule.projectionOnto W C hC)
      refine ⟨evTop.symm gExt, ?_⟩
      ext ⟨f, hf⟩
      change f (evTop.symm gExt) = g ⟨f, hf⟩
      have h1 : (evTop (evTop.symm gExt)) f = gExt f := by rw [evTop.apply_symm_apply]
      have h2 : (evTop (evTop.symm gExt)) f = f (evTop.symm gExt) := rfl
      rw [← h2, h1]
      change g (Submodule.projectionOnto W C hC f) = g ⟨f, hf⟩
      rw [Submodule.projectionOnto_apply_left hC ⟨f, hf⟩]
    have hrank := LinearMap.finrank_range_add_finrank_ker ev
    rw [LinearMap.range_eq_top.mpr hsurj_ev, finrank_top, hker_ev, Subspace.dual_finrank_eq] at hrank
    omega
  have hdim_quot := Submodule.finrank_quotient_add_finrank U
  have hdim_eq : Module.finrank ℚ_[p] W = Module.finrank ℚ_[p] (Module.Dual ℚ_[p] (D ⧸ U)) := by
    rw [Subspace.dual_finrank_eq]
    omega
  let ψ : W ≃ₗ[ℚ_[p]] Module.Dual ℚ_[p] (D ⧸ U) :=
    LinearEquiv.ofBijective ψLin
      ⟨hψ_inj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim_eq).mp hψ_inj⟩
  have hψ_phi :
      ((ψ.toLinearMap.comp ((dual M).restrictSub W hW).φ.toLinearMap).comp ψ.symm.toLinearMap) =
        (dual (M.quotSub U hU_stab)).φ.toLinearMap := by
    apply LinearMap.ext
    intro g
    obtain ⟨f, rfl⟩ := ψ.surjective g
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply]
    ext x
    change f.1 (M.φ.symm x) =
      (Submodule.liftQ U f.1 (fun z hz => hz f.1 f.2))
        ((quotEquiv M.φ U hU_stab).symm (Submodule.mkQ U x))
    have hq_symm : (quotEquiv M.φ U hU_stab).symm (Submodule.mkQ U x) =
        Submodule.mkQ U (M.φ.symm x) := by
      apply (quotEquiv M.φ U hU_stab).injective
      rw [LinearEquiv.apply_symm_apply]
      change Submodule.mkQ U x = Submodule.mkQ U (M.φ (M.φ.symm x))
      rw [M.φ.apply_symm_apply]
    rw [hq_symm]
    rfl
  have htN_W : ((dual M).restrictSub W hW).tN = (dual (M.quotSub U hU_stab)).tN := by
    unfold tN
    rw [← hψ_phi, det_conj_linearEquiv]
  have hfil_strict : ∀ i : ℤ,
      (((dual M).restrictSub W hW).fil.fil i) =
        ((dual (M.quotSub U hU_stab)).fil.fil i).comap ψ.toLinearMap := by
    intro i
    ext f
    change (∀ x ∈ M.fil.fil (1 - i), f.1 x = 0) ↔
      (∀ q ∈ (M.fil.fil (1 - i)).map (Submodule.mkQ U), (ψ f) q = 0)
    constructor
    · intro hf q hq
      rcases hq with ⟨x, hx, rfl⟩
      exact hf x hx
    · intro hf x hx
      exact hf (Submodule.mkQ U x) ⟨x, hx, rfl⟩
  have htH_W : ((dual M).restrictSub W hW).tH = (dual (M.quotSub U hU_stab)).tH := by
    have h1 := HodgeFiltration.tH_le_of_fil_le (F₁ := ((dual M).restrictSub W hW).fil)
      (F₂ := (dual (M.quotSub U hU_stab)).fil.comapInj ψ.toLinearMap ψ.injective)
      (fun i => le_of_eq (hfil_strict i))
    have h2 := HodgeFiltration.tH_le_of_fil_le (F₂ := ((dual M).restrictSub W hW).fil)
      (F₁ := (dual (M.quotSub U hU_stab)).fil.comapInj ψ.toLinearMap ψ.injective)
      (fun i => le_of_eq (hfil_strict i).symm)
    have hrange : LinearMap.range ψ.toLinearMap = ⊤ := LinearMap.range_eq_top.mpr ψ.surjective
    change ((dual M).restrictSub W hW).fil.tH = (dual (M.quotSub U hU_stab)).fil.tH
    rw [le_antisymm h1 h2, HodgeFiltration.comapInj_tH_eq_inducedSub_range, hrange,
      HodgeFiltration.inducedSub_top_tH]
  let Esub : ExactSeq (M.restrictSub U hU_stab) M (M.quotSub U hU_stab) :=
    { ses :=
        { f := U.subtype
          g := Submodule.mkQ U
          f_inj := Subtype.val_injective
          g_surj := Submodule.mkQ_surjective U
          exact := by rw [Submodule.range_subtype, Submodule.ker_mkQ]
          strict_sub := fun _ => rfl
          strict_quot := fun _ => rfl }
      comm_left := fun _ => rfl
      comm_right := fun _ => rfl }
  have hH_add := Esub.tH_add
  have hN_add := Esub.tN_add
  rw [htH_W, htN_W, dual_tH, dual_tN]
  have hU_le := hM.2 U hU_stab
  linarith [hM.1]

/-! ### Internal Endomorphism `End(D)` & Trace-Zero Adjoint `Ad⁰(D)` Filtered `φ`-Modules -/

/-- Internal endomorphism filtration on `D →ₗ[K] D`:
`Fil^i (End D) = { f | ∀ j, ∀ x ∈ Fil^j D, f x ∈ Fil^{j + i} D }`. -/
def endFiltration {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    (F : HodgeFiltration K V) : HodgeFiltration K (V →ₗ[K] V) where
  fil i :=
    { carrier := { f | ∀ j : ℤ, ∀ x ∈ F.fil j, f x ∈ F.fil (j + i) }
      add_mem' := fun hf hg j x hx => (F.fil (j + i)).add_mem (hf j x hx) (hg j x hx)
      zero_mem' := fun j _ _ => (F.fil (j + i)).zero_mem
      smul_mem' := fun c f hf j x hx => (F.fil (j + i)).smul_mem c (hf j x hx) }
  antitone i₁ i₂ hle f hf j x hx := F.antitone (by omega) (hf j x hx)
  botBound := F.botBound - F.topBound - 1
  topBound := F.topBound - F.botBound + 1
  bot_le_top := by linarith [F.bot_le_top]
  eq_top_of_le i hi := by
    ext f
    change (∀ j : ℤ, ∀ x ∈ F.fil j, f x ∈ F.fil (j + i)) ↔ True
    refine iff_true_intro fun j x hx => ?_
    by_cases hj : F.topBound < j
    · rw [F.eq_bot_of_gt j hj, Submodule.mem_bot] at hx
      rw [hx, map_zero]
      exact (F.fil (j + i)).zero_mem
    · rw [F.eq_top_of_le (j + i) (by omega)]
      trivial
  eq_bot_of_gt i hi := by
    ext f
    change (∀ j : ℤ, ∀ x ∈ F.fil j, f x ∈ F.fil (j + i)) ↔ f = 0
    constructor
    · intro hf
      ext x
      have hx : x ∈ F.fil F.botBound := by rw [F.eq_top_of_le F.botBound le_rfl]; trivial
      have hfx := hf F.botBound x hx
      rw [F.eq_bot_of_gt (F.botBound + i) (by omega), Submodule.mem_bot] at hfx
      exact hfx
    · rintro rfl j _ _; exact (F.fil (j + i)).zero_mem

/-- **Internal Endomorphism Filtered `φ`-Module `End(M)`** (`Ad(ρ)`):
underlying space `D →ₗ[ℚ_[p]] D`, conjugation Frobenius `φ_End(f) = φ ∘ f ∘ φ⁻¹`,
and internal Hom filtration `Fil^i(End M) = { f | ∀ j, f(Fil^j M) ⊆ Fil^{j + i} M }`. -/
def endModule (M : FilteredPhiModule p D) : FilteredPhiModule p (D →ₗ[ℚ_[p]] D) where
  φ :=
    { toFun := fun f => (M.φ.toLinearMap.comp f).comp M.φ.symm.toLinearMap
      invFun := fun f => (M.φ.symm.toLinearMap.comp f).comp M.φ.toLinearMap
      map_add' := fun f g => by ext x; simp
      map_smul' := fun c f => by ext x; simp
      left_inv := fun f => by ext x; simp
      right_inv := fun f => by ext x; simp }
  fil := endFiltration M.fil

/-- Trace-zero submodule `Ad⁰(D) = { f ∈ End(D) | tr(f) = 0 }`. -/
def ad0Submodule (p : ℕ) [Fact p.Prime] (D : Type u)
    [AddCommGroup D] [Module ℚ_[p] D] [Module.Finite ℚ_[p] D] :
    Submodule ℚ_[p] (D →ₗ[ℚ_[p]] D) :=
  LinearMap.ker (LinearMap.trace ℚ_[p] D)

theorem ad0Submodule_isPhiStable (M : FilteredPhiModule p D) :
    (endModule M).IsPhiStable (ad0Submodule p D) := by
  intro f hf
  rw [ad0Submodule, LinearMap.mem_ker] at hf ⊢
  change LinearMap.trace ℚ_[p] D (M.φ.toLinearMap * f * M.φ.symm.toLinearMap) = 0
  rw [LinearMap.trace_mul_cycle]
  have hcomp : M.φ.symm.toLinearMap * M.φ.toLinearMap = 1 := by ext x; simp
  rw [hcomp, one_mul]
  exact hf

/-- **Trace-Zero Adjoint Filtered `φ`-Module `Ad⁰(M)`**:
the `φ`-stable filtered submodule `ker(tr) ≤ End(M)`. -/
def ad0Module (M : FilteredPhiModule p D) : FilteredPhiModule p (ad0Submodule p D) :=
  (endModule M).restrictSub (ad0Submodule p D) (ad0Submodule_isPhiStable M)

end FilteredPhiModule

/-! ## Section 3: 2-Dimensional Crystalline Classification (`weaklyAdmissible_dim2_iff`) & `Δ₁₂..Δ₂₂` -/

section Dim2Classification

variable {p : ℕ} [Fact p.Prime]
variable {D : Type u} [AddCommGroup D] [Module ℚ_[p] D] [Module.Finite ℚ_[p] D]

/-- A 2-dimensional filtered `φ`-module `M` has **regular crystalline weights `{0, k - 1}`**
(`k ≥ 2`) with Hodge line `L ≤ D` (`dim L = 1`) when `Fil^i D = ⊤` (`i ≤ 0`), `L` (`1 ≤ i ≤ k - 1`),
and `⊥` (`i ≥ k`). -/
structure IsRegularDim2 (M : FilteredPhiModule p D) (k : ℕ) (L : Submodule ℚ_[p] D) : Prop where
  hk : 2 ≤ k
  hdim : Module.finrank ℚ_[p] D = 2
  hL_dim : Module.finrank ℚ_[p] L = 1
  hfil : ∀ i : ℤ, M.fil.fil i = if i ≤ 0 then ⊤ else if i ≤ (k - 1 : ℤ) then L else ⊥

theorem IsRegularDim2.tH_eq {M : FilteredPhiModule p D} {k : ℕ} {L : Submodule ℚ_[p] D}
    (h : IsRegularDim2 M k L) : M.tH = (k - 1 : ℤ) := by
  have hk := h.hk
  have hdimAt : ∀ i : ℤ, M.fil.dimAt i =
      if i ≤ 0 then 2 else if i ≤ (k - 1 : ℤ) then 1 else 0 := by
    intro i
    unfold HodgeFiltration.dimAt
    have hfi := h.hfil i
    by_cases h0 : i ≤ 0
    · rw [if_pos h0] at hfi ⊢
      rw [hfi, finrank_top, h.hdim]
    · rw [if_neg h0] at hfi ⊢
      by_cases hle : i ≤ (k - 1 : ℤ)
      · rw [if_pos hle] at hfi ⊢
        rw [hfi, h.hL_dim]
      · rw [if_neg hle] at hfi ⊢
        rw [hfi, finrank_bot]
  have hjump : ∀ i : ℤ, M.fil.jump i =
      if i = 0 then 1 else if i = (k - 1 : ℤ) then 1 else 0 := by
    intro i
    unfold HodgeFiltration.jump
    rw [hdimAt i, hdimAt (i + 1)]
    split_ifs <;> omega
  set a := min (0 : ℤ) M.fil.botBound
  set b := max ((k - 1 : ℤ)) M.fil.topBound
  change M.fil.tH = (k - 1 : ℤ)
  rw [M.fil.tH_eq_sum_Icc (min_le_right _ _) (le_max_right _ _)]
  have hmem : (k - 1 : ℤ) ∈ Finset.Icc a b := by
    rw [Finset.mem_Icc]
    have : a ≤ 0 := min_le_left _ _
    have : (k - 1 : ℤ) ≤ b := le_max_left _ _
    omega
  rw [Finset.sum_eq_single (k - 1 : ℤ)]
  · rw [hjump (k - 1 : ℤ), if_neg (by omega), if_pos rfl]
    simp
  · intro i _ hne
    rw [hjump i]
    by_cases h0 : i = 0
    · subst h0; simp
    · rw [if_neg h0, if_neg hne]; simp
  · intro hnot; exact absurd hmem hnot

/-- Hodge number of any 1-dimensional subspace `U ≤ D` in a regular 2D module `M` of weights
`{0, k - 1}`: equals `k - 1` if `U = L` and `0` if `U ≠ L`. -/
theorem IsRegularDim2.sub_tH_of_finrank_one {M : FilteredPhiModule p D} {k : ℕ}
    {L : Submodule ℚ_[p] D} (h : IsRegularDim2 M k L)
    {U : Submodule ℚ_[p] D} (hU_dim : Module.finrank ℚ_[p] U = 1) :
    (M.fil.inducedSub U).tH = if U = L then (k - 1 : ℤ) else 0 := by
  have hk := h.hk
  have hdimAt : ∀ i : ℤ, (M.fil.inducedSub U).dimAt i =
      if i ≤ 0 then 1 else if i ≤ (k - 1 : ℤ) then (if U = L then 1 else 0) else 0 := by
    intro i
    change Module.finrank ℚ_[p] ((M.fil.fil i).comap U.subtype) = _
    have hfi := h.hfil i
    by_cases h0 : i ≤ 0
    · rw [if_pos h0] at hfi ⊢
      have hcom : (M.fil.fil i).comap U.subtype = ⊤ := by rw [hfi]; simp
      rw [hcom, finrank_top, hU_dim]
    · rw [if_neg h0] at hfi ⊢
      by_cases hle : i ≤ (k - 1 : ℤ)
      · rw [if_pos hle] at hfi ⊢
        by_cases hUL : U = L
        · rw [if_pos hUL]
          have hcom : (M.fil.fil i).comap U.subtype = ⊤ := by
            rw [hfi, ← hUL]; ext ⟨x, hx⟩; simp
          rw [hcom, finrank_top, hU_dim]
        · rw [if_neg hUL]
          have hbot : (M.fil.fil i).comap U.subtype = ⊥ := by
            rw [hfi]
            by_contra hne
            have hpos : 0 < Module.finrank ℚ_[p] (L.comap U.subtype) := by
              by_contra h0'; push Not at h0'
              exact hne (Submodule.finrank_eq_zero.mp (Nat.eq_zero_of_le_zero h0'))
            have hleU : Module.finrank ℚ_[p] (L.comap U.subtype) ≤ 1 := by
              simpa [hU_dim] using Submodule.finrank_le (L.comap U.subtype)
            have htop : L.comap U.subtype = ⊤ :=
              Submodule.eq_top_of_finrank_eq (by rw [hU_dim]; omega)
            have hsub : U ≤ L := fun x hx => by
              have : (⟨x, hx⟩ : U) ∈ L.comap U.subtype := by rw [htop]; trivial
              exact this
            exact hUL (Submodule.eq_of_le_of_finrank_eq hsub (by rw [hU_dim, h.hL_dim]))
          rw [hbot, finrank_bot]
      · rw [if_neg hle] at hfi ⊢
        have hbot : (M.fil.fil i).comap U.subtype = ⊥ := by rw [hfi]; ext x; simp
        rw [hbot, finrank_bot]
  set a := min (0 : ℤ) (M.fil.inducedSub U).botBound
  set b := max ((k - 1 : ℤ)) (M.fil.inducedSub U).topBound
  rw [(M.fil.inducedSub U).tH_eq_sum_Icc (min_le_right _ _) (le_max_right _ _)]
  by_cases hUL : U = L
  · rw [if_pos hUL]
    have hmem : (k - 1 : ℤ) ∈ Finset.Icc a b := by
      rw [Finset.mem_Icc]
      have : a ≤ 0 := min_le_left _ _
      have : (k - 1 : ℤ) ≤ b := le_max_left _ _
      omega
    rw [Finset.sum_eq_single (k - 1 : ℤ)]
    · unfold HodgeFiltration.jump
      rw [hdimAt (k - 1 : ℤ), hdimAt ((k - 1 : ℤ) + 1)]
      rw [if_neg (by omega), if_pos le_rfl, if_pos hUL, if_neg (by omega), if_neg (by omega)]
      simp
    · intro i _ hne
      unfold HodgeFiltration.jump
      rw [hdimAt i, hdimAt (i + 1)]
      split_ifs <;> simp_all <;> omega
    · intro hnot; exact absurd hmem hnot
  · rw [if_neg hUL]
    refine Finset.sum_eq_zero fun i _ => ?_
    unfold HodgeFiltration.jump
    rw [hdimAt i, hdimAt (i + 1)]
    split_ifs <;> simp_all <;> omega

/-- On a 1-dimensional `φ`-stable subspace `U ≤ D`, `φ|_U` is scalar multiplication by an
eigenvalue `λ : ℚ_[p]`, and `t_N(U) = Padic.valuation λ`. -/
theorem exists_eigenvalue_of_finrank_one {M : FilteredPhiModule p D}
    {U : Submodule ℚ_[p] D} (hU : M.IsPhiStable U) (hU_dim : Module.finrank ℚ_[p] U = 1) :
    ∃ lam : ℚ_[p], (∀ x ∈ U, M.φ x = lam • x) ∧ (M.restrictSub U hU).tN = Padic.valuation lam := by
  classical
  let b : Basis (Fin 1) ℚ_[p] U := (Module.finBasis ℚ_[p] U).reindex (finCongr hU_dim)
  let e := restrictEquiv M.φ U hU
  let lam : ℚ_[p] := b.repr (e (b 0)) 0
  have he_smul : e.toLinearMap = lam • LinearMap.id := by
    apply b.ext
    intro i
    fin_cases i
    have hsum := (b.sum_repr (e (b 0))).symm
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton] at hsum
    simpa [lam] using hsum
  refine ⟨lam, fun x hx => ?_, ?_⟩
  · have := LinearMap.congr_fun he_smul ⟨x, hx⟩
    exact congrArg Subtype.val this
  · unfold FilteredPhiModule.tN FilteredPhiModule.restrictSub
    dsimp
    rw [he_smul, LinearMap.det_smul, LinearMap.det_id, mul_one, hU_dim, pow_one]

/-- Every eigenvalue `λ` of a 2D endomorphism `φ` satisfies `λ² - tr(φ) λ + det(φ) = 0`. -/
theorem eigenvalue_satisfies_charpoly_dim2 {M : FilteredPhiModule p D}
    (hdim : Module.finrank ℚ_[p] D = 2) {U : Submodule ℚ_[p] D}
    (hU_dim : Module.finrank ℚ_[p] U = 1) {lam : ℚ_[p]}
    (heig : ∀ x ∈ U, M.φ x = lam • x) :
    lam ^ 2 - LinearMap.trace ℚ_[p] D M.φ.toLinearMap * lam + LinearMap.det M.φ.toLinearMap = 0 := by
  rw [← det_sub_smul_id_dim2 hdim M.φ.toLinearMap lam]
  let g : D →ₗ[ℚ_[p]] D := M.φ.toLinearMap - lam • (LinearMap.id : D →ₗ[ℚ_[p]] D)
  have hgU : ∀ x ∈ U, g x = 0 := fun x hx => by
    change M.φ x - lam • x = 0
    rw [heig x hx, sub_self]
  have hstab : ∀ x ∈ U, g x ∈ U := fun x hx => by rw [hgU x hx]; exact U.zero_mem
  let gQ : (D ⧸ U) →ₗ[ℚ_[p]] (D ⧸ U) := Submodule.mapQ U U g hstab
  have hdet_mul := det_eq_mul_of_ses U.subtype (Submodule.mkQ U) Subtype.val_injective
    (Submodule.mkQ_surjective U) (by rw [Submodule.range_subtype, Submodule.ker_mkQ])
    (0 : U →ₗ[ℚ_[p]] U) g gQ
    (fun x => by change g x.1 = 0; exact hgU x.1 x.2)
    (fun _ => rfl)
  have hdet0 : LinearMap.det (0 : U →ₗ[ℚ_[p]] U) = 0 := by
    have h0 : (0 : U →ₗ[ℚ_[p]] U) = (0 : ℚ_[p]) • (LinearMap.id : U →ₗ[ℚ_[p]] U) := by simp
    rw [h0, LinearMap.det_smul, LinearMap.det_id, mul_one, hU_dim, pow_one]
  rw [hdet_mul, hdet0, zero_mul]

/-- Conversely, every root `λ ∈ ℚ_[p]` of `λ² - tr(φ) λ + det(φ) = 0` on a 2D `FilteredPhiModule p`
yields a 1-dimensional `φ`-stable eigenspace `U ≤ D` with `t_N(U) = Padic.valuation λ`. -/
theorem exists_phiStable_line_of_charpoly_root {M : FilteredPhiModule p D}
    (hdim : Module.finrank ℚ_[p] D = 2) {lam : ℚ_[p]}
    (hroot : lam ^ 2 - LinearMap.trace ℚ_[p] D M.φ.toLinearMap * lam +
      LinearMap.det M.φ.toLinearMap = 0) :
    ∃ (U : Submodule ℚ_[p] D) (hU : M.IsPhiStable U),
      Module.finrank ℚ_[p] U = 1 ∧ (∀ x ∈ U, M.φ x = lam • x) ∧
        (M.restrictSub U hU).tN = Padic.valuation lam := by
  let g : D →ₗ[ℚ_[p]] D := M.φ.toLinearMap - lam • (LinearMap.id : D →ₗ[ℚ_[p]] D)
  have hdet0 : LinearMap.det g = 0 := by
    rw [det_sub_smul_id_dim2 hdim, hroot]
  have hnot_inj : ¬ Function.Injective g := by
    intro hinj
    exact det_linearEquiv_ne_zero (linearEquivOfInjectiveEndo g hinj) hdet0
  have hker_ne : LinearMap.ker g ≠ ⊥ := fun hbot =>
    hnot_inj (LinearMap.ker_eq_bot.mp hbot)
  obtain ⟨v, hv_ker, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
  have hφv : M.φ v = lam • v := by
    rw [LinearMap.mem_ker] at hv_ker
    change M.φ v - lam • v = 0 at hv_ker
    exact sub_eq_zero.mp hv_ker
  let U : Submodule ℚ_[p] D := Submodule.span ℚ_[p] {v}
  have hU_dim : Module.finrank ℚ_[p] U = 1 := finrank_span_singleton hv0
  have hU_eig : ∀ x ∈ U, M.φ x = lam • x := by
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [map_smul, hφv, smul_comm]
  have hU_stab : M.IsPhiStable U := by
    intro x hx
    rw [hU_eig x hx]
    exact U.smul_mem lam hx
  obtain ⟨lam', hlam'_eig, hlam'_tN⟩ := exists_eigenvalue_of_finrank_one hU_stab hU_dim
  have hv_mem : v ∈ U := Submodule.subset_span (Set.mem_singleton v)
  have hlam_eq : lam' = lam := by
    have h1 := hlam'_eig v hv_mem
    rw [hφv] at h1
    exact smul_left_injective ℚ_[p] hv0 h1.symm
  rw [hlam_eq] at hlam'_tN
  exact ⟨U, hU_stab, hU_dim, hU_eig, hlam'_tN⟩

/-- **2-Dimensional Crystalline Weak Admissibility Classification (`weaklyAdmissible_dim2_iff`)**:
For ANY 2D filtered `φ`-module `M` over `ℚ_[p]` with Hodge–Tate weights `{0, k - 1}` (`k ≥ 2`,
Hodge line `L`) and Frobenius characteristic polynomial `X² - a_p X + p^{k - 1}`
(i.e. `tr(φ) = a_p`, `det(φ) = p^{k - 1}`):
`M` is weakly admissible **IF AND ONLY IF** `‖a_p‖ ≤ 1` (i.e. `a_p ∈ ℤ_[p]`) AND
if `L` is `φ`-stable with eigenvalue `λ`, then `(k - 1 : ℤ) ≤ Padic.valuation λ`! -/
theorem weaklyAdmissible_dim2_iff {M : FilteredPhiModule p D} {k : ℕ}
    {L : Submodule ℚ_[p] D} (hreg : IsRegularDim2 M k L) {a_p : ℚ_[p]}
    (htr : LinearMap.trace ℚ_[p] D M.φ.toLinearMap = a_p)
    (hdet : LinearMap.det M.φ.toLinearMap = (p : ℚ_[p]) ^ (k - 1)) :
    M.IsWeaklyAdmissible ↔
      ‖a_p‖ ≤ 1 ∧ (∀ lam : ℚ_[p], (∀ x ∈ L, M.φ x = lam • x) → (k - 1 : ℤ) ≤ Padic.valuation lam) := by
  have hk := hreg.hk
  have htH : M.tH = (k - 1 : ℤ) := hreg.tH_eq
  have htN : M.tN = (k - 1 : ℤ) := by
    unfold FilteredPhiModule.tN
    rw [hdet, padic_valuation_p_pow]
    omega
  constructor
  · intro hwa
    refine ⟨?_, ?_⟩
    · by_contra hgt
      push Not at hgt
      obtain ⟨lam, hroot, _, hval⟩ := exists_quad_root_of_one_le_norm hk hgt.le
      have hroot' : lam ^ 2 - LinearMap.trace ℚ_[p] D M.φ.toLinearMap * lam +
          LinearMap.det M.φ.toLinearMap = 0 := by rw [htr, hdet]; exact hroot
      obtain ⟨U, hU_stab, hU_dim, _, htN_U⟩ :=
        exists_phiStable_line_of_charpoly_root hreg.hdim hroot'
      have htH_U : (M.restrictSub U hU_stab).tH = if U = L then (k - 1 : ℤ) else 0 :=
        hreg.sub_tH_of_finrank_one hU_dim
      have hU_ad := hwa.2 U hU_stab
      have hval_neg : Padic.valuation lam < 0 := by
        rw [hval]
        exact padic_valuation_neg_of_one_lt_norm hgt
      rw [htH_U, htN_U] at hU_ad
      split_ifs at hU_ad <;> omega
    · intro lam heig
      have hL_stab : M.IsPhiStable L := fun x hx => by rw [heig x hx]; exact L.smul_mem lam hx
      have hL_ad := hwa.2 L hL_stab
      have htH_L : (M.restrictSub L hL_stab).tH = (k - 1 : ℤ) := by
        change (M.fil.inducedSub L).tH = (k - 1 : ℤ)
        rw [hreg.sub_tH_of_finrank_one hreg.hL_dim, if_pos rfl]
      obtain ⟨lam', heig', htN_L⟩ := exists_eigenvalue_of_finrank_one hL_stab hreg.hL_dim
      have hLdim := hreg.hL_dim
      have hL_ne : L ≠ ⊥ := fun h0 => by rw [h0, finrank_bot] at hLdim; omega
      obtain ⟨v, hvL, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL_ne
      have hlam_eq : lam' = lam := by
        have h1 := heig' v hvL
        rw [heig v hvL] at h1
        exact smul_left_injective ℚ_[p] hv0 h1.symm
      rw [htH_L, htN_L, hlam_eq] at hL_ad
      exact hL_ad
  · rintro ⟨ha, hL_cond⟩
    refine ⟨by rw [htH, htN], ?_⟩
    intro U hU_stab
    have hle2 : Module.finrank ℚ_[p] U ≤ 2 := by
      simpa [hreg.hdim] using Submodule.finrank_le U
    by_cases h0 : Module.finrank ℚ_[p] U = 0
    · have hbot : U = ⊥ := Submodule.finrank_eq_zero.mp h0
      subst hbot
      rw [M.restrictSub_bot_tH, M.restrictSub_bot_tN]
    · by_cases h2 : Module.finrank ℚ_[p] U = 2
      · have htop : U = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [h2, hreg.hdim])
        subst htop
        rw [M.restrictSub_top_tH, M.restrictSub_top_tN, htH, htN]
      · have h1 : Module.finrank ℚ_[p] U = 1 := by omega
        obtain ⟨lam, heig, htN_U⟩ := exists_eigenvalue_of_finrank_one hU_stab h1
        have htH_U : (M.restrictSub U hU_stab).tH = if U = L then (k - 1 : ℤ) else 0 :=
          hreg.sub_tH_of_finrank_one h1
        rw [htH_U, htN_U]
        split_ifs with hUL
        · subst hUL
          exact hL_cond lam heig
        · have hroot := eigenvalue_satisfies_charpoly_dim2 hreg.hdim h1 heig
          rw [htr, hdet] at hroot
          have hpk_le : ‖(p : ℚ_[p]) ^ (k - 1)‖ ≤ 1 := by
            rw [norm_pow, Padic.norm_p]
            have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
            have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
            exact pow_le_one₀ (inv_nonneg.mpr hp_pos.le) (inv_lt_one_of_one_lt₀ hp_gt1).le
          exact padic_valuation_nonneg_of_norm_le_one (norm_le_one_of_quad_root ha hpk_le hroot)

/-- **Non-Split 2D Weak Admissibility Equivalence**:
when the Hodge line `L` is NOT `φ`-stable, `M.IsWeaklyAdmissible ↔ ‖a_p‖ ≤ 1`
(equivalently `0 ≤ Padic.valuation a_p`, equivalently `a_p ∈ ℤ_[p]`)! -/
theorem weaklyAdmissible_dim2_iff_of_not_phiStable {M : FilteredPhiModule p D} {k : ℕ}
    {L : Submodule ℚ_[p] D} (hreg : IsRegularDim2 M k L) {a_p : ℚ_[p]}
    (htr : LinearMap.trace ℚ_[p] D M.φ.toLinearMap = a_p)
    (hdet : LinearMap.det M.φ.toLinearMap = (p : ℚ_[p]) ^ (k - 1))
    (hL_not : ¬ M.IsPhiStable L) :
    M.IsWeaklyAdmissible ↔ ‖a_p‖ ≤ 1 := by
  rw [weaklyAdmissible_dim2_iff hreg htr hdet]
  constructor
  · exact fun h => h.1
  · intro ha
    refine ⟨ha, fun lam heig => ?_⟩
    exact absurd (fun x hx => by rw [heig x hx]; exact L.smul_mem lam hx) hL_not

/-- **Ordinary vs Supersingular 2D Splitting Dichotomy**:
1. **Ordinary (`‖a_p‖ = 1`, i.e., `a_p ≠ 0` and `v_p(a_p) = 0`)**: `M` admits TWO distinct
   `φ`-stable lines of Newton slopes `0` (unit root) and `k - 1`!
2. **Supersingular (`‖a_p‖ < 1`)**: every `ℚ_[p]`-eigenvalue `λ` of `φ` satisfies
   `0 < v_p(λ) < k - 1`, so `L` can NEVER be `φ`-stable in a weakly admissible module! -/
theorem dim2_ordinary_vs_supersingular {M : FilteredPhiModule p D} {k : ℕ}
    {L : Submodule ℚ_[p] D} (hreg : IsRegularDim2 M k L) {a_p : ℚ_[p]}
    (htr : LinearMap.trace ℚ_[p] D M.φ.toLinearMap = a_p)
    (hdet : LinearMap.det M.φ.toLinearMap = (p : ℚ_[p]) ^ (k - 1)) :
    (‖a_p‖ = 1 →
      ∃ (U₀ U₁ : Submodule ℚ_[p] D) (h₀ : M.IsPhiStable U₀) (h₁ : M.IsPhiStable U₁),
        Module.finrank ℚ_[p] U₀ = 1 ∧ Module.finrank ℚ_[p] U₁ = 1 ∧ U₀ ≠ U₁ ∧
        (M.restrictSub U₀ h₀).tN = 0 ∧ (M.restrictSub U₁ h₁).tN = (k - 1 : ℤ)) ∧
    (‖a_p‖ < 1 →
      ∀ (U : Submodule ℚ_[p] D) (hU : M.IsPhiStable U), Module.finrank ℚ_[p] U = 1 →
        0 < (M.restrictSub U hU).tN ∧ (M.restrictSub U hU).tN < (k - 1 : ℤ)) := by
  have hk := hreg.hk
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  constructor
  · intro ha1
    obtain ⟨α, hα_root, hα_norm, hα_val⟩ := exists_quad_root_of_one_le_norm hk ha1.ge
    have hα_val0 : Padic.valuation α = 0 := by
      have ha0 : a_p ≠ 0 := by intro h; rw [h, norm_zero] at ha1; linarith
      rw [hα_val]
      rw [Padic.norm_eq_zpow_neg_valuation ha0] at ha1
      have h0 : (p : ℝ) ^ (-Padic.valuation a_p) = (p : ℝ) ^ (0 : ℤ) := by simpa using ha1
      have hexp := zpow_right_injective₀ hp_pos hp_gt1.ne' h0
      omega
    have hα0 : α ≠ 0 := by intro h; rw [h, norm_zero] at hα_norm; linarith
    let β : ℚ_[p] := (p : ℚ_[p]) ^ (k - 1) / α
    have hβ_root : β ^ 2 - a_p * β + (p : ℚ_[p]) ^ (k - 1) = 0 := by
      have hsum : α + β = a_p := by
        have h1 : α ^ 2 + (p : ℚ_[p]) ^ (k - 1) = a_p * α := by linear_combination hα_root
        dsimp [β]
        field_simp [hα0]
        linear_combination h1
      have hprod : α * β = (p : ℚ_[p]) ^ (k - 1) := by dsimp [β]; field_simp [hα0]
      rw [← hsum, ← hprod]
      ring
    have hβ_val : Padic.valuation β = (k - 1 : ℤ) := by
      dsimp [β]
      rw [div_eq_mul_inv, Padic.valuation_mul (pow_ne_zero _ hp0) (inv_ne_zero hα0),
        padic_valuation_p_pow, padic_valuation_inv hα0, hα_val0]
      omega
    obtain ⟨U₀, h₀, hdim₀, heig₀, htN₀⟩ := exists_phiStable_line_of_charpoly_root hreg.hdim
      (by rw [htr, hdet]; exact hα_root)
    obtain ⟨U₁, h₁, hdim₁, heig₁, htN₁⟩ := exists_phiStable_line_of_charpoly_root hreg.hdim
      (by rw [htr, hdet]; exact hβ_root)
    have hne : U₀ ≠ U₁ := by
      intro heq
      subst heq
      have ht : Padic.valuation α = Padic.valuation β := htN₀.symm.trans htN₁
      rw [hα_val0, hβ_val] at ht
      omega
    exact ⟨U₀, U₁, h₀, h₁, hdim₀, hdim₁, hne, by rw [htN₀, hα_val0], by rw [htN₁, hβ_val]⟩
  · intro ha_lt U hU hU_dim
    obtain ⟨lam, heig, htN_U⟩ := exists_eigenvalue_of_finrank_one hU hU_dim
    have hroot := eigenvalue_satisfies_charpoly_dim2 hreg.hdim hU_dim heig
    rw [htr, hdet] at hroot
    have hlam0 : lam ≠ 0 := by
      intro h0
      rw [h0] at hroot
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_self,
        zero_add] at hroot
      exact pow_ne_zero (k - 1) hp0 hroot
    have hpk_norm : ‖(p : ℚ_[p]) ^ (k - 1)‖ < 1 := by
      rw [norm_pow, Padic.norm_p]
      exact pow_lt_one₀ (inv_nonneg.mpr hp_pos.le) (inv_lt_one_of_one_lt₀ hp_gt1) (by omega)
    have hlam_lt1 : ‖lam‖ < 1 := by
      have hle := norm_le_one_of_quad_root ha_lt.le hpk_norm.le hroot
      by_contra hge
      push Not at hge
      have hlam1 : ‖lam‖ = 1 := le_antisymm hle hge
      have hsq : lam ^ 2 = a_p * lam - (p : ℚ_[p]) ^ (k - 1) := by linear_combination hroot
      have htri : ‖a_p * lam - (p : ℚ_[p]) ^ (k - 1)‖ ≤ max ‖a_p * lam‖ ‖(p : ℚ_[p]) ^ (k - 1)‖ := by
        simpa [sub_eq_add_neg, norm_neg] using
          IsUltrametricDist.norm_add_le_max (a_p * lam) (-((p : ℚ_[p]) ^ (k - 1)))
      rw [← hsq, norm_pow, hlam1, one_pow, norm_mul, hlam1, mul_one] at htri
      have hmax : max ‖a_p‖ ‖(p : ℚ_[p]) ^ (k - 1)‖ < 1 := max_lt ha_lt hpk_norm
      linarith
    have hv_pos : 0 < Padic.valuation lam := by
      rw [Padic.norm_eq_zpow_neg_valuation hlam0] at hlam_lt1
      have hlt : (p : ℝ) ^ (-Padic.valuation lam) < (p : ℝ) ^ (0 : ℤ) := by simpa using hlam_lt1
      have hexp := (zpow_lt_zpow_iff_right₀ hp_gt1).mp hlt
      omega
    let mu : ℚ_[p] := (p : ℚ_[p]) ^ (k - 1) / lam
    have hmu_root : mu ^ 2 - a_p * mu + (p : ℚ_[p]) ^ (k - 1) = 0 := by
      have hsum : lam + mu = a_p := by
        have h1 : lam ^ 2 + (p : ℚ_[p]) ^ (k - 1) = a_p * lam := by linear_combination hroot
        dsimp [mu]; field_simp [hlam0]; linear_combination h1
      have hprod : lam * mu = (p : ℚ_[p]) ^ (k - 1) := by dsimp [mu]; field_simp [hlam0]
      rw [← hsum, ← hprod]
      ring
    have hmu0 : mu ≠ 0 := div_ne_zero (pow_ne_zero _ hp0) hlam0
    have hmu_lt1 : ‖mu‖ < 1 := by
      have hle := norm_le_one_of_quad_root ha_lt.le hpk_norm.le hmu_root
      by_contra hge
      push Not at hge
      have hmu1 : ‖mu‖ = 1 := le_antisymm hle hge
      have hsq : mu ^ 2 = a_p * mu - (p : ℚ_[p]) ^ (k - 1) := by linear_combination hmu_root
      have htri : ‖a_p * mu - (p : ℚ_[p]) ^ (k - 1)‖ ≤ max ‖a_p * mu‖ ‖(p : ℚ_[p]) ^ (k - 1)‖ := by
        simpa [sub_eq_add_neg, norm_neg] using
          IsUltrametricDist.norm_add_le_max (a_p * mu) (-((p : ℚ_[p]) ^ (k - 1)))
      rw [← hsq, norm_pow, hmu1, one_pow, norm_mul, hmu1, mul_one] at htri
      have hmax : max ‖a_p‖ ‖(p : ℚ_[p]) ^ (k - 1)‖ < 1 := max_lt ha_lt hpk_norm
      linarith
    have hv_mu_pos : 0 < Padic.valuation mu := by
      rw [Padic.norm_eq_zpow_neg_valuation hmu0] at hmu_lt1
      have hlt : (p : ℝ) ^ (-Padic.valuation mu) < (p : ℝ) ^ (0 : ℤ) := by simpa using hmu_lt1
      have hexp := (zpow_lt_zpow_iff_right₀ hp_gt1).mp hlt
      omega
    have hv_sum : Padic.valuation lam + Padic.valuation mu = (k - 1 : ℤ) := by
      have hprod : lam * mu = (p : ℚ_[p]) ^ (k - 1) := by dsimp [mu]; field_simp [hlam0]
      have hv := congrArg Padic.valuation hprod
      rw [Padic.valuation_mul hlam0 hmu0, padic_valuation_p_pow] at hv
      omega
    rw [htN_U]
    omega

/-! ### Canonical 2D Crystalline Module `crystallineMod2D` & Verification for `Δ₁₂..Δ₂₂` -/

/-- Canonical Frobenius matrix `[[0, -1], [p^{k-1}, a_p]]` of characteristic polynomial
`X² - a_p X + p^{k-1}` over `ℚ_[p]`. -/
def crystallineMat2D (p : ℕ) [Fact p.Prime] (k : ℕ) (a_p : ℚ_[p]) :
    Matrix (Fin 2) (Fin 2) ℚ_[p] :=
  !![0, -1; (p : ℚ_[p]) ^ (k - 1), a_p]

theorem crystallineMat2D_trace (p : ℕ) [Fact p.Prime] (k : ℕ) (a_p : ℚ_[p]) :
    Matrix.trace (crystallineMat2D p k a_p) = a_p := by
  simp [crystallineMat2D, Matrix.trace_fin_two]

theorem crystallineMat2D_det (p : ℕ) [Fact p.Prime] (k : ℕ) (a_p : ℚ_[p]) :
    Matrix.det (crystallineMat2D p k a_p) = (p : ℚ_[p]) ^ (k - 1) := by
  simp [crystallineMat2D, Matrix.det_fin_two]

/-- The standard Hodge line `L₀ = span {e₀} ≤ (Fin 2 → ℚ_[p])`. -/
def stdHodgeLine (p : ℕ) [Fact p.Prime] : Submodule ℚ_[p] (Fin 2 → ℚ_[p]) :=
  Submodule.span ℚ_[p] {Pi.single (0 : Fin 2) (1 : ℚ_[p])}

theorem stdHodgeLine_finrank (p : ℕ) [Fact p.Prime] :
    Module.finrank ℚ_[p] (stdHodgeLine p) = 1 := by
  refine finrank_span_singleton ?_
  intro h
  have := congrFun h 0
  simp at this

/-- **Canonical 2D Crystalline Filtered `φ`-Module `crystallineMod2D p k a_p`** of weight `k ≥ 2`
and Frobenius trace `a_p ∈ ℚ_[p]`:
- Frobenius matrix `[[0, -1], [p^{k-1}, a_p]]` (trace `a_p`, determinant `p^{k-1}`),
- Hodge filtration `Fil^i = ⊤` (`i ≤ 0`), `span {e₀}` (`1 ≤ i ≤ k - 1`), `⊥` (`i ≥ k`). -/
def crystallineMod2D (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 2 ≤ k) (a_p : ℚ_[p]) :
    FilteredPhiModule p (Fin 2 → ℚ_[p]) where
  φ :=
    let A := crystallineMat2D p k a_p
    have hdet_unit : IsUnit A.det := by
      rw [crystallineMat2D_det]
      exact Ne.isUnit (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))
    { toLinearMap := Matrix.toLin' A
      invFun := Matrix.toLin' A⁻¹
      left_inv := fun v => by
        change A⁻¹.mulVec (A.mulVec v) = v
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hdet_unit, Matrix.one_mulVec]
      right_inv := fun v => by
        change A.mulVec (A⁻¹.mulVec v) = v
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdet_unit, Matrix.one_mulVec] }
  fil :=
    { fil := fun i => if i ≤ 0 then ⊤ else if i ≤ (k - 1 : ℤ) then stdHodgeLine p else ⊥
      antitone := fun i j hij => by
        split_ifs <;> simp_all <;> omega
      botBound := 0
      topBound := (k - 1 : ℤ)
      bot_le_top := by omega
      eq_top_of_le := fun i hi => by simp [hi]
      eq_bot_of_gt := fun i hi => by
        rw [if_neg (by omega), if_neg (by omega)] }

theorem crystallineMod2D_isRegularDim2 (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 2 ≤ k)
    (a_p : ℚ_[p]) :
    IsRegularDim2 (crystallineMod2D p k hk a_p) k (stdHodgeLine p) where
  hk := hk
  hdim := by simp
  hL_dim := stdHodgeLine_finrank p
  hfil _ := rfl

theorem crystallineMod2D_trace (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 2 ≤ k) (a_p : ℚ_[p]) :
    LinearMap.trace ℚ_[p] (Fin 2 → ℚ_[p]) (crystallineMod2D p k hk a_p).φ.toLinearMap = a_p := by
  change LinearMap.trace ℚ_[p] (Fin 2 → ℚ_[p]) (Matrix.toLin' (crystallineMat2D p k a_p)) = a_p
  rw [LinearMap.trace_eq_matrix_trace ℚ_[p] (Pi.basisFun ℚ_[p] (Fin 2)), Matrix.trace_fin_two]
  simp [crystallineMat2D, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem crystallineMod2D_det (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 2 ≤ k) (a_p : ℚ_[p]) :
    LinearMap.det (crystallineMod2D p k hk a_p).φ.toLinearMap = (p : ℚ_[p]) ^ (k - 1) := by
  change LinearMap.det (Matrix.toLin' (crystallineMat2D p k a_p)) = (p : ℚ_[p]) ^ (k - 1)
  rw [LinearMap.det_toLin', crystallineMat2D_det]

theorem crystallineMod2D_not_phiStable_stdHodgeLine (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 2 ≤ k)
    (a_p : ℚ_[p]) :
    ¬ (crystallineMod2D p k hk a_p).IsPhiStable (stdHodgeLine p) := by
  intro hstab
  have he0 : Pi.single (0 : Fin 2) (1 : ℚ_[p]) ∈ stdHodgeLine p :=
    Submodule.subset_span (Set.mem_singleton _)
  have hmem := hstab _ he0
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have h1 := congrFun hc 1
  simp only [Pi.smul_apply, Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0), smul_zero] at h1
  have hφ1 : ((crystallineMod2D p k hk a_p).φ (Pi.single (0 : Fin 2) (1 : ℚ_[p]))) 1 =
      (p : ℚ_[p]) ^ (k - 1) := by
    change (crystallineMat2D p k a_p).mulVec (Pi.single 0 1) 1 = (p : ℚ_[p]) ^ (k - 1)
    simp [crystallineMat2D, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hφ1] at h1
  exact pow_ne_zero (k - 1) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) h1.symm

/-- **Exact Weak Admissibility Equivalence for `crystallineMod2D`**:
`crystallineMod2D p k a_p` is weakly admissible **iff** `‖a_p‖ ≤ 1` (`a_p ∈ ℤ_[p]`)! -/
theorem crystallineMod2D_weaklyAdmissible_iff (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 2 ≤ k)
    (a_p : ℚ_[p]) :
    (crystallineMod2D p k hk a_p).IsWeaklyAdmissible ↔ ‖a_p‖ ≤ 1 :=
  weaklyAdmissible_dim2_iff_of_not_phiStable
    (crystallineMod2D_isRegularDim2 p k hk a_p)
    (crystallineMod2D_trace p k hk a_p)
    (crystallineMod2D_det p k hk a_p)
    (crystallineMod2D_not_phiStable_stdHodgeLine p k hk a_p)

/-- **Unconditional Weak Admissibility for Every Integral Weight-`k` Eigenform**:
for EVERY prime `p`, EVERY weight `k ≥ 2`, and EVERY integer Hecke eigenvalue `a : ℤ`,
`crystallineMod2D p k (a : ℚ_[p])` is UNCONDITIONALLY weakly admissible! -/
theorem crystallineMod2D_int_weaklyAdmissible (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 2 ≤ k)
    (a : ℤ) : (crystallineMod2D p k hk (a : ℚ_[p])).IsWeaklyAdmissible :=
  (crystallineMod2D_weaklyAdmissible_iff p k hk (a : ℚ_[p])).mpr (padic_norm_intCast_le_one a)

/-- Unconditional weak admissibility of Ramanujan's `Δ₁₂` (`k = 12`, `a_p = τ(p)`) at EVERY prime `p`! -/
theorem delta12_weaklyAdmissible (p : ℕ) [Fact p.Prime] :
    (crystallineMod2D p 12 (by omega) (ramanujanTau p : ℚ_[p])).IsWeaklyAdmissible :=
  crystallineMod2D_int_weaklyAdmissible p 12 (by omega) (ramanujanTau p)

/-- Unconditional weak admissibility of `Δ₁₆` (`k = 16`) at EVERY prime `p`! -/
theorem delta16_weaklyAdmissible (p : ℕ) [Fact p.Prime] :
    (crystallineMod2D p 16 (by omega) (coeffDelta16Z p : ℚ_[p])).IsWeaklyAdmissible :=
  crystallineMod2D_int_weaklyAdmissible p 16 (by omega) (coeffDelta16Z p)

/-- Unconditional weak admissibility of `Δ₁₈` (`k = 18`) at EVERY prime `p`! -/
theorem delta18_weaklyAdmissible (p : ℕ) [Fact p.Prime] :
    (crystallineMod2D p 18 (by omega) (coeffDelta18Z p : ℚ_[p])).IsWeaklyAdmissible :=
  crystallineMod2D_int_weaklyAdmissible p 18 (by omega) (coeffDelta18Z p)

/-- Unconditional weak admissibility of `Δ₂₀` (`k = 20`) at EVERY prime `p`! -/
theorem delta20_weaklyAdmissible (p : ℕ) [Fact p.Prime] :
    (crystallineMod2D p 20 (by omega) (coeffDelta20Z p : ℚ_[p])).IsWeaklyAdmissible :=
  crystallineMod2D_int_weaklyAdmissible p 20 (by omega) (coeffDelta20Z p)

/-- Unconditional weak admissibility of `Δ₂₂` (`k = 22`) at EVERY prime `p`! -/
theorem delta22_weaklyAdmissible (p : ℕ) [Fact p.Prime] :
    (crystallineMod2D p 22 (by omega) (coeffDelta22Z p : ℚ_[p])).IsWeaklyAdmissible :=
  crystallineMod2D_int_weaklyAdmissible p 22 (by omega) (coeffDelta22Z p)

end Dim2Classification

/-! ## Section 4: Concrete Fontaine–Laffaille Modules over `ℤ_[p]` & Mazur's Theorem -/

section FontaineLaffailleSection

variable {p : ℕ} [Fact p.Prime]

/-- Every submodule of a finite free `ℤ_[p]`-module is finite and free (since `ℤ_[p]` is a PID). -/
theorem submodule_finite_free_padicInt {N : Type u} [AddCommGroup N] [Module ℤ_[p] N]
    [Module.Free ℤ_[p] N] [Module.Finite ℤ_[p] N] (S : Submodule ℤ_[p] N) :
    Module.Finite ℤ_[p] S ∧ Module.Free ℤ_[p] S := by
  have : IsNoetherian ℤ_[p] N := isNoetherian_of_isNoetherianRing_of_finite ℤ_[p] N
  have hfin : Module.Finite ℤ_[p] S := Module.Finite.iff_fg.mpr (IsNoetherian.noetherian S)
  have : Module.IsTorsionFree ℤ_[p] N := inferInstance
  have : Module.IsTorsionFree ℤ_[p] S := inferInstance
  exact ⟨hfin, Module.free_of_finite_type_torsion_free'⟩

/-- Over `ℤ_[p]`, any quotient `N ⧸ K` that is free splits, so `K` is a direct summand of `N`. -/
theorem exists_isCompl_of_quot_free {N : Type u} [AddCommGroup N] [Module ℤ_[p] N]
    (K : Submodule ℤ_[p] N) [Module.Free ℤ_[p] (N ⧸ K)] :
    ∃ C : Submodule ℤ_[p] N, IsCompl K C := by
  let b := Module.Free.chooseBasis ℤ_[p] (N ⧸ K)
  let s : (N ⧸ K) →ₗ[ℤ_[p]] N :=
    b.constr ℤ_[p] (fun i => Classical.choose (Submodule.mkQ_surjective K (b i)))
  have hsec : ∀ q : N ⧸ K, Submodule.mkQ K (s q) = q := by
    have hcomp : (Submodule.mkQ K).comp s = LinearMap.id := by
      apply b.ext
      intro i
      simp only [LinearMap.comp_apply, LinearMap.id_apply, s, Basis.constr_basis]
      exact Classical.choose_spec (Submodule.mkQ_surjective K (b i))
    exact fun q => LinearMap.congr_fun hcomp q
  refine ⟨LinearMap.range s, ?_⟩
  rw [isCompl_iff]
  constructor
  · rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hxK, ⟨q, rfl⟩⟩
    have hq0 : q = 0 := by
      rw [← hsec q]
      exact (Submodule.Quotient.mk_eq_zero K).mpr hxK
    rw [hq0, map_zero]
    exact Submodule.zero_mem ⊥
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hmemK : x - s (Submodule.mkQ K x) ∈ K := by
      rw [← Submodule.Quotient.mk_eq_zero K, ← Submodule.mkQ_apply, map_sub, hsec, sub_self]
    have hmemR : s (Submodule.mkQ K x) ∈ LinearMap.range s := ⟨Submodule.mkQ K x, rfl⟩
    have hadd := Submodule.add_mem_sup hmemK hmemR
    simpa [sub_add_cancel] using hadd

/-- **Adapted Graded Basis Theorem for Direct-Summand Filtrations over `ℤ_[p]`**:
Any finite free `ℤ_[p]`-module `N` equipped with an antitone filtration by direct summands
`N = F 0 ≥ F 1 ≥ ... ≥ F m = ⊥` admits a `ℤ_[p]`-basis `b : Basis (Fin d) ℤ_[p] N` and
integer weights `h : Fin d → ℕ` (`h j < m`) such that for every `i : ℤ`:
`F i = Submodule.span ℤ_[p] { v | ∃ j : Fin d, i ≤ (h j : ℤ) ∧ v = b j }`! -/
theorem exists_adapted_graded_basis :
    ∀ (m : ℕ) {N : Type u} [AddCommGroup N] [Module ℤ_[p] N] [Module.Free ℤ_[p] N]
      [Module.Finite ℤ_[p] N] (F : ℤ → Submodule ℤ_[p] N),
      (∀ ⦃i j : ℤ⦄, i ≤ j → F j ≤ F i) →
      F 0 = ⊤ → F (m : ℤ) = ⊥ →
      (∀ i : ℤ, ∃ C : Submodule ℤ_[p] N, IsCompl (F i) C) →
      ∃ (d : ℕ) (b : Basis (Fin d) ℤ_[p] N) (h : Fin d → ℕ),
        (∀ j : Fin d, h j < m) ∧
        (∀ i : ℤ, F i = Submodule.span ℤ_[p] { v | ∃ j : Fin d, i ≤ (h j : ℤ) ∧ v = b j })
  | 0, N, _, _, _, _, F, hant, h0, hm, _ => by
    have htop_bot : (⊤ : Submodule ℤ_[p] N) = ⊥ := by rw [← h0]; simpa using hm
    have hsub : Subsingleton N := by
      refine ⟨fun x y => ?_⟩
      have hx : x = 0 := by rw [← Submodule.mem_bot (R := ℤ_[p]), ← htop_bot]; trivial
      have hy : y = 0 := by rw [← Submodule.mem_bot (R := ℤ_[p]), ← htop_bot]; trivial
      rw [hx, hy]
    let b : Basis (Fin 0) ℤ_[p] N :=
      Basis.mk (v := fun j : Fin 0 => Fin.elim0 j) (linearIndependent_empty_type)
        (fun x _ => by
          rw [Subsingleton.elim x 0]
          exact Submodule.zero_mem _)
    refine ⟨0, b, fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun i => ?_⟩
    ext x
    rw [Subsingleton.elim x 0]
    exact ⟨fun _ => Submodule.zero_mem _, fun _ => (F i).zero_mem⟩
  | m + 1, N, _, _, _, _, F, hant, h0, hm, hds => by
    obtain ⟨C, hC⟩ := hds 1
    have : Module.Finite ℤ_[p] C := (submodule_finite_free_padicInt C).1
    have : Module.Free ℤ_[p] C := (submodule_finite_free_padicInt C).2
    have : Module.Finite ℤ_[p] (F 1) := (submodule_finite_free_padicInt (F 1)).1
    have : Module.Free ℤ_[p] (F 1) := (submodule_finite_free_padicInt (F 1)).2
    let F' : ℤ → Submodule ℤ_[p] (F 1) := fun i => (F (i + 1)).comap (F 1).subtype
    have hF'_ant : ∀ ⦃i j : ℤ⦄, i ≤ j → F' j ≤ F' i := fun i j hij =>
      Submodule.comap_mono (hant (by omega))
    have hF'_0 : F' 0 = ⊤ := by ext ⟨x, hx⟩; simp [F']
    have hF'_m : F' (m : ℤ) = ⊥ := by
      ext ⟨x, hx⟩
      have hcast : ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) := by push_cast; ring
      simp only [F', Submodule.mem_comap, Submodule.coe_subtype, hcast, hm, Submodule.mem_bot]
      exact ⟨fun hx0 => Subtype.ext hx0, fun hx0 => congrArg Subtype.val hx0⟩
    have hF'_ds : ∀ i : ℤ, ∃ C' : Submodule ℤ_[p] (F 1), IsCompl (F' i) C' := by
      intro i
      by_cases hi : i < 0
      · refine ⟨⊥, ?_⟩
        have htop : F' i = ⊤ := top_unique (hF'_0 ▸ hF'_ant (by omega))
        rw [htop]
        exact isCompl_top_bot
      · obtain ⟨Ci, hCi⟩ := hds (i + 1)
        refine ⟨Ci.comap (F 1).subtype, ?_⟩
        have hle1 : F (i + 1) ≤ F 1 := hant (by omega)
        rw [isCompl_iff]
        constructor
        · rw [disjoint_iff, eq_bot_iff]
          rintro ⟨x, hx1⟩ ⟨hxF, hxC⟩
          have hbot : x ∈ F (i + 1) ⊓ Ci := ⟨hxF, hxC⟩
          rw [hCi.disjoint.eq_bot, Submodule.mem_bot] at hbot
          exact Subtype.ext hbot
        · rw [codisjoint_iff, eq_top_iff]
          rintro ⟨x, hx1⟩ _
          have hmem : x ∈ F (i + 1) ⊔ Ci := by rw [hCi.codisjoint.eq_top]; trivial
          obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
          have ha1 : a ∈ F 1 := hle1 ha
          have hb1 : b ∈ F 1 := by
            have : b = x - a := by rw [← hab]; abel
            rw [this]
            exact (F 1).sub_mem hx1 ha1
          have hadd := Submodule.add_mem_sup (show (⟨a, ha1⟩ : F 1) ∈ F' i from ha)
            (show (⟨b, hb1⟩ : F 1) ∈ Ci.comap (F 1).subtype from hb)
          convert hadd using 1
          exact Subtype.ext hab.symm
    obtain ⟨d₁, b₁, h₁, hh₁_lt, hF'_span⟩ :=
      exists_adapted_graded_basis m F' hF'_ant hF'_0 hF'_m hF'_ds
    let eC_idx := Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ_[p] C)
    let d₀ : ℕ := Fintype.card (Module.Free.ChooseBasisIndex ℤ_[p] C)
    let b₀ : Basis (Fin d₀) ℤ_[p] C := (Module.Free.chooseBasis ℤ_[p] C).reindex eC_idx
    let eProd : (C × F 1) ≃ₗ[ℤ_[p]] N :=
      Submodule.prodEquivOfIsCompl C (F 1) hC.symm
    let bSum : Basis (Fin d₀ ⊕ Fin d₁) ℤ_[p] N := (b₀.prod b₁).map eProd
    let b : Basis (Fin (d₀ + d₁)) ℤ_[p] N := bSum.reindex finSumFinEquiv
    let h : Fin (d₀ + d₁) → ℕ := fun j =>
      Sum.elim (fun _ => 0) (fun j₁ => h₁ j₁ + 1) (finSumFinEquiv.symm j)
    refine ⟨d₀ + d₁, b, h, ?_, ?_⟩
    · intro j
      dsimp [h]
      cases hj : finSumFinEquiv.symm j with
      | inl j₀ => simp
      | inr j₁ => exact Nat.succ_lt_succ (hh₁_lt j₁)
    · intro i
      by_cases hi : i ≤ 0
      · have htop : F i = ⊤ := top_unique (h0 ▸ hant hi)
        rw [htop]
        refine (eq_top_iff.mpr ?_).symm
        rw [← b.span_eq]
        refine Submodule.span_mono ?_
        rintro _ ⟨j, rfl⟩
        exact ⟨j, by omega, rfl⟩
      · have hi1 : 1 ≤ i := by omega
        have hFle : F i ≤ F 1 := hant hi1
        ext x
        constructor
        · intro hx
          have hx1 : x ∈ F 1 := hFle hx
          have hx' : (⟨x, hx1⟩ : F 1) ∈ F' (i - 1) := by
            change x ∈ F ((i - 1) + 1)
            simpa using hx
          rw [hF'_span (i - 1)] at hx'
          have hmap := Submodule.mem_map_of_mem (f := (F 1).subtype) hx'
          rw [Submodule.map_span] at hmap
          refine Submodule.span_mono ?_ hmap
          rintro _ ⟨_, ⟨j₁, hj₁, rfl⟩, rfl⟩
          refine ⟨finSumFinEquiv (m := d₀) (n := d₁) (Sum.inr j₁), ?_, ?_⟩
          · have hsym : (finSumFinEquiv (m := d₀) (n := d₁)).symm
                (finSumFinEquiv (m := d₀) (n := d₁) (Sum.inr j₁)) = Sum.inr j₁ :=
              Equiv.symm_apply_apply _ _
            simp only [h, hsym, Sum.elim_inr]
            omega
          · have hsym : (finSumFinEquiv (m := d₀) (n := d₁)).symm
                (finSumFinEquiv (m := d₀) (n := d₁) (Sum.inr j₁)) = Sum.inr j₁ :=
              Equiv.symm_apply_apply _ _
            rw [show b (finSumFinEquiv (m := d₀) (n := d₁) (Sum.inr j₁)) =
              bSum ((finSumFinEquiv (m := d₀) (n := d₁)).symm
                (finSumFinEquiv (m := d₀) (n := d₁) (Sum.inr j₁))) from Basis.reindex_apply _ _ _,
              hsym]
            simp [bSum, eProd, Basis.prod_apply]
        · intro hx
          refine Submodule.span_induction (p := fun v _ => v ∈ F i) ?_ (F i).zero_mem
            (fun _ _ _ _ ha hb => (F i).add_mem ha hb)
            (fun c _ _ ha => (F i).smul_mem c ha) hx
          rintro _ ⟨j, hj, rfl⟩
          dsimp [h] at hj
          cases hjs : finSumFinEquiv.symm j with
          | inl j₀ =>
            rw [hjs] at hj
            simp only [Sum.elim_inl, Nat.cast_zero] at hj
            omega
          | inr j₁ =>
            rw [hjs] at hj
            simp only [Sum.elim_inr] at hj
            have hmem' : b₁ j₁ ∈ F' (i - 1) := by
              rw [hF'_span (i - 1)]
              exact Submodule.subset_span ⟨j₁, by omega, rfl⟩
            have hbj : b j = (b₁ j₁ : N) := by
              rw [show b j = bSum (finSumFinEquiv.symm j) from Basis.reindex_apply _ _ _, hjs]
              simp [bSum, eProd, Basis.prod_apply]
            rw [hbj]
            have : (b₁ j₁ : N) ∈ F ((i - 1) + 1) := hmem'
            simpa using this

/-- **Concrete Fontaine–Laffaille Module over `ℤ_[p]`**:
a finite free `ℤ_[p]`-module `M`, a decreasing filtration `M = Fil^0 ⊇ Fil^1 ⊇ ... ⊇ Fil^{p-1} = 0`
by direct summands, and divided Frobenii `φ_i : Fil^i M →ₗ[ℤ_[p]] M` satisfying
`φ_i|_{Fil^{i+1} M} = p · φ_{i+1}` and strong divisibility `∑_{i=0}^{p-2} im(φ_i) = M`. -/
structure FontaineLaffailleModule (p : ℕ) [Fact p.Prime] (M : Type u)
    [AddCommGroup M] [Module ℤ_[p] M] [Module.Free ℤ_[p] M] [Module.Finite ℤ_[p] M] where
  fil : ℤ → Submodule ℤ_[p] M
  antitone : ∀ ⦃i j : ℤ⦄, i ≤ j → fil j ≤ fil i
  fil_zero : fil 0 = ⊤
  fil_top : fil ((p : ℤ) - 1) = ⊥
  directSummand : ∀ i : ℤ, ∃ C : Submodule ℤ_[p] M, IsCompl (fil i) C
  phiDiv : ∀ i : ℤ, fil i →ₗ[ℤ_[p]] M
  phiDiv_compat : ∀ (i : ℤ) (x : fil (i + 1)),
    phiDiv i ⟨x.1, antitone (by omega) x.2⟩ = (p : ℤ_[p]) • phiDiv (i + 1) x
  phiDiv_surj :
    (⨆ i ∈ Finset.Icc (0 : ℤ) ((p : ℤ) - 2), LinearMap.range (phiDiv i)) = ⊤

namespace FontaineLaffailleModule

variable {M : Type u} [AddCommGroup M] [Module ℤ_[p] M]
  [Module.Free ℤ_[p] M] [Module.Finite ℤ_[p] M]

/-- The un-divided Frobenius endomorphism `φ₀ : M →ₗ[ℤ_[p]] M` attached to `FL`. -/
def phi0 (FL : FontaineLaffailleModule p M) : M →ₗ[ℤ_[p]] M :=
  (FL.phiDiv 0).comp
    ({ toFun := fun x => ⟨x, by rw [FL.fil_zero]; trivial⟩
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl } : M →ₗ[ℤ_[p]] FL.fil 0)

@[simp] theorem phi0_apply (FL : FontaineLaffailleModule p M) (x : M) :
    FL.phi0 x = FL.phiDiv 0 ⟨x, by rw [FL.fil_zero]; trivial⟩ := rfl

theorem phiDiv_congr (FL : FontaineLaffailleModule p M) {i j : ℤ} (hij : i = j)
    (x : M) (hx : x ∈ FL.fil i) :
    FL.phiDiv i ⟨x, hx⟩ = FL.phiDiv j ⟨x, hij ▸ hx⟩ := by
  subst hij; rfl

/-- Iterated divided-Frobenius compatibility: for `n : ℕ` and `x ∈ Fil^{i + n} M`,
`φ_i(x) = p^n • φ_{i + n}(x)`. -/
theorem phiDiv_pow_compat (FL : FontaineLaffailleModule p M) (i : ℤ) :
    ∀ (n : ℕ) (x : M) (hx : x ∈ FL.fil (i + (n : ℤ))),
      FL.phiDiv i ⟨x, FL.antitone (by omega) hx⟩ =
        (p : ℤ_[p]) ^ n • FL.phiDiv (i + (n : ℤ)) ⟨x, hx⟩
  | 0, x, hx => by
    rw [pow_zero, one_smul]
    exact FL.phiDiv_congr (by omega) x _
  | n + 1, x, hx => by
    have hcast : i + ((n + 1 : ℕ) : ℤ) = i + (n : ℤ) + 1 := by push_cast; ring
    have hx' : x ∈ FL.fil (i + (n : ℤ) + 1) := hcast ▸ hx
    have hstep := FL.phiDiv_pow_compat i n x (FL.antitone (by omega) hx')
    have h1 := FL.phiDiv_compat (i + (n : ℤ)) ⟨x, hx'⟩
    rw [hstep, h1, pow_succ, mul_smul, FL.phiDiv_congr hcast.symm x hx']

/-- In particular, for any `n : ℕ` and `x ∈ Fil^n M`, `φ₀(x) = p^n • φ_n(x)`. -/
theorem phi0_eq_pow_smul_phiDiv (FL : FontaineLaffailleModule p M) (n : ℕ)
    {x : M} (hx : x ∈ FL.fil (n : ℤ)) :
    FL.phi0 x = (p : ℤ_[p]) ^ n • FL.phiDiv (n : ℤ) ⟨x, hx⟩ := by
  have hcast : (0 : ℤ) + (n : ℤ) = (n : ℤ) := zero_add _
  have h := FL.phiDiv_pow_compat 0 n x (hcast.symm ▸ hx)
  rw [phi0_apply, h]
  congr 1
  exact FL.phiDiv_congr hcast x _

/-- **Associated Graded Bijectivity Theorem**:
For EVERY `FL : FontaineLaffailleModule p M`, there exists an adapted graded `ℤ_[p]`-basis
`b : Basis (Fin d) ℤ_[p] M` with weights `h : Fin d → ℕ` (`h j ≤ p - 2`) such that the
associated graded Frobenius `Ψ(b j) = φ_{h j}(b j)` is SURJECTIVE with **`IsUnit (det Ψ)`**,
and `FL.phi0 = Ψ ∘ D_p` with `det(FL.phi0) = det(Ψ) * p^{∑ h j}`! -/
theorem exists_adapted_basis_unit_det (FL : FontaineLaffailleModule p M) :
    ∃ (d : ℕ) (b : Basis (Fin d) ℤ_[p] M) (h : Fin d → ℕ) (Ψ : M →ₗ[ℤ_[p]] M),
      (∀ j : Fin d, h j ≤ p - 2) ∧
      (∀ i : ℤ, FL.fil i = Submodule.span ℤ_[p] { v | ∃ j : Fin d, i ≤ (h j : ℤ) ∧ v = b j }) ∧
      (∀ j : Fin d, FL.phi0 (b j) = (p : ℤ_[p]) ^ (h j) • Ψ (b j)) ∧
      IsUnit (LinearMap.det Ψ) ∧
      LinearMap.det FL.phi0 = LinearMap.det Ψ * (p : ℤ_[p]) ^ (∑ j : Fin d, h j) := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have htop : FL.fil ((p - 1 : ℕ) : ℤ) = ⊥ := by
    have : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
    rw [this, FL.fil_top]
  obtain ⟨d, b, h, hh_lt, hfil_span⟩ :=
    exists_adapted_graded_basis (p - 1) FL.fil FL.antitone FL.fil_zero htop FL.directSummand
  have hh_le : ∀ j : Fin d, h j ≤ p - 2 := fun j => by have := hh_lt j; omega
  have hb_mem : ∀ j : Fin d, b j ∈ FL.fil (h j : ℤ) := fun j => by
    rw [hfil_span (h j : ℤ)]
    exact Submodule.subset_span ⟨j, le_rfl, rfl⟩
  let Ψ : M →ₗ[ℤ_[p]] M :=
    b.constr ℤ_[p] (fun j => FL.phiDiv (h j : ℤ) ⟨b j, hb_mem j⟩)
  have hΨ_apply : ∀ j : Fin d, Ψ (b j) = FL.phiDiv (h j : ℤ) ⟨b j, hb_mem j⟩ := fun j => by
    simp [Ψ]
  have hphi0_b : ∀ j : Fin d, FL.phi0 (b j) = (p : ℤ_[p]) ^ (h j) • Ψ (b j) := fun j => by
    rw [hΨ_apply j]
    exact FL.phi0_eq_pow_smul_phiDiv (h j) (hb_mem j)
  have hrange_le : ∀ i ∈ Finset.Icc (0 : ℤ) ((p : ℤ) - 2),
      LinearMap.range (FL.phiDiv i) ≤ LinearMap.range Ψ := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    rw [hfil_span i] at hx
    refine Submodule.span_induction
      (p := fun v hv =>
        FL.phiDiv i ⟨v, (hfil_span i).symm ▸ hv⟩ ∈ LinearMap.range Ψ) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨j, hj, rfl⟩
      have hn : i + ((h j - i.toNat : ℕ) : ℤ) = (h j : ℤ) := by omega
      have hcompat := FL.phiDiv_pow_compat i (h j - i.toNat) (b j) (hn.symm ▸ hb_mem j)
      have hcast_eq := FL.phiDiv_congr hn (b j) (hn.symm ▸ hb_mem j)
      refine ⟨(p : ℤ_[p]) ^ (h j - i.toNat) • b j, ?_⟩
      rw [map_smul, hΨ_apply j, ← hcast_eq]
      exact hcompat.symm
    · exact ⟨0, by rw [map_zero]; exact (map_zero (FL.phiDiv i)).symm⟩
    · intro x y hx' hy' ihx ihy
      have hadd : FL.phiDiv i ⟨x + y, (hfil_span i).symm ▸ Submodule.add_mem _ hx' hy'⟩ =
          FL.phiDiv i ⟨x, (hfil_span i).symm ▸ hx'⟩ +
            FL.phiDiv i ⟨y, (hfil_span i).symm ▸ hy'⟩ := by
        rw [← map_add]; rfl
      rw [hadd]
      exact (LinearMap.range Ψ).add_mem ihx ihy
    · intro c x hx' ihx
      have hsmul : FL.phiDiv i ⟨c • x, (hfil_span i).symm ▸ Submodule.smul_mem _ c hx'⟩ =
          c • FL.phiDiv i ⟨x, (hfil_span i).symm ▸ hx'⟩ := by
        rw [← map_smul]; rfl
      rw [hsmul]
      exact (LinearMap.range Ψ).smul_mem c ihx
  have hΨ_surj : Function.Surjective Ψ := by
    rw [← LinearMap.range_eq_top]
    refine top_unique ?_
    rw [← FL.phiDiv_surj]
    exact iSup₂_le hrange_le
  let G : M →ₗ[ℤ_[p]] M := b.constr ℤ_[p] (fun j => Classical.choose (hΨ_surj (b j)))
  have hcomp_id : Ψ.comp G = LinearMap.id := by
    apply b.ext
    intro j
    simp only [LinearMap.comp_apply, LinearMap.id_apply, G, Basis.constr_basis]
    exact Classical.choose_spec (hΨ_surj (b j))
  have hdet_mul_one : LinearMap.det Ψ * LinearMap.det G = 1 := by
    rw [← LinearMap.det_comp, hcomp_id, LinearMap.det_id]
  have hΨ_unit : IsUnit (LinearMap.det Ψ) := isUnit_iff_exists_inv.mpr ⟨LinearMap.det G, hdet_mul_one⟩
  let Dp : M →ₗ[ℤ_[p]] M := b.constr ℤ_[p] (fun j => (p : ℤ_[p]) ^ (h j) • b j)
  have hphi0_eq : FL.phi0 = Ψ.comp Dp := by
    apply b.ext
    intro j
    simp only [LinearMap.comp_apply, Dp, Basis.constr_basis, map_smul, hphi0_b j]
  have hDp_mat : LinearMap.toMatrix b b Dp = Matrix.diagonal (fun j : Fin d => (p : ℤ_[p]) ^ (h j)) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    simp only [Dp, Basis.constr_basis, map_smul, Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_apply, Matrix.diagonal_apply, smul_eq_mul]
    by_cases hij : j = i
    · subst hij; simp
    · rw [if_neg hij, if_neg (Ne.symm hij), mul_zero]
  have hDp_det : LinearMap.det Dp = (p : ℤ_[p]) ^ (∑ j : Fin d, h j) := by
    rw [← LinearMap.det_toMatrix b, hDp_mat, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]
  refine ⟨d, b, h, Ψ, hh_le, hfil_span, hphi0_b, hΨ_unit, ?_⟩
  rw [hphi0_eq, LinearMap.det_comp, hDp_det]

/-! ### Base Change `M →ₗ[ℤ_[p]] (Fin d → ℚ_[p])`, `toFilteredPhiModule` & Mazur's Theorem -/

/-- Canonical `ℤ_[p]`-basis of `M` indexed by `Fin (finrank ℤ_[p] M)`. -/
def canonBasis (M : Type u) [AddCommGroup M] [Module ℤ_[p] M]
    [Module.Free ℤ_[p] M] [Module.Finite ℤ_[p] M] :
    Basis (Fin (Module.finrank ℤ_[p] M)) ℤ_[p] M :=
  (Module.Free.chooseBasis ℤ_[p] M).reindex
    (Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis (Module.Free.chooseBasis ℤ_[p] M)).symm)

/-- Coordinate embedding `M →ₗ[ℤ_[p]] (Fin d → ℚ_[p])` induced by a `ℤ_[p]`-basis `b₀`. -/
def embedQ {d : ℕ} (b₀ : Basis (Fin d) ℤ_[p] M) : M →ₗ[ℤ_[p]] (Fin d → ℚ_[p]) where
  toFun x j := (b₀.repr x j : ℚ_[p])
  map_add' x y := by ext j; simp
  map_smul' c x := by ext j; simp [Algebra.smul_def]

@[simp] theorem padicInt_coeRingHom_eq (z : ℤ_[p]) :
    PadicInt.Coe.ringHom z = (z : ℚ_[p]) := rfl

omit [Module.Free ℤ_[p] M] [Module.Finite ℤ_[p] M] in
@[simp] theorem embedQ_smul {d : ℕ} (b₀ : Basis (Fin d) ℤ_[p] M) (c : ℤ_[p]) (x : M) :
    embedQ b₀ (c • x) = (c : ℚ_[p]) • embedQ b₀ x := by
  ext j
  simp [embedQ, Algebra.smul_def]

theorem padicInt_map_det {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ_[p]) :
    (B.map PadicInt.Coe.ringHom).det = (B.det : ℚ_[p]) :=
  (RingHom.map_det PadicInt.Coe.ringHom B).symm

omit [Module.Free ℤ_[p] M] [Module.Finite ℤ_[p] M] in
theorem embedQ_injective {d : ℕ} (b₀ : Basis (Fin d) ℤ_[p] M) :
    Function.Injective (embedQ b₀) := by
  intro x y hxy
  apply b₀.repr.injective
  ext j
  exact Subtype.ext (congrFun hxy j)

omit [Module.Free ℤ_[p] M] [Module.Finite ℤ_[p] M] in
/-- Denominator clearing: every vector `v : Fin d → ℚ_[p]` satisfies `p^n • v ∈ range (embedQ b₀)`
for some `n : ℕ`. -/
theorem exists_pow_p_smul_mem_range_embedQ {d : ℕ} (b₀ : Basis (Fin d) ℤ_[p] M)
    (v : Fin d → ℚ_[p]) :
    ∃ (n : ℕ) (x : M), (p : ℚ_[p]) ^ n • v = embedQ b₀ x := by
  classical
  let k : Fin d → ℕ := fun j => if v j = 0 then 0 else (-Padic.valuation (v j)).toNat
  let n : ℕ := Finset.univ.sup k
  have hnorm : ∀ j : Fin d, ‖(p : ℚ_[p]) ^ n * v j‖ ≤ 1 := by
    intro j
    by_cases hv : v j = 0
    · simp [hv]
    · have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
      have hkn : k j ≤ n := Finset.le_sup (Finset.mem_univ j)
      have hv_ge : 0 ≤ Padic.valuation ((p : ℚ_[p]) ^ n * v j) := by
        rw [Padic.valuation_mul (pow_ne_zero n hp0) hv, padic_valuation_p_pow]
        have hkdef : k j = (-Padic.valuation (v j)).toNat := if_neg hv
        omega
      exact padic_norm_le_one_of_valuation_nonneg hv_ge
  let z : Fin d → ℤ_[p] := fun j => ⟨(p : ℚ_[p]) ^ n * v j, hnorm j⟩
  refine ⟨n, b₀.repr.symm (Finsupp.equivFunOnFinite.symm z), ?_⟩
  ext j
  simp [embedQ, z]
  rfl

/-- Base change of a `ℤ_[p]`-linear endomorphism `f : M →ₗ[ℤ_[p]] M` to `Fin d → ℚ_[p]`. -/
def extendQ {d : ℕ} (b₀ : Basis (Fin d) ℤ_[p] M) (f : M →ₗ[ℤ_[p]] M) :
    (Fin d → ℚ_[p]) →ₗ[ℚ_[p]] (Fin d → ℚ_[p]) :=
  Matrix.toLin' ((LinearMap.toMatrix b₀ b₀ f).map PadicInt.Coe.ringHom)

omit [Module.Free ℤ_[p] M] [Module.Finite ℤ_[p] M] in
theorem extendQ_embedQ {d : ℕ} (b₀ : Basis (Fin d) ℤ_[p] M) (f : M →ₗ[ℤ_[p]] M) (x : M) :
    extendQ b₀ f (embedQ b₀ x) = embedQ b₀ (f x) := by
  ext i
  change (((LinearMap.toMatrix b₀ b₀ f).map PadicInt.Coe.ringHom).mulVec (embedQ b₀ x)) i =
    (b₀.repr (f x) i : ℚ_[p])
  have hmat := LinearMap.toMatrix_mulVec_repr b₀ b₀ f x
  have hi := congrFun hmat i
  have hcast := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hi
  simpa [Matrix.mulVec, dotProduct, embedQ] using hcast

omit [Module.Free ℤ_[p] M] [Module.Finite ℤ_[p] M] in
theorem det_extendQ {d : ℕ} (b₀ : Basis (Fin d) ℤ_[p] M) (f : M →ₗ[ℤ_[p]] M) :
    LinearMap.det (extendQ b₀ f) = ((LinearMap.det f : ℤ_[p]) : ℚ_[p]) := by
  unfold extendQ
  rw [LinearMap.det_toLin', padicInt_map_det, LinearMap.det_toMatrix b₀]

/-- **Base-Change Functor `FL.toFilteredPhiModule`**:
maps any concrete `FontaineLaffailleModule p M` over `ℤ_[p]` to a concrete
`FilteredPhiModule p (Fin (finrank ℤ_[p] M) → ℚ_[p])` over `ℚ_[p]`! -/
def toFilteredPhiModule (FL : FontaineLaffailleModule p M) :
    FilteredPhiModule p (Fin (Module.finrank ℤ_[p] M) → ℚ_[p]) :=
  let b₀ := canonBasis (p := p) M
  let A : Matrix (Fin (Module.finrank ℤ_[p] M)) (Fin (Module.finrank ℤ_[p] M)) ℚ_[p] :=
    (LinearMap.toMatrix b₀ b₀ FL.phi0).map PadicInt.Coe.ringHom
  have hdet_ne : A.det ≠ 0 := by
    have hdet_eq : A.det = ((LinearMap.det FL.phi0 : ℤ_[p]) : ℚ_[p]) := by
      rw [padicInt_map_det, LinearMap.det_toMatrix b₀]
    rw [hdet_eq]
    obtain ⟨_, _, h, Ψ, _, _, _, hΨ_unit, hdet_phi0⟩ := FL.exists_adapted_basis_unit_det
    rw [hdet_phi0]
    push_cast
    have hΨ_ne : ((LinearMap.det Ψ : ℤ_[p]) : ℚ_[p]) ≠ 0 := by
      intro h0
      obtain ⟨u, hu⟩ := hΨ_unit
      have hmul : ((LinearMap.det Ψ : ℤ_[p]) : ℚ_[p]) * (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) = 1 := by
        rw [← hu]
        exact_mod_cast congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) u.mul_inv
      rw [h0, zero_mul] at hmul
      exact zero_ne_one hmul
    have hp_ne : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    exact mul_ne_zero hΨ_ne (pow_ne_zero _ hp_ne)
  have hdet_unit : IsUnit A.det := Ne.isUnit hdet_ne
  { φ :=
      { toLinearMap := Matrix.toLin' A
        invFun := Matrix.toLin' A⁻¹
        left_inv := fun v => by
          change A⁻¹.mulVec (A.mulVec v) = v
          rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hdet_unit, Matrix.one_mulVec]
        right_inv := fun v => by
          change A.mulVec (A⁻¹.mulVec v) = v
          rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdet_unit, Matrix.one_mulVec] }
    fil :=
      { fil := fun i => Submodule.span ℚ_[p] (embedQ b₀ '' (FL.fil i : Set M))
        antitone := fun _ _ hij => Submodule.span_mono (Set.image_mono (FL.antitone hij))
        botBound := 0
        topBound := (p : ℤ) - 2
        bot_le_top := by have := (Fact.out : p.Prime).two_le; omega
        eq_top_of_le := fun i hi => by
          have htop : FL.fil i = ⊤ := top_unique (FL.fil_zero ▸ FL.antitone hi)
          rw [htop, eq_top_iff]
          intro v _
          obtain ⟨n, x, hx⟩ := exists_pow_p_smul_mem_range_embedQ b₀ v
          have hp_ne : ((p : ℚ_[p]) ^ n) ≠ 0 :=
            pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
          have hmem : embedQ b₀ x ∈ Submodule.span ℚ_[p] (embedQ b₀ '' ((⊤ : Submodule ℤ_[p] M) : Set M)) :=
            Submodule.subset_span ⟨x, trivial, rfl⟩
          have hv : v = ((p : ℚ_[p]) ^ n)⁻¹ • embedQ b₀ x := by
            rw [← hx, smul_smul, inv_mul_cancel₀ hp_ne, one_smul]
          rw [hv]
          exact Submodule.smul_mem _ _ hmem
        eq_bot_of_gt := fun i hi => by
          have hbot : FL.fil i = ⊥ := bot_unique (FL.fil_top ▸ FL.antitone (by omega))
          rw [hbot, eq_bot_iff, Submodule.span_le]
          rintro _ ⟨x, hx, rfl⟩
          rw [SetLike.mem_coe, Submodule.mem_bot] at hx
          rw [hx, map_zero]
          exact Submodule.zero_mem ⊥ } }

/-- Helper: given a `ℤ_[p]`-basis `b'` of the saturated lattice `satU = {x : M | embedQ b₀ x ∈ U}`
of a `ℚ_[p]`-subspace `U ≤ (Fin d → ℚ_[p])`, its image under `embedQ b₀` is a `ℚ_[p]`-basis of `U`. -/
def basisOfSatLattice {d r : ℕ} (b₀ : Basis (Fin d) ℤ_[p] M)
    (U : Submodule ℚ_[p] (Fin d → ℚ_[p]))
    (satU : Submodule ℤ_[p] M) (hsat : ∀ x : M, x ∈ satU ↔ embedQ b₀ x ∈ U)
    (b' : Basis (Fin r) ℤ_[p] satU) :
    Basis (Fin r) ℚ_[p] U :=
  Basis.mk (v := fun j => ⟨embedQ b₀ (b' j).1, (hsat _).mp (b' j).2⟩)
    (by
      classical
      rw [Fintype.linearIndependent_iff]
      intro c hc
      let k : Fin r → ℕ := fun j => if c j = 0 then 0 else (-Padic.valuation (c j)).toNat
      let n : ℕ := Finset.univ.sup k
      have hnorm : ∀ j : Fin r, ‖(p : ℚ_[p]) ^ n * c j‖ ≤ 1 := by
        intro j
        by_cases hcj : c j = 0
        · simp [hcj]
        · have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
          have hkn : k j ≤ n := Finset.le_sup (Finset.mem_univ j)
          have hv_ge : 0 ≤ Padic.valuation ((p : ℚ_[p]) ^ n * c j) := by
            rw [Padic.valuation_mul (pow_ne_zero n hp0) hcj, padic_valuation_p_pow]
            have hkdef : k j = (-Padic.valuation (c j)).toNat := if_neg hcj
            omega
          exact padic_norm_le_one_of_valuation_nonneg hv_ge
      let z : Fin r → ℤ_[p] := fun j => ⟨(p : ℚ_[p]) ^ n * c j, hnorm j⟩
      have hsum0 : ∑ j : Fin r, z j • b' j = 0 := by
        apply Subtype.ext
        apply embedQ_injective b₀
        rw [Submodule.coe_sum, Submodule.coe_zero, map_zero, map_sum]
        have hval := congrArg (fun u : U => (p : ℚ_[p]) ^ n • (u : Fin d → ℚ_[p])) hc
        rw [Submodule.coe_zero, smul_zero, Submodule.coe_sum, Finset.smul_sum] at hval
        refine Eq.trans ?_ hval
        refine Finset.sum_congr rfl fun j _ => ?_
        change embedQ b₀ (z j • (b' j).1) = (p : ℚ_[p]) ^ n • (c j • embedQ b₀ (b' j).1)
        rw [embedQ_smul, smul_smul]
      have hz0 : ∀ j : Fin r, z j = 0 := Fintype.linearIndependent_iff.mp b'.linearIndependent z hsum0
      intro j
      have hzj := congrArg (fun w : ℤ_[p] => (w : ℚ_[p])) (hz0 j)
      change (p : ℚ_[p]) ^ n * c j = 0 at hzj
      have hp_ne : (p : ℚ_[p]) ^ n ≠ 0 :=
        pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
      exact (mul_eq_zero.mp hzj).resolve_left hp_ne)
    (by
      intro u _
      obtain ⟨n, x, hx⟩ := exists_pow_p_smul_mem_range_embedQ b₀ (u : Fin d → ℚ_[p])
      have hx_sat : x ∈ satU := (hsat x).mpr (hx ▸ U.smul_mem ((p : ℚ_[p]) ^ n) u.2)
      have hrepr := (b'.sum_repr ⟨x, hx_sat⟩).symm
      have hp_ne : (p : ℚ_[p]) ^ n ≠ 0 :=
        pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
      have hu_eq : u = ∑ j : Fin r,
          (((p : ℚ_[p]) ^ n)⁻¹ * ((b'.repr ⟨x, hx_sat⟩ j : ℤ_[p]) : ℚ_[p])) •
            (⟨embedQ b₀ (b' j).1, (hsat _).mp (b' j).2⟩ : U) := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        have hx_emb : embedQ b₀ x =
            ∑ j : Fin r, ((b'.repr ⟨x, hx_sat⟩ j : ℤ_[p]) : ℚ_[p]) • embedQ b₀ (b' j).1 := by
          have h1 := congrArg (fun y : satU => embedQ b₀ y.1) hrepr
          rw [Submodule.coe_sum, map_sum] at h1
          refine h1.trans (Finset.sum_congr rfl fun j _ => ?_)
          exact embedQ_smul b₀ (b'.repr ⟨x, hx_sat⟩ j) (b' j).1
        calc (u : Fin d → ℚ_[p])
            = ((p : ℚ_[p]) ^ n)⁻¹ • ((p : ℚ_[p]) ^ n • (u : Fin d → ℚ_[p])) := by
                rw [smul_smul, inv_mul_cancel₀ hp_ne, one_smul]
          _ = ((p : ℚ_[p]) ^ n)⁻¹ • embedQ b₀ x := by rw [hx]
          _ = ((p : ℚ_[p]) ^ n)⁻¹ •
                ∑ j : Fin r, ((b'.repr ⟨x, hx_sat⟩ j : ℤ_[p]) : ℚ_[p]) • embedQ b₀ (b' j).1 := by
                rw [hx_emb]
          _ = ∑ j : Fin r,
                (((p : ℚ_[p]) ^ n)⁻¹ * ((b'.repr ⟨x, hx_sat⟩ j : ℤ_[p]) : ℚ_[p])) •
                  embedQ b₀ (b' j).1 := by
                rw [Finset.smul_sum]
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [smul_smul]
      rw [hu_eq]
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))

omit [Module.Free ℤ_[p] M] [Module.Finite ℤ_[p] M] in
@[simp] theorem basisOfSatLattice_apply {d r : ℕ} (b₀ : Basis (Fin d) ℤ_[p] M)
    (U : Submodule ℚ_[p] (Fin d → ℚ_[p]))
    (satU : Submodule ℤ_[p] M) (hsat : ∀ x : M, x ∈ satU ↔ embedQ b₀ x ∈ U)
    (b' : Basis (Fin r) ℤ_[p] satU) (j : Fin r) :
    (basisOfSatLattice b₀ U satU hsat b' j : Fin d → ℚ_[p]) = embedQ b₀ (b' j).1 := by
  simp [basisOfSatLattice]

/-- Helper: Hodge number `t_H` of a filtration generated by a basis `b` with weights `h : Fin r → ℕ`
(`Fil^i = span { b j | i ≤ h j }`) equals `∑ j : Fin r, (h j : ℤ)`! -/
theorem tH_eq_sum_weights_of_basis {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] {r : ℕ} (b : Basis (Fin r) K V) (h : Fin r → ℕ)
    (F : HodgeFiltration K V)
    (hF : ∀ i : ℤ, F.fil i = Submodule.span K { v | ∃ j : Fin r, i ≤ (h j : ℤ) ∧ v = b j }) :
    F.tH = ∑ j : Fin r, (h j : ℤ) := by
  classical
  have hdimAt : ∀ i : ℤ, F.dimAt i = (Finset.univ.filter (fun j : Fin r => i ≤ (h j : ℤ))).card := by
    intro i
    unfold HodgeFiltration.dimAt
    rw [hF i]
    let S : Set (Fin r) := { j : Fin r | i ≤ (h j : ℤ) }
    have hset : ({ v : V | ∃ j : Fin r, i ≤ (h j : ℤ) ∧ v = b j } : Set V) = b '' S := by
      ext v
      exact ⟨by rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩, by rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩⟩
    rw [hset]
    have hli : LinearIndependent K (fun j : S => b j.1) :=
      b.linearIndependent.comp Subtype.val Subtype.val_injective
    have hrange : Set.range (fun j : S => b j.1) = b '' S := by
      ext v; simp [S]
    rw [← hrange, finrank_span_eq_card hli]
    rw [Fintype.card_ofFinset (Finset.univ.filter (fun j : Fin r => i ≤ (h j : ℤ)))
      (fun j => by simp [S])]
  have hjump : ∀ i : ℤ, F.jump i = (Finset.univ.filter (fun j : Fin r => (h j : ℤ) = i)).card := by
    intro i
    unfold HodgeFiltration.jump
    rw [hdimAt i, hdimAt (i + 1)]
    have hdisj : Disjoint (Finset.univ.filter (fun j : Fin r => (h j : ℤ) = i))
        (Finset.univ.filter (fun j : Fin r => i + 1 ≤ (h j : ℤ))) := by
      rw [Finset.disjoint_left]
      intro j h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      omega
    have hunion : Finset.univ.filter (fun j : Fin r => i ≤ (h j : ℤ)) =
        Finset.univ.filter (fun j : Fin r => (h j : ℤ) = i) ∪
          Finset.univ.filter (fun j : Fin r => i + 1 ≤ (h j : ℤ)) := by
      ext j; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]; omega
    rw [hunion, Finset.card_union_of_disjoint hdisj]
    omega
  set Mmax : ℕ := Finset.univ.sup h
  set a : ℤ := min 0 F.botBound
  set bnd : ℤ := max (Mmax : ℤ) F.topBound
  rw [F.tH_eq_sum_Icc (min_le_right _ _) (le_max_right _ _)]
  have hsum_eq : (Finset.Icc a bnd).sum (fun i => (F.jump i : ℤ) * i) =
      (Finset.Icc a bnd).sum (fun i =>
        ∑ j ∈ Finset.univ.filter (fun j : Fin r => (h j : ℤ) = i), (h j : ℤ)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hjump i]
    have hconst : ∑ j ∈ Finset.univ.filter (fun j : Fin r => (h j : ℤ) = i), (h j : ℤ) =
        ∑ _j ∈ Finset.univ.filter (fun j : Fin r => (h j : ℤ) = i), i :=
      Finset.sum_congr rfl fun j hj => (Finset.mem_filter.mp hj).2
    rw [hconst, Finset.sum_const, nsmul_eq_mul]
  rw [hsum_eq, ← Finset.sum_fiberwise_of_maps_to (g := fun j : Fin r => (h j : ℤ))
    (t := Finset.Icc a bnd)]
  intro j _
  rw [Finset.mem_Icc]
  have ha0 : a ≤ 0 := min_le_left _ _
  have hleM : h j ≤ Mmax := Finset.le_sup (Finset.mem_univ j)
  have hMb : (Mmax : ℤ) ≤ bnd := le_max_left _ _
  omega

/-- **MAZUR'S / LAFFAILLE'S THEOREM (`fontaineLaffaille_implies_weaklyAdmissible`)**:
EVERY concrete Fontaine–Laffaille module `FL : FontaineLaffailleModule p M` over `ℤ_[p]`
yields a **WEAKLY ADMISSIBLE** filtered `φ`-module `FL.toFilteredPhiModule` over `ℚ_[p]`
(exact endpoint equality `t_H = t_N` and `t_H(U) ≤ t_N(U)` for EVERY `φ`-stable subspace `U`)! -/
theorem fontaineLaffaille_implies_weaklyAdmissible (FL : FontaineLaffailleModule p M) :
    FL.toFilteredPhiModule.IsWeaklyAdmissible := by
  let b₀ := canonBasis (p := p) M
  have hφ_emb : ∀ x : M, FL.toFilteredPhiModule.φ (embedQ b₀ x) = embedQ b₀ (FL.phi0 x) :=
    fun x => extendQ_embedQ b₀ FL.phi0 x
  -- Step 1: Exact endpoint equality `t_H = t_N`!
  have hend : FL.toFilteredPhiModule.tH = FL.toFilteredPhiModule.tN := by
    obtain ⟨d, b, h, Ψ, _, hfil_span, _, hΨ_unit, hdet_phi0⟩ := FL.exists_adapted_basis_unit_det
    -- Lift `b` to a `ℚ_[p]`-basis `bQ` of `⊤` (i.e. `Fin (finrank M) → ℚ_[p]`)
    let satTop : Submodule ℤ_[p] M := ⊤
    let eTop : M ≃ₗ[ℤ_[p]] satTop := (LinearEquiv.ofTop satTop rfl).symm
    let bTop : Basis (Fin d) ℤ_[p] satTop := b.map eTop
    let bQ_sub : Basis (Fin d) ℚ_[p] (⊤ : Submodule ℚ_[p] (Fin (Module.finrank ℤ_[p] M) → ℚ_[p])) :=
      basisOfSatLattice b₀ ⊤ satTop (fun _ => by simp [satTop]) bTop
    let bQ : Basis (Fin d) ℚ_[p] (Fin (Module.finrank ℤ_[p] M) → ℚ_[p]) :=
      bQ_sub.map Submodule.topEquiv
    have hbQ_apply : ∀ j : Fin d, bQ j = embedQ b₀ (b j) := fun j => by
      change (bQ_sub j : Fin (Module.finrank ℤ_[p] M) → ℚ_[p]) = embedQ b₀ (b j)
      rw [basisOfSatLattice_apply]
      rfl
    have hfilQ : ∀ i : ℤ, FL.toFilteredPhiModule.fil.fil i =
        Submodule.span ℚ_[p] { v | ∃ j : Fin d, i ≤ (h j : ℤ) ∧ v = bQ j } := by
      intro i
      change Submodule.span ℚ_[p] (embedQ b₀ '' (FL.fil i : Set M)) = _
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨x, hx, rfl⟩
        rw [SetLike.mem_coe, hfil_span i] at hx
        refine Submodule.span_induction
          (p := fun y _ => embedQ b₀ y ∈ Submodule.span ℚ_[p]
            { v | ∃ j : Fin d, i ≤ (h j : ℤ) ∧ v = bQ j })
          ?_ (by simp) (fun _ _ _ _ ha hb => by rw [map_add]; exact Submodule.add_mem _ ha hb)
          (fun c y _ ha => by
            rw [embedQ_smul]
            exact Submodule.smul_mem _ _ ha) hx
        rintro _ ⟨j, hj, rfl⟩
        exact Submodule.subset_span ⟨j, hj, (hbQ_apply j).symm⟩
      · rw [Submodule.span_le]
        rintro _ ⟨j, hj, rfl⟩
        rw [hbQ_apply j]
        refine Submodule.subset_span ⟨b j, ?_, rfl⟩
        rw [SetLike.mem_coe, hfil_span i]
        exact Submodule.subset_span ⟨j, hj, rfl⟩
    have htH : FL.toFilteredPhiModule.tH = ∑ j : Fin d, (h j : ℤ) :=
      tH_eq_sum_weights_of_basis bQ h FL.toFilteredPhiModule.fil hfilQ
    have htN : FL.toFilteredPhiModule.tN = ∑ j : Fin d, (h j : ℤ) := by
      unfold FilteredPhiModule.tN
      change Padic.valuation (LinearMap.det (extendQ b₀ FL.phi0)) = _
      rw [det_extendQ b₀ FL.phi0, hdet_phi0]
      obtain ⟨u, hu⟩ := hΨ_unit
      have hcast : ((LinearMap.det Ψ * (p : ℤ_[p]) ^ ∑ j : Fin d, h j : ℤ_[p]) : ℚ_[p]) =
          ((u : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ (∑ j : Fin d, h j) := by
        rw [← hu]; push_cast; rfl
      rw [hcast]
      have hu_ne : ((u : ℤ_[p]) : ℚ_[p]) ≠ 0 := by
        intro h0
        have hmul : ((u : ℤ_[p]) : ℚ_[p]) * (((u⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) = 1 := by
          exact_mod_cast congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) u.mul_inv
        rw [h0, zero_mul] at hmul
        exact zero_ne_one hmul
      have hp_ne : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
      rw [Padic.valuation_mul hu_ne (pow_ne_zero _ hp_ne), padic_valuation_padicInt_unit u,
        padic_valuation_p_pow, zero_add, Nat.cast_sum]
    rw [htH, htN]
  refine ⟨hend, ?_⟩
  intro U hU
  let satU : Submodule ℤ_[p] M :=
    { carrier := { x : M | embedQ b₀ x ∈ U }
      add_mem' := fun hx hy => by show embedQ b₀ (_ + _) ∈ U; rw [map_add]; exact U.add_mem hx hy
      zero_mem' := by show embedQ b₀ 0 ∈ U; rw [map_zero]; exact U.zero_mem
      smul_mem' := fun c x hx => by
        show embedQ b₀ (c • x) ∈ U
        rw [embedQ_smul]
        exact U.smul_mem (c : ℚ_[p]) hx }
  have : Module.Finite ℤ_[p] satU := (submodule_finite_free_padicInt satU).1
  have : Module.Free ℤ_[p] satU := (submodule_finite_free_padicInt satU).2
  let F_U : ℤ → Submodule ℤ_[p] satU := fun i => (FL.fil i).comap satU.subtype
  have hFU_ant : ∀ ⦃i j : ℤ⦄, i ≤ j → F_U j ≤ F_U i := fun _ _ hij =>
    Submodule.comap_mono (FL.antitone hij)
  have hFU_0 : F_U 0 = ⊤ := by ext ⟨x, _⟩; simp [F_U, FL.fil_zero]
  have hFU_top : F_U ((p - 1 : ℕ) : ℤ) = ⊥ := by
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    have hcast : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
    ext ⟨x, _⟩
    simp only [F_U, Submodule.mem_comap, Submodule.coe_subtype, hcast, FL.fil_top,
      Submodule.mem_bot]
    exact ⟨fun hx0 => Subtype.ext hx0, fun hx0 => congrArg Subtype.val hx0⟩
  have hFU_ds : ∀ i : ℤ, ∃ C' : Submodule ℤ_[p] satU, IsCompl (F_U i) C' := by
    intro i
    obtain ⟨Ci, hCi⟩ := FL.directSummand i
    let proj : satU →ₗ[ℤ_[p]] M :=
      Ci.subtype.comp ((Submodule.projectionOnto Ci (FL.fil i) hCi.symm).comp satU.subtype)
    have hker_eq : LinearMap.ker proj = F_U i := by
      ext ⟨x, hx⟩
      rw [LinearMap.mem_ker]
      change (Submodule.projectionOnto Ci (FL.fil i) hCi.symm x : M) = 0 ↔ x ∈ FL.fil i
      rw [Submodule.coe_eq_zero, ← LinearMap.mem_ker, Submodule.ker_projectionOnto]
    let eQ : (satU ⧸ F_U i) ≃ₗ[ℤ_[p]] LinearMap.range proj :=
      (Submodule.quotEquivOfEq (F_U i) (LinearMap.ker proj) hker_eq.symm).trans
        proj.quotKerEquivRange
    have : Module.Free ℤ_[p] (LinearMap.range proj) := (submodule_finite_free_padicInt _).2
    have : Module.Free ℤ_[p] (satU ⧸ F_U i) := Module.Free.of_equiv eQ.symm
    exact exists_isCompl_of_quot_free (F_U i)
  obtain ⟨r, b', h', hh'_lt, hFU_span⟩ :=
    exists_adapted_graded_basis (p - 1) F_U hFU_ant hFU_0 hFU_top hFU_ds
  let b'_Q : Basis (Fin r) ℚ_[p] U := basisOfSatLattice b₀ U satU (fun _ => Iff.rfl) b'
  have hb'_Q_apply : ∀ j : Fin r, (b'_Q j : Fin (Module.finrank ℤ_[p] M) → ℚ_[p]) =
      embedQ b₀ (b' j).1 := fun j => basisOfSatLattice_apply b₀ U satU (fun _ => Iff.rfl) b' j
  have hfilU_span : ∀ i : ℤ, (FL.toFilteredPhiModule.fil.inducedSub U).fil i =
      Submodule.span ℚ_[p] { v | ∃ j : Fin r, i ≤ (h' j : ℤ) ∧ v = b'_Q j } := by
    intro i
    apply le_antisymm
    · intro u hu
      have hu_fil : (u : Fin (Module.finrank ℤ_[p] M) → ℚ_[p]) ∈
          Submodule.span ℚ_[p] (embedQ b₀ '' (FL.fil i : Set M)) := hu
      have hclear : ∀ v ∈ Submodule.span ℚ_[p] (embedQ b₀ '' (FL.fil i : Set M)),
          ∃ (n : ℕ) (x : M), x ∈ FL.fil i ∧ (p : ℚ_[p]) ^ n • v = embedQ b₀ x := by
        classical
        intro v hv
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
        · rintro _ ⟨x, hx, rfl⟩
          exact ⟨0, x, hx, by simp⟩
        · exact ⟨0, 0, (FL.fil i).zero_mem, by simp⟩
        · rintro v₁ v₂ _ _ ⟨n₁, x₁, hx₁, h1⟩ ⟨n₂, x₂, hx₂, h2⟩
          refine ⟨n₁ + n₂, (p : ℤ_[p]) ^ n₂ • x₁ + (p : ℤ_[p]) ^ n₁ • x₂,
            (FL.fil i).add_mem ((FL.fil i).smul_mem _ hx₁) ((FL.fil i).smul_mem _ hx₂), ?_⟩
          rw [map_add, embedQ_smul, embedQ_smul, pow_add, smul_add]
          have hcast1 : (((p : ℤ_[p]) ^ n₂ : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) ^ n₂ := by push_cast; rfl
          have hcast2 : (((p : ℤ_[p]) ^ n₁ : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) ^ n₁ := by push_cast; rfl
          rw [hcast1, hcast2, ← h1, ← h2, smul_smul, smul_smul, mul_comm ((p : ℚ_[p]) ^ n₂)]
        · rintro c v _ ⟨n, x, hx, h1⟩
          let m : ℕ := if c = 0 then 0 else (-Padic.valuation c).toNat
          have hc_norm : ‖(p : ℚ_[p]) ^ m * c‖ ≤ 1 := by
            by_cases hc0 : c = 0
            · simp [hc0]
            · have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
              have hm : m = (-Padic.valuation c).toNat := if_neg hc0
              have hv_ge : 0 ≤ Padic.valuation ((p : ℚ_[p]) ^ m * c) := by
                rw [Padic.valuation_mul (pow_ne_zero m hp0) hc0, padic_valuation_p_pow]; omega
              exact padic_norm_le_one_of_valuation_nonneg hv_ge
          let cz : ℤ_[p] := ⟨(p : ℚ_[p]) ^ m * c, hc_norm⟩
          refine ⟨m + n, cz • x, (FL.fil i).smul_mem cz hx, ?_⟩
          rw [embedQ_smul, ← h1, smul_smul, smul_smul, pow_add]
          congr 1
          change (p : ℚ_[p]) ^ m * (p : ℚ_[p]) ^ n * c = (p : ℚ_[p]) ^ m * c * (p : ℚ_[p]) ^ n
          ring
      obtain ⟨n, x, hx_fil, hx_eq⟩ := hclear u.1 hu_fil
      have hx_sat : x ∈ satU := by
        show embedQ b₀ x ∈ U
        rw [← hx_eq]
        exact U.smul_mem ((p : ℚ_[p]) ^ n) u.2
      have hx_FU : (⟨x, hx_sat⟩ : satU) ∈ F_U i := hx_fil
      rw [hFU_span i] at hx_FU
      have hmem_emb : (⟨embedQ b₀ x, hx_sat⟩ : U) ∈
          Submodule.span ℚ_[p] { v | ∃ j : Fin r, i ≤ (h' j : ℤ) ∧ v = b'_Q j } := by
        refine Submodule.span_induction
          (p := fun (y : satU) _ => (⟨embedQ b₀ y.1, y.2⟩ : U) ∈
            Submodule.span ℚ_[p] { v | ∃ j : Fin r, i ≤ (h' j : ℤ) ∧ v = b'_Q j })
          ?_ ?_ ?_ ?_ hx_FU
        · rintro _ ⟨j, hj, rfl⟩
          exact Submodule.subset_span ⟨j, hj, Subtype.ext (hb'_Q_apply j).symm⟩
        · convert Submodule.zero_mem _ using 1
          exact Subtype.ext (map_zero _)
        · intro y₁ y₂ _ _ ih₁ ih₂
          convert Submodule.add_mem _ ih₁ ih₂ using 1
          exact Subtype.ext (map_add _ _ _)
        · intro c y _ ih
          convert Submodule.smul_mem _ (c : ℚ_[p]) ih using 1
          exact Subtype.ext (embedQ_smul b₀ c y.1)
      have hp_ne : (p : ℚ_[p]) ^ n ≠ 0 :=
        pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
      have hu_eq : u = ((p : ℚ_[p]) ^ n)⁻¹ • (⟨embedQ b₀ x, hx_sat⟩ : U) := by
        apply Subtype.ext
        change (u : Fin (Module.finrank ℤ_[p] M) → ℚ_[p]) = ((p : ℚ_[p]) ^ n)⁻¹ • embedQ b₀ x
        rw [← hx_eq, smul_smul, inv_mul_cancel₀ hp_ne, one_smul]
      rw [hu_eq]
      exact Submodule.smul_mem _ _ hmem_emb
    · rw [Submodule.span_le]
      rintro _ ⟨j, hj, rfl⟩
      have hbj : b' j ∈ F_U i := by
        rw [hFU_span i]
        exact Submodule.subset_span ⟨j, hj, rfl⟩
      change (b'_Q j : Fin (Module.finrank ℤ_[p] M) → ℚ_[p]) ∈
        Submodule.span ℚ_[p] (embedQ b₀ '' (FL.fil i : Set M))
      rw [hb'_Q_apply j]
      exact Submodule.subset_span ⟨(b' j).1, hbj, rfl⟩
  have htH_U : (FL.toFilteredPhiModule.restrictSub U hU).tH = ∑ j : Fin r, (h' j : ℤ) :=
    tH_eq_sum_weights_of_basis b'_Q h' (FL.toFilteredPhiModule.fil.inducedSub U) hfilU_span
  have hb'_fil : ∀ j : Fin r, (b' j).1 ∈ FL.fil (h' j : ℤ) := fun j => by
    have : b' j ∈ F_U (h' j : ℤ) := by rw [hFU_span (h' j : ℤ)]; exact Submodule.subset_span ⟨j, le_rfl, rfl⟩
    exact this
  have hdiv_mem_satU : ∀ j : Fin r, FL.phiDiv (h' j : ℤ) ⟨(b' j).1, hb'_fil j⟩ ∈ satU := fun j => by
    show embedQ b₀ (FL.phiDiv (h' j : ℤ) ⟨(b' j).1, hb'_fil j⟩) ∈ U
    have hpow := FL.phi0_eq_pow_smul_phiDiv (h' j) (hb'_fil j)
    have hφ_in : FL.toFilteredPhiModule.φ (embedQ b₀ (b' j).1) ∈ U := hU _ (b' j).2
    rw [hφ_emb, hpow, embedQ_smul] at hφ_in
    have hcastp : (((p : ℤ_[p]) ^ (h' j) : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) ^ (h' j) := by push_cast; rfl
    rw [hcastp] at hφ_in
    have hp_ne : (p : ℚ_[p]) ^ (h' j) ≠ 0 :=
      pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
    have hinv := U.smul_mem ((p : ℚ_[p]) ^ (h' j))⁻¹ hφ_in
    rwa [smul_smul, inv_mul_cancel₀ hp_ne, one_smul] at hinv
  let Ψ' : satU →ₗ[ℤ_[p]] satU :=
    b'.constr ℤ_[p] (fun j => ⟨FL.phiDiv (h' j : ℤ) ⟨(b' j).1, hb'_fil j⟩, hdiv_mem_satU j⟩)
  let Dp' : satU →ₗ[ℤ_[p]] satU :=
    b'.constr ℤ_[p] (fun j => (p : ℤ_[p]) ^ (h' j) • b' j)
  have hmat_eq : LinearMap.toMatrix b'_Q b'_Q (FL.toFilteredPhiModule.restrictSub U hU).φ.toLinearMap =
      (LinearMap.toMatrix b' b' (Ψ'.comp Dp')).map PadicInt.Coe.ringHom := by
    apply (LinearMap.toMatrix b'_Q b'_Q).symm.injective
    rw [LinearEquiv.symm_apply_apply]
    apply b'_Q.ext
    intro j
    have hLHS : (FL.toFilteredPhiModule.restrictSub U hU).φ.toLinearMap (b'_Q j) =
        (⟨embedQ b₀ (Ψ' (Dp' (b' j))).1, (Ψ' (Dp' (b' j))).2⟩ : U) := by
      apply Subtype.ext
      change FL.toFilteredPhiModule.φ (b'_Q j : Fin (Module.finrank ℤ_[p] M) → ℚ_[p]) =
        embedQ b₀ (Ψ' (Dp' (b' j))).1
      rw [hb'_Q_apply j, hφ_emb, FL.phi0_eq_pow_smul_phiDiv (h' j) (hb'_fil j)]
      congr 1
      simp only [Dp', Ψ', Basis.constr_basis, map_smul, Submodule.coe_smul_of_tower]
    rw [hLHS]
    rw [LinearMap.toMatrix_symm, Matrix.toLin_self]
    apply Subtype.ext
    rw [Submodule.coe_sum]
    have hrepr := (b'.sum_repr (Ψ' (Dp' (b' j)))).symm
    have h1 := congrArg (fun y : satU => embedQ b₀ y.1) hrepr
    rw [Submodule.coe_sum, map_sum] at h1
    refine h1.trans (Finset.sum_congr rfl fun i _ => ?_)
    change embedQ b₀ ((b'.repr (Ψ' (Dp' (b' j))) i) • (b' i).1) =
      (((LinearMap.toMatrix b' b' (Ψ'.comp Dp')) i j : ℤ_[p]) : ℚ_[p]) •
        (b'_Q i : Fin (Module.finrank ℤ_[p] M) → ℚ_[p])
    rw [embedQ_smul, hb'_Q_apply i, LinearMap.toMatrix_apply, LinearMap.comp_apply]
  have hdetU : LinearMap.det (FL.toFilteredPhiModule.restrictSub U hU).φ.toLinearMap =
      ((LinearMap.det Ψ' : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ (∑ j : Fin r, h' j) := by
    rw [← LinearMap.det_toMatrix b'_Q, hmat_eq, padicInt_map_det, LinearMap.det_toMatrix b',
      LinearMap.det_comp]
    have hDp'_mat : LinearMap.toMatrix b' b' Dp' =
        Matrix.diagonal (fun j : Fin r => (p : ℤ_[p]) ^ (h' j)) := by
      ext i j
      rw [LinearMap.toMatrix_apply]
      simp only [Dp', Basis.constr_basis, map_smul, Basis.repr_self, Finsupp.smul_apply,
        Finsupp.single_apply, Matrix.diagonal_apply, smul_eq_mul]
      by_cases hij : j = i
      · subst hij; simp
      · rw [if_neg hij, if_neg (Ne.symm hij), mul_zero]
    have hDp'_det : LinearMap.det Dp' = (p : ℤ_[p]) ^ (∑ j : Fin r, h' j) := by
      rw [← LinearMap.det_toMatrix b', hDp'_mat, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]
    rw [hDp'_det]
    push_cast
    rfl
  have hdetU_ne : LinearMap.det (FL.toFilteredPhiModule.restrictSub U hU).φ.toLinearMap ≠ 0 :=
    det_linearEquiv_ne_zero _
  rw [hdetU] at hdetU_ne
  have hΨ'_ne : ((LinearMap.det Ψ' : ℤ_[p]) : ℚ_[p]) ≠ 0 := left_ne_zero_of_mul hdetU_ne
  have hp_ne : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have htN_U : (FL.toFilteredPhiModule.restrictSub U hU).tN =
      Padic.valuation ((LinearMap.det Ψ' : ℤ_[p]) : ℚ_[p]) + ∑ j : Fin r, (h' j : ℤ) := by
    unfold FilteredPhiModule.tN
    rw [hdetU, Padic.valuation_mul hΨ'_ne (pow_ne_zero _ hp_ne), padic_valuation_p_pow, Nat.cast_sum]
  rw [htH_U, htN_U]
  have hnonneg : 0 ≤ Padic.valuation ((LinearMap.det Ψ' : ℤ_[p]) : ℚ_[p]) :=
    padic_valuation_padicInt_nonneg (LinearMap.det Ψ')
  linarith

/-! ### Mazur's Full Newton-Above-Hodge Polygon Theorem (Bridge to `Stage3DworkFrobenius`!) -/

/-- **Mazur's Full Newton-Above-Hodge Polygon Theorem for `FontaineLaffailleModule p`**
(directly bridging into `Stage3DworkFrobenius.polygonLe_of_fredholmDet_hodge_bound` and
`Stage2HodgeWeights.PolygonLe`!):
In an adapted basis `b : Basis (Fin d) ℤ_[p] M` with Hodge weights `h : Fin d → ℕ`, the matrix
`A : Matrix (Fin d) (Fin d) ℚ_[p]` of `FL.phi0` satisfies the exact column-decay bound
`‖A i j‖ ≤ ‖(p : ℚ_[p])‖ ^ (h j : ℝ)`, every coefficient of `fredholmDet A` satisfies
`‖(fredholmDet A).coeff k‖ ≤ ‖(p : ℚ_[p])‖ ^ (polygon H k : ℝ)` (`H = {h j}`), and whenever
`fredholmDet A` splits with rational Frobenius slopes `ν`, **`Stage2HodgeWeights.PolygonLe H N_slopes`**! -/
theorem fontaineLaffaille_newton_above_hodge_polygon (FL : FontaineLaffailleModule p M) :
    ∃ (d : ℕ) (h : Fin d → ℕ) (A : Matrix (Fin d) (Fin d) ℚ_[p]),
      let H : Multiset ℚ := (Finset.univ : Finset (Fin d)).val.map (fun j => (h j : ℚ))
      (∀ i j : Fin d, ‖A i j‖ ≤ ‖(p : ℚ_[p])‖ ^ (h j : ℝ)) ∧
      (∀ k : ℕ, k ≤ d → ‖(fredholmDet A).coeff k‖ ≤ ‖(p : ℚ_[p])‖ ^ (polygon H k : ℝ)) ∧
      (∀ (lam : Fin d → ℚ_[p]) (ν : Fin d → ℚ),
        fredholmDet A = ∏ i : Fin d, ((1 : Polynomial ℚ_[p]) - Polynomial.C (lam i) * Polynomial.X) →
        (∀ i : Fin d, ‖lam i‖ = ‖(p : ℚ_[p])‖ ^ (ν i : ℝ)) →
        H.sum = ((Finset.univ : Finset (Fin d)).val.map ν).sum →
        PolygonLe H ((Finset.univ : Finset (Fin d)).val.map ν)) := by
  classical
  obtain ⟨d, b, h, Ψ, _, _, hphi0_b, _, _⟩ := FL.exists_adapted_basis_unit_det
  let A : Matrix (Fin d) (Fin d) ℚ_[p] :=
    (LinearMap.toMatrix b b FL.phi0).map PadicInt.Coe.ringHom
  let H : Multiset ℚ := (Finset.univ : Finset (Fin d)).val.map (fun j => (h j : ℚ))
  have hp_prime : p.Prime := Fact.out
  have hp_pos : 0 < ‖(p : ℚ_[p])‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hp_prime.ne_zero)
  have hp_lt1 : ‖(p : ℚ_[p])‖ < 1 := by
    rw [Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp_prime.one_lt)
  have hA_col : ∀ i j : Fin d, ‖A i j‖ ≤ ‖(p : ℚ_[p])‖ ^ (h j : ℝ) := by
    intro i j
    have hAij : A i j = ((b.repr (Ψ (b j)) i : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ (h j) := by
      change ((LinearMap.toMatrix b b FL.phi0 i j : ℤ_[p]) : ℚ_[p]) = _
      rw [LinearMap.toMatrix_apply, hphi0_b j, map_smul, Finsupp.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [hAij, norm_mul, norm_pow, ← Real.rpow_natCast]
    have hz_le : ‖((b.repr (Ψ (b j)) i : ℤ_[p]) : ℚ_[p])‖ ≤ 1 := (b.repr (Ψ (b j)) i).2
    calc ‖((b.repr (Ψ (b j)) i : ℤ_[p]) : ℚ_[p])‖ * ‖(p : ℚ_[p])‖ ^ (h j : ℝ)
        ≤ 1 * ‖(p : ℚ_[p])‖ ^ (h j : ℝ) :=
          mul_le_mul_of_nonneg_right hz_le (Real.rpow_nonneg hp_pos.le _)
      _ = ‖(p : ℚ_[p])‖ ^ (h j : ℝ) := one_mul _
  have hcoeff : ∀ k : ℕ, k ≤ d →
      ‖(fredholmDet A).coeff k‖ ≤ ‖(p : ℚ_[p])‖ ^ (polygon H k : ℝ) := by
    intro k _
    rw [coeff_fredholmDet A k, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    refine PAdicChainValuation.ultrametric_norm_sum_le _ _ (Real.rpow_nonneg hp_pos.le _) fun σ _ => ?_
    have hsign : ‖Equiv.Perm.sign σ •
        ∑ S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin d)),
          if ∀ i ∉ S, σ i = i then ∏ i ∈ S, A (σ i) i else 0‖ =
        ‖∑ S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin d)),
          if ∀ i ∉ S, σ i = i then ∏ i ∈ S, A (σ i) i else 0‖ := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> simp [h1]
    rw [hsign]
    refine PAdicChainValuation.ultrametric_norm_sum_le _ _ (Real.rpow_nonneg hp_pos.le _) fun S hS => ?_
    rw [Finset.mem_powersetCard] at hS
    split_ifs
    · rw [norm_prod]
      calc ∏ i ∈ S, ‖A (σ i) i‖
          ≤ ∏ i ∈ S, ‖(p : ℚ_[p])‖ ^ (h i : ℝ) :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hA_col (σ i) i)
        _ = ‖(p : ℚ_[p])‖ ^ (∑ i ∈ S, (h i : ℝ)) := by
            rw [← Real.rpow_sum_of_pos hp_pos]
        _ ≤ ‖(p : ℚ_[p])‖ ^ (polygon H k : ℝ) := by
            refine Real.rpow_le_rpow_of_exponent_ge hp_pos hp_lt1.le ?_
            let T : Multiset ℚ := S.val.map (fun j : Fin d => (h j : ℚ))
            have hT_le : T ≤ H := Multiset.map_le_map (Finset.val_le_iff.mpr (Finset.subset_univ S))
            have hT_card : T.card = k := by simp [T, hS.2]
            have hpoly := polygon_le_sum_of_le hT_le
            rw [hT_card] at hpoly
            have hsum_cast : (T.sum : ℝ) = ∑ i ∈ S, (h i : ℝ) := by
              have hTsum : T.sum = ∑ j ∈ S, (h j : ℚ) := rfl
              rw [hTsum, Rat.cast_sum]
              refine Finset.sum_congr rfl fun i _ => by simp
            rw [← hsum_cast]
            exact_mod_cast hpoly
    · rw [norm_zero]
      exact Real.rpow_nonneg hp_pos.le _
  refine ⟨d, h, A, hA_col, hcoeff, fun lam ν hsplit hnorm hend => ?_⟩
  exact polygonLe_of_fredholmDet_hodge_bound hp_prime hp_lt1 (by simp)
    hsplit hnorm hcoeff hend

/-! ### Exact Sequences of Fontaine–Laffaille Modules & Exactness of Base Change -/

/-- A strict short exact sequence `0 → M₁ →[f] M₂ →[g] M₃ → 0` of `FontaineLaffailleModule p`s
over `ℤ_[p]`, preserving filtrations strictly and intertwining all divided Frobenii `φ_i`. -/
structure ExactSeq {M₁ M₂ M₃ : Type u}
    [AddCommGroup M₁] [Module ℤ_[p] M₁] [Module.Free ℤ_[p] M₁] [Module.Finite ℤ_[p] M₁]
    [AddCommGroup M₂] [Module ℤ_[p] M₂] [Module.Free ℤ_[p] M₂] [Module.Finite ℤ_[p] M₂]
    [AddCommGroup M₃] [Module ℤ_[p] M₃] [Module.Free ℤ_[p] M₃] [Module.Finite ℤ_[p] M₃]
    (FL₁ : FontaineLaffailleModule p M₁) (FL₂ : FontaineLaffailleModule p M₂)
    (FL₃ : FontaineLaffailleModule p M₃) where
  f : M₁ →ₗ[ℤ_[p]] M₂
  g : M₂ →ₗ[ℤ_[p]] M₃
  f_inj : Function.Injective f
  g_surj : Function.Surjective g
  exact : LinearMap.range f = LinearMap.ker g
  strict_sub : ∀ i : ℤ, FL₁.fil i = (FL₂.fil i).comap f
  strict_quot : ∀ i : ℤ, FL₃.fil i = (FL₂.fil i).map g
  phiDiv_left : ∀ (i : ℤ) (x : FL₁.fil i),
    f (FL₁.phiDiv i x) = FL₂.phiDiv i ⟨f x.1, by
      set v : M₁ := x.1
      have hv : v ∈ FL₁.fil i := x.2
      rw [strict_sub i] at hv
      exact hv⟩
  phiDiv_right : ∀ (i : ℤ) (x : FL₂.fil i),
    g (FL₂.phiDiv i x) = FL₃.phiDiv i ⟨g x.1, by rw [strict_quot i]; exact ⟨x.1, x.2, rfl⟩⟩

/-- **Exactness of `toFilteredPhiModule` on Short Exact Sequences of Fontaine–Laffaille Modules**:
Every `FontaineLaffailleModule.ExactSeq FL₁ FL₂ FL₃` maps to a strict
`FilteredPhiModule.ExactSeq FL₁.toFilteredPhiModule FL₂.toFilteredPhiModule FL₃.toFilteredPhiModule`
with exact rank additivity, exact Hodge-number additivity, and exact Newton-number additivity! -/
def ExactSeq.toFilteredPhiExactSeq {M₁ M₂ M₃ : Type u}
    [AddCommGroup M₁] [Module ℤ_[p] M₁] [Module.Free ℤ_[p] M₁] [Module.Finite ℤ_[p] M₁]
    [AddCommGroup M₂] [Module ℤ_[p] M₂] [Module.Free ℤ_[p] M₂] [Module.Finite ℤ_[p] M₂]
    [AddCommGroup M₃] [Module ℤ_[p] M₃] [Module.Free ℤ_[p] M₃] [Module.Finite ℤ_[p] M₃]
    {FL₁ : FontaineLaffailleModule p M₁} {FL₂ : FontaineLaffailleModule p M₂}
    {FL₃ : FontaineLaffailleModule p M₃}
    (E : ExactSeq FL₁ FL₂ FL₃) :
    FilteredPhiModule.ExactSeq FL₁.toFilteredPhiModule FL₂.toFilteredPhiModule
      FL₃.toFilteredPhiModule := by
  let b₁ := canonBasis (p := p) M₁
  let b₂ := canonBasis (p := p) M₂
  let b₃ := canonBasis (p := p) M₃
  let fQ : (Fin (Module.finrank ℤ_[p] M₁) → ℚ_[p]) →ₗ[ℚ_[p]]
      (Fin (Module.finrank ℤ_[p] M₂) → ℚ_[p]) :=
    Matrix.toLin' ((LinearMap.toMatrix b₁ b₂ E.f).map PadicInt.Coe.ringHom)
  let gQ : (Fin (Module.finrank ℤ_[p] M₂) → ℚ_[p]) →ₗ[ℚ_[p]]
      (Fin (Module.finrank ℤ_[p] M₃) → ℚ_[p]) :=
    Matrix.toLin' ((LinearMap.toMatrix b₂ b₃ E.g).map PadicInt.Coe.ringHom)
  have hfQ_emb : ∀ x : M₁, fQ (embedQ b₁ x) = embedQ b₂ (E.f x) := fun x => by
    ext i
    have hi := congrFun (LinearMap.toMatrix_mulVec_repr b₁ b₂ E.f x) i
    have hcast := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hi
    simpa [fQ, Matrix.mulVec, dotProduct, embedQ] using hcast
  have hgQ_emb : ∀ x : M₂, gQ (embedQ b₂ x) = embedQ b₃ (E.g x) := fun x => by
    ext i
    have hi := congrFun (LinearMap.toMatrix_mulVec_repr b₂ b₃ E.g x) i
    have hcast := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hi
    simpa [gQ, Matrix.mulVec, dotProduct, embedQ] using hcast
  have hfQ_inj : Function.Injective fQ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker] at hv
    obtain ⟨n, x, hx⟩ := exists_pow_p_smul_mem_range_embedQ b₁ v
    have hfx0 : embedQ b₂ (E.f x) = 0 := by rw [← hfQ_emb, ← hx, map_smul, hv, smul_zero]
    have hfx0' : E.f x = 0 := embedQ_injective b₂ (by rw [hfx0, map_zero])
    have hx0 : x = 0 := E.f_inj (by rw [hfx0', map_zero])
    rw [hx0, map_zero] at hx
    have hp_ne : (p : ℚ_[p]) ^ n ≠ 0 :=
      pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
    rw [Submodule.mem_bot]
    exact (smul_eq_zero.mp hx).resolve_left hp_ne
  have hgQ_surj : Function.Surjective gQ := by
    intro w
    obtain ⟨n, z, hz⟩ := exists_pow_p_smul_mem_range_embedQ b₃ w
    obtain ⟨y, rfl⟩ := E.g_surj z
    have hp_ne : (p : ℚ_[p]) ^ n ≠ 0 :=
      pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
    refine ⟨((p : ℚ_[p]) ^ n)⁻¹ • embedQ b₂ y, ?_⟩
    rw [map_smul, hgQ_emb, ← hz, smul_smul, inv_mul_cancel₀ hp_ne, one_smul]
  have hexactQ : LinearMap.range fQ = LinearMap.ker gQ := by
    ext v
    constructor
    · rintro ⟨u, rfl⟩
      rw [LinearMap.mem_ker]
      obtain ⟨n, x, hx⟩ := exists_pow_p_smul_mem_range_embedQ b₁ u
      have h0 : (p : ℚ_[p]) ^ n • gQ (fQ u) = 0 := by
        rw [← map_smul, ← map_smul, hx, hfQ_emb, hgQ_emb]
        have hgf : E.g (E.f x) = 0 := LinearMap.mem_ker.mp (E.exact ▸ ⟨x, rfl⟩)
        rw [hgf, map_zero]
      have hp_ne : (p : ℚ_[p]) ^ n ≠ 0 :=
        pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
      exact (smul_eq_zero.mp h0).resolve_left hp_ne
    · intro hv
      rw [LinearMap.mem_ker] at hv
      obtain ⟨n, y, hy⟩ := exists_pow_p_smul_mem_range_embedQ b₂ v
      have hgy0 : E.g y = 0 := embedQ_injective b₃ (by
        rw [map_zero, ← hgQ_emb, ← hy, map_smul, hv, smul_zero])
      obtain ⟨x, hx⟩ := E.exact.symm ▸ (LinearMap.mem_ker.mpr hgy0)
      have hp_ne : (p : ℚ_[p]) ^ n ≠ 0 :=
        pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
      refine ⟨((p : ℚ_[p]) ^ n)⁻¹ • embedQ b₁ x, ?_⟩
      rw [map_smul, hfQ_emb, hx, ← hy, smul_smul, inv_mul_cancel₀ hp_ne, one_smul]
  have hclear_fil : ∀ (i : ℤ) {M' : Type u} [AddCommGroup M'] [Module ℤ_[p] M']
      [Module.Free ℤ_[p] M'] [Module.Finite ℤ_[p] M'] (FL' : FontaineLaffailleModule p M')
      (b' : Basis (Fin (Module.finrank ℤ_[p] M')) ℤ_[p] M')
      (v : Fin (Module.finrank ℤ_[p] M') → ℚ_[p]),
      v ∈ Submodule.span ℚ_[p] (embedQ b' '' (FL'.fil i : Set M')) →
        ∃ (n : ℕ) (x : M'), x ∈ FL'.fil i ∧ (p : ℚ_[p]) ^ n • v = embedQ b' x := by
    classical
    intro i M' _ _ _ _ FL' b' v hv
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨x, hx, rfl⟩; exact ⟨0, x, hx, by simp⟩
    · exact ⟨0, 0, (FL'.fil i).zero_mem, by simp⟩
    · rintro v₁ v₂ _ _ ⟨n₁, x₁, hx₁, h1⟩ ⟨n₂, x₂, hx₂, h2⟩
      refine ⟨n₁ + n₂, (p : ℤ_[p]) ^ n₂ • x₁ + (p : ℤ_[p]) ^ n₁ • x₂,
        (FL'.fil i).add_mem ((FL'.fil i).smul_mem _ hx₁) ((FL'.fil i).smul_mem _ hx₂), ?_⟩
      rw [map_add, embedQ_smul, embedQ_smul, pow_add, smul_add]
      have hcast1 : (((p : ℤ_[p]) ^ n₂ : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) ^ n₂ := by push_cast; rfl
      have hcast2 : (((p : ℤ_[p]) ^ n₁ : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) ^ n₁ := by push_cast; rfl
      rw [hcast1, hcast2, ← h1, ← h2, smul_smul, smul_smul, mul_comm ((p : ℚ_[p]) ^ n₂)]
    · rintro c v _ ⟨n, x, hx, h1⟩
      let m : ℕ := if c = 0 then 0 else (-Padic.valuation c).toNat
      have hc_norm : ‖(p : ℚ_[p]) ^ m * c‖ ≤ 1 := by
        by_cases hc0 : c = 0
        · simp [hc0]
        · have hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
          have hm : m = (-Padic.valuation c).toNat := if_neg hc0
          have hv_ge : 0 ≤ Padic.valuation ((p : ℚ_[p]) ^ m * c) := by
            rw [Padic.valuation_mul (pow_ne_zero m hp0) hc0, padic_valuation_p_pow]; omega
          exact padic_norm_le_one_of_valuation_nonneg hv_ge
      let cz : ℤ_[p] := ⟨(p : ℚ_[p]) ^ m * c, hc_norm⟩
      refine ⟨m + n, cz • x, (FL'.fil i).smul_mem cz hx, ?_⟩
      rw [embedQ_smul, ← h1, smul_smul, smul_smul, pow_add]
      congr 1
      change (p : ℚ_[p]) ^ m * (p : ℚ_[p]) ^ n * c = (p : ℚ_[p]) ^ m * c * (p : ℚ_[p]) ^ n
      ring
  refine
    { ses :=
        { f := fQ
          g := gQ
          f_inj := hfQ_inj
          g_surj := hgQ_surj
          exact := hexactQ
          strict_sub := fun i => by
            apply le_antisymm
            · change Submodule.span ℚ_[p] (embedQ b₁ '' (FL₁.fil i : Set M₁)) ≤ _
              rw [Submodule.span_le]
              rintro _ ⟨x, hx, rfl⟩
              change fQ (embedQ b₁ x) ∈ Submodule.span ℚ_[p] (embedQ b₂ '' (FL₂.fil i : Set M₂))
              rw [hfQ_emb]
              have hfx_mem : E.f x ∈ FL₂.fil i := by
                have h := hx
                rw [SetLike.mem_coe, E.strict_sub i] at h
                exact h
              exact Submodule.subset_span ⟨E.f x, hfx_mem, rfl⟩
            · intro u hu
              obtain ⟨n, y, hy_fil, hy_eq⟩ := hclear_fil i FL₂ b₂ (fQ u) hu
              obtain ⟨m, x, hx_eq⟩ := exists_pow_p_smul_mem_range_embedQ b₁ u
              have heq_emb : embedQ b₂ ((p : ℤ_[p]) ^ m • y) = embedQ b₂ ((p : ℤ_[p]) ^ n • E.f x) := by
                rw [embedQ_smul, embedQ_smul]
                have hcm : (((p : ℤ_[p]) ^ m : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) ^ m := by push_cast; rfl
                have hcn : (((p : ℤ_[p]) ^ n : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) ^ n := by push_cast; rfl
                rw [hcm, hcn, ← hy_eq, ← hfQ_emb, ← hx_eq, map_smul, smul_comm]
              have heq_M2 : (p : ℤ_[p]) ^ m • y = E.f ((p : ℤ_[p]) ^ n • x) := by
                rw [map_smul]; exact embedQ_injective b₂ heq_emb
              have hfx_fil : E.f ((p : ℤ_[p]) ^ n • x) ∈ FL₂.fil i :=
                heq_M2 ▸ (FL₂.fil i).smul_mem _ hy_fil
              have hpx_fil : (p : ℤ_[p]) ^ n • x ∈ FL₁.fil i := by
                rw [E.strict_sub i]; exact hfx_fil
              have hp_ne : (p : ℚ_[p]) ^ (n + m) ≠ 0 :=
                pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
              have hu_eq : u = ((p : ℚ_[p]) ^ (n + m))⁻¹ • embedQ b₁ ((p : ℤ_[p]) ^ n • x) := by
                rw [embedQ_smul]
                have hcn : (((p : ℤ_[p]) ^ n : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) ^ n := by push_cast; rfl
                rw [hcn, ← hx_eq, smul_smul, smul_smul, mul_assoc, ← pow_add, inv_mul_cancel₀ hp_ne,
                  one_smul]
              rw [hu_eq]
              exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hpx_fil, rfl⟩)
          strict_quot := fun i => by
            change Submodule.span ℚ_[p] (embedQ b₃ '' (FL₃.fil i : Set M₃)) =
              (Submodule.span ℚ_[p] (embedQ b₂ '' (FL₂.fil i : Set M₂))).map gQ
            rw [Submodule.map_span, ← Set.image_comp]
            congr 1
            ext w
            simp only [Set.mem_image, SetLike.mem_coe, Function.comp_apply, hgQ_emb, E.strict_quot i]
            exact ⟨by rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨y, hy, rfl⟩,
              by rintro ⟨y, hy, rfl⟩; exact ⟨E.g y, ⟨y, hy, rfl⟩, rfl⟩⟩ }
      comm_left := fun u => by
        obtain ⟨n, x, hx⟩ := exists_pow_p_smul_mem_range_embedQ b₁ u
        have hp_ne : (p : ℚ_[p]) ^ n ≠ 0 :=
          pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
        apply smul_right_injective (Fin (Module.finrank ℤ_[p] M₂) → ℚ_[p]) hp_ne
        dsimp only
        rw [← map_smul, ← map_smul, ← map_smul, ← map_smul, hx, hfQ_emb]
        change extendQ b₂ FL₂.phi0 (embedQ b₂ (E.f x)) = fQ (extendQ b₁ FL₁.phi0 (embedQ b₁ x))
        rw [extendQ_embedQ, extendQ_embedQ, hfQ_emb]
        congr 1
        exact (E.phiDiv_left 0 ⟨x, by rw [FL₁.fil_zero]; trivial⟩).symm
      comm_right := fun v => by
        obtain ⟨n, y, hy⟩ := exists_pow_p_smul_mem_range_embedQ b₂ v
        have hp_ne : (p : ℚ_[p]) ^ n ≠ 0 :=
          pow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
        apply smul_right_injective (Fin (Module.finrank ℤ_[p] M₃) → ℚ_[p]) hp_ne
        dsimp only
        rw [← map_smul, ← map_smul, ← map_smul, ← map_smul, hy, hgQ_emb]
        change gQ (extendQ b₂ FL₂.phi0 (embedQ b₂ y)) = extendQ b₃ FL₃.phi0 (embedQ b₃ (E.g y))
        rw [extendQ_embedQ, extendQ_embedQ, hgQ_emb]
        congr 1
        exact E.phiDiv_right 0 ⟨y, by rw [FL₂.fil_zero]; trivial⟩ }

/-! ### Concrete 2-Dimensional Fontaine–Laffaille Modules `fontaineLaffaille2D` for `Δ₁₂..Δ₂₂` -/

/-- Standard rank-1 direct summand `L₀(ℤ_[p]) = span {e₀} ≤ (Fin 2 → ℤ_[p])`. -/
def stdHodgeLineZp (p : ℕ) [Fact p.Prime] : Submodule ℤ_[p] (Fin 2 → ℤ_[p]) :=
  Submodule.span ℤ_[p] {Pi.single (0 : Fin 2) (1 : ℤ_[p])}

theorem stdHodgeLineZp_isCompl (p : ℕ) [Fact p.Prime] :
    IsCompl (stdHodgeLineZp p) (Submodule.span ℤ_[p] {Pi.single (1 : Fin 2) (1 : ℤ_[p])}) := by
  rw [isCompl_iff]
  constructor
  · rw [disjoint_iff, eq_bot_iff]
    rintro v ⟨h0, h1⟩
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h0
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp h1
    have hv0 : v 0 = 0 := by rw [← hb]; simp
    have hv1 : v 1 = 0 := by rw [← ha]; simp
    rw [Submodule.mem_bot]
    ext i; fin_cases i <;> assumption
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have h0 : v 0 • Pi.single (0 : Fin 2) (1 : ℤ_[p]) ∈ stdHodgeLineZp p :=
      Submodule.mem_span_singleton.mpr ⟨v 0, rfl⟩
    have h1 : v 1 • Pi.single (1 : Fin 2) (1 : ℤ_[p]) ∈
        Submodule.span ℤ_[p] {Pi.single (1 : Fin 2) (1 : ℤ_[p])} :=
      Submodule.mem_span_singleton.mpr ⟨v 1, rfl⟩
    have hadd := Submodule.add_mem_sup h0 h1
    convert hadd using 1
    ext i; fin_cases i <;> simp

/-- Filtration for the concrete 2D Fontaine–Laffaille module of weight `k`. -/
def fl2DFil (p : ℕ) [Fact p.Prime] (k : ℕ) (i : ℤ) : Submodule ℤ_[p] (Fin 2 → ℤ_[p]) :=
  if i ≤ 0 then ⊤ else if i ≤ (k - 1 : ℤ) then stdHodgeLineZp p else ⊥

/-- Divided Frobenius `φ_i : fl2DFil p k i →ₗ[ℤ_[p]] (Fin 2 → ℤ_[p])` for `fontaineLaffaille2D`. -/
def fl2DPhiDiv (p : ℕ) [Fact p.Prime] (k : ℕ) (a_p : ℤ_[p]) (i : ℤ) :
    fl2DFil p k i →ₗ[ℤ_[p]] (Fin 2 → ℤ_[p]) :=
  if i ≤ 0 then
    ((p : ℤ_[p]) ^ (-i).toNat) •
      (Matrix.toLin' (!![0, -1; (p : ℤ_[p]) ^ (k - 1), a_p] : Matrix (Fin 2) (Fin 2) ℤ_[p])).comp
        (fl2DFil p k i).subtype
  else if i ≤ (k - 1 : ℤ) then
    { toFun := fun v => ((p : ℤ_[p]) ^ (k - 1 - i.toNat) * v.1 0) • Pi.single (1 : Fin 2) 1
      map_add' := fun x y => by simp [mul_add, add_smul]
      map_smul' := fun c x => by
        ext j
        simp only [Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  else 0

/-- **Concrete 2D Fontaine–Laffaille Module `fontaineLaffaille2D p k a_p`** over `ℤ_[p]`
for EVERY prime `p`, EVERY weight `k` in the Fontaine–Laffaille range `2 ≤ k ≤ p - 1`
(i.e. `0 < k - 1 < p - 1`), and EVERY integral Frobenius trace `a_p ∈ ℤ_[p]`:
- Filtration: `Fil^0 = ℤ_[p]²`, `Fil^1 = ... = Fil^{k-1} = span {e₀}`, `Fil^k = ... = Fil^{p-1} = 0`.
- Divided Frobenii: `φ_0 = !![0, -1; p^{k-1}, a_p]` and `φ_i(c • e₀) = (p^{k-1-i} * c) • e₁`
  (`1 ≤ i ≤ k - 1`), satisfying `im(φ_0) + im(φ_{k-1}) = ℤ_[p]²` unconditionally! -/
def fontaineLaffaille2D (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 2 ≤ k) (hk_lt : k ≤ p - 1)
    (a_p : ℤ_[p]) : FontaineLaffailleModule p (Fin 2 → ℤ_[p]) where
  fil := fl2DFil p k
  antitone i j hij := by unfold fl2DFil; split_ifs <;> simp_all <;> omega
  fil_zero := by simp [fl2DFil]
  fil_top := by unfold fl2DFil; rw [if_neg (by omega), if_neg (by omega)]
  directSummand i := by
    unfold fl2DFil
    by_cases h0 : i ≤ 0
    · rw [if_pos h0]; exact ⟨⊥, isCompl_top_bot⟩
    · rw [if_neg h0]
      by_cases hle : i ≤ (k - 1 : ℤ)
      · rw [if_pos hle]; exact ⟨_, stdHodgeLineZp_isCompl p⟩
      · rw [if_neg hle]; exact ⟨⊤, isCompl_bot_top⟩
  phiDiv := fl2DPhiDiv p k a_p
  phiDiv_compat i x := by
    unfold fl2DPhiDiv
    by_cases hi1 : i + 1 ≤ 0
    · have hi0 : i ≤ 0 := by omega
      simp only [hi0, hi1, ↓reduceIte, LinearMap.smul_apply, LinearMap.comp_apply,
        Submodule.coe_subtype]
      have hexp : (-i).toNat = (-(i + 1)).toNat + 1 := by omega
      rw [hexp, pow_succ', mul_smul]
    · by_cases hi0 : i ≤ 0
      · have hi_eq : i = 0 := by omega
        subst hi_eq
        simp only [le_refl, ↓reduceIte, zero_add, show ¬ ((1 : ℤ) ≤ 0) by omega,
          show (1 : ℤ) ≤ (k - 1 : ℤ) by omega, neg_zero, Int.toNat_zero, pow_zero, one_smul,
          LinearMap.comp_apply, Submodule.coe_subtype, LinearMap.coe_mk, AddHom.coe_mk]
        have hxL : x.1 ∈ stdHodgeLineZp p := by
          have hx' := x.2
          simp only [fl2DFil, zero_add, show ¬ ((1 : ℤ) ≤ 0) by omega,
            show (1 : ℤ) ≤ (k - 1 : ℤ) by omega, ↓reduceIte] at hx'
          exact hx'
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxL
        have hx0 : x.1 0 = c := by rw [← hc]; simp
        have hx1 : x.1 1 = 0 := by rw [← hc]; simp
        ext j
        fin_cases j
        · change (!![0, -1; (p : ℤ_[p]) ^ (k - 1), a_p].mulVec x.1) 0 = _
          simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hx1]
        · change (!![0, -1; (p : ℤ_[p]) ^ (k - 1), a_p].mulVec x.1) 1 = _
          have h1 : (!![0, -1; (p : ℤ_[p]) ^ (k - 1), a_p].mulVec x.1) 1 =
              (p : ℤ_[p]) ^ (k - 1) * x.1 0 + a_p * x.1 1 := by
            simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
          rw [h1, hx0, hx1, mul_zero, add_zero]
          change (p : ℤ_[p]) ^ (k - 1) * c =
            (p : ℤ_[p]) * (((p : ℤ_[p]) ^ (k - 1 - (1 : ℤ).toNat) * c) *
              ((Pi.single (1 : Fin 2) (1 : ℤ_[p]) : Fin 2 → ℤ_[p]) 1))
          rw [Pi.single_eq_same, mul_one]
          have hexp : k - 1 = (k - 1 - (1 : ℤ).toNat) + 1 := by omega
          conv_lhs => rw [hexp, pow_succ']
          ring
      · by_cases hi_le : i + 1 ≤ (k - 1 : ℤ)
        · have hi_le' : i ≤ (k - 1 : ℤ) := by omega
          simp only [hi0, hi1, hi_le, hi_le', ↓reduceIte, LinearMap.coe_mk, AddHom.coe_mk]
          have hexp : k - 1 - i.toNat = (k - 1 - (i + 1).toNat) + 1 := by omega
          rw [hexp, pow_succ', mul_assoc, mul_smul]
        · have hx0 : x.1 = 0 := by
            have hx' := x.2
            simp only [fl2DFil, hi1, hi_le, ↓reduceIte, Submodule.mem_bot] at hx'
            exact hx'
          simp only [hi0, hi1, hi_le, ↓reduceIte, LinearMap.zero_apply, smul_zero]
          by_cases hile : i ≤ (k - 1 : ℤ)
          · rw [if_pos hile]
            simp [hx0]
          · rw [if_neg hile]
            rfl
  phiDiv_surj := by
    rw [eq_top_iff]
    have h0_mem : (0 : ℤ) ∈ Finset.Icc (0 : ℤ) ((p : ℤ) - 2) := by
      rw [Finset.mem_Icc]; have := (Fact.out : p.Prime).two_le; omega
    have hw_mem : (k - 1 : ℤ) ∈ Finset.Icc (0 : ℤ) ((p : ℤ) - 2) := by
      rw [Finset.mem_Icc]; omega
    let e₀ : Fin 2 → ℤ_[p] := Pi.single 0 1
    let e₁ : Fin 2 → ℤ_[p] := Pi.single 1 1
    have he₁_in : e₁ ∈ ⨆ i ∈ Finset.Icc (0 : ℤ) ((p : ℤ) - 2),
        LinearMap.range (fl2DPhiDiv p k a_p i) := by
      refine Submodule.mem_iSup_of_mem (k - 1 : ℤ) (Submodule.mem_iSup_of_mem hw_mem ?_)
      have he0_fil : e₀ ∈ fl2DFil p k (k - 1 : ℤ) := by
        unfold fl2DFil
        rw [if_neg (by omega), if_pos le_rfl]
        exact Submodule.subset_span (Set.mem_singleton _)
      refine ⟨⟨e₀, he0_fil⟩, ?_⟩
      unfold fl2DPhiDiv
      rw [if_neg (by omega), if_pos le_rfl]
      change ((p : ℤ_[p]) ^ (k - 1 - (k - 1 : ℤ).toNat) * e₀ 0) • Pi.single (1 : Fin 2) 1 = e₁
      have hsub0 : k - 1 - (k - 1 : ℤ).toNat = 0 := by omega
      rw [hsub0, pow_zero, one_mul]
      simp [e₀, e₁]
    have hphi0_e1 : -e₀ + a_p • e₁ ∈ ⨆ i ∈ Finset.Icc (0 : ℤ) ((p : ℤ) - 2),
        LinearMap.range (fl2DPhiDiv p k a_p i) := by
      refine Submodule.mem_iSup_of_mem (0 : ℤ) (Submodule.mem_iSup_of_mem h0_mem ?_)
      refine ⟨⟨e₁, by simp [fl2DFil]⟩, ?_⟩
      unfold fl2DPhiDiv
      rw [if_pos le_rfl]
      simp only [neg_zero, Int.toNat_zero, pow_zero, one_smul, LinearMap.comp_apply,
        Submodule.coe_subtype]
      ext j; fin_cases j <;> simp [e₀, e₁, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have he₀_in : e₀ ∈ ⨆ i ∈ Finset.Icc (0 : ℤ) ((p : ℤ) - 2),
        LinearMap.range (fl2DPhiDiv p k a_p i) := by
      have hsub := Submodule.sub_mem _ (Submodule.smul_mem _ a_p he₁_in) hphi0_e1
      convert hsub using 1
      ext j; fin_cases j <;> simp [e₀, e₁]
    intro v _
    have hv : v = v 0 • e₀ + v 1 • e₁ := by ext j; fin_cases j <;> simp [e₀, e₁]
    rw [hv]
    exact Submodule.add_mem _ (Submodule.smul_mem _ (v 0) he₀_in) (Submodule.smul_mem _ (v 1) he₁_in)

/-- Every `fontaineLaffaille2D p k a_p` (`2 ≤ k ≤ p - 1`) is unconditionally weakly admissible
via Mazur's Theorem (`fontaineLaffaille_implies_weaklyAdmissible`)! -/
theorem fontaineLaffaille2D_weaklyAdmissible (p : ℕ) [Fact p.Prime] (k : ℕ)
    (hk : 2 ≤ k) (hk_lt : k ≤ p - 1) (a_p : ℤ_[p]) :
    (fontaineLaffaille2D p k hk hk_lt a_p).toFilteredPhiModule.IsWeaklyAdmissible :=
  fontaineLaffaille_implies_weaklyAdmissible (fontaineLaffaille2D p k hk hk_lt a_p)

/-- Concrete Fontaine–Laffaille realization of `fontaineLaffaille2D p k a_p` is regular 2D of
weights `{0, k - 1}` with exact Hodge line `Fil^1`! -/
theorem fontaineLaffaille2D_isRegularDim2 (p : ℕ) [Fact p.Prime] (k : ℕ)
    (hk : 2 ≤ k) (hk_lt : k ≤ p - 1) (a_p : ℤ_[p]) :
    let FL := fontaineLaffaille2D p k hk hk_lt a_p
    IsRegularDim2 FL.toFilteredPhiModule k (FL.toFilteredPhiModule.fil.fil 1) := by
  intro FL
  have hdim_M : Module.finrank ℤ_[p] (Fin 2 → ℤ_[p]) = 2 := by simp
  have hdim_Q : Module.finrank ℚ_[p] (Fin (Module.finrank ℤ_[p] (Fin 2 → ℤ_[p])) → ℚ_[p]) = 2 := by
    rw [Module.finrank_pi, hdim_M, Fintype.card_fin]
  let b₀ := canonBasis (p := p) (Fin 2 → ℤ_[p])
  have hL_span : FL.toFilteredPhiModule.fil.fil 1 =
      Submodule.span ℚ_[p] {embedQ b₀ (Pi.single (0 : Fin 2) (1 : ℤ_[p]))} := by
    change Submodule.span ℚ_[p] (embedQ b₀ '' (FL.fil 1 : Set (Fin 2 → ℤ_[p]))) = _
    have h1 : FL.fil 1 = stdHodgeLineZp p := by
      simp [FL, fontaineLaffaille2D, fl2DFil, show ¬ ((1 : ℤ) ≤ 0) by omega,
        show (1 : ℤ) ≤ (k - 1 : ℤ) by omega]
    rw [h1]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [embedQ_smul]
      exact Submodule.mem_span_singleton.mpr ⟨(c : ℚ_[p]), rfl⟩
    · rw [Submodule.span_le]
      rintro _ rfl
      exact Submodule.subset_span ⟨Pi.single 0 1, Submodule.subset_span (Set.mem_singleton _), rfl⟩
  have he0_ne : embedQ b₀ (Pi.single (0 : Fin 2) (1 : ℤ_[p])) ≠ 0 := by
    intro h0
    have h1 := embedQ_injective b₀ (h0.trans (map_zero _).symm)
    have h2 := congrFun h1 0
    simp at h2
  refine ⟨hk, hdim_Q, ?_, ?_⟩
  · rw [hL_span, finrank_span_singleton he0_ne]
  · intro i
    by_cases h0 : i ≤ 0
    · rw [if_pos h0]
      exact FL.toFilteredPhiModule.fil.eq_top_of_le i h0
    · rw [if_neg h0]
      by_cases hle : i ≤ (k - 1 : ℤ)
      · rw [if_pos hle]
        change Submodule.span ℚ_[p] (embedQ b₀ '' (FL.fil i : Set _)) =
          Submodule.span ℚ_[p] (embedQ b₀ '' (FL.fil 1 : Set _))
        have hEq : FL.fil i = FL.fil 1 := by
          simp [FL, fontaineLaffaille2D, fl2DFil, h0, hle, show ¬ ((1 : ℤ) ≤ 0) by omega,
            show (1 : ℤ) ≤ (k - 1 : ℤ) by omega]
        rw [hEq]
      · rw [if_neg hle]
        change Submodule.span ℚ_[p] (embedQ b₀ '' (FL.fil i : Set _)) = ⊥
        have hbot : FL.fil i = ⊥ := by simp [FL, fontaineLaffaille2D, fl2DFil, h0, hle]
        rw [hbot, eq_bot_iff, Submodule.span_le]
        rintro _ ⟨x, hx, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_bot] at hx
        rw [hx, map_zero]
        exact Submodule.zero_mem ⊥

/-- Explicit Fontaine–Laffaille modules for all five 1D eigenforms `Δ₁₂, Δ₁₆, Δ₁₈, Δ₂₀, Δ₂₂`
in the Fontaine–Laffaille range `p > k` (`k ≤ p - 1`): each is unconditionally weakly admissible! -/
theorem delta12_to_delta22_fontaineLaffaille_weaklyAdmissible (p : ℕ) [Fact p.Prime] :
    (∀ h : 12 ≤ p - 1, (fontaineLaffaille2D p 12 (by omega) h (ramanujanTau p : ℤ_[p])).toFilteredPhiModule.IsWeaklyAdmissible) ∧
    (∀ h : 16 ≤ p - 1, (fontaineLaffaille2D p 16 (by omega) h (coeffDelta16Z p : ℤ_[p])).toFilteredPhiModule.IsWeaklyAdmissible) ∧
    (∀ h : 18 ≤ p - 1, (fontaineLaffaille2D p 18 (by omega) h (coeffDelta18Z p : ℤ_[p])).toFilteredPhiModule.IsWeaklyAdmissible) ∧
    (∀ h : 20 ≤ p - 1, (fontaineLaffaille2D p 20 (by omega) h (coeffDelta20Z p : ℤ_[p])).toFilteredPhiModule.IsWeaklyAdmissible) ∧
    (∀ h : 22 ≤ p - 1, (fontaineLaffaille2D p 22 (by omega) h (coeffDelta22Z p : ℤ_[p])).toFilteredPhiModule.IsWeaklyAdmissible) :=
  ⟨fun h => fontaineLaffaille2D_weaklyAdmissible p 12 (by omega) h (ramanujanTau p : ℤ_[p]),
   fun h => fontaineLaffaille2D_weaklyAdmissible p 16 (by omega) h (coeffDelta16Z p : ℤ_[p]),
   fun h => fontaineLaffaille2D_weaklyAdmissible p 18 (by omega) h (coeffDelta18Z p : ℤ_[p]),
   fun h => fontaineLaffaille2D_weaklyAdmissible p 20 (by omega) h (coeffDelta20Z p : ℤ_[p]),
   fun h => fontaineLaffaille2D_weaklyAdmissible p 22 (by omega) h (coeffDelta22Z p : ℤ_[p])⟩

end FontaineLaffailleModule

end FontaineLaffailleSection

/-! ## Section 5: Crystalline Deformation Tangent Space `H¹_f(ℚ_p, Ad(D))` & `dim_crystalline_tangent_eq` -/

section CrystallineTangentDimension

variable {p : ℕ} [Fact p.Prime]
variable {D : Type u} [AddCommGroup D] [Module ℚ_[p] D] [Module.Finite ℚ_[p] D]

/-- **Bloch–Kato / Fontaine–Laffaille Fundamental Differential** for any filtered `φ`-module `E`:
`δ_E : E →ₗ[ℚ_[p]] (E ⧸ Fil^0 E) × E`, `x ↦ (x̄, φ(x) - x)`. -/
def blochKatoMap (E : FilteredPhiModule p D) :
    D →ₗ[ℚ_[p]] (D ⧸ E.fil.fil 0) × D :=
  (Submodule.mkQ (E.fil.fil 0)).prod (E.φ.toLinearMap - LinearMap.id)

/-- **Crystalline `H⁰(ℚ_p, E)`**: `ker(δ_E) = { x ∈ Fil^0 E | φ(x) = x }`. -/
def H0Cris (E : FilteredPhiModule p D) : Submodule ℚ_[p] D :=
  LinearMap.ker (blochKatoMap E)

theorem mem_H0Cris_iff (E : FilteredPhiModule p D) (x : D) :
    x ∈ H0Cris E ↔ x ∈ E.fil.fil 0 ∧ E.φ x = x := by
  change (Submodule.mkQ (E.fil.fil 0) x, E.φ x - x) = (0, 0) ↔ x ∈ E.fil.fil 0 ∧ E.φ x = x
  rw [Prod.mk.injEq, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, sub_eq_zero]

/-- **Crystalline Bloch–Kato Tangent Space `H¹_f(ℚ_p, E)`**:
`coker(δ_E) = ((E ⧸ Fil^0 E) × E) ⧸ range(δ_E)`. -/
abbrev H1fCris (E : FilteredPhiModule p D) : Type u :=
  ((D ⧸ E.fil.fil 0) × D) ⧸ LinearMap.range (blochKatoMap E)

/-- **General Bloch–Kato / Fontaine–Laffaille Exact Dimension Formula**:
for EVERY finite-dimensional filtered `φ`-module `E` over `ℚ_[p]`,
`dim H¹_f(ℚ_p, E) = dim(E ⧸ Fil^0 E) + dim H⁰(ℚ_p, E)`! -/
theorem finrank_H1fCris_eq (E : FilteredPhiModule p D) :
    Module.finrank ℚ_[p] (H1fCris E) =
      Module.finrank ℚ_[p] (D ⧸ E.fil.fil 0) + Module.finrank ℚ_[p] (H0Cris E) := by
  have hquot := Submodule.finrank_quotient_add_finrank (LinearMap.range (blochKatoMap E))
  have hrank := LinearMap.finrank_range_add_finrank_ker (blochKatoMap E)
  rw [Module.finrank_prod] at hquot
  change Module.finrank ℚ_[p] (H1fCris E) +
      Module.finrank ℚ_[p] (LinearMap.range (blochKatoMap E)) =
    Module.finrank ℚ_[p] (D ⧸ E.fil.fil 0) + Module.finrank ℚ_[p] D at hquot
  change Module.finrank ℚ_[p] (LinearMap.range (blochKatoMap E)) +
      Module.finrank ℚ_[p] (H0Cris E) = Module.finrank ℚ_[p] D at hrank
  omega

/-- For any regular 2D filtered `φ`-module `M` (weights `{0, k - 1}`, `k ≥ 2`, Hodge line `L`),
`Fil^0(End M)` consists precisely of endomorphisms stabilizing the Hodge line `L`:
`Fil^0(End M) = { f : D →ₗ D | ∀ x ∈ L, f x ∈ L }` (the Borel subalgebra!). -/
theorem IsRegularDim2.mem_endModule_fil0_iff {M : FilteredPhiModule p D} {k : ℕ}
    {L : Submodule ℚ_[p] D} (hreg : IsRegularDim2 M k L) (f : D →ₗ[ℚ_[p]] D) :
    f ∈ (M.endModule).fil.fil 0 ↔ ∀ x ∈ L, f x ∈ L := by
  have hk := hreg.hk
  change (∀ j : ℤ, ∀ x ∈ M.fil.fil j, f x ∈ M.fil.fil (j + 0)) ↔ ∀ x ∈ L, f x ∈ L
  constructor
  · intro hf x hx
    have h1 := hf 1 x (by rw [hreg.hfil 1, if_neg (by omega), if_pos (by omega)]; exact hx)
    rw [add_zero, hreg.hfil 1, if_neg (by omega), if_pos (by omega)] at h1
    exact h1
  · intro hf j x hx
    rw [add_zero]
    rw [hreg.hfil j] at hx ⊢
    split_ifs at hx ⊢
    · trivial
    · exact hf x hx
    · rw [Submodule.mem_bot] at hx ⊢
      rw [hx, map_zero]

/-- **Exact Codimension 1 of `Fil^0(End M)`**:
for any regular 2D filtered `φ`-module `M`, `dim(End(M) ⧸ Fil^0 End(M)) = 1`! -/
theorem IsRegularDim2.finrank_endModule_quot_fil0 {M : FilteredPhiModule p D} {k : ℕ}
    {L : Submodule ℚ_[p] D} (hreg : IsRegularDim2 M k L) :
    Module.finrank ℚ_[p] ((D →ₗ[ℚ_[p]] D) ⧸ (M.endModule).fil.fil 0) = 1 := by
  let proj : (D →ₗ[ℚ_[p]] D) →ₗ[ℚ_[p]] (L →ₗ[ℚ_[p]] (D ⧸ L)) :=
    { toFun := fun f => ((Submodule.mkQ L).comp f).comp L.subtype
      map_add' := fun f g => by ext x; simp
      map_smul' := fun c f => by ext x; simp }
  have hker : LinearMap.ker proj = (M.endModule).fil.fil 0 := by
    ext f
    rw [LinearMap.mem_ker, hreg.mem_endModule_fil0_iff]
    constructor
    · intro h x hx
      have := LinearMap.congr_fun h ⟨x, hx⟩
      simpa [proj, Submodule.Quotient.mk_eq_zero] using this
    · intro h
      ext ⟨x, hx⟩
      simpa [proj, Submodule.Quotient.mk_eq_zero] using h x hx
  have hsurj : Function.Surjective proj := by
    intro g
    obtain ⟨C, hC⟩ := L.exists_isCompl
    let pL : D →ₗ[ℚ_[p]] L := Submodule.projectionOnto L C hC
    obtain ⟨s, hs⟩ := (Submodule.mkQ L).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective L))
    have hLs : ∀ q : D ⧸ L, Submodule.mkQ L (s q) = q := fun q => LinearMap.congr_fun hs q
    refine ⟨(s.comp g).comp pL, ?_⟩
    ext ⟨x, hx⟩
    change Submodule.mkQ L (s (g (pL x))) = g ⟨x, hx⟩
    rw [hLs, Submodule.projectionOnto_apply_left hC ⟨x, hx⟩]
  have hrank := LinearMap.finrank_range_add_finrank_ker proj
  have hquot := Submodule.finrank_quotient_add_finrank ((M.endModule).fil.fil 0)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker] at hrank
  have hdim_hom : Module.finrank ℚ_[p] (L →ₗ[ℚ_[p]] (D ⧸ L)) = 1 := by
    rw [Module.finrank_linearMap, hreg.hL_dim]
    have hq := Submodule.finrank_quotient_add_finrank L
    rw [hreg.hdim, hreg.hL_dim] at hq
    have : Module.finrank ℚ_[p] (D ⧸ L) = 1 := by omega
    rw [this, mul_one]
  omega

/-- **Exact Codimension 1 of `Fil^0(Ad⁰ M)`**:
for any regular 2D filtered `φ`-module `M`, `dim(Ad⁰(M) ⧸ Fil^0 Ad⁰(M)) = 1`! -/
theorem IsRegularDim2.finrank_ad0Module_quot_fil0 {M : FilteredPhiModule p D} {k : ℕ}
    {L : Submodule ℚ_[p] D} (hreg : IsRegularDim2 M k L) :
    Module.finrank ℚ_[p] (FilteredPhiModule.ad0Submodule p D ⧸ (M.ad0Module).fil.fil 0) = 1 := by
  let proj : FilteredPhiModule.ad0Submodule p D →ₗ[ℚ_[p]] (L →ₗ[ℚ_[p]] (D ⧸ L)) :=
    { toFun := fun f => ((Submodule.mkQ L).comp f.1).comp L.subtype
      map_add' := fun f g => by ext x; simp
      map_smul' := fun c f => by ext x; simp }
  have hker : LinearMap.ker proj = (M.ad0Module).fil.fil 0 := by
    ext f
    rw [LinearMap.mem_ker]
    change proj f = 0 ↔ f.1 ∈ (M.endModule).fil.fil 0
    rw [hreg.mem_endModule_fil0_iff]
    constructor
    · intro h x hx
      have := LinearMap.congr_fun h ⟨x, hx⟩
      simpa [proj, Submodule.Quotient.mk_eq_zero] using this
    · intro h
      ext ⟨x, hx⟩
      simpa [proj, Submodule.Quotient.mk_eq_zero] using h x hx
  have hsurj : Function.Surjective proj := by
    intro g
    obtain ⟨C, hC⟩ := L.exists_isCompl
    let pL : D →ₗ[ℚ_[p]] L := Submodule.projectionOnto L C hC
    obtain ⟨s, hs⟩ := (Submodule.mkQ L).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective L))
    have hLs : ∀ q : D ⧸ L, Submodule.mkQ L (s q) = q := fun q => LinearMap.congr_fun hs q
    let f0 : D →ₗ[ℚ_[p]] D := (s.comp g).comp pL
    let c : ℚ_[p] := LinearMap.trace ℚ_[p] D f0 / (2 : ℚ_[p])
    let f : D →ₗ[ℚ_[p]] D := f0 - c • LinearMap.id
    have htr_id : LinearMap.trace ℚ_[p] D (LinearMap.id : D →ₗ[ℚ_[p]] D) = (2 : ℚ_[p]) := by
      rw [LinearMap.trace_id, hreg.hdim]; norm_num
    have hf_tr : f ∈ FilteredPhiModule.ad0Submodule p D := by
      rw [FilteredPhiModule.ad0Submodule, LinearMap.mem_ker]
      simp only [f, map_sub, map_smul, htr_id, smul_eq_mul, c]
      have h2ne : (2 : ℚ_[p]) ≠ 0 := by norm_num
      field_simp [h2ne]
      ring
    refine ⟨⟨f, hf_tr⟩, ?_⟩
    ext ⟨x, hx⟩
    change Submodule.mkQ L (f0 x - c • x) = g ⟨x, hx⟩
    have hLx : Submodule.mkQ L x = 0 := (Submodule.Quotient.mk_eq_zero L).mpr hx
    rw [map_sub, map_smul, hLx, smul_zero, sub_zero]
    change Submodule.mkQ L (s (g (pL x))) = g ⟨x, hx⟩
    rw [hLs, Submodule.projectionOnto_apply_left hC ⟨x, hx⟩]
  have hrank := LinearMap.finrank_range_add_finrank_ker proj
  have hquot := Submodule.finrank_quotient_add_finrank ((M.ad0Module).fil.fil 0)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, hker] at hrank
  have hdim_hom : Module.finrank ℚ_[p] (L →ₗ[ℚ_[p]] (D ⧸ L)) = 1 := by
    rw [Module.finrank_linearMap, hreg.hL_dim]
    have hq := Submodule.finrank_quotient_add_finrank L
    rw [hreg.hdim, hreg.hL_dim] at hq
    have : Module.finrank ℚ_[p] (D ⧸ L) = 1 := by omega
    rw [this, mul_one]
  omega

/-- **EXACT CRYSTALLINE TANGENT SPACE DIMENSION (`dim_crystalline_tangent_eq`)**:
For ANY regular 2D filtered `φ`-module `M` (weights `{0, k - 1}`, `k ≥ 2`, including every regular
2D Fontaine–Laffaille module with `0 < k - 1 < p - 1`):
1. `dim H¹_f(ℚ_p, Ad(M)) = 1 + dim H⁰(ℚ_p, Ad(M))`
2. `dim H¹_f(ℚ_p, Ad⁰(M)) = 1 + dim H⁰(ℚ_p, Ad⁰(M))`
matching the exact Taylor–Wiles local excess `dim H¹_f - dim H⁰ = 1 = [ℚ : ℚ]`! -/
theorem dim_crystalline_tangent_eq {M : FilteredPhiModule p D} {k : ℕ}
    {L : Submodule ℚ_[p] D} (hreg : IsRegularDim2 M k L) :
    Module.finrank ℚ_[p] (H1fCris (M.endModule)) =
        1 + Module.finrank ℚ_[p] (H0Cris (M.endModule)) ∧
      Module.finrank ℚ_[p] (H1fCris (M.ad0Module)) =
        1 + Module.finrank ℚ_[p] (H0Cris (M.ad0Module)) := by
  refine ⟨?_, ?_⟩
  · rw [finrank_H1fCris_eq, hreg.finrank_endModule_quot_fil0]
  · rw [finrank_H1fCris_eq, hreg.finrank_ad0Module_quot_fil0]

/-- **Exact Taylor–Wiles Local Excess (`dim H¹_f - dim H⁰ = 1 = [ℚ : ℚ]`)** for both
`Ad(M)` and `Ad⁰(M)` of any regular 2D crystalline module `M`. -/
theorem taylor_wiles_local_crystalline_excess {M : FilteredPhiModule p D} {k : ℕ}
    {L : Submodule ℚ_[p] D} (hreg : IsRegularDim2 M k L) :
    (Module.finrank ℚ_[p] (H1fCris (M.endModule)) : ℤ) -
        (Module.finrank ℚ_[p] (H0Cris (M.endModule)) : ℤ) = 1 ∧
      (Module.finrank ℚ_[p] (H1fCris (M.ad0Module)) : ℤ) -
        (Module.finrank ℚ_[p] (H0Cris (M.ad0Module)) : ℤ) = 1 := by
  obtain ⟨h1, h2⟩ := dim_crystalline_tangent_eq hreg
  omega

/-- **Schur's Lemma for Non-Split 2D Crystalline Filtered `φ`-Modules**:
if `L = Fil^1 D` is NOT `φ`-stable, then every filtered `φ`-endomorphism of `M` is a scalar
multiple of `id`, so:
- `dim H⁰(ℚ_p, Ad(M)) = 1` and `dim H¹_f(ℚ_p, Ad(M)) = 2`,
- `dim H⁰(ℚ_p, Ad⁰(M)) = 0` and `dim H¹_f(ℚ_p, Ad⁰(M)) = 1`! -/
theorem schur_nonSplit_dim2_crystalline {M : FilteredPhiModule p D} {k : ℕ}
    {L : Submodule ℚ_[p] D} (hreg : IsRegularDim2 M k L) (hL_not : ¬ M.IsPhiStable L) :
    Module.finrank ℚ_[p] (H0Cris (M.endModule)) = 1 ∧
      Module.finrank ℚ_[p] (H1fCris (M.endModule)) = 2 ∧
      Module.finrank ℚ_[p] (H0Cris (M.ad0Module)) = 0 ∧
      Module.finrank ℚ_[p] (H1fCris (M.ad0Module)) = 1 := by
  have hscalar : ∀ f ∈ H0Cris (M.endModule), ∃ c : ℚ_[p], f = c • LinearMap.id := by
    intro f hf
    rw [mem_H0Cris_iff, hreg.mem_endModule_fil0_iff] at hf
    obtain ⟨hfL, hfphi⟩ := hf
    have hcomm : ∀ x : D, M.φ (f x) = f (M.φ x) := fun x => by
      have h := LinearMap.congr_fun hfphi (M.φ x)
      simpa [FilteredPhiModule.endModule] using h
    have hLdim := hreg.hL_dim
    have hL_ne : L ≠ ⊥ := fun h0 => by rw [h0, finrank_bot] at hLdim; omega
    obtain ⟨v, hvL, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL_ne
    have hL_eq : L = Submodule.span ℚ_[p] {v} := by
      refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
      · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvL)
      · rw [finrank_span_singleton hv0, hLdim]
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hL_eq ▸ hfL v hvL)
    have hfv : f v = c • v := hc.symm
    have hφv_not : M.φ v ∉ L := by
      intro hmem
      apply hL_not
      intro x hx
      rw [hL_eq] at hx
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [map_smul]
      exact L.smul_mem r hmem
    have hspan_top : Submodule.span ℚ_[p] ({v, M.φ v} : Set D) = ⊤ := by
      have hL_lt : L < Submodule.span ℚ_[p] ({v, M.φ v} : Set D) := by
        refine lt_of_le_of_ne ?_ ?_
        · rw [hL_eq]
          exact Submodule.span_mono (by simp)
        · intro heq
          exact hφv_not (heq ▸ Submodule.subset_span (by simp))
      have hdim_gt := Submodule.finrank_lt_finrank_of_lt hL_lt
      have hdim_le : Module.finrank ℚ_[p] (Submodule.span ℚ_[p] ({v, M.φ v} : Set D)) ≤ 2 := by
        simpa [hreg.hdim] using Submodule.finrank_le (Submodule.span ℚ_[p] ({v, M.φ v} : Set D))
      exact Submodule.eq_top_of_finrank_eq (by rw [hreg.hdim]; omega)
    refine ⟨c, ?_⟩
    apply LinearMap.ext
    intro x
    have hx : x ∈ Submodule.span ℚ_[p] ({v, M.φ v} : Set D) := by rw [hspan_top]; trivial
    rw [Submodule.mem_span_pair] at hx
    obtain ⟨a, b, rfl⟩ := hx
    rw [map_add, map_smul, map_smul, hfv, ← hcomm v, hfv, map_smul]
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_add]
    rw [smul_comm a c, smul_comm b c]
  have hH0_eq : H0Cris (M.endModule) = Submodule.span ℚ_[p] {LinearMap.id} := by
    ext f
    constructor
    · intro hf
      obtain ⟨c, rfl⟩ := hscalar f hf
      exact Submodule.mem_span_singleton.mpr ⟨c, rfl⟩
    · intro hf
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hf
      rw [mem_H0Cris_iff, hreg.mem_endModule_fil0_iff]
      refine ⟨fun x hx => L.smul_mem c hx, ?_⟩
      ext x
      simp [FilteredPhiModule.endModule]
  have hH0_end : Module.finrank ℚ_[p] (H0Cris (M.endModule)) = 1 := by
    rw [hH0_eq]
    refine finrank_span_singleton ?_
    intro h0
    have htr := congrArg (LinearMap.trace ℚ_[p] D) h0
    rw [LinearMap.trace_id, map_zero, hreg.hdim] at htr
    norm_num at htr
  have hH0_ad0 : Module.finrank ℚ_[p] (H0Cris (M.ad0Module)) = 0 := by
    have hbot : H0Cris (M.ad0Module) = ⊥ := by
      ext ⟨f, hf_tr⟩
      rw [Submodule.mem_bot, mem_H0Cris_iff]
      constructor
      · rintro ⟨hf0, hfphi⟩
        have hf_end : f ∈ H0Cris (M.endModule) := by
          rw [mem_H0Cris_iff]
          exact ⟨hf0, congrArg Subtype.val hfphi⟩
        obtain ⟨c, rfl⟩ := hscalar f hf_end
        rw [FilteredPhiModule.ad0Submodule, LinearMap.mem_ker, map_smul, LinearMap.trace_id,
          hreg.hdim, smul_eq_mul] at hf_tr
        have h2ne : ((2 : ℕ) : ℚ_[p]) ≠ 0 := by norm_num
        have hc0 : c = 0 := (mul_eq_zero.mp hf_tr).resolve_right h2ne
        subst hc0
        exact Subtype.ext (by simp)
      · intro h0
        rw [h0]
        exact ⟨(M.ad0Module.fil.fil 0).zero_mem, map_zero _⟩
    rw [hbot, finrank_bot]
  obtain ⟨h1, h2⟩ := dim_crystalline_tangent_eq hreg
  refine ⟨hH0_end, by omega, hH0_ad0, by omega⟩

/-- Concrete specialization of `dim_crystalline_tangent_eq` + Schur's lemma to `crystallineMod2D`:
for EVERY prime `p`, EVERY weight `k ≥ 2`, and EVERY `a_p ∈ ℚ_[p]`,
`dim H¹_f(Ad) = 2`, `dim H⁰(Ad) = 1`, `dim H¹_f(Ad⁰) = 1`, `dim H⁰(Ad⁰) = 0`! -/
theorem crystallineMod2D_tangent_dims (p : ℕ) [Fact p.Prime] (k : ℕ) (hk : 2 ≤ k) (a_p : ℚ_[p]) :
    Module.finrank ℚ_[p] (H0Cris (crystallineMod2D p k hk a_p).endModule) = 1 ∧
      Module.finrank ℚ_[p] (H1fCris (crystallineMod2D p k hk a_p).endModule) = 2 ∧
      Module.finrank ℚ_[p] (H0Cris (crystallineMod2D p k hk a_p).ad0Module) = 0 ∧
      Module.finrank ℚ_[p] (H1fCris (crystallineMod2D p k hk a_p).ad0Module) = 1 :=
  schur_nonSplit_dim2_crystalline
    (crystallineMod2D_isRegularDim2 p k hk a_p)
    (crystallineMod2D_not_phiStable_stdHodgeLine p k hk a_p)

/-- **Exact Crystalline Tangent Dimension for Every 2D Fontaine–Laffaille Module (`0 < k - 1 < p - 1`)**:
for `FL = fontaineLaffaille2D p k hk hk_lt a_p` (`2 ≤ k ≤ p - 1`, `a_p ∈ ℤ_[p]`),
`dim H¹_f(ℚ_p, Ad(FL)) = 1 + dim H⁰(ℚ_p, Ad(FL))` and
`dim H¹_f(ℚ_p, Ad⁰(FL)) = 1 + dim H⁰(ℚ_p, Ad⁰(FL))`,
giving the exact Taylor–Wiles local excess `dim H¹_f - dim H⁰ = 1 = [ℚ : ℚ]`! -/
theorem fontaineLaffaille2D_tangent_dims (p : ℕ) [Fact p.Prime] (k : ℕ)
    (hk : 2 ≤ k) (hk_lt : k ≤ p - 1) (a_p : ℤ_[p]) :
    let D_FL := (FontaineLaffailleModule.fontaineLaffaille2D p k hk hk_lt a_p).toFilteredPhiModule
    Module.finrank ℚ_[p] (H1fCris D_FL.endModule) =
        1 + Module.finrank ℚ_[p] (H0Cris D_FL.endModule) ∧
      Module.finrank ℚ_[p] (H1fCris D_FL.ad0Module) =
        1 + Module.finrank ℚ_[p] (H0Cris D_FL.ad0Module) ∧
      (Module.finrank ℚ_[p] (H1fCris D_FL.ad0Module) : ℤ) -
        (Module.finrank ℚ_[p] (H0Cris D_FL.ad0Module) : ℤ) = 1 := by
  intro D_FL
  have hreg := FontaineLaffailleModule.fontaineLaffaille2D_isRegularDim2 p k hk hk_lt a_p
  obtain ⟨h1, h2⟩ := dim_crystalline_tangent_eq hreg
  refine ⟨h1, h2, ?_⟩
  change Module.finrank ℚ_[p] (H1fCris D_FL.ad0Module) =
    1 + Module.finrank ℚ_[p] (H0Cris D_FL.ad0Module) at h2
  omega

end CrystallineTangentDimension

end Stage11CrystallineFontaine
end RHDirect

end
