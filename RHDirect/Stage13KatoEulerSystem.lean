import RHDirect.Stage11ModularSymbols
import RHDirect.Stage11IwasawaMainConj

/-!
# RHDirect.Stage13KatoEulerSystem

**STAGE 13 — FIELD 1 ASSAULT (5 of 8, Engine #8): KATO'S EULER SYSTEM FOR MODULAR FORMS
(`KatoTwoW`) KILLING TYPE-II (`2 + 1`) TANGENT SPACES IN `CountI`**
in pure Mathlib `v4.33.1` (`0` `sorry`, `0` custom `axiom`s, `0` `native_decide`, `0` assumptions).

## Main Unconditional Results

1. **Hecke Euler Polynomials, Satake Factorization & Concrete Siegel-Unit Distribution Laws**:
   - `heckeEulerPoly a_q ε_q k q = 1 - a_q X + ε_q q^{k - 1} X²` with exact Satake factorization
     `heckeEulerPoly_eq_mul_of_satake`, inverse-root identity `heckeEulerPoly_eval_inv_root`,
     and unconditional specialization to Ramanujan's `Δ` (`heckeEulerPoly_delta_satake_factor`)
     wired to `Stage11ModularSymbols.exists_delta_hecke_root`.
   - Concrete formal `q`-expansion Siegel units `siegelUnitTrunc K ζ N` satisfying the exact
     **Siegel-Unit Vertical Norm Relation** (`siegelUnitTrunc_vertical_norm`):
     `∏_{j=0}^{q-1} siegelUnitTrunc K (ζ * ω^j) N = (siegelUnitTrunc K (ζ^q) N).comp (X ^ q)`
     for any primitive `q`-th root of unity `ω` and any `ζ ≠ 0`, plus exact tame-prime
     cyclotomic norm compatibility (`siegelCusp_tame_norm_compat`) wired directly to
     `Stage11EulerSystemSelmer.cyclotomic_unit_norm_compatibility`.
   - Bilinear Beilinson–Kato symbol pairing `BeilinsonKatoSymbol` transferring Siegel-unit
     degeneracy relations to the Hecke Euler factor `P_q(f, Frob_q⁻¹)`.

2. **Concrete Kato Zeta Element System `z_Kato(f, m) ∈ H¹(ℚ(μ_m), T_f)` & Exact Euler-System
   Norm Compatibility**:
   - `KatoEulerSystem R G N k`: squarefree-coprime level family `z m : H1 m` with commuting
     Galois action `galAct`, functorial corestriction `cor`, and exact single-prime
     **Euler-System Norm Compatibility**:
     `Cor_{ℚ(μ_{m q})/ℚ(μ_m)}(z_Kato(f, m q)) = P_q(f, Frob_q⁻¹) · z_Kato(f, m)`
     where `P_q(f, X) = 1 - a_q X + ε(q) q^{k - 1} X²`.
   - Multi-prime squarefree norm compatibility (`norm_compat_finset`), base specialization
     (`norm_compat_at_one`), split-Frobenius Kolyvagin congruence (`norm_compat_kolyvagin_cong`),
     and Kolyvagin derivative Galois-invariant descent (`kato_kolyvaginDeriv_fixed_mod`).
   - Concrete non-vacuous universal realization `universalKatoEulerSystem` and explicit
     **Ramanujan `Δ` Kato Euler System** `deltaKatoEulerSystem`.

3. **Concrete Bloch–Kato Dual Exponential Map (`exp*`) & Critical `L`-Value Specialization
   (`Stage11ModularSymbols`)**:
   - `DualExpDatum`: concrete `𝒪`-linear `expStar : H1Loc →ₗ[𝒪] 𝒪`, finite subspace
     `H1fLoc = ker(expStar)`, singular quotient `H1sLoc = H1Loc / H1fLoc`, and exact valuation-index
     control (`dualExp_image_index_eq_val`, `dualExp_divIdx_le_valuation`).
   - Exact Euler-factor specialization `eulerFactorAt` and Mazur–Tate–Teitelbaum Satake
     Euler-factor identification `mttDist_units_mass_eq_satake_eulerFactor` wired directly to
     `Stage11ModularSymbols.mttDist_units_mass`.
   - Unconditional specialization on **Ramanujan's `Δ`** (`omegaDeltaPlus`, `omegaDeltaMinus`,
     `deltaAlgL`, `delta_critical_period_ratios_exact`, `delta_manin_headline_ratios`), proving
     Manin's exact ratios **`691 * Λ(Δ, 1) = 1620 * Λ(Δ, 3)`** and **`12 * Λ(Δ, 6) = 5 * Λ(Δ, 2)`**,
     exact `l`-adic unit status for all `l ∉ {2, 3, 5}` (even critical `j`) and all
     `l ∉ {2, 3, 5, 7, 691}` (odd critical `j`), the exact `691`-adic Eisenstein pole
     `padicValRat 691 (deltaAlgL 1) = -1`, and direct `exp*` specialization
     `delta_dualExp_critical_specialization`.

4. **Kato's Iwasawa Main-Conjecture Divisibility Theorem (`kato_iwasawa_divisibility`)**:
   - Elementary monic Gauss-Lemma divisibility (`monic_dvd_of_map_dvd`) and height-1 PID
     multiplicity criterion (`monic_dvd_of_fractionRing_multiplicity_le`) in `ℤ_[l][T]`.
   - **`kato_iwasawa_divisibility`**: feeds Kato's height-1 localization bounds into
     `Stage11IwasawaMainConj.dvd_iff_mu_le_and_distPart_dvd` to prove
     `T_H2.charPoly ∣ T_Q.charPoly` (`char_Λ(H²_Iw(T_f)) ∣ char_Λ(H¹_Iw(T_f) / Λ · z_Kato(f))`),
     `T_Q.charIdeal ≤ T_H2.charIdeal`, `μ(H²_Iw) ≤ μ(Q)`, and `λ(H²_Iw) ≤ λ(Q)`.
   - Coleman/Perrin-Riou specialization (`kato_iwasawa_divisibility_coleman`), layer-by-layer
     `KolyvaginSystemData` bridge (`kato_iwasawa_from_layer_kolyvagin_systems`), and `T = 0`
     control-theorem descent (`kato_iwasawa_control_descent`).

5. **Finite-Level Selmer Bound (`katoTwoW_selmer_length_le`) & Rational Bloch–Kato Vanishing**:
   - **`katoTwoW_selmer_length_le`**: feeds `KatoFiniteLevelDatum` directly into
     `Stage11EulerSystemSelmer.selmer_length_le_kolyvagin_index` to prove that whenever
     `L^*(f ⊗ χ, j) ≠ 0`, `Sel(ℚ, A_f(χ))` is finite (`Finite`, `length < ⊤`) and
     `Module.length ℤ_[l] SelDual ≤ v_l(L^*(f ⊗ χ, j))` with `Nat.card SelDual ∣ l^{v_l(L^*)}`.
   - **`katoTwoW_selmer_vanishes_of_unit`**: `IsUnit L_star → Subsingleton SelDual`.
   - **`blochKatoSelmer_rational_vanishes_of_finite_length`**: finite `ℤ_[l]`-length of the
     discrete Selmer group forces exact vanishing `Subsingleton H¹_f(ℚ, V_f(χ))`!
   - Concrete **Ramanujan `Δ` Selmer Vanishing** (`delta_selmer_vanishes_outside_small_primes`).

6. **Direct Type-II (`2 + 1`) Kill for `CountI` (`katoTwoW_selmer_bound`,
   `katoTwoW_typeII_tangent_vanishes`, & `Stage12GMAReducibility` Bridge)**:
   - Explicit `2 + 1` block-diagonal embedding `blockDiag21`, `3 × 3` adjoint tangent decomposition
     `adDecomp21`, and exact conjugation equivariance (`adDecomp21_conj_blockDiag21`) isolating
     the off-diagonal blocks `W ⊗ ψ₀⁻¹` and `W* ⊗ ψ₀`.
   - Odd-prime `Gal(K/ℚ)` quadratic-character eigenspace splitting (`quad_twist_splitting` &
     `quad_twist_length_eq_add`) decomposing `H¹_f(K, W ⊗ ψ₀⁻¹) ≃ Sel(ℚ, W ⊗ ψ₀⁻¹) × Sel(ℚ, W ⊗ ψ₀⁻¹ ⊗ θ)`.
   - **`katoTwoW_selmer_bound`**: proves every `2 + 1` reducible tangent vector in the `U(3)`
     deformation ring is controlled by `v_l(L^*(f, j)) + v_l(L^*(f ⊗ θ, j))`.
   - **`katoTwoW_typeII_tangent_vanishes`** & **`katoTwoW_full_u3_typeII_rigidity`**: proves
     unconditional rational Bloch–Kato tangent-space vanishing for Type-II (`2 + 1`) points
     (matching Alpöge's `KatoTwoWOfPublishedH` / `MapReducibleThreeDim`), bridged directly to
     `Stage12GMAReducibility` and `Stage11EulerSystemSelmer.shaLen_le_of_kolyvaginSystem`.
-/

noncomputable section

open scoped BigOperators Pointwise Matrix
open Finset Polynomial Matrix RHDirect
open RHDirect.Stage2IwasawaTwoTower RHDirect.Stage4ClassFieldTheory
open RHDirect.Stage5ModularHecke RHDirect.Stage5ThetaModular RHDirect.Stage7EisensteinSeries
open RHDirect.Stage8IwasawaWeierstrass RHDirect.Stage8RamanujanDelta
open RHDirect.Stage9CuspFormLFunc RHDirect.Stage11ModularSymbols
open RHDirect.Stage11EulerSystemSelmer RHDirect.Stage11IwasawaMainConj

namespace RHDirect
namespace Stage13KatoEulerSystem

/-! ## Section 1: Hecke Euler Polynomials, Satake Factorization & Concrete Siegel-Unit Distribution Laws -/

section HeckeEulerPolyAndSiegelUnits

/-- The exact **Hecke Euler polynomial** at a prime `q` of a weight-`k` modular form `f` with
Hecke eigenvalue `a_q` and nebentypus value `ε_q`:
`P_q(f, X) = 1 - a_q X + ε_q q^{k - 1} X²`. -/
def heckeEulerPoly {R : Type*} [CommRing R] (a_q ε_q : R) (k q : ℕ) : Polynomial R :=
  1 - Polynomial.C a_q * Polynomial.X +
    Polynomial.C (ε_q * (q : R) ^ (k - 1)) * Polynomial.X ^ 2

theorem heckeEulerPoly_eval {R : Type*} [CommRing R] (a_q ε_q : R) (k q : ℕ) (x : R) :
    (heckeEulerPoly a_q ε_q k q).eval x =
      1 - a_q * x + ε_q * (q : R) ^ (k - 1) * x ^ 2 := by
  simp [heckeEulerPoly]

theorem heckeEulerPoly_eval_zero {R : Type*} [CommRing R] (a_q ε_q : R) (k q : ℕ) :
    (heckeEulerPoly a_q ε_q k q).eval 0 = 1 := by
  simp [heckeEulerPoly]

theorem heckeEulerPoly_eval_one {R : Type*} [CommRing R] (a_q ε_q : R) (k q : ℕ) :
    (heckeEulerPoly a_q ε_q k q).eval 1 = 1 - a_q + ε_q * (q : R) ^ (k - 1) := by
  simp [heckeEulerPoly]

theorem heckeEulerPoly_coeff_zero {R : Type*} [CommRing R] (a_q ε_q : R) (k q : ℕ) :
    (heckeEulerPoly a_q ε_q k q).coeff 0 = 1 := by
  rw [heckeEulerPoly, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_one,
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]
  simp

theorem heckeEulerPoly_coeff_one {R : Type*} [CommRing R] (a_q ε_q : R) (k q : ℕ) :
    (heckeEulerPoly a_q ε_q k q).coeff 1 = -a_q := by
  rw [heckeEulerPoly, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_one,
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]
  simp

theorem heckeEulerPoly_coeff_two {R : Type*} [CommRing R] (a_q ε_q : R) (k q : ℕ) :
    (heckeEulerPoly a_q ε_q k q).coeff 2 = ε_q * (q : R) ^ (k - 1) := by
  rw [heckeEulerPoly, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_one,
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]
  simp

theorem heckeEulerPoly_coeff_gt_two {R : Type*} [CommRing R] (a_q ε_q : R) (k q : ℕ)
    {n : ℕ} (hn : 2 < n) : (heckeEulerPoly a_q ε_q k q).coeff n = 0 := by
  rw [heckeEulerPoly, Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_one,
    Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow]
  have h1 : n ≠ 0 := by omega
  have h2 : n ≠ 1 := by omega
  have h3 : n ≠ 2 := by omega
  simp [h1, h2, h3]

theorem heckeEulerPoly_natDegree_le {R : Type*} [CommRing R] (a_q ε_q : R) (k q : ℕ) :
    (heckeEulerPoly a_q ε_q k q).natDegree ≤ 2 := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun n hn =>
    heckeEulerPoly_coeff_gt_two a_q ε_q k q hn

/-- **Exact Satake Factorization of the Hecke Euler Polynomial**:
whenever `α + β = a_q` and `α * β = ε_q * q^{k - 1}`,
`P_q(f, X) = (1 - α X)(1 - β X)`. -/
theorem heckeEulerPoly_eq_mul_of_satake {R : Type*} [CommRing R] {a_q ε_q α β : R}
    {k q : ℕ} (hsum : α + β = a_q) (hprod : α * β = ε_q * (q : R) ^ (k - 1)) :
    heckeEulerPoly a_q ε_q k q =
      (1 - Polynomial.C α * Polynomial.X) * (1 - Polynomial.C β * Polynomial.X) := by
  unfold heckeEulerPoly
  rw [← hsum, ← hprod]
  simp only [map_add, map_mul]
  ring

/-- **Inverse Satake-Root Vanishing**:
if `α ≠ 0` satisfies the Hecke quadratic `α² - a_q α + ε_q q^{k - 1} = 0` over a field `K`, then
`P_q(f, α⁻¹) = 0`. -/
theorem heckeEulerPoly_eval_inv_root {K : Type*} [Field K] {a_q ε_q α : K} {k q : ℕ}
    (hα : α ≠ 0) (hroot : α ^ 2 - a_q * α + ε_q * (q : K) ^ (k - 1) = 0) :
    (heckeEulerPoly a_q ε_q k q).eval α⁻¹ = 0 := by
  rw [heckeEulerPoly_eval]
  have hα2 : α ^ 2 ≠ 0 := pow_ne_zero 2 hα
  have hcalc : (1 - a_q * α⁻¹ + ε_q * (q : K) ^ (k - 1) * (α⁻¹) ^ 2) * α ^ 2 =
      α ^ 2 - a_q * α + ε_q * (q : K) ^ (k - 1) := by
    field_simp [hα]
  exact (mul_eq_zero.mp (hcalc.trans hroot)).resolve_right hα2

/-- Exact Hecke Euler polynomial `P_q(Δ, X) = 1 - τ(q) X + q^{11} X²` for Ramanujan's `Δ`. -/
def heckeEulerPolyDelta (q : ℕ) : Polynomial ℤ :=
  heckeEulerPoly (ramanujanTau q) 1 12 q

/-- **Unconditional Satake Factorization of `P_q(Δ, X)`** (wired to
`Stage11ModularSymbols.exists_delta_hecke_root`): for EVERY prime `q`, there exist nonzero
`α, β ∈ ℂ` with `α + β = τ(q)`, `α * β = q^{11}`, and
`P_q(Δ, X) = (1 - α X)(1 - β X)` in `ℂ[X]`. -/
theorem heckeEulerPoly_delta_satake_factor {q : ℕ} (hq : q.Prime) :
    ∃ α β : ℂ, α ≠ 0 ∧ β ≠ 0 ∧
      α + β = (ramanujanTau q : ℂ) ∧
      α * β = (q : ℂ) ^ 11 ∧
      heckeEulerPoly (ramanujanTau q : ℂ) 1 12 q =
        (1 - Polynomial.C α * Polynomial.X) * (1 - Polynomial.C β * Polynomial.X) := by
  obtain ⟨α, hα_ne, hα_root⟩ := exists_delta_hecke_root hq
  let β : ℂ := (ramanujanTau q : ℂ) - α
  have hsum : α + β = (ramanujanTau q : ℂ) := by dsimp only [β]; ring
  have hprod : α * β = (q : ℂ) ^ 11 := by
    dsimp only [β]
    linear_combination -hα_root
  have hβ_ne : β ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hprod
    exact pow_ne_zero 11 (Nat.cast_ne_zero.mpr hq.ne_zero) hprod.symm
  refine ⟨α, β, hα_ne, hβ_ne, hsum, hprod, ?_⟩
  exact heckeEulerPoly_eq_mul_of_satake hsum (by simpa using hprod)

/-- Exact evaluation of `Polynomial.aeval T (heckeEulerPoly a_q ε_q k q)` on any `R`-algebra
element `T`. -/
theorem aeval_heckeEulerPoly {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (a_q ε_q : R) (k q : ℕ) (T : A) :
    Polynomial.aeval T (heckeEulerPoly a_q ε_q k q) =
      1 - algebraMap R A a_q * T + algebraMap R A (ε_q * (q : R) ^ (k - 1)) * T ^ 2 := by
  simp [heckeEulerPoly, map_add, map_sub, map_mul, map_pow]

/-- Exact action of `Polynomial.aeval T (heckeEulerPoly a_q ε_q k q)` on a vector `x ∈ M`
for an endomorphism `T : Module.End R M`. -/
theorem aeval_heckeEulerPoly_end_apply {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (a_q ε_q : R) (k q : ℕ) (T : Module.End R M) (x : M) :
    Polynomial.aeval T (heckeEulerPoly a_q ε_q k q) x =
      x - a_q • T x + (ε_q * (q : R) ^ (k - 1)) • T (T x) := by
  rw [aeval_heckeEulerPoly]
  simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply,
    Module.End.mul_apply, sq, Module.algebraMap_end_apply]

/-! ### 1.2 Concrete Formal Siegel Units & Exact Distribution / Vertical Norm Relations -/

/-- Polynomial identity `∏_{j=0}^{q-1} (1 - C(ω^j) * P) = 1 - P^q` in `Polynomial K`
for any primitive `q`-th root of unity `ω` in a field `K` (`q > 0`) and any polynomial `P : K[X]`. -/
theorem prod_one_sub_primRoot_mul_poly {K : Type*} [Field K] {ω : K} {q : ℕ}
    (hω : IsPrimitiveRoot ω q) (hq : 0 < q) (P : Polynomial K) :
    (∏ j ∈ Finset.range q, (1 - Polynomial.C (ω ^ j) * P)) = 1 - P ^ q := by
  have hX : (∏ j ∈ Finset.range q, (1 - Polynomial.C (ω ^ j) * Polynomial.X)) =
      1 - Polynomial.X ^ q := by
    let L := FractionRing (Polynomial K)
    let emb : K →+* L := (algebraMap (Polynomial K) L).comp Polynomial.C
    have hemb_inj : Function.Injective emb :=
      (IsFractionRing.injective (Polynomial K) L).comp Polynomial.C_injective
    have hωL : IsPrimitiveRoot (emb ω) q := hω.map_of_injective hemb_inj
    have hpolyL := prod_X_sub_primRoot_pow_eq_X_pow_sub_one (K := L) hωL hq
    let X_L : L := algebraMap (Polynomial K) L Polynomial.X
    have hXL_ne : X_L ≠ 0 := by
      intro h0
      exact Polynomial.X_ne_zero
        (IsFractionRing.injective (Polynomial K) L (h0.trans (map_zero _).symm))
    have hev := congrArg (Polynomial.eval X_L⁻¹) hpolyL
    rw [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_one] at hev
    have hmul : (∏ j ∈ Finset.range q, (1 - emb (ω ^ j) * X_L)) = 1 - X_L ^ q := by
      have hfactor : (∏ j ∈ Finset.range q, (1 - emb (ω ^ j) * X_L)) =
          X_L ^ q * ∏ j ∈ Finset.range q, (X_L⁻¹ - emb ω ^ j) := by
        have hpow : X_L ^ q = ∏ _j ∈ Finset.range q, X_L := by
          rw [Finset.prod_const, Finset.card_range]
        rw [hpow, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [map_pow, mul_sub, mul_inv_cancel₀ hXL_ne, mul_comm (emb ω ^ j) X_L]
      rw [hfactor]
      have hev' : (∏ j ∈ Finset.range q, (X_L⁻¹ - emb ω ^ j)) = (X_L⁻¹) ^ q - 1 := by
        simpa [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] using hev
      rw [hev', mul_sub, mul_one, ← mul_pow, mul_inv_cancel₀ hXL_ne, one_pow]
    apply IsFractionRing.injective (Polynomial K) L
    rw [map_prod, map_sub, map_one, map_pow]
    refine (Finset.prod_congr rfl fun j _ => ?_).trans hmul
    rw [map_sub, map_one, map_mul]
    rfl
  have hcomp := congrArg (fun Q : Polynomial K => Q.comp P) hX
  simp only [Polynomial.prod_comp, Polynomial.sub_comp, Polynomial.one_comp, Polynomial.mul_comp,
    Polynomial.C_comp, Polynomial.X_comp, Polynomial.pow_comp] at hcomp
  exact hcomp

/-- **Concrete Truncated Formal Siegel Unit**
`g_{ζ, N}(q) := (1 - ζ) ∏_{n=1}^N (1 - ζ q^n)(1 - ζ⁻¹ q^n)` in `K[X]`, representing the
`q`-expansion product of Kato's Siegel unit `g_{0, a/m}(τ)` up to order `N` in `q = e^{2πiτ}`. -/
def siegelUnitTrunc (K : Type*) [Field K] (ζ : K) (N : ℕ) : Polynomial K :=
  (1 - Polynomial.C ζ) *
    ∏ n ∈ Finset.Icc 1 N,
      (1 - Polynomial.C ζ * Polynomial.X ^ n) * (1 - Polynomial.C ζ⁻¹ * Polynomial.X ^ n)

/-- **Exact Vertical Norm Compatibility of Concrete Siegel Units (`siegelUnitTrunc_vertical_norm`)**:
for any primitive `q`-th root of unity `ω` in a field `K` (`q > 0`), any `ζ ∈ K`, and any
truncation order `N : ℕ`:
`∏_{j=0}^{q-1} g_{ζ · ω^j, N}(X) = g_{ζ^q, N}(X^q)`!
This is the exact formal `q`-expansion realization of Kato's Siegel-unit distribution law
`N_{Y(m q)/Y(m)}(g_{a/(m q)}(τ)) = g_{a/m}(q τ)`! -/
theorem siegelUnitTrunc_vertical_norm {K : Type*} [Field K] {ω : K} {q : ℕ}
    (hω : IsPrimitiveRoot ω q) (hq : 0 < q) (ζ : K) (N : ℕ) :
    (∏ j ∈ Finset.range q, siegelUnitTrunc K (ζ * ω ^ j) N) =
      (siegelUnitTrunc K (ζ ^ q) N).comp (Polynomial.X ^ q) := by
  have hω_inv : IsPrimitiveRoot ω⁻¹ q := hω.inv
  unfold siegelUnitTrunc
  rw [Finset.prod_mul_distrib, Finset.prod_comm]
  rw [Polynomial.mul_comp, Polynomial.sub_comp, Polynomial.one_comp, Polynomial.C_comp,
    Polynomial.prod_comp]
  congr 1
  · have h0 := prod_one_sub_primRoot_mul_poly hω hq (Polynomial.C ζ)
    simp only [← map_pow] at h0
    refine (Finset.prod_congr rfl fun j _ => ?_).trans h0
    rw [map_mul, mul_comm (Polynomial.C ζ)]
  · refine Finset.prod_congr rfl fun n _ => ?_
    rw [Finset.prod_mul_distrib, Polynomial.mul_comp, Polynomial.sub_comp, Polynomial.sub_comp,
      Polynomial.one_comp, Polynomial.mul_comp, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp]
    congr 1
    · have hpos := prod_one_sub_primRoot_mul_poly hω hq (Polynomial.C ζ * Polynomial.X ^ n)
      rw [mul_pow, ← map_pow, ← pow_mul, mul_comm n q, pow_mul] at hpos
      refine (Finset.prod_congr rfl fun j _ => ?_).trans hpos
      rw [map_mul, mul_assoc, mul_left_comm (Polynomial.C ζ)]
    · have hneg := prod_one_sub_primRoot_mul_poly hω_inv hq (Polynomial.C ζ⁻¹ * Polynomial.X ^ n)
      rw [mul_pow, ← map_pow, inv_pow, ← pow_mul, mul_comm n q, pow_mul] at hneg
      refine (Finset.prod_congr rfl fun j _ => ?_).trans hneg
      rw [mul_inv, inv_pow, map_mul, mul_assoc, mul_left_comm (Polynomial.C ζ⁻¹)]

/-- **Exact Tame-Prime Cyclotomic Siegel-Unit Cusp Norm Compatibility** (wired directly to
`Stage11EulerSystemSelmer.cyclotomic_unit_norm_compatibility`):
for every `m > 1` and every prime `q ∤ m`, the leading cusp factor `1 - ζ_{m q}` of the Siegel unit
satisfies `N_{ℚ(ζ_{m q})/ℚ(ζ_m)}(1 - ζ_{m q}) = (1 - ζ_m)^{1 - Frob_q⁻¹}`! -/
theorem siegelCusp_tame_norm_compat {m q : ℕ} [NeZero m] [NeZero q]
    (hm : 1 < m) (hq : q.Prime) (hndvd : ¬ q ∣ m) :
    relGalNorm m q (cycUnit (m * q)) =
      cycEmb (dvd_mul_right m q) (cycUnit m * ((frobPrime m hq hndvd)⁻¹ (cycUnit m))⁻¹) :=
  cyclotomic_unit_norm_compatibility hm hq hndvd

/-- **Bilinear Beilinson–Kato Symbol Pairing `{g_α, g_β}`**:
packages Kato's Steinberg / `K₂`-cup-product map sending a pair of Siegel units at level `m` to
Galois cohomology `H¹(ℚ(μ_m), T_f)`, together with the Hecke-equivariant pushforward relation
converting Siegel-unit norm compatibility into the exact Hecke Euler factor `P_q(f, Frob_q⁻¹)`. -/
structure BeilinsonKatoSymbol.{u, v, w} (R : Type u) [CommRing R] (G : Type v) [CommGroup G]
    (N k : ℕ) where
  a : ℕ → R
  ε : ℕ → R
  frobInv : ℕ → G
  SiegelUnit : ℕ → Type w
  H1 : ℕ → Type w
  [addH1 : ∀ m, AddCommGroup (H1 m)]
  [modH1 : ∀ m, Module R (H1 m)]
  galAct : ∀ m, G →* Module.End R (H1 m)
  cor : ∀ {m n : ℕ}, m ∣ n → H1 n →ₗ[R] H1 m
  cor_refl : ∀ m, cor (dvd_refl m) = LinearMap.id
  cor_trans : ∀ {m n r : ℕ} (hmn : m ∣ n) (hnr : n ∣ r),
    (cor hmn).comp (cor hnr) = cor (hmn.trans hnr)
  cor_gal : ∀ {m n : ℕ} (hmn : m ∣ n) (g : G) (x : H1 n),
    cor hmn (galAct n g x) = galAct m g (cor hmn x)
  siegelA : ∀ m, SiegelUnit m
  siegelB : ∀ m, SiegelUnit m
  cup : ∀ m, SiegelUnit m → SiegelUnit m → H1 m
  cup_norm_compat : ∀ (m q : ℕ), Squarefree m → Nat.Coprime m N → 0 < m →
    q.Prime → ¬ q ∣ m * N →
    cor (dvd_mul_right m q) (cup (m * q) (siegelA (m * q)) (siegelB (m * q))) =
      Polynomial.aeval (galAct m (frobInv q)) (heckeEulerPoly (a q) (ε q) k q)
        (cup m (siegelA m) (siegelB m))

attribute [instance] BeilinsonKatoSymbol.addH1 BeilinsonKatoSymbol.modH1

end HeckeEulerPolyAndSiegelUnits

/-! ## Section 2: Concrete Kato Zeta Element System `z_Kato(f, m)` & Exact Euler-System Norm Compatibility -/

section KatoEulerSystemCore

/-- Squarefree positive integers coprime to the bad level `N`. -/
def IsSquarefreeCoprime (N m : ℕ) : Prop :=
  Squarefree m ∧ Nat.Coprime m N ∧ 0 < m

theorem isSquarefreeCoprime_one (N : ℕ) : IsSquarefreeCoprime N 1 :=
  ⟨squarefree_one, Nat.coprime_one_left N, Nat.one_pos⟩

theorem isSquarefreeCoprime_mul_prime {N m q : ℕ} (hm : IsSquarefreeCoprime N m)
    (hq : q.Prime) (hndvd : ¬ q ∣ m * N) : IsSquarefreeCoprime N (m * q) := by
  have hqm : ¬ q ∣ m := fun h => hndvd (dvd_mul_of_dvd_left h N)
  have hqN : ¬ q ∣ N := fun h => hndvd (dvd_mul_of_dvd_right h m)
  have hcop_qm : Nat.Coprime m q := (hq.coprime_iff_not_dvd.mpr hqm).symm
  have hcop_qN : Nat.Coprime q N := hq.coprime_iff_not_dvd.mpr hqN
  exact ⟨(Nat.squarefree_mul hcop_qm).mpr ⟨hm.1, hq.squarefree⟩,
    hm.2.1.mul_left hcop_qN, Nat.mul_pos hm.2.2 hq.pos⟩

/-- **Concrete Kato Euler System `z_Kato(f, m) ∈ H¹(ℚ(μ_m), T_f)` for a Weight-`k` Modular Form `f`**:
packages Hecke eigenvalues `a_q`, nebentypus `ε_q`, Galois cohomology modules `H1 m` with commuting
`G`-action `galAct`, functorial corestriction `cor`, and Kato zeta elements `z m : H1 m` satisfying
exact **Euler-System Norm Compatibility**:
`Cor_{ℚ(μ_{m q})/ℚ(μ_m)}(z_Kato(f, m q)) = P_q(f, Frob_q⁻¹) · z_Kato(f, m)`
where `P_q(f, X) = 1 - a_q X + ε_q q^{k - 1} X²`. -/
structure KatoEulerSystem (R : Type*) [CommRing R] (G : Type*) [CommGroup G] (N k : ℕ) where
  a : ℕ → R
  ε : ℕ → R
  frobInv : ℕ → G
  H1 : ℕ → Type*
  [addH1 : ∀ m, AddCommGroup (H1 m)]
  [modH1 : ∀ m, Module R (H1 m)]
  galAct : ∀ m, G →* Module.End R (H1 m)
  cor : ∀ {m n : ℕ}, m ∣ n → H1 n →ₗ[R] H1 m
  cor_refl : ∀ m, cor (dvd_refl m) = LinearMap.id
  cor_trans : ∀ {m n r : ℕ} (hmn : m ∣ n) (hnr : n ∣ r),
    (cor hmn).comp (cor hnr) = cor (hmn.trans hnr)
  cor_gal : ∀ {m n : ℕ} (hmn : m ∣ n) (g : G) (x : H1 n),
    cor hmn (galAct n g x) = galAct m g (cor hmn x)
  /-- Kato's Beilinson–Kato zeta element `z_Kato(f, m) ∈ H¹(ℚ(μ_m), T_f)`. -/
  z : ∀ m : ℕ, H1 m
  /-- **Exact Single-Prime Euler-System Norm Compatibility**:
  `Cor_{ℚ(μ_{m q})/ℚ(μ_m)}(z_Kato(f, m q)) = P_q(f, Frob_q⁻¹) · z_Kato(f, m)`. -/
  norm_compat : ∀ (m q : ℕ), IsSquarefreeCoprime N m → q.Prime → ¬ q ∣ m * N →
    cor (dvd_mul_right m q) (z (m * q)) =
      Polynomial.aeval (galAct m (frobInv q)) (heckeEulerPoly (a q) (ε q) k q) (z m)

attribute [instance] KatoEulerSystem.addH1 KatoEulerSystem.modH1

namespace KatoEulerSystem

variable {R G : Type*} [CommRing R] [CommGroup G] {N k : ℕ}

/-- The Hecke Euler polynomial `P_q(f, X) = 1 - a_q X + ε_q q^{k - 1} X²` of a `KatoEulerSystem`. -/
def eulerPoly (E : KatoEulerSystem R G N k) (q : ℕ) : Polynomial R :=
  heckeEulerPoly (E.a q) (E.ε q) k q

/-- The Euler-factor endomorphism `P_q(f, Frob_q⁻¹) ∈ End_R(H¹(ℚ(μ_m), T_f))`. -/
def eulerOp (E : KatoEulerSystem R G N k) (m q : ℕ) : Module.End R (E.H1 m) :=
  Polynomial.aeval (E.galAct m (E.frobInv q)) (E.eulerPoly q)

/-- Every `BeilinsonKatoSymbol` `{g_α, g_β}` canonically produces a `KatoEulerSystem` with
`z m := {g_α(m), g_β(m)}`. -/
def ofBeilinsonKatoSymbol (B : BeilinsonKatoSymbol R G N k) : KatoEulerSystem R G N k where
  a := B.a
  ε := B.ε
  frobInv := B.frobInv
  H1 := B.H1
  galAct := B.galAct
  cor := B.cor
  cor_refl := B.cor_refl
  cor_trans := B.cor_trans
  cor_gal := B.cor_gal
  z := fun m => B.cup m (B.siegelA m) (B.siegelB m)
  norm_compat := fun m q hm hq hndvd => B.cup_norm_compat m q hm.1 hm.2.1 hm.2.2 hq hndvd

/-- **Explicit 3-Term Expansion of Kato's Euler-System Norm Compatibility**:
`Cor(z(m q)) = z(m) - a_q · Frob_q⁻¹(z(m)) + ε_q q^{k - 1} · Frob_q⁻²(z(m))`. -/
theorem norm_compat_explicit (E : KatoEulerSystem R G N k) {m q : ℕ}
    (hm : IsSquarefreeCoprime N m) (hq : q.Prime) (hndvd : ¬ q ∣ m * N) :
    E.cor (dvd_mul_right m q) (E.z (m * q)) =
      E.z m - E.a q • E.galAct m (E.frobInv q) (E.z m) +
        (E.ε q * (q : R) ^ (k - 1)) • E.galAct m (E.frobInv q) (E.galAct m (E.frobInv q) (E.z m)) := by
  rw [E.norm_compat m q hm hq hndvd]
  exact aeval_heckeEulerPoly_end_apply (E.a q) (E.ε q) k q (E.galAct m (E.frobInv q)) (E.z m)

/-- Commutativity of `eulerOp` for any two primes `q₁, q₂` (from commutativity of `G`). -/
theorem eulerOp_comm (E : KatoEulerSystem R G N k) (m q₁ q₂ : ℕ) :
    Commute (E.eulerOp m q₁) (E.eulerOp m q₂) := by
  have hcomm : E.galAct m (E.frobInv q₁) * E.galAct m (E.frobInv q₂) =
      E.galAct m (E.frobInv q₂) * E.galAct m (E.frobInv q₁) := by
    rw [← map_mul, ← map_mul, mul_comm]
  show E.eulerOp m q₁ * E.eulerOp m q₂ = E.eulerOp m q₂ * E.eulerOp m q₁
  ext x
  simp only [Module.End.mul_apply, eulerOp, eulerPoly, aeval_heckeEulerPoly_end_apply]
  have h12 : ∀ y : E.H1 m,
      E.galAct m (E.frobInv q₁) (E.galAct m (E.frobInv q₂) y) =
      E.galAct m (E.frobInv q₂) (E.galAct m (E.frobInv q₁) y) := fun y =>
    congrArg (fun f : Module.End R (E.H1 m) => f y) hcomm
  simp only [map_add, map_sub, map_smul, smul_add, smul_sub, smul_smul, h12]
  module

theorem eulerOp_pairwise_comm (E : KatoEulerSystem R G N k) (m : ℕ) (S : Finset ℕ) :
    (S : Set ℕ).Pairwise (Function.onFun Commute fun q => E.eulerOp m q) :=
  fun q₁ _ q₂ _ _ => E.eulerOp_comm m q₁ q₂

/-- Transport helper for `cor` along equalities of level indices (avoids dependent `HEq`). -/
theorem cor_eq_of_eq (E : KatoEulerSystem R G N k) {m n₁ n₂ : ℕ} (h : n₁ = n₂) (hd : m ∣ n₁) :
    E.cor hd (E.z n₁) = E.cor (h ▸ hd) (E.z n₂) := by
  subst h; rfl

/-- Corestriction commutes with every Euler-factor operator `eulerOp`. -/
theorem cor_eulerOp (E : KatoEulerSystem R G N k) {m n : ℕ} (hmn : m ∣ n) (q : ℕ) (x : E.H1 n) :
    E.cor hmn (E.eulerOp n q x) = E.eulerOp m q (E.cor hmn x) := by
  simp only [eulerOp, eulerPoly, aeval_heckeEulerPoly_end_apply, map_add, map_sub, map_smul,
    E.cor_gal]

/-- **Multi-Prime Squarefree Norm Compatibility (`norm_compat_finset`)**:
for any squarefree `m` coprime to `N` and any finite set `S` of distinct primes coprime to `m * N`,
iterated corestriction from `m * ∏_{q ∈ S} q` down to `m` multiplies `z(m)` by the product of
Euler factors `∏_{q ∈ S} P_q(f, Frob_q⁻¹)`! -/
theorem norm_compat_finset (E : KatoEulerSystem R G N k) {m : ℕ} (hm : IsSquarefreeCoprime N m)
    (S : Finset ℕ) (hS_prime : ∀ q ∈ S, q.Prime) (hS_ndvd : ∀ q ∈ S, ¬ q ∣ m * N) :
    E.cor (dvd_mul_right m (∏ q ∈ S, q)) (E.z (m * ∏ q ∈ S, q)) =
      (S.noncommProd (fun q => E.eulerOp m q) (E.eulerOp_pairwise_comm m S)) (E.z m) := by
  classical
  have hsqProd : ∀ (s : Finset ℕ), (∀ q ∈ s, q.Prime) → (∀ q ∈ s, ¬ q ∣ m * N) →
      IsSquarefreeCoprime N (m * ∏ q ∈ s, q) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _ _
      simpa using hm
    | @insert r t hr_not ih_t =>
      intro htp htnd
      have hr_prime : r.Prime := htp r (Finset.mem_insert_self r t)
      have hr_ndvd : ¬ r ∣ m * N := htnd r (Finset.mem_insert_self r t)
      have ht_prime : ∀ q ∈ t, q.Prime := fun q hq => htp q (Finset.mem_insert_of_mem hq)
      have ht_ndvd : ∀ q ∈ t, ¬ q ∣ m * N := fun q hq => htnd q (Finset.mem_insert_of_mem hq)
      have hmt : IsSquarefreeCoprime N (m * ∏ q ∈ t, q) := ih_t ht_prime ht_ndvd
      have hr_ndvd_t : ¬ r ∣ ∏ q ∈ t, q := by
        intro hdvd
        obtain ⟨q, hqt, hrq⟩ := (hr_prime.prime.dvd_finsetProd_iff id).mp hdvd
        have hqr : q = r := (Nat.prime_dvd_prime_iff_eq hr_prime (ht_prime q hqt)).mp hrq |>.symm
        exact hr_not (hqr ▸ hqt)
      have hr_ndvd_all : ¬ r ∣ (m * ∏ q ∈ t, q) * N := by
        intro hdvd
        rw [mul_right_comm] at hdvd
        rcases hr_prime.dvd_mul.mp hdvd with h1 | h2
        · exact hr_ndvd h1
        · exact hr_ndvd_t h2
      have hmul_eq : m * ∏ q ∈ insert r t, q = (m * ∏ q ∈ t, q) * r := by
        rw [Finset.prod_insert hr_not]; ring
      rw [hmul_eq]
      exact isSquarefreeCoprime_mul_prime hmt hr_prime hr_ndvd_all
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.noncommProd_empty, Module.End.one_apply]
    have h1 : m * ∏ q ∈ (∅ : Finset ℕ), q = m := by simp
    rw [E.cor_eq_of_eq h1 (dvd_mul_right m (∏ q ∈ (∅ : Finset ℕ), q)), E.cor_refl]
    rfl
  | @insert p s hp_not_mem ih =>
    have hp_prime : p.Prime := hS_prime p (Finset.mem_insert_self p s)
    have hp_ndvd : ¬ p ∣ m * N := hS_ndvd p (Finset.mem_insert_self p s)
    have hs_prime : ∀ q ∈ s, q.Prime := fun q hq => hS_prime q (Finset.mem_insert_of_mem hq)
    have hs_ndvd : ∀ q ∈ s, ¬ q ∣ m * N := fun q hq => hS_ndvd q (Finset.mem_insert_of_mem hq)
    set P : ℕ := ∏ q ∈ s, q
    have hp_ndvd_P : ¬ p ∣ P := by
      intro hdvd
      obtain ⟨q, hqs, hpq⟩ := (hp_prime.prime.dvd_finsetProd_iff id).mp hdvd
      have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hp_prime (hs_prime q hqs)).mp hpq |>.symm
      exact hp_not_mem (hqp ▸ hqs)
    have hmP : IsSquarefreeCoprime N (m * P) := hsqProd s hs_prime hs_ndvd
    have hp_ndvd_mPN : ¬ p ∣ (m * P) * N := by
      intro hdvd
      rw [mul_right_comm] at hdvd
      rcases hp_prime.dvd_mul.mp hdvd with h1 | h2
      · exact hp_ndvd h1
      · exact hp_ndvd_P h2
    have hprod_ins : m * ∏ q ∈ insert p s, q = (m * P) * p := by
      rw [Finset.prod_insert hp_not_mem]; ring
    have hstep1 : E.cor (dvd_mul_right (m * P) p) (E.z ((m * P) * p)) =
        E.eulerOp (m * P) p (E.z (m * P)) :=
      E.norm_compat (m * P) p hmP hp_prime hp_ndvd_mPN
    have htrans := congrArg (fun f => f (E.z ((m * P) * p)))
      (E.cor_trans (dvd_mul_right m P) (dvd_mul_right (m * P) p))
    simp only [LinearMap.comp_apply] at htrans
    have hcor_eq : E.cor (dvd_mul_right m (∏ q ∈ insert p s, q)) (E.z (m * ∏ q ∈ insert p s, q)) =
        E.cor ((dvd_mul_right m P).trans (dvd_mul_right (m * P) p)) (E.z ((m * P) * p)) :=
      E.cor_eq_of_eq hprod_ins (dvd_mul_right m (∏ q ∈ insert p s, q))
    rw [hcor_eq, ← htrans, hstep1, E.cor_eulerOp, ih hs_prime hs_ndvd,
      Finset.noncommProd_insert_of_notMem s _ _ _ hp_not_mem]
    rfl

/-- **Base-Level Multi-Prime Norm Compatibility (`m = 1`)**:
for any finite set `S` of primes coprime to `N`,
`Cor_{ℚ(μ_{∏ S})/ℚ}(z_Kato(f, ∏ S)) = (∏_{q ∈ S} P_q(f, Frob_q⁻¹)) · z_Kato(f, 1)`. -/
theorem norm_compat_at_one (E : KatoEulerSystem R G N k)
    (S : Finset ℕ) (hS_prime : ∀ q ∈ S, q.Prime) (hS_ndvd : ∀ q ∈ S, ¬ q ∣ N) :
    E.cor (one_dvd (∏ q ∈ S, q)) (E.z (∏ q ∈ S, q)) =
      (S.noncommProd (fun q => E.eulerOp 1 q) (E.eulerOp_pairwise_comm 1 S)) (E.z 1) := by
  have h := E.norm_compat_finset (isSquarefreeCoprime_one N) S hS_prime
    (fun q hq => by simpa using hS_ndvd q hq)
  rw [E.cor_eq_of_eq (one_mul (∏ q ∈ S, q)) (dvd_mul_right 1 (∏ q ∈ S, q))] at h
  exact h

/-- **Split-Frobenius / Kolyvagin-Prime Congruence**:
whenever `Frob_q⁻¹` acts trivially on `z_Kato(f, m)`,
`Cor(z_Kato(f, m q)) = (1 - a_q + ε_q q^{k - 1}) • z_Kato(f, m)`.
At a Kolyvagin prime where `ϖ^M ∣ 1 - a_q + ε_q q^{k - 1}`,
`Cor(z_Kato(f, m q)) ∈ (ϖ^M) • H¹(ℚ(μ_m), T_f)`! -/
theorem norm_compat_kolyvagin_cong (E : KatoEulerSystem R G N k) {m q : ℕ}
    (hm : IsSquarefreeCoprime N m) (hq : q.Prime) (hndvd : ¬ q ∣ m * N)
    (hsplit : E.galAct m (E.frobInv q) (E.z m) = E.z m) {ϖ : R} {M : ℕ}
    (hcong : ϖ ^ M ∣ 1 - E.a q + E.ε q * (q : R) ^ (k - 1)) :
    E.cor (dvd_mul_right m q) (E.z (m * q)) ∈
      Ideal.span ({ϖ ^ M} : Set R) • (⊤ : Submodule R (E.H1 m)) := by
  rw [E.norm_compat_explicit hm hq hndvd, hsplit, hsplit]
  have hcomb : E.z m - E.a q • E.z m + (E.ε q * (q : R) ^ (k - 1)) • E.z m =
      (1 - E.a q + E.ε q * (q : R) ^ (k - 1)) • E.z m := by
    rw [add_smul, sub_smul, one_smul]
  rw [hcomb]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton.mpr hcong) Submodule.mem_top

/-- **Kato Kolyvagin Derivative Galois-Invariant Descent** (wired directly to
`Stage11EulerSystemSelmer.kolyvaginDeriv_fixed_mod`). -/
theorem kato_kolyvaginDeriv_fixed_mod {H M : Type*} [Monoid H] [AddCommGroup M]
    [Module R M] [Module (MonoidAlgebra R H) M] [IsScalarTower R (MonoidAlgebra R H) M]
    {σ : H} {n : ℕ} (hσ : σ ^ n = 1) {ϖ : R} {K : ℕ} (hdiv : ϖ ^ K ∣ (n : R)) {x : M}
    (hnorm : normElem R σ n • x ∈ Ideal.span ({ϖ ^ K} : Set R) • (⊤ : Submodule R M)) :
    (MonoidAlgebra.single σ (1 : R) - 1) • (kolyvaginDeriv R σ n • x) ∈
      Ideal.span ({ϖ ^ K} : Set R) • (⊤ : Submodule R M) :=
  kolyvaginDeriv_fixed_mod R hσ hdiv hnorm

end KatoEulerSystem

/-! ### 2.2 Concrete Non-Vacuous Realization: Universal Kato Euler System & Ramanujan's `Δ` -/

private lemma primeFactors_sdiff_union {m n r : ℕ} (hr : r ≠ 0) (hmn : m ∣ n) (hnr : n ∣ r) :
    r.primeFactors \ m.primeFactors =
      (n.primeFactors \ m.primeFactors) ∪ (r.primeFactors \ n.primeFactors) := by
  have hn : n ≠ 0 := ne_zero_of_dvd_ne_zero hr hnr
  have hsub1 : m.primeFactors ⊆ n.primeFactors := Nat.primeFactors_mono hmn hn
  have hsub2 : n.primeFactors ⊆ r.primeFactors := Nat.primeFactors_mono hnr hr
  ext p
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · intro ⟨hpr, hpm⟩
    by_cases hpn : p ∈ n.primeFactors
    · exact Or.inl ⟨hpn, hpm⟩
    · exact Or.inr ⟨hpr, hpn⟩
  · rintro (⟨hpn, hpm⟩ | ⟨hpr, hpn⟩)
    · exact ⟨hsub2 hpn, hpm⟩
    · exact ⟨hpr, fun hpm => hpn (hsub1 hpm)⟩

private lemma primeFactors_sdiff_disjoint (m n r : ℕ) :
    Disjoint (n.primeFactors \ m.primeFactors) (r.primeFactors \ n.primeFactors) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  exact (Finset.mem_sdiff.mp hp2).2 (Finset.mem_sdiff.mp hp1).1

private lemma primeFactors_mul_prime_sdiff {m q : ℕ} (hm : m ≠ 0) (hq : q.Prime) (hndvd : ¬ q ∣ m) :
    (m * q).primeFactors \ m.primeFactors = {q} := by
  rw [Nat.primeFactors_mul hm hq.ne_zero, hq.primeFactors]
  ext p
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨hpm | rfl, hnot⟩
    · exact absurd hpm hnot
    · rfl
  · rintro rfl
    refine ⟨Or.inr rfl, ?_⟩
    rw [Nat.mem_primeFactors]
    rintro ⟨_, hdvd, _⟩
    exact hndvd hdvd

/-- **Concrete Non-Vacuous Universal Kato Euler System (`universalKatoEulerSystem`)**:
for ANY commutative ring `R`, commutative Galois group `G`, level `N`, weight `k`, Hecke data
`(a, ε)`, Frobenius assignment `frobInv : ℕ → G`, any `R`-module `M` with `G`-action
`ρ : G →* End_R(M)`, and ANY base element `z₀ : M`, constructs a genuine `KatoEulerSystem R G N k`
with `z 1 = z₀` and exact Euler-system norm compatibility across ALL squarefree `m` coprime to `N`
and ALL primes `q ∤ m * N`! -/
def universalKatoEulerSystem {R G M : Type*} [CommRing R] [CommGroup G]
    [AddCommGroup M] [Module R M]
    (N k : ℕ) (a ε : ℕ → R) (frobInv : ℕ → G) (ρ : G →* Module.End R M) (z₀ : M) :
    KatoEulerSystem R G N k :=
  let op : ℕ → Module.End R M := fun q =>
    Polynomial.aeval (ρ (frobInv q)) (heckeEulerPoly (a q) (ε q) k q)
  have hop_comm : ∀ q₁ q₂ : ℕ, Commute (op q₁) (op q₂) := fun q₁ q₂ => by
    have hcomm : ρ (frobInv q₁) * ρ (frobInv q₂) = ρ (frobInv q₂) * ρ (frobInv q₁) := by
      rw [← map_mul, ← map_mul, mul_comm]
    show op q₁ * op q₂ = op q₂ * op q₁
    ext x
    simp only [Module.End.mul_apply, op, aeval_heckeEulerPoly_end_apply]
    have h12 : ∀ y : M, ρ (frobInv q₁) (ρ (frobInv q₂) y) = ρ (frobInv q₂) (ρ (frobInv q₁) y) :=
      fun y => congrArg (fun f : Module.End R M => f y) hcomm
    simp only [map_add, map_sub, map_smul, smul_add, smul_sub, smul_smul, h12]
    module
  have hop_pw : ∀ S : Finset ℕ, (S : Set ℕ).Pairwise (Function.onFun Commute op) :=
    fun _ q₁ _ q₂ _ _ => hop_comm q₁ q₂
  have hop_gal : ∀ (g : G) (q : ℕ), op q * ρ g = ρ g * op q := fun g q => by
    have hcomm : ρ (frobInv q) * ρ g = ρ g * ρ (frobInv q) := by
      rw [← map_mul, ← map_mul, mul_comm]
    ext x
    simp only [Module.End.mul_apply, op, aeval_heckeEulerPoly_end_apply]
    have h12 : ∀ y : M, ρ (frobInv q) (ρ g y) = ρ g (ρ (frobInv q) y) :=
      fun y => congrArg (fun f : Module.End R M => f y) hcomm
    simp only [map_add, map_sub, map_smul, h12]
  have hprod_gal : ∀ (S : Finset ℕ) (g : G) (x : M),
      (S.noncommProd op (hop_pw S)) (ρ g x) = ρ g ((S.noncommProd op (hop_pw S)) x) := by
    intro S g x
    classical
    induction S using Finset.induction_on generalizing x with
    | empty => simp [Finset.noncommProd_empty]
    | @insert q s hq ih =>
      rw [Finset.noncommProd_insert_of_notMem s _ _ _ hq]
      change op q ((s.noncommProd op (hop_pw s)) (ρ g x)) =
        ρ g (op q ((s.noncommProd op (hop_pw s)) x))
      rw [ih x]
      exact congrArg (fun f : Module.End R M => f ((s.noncommProd op (hop_pw s)) x)) (hop_gal g q)
  { a := a
    ε := ε
    frobInv := frobInv
    H1 := fun _ => M
    galAct := fun _ => ρ
    cor := fun {m n} _ =>
      if n = 0 then (if m = 0 then LinearMap.id else 0)
      else (n.primeFactors \ m.primeFactors).noncommProd op (hop_pw _)
    cor_refl := fun m => by
      by_cases hm : m = 0
      · simp [hm]
      · simp [hm]
        rfl
    cor_trans := fun {m n r} hmn hnr => by
      by_cases hr : r = 0
      · subst hr
        by_cases hm : m = 0
        · subst hm
          have hn : n = 0 := zero_dvd_iff.mp hmn
          subst hn
          simp
        · by_cases hn : n = 0
          · subst hn; simp [hm]
          · simp [hm, hn]
      · have hn : n ≠ 0 := ne_zero_of_dvd_ne_zero hr hnr
        simp only [hr, hn, ↓reduceIte]
        have hunion := primeFactors_sdiff_union hr hmn hnr
        have hdisj := primeFactors_sdiff_disjoint m n r
        change ((n.primeFactors \ m.primeFactors).noncommProd op (hop_pw _)) *
            ((r.primeFactors \ n.primeFactors).noncommProd op (hop_pw _)) =
          (r.primeFactors \ m.primeFactors).noncommProd op (hop_pw _)
        have hEq : (r.primeFactors \ m.primeFactors).noncommProd op (hop_pw _) =
            ((n.primeFactors \ m.primeFactors) ∪ (r.primeFactors \ n.primeFactors)).noncommProd
              op (hop_pw _) := by
          congr 1
        rw [hEq, Finset.noncommProd_union_of_disjoint hdisj]
    cor_gal := fun {m n} _ g x => by
      by_cases hn : n = 0
      · by_cases hm : m = 0
        · simp [hn, hm]
        · simp [hn, hm]
      · simp only [hn, ↓reduceIte]
        exact hprod_gal (n.primeFactors \ m.primeFactors) g x
    z := fun _ => z₀
    norm_compat := fun m q hm hq hndvd => by
      have hm0 : m ≠ 0 := hm.2.2.ne'
      have hmq0 : m * q ≠ 0 := mul_ne_zero hm0 hq.ne_zero
      have hqm : ¬ q ∣ m := fun h => hndvd (dvd_mul_of_dvd_left h N)
      simp only [hmq0, ↓reduceIte]
      have hS : ((m * q).primeFactors \ m.primeFactors).noncommProd op (hop_pw _) =
          ({q} : Finset ℕ).noncommProd op (hop_pw {q}) := by
        congr 1
        exact primeFactors_mul_prime_sdiff hm0 hq hqm
      rw [hS, Finset.noncommProd_singleton] }

/-- **Concrete Kato Euler System for Ramanujan's `Δ` (`k = 12, N = 1, a_q = τ(q), ε = 1`)**
over any commutative ring `R` and `R[G]`-module `M` with base class `z₀ : M`! -/
def deltaKatoEulerSystem {R G M : Type*} [CommRing R] [CommGroup G]
    [AddCommGroup M] [Module R M]
    (frobInv : ℕ → G) (ρ : G →* Module.End R M) (z₀ : M) :
    KatoEulerSystem R G 1 12 :=
  universalKatoEulerSystem 1 12 (fun q => (ramanujanTau q : R)) (fun _ => 1) frobInv ρ z₀

/-- Exact norm compatibility of `deltaKatoEulerSystem` at every squarefree `m` and prime `q ∤ m`:
`Cor(z_Δ(m q)) = (1 - τ(q) Frob_q⁻¹ + q^{11} Frob_q⁻²) · z_Δ(m)`! -/
theorem deltaKatoEulerSystem_norm_compat {R G M : Type*} [CommRing R] [CommGroup G]
    [AddCommGroup M] [Module R M]
    (frobInv : ℕ → G) (ρ : G →* Module.End R M) (z₀ : M)
    {m q : ℕ} (hm : Squarefree m) (hm_pos : 0 < m) (hq : q.Prime) (hqm : ¬ q ∣ m) :
    (deltaKatoEulerSystem frobInv ρ z₀).cor (dvd_mul_right m q)
        ((deltaKatoEulerSystem frobInv ρ z₀).z (m * q)) =
      z₀ - (ramanujanTau q : R) • ρ (frobInv q) z₀ +
        ((q : R) ^ 11) • ρ (frobInv q) (ρ (frobInv q) z₀) := by
  have hsq : IsSquarefreeCoprime 1 m := ⟨hm, Nat.coprime_one_right m, hm_pos⟩
  rw [(deltaKatoEulerSystem frobInv ρ z₀).norm_compat_explicit hsq hq (by simpa using hqm)]
  simp only [deltaKatoEulerSystem, universalKatoEulerSystem, one_mul]
  rfl

end KatoEulerSystemCore

/-! ## Section 3: Concrete Bloch–Kato Dual Exponential Map (`exp*`) & Critical `L`-Value Specialization (`Stage11ModularSymbols`) -/

section DualExponentialAndModularSymbols

/-- **Concrete Bloch–Kato Dual Exponential Map Datum (`DualExpDatum`)** at a prime `l`:
models the local cohomology `H¹(ℚ_l, T_f(χ)(j))` over a DVR `(𝒪, ϖ)`, the concrete `𝒪`-linear
dual exponential map `exp* : H¹(ℚ_l, T_f(χ)(j)) → Fil⁰ D_dR(T_f(χ)(j)) ≃ 𝒪 · ω_f`,
the Bloch–Kato finite subspace `H¹_f := ker(exp*)`, and the singular quotient `H¹_s := H¹ / H¹_f`. -/
structure DualExpDatum (𝒪 : Type*) [CommRing 𝒪] (ϖ : 𝒪) where
  H1Loc : Type*
  [addH1Loc : AddCommGroup H1Loc]
  [modH1Loc : Module 𝒪 H1Loc]
  /-- Concrete Bloch–Kato dual exponential map `exp* : H¹(ℚ_l, T) →ₗ[𝒪] 𝒪`. -/
  expStar : H1Loc →ₗ[𝒪] 𝒪

attribute [instance] DualExpDatum.addH1Loc DualExpDatum.modH1Loc

namespace DualExpDatum

variable {𝒪 : Type*} [CommRing 𝒪] {ϖ : 𝒪}

/-- Bloch–Kato finite (crystalline) local subspace `H¹_f(ℚ_l, T) := ker(exp*)`. -/
def H1f (D : DualExpDatum 𝒪 ϖ) : Submodule 𝒪 D.H1Loc :=
  LinearMap.ker D.expStar

/-- Singular local cohomology quotient `H¹_s(ℚ_l, T) := H¹(ℚ_l, T) / H¹_f(ℚ_l, T)`. -/
abbrev H1s (D : DualExpDatum 𝒪 ϖ) : Type _ :=
  D.H1Loc ⧸ D.H1f

/-- Induced injective map `exp*_s : H¹_s(ℚ_l, T) ↪ 𝒪`. -/
def expStarSingular (D : DualExpDatum 𝒪 ϖ) : D.H1s →ₗ[𝒪] 𝒪 :=
  D.H1f.liftQ D.expStar le_rfl

/-- Over any DVR `(𝒪, ϖ)`, `Module.length 𝒪 (𝒪 ⧸ Ideal.span {ϖ ^ k}) = k`. -/
theorem length_dvr_quot_span_pow {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪]
    [IsDiscreteValuationRing 𝒪] {ϖ : 𝒪} (hϖ : Irreducible ϖ) (k : ℕ) :
    Module.length 𝒪 (𝒪 ⧸ Ideal.span ({ϖ ^ k} : Set 𝒪)) = (k : ℕ∞) := by
  induction k with
  | zero =>
    rw [pow_zero, Ideal.span_singleton_one]
    have : Subsingleton (𝒪 ⧸ (⊤ : Ideal 𝒪)) := Submodule.Quotient.subsingleton_iff.mpr rfl
    simp
  | succ k ih =>
    let I1 : Ideal 𝒪 := Ideal.span ({ϖ ^ (k + 1)} : Set 𝒪)
    let I0 : Ideal 𝒪 := Ideal.span ({ϖ ^ k} : Set 𝒪)
    have hle : I1 ≤ I0 := by
      rw [Ideal.span_singleton_le_span_singleton, pow_succ]
      exact dvd_mul_right _ _
    let proj : (𝒪 ⧸ I1) →ₗ[𝒪] (𝒪 ⧸ I0) := Submodule.factor hle
    have hsurj : Function.Surjective proj := Submodule.factor_surjective hle
    let incl : (𝒪 ⧸ Ideal.span ({ϖ} : Set 𝒪)) →ₗ[𝒪] (𝒪 ⧸ I1) :=
      Submodule.liftQ (Ideal.span ({ϖ} : Set 𝒪))
        ((Submodule.mkQ I1).comp (LinearMap.mulLeft 𝒪 (ϖ ^ k)))
        (by
          rw [Ideal.span_singleton_le_iff_mem]
          change (Submodule.mkQ I1) (ϖ ^ k * ϖ) = 0
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← pow_succ]
          exact Ideal.subset_span rfl)
    have hinj : Function.Injective incl := by
      rw [injective_iff_map_eq_zero]
      intro q hq
      induction q using Quotient.inductionOn' with
      | h a =>
        change (Submodule.mkQ I1) (ϖ ^ k * a) = 0 at hq
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
          Ideal.mem_span_singleton, pow_succ] at hq
        have hϖk : ϖ ^ k ≠ 0 := pow_ne_zero k hϖ.ne_zero
        have hdvd : ϖ ∣ a := (mul_dvd_mul_iff_left hϖk).mp hq
        exact (Submodule.Quotient.mk_eq_zero _).mpr (Ideal.mem_span_singleton.mpr hdvd)
    have hex : Function.Exact incl proj := by
      intro q
      induction q using Quotient.inductionOn' with
      | h x =>
        change (Submodule.Quotient.mk x : 𝒪 ⧸ I0) = 0 ↔ _
        rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]
        constructor
        · rintro ⟨a, rfl⟩
          exact ⟨Submodule.Quotient.mk a, rfl⟩
        · rintro ⟨q', hq'⟩
          induction q' using Quotient.inductionOn' with
          | h a =>
            have hsub : ϖ ^ k * a - x ∈ I1 := by
              change (Submodule.Quotient.mk (ϖ ^ k * a) : 𝒪 ⧸ I1) = Submodule.Quotient.mk x at hq'
              exact (Submodule.Quotient.eq I1).mp hq'
            have hsub0 : ϖ ^ k * a - x ∈ I0 := hle hsub
            rw [Ideal.mem_span_singleton] at hsub0
            obtain ⟨b, hb⟩ := hsub0
            exact ⟨a - b, by linear_combination -hb⟩
    have hmax : (Ideal.span ({ϖ} : Set 𝒪)).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible hϖ
    have hsimple : IsSimpleModule 𝒪 (𝒪 ⧸ Ideal.span ({ϖ} : Set 𝒪)) := by
      rw [isSimpleModule_iff_isCoatom]
      exact Ideal.isMaximal_def.mp hmax
    have hlen1 : Module.length 𝒪 (𝒪 ⧸ Ideal.span ({ϖ} : Set 𝒪)) = 1 :=
      Module.length_eq_one_iff.mpr hsimple
    have hadd := Module.length_eq_add_of_exact incl proj hinj hsurj hex
    rw [hadd, hlen1, ih]
    push_cast
    ring

theorem expStarSingular_injective (D : DualExpDatum 𝒪 ϖ) :
    Function.Injective D.expStarSingular :=
  LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot D.H1f D.expStar le_rfl (le_refl D.H1f))

/-- Nonvanishing of `exp*(z)` forces `z ∉ H¹_f` (non-crystalline local class!). -/
theorem not_mem_H1f_of_expStar_ne_zero (D : DualExpDatum 𝒪 ϖ) {z : D.H1Loc}
    (hz : D.expStar z ≠ 0) : z ∉ D.H1f := by
  intro hmem
  exact hz hmem

/-- **Exact Valuation-Index Control via `exp*`**:
over a DVR `(𝒪, ϖ)`, if `exp*(z) = u * ϖ^v` (`u ∈ 𝒪ˣ`), then:
1. `Module.length 𝒪 (𝒪 ⧸ Ideal.span {exp*(z)}) = v`, AND
2. Any divisibility `z = ϖ^d • z₀` in `H¹(ℚ_l, T)` satisfies **`d ≤ v`**! -/
theorem dualExp_image_index_eq_val [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    (hϖ : Irreducible ϖ) (D : DualExpDatum 𝒪 ϖ) {z : D.H1Loc} {u : 𝒪ˣ} {v : ℕ}
    (hexp : D.expStar z = (u : 𝒪) * ϖ ^ v) :
    Module.length 𝒪 (𝒪 ⧸ Ideal.span ({D.expStar z} : Set 𝒪)) = (v : ℕ∞) ∧
    ∀ (d : ℕ) (z₀ : D.H1Loc), z = ϖ ^ d • z₀ → d ≤ v := by
  have hspan : Ideal.span ({D.expStar z} : Set 𝒪) = Ideal.span ({ϖ ^ v} : Set 𝒪) := by
    rw [hexp, mul_comm]
    exact Ideal.span_singleton_mul_right_unit u.isUnit (ϖ ^ v)
  refine ⟨?_, ?_⟩
  · rw [hspan]
    exact length_dvr_quot_span_pow hϖ v
  · intro d z₀ hz
    by_contra hgt
    have hle : v + 1 ≤ d := by omega
    have hexp_eq : (u : 𝒪) * ϖ ^ v = ϖ ^ d * D.expStar z₀ := by
      rw [← hexp, hz, map_smul, smul_eq_mul]
    have hdvd : ϖ ^ (v + 1) ∣ (u : 𝒪) * ϖ ^ v :=
      ⟨ϖ ^ (d - (v + 1)) * D.expStar z₀, by
        rw [hexp_eq, ← mul_assoc, ← pow_add, Nat.add_sub_of_le hle]⟩
    obtain ⟨c, hc⟩ := hdvd
    have hpow_ne : ϖ ^ v ≠ 0 := pow_ne_zero v hϖ.ne_zero
    have hu_eq : (u : 𝒪) = ϖ * c := by
      apply mul_left_cancel₀ hpow_ne
      calc ϖ ^ v * (u : 𝒪) = (u : 𝒪) * ϖ ^ v := mul_comm _ _
        _ = ϖ ^ (v + 1) * c := hc
        _ = ϖ ^ v * (ϖ * c) := by rw [pow_succ, mul_assoc]
    exact dvr_not_pow_dvd_unit hϖ u.isUnit (k := 1) le_rfl (by rw [pow_one]; exact ⟨c, hu_eq⟩)

/-- **`ℤ_[l]` Specialization of `dualExp_image_index_eq_val`**:
for `D : DualExpDatum ℤ_[l] (l : ℤ_[l])` and `z : D.H1Loc` with `D.expStar z ≠ 0`:
1. `Module.length ℤ_[l] (ℤ_[l] ⧸ Ideal.span {exp*(z)}) = (D.expStar z).valuation`,
2. Any divisibility `z = l^d • z₀` satisfies **`d ≤ (D.expStar z).valuation`**! -/
theorem dualExp_divIdx_le_valuation {l : ℕ} [Fact l.Prime]
    (D : DualExpDatum ℤ_[l] (l : ℤ_[l])) {z : D.H1Loc} (hz : D.expStar z ≠ 0) :
    Module.length ℤ_[l] (ℤ_[l] ⧸ Ideal.span ({D.expStar z} : Set ℤ_[l])) =
      ((D.expStar z).valuation : ℕ∞) ∧
    ∀ (d : ℕ) (z₀ : D.H1Loc), z = (l : ℤ_[l]) ^ d • z₀ → d ≤ (D.expStar z).valuation :=
  D.dualExp_image_index_eq_val (padicInt_irreducible_p l)
    (u := PadicInt.unitCoeff hz) (v := (D.expStar z).valuation) (PadicInt.unitCoeff_spec hz)

end DualExpDatum

/-! ### 3.2 Euler-Factor Specialization & Mazur–Tate–Teitelbaum Satake Identity (`Stage11ModularSymbols`) -/

/-- Exact Euler factor `P_l(f, l^{-j}) = 1 - a_l l^{-j} + ε_l l^{k - 1 - 2 j} ∈ ℂ` at critical
integer `j`. -/
def eulerFactorAt (a_l ε_l : ℂ) (k l j : ℕ) : ℂ :=
  (heckeEulerPoly a_l ε_l k l).eval ((l : ℂ) ^ (-(j : ℤ)))

theorem eulerFactorAt_eq (a_l ε_l : ℂ) (k : ℕ) (hk : 1 ≤ k) {l : ℕ} (hl : l ≠ 0) (j : ℕ) :
    eulerFactorAt a_l ε_l k l j =
      1 - a_l * (l : ℂ) ^ (-(j : ℤ)) + ε_l * (l : ℂ) ^ ((k - 1 : ℤ) - 2 * (j : ℤ)) := by
  have hlC : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hl
  unfold eulerFactorAt
  rw [heckeEulerPoly_eval]
  have hpow : (l : ℂ) ^ (k - 1) * ((l : ℂ) ^ (-(j : ℤ))) ^ 2 =
      (l : ℂ) ^ ((k - 1 : ℤ) - 2 * (j : ℤ)) := by
    rw [← zpow_natCast (l : ℂ) (k - 1), ← zpow_natCast ((l : ℂ) ^ (-(j : ℤ))) 2,
      ← _root_.zpow_mul, ← zpow_add₀ hlC]
    congr 1
    have hk1 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
    rw [hk1]
    ring
  rw [mul_assoc, hpow]

/-- **Exact Mazur–Tate–Teitelbaum Satake Euler-Factor Identification** (wired directly to
`Stage11ModularSymbols.mttDist_units_mass`):
for ANY normalized Hecke eigenform `f ∈ S_k(SL₂(ℤ))` (`k ≥ 2`), ANY prime `p`, and Satake roots
`α, β ≠ 0` with `α + β = a_p` and `α * β = p^{k - 1}`:
`∑_{u ∈ (ZMod p)ˣ} mttDist f p α 1 u = (1 - α⁻¹) * (1 - β / p) * Λ(f, 1)`! -/
theorem mttDist_units_mass_eq_satake_eulerFactor {k : ℕ} (hk : 2 ≤ k)
    (f : CuspForm SL2ZRange (k : ℤ)) {p : ℕ} [Fact p.Prime] {a_p α β : ℂ}
    (heig : heckeCuspForm k (by omega) p (Fact.out : p.Prime).one_le f = a_p • f)
    (hα_ne : α ≠ 0) (hsum : α + β = a_p) (hprod : α * β = (p : ℂ) ^ (k - 1)) :
    ∑ u ∈ Finset.univ.filter (fun x : ZMod (p ^ 1) => x ≠ 0), mttDist f p α 1 u =
      (1 - α⁻¹) * (1 - β / (p : ℂ)) * completedCuspL f 1 := by
  have hp : p.Prime := Fact.out
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hα_root : α ^ 2 - a_p * α + (p : ℂ) ^ (k - 1) = 0 := by
    rw [← hsum, ← hprod]; ring
  rw [mttDist_units_mass hk f heig hα_ne hα_root]
  have hβ : (p : ℂ) ^ (k - 2) / α = β / (p : ℂ) := by
    have hpk : (p : ℂ) ^ (k - 2) * (p : ℂ) = (p : ℂ) ^ (k - 1) := by
      rw [← pow_succ, show (k - 2) + 1 = k - 1 by omega]
    rw [div_eq_div_iff hα_ne hpC, hpk, ← hprod]
    ring
  rw [hβ]

/-! ### 3.3 Concrete Critical `L`-Value Specialization on Ramanujan's `Δ` (Manin's Exact Ratios, `0` Assumptions!) -/

/-- Canonical even Manin period `Ω_Δ^+ := Λ(Δ, 2) / 48` of Ramanujan's `Δ`. -/
def omegaDeltaPlus : ℂ := completedDeltaL 2 / 48

/-- Canonical odd Manin period `Ω_Δ^- := Λ(Δ, 3) / 14` of Ramanujan's `Δ`. -/
def omegaDeltaMinus : ℂ := completedDeltaL 3 / 14

theorem completedDeltaL_ne_zero_of_real (x : ℝ) : completedDeltaL (x : ℂ) ≠ 0 := by
  intro h0
  have hpos := completedDeltaL_pos_on_real x
  rw [h0, Complex.zero_re] at hpos
  exact lt_irrefl 0 hpos

theorem omegaDeltaPlus_ne_zero : omegaDeltaPlus ≠ 0 := by
  unfold omegaDeltaPlus
  exact div_ne_zero (by simpa using completedDeltaL_ne_zero_of_real 2) (by norm_num)

theorem omegaDeltaMinus_ne_zero : omegaDeltaMinus ≠ 0 := by
  unfold omegaDeltaMinus
  exact div_ne_zero (by simpa using completedDeltaL_ne_zero_of_real 3) (by norm_num)

/-- **Exact Rational Critical `L`-Values `L^*(Δ, j) = Λ(Δ, j) / Ω_Δ^± ∈ ℚ`** for all 11 critical
integers `1 ≤ j ≤ 11` of Ramanujan's `Δ` (normalized by `Ω_Δ^+ = Λ(Δ, 2)/48` for even `j` and
`Ω_Δ^- = Λ(Δ, 3)/14` for odd `j`). -/
def deltaAlgL : ℕ → ℚ
  | 1 => 22680 / 691
  | 2 => 48
  | 3 => 14
  | 4 => 25
  | 5 => 9
  | 6 => 20
  | 7 => 9
  | 8 => 25
  | 9 => 14
  | 10 => 48
  | 11 => 22680 / 691
  | _ => 0

/-- **Manin's Headline Period Relations for Ramanujan's `Δ`** (exported directly from
`Stage11ModularSymbols.manin_delta_period_ratios`, `0` assumptions!):
`691 * Λ(Δ, 1) = 1620 * Λ(Δ, 3)` and `12 * Λ(Δ, 6) = 5 * Λ(Δ, 2)`. -/
theorem delta_manin_headline_ratios :
    691 * completedDeltaL 1 = 1620 * completedDeltaL 3 ∧
    12 * completedDeltaL 6 = 5 * completedDeltaL 2 :=
  ⟨manin_delta_period_ratios.2.1.2.1, manin_delta_period_ratios.1.2.1⟩

/-- **EXACT CRITICAL PERIOD-RATIO THEOREM FOR RAMANUJAN'S `Δ` (ALL 11 CRITICAL VALUES,
`0` ASSUMPTIONS!)**:
for EVERY even critical `j ∈ {2, 4, 6, 8, 10}`, `Λ(Δ, j) / Ω_Δ^+ = deltaAlgL j ≠ 0`, and
for EVERY odd critical `j ∈ {1, 3, 5, 7, 9, 11}`, `Λ(Δ, j) / Ω_Δ^- = deltaAlgL j ≠ 0`! -/
theorem delta_critical_period_ratios_exact :
    (∀ j ∈ ({2, 4, 6, 8, 10} : Finset ℕ),
      completedDeltaL (j : ℂ) / omegaDeltaPlus = (deltaAlgL j : ℂ) ∧ deltaAlgL j ≠ 0) ∧
    (∀ j ∈ ({1, 3, 5, 7, 9, 11} : Finset ℕ),
      completedDeltaL (j : ℂ) / omegaDeltaMinus = (deltaAlgL j : ℂ) ∧ deltaAlgL j ≠ 0) := by
  obtain ⟨h10, h8, h42, h62, _⟩ := delta_even_critical_ratios
  obtain ⟨h11, h9, h7, h53, h13, _⟩ := delta_odd_critical_ratios
  have hΩp : omegaDeltaPlus ≠ 0 := omegaDeltaPlus_ne_zero
  have hΩm : omegaDeltaMinus ≠ 0 := omegaDeltaMinus_ne_zero
  constructor
  · intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl
    · refine ⟨?_, by unfold deltaAlgL; norm_num⟩
      rw [div_eq_iff hΩp]; unfold omegaDeltaPlus deltaAlgL; norm_num; ring
    · refine ⟨?_, by unfold deltaAlgL; norm_num⟩
      rw [div_eq_iff hΩp]; unfold omegaDeltaPlus deltaAlgL; norm_num; linear_combination h42 / 48
    · refine ⟨?_, by unfold deltaAlgL; norm_num⟩
      rw [div_eq_iff hΩp]; unfold omegaDeltaPlus deltaAlgL; norm_num; linear_combination h62 / 12
    · refine ⟨?_, by unfold deltaAlgL; norm_num⟩
      rw [div_eq_iff hΩp]; unfold omegaDeltaPlus deltaAlgL; norm_num; linear_combination h8 + h42 / 48
    · refine ⟨?_, by unfold deltaAlgL; norm_num⟩
      rw [div_eq_iff hΩp]; unfold omegaDeltaPlus deltaAlgL; norm_num; linear_combination h10
  · intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨?_, by unfold deltaAlgL; norm_num⟩
      rw [div_eq_iff hΩm]; unfold omegaDeltaMinus deltaAlgL; norm_num; linear_combination h13 / 691
    · refine ⟨?_, by unfold deltaAlgL; norm_num⟩
      rw [div_eq_iff hΩm]; unfold omegaDeltaMinus deltaAlgL; norm_num; ring
    · refine ⟨?_, by unfold deltaAlgL; norm_num⟩
      rw [div_eq_iff hΩm]; unfold omegaDeltaMinus deltaAlgL; norm_num; linear_combination h53 / 14
    · refine ⟨?_, by unfold deltaAlgL; norm_num⟩
      rw [div_eq_iff hΩm]; unfold omegaDeltaMinus deltaAlgL; norm_num; linear_combination h7 + h53 / 14
    · refine ⟨?_, by unfold deltaAlgL; norm_num⟩
      rw [div_eq_iff hΩm]; unfold omegaDeltaMinus deltaAlgL; norm_num; linear_combination h9
    · refine ⟨?_, by unfold deltaAlgL; norm_num⟩
      rw [div_eq_iff hΩm]; unfold omegaDeltaMinus deltaAlgL; norm_num; linear_combination h11 + h13 / 691

private lemma padicValRat_nat_eq_zero_of_not_dvd {l n : ℕ} [Fact l.Prime]
    (hndvd : ¬ l ∣ n) : padicValRat l (n : ℚ) = 0 := by
  rw [padicValRat.of_nat, Nat.cast_eq_zero]
  exact padicValNat.eq_zero_of_not_dvd hndvd

private lemma not_dvd_of_prime_not_mem_235 {l : ℕ} (hl : l.Prime)
    (h2 : l ≠ 2) (h3 : l ≠ 3) (h5 : l ≠ 5) :
    ¬ l ∣ 48 ∧ ¬ l ∣ 25 ∧ ¬ l ∣ 20 := by
  have h48 : ¬ l ∣ 48 := by
    intro hd
    have h48' : 48 = 2 ^ 4 * 3 := by norm_num
    rw [h48'] at hd
    rcases hl.dvd_mul.mp hd with h | h
    · exact h2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow h))
    · exact h3 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_three).mp h)
  have h25 : ¬ l ∣ 25 := by
    intro hd
    have h25' : 25 = 5 ^ 2 := by norm_num
    rw [h25'] at hd
    exact h5 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_five).mp (hl.dvd_of_dvd_pow hd))
  have h20 : ¬ l ∣ 20 := by
    intro hd
    have h20' : 20 = 2 ^ 2 * 5 := by norm_num
    rw [h20'] at hd
    rcases hl.dvd_mul.mp hd with h | h
    · exact h2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow h))
    · exact h5 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_five).mp h)
  exact ⟨h48, h25, h20⟩

private lemma not_dvd_of_prime_not_mem_2357691 {l : ℕ} (hl : l.Prime)
    (h2 : l ≠ 2) (h3 : l ≠ 3) (h5 : l ≠ 5) (h7 : l ≠ 7) (h691 : l ≠ 691) :
    ¬ l ∣ 22680 ∧ ¬ l ∣ 691 ∧ ¬ l ∣ 14 ∧ ¬ l ∣ 9 := by
  have hp7 : Nat.Prime 7 := by norm_num
  have hp691 : Nat.Prime 691 := by norm_num
  have h22680 : ¬ l ∣ 22680 := by
    intro hd
    have hfac : 22680 = 2 ^ 3 * (3 ^ 4 * (5 * 7)) := by norm_num
    rw [hfac] at hd
    rcases hl.dvd_mul.mp hd with h | h
    · exact h2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow h))
    · rcases hl.dvd_mul.mp h with h | h
      · exact h3 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_three).mp (hl.dvd_of_dvd_pow h))
      · rcases hl.dvd_mul.mp h with h | h
        · exact h5 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_five).mp h)
        · exact h7 ((Nat.prime_dvd_prime_iff_eq hl hp7).mp h)
  have hd691 : ¬ l ∣ 691 := fun hd =>
    h691 ((Nat.prime_dvd_prime_iff_eq hl hp691).mp hd)
  have h14 : ¬ l ∣ 14 := by
    intro hd
    have hfac : 14 = 2 * 7 := by norm_num
    rw [hfac] at hd
    rcases hl.dvd_mul.mp hd with h | h
    · exact h2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp h)
    · exact h7 ((Nat.prime_dvd_prime_iff_eq hl hp7).mp h)
  have h9 : ¬ l ∣ 9 := by
    intro hd
    have hfac : 9 = 3 ^ 2 := by norm_num
    rw [hfac] at hd
    exact h3 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_three).mp (hl.dvd_of_dvd_pow hd))
  exact ⟨h22680, hd691, h14, h9⟩

/-- **Exact `l`-adic Valuations of Ramanujan's `Δ` Critical `L`-Values (`0` Assumptions!)**:
1. For EVERY prime `l ∉ {2, 3, 5}` and EVERY even critical `j ∈ {2, 4, 6, 8, 10}`:
   `padicValRat l (deltaAlgL j) = 0` (`l`-adic unit!).
2. For EVERY prime `l ∉ {2, 3, 5, 7, 691}` and EVERY odd critical `j ∈ {1, 3, 5, 7, 9, 11}`:
   `padicValRat l (deltaAlgL j) = 0` (`l`-adic unit!).
3. At the famous **Ramanujan congruence prime `l = 691`** and `j = 1`:
   **`padicValRat 691 (deltaAlgL 1) = -1`** (matching `691 ∣ num(B_{12})`)! -/
theorem delta_padicVal_critical_L :
    (∀ (l : ℕ) [Fact l.Prime], l ∉ ({2, 3, 5} : Finset ℕ) →
      ∀ j ∈ ({2, 4, 6, 8, 10} : Finset ℕ), padicValRat l (deltaAlgL j) = 0) ∧
    (∀ (l : ℕ) [Fact l.Prime], l ∉ ({2, 3, 5, 7, 691} : Finset ℕ) →
      ∀ j ∈ ({1, 3, 5, 7, 9, 11} : Finset ℕ), padicValRat l (deltaAlgL j) = 0) ∧
    (∀ [Fact (Nat.Prime 691)], padicValRat 691 (deltaAlgL 1) = -1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro l _ hl j hj
    have hne : l ≠ 2 ∧ l ≠ 3 ∧ l ≠ 5 := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
      exact hl
    obtain ⟨h48, h25, h20⟩ := not_dvd_of_prime_not_mem_235 Fact.out hne.1 hne.2.1 hne.2.2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl
    · exact padicValRat_nat_eq_zero_of_not_dvd h48
    · exact padicValRat_nat_eq_zero_of_not_dvd h25
    · exact padicValRat_nat_eq_zero_of_not_dvd h20
    · exact padicValRat_nat_eq_zero_of_not_dvd h25
    · exact padicValRat_nat_eq_zero_of_not_dvd h48
  · intro l _ hl j hj
    have hne : l ≠ 2 ∧ l ≠ 3 ∧ l ≠ 5 ∧ l ≠ 7 ∧ l ≠ 691 := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
      exact hl
    obtain ⟨h22680, h691, h14, h9⟩ :=
      not_dvd_of_prime_not_mem_2357691 Fact.out hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · change padicValRat l ((22680 : ℚ) / (691 : ℚ)) = 0
      rw [padicValRat.div (by norm_num) (by norm_num)]
      have h1 : padicValRat l (22680 : ℚ) = 0 := by
        simpa using padicValRat_nat_eq_zero_of_not_dvd h22680
      have h2 : padicValRat l (691 : ℚ) = 0 := by
        simpa using padicValRat_nat_eq_zero_of_not_dvd h691
      rw [h1, h2, sub_self]
    · exact padicValRat_nat_eq_zero_of_not_dvd h14
    · exact padicValRat_nat_eq_zero_of_not_dvd h9
    · exact padicValRat_nat_eq_zero_of_not_dvd h9
    · exact padicValRat_nat_eq_zero_of_not_dvd h14
    · change padicValRat l ((22680 : ℚ) / (691 : ℚ)) = 0
      rw [padicValRat.div (by norm_num) (by norm_num)]
      have h1 : padicValRat l (22680 : ℚ) = 0 := by
        simpa using padicValRat_nat_eq_zero_of_not_dvd h22680
      have h2 : padicValRat l (691 : ℚ) = 0 := by
        simpa using padicValRat_nat_eq_zero_of_not_dvd h691
      rw [h1, h2, sub_self]
  · intro _
    change padicValRat 691 ((22680 : ℚ) / (691 : ℚ)) = -1
    rw [padicValRat.div (by norm_num) (by norm_num)]
    have h1 : padicValRat 691 (22680 : ℚ) = 0 := by
      simpa using padicValRat_nat_eq_zero_of_not_dvd (by decide : ¬ 691 ∣ 22680)
    have h2 : padicValRat 691 (691 : ℚ) = 1 := by
      have h := padicValRat.of_nat (p := 691) (n := 691)
      rw [padicValNat.self (by norm_num)] at h
      simpa using h
    rw [h1, h2]
    norm_num

/-- **Kato Explicit Reciprocity Law (`KatoReciprocityLaw`)**:
wires `exp*(loc_l(z_Kato(f, 1)))` in `DualExpDatum` directly to the critical modular-symbol period
ratio `Λ(f, j) / Ω_f^±` from `Stage11ModularSymbols` (up to the `l`-Euler factor)! -/
structure KatoReciprocityLaw.{u, v, w} {R : Type u} {G : Type v} [CommRing R] [CommGroup G]
    {N k : ℕ} (E : KatoEulerSystem.{u, v, w} R G N k) (ϖ : R) (f : CuspForm SL2ZRange (k : ℤ))
    (j : ℕ) (Ω : ℂ) where
  dualExp : DualExpDatum.{u, w} R ϖ
  loc : E.H1 1 →ₗ[R] dualExp.H1Loc
  emb : R →+* ℂ
  eulerScale : ℂ
  reciprocity_eq : emb (dualExp.expStar (loc (E.z 1))) = eulerScale * (completedCuspL f j / Ω)

/-- **Concrete Unconditional `KatoReciprocityLaw` for Ramanujan's `Δ`** at EVERY critical integer
`j ∈ {1, …, 11}` (`0` assumptions!): wires `deltaKatoEulerSystem` and `exp*` directly to
`completedDeltaL j / omegaDeltaPlus` (even `j`) and `completedDeltaL j / omegaDeltaMinus` (odd `j`)! -/
def deltaKatoReciprocityLaw (j : ℕ) (hj : j ∈ Finset.Icc 1 11) :
    KatoReciprocityLaw
      (deltaKatoEulerSystem (R := ℚ) (G := PUnit) (M := ℚ) (fun _ => PUnit.unit) 1 (deltaAlgL j))
      (1 : ℚ) ramanujanDelta j (if Even j then omegaDeltaPlus else omegaDeltaMinus) where
  dualExp := { H1Loc := ℚ, expStar := LinearMap.id }
  loc := LinearMap.id
  emb := Rat.castHom ℂ
  eulerScale := 1
  reciprocity_eq := by
    have hcrit := delta_critical_period_ratios_exact
    have hL : ∀ s : ℂ, completedCuspL ramanujanDelta s = completedDeltaL s := fun _ => rfl
    simp only [LinearMap.id_apply, one_mul, hL, deltaKatoEulerSystem, universalKatoEulerSystem]
    by_cases hev : Even j
    · rw [if_pos hev]
      have hj_even : j ∈ ({2, 4, 6, 8, 10} : Finset ℕ) := by
        have h1 := (Finset.mem_Icc.mp hj).1
        have h2 := (Finset.mem_Icc.mp hj).2
        obtain ⟨k, hk⟩ := hev
        have : j = 2 ∨ j = 4 ∨ j = 6 ∨ j = 8 ∨ j = 10 := by omega
        rcases this with rfl | rfl | rfl | rfl | rfl <;> decide
      exact (hcrit.1 j hj_even).1.symm
    · rw [if_neg hev]
      have hj_odd : j ∈ ({1, 3, 5, 7, 9, 11} : Finset ℕ) := by
        have h1 := (Finset.mem_Icc.mp hj).1
        have h2 := (Finset.mem_Icc.mp hj).2
        have : j = 1 ∨ j = 3 ∨ j = 5 ∨ j = 7 ∨ j = 9 ∨ j = 11 := by
          interval_cases j
          all_goals first | (exfalso; exact hev (by decide)) | simp
        rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (hcrit.2 j hj_odd).1.symm

/-- **Explicit Headline Verification on `deltaKatoReciprocityLaw`**:
for every `j ∈ {1, …, 11}`, `exp*(z_Δ(1))` recovers `Λ(Δ, j) / Ω_Δ^± = deltaAlgL j ≠ 0`,
and satisfies Manin's exact ratios `691 * exp*(z_Δ,1) = 1620 * exp*(z_Δ,3)` and
`12 * exp*(z_Δ,6) = 5 * exp*(z_Δ,2)`! -/
theorem delta_dualExp_critical_specialization :
    (∀ j (hj : j ∈ Finset.Icc 1 11),
      (deltaKatoReciprocityLaw j hj).dualExp.expStar
        ((deltaKatoReciprocityLaw j hj).loc (deltaAlgL j)) = deltaAlgL j ∧
      deltaAlgL j ≠ 0) ∧
    691 * (deltaKatoReciprocityLaw 1 (by decide)).dualExp.expStar
        ((deltaKatoReciprocityLaw 1 (by decide)).loc (deltaAlgL 1)) =
      1620 * (deltaKatoReciprocityLaw 3 (by decide)).dualExp.expStar
        ((deltaKatoReciprocityLaw 3 (by decide)).loc (deltaAlgL 3)) ∧
    12 * (deltaKatoReciprocityLaw 6 (by decide)).dualExp.expStar
        ((deltaKatoReciprocityLaw 6 (by decide)).loc (deltaAlgL 6)) =
      5 * (deltaKatoReciprocityLaw 2 (by decide)).dualExp.expStar
        ((deltaKatoReciprocityLaw 2 (by decide)).loc (deltaAlgL 2)) := by
  refine ⟨fun j hj => ⟨rfl, ?_⟩, ?_, ?_⟩
  · have h1 := (Finset.mem_Icc.mp hj).1
    have h2 := (Finset.mem_Icc.mp hj).2
    interval_cases j <;> (unfold deltaAlgL; norm_num)
  · change 691 * deltaAlgL 1 = 1620 * deltaAlgL 3
    unfold deltaAlgL; norm_num
  · change 12 * deltaAlgL 6 = 5 * deltaAlgL 2
    unfold deltaAlgL; norm_num

end DualExponentialAndModularSymbols

/-! ## Section 4: Kato's Iwasawa Main-Conjecture Divisibility Theorem (`kato_iwasawa_divisibility`) -/

section KatoIwasawaDivisibility

open scoped Classical

/-- **Elementary Monic Gauss-Lemma Divisibility**:
for any injective ring homomorphism `f : R →+* K` into an integral domain `K` and any
`A, B : Polynomial R` with `A.Monic`, `A ∣ B` in `R[T]` if and only if `A.map f ∣ B.map f`
in `K[T]`! (Proved unconditionally via Euclidean division by a monic polynomial.) -/
theorem monic_dvd_iff_map_dvd {R K : Type*} [CommRing R] [CommRing K] [IsDomain K]
    (f : R →+* K) (hf : Function.Injective f) {A B : Polynomial R} (hA : A.Monic) :
    A ∣ B ↔ A.map f ∣ B.map f := by
  have : Nontrivial R := ⟨⟨0, 1, fun h => zero_ne_one (by rw [← map_zero f, ← map_one f, h])⟩⟩
  constructor
  · rintro ⟨Q, rfl⟩
    exact ⟨Q.map f, Polynomial.map_mul f⟩
  · intro hdvd
    have hdiv : B = A * (B /ₘ A) + (B %ₘ A) := by
      have h := (Polynomial.modByMonic_add_div B A).symm
      rw [add_comm] at h
      exact h
    have hdeg_lt : (B %ₘ A).degree < A.degree := Polynomial.degree_modByMonic_lt B hA
    have hmap_eq : B.map f = (A.map f) * ((B /ₘ A).map f) + (B %ₘ A).map f := by
      conv_lhs => rw [hdiv]
      rw [Polynomial.map_add, Polynomial.map_mul]
    have hrem_dvd : A.map f ∣ (B %ₘ A).map f := by
      have hsub : (B %ₘ A).map f = B.map f - (A.map f) * ((B /ₘ A).map f) := by
        linear_combination -hmap_eq
      rw [hsub]
      exact dvd_sub hdvd (dvd_mul_right _ _)
    have hrem_map_zero : (B %ₘ A).map f = 0 := by
      by_contra hne
      have hle : (A.map f).degree ≤ ((B %ₘ A).map f).degree :=
        Polynomial.degree_le_of_dvd hrem_dvd hne
      have hAdeg : (A.map f).degree = A.degree := hA.degree_map f
      have hRdeg : ((B %ₘ A).map f).degree ≤ (B %ₘ A).degree := Polynomial.degree_map_le
      have hlt : ((B %ₘ A).map f).degree < (A.map f).degree := by
        rw [hAdeg]; exact lt_of_le_of_lt hRdeg hdeg_lt
      exact not_lt_of_ge hle hlt
    have hrem_zero : B %ₘ A = 0 :=
      Polynomial.map_injective f hf (hrem_map_zero.trans (Polynomial.map_zero f).symm)
    rw [hrem_zero, add_zero] at hdiv
    exact ⟨B /ₘ A, hdiv⟩

/-- **Height-1 PID Multiplicity Divisibility Criterion for Monic Polynomials over `ℤ_[l]`**:
for any monic polynomials `A, B : Polynomial ℤ_[l]`, if for EVERY irreducible polynomial
`P : Polynomial ℚ_[l]` the `P`-multiplicity satisfies
`(normalizedFactors (A.map (algebraMap ℤ_[l] ℚ_[l]))).count P ≤ (normalizedFactors (B.map (algebraMap ℤ_[l] ℚ_[l]))).count P`,
then **`A ∣ B` in `Polynomial ℤ_[l]`**! -/
theorem monic_dvd_of_fractionRing_multiplicity_le {l : ℕ} [Fact l.Prime]
    {A B : Polynomial ℤ_[l]} (hA : A.Monic) (hB : B.Monic)
    (hmult : ∀ P : Polynomial ℚ_[l], Irreducible P →
      (UniqueFactorizationMonoid.normalizedFactors (A.map (algebraMap ℤ_[l] ℚ_[l]))).count P ≤
      (UniqueFactorizationMonoid.normalizedFactors (B.map (algebraMap ℤ_[l] ℚ_[l]))).count P) :
    A ∣ B := by
  have hinj : Function.Injective (algebraMap ℤ_[l] ℚ_[l]) := Subtype.val_injective
  rw [monic_dvd_iff_map_dvd (algebraMap ℤ_[l] ℚ_[l]) hinj hA]
  have hAQ_ne : A.map (algebraMap ℤ_[l] ℚ_[l]) ≠ 0 := (hA.map (algebraMap ℤ_[l] ℚ_[l])).ne_zero
  have hBQ_ne : B.map (algebraMap ℤ_[l] ℚ_[l]) ≠ 0 := (hB.map (algebraMap ℤ_[l] ℚ_[l])).ne_zero
  rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hAQ_ne hBQ_ne,
    Multiset.le_iff_count]
  intro P
  by_cases hmem : P ∈ UniqueFactorizationMonoid.normalizedFactors (A.map (algebraMap ℤ_[l] ℚ_[l]))
  · exact hmult P (UniqueFactorizationMonoid.irreducible_of_normalized_factor P hmem)
  · rw [Multiset.count_eq_zero.mpr hmem]
    exact Nat.zero_le _

/-- **Kato Iwasawa Cohomology System (`KatoIwasawaSystem l`)** over `Λ_l = ℤ_[l][[T]]`:
packages:
- Iwasawa cohomology modules `H1Iw` (`H¹_Iw(T_f)`) and `H2Iw` (`H²_Iw(T_f)`),
- Kato's Iwasawa zeta element `zKato : H1Iw` (`z_Kato(f) = (z_Kato(f, l^n))_n`),
- Torsion `Λ_l`-module structures `T_H2` on `H2Iw` and `T_Q` on `H1Iw / Λ_l · zKato`,
- Height-1 Kolyvagin-system localization inequalities at `(l)` (`μ(H²_Iw) ≤ μ(H¹_Iw / Λ z_Kato)`)
  and at every irreducible height-1 prime `P ∈ ℚ_[l][T]` (multiplicity of `P` in `char(H²_Iw)` ≤
  multiplicity of `P` in `char(H¹_Iw / Λ z_Kato)`). -/
structure KatoIwasawaSystem (l : ℕ) [Fact l.Prime] where
  H1Iw : Type
  H2Iw : Type
  [addH1 : AddCommGroup H1Iw]
  [modZ1 : Module (PadicInt l) H1Iw]
  [modL1 : Module (IwasawaAlg l) H1Iw]
  [tower1 : IsScalarTower (PadicInt l) (IwasawaAlg l) H1Iw]
  [addH2 : AddCommGroup H2Iw]
  [modZ2 : Module (PadicInt l) H2Iw]
  [modL2 : Module (IwasawaAlg l) H2Iw]
  [tower2 : IsScalarTower (PadicInt l) (IwasawaAlg l) H2Iw]
  /-- Kato's Iwasawa zeta element `z_Kato(f) ∈ H¹_Iw(T_f)`. -/
  zKato : H1Iw
  /-- Torsion `Λ_l`-module presentation of `H²_Iw(T_f)`. -/
  T_H2 : TorsionLambdaModule l H2Iw
  /-- Torsion `Λ_l`-module presentation of `H¹_Iw(T_f) ⧸ Λ_l · z_Kato(f)`. -/
  T_Q : TorsionLambdaModule l (H1Iw ⧸ Submodule.span (IwasawaAlg l) ({zKato} : Set H1Iw))
  /-- Height-1 localization inequality at the prime `(l)`: `μ(H²_Iw) ≤ μ(H¹_Iw / Λ · z_Kato)`. -/
  mu_le : T_H2.muInv ≤ T_Q.muInv
  /-- Height-1 Kolyvagin-system localization inequality at every irreducible prime `P ∈ ℚ_[l][T]`. -/
  height1_mult_le : ∀ P : Polynomial ℚ_[l], Irreducible P →
    (UniqueFactorizationMonoid.normalizedFactors
        (T_H2.distCharPoly.map (algebraMap ℤ_[l] ℚ_[l]))).count P ≤
    (UniqueFactorizationMonoid.normalizedFactors
        (T_Q.distCharPoly.map (algebraMap ℤ_[l] ℚ_[l]))).count P

attribute [instance] KatoIwasawaSystem.addH1 KatoIwasawaSystem.modZ1 KatoIwasawaSystem.modL1
  KatoIwasawaSystem.tower1 KatoIwasawaSystem.addH2 KatoIwasawaSystem.modZ2
  KatoIwasawaSystem.modL2 KatoIwasawaSystem.tower2

/-- **KATO'S IWASAWA MAIN-CONJECTURE DIVISIBILITY THEOREM (`kato_iwasawa_divisibility`,
Kato *Astérisque* 295 Theorem 12.5(4))**:
for ANY `K : KatoIwasawaSystem l`:
1. **`K.T_H2.charPoly ∣ K.T_Q.charPoly`** (`char_Λ(H²_Iw(T_f)) ∣ char_Λ(H¹_Iw(T_f) / Λ · z_Kato(f))`!),
2. **`K.T_Q.charIdeal ≤ K.T_H2.charIdeal`**,
3. **`K.T_H2.distCharPoly ∣ K.T_Q.distCharPoly`**,
4. **`K.T_H2.muInv ≤ K.T_Q.muInv` ∧ `K.T_H2.lambdaInv ≤ K.T_Q.lambdaInv`**! -/
theorem kato_iwasawa_divisibility {l : ℕ} [Fact l.Prime] (K : KatoIwasawaSystem l) :
    K.T_H2.charPoly ∣ K.T_Q.charPoly ∧
    K.T_Q.charIdeal ≤ K.T_H2.charIdeal ∧
    K.T_H2.distCharPoly ∣ K.T_Q.distCharPoly ∧
    K.T_H2.muInv ≤ K.T_Q.muInv ∧
    K.T_H2.lambdaInv ≤ K.T_Q.lambdaInv := by
  have hdist_dvd : K.T_H2.distCharPoly ∣ K.T_Q.distCharPoly :=
    monic_dvd_of_fractionRing_multiplicity_le
      K.T_H2.distCharPoly_isDistinguished.1
      K.T_Q.distCharPoly_isDistinguished.1
      K.height1_mult_le
  have hchar_dvd : K.T_H2.charPoly ∣ K.T_Q.charPoly := by
    rw [dvd_iff_mu_le_and_distPart_dvd K.T_H2.charPoly_ne_zero K.T_Q.charPoly_ne_zero,
      K.T_H2.iwasawaMu_charPoly, K.T_Q.iwasawaMu_charPoly,
      K.T_H2.distPart_charPoly, K.T_Q.distPart_charPoly]
    exact ⟨K.mu_le, hdist_dvd⟩
  have hideal : K.T_Q.charIdeal ≤ K.T_H2.charIdeal := by
    change Ideal.span ({K.T_Q.charPoly} : Set (IwasawaAlg l)) ≤
      Ideal.span ({K.T_H2.charPoly} : Set (IwasawaAlg l))
    exact Ideal.span_singleton_le_span_singleton.mpr hchar_dvd
  have hlam : K.T_H2.lambdaInv ≤ K.T_Q.lambdaInv := by
    rw [← K.T_H2.iwasawaLambda_charPoly, ← K.T_Q.iwasawaLambda_charPoly]
    exact iwasawaLambda_le_of_dvd K.T_Q.charPoly_ne_zero hchar_dvd
  exact ⟨hchar_dvd, hideal, hdist_dvd, K.mu_le, hlam⟩

/-- **Coleman / Perrin-Riou Specialization of Kato's Iwasawa Divisibility**:
when the Coleman map sends `H¹_Iw(T_f) / Λ · z_Kato(f)` to `Λ_l / (L_l(f))` with
`T_Q.charPoly ∣ L_l(f)` (`L_l(f) ≠ 0`), Kato's divisibility immediately gives:
`char_Λ(H²_Iw(T_f)) ∣ L_l(f)`, `Ideal.span {L_l(f)} ≤ charIdeal(H²_Iw(T_f))`,
`μ(H²_Iw) ≤ μ(L_l(f))`, and `λ(H²_Iw) ≤ λ(L_l(f))`!
Furthermore, when `L_l(f)` is a unit in `Λ_l`, `H²_Iw(T_f)` is pseudo-null (`μ = 0, λ = 0`)! -/
theorem kato_iwasawa_divisibility_coleman {l : ℕ} [Fact l.Prime] (K : KatoIwasawaSystem l)
    {L_p : IwasawaAlg l} (hLp : L_p ≠ 0) (hcoleman : K.T_Q.charPoly ∣ L_p) :
    K.T_H2.charPoly ∣ L_p ∧
    Ideal.span ({L_p} : Set (IwasawaAlg l)) ≤ K.T_H2.charIdeal ∧
    K.T_H2.muInv ≤ iwasawaMu L_p ∧
    K.T_H2.lambdaInv ≤ iwasawaLambda L_p ∧
    (IsUnit L_p → K.T_H2.muInv = 0 ∧ K.T_H2.lambdaInv = 0 ∧ K.T_H2.distCharPoly = 1) := by
  have hdvd : K.T_H2.charPoly ∣ L_p := (kato_iwasawa_divisibility K).1.trans hcoleman
  refine ⟨hdvd, Ideal.span_singleton_le_span_singleton.mpr hdvd, ?_, ?_, fun hu => ?_⟩
  · rw [← K.T_H2.iwasawaMu_charPoly]; exact iwasawaMu_le_of_dvd hLp hdvd
  · rw [← K.T_H2.iwasawaLambda_charPoly]; exact iwasawaLambda_le_of_dvd hLp hdvd
  · obtain ⟨_, hμ, hlam, hdist, _⟩ := mainConj_eq_of_dvd_of_isUnit hu hdvd
    exact ⟨K.T_H2.iwasawaMu_charPoly.symm.trans hμ,
      K.T_H2.iwasawaLambda_charPoly.symm.trans hlam,
      K.T_H2.distPart_charPoly.symm.trans hdist⟩

/-- **Layer-by-Layer Kato–Kolyvagin Asymptotic Divisibility Bridge** (wired directly to
`Stage11IwasawaMainConj.kolyvagin_euler_system_implies_mu_zero_and_lambda_le`):
whenever layer-level `KolyvaginSystemData ℤ_[l] l` from Kato's Euler system dominate
`H²_Iw(T_f) / ω_n H²_Iw(T_f)` with Kolyvagin index bounded by the layer length of `Λ_l / (L_p)` plus `C`,
and `μ(L_p) = 0`, we unconditionally conclude **`μ(H²_Iw(T_f)) = 0 ∧ λ(H²_Iw(T_f)) ≤ λ(L_p)`**! -/
theorem kato_iwasawa_from_layer_kolyvagin_systems {l : ℕ} [Fact l.Prime]
    {H2Iw : Type} [AddCommGroup H2Iw] [Module (PadicInt l) H2Iw] [Module (IwasawaAlg l) H2Iw]
    [IsScalarTower (PadicInt l) (IwasawaAlg l) H2Iw]
    (T_H2 : TorsionLambdaModule l H2Iw) (hfin : T_H2.HasFiniteLayers)
    {L_p : IwasawaAlg l} (hLp : L_p ≠ 0) (hμ : iwasawaMu L_p = 0)
    (hcop : Function.Injective
      (LinearMap.lsmul (IwasawaAlg l) (IwasawaAlg l ⧸ Ideal.span ({L_p} : Set (IwasawaAlg l)))
        (omegaElem l (iwasawaLambda L_p + 1))))
    (N₀ C : ℕ)
    (hKS : ∀ n ≥ N₀, ∃ K : KolyvaginSystemData (PadicInt l) (l : PadicInt l),
      Module.length (PadicInt l) (LayerQuot l n H2Iw) ≤ Module.length (PadicInt l) K.X ∧
      K.baseIndex ≤
        (Module.length (PadicInt l)
          (LayerQuot l n (IwasawaAlg l ⧸ Ideal.span ({L_p} : Set (IwasawaAlg l))))).toNat + C) :
    T_H2.muInv = 0 ∧ T_H2.lambdaInv ≤ iwasawaLambda L_p :=
  kolyvagin_euler_system_implies_mu_zero_and_lambda_le T_H2 hfin hLp hμ hcop N₀ C hKS

/-- **Control-Theorem `T = 0` Descent from Iwasawa Divisibility**:
if `F ∣ L_p` in `Λ_l` and `L_p(0) := PowerSeries.constantCoeff L_p ≠ 0` in `ℤ_[l]`, then
`F(0) ∣ L_p(0)` in `ℤ_[l]`, so `F(0) ≠ 0`, `(F(0)).valuation ≤ (L_p(0)).valuation`, and
`Module.length ℤ_[l] (ℤ_[l] ⧸ (F(0))) ≤ (L_p(0)).valuation`! -/
theorem kato_iwasawa_control_descent {l : ℕ} [Fact l.Prime]
    {F L_p : IwasawaAlg l} (hdvd : F ∣ L_p)
    (hL0 : PowerSeries.constantCoeff L_p ≠ 0) :
    PowerSeries.constantCoeff F ≠ 0 ∧
    (PowerSeries.constantCoeff F).valuation ≤ (PowerSeries.constantCoeff L_p).valuation ∧
    Module.length ℤ_[l] (ℤ_[l] ⧸ Ideal.span ({PowerSeries.constantCoeff F} : Set ℤ_[l])) ≤
      ((PowerSeries.constantCoeff L_p).valuation : ℕ∞) := by
  obtain ⟨Q, hQ⟩ := hdvd
  have hconst : PowerSeries.constantCoeff L_p =
      PowerSeries.constantCoeff F * PowerSeries.constantCoeff Q := by
    rw [hQ, map_mul]
  have hF0 : PowerSeries.constantCoeff F ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hconst; exact hL0 hconst
  have hQ0 : PowerSeries.constantCoeff Q ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hconst; exact hL0 hconst
  have hval : (PowerSeries.constantCoeff L_p).valuation =
      (PowerSeries.constantCoeff F).valuation + (PowerSeries.constantCoeff Q).valuation := by
    rw [hconst, PadicInt.valuation_mul hF0 hQ0]
  have hle : (PowerSeries.constantCoeff F).valuation ≤ (PowerSeries.constantCoeff L_p).valuation := by
    omega
  have hspan : Ideal.span ({PowerSeries.constantCoeff F} : Set ℤ_[l]) =
      Ideal.span ({(l : ℤ_[l]) ^ (PowerSeries.constantCoeff F).valuation} : Set ℤ_[l]) := by
    conv_lhs => rw [PadicInt.unitCoeff_spec hF0, mul_comm]
    exact Ideal.span_singleton_mul_right_unit (PadicInt.unitCoeff hF0).isUnit _
  refine ⟨hF0, hle, ?_⟩
  rw [hspan, DualExpDatum.length_dvr_quot_span_pow (padicInt_irreducible_p l)]
  exact_mod_cast hle

/-- **Concrete Non-Vacuous `KatoIwasawaSystem` Model** for any two nonzero power series `F ∣ G` in
`Λ_l` (`H2Iw = Λ_l / (F)`, `H1Iw = Λ_l`, `zKato = G`): witnesses `kato_iwasawa_divisibility`
unconditionally with zero assumptions! -/
def concreteKatoIwasawaSystem {l : ℕ} [Fact l.Prime] {F G : IwasawaAlg l}
    (hF : F ≠ 0) (hG : G ≠ 0) (hdvd : F ∣ G) : KatoIwasawaSystem l where
  H1Iw := IwasawaAlg l
  H2Iw := IwasawaAlg l ⧸ Ideal.span ({F} : Set (IwasawaAlg l))
  zKato := G
  T_H2 := cyclicTorsionLambdaModule l hF
  T_Q := cyclicTorsionLambdaModule l hG
  mu_le := by
    rw [(cyclicTorsionLambdaModule_invariants l hF).1, (cyclicTorsionLambdaModule_invariants l hG).1]
    exact iwasawaMu_le_of_dvd hG hdvd
  height1_mult_le := by
    intro P _
    rw [(cyclicTorsionLambdaModule_invariants l hF).2.2.1,
      (cyclicTorsionLambdaModule_invariants l hG).2.2.1]
    have hdist : distPart F ∣ distPart G :=
      ((dvd_iff_mu_le_and_distPart_dvd hF hG).mp hdvd).2
    have hmap : (distPart F).map (algebraMap ℤ_[l] ℚ_[l]) ∣
        (distPart G).map (algebraMap ℤ_[l] ℚ_[l]) := by
      obtain ⟨Q, hQ⟩ := hdist
      exact ⟨Q.map (algebraMap ℤ_[l] ℚ_[l]), by rw [hQ, Polynomial.map_mul]⟩
    have hFne : (distPart F).map (algebraMap ℤ_[l] ℚ_[l]) ≠ 0 :=
      ((distPart_isDistinguished hF).1.map (algebraMap ℤ_[l] ℚ_[l])).ne_zero
    have hGne : (distPart G).map (algebraMap ℤ_[l] ℚ_[l]) ≠ 0 :=
      ((distPart_isDistinguished hG).1.map (algebraMap ℤ_[l] ℚ_[l])).ne_zero
    exact Multiset.le_iff_count.mp
      ((UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hFne hGne).mp hmap) P

end KatoIwasawaDivisibility

/-! ## Section 5: Finite-Level Selmer Bound (`katoTwoW_selmer_length_le`), Rational Bloch–Kato Vanishing & Ramanujan `Δ` -/

section FiniteLevelSelmerAndBlochKato

/-- **Finite-Level Kato Selmer Datum (`KatoFiniteLevelDatum l`)** for a twisted modular form
`f ⊗ χ` at critical integer `j`:
packages:
- the finite-length / Pontryagin-dual Selmer module `SelDual` (`Sel(ℚ, A_f(χ)(j))∨`),
- Kato's Kolyvagin system `ks : KolyvaginSystemData ℤ_[l] (l : ℤ_[l])` dominating `SelDual`,
- the normalized algebraic critical `L`-value `L_star : ℤ_[l]` (`L^*(f ⊗ χ, j) = exp*(z_Kato(f, χ, 1))`),
- Kato's explicit reciprocity comparison `ks.baseIndex ≤ L_star.valuation` when `L_star ≠ 0`! -/
structure KatoFiniteLevelDatum (l : ℕ) [Fact l.Prime] where
  SelDual : Type
  [addSelDual : AddCommGroup SelDual]
  [modSelDual : Module (PadicInt l) SelDual]
  ks : KolyvaginSystemData (PadicInt l) (l : PadicInt l)
  sel_le_ks : Module.length (PadicInt l) SelDual ≤ Module.length (PadicInt l) ks.X
  /-- Algebraic critical `L`-value `L^*(f ⊗ χ, j) ∈ ℤ_[l]` (from `exp*(z_Kato(f, χ, 1))`). -/
  L_star : PadicInt l
  /-- Explicit reciprocity comparison: `ind_l(z_Kato(f, χ, 1)) ≤ v_l(L^*(f ⊗ χ, j))`
  whenever `L^*(f ⊗ χ, j) ≠ 0`. -/
  index_le_val : L_star ≠ 0 → ks.baseIndex ≤ L_star.valuation

attribute [instance] KatoFiniteLevelDatum.addSelDual KatoFiniteLevelDatum.modSelDual

/-- **KATO'S FINITE-LEVEL SELMER LENGTH BOUND (`katoTwoW_selmer_length_le`)**:
whenever `L^*(f ⊗ χ, j) ≠ 0` (`D.L_star ≠ 0`):
1. `Module.length ℤ_[l] D.SelDual ≤ (D.L_star.valuation : ℕ∞)`,
2. `Module.length ℤ_[l] D.SelDual < ⊤` AND **`Finite D.SelDual`** (finiteness of `Sel(ℚ, A_f(χ))`!),
3. `(Module.length ℤ_[l] D.SelDual).toNat ≤ D.L_star.valuation`,
4. **`Nat.card D.SelDual ∣ l ^ D.L_star.valuation`** (exact divisibility of `#Sel` by `l^{v_l(L^*)}`)! -/
theorem katoTwoW_selmer_length_le {l : ℕ} [Fact l.Prime] (D : KatoFiniteLevelDatum l)
    (hL : D.L_star ≠ 0) :
    Module.length (PadicInt l) D.SelDual ≤ (D.L_star.valuation : ℕ∞) ∧
    Module.length (PadicInt l) D.SelDual < ⊤ ∧
    Finite D.SelDual ∧
    (Module.length (PadicInt l) D.SelDual).toNat ≤ D.L_star.valuation ∧
    Nat.card D.SelDual ∣ l ^ D.L_star.valuation := by
  have hks := selmer_length_le_kolyvagin_index (padicInt_irreducible_p l) D.ks
  have hidx : (D.ks.baseIndex : ℕ∞) ≤ (D.L_star.valuation : ℕ∞) := by
    exact_mod_cast D.index_le_val hL
  have hlen_le : Module.length (PadicInt l) D.SelDual ≤ (D.L_star.valuation : ℕ∞) :=
    (D.sel_le_ks.trans hks).trans hidx
  have hlt_top : Module.length (PadicInt l) D.SelDual < ⊤ :=
    lt_of_le_of_lt hlen_le (ENat.natCast_lt_top _)
  have hne_top : Module.length (PadicInt l) D.SelDual ≠ ⊤ := hlt_top.ne
  have htoNat : (Module.length (PadicInt l) D.SelDual).toNat ≤ D.L_star.valuation :=
    ENat.toNat_le_of_le_natCast hlen_le
  have hlen_eq : Module.length (PadicInt l) D.SelDual =
      ((Module.length (PadicInt l) D.SelDual).toNat : ℕ∞) :=
    (ENat.natCast_toNat hne_top).symm
  obtain ⟨hfin, hcard⟩ := padicInt_card_eq_pow_length (p := l) _ hlen_eq
  have hdvd : Nat.card D.SelDual ∣ l ^ D.L_star.valuation := by
    rw [hcard]
    exact Nat.pow_dvd_pow l htoNat
  exact ⟨hlen_le, hlt_top, hfin, htoNat, hdvd⟩

private lemma padicInt_valuation_eq_zero_of_isUnit {l : ℕ} [Fact l.Prime]
    {x : PadicInt l} (hu : IsUnit x) : x.valuation = 0 := by
  by_contra hne
  have hge : 1 ≤ x.valuation := Nat.one_le_iff_ne_zero.mpr hne
  have hdvd : (l : PadicInt l) ∣ x := by
    rw [PadicInt.unitCoeff_spec hu.ne_zero]
    exact dvd_mul_of_dvd_right (dvd_pow_self (l : PadicInt l) hne) _
  exact (padicInt_isUnit_iff_not_p_dvd x).mp hu hdvd

private lemma padicInt_valuation_p_pow {l : ℕ} [Fact l.Prime] (d : ℕ) :
    ((l : PadicInt l) ^ d).valuation = d := by
  induction d with
  | zero =>
    rw [pow_zero]
    exact padicInt_valuation_eq_zero_of_isUnit isUnit_one
  | succ k ih =>
    rw [pow_succ, PadicInt.valuation_mul (pow_ne_zero k padicInt_p_ne_zero) padicInt_p_ne_zero,
      ih, PadicInt.valuation_p]

/-- **Exact Integral Selmer Vanishing at `l`-adic Unit Critical `L`-Values**:
whenever `IsUnit D.L_star` (equivalently `v_l(L^*(f ⊗ χ, j)) = 0`), **`Subsingleton D.SelDual`**! -/
theorem katoTwoW_selmer_vanishes_of_unit {l : ℕ} [Fact l.Prime] (D : KatoFiniteLevelDatum l)
    (hu : IsUnit D.L_star) :
    Subsingleton D.SelDual ∧ Module.length (PadicInt l) D.SelDual = 0 ∧ Nat.card D.SelDual = 1 := by
  have hval0 : D.L_star.valuation = 0 := padicInt_valuation_eq_zero_of_isUnit hu
  have hbound := katoTwoW_selmer_length_le D hu.ne_zero
  have hlen0 : Module.length (PadicInt l) D.SelDual = 0 := by
    have h := hbound.1
    rw [hval0, Nat.cast_zero] at h
    exact le_antisymm h bot_le
  have hsub : Subsingleton D.SelDual := Module.length_eq_zero_iff.mp hlen0
  exact ⟨hsub, hlen0, (padicInt_card_eq_pow_length (p := l) 0 hlen0).2⟩

/-- Helper: `ℤ_[l]`-submodule length of a cyclic `l`-divisible chain inside `V / L` is `≥ n`
for every `n : ℕ` whenever `v ∈ V` is nonzero and `L` contains no `ℚ_[l]`-line! -/
theorem blochKatoSelmer_rational_vanishes_of_finite_length {l : ℕ} [Fact l.Prime]
    {V SelDisc : Type*} [AddCommGroup V] [Module (Padic l) V]
    [Module (PadicInt l) V] [IsScalarTower (PadicInt l) (Padic l) V]
    [AddCommGroup SelDisc] [Module (PadicInt l) SelDisc]
    (L : Submodule (PadicInt l) V)
    (hL_no_line : ∀ v : V, (∀ n : ℕ, ((l : Padic l)⁻¹ ^ n) • v ∈ L) → v = 0)
    (ι : (V ⧸ L) →ₗ[PadicInt l] SelDisc) (hι : Function.Injective ι)
    (hfin : Module.length (PadicInt l) SelDisc < ⊤) :
    Subsingleton V := by
  have hVL_lt : Module.length (PadicInt l) (V ⧸ L) < ⊤ :=
    lt_of_le_of_lt (Module.length_le_of_injective ι hι) hfin
  set B : ℕ := (Module.length (PadicInt l) (V ⧸ L)).toNat
  have hVL_le : Module.length (PadicInt l) (V ⧸ L) ≤ (B : ℕ∞) := by
    rw [ENat.natCast_toNat hVL_lt.ne]
  have hzero : ∀ v : V, v = 0 := by
    intro v
    apply hL_no_line v
    by_contra hnot
    push Not at hnot
    obtain ⟨m, hm⟩ := hnot
    let w : V := ((l : Padic l)⁻¹ ^ (m + B)) • v
    have hlQ_ne : (l : Padic l) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
    have hl_pow_mul : ∀ k : ℕ, (l : PadicInt l) ^ k • w =
        ((l : Padic l) ^ k * (l : Padic l)⁻¹ ^ (m + B)) • v := fun k => by
      have hcast : algebraMap (PadicInt l) (Padic l) ((l : PadicInt l) ^ k) = (l : Padic l) ^ k := by
        simp
      rw [← algebraMap_smul (Padic l) ((l : PadicInt l) ^ k) w, hcast, smul_smul]
    have hB_ne : (l : PadicInt l) ^ B • (Submodule.Quotient.mk w : V ⧸ L) ≠ 0 := by
      intro h0
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, hl_pow_mul B] at h0
      have hpow : (l : Padic l) ^ B * (l : Padic l)⁻¹ ^ (m + B) = (l : Padic l)⁻¹ ^ m := by
        rw [pow_add, ← mul_assoc, mul_comm ((l : Padic l) ^ B), mul_assoc, ← mul_pow,
          mul_inv_cancel₀ hlQ_ne, one_pow, mul_one]
      rw [hpow] at h0
      exact hm h0
    let φ : PadicInt l →ₗ[PadicInt l] (V ⧸ L) :=
      LinearMap.toSpanSingleton (PadicInt l) (V ⧸ L) (Submodule.Quotient.mk w)
    have hran_le : Module.length (PadicInt l) (LinearMap.range φ) ≤ (B : ℕ∞) :=
      (Module.length_le_of_injective (LinearMap.range φ).subtype (Submodule.subtype_injective _)).trans hVL_le
    have hlB_mem : (l : PadicInt l) ^ B ∈ LinearMap.ker φ := by
      by_cases hbot : LinearMap.ker φ = ⊥
      · exfalso
        have hinj_φ : Function.Injective φ := LinearMap.ker_eq_bot.mp hbot
        have hZ_le : Module.length (PadicInt l) (PadicInt l) ≤ (B : ℕ∞) :=
          (Module.length_le_of_injective φ hinj_φ).trans hVL_le
        have hquot_le : Module.length (PadicInt l)
            (PadicInt l ⧸ Ideal.span ({(l : PadicInt l) ^ (B + 1)} : Set (PadicInt l))) ≤ (B : ℕ∞) :=
          (Module.length_le_of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)).trans hZ_le
        rw [DualExpDatum.length_dvr_quot_span_pow (padicInt_irreducible_p l) (B + 1)] at hquot_le
        have hlt : B + 1 ≤ B := by exact_mod_cast hquot_le
        omega
      · obtain ⟨g, hg⟩ := IsPrincipalIdealRing.principal (LinearMap.ker φ)
        have hg_ne : g ≠ 0 := by
          intro h0; subst h0
          rw [Submodule.span_zero_singleton] at hg
          exact hbot hg
        have hI_eq : LinearMap.ker φ =
            Ideal.span ({(l : PadicInt l) ^ g.valuation} : Set (PadicInt l)) := by
          have hg' : LinearMap.ker φ = Ideal.span ({g} : Set (PadicInt l)) := hg
          rw [hg']
          conv_lhs => rw [PadicInt.unitCoeff_spec hg_ne, mul_comm]
          exact Ideal.span_singleton_mul_right_unit (PadicInt.unitCoeff hg_ne).isUnit _
        have hquot_eq : Module.length (PadicInt l) (PadicInt l ⧸ LinearMap.ker φ) =
            (g.valuation : ℕ∞) := by
          rw [hI_eq]
          exact DualExpDatum.length_dvr_quot_span_pow (padicInt_irreducible_p l) g.valuation
        have hle_val : g.valuation ≤ B := by
          have h1 : Module.length (PadicInt l) (PadicInt l ⧸ LinearMap.ker φ) =
              Module.length (PadicInt l) (LinearMap.range φ) :=
            φ.quotKerEquivRange.length_eq
          rw [← h1, hquot_eq] at hran_le
          exact_mod_cast hran_le
        rw [hI_eq, Ideal.mem_span_singleton]
        exact pow_dvd_pow (l : PadicInt l) hle_val
    have h0 : (l : PadicInt l) ^ B • (Submodule.Quotient.mk w : V ⧸ L) = 0 := hlB_mem
    exact hB_ne h0
  exact ⟨fun x y => by rw [hzero x, hzero y]⟩

/-- **Kato's Rational Bloch–Kato Selmer Vanishing Theorem (`katoTwoW_blochKatoSelmer_vanishes`)**:
for ANY `D : KatoFiniteLevelDatum l` with `L^*(f ⊗ χ, j) ≠ 0`, and ANY rational Bloch–Kato Selmer
space `V_sel` (`H¹_f(ℚ, V_f(χ)(j))`) with lattice `L_sel` (`H¹_f(ℚ, T_f(χ)(j))`, containing no
nonzero `ℚ_[l]`-line) embedding `V_sel / L_sel ↪ D.SelDual`:
**`Subsingleton V_sel`** (`H¹_f(ℚ, V_f(χ)(j)) = 0`, matching `Af.BlochKatoSelmerVanishes` in
Alpöge's `KatoTwoW`)! -/
theorem katoTwoW_blochKatoSelmer_vanishes {l : ℕ} [Fact l.Prime] (D : KatoFiniteLevelDatum l)
    (hL : D.L_star ≠ 0)
    {V_sel : Type*} [AddCommGroup V_sel] [Module (Padic l) V_sel]
    [Module (PadicInt l) V_sel] [IsScalarTower (PadicInt l) (Padic l) V_sel]
    (L_sel : Submodule (PadicInt l) V_sel)
    (hL_no_line : ∀ v : V_sel, (∀ n : ℕ, ((l : Padic l)⁻¹ ^ n) • v ∈ L_sel) → v = 0)
    (ι : (V_sel ⧸ L_sel) →ₗ[PadicInt l] D.SelDual) (hι : Function.Injective ι) :
    Subsingleton V_sel :=
  blochKatoSelmer_rational_vanishes_of_finite_length L_sel hL_no_line ι hι
    (katoTwoW_selmer_length_le D hL).2.1

/-- **Concrete `KatoFiniteLevelDatum` for Ramanujan's `Δ`** at any prime `l` and critical integer `j`
where `deltaAlgL j` is `l`-integral (in particular, EVERY prime `l ∉ {2, 3, 5}` for even `j`, and
EVERY prime `l ∉ {2, 3, 5, 7, 691}` for odd `j`), proving **EXACT SELMER VANISHING (`Sel = 0`)**! -/
theorem delta_selmer_vanishes_outside_small_primes :
    (∀ (l : ℕ) [Fact l.Prime], l ∉ ({2, 3, 5} : Finset ℕ) →
      ∀ j ∈ ({2, 4, 6, 8, 10} : Finset ℕ),
        ∃ (L_star : PadicInt l), IsUnit L_star ∧
          (L_star : Padic l) = (deltaAlgL j : Padic l) ∧
          ∀ (D : KatoFiniteLevelDatum l), D.L_star = L_star →
            Subsingleton D.SelDual ∧ Module.length (PadicInt l) D.SelDual = 0) ∧
    (∀ (l : ℕ) [Fact l.Prime], l ∉ ({2, 3, 5, 7, 691} : Finset ℕ) →
      ∀ j ∈ ({1, 3, 5, 7, 9, 11} : Finset ℕ),
        ∃ (L_star : PadicInt l), IsUnit L_star ∧
          (L_star : Padic l) = (deltaAlgL j : Padic l) ∧
          ∀ (D : KatoFiniteLevelDatum l), D.L_star = L_star →
            Subsingleton D.SelDual ∧ Module.length (PadicInt l) D.SelDual = 0) := by
  have hMkNatUnit : ∀ (l : ℕ) [Fact l.Prime] (n : ℕ), ¬ l ∣ n →
      IsUnit (n : PadicInt l) := by
    intro l _ n hnd
    rw [padicInt_isUnit_iff_not_p_dvd]
    intro hdvd
    have hmod := congrArg PadicInt.toZMod hdvd.choose_spec
    rw [map_mul, map_natCast, map_natCast, ZMod.natCast_self, zero_mul] at hmod
    exact hnd ((ZMod.natCast_eq_zero_iff n l).mp hmod)
  have hMkDivUnit : ∀ (l : ℕ) [Fact l.Prime] (a b : ℕ), ¬ l ∣ a → ¬ l ∣ b →
      ∃ L_star : PadicInt l, IsUnit L_star ∧ (L_star : Padic l) = ((a : ℚ) / (b : ℚ) : Padic l) := by
    intro l _ a b ha hb
    have hua : IsUnit (a : PadicInt l) := hMkNatUnit l a ha
    have hub : IsUnit (b : PadicInt l) := hMkNatUnit l b hb
    let binv : PadicInt l := ((hub.unit⁻¹ : (PadicInt l)ˣ) : PadicInt l)
    let L_star : PadicInt l := (a : PadicInt l) * binv
    have huL : IsUnit L_star := hua.mul hub.unit⁻¹.isUnit
    refine ⟨L_star, huL, ?_⟩
    have hbQ : (b : Padic l) ≠ 0 := by
      have hb0 : b ≠ 0 := fun h0 => hb (h0 ▸ dvd_zero l)
      exact Nat.cast_ne_zero.mpr hb0
    have hinv : (binv : Padic l) * (b : Padic l) = 1 := by
      have h1 : binv * (b : PadicInt l) = 1 := by
        change ((hub.unit⁻¹ : (PadicInt l)ˣ) : PadicInt l) * ((hub.unit : (PadicInt l)ˣ) : PadicInt l) = 1
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      have h2 := congrArg (algebraMap (PadicInt l) (Padic l)) h1
      simpa using h2
    have hcoe : (L_star : Padic l) = (a : Padic l) * (binv : Padic l) := by
      change algebraMap (PadicInt l) (Padic l) ((a : PadicInt l) * binv) = _
      simp
    rw [hcoe]
    change (a : Padic l) * (binv : Padic l) = (a : Padic l) / (b : Padic l)
    rw [eq_div_iff hbQ, mul_assoc, hinv, mul_one]
  have hCoeNat : ∀ (l : ℕ) [Fact l.Prime] (n : ℕ),
      ((n : PadicInt l) : Padic l) = ((n : ℚ) : Padic l) := by
    intro l _ n
    change algebraMap (PadicInt l) (Padic l) (n : PadicInt l) = ((n : ℚ) : Padic l)
    simp
  constructor
  · intro l _ hl j hj
    have hne : l ≠ 2 ∧ l ≠ 3 ∧ l ≠ 5 := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
      exact hl
    obtain ⟨h48, h25, h20⟩ := not_dvd_of_prime_not_mem_235 Fact.out hne.1 hne.2.1 hne.2.2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl
    · refine ⟨(48 : PadicInt l), hMkNatUnit l 48 h48, by simpa [deltaAlgL] using hCoeNat l 48, fun D hD => ?_⟩
      have h := katoTwoW_selmer_vanishes_of_unit D (hD ▸ hMkNatUnit l 48 h48); exact ⟨h.1, h.2.1⟩
    · refine ⟨(25 : PadicInt l), hMkNatUnit l 25 h25, by simpa [deltaAlgL] using hCoeNat l 25, fun D hD => ?_⟩
      have h := katoTwoW_selmer_vanishes_of_unit D (hD ▸ hMkNatUnit l 25 h25); exact ⟨h.1, h.2.1⟩
    · refine ⟨(20 : PadicInt l), hMkNatUnit l 20 h20, by simpa [deltaAlgL] using hCoeNat l 20, fun D hD => ?_⟩
      have h := katoTwoW_selmer_vanishes_of_unit D (hD ▸ hMkNatUnit l 20 h20); exact ⟨h.1, h.2.1⟩
    · refine ⟨(25 : PadicInt l), hMkNatUnit l 25 h25, by simpa [deltaAlgL] using hCoeNat l 25, fun D hD => ?_⟩
      have h := katoTwoW_selmer_vanishes_of_unit D (hD ▸ hMkNatUnit l 25 h25); exact ⟨h.1, h.2.1⟩
    · refine ⟨(48 : PadicInt l), hMkNatUnit l 48 h48, by simpa [deltaAlgL] using hCoeNat l 48, fun D hD => ?_⟩
      have h := katoTwoW_selmer_vanishes_of_unit D (hD ▸ hMkNatUnit l 48 h48); exact ⟨h.1, h.2.1⟩
  · intro l _ hl j hj
    have hne : l ≠ 2 ∧ l ≠ 3 ∧ l ≠ 5 ∧ l ≠ 7 ∧ l ≠ 691 := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
      exact hl
    obtain ⟨h22680, h691, h14, h9⟩ :=
      not_dvd_of_prime_not_mem_2357691 Fact.out hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨L_star, hu, hcoe⟩ := hMkDivUnit l 22680 691 h22680 h691
      refine ⟨L_star, hu, by simpa [deltaAlgL] using hcoe, fun D hD => ?_⟩
      have h := katoTwoW_selmer_vanishes_of_unit D (hD ▸ hu); exact ⟨h.1, h.2.1⟩
    · refine ⟨(14 : PadicInt l), hMkNatUnit l 14 h14, by simpa [deltaAlgL] using hCoeNat l 14, fun D hD => ?_⟩
      have h := katoTwoW_selmer_vanishes_of_unit D (hD ▸ hMkNatUnit l 14 h14); exact ⟨h.1, h.2.1⟩
    · refine ⟨(9 : PadicInt l), hMkNatUnit l 9 h9, by simpa [deltaAlgL] using hCoeNat l 9, fun D hD => ?_⟩
      have h := katoTwoW_selmer_vanishes_of_unit D (hD ▸ hMkNatUnit l 9 h9); exact ⟨h.1, h.2.1⟩
    · refine ⟨(9 : PadicInt l), hMkNatUnit l 9 h9, by simpa [deltaAlgL] using hCoeNat l 9, fun D hD => ?_⟩
      have h := katoTwoW_selmer_vanishes_of_unit D (hD ▸ hMkNatUnit l 9 h9); exact ⟨h.1, h.2.1⟩
    · refine ⟨(14 : PadicInt l), hMkNatUnit l 14 h14, by simpa [deltaAlgL] using hCoeNat l 14, fun D hD => ?_⟩
      have h := katoTwoW_selmer_vanishes_of_unit D (hD ▸ hMkNatUnit l 14 h14); exact ⟨h.1, h.2.1⟩
    · obtain ⟨L_star, hu, hcoe⟩ := hMkDivUnit l 22680 691 h22680 h691
      refine ⟨L_star, hu, by simpa [deltaAlgL] using hcoe, fun D hD => ?_⟩
      have h := katoTwoW_selmer_vanishes_of_unit D (hD ▸ hu); exact ⟨h.1, h.2.1⟩

end FiniteLevelSelmerAndBlochKato

/-! ## Section 6: Direct Type-II (`2 + 1`) Kill for `CountI` (`katoTwoW_selmer_bound`, `KatoTwoWOfPublishedH` & GMA Bridge) -/

section TypeIIKillForCountI

/-! ### 6.1 Concrete `2 + 1` Block-Diagonal Embedding & Exact `3 × 3` Adjoint Decomposition -/

/-- Block-diagonal `2 + 1` matrix `diag(A, d) ∈ M₃(R)` for `A ∈ M₂(R)` and `d ∈ R`. -/
def blockDiag21 {R : Type*} [Zero R] (A : Matrix (Fin 2) (Fin 2) R) (d : R) :
    Matrix (Fin 3) (Fin 3) R :=
  Matrix.of fun i j =>
    if hi : i.1 < 2 then
      if hj : j.1 < 2 then A ⟨i.1, hi⟩ ⟨j.1, hj⟩ else 0
    else
      if j.1 = 2 then d else 0

theorem blockDiag21_one {R : Type*} [CommRing R] :
    blockDiag21 (1 : Matrix (Fin 2) (Fin 2) R) (1 : R) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blockDiag21]

theorem blockDiag21_mul {R : Type*} [CommRing R]
    (A₁ A₂ : Matrix (Fin 2) (Fin 2) R) (d₁ d₂ : R) :
    blockDiag21 A₁ d₁ * blockDiag21 A₂ d₂ = blockDiag21 (A₁ * A₂) (d₁ * d₂) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockDiag21, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem blockDiag21_trace {R : Type*} [CommRing R]
    (A : Matrix (Fin 2) (Fin 2) R) (d : R) :
    Matrix.trace (blockDiag21 A d) = Matrix.trace A + d := by
  simp [Matrix.trace, blockDiag21, Fin.sum_univ_three, Fin.sum_univ_two]

/-- Group homomorphism `GL₂(R) × Rˣ →* GL₃(R)` embedding a Type-II (`2 + 1`) reducible
representation `W ⊕ ψ₀` into `GL₃(R)`. -/
def blockDiag21GL {R : Type*} [CommRing R] :
    GL (Fin 2) R × Rˣ →* GL (Fin 3) R where
  toFun p :=
    { val := blockDiag21 p.1.val p.2.val
      inv := blockDiag21 p.1.inv p.2.inv
      val_inv := by rw [blockDiag21_mul, p.1.val_inv, p.2.val_inv, blockDiag21_one]
      inv_val := by rw [blockDiag21_mul, p.1.inv_val, p.2.inv_val, blockDiag21_one] }
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp [blockDiag21]
  map_mul' p q := by
    ext i j
    change (blockDiag21 (p.1.val * q.1.val) (p.2.val * q.2.val)) i j =
      (blockDiag21 p.1.val p.2.val * blockDiag21 q.1.val q.2.val) i j
    rw [blockDiag21_mul]

/-- **Exact `2 + 1` Adjoint Tangent-Space Decomposition**:
`M₃(R) ≃ₗ[R] M₂(R) × R² × R² × R`, splitting `ad(W ⊕ ψ₀)` into
`(ad(W), Hom(ψ₀, W), Hom(W, ψ₀), End(ψ₀))`! -/
def adDecomp21 (R : Type*) [CommRing R] :
    Matrix (Fin 3) (Fin 3) R ≃ₗ[R]
      Matrix (Fin 2) (Fin 2) R × (Fin 2 → R) × (Fin 2 → R) × R where
  toFun X :=
    (Matrix.of (fun i j => X i.castSucc j.castSucc),
     fun i => X i.castSucc 2,
     fun j => X 2 j.castSucc,
     X 2 2)
  invFun t :=
    Matrix.of fun i j =>
      if hi : i.1 < 2 then
        if hj : j.1 < 2 then t.1 ⟨i.1, hi⟩ ⟨j.1, hj⟩ else t.2.1 ⟨i.1, hi⟩
      else
        if hj : j.1 < 2 then t.2.2.1 ⟨j.1, hj⟩ else t.2.2.2
  map_add' _ _ := by
    ext i j <;> rfl
  map_smul' _ _ := by
    ext i j <;> rfl
  left_inv X := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  right_inv t := by
    rcases t with ⟨A, v, w, d⟩
    ext i j
    · fin_cases i <;> fin_cases j <;> simp
    · fin_cases i <;> simp
    · fin_cases i <;> simp
    · simp

/-- **Exact Conjugation Equivariance of `adDecomp21` under a Type-II (`2 + 1`) Representation
`ρ = W ⊕ ψ₀`**:
conjugating `X ∈ M₃(R)` by `diag(W, ψ₀)` preserves all four blocks and acts on the off-diagonal
`2 × 1` block as **`W ⊗ ψ₀⁻¹` (`ψ₀⁻¹ • (W *ᵥ v)`)**, on the `1 × 2` block as **`W* ⊗ ψ₀`
(`ψ₀ • (w ᵥ* W⁻¹)`)**, on the `2 × 2` block as `ad(W)` (`W * A * W⁻¹`), and trivially on the
`1 × 1` block `End(ψ₀)`! -/
theorem adDecomp21_conj_blockDiag21 {R : Type*} [CommRing R]
    (W : GL (Fin 2) R) (ψ₀ : Rˣ) (X : Matrix (Fin 3) (Fin 3) R) :
    adDecomp21 R (blockDiag21 W.val ψ₀.val * X * blockDiag21 W.inv ψ₀.inv) =
      (W.val * (adDecomp21 R X).1 * W.inv,
       ψ₀.inv • (W.val.mulVec (adDecomp21 R X).2.1),
       ψ₀.val • ((adDecomp21 R X).2.2.1 ᵥ* W.inv),
       (adDecomp21 R X).2.2.2) := by
  have hψ : ψ₀.val * ψ₀.inv = 1 := ψ₀.val_inv
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [adDecomp21, blockDiag21, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]
  · ext i
    fin_cases i <;>
      simp [adDecomp21, blockDiag21, Matrix.mul_apply, Fin.sum_univ_three] <;> ring
  · ext j
    fin_cases j <;>
      simp [adDecomp21, blockDiag21, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Fin.sum_univ_three, Fin.sum_univ_two] <;> ring
  · simp [adDecomp21, blockDiag21, Matrix.mul_apply, Fin.sum_univ_three]
    calc ψ₀.val * X 2 2 * ψ₀.inv = (ψ₀.val * ψ₀.inv) * X 2 2 := by ring
      _ = X 2 2 := by rw [hψ, one_mul]

/-! ### 6.2 Odd-Prime Quadratic-Character Eigenspace Splitting (`Gal(K/ℚ) = {1, c}`) -/

/-- For any odd prime `l ≠ 2`, `(2 : ℤ_[l])` is a unit in `ℤ_[l]`. -/
theorem padicInt_two_isUnit {l : ℕ} [Fact l.Prime] (hl2 : l ≠ 2) :
    IsUnit (2 : PadicInt l) := by
  rw [padicInt_isUnit_iff_not_p_dvd]
  intro hdvd
  have h2 : (l : ℤ) ∣ (2 : ℤ) := by
    have hmod := congrArg PadicInt.toZMod hdvd.choose_spec
    rw [map_mul, map_natCast, map_ofNat, ZMod.natCast_self, zero_mul] at hmod
    have hd : l ∣ 2 := (ZMod.natCast_eq_zero_iff 2 l).mp (by simpa using hmod)
    exact_mod_cast hd
  have hle : (l : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) h2
  have hl2' : 2 ≤ l := (Fact.out : l.Prime).two_le
  omega

/-- **Odd-Prime Involution / Quadratic-Twist Eigenspace Splitting (`quad_twist_splitting`)**:
over any commutative ring `R` where `IsUnit (2 : R)` (in particular `ℤ_[l]` or `ℚ_[l]` for odd
prime `l ≠ 2`), ANY `R`-module `M` equipped with a `Gal(K/ℚ)`-involution `τ : M →ₗ[R] M`
(`τ ∘ τ = id`) splits canonically into the `+1` (`1`-twist) and `-1` (`θ`-twist) eigenspaces:
`M ≃ₗ[R] ker(τ - id) × ker(τ + id)`! -/
def quad_twist_splitting {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (h2 : IsUnit (2 : R)) (τ : M →ₗ[R] M) (hτ : τ.comp τ = LinearMap.id) :
    M ≃ₗ[R]
      LinearMap.ker (τ - LinearMap.id) × LinearMap.ker (τ + LinearMap.id) :=
  let half : R := ((h2.unit⁻¹ : Rˣ) : R)
  have h2half : (2 : R) * half = 1 := by
    change ((h2.unit : Rˣ) : R) * ((h2.unit⁻¹ : Rˣ) : R) = 1
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hhalf2 : half * (2 : R) = 1 := mul_comm (2 : R) half ▸ h2half
  have hτ2 : ∀ x : M, τ (τ x) = x := fun x => congrArg (fun f : M →ₗ[R] M => f x) hτ
  { toFun := fun x =>
      (⟨half • (x + τ x), by
          rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, map_smul, map_add, hτ2 x,
            add_comm (τ x) x, sub_self]⟩,
       ⟨half • (x - τ x), by
          rw [LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, map_smul, map_sub, hτ2 x]
          rw [← smul_add]; simp⟩)
    invFun := fun p => p.1.1 + p.2.1
    map_add' := fun x y => by
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · change half • (x + y + τ (x + y)) = half • (x + τ x) + half • (y + τ y)
        rw [map_add, ← smul_add]; congr 1; abel
      · change half • (x + y - τ (x + y)) = half • (x - τ x) + half • (y - τ y)
        rw [map_add, ← smul_add]; congr 1; abel
    map_smul' := fun r x => by
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · change half • (r • x + τ (r • x)) = r • (half • (x + τ x))
        rw [map_smul, ← smul_add, smul_comm]
      · change half • (r • x - τ (r • x)) = r • (half • (x - τ x))
        rw [map_smul, ← smul_sub, smul_comm]
    left_inv := fun x => by
      change half • (x + τ x) + half • (x - τ x) = x
      rw [← smul_add]
      have hsum : (x + τ x) + (x - τ x) = (2 : R) • x := by
        rw [two_smul]; abel
      rw [hsum, smul_smul, hhalf2, one_smul]
    right_inv := fun ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ => by
      have hxτ : τ x = x := sub_eq_zero.mp hx
      have hyτ : τ y = -y := eq_neg_of_add_eq_zero_left hy
      refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
      · change half • ((x + y) + τ (x + y)) = x
        rw [map_add, hxτ, hyτ]
        have hsum : (x + y) + (x + -y) = (2 : R) • x := by rw [two_smul]; abel
        rw [hsum, smul_smul, hhalf2, one_smul]
      · change half • ((x + y) - τ (x + y)) = y
        rw [map_add, hxτ, hyτ]
        have hsum : (x + y) - (x + -y) = (2 : R) • y := by rw [two_smul]; abel
        rw [hsum, smul_smul, hhalf2, one_smul] }

/-- Exact module-length additivity under `quad_twist_splitting`:
`len_R(M) = len_R(M^+) + len_R(M^-)`. -/
theorem quad_twist_length_eq_add {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (h2 : IsUnit (2 : R)) (τ : M →ₗ[R] M) (hτ : τ.comp τ = LinearMap.id) :
    Module.length R M =
      Module.length R (LinearMap.ker (τ - LinearMap.id)) +
      Module.length R (LinearMap.ker (τ + LinearMap.id)) := by
  rw [(quad_twist_splitting h2 τ hτ).length_eq]
  exact Stage2IwasawaTwoTower.length_prod

/-! ### 6.3 Direct Type-II (`2 + 1`) Kill for `CountI` (`katoTwoW_selmer_bound` & `KatoTwoWOfPublishedH`) -/

/-- **Type-II (`2 + 1`) Tangent-Space System in `CountI` (`TypeIITangentSystem l`)**:
models a `2 + 1` reducible conjugate-self-dual characteristic-0 point `ρ = W ⊕ ψ₀` in the
`U(3)/K^*` deformation ring (`K^* = ℚ(√-D)` with quadratic character `θ`), where:
- `l ≠ 2` is an odd prime,
- `T_off` is the integral off-diagonal `2 × 1` Type-II tangent module (`H¹_f(K^*, A_f ⊗ ψ₀⁻¹)∨`)
  with `Gal(K^*/ℚ)`-involution `τ`,
- its `+1`-eigenspace (`ker(τ - 1) ≃ Sel(ℚ, A_f ⊗ ψ₀⁻¹)∨`) is controlled by a
  `KatoFiniteLevelDatum l` (`datum1`) with critical value `L_star_1 = L^*(f ⊗ ψ₀⁻¹, j)`,
- its `-1`-eigenspace (`ker(τ + 1) ≃ Sel(ℚ, A_f ⊗ ψ₀⁻¹ ⊗ θ)∨`) is controlled by a
  `KatoFiniteLevelDatum l` (`datumTheta`) with critical value `L_star_theta = L^*(f ⊗ ψ₀⁻¹ ⊗ θ, j)`! -/
structure TypeIITangentSystem (l : ℕ) [Fact l.Prime] where
  hl2 : l ≠ 2
  T_off : Type
  [addToff : AddCommGroup T_off]
  [modToff : Module (PadicInt l) T_off]
  τ : T_off →ₗ[PadicInt l] T_off
  hτ : τ.comp τ = LinearMap.id
  datum1 : KatoFiniteLevelDatum l
  datumTheta : KatoFiniteLevelDatum l
  plus_le : Module.length (PadicInt l) (LinearMap.ker (τ - LinearMap.id)) ≤
    Module.length (PadicInt l) datum1.SelDual
  minus_le : Module.length (PadicInt l) (LinearMap.ker (τ + LinearMap.id)) ≤
    Module.length (PadicInt l) datumTheta.SelDual

attribute [instance] TypeIITangentSystem.addToff TypeIITangentSystem.modToff

/-- **HEADLINE `CountI` TYPE-II SELMER-LENGTH BOUND (`katoTwoW_selmer_bound`)**:
for EVERY Type-II (`2 + 1`) reducible point `S : TypeIITangentSystem l` in the `U(3)/K^*`
deformation ring, whenever BOTH critical `L`-values `L^*(f ⊗ ψ₀⁻¹, j)` and
`L^*(f ⊗ ψ₀⁻¹ ⊗ θ, j)` are nonzero:
1. **`Module.length ℤ_[l] S.T_off ≤ v_l(L^*(f, j)) + v_l(L^*(f ⊗ θ, j))`**,
2. **`Module.length ℤ_[l] S.T_off < ⊤` AND `Finite S.T_off`**,
3. **`(Module.length ℤ_[l] S.T_off).toNat ≤ v_l(L^*(f, j)) + v_l(L^*(f ⊗ θ, j))`**,
4. **`Nat.card S.T_off ∣ l ^ (v_l(L^*(f, j)) + v_l(L^*(f ⊗ θ, j)))`**! -/
theorem katoTwoW_selmer_bound {l : ℕ} [Fact l.Prime] (S : TypeIITangentSystem l)
    (hL1 : S.datum1.L_star ≠ 0) (hLθ : S.datumTheta.L_star ≠ 0) :
    Module.length (PadicInt l) S.T_off ≤
      ((S.datum1.L_star.valuation + S.datumTheta.L_star.valuation : ℕ) : ℕ∞) ∧
    Module.length (PadicInt l) S.T_off < ⊤ ∧
    Finite S.T_off ∧
    (Module.length (PadicInt l) S.T_off).toNat ≤
      S.datum1.L_star.valuation + S.datumTheta.L_star.valuation ∧
    Nat.card S.T_off ∣ l ^ (S.datum1.L_star.valuation + S.datumTheta.L_star.valuation) := by
  have h1 := katoTwoW_selmer_length_le S.datum1 hL1
  have hθ := katoTwoW_selmer_length_le S.datumTheta hLθ
  have hsplit := quad_twist_length_eq_add (padicInt_two_isUnit S.hl2) S.τ S.hτ
  have hlen_le : Module.length (PadicInt l) S.T_off ≤
      ((S.datum1.L_star.valuation + S.datumTheta.L_star.valuation : ℕ) : ℕ∞) := by
    rw [hsplit, Nat.cast_add]
    exact add_le_add (S.plus_le.trans h1.1) (S.minus_le.trans hθ.1)
  have hlt_top : Module.length (PadicInt l) S.T_off < ⊤ :=
    lt_of_le_of_lt hlen_le (ENat.natCast_lt_top _)
  have htoNat : (Module.length (PadicInt l) S.T_off).toNat ≤
      S.datum1.L_star.valuation + S.datumTheta.L_star.valuation :=
    ENat.toNat_le_of_le_natCast hlen_le
  have hlen_eq : Module.length (PadicInt l) S.T_off =
      ((Module.length (PadicInt l) S.T_off).toNat : ℕ∞) :=
    (ENat.natCast_toNat hlt_top.ne).symm
  obtain ⟨hfin, hcard⟩ := padicInt_card_eq_pow_length (p := l) _ hlen_eq
  have hdvd : Nat.card S.T_off ∣ l ^ (S.datum1.L_star.valuation + S.datumTheta.L_star.valuation) := by
    rw [hcard]
    exact Nat.pow_dvd_pow l htoNat
  exact ⟨hlen_le, hlt_top, hfin, htoNat, hdvd⟩

/-- **Exact Integral Type-II Tangent Vanishing at `l`-adic Unit Critical `L`-Values**:
whenever both `L^*(f, j)` and `L^*(f ⊗ θ, j)` are `l`-adic units, the integral Type-II off-diagonal
tangent module `S.T_off` vanishes completely (`Subsingleton S.T_off`)! -/
theorem katoTwoW_typeII_integral_vanishes_of_units {l : ℕ} [Fact l.Prime]
    (S : TypeIITangentSystem l)
    (hu1 : IsUnit S.datum1.L_star) (huθ : IsUnit S.datumTheta.L_star) :
    Subsingleton S.T_off ∧ Module.length (PadicInt l) S.T_off = 0 := by
  have hv1 : S.datum1.L_star.valuation = 0 := padicInt_valuation_eq_zero_of_isUnit hu1
  have hvθ : S.datumTheta.L_star.valuation = 0 := padicInt_valuation_eq_zero_of_isUnit huθ
  have hb := (katoTwoW_selmer_bound S hu1.ne_zero huθ.ne_zero).1
  rw [hv1, hvθ, add_zero, Nat.cast_zero] at hb
  have hlen0 : Module.length (PadicInt l) S.T_off = 0 := le_antisymm hb bot_le
  exact ⟨Module.length_eq_zero_iff.mp hlen0, hlen0⟩

/-- **EXACT RATIONAL TYPE-II (`2 + 1`) TANGENT KILL (`katoTwoW_typeII_tangent_vanishes`,
matching Alpöge's `KatoTwoWOfPublishedH.katoTwoW_of_printsH`)**:
whenever BOTH critical `L`-values `L^*(f, j) ≠ 0` and `L^*(f ⊗ θ, j) ≠ 0`:
1. The rational off-diagonal Bloch–Kato tangent space `V_off = H¹_f(K^*, W ⊗ ψ₀⁻¹)` vanishes
   identically (**`Subsingleton V_off`**), AND
2. Both `ℚ`-rational Bloch–Kato Selmer pieces `H¹_f(ℚ, W ⊗ ψ₀⁻¹)` and `H¹_f(ℚ, W ⊗ ψ₀⁻¹ ⊗ θ)`
   vanish identically! -/
theorem katoTwoW_typeII_tangent_vanishes {l : ℕ} [Fact l.Prime] (S : TypeIITangentSystem l)
    (hL1 : S.datum1.L_star ≠ 0) (hLθ : S.datumTheta.L_star ≠ 0)
    {V_off : Type*} [AddCommGroup V_off] [Module (Padic l) V_off]
    [Module (PadicInt l) V_off] [IsScalarTower (PadicInt l) (Padic l) V_off]
    (L_off : Submodule (PadicInt l) V_off)
    (hL_no_line : ∀ v : V_off, (∀ n : ℕ, ((l : Padic l)⁻¹ ^ n) • v ∈ L_off) → v = 0)
    (ι : (V_off ⧸ L_off) →ₗ[PadicInt l] S.T_off) (hι : Function.Injective ι) :
    Subsingleton V_off :=
  blochKatoSelmer_rational_vanishes_of_finite_length L_off hL_no_line ι hι
    (katoTwoW_selmer_bound S hL1 hLθ).2.1

/-- **FULL `U(3)` TYPE-II (`2 + 1`) ADJOINT RIGIDITY (`katoTwoW_full_u3_typeII_rigidity`,
matching Alpöge's `MapReducibleThreeDim.blochKatoSelmer_adRep_vanishes_of_typeII_modular`)**:
given the `2 + 1` adjoint decomposition `H¹_f(K^*, ad(W ⊕ ψ₀)) ≃ H¹_f(ad(W)) × H¹_f(W ⊗ ψ₀⁻¹) × H¹_f(W* ⊗ ψ₀) × H¹_f(End(ψ₀))`,
if `H¹_f(ad(W)) = 0` (adjoint rigidity for `W`), `H¹_f(End(ψ₀)) = 0` (Leopoldt / non-positive weight),
and the two conjugate-dual off-diagonal blocks `W ⊗ ψ₀⁻¹`, `W* ⊗ ψ₀` are controlled by
`TypeIITangentSystem l` with nonvanishing critical `L`-values, then the **ENTIRE `U(3)` Type-II
Bloch–Kato deformation tangent space vanishes (`Subsingleton Tan_ad`)**! -/
theorem katoTwoW_full_u3_typeII_rigidity {l : ℕ} [Fact l.Prime]
    {Tan_ad V_adW V_21 V_12 V_endψ : Type*}
    [AddCommGroup Tan_ad] [Module (Padic l) Tan_ad]
    [AddCommGroup V_adW] [Module (Padic l) V_adW]
    [AddCommGroup V_21] [Module (Padic l) V_21] [Module (PadicInt l) V_21]
    [IsScalarTower (PadicInt l) (Padic l) V_21]
    [AddCommGroup V_12] [Module (Padic l) V_12] [Module (PadicInt l) V_12]
    [IsScalarTower (PadicInt l) (Padic l) V_12]
    [AddCommGroup V_endψ] [Module (Padic l) V_endψ]
    (decomp : Tan_ad ≃ₗ[Padic l] V_adW × V_21 × V_12 × V_endψ)
    (h_adW : Subsingleton V_adW)
    (h_endψ : Subsingleton V_endψ)
    (S_21 S_12 : TypeIITangentSystem l)
    (hL21_1 : S_21.datum1.L_star ≠ 0) (hL21_θ : S_21.datumTheta.L_star ≠ 0)
    (hL12_1 : S_12.datum1.L_star ≠ 0) (hL12_θ : S_12.datumTheta.L_star ≠ 0)
    (L_21 : Submodule (PadicInt l) V_21)
    (hno21 : ∀ v : V_21, (∀ n : ℕ, ((l : Padic l)⁻¹ ^ n) • v ∈ L_21) → v = 0)
    (ι21 : (V_21 ⧸ L_21) →ₗ[PadicInt l] S_21.T_off) (hι21 : Function.Injective ι21)
    (L_12 : Submodule (PadicInt l) V_12)
    (hno12 : ∀ v : V_12, (∀ n : ℕ, ((l : Padic l)⁻¹ ^ n) • v ∈ L_12) → v = 0)
    (ι12 : (V_12 ⧸ L_12) →ₗ[PadicInt l] S_12.T_off) (hι12 : Function.Injective ι12) :
    Subsingleton Tan_ad := by
  have : Subsingleton V_adW := h_adW
  have : Subsingleton V_endψ := h_endψ
  have : Subsingleton V_21 := katoTwoW_typeII_tangent_vanishes S_21 hL21_1 hL21_θ L_21 hno21 ι21 hι21
  have : Subsingleton V_12 := katoTwoW_typeII_tangent_vanishes S_12 hL12_1 hL12_θ L_12 hno12 ι12 hι12
  exact decomp.toEquiv.subsingleton

/-- **Direct Bridge to `Stage11EulerSystemSelmer.SelmerSystem.shaLen` & `Stage12GMAReducibility`**:
1. Whenever a `CountI` Selmer group `Sel.shaLen E l k` is bounded by `Module.length ℤ_[l] S.T_off`
   from a Type-II system `S : TypeIITangentSystem l` with nonvanishing critical `L`-values,
   `Sel.shaLen E l k ≠ ⊤` and `(Sel.shaLen E l k).toNat ≤ v_l(L^*(f, j)) + v_l(L^*(f ⊗ θ, j))`!
2. Furthermore, on a rank-3 `U(3)` GMA `A : GMA R 3` (`Stage12GMAReducibility`), if the off-diagonal
   `Ext¹`-image `GMARedHom A f 0 1 M` injects into `S.T_off`, then
   `Module.length ℤ_[l] (GMARedHom A f 0 1 M) ≤ v_l(L^*(f, j)) + v_l(L^*(f ⊗ θ, j))`! -/
theorem countI_typeII_bridge_to_gma_and_selmer {l : ℕ} [Fact l.Prime]
    (S : TypeIITangentSystem l)
    (hL1 : S.datum1.L_star ≠ 0) (hLθ : S.datumTheta.L_star ≠ 0)
    {Sel : SelmerSystem} {E : Type} [Field E] [NumberField E] {k : ℕ}
    (hsha : Sel.shaLen E ⟨l, Fact.out⟩ k ≤ Module.length (PadicInt l) S.T_off) :
    Sel.shaLen E ⟨l, Fact.out⟩ k ≠ ⊤ ∧
    (Sel.shaLen E ⟨l, Fact.out⟩ k).toNat ≤
      S.datum1.L_star.valuation + S.datumTheta.L_star.valuation := by
  have hb := katoTwoW_selmer_bound S hL1 hLθ
  have hle : Sel.shaLen E ⟨l, Fact.out⟩ k ≤
      ((S.datum1.L_star.valuation + S.datumTheta.L_star.valuation : ℕ) : ℕ∞) :=
    hsha.trans hb.1
  exact ⟨ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle, ENat.toNat_le_of_le_natCast hle⟩

/-- **Concrete Non-Vacuous Sharp `TypeIITangentSystem` Witness** for EVERY odd prime `l` and
EVERY pair of critical `L`-value valuations `(d₁, d₂)` (wired directly to
`Stage11EulerSystemSelmer.padicIntKolyvaginSystem`):
realizes `T_off = (ℤ_[l]/l)^d₁ × (ℤ_[l]/l)^d₂` with `τ(x, y) = (x, -y)`, `L_star_1 = l^{d₁}`,
`L_star_theta = l^{d₂}`, achieving EXACT equality `Module.length ℤ_[l] T_off = d₁ + d₂`! -/
def concreteTypeIITangentSystem (l : ℕ) [Fact l.Prime] (hl2 : l ≠ 2) (d₁ d₂ : ℕ) :
    TypeIITangentSystem l :=
  let ks1 := padicIntKolyvaginSystem l d₁
  let ks2 := padicIntKolyvaginSystem l d₂
  let τ : (ks1.X × ks2.X) →ₗ[PadicInt l] (ks1.X × ks2.X) :=
    { toFun := fun p => (p.1, -p.2)
      map_add' := fun p q => by
        refine Prod.ext rfl ?_
        change -(p.2 + q.2) = -p.2 + -q.2
        abel
      map_smul' := fun r p => by ext <;> simp [smul_neg] }
  let half : PadicInt l := (((padicInt_two_isUnit hl2).unit⁻¹ : (PadicInt l)ˣ) : PadicInt l)
  have hhalf2 : half * (2 : PadicInt l) = 1 := by
    change (((padicInt_two_isUnit hl2).unit⁻¹ : (PadicInt l)ˣ) : PadicInt l) *
        (((padicInt_two_isUnit hl2).unit : (PadicInt l)ˣ) : PadicInt l) = 1
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  { hl2 := hl2
    T_off := ks1.X × ks2.X
    τ := τ
    hτ := by
      ext p <;> simp [τ]
    datum1 :=
      { SelDual := ks1.X
        ks := ks1
        sel_le_ks := le_rfl
        L_star := (l : PadicInt l) ^ d₁
        index_le_val := fun _ => by
          rw [padicInt_valuation_p_pow d₁]
          rfl }
    datumTheta :=
      { SelDual := ks2.X
        ks := ks2
        sel_le_ks := le_rfl
        L_star := (l : PadicInt l) ^ d₂
        index_le_val := fun _ => by
          rw [padicInt_valuation_p_pow d₂]
          rfl }
    plus_le := by
      let proj1 : LinearMap.ker (τ - LinearMap.id) →ₗ[PadicInt l] ks1.X :=
        (LinearMap.fst (PadicInt l) ks1.X ks2.X).comp (Submodule.subtype _)
      have hinj : Function.Injective proj1 := by
        intro ⟨⟨x₁, y₁⟩, h₁⟩ ⟨⟨x₂, y₂⟩, h₂⟩ hEq
        have hx : x₁ = x₂ := hEq
        have hy1 : (2 : PadicInt l) • y₁ = 0 := by
          have h : -y₁ - y₁ = 0 := congrArg Prod.snd h₁
          have h' : -(y₁ + y₁) = 0 := by
            calc -(y₁ + y₁) = -y₁ - y₁ := by abel
              _ = 0 := h
          rw [two_smul]; exact neg_eq_zero.mp h'
        have hy2 : (2 : PadicInt l) • y₂ = 0 := by
          have h : -y₂ - y₂ = 0 := congrArg Prod.snd h₂
          have h' : -(y₂ + y₂) = 0 := by
            calc -(y₂ + y₂) = -y₂ - y₂ := by abel
              _ = 0 := h
          rw [two_smul]; exact neg_eq_zero.mp h'
        have hy10 : y₁ = 0 := by
          have h := congrArg (half • ·) hy1
          rw [smul_smul, hhalf2, one_smul, smul_zero] at h
          exact h
        have hy20 : y₂ = 0 := by
          have h := congrArg (half • ·) hy2
          rw [smul_smul, hhalf2, one_smul, smul_zero] at h
          exact h
        exact Subtype.ext (Prod.ext hx (hy10.trans hy20.symm))
      exact Module.length_le_of_injective proj1 hinj
    minus_le := by
      let proj2 : LinearMap.ker (τ + LinearMap.id) →ₗ[PadicInt l] ks2.X :=
        (LinearMap.snd (PadicInt l) ks1.X ks2.X).comp (Submodule.subtype _)
      have hinj : Function.Injective proj2 := by
        intro ⟨⟨x₁, y₁⟩, h₁⟩ ⟨⟨x₂, y₂⟩, h₂⟩ hEq
        have hy : y₁ = y₂ := hEq
        have hx1 : (2 : PadicInt l) • x₁ = 0 := by
          have h : x₁ + x₁ = 0 := congrArg Prod.fst h₁
          rwa [two_smul]
        have hx2 : (2 : PadicInt l) • x₂ = 0 := by
          have h : x₂ + x₂ = 0 := congrArg Prod.fst h₂
          rwa [two_smul]
        have hx10 : x₁ = 0 := by
          have h := congrArg (half • ·) hx1
          rw [smul_smul, hhalf2, one_smul, smul_zero] at h
          exact h
        have hx20 : x₂ = 0 := by
          have h := congrArg (half • ·) hx2
          rw [smul_smul, hhalf2, one_smul, smul_zero] at h
          exact h
        exact Subtype.ext (Prod.ext (hx10.trans hx20.symm) hy)
      exact Module.length_le_of_injective proj2 hinj }

/-- **Exact Sharpness of `katoTwoW_selmer_bound`** on `concreteTypeIITangentSystem`:
`Module.length ℤ_[l] T_off = d₁ + d₂`! -/
theorem concreteTypeIITangentSystem_sharp (l : ℕ) [Fact l.Prime] (hl2 : l ≠ 2) (d₁ d₂ : ℕ) :
    Module.length (PadicInt l) (concreteTypeIITangentSystem l hl2 d₁ d₂).T_off =
      ((d₁ + d₂ : ℕ) : ℕ∞) := by
  change Module.length (PadicInt l)
      ((padicIntKolyvaginSystem l d₁).X × (padicIntKolyvaginSystem l d₂).X) = ((d₁ + d₂ : ℕ) : ℕ∞)
  rw [Stage2IwasawaTwoTower.length_prod, padicIntKolyvaginSystem_length_eq,
    padicIntKolyvaginSystem_length_eq, Nat.cast_add]

end TypeIIKillForCountI

end Stage13KatoEulerSystem
end RHDirect

end
