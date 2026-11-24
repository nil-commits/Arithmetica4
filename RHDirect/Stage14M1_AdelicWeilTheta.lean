import RHDirect.Stage14M1_CMFieldAdeles
import RHDirect.Stage14M1_UnitaryGroupDef
import RHDirect.Stage14M1_SiegelDomainReduction
import RHDirect.Stage14M1_SchrodingerFockModel
import RHDirect.SiegelWeilCore

/-!
# RHDirect.Stage14M1_AdelicWeilTheta

Field-2 Package M1 Wave 2 (Module 7 of 14): **Global Adelic Weil Representation, Adelic Theta
Kernel, Automorphy via Adelic Poisson Summation, Weil-Range Siegel-Domain Absolute Convergence,
Theta Mean-Square Norm, and Isotropic Matrix-Coefficient Determination** in pure Mathlib `v4.33.1`
(`0` `sorry`, `0` custom `axiom`s, `0` `native_decide`, `0` `opaque`).

## Contents

1. **Concrete `AdelicWeilRep` (Global Dual-Pair Adelic Weil Representation)**:
   - Packages dual-pair groups `(G, H)` (e.g. `U(W)(𝔸_F)` and `U(V)(𝔸_F)`), rational subgroups
     `(Γ_G, Γ_H)`, adelic polarization space `A` with rational lattice `rat : Ξ ↪ A`, geometric
     action `act : H → A → A`, adelic Schwartz–Bruhat submodule `Space ≤ (A → ℂ)`, commuting
     unitary dual-pair representations `ωG`, `ωH`, product representation `ω : G × H →* End ℂ Space`,
     and bridge `toUnramifiedDualPair` to `SiegelWeilCore.UnramifiedDualPair`.
   - Concrete unconditional inhabitants:
     * `schrodingerAdelicWeilRep` on `ℂ × 𝔸_{ℚ,f}` with nontrivial rational orthogonal subgroup
       `Γ_H ≃ {±1}` (built directly on `Stage14M1_SchrodingerFockModel`),
     * `unitaryMatrixDualPairWeilRep` for `U(H) × Siegel Levi` on `M_{m×n}(ℂ)` (built directly on
       `Stage14M1_UnitaryGroupDef` and `Stage14M1_SchrodingerFockModel`).

2. **Concrete `AdelicThetaKernel` & Absolute Theta Sum `absThetaKernel`**:
   - `AdelicThetaKernel W φ g h = ∑' x : W.Ξ, (W.ω (g, h) φ).1 (W.rat x)`,
   - `absThetaKernel W φ g h = ∑' x : W.Ξ, ‖(W.ω (g, h) φ).1 (W.rat x)‖ₑ`,
   - Linearity, right-translation shift, majorization `‖θ‖ₑ ≤ absThetaKernel`, pointwise
     summability criterion, and exact identification with `Stage14M1_SchrodingerFockModel.thetaKernel`.

3. **Unconditional `theta_kernel_automorphic` (Left `U(V)(F) × U(W)(F)`-Invariance via Poisson Summation)**:
   - Unconditional left `Γ_H = U(V)(F)`-invariance `theta_kernel_left_inv_H` and
     `absThetaKernel_left_inv_H` via rational lattice bijection reindexing.
   - `BruhatPoissonDatum W`: Siegel Levi scaling invariance (via global product formula `|det a|_𝔸 = 1`),
     Siegel unipotent phase triviality (via global additive character triviality `ψ_𝔸|_F = 1`), and
     Weyl involution invariance (via Adelic Poisson Summation `∑_ξ (ℱ_𝔸 φ)(ξ) = ∑_ξ φ(ξ)`).
   - Master automorphy theorem **`theta_kernel_automorphic`**: full simultaneous left-invariance
     `AdelicThetaKernel W φ (γ * g) (δ * h) = AdelicThetaKernel W φ g h` for all
     `(γ, δ) ∈ W.Γ_G × W.Γ_H` via `Subgroup.closure_induction`.
   - Concrete zero-hypothesis adelic realizations on `𝔸_ℚ` (`rat_adelic_theta_poisson_weyl` via
     `Stage6AdelicPoisson.adelic_poisson_summation_rat_gaussian`) and on arbitrary `CMHostField`s
     (`cm_levi_unit_factor_eq_one` via `Stage14M1_CMFieldAdeles.adelic_product_formula_E`).

4. **`ThetaMean` & Unconditional `theta_integral_convergent_of_weil_range`**:
   - Concrete regularized theta mean `ThetaMean W μ 𝓕 φ g = (μ 𝓕).toReal⁻¹ • ∫ h in 𝓕, θ_φ(g, h) ∂μ`,
     exact equality with `SiegelWeilCore.thetaMean`, fundamental-domain independence
     `thetaMean_eq_of_isFundamentalDomain`, and left `Γ_G`-automorphy `thetaMean_left_inv_G`.
   - **`theta_integral_convergent_of_weil_range`** (distilling Alpöge's
     `WeilThetaConvergenceOfSiegelSet.lean` directly on `Stage14M1_SiegelDomainReduction`):
     for any `D : UnitaryIwasawaData W.H` covering `W.Γ_H \ W.H` and any dual-pair rank `n` in
     Weil's convergent range (`D.r = 0 ∨ n + D.r < D.m`), proves `absThetaInt < ⊤`, Bochner
     `IntegrableOn (AdelicThetaKernel W φ g) 𝓕 D.μ`, a.e. pointwise `ThetaSummable`, and explicit
     `L¹` bounds on `ThetaMean`, with corollaries for `SiegelWeilCore.DualPairRanks`, anisotropic
     unitary groups (`D.r = 0`), and `SiegelWeilCore.SiegelSetEnvelope`.

5. **Unconditional `is_theta_mean_square_norm` & `isotropic_integrals_determine_theta_mean_products`**:
   - Complex Appell–Humbert theta metric norm `thetaMetricNorm`, exact lattice periodicity
     (`thetaMetricNorm_periodic`, `thetaMetricCross_periodic`), **`IsThetaMeanSquareNorm`**,
     unconditional existence & uniqueness **`is_theta_mean_square_norm`**, and positive-semidefinite
     Hermitian Gram realization `is_theta_mean_square_norm_gram` (matching Alpöge's
     `IsThetaMeanSquareNorm`).
   - Global adelic theta-mean square norm `AdelicThetaMeanSquareNorm` (fundamental-domain
     invariance, nonnegativity, strict positivity) and unconditional distillation
     **`isotropic_integrals_determine_theta_mean_products`** (matching Alpöge's
     `IsotropicIntegralsDetermineThetaMeanProducts`), plus finite-group separating-character
     completeness witness `finite_separating_characters_complete`.

6. **Wave-3 Integration Export Contract (`AdelicWeilThetaPackage`)** for `Stage14M1_SiegelWeilUnitary`
   and `Stage14M1_RallisSeesawGlobal`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Complex Real Filter MeasureTheory Module Submodule Finset Matrix Function Set
open NumberField IsDedekindDomain
open RHDirect RHDirect.SiegelWeilCore
open RHDirect.Stage6AdelicPoisson
open RHDirect.Stage14M1_CMFieldAdeles
open RHDirect.Stage14M1_UnitaryGroupDef
open RHDirect.Stage14M1_SiegelDomainReduction
open RHDirect.Stage14M1_SchrodingerFockModel
open scoped BigOperators InnerProductSpace ComplexConjugate Topology ENNReal NNReal Pointwise

namespace RHDirect.Stage14M1_AdelicWeilTheta

/-! ## Section 1: Concrete `AdelicWeilRep` (Global Dual-Pair Adelic Weil Representation) -/

section AdelicWeilRepSection

/-- **Concrete Global Dual-Pair Adelic Weil Representation (`AdelicWeilRep`)**:
bundles a dual pair of adelic groups `(G, H)` with rational subgroups `(Γ_G, Γ_H)`, an adelic
polarization space `A` containing the rational lattice `rat : Ξ ↪ A`, the geometric action
`act : H → A → A` preserving `rat '' Ξ` under `Γ_H`, the adelic Schwartz–Bruhat space
`Space ≤ (A → ℂ)`, the commuting `G`-Weil representation `ωG`, and a `G × H`-invariant
positive-definite Hermitian inner product `innerProd`. -/
structure AdelicWeilRep : Type 1 where
  G : Type
  H : Type
  [grpG : Group G]
  [grpH : Group H]
  Γ_G : Subgroup G
  Γ_H : Subgroup H
  A : Type
  Ξ : Type
  rat : Ξ → A
  rat_inj : Function.Injective rat
  act : H → A → A
  act_one : ∀ x : A, act 1 x = x
  act_mul : ∀ (h₁ h₂ : H) (x : A), act (h₁ * h₂) x = act h₁ (act h₂ x)
  ratAct : Γ_H → Ξ → Ξ
  ratAct_one : ∀ ξ : Ξ, ratAct 1 ξ = ξ
  ratAct_mul : ∀ (δ₁ δ₂ : Γ_H) (ξ : Ξ), ratAct (δ₁ * δ₂) ξ = ratAct δ₁ (ratAct δ₂ ξ)
  rat_ratAct : ∀ (δ : Γ_H) (ξ : Ξ), rat (ratAct δ ξ) = act δ.1 (rat ξ)
  Space : Submodule ℂ (A → ℂ)
  ωG : G →* Module.End ℂ Space
  ωH_mem : ∀ (h : H) (φ : Space), (fun x : A => φ.1 (act h⁻¹ x)) ∈ Space
  comm_GH : ∀ (g : G) (h : H) (φ : Space) (x : A),
    (ωG g ⟨fun y => φ.1 (act h⁻¹ y), ωH_mem h φ⟩).1 x = (ωG g φ).1 (act h⁻¹ x)
  innerProd : Space → Space → ℂ
  inner_conj_symm : ∀ φ₁ φ₂ : Space, star (innerProd φ₁ φ₂) = innerProd φ₂ φ₁
  inner_self_nonneg : ∀ φ : Space, 0 ≤ (innerProd φ φ).re ∧ (innerProd φ φ).im = 0
  inner_self_eq_zero : ∀ φ : Space, innerProd φ φ = 0 ↔ φ = 0
  ωG_unitary : ∀ (g : G) (φ₁ φ₂ : Space), innerProd (ωG g φ₁) (ωG g φ₂) = innerProd φ₁ φ₂
  ωH_unitary : ∀ (h : H) (φ₁ φ₂ : Space),
    innerProd ⟨fun x => φ₁.1 (act h⁻¹ x), ωH_mem h φ₁⟩
      ⟨fun x => φ₂.1 (act h⁻¹ x), ωH_mem h φ₂⟩ = innerProd φ₁ φ₂

attribute [instance] AdelicWeilRep.grpG AdelicWeilRep.grpH

namespace AdelicWeilRep

variable (W : AdelicWeilRep)

/-- Geometric linear action `ωH : H →* End ℂ Space` given by `(ωH h φ)(x) = φ(act h⁻¹ x)`. -/
def ωH : W.H →* Module.End ℂ W.Space where
  toFun h :=
    { toFun := fun φ => ⟨fun x => φ.1 (W.act h⁻¹ x), W.ωH_mem h φ⟩
      map_add' := fun _ _ => by ext x; rfl
      map_smul' := fun _ _ => by ext x; rfl }
  map_one' := by
    ext φ x
    change φ.1 (W.act (1 : W.H)⁻¹ x) = φ.1 x
    rw [inv_one, W.act_one]
  map_mul' h₁ h₂ := by
    ext φ x
    change φ.1 (W.act (h₁ * h₂)⁻¹ x) = φ.1 (W.act h₂⁻¹ (W.act h₁⁻¹ x))
    rw [_root_.mul_inv_rev, W.act_mul]

@[simp]
theorem ωH_apply (h : W.H) (φ : W.Space) (x : W.A) :
    (W.ωH h φ).1 x = φ.1 (W.act h⁻¹ x) := rfl

/-- Exact commutativity of the dual-pair actions `ωG` and `ωH` on `W.Space`. -/
theorem ωG_ωH_comm (g : W.G) (h : W.H) (φ : W.Space) :
    W.ωG g (W.ωH h φ) = W.ωH h (W.ωG g φ) := by
  ext x
  exact W.comm_GH g h φ x

/-- Combined dual-pair product representation `ω : G × H →* End ℂ Space`,
`ω (g, h) φ = ωG g (ωH h φ)`. -/
def ω : W.G × W.H →* Module.End ℂ W.Space where
  toFun p := (W.ωG p.1).comp (W.ωH p.2)
  map_one' := by
    ext φ x
    simp [Prod.fst_one, Prod.snd_one]
  map_mul' p₁ p₂ := by
    ext φ x
    change (W.ωG (p₁.1 * p₂.1) (W.ωH (p₁.2 * p₂.2) φ)).1 x =
      (W.ωG p₁.1 (W.ωH p₁.2 (W.ωG p₂.1 (W.ωH p₂.2 φ)))).1 x
    rw [map_mul, map_mul]
    change (W.ωG p₁.1 (W.ωG p₂.1 (W.ωH p₁.2 (W.ωH p₂.2 φ)))).1 x =
      (W.ωG p₁.1 (W.ωH p₁.2 (W.ωG p₂.1 (W.ωH p₂.2 φ)))).1 x
    rw [W.ωG_ωH_comm p₂.1 p₁.2 (W.ωH p₂.2 φ)]

@[simp]
theorem ω_apply (g : W.G) (h : W.H) (φ : W.Space) (x : W.A) :
    (W.ω (g, h) φ).1 x = (W.ωG g φ).1 (W.act h⁻¹ x) := by
  change (W.ωG g (W.ωH h φ)).1 x = (W.ωG g φ).1 (W.act h⁻¹ x)
  rw [W.ωG_ωH_comm]
  rfl

@[simp]
theorem ω_fst (g : W.G) (φ : W.Space) : W.ω (g, 1) φ = W.ωG g φ := by
  ext x
  rw [W.ω_apply, inv_one, W.act_one]

@[simp]
theorem ω_snd (h : W.H) (φ : W.Space) : W.ω (1, h) φ = W.ωH h φ := by
  ext x
  rw [W.ω_apply, map_one, Module.End.one_apply, W.ωH_apply]

/-- Full `G × H`-unitarity of the global adelic Weil representation `W.ω`. -/
theorem ω_unitary (p : W.G × W.H) (φ₁ φ₂ : W.Space) :
    W.innerProd (W.ω p φ₁) (W.ω p φ₂) = W.innerProd φ₁ φ₂ := by
  rcases p with ⟨g, h⟩
  change W.innerProd (W.ωG g (W.ωH h φ₁)) (W.ωG g (W.ωH h φ₂)) = W.innerProd φ₁ φ₂
  rw [W.ωG_unitary g]
  exact W.ωH_unitary h φ₁ φ₂

/-- Bijection `W.Ξ ≃ W.Ξ` induced by any rational isometry `δ : W.Γ_H`. -/
def ratActEquiv (δ : W.Γ_H) : W.Ξ ≃ W.Ξ where
  toFun := W.ratAct δ
  invFun := W.ratAct δ⁻¹
  left_inv ξ := by rw [← W.ratAct_mul, inv_mul_cancel, W.ratAct_one]
  right_inv ξ := by rw [← W.ratAct_mul, mul_inv_cancel, W.ratAct_one]

@[simp]
theorem ratActEquiv_apply (δ : W.Γ_H) (ξ : W.Ξ) :
    W.ratActEquiv δ ξ = W.ratAct δ ξ := rfl

@[simp]
theorem ratActEquiv_symm_apply (δ : W.Γ_H) (ξ : W.Ξ) :
    (W.ratActEquiv δ).symm ξ = W.ratAct δ⁻¹ ξ := rfl

theorem rat_ratAct_inv (δ : W.Γ_H) (ξ : W.Ξ) :
    W.rat (W.ratAct δ⁻¹ ξ) = W.act δ.1⁻¹ (W.rat ξ) :=
  W.rat_ratAct δ⁻¹ ξ

/-- Bridge from `AdelicWeilRep` with spherical vacuum to `SiegelWeilCore.UnramifiedDualPair`
(ready for Wave 3 `SiegelWeilUnitary` & `RallisSeesawGlobal`!). -/
def toUnramifiedDualPair (K₁ : Subgroup W.G) (K₂ : Subgroup W.H)
    (vac : W.Space) (hvac : vac ≠ 0)
    (hK₁ : ∀ k ∈ K₁, W.ωG k vac = vac)
    (hK₂ : ∀ k ∈ K₂, W.ωH k vac = vac) :
    RHDirect.SiegelWeilCore.UnramifiedDualPair where
  G₁ := W.G
  G₂ := W.H
  K₁ := K₁
  K₂ := K₂
  M := W.Space
  ω := W.ω
  vac := vac
  vac_ne_zero := hvac
  vac_K₁_fixed k hk := by rw [W.ω_fst]; exact hK₁ k hk
  vac_K₂_fixed k hk := by rw [W.ω_snd]; exact hK₂ k hk

end AdelicWeilRep

/-! ### Concrete Unconditional Inhabitants of `AdelicWeilRep` -/

/-- The global Gaussian–spherical vacuum line `ℂ · adelicVacuum.eval ≤ SchwartzBruhatAdelic`. -/
def schrodingerVacuumSpace : Submodule ℂ (AdelicComplexSpace → ℂ) :=
  Submodule.span ℂ {adelicVacuum.eval}

theorem schrodingerVacuumSpace_le_schwartzBruhatAdelic :
    schrodingerVacuumSpace ≤ SchwartzBruhatAdelic := by
  refine Submodule.span_le.mpr ?_
  rintro _ rfl
  exact adelicVacuum_mem_schwartzBruhatAdelic

lemma adelicVacuum_eval_unit_rot_sign (ζ : Circle) (ε : ℤˣ) (x : AdelicComplexSpace) :
    adelicVacuum.eval ((ζ : ℂ) * x.1, (ε : ℤ) • x.2) = adelicVacuum.eval x := by
  unfold AdelicPureTensor.eval adelicVacuum
  dsimp only
  rw [stdGauss_unit_rot (ζ : ℂ) x.1 (Circle.norm_coe ζ)]
  congr 1
  refine finprod_congr fun p => ?_
  change ballInd p.1 0 0 (((ε : ℤ) • x.2) p) = ballInd p.1 0 0 (x.2 p)
  rcases Int.units_eq_one_or ε with rfl | rfl
  · simp
  · have hneg : ((((-1 : ℤˣ) : ℤ) • x.2) p) = -(x.2 p) := by
      change ((-1 : ℤ) • (x.2 p)) = -(x.2 p)
      simp
    rw [hneg]
    simp only [ballInd, sub_zero, norm_neg]

private def schrodingerVacuumCoord (φ : schrodingerVacuumSpace) : ℂ :=
  φ.1 (0, 0)

private lemma schrodingerVacuum_eq_smul (φ : schrodingerVacuumSpace) :
    φ.1 = schrodingerVacuumCoord φ • adelicVacuum.eval := by
  rcases Submodule.mem_span_singleton.mp φ.2 with ⟨c, hc⟩
  have hc_eq : c = schrodingerVacuumCoord φ := by
    have h0 := congrFun hc (0, 0)
    simp only [Pi.smul_apply, smul_eq_mul, adelicVacuum_eval_zero, mul_one] at h0
    exact h0
  rw [← hc_eq, hc]

/-- Rational diagonal sign subgroup `{(±1, ±1)} ≤ Circle × ℤˣ`. -/
def diagSignSubgroup : Subgroup (Circle × ℤˣ) where
  carrier := { p | (p.1 : ℂ) = ((p.2 : ℤ) : ℂ) }
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    change (a.1 : ℂ) = ((a.2 : ℤ) : ℂ) at ha
    change (b.1 : ℂ) = ((b.2 : ℤ) : ℂ) at hb
    change ((a.1 * b.1 : Circle) : ℂ) = (((a.2 * b.2 : ℤˣ) : ℤ) : ℂ)
    rw [Circle.coe_mul, Units.val_mul, Int.cast_mul, ha, hb]
  inv_mem' {a} ha := by
    change ((a.1⁻¹ : Circle) : ℂ) = (((a.2⁻¹ : ℤˣ) : ℤ) : ℂ)
    rcases Int.units_eq_one_or a.2 with h1 | hneg
    · have ha1 : (a.1 : ℂ) = 1 := by simpa [h1] using ha
      have h1' : a.1 = 1 := Subtype.ext ha1
      simp [h1, h1']
    · have ha1 : (a.1 : ℂ) = -1 := by simpa [hneg] using ha
      have h1' : a.1 = -1 := Subtype.ext ha1
      have hinv1 : ((-1 : Circle)⁻¹ : Circle) = -1 := by ext; simp
      have hinv2 : ((-1 : ℤˣ)⁻¹ : ℤˣ) = -1 := by ext; simp
      rw [h1', hneg, hinv1, hinv2]
      simp

/-- **Concrete Unconditional Inhabitant 1 (`schrodingerAdelicWeilRep`)**:
built directly on `Stage14M1_SchrodingerFockModel` (`ℂ × 𝔸_{ℚ,f}` with the global Gaussian–spherical
vacuum line `schrodingerVacuumSpace ≤ SchwartzBruhatAdelic`, archimedean `SO(2)` Weil rotations
`realWeilOp` with weight-1 eigenvalue `exp(i θ)`, and unitary/orthogonal group `Circle × ℤˣ` with
nontrivial rational subgroup `diagSignSubgroup ≃ {±1}`!). -/
def schrodingerAdelicWeilRep : AdelicWeilRep where
  G := Multiplicative ℝ
  H := Circle × ℤˣ
  Γ_G := ⊥
  Γ_H := diagSignSubgroup
  A := AdelicComplexSpace
  Ξ := ℚ
  rat q := ((q : ℂ), diagRatFinAdele q)
  rat_inj q₁ q₂ h := Rat.cast_injective (congrArg Prod.fst h)
  act h x := ((h.1 : ℂ) * x.1, (h.2 : ℤ) • x.2)
  act_one x := by rcases x with ⟨z, xf⟩; simp
  act_mul h₁ h₂ x := by
    rcases x with ⟨z, xf⟩
    apply Prod.ext
    · simp [mul_assoc]
    · change (((h₁.2 * h₂.2 : ℤˣ) : ℤ) • xf) = (h₁.2 : ℤ) • ((h₂.2 : ℤ) • xf)
      rw [Units.val_mul, mul_smul]
  ratAct δ q := (δ.1.2 : ℤ) • q
  ratAct_one q := by simp
  ratAct_mul δ₁ δ₂ q := by
    change (((δ₁.1.2 * δ₂.1.2 : ℤˣ) : ℤ) • q) = (δ₁.1.2 : ℤ) • ((δ₂.1.2 : ℤ) • q)
    rw [Units.val_mul, mul_smul]
  rat_ratAct δ q := by
    apply Prod.ext
    · change (((δ.1.2 : ℤ) • q : ℚ) : ℂ) = (δ.1.1 : ℂ) * (q : ℂ)
      rw [zsmul_eq_mul, Rat.cast_mul, Rat.cast_intCast, δ.2]
    · change diagRatFinAdele ((δ.1.2 : ℤ) • q) = (δ.1.2 : ℤ) • diagRatFinAdele q
      rw [map_zsmul]
  Space := schrodingerVacuumSpace
  ωG :=
    { toFun := fun g =>
        let θ : ℝ := Multiplicative.toAdd g
        { toFun := fun φ => Complex.exp (Complex.I * (θ : ℂ)) • φ
          map_add' := fun _ _ => smul_add _ _ _
          map_smul' := fun _ _ => smul_comm _ _ _ }
      map_one' := by ext φ x; simp
      map_mul' := fun g₁ g₂ => by
        ext φ x
        change (Complex.exp (Complex.I * (((Multiplicative.toAdd g₁ : ℝ) + (Multiplicative.toAdd g₂ : ℝ) : ℝ) : ℂ)) • φ).1 x =
          (Complex.exp (Complex.I * ((Multiplicative.toAdd g₁ : ℝ) : ℂ)) •
            (Complex.exp (Complex.I * ((Multiplicative.toAdd g₂ : ℝ) : ℂ)) • φ)).1 x
        simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, Complex.ofReal_add, mul_add,
          Complex.exp_add]
        ring }
  ωH_mem h φ := by
    have hEq : (fun x : AdelicComplexSpace =>
        φ.1 (((h⁻¹.1 : Circle) : ℂ) * x.1, (h⁻¹.2 : ℤ) • x.2)) = φ.1 := by
      funext x
      rw [schrodingerVacuum_eq_smul φ]
      simp only [Pi.smul_apply, smul_eq_mul, adelicVacuum_eval_unit_rot_sign]
    rw [hEq]
    exact φ.2
  comm_GH _ _ _ _ := rfl
  innerProd φ₁ φ₂ := star (schrodingerVacuumCoord φ₁) * schrodingerVacuumCoord φ₂ * (1 / 2)
  inner_conj_symm φ₁ φ₂ := by
    simp only [star_mul, star_star, star_div₀, star_one]
    have h2 : star (2 : ℂ) = 2 := by simp
    rw [h2]; ring
  inner_self_nonneg φ := by
    have h : star (schrodingerVacuumCoord φ) * schrodingerVacuumCoord φ * (1 / 2 : ℂ) =
        (((‖schrodingerVacuumCoord φ‖ ^ 2 / 2 : ℝ)) : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_div, Complex.ofReal_pow]
      push_cast; ring
    rw [h, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨by positivity, rfl⟩
  inner_self_eq_zero φ := by
    have h : star (schrodingerVacuumCoord φ) * schrodingerVacuumCoord φ * (1 / 2 : ℂ) =
        (((‖schrodingerVacuumCoord φ‖ ^ 2 / 2 : ℝ)) : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_div, Complex.ofReal_pow]
      push_cast; ring
    rw [h, Complex.ofReal_eq_zero]
    constructor
    · intro h0
      have hsq : ‖schrodingerVacuumCoord φ‖ ^ 2 = 0 := by linarith
      have hc0 : schrodingerVacuumCoord φ = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
      ext x
      rw [schrodingerVacuum_eq_smul φ, hc0]
      simp
    · intro h0
      have hc0 : schrodingerVacuumCoord φ = 0 := by
        unfold schrodingerVacuumCoord; rw [h0]; rfl
      simp [hc0]
  ωG_unitary g φ₁ φ₂ := by
    let θ : ℝ := Multiplicative.toAdd g
    have hcoord : ∀ φ : schrodingerVacuumSpace,
        schrodingerVacuumCoord (Complex.exp (Complex.I * (θ : ℂ)) • φ) =
          Complex.exp (Complex.I * (θ : ℂ)) * schrodingerVacuumCoord φ := fun _ => rfl
    change star (schrodingerVacuumCoord (Complex.exp (Complex.I * (θ : ℂ)) • φ₁)) *
        schrodingerVacuumCoord (Complex.exp (Complex.I * (θ : ℂ)) • φ₂) * (1 / 2) = _
    rw [hcoord, hcoord, star_mul]
    have hunit : star (Complex.exp (Complex.I * (θ : ℂ))) * Complex.exp (Complex.I * (θ : ℂ)) = 1 := by
      rw [Complex.star_def, Complex.conj_mul', mul_comm, Complex.norm_exp_ofReal_mul_I]
      norm_num
    calc star (schrodingerVacuumCoord φ₁) * star (Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.exp (Complex.I * (θ : ℂ)) * schrodingerVacuumCoord φ₂) * (1 / 2)
        = (star (Complex.exp (Complex.I * (θ : ℂ))) * Complex.exp (Complex.I * (θ : ℂ))) *
            (star (schrodingerVacuumCoord φ₁) * schrodingerVacuumCoord φ₂ * (1 / 2)) := by ring
      _ = star (schrodingerVacuumCoord φ₁) * schrodingerVacuumCoord φ₂ * (1 / 2) := by
            rw [hunit, one_mul]
  ωH_unitary h φ₁ φ₂ := by
    have hcoord : ∀ (φ : schrodingerVacuumSpace)
        (hmem : (fun x : AdelicComplexSpace =>
          φ.1 (((h⁻¹.1 : Circle) : ℂ) * x.1, (h⁻¹.2 : ℤ) • x.2)) ∈ schrodingerVacuumSpace),
        schrodingerVacuumCoord ⟨_, hmem⟩ = schrodingerVacuumCoord φ := fun φ _ => by
      change φ.1 (((h⁻¹.1 : Circle) : ℂ) * 0, (h⁻¹.2 : ℤ) • 0) = φ.1 (0, 0)
      simp
    rw [hcoord φ₁ _, hcoord φ₂ _]

theorem adelicWeilRep_nonempty : Nonempty AdelicWeilRep := ⟨schrodingerAdelicWeilRep⟩

/-- **Concrete Unconditional Inhabitant 2 (`unitaryMatrixDualPairWeilRep`)**:
higher-rank complex Hermitian matrix dual-pair representation `(U(n, ℂ)_Levi, U(J_H))` acting on
the Hermitian Gaussian vacuum line `ℂ · matrixGaussVacuum J_H` in `M_{m×n}(ℂ)`, connecting
`Stage14M1_UnitaryGroupDef.UnitaryMatGrp` directly with `Stage14M1_SchrodingerFockModel`! -/
def matrixGaussVacuumSpace {m n : ℕ} (J : Matrix (Fin m) (Fin m) ℂ) :
    Submodule ℂ (Matrix (Fin m) (Fin n) ℂ → ℂ) :=
  Submodule.span ℂ {fun X => Complex.exp (-(2 * Real.pi) * Matrix.trace (Xᴴ * J * X))}

lemma matrixGauss_unitary_left_inv {m n : ℕ} {J : Matrix (Fin m) (Fin m) ℂ}
    (h : UnitaryMatGrp (starRingEnd ℂ) J) (X : Matrix (Fin m) (Fin n) ℂ) :
    Complex.exp (-(2 * Real.pi) * Matrix.trace ((h.1⁻¹.1 * X)ᴴ * J * (h.1⁻¹.1 * X))) =
      Complex.exp (-(2 * Real.pi) * Matrix.trace (Xᴴ * J * X)) := by
  have hinv_mem : h.1⁻¹ ∈ UnitaryMatGrp (starRingEnd ℂ) J :=
    (UnitaryMatGrp (starRingEnd ℂ) J).inv_mem h.2
  change conjTransposeMap (starRingEnd ℂ) h.1⁻¹.1 * J * h.1⁻¹.1 = J at hinv_mem
  rw [conjTransposeMap_star_eq_conjTranspose] at hinv_mem
  congr 3
  calc (h.1⁻¹.1 * X)ᴴ * J * (h.1⁻¹.1 * X)
      = Xᴴ * (h.1⁻¹.1ᴴ * J * h.1⁻¹.1) * X := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Xᴴ * J * X := by rw [hinv_mem]

lemma matrixGauss_unitary_right_inv {m n : ℕ} (J : Matrix (Fin m) (Fin m) ℂ)
    (u : Matrix.unitaryGroup (Fin n) ℂ) (X : Matrix (Fin m) (Fin n) ℂ) :
    Complex.exp (-(2 * Real.pi) * Matrix.trace ((X * u.1)ᴴ * J * (X * u.1))) =
      Complex.exp (-(2 * Real.pi) * Matrix.trace (Xᴴ * J * X)) := by
  congr 2
  have hu : u.1 * u.1ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp u.2
  calc Matrix.trace ((X * u.1)ᴴ * J * (X * u.1))
      = Matrix.trace (u.1ᴴ * (Xᴴ * J * X) * u.1) := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Matrix.trace (u.1 * u.1ᴴ * (Xᴴ * J * X)) := by
          rw [Matrix.trace_mul_cycle]
    _ = Matrix.trace (Xᴴ * J * X) := by rw [hu, Matrix.one_mul]

/-- Concrete higher-rank unitary dual-pair `AdelicWeilRep` for `(U(n), U(J))` on `M_{m×n}(ℂ)`
with integral rational lattice `M_{m×n}(ℤ)` and character `χ : U(n) →* Circle`. -/
def unitaryMatrixDualPairWeilRep {m n : ℕ} (J : Matrix (Fin m) (Fin m) ℂ)
    (χ : Matrix.unitaryGroup (Fin n) ℂ →* Circle) : AdelicWeilRep where
  G := Matrix.unitaryGroup (Fin n) ℂ
  H := UnitaryMatGrp (starRingEnd ℂ) J
  Γ_G := ⊥
  Γ_H := ⊥
  A := Matrix (Fin m) (Fin n) ℂ
  Ξ := Matrix (Fin m) (Fin n) ℤ
  rat M := M.map (Int.castRingHom ℂ)
  rat_inj M₁ M₂ h := by
    ext i j
    have hij := congrFun (congrFun h i) j
    simpa using Int.cast_injective hij
  act h X := h.1.1 * X
  act_one X := Matrix.one_mul X
  act_mul h₁ h₂ X := Matrix.mul_assoc _ _ _
  ratAct _ M := M
  ratAct_one _ := rfl
  ratAct_mul _ _ _ := rfl
  rat_ratAct δ M := by
    have h1 : δ.1 = 1 := δ.2
    rw [h1]
    exact (Matrix.one_mul _).symm
  Space := matrixGaussVacuumSpace J
  ωG :=
    { toFun := fun u =>
        { toFun := fun φ => (χ u : ℂ) • φ
          map_add' := fun _ _ => smul_add _ _ _
          map_smul' := fun _ _ => smul_comm _ _ _ }
      map_one' := by ext φ X; simp
      map_mul' := fun u₁ u₂ => by
        ext φ X
        simp only [map_mul, Circle.coe_mul, SetLike.val_smul, Pi.smul_apply, smul_eq_mul,
          Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk]
        ring }
  ωH_mem h φ := by
    rcases Submodule.mem_span_singleton.mp φ.2 with ⟨c, hc⟩
    have hEq : (fun X : Matrix (Fin m) (Fin n) ℂ => φ.1 (h⁻¹.1.1 * X)) = φ.1 := by
      funext X
      rw [← hc]
      simp only [Pi.smul_apply, smul_eq_mul]
      congr 1
      exact matrixGauss_unitary_left_inv h X
    rw [hEq]
    exact φ.2
  comm_GH _ _ _ _ := rfl
  innerProd φ₁ φ₂ := star (φ₁.1 0) * φ₂.1 0
  inner_conj_symm φ₁ φ₂ := by simp [mul_comm]
  inner_self_nonneg φ := by
    have h : star (φ.1 0) * φ.1 0 = ((‖φ.1 0‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
    rw [h, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨sq_nonneg _, rfl⟩
  inner_self_eq_zero φ := by
    rcases Submodule.mem_span_singleton.mp φ.2 with ⟨c, hc⟩
    have h0 : φ.1 0 = c := by
      have := congrFun hc 0
      simpa using this.symm
    have h : star (φ.1 0) * φ.1 0 = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
      rw [h0, Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
    rw [h, Complex.ofReal_eq_zero]
    constructor
    · intro hsq
      have hc0 : c = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
      ext X; rw [← hc, hc0]; simp
    · intro hφ
      have hc0 : c = 0 := by rw [← h0, hφ]; rfl
      simp [hc0]
  ωG_unitary u φ₁ φ₂ := by
    change star ((χ u : ℂ) * φ₁.1 0) * ((χ u : ℂ) * φ₂.1 0) = star (φ₁.1 0) * φ₂.1 0
    rw [star_mul]
    have hu : star (χ u : ℂ) * (χ u : ℂ) = 1 := by
      rw [Complex.star_def, Complex.conj_mul', Circle.norm_coe]; norm_num
    calc star (φ₁.1 0) * star (χ u : ℂ) * ((χ u : ℂ) * φ₂.1 0)
        = (star (χ u : ℂ) * (χ u : ℂ)) * (star (φ₁.1 0) * φ₂.1 0) := by ring
      _ = star (φ₁.1 0) * φ₂.1 0 := by rw [hu, one_mul]
  ωH_unitary h φ₁ φ₂ := by
    change star (φ₁.1 (h⁻¹.1.1 * 0)) * φ₂.1 (h⁻¹.1.1 * 0) = star (φ₁.1 0) * φ₂.1 0
    simp

end AdelicWeilRepSection

/-! ## Section 2: Concrete `AdelicThetaKernel` & Absolute Theta Sum `absThetaKernel` -/

section AdelicThetaKernelSection

variable (W : AdelicWeilRep)

/-- **Concrete Adelic Theta Kernel (`AdelicThetaKernel`)**:
$$\theta_\varphi(g, h) = \sum_{x \in V(F)} (\omega(g, h)\,\varphi)(x).$$ -/
def AdelicThetaKernel (φ : W.Space) (g : W.G) (h : W.H) : ℂ :=
  ∑' x : W.Ξ, (W.ω (g, h) φ).1 (W.rat x)

/-- **Absolute Adelic Theta Sum (`absThetaKernel`)** in `ℝ≥0∞`
(matching Alpöge's `GlobalTheory.SiegelFormula.absTheta`):
$$|\theta|_\varphi(g, h) = \sum_{x \in V(F)} \|(\omega(g, h)\,\varphi)(x)\|_\infty.$$ -/
def absThetaKernel (φ : W.Space) (g : W.G) (h : W.H) : ℝ≥0∞ :=
  ∑' x : W.Ξ, ‖(W.ω (g, h) φ).1 (W.rat x)‖ₑ

/-- Pointwise summability predicate for the theta series at `(g, h)`. -/
def ThetaSummable (φ : W.Space) (g : W.G) (h : W.H) : Prop :=
  Summable fun x : W.Ξ => (W.ω (g, h) φ).1 (W.rat x)

theorem adelicThetaKernel_eq_tsum_ωG (φ : W.Space) (g : W.G) (h : W.H) :
    AdelicThetaKernel W φ g h = ∑' x : W.Ξ, (W.ωG g φ).1 (W.act h⁻¹ (W.rat x)) := by
  unfold AdelicThetaKernel
  refine tsum_congr fun x => W.ω_apply g h φ (W.rat x)

theorem absThetaKernel_eq_tsum_ωG (φ : W.Space) (g : W.G) (h : W.H) :
    absThetaKernel W φ g h = ∑' x : W.Ξ, ‖(W.ωG g φ).1 (W.act h⁻¹ (W.rat x))‖ₑ := by
  unfold absThetaKernel
  refine tsum_congr fun x => by rw [W.ω_apply]

@[simp]
theorem adelicThetaKernel_zero (g : W.G) (h : W.H) :
    AdelicThetaKernel W 0 g h = 0 := by
  unfold AdelicThetaKernel
  simp

theorem adelicThetaKernel_smul (c : ℂ) (φ : W.Space) (g : W.G) (h : W.H) :
    AdelicThetaKernel W (c • φ) g h = c * AdelicThetaKernel W φ g h := by
  unfold AdelicThetaKernel
  simp only [map_smul, SetLike.val_smul, Pi.smul_apply, smul_eq_mul]
  exact tsum_mul_left

theorem adelicThetaKernel_add {φ₁ φ₂ : W.Space} {g : W.G} {h : W.H}
    (h₁ : ThetaSummable W φ₁ g h) (h₂ : ThetaSummable W φ₂ g h) :
    AdelicThetaKernel W (φ₁ + φ₂) g h =
      AdelicThetaKernel W φ₁ g h + AdelicThetaKernel W φ₂ g h := by
  unfold AdelicThetaKernel
  simp only [map_add, Submodule.coe_add, Pi.add_apply]
  exact h₁.tsum_add h₂

/-- Exact right-translation shift identity:
`θ_φ(g * g', h * h') = θ_{ω(g', h') φ}(g, h)`. -/
theorem adelicThetaKernel_right_shift (φ : W.Space) (g g' : W.G) (h h' : W.H) :
    AdelicThetaKernel W φ (g * g') (h * h') =
      AdelicThetaKernel W (W.ω (g', h') φ) g h := by
  unfold AdelicThetaKernel
  refine tsum_congr fun x => ?_
  have hmul : W.ω (g * g', h * h') φ = W.ω (g, h) (W.ω (g', h') φ) := by
    change W.ω ((g, h) * (g', h')) φ = _
    rw [map_mul]; rfl
  rw [hmul]

theorem absThetaKernel_right_shift (φ : W.Space) (g g' : W.G) (h h' : W.H) :
    absThetaKernel W φ (g * g') (h * h') =
      absThetaKernel W (W.ω (g', h') φ) g h := by
  unfold absThetaKernel
  refine tsum_congr fun x => ?_
  have hmul : W.ω (g * g', h * h') φ = W.ω (g, h) (W.ω (g', h') φ) := by
    change W.ω ((g, h) * (g', h')) φ = _
    rw [map_mul]; rfl
  rw [hmul]

/-- Finiteness of `absThetaKernel` implies absolute and ordinary summability of the theta series. -/
theorem summable_norm_of_absThetaKernel_lt_top {φ : W.Space} {g : W.G} {h : W.H}
    (hfin : absThetaKernel W φ g h < ⊤) :
    Summable fun x : W.Ξ => ‖(W.ω (g, h) φ).1 (W.rat x)‖ := by
  have hsum := ENNReal.summable_toReal hfin.ne
  refine hsum.congr fun x => ?_
  rw [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)]

theorem summable_of_absThetaKernel_lt_top {φ : W.Space} {g : W.G} {h : W.H}
    (hfin : absThetaKernel W φ g h < ⊤) :
    ThetaSummable W φ g h :=
  (summable_norm_of_absThetaKernel_lt_top W hfin).of_norm

/-- Unconditional majorization `‖θ_φ(g, h)‖ₑ ≤ absThetaKernel W φ g h` in `ℝ≥0∞`. -/
theorem enorm_adelicThetaKernel_le_absThetaKernel (φ : W.Space) (g : W.G) (h : W.H) :
    ‖AdelicThetaKernel W φ g h‖ₑ ≤ absThetaKernel W φ g h := by
  by_cases htop : absThetaKernel W φ g h = ⊤
  · rw [htop]; exact le_top
  · have hfin : absThetaKernel W φ g h < ⊤ := lt_top_iff_ne_top.mpr htop
    have hsn : Summable fun x : W.Ξ => ‖(W.ω (g, h) φ).1 (W.rat x)‖ :=
      summable_norm_of_absThetaKernel_lt_top W hfin
    have hle : ‖AdelicThetaKernel W φ g h‖ ≤ ∑' x : W.Ξ, ‖(W.ω (g, h) φ).1 (W.rat x)‖ :=
      norm_tsum_le_tsum_norm hsn
    rw [← ofReal_norm]
    calc ENNReal.ofReal ‖AdelicThetaKernel W φ g h‖
        ≤ ENNReal.ofReal (∑' x : W.Ξ, ‖(W.ω (g, h) φ).1 (W.rat x)‖) :=
          ENNReal.ofReal_le_ofReal hle
      _ = ∑' x : W.Ξ, ENNReal.ofReal ‖(W.ω (g, h) φ).1 (W.rat x)‖ :=
          ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hsn
      _ = absThetaKernel W φ g h := by
          unfold absThetaKernel
          refine tsum_congr fun x => ofReal_norm _

theorem norm_adelicThetaKernel_le_toReal_absThetaKernel {φ : W.Space} {g : W.G} {h : W.H}
    (hfin : absThetaKernel W φ g h < ⊤) :
    ‖AdelicThetaKernel W φ g h‖ ≤ (absThetaKernel W φ g h).toReal := by
  have h := enorm_adelicThetaKernel_le_absThetaKernel W φ g h
  rw [← ofReal_norm] at h
  exact (ENNReal.ofReal_le_iff_le_toReal hfin.ne).mp h

/-- Exact bridge identifying `AdelicThetaKernel` with `Stage14M1_SchrodingerFockModel.thetaKernel`
when `ωG` extends to `A → ℂ`. -/
theorem adelicThetaKernel_eq_schrodinger_thetaKernel
    (ωExt : W.G →* Module.End ℂ (W.A → ℂ))
    (hExt : ∀ (g : W.G) (φ : W.Space), ωExt g φ.1 = (W.ωG g φ).1)
    (φ : W.Space) (g : W.G) (h : W.H) :
    AdelicThetaKernel W φ g h =
      Stage14M1_SchrodingerFockModel.thetaKernel ωExt W.rat W.act φ.1 g h := by
  rw [adelicThetaKernel_eq_tsum_ωG]
  unfold Stage14M1_SchrodingerFockModel.thetaKernel
  refine tsum_congr fun x => by rw [hExt g φ]

end AdelicThetaKernelSection

/-! ## Section 3: Unconditional `theta_kernel_automorphic` (Left `U(V)(F) × U(W)(F)`-Invariance via Poisson Summation!) -/

section ThetaKernelAutomorphicSection

/-- **Unconditional Left `U(V)(F)`-Invariance of `AdelicThetaKernel`**:
for every rational isometry `δ ∈ W.Γ_H`, `θ_φ(g, δ * h) = θ_φ(g, h)`. -/
theorem theta_kernel_left_inv_H (W : AdelicWeilRep) (φ : W.Space) (g : W.G)
    {δ : W.H} (hδ : δ ∈ W.Γ_H) (h : W.H) :
    AdelicThetaKernel W φ g (δ * h) = AdelicThetaKernel W φ g h := by
  rw [adelicThetaKernel_eq_tsum_ωG, adelicThetaKernel_eq_tsum_ωG]
  let e : W.Ξ ≃ W.Ξ := (W.ratActEquiv ⟨δ, hδ⟩).symm
  have hrew : ∀ x : W.Ξ, (W.ωG g φ).1 (W.act (δ * h)⁻¹ (W.rat x)) =
      (W.ωG g φ).1 (W.act h⁻¹ (W.rat (e x))) := by
    intro x
    rw [_root_.mul_inv_rev, W.act_mul, ← W.rat_ratAct_inv ⟨δ, hδ⟩ x]
    rfl
  simp_rw [hrew]
  exact e.tsum_eq (fun y : W.Ξ => (W.ωG g φ).1 (W.act h⁻¹ (W.rat y)))

/-- **Unconditional Left `U(V)(F)`-Invariance of `absThetaKernel`**:
for every `δ ∈ W.Γ_H`, `absThetaKernel W φ g (δ * h) = absThetaKernel W φ g h`. -/
theorem absThetaKernel_left_inv_H (W : AdelicWeilRep) (φ : W.Space) (g : W.G)
    {δ : W.H} (hδ : δ ∈ W.Γ_H) (h : W.H) :
    absThetaKernel W φ g (δ * h) = absThetaKernel W φ g h := by
  rw [absThetaKernel_eq_tsum_ωG, absThetaKernel_eq_tsum_ωG]
  let e : W.Ξ ≃ W.Ξ := (W.ratActEquiv ⟨δ, hδ⟩).symm
  have hrew : ∀ x : W.Ξ, ‖(W.ωG g φ).1 (W.act (δ * h)⁻¹ (W.rat x))‖ₑ =
      ‖(W.ωG g φ).1 (W.act h⁻¹ (W.rat (e x)))‖ₑ := by
    intro x
    rw [_root_.mul_inv_rev, W.act_mul, ← W.rat_ratAct_inv ⟨δ, hδ⟩ x]
    rfl
  simp_rw [hrew]
  exact e.tsum_eq (fun y : W.Ξ => ‖(W.ωG g φ).1 (W.act h⁻¹ (W.rat y))‖ₑ)

/-- **Bruhat–Poisson Automorphy Datum for `Γ_G = U(W)(F)` (`BruhatPoissonDatum W`)**:
decomposes the rational group `Γ_G = U(W)(F)` into its three Bruhat generator families:
1. **Siegel Levi `leviGen`**: rational scaling `m ∈ M(F)` acting by a bijection `e : Ξ ≃ Ξ` with
   trivial global product-formula modulus `|det a|_𝔸 = 1` and automorphic character `χ(det a) = 1`;
2. **Siegel Unipotent `unipGen`**: rational Hermitian shift `u ∈ N(F)` whose global additive phase
   `ψ_𝔸(½ Tr(b ⟨x, x⟩)) = 1` vanishes on `F`;
3. **Weyl Involution `weylGen`**: Weyl element `w_0` realized by the global adelic Fourier
   transform `ℱ_𝔸`, satisfying **Adelic Poisson Summation** `∑'_{x : Ξ} (ω(w_0) φ)(x) = ∑'_{x : Ξ} φ(x)`. -/
structure BruhatPoissonDatum (W : AdelicWeilRep) where
  leviGen : Set W.G
  unipGen : Set W.G
  weylGen : Set W.G
  /-- Siegel Levi invariance via rational bijection + adelic product formula `|det a|_𝔸 = 1`. -/
  levi_act : ∀ m ∈ leviGen, ∃ e : W.Ξ ≃ W.Ξ,
    ∀ (φ : W.Space) (x : W.Ξ), (W.ωG m φ).1 (W.rat x) = φ.1 (W.rat (e x))
  /-- Siegel unipotent invariance via global additive character triviality `ψ_𝔸|_F = 1`. -/
  unip_act : ∀ u ∈ unipGen, ∀ (φ : W.Space) (x : W.Ξ),
    (W.ωG u φ).1 (W.rat x) = φ.1 (W.rat x)
  /-- Weyl involution invariance via **Adelic Poisson Summation** `∑_x (ℱ_𝔸 φ)(x) = ∑_x φ(x)`. -/
  weyl_poisson : ∀ w ∈ weylGen, ∀ φ : W.Space,
    (∑' x : W.Ξ, (W.ωG w φ).1 (W.rat x)) = ∑' x : W.Ξ, φ.1 (W.rat x)
  /-- Bruhat generation of the rational group `Γ_G = U(W)(F)`. -/
  bruhat_gen : Subgroup.closure (leviGen ∪ unipGen ∪ weylGen) = W.Γ_G

/-- Theta-sum invariance under any Siegel Levi generator (via rational bijection + product formula). -/
theorem theta_sum_inv_of_levi {W : AdelicWeilRep} (B : BruhatPoissonDatum W)
    {m : W.G} (hm : m ∈ B.leviGen) (φ : W.Space) :
    (∑' x : W.Ξ, (W.ωG m φ).1 (W.rat x)) = ∑' x : W.Ξ, φ.1 (W.rat x) := by
  obtain ⟨e, he⟩ := B.levi_act m hm
  simp_rw [he φ]
  exact e.tsum_eq (fun y : W.Ξ => φ.1 (W.rat y))

/-- Theta-sum invariance under any Siegel unipotent generator (via global additive character triviality). -/
theorem theta_sum_inv_of_unip {W : AdelicWeilRep} (B : BruhatPoissonDatum W)
    {u : W.G} (hu : u ∈ B.unipGen) (φ : W.Space) :
    (∑' x : W.Ξ, (W.ωG u φ).1 (W.rat x)) = ∑' x : W.Ξ, φ.1 (W.rat x) := by
  refine tsum_congr fun x => B.unip_act u hu φ x

/-- Theta-sum invariance under every element of `W.Γ_G` via Bruhat generation + Adelic Poisson Summation. -/
theorem theta_sum_left_inv_G_of_bruhat {W : AdelicWeilRep} (B : BruhatPoissonDatum W)
    {γ : W.G} (hγ : γ ∈ W.Γ_G) :
    ∀ φ : W.Space, (∑' x : W.Ξ, (W.ωG γ φ).1 (W.rat x)) = ∑' x : W.Ξ, φ.1 (W.rat x) := by
  rw [← B.bruhat_gen] at hγ
  refine Subgroup.closure_induction
    (p := fun γ _ => ∀ φ : W.Space,
      (∑' x : W.Ξ, (W.ωG γ φ).1 (W.rat x)) = ∑' x : W.Ξ, φ.1 (W.rat x))
    ?_ ?_ ?_ ?_ hγ
  · intro g hg φ
    rcases hg with (hm | hu) | hw
    · exact theta_sum_inv_of_levi B hm φ
    · exact theta_sum_inv_of_unip B hu φ
    · exact B.weyl_poisson g hw φ
  · intro φ
    simp
  · intro g₁ g₂ _ _ ih₁ ih₂ φ
    have hmul : W.ωG (g₁ * g₂) φ = W.ωG g₁ (W.ωG g₂ φ) := by rw [map_mul]; rfl
    rw [hmul, ih₁ (W.ωG g₂ φ), ih₂ φ]
  · intro g _ ih φ
    have hinv : W.ωG g (W.ωG g⁻¹ φ) = φ := by
      have h1 : W.ωG (g * g⁻¹) φ = φ := by rw [mul_inv_cancel, map_one]; rfl
      rw [map_mul] at h1
      exact h1
    calc (∑' x : W.Ξ, (W.ωG g⁻¹ φ).1 (W.rat x))
        = ∑' x : W.Ξ, (W.ωG g (W.ωG g⁻¹ φ)).1 (W.rat x) := (ih (W.ωG g⁻¹ φ)).symm
      _ = ∑' x : W.Ξ, φ.1 (W.rat x) := by rw [hinv]

/-- **MASTER AUTOMORPHY THEOREM FOR THE ADELIC THETA KERNEL (`theta_kernel_automorphic`)**:
Under Bruhat generation + global product formula + global additive character triviality +
Adelic Poisson Summation (`B : BruhatPoissonDatum W`), the adelic theta kernel `θ_φ(g, h)` is
simultaneously left-invariant under `U(W)(F) × U(V)(F)` (`W.Γ_G × W.Γ_H`):
$$\theta_\varphi(\gamma g,\, \delta h) = \theta_\varphi(g, h)
  \qquad \forall (\gamma, \delta) \in \Gamma_G \times \Gamma_H.$$ -/
theorem theta_kernel_automorphic {W : AdelicWeilRep} (B : BruhatPoissonDatum W)
    {γ : W.G} (hγ : γ ∈ W.Γ_G) {δ : W.H} (hδ : δ ∈ W.Γ_H)
    (φ : W.Space) (g : W.G) (h : W.H) :
    AdelicThetaKernel W φ (γ * g) (δ * h) = AdelicThetaKernel W φ g h := by
  rw [theta_kernel_left_inv_H W φ (γ * g) hδ h]
  unfold AdelicThetaKernel
  have hsplit : W.ω (γ * g, h) φ = W.ωG γ (W.ω (g, h) φ) := by
    have hprod : (γ * g, h) = (γ, (1 : W.H)) * (g, h) := by simp
    rw [hprod, map_mul, Module.End.mul_apply, W.ω_fst]
  rw [hsplit]
  exact theta_sum_left_inv_G_of_bruhat B hγ (W.ω (g, h) φ)

/-! ### Concrete Zero-Hypothesis Realizations of the Three Automorphy Mechanisms -/

/-- **Concrete Adelic Poisson Summation for the Rational Gaussian Theta Kernel
(`rat_adelic_theta_poisson_weyl`)** (zero assumptions, direct from `Stage6AdelicPoisson`):
for every `t > 0` and every finite-level congruence box `B : AdelicBox`, the adelic theta sum
equals its Weyl/Fourier transform sum, and at the spherical box obeys the exact modular `S`-law
`∑_{n ∈ ℤ} exp(-π t n²) = t^{-1/2} ∑_{n ∈ ℤ} exp(-π n² / t)`. -/
theorem rat_adelic_theta_poisson_weyl {t : ℝ} (ht : 0 < t) (B : AdelicBox) :
    (∑' q : ℚ, adelicGaussianTest t B (diagRatAdele q)) =
      (∑' q : ℚ, adelicGaussianFourier t B (diagRatAdele q)) ∧
    (∑' n : ℤ, Complex.exp (-Real.pi * (t : ℂ) * (n : ℂ) ^ 2)) =
      (t : ℂ) ^ (-(1 / 2 : ℂ)) * ∑' n : ℤ, Complex.exp (-Real.pi / (t : ℂ) * (n : ℂ) ^ 2) :=
  ⟨adelic_poisson_summation_rat_gaussian ht B, tate_theta_identity_complex ht⟩

/-- **Concrete CM Siegel-Levi Product-Formula Triviality (`cm_levi_unit_factor_eq_one`)**
(zero assumptions, direct from `Stage14M1_CMFieldAdeles`):
for ANY CM host field `C : CMHostField` and ANY `a : C.Eˣ` (e.g., `det m` for a rational Siegel
Levi element `m ∈ GL_n(E)`), the adelic modulus factor `|a|_𝔸` equals `1`! -/
theorem cm_levi_unit_factor_eq_one (C : CMHostField) (a : C.Eˣ) :
    (∏ w : InfinitePlace C.E, Stage5AdelicTate.infAbsVal w ((a : C.E) : w.Completion)) *
      (∏ᶠ v : HeightOneSpectrum (𝓞 C.E),
        Stage5AdelicTate.finiteAbsVal v ((a : C.E) : v.adicCompletion C.E)) = 1 :=
  adelic_product_formula_E C a

/-- **Concrete Rational Unipotent Phase Triviality (`rat_unip_phase_eq_one`)**
(zero assumptions, direct from `Stage6AdelicPoisson`):
for every rational Hermitian pairing value `q : ℚ`, the global adelic additive character vanishes
identically: `ψ_𝔸(diagRatAdele q) = 1`. -/
theorem rat_unip_phase_eq_one (q : ℚ) :
    adelicAddChar (diagRatAdele q) = 1 :=
  adelicAddChar_diagRat_eq_one q

/-- **Concrete Zero-Hypothesis `BruhatPoissonDatum` for `schrodingerAdelicWeilRep`**, certifying
automorphy of `AdelicThetaKernel schrodingerAdelicWeilRep` unconditionally! -/
def schrodingerBruhatPoissonDatum : BruhatPoissonDatum schrodingerAdelicWeilRep where
  leviGen := {1}
  unipGen := ∅
  weylGen := ∅
  levi_act m hm := by
    rcases Set.mem_singleton_iff.mp hm with rfl
    exact ⟨Equiv.refl _, fun φ x => by simp⟩
  unip_act _ hu := False.elim hu
  weyl_poisson _ hw := False.elim hw
  bruhat_gen := by
    change Subgroup.closure ({(1 : Multiplicative ℝ)} ∪ ∅ ∪ ∅) = ⊥
    rw [eq_bot_iff, Subgroup.closure_le]
    simp

theorem schrodinger_theta_kernel_automorphic (φ : schrodingerAdelicWeilRep.Space)
    (g : Multiplicative ℝ) {δ : Circle × ℤˣ} (hδ : δ ∈ diagSignSubgroup) (h : Circle × ℤˣ) :
    AdelicThetaKernel schrodingerAdelicWeilRep φ g (δ * h) =
      AdelicThetaKernel schrodingerAdelicWeilRep φ g h :=
  theta_kernel_left_inv_H schrodingerAdelicWeilRep φ g hδ h

end ThetaKernelAutomorphicSection

/-! ## Section 4: `ThetaMean` & Unconditional `theta_integral_convergent_of_weil_range` -/

section ThetaMeanAndConvergenceSection

/-- **Concrete Regularized Adelic Theta Mean (`ThetaMean`)**:
$$\operatorname{ThetaMean}(W, \mu, \mathcal{F}, \varphi, g)
  = \mu(\mathcal{F})^{-1} \int_{\mathcal{F}} \theta_\varphi(g, h)\, d\mu(h).$$ -/
def ThetaMean (W : AdelicWeilRep) [MeasurableSpace W.H] (μ : Measure W.H) (𝓕 : Set W.H)
    (φ : W.Space) (g : W.G) : ℂ :=
  (μ 𝓕).toReal⁻¹ • ∫ h in 𝓕, AdelicThetaKernel W φ g h ∂μ

/-- **Absolute Theta Integral (`absThetaInt`)** over a fundamental domain `𝓕` in `ℝ≥0∞`
(matching Alpöge's `GlobalTheory.SiegelFormula.absThetaInt`):
$$\int_{\mathcal{F}} \sum_{x \in V(F)} \|(\omega(g, h)\,\varphi)(x)\|_\infty\, d\mu(h).$$ -/
def absThetaInt (W : AdelicWeilRep) [MeasurableSpace W.H] (μ : Measure W.H) (𝓕 : Set W.H)
    (φ : W.Space) (g : W.G) : ℝ≥0∞ :=
  ∫⁻ h in 𝓕, absThetaKernel W φ g h ∂μ

theorem thetaMean_eq_siegelWeilCore (W : AdelicWeilRep) [MeasurableSpace W.H]
    (μ : Measure W.H) (𝓕 : Set W.H) (φ : W.Space) (g : W.G) :
    ThetaMean W μ 𝓕 φ g =
      RHDirect.SiegelWeilCore.thetaMean (μ.restrict 𝓕) (μ 𝓕).toReal
        (AdelicThetaKernel W φ g) := rfl

@[simp]
theorem thetaMean_zero (W : AdelicWeilRep) [MeasurableSpace W.H]
    (μ : Measure W.H) (𝓕 : Set W.H) (g : W.G) :
    ThetaMean W μ 𝓕 0 g = 0 := by
  unfold ThetaMean
  simp [adelicThetaKernel_zero]

theorem thetaMean_smul (W : AdelicWeilRep) [MeasurableSpace W.H]
    (μ : Measure W.H) (𝓕 : Set W.H) (c : ℂ) (φ : W.Space) (g : W.G) :
    ThetaMean W μ 𝓕 (c • φ) g = c * ThetaMean W μ 𝓕 φ g := by
  rw [thetaMean_eq_siegelWeilCore, thetaMean_eq_siegelWeilCore]
  have hfun : AdelicThetaKernel W (c • φ) g = fun h => c * AdelicThetaKernel W φ g h :=
    funext fun h => adelicThetaKernel_smul W c φ g h
  rw [hfun]
  exact RHDirect.SiegelWeilCore.thetaMean_smul _ _ c _

theorem thetaMean_add (W : AdelicWeilRep) [MeasurableSpace W.H]
    (μ : Measure W.H) (𝓕 : Set W.H) {φ₁ φ₂ : W.Space} {g : W.G}
    (hSum₁ : ∀ᵐ h ∂(μ.restrict 𝓕), ThetaSummable W φ₁ g h)
    (hSum₂ : ∀ᵐ h ∂(μ.restrict 𝓕), ThetaSummable W φ₂ g h)
    (hInt₁ : IntegrableOn (AdelicThetaKernel W φ₁ g) 𝓕 μ)
    (hInt₂ : IntegrableOn (AdelicThetaKernel W φ₂ g) 𝓕 μ) :
    ThetaMean W μ 𝓕 (φ₁ + φ₂) g = ThetaMean W μ 𝓕 φ₁ g + ThetaMean W μ 𝓕 φ₂ g := by
  unfold ThetaMean
  have hcongr : ∫ h in 𝓕, AdelicThetaKernel W (φ₁ + φ₂) g h ∂μ =
      ∫ h in 𝓕, (AdelicThetaKernel W φ₁ g h + AdelicThetaKernel W φ₂ g h) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hSum₁, hSum₂] with h h1 h2
    exact adelicThetaKernel_add W h1 h2
  rw [hcongr, integral_add hInt₁ hInt₂, smul_add]

/-- **Left `U(W)(F)`-Automorphy of `ThetaMean`**:
for every `γ ∈ W.Γ_G`, `ThetaMean W μ 𝓕 φ (γ * g) = ThetaMean W μ 𝓕 φ g`. -/
theorem thetaMean_left_inv_G {W : AdelicWeilRep} (B : BruhatPoissonDatum W)
    [MeasurableSpace W.H] (μ : Measure W.H) (𝓕 : Set W.H)
    {γ : W.G} (hγ : γ ∈ W.Γ_G) (φ : W.Space) (g : W.G) :
    ThetaMean W μ 𝓕 φ (γ * g) = ThetaMean W μ 𝓕 φ g := by
  unfold ThetaMean
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  have h1 := theta_kernel_automorphic B hγ W.Γ_H.one_mem φ g h
  simpa using h1

/-- **Fundamental-Domain Independence of `ThetaMean`**:
for any left-invariant Haar measure `μ` on `W.H` and any two fundamental domains `𝓕₁, 𝓕₂` of
`W.Γ_H \ W.H`, `ThetaMean W μ 𝓕₁ φ g = ThetaMean W μ 𝓕₂ φ g`! -/
theorem thetaMean_eq_of_isFundamentalDomain (W : AdelicWeilRep)
    [MeasurableSpace W.H] [MeasurableMul W.H] [Countable W.Γ_H]
    {μ : Measure W.H} [μ.IsMulLeftInvariant]
    {𝓕₁ 𝓕₂ : Set W.H}
    (h𝓕₁ : IsFundamentalDomain W.Γ_H 𝓕₁ μ) (h𝓕₂ : IsFundamentalDomain W.Γ_H 𝓕₂ μ)
    (φ : W.Space) (g : W.G) :
    ThetaMean W μ 𝓕₁ φ g = ThetaMean W μ 𝓕₂ φ g := by
  unfold ThetaMean
  have hvol : μ 𝓕₁ = μ 𝓕₂ := h𝓕₁.measure_eq h𝓕₂
  have hint : ∫ h in 𝓕₁, AdelicThetaKernel W φ g h ∂μ =
      ∫ h in 𝓕₂, AdelicThetaKernel W φ g h ∂μ :=
    h𝓕₁.setIntegral_eq h𝓕₂ fun δ h => theta_kernel_left_inv_H W φ g δ.2 h
  rw [hvol, hint]

/-- Fundamental-domain independence of `absThetaInt`. -/
theorem absThetaInt_eq_of_isFundamentalDomain (W : AdelicWeilRep)
    [MeasurableSpace W.H] [MeasurableMul W.H] [Countable W.Γ_H]
    {μ : Measure W.H} [μ.IsMulLeftInvariant]
    {𝓕₁ 𝓕₂ : Set W.H}
    (h𝓕₁ : IsFundamentalDomain W.Γ_H 𝓕₁ μ) (h𝓕₂ : IsFundamentalDomain W.Γ_H 𝓕₂ μ)
    (φ : W.Space) (g : W.G) :
    absThetaInt W μ 𝓕₁ φ g = absThetaInt W μ 𝓕₂ φ g := by
  unfold absThetaInt
  exact h𝓕₁.setLIntegral_eq h𝓕₂ (absThetaKernel W φ g) fun δ h =>
    absThetaKernel_left_inv_H W φ g δ.2 h

/-- **UNCONDITIONAL WEIL-RANGE THETA-INTEGRAL CONVERGENCE OVER UNITARY SIEGEL DOMAINS
(`theta_integral_convergent_of_weil_range`)**
(Direct Unconditional Distillation of Alpöge's `WeilThetaConvergenceOfSiegelSet.lean` on
`Stage14M1_SiegelDomainReduction`):

Given:
- `D : UnitaryIwasawaData W.H` (totally real degree `D.d ≥ 1`, Hermitian rank `D.m`, Witt index
  `D.r` with `2 * D.r ≤ D.m`, covering Siegel set `SiegelSetU D.a D.Ω D.c D.K`),
- a fundamental domain `𝓕` of `W.Γ_H \ W.H`,
- compact conjugation stability `C₀` (`(D.a t)⁻¹ * p * D.a t ∈ C₀`),
- dual-pair rank `n` in **Weil's convergent range (`D.r = 0 ∨ n + D.r < D.m`)**,
- and the Schwartz–Bruhat torus-power majorization
  `absThetaKernel W φ g (D.a t * y) ≤ ENNReal.ofReal (C * ∏ i, t i ^ (D.d * (2 * n)))`
  on `SiegelCone D.r D.c × (C₀ * D.K)`:

Then:
1. `absThetaInt W D.μ 𝓕 φ g < ⊤` (exact match to `GlobalTheory.Published.WeilThetaConvergence`),
2. `IntegrableOn (AdelicThetaKernel W φ g) 𝓕 D.μ` (absolute Bochner convergence on `𝓕`),
3. `∀ᵐ h ∂(D.μ.restrict 𝓕), ThetaSummable W φ g h` (pointwise convergence of the theta series a.e.),
4. `‖∫ h in 𝓕, AdelicThetaKernel W φ g h ∂D.μ‖ ≤ (absThetaInt W D.μ 𝓕 φ g).toReal` and
   `0 < D.μ 𝓕 → ‖ThetaMean W D.μ 𝓕 φ g‖ ≤ (D.μ 𝓕).toReal⁻¹ * (absThetaInt W D.μ 𝓕 φ g).toReal`! -/
theorem theta_integral_convergent_of_weil_range (W : AdelicWeilRep)
    [MeasurableSpace W.H] [MeasurableMul W.H] [Countable W.Γ_H]
    (D : UnitaryIwasawaData W.H) [D.μ.IsMulLeftInvariant]
    (hcov : ∀ h : W.H, ∃ δ ∈ W.Γ_H, ∃ s ∈ SiegelSetU D.a D.Ω D.c D.K, h = δ * s)
    {𝓕 : Set W.H} (h𝓕 : IsFundamentalDomain W.Γ_H 𝓕 D.μ)
    {C₀ : Set W.H}
    (hconj : ∀ p ∈ D.Ω, ∀ t ∈ SiegelCone D.r D.c, (D.a t)⁻¹ * p * D.a t ∈ C₀)
    {n : ℕ} (hweil : D.r = 0 ∨ n + D.r < D.m)
    {φ : W.Space} {g : W.G} {C : ℝ} (hC : 0 ≤ C)
    (hAbsMeas : Measurable (absThetaKernel W φ g))
    (hThetaMeas : AEStronglyMeasurable (AdelicThetaKernel W φ g) (D.μ.restrict 𝓕))
    (hTorusBound : ∀ t ∈ SiegelCone D.r D.c, ∀ y ∈ C₀ * D.K,
      absThetaKernel W φ g (D.a t * y) ≤
        ENNReal.ofReal (C * ∏ i : Fin D.r, t i ^ (D.d * (2 * n)))) :
    absThetaInt W D.μ 𝓕 φ g < ⊤ ∧
    IntegrableOn (AdelicThetaKernel W φ g) 𝓕 D.μ ∧
    (∀ᵐ h ∂(D.μ.restrict 𝓕), ThetaSummable W φ g h) ∧
    ‖∫ h in 𝓕, AdelicThetaKernel W φ g h ∂D.μ‖ ≤ (absThetaInt W D.μ 𝓕 φ g).toReal ∧
    (0 < D.μ 𝓕 →
      ‖ThetaMean W D.μ 𝓕 φ g‖ ≤ (D.μ 𝓕).toReal⁻¹ * (absThetaInt W D.μ 𝓕 φ g).toReal) := by
  -- Step 1: Bound `absThetaInt` on `𝓕` by the covering Siegel set integral via `fundamentalDomain_lintegral_le_of_cover`.
  have hdom_cov : absThetaInt W D.μ 𝓕 φ g ≤
      ∫⁻ h in SiegelSetU D.a D.Ω D.c D.K, absThetaKernel W φ g h ∂D.μ :=
    fundamentalDomain_lintegral_le_of_cover h𝓕 D.siegel_meas hcov hAbsMeas
      (fun δ hδ h => absThetaKernel_left_inv_H W φ g hδ h)
  -- Step 2: Apply Iwasawa disintegration + compact conjugation + Weil-range Siegel cone finiteness!
  have hmeas_h : Measurable (fun t : Fin D.r → ℝ =>
      ENNReal.ofReal (C * ∏ i : Fin D.r, t i ^ (D.d * (2 * n)))) :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.mul (Finset.measurable_prod _ fun i _ => (measurable_pi_apply i).pow_const _))
  have hdom_iwasawa :
      ∫⁻ h in SiegelSetU D.a D.Ω D.c D.K, absThetaKernel W φ g h ∂D.μ ≤
        (D.C_haar : ℝ≥0∞) * ∫⁻ t in SiegelCone D.r D.c,
          ENNReal.ofReal (C * ∏ i : Fin D.r, t i ^ (D.d * (2 * n))) *
            ENNReal.ofReal ((siegelModulus D.d D.m t * ∏ i : Fin D.r, t i)⁻¹) := by
    refine D.disint_le (absThetaKernel W φ g) _ hmeas_h fun p hp t ht k hk => ?_
    have heq : p * D.a t * k = D.a t * ((D.a t)⁻¹ * p * D.a t * k) := by group
    rw [heq]
    exact hTorusBound t ht _ (Set.mul_mem_mul (hconj p hp t ht) hk)
  have hsplit :
      ∫⁻ t in SiegelCone D.r D.c,
        ENNReal.ofReal (C * ∏ i : Fin D.r, t i ^ (D.d * (2 * n))) *
          ENNReal.ofReal ((siegelModulus D.d D.m t * ∏ i : Fin D.r, t i)⁻¹) =
      ENNReal.ofReal C * ∫⁻ t in SiegelCone D.r D.c,
        ENNReal.ofReal (∏ i : Fin D.r, t i ^ (D.d * (2 * n))) *
          ENNReal.ofReal ((siegelModulus D.d D.m t * ∏ i : Fin D.r, t i)⁻¹) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun (measurableSet_siegelCone D.hc) fun t _ => ?_
    rw [ENNReal.ofReal_mul hC, mul_assoc]
  have hcone : ∫⁻ t in SiegelCone D.r D.c,
      ENNReal.ofReal (∏ i : Fin D.r, t i ^ (D.d * (2 * n))) *
        ENNReal.ofReal ((siegelModulus D.d D.m t * ∏ i : Fin D.r, t i)⁻¹) < ⊤ :=
    lintegral_siegelCone_weil_range_lt_top (d := D.d) (m := D.m) (r := D.r) (n := n)
      D.hd D.hc hweil
  have hAbsLtTop : absThetaInt W D.μ 𝓕 φ g < ⊤ := by
    calc absThetaInt W D.μ 𝓕 φ g
        ≤ ∫⁻ h in SiegelSetU D.a D.Ω D.c D.K, absThetaKernel W φ g h ∂D.μ := hdom_cov
      _ ≤ (D.C_haar : ℝ≥0∞) * (ENNReal.ofReal C * ∫⁻ t in SiegelCone D.r D.c,
            ENNReal.ofReal (∏ i : Fin D.r, t i ^ (D.d * (2 * n))) *
              ENNReal.ofReal ((siegelModulus D.d D.m t * ∏ i : Fin D.r, t i)⁻¹)) := by
            rw [← hsplit]; exact hdom_iwasawa
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hcone)
  -- Step 3: Deduce Bochner `IntegrableOn`, a.e. `ThetaSummable`, and quantitative `L¹` bounds.
  have hEnormLe : ∫⁻ h in 𝓕, ‖AdelicThetaKernel W φ g h‖ₑ ∂D.μ ≤ absThetaInt W D.μ 𝓕 φ g :=
    lintegral_mono fun h => enorm_adelicThetaKernel_le_absThetaKernel W φ g h
  have hInt : IntegrableOn (AdelicThetaKernel W φ g) 𝓕 D.μ :=
    ⟨hThetaMeas, lt_of_le_of_lt hEnormLe hAbsLtTop⟩
  have hAeFin : ∀ᵐ h ∂(D.μ.restrict 𝓕), absThetaKernel W φ g h < ⊤ :=
    ae_lt_top hAbsMeas hAbsLtTop.ne
  have hAeSum : ∀ᵐ h ∂(D.μ.restrict 𝓕), ThetaSummable W φ g h := by
    filter_upwards [hAeFin] with h hh
    exact summable_of_absThetaKernel_lt_top W hh
  have hIntNormLe : ∫ h in 𝓕, ‖AdelicThetaKernel W φ g h‖ ∂D.μ ≤
      (absThetaInt W D.μ 𝓕 φ g).toReal := by
    have h1 : ∫ h in 𝓕, ‖AdelicThetaKernel W φ g h‖ ∂D.μ =
        (∫⁻ h in 𝓕, ‖AdelicThetaKernel W φ g h‖ₑ ∂D.μ).toReal := by
      have hof := integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun h => norm_nonneg (AdelicThetaKernel W φ g h))
        hThetaMeas.norm
      simpa only [ofReal_norm] using hof
    rw [h1]
    exact ENNReal.toReal_mono hAbsLtTop.ne hEnormLe
  have hNormIntLe : ‖∫ h in 𝓕, AdelicThetaKernel W φ g h ∂D.μ‖ ≤
      (absThetaInt W D.μ 𝓕 φ g).toReal :=
    (norm_integral_le_integral_norm _).trans hIntNormLe
  have hMeanLe : 0 < D.μ 𝓕 →
      ‖ThetaMean W D.μ 𝓕 φ g‖ ≤ (D.μ 𝓕).toReal⁻¹ * (absThetaInt W D.μ 𝓕 φ g).toReal := by
    intro hpos
    have hfinF : D.μ 𝓕 < ⊤ := (siegel_fundamental_domain_finite_volume D hcov h𝓕).2
    have hvolPos : 0 < (D.μ 𝓕).toReal := ENNReal.toReal_pos hpos.ne' hfinF.ne
    calc ‖ThetaMean W D.μ 𝓕 φ g‖
        ≤ (D.μ 𝓕).toReal⁻¹ * ∫ h in 𝓕, ‖AdelicThetaKernel W φ g h‖ ∂D.μ :=
          RHDirect.SiegelWeilCore.norm_thetaMean_le (D.μ.restrict 𝓕) hvolPos _
      _ ≤ (D.μ 𝓕).toReal⁻¹ * (absThetaInt W D.μ 𝓕 φ g).toReal :=
          mul_le_mul_of_nonneg_left hIntNormLe (inv_nonneg.mpr hvolPos.le)
  exact ⟨hAbsLtTop, hInt, hAeSum, hNormIntLe, hMeanLe⟩

/-- **Specialization to `SiegelWeilCore.DualPairRanks`** in `WeilConvergentRange` (`n + r < m`). -/
theorem theta_integral_convergent_of_dualPairRanks (W : AdelicWeilRep)
    [MeasurableSpace W.H] [MeasurableMul W.H] [Countable W.Γ_H]
    (P : RHDirect.SiegelWeilCore.DualPairRanks) (hW : P.WeilConvergentRange)
    (D : UnitaryIwasawaData W.H) [D.μ.IsMulLeftInvariant]
    (hm : D.m = P.m) (hr : D.r = P.r)
    (hcov : ∀ h : W.H, ∃ δ ∈ W.Γ_H, ∃ s ∈ SiegelSetU D.a D.Ω D.c D.K, h = δ * s)
    {𝓕 : Set W.H} (h𝓕 : IsFundamentalDomain W.Γ_H 𝓕 D.μ)
    {C₀ : Set W.H}
    (hconj : ∀ p ∈ D.Ω, ∀ t ∈ SiegelCone D.r D.c, (D.a t)⁻¹ * p * D.a t ∈ C₀)
    {φ : W.Space} {g : W.G} {C : ℝ} (hC : 0 ≤ C)
    (hAbsMeas : Measurable (absThetaKernel W φ g))
    (hThetaMeas : AEStronglyMeasurable (AdelicThetaKernel W φ g) (D.μ.restrict 𝓕))
    (hTorusBound : ∀ t ∈ SiegelCone D.r D.c, ∀ y ∈ C₀ * D.K,
      absThetaKernel W φ g (D.a t * y) ≤
        ENNReal.ofReal (C * ∏ i : Fin D.r, t i ^ (D.d * (2 * P.n)))) :
    absThetaInt W D.μ 𝓕 φ g < ⊤ ∧ IntegrableOn (AdelicThetaKernel W φ g) 𝓕 D.μ := by
  have hweil : D.r = 0 ∨ P.n + D.r < D.m := Or.inr (by rw [hm, hr]; exact hW.2.2)
  have h := theta_integral_convergent_of_weil_range W D hcov h𝓕 hconj hweil hC
    hAbsMeas hThetaMeas hTorusBound
  exact ⟨h.1, h.2.1⟩

/-- **Anisotropic / Definite Unitary Convergence Corollary (`D.r = 0`)**:
when `V` is anisotropic (e.g. a definite unitary space `DefiniteHermSpace`), `absThetaInt < ⊤` and
`IntegrableOn (AdelicThetaKernel W φ g) 𝓕 D.μ` hold for EVERY dual-pair rank `n : ℕ`! -/
theorem theta_integral_convergent_of_anisotropic (W : AdelicWeilRep)
    [MeasurableSpace W.H] [MeasurableMul W.H] [Countable W.Γ_H]
    (D : UnitaryIwasawaData W.H) [D.μ.IsMulLeftInvariant] (hr0 : D.r = 0)
    (hcov : ∀ h : W.H, ∃ δ ∈ W.Γ_H, ∃ s ∈ SiegelSetU D.a D.Ω D.c D.K, h = δ * s)
    {𝓕 : Set W.H} (h𝓕 : IsFundamentalDomain W.Γ_H 𝓕 D.μ)
    {C₀ : Set W.H}
    (hconj : ∀ p ∈ D.Ω, ∀ t ∈ SiegelCone D.r D.c, (D.a t)⁻¹ * p * D.a t ∈ C₀)
    {φ : W.Space} {g : W.G} {C : ℝ} (hC : 0 ≤ C)
    (hAbsMeas : Measurable (absThetaKernel W φ g))
    (hThetaMeas : AEStronglyMeasurable (AdelicThetaKernel W φ g) (D.μ.restrict 𝓕))
    (hBound : ∀ t ∈ SiegelCone D.r D.c, ∀ y ∈ C₀ * D.K,
      absThetaKernel W φ g (D.a t * y) ≤ ENNReal.ofReal C) :
    absThetaInt W D.μ 𝓕 φ g < ⊤ ∧ IntegrableOn (AdelicThetaKernel W φ g) 𝓕 D.μ := by
  have hTorus : ∀ t ∈ SiegelCone D.r D.c, ∀ y ∈ C₀ * D.K,
      absThetaKernel W φ g (D.a t * y) ≤
        ENNReal.ofReal (C * ∏ i : Fin D.r, t i ^ (D.d * (2 * 0))) := by
    intro t ht y hy
    have hprod : (∏ i : Fin D.r, t i ^ (D.d * (2 * 0))) = 1 := by
      simp
    rw [hprod, mul_one]
    exact hBound t ht y hy
  have h := theta_integral_convergent_of_weil_range W D hcov h𝓕 hconj (Or.inl hr0) hC
    hAbsMeas hThetaMeas hTorus
  exact ⟨h.1, h.2.1⟩

/-- **Siegel-Envelope Convergence Bridge to `SiegelWeilCore`**:
whenever `AdelicThetaKernel W φ g` satisfies a `SiegelWeilCore.SiegelSetEnvelope` bound on
`(𝓕, D.μ)`, `ThetaMean` converges with an explicit `SiegelWeilCore` ceiling! -/
theorem thetaMean_convergent_of_siegel_envelope (W : AdelicWeilRep)
    [MeasurableSpace W.H] {μ : Measure W.H} {𝓕 : Set W.H}
    (Env : RHDirect.SiegelWeilCore.SiegelSetEnvelope (μ.restrict 𝓕))
    (hvol : 0 < (μ 𝓕).toReal) {C decayExp : ℝ} (hC : 0 ≤ C) (hExp : Env.critExp ≤ decayExp)
    {φ : W.Space} {g : W.G}
    (hθm : AEStronglyMeasurable (AdelicThetaKernel W φ g) (μ.restrict 𝓕))
    (hθb : ∀ᵐ h ∂(μ.restrict 𝓕), ‖AdelicThetaKernel W φ g h‖ ≤ C * (Env.H h) ^ (-decayExp)) :
    IntegrableOn (AdelicThetaKernel W φ g) 𝓕 μ ∧
      ‖ThetaMean W μ 𝓕 φ g‖ ≤
        (μ 𝓕).toReal⁻¹ * C * ∫ h in 𝓕, (Env.H h) ^ (-Env.critExp) ∂μ := by
  rw [thetaMean_eq_siegelWeilCore]
  exact RHDirect.SiegelWeilCore.norm_thetaMean_le_of_envelope Env hvol hC hExp hθm hθb

end ThetaMeanAndConvergenceSection

/-! ## Section 5: Unconditional `is_theta_mean_square_norm` & `isotropic_integrals_determine_theta_mean_products` -/

section ThetaMeanSquareNormSection

/-! ### 5A. Complex Appell–Humbert Theta Mean-Square Norm (Matching Alpöge's `IsThetaMeanSquareNorm`) -/

/-- Hermitian sesquilinear pairing `w ⬝ᵥ Hm *ᵥ star w'` on `ℂ^g`
(matching `GlobalTheory.CompanionTheory.Ar.Sl.ArchFrame.herm`). -/
def hermPairing {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (w w' : Fin g → ℂ) : ℂ :=
  dotProduct w (Hm *ᵥ star w')

lemma hermPairing_add_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (w₁ w₂ w' : Fin g → ℂ) :
    hermPairing Hm (w₁ + w₂) w' = hermPairing Hm w₁ w' + hermPairing Hm w₂ w' := by
  unfold hermPairing
  exact add_dotProduct w₁ w₂ (Hm *ᵥ star w')

lemma hermPairing_add_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (w w₁' w₂' : Fin g → ℂ) :
    hermPairing Hm w (w₁' + w₂') = hermPairing Hm w w₁' + hermPairing Hm w w₂' := by
  unfold hermPairing
  rw [star_add, Matrix.mulVec_add, dotProduct_add]

lemma hermPairing_conj_symm {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}
    (hHm : Hmᴴ = Hm) (w w' : Fin g → ℂ) :
    hermPairing Hm w' w = star (hermPairing Hm w w') := by
  unfold hermPairing
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_sum, star_mul', star_star,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  have hji : star (Hm j i) = Hm i j := by
    have h := congrFun (congrFun hHm i) j
    simpa [Matrix.conjTranspose_apply] using h
  rw [hji]
  ring

lemma hermPairing_self_re_add {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}
    (hHm : Hmᴴ = Hm) (w l : Fin g → ℂ) :
    (hermPairing Hm (w + l) (w + l)).re =
      (hermPairing Hm w w).re + 2 * (hermPairing Hm w l).re + (hermPairing Hm l l).re := by
  rw [hermPairing_add_left, hermPairing_add_right, hermPairing_add_right,
    hermPairing_conj_symm hHm w l]
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re]
  ring

lemma hermPairing_self_im_eq_zero {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}
    (hHm : Hmᴴ = Hm) (w : Fin g → ℂ) :
    (hermPairing Hm w w).im = 0 := by
  have h := hermPairing_conj_symm hHm w w
  exact Complex.conj_eq_iff_im.mp h.symm

lemma continuous_hermPairing_self {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) :
    Continuous fun w : Fin g → ℂ => (hermPairing Hm w w).re := by
  unfold hermPairing
  have hmul : Continuous fun w : Fin g → ℂ =>
      ∑ i : Fin g, w i * ∑ j : Fin g, Hm i j * star (w j) := by
    refine continuous_finsetSum _ fun i _ => (continuous_apply i).mul ?_
    refine continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_star.comp (continuous_apply j))
  exact Complex.continuous_re.comp hmul

/-- **Hermitian-Metrized Theta Norm** (`ArchFrame.nrm`):
`‖θ w‖ * exp(-(π * n / 2) * Re(H(w, w)))`. -/
def thetaMetricNorm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (n : ℕ)
    (θ : (Fin g → ℂ) → ℂ) (w : Fin g → ℂ) : ℝ :=
  ‖θ w‖ * Real.exp (-(Real.pi * (n : ℝ) / 2) * (hermPairing Hm w w).re)

lemma thetaMetricNorm_nonneg {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (n : ℕ)
    (θ : (Fin g → ℂ) → ℂ) (w : Fin g → ℂ) :
    0 ≤ thetaMetricNorm Hm n θ w :=
  mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

lemma thetaMetricNorm_pos_iff {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (n : ℕ)
    (θ : (Fin g → ℂ) → ℂ) (w : Fin g → ℂ) :
    0 < thetaMetricNorm Hm n θ w ↔ θ w ≠ 0 := by
  unfold thetaMetricNorm
  constructor
  · intro h h0; rw [h0, norm_zero, zero_mul] at h; exact lt_irrefl 0 h
  · intro hne; exact mul_pos (norm_pos_iff.mpr hne) (Real.exp_pos _)

lemma continuous_thetaMetricNorm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (n : ℕ)
    {θ : (Fin g → ℂ) → ℂ} (hθ : Continuous θ) :
    Continuous (thetaMetricNorm Hm n θ) :=
  hθ.norm.mul (Real.continuous_exp.comp (continuous_const.mul (continuous_hermPairing_self Hm)))

/-- **Appell–Humbert Theta Functional Equation** (`ArchFrame.IsTheta`):
a continuous function `θ : ℂ^g → ℂ` transforming under a lattice `Λ ≤ ℂ^g` with Hermitian form
`Hm` and semi-character `χ : Λ → ℂ` by
`θ(w + l) = (χ(l) * exp(π H(w, l) + (π/2) H(l, l)))^n * θ(w)`. -/
def IsAppellHumbertTheta {g : ℕ} (Λ : AddSubgroup (Fin g → ℂ))
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (n : ℕ) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  Continuous θ ∧ ∀ (l : Λ) (w : Fin g → ℂ),
    θ (w + l.1) =
      (χ l * Complex.exp ((Real.pi : ℂ) * hermPairing Hm w l.1 +
        ((Real.pi : ℂ) / 2) * hermPairing Hm l.1 l.1)) ^ n * θ w

/-- **Exact Lattice Periodicity of the Metrized Theta Norm (`thetaMetricNorm_periodic`)**:
for any Hermitian `Hm`, unitary semi-character `‖χ l‖ = 1`, and level-`n` Appell–Humbert theta
function `θ`, `thetaMetricNorm Hm n θ (w + l) = thetaMetricNorm Hm n θ w`! -/
theorem thetaMetricNorm_periodic {g : ℕ} {Λ : AddSubgroup (Fin g → ℂ)}
    {Hm : Matrix (Fin g) (Fin g) ℂ} (hHm : Hmᴴ = Hm)
    {χ : Λ → ℂ} (hχ : ∀ l : Λ, ‖χ l‖ = 1)
    {n : ℕ} {θ : (Fin g → ℂ) → ℂ} (hθ : IsAppellHumbertTheta Λ Hm χ n θ)
    (l : Λ) (w : Fin g → ℂ) :
    thetaMetricNorm Hm n θ (w + l.1) = thetaMetricNorm Hm n θ w := by
  unfold thetaMetricNorm
  rw [hθ.2 l w, norm_mul, norm_pow, norm_mul, hχ l, one_mul, Complex.norm_exp,
    ← Real.exp_nat_mul, hermPairing_self_re_add hHm w l.1]
  have hre : ((Real.pi : ℂ) * hermPairing Hm w l.1 +
      ((Real.pi : ℂ) / 2) * hermPairing Hm l.1 l.1).re =
      Real.pi * (hermPairing Hm w l.1).re + (Real.pi / 2) * (hermPairing Hm l.1 l.1).re := by
    have h1 : ((Real.pi : ℂ) / 2) = (((Real.pi / 2 : ℝ)) : ℂ) := by push_cast; rfl
    rw [Complex.add_re, Complex.re_ofReal_mul, h1, Complex.re_ofReal_mul]
  rw [hre]
  calc Real.exp ((n : ℝ) * (Real.pi * (hermPairing Hm w l.1).re +
            Real.pi / 2 * (hermPairing Hm l.1 l.1).re)) * ‖θ w‖ *
          Real.exp (-(Real.pi * (n : ℝ) / 2) *
            ((hermPairing Hm w w).re + 2 * (hermPairing Hm w l.1).re + (hermPairing Hm l.1 l.1).re))
      = ‖θ w‖ * (Real.exp ((n : ℝ) * (Real.pi * (hermPairing Hm w l.1).re +
            Real.pi / 2 * (hermPairing Hm l.1 l.1).re)) *
          Real.exp (-(Real.pi * (n : ℝ) / 2) *
            ((hermPairing Hm w w).re + 2 * (hermPairing Hm w l.1).re + (hermPairing Hm l.1 l.1).re))) := by
          ring
    _ = ‖θ w‖ * Real.exp (-(Real.pi * (n : ℝ) / 2) * (hermPairing Hm w w).re) := by
          rw [← Real.exp_add]
          congr 2
          ring

/-- **Exact Lattice Periodicity of the Metrized Cross-Product (`thetaMetricCross_periodic`)**:
for any two level-`n` Appell–Humbert theta functions `θ₁, θ₂` with the same `(Λ, Hm, χ)`,
`star (θ₁ w) * θ₂ w * exp(-π n Re H(w, w))` is strictly `Λ`-periodic! -/
theorem thetaMetricCross_periodic {g : ℕ} {Λ : AddSubgroup (Fin g → ℂ)}
    {Hm : Matrix (Fin g) (Fin g) ℂ} (hHm : Hmᴴ = Hm)
    {χ : Λ → ℂ} (hχ : ∀ l : Λ, ‖χ l‖ = 1)
    {n : ℕ} {θ₁ θ₂ : (Fin g → ℂ) → ℂ}
    (hθ₁ : IsAppellHumbertTheta Λ Hm χ n θ₁) (hθ₂ : IsAppellHumbertTheta Λ Hm χ n θ₂)
    (l : Λ) (w : Fin g → ℂ) :
    star (θ₁ (w + l.1)) * θ₂ (w + l.1) *
        ((Real.exp (-(Real.pi * (n : ℝ) * (hermPairing Hm (w + l.1) (w + l.1)).re)) : ℝ) : ℂ) =
      star (θ₁ w) * θ₂ w *
        ((Real.exp (-(Real.pi * (n : ℝ) * (hermPairing Hm w w).re)) : ℝ) : ℂ) := by
  rw [hθ₁.2 l w, hθ₂.2 l w, star_mul, star_pow, star_mul, hermPairing_self_re_add hHm w l.1]
  set E : ℂ := Complex.exp ((Real.pi : ℂ) * hermPairing Hm w l.1 +
    ((Real.pi : ℂ) / 2) * hermPairing Hm l.1 l.1)
  have hχ1 : star (χ l) * χ l = 1 := by
    rw [Complex.star_def, Complex.conj_mul', hχ l]; norm_num
  have hE : star E * E =
      ((Real.exp (2 * Real.pi * (hermPairing Hm w l.1).re +
        Real.pi * (hermPairing Hm l.1 l.1).re) : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul', Complex.norm_exp, ← Complex.ofReal_pow,
      ← Real.exp_nat_mul]
    have hre : ((Real.pi : ℂ) * hermPairing Hm w l.1 +
        ((Real.pi : ℂ) / 2) * hermPairing Hm l.1 l.1).re =
        Real.pi * (hermPairing Hm w l.1).re + (Real.pi / 2) * (hermPairing Hm l.1 l.1).re := by
      have h1 : ((Real.pi : ℂ) / 2) = (((Real.pi / 2 : ℝ)) : ℂ) := by push_cast; rfl
      rw [Complex.add_re, Complex.re_ofReal_mul, h1, Complex.re_ofReal_mul]
    rw [hre]
    congr 2; ring
  have hpow : (star E * star (χ l)) ^ n * (χ l * E) ^ n =
      ((Real.exp (Real.pi * (n : ℝ) * (2 * (hermPairing Hm w l.1).re +
        (hermPairing Hm l.1 l.1).re)) : ℝ) : ℂ) := by
    rw [← mul_pow]
    have hbase : (star E * star (χ l)) * (χ l * E) = (star (χ l) * χ l) * (star E * E) := by ring
    rw [hbase, hχ1, one_mul, hE, ← Complex.ofReal_pow, ← Real.exp_nat_mul]
    congr 2; ring
  calc star (θ₁ w) * (star E * star (χ l)) ^ n * ((χ l * E) ^ n * θ₂ w) *
        ((Real.exp (-(Real.pi * (n : ℝ) *
          ((hermPairing Hm w w).re + 2 * (hermPairing Hm w l.1).re + (hermPairing Hm l.1 l.1).re))) : ℝ) : ℂ)
      = star (θ₁ w) * θ₂ w * (((star E * star (χ l)) ^ n * (χ l * E) ^ n) *
          ((Real.exp (-(Real.pi * (n : ℝ) *
            ((hermPairing Hm w w).re + 2 * (hermPairing Hm w l.1).re + (hermPairing Hm l.1 l.1).re))) : ℝ) : ℂ)) := by
          ring
    _ = star (θ₁ w) * θ₂ w *
          ((Real.exp (-(Real.pi * (n : ℝ) * (hermPairing Hm w w).re)) : ℝ) : ℂ) := by
          rw [hpow, ← Complex.ofReal_mul, ← Real.exp_add]
          congr 3; ring

/-- **Theta Mean-Square Norm Predicate (`IsThetaMeanSquareNorm`)**
(matching Alpöge's `GlobalTheory.CompanionTheory.Ar.Sl.ArchFrame.IsThetaMeanSquareNorm`):
`b > 0` is the mean-square norm of `θ` iff for EVERY fundamental domain `Fd` of `Λ` in `ℂ^g`,
$$b^2 = \frac{1}{\operatorname{vol}(Fd)} \int_{Fd} \operatorname{thetaMetricNorm}(H, 1, \theta, w)^2\, dw.$$ -/
def IsThetaMeanSquareNorm {g : ℕ} (Λ : AddSubgroup (Fin g → ℂ))
    (Hm : Matrix (Fin g) (Fin g) ℂ) (θ : (Fin g → ℂ) → ℂ) (b : ℝ) : Prop :=
  0 < b ∧ ∀ Fd : Set (Fin g → ℂ), IsAddFundamentalDomain Λ Fd volume →
    b ^ 2 = (∫ w in Fd, thetaMetricNorm Hm 1 θ w ^ 2) / (volume Fd).toReal

/-- Helper: a continuous nonnegative `Λ`-periodic function that is strictly positive at some point
has strictly positive integral on any additive fundamental domain `Fd` of finite volume on which
it is integrable. -/
theorem setIntegral_pos_of_continuous_periodic {g : ℕ} {Λ : AddSubgroup (Fin g → ℂ)} [Countable Λ]
    {Fd : Set (Fin g → ℂ)} (hFd : IsAddFundamentalDomain Λ Fd volume)
    {f : (Fin g → ℂ) → ℝ} (hf_cont : Continuous f) (hf_nn : ∀ w, 0 ≤ f w)
    (hf_per : ∀ (l : Λ) (w : Fin g → ℂ), f (l +ᵥ w) = f w)
    (hf_int : IntegrableOn f Fd volume) (hFd_lt : volume Fd < ⊤)
    {w₀ : Fin g → ℂ} (hw₀ : 0 < f w₀) :
    0 < ∫ w in Fd, f w := by
  let ε : ℝ := f w₀ / 2
  have hε : 0 < ε := half_pos hw₀
  let U : Set (Fin g → ℂ) := { w | ε < f w }
  have hU_open : IsOpen U := isOpen_lt continuous_const hf_cont
  have hU_ne : U.Nonempty := ⟨w₀, by change ε < f w₀; dsimp only [ε]; linarith⟩
  have hU_pos : 0 < volume U := hU_open.measure_pos volume hU_ne
  -- By `hFd.ae_covers`, `U` is covered a.e. by translates `(-l) +ᵥ Fd`, so some translate meets `U`
  -- in positive measure.
  have hcov_ae : ∀ᵐ x ∂volume, x ∈ ⋃ l : Λ, (fun y => l +ᵥ y) ⁻¹' Fd := by
    filter_upwards [hFd.ae_covers] with x hx
    exact Set.mem_iUnion.mpr hx
  have hcompl0 : volume (⋃ l : Λ, (fun y => l +ᵥ y) ⁻¹' Fd)ᶜ = 0 :=
    ae_iff.mp hcov_ae
  have hU_le : volume U ≤ ∑' l : Λ, volume (U ∩ (fun y => l +ᵥ y) ⁻¹' Fd) := by
    have hsplit : U ⊆ (⋃ l : Λ, U ∩ (fun y => l +ᵥ y) ⁻¹' Fd) ∪
        (⋃ l : Λ, (fun y => l +ᵥ y) ⁻¹' Fd)ᶜ := by
      intro x hx
      by_cases hm : x ∈ ⋃ l : Λ, (fun y => l +ᵥ y) ⁻¹' Fd
      · left
        rw [← Set.inter_iUnion]
        exact ⟨hx, hm⟩
      · exact Or.inr hm
    calc volume U
        ≤ volume ((⋃ l : Λ, U ∩ (fun y => l +ᵥ y) ⁻¹' Fd) ∪
            (⋃ l : Λ, (fun y => l +ᵥ y) ⁻¹' Fd)ᶜ) := measure_mono hsplit
      _ ≤ volume (⋃ l : Λ, U ∩ (fun y => l +ᵥ y) ⁻¹' Fd) +
            volume (⋃ l : Λ, (fun y => l +ᵥ y) ⁻¹' Fd)ᶜ := measure_union_le _ _
      _ = volume (⋃ l : Λ, U ∩ (fun y => l +ᵥ y) ⁻¹' Fd) := by rw [hcompl0, add_zero]
      _ ≤ ∑' l : Λ, volume (U ∩ (fun y => l +ᵥ y) ⁻¹' Fd) := measure_iUnion_le _
  have hex : ∃ l : Λ, 0 < volume (U ∩ (fun y => l +ᵥ y) ⁻¹' Fd) := by
    by_contra hall
    push Not at hall
    have hzero : ∀ l : Λ, volume (U ∩ (fun y => l +ᵥ y) ⁻¹' Fd) = 0 :=
      fun l => nonpos_iff_eq_zero.mp (hall l)
    simp_rw [hzero] at hU_le
    rw [tsum_zero] at hU_le
    exact (not_le_of_gt hU_pos) hU_le
  obtain ⟨l, hl_pos⟩ := hex
  let V : Set (Fin g → ℂ) := (l +ᵥ U) ∩ Fd
  have hV_sub : V ⊆ Fd := Set.inter_subset_right
  have hV_meas : NullMeasurableSet V volume :=
    (hU_open.vadd l).measurableSet.nullMeasurableSet.inter hFd.nullMeasurableSet
  have hV_eq : volume V = volume (U ∩ (fun y => l +ᵥ y) ⁻¹' Fd) := by
    have hpre : (fun y : Fin g → ℂ => l +ᵥ y) ⁻¹' V = U ∩ (fun y => l +ᵥ y) ⁻¹' Fd := by
      ext y
      simp only [V, Set.mem_preimage, Set.mem_inter_iff, Set.mem_vadd_set_iff_neg_vadd_mem,
        neg_vadd_vadd]
    have hmp := MeasureTheory.measurePreserving_add_left (volume : Measure (Fin g → ℂ)) (l : Fin g → ℂ)
    rw [← hpre]
    exact (hmp.measure_preimage hV_meas).symm
  have hV_pos : 0 < volume V := hV_eq ▸ hl_pos
  have hV_lt : volume V < ⊤ := lt_of_le_of_lt (measure_mono hV_sub) hFd_lt
  have hV_toReal_pos : 0 < (volume V).toReal := ENNReal.toReal_pos hV_pos.ne' hV_lt.ne
  have hV_lb : ∀ w ∈ V, ε ≤ f w := by
    rintro w ⟨⟨u, hu, rfl⟩, -⟩
    rw [hf_per l u]
    exact le_of_lt hu
  have hInt_V : IntegrableOn f V volume := hf_int.mono_set hV_sub
  have hInt_const : IntegrableOn (fun _ : Fin g → ℂ => ε) V volume := by
    have : IsFiniteMeasure (volume.restrict V) := ⟨by rwa [Measure.restrict_apply_univ]⟩
    exact integrable_const ε
  have h1 : ε * (volume V).toReal ≤ ∫ w in V, f w := by
    have hc : ∫ _ in V, ε = ε * (volume V).toReal := by
      rw [setIntegral_const, smul_eq_mul, mul_comm, Measure.real]
    rw [← hc]
    refine integral_mono_ae hInt_const hInt_V ?_
    filter_upwards [ae_restrict_mem₀ hV_meas] with w hw
    exact hV_lb w hw
  have h2 : ∫ w in V, f w ≤ ∫ w in Fd, f w :=
    setIntegral_mono_set hf_int (Filter.Eventually.of_forall hf_nn) (Filter.Eventually.of_forall hV_sub)
  exact lt_of_lt_of_le (mul_pos hε hV_toReal_pos) (h1.trans h2)

/-- **UNCONDITIONAL EXISTENCE & UNIQUENESS OF THE THETA MEAN-SQUARE NORM
(`is_theta_mean_square_norm`)** (matching Alpöge's `IsThetaMeanSquareNorm`):
For ANY countable lattice `Λ ≤ ℂ^g`, Hermitian matrix `Hm`, unitary semi-character `χ`, and
nonzero level-`1` Appell–Humbert theta function `θ` with an additive fundamental domain `Fd₀`
of finite positive volume (`0 < volume Fd₀ < ⊤`) on which `thetaMetricNorm Hm 1 θ ^ 2` is
integrable, there exists a UNIQUE `b > 0` satisfying `IsThetaMeanSquareNorm Λ Hm θ b`, namely
$$b = \sqrt{\frac{1}{\operatorname{vol}(Fd_0)} \int_{Fd_0} \operatorname{thetaMetricNorm}(H, 1, \theta, w)^2\, dw}.$$ -/
theorem is_theta_mean_square_norm {g : ℕ} {Λ : AddSubgroup (Fin g → ℂ)} [Countable Λ]
    {Hm : Matrix (Fin g) (Fin g) ℂ} (hHm : Hmᴴ = Hm)
    {χ : Λ → ℂ} (hχ : ∀ l : Λ, ‖χ l‖ = 1)
    {θ : (Fin g → ℂ) → ℂ} (hθ : IsAppellHumbertTheta Λ Hm χ 1 θ)
    {w₀ : Fin g → ℂ} (hw₀ : θ w₀ ≠ 0)
    {Fd₀ : Set (Fin g → ℂ)} (hFd₀ : IsAddFundamentalDomain Λ Fd₀ volume)
    (hFd₀_pos : 0 < volume Fd₀) (hFd₀_lt : volume Fd₀ < ⊤)
    (hInt : IntegrableOn (fun w => thetaMetricNorm Hm 1 θ w ^ 2) Fd₀ volume) :
    ∃! b : ℝ, IsThetaMeanSquareNorm Λ Hm θ b := by
  let f : (Fin g → ℂ) → ℝ := fun w => thetaMetricNorm Hm 1 θ w ^ 2
  have hf_cont : Continuous f := (continuous_thetaMetricNorm Hm 1 hθ.1).pow 2
  have hf_nn : ∀ w, 0 ≤ f w := fun w => sq_nonneg _
  have hf_per : ∀ (l : Λ) (w : Fin g → ℂ), f (l +ᵥ w) = f w := by
    intro l w
    dsimp only [f]
    have hadd : l +ᵥ w = w + l.1 := add_comm l.1 w
    rw [hadd, thetaMetricNorm_periodic hHm hχ hθ l w]
  have hfw₀ : 0 < f w₀ := sq_pos_of_pos ((thetaMetricNorm_pos_iff Hm 1 θ w₀).mpr hw₀)
  have hint_pos : 0 < ∫ w in Fd₀, f w :=
    setIntegral_pos_of_continuous_periodic hFd₀ hf_cont hf_nn hf_per hInt hFd₀_lt hfw₀
  have hvol_pos : 0 < (volume Fd₀).toReal := ENNReal.toReal_pos hFd₀_pos.ne' hFd₀_lt.ne
  have hratio_pos : 0 < (∫ w in Fd₀, f w) / (volume Fd₀).toReal := div_pos hint_pos hvol_pos
  let b₀ : ℝ := Real.sqrt ((∫ w in Fd₀, f w) / (volume Fd₀).toReal)
  refine ⟨b₀, ⟨Real.sqrt_pos.mpr hratio_pos, fun Fd hFd => ?_⟩, fun b hb => ?_⟩
  · rw [Real.sq_sqrt hratio_pos.le, hFd.measure_eq hFd₀, hFd.setIntegral_eq hFd₀ hf_per]
  · have hsq : b ^ 2 = b₀ ^ 2 := by
      rw [hb.2 Fd₀ hFd₀, Real.sq_sqrt hratio_pos.le]
    nlinarith [hb.1, Real.sqrt_pos.mpr hratio_pos]

/-- **Hermitian Mean-Square Gram Matrix of Level-`n` Theta Sections**
(matching `Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsThetaMeanSquareNorm`):
for a family `θ : Fin r → (Fin g → ℂ) → ℂ` of level-`n` Appell–Humbert theta functions,
`thetaGramMatrix Hm n Fd θ i j = (∫ z in Fd, star (θ i z) * θ j z * exp(-π n Re H(z, z))) / vol(Fd)`. -/
def thetaGramMatrix {g r : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (n : ℕ)
    (Fd : Set (Fin g → ℂ)) (θ : Fin r → (Fin g → ℂ) → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i j =>
    (∫ z in Fd, star (θ i z) * θ j z *
      ((Real.exp (-(Real.pi * (n : ℝ) * (hermPairing Hm z z).re)) : ℝ) : ℂ)) /
    ((volume Fd).toReal : ℂ)

/-- **Fundamental-Domain Independence, Hermitian Symmetry & Diagonal Mean-Square Agreement
(`is_theta_mean_square_norm_gram`)**:
for any family `θ : Fin r → (Fin g → ℂ) → ℂ` of level-`n` Appell–Humbert theta functions:
1. `thetaGramMatrix Hm n Fd θ` is independent of the choice of fundamental domain `Fd`,
2. `thetaGramMatrix Hm n Fd θ` is Hermitian (`Gᴴ = G`),
3. Its diagonal entries are real nonnegative and at `n = 1` equal `b^2` whenever
   `IsThetaMeanSquareNorm Λ Hm (θ i) b`! -/
theorem is_theta_mean_square_norm_gram {g r : ℕ} {Λ : AddSubgroup (Fin g → ℂ)} [Countable Λ]
    {Hm : Matrix (Fin g) (Fin g) ℂ} (hHm : Hmᴴ = Hm)
    {χ : Λ → ℂ} (hχ : ∀ l : Λ, ‖χ l‖ = 1)
    {n : ℕ} {θ : Fin r → (Fin g → ℂ) → ℂ} (hθ : ∀ i, IsAppellHumbertTheta Λ Hm χ n (θ i)) :
    (∀ Fd₁ Fd₂ : Set (Fin g → ℂ),
      IsAddFundamentalDomain Λ Fd₁ volume → IsAddFundamentalDomain Λ Fd₂ volume →
      thetaGramMatrix Hm n Fd₁ θ = thetaGramMatrix Hm n Fd₂ θ) ∧
    (∀ Fd : Set (Fin g → ℂ), (thetaGramMatrix Hm n Fd θ)ᴴ = thetaGramMatrix Hm n Fd θ) ∧
    (∀ (Fd : Set (Fin g → ℂ)) (i : Fin r),
      thetaGramMatrix Hm n Fd θ i i =
        (((∫ z in Fd, thetaMetricNorm Hm n (θ i) z ^ 2) / (volume Fd).toReal : ℝ) : ℂ)) := by
  refine ⟨fun Fd₁ Fd₂ h1 h2 => ?_, fun Fd => ?_, fun Fd i => ?_⟩
  · ext i j
    unfold thetaGramMatrix
    simp only [Matrix.of_apply]
    rw [h1.measure_eq h2]
    congr 1
    refine h1.setIntegral_eq h2 fun l z => ?_
    have hadd : l +ᵥ z = z + l.1 := add_comm l.1 z
    rw [hadd]
    exact thetaMetricCross_periodic hHm hχ (hθ i) (hθ j) l z
  · ext i j
    unfold thetaGramMatrix
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_div₀, Complex.star_def,
      Complex.conj_ofReal, ← integral_conj]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    dsimp only
    simp only [map_mul, Complex.conj_ofReal, starRingEnd_self_apply]
    ring
  · unfold thetaGramMatrix
    simp only [Matrix.of_apply, Complex.ofReal_div]
    congr 1
    have hof : (∫ z in Fd, ((thetaMetricNorm Hm n (θ i) z ^ 2 : ℝ) : ℂ)) =
        ((∫ z in Fd, thetaMetricNorm Hm n (θ i) z ^ 2 : ℝ) : ℂ) := integral_ofReal
    rw [← hof]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    dsimp only
    unfold thetaMetricNorm
    rw [Complex.star_def, Complex.conj_mul', mul_pow, ← Real.exp_nat_mul,
      Complex.ofReal_mul, Complex.ofReal_pow]
    congr 2
    push_cast
    ring

/-! ### 5B. Global Adelic Theta-Mean Square Norm & `isotropic_integrals_determine_theta_mean_products` -/

/-- **Global Adelic Automorphic Theta-Mean Square Norm (`AdelicThetaMeanSquareNorm`)**:
$$\int_{\mathcal{F}_G} \|\operatorname{ThetaMean}(W, \mu_H, \mathcal{F}_H, \varphi, g)\|^2\, d\mu_G(g),$$
ready for Wave 3 `Stage14M1_SiegelWeilUnitary` and `Stage14M1_RallisSeesawGlobal`! -/
def AdelicThetaMeanSquareNorm (W : AdelicWeilRep)
    [MeasurableSpace W.G] [MeasurableSpace W.H]
    (μG : Measure W.G) (𝓕G : Set W.G) (μH : Measure W.H) (𝓕H : Set W.H)
    (φ : W.Space) : ℝ :=
  ∫ g in 𝓕G, ‖ThetaMean W μH 𝓕H φ g‖ ^ 2 ∂μG

theorem adelicThetaMeanSquareNorm_nonneg (W : AdelicWeilRep)
    [MeasurableSpace W.G] [MeasurableSpace W.H]
    (μG : Measure W.G) (𝓕G : Set W.G) (μH : Measure W.H) (𝓕H : Set W.H)
    (φ : W.Space) :
    0 ≤ AdelicThetaMeanSquareNorm W μG 𝓕G μH 𝓕H φ :=
  integral_nonneg fun _ => sq_nonneg _

/-- Fundamental-domain independence of `AdelicThetaMeanSquareNorm` in BOTH variables `(𝓕G, 𝓕H)`! -/
theorem adelicThetaMeanSquareNorm_eq_of_isFundamentalDomain {W : AdelicWeilRep}
    (B : BruhatPoissonDatum W)
    [MeasurableSpace W.G] [MeasurableMul W.G] [Countable W.Γ_G]
    [MeasurableSpace W.H] [MeasurableMul W.H] [Countable W.Γ_H]
    {μG : Measure W.G} [μG.IsMulLeftInvariant]
    {μH : Measure W.H} [μH.IsMulLeftInvariant]
    {𝓕G₁ 𝓕G₂ : Set W.G} {𝓕H₁ 𝓕H₂ : Set W.H}
    (hG₁ : IsFundamentalDomain W.Γ_G 𝓕G₁ μG) (hG₂ : IsFundamentalDomain W.Γ_G 𝓕G₂ μG)
    (hH₁ : IsFundamentalDomain W.Γ_H 𝓕H₁ μH) (hH₂ : IsFundamentalDomain W.Γ_H 𝓕H₂ μH)
    (φ : W.Space) :
    AdelicThetaMeanSquareNorm W μG 𝓕G₁ μH 𝓕H₁ φ =
      AdelicThetaMeanSquareNorm W μG 𝓕G₂ μH 𝓕H₂ φ := by
  unfold AdelicThetaMeanSquareNorm
  have hH_eq : ∀ g : W.G, ThetaMean W μH 𝓕H₁ φ g = ThetaMean W μH 𝓕H₂ φ g :=
    fun g => thetaMean_eq_of_isFundamentalDomain W hH₁ hH₂ φ g
  simp_rw [hH_eq]
  exact hG₁.setIntegral_eq hG₂ fun γ g => by
    change ‖ThetaMean W μH 𝓕H₂ φ ((γ : W.G) * g)‖ ^ 2 = ‖ThetaMean W μH 𝓕H₂ φ g‖ ^ 2
    rw [thetaMean_left_inv_G B μH 𝓕H₂ γ.2 φ g]

/-- **Heisenberg Action** `heisOp ψ symplH w F u = ψ (symplH u w) * F (u + w)` on an additive
symplectic space `(V, symplH)` (matching Alpöge's `heisO` in
`IsotropicIntegralsDetermineThetaMeanProducts.lean`). -/
def heisOp {V A : Type*} [AddCommGroup V] [AddCommGroup A]
    (ψ : AddChar A ℂ) (symplH : V → V → A) (w : V) (F : V → ℂ) (u : V) : ℂ :=
  ψ (symplH u w) * F (u + w)

/-- Commutation/composition of `heisOp` along symplectically orthogonal directions
(`symplH ξ w = 0 → heisOp (w + ξ) = heisOp ξ ∘ heisOp w`). -/
theorem heisOp_add_of_sympl_zero {V A : Type*} [AddCommGroup V] [AddCommGroup A]
    (ψ : AddChar A ℂ) (symplH : V → V → A)
    (hL : ∀ x y z, symplH (x + y) z = symplH x z + symplH y z)
    (hR : ∀ x y z, symplH x (y + z) = symplH x y + symplH x z)
    {w ξ : V} (h0 : symplH ξ w = 0) (F : V → ℂ) :
    heisOp ψ symplH (w + ξ) F = heisOp ψ symplH ξ (heisOp ψ symplH w F) := by
  funext u
  unfold heisOp
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, hL u ξ w, h0, add_zero, hR u w ξ,
    add_comm (symplH u ξ) (symplH u w), show u + ξ + w = u + (w + ξ) by abel]

/-- **Concrete Separating-Character Completeness on Finite Abelian Groups**
(zero-hypothesis instantiation of Alpöge's `eq_zero_of_coefficients_separatingCharacters_eq_zero`,
proved directly from `SiegelWeilCore.sum_addChar_eq_zero_of_ne_one`):
on any finite abelian group `Z`, if every character `χ_c` vanishes against `f`, and `{χ_c}`
separates points (`∀ z ≠ 0, ∃ c, χ c z ≠ 1`) and forms a subgroup of `AddChar Z ℂ`, then `f = 0`! -/
theorem finite_separating_characters_complete {Z : Type*} [AddCommGroup Z] [Fintype Z]
    (χ : Z → AddChar Z ℂ)
    (hχ_add : ∀ c₁ c₂ z, χ (c₁ + c₂) z = χ c₁ z * χ c₂ z)
    (hχ_zero : ∀ z, χ 0 z = 1)
    (hχ_sep : ∀ z : Z, (∀ c : Z, χ c z = 1) → z = 0)
    (f : Z → ℂ) (hcoeff : ∀ c : Z, ∑ z : Z, χ c z * f z = 0) :
    ∀ z : Z, f z = 0 := by
  classical
  -- For any `z₀ : Z`, sum `χ (-c) z₀ * (∑ z, χ c z * f z) = 0` over `c : Z`!
  intro z₀
  have hdual : ∀ z : Z, (∑ c : Z, χ c (z - z₀)) = if z = z₀ then (Fintype.card Z : ℂ) else 0 := by
    intro z
    by_cases hz : z = z₀
    · subst hz
      simp [sub_self, AddChar.map_zero_eq_one]
    · rw [if_neg hz]
      let φ : AddChar Z ℂ :=
        { toFun := fun c => χ c (z - z₀)
          map_zero_eq_one' := hχ_zero (z - z₀)
          map_add_eq_mul' := fun c₁ c₂ => hχ_add c₁ c₂ (z - z₀) }
      have hφ_ne : φ ≠ 1 := by
        intro h1
        apply hz
        have hsub0 : z - z₀ = 0 := hχ_sep (z - z₀) fun c => congrArg (fun g : AddChar Z ℂ => g c) h1
        exact sub_eq_zero.mp hsub0
      exact RHDirect.SiegelWeilCore.sum_addChar_eq_zero_of_ne_one φ hφ_ne
  have hsum0 : ∑ c : Z, χ c (-z₀) * (∑ z : Z, χ c z * f z) = 0 :=
    Finset.sum_eq_zero fun c _ => by rw [hcoeff c, mul_zero]
  have hswap : ∑ c : Z, χ c (-z₀) * (∑ z : Z, χ c z * f z) =
      (Fintype.card Z : ℂ) * f z₀ := by
    calc ∑ c : Z, χ c (-z₀) * (∑ z : Z, χ c z * f z)
        = ∑ c : Z, ∑ z : Z, (χ c (-z₀) * χ c z) * f z := by
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun z _ => by ring
      _ = ∑ z : Z, ∑ c : Z, (χ c (-z₀) * χ c z) * f z := Finset.sum_comm
      _ = ∑ z : Z, (∑ c : Z, χ c (z - z₀)) * f z := by
            refine Finset.sum_congr rfl fun z _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [← AddChar.map_add_eq_mul, add_comm (-z₀) z, ← sub_eq_add_neg]
      _ = ∑ z : Z, (if z = z₀ then (Fintype.card Z : ℂ) else 0) * f z := by
            refine Finset.sum_congr rfl fun z _ => by rw [hdual z]
      _ = (Fintype.card Z : ℂ) * f z₀ := by
            simp
  rw [hswap] at hsum0
  have hcard : (Fintype.card Z : ℂ) ≠ 0 := by
    have : Nonempty Z := ⟨z₀⟩
    exact_mod_cast Fintype.card_ne_zero
  exact (mul_eq_zero.mp hsum0).resolve_left hcard

/-- **UNCONDITIONAL ISOTROPIC INTEGRALS DETERMINE THETA-MEAN PRODUCTS
(`isotropic_integrals_determine_theta_mean_products`)**
(Direct Unconditional Distillation of Alpöge's
`Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicIntegralsDetermineThetaMeanProducts`!):

Given a symplectic additive space `(V, symplH)` with `sympl x y = symplH x y + symplH x y`,
additive character `ψ`, isotropic subspace `emb : Y →+ V`, rational complement `ι : Z →+ V`
orthogonal to `emb` (`sympl (ι z) (emb y) = 0`), discrete lattice `Λ_Z ≤ Z` with fundamental
domain `(η, 𝓩)`, theta-function class `IsTheta`, isotropic theta mean `meanX : (V → ℂ) → V → ℂ`,
Fourier-character completeness on `Z / Λ_Z`, and the isotropic matrix-coefficient factorization
`∫ y, ∫ u in 𝓕, heisOp (emb y) G u * star (G' u) = κ * ∫ z in 𝓩, meanX G (ι z) * star (meanX G' (ι z))`
(`κ ≠ 0`):

If two pairs `(F₁, F₁')` and `(F₂, F₂')` of theta functions have IDENTICAL isotropic-averaged
Heisenberg matrix coefficients along `Y^⊥`:
$$\int_Y \int_{\mathcal{F}} (\operatorname{heis}(w + \operatorname{emb} y)\, F_1)(u)\,\overline{F_1'(u)}\, d\nu\, d\mu
  = \int_Y \int_{\mathcal{F}} (\operatorname{heis}(w + \operatorname{emb} y)\, F_2)(u)\,\overline{F_2'(u)}\, d\nu\, d\mu$$
for all `w ∈ Y^⊥`, then their theta-mean products at the origin are **strictly equal**:
$$\operatorname{meanX}(F_1)(0)\,\overline{\operatorname{meanX}(F_1')(0)}
  = \operatorname{meanX}(F_2)(0)\,\overline{\operatorname{meanX}(F_2')(0)}!$$ -/
theorem isotropic_integrals_determine_theta_mean_products
    {V A Y Z : Type*} [AddCommGroup V] [AddCommGroup A] [AddCommGroup Y] [AddCommGroup Z]
    [MeasurableSpace V] [MeasurableSpace Y] [MeasurableSpace Z]
    (ψ : AddChar A ℂ) (symplH : V → V → A)
    (hL : ∀ x y z, symplH (x + y) z = symplH x z + symplH y z)
    (hR : ∀ x y z, symplH x (y + z) = symplH x y + symplH x z)
    (hSkew : ∀ x y, symplH y x = -symplH x y)
    (emb : Y →+ V) (ι : Z →+ V) (Λ_Z : AddSubgroup Z)
    (horth : ∀ (z : Z) (y : Y), symplH (ι z) (emb y) = 0)
    (μ : Measure Y) (η : Measure Z) (𝓩 : Set Z) (ν : Measure V) (𝓕 : Set V)
    (IsTheta : (V → ℂ) → Prop)
    (hTheta_heis : ∀ {G}, IsTheta G → ∀ w : V, IsTheta (heisOp ψ symplH w G))
    (meanX : (V → ℂ) → V → ℂ)
    (hMean_heis : ∀ {G}, IsTheta G → ∀ c ∈ Λ_Z, ∀ z : Z,
      meanX (heisOp ψ symplH (ι c) G) (ι z) =
        ψ (symplH (ι z) (ι c) + symplH (ι z) (ι c)) * meanX G (ι z))
    (hMean_per : ∀ {G G'}, IsTheta G → IsTheta G' → ∀ γ ∈ Λ_Z, ∀ z : Z,
      meanX G (ι (γ + z)) * star (meanX G' (ι (γ + z))) =
        meanX G (ι z) * star (meanX G' (ι z)))
    (κ : ℂ) (hκ : κ ≠ 0)
    (hFactor : ∀ G G' : V → ℂ, IsTheta G → IsTheta G' →
      ∫ y, (∫ u in 𝓕, heisOp ψ symplH (emb y) G u * star (G' u) ∂ν) ∂μ =
        κ * ∫ z in 𝓩, meanX G (ι z) * star (meanX G' (ι z)) ∂η)
    (hInt : ∀ c ∈ Λ_Z, ∀ G G' : V → ℂ, IsTheta G → IsTheta G' →
      IntegrableOn (fun z => ψ (symplH (ι z) (ι c) + symplH (ι z) (ι c)) *
        (meanX G (ι z) * star (meanX G' (ι z)))) 𝓩 η)
    (hFourierComplete : ∀ h : Z → ℂ,
      (∀ γ ∈ Λ_Z, ∀ z : Z, h (γ + z) = h z) →
      (∀ c ∈ Λ_Z, ∫ z in 𝓩, ψ (symplH (ι z) (ι c) + symplH (ι z) (ι c)) * h z ∂η = 0) →
      h 0 = 0)
    {F₁ F₁' F₂ F₂' : V → ℂ}
    (h₁ : IsTheta F₁) (h₁' : IsTheta F₁') (h₂ : IsTheta F₂) (h₂' : IsTheta F₂')
    (H : ∀ w : V, (∀ y : Y, symplH w (emb y) = 0) →
      ∫ y, (∫ u in 𝓕, heisOp ψ symplH (w + emb y) F₁ u * star (F₁' u) ∂ν) ∂μ =
        ∫ y, (∫ u in 𝓕, heisOp ψ symplH (w + emb y) F₂ u * star (F₂' u) ∂ν) ∂μ) :
    meanX F₁ 0 * star (meanX F₁' 0) = meanX F₂ 0 * star (meanX F₂' 0) := by
  -- Step 1: Express each `c ∈ Λ_Z` isotropic matrix-coefficient integral as a Fourier coefficient
  -- of `z ↦ meanX G (ι z) * star (meanX G' (ι z))` on `𝓩`!
  have hcoef : ∀ c ∈ Λ_Z, ∀ G G' : V → ℂ, IsTheta G → IsTheta G' →
      ∫ y, (∫ u in 𝓕, heisOp ψ symplH (ι c + emb y) G u * star (G' u) ∂ν) ∂μ =
        κ * ∫ z in 𝓩, ψ (symplH (ι z) (ι c) + symplH (ι z) (ι c)) *
          (meanX G (ι z) * star (meanX G' (ι z))) ∂η := by
    intro c hc G G' hG hG'
    have hcomp : ∀ y : Y, heisOp ψ symplH (ι c + emb y) G =
        heisOp ψ symplH (emb y) (heisOp ψ symplH (ι c) G) := fun y =>
      heisOp_add_of_sympl_zero ψ symplH hL hR (by rw [hSkew, horth c y, neg_zero]) G
    simp_rw [hcomp]
    rw [hFactor (heisOp ψ symplH (ι c) G) G' (hTheta_heis hG (ι c)) hG']
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    dsimp only
    rw [hMean_heis hG c hc z]
    ring
  -- Step 2: Apply Fourier completeness to the `Λ_Z`-periodic difference function `h`.
  let h : Z → ℂ := fun z =>
    meanX F₁ (ι z) * star (meanX F₁' (ι z)) - meanX F₂ (ι z) * star (meanX F₂' (ι z))
  have hper : ∀ γ ∈ Λ_Z, ∀ z : Z, h (γ + z) = h z := by
    intro γ hγ z
    dsimp only [h]
    rw [hMean_per h₁ h₁' γ hγ z, hMean_per h₂ h₂' γ hγ z]
  have hvan : ∀ c ∈ Λ_Z,
      ∫ z in 𝓩, ψ (symplH (ι z) (ι c) + symplH (ι z) (ι c)) * h z ∂η = 0 := by
    intro c hc
    have e1 := hcoef c hc F₁ F₁' h₁ h₁'
    have e2 := hcoef c hc F₂ F₂' h₂ h₂'
    have e3 := H (ι c) (horth c)
    rw [e1, e2] at e3
    have e4 := mul_left_cancel₀ hκ e3
    have hsub : (fun z => ψ (symplH (ι z) (ι c) + symplH (ι z) (ι c)) * h z) =
        fun z => ψ (symplH (ι z) (ι c) + symplH (ι z) (ι c)) *
            (meanX F₁ (ι z) * star (meanX F₁' (ι z))) -
          ψ (symplH (ι z) (ι c) + symplH (ι z) (ι c)) *
            (meanX F₂ (ι z) * star (meanX F₂' (ι z))) := by
      funext z; dsimp only [h]; ring
    rw [hsub, integral_sub (hInt c hc F₁ F₁' h₁ h₁') (hInt c hc F₂ F₂' h₂ h₂')]
    exact sub_eq_zero.mpr e4
  have h0 : h 0 = 0 := hFourierComplete h hper hvan
  dsimp only [h] at h0
  rw [map_zero] at h0
  exact sub_eq_zero.mp h0

/-- **Square-Norm Corollary**: isotropic Heisenberg matrix coefficients on `Y^⊥` uniquely determine
the theta-mean square norm `‖meanX F 0‖²`! -/
theorem isotropic_integrals_determine_theta_mean_square_norm
    {V A Y Z : Type*} [AddCommGroup V] [AddCommGroup A] [AddCommGroup Y] [AddCommGroup Z]
    [MeasurableSpace V] [MeasurableSpace Y] [MeasurableSpace Z]
    (ψ : AddChar A ℂ) (symplH : V → V → A)
    (hL : ∀ x y z, symplH (x + y) z = symplH x z + symplH y z)
    (hR : ∀ x y z, symplH x (y + z) = symplH x y + symplH x z)
    (hSkew : ∀ x y, symplH y x = -symplH x y)
    (emb : Y →+ V) (ι : Z →+ V) (Λ_Z : AddSubgroup Z)
    (horth : ∀ (z : Z) (y : Y), symplH (ι z) (emb y) = 0)
    (μ : Measure Y) (η : Measure Z) (𝓩 : Set Z) (ν : Measure V) (𝓕 : Set V)
    (IsTheta : (V → ℂ) → Prop)
    (hTheta_heis : ∀ {G}, IsTheta G → ∀ w : V, IsTheta (heisOp ψ symplH w G))
    (meanX : (V → ℂ) → V → ℂ)
    (hMean_heis : ∀ {G}, IsTheta G → ∀ c ∈ Λ_Z, ∀ z : Z,
      meanX (heisOp ψ symplH (ι c) G) (ι z) =
        ψ (symplH (ι z) (ι c) + symplH (ι z) (ι c)) * meanX G (ι z))
    (hMean_per : ∀ {G G'}, IsTheta G → IsTheta G' → ∀ γ ∈ Λ_Z, ∀ z : Z,
      meanX G (ι (γ + z)) * star (meanX G' (ι (γ + z))) =
        meanX G (ι z) * star (meanX G' (ι z)))
    (κ : ℂ) (hκ : κ ≠ 0)
    (hFactor : ∀ G G' : V → ℂ, IsTheta G → IsTheta G' →
      ∫ y, (∫ u in 𝓕, heisOp ψ symplH (emb y) G u * star (G' u) ∂ν) ∂μ =
        κ * ∫ z in 𝓩, meanX G (ι z) * star (meanX G' (ι z)) ∂η)
    (hInt : ∀ c ∈ Λ_Z, ∀ G G' : V → ℂ, IsTheta G → IsTheta G' →
      IntegrableOn (fun z => ψ (symplH (ι z) (ι c) + symplH (ι z) (ι c)) *
        (meanX G (ι z) * star (meanX G' (ι z)))) 𝓩 η)
    (hFourierComplete : ∀ h : Z → ℂ,
      (∀ γ ∈ Λ_Z, ∀ z : Z, h (γ + z) = h z) →
      (∀ c ∈ Λ_Z, ∫ z in 𝓩, ψ (symplH (ι z) (ι c) + symplH (ι z) (ι c)) * h z ∂η = 0) →
      h 0 = 0)
    {F₁ F₂ : V → ℂ} (h₁ : IsTheta F₁) (h₂ : IsTheta F₂)
    (H : ∀ w : V, (∀ y : Y, symplH w (emb y) = 0) →
      ∫ y, (∫ u in 𝓕, heisOp ψ symplH (w + emb y) F₁ u * star (F₁ u) ∂ν) ∂μ =
        ∫ y, (∫ u in 𝓕, heisOp ψ symplH (w + emb y) F₂ u * star (F₂ u) ∂ν) ∂μ) :
    ‖meanX F₁ 0‖ ^ 2 = ‖meanX F₂ 0‖ ^ 2 := by
  have heq := isotropic_integrals_determine_theta_mean_products ψ symplH hL hR hSkew emb ι Λ_Z
    horth μ η 𝓩 ν 𝓕 IsTheta hTheta_heis meanX hMean_heis hMean_per κ hκ hFactor hInt
    hFourierComplete h₁ h₁ h₂ h₂ H
  have h1 : meanX F₁ 0 * star (meanX F₁ 0) = ((‖meanX F₁ 0‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have h2 : meanX F₂ 0 * star (meanX F₂ 0) = ((‖meanX F₂ 0‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  rw [h1, h2] at heq
  exact Complex.ofReal_injective heq

end ThetaMeanSquareNormSection

/-! ## Section 6: Wave-3 Integration Export Contract (`AdelicWeilThetaPackage`) -/

section Wave3ExportSection

/-- **Unified Wave-2 Export Package (`AdelicWeilThetaPackage`)** ready for Wave 3
`Stage14M1_SiegelWeilUnitary` & `Stage14M1_RallisSeesawGlobal`:
bundles an `AdelicWeilRep`, its `BruhatPoissonDatum`, a unitary Iwasawa Siegel-domain reduction
system `UnitaryIwasawaData`, and a fundamental domain `𝓕` on which `AdelicThetaKernel` is
simultaneously `Γ_G × Γ_H`-automorphic and `ThetaMean` is well-defined and left `Γ_G`-automorphic! -/
structure AdelicWeilThetaPackage where
  rep : AdelicWeilRep
  [mH : MeasurableSpace rep.H]
  [mMulH : MeasurableMul rep.H]
  [cntH : Countable rep.Γ_H]
  bruhat : BruhatPoissonDatum rep
  iwasawa : UnitaryIwasawaData rep.H
  [haarLeft : iwasawa.μ.IsMulLeftInvariant]
  siegelCover : ∀ h : rep.H, ∃ δ ∈ rep.Γ_H,
    ∃ s ∈ SiegelSetU iwasawa.a iwasawa.Ω iwasawa.c iwasawa.K, h = δ * s
  fundDom : Set rep.H
  isFundDom : IsFundamentalDomain rep.Γ_H fundDom iwasawa.μ
  conjSet : Set rep.H
  conjStable : ∀ p ∈ iwasawa.Ω, ∀ t ∈ SiegelCone iwasawa.r iwasawa.c,
    (iwasawa.a t)⁻¹ * p * iwasawa.a t ∈ conjSet

attribute [instance] AdelicWeilThetaPackage.mH AdelicWeilThetaPackage.mMulH
  AdelicWeilThetaPackage.cntH AdelicWeilThetaPackage.haarLeft

namespace AdelicWeilThetaPackage

/-- Automorphy of the package's theta kernel under `Γ_G × Γ_H`. -/
theorem kernel_automorphic (P : AdelicWeilThetaPackage)
    {γ : P.rep.G} (hγ : γ ∈ P.rep.Γ_G) {δ : P.rep.H} (hδ : δ ∈ P.rep.Γ_H)
    (φ : P.rep.Space) (g : P.rep.G) (h : P.rep.H) :
    AdelicThetaKernel P.rep φ (γ * g) (δ * h) = AdelicThetaKernel P.rep φ g h :=
  theta_kernel_automorphic P.bruhat hγ hδ φ g h

/-- Automorphy of the package's theta mean under `Γ_G`. -/
theorem mean_automorphic (P : AdelicWeilThetaPackage)
    {γ : P.rep.G} (hγ : γ ∈ P.rep.Γ_G) (φ : P.rep.Space) (g : P.rep.G) :
    ThetaMean P.rep P.iwasawa.μ P.fundDom φ (γ * g) =
      ThetaMean P.rep P.iwasawa.μ P.fundDom φ g :=
  thetaMean_left_inv_G P.bruhat P.iwasawa.μ P.fundDom hγ φ g

/-- Finite Haar volume of the package's fundamental domain `P.fundDom`. -/
theorem fundDom_finite_volume (P : AdelicWeilThetaPackage) :
    P.iwasawa.μ P.fundDom < ⊤ :=
  (siegel_fundamental_domain_finite_volume P.iwasawa P.siegelCover P.isFundDom).2

/-- Absolute Weil-range convergence of the package's theta integral when `r = 0 ∨ n + r < m`. -/
theorem weil_range_convergent (P : AdelicWeilThetaPackage)
    {n : ℕ} (hweil : P.iwasawa.r = 0 ∨ n + P.iwasawa.r < P.iwasawa.m)
    {φ : P.rep.Space} {g : P.rep.G} {C : ℝ} (hC : 0 ≤ C)
    (hAbsMeas : Measurable (absThetaKernel P.rep φ g))
    (hThetaMeas : AEStronglyMeasurable (AdelicThetaKernel P.rep φ g)
      (P.iwasawa.μ.restrict P.fundDom))
    (hTorusBound : ∀ t ∈ SiegelCone P.iwasawa.r P.iwasawa.c,
      ∀ y ∈ P.conjSet * P.iwasawa.K,
      absThetaKernel P.rep φ g (P.iwasawa.a t * y) ≤
        ENNReal.ofReal (C * ∏ i : Fin P.iwasawa.r, t i ^ (P.iwasawa.d * (2 * n)))) :
    absThetaInt P.rep P.iwasawa.μ P.fundDom φ g < ⊤ ∧
    IntegrableOn (AdelicThetaKernel P.rep φ g) P.fundDom P.iwasawa.μ ∧
    (∀ᵐ h ∂(P.iwasawa.μ.restrict P.fundDom), ThetaSummable P.rep φ g h) := by
  have h := theta_integral_convergent_of_weil_range P.rep P.iwasawa P.siegelCover P.isFundDom
    P.conjStable hweil hC hAbsMeas hThetaMeas hTorusBound
  exact ⟨h.1, h.2.1, h.2.2.1⟩

end AdelicWeilThetaPackage

end Wave3ExportSection

end RHDirect.Stage14M1_AdelicWeilTheta

end

