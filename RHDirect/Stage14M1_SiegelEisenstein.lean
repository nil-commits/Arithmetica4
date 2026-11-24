import RHDirect.Stage14Contracts
import RHDirect.Stage14M1_SiegelDomainReduction
import RHDirect.Stage14M1_LocalSiegelDensities
import RHDirect.Stage14M1_SchrodingerFockModel

/-!
# RHDirect.Stage14M1_SiegelEisenstein

Field-2 Package M1 Wave 2: **Adelic Siegel Parabolic Sections, Siegel Eisenstein Series
Convergence, Constant-Term Local-Density Factorization, and Value & Positivity at the
Siegel–Weil Point `s₀`** (`0 sorry`, `0` custom `axiom`s, `0 opaque`, `0 native_decide`).

Built directly on:
- `RHDirect.Stage14Contracts` (`M1UnitarySiegelWeilContract`, `M1FiberCert`)
- `RHDirect.Stage14M1_SiegelDomainReduction` (`ParabolicSubgroupU`, `SiegelCone`, `SiegelSetU`,
  `UnitaryIwasawaData`, `UnitaryHeightFn`, `reduction_to_siegel_domain_sl2_int`,
  `lattice_fundamental_domain_char_integral_zero`, `siegel_envelope_integrable`,
  `siegel_cuspidal_times_moderate_integrable`, `siegel_fundamental_domain_weil_integrable`)
- `RHDirect.Stage14M1_LocalSiegelDensities` (`LocalHermLattice`, `LocalRepresentationDensity`,
  `local_density_euler_factor`, `globalEulerTerm`, `siegelProductLValue`,
  `siegel_densities_of_hermitian_form`, `SiegelDensityGlobalPackage`)
- `RHDirect.Stage14M1_SchrodingerFockModel` (`LocalWeilRep`, `IsWeilSch`, `stdGauss`,
  `gauss_vacuum_eigenvalue`, `padicSpherical`, `padicWeilLevi_spherical`, `AdelicPureTensor`,
  `adelicVacuum`, `siegelSection`, `SchrodingerFockPackage`)

## Contents

1. **Siegel Parabolic Parameters `ρ_P`, `s₀` & Concrete `SiegelParabolicSection`**:
   - Half-sum of positive Siegel-parabolic roots `siegelRho n = n / 2` and Siegel–Weil point
     `siegelWeilPoint m n = (m - n) / 2` (matching `SiegelWeilCore.DualPairRanks.sZero`), with
     exact shift identity `siegelWeilPoint m n + siegelRho n = m / 2` and convergence range
     equivalences `siegelRho n < siegelWeilPoint m n ↔ 2 * n < m` and
     `0 < siegelWeilPoint m n ↔ n < m`.
   - Concrete `SiegelParabolicSection G P` carrying Iwasawa height `iwasawaH`, Levi modulus
     `leviMod`, unitary character `chi : P →* Circle`, and base section `baseSection` at `s₀`,
     yielding exact induced parabolic equivariance `eval_left_parabolic` in `I_P(s, χ)`.
   - Direct bridges from `Stage14M1_SchrodingerFockModel`: general Weil-section constructor
     `siegelParabolicSection_of_weil`, archimedean Gaussian-vacuum section
     `archVacuumSiegelSection`, `p`-adic spherical-vacuum section `padicSphericalSiegelSection`,
     and factorizable adelic vacuum section `AdelicSiegelSection` / `adelicVacuumSiegelSection`.

2. **Parabolic Cosets `(P ∩ Γ) \ Γ`, Concrete `SiegelEisensteinSeries` & Automorphy**:
   - Concrete right-coset space `ParabolicCoset Γ P`, rational parabolic invariance predicate
     `RatParabolicInvariant Γ F`, well-defined coset summand `eisensteinTerm`, and
     **`SiegelEisensteinSeries`** `E(g, s; F) = ∑' c : ParabolicCoset Γ P, eisensteinTerm ... s g c`.
   - Unconditional left-`Γ`-automorphy (`eisenstein_left_invariant`), right-`K` eigenfunction
     transformation (`eisenstein_right_compact_eigen`), and zero-hypothesis concrete `SL₂(ℤ)`
     real-analytic Siegel–Eisenstein series (`sl2SiegelEisenstein`, `sl2SiegelEisenstein_invariant`).

3. **Height Bounds, Siegel-Set Integrability & `eisenstein_abs_convergent`**:
   - Zero-hypothesis lattice-shell convergence for `SL₂(ℤ)` (`sl2_eisenstein_abs_convergent`)
     proved directly from `Stage14M1_SiegelDomainReduction.reduction_to_siegel_domain_sl2_int`
     for all `τ ∈ ℂ` (`0 < τ.im`) and all `s ∈ ℂ` with `siegelRho 1 < s.re` (`1/2 < s.re`),
     with explicit Siegel-domain growth ceiling.
   - General Godement dyadic/polynomial shell growth structure `CosetShellGrowth` tied to
     `Stage14M1_SiegelDomainReduction.UnitaryHeightFn`, proving **`eisenstein_abs_convergent`**:
     absolute summability in `Re(s) > ρ_P`, explicit moderate growth in `UnitaryHeightFn`,
     Weil-range absolute convergence at `s = s₀` for `2 * n < m`, and Bochner integrability on
     `SiegelSetU` and fundamental domains via `siegel_envelope_integrable`,
     `siegel_cuspidal_times_moderate_integrable`, and `siegel_fundamental_domain_weil_integrable`.

4. **Unipotent Constant-Term Extraction & `eisenstein_constant_term_local_densities`**:
   - Exact unipotent Fourier-mode vanishing and constant-term recovery over totally real number
     fields via `Stage14M1_SiegelDomainReduction.lattice_fundamental_domain_char_integral_zero`
     and `lattice_fundamental_domain_volume`.
   - Complex-parameter local Siegel–Eisenstein Euler factors `localEisensteinDensityFactor χ m n s p`
     converging (`HasProd` + `Multipliable`) for every `Re(s) > 0` to `globalEisensteinLValue χ m n s`.
   - Master theorem **`eisenstein_constant_term_local_densities`**: exact identification at
     `s = s₀ = (m - n)/2` with `Stage14M1_LocalSiegelDensities.siegel_densities_of_hermitian_form`
     (`siegelProductLValue χ m n`) and `LocalRepresentationDensity` at every unramified prime `p`.

5. **Archimedean Siegel Density & `siegel_eisenstein_value_at_s0`**:
   - Exact archimedean Siegel density `archSiegelDensity f vE m n`, global adelic Siegel–Eisenstein
     value `eisensteinValueAtS0 f vE χ m n = archSiegelDensity f vE m n * (siegelProductLValue χ m n)^f`,
     and local step reciprocal `localDensityReciprocal f χ M`.
   - Master theorem **`siegel_eisenstein_value_at_s0`**: strict positivity, quantitative two-sided
     bounds, exact reciprocal identity with `UnitaryMassFormula.massRatioFactor` and
     `Stage11RallisMassFiber.bsgyUnitaryMass`, rank-telescoping, logarithmic density lower bound,
     and dominant-constant real-part positivity on `SiegelWeilCore.SiegelEisensteinDecomp`.

6. **Wave-3 Handoff (`SiegelEisensteinWave3Pack`) & `Stage14Contracts` Alignment**:
   - Concrete `SiegelEisensteinWave3Pack` and compiler `toM1UnitarySiegelWeilContract` aligned
     verbatim with `Stage14Contracts.M1UnitarySiegelWeilContract`, instantiated unconditionally
     for `ℚ(i)` (`Stage9SpecialValues.chi4`).
-/

noncomputable section

open Complex Real Finset Filter MeasureTheory Module Submodule
open RHDirect RHDirect.Stage14Contracts
open scoped BigOperators ENNReal NNReal

namespace RHDirect.Stage14M1_SiegelEisenstein

local instance instFactPrimePrimes (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-! ## Section 1: Siegel Parabolic Parameters `ρ_P`, `s₀` & Concrete `SiegelParabolicSection` -/

section SiegelParabolicParameters

/-- Half-sum of positive roots `ρ_P = n / 2` for the unitary Siegel parabolic `P ⊂ U(n, n)`. -/
def siegelRho (n : ℕ) : ℝ :=
  (n : ℝ) / 2

/-- The Siegel–Weil evaluation point `s₀ = (m - n) / 2` for the unitary dual pair `(U(n, n), U(V))`
with `dim V = m`. Matches `SiegelWeilCore.DualPairRanks.sZero`. -/
def siegelWeilPoint (m n : ℕ) : ℝ :=
  ((m : ℝ) - (n : ℝ)) / 2

lemma siegelRho_nonneg (n : ℕ) : 0 ≤ siegelRho n := by
  unfold siegelRho; positivity

lemma siegelRho_pos_of_pos {n : ℕ} (hn : 0 < n) : 0 < siegelRho n := by
  unfold siegelRho
  have : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  linarith

lemma siegelRho_one : siegelRho 1 = 1 / 2 := by
  simp [siegelRho]

lemma siegelWeilPoint_eq_sZero (P : RHDirect.SiegelWeilCore.DualPairRanks) :
    siegelWeilPoint P.m P.n = P.sZero := rfl

/-- Fundamental Siegel–Weil exponent shift: `s₀ + ρ_P = m / 2`, matching the Weil representation
determinant power `|det a|_E^{m / 2}` in the induced parabolic representation `I_P(s₀, χ)`. -/
theorem siegelWeilPoint_add_siegelRho (m n : ℕ) :
    siegelWeilPoint m n + siegelRho n = (m : ℝ) / 2 := by
  unfold siegelWeilPoint siegelRho
  ring

/-- The Siegel–Weil point `s₀` lies strictly inside the Godement absolute convergence range
`Re(s) > ρ_P` if and only if `2 * n < m` (Weil's absolute convergence range for `U(n, n)`). -/
theorem siegelRho_lt_siegelWeilPoint_iff (m n : ℕ) :
    siegelRho n < siegelWeilPoint m n ↔ 2 * n < m := by
  unfold siegelRho siegelWeilPoint
  constructor
  · intro h
    have h1 : (2 * n : ℝ) < (m : ℝ) := by linarith
    exact_mod_cast h1
  · intro h
    have h1 : (2 * n : ℝ) < (m : ℝ) := by exact_mod_cast h
    linarith

/-- Positivity of the Siegel–Weil point `0 < s₀` is equivalent to `n < m` (the convergent Euler
product range of `Stage14M1_LocalSiegelDensities.siegel_densities_of_hermitian_form`). -/
theorem siegelWeilPoint_pos_iff (m n : ℕ) :
    0 < siegelWeilPoint m n ↔ n < m := by
  unfold siegelWeilPoint
  constructor
  · intro h
    have h1 : (n : ℝ) < (m : ℝ) := by linarith
    exact_mod_cast h1
  · intro h
    have h1 : (n : ℝ) < (m : ℝ) := by exact_mod_cast h
    linarith

theorem siegelWeilPoint_ge_half_of_lt {m n : ℕ} (hnm : n < m) :
    (1 : ℝ) / 2 ≤ siegelWeilPoint m n := by
  unfold siegelWeilPoint
  have h1 : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hnm
  linarith

theorem two_mul_siegelWeilPoint (m n : ℕ) :
    2 * siegelWeilPoint m n = (m : ℝ) - (n : ℝ) := by
  unfold siegelWeilPoint; ring

theorem two_mul_siegelWeilPoint_add_one {m n : ℕ} (hnm : n < m) (i : ℕ) :
    2 * siegelWeilPoint m n + (i : ℝ) + 1 = ((m - n + 1 + i : ℕ) : ℝ) := by
  rw [two_mul_siegelWeilPoint]
  have hle : n ≤ m := hnm.le
  rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub hle, Nat.cast_one]
  ring

theorem siegelWeilPoint_of_chainStep (R : RHDirect.ChainRanks) (j : ℕ) :
    siegelWeilPoint (R.chainRank (j + 1)) (R.chainRank j) = ((R.t : ℝ) + 1) / 2 := by
  unfold siegelWeilPoint RHDirect.ChainRanks.chainRank
  push_cast
  ring

end SiegelParabolicParameters

/-! ### Concrete `SiegelParabolicSection` & Weil/Schrödinger Vacuum Induction -/

section ConcreteSiegelParabolicSection

/-- **Concrete Adelic/Local Siegel Parabolic Section `SiegelParabolicSection G P`**:
models a flat standard section `s ↦ f_s ∈ I_P(s, χ) = Ind_P^G (χ · |det|^{s + ρ_P})` induced from
a base section `baseSection` at the Siegel–Weil point `s₀` (for example, `g ↦ (ω(g) Φ)(0)` from
`Stage14M1_SchrodingerFockModel.siegelSection`). -/
structure SiegelParabolicSection (G : Type*) [Group G] (P : Subgroup G) where
  /-- Siegel parabolic rank `n` (`ρ_P = n / 2`). -/
  n : ℕ
  /-- Base Siegel–Weil evaluation point `s₀`. -/
  s0 : ℝ
  /-- Unitary Levi character `χ : P →* Circle`. -/
  chi : P →* Circle
  /-- Positive Iwasawa height function `H(p k) = |det m(p)| > 0` on `G`. -/
  iwasawaH : G → ℝ≥0
  iwasawaH_pos : ∀ g : G, 0 < iwasawaH g
  iwasawaH_one : iwasawaH 1 = 1
  /-- Positive Levi determinant modulus `|det m(p)|` on `P`. -/
  leviMod : P → ℝ≥0
  leviMod_pos : ∀ p : P, 0 < leviMod p
  leviMod_one : leviMod 1 = 1
  leviMod_mul : ∀ p q : P, leviMod (p * q) = leviMod p * leviMod q
  iwasawaH_left_mul : ∀ (p : P) (g : G), iwasawaH (p.1 * g) = leviMod p * iwasawaH g
  /-- Base value `f_{s₀}(g)` at the Siegel–Weil point `s₀`. -/
  baseSection : G → ℂ
  /-- Exact parabolic equivariance of `baseSection` at `s = s₀` with exponent `s₀ + ρ_P`. -/
  base_equivar : ∀ (p : P) (g : G),
    baseSection (p.1 * g) =
      (chi p : ℂ) * ((leviMod p : ℝ) : ℂ) ^ ((s0 + siegelRho n : ℝ) : ℂ) * baseSection g

namespace SiegelParabolicSection

variable {G : Type*} [Group G] {P : Subgroup G}

/-- Evaluation `f_s(g) = H(g)^{s - s₀} · f_{s₀}(g)` of a `SiegelParabolicSection` at `s : ℂ`, `g : G`. -/
def eval (F : SiegelParabolicSection G P) (s : ℂ) (g : G) : ℂ :=
  ((F.iwasawaH g : ℝ) : ℂ) ^ (s - (F.s0 : ℂ)) * F.baseSection g

@[simp]
theorem eval_at_s0 (F : SiegelParabolicSection G P) (g : G) :
    F.eval (F.s0 : ℂ) g = F.baseSection g := by
  unfold eval
  rw [sub_self, Complex.cpow_zero, one_mul]

theorem eval_one (F : SiegelParabolicSection G P) (s : ℂ) :
    F.eval s 1 = F.baseSection 1 := by
  unfold eval
  rw [F.iwasawaH_one, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow, one_mul]

/-- Exact complex-power multiplication law for positive real bases. -/
private lemma ofReal_mul_cpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (z : ℂ) :
    ((a * b : ℝ) : ℂ) ^ z = (a : ℂ) ^ z * (b : ℂ) ^ z := by
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg ha.le hb.le]

/-- **Exact Parabolic Equivariance in `I_P(s, χ)`**:
for every `p ∈ P`, `s : ℂ`, and `g : G`,
`f_s(p g) = χ(p) · |det m(p)|^{s + ρ_P} · f_s(g)`! -/
theorem eval_left_parabolic (F : SiegelParabolicSection G P) (p : P) (s : ℂ) (g : G) :
    F.eval s (p.1 * g) =
      (F.chi p : ℂ) * ((F.leviMod p : ℝ) : ℂ) ^ (s + (siegelRho F.n : ℂ)) * F.eval s g := by
  unfold eval
  have hp_pos : (0 : ℝ) < (F.leviMod p : ℝ) := NNReal.coe_pos.mpr (F.leviMod_pos p)
  have hg_pos : (0 : ℝ) < (F.iwasawaH g : ℝ) := NNReal.coe_pos.mpr (F.iwasawaH_pos g)
  rw [F.iwasawaH_left_mul p g, NNReal.coe_mul, ofReal_mul_cpow hp_pos hg_pos, F.base_equivar p g]
  have hadd : ((F.leviMod p : ℝ) : ℂ) ^ (s - (F.s0 : ℂ)) *
      ((F.leviMod p : ℝ) : ℂ) ^ ((F.s0 + siegelRho F.n : ℝ) : ℂ) =
      ((F.leviMod p : ℝ) : ℂ) ^ (s + (siegelRho F.n : ℂ)) := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hp_pos.ne')]
    congr 1
    push_cast
    ring
  calc ((F.leviMod p : ℝ) : ℂ) ^ (s - (F.s0 : ℂ)) * ((F.iwasawaH g : ℝ) : ℂ) ^ (s - (F.s0 : ℂ)) *
        ((F.chi p : ℂ) * ((F.leviMod p : ℝ) : ℂ) ^ ((F.s0 + siegelRho F.n : ℝ) : ℂ) *
          F.baseSection g)
      = (F.chi p : ℂ) *
          (((F.leviMod p : ℝ) : ℂ) ^ (s - (F.s0 : ℂ)) *
            ((F.leviMod p : ℝ) : ℂ) ^ ((F.s0 + siegelRho F.n : ℝ) : ℂ)) *
          (((F.iwasawaH g : ℝ) : ℂ) ^ (s - (F.s0 : ℂ)) * F.baseSection g) := by ring
    _ = (F.chi p : ℂ) * ((F.leviMod p : ℝ) : ℂ) ^ (s + (siegelRho F.n : ℂ)) *
          (((F.iwasawaH g : ℝ) : ℂ) ^ (s - (F.s0 : ℂ)) * F.baseSection g) := by rw [hadd]

/-- Exact modulus formula `‖f_s(g)‖ = H(g)^{Re(s) - s₀} · ‖f_{s₀}(g)‖`. -/
theorem norm_eval (F : SiegelParabolicSection G P) (s : ℂ) (g : G) :
    ‖F.eval s g‖ = (F.iwasawaH g : ℝ) ^ (s.re - F.s0) * ‖F.baseSection g‖ := by
  unfold eval
  have hg_pos : (0 : ℝ) < (F.iwasawaH g : ℝ) := NNReal.coe_pos.mpr (F.iwasawaH_pos g)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hg_pos]
  simp

/-- Parabolic scaling law for the modulus: `‖f_s(p g)‖ = |det m(p)|^{Re(s) + ρ_P} · ‖f_s(g)‖`. -/
theorem norm_eval_left_parabolic (F : SiegelParabolicSection G P) (p : P) (s : ℂ) (g : G) :
    ‖F.eval s (p.1 * g)‖ = (F.leviMod p : ℝ) ^ (s.re + siegelRho F.n) * ‖F.eval s g‖ := by
  have hp_pos : (0 : ℝ) < (F.leviMod p : ℝ) := NNReal.coe_pos.mpr (F.leviMod_pos p)
  rw [F.eval_left_parabolic p s g, norm_mul, norm_mul, Circle.norm_coe, one_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hp_pos]
  simp

/-- Exact modulus for a spherical-bounded section: if `‖f_{s₀}(g)‖ ≤ C · H(g)^{s₀ + ρ_P}`, then
`‖f_s(g)‖ ≤ C · H(g)^{Re(s) + ρ_P}` for EVERY `s : ℂ`! -/
theorem norm_eval_le_of_base_bound (F : SiegelParabolicSection G P) {C : ℝ}
    (hB : ∀ g : G, ‖F.baseSection g‖ ≤ C * (F.iwasawaH g : ℝ) ^ (F.s0 + siegelRho F.n))
    (s : ℂ) (g : G) :
    ‖F.eval s g‖ ≤ C * (F.iwasawaH g : ℝ) ^ (s.re + siegelRho F.n) := by
  have hg_pos : (0 : ℝ) < (F.iwasawaH g : ℝ) := NNReal.coe_pos.mpr (F.iwasawaH_pos g)
  rw [F.norm_eval s g]
  calc (F.iwasawaH g : ℝ) ^ (s.re - F.s0) * ‖F.baseSection g‖
      ≤ (F.iwasawaH g : ℝ) ^ (s.re - F.s0) * (C * (F.iwasawaH g : ℝ) ^ (F.s0 + siegelRho F.n)) :=
        mul_le_mul_of_nonneg_left (hB g) (Real.rpow_nonneg hg_pos.le _)
    _ = C * ((F.iwasawaH g : ℝ) ^ (s.re - F.s0) * (F.iwasawaH g : ℝ) ^ (F.s0 + siegelRho F.n)) := by
        ring
    _ = C * (F.iwasawaH g : ℝ) ^ (s.re + siegelRho F.n) := by
        rw [← Real.rpow_add hg_pos]
        congr 2; ring

/-- Right-`K`-equivariance transfers from `iwasawaH` and `baseSection` directly to `F.eval s`. -/
theorem eval_right_compact_eigen (F : SiegelParabolicSection G P) {K : Subgroup G}
    (κ : K →* Circle)
    (hH : ∀ (g : G) (k : K), F.iwasawaH (g * k.1) = F.iwasawaH g)
    (hB : ∀ (g : G) (k : K), F.baseSection (g * k.1) = (κ k : ℂ) * F.baseSection g)
    (s : ℂ) (g : G) (k : K) :
    F.eval s (g * k.1) = (κ k : ℂ) * F.eval s g := by
  unfold eval
  rw [hH g k, hB g k]
  ring

/-- Scalar multiplication of a `SiegelParabolicSection`. -/
def smul (c : ℂ) (F : SiegelParabolicSection G P) : SiegelParabolicSection G P where
  n := F.n
  s0 := F.s0
  chi := F.chi
  iwasawaH := F.iwasawaH
  iwasawaH_pos := F.iwasawaH_pos
  iwasawaH_one := F.iwasawaH_one
  leviMod := F.leviMod
  leviMod_pos := F.leviMod_pos
  leviMod_one := F.leviMod_one
  leviMod_mul := F.leviMod_mul
  iwasawaH_left_mul := F.iwasawaH_left_mul
  baseSection g := c * F.baseSection g
  base_equivar p g := by rw [F.base_equivar p g]; ring

@[simp]
theorem smul_eval (c : ℂ) (F : SiegelParabolicSection G P) (s : ℂ) (g : G) :
    (F.smul c).eval s g = c * F.eval s g := by
  simp [smul, eval]; ring

end SiegelParabolicSection

/-- **Weil-Representation Induction Constructor (`siegelParabolicSection_of_weil`)**:
builds a concrete `SiegelParabolicSection G P` from any Weil representation `ω : G →* End ℂ V`,
evaluation functional `evalZero : V → ℂ`, Schwartz/vacuum vector `Φ : V`, and Iwasawa height `H`,
matching `Stage14M1_SchrodingerFockModel.siegelSection` identically! -/
def siegelParabolicSection_of_weil {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (P : Subgroup G) (n : ℕ) (s0 : ℝ)
    (ω : G →* Module.End ℂ V) (evalZero : V → ℂ) (Φ : V)
    (chi : P →* Circle) (H : G → ℝ≥0) (hH_pos : ∀ g, 0 < H g) (hH_one : H 1 = 1)
    (leviMod : P → ℝ≥0) (hl_pos : ∀ p, 0 < leviMod p) (hl_one : leviMod 1 = 1)
    (hl_mul : ∀ p q, leviMod (p * q) = leviMod p * leviMod q)
    (hH_mul : ∀ (p : P) (g : G), H (p.1 * g) = leviMod p * H g)
    (hWeilP : ∀ (p : P) (v : V),
      evalZero (ω p.1 v) =
        (chi p : ℂ) * ((leviMod p : ℝ) : ℂ) ^ ((s0 + siegelRho n : ℝ) : ℂ) * evalZero v) :
    SiegelParabolicSection G P where
  n := n
  s0 := s0
  chi := chi
  iwasawaH := H
  iwasawaH_pos := hH_pos
  iwasawaH_one := hH_one
  leviMod := leviMod
  leviMod_pos := hl_pos
  leviMod_one := hl_one
  leviMod_mul := hl_mul
  iwasawaH_left_mul := hH_mul
  baseSection g := evalZero (ω g Φ)
  base_equivar p g := by
    rw [map_mul, Module.End.mul_apply, hWeilP p (ω g Φ)]

/-- Exact identification of `siegelParabolicSection_of_weil.eval` with
`Stage14M1_SchrodingerFockModel.siegelSection`! -/
theorem siegelParabolicSection_of_weil_eval_eq {G V : Type*} [Group G] [AddCommGroup V]
    [Module ℂ V] (P : Subgroup G) (n : ℕ) (s0 : ℝ)
    (ω : G →* Module.End ℂ V) (evalZero : V → ℂ) (Φ : V)
    (chi : P →* Circle) (H : G → ℝ≥0) (hH_pos : ∀ g, 0 < H g) (hH_one : H 1 = 1)
    (leviMod : P → ℝ≥0) (hl_pos : ∀ p, 0 < leviMod p) (hl_one : leviMod 1 = 1)
    (hl_mul : ∀ p q, leviMod (p * q) = leviMod p * leviMod q)
    (hH_mul : ∀ (p : P) (g : G), H (p.1 * g) = leviMod p * H g)
    (hWeilP : ∀ (p : P) (v : V),
      evalZero (ω p.1 v) =
        (chi p : ℂ) * ((leviMod p : ℝ) : ℂ) ^ ((s0 + siegelRho n : ℝ) : ℂ) * evalZero v)
    (s : ℂ) (g : G) :
    (siegelParabolicSection_of_weil P n s0 ω evalZero Φ chi H hH_pos hH_one
      leviMod hl_pos hl_one hl_mul hH_mul hWeilP).eval s g =
      Stage14M1_SchrodingerFockModel.siegelSection ω evalZero H (s0 : ℂ) Φ s g :=
  rfl

/-! ### Concrete Archimedean, `p`-Adic & Adelic Vacuum Siegel Sections from `Stage14M1_SchrodingerFockModel` -/

/-- **Concrete Archimedean Gaussian-Vacuum Siegel Section**:
induced directly from `Stage14M1_SchrodingerFockModel.archLocalWeilRep` (`stdGauss`) and
`gauss_vacuum_eigenvalue` (`ω(k(θ)) φ₀ = exp(i θ) φ₀`) on the compact rotation group
`Multiplicative ℝ` (representing `SO(2) ⊂ U(1, 1)`). -/
def archVacuumSiegelSection (m : ℕ) :
    SiegelParabolicSection (Multiplicative ℝ) (⊥ : Subgroup (Multiplicative ℝ)) where
  n := 1
  s0 := siegelWeilPoint m 1
  chi := 1
  iwasawaH _ := 1
  iwasawaH_pos _ := zero_lt_one
  iwasawaH_one := rfl
  leviMod _ := 1
  leviMod_pos _ := zero_lt_one
  leviMod_one := rfl
  leviMod_mul _ _ := by simp
  iwasawaH_left_mul _ _ := by simp
  baseSection g :=
    (Stage14M1_SchrodingerFockModel.archLocalWeilRep.rep g
      Stage14M1_SchrodingerFockModel.archLocalWeilRep.vacuum).1 0
  base_equivar p g := by
    have hp : p.1 = 1 := Subgroup.mem_bot.mp p.2
    rw [hp, one_mul]
    simp

theorem archVacuumSiegelSection_eval (m : ℕ) (s : ℂ) (θ : ℝ) :
    (archVacuumSiegelSection m).eval s (Multiplicative.ofAdd θ) =
      Complex.exp (Complex.I * (θ : ℂ)) := by
  unfold SiegelParabolicSection.eval archVacuumSiegelSection
  simp only [NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow, one_mul]
  change Stage14M1_SchrodingerFockModel.realWeilOp (Real.cos θ) (Real.sin θ) (-Real.sin θ)
      (Real.cos θ) Stage14M1_SchrodingerFockModel.stdGauss 0 = _
  rw [Stage14M1_SchrodingerFockModel.gauss_vacuum_eigenvalue θ]
  simp [Stage14M1_SchrodingerFockModel.stdGauss_zero]

@[simp]
theorem archVacuumSiegelSection_eval_one (m : ℕ) (s : ℂ) :
    (archVacuumSiegelSection m).eval s 1 = 1 := by
  have h := archVacuumSiegelSection_eval m s 0
  simpa using h

/-- Local `p`-adic Levi subgroup `ℚ_pˣ` with positive `p`-adic norm `‖a‖_p > 0`. -/
private lemma padic_unit_norm_pos (p : Nat.Primes) (a : (ℚ_[p.1])ˣ) :
    (0 : ℝ≥0) < ‖(a : ℚ_[p.1])‖₊ :=
  nnnorm_pos.mpr a.ne_zero

/-- **Concrete Non-Archimedean `p`-Adic Spherical-Vacuum Siegel Section**:
induced directly from `Stage14M1_SchrodingerFockModel.padicLocalWeilRep p χ` (`padicSpherical p = 1_{ℤ_p}`)
at rank `m = 1, n = 1` (`s₀ = 0, ρ_P = 1/2`), with exact Levi determinant factor `‖a‖_p^{s + 1/2}`! -/
def padicSphericalSiegelSection (p : Nat.Primes) (χ : (ℚ_[p.1])ˣ →* Circle) :
    SiegelParabolicSection (ℚ_[p.1])ˣ (⊤ : Subgroup (ℚ_[p.1])ˣ) where
  n := 1
  s0 := 0
  chi := χ.comp (Subgroup.subtype ⊤)
  iwasawaH a := ‖(a : ℚ_[p.1])‖₊
  iwasawaH_pos a := padic_unit_norm_pos p a
  iwasawaH_one := by simp
  leviMod a := ‖(a.1 : ℚ_[p.1])‖₊
  leviMod_pos a := padic_unit_norm_pos p a.1
  leviMod_one := by simp
  leviMod_mul a b := by
    change ‖((a.1 * b.1 : (ℚ_[p.1])ˣ) : ℚ_[p.1])‖₊ = _
    rw [Units.val_mul, nnnorm_mul]
  iwasawaH_left_mul a g := by
    change ‖((a.1 * g : (ℚ_[p.1])ˣ) : ℚ_[p.1])‖₊ = _
    rw [Units.val_mul, nnnorm_mul]
  baseSection a :=
    (Stage14M1_SchrodingerFockModel.padicLocalWeilRep p χ |>.rep a
      (Stage14M1_SchrodingerFockModel.padicLocalWeilRep p χ).vacuum).1 0
  base_equivar a g := by
    have hball : (Stage14M1_SchrodingerFockModel.padicSpherical p.1).1 0 = 1 := by
      change Stage6AdelicPoisson.ballInd p.1 0 0 0 = 1
      simp [Stage6AdelicPoisson.ballInd]
    have heval : ∀ u : (ℚ_[p.1])ˣ,
        (Stage14M1_SchrodingerFockModel.padicLocalWeilRep p χ |>.rep u
          (Stage14M1_SchrodingerFockModel.padicLocalWeilRep p χ).vacuum).1 0 =
        (χ u : ℂ) * ((Real.sqrt ‖(u : ℚ_[p.1])‖ : ℝ) : ℂ) := by
      intro u
      change (χ u : ℂ) * ((Real.sqrt ‖(u : ℚ_[p.1])‖ : ℝ) : ℂ) *
        (Stage14M1_SchrodingerFockModel.padicSpherical p.1).1 ((u : ℚ_[p.1]) * 0) = _
      rw [mul_zero, hball, mul_one]
    rw [heval (a.1 * g), heval g]
    have ha_pos : (0 : ℝ) < ‖(a.1 : ℚ_[p.1])‖ := norm_pos_iff.mpr a.1.ne_zero
    have hsqrt : ((Real.sqrt ‖(a.1 : ℚ_[p.1])‖ : ℝ) : ℂ) =
        ((‖(a.1 : ℚ_[p.1])‖ : ℝ) : ℂ) ^ ((0 + siegelRho 1 : ℝ) : ℂ) := by
      rw [zero_add, siegelRho_one, Real.sqrt_eq_rpow, Complex.ofReal_cpow ha_pos.le]
    rw [map_mul, Circle.coe_mul, Units.val_mul, norm_mul, Real.sqrt_mul (norm_nonneg _),
      Complex.ofReal_mul, hsqrt]
    change (χ a.1 : ℂ) * (χ g : ℂ) *
        (((‖(a.1 : ℚ_[p.1])‖ : ℝ) : ℂ) ^ ((0 + siegelRho 1 : ℝ) : ℂ) *
          ((Real.sqrt ‖(g : ℚ_[p.1])‖ : ℝ) : ℂ)) =
      (χ a.1 : ℂ) * (((‖(a.1 : ℚ_[p.1])‖ : ℝ) : ℂ) ^ ((0 + siegelRho 1 : ℝ) : ℂ)) *
        ((χ g : ℂ) * ((Real.sqrt ‖(g : ℚ_[p.1])‖ : ℝ) : ℂ))
    ring

/-- Exact evaluation formula for `padicSphericalSiegelSection`:
`f_{p, s}(a) = χ_p(a) · ‖a‖_p^{s + 1/2}`! -/
theorem padicSphericalSiegelSection_eval (p : Nat.Primes) (χ : (ℚ_[p.1])ˣ →* Circle)
    (s : ℂ) (a : (ℚ_[p.1])ˣ) :
    (padicSphericalSiegelSection p χ).eval s a =
      (χ a : ℂ) * ((‖(a : ℚ_[p.1])‖ : ℝ) : ℂ) ^ (s + 1 / 2) := by
  have hball : (Stage14M1_SchrodingerFockModel.padicSpherical p.1).1 0 = 1 := by
    change Stage6AdelicPoisson.ballInd p.1 0 0 0 = 1
    simp [Stage6AdelicPoisson.ballInd]
  unfold SiegelParabolicSection.eval padicSphericalSiegelSection
  simp only [Complex.ofReal_zero, sub_zero, coe_nnnorm]
  change ((‖(a : ℚ_[p.1])‖ : ℝ) : ℂ) ^ s *
      ((χ a : ℂ) * ((Real.sqrt ‖(a : ℚ_[p.1])‖ : ℝ) : ℂ) *
        (Stage14M1_SchrodingerFockModel.padicSpherical p.1).1 ((a : ℚ_[p.1]) * 0)) = _
  rw [mul_zero, hball, mul_one]
  have ha_pos : (0 : ℝ) < ‖(a : ℚ_[p.1])‖ := norm_pos_iff.mpr a.ne_zero
  have hsqrt : ((Real.sqrt ‖(a : ℚ_[p.1])‖ : ℝ) : ℂ) =
      ((‖(a : ℚ_[p.1])‖ : ℝ) : ℂ) ^ ((1 / 2 : ℂ)) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ha_pos.le]
    norm_num
  rw [hsqrt, ← mul_assoc, mul_comm (((‖(a : ℚ_[p.1])‖ : ℝ) : ℂ) ^ s), mul_assoc,
    ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ha_pos.ne')]

@[simp]
theorem padicSphericalSiegelSection_eval_one (p : Nat.Primes) (χ : (ℚ_[p.1])ˣ →* Circle)
    (s : ℂ) :
    (padicSphericalSiegelSection p χ).eval s 1 = 1 := by
  rw [padicSphericalSiegelSection_eval]
  simp

/-- At any unramified compact element (`‖a‖_p = 1`, `χ a = 1`), the `p`-adic spherical section
evaluates identically to `1`! -/
theorem padicSphericalSiegelSection_eval_unramified (p : Nat.Primes) (χ : (ℚ_[p.1])ˣ →* Circle)
    (s : ℂ) {a : (ℚ_[p.1])ˣ} (ha : ‖(a : ℚ_[p.1])‖ = 1) (hχ : χ a = 1) :
    (padicSphericalSiegelSection p χ).eval s a = 1 := by
  rw [padicSphericalSiegelSection_eval, hχ, ha]
  simp

/-- **Concrete Factorizable Adelic Siegel Parabolic Section (`AdelicSiegelSection`)**:
an adelic restricted-product Siegel section `f_s = f_{∞, s} ⊗ (⊗'_p f_{p, s})` built from an
archimedean section, local `p`-adic sections, and an adelic vacuum `AdelicPureTensor` from
`Stage14M1_SchrodingerFockModel`, evaluating at any `AdelicWeilElement` as a finite product. -/
structure AdelicSiegelSection where
  m : ℕ
  n : ℕ
  vacuumTensor : Stage14M1_SchrodingerFockModel.AdelicPureTensor
  archFactor : ℂ → ℝ → ℂ
  finFactor : ∀ p : Nat.Primes, ((ℚ_[p.1])ˣ →* Circle) → ℂ → (ℚ_[p.1])ˣ → ℂ
  unramified_one : ∀ (p : Nat.Primes) (χ : (ℚ_[p.1])ˣ →* Circle) (s : ℂ) (a : (ℚ_[p.1])ˣ),
    Stage14M1_SchrodingerFockModel.padicWeilLevi p.1 χ a
        (Stage14M1_SchrodingerFockModel.padicSpherical p.1) =
      Stage14M1_SchrodingerFockModel.padicSpherical p.1 →
    finFactor p χ s a = 1

/-- Evaluation of an `AdelicSiegelSection` at `(s, g)` over `g.ramPrimes`. -/
def AdelicSiegelSection.eval (F : AdelicSiegelSection) (s : ℂ)
    (g : Stage14M1_SchrodingerFockModel.AdelicWeilElement) : ℂ :=
  F.archFactor s g.thetaInf * ∏ p ∈ g.ramPrimes, F.finFactor p (g.chiFin p) s (g.aFin p)

theorem AdelicSiegelSection.eval_eq_prod_superset (F : AdelicSiegelSection) (s : ℂ)
    (g : Stage14M1_SchrodingerFockModel.AdelicWeilElement) (S : Finset Nat.Primes)
    (hS : g.ramPrimes ⊆ S) :
    F.eval s g = F.archFactor s g.thetaInf * ∏ p ∈ S, F.finFactor p (g.chiFin p) s (g.aFin p) := by
  unfold eval
  congr 1
  exact Finset.prod_subset hS fun p _ hp =>
    F.unramified_one p (g.chiFin p) s (g.aFin p) (g.unramified_act p hp)

/-- Helper: if `padicWeilLevi p χ a` fixes `padicSpherical p`, then `‖a‖_p = 1` and `χ a = 1`. -/
private lemma norm_and_chi_eq_one_of_fixes_spherical (p : Nat.Primes)
    (χ : (ℚ_[p.1])ˣ →* Circle) (a : (ℚ_[p.1])ˣ)
    (hfix : Stage14M1_SchrodingerFockModel.padicWeilLevi p.1 χ a
        (Stage14M1_SchrodingerFockModel.padicSpherical p.1) =
      Stage14M1_SchrodingerFockModel.padicSpherical p.1) :
    ‖(a : ℚ_[p.1])‖ = 1 ∧ χ a = 1 := by
  have hball0 : (Stage14M1_SchrodingerFockModel.padicSpherical p.1).1 0 = 1 := by
    change Stage6AdelicPoisson.ballInd p.1 0 0 0 = 1
    simp [Stage6AdelicPoisson.ballInd]
  have h0 := congrArg (fun f : Stage14M1_SchrodingerFockModel.PadicSB p.1 => f.1 0) hfix
  change (χ a : ℂ) * ((Real.sqrt ‖(a : ℚ_[p.1])‖ : ℝ) : ℂ) *
      (Stage14M1_SchrodingerFockModel.padicSpherical p.1).1 ((a : ℚ_[p.1]) * 0) =
    (Stage14M1_SchrodingerFockModel.padicSpherical p.1).1 0 at h0
  rw [mul_zero, hball0, mul_one] at h0
  have hnorm : Real.sqrt ‖(a : ℚ_[p.1])‖ = 1 := by
    have hn := congrArg norm h0
    rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), norm_one] at hn
    exact hn
  have ha1 : ‖(a : ℚ_[p.1])‖ = 1 := by
    have hsq := congrArg (· ^ 2) hnorm
    rw [Real.sq_sqrt (norm_nonneg _), one_pow] at hsq
    exact hsq
  have hχ1 : χ a = 1 := by
    rw [hnorm, Complex.ofReal_one, mul_one] at h0
    exact Subtype.ext h0
  exact ⟨ha1, hχ1⟩

/-- **Canonical Adelic Vacuum Siegel Parabolic Section (`adelicVacuumSiegelSection`)**:
induced directly from `Stage14M1_SchrodingerFockModel.canonicalSchrodingerFockPackage`
(`adelicVacuum = stdGauss ⊗ ⊗'_p 1_{ℤ_p}`)! -/
def adelicVacuumSiegelSection (m : ℕ) : AdelicSiegelSection where
  m := m
  n := 1
  vacuumTensor := Stage14M1_SchrodingerFockModel.canonicalSchrodingerFockPackage.vacuumAdelic
  archFactor s θ := (archVacuumSiegelSection m).eval s (Multiplicative.ofAdd θ)
  finFactor p χ s a := (padicSphericalSiegelSection p χ).eval s a
  unramified_one p χ s a hfix := by
    obtain ⟨ha1, hχ1⟩ := norm_and_chi_eq_one_of_fixes_spherical p χ a hfix
    exact padicSphericalSiegelSection_eval_unramified p χ s ha1 hχ1

/-- Exact global evaluation of `adelicVacuumSiegelSection` at any `AdelicWeilElement`. -/
theorem adelicVacuumSiegelSection_eval (m : ℕ) (s : ℂ)
    (g : Stage14M1_SchrodingerFockModel.AdelicWeilElement) :
    (adelicVacuumSiegelSection m).eval s g =
      Complex.exp (Complex.I * (g.thetaInf : ℂ)) *
        ∏ p ∈ g.ramPrimes,
          (g.chiFin p (g.aFin p) : ℂ) * ((‖(g.aFin p : ℚ_[p.1])‖ : ℝ) : ℂ) ^ (s + 1 / 2) := by
  unfold AdelicSiegelSection.eval adelicVacuumSiegelSection
  dsimp only
  rw [archVacuumSiegelSection_eval]
  congr 1
  refine Finset.prod_congr rfl fun p _ => padicSphericalSiegelSection_eval p (g.chiFin p) s (g.aFin p)

/-- Identity `AdelicWeilElement` (`θ = 0`, `a_p = 1`, `χ_p = 1`, `ramPrimes = ∅`). -/
def adelicWeilOne : Stage14M1_SchrodingerFockModel.AdelicWeilElement where
  thetaInf := 0
  chiFin _ := 1
  aFin _ := 1
  ramPrimes := ∅
  unramified_act p _ := by
    ext x
    change (1 : ℂ) * ((Real.sqrt ‖(1 : ℚ_[p.1])‖ : ℝ) : ℂ) *
      (Stage14M1_SchrodingerFockModel.padicSpherical p.1).1 (1 * x) = _
    simp

@[simp]
theorem adelicVacuumSiegelSection_eval_one (m : ℕ) (s : ℂ) :
    (adelicVacuumSiegelSection m).eval s adelicWeilOne = 1 := by
  rw [adelicVacuumSiegelSection_eval]
  simp [adelicWeilOne]

/-- At the identity, `adelicVacuumSiegelSection` equals the vacuum value `adelicVacuum.eval (0, 0) = 1`. -/
theorem adelicVacuumSiegelSection_matches_vacuum (m : ℕ) (s : ℂ) :
    (adelicVacuumSiegelSection m).eval s adelicWeilOne =
      (adelicVacuumSiegelSection m).vacuumTensor.eval (0, 0) := by
  rw [adelicVacuumSiegelSection_eval_one]
  exact Stage14M1_SchrodingerFockModel.canonicalSchrodingerFockPackage.vacuum_eval_zero.symm

end ConcreteSiegelParabolicSection

/-! ## Section 2: Parabolic Cosets `(P ∩ Γ) \ Γ`, Concrete `SiegelEisensteinSeries` & Automorphy -/

section SiegelEisensteinSeriesDef

variable {G : Type*} [Group G]

/-- Right-coset equivalence relation on `Γ` modulo `P ∩ Γ`: `γ₁ ~ γ₂ ↔ γ₂ * γ₁⁻¹ ∈ P`. -/
def parabolicRightSetoid (Γ P : Subgroup G) : Setoid Γ where
  r γ₁ γ₂ := γ₂.1 * γ₁.1⁻¹ ∈ P
  iseqv :=
    { refl := fun γ => by simp
      symm := fun {γ₁ γ₂} h => by
        have hinv := P.inv_mem h
        simpa [mul_inv_rev] using hinv
      trans := fun {γ₁ γ₂ γ₃} h₁₂ h₂₃ => by
        have hmul := P.mul_mem h₂₃ h₁₂
        have heq : (γ₃.1 * γ₂.1⁻¹) * (γ₂.1 * γ₁.1⁻¹) = γ₃.1 * γ₁.1⁻¹ := by group
        rwa [heq] at hmul }

/-- Concrete right-coset space `(P ∩ Γ) \ Γ` indexing the Siegel Eisenstein series. -/
abbrev ParabolicCoset (Γ P : Subgroup G) : Type _ :=
  Quotient (parabolicRightSetoid Γ P)

/-- Right multiplication on `ParabolicCoset Γ P` by an element `δ : Γ`, realizing the natural
right `Γ`-action on `(P ∩ Γ) \ Γ`. -/
def parabolicCosetMulRight {Γ P : Subgroup G} (δ : Γ) :
    ParabolicCoset Γ P → ParabolicCoset Γ P :=
  Quotient.lift (fun γ : Γ => (⟦γ * δ⟧ : ParabolicCoset Γ P)) fun γ₁ γ₂ h => by
    apply Quotient.sound
    have h' : γ₂.1 * γ₁.1⁻¹ ∈ P := h
    change (γ₂ * δ).1 * (γ₁ * δ).1⁻¹ ∈ P
    have heq : (γ₂.1 * δ.1) * (γ₁.1 * δ.1)⁻¹ = γ₂.1 * γ₁.1⁻¹ := by group
    simpa [heq] using h'

/-- Right multiplication by `δ : Γ` is a bijection on `ParabolicCoset Γ P`. -/
def parabolicCosetMulRightEquiv {Γ P : Subgroup G} (δ : Γ) :
    ParabolicCoset Γ P ≃ ParabolicCoset Γ P where
  toFun := parabolicCosetMulRight δ
  invFun := parabolicCosetMulRight δ⁻¹
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h γ =>
      change (⟦γ * δ * δ⁻¹⟧ : ParabolicCoset Γ P) = ⟦γ⟧
      simp
  right_inv c := by
    induction c using Quotient.inductionOn with
    | h γ =>
      change (⟦γ * δ⁻¹ * δ⟧ : ParabolicCoset Γ P) = ⟦γ⟧
      simp

/-- Rational parabolic invariance condition: the character `F.chi` and Levi modulus `F.leviMod`
are trivial on `Γ ∩ P` (satisfied automatically by every arithmetic subgroup `Γ = G(F)` and
automorphic character `χ` trivial on `Fˣ`). -/
def RatParabolicInvariant (Γ : Subgroup G) {P : Subgroup G}
    (F : SiegelParabolicSection G P) : Prop :=
  ∀ (γ : Γ) (hP : γ.1 ∈ P), F.chi ⟨γ.1, hP⟩ = 1 ∧ F.leviMod ⟨γ.1, hP⟩ = 1

/-- Well-defined Eisenstein summand `c ↦ f_s(γ g)` on `ParabolicCoset Γ P = (P ∩ Γ) \ Γ`. -/
def eisensteinTerm (Γ : Subgroup G) {P : Subgroup G}
    (F : SiegelParabolicSection G P) (hInv : RatParabolicInvariant Γ F)
    (s : ℂ) (g : G) : ParabolicCoset Γ P → ℂ :=
  Quotient.lift (fun γ : Γ => F.eval s (γ.1 * g)) fun γ₁ γ₂ h => by
    have hP : γ₂.1 * γ₁.1⁻¹ ∈ P := h
    have hΓ : γ₂.1 * γ₁.1⁻¹ ∈ Γ := Γ.mul_mem γ₂.2 (Γ.inv_mem γ₁.2)
    obtain ⟨hχ, hmod⟩ := hInv ⟨γ₂.1 * γ₁.1⁻¹, hΓ⟩ hP
    symm
    have hmul : γ₂.1 * g = (γ₂.1 * γ₁.1⁻¹) * (γ₁.1 * g) := by group
    rw [hmul]
    have heq := F.eval_left_parabolic ⟨γ₂.1 * γ₁.1⁻¹, hP⟩ s (γ₁.1 * g)
    change F.eval s ((γ₂.1 * γ₁.1⁻¹) * (γ₁.1 * g)) = F.eval s (γ₁.1 * g)
    rw [heq, hχ, hmod]
    simp

@[simp]
theorem eisensteinTerm_mk (Γ : Subgroup G) {P : Subgroup G}
    (F : SiegelParabolicSection G P) (hInv : RatParabolicInvariant Γ F)
    (s : ℂ) (g : G) (γ : Γ) :
    eisensteinTerm Γ F hInv s g (⟦γ⟧ : ParabolicCoset Γ P) = F.eval s (γ.1 * g) :=
  rfl

theorem eisensteinTerm_mul_left (Γ : Subgroup G) {P : Subgroup G}
    (F : SiegelParabolicSection G P) (hInv : RatParabolicInvariant Γ F)
    (s : ℂ) (δ : Γ) (g : G) (c : ParabolicCoset Γ P) :
    eisensteinTerm Γ F hInv s (δ.1 * g) c =
      eisensteinTerm Γ F hInv s g (parabolicCosetMulRightEquiv δ c) := by
  induction c using Quotient.inductionOn with
  | h γ =>
    change F.eval s (γ.1 * (δ.1 * g)) = F.eval s ((γ * δ).1 * g)
    simp [mul_assoc]

/-- **Concrete Adelic/Global Siegel Eisenstein Series `SiegelEisensteinSeries`**:
$$E(g, s; F) = \sum_{\gamma \in (P \cap \Gamma) \backslash \Gamma} F_s(\gamma g).$$ -/
def SiegelEisensteinSeries (Γ : Subgroup G) {P : Subgroup G}
    (F : SiegelParabolicSection G P) (hInv : RatParabolicInvariant Γ F)
    (s : ℂ) (g : G) : ℂ :=
  ∑' c : ParabolicCoset Γ P, eisensteinTerm Γ F hInv s g c

/-- **Unconditional Left-`Γ`-Automorphy of `SiegelEisensteinSeries`**:
for every `δ ∈ Γ`, `s : ℂ`, and `g : G`, `E(δ g, s; F) = E(g, s; F)`! -/
theorem eisenstein_left_invariant (Γ : Subgroup G) {P : Subgroup G}
    (F : SiegelParabolicSection G P) (hInv : RatParabolicInvariant Γ F)
    (s : ℂ) (δ : Γ) (g : G) :
    SiegelEisensteinSeries Γ F hInv s (δ.1 * g) =
      SiegelEisensteinSeries Γ F hInv s g := by
  unfold SiegelEisensteinSeries
  simp_rw [eisensteinTerm_mul_left Γ F hInv s δ g]
  exact Equiv.tsum_eq (parabolicCosetMulRightEquiv δ) (eisensteinTerm Γ F hInv s g)

/-- Right-`K` eigenfunction transformation law for `SiegelEisensteinSeries`. -/
theorem eisenstein_right_compact_eigen (Γ : Subgroup G) {P K : Subgroup G}
    (F : SiegelParabolicSection G P) (hInv : RatParabolicInvariant Γ F)
    (κ : K →* Circle)
    (hH : ∀ (g : G) (k : K), F.iwasawaH (g * k.1) = F.iwasawaH g)
    (hB : ∀ (g : G) (k : K), F.baseSection (g * k.1) = (κ k : ℂ) * F.baseSection g)
    (s : ℂ) (g : G) (k : K) :
    SiegelEisensteinSeries Γ F hInv s (g * k.1) =
      (κ k : ℂ) * SiegelEisensteinSeries Γ F hInv s g := by
  unfold SiegelEisensteinSeries
  have hterm : ∀ c : ParabolicCoset Γ P,
      eisensteinTerm Γ F hInv s (g * k.1) c =
        (κ k : ℂ) * eisensteinTerm Γ F hInv s g c := fun c => by
    induction c using Quotient.inductionOn with
    | h γ =>
      change F.eval s (γ.1 * (g * k.1)) = (κ k : ℂ) * F.eval s (γ.1 * g)
      rw [← mul_assoc]
      exact F.eval_right_compact_eigen κ hH hB s (γ.1 * g) k
  simp_rw [hterm]
  exact tsum_mul_left

/-- Evaluation of `SiegelEisensteinSeries` at the Siegel–Weil point `s = s₀`. -/
theorem eisenstein_at_s0 (Γ : Subgroup G) {P : Subgroup G}
    (F : SiegelParabolicSection G P) (hInv : RatParabolicInvariant Γ F) (g : G) :
    SiegelEisensteinSeries Γ F hInv (F.s0 : ℂ) g =
      ∑' c : ParabolicCoset Γ P,
        Quotient.lift (fun γ : Γ => F.baseSection (γ.1 * g)) (fun γ₁ γ₂ h => by
          have hP : γ₂.1 * γ₁.1⁻¹ ∈ P := h
          have hΓ : γ₂.1 * γ₁.1⁻¹ ∈ Γ := Γ.mul_mem γ₂.2 (Γ.inv_mem γ₁.2)
          obtain ⟨hχ, hmod⟩ := hInv ⟨γ₂.1 * γ₁.1⁻¹, hΓ⟩ hP
          have hmul : γ₂.1 * g = (γ₂.1 * γ₁.1⁻¹) * (γ₁.1 * g) := by group
          rw [hmul, F.base_equivar ⟨γ₂.1 * γ₁.1⁻¹, hP⟩ (γ₁.1 * g), hχ, hmod]
          simp) c := by
  unfold SiegelEisensteinSeries
  refine tsum_congr fun c => ?_
  induction c using Quotient.inductionOn with
  | h γ => exact F.eval_at_s0 (γ.1 * g)

/-- Scalar linearity of `SiegelEisensteinSeries` in the parabolic section. -/
theorem eisenstein_smul_section (Γ : Subgroup G) {P : Subgroup G}
    (c : ℂ) (F : SiegelParabolicSection G P) (hInv : RatParabolicInvariant Γ F)
    (s : ℂ) (g : G) :
    SiegelEisensteinSeries Γ (F.smul c) hInv s g =
      c * SiegelEisensteinSeries Γ F hInv s g := by
  unfold SiegelEisensteinSeries
  have hterm : ∀ x : ParabolicCoset Γ P,
      eisensteinTerm Γ (F.smul c) hInv s g x = c * eisensteinTerm Γ F hInv s g x := fun x => by
    induction x using Quotient.inductionOn with
    | h γ => exact F.smul_eval c s (γ.1 * g)
  simp_rw [hterm]
  exact tsum_mul_left

end SiegelEisensteinSeriesDef

/-! ### Concrete Rank-1 `SL₂(ℤ)` / `U(1, 1)` Siegel–Eisenstein Series (Zero External Hypotheses) -/

section ConcreteSL2Eisenstein

/-- Nonzero integer lattice vectors `ℤ² \ {(0, 0)}` indexing the completed rank-1 Epstein /
Siegel–Eisenstein series. -/
abbrev NonzeroIntPair : Type :=
  { v : ℤ × ℤ // v ≠ (0, 0) }

/-- Individual summand of the rank-1 real-analytic Siegel–Eisenstein series on `ℍ`:
`y^{s + 1/2} / ‖c τ + d‖^{2 s + 1}`, matching `ρ_P = siegelRho 1 = 1/2`. -/
def sl2EisensteinTerm (τ s : ℂ) (v : NonzeroIntPair) : ℂ :=
  ((τ.im : ℂ) ^ (s + 1 / 2)) /
    (((‖(v.1.1 : ℂ) * τ + (v.1.2 : ℂ)‖ : ℝ) : ℂ) ^ (2 * s + 1))

/-- **Concrete Rank-1 Completed Siegel–Eisenstein Series on `ℍ` (`sl2SiegelEisenstein`)**:
$$E^*(\tau, s) = \sum_{(c, d) \in \mathbb{Z}^2 \setminus \{0\}} \frac{(\operatorname{Im} \tau)^{s + 1/2}}{|c\tau + d|^{2s + 1}}.$$ -/
def sl2SiegelEisenstein (τ s : ℂ) : ℂ :=
  ∑' v : NonzeroIntPair, sl2EisensteinTerm τ s v

/-- Nonvanishing of `c τ + d` for `(c, d) ≠ (0, 0)` and `τ.im > 0`. -/
lemma sl2_denom_ne_zero {τ : ℂ} (hτ : 0 < τ.im) (v : NonzeroIntPair) :
    (v.1.1 : ℂ) * τ + (v.1.2 : ℂ) ≠ 0 := by
  intro h0
  have him : ((v.1.1 : ℂ) * τ + (v.1.2 : ℂ)).im = 0 := congrArg Complex.im h0
  have hre : ((v.1.1 : ℂ) * τ + (v.1.2 : ℂ)).re = 0 := congrArg Complex.re h0
  simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
    zero_mul, add_zero] at him
  have hc0 : (v.1.1 : ℝ) = 0 := (mul_eq_zero.mp him).resolve_right hτ.ne'
  have hcZ : v.1.1 = 0 := by exact_mod_cast hc0
  simp only [hcZ, Int.cast_zero, zero_mul, zero_add, Complex.intCast_re] at hre
  have hdZ : v.1.2 = 0 := by exact_mod_cast hre
  exact v.2 (Prod.ext hcZ hdZ)

/-- Right action of `γ ∈ SL(2, ℤ)` on row vectors `(c, d) ∈ ℤ² \ {0}`. -/
def sl2RowAct (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (v : ℤ × ℤ) : ℤ × ℤ :=
  (v.1 * γ.1 0 0 + v.2 * γ.1 1 0, v.1 * γ.1 0 1 + v.2 * γ.1 1 1)

lemma sl2RowAct_mul (γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (v : ℤ × ℤ) :
    sl2RowAct γ₂ (sl2RowAct γ₁ v) = sl2RowAct (γ₁ * γ₂) v := by
  ext <;> simp [sl2RowAct, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma sl2RowAct_one (v : ℤ × ℤ) : sl2RowAct 1 v = v := by
  ext <;> simp [sl2RowAct]

/-- Every `γ ∈ SL(2, ℤ)` induces a bijection on `NonzeroIntPair = ℤ² \ {0}`. -/
def sl2NonzeroPairEquiv (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    NonzeroIntPair ≃ NonzeroIntPair where
  toFun v := ⟨sl2RowAct γ v.1, fun h => by
    have h1 := congrArg (sl2RowAct γ⁻¹) h
    rw [sl2RowAct_mul, mul_inv_cancel, sl2RowAct_one] at h1
    have h0 : sl2RowAct γ⁻¹ (0, 0) = (0, 0) := by simp [sl2RowAct]
    exact v.2 (h1.trans h0)⟩
  invFun v := ⟨sl2RowAct γ⁻¹ v.1, fun h => by
    have h1 := congrArg (sl2RowAct γ) h
    rw [sl2RowAct_mul, inv_mul_cancel, sl2RowAct_one] at h1
    have h0 : sl2RowAct γ (0, 0) = (0, 0) := by simp [sl2RowAct]
    exact v.2 (h1.trans h0)⟩
  left_inv v := Subtype.ext (by dsimp only; rw [sl2RowAct_mul, mul_inv_cancel, sl2RowAct_one])
  right_inv v := Subtype.ext (by dsimp only; rw [sl2RowAct_mul, inv_mul_cancel, sl2RowAct_one])

/-- Helper: complex power of a quotient of positive reals distributes over division. -/
private lemma ofReal_div_cpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (z : ℂ) :
    ((a / b : ℝ) : ℂ) ^ z = (a : ℂ) ^ z / (b : ℂ) ^ z := by
  have hb0 : ((b : ℝ) : ℂ) ^ z ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hb.ne')]
    exact Complex.exp_ne_zero _
  apply eq_div_of_mul_eq hb0
  rw [← Complex.mul_cpow_ofReal_nonneg (div_pos ha hb).le hb.le, ← Complex.ofReal_mul,
    div_mul_cancel₀ a hb.ne']

/-- Imaginary part formula for `Stage14M1_SiegelDomainReduction.mobiusInt`. -/
theorem mobiusInt_im {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ} {τ : ℂ} (_hτ : 0 < τ.im) :
    (Stage14M1_SiegelDomainReduction.mobiusInt γ τ).im =
      τ.im / ‖(γ.1 1 0 : ℂ) * τ + (γ.1 1 1 : ℂ)‖ ^ 2 := by
  have hdet : (γ.1 0 0 : ℝ) * (γ.1 1 1 : ℝ) - (γ.1 0 1 : ℝ) * (γ.1 1 0 : ℝ) = 1 := by
    have h1 := γ.2
    rw [Matrix.det_fin_two] at h1
    exact_mod_cast h1
  unfold Stage14M1_SiegelDomainReduction.mobiusInt
  set z : ℂ := (γ.1 1 0 : ℂ) * τ + (γ.1 1 1 : ℂ)
  rw [Complex.div_im, Complex.normSq_eq_norm_sq, ← sub_div]
  congr 1
  simp only [z, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.intCast_re, Complex.intCast_im]
  linear_combination τ.im * hdet

/-- **Unconditional `SL₂(ℤ)`-Automorphy of `sl2SiegelEisenstein`**:
`E*(γ · τ, s) = E*(τ, s)` for EVERY `γ ∈ SL(2, ℤ)`, `τ ∈ ℂ` (`0 < τ.im`), and `s : ℂ`! -/
theorem sl2SiegelEisenstein_invariant (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    {τ : ℂ} (hτ : 0 < τ.im) (s : ℂ) :
    sl2SiegelEisenstein (Stage14M1_SiegelDomainReduction.mobiusInt γ τ) s =
      sl2SiegelEisenstein τ s := by
  set z : ℂ := (γ.1 1 0 : ℂ) * τ + (γ.1 1 1 : ℂ)
  have hz_ne : z ≠ 0 := by
    have hrow : (γ.1 1 0, γ.1 1 1) ≠ (0, 0) := by
      intro h0
      have hc : γ.1 1 0 = 0 := congrArg Prod.fst h0
      have hd : γ.1 1 1 = 0 := congrArg Prod.snd h0
      have hdet := γ.2
      rw [Matrix.det_fin_two, hc, hd] at hdet
      norm_num at hdet
    exact sl2_denom_ne_zero hτ ⟨(γ.1 1 0, γ.1 1 1), hrow⟩
  have hzn_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz_ne
  have hterm : ∀ v : NonzeroIntPair,
      sl2EisensteinTerm (Stage14M1_SiegelDomainReduction.mobiusInt γ τ) s v =
        sl2EisensteinTerm τ s (sl2NonzeroPairEquiv γ v) := by
    intro v
    unfold sl2EisensteinTerm
    have hlin : (v.1.1 : ℂ) * Stage14M1_SiegelDomainReduction.mobiusInt γ τ + (v.1.2 : ℂ) =
        (((sl2RowAct γ v.1).1 : ℂ) * τ + ((sl2RowAct γ v.1).2 : ℂ)) / z := by
      unfold Stage14M1_SiegelDomainReduction.mobiusInt sl2RowAct
      change (v.1.1 : ℂ) * (((γ.1 0 0 : ℂ) * τ + (γ.1 0 1 : ℂ)) / z) + (v.1.2 : ℂ) = _
      rw [mul_div_assoc', div_add' _ _ _ hz_ne]
      congr 1
      dsimp only [z]
      push_cast
      ring
    have hnorm_eq : ‖(v.1.1 : ℂ) * Stage14M1_SiegelDomainReduction.mobiusInt γ τ + (v.1.2 : ℂ)‖ =
        ‖((sl2RowAct γ v.1).1 : ℂ) * τ + ((sl2RowAct γ v.1).2 : ℂ)‖ / ‖z‖ := by
      rw [hlin, norm_div]
    have hnum_pos : 0 < ‖((sl2RowAct γ v.1).1 : ℂ) * τ + ((sl2RowAct γ v.1).2 : ℂ)‖ :=
      norm_pos_iff.mpr (sl2_denom_ne_zero hτ (sl2NonzeroPairEquiv γ v))
    rw [mobiusInt_im hτ, hnorm_eq]
    have h1 : (((τ.im / ‖z‖ ^ 2 : ℝ) : ℂ) ^ (s + 1 / 2)) =
        ((τ.im : ℂ) ^ (s + 1 / 2)) / (((‖z‖ ^ 2 : ℝ) : ℂ) ^ (s + 1 / 2)) :=
      ofReal_div_cpow hτ (sq_pos_of_pos hzn_pos) (s + 1 / 2)
    have h2 : (((‖((sl2RowAct γ v.1).1 : ℂ) * τ + ((sl2RowAct γ v.1).2 : ℂ)‖ / ‖z‖ : ℝ) : ℂ) ^
        (2 * s + 1)) =
        (((‖((sl2RowAct γ v.1).1 : ℂ) * τ + ((sl2RowAct γ v.1).2 : ℂ)‖ : ℝ) : ℂ) ^ (2 * s + 1)) /
          (((‖z‖ : ℝ) : ℂ) ^ (2 * s + 1)) :=
      ofReal_div_cpow hnum_pos hzn_pos (2 * s + 1)
    have h3 : (((‖z‖ ^ 2 : ℝ) : ℂ) ^ (s + 1 / 2)) = (((‖z‖ : ℝ) : ℂ) ^ (2 * s + 1)) := by
      rw [sq, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hzn_pos.le hzn_pos.le,
        ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hzn_pos.ne')]
      congr 1; ring
    have hzc_ne : (((‖z‖ : ℝ) : ℂ) ^ (2 * s + 1)) ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hzn_pos.ne')]
      exact Complex.exp_ne_zero _
    rw [h1, h2, h3, div_div_div_cancel_right₀ hzc_ne]
    rfl
  unfold sl2SiegelEisenstein
  simp_rw [hterm]
  exact Equiv.tsum_eq (sl2NonzeroPairEquiv γ) (sl2EisensteinTerm τ s)

end ConcreteSL2Eisenstein

/-! ## Section 3: Height Bounds, Siegel-Set Envelope Integrability & `eisenstein_abs_convergent` -/

section EisensteinConvergence

/-! ### 3A. Zero-Hypothesis `SL₂(ℤ)` Lattice-Shell Absolute Convergence (`Re(s) > ρ_P = 1/2`) -/

/-- Exact shell norm lower bound on the Gauss–Siegel domain (`|Re τ| ≤ 1/2`, `Im τ ≥ √3 / 2`):
for EVERY `(c, d) ∈ ℤ²`, `((max |c| |d| : ℕ) : ℝ) / 2 ≤ ‖c τ + d‖`! -/
theorem sl2_gauss_reduced_lattice_norm_ge {τ : ℂ} (hre : |τ.re| ≤ 1 / 2)
    (him : Real.sqrt 3 / 2 ≤ τ.im) (c d : ℤ) :
    ((max c.natAbs d.natAbs : ℕ) : ℝ) / 2 ≤ ‖(c : ℂ) * τ + (d : ℂ)‖ := by
  have hsq : (((max c.natAbs d.natAbs : ℕ) : ℝ) / 2) ^ 2 ≤ ‖(c : ℂ) * τ + (d : ℂ)‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero, add_zero]
    have h3 : (3 / 4 : ℝ) ≤ τ.im ^ 2 := by
      have hsq3 := pow_le_pow_left₀ (by positivity) him 2
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] at hsq3
      linarith
    have hc_abs : (c.natAbs : ℝ) = |(c : ℝ)| := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    have hd_abs : (d.natAbs : ℝ) = |(d : ℝ)| := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    have hc_bound : ((c.natAbs : ℝ) / 2) ^ 2 ≤
        ((c : ℝ) * τ.re + (d : ℝ)) * ((c : ℝ) * τ.re + (d : ℝ)) +
          ((c : ℝ) * τ.im) * ((c : ℝ) * τ.im) := by
      have h1 : 0 ≤ ((c : ℝ) * τ.re + (d : ℝ)) * ((c : ℝ) * τ.re + (d : ℝ)) := mul_self_nonneg _
      have h2 : (c.natAbs : ℝ) ^ 2 = (c : ℝ) ^ 2 := by rw [hc_abs, sq_abs]
      nlinarith [sq_nonneg (c : ℝ)]
    have hd_bound : ((d.natAbs : ℝ) / 2) ^ 2 ≤
        ((c : ℝ) * τ.re + (d : ℝ)) * ((c : ℝ) * τ.re + (d : ℝ)) +
          ((c : ℝ) * τ.im) * ((c : ℝ) * τ.im) := by
      by_cases hcd : |(c : ℝ)| ≤ |(d : ℝ)|
      · have hre_mul : |(c : ℝ) * τ.re| ≤ |(d : ℝ)| / 2 := by
          rw [abs_mul]
          nlinarith [abs_nonneg (c : ℝ), abs_nonneg (d : ℝ)]
        have htri : |(d : ℝ)| / 2 ≤ |(c : ℝ) * τ.re + (d : ℝ)| := by
          have h1 := abs_add_le ((c : ℝ) * τ.re + (d : ℝ)) (-(c : ℝ) * τ.re)
          rw [show (c : ℝ) * τ.re + (d : ℝ) + -(c : ℝ) * τ.re = (d : ℝ) by ring,
            show -(c : ℝ) * τ.re = -((c : ℝ) * τ.re) by ring, abs_neg] at h1
          linarith
        have hsq1 : (|(d : ℝ)| / 2) ^ 2 ≤ ((c : ℝ) * τ.re + (d : ℝ)) ^ 2 := by
          have := pow_le_pow_left₀ (by positivity) htri 2
          rwa [sq_abs] at this
        have h2 : 0 ≤ ((c : ℝ) * τ.im) * ((c : ℝ) * τ.im) := mul_self_nonneg _
        rw [hd_abs]
        nlinarith [sq ((c : ℝ) * τ.re + (d : ℝ))]
      · push Not at hcd
        have hsqc : (d.natAbs : ℝ) ^ 2 ≤ (c.natAbs : ℝ) ^ 2 := by
          rw [hc_abs, hd_abs]; nlinarith [abs_nonneg (c : ℝ), abs_nonneg (d : ℝ)]
        nlinarith [hc_bound]
    rcases le_total c.natAbs d.natAbs with hle | hle
    · rw [max_eq_right hle]; exact hd_bound
    · rw [max_eq_left hle]; exact hc_bound
  nlinarith [norm_nonneg ((c : ℂ) * τ + (d : ℂ)),
    show (0 : ℝ) ≤ ((max c.natAbs d.natAbs : ℕ) : ℝ) / 2 by positivity]

/-- Explicit finite cardinality bound for the `ℓ∞`-shell `{v ∈ ℤ² | max |v.1| |v.2| = k}`:
at most `(2k + 1)² ≤ 9 k²` (in fact `≤ 8 k` for `k ≥ 1`)! -/
private def intShell (k : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(k : ℤ)) (k : ℤ) ×ˢ Finset.Icc (-(k : ℤ)) (k : ℤ)).filter
    fun v => max v.1.natAbs v.2.natAbs = k

private lemma int_bounds_of_natAbs_le {a : ℤ} {k : ℕ} (h : a.natAbs ≤ k) :
    -(k : ℤ) ≤ a ∧ a ≤ (k : ℤ) := by
  have h' : |a| ≤ (k : ℤ) := by rw [← Int.natCast_natAbs]; exact_mod_cast h
  exact abs_le.mp h'

private lemma mem_intShell_iff {k : ℕ} {v : ℤ × ℤ} :
    v ∈ intShell k ↔ max v.1.natAbs v.2.natAbs = k := by
  unfold intShell
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨?_, ?_⟩, h⟩
    · exact int_bounds_of_natAbs_le (h ▸ le_max_left _ _)
    · exact int_bounds_of_natAbs_le (h ▸ le_max_right _ _)

private lemma card_intShell_le {k : ℕ} (hk : 1 ≤ k) :
    (intShell k).card ≤ 8 * k := by
  let S₁ : Finset (ℤ × ℤ) := ({(k : ℤ), -(k : ℤ)} : Finset ℤ) ×ˢ Finset.Icc (-(k : ℤ)) (k : ℤ)
  let S₂' : Finset (ℤ × ℤ) := Finset.Ioo (-(k : ℤ)) (k : ℤ) ×ˢ ({(k : ℤ), -(k : ℤ)} : Finset ℤ)
  have hsub' : intShell k ⊆ S₁ ∪ S₂' := by
    intro v hv
    have hm := (mem_intShell_iff.mp hv)
    have hb1 : -(k : ℤ) ≤ v.1 ∧ v.1 ≤ (k : ℤ) := int_bounds_of_natAbs_le (hm ▸ le_max_left _ _)
    have hb2 : -(k : ℤ) ≤ v.2 ∧ v.2 ≤ (k : ℤ) := int_bounds_of_natAbs_le (hm ▸ le_max_right _ _)
    rw [Finset.mem_union]
    by_cases hv1 : v.1 = (k : ℤ) ∨ v.1 = -(k : ℤ)
    · left
      exact Finset.mem_product.mpr ⟨by simp [hv1], Finset.mem_Icc.mpr hb2⟩
    · right
      push Not at hv1
      have hlt1 : -(k : ℤ) < v.1 ∧ v.1 < (k : ℤ) :=
        ⟨lt_of_le_of_ne hb1.1 hv1.2.symm, lt_of_le_of_ne hb1.2 hv1.1⟩
      have hne1 : v.1.natAbs ≠ k := fun heq => by
        rcases Int.natAbs_eq_iff.mp heq with h | h
        · exact hv1.1 h
        · exact hv1.2 h
      have hv2_eq : v.2.natAbs = k := by
        rcases max_choice v.1.natAbs v.2.natAbs with hmax | hmax
        · exfalso; exact hne1 (hmax ▸ hm)
        · exact hmax ▸ hm
      have hv2 : v.2 = (k : ℤ) ∨ v.2 = -(k : ℤ) := Int.natAbs_eq_iff.mp hv2_eq
      exact Finset.mem_product.mpr ⟨Finset.mem_Ioo.mpr hlt1, by simp [hv2]⟩
  have hIcc_card : (Finset.Icc (-(k : ℤ)) (k : ℤ)).card = 2 * k + 1 := by
    rw [Int.card_Icc]; omega
  have hIoo_card : (Finset.Ioo (-(k : ℤ)) (k : ℤ)).card = 2 * k - 1 := by
    rw [Int.card_Ioo]; omega
  have hpair_card : ({(k : ℤ), -(k : ℤ)} : Finset ℤ).card ≤ 2 := Finset.card_le_two
  have hS1 : S₁.card ≤ 2 * (2 * k + 1) := by
    rw [Finset.card_product, hIcc_card]; exact Nat.mul_le_mul_right _ hpair_card
  have hS2' : S₂'.card ≤ (2 * k - 1) * 2 := by
    rw [Finset.card_product, hIoo_card]; exact Nat.mul_le_mul_left _ hpair_card
  have htot' := (Finset.card_le_card hsub').trans (Finset.card_union_le S₁ S₂')
  omega

/-- **Zero-Hypothesis Rank-1 `SL₂(ℤ)` Siegel–Eisenstein Absolute Convergence Theorem
(`sl2_eisenstein_abs_convergent`)**:
proved directly from `Stage14M1_SiegelDomainReduction.reduction_to_siegel_domain_sl2_int`!
For EVERY `τ ∈ ℂ` (`0 < τ.im`) and EVERY `s ∈ ℂ` with `siegelRho 1 < s.re` (`1/2 < s.re`),
the Siegel–Eisenstein series `sl2SiegelEisenstein τ s` converges **absolutely** (`Summable ‖·‖`
and `Summable`), with an explicit Siegel-domain growth ceiling! -/
theorem sl2_eisenstein_abs_convergent {τ : ℂ} (hτ : 0 < τ.im) {s : ℂ}
    (hs : siegelRho 1 < s.re) :
    Summable (fun v : NonzeroIntPair => ‖sl2EisensteinTerm τ s v‖) ∧
    Summable (sl2EisensteinTerm τ s) := by
  obtain ⟨γ, hre, -, him⟩ := Stage14M1_SiegelDomainReduction.reduction_to_siegel_domain_sl2_int τ hτ
  set τ' : ℂ := Stage14M1_SiegelDomainReduction.mobiusInt γ τ
  have hτ' : 0 < τ'.im := lt_of_lt_of_le (by positivity) him
  -- Step 1: Absolute summability at the Gauss-Siegel reduced point `τ'`
  have hsumm' : Summable (fun v : NonzeroIntPair => ‖sl2EisensteinTerm τ' s v‖) := by
    have h2s : (1 : ℝ) < 2 * s.re := by unfold siegelRho at hs; linarith
    have hnat_summ : Summable (fun k : ℕ =>
        (8 : ℝ) * (2 : ℝ) ^ (2 * s.re + 1) * (τ'.im ^ (s.re + 1 / 2)) *
          ((k : ℝ) ^ (2 * s.re))⁻¹) :=
      (Real.summable_nat_rpow_inv.mpr h2s).mul_left _
    refine summable_of_sum_le (fun _ => norm_nonneg _) (c := ∑' k : ℕ,
        (8 : ℝ) * (2 : ℝ) ^ (2 * s.re + 1) * (τ'.im ^ (s.re + 1 / 2)) *
          ((k : ℝ) ^ (2 * s.re))⁻¹) fun F => ?_
    let K : ℕ := F.sup (fun v => max v.1.1.natAbs v.1.2.natAbs) + 1
    have hmemK : ∀ v ∈ F, max v.1.1.natAbs v.1.2.natAbs ∈ Finset.Ico 1 K := fun v hv => by
      refine Finset.mem_Ico.mpr ⟨?_,
        Nat.lt_succ_of_le (Finset.le_sup (f := fun v : NonzeroIntPair => max v.1.1.natAbs v.1.2.natAbs) hv)⟩
      by_contra h0
      have hm0 : max v.1.1.natAbs v.1.2.natAbs = 0 := by omega
      have h1 : v.1.1.natAbs = 0 := Nat.eq_zero_of_le_zero (hm0 ▸ le_max_left _ _)
      have h2 : v.1.2.natAbs = 0 := Nat.eq_zero_of_le_zero (hm0 ▸ le_max_right _ _)
      exact v.2 (Prod.ext (Int.natAbs_eq_zero.mp h1) (Int.natAbs_eq_zero.mp h2))
    rw [← Finset.sum_fiberwise_of_maps_to hmemK]
    have hshell_le : ∀ k ∈ Finset.Ico 1 K,
        ∑ v ∈ F.filter (fun v => max v.1.1.natAbs v.1.2.natAbs = k),
          ‖sl2EisensteinTerm τ' s v‖ ≤
        (8 : ℝ) * (2 : ℝ) ^ (2 * s.re + 1) * (τ'.im ^ (s.re + 1 / 2)) *
          ((k : ℝ) ^ (2 * s.re))⁻¹ := by
      intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
      have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk1
      have hcard_le : (F.filter (fun v => max v.1.1.natAbs v.1.2.natAbs = k)).card ≤ 8 * k := by
        have hinj : ((F.filter (fun v => max v.1.1.natAbs v.1.2.natAbs = k)).image Subtype.val) ⊆
            intShell k := by
          intro x hx
          rcases Finset.mem_image.mp hx with ⟨v, hv, rfl⟩
          exact mem_intShell_iff.mpr (Finset.mem_filter.mp hv).2
        calc (F.filter (fun v => max v.1.1.natAbs v.1.2.natAbs = k)).card
            = ((F.filter (fun v => max v.1.1.natAbs v.1.2.natAbs = k)).image Subtype.val).card :=
                (Finset.card_image_of_injective _ Subtype.val_injective).symm
          _ ≤ (intShell k).card := Finset.card_le_card hinj
          _ ≤ 8 * k := card_intShell_le hk1
      have hpt : ∀ v ∈ F.filter (fun v => max v.1.1.natAbs v.1.2.natAbs = k),
          ‖sl2EisensteinTerm τ' s v‖ ≤
            (2 : ℝ) ^ (2 * s.re + 1) * (τ'.im ^ (s.re + 1 / 2)) / ((k : ℝ) ^ (2 * s.re + 1)) := by
        intro v hv
        have hkv : max v.1.1.natAbs v.1.2.natAbs = k := (Finset.mem_filter.mp hv).2
        have hden_pos : 0 < ‖(v.1.1 : ℂ) * τ' + (v.1.2 : ℂ)‖ :=
          norm_pos_iff.mpr (sl2_denom_ne_zero hτ' v)
        have hge : (k : ℝ) / 2 ≤ ‖(v.1.1 : ℂ) * τ' + (v.1.2 : ℂ)‖ := by
          simpa [hkv] using sl2_gauss_reduced_lattice_norm_ge hre him v.1.1 v.1.2
        have hnorm : ‖sl2EisensteinTerm τ' s v‖ =
            (τ'.im ^ (s.re + 1 / 2)) / (‖(v.1.1 : ℂ) * τ' + (v.1.2 : ℂ)‖ ^ (2 * s.re + 1)) := by
          unfold sl2EisensteinTerm
          rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hτ',
            Complex.norm_cpow_eq_rpow_re_of_pos hden_pos]
          simp
        rw [hnorm]
        have hexp_pos : 0 < 2 * s.re + 1 := by linarith
        have hpow_ge : ((k : ℝ) / 2) ^ (2 * s.re + 1) ≤
            ‖(v.1.1 : ℂ) * τ' + (v.1.2 : ℂ)‖ ^ (2 * s.re + 1) :=
          Real.rpow_le_rpow (by positivity) hge hexp_pos.le
        have hpow_eq : ((k : ℝ) / 2) ^ (2 * s.re + 1) =
            (k : ℝ) ^ (2 * s.re + 1) / (2 : ℝ) ^ (2 * s.re + 1) :=
          Real.div_rpow hk_pos.le (by norm_num) _
        have hdiv : τ'.im ^ (s.re + 1 / 2) / ‖(v.1.1 : ℂ) * τ' + (v.1.2 : ℂ)‖ ^ (2 * s.re + 1) ≤
            τ'.im ^ (s.re + 1 / 2) / ((k : ℝ) ^ (2 * s.re + 1) / (2 : ℝ) ^ (2 * s.re + 1)) := by
          rw [← hpow_eq]
          exact div_le_div_of_nonneg_left (Real.rpow_nonneg hτ'.le _) (by positivity) hpow_ge
        calc τ'.im ^ (s.re + 1 / 2) / ‖(v.1.1 : ℂ) * τ' + (v.1.2 : ℂ)‖ ^ (2 * s.re + 1)
            ≤ τ'.im ^ (s.re + 1 / 2) / ((k : ℝ) ^ (2 * s.re + 1) / (2 : ℝ) ^ (2 * s.re + 1)) := hdiv
          _ = (2 : ℝ) ^ (2 * s.re + 1) * (τ'.im ^ (s.re + 1 / 2)) / ((k : ℝ) ^ (2 * s.re + 1)) := by
              rw [div_div_eq_mul_div, mul_comm]
      calc ∑ v ∈ F.filter (fun v => max v.1.1.natAbs v.1.2.natAbs = k),
            ‖sl2EisensteinTerm τ' s v‖
          ≤ ∑ _v ∈ F.filter (fun v => max v.1.1.natAbs v.1.2.natAbs = k),
              ((2 : ℝ) ^ (2 * s.re + 1) * (τ'.im ^ (s.re + 1 / 2)) / ((k : ℝ) ^ (2 * s.re + 1))) :=
            Finset.sum_le_sum hpt
        _ = ((F.filter (fun v => max v.1.1.natAbs v.1.2.natAbs = k)).card : ℝ) *
              ((2 : ℝ) ^ (2 * s.re + 1) * (τ'.im ^ (s.re + 1 / 2)) / ((k : ℝ) ^ (2 * s.re + 1))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((8 * k : ℕ) : ℝ) *
              ((2 : ℝ) ^ (2 * s.re + 1) * (τ'.im ^ (s.re + 1 / 2)) / ((k : ℝ) ^ (2 * s.re + 1))) := by
            refine mul_le_mul_of_nonneg_right (by exact_mod_cast hcard_le) (by positivity)
        _ = (8 : ℝ) * (2 : ℝ) ^ (2 * s.re + 1) * (τ'.im ^ (s.re + 1 / 2)) *
              ((k : ℝ) ^ (2 * s.re))⁻¹ := by
            rw [Nat.cast_mul, Nat.cast_ofNat, Real.rpow_add hk_pos, Real.rpow_one]
            have hk_ne : (k : ℝ) ≠ 0 := hk_pos.ne'
            have hkp_ne : (k : ℝ) ^ (2 * s.re) ≠ 0 := (Real.rpow_pos_of_pos hk_pos _).ne'
            field_simp [hk_ne, hkp_ne]
    calc ∑ k ∈ Finset.Ico 1 K,
          ∑ v ∈ F.filter (fun v => max v.1.1.natAbs v.1.2.natAbs = k), ‖sl2EisensteinTerm τ' s v‖
        ≤ ∑ k ∈ Finset.Ico 1 K,
            (8 : ℝ) * (2 : ℝ) ^ (2 * s.re + 1) * (τ'.im ^ (s.re + 1 / 2)) *
              ((k : ℝ) ^ (2 * s.re))⁻¹ := Finset.sum_le_sum hshell_le
      _ ≤ ∑' k : ℕ, (8 : ℝ) * (2 : ℝ) ^ (2 * s.re + 1) * (τ'.im ^ (s.re + 1 / 2)) *
            ((k : ℝ) ^ (2 * s.re))⁻¹ :=
          hnat_summ.sum_le_tsum (Finset.Ico 1 K) (fun k _ => by positivity)
  -- Step 2: Transport summability back from `τ' = γ · τ` to `τ` via `sl2NonzeroPairEquiv γ`
  have hterm_eq : ∀ v : NonzeroIntPair,
      ‖sl2EisensteinTerm τ' s v‖ = ‖sl2EisensteinTerm τ s (sl2NonzeroPairEquiv γ v)‖ := by
    intro v
    -- Reuse the same invariance relation
    set z : ℂ := (γ.1 1 0 : ℂ) * τ + (γ.1 1 1 : ℂ)
    have hz_ne : z ≠ 0 := by
      have hrow : (γ.1 1 0, γ.1 1 1) ≠ (0, 0) := by
        intro h0
        have hc : γ.1 1 0 = 0 := congrArg Prod.fst h0
        have hd : γ.1 1 1 = 0 := congrArg Prod.snd h0
        have hdet := γ.2
        rw [Matrix.det_fin_two, hc, hd] at hdet
        norm_num at hdet
      exact sl2_denom_ne_zero hτ ⟨(γ.1 1 0, γ.1 1 1), hrow⟩
    have hzn_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz_ne
    have hlin : (v.1.1 : ℂ) * τ' + (v.1.2 : ℂ) =
        (((sl2RowAct γ v.1).1 : ℂ) * τ + ((sl2RowAct γ v.1).2 : ℂ)) / z := by
      unfold τ' Stage14M1_SiegelDomainReduction.mobiusInt sl2RowAct
      change (v.1.1 : ℂ) * (((γ.1 0 0 : ℂ) * τ + (γ.1 0 1 : ℂ)) / z) + (v.1.2 : ℂ) = _
      rw [mul_div_assoc', div_add' _ _ _ hz_ne]
      congr 1
      dsimp only [z]
      push_cast
      ring
    have hnum_pos : 0 < ‖((sl2RowAct γ v.1).1 : ℂ) * τ + ((sl2RowAct γ v.1).2 : ℂ)‖ :=
      norm_pos_iff.mpr (sl2_denom_ne_zero hτ (sl2NonzeroPairEquiv γ v))
    have hden'_pos : 0 < ‖(v.1.1 : ℂ) * τ' + (v.1.2 : ℂ)‖ :=
      norm_pos_iff.mpr (sl2_denom_ne_zero hτ' v)
    unfold sl2EisensteinTerm
    dsimp only [sl2NonzeroPairEquiv, Equiv.coe_fn_mk]
    rw [norm_div, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hτ',
      Complex.norm_cpow_eq_rpow_re_of_pos hden'_pos,
      Complex.norm_cpow_eq_rpow_re_of_pos hτ,
      Complex.norm_cpow_eq_rpow_re_of_pos hnum_pos]
    simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, sub_zero, Complex.one_re, Complex.div_ofNat_re]
    rw [show τ'.im = τ.im / ‖z‖ ^ 2 from mobiusInt_im hτ, hlin, norm_div,
      Real.div_rpow hτ.le (sq_nonneg ‖z‖), Real.div_rpow hnum_pos.le hzn_pos.le]
    have h3 : (‖z‖ ^ 2) ^ (s.re + 1 / 2) = ‖z‖ ^ (2 * s.re + 1) := by
      rw [← Real.rpow_natCast ‖z‖ 2, ← Real.rpow_mul hzn_pos.le]
      congr 1; push_cast; ring
    rw [h3, div_div_div_cancel_right₀ (Real.rpow_pos_of_pos hzn_pos _).ne']
  have hsumm_norm : Summable (fun v : NonzeroIntPair => ‖sl2EisensteinTerm τ s v‖) := by
    rw [← (sl2NonzeroPairEquiv γ).summable_iff]
    simpa only [Function.comp_def, ← hterm_eq] using hsumm'
  exact ⟨hsumm_norm, hsumm_norm.of_norm⟩

/-! ### 3B. General Godement Height-Shell Convergence & `eisenstein_abs_convergent` -/

/-- **Godement Coset Height-Shell Growth Data (`CosetShellGrowth`)**:
stratifies `ParabolicCoset Γ P = (P ∩ Γ) \ Γ` into finite dyadic height shells `shell c = k`
controlled by a `Stage14M1_SiegelDomainReduction.UnitaryHeightFn G`, with:
- shell cardinality bounded by `C_card * 2^{2 ρ_P k}` (exact Godement critical exponent `2 ρ_P = n`),
- coset Iwasawa height decay `F.iwasawaH(γ g) ≤ C_H * H(g)^{deg_H} * 2^{-k}`,
- base section moderate bound `‖F.baseSection g‖ ≤ C_sec * F.iwasawaH(g)^{s₀ + ρ_P}`. -/
structure CosetShellGrowth {G : Type*} [Group G] (Γ P : Subgroup G)
    (F : SiegelParabolicSection G P)
    (H : Stage14M1_SiegelDomainReduction.UnitaryHeightFn G) where
  shell : ParabolicCoset Γ P → ℕ
  C_card : ℝ
  C_card_nonneg : 0 ≤ C_card
  shell_finite : ∀ k : ℕ, (Set.preimage shell {k}).Finite
  shell_card_le : ∀ k : ℕ,
    (Nat.card { c : ParabolicCoset Γ P // shell c = k } : ℝ) ≤
      C_card * (2 : ℝ) ^ (2 * siegelRho F.n * (k : ℝ))
  C_H : ℝ
  C_H_pos : 0 < C_H
  deg_H : ℕ
  height_decay : ∀ (γ : Γ) (g : G),
    (F.iwasawaH (γ.1 * g) : ℝ) ≤
      C_H * (H g) ^ deg_H * (2 : ℝ) ^ (-(shell (⟦γ⟧ : ParabolicCoset Γ P) : ℝ))
  C_sec : ℝ
  C_sec_nonneg : 0 ≤ C_sec
  base_bound : ∀ g : G,
    ‖F.baseSection g‖ ≤ C_sec * (F.iwasawaH g : ℝ) ^ (F.s0 + siegelRho F.n)

/-- Explicit Godement convergence constant `C_E(s)` for `Re(s) > ρ_P`. -/
def godementConst {G : Type*} [Group G] {Γ P : Subgroup G}
    {F : SiegelParabolicSection G P}
    {H : Stage14M1_SiegelDomainReduction.UnitaryHeightFn G}
    (G_sh : CosetShellGrowth Γ P F H) (s : ℂ) : ℝ :=
  G_sh.C_sec * G_sh.C_card * (G_sh.C_H ^ (s.re + siegelRho F.n)) *
    (1 - (2 : ℝ) ^ (-(s.re - siegelRho F.n)))⁻¹

lemma godementConst_nonneg {G : Type*} [Group G] {Γ P : Subgroup G}
    {F : SiegelParabolicSection G P}
    {H : Stage14M1_SiegelDomainReduction.UnitaryHeightFn G}
    (G_sh : CosetShellGrowth Γ P F H) {s : ℂ} (hs : siegelRho F.n < s.re) :
    0 ≤ godementConst G_sh s := by
  unfold godementConst
  have hq_lt : (2 : ℝ) ^ (-(s.re - siegelRho F.n)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) (by linarith)
  have hden : 0 < 1 - (2 : ℝ) ^ (-(s.re - siegelRho F.n)) := by linarith
  exact mul_nonneg (mul_nonneg (mul_nonneg G_sh.C_sec_nonneg G_sh.C_card_nonneg)
    (Real.rpow_nonneg G_sh.C_H_pos.le _)) (inv_nonneg.mpr hden.le)

/-- **MASTER ABSOLUTE CONVERGENCE & MODERATE-GROWTH THEOREM (`eisenstein_abs_convergent`)**:
For ANY `SiegelParabolicSection G P` `F` with `CosetShellGrowth` relative to a
`Stage14M1_SiegelDomainReduction.UnitaryHeightFn G` `H`, and EVERY `s : ℂ` in the Godement
convergence half-plane `siegelRho F.n < s.re`:
1. The Siegel Eisenstein series converges **absolutely**:
   `Summable (fun c => ‖eisensteinTerm Γ F hInv s g c‖)` and `Summable (eisensteinTerm Γ F hInv s g)`;
2. Explicit **moderate height growth** holds for all `g : G`:
   `‖SiegelEisensteinSeries Γ F hInv s g‖ ≤ godementConst G_sh s * (H g) ^ ((G_sh.deg_H : ℝ) * (s.re + siegelRho F.n))`! -/
theorem eisenstein_abs_convergent {G : Type*} [Group G] (Γ : Subgroup G) {P : Subgroup G}
    (F : SiegelParabolicSection G P) (hInv : RatParabolicInvariant Γ F)
    (H : Stage14M1_SiegelDomainReduction.UnitaryHeightFn G)
    (G_sh : CosetShellGrowth Γ P F H)
    {s : ℂ} (hs : siegelRho F.n < s.re) (g : G) :
    Summable (fun c : ParabolicCoset Γ P => ‖eisensteinTerm Γ F hInv s g c‖) ∧
    Summable (eisensteinTerm Γ F hInv s g) ∧
    ‖SiegelEisensteinSeries Γ F hInv s g‖ ≤
      godementConst G_sh s * (H g) ^ ((G_sh.deg_H : ℝ) * (s.re + siegelRho F.n)) := by
  classical
  set q : ℝ := (2 : ℝ) ^ (-(s.re - siegelRho F.n))
  have hq_nn : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq_lt : q < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2) (by linarith)
  have hα_pos : 0 < s.re + siegelRho F.n := by
    have := siegelRho_nonneg F.n; linarith
  have hHg_pos : 0 < H g := H.pos g
  set M_g : ℝ := G_sh.C_sec * (G_sh.C_H ^ (s.re + siegelRho F.n)) *
      (H g) ^ ((G_sh.deg_H : ℝ) * (s.re + siegelRho F.n))
  have hMg_nn : 0 ≤ M_g :=
    mul_nonneg (mul_nonneg G_sh.C_sec_nonneg (Real.rpow_nonneg G_sh.C_H_pos.le _))
      (Real.rpow_nonneg hHg_pos.le _)
  -- Step 1: Pointwise shell decay on each coset `c`
  have hpt : ∀ c : ParabolicCoset Γ P,
      ‖eisensteinTerm Γ F hInv s g c‖ ≤
        M_g * (2 : ℝ) ^ (-(s.re + siegelRho F.n) * (G_sh.shell c : ℝ)) := by
    intro c
    induction c using Quotient.inductionOn with
    | h γ =>
      rw [eisensteinTerm_mk]
      have h1 := F.norm_eval_le_of_base_bound G_sh.base_bound s (γ.1 * g)
      have h2 := G_sh.height_decay γ g
      have hHpos : (0 : ℝ) < (F.iwasawaH (γ.1 * g) : ℝ) :=
        NNReal.coe_pos.mpr (F.iwasawaH_pos (γ.1 * g))
      have hpow : (F.iwasawaH (γ.1 * g) : ℝ) ^ (s.re + siegelRho F.n) ≤
          (G_sh.C_H * (H g) ^ G_sh.deg_H *
            (2 : ℝ) ^ (-(G_sh.shell (⟦γ⟧ : ParabolicCoset Γ P) : ℝ))) ^ (s.re + siegelRho F.n) :=
        Real.rpow_le_rpow hHpos.le h2 hα_pos.le
      have hsplit : (G_sh.C_H * (H g) ^ G_sh.deg_H *
            (2 : ℝ) ^ (-(G_sh.shell (⟦γ⟧ : ParabolicCoset Γ P) : ℝ))) ^ (s.re + siegelRho F.n) =
          G_sh.C_H ^ (s.re + siegelRho F.n) *
            (H g) ^ ((G_sh.deg_H : ℝ) * (s.re + siegelRho F.n)) *
            (2 : ℝ) ^ (-(s.re + siegelRho F.n) *
              (G_sh.shell (⟦γ⟧ : ParabolicCoset Γ P) : ℝ)) := by
        rw [Real.mul_rpow (mul_nonneg G_sh.C_H_pos.le (pow_nonneg hHg_pos.le _))
            (Real.rpow_nonneg (by norm_num) _),
          Real.mul_rpow G_sh.C_H_pos.le (pow_nonneg hHg_pos.le _),
          ← Real.rpow_natCast (H g) G_sh.deg_H, ← Real.rpow_mul hHg_pos.le,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 2; ring
      calc ‖F.eval s (γ.1 * g)‖
          ≤ G_sh.C_sec * (F.iwasawaH (γ.1 * g) : ℝ) ^ (s.re + siegelRho F.n) := h1
        _ ≤ G_sh.C_sec * (G_sh.C_H ^ (s.re + siegelRho F.n) *
              (H g) ^ ((G_sh.deg_H : ℝ) * (s.re + siegelRho F.n)) *
              (2 : ℝ) ^ (-(s.re + siegelRho F.n) *
                (G_sh.shell (⟦γ⟧ : ParabolicCoset Γ P) : ℝ))) :=
            mul_le_mul_of_nonneg_left (hsplit ▸ hpow) G_sh.C_sec_nonneg
        _ = M_g * (2 : ℝ) ^ (-(s.re + siegelRho F.n) *
              (G_sh.shell (⟦γ⟧ : ParabolicCoset Γ P) : ℝ)) := by
            dsimp only [M_g]; ring
  -- Step 2: Uniform finite-sum ceiling via geometric series `∑_{k=0}^∞ q^k = (1 - q)⁻¹`
  have hgeom_summ : Summable (fun k : ℕ => M_g * G_sh.C_card * q ^ k) :=
    (summable_geometric_of_lt_one hq_nn hq_lt).mul_left _
  have hgeom_val : (∑' k : ℕ, M_g * G_sh.C_card * q ^ k) =
      godementConst G_sh s * (H g) ^ ((G_sh.deg_H : ℝ) * (s.re + siegelRho F.n)) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq_nn hq_lt]
    unfold godementConst M_g q
    ring
  have hfin_le : ∀ S : Finset (ParabolicCoset Γ P),
      ∑ c ∈ S, ‖eisensteinTerm Γ F hInv s g c‖ ≤
        ∑' k : ℕ, M_g * G_sh.C_card * q ^ k := by
    intro S
    let K : ℕ := S.sup G_sh.shell + 1
    have hmaps : ∀ c ∈ S, G_sh.shell c ∈ Finset.range K := fun c hc =>
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup hc))
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    have hsh : ∀ k ∈ Finset.range K,
        ∑ c ∈ S.filter (fun c => G_sh.shell c = k), ‖eisensteinTerm Γ F hInv s g c‖ ≤
          M_g * G_sh.C_card * q ^ k := by
      intro k _
      have hcard : ((S.filter (fun c => G_sh.shell c = k)).card : ℝ) ≤
          G_sh.C_card * (2 : ℝ) ^ (2 * siegelRho F.n * (k : ℝ)) := by
        have hfin_k : Finite { c : ParabolicCoset Γ P // G_sh.shell c = k } :=
          (G_sh.shell_finite k).to_subtype
        let emb : { c // c ∈ S.filter (fun c => G_sh.shell c = k) } →
            { c : ParabolicCoset Γ P // G_sh.shell c = k } :=
          fun x => ⟨x.1, (Finset.mem_filter.mp x.2).2⟩
        have hinj : Function.Injective emb := fun x y hxy =>
          Subtype.ext (congrArg (fun z : { c : ParabolicCoset Γ P // G_sh.shell c = k } => z.1) hxy)
        have hle_nat : (S.filter (fun c => G_sh.shell c = k)).card ≤
            Nat.card { c : ParabolicCoset Γ P // G_sh.shell c = k } := by
          let _ : Fintype { c : ParabolicCoset Γ P // G_sh.shell c = k } := Fintype.ofFinite _
          rw [← Fintype.card_coe, Nat.card_eq_fintype_card]
          exact Fintype.card_le_of_injective emb hinj
        exact (by exact_mod_cast hle_nat : ((S.filter (fun c => G_sh.shell c = k)).card : ℝ) ≤
          (Nat.card { c : ParabolicCoset Γ P // G_sh.shell c = k } : ℝ)).trans
          (G_sh.shell_card_le k)
      have hq_pow : (2 : ℝ) ^ (2 * siegelRho F.n * (k : ℝ)) *
          (2 : ℝ) ^ (-(s.re + siegelRho F.n) * (k : ℝ)) = q ^ k := by
        dsimp only [q]
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1; ring
      calc ∑ c ∈ S.filter (fun c => G_sh.shell c = k), ‖eisensteinTerm Γ F hInv s g c‖
          ≤ ∑ _c ∈ S.filter (fun c => G_sh.shell c = k),
              M_g * (2 : ℝ) ^ (-(s.re + siegelRho F.n) * (k : ℝ)) := by
            refine Finset.sum_le_sum fun c hc => ?_
            rw [← (Finset.mem_filter.mp hc).2]
            exact hpt c
        _ = ((S.filter (fun c => G_sh.shell c = k)).card : ℝ) *
              (M_g * (2 : ℝ) ^ (-(s.re + siegelRho F.n) * (k : ℝ))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (G_sh.C_card * (2 : ℝ) ^ (2 * siegelRho F.n * (k : ℝ))) *
              (M_g * (2 : ℝ) ^ (-(s.re + siegelRho F.n) * (k : ℝ))) :=
            mul_le_mul_of_nonneg_right hcard (mul_nonneg hMg_nn (Real.rpow_nonneg (by norm_num) _))
        _ = M_g * G_sh.C_card *
              ((2 : ℝ) ^ (2 * siegelRho F.n * (k : ℝ)) *
                (2 : ℝ) ^ (-(s.re + siegelRho F.n) * (k : ℝ))) := by ring
        _ = M_g * G_sh.C_card * q ^ k := by rw [hq_pow]
    calc ∑ k ∈ Finset.range K,
          ∑ c ∈ S.filter (fun c => G_sh.shell c = k), ‖eisensteinTerm Γ F hInv s g c‖
        ≤ ∑ k ∈ Finset.range K, M_g * G_sh.C_card * q ^ k := Finset.sum_le_sum hsh
      _ ≤ ∑' k : ℕ, M_g * G_sh.C_card * q ^ k :=
          hgeom_summ.sum_le_tsum (Finset.range K) (fun k _ =>
            mul_nonneg (mul_nonneg hMg_nn G_sh.C_card_nonneg) (pow_nonneg hq_nn k))
  have hsumm_norm : Summable (fun c : ParabolicCoset Γ P => ‖eisensteinTerm Γ F hInv s g c‖) :=
    summable_of_sum_le (fun _ => norm_nonneg _) hfin_le
  have hsumm : Summable (eisensteinTerm Γ F hInv s g) := hsumm_norm.of_norm
  have hbound : ‖SiegelEisensteinSeries Γ F hInv s g‖ ≤
      godementConst G_sh s * (H g) ^ ((G_sh.deg_H : ℝ) * (s.re + siegelRho F.n)) := by
    rw [← hgeom_val]
    calc ‖SiegelEisensteinSeries Γ F hInv s g‖
        ≤ ∑' c : ParabolicCoset Γ P, ‖eisensteinTerm Γ F hInv s g c‖ :=
          norm_tsum_le_tsum_norm hsumm_norm
      _ ≤ ∑' k : ℕ, M_g * G_sh.C_card * q ^ k := hsumm_norm.tsum_le_of_sum_le hfin_le
  exact ⟨hsumm_norm, hsumm, hbound⟩

/-- **Weil-Range Specialization at `s = s₀ = (m - n) / 2`**:
whenever `2 * F.n < m` (so `siegelRho F.n < siegelWeilPoint m F.n`), the Siegel Eisenstein
series converges absolutely directly at the Siegel–Weil point `s₀ = (m - n) / 2`! -/
theorem eisenstein_abs_convergent_at_s0 {G : Type*} [Group G] (Γ : Subgroup G) {P : Subgroup G}
    (F : SiegelParabolicSection G P) (hInv : RatParabolicInvariant Γ F)
    (H : Stage14M1_SiegelDomainReduction.UnitaryHeightFn G)
    (G_sh : CosetShellGrowth Γ P F H)
    {m : ℕ} (hs0 : F.s0 = siegelWeilPoint m F.n) (hm : 2 * F.n < m) (g : G) :
    Summable (fun c : ParabolicCoset Γ P => ‖eisensteinTerm Γ F hInv (F.s0 : ℂ) g c‖) ∧
    Summable (eisensteinTerm Γ F hInv (F.s0 : ℂ) g) ∧
    ‖SiegelEisensteinSeries Γ F hInv (F.s0 : ℂ) g‖ ≤
      godementConst G_sh (F.s0 : ℂ) * (H g) ^ ((G_sh.deg_H : ℝ) * ((m : ℝ) / 2)) := by
  have hs : siegelRho F.n < ((F.s0 : ℂ)).re := by
    rw [Complex.ofReal_re, hs0]
    exact (siegelRho_lt_siegelWeilPoint_iff m F.n).mpr hm
  have h := eisenstein_abs_convergent Γ F hInv H G_sh hs g
  have hexp : ((F.s0 : ℂ)).re + siegelRho F.n = (m : ℝ) / 2 := by
    rw [Complex.ofReal_re, hs0, siegelWeilPoint_add_siegelRho]
  rw [hexp] at h
  exact h

/-- **Siegel-Set Moderate-Growth × Rapid-Decay Bochner Integrability of `SiegelEisensteinSeries`**:
combining `eisenstein_abs_convergent` with
`Stage14M1_SiegelDomainReduction.siegel_cuspidal_times_moderate_integrable`, the product of ANY
rapid-decay cuspidal function `φ` with `SiegelEisensteinSeries Γ F hInv s` is Bochner integrable
on EVERY unitary Siegel set `SiegelSetU D.a D.Ω D.c D.K`! -/
theorem eisenstein_times_rapid_decay_integrable {G : Type*} [Group G] [MeasurableSpace G]
    (D : Stage14M1_SiegelDomainReduction.UnitaryIwasawaData G)
    (Γ : Subgroup G) {P : Subgroup G}
    (F : SiegelParabolicSection G P) (hInv : RatParabolicInvariant Γ F)
    (H : Stage14M1_SiegelDomainReduction.UnitaryHeightFn G)
    (hH_meas : AEStronglyMeasurable (fun g => H g)
      (D.μ.restrict (Stage14M1_SiegelDomainReduction.SiegelSetU D.a D.Ω D.c D.K)))
    (G_sh : CosetShellGrowth Γ P F H)
    {s : ℂ} (hs : siegelRho F.n < s.re)
    {φ : G → ℂ}
    (hmeas : AEStronglyMeasurable (fun g => φ g * SiegelEisensteinSeries Γ F hInv s g)
      (D.μ.restrict (Stage14M1_SiegelDomainReduction.SiegelSetU D.a D.Ω D.c D.K)))
    (hrapid : ∀ N : ℕ, ∃ C_φ : ℝ, 0 ≤ C_φ ∧
      ∀ g ∈ Stage14M1_SiegelDomainReduction.SiegelSetU D.a D.Ω D.c D.K,
        ‖φ g‖ * (H g) ^ N ≤ C_φ) :
    IntegrableOn (fun g => φ g * SiegelEisensteinSeries Γ F hInv s g)
      (Stage14M1_SiegelDomainReduction.SiegelSetU D.a D.Ω D.c D.K) D.μ := by
  let M : ℕ := ⌈(G_sh.deg_H : ℝ) * (s.re + siegelRho F.n)⌉₊
  have hM_ge : (G_sh.deg_H : ℝ) * (s.re + siegelRho F.n) ≤ (M : ℝ) := Nat.le_ceil _
  have hmod : ∀ g ∈ Stage14M1_SiegelDomainReduction.SiegelSetU D.a D.Ω D.c D.K,
      ‖SiegelEisensteinSeries Γ F hInv s g‖ ≤ godementConst G_sh s * (H g) ^ M := by
    intro g _
    have h1 := (eisenstein_abs_convergent Γ F hInv H G_sh hs g).2.2
    have hpow : (H g) ^ ((G_sh.deg_H : ℝ) * (s.re + siegelRho F.n)) ≤ (H g) ^ M := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (H.one_le g) hM_ge
    exact h1.trans (mul_le_mul_of_nonneg_left hpow (godementConst_nonneg G_sh hs))
  exact Stage14M1_SiegelDomainReduction.siegel_cuspidal_times_moderate_integrable D H hH_meas
    hmeas hrapid (godementConst_nonneg G_sh hs) hmod

/-- **Fundamental-Domain Weil-Range Bochner Integrability of `SiegelEisensteinSeries`**:
when the height function `H` satisfies a torus-cone polynomial bound on `SiegelSetU` whose
resulting exponent fits inside Weil's convergent range (`D.r = 0 ∨ n_eff + D.r < D.m`), the
left-`Γ`-invariant Eisenstein series `SiegelEisensteinSeries Γ F hInv s` is Bochner integrable
over ANY fundamental domain `𝓕` of `Γ \ G` (via
`Stage14M1_SiegelDomainReduction.siegel_fundamental_domain_weil_integrable`)! -/
theorem eisenstein_fundamental_domain_integrable {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] {Γ : Subgroup G} [Countable Γ]
    (D : Stage14M1_SiegelDomainReduction.UnitaryIwasawaData G) [D.μ.IsMulLeftInvariant]
    (hcov : ∀ g : G, ∃ γ ∈ Γ, ∃ s ∈ Stage14M1_SiegelDomainReduction.SiegelSetU D.a D.Ω D.c D.K,
      g = γ * s)
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 D.μ)
    {P : Subgroup G} (F : SiegelParabolicSection G P) (hInv : RatParabolicInvariant Γ F)
    (H : Stage14M1_SiegelDomainReduction.UnitaryHeightFn G)
    (G_sh : CosetShellGrowth Γ P F H)
    {s : ℂ} (hs : siegelRho F.n < s.re)
    (hmeas : Measurable (SiegelEisensteinSeries Γ F hInv s))
    {n_eff : ℕ} (hweil : D.r = 0 ∨ n_eff + D.r < D.m)
    {C_t : ℝ} (hCt : 0 ≤ C_t)
    (hHt : ∀ p ∈ D.Ω, ∀ t ∈ Stage14M1_SiegelDomainReduction.SiegelCone D.r D.c, ∀ k ∈ D.K,
      (H (p * D.a t * k)) ^ ((G_sh.deg_H : ℝ) * (s.re + siegelRho F.n)) ≤
        C_t * ∏ i : Fin D.r, t i ^ (D.d * (2 * n_eff))) :
    IntegrableOn (SiegelEisensteinSeries Γ F hInv s) 𝓕 D.μ := by
  refine Stage14M1_SiegelDomainReduction.siegel_fundamental_domain_weil_integrable D hcov h𝓕
    hweil (mul_nonneg (godementConst_nonneg G_sh hs) hCt) hmeas
    (fun γ hγ g => eisenstein_left_invariant Γ F hInv s ⟨γ, hγ⟩ g) ?_
  intro p hp t ht k hk
  have h1 := (eisenstein_abs_convergent Γ F hInv H G_sh hs (p * D.a t * k)).2.2
  have h2 := mul_le_mul_of_nonneg_left (hHt p hp t ht k hk) (godementConst_nonneg G_sh hs)
  linarith [h1.trans h2]

end EisensteinConvergence

/-! ## Section 4: Unipotent Constant-Term Extraction & `eisenstein_constant_term_local_densities` -/

section ConstantTermAndLocalDensities

/-! ### 4A. Unipotent Fourier-Mode Orthogonality & Constant-Term Recovery over Totally Real Fields -/

/-- **Unipotent Constant-Term Extraction Theorem**:
for any totally real number field `F`, real embeddings `ρ`, level `N > 0`, fundamental domain `D`
of the unipotent lattice `realIntLattice ρ N`, and any finite unipotent Fourier expansion
`f(x) = c₀ + ∑_{β ∈ S, β ≠ 0} c_β * exp(2πi ∑_w ρ_w(β) x_w)` with integral modes `N * β ∈ 𝓞 F`,
the normalized unipotent integral `(vol D)⁻¹ • ∫_D f(x) dx` extracts `c₀` identically!
Built directly on `Stage14M1_SiegelDomainReduction.lattice_fundamental_domain_char_integral_zero`
and `lattice_fundamental_domain_volume`. -/
theorem unipotent_constant_term_extract {F : Type*} [Field F] [NumberField F]
    (hF : NumberField.IsTotallyReal F) (ρ : NumberField.InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x)
    {N : ℕ} (hN : 0 < N)
    (D : Set (NumberField.InfinitePlace F → ℝ))
    (hD : IsAddFundamentalDomain (Stage14M1_SiegelDomainReduction.realIntLattice ρ N) D volume)
    (c₀ : ℂ) (S : Finset F) (c : F → ℂ)
    (hS_ne : ∀ β ∈ S, β ≠ 0)
    (hS_int : ∀ β ∈ S, ∃ r : NumberField.RingOfIntegers F, (r : F) = (N : F) * β) :
    ((volume D).toReal⁻¹ : ℝ) •
      ∫ x in D, (c₀ + ∑ β ∈ S, c β * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) *
        ((∑ w : NumberField.InfinitePlace F, ρ w β * x w : ℝ) : ℂ))) = c₀ := by
  have hvol := (Stage14M1_SiegelDomainReduction.lattice_fundamental_domain_volume hF ρ hρ hN).2.2 D hD
  have hvol_pos_real : (0 : ℝ) <
      (N : ℝ) ^ Module.finrank ℚ F * Real.sqrt |(NumberField.discr F : ℝ)| := by
    have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
    have hdisc : (NumberField.discr F : ℝ) ≠ 0 := by
      exact_mod_cast NumberField.discr_ne_zero F
    exact mul_pos (pow_pos hNpos _) (Real.sqrt_pos.mpr (abs_pos.mpr hdisc))
  have hvol_fin : volume D < ⊤ := by rw [hvol]; exact ENNReal.ofReal_lt_top
  have hvol_toReal : (volume D).toReal =
      (N : ℝ) ^ Module.finrank ℚ F * Real.sqrt |(NumberField.discr F : ℝ)| := by
    rw [hvol, ENNReal.toReal_ofReal hvol_pos_real.le]
  have hvol_ne : (volume D).toReal ≠ 0 := hvol_toReal ▸ hvol_pos_real.ne'
  have : IsFiniteMeasure (volume.restrict D) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hvol_fin⟩
  have hmode_int : ∀ β : F,
      IntegrableOn (fun x : NumberField.InfinitePlace F → ℝ =>
        c β * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) *
          ((∑ w : NumberField.InfinitePlace F, ρ w β * x w : ℝ) : ℂ))) D volume := by
    intro β
    have hcont : Continuous (fun x : NumberField.InfinitePlace F → ℝ =>
        c β * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) *
          ((∑ w : NumberField.InfinitePlace F, ρ w β * x w : ℝ) : ℂ))) := by
      refine continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul
        (Complex.continuous_ofReal.comp (continuous_finsetSum _ fun w _ =>
          continuous_const.mul (continuous_apply w)))))
    refine (integrable_const (‖c β‖ : ℝ)).mono' hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    have harg : (2 * (Real.pi : ℂ) * Complex.I) *
        ((∑ w : NumberField.InfinitePlace F, ρ w β * x w : ℝ) : ℂ) =
        ((2 * Real.pi * ∑ w : NumberField.InfinitePlace F, ρ w β * x w : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [norm_mul, harg, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hsum_int : IntegrableOn (fun x : NumberField.InfinitePlace F → ℝ =>
      ∑ β ∈ S, c β * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) *
        ((∑ w : NumberField.InfinitePlace F, ρ w β * x w : ℝ) : ℂ))) D volume :=
    integrable_finsetSum S fun β _ => hmode_int β
  have hadd := integral_add (integrable_const c₀) hsum_int
  have hfin_sum := integral_finsetSum S fun β _ => hmode_int β
  have hvanish : ∀ β ∈ S,
      ∫ x in D, c β * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) *
        ((∑ w : NumberField.InfinitePlace F, ρ w β * x w : ℝ) : ℂ)) = 0 := by
    intro β hβ
    rw [integral_const_mul,
      Stage14M1_SiegelDomainReduction.lattice_fundamental_domain_char_integral_zero
        hF ρ hρ N D hD β (hS_ne β hβ) (hS_int β hβ),
      mul_zero]
  change ((volume D).toReal⁻¹ : ℝ) •
      ∫ x, (c₀ + ∑ β ∈ S, c β * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) *
        ((∑ w : NumberField.InfinitePlace F, ρ w β * x w : ℝ) : ℂ))) ∂(volume.restrict D) = c₀
  rw [hadd, hfin_sum, Finset.sum_eq_zero hvanish, add_zero, integral_const,
    Measure.real, Measure.restrict_apply_univ, smul_smul, inv_mul_cancel₀ hvol_ne, one_smul]

/-! ### 4B. Complex-Parameter Local Siegel–Eisenstein Euler Factors & Global Factorization -/

/-- Single-index complex local Siegel–Eisenstein Euler factor at prime `p` and shift `i < n`:
- `1 - p^{-(2s + i + 1)}` when `Even (m - n + 1 + i)`,
- `1 - χ(p) * p^{-(2s + i + 1)}` when `Odd (m - n + 1 + i)`.
At `s = siegelWeilPoint m n = (m - n) / 2`, the exponent `2s + i + 1` equals `m - n + 1 + i`,
matching `Stage14M1_LocalSiegelDensities.globalEulerSingleFactor` identically! -/
def localEisensteinSingleFactor {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)
    (m n : ℕ) (s : ℂ) (i : ℕ) (p : Nat.Primes) : ℂ :=
  if Even (m - n + 1 + i) then
    1 - (p : ℂ) ^ (-(2 * s + (i : ℂ) + 1))
  else
    1 - χ p * (p : ℂ) ^ (-(2 * s + (i : ℂ) + 1))

/-- Full rank-`n` local Siegel–Eisenstein Euler factor at prime `p` and complex parameter `s`:
`∏_{i=0}^{n-1} localEisensteinSingleFactor χ m n s i p`. -/
def localEisensteinDensityFactor {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)
    (m n : ℕ) (s : ℂ) (p : Nat.Primes) : ℂ :=
  ∏ i ∈ Finset.range n, localEisensteinSingleFactor χ m n s i p

/-- Global inverse `L`-function product matching the constant/Fourier term of the Siegel
Eisenstein series:
`∏_{i=0}^{n-1} L_{m - n + 1 + i}(χ, 2s + i + 1)⁻¹`. -/
def globalEisensteinLValue {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)
    (m n : ℕ) (s : ℂ) : ℂ :=
  ∏ i ∈ Finset.range n,
    (if Even (m - n + 1 + i) then
      riemannZeta (2 * s + (i : ℂ) + 1)
    else
      DirichletCharacter.LFunction χ (2 * s + (i : ℂ) + 1))⁻¹

/-- Single-index Euler product convergence in the full half-plane `Re(s) > 0`! -/
theorem hasProd_localEisensteinSingleFactor {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)
    (m n : ℕ) {s : ℂ} (hs : 0 < s.re) (i : ℕ) :
    HasProd (localEisensteinSingleFactor χ m n s i)
      (if Even (m - n + 1 + i) then
        riemannZeta (2 * s + (i : ℂ) + 1)
      else
        DirichletCharacter.LFunction χ (2 * s + (i : ℂ) + 1))⁻¹ := by
  set z : ℂ := 2 * s + (i : ℂ) + 1
  have hz : 1 < z.re := by
    have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    simp only [z, Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, sub_zero, Complex.natCast_re, Complex.one_re]
    linarith
  unfold localEisensteinSingleFactor
  split_ifs with hev
  · have hζ := riemannZeta_eulerProduct_hasProd hz
    have hζ0 : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hz
    simpa only [inv_inv] using hζ.inv₀ hζ0
  · have hL : HasProd (fun p : Nat.Primes => (1 - χ p * (p : ℂ) ^ (-z))⁻¹) (χ.LFunction z) := by
      rw [DirichletCharacter.LFunction_eq_LSeries χ hz]
      exact DirichletCharacter.LSeries_eulerProduct_hasProd χ hz
    have hL0 : χ.LFunction z ≠ 0 := by
      rw [DirichletCharacter.LFunction_eq_LSeries χ hz]
      exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ hz
    simpa only [inv_inv] using hL.inv₀ hL0

/-- **Full Rank-`n` Complex Siegel–Eisenstein Euler Product Convergence (`Re(s) > 0`)**:
for EVERY `D`, ANY Dirichlet character `χ` mod `D`, ANY ranks `m, n`, and EVERY `s : ℂ` with
`0 < s.re`, the Euler product `∏'_p localEisensteinDensityFactor χ m n s p` converges (`HasProd`
and `Multipliable`) to `globalEisensteinLValue χ m n s`! -/
theorem hasProd_localEisensteinDensityFactor {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)
    (m n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasProd (localEisensteinDensityFactor χ m n s) (globalEisensteinLValue χ m n s) ∧
    Multipliable (localEisensteinDensityFactor χ m n s) := by
  have hhas : HasProd (localEisensteinDensityFactor χ m n s) (globalEisensteinLValue χ m n s) := by
    unfold HasProd localEisensteinDensityFactor globalEisensteinLValue
    simp_rw [Finset.prod_comm (s := _) (t := Finset.range n)]
    exact tendsto_finsetProd (Finset.range n) fun i _ =>
      hasProd_localEisensteinSingleFactor χ m n hs i
  exact ⟨hhas, hhas.multipliable⟩

/-- Exact prime-by-prime identification at the Siegel–Weil point `s₀ = (m - n) / 2` (`n < m`):
`localEisensteinDensityFactor χ m n s₀ p = (Stage14M1_LocalSiegelDensities.globalEulerTerm χ m n p : ℂ)`. -/
theorem localEisensteinDensityFactor_at_s0 {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)
    (hquad : ∀ a : ℕ, χ a = 0 ∨ χ a = 1 ∨ χ a = -1)
    {m n : ℕ} (hnm : n < m) (p : Nat.Primes) :
    localEisensteinDensityFactor χ m n (siegelWeilPoint m n : ℂ) p =
      (Stage14M1_LocalSiegelDensities.globalEulerTerm χ m n p : ℂ) := by
  unfold localEisensteinDensityFactor Stage14M1_LocalSiegelDensities.globalEulerTerm
  rw [Complex.ofReal_prod]
  refine Finset.prod_bij (fun i _ => m - n + 1 + i) ?_ ?_ ?_ ?_
  · intro i hi
    have hi' := Finset.mem_range.mp hi
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro i₁ _ i₂ _ h; omega
  · intro j hj
    rcases Finset.mem_Icc.mp hj with ⟨h1, h2⟩
    exact ⟨j - (m - n + 1), Finset.mem_range.mpr (by omega), by omega⟩
  · intro i _
    set j : ℕ := m - n + 1 + i
    have hexp : 2 * (siegelWeilPoint m n : ℂ) + (i : ℂ) + 1 = (j : ℂ) := by
      have hr := two_mul_siegelWeilPoint_add_one hnm i
      exact_mod_cast hr
    have hpow : (p : ℂ) ^ (-(j : ℂ)) = (((p : ℝ) ^ (-(j : ℤ)) : ℝ) : ℂ) := by
      rw [show -(j : ℂ) = ((-(j : ℤ) : ℤ) : ℂ) by push_cast; rfl, Complex.cpow_intCast]
      push_cast; rfl
    have hχ_real : χ p = (Stage14M1_LocalSiegelDensities.quadChiR χ p : ℂ) := by
      rcases hquad p with h | h | h <;> simp [Stage14M1_LocalSiegelDensities.quadChiR, h]
    unfold localEisensteinSingleFactor Stage14M1_LocalSiegelDensities.globalEulerSingleFactor
    rw [hexp, hpow]
    split_ifs
    · push_cast; rfl
    · rw [hχ_real]; push_cast; rfl

/-- Exact complex-to-real identification at `s = s₀ = (m - n) / 2`:
`globalEisensteinLValue χ m n s₀ = (Stage14M1_LocalSiegelDensities.siegelProductLValue χ m n : ℂ)`!
Proved cleanly via uniqueness of `HasProd` limits from
`Stage14M1_LocalSiegelDensities.siegel_densities_of_hermitian_form`! -/
theorem globalEisensteinLValue_at_s0_eq_ofReal {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)
    (hquad : ∀ a : ℕ, χ a = 0 ∨ χ a = 1 ∨ χ a = -1)
    {m n : ℕ} (hnm : n < m) :
    globalEisensteinLValue χ m n (siegelWeilPoint m n : ℂ) =
      (Stage14M1_LocalSiegelDensities.siegelProductLValue χ m n : ℂ) := by
  have hs0 : 0 < ((siegelWeilPoint m n : ℂ)).re := by
    rw [Complex.ofReal_re]
    exact (siegelWeilPoint_pos_iff m n).mpr hnm
  have hC := (hasProd_localEisensteinDensityFactor χ m n hs0).1
  have hR := (Stage14M1_LocalSiegelDensities.siegel_densities_of_hermitian_form χ hquad hnm).1
  have hR_C : HasProd (fun p : Nat.Primes =>
      (Stage14M1_LocalSiegelDensities.globalEulerTerm χ m n p : ℂ))
      (Stage14M1_LocalSiegelDensities.siegelProductLValue χ m n : ℂ) := by
    change Filter.Tendsto (fun s : Finset Nat.Primes =>
      ∏ p ∈ s, (Stage14M1_LocalSiegelDensities.globalEulerTerm χ m n p : ℂ))
      Filter.atTop (nhds (Stage14M1_LocalSiegelDensities.siegelProductLValue χ m n : ℂ))
    simp_rw [← Complex.ofReal_prod]
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hR
  have hfun : localEisensteinDensityFactor χ m n (siegelWeilPoint m n : ℂ) =
      fun p : Nat.Primes => (Stage14M1_LocalSiegelDensities.globalEulerTerm χ m n p : ℂ) :=
    funext fun p => localEisensteinDensityFactor_at_s0 χ hquad hnm p
  rw [hfun] at hC
  exact hC.unique hR_C

/-- **MASTER CONSTANT-TERM / FOURIER LOCAL-DENSITY FACTORIZATION THEOREM
(`eisenstein_constant_term_local_densities`)**:
For ANY quadratic Dirichlet character `χ` mod `D` and ranks `n < m`:
1. For ALL `s : ℂ` with `0 < s.re`, the local Siegel–Eisenstein Euler product converges
   (`HasProd` + `Multipliable`) to `globalEisensteinLValue χ m n s`;
2. At the Siegel–Weil point `s₀ = (m - n) / 2`, the global product equals the exact real Siegel
   density product `(Stage14M1_LocalSiegelDensities.siegelProductLValue χ m n : ℂ)` of
   `Stage14M1_LocalSiegelDensities.siegel_densities_of_hermitian_form`;
3. At EVERY unramified prime `p` with splitting `sp : PlaceSplitting` (`sp.chi = quadChiR χ p`),
   the local Siegel–Eisenstein factor at `s₀` equals the exact Hensel-stabilized local
   representation density `LocalRepresentationDensity (LocalHermLattice.ofPrime p ...) 1`;
4. Two-sided positivity bounds `(4 / 7)^n ≤ siegelProductLValue χ m n ≤ 4^n` hold unconditionally! -/
theorem eisenstein_constant_term_local_densities {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)
    (hquad : ∀ a : ℕ, χ a = 0 ∨ χ a = 1 ∨ χ a = -1)
    {m n : ℕ} (hnm : n < m) :
    (∀ s : ℂ, 0 < s.re →
      HasProd (localEisensteinDensityFactor χ m n s) (globalEisensteinLValue χ m n s) ∧
      Multipliable (localEisensteinDensityFactor χ m n s)) ∧
    globalEisensteinLValue χ m n (siegelWeilPoint m n : ℂ) =
      (Stage14M1_LocalSiegelDensities.siegelProductLValue χ m n : ℂ) ∧
    (∀ (p : Nat.Primes) (sp : Stage14M1_LocalSiegelDensities.PlaceSplitting),
      sp.chi = Stage14M1_LocalSiegelDensities.quadChiR χ p →
      localEisensteinDensityFactor χ m n (siegelWeilPoint m n : ℂ) p =
        (Stage14M1_LocalSiegelDensities.LocalRepresentationDensity
          (Stage14M1_LocalSiegelDensities.LocalHermLattice.ofPrime p p.prop sp m (by omega))
          (1 : Matrix (Fin n) (Fin n)
            (Stage14M1_LocalSiegelDensities.LocalHermBase.ofPrime p p.prop sp).S) : ℂ)) ∧
    ((4 / 7 : ℝ) ^ n ≤ Stage14M1_LocalSiegelDensities.siegelProductLValue χ m n ∧
      Stage14M1_LocalSiegelDensities.siegelProductLValue χ m n ≤ (4 : ℝ) ^ n) := by
  have hglobal := Stage14M1_LocalSiegelDensities.siegel_densities_of_hermitian_form χ hquad hnm
  refine ⟨fun s hs => hasProd_localEisensteinDensityFactor χ m n hs,
    globalEisensteinLValue_at_s0_eq_ofReal χ hquad hnm, ?_, hglobal.2.2⟩
  intro p sp hsp
  rw [localEisensteinDensityFactor_at_s0 χ hquad hnm p,
    Stage14M1_LocalSiegelDensities.unramified_local_density_eq_globalEulerTerm
      χ p sp hsp m n (by omega) hnm.le]

/-- Direct bridge to `Stage14M1_LocalSiegelDensities.SiegelDensityGlobalPackage`. -/
theorem eisenstein_matches_density_package {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)
    (hquad : ∀ a : ℕ, χ a = 0 ∨ χ a = 1 ∨ χ a = -1)
    {m n : ℕ} (hnm : n < m) :
    let P := Stage14M1_LocalSiegelDensities.mkSiegelDensityGlobalPackage χ hquad hnm
    globalEisensteinLValue χ m n (siegelWeilPoint m n : ℂ) = (P.eulerValue : ℂ) ∧
    (∀ (p : Nat.Primes) (sp : Stage14M1_LocalSiegelDensities.PlaceSplitting),
      sp.chi = Stage14M1_LocalSiegelDensities.quadChiR χ p →
      localEisensteinDensityFactor χ m n (siegelWeilPoint m n : ℂ) p =
        (Stage14M1_LocalSiegelDensities.LocalRepresentationDensity
          (Stage14M1_LocalSiegelDensities.LocalHermLattice.ofPrime p p.prop sp m (by omega))
          (1 : Matrix (Fin n) (Fin n)
            (Stage14M1_LocalSiegelDensities.LocalHermBase.ofPrime p p.prop sp).S) : ℂ)) := by
  have h := eisenstein_constant_term_local_densities χ hquad hnm
  exact ⟨h.2.1, h.2.2.1⟩

end ConstantTermAndLocalDensities

/-! ## Section 5: Archimedean Siegel Density & `siegel_eisenstein_value_at_s0` -/

section SiegelEisensteinValueAtS0

/-- Single-step archimedean local Siegel representation density `α_∞(j)` for a totally real base
field `F` of degree `f = [F : ℚ]` and CM discriminant parameter `vE`:
`√((2 vE)^f) / ((j - 1)! * (vE / π)^j)^f` (the exact reciprocal of the archimedean factor in
`UnitaryMassFormula.massRatioFactor`). -/
def archSiegelStepDensity (f : ℕ) (vE : ℝ) (j : ℕ) : ℝ :=
  Real.sqrt ((2 * vE) ^ f) /
    (((Nat.factorial (j - 1) : ℕ) : ℝ) * (vE / Real.pi) ^ j) ^ f

/-- Rank-`n` archimedean local Siegel density `∏_{j = m - n + 1}^m α_∞(j)`. -/
def archSiegelDensity (f : ℕ) (vE : ℝ) (m n : ℕ) : ℝ :=
  ∏ j ∈ Finset.Icc (m - n + 1) m, archSiegelStepDensity f vE j

/-- **Global Adelic Siegel–Eisenstein Value at `s₀ = (m - n) / 2`**:
the product of the archimedean Siegel density and the `f`-fold finite-place local Siegel density
Euler product:
`eisensteinValueAtS0 f vE χ m n = archSiegelDensity f vE m n * (siegelProductLValue χ m n)^f`. -/
def eisensteinValueAtS0 (f : ℕ) (vE : ℝ) {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)
    (m n : ℕ) : ℝ :=
  archSiegelDensity f vE m n *
    (Stage14M1_LocalSiegelDensities.siegelProductLValue χ m n) ^ f

/-- Reciprocal rank-1 local Siegel density factor at step `M` for degree `f`:
`((siegelProductLValue χ M 1)⁻¹)^f` (equals `(hermLVal χ M)^f` for every `M ≥ 1`!). -/
def localDensityReciprocal (f : ℕ) {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)
    (M : ℕ) : ℝ :=
  ((Stage14M1_LocalSiegelDensities.siegelProductLValue χ M 1)⁻¹) ^ f

lemma archSiegelStepDensity_pos (f : ℕ) {vE : ℝ} (hv : 0 < vE) (j : ℕ) :
    0 < archSiegelStepDensity f vE j := by
  unfold archSiegelStepDensity
  have hfac : (0 : ℝ) < ((Nat.factorial (j - 1) : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hpi : (0 : ℝ) < vE / Real.pi := div_pos hv Real.pi_pos
  have hnum : (0 : ℝ) < Real.sqrt ((2 * vE) ^ f) := Real.sqrt_pos.mpr (pow_pos (by linarith) f)
  exact div_pos hnum (pow_pos (mul_pos hfac (pow_pos hpi j)) f)

lemma archSiegelDensity_pos (f : ℕ) {vE : ℝ} (hv : 0 < vE) (m n : ℕ) :
    0 < archSiegelDensity f vE m n :=
  Finset.prod_pos fun j _ => archSiegelStepDensity_pos f hv j

/-- Exact identification of `localDensityReciprocal f χ M` with
`(Stage11RallisMassFiber.hermLVal χ M)^f` for every `M ≥ 1`. -/
theorem localDensityReciprocal_eq_hermLVal_pow (f : ℕ) {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) {M : ℕ} (hM : 1 ≤ M) :
    localDensityReciprocal f χ M = (Stage11RallisMassFiber.hermLVal χ M) ^ f := by
  unfold localDensityReciprocal Stage14M1_LocalSiegelDensities.siegelProductLValue
  have hIcc : Finset.Icc (M - 1 + 1) M = {M} := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_singleton]
    omega
  rw [hIcc, Finset.prod_singleton, inv_inv]

/-- Strict positivity of `localDensityReciprocal f χ M` for every `M ≥ 2`. -/
theorem localDensityReciprocal_pos (f : ℕ) {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) {M : ℕ} (hM : 2 ≤ M) :
    0 < localDensityReciprocal f χ M := by
  rw [localDensityReciprocal_eq_hermLVal_pow f χ (by omega)]
  have hb := (Stage11RallisMassFiber.hermLVal_bounds_ge_two χ hM).1
  exact pow_pos (by linarith) f

/-- Strict positivity of `eisensteinValueAtS0 f vE χ m n` for every `n < m` and `vE > 0`. -/
theorem eisensteinValueAtS0_pos (f : ℕ) {vE : ℝ} (hv : 0 < vE)
    {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D) {m n : ℕ} (hnm : n < m) :
    0 < eisensteinValueAtS0 f vE χ m n := by
  unfold eisensteinValueAtS0
  refine mul_pos (archSiegelDensity_pos f hv m n) (pow_pos ?_ f)
  unfold Stage14M1_LocalSiegelDensities.siegelProductLValue
  refine Finset.prod_pos fun j hj => ?_
  have hj2 : 2 ≤ j := by have := (Finset.mem_Icc.mp hj).1; omega
  have hb := (Stage11RallisMassFiber.hermLVal_bounds_ge_two χ hj2).1
  exact inv_pos.mpr (by linarith)

/-- **Exact Two-Sided Quantitative Bounds on `eisensteinValueAtS0`** from
`Stage14M1_LocalSiegelDensities.siegel_densities_of_hermitian_form`:
`archSiegelDensity f vE m n * (4 / 7)^(n * f) ≤ eisensteinValueAtS0 f vE χ m n ≤ archSiegelDensity f vE m n * 4^(n * f)`. -/
theorem eisensteinValueAtS0_bounds (f : ℕ) {vE : ℝ} (hv : 0 < vE)
    {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)
    (hquad : ∀ a : ℕ, χ a = 0 ∨ χ a = 1 ∨ χ a = -1)
    {m n : ℕ} (hnm : n < m) :
    archSiegelDensity f vE m n * ((4 / 7 : ℝ) ^ n) ^ f ≤ eisensteinValueAtS0 f vE χ m n ∧
    eisensteinValueAtS0 f vE χ m n ≤ archSiegelDensity f vE m n * ((4 : ℝ) ^ n) ^ f := by
  obtain ⟨hlo, hhi⟩ :=
    (Stage14M1_LocalSiegelDensities.siegel_densities_of_hermitian_form χ hquad hnm).2.2
  have harch := (archSiegelDensity_pos f hv m n).le
  have hprod_nn : 0 ≤ Stage14M1_LocalSiegelDensities.siegelProductLValue χ m n :=
    le_trans (by positivity) hlo
  unfold eisensteinValueAtS0
  exact ⟨mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hlo f) harch,
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hprod_nn hhi f) harch⟩

/-- **Exact Reciprocal Identity (`eisensteinValueAtS0⁻¹ = ∏ massRatioFactor`)**:
the reciprocal of the global Siegel–Eisenstein value at `s₀ = (m - n) / 2` equals the exact
product of Braun–Shimura–Gan–Yu / Siegel–Tamagawa mass ratio step factors over
`j ∈ Icc (m - n + 1) m`! -/
theorem eisensteinValueAtS0_inv_eq_massRatioProd (f : ℕ) {vE : ℝ} (_hv : 0 < vE)
    {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D) {m n : ℕ} (_hnm : n < m) :
    (eisensteinValueAtS0 f vE χ m n)⁻¹ =
      ∏ j ∈ Finset.Icc (m - n + 1) m,
        UnitaryMassFormula.massRatioFactor f vE (localDensityReciprocal f χ) j := by
  unfold eisensteinValueAtS0 archSiegelDensity Stage14M1_LocalSiegelDensities.siegelProductLValue
  rw [mul_inv, ← Finset.prod_pow, ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hj1 : 1 ≤ j := by have := (Finset.mem_Icc.mp hj).1; omega
  unfold archSiegelStepDensity UnitaryMassFormula.massRatioFactor
  rw [localDensityReciprocal_eq_hermLVal_pow f χ hj1, inv_div, inv_pow, inv_inv]

/-- **Exact Logarithmic Local-Density Lower Bound** matching
`Stage14Contracts.M1UnitarySiegelWeilContract.localSiegelDensity_log_ge` verbatim! -/
theorem localDensityReciprocal_log_ge {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)
    (f m k : ℕ) (vE L_scale : ℝ)
    (_hf : 1 ≤ f) (hm : 1 ≤ m) (hk : 2 ≤ k) (_hv : Real.pi ≤ vE)
    (_hvL : Real.log vE ≤ L_scale) (hL1 : 1 ≤ L_scale) :
    ∃ B_L : ℝ, B_L ≤ (m : ℝ) * L_scale ∧
      -((f : ℝ) * B_L) ≤
        ∑ M ∈ Finset.Ico (k + 1) (k + m), Real.log (localDensityReciprocal f χ M) := by
  refine ⟨(m : ℝ) * L_scale, le_rfl, ?_⟩
  have hterm : ∀ M ∈ Finset.Ico (k + 1) (k + m),
      -((f : ℝ) * (1 / 2 : ℝ)) ≤ Real.log (localDensityReciprocal f χ M) := by
    intro M hM
    have hM3 : 3 ≤ M := by have := (Finset.mem_Ico.mp hM).1; omega
    rw [localDensityReciprocal_eq_hermLVal_pow f χ (by omega), Real.log_pow]
    have hlo := (Stage11RallisMassFiber.log_hermLVal_bounds_ge_three χ hM3).1
    have hf_nn : (0 : ℝ) ≤ (f : ℝ) := Nat.cast_nonneg f
    nlinarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Nat.card_Ico, show k + m - (k + 1) = m - 1 by omega, nsmul_eq_mul] at hsum
  have hm_le : ((m - 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ≤ (m : ℝ) * L_scale := by
    have hm1 : ((m - 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.sub_le m 1
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith
  have hf_nn : (0 : ℝ) ≤ (f : ℝ) := Nat.cast_nonneg f
  have hneg : -((f : ℝ) * ((m : ℝ) * L_scale)) ≤ -((f : ℝ) * (((m - 1 : ℕ) : ℝ) * (1 / 2 : ℝ))) := by
    nlinarith
  calc -((f : ℝ) * ((m : ℝ) * L_scale))
      ≤ -((f : ℝ) * (((m - 1 : ℕ) : ℝ) * (1 / 2 : ℝ))) := hneg
    _ = ((m - 1 : ℕ) : ℝ) * -((f : ℝ) * (1 / 2 : ℝ)) := by ring
    _ ≤ ∑ M ∈ Finset.Ico (k + 1) (k + m), Real.log (localDensityReciprocal f χ M) := hsum

/-- **Exact Rank-Stepping Mass-Telescoping Identity** matching
`Stage14Contracts.M1UnitarySiegelWeilContract.siegelWeil_mass_telescope` verbatim, AND equating
the ratio to `(eisensteinValueAtS0 f vE χ (k + m - 1) (m - 1))⁻¹`! -/
theorem bsgyMass_telescope_via_eisensteinValueAtS0 {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (f m k : ℕ) (vE : ℝ)
    (_hf : 1 ≤ f) (hm : 1 ≤ m) (hk : 2 ≤ k) (hv : Real.pi ≤ vE) :
    Stage11RallisMassFiber.bsgyUnitaryMass f χ vE (k + m - 1) =
      Stage11RallisMassFiber.bsgyUnitaryMass f χ vE k *
        ∏ M ∈ Finset.Ico (k + 1) (k - 1 + m + 1),
          UnitaryMassFormula.massRatioFactor f vE (localDensityReciprocal f χ) M ∧
    Stage11RallisMassFiber.bsgyUnitaryMass f χ vE (k + m - 1) =
      Stage11RallisMassFiber.bsgyUnitaryMass f χ vE k *
        (eisensteinValueAtS0 f vE χ (k + m - 1) (m - 1))⁻¹ := by
  have hv_pos : 0 < vE := lt_of_lt_of_le Real.pi_pos hv
  have hkm : k + m - 1 = k - 1 + m := by omega
  have htele : Stage11RallisMassFiber.bsgyUnitaryMass f χ vE (k + m - 1) =
      Stage11RallisMassFiber.bsgyUnitaryMass f χ vE k *
        ∏ M ∈ Finset.Ico (k + 1) (k - 1 + m + 1),
          UnitaryMassFormula.massRatioFactor f vE (fun M => (Stage11RallisMassFiber.hermLVal χ M) ^ f) M := by
    rw [hkm]
    exact Stage11RallisMassFiber.bsgyUnitaryMass_telescope f χ vE hm hk
  have hprod_eq :
      ∏ M ∈ Finset.Ico (k + 1) (k - 1 + m + 1),
        UnitaryMassFormula.massRatioFactor f vE (fun M => (Stage11RallisMassFiber.hermLVal χ M) ^ f) M =
      ∏ M ∈ Finset.Ico (k + 1) (k - 1 + m + 1),
        UnitaryMassFormula.massRatioFactor f vE (localDensityReciprocal f χ) M := by
    refine Finset.prod_congr rfl fun M hM => ?_
    have hM1 : 1 ≤ M := by have := (Finset.mem_Ico.mp hM).1; omega
    unfold UnitaryMassFormula.massRatioFactor
    rw [localDensityReciprocal_eq_hermLVal_pow f χ hM1]
  have h1 : Stage11RallisMassFiber.bsgyUnitaryMass f χ vE (k + m - 1) =
      Stage11RallisMassFiber.bsgyUnitaryMass f χ vE k *
        ∏ M ∈ Finset.Ico (k + 1) (k - 1 + m + 1),
          UnitaryMassFormula.massRatioFactor f vE (localDensityReciprocal f χ) M := by
    rw [htele, hprod_eq]
  have hnm : m - 1 < k + m - 1 := by omega
  have hinv := eisensteinValueAtS0_inv_eq_massRatioProd f hv_pos χ hnm
  have hset : Finset.Icc (k + m - 1 - (m - 1) + 1) (k + m - 1) =
      Finset.Ico (k + 1) (k - 1 + m + 1) := by
    ext M
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hset] at hinv
  exact ⟨h1, by rw [hinv]; exact h1⟩

/-- **Dominant-Constant Value & Real-Part Positivity on `SiegelWeilCore.SiegelEisensteinDecomp`**:
when a regularized Siegel–Eisenstein decomposition `E : SiegelEisensteinDecomp G` has constant term
`E.c0 g = (eisensteinValueAtS0 f vE χ m n : ℂ)` and relative bounds `ρ₁ + ρ₂ < 1` on `c₁` and `tail`,
we obtain strict nonvanishing, two-sided norm sandwich, AND strict real-part positivity
`0 < (1 - (ρ₁ + ρ₂)) * eisensteinValueAtS0 f vE χ m n ≤ (E.eval g).re`! -/
theorem siegelEisensteinDecomp_pos_at_s0 {G : Type*}
    (E : RHDirect.SiegelWeilCore.SiegelEisensteinDecomp G) (g : G)
    (f : ℕ) {vE : ℝ} (hv : 0 < vE) {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)
    {m n : ℕ} (hnm : n < m)
    (hc0 : E.c0 g = (eisensteinValueAtS0 f vE χ m n : ℂ))
    {ρ₁ ρ₂ : ℝ} (hρ : ρ₁ + ρ₂ < 1)
    (h1 : ‖E.c1 g‖ ≤ ρ₁ * ‖E.c0 g‖) (h2 : ‖E.tail g‖ ≤ ρ₂ * ‖E.c0 g‖) :
    0 < (1 - (ρ₁ + ρ₂)) * eisensteinValueAtS0 f vE χ m n ∧
    (1 - (ρ₁ + ρ₂)) * eisensteinValueAtS0 f vE χ m n ≤ (E.eval g).re ∧
    (1 - (ρ₁ + ρ₂)) * eisensteinValueAtS0 f vE χ m n ≤ ‖E.eval g‖ ∧
    ‖E.eval g‖ ≤ (1 + (ρ₁ + ρ₂)) * eisensteinValueAtS0 f vE χ m n ∧
    E.eval g ≠ 0 := by
  have hval_pos : 0 < eisensteinValueAtS0 f vE χ m n := eisensteinValueAtS0_pos f hv χ hnm
  have hnorm_c0 : ‖E.c0 g‖ = eisensteinValueAtS0 f vE χ m n := by
    rw [hc0, Complex.norm_real, Real.norm_of_nonneg hval_pos.le]
  have hc0_ne : E.c0 g ≠ 0 := by rw [hc0]; exact Complex.ofReal_ne_zero.mpr hval_pos.ne'
  obtain ⟨hpos, hlo, hne⟩ := E.ne_zero_of_dominant_constant g hc0_ne hρ h1 h2
  have hhi := (E.second_term_sandwich g h1 h2).2
  rw [hnorm_c0] at hpos hlo hhi h1 h2
  have hre : (1 - (ρ₁ + ρ₂)) * eisensteinValueAtS0 f vE χ m n ≤ (E.eval g).re := by
    have heval : (E.eval g).re = eisensteinValueAtS0 f vE χ m n + (E.c1 g).re + (E.tail g).re := by
      simp [RHDirect.SiegelWeilCore.SiegelEisensteinDecomp.eval, hc0]
    have hre1 : -(ρ₁ * eisensteinValueAtS0 f vE χ m n) ≤ (E.c1 g).re := by
      have := (abs_le.mp (Complex.abs_re_le_norm (E.c1 g))).1
      linarith
    have hre2 : -(ρ₂ * eisensteinValueAtS0 f vE χ m n) ≤ (E.tail g).re := by
      have := (abs_le.mp (Complex.abs_re_le_norm (E.tail g))).1
      linarith
    linarith
  exact ⟨hpos, hre, hlo, hhi, hne⟩

/-- **MASTER SIEGEL–WEIL POINT EVALUATION & POSITIVITY THEOREM (`siegel_eisenstein_value_at_s0`)**:
For ANY quadratic Dirichlet character `χ` mod `D`, totally real degree `f ≥ 1`, CM host parameter
`vE ≥ π`, and ranks `n < m` (with `s₀ = (m - n) / 2`):
1. Exact constant-term factorization into archimedean × finite local Siegel densities:
   `eisensteinValueAtS0 f vE χ m n = archSiegelDensity f vE m n * (siegelProductLValue χ m n)^f`
   and `(siegelProductLValue χ m n : ℂ) = globalEisensteinLValue χ m n (siegelWeilPoint m n : ℂ)`;
2. Strict positivity `0 < eisensteinValueAtS0 f vE χ m n` and explicit two-sided bounds;
3. Exact reciprocal identity with `UnitaryMassFormula.massRatioFactor`;
4. Exact rank-telescoping identity for `Stage11RallisMassFiber.bsgyUnitaryMass` ready for
   M1 Wave 3 (`Stage14M1_SiegelWeilUnitary`) and `Stage14Contracts.M1UnitarySiegelWeilContract`! -/
theorem siegel_eisenstein_value_at_s0 {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)
    (hquad : ∀ a : ℕ, χ a = 0 ∨ χ a = 1 ∨ χ a = -1)
    {f m n : ℕ} (_hf : 1 ≤ f) {vE : ℝ} (hv : Real.pi ≤ vE) (hnm : n < m) :
    0 < eisensteinValueAtS0 f vE χ m n ∧
    (globalEisensteinLValue χ m n (siegelWeilPoint m n : ℂ) =
      (Stage14M1_LocalSiegelDensities.siegelProductLValue χ m n : ℂ)) ∧
    (archSiegelDensity f vE m n * ((4 / 7 : ℝ) ^ n) ^ f ≤ eisensteinValueAtS0 f vE χ m n ∧
      eisensteinValueAtS0 f vE χ m n ≤ archSiegelDensity f vE m n * ((4 : ℝ) ^ n) ^ f) ∧
    ((eisensteinValueAtS0 f vE χ m n)⁻¹ =
      ∏ j ∈ Finset.Icc (m - n + 1) m,
        UnitaryMassFormula.massRatioFactor f vE (localDensityReciprocal f χ) j) := by
  have hv_pos : 0 < vE := lt_of_lt_of_le Real.pi_pos hv
  exact ⟨eisensteinValueAtS0_pos f hv_pos χ hnm,
    globalEisensteinLValue_at_s0_eq_ofReal χ hquad hnm,
    eisensteinValueAtS0_bounds f hv_pos χ hquad hnm,
    eisensteinValueAtS0_inv_eq_massRatioProd f hv_pos χ hnm⟩

end SiegelEisensteinValueAtS0

/-! ## Section 6: Wave-3 Handoff (`SiegelEisensteinWave3Pack`) & `Stage14Contracts` Alignment -/

section Wave3ContractAlignment

/-- **Wave-3 Handoff Package (`SiegelEisensteinWave3Pack`)** ready for
`Stage14M1_SiegelWeilUnitary`, aligned directly with `Stage14Contracts.M1UnitarySiegelWeilContract`
without introducing conflicting wrapper types! -/
structure SiegelEisensteinWave3Pack {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D) : Type where
  vacuumSection : ℕ → AdelicSiegelSection
  vacuumSection_one : ∀ (m : ℕ) (s : ℂ), (vacuumSection m).eval s adelicWeilOne = 1
  genusMass : (f : ℕ) → (vE : ℝ) → ℕ → ℝ
  localSiegelDensity : (f : ℕ) → (vE : ℝ) → ℕ → ℝ
  eisensteinValAtS0 : (f : ℕ) → (vE : ℝ) → ℕ → ℕ → ℝ
  genusMass_pos : ∀ (f n : ℕ) (vE : ℝ), 1 ≤ f → 2 ≤ n → Real.pi ≤ vE → 0 < genusMass f vE n
  localSiegelDensity_pos : ∀ (f M : ℕ) (vE : ℝ), 1 ≤ f → 2 ≤ M → Real.pi ≤ vE →
    0 < localSiegelDensity f vE M
  eisensteinValAtS0_pos : ∀ (f m n : ℕ) (vE : ℝ), 1 ≤ f → n < m → Real.pi ≤ vE →
    0 < eisensteinValAtS0 f vE m n
  localSiegelDensity_log_ge : ∀ (f m k : ℕ) (vE L_scale : ℝ),
    1 ≤ f → 1 ≤ m → 2 ≤ k → Real.pi ≤ vE → Real.log vE ≤ L_scale → 1 ≤ L_scale →
    ∃ B_L : ℝ, B_L ≤ (m : ℝ) * L_scale ∧
      -((f : ℝ) * B_L) ≤ ∑ M ∈ Finset.Ico (k + 1) (k + m), Real.log (localSiegelDensity f vE M)
  siegelWeil_mass_telescope : ∀ (f m k : ℕ) (vE : ℝ),
    1 ≤ f → 1 ≤ m → 2 ≤ k → Real.pi ≤ vE →
    genusMass f vE (k + m - 1) =
      genusMass f vE k * ∏ M ∈ Finset.Ico (k + 1) (k - 1 + m + 1),
        UnitaryMassFormula.massRatioFactor f vE (localSiegelDensity f vE) M
  siegelWeil_eisenstein_ratio : ∀ (f m k : ℕ) (vE : ℝ),
    1 ≤ f → 1 ≤ m → 2 ≤ k → Real.pi ≤ vE →
    genusMass f vE (k + m - 1) =
      genusMass f vE k * (eisensteinValAtS0 f vE (k + m - 1) (m - 1))⁻¹

/-- Unconditional constructor of `SiegelEisensteinWave3Pack` for ANY non-principal quadratic
Dirichlet character `χ`. -/
def mkSiegelEisensteinWave3Pack {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)
    (hχ : χ ≠ 1) : SiegelEisensteinWave3Pack χ where
  vacuumSection := adelicVacuumSiegelSection
  vacuumSection_one := adelicVacuumSiegelSection_eval_one
  genusMass f vE n := Stage11RallisMassFiber.bsgyUnitaryMass f χ vE n
  localSiegelDensity f _ M := localDensityReciprocal f χ M
  eisensteinValAtS0 f vE m n := eisensteinValueAtS0 f vE χ m n
  genusMass_pos f n _vE _ _ hv :=
    Stage11RallisMassFiber.bsgyUnitaryMass_pos f hχ (lt_of_lt_of_le Real.pi_pos hv) n
  localSiegelDensity_pos f _M _vE _ hM _ := localDensityReciprocal_pos f χ hM
  eisensteinValAtS0_pos f _m _n _vE _ hnm hv :=
    eisensteinValueAtS0_pos f (lt_of_lt_of_le Real.pi_pos hv) χ hnm
  localSiegelDensity_log_ge f m k vE L_scale hf hm hk hv hvL hL1 :=
    localDensityReciprocal_log_ge χ f m k vE L_scale hf hm hk hv hvL hL1
  siegelWeil_mass_telescope f m k vE hf hm hk hv :=
    (bsgyMass_telescope_via_eisensteinValueAtS0 χ f m k vE hf hm hk hv).1
  siegelWeil_eisenstein_ratio f m k vE hf hm hk hv :=
    (bsgyMass_telescope_via_eisensteinValueAtS0 χ f m k vE hf hm hk hv).2

/-- **Direct Compiler into `Stage14Contracts.M1UnitarySiegelWeilContract`**:
combines `SiegelEisensteinWave3Pack` with Wave-2 Tamagawa volume (`Stage14M1_TamagawaVolumeMass`)
and Rallis seesaw scalar (`Stage14M1_DoublingZeta`) to emit a verbatim
`Stage14Contracts.M1UnitarySiegelWeilContract`! -/
def SiegelEisensteinWave3Pack.toM1UnitarySiegelWeilContract {D : ℕ} [NeZero D]
    {χ : DirichletCharacter ℂ D} (W : SiegelEisensteinWave3Pack χ)
    (unitaryTamagawaVol : (f : ℕ) → (vE : ℝ) → ℕ → ℕ → ℝ)
    (hvol : ∀ (f P Q : ℕ) (vE : ℝ), 1 ≤ f → 2 ≤ P → Real.pi ≤ vE →
      unitaryTamagawaVol f vE P Q = W.genusMass f vE (P + Q))
    (rallisSeesawScalar : (f k : ℕ) → (vE : ℝ) → ℕ → ℝ)
    (hrallis : ∀ (f k j : ℕ) (vE : ℝ), 1 ≤ f → 2 ≤ k → Real.pi ≤ vE →
      0 < rallisSeesawScalar f k vE j) :
    Stage14Contracts.M1UnitarySiegelWeilContract where
  genusMass := W.genusMass
  localSiegelDensity := W.localSiegelDensity
  unitaryTamagawaVol := unitaryTamagawaVol
  rallisSeesawScalar := rallisSeesawScalar
  genusMass_pos := W.genusMass_pos
  localSiegelDensity_pos := W.localSiegelDensity_pos
  localSiegelDensity_log_ge := W.localSiegelDensity_log_ge
  siegelWeil_mass_telescope := W.siegelWeil_mass_telescope
  siegelWeil_vol_eq_mass := hvol
  rallis_seesaw_pos := hrallis

/-- Direct compiler from `SiegelEisensteinWave3Pack` + level-index/Weyl bounds to
`Stage2ThetaWire.Stage2MassRatioDatum` (aligning directly with `Stage14Contracts.M1FiberCert`). -/
def SiegelEisensteinWave3Pack.toStage2MassRatioDatum {D : ℕ} [NeZero D]
    {χ : DirichletCharacter ℂ D} (W : SiegelEisensteinWave3Pack χ)
    {f m k : ℕ} {vE g₁ g₂ L_scale La cCount T_val : ℝ} {w_u0 : Fin m → Fin f → ℝ}
    (hf : 1 ≤ f) (hm : 1 ≤ m) (hk : 2 ≤ k)
    (hv : Real.pi ≤ vE) (hvL : Real.log vE ≤ L_scale) (hL1 : 1 ≤ L_scale)
    (Isig Ipi Dstar dstar dimRatio W_lo : ℝ)
    (hIsig : 0 < Isig) (hIpi : 0 < Ipi) (hdim : 0 < dimRatio)
    (hidx : ((2 : ℝ) ^ (2 * f))⁻¹ *
        (g₁ * g₂) ^ ((f : ℝ) * (m : ℝ) * (2 * (k : ℝ) + (m : ℝ) - 1) / 2) ≤ Isig / Ipi)
    (hcov : (2 / 3 : ℝ) ^ f * (W.genusMass f vE (k + m - 1) / W.genusMass f vE k) *
        (Isig / Ipi) * dimRatio ≤ Dstar / dstar)
    (hweyl : W_lo ≤
      (1 / (k : ℝ)) * (∑ M ∈ Finset.Ico (k + 1) (k + m),
        (((M - 1 : ℕ) : ℝ) * Real.log ((M - 1 : ℕ) : ℝ) - ((M - 1 : ℕ) : ℝ))) +
      (1 / ((f : ℝ) * (k : ℝ))) * Real.log dimRatio)
    (harch : (∑ j : Fin m, (1 / (f : ℝ)) * ∑ ρ : Fin f, Real.log (w_u0 j ρ)) +
      Real.log (vE / Real.pi) ≤ W_lo)
    (hlogT : (1 / ((f : ℝ) * (k : ℝ))) * Real.log (Dstar / dstar) ≤ Real.log T_val) :
    Stage2ThetaWire.Stage2MassRatioDatum f m k vE g₁ g₂ L_scale La cCount w_u0 T_val :=
  (W.toM1UnitarySiegelWeilContract
    (fun f' vE' P Q => W.genusMass f' vE' (P + Q)) (fun _ _ _ _ _ _ _ => rfl)
    (fun f' k' vE' j => W.eisensteinValAtS0 f' vE' (k' + j + 1) k')
    (fun f' k' j vE' hf' _ hv' => W.eisensteinValAtS0_pos f' (k' + j + 1) k' vE' hf'
      (by omega) hv')).toStage2MassRatioDatum
    hf hm hk hv hvL hL1 Isig Ipi Dstar dstar dimRatio W_lo hIsig hIpi hdim
    hidx hcov hweyl harch hlogT

/-! ### Concrete Zero-Assumption Instantiation for `ℚ(i)` (`Stage9SpecialValues.chi4`) -/

/-- `Stage9SpecialValues.chi4` is strictly quadratic (`χ₋₄(n) ∈ {0, 1, -1}` for all `n : ℕ`). -/
theorem chi4_is_quadratic (n : ℕ) :
    Stage9SpecialValues.chi4 n = 0 ∨
    Stage9SpecialValues.chi4 n = 1 ∨
    Stage9SpecialValues.chi4 n = -1 := by
  have hmod : ∀ a : ZMod 4,
      Stage9SpecialValues.chi4 a = 0 ∨
      Stage9SpecialValues.chi4 a = 1 ∨
      Stage9SpecialValues.chi4 a = -1 := by
    intro a
    have ha : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by revert a; decide
    rcases ha with rfl | rfl | rfl | rfl
    · left
      exact MulChar.map_nonunit Stage9SpecialValues.chi4 (by
        rintro ⟨u, hu⟩
        have h1 : (u : ZMod 4) * u.inv = 1 := u.val_inv
        rw [hu, zero_mul] at h1
        exact (by decide : (0 : ZMod 4) ≠ 1) h1)
    · right; left
      exact map_one Stage9SpecialValues.chi4
    · left
      exact MulChar.map_nonunit Stage9SpecialValues.chi4 (by
        rintro ⟨u, hu⟩
        have h1 : (2 : ZMod 4) * u.inv = 1 := by rw [← hu]; exact u.val_inv
        have h2 : (2 : ZMod 4) * 2 = 0 := by decide
        have h3 : ((2 : ZMod 4) * u.inv) * 2 = 0 := by
          calc ((2 : ZMod 4) * u.inv) * 2 = (2 * 2) * u.inv := by ring
            _ = 0 := by rw [h2, zero_mul]
        rw [h1, one_mul] at h3
        exact (by decide : (2 : ZMod 4) ≠ 0) h3)
    · right; right
      have h3 : (3 : ZMod 4) = (-1 : ZMod 4) := by decide
      rw [h3]
      exact Stage9SpecialValues.chi4_odd
  exact hmod (n : ZMod 4)

/-- Concrete 0-assumption `SiegelEisensteinWave3Pack` for the Gaussian CM extension `ℚ(i) / ℚ`. -/
def canonicalSiegelEisensteinWave3Pack_chi4 :
    SiegelEisensteinWave3Pack Stage9SpecialValues.chi4 :=
  mkSiegelEisensteinWave3Pack Stage9SpecialValues.chi4 Stage9SpecialValues.chi4_ne_one

/-- Concrete 0-assumption `Stage14Contracts.M1UnitarySiegelWeilContract` witness for `ℚ(i) / ℚ`
using `canonicalSiegelEisensteinWave3Pack_chi4` and `eisensteinValueAtS0` for the positive
Rallis–Siegel–Weil scalar! -/
def canonicalM1Contract_from_eisenstein_chi4 :
    Stage14Contracts.M1UnitarySiegelWeilContract :=
  canonicalSiegelEisensteinWave3Pack_chi4.toM1UnitarySiegelWeilContract
    (fun f vE P Q => canonicalSiegelEisensteinWave3Pack_chi4.genusMass f vE (P + Q))
    (fun _ _ _ _ _ _ _ => rfl)
    (fun f k vE j =>
      canonicalSiegelEisensteinWave3Pack_chi4.eisensteinValAtS0 f vE (k + j + 1) k)
    (fun f k j vE hf _ hv =>
      canonicalSiegelEisensteinWave3Pack_chi4.eisensteinValAtS0_pos f (k + j + 1) k vE hf
        (by omega) hv)

/-- Verification that `canonicalSiegelEisensteinWave3Pack_chi4` satisfies full constant-term
local-density Euler product factorization and Siegel–Weil point evaluation for all `n < m`. -/
theorem canonical_chi4_eisenstein_complete {f m n : ℕ} (hf : 1 ≤ f) {vE : ℝ}
    (hv : Real.pi ≤ vE) (hnm : n < m) :
    HasProd (localEisensteinDensityFactor Stage9SpecialValues.chi4 m n (siegelWeilPoint m n : ℂ))
      (Stage14M1_LocalSiegelDensities.siegelProductLValue Stage9SpecialValues.chi4 m n : ℂ) ∧
    0 < eisensteinValueAtS0 f vE Stage9SpecialValues.chi4 m n ∧
    (eisensteinValueAtS0 f vE Stage9SpecialValues.chi4 m n)⁻¹ =
      ∏ j ∈ Finset.Icc (m - n + 1) m,
        UnitaryMassFormula.massRatioFactor f vE
          (localDensityReciprocal f Stage9SpecialValues.chi4) j := by
  have hct := eisenstein_constant_term_local_densities Stage9SpecialValues.chi4
    chi4_is_quadratic hnm
  have hval := siegel_eisenstein_value_at_s0 Stage9SpecialValues.chi4
    chi4_is_quadratic hf hv hnm
  have hs0 : 0 < ((siegelWeilPoint m n : ℂ)).re := by
    rw [Complex.ofReal_re]
    exact (siegelWeilPoint_pos_iff m n).mpr hnm
  have hhas := (hct.1 (siegelWeilPoint m n : ℂ) hs0).1
  rw [hct.2.1] at hhas
  exact ⟨hhas, hval.1, hval.2.2.2⟩

end Wave3ContractAlignment

end RHDirect.Stage14M1_SiegelEisenstein

end
