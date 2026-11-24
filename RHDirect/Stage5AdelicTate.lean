import RHDirect.Stage4ClassFieldTheory
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# RHDirect.Stage5AdelicTate

Concrete, self-contained, zero-`sorry`, zero-custom-`axiom` Lean 4 formalization of
**Adeles, Ideles, Normalized Local Absolute Values, the Unconditional Artin–Whaples
Product Formula, the Norm-1 Idele Class Group, and Local/Global Tate Zeta Integral
Factorization** directly on Mathlib's `NumberField.AdeleRing`,
`IsDedekindDomain.FiniteAdeleRing`, `NumberField.InfinitePlace`, and
`IsDedekindDomain.HeightOneSpectrum` in pure Mathlib `v4.33.1`.

## Contents

1. **Concrete Adele Ring `𝔸_K`, Idele Group `𝕀_K = 𝔸_Kˣ` & Diagonal Principal Embedding**:
   - Uses Mathlib's actual `NumberField.AdeleRing (𝓞 K) K = InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K`,
     defines the concrete idele group `Idele K := (Adele K)ˣ`, its infinite and finite
     projections (`ideleInf`, `ideleFin`, `ideleInfAt`, `ideleFinAt`), and characterizes
     adelic units (`isUnit_adele_iff`).
   - Diagonal principal embeddings `diagAdele : K →+* Adele K` and `principalIdele : Kˣ →* Idele K`
     (both proved injective), principal subgroup `principalSubgroup K ≤ Idele K`, and the global
     idele class group `IdeleClassGroup K := Idele K ⧸ principalSubgroup K`.
2. **Concrete Normalized Local Absolute Values `|·|_v` & `|·|_w`**:
   - At every finite place `v : HeightOneSpectrum (𝓞 K)` with residue cardinality
     `residueCard v = Nat.card (𝓞 K ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal > 1`, defines
     the additive `v`-adic order `finiteOrd v : v.adicCompletion K → ℤ` and normalized absolute
     value `finiteAbsVal v : v.adicCompletion K → ℝ`, proving
     `finiteAbsVal v x = (Nat.card (𝓞 K ⧸ v.asIdeal) : ℝ) ^ (-finiteOrd v x)` for `x ≠ 0`.
   - At every infinite place `w : InfinitePlace K`, defines the normalized absolute value
     `infAbsVal w x = ‖x‖ ^ w.mult` (`mult = 1` if real, `2` if complex), agreeing with
     `(w x) ^ w.mult` on `K`.
3. **Unconditional Artin–Whaples Product Formula & Norm-1 Idele Class Group `𝕀_K¹ / Kˣ`**:
   - Defines the global idelic norm homomorphism `ideleNorm : Idele K →* PosReal`
     (`|a|_𝔸 = (∏_w |a_w|_w) * (∏'_v |a_v|_v)`, well-defined by finite multiplicative support).
   - Proves **unconditionally (`0` assumptions)** for every number field `K` and every `x : Kˣ`:
     `ideleNorm (principalIdele K x) = 1` and the explicit product formula
     `(∏ w, (w x) ^ w.mult) * (∏ᶠ v, (Nat.card (𝓞 K ⧸ v.asIdeal) : ℝ) ^ (-finiteOrd v x)) = 1`.
   - Defines `NormOneIdeles K := (ideleNorm).ker`, proves `principalSubgroup K ≤ NormOneIdeles K`,
     defines `NormOneIdeleClassGroup K := NormOneIdeles K ⧸ principalInNormOne K`, proves
     the exact sequence `1 → NormOneIdeleClassGroup K → IdeleClassGroup K → PosReal → 1`
     (including surjectivity via the explicit multiplicative section `ideleNormSection`), and
     constructs the canonical direct-product splittings `ideleEquivNormOneProd : 𝕀_K ≃* 𝕀_K¹ × ℝ_{>0}`
     and `ideleClassEquivNormOneProd : 𝕀_K / Kˣ ≃* (𝕀_K¹ / Kˣ) × ℝ_{>0}`.
4. **Concrete Local Tate Zeta Integrals (Non-Archimedean & Archimedean)**:
   - Non-Archimedean: unramified local characters `IsUnramifiedLocalChar v χ`, uniformizer-independent
     Satake parameter `satakeParam v χ`, exact shell evaluation `χ(x) = α^{ord_v(x)}`, spherical
     local Tate zeta integral `Z_v(1_{𝒪_v}, χ_v, s) = (1 - χ_v(ϖ_v) q_v^{-s})⁻¹` via geometric
     series, plus shifted-shell and unit-shell formulas.
   - Archimedean: actual Lebesgue integrals over `ℝ` for the even Gaussian `e^{-π x²}`
     (`= π^{-s/2} Γ(s/2) = Complex.Gammaℝ s`), odd Gaussian `x e^{-π x²}` with `sign`
     (`= Complex.Gammaℝ (s + 1)`), complex-place radial Gaussian (`= 2 (2π)^{-s} Γ(s) = Complex.Gammaℂ s`),
     and the general number-field product `Gammaℝ(s)^{r₁} * Gammaℂ(s)^{r₂}`.
5. **Global Factorizable Tate Zeta Factorization**:
   - General number-field factorizable factorization away from a finite ramified set `S`.
   - Explicit prime–place bijection `heightOneIntEquivPrimes : HeightOneSpectrum ℤ ≃ Nat.Primes`
     preserving residue cardinality (`Nat.card (ℤ ⧸ v.asIdeal) = p`).
   - Exact global factorization over `ℚ` on `1 < s.re`:
     * Trivial character: `Z_∞(e^{-π x²}, 1, s) * ∏'_v Z_v(1_{ℤ_v}, 1, s) = completedRiemannZeta s`,
       with Tate functional equation `completedRiemannZeta (1 - s) = completedRiemannZeta s`.
     * Arbitrary Dirichlet character `χ : DirichletCharacter ℂ N`:
       `Z_∞(χ, s) * ∏'_v Z_v(χ, s) = DirichletCharacter.completedLFunction χ s`,
       with finite part equal to `DirichletCharacter.LFunction χ s` and direct bridge to
       `Stage4ClassFieldTheory.artinLSeries`.

Zero `sorry`, zero custom `axiom`s.
-/

noncomputable section

open Complex MeasureTheory NumberField IsDedekindDomain
open scoped BigOperators NumberField NNReal Topology Real RestrictedProduct

namespace RHDirect.Stage5AdelicTate

/-! ## Section 1: Concrete Adele Ring `𝔸_K`, Idele Group `𝕀_K = 𝔸_Kˣ` & Principal Embedding -/

section AdeleIdele

variable (K : Type*) [Field K]

/-- The infinite adele ring `K_∞ = ∏_{w∣∞} K_w` of `K`. -/
abbrev InfAdele : Type _ := NumberField.InfiniteAdeleRing K

/-- The infinite idele group `K_∞ˣ`. -/
abbrev InfIdele : Type _ := (InfAdele K)ˣ

variable [NumberField K]

/-- The finite adele ring `𝔸_{K,f} = ∏'_v (K_v, 𝒪_v)` of a number field `K`. -/
abbrev FinAdele : Type _ := IsDedekindDomain.FiniteAdeleRing (𝓞 K) K

/-- The full adele ring `𝔸_K = K_∞ × 𝔸_{K,f}` of a number field `K`. -/
abbrev Adele : Type _ := NumberField.AdeleRing (𝓞 K) K

/-- The finite idele group `𝕀_{K,f} = 𝔸_{K,f}ˣ`. -/
abbrev FinIdele : Type _ := (FinAdele K)ˣ

/-- The full idele group `𝕀_K = 𝔸_Kˣ` of a number field `K`. -/
abbrev Idele : Type _ := (Adele K)ˣ

/-- Canonical ring isomorphism identifying `Adele K` with `InfAdele K × FinAdele K`. -/
def adeleEquivProd : Adele K ≃+* InfAdele K × FinAdele K := RingEquiv.refl _

/-- Canonical group isomorphism `𝕀_K ≃* K_∞ˣ × 𝕀_{K,f}` splitting an idele into its
infinite and finite parts. -/
def ideleEquivProd : Idele K ≃* InfIdele K × FinIdele K :=
  (Units.mapEquiv (adeleEquivProd K).toMulEquiv).trans MulEquiv.prodUnits

/-- Projection from the full idele group `𝕀_K` to the infinite idele group `K_∞ˣ`. -/
def ideleInf : Idele K →* InfIdele K :=
  (MonoidHom.fst (InfIdele K) (FinIdele K)).comp (ideleEquivProd K).toMonoidHom

/-- Projection from the full idele group `𝕀_K` to the finite idele group `𝕀_{K,f}`. -/
def ideleFin : Idele K →* FinIdele K :=
  (MonoidHom.snd (InfIdele K) (FinIdele K)).comp (ideleEquivProd K).toMonoidHom

@[simp]
theorem ideleInf_val (a : Idele K) : ((ideleInf K a : InfIdele K) : InfAdele K) = a.1.1 := rfl

@[simp]
theorem ideleFin_val (a : Idele K) : ((ideleFin K a : FinIdele K) : FinAdele K) = a.1.2 := rfl

/-- Local infinite component homomorphism `𝕀_K →* K_wˣ` at an infinite place `w`. -/
def ideleInfAt (w : InfinitePlace K) : Idele K →* (w.Completion)ˣ :=
  ((Pi.evalMonoidHom (fun v : InfinitePlace K ↦ (v.Completion)ˣ) w).comp
    MulEquiv.piUnits.toMonoidHom).comp (ideleInf K)

@[simp]
theorem ideleInfAt_val (w : InfinitePlace K) (a : Idele K) :
    ((ideleInfAt K w a : (w.Completion)ˣ) : w.Completion) = a.1.1 w := rfl

/-- Local finite component homomorphism `𝕀_K →* K_vˣ` at a finite place `v`. -/
def ideleFinAt (v : HeightOneSpectrum (𝓞 K)) : Idele K →* (v.adicCompletion K)ˣ :=
  ((Pi.evalMonoidHom (fun u : HeightOneSpectrum (𝓞 K) ↦ (u.adicCompletion K)ˣ) v).comp
    RestrictedProduct.coeUnits).comp (ideleFin K)

@[simp]
theorem ideleFinAt_val (v : HeightOneSpectrum (𝓞 K)) (a : Idele K) :
    ((ideleFinAt K v a : (v.adicCompletion K)ˣ) : v.adicCompletion K) = a.1.2 v := rfl

/-- Extensionality for ideles via their local infinite and finite components. -/
theorem idele_ext {a b : Idele K}
    (hinf : ∀ w : InfinitePlace K, ideleInfAt K w a = ideleInfAt K w b)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), ideleFinAt K v a = ideleFinAt K v b) :
    a = b := by
  apply Units.ext
  apply Prod.ext
  · funext w
    exact congrArg Units.val (hinf w)
  · apply FiniteAdeleRing.ext
    intro v
    exact congrArg Units.val (hfin v)

/-- Every idele has `v`-adic valuation equal to `1` at all but finitely many finite places `v`. -/
theorem ideleFinAt_eventually_valued_eq_one (a : Idele K) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      Valued.v ((ideleFinAt K v a : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
  filter_upwards [FiniteAdeleRing.unitsEquiv_finite_valued_eq_one (ideleFin K a)] with v hv
  exact hv

/-- Explicit characterization of units in the full adele ring `𝔸_K`:
an adele `a = (a_∞, a_f)` is an idele iff every infinite component `a_w ≠ 0`, every finite
component `a_v ≠ 0`, and `Valued.v (a_v) = 1` for all but finitely many finite places `v`. -/
theorem isUnit_adele_iff (a : Adele K) :
    IsUnit a ↔
      (∀ w : InfinitePlace K, a.1 w ≠ 0) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), a.2 v ≠ 0) ∧
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, Valued.v (a.2 v) = 1) := by
  have h0 : IsUnit a ↔ IsUnit (adeleEquivProd K a) :=
    ⟨fun h ↦ h.map (adeleEquivProd K).toMonoidHom,
     fun h ↦ by simpa using h.map (adeleEquivProd K).symm.toMonoidHom⟩
  have h1 : IsUnit (adeleEquivProd K a).1 ↔ ∀ w : InfinitePlace K, a.1 w ≠ 0 := by
    let eInf : InfAdele K ≃+* ((w : InfinitePlace K) → w.Completion) := RingEquiv.refl _
    have h1' : IsUnit (adeleEquivProd K a).1 ↔ IsUnit (eInf (adeleEquivProd K a).1) :=
      ⟨fun h ↦ h.map eInf.toMonoidHom,
       fun h ↦ by simpa using h.map eInf.symm.toMonoidHom⟩
    rw [h1', Pi.isUnit_iff]
    simp only [isUnit_iff_ne_zero]
    rfl
  have h2 : IsUnit (adeleEquivProd K a).2 ↔
      (∀ v : HeightOneSpectrum (𝓞 K), a.2 v ≠ 0) ∧
      (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, Valued.v (a.2 v) = 1) :=
    FiniteAdeleRing.isUnit_iff
  rw [h0, Prod.isUnit_iff, h1, h2]

/-- The diagonal embedding `K →+* 𝔸_K` sending `x` to the constant tuple `(x)_v`. -/
def diagAdele : K →+* Adele K := algebraMap K (Adele K)

theorem diagAdele_injective : Function.Injective (diagAdele K) :=
  NumberField.AdeleRing.algebraMap_injective (𝓞 K) K

@[simp]
theorem diagAdele_inf_apply (x : K) (w : InfinitePlace K) :
    (diagAdele K x).1 w = (x : w.Completion) := rfl

@[simp]
theorem diagAdele_fin_apply (x : K) (v : HeightOneSpectrum (𝓞 K)) :
    (diagAdele K x).2 v = (x : v.adicCompletion K) := rfl

/-- The diagonal principal idele embedding `Kˣ →* 𝕀_K`. -/
def principalIdele : Kˣ →* Idele K := Units.map (diagAdele K).toMonoidHom

theorem principalIdele_injective : Function.Injective (principalIdele K) :=
  Units.map_injective (diagAdele_injective K)

@[simp]
theorem principalIdele_infAt_val (x : Kˣ) (w : InfinitePlace K) :
    ((ideleInfAt K w (principalIdele K x) : (w.Completion)ˣ) : w.Completion) =
      ((x : K) : w.Completion) := rfl

@[simp]
theorem principalIdele_finAt_val (x : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ((ideleFinAt K v (principalIdele K x) : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      ((x : K) : v.adicCompletion K) := rfl

/-- The subgroup of principal ideles `Kˣ ↪ 𝕀_K`. -/
def principalSubgroup : Subgroup (Idele K) := (principalIdele K).range

theorem mem_principalSubgroup_iff (a : Idele K) :
    a ∈ principalSubgroup K ↔ ∃ x : Kˣ, principalIdele K x = a := Iff.rfl

/-- The global idele class group `ℂ_K = 𝕀_K / Kˣ` of a number field `K`. -/
abbrev IdeleClassGroup : Type _ := Idele K ⧸ principalSubgroup K

end AdeleIdele

/-! ## Section 2: Concrete Normalized Local Absolute Values `|·|_v` & `|·|_w` -/

section LocalAbsoluteValues

variable {K : Type*} [Field K] [NumberField K]

/-- Residue field cardinality `q_v = #(𝒪_K ⧸ v) = Ideal.absNorm v.asIdeal` at a finite place `v`. -/
def residueCard (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  Nat.card (𝓞 K ⧸ v.asIdeal)

theorem residueCard_eq_absNorm (v : HeightOneSpectrum (𝓞 K)) :
    residueCard v = Ideal.absNorm v.asIdeal := rfl

theorem one_lt_residueCard (v : HeightOneSpectrum (𝓞 K)) : 1 < residueCard v := by
  rw [residueCard_eq_absNorm]
  exact NumberField.HeightOneSpectrum.one_lt_absNorm v

theorem residueCard_pos (v : HeightOneSpectrum (𝓞 K)) : 0 < residueCard v :=
  Nat.zero_lt_one.trans (one_lt_residueCard v)

theorem residueCard_ne_zero (v : HeightOneSpectrum (𝓞 K)) : residueCard v ≠ 0 :=
  (residueCard_pos v).ne'

/-- Additive `v`-adic valuation `ord_v : K_v → ℤ` (with `ord_v(0) = 0` and `ord_v(ϖ_v) = 1`),
defined by `ord_v(x) = -WithZero.log (Valued.v x)`. -/
def finiteOrd (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) : ℤ :=
  -WithZero.log (Valued.v x)

@[simp]
theorem finiteOrd_zero (v : HeightOneSpectrum (𝓞 K)) :
    finiteOrd v (0 : v.adicCompletion K) = 0 := by
  simp [finiteOrd]

@[simp]
theorem finiteOrd_one (v : HeightOneSpectrum (𝓞 K)) :
    finiteOrd v (1 : v.adicCompletion K) = 0 := by
  simp [finiteOrd]

theorem finiteOrd_mul (v : HeightOneSpectrum (𝓞 K)) {x y : v.adicCompletion K}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    finiteOrd v (x * y) = finiteOrd v x + finiteOrd v y := by
  have hvx : (Valued.v x : WithZero (Multiplicative ℤ)) ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  have hvy : (Valued.v y : WithZero (Multiplicative ℤ)) ≠ 0 := (Valuation.ne_zero_iff _).mpr hy
  simp only [finiteOrd, map_mul, WithZero.log_mul hvx hvy, neg_add]

theorem finiteOrd_inv (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    finiteOrd v x⁻¹ = -finiteOrd v x := by
  simp [finiteOrd]

theorem finiteOrd_zpow (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) (n : ℤ) :
    finiteOrd v ((x ^ n : (v.adicCompletion K)ˣ) : v.adicCompletion K) = n * finiteOrd v x := by
  simp only [finiteOrd, Units.val_zpow_eq_zpow_val, map_zpow₀, WithZero.log_zpow, zsmul_eq_mul,
    mul_neg, Int.cast_id]

theorem finiteOrd_eq_zero_iff_valued_eq_one (v : HeightOneSpectrum (𝓞 K))
    {x : v.adicCompletion K} (hx : x ≠ 0) :
    finiteOrd v x = 0 ↔ Valued.v x = 1 := by
  have hvx : (Valued.v x : WithZero (Multiplicative ℤ)) ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  simp only [finiteOrd, neg_eq_zero]
  constructor
  · intro h
    rw [← WithZero.exp_log hvx, h, WithZero.exp_zero]
  · intro h
    rw [h, WithZero.log_one]

/-- For every nonzero algebraic integer `r ∈ 𝒪_K`, `finiteOrd v r` equals the exact ideal
multiplicity `multiplicity v.asIdeal (Ideal.span {r})`. -/
theorem finiteOrd_of_int (v : HeightOneSpectrum (𝓞 K)) {r : 𝓞 K} (hr : r ≠ 0) :
    finiteOrd v ((r : K) : v.adicCompletion K) =
      (multiplicity v.asIdeal (Ideal.span {r}) : ℤ) := by
  unfold finiteOrd
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    RingOfIntegers.coe_eq_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity v hr, WithZero.log_exp, neg_neg]

/-- Normalized non-Archimedean absolute value `|·|_v` on the completion `K_v`. -/
def finiteAbsVal (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) : ℝ := ‖x‖

@[simp]
theorem finiteAbsVal_zero (v : HeightOneSpectrum (𝓞 K)) :
    finiteAbsVal v (0 : v.adicCompletion K) = 0 := norm_zero

@[simp]
theorem finiteAbsVal_one (v : HeightOneSpectrum (𝓞 K)) :
    finiteAbsVal v (1 : v.adicCompletion K) = 1 := norm_one

theorem finiteAbsVal_mul (v : HeightOneSpectrum (𝓞 K)) (x y : v.adicCompletion K) :
    finiteAbsVal v (x * y) = finiteAbsVal v x * finiteAbsVal v y := norm_mul x y

theorem finiteAbsVal_inv (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    finiteAbsVal v x⁻¹ = (finiteAbsVal v x)⁻¹ := norm_inv x

theorem finiteAbsVal_nonneg (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K) :
    0 ≤ finiteAbsVal v x := norm_nonneg x

theorem finiteAbsVal_pos_of_ne_zero (v : HeightOneSpectrum (𝓞 K)) {x : v.adicCompletion K}
    (hx : x ≠ 0) : 0 < finiteAbsVal v x := norm_pos_iff.mpr hx

/-- Exact closed formula for the normalized finite absolute value:
for every nonzero `x ∈ K_v`,
`|x|_v = (Nat.card (𝒪_K ⧸ v.asIdeal) : ℝ) ^ (-finiteOrd v x)`. -/
theorem finiteAbsVal_eq_residueCard_zpow (v : HeightOneSpectrum (𝓞 K)) {x : v.adicCompletion K}
    (hx : x ≠ 0) :
    finiteAbsVal v x = (Nat.card (𝓞 K ⧸ v.asIdeal) : ℝ) ^ (-finiteOrd v x) := by
  have hvx : (Valued.v x : WithZero (Multiplicative ℤ)) ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  rw [finiteAbsVal, NumberField.FinitePlace.norm_def,
    WithZeroMulInt.toNNReal_neg_apply (NumberField.HeightOneSpectrum.absNorm_ne_zero v) hvx,
    WithZero.toAdd_unzero_eq_log hvx]
  simp only [finiteOrd, neg_neg, NNReal.coe_zpow, NNReal.coe_natCast]
  rfl

theorem finiteAbsVal_eq_one_iff_valued_eq_one (v : HeightOneSpectrum (𝓞 K))
    (x : v.adicCompletion K) :
    finiteAbsVal v x = 1 ↔ Valued.v x = 1 := by
  rw [finiteAbsVal, NumberField.FinitePlace.norm_def]
  have h1 : (Ideal.absNorm v.asIdeal : ℝ≥0) ≠ 1 :=
    (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v).ne'
  rw [← NNReal.coe_one, NNReal.coe_inj]
  exact WithZeroMulInt.toNNReal_eq_one_iff _ (NumberField.HeightOneSpectrum.absNorm_ne_zero v) h1

/-- Compatibility of `finiteAbsVal v` on `K ↪ K_v` with Mathlib's `NumberField.FinitePlace.mk v`. -/
theorem finiteAbsVal_coe_eq_finitePlace (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    finiteAbsVal v (x : v.adicCompletion K) = NumberField.FinitePlace.mk v x := rfl

/-- Ultrametric inequality for `finiteAbsVal v` on `K`. -/
theorem finiteAbsVal_add_le_max_coe (v : HeightOneSpectrum (𝓞 K)) (x y : K) :
    finiteAbsVal v ((x + y : K) : v.adicCompletion K) ≤
      max (finiteAbsVal v (x : v.adicCompletion K)) (finiteAbsVal v (y : v.adicCompletion K)) := by
  simp only [finiteAbsVal_coe_eq_finitePlace]
  exact NumberField.FinitePlace.add_le (NumberField.FinitePlace.mk v) x y

end LocalAbsoluteValues

section LocalAbsoluteValuesInf

variable {K : Type*} [Field K]

/-- Normalized Archimedean absolute value `|·|_w` on the completion `K_w`:
`|x|_w = ‖x‖ ^ w.mult`, where `w.mult = 1` if `w` is real and `w.mult = 2` if `w` is complex. -/
def infAbsVal (w : InfinitePlace K) (x : w.Completion) : ℝ := ‖x‖ ^ w.mult

@[simp]
theorem infAbsVal_zero (w : InfinitePlace K) : infAbsVal w (0 : w.Completion) = 0 := by
  simp [infAbsVal, zero_pow w.mult_ne_zero]

@[simp]
theorem infAbsVal_one (w : InfinitePlace K) : infAbsVal w (1 : w.Completion) = 1 := by
  simp [infAbsVal]

theorem infAbsVal_mul (w : InfinitePlace K) (x y : w.Completion) :
    infAbsVal w (x * y) = infAbsVal w x * infAbsVal w y := by
  simp [infAbsVal, norm_mul, mul_pow]

theorem infAbsVal_inv (w : InfinitePlace K) (x : w.Completion) :
    infAbsVal w x⁻¹ = (infAbsVal w x)⁻¹ := by
  simp [infAbsVal, norm_inv, inv_pow]

theorem infAbsVal_nonneg (w : InfinitePlace K) (x : w.Completion) :
    0 ≤ infAbsVal w x := pow_nonneg (norm_nonneg x) _

theorem infAbsVal_pos_of_ne_zero (w : InfinitePlace K) {x : w.Completion} (hx : x ≠ 0) :
    0 < infAbsVal w x := pow_pos (norm_pos_iff.mpr hx) _

theorem infAbsVal_of_isReal {w : InfinitePlace K} (hw : w.IsReal) (x : w.Completion) :
    infAbsVal w x = ‖x‖ := by
  simp [infAbsVal, hw.mult_eq_one]

theorem infAbsVal_of_isComplex {w : InfinitePlace K} (hw : w.IsComplex) (x : w.Completion) :
    infAbsVal w x = ‖x‖ ^ 2 := by
  simp [infAbsVal, hw.mult_eq_two]

/-- On `K ↪ K_w`, `infAbsVal w` equals `(w x) ^ w.mult`. -/
theorem infAbsVal_coe_eq (w : InfinitePlace K) (x : K) :
    infAbsVal w (x : w.Completion) = (w x) ^ w.mult := by
  unfold infAbsVal
  have hnorm : ‖(x : w.Completion)‖ = w x := by
    simpa using NumberField.InfinitePlace.Completion.norm_coe w ((WithAbs.equiv w.1).symm x)
  rw [hnorm]

end LocalAbsoluteValuesInf

/-! ## Section 3: Idelic Norm, Unconditional Artin–Whaples Product Formula & Norm-1 Idele Class Group -/

section ProductFormula

/-- The multiplicative group `ℝ_{>0}` of strictly positive real numbers. -/
abbrev PosReal : Type := { r : ℝ // 0 < r }

instance : CommGroup PosReal where
  one := ⟨1, zero_lt_one⟩
  mul x y := ⟨x.1 * y.1, mul_pos x.2 y.2⟩
  inv x := ⟨x.1⁻¹, inv_pos.mpr x.2⟩
  div x y := ⟨x.1 / y.1, div_pos x.2 y.2⟩
  mul_assoc a b c := Subtype.ext (mul_assoc a.1 b.1 c.1)
  one_mul a := Subtype.ext (one_mul a.1)
  mul_one a := Subtype.ext (mul_one a.1)
  inv_mul_cancel a := Subtype.ext (inv_mul_cancel₀ a.2.ne')
  div_eq_mul_inv a b := Subtype.ext (div_eq_mul_inv a.1 b.1)
  mul_comm a b := Subtype.ext (mul_comm a.1 b.1)

@[simp] theorem PosReal.coe_one : ((1 : PosReal) : ℝ) = 1 := rfl
@[simp] theorem PosReal.coe_mul (x y : PosReal) : ((x * y : PosReal) : ℝ) = x.1 * y.1 := rfl
@[simp] theorem PosReal.coe_inv (x : PosReal) : ((x⁻¹ : PosReal) : ℝ) = x.1⁻¹ := rfl
@[simp] theorem PosReal.coe_div (x y : PosReal) : ((x / y : PosReal) : ℝ) = x.1 / y.1 := rfl

variable {K : Type*} [Field K] [NumberField K]

/-- For every idele `a : Idele K`, the finite local absolute values `|a_v|_v` equal `1`
for all but finitely many `v`. -/
theorem hasFiniteMulSupport_ideleFinAbsVal (a : Idele K) :
    (fun v : HeightOneSpectrum (𝓞 K) ↦
      finiteAbsVal v ((ideleFinAt K v a : (v.adicCompletion K)ˣ) : v.adicCompletion K)).HasFiniteMulSupport := by
  rw [Function.HasFiniteMulSupport, Function.mulSupport]
  have h := ideleFinAt_eventually_valued_eq_one K a
  rw [Filter.eventually_cofinite] at h
  refine h.subset ?_
  intro v hv
  simp only [Set.mem_ofPred_eq] at hv ⊢
  rwa [← finiteAbsVal_eq_one_iff_valued_eq_one]

/-- The infinite part of the idelic norm: `|a|_∞ = ∏_{w∣∞} |a_w|_w`. -/
def infIdeleNormReal (a : Idele K) : ℝ :=
  ∏ w : InfinitePlace K, infAbsVal w ((ideleInfAt K w a : (w.Completion)ˣ) : w.Completion)

theorem infIdeleNormReal_eq_norm (a : Idele K) :
    infIdeleNormReal a = ‖a.1.1‖ := rfl

theorem infIdeleNormReal_pos (a : Idele K) : 0 < infIdeleNormReal a := by
  unfold infIdeleNormReal
  exact Finset.prod_pos fun w _ ↦ infAbsVal_pos_of_ne_zero w (ideleInfAt K w a).ne_zero

theorem infIdeleNormReal_one : infIdeleNormReal (1 : Idele K) = 1 := by
  simp [infIdeleNormReal]

theorem infIdeleNormReal_mul (a b : Idele K) :
    infIdeleNormReal (a * b) = infIdeleNormReal a * infIdeleNormReal b := by
  simp only [infIdeleNormReal, map_mul, Units.val_mul, infAbsVal_mul, Finset.prod_mul_distrib]

/-- The finite part of the idelic norm: `|a|_f = ∏'_{v} |a_v|_v`. -/
def finIdeleNormReal (a : Idele K) : ℝ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K),
    finiteAbsVal v ((ideleFinAt K v a : (v.adicCompletion K)ˣ) : v.adicCompletion K)

theorem finIdeleNormReal_pos (a : Idele K) : 0 < finIdeleNormReal a := by
  classical
  unfold finIdeleNormReal
  rw [finprod_def, dif_pos (hasFiniteMulSupport_ideleFinAbsVal a)]
  exact Finset.prod_pos fun v _ ↦ finiteAbsVal_pos_of_ne_zero v (ideleFinAt K v a).ne_zero

theorem finIdeleNormReal_one : finIdeleNormReal (1 : Idele K) = 1 := by
  simp [finIdeleNormReal]

theorem finIdeleNormReal_mul (a b : Idele K) :
    finIdeleNormReal (a * b) = finIdeleNormReal a * finIdeleNormReal b := by
  unfold finIdeleNormReal
  have h :
      (fun v : HeightOneSpectrum (𝓞 K) ↦
        finiteAbsVal v ((ideleFinAt K v (a * b) : (v.adicCompletion K)ˣ) : v.adicCompletion K)) =
      fun v : HeightOneSpectrum (𝓞 K) ↦
        finiteAbsVal v ((ideleFinAt K v a : (v.adicCompletion K)ˣ) : v.adicCompletion K) *
        finiteAbsVal v ((ideleFinAt K v b : (v.adicCompletion K)ˣ) : v.adicCompletion K) := by
    funext v
    simp only [map_mul, Units.val_mul, finiteAbsVal_mul]
  rw [h]
  exact finprod_mul_distrib (hasFiniteMulSupport_ideleFinAbsVal a)
    (hasFiniteMulSupport_ideleFinAbsVal b)

/-- The real-valued global idelic norm homomorphism `|·|_𝔸 : 𝕀_K →* ℝ`. -/
def ideleNormReal : Idele K →* ℝ where
  toFun a := infIdeleNormReal a * finIdeleNormReal a
  map_one' := by simp [infIdeleNormReal_one, finIdeleNormReal_one]
  map_mul' a b := by
    simp only [infIdeleNormReal_mul, finIdeleNormReal_mul]
    ring

theorem ideleNormReal_pos (a : Idele K) : 0 < ideleNormReal a :=
  mul_pos (infIdeleNormReal_pos a) (finIdeleNormReal_pos a)

/-- The `ℝ_{>0}`-valued global idelic norm homomorphism `|·|_𝔸 : 𝕀_K →* ℝ_{>0}`. -/
def ideleNorm : Idele K →* PosReal where
  toFun a := ⟨ideleNormReal a, ideleNormReal_pos a⟩
  map_one' := Subtype.ext (map_one ideleNormReal)
  map_mul' a b := Subtype.ext (map_mul ideleNormReal a b)

@[simp]
theorem ideleNorm_coe (a : Idele K) :
    ((ideleNorm a : PosReal) : ℝ) = infIdeleNormReal a * finIdeleNormReal a := rfl

/-- Infinite product formula on principal ideles:
`|x|_∞ = ∏_{w∣∞} |x|_w = |N_{K/ℚ}(x)|`. -/
theorem infIdeleNormReal_principal (x : Kˣ) :
    infIdeleNormReal (principalIdele K x) = |(Algebra.norm ℚ (x : K) : ℝ)| := by
  have h :
      infIdeleNormReal (principalIdele K x) =
        ∏ w : InfinitePlace K, w (x : K) ^ w.mult := by
    unfold infIdeleNormReal
    refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [principalIdele_infAt_val, infAbsVal_coe_eq]
  rw [h, NumberField.InfinitePlace.prod_eq_abs_norm (x : K)]
  simp

/-- Finite product formula on principal ideles:
`|x|_f = ∏'_{v} |x|_v = |N_{K/ℚ}(x)|⁻¹`. -/
theorem finIdeleNormReal_principal (x : Kˣ) :
    finIdeleNormReal (principalIdele K x) = |(Algebra.norm ℚ (x : K) : ℝ)|⁻¹ := by
  unfold finIdeleNormReal
  have h1 :
      (∏ᶠ v : HeightOneSpectrum (𝓞 K),
        finiteAbsVal v
          ((ideleFinAt K v (principalIdele K x) : (v.adicCompletion K)ˣ) : v.adicCompletion K)) =
      ∏ᶠ w : NumberField.FinitePlace K, w (x : K) := by
    rw [← finprod_comp_equiv NumberField.FinitePlace.equivHeightOneSpectrum.symm]
    refine finprod_congr fun v ↦ ?_
    rw [principalIdele_finAt_val, finiteAbsVal_coe_eq_finitePlace]
    rfl
  rw [h1, NumberField.FinitePlace.prod_eq_inv_abs_norm (x := (x : K)) x.ne_zero]
  simp

/-- **UNCONDITIONAL ARTIN–WHAPLES PRODUCT FORMULA (Idelic Norm Form, `ℝ`-valued)**:
for every number field `K` and every `x ∈ Kˣ`, `|principalIdele K x|_𝔸 = 1`. -/
theorem ideleNormReal_principal (x : Kˣ) :
    ideleNormReal (principalIdele K x) = 1 := by
  change infIdeleNormReal (principalIdele K x) * finIdeleNormReal (principalIdele K x) = 1
  rw [infIdeleNormReal_principal, finIdeleNormReal_principal]
  have hnorm_ne : (Algebra.norm ℚ (x : K) : ℝ) ≠ 0 := by
    exact_mod_cast (Algebra.norm_ne_zero_iff (R := ℚ) (x := (x : K))).mpr x.ne_zero
  exact mul_inv_cancel₀ (abs_ne_zero.mpr hnorm_ne)

/-- **UNCONDITIONAL ARTIN–WHAPLES PRODUCT FORMULA (`ℝ_{>0}`-valued)**:
for every number field `K` and every `x ∈ Kˣ`, `ideleNorm (principalIdele K x) = 1`. -/
theorem ideleNorm_principal (x : Kˣ) :
    ideleNorm (principalIdele K x) = 1 :=
  Subtype.ext (ideleNormReal_principal x)

/-- **UNCONDITIONAL CONCRETE ARTIN–WHAPLES PRODUCT FORMULA**:
for every number field `K` and every `x ∈ Kˣ`,
`(∏_{w∣∞} (w x) ^ w.mult) * (∏'_{v} (Nat.card (𝒪_K ⧸ v.asIdeal) : ℝ) ^ (-ord_v(x))) = 1`. -/
theorem artin_whaples_product_formula (x : Kˣ) :
    (∏ w : InfinitePlace K, (w (x : K)) ^ w.mult) *
      (∏ᶠ v : HeightOneSpectrum (𝓞 K),
        (Nat.card (𝓞 K ⧸ v.asIdeal) : ℝ) ^ (-finiteOrd v ((x : K) : v.adicCompletion K))) = 1 := by
  have h := ideleNormReal_principal x
  change infIdeleNormReal (principalIdele K x) * finIdeleNormReal (principalIdele K x) = 1 at h
  have hinf :
      infIdeleNormReal (principalIdele K x) = ∏ w : InfinitePlace K, (w (x : K)) ^ w.mult := by
    unfold infIdeleNormReal
    refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [principalIdele_infAt_val, infAbsVal_coe_eq]
  have hfin :
      finIdeleNormReal (principalIdele K x) =
        ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          (Nat.card (𝓞 K ⧸ v.asIdeal) : ℝ) ^ (-finiteOrd v ((x : K) : v.adicCompletion K)) := by
    unfold finIdeleNormReal
    refine finprod_congr fun v ↦ ?_
    rw [principalIdele_finAt_val]
    have hxne : ((x : K) : v.adicCompletion K) ≠ 0 :=
      (map_ne_zero_iff (algebraMap K (v.adicCompletion K))
        (algebraMap K (v.adicCompletion K)).injective).mpr x.ne_zero
    exact finiteAbsVal_eq_residueCard_zpow v hxne
  rw [← hinf, ← hfin]
  exact h

variable (K)

/-- The subgroup `𝕀_K¹ = ker(|·|_𝔸)` of norm-1 ideles of `K`. -/
def NormOneIdeles : Subgroup (Idele K) := (ideleNorm (K := K)).ker

theorem mem_normOneIdeles_iff (a : Idele K) :
    a ∈ NormOneIdeles K ↔ ideleNorm a = 1 := Iff.rfl

/-- By the Artin–Whaples product formula, every principal idele has norm `1`:
`Kˣ ≤ 𝕀_K¹`. -/
theorem principalSubgroup_le_normOneIdeles :
    principalSubgroup K ≤ NormOneIdeles K := by
  rintro _ ⟨x, rfl⟩
  exact ideleNorm_principal x

/-- Principal ideles regarded as a subgroup of `𝕀_K¹`. -/
def principalInNormOne : Subgroup (NormOneIdeles K) :=
  (principalSubgroup K).subgroupOf (NormOneIdeles K)

/-- The canonical norm-1 idele class group `ℂ_K¹ = 𝕀_K¹ / Kˣ`. -/
abbrev NormOneIdeleClassGroup : Type _ :=
  NormOneIdeles K ⧸ principalInNormOne K

/-- The induced global norm homomorphism `|·|_𝔸 : ℂ_K = 𝕀_K / Kˣ →* ℝ_{>0}`. -/
def ideleClassNorm : IdeleClassGroup K →* PosReal :=
  QuotientGroup.lift (principalSubgroup K) (ideleNorm (K := K)) fun _ ha ↦
    principalSubgroup_le_normOneIdeles K ha

@[simp]
theorem ideleClassNorm_mk (a : Idele K) :
    ideleClassNorm K (QuotientGroup.mk a) = ideleNorm a := rfl

/-- The canonical homomorphism `𝕀_K¹ / Kˣ →* 𝕀_K / Kˣ`. -/
def normOneClassIncl : NormOneIdeleClassGroup K →* IdeleClassGroup K :=
  QuotientGroup.map (principalInNormOne K) (principalSubgroup K) (NormOneIdeles K).subtype
    (by
      intro x hx
      exact hx)

theorem normOneClassIncl_injective : Function.Injective (normOneClassIncl K) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro q hq
  induction q using QuotientGroup.induction_on with
  | H a =>
    rw [MonoidHom.mem_ker] at hq
    change (QuotientGroup.mk (a : Idele K) : IdeleClassGroup K) = 1 at hq
    rw [QuotientGroup.eq_one_iff] at hq
    rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
    exact hq

/-- Exactness at `ℂ_K`: `im(𝕀_K¹ / Kˣ → 𝕀_K / Kˣ) = ker(|·|_𝔸 : ℂ_K → ℝ_{>0})`. -/
theorem normOneClassIncl_range_eq_ker :
    (normOneClassIncl K).range = (ideleClassNorm K).ker := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H a =>
    simp only [MonoidHom.mem_range, MonoidHom.mem_ker, ideleClassNorm_mk]
    constructor
    · rintro ⟨q', hq'⟩
      induction q' using QuotientGroup.induction_on with
      | H b =>
        change (QuotientGroup.mk (b : Idele K) : IdeleClassGroup K) = QuotientGroup.mk a at hq'
        have hEq := congrArg (ideleClassNorm K) hq'
        simp only [ideleClassNorm_mk] at hEq
        rw [← hEq]
        exact b.2
    · intro ha
      exact ⟨QuotientGroup.mk ⟨a, ha⟩, rfl⟩

/-- Canonical multiplicative section `ℝ_{>0} →* 𝕀_K` of the global idelic norm `ideleNorm`,
defined by scaling a chosen infinite place `w₀` by `t ^ (1 / w₀.mult)` and setting all other
places to `1`. -/
def ideleNormSection : PosReal →* Idele K := by
  classical
  let w₀ : InfinitePlace K := Classical.arbitrary (InfinitePlace K)
  let rHom : PosReal →* ℝˣ :=
    { toFun := fun t ↦ Units.mk0 (t.1 ^ ((w₀.mult : ℝ)⁻¹)) (Real.rpow_pos_of_pos t.2 _).ne'
      map_one' := by
        apply Units.ext
        simp
      map_mul' := fun t₁ t₂ ↦ by
        apply Units.ext
        exact Real.mul_rpow t₁.2.le t₂.2.le }
  let scaleAt : (w : InfinitePlace K) → PosReal →* (w.Completion)ˣ := fun w ↦
    if hw : w = w₀ then
      if hreal : w.IsReal then
        (Units.map (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hreal).symm.toMonoidHom).comp rHom
      else
        (Units.map ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hreal)).symm.toMonoidHom.comp
          (Complex.ofRealHom.toMonoidHom))).comp rHom
    else 1
  let infSection : PosReal →* InfIdele K :=
    MulEquiv.piUnits.symm.toMonoidHom.comp (MonoidHom.pi scaleAt)
  exact (ideleEquivProd K).symm.toMonoidHom.comp
    (MonoidHom.prod infSection (1 : PosReal →* FinIdele K))

/-- `ideleNormSection` is a right inverse to `ideleNorm`: `|ideleNormSection K t|_𝔸 = t`
for every `t ∈ ℝ_{>0}`. -/
theorem ideleNorm_section (t : PosReal) :
    ideleNorm (ideleNormSection K t) = t := by
  classical
  apply Subtype.ext
  let w₀ : InfinitePlace K := Classical.arbitrary (InfinitePlace K)
  let r : ℝ := t.1 ^ ((w₀.mult : ℝ)⁻¹)
  have hr_pos : 0 < r := Real.rpow_pos_of_pos t.2 _
  have hfin : finIdeleNormReal (ideleNormSection K t) = 1 := by
    unfold finIdeleNormReal
    refine finprod_eq_one_of_forall_eq_one fun v ↦ ?_
    have hv : ideleFinAt K v (ideleNormSection K t) = 1 := by
      apply Units.ext
      change ((ideleFin K (ideleNormSection K t) : FinIdele K) : FinAdele K) v = 1
      have h1 : ideleFin K (ideleNormSection K t) = 1 := by
        simp only [ideleFin, ideleNormSection, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          MulEquiv.apply_symm_apply]
        rfl
      rw [h1]
      rfl
    rw [hv, Units.val_one, finiteAbsVal_one]
  have hinf_eq : ideleInf K (ideleNormSection K t) =
      MulEquiv.piUnits.symm (fun u ↦
        if hu : u = w₀ then
          if hreal : u.IsReal then
            Units.map (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hreal).symm.toMonoidHom
              (Units.mk0 r hr_pos.ne')
          else
            Units.map ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex
              (NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hreal)).symm.toMonoidHom.comp
              Complex.ofRealHom.toMonoidHom) (Units.mk0 r hr_pos.ne')
        else 1) := by
    simp only [ideleInf, ideleNormSection, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply]
    change MulEquiv.piUnits.symm _ = _
    congr 1
    funext u
    by_cases hu : u = w₀
    · subst hu
      by_cases hreal : w₀.IsReal <;> simp [hreal, r, w₀]
    · simp [hu, w₀]
  have hinf_other : ∀ w : InfinitePlace K, w ≠ w₀ →
      ideleInfAt K w (ideleNormSection K t) = 1 := by
    intro w hw
    change (MulEquiv.piUnits (ideleInf K (ideleNormSection K t))) w = 1
    rw [hinf_eq]
    simp [hw]
  have hnorm_w0 :
      infAbsVal w₀ ((ideleInfAt K w₀ (ideleNormSection K t) : (w₀.Completion)ˣ) : w₀.Completion) =
        t.1 := by
    by_cases hreal : w₀.IsReal
    · have hval :
          ((ideleInfAt K w₀ (ideleNormSection K t) : (w₀.Completion)ˣ) : w₀.Completion) =
            (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hreal).symm r := by
        change ((MulEquiv.piUnits (ideleInf K (ideleNormSection K t)) w₀ : (w₀.Completion)ˣ) :
          w₀.Completion) = _
        rw [hinf_eq]
        simp [hreal]
      rw [hval, infAbsVal_of_isReal hreal]
      have hiso := NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hreal
      have heq : ‖(NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hreal).symm r‖ =
          ‖r‖ := by
        have h1 := hiso.norm_map_of_map_zero (map_zero _)
          ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hreal).symm r)
        have h2 : NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hreal
            ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hreal).symm r) = r :=
          (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hreal).apply_symm_apply r
        rw [h2] at h1
        exact h1.symm
      rw [heq, Real.norm_of_nonneg hr_pos.le]
      simp [r, hreal.mult_eq_one]
    · have hcomp : w₀.IsComplex := NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hreal
      have hval :
          ((ideleInfAt K w₀ (ideleNormSection K t) : (w₀.Completion)ˣ) : w₀.Completion) =
            (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hcomp).symm (r : ℂ) := by
        change ((MulEquiv.piUnits (ideleInf K (ideleNormSection K t)) w₀ : (w₀.Completion)ˣ) :
          w₀.Completion) = _
        rw [hinf_eq]
        simp [hreal]
      rw [hval, infAbsVal_of_isComplex hcomp]
      have hiso := NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w₀
      have heq :
          ‖(NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hcomp).symm (r : ℂ)‖ =
            ‖(r : ℂ)‖ := by
        have h1 := hiso.norm_map_of_map_zero (map_zero _)
          ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hcomp).symm (r : ℂ))
        have h2 : NumberField.InfinitePlace.Completion.extensionEmbedding w₀
            ((NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hcomp).symm (r : ℂ)) =
              (r : ℂ) :=
          (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hcomp).apply_symm_apply
            (r : ℂ)
        rw [h2] at h1
        exact h1.symm
      rw [heq, Complex.norm_real, Real.norm_of_nonneg hr_pos.le]
      simp only [r, hcomp.mult_eq_two, Nat.cast_ofNat]
      rw [← Real.rpow_natCast, ← Real.rpow_mul t.2.le]
      norm_num
  have hinf : infIdeleNormReal (ideleNormSection K t) = t.1 := by
    unfold infIdeleNormReal
    rw [Finset.prod_eq_single w₀]
    · exact hnorm_w0
    · intro w _ hw
      rw [hinf_other w hw, Units.val_one, infAbsVal_one]
    · intro h
      exact absurd (Finset.mem_univ w₀) h
  rw [ideleNorm_coe, hinf, hfin, mul_one]

/-- The global idelic norm `ideleNorm : 𝕀_K →* ℝ_{>0}` is surjective. -/
theorem ideleNorm_surjective : Function.Surjective (ideleNorm (K := K)) :=
  fun t ↦ ⟨ideleNormSection K t, ideleNorm_section K t⟩

/-- The idele class norm `|·|_𝔸 : ℂ_K →* ℝ_{>0}` is surjective. -/
theorem ideleClassNorm_surjective : Function.Surjective (ideleClassNorm K) := by
  intro t
  obtain ⟨a, ha⟩ := ideleNorm_surjective K t
  exact ⟨QuotientGroup.mk a, ha⟩

/-- **Canonical Direct-Product Splitting of the Idele Group**:
`𝕀_K ≃* 𝕀_K¹ × ℝ_{>0}`. -/
def ideleEquivNormOneProd : Idele K ≃* NormOneIdeles K × PosReal where
  toFun a :=
    (⟨a * (ideleNormSection K (ideleNorm a))⁻¹, by
      rw [mem_normOneIdeles_iff, map_mul, map_inv, ideleNorm_section, mul_inv_cancel]⟩,
     ideleNorm a)
  invFun p := (p.1 : Idele K) * ideleNormSection K p.2
  left_inv a := by
    simp
  right_inv p := by
    rcases p with ⟨⟨b, hb⟩, t⟩
    have hnorm : ideleNorm (b * ideleNormSection K t) = t := by
      rw [map_mul, (mem_normOneIdeles_iff K b).mp hb, one_mul, ideleNorm_section]
    apply Prod.ext
    · apply Subtype.ext
      simp [hnorm]
    · exact hnorm
  map_mul' a b := by
    apply Prod.ext
    · apply Subtype.ext
      simp only [Prod.fst_mul, Subgroup.coe_mul, map_mul, mul_inv]
      ac_rfl
    · exact map_mul ideleNorm a b

/-- **Canonical Direct-Product Splitting of the Idele Class Group** (Tate's decomposition):
`𝕀_K / Kˣ ≃* (𝕀_K¹ / Kˣ) × ℝ_{>0}`. -/
def ideleClassEquivNormOneProd : IdeleClassGroup K ≃* NormOneIdeleClassGroup K × PosReal :=
  MulEquiv.ofBijective
    (QuotientGroup.lift (principalSubgroup K)
      (MonoidHom.prod
        ((QuotientGroup.mk' (principalInNormOne K)).comp
          ((MonoidHom.fst (NormOneIdeles K) PosReal).comp (ideleEquivNormOneProd K).toMonoidHom))
        (ideleNorm (K := K)))
      (fun a ha ↦ by
        apply Prod.ext
        · change (QuotientGroup.mk
            (⟨a * (ideleNormSection K (ideleNorm a))⁻¹, _⟩ : NormOneIdeles K) :
            NormOneIdeleClassGroup K) = 1
          have ha1 : ideleNorm a = 1 := principalSubgroup_le_normOneIdeles K ha
          rw [QuotientGroup.eq_one_iff]
          change a * (ideleNormSection K (ideleNorm a))⁻¹ ∈ principalSubgroup K
          simpa [ha1] using ha
        · exact principalSubgroup_le_normOneIdeles K ha))
    ⟨by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro q hq
      induction q using QuotientGroup.induction_on with
      | H a =>
        rw [MonoidHom.mem_ker, Prod.ext_iff] at hq
        have h1 : (QuotientGroup.mk
            (⟨a * (ideleNormSection K (ideleNorm a))⁻¹, _⟩ : NormOneIdeles K) :
            NormOneIdeleClassGroup K) = 1 := hq.1
        have h2 : ideleNorm a = 1 := hq.2
        rw [QuotientGroup.eq_one_iff] at h1
        change a * (ideleNormSection K (ideleNorm a))⁻¹ ∈ principalSubgroup K at h1
        rw [h2, map_one, inv_one, mul_one] at h1
        rw [Subgroup.mem_bot, QuotientGroup.eq_one_iff]
        exact h1,
     by
      rintro ⟨q, t⟩
      induction q using QuotientGroup.induction_on with
      | H b =>
        refine ⟨QuotientGroup.mk ((b : Idele K) * ideleNormSection K t), ?_⟩
        have hnorm : ideleNorm ((b : Idele K) * ideleNormSection K t) = t := by
          rw [map_mul, (mem_normOneIdeles_iff K b).mp b.2, one_mul, ideleNorm_section]
        apply Prod.ext
        · change QuotientGroup.mk
            (⟨((b : Idele K) * ideleNormSection K t) *
              (ideleNormSection K (ideleNorm ((b : Idele K) * ideleNormSection K t)))⁻¹, _⟩ :
              NormOneIdeles K) = QuotientGroup.mk b
          congr 1
          apply Subtype.ext
          simp [hnorm]
        · exact hnorm⟩

end ProductFormula

/-! ## Section 4: Concrete Local Tate Zeta Integrals (Non-Archimedean & Archimedean) -/

section LocalTateFinite

variable {K : Type*} [Field K] [NumberField K]

/-- A local multiplicative character `χ : K_vˣ →* ℂˣ` is **unramified** if it is trivial on the
local unit group `𝒪_vˣ = (v.adicCompletionIntegers K).units`. -/
def IsUnramifiedLocalChar (v : HeightOneSpectrum (𝓞 K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) : Prop :=
  ∀ u ∈ (v.adicCompletionIntegers K).units, χ u = 1

/-- Every finite place `v` of a number field admits a local uniformizer `ϖ_v ∈ K_vˣ` with
`Valued.v ϖ_v = WithZero.exp (-1)` (hence `finiteOrd v ϖ_v = 1`). -/
theorem exists_local_uniformizer (v : HeightOneSpectrum (𝓞 K)) :
    ∃ ϖ : (v.adicCompletion K)ˣ,
      Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨ϖ, hϖ⟩ := v.valuation_exists_uniformizer K
  have hval : Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hϖ]
  have hne : (ϖ : v.adicCompletion K) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hval
    exact WithZero.exp_ne_zero hval.symm
  exact ⟨Units.mk0 (ϖ : v.adicCompletion K) hne, hval⟩

/-- The canonical Satake parameter `α_v = χ_v(ϖ_v) ∈ ℂ` of a local character `χ_v` at `v`. -/
def satakeParam (v : HeightOneSpectrum (𝓞 K)) (χ : (v.adicCompletion K)ˣ →* ℂˣ) : ℂ :=
  (χ (exists_local_uniformizer v).choose : ℂ)

/-- For an unramified local character `χ`, `χ(ϖ)` is independent of the choice of uniformizer `ϖ`
and equals `satakeParam v χ`. -/
theorem satakeParam_eq_of_isUniformizer (v : HeightOneSpectrum (𝓞 K))
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} (hunr : IsUnramifiedLocalChar v χ)
    {ϖ : (v.adicCompletion K)ˣ}
    (hϖ : Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1 : ℤ)) :
    (χ ϖ : ℂ) = satakeParam v χ := by
  set ϖ₀ := (exists_local_uniformizer v).choose
  have hϖ₀ : Valued.v (ϖ₀ : v.adicCompletion K) = WithZero.exp (-1 : ℤ) :=
    (exists_local_uniformizer v).choose_spec
  have hratio_val : Valued.v ((ϖ * ϖ₀⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
    simp [Units.val_mul, hϖ, hϖ₀]
  have hmem : ϖ * ϖ₀⁻¹ ∈ (v.adicCompletionIntegers K).units :=
    (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one).mpr hratio_val
  have hkill : χ (ϖ * ϖ₀⁻¹) = 1 := hunr _ hmem
  have heq : χ ϖ = χ ϖ₀ := by
    calc χ ϖ = χ (ϖ * ϖ₀⁻¹ * ϖ₀) := by simp
      _ = χ (ϖ * ϖ₀⁻¹) * χ ϖ₀ := map_mul χ _ _
      _ = χ ϖ₀ := by rw [hkill, one_mul]
  exact congrArg Units.val heq

/-- Every unramified local character satisfies `χ(x) = (satakeParam v χ) ^ (finiteOrd v x)`
for EVERY `x ∈ K_vˣ`. -/
theorem unramifiedChar_apply_eq_zpow (v : HeightOneSpectrum (𝓞 K))
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} (hunr : IsUnramifiedLocalChar v χ)
    (x : (v.adicCompletion K)ˣ) :
    (χ x : ℂ) = (satakeParam v χ) ^ (finiteOrd v (x : v.adicCompletion K)) := by
  set ϖ₀ := (exists_local_uniformizer v).choose
  have hϖ₀ : Valued.v (ϖ₀ : v.adicCompletion K) = WithZero.exp (-1 : ℤ) :=
    (exists_local_uniformizer v).choose_spec
  set n : ℤ := finiteOrd v (x : v.adicCompletion K)
  have hx_val : Valued.v (x : v.adicCompletion K) = WithZero.exp (-n) := by
    have hvx : (Valued.v (x : v.adicCompletion K) : WithZero (Multiplicative ℤ)) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr x.ne_zero
    simp only [n, finiteOrd, neg_neg, WithZero.exp_log hvx]
  have hpow_val : Valued.v ((ϖ₀ ^ n : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      WithZero.exp (-n) := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ₀, ← WithZero.exp_zsmul]
    simp
  have hratio_val : Valued.v ((x * (ϖ₀ ^ n)⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) = 1 := by
    rw [Units.val_mul, map_mul, hx_val, Units.val_inv_eq_inv_val, map_inv₀, hpow_val,
      mul_inv_cancel₀ WithZero.exp_ne_zero]
  have hmem : x * (ϖ₀ ^ n)⁻¹ ∈ (v.adicCompletionIntegers K).units :=
    (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one).mpr hratio_val
  have hkill : χ (x * (ϖ₀ ^ n)⁻¹) = 1 := hunr _ hmem
  have heq : χ x = (χ ϖ₀) ^ n := by
    calc χ x = χ (x * (ϖ₀ ^ n)⁻¹ * ϖ₀ ^ n) := by simp
      _ = χ (x * (ϖ₀ ^ n)⁻¹) * χ (ϖ₀ ^ n) := map_mul χ _ _
      _ = (χ ϖ₀) ^ n := by rw [hkill, one_mul, map_zpow]
  rw [heq, Units.val_zpow_eq_zpow_val]
  rfl

/-- Concrete finite-place spherical local Tate zeta integral `Z_v(1_{𝒪_v}, α, s)` obtained from
the disjoint valuation-shell decomposition `𝒪_v \ {0} = ⨆_{n : ℕ} ϖ_v^n 𝒪_vˣ` with normalized
Haar measure `vol(𝒪_vˣ) = 1`:
`Z_v(1_{𝒪_v}, α, s) = ∑'_{n : ℕ} (α * q_v^{-s})^n`. -/
def localTateZetaFin (v : HeightOneSpectrum (𝓞 K)) (α s : ℂ) : ℂ :=
  ∑' n : ℕ, (α * (residueCard v : ℂ) ^ (-s)) ^ n

/-- Unramified local Tate zeta integral `Z_v(1_{𝒪_v}, χ_v, s)` of a local character `χ_v`. -/
def localTateZetaUnramified (v : HeightOneSpectrum (𝓞 K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (s : ℂ) : ℂ :=
  localTateZetaFin v (satakeParam v χ) s

/-- For `‖α‖ ≤ 1` and `0 < s.re`, the geometric ratio `α * q_v^{-s}` has norm strictly `< 1`. -/
theorem norm_satake_mul_residueCard_cpow_lt_one (v : HeightOneSpectrum (𝓞 K))
    {α s : ℂ} (hα : ‖α‖ ≤ 1) (hs : 0 < s.re) :
    ‖α * (residueCard v : ℂ) ^ (-s)‖ < 1 := by
  have hq1 : (1 : ℝ) < (residueCard v : ℝ) := by
    exact_mod_cast one_lt_residueCard v
  have hq0 : (0 : ℝ) < (residueCard v : ℝ) := zero_lt_one.trans hq1
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (residueCard_pos v), Complex.neg_re]
  have hrpow : (residueCard v : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hq1 (neg_lt_zero.mpr hs)
  calc ‖α‖ * (residueCard v : ℝ) ^ (-s.re)
      ≤ 1 * (residueCard v : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right hα (Real.rpow_nonneg hq0.le _)
    _ = (residueCard v : ℝ) ^ (-s.re) := one_mul _
    _ < 1 := hrpow

/-- Exact geometric-series convergence (`HasSum`) of the finite-place spherical local Tate zeta
integral to the local Euler factor `(1 - α q_v^{-s})⁻¹`. -/
theorem localTateZetaFin_hasSum (v : HeightOneSpectrum (𝓞 K))
    {α s : ℂ} (hα : ‖α‖ ≤ 1) (hs : 0 < s.re) :
    HasSum (fun n : ℕ ↦ (α * (residueCard v : ℂ) ^ (-s)) ^ n)
      (1 - α * (residueCard v : ℂ) ^ (-s))⁻¹ :=
  hasSum_geometric_of_norm_lt_one (norm_satake_mul_residueCard_cpow_lt_one v hα hs)

/-- **Finite-Place Spherical Local Tate Zeta Evaluation**:
`Z_v(1_{𝒪_v}, α, s) = (1 - α * q_v^{-s})⁻¹` for `‖α‖ ≤ 1` and `0 < s.re`. -/
theorem localTateZetaFin_eq_eulerFactor (v : HeightOneSpectrum (𝓞 K))
    {α s : ℂ} (hα : ‖α‖ ≤ 1) (hs : 0 < s.re) :
    localTateZetaFin v α s = (1 - α * (residueCard v : ℂ) ^ (-s))⁻¹ :=
  (localTateZetaFin_hasSum v hα hs).tsum_eq

/-- **Unramified Local Tate Zeta Integral = Exact Local Euler Factor** (for any uniformizer `ϖ`):
`Z_v(1_{𝒪_v}, χ_v, s) = (1 - χ_v(ϖ) * (Nat.card (𝒪_K ⧸ v.asIdeal))^{-s})⁻¹`. -/
theorem localTateZetaUnramified_eq_eulerFactor (v : HeightOneSpectrum (𝓞 K))
    {χ : (v.adicCompletion K)ˣ →* ℂˣ} (hunr : IsUnramifiedLocalChar v χ)
    {ϖ : (v.adicCompletion K)ˣ}
    (hϖ : Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1 : ℤ))
    {s : ℂ} (hunitary : ‖(χ ϖ : ℂ)‖ ≤ 1) (hs : 0 < s.re) :
    localTateZetaUnramified v χ s =
      (1 - (χ ϖ : ℂ) * (Nat.card (𝓞 K ⧸ v.asIdeal) : ℂ) ^ (-s))⁻¹ := by
  have hsat := satakeParam_eq_of_isUniformizer v hunr hϖ
  unfold localTateZetaUnramified
  rw [← hsat]
  exact localTateZetaFin_eq_eulerFactor v hunitary hs

/-- Shifted spherical local Schwartz–Bruhat function `1_{ϖ_v^k 𝒪_v}` (`k : ℕ`):
`Z_v(1_{ϖ_v^k 𝒪_v}, α, s) = ∑'_{n : ℕ} (α q_v^{-s})^{n + k} = (α q_v^{-s})^k * (1 - α q_v^{-s})⁻¹`. -/
def localTateZetaShifted (v : HeightOneSpectrum (𝓞 K)) (k : ℕ) (α s : ℂ) : ℂ :=
  ∑' n : ℕ, (α * (residueCard v : ℂ) ^ (-s)) ^ (n + k)

theorem localTateZetaShifted_eq (v : HeightOneSpectrum (𝓞 K)) (k : ℕ)
    {α s : ℂ} (hα : ‖α‖ ≤ 1) (hs : 0 < s.re) :
    localTateZetaShifted v k α s =
      (α * (residueCard v : ℂ) ^ (-s)) ^ k * (1 - α * (residueCard v : ℂ) ^ (-s))⁻¹ := by
  unfold localTateZetaShifted
  have hrew :
      (fun n : ℕ ↦ (α * (residueCard v : ℂ) ^ (-s)) ^ (n + k)) =
      fun n : ℕ ↦ (α * (residueCard v : ℂ) ^ (-s)) ^ k * (α * (residueCard v : ℂ) ^ (-s)) ^ n := by
    funext n
    rw [pow_add, mul_comm]
  rw [hrew, tsum_mul_left, ← localTateZetaFin, localTateZetaFin_eq_eulerFactor v hα hs]

omit [NumberField K] in
/-- At a ramified place (`α = 0`), `localTateZetaFin v 0 s = 1` (the trivial local Euler factor). -/
@[simp]
theorem localTateZetaFin_zero (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    localTateZetaFin v 0 s = 1 := by
  unfold localTateZetaFin
  simp only [zero_mul]
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    exact zero_pow hn

end LocalTateFinite

/-! ### Archimedean Local Tate Zeta Integrals (Real & Complex Gaussians) -/

section LocalTateArchimedean

/-- Standard even Gaussian Schwartz function `φ_0(x) = exp(-π x²)` on `ℝ`. -/
def gaussReal (x : ℝ) : ℂ := (Real.exp (-Real.pi * x ^ 2) : ℂ)

/-- Standard odd Gaussian Schwartz function `φ_1(x) = x · exp(-π x²)` on `ℝ`. -/
def gaussRealOdd (x : ℝ) : ℂ := (x : ℂ) * (Real.exp (-Real.pi * x ^ 2) : ℂ)

/-- Concrete Archimedean local Tate zeta integral over `ℝˣ` with multiplicative Haar measure
`dx / |x|`:
`Z_∞(φ, χ, s) = ∫_{ℝ} φ(x) · χ(x) · |x|^{s - 1} dx`. -/
def archTateZetaReal (φ χ : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ x : ℝ, φ x * χ x * ((|x| : ℝ) : ℂ) ^ (s - 1)

/-- Helper: for any integrable even function `f : ℝ → ℂ`,
`∫ x : ℝ, f x = 2 * ∫ x in Set.Ioi 0, f x`. -/
lemma integral_even_eq_two_mul_Ioi {f : ℝ → ℂ} (heven : ∀ x : ℝ, f (-x) = f x)
    (hint : IntegrableOn f (Set.Ioi 0)) :
    ∫ x : ℝ, f x = 2 * ∫ x in Set.Ioi (0 : ℝ), f x := by
  have hneg_img : (fun x : ℝ ↦ -x) '' Set.Ioi (0 : ℝ) = Set.Iio (0 : ℝ) := by
    ext y
    simp only [Set.mem_image, Set.mem_Ioi, Set.mem_Iio]
    constructor
    · rintro ⟨x, hx, rfl⟩
      linarith
    · intro hy
      exact ⟨-y, by linarith, neg_neg y⟩
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt (fun t : ℝ ↦ -t) (-1) (Set.Ioi 0) x :=
    fun x _ ↦ (hasDerivAt_neg x).hasDerivWithinAt
  have hinj : Set.InjOn (fun t : ℝ ↦ -t) (Set.Ioi 0) := fun _ _ _ _ h ↦ neg_inj.mp h
  have hint_Iio : IntegrableOn f (Set.Iio 0) := by
    rw [← hneg_img,
      MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hinj]
    simpa [abs_neg, abs_one, one_smul, heven] using hint
  have hIio_eq : ∫ x in Set.Iio (0 : ℝ), f x = ∫ x in Set.Ioi (0 : ℝ), f x := by
    rw [← hneg_img,
      MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj]
    simp [abs_neg, abs_one, one_smul, heven]
  have hunion_ae : (Set.Iio (0 : ℝ) ∪ Set.Ioi (0 : ℝ) : Set ℝ) =ᵐ[volume] Set.univ := by
    rw [MeasureTheory.ae_eq_univ]
    have hcompl : (Set.Iio (0 : ℝ) ∪ Set.Ioi (0 : ℝ))ᶜ = {(0 : ℝ)} := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_Iio, Set.mem_Ioi, not_or, not_lt,
        Set.mem_singleton_iff]
      exact ⟨fun ⟨h1, h2⟩ ↦ le_antisymm h2 h1, fun h ↦ by rw [h]; exact ⟨le_rfl, le_rfl⟩⟩
    rw [hcompl]
    exact measure_singleton (0 : ℝ)
  have hdisj : Disjoint (Set.Iio (0 : ℝ)) (Set.Ioi (0 : ℝ)) :=
    Set.disjoint_left.mpr fun _ h1 h2 ↦ lt_asymm (Set.mem_Iio.mp h1) (Set.mem_Ioi.mp h2)
  rw [← MeasureTheory.setIntegral_univ, ← MeasureTheory.setIntegral_congr_set hunion_ae,
    MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hint_Iio hint, hIio_eq, two_mul]

/-- Helper: integrability of `t ↦ (t : ℂ) ^ (a - 1) * Complex.exp (-(r * t))` on `(0, ∞)`
for `0 < a.re` and `0 < r`. -/
lemma integrableOn_cpow_mul_exp_neg_mul_Ioi {a : ℂ} {r : ℝ} (ha : 0 < a.re) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (a - 1) * Complex.exp (-((r : ℂ) * t))) (Set.Ioi 0) := by
  have hG := Complex.GammaIntegral_convergent ha
  have hcomp : IntegrableOn (fun t : ℝ ↦ ↑(-(r * t)).exp * (↑(r * t) : ℂ) ^ (a - 1)) (Set.Ioi 0) := by
    have := (MeasureTheory.integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ ↦ (Real.exp (-x) : ℂ) * (x : ℂ) ^ (a - 1)) 0 hr).mpr (by simpa using hG)
    simpa using this
  have hscaled : IntegrableOn
      (fun t : ℝ ↦ ((r : ℂ) ^ (a - 1))⁻¹ * (↑(-(r * t)).exp * (↑(r * t) : ℂ) ^ (a - 1)))
      (Set.Ioi 0) :=
    hcomp.const_mul ((r : ℂ) ^ (a - 1))⁻¹
  refine MeasureTheory.IntegrableOn.congr_fun hscaled (fun t ht ↦ ?_) measurableSet_Ioi
  have ht0 : 0 < t := ht
  have hrC : (r : ℂ) ^ (a - 1) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    push Not
    intro h
    exact absurd (Complex.ofReal_eq_zero.mp h) hr.ne'
  simp only [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hr.le ht0.le,
    Complex.ofReal_exp, Complex.ofReal_neg]
  rw [mul_left_comm ((r : ℂ) ^ (a - 1))⁻¹, ← mul_assoc ((r : ℂ) ^ (a - 1))⁻¹,
    inv_mul_cancel₀ hrC, one_mul, mul_comm]

/-- Helper: general Gaussian Mellin integral on `(0, ∞)`:
for `0 < r` and `0 < s.re`,
`2 * ∫ x in Ioi 0, exp(-r * x²) * x^(s - 1) = (1 / r)^(s / 2) * Γ(s / 2)`. -/
lemma two_mul_integral_gauss_Ioi {r : ℝ} (hr : 0 < r) {s : ℂ} (hs : 0 < s.re) :
    2 * ∫ x in Set.Ioi (0 : ℝ), (Real.exp (-r * x ^ 2) : ℂ) * (x : ℂ) ^ (s - 1) =
      (1 / (r : ℂ)) ^ (s / 2) * Complex.Gamma (s / 2) := by
  have hs2 : 0 < (s / 2).re := by
    rw [Complex.div_ofNat_re]
    linarith
  let g : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (s / 2 - 1) * Complex.exp (-((r : ℂ) * t))
  have himg : (fun x : ℝ ↦ x ^ 2) '' Set.Ioi (0 : ℝ) = Set.Ioi (0 : ℝ) := by
    ext y
    simp only [Set.mem_image, Set.mem_Ioi]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact sq_pos_of_pos hx
    · intro hy
      exact ⟨Real.sqrt y, Real.sqrt_pos.mpr hy, Real.sq_sqrt hy.le⟩
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt (fun t : ℝ ↦ t ^ 2) (2 * x) (Set.Ioi 0) x := by
    intro x _
    simpa using (hasDerivAt_pow 2 x).hasDerivWithinAt
  have hinj : Set.InjOn (fun t : ℝ ↦ t ^ 2) (Set.Ioi 0) := by
    intro x hx y hy hxy
    have hx' : 0 ≤ x := le_of_lt hx
    have hy' : 0 ≤ y := le_of_lt hy
    nlinarith [sq_nonneg (x - y)]
  have hcov : ∫ t in Set.Ioi (0 : ℝ), g t = ∫ x in Set.Ioi (0 : ℝ), |2 * x| • g (x ^ 2) := by
    simpa [himg] using
      MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj g
  have hpt :
      Set.EqOn (fun x : ℝ ↦ |2 * x| • g (x ^ 2))
        (fun x : ℝ ↦ (2 : ℂ) * ((Real.exp (-r * x ^ 2) : ℂ) * (x : ℂ) ^ (s - 1)))
        (Set.Ioi 0) := by
    intro x hx
    dsimp only
    have hx0 : 0 < x := hx
    have h2x : 0 ≤ 2 * x := by positivity
    rw [abs_of_nonneg h2x, Complex.real_smul]
    simp only [g]
    have hpow : ((x ^ 2 : ℝ) : ℂ) ^ (s / 2 - 1) = (x : ℂ) ^ (s - 2) := by
      rw [Complex.ofReal_pow, ← Complex.cpow_nat_mul']
      · congr 1
        push_cast
        ring
      · rw [Complex.arg_ofReal_of_nonneg hx0.le]
        linarith [Real.pi_pos]
      · rw [Complex.arg_ofReal_of_nonneg hx0.le]
        linarith [Real.pi_pos]
    have hmul_pow : (x : ℂ) * (x : ℂ) ^ (s - 2) = (x : ℂ) ^ (s - 1) := by
      have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
      nth_rw 1 [← Complex.cpow_one (x : ℂ)]
      rw [← Complex.cpow_add _ _ hxC]
      congr 1
      ring
    have hexp : Complex.exp (-((r : ℂ) * ((x ^ 2 : ℝ) : ℂ))) = (Real.exp (-r * x ^ 2) : ℂ) := by
      rw [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg, neg_mul]
    rw [hpow, hexp, Complex.ofReal_mul, Complex.ofReal_ofNat]
    calc (2 : ℂ) * (x : ℂ) * ((x : ℂ) ^ (s - 2) * (Real.exp (-r * x ^ 2) : ℂ))
        = (2 : ℂ) * ((Real.exp (-r * x ^ 2) : ℂ) * ((x : ℂ) * (x : ℂ) ^ (s - 2))) := by ring
      _ = (2 : ℂ) * ((Real.exp (-r * x ^ 2) : ℂ) * (x : ℂ) ^ (s - 1)) := by rw [hmul_pow]
  have hEq :
      ∫ t in Set.Ioi (0 : ℝ), g t =
        2 * ∫ x in Set.Ioi (0 : ℝ), (Real.exp (-r * x ^ 2) : ℂ) * (x : ℂ) ^ (s - 1) := by
    rw [hcov, MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpt,
      MeasureTheory.integral_const_mul]
  rw [← hEq]
  exact Complex.integral_cpow_mul_exp_neg_mul_Ioi hs2 hr

/-- Helper: integrability of `x ↦ exp(-r * x²) * x^(s - 1)` on `(0, ∞)` for `0 < r` and `0 < s.re`. -/
lemma integrableOn_gauss_Ioi {r : ℝ} (hr : 0 < r) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ ↦ (Real.exp (-r * x ^ 2) : ℂ) * ((|x| : ℝ) : ℂ) ^ (s - 1)) (Set.Ioi 0) := by
  have hs2 : 0 < (s / 2).re := by
    rw [Complex.div_ofNat_re]
    linarith
  let g : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (s / 2 - 1) * Complex.exp (-((r : ℂ) * t))
  have hg : IntegrableOn g (Set.Ioi 0) := integrableOn_cpow_mul_exp_neg_mul_Ioi hs2 hr
  have himg : (fun x : ℝ ↦ x ^ 2) '' Set.Ioi (0 : ℝ) = Set.Ioi (0 : ℝ) := by
    ext y
    simp only [Set.mem_image, Set.mem_Ioi]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact sq_pos_of_pos hx
    · intro hy
      exact ⟨Real.sqrt y, Real.sqrt_pos.mpr hy, Real.sq_sqrt hy.le⟩
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt (fun t : ℝ ↦ t ^ 2) (2 * x) (Set.Ioi 0) x :=
    fun x _ ↦ by simpa using (hasDerivAt_pow 2 x).hasDerivWithinAt
  have hinj : Set.InjOn (fun t : ℝ ↦ t ^ 2) (Set.Ioi 0) := by
    intro x hx y hy hxy
    have hx' : 0 ≤ x := le_of_lt hx
    have hy' : 0 ≤ y := le_of_lt hy
    nlinarith [sq_nonneg (x - y)]
  have hpull : IntegrableOn (fun x : ℝ ↦ |2 * x| • g (x ^ 2)) (Set.Ioi 0) := by
    rw [← MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
      measurableSet_Ioi hderiv hinj, himg]
    exact hg
  have hhalf : IntegrableOn (fun x : ℝ ↦ (2 : ℂ)⁻¹ * (|2 * x| • g (x ^ 2))) (Set.Ioi 0) :=
    hpull.const_mul (2 : ℂ)⁻¹
  refine MeasureTheory.IntegrableOn.congr_fun hhalf (fun x hx ↦ ?_) measurableSet_Ioi
  have hx0 : 0 < x := hx
  have h2x : 0 ≤ 2 * x := by positivity
  simp only [g]
  rw [abs_of_nonneg h2x, abs_of_pos hx0, Complex.real_smul]
  have hpow : ((x ^ 2 : ℝ) : ℂ) ^ (s / 2 - 1) = (x : ℂ) ^ (s - 2) := by
    rw [Complex.ofReal_pow, ← Complex.cpow_nat_mul']
    · congr 1
      push_cast
      ring
    · rw [Complex.arg_ofReal_of_nonneg hx0.le]
      linarith [Real.pi_pos]
    · rw [Complex.arg_ofReal_of_nonneg hx0.le]
      linarith [Real.pi_pos]
  have hmul_pow : (x : ℂ) * (x : ℂ) ^ (s - 2) = (x : ℂ) ^ (s - 1) := by
    have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
    nth_rw 1 [← Complex.cpow_one (x : ℂ)]
    rw [← Complex.cpow_add _ _ hxC]
    congr 1
    ring
  have hexp : Complex.exp (-((r : ℂ) * ((x ^ 2 : ℝ) : ℂ))) = (Real.exp (-r * x ^ 2) : ℂ) := by
    rw [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg, neg_mul]
  rw [hpow, hexp, Complex.ofReal_mul, Complex.ofReal_ofNat]
  have h2ne : (2 : ℂ) ≠ 0 := two_ne_zero
  calc (2 : ℂ)⁻¹ * ((2 : ℂ) * (x : ℂ) * ((x : ℂ) ^ (s - 2) * (Real.exp (-r * x ^ 2) : ℂ)))
      = ((2 : ℂ)⁻¹ * 2) * ((Real.exp (-r * x ^ 2) : ℂ) * ((x : ℂ) * (x : ℂ) ^ (s - 2))) := by ring
    _ = (Real.exp (-r * x ^ 2) : ℂ) * (x : ℂ) ^ (s - 1) := by
        rw [inv_mul_cancel₀ h2ne, one_mul, hmul_pow]

/-- **Archimedean Real Gaussian Local Tate Zeta Integral (Even Character `1`)**:
for every `s : ℂ` with `0 < s.re`,
`∫_{ℝ} exp(-π x²) · |x|^{s - 1} dx = π^{-s/2} · Γ(s/2) = Complex.Gammaℝ s`. -/
theorem archTateZetaReal_gaussReal_eq_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    archTateZetaReal gaussReal (fun _ ↦ 1) s = Complex.Gammaℝ s := by
  unfold archTateZetaReal gaussReal
  simp only [mul_one]
  have heven : ∀ x : ℝ,
      (Real.exp (-Real.pi * (-x) ^ 2) : ℂ) * ((|-x| : ℝ) : ℂ) ^ (s - 1) =
        (Real.exp (-Real.pi * x ^ 2) : ℂ) * ((|x| : ℝ) : ℂ) ^ (s - 1) := by
    intro x
    rw [neg_sq, abs_neg]
  rw [integral_even_eq_two_mul_Ioi heven (integrableOn_gauss_Ioi Real.pi_pos hs)]
  have hcongr :
      ∫ x in Set.Ioi (0 : ℝ), (Real.exp (-Real.pi * x ^ 2) : ℂ) * ((|x| : ℝ) : ℂ) ^ (s - 1) =
        ∫ x in Set.Ioi (0 : ℝ), (Real.exp (-Real.pi * x ^ 2) : ℂ) * (x : ℂ) ^ (s - 1) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
    rw [abs_of_pos hx]
  rw [hcongr, two_mul_integral_gauss_Ioi Real.pi_pos hs, Complex.Gammaℝ_def]
  congr 1
  rw [one_div, Complex.inv_cpow _ _ (by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact Real.pi_pos.ne), neg_div, ← Complex.cpow_neg]

/-- Explicit `π^{-s/2} Γ(s/2)` form of the real Gaussian local Tate zeta integral. -/
theorem archTateZetaReal_gaussReal_eq_pi_cpow_mul_Gamma {s : ℂ} (hs : 0 < s.re) :
    archTateZetaReal gaussReal (fun _ ↦ 1) s = (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) :=
  archTateZetaReal_gaussReal_eq_Gammaℝ hs

/-- **Archimedean Real Gaussian Local Tate Zeta Integral (Odd Character `sign`)**:
for every `s : ℂ` with `0 < (s + 1).re` (in particular `0 < s.re`),
`∫_{ℝ} (x exp(-π x²)) · sign(x) · |x|^{s - 1} dx = Complex.Gammaℝ (s + 1)`. -/
theorem archTateZetaReal_gaussRealOdd_eq_Gammaℝ {s : ℂ} (hs : 0 < (s + 1).re) :
    archTateZetaReal gaussRealOdd (fun x ↦ (SignType.sign x : ℂ)) s = Complex.Gammaℝ (s + 1) := by
  have hrew :
      archTateZetaReal gaussRealOdd (fun x ↦ (SignType.sign x : ℂ)) s =
        archTateZetaReal gaussReal (fun _ ↦ 1) (s + 1) := by
    unfold archTateZetaReal gaussRealOdd gaussReal
    refine MeasureTheory.integral_congr_ae ?_
    have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
      rw [ae_iff]
      simp [measure_singleton]
    filter_upwards [hne] with x hx
    have hxs : (x : ℂ) * (SignType.sign x : ℂ) = ((|x| : ℝ) : ℂ) := by
      have hreal : x * (SignType.sign x : ℝ) = |x| := by
        cases h : SignType.sign x
        · exfalso
          have h0 : x = 0 := by
            rw [← sign_mul_abs x, h]
            simp
          exact hx h0
        · rw [← sign_mul_abs x, h]
          simp
        · rw [← sign_mul_abs x, h]
          simp
      have hcast := congrArg Complex.ofReal hreal
      rw [Complex.ofReal_mul] at hcast
      simpa only [← Complex.ofRealHom_eq_coe, SignType.map_cast] using hcast
    have habs_ne : ((|x| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr hx)
    have hpow : ((|x| : ℝ) : ℂ) * ((|x| : ℝ) : ℂ) ^ (s - 1) = ((|x| : ℝ) : ℂ) ^ (s + 1 - 1) := by
      nth_rw 1 [← Complex.cpow_one ((|x| : ℝ) : ℂ)]
      rw [← Complex.cpow_add _ _ habs_ne]
      congr 1
      ring
    calc (x : ℂ) * (Real.exp (-Real.pi * x ^ 2) : ℂ) * (SignType.sign x : ℂ) *
            ((|x| : ℝ) : ℂ) ^ (s - 1)
        = (Real.exp (-Real.pi * x ^ 2) : ℂ) *
            (((x : ℂ) * (SignType.sign x : ℂ)) * ((|x| : ℝ) : ℂ) ^ (s - 1)) := by ring
      _ = (Real.exp (-Real.pi * x ^ 2) : ℂ) * 1 * ((|x| : ℝ) : ℂ) ^ (s + 1 - 1) := by
          rw [hxs, hpow, mul_one]
  rw [hrew]
  exact archTateZetaReal_gaussReal_eq_Gammaℝ hs

/-- Concrete Archimedean complex-place radial Gaussian Tate zeta integral:
`Z_ℂ(e^{-2π |z|²}, 1, s) = 2 ∫_0^∞ exp(-2π r²) · (r²)^{s - 1} · (2 r dr)`. -/
def archTateZetaComplex (s : ℂ) : ℂ :=
  ∫ r in Set.Ioi (0 : ℝ),
    (2 : ℂ) * (Real.exp (-(2 * Real.pi) * r ^ 2) : ℂ) * ((r ^ 2 : ℝ) : ℂ) ^ (s - 1) * (2 * (r : ℂ))

/-- **Archimedean Complex Gaussian Local Tate Zeta Integral**:
for every `s : ℂ` with `0 < s.re`,
`Z_ℂ(e^{-2π |z|²}, 1, s) = 2 · (2π)^{-s} · Γ(s) = Complex.Gammaℂ s`. -/
theorem archTateZetaComplex_eq_Gammaℂ {s : ℂ} (hs : 0 < s.re) :
    archTateZetaComplex s = Complex.Gammaℂ s := by
  have h2pi : 0 < 2 * Real.pi := by positivity
  have h2s : 0 < (2 * s).re := by
    rw [show (2 * s).re = 2 * s.re by simp]
    linarith
  have hpt :
      Set.EqOn
        (fun r : ℝ ↦
          (2 : ℂ) * (Real.exp (-(2 * Real.pi) * r ^ 2) : ℂ) *
            ((r ^ 2 : ℝ) : ℂ) ^ (s - 1) * (2 * (r : ℂ)))
        (fun r : ℝ ↦
          (2 : ℂ) * ((2 : ℂ) * ((Real.exp (-(2 * Real.pi) * r ^ 2) : ℂ) * (r : ℂ) ^ (2 * s - 1))))
        (Set.Ioi 0) := by
    intro r hr
    dsimp only
    have hr0 : 0 < r := hr
    have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0.ne'
    have hsq : ((r ^ 2 : ℝ) : ℂ) ^ (s - 1) = (r : ℂ) ^ (2 * s - 2) := by
      rw [Complex.ofReal_pow, ← Complex.cpow_nat_mul']
      · congr 1
        push_cast
        ring
      · rw [Complex.arg_ofReal_of_nonneg hr0.le]
        linarith [Real.pi_pos]
      · rw [Complex.arg_ofReal_of_nonneg hr0.le]
        linarith [Real.pi_pos]
    have hmul : (r : ℂ) ^ (2 * s - 2) * (r : ℂ) = (r : ℂ) ^ (2 * s - 1) := by
      nth_rw 2 [← Complex.cpow_one (r : ℂ)]
      rw [← Complex.cpow_add _ _ hrC]
      congr 1
      ring
    rw [hsq]
    calc (2 : ℂ) * (Real.exp (-(2 * Real.pi) * r ^ 2) : ℂ) * (r : ℂ) ^ (2 * s - 2) * (2 * (r : ℂ))
        = (2 : ℂ) * ((2 : ℂ) * ((Real.exp (-(2 * Real.pi) * r ^ 2) : ℂ) * ((r : ℂ) ^ (2 * s - 2) * (r : ℂ)))) := by ring
      _ = (2 : ℂ) * ((2 : ℂ) * ((Real.exp (-(2 * Real.pi) * r ^ 2) : ℂ) * (r : ℂ) ^ (2 * s - 1))) := by
          rw [hmul]
  unfold archTateZetaComplex
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpt,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    two_mul_integral_gauss_Ioi h2pi h2s, Complex.Gammaℂ_def]
  have h2s2 : 2 * s / 2 = s := by ring
  rw [h2s2]
  have hpow : (1 / ((2 * Real.pi : ℝ) : ℂ)) ^ s = (2 * (Real.pi : ℂ)) ^ (-s) := by
    rw [one_div, Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg h2pi.le]
      exact Real.pi_pos.ne)]
    push_cast
    rw [← Complex.cpow_neg]
  rw [hpow]
  ring

/-- Archimedean product of local Gaussian Tate zeta integrals across all infinite places of an
arbitrary number field `K`: real places contribute `Z_ℝ(e^{-π x²}, 1, s) = Γ_ℝ(s)` and complex
places contribute `Z_ℂ(e^{-2π |z|²}, 1, s) = Γ_ℂ(s)`. -/
def archTateZetaField (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ := by
  classical
  exact ∏ w : InfinitePlace K,
    if w.IsReal then archTateZetaReal gaussReal (fun _ ↦ 1) s else archTateZetaComplex s

/-- **General Number Field Archimedean Tate Zeta Product Formula**:
for EVERY number field `K` and EVERY `s : ℂ` with `0 < s.re`,
`archTateZetaField K s = Gammaℝ(s) ^ r₁(K) * Gammaℂ(s) ^ r₂(K)`. -/
theorem archTateZetaField_eq_gamma_prod (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 0 < s.re) :
    archTateZetaField K s =
      (Complex.Gammaℝ s) ^ (InfinitePlace.nrRealPlaces K) *
        (Complex.Gammaℂ s) ^ (InfinitePlace.nrComplexPlaces K) := by
  classical
  unfold archTateZetaField
  rw [InfinitePlace.prod_eq_prod_mul_prod]
  congr 1
  · trans ∏ _w : {w : InfinitePlace K // w.IsReal}, Complex.Gammaℝ s
    · refine Finset.prod_congr rfl fun w _ ↦ ?_
      rw [if_pos w.2, archTateZetaReal_gaussReal_eq_Gammaℝ hs]
    · simp [InfinitePlace.nrRealPlaces]
  · trans ∏ _w : {w : InfinitePlace K // w.IsComplex}, Complex.Gammaℂ s
    · refine Finset.prod_congr rfl fun w _ ↦ ?_
      have hnr : ¬w.1.IsReal := (InfinitePlace.not_isReal_iff_isComplex).mpr w.2
      rw [if_neg hnr, archTateZetaComplex_eq_Gammaℂ hs]
    · simp [InfinitePlace.nrComplexPlaces]

end LocalTateArchimedean

/-! ## Section 5: Global Factorizable Tate Zeta Factorization & Exact Matching with `ζ(s)` and `L(s, χ)` -/

section GlobalFactorization

/-- A **factorizable Schwartz–Bruhat Tate datum** over a number field `K` with a finite set `S`
of exceptional (ramified/non-spherical) finite places, spherical local Satake parameters `α_v`
(with `‖α_v‖ ≤ 1`), and arbitrary local test-zeta values `localBad v s` at `v ∈ S`. -/
structure FactorizableTateDatum (K : Type*) [Field K] [NumberField K] where
  /-- Finite set of non-spherical finite places. -/
  badPlaces : Finset (HeightOneSpectrum (𝓞 K))
  /-- Local Satake parameters at finite places. -/
  satake : HeightOneSpectrum (𝓞 K) → ℂ
  /-- Tempered/unitary bound on Satake parameters (`‖α_v‖ ≤ 1`). -/
  norm_satake_le_one : ∀ v, ‖satake v‖ ≤ 1
  /-- Local zeta integral at bad places `v ∈ S`. -/
  badLocalZeta : HeightOneSpectrum (𝓞 K) → ℂ → ℂ

/-- Local finite-place factor of a factorizable Tate datum: equals `badLocalZeta v s` for
`v ∈ S`, and the spherical local Tate integral `localTateZetaFin v (α v) s` for `v ∉ S`. -/
def FactorizableTateDatum.localZeta {K : Type*} [Field K] [NumberField K]
    (D : FactorizableTateDatum K) (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) : ℂ := by
  classical
  exact if v ∈ D.badPlaces then D.badLocalZeta v s else localTateZetaFin v (D.satake v) s

/-- Global Tate zeta function `Z(Φ, χ, s) = Z_∞(s) · ∏'_v Z_v(Φ_v, χ_v, s)` of a factorizable
Schwartz–Bruhat datum over `K`. -/
def FactorizableTateDatum.globalZeta {K : Type*} [Field K] [NumberField K]
    (D : FactorizableTateDatum K) (s : ℂ) : ℂ :=
  archTateZetaField K s * ∏' v : HeightOneSpectrum (𝓞 K), D.localZeta v s

/-- **General Number-Field Factorizable Global Tate Zeta Product Factorization**:
whenever the unramified product away from `S` is multipliable and `0 < s.re`,
`Z(Φ, χ, s)` factorizes cleanly into the Archimedean Gamma product `Γ_ℝ(s)^{r₁} Γ_ℂ(s)^{r₂}`,
the finite product over `v ∈ S`, and the convergent unramified Euler product over `v ∉ S`! -/
theorem FactorizableTateDatum.globalZeta_factorization {K : Type*} [Field K] [NumberField K]
    (D : FactorizableTateDatum K) {s : ℂ} (hs : 0 < s.re)
    (hmult : Multipliable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ D.badPlaces} ↦
      (1 - D.satake v.1 * (residueCard v.1 : ℂ) ^ (-s))⁻¹) :
    D.globalZeta s =
      ((Complex.Gammaℝ s) ^ (InfinitePlace.nrRealPlaces K) *
        (Complex.Gammaℂ s) ^ (InfinitePlace.nrComplexPlaces K)) *
      (∏ v ∈ D.badPlaces, D.badLocalZeta v s) *
      (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ D.badPlaces},
        (1 - D.satake v.1 * (residueCard v.1 : ℂ) ^ (-s))⁻¹) := by
  classical
  have hbad_eq :
      (∏ v : {v : HeightOneSpectrum (𝓞 K) // v ∈ D.badPlaces}, D.localZeta v.1 s) =
        ∏ v ∈ D.badPlaces, D.badLocalZeta v s := by
    rw [Finset.prod_coe_sort D.badPlaces (fun v ↦ D.localZeta v s)]
    refine Finset.prod_congr rfl fun v hv ↦ ?_
    simp [FactorizableTateDatum.localZeta, hv]
  have hgood_eq :
      (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ D.badPlaces} ↦ D.localZeta v.1 s) =
      fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ D.badPlaces} ↦
        (1 - D.satake v.1 * (residueCard v.1 : ℂ) ^ (-s))⁻¹ := by
    funext v
    simp only [FactorizableTateDatum.localZeta, if_neg v.2]
    exact localTateZetaFin_eq_eulerFactor v.1 (D.norm_satake_le_one v.1) hs
  have hmult_good : Multipliable (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ D.badPlaces} ↦
      D.localZeta v.1 s) := by
    simpa only [hgood_eq] using hmult
  have hmult_bad : Multipliable (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∈ D.badPlaces} ↦
      D.localZeta v.1 s) := Multipliable.of_finite
  have hsplit :
      (∏' v : HeightOneSpectrum (𝓞 K), D.localZeta v s) =
        (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∈ D.badPlaces}, D.localZeta v.1 s) *
        (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ D.badPlaces}, D.localZeta v.1 s) := by
    let S : Set (HeightOneSpectrum (𝓞 K)) := (D.badPlaces : Set _)
    have h1 : (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∈ D.badPlaces}, D.localZeta v.1 s) =
        ∏' v : S, D.localZeta v.1 s := rfl
    have h2 : (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ D.badPlaces}, D.localZeta v.1 s) =
        ∏' v : (Sᶜ : Set _), D.localZeta v.1 s := rfl
    rw [h1, h2, tprod_subtype S (fun v ↦ D.localZeta v s),
      tprod_subtype (Sᶜ : Set _) (fun v ↦ D.localZeta v s),
      ← Multipliable.tprod_mul
        (multipliable_subtype_iff_mulIndicator.mp (hmult_bad : Multipliable fun v : S ↦ D.localZeta v.1 s))
        (multipliable_subtype_iff_mulIndicator.mp (hmult_good : Multipliable fun v : (Sᶜ : Set _) ↦ D.localZeta v.1 s))]
    refine tprod_congr fun v ↦ ?_
    by_cases hv : v ∈ S <;> simp [Set.mulIndicator, hv]
  unfold FactorizableTateDatum.globalZeta
  rw [archTateZetaField_eq_gamma_prod K hs, hsplit, tprod_fintype, hbad_eq, hgood_eq]
  ring

/-! ### Explicit Prime–Place Bijection `HeightOneSpectrum ℤ ≃ Nat.Primes` -/

/-- Construct the height-one prime ideal `(p) ⊂ ℤ` from a natural prime `p : Nat.Primes`. -/
def primeToHeightOne (p : Nat.Primes) : HeightOneSpectrum ℤ where
  asIdeal := Ideal.span {(p : ℤ)}
  isPrime := (Ideal.span_singleton_prime (Int.natCast_ne_zero.mpr p.2.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp p.2)
  ne_bot := Ideal.span_singleton_eq_bot.not.mpr (Int.natCast_ne_zero.mpr p.2.ne_zero)

/-- Extract the unique positive prime generator `p : Nat.Primes` of a height-one prime `v` of `ℤ`. -/
def heightOneIntToPrime (v : HeightOneSpectrum ℤ) : Nat.Primes := by
  let g : ℤ := Submodule.IsPrincipal.generator v.asIdeal
  have hspan : v.asIdeal = Ideal.span {g} := (Submodule.IsPrincipal.span_singleton_generator v.asIdeal).symm
  have hg0 : g ≠ 0 := by
    intro h
    rw [h, Ideal.span_singleton_zero] at hspan
    exact v.ne_bot hspan
  have hgprime : Prime g := (Ideal.span_singleton_prime hg0).mp (hspan ▸ v.isPrime)
  exact ⟨g.natAbs, Int.prime_iff_natAbs_prime.mp hgprime⟩

/-- Canonical bijection `HeightOneSpectrum ℤ ≃ Nat.Primes` between finite places of `ℚ`
and rational prime numbers. -/
def heightOneIntEquivPrimes : HeightOneSpectrum ℤ ≃ Nat.Primes where
  toFun := heightOneIntToPrime
  invFun := primeToHeightOne
  left_inv v := by
    apply HeightOneSpectrum.ext
    change Ideal.span {((Submodule.IsPrincipal.generator v.asIdeal).natAbs : ℤ)} = v.asIdeal
    have hspan : v.asIdeal = Ideal.span {Submodule.IsPrincipal.generator v.asIdeal} :=
      (Submodule.IsPrincipal.span_singleton_generator v.asIdeal).symm
    conv_rhs => rw [hspan]
    rw [Ideal.span_singleton_eq_span_singleton]
    exact (Int.associated_natAbs _).symm
  right_inv p := by
    apply Subtype.ext
    change (Submodule.IsPrincipal.generator (Ideal.span {(p : ℤ)})).natAbs = (p : ℕ)
    have hspan : Ideal.span {Submodule.IsPrincipal.generator (Ideal.span {(p : ℤ)})} =
        Ideal.span {(p : ℤ)} := Submodule.IsPrincipal.span_singleton_generator _
    have hassoc : Associated (Submodule.IsPrincipal.generator (Ideal.span {(p : ℤ)})) (p : ℤ) :=
      Ideal.span_singleton_eq_span_singleton.mp hspan
    have habs := Int.natAbs_eq_natAbs_iff.mpr (Int.associated_iff.mp hassoc)
    simpa using habs

@[simp]
theorem heightOneIntEquivPrimes_symm_apply (p : Nat.Primes) :
    heightOneIntEquivPrimes.symm p = primeToHeightOne p := rfl

/-- The residue cardinality `Nat.card (ℤ ⧸ (p))` of the finite place `(p)` equals `p`. -/
theorem absNorm_primeToHeightOne (p : Nat.Primes) :
    Ideal.absNorm (primeToHeightOne p).asIdeal = (p : ℕ) := by
  change Ideal.absNorm (Ideal.span {(p : ℤ)}) = (p : ℕ)
  rw [Ideal.absNorm_span_singleton]
  simp [Algebra.norm_self]

theorem residueCard_int_eq (v : HeightOneSpectrum ℤ) :
    Nat.card (ℤ ⧸ v.asIdeal) = (heightOneIntEquivPrimes v : ℕ) := by
  have hv : v = primeToHeightOne (heightOneIntEquivPrimes v) :=
    (heightOneIntEquivPrimes.symm_apply_apply v).symm
  conv_lhs => rw [hv]
  exact absNorm_primeToHeightOne (heightOneIntEquivPrimes v)

/-! ### Exact Global Tate Zeta Factorization over `ℚ` Matching `completedRiemannZeta` & `completedLFunction` -/

/-- Concrete finite-place local Tate zeta integral over `ℚ` at `v : HeightOneSpectrum ℤ`:
`Z_v(1_{ℤ_v}, α, s) = ∑'_{n : ℕ} (α(v) * (Nat.card (ℤ ⧸ v))^{-s})^n`. -/
def localTateZetaRat (α : HeightOneSpectrum ℤ → ℂ) (v : HeightOneSpectrum ℤ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, (α v * (Nat.card (ℤ ⧸ v.asIdeal) : ℂ) ^ (-s)) ^ n

/-- Evaluation of `localTateZetaRat` as the exact local Euler factor `(1 - α(v) p_v^{-s})⁻¹`. -/
theorem localTateZetaRat_eq_eulerFactor (α : HeightOneSpectrum ℤ → ℂ) (v : HeightOneSpectrum ℤ)
    {s : ℂ} (hα : ‖α v‖ ≤ 1) (hs : 0 < s.re) :
    localTateZetaRat α v s =
      (1 - α v * ((heightOneIntEquivPrimes v : ℕ) : ℂ) ^ (-s))⁻¹ := by
  unfold localTateZetaRat
  rw [residueCard_int_eq v]
  set p := heightOneIntEquivPrimes v
  have hp1 : (1 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.one_lt
  have hnorm : ‖α v * ((p : ℕ) : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.neg_re]
    have hrpow : ((p : ℕ) : ℝ) ^ (-s.re) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hp1 (neg_lt_zero.mpr hs)
    calc ‖α v‖ * ((p : ℕ) : ℝ) ^ (-s.re)
        ≤ 1 * ((p : ℕ) : ℝ) ^ (-s.re) := mul_le_mul_of_nonneg_right hα (by positivity)
      _ = ((p : ℕ) : ℝ) ^ (-s.re) := one_mul _
      _ < 1 := hrpow
  exact (hasSum_geometric_of_norm_lt_one hnorm).tsum_eq

/-- **Finite-Place Global Tate Product = Riemann Zeta `ζ(s)`** (`HasProd` form, `1 < s.re`):
`HasProd (fun v : HeightOneSpectrum ℤ ↦ Z_v(1_{ℤ_v}, 1, s)) (riemannZeta s)`. -/
theorem riemannZeta_hasProd_localTateZetaRat {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum ℤ ↦ localTateZetaRat (fun _ ↦ 1) v s) (riemannZeta s) := by
  have hs0 : 0 < s.re := zero_lt_one.trans hs
  have hbase := riemannZeta_eulerProduct_hasProd hs
  have hcomp : HasProd (fun v : HeightOneSpectrum ℤ ↦
      (1 - ((heightOneIntEquivPrimes v : ℕ) : ℂ) ^ (-s))⁻¹) (riemannZeta s) :=
    (Equiv.hasProd_iff heightOneIntEquivPrimes).mpr hbase
  refine hcomp.congr_fun fun v ↦ ?_
  rw [localTateZetaRat_eq_eulerFactor (fun _ ↦ 1) v (by simp) hs0, one_mul]

/-- **Finite-Place Global Tate Product = Riemann Zeta `ζ(s)`** (`tprod` form, `1 < s.re`). -/
theorem riemannZeta_eq_tprod_localTateZetaRat {s : ℂ} (hs : 1 < s.re) :
    ∏' v : HeightOneSpectrum ℤ, localTateZetaRat (fun _ ↦ 1) v s = riemannZeta s :=
  (riemannZeta_hasProd_localTateZetaRat hs).tprod_eq

/-- **GLOBAL TATE ZETA FACTORIZATION FOR THE COMPLETED RIEMANN ZETA FUNCTION `Λ(s)`**:
for every `s : ℂ` with `1 < s.re`, the product of the Archimedean Gaussian Tate integral
`Z_∞(e^{-π x²}, 1, s)` and the non-Archimedean spherical Tate product
`∏'_v Z_v(1_{ℤ_v}, 1, s)` over all finite places `v : HeightOneSpectrum ℤ` equals
Mathlib's `completedRiemannZeta s`! -/
theorem completedRiemannZeta_eq_globalTateZeta {s : ℂ} (hs : 1 < s.re) :
    archTateZetaReal gaussReal (fun _ ↦ 1) s *
      (∏' v : HeightOneSpectrum ℤ, localTateZetaRat (fun _ ↦ 1) v s) =
      completedRiemannZeta s := by
  have hs0 : 0 < s.re := zero_lt_one.trans hs
  have hs_ne : s ≠ 0 := Complex.ne_zero_of_one_lt_re hs
  rw [archTateZetaReal_gaussReal_eq_Gammaℝ hs0, riemannZeta_eq_tprod_localTateZetaRat hs,
    riemannZeta_def_of_ne_zero hs_ne,
    mul_div_cancel₀ _ (Complex.Gammaℝ_ne_zero_of_re_pos hs0)]

/-- **Global Tate Functional Equation for `completedRiemannZeta`**:
`completedRiemannZeta (1 - s) = completedRiemannZeta s`. -/
theorem completedRiemannZeta_functional_eq (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s :=
  completedRiemannZeta_one_sub s

/-- Local Satake parameter `χ(p_v)` at `v : HeightOneSpectrum ℤ` attached to a Dirichlet
character `χ : DirichletCharacter ℂ N` (`0` at ramified primes `p_v ∣ N`, `χ(p_v)` at
unramified primes `p_v ∤ N`). -/
def dirichletSatake {N : ℕ} (χ : DirichletCharacter ℂ N) (v : HeightOneSpectrum ℤ) : ℂ :=
  χ ((heightOneIntEquivPrimes v : ℕ) : ZMod N)

/-- Archimedean local Gaussian Tate zeta integral matching a Dirichlet character `χ`:
even Gaussian `e^{-π x²}` if `χ` is even, odd Gaussian `x e^{-π x²}` twisted by `sign`
if `χ` is odd. -/
def archTateZetaDirichlet {N : ℕ} (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ := by
  classical
  exact if χ.Even then archTateZetaReal gaussReal (fun _ ↦ 1) s
    else archTateZetaReal gaussRealOdd (fun x ↦ (SignType.sign x : ℂ)) s

/-- For every Dirichlet character `χ` and every `s` with `0 < s.re`, the Archimedean local
Gaussian Tate integral equals Mathlib's `DirichletCharacter.gammaFactor χ s`. -/
theorem archTateZetaDirichlet_eq_gammaFactor {N : ℕ} (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 0 < s.re) :
    archTateZetaDirichlet χ s = DirichletCharacter.gammaFactor χ s := by
  classical
  unfold archTateZetaDirichlet DirichletCharacter.gammaFactor
  split_ifs
  · exact archTateZetaReal_gaussReal_eq_Gammaℝ hs
  · have hs1 : 0 < (s + 1).re := by
      rw [Complex.add_re, Complex.one_re]
      linarith
    exact archTateZetaReal_gaussRealOdd_eq_Gammaℝ hs1

/-- **Finite-Place Global Tate Product = Dirichlet `L`-Function `L(s, χ)`** (`HasProd` form,
`1 < s.re`). -/
theorem dirichletLFunction_hasProd_localTateZetaRat {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum ℤ ↦ localTateZetaRat (dirichletSatake χ) v s)
      (DirichletCharacter.LFunction χ s) := by
  have hs0 : 0 < s.re := zero_lt_one.trans hs
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  have hbase := DirichletCharacter.LSeries_eulerProduct_hasProd χ hs
  have hcomp : HasProd (fun v : HeightOneSpectrum ℤ ↦
      (1 - χ ((heightOneIntEquivPrimes v : ℕ) : ZMod N) *
        ((heightOneIntEquivPrimes v : ℕ) : ℂ) ^ (-s))⁻¹) (LSeries (fun n ↦ χ n) s) :=
    (Equiv.hasProd_iff heightOneIntEquivPrimes).mpr hbase
  refine hcomp.congr_fun fun v ↦ ?_
  have hle : ‖dirichletSatake χ v‖ ≤ 1 := χ.norm_le_one _
  exact localTateZetaRat_eq_eulerFactor (dirichletSatake χ) v hle hs0

/-- **Finite-Place Global Tate Product = Dirichlet `L`-Function `L(s, χ)`** (`tprod` form,
`1 < s.re`). -/
theorem dirichletLFunction_eq_tprod_localTateZetaRat {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    ∏' v : HeightOneSpectrum ℤ, localTateZetaRat (dirichletSatake χ) v s =
      DirichletCharacter.LFunction χ s :=
  (dirichletLFunction_hasProd_localTateZetaRat χ hs).tprod_eq

/-- **GLOBAL TATE ZETA FACTORIZATION FOR EVERY DIRICHLET CHARACTER `χ`**:
for every `N ≥ 1`, every `χ : DirichletCharacter ℂ N`, and every `s : ℂ` with `1 < s.re`,
`Z_∞(χ, s) * ∏'_{v : HeightOneSpectrum ℤ} Z_v(χ, s) = DirichletCharacter.completedLFunction χ s`. -/
theorem completedLFunction_eq_globalTateZeta {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    archTateZetaDirichlet χ s *
      (∏' v : HeightOneSpectrum ℤ, localTateZetaRat (dirichletSatake χ) v s) =
      DirichletCharacter.completedLFunction χ s := by
  have hs0 : 0 < s.re := zero_lt_one.trans hs
  have hs_ne : s ≠ 0 := Complex.ne_zero_of_one_lt_re hs
  rw [archTateZetaDirichlet_eq_gammaFactor χ hs0,
    dirichletLFunction_eq_tprod_localTateZetaRat χ hs,
    DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs_ne)]
  have hgam_ne : DirichletCharacter.gammaFactor χ s ≠ 0 := by
    classical
    unfold DirichletCharacter.gammaFactor
    split_ifs
    · exact Complex.Gammaℝ_ne_zero_of_re_pos hs0
    · exact Complex.Gammaℝ_ne_zero_of_re_pos (by rw [Complex.add_re, Complex.one_re]; linarith)
  exact mul_div_cancel₀ _ hgam_ne

/-- **Global Tate Functional Equation for Every Primitive Dirichlet Character `χ`**:
for every primitive `χ : DirichletCharacter ℂ N` (`N ≥ 1`) and every `s : ℂ`,
`Λ(1 - s, χ) = N^{s - 1/2} · W(χ) · Λ(s, χ⁻¹)`, and on `1 < s.re` the right-hand side
equals `N^{s - 1/2} · W(χ) · Z_∞(χ⁻¹, s) · ∏'_v Z_v(χ⁻¹, s)`. -/
theorem completedLFunction_primitive_functional_eq_tate {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.completedLFunction χ (1 - s) =
      (N : ℂ) ^ (s - 1 / 2) * DirichletCharacter.rootNumber χ *
        (archTateZetaDirichlet χ⁻¹ s *
          ∏' v : HeightOneSpectrum ℤ, localTateZetaRat (dirichletSatake χ⁻¹) v s) := by
  rw [completedLFunction_eq_globalTateZeta χ⁻¹ hs]
  exact hχ.completedLFunction_one_sub s

/-- **Global Tate–Artin Factorization Bridge (connecting to `Stage4ClassFieldTheory`)**:
for every cyclotomic Galois character `ρ : Gal(ℚ(ζ_m)/ℚ) →* ℂˣ` (`m ≥ 1`) and `1 < s.re`,
the finite-place Tate product recovers `Stage4ClassFieldTheory.artinLSeries ρ s`, and
multiplying by the Archimedean Gaussian Tate integral recovers
`DirichletCharacter.completedLFunction (dirichletOfGal m ρ) s`. -/
theorem artinLSeries_eq_tprod_localTateZetaRat {m : ℕ} [NeZero m]
    (ρ : RHDirect.Stage4ClassFieldTheory.GalChar m) {s : ℂ} (hs : 1 < s.re) :
    ∏' v : HeightOneSpectrum ℤ,
        localTateZetaRat (dirichletSatake (RHDirect.Stage4ClassFieldTheory.dirichletOfGal m ρ)) v s =
      RHDirect.Stage4ClassFieldTheory.artinLSeries ρ s := by
  rw [dirichletLFunction_eq_tprod_localTateZetaRat _ hs,
    ← RHDirect.Stage4ClassFieldTheory.artinLSeries_eq_LFunction ρ hs]

theorem completedArtinLFunction_eq_globalTateZeta {m : ℕ} [NeZero m]
    (ρ : RHDirect.Stage4ClassFieldTheory.GalChar m) {s : ℂ} (hs : 1 < s.re) :
    archTateZetaDirichlet (RHDirect.Stage4ClassFieldTheory.dirichletOfGal m ρ) s *
      RHDirect.Stage4ClassFieldTheory.artinLSeries ρ s =
      DirichletCharacter.completedLFunction (RHDirect.Stage4ClassFieldTheory.dirichletOfGal m ρ) s := by
  rw [← artinLSeries_eq_tprod_localTateZetaRat ρ hs]
  exact completedLFunction_eq_globalTateZeta _ hs

end GlobalFactorization

/-! ## Section 6: Unified Unconditional Stage 5 Adelic & Tate Thesis Summary -/

/-- **Unified Unconditional Stage 5 Adelic & Tate Thesis Theorem** (`0` assumptions):
collects:
1. Concrete injective principal idele embedding `Kˣ ↪ 𝕀_K`,
2. Unconditional Artin–Whaples Product Formula `|principalIdele K x|_𝔸 = 1` for EVERY number
   field `K` and EVERY `x ∈ Kˣ`,
3. Exact norm-1 idele class sequence `1 → 𝕀_K¹ / Kˣ → 𝕀_K / Kˣ → ℝ_{>0} → 1`,
4. Finite-place unramified local Tate zeta = local Euler factor `(1 - χ_v(ϖ_v) q_v^{-s})⁻¹`,
5. Archimedean real & complex Gaussian local Tate integrals = `Γ_ℝ(s)`, `Γ_ℂ(s)`, and general
   number-field Gamma product `Γ_ℝ(s)^{r₁} Γ_ℂ(s)^{r₂}`,
6. Exact global Tate zeta factorization matching `completedRiemannZeta s` and
   `DirichletCharacter.completedLFunction χ s` on `1 < s.re`. -/
theorem stage5_adelicTate_unconditional :
    (∀ (K : Type) [Field K] [NumberField K],
      Function.Injective (principalIdele K) ∧
      (∀ x : Kˣ, ideleNorm (principalIdele K x) = 1) ∧
      (principalSubgroup K ≤ NormOneIdeles K) ∧
      Function.Injective (normOneClassIncl K) ∧
      (normOneClassIncl K).range = (ideleClassNorm K).ker ∧
      Function.Surjective (ideleClassNorm K)) ∧
    (∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
      (χ : (v.adicCompletion K)ˣ →* ℂˣ) (_ : IsUnramifiedLocalChar v χ)
      (ϖ : (v.adicCompletion K)ˣ)
      (_ : Valued.v (ϖ : v.adicCompletion K) = WithZero.exp (-1 : ℤ))
      (s : ℂ) (_ : ‖(χ ϖ : ℂ)‖ ≤ 1) (_ : 0 < s.re),
      localTateZetaUnramified v χ s =
        (1 - (χ ϖ : ℂ) * (Nat.card (𝓞 K ⧸ v.asIdeal) : ℂ) ^ (-s))⁻¹) ∧
    (∀ (K : Type) [Field K] [NumberField K] (s : ℂ), 0 < s.re →
      archTateZetaReal gaussReal (fun _ ↦ 1) s = Complex.Gammaℝ s ∧
      archTateZetaComplex s = Complex.Gammaℂ s ∧
      archTateZetaField K s =
        (Complex.Gammaℝ s) ^ (InfinitePlace.nrRealPlaces K) *
          (Complex.Gammaℂ s) ^ (InfinitePlace.nrComplexPlaces K)) ∧
    (∀ (s : ℂ), 1 < s.re →
      archTateZetaReal gaussReal (fun _ ↦ 1) s *
        (∏' v : HeightOneSpectrum ℤ, localTateZetaRat (fun _ ↦ 1) v s) =
        completedRiemannZeta s) ∧
    (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 < s.re →
      archTateZetaDirichlet χ s *
        (∏' v : HeightOneSpectrum ℤ, localTateZetaRat (dirichletSatake χ) v s) =
        DirichletCharacter.completedLFunction χ s) :=
  ⟨fun K _ _ ↦
    ⟨principalIdele_injective K,
     fun x ↦ ideleNorm_principal x,
     principalSubgroup_le_normOneIdeles K,
     normOneClassIncl_injective K,
     normOneClassIncl_range_eq_ker K,
     ideleClassNorm_surjective K⟩,
   fun _ _ _ v _ hunr _ hϖ _ hunit hs ↦
    localTateZetaUnramified_eq_eulerFactor v hunr hϖ hunit hs,
   fun K _ _ _ hs ↦
    ⟨archTateZetaReal_gaussReal_eq_Gammaℝ hs,
     archTateZetaComplex_eq_Gammaℂ hs,
     archTateZetaField_eq_gamma_prod K hs⟩,
   fun _ hs ↦ completedRiemannZeta_eq_globalTateZeta hs,
   fun _ _ χ _ hs ↦ completedLFunction_eq_globalTateZeta χ hs⟩

end RHDirect.Stage5AdelicTate

end
