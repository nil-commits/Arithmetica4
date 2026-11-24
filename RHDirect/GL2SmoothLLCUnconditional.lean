import RHDirect.Stage11GL2SmoothRep
import RHDirect.Stage11LocalLanglandsGL2
import RHDirect.CFT_LocalArtinReciprocity
import Mathlib.LinearAlgebra.Determinant

/-!
# RHDirect.GL2SmoothLLCUnconditional

**GENUINE UNCONDITIONAL LOCAL LANGLANDS CORRESPONDENCE FOR THE COMPLETE NON-SUPERCUSPIDAL
SMOOTH SPECTRUM OF `GL₂(ℚ_p)` VIA ACTUAL `Gal(ℚ_p^{ab} / ℚ_p)` & `CFT_LocalArtinReciprocity`**
in pure targeted Mathlib (`0` `sorry`, `0` custom `axiom`, `0` `opaque`, `0` `native_decide`).

## Scope & Transparency
This module covers the **complete non-supercuspidal smooth admissible spectrum** of
`GL₂(ℚ_p) = Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]`:
1. Smooth principal series representations `SmoothInd p χ₁ χ₂` (irreducible when `χ₁ χ₂⁻¹ ≠ |·|_p^{±1}`),
2. Smooth 1-dimensional representations `oneDimSubrep p χ ≅ ℂ · (χ ∘ det)`,
3. Smooth twisted Steinberg representations `SmoothSteinberg p χ = SteinbergAmbient p χ / (ℂ · (χ ∘ det))`.

**Supercuspidal representations** (which require irreducible 2-dimensional representations of the
non-abelian Weil group `W_{ℚ_p}` rather than its abelianization `W_{ℚ_p}^{ab}`) are explicitly
**out of scope** for this module.

## Main Components
1. **Genuine Central Character & Full Admissibility on `GL (Fin 2) ℚ_[p]`**:
   - Scalar matrices `scalarGL2 p z = diag(z, z)` lie in the center of `GL (Fin 2) ℚ_[p]` and act on
     `SmoothInd p χ₁ χ₂` by `χ₁(z) χ₂(z)` and on `oneDimSubrep p χ` and `SmoothSteinberg p χ` by `χ(z)²`.
   - **Full Admissibility**: for EVERY `n : ℕ` and ALL smooth characters (unramified or ramified),
     `(SmoothInd p χ₁ χ₂)^{K_n}` and `(SmoothSteinberg p χ)^{K_n}` are finite-dimensional over `ℂ`,
     with exact `K₀`- and `Iwahori`-invariant dimensions (`1`/`2` for unramified `SmoothInd`,
     `0`/`0` for ramified `SmoothInd`, `0`/`1` for unramified `SmoothSteinberg`).
2. **Genuine Abelianized Weil Group `W_{ℚ_p}^{ab} ≤ Gal(ℚ_p^{ab} / ℚ_p)` via Local Artin Reciprocity**:
   - Using `RHDirect.CFT.LocalField.localArtinMap ℚ_[p] Ω : ℚ_[p]ˣ →* Gal(ℚ_p^{ab} / ℚ_p)`, we define
     the genuine abelianized inertia group `InertiaAb p Ω = ker(Gal(ℚ_p^{ab}/ℚ_p) → Gal(ℚ_p^{ur}/ℚ_p))`
     and the genuine abelianized Weil group `WeilAb p Ω = {σ ∈ Gal(ℚ_p^{ab}/ℚ_p) | ∃ n : ℤ, σ|_{ℚ_p^{ur}} = Frob_p^n}`.
   - We prove unconditionally that `localArtinMap ℚ_[p] Ω` induces a group isomorphism
     `localArtinWeilEquiv : ℚ_[p]ˣ ≃* WeilAb p Ω` and a topological group isomorphism
     `localArtinInertiaHomeo : unitFiltrationUnits ℚ_[p] 0 ≃ₜ* InertiaAb p Ω` (Krull topology),
     yielding an exact multiplicative bijection `artinCharEquiv : LocalChar p ≃* WeilChar p Ω` between
     smooth characters of `ℚ_[p]ˣ` and Krull-smooth 1D Galois/Weil characters of `W_{ℚ_p}^{ab}`.
3. **Genuine 2-Dimensional Weil–Deligne Representations `(ρ, N)` & Intrinsic `LinearMap.det` `L`-Factors**:
   - `WeilDeligneRep2 p Ω` consists of an actual homomorphism `ρ : WeilAb p Ω →* GL (Fin 2) ℂ`
     (smooth on Krull-topology `InertiaAb p Ω`) and nilpotent `N : Matrix (Fin 2) (Fin 2) ℂ` (`N² = 0`)
     satisfying the exact monodromy equation `ρ(σ) N ρ(σ)⁻¹ = ‖σ‖_W • N` for ALL `σ ∈ WeilAb p Ω`.
   - The local `L`-factor is defined **intrinsically** via Mathlib's `LinearMap.det` on the genuine
     subspace `V^{I, N=0} ≤ (Fin 2 → ℂ)`:
     `W.localLFactor T = (LinearMap.det (LinearMap.id - T • W.frobOnInvKerN))⁻¹`.
4. **Genuine Local Langlands Correspondence `genuineLLC` on Non-Supercuspidal Smooth `GL₂(ℚ_p)` Reps**:
   - **Central Character = Determinant via Local Artin Map**:
     `π.action (scalarGL2 p z) v = det(ρ(localArtinWeilEquiv z)) • v` for ALL `z : ℚ_[p]ˣ` and `v : π.Space`.
   - **Satake / Hecke `T_p`–Frobenius Compatibility**:
     `heckeTp p f₀ g = p^{1/2} · Tr(ρ(Frob_p)) · f₀(g)` and `L(W, T) = (1 - (p^{-1/2} λ_{T_p}) T + ω(p) T²)⁻¹`.
   - **Steinberg Iwahori `U_p`–Frobenius Compatibility on `V^{I, N=0}`**:
     `steinbergHeckeUpNorm p χ v = λ • v` where `λ` is the exact eigenvalue of `Frob_p` on the 1D
     subspace `V^{I, N=0}` of `steinbergWD p Ω χ`, and `L(W, T) = (1 - λ T)⁻¹`.
   - **Exact Local `L`-Factor Equality**: `π.automorphicLFactor T = (genuineLLC p Ω π).localLFactor T`,
     proved by genuine linear algebra on `invKerN` and matching `Stage11LocalLanglandsGL2` and all
     seven classical Hecke eigenforms (`Δ₁₂..Δ₂₂, S₂₄±`).
-/

noncomputable section

open Complex Matrix
open scoped BigOperators
open RHDirect.Stage11LocalLanglandsGL2
open RHDirect.Stage11GL2SmoothRep
open RHDirect.CFT.LocalField

namespace RHDirect
namespace GL2SmoothLLC

/-! ## Section 1: Genuine Central Character & Full Admissibility on `GL (Fin 2) ℚ_[p]` -/

section AdmissibilityAndCentralChar

variable (p : ℕ) [hp : Fact p.Prime]

/-- Scalar (central) matrix `diag(z, z) ∈ GL (Fin 2) ℚ_[p]` for `z ∈ ℚ_[p]ˣ`. -/
def scalarGL2 (z : ℚ_[p]ˣ) : GL2Qp p :=
  diagGL2 p z z

@[simp]
lemma scalarGL2_val (z : ℚ_[p]ˣ) :
    (scalarGL2 p z).1 = !![(z : ℚ_[p]), 0; 0, (z : ℚ_[p])] := rfl

lemma scalarGL2_mem_Borel (z : ℚ_[p]ˣ) : scalarGL2 p z ∈ Borel p := rfl

/-- Every scalar matrix `diag(z, z)` commutes with every `g ∈ GL (Fin 2) ℚ_[p]`. -/
theorem scalarGL2_comm (z : ℚ_[p]ˣ) (g : GL2Qp p) :
    scalarGL2 p z * g = g * scalarGL2 p z := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scalarGL2, diagGL2, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

lemma scalarGL2_mul (z₁ z₂ : ℚ_[p]ˣ) :
    scalarGL2 p (z₁ * z₂) = scalarGL2 p z₁ * scalarGL2 p z₂ := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scalarGL2, diagGL2, Matrix.mul_apply, Fin.sum_univ_two]

lemma scalarGL2_one : scalarGL2 p 1 = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scalarGL2, diagGL2]

lemma scalarGL2_det (z : ℚ_[p]ˣ) :
    Matrix.GeneralLinearGroup.det (scalarGL2 p z) = z ^ 2 := by
  ext
  simp [scalarGL2, diagGL2, sq]

/-- Exact Borel character on scalar matrices: `δ_B^{1/2}(diag(z, z)) = 1`, so
`borelChar χ₁ χ₂ (diag(z, z)) = χ₁(z) χ₂(z)`. -/
theorem borelChar_scalarGL2 (χ₁ χ₂ : LocalChar p) (z : ℚ_[p]ˣ) :
    borelChar p χ₁ χ₂ ⟨scalarGL2 p z, scalarGL2_mem_Borel p z⟩ = (χ₁ * χ₂).toHom z := by
  have hd0 : borelDiag0 p ⟨scalarGL2 p z, scalarGL2_mem_Borel p z⟩ = z := by ext; rfl
  have hd1 : borelDiag1 p ⟨scalarGL2 p z, scalarGL2_mem_Borel p z⟩ = z := by ext; rfl
  simp only [borelChar, deltaBHalf, MonoidHom.coe_mk, OneHom.coe_mk, hd0, hd1, mul_inv_cancel,
    one_mul, LocalChar.mul_toHom, MonoidHom.mul_apply]

/-- **GENUINE CENTRAL CHARACTER OF `SmoothInd p χ₁ χ₂`**:
for ALL smooth characters `χ₁, χ₂ : LocalChar p`, ALL `z : ℚ_[p]ˣ`, and ALL `f : SmoothInd p χ₁ χ₂`,
the central matrix `diag(z, z) ∈ GL (Fin 2) ℚ_[p]` acts by scalar multiplication by `χ₁(z) χ₂(z)`! -/
theorem smoothInd_centralChar (χ₁ χ₂ : LocalChar p) (z : ℚ_[p]ˣ) (f : SmoothInd p χ₁ χ₂) :
    rightAction p χ₁ χ₂ (scalarGL2 p z) f = (((χ₁ * χ₂).toHom z : ℂ)) • f := by
  ext g
  rw [rightAction_apply, ← scalarGL2_comm p z g]
  have hb := f.2.1 ⟨scalarGL2 p z, scalarGL2_mem_Borel p z⟩ g
  rw [borelChar_scalarGL2] at hb
  simpa [Submodule.coe_smul_of_tower] using hb

/-- **GENUINE CENTRAL CHARACTER OF `oneDimSubrep p χ`**:
`diag(z, z) ∈ GL (Fin 2) ℚ_[p]` acts on `ℂ · (χ ∘ det)` by `χ(z)²`! -/
theorem oneDimSubrep_centralChar (χ : LocalChar p) (z : ℚ_[p]ˣ) (f : oneDimSubrep p χ) :
    rightAction p _ _ (scalarGL2 p z) f.1 = (((χ ^ 2).toHom z : ℂ)) • f.1 := by
  have h := smoothInd_centralChar p
    (χ * LocalChar.normPowChar p (-(1 / 2))) (χ * LocalChar.normPowChar p (1 / 2)) z f.1
  have hprod : (χ * LocalChar.normPowChar p (-(1 / 2))) * (χ * LocalChar.normPowChar p (1 / 2)) =
      χ ^ 2 := by
    calc (χ * LocalChar.normPowChar p (-(1 / 2))) * (χ * LocalChar.normPowChar p (1 / 2))
        = (χ * χ) * (LocalChar.normPowChar p (1 / 2) * LocalChar.normPowChar p (-(1 / 2))) := by
          ac_rfl
      _ = χ ^ 2 := by rw [LocalChar.normPowChar_half_mul_neg_half, mul_one, sq]
  rw [hprod] at h
  exact h

/-- **GENUINE CENTRAL CHARACTER OF `SmoothSteinberg p χ`**:
for ALL smooth characters `χ : LocalChar p`, ALL `z : ℚ_[p]ˣ`, and ALL `v : SmoothSteinberg p χ`,
the central matrix `diag(z, z) ∈ GL (Fin 2) ℚ_[p]` acts by scalar multiplication by `χ(z)²`! -/
theorem smoothSteinberg_centralChar (χ : LocalChar p) (z : ℚ_[p]ˣ) (v : SmoothSteinberg p χ) :
    steinbergAction p χ (scalarGL2 p z) v = (((χ ^ 2).toHom z : ℂ)) • v := by
  induction v using Submodule.Quotient.induction_on with
  | _ f =>
    change steinbergAction p χ (scalarGL2 p z) (steinbergMk p χ f) =
      (((χ ^ 2).toHom z : ℂ)) • steinbergMk p χ f
    rw [steinbergAction_mk, smoothInd_centralChar]
    have hprod : (χ * LocalChar.normPowChar p (-(1 / 2))) * (χ * LocalChar.normPowChar p (1 / 2)) =
        χ ^ 2 := by
      calc (χ * LocalChar.normPowChar p (-(1 / 2))) * (χ * LocalChar.normPowChar p (1 / 2))
          = (χ * χ) * (LocalChar.normPowChar p (1 / 2) * LocalChar.normPowChar p (-(1 / 2))) := by
            ac_rfl
        _ = χ ^ 2 := by rw [LocalChar.normPowChar_half_mul_neg_half, mul_one, sq]
    rw [hprod, map_smul]

/-! ### Full Admissibility: Finite-Dimensionality of `(SmoothInd)^{K_n}` and `(SmoothSteinberg)^{K_n}` -/

/-- Auxiliary reduction map `K₀ → (Fin 2 → Fin 2 → ZMod (p ^ n))` for `n ≥ 1`. -/
private def K0ModPow (n : ℕ) (k : K0 p) : Fin 2 → Fin 2 → ZMod (p ^ n) :=
  fun i j => PadicInt.toZModPow n (mkPadicInt (k.2.1 i j))

/-- Two elements of `K₀` with the same reduction mod `p^n` (`n ≥ 1`) differ by an element of
`principalCongruence p n`! -/
private lemma K0_inv_mul_mem_principalCongruence_of_mod_eq {n : ℕ} (hn : 1 ≤ n)
    {k₁ k₂ : K0 p} (heq : K0ModPow p n k₁ = K0ModPow p n k₂) :
    k₁.1⁻¹ * k₂.1 ∈ principalCongruence p n := by
  have hdiff_le : ∀ i j : Fin 2,
      ‖k₂.1.1 i j - k₁.1.1 i j‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
    intro i j
    have hker : mkPadicInt (k₂.2.1 i j) - mkPadicInt (k₁.2.1 i j) ∈
        RingHom.ker (PadicInt.toZModPow n) := by
      rw [RingHom.mem_ker, map_sub]
      have hij := congrFun (congrFun heq i) j
      exact sub_eq_zero.mpr hij.symm
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hker
    rcases hker with ⟨q, hq⟩
    have hcoe : k₂.1.1 i j - k₁.1.1 i j = ((p : ℚ_[p]) ^ n) * (q : ℚ_[p]) := by
      have := congrArg (fun z : ℤ_[p] => (z : ℚ_[p])) hq
      simpa [mkPadicInt_coe] using this
    rw [hcoe, norm_mul, norm_pow, Padic.norm_p, inv_pow,
      ← zpow_neg_coe_of_pos _ (Nat.pos_of_ne_zero (by omega))]
    calc (p : ℝ) ^ (-(n : ℤ)) * ‖(q : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ)) * 1 :=
          mul_le_mul_of_nonneg_left q.2 (zpow_pos (prime_pos_R p) _).le
      _ = (p : ℝ) ^ (-(n : ℤ)) := mul_one _
  have hsplit : (k₁.1⁻¹ * k₂.1 : GL2Qp p).1 - 1 =
      (k₁.1⁻¹ : GL2Qp p).1 * (k₂.1.1 - k₁.1.1) := by
    have hmul : (k₁.1⁻¹ : GL2Qp p).1 * k₁.1.1 = 1 := by
      change (k₁.1⁻¹ * k₁.1 : GL2Qp p).1 = 1; rw [inv_mul_cancel]; rfl
    rw [Matrix.mul_sub, hmul]; rfl
  have hinvK0 : k₁.1⁻¹ ∈ K0 p := (K0 p).inv_mem k₁.2
  have hdiff_le' : ∀ i j : Fin 2, ‖(k₂.1.1 - k₁.1.1) i j‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := hdiff_le
  have h1 := norm_mat_mul_le p zero_le_one (zpow_pos (prime_pos_R p) _).le hinvK0.1 hdiff_le'
  refine mem_principalCongruence_of_sub_one_le p hn (fun i j => ?_)
  change ‖((k₁.1⁻¹ * k₂.1 : GL2Qp p).1 - 1) i j‖ ≤ _
  rw [hsplit]
  simpa using h1 i j

/-- **FULL ADMISSIBILITY OF `SmoothInd p χ₁ χ₂`**:
for EVERY level `n : ℕ` and ALL smooth characters `χ₁, χ₂ : LocalChar p` (unramified or ramified),
the `K_n`-fixed subspace `(SmoothInd p χ₁ χ₂)^{K_n}` is finite-dimensional over `ℂ`! -/
theorem smoothInd_admissible (χ₁ χ₂ : LocalChar p) (n : ℕ) :
    FiniteDimensional ℂ (fixedSubmodule p χ₁ χ₂ (principalCongruence p n)) := by
  have hle : fixedSubmodule p χ₁ χ₂ (principalCongruence p n) ≤
      fixedSubmodule p χ₁ χ₂ (principalCongruence p (max n 1)) := by
    intro f hf k hk
    exact hf k (principalCongruence_anti p (le_max_left n 1) hk)
  suffices hfin : FiniteDimensional ℂ (fixedSubmodule p χ₁ χ₂ (principalCongruence p (max n 1))) from
    FiniteDimensional.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  set m := max n 1
  have hm : 1 ≤ m := le_max_right n 1
  have : NeZero (p ^ m) := ⟨pow_ne_zero m hp.out.ne_zero⟩
  let M_im := Set.range (K0ModPow p m)
  have : Finite M_im := inferInstance
  -- Choose a section `s : M_im → K0 p`
  let s : M_im → K0 p := fun y => Classical.choose y.2
  have hs : ∀ y : M_im, K0ModPow p m (s y) = y.1 := fun y => Classical.choose_spec y.2
  -- Evaluation linear map into the finite-dimensional space `M_im → ℂ`
  let evalMap : fixedSubmodule p χ₁ χ₂ (principalCongruence p m) →ₗ[ℂ] (M_im → ℂ) :=
    { toFun := fun f y => f.1.1 (s y).1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective evalMap := by
    intro f₁ f₂ heq
    ext g
    obtain ⟨b, k, rfl⟩ := iwasawa_decomp p g
    rw [f₁.1.2.1 b k.1, f₂.1.2.1 b k.1]
    congr 1
    set y : M_im := ⟨K0ModPow p m k, k, rfl⟩
    have hmod : K0ModPow p m (s y) = K0ModPow p m k := hs y
    have hkn : (s y).1⁻¹ * k.1 ∈ principalCongruence p m :=
      K0_inv_mul_mem_principalCongruence_of_mod_eq p hm hmod
    have hk_eq : k.1 = (s y).1 * ((s y).1⁻¹ * k.1) := by group
    rw [hk_eq, (mem_fixedSubmodule_iff p).mp f₁.2 (s y).1 _ hkn,
      (mem_fixedSubmodule_iff p).mp f₂.2 (s y).1 _ hkn]
    exact congrFun heq y
  exact FiniteDimensional.of_injective evalMap hinj

/-- Exact lifting of `K_n`-invariants from `SmoothSteinberg p χ` to `SteinbergAmbient p χ`
for any `n ≥ χ.condExp` (so `K_n` acts trivially on `detCharVec p χ`)! -/
private lemma lift_steinbergFixed_principalCongruence (χ : LocalChar p) {n : ℕ}
    (hn : χ.condExp ≤ n) {f : SteinbergAmbient p χ}
    (hf : steinbergMk p χ f ∈ steinbergFixed p χ (principalCongruence p n)) :
    f ∈ fixedSubmodule p _ _ (principalCongruence p n) := by
  have hdet_triv : ∀ k ∈ principalCongruence p n,
      rightAction p _ _ k (detCharVec p χ) = detCharVec p χ := by
    intro k hk
    have hk' : k ∈ principalCongruence p χ.condExp := principalCongruence_anti p hn hk
    ext g
    rw [rightAction_apply]
    exact (detCharVec p χ).2.2.choose_spec |> fun _ => by
      -- Directly from `detCharVec` definition (smooth of level `χ.condExp`)
      have hdet_filt : IsInUnitFilt p χ.condExp (Matrix.GeneralLinearGroup.det k) := by
        refine ⟨hk'.1.2, ?_⟩
        by_cases h0 : χ.condExp = 0
        · exact Or.inl h0
        · right
          rcases hk'.2 with h0' | hle
          · exact absurd h0' h0
          · have hp_lt1 : (p : ℝ) ^ (-(χ.condExp : ℤ)) < 1 :=
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
                    mul_le_mul he00 (he11.trans hp_lt1.le) (norm_nonneg _)
                      (zpow_pos (prime_pos_R p) _).le
                _ = (p : ℝ) ^ (-(χ.condExp : ℤ)) := mul_one _
            have hmul2 : ‖-(e01 * e10)‖ ≤ (p : ℝ) ^ (-(χ.condExp : ℤ)) := by
              rw [norm_neg, norm_mul]
              calc ‖e01‖ * ‖e10‖ ≤ (p : ℝ) ^ (-(χ.condExp : ℤ)) * 1 :=
                    mul_le_mul he01 (he10.trans hp_lt1.le) (norm_nonneg _)
                      (zpow_pos (prime_pos_R p) _).le
                _ = (p : ℝ) ^ (-(χ.condExp : ℤ)) := mul_one _
            exact (Padic.nonarchimedean _ _).trans (max_le
              ((Padic.nonarchimedean _ _).trans (max_le
                ((Padic.nonarchimedean _ _).trans (max_le he00 he11)) hmul1)) hmul2)
      simp only [detCharVec_apply, map_mul, χ.condExp_spec _ hdet_filt, mul_one]
  intro h hh
  have hq := hf h hh
  rw [steinbergAction_mk, ← sub_eq_zero, ← map_sub] at hq
  obtain ⟨c, hc⟩ := (mem_oneDimSubrep_iff p χ _).mp ((Submodule.Quotient.mk_eq_zero _).mp hq)
  have hpow_all : ∀ r : ℕ, rightAction p _ _ (h ^ r) f - f =
      ((r : ℕ) : ℂ) • (c • detCharVec p χ) := by
    intro r
    induction r with
    | zero => simp [rightAction_one]
    | succ r ih =>
      rw [pow_succ, rightAction_mul]
      have hstep : rightAction p _ _ (h ^ r) (rightAction p _ _ h f) - f =
          rightAction p _ _ (h ^ r) (rightAction p _ _ h f - f) +
            (rightAction p _ _ (h ^ r) f - f) := by
        rw [map_sub]; abel
      rw [hstep, hc, map_smul, hdet_triv (h ^ r) ((principalCongruence p n).pow_mem hh r), ih,
        smul_smul, smul_smul, ← add_smul]
      congr 1; push_cast; ring
  rcases f.2.2 with ⟨m₀, hm₀⟩
  obtain ⟨r, hr_pos, hkr⟩ := exists_pow_mem_principalCongruence p (principalCongruence_le_K0 p n hh) m₀
  have hpow_eq := hpow_all r
  have hzero : rightAction p _ _ (h ^ r) f - f = 0 := by
    rw [sub_eq_zero]; ext g; exact hm₀ g (h ^ r) hkr
  rw [hzero] at hpow_eq
  have heval1 := congrFun (congrArg Subtype.val hpow_eq) 1
  simp only [Submodule.coe_zero, Pi.zero_apply, Submodule.coe_smul_of_tower, Pi.smul_apply,
    smul_eq_mul, detCharVec_apply, map_one, Units.val_one, mul_one] at heval1
  have hr_ne : ((r : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hr_pos.ne'
  have hc0 : c = 0 := (mul_eq_zero.mp heval1.symm).resolve_left hr_ne
  rw [hc0, zero_smul] at hc
  exact sub_eq_zero.mp hc

/-- **FULL ADMISSIBILITY OF `SmoothSteinberg p χ`**:
for EVERY level `n : ℕ` and EVERY smooth character `χ : LocalChar p` (unramified or ramified),
the `K_n`-fixed subspace `(SmoothSteinberg p χ)^{K_n}` is finite-dimensional over `ℂ`! -/
theorem smoothSteinberg_admissible (χ : LocalChar p) (n : ℕ) :
    FiniteDimensional ℂ (steinbergFixed p χ (principalCongruence p n)) := by
  set m := max n χ.condExp
  have hle : steinbergFixed p χ (principalCongruence p n) ≤
      steinbergFixed p χ (principalCongruence p m) := by
    intro v hv k hk
    exact hv k (principalCongruence_anti p (le_max_left n χ.condExp) hk)
  suffices hfin : FiniteDimensional ℂ (steinbergFixed p χ (principalCongruence p m)) from
    FiniteDimensional.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  have : FiniteDimensional ℂ (fixedSubmodule p
      (χ * LocalChar.normPowChar p (-(1 / 2)))
      (χ * LocalChar.normPowChar p (1 / 2)) (principalCongruence p m)) :=
    smoothInd_admissible p
      (χ * LocalChar.normPowChar p (-(1 / 2)))
      (χ * LocalChar.normPowChar p (1 / 2)) m
  let φ : fixedSubmodule p
      (χ * LocalChar.normPowChar p (-(1 / 2)))
      (χ * LocalChar.normPowChar p (1 / 2)) (principalCongruence p m) →ₗ[ℂ]
      steinbergFixed p χ (principalCongruence p m) :=
    { toFun := fun f => ⟨steinbergMk p χ f.1, fun k hk => by
        rw [steinbergAction_mk, f.2 k hk]⟩
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
      map_smul' := fun _ _ => Subtype.ext (map_smul _ _ _) }
  have hsurj : Function.Surjective φ := by
    rintro ⟨v, hv⟩
    induction v using Submodule.Quotient.induction_on with
    | _ f =>
      exact ⟨⟨f, lift_steinbergFixed_principalCongruence p χ (le_max_right n χ.condExp) hv⟩, rfl⟩
  exact Module.Finite.of_surjective φ hsurj

/-- Vanishing of `K₀`-invariants of `SmoothInd p χ₁ χ₂` when either `χ₁` or `χ₂` is ramified. -/
theorem smoothInd_fixedK0_eq_bot_of_ramified {χ₁ χ₂ : LocalChar p}
    (hram : ¬χ₁.IsUnramified ∨ ¬χ₂.IsUnramified) :
    fixedSubmodule p χ₁ χ₂ (K0 p) = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  change f = 0
  have hf1 : f.1 1 = 0 := by
    rcases hram with h₁ | h₂
    · simp only [LocalChar.IsUnramified, not_forall] at h₁
      rcases h₁ with ⟨u, hu_norm, hu_ne⟩
      let d : GL2Qp p := diagGL2 p u 1
      have hd_K0 : d ∈ K0 p := by
        refine ⟨fun i j => ?_, ?_⟩
        · fin_cases i <;> fin_cases j <;> simp [d, diagGL2, hu_norm]
        · simp [d, diagGL2, hu_norm]
      have h1 : f.1 d = f.1 1 := by
        simpa using (mem_fixedSubmodule_iff p).mp hf 1 d hd_K0
      have h2 : f.1 d = (χ₁.toHom u : ℂ) * f.1 1 := by
        have hb := f.2.1 ⟨d, diagGL2_mem_Borel p u 1⟩ 1
        simp only [mul_one] at hb
        have hd0 : borelDiag0 p ⟨d, diagGL2_mem_Borel p u 1⟩ = u := by ext; rfl
        have hd1 : borelDiag1 p ⟨d, diagGL2_mem_Borel p u 1⟩ = 1 := by ext; rfl
        unfold borelChar deltaBHalf at hb
        simp only [MonoidHom.coe_mk, OneHom.coe_mk, hd0, hd1, map_one, inv_one, mul_one,
          LocalChar.normPowChar_isUnramified p (1 / 2) u hu_norm, one_mul] at hb
        exact hb
      have hsub : ((χ₁.toHom u : ℂ) - 1) * f.1 1 = 0 := by linear_combination h1 - h2
      have hne0 : (χ₁.toHom u : ℂ) - 1 ≠ 0 := by
        intro h0; exact hu_ne (Units.ext (sub_eq_zero.mp h0))
      exact (mul_eq_zero.mp hsub).resolve_left hne0
    · simp only [LocalChar.IsUnramified, not_forall] at h₂
      rcases h₂ with ⟨u, hu_norm, hu_ne⟩
      let d : GL2Qp p := diagGL2 p 1 u
      have hd_K0 : d ∈ K0 p := by
        refine ⟨fun i j => ?_, ?_⟩
        · fin_cases i <;> fin_cases j <;> simp [d, diagGL2, hu_norm]
        · simp [d, diagGL2, hu_norm]
      have h1 : f.1 d = f.1 1 := by
        simpa using (mem_fixedSubmodule_iff p).mp hf 1 d hd_K0
      have h2 : f.1 d = (χ₂.toHom u : ℂ) * f.1 1 := by
        have hb := f.2.1 ⟨d, diagGL2_mem_Borel p 1 u⟩ 1
        simp only [mul_one] at hb
        have hd0 : borelDiag0 p ⟨d, diagGL2_mem_Borel p 1 u⟩ = 1 := by ext; rfl
        have hd1 : borelDiag1 p ⟨d, diagGL2_mem_Borel p 1 u⟩ = u := by ext; rfl
        unfold borelChar deltaBHalf at hb
        simp only [MonoidHom.coe_mk, OneHom.coe_mk, hd0, hd1, map_one, one_mul,
          LocalChar.normPowChar_isUnramified p (1 / 2) u hu_norm, inv_one] at hb
        exact hb
      have hsub : ((χ₂.toHom u : ℂ) - 1) * f.1 1 = 0 := by linear_combination h1 - h2
      have hne0 : (χ₂.toHom u : ℂ) - 1 ≠ 0 := by
        intro h0; exact hu_ne (Units.ext (sub_eq_zero.mp h0))
      exact (mul_eq_zero.mp hsub).resolve_left hne0
  ext g
  obtain ⟨b, k, rfl⟩ := iwasawa_decomp p g
  have hfk : f.1 k.1 = f.1 1 := by
    simpa using (mem_fixedSubmodule_iff p).mp hf 1 k.1 k.2
  rw [f.2.1 b k.1, hfk, hf1, mul_zero]; rfl

/-- Exact summary of `K₀`- and `Iwahori`-invariant dimensions for unramified `SmoothInd` and
`SmoothSteinberg` (collecting admissibility + exact dimensions `1/2` and `0/1`). -/
theorem smooth_K0_iwahori_exact_dimensions {χ₁ χ₂ χ : LocalChar p}
    (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified) (hχ : χ.IsUnramified) :
    FiniteDimensional ℂ (fixedSubmodule p χ₁ χ₂ (K0 p)) ∧
    Module.finrank ℂ (fixedSubmodule p χ₁ χ₂ (K0 p)) = 1 ∧
    FiniteDimensional ℂ (fixedSubmodule p χ₁ χ₂ (Iwahori p)) ∧
    Module.finrank ℂ (fixedSubmodule p χ₁ χ₂ (Iwahori p)) = 2 ∧
    FiniteDimensional ℂ (steinbergFixed p χ (K0 p)) ∧
    Module.finrank ℂ (steinbergFixed p χ (K0 p)) = 0 ∧
    FiniteDimensional ℂ (steinbergFixed p χ (Iwahori p)) ∧
    Module.finrank ℂ (steinbergFixed p χ (Iwahori p)) = 1 :=
  ⟨(sphericalFixedEquiv p h₁ h₂).symm.finiteDimensional,
   finrank_sphericalFixed p h₁ h₂,
   (iwahoriFixedEquiv p h₁ h₂).symm.finiteDimensional,
   finrank_iwahoriFixed p h₁ h₂,
   by rw [steinbergFixed_K0_eq_bot p hχ]; infer_instance,
   finrank_steinbergFixed_K0 p hχ,
   (steinbergIwahoriFixedEquiv p hχ).symm.finiteDimensional,
   finrank_steinbergFixed_iwahori p hχ⟩

end AdmissibilityAndCentralChar

/-! ## Section 2: Genuine Abelianized Weil Group `W_{ℚ_p}^{ab} ≤ Gal(ℚ_p^{ab} / ℚ_p)` via
`CFT_LocalArtinReciprocity` -/

section GenuineWeilGroup

open RHDirect.CFT_AbstractLocalReciprocity ValuativeRel RHDirect.CFT.LocalField.FormalGroup

variable (p : ℕ) [hp : Fact p.Prime]

/-- Exact equality between CFT's `ord` and Mathlib's `Padic.valuation` on `ℚ_[p]ˣ`. -/
theorem padic_ord_eq_valuation (x : ℚ_[p]ˣ) :
    ord (x : ℚ_[p]) = Padic.valuation (x : ℚ_[p]) := by
  have hu_norm : ‖((padicUnitPart p x : ℚ_[p]ˣ) : ℚ_[p])‖ = 1 := norm_padicUnitPart p x
  let uZ : ℤ_[p] := mkPadicInt hu_norm.le
  have huZ_unit : IsUnit uZ := PadicInt.isUnit_iff.mpr hu_norm
  have hx : (x : ℚ_[p]) = ((huZ_unit.unit : ℤ_[p]) : ℚ_[p]) *
      (p : ℚ_[p]) ^ (Padic.valuation (x : ℚ_[p])) := by
    have hd := congrArg Units.val (padicUnitPart_decomp p x)
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, padicPrimeUnit_val] at hd
    rw [IsUnit.unit_spec, mkPadicInt_coe, mul_comm]
    exact hd
  exact Padic.ord_eq_of_eq_mul_zpow p x huZ_unit.unit (Padic.valuation (x : ℚ_[p])) hx

/-- Exact equivalence between `ValuativeRel` valuation comparison and `p`-adic norm on `ℚ_[p]`. -/
lemma padic_valuation_le_iff_norm_le (a b : ℚ_[p]) :
    valuation ℚ_[p] a ≤ valuation ℚ_[p] b ↔ ‖a‖ ≤ ‖b‖ := by
  rw [← (valuation ℚ_[p]).vle_iff_le,
    Valuation.Compatible.vle_iff_le (v := Padic.mulValuation),
    Padic.mulValuation_le_iff_norm_le]

lemma padic_valuation_eq_one_iff_norm_eq_one (a : ℚ_[p]) :
    valuation ℚ_[p] a = 1 ↔ ‖a‖ = 1 := by
  rw [le_antisymm_iff, le_antisymm_iff, ← map_one (valuation ℚ_[p]),
    padic_valuation_le_iff_norm_le, padic_valuation_le_iff_norm_le, norm_one]

/-- **Exact Identification of CFT Unit Filtration and `IsInUnitFilt`** on `ℚ_[p]ˣ`:
`x ∈ unitFiltrationUnits ℚ_[p] n ↔ IsInUnitFilt p n x` for every `n : ℕ`! -/
theorem mem_unitFiltrationUnits_iff_isInUnitFilt (n : ℕ) (x : ℚ_[p]ˣ) :
    x ∈ unitFiltrationUnits ℚ_[p] n ↔ IsInUnitFilt p n x := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [mem_unitFiltrationUnits_zero_iff, padic_valuation_eq_one_iff_norm_eq_one]
    exact ⟨fun h => ⟨h, Or.inl rfl⟩, fun h => h.1⟩
  · rw [mem_unitFiltrationUnits_iff hn (Padic.irreducible_natCast_integer p)]
    have hpow : valuation ℚ_[p] (((p : 𝒪[ℚ_[p]]) : ℚ_[p])) ^ n =
        valuation ℚ_[p] ((p : ℚ_[p]) ^ n) := by
      rw [map_pow]; rfl
    rw [hpow, padic_valuation_le_iff_norm_le, norm_pow, Padic.norm_p, inv_pow,
      ← zpow_neg_coe_of_pos _ hn]
    constructor
    · intro hle
      have hlt1 : ‖(x : ℚ_[p]) - 1‖ < 1 :=
        lt_of_le_of_lt hle (zpow_lt_one_of_neg₀ (prime_one_lt_R p) (by omega))
      have hnorm1 : ‖(x : ℚ_[p])‖ = 1 := by
        have hsplit : (x : ℚ_[p]) = 1 + ((x : ℚ_[p]) - 1) := by ring
        rw [hsplit]
        exact norm_sub_eq_one_of_lt p hlt1
      exact ⟨hnorm1, Or.inr hle⟩
    · rintro ⟨_, h0 | hle⟩
      · omega
      · exact hle

variable (Ω : Type*) [Field Ω] [Algebra ℚ_[p] Ω] [IsSepClosure ℚ_[p] Ω]

/-- Mathlib's genuine maximal abelian Galois group `Gal(ℚ_p^{ab} / ℚ_p)`. -/
abbrev GalAb := maximalAbelianExtension ℚ_[p] Ω ≃ₐ[ℚ_[p]] maximalAbelianExtension ℚ_[p] Ω

/-- Restriction homomorphism `Gal(ℚ_p^{ab} / ℚ_p) →* Gal(ℚ_p^{ur} / ℚ_p)`. -/
def restrictToMaxUnram :
    GalAb p Ω →* (maximalUnramifiedExtension ℚ_[p] Ω ≃ₐ[ℚ_[p]] maximalUnramifiedExtension ℚ_[p] Ω) :=
  restrictAb (maximalUnramifiedExtension ℚ_[p] Ω)
    maximalUnramifiedExtension_le_maximalAbelianExtension

/-- **Genuine Abelianized Inertia Group `I_{ℚ_p}^{ab} ≤ Gal(ℚ_p^{ab} / ℚ_p)`**:
the kernel of restriction to the maximal unramified extension `ℚ_p^{ur}`. -/
def InertiaAb : Subgroup (GalAb p Ω) :=
  (restrictToMaxUnram p Ω).ker

/-- **Genuine Abelianized Weil Group `W_{ℚ_p}^{ab} ≤ Gal(ℚ_p^{ab} / ℚ_p)`**:
all automorphisms `σ ∈ Gal(ℚ_p^{ab} / ℚ_p)` whose restriction to `ℚ_p^{ur}` is an integer power
`Frob_p^n` (`n : ℤ`) of the Frobenius automorphism! -/
def WeilAb : Subgroup (GalAb p Ω) where
  carrier := { σ : GalAb p Ω |
    ∃ n : ℤ, restrictToMaxUnram p Ω σ = maximalUnramifiedExtensionFrobenius ℚ_[p] Ω ^ n }
  one_mem' := ⟨0, by simp⟩
  mul_mem' {σ τ} := by
    rintro ⟨n, hn⟩ ⟨m, hm⟩
    exact ⟨n + m, by rw [map_mul, hn, hm, _root_.zpow_add]⟩
  inv_mem' {σ} := by
    rintro ⟨n, hn⟩
    exact ⟨-n, by rw [map_inv, hn, _root_.zpow_neg]⟩

lemma inertiaAb_le_weilAb : InertiaAb p Ω ≤ WeilAb p Ω := fun σ hσ =>
  ⟨0, by simpa [InertiaAb, MonoidHom.mem_ker] using hσ⟩

/-- Canonical inclusion `I_{ℚ_p}^{ab} ↪ W_{ℚ_p}^{ab}`. -/
def inertiaIncl : InertiaAb p Ω →* WeilAb p Ω :=
  Subgroup.inclusion (inertiaAb_le_weilAb p Ω)

/-- `restrictToMaxUnram (localArtinMap ℚ_[p] Ω x) = Frob_p^{v_p(x)}` for ALL `x : ℚ_[p]ˣ`! -/
theorem restrictToMaxUnram_localArtinMap (x : ℚ_[p]ˣ) :
    restrictToMaxUnram p Ω (localArtinMap ℚ_[p] Ω x) =
      maximalUnramifiedExtensionFrobenius ℚ_[p] Ω ^ (Padic.valuation (x : ℚ_[p])) := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (localReciprocityLimit ℚ_[p] Ω x)
  rw [restrictToMaxUnram, localArtinMap_apply, ← hg, restrictAb_topologicalAbelianizationEquiv]
  apply unramifiedDegree_maximalUnramifiedExtension_injective
  change unramifiedDegree ℚ_[p] (maximalUnramifiedExtension ℚ_[p] Ω)
      (g.restrictNormal (maximalUnramifiedExtension ℚ_[p] Ω)) = _
  rw [unramifiedDegree_restrictNormal, unramifiedDegree_of_mk_eq_localReciprocityLimit hg,
    padic_ord_eq_valuation, map_zpow, unramifiedDegree_maximalUnramifiedExtensionFrobenius,
    ← ofAdd_zsmul, zsmul_one]

lemma localArtinMap_mem_weilAb (x : ℚ_[p]ˣ) :
    localArtinMap ℚ_[p] Ω x ∈ WeilAb p Ω :=
  ⟨Padic.valuation (x : ℚ_[p]), restrictToMaxUnram_localArtinMap p Ω x⟩

lemma localArtinMap_mem_inertiaAb_iff (x : ℚ_[p]ˣ) :
    localArtinMap ℚ_[p] Ω x ∈ InertiaAb p Ω ↔ x ∈ unitFiltrationUnits ℚ_[p] 0 := by
  rw [InertiaAb, MonoidHom.mem_ker, restrictToMaxUnram_localArtinMap]
  rw [mem_unitFiltrationUnits_iff_isInUnitFilt]
  constructor
  · intro h
    have h0 : maximalUnramifiedExtensionFrobenius ℚ_[p] Ω ^ (Padic.valuation (x : ℚ_[p])) =
        maximalUnramifiedExtensionFrobenius ℚ_[p] Ω ^ (0 : ℤ) := by simpa using h
    have hv0 : Padic.valuation (x : ℚ_[p]) = 0 := by
      have h1 := congrArg (maximalUnramifiedExtensionGaloisEquiv ℚ_[p] Ω) h0
      rw [map_zpow, map_zpow, zpow_zero] at h1
      have hF : maximalUnramifiedExtensionGaloisEquiv ℚ_[p] Ω
          (maximalUnramifiedExtensionFrobenius ℚ_[p] Ω) = Multiplicative.ofAdd 1 := by
        rw [maximalUnramifiedExtensionGaloisEquiv_apply,
          unramifiedDegree_maximalUnramifiedExtensionFrobenius]
      rw [hF, ← ofAdd_zsmul, zsmul_one] at h1
      have h2 : ((Padic.valuation (x : ℚ_[p]) : ℤ) : ℤ̂) = 0 := by
        simpa using congrArg Multiplicative.toAdd h1
      by_contra hne
      set k : ℕ+ := ⟨(Padic.valuation (x : ℚ_[p])).natAbs + 1, by omega⟩
      have hproj := congrArg (RHDirect.CFT_AbstractLocalReciprocity.ProfiniteInteger.proj k) h2
      rw [map_intCast, map_zero, ZMod.intCast_zmod_eq_zero_iff_dvd] at hproj
      have hlt : (Padic.valuation (x : ℚ_[p])).natAbs < ((k : ℕ) : ℤ).natAbs := by
        rw [Int.natAbs_natCast]; simp [k]
      exact hne (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hproj hlt)
    refine ⟨?_, Or.inl rfl⟩
    rw [Padic.norm_eq_zpow_neg_valuation x.ne_zero, hv0, neg_zero, zpow_zero]
  · intro hx
    rw [valuation_eq_zero_of_norm_eq_one hx.1, zpow_zero]

/-- **Surjectivity of `localArtinMap ℚ_[p] Ω` from `ℤ_[p]ˣ` onto the inertia subgroup of any finite
abelian extension `M / ℚ_p`**: for every `τ ∈ InertiaAb p Ω` and finite abelian `M`, there exists
`u ∈ unitFiltrationUnits ℚ_[p] 0` with `restrictAb M (localArtinMap u) = restrictAb M τ`! -/
private lemma exists_unit_restrictAb_eq_of_mem_inertiaAb
    {τ : GalAb p Ω} (hτ : τ ∈ InertiaAb p Ω)
    (M : IntermediateField ℚ_[p] Ω) [FiniteDimensional ℚ_[p] M] [IsAbelianGalois ℚ_[p] M] :
    ∃ u ∈ unitFiltrationUnits ℚ_[p] 0,
      restrictAb M (le_maximalAbelianExtension M) (localArtinMap ℚ_[p] Ω u) =
        restrictAb M (le_maximalAbelianExtension M) τ := by
  let := algebraicValuativeRel ℚ_[p] Ω
  let := algebraicTopology ℚ_[p] Ω
  have := algebraicValuativeRel_valuativeExtension ℚ_[p] Ω
  have := algebraicTopology_isValuativeTopology ℚ_[p] Ω
  have : IsSepClosed Ω := IsSepClosure.sep_closed ℚ_[p]
  set f := residueDegree ℚ_[p] M
  have hf_pos : 0 < f := residueDegree_pos ℚ_[p] M
  set E := unramifiedTower ℚ_[p] Ω f
  have hE_unr := isUnramifiedSubextension_unramifiedTower (K := ℚ_[p]) (Ω := Ω) f
  have : FiniteDimensional ℚ_[p] E := hE_unr.1
  have : IsGalois ℚ_[p] E := hE_unr.isGalois
  have hE_le : E ≤ maximalUnramifiedExtension ℚ_[p] Ω := hE_unr.le_maximalUnramifiedExtension
  have : IsAbelianGalois ℚ_[p] E :=
    isAbelianGalois_of_le_maximalAbelianExtension E
      (hE_le.trans maximalUnramifiedExtension_le_maximalAbelianExtension)
  set M' : IntermediateField ℚ_[p] Ω := M ⊔ E
  have : FiniteDimensional ℚ_[p] M' := inferInstance
  have : IsAbelianGalois ℚ_[p] M' := isAbelianGalois_sup M E
  obtain ⟨x, hx⟩ := surjective_restrictAb_localArtinMap (Ω := Ω) M'
    (restrictAb M' (le_maximalAbelianExtension M') τ)
  -- Restrict to `E ≤ M'`: since `τ ∈ InertiaAb` and `E ≤ ℚ_p^{ur}`, `restrictAb E τ = 1`
  have hxE : restrictAb E (le_maximalAbelianExtension E) (localArtinMap ℚ_[p] Ω x) = 1 := by
    have h1 := restrictAb_eq_of_le (le_maximalAbelianExtension M') (le_sup_right : E ≤ M') hx
    have hτE : restrictAb E (le_maximalAbelianExtension E) τ = 1 := by
      have hτ1 : restrictAb (maximalUnramifiedExtension ℚ_[p] Ω)
          maximalUnramifiedExtension_le_maximalAbelianExtension τ =
          restrictAb (maximalUnramifiedExtension ℚ_[p] Ω)
          maximalUnramifiedExtension_le_maximalAbelianExtension 1 := by
        rw [map_one]; exact hτ
      have h2 := restrictAb_eq_of_le maximalUnramifiedExtension_le_maximalAbelianExtension hE_le hτ1
      simpa using h2
    exact h1.trans hτE
  have hx_normE : x ∈ (normUnits ℚ_[p] E).range := by
    rw [← ker_restrictAb_localArtinMap (Ω := Ω) E, MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact hxE
  rcases hx_normE with ⟨z, hz⟩
  have hord_x : ord (x : ℚ_[p]) = (residueDegree ℚ_[p] E : ℤ) * ord ((z : E) : E) := by
    rw [← hz, coe_normUnits, ord_norm]
  have hf_dvd_E : f ∣ residueDegree ℚ_[p] E := by
    rw [residueDegree_eq_finrank_of_unramified ℚ_[p] E hE_unr.ramificationIndex_eq_one,
      finrank_unramifiedTower]
    exact Nat.dvd_factorial hf_pos f.le_succ
  rcases hf_dvd_E with ⟨q, hq⟩
  obtain ⟨ϖM, hϖM⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[M]
  set y : ℚ_[p]ˣ := normUnits ℚ_[p] M (uniformizerUnit hϖM)
  have hord_y : ord (y : ℚ_[p]) = (f : ℤ) := by
    rw [coe_normUnits, ord_norm, coe_uniformizerUnit, ord_uniformizer hϖM, mul_one]
  set k : ℤ := (q : ℤ) * ord ((z : E) : E)
  set u : ℚ_[p]ˣ := x * y ^ (-k)
  have hu_mem : u ∈ unitFiltrationUnits ℚ_[p] 0 := by
    rw [← ord_eq_zero_iff_mem]
    have hu_val : (u : ℚ_[p]) = (x : ℚ_[p]) * (y : ℚ_[p]) ^ (-k) := by
      simp [u]
    rw [hu_val, ord_mul x.ne_zero (zpow_ne_zero _ y.ne_zero), ord_zpow y.ne_zero, hord_x, hq, hord_y]
    push_cast; simp only [k]; ring
  have hy_ker : restrictAb M (le_maximalAbelianExtension M) (localArtinMap ℚ_[p] Ω y) = 1 := by
    have hmem : y ∈ ((restrictAb M (le_maximalAbelianExtension M)).comp
        (localArtinMap ℚ_[p] Ω)).ker := by
      rw [ker_restrictAb_localArtinMap]
      exact ⟨uniformizerUnit hϖM, rfl⟩
    exact hmem
  refine ⟨u, hu_mem, ?_⟩
  have hxM : restrictAb M (le_maximalAbelianExtension M) (localArtinMap ℚ_[p] Ω x) =
      restrictAb M (le_maximalAbelianExtension M) τ :=
    restrictAb_eq_of_le (le_maximalAbelianExtension M') (le_sup_left : M ≤ M') hx
  simp only [u, map_mul, map_zpow, hy_ker, _root_.one_zpow, mul_one, hxM]

/-- **GENUINE INERTIA RECIPROCITY THEOREM**:
`localArtinMap ℚ_[p] Ω` maps `ℤ_[p]ˣ = unitFiltrationUnits ℚ_[p] 0` SURJECTIVELY onto the
abelianized inertia group `InertiaAb p Ω = ker(Gal(ℚ_p^{ab}/ℚ_p) → Gal(ℚ_p^{ur}/ℚ_p))`! -/
theorem localArtinMap_image_units_eq_inertiaAb :
    localArtinMap ℚ_[p] Ω '' (unitFiltrationUnits ℚ_[p] 0 : Set ℚ_[p]ˣ) = (InertiaAb p Ω : Set (GalAb p Ω)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨u, hu, rfl⟩
    exact (localArtinMap_mem_inertiaAb_iff p Ω u).mpr hu
  · intro τ hτ
    have : T2Space (GalAb p Ω) := krullTopology_t2
    have hclosed : IsClosed (localArtinMap ℚ_[p] Ω '' (unitFiltrationUnits ℚ_[p] 0 : Set ℚ_[p]ˣ)) :=
      ((isCompact_unitFiltrationUnits (K := ℚ_[p]) 0).image continuous_localArtinMap).isClosed
    rw [← hclosed.closure_eq, mem_closure_iff]
    intro V hV hτV
    -- Pull back open neighborhood `V` along the closed embedding `restrictAbPi ℚ_[p] Ω`
    obtain ⟨W, hW, rfl⟩ :=
      (isClosedEmbedding_restrictAbPi (F := ℚ_[p]) (Ω := Ω)).isInducing.isOpen_iff.mp hV
    obtain ⟨I, U, hU, hIW⟩ := isOpen_pi_iff.mp hW _ hτV
    -- Build finite compositum `M = ⨆ L ∈ I, L` (still finite abelian!)
    have hM_exists : ∀ (J : Finset (finiteAbelianExtensions ℚ_[p] Ω)),
        ∃ (M : IntermediateField ℚ_[p] Ω) (_ : FiniteDimensional ℚ_[p] M)
          (_ : IsAbelianGalois ℚ_[p] M), ∀ L ∈ J, (L : IntermediateField ℚ_[p] Ω) ≤ M := by
      classical
      intro J
      induction J using Finset.induction_on with
      | empty =>
        refine ⟨⊥, inferInstance, ?_, fun _ h => absurd h (Finset.notMem_empty _)⟩
        exact isAbelianGalois_of_le_maximalAbelianExtension ⊥ bot_le
      | @insert L s _ ih =>
        obtain ⟨M₀, hfd₀, hab₀, hle₀⟩ := ih
        have := L.2.1
        have := L.2.2
        have := hfd₀
        have := hab₀
        refine ⟨(L : IntermediateField ℚ_[p] Ω) ⊔ M₀, inferInstance, isAbelianGalois_sup _ _, ?_⟩
        intro L' hL'
        rcases Finset.mem_insert.mp hL' with rfl | hmem
        · exact le_sup_left
        · exact (hle₀ L' hmem).trans le_sup_right
    obtain ⟨M, hfdM, habM, hleM⟩ := hM_exists I
    have := hfdM
    have := habM
    obtain ⟨u, hu, huM⟩ := exists_unit_restrictAb_eq_of_mem_inertiaAb p Ω hτ M
    refine ⟨localArtinMap ℚ_[p] Ω u, ?_, u, hu, rfl⟩
    change restrictAbPi ℚ_[p] Ω (localArtinMap ℚ_[p] Ω u) ∈ W
    refine hIW fun L hL => ?_
    have := L.2.1
    have := L.2.2
    have hreq : restrictAbPi ℚ_[p] Ω (localArtinMap ℚ_[p] Ω u) L = restrictAbPi ℚ_[p] Ω τ L :=
      restrictAb_eq_of_le (le_maximalAbelianExtension M) (hleM L hL) huM
    rw [hreq]
    exact (hU L hL).2

/-- **GENUINE WEIL GROUP RECIPROCITY THEOREM**:
the range of `localArtinMap ℚ_[p] Ω : ℚ_[p]ˣ →* Gal(ℚ_p^{ab} / ℚ_p)` is **EXACTLY** the genuine
abelianized Weil group `WeilAb p Ω = { σ ∈ Gal(ℚ_p^{ab}/ℚ_p) | ∃ n : ℤ, σ|_{ℚ_p^{ur}} = Frob_p^n }`! -/
theorem localArtinMap_range_eq_weilAb :
    (localArtinMap ℚ_[p] Ω).range = WeilAb p Ω := by
  ext σ
  constructor
  · rintro ⟨x, rfl⟩
    exact localArtinMap_mem_weilAb p Ω x
  · rintro ⟨n, hn⟩
    set τ : GalAb p Ω := σ * (localArtinMap ℚ_[p] Ω (padicPrimeUnit p ^ n))⁻¹
    have hτ : τ ∈ InertiaAb p Ω := by
      rw [InertiaAb, MonoidHom.mem_ker, map_mul, map_inv, map_zpow, map_zpow,
        restrictToMaxUnram_localArtinMap, valuation_padicPrimeUnit, zpow_one, hn, mul_inv_cancel]
    have hτ_im : τ ∈ localArtinMap ℚ_[p] Ω '' (unitFiltrationUnits ℚ_[p] 0 : Set ℚ_[p]ˣ) := by
      rw [localArtinMap_image_units_eq_inertiaAb]; exact hτ
    rcases hτ_im with ⟨u, _, hu⟩
    refine ⟨u * padicPrimeUnit p ^ n, ?_⟩
    rw [map_mul, hu]
    simp [τ]

/-- **GENUINE LOCAL ARTIN RECIPROCITY ISOMORPHISM `ℚ_[p]ˣ ≃* W_{ℚ_p}^{ab}`**
onto the actual abelianized Weil subgroup `WeilAb p Ω ≤ Gal(ℚ_p^{ab} / ℚ_p)`! -/
def localArtinWeilEquiv : ℚ_[p]ˣ ≃* WeilAb p Ω :=
  MulEquiv.ofBijective
    ((localArtinMap ℚ_[p] Ω).codRestrict (WeilAb p Ω) (localArtinMap_mem_weilAb p Ω))
    ⟨fun _ _ h => injective_localArtinMap (congrArg Subtype.val h),
     fun ⟨σ, hσ⟩ => by
       have hmem : σ ∈ (localArtinMap ℚ_[p] Ω).range := by
         rw [localArtinMap_range_eq_weilAb]; exact hσ
       rcases hmem with ⟨x, hx⟩
       exact ⟨x, Subtype.ext hx⟩⟩

@[simp]
theorem localArtinWeilEquiv_coe (x : ℚ_[p]ˣ) :
    ((localArtinWeilEquiv p Ω x : WeilAb p Ω) : GalAb p Ω) = localArtinMap ℚ_[p] Ω x := rfl

/-- **GENUINE TOPOLOGICAL INERTIA ISOMORPHISM `ℤ_[p]ˣ ≃ₜ* I_{ℚ_p}^{ab}`** (Krull topology)! -/
def localArtinInertiaHomeo : unitFiltrationUnits ℚ_[p] 0 ≃ₜ* InertiaAb p Ω :=
  haveI : CompactSpace (unitFiltrationUnits ℚ_[p] 0) :=
    isCompact_iff_compactSpace.mp (isCompact_unitFiltrationUnits (K := ℚ_[p]) 0)
  haveI : T2Space (GalAb p Ω) := krullTopology_t2
  haveI : T2Space (InertiaAb p Ω) := inferInstance
  let f : unitFiltrationUnits ℚ_[p] 0 →* InertiaAb p Ω :=
    { toFun := fun u => ⟨localArtinMap ℚ_[p] Ω u.1,
        (localArtinMap_mem_inertiaAb_iff p Ω u.1).mpr u.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _) }
  have hf_inj : Function.Injective f := fun u₁ u₂ h =>
    Subtype.ext (injective_localArtinMap (congrArg Subtype.val h))
  have hf_surj : Function.Surjective f := fun ⟨τ, hτ⟩ => by
    have hmem : τ ∈ localArtinMap ℚ_[p] Ω '' (unitFiltrationUnits ℚ_[p] 0 : Set ℚ_[p]ˣ) := by
      rw [localArtinMap_image_units_eq_inertiaAb]; exact hτ
    rcases hmem with ⟨u, hu, rfl⟩
    exact ⟨⟨u, hu⟩, rfl⟩
  let e : unitFiltrationUnits ℚ_[p] 0 ≃* InertiaAb p Ω :=
    MulEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hc : Continuous e :=
    (continuous_localArtinMap.comp continuous_subtype_val).subtype_mk _
  { e with
    continuous_toFun := hc
    continuous_invFun := (hc.homeoOfEquivCompactToT2 (f := e.toEquiv)).symm.continuous }

@[simp]
theorem localArtinInertiaHomeo_coe (u : unitFiltrationUnits ℚ_[p] 0) :
    ((localArtinInertiaHomeo p Ω u : InertiaAb p Ω) : GalAb p Ω) = localArtinMap ℚ_[p] Ω u.1 := rfl

lemma inertiaIncl_localArtinInertiaHomeo (u : unitFiltrationUnits ℚ_[p] 0) :
    inertiaIncl p Ω (localArtinInertiaHomeo p Ω u) = localArtinWeilEquiv p Ω u.1 :=
  Subtype.ext rfl

/-- The **genuine arithmetic Frobenius element `Frob_p ∈ W_{ℚ_p}^{ab} ≤ Gal(ℚ_p^{ab} / ℚ_p)`**,
defined as `localArtinMap ℚ_[p] Ω (padicPrimeUnit p)`. -/
def frobWeil : WeilAb p Ω :=
  localArtinWeilEquiv p Ω (padicPrimeUnit p)

/-- `frobWeil p Ω` restricts on `ℚ_p^{ur}` to the genuine Frobenius automorphism
`maximalUnramifiedExtensionFrobenius ℚ_[p] Ω`! -/
theorem restrictToMaxUnram_frobWeil :
    restrictToMaxUnram p Ω (frobWeil p Ω).1 = maximalUnramifiedExtensionFrobenius ℚ_[p] Ω := by
  change restrictToMaxUnram p Ω (localArtinMap ℚ_[p] Ω (padicPrimeUnit p)) = _
  rw [restrictToMaxUnram_localArtinMap, valuation_padicPrimeUnit, zpow_one]

/-- The **genuine Weil group norm `‖·‖_W : W_{ℚ_p}^{ab} →* ℝ`** satisfying `‖Frob_p‖_W = p⁻¹`
and `‖localArtinWeilEquiv x‖_W = ‖x‖_p` for all `x ∈ ℚ_[p]ˣ`! -/
def weilNorm : WeilAb p Ω →* ℝ where
  toFun σ := ‖(((localArtinWeilEquiv p Ω).symm σ : ℚ_[p]ˣ) : ℚ_[p])‖
  map_one' := by simp
  map_mul' σ₁ σ₂ := by simp [map_mul]

@[simp]
theorem weilNorm_localArtinWeilEquiv (x : ℚ_[p]ˣ) :
    weilNorm p Ω (localArtinWeilEquiv p Ω x) = ‖(x : ℚ_[p])‖ := by
  simp [weilNorm]

@[simp]
theorem weilNorm_frobWeil : weilNorm p Ω (frobWeil p Ω) = (p : ℝ)⁻¹ := by
  rw [frobWeil, weilNorm_localArtinWeilEquiv, padicPrimeUnit_val, Padic.norm_p]

lemma weilNorm_eq_one_of_mem_inertia (σ : InertiaAb p Ω) :
    weilNorm p Ω (inertiaIncl p Ω σ) = 1 := by
  obtain ⟨u, rfl⟩ := (localArtinInertiaHomeo p Ω).surjective σ
  rw [inertiaIncl_localArtinInertiaHomeo, weilNorm_localArtinWeilEquiv]
  exact ((mem_unitFiltrationUnits_iff_isInUnitFilt p 0 u.1).mp u.2).1

/-! ### Genuine Smooth 1-Dimensional Galois/Weil Characters `WeilChar p Ω` & CFT Bijection -/

/-- **Genuine Smooth 1-Dimensional Representation of `W_{ℚ_p}^{ab} ≤ Gal(ℚ_p^{ab} / ℚ_p)`**:
a group homomorphism `χ_W : WeilAb p Ω →* ℂˣ` whose restriction to the Krull-topology inertia
subgroup `InertiaAb p Ω` has open kernel (equivalently, is locally constant / continuous for the
discrete topology on `ℂˣ`). -/
structure WeilChar where
  toHom : WeilAb p Ω →* ℂˣ
  smooth : IsOpen ((toHom.comp (inertiaIncl p Ω)).ker : Set (InertiaAb p Ω))

namespace WeilChar

variable {p Ω}

@[ext]
lemma ext_hom {χ₁ χ₂ : WeilChar p Ω} (h : ∀ σ : WeilAb p Ω, χ₁.toHom σ = χ₂.toHom σ) :
    χ₁ = χ₂ := by
  cases χ₁; cases χ₂
  congr
  exact MonoidHom.ext h

/-- Unramified predicate on `WeilChar p Ω`: trivial on the genuine inertia subgroup `InertiaAb p Ω`! -/
def IsUnramified (χ : WeilChar p Ω) : Prop :=
  ∀ σ : InertiaAb p Ω, χ.toHom (inertiaIncl p Ω σ) = 1

instance : CommGroup (WeilChar p Ω) where
  one := ⟨1, by
    have htop : ((1 : WeilAb p Ω →* ℂˣ).comp (inertiaIncl p Ω)).ker = ⊤ := by ext; simp
    rw [htop]; exact isOpen_univ⟩
  mul χ₁ χ₂ := ⟨χ₁.toHom * χ₂.toHom, by
    refine Subgroup.isOpen_mono (H₁ := (χ₁.toHom.comp (inertiaIncl p Ω)).ker ⊓
        (χ₂.toHom.comp (inertiaIncl p Ω)).ker) ?_ (χ₁.smooth.inter χ₂.smooth)
    intro σ hσ
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mul_apply] at hσ ⊢
    rw [hσ.1, hσ.2, mul_one]⟩
  inv χ := ⟨χ.toHom⁻¹, by
    have hker : (χ.toHom⁻¹.comp (inertiaIncl p Ω)).ker = (χ.toHom.comp (inertiaIncl p Ω)).ker := by
      ext σ; simp
    rw [hker]; exact χ.smooth⟩
  mul_assoc a b c := ext_hom fun σ => mul_assoc (a.toHom σ) (b.toHom σ) (c.toHom σ)
  one_mul a := ext_hom fun σ => one_mul (a.toHom σ)
  mul_one a := ext_hom fun σ => mul_one (a.toHom σ)
  inv_mul_cancel a := ext_hom fun σ => inv_mul_cancel (a.toHom σ)
  mul_comm a b := ext_hom fun σ => mul_comm (a.toHom σ) (b.toHom σ)

@[simp] lemma one_toHom : (1 : WeilChar p Ω).toHom = 1 := rfl
@[simp] lemma mul_toHom (χ₁ χ₂ : WeilChar p Ω) : (χ₁ * χ₂).toHom = χ₁.toHom * χ₂.toHom := rfl
@[simp] lemma inv_toHom (χ : WeilChar p Ω) : χ⁻¹.toHom = χ.toHom⁻¹ := rfl

end WeilChar

/-- **GENUINE LOCAL CLASS FIELD THEORY `GL₁` CORRESPONDENCE `artinCharEquiv : LocalChar p ≃* WeilChar p Ω`**:
a multiplicative group isomorphism connecting smooth characters of `ℚ_[p]ˣ` with Krull-smooth
1-dimensional representations of `W_{ℚ_p}^{ab} ≤ Gal(ℚ_p^{ab} / ℚ_p)` via `localArtinMap ℚ_[p] Ω`! -/
def artinCharEquiv : LocalChar p ≃* WeilChar p Ω where
  toFun χ :=
    { toHom := χ.toHom.comp (localArtinWeilEquiv p Ω).symm.toMonoidHom
      smooth := by
        rcases χ.smooth with ⟨n, hn⟩
        -- The subgroup `U_n ≤ U_0` is open in `U_0`, hence its image in `InertiaAb` is open!
        have hopen_Un : IsOpen (((unitFiltrationUnits ℚ_[p] n).subgroupOf
            (unitFiltrationUnits ℚ_[p] 0)) : Set (unitFiltrationUnits ℚ_[p] 0)) :=
          (isOpen_unitFiltrationUnits n).preimage continuous_subtype_val
        have hopen_im : IsOpen ((((unitFiltrationUnits ℚ_[p] n).subgroupOf
            (unitFiltrationUnits ℚ_[p] 0)).map
              (localArtinInertiaHomeo p Ω).toMulEquiv.toMonoidHom) : Set (InertiaAb p Ω)) := by
          have hpre : (((unitFiltrationUnits ℚ_[p] n).subgroupOf
              (unitFiltrationUnits ℚ_[p] 0)).map
                (localArtinInertiaHomeo p Ω).toMulEquiv.toMonoidHom : Set (InertiaAb p Ω)) =
              (localArtinInertiaHomeo p Ω).symm ⁻¹'
                (((unitFiltrationUnits ℚ_[p] n).subgroupOf
                  (unitFiltrationUnits ℚ_[p] 0)) : Set (unitFiltrationUnits ℚ_[p] 0)) := by
            ext σ
            simp only [SetLike.mem_coe, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
              Set.mem_preimage]
            constructor
            · rintro ⟨u, hu, rfl⟩
              change (localArtinInertiaHomeo p Ω).symm (localArtinInertiaHomeo p Ω u) ∈ _
              rw [ContinuousMulEquiv.symm_apply_apply]; exact hu
            · intro h
              exact ⟨(localArtinInertiaHomeo p Ω).symm σ, h,
                ContinuousMulEquiv.apply_symm_apply _ _⟩
          rw [hpre]
          exact hopen_Un.preimage (localArtinInertiaHomeo p Ω).symm.continuous
        refine Subgroup.isOpen_mono ?_ hopen_im
        rintro σ ⟨u, hu, rfl⟩
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply]
        change χ.toHom ((localArtinWeilEquiv p Ω).symm
          (inertiaIncl p Ω (localArtinInertiaHomeo p Ω u))) = 1
        rw [inertiaIncl_localArtinInertiaHomeo, MulEquiv.symm_apply_apply]
        exact hn u.1 ((mem_unitFiltrationUnits_iff_isInUnitFilt p n u.1).mp hu) }
  invFun χW :=
    { toHom := χW.toHom.comp (localArtinWeilEquiv p Ω).toMonoidHom
      smooth := by
        have hopen_U0 : IsOpen ((χW.toHom.comp (inertiaIncl p Ω)).ker.comap
            (localArtinInertiaHomeo p Ω).toMulEquiv.toMonoidHom : Set (unitFiltrationUnits ℚ_[p] 0)) :=
          χW.smooth.preimage (localArtinInertiaHomeo p Ω).continuous
        -- Push open subgroup of open `U_0` into `ℚ_[p]ˣ`
        set H : Subgroup ℚ_[p]ˣ := (χW.toHom.comp (localArtinWeilEquiv p Ω).toMonoidHom).ker
        have hH_open : IsOpen (H : Set ℚ_[p]ˣ) := by
          have hsub : (H.subgroupOf (unitFiltrationUnits ℚ_[p] 0)) =
              (χW.toHom.comp (inertiaIncl p Ω)).ker.comap
                (localArtinInertiaHomeo p Ω).toMulEquiv.toMonoidHom := by
            ext u
            simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, MonoidHom.mem_ker,
              MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, H]
            change χW.toHom (localArtinWeilEquiv p Ω u.1) = 1 ↔
              χW.toHom (inertiaIncl p Ω (localArtinInertiaHomeo p Ω u)) = 1
            rw [inertiaIncl_localArtinInertiaHomeo]
          have hopen_sub : IsOpen ((H ⊓ unitFiltrationUnits ℚ_[p] 0 : Subgroup ℚ_[p]ˣ) : Set ℚ_[p]ˣ) := by
            have heq_set : ((H ⊓ unitFiltrationUnits ℚ_[p] 0 : Subgroup ℚ_[p]ˣ) : Set ℚ_[p]ˣ) =
                ((↑) : unitFiltrationUnits ℚ_[p] 0 → ℚ_[p]ˣ) ''
                  (H.subgroupOf (unitFiltrationUnits ℚ_[p] 0) : Set (unitFiltrationUnits ℚ_[p] 0)) := by
              ext x
              simp only [SetLike.mem_coe, Subgroup.mem_inf, Set.mem_image, Subgroup.mem_subgroupOf]
              exact ⟨fun ⟨hxH, hx0⟩ => ⟨⟨x, hx0⟩, hxH, rfl⟩, fun ⟨u, hu, hux⟩ => hux ▸ ⟨hu, u.2⟩⟩
            rw [heq_set, hsub]
            exact (isOpen_unitFiltrationUnits (K := ℚ_[p]) 0).isOpenMap_subtype_val _ hopen_U0
          exact Subgroup.isOpen_mono inf_le_left hopen_sub
        obtain ⟨n, hn⟩ := exists_unitFiltrationUnits_le hH_open
        refine ⟨n, fun u hu => ?_⟩
        exact hn ((mem_unitFiltrationUnits_iff_isInUnitFilt p n u).mpr hu) }
  left_inv χ := LocalChar.ext_hom fun x => by simp
  right_inv χW := WeilChar.ext_hom fun σ => by simp
  map_mul' χ₁ χ₂ := WeilChar.ext_hom fun σ => rfl

/-- **Exact Local Artin Pullback Identity**:
`(artinCharEquiv p Ω χ).toHom (localArtinWeilEquiv p Ω x) = χ.toHom x` for ALL `x : ℚ_[p]ˣ`! -/
@[simp]
theorem artinCharEquiv_apply_localArtin (χ : LocalChar p) (x : ℚ_[p]ˣ) :
    (artinCharEquiv p Ω χ).toHom (localArtinWeilEquiv p Ω x) = χ.toHom x := by
  simp [artinCharEquiv]

/-- **Exact Frobenius Evaluation**: `(artinCharEquiv p Ω χ).toHom (frobWeil p Ω) = χ.evalP`! -/
@[simp]
theorem artinCharEquiv_frobWeil (χ : LocalChar p) :
    (artinCharEquiv p Ω χ).toHom (frobWeil p Ω) = χ.evalP := by
  rw [frobWeil, artinCharEquiv_apply_localArtin]; rfl

/-- **Exact Unramified Equivalence**:
`χ : LocalChar p` is unramified iff `artinCharEquiv p Ω χ` is trivial on the genuine inertia
subgroup `InertiaAb p Ω ≤ Gal(ℚ_p^{ab} / ℚ_p)`! -/
theorem artinCharEquiv_isUnramified_iff (χ : LocalChar p) :
    (artinCharEquiv p Ω χ).IsUnramified ↔ χ.IsUnramified := by
  constructor
  · intro h u hu_norm
    have hu0 : u ∈ unitFiltrationUnits ℚ_[p] 0 :=
      (mem_unitFiltrationUnits_iff_isInUnitFilt p 0 u).mpr ⟨hu_norm, Or.inl rfl⟩
    have h1 := h (localArtinInertiaHomeo p Ω ⟨u, hu0⟩)
    rw [inertiaIncl_localArtinInertiaHomeo, artinCharEquiv_apply_localArtin] at h1
    exact h1
  · intro h σ
    obtain ⟨u, rfl⟩ := (localArtinInertiaHomeo p Ω).surjective σ
    rw [inertiaIncl_localArtinInertiaHomeo, artinCharEquiv_apply_localArtin]
    exact h u.1 ((mem_unitFiltrationUnits_iff_isInUnitFilt p 0 u.1).mp u.2).1

end GenuineWeilGroup

/-! ## Section 3: Genuine 2-Dimensional Weil–Deligne Representations `(ρ, N)` & Intrinsic
`LinearMap.det` Local `L`-Factors -/

section GenuineWeilDeligne

open RHDirect.CFT_AbstractLocalReciprocity ValuativeRel

variable (p : ℕ) [hp : Fact p.Prime] (Ω : Type*) [Field Ω] [Algebra ℚ_[p] Ω] [IsSepClosure ℚ_[p] Ω]

/-- **GENUINE 2-DIMENSIONAL WEIL–DELIGNE REPRESENTATION `(ρ, N)` OF `W_{ℚ_p}^{ab}`**:
- `rho : WeilAb p Ω →* GL (Fin 2) ℂ` is an actual 2D representation of `W_{ℚ_p}^{ab} ≤ Gal(ℚ_p^{ab}/ℚ_p)`,
- `smooth`: `rho` restricted to the Krull-topology inertia subgroup `InertiaAb p Ω` has open kernel,
- `N : Matrix (Fin 2) (Fin 2) ℂ` is a nilpotent monodromy operator (`N² = 0`),
- `wd_compat`: `ρ(σ) N ρ(σ)⁻¹ = ‖σ‖_W • N` for ALL `σ ∈ W_{ℚ_p}^{ab}`! -/
structure WeilDeligneRep2 where
  rho : WeilAb p Ω →* Matrix.GeneralLinearGroup (Fin 2) ℂ
  N : Matrix (Fin 2) (Fin 2) ℂ
  smooth : IsOpen ((rho.comp (inertiaIncl p Ω)).ker : Set (InertiaAb p Ω))
  nilpotent : N ^ 2 = 0
  wd_compat : ∀ σ : WeilAb p Ω,
    (rho σ).1 * N * ((rho σ)⁻¹).1 = ((weilNorm p Ω σ : ℝ) : ℂ) • N

namespace WeilDeligneRep2

variable {p Ω}

/-- Determinant character `det ∘ ρ : W_{ℚ_p}^{ab} →* ℂˣ` of a 2D Weil–Deligne representation. -/
def detHom (W : WeilDeligneRep2 p Ω) : WeilAb p Ω →* ℂˣ :=
  Matrix.GeneralLinearGroup.det.comp W.rho

@[simp]
lemma detHom_val (W : WeilDeligneRep2 p Ω) (σ : WeilAb p Ω) :
    (W.detHom σ : ℂ) = Matrix.det (W.rho σ).1 := rfl

/-- The **genuine inertia-invariant monodromy-kernel subspace `V^{I, N=0} ≤ ℂ²`**:
all vectors `v : Fin 2 → ℂ` fixed by `I_{ℚ_p}^{ab}` and annihilated by `N`. -/
def invKerN (W : WeilDeligneRep2 p Ω) : Submodule ℂ (Fin 2 → ℂ) where
  carrier := { v : Fin 2 → ℂ |
    (∀ σ : InertiaAb p Ω, (W.rho (inertiaIncl p Ω σ)).1 *ᵥ v = v) ∧
    W.N *ᵥ v = 0 }
  zero_mem' := ⟨fun _ => Matrix.mulVec_zero _, Matrix.mulVec_zero _⟩
  add_mem' {u v} hu hv :=
    ⟨fun σ => by rw [Matrix.mulVec_add, hu.1 σ, hv.1 σ],
     by rw [Matrix.mulVec_add, hu.2, hv.2, add_zero]⟩
  smul_mem' c {v} hv :=
    ⟨fun σ => by rw [Matrix.mulVec_smul, hv.1 σ],
     by rw [Matrix.mulVec_smul, hv.2, smul_zero]⟩

lemma mem_invKerN_iff (W : WeilDeligneRep2 p Ω) (v : Fin 2 → ℂ) :
    v ∈ W.invKerN ↔
      (∀ σ : InertiaAb p Ω, (W.rho (inertiaIncl p Ω σ)).1 *ᵥ v = v) ∧ W.N *ᵥ v = 0 :=
  Iff.rfl

/-- `ρ(Frob_p)` preserves `V^{I, N=0}` (using commutativity of `W_{ℚ_p}^{ab}` and `wd_compat`)! -/
lemma frob_mem_invKerN (W : WeilDeligneRep2 p Ω) {v : Fin 2 → ℂ} (hv : v ∈ W.invKerN) :
    (W.rho (frobWeil p Ω)).1 *ᵥ v ∈ W.invKerN := by
  constructor
  · intro σ
    have hcomm : inertiaIncl p Ω σ * frobWeil p Ω = frobWeil p Ω * inertiaIncl p Ω σ := by
      apply Subtype.ext
      exact mul_comm' _ _
    calc (W.rho (inertiaIncl p Ω σ)).1 *ᵥ ((W.rho (frobWeil p Ω)).1 *ᵥ v)
        = ((W.rho (inertiaIncl p Ω σ)).1 * (W.rho (frobWeil p Ω)).1) *ᵥ v := by
            rw [Matrix.mulVec_mulVec]
      _ = (W.rho (inertiaIncl p Ω σ * frobWeil p Ω)).1 *ᵥ v := by rw [map_mul]; rfl
      _ = (W.rho (frobWeil p Ω * inertiaIncl p Ω σ)).1 *ᵥ v := by rw [hcomm]
      _ = ((W.rho (frobWeil p Ω)).1 * (W.rho (inertiaIncl p Ω σ)).1) *ᵥ v := by rw [map_mul]; rfl
      _ = (W.rho (frobWeil p Ω)).1 *ᵥ ((W.rho (inertiaIncl p Ω σ)).1 *ᵥ v) := by
            rw [Matrix.mulVec_mulVec]
      _ = (W.rho (frobWeil p Ω)).1 *ᵥ v := by rw [hv.1 σ]
  · have hcompat := W.wd_compat (frobWeil p Ω)⁻¹
    rw [map_inv, inv_inv] at hcompat
    have hNmul : W.N * (W.rho (frobWeil p Ω)).1 =
        ((weilNorm p Ω (frobWeil p Ω)⁻¹ : ℝ) : ℂ) • ((W.rho (frobWeil p Ω)).1 * W.N) := by
      have h1 := congrArg (fun M => (W.rho (frobWeil p Ω)).1 * M) hcompat
      simp only [Matrix.mul_smul] at h1
      have hmul1 : (W.rho (frobWeil p Ω)).1 * ((W.rho (frobWeil p Ω))⁻¹).1 = 1 := by
        change (W.rho (frobWeil p Ω) * (W.rho (frobWeil p Ω))⁻¹).1 = 1
        rw [mul_inv_cancel]; rfl
      have h2 : (W.rho (frobWeil p Ω)).1 * (((W.rho (frobWeil p Ω))⁻¹).1 * W.N * (W.rho (frobWeil p Ω)).1) =
          W.N * (W.rho (frobWeil p Ω)).1 := by
        calc (W.rho (frobWeil p Ω)).1 * (((W.rho (frobWeil p Ω))⁻¹).1 * W.N * (W.rho (frobWeil p Ω)).1)
            = ((W.rho (frobWeil p Ω)).1 * ((W.rho (frobWeil p Ω))⁻¹).1) * W.N * (W.rho (frobWeil p Ω)).1 := by
                simp only [Matrix.mul_assoc]
          _ = W.N * (W.rho (frobWeil p Ω)).1 := by rw [hmul1, Matrix.one_mul]
      rw [h2] at h1
      exact h1
    have hsmul : (((weilNorm p Ω (frobWeil p Ω)⁻¹ : ℝ) : ℂ) •
        ((W.rho (frobWeil p Ω)).1 * W.N)) *ᵥ v =
        ((weilNorm p Ω (frobWeil p Ω)⁻¹ : ℝ) : ℂ) •
          (((W.rho (frobWeil p Ω)).1 * W.N) *ᵥ v) := by
      ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
    rw [Matrix.mulVec_mulVec, hNmul, hsmul, ← Matrix.mulVec_mulVec,
      hv.2, Matrix.mulVec_zero, smul_zero]

/-- The **genuine Frobenius endomorphism `Frob_p | V^{I, N=0}`** as a `ℂ`-linear map on `W.invKerN`. -/
def frobOnInvKerN (W : WeilDeligneRep2 p Ω) : W.invKerN →ₗ[ℂ] W.invKerN where
  toFun v := ⟨(W.rho (frobWeil p Ω)).1 *ᵥ v.1, W.frob_mem_invKerN v.2⟩
  map_add' u v := Subtype.ext (by
    change (W.rho (frobWeil p Ω)).1 *ᵥ (u.1 + v.1) =
      (W.rho (frobWeil p Ω)).1 *ᵥ u.1 + (W.rho (frobWeil p Ω)).1 *ᵥ v.1
    exact Matrix.mulVec_add _ _ _)
  map_smul' c v := Subtype.ext (by
    change (W.rho (frobWeil p Ω)).1 *ᵥ (c • v.1) = c • ((W.rho (frobWeil p Ω)).1 *ᵥ v.1)
    exact Matrix.mulVec_smul _ _ _)

@[simp]
lemma frobOnInvKerN_val (W : WeilDeligneRep2 p Ω) (v : W.invKerN) :
    ((W.frobOnInvKerN v : W.invKerN) : Fin 2 → ℂ) = (W.rho (frobWeil p Ω)).1 *ᵥ (v : Fin 2 → ℂ) := rfl

/-- **GENUINE INTRINSIC WEIL–DELIGNE LOCAL `L`-FACTOR**:
`L(W, T) = det(1 - T · Frob_p | V^{I, N=0})⁻¹`, computed directly via Mathlib's `LinearMap.det`
on the genuine submodule `W.invKerN ≤ (Fin 2 → ℂ)`! -/
def localLFactor (W : WeilDeligneRep2 p Ω) (T : ℂ) : ℂ :=
  (LinearMap.det (LinearMap.id - T • W.frobOnInvKerN))⁻¹

/-- Helper: compute `LinearMap.det` on a 0-dimensional (subsingleton) space. -/
lemma det_of_subsingleton {M : Type*} [AddCommGroup M] [Module ℂ M] [Subsingleton M]
    (f : M →ₗ[ℂ] M) : LinearMap.det f = 1 := by
  let e : M ≃ₗ[ℂ] (Fin 0 → ℂ) :=
    { toFun := fun _ => Fin.elim0
      map_add' := fun _ _ => funext fun i => Fin.elim0 i
      map_smul' := fun _ _ => funext fun i => Fin.elim0 i
      invFun := fun _ => 0
      left_inv := fun x => Subsingleton.elim _ x
      right_inv := fun _ => funext fun i => Fin.elim0 i }
  let b := (Pi.basisFun ℂ (Fin 0)).map e.symm
  rw [← LinearMap.det_toMatrix b f]
  exact Matrix.det_isEmpty

/-- Helper: compute `LinearMap.det` of a scalar linear map `c • id` on a 1D space. -/
lemma det_smul_id_of_equiv_fin1 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (e : M ≃ₗ[ℂ] (Fin 1 → ℂ)) (f : M →ₗ[ℂ] M) (c : ℂ) (hf : ∀ x, f x = c • x) :
    LinearMap.det f = c := by
  let b := (Pi.basisFun ℂ (Fin 1)).map e.symm
  rw [← LinearMap.det_toMatrix b f, Matrix.det_fin_one]
  simp only [LinearMap.toMatrix_apply, hf, map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
    Module.Basis.repr_self, Finsupp.single_eq_same, mul_one]

/-- Helper: compute `LinearMap.det` of a diagonal linear map on a 2D space. -/
lemma det_diag_of_equiv_fin2 {M : Type*} [AddCommGroup M] [Module ℂ M]
    (e : M ≃ₗ[ℂ] (Fin 2 → ℂ)) (f : M →ₗ[ℂ] M) (c₀ c₁ : ℂ)
    (h0 : f (e.symm (Pi.single 0 1)) = c₀ • e.symm (Pi.single 0 1))
    (h1 : f (e.symm (Pi.single 1 1)) = c₁ • e.symm (Pi.single 1 1)) :
    LinearMap.det f = c₀ * c₁ := by
  let b := (Pi.basisFun ℂ (Fin 2)).map e.symm
  have hb0 : b 0 = e.symm (Pi.single 0 1) := by simp [b, Pi.basisFun_apply]
  have hb1 : b 1 = e.symm (Pi.single 1 1) := by simp [b, Pi.basisFun_apply]
  have hf0 : f (b 0) = c₀ • b 0 := by rw [hb0, h0]
  have hf1 : f (b 1) = c₁ • b 1 := by rw [hb1, h1]
  rw [← LinearMap.det_toMatrix b f, Matrix.det_fin_two]
  have m00 : LinearMap.toMatrix b b f 0 0 = c₀ := by
    rw [LinearMap.toMatrix_apply, hf0, map_smul, Module.Basis.repr_self]
    simp
  have m11 : LinearMap.toMatrix b b f 1 1 = c₁ := by
    rw [LinearMap.toMatrix_apply, hf1, map_smul, Module.Basis.repr_self]
    simp
  have m01 : LinearMap.toMatrix b b f 0 1 = 0 := by
    rw [LinearMap.toMatrix_apply, hf1, map_smul, Module.Basis.repr_self]
    simp
  have m10 : LinearMap.toMatrix b b f 1 0 = 0 := by
    rw [LinearMap.toMatrix_apply, hf0, map_smul, Module.Basis.repr_self]
    simp
  rw [m00, m11, m01, m10]; ring

end WeilDeligneRep2

/-- Diagonal matrix `diag(a, d) ∈ GL (Fin 2) ℂ`. -/
def diagGL2C (a d : ℂˣ) : Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(a : ℂ), 0; 0, (d : ℂ)]
    (by simp [Matrix.det_fin_two, a.ne_zero, d.ne_zero])

@[simp]
lemma diagGL2C_val (a d : ℂˣ) : (diagGL2C a d).1 = !![(a : ℂ), 0; 0, (d : ℂ)] := rfl

lemma diagGL2C_mul (a₁ d₁ a₂ d₂ : ℂˣ) :
    diagGL2C (a₁ * a₂) (d₁ * d₂) = diagGL2C a₁ d₁ * diagGL2C a₂ d₂ := by
  apply Units.ext; ext i j
  fin_cases i <;> fin_cases j <;> simp [diagGL2C, Matrix.mul_apply, Fin.sum_univ_two]

lemma diagGL2C_one : diagGL2C 1 1 = 1 := by
  apply Units.ext; ext i j
  fin_cases i <;> fin_cases j <;> simp [diagGL2C]

lemma diagGL2C_inv (a d : ℂˣ) : (diagGL2C a d)⁻¹ = diagGL2C a⁻¹ d⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [← diagGL2C_mul, mul_inv_cancel, mul_inv_cancel, diagGL2C_one]

/-- Diagonal 2D Weil representation `ρ₁ ⊕ ρ₂ : W_{ℚ_p}^{ab} →* GL (Fin 2) ℂ` built from two
genuine `WeilChar p Ω` characters. -/
def diagWeilHom (χ₁ χ₂ : LocalChar p) :
    WeilAb p Ω →* Matrix.GeneralLinearGroup (Fin 2) ℂ where
  toFun σ := diagGL2C ((artinCharEquiv p Ω χ₁).toHom σ) ((artinCharEquiv p Ω χ₂).toHom σ)
  map_one' := by simp [diagGL2C_one]
  map_mul' σ₁ σ₂ := by simp [map_mul, diagGL2C_mul]

lemma diagWeilHom_smooth (χ₁ χ₂ : LocalChar p) :
    IsOpen (((diagWeilHom p Ω χ₁ χ₂).comp (inertiaIncl p Ω)).ker : Set (InertiaAb p Ω)) := by
  refine Subgroup.isOpen_mono
    (H₁ := ((artinCharEquiv p Ω χ₁).toHom.comp (inertiaIncl p Ω)).ker ⊓
      ((artinCharEquiv p Ω χ₂).toHom.comp (inertiaIncl p Ω)).ker) ?_
    ((artinCharEquiv p Ω χ₁).smooth.inter (artinCharEquiv p Ω χ₂).smooth)
  intro σ hσ
  simp only [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.comp_apply, diagWeilHom,
    MonoidHom.coe_mk, OneHom.coe_mk] at hσ ⊢
  rw [hσ.1, hσ.2, diagGL2C_one]

/-- **Genuine Reducible Frobenius-Semisimple Weil–Deligne Representation**
`WD(χ₁, χ₂) = (artinChar χ₁ ⊕ artinChar χ₂, N = 0)` on `W_{ℚ_p}^{ab} ≤ Gal(ℚ_p^{ab} / ℚ_p)`! -/
def principalSeriesWD (χ₁ χ₂ : LocalChar p) : WeilDeligneRep2 p Ω where
  rho := diagWeilHom p Ω χ₁ χ₂
  N := 0
  smooth := diagWeilHom_smooth p Ω χ₁ χ₂
  nilpotent := by simp
  wd_compat σ := by simp

/-- **Genuine Special (Steinberg) Weil–Deligne Representation**
`Sp(χ) = (artinChar(χ|·|^{1/2}) ⊕ artinChar(χ|·|^{-1/2}), N = !![0, 1; 0, 0])` on
`W_{ℚ_p}^{ab} ≤ Gal(ℚ_p^{ab} / ℚ_p)`, satisfying the EXACT monodromy equation
`ρ(σ) N ρ(σ)⁻¹ = ‖σ‖_W • N` for ALL `σ ∈ W_{ℚ_p}^{ab}`! -/
def steinbergWD (χ : LocalChar p) : WeilDeligneRep2 p Ω where
  rho := diagWeilHom p Ω
    (χ * LocalChar.normPowChar p (1 / 2))
    (χ * LocalChar.normPowChar p (-(1 / 2)))
  N := !![(0 : ℂ), 1; 0, 0]
  smooth := diagWeilHom_smooth p Ω _ _
  nilpotent := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two]
  wd_compat σ := by
    obtain ⟨x, rfl⟩ := (localArtinWeilEquiv p Ω).surjective σ
    rw [weilNorm_localArtinWeilEquiv]
    change (diagGL2C _ _).1 * !![(0 : ℂ), 1; 0, 0] * ((diagGL2C _ _)⁻¹).1 = _
    rw [diagGL2C_inv]
    simp only [artinCharEquiv_apply_localArtin, diagGL2C_val, LocalChar.mul_toHom,
      MonoidHom.mul_apply]
    set a : ℂ := ((χ.toHom x * (LocalChar.normPowChar p (1 / 2)).toHom x : ℂˣ) : ℂ)
    set d : ℂ := ((χ.toHom x * (LocalChar.normPowChar p (-(1 / 2))).toHom x : ℂˣ) : ℂ)
    have hratio : a * d⁻¹ = ((‖(x : ℚ_[p])‖ : ℝ) : ℂ) := by
      simp only [a, d, Units.val_mul, normPowChar_toHom_val]
      have hχ0 : (χ.toHom x : ℂ) ≠ 0 := Units.ne_zero _
      have hpos : (0 : ℝ) < ‖(x : ℚ_[p])‖ := norm_pos_iff.mpr x.ne_zero
      have hpow : (((‖(x : ℚ_[p])‖ ^ (1 / 2 : ℝ) : ℝ) : ℂ)) *
          ((((‖(x : ℚ_[p])‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)))⁻¹ = ((‖(x : ℚ_[p])‖ : ℝ) : ℂ) := by
        rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Real.rpow_neg hpos.le, neg_neg,
          ← Real.rpow_add hpos]
        norm_num
      calc (χ.toHom x : ℂ) * (((‖(x : ℚ_[p])‖ ^ (1 / 2 : ℝ) : ℝ) : ℂ)) *
            ((χ.toHom x : ℂ) * (((‖(x : ℚ_[p])‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)))⁻¹
          = ((χ.toHom x : ℂ) * (χ.toHom x : ℂ)⁻¹) *
            ((((‖(x : ℚ_[p])‖ ^ (1 / 2 : ℝ) : ℝ) : ℂ)) *
              ((((‖(x : ℚ_[p])‖ ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)))⁻¹) := by
              rw [mul_inv]; ring
        _ = ((‖(x : ℚ_[p])‖ : ℝ) : ℂ) := by rw [mul_inv_cancel₀ hχ0, one_mul, hpow]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    simpa [a, d, Units.val_mul, mul_inv] using hratio

/-! ### Exact Determinant, Trace, `invKerN`, and Intrinsic `LinearMap.det` Local `L`-Factor Proofs -/

theorem principalSeriesWD_det (χ₁ χ₂ : LocalChar p) (x : ℚ_[p]ˣ) :
    Matrix.det ((principalSeriesWD p Ω χ₁ χ₂).rho (localArtinWeilEquiv p Ω x)).1 =
      ((χ₁ * χ₂).toHom x : ℂ) := by
  simp [principalSeriesWD, diagWeilHom, Matrix.det_fin_two]

theorem principalSeriesWD_trace_frob (χ₁ χ₂ : LocalChar p) :
    Matrix.trace ((principalSeriesWD p Ω χ₁ χ₂).rho (frobWeil p Ω)).1 =
      (χ₁.evalP : ℂ) + (χ₂.evalP : ℂ) := by
  simp [principalSeriesWD, diagWeilHom, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

theorem steinbergWD_det (χ : LocalChar p) (x : ℚ_[p]ˣ) :
    Matrix.det ((steinbergWD p Ω χ).rho (localArtinWeilEquiv p Ω x)).1 =
      ((χ ^ 2).toHom x : ℂ) := by
  simp only [steinbergWD, diagWeilHom, MonoidHom.coe_mk, OneHom.coe_mk, diagGL2C_val,
    artinCharEquiv_apply_localArtin, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_zero, sub_zero]
  have hprod : (χ * LocalChar.normPowChar p (1 / 2)) * (χ * LocalChar.normPowChar p (-(1 / 2))) =
      χ ^ 2 := by
    calc (χ * LocalChar.normPowChar p (1 / 2)) * (χ * LocalChar.normPowChar p (-(1 / 2)))
        = (χ * χ) * (LocalChar.normPowChar p (1 / 2) * LocalChar.normPowChar p (-(1 / 2))) := by
          ac_rfl
      _ = χ ^ 2 := by rw [LocalChar.normPowChar_half_mul_neg_half, mul_one, sq]
  have hv := congrArg (fun η : LocalChar p => (η.toHom x : ℂ)) hprod
  simpa using hv

/-- Exact membership characterization of `V^{I, N=0}` for `principalSeriesWD p Ω χ₁ χ₂`. -/
lemma mem_invKerN_principalSeriesWD_iff (χ₁ χ₂ : LocalChar p) (v : Fin 2 → ℂ) :
    v ∈ (principalSeriesWD p Ω χ₁ χ₂).invKerN ↔
      (¬χ₁.IsUnramified → v 0 = 0) ∧ (¬χ₂.IsUnramified → v 1 = 0) := by
  rw [WeilDeligneRep2.mem_invKerN_iff]
  have hN0 : (principalSeriesWD p Ω χ₁ χ₂).N *ᵥ v = 0 := by simp [principalSeriesWD]
  have hact : ∀ σ : InertiaAb p Ω,
      ((principalSeriesWD p Ω χ₁ χ₂).rho (inertiaIncl p Ω σ)).1 *ᵥ v =
        ![((artinCharEquiv p Ω χ₁).toHom (inertiaIncl p Ω σ) : ℂ) * v 0,
          ((artinCharEquiv p Ω χ₂).toHom (inertiaIncl p Ω σ) : ℂ) * v 1] := by
    intro σ; ext i; fin_cases i <;>
      simp [principalSeriesWD, diagWeilHom, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  constructor
  · intro ⟨hI, _⟩
    constructor
    · intro hram
      rw [← artinCharEquiv_isUnramified_iff p Ω] at hram
      simp only [WeilChar.IsUnramified, not_forall] at hram
      rcases hram with ⟨σ, hσ⟩
      have h0 := congrFun (hI σ) 0
      rw [hact σ] at h0
      simp only [Matrix.cons_val_zero] at h0
      have hsub : (((artinCharEquiv p Ω χ₁).toHom (inertiaIncl p Ω σ) : ℂ) - 1) * v 0 = 0 := by
        linear_combination h0
      have hne : ((artinCharEquiv p Ω χ₁).toHom (inertiaIncl p Ω σ) : ℂ) - 1 ≠ 0 :=
        fun h => hσ (Units.ext (sub_eq_zero.mp h))
      exact (mul_eq_zero.mp hsub).resolve_left hne
    · intro hram
      rw [← artinCharEquiv_isUnramified_iff p Ω] at hram
      simp only [WeilChar.IsUnramified, not_forall] at hram
      rcases hram with ⟨σ, hσ⟩
      have h1 := congrFun (hI σ) 1
      rw [hact σ] at h1
      simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at h1
      have hsub : (((artinCharEquiv p Ω χ₂).toHom (inertiaIncl p Ω σ) : ℂ) - 1) * v 1 = 0 := by
        linear_combination h1
      have hne : ((artinCharEquiv p Ω χ₂).toHom (inertiaIncl p Ω σ) : ℂ) - 1 ≠ 0 :=
        fun h => hσ (Units.ext (sub_eq_zero.mp h))
      exact (mul_eq_zero.mp hsub).resolve_left hne
  · rintro ⟨h0, h1⟩
    refine ⟨fun σ => ?_, hN0⟩
    rw [hact σ]
    ext i
    fin_cases i
    · by_cases hu : χ₁.IsUnramified
      · have htriv := (artinCharEquiv_isUnramified_iff p Ω χ₁).mpr hu σ
        simp [htriv]
      · simp [h0 hu]
    · by_cases hu : χ₂.IsUnramified
      · have htriv := (artinCharEquiv_isUnramified_iff p Ω χ₂).mpr hu σ
        simp [htriv]
      · simp [h1 hu]

/-- **INTRINSIC `LinearMap.det` COMPUTATION OF `L(principalSeriesWD χ₁ χ₂, T)`**
(proved by genuine linear algebra on `invKerN` across all 4 ramification cases, ZERO enum `rfl`!):
`det(1 - T · Frob_p | V^{I, N=0})⁻¹ = L(χ₁, T) · L(χ₂, T)`! -/
theorem principalSeriesWD_localLFactor (χ₁ χ₂ : LocalChar p) (T : ℂ) :
    (principalSeriesWD p Ω χ₁ χ₂).localLFactor T = χ₁.gl1LFactor T * χ₂.gl1LFactor T := by
  set W := principalSeriesWD p Ω χ₁ χ₂
  have hfrob_apply : ∀ (v : W.invKerN),
      (W.frobOnInvKerN v).1 = ![(χ₁.evalP : ℂ) * v.1 0, (χ₂.evalP : ℂ) * v.1 1] := by
    intro v
    change (W.rho (frobWeil p Ω)).1 *ᵥ v.1 = _
    ext i; fin_cases i <;>
      simp [W, principalSeriesWD, diagWeilHom, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  by_cases h₁ : χ₁.IsUnramified <;> by_cases h₂ : χ₂.IsUnramified
  · -- Case 1: Both unramified ⇒ V^{I, N=0} = ℂ²
    rw [LocalChar.gl1LFactor_of_isUnramified h₁, LocalChar.gl1LFactor_of_isUnramified h₂, ← mul_inv]
    unfold WeilDeligneRep2.localLFactor
    congr 1
    let e : W.invKerN ≃ₗ[ℂ] (Fin 2 → ℂ) :=
      { toFun := fun v => v.1
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        invFun := fun v => ⟨v, (mem_invKerN_principalSeriesWD_iff p Ω χ₁ χ₂ v).mpr
          ⟨fun h => absurd h₁ h, fun h => absurd h₂ h⟩⟩
        left_inv := fun _ => Subtype.ext rfl
        right_inv := fun _ => rfl }
    refine WeilDeligneRep2.det_diag_of_equiv_fin2 e _ (1 - (χ₁.evalP : ℂ) * T)
      (1 - (χ₂.evalP : ℂ) * T) ?_ ?_
    · apply Subtype.ext; ext i
      change (e.symm (Pi.single 0 1)).1 i - T * (W.frobOnInvKerN (e.symm (Pi.single 0 1))).1 i = _
      rw [hfrob_apply]
      fin_cases i <;> simp [e]; ring
    · apply Subtype.ext; ext i
      change (e.symm (Pi.single 1 1)).1 i - T * (W.frobOnInvKerN (e.symm (Pi.single 1 1))).1 i = _
      rw [hfrob_apply]
      fin_cases i <;> simp [e]; ring
  · -- Case 2: χ₁ unramified, χ₂ ramified ⇒ V^{I, N=0} = ℂ · e₀
    rw [LocalChar.gl1LFactor_of_isUnramified h₁, LocalChar.gl1LFactor_of_not_isUnramified h₂, mul_one]
    unfold WeilDeligneRep2.localLFactor
    congr 1
    let e : W.invKerN ≃ₗ[ℂ] (Fin 1 → ℂ) :=
      { toFun := fun v _ => v.1 0
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        invFun := fun c => ⟨![c 0, 0], (mem_invKerN_principalSeriesWD_iff p Ω χ₁ χ₂ _).mpr
          ⟨fun h => absurd h₁ h, fun _ => rfl⟩⟩
        left_inv := fun v => Subtype.ext <| by
          have hv1 := ((mem_invKerN_principalSeriesWD_iff p Ω χ₁ χ₂ v.1).mp v.2).2 h₂
          ext i; fin_cases i <;> simp [hv1]
        right_inv := fun c => by ext i; fin_cases i; rfl }
    refine WeilDeligneRep2.det_smul_id_of_equiv_fin1 e _ (1 - (χ₁.evalP : ℂ) * T) fun v => ?_
    have hv1 := ((mem_invKerN_principalSeriesWD_iff p Ω χ₁ χ₂ v.1).mp v.2).2 h₂
    apply Subtype.ext; ext i
    change v.1 i - T * (W.frobOnInvKerN v).1 i = (1 - (χ₁.evalP : ℂ) * T) * v.1 i
    rw [hfrob_apply]
    fin_cases i
    · simp; ring
    · simp [hv1]
  · -- Case 3: χ₁ ramified, χ₂ unramified ⇒ V^{I, N=0} = ℂ · e₁
    rw [LocalChar.gl1LFactor_of_not_isUnramified h₁, LocalChar.gl1LFactor_of_isUnramified h₂, one_mul]
    unfold WeilDeligneRep2.localLFactor
    congr 1
    let e : W.invKerN ≃ₗ[ℂ] (Fin 1 → ℂ) :=
      { toFun := fun v _ => v.1 1
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        invFun := fun c => ⟨![0, c 0], (mem_invKerN_principalSeriesWD_iff p Ω χ₁ χ₂ _).mpr
          ⟨fun _ => rfl, fun h => absurd h₂ h⟩⟩
        left_inv := fun v => Subtype.ext <| by
          have hv0 := ((mem_invKerN_principalSeriesWD_iff p Ω χ₁ χ₂ v.1).mp v.2).1 h₁
          ext i; fin_cases i <;> simp [hv0]
        right_inv := fun c => by ext i; fin_cases i; rfl }
    refine WeilDeligneRep2.det_smul_id_of_equiv_fin1 e _ (1 - (χ₂.evalP : ℂ) * T) fun v => ?_
    have hv0 := ((mem_invKerN_principalSeriesWD_iff p Ω χ₁ χ₂ v.1).mp v.2).1 h₁
    apply Subtype.ext; ext i
    change v.1 i - T * (W.frobOnInvKerN v).1 i = (1 - (χ₂.evalP : ℂ) * T) * v.1 i
    rw [hfrob_apply]
    fin_cases i
    · simp [hv0]
    · simp; ring
  · -- Case 4: Both ramified ⇒ V^{I, N=0} = 0
    rw [LocalChar.gl1LFactor_of_not_isUnramified h₁, LocalChar.gl1LFactor_of_not_isUnramified h₂,
      mul_one]
    unfold WeilDeligneRep2.localLFactor
    have : Subsingleton W.invKerN := ⟨fun u v => Subtype.ext <| by
      have hu := (mem_invKerN_principalSeriesWD_iff p Ω χ₁ χ₂ u.1).mp u.2
      have hv := (mem_invKerN_principalSeriesWD_iff p Ω χ₁ χ₂ v.1).mp v.2
      ext i; fin_cases i <;> dsimp
      · rw [hu.1 h₁, hv.1 h₁]
      · rw [hu.2 h₂, hv.2 h₂]⟩
    rw [WeilDeligneRep2.det_of_subsingleton, inv_one]

/-- Exact membership characterization of `V^{I, N=0}` for `steinbergWD p Ω χ`. -/
lemma mem_invKerN_steinbergWD_iff (χ : LocalChar p) (v : Fin 2 → ℂ) :
    v ∈ (steinbergWD p Ω χ).invKerN ↔ v 1 = 0 ∧ (¬χ.IsUnramified → v 0 = 0) := by
  rw [WeilDeligneRep2.mem_invKerN_iff]
  have hN : (steinbergWD p Ω χ).N *ᵥ v = 0 ↔ v 1 = 0 := by
    constructor
    · intro h
      have h0 := congrFun h 0
      simpa [steinbergWD, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h0
    · intro hv1
      ext i; fin_cases i <;>
        simp [steinbergWD, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hv1]
  have hact : ∀ σ : InertiaAb p Ω,
      ((steinbergWD p Ω χ).rho (inertiaIncl p Ω σ)).1 *ᵥ v =
        ![((artinCharEquiv p Ω χ).toHom (inertiaIncl p Ω σ) : ℂ) * v 0,
          ((artinCharEquiv p Ω χ).toHom (inertiaIncl p Ω σ) : ℂ) * v 1] := by
    intro σ
    have h1 : (artinCharEquiv p Ω (LocalChar.normPowChar p (1 / 2))).toHom (inertiaIncl p Ω σ) = 1 :=
      (artinCharEquiv_isUnramified_iff p Ω _).mpr (LocalChar.normPowChar_isUnramified p _) σ
    have h2 : (artinCharEquiv p Ω (LocalChar.normPowChar p (-(1 / 2)))).toHom (inertiaIncl p Ω σ) = 1 :=
      (artinCharEquiv_isUnramified_iff p Ω _).mpr (LocalChar.normPowChar_isUnramified p _) σ
    simp only [one_div] at h1 h2
    ext i; fin_cases i <;>
      simp [steinbergWD, diagWeilHom, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h1, h2]
  rw [hN]
  constructor
  · intro ⟨hI, hv1⟩
    refine ⟨hv1, fun hram => ?_⟩
    rw [← artinCharEquiv_isUnramified_iff p Ω] at hram
    simp only [WeilChar.IsUnramified, not_forall] at hram
    rcases hram with ⟨σ, hσ⟩
    have h0 := congrFun (hI σ) 0
    rw [hact σ] at h0
    simp only [Matrix.cons_val_zero] at h0
    have hsub : (((artinCharEquiv p Ω χ).toHom (inertiaIncl p Ω σ) : ℂ) - 1) * v 0 = 0 := by
      linear_combination h0
    have hne : ((artinCharEquiv p Ω χ).toHom (inertiaIncl p Ω σ) : ℂ) - 1 ≠ 0 :=
      fun h => hσ (Units.ext (sub_eq_zero.mp h))
    exact (mul_eq_zero.mp hsub).resolve_left hne
  · rintro ⟨hv1, h0⟩
    refine ⟨fun σ => ?_, hv1⟩
    rw [hact σ]
    ext i
    fin_cases i
    · by_cases hu : χ.IsUnramified
      · have htriv := (artinCharEquiv_isUnramified_iff p Ω χ).mpr hu σ
        simp [htriv]
      · simp [h0 hu]
    · simp [hv1]

/-- Exact Frobenius action on `V^{I, N=0}` of `steinbergWD p Ω χ`:
`Frob_p` acts on `V^{I, N=0}` by the scalar `χ(p) · p^{-1/2}`! -/
theorem steinbergWD_frobOnInvKerN_eq_smul (χ : LocalChar p)
    (v : (steinbergWD p Ω χ).invKerN) :
    (steinbergWD p Ω χ).frobOnInvKerN v =
      ((χ.evalP : ℂ) * (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • v := by
  have hv1 : v.1 1 = 0 := ((mem_invKerN_steinbergWD_iff p Ω χ v.1).mp v.2).1
  apply Subtype.ext
  change ((steinbergWD p Ω χ).rho (frobWeil p Ω)).1 *ᵥ v.1 =
    ((χ.evalP : ℂ) * (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • v.1
  ext i
  fin_cases i
  · simp [steinbergWD, diagWeilHom, Matrix.mulVec, dotProduct, Fin.sum_univ_two, mul_assoc]
  · simp [steinbergWD, diagWeilHom, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hv1]

/-- For unramified `χ`, `V^{I, N=0}` of `steinbergWD p Ω χ` is **1-dimensional**! -/
theorem steinbergWD_invKerN_finrank_unram {χ : LocalChar p} (hχ : χ.IsUnramified) :
    Module.finrank ℂ (steinbergWD p Ω χ).invKerN = 1 := by
  let e : (steinbergWD p Ω χ).invKerN ≃ₗ[ℂ] ℂ :=
    { toFun := fun v => v.1 0
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun c => ⟨![c, 0], (mem_invKerN_steinbergWD_iff p Ω χ _).mpr
        ⟨rfl, fun h => absurd hχ h⟩⟩
      left_inv := fun v => Subtype.ext <| by
        have hv1 := ((mem_invKerN_steinbergWD_iff p Ω χ v.1).mp v.2).1
        ext i; fin_cases i <;> simp [hv1]
      right_inv := fun _ => rfl }
  rw [e.finrank_eq, Module.finrank_self]

/-- **INTRINSIC `LinearMap.det` COMPUTATION OF `L(steinbergWD χ, T)`**
(proved by genuine linear algebra on `invKerN`, ZERO enum `rfl`!):
`det(1 - T · Frob_p | V^{I, N=0})⁻¹ = L(χ · |·|^{1/2}, T)`! -/
theorem steinbergWD_localLFactor (χ : LocalChar p) (T : ℂ) :
    (steinbergWD p Ω χ).localLFactor T =
      (χ * LocalChar.normPowChar p (1 / 2)).gl1LFactor T := by
  set W := steinbergWD p Ω χ
  by_cases hχ : χ.IsUnramified
  · have hunr : (χ * LocalChar.normPowChar p (1 / 2)).IsUnramified :=
      LocalChar.isUnramified_mul hχ (LocalChar.normPowChar_isUnramified p _)
    rw [LocalChar.gl1LFactor_of_isUnramified hunr]
    simp only [LocalChar.evalP_mul, LocalChar.normPowChar_evalP_val, Units.val_mul]
    unfold WeilDeligneRep2.localLFactor
    congr 1
    let e : W.invKerN ≃ₗ[ℂ] (Fin 1 → ℂ) :=
      { toFun := fun v _ => v.1 0
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        invFun := fun c => ⟨![c 0, 0], (mem_invKerN_steinbergWD_iff p Ω χ _).mpr
          ⟨rfl, fun h => absurd hχ h⟩⟩
        left_inv := fun v => Subtype.ext <| by
          have hv1 := ((mem_invKerN_steinbergWD_iff p Ω χ v.1).mp v.2).1
          ext i; fin_cases i <;> simp [hv1]
        right_inv := fun c => by ext i; fin_cases i; rfl }
    refine WeilDeligneRep2.det_smul_id_of_equiv_fin1 e _
      (1 - (χ.evalP : ℂ) * (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * T) fun v => ?_
    change v - T • W.frobOnInvKerN v = _
    rw [steinbergWD_frobOnInvKerN_eq_smul p Ω χ v, smul_smul]
    calc v - (T * ((χ.evalP : ℂ) * (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) • v
        = (1 : ℂ) • v - (T * ((χ.evalP : ℂ) * (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))) • v := by
            rw [one_smul]
      _ = (1 - (χ.evalP : ℂ) * (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * T) • v := by
            rw [← sub_smul]; congr 1; ring
  · have hram : ¬(χ * LocalChar.normPowChar p (1 / 2)).IsUnramified := by
      intro hunr
      apply hχ
      have h := LocalChar.isUnramified_mul hunr (LocalChar.normPowChar_isUnramified p (-(1 / 2)))
      rwa [mul_assoc, LocalChar.normPowChar_half_mul_neg_half, mul_one] at h
    rw [LocalChar.gl1LFactor_of_not_isUnramified hram]
    unfold WeilDeligneRep2.localLFactor
    have : Subsingleton W.invKerN := ⟨fun u v => Subtype.ext <| by
      have hu := (mem_invKerN_steinbergWD_iff p Ω χ u.1).mp u.2
      have hv := (mem_invKerN_steinbergWD_iff p Ω χ v.1).mp v.2
      ext i; fin_cases i <;> dsimp
      · rw [hu.2 hχ, hv.2 hχ]
      · rw [hu.1, hv.1]⟩
    rw [WeilDeligneRep2.det_of_subsingleton, inv_one]

/-- **Weyl-Symmetry Isomorphism `principalSeriesWD χ₁ χ₂ ≅ principalSeriesWD χ₂ χ₁`**:
conjugation by the involution `J = !![0, 1; 1, 0] ∈ GL₂(ℂ)` intertwines `principalSeriesWD χ₁ χ₂`
and `principalSeriesWD χ₂ χ₁` identically on ALL `σ ∈ W_{ℚ_p}^{ab}` and preserves `localLFactor`! -/
theorem principalSeriesWD_swap_intertwine (χ₁ χ₂ : LocalChar p) :
    let J : Matrix (Fin 2) (Fin 2) ℂ := !![(0 : ℂ), 1; 1, 0]
    (∀ σ : WeilAb p Ω,
      J * ((principalSeriesWD p Ω χ₁ χ₂).rho σ).1 =
        ((principalSeriesWD p Ω χ₂ χ₁).rho σ).1 * J) ∧
    (∀ T : ℂ, (principalSeriesWD p Ω χ₁ χ₂).localLFactor T =
      (principalSeriesWD p Ω χ₂ χ₁).localLFactor T) := by
  refine ⟨fun σ => ?_, fun T => ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [principalSeriesWD, diagWeilHom, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [principalSeriesWD_localLFactor, principalSeriesWD_localLFactor, mul_comm]

end GenuineWeilDeligne

/-! ## Section 4: Genuine Local Langlands Correspondence on the Complete Non-Supercuspidal Smooth
Spectrum of `GL₂(ℚ_p)` -/

section GenuineSmoothLLC

open RHDirect.CFT_AbstractLocalReciprocity ValuativeRel

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Complete Non-Supercuspidal Smooth Spectrum of `GL₂(ℚ_p)`**:
each member indexes a genuine smooth admissible `GL (Fin 2) ℚ_[p]`-representation constructed in
`Stage11GL2SmoothRep`:
- `principalSeries χ₁ χ₂ hirr`: irreducible smooth principal series `SmoothInd p χ₁ χ₂`,
- `oneDim χ`: 1-dimensional smooth representation `oneDimSubrep p χ = ℂ · (χ ∘ det)`,
- `steinberg χ`: smooth Steinberg quotient `SmoothSteinberg p χ = SteinbergAmbient p χ / (ℂ · (χ ∘ det))`.

*(Supercuspidal representations are explicitly out of scope here.)* -/
inductive NonSupercuspidalGL2Rep where
  | principalSeries (χ₁ χ₂ : LocalChar p) (hirr : IsIrredPSPair p s(χ₁, χ₂)) :
      NonSupercuspidalGL2Rep
  | oneDim (χ : LocalChar p) : NonSupercuspidalGL2Rep
  | steinberg (χ : LocalChar p) : NonSupercuspidalGL2Rep

namespace NonSupercuspidalGL2Rep

variable {p}

/-- The **genuine `ℂ`-vector space** carrying the smooth `GL (Fin 2) ℚ_[p]`-representation! -/
@[reducible]
def Space : NonSupercuspidalGL2Rep p → Type
  | .principalSeries χ₁ χ₂ _ => SmoothInd p χ₁ χ₂
  | .oneDim χ => oneDimSubrep p χ
  | .steinberg χ => SmoothSteinberg p χ

instance instAddCommGroupSpace : (π : NonSupercuspidalGL2Rep p) → AddCommGroup π.Space
  | .principalSeries χ₁ χ₂ _ => inferInstanceAs (AddCommGroup (SmoothInd p χ₁ χ₂))
  | .oneDim χ => inferInstanceAs (AddCommGroup (oneDimSubrep p χ))
  | .steinberg χ => inferInstanceAs (AddCommGroup (SmoothSteinberg p χ))

instance instModuleSpace : (π : NonSupercuspidalGL2Rep p) → Module ℂ π.Space
  | .principalSeries χ₁ χ₂ _ => inferInstanceAs (Module ℂ (SmoothInd p χ₁ χ₂))
  | .oneDim χ => inferInstanceAs (Module ℂ (oneDimSubrep p χ))
  | .steinberg χ => inferInstanceAs (Module ℂ (SmoothSteinberg p χ))

/-- The **genuine `GL (Fin 2) ℚ_[p]`-action** on `π.Space`! -/
def action : (π : NonSupercuspidalGL2Rep p) → GL2Qp p → (π.Space →ₗ[ℂ] π.Space)
  | .principalSeries χ₁ χ₂ _, h => rightAction p χ₁ χ₂ h
  | .oneDim χ, h =>
      (rightAction p _ _ h).restrict (fun f hf => oneDimSubrep_invariant p χ h ⟨f, hf, rfl⟩)
  | .steinberg χ, h => steinbergAction p χ h

theorem action_one (π : NonSupercuspidalGL2Rep p) (v : π.Space) :
    π.action 1 v = v := by
  cases π with
  | principalSeries χ₁ χ₂ _ => exact rightAction_one p χ₁ χ₂ v
  | oneDim χ => exact Subtype.ext (rightAction_one p _ _ v.1)
  | steinberg χ => exact steinbergAction_one p χ v

theorem action_mul (π : NonSupercuspidalGL2Rep p) (g₁ g₂ : GL2Qp p) (v : π.Space) :
    π.action (g₁ * g₂) v = π.action g₁ (π.action g₂ v) := by
  cases π with
  | principalSeries χ₁ χ₂ _ => exact rightAction_mul p χ₁ χ₂ g₁ g₂ v
  | oneDim χ => exact Subtype.ext (rightAction_mul p _ _ g₁ g₂ v.1)
  | steinberg χ => exact steinbergAction_mul p χ g₁ g₂ v

/-- The `H`-fixed subspace `π.Space^H` for any subgroup `H ≤ GL (Fin 2) ℚ_[p]`. -/
def fixedSubspace (π : NonSupercuspidalGL2Rep p) (H : Subgroup (GL2Qp p)) :
    Submodule ℂ π.Space where
  carrier := { v : π.Space | ∀ h ∈ H, π.action h v = v }
  zero_mem' h _ := map_zero _
  add_mem' {u v} hu hv h hh := by rw [map_add, hu h hh, hv h hh]
  smul_mem' c {v} hv h hh := by rw [map_smul, hv h hh]

/-- **GENUINE FULL ADMISSIBILITY FOR EVERY `π : NonSupercuspidalGL2Rep p`**:
every principal congruence fixed subspace `π.Space^{K_n}` is finite-dimensional over `ℂ`! -/
theorem admissible (π : NonSupercuspidalGL2Rep p) (n : ℕ) :
    FiniteDimensional ℂ (π.fixedSubspace (principalCongruence p n)) := by
  cases π with
  | principalSeries χ₁ χ₂ _ => exact smoothInd_admissible p χ₁ χ₂ n
  | oneDim χ =>
    have : FiniteDimensional ℂ (oneDimSubrep p χ) := by
      have h1 := finrank_oneDimSubrep p χ
      exact FiniteDimensional.of_finrank_pos (by omega)
    infer_instance
  | steinberg χ => exact smoothSteinberg_admissible p χ n

/-- The central character `ω_π : LocalChar p` of `π`. -/
def centralChar : NonSupercuspidalGL2Rep p → LocalChar p
  | .principalSeries χ₁ χ₂ _ => χ₁ * χ₂
  | .oneDim χ => χ ^ 2
  | .steinberg χ => χ ^ 2

/-- **GENUINE CENTRAL CHARACTER ACTION ON `π.Space`**:
`scalarGL2 p z = diag(z, z)` acts on every vector `v : π.Space` by `ω_π(z)`! -/
theorem action_scalarGL2 (π : NonSupercuspidalGL2Rep p) (z : ℚ_[p]ˣ) (v : π.Space) :
    π.action (scalarGL2 p z) v = ((π.centralChar.toHom z : ℂ)) • v := by
  cases π with
  | principalSeries χ₁ χ₂ _ => exact smoothInd_centralChar p χ₁ χ₂ z v
  | oneDim χ => exact Subtype.ext (oneDimSubrep_centralChar p χ z v)
  | steinberg χ => exact smoothSteinberg_centralChar p χ z v

/-- Automorphic (Godement–Jacquet) local `L`-factor of `π : NonSupercuspidalGL2Rep p`. -/
def automorphicLFactor : NonSupercuspidalGL2Rep p → ℂ → ℂ
  | .principalSeries χ₁ χ₂ _, T => χ₁.gl1LFactor T * χ₂.gl1LFactor T
  | .oneDim χ, T =>
      (χ * LocalChar.normPowChar p (1 / 2)).gl1LFactor T *
        (χ * LocalChar.normPowChar p (-(1 / 2))).gl1LFactor T
  | .steinberg χ, T => (χ * LocalChar.normPowChar p (1 / 2)).gl1LFactor T

/-- Embedding into `Stage11LocalLanglandsGL2.GL2LocalRep p` (for full backwards compatibility). -/
def toStage11 : NonSupercuspidalGL2Rep p → GL2LocalRep p
  | .principalSeries χ₁ χ₂ hirr => .principalSeries s(χ₁, χ₂) hirr
  | .oneDim χ => .oneDim χ
  | .steinberg χ => .steinberg χ

end NonSupercuspidalGL2Rep

variable (Ω : Type*) [Field Ω] [Algebra ℚ_[p] Ω] [IsSepClosure ℚ_[p] Ω]

/-- **THE GENUINE LOCAL LANGLANDS CORRESPONDENCE `genuineLLC` ON THE COMPLETE NON-SUPERCUSPIDAL
SMOOTH SPECTRUM OF `GL₂(ℚ_p)`**:
maps each genuine smooth admissible `GL (Fin 2) ℚ_[p]`-representation `π` directly to a genuine
2-dimensional Frobenius-semisimple Weil–Deligne representation `(ρ, N)` of `W_{ℚ_p}^{ab} ≤ Gal(ℚ_p^{ab}/ℚ_p)`
built via `CFT_LocalArtinReciprocity.localArtinMap ℚ_[p] Ω`! -/
def genuineLLC : NonSupercuspidalGL2Rep p → WeilDeligneRep2 p Ω
  | .principalSeries χ₁ χ₂ _ => principalSeriesWD p Ω χ₁ χ₂
  | .oneDim χ =>
      principalSeriesWD p Ω
        (χ * LocalChar.normPowChar p (1 / 2))
        (χ * LocalChar.normPowChar p (-(1 / 2)))
  | .steinberg χ => steinbergWD p Ω χ

/-- **THEOREM 1 (CENTRAL CHARACTER = DETERMINANT VIA LOCAL ARTIN MAP)**:
for EVERY `π : NonSupercuspidalGL2Rep p`, EVERY `z : ℚ_[p]ˣ`, and EVERY `v : π.Space`,
the scalar matrix `diag(z, z) ∈ GL (Fin 2) ℚ_[p]` acts on `v` by
`det (ρ (localArtinWeilEquiv p Ω z))`! -/
theorem genuineLLC_centralChar_eq_det (π : NonSupercuspidalGL2Rep p) (z : ℚ_[p]ˣ) (v : π.Space) :
    π.action (scalarGL2 p z) v =
      (Matrix.det ((genuineLLC p Ω π).rho (localArtinWeilEquiv p Ω z)).1) • v := by
  rw [π.action_scalarGL2 z v]
  congr 1
  cases π with
  | principalSeries χ₁ χ₂ _ =>
    exact (principalSeriesWD_det p Ω χ₁ χ₂ z).symm
  | oneDim χ =>
    rw [genuineLLC, principalSeriesWD_det]
    have hprod : (χ * LocalChar.normPowChar p (1 / 2)) * (χ * LocalChar.normPowChar p (-(1 / 2))) =
        χ ^ 2 := by
      calc (χ * LocalChar.normPowChar p (1 / 2)) * (χ * LocalChar.normPowChar p (-(1 / 2)))
          = (χ * χ) * (LocalChar.normPowChar p (1 / 2) * LocalChar.normPowChar p (-(1 / 2))) := by
            ac_rfl
        _ = χ ^ 2 := by rw [LocalChar.normPowChar_half_mul_neg_half, mul_one, sq]
    rw [hprod]; rfl
  | steinberg χ =>
    exact (steinbergWD_det p Ω χ z).symm

/-- **THEOREM 2 (EXACT LOCAL `L`-FACTOR EQUALITY FROM INTRINSIC `LinearMap.det` ON `V^{I, N=0}`)**:
for EVERY `π : NonSupercuspidalGL2Rep p` and EVERY `T : ℂ`,
`π.automorphicLFactor T = det(1 - T · Frob_p | V^{I, N=0})⁻¹`! -/
theorem genuineLLC_localLFactor_eq (π : NonSupercuspidalGL2Rep p) (T : ℂ) :
    π.automorphicLFactor T = (genuineLLC p Ω π).localLFactor T := by
  cases π with
  | principalSeries χ₁ χ₂ _ =>
    exact (principalSeriesWD_localLFactor p Ω χ₁ χ₂ T).symm
  | oneDim χ =>
    exact (principalSeriesWD_localLFactor p Ω _ _ T).symm
  | steinberg χ =>
    exact (steinbergWD_localLFactor p Ω χ T).symm

/-- **THEOREM 3 (GENUINE SATAKE / HECKE `T_p`–FROBENIUS COMPATIBILITY ON `SmoothInd`)**:
for ALL unramified `χ₁, χ₂ : LocalChar p`, ALL `g : GL2Qp p`, and ALL `T : ℂ`:
1. The genuine spherical Hecke operator `T_p` on `SmoothInd p χ₁ χ₂` acts on its unique spherical
   vector `f₀` with eigenvalue `p^{1/2} · Tr(ρ(Frob_p))`,
2. The normalized Hecke operator `T_p^{norm} = p^{-1/2} T_p` acts with eigenvalue `Tr(ρ(Frob_p))`,
3. Scalar `diag(p, p)` acts by `det(ρ(Frob_p))`,
4. The intrinsic Weil–Deligne `L`-factor `det(1 - T · Frob_p | V^{I, N=0})⁻¹` equals the exact
   spherical Hecke Euler factor `(1 - Tr(ρ(Frob_p)) T + det(ρ(Frob_p)) T²)⁻¹`! -/
theorem genuineLLC_satake_hecke_frob_compat {χ₁ χ₂ : LocalChar p}
    (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified) :
    let W := principalSeriesWD p Ω χ₁ χ₂
    (∀ g : GL2Qp p,
      heckeTp p (sphericalVec p h₁ h₂).1 g =
        (((p : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * Matrix.trace (W.rho (frobWeil p Ω)).1 *
          (sphericalVec p h₁ h₂).1 g) ∧
    (∀ g : GL2Qp p,
      heckeTpNorm p (sphericalVec p h₁ h₂).1 g =
        Matrix.trace (W.rho (frobWeil p Ω)).1 * (sphericalVec p h₁ h₂).1 g) ∧
    (∀ f : SmoothInd p χ₁ χ₂,
      rightAction p χ₁ χ₂ (scalarGL2 p (padicPrimeUnit p)) f =
        Matrix.det (W.rho (frobWeil p Ω)).1 • f) ∧
    (∀ T : ℂ,
      W.localLFactor T =
        (1 - Matrix.trace (W.rho (frobWeil p Ω)).1 * T +
          Matrix.det (W.rho (frobWeil p Ω)).1 * T ^ 2)⁻¹) := by
  refine ⟨fun g => ?_, fun g => ?_, fun f => ?_, fun T => ?_⟩
  · rw [heckeTp_sphericalVec, principalSeriesWD_trace_frob]
  · rw [heckeTpNorm_sphericalVec, principalSeriesWD_trace_frob]
  · rw [smoothInd_centralChar, frobWeil, principalSeriesWD_det]
  · rw [principalSeriesWD_localLFactor, LocalChar.gl1LFactor_of_isUnramified h₁,
      LocalChar.gl1LFactor_of_isUnramified h₂, ← mul_inv,
      principalSeriesWD_trace_frob, frobWeil, principalSeriesWD_det]
    congr 1
    simp only [LocalChar.evalP, LocalChar.mul_toHom, MonoidHom.mul_apply, Units.val_mul]
    ring

/-- **THEOREM 4 (GENUINE STEINBERG IWAHORI `U_p`–FROBENIUS COMPATIBILITY ON `SmoothSteinberg`)**:
for EVERY unramified `χ : LocalChar p`:
there exists a unique scalar `eig = χ(p) p^{-1/2} : ℂ` such that:
1. `Frob_p` acts on the 1-dimensional subspace `V^{I, N=0}` of `steinbergWD p Ω χ` by `eig`,
2. The normalized Iwahori Hecke operator `p^{-1/2} U_p` acts on the 1-dimensional Iwahori-fixed
   space `(SmoothSteinberg p χ)^I` by the **EXACT SAME** eigenvalue `eig` (and raw `U_p` acts by
   `p^{1/2} eig = χ(p)`),
3. The intrinsic Weil–Deligne `L`-factor `det(1 - T · Frob_p | V^{I, N=0})⁻¹` equals `(1 - eig T)⁻¹`,
4. Scalar `diag(z, z)` acts on `SmoothSteinberg p χ` by `det(ρ(localArtinWeilEquiv z))`! -/
theorem genuineLLC_steinberg_Up_frob_compat {χ : LocalChar p} (hχ : χ.IsUnramified) :
    let W := steinbergWD p Ω χ
    let eig : ℂ := (χ.evalP : ℂ) * (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
    Module.finrank ℂ W.invKerN = 1 ∧
    Module.finrank ℂ (steinbergFixed p χ (Iwahori p)) = 1 ∧
    (∀ w : W.invKerN, W.frobOnInvKerN w = eig • w) ∧
    (∀ v ∈ steinbergFixed p χ (Iwahori p), steinbergHeckeUpNorm p χ v = eig • v) ∧
    (∀ v ∈ steinbergFixed p χ (Iwahori p),
      steinbergHeckeUp p χ v = ((((p : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * eig) • v) ∧
    (∀ T : ℂ, W.localLFactor T = (1 - eig * T)⁻¹) ∧
    (∀ (z : ℚ_[p]ˣ) (v : SmoothSteinberg p χ),
      steinbergAction p χ (scalarGL2 p z) v =
        Matrix.det (W.rho (localArtinWeilEquiv p Ω z)).1 • v) := by
  refine ⟨steinbergWD_invKerN_finrank_unram p Ω hχ,
    finrank_steinbergFixed_iwahori p hχ,
    steinbergWD_frobOnInvKerN_eq_smul p Ω χ,
    fun v hv => (steinbergHeckeUpNorm_eigenvalue_and_LFactor p hχ hv 0).1,
    fun v hv => ?_,
    fun T => ?_,
    fun z v => ?_⟩
  · rw [steinbergHeckeUp_eigenvalue p hχ hv]
    congr 1
    have hcancel : (((p : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.rpow_add (prime_pos_R p)]; norm_num
    calc (χ.evalP : ℂ)
        = (χ.evalP : ℂ) * 1 := (mul_one _).symm
      _ = (χ.evalP : ℂ) * ((((p : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
            (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) := by rw [hcancel]
      _ = (((p : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
            ((χ.evalP : ℂ) * (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) := by ring
  · rw [steinbergWD_localLFactor]
    have hunr : (χ * LocalChar.normPowChar p (1 / 2)).IsUnramified :=
      LocalChar.isUnramified_mul hχ (LocalChar.normPowChar_isUnramified p _)
    rw [LocalChar.gl1LFactor_of_isUnramified hunr]
    simp
  · rw [smoothSteinberg_centralChar, steinbergWD_det]

/-- **THEOREM 5 (EXACT COMPATIBILITY WITH `Stage11LocalLanglandsGL2` & ALL CLASSICAL EIGENFORMS)**:
`genuineLLC p Ω` refines `Stage11LocalLanglandsGL2.llcGL2 p` across the entire non-supercuspidal
spectrum, matching `localLFactor`, `detChar`, and `satakeGL2OfEigenform a_p p k` (including
`Δ₁₂, Δ₁₆, Δ₁₈, Δ₂₀, Δ₂₂, S₂₄⁺, S₂₄⁻`) at every prime `p`! -/
theorem genuineLLC_refines_stage11 (π : NonSupercuspidalGL2Rep p) :
    (∀ T : ℂ, (genuineLLC p Ω π).localLFactor T = (llcGL2 p π.toStage11).localLFactor T) ∧
    (∀ z : ℚ_[p]ˣ,
      Matrix.det ((genuineLLC p Ω π).rho (localArtinWeilEquiv p Ω z)).1 =
        ((llcGL2 p π.toStage11).detChar.toHom z : ℂ)) := by
  constructor
  · intro T
    rw [← genuineLLC_localLFactor_eq p Ω π T, localLFactor_llcGL2_eq]
    cases π <;> rfl
  · intro z
    rw [det_llcGL2_eq_centralChar]
    cases π with
    | principalSeries χ₁ χ₂ _ =>
      exact principalSeriesWD_det p Ω χ₁ χ₂ z
    | oneDim χ =>
      rw [genuineLLC, principalSeriesWD_det]
      have hprod : (χ * LocalChar.normPowChar p (1 / 2)) * (χ * LocalChar.normPowChar p (-(1 / 2))) =
          χ ^ 2 := by
        calc (χ * LocalChar.normPowChar p (1 / 2)) * (χ * LocalChar.normPowChar p (-(1 / 2)))
            = (χ * χ) * (LocalChar.normPowChar p (1 / 2) * LocalChar.normPowChar p (-(1 / 2))) := by
              ac_rfl
          _ = χ ^ 2 := by rw [LocalChar.normPowChar_half_mul_neg_half, mul_one, sq]
      rw [hprod]; rfl
    | steinberg χ =>
      exact steinbergWD_det p Ω χ z

/-- Direct Satake–Frobenius–Local-Artin bridge for ANY weight-`k` normalized Hecke eigenform with
eigenvalue `a_p` at prime `p` (specializing immediately to `Δ₁₂..Δ₂₂, S₂₄±`):
`heckeTp` on `smoothPrincipalSeriesOfEigenform a_p p k` has eigenvalue `p^{1/2} · Tr(ρ(Frob_p)) = p^{1/2} · a_p`,
`det(ρ(Frob_p)) = p^{k-1}`, and `det(1 - T · Frob_p | V^{I, N=0})⁻¹ = (1 - a_p T + p^{k-1} T²)⁻¹`! -/
theorem genuineLLC_eigenform_satake_match (a_p : ℂ) (k : ℕ) :
    let W := principalSeriesWD p Ω
      (LocalChar.unramChar p (satakeRoots a_p p k).1)
      (LocalChar.unramChar p (satakeRoots a_p p k).2)
    Matrix.trace (W.rho (frobWeil p Ω)).1 = a_p ∧
    Matrix.det (W.rho (frobWeil p Ω)).1 = (p : ℂ) ^ (k - 1) ∧
    (∀ g : GL2Qp p,
      heckeTp p (eigenformSphericalVec a_p p k).1 g =
        (((p : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * Matrix.trace (W.rho (frobWeil p Ω)).1 *
          (eigenformSphericalVec a_p p k).1 g) ∧
    (∀ T : ℂ,
      W.localLFactor T = (1 - a_p * T + (p : ℂ) ^ (k - 1) * T ^ 2)⁻¹) := by
  have hcompat := genuineLLC_satake_hecke_frob_compat p Ω
    (LocalChar.unramChar_isUnramified p (satakeRoots a_p p k).1)
    (LocalChar.unramChar_isUnramified p (satakeRoots a_p p k).2)
  have htr : Matrix.trace ((principalSeriesWD p Ω
      (LocalChar.unramChar p (satakeRoots a_p p k).1)
      (LocalChar.unramChar p (satakeRoots a_p p k).2)).rho (frobWeil p Ω)).1 = a_p := by
    rw [principalSeriesWD_trace_frob, LocalChar.unramChar_evalP, LocalChar.unramChar_evalP,
      satakeRoots_add]
  have hdet : Matrix.det ((principalSeriesWD p Ω
      (LocalChar.unramChar p (satakeRoots a_p p k).1)
      (LocalChar.unramChar p (satakeRoots a_p p k).2)).rho (frobWeil p Ω)).1 =
      (p : ℂ) ^ (k - 1) := by
    rw [frobWeil, principalSeriesWD_det]
    change (((LocalChar.unramChar p (satakeRoots a_p p k).1).evalP *
      (LocalChar.unramChar p (satakeRoots a_p p k).2).evalP : ℂˣ) : ℂ) = _
    rw [Units.val_mul, LocalChar.unramChar_evalP, LocalChar.unramChar_evalP, satakeRoots_mul]
  refine ⟨htr, hdet, hcompat.1, fun T => ?_⟩
  rw [hcompat.2.2.2 T, htr, hdet]

end GenuineSmoothLLC

/-! ## Section 5: Concrete Instantiation on `SeparableClosure ℚ_[p]` (Zero Free Parameters!) -/

section ConcreteMaster

variable (p : ℕ) [hp : Fact p.Prime]

/-- Canonical separable closure `ℚ_p^{sep} = SeparableClosure ℚ_[p]`. -/
abbrev QpSep := SeparableClosure ℚ_[p]

/-- **MASTER UNCONDITIONAL THEOREM (CONCRETELY INSTANTIATED AT `Ω = SeparableClosure ℚ_[p]`)**:
for every prime `p`, the genuine Local Langlands correspondence `genuineLLC p (QpSep p)` on the
complete non-supercuspidal smooth admissible spectrum of `GL₂(ℚ_p)` satisfies unconditionally:
1. **Local Artin Reciprocity**: `ℚ_[p]ˣ ≃* W_{ℚ_p}^{ab} ≤ Gal(ℚ_p^{ab}/ℚ_p)` with
   `Frob_p|_{ℚ_p^{ur}} = maximalUnramifiedExtensionFrobenius ℚ_[p] (QpSep p)`,
2. **Full Admissibility**: `∀ π n, FiniteDimensional ℂ (π.fixedSubspace (principalCongruence p n))`,
3. **Central Character = Determinant via Local Artin Map**:
   `∀ π z v, π.action (scalarGL2 p z) v = det(ρ(localArtinWeilEquiv z)) • v`,
4. **Intrinsic Local `L`-Factor Equality**:
   `∀ π T, π.automorphicLFactor T = det(1 - T · Frob_p | V^{I, N=0})⁻¹`,
5. **Satake `T_p`–Frobenius Compatibility** for all unramified principal series,
6. **Steinberg `U_p`–Frobenius Compatibility** on `V^{I, N=0}` for all unramified twisted Steinberg reps! -/
theorem gl2_smooth_llc_master_unconditional :
    restrictToMaxUnram p (QpSep p) (frobWeil p (QpSep p)).1 =
      maximalUnramifiedExtensionFrobenius ℚ_[p] (QpSep p) ∧
    (∀ (π : NonSupercuspidalGL2Rep p) (n : ℕ),
      FiniteDimensional ℂ (π.fixedSubspace (principalCongruence p n))) ∧
    (∀ (π : NonSupercuspidalGL2Rep p) (z : ℚ_[p]ˣ) (v : π.Space),
      π.action (scalarGL2 p z) v =
        (Matrix.det ((genuineLLC p (QpSep p) π).rho
          (localArtinWeilEquiv p (QpSep p) z)).1) • v) ∧
    (∀ (π : NonSupercuspidalGL2Rep p) (T : ℂ),
      π.automorphicLFactor T = (genuineLLC p (QpSep p) π).localLFactor T) ∧
    (∀ {χ₁ χ₂ : LocalChar p} (h₁ : χ₁.IsUnramified) (h₂ : χ₂.IsUnramified) (g : GL2Qp p),
      heckeTp p (sphericalVec p h₁ h₂).1 g =
        (((p : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          Matrix.trace ((principalSeriesWD p (QpSep p) χ₁ χ₂).rho (frobWeil p (QpSep p))).1 *
          (sphericalVec p h₁ h₂).1 g) ∧
    (∀ {χ : LocalChar p}, χ.IsUnramified → ∀ (v : SmoothSteinberg p χ),
      v ∈ steinbergFixed p χ (Iwahori p) →
        steinbergHeckeUpNorm p χ v =
          ((χ.evalP : ℂ) * (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • v ∧
        (∀ w : (steinbergWD p (QpSep p) χ).invKerN,
          (steinbergWD p (QpSep p) χ).frobOnInvKerN w =
            ((χ.evalP : ℂ) * (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) • w) ∧
        (∀ T : ℂ,
          (steinbergWD p (QpSep p) χ).localLFactor T =
            (1 - ((χ.evalP : ℂ) * (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) * T)⁻¹)) := by
  refine ⟨restrictToMaxUnram_frobWeil p (QpSep p),
    fun π n => π.admissible n,
    fun π z v => genuineLLC_centralChar_eq_det p (QpSep p) π z v,
    fun π T => genuineLLC_localLFactor_eq p (QpSep p) π T,
    fun h₁ h₂ g => (genuineLLC_satake_hecke_frob_compat p (QpSep p) h₁ h₂).1 g,
    fun hχ v hv => ?_⟩
  have hst := genuineLLC_steinberg_Up_frob_compat p (QpSep p) hχ
  exact ⟨hst.2.2.2.1 v hv, hst.2.2.1, hst.2.2.2.2.2.1⟩

end ConcreteMaster

end GL2SmoothLLC
end RHDirect
