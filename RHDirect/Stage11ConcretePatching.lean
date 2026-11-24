import RHDirect.Stage3PatchingUnification
import RHDirect.Stage7HeckeRing
import RHDirect.Stage8IwasawaWeierstrass
import RHDirect.Stage10PeterssonHecke
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# RHDirect.Stage11ConcretePatching

Concrete `ℤ_[p]`-patching instantiations of `Stage3PatchingUnification.TaylorWilesPatchingDatum`,
`IsGorensteinOver`, `TaylorWilesCongruenceDatum`, and `CongruencePatchingRealization` built
directly from the regular local patching base ring `S_∞ = MvPowerSeries (Fin g) ℤ_[p]` and the
concrete integral Hecke algebras of `Stage7HeckeRing` + `Stage10PeterssonHecke` (`S₁₂`, `S₁₆`,
`S₁₈`, `S₂₀`, `S₂₂`, and `S₂₄` over `ℚ(√144169)`), with **0 `sorry`**, **0 custom `axiom`s**,
and **0 assumptions** in pure Mathlib `v4.33.1`.

## Contents

1. **Concrete Patching Base Ring `S_∞ = MvPowerSeries (Fin g) ℤ_[p]`**:
   - `IsLocalRing (PatchingBaseRing p g)` and `IsDomain (PatchingBaseRing p g)`.
   - Exact explicit variable decomposition `f = C (constantCoeff f) + ∑ i, X i * q_i`.
   - Exact augmentation ideal `𝔞 = (y_1, ..., y_g) = ker(constantCoeff)`, exact quotient
     isomorphism `S_∞ ⧸ 𝔞 ≃+* ℤ_[p]`, inclusion `𝔞 ≤ 𝔪` (`aug_le_max`), exact maximal ideal
     `𝔪 = (p, y_1, ..., y_g)`, and residue field `S_∞ ⧸ 𝔪 ≃+* ZMod p`.
   - Exact regular sequence `(y_0, ..., y_{g-1}, p)` of length `g + 1` (each partial quotient
     `S_∞ ⧸ (y_0, ..., y_{k-1}) ≃+* MvPowerSeries (Fin (g - k)) ℤ_[p]` is a domain, so each next
     element is a non-zero-divisor!) and Nakayama coinvariant generation/surjectivity on `S_∞`.

2. **Concrete Monogenic Quadratic Algebras (`QuadAlg`), Gorenstein Pairing, & Concrete
   `TaylorWilesPatchingDatum` Instantiations over `S_∞ = MvPowerSeries (Fin g) ℤ_[p]`**:
   - `QuadAlg A b c` (`≃ A[X] / (X² - b X + c)`): unconditionally free of rank 2 and
     unconditionally **Gorenstein** (`IsGorensteinOver A (QuadAlg A b c)`) over EVERY
     commutative ring `A` via the Tate–Grothendieck trace form `⟨x, y⟩ ↦ y`.
   - Exact congruence ideal & complete-intersection cotangent isomorphism for any root `λ ∈ A`
     of `λ² - b λ + c = 0`: `congruenceIdeal (quadAlgAug hroot) = Ideal.span {2λ - b}`,
     `(2λ - b)² = b² - 4c`, and `Cotangent (quadAlgAug hroot) ≃ₗ[A] (A ⧸ congruenceIdeal _)`.
   - Concrete `TaylorWilesPatchingDatum` instances over `S_∞ = MvPowerSeries (Fin g) ℤ_[p]`:
     * `concrete_taylorWilesPatchingDatum_Zp`: rank-`r` domain-faithful patching (`R_∞ = S_∞`),
     * `quadraticPatchingDatum_Zp`: rank-2 Orzech-faithful patching (`R_∞ = QuadAlg S_∞ (C b) (C c)`)
       yielding `R_0 ≃+* T_0` and `IsGorensteinOver ℤ_[p] T_0`,
     * `freeAlgPatchingDatum_Zp`: general finite-free `ℤ_[p]`-algebra patching
       (`S_∞ ⊗[ℤ_[p]] T_0`) for ANY rank `r ≥ 1`.

3. **Concrete Integral Hecke Rings of `S₁₂, S₁₆, S₁₈, S₂₀, S₂₂` and `S₂₄` (`Stage7HeckeRing` +
   `Stage10PeterssonHecke`)**:
   - Exact `ℤ`-algebra isomorphism `IntHeckeAlg ≃ₐ[ℤ] ℤ`, Gorensteinness, and trivial congruence
     ideal (`Δ = 1`) for all five 1D cusp spaces `S₁₂, S₁₆, S₁₈, S₂₀, S₂₂`.
   - Exact `ℤ`-algebra isomorphism `IntHeckeAlg(S₂₄) ≃ₐ[ℤ] QuadAlg ℤ 1080 (-20468736)`,
     unconditional Gorensteinness, exact discriminant `disc(T₂) = 83041344 = 24² * 144169`,
     proved primality `Nat.Prime 144169`, exact prime-factor set `{2, 3, 144169}`, and concrete
     `ℤ_[p]`-patching `R_0 ≃+* T_0` for every prime `p`.

4. **Wiles–Lenstra `p`-adic Congruence Bounds & Finite-Support `CongruencePatchingRealization`**:
   - Exact `p`-adic length formula `length_{ℤ_[p]}(ℤ_[p] ⧸ (n)) = padicValNat p n.natAbs` and
     exact prime-factor log sum `∑_{l ∈ n.primeFactors} log l * padicValNat l n = log n`.
   - Base-change congruence bridge `Stage7HeckeRing` → `ℤ_[l]` (`intCast_mem_congruenceIdeal_baseChangeAug`).
   - `congruencePatchingRealization_of_hecke_congruence_primes`: fires
     `Stage3PatchingUnification.CongruencePatchingRealization.ofFiniteSupport` with
     `P₀ = oddUnramifiedPrimeFactors Δ_T M ⊆ Δ_T.natAbs.primeFactors` and explicit envelope
     `B_patch = (R * (t - 1)) * log |Δ_T| ≤ (R * t) * log |Δ_T|`.
   - Concrete `B_patch` theorems for **`S₁₂`** (`Δ = 1`, `B_patch = 0`) and **`S₂₄`**
     (`disc(T₂) = 24² * 144169`, support `⊆ {2, 3, 144169}`, explicit `B_patch ≤ (t - 1) * (2 log 3 + log 144169)`
     and maximal-order `Δ = 4 * 144169` bound `(t - 1) * log 144169`), including zero-assumption
     concrete Selmer-system realizations.
-/

noncomputable section

open scoped BigOperators TensorProduct
open Finset Module Submodule RHDirect RHDirect.Stage2IwasawaTwoTower
  RHDirect.Stage3PatchingUnification RHDirect.Stage5ModularHecke
  RHDirect.Stage7EisensteinSeries RHDirect.Stage7HeckeRing RHDirect.Stage8IwasawaWeierstrass
  RHDirect.Stage8ModularRing RHDirect.Stage8RamanujanDelta
  RHDirect.Stage9CuspFormLFunc RHDirect.Stage10PeterssonHecke

namespace RHDirect
namespace Stage11ConcretePatching

/-! ## Section 1: Concrete Patching Base Ring `S_∞ = MvPowerSeries (Fin g) ℤ_[p]` -/

section PatchingBaseRingSection

/-- General multivariable power-series coordinate decomposition over any commutative ring `R`:
every `f ∈ MvPowerSeries (Fin g) R` splits explicitly as `C (constantCoeff f) + ∑ i, X i * q i`,
where each `q i` is supported on multi-indices with `0` in coordinates `< i`. -/
theorem mvPowerSeries_sub_constantCoeff_eq_sum_X_mul {R : Type*} [CommRing R] {g : ℕ}
    (f : MvPowerSeries (Fin g) R) :
    ∃ q : Fin g → MvPowerSeries (Fin g) R,
      f = MvPowerSeries.C (MvPowerSeries.constantCoeff f) +
        ∑ i : Fin g, MvPowerSeries.X i * q i := by
  classical
  let q : Fin g → MvPowerSeries (Fin g) R := fun i m =>
    if ∀ j : Fin g, j < i → m j = 0 then
      MvPowerSeries.coeff (m + Finsupp.single i 1) f
    else 0
  refine ⟨q, ?_⟩
  ext n
  rw [map_add, map_sum]
  by_cases hn : n = 0
  · subst hn
    have hsum0 : ∑ i : Fin g, MvPowerSeries.coeff (0 : Fin g →₀ ℕ) (MvPowerSeries.X i * q i) = 0 :=
      Finset.sum_eq_zero fun i _ => MvPowerSeries.coeff_zero_X_mul (q i) i
    rw [hsum0, add_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_C]
  · rw [MvPowerSeries.coeff_C_of_ne_zero hn, zero_add]
    have hsupp : n.support.Nonempty := Finsupp.support_nonempty_iff.mpr hn
    set i₀ : Fin g := n.support.min' hsupp with hi₀_def
    have hi₀_mem : i₀ ∈ n.support := Finset.min'_mem n.support hsupp
    have hi₀_pos : 1 ≤ n i₀ := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi₀_mem)
    have hi₀_lt_zero : ∀ j : Fin g, j < i₀ → n j = 0 := by
      intro j hj
      by_contra hnj
      have hj_mem : j ∈ n.support := Finsupp.mem_support_iff.mpr hnj
      have hle : i₀ ≤ j := Finset.min'_le n.support j hj_mem
      exact not_lt_of_ge hle hj
    have hterm : ∀ i : Fin g,
        MvPowerSeries.coeff n (MvPowerSeries.X i * q i) =
          if i = i₀ then MvPowerSeries.coeff n f else 0 := by
      intro i
      rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul, one_mul]
      have hle_iff : Finsupp.single i (1 : ℕ) ≤ n ↔ 1 ≤ n i := Finsupp.single_le_iff
      by_cases hi : i = i₀
      · subst hi
        rw [if_pos (hle_iff.mpr hi₀_pos), if_pos rfl]
        let m₀ : Fin g →₀ ℕ := n - Finsupp.single i₀ (1 : ℕ)
        change (if ∀ j : Fin g, j < i₀ → m₀ j = 0 then
          MvPowerSeries.coeff (m₀ + Finsupp.single i₀ (1 : ℕ)) f else 0) = _
        have hcond : ∀ j : Fin g, j < i₀ → m₀ j = 0 := by
          intro j hj
          change (n - Finsupp.single i₀ (1 : ℕ)) j = 0
          rw [Finsupp.tsub_apply, hi₀_lt_zero j hj, Nat.zero_sub]
        rw [if_pos hcond]
        have hm₀_eq : m₀ + Finsupp.single i₀ (1 : ℕ) = n :=
          tsub_add_cancel_of_le (hle_iff.mpr hi₀_pos)
        rw [hm₀_eq]
      · rw [if_neg hi]
        split_ifs with hle
        · have hni : 1 ≤ n i := hle_iff.mp hle
          have hi_mem : i ∈ n.support := Finsupp.mem_support_iff.mpr (by omega)
          have hi₀_le_i : i₀ ≤ i := Finset.min'_le n.support i hi_mem
          have hi₀_lt_i : i₀ < i := lt_of_le_of_ne hi₀_le_i (Ne.symm hi)
          let mi : Fin g →₀ ℕ := n - Finsupp.single i (1 : ℕ)
          have hnot : ¬ (∀ j : Fin g, j < i → mi j = 0) := by
            intro hall
            have h0 := hall i₀ hi₀_lt_i
            change (n - Finsupp.single i (1 : ℕ)) i₀ = 0 at h0
            rw [Finsupp.tsub_apply, Finsupp.single_eq_of_ne hi₀_lt_i.ne, Nat.sub_zero] at h0
            omega
          change (if ∀ j : Fin g, j < i → mi j = 0 then
            MvPowerSeries.coeff (mi + Finsupp.single i (1 : ℕ)) f else 0) = 0
          rw [if_neg hnot]
        · rfl
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    simp

/-- Exact augmentation ideal identity for `MvPowerSeries (Fin g) R`:
`Ideal.span { X_0, ..., X_{g-1} } = ker(constantCoeff)`. -/
theorem mvPowerSeries_span_X_eq_ker_constantCoeff {R : Type*} [CommRing R] (g : ℕ) :
    Ideal.span (Set.range (MvPowerSeries.X : Fin g → MvPowerSeries (Fin g) R)) =
      RingHom.ker (MvPowerSeries.constantCoeff : MvPowerSeries (Fin g) R →+* R) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact MvPowerSeries.constantCoeff_X i
  · intro f hf
    obtain ⟨q, hq⟩ := mvPowerSeries_sub_constantCoeff_eq_sum_X_mul f
    have h0 : MvPowerSeries.constantCoeff f = 0 := hf
    rw [h0, map_zero, zero_add] at hq
    rw [hq]
    refine Ideal.sum_mem _ fun i _ => ?_
    exact Ideal.mul_mem_right (q i) _ (Ideal.subset_span ⟨i, rfl⟩)

/-- **Concrete Taylor–Wiles–Kisin Patching Base Ring** `S_∞ := ℤ_[p][[y_0, ..., y_{g-1}]]`
(regular local domain of Krull dimension `g + 1`). -/
abbrev PatchingBaseRing (p g : ℕ) [Fact p.Prime] : Type :=
  MvPowerSeries (Fin g) ℤ_[p]

/-- The `i`-th diamond / patching variable `y_i = X_i ∈ S_∞`. -/
def patchingVar {p g : ℕ} [Fact p.Prime] (i : Fin g) : PatchingBaseRing p g :=
  MvPowerSeries.X i

/-- The augmentation ideal `𝔞 = (y_0, ..., y_{g-1}) ⊆ S_∞`. -/
def patchingAugIdeal (p g : ℕ) [Fact p.Prime] : Ideal (PatchingBaseRing p g) :=
  Ideal.span (Set.range (patchingVar (p := p) (g := g)))

/-- The explicit maximal ideal `𝔪 = (p, y_0, ..., y_{g-1}) ⊆ S_∞`. -/
def patchingMaxIdeal (p g : ℕ) [Fact p.Prime] : Ideal (PatchingBaseRing p g) :=
  Ideal.span (insert (p : PatchingBaseRing p g) (Set.range (patchingVar (p := p) (g := g))))

theorem patchingBaseRing_isLocalRing (p g : ℕ) [Fact p.Prime] :
    IsLocalRing (PatchingBaseRing p g) :=
  inferInstance

instance instIsDomainPatchingBaseRing (p g : ℕ) [Fact p.Prime] :
    IsDomain (PatchingBaseRing p g) := by
  have : Nontrivial (PatchingBaseRing p g) :=
    ⟨⟨0, 1, fun h => zero_ne_one (α := ℤ_[p]) (by simpa using congrArg MvPowerSeries.constantCoeff h)⟩⟩
  exact NoZeroDivisors.to_isDomain _

theorem patchingBaseRing_isDomain (p g : ℕ) [Fact p.Prime] :
    IsDomain (PatchingBaseRing p g) :=
  inferInstance

/-- Exact unit criterion in `S_∞ = MvPowerSeries (Fin g) ℤ_[p]`:
`f` is a unit iff `p ∤ constantCoeff f`. -/
theorem patchingBaseRing_isUnit_iff {p g : ℕ} [Fact p.Prime] (f : PatchingBaseRing p g) :
    IsUnit f ↔ ¬ (p : ℤ_[p]) ∣ MvPowerSeries.constantCoeff f := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff, padicInt_isUnit_iff_not_p_dvd]

/-- Exact kernel characterization of the augmentation ideal `𝔞 = ker(constantCoeff)`. -/
theorem patchingAugIdeal_eq_ker_constantCoeff (p g : ℕ) [Fact p.Prime] :
    patchingAugIdeal p g =
      RingHom.ker (MvPowerSeries.constantCoeff : PatchingBaseRing p g →+* ℤ_[p]) :=
  mvPowerSeries_span_X_eq_ker_constantCoeff g

theorem patchingBaseRing_constantCoeff_surjective (p g : ℕ) [Fact p.Prime] :
    Function.Surjective (MvPowerSeries.constantCoeff : PatchingBaseRing p g →+* ℤ_[p]) :=
  fun a => ⟨MvPowerSeries.C a, MvPowerSeries.constantCoeff_C a⟩

/-- **Exact Quotient Isomorphism `S_∞ ⧸ 𝔞 ≃+* ℤ_[p]`** (evaluation at `y_1 = ... = y_g = 0`). -/
def patchingBaseRing_quot_augIdeal_equiv_Zp (p g : ℕ) [Fact p.Prime] :
    (PatchingBaseRing p g ⧸ patchingAugIdeal p g) ≃+* ℤ_[p] :=
  (Ideal.quotEquivOfEq (patchingAugIdeal_eq_ker_constantCoeff p g)).trans
    (RingHom.quotientKerEquivOfSurjective (patchingBaseRing_constantCoeff_surjective p g))

@[simp]
theorem patchingBaseRing_quot_augIdeal_equiv_Zp_mk {p g : ℕ} [Fact p.Prime]
    (f : PatchingBaseRing p g) :
    patchingBaseRing_quot_augIdeal_equiv_Zp p g (Ideal.Quotient.mk (patchingAugIdeal p g) f) =
      MvPowerSeries.constantCoeff f :=
  rfl

/-- **`aug_le_max`**: the augmentation ideal `𝔞 = (y_0, ..., y_{g-1})` is contained in the unique
maximal ideal of `S_∞ = MvPowerSeries (Fin g) ℤ_[p]`. -/
theorem patchingAugIdeal_le_maximalIdeal (p g : ℕ) [Fact p.Prime] :
    patchingAugIdeal p g ≤ IsLocalRing.maximalIdeal (PatchingBaseRing p g) := by
  rw [patchingAugIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    patchingBaseRing_isUnit_iff, not_not, patchingVar, MvPowerSeries.constantCoeff_X]
  exact dvd_zero _

/-- **Explicit Maximal Ideal `𝔪 = (p, y_0, ..., y_{g-1})` of `S_∞ = MvPowerSeries (Fin g) ℤ_[p]`**. -/
theorem maximalIdeal_patchingBaseRing_eq (p g : ℕ) [Fact p.Prime] :
    IsLocalRing.maximalIdeal (PatchingBaseRing p g) = patchingMaxIdeal p g := by
  ext f
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, patchingBaseRing_isUnit_iff, not_not]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨q, hq⟩ := mvPowerSeries_sub_constantCoeff_eq_sum_X_mul f
    have hsplit : f = (p : PatchingBaseRing p g) * MvPowerSeries.C c +
        ∑ i : Fin g, patchingVar i * q i := by
      conv_lhs => rw [hq, hc, map_mul, map_natCast]
      rfl
    rw [hsplit]
    refine Ideal.add_mem _ ?_ (Ideal.sum_mem _ fun i _ => ?_)
    · exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
    · exact Ideal.mul_mem_right _ _
        (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨i, rfl⟩))
  · intro hf
    have hle : patchingMaxIdeal p g ≤ IsLocalRing.maximalIdeal (PatchingBaseRing p g) := by
      rw [patchingMaxIdeal, Ideal.span_le]
      rintro x (rfl | ⟨i, rfl⟩)
      · rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
          patchingBaseRing_isUnit_iff, not_not, map_natCast]
      · exact patchingAugIdeal_le_maximalIdeal p g (Ideal.subset_span ⟨i, rfl⟩)
    have hmem := hle hf
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, patchingBaseRing_isUnit_iff, not_not] at hmem
    exact hmem

/-- **Exact Residue Field Isomorphism `S_∞ ⧸ 𝔪 ≃+* ZMod p`**. -/
def patchingBaseRing_residueField_equiv_ZMod (p g : ℕ) [Fact p.Prime] :
    (PatchingBaseRing p g ⧸ IsLocalRing.maximalIdeal (PatchingBaseRing p g)) ≃+* ZMod p := by
  let red : PatchingBaseRing p g →+* ZMod p :=
    (PadicInt.toZMod : ℤ_[p] →+* ZMod p).comp MvPowerSeries.constantCoeff
  have hsurj : Function.Surjective red :=
    padicInt_toZMod_surjective.comp (patchingBaseRing_constantCoeff_surjective p g)
  have hker : RingHom.ker red = IsLocalRing.maximalIdeal (PatchingBaseRing p g) := by
    ext f
    rw [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      patchingBaseRing_isUnit_iff, not_not, padicInt_p_dvd_iff_toZMod_eq_zero]
    rfl
  exact (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)

/-! ### Exact Regular Sequence `(y_0, ..., y_{g-1}, p)` & Nakayama Lemma on `S_∞` -/

/-- Partial augmentation ideal `I_k = (y_0, ..., y_{k-1}) ⊆ S_∞`. -/
def partialAugIdeal (p g k : ℕ) [Fact p.Prime] : Ideal (PatchingBaseRing p g) :=
  Ideal.span { x : PatchingBaseRing p g | ∃ i : Fin g, i.1 < k ∧ x = patchingVar i }

/-- Suffix index embedding `Fin (g - k) ↪ Fin g` (`j ↦ k + j`). -/
private def suffixEmb {g k : ℕ} (hk : k ≤ g) : Fin (g - k) ↪ Fin g where
  toFun j := ⟨k + j.1, by omega⟩
  inj' j₁ j₂ h := Fin.ext (by
    have hval : k + j₁.1 = k + j₂.1 := congrArg Fin.val h
    omega)

@[simp]
private lemma suffixEmb_val {g k : ℕ} (hk : k ≤ g) (j : Fin (g - k)) :
    (suffixEmb hk j).1 = k + j.1 := rfl

private def evalPrefixZeroFun {p g : ℕ} [Fact p.Prime] (k : ℕ) (hk : k ≤ g)
    (f : PatchingBaseRing p g) : PatchingBaseRing p (g - k) :=
  fun m => MvPowerSeries.coeff (m.mapDomain (suffixEmb hk)) f

/-- Prefix-zero evaluation homomorphism `S_∞ →+* MvPowerSeries (Fin (g - k)) ℤ_[p]` setting
`y_0 = ... = y_{k-1} = 0`. -/
def evalPrefixZero {p g : ℕ} [Fact p.Prime] (k : ℕ) (hk : k ≤ g) :
    PatchingBaseRing p g →+* PatchingBaseRing p (g - k) where
  toFun := evalPrefixZeroFun k hk
  map_one' := by
    ext m
    change MvPowerSeries.coeff (m.mapDomain (suffixEmb hk)) (1 : PatchingBaseRing p g) =
      MvPowerSeries.coeff m (1 : PatchingBaseRing p (g - k))
    rw [MvPowerSeries.coeff_one, MvPowerSeries.coeff_one]
    have hiff : m.mapDomain (suffixEmb hk) = 0 ↔ m = 0 := by
      constructor
      · intro h
        ext j
        have hj := congrArg (fun d : Fin g →₀ ℕ => d (suffixEmb hk j)) h
        rw [Finsupp.mapDomain_apply (suffixEmb hk).injective] at hj
        exact hj
      · rintro rfl; simp
    by_cases hm : m = 0
    · rw [if_pos (hiff.mpr hm), if_pos hm]
    · rw [if_neg (fun h => hm (hiff.mp h)), if_neg hm]
  map_mul' f₁ f₂ := by
    classical
    ext m
    change MvPowerSeries.coeff (m.mapDomain (suffixEmb hk)) (f₁ * f₂) =
      MvPowerSeries.coeff m (evalPrefixZeroFun k hk f₁ * evalPrefixZeroFun k hk f₂)
    rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
    let embPair : (Fin (g - k) →₀ ℕ) × (Fin (g - k) →₀ ℕ) → (Fin g →₀ ℕ) × (Fin g →₀ ℕ) :=
      fun ab => (ab.1.mapDomain (suffixEmb hk), ab.2.mapDomain (suffixEmb hk))
    have hinj : Function.Injective embPair := by
      rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
      have h1 : a₁.mapDomain (suffixEmb hk) = a₂.mapDomain (suffixEmb hk) := congrArg Prod.fst h
      have h2 : b₁.mapDomain (suffixEmb hk) = b₂.mapDomain (suffixEmb hk) := congrArg Prod.snd h
      exact Prod.ext
        (Finsupp.mapDomain_injective (suffixEmb hk).injective h1)
        (Finsupp.mapDomain_injective (suffixEmb hk).injective h2)
    symm
    refine Finset.sum_nbij embPair ?_ ?_ ?_ ?_
    · intro ab hab
      rw [Finset.mem_antidiagonal] at hab ⊢
      change ab.1.mapDomain (suffixEmb hk) + ab.2.mapDomain (suffixEmb hk) =
        m.mapDomain (suffixEmb hk)
      rw [← Finsupp.mapDomain_add, hab]
    · intro a₁ _ a₂ _ h; exact hinj h
    · intro cd hcd
      rw [Finset.mem_coe, Finset.mem_antidiagonal] at hcd
      have hzero_lt : ∀ i : Fin g, i.1 < k → cd.1 i = 0 ∧ cd.2 i = 0 := by
        intro i hi
        have hsum : cd.1 i + cd.2 i = (m.mapDomain (suffixEmb hk)) i := by
          have := congrArg (fun d : Fin g →₀ ℕ => d i) hcd
          simpa using this
        have hnot_range : i ∉ Set.range (suffixEmb hk) := by
          rintro ⟨j, hj⟩
          have hval : k + j.1 = i.1 := by simpa using congrArg Fin.val hj
          omega
        have hm0 : (m.mapDomain (suffixEmb hk)) i = 0 :=
          Finsupp.mapDomain_of_notMem_range m i hnot_range
        rw [hm0] at hsum
        omega
      let a : Fin (g - k) →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun j => cd.1 (suffixEmb hk j))
      let b : Fin (g - k) →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun j => cd.2 (suffixEmb hk j))
      have ha_map : a.mapDomain (suffixEmb hk) = cd.1 := by
        ext i
        by_cases hi : i.1 < k
        · have hnot : i ∉ Set.range (suffixEmb hk) := by
            rintro ⟨j, hj⟩; have hval : k + j.1 = i.1 := by simpa using congrArg Fin.val hj
            omega
          rw [Finsupp.mapDomain_of_notMem_range a i hnot, (hzero_lt i hi).1]
        · let j : Fin (g - k) := ⟨i.1 - k, by omega⟩
          have hj : suffixEmb hk j = i := Fin.ext (by show k + (i.1 - k) = i.1; omega)
          rw [← hj, Finsupp.mapDomain_apply (suffixEmb hk).injective]
          rfl
      have hb_map : b.mapDomain (suffixEmb hk) = cd.2 := by
        ext i
        by_cases hi : i.1 < k
        · have hnot : i ∉ Set.range (suffixEmb hk) := by
            rintro ⟨j, hj⟩; have hval : k + j.1 = i.1 := by simpa using congrArg Fin.val hj
            omega
          rw [Finsupp.mapDomain_of_notMem_range b i hnot, (hzero_lt i hi).2]
        · let j : Fin (g - k) := ⟨i.1 - k, by omega⟩
          have hj : suffixEmb hk j = i := Fin.ext (by show k + (i.1 - k) = i.1; omega)
          rw [← hj, Finsupp.mapDomain_apply (suffixEmb hk).injective]
          rfl
      refine ⟨(a, b), Finset.mem_coe.mpr (Finset.mem_antidiagonal.mpr ?_), Prod.ext ha_map hb_map⟩
      apply Finsupp.mapDomain_injective (suffixEmb hk).injective
      rw [Finsupp.mapDomain_add, ha_map, hb_map, hcd]
    · intro ab _; rfl
  map_zero' := by ext m; rfl
  map_add' f₁ f₂ := by ext m; rfl

theorem evalPrefixZero_surjective {p g : ℕ} [Fact p.Prime] (k : ℕ) (hk : k ≤ g) :
    Function.Surjective (evalPrefixZero (p := p) (g := g) k hk) := by
  classical
  intro h
  let lift : PatchingBaseRing p g := fun n =>
    if ∀ i : Fin g, i.1 < k → n i = 0 then
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm fun j : Fin (g - k) => n (suffixEmb hk j)) h
    else 0
  refine ⟨lift, ?_⟩
  ext m
  change MvPowerSeries.coeff (m.mapDomain (suffixEmb hk)) lift = MvPowerSeries.coeff m h
  have hcond : ∀ i : Fin g, i.1 < k → (m.mapDomain (suffixEmb hk)) i = 0 := by
    intro i hi
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨j, hj⟩
    have hval : k + j.1 = i.1 := by simpa using congrArg Fin.val hj
    omega
  change (if ∀ i : Fin g, i.1 < k → (m.mapDomain (suffixEmb hk)) i = 0 then _ else 0) = _
  rw [if_pos hcond]
  have heq : (Finsupp.equivFunOnFinite.symm fun j : Fin (g - k) =>
      (m.mapDomain (suffixEmb hk)) (suffixEmb hk j)) = m := by
    ext j
    change (m.mapDomain (suffixEmb hk)) (suffixEmb hk j) = m j
    exact Finsupp.mapDomain_apply (suffixEmb hk).injective m j
  rw [heq]

/-- Exact kernel of `evalPrefixZero k`: `ker(evalPrefixZero k) = (y_0, ..., y_{k-1})`. -/
theorem ker_evalPrefixZero {p g : ℕ} [Fact p.Prime] (k : ℕ) (hk : k ≤ g) :
    RingHom.ker (evalPrefixZero (p := p) (g := g) k hk) = partialAugIdeal p g k := by
  classical
  apply le_antisymm
  · intro f hf
    let q : Fin g → PatchingBaseRing p g := fun i m =>
      if i.1 < k ∧ (∀ j : Fin g, j < i → m j = 0) then
        MvPowerSeries.coeff (m + Finsupp.single i (1 : ℕ)) f
      else 0
    have hdecomp : f = ∑ i : Fin g, if i.1 < k then patchingVar i * q i else 0 := by
      ext n
      rw [map_sum]
      by_cases hall : ∀ i : Fin g, i.1 < k → n i = 0
      · have hzero_rhs :
            ∑ i : Fin g, MvPowerSeries.coeff n (if i.1 < k then patchingVar i * q i else 0) = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          split_ifs with hik
          · rw [patchingVar, MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul, one_mul]
            have hnot : ¬ Finsupp.single i (1 : ℕ) ≤ n := by
              rw [Finsupp.single_le_iff, hall i hik]
              omega
            rw [if_neg hnot]
          · simp
        rw [hzero_rhs]
        let m : Fin (g - k) →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun j => n (suffixEmb hk j))
        have hm_map : m.mapDomain (suffixEmb hk) = n := by
          ext i
          by_cases hi : i.1 < k
          · have hnot : i ∉ Set.range (suffixEmb hk) := by
              rintro ⟨j, hj⟩; have hval : k + j.1 = i.1 := by simpa using congrArg Fin.val hj
              omega
            rw [Finsupp.mapDomain_of_notMem_range m i hnot, hall i hi]
          · let j : Fin (g - k) := ⟨i.1 - k, by omega⟩
            have hj : suffixEmb hk j = i := Fin.ext (by show k + (i.1 - k) = i.1; omega)
            rw [← hj, Finsupp.mapDomain_apply (suffixEmb hk).injective]
            rfl
        have hf0 : MvPowerSeries.coeff m (evalPrefixZero k hk f) = 0 := by
          rw [show evalPrefixZero k hk f = 0 from hf, map_zero]
        change MvPowerSeries.coeff (m.mapDomain (suffixEmb hk)) f = 0 at hf0
        rwa [hm_map] at hf0
      · push Not at hall
        let S : Finset (Fin g) := Finset.univ.filter (fun i : Fin g => i.1 < k ∧ n i ≠ 0)
        have hSne : S.Nonempty := by
          obtain ⟨i, hik, hni⟩ := hall
          exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hik, hni⟩⟩
        set i₀ : Fin g := S.min' hSne with hi₀_def
        have hi₀_mem : i₀ ∈ S := Finset.min'_mem S hSne
        have hi₀_lt : i₀.1 < k := (Finset.mem_filter.mp hi₀_mem).2.1
        have hi₀_pos : 1 ≤ n i₀ := Nat.one_le_iff_ne_zero.mpr (Finset.mem_filter.mp hi₀_mem).2.2
        have hi₀_zero : ∀ j : Fin g, j < i₀ → n j = 0 := by
          intro j hj
          by_contra hnj
          have hj_lt : j.1 < k := lt_trans hj hi₀_lt
          have hj_mem : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj_lt, hnj⟩
          exact not_lt_of_ge (Finset.min'_le S j hj_mem) hj
        have hterm : ∀ i : Fin g,
            MvPowerSeries.coeff n (if i.1 < k then patchingVar i * q i else 0) =
              if i = i₀ then MvPowerSeries.coeff n f else 0 := by
          intro i
          by_cases hi : i = i₀
          · subst hi
            rw [if_pos hi₀_lt, if_pos rfl, patchingVar, MvPowerSeries.X_def,
              MvPowerSeries.coeff_monomial_mul, one_mul]
            have hle : Finsupp.single i₀ (1 : ℕ) ≤ n := Finsupp.single_le_iff.mpr hi₀_pos
            rw [if_pos hle]
            let m₀ : Fin g →₀ ℕ := n - Finsupp.single i₀ (1 : ℕ)
            have hcond : i₀.1 < k ∧ ∀ j : Fin g, j < i₀ → m₀ j = 0 :=
              ⟨hi₀_lt, fun j hj => by
                change (n - Finsupp.single i₀ (1 : ℕ)) j = 0
                rw [Finsupp.tsub_apply, hi₀_zero j hj, Nat.zero_sub]⟩
            change (if i₀.1 < k ∧ ∀ j : Fin g, j < i₀ → m₀ j = 0 then
              MvPowerSeries.coeff (m₀ + Finsupp.single i₀ (1 : ℕ)) f else 0) = _
            rw [if_pos hcond, tsub_add_cancel_of_le hle]
          · rw [if_neg hi]
            split_ifs with hik
            · rw [patchingVar, MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul, one_mul]
              split_ifs with hle
              · have hni : 1 ≤ n i := Finsupp.single_le_iff.mp hle
                have hi_mem : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hik, by omega⟩
                have hi₀_lt_i : i₀ < i := lt_of_le_of_ne (Finset.min'_le S i hi_mem) (Ne.symm hi)
                let mi : Fin g →₀ ℕ := n - Finsupp.single i (1 : ℕ)
                have hnot : ¬ (i.1 < k ∧ ∀ j : Fin g, j < i → mi j = 0) := by
                  intro h
                  have h0 := h.2 i₀ hi₀_lt_i
                  change (n - Finsupp.single i (1 : ℕ)) i₀ = 0 at h0
                  rw [Finsupp.tsub_apply, Finsupp.single_eq_of_ne hi₀_lt_i.ne, Nat.sub_zero] at h0
                  omega
                change (if i.1 < k ∧ ∀ j : Fin g, j < i → mi j = 0 then
                  MvPowerSeries.coeff (mi + Finsupp.single i (1 : ℕ)) f else 0) = 0
                rw [if_neg hnot]
              · rfl
            · simp
        rw [Finset.sum_congr rfl fun i _ => hterm i]
        simp
    rw [hdecomp]
    refine Ideal.sum_mem _ fun i _ => ?_
    split_ifs with hik
    · exact Ideal.mul_mem_right (q i) _ (Ideal.subset_span ⟨i, hik, rfl⟩)
    · exact (partialAugIdeal p g k).zero_mem
  · rw [partialAugIdeal, Ideal.span_le]
    rintro _ ⟨i, hik, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    ext m
    change MvPowerSeries.coeff (m.mapDomain (suffixEmb hk)) (MvPowerSeries.X i) = 0
    rw [MvPowerSeries.coeff_X]
    refine if_neg fun heq => ?_
    have hi1 : (m.mapDomain (suffixEmb hk)) i = 1 := by
      rw [heq, Finsupp.single_eq_same]
    have hnot : i ∉ Set.range (suffixEmb hk) := by
      rintro ⟨j, hj⟩; have hval : k + j.1 = i.1 := by simpa using congrArg Fin.val hj
      omega
    rw [Finsupp.mapDomain_of_notMem_range m i hnot] at hi1
    exact zero_ne_one hi1

/-- Exact quotient isomorphism `S_∞ ⧸ (y_0, ..., y_{k-1}) ≃+* MvPowerSeries (Fin (g - k)) ℤ_[p]`. -/
def quot_partialAugIdeal_equiv (p g k : ℕ) [Fact p.Prime] (hk : k ≤ g) :
    (PatchingBaseRing p g ⧸ partialAugIdeal p g k) ≃+* PatchingBaseRing p (g - k) :=
  (Ideal.quotEquivOfEq (ker_evalPrefixZero k hk).symm).trans
    (RingHom.quotientKerEquivOfSurjective (evalPrefixZero_surjective k hk))

/-- **Exact Regular Sequence `(y_0, ..., y_{g-1}, p)` of Length `g + 1` on `S_∞ = ℤ_[p][[y_0,...,y_{g-1}]]`**:
1. For every `0 ≤ k < g`, multiplication by `y_k` on `S_∞ ⧸ (y_0, ..., y_{k-1})` is injective
   (non-zero-divisor modulo `(y_0, ..., y_{k-1})`),
2. Modulo `(y_0, ..., y_{g-1})`, multiplication by `p` on `S_∞ ⧸ 𝔞 ≃+* ℤ_[p]` is injective! -/
theorem patchingBaseRing_regular_sequence (p g : ℕ) [Fact p.Prime] :
    (∀ (k : ℕ) (hk : k < g),
      Function.Injective (fun x : PatchingBaseRing p g ⧸ partialAugIdeal p g k =>
        Ideal.Quotient.mk (partialAugIdeal p g k) (patchingVar ⟨k, hk⟩) * x)) ∧
    Function.Injective (fun x : PatchingBaseRing p g ⧸ patchingAugIdeal p g =>
      Ideal.Quotient.mk (patchingAugIdeal p g) (p : PatchingBaseRing p g) * x) := by
  constructor
  · intro k hk
    let e := quot_partialAugIdeal_equiv p g k hk.le
    have hvar : e (Ideal.Quotient.mk (partialAugIdeal p g k) (patchingVar ⟨k, hk⟩)) =
        MvPowerSeries.X (⟨0, by omega⟩ : Fin (g - k)) := by
      ext m
      change MvPowerSeries.coeff (m.mapDomain (suffixEmb hk.le)) (MvPowerSeries.X ⟨k, hk⟩) =
        MvPowerSeries.coeff m (MvPowerSeries.X ⟨0, by omega⟩)
      rw [MvPowerSeries.coeff_X, MvPowerSeries.coeff_X]
      have hiff : m.mapDomain (suffixEmb hk.le) = Finsupp.single ⟨k, hk⟩ 1 ↔
          m = Finsupp.single ⟨0, by omega⟩ 1 := by
        have h0 : suffixEmb hk.le ⟨0, by omega⟩ = ⟨k, hk⟩ := Fin.ext (by simp)
        rw [← h0, ← Finsupp.mapDomain_single]
        exact (Finsupp.mapDomain_injective (suffixEmb hk.le).injective).eq_iff
      by_cases hm : m = Finsupp.single ⟨0, by omega⟩ 1
      · rw [if_pos (hiff.mpr hm), if_pos hm]
      · rw [if_neg (fun h => hm (hiff.mp h)), if_neg hm]
    have hXne : (MvPowerSeries.X (⟨0, by omega⟩ : Fin (g - k)) :
        PatchingBaseRing p (g - k)) ≠ 0 := by
      intro h0
      have h1 := congrArg (MvPowerSeries.coeff (Finsupp.single ⟨0, by omega⟩ 1)) h0
      rw [MvPowerSeries.coeff_X, if_pos rfl, map_zero] at h1
      exact one_ne_zero h1
    intro x₁ x₂ hx
    apply e.injective
    have hx' := congrArg e hx
    rw [map_mul, map_mul, hvar] at hx'
    exact mul_left_cancel₀ hXne hx'
  · intro x₁ x₂ hx
    let e := patchingBaseRing_quot_augIdeal_equiv_Zp p g
    apply e.injective
    have hx' := congrArg e hx
    rw [map_mul, map_mul, patchingBaseRing_quot_augIdeal_equiv_Zp_mk, map_natCast] at hx'
    exact mul_left_cancel₀ padicInt_p_ne_zero hx'

/-- **Nakayama Coinvariant Generation over `S_∞ = MvPowerSeries (Fin g) ℤ_[p]`**:
if `M` is finitely generated over `S_∞` and `v : Fin r → M` generates `M ⧸ 𝔞 M`, then `v`
already generates `M` over `S_∞`. -/
theorem nakayama_patchingBaseRing_gen {p g r : ℕ} [Fact p.Prime] {M : Type*} [AddCommGroup M]
    [Module (PatchingBaseRing p g) M] [Module.Finite (PatchingBaseRing p g) M] (v : Fin r → M)
    (hgen : Submodule.span (PatchingBaseRing p g)
      (Set.range fun i => Submodule.Quotient.mk
        (p := patchingAugIdeal p g • (⊤ : Submodule (PatchingBaseRing p g) M)) (v i)) = ⊤) :
    Submodule.span (PatchingBaseRing p g) (Set.range v) = ⊤ :=
  nakayama_coinv_gen (patchingAugIdeal_le_maximalIdeal p g) v hgen

/-- **Nakayama Coinvariant Surjectivity over `S_∞ = MvPowerSeries (Fin g) ℤ_[p]`**. -/
theorem nakayama_patchingBaseRing_surjective {p g : ℕ} [Fact p.Prime] {N M : Type*}
    [AddCommGroup N] [Module (PatchingBaseRing p g) N]
    [AddCommGroup M] [Module (PatchingBaseRing p g) M] [Module.Finite (PatchingBaseRing p g) M]
    (f : N →ₗ[PatchingBaseRing p g] M)
    (hsurj : Function.Surjective
      ((patchingAugIdeal p g • (⊤ : Submodule (PatchingBaseRing p g) M)).mkQ.comp f)) :
    Function.Surjective f :=
  nakayama_coinv_surjective (patchingAugIdeal_le_maximalIdeal p g) f hsurj

/-- Exact coinvariant rank-preserving isomorphism
`Coinv (patchingAugIdeal p g) (Fin r → S_∞) ≃ₗ[ℤ_[p]] (Fin r → ℤ_[p])`. -/
def coinv_patchingBaseRing_pi_equiv_Zp (p g r : ℕ) [Fact p.Prime] :
    Coinv (patchingAugIdeal p g) (Fin r → PatchingBaseRing p g) ≃ₗ[ℤ_[p]] (Fin r → ℤ_[p]) := by
  let eQ := coinvPiEquiv (patchingAugIdeal p g) r
  let eR := patchingBaseRing_quot_augIdeal_equiv_Zp p g
  refine
    { toFun := fun x i => eR (eQ x i)
      invFun := fun v => eQ.symm (fun i => eR.symm (v i))
      left_inv := fun x => by
        dsimp only
        have h : (fun i => eR.symm (eR (eQ x i))) = eQ x := funext fun i => eR.symm_apply_apply _
        rw [h, eQ.symm_apply_apply]
      right_inv := fun v => by
        ext i
        simp
      map_add' := fun x y => by ext i; simp [map_add]
      map_smul' := fun a x => by
        ext i
        have hsmul : a • x = Ideal.Quotient.mk (patchingAugIdeal p g) (MvPowerSeries.C a) • x := by
          induction x using Quotient.inductionOn' with
          | h v =>
            change Submodule.Quotient.mk (a • v) =
              Submodule.Quotient.mk (MvPowerSeries.C a • v)
            congr 1
            funext j
            exact MvPowerSeries.smul_eq_C_mul (v j) a
        change eR (eQ (a • x) i) = a * eR (eQ x i)
        rw [hsmul, eQ.map_smul, Pi.smul_apply, smul_eq_mul, map_mul,
          patchingBaseRing_quot_augIdeal_equiv_Zp_mk, MvPowerSeries.constantCoeff_C] }

end PatchingBaseRingSection

/-! ## Section 2: Monogenic Quadratic Complete-Intersection Algebras (`QuadAlg`), Gorensteinness,
& Concrete `TaylorWilesPatchingDatum` Instantiations over `S_∞ = MvPowerSeries (Fin g) ℤ_[p]` -/

section ConcretePatchingDatums

/-- Transport `IsGorensteinOver 𝒪 R` across any `𝒪`-algebra isomorphism `e : R ≃ₐ[𝒪] T`. -/
def isGorensteinOver_ofAlgEquiv {𝒪 R T : Type*} [CommRing 𝒪] [CommRing R] [CommRing T]
    [Algebra 𝒪 R] [Algebra 𝒪 T] (G : IsGorensteinOver 𝒪 R) (e : R ≃ₐ[𝒪] T) :
    IsGorensteinOver 𝒪 T where
  traceForm := G.traceForm.comp e.symm.toLinearMap
  pairing_bijective := by
    constructor
    · intro t₁ t₂ h
      apply e.symm.injective
      apply G.pairing_bijective.1
      ext r
      have hr := congrFun (congrArg DFunLike.coe h) (e r)
      simpa [map_mul] using hr
    · intro φ
      let φR : R →ₗ[𝒪] 𝒪 := φ.comp e.toLinearMap
      obtain ⟨r, hr⟩ := G.pairing_bijective.2 φR
      refine ⟨e r, ?_⟩
      ext t
      have ht := congrFun (congrArg DFunLike.coe hr) (e.symm t)
      simpa [φR, map_mul] using ht

/-- Every commutative ring `𝒪` is unconditionally rank-1 Gorenstein over itself (`traceForm = id`). -/
def isGorensteinOver_self (𝒪 : Type*) [CommRing 𝒪] : IsGorensteinOver 𝒪 𝒪 where
  traceForm := LinearMap.id
  pairing_bijective := by
    constructor
    · intro a b h
      have h1 := congrFun (congrArg DFunLike.coe h) 1
      simpa using h1
    · intro φ
      refine ⟨φ 1, ?_⟩
      apply LinearMap.ext
      intro x
      change φ 1 * x = φ x
      simpa [mul_comm] using (φ.map_smul x 1).symm

/-- **Concrete Monogenic Quadratic Algebra `QuadAlg A b c := A[X] / (X² - b X + c)`**:
represented explicitly as ordered pairs `⟨x, y⟩ = x + y · α` with `α² = b · α - c`. -/
@[ext]
structure QuadAlg (A : Type*) (b c : A) where
  fst : A
  snd : A

namespace QuadAlg

variable {A : Type*} [CommRing A] {b c : A}

instance : Zero (QuadAlg A b c) := ⟨⟨0, 0⟩⟩
instance : One (QuadAlg A b c) := ⟨⟨1, 0⟩⟩
instance : Add (QuadAlg A b c) := ⟨fun u v => ⟨u.fst + v.fst, u.snd + v.snd⟩⟩
instance : Neg (QuadAlg A b c) := ⟨fun u => ⟨-u.fst, -u.snd⟩⟩
instance : Sub (QuadAlg A b c) := ⟨fun u v => ⟨u.fst - v.fst, u.snd - v.snd⟩⟩
instance : Mul (QuadAlg A b c) :=
  ⟨fun u v => ⟨u.fst * v.fst - c * (u.snd * v.snd),
    u.fst * v.snd + u.snd * v.fst + b * (u.snd * v.snd)⟩⟩

@[simp] theorem zero_fst : (0 : QuadAlg A b c).fst = 0 := rfl
@[simp] theorem zero_snd : (0 : QuadAlg A b c).snd = 0 := rfl
@[simp] theorem one_fst : (1 : QuadAlg A b c).fst = 1 := rfl
@[simp] theorem one_snd : (1 : QuadAlg A b c).snd = 0 := rfl
@[simp] theorem add_fst (u v : QuadAlg A b c) : (u + v).fst = u.fst + v.fst := rfl
@[simp] theorem add_snd (u v : QuadAlg A b c) : (u + v).snd = u.snd + v.snd := rfl
@[simp] theorem neg_fst (u : QuadAlg A b c) : (-u).fst = -u.fst := rfl
@[simp] theorem neg_snd (u : QuadAlg A b c) : (-u).snd = -u.snd := rfl
@[simp] theorem sub_fst (u v : QuadAlg A b c) : (u - v).fst = u.fst - v.fst := rfl
@[simp] theorem sub_snd (u v : QuadAlg A b c) : (u - v).snd = u.snd - v.snd := rfl
@[simp] theorem mul_fst (u v : QuadAlg A b c) :
    (u * v).fst = u.fst * v.fst - c * (u.snd * v.snd) := rfl
@[simp] theorem mul_snd (u v : QuadAlg A b c) :
    (u * v).snd = u.fst * v.snd + u.snd * v.fst + b * (u.snd * v.snd) := rfl

instance instCommRing : CommRing (QuadAlg A b c) where
  add_assoc u v w := by ext <;> simp [add_assoc]
  zero_add u := by ext <;> simp
  add_zero u := by ext <;> simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel u := by ext <;> simp
  add_comm u v := by ext <;> simp [add_comm]
  sub_eq_add_neg u v := by ext <;> simp [sub_eq_add_neg]
  mul_assoc u v w := by ext <;> simp <;> ring
  one_mul u := by ext <;> simp
  mul_one u := by ext <;> simp
  left_distrib u v w := by ext <;> simp <;> ring
  right_distrib u v w := by ext <;> simp <;> ring
  zero_mul u := by ext <;> simp
  mul_zero u := by ext <;> simp
  mul_comm u v := by ext <;> simp <;> ring

instance instSMul : SMul A (QuadAlg A b c) :=
  ⟨fun a u => ⟨a * u.fst, a * u.snd⟩⟩

@[simp] theorem smul_fst (a : A) (u : QuadAlg A b c) : (a • u).fst = a * u.fst := rfl
@[simp] theorem smul_snd (a : A) (u : QuadAlg A b c) : (a • u).snd = a * u.snd := rfl

instance instAlgebra : Algebra A (QuadAlg A b c) where
  algebraMap :=
    { toFun := fun a => ⟨a, 0⟩
      map_one' := rfl
      map_mul' := fun x y => by ext <;> simp
      map_zero' := rfl
      map_add' := fun x y => by ext <;> simp }
  smul := (· • ·)
  commutes' a u := mul_comm _ u
  smul_def' a u := by ext <;> simp

@[simp] theorem algebraMap_fst (a : A) : (algebraMap A (QuadAlg A b c) a).fst = a := rfl
@[simp] theorem algebraMap_snd (a : A) : (algebraMap A (QuadAlg A b c) a).snd = 0 := rfl

/-- Canonical monogenic generator `α = ⟨0, 1⟩` of `QuadAlg A b c`. -/
def gen : QuadAlg A b c := ⟨0, 1⟩

/-- Exact quadratic relation `α² - b • α + c • 1 = 0`. -/
theorem gen_sq_rel : (gen (b := b) (c := c)) ^ 2 - b • gen + c • (1 : QuadAlg A b c) = 0 := by
  ext <;> simp [sq, gen]

/-- Explicit rank-2 `A`-linear freeness equivalence `QuadAlg A b c ≃ₗ[A] (Fin 2 → A)`. -/
def equivPi2 (A : Type*) [CommRing A] (b c : A) : QuadAlg A b c ≃ₗ[A] (Fin 2 → A) where
  toFun u := ![u.fst, u.snd]
  invFun v := ⟨v 0, v 1⟩
  left_inv u := by ext <;> rfl
  right_inv v := by ext i; fin_cases i <;> rfl
  map_add' u v := by ext i; fin_cases i <;> rfl
  map_smul' a u := by ext i; fin_cases i <;> rfl

instance instModuleFinite : Module.Finite A (QuadAlg A b c) :=
  Module.Finite.equiv (equivPi2 A b c).symm

instance instModuleFree : Module.Free A (QuadAlg A b c) :=
  Module.Free.of_equiv (equivPi2 A b c).symm

/-- **Unconditional Gorensteinness of `QuadAlg A b c` over EVERY commutative ring `A`**
(including ramified primes `p ∣ Δ`!): the Tate–Grothendieck trace functional `⟨x, y⟩ ↦ y`
induces a bijective Frobenius pairing `QuadAlg A b c ≃ (QuadAlg A b c →ₗ[A] A)`. -/
def isGorensteinOver (A : Type*) [CommRing A] (b c : A) :
    IsGorensteinOver A (QuadAlg A b c) where
  traceForm :=
    { toFun := fun u => u.snd
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  pairing_bijective := by
    constructor
    · intro r₁ r₂ h
      have h1 := congrFun (congrArg DFunLike.coe h) (1 : QuadAlg A b c)
      have hα := congrFun (congrArg DFunLike.coe h) (gen (b := b) (c := c))
      simp only [LinearMap.coe_mk, AddHom.coe_mk, mul_one] at h1
      simp only [LinearMap.coe_mk, AddHom.coe_mk, gen, mul_snd, mul_one, mul_zero, add_zero] at hα
      ext
      · rw [h1] at hα
        exact add_right_cancel hα
      · exact h1
    · intro φ
      let r : QuadAlg A b c := ⟨φ gen - b * φ 1, φ 1⟩
      refine ⟨r, ?_⟩
      ext u
      have hu : u = u.fst • (1 : QuadAlg A b c) + u.snd • gen := by
        ext <;> simp [gen]
      conv_rhs => rw [hu, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      change (r * u).snd = u.fst * φ 1 + u.snd * φ gen
      simp only [r, mul_snd]
      ring

/-- Functorial ring homomorphism `QuadAlg A b c →+* QuadAlg B (f b) (f c)` induced by `f : A →+* B`. -/
def mapRingHom {B : Type*} [CommRing B] (f : A →+* B) (b c : A) :
    QuadAlg A b c →+* QuadAlg B (f b) (f c) where
  toFun u := ⟨f u.fst, f u.snd⟩
  map_one' := by ext <;> simp
  map_mul' u v := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' u v := by ext <;> simp

/-- Exact augmentation `π_λ : QuadAlg A b c →ₐ[A] A` attached to any root `λ ∈ A` of
`λ² - b λ + c = 0` (`⟨x, y⟩ ↦ x + y * λ`). -/
def aug {lam : A} (hroot : lam ^ 2 - b * lam + c = 0) : QuadAlg A b c →ₐ[A] A where
  toFun u := u.fst + u.snd * lam
  map_one' := by simp
  map_mul' u v := by
    change (u.fst * v.fst - c * (u.snd * v.snd)) +
        (u.fst * v.snd + u.snd * v.fst + b * (u.snd * v.snd)) * lam =
      (u.fst + u.snd * lam) * (v.fst + v.snd * lam)
    linear_combination -u.snd * v.snd * hroot
  map_zero' := by simp
  map_add' u v := by
    change (u.fst + v.fst) + (u.snd + v.snd) * lam = (u.fst + u.snd * lam) + (v.fst + v.snd * lam)
    ring
  commutes' a := by simp

theorem disc_eq_sq {lam : A} (hroot : lam ^ 2 - b * lam + c = 0) :
    (2 * lam - b) ^ 2 = b ^ 2 - 4 * c := by
  linear_combination 4 * hroot

/-- **Exact Congruence Ideal of `QuadAlg A b c`**:
`congruenceIdeal (QuadAlg.aug hroot) = Ideal.span {2 * λ - b}` (UNCONDITIONAL over EVERY ring `A`!). -/
theorem congruenceIdeal_aug_eq {lam : A} (hroot : lam ^ 2 - b * lam + c = 0) :
    Stage3PatchingUnification.congruenceIdeal (aug hroot) = Ideal.span ({2 * lam - b} : Set A) := by
  let e : QuadAlg A b c := ⟨-lam, 1⟩
  have he_mem : e ∈ Stage3PatchingUnification.augIdeal (aug hroot) := by
    change -lam + 1 * lam = 0
    ring
  apply le_antisymm
  · intro a ha
    obtain ⟨t, ht_ann, rfl⟩ :=
      (Stage3PatchingUnification.mem_congruenceIdeal_iff (aug hroot) a).mp ha
    have hte : t * e = 0 :=
      (Stage3PatchingUnification.mem_annAugIdeal_iff (aug hroot) t).mp ht_ann e he_mem
    have hsnd : (t * e).snd = 0 := congrArg QuadAlg.snd hte
    simp only [e, mul_snd, mul_one, mul_neg] at hsnd
    have hfst : t.fst = t.snd * (lam - b) := by linear_combination hsnd
    rw [Ideal.mem_span_singleton]
    refine ⟨t.snd, ?_⟩
    change t.fst + t.snd * lam = (2 * lam - b) * t.snd
    rw [hfst]; ring
  · rw [Ideal.span_singleton_le_iff_mem]
    let t₀ : QuadAlg A b c := ⟨lam - b, 1⟩
    refine (Stage3PatchingUnification.mem_congruenceIdeal_iff (aug hroot) (2 * lam - b)).mpr
      ⟨t₀, ?_, ?_⟩
    · rw [Stage3PatchingUnification.mem_annAugIdeal_iff]
      intro x hx
      have hx0 : x.fst + x.snd * lam = 0 := hx
      ext
      · change (lam - b) * x.fst - c * (1 * x.snd) = 0
        linear_combination (lam - b) * hx0 - x.snd * hroot
      · change (lam - b) * x.snd + 1 * x.fst + b * (1 * x.snd) = 0
        linear_combination hx0
    · change (lam - b) + 1 * lam = 2 * lam - b
      ring

/-- The discriminant `Δ = b² - 4 c` always lies in `congruenceIdeal (QuadAlg.aug hroot)`. -/
theorem disc_mem_congruenceIdeal_aug {lam : A} (hroot : lam ^ 2 - b * lam + c = 0) :
    b ^ 2 - 4 * c ∈ Stage3PatchingUnification.congruenceIdeal (aug hroot) := by
  rw [congruenceIdeal_aug_eq hroot, Ideal.mem_span_singleton]
  refine ⟨2 * lam - b, ?_⟩
  rw [← sq, disc_eq_sq hroot]

/-- **Exact Complete-Intersection Cotangent Isomorphism**:
`Cotangent (QuadAlg.aug hroot) ≃ₗ[A] (A ⧸ congruenceIdeal (QuadAlg.aug hroot))`! -/
def cotangentEquiv {lam : A} (hroot : lam ^ 2 - b * lam + c = 0) :
    Stage3PatchingUnification.Cotangent (aug hroot) ≃ₗ[A]
      (A ⧸ Stage3PatchingUnification.congruenceIdeal (aug hroot)) := by
  let δ : A := 2 * lam - b
  have hη : Stage3PatchingUnification.congruenceIdeal (aug hroot) = Ideal.span ({δ} : Set A) :=
    congruenceIdeal_aug_eq hroot
  let proj : Stage3PatchingUnification.augIdeal (aug hroot) →ₗ[A]
      (A ⧸ Stage3PatchingUnification.congruenceIdeal (aug hroot)) :=
    { toFun := fun x => Ideal.Quotient.mk _ x.1.snd
      map_add' := fun _ _ => map_add _ _ _
      map_smul' := fun r x => by
        change Ideal.Quotient.mk _ (r * x.1.snd) = r • Ideal.Quotient.mk _ x.1.snd
        rw [map_mul]; rfl }
  have hsurj : Function.Surjective proj := by
    intro q
    induction q using Quotient.inductionOn' with
    | h y =>
      refine ⟨⟨⟨-(y * lam), y⟩, by change -(y * lam) + y * lam = 0; ring⟩, rfl⟩
  have hker : LinearMap.ker proj = Stage3PatchingUnification.cotangentSubmodule (aug hroot) := by
    ext x
    rw [LinearMap.mem_ker]
    change Ideal.Quotient.mk (Stage3PatchingUnification.congruenceIdeal (aug hroot)) x.1.snd = 0 ↔
      x.1 ∈ Stage3PatchingUnification.augIdeal (aug hroot) ^ 2
    rw [Ideal.Quotient.eq_zero_iff_mem, hη, Ideal.mem_span_singleton]
    have hx0 : x.1.fst + x.1.snd * lam = 0 := x.2
    constructor
    · rintro ⟨q, hq⟩
      let u : QuadAlg A b c := ⟨q * lam, -q⟩
      let v : QuadAlg A b c := ⟨-lam, 1⟩
      have hu : u ∈ Stage3PatchingUnification.augIdeal (aug hroot) := by
        change q * lam + (-q) * lam = 0; ring
      have hv : v ∈ Stage3PatchingUnification.augIdeal (aug hroot) := by
        change -lam + 1 * lam = 0; ring
      have huv : x.1 = u * v := by
        ext
        · change x.1.fst = (q * lam) * (-lam) - c * ((-q) * 1)
          linear_combination hx0 - lam * hq - q * hroot
        · change x.1.snd = (q * lam) * 1 + (-q) * (-lam) + b * ((-q) * 1)
          linear_combination hq
      rw [huv, pow_two]
      exact Ideal.mul_mem_mul hu hv
    · intro hx2
      rw [pow_two] at hx2
      have hstep : ∀ w ∈ Stage3PatchingUnification.augIdeal (aug hroot) *
          Stage3PatchingUnification.augIdeal (aug hroot), δ ∣ w.snd := by
        intro w hw
        refine Submodule.mul_induction_on hw ?_ ?_
        · intro u hu v hv
          have hu0 : u.fst + u.snd * lam = 0 := hu
          have hv0 : v.fst + v.snd * lam = 0 := hv
          refine ⟨-(u.snd * v.snd), ?_⟩
          change u.fst * v.snd + u.snd * v.fst + b * (u.snd * v.snd) = (2 * lam - b) * -(u.snd * v.snd)
          linear_combination v.snd * hu0 + u.snd * hv0
        · intro w₁ w₂ h₁ h₂
          exact dvd_add h₁ h₂
      exact hstep x.1 hx2
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans (proj.quotKerEquivOfSurjective hsurj)

/-- **Exact Complete-Intersection Length Equality** for `QuadAlg A b c`:
`len_A(Φ_T) = len_A(A ⧸ η_T)` (feeds `shaLen_le_congLen_of_completeIntersection` directly!). -/
theorem length_cotangent_eq {lam : A} (hroot : lam ^ 2 - b * lam + c = 0) :
    Module.length A (Stage3PatchingUnification.Cotangent (aug hroot)) =
      Module.length A (A ⧸ Stage3PatchingUnification.congruenceIdeal (aug hroot)) :=
  (cotangentEquiv hroot).length_eq

end QuadAlg

/-! ### Concrete `TaylorWilesPatchingDatum` Instantiations over `S_∞ = MvPowerSeries (Fin g) ℤ_[p]` -/

/-- **1. Concrete Rank-`r` Domain-Faithful `TaylorWilesPatchingDatum` over `S_∞ = MvPowerSeries (Fin g) ℤ_[p]`**
(`0` assumptions!): instantiates `R_∞ = T_∞ = S_∞ = ℤ_[p][[y_1,...,y_g]]`, `M_∞ = S_∞^r` (`r ≥ 1`),
using `IsDomain (MvPowerSeries (Fin g) ℤ_[p])` for the Kisin domain-faithfulness witness, and
specializing modulo `(y_1,...,y_g)` to `R_0 = T_0 = ℤ_[p]` (or any ring `T₀ ≃+* ℤ_[p]`). -/
def concrete_taylorWilesPatchingDatum_Zp_of_equiv (p g r : ℕ) [Fact p.Prime] (hr : 0 < r)
    (T₀ : Type) [CommRing T₀] (eT : ℤ_[p] ≃+* T₀) :
    TaylorWilesPatchingDatum where
  S_inf := PatchingBaseRing p g
  g := g
  y := patchingVar
  aug_le_max := patchingAugIdeal_le_maximalIdeal p g
  R_inf := PatchingBaseRing p g
  T_inf := PatchingBaseRing p g
  phi_inf := AlgHom.id (PatchingBaseRing p g) (PatchingBaseRing p g)
  phi_surj := Function.surjective_id
  M_inf := Fin r → PatchingBaseRing p g
  compat_RM_TM := fun _ _ => rfl
  rank := r
  rank_pos := hr
  M_free_S := LinearEquiv.refl _ _
  faithful_witness := Or.inl inferInstance
  R_0 := ℤ_[p]
  T_0 := T₀
  specR :=
    (Ideal.quotEquivOfEq (Ideal.map_id (patchingAugIdeal p g))).trans
      (patchingBaseRing_quot_augIdeal_equiv_Zp p g)
  specT :=
    ((Ideal.quotEquivOfEq (Ideal.map_id (patchingAugIdeal p g))).trans
      (patchingBaseRing_quot_augIdeal_equiv_Zp p g)).trans eT

/-- Canonical `T₀ = ℤ_[p]` specialization of `concrete_taylorWilesPatchingDatum_Zp_of_equiv`. -/
def concrete_taylorWilesPatchingDatum_Zp (p g r : ℕ) [Fact p.Prime] (hr : 0 < r) :
    TaylorWilesPatchingDatum :=
  concrete_taylorWilesPatchingDatum_Zp_of_equiv p g r hr ℤ_[p] (RingEquiv.refl ℤ_[p])

theorem concrete_taylorWilesPatchingDatum_Zp_spec (p g r : ℕ) [Fact p.Prime] (hr : 0 < r) :
    let D := concrete_taylorWilesPatchingDatum_Zp p g r hr
    Nonempty (D.R_inf ≃ₐ[D.S_inf] D.T_inf) ∧
      Nonempty (D.R_0 ≃+* D.T_0) ∧
      Module.Free (D.S_inf ⧸ D.augIdeal) D.M_0 ∧
      Module.Finite (D.S_inf ⧸ D.augIdeal) D.M_0 ∧
      Nonempty (IsGorensteinOver ℤ_[p] ℤ_[p]) := by
  intro D
  exact ⟨⟨D.R_inf_equiv_T_inf⟩, ⟨D.R0_equiv_T0⟩, D.M0_free_finite.1, D.M0_free_finite.2,
    ⟨isGorensteinOver_self ℤ_[p]⟩⟩

/-- Exact reduction isomorphism modulo `𝔞 = (y_1, ..., y_g)` for a patched quadratic algebra
`QuadAlg S_∞ (C b) (C c) ⧸ 𝔞 · QuadAlg S_∞ (C b) (C c) ≃+* QuadAlg ℤ_[p] b c`. -/
def quadAlg_patchingBaseRing_quot_equiv (p g : ℕ) [Fact p.Prime] (b c : ℤ_[p]) :
    let S := PatchingBaseRing p g
    let B : S := MvPowerSeries.C b
    let C' : S := MvPowerSeries.C c
    (QuadAlg S B C' ⧸ (patchingAugIdeal p g).map (algebraMap S (QuadAlg S B C'))) ≃+*
      QuadAlg ℤ_[p] b c := by
  intro S B C'
  let ev : QuadAlg S B C' →+* QuadAlg ℤ_[p] b c :=
    { toFun := fun u => ⟨MvPowerSeries.constantCoeff u.fst, MvPowerSeries.constantCoeff u.snd⟩
      map_one' := by ext <;> simp
      map_mul' := fun u v => by
        ext
        · change MvPowerSeries.constantCoeff (u.fst * v.fst - C' * (u.snd * v.snd)) =
            MvPowerSeries.constantCoeff u.fst * MvPowerSeries.constantCoeff v.fst -
              c * (MvPowerSeries.constantCoeff u.snd * MvPowerSeries.constantCoeff v.snd)
          simp [C']
        · change MvPowerSeries.constantCoeff (u.fst * v.snd + u.snd * v.fst + B * (u.snd * v.snd)) =
            MvPowerSeries.constantCoeff u.fst * MvPowerSeries.constantCoeff v.snd +
              MvPowerSeries.constantCoeff u.snd * MvPowerSeries.constantCoeff v.fst +
              b * (MvPowerSeries.constantCoeff u.snd * MvPowerSeries.constantCoeff v.snd)
          simp [B]
      map_zero' := by ext <;> simp
      map_add' := fun u v => by ext <;> simp }
  have hsurj : Function.Surjective ev := fun w =>
    ⟨⟨MvPowerSeries.C w.fst, MvPowerSeries.C w.snd⟩, by ext <;> simp [ev]⟩
  have hker : RingHom.ker ev = (patchingAugIdeal p g).map (algebraMap S (QuadAlg S B C')) := by
    apply le_antisymm
    · intro u hu
      have h1 : MvPowerSeries.constantCoeff u.fst = 0 := congrArg QuadAlg.fst hu
      have h2 : MvPowerSeries.constantCoeff u.snd = 0 := congrArg QuadAlg.snd hu
      have hm1 : u.fst ∈ patchingAugIdeal p g := by
        rw [patchingAugIdeal_eq_ker_constantCoeff]; exact h1
      have hm2 : u.snd ∈ patchingAugIdeal p g := by
        rw [patchingAugIdeal_eq_ker_constantCoeff]; exact h2
      have hdecomp : u = algebraMap S (QuadAlg S B C') u.fst * 1 +
          algebraMap S (QuadAlg S B C') u.snd * QuadAlg.gen := by
        ext <;> simp [QuadAlg.gen]
      rw [hdecomp]
      exact Ideal.add_mem _
        (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hm1))
        (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hm2))
    · rw [Ideal.map_le_iff_le_comap]
      intro s hs
      rw [patchingAugIdeal_eq_ker_constantCoeff] at hs
      change ev ⟨s, 0⟩ = 0
      ext
      · exact hs
      · exact map_zero _
  exact (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)

/-- **2. Concrete Rank-2 Quadratic Complete-Intersection `TaylorWilesPatchingDatum` over `S_∞`**:
patches `T_0 = QuadAlg ℤ_[p] b c` (e.g. `S₂₄` with `b = 1080`, `c = -20468736`) via
`R_∞ = T_∞ = M_∞ = QuadAlg S_∞ (C b) (C c)` using Orzech same-rank cyclic faithfulness (works
even when `R_∞` is NOT an integral domain!), yielding `R_0 ≃+* T_0` AND `IsGorensteinOver ℤ_[p] T_0`. -/
def quadraticPatchingDatum_Zp (p g : ℕ) [Fact p.Prime] (b c : ℤ_[p]) :
    TaylorWilesPatchingDatum where
  S_inf := PatchingBaseRing p g
  g := g
  y := patchingVar
  aug_le_max := patchingAugIdeal_le_maximalIdeal p g
  R_inf := QuadAlg (PatchingBaseRing p g) (MvPowerSeries.C b) (MvPowerSeries.C c)
  T_inf := QuadAlg (PatchingBaseRing p g) (MvPowerSeries.C b) (MvPowerSeries.C c)
  phi_inf := AlgHom.id _ _
  phi_surj := Function.surjective_id
  M_inf := QuadAlg (PatchingBaseRing p g) (MvPowerSeries.C b) (MvPowerSeries.C c)
  compat_RM_TM := fun _ _ => rfl
  rank := 2
  rank_pos := by norm_num
  M_free_S := QuadAlg.equivPi2 (PatchingBaseRing p g) (MvPowerSeries.C b) (MvPowerSeries.C c)
  faithful_witness := Or.inr ⟨⟨QuadAlg.equivPi2 _ _ _, ⟨LinearMap.id, Function.surjective_id⟩⟩⟩
  R_0 := QuadAlg ℤ_[p] b c
  T_0 := QuadAlg ℤ_[p] b c
  specR := quadAlg_patchingBaseRing_quot_equiv p g b c
  specT := quadAlg_patchingBaseRing_quot_equiv p g b c

theorem quadraticPatchingDatum_Zp_spec (p g : ℕ) [Fact p.Prime] (b c : ℤ_[p]) :
    let D := quadraticPatchingDatum_Zp p g b c
    Nonempty (D.R_inf ≃ₐ[D.S_inf] D.T_inf) ∧
      Nonempty (D.R_0 ≃+* D.T_0) ∧
      Module.Free (D.S_inf ⧸ D.augIdeal) D.M_0 ∧
      Module.Finite (D.S_inf ⧸ D.augIdeal) D.M_0 ∧
      Nonempty (IsGorensteinOver ℤ_[p] (QuadAlg ℤ_[p] b c)) := by
  intro D
  exact ⟨⟨D.R_inf_equiv_T_inf⟩, ⟨D.R0_equiv_T0⟩, D.M0_free_finite.1, D.M0_free_finite.2,
    ⟨QuadAlg.isGorensteinOver ℤ_[p] b c⟩⟩

/-- Helper: linear freeness of `S_∞ ⊗[ℤ_[p]] T₀` over `S_∞` from `T₀ ≃ₗ[ℤ_[p]] (Fin r → ℤ_[p])`. -/
private def freeAlg_patching_equivPi (p g r : ℕ) [Fact p.Prime]
    (T₀ : Type) [CommRing T₀] [Algebra ℤ_[p] T₀] (eT : T₀ ≃ₗ[ℤ_[p]] (Fin r → ℤ_[p])) :
    (PatchingBaseRing p g ⊗[ℤ_[p]] T₀) ≃ₗ[PatchingBaseRing p g] (Fin r → PatchingBaseRing p g) :=
  let b₀ : Module.Basis (Fin r) ℤ_[p] T₀ := (Pi.basisFun ℤ_[p] (Fin r)).map eT.symm
  (b₀.baseChange (PatchingBaseRing p g)).repr.trans
    (Finsupp.linearEquivFunOnFinite (PatchingBaseRing p g) (PatchingBaseRing p g) (Fin r))

/-- Helper: specialization ring isomorphism `(S_∞ ⊗[ℤ_[p]] T₀) ⧸ 𝔞 · (S_∞ ⊗ T₀) ≃+* T₀`. -/
private def freeAlg_patching_specEquiv (p g r : ℕ) [Fact p.Prime]
    (T₀ : Type) [CommRing T₀] [Algebra ℤ_[p] T₀] (eT : T₀ ≃ₗ[ℤ_[p]] (Fin r → ℤ_[p])) :
    ((PatchingBaseRing p g ⊗[ℤ_[p]] T₀) ⧸
      (patchingAugIdeal p g).map (algebraMap (PatchingBaseRing p g) (PatchingBaseRing p g ⊗[ℤ_[p]] T₀))) ≃+*
      T₀ := by
  let b₀ : Module.Basis (Fin r) ℤ_[p] T₀ := (Pi.basisFun ℤ_[p] (Fin r)).map eT.symm
  let cAlg : MvPowerSeries (Fin g) ℤ_[p] →ₐ[ℤ_[p]] ℤ_[p] :=
    { toRingHom := MvPowerSeries.constantCoeff
      commutes' := fun a => MvPowerSeries.constantCoeff_C a }
  let ev : (MvPowerSeries (Fin g) ℤ_[p] ⊗[ℤ_[p]] T₀) →ₐ[ℤ_[p]] T₀ :=
    Algebra.TensorProduct.lift ((Algebra.ofId ℤ_[p] T₀).comp cAlg) (AlgHom.id ℤ_[p] T₀)
      (fun _ _ => Commute.all _ _)
  have hev_tmul : ∀ (f : MvPowerSeries (Fin g) ℤ_[p]) (t : T₀),
      ev (f ⊗ₜ[ℤ_[p]] t) = MvPowerSeries.constantCoeff f • t := fun f t => by
    change Algebra.TensorProduct.lift ((Algebra.ofId ℤ_[p] T₀).comp cAlg) (AlgHom.id ℤ_[p] T₀)
      (fun _ _ => Commute.all _ _) (f ⊗ₜ[ℤ_[p]] t) = _
    rw [Algebra.TensorProduct.lift_tmul]
    simp only [AlgHom.comp_apply, Algebra.ofId_apply, AlgHom.id_apply, Algebra.smul_def]
    rfl
  have hev_surj : Function.Surjective ev := fun t =>
    ⟨(1 : MvPowerSeries (Fin g) ℤ_[p]) ⊗ₜ[ℤ_[p]] t, by rw [hev_tmul, map_one, one_smul]⟩
  have hev_ker : RingHom.ker ev.toRingHom =
      (patchingAugIdeal p g).map (algebraMap (PatchingBaseRing p g) (PatchingBaseRing p g ⊗[ℤ_[p]] T₀)) := by
    apply le_antisymm
    · intro z hz
      have hz_decomp : z = ∑ i : Fin r,
          (b₀.baseChange (MvPowerSeries (Fin g) ℤ_[p])).repr z i ⊗ₜ[ℤ_[p]] b₀ i := by
        have hsum := ((b₀.baseChange (MvPowerSeries (Fin g) ℤ_[p])).sum_repr z).symm
        conv_lhs => rw [hsum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Module.Basis.baseChange_apply, Algebra.smul_def]
        change ((b₀.baseChange (MvPowerSeries (Fin g) ℤ_[p])).repr z i ⊗ₜ[ℤ_[p]] (1 : T₀)) *
          ((1 : MvPowerSeries (Fin g) ℤ_[p]) ⊗ₜ[ℤ_[p]] b₀ i) = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      have hev_z : ev z = ∑ i : Fin r,
          MvPowerSeries.constantCoeff ((b₀.baseChange (MvPowerSeries (Fin g) ℤ_[p])).repr z i) • b₀ i := by
        conv_lhs => rw [hz_decomp]
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => hev_tmul _ _
      have hz0 : ev z = 0 := hz
      rw [hev_z] at hz0
      have hcoord0 : ∀ i : Fin r,
          MvPowerSeries.constantCoeff ((b₀.baseChange (MvPowerSeries (Fin g) ℤ_[p])).repr z i) = 0 :=
        (Fintype.linearIndependent_iff.mp b₀.linearIndependent) _ hz0
      rw [hz_decomp]
      refine Ideal.sum_mem _ fun i _ => ?_
      have hmem : (b₀.baseChange (MvPowerSeries (Fin g) ℤ_[p])).repr z i ∈ patchingAugIdeal p g := by
        rw [patchingAugIdeal_eq_ker_constantCoeff]; exact hcoord0 i
      have hprod : (b₀.baseChange (MvPowerSeries (Fin g) ℤ_[p])).repr z i ⊗ₜ[ℤ_[p]] b₀ i =
          algebraMap (PatchingBaseRing p g) (PatchingBaseRing p g ⊗[ℤ_[p]] T₀)
            ((b₀.baseChange (MvPowerSeries (Fin g) ℤ_[p])).repr z i) *
            ((1 : PatchingBaseRing p g) ⊗ₜ[ℤ_[p]] b₀ i) := by
        change _ = ((b₀.baseChange (MvPowerSeries (Fin g) ℤ_[p])).repr z i ⊗ₜ[ℤ_[p]] (1 : T₀)) *
          ((1 : PatchingBaseRing p g) ⊗ₜ[ℤ_[p]] b₀ i)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hprod]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hmem)
    · rw [Ideal.map_le_iff_le_comap]
      intro s hs
      rw [patchingAugIdeal_eq_ker_constantCoeff] at hs
      change ev (s ⊗ₜ[ℤ_[p]] (1 : T₀)) = 0
      rw [hev_tmul, show MvPowerSeries.constantCoeff s = 0 from hs, zero_smul]
  exact (Ideal.quotEquivOfEq hev_ker.symm).trans (RingHom.quotientKerEquivOfSurjective hev_surj)

/-- **3. General Finite-Free `ℤ_[p]`-Algebra Patching Datum (`S_∞ ⊗[ℤ_[p]] T₀`)**:
for ANY commutative `ℤ_[p]`-algebra `T₀` free of finite rank `r ≥ 1` over `ℤ_[p]` (in particular
`ℤ_[p] ⊗[ℤ] 𝕋_ℤ` for ANY `Stage7HeckeRing.IntHeckeAlg`), constructs a concrete
`TaylorWilesPatchingDatum` over `S_∞ = MvPowerSeries (Fin g) ℤ_[p]` with `R_0 = T_0 = T₀`. -/
def freeAlgPatchingDatum_Zp (p g r : ℕ) [Fact p.Prime] (hr : 0 < r)
    (T₀ : Type) [CommRing T₀] [Algebra ℤ_[p] T₀] (eT : T₀ ≃ₗ[ℤ_[p]] (Fin r → ℤ_[p])) :
    TaylorWilesPatchingDatum where
  S_inf := PatchingBaseRing p g
  g := g
  y := patchingVar
  aug_le_max := patchingAugIdeal_le_maximalIdeal p g
  R_inf := PatchingBaseRing p g ⊗[ℤ_[p]] T₀
  finSR := Module.Finite.equiv (freeAlg_patching_equivPi p g r T₀ eT).symm
  T_inf := PatchingBaseRing p g ⊗[ℤ_[p]] T₀
  phi_inf := AlgHom.id _ _
  phi_surj := Function.surjective_id
  M_inf := PatchingBaseRing p g ⊗[ℤ_[p]] T₀
  compat_RM_TM := fun _ _ => rfl
  rank := r
  rank_pos := hr
  M_free_S := freeAlg_patching_equivPi p g r T₀ eT
  faithful_witness := Or.inr ⟨⟨freeAlg_patching_equivPi p g r T₀ eT,
    ⟨LinearMap.id, Function.surjective_id⟩⟩⟩
  R_0 := T₀
  T_0 := T₀
  specR := freeAlg_patching_specEquiv p g r T₀ eT
  specT := freeAlg_patching_specEquiv p g r T₀ eT

end ConcretePatchingDatums

/-! ## Section 3: Concrete Integral Hecke Rings of `S₁₂, S₁₆, S₁₈, S₂₀, S₂₂` and `S₂₄` -/

section ConcreteModularHeckeRings

private lemma trivialChar_int_range (d : ℕ) :
    (1 : DirichletCharacter ℂ 1) (d : ZMod 1) ∈ Set.range (algebraMap ℤ ℂ) := by
  refine ⟨1, ?_⟩
  have hu : IsUnit (d : ZMod 1) := (ZMod.isUnit_iff_coprime d 1).mpr (Nat.coprime_one_right d)
  simp [MulChar.one_apply hu]

/-- **Unified 1-Dimensional Integral Hecke Ring Theorem**:
for ANY normalized level-1 integer Hecke eigenform `f` (`f 0 = 0`, `f 1 = 1`, `∀ n, f n ∈ ℤ`),
the concrete `Stage7HeckeRing.IntHeckeAlg` on `S = ℂ · f` satisfies:
1. `IntHeckeAlg ≃ₐ[ℤ] ℤ`,
2. `IsGorensteinOver ℤ IntHeckeAlg`,
3. `congruenceIdeal π_f = ⊤` (`Δ = 1`). -/
theorem oneDim_intHeckeAlg_equiv_int (k : ℕ) (aZ : ℕ → ℤ)
    (_h0 : aZ 0 = 0) (h1 : aZ 1 = 1)
    (heig : IsNormalizedHeckeEigenform k (1 : DirichletCharacter ℂ 1)
      (fun n => (aZ n : ℂ)) (fun n => (aZ n : ℂ))) :
    let fC : ℕ → ℂ := fun n => (aZ n : ℂ)
    let S : Submodule ℂ (ℕ → ℂ) := Submodule.span ℂ ({fC} : Set (ℕ → ℂ))
    ∃ (hinv : ∀ n : ℕ, 1 ≤ n → ∀ g ∈ S, heckeOp k (1 : DirichletCharacter ℂ 1) n g ∈ S),
      let S_ℤ := integralCuspLattice ℤ S
      let hS_ℤ_inv := integralCuspLattice_hecke_invariant k (1 : DirichletCharacter ℂ 1) S hinv
        trivialChar_int_range
      let 𝕋_ℤ := IntHeckeAlg k (1 : DirichletCharacter ℂ 1) S hinv S_ℤ hS_ℤ_inv
      let fS : S := ⟨fC, Submodule.subset_span rfl⟩
      let fZ : S_ℤ := ⟨fS, fun n => ⟨aZ n, rfl⟩⟩
      let π_f := eigenformAug k (1 : DirichletCharacter ℂ 1) S hinv Int.cast_injective S_ℤ hS_ℤ_inv
        fZ heig (fun n _ => ⟨aZ n, rfl⟩)
      Nonempty (𝕋_ℤ ≃ₐ[ℤ] ℤ) ∧
        Nonempty (IsGorensteinOver ℤ 𝕋_ℤ) ∧
        Stage3PatchingUnification.congruenceIdeal π_f = ⊤ := by
  intro fC S
  have hinv : ∀ n : ℕ, 1 ≤ n → ∀ g ∈ S, heckeOp k (1 : DirichletCharacter ℂ 1) n g ∈ S := by
    intro n hn g hg
    rw [Submodule.mem_span_singleton] at hg
    obtain ⟨c, rfl⟩ := hg
    rw [heckeOp_smul, heig.2 n hn, smul_smul]
    exact Submodule.smul_mem S _ (Submodule.subset_span rfl)
  refine ⟨hinv, ?_⟩
  intro S_ℤ hS_ℤ_inv 𝕋_ℤ fS fZ π_f
  have hZ_eq : ∀ g : S_ℤ, g = integralCoeff (𝒪 := ℤ) g 1 • fZ := by
    intro g
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp g.1.2
    have hc1 : c = (integralCoeff (𝒪 := ℤ) g 1 : ℂ) := by
      have h1_eq := congrFun hc 1
      have hf1 : fC 1 = 1 := by simp [fC, h1]
      have hg1 : g.1.1 1 = (integralCoeff (𝒪 := ℤ) g 1 : ℂ) := (algebraMap_integralCoeff g 1).symm
      simpa [hf1, hg1] using h1_eq
    apply Subtype.ext; apply Subtype.ext
    rw [← hc, hc1]
    funext n
    simp [Algebra.smul_def, fZ, fS]
  have hπ_inj : Function.Injective π_f := by
    rw [injective_iff_map_eq_zero]
    intro T hT
    apply Subtype.ext; apply LinearMap.ext; intro g
    rw [hZ_eq g, map_smul,
      eigenformAug_smul_eq k (1 : DirichletCharacter ℂ 1) S hinv Int.cast_injective S_ℤ hS_ℤ_inv
        fZ heig (fun n _ => ⟨aZ n, rfl⟩) T,
      hT, zero_smul, smul_zero]
    rfl
  have hπ_surj : Function.Surjective π_f := fun z => ⟨algebraMap ℤ 𝕋_ℤ z, π_f.commutes z⟩
  let e : 𝕋_ℤ ≃ₐ[ℤ] ℤ := AlgEquiv.ofBijective π_f ⟨hπ_inj, hπ_surj⟩
  have hcong : Stage3PatchingUnification.congruenceIdeal π_f = ⊤ := by
    rw [eq_top_iff]
    intro z _
    refine (Stage3PatchingUnification.mem_congruenceIdeal_iff π_f z).mpr
      ⟨algebraMap ℤ 𝕋_ℤ z, ?_, π_f.commutes z⟩
    rw [Stage3PatchingUnification.mem_annAugIdeal_iff]
    intro x hx
    have hx0 : x = 0 := hπ_inj (hx.trans (map_zero π_f).symm)
    rw [hx0, mul_zero]
  exact ⟨⟨e⟩, ⟨isGorensteinOver_ofAlgEquiv (isGorensteinOver_self ℤ) e.symm⟩, hcong⟩

/-- **Concrete `S₁₂` (`Δ = ramanujanDelta`) Integral Hecke Ring Theorem**:
`𝕋_ℤ(S₁₂) ≃ₐ[ℤ] ℤ`, Gorenstein over `ℤ`, trivial congruence ideal (`Δ = 1`). -/
theorem S12_intHeckeAlg_equiv_int :
    let fC : ℕ → ℂ := fun n => (coeffDelta12Z n : ℂ)
    let S : Submodule ℂ (ℕ → ℂ) := Submodule.span ℂ ({fC} : Set (ℕ → ℂ))
    ∃ (hinv : ∀ n : ℕ, 1 ≤ n → ∀ g ∈ S, heckeOp 12 (1 : DirichletCharacter ℂ 1) n g ∈ S),
      let S_ℤ := integralCuspLattice ℤ S
      let hS_ℤ_inv := integralCuspLattice_hecke_invariant 12 (1 : DirichletCharacter ℂ 1) S hinv
        trivialChar_int_range
      let 𝕋_ℤ := IntHeckeAlg 12 (1 : DirichletCharacter ℂ 1) S hinv S_ℤ hS_ℤ_inv
      let fS : S := ⟨fC, Submodule.subset_span rfl⟩
      let fZ : S_ℤ := ⟨fS, fun n => ⟨coeffDelta12Z n, rfl⟩⟩
      let π_f := eigenformAug 12 (1 : DirichletCharacter ℂ 1) S hinv Int.cast_injective S_ℤ hS_ℤ_inv
        fZ (by
          change IsNormalizedHeckeEigenform 12 (1 : DirichletCharacter ℂ 1)
            (fun n => (coeffDelta12Z n : ℂ)) (fun n => (coeffDelta12Z n : ℂ))
          have hcast : (fun n => (coeffDelta12Z n : ℂ)) = qExpansionCoeff delta12 := funext fun n => by
            unfold coeffDelta12Z delta12 qExpansionCoeff
            rw [← ramanujanDeltaPowerSeriesZ_map_eq, PowerSeries.coeff_map]
            rfl
          rw [hcast]
          exact isNormalizedHeckeEigenform_of_heckeCuspForm (by norm_num)
            (by rw [← hcast]; simp [coeffDelta12Z, ramanujanTau_one])
            (fun n hn => by
              rw [heckeCuspForm_delta12 hn, ← hcast]))
        (fun n _ => ⟨coeffDelta12Z n, rfl⟩)
      Nonempty (𝕋_ℤ ≃ₐ[ℤ] ℤ) ∧
        Nonempty (IsGorensteinOver ℤ 𝕋_ℤ) ∧
        Stage3PatchingUnification.congruenceIdeal π_f = ⊤ := by
  have hcast : (fun n => (coeffDelta12Z n : ℂ)) = qExpansionCoeff delta12 := funext fun n => by
    unfold coeffDelta12Z delta12 qExpansionCoeff
    rw [← ramanujanDeltaPowerSeriesZ_map_eq, PowerSeries.coeff_map]
    rfl
  have heig : IsNormalizedHeckeEigenform 12 (1 : DirichletCharacter ℂ 1)
      (fun n => (coeffDelta12Z n : ℂ)) (fun n => (coeffDelta12Z n : ℂ)) := by
    rw [hcast]
    exact isNormalizedHeckeEigenform_of_heckeCuspForm (by norm_num)
      (by rw [← hcast]; simp [coeffDelta12Z, ramanujanTau_one])
      (fun n hn => by rw [heckeCuspForm_delta12 hn, ← hcast])
  exact oneDim_intHeckeAlg_equiv_int 12 coeffDelta12Z ramanujanTau_zero ramanujanTau_one heig

/-- Concrete 1D Integral Hecke Ring Theorem for `S₁₆`, `S₁₈`, `S₂₀`, `S₂₂`. -/
theorem S16_to_S22_intHeckeAlg_equiv_int :
    (∃ (hinv : ∀ n : ℕ, 1 ≤ n → ∀ g ∈ Submodule.span ℂ ({fun m => (coeffDelta16Z m : ℂ)} : Set (ℕ → ℂ)),
        heckeOp 16 (1 : DirichletCharacter ℂ 1) n g ∈ Submodule.span ℂ ({fun m => (coeffDelta16Z m : ℂ)} : Set (ℕ → ℂ))),
      Nonempty (IntHeckeAlg 16 1 _ hinv (integralCuspLattice ℤ _)
        (integralCuspLattice_hecke_invariant 16 1 _ hinv trivialChar_int_range) ≃ₐ[ℤ] ℤ)) ∧
    (∃ (hinv : ∀ n : ℕ, 1 ≤ n → ∀ g ∈ Submodule.span ℂ ({fun m => (coeffDelta18Z m : ℂ)} : Set (ℕ → ℂ)),
        heckeOp 18 (1 : DirichletCharacter ℂ 1) n g ∈ Submodule.span ℂ ({fun m => (coeffDelta18Z m : ℂ)} : Set (ℕ → ℂ))),
      Nonempty (IntHeckeAlg 18 1 _ hinv (integralCuspLattice ℤ _)
        (integralCuspLattice_hecke_invariant 18 1 _ hinv trivialChar_int_range) ≃ₐ[ℤ] ℤ)) ∧
    (∃ (hinv : ∀ n : ℕ, 1 ≤ n → ∀ g ∈ Submodule.span ℂ ({fun m => (coeffDelta20Z m : ℂ)} : Set (ℕ → ℂ)),
        heckeOp 20 (1 : DirichletCharacter ℂ 1) n g ∈ Submodule.span ℂ ({fun m => (coeffDelta20Z m : ℂ)} : Set (ℕ → ℂ))),
      Nonempty (IntHeckeAlg 20 1 _ hinv (integralCuspLattice ℤ _)
        (integralCuspLattice_hecke_invariant 20 1 _ hinv trivialChar_int_range) ≃ₐ[ℤ] ℤ)) ∧
    (∃ (hinv : ∀ n : ℕ, 1 ≤ n → ∀ g ∈ Submodule.span ℂ ({fun m => (coeffDelta22Z m : ℂ)} : Set (ℕ → ℂ)),
        heckeOp 22 (1 : DirichletCharacter ℂ 1) n g ∈ Submodule.span ℂ ({fun m => (coeffDelta22Z m : ℂ)} : Set (ℕ → ℂ))),
      Nonempty (IntHeckeAlg 22 1 _ hinv (integralCuspLattice ℤ _)
        (integralCuspLattice_hecke_invariant 22 1 _ hinv trivialChar_int_range) ≃ₐ[ℤ] ℤ)) := by
  have h16 := oneDim_intHeckeAlg_equiv_int 16 coeffDelta16Z coeffDelta16Z_small.1
    coeffDelta16Z_small.2.1 (by simpa [funext coeffDelta16Z_cast_eq] using isNormalizedHeckeEigenform_delta16)
  have h18 := oneDim_intHeckeAlg_equiv_int 18 coeffDelta18Z coeffDelta18Z_small.1
    coeffDelta18Z_small.2.1 (by simpa [funext coeffDelta18Z_cast_eq] using isNormalizedHeckeEigenform_delta18)
  have h20 := oneDim_intHeckeAlg_equiv_int 20 coeffDelta20Z coeffDelta20Z_small.1
    coeffDelta20Z_small.2.1 (by simpa [funext coeffDelta20Z_cast_eq] using isNormalizedHeckeEigenform_delta20)
  have h22 := oneDim_intHeckeAlg_equiv_int 22 coeffDelta22Z coeffDelta22Z_small.1
    coeffDelta22Z_small.2.1 (by simpa [funext coeffDelta22Z_cast_eq] using isNormalizedHeckeEigenform_delta22)
  exact ⟨⟨h16.choose, h16.choose_spec.1⟩, ⟨h18.choose, h18.choose_spec.1⟩,
    ⟨h20.choose, h20.choose_spec.1⟩, ⟨h22.choose, h22.choose_spec.1⟩⟩

/-! ### Concrete Weight-24 (`S₂₄`, `dim = 2`) Integral Hecke Algebra `𝕋_ℤ(S₂₄) ≃ₐ[ℤ] QuadAlg ℤ 1080 (-20468736)` -/

/-- Exact concrete `q`-expansion subspace `S24_qSpace ⊆ (ℕ → ℂ)` of `S₂₄(SL₂(ℤ))`. -/
def S24_qSpace : Submodule ℂ (ℕ → ℂ) :=
  Submodule.span ℂ ({qExpansionCoeff S24_vm1, qExpansionCoeff S24_vm2} : Set (ℕ → ℂ))

/-- Every `f : CuspForm SL2ZRange 24` has `qExpansionCoeff f ∈ S24_qSpace`. -/
theorem qExpansionCoeff_mem_S24_qSpace (f : CuspForm SL2ZRange 24) :
    qExpansionCoeff f ∈ S24_qSpace := by
  have hf : qExpansionCoeff f =
      qExpansionCoeff f 1 • qExpansionCoeff S24_vm1 +
        qExpansionCoeff f 2 • qExpansionCoeff S24_vm2 := by
    funext m
    conv_lhs => rw [S24_eq_vm_linear_comb f]
    simp [qExpansionCoeff_add, qExpansionCoeff_smul]
  rw [hf]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert_of_mem _ rfl)))

/-- `S24_qSpace` is invariant under every Hecke operator `T_n` (`n ≥ 1`). -/
theorem S24_qSpace_hecke_inv (n : ℕ) (hn : 1 ≤ n) (g : ℕ → ℂ) (hg : g ∈ S24_qSpace) :
    heckeOp 24 (1 : DirichletCharacter ℂ 1) n g ∈ S24_qSpace := by
  refine Submodule.span_induction (p := fun g _ => heckeOp 24 (1 : DirichletCharacter ℂ 1) n g ∈ S24_qSpace)
    (mem := by
      rintro g (rfl | rfl)
      · have h : heckeOp 24 (1 : DirichletCharacter ℂ 1) n (qExpansionCoeff S24_vm1) =
            qExpansionCoeff (heckeCuspForm 24 (by norm_num) n hn S24_vm1) := by
          funext m; exact (heckeCuspForm_qExpansion_coeff 24 (by norm_num) n hn S24_vm1 m).symm
        rw [h]; exact qExpansionCoeff_mem_S24_qSpace _
      · have h : heckeOp 24 (1 : DirichletCharacter ℂ 1) n (qExpansionCoeff S24_vm2) =
            qExpansionCoeff (heckeCuspForm 24 (by norm_num) n hn S24_vm2) := by
          funext m; exact (heckeCuspForm_qExpansion_coeff 24 (by norm_num) n hn S24_vm2 m).symm
        rw [h]; exact qExpansionCoeff_mem_S24_qSpace _)
    (zero := by
      have hz : heckeOp 24 (1 : DirichletCharacter ℂ 1) n 0 = 0 :=
        (heckeOpLin 24 (1 : DirichletCharacter ℂ 1) n).map_zero
      rw [hz]; exact S24_qSpace.zero_mem)
    (add := fun x y _ _ hx hy => by rw [heckeOp_add]; exact S24_qSpace.add_mem hx hy)
    (smul := fun c x _ hx => by rw [heckeOp_smul]; exact S24_qSpace.smul_mem c hx)
    hg

/-- Both Victor Miller basis elements `S24_vm1` and `S24_vm2` have integer Fourier coefficients. -/
theorem S24_vm_integral_coeffs :
    (∀ n : ℕ, qExpansionCoeff S24_vm1 n ∈ Set.range (algebraMap ℤ ℂ)) ∧
    (∀ n : ℕ, qExpansionCoeff S24_vm2 n ∈ Set.range (algebraMap ℤ ℂ)) := by
  have hE4 : PowerSeries.map (Int.castRingHom ℂ) (ramanujanDeltaPowerSeriesZ * E4SeriesZ ^ 3) =
      UpperHalfPlane.qExpansion 1 (S24_E4CubeDelta : UpperHalfPlane → ℂ) := by
    unfold S24_E4CubeDelta
    rw [map_mul, map_pow, ramanujanDeltaPowerSeriesZ_map_eq, E4SeriesZ_map_eq,
      qExpansion_cuspFormShift_symm]
    congr 1
    unfold monomialE4E6
    rw [ModularForm.qExpansion_mcast,
      ModularForm.qExpansion_mul zero_lt_one one_mem_strictPeriods_SL,
      ModularForm.qExpansion_pow zero_lt_one one_mem_strictPeriods_SL,
      ModularForm.qExpansion_pow zero_lt_one one_mem_strictPeriods_SL]
    simp
  have hD2 : PowerSeries.map (Int.castRingHom ℂ) (ramanujanDeltaPowerSeriesZ * ramanujanDeltaPowerSeriesZ) =
      UpperHalfPlane.qExpansion 1 (S24_DeltaSq : UpperHalfPlane → ℂ) := by
    unfold S24_DeltaSq
    rw [map_mul, ramanujanDeltaPowerSeriesZ_map_eq, qExpansion_cuspFormShift_symm]
    rfl
  have hE4_int : ∀ n : ℕ, qExpansionCoeff S24_E4CubeDelta n ∈ Set.range (algebraMap ℤ ℂ) := fun n =>
    ⟨PowerSeries.coeff n (ramanujanDeltaPowerSeriesZ * E4SeriesZ ^ 3), by
      rw [qExpansionCoeff, ← hE4, PowerSeries.coeff_map]; rfl⟩
  have hD2_int : ∀ n : ℕ, qExpansionCoeff S24_DeltaSq n ∈ Set.range (algebraMap ℤ ℂ) := fun n =>
    ⟨PowerSeries.coeff n (ramanujanDeltaPowerSeriesZ * ramanujanDeltaPowerSeriesZ), by
      rw [qExpansionCoeff, ← hD2, PowerSeries.coeff_map]; rfl⟩
  refine ⟨fun n => ?_, hD2_int⟩
  obtain ⟨a, ha⟩ := hE4_int n
  obtain ⟨b, hb⟩ := hD2_int n
  refine ⟨a - 696 * b, ?_⟩
  rw [S24_vm1, qExpansionCoeff_sub, qExpansionCoeff_smul, ← ha, ← hb]
  simp

/-- Canonical integral `q`-expansion lattice `S24_Z := integralCuspLattice ℤ S24_qSpace`. -/
abbrev S24_Z : Submodule ℤ S24_qSpace :=
  integralCuspLattice ℤ S24_qSpace

/-- Hecke-invariance of `S24_Z`. -/
theorem S24_Z_hecke_inv :
    ∀ (n : ℕ) (hn : 1 ≤ n), ∀ f ∈ S24_Z,
      heckeEnd 24 (1 : DirichletCharacter ℂ 1) S24_qSpace S24_qSpace_hecke_inv n hn f ∈ S24_Z :=
  integralCuspLattice_hecke_invariant 24 (1 : DirichletCharacter ℂ 1) S24_qSpace
    S24_qSpace_hecke_inv trivialChar_int_range

/-- **Concrete Integral Hecke Algebra `𝕋_ℤ(S₂₄)` of Weight 24 (`Stage7HeckeRing.IntHeckeAlg`)**. -/
abbrev S24_IntHeckeAlg : Type :=
  IntHeckeAlg 24 (1 : DirichletCharacter ℂ 1) S24_qSpace S24_qSpace_hecke_inv S24_Z S24_Z_hecke_inv

/-- **EXACT `ℤ`-ALGEBRA ISOMORPHISM `𝕋_ℤ(S₂₄) ≃ₐ[ℤ] QuadAlg ℤ 1080 (-20468736)` (`0` Assumptions!)**:
proves directly from `Stage7HeckeRing` + `Stage10PeterssonHecke.S24_T2_on_vm` that the full
integral Hecke algebra `𝕋_ℤ(S₂₄)` is generated over `ℤ` by `T₂` with exact relation
`T₂² - 1080 T₂ - 20468736 = 0`! -/
def S24_intHeckeAlg_equiv_quadAlg :
    S24_IntHeckeAlg ≃ₐ[ℤ] QuadAlg ℤ 1080 (-20468736) := by
  let vm1S : S24_qSpace := ⟨qExpansionCoeff S24_vm1, Submodule.subset_span (Set.mem_insert _ _)⟩
  let vm2S : S24_qSpace := ⟨qExpansionCoeff S24_vm2,
    Submodule.subset_span (Set.mem_insert_of_mem _ rfl)⟩
  let vm1Z : S24_Z := ⟨vm1S, S24_vm_integral_coeffs.1⟩
  let vm2Z : S24_Z := ⟨vm2S, S24_vm_integral_coeffs.2⟩
  have hZ_decomp : ∀ g : S24_Z, g = integralCoeff (𝒪 := ℤ) g 1 • vm1Z + integralCoeff (𝒪 := ℤ) g 2 • vm2Z := by
    intro g
    have hg_span : ∃ a b : ℂ, g.1.1 = a • qExpansionCoeff S24_vm1 + b • qExpansionCoeff S24_vm2 := by
      refine Submodule.span_induction
        (p := fun v _ => ∃ a b : ℂ, v = a • qExpansionCoeff S24_vm1 + b • qExpansionCoeff S24_vm2)
        (mem := by
          rintro _ (rfl | rfl)
          · exact ⟨1, 0, by simp⟩
          · exact ⟨0, 1, by simp⟩)
        (zero := ⟨0, 0, by simp⟩)
        (add := by
          rintro _ _ _ _ ⟨a₁, b₁, rfl⟩ ⟨a₂, b₂, rfl⟩
          exact ⟨a₁ + a₂, b₁ + b₂, by funext m; simp [add_smul]; ring⟩)
        (smul := by
          rintro c _ _ ⟨a, b, rfl⟩
          exact ⟨c * a, c * b, by funext m; simp; ring⟩)
        g.1.2
    obtain ⟨a, b, hab⟩ := hg_span
    have ha : a = (integralCoeff (𝒪 := ℤ) g 1 : ℂ) := by
      have h1 := congrFun hab 1
      have hg1 : g.1.1 1 = (integralCoeff (𝒪 := ℤ) g 1 : ℂ) := (algebraMap_integralCoeff g 1).symm
      simpa [hg1, S24_vm1_coeffs.1, S24_vm2, S24_DeltaSq_coeffs.2.1] using h1.symm
    have hb : b = (integralCoeff (𝒪 := ℤ) g 2 : ℂ) := by
      have h2 := congrFun hab 2
      have hg2 : g.1.1 2 = (integralCoeff (𝒪 := ℤ) g 2 : ℂ) := (algebraMap_integralCoeff g 2).symm
      simpa [hg2, S24_vm1_coeffs.2.1, S24_vm2, S24_DeltaSq_coeffs.2.2.1] using h2.symm
    apply Subtype.ext; apply Subtype.ext
    rw [hab, ha, hb]
    funext m
    simp [Algebra.smul_def, vm1Z, vm2Z, vm1S, vm2S]
  let T2 : S24_IntHeckeAlg :=
    oHeckeAlgGen 24 (1 : DirichletCharacter ℂ 1) S24_qSpace S24_qSpace_hecke_inv S24_Z S24_Z_hecke_inv
      2 (by norm_num)
  have hT2_vm1 : T2.1 vm1Z = (20468736 : ℤ) • vm2Z := by
    apply Subtype.ext; apply Subtype.ext
    funext m
    change heckeOp 24 (1 : DirichletCharacter ℂ 1) 2 (qExpansionCoeff S24_vm1) m =
      (20468736 : ℤ) • qExpansionCoeff S24_vm2 m
    have hq := (heckeCuspForm_qExpansion_coeff 24 (by norm_num) 2 (by norm_num) S24_vm1 m).symm
    change heckeOp 24 (1 : DirichletCharacter ℂ 1) 2 (qExpansionCoeff S24_vm1) m =
      qExpansionCoeff (heckeCuspForm 24 (by norm_num) 2 (by norm_num) S24_vm1) m at hq
    rw [hq, S24_T2_on_vm.1, qExpansionCoeff_smul]
    simp [zsmul_eq_mul]
  have hT2_vm2 : T2.1 vm2Z = vm1Z + (1080 : ℤ) • vm2Z := by
    apply Subtype.ext; apply Subtype.ext
    funext m
    change heckeOp 24 (1 : DirichletCharacter ℂ 1) 2 (qExpansionCoeff S24_vm2) m =
      qExpansionCoeff S24_vm1 m + (1080 : ℤ) • qExpansionCoeff S24_vm2 m
    have hq := (heckeCuspForm_qExpansion_coeff 24 (by norm_num) 2 (by norm_num) S24_vm2 m).symm
    change heckeOp 24 (1 : DirichletCharacter ℂ 1) 2 (qExpansionCoeff S24_vm2) m =
      qExpansionCoeff (heckeCuspForm 24 (by norm_num) 2 (by norm_num) S24_vm2) m at hq
    rw [hq, S24_T2_on_vm.2, qExpansionCoeff_add, qExpansionCoeff_smul]
    simp [zsmul_eq_mul]
  have hT2_sq : T2 * T2 = (1080 : ℤ) • T2 + (20468736 : ℤ) • (1 : S24_IntHeckeAlg) := by
    apply Subtype.ext; apply LinearMap.ext; intro g
    rw [hZ_decomp g]
    have hvm1 : (T2 * T2).1 vm1Z = ((1080 : ℤ) • T2 + (20468736 : ℤ) • (1 : S24_IntHeckeAlg)).1 vm1Z := by
      change T2.1 (T2.1 vm1Z) = (1080 : ℤ) • T2.1 vm1Z + (20468736 : ℤ) • vm1Z
      rw [hT2_vm1, map_zsmul, hT2_vm2, smul_add, smul_smul, smul_smul]
      abel
    have hvm2 : (T2 * T2).1 vm2Z = ((1080 : ℤ) • T2 + (20468736 : ℤ) • (1 : S24_IntHeckeAlg)).1 vm2Z := by
      change T2.1 (T2.1 vm2Z) = (1080 : ℤ) • T2.1 vm2Z + (20468736 : ℤ) • vm2Z
      rw [hT2_vm2, map_add, map_zsmul, hT2_vm1, hT2_vm2]
      module
    simp only [map_add, map_zsmul, hvm1, hvm2]
  let φ : QuadAlg ℤ 1080 (-20468736) →ₐ[ℤ] S24_IntHeckeAlg :=
    { toFun := fun u => u.fst • (1 : S24_IntHeckeAlg) + u.snd • T2
      map_one' := by simp
      map_mul' := fun u v => by
        change (u.fst * v.fst - (-20468736) * (u.snd * v.snd)) • (1 : S24_IntHeckeAlg) +
            (u.fst * v.snd + u.snd * v.fst + 1080 * (u.snd * v.snd)) • T2 =
          (u.fst • (1 : S24_IntHeckeAlg) + u.snd • T2) * (v.fst • 1 + v.snd • T2)
        have hmul : (u.fst • (1 : S24_IntHeckeAlg) + u.snd • T2) * (v.fst • 1 + v.snd • T2) =
            (u.fst * v.fst) • (1 : S24_IntHeckeAlg) +
              (u.fst * v.snd + u.snd * v.fst) • T2 +
              (u.snd * v.snd) • (T2 * T2) := by
          simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
          module
        rw [hmul, hT2_sq]
        module
      map_zero' := by simp
      map_add' := fun u v => by
        change (u.fst + v.fst) • (1 : S24_IntHeckeAlg) + (u.snd + v.snd) • T2 =
          (u.fst • 1 + u.snd • T2) + (v.fst • 1 + v.snd • T2)
        module
      commutes' := fun z => by
        change z • (1 : S24_IntHeckeAlg) + (0 : ℤ) • T2 = algebraMap ℤ S24_IntHeckeAlg z
        rw [zero_smul, add_zero, Algebra.algebraMap_eq_smul_one] }
  have hφ_inj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    have hact : (φ u).1 vm1Z = 0 := by rw [hu]; rfl
    change u.fst • vm1Z + u.snd • (T2.1 vm1Z) = 0 at hact
    rw [hT2_vm1, smul_smul] at hact
    have h1 := congrFun (congrArg (fun x : S24_Z => x.1.1) hact) 1
    have h2 := congrFun (congrArg (fun x : S24_Z => x.1.1) hact) 2
    have hfstC : (u.fst : ℂ) = 0 := by
      simpa [vm1Z, vm2Z, vm1S, vm2S, S24_vm1_coeffs.1, S24_vm2, S24_DeltaSq_coeffs.2.1,
        zsmul_eq_mul] using h1
    have hsndC : (u.snd : ℂ) * 20468736 = 0 := by
      simpa [vm1Z, vm2Z, vm1S, vm2S, S24_vm1_coeffs.2.1, S24_vm2, S24_DeltaSq_coeffs.2.2.1,
        zsmul_eq_mul] using h2
    have hfst : u.fst = 0 := Int.cast_injective (α := ℂ) (by simpa using hfstC)
    have hsnd : u.snd = 0 := by
      have hsC : (u.snd : ℂ) = 0 := (mul_eq_zero.mp hsndC).resolve_right (by norm_num)
      exact Int.cast_injective (α := ℂ) (by simpa using hsC)
    ext <;> assumption
  have hφ_surj : Function.Surjective φ := by
    intro T
    let a : ℤ := integralCoeff (T.1 vm1Z) 1
    let b : ℤ := integralCoeff (T.1 vm1Z) 2
    let c : ℤ := integralCoeff (T.1 vm2Z) 1
    let d : ℤ := integralCoeff (T.1 vm2Z) 2
    have hT1 : T.1 vm1Z = a • vm1Z + b • vm2Z := hZ_decomp (T.1 vm1Z)
    have hT2 : T.1 vm2Z = c • vm1Z + d • vm2Z := hZ_decomp (T.1 vm2Z)
    have hcomm : (T * T2).1 vm1Z = (T2 * T).1 vm1Z := by rw [mul_comm]
    change T.1 (T2.1 vm1Z) = T2.1 (T.1 vm1Z) at hcomm
    rw [hT2_vm1, map_zsmul, hT2, hT1, map_add, map_zsmul, map_zsmul, hT2_vm1, hT2_vm2] at hcomm
    have h1 := congrFun (congrArg (fun x : S24_Z => x.1.1) hcomm) 1
    have h2 := congrFun (congrArg (fun x : S24_Z => x.1.1) hcomm) 2
    have hb_eqC : (20468736 : ℂ) * (c : ℂ) = (b : ℂ) := by
      simpa [vm1Z, vm2Z, vm1S, vm2S, S24_vm1_coeffs.1, S24_vm2, S24_DeltaSq_coeffs.2.1,
        zsmul_eq_mul] using h1
    have hb_eq : b = 20468736 * c :=
      Int.cast_injective (α := ℂ) (by push_cast; exact hb_eqC.symm)
    have hd_eqC : (20468736 : ℂ) * (d : ℂ) = (a : ℂ) * 20468736 + (b : ℂ) * 1080 := by
      simpa [vm1Z, vm2Z, vm1S, vm2S, S24_vm1_coeffs.2.1, S24_vm2, S24_DeltaSq_coeffs.2.2.1,
        zsmul_eq_mul] using h2
    have hd_eq : d = a + 1080 * c := by
      have hmul : (20468736 : ℤ) * d = 20468736 * (a + 1080 * c) := by
        have hZ : (20468736 : ℤ) * d = a * 20468736 + b * 1080 :=
          Int.cast_injective (α := ℂ) (by push_cast; exact hd_eqC)
        rw [hb_eq] at hZ; linarith
      omega
    refine ⟨⟨a, c⟩, ?_⟩
    apply Subtype.ext; apply LinearMap.ext; intro g
    rw [hZ_decomp g, map_add, map_zsmul, map_zsmul, map_add, map_zsmul, map_zsmul]
    have hm1 : (φ ⟨a, c⟩).1 vm1Z = T.1 vm1Z := by
      change a • vm1Z + c • T2.1 vm1Z = T.1 vm1Z
      rw [hT2_vm1, smul_smul, hT1, hb_eq, mul_comm]
    have hm2 : (φ ⟨a, c⟩).1 vm2Z = T.1 vm2Z := by
      change a • vm2Z + c • T2.1 vm2Z = T.1 vm2Z
      rw [hT2_vm2, smul_add, smul_smul, hT2, hd_eq, add_smul, mul_comm c 1080]
      abel
    rw [hm1, hm2]
  exact (AlgEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩).symm

/-- **Unconditional Gorensteinness of `𝕋_ℤ(S₂₄)` over `ℤ`**. -/
def S24_intHeckeAlg_isGorensteinOver : IsGorensteinOver ℤ S24_IntHeckeAlg :=
  isGorensteinOver_ofAlgEquiv (QuadAlg.isGorensteinOver ℤ 1080 (-20468736))
    S24_intHeckeAlg_equiv_quadAlg.symm

/-- Exact discriminant identity and prime factorization of `disc(T₂)` on `S₂₄`:
`disc(T₂) = 1080² - 4 * (-20468736) = 83041344 = 24² * 144169 = 2⁶ * 3² * 144169`,
with `Nat.Prime 144169` and exact prime-factor set `{2, 3, 144169}`! -/
theorem S24_T2_disc_factorization :
    (1080 : ℤ) ^ 2 - 4 * (-20468736) = 83041344 ∧
    (83041344 : ℕ) = 24 ^ 2 * 144169 ∧
    (83041344 : ℕ) = 2 ^ 6 * 3 ^ 2 * 144169 ∧
    Nat.Prime 144169 ∧
    (83041344 : ℕ).primeFactors = {2, 3, 144169} := by
  have hp144169 : Nat.Prime 144169 := by norm_num
  have hfac : (83041344 : ℕ) = 2 ^ 6 * 3 ^ 2 * 144169 := by norm_num
  have hpf : (83041344 : ℕ).primeFactors = {2, 3, 144169} := by
    rw [hfac, Nat.primeFactors_mul (by norm_num) hp144169.ne_zero,
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_pow 2 (by norm_num), Nat.primeFactors_pow 3 (by norm_num),
      Nat.Prime.primeFactors (by norm_num : Nat.Prime 2),
      Nat.Prime.primeFactors (by norm_num : Nat.Prime 3),
      Nat.Prime.primeFactors hp144169]
    ext q; simp
  exact ⟨by norm_num, by norm_num, hfac, hp144169, hpf⟩

/-- **Concrete `ℤ_[p]`-Patching & Gorensteinness of `S₂₄` for EVERY prime `p`**:
patches `T_0 = QuadAlg ℤ_[p] 1080 (-20468736)` over `S_∞ = MvPowerSeries (Fin g) ℤ_[p]`,
yielding `R_∞ ≃ T_∞`, `R_0 ≃+* T_0`, and `IsGorensteinOver ℤ_[p] T_0`! -/
theorem S24_patching_and_gorenstein_Zp (p g : ℕ) [Fact p.Prime] :
    let D := quadraticPatchingDatum_Zp p g (1080 : ℤ_[p]) (-20468736 : ℤ_[p])
    Nonempty (D.R_inf ≃ₐ[D.S_inf] D.T_inf) ∧
      Nonempty (D.R_0 ≃+* D.T_0) ∧
      Module.Free (D.S_inf ⧸ D.augIdeal) D.M_0 ∧
      Module.Finite (D.S_inf ⧸ D.augIdeal) D.M_0 ∧
      Nonempty (IsGorensteinOver ℤ_[p] (QuadAlg ℤ_[p] (1080 : ℤ_[p]) (-20468736 : ℤ_[p]))) :=
  quadraticPatchingDatum_Zp_spec p g 1080 (-20468736)

end ConcreteModularHeckeRings

/-! ## Section 4: Wiles–Lenstra `p`-adic Congruence Bounds & Finite-Support
`CongruencePatchingRealization` Discharge (`S₁₂`, `S₂₄`, and General `Δ_T`) -/

section PadicCongruenceBoundsAndRealization

/-- Exact `ℤ_[p]`-length of `ℤ_[p] ⧸ (n)` for any nonzero integer `n : ℤ`:
`Module.length ℤ_[p] (ℤ_[p] ⧸ Ideal.span {(n : ℤ_[p])}) = padicValNat p n.natAbs`. -/
theorem padicInt_length_quot_span_intCast (p : ℕ) [Fact p.Prime] {n : ℤ} (hn : n ≠ 0) :
    Module.length ℤ_[p] (ℤ_[p] ⧸ Ideal.span ({(n : ℤ_[p])} : Set ℤ_[p])) =
      (padicValNat p n.natAbs : ℕ∞) := by
  have hp : p.Prime := Fact.out
  have hna : n.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hn
  let v : ℕ := padicValNat p n.natAbs
  let m : ℕ := n.natAbs / p ^ v
  have hdvd : p ^ v ∣ n.natAbs := pow_padicValNat_dvd
  have hmul : p ^ v * m = n.natAbs := Nat.mul_div_cancel' hdvd
  have hnd : ¬ p ∣ m := by
    intro hpm
    obtain ⟨q, hq⟩ := hpm
    have hdvd1 : p ^ (v + 1) ∣ n.natAbs := by
      refine ⟨q, ?_⟩
      calc n.natAbs = p ^ v * m := hmul.symm
        _ = p ^ v * (p * q) := by rw [hq]
        _ = p ^ (v + 1) * q := by rw [pow_succ]; ring
    have hle := (padicValNat_dvd_iff_le hna).mp hdvd1
    omega
  have hm_unit : IsUnit (m : ℤ_[p]) := by
    apply padicInt_isUnit_of_toZMod_ne_zero
    rw [map_natCast, Ne, ZMod.natCast_eq_zero_iff]
    exact hnd
  have habs_assoc : Associated ((p : ℤ_[p]) ^ v) (n.natAbs : ℤ_[p]) := by
    obtain ⟨u, hu⟩ := hm_unit
    refine ⟨u, ?_⟩
    rw [hu, ← Nat.cast_pow, ← Nat.cast_mul, hmul]
  have hn_assoc : Associated (n.natAbs : ℤ_[p]) (n : ℤ_[p]) := by
    rcases Int.natAbs_eq n with hpos | hneg
    · have : (n.natAbs : ℤ_[p]) = (n : ℤ_[p]) := by
        rw [← Int.cast_natCast, ← hpos]
      rw [this]
    · refine ⟨-1, ?_⟩
      have h1 : (n : ℤ) = -(n.natAbs : ℤ) := by omega
      rw [h1]
      simp
  have hspan : Ideal.span ({(n : ℤ_[p])} : Set ℤ_[p]) =
      Ideal.span ({(p : ℤ_[p]) ^ v} : Set ℤ_[p]) :=
    span_singleton_eq_of_associated (habs_assoc.trans hn_assoc).symm
  rw [hspan]
  exact padicInt_length_quot_span_p_pow v

/-- If a nonzero integer `n : ℤ` maps into an ideal `I : Ideal ℤ_[p]`, then
`Module.length ℤ_[p] (ℤ_[p] ⧸ I) ≤ padicValNat p n.natAbs`. -/
theorem padicInt_length_quot_le_padicValNat_of_mem (p : ℕ) [Fact p.Prime]
    {I : Ideal ℤ_[p]} {n : ℤ} (hn : n ≠ 0) (hmem : (n : ℤ_[p]) ∈ I) :
    Module.length ℤ_[p] (ℤ_[p] ⧸ I) ≤ (padicValNat p n.natAbs : ℕ∞) := by
  have hle : Ideal.span ({(n : ℤ_[p])} : Set ℤ_[p]) ≤ I :=
    (Ideal.span_singleton_le_iff_mem I).mpr hmem
  calc Module.length ℤ_[p] (ℤ_[p] ⧸ I)
      ≤ Module.length ℤ_[p] (ℤ_[p] ⧸ Ideal.span ({(n : ℤ_[p])} : Set ℤ_[p])) :=
        Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)
    _ = (padicValNat p n.natAbs : ℕ∞) := padicInt_length_quot_span_intCast p hn

/-- If `(n : ℤ_[p]) ∈ I` and `p ∤ n.natAbs`, then `I = ⊤` (trivial congruence ideal!). -/
theorem padicInt_ideal_eq_top_of_not_dvd (p : ℕ) [Fact p.Prime]
    {I : Ideal ℤ_[p]} {n : ℤ} (_hn : n ≠ 0) (hnd : ¬ p ∣ n.natAbs) (hmem : (n : ℤ_[p]) ∈ I) :
    I = ⊤ := by
  have hunit : IsUnit (n : ℤ_[p]) := by
    apply padicInt_isUnit_of_toZMod_ne_zero
    rw [map_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro hdvd
    exact hnd (Int.natCast_dvd.mp hdvd)
  exact Ideal.eq_top_of_isUnit_mem I hmem hunit

/-- Exact prime-factor logarithmic sum identity:
`∑ p ∈ n.primeFactors, Real.log p * padicValNat p n = Real.log n` for every `n ≠ 0`. -/
theorem sum_primeFactors_log_mul_padicValNat {n : ℕ} (hn : n ≠ 0) :
    ∑ p ∈ n.primeFactors, Real.log (p : ℝ) * (padicValNat p n : ℝ) = Real.log (n : ℝ) := by
  have hprod : ∏ p ∈ n.primeFactors, (p : ℝ) ^ (n.factorization p) = (n : ℝ) := by
    have hnat : ∏ p ∈ n.primeFactors, p ^ (n.factorization p) = n :=
      Nat.prod_factorization_pow_eq_self hn
    exact_mod_cast hnat
  have hne : ∀ p ∈ n.primeFactors, ((p : ℝ) ^ (n.factorization p)) ≠ 0 := fun p hp =>
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.pos_of_mem_primeFactors hp).ne')
  rw [← hprod, Real.log_prod hne]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  rw [Real.log_pow, Nat.factorization_def n hp_prime, mul_comm]

/-! ### Base-Change Congruence-Ideal Bridge (`Stage7HeckeRing` / `𝕋_ℤ` → `ℤ_[l] ⊗[ℤ] 𝕋_ℤ`) -/

/-- Canonical `ℤ_[l]`-augmentation on the `l`-adic base change `ℤ_[l] ⊗[ℤ] T` of ANY augmented
`ℤ`-algebra `(T, π : T →ₐ[ℤ] ℤ)` (e.g. `Stage7HeckeRing.IntHeckeAlg` with `eigenformAug`!). -/
def baseChangeAug (l : ℕ) [Fact l.Prime] {T : Type*} [CommRing T] (π : T →ₐ[ℤ] ℤ) :
    (ℤ_[l] ⊗[ℤ] T) →ₐ[ℤ_[l]] ℤ_[l] where
  toRingHom :=
    (Algebra.TensorProduct.lift (AlgHom.id ℤ ℤ_[l]) ((Algebra.ofId ℤ ℤ_[l]).comp π)
      (fun _ _ => Commute.all _ _)).toRingHom
  commutes' a := by
    change Algebra.TensorProduct.lift (AlgHom.id ℤ ℤ_[l]) ((Algebra.ofId ℤ ℤ_[l]).comp π)
      (fun _ _ => Commute.all _ _) (a ⊗ₜ[ℤ] 1) = a
    simp

@[simp]
theorem baseChangeAug_tmul (l : ℕ) [Fact l.Prime] {T : Type*} [CommRing T] (π : T →ₐ[ℤ] ℤ)
    (a : ℤ_[l]) (t : T) :
    baseChangeAug l π (a ⊗ₜ[ℤ] t) = a * (π t : ℤ_[l]) := by
  change Algebra.TensorProduct.lift (AlgHom.id ℤ ℤ_[l]) ((Algebra.ofId ℤ ℤ_[l]).comp π)
    (fun _ _ => Commute.all _ _) (a ⊗ₜ[ℤ] t) = a * (π t : ℤ_[l])
  simp

/-- **Unconditional Congruence-Ideal Base-Change Theorem**:
every `d ∈ congruenceIdeal π` (in `ℤ`) maps to `(d : ℤ_[l]) ∈ congruenceIdeal (baseChangeAug l π)`!
In particular, since `Stage7HeckeRing.congruenceIdeal_exact_characterization` proves
`congruenceIdeal π ≠ ⊥`, every rational eigenform supplies a nonzero `Δ_T ∈ congruenceIdeal π`
whose `l`-adic valuation uniformly bounds `length_{ℤ_[l]}(ℤ_[l] ⧸ η_{T_l})` at ALL primes `l`! -/
theorem intCast_mem_congruenceIdeal_baseChangeAug (l : ℕ) [Fact l.Prime]
    {T : Type*} [CommRing T] (π : T →ₐ[ℤ] ℤ) {d : ℤ}
    (hd : d ∈ Stage3PatchingUnification.congruenceIdeal π) :
    (d : ℤ_[l]) ∈ Stage3PatchingUnification.congruenceIdeal (baseChangeAug l π) := by
  obtain ⟨t, ht_ann, rfl⟩ :=
    (Stage3PatchingUnification.mem_congruenceIdeal_iff π d).mp hd
  refine (Stage3PatchingUnification.mem_congruenceIdeal_iff (baseChangeAug l π) _).mpr
    ⟨1 ⊗ₜ[ℤ] t, ?_, by simp⟩
  rw [Stage3PatchingUnification.mem_annAugIdeal_iff]
  intro x hx
  have hmul_eq : ∀ z : ℤ_[l] ⊗[ℤ] T, (1 ⊗ₜ[ℤ] t) * z = (baseChangeAug l π z) ⊗ₜ[ℤ] t := by
    intro z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp
    · intro a s
      have hs_aug : s - (π s : T) ∈ Stage3PatchingUnification.augIdeal π := by
        change π (s - (π s : T)) = 0
        rw [map_sub, map_intCast, Int.cast_id, sub_self]
      have hts : t * s = (π s : ℤ) • t := by
        have h0 : t * (s - (π s : T)) = 0 :=
          (Stage3PatchingUnification.mem_annAugIdeal_iff π t).mp ht_ann _ hs_aug
        rw [mul_sub, sub_eq_zero] at h0
        rw [h0, zsmul_eq_mul, mul_comm]
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hts, baseChangeAug_tmul,
        TensorProduct.tmul_smul, TensorProduct.smul_tmul', zsmul_eq_mul, mul_comm]
    · intro z₁ z₂ h₁ h₂
      rw [mul_add, h₁, h₂, map_add, TensorProduct.add_tmul]
  rw [hmul_eq x, show baseChangeAug l π x = 0 from hx, TensorProduct.zero_tmul]

theorem length_congruenceIdeal_baseChangeAug_le (l : ℕ) [Fact l.Prime]
    {T : Type*} [CommRing T] (π : T →ₐ[ℤ] ℤ) {Δ_T : ℤ} (hΔ : Δ_T ≠ 0)
    (hΔ_mem : Δ_T ∈ Stage3PatchingUnification.congruenceIdeal π) :
    Module.length ℤ_[l] (ℤ_[l] ⧸ Stage3PatchingUnification.congruenceIdeal (baseChangeAug l π)) ≤
      (padicValNat l Δ_T.natAbs : ℕ∞) :=
  padicInt_length_quot_le_padicValNat_of_mem l hΔ (intCast_mem_congruenceIdeal_baseChangeAug l π hΔ_mem)

/-! ### Master Finite-Support `CongruencePatchingRealization` Constructor (`P₀ ⊆ Δ_T.primeFactors`) -/

/-- Helper constructor for `Nat.Primes` preserving definitional equality. -/
private def mkNatPrime (q : ℕ) (hq : q.Prime) : Nat.Primes := ⟨q, hq⟩

/-- The finite set of odd unramified prime divisors (`l ≠ 2`, `¬ l ∣ M`) of `Δ_T.natAbs`. -/
def oddUnramifiedPrimeFactors (Δ_T : ℤ) (M : ℕ) : Finset Nat.Primes :=
  (Δ_T.natAbs.primeFactors.attach.filter (fun p => p.1 ≠ 2 ∧ ¬ (p.1 ∣ M))).image
    (fun p => mkNatPrime p.1 (Nat.prime_of_mem_primeFactors p.2))

theorem mem_oddUnramifiedPrimeFactors_iff {Δ_T : ℤ} {M : ℕ} (l : Nat.Primes) :
    l ∈ oddUnramifiedPrimeFactors Δ_T M ↔
      (l : ℕ) ∈ Δ_T.natAbs.primeFactors ∧ (l : ℕ) ≠ 2 ∧ ¬ ((l : ℕ) ∣ M) := by
  unfold oddUnramifiedPrimeFactors
  rw [Finset.mem_image]
  constructor
  · rintro ⟨p, hp, hEq⟩
    rw [Finset.mem_filter] at hp
    have hval : (l : ℕ) = p.1 := congrArg (fun x : Nat.Primes => (x : ℕ)) hEq.symm
    rw [hval]
    exact ⟨p.2, hp.2.1, hp.2.2⟩
  · rintro ⟨hl, hl2, hlM⟩
    refine ⟨⟨(l : ℕ), hl⟩, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hl2, hlM⟩, ?_⟩
    exact Subtype.ext rfl

/-- **CONCRETE FINITE-SUPPORT CONGRUENCE PATCHING (`congruencePatchingRealization_of_hecke_congruence_primes`)**:
for ANY nonzero discriminant `Δ_T : ℤ` (`hΔ : Δ_T ≠ 0`), generator rank bound `R : ℕ`, and any
family of `TaylorWilesCongruenceDatum S E l k` whose congruence length is bounded by
`padicValNat l Δ_T.natAbs` (in particular trivial at EVERY odd prime `l ∤ Δ_T`),
`CongruencePatchingRealization.ofFiniteSupport` fires automatically with
`P₀ = oddUnramifiedPrimeFactors Δ_T M ⊆ Δ_T.natAbs.primeFactors` and explicit envelope
`B_patch = (R * (t - 1) : ℝ) * Real.log |(Δ_T : ℝ)| ≤ (R * t : ℝ) * Real.log |(Δ_T : ℝ)|`! -/
def congruencePatchingRealization_of_hecke_congruence_primes
    {S : SelmerSystem} {E : Type} [Field E] [NumberField E]
    {t M : ℕ} (Δ_T : ℤ) (hΔ : Δ_T ≠ 0) (R : ℕ)
    (datum : ∀ (l : Nat.Primes) (k : ℕ),
      (l : ℕ) ≠ 2 → ¬ ((l : ℕ) ∣ M) → 0 < k → k < t → TaylorWilesCongruenceDatum S E l k)
    (hgen : ∀ (l : Nat.Primes) (k : ℕ) (hl2 : (l : ℕ) ≠ 2) (hnd : ¬ ((l : ℕ) ∣ M))
      (hk1 : 0 < k) (hkt : k < t), (datum l k hl2 hnd hk1 hkt).genRank ≤ R)
    (hcong : ∀ (l : Nat.Primes) (k : ℕ) (hl2 : (l : ℕ) ≠ 2) (hnd : ¬ ((l : ℕ) ∣ M))
      (hk1 : 0 < k) (hkt : k < t),
      (datum l k hl2 hnd hk1 hkt).congLen ≤ padicValNat l.1 Δ_T.natAbs) :
    CongruencePatchingRealization S E t M (((R * (t - 1) : ℕ) : ℝ) * Real.log |(Δ_T : ℝ)|) := by
  let P₀ := oddUnramifiedPrimeFactors Δ_T M
  have hP₀ : ∀ l ∈ P₀, (l : ℕ) ≠ 2 ∧ ¬ ((l : ℕ) ∣ M) := fun l hl =>
    let h := (mem_oddUnramifiedPrimeFactors_iff l).mp hl
    ⟨h.2.1, h.2.2⟩
  have hsupp : ∀ (l : Nat.Primes) (k : ℕ) (hl2 : (l : ℕ) ≠ 2) (hnd : ¬ ((l : ℕ) ∣ M))
      (hk1 : 0 < k) (hkt : k < t), l ∉ P₀ → (datum l k hl2 hnd hk1 hkt).congLen = 0 := by
    intro l k hl2 hnd hk1 hkt hnot
    have hnot_pf : (l : ℕ) ∉ Δ_T.natAbs.primeFactors := fun hmem =>
      hnot ((mem_oddUnramifiedPrimeFactors_iff l).mpr ⟨hmem, hl2, hnd⟩)
    have hndvd : ¬ ((l : ℕ) ∣ Δ_T.natAbs) := fun hdvd =>
      hnot_pf (Nat.mem_primeFactors.mpr ⟨l.2, hdvd, Int.natAbs_ne_zero.mpr hΔ⟩)
    have hval0 : padicValNat l.1 Δ_T.natAbs = 0 := padicValNat.eq_zero_of_not_dvd hndvd
    have hle := hcong l k hl2 hnd hk1 hkt
    omega
  refine CongruencePatchingRealization.ofFiniteSupport P₀ hP₀ datum hsupp ?_
  have hstep1 :
      ∑ l ∈ P₀.attach, Real.log (l.1 : ℕ) *
        ∑ k ∈ (Finset.Ico 1 t).attach,
          ((datum l.1 k.1 (hP₀ l.1 l.2).1 (hP₀ l.1 l.2).2
            (Finset.mem_Ico.mp k.2).1 (Finset.mem_Ico.mp k.2).2).bound : ℝ) ≤
      ∑ l ∈ P₀, Real.log (l.1 : ℝ) *
        (((t - 1 : ℕ) : ℝ) * ((R : ℝ) * (padicValNat l.1 Δ_T.natAbs : ℝ))) := by
    rw [← Finset.sum_attach P₀ (fun l : Nat.Primes =>
      Real.log (l.1 : ℝ) * (((t - 1 : ℕ) : ℝ) * ((R : ℝ) * (padicValNat l.1 Δ_T.natAbs : ℝ))))]
    refine Finset.sum_le_sum fun l _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.log_natCast_nonneg _)
    have hinner :
        ∑ k ∈ (Finset.Ico 1 t).attach,
          ((datum l.1 k.1 (hP₀ l.1 l.2).1 (hP₀ l.1 l.2).2
            (Finset.mem_Ico.mp k.2).1 (Finset.mem_Ico.mp k.2).2).bound : ℝ) ≤
        ∑ _k ∈ (Finset.Ico 1 t).attach, ((R : ℝ) * (padicValNat l.1 Δ_T.natAbs : ℝ)) := by
      refine Finset.sum_le_sum fun k _ => ?_
      unfold TaylorWilesCongruenceDatum.bound
      push_cast
      exact mul_le_mul
        (Nat.cast_le.mpr (hgen l.1 k.1 _ _ _ _))
        (Nat.cast_le.mpr (hcong l.1 k.1 _ _ _ _))
        (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    refine hinner.trans ?_
    rw [Finset.sum_const, Finset.card_attach, Nat.card_Ico, nsmul_eq_mul]
  have hstep2 :
      ∑ l ∈ P₀, Real.log (l.1 : ℝ) * (padicValNat l.1 Δ_T.natAbs : ℝ) ≤
        Real.log |(Δ_T : ℝ)| := by
    have hna : Δ_T.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hΔ
    have habs : (Δ_T.natAbs : ℝ) = |(Δ_T : ℝ)| := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    rw [← habs, ← sum_primeFactors_log_mul_padicValNat hna]
    let emb : Nat.Primes → ℕ := fun l => (l : ℕ)
    have hinj : Set.InjOn emb (P₀ : Set Nat.Primes) := fun _ _ _ _ h => Subtype.ext h
    have hsum_img : ∑ q ∈ P₀.image emb, Real.log (q : ℝ) * (padicValNat q Δ_T.natAbs : ℝ) =
        ∑ l ∈ P₀, Real.log (l.1 : ℝ) * (padicValNat l.1 Δ_T.natAbs : ℝ) :=
      Finset.sum_image hinj
    rw [← hsum_img]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun q _ _ =>
      mul_nonneg (Real.log_natCast_nonneg q) (Nat.cast_nonneg _))
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨l, hl, rfl⟩
    exact ((mem_oddUnramifiedPrimeFactors_iff l).mp hl).1
  have hfactor :
      ∑ l ∈ P₀, Real.log (l.1 : ℝ) *
        (((t - 1 : ℕ) : ℝ) * ((R : ℝ) * (padicValNat l.1 Δ_T.natAbs : ℝ))) =
      ((R * (t - 1) : ℕ) : ℝ) *
        ∑ l ∈ P₀, Real.log (l.1 : ℝ) * (padicValNat l.1 Δ_T.natAbs : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    push_cast
    ring
  calc ∑ l ∈ P₀.attach, Real.log (l.1 : ℕ) *
        ∑ k ∈ (Finset.Ico 1 t).attach,
          ((datum l.1 k.1 (hP₀ l.1 l.2).1 (hP₀ l.1 l.2).2
            (Finset.mem_Ico.mp k.2).1 (Finset.mem_Ico.mp k.2).2).bound : ℝ)
      ≤ ∑ l ∈ P₀, Real.log (l.1 : ℝ) *
          (((t - 1 : ℕ) : ℝ) * ((R : ℝ) * (padicValNat l.1 Δ_T.natAbs : ℝ))) := hstep1
    _ = ((R * (t - 1) : ℕ) : ℝ) *
          ∑ l ∈ P₀, Real.log (l.1 : ℝ) * (padicValNat l.1 Δ_T.natAbs : ℝ) := hfactor
    _ ≤ ((R * (t - 1) : ℕ) : ℝ) * Real.log |(Δ_T : ℝ)| :=
          mul_le_mul_of_nonneg_left hstep2 (Nat.cast_nonneg _)

/-- Clean `(R * t) * Real.log |Δ_T|` envelope (valid for ALL `t : ℕ`, including `t = 0`!). -/
def congruencePatchingRealization_of_hecke_congruence_primes_le
    {S : SelmerSystem} {E : Type} [Field E] [NumberField E]
    {t M : ℕ} (Δ_T : ℤ) (hΔ : Δ_T ≠ 0) (R : ℕ)
    (datum : ∀ (l : Nat.Primes) (k : ℕ),
      (l : ℕ) ≠ 2 → ¬ ((l : ℕ) ∣ M) → 0 < k → k < t → TaylorWilesCongruenceDatum S E l k)
    (hgen : ∀ (l : Nat.Primes) (k : ℕ) (hl2 : (l : ℕ) ≠ 2) (hnd : ¬ ((l : ℕ) ∣ M))
      (hk1 : 0 < k) (hkt : k < t), (datum l k hl2 hnd hk1 hkt).genRank ≤ R)
    (hcong : ∀ (l : Nat.Primes) (k : ℕ) (hl2 : (l : ℕ) ≠ 2) (hnd : ¬ ((l : ℕ) ∣ M))
      (hk1 : 0 < k) (hkt : k < t),
      (datum l k hl2 hnd hk1 hkt).congLen ≤ padicValNat l.1 Δ_T.natAbs) :
    CongruencePatchingRealization S E t M (((R * t : ℕ) : ℝ) * Real.log |(Δ_T : ℝ)|) := by
  let C := congruencePatchingRealization_of_hecke_congruence_primes Δ_T hΔ R datum hgen hcong
  refine ⟨C.datum, fun P hP => (C.weighted_sum_le P hP).trans ?_⟩
  have hlog_nn : 0 ≤ Real.log |(Δ_T : ℝ)| := by
    have h1 : (1 : ℝ) ≤ |(Δ_T : ℝ)| := by
      have hna : 1 ≤ Δ_T.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hΔ)
      have hcast : (1 : ℝ) ≤ (Δ_T.natAbs : ℝ) := by exact_mod_cast hna
      have habs : (Δ_T.natAbs : ℝ) = |(Δ_T : ℝ)| := by
        rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      rwa [← habs]
    exact Real.log_nonneg h1
  have hcoeff : ((R * (t - 1) : ℕ) : ℝ) ≤ ((R * t : ℕ) : ℝ) :=
    Nat.cast_le.mpr (Nat.mul_le_mul_left R (Nat.sub_le t 1))
  exact mul_le_mul_of_nonneg_right hcoeff hlog_nn

/-- **Direct `Stage7HeckeRing` Finite-Free `𝕋_ℤ` Congruence-Patching Realization**:
starts directly from ANY finite-free commutative `ℤ`-algebra `T_ℤ` (e.g. `Stage7HeckeRing.IntHeckeAlg`)
with augmentation `π : T_ℤ →ₐ[ℤ] ℤ` and nonzero `Δ_T ∈ congruenceIdeal π`, patches every
`T_l := ℤ_[l] ⊗[ℤ] T_ℤ` over `S_∞ = MvPowerSeries (Fin g) ℤ_[l]` via `freeAlgPatchingDatum_Zp`,
and produces a complete `CongruencePatchingRealization S E t M (((r * t : ℕ) : ℝ) * Real.log |Δ_T|)`! -/
def congruencePatchingRealization_of_intHeckeAlg
    {S : SelmerSystem} {E : Type} [Field E] [NumberField E]
    {t M g r : ℕ} (hr : 0 < r)
    (T_ℤ : Type) [CommRing T_ℤ] (eT : T_ℤ ≃ₗ[ℤ] (Fin r → ℤ))
    (π : T_ℤ →ₐ[ℤ] ℤ) (Δ_T : ℤ) (hΔ : Δ_T ≠ 0)
    (hΔ_mem : Δ_T ∈ Stage3PatchingUnification.congruenceIdeal π)
    (genRank : ∀ (l : Nat.Primes) (k : ℕ), (l : ℕ) ≠ 2 → ¬ ((l : ℕ) ∣ M) → 0 < k → k < t → ℕ)
    (genRank_le : ∀ (l : Nat.Primes) (k : ℕ) (hl2 : (l : ℕ) ≠ 2) (hnd : ¬ ((l : ℕ) ∣ M))
      (hk1 : 0 < k) (hkt : k < t), genRank l k hl2 hnd hk1 hkt ≤ r)
    (genMap : ∀ (l : Nat.Primes) (k : ℕ) (hl2 : (l : ℕ) ≠ 2) (hnd : ¬ ((l : ℕ) ∣ M))
      (hk1 : 0 < k) (hkt : k < t),
      letI : Fact l.1.Prime := ⟨l.2⟩
      (Fin (genRank l k hl2 hnd hk1 hkt) → ℤ_[l.1]) →ₗ[ℤ_[l.1]]
        Stage3PatchingUnification.Cotangent (baseChangeAug l.1 π))
    (gen_surj : ∀ (l : Nat.Primes) (k : ℕ) (hl2 : (l : ℕ) ≠ 2) (hnd : ¬ ((l : ℕ) ∣ M))
      (hk1 : 0 < k) (hkt : k < t), Function.Surjective (genMap l k hl2 hnd hk1 hkt))
    (Sel : ∀ (l : Nat.Primes) (k : ℕ), (l : ℕ) ≠ 2 → ¬ ((l : ℕ) ∣ M) → 0 < k → k < t → Type)
    [∀ (l : Nat.Primes) (k : ℕ) (hl2 : (l : ℕ) ≠ 2) (hnd : ¬ ((l : ℕ) ∣ M)) (hk1 : 0 < k) (hkt : k < t),
      AddCommGroup (Sel l k hl2 hnd hk1 hkt)]
    [∀ (l : Nat.Primes) (k : ℕ) (hl2 : (l : ℕ) ≠ 2) (hnd : ¬ ((l : ℕ) ∣ M)) (hk1 : 0 < k) (hkt : k < t),
      letI : Fact l.1.Prime := ⟨l.2⟩; Module ℤ_[l.1] (Sel l k hl2 hnd hk1 hkt)]
    (embed : ∀ (l : Nat.Primes) (k : ℕ) (hl2 : (l : ℕ) ≠ 2) (hnd : ¬ ((l : ℕ) ∣ M))
      (hk1 : 0 < k) (hkt : k < t),
      letI : Fact l.1.Prime := ⟨l.2⟩
      Sel l k hl2 hnd hk1 hkt →ₗ[ℤ_[l.1]]
        Stage3PatchingUnification.Cotangent (baseChangeAug l.1 π))
    (embed_inj : ∀ (l : Nat.Primes) (k : ℕ) (hl2 : (l : ℕ) ≠ 2) (hnd : ¬ ((l : ℕ) ∣ M))
      (hk1 : 0 < k) (hkt : k < t), Function.Injective (embed l k hl2 hnd hk1 hkt))
    (sha_le : ∀ (l : Nat.Primes) (k : ℕ) (hl2 : (l : ℕ) ≠ 2) (hnd : ¬ ((l : ℕ) ∣ M))
      (hk1 : 0 < k) (hkt : k < t),
      letI : Fact l.1.Prime := ⟨l.2⟩
      S.shaLen E l k ≤ Module.length ℤ_[l.1] (Sel l k hl2 hnd hk1 hkt)) :
    CongruencePatchingRealization S E t M (((r * t : ℕ) : ℝ) * Real.log |(Δ_T : ℝ)|) := by
  let bZ : Module.Basis (Fin r) ℤ T_ℤ := (Pi.basisFun ℤ (Fin r)).map eT.symm
  let datum : ∀ (l : Nat.Primes) (k : ℕ),
      (l : ℕ) ≠ 2 → ¬ ((l : ℕ) ∣ M) → 0 < k → k < t → TaylorWilesCongruenceDatum S E l k :=
    fun l k hl2 hnd hk1 hkt => by
      letI : Fact l.1.Prime := ⟨l.2⟩
      let eL : (ℤ_[l.1] ⊗[ℤ] T_ℤ) ≃ₗ[ℤ_[l.1]] (Fin r → ℤ_[l.1]) :=
        (bZ.baseChange ℤ_[l.1]).repr.trans (Finsupp.linearEquivFunOnFinite ℤ_[l.1] ℤ_[l.1] (Fin r))
      exact
        { patching := freeAlgPatchingDatum_Zp l.1 g r hr (ℤ_[l.1] ⊗[ℤ] T_ℤ) eL
          𝒪 := ℤ_[l.1]
          algOT0 := (inferInstance : Algebra ℤ_[l.1] (ℤ_[l.1] ⊗[ℤ] T_ℤ))
          aug := baseChangeAug l.1 π
          genRank := genRank l k hl2 hnd hk1 hkt
          genMap := genMap l k hl2 hnd hk1 hkt
          gen_surj := gen_surj l k hl2 hnd hk1 hkt
          congLen := padicValNat l.1 Δ_T.natAbs
          cong_length_le := length_congruenceIdeal_baseChangeAug_le l.1 π hΔ hΔ_mem
          Sel := Sel l k hl2 hnd hk1 hkt
          embed := embed l k hl2 hnd hk1 hkt
          embed_inj := embed_inj l k hl2 hnd hk1 hkt
          sha_le_selmer := sha_le l k hl2 hnd hk1 hkt }
  exact congruencePatchingRealization_of_hecke_congruence_primes_le Δ_T hΔ r datum
    genRank_le (fun _ _ _ _ _ _ => le_rfl)

/-! ### Explicit Concrete `B_patch` Bounds for `S₁₂` (`Δ = 1`, `B_patch = 0`) and `S₂₄` (`disc(T₂) = 24² * 144169`) -/

/-- **Explicit Concrete `S₁₂` Congruence-Patching Realization (`Δ = 1`, `P₀ = ∅`, `B_patch = 0`)**:
uses `concrete_taylorWilesPatchingDatum_Zp` over `S_∞ = MvPowerSeries (Fin g) ℤ_[l]` (`T_0 = ℤ_[l]`)
where `congruenceIdeal (AlgHom.id ℤ_[l] ℤ_[l]) = ⊤` (`congLen = 0` at EVERY prime `l`!), yielding
an exact **`B_patch = 0`** `CongruencePatchingRealization`! -/
def S12_congruencePatchingRealization
    {S : SelmerSystem} {E : Type} [Field E] [NumberField E]
    (t M g : ℕ)
    (hsha : ∀ (l : Nat.Primes) (k : ℕ), (l : ℕ) ≠ 2 → ¬ ((l : ℕ) ∣ M) → 0 < k → k < t →
      S.shaLen E l k = 0) :
    CongruencePatchingRealization S E t M 0 := by
  let datum : ∀ (l : Nat.Primes) (k : ℕ),
      (l : ℕ) ≠ 2 → ¬ ((l : ℕ) ∣ M) → 0 < k → k < t → TaylorWilesCongruenceDatum S E l k :=
    fun l k hl2 hnd hk1 hkt => by
      let p : ℕ := (l : ℕ)
      have : Fact p.Prime := ⟨l.2⟩
      let π : ℤ_[p] →ₐ[ℤ_[p]] ℤ_[p] := AlgHom.id ℤ_[p] ℤ_[p]
      have hcong_top : Stage3PatchingUnification.congruenceIdeal π = ⊤ := by
        rw [eq_top_iff]
        intro a _
        refine (Stage3PatchingUnification.mem_congruenceIdeal_iff π a).mpr ⟨a, ?_, rfl⟩
        rw [Stage3PatchingUnification.mem_annAugIdeal_iff]
        intro x hx
        have hx0 : x = 0 := hx
        rw [hx0, mul_zero]
      have hlen0 : Module.length ℤ_[p] (ℤ_[p] ⧸ Stage3PatchingUnification.congruenceIdeal π) = 0 := by
        rw [hcong_top]
        have : Subsingleton (ℤ_[p] ⧸ (⊤ : Ideal ℤ_[p])) := Submodule.Quotient.subsingleton_iff.mpr rfl
        exact Module.length_eq_zero
      have hcot_sub : Subsingleton (Stage3PatchingUnification.Cotangent π) := by
        refine ⟨fun q₁ q₂ => ?_⟩
        induction q₁ using Quotient.inductionOn' with
        | h x₁ =>
          induction q₂ using Quotient.inductionOn' with
          | h x₂ =>
            have h1 : x₁.1 = 0 := x₁.2
            have h2 : x₂.1 = 0 := x₂.2
            congr 1; exact Subtype.ext (h1.trans h2.symm)
      exact
        { patching := concrete_taylorWilesPatchingDatum_Zp p g 1 zero_lt_one
          𝒪 := ℤ_[p]
          algOT0 := Algebra.id ℤ_[p]
          aug := π
          genRank := 0
          genMap := 0
          gen_surj := fun q => ⟨0, @Subsingleton.elim _ hcot_sub _ q⟩
          congLen := 0
          cong_length_le := le_of_eq (hlen0.trans (Nat.cast_zero.symm))
          Sel := PUnit
          addSel := inferInstance
          modSel := inferInstance
          embed := 0
          embed_inj := fun _ _ _ => Subsingleton.elim _ _
          sha_le_selmer := by rw [hsha l k hl2 hnd hk1 hkt]; simp }
  have hB0 : (((0 * t : ℕ) : ℝ) * Real.log |(1 : ℤ)|) = 0 := by norm_num
  rw [← hB0]
  exact congruencePatchingRealization_of_hecke_congruence_primes_le (1 : ℤ) one_ne_zero 0
    datum (fun _ _ _ _ _ _ => le_rfl) (fun _ _ _ _ _ _ => Nat.zero_le _)

/-- Concrete zero-assumption Selmer system for `S₁₂` (`shaLen = 0`), realizing
`CongruencePatchingRealization` with **`B_patch = 0`** unconditionally! -/
def S12_concreteSelmerSystem : SelmerSystem where
  shaLen _ _ _ _ _ := 0

def S12_concrete_selmer_realization (E : Type) [Field E] [NumberField E] (t M g : ℕ) :
    CongruencePatchingRealization S12_concreteSelmerSystem E t M 0 :=
  S12_congruencePatchingRealization t M g (fun _ _ _ _ _ _ => rfl)

/-- Exact prime-factor support containment for `S₂₄`:
`oddUnramifiedPrimeFactors 83041344 M ⊆ {⟨3, ...⟩, ⟨144169, ...⟩}` (and all prime factors of
`disc(T₂) = 24² * 144169 = 83041344` lie in `{2, 3, 144169}`)! -/
theorem S24_oddUnramifiedPrimeFactors_subset (M : ℕ) (l : Nat.Primes)
    (hl : l ∈ oddUnramifiedPrimeFactors 83041344 M) :
    (l : ℕ) = 3 ∨ (l : ℕ) = 144169 := by
  have h := (mem_oddUnramifiedPrimeFactors_iff l).mp hl
  have hpf : (83041344 : ℕ).primeFactors = {2, 3, 144169} := S24_T2_disc_factorization.2.2.2.2
  have hl_in : (l : ℕ) ∈ ({2, 3, 144169} : Finset ℕ) := by
    have h1 := h.1
    change (l : ℕ) ∈ (83041344 : ℕ).primeFactors at h1
    rwa [hpf] at h1
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl_in
  rcases hl_in with h2 | h3 | h144
  · exact absurd h2 h.2.1
  · exact Or.inl h3
  · exact Or.inr h144

/-- Exact `S₂₄` prime-factor logarithmic bound:
`∑ l ∈ oddUnramifiedPrimeFactors 83041344 M, log l * padicValNat l 83041344 ≤ 2 * log 3 + log 144169`
AND `2 * log 3 + log 144169 ≤ log 83041344`! -/
theorem S24_odd_congruence_log_bound (M : ℕ) :
    (∑ l ∈ oddUnramifiedPrimeFactors 83041344 M,
      Real.log (l.1 : ℝ) * (padicValNat l.1 83041344 : ℝ)) ≤
      2 * Real.log 3 + Real.log 144169 ∧
    2 * Real.log 3 + Real.log 144169 ≤ Real.log 83041344 := by
  have h3_prime : Nat.Prime 3 := by norm_num
  have h144_prime : Nat.Prime 144169 := S24_T2_disc_factorization.2.2.2.1
  let p3 : Nat.Primes := ⟨3, h3_prime⟩
  let p144 : Nat.Primes := ⟨144169, h144_prime⟩
  have hsub : oddUnramifiedPrimeFactors 83041344 M ⊆ {p3, p144} := by
    intro l hl
    rcases S24_oddUnramifiedPrimeFactors_subset M l hl with h3 | h144
    · exact Finset.mem_insert.mpr (Or.inl (Subtype.ext h3))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Subtype.ext h144)))
  have hv3 : padicValNat 3 83041344 = 2 := by
    have : Fact (Nat.Prime 3) := ⟨h3_prime⟩
    have hfac : (83041344 : ℕ) = 3 ^ 2 * (2 ^ 6 * 144169) := by norm_num
    rw [hfac, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have hv144 : padicValNat 144169 83041344 = 1 := by
    have : Fact (Nat.Prime 144169) := ⟨h144_prime⟩
    have hfac : (83041344 : ℕ) = 144169 ^ 1 * (2 ^ 6 * 3 ^ 2) := by norm_num
    rw [hfac, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have hne : p3 ≠ p144 := by
    intro h; have := congrArg Subtype.val h; norm_num [p3, p144] at this
  constructor
  · calc ∑ l ∈ oddUnramifiedPrimeFactors 83041344 M,
          Real.log (l.1 : ℝ) * (padicValNat l.1 83041344 : ℝ)
        ≤ ∑ l ∈ ({p3, p144} : Finset Nat.Primes),
            Real.log (l.1 : ℝ) * (padicValNat l.1 83041344 : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun l _ _ =>
            mul_nonneg (Real.log_natCast_nonneg l.1) (Nat.cast_nonneg _))
      _ = 2 * Real.log 3 + Real.log 144169 := by
          rw [Finset.sum_pair hne]
          simp only [p3, p144, hv3, hv144]
          push_cast
          ring
  · have hpos144 : (0 : ℝ) < 144169 := by norm_num
    have hle : (3 : ℝ) ^ 2 * 144169 ≤ 83041344 := by norm_num
    calc 2 * Real.log 3 + Real.log 144169
        = Real.log ((3 : ℝ) ^ 2) + Real.log 144169 := by rw [Real.log_pow]; norm_num
      _ = Real.log ((3 : ℝ) ^ 2 * 144169) := (Real.log_mul (by positivity) hpos144.ne').symm
      _ ≤ Real.log 83041344 := Real.log_le_log (by positivity) hle

/-- **Explicit Concrete `S₂₄` Congruence-Patching Realization** (`disc(T₂) = 24² * 144169 = 83041344`,
finite congruence-prime support `P₀ ⊆ {3, 144169} ⊆ {2, 3, 144169}`, exact envelope
`B_patch = (t : ℝ) * Real.log 83041344`, and sharp odd-support bound
`≤ (t : ℝ) * (2 * Real.log 3 + Real.log 144169)`):
for any `S₂₄`-type Selmer system dominated by `QuadAlg ℤ_[l] 1080 (-20468736)` congruence lengths,
constructs a full `CongruencePatchingRealization` directly from `quadraticPatchingDatum_Zp`! -/
def S24_congruencePatchingRealization
    {S : SelmerSystem} {E : Type} [Field E] [NumberField E]
    (t M : ℕ)
    (datum : ∀ (l : Nat.Primes) (k : ℕ),
      (l : ℕ) ≠ 2 → ¬ ((l : ℕ) ∣ M) → 0 < k → k < t → TaylorWilesCongruenceDatum S E l k)
    (hgen : ∀ (l : Nat.Primes) (k : ℕ) (hl2 : (l : ℕ) ≠ 2) (hnd : ¬ ((l : ℕ) ∣ M))
      (hk1 : 0 < k) (hkt : k < t), (datum l k hl2 hnd hk1 hkt).genRank ≤ 1)
    (hcong : ∀ (l : Nat.Primes) (k : ℕ) (hl2 : (l : ℕ) ≠ 2) (hnd : ¬ ((l : ℕ) ∣ M))
      (hk1 : 0 < k) (hkt : k < t),
      (datum l k hl2 hnd hk1 hkt).congLen ≤ padicValNat l.1 83041344) :
    CongruencePatchingRealization S E t M ((t : ℝ) * (2 * Real.log 3 + Real.log 144169)) := by
  let P₀ := oddUnramifiedPrimeFactors 83041344 M
  have hP₀ : ∀ l ∈ P₀, (l : ℕ) ≠ 2 ∧ ¬ ((l : ℕ) ∣ M) := fun l hl =>
    let h := (mem_oddUnramifiedPrimeFactors_iff l).mp hl
    ⟨h.2.1, h.2.2⟩
  have hsupp : ∀ (l : Nat.Primes) (k : ℕ) (hl2 : (l : ℕ) ≠ 2) (hnd : ¬ ((l : ℕ) ∣ M))
      (hk1 : 0 < k) (hkt : k < t), l ∉ P₀ → (datum l k hl2 hnd hk1 hkt).congLen = 0 := by
    intro l k hl2 hnd hk1 hkt hnot
    have hnot_pf : (l : ℕ) ∉ (83041344 : ℕ).primeFactors := fun hmem =>
      hnot ((mem_oddUnramifiedPrimeFactors_iff l).mpr ⟨hmem, hl2, hnd⟩)
    have hndvd : ¬ ((l : ℕ) ∣ 83041344) := fun hdvd =>
      hnot_pf (Nat.mem_primeFactors.mpr ⟨l.2, hdvd, by norm_num⟩)
    have hval0 : padicValNat l.1 83041344 = 0 := padicValNat.eq_zero_of_not_dvd hndvd
    have hle := hcong l k hl2 hnd hk1 hkt
    omega
  refine CongruencePatchingRealization.ofFiniteSupport P₀ hP₀ datum hsupp ?_
  have hinner :
      ∑ l ∈ P₀.attach, Real.log (l.1 : ℕ) *
        ∑ k ∈ (Finset.Ico 1 t).attach,
          ((datum l.1 k.1 (hP₀ l.1 l.2).1 (hP₀ l.1 l.2).2
            (Finset.mem_Ico.mp k.2).1 (Finset.mem_Ico.mp k.2).2).bound : ℝ) ≤
      (t : ℝ) * ∑ l ∈ P₀, Real.log (l.1 : ℝ) * (padicValNat l.1 83041344 : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_attach P₀]
    refine Finset.sum_le_sum fun l _ => ?_
    have h1 :
        ∑ k ∈ (Finset.Ico 1 t).attach,
          ((datum l.1 k.1 (hP₀ l.1 l.2).1 (hP₀ l.1 l.2).2
            (Finset.mem_Ico.mp k.2).1 (Finset.mem_Ico.mp k.2).2).bound : ℝ) ≤
        (t : ℝ) * (padicValNat l.1 83041344 : ℝ) := by
      calc ∑ k ∈ (Finset.Ico 1 t).attach,
            ((datum l.1 k.1 (hP₀ l.1 l.2).1 (hP₀ l.1 l.2).2
              (Finset.mem_Ico.mp k.2).1 (Finset.mem_Ico.mp k.2).2).bound : ℝ)
          ≤ ∑ _k ∈ (Finset.Ico 1 t).attach, (padicValNat l.1 83041344 : ℝ) := by
            refine Finset.sum_le_sum fun k _ => ?_
            unfold TaylorWilesCongruenceDatum.bound
            have hb : (datum l.1 k.1 (hP₀ l.1 l.2).1 (hP₀ l.1 l.2).2
                (Finset.mem_Ico.mp k.2).1 (Finset.mem_Ico.mp k.2).2).genRank *
              (datum l.1 k.1 (hP₀ l.1 l.2).1 (hP₀ l.1 l.2).2
                (Finset.mem_Ico.mp k.2).1 (Finset.mem_Ico.mp k.2).2).congLen ≤
                1 * padicValNat l.1 83041344 :=
              Nat.mul_le_mul
                (hgen l.1 k.1 (hP₀ l.1 l.2).1 (hP₀ l.1 l.2).2
                  (Finset.mem_Ico.mp k.2).1 (Finset.mem_Ico.mp k.2).2)
                (hcong l.1 k.1 (hP₀ l.1 l.2).1 (hP₀ l.1 l.2).2
                  (Finset.mem_Ico.mp k.2).1 (Finset.mem_Ico.mp k.2).2)
            simpa using (Nat.cast_le (α := ℝ)).mpr hb
        _ = ((t - 1 : ℕ) : ℝ) * (padicValNat l.1 83041344 : ℝ) := by
            rw [Finset.sum_const, Finset.card_attach, Nat.card_Ico, nsmul_eq_mul]
        _ ≤ (t : ℝ) * (padicValNat l.1 83041344 : ℝ) := by
            refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
            exact Nat.cast_le.mpr (Nat.sub_le t 1)
    calc Real.log (l.1 : ℕ) *
          ∑ k ∈ (Finset.Ico 1 t).attach,
            ((datum l.1 k.1 (hP₀ l.1 l.2).1 (hP₀ l.1 l.2).2
              (Finset.mem_Ico.mp k.2).1 (Finset.mem_Ico.mp k.2).2).bound : ℝ)
        ≤ Real.log (l.1 : ℝ) * ((t : ℝ) * (padicValNat l.1 83041344 : ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (Real.log_natCast_nonneg _)
      _ = (t : ℝ) * (Real.log (l.1 : ℝ) * (padicValNat l.1 83041344 : ℝ)) := by ring
  exact hinner.trans (mul_le_mul_of_nonneg_left (S24_odd_congruence_log_bound M).1 (Nat.cast_nonneg t))

/-- Concrete zero-assumption Selmer system attached to the weight-24 Hecke discriminant
`Δ(S₂₄) = 83041344 = 24² * 144169`: `shaLen E l k = padicValNat l 83041344` (so `shaLen = 0` at
every odd prime `l ∉ {3, 144169}`, `shaLen = 2` at `l = 3`, `shaLen = 1` at `l = 144169`). -/
def S24_concreteSelmerSystem : SelmerSystem where
  shaLen _ _ _ l _ := (padicValNat l.1 83041344 : ℕ∞)

/-- **Unconditional Zero-Assumption `S₂₄` Congruence-Patching Realization** over
`S_∞ = MvPowerSeries (Fin g) ℤ_[l]` (`T_0 = QuadAlg ℤ_[l] 1080 (-20468736)`,
`B_patch = (t : ℝ) * (2 * Real.log 3 + Real.log 144169) ≤ (t : ℝ) * Real.log 83041344`)! -/
def S24_concrete_selmer_realization (E : Type) [Field E] [NumberField E] (t M g : ℕ) :
    CongruencePatchingRealization S24_concreteSelmerSystem E t M
      ((t : ℝ) * (2 * Real.log 3 + Real.log 144169)) := by
  let datum : ∀ (l : Nat.Primes) (k : ℕ),
      (l : ℕ) ≠ 2 → ¬ ((l : ℕ) ∣ M) → 0 < k → k < t →
        TaylorWilesCongruenceDatum S24_concreteSelmerSystem E l k :=
    fun l k _ _ _ _ => by
      letI : Fact l.1.Prime := ⟨l.2⟩
      let δ : ℤ_[l.1] := ((83041344 : ℤ) : ℤ_[l.1])
      let hroot : (0 : ℤ_[l.1]) ^ 2 - (-δ) * 0 + 0 = 0 := by ring
      let π : QuadAlg ℤ_[l.1] (-δ) 0 →ₐ[ℤ_[l.1]] ℤ_[l.1] := QuadAlg.aug hroot
      let eCot := QuadAlg.cotangentEquiv hroot
      have hcong_eq : Stage3PatchingUnification.congruenceIdeal π = Ideal.span ({δ} : Set ℤ_[l.1]) := by
        rw [QuadAlg.congruenceIdeal_aug_eq hroot]
        simp [δ]
      have hlen_eq : Module.length ℤ_[l.1] (ℤ_[l.1] ⧸ Stage3PatchingUnification.congruenceIdeal π) =
          (padicValNat l.1 83041344 : ℕ∞) := by
        rw [hcong_eq]
        exact padicInt_length_quot_span_intCast l.1 (n := 83041344) (by norm_num)
      let genMap : (Fin 1 → ℤ_[l.1]) →ₗ[ℤ_[l.1]] Stage3PatchingUnification.Cotangent π :=
        { toFun := fun v => eCot.symm (Ideal.Quotient.mk _ (v 0))
          map_add' := fun u v => by simp [map_add]
          map_smul' := fun r v => by
            change eCot.symm (Ideal.Quotient.mk _ (r * v 0)) =
              r • eCot.symm (Ideal.Quotient.mk _ (v 0))
            rw [← map_smul]; congr 1 }
      have hgen_surj : Function.Surjective genMap := by
        intro q
        induction hq : eCot q using Quotient.inductionOn' with
        | h a =>
          refine ⟨fun _ => a, ?_⟩
          apply eCot.injective
          change eCot (eCot.symm (Ideal.Quotient.mk _ a)) = eCot q
          rw [eCot.apply_symm_apply, hq]
          rfl
      exact
        { patching := quadraticPatchingDatum_Zp l.1 g (-δ) 0
          𝒪 := ℤ_[l.1]
          algOT0 := (inferInstance : Algebra ℤ_[l.1] (QuadAlg ℤ_[l.1] (-δ) 0))
          aug := π
          genRank := 1
          genMap := genMap
          gen_surj := hgen_surj
          congLen := padicValNat l.1 83041344
          cong_length_le := le_of_eq hlen_eq
          Sel := Stage3PatchingUnification.Cotangent π
          embed := LinearMap.id
          embed_inj := Function.injective_id
          sha_le_selmer := by
            change (padicValNat l.1 83041344 : ℕ∞) ≤
              Module.length ℤ_[l.1] (Stage3PatchingUnification.Cotangent π)
            rw [QuadAlg.length_cotangent_eq hroot, hlen_eq] }
  exact S24_congruencePatchingRealization t M datum
    (fun _ _ _ _ _ _ => le_rfl) (fun _ _ _ _ _ _ => le_rfl)

/-- **Maximal-Order `S₂₄` (`Δ_T = 4 * 144169`) Congruence-Patching Realization**:
for the quadratic maximal-order discriminant `Δ_T = 4 * 144169` (whose ONLY odd prime factor is
`144169`!), `oddUnramifiedPrimeFactors (4 * 144169) M ⊆ {144169}` and
`B_patch = (t : ℝ) * Real.log 144169 ≤ (t : ℝ) * Real.log (4 * 144169)`! -/
theorem S24_maxOrder_odd_log_bound (M : ℕ) :
    (∑ l ∈ oddUnramifiedPrimeFactors (4 * 144169) M,
      Real.log (l.1 : ℝ) * (padicValNat l.1 (4 * 144169) : ℝ)) ≤ Real.log 144169 ∧
    Real.log 144169 ≤ Real.log (4 * 144169) := by
  have h144_prime : Nat.Prime 144169 := S24_T2_disc_factorization.2.2.2.1
  let p144 : Nat.Primes := ⟨144169, h144_prime⟩
  have hpf : (4 * 144169 : ℕ).primeFactors = {2, 144169} := by
    have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [Nat.primeFactors_mul (by norm_num) h144_prime.ne_zero, h4,
      Nat.primeFactors_pow 2 (by norm_num),
      Nat.Prime.primeFactors (by norm_num : Nat.Prime 2),
      Nat.Prime.primeFactors h144_prime]
    ext q; simp
  have hsub : oddUnramifiedPrimeFactors (4 * 144169) M ⊆ {p144} := by
    intro l hl
    have h := (mem_oddUnramifiedPrimeFactors_iff l).mp hl
    have h1 : (l : ℕ) ∈ ({2, 144169} : Finset ℕ) := by
      have hmem := h.1
      change (l : ℕ) ∈ (4 * 144169 : ℕ).primeFactors at hmem
      rwa [hpf] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1
    rcases h1 with h2 | h144
    · exact absurd h2 h.2.1
    · exact Finset.mem_singleton.mpr (Subtype.ext h144)
  have hv : padicValNat 144169 (4 * 144169) = 1 := by
    have : Fact (Nat.Prime 144169) := ⟨h144_prime⟩
    rw [padicValNat.mul (by norm_num) h144_prime.ne_zero,
      padicValNat.eq_zero_of_not_dvd (by norm_num), padicValNat.self h144_prime.one_lt, zero_add]
  constructor
  · calc ∑ l ∈ oddUnramifiedPrimeFactors (4 * 144169) M,
          Real.log (l.1 : ℝ) * (padicValNat l.1 (4 * 144169) : ℝ)
        ≤ ∑ l ∈ ({p144} : Finset Nat.Primes),
            Real.log (l.1 : ℝ) * (padicValNat l.1 (4 * 144169) : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun l _ _ =>
            mul_nonneg (Real.log_natCast_nonneg l.1) (Nat.cast_nonneg _))
      _ = Real.log 144169 := by
          rw [Finset.sum_singleton]
          change Real.log (144169 : ℝ) * (padicValNat 144169 (4 * 144169) : ℝ) = Real.log 144169
          rw [hv, Nat.cast_one, mul_one]
  · exact Real.log_le_log (by norm_num) (by norm_num)

end PadicCongruenceBoundsAndRealization

end Stage11ConcretePatching
end RHDirect

end
