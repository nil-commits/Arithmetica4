import RHDirect.Interfaces
import RHDirect.TaylorWilesWindow
import RHDirect.Stage2GaloisWire
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.FiniteLength
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.CharP.Lemmas

/-!
# RHDirect.Stage2IwasawaTwoTower

Compact, direct, zero-`sorry`, zero-custom-`axiom` Lean 4 formalization of the **`l = 2` Iwasawa
2-Tower & Ferrero–Washington (`μ = 0`)** branch (`B₂`) of `Stage2GaloisWire.ThreePartPatchingWindow`
against `RHDirect.Interfaces`, `RHDirect.TaylorWilesWindow`, `RHDirect.Stage2GaloisWire`, and
targeted Mathlib `v4.33.1`.

## Contents

1. **`p`-adic Integers `ℤ_[p]`, Simple Residue Module & Exact Length-to-Cardinality Bridge**:
   - Exact residue isomorphism `PadicInt p ⧸ Ideal.span {(p : PadicInt p)} ≃+* ZMod p`,
     simplicity `IsSimpleModule (PadicInt p) (PadicInt p ⧸ Ideal.span {(p : PadicInt p)})`,
     unit criterion `padicInt_isUnit_one_add_p_mul`, and exact length
     `Module.length (PadicInt p) (PadicInt p ⧸ Ideal.span {(p : PadicInt p) ^ k}) = k`.
   - Exact length-to-cardinality theorem `padicInt_card_eq_pow_length`: for EVERY finite-length
     `ℤ_[p]`-module `A`, `Finite A` and `Nat.card A = p ^ (Module.length (PadicInt p) A).toNat`.

2. **Concrete Iwasawa Algebra `Λ_p = PowerSeries (PadicInt p)` & Finite-Level Quotients `M / ω_n M`**:
   - Cyclotomic layer elements `ω_n = (1 + T)^(p^n) - 1` and relative cyclotomic factors
     `Φ_n = ∑_{j < p} ((1 + T)^(p^n))^j` with exact factorization `ω_{n+1} = ω_n * Φ_n` and
     exact mod-`p` Frobenius reduction `ω_n ≡ T^(p^n) (mod p)`.
   - General `Λ_p`-module quotient length subadditivity, exactness under injectivity, monotonicity
     across tower levels `m ≤ n`, and the **Pseudo-Isomorphism Transfer Inequality**
     `length(M / ω_n M) ≤ length(E / ω_n E) + length(ker φ) + length(coker φ)`.

3. **Elementary Iwasawa Modules & Exact `p`-adic Length Growth**:
   - `p`-power torsion elementary modules `Λ_p / (p^m)`: exact `ℤ_[p]`-length
     `Module.length (PadicInt p) (LayerQuot p n (ElemPTorsion p m)) = m * p ^ n`.
   - Distinguished `ℤ_[p]`-free lattices `DistinguishedLattice p lam`: proves `ω_n ∈ p • End` for
     `p^n ≥ d`, `ω_{n+1} ∈ p^2 • End`, `Φ_{n+1} = p • (1 + p • B)`, matrix-determinant
     invertibility of `1 + p • B` over `ℤ_[p]`, exact step length `length(F / Φ_k F) = lam`,
     and exact linear growth `e_n = λ * n + ν` (for all primes `p`, including `p = 2`!).

4. **Iwasawa Length Growth Formula & Ferrero–Washington (`μ = 0`)**:
   - `iwasawa_length_growth_formula`: `e_n ≤ λ * n + μ * p^n + ν` and
     `|A_n| ≤ p ^ (λ * n + μ * p^n + ν)` for every `IwasawaModuleModel p M`.
   - `ferrero_washington_card_bound`: `μ = 0 ⇒ |A_n| ≤ C * p ^ (λ * n)` with `C = p ^ ν`.
   - Non-vacuity witness `concreteTwoTowerModel` over `ℤ_[2][[T]]`.

5. **Quantitative `PageN` Exponential Domination (`μ = 0` vs `μ ≥ 1`)**:
   - `ferrero_washington_card_lt_exp_rpow_of_pageN`: for `μ = 0`, `C * 2 ^ (λ * e) < exp(x^(4ε/5))`
     and `< exp(x^ε)` on `PageN` windows!
   - `mu_pos_card_gt_exp_rpow_of_pageN`: sharp contrast proving `μ ≥ 1 ⇒ exp(x^ε) < 2 ^ (μ * 2^e)`
     on `PageN` windows (why Ferrero–Washington `μ = 0` is indispensable!).
   - `iwasawa_two_sum_le_exp_of_admissible`: absorbs the `1 ≤ k < t x` sum of `μ = 0` Iwasawa
     2-tower lengths into `Real.exp (x ^ (4 * eps / 5)) * Real.log 2`.

6. **Direct Discharge of `B₂` into `TaylorWilesWindow.vvle_of_three_parts` & `ThreePartPatchingWindow`**:
   - `IwasawaTwoTowerBound` / `IwasawaTwoTowerRealization` discharging `l = 2` finiteness and sum
     bounds directly into `TaylorWilesWindow.vvle_of_three_parts` and
     `Stage2GaloisWire.vvle_of_patching_three_parts`.
   - `threePartPatchingWindow_of_iwasawa` and `galoisModularityContract_of_iwasawa`: discharges the
     `l = 2` branch of `Stage2GaloisWire.ThreePartPatchingWindow` cleanly into
     `RHDirect.GaloisModularityContract S` (`VWin S`).

Zero `sorry`, zero custom `axiom`s.
-/

noncomputable section

open scoped BigOperators
open Real Finset Filter RHDirect

namespace RHDirect.Stage2IwasawaTwoTower

/-! ## Section 1: `p`-adic Integers `ℤ_[p]`, Simple Residue Module & Length-to-Cardinality Bridge -/

section PadicLengthCard

variable {p : ℕ} [Fact p.Prime]

/-- The canonical residue reduction `PadicInt p →+* ZMod p` is surjective. -/
theorem padicInt_toZMod_surjective :
    Function.Surjective (PadicInt.toZMod : PadicInt p →+* ZMod p) := by
  intro z
  refine ⟨(z.val : PadicInt p), ?_⟩
  rw [map_natCast, ZMod.natCast_zmod_val]

/-- The unique maximal ideal of the local ring `PadicInt p` is the principal ideal `(p)`. -/
theorem padicInt_maximalIdeal_eq_span_p :
    IsLocalRing.maximalIdeal (PadicInt p) =
      Ideal.span ({(p : PadicInt p)} : Set (PadicInt p)) := by
  ext x
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · intro hx
    by_cases hx0 : x = 0
    · exact ⟨0, by simp [hx0]⟩
    · have hnu : ¬ IsUnit x := by
        rw [← IsLocalRing.notMem_maximalIdeal, not_not, ← PadicInt.ker_toZMod, RingHom.mem_ker]
        exact hx
      have hspec := PadicInt.unitCoeff_spec hx0
      cases hv : x.valuation with
      | zero =>
        rw [hv, pow_zero, mul_one] at hspec
        exact absurd (hspec ▸ (PadicInt.unitCoeff hx0).isUnit) hnu
      | succ k =>
        rw [hv, pow_succ'] at hspec
        exact ⟨(PadicInt.unitCoeff hx0 : PadicInt p) * (p : PadicInt p) ^ k, hspec.trans (by ring)⟩
  · rintro ⟨y, rfl⟩
    rw [map_mul, map_natCast, ZMod.natCast_self, zero_mul]

/-- The kernel of `PadicInt.toZMod : PadicInt p →+* ZMod p` is the principal ideal `(p)`. -/
theorem padicInt_ker_toZMod_eq_span_p :
    RingHom.ker (PadicInt.toZMod : PadicInt p →+* ZMod p) =
      Ideal.span ({(p : PadicInt p)} : Set (PadicInt p)) :=
  PadicInt.ker_toZMod.trans padicInt_maximalIdeal_eq_span_p

/-- Ring equivalence `PadicInt p ⧸ (p) ≃+* ZMod p`. -/
def padicIntQuotSpanPEquivZMod :
    (PadicInt p ⧸ Ideal.span ({(p : PadicInt p)} : Set (PadicInt p))) ≃+* ZMod p :=
  (Ideal.quotEquivOfEq padicInt_ker_toZMod_eq_span_p.symm).trans
    (RingHom.quotientKerEquivOfSurjective padicInt_toZMod_surjective)

/-- The ideal `(p)` in `PadicInt p` is maximal. -/
theorem padicInt_span_p_isMaximal :
    (Ideal.span ({(p : PadicInt p)} : Set (PadicInt p))).IsMaximal := by
  rw [← padicInt_ker_toZMod_eq_span_p]
  exact RingHom.ker_isMaximal_of_surjective _ padicInt_toZMod_surjective

/-- An element of `PadicInt p` with nonzero residue in `ZMod p` is a unit. -/
theorem padicInt_isUnit_of_toZMod_ne_zero {x : PadicInt p}
    (hx : PadicInt.toZMod x ≠ 0) : IsUnit x := by
  rw [← IsLocalRing.notMem_maximalIdeal, padicInt_maximalIdeal_eq_span_p,
    ← padicInt_ker_toZMod_eq_span_p, RingHom.mem_ker]
  exact hx

/-- Every element `1 + p * y` in `PadicInt p` is a unit. -/
theorem padicInt_isUnit_one_add_p_mul (y : PadicInt p) :
    IsUnit (1 + (p : PadicInt p) * y) := by
  apply padicInt_isUnit_of_toZMod_ne_zero
  rw [map_add, map_one, map_mul, map_natCast, ZMod.natCast_self, zero_mul, add_zero]
  exact one_ne_zero

/-- The residue quotient `PadicInt p ⧸ (p)` is a simple `PadicInt p`-module. -/
instance padicInt_isSimpleModule_quot_span_p :
    IsSimpleModule (PadicInt p)
      (PadicInt p ⧸ Ideal.span ({(p : PadicInt p)} : Set (PadicInt p))) := by
  have : (Ideal.span ({(p : PadicInt p)} : Set (PadicInt p))).IsMaximal :=
    padicInt_span_p_isMaximal
  exact isSimpleModule_iff_quot_maximal.mpr
    ⟨Ideal.span ({(p : PadicInt p)} : Set (PadicInt p)), this,
      ⟨LinearEquiv.refl _ _⟩⟩

/-- Exact length `length_{ℤ_[p]}(ℤ_[p] ⧸ (p)) = 1`. -/
theorem padicInt_length_quot_span_p :
    Module.length (PadicInt p)
      (PadicInt p ⧸ Ideal.span ({(p : PadicInt p)} : Set (PadicInt p))) = 1 :=
  Module.length_eq_one (PadicInt p) _

/-- Exact length `length_{ℤ_[p]}(ℤ_[p] ⧸ (p^k)) = k` for every `k : ℕ`. -/
theorem padicInt_length_quot_span_p_pow :
    ∀ k : ℕ,
      Module.length (PadicInt p)
        (PadicInt p ⧸ Ideal.span ({(p : PadicInt p) ^ k} : Set (PadicInt p))) = (k : ℕ∞)
  | 0 => by
      have htop : Ideal.span ({(p : PadicInt p) ^ 0} : Set (PadicInt p)) = ⊤ := by
        rw [pow_zero, Ideal.span_singleton_one]
      have hsub : Subsingleton
          (PadicInt p ⧸ Ideal.span ({(p : PadicInt p) ^ 0} : Set (PadicInt p))) := by
        rw [htop]
        infer_instance
      simp [Module.length_eq_zero]
  | k + 1 => by
      let R := PadicInt p
      let pi : R := (p : R)
      have hpi_ne : pi ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
      let Ik : Ideal R := Ideal.span ({pi ^ k} : Set R)
      let Ik1 : Ideal R := Ideal.span ({pi ^ (k + 1)} : Set R)
      let I1 : Ideal R := Ideal.span ({pi} : Set R)
      have hle : Ik1 ≤ I1 := by
        rw [Ideal.span_singleton_le_iff_mem, pow_succ]
        exact Ideal.mul_mem_left I1 (pi ^ k) (Ideal.subset_span rfl)
      let qMap : (R ⧸ Ik1) →ₗ[R] (R ⧸ I1) := Submodule.factor hle
      have hqSurj : Function.Surjective qMap := Submodule.factor_surjective hle
      let mulPi : R →ₗ[R] (R ⧸ Ik1) :=
        { toFun := fun x => Ideal.Quotient.mk Ik1 (pi * x)
          map_add' := fun x y => by rw [mul_add, map_add]
          map_smul' := fun r x => by
            change Ideal.Quotient.mk Ik1 (pi * (r * x)) = r • Ideal.Quotient.mk Ik1 (pi * x)
            rw [← mul_assoc, mul_comm pi r, mul_assoc]
            exact map_smul (Ideal.Quotient.mkₐ R Ik1).toLinearMap r (pi * x) }
      let iMap : (R ⧸ Ik) →ₗ[R] (R ⧸ Ik1) :=
        Ik.liftQ mulPi (by
          intro x hx
          rw [LinearMap.mem_ker]
          rw [Ideal.mem_span_singleton] at hx
          obtain ⟨c, rfl⟩ := hx
          change Ideal.Quotient.mk Ik1 (pi * (pi ^ k * c)) = 0
          rw [Ideal.Quotient.eq_zero_iff_mem, ← mul_assoc, ← pow_succ']
          exact Ideal.mul_mem_right c Ik1 (Ideal.subset_span rfl))
      have hiInj : Function.Injective iMap := by
        rw [injective_iff_map_eq_zero]
        intro q hq
        induction q using Quotient.inductionOn' with
        | h x =>
          change Ideal.Quotient.mk Ik1 (pi * x) = 0 at hq
          rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hq
          obtain ⟨c, hc⟩ := hq
          have hc' : pi * x = pi * (pi ^ k * c) := by
            calc pi * x = pi ^ (k + 1) * c := hc
              _ = pi * (pi ^ k * c) := by rw [pow_succ', mul_assoc]
          have hx : x = pi ^ k * c := mul_left_cancel₀ hpi_ne hc'
          change Ideal.Quotient.mk Ik x = 0
          rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
          exact ⟨c, hx⟩
      have hexact : Function.Exact iMap qMap := by
        rw [LinearMap.exact_iff]
        ext y
        induction y using Quotient.inductionOn' with
        | h r =>
          simp only [LinearMap.mem_ker, LinearMap.mem_range]
          constructor
          · intro hr
            have hr' : r ∈ I1 := Ideal.Quotient.eq_zero_iff_mem.mp hr
            rw [Ideal.mem_span_singleton] at hr'
            obtain ⟨x, rfl⟩ := hr'
            exact ⟨Ideal.Quotient.mk Ik x, rfl⟩
          · rintro ⟨q, hq⟩
            induction q using Quotient.inductionOn' with
            | h x =>
              rw [← hq]
              change Ideal.Quotient.mk I1 (pi * x) = 0
              rw [Ideal.Quotient.eq_zero_iff_mem]
              exact Ideal.mul_mem_right x I1 (Ideal.subset_span rfl)
      have hadd := Module.length_eq_add_of_exact iMap qMap hiInj hqSurj hexact
      rw [hadd, padicInt_length_quot_span_p_pow k, padicInt_length_quot_span_p]
      push_cast
      rfl

/-- Every simple `ℤ_[p]`-module is finite of exact cardinality `p`. -/
theorem padicInt_card_of_isSimple {S : Type*} [AddCommGroup S] [Module (PadicInt p) S]
    [IsSimpleModule (PadicInt p) S] :
    Finite S ∧ Nat.card S = p := by
  have hne : (⊥ : Submodule (PadicInt p) S) ≠ ⊤ := bot_ne_top
  obtain ⟨x, hx⟩ : ∃ x : S, x ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    ext y
    simp [h y]
  let f : PadicInt p →ₗ[PadicInt p] S := LinearMap.toSpanSingleton (PadicInt p) S x
  have hrange_ne : LinearMap.range f ≠ ⊥ := by
    intro hbot
    have hx_mem : x ∈ LinearMap.range f := ⟨1, by simp [f]⟩
    rw [hbot, Submodule.mem_bot] at hx_mem
    exact hx hx_mem
  have hsurj : Function.Surjective f := by
    rw [← LinearMap.range_eq_top]
    exact (IsSimpleOrder.eq_bot_or_eq_top (LinearMap.range f)).resolve_left hrange_ne
  let K : Ideal (PadicInt p) := LinearMap.ker f
  let e1 : (PadicInt p ⧸ K) ≃ₗ[PadicInt p] S :=
    LinearMap.quotKerEquivOfSurjective f hsurj
  have hmax : K.IsMaximal := by
    rw [Ideal.isMaximal_def]
    refine ⟨?_, fun J hJ => ?_⟩
    · intro htop
      have hsub : Subsingleton (PadicInt p ⧸ K) := by
        rw [htop]
        infer_instance
      have : x = 0 := by
        have hsubS : Subsingleton S := e1.symm.injective.subsingleton
        exact Subsingleton.elim x 0
      exact hx this
    · have hmap : Submodule.map f J ≠ ⊥ := by
        intro hbot
        have hle : J ≤ K := by
          intro r hr
          rw [LinearMap.mem_ker]
          have : f r ∈ Submodule.map f J := ⟨r, hr, rfl⟩
          rwa [hbot, Submodule.mem_bot] at this
        exact not_le_of_gt hJ hle
      have htopM : Submodule.map f J = ⊤ :=
        (IsSimpleOrder.eq_bot_or_eq_top (Submodule.map f J)).resolve_left hmap
      rw [eq_top_iff]
      intro r _
      have : f r ∈ Submodule.map f J := by rw [htopM]; trivial
      obtain ⟨j, hj, hfj⟩ := this
      have hdiff : r - j ∈ K := by
        rw [LinearMap.mem_ker, map_sub, hfj, sub_self]
      have : r = j + (r - j) := by ring
      rw [this]
      exact J.add_mem hj (hJ.le hdiff)
  have hker_eq : K = Ideal.span ({(p : PadicInt p)} : Set (PadicInt p)) :=
    (IsLocalRing.eq_maximalIdeal hmax).trans padicInt_maximalIdeal_eq_span_p
  let e : S ≃ ZMod p :=
    e1.symm.toEquiv.trans
      ((Ideal.quotEquivOfEq hker_eq).toEquiv.trans padicIntQuotSpanPEquivZMod.toEquiv)
  refine ⟨Finite.of_equiv (ZMod p) e.symm, ?_⟩
  rw [Nat.card_congr e, Nat.card_zmod]

/-- Helper: every nontrivial finite-length `R`-module contains a simple submodule. -/
theorem exists_simple_submodule_of_length_ne_zero_ne_top {R A : Type*} [CommRing R]
    [AddCommGroup A] [Module R A]
    (h0 : Module.length R A ≠ 0) (htop : Module.length R A ≠ ⊤) :
    ∃ S : Submodule R A, IsSimpleModule R S := by
  have hfl : IsFiniteLength R A := Module.length_ne_top_iff.mp htop
  have hArt : IsArtinian R A := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).2
  have hne : ({N : Submodule R A | N ≠ ⊥}).Nonempty := by
    refine ⟨⊤, ?_⟩
    intro h
    apply h0
    have hsub : Subsingleton A := by
      refine ⟨fun x y => ?_⟩
      have hx : x ∈ (⊥ : Submodule R A) := by rw [← h]; trivial
      have hy : y ∈ (⊥ : Submodule R A) := by rw [← h]; trivial
      rw [Submodule.mem_bot] at hx hy
      rw [hx, hy]
    exact Module.length_eq_zero
  obtain ⟨S, hS_ne, hS_min⟩ :=
    WellFounded.has_min (wellFounded_lt (α := Submodule R A)) {N : Submodule R A | N ≠ ⊥} hne
  refine ⟨S, ?_⟩
  have hsimple : IsSimpleOrder (Submodule R S) := by
    refine isSimpleOrder_iff_isAtom_top.mpr ?_
    constructor
    · intro h
      apply hS_ne
      ext x
      simp only [Submodule.mem_bot]
      constructor
      · intro hx
        have hmem : (⟨x, hx⟩ : S) ∈ (⊥ : Submodule R S) := by rw [← h]; trivial
        exact congrArg Subtype.val ((Submodule.mem_bot R).mp hmem)
      · rintro rfl
        exact S.zero_mem
    · intro T hT
      by_contra hT_ne
      have hmap_ne : T.map S.subtype ≠ ⊥ := by
        intro hbot
        apply hT_ne
        ext ⟨x, hx⟩
        simp only [Submodule.mem_bot]
        constructor
        · intro hxT
          have : x ∈ T.map S.subtype := ⟨⟨x, hx⟩, hxT, rfl⟩
          rw [hbot, Submodule.mem_bot] at this
          exact Subtype.ext this
        · intro hx0
          have : (⟨x, hx⟩ : S) = 0 := Subtype.ext (congrArg Subtype.val hx0)
          rw [this]
          exact T.zero_mem
      have hmap_lt : T.map S.subtype < S := by
        refine lt_of_le_of_ne (fun x hx => ?_) (fun heq => ?_)
        · obtain ⟨⟨y, hy⟩, _, rfl⟩ := hx
          exact hy
        · apply ne_of_lt hT
          ext ⟨x, hx⟩
          simp only [Submodule.mem_top, iff_true]
          have : x ∈ T.map S.subtype := by rw [heq]; exact hx
          obtain ⟨⟨y, hy⟩, hyT, rfl⟩ := this
          exact hyT
      exact hS_min (T.map S.subtype) hmap_ne hmap_lt
  exact @IsSimpleModule.mk R _ S _ _ hsimple

/-- **Exact Length-to-Cardinality Theorem for `ℤ_[p]`-modules**:
every finite-length `ℤ_[p]`-module `A` is finite and satisfies `|A| = p ^ length_{ℤ_[p]}(A)`. -/
theorem padicInt_card_eq_pow_length :
    ∀ (k : ℕ) {A : Type*} [AddCommGroup A] [Module (PadicInt p) A],
      Module.length (PadicInt p) A = (k : ℕ∞) →
      Finite A ∧ Nat.card A = p ^ k
  | 0, A, _, _, hlen => by
      have hsub : Subsingleton A := Module.length_eq_zero_iff.mp hlen
      refine ⟨Finite.of_subsingleton, ?_⟩
      rw [pow_zero, Nat.card_eq_one_iff_unique]
      exact ⟨hsub, ⟨0⟩⟩
  | k + 1, A, _, _, hlen => by
      have h0 : Module.length (PadicInt p) A ≠ 0 := by rw [hlen]; simp
      have htop : Module.length (PadicInt p) A ≠ ⊤ := by rw [hlen]; exact ENat.natCast_ne_top _
      obtain ⟨S, hS⟩ := exists_simple_submodule_of_length_ne_zero_ne_top h0 htop
      have : IsSimpleModule (PadicInt p) S := hS
      have hadd : Module.length (PadicInt p) A =
          Module.length (PadicInt p) S + Module.length (PadicInt p) (A ⧸ S) :=
        Module.length_eq_add_of_exact S.subtype S.mkQ (Submodule.subtype_injective S)
          (Submodule.mkQ_surjective S) (LinearMap.exact_subtype_mkQ S)
      have hSlen : Module.length (PadicInt p) S = 1 := Module.length_eq_one (PadicInt p) S
      have hQlen : Module.length (PadicInt p) (A ⧸ S) = (k : ℕ∞) := by
        rw [hlen, hSlen] at hadd
        have hadd' : (1 : ℕ∞) + (k : ℕ∞) = (1 : ℕ∞) + Module.length (PadicInt p) (A ⧸ S) := by
          simpa [add_comm] using hadd
        exact (WithTop.add_left_cancel (by simp : (1 : ℕ∞) ≠ ⊤) hadd').symm
      obtain ⟨hfinS, hcardS⟩ := padicInt_card_of_isSimple (p := p) (S := S)
      obtain ⟨hfinQ, hcardQ⟩ := padicInt_card_eq_pow_length k hQlen
      have hlag : Nat.card A = Nat.card (A ⧸ S.toAddSubgroup) * Nat.card S.toAddSubgroup :=
        AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup S.toAddSubgroup
      have hQcard : Nat.card (A ⧸ S.toAddSubgroup) = Nat.card (A ⧸ S) := rfl
      have hScard : Nat.card S.toAddSubgroup = Nat.card S := rfl
      have hcardA : Nat.card A = p ^ (k + 1) := by
        rw [hlag, hQcard, hScard, hcardQ, hcardS, pow_succ]
      have hfinA : Finite A :=
        Nat.finite_of_card_ne_zero (by rw [hcardA]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
      exact ⟨hfinA, hcardA⟩

/-- Cardinality upper bound directly from a `ℤ_[p]`-length bound `length_{ℤ_[p]}(A) ≤ B`. -/
theorem padicInt_card_le_of_length_le {A : Type*} [AddCommGroup A] [Module (PadicInt p) A]
    {B : ℕ} (h : Module.length (PadicInt p) A ≤ (B : ℕ∞)) :
    Finite A ∧ Nat.card A ≤ p ^ B := by
  have hne : Module.length (PadicInt p) A ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top B) h
  set k := (Module.length (PadicInt p) A).toNat
  have hk_eq : Module.length (PadicInt p) A = (k : ℕ∞) := (ENat.natCast_toNat hne).symm
  have hk_le : k ≤ B := ENat.toNat_le_of_le_natCast h
  obtain ⟨hfin, hcard⟩ := padicInt_card_eq_pow_length (p := p) k hk_eq
  refine ⟨hfin, ?_⟩
  rw [hcard]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hk_le

/-- Length of a product of two `R`-modules is the sum of their lengths. -/
theorem length_prod {R A B : Type*} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] :
    Module.length R (A × B) = Module.length R A + Module.length R B := by
  refine Module.length_eq_add_of_exact (LinearMap.inl R A B) (LinearMap.snd R A B)
    LinearMap.inl_injective LinearMap.snd_surjective ?_
  rw [LinearMap.exact_iff]
  ext ⟨a, b⟩
  simp [eq_comm]

/-- Length of a finite indexed product `∀ i : Fin k, M i` is the sum of component lengths. -/
theorem length_pi_fin {R : Type*} [CommRing R] :
    ∀ (k : ℕ) (M : Fin k → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)],
      Module.length R (∀ i : Fin k, M i) = ∑ i : Fin k, Module.length R (M i)
  | 0, M, _, _ => by
      have : Subsingleton (∀ i : Fin 0, M i) := Unique.instSubsingleton
      simp [Module.length_eq_zero]
  | k + 1, M, _, _ => by
      let e : (∀ i : Fin (k + 1), M i) ≃ₗ[R] (M 0 × ∀ i : Fin k, M i.succ) :=
        { toFun := fun f => (f 0, fun i => f i.succ)
          invFun := fun q => Fin.cons q.1 q.2
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl
          left_inv := fun f => by ext i; refine Fin.cases rfl (fun _ => rfl) i
          right_inv := fun q => by cases q; ext <;> rfl }
      rw [e.length_eq, length_prod, length_pi_fin k (fun i => M i.succ), Fin.sum_univ_succ]

end PadicLengthCard

/-! ## Section 2: Concrete Iwasawa Algebra `Λ_p = ℤ_[p][[T]]` & Finite-Level Quotients `M / ω_n M` -/

section IwasawaAlgebra

variable (p : ℕ) [Fact p.Prime]

/-- The Iwasawa algebra `Λ_p = ℤ_[p][[T]]` of formal power series over the `p`-adic integers. -/
abbrev IwasawaAlg (p : ℕ) [Fact p.Prime] : Type := PowerSeries (PadicInt p)

/-- The `n`-th cyclotomic layer element `ω_n = (1 + T)^(p^n) - 1 ∈ Λ_p`. -/
def omegaElem (n : ℕ) : IwasawaAlg p :=
  (1 + PowerSeries.X) ^ (p ^ n) - 1

/-- The relative cyclotomic transition element `Φ_n = ∑_{j=0}^{p-1} ((1 + T)^(p^n))^j ∈ Λ_p`,
satisfying `ω_{n+1} = ω_n * Φ_n`. -/
def phiElem (n : ℕ) : IwasawaAlg p :=
  ∑ j ∈ Finset.range p, ((1 + PowerSeries.X) ^ (p ^ n)) ^ j

/-- The `n`-th layer submodule `ω_n • M` of a `Λ_p`-module `M`. -/
def layerSubmodule (n : ℕ) (M : Type*) [AddCommGroup M] [Module (IwasawaAlg p) M] :
    Submodule (IwasawaAlg p) M :=
  LinearMap.range (LinearMap.lsmul (IwasawaAlg p) M (omegaElem p n))

/-- The finite-level quotient `A_n(M) = M / ω_n M = M / ((1 + T)^(p^n) - 1) M`. -/
abbrev LayerQuot (n : ℕ) (M : Type*) [AddCommGroup M] [Module (IwasawaAlg p) M] : Type _ :=
  M ⧸ layerSubmodule p n M

theorem omegaElem_zero : omegaElem p 0 = PowerSeries.X := by
  simp [omegaElem]

theorem omegaElem_succ (n : ℕ) : omegaElem p (n + 1) = omegaElem p n * phiElem p n := by
  unfold omegaElem phiElem
  rw [pow_succ, pow_mul]
  symm
  simpa [mul_comm] using geom_sum_mul ((1 + PowerSeries.X : IwasawaAlg p) ^ (p ^ n)) p

theorem omegaElem_dvd_succ (n : ℕ) : omegaElem p n ∣ omegaElem p (n + 1) :=
  ⟨phiElem p n, omegaElem_succ p n⟩

theorem omegaElem_dvd_of_le {m n : ℕ} (h : m ≤ n) : omegaElem p m ∣ omegaElem p n := by
  induction n with
  | zero =>
    obtain rfl : m = 0 := Nat.le_zero.mp h
    exact dvd_rfl
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact dvd_rfl
    · exact (ih (Nat.lt_succ_iff.mp hlt)).trans (omegaElem_dvd_succ p k)

/-- `PowerSeries (ZMod p)` has characteristic `p`. -/
theorem charP_powerSeries_zmod : CharP (PowerSeries (ZMod p)) p := by
  refine ⟨fun n => ?_⟩
  rw [← map_natCast (PowerSeries.C (R := ZMod p)), ← map_zero (PowerSeries.C (R := ZMod p)),
    PowerSeries.C_injective.eq_iff]
  exact CharP.cast_eq_zero_iff (ZMod p) p n

/-- Mod-`p` Frobenius reduction: `ω_n = (1 + T)^(p^n) - 1` reduces to `T^(p^n)` in `(ZMod p)[[T]]`. -/
theorem map_toZMod_omegaElem (n : ℕ) :
    PowerSeries.map (PadicInt.toZMod : PadicInt p →+* ZMod p) (omegaElem p n) =
      (PowerSeries.X : PowerSeries (ZMod p)) ^ (p ^ n) := by
  have : CharP (PowerSeries (ZMod p)) p := charP_powerSeries_zmod p
  unfold omegaElem
  rw [map_sub, map_pow, map_add, map_one, PowerSeries.map_X]
  rw [add_pow_char_pow (R := PowerSeries (ZMod p)), one_pow, add_sub_cancel_left]

/-- Exact `p`-adic congruence `ω_n = T^(p^n) + p * g` in `Λ_p = ℤ_[p][[T]]`. -/
theorem exists_omegaElem_eq_X_pow_add_p_mul (n : ℕ) :
    ∃ g : IwasawaAlg p,
      omegaElem p n = PowerSeries.X ^ (p ^ n) + PowerSeries.C (p : PadicInt p) * g := by
  have hzero : PowerSeries.map (PadicInt.toZMod : PadicInt p →+* ZMod p)
      (omegaElem p n - PowerSeries.X ^ (p ^ n)) = 0 := by
    rw [map_sub, map_toZMod_omegaElem, map_pow, PowerSeries.map_X, sub_self]
  have hdiv : ∀ k : ℕ, ∃ c : PadicInt p,
      PowerSeries.coeff k (omegaElem p n - PowerSeries.X ^ (p ^ n)) = (p : PadicInt p) * c := by
    intro k
    have hk : PadicInt.toZMod (PowerSeries.coeff k (omegaElem p n - PowerSeries.X ^ (p ^ n))) = 0 := by
      rw [← PowerSeries.coeff_map, hzero, map_zero]
    have hmem : PowerSeries.coeff k (omegaElem p n - PowerSeries.X ^ (p ^ n)) ∈
        Ideal.span ({(p : PadicInt p)} : Set (PadicInt p)) := by
      rw [← padicInt_ker_toZMod_eq_span_p, RingHom.mem_ker]
      exact hk
    exact Ideal.mem_span_singleton.mp hmem
  choose c hc using hdiv
  refine ⟨PowerSeries.mk c, ?_⟩
  ext k
  have hk := hc k
  rw [map_sub] at hk
  rw [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
  exact eq_add_of_sub_eq' hk

/-- The layer submodule equals `(ω_n) • ⊤`. -/
theorem layerSubmodule_eq_span_smul (n : ℕ) (M : Type*) [AddCommGroup M]
    [Module (IwasawaAlg p) M] :
    layerSubmodule p n M =
      Ideal.span ({omegaElem p n} : Set (IwasawaAlg p)) • (⊤ : Submodule (IwasawaAlg p) M) := by
  ext x
  simp only [layerSubmodule, LinearMap.mem_range, LinearMap.lsmul_apply]
  constructor
  · rintro ⟨m, rfl⟩
    exact Submodule.smul_mem_smul (Ideal.subset_span rfl) Submodule.mem_top
  · intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr m _
      rw [Ideal.mem_span_singleton] at hr
      obtain ⟨c, rfl⟩ := hr
      exact ⟨c • m, by rw [mul_smul]⟩
    · rintro x₁ x₂ ⟨m₁, rfl⟩ ⟨m₂, rfl⟩
      exact ⟨m₁ + m₂, smul_add _ m₁ m₂⟩

/-- Tower monotonicity: `m ≤ n` induces a surjection `M / ω_n M ↠ M / ω_m M`, hence
`length(M / ω_m M) ≤ length(M / ω_n M)`. -/
theorem length_layerQuot_mono {M : Type*} [AddCommGroup M]
    [Module (PadicInt p) M] [Module (IwasawaAlg p) M] [IsScalarTower (PadicInt p) (IwasawaAlg p) M]
    {m n : ℕ} (h : m ≤ n) :
    Module.length (PadicInt p) (LayerQuot p m M) ≤
      Module.length (PadicInt p) (LayerQuot p n M) := by
  have hle : layerSubmodule p n M ≤ layerSubmodule p m M := by
    obtain ⟨q, hq⟩ := omegaElem_dvd_of_le p h
    rintro x ⟨y, rfl⟩
    refine ⟨q • y, ?_⟩
    simp only [LinearMap.lsmul_apply, hq, mul_smul]
  exact Module.length_le_of_surjective
    ((Submodule.factor hle).restrictScalars (PadicInt p)) (Submodule.factor_surjective hle)

/-- General multiplicative quotient length subadditivity for any `a, b ∈ Λ_p` on any `Λ_p`-module `M`:
`length(M / (a * b) M) ≤ length(M / a M) + length(M / b M)`. -/
theorem length_quot_mul_le {M : Type*} [AddCommGroup M]
    [Module (PadicInt p) M] [Module (IwasawaAlg p) M] [IsScalarTower (PadicInt p) (IwasawaAlg p) M]
    (a b : IwasawaAlg p) :
    Module.length (PadicInt p) (M ⧸ LinearMap.range (LinearMap.lsmul (IwasawaAlg p) M (a * b))) ≤
      Module.length (PadicInt p) (M ⧸ LinearMap.range (LinearMap.lsmul (IwasawaAlg p) M a)) +
        Module.length (PadicInt p) (M ⧸ LinearMap.range (LinearMap.lsmul (IwasawaAlg p) M b)) := by
  let Iab := LinearMap.range (LinearMap.lsmul (IwasawaAlg p) M (a * b))
  let Ia := LinearMap.range (LinearMap.lsmul (IwasawaAlg p) M a)
  let Ib := LinearMap.range (LinearMap.lsmul (IwasawaAlg p) M b)
  have hle : Iab ≤ Ia := by
    rintro x ⟨m, rfl⟩
    refine ⟨b • m, ?_⟩
    simp only [LinearMap.lsmul_apply, mul_smul]
  let qMap : (M ⧸ Iab) →ₗ[PadicInt p] (M ⧸ Ia) := (Submodule.factor hle).restrictScalars (PadicInt p)
  have hqSurj : Function.Surjective qMap := Submodule.factor_surjective hle
  have hadd := Module.length_eq_add_of_exact (LinearMap.ker qMap).subtype qMap
    (Submodule.subtype_injective _) hqSurj (LinearMap.exact_subtype_ker_map qMap)
  let mulA : M →ₗ[PadicInt p] LinearMap.ker qMap :=
    { toFun := fun m =>
        ⟨Submodule.Quotient.mk (a • m), by
          change Submodule.Quotient.mk (p := Ia) (a • m) = 0
          rw [Submodule.Quotient.mk_eq_zero]
          exact ⟨m, rfl⟩⟩
      map_add' := fun x y => by
        apply Subtype.ext
        change Submodule.Quotient.mk (p := Iab) (a • (x + y)) =
          Submodule.Quotient.mk (a • x) + Submodule.Quotient.mk (a • y)
        rw [smul_add, Submodule.Quotient.mk_add]
      map_smul' := fun r x => by
        apply Subtype.ext
        change Submodule.Quotient.mk (p := Iab) (a • (r • x)) =
          r • Submodule.Quotient.mk (a • x)
        rw [← algebraMap_smul (IwasawaAlg p) r x, smul_comm,
          algebraMap_smul (IwasawaAlg p) r (a • x), Submodule.Quotient.mk_smul] }
  let liftA : (M ⧸ Ib) →ₗ[PadicInt p] LinearMap.ker qMap :=
    (Ib.restrictScalars (PadicInt p)).liftQ mulA (by
      rintro x ⟨m, rfl⟩
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      change Submodule.Quotient.mk (p := Iab) (a • (b • m)) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact ⟨m, by simp [LinearMap.lsmul_apply, mul_smul]⟩)
  have hSurjK : Function.Surjective liftA := by
    rintro ⟨y, hy⟩
    induction y using Quotient.inductionOn' with
    | h m =>
      have hm : m ∈ Ia := by
        have h0 : Submodule.Quotient.mk (p := Ia) m = 0 := hy
        exact (Submodule.Quotient.mk_eq_zero Ia).mp h0
      obtain ⟨x, rfl⟩ := hm
      exact ⟨Submodule.Quotient.mk x, rfl⟩
  have hKle := Module.length_le_of_surjective liftA hSurjK
  rw [hadd, add_comm]
  gcongr

/-- Exact multiplicative quotient length additivity when multiplication by `a` is injective on `M`. -/
theorem length_quot_mul_eq_of_injective {M : Type*} [AddCommGroup M]
    [Module (PadicInt p) M] [Module (IwasawaAlg p) M] [IsScalarTower (PadicInt p) (IwasawaAlg p) M]
    (a b : IwasawaAlg p)
    (hinj : Function.Injective (LinearMap.lsmul (IwasawaAlg p) M a)) :
    Module.length (PadicInt p) (M ⧸ LinearMap.range (LinearMap.lsmul (IwasawaAlg p) M (a * b))) =
      Module.length (PadicInt p) (M ⧸ LinearMap.range (LinearMap.lsmul (IwasawaAlg p) M a)) +
        Module.length (PadicInt p) (M ⧸ LinearMap.range (LinearMap.lsmul (IwasawaAlg p) M b)) := by
  let Iab := LinearMap.range (LinearMap.lsmul (IwasawaAlg p) M (a * b))
  let Ia := LinearMap.range (LinearMap.lsmul (IwasawaAlg p) M a)
  let Ib := LinearMap.range (LinearMap.lsmul (IwasawaAlg p) M b)
  have hle : Iab ≤ Ia := by
    rintro x ⟨m, rfl⟩
    refine ⟨b • m, ?_⟩
    simp only [LinearMap.lsmul_apply, mul_smul]
  let qMap : (M ⧸ Iab) →ₗ[PadicInt p] (M ⧸ Ia) := (Submodule.factor hle).restrictScalars (PadicInt p)
  have hqSurj : Function.Surjective qMap := Submodule.factor_surjective hle
  let mulA : M →ₗ[PadicInt p] (M ⧸ Iab) :=
    { toFun := fun m => Submodule.Quotient.mk (a • m)
      map_add' := fun x y => by rw [smul_add, Submodule.Quotient.mk_add]
      map_smul' := fun r x => by
        change Submodule.Quotient.mk (p := Iab) (a • (r • x)) = r • Submodule.Quotient.mk (a • x)
        rw [← algebraMap_smul (IwasawaAlg p) r x, smul_comm,
          algebraMap_smul (IwasawaAlg p) r (a • x), Submodule.Quotient.mk_smul] }
  let iMap : (M ⧸ Ib) →ₗ[PadicInt p] (M ⧸ Iab) :=
    (Ib.restrictScalars (PadicInt p)).liftQ mulA (by
      rintro x ⟨m, rfl⟩
      rw [LinearMap.mem_ker]
      change Submodule.Quotient.mk (p := Iab) (a • (b • m)) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact ⟨m, by simp [LinearMap.lsmul_apply, mul_smul]⟩)
  have hiInj : Function.Injective iMap := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    induction q using Quotient.inductionOn' with
    | h m =>
      change Submodule.Quotient.mk (p := Iab) (a • m) = 0 at hq
      rw [Submodule.Quotient.mk_eq_zero] at hq
      obtain ⟨x, hx⟩ := hq
      have hEq : a • (b • x) = a • m := by
        simpa [LinearMap.lsmul_apply, mul_smul] using hx
      have hbx : b • x = m := hinj hEq
      change Submodule.Quotient.mk (p := Ib) m = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact ⟨x, hbx⟩
  have hexact : Function.Exact iMap qMap := by
    rw [LinearMap.exact_iff]
    ext y
    induction y using Quotient.inductionOn' with
    | h m =>
      simp only [LinearMap.mem_ker, LinearMap.mem_range]
      constructor
      · intro hm
        have hm' : m ∈ Ia := (Submodule.Quotient.mk_eq_zero Ia).mp hm
        obtain ⟨x, rfl⟩ := hm'
        exact ⟨Submodule.Quotient.mk x, rfl⟩
      · rintro ⟨q, hq⟩
        induction q using Quotient.inductionOn' with
        | h x =>
          rw [← hq]
          change Submodule.Quotient.mk (p := Ia) (a • x) = 0
          rw [Submodule.Quotient.mk_eq_zero]
          exact ⟨x, rfl⟩
  rw [Module.length_eq_add_of_exact iMap qMap hiInj hqSurj hexact, add_comm]

/-- Layer transition subadditivity: `length(M / ω_{n+1} M) ≤ length(M / ω_n M) + length(M / Φ_n M)`. -/
theorem length_layerQuot_succ_le {M : Type*} [AddCommGroup M]
    [Module (PadicInt p) M] [Module (IwasawaAlg p) M] [IsScalarTower (PadicInt p) (IwasawaAlg p) M]
    (n : ℕ) :
    Module.length (PadicInt p) (LayerQuot p (n + 1) M) ≤
      Module.length (PadicInt p) (LayerQuot p n M) +
        Module.length (PadicInt p) (M ⧸ LinearMap.range (LinearMap.lsmul (IwasawaAlg p) M (phiElem p n))) := by
  unfold LayerQuot layerSubmodule
  rw [omegaElem_succ p n]
  exact length_quot_mul_le p (omegaElem p n) (phiElem p n)

/-- **Pseudo-Isomorphism Transfer Inequality**: for ANY `Λ_p`-linear map `φ : M →ₗ[Λ_p] E` and
EVERY level `n : ℕ`,
`length_{ℤ_[p]}(M / ω_n M) ≤ length_{ℤ_[p]}(E / ω_n E) + length_{ℤ_[p]}(ker φ) + length_{ℤ_[p]}(coker φ)`. -/
theorem length_layerQuot_le_of_pseudoIso {M E : Type*} [AddCommGroup M] [AddCommGroup E]
    [Module (PadicInt p) M] [Module (IwasawaAlg p) M] [IsScalarTower (PadicInt p) (IwasawaAlg p) M]
    [Module (PadicInt p) E] [Module (IwasawaAlg p) E] [IsScalarTower (PadicInt p) (IwasawaAlg p) E]
    (φ : M →ₗ[IwasawaAlg p] E) (n : ℕ) :
    Module.length (PadicInt p) (LayerQuot p n M) ≤
      Module.length (PadicInt p) (LayerQuot p n E) +
        Module.length (PadicInt p) (LinearMap.ker φ) +
        Module.length (PadicInt p) (E ⧸ LinearMap.range φ) := by
  let I := LinearMap.range φ
  let πI : M →ₗ[IwasawaAlg p] I := φ.rangeRestrict
  have hπI_surj : Function.Surjective πI := φ.surjective_rangeRestrict
  have hmap1 : layerSubmodule p n M ≤ (layerSubmodule p n I).comap πI := by
    rintro x ⟨m, rfl⟩
    exact ⟨πI m, by simp [LinearMap.lsmul_apply, map_smul]⟩
  let f1 : LayerQuot p n M →ₗ[PadicInt p] LayerQuot p n I :=
    (Submodule.mapQ (layerSubmodule p n M) (layerSubmodule p n I) πI hmap1).restrictScalars (PadicInt p)
  have hf1_surj : Function.Surjective f1 := by
    intro q
    induction q using Quotient.inductionOn' with
    | h y =>
      obtain ⟨m, rfl⟩ := hπI_surj y
      exact ⟨Submodule.Quotient.mk m, rfl⟩
  have hadd1 := Module.length_eq_add_of_exact (LinearMap.ker f1).subtype f1
    (Submodule.subtype_injective _) hf1_surj (LinearMap.exact_subtype_ker_map f1)
  let kerToKer1 : LinearMap.ker φ →ₗ[PadicInt p] LinearMap.ker f1 :=
    { toFun := fun k =>
        ⟨Submodule.Quotient.mk k.1, by
          change Submodule.Quotient.mk (p := layerSubmodule p n I) (πI k.1) = 0
          have hk0 : πI k.1 = 0 := Subtype.ext k.2
          rw [hk0]
          exact Submodule.Quotient.mk_zero _⟩
      map_add' := fun _ _ => by apply Subtype.ext; rfl
      map_smul' := fun _ _ => by apply Subtype.ext; rfl }
  have hker1_surj : Function.Surjective kerToKer1 := by
    rintro ⟨q, hq⟩
    induction q using Quotient.inductionOn' with
    | h m =>
      have hm : πI m ∈ layerSubmodule p n I :=
        (Submodule.Quotient.mk_eq_zero (layerSubmodule p n I)).mp hq
      obtain ⟨y, hy⟩ := hm
      obtain ⟨m', rfl⟩ := hπI_surj y
      have hdiff : m - omegaElem p n • m' ∈ LinearMap.ker φ := by
        rw [LinearMap.mem_ker, map_sub, map_smul]
        have hy' : omegaElem p n • φ m' = φ m := congrArg Subtype.val hy
        rw [hy', sub_self]
      refine ⟨⟨m - omegaElem p n • m', hdiff⟩, ?_⟩
      apply Subtype.ext
      change Submodule.Quotient.mk (p := layerSubmodule p n M) (m - omegaElem p n • m') =
        Submodule.Quotient.mk m
      rw [Submodule.Quotient.eq]
      have : (m - omegaElem p n • m') - m = omegaElem p n • (-m') := by
        rw [smul_neg]
        abel
      rw [this]
      exact ⟨-m', rfl⟩
  have hStep1 : Module.length (PadicInt p) (LayerQuot p n M) ≤
      Module.length (PadicInt p) (LayerQuot p n I) +
        Module.length (PadicInt p) (LinearMap.ker φ) := by
    rw [hadd1, add_comm]
    have hle := Module.length_le_of_surjective kerToKer1 hker1_surj
    gcongr
  have hmap2 : layerSubmodule p n I ≤ (layerSubmodule p n E).comap I.subtype := by
    rintro x ⟨y, rfl⟩
    exact ⟨y.1, rfl⟩
  let f2 : LayerQuot p n I →ₗ[PadicInt p] LayerQuot p n E :=
    (Submodule.mapQ (layerSubmodule p n I) (layerSubmodule p n E) I.subtype hmap2).restrictScalars (PadicInt p)
  have hadd2 := Module.length_eq_add_of_exact (LinearMap.ker f2).subtype f2.rangeRestrict
    (Submodule.subtype_injective _) f2.surjective_rangeRestrict (by
      rw [LinearMap.exact_iff]
      ext x
      simp [LinearMap.mem_ker])
  have him2_le : Module.length (PadicInt p) (LinearMap.range f2) ≤
      Module.length (PadicInt p) (LayerQuot p n E) :=
    Module.length_le_of_injective (LinearMap.range f2).subtype (Submodule.subtype_injective _)
  let Q := E ⧸ I
  let Qtor : Submodule (PadicInt p) Q :=
    LinearMap.ker ((LinearMap.lsmul (IwasawaAlg p) Q (omegaElem p n)).restrictScalars (PadicInt p))
  let preSub : Submodule (PadicInt p) E :=
    (I.restrictScalars (PadicInt p)).comap
      ((LinearMap.lsmul (IwasawaAlg p) E (omegaElem p n)).restrictScalars (PadicInt p))
  let δPre : preSub →ₗ[PadicInt p] LinearMap.ker f2 :=
    { toFun := fun e =>
        ⟨Submodule.Quotient.mk ⟨omegaElem p n • e.1, e.2⟩, by
          change Submodule.Quotient.mk (p := layerSubmodule p n E) (omegaElem p n • e.1) = 0
          rw [Submodule.Quotient.mk_eq_zero]
          exact ⟨e.1, rfl⟩⟩
      map_add' := fun x y => by
        apply Subtype.ext
        change Submodule.Quotient.mk (p := layerSubmodule p n I)
          ⟨omegaElem p n • (x.1 + y.1), _⟩ =
          Submodule.Quotient.mk ⟨omegaElem p n • x.1, x.2⟩ +
            Submodule.Quotient.mk ⟨omegaElem p n • y.1, y.2⟩
        rw [← Submodule.Quotient.mk_add]
        congr 1
        apply Subtype.ext
        exact smul_add _ x.1 y.1
      map_smul' := fun r x => by
        apply Subtype.ext
        change Submodule.Quotient.mk (p := layerSubmodule p n I)
          ⟨omegaElem p n • (r • x.1), _⟩ =
          r • Submodule.Quotient.mk ⟨omegaElem p n • x.1, x.2⟩
        rw [← Submodule.Quotient.mk_smul]
        congr 1
        apply Subtype.ext
        change omegaElem p n • (r • x.1) = r • (omegaElem p n • x.1)
        rw [← algebraMap_smul (IwasawaAlg p) r x.1, smul_comm,
          algebraMap_smul (IwasawaAlg p) r (omegaElem p n • x.1)] }
  have hδPre_surj : Function.Surjective δPre := by
    rintro ⟨q, hq⟩
    induction q using Quotient.inductionOn' with
    | h y =>
      have hy : y.1 ∈ layerSubmodule p n E :=
        (Submodule.Quotient.mk_eq_zero (layerSubmodule p n E)).mp hq
      obtain ⟨e, he⟩ := hy
      have he' : omegaElem p n • e = y.1 := he
      have he_mem : e ∈ preSub := by
        change omegaElem p n • e ∈ I
        rw [he']
        exact y.2
      refine ⟨⟨e, he_mem⟩, ?_⟩
      apply Subtype.ext
      change Submodule.Quotient.mk (p := layerSubmodule p n I) ⟨omegaElem p n • e, he_mem⟩ =
        Submodule.Quotient.mk y
      congr 1
      exact Subtype.ext he'
  let qProj : preSub →ₗ[PadicInt p] Qtor :=
    { toFun := fun e =>
        ⟨Submodule.Quotient.mk e.1, by
          change omegaElem p n • Submodule.Quotient.mk (p := I) e.1 = 0
          rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
          exact e.2⟩
      map_add' := fun _ _ => by apply Subtype.ext; rfl
      map_smul' := fun _ _ => by apply Subtype.ext; rfl }
  have hker_le : LinearMap.ker qProj ≤ LinearMap.ker δPre := by
    intro e he
    rw [LinearMap.mem_ker] at he ⊢
    have heI : e.1 ∈ I := (Submodule.Quotient.mk_eq_zero I).mp (congrArg Subtype.val he)
    apply Subtype.ext
    change Submodule.Quotient.mk (p := layerSubmodule p n I) ⟨omegaElem p n • e.1, e.2⟩ = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨⟨e.1, heI⟩, rfl⟩
  let δQ : (preSub ⧸ LinearMap.ker qProj) →ₗ[PadicInt p] LinearMap.ker f2 :=
    (LinearMap.ker qProj).liftQ δPre hker_le
  have hδQ_surj : Function.Surjective δQ := by
    intro y
    obtain ⟨e, rfl⟩ := hδPre_surj y
    exact ⟨Submodule.Quotient.mk e, rfl⟩
  have hker2_le : Module.length (PadicInt p) (LinearMap.ker f2) ≤ Module.length (PadicInt p) Q := by
    calc Module.length (PadicInt p) (LinearMap.ker f2)
        ≤ Module.length (PadicInt p) (preSub ⧸ LinearMap.ker qProj) :=
            Module.length_le_of_surjective δQ hδQ_surj
      _ = Module.length (PadicInt p) (LinearMap.range qProj) :=
            (LinearMap.quotKerEquivRange qProj).length_eq
      _ ≤ Module.length (PadicInt p) Qtor :=
            Module.length_le_of_injective (LinearMap.range qProj).subtype (Submodule.subtype_injective _)
      _ ≤ Module.length (PadicInt p) Q :=
            Module.length_le_of_injective Qtor.subtype (Submodule.subtype_injective _)
  have hStep2 : Module.length (PadicInt p) (LayerQuot p n I) ≤
      Module.length (PadicInt p) (LayerQuot p n E) + Module.length (PadicInt p) Q := by
    rw [hadd2, add_comm]
    exact add_le_add him2_le hker2_le
  calc Module.length (PadicInt p) (LayerQuot p n M)
      ≤ Module.length (PadicInt p) (LayerQuot p n I) +
          Module.length (PadicInt p) (LinearMap.ker φ) := hStep1
    _ ≤ (Module.length (PadicInt p) (LayerQuot p n E) + Module.length (PadicInt p) Q) +
          Module.length (PadicInt p) (LinearMap.ker φ) := by gcongr
    _ = Module.length (PadicInt p) (LayerQuot p n E) +
          Module.length (PadicInt p) (LinearMap.ker φ) +
          Module.length (PadicInt p) Q := by ac_rfl

/-- Product splitting of finite-level quotients `LayerQuot p n (A × B) ≃ LayerQuot p n A × LayerQuot p n B`. -/
def layerQuotProdEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module (PadicInt p) A] [Module (IwasawaAlg p) A] [IsScalarTower (PadicInt p) (IwasawaAlg p) A]
    [Module (PadicInt p) B] [Module (IwasawaAlg p) B] [IsScalarTower (PadicInt p) (IwasawaAlg p) B]
    (n : ℕ) :
    LayerQuot p n (A × B) ≃ₗ[PadicInt p] (LayerQuot p n A × LayerQuot p n B) := by
  let f : (A × B) →ₗ[PadicInt p] (LayerQuot p n A × LayerQuot p n B) :=
    { toFun := fun q => (Submodule.Quotient.mk q.1, Submodule.Quotient.mk q.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hsurj : Function.Surjective f := by
    rintro ⟨qa, qb⟩
    induction qa using Quotient.inductionOn' with
    | h a =>
      induction qb using Quotient.inductionOn' with
      | h b => exact ⟨(a, b), rfl⟩
  have hker : LinearMap.ker f = (layerSubmodule p n (A × B)).restrictScalars (PadicInt p) := by
    ext ⟨a, b⟩
    change (Submodule.Quotient.mk (p := layerSubmodule p n A) a,
      Submodule.Quotient.mk (p := layerSubmodule p n B) b) = 0 ↔
      (a, b) ∈ layerSubmodule p n (A × B)
    rw [Prod.mk_eq_zero, Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩
      exact ⟨(a', b'), Prod.ext ha' hb'⟩
    · rintro ⟨⟨a', b'⟩, h⟩
      exact ⟨⟨a', congrArg Prod.fst h⟩, ⟨b', congrArg Prod.snd h⟩⟩
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans (LinearMap.quotKerEquivOfSurjective f hsurj)

/-- Finite-indexed product splitting of `LayerQuot p n`. -/
def layerQuotPiEquiv {k : ℕ} {M : Fin k → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module (PadicInt p) (M i)]
    [∀ i, Module (IwasawaAlg p) (M i)] [∀ i, IsScalarTower (PadicInt p) (IwasawaAlg p) (M i)]
    (n : ℕ) :
    LayerQuot p n (∀ i : Fin k, M i) ≃ₗ[PadicInt p] (∀ i : Fin k, LayerQuot p n (M i)) := by
  let f : (∀ i : Fin k, M i) →ₗ[PadicInt p] (∀ i : Fin k, LayerQuot p n (M i)) :=
    { toFun := fun v i => Submodule.Quotient.mk (v i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hsurj : Function.Surjective f := by
    intro q
    have hch : ∀ i : Fin k, ∃ m : M i, Submodule.Quotient.mk (p := layerSubmodule p n (M i)) m = q i :=
      fun i => Quotient.exists_rep (q i)
    choose v hv using hch
    exact ⟨v, funext hv⟩
  have hker : LinearMap.ker f = (layerSubmodule p n (∀ i : Fin k, M i)).restrictScalars (PadicInt p) := by
    ext v
    change (fun i => Submodule.Quotient.mk (p := layerSubmodule p n (M i)) (v i)) = 0 ↔
      v ∈ layerSubmodule p n (∀ i : Fin k, M i)
    rw [funext_iff]
    simp only [Pi.zero_apply, Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hv
      have hv' : ∀ i : Fin k, ∃ w : M i, omegaElem p n • w = v i := hv
      choose w hw using hv'
      exact ⟨w, funext hw⟩
    · rintro ⟨w, rfl⟩ i
      exact ⟨w i, rfl⟩
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans (LinearMap.quotKerEquivOfSurjective f hsurj)

end IwasawaAlgebra

/-! ## Section 3: Elementary Iwasawa Modules (`Λ_p / (p^m)` & Distinguished `ℤ_[p]`-Free Lattices) -/

section ElementaryModules

variable (p : ℕ) [Fact p.Prime]

/-- `p`-power torsion elementary Iwasawa module `Λ_p ⧸ (p^m)`. -/
abbrev ElemPTorsion (m : ℕ) : Type :=
  IwasawaAlg p ⧸ Ideal.span ({(PowerSeries.C (p : PadicInt p)) ^ m} : Set (IwasawaAlg p))

/-- Exact `ℤ_[p]`-length of `LayerQuot p n (ElemPTorsion p 1)`: equals `p ^ n`. -/
theorem length_layerQuot_elemPTorsion_one (n : ℕ) :
    Module.length (PadicInt p) (LayerQuot p n (ElemPTorsion p 1)) = ((p ^ n : ℕ) : ℕ∞) := by
  let R := PadicInt p
  let Ip : Ideal R := Ideal.span ({(p : R)} : Set R)
  let I1 : Ideal (IwasawaAlg p) := Ideal.span ({(PowerSeries.C (p : R)) ^ 1} : Set (IwasawaAlg p))
  -- Direct surjection `Λ_p →ₗ[R] (Fin (p^n) → R ⧸ (p))` sending `f` to its first `p^n` coefficients mod `p`.
  let τ : IwasawaAlg p →ₗ[R] (Fin (p ^ n) → R ⧸ Ip) :=
    { toFun := fun f i => Ideal.Quotient.mk Ip (PowerSeries.coeff i.val f)
      map_add' := fun f g => by ext i; simp [map_add]
      map_smul' := fun r f => by
        ext i
        change Ideal.Quotient.mk Ip (PowerSeries.coeff i.val (r • f)) =
          r • Ideal.Quotient.mk Ip (PowerSeries.coeff i.val f)
        rw [PowerSeries.coeff_smul, smul_eq_mul]
        exact map_smul (Ideal.Quotient.mkₐ R Ip).toLinearMap r (PowerSeries.coeff i.val f) }
  have hτ_surj : Function.Surjective τ := by
    intro v
    have hlift : ∀ i : Fin (p ^ n), ∃ a : R, Ideal.Quotient.mk Ip a = v i :=
      fun i => Ideal.Quotient.mk_surjective (v i)
    choose a ha using hlift
    refine ⟨PowerSeries.mk (fun k => if h : k < p ^ n then a ⟨k, h⟩ else 0), ?_⟩
    ext i
    simp [τ, PowerSeries.coeff_mk, i.isLt, ha i]
  obtain ⟨g, hg⟩ := exists_omegaElem_eq_X_pow_add_p_mul p n
  -- Factor `τ` through `ElemPTorsion p 1`, then through `LayerQuot p n (ElemPTorsion p 1)`.
  have hI1_ker : I1.restrictScalars R ≤ LinearMap.ker τ := by
    intro f hf
    have hf' : f ∈ I1 := hf
    rw [Ideal.mem_span_singleton, pow_one] at hf'
    obtain ⟨q, rfl⟩ := hf'
    rw [LinearMap.mem_ker]
    ext i
    change Ideal.Quotient.mk Ip (PowerSeries.coeff i.val (PowerSeries.C (p : R) * q)) = 0
    rw [PowerSeries.coeff_C_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ Ip (Ideal.subset_span rfl)
  let τ1 : ElemPTorsion p 1 →ₗ[R] (Fin (p ^ n) → R ⧸ Ip) :=
    (I1.restrictScalars R).liftQ τ hI1_ker
  have hω_ker : (layerSubmodule p n (ElemPTorsion p 1)).restrictScalars R ≤ LinearMap.ker τ1 := by
    rintro x ⟨q, rfl⟩
    induction q using Quotient.inductionOn' with
    | h h =>
      rw [LinearMap.mem_ker]
      ext i
      change Ideal.Quotient.mk Ip (PowerSeries.coeff i.val (omegaElem p n * h)) = 0
      rw [hg, add_mul, map_add, PowerSeries.coeff_X_pow_mul',
        if_neg (not_le_of_gt i.isLt), zero_add, mul_assoc, PowerSeries.coeff_C_mul,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right _ Ip (Ideal.subset_span rfl)
  let τ2 : LayerQuot p n (ElemPTorsion p 1) →ₗ[R] (Fin (p ^ n) → R ⧸ Ip) :=
    ((layerSubmodule p n (ElemPTorsion p 1)).restrictScalars R).liftQ τ1 hω_ker
  have hτ2_surj : Function.Surjective τ2 := by
    intro v
    obtain ⟨f, rfl⟩ := hτ_surj v
    exact ⟨Submodule.Quotient.mk (Ideal.Quotient.mk I1 f), rfl⟩
  have hτ2_inj : Function.Injective τ2 := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    induction y using Quotient.inductionOn' with
    | h q =>
      induction q using Quotient.inductionOn' with
      | h f =>
        have hcoeff : ∀ k : ℕ, k < p ^ n → ∃ c : R, PowerSeries.coeff k f = (p : R) * c := by
          intro k hk
          have h0 : Ideal.Quotient.mk Ip (PowerSeries.coeff k f) = 0 := congrFun hy ⟨k, hk⟩
          exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h0)
        let f1 : IwasawaAlg p :=
          PowerSeries.mk fun k => if hk : k < p ^ n then (hcoeff k hk).choose else 0
        let f' : IwasawaAlg p := f - PowerSeries.C (p : R) * f1
        have hf'_zero : ∀ k < p ^ n, PowerSeries.coeff k f' = 0 := by
          intro k hk
          simp only [f', map_sub, PowerSeries.coeff_C_mul, f1, PowerSeries.coeff_mk, dif_pos hk]
          have hck := (hcoeff k hk).choose_spec
          rw [← hck, sub_self]
        let q' : IwasawaAlg p := PowerSeries.mk fun k => PowerSeries.coeff (k + p ^ n) f'
        have hf'_eq : f' = PowerSeries.X ^ (p ^ n) * q' := by
          ext k
          by_cases hk : p ^ n ≤ k
          · rw [PowerSeries.coeff_X_pow_mul', if_pos hk]
            simp only [q', PowerSeries.coeff_mk, Nat.sub_add_cancel hk]
          · rw [PowerSeries.coeff_X_pow_mul', if_neg hk]
            exact hf'_zero k (lt_of_not_ge hk)
        have hf_decomp : f = omegaElem p n * q' + PowerSeries.C (p : R) * (f1 - g * q') := by
          have h1 : f = f' + PowerSeries.C (p : R) * f1 := by simp [f']
          rw [h1, hf'_eq]
          have hX : PowerSeries.X ^ (p ^ n) = omegaElem p n - PowerSeries.C (p : R) * g := by
            rw [hg, add_sub_cancel_right]
          rw [hX]
          ring
        change Submodule.Quotient.mk (p := layerSubmodule p n (ElemPTorsion p 1))
          (Ideal.Quotient.mk I1 f) = 0
        rw [Submodule.Quotient.mk_eq_zero]
        refine ⟨Ideal.Quotient.mk I1 q', ?_⟩
        change Ideal.Quotient.mk I1 (omegaElem p n * q') = Ideal.Quotient.mk I1 f
        rw [hf_decomp, map_add]
        have hzero : Ideal.Quotient.mk I1 (PowerSeries.C (p : R) * (f1 - g * q')) = 0 := by
          rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, pow_one]
          exact ⟨f1 - g * q', rfl⟩
        rw [hzero, add_zero]
  let e : LayerQuot p n (ElemPTorsion p 1) ≃ₗ[R] (Fin (p ^ n) → R ⧸ Ip) :=
    LinearEquiv.ofBijective τ2 ⟨hτ2_inj, hτ2_surj⟩
  rw [e.length_eq, Module.length_pi, padicInt_length_quot_span_p, mul_one]
  simp

/-- Exact `ℤ_[p]`-length of `LayerQuot p n (ElemPTorsion p m)`:
`length_{ℤ_[p]}((Λ_p / (p^m)) / ω_n (Λ_p / (p^m))) = m * p ^ n` for ALL `m, n : ℕ`. -/
theorem length_layerQuot_elemPTorsion (n : ℕ) :
    ∀ m : ℕ,
      Module.length (PadicInt p) (LayerQuot p n (ElemPTorsion p m)) = ((m * p ^ n : ℕ) : ℕ∞)
  | 0 => by
      have htop : Ideal.span ({(PowerSeries.C (p : PadicInt p)) ^ 0} : Set (IwasawaAlg p)) = ⊤ := by
        rw [pow_zero, Ideal.span_singleton_one]
      have hsub1 : Subsingleton (ElemPTorsion p 0) := by
        unfold ElemPTorsion
        rw [htop]
        infer_instance
      have hsub2 : Subsingleton (LayerQuot p n (ElemPTorsion p 0)) :=
        ⟨fun a b => by
          induction a using Quotient.inductionOn' with
          | h x =>
            induction b using Quotient.inductionOn' with
            | h y => rw [hsub1.elim x y]⟩
      simp [Module.length_eq_zero]
  | m + 1 => by
      let R := PadicInt p
      let pi : IwasawaAlg p := PowerSeries.C (p : R)
      have hp_ne : (p : R) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
      let Im : Ideal (IwasawaAlg p) := Ideal.span ({pi ^ m} : Set (IwasawaAlg p))
      let Im1 : Ideal (IwasawaAlg p) := Ideal.span ({pi ^ (m + 1)} : Set (IwasawaAlg p))
      let I1 : Ideal (IwasawaAlg p) := Ideal.span ({pi ^ 1} : Set (IwasawaAlg p))
      have hle : Im1 ≤ I1 := by
        rw [Ideal.span_singleton_le_iff_mem, pow_succ]
        exact Ideal.mul_mem_left I1 (pi ^ m) (by simp [I1])
      let fac : ElemPTorsion p (m + 1) →ₗ[IwasawaAlg p] ElemPTorsion p 1 := Submodule.factor hle
      have hfac_map : layerSubmodule p n (ElemPTorsion p (m + 1)) ≤
          (layerSubmodule p n (ElemPTorsion p 1)).comap fac := by
        rintro x ⟨y, rfl⟩
        exact ⟨fac y, by simp [LinearMap.lsmul_apply, map_smul]⟩
      let qMap : LayerQuot p n (ElemPTorsion p (m + 1)) →ₗ[R] LayerQuot p n (ElemPTorsion p 1) :=
        (Submodule.mapQ _ _ fac hfac_map).restrictScalars R
      have hqSurj : Function.Surjective qMap := by
        intro q
        induction q using Quotient.inductionOn' with
        | h x =>
          obtain ⟨y, rfl⟩ := Submodule.factor_surjective hle x
          exact ⟨Submodule.Quotient.mk y, rfl⟩
      -- Map `× C p : ElemPTorsion p m →ₗ[Λ_p] ElemPTorsion p (m + 1)`
      let mulP0 : IwasawaAlg p →ₗ[IwasawaAlg p] ElemPTorsion p (m + 1) :=
        (Ideal.Quotient.mkₐ (IwasawaAlg p) Im1).toLinearMap.comp
          (LinearMap.lsmul (IwasawaAlg p) (IwasawaAlg p) pi)
      let mulP : ElemPTorsion p m →ₗ[IwasawaAlg p] ElemPTorsion p (m + 1) :=
        Im.liftQ mulP0 (by
          intro x hx
          rw [LinearMap.mem_ker]
          rw [Ideal.mem_span_singleton] at hx
          obtain ⟨c, rfl⟩ := hx
          change Ideal.Quotient.mk Im1 (pi * (pi ^ m * c)) = 0
          rw [Ideal.Quotient.eq_zero_iff_mem, ← mul_assoc, ← pow_succ']
          exact Ideal.mul_mem_right c Im1 (Ideal.subset_span rfl))
      have hmulP_map : layerSubmodule p n (ElemPTorsion p m) ≤
          (layerSubmodule p n (ElemPTorsion p (m + 1))).comap mulP := by
        rintro x ⟨y, rfl⟩
        exact ⟨mulP y, by simp [LinearMap.lsmul_apply, map_smul]⟩
      let iMap : LayerQuot p n (ElemPTorsion p m) →ₗ[R] LayerQuot p n (ElemPTorsion p (m + 1)) :=
        (Submodule.mapQ _ _ mulP hmulP_map).restrictScalars R
      obtain ⟨g, hg⟩ := exists_omegaElem_eq_X_pow_add_p_mul p n
      -- Injectivity of `iMap` via exact regularity of `(p, ω_n)` in `ℤ_[p][[T]]`!
      have hiInj : Function.Injective iMap := by
        rw [injective_iff_map_eq_zero]
        intro q hq
        induction q using Quotient.inductionOn' with
        | h x =>
          induction x using Quotient.inductionOn' with
          | h f =>
            change Submodule.Quotient.mk (p := layerSubmodule p n (ElemPTorsion p (m + 1)))
              (Ideal.Quotient.mk Im1 (pi * f)) = 0 at hq
            rw [Submodule.Quotient.mk_eq_zero] at hq
            obtain ⟨y, hy⟩ := hq
            induction y using Quotient.inductionOn' with
            | h h =>
              have hdiff : Ideal.Quotient.mk Im1 (omegaElem p n * h - pi * f) = 0 := by
                have hy' : Ideal.Quotient.mk Im1 (omegaElem p n * h) = Ideal.Quotient.mk Im1 (pi * f) := hy
                rw [map_sub, hy', sub_self]
              rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hdiff
              obtain ⟨c, hc⟩ := hdiff
              -- Show `h = pi * h'` by reading off `coeff (k + p^n)` of `X^(p^n) * h`.
              have hXh : PowerSeries.X ^ (p ^ n) * h =
                  pi * (f + pi ^ m * c - g * h) := by
                have h1 : omegaElem p n * h = pi * f + pi ^ (m + 1) * c :=
                  eq_add_of_sub_eq' (by simpa [add_comm] using hc)
                rw [hg, add_mul, pow_succ'] at h1
                have h2 : PowerSeries.X ^ (p ^ n) * h =
                    pi * f + pi * (pi ^ m * c) - pi * (g * h) := by
                  calc PowerSeries.X ^ (p ^ n) * h
                      = (PowerSeries.X ^ (p ^ n) * h + pi * g * h) - pi * g * h := by ring
                    _ = pi * f + pi * pi ^ m * c - pi * g * h := by rw [h1]
                    _ = pi * f + pi * (pi ^ m * c) - pi * (g * h) := by ring
                rw [h2]
                ring
              let h' : IwasawaAlg p :=
                PowerSeries.mk fun k =>
                  PowerSeries.coeff (k + p ^ n) (f + pi ^ m * c - g * h)
              have hh_eq : h = pi * h' := by
                ext k
                have hk := congrArg (PowerSeries.coeff (k + p ^ n)) hXh
                rw [PowerSeries.coeff_X_pow_mul', if_pos (Nat.le_add_left _ _),
                  Nat.add_sub_cancel] at hk
                rw [hk, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
              have hpi_eq : pi * f = pi * (omegaElem p n * h' - pi ^ m * c) := by
                have h1 : omegaElem p n * (pi * h') = pi ^ (m + 1) * c + pi * f := by
                  rw [← hh_eq]
                  exact eq_add_of_sub_eq hc
                rw [pow_succ'] at h1
                calc pi * f
                    = (pi * pi ^ m * c + pi * f) - pi * pi ^ m * c := by ring
                  _ = omegaElem p n * (pi * h') - pi * pi ^ m * c := by rw [← h1]
                  _ = pi * (omegaElem p n * h' - pi ^ m * c) := by ring
              have hf_eq : f = omegaElem p n * h' - pi ^ m * c := by
                ext k
                have hk := congrArg (PowerSeries.coeff k) hpi_eq
                rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul] at hk
                exact mul_left_cancel₀ hp_ne hk
              change Submodule.Quotient.mk (p := layerSubmodule p n (ElemPTorsion p m))
                (Ideal.Quotient.mk Im f) = 0
              rw [Submodule.Quotient.mk_eq_zero]
              refine ⟨Ideal.Quotient.mk Im h', ?_⟩
              change Ideal.Quotient.mk Im (omegaElem p n * h') = Ideal.Quotient.mk Im f
              rw [hf_eq, map_sub]
              have hc0 : Ideal.Quotient.mk Im (pi ^ m * c) = 0 := by
                rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
                exact ⟨c, rfl⟩
              rw [hc0, sub_zero]
      have hexact : Function.Exact iMap qMap := by
        rw [LinearMap.exact_iff]
        ext y
        induction y using Quotient.inductionOn' with
        | h x =>
          induction x using Quotient.inductionOn' with
          | h f =>
            simp only [LinearMap.mem_ker, LinearMap.mem_range]
            constructor
            · intro hf
              change Submodule.Quotient.mk (p := layerSubmodule p n (ElemPTorsion p 1))
                (Ideal.Quotient.mk I1 f) = 0 at hf
              rw [Submodule.Quotient.mk_eq_zero] at hf
              obtain ⟨z, hz⟩ := hf
              induction z using Quotient.inductionOn' with
              | h h =>
                have hdiff : Ideal.Quotient.mk I1 (f - omegaElem p n * h) = 0 := by
                  have hz' : Ideal.Quotient.mk I1 (omegaElem p n * h) = Ideal.Quotient.mk I1 f := hz
                  rw [map_sub, hz', sub_self]
                rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, pow_one] at hdiff
                obtain ⟨c, hc⟩ := hdiff
                refine ⟨Submodule.Quotient.mk (Ideal.Quotient.mk Im c), ?_⟩
                change Submodule.Quotient.mk (p := layerSubmodule p n (ElemPTorsion p (m + 1)))
                  (Ideal.Quotient.mk Im1 (pi * c)) = Submodule.Quotient.mk (Ideal.Quotient.mk Im1 f)
                rw [Submodule.Quotient.eq]
                refine ⟨Ideal.Quotient.mk Im1 (-h), ?_⟩
                change Ideal.Quotient.mk Im1 (omegaElem p n * (-h)) =
                  Ideal.Quotient.mk Im1 (pi * c - f)
                congr 1
                have : pi * c - f = -(f - pi * c) := by ring
                rw [this]
                have hf2 : f - pi * c = omegaElem p n * h := by
                  have := eq_add_of_sub_eq hc
                  rw [this]
                  ring
                rw [hf2]
                ring
            · rintro ⟨q, hq⟩
              induction q using Quotient.inductionOn' with
              | h z =>
                induction z using Quotient.inductionOn' with
                | h c =>
                  rw [← hq]
                  change Submodule.Quotient.mk (p := layerSubmodule p n (ElemPTorsion p 1))
                    (Ideal.Quotient.mk I1 (pi * c)) = 0
                  have h0 : Ideal.Quotient.mk I1 (pi * c) = 0 := by
                    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, pow_one]
                    exact ⟨c, rfl⟩
                  rw [h0]
                  exact Submodule.Quotient.mk_zero _
      have hadd := Module.length_eq_add_of_exact iMap qMap hiInj hqSurj hexact
      rw [hadd, length_layerQuot_elemPTorsion n m, length_layerQuot_elemPTorsion_one p n]
      push_cast
      ring

/-- **Matrix-Determinant Invertibility over `ℤ_[p]`**: every `ℤ_[p]`-linear endomorphism of the
form `id + p • B` on `Fin lam → ℤ_[p]` is bijective! -/
theorem bijective_id_add_p_smul {lam : ℕ}
    (B : (Fin lam → PadicInt p) →ₗ[PadicInt p] (Fin lam → PadicInt p)) :
    Function.Bijective
      (LinearMap.id (R := PadicInt p) (M := Fin lam → PadicInt p) + (p : PadicInt p) • B) := by
  let M : Matrix (Fin lam) (Fin lam) (PadicInt p) := LinearMap.toMatrix' B
  let A : Matrix (Fin lam) (Fin lam) (PadicInt p) := 1 + (p : PadicInt p) • M
  have hmap : A.map (PadicInt.toZMod : PadicInt p →+* ZMod p) = 1 := by
    ext i j
    simp only [A, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      map_add, map_mul, map_natCast, ZMod.natCast_self, zero_mul, add_zero]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  have hdet_mod : PadicInt.toZMod A.det = 1 := by
    rw [RingHom.map_det]
    change (A.map (PadicInt.toZMod : PadicInt p →+* ZMod p)).det = 1
    rw [hmap, Matrix.det_one]
  have hdet_unit : IsUnit A.det :=
    padicInt_isUnit_of_toZMod_ne_zero (by rw [hdet_mod]; exact one_ne_zero)
  have hA_unit : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr hdet_unit
  obtain ⟨u, hu⟩ := hA_unit
  have hEq : (LinearMap.id (R := PadicInt p) (M := Fin lam → PadicInt p) + (p : PadicInt p) • B) =
      Matrix.toLin' A := by
    apply LinearMap.ext
    intro v
    funext i
    change v i + (p : PadicInt p) * B v i = A.mulVec v i
    have hMv : M.mulVec v = B v := by
      change (Matrix.toLin' M) v = B v
      rw [Matrix.toLin'_toMatrix']
    simp only [A, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, hMv]
  rw [hEq]
  refine ⟨?_, ?_⟩
  · intro x y hxy
    have hmul : (↑u⁻¹ : Matrix (Fin lam) (Fin lam) (PadicInt p)).mulVec (A.mulVec x) =
        (↑u⁻¹ : Matrix (Fin lam) (Fin lam) (PadicInt p)).mulVec (A.mulVec y) :=
      congrArg (Matrix.mulVec (↑u⁻¹ : Matrix (Fin lam) (Fin lam) (PadicInt p))) hxy
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hu, Units.inv_mul,
      Matrix.one_mulVec, Matrix.one_mulVec] at hmul
    exact hmul
  · intro y
    refine ⟨(↑u⁻¹ : Matrix (Fin lam) (Fin lam) (PadicInt p)).mulVec y, ?_⟩
    change A.mulVec ((↑u⁻¹ : Matrix (Fin lam) (Fin lam) (PadicInt p)).mulVec y) = y
    rw [Matrix.mulVec_mulVec, ← hu, Units.mul_inv, Matrix.one_mulVec]

/-- A **Distinguished `ℤ_[p]`-Free Lattice** of rank `lam`: models the `μ = 0` free part
`⨁ Λ_p / (f_j)` (with `f_j` distinguished polynomials of total degree `lam`) of a finitely
generated torsion `Λ_p`-module. -/
structure DistinguishedLattice (lam : ℕ) where
  Carrier : Type
  [addCommGroup : AddCommGroup Carrier]
  [modZ : Module (PadicInt p) Carrier]
  [modLam : Module (IwasawaAlg p) Carrier]
  [tower : IsScalarTower (PadicInt p) (IwasawaAlg p) Carrier]
  freeEquiv : Carrier ≃ₗ[PadicInt p] (Fin lam → PadicInt p)
  distDeg : ℕ
  /-- Topological nilpotency of `T = PowerSeries.X`: `T^d ∈ p • End_{ℤ_[p]}(Carrier)`
  (automatically satisfied whenever a distinguished polynomial `T^d + p * g(T)` annihilates `Carrier`). -/
  topNilpotent : ∃ C : Carrier →ₗ[PadicInt p] Carrier,
    (LinearMap.lsmul (IwasawaAlg p) Carrier (PowerSeries.X ^ distDeg)).restrictScalars (PadicInt p) =
      (p : PadicInt p) • C
  /-- Finite length at the stabilization base layer `distDeg + 1`. -/
  baseFinite : Module.length (PadicInt p) (LayerQuot p (distDeg + 1) Carrier) ≠ ⊤

attribute [instance] DistinguishedLattice.addCommGroup DistinguishedLattice.modZ
  DistinguishedLattice.modLam DistinguishedLattice.tower

namespace DistinguishedLattice

variable {p : ℕ} [Fact p.Prime] {lam : ℕ}

/-- Any `Λ_p`-module annihilated by a distinguished polynomial `T^d + p * g` satisfies `topNilpotent`. -/
theorem topNilpotent_of_distinguished_annihilator {M : Type} [AddCommGroup M]
    [Module (PadicInt p) M] [Module (IwasawaAlg p) M] [IsScalarTower (PadicInt p) (IwasawaAlg p) M]
    {d : ℕ} {g : IwasawaAlg p}
    (hann : ∀ m : M, (PowerSeries.X ^ d + PowerSeries.C (p : PadicInt p) * g) • m = 0) :
    ∃ C : M →ₗ[PadicInt p] M,
      (LinearMap.lsmul (IwasawaAlg p) M (PowerSeries.X ^ d)).restrictScalars (PadicInt p) =
        (p : PadicInt p) • C := by
  refine ⟨-(LinearMap.lsmul (IwasawaAlg p) M g).restrictScalars (PadicInt p), ?_⟩
  ext m
  have hm := hann m
  rw [add_smul, mul_smul] at hm
  have h1 : (PowerSeries.X ^ d : IwasawaAlg p) • m =
      -(PowerSeries.C (p : PadicInt p) • (g • m)) := eq_neg_of_add_eq_zero_left hm
  change (PowerSeries.X ^ d : IwasawaAlg p) • m = (p : PadicInt p) • (-(g • m))
  rw [h1, smul_neg]
  congr 1
  exact algebraMap_smul (IwasawaAlg p) (p : PadicInt p) (g • m)

/-- Helper: `d ≤ p ^ d` for every prime `p` and `d : ℕ`. -/
theorem le_prime_pow_self (d : ℕ) : d ≤ p ^ d := by
  have h2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  exact le_trans (Nat.lt_two_pow_self (n := d)).le (Nat.pow_le_pow_left h2 d)

/-- For every `n ≥ F.distDeg`, `ω_n` acts as `p • V` on `F.Carrier`. -/
theorem omega_mem_p_end (F : DistinguishedLattice p lam) {n : ℕ} (hn : F.distDeg ≤ n) :
    ∃ V : F.Carrier →ₗ[PadicInt p] F.Carrier,
      (LinearMap.lsmul (IwasawaAlg p) F.Carrier (omegaElem p n)).restrictScalars (PadicInt p) =
        (p : PadicInt p) • V := by
  obtain ⟨C, hC⟩ := F.topNilpotent
  obtain ⟨g, hg⟩ := exists_omegaElem_eq_X_pow_add_p_mul p n
  have hd_le : F.distDeg ≤ p ^ n :=
    le_trans (le_prime_pow_self (p := p) F.distDeg)
      (Nat.pow_le_pow_right (Fact.out : p.Prime).pos hn)
  let rem : IwasawaAlg p := PowerSeries.X ^ (p ^ n - F.distDeg)
  refine ⟨C.comp ((LinearMap.lsmul (IwasawaAlg p) F.Carrier rem).restrictScalars (PadicInt p)) +
      (LinearMap.lsmul (IwasawaAlg p) F.Carrier g).restrictScalars (PadicInt p), ?_⟩
  ext m
  change omegaElem p n • m = (p : PadicInt p) • (C (rem • m) + g • m)
  rw [hg, add_smul, smul_add]
  congr 1
  · have hpow : PowerSeries.X ^ (p ^ n) = PowerSeries.X ^ F.distDeg * rem := by
      rw [← pow_add, Nat.add_sub_of_le hd_le]
    rw [hpow, mul_smul]
    exact congrArg (fun f => f (rem • m)) hC
  · rw [mul_smul]
    exact algebraMap_smul (IwasawaAlg p) (p : PadicInt p) (g • m)

/-- Exact lifting lemma: if `ω_n` acts as `p • V` on `F.Carrier`, then `ω_{n+1}` acts as
`p^2 • W` on `F.Carrier` (valid for ALL primes `p`, including `p = 2`!). -/
theorem omega_succ_mem_p_sq_end (F : DistinguishedLattice p lam) {n : ℕ}
    {V : F.Carrier →ₗ[PadicInt p] F.Carrier}
    (hV : (LinearMap.lsmul (IwasawaAlg p) F.Carrier (omegaElem p n)).restrictScalars (PadicInt p) =
      (p : PadicInt p) • V) :
    ∃ W : F.Carrier →ₗ[PadicInt p] F.Carrier,
      (LinearMap.lsmul (IwasawaAlg p) F.Carrier (omegaElem p (n + 1))).restrictScalars (PadicInt p) =
        ((p : PadicInt p) ^ 2) • W := by
  let U : Module.End (PadicInt p) F.Carrier :=
    (LinearMap.lsmul (IwasawaAlg p) F.Carrier (omegaElem p n)).restrictScalars (PadicInt p)
  have hUn1 :
      (LinearMap.lsmul (IwasawaAlg p) F.Carrier (omegaElem p (n + 1))).restrictScalars (PadicInt p) =
        (1 + U) ^ p - 1 := by
    have hpow : ∀ k : ℕ,
        (LinearMap.lsmul (IwasawaAlg p) F.Carrier ((1 + omegaElem p n) ^ k)).restrictScalars (PadicInt p) =
          (1 + U) ^ k := by
      intro k
      induction k with
      | zero =>
        ext m; simp
      | succ k ih =>
        rw [pow_succ, pow_succ]
        ext m
        change ((1 + omegaElem p n) ^ k * (1 + omegaElem p n)) • m =
          ((1 + U) ^ k) ((1 + U) m)
        rw [mul_smul]
        have h1 : (1 + omegaElem p n) • m = (1 + U) m := by
          simp [U, add_smul]
        rw [h1]
        exact congrArg (fun f => f ((1 + U) m)) ih
    have hEq : omegaElem p (n + 1) = (1 + omegaElem p n) ^ p - 1 := by
      unfold omegaElem
      rw [add_sub_cancel, pow_succ, pow_mul]
    rw [hEq]
    ext m
    have hsub := congrArg (fun f => f m) (hpow p)
    change ((1 + omegaElem p n) ^ p - 1) • m = (((1 + U) ^ p - 1) m)
    rw [sub_smul, one_smul]
    simpa [LinearMap.sub_apply] using congrArg (fun z => z - m) hsub
  have hcomm : Commute U (1 : Module.End (PadicInt p) F.Carrier) := Commute.one_right U
  have hexp : (1 + U) ^ p - 1 =
      ∑ j ∈ Finset.Ico 1 (p + 1), (p.choose j : PadicInt p) • U ^ j := by
    rw [add_comm 1 U, hcomm.add_pow,
      Finset.sum_range_eq_add_Ico
        (f := fun j => U ^ j * (1 : Module.End (PadicInt p) F.Carrier) ^ (p - j) * (p.choose j))
        (Nat.succ_pos p)]
    simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.cast_one,
      add_sub_cancel_left]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul (PadicInt p)]
  -- Factor `(p : PadicInt p) ^ 2` out of every term `j ∈ [1, p]`!
  let coeffW : ℕ → Module.End (PadicInt p) F.Carrier := fun j =>
    if j = 1 then V
    else ((p.choose j : PadicInt p) * (p : PadicInt p) ^ (j - 2)) • V ^ j
  refine ⟨∑ j ∈ Finset.Ico 1 (p + 1), coeffW j, ?_⟩
  rw [hUn1, hexp, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
  have hU_pow : U ^ j = ((p : PadicInt p) ^ j) • V ^ j := by
    rw [show U = (p : PadicInt p) • V from hV, smul_pow]
  by_cases hjeq : j = 1
  · subst hjeq
    simp only [coeffW, ite_true, Nat.choose_one_right, hU_pow, pow_one, smul_smul, sq]
  · have hj2 : 2 ≤ j := by omega
    simp only [coeffW, if_neg hjeq, hU_pow, smul_smul]
    congr 1
    calc (p.choose j : PadicInt p) * (p : PadicInt p) ^ j
        = (p.choose j : PadicInt p) * ((p : PadicInt p) ^ 2 * (p : PadicInt p) ^ (j - 2)) := by
            rw [← pow_add, Nat.add_sub_of_le hj2]
      _ = (p : PadicInt p) ^ 2 * ((p.choose j : PadicInt p) * (p : PadicInt p) ^ (j - 2)) := by
            ring

/-- For EVERY `n ≥ F.distDeg + 1`, `ω_n` acts as `p^2 • W` on `F.Carrier`. -/
theorem omega_mem_p_sq_end (F : DistinguishedLattice p lam) {n : ℕ} (hn : F.distDeg + 1 ≤ n) :
    ∃ W : F.Carrier →ₗ[PadicInt p] F.Carrier,
      (LinearMap.lsmul (IwasawaAlg p) F.Carrier (omegaElem p n)).restrictScalars (PadicInt p) =
        ((p : PadicInt p) ^ 2) • W := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨V, hV⟩ := F.omega_mem_p_end (by omega : F.distDeg ≤ m)
  exact F.omega_succ_mem_p_sq_end hV

/-- For EVERY `n ≥ F.distDeg + 1`, `Φ_n` acts as `p • (id + p • B)` on `F.Carrier`. -/
theorem phi_eq_p_smul_id_add_p_smul (F : DistinguishedLattice p lam) {n : ℕ}
    (hn : F.distDeg + 1 ≤ n) :
    ∃ B : F.Carrier →ₗ[PadicInt p] F.Carrier,
      (LinearMap.lsmul (IwasawaAlg p) F.Carrier (phiElem p n)).restrictScalars (PadicInt p) =
        (p : PadicInt p) • (LinearMap.id + (p : PadicInt p) • B) := by
  obtain ⟨W, hW⟩ := F.omega_mem_p_sq_end hn
  let G : IwasawaAlg p :=
    ∑ j ∈ Finset.range p, ∑ i ∈ Finset.range j, ((1 + PowerSeries.X) ^ (p ^ n)) ^ i
  have hphi_id : phiElem p n = (p : IwasawaAlg p) + omegaElem p n * G := by
    unfold phiElem G
    rw [Finset.mul_sum]
    have hsum : ∑ j ∈ Finset.range p, ((1 + PowerSeries.X : IwasawaAlg p) ^ (p ^ n)) ^ j =
        ∑ j ∈ Finset.range p,
          (1 + omegaElem p n * ∑ i ∈ Finset.range j, ((1 + PowerSeries.X : IwasawaAlg p) ^ (p ^ n)) ^ i) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      have hg := geom_sum_mul ((1 + PowerSeries.X : IwasawaAlg p) ^ (p ^ n)) j
      unfold omegaElem
      rw [mul_comm, hg]
      ring
    rw [hsum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  refine ⟨W.comp ((LinearMap.lsmul (IwasawaAlg p) F.Carrier G).restrictScalars (PadicInt p)), ?_⟩
  ext m
  change phiElem p n • m = (p : PadicInt p) • (m + (p : PadicInt p) • W (G • m))
  rw [hphi_id, add_smul, mul_smul, smul_add]
  congr 1
  · have hcast : (p : IwasawaAlg p) = algebraMap (PadicInt p) (IwasawaAlg p) (p : PadicInt p) := by
      rw [map_natCast]
    rw [hcast, algebraMap_smul]
  · have hWm : omegaElem p n • (G • m) = ((p : PadicInt p) ^ 2) • W (G • m) :=
      congrArg (fun f => f (G • m)) hW
    calc omegaElem p n • (G • m)
        = ((p : PadicInt p) ^ 2) • W (G • m) := hWm
      _ = (p : PadicInt p) • ((p : PadicInt p) • W (G • m)) := by rw [sq, mul_smul]

/-- **Exact Step Length Theorem**: for EVERY `n ≥ F.distDeg + 1`,
`length_{ℤ_[p]}(F / Φ_n F) = lam`! -/
theorem length_quot_phi_eq_lam (F : DistinguishedLattice p lam) {n : ℕ}
    (hn : F.distDeg + 1 ≤ n) :
    Module.length (PadicInt p)
      (F.Carrier ⧸ LinearMap.range (LinearMap.lsmul (IwasawaAlg p) F.Carrier (phiElem p n))) =
        (lam : ℕ∞) := by
  obtain ⟨B, hB⟩ := F.phi_eq_p_smul_id_add_p_smul hn
  let e := F.freeEquiv
  let B' : (Fin lam → PadicInt p) →ₗ[PadicInt p] (Fin lam → PadicInt p) :=
    (e.toLinearMap.comp B).comp e.symm.toLinearMap
  let idL : (Fin lam → PadicInt p) →ₗ[PadicInt p] (Fin lam → PadicInt p) := LinearMap.id
  let idF : F.Carrier →ₗ[PadicInt p] F.Carrier := LinearMap.id
  have hbij' : Function.Bijective (idL + (p : PadicInt p) • B') :=
    bijective_id_add_p_smul p B'
  have hconj : (idL + (p : PadicInt p) • B') =
      (e.toLinearMap.comp (idF + (p : PadicInt p) • B)).comp e.symm.toLinearMap := by
    ext v
    simp [idL, idF, B']
  have hbij : Function.Bijective (idF + (p : PadicInt p) • B) := by
    refine ⟨?_, ?_⟩
    · intro x y hxy
      apply e.injective
      apply hbij'.1
      rw [hconj]
      simp [hxy]
    · intro y
      obtain ⟨v, hv⟩ := hbij'.2 (e y)
      refine ⟨e.symm v, ?_⟩
      apply e.injective
      rw [hconj] at hv
      simpa using hv
  -- Therefore `range (Φ_n • id) = range (p • id)` as `ℤ_[p]`-submodules of `F.Carrier`!
  have hrange_eq :
      (LinearMap.range (LinearMap.lsmul (IwasawaAlg p) F.Carrier (phiElem p n))).restrictScalars (PadicInt p) =
        LinearMap.range ((p : PadicInt p) • idF) := by
    ext x
    change x ∈ LinearMap.range (LinearMap.lsmul (IwasawaAlg p) F.Carrier (phiElem p n)) ↔
      x ∈ LinearMap.range ((p : PadicInt p) • idF)
    simp only [LinearMap.mem_range, LinearMap.lsmul_apply, LinearMap.smul_apply, idF,
      LinearMap.id_apply]
    constructor
    · rintro ⟨m, rfl⟩
      refine ⟨(idF + (p : PadicInt p) • B) m, ?_⟩
      exact (congrArg (fun f => f m) hB).symm
    · rintro ⟨y, rfl⟩
      obtain ⟨m, hm⟩ := hbij.2 y
      refine ⟨m, ?_⟩
      have hBm : phiElem p n • m = (p : PadicInt p) • ((idF + (p : PadicInt p) • B) m) :=
        congrArg (fun f => f m) hB
      rw [hBm, hm]
  -- Now compute `F.Carrier ⧸ range (p • id) ≃ₗ[ℤ_[p]] (Fin lam → ℤ_[p] ⧸ (p))`.
  let R := PadicInt p
  let Ip : Ideal R := Ideal.span ({(p : R)} : Set R)
  let proj : F.Carrier →ₗ[R] (Fin lam → R ⧸ Ip) :=
    { toFun := fun m i => Ideal.Quotient.mk Ip (e m i)
      map_add' := fun x y => by ext i; simp [map_add]
      map_smul' := fun r x => by
        ext i
        change Ideal.Quotient.mk Ip (e (r • x) i) = r • Ideal.Quotient.mk Ip (e x i)
        rw [map_smul, Pi.smul_apply, smul_eq_mul]
        exact map_smul (Ideal.Quotient.mkₐ R Ip).toLinearMap r (e x i) }
  have hproj_surj : Function.Surjective proj := by
    intro v
    have hl : ∀ i, ∃ a : R, Ideal.Quotient.mk Ip a = v i := fun i => Ideal.Quotient.mk_surjective _
    choose a ha using hl
    refine ⟨e.symm a, ?_⟩
    ext i
    simp [proj, ha i]
  have hproj_ker : LinearMap.ker proj = LinearMap.range ((p : R) • idF) := by
    ext x
    constructor
    · intro hx
      have hx' : ∀ i : Fin lam, ∃ c : R, e x i = (p : R) * c := fun i =>
        Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp (congrFun hx i))
      choose c hc using hx'
      refine ⟨e.symm c, ?_⟩
      change (p : R) • e.symm c = x
      apply e.injective
      ext i
      rw [map_smul, e.apply_symm_apply, Pi.smul_apply, smul_eq_mul, hc i]
    · rintro ⟨y, rfl⟩
      rw [LinearMap.mem_ker]
      ext i
      change Ideal.Quotient.mk Ip (e ((p : R) • y) i) = 0
      rw [map_smul, Pi.smul_apply, smul_eq_mul, Ideal.Quotient.eq_zero_iff_mem,
        Ideal.mem_span_singleton]
      exact ⟨e y i, rfl⟩
  let qEquiv :
      (F.Carrier ⧸ LinearMap.range (LinearMap.lsmul (IwasawaAlg p) F.Carrier (phiElem p n))) ≃ₗ[R]
        (Fin lam → R ⧸ Ip) :=
    (Submodule.quotEquivOfEq _ _ (hrange_eq.trans hproj_ker.symm)).trans
      (LinearMap.quotKerEquivOfSurjective proj hproj_surj)
  rw [qEquiv.length_eq, Module.length_pi, padicInt_length_quot_span_p, mul_one]
  simp

/-- Base length of `F` at the stabilization threshold `F.distDeg + 1`. -/
def baseLen (F : DistinguishedLattice p lam) : ℕ :=
  (Module.length (PadicInt p) (LayerQuot p (F.distDeg + 1) F.Carrier)).toNat

/-- **Linear Length Growth Upper Bound** for every distinguished `ℤ_[p]`-free lattice `F`:
for ALL `n : ℕ`, `length_{ℤ_[p]}(F / ω_n F) ≤ lam * n + F.baseLen`! -/
theorem length_layerQuot_le (F : DistinguishedLattice p lam) :
    ∀ n : ℕ, Module.length (PadicInt p) (LayerQuot p n F.Carrier) ≤
      ((lam * n + F.baseLen : ℕ) : ℕ∞) := by
  intro n
  by_cases hle : n ≤ F.distDeg + 1
  · calc Module.length (PadicInt p) (LayerQuot p n F.Carrier)
        ≤ Module.length (PadicInt p) (LayerQuot p (F.distDeg + 1) F.Carrier) :=
            length_layerQuot_mono p hle
      _ = (F.baseLen : ℕ∞) := (ENat.natCast_toNat F.baseFinite).symm
      _ ≤ ((lam * n + F.baseLen : ℕ) : ℕ∞) := by exact_mod_cast Nat.le_add_left _ _
  · have hge : F.distDeg + 1 ≤ n := by omega
    obtain ⟨k, rfl⟩ : ∃ k, n = (F.distDeg + 1) + k := ⟨n - (F.distDeg + 1), by omega⟩
    have hstep : ∀ k : ℕ,
        Module.length (PadicInt p) (LayerQuot p (F.distDeg + 1 + k) F.Carrier) ≤
          ((lam * k + F.baseLen : ℕ) : ℕ∞) := by
      intro k
      induction k with
      | zero =>
        simp only [mul_zero, zero_add]
        exact le_of_eq (ENat.natCast_toNat F.baseFinite).symm
      | succ k ih =>
        calc Module.length (PadicInt p) (LayerQuot p (F.distDeg + 1 + (k + 1)) F.Carrier)
            = Module.length (PadicInt p) (LayerQuot p ((F.distDeg + 1 + k) + 1) F.Carrier) := by
                rw [show F.distDeg + 1 + (k + 1) = (F.distDeg + 1 + k) + 1 by omega]
          _ ≤ Module.length (PadicInt p) (LayerQuot p (F.distDeg + 1 + k) F.Carrier) +
                Module.length (PadicInt p)
                  (F.Carrier ⧸ LinearMap.range
                    (LinearMap.lsmul (IwasawaAlg p) F.Carrier (phiElem p (F.distDeg + 1 + k)))) :=
                length_layerQuot_succ_le p (F.distDeg + 1 + k)
          _ = Module.length (PadicInt p) (LayerQuot p (F.distDeg + 1 + k) F.Carrier) + (lam : ℕ∞) := by
                rw [F.length_quot_phi_eq_lam (Nat.le_add_right _ _)]
          _ ≤ ((lam * k + F.baseLen : ℕ) : ℕ∞) + (lam : ℕ∞) := by gcongr
          _ = ((lam * (k + 1) + F.baseLen : ℕ) : ℕ∞) := by push_cast; ring
    refine (hstep k).trans ?_
    exact_mod_cast Nat.add_le_add_right (Nat.mul_le_mul_left lam (Nat.le_add_left k _)) F.baseLen

/-- **Exact Linear Growth Equality** when `ω_{d+1}` acts injectively on `F`:
for ALL `n ≥ F.distDeg + 1`, `length_{ℤ_[p]}(F / ω_n F) = F.baseLen + lam * (n - (F.distDeg + 1))`! -/
theorem length_layerQuot_eq_of_injective (F : DistinguishedLattice p lam)
    (hinj : Function.Injective
      (LinearMap.lsmul (IwasawaAlg p) F.Carrier (omegaElem p (F.distDeg + 1)))) :
    ∀ k : ℕ,
      Module.length (PadicInt p) (LayerQuot p (F.distDeg + 1 + k) F.Carrier) =
        ((F.baseLen + lam * k : ℕ) : ℕ∞) := by
  have hphi_inj : ∀ n : ℕ, F.distDeg + 1 ≤ n →
      Function.Injective (LinearMap.lsmul (IwasawaAlg p) F.Carrier (phiElem p n)) := by
    intro n hn
    obtain ⟨B, hB⟩ := F.phi_eq_p_smul_id_add_p_smul hn
    let e := F.freeEquiv
    let B' : (Fin lam → PadicInt p) →ₗ[PadicInt p] (Fin lam → PadicInt p) :=
      (e.toLinearMap.comp B).comp e.symm.toLinearMap
    let idL : (Fin lam → PadicInt p) →ₗ[PadicInt p] (Fin lam → PadicInt p) := LinearMap.id
    let idF : F.Carrier →ₗ[PadicInt p] F.Carrier := LinearMap.id
    have hbij' := bijective_id_add_p_smul p B'
    have hbij : Function.Injective (idF + (p : PadicInt p) • B) := by
      intro x y hxy
      apply e.injective
      apply hbij'.1
      have h1 : (idL + (p : PadicInt p) • B') (e x) = e ((idF + (p : PadicInt p) • B) x) := by
        simp [idL, idF, B']
      have h2 : (idL + (p : PadicInt p) • B') (e y) = e ((idF + (p : PadicInt p) • B) y) := by
        simp [idL, idF, B']
      rw [h1, h2, hxy]
    have hp_inj : Function.Injective ((p : PadicInt p) • (LinearMap.id : F.Carrier →ₗ[PadicInt p] F.Carrier)) := by
      intro x y hxy
      apply e.injective
      ext i
      have hi : (p : PadicInt p) * e x i = (p : PadicInt p) * e y i := by
        have := congrArg (fun z => e z i) hxy
        simpa [map_smul, Pi.smul_apply, smul_eq_mul] using this
      exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hi
    intro x y hxy
    apply hbij
    apply hp_inj
    have hx : phiElem p n • x = (p : PadicInt p) • ((idF + (p : PadicInt p) • B) x) :=
      congrArg (fun f => f x) hB
    have hy : phiElem p n • y = (p : PadicInt p) • ((idF + (p : PadicInt p) • B) y) :=
      congrArg (fun f => f y) hB
    change (p : PadicInt p) • ((idF + (p : PadicInt p) • B) x) =
      (p : PadicInt p) • ((idF + (p : PadicInt p) • B) y)
    rw [← hx, ← hy]
    exact hxy
  have homega_inj : ∀ k : ℕ,
      Function.Injective
        (LinearMap.lsmul (IwasawaAlg p) F.Carrier (omegaElem p (F.distDeg + 1 + k))) := by
    intro k
    induction k with
    | zero => simpa using hinj
    | succ k ih =>
      rw [← add_assoc]
      intro x y hxy
      have h1 : omegaElem p (F.distDeg + 1 + k) • (phiElem p (F.distDeg + 1 + k) • x) =
          omegaElem p (F.distDeg + 1 + k) • (phiElem p (F.distDeg + 1 + k) • y) := by
        simpa [LinearMap.lsmul_apply, omegaElem_succ, mul_smul] using hxy
      exact hphi_inj _ (Nat.le_add_right _ _) (ih h1)
  intro k
  induction k with
  | zero =>
    simp only [add_zero, mul_zero]
    exact (ENat.natCast_toNat F.baseFinite).symm
  | succ k ih =>
    rw [← add_assoc]
    unfold LayerQuot layerSubmodule
    rw [omegaElem_succ p (F.distDeg + 1 + k)]
    rw [length_quot_mul_eq_of_injective p _ _ (homega_inj k)]
    change Module.length (PadicInt p) (LayerQuot p (F.distDeg + 1 + k) F.Carrier) +
      Module.length (PadicInt p)
        (F.Carrier ⧸ LinearMap.range
          (LinearMap.lsmul (IwasawaAlg p) F.Carrier (phiElem p (F.distDeg + 1 + k)))) = _
    rw [ih, F.length_quot_phi_eq_lam (Nat.le_add_right _ _)]
    push_cast
    ring

end DistinguishedLattice

end ElementaryModules

/-! ## Section 4: Full Iwasawa Structure Theorem Growth Formula & Ferrero–Washington (`μ = 0`) -/

section IwasawaGrowthFormula

variable (p : ℕ) [Fact p.Prime]

/-- **Iwasawa Structure Model** for a finitely generated torsion `Λ_p`-module `M`:
a pseudo-isomorphism `φ : M →ₗ[Λ_p] (⨁_{i} Λ_p / (p^{m_i})) × F_λ` with finite kernel and
cokernel, recording the exact Iwasawa invariants `μ = ∑ m_i`, `λ = rank(F_λ)`, and `ν`. -/
structure IwasawaModuleModel (M : Type) [AddCommGroup M]
    [Module (PadicInt p) M] [Module (IwasawaAlg p) M] [IsScalarTower (PadicInt p) (IwasawaAlg p) M] where
  muExps : List ℕ
  lamInvariant : ℕ
  freePart : DistinguishedLattice p lamInvariant
  pseudoIso :
    M →ₗ[IwasawaAlg p]
      ((i : Fin muExps.length) → ElemPTorsion p (muExps.get i)) × freePart.Carrier
  ker_finite : Module.length (PadicInt p) (LinearMap.ker pseudoIso) ≠ ⊤
  coker_finite : Module.length (PadicInt p) (_ ⧸ LinearMap.range pseudoIso) ≠ ⊤

namespace IwasawaModuleModel

variable {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M]
  [Module (PadicInt p) M] [Module (IwasawaAlg p) M] [IsScalarTower (PadicInt p) (IwasawaAlg p) M]

/-- The Iwasawa `μ`-invariant `μ(M) = ∑_i m_i`. -/
def mu (model : IwasawaModuleModel p M) : ℕ := model.muExps.sum

/-- The Iwasawa `λ`-invariant `λ(M)`. -/
def lam (model : IwasawaModuleModel p M) : ℕ := model.lamInvariant

/-- The Iwasawa `ν`-offset bound `ν(M) = baseLen(F_λ) + length(ker φ) + length(coker φ)`. -/
def nu (model : IwasawaModuleModel p M) : ℕ :=
  model.freePart.baseLen +
    (Module.length (PadicInt p) (LinearMap.ker model.pseudoIso)).toNat +
    (Module.length (PadicInt p) (_ ⧸ LinearMap.range model.pseudoIso)).toNat

/-- Helper: sum of `List.get` over `Fin L.length` equals `L.sum`. -/
theorem sum_fin_get_eq_list_sum (L : List ℕ) :
    (∑ i : Fin L.length, L.get i) = L.sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.length_cons, Fin.sum_univ_succ, List.get_eq_getElem, List.sum_cons]
    congr 1

/-- **Iwasawa `p`-adic Length Growth Formula**:
for every `IwasawaModuleModel p M` and every tower level `n : ℕ`:
1. `length_{ℤ_[p]}(M / ω_n M) ≠ ⊤`,
2. `e_n := (length_{ℤ_[p]}(M / ω_n M)).toNat ≤ λ * n + μ * p ^ n + ν`,
3. `Finite (M / ω_n M)` and `|M / ω_n M| ≤ p ^ (λ * n + μ * p ^ n + ν)`! -/
theorem iwasawa_length_growth_formula (model : IwasawaModuleModel p M) (n : ℕ) :
    Module.length (PadicInt p) (LayerQuot p n M) ≠ ⊤ ∧
    (Module.length (PadicInt p) (LayerQuot p n M)).toNat ≤
      model.lam * n + model.mu * p ^ n + model.nu ∧
    Finite (LayerQuot p n M) ∧
    Nat.card (LayerQuot p n M) ≤ p ^ (model.lam * n + model.mu * p ^ n + model.nu) := by
  have htor : Module.length (PadicInt p)
      (LayerQuot p n (∀ i : Fin model.muExps.length, ElemPTorsion p (model.muExps.get i))) =
        ((model.mu * p ^ n : ℕ) : ℕ∞) := by
    rw [(layerQuotPiEquiv p n).length_eq, length_pi_fin]
    have hsum : (∑ i : Fin model.muExps.length,
        Module.length (PadicInt p) (LayerQuot p n (ElemPTorsion p (model.muExps.get i)))) =
        ∑ i : Fin model.muExps.length, ((model.muExps.get i * p ^ n : ℕ) : ℕ∞) := by
      refine Finset.sum_congr rfl fun i _ => length_layerQuot_elemPTorsion p n (model.muExps.get i)
    rw [hsum, ← Nat.cast_sum, ← Finset.sum_mul, sum_fin_get_eq_list_sum]
    rfl
  have hfree : Module.length (PadicInt p) (LayerQuot p n model.freePart.Carrier) ≤
      ((model.lam * n + model.freePart.baseLen : ℕ) : ℕ∞) :=
    model.freePart.length_layerQuot_le n
  have hE : Module.length (PadicInt p)
      (LayerQuot p n
        (((i : Fin model.muExps.length) → ElemPTorsion p (model.muExps.get i)) ×
          model.freePart.Carrier)) ≤
      ((model.mu * p ^ n + (model.lam * n + model.freePart.baseLen) : ℕ) : ℕ∞) := by
    rw [(layerQuotProdEquiv p n).length_eq, length_prod, htor]
    rw [Nat.cast_add]
    exact add_le_add_right hfree _
  have hker : Module.length (PadicInt p) (LinearMap.ker model.pseudoIso) =
      ((Module.length (PadicInt p) (LinearMap.ker model.pseudoIso)).toNat : ℕ∞) :=
    (ENat.natCast_toNat model.ker_finite).symm
  have hcoker : Module.length (PadicInt p) (_ ⧸ LinearMap.range model.pseudoIso) =
      ((Module.length (PadicInt p) (_ ⧸ LinearMap.range model.pseudoIso)).toNat : ℕ∞) :=
    (ENat.natCast_toNat model.coker_finite).symm
  have hle : Module.length (PadicInt p) (LayerQuot p n M) ≤
      ((model.lam * n + model.mu * p ^ n + model.nu : ℕ) : ℕ∞) := by
    calc Module.length (PadicInt p) (LayerQuot p n M)
        ≤ Module.length (PadicInt p)
            (LayerQuot p n
              (((i : Fin model.muExps.length) → ElemPTorsion p (model.muExps.get i)) ×
                model.freePart.Carrier)) +
            Module.length (PadicInt p) (LinearMap.ker model.pseudoIso) +
            Module.length (PadicInt p) (_ ⧸ LinearMap.range model.pseudoIso) :=
              length_layerQuot_le_of_pseudoIso p model.pseudoIso n
      _ ≤ ((model.mu * p ^ n + (model.lam * n + model.freePart.baseLen) : ℕ) : ℕ∞) +
            ((Module.length (PadicInt p) (LinearMap.ker model.pseudoIso)).toNat : ℕ∞) +
            ((Module.length (PadicInt p) (_ ⧸ LinearMap.range model.pseudoIso)).toNat : ℕ∞) := by
              rw [hker, hcoker]
              exact add_le_add_left (add_le_add_left hE _) _
      _ = ((model.lam * n + model.mu * p ^ n + model.nu : ℕ) : ℕ∞) := by
              unfold nu
              push_cast
              ring
  have hne : Module.length (PadicInt p) (LayerQuot p n M) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle
  obtain ⟨hfin, hcard⟩ := padicInt_card_le_of_length_le hle
  exact ⟨hne, ENat.toNat_le_of_le_natCast hle, hfin, hcard⟩

/-- **Ferrero–Washington (`μ = 0`) Length & Cardinality Collapse**:
whenever `model.mu = 0`, we have `e_n ≤ λ * n + ν` and `|A_n| ≤ C * p ^ (λ * n)` with `C = p ^ ν`! -/
theorem ferrero_washington_card_bound (model : IwasawaModuleModel p M)
    (hmu : model.mu = 0) (n : ℕ) :
    Module.length (PadicInt p) (LayerQuot p n M) ≠ ⊤ ∧
    (Module.length (PadicInt p) (LayerQuot p n M)).toNat ≤ model.lam * n + model.nu ∧
    Finite (LayerQuot p n M) ∧
    Nat.card (LayerQuot p n M) ≤ p ^ model.nu * p ^ (model.lam * n) := by
  obtain ⟨hne, hlen, hfin, hcard⟩ := model.iwasawa_length_growth_formula n
  rw [hmu, zero_mul, add_zero] at hlen hcard
  refine ⟨hne, hlen, hfin, ?_⟩
  rw [← pow_add, add_comm]
  exact hcard

end IwasawaModuleModel

/-- Concrete non-vacuous rank-`0` distinguished lattice over `Λ_p` using `ElemPTorsion p 0`. -/
def concreteZeroLattice (p : ℕ) [Fact p.Prime] : DistinguishedLattice p 0 where
  Carrier := ElemPTorsion p 0
  freeEquiv :=
    { toFun := fun _ i => i.elim0
      invFun := fun _ => 0
      map_add' := fun _ _ => funext fun i => i.elim0
      map_smul' := fun _ _ => funext fun i => i.elim0
      left_inv := fun x => by
        have htop : Ideal.span ({(PowerSeries.C (p : PadicInt p)) ^ 0} : Set (IwasawaAlg p)) = ⊤ := by
          rw [pow_zero, Ideal.span_singleton_one]
        have hsub : Subsingleton (ElemPTorsion p 0) := by
          unfold ElemPTorsion
          rw [htop]
          infer_instance
        exact hsub.elim 0 x
      right_inv := fun v => funext fun i => i.elim0 }
  distDeg := 0
  topNilpotent := ⟨0, by
    have htop : Ideal.span ({(PowerSeries.C (p : PadicInt p)) ^ 0} : Set (IwasawaAlg p)) = ⊤ := by
      rw [pow_zero, Ideal.span_singleton_one]
    have hsub : Subsingleton (ElemPTorsion p 0) := by
      unfold ElemPTorsion
      rw [htop]
      infer_instance
    ext x
    exact hsub.elim _ _⟩
  baseFinite := by
    rw [length_layerQuot_elemPTorsion p 1 0]
    exact ENat.natCast_ne_top _

/-- Concrete non-vacuous `IwasawaModuleModel p (ElemPTorsion p m)` realizing arbitrary `μ = m`,
`λ = 0`, `ν = 0` (including the Ferrero–Washington `μ = 0` witness at `m = 0`). -/
def concretePTorsionModel (p : ℕ) [Fact p.Prime] (m : ℕ) :
    IwasawaModuleModel p (ElemPTorsion p m) :=
  let φ : ElemPTorsion p m →ₗ[IwasawaAlg p]
      ((i : Fin ([m] : List ℕ).length) → ElemPTorsion p ([m].get i)) × (concreteZeroLattice p).Carrier :=
    { toFun := fun x => (fun i => match i with | ⟨0, _⟩ => x, 0)
      map_add' := fun x y => by
        apply Prod.ext
        · ext i
          rcases i with ⟨k, hk⟩
          have hk0 : k = 0 := by simp at hk; omega
          subst hk0
          rfl
        · simp
      map_smul' := fun r x => by
        apply Prod.ext
        · ext i
          rcases i with ⟨k, hk⟩
          have hk0 : k = 0 := by simp at hk; omega
          subst hk0
          rfl
        · simp }
  { muExps := [m]
    lamInvariant := 0
    freePart := concreteZeroLattice p
    pseudoIso := φ
    ker_finite := by
      have hsub : Subsingleton (LinearMap.ker φ) := by
        refine ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ => Subtype.ext ?_⟩
        have hx0 : x = 0 := congrFun (congrArg Prod.fst hx) ⟨0, by simp⟩
        have hy0 : y = 0 := congrFun (congrArg Prod.fst hy) ⟨0, by simp⟩
        exact hx0.trans hy0.symm
      rw [Module.length_eq_zero]
      exact ENat.natCast_ne_top 0
    coker_finite := by
      have htop0 : Ideal.span ({(PowerSeries.C (p : PadicInt p)) ^ 0} : Set (IwasawaAlg p)) = ⊤ := by
        rw [pow_zero, Ideal.span_singleton_one]
      have hsub0 : Subsingleton (ElemPTorsion p 0) := by
        unfold ElemPTorsion
        rw [htop0]
        infer_instance
      have hsurj : Function.Surjective φ := by
        rintro ⟨f, z⟩
        refine ⟨f ⟨0, by simp⟩, Prod.ext ?_ (hsub0.elim 0 z)⟩
        ext i
        rcases i with ⟨k, hk⟩
        have hk0 : k = 0 := by simp at hk; omega
        subst hk0
        rfl
      have htop : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hsurj
      have hsub : Subsingleton (_ ⧸ LinearMap.range φ) := by rw [htop]; infer_instance
      rw [Module.length_eq_zero]
      exact ENat.natCast_ne_top 0 }

end IwasawaGrowthFormula

/-! ## Section 5: Quantitative `PageN` Exponential Domination (`μ = 0` vs `μ ≥ 1`) -/

section PageNExponentialDomination

/-- Logarithmic upper bound on the tower level `e` from `PageN eps x e`. -/
theorem pageN_level_le_log {eps x : ℝ} {e : ℕ} (hx : 1 ≤ x) (hP : PageN eps x e) :
    (e : ℝ) ≤ ((2 + 8 * eps) * Real.log x + Real.log 2) / Real.log 2 := by
  have hxpos : 0 < x := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ e) hP.2
  rw [Real.log_pow, Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hxpos _).ne',
    Real.log_rpow hxpos] at hlog
  rw [le_div_iff₀ hlog2]
  linarith

/-- Logarithmic upper bound on `e x` from `TaylorWilesWindow.AdmissiblePage A1 Ct e t`. -/
theorem admissiblePage_level_le_log {A1 Ct : ℝ} {e t : ℝ → ℕ}
    (hadm : TaylorWilesWindow.AdmissiblePage A1 Ct e t) {x : ℝ} (hx : 2 ≤ x) :
    (e x : ℝ) ≤ A1 * Real.log x / Real.log 2 := by
  have hxpos : 0 < x := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2 := (hadm x hx).2.1
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ e x) h2
  rw [Real.log_pow, Real.log_rpow hxpos] at hlog
  rw [le_div_iff₀ hlog2]
  exact hlog

/-- **Ferrero–Washington (`μ = 0`) Exponential Domination on `PageN` Windows**:
for any `ε > 0`, `C ≥ 0`, and `λ : ℕ`, on all sufficiently large `PageN eps x e` windows the
`μ = 0` Iwasawa cardinality bound `C * 2 ^ (λ * e)` is **strictly smaller** than BOTH
`exp(x ^ (4 * ε / 5))` and `exp(x ^ ε)`! -/
theorem ferrero_washington_card_lt_exp_rpow_of_pageN (eps C : ℝ) (lam : ℕ)
    (heps : 0 < eps) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ e : ℕ, PageN eps x e →
      C * ((2 : ℝ) ^ (lam * e)) < Real.exp (x ^ (4 * eps / 5)) ∧
      C * ((2 : ℝ) ^ (lam * e)) < Real.exp (x ^ eps) := by
  set α : ℝ := (lam : ℝ) * (2 + 8 * eps)
  set K : ℝ := (|C| + 1) * (2 : ℝ) ^ lam
  have hKpos : 0 < K := by positivity
  have hr : 0 < 4 * eps / 5 := by positivity
  have h1 := (isLittleO_log_rpow_atTop hr).bound
    (show (0 : ℝ) < 1 / (2 * (|α| + 1)) by positivity)
  have h2 := (tendsto_rpow_atTop hr).eventually_ge_atTop (2 * (|Real.log K| + 1))
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 ((h1.and h2).and (Filter.eventually_ge_atTop 1))
  refine ⟨x0, fun x hx e hP => ?_⟩
  obtain ⟨⟨hl, hg⟩, hx1⟩ := hx0 x hx
  have hxpos : 0 < x := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hXpos : 0 < x ^ (4 * eps / 5) := Real.rpow_pos_of_pos hxpos _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlogx, abs_of_pos hXpos] at hl
  have hpow2 : ((2 : ℝ) ^ (lam * e)) ≤ (2 : ℝ) ^ lam * x ^ α := by
    calc (2 : ℝ) ^ (lam * e)
        = ((2 : ℝ) ^ e) ^ lam := by rw [mul_comm, pow_mul]
      _ ≤ (2 * x ^ (2 + 8 * eps)) ^ lam :=
          pow_le_pow_left₀ (by positivity) hP.2 lam
      _ = (2 : ℝ) ^ lam * (x ^ (2 + 8 * eps)) ^ lam := mul_pow _ _ _
      _ = (2 : ℝ) ^ lam * x ^ α := by
          rw [← Real.rpow_natCast (x ^ (2 + 8 * eps)), ← Real.rpow_mul hxpos.le]
          congr 2
          ring
  have hcard_le : C * ((2 : ℝ) ^ (lam * e)) ≤ K * x ^ α := by
    have hC : C ≤ |C| + 1 := by linarith [le_abs_self C]
    calc C * ((2 : ℝ) ^ (lam * e))
        ≤ (|C| + 1) * ((2 : ℝ) ^ lam * x ^ α) :=
          mul_le_mul hC hpow2 (by positivity) (by positivity)
      _ = K * x ^ α := by ring
  have hKxa : K * x ^ α = Real.exp (Real.log K + α * Real.log x) := by
    rw [Real.exp_add, Real.exp_log hKpos, Real.rpow_def_of_pos hxpos, mul_comm (Real.log x) α]
  have hαlog : α * Real.log x ≤ x ^ (4 * eps / 5) / 2 := by
    have hα_le : α ≤ |α| + 1 := by linarith [le_abs_self α]
    calc α * Real.log x
        ≤ (|α| + 1) * Real.log x := mul_le_mul_of_nonneg_right hα_le hlogx
      _ ≤ (|α| + 1) * (1 / (2 * (|α| + 1)) * x ^ (4 * eps / 5)) :=
          mul_le_mul_of_nonneg_left hl (by positivity)
      _ = x ^ (4 * eps / 5) / 2 := by field_simp
  have hlogK_lt : Real.log K < x ^ (4 * eps / 5) / 2 := by
    have := le_abs_self (Real.log K)
    linarith
  have hlt1 : C * ((2 : ℝ) ^ (lam * e)) < Real.exp (x ^ (4 * eps / 5)) := by
    calc C * ((2 : ℝ) ^ (lam * e))
        ≤ K * x ^ α := hcard_le
      _ = Real.exp (Real.log K + α * Real.log x) := hKxa
      _ < Real.exp (x ^ (4 * eps / 5)) := Real.exp_lt_exp.mpr (by linarith)
  have hlt2 : Real.exp (x ^ (4 * eps / 5)) ≤ Real.exp (x ^ eps) :=
    Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith))
  exact ⟨hlt1, lt_of_lt_of_le hlt1 hlt2⟩

/-- **Sharp Contrast (`μ ≥ 1` Blow-Up on `PageN`)**:
if `μ ≥ 1` and `0 < ε < 1 / 52`, then for all sufficiently large `x`, `exp(x ^ ε) < 2 ^ (μ * 2 ^ e)`
on every `PageN eps x e` window — proving mathematically why Ferrero–Washington (`μ = 0`) is
indispensable! -/
theorem mu_pos_card_gt_exp_rpow_of_pageN (eps : ℝ) (mu : ℕ)
    (heps : 0 < eps) (heps1 : eps < 1 / 52) (hmu : 1 ≤ mu) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ e : ℕ, PageN eps x e →
      Real.exp (x ^ eps) < (2 : ℝ) ^ (mu * 2 ^ e) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hr : 0 < 2 + 7 * eps := by linarith
  have h1 := (tendsto_rpow_atTop hr).eventually_gt_atTop (1 / Real.log 2)
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 (h1.and (Filter.eventually_ge_atTop 1))
  refine ⟨x0, fun x hx e hP => ?_⟩
  obtain ⟨hgt, hx1⟩ := hx0 x hx
  have hxpos : 0 < x := by linarith
  have hmu1 : (1 : ℝ) ≤ (mu : ℝ) := by exact_mod_cast hmu
  have hpow_eq : (2 : ℝ) ^ (mu * 2 ^ e) = Real.exp (((mu : ℝ) * (2 : ℝ) ^ e) * Real.log 2) := by
    rw [← Real.rpow_natCast (2 : ℝ), Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    push_cast
    ring
  rw [hpow_eq]
  apply Real.exp_lt_exp.mpr
  have hsplit : x ^ (2 + 8 * eps) = x ^ eps * x ^ (2 + 7 * eps) := by
    rw [← Real.rpow_add hxpos]
    congr 1
    ring
  have h1lt : 1 < x ^ (2 + 7 * eps) * Real.log 2 := by
    have := (div_lt_iff₀ hlog2).mp hgt
    linarith
  have hxeps_pos : 0 < x ^ eps := Real.rpow_pos_of_pos hxpos _
  calc x ^ eps
      = x ^ eps * 1 := (mul_one _).symm
    _ < x ^ eps * (x ^ (2 + 7 * eps) * Real.log 2) := mul_lt_mul_of_pos_left h1lt hxeps_pos
    _ = x ^ (2 + 8 * eps) * Real.log 2 := by rw [← mul_assoc, ← hsplit]
    _ ≤ (2 : ℝ) ^ e * Real.log 2 := mul_le_mul_of_nonneg_right hP.1 hlog2.le
    _ ≤ ((mu : ℝ) * (2 : ℝ) ^ e) * Real.log 2 := by
        have h2pos : (0 : ℝ) ≤ (2 : ℝ) ^ e := by positivity
        exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_left h2pos hmu1) hlog2.le

/-- **Quantitative `B₂` Sum Absorption on `AdmissiblePage`**:
if at each scale `x` and twist weight `1 ≤ k < t x`, the `μ = 0` Iwasawa invariants satisfy
`lam_k + nu_k ≤ A * exp(α * x ^ (eps / 4))` (which automatically holds for any fixed invariants
OR any polynomial bound in `condF E * t x` with `log(condF E * t x) ≤ 2 * x ^ (eps / 4)`!),
then for all sufficiently large `x`,
`∑ k ∈ Finset.Ico 1 (t x), (lam_k * e x + nu_k) ≤ Real.exp (x ^ (4 * eps / 5))`! -/
theorem iwasawa_two_sum_le_exp_of_admissible (eps A1 Ct A α : ℝ)
    (heps : 0 < eps) (hA1 : 0 < A1) (hCt : 0 ≤ Ct) (hA : 0 ≤ A) :
    ∃ x0 : ℝ, 2 ≤ x0 ∧ ∀ (e t : ℝ → ℕ), TaylorWilesWindow.AdmissiblePage A1 Ct e t →
      ∀ x ≥ x0, ∀ (lam nu : ℕ → ℕ),
        (∀ k ∈ Finset.Ico 1 (t x), ((lam k + nu k : ℕ) : ℝ) ≤ A * Real.exp (α * x ^ (eps / 4))) →
        ∑ k ∈ Finset.Ico 1 (t x), ((lam k * e x + nu k : ℕ) : ℝ) ≤
          Real.exp (x ^ (4 * eps / 5)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K : ℝ := (A + 1) * (A1 / Real.log 2 + 1)
  have hKpos : 0 < K := by positivity
  have hr : 0 < 4 * eps / 5 := by positivity
  have hdiff : 0 < 11 * eps / 20 := by positivity
  have h1 := (isLittleO_log_rpow_atTop hr).bound
    (show (0 : ℝ) < 1 / (3 * (Ct + 2)) by positivity)
  have h2 := (tendsto_rpow_atTop hr).eventually_ge_atTop (3 * (|Real.log K| + 1))
  have h3 := (tendsto_rpow_atTop hdiff).eventually_ge_atTop (3 * (α + 1))
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1
    (((h1.and h2).and h3).and (Filter.eventually_ge_atTop 2))
  refine ⟨max x0 2, le_max_right _ _, fun e t hadm x hx lam nu hinv => ?_⟩
  obtain ⟨⟨⟨hl, hg⟩, hαg⟩, hx2⟩ := hx0 x (le_trans (le_max_left _ _) hx)
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hXpos : 0 < x ^ (4 * eps / 5) := Real.rpow_pos_of_pos hxpos _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlogx, abs_of_pos hXpos] at hl
  have he_le : (e x : ℝ) + 1 ≤ (A1 / Real.log 2 + 1) * x := by
    have hel := admissiblePage_level_le_log hadm hx2
    have hlogx_le : Real.log x ≤ x := by
      have := Real.log_le_sub_one_of_pos hxpos
      linarith
    have h1x : (1 : ℝ) ≤ x := hx1
    have hdiv : A1 * Real.log x / Real.log 2 = (A1 / Real.log 2) * Real.log x := by ring
    rw [hdiv] at hel
    have hmul : (A1 / Real.log 2) * Real.log x ≤ (A1 / Real.log 2) * x :=
      mul_le_mul_of_nonneg_left hlogx_le (by positivity)
    linarith
  have ht_le : (t x : ℝ) ≤ x ^ Ct := (hadm x hx2).2.2.2
  have hcard_le : ((Finset.Ico 1 (t x)).card : ℝ) ≤ x ^ Ct := by
    have hc : (Finset.Ico 1 (t x)).card ≤ t x := by simp
    exact le_trans (by exact_mod_cast hc) ht_le
  have hterm : ∀ k ∈ Finset.Ico 1 (t x),
      ((lam k * e x + nu k : ℕ) : ℝ) ≤
        (A + 1) * Real.exp (α * x ^ (eps / 4)) * ((A1 / Real.log 2 + 1) * x) := by
    intro k hk
    have hkn : ((lam k * e x + nu k : ℕ) : ℝ) ≤ ((lam k + nu k : ℕ) : ℝ) * ((e x : ℝ) + 1) := by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) (lam k), Nat.cast_nonneg (α := ℝ) (nu k),
        Nat.cast_nonneg (α := ℝ) (e x)]
    have hA_le : A * Real.exp (α * x ^ (eps / 4)) ≤ (A + 1) * Real.exp (α * x ^ (eps / 4)) := by
      have := Real.exp_pos (α * x ^ (eps / 4))
      linarith
    calc ((lam k * e x + nu k : ℕ) : ℝ)
        ≤ ((lam k + nu k : ℕ) : ℝ) * ((e x : ℝ) + 1) := hkn
      _ ≤ ((A + 1) * Real.exp (α * x ^ (eps / 4))) * ((A1 / Real.log 2 + 1) * x) :=
          mul_le_mul ((hinv k hk).trans hA_le) he_le (by positivity) (by positivity)
  have hsum_le : ∑ k ∈ Finset.Ico 1 (t x), ((lam k * e x + nu k : ℕ) : ℝ) ≤
      K * x ^ (Ct + 1) * Real.exp (α * x ^ (eps / 4)) := by
    calc ∑ k ∈ Finset.Ico 1 (t x), ((lam k * e x + nu k : ℕ) : ℝ)
        ≤ ∑ _k ∈ Finset.Ico 1 (t x),
            (A + 1) * Real.exp (α * x ^ (eps / 4)) * ((A1 / Real.log 2 + 1) * x) :=
          Finset.sum_le_sum hterm
      _ = ((Finset.Ico 1 (t x)).card : ℝ) *
            ((A + 1) * Real.exp (α * x ^ (eps / 4)) * ((A1 / Real.log 2 + 1) * x)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ x ^ Ct * ((A + 1) * Real.exp (α * x ^ (eps / 4)) * ((A1 / Real.log 2 + 1) * x)) :=
          mul_le_mul_of_nonneg_right hcard_le (by positivity)
      _ = K * (x ^ Ct * x) * Real.exp (α * x ^ (eps / 4)) := by ring
      _ = K * x ^ (Ct + 1) * Real.exp (α * x ^ (eps / 4)) := by
          rw [Real.rpow_add_one hxpos.ne']
  have hRHS : K * x ^ (Ct + 1) * Real.exp (α * x ^ (eps / 4)) =
      Real.exp (Real.log K + (Ct + 1) * Real.log x + α * x ^ (eps / 4)) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_log hKpos, Real.rpow_def_of_pos hxpos,
      mul_comm (Real.log x) (Ct + 1)]
  have hp1 : Real.log K ≤ x ^ (4 * eps / 5) / 3 := by
    have := le_abs_self (Real.log K)
    linarith
  have hp2 : (Ct + 1) * Real.log x ≤ x ^ (4 * eps / 5) / 3 := by
    calc (Ct + 1) * Real.log x
        ≤ (Ct + 2) * Real.log x := by nlinarith
      _ ≤ (Ct + 2) * (1 / (3 * (Ct + 2)) * x ^ (4 * eps / 5)) :=
          mul_le_mul_of_nonneg_left hl (by positivity)
      _ = x ^ (4 * eps / 5) / 3 := by field_simp
  have hp3 : α * x ^ (eps / 4) ≤ x ^ (4 * eps / 5) / 3 := by
    have hsplit : x ^ (4 * eps / 5) = x ^ (eps / 4) * x ^ (11 * eps / 20) := by
      rw [← Real.rpow_add hxpos]
      congr 1
      ring
    have hxa_pos : 0 ≤ x ^ (eps / 4) := by positivity
    rw [hsplit]
    have hmul : (3 * (α + 1)) * x ^ (eps / 4) ≤ x ^ (11 * eps / 20) * x ^ (eps / 4) :=
      mul_le_mul_of_nonneg_right hαg hxa_pos
    linarith
  calc ∑ k ∈ Finset.Ico 1 (t x), ((lam k * e x + nu k : ℕ) : ℝ)
      ≤ K * x ^ (Ct + 1) * Real.exp (α * x ^ (eps / 4)) := hsum_le
    _ = Real.exp (Real.log K + (Ct + 1) * Real.log x + α * x ^ (eps / 4)) := hRHS
    _ ≤ Real.exp (x ^ (4 * eps / 5)) := Real.exp_le_exp.mpr (by linarith)

/-- Helper: any finite set `P₂` of primes all equal to `2` has at most the single prime `⟨2, prime_two⟩`,
so summing `log l * f l` over `P₂` is bounded by `f ⟨2, prime_two⟩ * log 2` whenever `0 ≤ f`. -/
theorem sum_prime_two_finset_le {f : Nat.Primes → ℝ} (hf : 0 ≤ f ⟨2, Nat.prime_two⟩)
    (P₂ : Finset Nat.Primes) (hP₂ : ∀ l ∈ P₂, (l : ℕ) = 2) :
    ∑ l ∈ P₂, Real.log (l : ℕ) * f l ≤ f ⟨2, Nat.prime_two⟩ * Real.log 2 := by
  let twoP : Nat.Primes := ⟨2, Nat.prime_two⟩
  have hsub : P₂ ⊆ ({twoP} : Finset Nat.Primes) := by
    intro l hl
    rw [Finset.mem_singleton]
    exact Subtype.ext (hP₂ l hl)
  have hnonneg : ∀ l ∈ ({twoP} : Finset Nat.Primes),
      0 ≤ Real.log (l : ℕ) * f l := by
    intro l hl
    rw [Finset.mem_singleton] at hl
    subst hl
    exact mul_nonneg (Real.log_natCast_nonneg 2) hf
  calc ∑ l ∈ P₂, Real.log (l : ℕ) * f l
      ≤ ∑ l ∈ ({twoP} : Finset Nat.Primes), Real.log (l : ℕ) * f l :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun l hl _ => hnonneg l hl
    _ = Real.log 2 * f twoP := by
        rw [Finset.sum_singleton]
        rfl
    _ = f ⟨2, Nat.prime_two⟩ * Real.log 2 := mul_comm _ _

end PageNExponentialDomination

/-! ## Section 6: Direct Discharge of `B₂` into `TaylorWilesWindow.vvle_of_three_parts` & `ThreePartPatchingWindow` -/

section ThreePartDischarge

/-- Pointwise **`l = 2` Iwasawa 2-Tower + Ferrero–Washington (`μ = 0`) Selmer Realization**
at a host field `E`, 2-tower height `level`, and twist weight `k`:
realizes `S.shaLen E ⟨2, prime_two⟩ k` inside the `level`-th finite-level quotient
`M / ((1 + T)^(2^level) - 1) M` of a `μ = 0` Iwasawa module over `ℤ_[2][[T]]`! -/
structure IwasawaTwoTowerBound (S : SelmerSystem) (E : Type) [Field E] [NumberField E]
    (level k : ℕ) where
  M : Type
  [addM : AddCommGroup M]
  [modZ : Module (PadicInt 2) M]
  [modLam : Module (IwasawaAlg 2) M]
  [tower : IsScalarTower (PadicInt 2) (IwasawaAlg 2) M]
  model : IwasawaModuleModel 2 M
  /-- Ferrero–Washington vanishing `μ = 0` along the cyclotomic `2`-tower! -/
  ferrero_washington : model.mu = 0
  Sel : Type
  [addSel : AddCommGroup Sel]
  [modSel : Module (PadicInt 2) Sel]
  embed : Sel →ₗ[PadicInt 2] LayerQuot 2 level M
  embed_inj : Function.Injective embed
  sha_le_selmer : S.shaLen E ⟨2, Nat.prime_two⟩ k ≤ Module.length (PadicInt 2) Sel

attribute [instance] IwasawaTwoTowerBound.addM IwasawaTwoTowerBound.modZ
  IwasawaTwoTowerBound.modLam IwasawaTwoTowerBound.tower
  IwasawaTwoTowerBound.addSel IwasawaTwoTowerBound.modSel

namespace IwasawaTwoTowerBound

variable {S : SelmerSystem} {E : Type} [Field E] [NumberField E] {level k : ℕ}

/-- Effective `l = 2` length upper bound `λ * level + ν` from `μ = 0`. -/
def lenBound (B : IwasawaTwoTowerBound S E level k) : ℕ :=
  B.model.lam * level + B.model.nu

/-- **Discharges BOTH `l = 2` Selmer finiteness AND linear length bound** directly from
`IwasawaModuleModel.ferrero_washington_card_bound`! -/
theorem shaLen_finite_and_le (B : IwasawaTwoTowerBound S E level k) :
    S.shaLen E ⟨2, Nat.prime_two⟩ k ≠ ⊤ ∧
      (S.shaLen E ⟨2, Nat.prime_two⟩ k).toNat ≤ B.lenBound := by
  obtain ⟨hfinQ, hlenQ, _, _⟩ := B.model.ferrero_washington_card_bound B.ferrero_washington level
  have hSel_le : Module.length (PadicInt 2) B.Sel ≤
      Module.length (PadicInt 2) (LayerQuot 2 level B.M) :=
    Module.length_le_of_injective B.embed B.embed_inj
  have hsha_le : S.shaLen E ⟨2, Nat.prime_two⟩ k ≤
      Module.length (PadicInt 2) (LayerQuot 2 level B.M) :=
    B.sha_le_selmer.trans hSel_le
  refine ⟨ne_top_of_le_ne_top hfinQ hsha_le, ?_⟩
  exact (ENat.toNat_le_toNat hsha_le hfinQ).trans hlenQ

/-- Exact cardinality bound on the `2`-Selmer group `Sel`: `|Sel| ≤ 2^ν * 2^(λ * level)`. -/
theorem selmer_card_le (B : IwasawaTwoTowerBound S E level k) :
    Finite B.Sel ∧ Nat.card B.Sel ≤ 2 ^ B.model.nu * 2 ^ (B.model.lam * level) := by
  obtain ⟨hfinQ, hlenQ, _, _⟩ := B.model.ferrero_washington_card_bound B.ferrero_washington level
  have hle : Module.length (PadicInt 2) B.Sel ≤ ((B.model.lam * level + B.model.nu : ℕ) : ℕ∞) := by
    calc Module.length (PadicInt 2) B.Sel
        ≤ Module.length (PadicInt 2) (LayerQuot 2 level B.M) :=
            Module.length_le_of_injective B.embed B.embed_inj
      _ = ((Module.length (PadicInt 2) (LayerQuot 2 level B.M)).toNat : ℕ∞) :=
            (ENat.natCast_toNat hfinQ).symm
      _ ≤ ((B.model.lam * level + B.model.nu : ℕ) : ℕ∞) := by exact_mod_cast hlenQ
  obtain ⟨hfin, hcard⟩ := padicInt_card_le_of_length_le hle
  refine ⟨hfin, ?_⟩
  rw [← pow_add, add_comm]
  exact hcard

end IwasawaTwoTowerBound

/-- Complete `l = 2` Iwasawa 2-tower realization across all twist weights `1 ≤ k < t` at level
`level`, with total length-sum envelope `B₂_sum`. -/
structure IwasawaTwoTowerRealization (S : SelmerSystem) (E : Type) [Field E] [NumberField E]
    (level t : ℕ) (B₂_sum : ℝ) where
  weightBound : ∀ k : ℕ, 0 < k → k < t → IwasawaTwoTowerBound S E level k
  sum_le :
    ∑ k ∈ (Finset.Ico 1 t).attach,
      ((weightBound k.1 (Finset.mem_Ico.mp k.2).1 (Finset.mem_Ico.mp k.2).2).lenBound : ℝ) ≤ B₂_sum

/-- Extracts BOTH `l = 2` hypotheses (`h2_fin` and `h2_sum` with bound `B₂_sum * Real.log 2`)
needed by `TaylorWilesWindow.vvle_of_three_parts`! -/
theorem IwasawaTwoTowerRealization.to_vvle_two_part {S : SelmerSystem} {E : Type} [Field E]
    [NumberField E] {level t : ℕ} {B₂_sum : ℝ}
    (R : IwasawaTwoTowerRealization S E level t B₂_sum) :
    (∀ (l : Nat.Primes) (k : ℕ), (l : ℕ) = 2 → 0 < k → k < t → S.shaLen E l k ≠ ⊤) ∧
    (∀ P₂ : Finset Nat.Primes, (∀ l ∈ P₂, (l : ℕ) = 2) →
      ∑ l ∈ P₂, Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, ((S.shaLen E l k).toNat : ℝ) ≤
        B₂_sum * Real.log 2) := by
  refine ⟨?_, ?_⟩
  · intro l k hl2 hk1 hk2
    have hl : l = ⟨2, Nat.prime_two⟩ := Subtype.ext hl2
    rw [hl]
    exact (R.weightBound k hk1 hk2).shaLen_finite_and_le.1
  · intro P₂ hP₂
    have hsum2 : ∑ k ∈ Finset.Ico 1 t, ((S.shaLen E ⟨2, Nat.prime_two⟩ k).toNat : ℝ) ≤ B₂_sum := by
      calc ∑ k ∈ Finset.Ico 1 t, ((S.shaLen E ⟨2, Nat.prime_two⟩ k).toNat : ℝ)
          = ∑ k ∈ (Finset.Ico 1 t).attach, ((S.shaLen E ⟨2, Nat.prime_two⟩ k.1).toNat : ℝ) :=
              (Finset.sum_attach (Finset.Ico 1 t) _).symm
        _ ≤ ∑ k ∈ (Finset.Ico 1 t).attach,
              ((R.weightBound k.1 (Finset.mem_Ico.mp k.2).1 (Finset.mem_Ico.mp k.2).2).lenBound : ℝ) := by
              refine Finset.sum_le_sum fun k _ => ?_
              exact_mod_cast (R.weightBound k.1 (Finset.mem_Ico.mp k.2).1
                (Finset.mem_Ico.mp k.2).2).shaLen_finite_and_le.2
        _ ≤ B₂_sum := R.sum_le
    have hnonneg : 0 ≤ ∑ k ∈ Finset.Ico 1 t, ((S.shaLen E ⟨2, Nat.prime_two⟩ k).toNat : ℝ) :=
      Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    calc ∑ l ∈ P₂, Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, ((S.shaLen E l k).toNat : ℝ)
        ≤ (∑ k ∈ Finset.Ico 1 t, ((S.shaLen E ⟨2, Nat.prime_two⟩ k).toNat : ℝ)) * Real.log 2 :=
          sum_prime_two_finset_le hnonneg P₂ hP₂
      _ ≤ B₂_sum * Real.log 2 := mul_le_mul_of_nonneg_right hsum2 (Real.log_natCast_nonneg 2)

/-- **Direct Discharge into `TaylorWilesWindow.vvle_of_three_parts`**:
discharges the `l = 2` branch (`B₂`) cleanly from an `IwasawaTwoTowerRealization` with `μ = 0`! -/
theorem vvle_of_iwasawa_two_tower_and_odd_parts {S : SelmerSystem} {E : Type} [Field E]
    [NumberField E] {level t M : ℕ} {B₂_sum B_ram B_patch : ℝ}
    (h2 : IwasawaTwoTowerRealization S E level t B₂_sum)
    (hram_fin : ∀ (l : Nat.Primes) (k : ℕ), (l : ℕ) ≠ 2 → (l : ℕ) ∣ M → 0 < k → k < t →
      S.shaLen E l k ≠ ⊤)
    (hram_sum : ∀ P : Finset Nat.Primes, (∀ l ∈ P, (l : ℕ) ≠ 2 ∧ (l : ℕ) ∣ M) →
      ∑ l ∈ P, Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, ((S.shaLen E l k).toNat : ℝ) ≤ B_ram)
    (hpat_fin : ∀ (l : Nat.Primes) (k : ℕ), (l : ℕ) ≠ 2 → ¬((l : ℕ) ∣ M) → 0 < k → k < t →
      S.shaLen E l k ≠ ⊤)
    (hpat_sum : ∀ P : Finset Nat.Primes, (∀ l ∈ P, (l : ℕ) ≠ 2 ∧ ¬((l : ℕ) ∣ M)) →
      ∑ l ∈ P, Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, ((S.shaLen E l k).toNat : ℝ) ≤ B_patch) :
    VVle S E t (B₂_sum * Real.log 2 + B_ram + B_patch) :=
  TaylorWilesWindow.vvle_of_three_parts (M := M)
    h2.to_vvle_two_part.1 h2.to_vvle_two_part.2 hram_fin hram_sum hpat_fin hpat_sum

/-- **Direct Discharge into `Stage2GaloisWire.vvle_of_patching_three_parts`**:
combines `IwasawaTwoTowerRealization` (`l = 2`, `μ = 0`), odd ramified (`l ∣ M`), and
`Stage2GaloisWire.PatchedOddUnramifiedRealization` (`l ∤ 2 * M`) into `VVle`! -/
theorem vvle_of_iwasawa_and_patching {S : SelmerSystem} {E : Type} [Field E]
    [NumberField E] {level t M : ℕ} {B₂_sum B_ram B_patch : ℝ}
    (h2 : IwasawaTwoTowerRealization S E level t B₂_sum)
    (hram_fin : ∀ (l : Nat.Primes) (k : ℕ), (l : ℕ) ≠ 2 → (l : ℕ) ∣ M → 0 < k → k < t →
      S.shaLen E l k ≠ ⊤)
    (hram_sum : ∀ P : Finset Nat.Primes, (∀ l ∈ P, (l : ℕ) ≠ 2 ∧ (l : ℕ) ∣ M) →
      ∑ l ∈ P, Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, ((S.shaLen E l k).toNat : ℝ) ≤ B_ram)
    (hpat : Stage2GaloisWire.PatchedOddUnramifiedRealization S E t M B_patch) :
    VVle S E t (B₂_sum * Real.log 2 + B_ram + B_patch) :=
  Stage2GaloisWire.vvle_of_patching_three_parts
    h2.to_vvle_two_part.1 h2.to_vvle_two_part.2 hram_fin hram_sum hpat

/-- **Iwasawa-Discharged Three-Part Patching Window**: replaces the raw `l = 2` finiteness and
`exp(x^(4ε/5)) * log 2` inequalities of `Stage2GaloisWire.ThreePartPatchingWindow` by a concrete
`μ = 0` `IwasawaTwoTowerBound` family whose `(λ, ν)` invariants grow at most like
`A * exp(α * x ^ (eps / 4))`! -/
structure IwasawaDischargedThreePartWindow (S : SelmerSystem) : Prop where
  window : ∃ Cb : ℝ, ∀ (ψ : PChar) (eps : ℝ), 0 < eps → eps < 1 / 52 →
    ∀ (e t : ℝ → ℕ), TaylorWilesWindow.AdmissiblePage 4 401 e t →
    ∃ (J C P XJ A α : ℝ), 0 < J ∧ 0 ≤ A ∧ 0 ≤ α ∧
      ∀ X ≥ XJ, ∀ q d : ℕ, TaylorWilesWindow.PrimePair ψ.N q d →
        2 * X ^ (401 : ℝ) + 1 < (q : ℝ) → 2 * X ^ (401 : ℝ) + 1 < (d : ℝ) →
        P < (q : ℝ) → P < (d : ℝ) → Real.log ((q : ℝ) * d) ≤ X ^ (eps / (4 * J)) →
        ∃ Y : ℝ, X ^ (1 / J) ≤ Y ∧ Y ^ (2 : ℝ) ≤ X ∧
          ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (2 : ℝ) →
            ∀ (E : Type) [Field E] [NumberField E], IsChiField ψ (e x) q d E →
              (∀ k : ℕ, 0 < k → k < t x →
                ∃ B : IwasawaTwoTowerBound S E (e x) k,
                  ((B.model.lam + B.model.nu : ℕ) : ℝ) ≤ A * Real.exp (α * x ^ (eps / 4))) ∧
              (∀ (l : Nat.Primes) (k : ℕ), (l : ℕ) ≠ 2 → (l : ℕ) ∣ ψ.N → 0 < k → k < t x →
                S.shaLen E l k ≠ ⊤) ∧
              (∀ Pram : Finset Nat.Primes, (∀ l ∈ Pram, (l : ℕ) ≠ 2 ∧ (l : ℕ) ∣ ψ.N) →
                ∑ l ∈ Pram, Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 (t x), ((S.shaLen E l k).toNat : ℝ) ≤
                  TaylorWilesWindow.minusBound Cb ψ.N (Module.finrank ℚ E) (condF E) (t x)) ∧
              Nonempty (Stage2GaloisWire.PatchedOddUnramifiedRealization S E (t x) ψ.N
                (((condF E : ℝ) * (t x : ℝ)) ^ C + C * Real.exp (x ^ (4 * eps / 5))))

/-- **Master `l = 2` Branch Discharge Theorem**: proves `Stage2GaloisWire.ThreePartPatchingWindow S`
from `IwasawaDischargedThreePartWindow S` by combining `IwasawaModuleModel.ferrero_washington_card_bound`
with `iwasawa_two_sum_le_exp_of_admissible`! -/
theorem threePartPatchingWindow_of_iwasawa {S : SelmerSystem}
    (H : IwasawaDischargedThreePartWindow S) :
    Stage2GaloisWire.ThreePartPatchingWindow S := by
  classical
  refine ⟨?_⟩
  obtain ⟨Cb, hCb⟩ := H.window
  refine ⟨Cb, fun ψ eps h0 h1 e t hadm => ?_⟩
  obtain ⟨J, C, P, XJ, A, α, hJ0, hA0, _, hmain⟩ := hCb ψ eps h0 h1 e t hadm
  obtain ⟨x0, hx0_ge2, hx0⟩ :=
    iwasawa_two_sum_le_exp_of_admissible eps 4 401 A α h0 (by norm_num) (by norm_num) hA0
  have hx0_nonneg : 0 ≤ x0 := by linarith
  refine ⟨J, C, P, max XJ (x0 ^ J), hJ0, fun X hX q d hpp hq3 hd3 hPq hPd hlog => ?_⟩
  have hXJ : XJ ≤ X := le_trans (le_max_left _ _) hX
  have hx0J : x0 ^ J ≤ X := le_trans (le_max_right _ _) hX
  have hx0_le_XJ : x0 ≤ X ^ (1 / J) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hx0_nonneg _) hx0J
      (le_of_lt (one_div_pos.mpr hJ0))
    rwa [← Real.rpow_mul hx0_nonneg, mul_one_div_cancel hJ0.ne', Real.rpow_one] at h
  obtain ⟨Y, hYlo, hYhi, hY⟩ := hmain X hXJ q d hpp hq3 hd3 hPq hPd hlog
  refine ⟨Y, hYlo, hYhi, fun x hxY hxY2 E _ _ hE => ?_⟩
  obtain ⟨h2iwasawa, hrf, hrs, hpat⟩ := hY x hxY hxY2 E hE
  have hx_ge_x0 : x0 ≤ x := (hx0_le_XJ.trans hYlo).trans hxY
  -- Choose a concrete `IwasawaTwoTowerBound` for each `1 ≤ k < t x`.
  let getB : ∀ k : ℕ, 0 < k → k < t x → IwasawaTwoTowerBound S E (e x) k :=
    fun k hk1 hk2 => (h2iwasawa k hk1 hk2).choose
  let lamFn : ℕ → ℕ := fun k =>
    if h : 0 < k ∧ k < t x then (getB k h.1 h.2).model.lam else 0
  let nuFn : ℕ → ℕ := fun k =>
    if h : 0 < k ∧ k < t x then (getB k h.1 h.2).model.nu else 0
  have hinv : ∀ k ∈ Finset.Ico 1 (t x),
      ((lamFn k + nuFn k : ℕ) : ℝ) ≤ A * Real.exp (α * x ^ (eps / 4)) := by
    intro k hk
    have hk' : 0 < k ∧ k < t x := by
      simp only [Finset.mem_Ico] at hk
      omega
    simp only [lamFn, nuFn, dif_pos hk']
    exact (h2iwasawa k hk'.1 hk'.2).choose_spec
  have hsum_exp : ∑ k ∈ Finset.Ico 1 (t x), ((lamFn k * e x + nuFn k : ℕ) : ℝ) ≤
      Real.exp (x ^ (4 * eps / 5)) :=
    hx0 e t hadm x hx_ge_x0 lamFn nuFn hinv
  let R : IwasawaTwoTowerRealization S E (e x) (t x) (Real.exp (x ^ (4 * eps / 5))) :=
    { weightBound := getB
      sum_le := by
        calc ∑ k ∈ (Finset.Ico 1 (t x)).attach,
              ((getB k.1 (Finset.mem_Ico.mp k.2).1 (Finset.mem_Ico.mp k.2).2).lenBound : ℝ)
            = ∑ k ∈ Finset.Ico 1 (t x), ((lamFn k * e x + nuFn k : ℕ) : ℝ) := by
                rw [← Finset.sum_attach (Finset.Ico 1 (t x))]
                refine Finset.sum_congr rfl fun k _ => ?_
                have hk' : 0 < k.1 ∧ k.1 < t x := by
                  have := Finset.mem_Ico.mp k.2
                  omega
                simp only [lamFn, nuFn, dif_pos hk', IwasawaTwoTowerBound.lenBound]
          _ ≤ Real.exp (x ^ (4 * eps / 5)) := hsum_exp }
  exact ⟨R.to_vvle_two_part.1, R.to_vvle_two_part.2, hrf, hrs, hpat⟩

/-- **End-to-End Pillar 3 Export**: discharges `RHDirect.GaloisModularityContract S` (`VWin S`)
directly from `IwasawaDischargedThreePartWindow S`! -/
theorem galoisModularityContract_of_iwasawa {S : SelmerSystem}
    (H : IwasawaDischargedThreePartWindow S) :
    GaloisModularityContract S :=
  Stage2GaloisWire.galoisModularityContract_of_threePart (threePartPatchingWindow_of_iwasawa H)

end ThreePartDischarge

end RHDirect.Stage2IwasawaTwoTower

end
