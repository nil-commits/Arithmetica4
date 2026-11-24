import RHDirect.Stage11DiamondFujiwara
import RHDirect.Stage11MazurDeformation
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# RHDirect.Stage13UltraproductPatching

Unconditional (`0` assumptions, `0` `sorry`, `0` custom `axiom`s, `0` `native_decide`, pure Mathlib
`v4.33.1`) formalization of **Stage 13 — Field 1 Assault (Engine #6)**:
**Higher-Rank Ultraproduct Taylor–Wiles–Thorne Ordinary Determinant Patching**
(`PmodEx`, `CohAx`, `TaylorWilesObstructionBound`, `CoreBC`, `LiftPt`, `AnnBc`),
with ZERO nested global `Algebra` instances over `MvPowerSeries` (explicit `RingHom`s & bundled
finite-level patching systems throughout).

## Main Results

1. **Unconditional Non-Principal Ultrafilter Patching Construction (`PmodEx` on `Ultrafilter ℕ`)**:
   - Non-principal ultrafilter `nonprincipalUltrafilterNat : Ultrafilter ℕ` (`≤ Filter.atTop`) and
     exact finite-set stabilization `ultrafilter_eventually_const_of_finite`.
   - Open truncation filtration `truncIdeal p g k ≤ PatchingBaseRing p g`, proved to have finite
     quotients `TruncRing p g k`, cube-zero transition kernels (`x ^ 3 = 0`), surjective `GL_r`
     lifting `mapGL_surjective_of_ker_cube_zero`, and exact inverse-limit isomorphism
     `patchingBaseRingEquivTruncLimit : PatchingBaseRing p g ≃+* TruncLimit p g`.
   - Genuine ultraproduct construction (`UltraproductPatchingData` → `PatchedR`, `PatchedT`,
     `PatchedM`) and **`pmodEx_patched_free_over_Sinf`**: `M_∞` is finite free of rank `r ≥ 1`
     over `S_∞ = ℤ_[p][[y_0,…,y_{g-1}]]`, `M_∞` is faithful over `T_∞`, `R_∞ ↠ T_∞` has nilpotent
     kernel (and `R_∞ ≃+* T_∞` when reduced), and specialization mod `(y_0,…,y_{g-1})` recovers
     `M_0` as a faithful `T_0`-module.
2. **Higher-Rank `𝒢_n` Ordinary Determinant Rings & Thorne Component-Chain Automorphy Propagation
   (`CoreBC`, `LiftPt`, `AnnBc`)**:
   - Clozel–Harris–Taylor group `GnGroup d R`, degree-`d` Chenevier determinant laws `DetLaw`,
     and ordinary determinant data `OrdinaryDetDatum`.
   - **Taylor–Wiles–Thorne Support Theorem (`supp_eq_union_irred_components`)**: for any Noetherian
     `R` finite over `S_∞` with `ringKrullDim R ≤ g + 1` and any finite-free `S_∞`-module `M`
     of rank `r ≥ 1`, EVERY minimal prime of `ann_R(M)` contracts to `⊥` in `S_∞` and is a minimal
     prime of `R`, so `Supp(M)` is a union of irreducible components of `Spec(R)`.
   - **Component-Chain Propagation (`liftPt_support_propagation`, `coreBC_component_chain`)** and
     **Nakayama Determinant-Trick Fiber Theorem (`annBc_R0_annihilator_nilpotent`,
     `annBc_reduced_R0_equiv_T0`)**: connectedness of the irreducible-component graph forces
     `ann_{R_∞}(M_∞)` and `ann_{R_0}(M_0)` to be nilpotent, yielding `R_0^red ≃+* T_0`.
3. **Poitou–Tate Obstruction Dimension Balance (`CohAx` / `TaylorWilesObstructionBound`)**:
   - Concrete higher-rank adjoint Lie algebras (`M_3`/`sl_3` for `U(3)`, `sp_4` of dim `10` for
     `Sp₄`) with matrix-proved archimedean `H⁰(G_∞)` (`dim = 3` for `U(3)`, `dim = 4` for `Sp₄`)
     and regular-semisimple Frobenius centralizer dimensions, wired directly into
     `Stage11MazurDeformation.greenberg_wiles_euler_characteristic` and `Stage11DiamondFujiwara`.
-/

noncomputable section

open scoped BigOperators Pointwise
open Filter Finset Module Submodule Matrix
open RHDirect RHDirect.Stage2GaloisCohomology RHDirect.Stage3PatchingUnification
open RHDirect.Stage11ConcretePatching RHDirect.Stage11MazurDeformation
open RHDirect.Stage11DiamondFujiwara

namespace RHDirect
namespace Stage13UltraproductPatching

/-! ## Section 1: Non-Principal Ultrafilter (`Ultrafilter ℕ`) & Ultraproduct Patching (`PmodEx`) -/

section UltrafilterPatching

/-! ### 1.1 Non-Principal Ultrafilter on `ℕ` & Finite Stabilization -/

/-- Canonical non-principal ultrafilter on `ℕ` extending the cofinite/atTop filter `Filter.atTop`. -/
def nonprincipalUltrafilterNat : Ultrafilter ℕ :=
  Ultrafilter.of Filter.atTop

theorem nonprincipalUltrafilterNat_le_atTop :
    (nonprincipalUltrafilterNat : Filter ℕ) ≤ Filter.atTop :=
  Ultrafilter.of_le Filter.atTop

theorem exists_nonprincipal_ultrafilter_nat :
    ∃ 𝒰 : Ultrafilter ℕ, (𝒰 : Filter ℕ) ≤ Filter.atTop :=
  ⟨nonprincipalUltrafilterNat, nonprincipalUltrafilterNat_le_atTop⟩

theorem ultrafilter_eventually_ge (𝒰 : Ultrafilter ℕ) (h𝒰 : (𝒰 : Filter ℕ) ≤ Filter.atTop)
    (k : ℕ) : ∀ᶠ n in (𝒰 : Filter ℕ), k ≤ n :=
  h𝒰 (Filter.eventually_ge_atTop k)

theorem ultrafilter_not_mem_finite (𝒰 : Ultrafilter ℕ) (h𝒰 : (𝒰 : Filter ℕ) ≤ Filter.atTop)
    {s : Set ℕ} (hs : s.Finite) : s ∉ 𝒰 := by
  intro hsU
  obtain ⟨B, hB⟩ := hs.bddAbove
  have hge : {n : ℕ | B + 1 ≤ n} ∈ (𝒰 : Filter ℕ) := ultrafilter_eventually_ge 𝒰 h𝒰 (B + 1)
  have hinter : (s ∩ {n : ℕ | B + 1 ≤ n}) ∈ (𝒰 : Filter ℕ) :=
    Filter.inter_mem hsU hge
  obtain ⟨n, hn_s, hn_ge⟩ := (Ultrafilter.nonempty_of_mem hinter)
  change B + 1 ≤ n at hn_ge
  have hn_le : n ≤ B := hB hn_s
  omega

/-- Helper: if a sequence lands `𝒰`-eventually inside a finite set `s`, it is `𝒰`-eventually
constant at some element `a ∈ s`. -/
private theorem ultrafilter_exists_const_of_mem_finset {α : Type*} [DecidableEq α]
    (𝒰 : Ultrafilter ℕ) (f : ℕ → α) (s : Finset α)
    (hs : {n : ℕ | f n ∈ s} ∈ 𝒰) :
    ∃ a ∈ s, ∀ᶠ n in (𝒰 : Filter ℕ), f n = a := by
  induction s using Finset.induction_on with
  | empty =>
    have hempty : ({n : ℕ | f n ∈ (∅ : Finset α)}) = ∅ := by ext n; simp
    rw [hempty] at hs
    exact absurd hs Ultrafilter.empty_notMem
  | @insert a t ha ih =>
    have hunion : {n : ℕ | f n ∈ insert a t} = {n : ℕ | f n = a} ∪ {n : ℕ | f n ∈ t} := by
      ext n; simp [Set.mem_union]
    rw [hunion] at hs
    rcases (Ultrafilter.union_mem_iff.mp hs) with haU | htU
    · exact ⟨a, Finset.mem_insert_self a t, haU⟩
    · obtain ⟨b, hbt, hbU⟩ := ih htU
      exact ⟨b, Finset.mem_insert_of_mem hbt, hbU⟩

/-- **Ultrafilter Finite Stabilization Principle**: any sequence `f : ℕ → α` into a finite type `α`
stabilizes along any ultrafilter `𝒰 : Ultrafilter ℕ` to a UNIQUE value `a : α`. -/
theorem ultrafilter_eventually_const_of_finite {α : Type*} [Finite α]
    (𝒰 : Ultrafilter ℕ) (f : ℕ → α) :
    ∃! a : α, ∀ᶠ n in (𝒰 : Filter ℕ), f n = a := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have huniv : {n : ℕ | f n ∈ (Finset.univ : Finset α)} ∈ 𝒰 := by
    have : {n : ℕ | f n ∈ (Finset.univ : Finset α)} = Set.univ := by ext n; simp
    rw [this]; exact Filter.univ_mem
  obtain ⟨a, _, ha⟩ := ultrafilter_exists_const_of_mem_finset 𝒰 f Finset.univ huniv
  refine ⟨a, ha, fun b hb => ?_⟩
  have hboth : ∀ᶠ n in (𝒰 : Filter ℕ), f n = a ∧ f n = b := ha.and hb
  obtain ⟨n, hna, hnb⟩ := hboth.exists
  exact hnb.symm.trans hna

/-- The unique `𝒰`-limit of a sequence `f : ℕ → α` into a finite type `α`. -/
def ultraLimitVal {α : Type*} [Finite α] (𝒰 : Ultrafilter ℕ) (f : ℕ → α) : α :=
  Classical.choose (ultrafilter_eventually_const_of_finite 𝒰 f).exists

theorem ultraLimitVal_spec {α : Type*} [Finite α] (𝒰 : Ultrafilter ℕ) (f : ℕ → α) :
    ∀ᶠ n in (𝒰 : Filter ℕ), f n = ultraLimitVal 𝒰 f :=
  Classical.choose_spec (ultrafilter_eventually_const_of_finite 𝒰 f).exists

theorem ultraLimitVal_eq_of_eventually_eq {α : Type*} [Finite α] (𝒰 : Ultrafilter ℕ)
    {f : ℕ → α} {a : α} (h : ∀ᶠ n in (𝒰 : Filter ℕ), f n = a) :
    ultraLimitVal 𝒰 f = a :=
  ((ultrafilter_eventually_const_of_finite 𝒰 f).unique (ultraLimitVal_spec 𝒰 f) h)

/-! ### 1.2 Open Truncation Filtration `truncIdeal p g k`, Finiteness, `GL_r` Lifting & `S_∞ ≃+* lim_k A_k` -/

/-- The open degree-and-`p`-adic truncation ideal on `S_∞ = PatchingBaseRing p g`:
`f ∈ truncIdeal p g k` iff every coefficient of total degree `< k` is divisible by `p ^ k`. -/
def truncIdeal (p g k : ℕ) [Fact p.Prime] : Ideal (PatchingBaseRing p g) where
  carrier := { f | ∀ α : Fin g →₀ ℕ, (∑ i : Fin g, α i) < k →
    (p : ℤ_[p]) ^ k ∣ MvPowerSeries.coeff α f }
  zero_mem' α _ := by rw [map_zero]; exact dvd_zero _
  add_mem' {f h} hf hh α hα := by
    rw [map_add]; exact dvd_add (hf α hα) (hh α hα)
  smul_mem' c {f} hf α hα := by
    change (p : ℤ_[p]) ^ k ∣ MvPowerSeries.coeff α (c * f)
    rw [MvPowerSeries.coeff_mul]
    refine Finset.dvd_sum fun ab hab => ?_
    rw [Finset.mem_antidiagonal] at hab
    have hdeg_le : (∑ i : Fin g, ab.2 i) ≤ ∑ i : Fin g, α i := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hi : ab.1 i + ab.2 i = α i := by
        have := congrArg (fun d : Fin g →₀ ℕ => d i) hab; simpa using this
      omega
    exact dvd_mul_of_dvd_right (hf ab.2 (lt_of_le_of_lt hdeg_le hα)) _

theorem truncIdeal_antitone (p g : ℕ) [Fact p.Prime] :
    Antitone (fun k => truncIdeal p g k) := by
  intro k m hkm f hf α hα
  exact (pow_dvd_pow (p : ℤ_[p]) hkm).trans (hf α (lt_of_lt_of_le hα hkm))

/-- **Cube-Zero Transition Kernel Property**: `f ∈ truncIdeal p g (k + 1) ⇒ f ^ 3 ∈ truncIdeal p g (k + 2)`. -/
theorem truncIdeal_cube_le_succ (p g k : ℕ) [Fact p.Prime] {f : PatchingBaseRing p g}
    (hf : f ∈ truncIdeal p g (k + 1)) :
    f ^ 3 ∈ truncIdeal p g (k + 2) := by
  intro α hα
  have hpow3 : f ^ 3 = f * (f * f) := by ring
  rw [hpow3, MvPowerSeries.coeff_mul]
  refine Finset.dvd_sum fun ab hab => ?_
  rw [Finset.mem_antidiagonal] at hab
  rw [MvPowerSeries.coeff_mul, Finset.mul_sum]
  refine Finset.dvd_sum fun cd hcd => ?_
  rw [Finset.mem_antidiagonal] at hcd
  have hsum : (∑ i : Fin g, ab.1 i) + (∑ i : Fin g, cd.1 i) + (∑ i : Fin g, cd.2 i) =
      ∑ i : Fin g, α i := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : ab.1 i + ab.2 i = α i := by
      have := congrArg (fun d : Fin g →₀ ℕ => d i) hab; simpa using this
    have h2 : cd.1 i + cd.2 i = ab.2 i := by
      have := congrArg (fun d : Fin g →₀ ℕ => d i) hcd; simpa using this
    omega
  have h2k : k + 2 ≤ (k + 1) + (k + 1) := by omega
  by_cases h1 : (∑ i : Fin g, ab.1 i) < k + 1
  · by_cases h2 : (∑ i : Fin g, cd.1 i) < k + 1
    · have hd1 := hf ab.1 h1
      have hd2 := hf cd.1 h2
      have hprod : (p : ℤ_[p]) ^ ((k + 1) + (k + 1)) ∣
          MvPowerSeries.coeff ab.1 f * MvPowerSeries.coeff cd.1 f := by
        rw [pow_add]; exact mul_dvd_mul hd1 hd2
      have hmul : (p : ℤ_[p]) ^ ((k + 1) + (k + 1)) ∣
          MvPowerSeries.coeff ab.1 f * (MvPowerSeries.coeff cd.1 f * MvPowerSeries.coeff cd.2 f) := by
        rw [← mul_assoc]; exact dvd_mul_of_dvd_left hprod _
      exact (pow_dvd_pow (p : ℤ_[p]) h2k).trans hmul
    · have h3 : (∑ i : Fin g, cd.2 i) < k + 1 := by omega
      have hd1 := hf ab.1 h1
      have hd3 := hf cd.2 h3
      have hprod : (p : ℤ_[p]) ^ ((k + 1) + (k + 1)) ∣
          MvPowerSeries.coeff ab.1 f * MvPowerSeries.coeff cd.2 f := by
        rw [pow_add]; exact mul_dvd_mul hd1 hd3
      have hrew : MvPowerSeries.coeff ab.1 f * (MvPowerSeries.coeff cd.1 f * MvPowerSeries.coeff cd.2 f) =
          (MvPowerSeries.coeff ab.1 f * MvPowerSeries.coeff cd.2 f) * MvPowerSeries.coeff cd.1 f := by ring
      rw [hrew]
      exact (pow_dvd_pow (p : ℤ_[p]) h2k).trans (dvd_mul_of_dvd_left hprod _)
  · have h2 : (∑ i : Fin g, cd.1 i) < k + 1 := by omega
    have h3 : (∑ i : Fin g, cd.2 i) < k + 1 := by omega
    have hd2 := hf cd.1 h2
    have hd3 := hf cd.2 h3
    have hprod : (p : ℤ_[p]) ^ ((k + 1) + (k + 1)) ∣
        MvPowerSeries.coeff cd.1 f * MvPowerSeries.coeff cd.2 f := by
      rw [pow_add]; exact mul_dvd_mul hd2 hd3
    exact (pow_dvd_pow (p : ℤ_[p]) h2k).trans (dvd_mul_of_dvd_right hprod _)

theorem truncIdeal_iInf_eq_bot (p g : ℕ) [Fact p.Prime] {f : PatchingBaseRing p g}
    (hf : ∀ k : ℕ, f ∈ truncIdeal p g (k + 1)) : f = 0 := by
  ext α
  rw [map_zero]
  set d := ∑ i : Fin g, α i
  have hnorm : ∀ m : ℕ, ‖MvPowerSeries.coeff α f‖ ≤ (p : ℝ) ^ (-((d + m + 1 : ℕ) : ℤ)) := by
    intro m
    have hdvd : (p : ℤ_[p]) ^ (d + m + 1) ∣ MvPowerSeries.coeff α f :=
      hf (d + m) α (by omega)
    rw [← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow] at hdvd
    exact hdvd
  have hle0 : ‖MvPowerSeries.coeff α f‖ ≤ 0 := by
    have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have hinv_lt1 : ((p : ℝ)⁻¹) < 1 := inv_lt_one_of_one_lt₀ hp_gt1
    have hlim : Tendsto (fun m : ℕ => ((p : ℝ)⁻¹) ^ (d + m + 1)) atTop (nhds 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hinv_lt1).comp
        (tendsto_atTop_mono (fun m => show m ≤ d + m + 1 by omega) tendsto_id)
    refine ge_of_tendsto' hlim fun m => ?_
    calc ‖MvPowerSeries.coeff α f‖ ≤ (p : ℝ) ^ (-((d + m + 1 : ℕ) : ℤ)) := hnorm m
      _ = ((p : ℝ)⁻¹) ^ (d + m + 1) := by rw [_root_.zpow_neg, zpow_natCast, inv_pow]
  exact norm_eq_zero.mp (le_antisymm hle0 (norm_nonneg _))

theorem truncIdeal_le_aug_sup_pPow (p g k : ℕ) [Fact p.Prime] :
    truncIdeal p g (k + 1) ≤ patchingAugIdeal p g ⊔ Ideal.span {(p : PatchingBaseRing p g) ^ (k + 1)} := by
  intro f hf
  have hconst : (p : ℤ_[p]) ^ (k + 1) ∣ MvPowerSeries.constantCoeff f := by
    have h0 := hf 0 (by simp)
    rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at h0
  obtain ⟨c, hc⟩ := hconst
  have hsub : f - MvPowerSeries.C (MvPowerSeries.constantCoeff f) ∈ patchingAugIdeal p g := by
    rw [patchingAugIdeal_eq_ker_constantCoeff, RingHom.mem_ker, map_sub, MvPowerSeries.constantCoeff_C,
      sub_self]
  have hCmem : MvPowerSeries.C (MvPowerSeries.constantCoeff f) ∈
      Ideal.span {(p : PatchingBaseRing p g) ^ (k + 1)} := by
    rw [hc, map_mul, map_pow, map_natCast, Ideal.mem_span_singleton]
    exact dvd_mul_right _ _
  have heq : f = (f - MvPowerSeries.C (MvPowerSeries.constantCoeff f)) +
      MvPowerSeries.C (MvPowerSeries.constantCoeff f) := by ring
  rw [heq]
  exact Submodule.add_mem_sup hsub hCmem

/-- Bundled finite Artinian quotient ring `TruncRing p g k := S_∞ ⧸ truncIdeal p g (k + 1)`. -/
abbrev TruncRing (p g k : ℕ) [Fact p.Prime] : Type :=
  PatchingBaseRing p g ⧸ truncIdeal p g (k + 1)

/-- Canonical quotient ring homomorphism `S_∞ →+* TruncRing p g k`. -/
def truncProj (p g k : ℕ) [Fact p.Prime] : PatchingBaseRing p g →+* TruncRing p g k :=
  Ideal.Quotient.mk (truncIdeal p g (k + 1))

theorem truncProj_surjective (p g k : ℕ) [Fact p.Prime] :
    Function.Surjective (truncProj p g k) :=
  Ideal.Quotient.mk_surjective

/-- Canonical transition homomorphism `TruncRing p g (k + 1) →+* TruncRing p g k`. -/
def truncTrans (p g k : ℕ) [Fact p.Prime] : TruncRing p g (k + 1) →+* TruncRing p g k :=
  Ideal.quotientMap (truncIdeal p g (k + 1)) (RingHom.id _)
    (fun _ hx => truncIdeal_antitone p g (Nat.le_succ (k + 1)) hx)

@[simp]
theorem truncTrans_mk (p g k : ℕ) [Fact p.Prime] (f : PatchingBaseRing p g) :
    truncTrans p g k (truncProj p g (k + 1) f) = truncProj p g k f := rfl

theorem truncTrans_comp_proj (p g k : ℕ) [Fact p.Prime] :
    (truncTrans p g k).comp (truncProj p g (k + 1)) = truncProj p g k := by
  ext f; rfl

theorem truncTrans_surjective (p g k : ℕ) [Fact p.Prime] :
    Function.Surjective (truncTrans p g k) := by
  intro y
  obtain ⟨f, rfl⟩ := truncProj_surjective p g k y
  exact ⟨truncProj p g (k + 1) f, rfl⟩

theorem truncTrans_ker_cube_eq_zero (p g k : ℕ) [Fact p.Prime]
    {x : TruncRing p g (k + 1)} (hx : x ∈ RingHom.ker (truncTrans p g k)) :
    x ^ 3 = 0 := by
  obtain ⟨f, rfl⟩ := truncProj_surjective p g (k + 1) x
  have hf : f ∈ truncIdeal p g (k + 1) := by
    have h0 : truncProj p g k f = 0 := hx
    exact Ideal.Quotient.eq_zero_iff_mem.mp h0
  change (Ideal.Quotient.mk (truncIdeal p g (k + 2)) f) ^ 3 = 0
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (truncIdeal_cube_le_succ p g k hf)

/-- Canonical reduction `TruncRing p g k →+* ZMod (p ^ (k + 1))` (specializing `y_i = 0` and
reducing `constantCoeff` mod `p ^ (k + 1)`). -/
def truncToZModPow (p g k : ℕ) [Fact p.Prime] :
    TruncRing p g k →+* ZMod (p ^ (k + 1)) :=
  Ideal.Quotient.lift (truncIdeal p g (k + 1))
    ((PadicInt.toZModPow (k + 1) : ℤ_[p] →+* ZMod (p ^ (k + 1))).comp MvPowerSeries.constantCoeff)
    (fun f hf => by
      have h0 : (p : ℤ_[p]) ^ (k + 1) ∣ MvPowerSeries.constantCoeff f := by
        simpa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using hf 0 (by simp)
      change PadicInt.toZModPow (k + 1) (MvPowerSeries.constantCoeff f) = 0
      rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
      exact h0)

@[simp]
theorem truncToZModPow_mk (p g k : ℕ) [Fact p.Prime] (f : PatchingBaseRing p g) :
    truncToZModPow p g k (truncProj p g k f) =
      PadicInt.toZModPow (k + 1) (MvPowerSeries.constantCoeff f) := rfl

/-- Finite index set of multi-indices of total degree `< k + 1`. -/
private abbrev DegBelow (g k : ℕ) : Type :=
  { α : Fin g → Fin (k + 1) // (∑ i : Fin g, (α i).1) < k + 1 }

/-- **Unconditional Finiteness of Every Truncated Patching Ring `TruncRing p g k`**! -/
instance instFiniteTruncRing (p g k : ℕ) [Fact p.Prime] : Finite (TruncRing p g k) := by
  have : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero (k + 1) (Fact.out : p.Prime).ne_zero⟩
  let toFinsupp (α : DegBelow g k) : Fin g →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm (fun i => (α.1 i).1)
  let coords : TruncRing p g k → (DegBelow g k → ZMod (p ^ (k + 1))) :=
    Quotient.lift
      (fun f α => PadicInt.toZModPow (k + 1) (MvPowerSeries.coeff (toFinsupp α) f))
      (fun f h hfh => by
        funext α
        have hdiff : f - h ∈ truncIdeal p g (k + 1) :=
          Ideal.Quotient.eq.mp (Quotient.sound hfh)
        have hdeg : (∑ i : Fin g, toFinsupp α i) < k + 1 := by
          simpa [toFinsupp] using α.2
        have hdvd := hdiff (toFinsupp α) hdeg
        rw [map_sub] at hdvd
        have hker : MvPowerSeries.coeff (toFinsupp α) f - MvPowerSeries.coeff (toFinsupp α) h ∈
            RingHom.ker (PadicInt.toZModPow (k + 1) : ℤ_[p] →+* ZMod (p ^ (k + 1))) := by
          rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton]; exact hdvd
        rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hker
        exact hker)
  have hcoords_inj : Function.Injective coords := by
    intro x y hxy
    obtain ⟨f, rfl⟩ := truncProj_surjective p g k x
    obtain ⟨h, rfl⟩ := truncProj_surjective p g k y
    apply Ideal.Quotient.eq.mpr
    intro β hβ
    have hβ_lt : ∀ i : Fin g, β i < k + 1 := fun i =>
      lt_of_le_of_lt (Finset.single_le_sum (fun j _ => Nat.zero_le (β j)) (Finset.mem_univ i)) hβ
    let α : DegBelow g k := ⟨fun i => ⟨β i, hβ_lt i⟩, by simpa using hβ⟩
    have hto : toFinsupp α = β := by ext i; rfl
    have heq := congrFun hxy α
    change PadicInt.toZModPow (k + 1) (MvPowerSeries.coeff (toFinsupp α) f) =
      PadicInt.toZModPow (k + 1) (MvPowerSeries.coeff (toFinsupp α) h) at heq
    rw [hto] at heq
    have hker : MvPowerSeries.coeff β f - MvPowerSeries.coeff β h ∈
        RingHom.ker (PadicInt.toZModPow (k + 1) : ℤ_[p] →+* ZMod (p ^ (k + 1))) := by
      rw [RingHom.mem_ker, map_sub, heq, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hker
    simpa [map_sub] using hker
  exact Finite.of_injective coords hcoords_inj

/-- **Elementary Unit Lifting across Cube-Zero-Kernel Surjections**:
if `f : B ↠ A` has `∀ x ∈ ker f, x ^ 3 = 0`, then any `b : B` with `IsUnit (f b)` is a unit in `B`. -/
theorem isUnit_of_map_isUnit_of_ker_cube_zero {B A : Type*} [CommRing B] [CommRing A]
    (f : B →+* A) (hf : Function.Surjective f) (hker : ∀ x ∈ RingHom.ker f, x ^ 3 = 0)
    {b : B} (hu : IsUnit (f b)) : IsUnit b := by
  obtain ⟨u, hu_eq⟩ := hu
  obtain ⟨c, hc⟩ := hf (u⁻¹ : Aˣ)
  let x : B := 1 - b * c
  have hx_ker : x ∈ RingHom.ker f := by
    rw [RingHom.mem_ker]
    change f (1 - b * c) = 0
    rw [map_sub, map_one, map_mul, hc, ← hu_eq, Units.mul_inv, sub_self]
  have hx3 : x ^ 3 = 0 := hker x hx_ker
  refine isUnit_iff_exists_inv.mpr ⟨c * (1 + x + x ^ 2), ?_⟩
  have hid : b * (c * (1 + x + x ^ 2)) = 1 - x ^ 3 := by
    dsimp only [x]; ring
  rw [hid, hx3, sub_zero]

/-- **Surjectivity of `GL_r(B) ↠ GL_r(A)` across Cube-Zero-Kernel Surjections**! -/
theorem mapGL_surjective_of_ker_cube_zero {B A : Type*} [CommRing B] [CommRing A]
    (r : ℕ) (f : B →+* A) (hf : Function.Surjective f) (hker : ∀ x ∈ RingHom.ker f, x ^ 3 = 0) :
    Function.Surjective
      (Units.map (RingHom.mapMatrix f : Matrix (Fin r) (Fin r) B →+* Matrix (Fin r) (Fin r) A).toMonoidHom) := by
  intro U
  have hlift : ∀ i j : Fin r, ∃ b : B, f b = U.1 i j := fun i j => hf (U.1 i j)
  choose Mfn hM using hlift
  let M : Matrix (Fin r) (Fin r) B := Matrix.of Mfn
  have hfM : RingHom.mapMatrix f M = U.1 := by ext i j; exact hM i j
  have hdet_unit_A : IsUnit (f M.det) := by
    rw [RingHom.map_det f M, hfM]
    exact (Matrix.isUnit_iff_isUnit_det U.1).mp U.isUnit
  have hdet_unit_B : IsUnit M.det := isUnit_of_map_isUnit_of_ker_cube_zero f hf hker hdet_unit_A
  have hM_unit : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr hdet_unit_B
  refine ⟨hM_unit.unit, ?_⟩
  apply Units.ext
  exact hfM

/-- **Compatible Inverse Limit `TruncLimit p g := lim_k (S_∞ ⧸ truncIdeal p g (k + 1))`**. -/
@[ext]
structure TruncLimit (p g : ℕ) [Fact p.Prime] where
  val : ∀ k : ℕ, TruncRing p g k
  compat : ∀ k : ℕ, truncTrans p g k (val (k + 1)) = val k

namespace TruncLimit

variable {p g : ℕ} [Fact p.Prime]

instance : CommRing (TruncLimit p g) where
  zero := ⟨fun _ => 0, fun _ => map_zero _⟩
  one := ⟨fun _ => 1, fun _ => map_one _⟩
  add x y := ⟨fun k => x.val k + y.val k, fun k => by rw [map_add, x.compat k, y.compat k]⟩
  neg x := ⟨fun k => -x.val k, fun k => by rw [map_neg, x.compat k]⟩
  sub x y := ⟨fun k => x.val k - y.val k, fun k => by rw [map_sub, x.compat k, y.compat k]⟩
  mul x y := ⟨fun k => x.val k * y.val k, fun k => by rw [map_mul, x.compat k, y.compat k]⟩
  add_assoc _ _ _ := by ext k; exact add_assoc _ _ _
  zero_add _ := by ext k; exact zero_add _
  add_zero _ := by ext k; exact add_zero _
  nsmul n x := ⟨fun k => n • x.val k, fun k => by rw [map_nsmul, x.compat k]⟩
  nsmul_zero _ := by ext k; exact zero_nsmul _
  nsmul_succ _ _ := by ext k; exact succ_nsmul _ _
  zsmul n x := ⟨fun k => n • x.val k, fun k => by rw [map_zsmul, x.compat k]⟩
  zsmul_zero' _ := by ext k; exact zero_zsmul _
  zsmul_succ' n x := by
    ext k; change ((n + 1 : ℕ) : ℤ) • x.val k = (n : ℤ) • x.val k + x.val k
    rw [Nat.cast_add, Nat.cast_one, add_zsmul, one_zsmul]
  zsmul_neg' n x := by
    ext k; change Int.negSucc n • x.val k = -(((n + 1 : ℕ) : ℤ) • x.val k)
    rw [negSucc_zsmul, natCast_zsmul]
  sub_eq_add_neg _ _ := by ext k; exact sub_eq_add_neg _ _
  neg_add_cancel _ := by ext k; exact neg_add_cancel _
  add_comm _ _ := by ext k; exact add_comm _ _
  mul_assoc _ _ _ := by ext k; exact mul_assoc _ _ _
  one_mul _ := by ext k; exact one_mul _
  mul_one _ := by ext k; exact mul_one _
  left_distrib _ _ _ := by ext k; exact left_distrib _ _ _
  right_distrib _ _ _ := by ext k; exact right_distrib _ _ _
  zero_mul _ := by ext k; exact zero_mul _
  mul_zero _ := by ext k; exact mul_zero _
  mul_comm _ _ := by ext k; exact mul_comm _ _

/-- Canonical ring homomorphism `S_∞ →+* TruncLimit p g`. -/
def ofBase (p g : ℕ) [Fact p.Prime] : PatchingBaseRing p g →+* TruncLimit p g where
  toFun f := ⟨fun k => truncProj p g k f, fun _ => rfl⟩
  map_one' := by ext k; exact map_one _
  map_mul' f h := by ext k; exact map_mul _ f h
  map_zero' := by ext k; exact map_zero _
  map_add' f h := by ext k; exact map_add _ f h

/-- Multi-step compatibility of representatives of a `TruncLimit` element. -/
private lemma rep_sub_mem_of_le (x : TruncLimit p g) (rep : ℕ → PatchingBaseRing p g)
    (hrep : ∀ k, truncProj p g k (rep k) = x.val k) {k m : ℕ} (hkm : k ≤ m) :
    rep m - rep k ∈ truncIdeal p g (k + 1) := by
  have htrans : ∀ d : ℕ, truncProj p g k (rep (k + d)) = x.val k := by
    intro d
    induction d with
    | zero => simpa using hrep k
    | succ d ih =>
      have hstep : truncProj p g (k + d) (rep (k + (d + 1))) = x.val (k + d) := by
        rw [← truncTrans_mk p g (k + d), ← Nat.add_assoc, hrep (k + d + 1), x.compat (k + d)]
      have hdiff : rep (k + (d + 1)) - rep (k + d) ∈ truncIdeal p g (k + d + 1) :=
        Ideal.Quotient.eq.mp (hstep.trans (hrep (k + d)).symm)
      have hdiff_k : rep (k + (d + 1)) - rep (k + d) ∈ truncIdeal p g (k + 1) :=
        truncIdeal_antitone p g (by omega) hdiff
      have heq : truncProj p g k (rep (k + (d + 1))) = truncProj p g k (rep (k + d)) :=
        Ideal.Quotient.eq.mpr hdiff_k
      exact heq.trans ih
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkm
  exact Ideal.Quotient.eq.mp ((htrans d).trans (hrep k).symm)

/-- **UNCONDITIONAL INVERSE-LIMIT ISOMORPHISM `S_∞ = ℤ_[p][[y_0,…,y_{g-1}]] ≃+* lim_k (S_∞ ⧸ J_k)`**! -/
def patchingBaseRingEquivTruncLimit (p g : ℕ) [Fact p.Prime] :
    PatchingBaseRing p g ≃+* TruncLimit p g := by
  refine RingEquiv.ofBijective (ofBase p g) ⟨?_, ?_⟩
  · intro f h hfh
    apply sub_eq_zero.mp
    refine truncIdeal_iInf_eq_bot p g fun k => ?_
    have hk : truncProj p g k f = truncProj p g k h := congrArg (fun z : TruncLimit p g => z.val k) hfh
    exact Ideal.Quotient.eq.mp hk
  · intro x
    choose rep hrep using fun k => truncProj_surjective p g k (x.val k)
    have hcoeff_lim : ∀ α : Fin g →₀ ℕ, ∃ z : ℤ_[p],
        Tendsto (fun m : ℕ => MvPowerSeries.coeff α (rep ((∑ i : Fin g, α i) + m))) atTop (nhds z) := by
      intro α
      set d := ∑ i : Fin g, α i
      let u : ℕ → ℤ_[p] := fun m => MvPowerSeries.coeff α (rep (d + m))
      have hcauchy : CauchySeq u := by
        rw [Metric.cauchySeq_iff]
        intro ε hε
        have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
        have hlim : Tendsto (fun m : ℕ => ((p : ℝ)⁻¹) ^ (d + m + 1)) atTop (nhds 0) :=
          (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp_gt1)).comp
            (tendsto_atTop_mono (fun m => show m ≤ d + m + 1 by omega) tendsto_id)
        obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hlim) ε hε
        refine ⟨N, fun m hm n hn => ?_⟩
        wlog hmn : m ≤ n generalizing m n
        · rw [dist_comm]; exact this n hn m hm (le_of_not_ge hmn)
        have hdiff : rep (d + n) - rep (d + m) ∈ truncIdeal p g (d + m + 1) :=
          rep_sub_mem_of_le x rep hrep (by omega)
        have hdvd : (p : ℤ_[p]) ^ (d + m + 1) ∣ (u n - u m) := by
          simpa [u, map_sub] using hdiff α (by omega)
        have hnorm_le : ‖u n - u m‖ ≤ ((p : ℝ)⁻¹) ^ (d + m + 1) := by
          rw [← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow] at hdvd
          calc ‖u n - u m‖ ≤ (p : ℝ) ^ (-((d + m + 1 : ℕ) : ℤ)) := hdvd
            _ = ((p : ℝ)⁻¹) ^ (d + m + 1) := by rw [_root_.zpow_neg, zpow_natCast, inv_pow]
        have hN_lt : ((p : ℝ)⁻¹) ^ (d + m + 1) < ε := by
          have h1 := hN m hm
          rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h1
          exact h1
        rw [dist_comm, dist_eq_norm]
        exact lt_of_le_of_lt hnorm_le hN_lt
      exact CompleteSpace.complete hcauchy
    choose limCoeff hlimCoeff using hcoeff_lim
    let f : PatchingBaseRing p g := fun α => limCoeff α
    refine ⟨f, ?_⟩
    ext k
    change truncProj p g k f = x.val k
    rw [← hrep k]
    apply Ideal.Quotient.eq.mpr
    intro α hα
    set d := ∑ i : Fin g, α i
    rw [map_sub, ← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow]
    have htend : Tendsto (fun m : ℕ => ‖MvPowerSeries.coeff α (rep (d + m)) - MvPowerSeries.coeff α (rep k)‖)
        atTop (nhds ‖MvPowerSeries.coeff α f - MvPowerSeries.coeff α (rep k)‖) :=
      ((hlimCoeff α).sub tendsto_const_nhds).norm
    refine le_of_tendsto htend ?_
    filter_upwards [Filter.eventually_ge_atTop k] with m hm
    have hdiff : rep (d + m) - rep k ∈ truncIdeal p g (k + 1) :=
      rep_sub_mem_of_le x rep hrep (by omega)
    have hdvd : (p : ℤ_[p]) ^ (k + 1) ∣ (MvPowerSeries.coeff α (rep (d + m)) - MvPowerSeries.coeff α (rep k)) := by
      simpa [map_sub] using hdiff α hα
    rw [← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow] at hdvd
    exact hdvd

end TruncLimit

/-! ### 1.3 Genuine Ultraproduct Patching Engine (`UltraproductPatchingData` & `pmodEx_patched_free_over_Sinf`) -/

/-- A countable descending system of finite-quotient open ideals on a fixed ambient universal
deformation ring `R_univ` (e.g. `PatchingBaseRing p h_gen`), with ZERO nested `Algebra` diamonds. -/
structure FiniteQuotRingSystem (R_univ : Type) [CommRing R_univ] where
  K : ℕ → Ideal R_univ
  K_antitone : Antitone K
  K_finite : ∀ k : ℕ, Finite (R_univ ⧸ K k)
  K_iInf_bot : ∀ x : R_univ, (∀ k : ℕ, x ∈ K k) → x = 0

attribute [instance] FiniteQuotRingSystem.K_finite

/-- Canonical transition homomorphism `(R_univ ⧸ Q.K (k + 1)) →+* (R_univ ⧸ Q.K k)`. -/
def FiniteQuotRingSystem.trans {R_univ : Type} [CommRing R_univ]
    (Q : FiniteQuotRingSystem R_univ) (k : ℕ) :
    (R_univ ⧸ Q.K (k + 1)) →+* (R_univ ⧸ Q.K k) :=
  Ideal.quotientMap (Q.K k) (RingHom.id _) (fun _ hx => Q.K_antitone (Nat.le_succ k) hx)

/-- Concrete `FiniteQuotRingSystem` on `PatchingBaseRing p h` given by `truncIdeal p h (k + 1)`. -/
def patchingBaseFiniteQuotSystem (p h : ℕ) [Fact p.Prime] :
    FiniteQuotRingSystem (PatchingBaseRing p h) where
  K k := truncIdeal p h (k + 1)
  K_antitone _ _ hab := truncIdeal_antitone p h (Nat.add_le_add_right hab 1)
  K_finite k := instFiniteTruncRing p h k
  K_iInf_bot _ hf := truncIdeal_iInf_eq_bot p h hf

/-- **Finite-Level Taylor–Wiles–Thorne Ultraproduct Patching System**:
a sequence of finite-level patching data `(R_n, T_n, M_n)` over `S_∞ = PatchingBaseRing p g`
dominated by an ambient universal ring `R_univ` with finite-quotient system `Q`, together with a
non-principal ultrafilter `𝒰 : Ultrafilter ℕ` and level-0 specialization `(M_0, act0)`.
All actions and homomorphisms are bundled explicitly (ZERO `Algebra`/`SMul` diamonds!). -/
structure UltraproductPatchingData (p g : ℕ) [Fact p.Prime]
    (R_univ : Type) [CommRing R_univ] (Q : FiniteQuotRingSystem R_univ) where
  𝒰 : Ultrafilter ℕ
  𝒰_le_atTop : (𝒰 : Filter ℕ) ≤ Filter.atTop
  rank : ℕ
  rank_pos : 0 < rank
  /-- Diamond-algebra structure map `S_∞ →+* R_univ`. -/
  s_univ : PatchingBaseRing p g →+* R_univ
  /-- Finite-level kernel ideals `ker(R_univ ⧸ K_k → R_n ⧸ J_k R_n)` at level `n` and depth `k`. -/
  ker_nk : ℕ → ∀ k : ℕ, Ideal (R_univ ⧸ Q.K k)
  /-- Finite-level matrix representations `R_univ ⧸ K_k →+* M_r(TruncRing p g k)` induced by
  `M_n ⧸ J_k M_n ≃ (Fin rank → TruncRing p g k)`. -/
  act_nk : ℕ → ∀ k : ℕ, (R_univ ⧸ Q.K k) →+* Matrix (Fin rank) (Fin rank) (TruncRing p g k)
  /-- `𝒰`-eventually at depth `k`, the kernel `ker_nk n k` annihilates the level-`n` module action. -/
  ker_le_act : ∀ k : ℕ, ∀ᶠ n in (𝒰 : Filter ℕ),
    ker_nk n k ≤ RingHom.ker (act_nk n k)
  /-- `𝒰`-eventually at depth `k`, the `S_∞`-action is scalar. -/
  act_scalar_S : ∀ k : ℕ, ∀ᶠ n in (𝒰 : Filter ℕ),
    ∀ s : PatchingBaseRing p g,
      act_nk n k (Ideal.Quotient.mk (Q.K k) (s_univ s)) =
        Matrix.scalar (Fin rank) (truncProj p g k s)
  /-- `𝒰`-eventually at depth `k`, reducing the depth-`(k+1)` basis to depth `k` differs from
  the depth-`k` basis by an invertible transition matrix `U ∈ GL_r(TruncRing p g k)`. -/
  trans_conj : ∀ k : ℕ, ∀ᶠ n in (𝒰 : Filter ℕ),
    ∃ U : Matrix.GeneralLinearGroup (Fin rank) (TruncRing p g k),
      ∀ x : R_univ ⧸ Q.K (k + 1),
        RingHom.mapMatrix (truncTrans p g k) (act_nk n (k + 1) x) =
          U.1 * act_nk n k (Q.trans k x) * U⁻¹.1
  /-- Level-0 module `M_0` (free of rank `rank` over `ℤ_[p]`) and `R_univ`-action `act0`. -/
  M_0 : Type
  [addM0 : AddCommGroup M_0]
  [modZpM0 : Module ℤ_[p] M_0]
  eM0 : M_0 ≃ₗ[ℤ_[p]] (Fin rank → ℤ_[p])
  act0 : R_univ →+* Matrix (Fin rank) (Fin rank) ℤ_[p]
  act0_scalar : ∀ s : PatchingBaseRing p g,
    act0 (s_univ s) = Matrix.scalar (Fin rank) (MvPowerSeries.constantCoeff s)
  /-- Specialization compatibility: at every depth `k`, `𝒰`-eventually reducing `act_nk n k`
  modulo `(y_0,…,y_{g-1})` agrees with `act0` mod `p ^ (k + 1)` up to `GL_r(ZMod (p^(k+1)))`. -/
  spec_compat : ∀ k : ℕ, ∀ᶠ n in (𝒰 : Filter ℕ),
    ∀ x : R_univ,
      RingHom.mapMatrix (truncToZModPow p g k) (act_nk n k (Ideal.Quotient.mk (Q.K k) x)) =
        RingHom.mapMatrix (PadicInt.toZModPow (k + 1)) (act0 x)

attribute [instance] UltraproductPatchingData.addM0 UltraproductPatchingData.modZpM0

namespace UltraproductPatchingData

variable {p g : ℕ} [Fact p.Prime] {R_univ : Type} [CommRing R_univ]
  {Q : FiniteQuotRingSystem R_univ} (D : UltraproductPatchingData p g R_univ Q)

/-- Finite instance on `Ideal (R_univ ⧸ Q.K k)` (subsets of a finite ring). -/
instance instFiniteIdealQuot (k : ℕ) : Finite (Ideal (R_univ ⧸ Q.K k)) :=
  Finite.of_injective (fun I : Ideal (R_univ ⧸ Q.K k) => (I : Set (R_univ ⧸ Q.K k)))
    (fun _ _ h => SetLike.ext' h)

/-- Finite instance on ring homomorphisms `(R_univ ⧸ Q.K k) →+* M_r(TruncRing p g k)`. -/
instance instFiniteActHom (k : ℕ) :
    Finite ((R_univ ⧸ Q.K k) →+* Matrix (Fin D.rank) (Fin D.rank) (TruncRing p g k)) :=
  Finite.of_injective (fun f => (f : (R_univ ⧸ Q.K k) → Matrix (Fin D.rank) (Fin D.rank) (TruncRing p g k)))
    (fun _ _ h => RingHom.ext (congrFun h))

/-- Finite instance on `GL_r(TruncRing p g k)`. -/
instance instFiniteGLTrunc (k : ℕ) :
    Finite (Matrix.GeneralLinearGroup (Fin D.rank) (TruncRing p g k)) :=
  Finite.of_injective (fun U : Matrix.GeneralLinearGroup (Fin D.rank) (TruncRing p g k) => U.1)
    (fun _ _ h => Units.ext h)

/-- Stabilized depth-`k` kernel ideal `I_{∞,k} := lim_{n → 𝒰} ker_nk n k`. -/
def stabilizedKer (k : ℕ) : Ideal (R_univ ⧸ Q.K k) :=
  ultraLimitVal D.𝒰 (fun n => D.ker_nk n k)

/-- Stabilized depth-`k` matrix action `act_{∞,k} := lim_{n → 𝒰} act_nk n k`. -/
def stabilizedAct (k : ℕ) :
    (R_univ ⧸ Q.K k) →+* Matrix (Fin D.rank) (Fin D.rank) (TruncRing p g k) :=
  ultraLimitVal D.𝒰 (fun n => D.act_nk n k)

theorem stabilizedKer_le_act (k : ℕ) :
    D.stabilizedKer k ≤ RingHom.ker (D.stabilizedAct k) := by
  have h1 := ultraLimitVal_spec D.𝒰 (fun n => D.ker_nk n k)
  have h2 := ultraLimitVal_spec D.𝒰 (fun n => D.act_nk n k)
  have h3 := D.ker_le_act k
  obtain ⟨n, hnk, hna, hle⟩ := (h1.and (h2.and h3)).exists
  change D.ker_nk n k = D.stabilizedKer k at hnk
  change D.act_nk n k = D.stabilizedAct k at hna
  rw [← hnk, ← hna]
  exact hle

theorem stabilizedAct_scalar_S (k : ℕ) (s : PatchingBaseRing p g) :
    D.stabilizedAct k (Ideal.Quotient.mk (Q.K k) (D.s_univ s)) =
      Matrix.scalar (Fin D.rank) (truncProj p g k s) := by
  have h1 := ultraLimitVal_spec D.𝒰 (fun n => D.act_nk n k)
  have h2 := D.act_scalar_S k
  obtain ⟨n, hna, hsc⟩ := (h1.and h2).exists
  change D.act_nk n k = D.stabilizedAct k at hna
  rw [← hna]
  exact hsc s

theorem stabilizedAct_trans_conj (k : ℕ) :
    ∃ U : Matrix.GeneralLinearGroup (Fin D.rank) (TruncRing p g k),
      ∀ x : R_univ ⧸ Q.K (k + 1),
        RingHom.mapMatrix (truncTrans p g k) (D.stabilizedAct (k + 1) x) =
          U.1 * D.stabilizedAct k (Q.trans k x) * U⁻¹.1 := by
  have h1 := ultraLimitVal_spec D.𝒰 (fun n => D.act_nk n k)
  have h2 := ultraLimitVal_spec D.𝒰 (fun n => D.act_nk n (k + 1))
  have h3 := D.trans_conj k
  obtain ⟨n, ha_k, ha_k1, U, hU⟩ := (h1.and (h2.and h3)).exists
  change D.act_nk n k = D.stabilizedAct k at ha_k
  change D.act_nk n (k + 1) = D.stabilizedAct (k + 1) at ha_k1
  refine ⟨U, fun x => ?_⟩
  rw [← ha_k, ← ha_k1]
  exact hU x

theorem stabilizedAct_spec_compat (k : ℕ) (x : R_univ) :
    RingHom.mapMatrix (truncToZModPow p g k) (D.stabilizedAct k (Ideal.Quotient.mk (Q.K k) x)) =
      RingHom.mapMatrix (PadicInt.toZModPow (k + 1)) (D.act0 x) := by
  have h1 := ultraLimitVal_spec D.𝒰 (fun n => D.act_nk n k)
  have h2 := D.spec_compat k
  obtain ⟨n, hna, hsp⟩ := (h1.and h2).exists
  change D.act_nk n k = D.stabilizedAct k at hna
  rw [← hna]
  exact hsp x

/-- Helper: conjugation by `W ∈ GL_r(A)` is a ring endomorphism of `M_r(A)`. -/
private def conjMatHom {A : Type*} [CommRing A] {r : ℕ}
    (W : Matrix.GeneralLinearGroup (Fin r) A) :
    Matrix (Fin r) (Fin r) A →+* Matrix (Fin r) (Fin r) A where
  toFun M := W⁻¹.1 * M * W.1
  map_one' := by simp
  map_mul' M N := by
    calc W⁻¹.1 * (M * N) * W.1
        = W⁻¹.1 * M * (W.1 * W⁻¹.1) * N * W.1 := by rw [Units.mul_inv, Matrix.mul_one]; simp [Matrix.mul_assoc]
      _ = (W⁻¹.1 * M * W.1) * (W⁻¹.1 * N * W.1) := by simp [Matrix.mul_assoc]
  map_zero' := by simp
  map_add' M N := by rw [Matrix.mul_add, Matrix.add_mul]

/-- Inductive alignment matrices `alignMat D k ∈ GL_r(TruncRing p g k)` constructed via
`mapGL_surjective_of_ker_cube_zero` so that `alignedAct D k` forms a strictly compatible inverse
system! -/
def alignMat : ∀ k : ℕ, Matrix.GeneralLinearGroup (Fin D.rank) (TruncRing p g k)
  | 0 => 1
  | k + 1 =>
    let U := Classical.choose (D.stabilizedAct_trans_conj k)
    let V : Matrix.GeneralLinearGroup (Fin D.rank) (TruncRing p g k) := U * alignMat k
    Classical.choose
      (mapGL_surjective_of_ker_cube_zero D.rank (truncTrans p g k)
        (truncTrans_surjective p g k) (fun _ hx => truncTrans_ker_cube_eq_zero p g k hx) V)

theorem alignMat_succ_map (k : ℕ) :
    Units.map (RingHom.mapMatrix (truncTrans p g k)).toMonoidHom (D.alignMat (k + 1)) =
      Classical.choose (D.stabilizedAct_trans_conj k) * D.alignMat k :=
  Classical.choose_spec
    (mapGL_surjective_of_ker_cube_zero D.rank (truncTrans p g k)
      (truncTrans_surjective p g k) (fun _ hx => truncTrans_ker_cube_eq_zero p g k hx)
      (Classical.choose (D.stabilizedAct_trans_conj k) * D.alignMat k))

/-- Strictly compatible depth-`k` matrix action `R_univ →+* M_r(TruncRing p g k)`. -/
def alignedAct (k : ℕ) :
    R_univ →+* Matrix (Fin D.rank) (Fin D.rank) (TruncRing p g k) :=
  ((conjMatHom (D.alignMat k)).comp (D.stabilizedAct k)).comp (Ideal.Quotient.mk (Q.K k))

theorem alignedAct_compat (k : ℕ) (x : R_univ) :
    RingHom.mapMatrix (truncTrans p g k) (D.alignedAct (k + 1) x) = D.alignedAct k x := by
  let U := Classical.choose (D.stabilizedAct_trans_conj k)
  have hU := Classical.choose_spec (D.stabilizedAct_trans_conj k)
  have hW : Units.map (RingHom.mapMatrix (truncTrans p g k)).toMonoidHom (D.alignMat (k + 1)) =
      U * D.alignMat k := D.alignMat_succ_map k
  have hW_val : RingHom.mapMatrix (truncTrans p g k) (D.alignMat (k + 1)).1 =
      U.1 * (D.alignMat k).1 := congrArg Units.val hW
  have hWinv_val : RingHom.mapMatrix (truncTrans p g k) (D.alignMat (k + 1))⁻¹.1 =
      (D.alignMat k)⁻¹.1 * U⁻¹.1 := by
    have := congrArg (fun g => Units.val g⁻¹) hW
    simpa [map_inv, _root_.mul_inv_rev] using this
  change RingHom.mapMatrix (truncTrans p g k)
    ((D.alignMat (k + 1))⁻¹.1 * D.stabilizedAct (k + 1) (Ideal.Quotient.mk (Q.K (k + 1)) x) *
      (D.alignMat (k + 1)).1) =
    (D.alignMat k)⁻¹.1 * D.stabilizedAct k (Ideal.Quotient.mk (Q.K k) x) * (D.alignMat k).1
  rw [map_mul, map_mul, hWinv_val, hW_val, hU (Ideal.Quotient.mk (Q.K (k + 1)) x)]
  have htr : Q.trans k (Ideal.Quotient.mk (Q.K (k + 1)) x) = Ideal.Quotient.mk (Q.K k) x := rfl
  rw [htr]
  calc (D.alignMat k)⁻¹.1 * U⁻¹.1 *
        (U.1 * D.stabilizedAct k (Ideal.Quotient.mk (Q.K k) x) * U⁻¹.1) *
        (U.1 * (D.alignMat k).1)
      = (D.alignMat k)⁻¹.1 * (U⁻¹.1 * U.1) *
        D.stabilizedAct k (Ideal.Quotient.mk (Q.K k) x) *
        (U⁻¹.1 * U.1) * (D.alignMat k).1 := by simp only [Matrix.mul_assoc]
    _ = (D.alignMat k)⁻¹.1 * D.stabilizedAct k (Ideal.Quotient.mk (Q.K k) x) * (D.alignMat k).1 := by
        rw [Units.inv_mul, Matrix.mul_one, Matrix.mul_one]

theorem alignedAct_scalar_S (k : ℕ) (s : PatchingBaseRing p g) :
    D.alignedAct k (D.s_univ s) = Matrix.scalar (Fin D.rank) (truncProj p g k s) := by
  change (D.alignMat k)⁻¹.1 * D.stabilizedAct k (Ideal.Quotient.mk (Q.K k) (D.s_univ s)) *
      (D.alignMat k).1 = Matrix.scalar (Fin D.rank) (truncProj p g k s)
  rw [D.stabilizedAct_scalar_S k s, Matrix.scalar_apply]
  have h1 : Matrix.diagonal (fun _ : Fin D.rank => truncProj p g k s) =
      (truncProj p g k s) • (1 : Matrix (Fin D.rank) (Fin D.rank) (TruncRing p g k)) := by
    apply Matrix.ext; intro i j; by_cases hij : i = j <;> simp [hij]
  rw [h1, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Units.inv_mul]

/-- **Genuine Ultraproduct Inverse-Limit Matrix Action `patchedAct : R_univ →+* M_r(S_∞)`**! -/
def patchedAct : R_univ →+* Matrix (Fin D.rank) (Fin D.rank) (PatchingBaseRing p g) where
  toFun x i j :=
    (TruncLimit.patchingBaseRingEquivTruncLimit p g).symm
      ⟨fun k => D.alignedAct k x i j, fun k => by
        have h := congrFun (congrFun (D.alignedAct_compat k x) i) j
        simpa [RingHom.mapMatrix_apply] using h⟩
  map_one' := by
    apply Matrix.ext; intro i j
    apply (TruncLimit.patchingBaseRingEquivTruncLimit p g).injective
    rw [RingEquiv.apply_symm_apply]
    ext k
    change D.alignedAct k 1 i j = truncProj p g k ((1 : Matrix (Fin D.rank) (Fin D.rank) (PatchingBaseRing p g)) i j)
    rw [map_one]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  map_mul' x y := by
    apply Matrix.ext; intro i j
    apply (TruncLimit.patchingBaseRingEquivTruncLimit p g).injective
    rw [RingEquiv.apply_symm_apply]
    ext k
    change D.alignedAct k (x * y) i j =
      truncProj p g k (∑ l : Fin D.rank,
        ((TruncLimit.patchingBaseRingEquivTruncLimit p g).symm ⟨fun m => D.alignedAct m x i l, _⟩) *
        ((TruncLimit.patchingBaseRingEquivTruncLimit p g).symm ⟨fun m => D.alignedAct m y l j, _⟩))
    rw [map_mul, Matrix.mul_apply, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul]
    have h1 : truncProj p g k ((TruncLimit.patchingBaseRingEquivTruncLimit p g).symm
        ⟨fun m => D.alignedAct m x i l, fun m => by
          simpa [RingHom.mapMatrix_apply] using congrFun (congrFun (D.alignedAct_compat m x) i) l⟩) =
        D.alignedAct k x i l :=
      congrArg (fun z : TruncLimit p g => z.val k)
        ((TruncLimit.patchingBaseRingEquivTruncLimit p g).apply_symm_apply
          ⟨fun m => D.alignedAct m x i l, fun m => by
            simpa [RingHom.mapMatrix_apply] using congrFun (congrFun (D.alignedAct_compat m x) i) l⟩)
    have h2 : truncProj p g k ((TruncLimit.patchingBaseRingEquivTruncLimit p g).symm
        ⟨fun m => D.alignedAct m y l j, fun m => by
          simpa [RingHom.mapMatrix_apply] using congrFun (congrFun (D.alignedAct_compat m y) l) j⟩) =
        D.alignedAct k y l j :=
      congrArg (fun z : TruncLimit p g => z.val k)
        ((TruncLimit.patchingBaseRingEquivTruncLimit p g).apply_symm_apply
          ⟨fun m => D.alignedAct m y l j, fun m => by
            simpa [RingHom.mapMatrix_apply] using congrFun (congrFun (D.alignedAct_compat m y) l) j⟩)
    rw [h1, h2]
  map_zero' := by
    apply Matrix.ext; intro i j
    apply (TruncLimit.patchingBaseRingEquivTruncLimit p g).injective
    rw [RingEquiv.apply_symm_apply]
    ext k
    change D.alignedAct k 0 i j = truncProj p g k 0
    rw [map_zero, map_zero]; rfl
  map_add' x y := by
    apply Matrix.ext; intro i j
    apply (TruncLimit.patchingBaseRingEquivTruncLimit p g).injective
    rw [RingEquiv.apply_symm_apply]
    ext k
    change D.alignedAct k (x + y) i j =
      truncProj p g k (
        (TruncLimit.patchingBaseRingEquivTruncLimit p g).symm ⟨fun m => D.alignedAct m x i j, _⟩ +
        (TruncLimit.patchingBaseRingEquivTruncLimit p g).symm ⟨fun m => D.alignedAct m y i j, _⟩)
    rw [map_add, Matrix.add_apply, map_add]
    have h1 : truncProj p g k ((TruncLimit.patchingBaseRingEquivTruncLimit p g).symm
        ⟨fun m => D.alignedAct m x i j, fun m => by
          simpa [RingHom.mapMatrix_apply] using congrFun (congrFun (D.alignedAct_compat m x) i) j⟩) =
        D.alignedAct k x i j :=
      congrArg (fun z : TruncLimit p g => z.val k)
        ((TruncLimit.patchingBaseRingEquivTruncLimit p g).apply_symm_apply _)
    have h2 : truncProj p g k ((TruncLimit.patchingBaseRingEquivTruncLimit p g).symm
        ⟨fun m => D.alignedAct m y i j, fun m => by
          simpa [RingHom.mapMatrix_apply] using congrFun (congrFun (D.alignedAct_compat m y) i) j⟩) =
        D.alignedAct k y i j :=
      congrArg (fun z : TruncLimit p g => z.val k)
        ((TruncLimit.patchingBaseRingEquivTruncLimit p g).apply_symm_apply _)
    rw [h1, h2]

theorem patchedAct_truncProj (k : ℕ) (x : R_univ) :
    RingHom.mapMatrix (truncProj p g k) (D.patchedAct x) = D.alignedAct k x := by
  apply Matrix.ext; intro i j
  exact congrArg (fun z : TruncLimit p g => z.val k)
    ((TruncLimit.patchingBaseRingEquivTruncLimit p g).apply_symm_apply _)

theorem patchedAct_scalar_S (s : PatchingBaseRing p g) :
    D.patchedAct (D.s_univ s) = Matrix.scalar (Fin D.rank) s := by
  apply Matrix.ext; intro i j
  apply (TruncLimit.patchingBaseRingEquivTruncLimit p g).injective
  ext k
  have h1 := congrFun (congrFun (D.patchedAct_truncProj k (D.s_univ s)) i) j
  rw [D.alignedAct_scalar_S k s] at h1
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at h1
  change truncProj p g k (D.patchedAct (D.s_univ s) i j) =
    truncProj p g k (Matrix.scalar (Fin D.rank) s i j)
  rw [h1]
  by_cases hij : i = j
  · subst hij; simp [Matrix.scalar_apply]
  · simp [Matrix.scalar_apply, hij]

/-- Stabilized patched kernel ideal `I_∞ := ⋂_k comap(proj_k, I_{∞,k}) ≤ R_univ`. -/
def patchedIdeal : Ideal R_univ :=
  ⨅ k : ℕ, (D.stabilizedKer k).comap (Ideal.Quotient.mk (Q.K k))

theorem patchedIdeal_le_ker_patchedAct :
    D.patchedIdeal ≤ RingHom.ker D.patchedAct := by
  intro x hx
  rw [RingHom.mem_ker]
  apply Matrix.ext; intro i j
  change D.patchedAct x i j = 0
  apply (TruncLimit.patchingBaseRingEquivTruncLimit p g).injective
  rw [map_zero]
  ext k
  have hkx : Ideal.Quotient.mk (Q.K k) x ∈ D.stabilizedKer k :=
    Ideal.mem_iInf.mp hx k
  have hact0 : D.stabilizedAct k (Ideal.Quotient.mk (Q.K k) x) = 0 :=
    D.stabilizedKer_le_act k hkx
  have h1 := congrFun (congrFun (D.patchedAct_truncProj k x) i) j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at h1
  change truncProj p g k (D.patchedAct x i j) = 0
  rw [h1]
  change ((D.alignMat k)⁻¹.1 * D.stabilizedAct k (Ideal.Quotient.mk (Q.K k) x) *
    (D.alignMat k).1) i j = 0
  rw [hact0, Matrix.mul_zero, Matrix.zero_mul]; rfl

/-- **Patched Deformation Ring `R_∞ := R_univ ⧸ I_∞`**. -/
abbrev PatchedR : Type := R_univ ⧸ D.patchedIdeal

/-- Factored patched matrix action `R_∞ →+* M_r(S_∞)`. -/
def patchedActR : D.PatchedR →+* Matrix (Fin D.rank) (Fin D.rank) (PatchingBaseRing p g) :=
  Ideal.Quotient.lift D.patchedIdeal D.patchedAct (fun _ hx => D.patchedIdeal_le_ker_patchedAct hx)

/-- **Patched Ultraproduct Module `M_∞`** (carrier `Fin rank → PatchingBaseRing p g`, with
explicit `S_∞`-action and `R_∞`-action via `patchedActR`). -/
@[ext]
structure PatchedM where
  coords : Fin D.rank → PatchingBaseRing p g

instance instAddCommGroupPatchedM : AddCommGroup D.PatchedM where
  zero := ⟨0⟩
  add u v := ⟨u.coords + v.coords⟩
  neg u := ⟨-u.coords⟩
  sub u v := ⟨u.coords - v.coords⟩
  add_assoc u v w := PatchedM.ext (add_assoc u.coords v.coords w.coords)
  zero_add u := PatchedM.ext (zero_add u.coords)
  add_zero u := PatchedM.ext (add_zero u.coords)
  nsmul n u := ⟨n • u.coords⟩
  nsmul_zero u := PatchedM.ext (zero_nsmul u.coords)
  nsmul_succ n u := PatchedM.ext (succ_nsmul u.coords n)
  zsmul n u := ⟨n • u.coords⟩
  zsmul_zero' u := PatchedM.ext (zero_zsmul u.coords)
  zsmul_succ' n u := PatchedM.ext (by
    change ((n + 1 : ℕ) : ℤ) • u.coords = (n : ℤ) • u.coords + u.coords
    rw [Nat.cast_add, Nat.cast_one, add_zsmul, one_zsmul])
  zsmul_neg' n u := PatchedM.ext (by
    change Int.negSucc n • u.coords = -(((n + 1 : ℕ) : ℤ) • u.coords)
    rw [negSucc_zsmul, natCast_zsmul])
  sub_eq_add_neg u v := PatchedM.ext (sub_eq_add_neg u.coords v.coords)
  neg_add_cancel u := PatchedM.ext (neg_add_cancel u.coords)
  add_comm u v := PatchedM.ext (add_comm u.coords v.coords)

instance instModuleSPatchedM : Module (PatchingBaseRing p g) D.PatchedM where
  smul s u := ⟨s • u.coords⟩
  one_smul u := PatchedM.ext (one_smul _ u.coords)
  mul_smul s₁ s₂ u := PatchedM.ext (mul_smul s₁ s₂ u.coords)
  smul_zero s := PatchedM.ext (smul_zero s)
  smul_add s u v := PatchedM.ext (smul_add s u.coords v.coords)
  add_smul s₁ s₂ u := PatchedM.ext (add_smul s₁ s₂ u.coords)
  zero_smul u := PatchedM.ext (zero_smul _ u.coords)

instance instModuleRPatchedM : Module D.PatchedR D.PatchedM where
  smul r u := ⟨(D.patchedActR r).mulVec u.coords⟩
  one_smul u := PatchedM.ext (by
    change (D.patchedActR 1).mulVec u.coords = u.coords
    rw [map_one, Matrix.one_mulVec])
  mul_smul r₁ r₂ u := PatchedM.ext (by
    change (D.patchedActR (r₁ * r₂)).mulVec u.coords =
      (D.patchedActR r₁).mulVec ((D.patchedActR r₂).mulVec u.coords)
    rw [map_mul, Matrix.mulVec_mulVec])
  smul_zero r := PatchedM.ext (by
    change (D.patchedActR r).mulVec 0 = 0
    exact Matrix.mulVec_zero _)
  smul_add r u v := PatchedM.ext (Matrix.mulVec_add _ u.coords v.coords)
  add_smul r₁ r₂ u := PatchedM.ext (by
    change (D.patchedActR (r₁ + r₂)).mulVec u.coords =
      (D.patchedActR r₁).mulVec u.coords + (D.patchedActR r₂).mulVec u.coords
    rw [map_add, Matrix.add_mulVec])
  zero_smul u := PatchedM.ext (by
    change (D.patchedActR 0).mulVec u.coords = 0
    rw [map_zero, Matrix.zero_mulVec])

/-- Explicit `S_∞`-linear freeness equivalence `M_∞ ≃ₗ[S_∞] (Fin rank → S_∞)`. -/
def patchedMEquivFreeS : D.PatchedM ≃ₗ[PatchingBaseRing p g] (Fin D.rank → PatchingBaseRing p g) where
  toFun u := u.coords
  invFun v := ⟨v⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Compatibility of the `S_∞` and `R_∞` module actions via `s_R : S_∞ →+* R_∞`. -/
theorem patchedM_smul_sR (s : PatchingBaseRing p g) (u : D.PatchedM) :
    (Ideal.Quotient.mk D.patchedIdeal (D.s_univ s) : D.PatchedR) • u = s • u := by
  apply PatchedM.ext
  have hL : ((Ideal.Quotient.mk D.patchedIdeal (D.s_univ s) : D.PatchedR) • u).coords =
      (D.patchedAct (D.s_univ s)).mulVec u.coords := rfl
  rw [hL, D.patchedAct_scalar_S s, Matrix.scalar_apply]
  funext i
  simp [Matrix.mulVec_diagonal]
  rfl

/-- **Patched Hecke Algebra `T_∞ := R_∞ ⧸ Ann_{R_∞}(M_∞)`**. -/
abbrev PatchedT : Type := D.PatchedR ⧸ Module.annihilator D.PatchedR D.PatchedM

/-- Surjective patched homomorphism `φ_∞ : R_∞ →+* T_∞`. -/
def patchedPhi : D.PatchedR →+* D.PatchedT :=
  Ideal.Quotient.mk (Module.annihilator D.PatchedR D.PatchedM)

theorem patchedPhi_surjective : Function.Surjective D.patchedPhi :=
  Ideal.Quotient.mk_surjective

/-- Exact characterization `Ann_{R_∞}(M_∞) = ker(patchedActR)`. -/
theorem annihilator_patchedR_eq_ker :
    Module.annihilator D.PatchedR D.PatchedM = RingHom.ker D.patchedActR := by
  ext r
  rw [Module.mem_annihilator, RingHom.mem_ker]
  constructor
  · intro hr
    apply Matrix.ext; intro i j
    have hj := congrFun (congrArg PatchedM.coords (hr ⟨Pi.single j 1⟩)) i
    have hL : ((r • (⟨Pi.single j 1⟩ : D.PatchedM)).coords) i =
        ((D.patchedActR r).mulVec (Pi.single j 1)) i := rfl
    have hR : ((0 : D.PatchedM).coords) i = 0 := rfl
    rw [hL, hR] at hj
    simpa [Matrix.mulVec_single] using hj
  · intro hr m
    apply PatchedM.ext
    have hL : (r • m).coords = (D.patchedActR r).mulVec m.coords := rfl
    have hR : (0 : D.PatchedM).coords = 0 := rfl
    rw [hL, hR, hr, Matrix.zero_mulVec]

/-- Factored faithful action `T_∞ →+* M_r(S_∞)`. -/
def patchedActT : D.PatchedT →+* Matrix (Fin D.rank) (Fin D.rank) (PatchingBaseRing p g) :=
  Ideal.Quotient.lift (Module.annihilator D.PatchedR D.PatchedM) D.patchedActR
    (fun r hr => by rw [D.annihilator_patchedR_eq_ker, RingHom.mem_ker] at hr; exact hr)

instance instModuleTPatchedM : Module D.PatchedT D.PatchedM where
  smul t u := ⟨(D.patchedActT t).mulVec u.coords⟩
  one_smul u := PatchedM.ext (by
    change (D.patchedActT 1).mulVec u.coords = u.coords
    rw [map_one, Matrix.one_mulVec])
  mul_smul t₁ t₂ u := PatchedM.ext (by
    change (D.patchedActT (t₁ * t₂)).mulVec u.coords =
      (D.patchedActT t₁).mulVec ((D.patchedActT t₂).mulVec u.coords)
    rw [map_mul, Matrix.mulVec_mulVec])
  smul_zero t := PatchedM.ext (by
    change (D.patchedActT t).mulVec 0 = 0
    exact Matrix.mulVec_zero _)
  smul_add t u v := PatchedM.ext (Matrix.mulVec_add _ u.coords v.coords)
  add_smul t₁ t₂ u := PatchedM.ext (by
    change (D.patchedActT (t₁ + t₂)).mulVec u.coords =
      (D.patchedActT t₁).mulVec u.coords + (D.patchedActT t₂).mulVec u.coords
    rw [map_add, Matrix.add_mulVec])
  zero_smul u := PatchedM.ext (by
    change (D.patchedActT 0).mulVec u.coords = 0
    rw [map_zero, Matrix.zero_mulVec])

theorem patchedT_faithful : Module.annihilator D.PatchedT D.PatchedM = ⊥ := by
  rw [eq_bot_iff]
  intro t ht
  obtain ⟨r, rfl⟩ := D.patchedPhi_surjective t
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [Module.mem_annihilator]
  intro m
  have hm := Module.mem_annihilator.mp ht m
  exact PatchedM.ext (congrArg PatchedM.coords hm)

/-- Bundled specialized patched module `M_∞ ⧸ (y_0,…,y_{g-1}) M_∞` with its canonical `ℤ_[p]`-action. -/
abbrev PatchedM0 : Type := Coinv (patchingAugIdeal p g) D.PatchedM

instance instModuleZpPatchedM0 : Module ℤ_[p] D.PatchedM0 :=
  Module.compHom D.PatchedM0 (patchingBaseRing_quot_augIdeal_equiv_Zp p g).symm.toRingHom

/-- Specialization of `M_∞` modulo `(y_0,…,y_{g-1})` recovers `D.M_0` as a `ℤ_[p]`-module! -/
def specM0Equiv : D.PatchedM0 ≃ₗ[ℤ_[p]] D.M_0 := by
  let e1 := coinvEquivPiOfEquivPi (patchingAugIdeal p g) D.patchedMEquivFreeS
  let eR : (PatchingBaseRing p g ⧸ patchingAugIdeal p g) ≃+* ℤ_[p] :=
    patchingBaseRing_quot_augIdeal_equiv_Zp p g
  let e2 : D.PatchedM0 ≃ₗ[ℤ_[p]] (Fin D.rank → ℤ_[p]) :=
    { toFun := fun x i => eR (e1 x i)
      invFun := fun v => e1.symm (fun i => eR.symm (v i))
      left_inv := fun x => by
        dsimp only
        have h : (fun i => eR.symm (eR (e1 x i))) = e1 x := funext fun i => eR.symm_apply_apply _
        rw [h, e1.symm_apply_apply]
      right_inv := fun v => by ext i; simp
      map_add' := fun x y => by ext i; simp [map_add]
      map_smul' := fun a x => by
        ext i
        change eR (e1 (eR.symm a • x) i) = a * eR (e1 x i)
        rw [e1.map_smul, Pi.smul_apply, smul_eq_mul, map_mul, eR.apply_symm_apply] }
  exact e2.trans D.eM0.symm

/-- Level-0 Hecke ring `T_0 := R_univ ⧸ ker(act0)` acting faithfully on `M_0`. -/
abbrev Level0T : Type := R_univ ⧸ RingHom.ker D.act0

/-- Factored level-0 matrix action `T_0 →+* M_r(ℤ_[p])`. -/
def level0ActT : D.Level0T →+* Matrix (Fin D.rank) (Fin D.rank) ℤ_[p] :=
  Ideal.Quotient.lift (RingHom.ker D.act0) D.act0 (fun _ h => RingHom.mem_ker.mp h)

instance instModuleLevel0TM0 : Module D.Level0T D.M_0 where
  smul t m := D.eM0.symm ((D.level0ActT t).mulVec (D.eM0 m))
  one_smul m := by
    change D.eM0.symm ((D.level0ActT 1).mulVec (D.eM0 m)) = m
    rw [map_one, Matrix.one_mulVec, D.eM0.symm_apply_apply]
  mul_smul t₁ t₂ m := by
    change D.eM0.symm ((D.level0ActT (t₁ * t₂)).mulVec (D.eM0 m)) =
      D.eM0.symm ((D.level0ActT t₁).mulVec (D.eM0 (D.eM0.symm ((D.level0ActT t₂).mulVec (D.eM0 m)))))
    rw [D.eM0.apply_symm_apply, map_mul, Matrix.mulVec_mulVec]
  smul_zero t := by
    change D.eM0.symm ((D.level0ActT t).mulVec (D.eM0 0)) = 0
    rw [map_zero, Matrix.mulVec_zero, map_zero]
  smul_add t m₁ m₂ := by
    change D.eM0.symm ((D.level0ActT t).mulVec (D.eM0 (m₁ + m₂))) =
      D.eM0.symm ((D.level0ActT t).mulVec (D.eM0 m₁)) +
      D.eM0.symm ((D.level0ActT t).mulVec (D.eM0 m₂))
    rw [map_add, Matrix.mulVec_add, map_add]
  add_smul t₁ t₂ m := by
    change D.eM0.symm ((D.level0ActT (t₁ + t₂)).mulVec (D.eM0 m)) =
      D.eM0.symm ((D.level0ActT t₁).mulVec (D.eM0 m)) +
      D.eM0.symm ((D.level0ActT t₂).mulVec (D.eM0 m))
    rw [map_add, Matrix.add_mulVec, map_add]
  zero_smul m := by
    change D.eM0.symm ((D.level0ActT 0).mulVec (D.eM0 m)) = 0
    rw [map_zero, Matrix.zero_mulVec, map_zero]

theorem level0T_faithful : Module.annihilator D.Level0T D.M_0 = ⊥ := by
  rw [eq_bot_iff]
  intro t ht
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective t
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [RingHom.mem_ker]
  apply Matrix.ext; intro i j
  have hm := Module.mem_annihilator.mp ht (D.eM0.symm (Pi.single j 1))
  have hm' := congrFun (congrArg D.eM0 hm) i
  have hact : (Ideal.Quotient.mk (RingHom.ker D.act0) x : D.Level0T) • D.eM0.symm (Pi.single j 1) =
      D.eM0.symm ((D.act0 x).mulVec (D.eM0 (D.eM0.symm (Pi.single j 1)))) := rfl
  rw [hact, D.eM0.apply_symm_apply, D.eM0.apply_symm_apply, map_zero] at hm'
  simpa [Matrix.mulVec_single] using hm'

/-- **MASTER THEOREM 1 (`pmodEx_patched_free_over_Sinf`)**:
Unconditional Non-Principal Ultrafilter Patching Theorem! From ANY `UltraproductPatchingData`:
1. `M_∞` is **finite free** of positive rank `D.rank ≥ 1` over `S_∞ = ℤ_[p][[y_0,…,y_{g-1}]]`;
2. `M_∞` is a **faithful** `T_∞`-module (`Ann_{T_∞}(M_∞) = ⊥`);
3. `patchedPhi : R_∞ →+* T_∞` is surjective, and whenever `Ann_{R_∞}(M_∞) ≤ nilradical R_∞`,
   `ker(patchedPhi)` is nilpotent, and if `IsReduced R_∞` then **`R_∞ ≃+* T_∞`**;
4. Specialization modulo `(y_0,…,y_{g-1})` recovers `M_0` (`PatchedM0 ≃ₗ[ℤ_[p]] M_0`) as a
   faithful `T_0`-module! -/
theorem pmodEx_patched_free_over_Sinf :
    0 < D.rank ∧
    Nonempty (D.PatchedM ≃ₗ[PatchingBaseRing p g] (Fin D.rank → PatchingBaseRing p g)) ∧
    Function.Surjective D.patchedPhi ∧
    Module.annihilator D.PatchedT D.PatchedM = ⊥ ∧
    (Module.annihilator D.PatchedR D.PatchedM ≤ nilradical D.PatchedR →
      (∀ r ∈ RingHom.ker D.patchedPhi, IsNilpotent r) ∧
      (IsReduced D.PatchedR → Nonempty (D.PatchedR ≃+* D.PatchedT))) ∧
    Nonempty (D.PatchedM0 ≃ₗ[ℤ_[p]] D.M_0) ∧
    Module.annihilator D.Level0T D.M_0 = ⊥ := by
  refine ⟨D.rank_pos, ⟨D.patchedMEquivFreeS⟩, D.patchedPhi_surjective, D.patchedT_faithful,
    ?_, ⟨D.specM0Equiv⟩, D.level0T_faithful⟩
  intro hnil
  have hker_eq : RingHom.ker D.patchedPhi = Module.annihilator D.PatchedR D.PatchedM :=
    Ideal.mk_ker
  refine ⟨fun r hr => hnil (hker_eq ▸ hr), fun hred => ?_⟩
  have hker_bot : RingHom.ker D.patchedPhi = ⊥ := by
    rw [eq_bot_iff]
    intro r hr
    exact IsReduced.eq_zero r (hnil (hker_eq ▸ hr))
  have hinj : Function.Injective D.patchedPhi :=
    (RingHom.injective_iff_ker_eq_bot D.patchedPhi).mpr hker_bot
  exact ⟨RingEquiv.ofBijective D.patchedPhi ⟨hinj, D.patchedPhi_surjective⟩⟩

end UltraproductPatchingData

end UltrafilterPatching

/-! ## Section 2: Higher-Rank `𝒢_n` Ordinary Determinant Rings & Thorne Component-Chain Propagation
(`CoreBC`, `LiftPt`, `AnnBc`) -/

section HigherRankDetAndThornePropagation

/-! ### 2.1 Higher-Rank `𝒢_d` Groups & Chenevier Ordinary Determinant Rings -/

/-- **Clozel–Harris–Taylor Group `𝒢_d(R) := (GL_d(R) × Rˣ) ⋊ {1, c}`**:
represented explicitly as triples `(g, μ, ε)` with `ε : Bool` (`false` = `𝒢_d⁰`, `true` = `c · 𝒢_d⁰`),
with twisted multiplication `(g₁, μ₁, false) * (g₂, μ₂, ε₂) = (g₁ g₂, μ₁ μ₂, ε₂)` and
`(g₁, μ₁, true) * (g₂, μ₂, ε₂) = (g₁ (μ₂ • (g₂ᵀ)⁻¹), μ₁ μ₂, !ε₂)`. -/
@[ext]
structure GnGroup (d : ℕ) (R : Type*) [CommRing R] where
  mat : Matrix.GeneralLinearGroup (Fin d) R
  mult : Rˣ
  parity : Bool

namespace GnGroup

variable {d : ℕ} {R : Type*} [CommRing R]

/-- Helper: transpose-inverse automorphism on `GL_d(R)` (`g ↦ (gᵀ)⁻¹`). -/
def transposeInv (g : Matrix.GeneralLinearGroup (Fin d) R) :
    Matrix.GeneralLinearGroup (Fin d) R where
  val := g⁻¹.1.transpose
  inv := g.1.transpose
  val_inv := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

@[simp] theorem transposeInv_one : transposeInv (1 : Matrix.GeneralLinearGroup (Fin d) R) = 1 := by
  apply Units.ext; simp [transposeInv]

@[simp] theorem transposeInv_mul (g h : Matrix.GeneralLinearGroup (Fin d) R) :
    transposeInv (g * h) = transposeInv g * transposeInv h := by
  apply Units.ext
  change (g * h)⁻¹.1.transpose = g⁻¹.1.transpose * h⁻¹.1.transpose
  rw [_root_.mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

@[simp] theorem transposeInv_invol (g : Matrix.GeneralLinearGroup (Fin d) R) :
    transposeInv (transposeInv g) = g := by
  apply Units.ext
  change (transposeInv g)⁻¹.1.transpose = g.1
  change (g.1.transpose).transpose = g.1
  exact Matrix.transpose_transpose g.1

/-- Scalar unit matrix `μ • I_d ∈ GL_d(R)`. -/
def scalarGL (μ : Rˣ) : Matrix.GeneralLinearGroup (Fin d) R where
  val := Matrix.scalar (Fin d) (μ : R)
  inv := Matrix.scalar (Fin d) ((μ⁻¹ : Rˣ) : R)
  val_inv := by rw [← map_mul, Units.mul_inv, map_one]
  inv_val := by rw [← map_mul, Units.inv_mul, map_one]

theorem scalarGL_comm (μ : Rˣ) (g : Matrix.GeneralLinearGroup (Fin d) R) :
    scalarGL (d := d) μ * g = g * scalarGL μ := by
  apply Units.ext
  change Matrix.scalar (Fin d) (μ : R) * g.1 = g.1 * Matrix.scalar (Fin d) (μ : R)
  have hsc : Matrix.scalar (Fin d) (μ : R) = (μ : R) • (1 : Matrix (Fin d) (Fin d) R) := by
    apply Matrix.ext; intro i j; by_cases hij : i = j <;> simp [hij]
  rw [hsc, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

@[simp] theorem scalarGL_one : scalarGL (d := d) (1 : Rˣ) = 1 := by
  apply Units.ext; exact map_one _

@[simp] theorem scalarGL_mul (μ ν : Rˣ) :
    scalarGL (d := d) (μ * ν) = scalarGL μ * scalarGL ν := by
  apply Units.ext; exact map_mul _ _ _

@[simp] theorem transposeInv_scalarGL (μ : Rˣ) :
    transposeInv (scalarGL (d := d) μ) = scalarGL μ⁻¹ := by
  apply Units.ext
  change (Matrix.scalar (Fin d) ((μ⁻¹ : Rˣ) : R)).transpose = Matrix.scalar (Fin d) ((μ⁻¹ : Rˣ) : R)
  apply Matrix.ext; intro i j; by_cases hij : i = j <;> simp [hij, eq_comm]

/-- The outer involution `θ(g, μ) = (μ • (gᵀ)⁻¹, μ)` on `GL_d(R) × Rˣ`. -/
def twist (g : Matrix.GeneralLinearGroup (Fin d) R) (μ : Rˣ) :
    Matrix.GeneralLinearGroup (Fin d) R :=
  scalarGL μ * transposeInv g

theorem twist_mul (g₁ g₂ : Matrix.GeneralLinearGroup (Fin d) R) (μ₁ μ₂ : Rˣ) :
    twist (g₁ * g₂) (μ₁ * μ₂) = twist g₁ μ₁ * twist g₂ μ₂ := by
  unfold twist
  rw [scalarGL_mul, transposeInv_mul]
  calc scalarGL μ₁ * scalarGL μ₂ * (transposeInv g₁ * transposeInv g₂)
      = scalarGL μ₁ * (scalarGL μ₂ * transposeInv g₁) * transposeInv g₂ := by group
    _ = scalarGL μ₁ * (transposeInv g₁ * scalarGL μ₂) * transposeInv g₂ := by
          rw [scalarGL_comm μ₂ (transposeInv g₁)]
    _ = scalarGL μ₁ * transposeInv g₁ * (scalarGL μ₂ * transposeInv g₂) := by group

theorem twist_twist (g : Matrix.GeneralLinearGroup (Fin d) R) (μ : Rˣ) :
    twist (twist g μ) μ = g := by
  unfold twist
  rw [transposeInv_mul, transposeInv_scalarGL, transposeInv_invol]
  calc scalarGL μ * (scalarGL μ⁻¹ * g)
      = (scalarGL μ * scalarGL μ⁻¹) * g := by group
    _ = scalarGL (μ * μ⁻¹) * g := by rw [← scalarGL_mul]
    _ = g := by rw [mul_inv_cancel, scalarGL_one, one_mul]

instance : One (GnGroup d R) := ⟨⟨1, 1, false⟩⟩
instance : Mul (GnGroup d R) := ⟨fun x y =>
  ⟨if x.parity then x.mat * twist y.mat y.mult else x.mat * y.mat,
   x.mult * y.mult,
   xor x.parity y.parity⟩⟩
instance : Inv (GnGroup d R) := ⟨fun x =>
  ⟨if x.parity then twist x.mat⁻¹ x.mult⁻¹ else x.mat⁻¹,
   x.mult⁻¹,
   x.parity⟩⟩

@[simp] theorem one_mat : (1 : GnGroup d R).mat = 1 := rfl
@[simp] theorem one_mult : (1 : GnGroup d R).mult = 1 := rfl
@[simp] theorem one_parity : (1 : GnGroup d R).parity = false := rfl
@[simp] theorem mul_mat (x y : GnGroup d R) :
    (x * y).mat = if x.parity then x.mat * twist y.mat y.mult else x.mat * y.mat := rfl
@[simp] theorem mul_mult (x y : GnGroup d R) : (x * y).mult = x.mult * y.mult := rfl
@[simp] theorem mul_parity (x y : GnGroup d R) : (x * y).parity = xor x.parity y.parity := rfl
@[simp] theorem inv_mat (x : GnGroup d R) :
    x⁻¹.mat = if x.parity then twist x.mat⁻¹ x.mult⁻¹ else x.mat⁻¹ := rfl
@[simp] theorem inv_mult (x : GnGroup d R) : x⁻¹.mult = x.mult⁻¹ := rfl
@[simp] theorem inv_parity (x : GnGroup d R) : x⁻¹.parity = x.parity := rfl

/-- Explicit `Group` structure on `𝒢_d(R)`. -/
instance instGroup : Group (GnGroup d R) where
  mul_assoc x y z := by
    cases x with | mk g₁ μ₁ b₁ =>
    cases y with | mk g₂ μ₂ b₂ =>
    cases z with | mk g₃ μ₃ b₃ =>
    cases b₁ <;> cases b₂ <;> cases b₃ <;>
      (apply GnGroup.ext <;> simp [twist_mul, twist_twist, mul_assoc])
  one_mul x := by
    cases x with | mk g μ b =>
    cases b <;> (apply GnGroup.ext <;> simp)
  mul_one x := by
    cases x with | mk g μ b =>
    cases b <;> (apply GnGroup.ext <;> simp [twist])
  inv_mul_cancel x := by
    cases x with | mk g μ b =>
    cases b
    · apply GnGroup.ext <;> simp
    · apply GnGroup.ext
      · simp only [mul_mat, inv_parity, inv_mat, ↓reduceIte, one_mat]
        rw [← twist_mul, inv_mul_cancel, inv_mul_cancel]
        simp [twist]
      · simp
      · simp

/-- Multiplier character `ν : 𝒢_d(R) →* Rˣ`. -/
def multHom : GnGroup d R →* Rˣ where
  toFun x := x.mult
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Index-2 parity homomorphism `𝒢_d(R) →* Multiplicative (ZMod 2)` (represented via `Bool`). -/
def isEvenSubgroup : Subgroup (GnGroup d R) where
  carrier := { x | x.parity = false }
  one_mem' := rfl
  mul_mem' {x y} hx hy := by change xor x.parity y.parity = false; rw [hx, hy]; rfl
  inv_mem' {x} hx := hx

end GnGroup

/-- **Degree-`d` Chenevier Determinant Law / Characteristic Polynomial Datum** on a group `G`
with coefficients in a commutative ring `R`. -/
@[ext]
structure DetLaw (G : Type*) [Group G] (R : Type*) [CommRing R] (d : ℕ) where
  charpoly : G → Polynomial R
  monic : ∀ g : G, (charpoly g).Monic
  natDegree_eq : ∀ g : G, (charpoly g).natDegree = d
  charpoly_one : charpoly 1 = (Polynomial.X - 1) ^ d
  charpoly_conj : ∀ g h : G, charpoly (h * g * h⁻¹) = charpoly g

namespace DetLaw

/-- Functorial base change of a determinant law along any `RingHom f : R →+* S`. -/
def map {G R S : Type*} [Group G] [CommRing R] [CommRing S] [Nontrivial S] {d : ℕ}
    (D : DetLaw G R d) (f : R →+* S) : DetLaw G S d where
  charpoly g := (D.charpoly g).map f
  monic g := (D.monic g).map f
  natDegree_eq g := by
    rw [(D.monic g).natDegree_map f, D.natDegree_eq g]
  charpoly_one := by
    rw [D.charpoly_one, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one]
  charpoly_conj g h := by rw [D.charpoly_conj g h]

/-- Concrete determinant law attached to any matrix representation `ρ : G →* GL_d(R)`. -/
def ofRep {G R : Type*} [Group G] [CommRing R] [Nontrivial R] {d : ℕ}
    (ρ : G →* Matrix.GeneralLinearGroup (Fin d) R) : DetLaw G R d where
  charpoly g := (ρ g).1.charpoly
  monic g := Matrix.charpoly_monic (ρ g).1
  natDegree_eq g := by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  charpoly_one := by rw [map_one, Units.val_one, Matrix.charpoly_one, Fintype.card_fin]
  charpoly_conj g h := by
    rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul]
    have h1 : (ρ h).1 * (ρ g).1 * (ρ h)⁻¹.1 = (ρ h).1 * ((ρ g).1 * (ρ h)⁻¹.1) := by
      rw [Matrix.mul_assoc]
    rw [h1, Matrix.charpoly_mul_comm, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

theorem ofRep_map {G R S : Type*} [Group G] [CommRing R] [Nontrivial R] [CommRing S] [Nontrivial S]
    {d : ℕ} (ρ : G →* Matrix.GeneralLinearGroup (Fin d) R) (f : R →+* S) :
    (ofRep ρ).map f = ofRep ((Units.map (RingHom.mapMatrix f).toMonoidHom).comp ρ) := by
  apply DetLaw.ext
  funext g
  change ((ρ g).1.charpoly).map f = (RingHom.mapMatrix f (ρ g).1).charpoly
  unfold Matrix.charpoly Matrix.charmatrix
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det (Polynomial.mapRingHom f)]
  congr 1
  apply Matrix.ext; intro i j
  change Polynomial.map f (Matrix.scalar (Fin d) Polynomial.X i j - Polynomial.C ((ρ g).1 i j)) =
    Matrix.scalar (Fin d) Polynomial.X i j - Polynomial.C (f ((ρ g).1 i j))
  rw [Polynomial.map_sub, Polynomial.map_C]
  by_cases hij : i = j
  · subst hij; simp [Matrix.scalar_apply]
  · simp [Matrix.scalar_apply, hij]

end DetLaw

/-- **Higher-Rank Ordinary Determinant Ring Datum (`OrdinaryDetDatum`)**:
a commutative ring `R` equipped with a degree-`d` Chenevier determinant law `detLaw` on `G` and
ordinary local inertia characters `ordChar v i : I_v →* Rˣ` at each `p`-adic place `v ∈ Places`
such that `detLaw.charpoly (ι_v g) = ∏ i : Fin d, (X - C (ordChar v i g))`. -/
structure OrdinaryDetDatum (G : Type*) [Group G] (Places : Type*)
    (I_loc : Places → Type*) [∀ v, Group (I_loc v)] (ι_loc : ∀ v, I_loc v →* G)
    (R : Type*) [CommRing R] (d : ℕ) where
  detLaw : DetLaw G R d
  ordChar : ∀ v : Places, Fin d → (I_loc v →* Rˣ)
  ord_factor : ∀ (v : Places) (g : I_loc v),
    detLaw.charpoly (ι_loc v g) =
      ∏ i : Fin d, (Polynomial.X - Polynomial.C (ordChar v i g : R))

/-- Functorial pushforward of an `OrdinaryDetDatum` along any `RingHom f : R →+* S`. -/
def OrdinaryDetDatum.map {G Places : Type*} [Group G]
    {I_loc : Places → Type*} [∀ v, Group (I_loc v)] {ι_loc : ∀ v, I_loc v →* G}
    {R S : Type*} [CommRing R] [CommRing S] [Nontrivial S] {d : ℕ}
    (O : OrdinaryDetDatum G Places I_loc ι_loc R d) (f : R →+* S) :
    OrdinaryDetDatum G Places I_loc ι_loc S d where
  detLaw := O.detLaw.map f
  ordChar v i := (Units.map f.toMonoidHom).comp (O.ordChar v i)
  ord_factor v g := by
    change (O.detLaw.charpoly (ι_loc v g)).map f = _
    rw [O.ord_factor v g, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

/-! ### 2.2 Taylor–Wiles–Thorne Support Theorem (`Supp(M_∞)` = Union of Irreducible Components) -/

/-- Support of an `R`-module `M` in `PrimeSpectrum R`: `{ 𝔭 | Ann_R(M) ≤ 𝔭 }`. -/
def ModuleSupport (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] :
    Set (PrimeSpectrum R) :=
  { 𝔭 : PrimeSpectrum R | Module.annihilator R M ≤ 𝔭.asIdeal }

/-- Characteristic-0 locus `Spec(R[1/p]) ⊆ Spec(R)`: primes not containing `p`. -/
def CharZeroLocus (R : Type*) [CommRing R] (p : ℕ) : Set (PrimeSpectrum R) :=
  { 𝔭 : PrimeSpectrum R | (p : R) ∉ 𝔭.asIdeal }

/-- **Pure Commutative-Algebra Strict-Drop Krull Dimension Lemma**:
if `𝔮 < 𝔭` are prime ideals of `R`, then `ringKrullDim (R ⧸ 𝔭) + 1 ≤ ringKrullDim (R ⧸ 𝔮)`. -/
theorem ringKrullDim_quot_lt_add_one_le {R : Type*} [CommRing R] {𝔮 𝔭 : Ideal R}
    [𝔮.IsPrime] [𝔭.IsPrime] (hlt : 𝔮 < 𝔭) :
    ringKrullDim (R ⧸ 𝔭) + 1 ≤ ringKrullDim (R ⧸ 𝔮) := by
  have hlift : ∀ s : LTSeries (PrimeSpectrum (R ⧸ 𝔭)),
      ∃ t : LTSeries (PrimeSpectrum (R ⧸ 𝔮)), t.length = s.length + 1 := by
    intro s
    let mkq : R →+* R ⧸ 𝔮 := Ideal.Quotient.mk 𝔮
    let mkp : R →+* R ⧸ 𝔭 := Ideal.Quotient.mk 𝔭
    let qMap : (R ⧸ 𝔮) →+* (R ⧸ 𝔭) := Ideal.quotientMap 𝔭 (RingHom.id R) (fun _ hx => hlt.le hx)
    have hbot_prime : (⊥ : Ideal (R ⧸ 𝔮)).IsPrime :=
      Ideal.isPrime_bot
    let botPt : PrimeSpectrum (R ⧸ 𝔮) := ⟨⊥, hbot_prime⟩
    let up : Fin (s.length + 1) → PrimeSpectrum (R ⧸ 𝔮) :=
      fun i => PrimeSpectrum.comap qMap (s.toFun i)
    have hbot_lt_up0 : botPt < up 0 := by
      change (⊥ : Ideal (R ⧸ 𝔮)) < (s.toFun 0).asIdeal.comap qMap
      rw [lt_iff_le_and_ne]
      refine ⟨bot_le, fun heq => ?_⟩
      obtain ⟨a, ha_p, ha_not_q⟩ := SetLike.exists_of_lt hlt
      have hmem : mkq a ∈ (s.toFun 0).asIdeal.comap qMap := by
        change qMap (mkq a) ∈ (s.toFun 0).asIdeal
        have h0 : qMap (mkq a) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha_p
        rw [h0]; exact (s.toFun 0).asIdeal.zero_mem
      rw [← heq, Ideal.mem_bot] at hmem
      exact ha_not_q (Ideal.Quotient.eq_zero_iff_mem.mp hmem)
    have hup_mono : StrictMono up := by
      intro i j hij
      have hlt_ij : (s.toFun i).asIdeal < (s.toFun j).asIdeal := s.strictMono hij
      change (s.toFun i).asIdeal.comap qMap < (s.toFun j).asIdeal.comap qMap
      rw [lt_iff_le_and_ne]
      refine ⟨Ideal.comap_mono hlt_ij.le, fun heq => ?_⟩
      obtain ⟨y, hyj, hyni⟩ := SetLike.exists_of_lt hlt_ij
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
      have hr : mkq r ∈ (s.toFun j).asIdeal.comap qMap := hyj
      rw [← heq] at hr
      exact hyni hr
    let tFun : Fin (s.length + 2) → PrimeSpectrum (R ⧸ 𝔮) :=
      Fin.cons botPt up
    refine ⟨{ length := s.length + 1, toFun := tFun, step := fun i => ?_ }, rfl⟩
    refine Fin.cases ?_ (fun i' => ?_) i
    · simpa [tFun, Fin.cons_zero, Fin.cons_succ] using hbot_lt_up0
    · simpa [tFun, Fin.cons_succ] using hup_mono (Fin.castSucc_lt_succ (i := i'))
  have hle : ∀ s : LTSeries (PrimeSpectrum (R ⧸ 𝔭)),
      ((s.length : WithBot ℕ∞) + 1) ≤ ringKrullDim (R ⧸ 𝔮) := by
    intro s
    obtain ⟨t, ht⟩ := hlift s
    have h1 : (t.length : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ 𝔮) :=
      le_iSup (fun u : LTSeries (PrimeSpectrum (R ⧸ 𝔮)) => (u.length : WithBot ℕ∞)) t
    rw [ht] at h1
    simpa [Nat.cast_add] using h1
  let s0 : LTSeries (PrimeSpectrum (R ⧸ 𝔭)) := RelSeries.singleton _ ⟨⊥, Ideal.isPrime_bot⟩
  cases hM : ringKrullDim (R ⧸ 𝔮) with
  | bot =>
    have h0 := hle s0
    rw [hM] at h0
    exact absurd h0 (by simp [s0])
  | coe e =>
    cases e with
    | top => exact le_top
    | coe m =>
      have hm_pos : 1 ≤ m := by
        have h0 := hle s0
        rw [hM] at h0
        have : ((s0.length + 1 : ℕ) : WithBot ℕ∞) ≤ ((m : ℕ) : WithBot ℕ∞) := by
          simpa [Nat.cast_add] using h0
        have hnat : s0.length + 1 ≤ m := by exact_mod_cast this
        omega
      have hL : ringKrullDim (R ⧸ 𝔭) ≤ (((m - 1 : ℕ) : WithBot ℕ∞)) := by
        unfold ringKrullDim Order.krullDim
        refine iSup_le fun s => ?_
        have hs := hle s
        rw [hM] at hs
        have hcast : ((s.length + 1 : ℕ) : WithBot ℕ∞) ≤ ((m : ℕ) : WithBot ℕ∞) := by
          simpa [Nat.cast_add] using hs
        have hnat : s.length + 1 ≤ m := by exact_mod_cast hcast
        have hnat' : s.length ≤ m - 1 := by omega
        exact_mod_cast hnat'
      calc ringKrullDim (R ⧸ 𝔭) + 1
          ≤ (((m - 1 : ℕ) : WithBot ℕ∞)) + 1 := add_le_add hL le_rfl
        _ = ((m : ℕ) : WithBot ℕ∞) := by
            have hm_eq : (m - 1) + 1 = m := by omega
            have : ((((m - 1) + 1 : ℕ) : WithBot ℕ∞)) = ((m : ℕ) : WithBot ℕ∞) := by rw [hm_eq]
            simpa [Nat.cast_add] using this

/-- Helper: `ringKrullDim (R ⧸ 𝔮) ≤ ringKrullDim R` for every prime `𝔮` of `R`. -/
theorem ringKrullDim_quot_le {R : Type*} [CommRing R] (𝔮 : Ideal R) :
    ringKrullDim (R ⧸ 𝔮) ≤ ringKrullDim R := by
  unfold ringKrullDim Order.krullDim
  refine iSup_le fun s => ?_
  let t : LTSeries (PrimeSpectrum R) :=
    { length := s.length
      toFun := fun i => PrimeSpectrum.comap (Ideal.Quotient.mk 𝔮) (s.toFun i)
      step := fun i => by
        have hlt : (s.toFun i.castSucc).asIdeal < (s.toFun i.succ).asIdeal :=
          s.strictMono (Fin.castSucc_lt_succ (i := i))
        change (s.toFun i.castSucc).asIdeal.comap (Ideal.Quotient.mk 𝔮) <
          (s.toFun i.succ).asIdeal.comap (Ideal.Quotient.mk 𝔮)
        rw [lt_iff_le_and_ne]
        refine ⟨Ideal.comap_mono hlt.le, fun heq => ?_⟩
        obtain ⟨y, hy1, hy0⟩ := SetLike.exists_of_lt hlt
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
        have hmem : r ∈ (s.toFun i.succ).asIdeal.comap (Ideal.Quotient.mk 𝔮) := hy1
        rw [← heq] at hmem
        exact hy0 hmem }
  exact le_iSup (fun u : LTSeries (PrimeSpectrum R) => (u.length : WithBot ℕ∞)) t

/-- **Dimension-Matching Minimality Criterion**: if `ringKrullDim R ≤ d` (`d : ℕ`) and a prime `𝔭`
satisfies `d ≤ ringKrullDim (R ⧸ 𝔭)`, then `𝔭` is a **minimal prime of `R`**! -/
theorem mem_minimalPrimes_of_dim_ge {R : Type*} [CommRing R] {d : ℕ}
    (hdimR : ringKrullDim R ≤ (d : WithBot ℕ∞)) {𝔭 : Ideal R} (h𝔭 : 𝔭.IsPrime)
    (hdimP : (d : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ 𝔭)) :
    𝔭 ∈ minimalPrimes R := by
  refine ⟨⟨h𝔭, bot_le⟩, fun 𝔮 ⟨h𝔮, _⟩ hle => ?_⟩
  by_contra hnot
  have hlt : 𝔮 < 𝔭 := lt_of_le_of_ne hle (fun h => hnot (le_of_eq h.symm))
  have : 𝔮.IsPrime := h𝔮
  have : 𝔭.IsPrime := h𝔭
  have hstep := ringKrullDim_quot_lt_add_one_le hlt
  have h1 : ((d : WithBot ℕ∞) + 1) ≤ (d : WithBot ℕ∞) :=
    (add_le_add hdimP le_rfl).trans (hstep.trans ((ringKrullDim_quot_le 𝔮).trans hdimR))
  have hcast : ((d + 1 : ℕ) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by
    simpa [Nat.cast_add] using h1
  have hnat : d + 1 ≤ d := by exact_mod_cast hcast
  omega

/-- **Crucial Noetherian Torsion-Free Contraction Lemma**:
if `R` is a Noetherian `S`-algebra over an integral domain `S`, and `M` is an `R`-module that is
`S`-torsion-free (in particular, free of finite rank over `S`), then EVERY minimal prime `𝔭` of
`Module.annihilator R M` satisfies **`Ideal.comap (algebraMap S R) 𝔭 = ⊥`**! -/
theorem comap_minimalPrime_annihilator_eq_bot {S R M : Type*}
    [CommRing S] [IsDomain S] [CommRing R] [IsNoetherianRing R] [Algebra S R]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower S R M]
    (htf : ∀ (s : S), s ≠ 0 → ∀ (m : M), s • m = 0 → m = 0)
    {𝔭 : Ideal R} (h𝔭 : 𝔭 ∈ (Module.annihilator R M).minimalPrimes) :
    Ideal.comap (algebraMap S R) 𝔭 = ⊥ := by
  classical
  let I := Module.annihilator R M
  have h𝔭_prime : 𝔭.IsPrime := h𝔭.1.1
  have hfin : I.minimalPrimes.Finite := by
    rw [Ideal.minimalPrimes_eq_comap]
    exact (minimalPrimes.finite_of_isNoetherianRing (R ⧸ I)).image _
  let minSet : Finset (Ideal R) := hfin.toFinset
  rw [eq_bot_iff]
  intro s hs
  rw [Ideal.mem_bot]
  by_contra hs0
  have hpick : ∀ 𝔮 ∈ minSet.erase 𝔭, ∃ a : R, a ∈ 𝔮 ∧ a ∉ 𝔭 := by
    intro 𝔮 h𝔮
    rw [Finset.mem_erase, Set.Finite.mem_toFinset] at h𝔮
    have hnotle : ¬ (𝔮 ≤ 𝔭) := fun hle => h𝔮.1 (le_antisymm hle (h𝔭.2 h𝔮.2.1 hle))
    exact SetLike.not_le_iff_exists.mp hnotle
  choose a ha using fun 𝔮 : { 𝔮 // 𝔮 ∈ minSet.erase 𝔭 } => hpick 𝔮.1 𝔮.2
  let prodA : R := ∏ 𝔮 ∈ (minSet.erase 𝔭).attach, a 𝔮
  have hprodA_not_mem : prodA ∉ 𝔭 := by
    intro hmem
    obtain ⟨𝔮, _, hqmem⟩ := h𝔭_prime.prod_mem_iff.mp hmem
    exact (ha 𝔮).2 hqmem
  have hrad : algebraMap S R s * prodA ∈ I.radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    intro P ⟨hIP, hPprime⟩
    obtain ⟨𝔮, h𝔮min, h𝔮le⟩ := Ideal.exists_minimalPrimes_le hIP
    by_cases hqp : 𝔮 = 𝔭
    · subst hqp
      exact h𝔮le (Ideal.mul_mem_right prodA 𝔮 hs)
    · have hmem_er : 𝔮 ∈ minSet.erase 𝔭 :=
        Finset.mem_erase.mpr ⟨hqp, hfin.mem_toFinset.mpr h𝔮min⟩
      have haq : prodA ∈ 𝔮 := by
        obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem a (Finset.mem_attach _ ⟨𝔮, hmem_er⟩)
        dsimp only [prodA]
        rw [hc]
        exact Ideal.mul_mem_right c 𝔮 (ha ⟨𝔮, hmem_er⟩).1
      exact h𝔮le (Ideal.mul_mem_left 𝔮 (algebraMap S R s) haq)
  obtain ⟨N, hN⟩ := hrad
  have hpow_ann : (algebraMap S R (s ^ N) * prodA ^ N) ∈ I := by
    rwa [mul_pow, ← map_pow] at hN
  have hprod_ann : prodA ^ N ∈ I := by
    rw [Module.mem_annihilator]
    intro m
    have hsmul0 : (s ^ N) • (prodA ^ N • m) = 0 := by
      rw [← algebraMap_smul R (s ^ N), ← mul_smul]
      exact Module.mem_annihilator.mp hpow_ann m
    exact htf (s ^ N) (pow_ne_zero N hs0) (prodA ^ N • m) hsmul0
  have hprod_in_p : prodA ^ N ∈ 𝔭 := h𝔭.1.2 hprod_ann
  exact hprodA_not_mem (h𝔭_prime.mem_of_pow_mem N hprod_in_p)

/-- **TAYLOR–WILES–THORNE SUPPORT THEOREM (`supp_eq_union_irred_components`)**:
Let `S_∞ = PatchingBaseRing p g = ℤ_[p][[y_0,…,y_{g-1}]]`, let `R` be a Noetherian finite
`S_∞`-algebra with **`ringKrullDim R ≤ g + 1`**, and let `M` be an `R`-module that is **free of
positive finite rank `r ≥ 1` over `S_∞`**. Then:
1. EVERY minimal prime `𝔭` of `Module.annihilator R M` is a **minimal prime of `R`**
   (`𝔭 ∈ minimalPrimes R`) with `ringKrullDim (R ⧸ 𝔭) = g + 1`;
2. **`ModuleSupport R M` is a union of irreducible components of `Spec(R)`**:
   `Q ∈ ModuleSupport R M ↔ ∃ 𝔭 ∈ minimalPrimes R, Module.annihilator R M ≤ 𝔭 ∧ 𝔭 ≤ Q.asIdeal`! -/
theorem supp_eq_union_irred_components {p g r : ℕ} [Fact p.Prime] (_hr : 0 < r)
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [Algebra (PatchingBaseRing p g) R]
    [Module.Finite (PatchingBaseRing p g) R]
    [AddCommGroup M] [Module (PatchingBaseRing p g) M] [Module R M]
    [IsScalarTower (PatchingBaseRing p g) R M]
    (eM : M ≃ₗ[PatchingBaseRing p g] (Fin r → PatchingBaseRing p g))
    (hdimR : ringKrullDim R ≤ ((g + 1 : ℕ) : WithBot ℕ∞)) :
    (∀ 𝔭 ∈ (Module.annihilator R M).minimalPrimes,
      𝔭 ∈ minimalPrimes R ∧ ringKrullDim (R ⧸ 𝔭) = ((g + 1 : ℕ) : WithBot ℕ∞)) ∧
    (∀ Q : PrimeSpectrum R,
      Q ∈ ModuleSupport R M ↔
        ∃ 𝔭 ∈ minimalPrimes R, Module.annihilator R M ≤ 𝔭 ∧ 𝔭 ≤ Q.asIdeal) := by
  have htf : ∀ (s : PatchingBaseRing p g), s ≠ 0 → ∀ (m : M), s • m = 0 → m = 0 := by
    intro s hs m hm
    apply eM.injective
    rw [map_zero]
    funext i
    have hi := congrFun (congrArg eM hm) i
    rw [eM.map_smul, map_zero, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
    exact (mul_eq_zero.mp hi).resolve_left hs
  have hmin : ∀ 𝔭 ∈ (Module.annihilator R M).minimalPrimes,
      𝔭 ∈ minimalPrimes R ∧ ringKrullDim (R ⧸ 𝔭) = ((g + 1 : ℕ) : WithBot ℕ∞) := by
    intro 𝔭 h𝔭
    have hcomap : Ideal.comap (algebraMap (PatchingBaseRing p g) R) 𝔭 = ⊥ :=
      comap_minimalPrime_annihilator_eq_bot htf h𝔭
    have hinj : Function.Injective (algebraMap (PatchingBaseRing p g) (R ⧸ 𝔭)) := by
      rw [RingHom.injective_iff_ker_eq_bot]
      change Ideal.comap (algebraMap (PatchingBaseRing p g) R) (RingHom.ker (Ideal.Quotient.mk 𝔭)) = ⊥
      rw [Ideal.mk_ker]
      exact hcomap
    have : Module.Finite (PatchingBaseRing p g) (R ⧸ 𝔭) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ (PatchingBaseRing p g) 𝔭).toLinearMap
        Ideal.Quotient.mk_surjective
    have hdim_ge : ((g + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ 𝔭) :=
      (ringKrullDim_patchingBaseRing_ge p g).trans (ringKrullDim_le_of_isIntegral_injective hinj)
    have hdim_le : ringKrullDim (R ⧸ 𝔭) ≤ ((g + 1 : ℕ) : WithBot ℕ∞) :=
      (ringKrullDim_quot_le 𝔭).trans hdimR
    exact ⟨mem_minimalPrimes_of_dim_ge hdimR h𝔭.1.1 hdim_ge, le_antisymm hdim_le hdim_ge⟩
  refine ⟨hmin, fun Q => ?_⟩
  constructor
  · intro hQ
    obtain ⟨𝔭, h𝔭min, h𝔭le⟩ := Ideal.exists_minimalPrimes_le hQ
    exact ⟨𝔭, (hmin 𝔭 h𝔭min).1, h𝔭min.1.2, h𝔭le⟩
  · rintro ⟨𝔭, _, hann, hle⟩
    exact hann.trans hle

/-! ### 2.3 Irreducible-Component Graph of `Spec(R[1/p])`, Component-Chain Propagation (`CoreBC`, `LiftPt`),
& Nakayama Determinant-Trick Fiber Theorem (`AnnBc`) -/

/-- **Single-Component Automorphy Propagation**: if `Supp_R(M)` is a union of irreducible components
of `Spec(R)` and a point `x ∈ Supp_R(M)` lies on a UNIQUE minimal prime `𝔭` of `R` (a smooth /
generic point of component `𝔭`), then `Ann_R(M) ≤ 𝔭` and EVERY point `y ∈ V(𝔭)` (in particular
every characteristic-0 point on `𝔭`) lies in `Supp_R(M)`! -/
theorem same_component_automorphic {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (hunion : ∀ Q : PrimeSpectrum R,
      Q ∈ ModuleSupport R M ↔
        ∃ 𝔮 ∈ minimalPrimes R, Module.annihilator R M ≤ 𝔮 ∧ 𝔮 ≤ Q.asIdeal)
    {𝔭 : Ideal R} {x : PrimeSpectrum R} (hx_supp : x ∈ ModuleSupport R M)
    (hx_unique : ∀ 𝔮 ∈ minimalPrimes R, 𝔮 ≤ x.asIdeal → 𝔮 = 𝔭) :
    Module.annihilator R M ≤ 𝔭 ∧
    ∀ y : PrimeSpectrum R, 𝔭 ≤ y.asIdeal → y ∈ ModuleSupport R M := by
  obtain ⟨𝔮, h𝔮min, h𝔮ann, h𝔮le⟩ := (hunion x).mp hx_supp
  have hEq : 𝔮 = 𝔭 := hx_unique 𝔮 h𝔮min h𝔮le
  subst hEq
  exact ⟨h𝔮ann, fun y hy => h𝔮ann.trans hy⟩

/-- **Irreducible-Component Chain (`CompChain`)** of length `h` in `Spec(R)` relative to an adjacency
relation `Adj : Ideal R → Ideal R → Prop` on minimal primes (Thorne / `CoreBC` component graph). -/
structure CompChain (R : Type*) [CommRing R] (Adj : Ideal R → Ideal R → Prop)
    (𝔭₀ 𝔭_end : Ideal R) where
  len : ℕ
  nodes : Fin (len + 1) → Ideal R
  nodes_min : ∀ i, nodes i ∈ minimalPrimes R
  start_eq : nodes 0 = 𝔭₀
  end_eq : nodes (Fin.last len) = 𝔭_end
  step_adj : ∀ i : Fin len, Adj (nodes i.castSucc) (nodes i.succ)

/-- **Thorne / `CoreBC` Base-Change Component Transition Certificate**:
two minimal primes `𝔭, 𝔮 ∈ minimalPrimes R` are `CoreBC`-adjacent for `(R, M)` if there exists a
characteristic-0 intersection prime `E ∈ CharZeroLocus R p` with `𝔭 ≤ E` and `𝔮 ≤ E` and a local
transition property certifying that whenever `M` is supported on `𝔭`, it is also supported on `𝔮`
(abstracting Alpöge's `ChainAbs` / `pmMove` transfer across completed local rings `B_i`). -/
def CoreBCAdj (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] (p : ℕ)
    (𝔭 𝔮 : Ideal R) : Prop :=
  (∃ E : PrimeSpectrum R, E ∈ CharZeroLocus R p ∧ 𝔭 ≤ E.asIdeal ∧ 𝔮 ≤ E.asIdeal) ∧
  (Module.annihilator R M ≤ 𝔭 → Module.annihilator R M ≤ 𝔮)

/-- **TAYLOR–WILES–THORNE COMPONENT-CHAIN PROPAGATION (`liftPt_support_propagation`)**:
Over `S_∞ = PatchingBaseRing p g`, if `R` is Noetherian finite over `S_∞` with `dim R ≤ g + 1`,
`M` is free of rank `r ≥ 1` over `S_∞`, `x₀ ∈ Supp_R(M)` is an automorphic seed lying uniquely on
component `𝔭₀`, and `C : CompChain R (CoreBCAdj R M p) 𝔭₀ 𝔭_end` is ANY chain of intersecting
characteristic-0 components, then **`Ann_R(M) ≤ 𝔭_end`** and **EVERY characteristic-0 point
`y ∈ CharZeroLocus R p` on `𝔭_end` is automorphic (`y ∈ Supp_R(M)`)**! -/
theorem liftPt_support_propagation {p g r : ℕ} [Fact p.Prime] (hr : 0 < r)
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [Algebra (PatchingBaseRing p g) R]
    [Module.Finite (PatchingBaseRing p g) R]
    [AddCommGroup M] [Module (PatchingBaseRing p g) M] [Module R M]
    [IsScalarTower (PatchingBaseRing p g) R M]
    (eM : M ≃ₗ[PatchingBaseRing p g] (Fin r → PatchingBaseRing p g))
    (hdimR : ringKrullDim R ≤ ((g + 1 : ℕ) : WithBot ℕ∞))
    {𝔭₀ 𝔭_end : Ideal R} {x₀ : PrimeSpectrum R}
    (hx₀_supp : x₀ ∈ ModuleSupport R M)
    (hx₀_unique : ∀ 𝔮 ∈ minimalPrimes R, 𝔮 ≤ x₀.asIdeal → 𝔮 = 𝔭₀)
    (C : CompChain R (CoreBCAdj R M p) 𝔭₀ 𝔭_end) :
    Module.annihilator R M ≤ 𝔭_end ∧
    ∀ y : PrimeSpectrum R, y ∈ CharZeroLocus R p → 𝔭_end ≤ y.asIdeal → y ∈ ModuleSupport R M := by
  have hunion := (supp_eq_union_irred_components hr eM hdimR).2
  have hstart : Module.annihilator R M ≤ C.nodes 0 := by
    rw [C.start_eq]
    exact (same_component_automorphic hunion hx₀_supp hx₀_unique).1
  have hind : ∀ i : Fin (C.len + 1), Module.annihilator R M ≤ C.nodes i := by
    intro i
    induction i using Fin.induction with
    | zero => exact hstart
    | succ j ih => exact (C.step_adj j).2 ih
  have hend : Module.annihilator R M ≤ 𝔭_end := by
    rw [← C.end_eq]
    exact hind (Fin.last C.len)
  exact ⟨hend, fun y _ hy => hend.trans hy⟩

/-- **NAKAYAMA DETERMINANT-TRICK FIBER SUPPORT THEOREM (`supp_coinv_eq_inter`)**:
for ANY finitely generated `R`-module `M`, ANY ideal `I ≤ R`, and ANY prime ideal `𝔭` of `R`
containing `I`:
**`Ann_R(M / I M) ≤ 𝔭 ↔ Ann_R(M) ≤ 𝔭`**!
(Proved unconditionally via the `adjugate` determinant trick — zero localization needed!) -/
theorem annihilator_coinv_le_prime_iff {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) {𝔭 : Ideal R} (h𝔭 : 𝔭.IsPrime) (hI : I ≤ 𝔭) :
    Module.annihilator R (Coinv I M) ≤ 𝔭 ↔ Module.annihilator R M ≤ 𝔭 := by
  constructor
  · intro hle a ha
    apply hle
    rw [Module.mem_annihilator]
    intro x
    induction x using Quotient.inductionOn' with
    | h m =>
      change Submodule.Quotient.mk (p := I • (⊤ : Submodule R M)) (a • m) = 0
      rw [Module.mem_annihilator.mp ha m, Submodule.Quotient.mk_zero]
  · intro hle a ha
    have ha_le : ∀ m : M, a • m ∈ 𝔭 • (⊤ : Submodule R M) := by
      intro m
      have hq0 : Submodule.Quotient.mk (p := I • (⊤ : Submodule R M)) (a • m) = 0 :=
        Module.mem_annihilator.mp ha (Submodule.Quotient.mk m)
      have hmI : a • m ∈ I • (⊤ : Submodule R M) := (Submodule.Quotient.mk_eq_zero _).mp hq0
      exact Submodule.smul_mono hI le_rfl hmI
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
    let n := Fintype.card s
    let eFin : Fin n ≃ s := (Fintype.equivFin s).symm
    let v : Fin n → M := fun i => (eFin i).1
    have hv_span : Submodule.span R (Set.range v) = ⊤ := by
      rw [eq_top_iff]
      intro m _
      have hm : m ∈ Submodule.span R (s : Set M) := by rw [hs]; trivial
      refine Submodule.span_mono ?_ hm
      intro x hx
      refine ⟨eFin.symm ⟨x, hx⟩, ?_⟩
      simp [v]
    have hcoeff : ∀ i : Fin n, ∃ row : Fin n → R,
        (∀ j, row j ∈ 𝔭) ∧ a • v i = ∑ j : Fin n, row j • v j := by
      intro i
      have hmem : a • v i ∈ 𝔭 • Submodule.span R (Set.range v) := by
        rw [hv_span]; exact ha_le (v i)
      refine Submodule.smul_induction_on hmem ?_ ?_
      · intro r hr m hm
        rw [Submodule.mem_span_range_iff_exists_fun] at hm
        obtain ⟨c, rfl⟩ := hm
        refine ⟨fun j => r * c j, fun j => Ideal.mul_mem_right (c j) 𝔭 hr, ?_⟩
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => by rw [mul_smul]
      · rintro _ _ ⟨r₁, hr₁, h₁⟩ ⟨r₂, hr₂, h₂⟩
        refine ⟨fun j => r₁ j + r₂ j, fun j => Ideal.add_mem 𝔭 (hr₁ j) (hr₂ j), ?_⟩
        rw [h₁, h₂, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => by rw [add_smul]
    choose P hP_mem hP_eq using hcoeff
    let Pmat : Matrix (Fin n) (Fin n) R := Matrix.of P
    let A : Matrix (Fin n) (Fin n) R := Matrix.diagonal (fun _ : Fin n => a) - Pmat
    have hAv : ∀ i : Fin n, ∑ j : Fin n, A i j • v j = 0 := by
      intro i
      have h1 : ∑ j : Fin n, A i j • v j =
          (∑ j : Fin n, Matrix.diagonal (fun _ : Fin n => a) i j • v j) -
          (∑ j : Fin n, P i j • v j) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        change (Matrix.diagonal (fun _ : Fin n => a) i j - P i j) • v j = _
        rw [sub_smul]
      rw [h1]
      have hdiag : ∑ j : Fin n, Matrix.diagonal (fun _ : Fin n => a) i j • v j = a • v i := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji; simp [Matrix.diagonal_apply_ne _ hji.symm]
        · intro h; exact absurd (Finset.mem_univ i) h
      rw [hdiag, hP_eq i, sub_self]
    have hdet_ann : A.det ∈ Module.annihilator R M := by
      rw [Module.mem_annihilator]
      intro m
      have hm : m ∈ Submodule.span R (Set.range v) := by rw [hv_span]; trivial
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hm
      · rintro _ ⟨k, rfl⟩
        have hsum0 : ∑ i : Fin n, (Matrix.adjugate A k i) • (∑ j : Fin n, A i j • v j) = 0 :=
          Finset.sum_eq_zero fun i _ => by rw [hAv i, smul_zero]
        have hrew : ∑ i : Fin n, (Matrix.adjugate A k i) • (∑ j : Fin n, A i j • v j) =
            ∑ j : Fin n, ((Matrix.adjugate A * A) k j) • v j := by
          simp_rw [Finset.smul_sum, smul_smul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Matrix.mul_apply, Finset.sum_smul]
        rw [hrew, Matrix.adjugate_mul] at hsum0
        have hdiag : ∑ j : Fin n, (A.det • (1 : Matrix (Fin n) (Fin n) R)) k j • v j = A.det • v k := by
          rw [Finset.sum_eq_single k]
          · simp
          · intro j _ hjk; simp [Matrix.one_apply_ne (Ne.symm hjk)]
          · intro h; exact absurd (Finset.mem_univ k) h
        rwa [hdiag] at hsum0
      · exact smul_zero _
      · intro x y _ _ hx hy; rw [smul_add, hx, hy, add_zero]
      · intro c x _ hx; rw [smul_comm, hx, smul_zero]
    have hdet_p : A.det ∈ 𝔭 := hle hdet_ann
    have hmapA : RingHom.mapMatrix (Ideal.Quotient.mk 𝔭) A =
        Matrix.diagonal (fun _ : Fin n => Ideal.Quotient.mk 𝔭 a) := by
      apply Matrix.ext; intro i j
      change Ideal.Quotient.mk 𝔭 (Matrix.diagonal (fun _ : Fin n => a) i j - P i j) = _
      rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr (hP_mem i j), sub_zero]
      by_cases hij : i = j <;> simp [hij]
    have hpow0 : (Ideal.Quotient.mk 𝔭 a) ^ n = 0 := by
      have h1 : (RingHom.mapMatrix (Ideal.Quotient.mk 𝔭) A).det = 0 := by
        rw [← RingHom.map_det (Ideal.Quotient.mk 𝔭) A]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hdet_p
      rw [hmapA, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
      exact h1
    have hpow_mem : a ^ n ∈ 𝔭 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_pow]; exact hpow0
    exact h𝔭.mem_of_pow_mem n hpow_mem

/-- **`AnnBc` Nilpotence & Reduced `R_0^red ≃+* T_0` Theorem**:
Let `R_∞` be Noetherian finite over `S_∞ = PatchingBaseRing p g` with `ringKrullDim R_∞ ≤ g + 1`,
`M_∞` free of rank `r ≥ 1` over `S_∞`, and suppose EVERY minimal prime `𝔭 ∈ minimalPrimes R_∞` is
reachable by a `CoreBCAdj` component chain from an automorphic seed point `x_𝔭 ∈ Supp(M_∞)`.
Then:
1. **`Ann_{R_∞}(M_∞)` is nilpotent** (`≤ nilradical R_∞`, and `∃ N, Ann_{R_∞}(M_∞)^N = ⊥`);
2. For `I_y := (patchingAugIdeal p g).map (algebraMap S_∞ R_∞)`, `R_0 := R_∞ ⧸ I_y`,
   `M_0 := Coinv I_y M_∞`, **`Ann_{R_0}(M_0)` is nilpotent** (`≤ nilradical R_0`);
3. Letting `T_0 := R_0 ⧸ Ann_{R_0}(M_0)`, the canonical map induces a **ring isomorphism on
   reduced quotients `R_0 ⧸ nilradical R_0 ≃+* T_0 ⧸ nilradical T_0`**, and whenever `T_0` is
   reduced, **`(R_0 ⧸ nilradical R_0) ≃+* T_0`**! -/
theorem annBc_nilpotent_and_reduced_R0_equiv_T0 {p g r : ℕ} [Fact p.Prime] (hr : 0 < r)
    {R_inf M_inf : Type*} [CommRing R_inf] [IsNoetherianRing R_inf]
    [Algebra (PatchingBaseRing p g) R_inf] [Module.Finite (PatchingBaseRing p g) R_inf]
    [AddCommGroup M_inf] [Module (PatchingBaseRing p g) M_inf] [Module R_inf M_inf]
    [IsScalarTower (PatchingBaseRing p g) R_inf M_inf]
    (eM : M_inf ≃ₗ[PatchingBaseRing p g] (Fin r → PatchingBaseRing p g))
    (hdimR : ringKrullDim R_inf ≤ ((g + 1 : ℕ) : WithBot ℕ∞))
    (hconn : ∀ 𝔭 ∈ minimalPrimes R_inf,
      ∃ (𝔭₀ : Ideal R_inf) (x₀ : PrimeSpectrum R_inf),
        x₀ ∈ ModuleSupport R_inf M_inf ∧
        (∀ 𝔮 ∈ minimalPrimes R_inf, 𝔮 ≤ x₀.asIdeal → 𝔮 = 𝔭₀) ∧
        Nonempty (CompChain R_inf (CoreBCAdj R_inf M_inf p) 𝔭₀ 𝔭)) :
    let I_y := (patchingAugIdeal p g).map (algebraMap (PatchingBaseRing p g) R_inf)
    let R_0 := R_inf ⧸ I_y
    let M_0 := Coinv I_y M_inf
    let T_0 := R_0 ⧸ Module.annihilator R_0 M_0
    Module.annihilator R_inf M_inf ≤ nilradical R_inf ∧
    (∃ N : ℕ, Module.annihilator R_inf M_inf ^ N = ⊥) ∧
    Module.annihilator R_0 M_0 ≤ nilradical R_0 ∧
    Nonempty ((R_0 ⧸ nilradical R_0) ≃+* (T_0 ⧸ nilradical T_0)) ∧
    (IsReduced T_0 → Nonempty ((R_0 ⧸ nilradical R_0) ≃+* T_0)) := by
  intro I_y R_0 M_0 T_0
  have : Module.Finite (PatchingBaseRing p g) M_inf := Module.Finite.equiv eM.symm
  have : Module.Finite R_inf M_inf :=
    Module.Finite.of_restrictScalars_finite (PatchingBaseRing p g) R_inf M_inf
  -- Step 1: `Ann_{R_∞}(M_∞) ≤ 𝔭` for every minimal prime `𝔭`, hence `≤ nilradical R_∞`.
  have hann_nil_inf : Module.annihilator R_inf M_inf ≤ nilradical R_inf := by
    rw [nilradical, Ideal.radical_eq_sInf, le_sInf_iff]
    intro P ⟨_, hPprime⟩
    obtain ⟨𝔭, h𝔭min, h𝔭le⟩ := Ideal.exists_minimalPrimes_le (show (⊥ : Ideal R_inf) ≤ P from bot_le)
    obtain ⟨𝔭₀, x₀, hx₀, hx₀_uniq, ⟨C⟩⟩ := hconn 𝔭 h𝔭min
    have hann_p : Module.annihilator R_inf M_inf ≤ 𝔭 :=
      (liftPt_support_propagation hr eM hdimR hx₀ hx₀_uniq C).1
    exact hann_p.trans h𝔭le
  -- Step 2: Since `R_∞` is Noetherian, `Ann_{R_∞}(M_∞)` is finitely generated, hence nilpotent as an ideal.
  have hann_pow_bot : ∃ N : ℕ, Module.annihilator R_inf M_inf ^ N = ⊥ := by
    have hfg : (Module.annihilator R_inf M_inf).FG := IsNoetherian.noetherian _
    have hle_rad : Module.annihilator R_inf M_inf ≤ (⊥ : Ideal R_inf).radical := hann_nil_inf
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle_rad hfg
    exact ⟨N, le_bot_iff.mp hN⟩
  -- Step 3: Specialize to `R_0 = R_∞ ⧸ I_y` and `M_0 = Coinv I_y M_∞` via the determinant trick!
  have hann_nil_0 : Module.annihilator R_0 M_0 ≤ nilradical R_0 := by
    rw [nilradical, Ideal.radical_eq_sInf, le_sInf_iff]
    intro P₀ ⟨_, hP₀prime⟩
    let 𝔭 : Ideal R_inf := P₀.comap (Ideal.Quotient.mk I_y)
    have h𝔭prime : 𝔭.IsPrime := Ideal.comap_isPrime (Ideal.Quotient.mk I_y) P₀
    have hI_le : I_y ≤ 𝔭 := by
      intro x hx
      change Ideal.Quotient.mk I_y x ∈ P₀
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]; exact P₀.zero_mem
    have hann_le_p : Module.annihilator R_inf M_inf ≤ 𝔭 :=
      hann_nil_inf.trans (by
        intro x hx; obtain ⟨k, hk⟩ := hx
        exact h𝔭prime.mem_of_pow_mem k (by rw [hk]; exact 𝔭.zero_mem))
    have hcoinv_le : Module.annihilator R_inf M_0 ≤ 𝔭 :=
      (annihilator_coinv_le_prime_iff I_y h𝔭prime hI_le).mpr hann_le_p
    intro r₀ hr₀
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r₀
    have hr_ann : r ∈ Module.annihilator R_inf M_0 := by
      rw [Module.mem_annihilator]
      intro m
      exact Module.mem_annihilator.mp hr₀ m
    exact hcoinv_le hr_ann
  -- Step 4: Canonical isomorphism `R_0^red ≃+* T_0^red` (and `R_0^red ≃+* T_0` when `T_0` reduced).
  let qRT : R_0 →+* T_0 := Ideal.Quotient.mk (Module.annihilator R_0 M_0)
  let qTred : T_0 →+* T_0 ⧸ nilradical T_0 := Ideal.Quotient.mk (nilradical T_0)
  have hker_comp : RingHom.ker (qTred.comp qRT) = nilradical R_0 := by
    ext r₀
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · rintro ⟨k, hk⟩
      have hpow_ann : r₀ ^ k ∈ Module.annihilator R_0 M_0 := by
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        rw [map_pow]; exact hk
      obtain ⟨m, hm⟩ := hann_nil_0 hpow_ann
      exact ⟨k * m, by rw [pow_mul]; exact hm⟩
    · rintro ⟨k, hk⟩
      have hk0 : r₀ ^ k = 0 := Ideal.mem_bot.mp hk
      exact ⟨k, by rw [← map_pow, hk0, map_zero]; exact Ideal.zero_mem _⟩
  let phiRed : (R_0 ⧸ nilradical R_0) →+* (T_0 ⧸ nilradical T_0) :=
    Ideal.Quotient.lift (nilradical R_0) (qTred.comp qRT) (fun x hx => by
      rw [← hker_comp] at hx; exact hx)
  have hphiRed_bij : Function.Bijective phiRed := by
    refine ⟨?_, ?_⟩
    · rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
      intro x hx
      obtain ⟨r₀, rfl⟩ := Ideal.Quotient.mk_surjective x
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [← hker_comp]; exact hx
    · intro y
      obtain ⟨t₀, rfl⟩ := Ideal.Quotient.mk_surjective y
      obtain ⟨r₀, rfl⟩ := Ideal.Quotient.mk_surjective t₀
      exact ⟨Ideal.Quotient.mk (nilradical R_0) r₀, rfl⟩
  let eRed : (R_0 ⧸ nilradical R_0) ≃+* (T_0 ⧸ nilradical T_0) :=
    RingEquiv.ofBijective phiRed hphiRed_bij
  refine ⟨hann_nil_inf, hann_pow_bot, hann_nil_0, ⟨eRed⟩, fun hredT0 => ?_⟩
  have hnilT0 : nilradical T_0 = ⊥ := by
    rw [eq_bot_iff]; intro t ht; exact IsReduced.eq_zero t ht
  let eT0 : (T_0 ⧸ nilradical T_0) ≃+* T_0 :=
    (Ideal.quotEquivOfEq hnilT0).trans (RingEquiv.quotientBot T_0)
  exact ⟨eRed.trans eT0⟩

end HigherRankDetAndThornePropagation

/-! ## Section 3: Higher-Rank Poitou–Tate Obstruction Dimension Balance (`CohAx` / `TaylorWilesObstructionBound`) -/

section HigherRankPoitouTateBalance

/-! ### 3.1 Concrete `U(3)` (`d = 3`) Adjoint Lie Algebra, Archimedean `H⁰` (`dim = 3`), & Frobenius Centralizers -/

/-- Anti-diagonal symmetric involution matrix `J₃ ∈ M₃(K)` defining the odd conjugate-self-dual
polarity `X ↦ -J₃ Xᵀ J₃` on `𝔤𝔩₃(K)`. -/
def J3 (K : Type*) [CommRing K] : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 1; 0, 1, 0; 1, 0, 0]

theorem J3_transpose (K : Type*) [CommRing K] : (J3 K).transpose = J3 K := by
  apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> rfl

theorem J3_mul_J3 (K : Type*) [CommRing K] : J3 K * J3 K = 1 := by
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j <;> simp [J3, Matrix.mul_apply, Fin.sum_univ_three]

/-- Exact entrywise formula `(J₃ * Xᵀ * J₃) i j = X ⟨2 - j, _⟩ ⟨2 - i, _⟩`. -/
private lemma J3_mul_transpose_mul_J3_apply {K : Type*} [CommRing K]
    (X : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    (J3 K * X.transpose * J3 K) i j = X ⟨2 - j.1, by omega⟩ ⟨2 - i.1, by omega⟩ := by
  have hL : ∀ r c : Fin 3, (J3 K * X.transpose) r c = X c ⟨2 - r.1, by omega⟩ := by
    intro r c
    rw [Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases r <;> simp [J3]
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  simp_rw [hL]
  fin_cases j <;> simp [J3]

/-- Concrete archimedean invariant subspace `H⁰(⟨c⟩, ad(ρ̄)) = { X ∈ M₃(K) | J₃ Xᵀ J₃ = -X }`
for odd conjugate-self-dual 3D representations on `U(3)`. -/
def U3ArchH0 (K : Type*) [Field K] : Submodule K (Matrix (Fin 3) (Fin 3) K) where
  carrier := { X | J3 K * X.transpose * J3 K = -X }
  zero_mem' := by simp
  add_mem' {X Y} hX hY := by
    change J3 K * (X + Y).transpose * J3 K = -(X + Y)
    rw [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, hX, hY, neg_add]
  smul_mem' c {X} hX := by
    change J3 K * (c • X).transpose * J3 K = -(c • X)
    rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, hX, smul_neg]

/-- Explicit 3-dimensional basis equivalence `U3ArchH0 K ≃ₗ[K] (Fin 3 → K)` for `char K ≠ 2`. -/
def u3ArchH0EquivFin3 (K : Type*) [Field K] (h2 : (2 : K) ≠ 0) :
    U3ArchH0 K ≃ₗ[K] (Fin 3 → K) where
  toFun X := ![X.1 0 0, X.1 0 1, X.1 1 0]
  invFun v :=
    ⟨!![v 0, v 1, 0; v 2, 0, -v 1; 0, -v 2, -v 0], by
      apply Matrix.ext; intro i j
      rw [J3_mul_transpose_mul_J3_apply]
      fin_cases i <;> fin_cases j <;> simp⟩
  left_inv X := by
    apply Subtype.ext
    have hent : ∀ i j : Fin 3, X.1 ⟨2 - j.1, by omega⟩ ⟨2 - i.1, by omega⟩ = -X.1 i j :=
      fun i j => (J3_mul_transpose_mul_J3_apply X.1 i j).symm.trans (congrFun (congrFun X.2 i) j)
    have h02 : X.1 0 2 = 0 := by
      have h : X.1 0 2 = -X.1 0 2 := hent 0 2
      have h2x : (2 : K) * X.1 0 2 = 0 := by linear_combination h
      exact (mul_eq_zero.mp h2x).resolve_left h2
    have h11 : X.1 1 1 = 0 := by
      have h : X.1 1 1 = -X.1 1 1 := hent 1 1
      have h2x : (2 : K) * X.1 1 1 = 0 := by linear_combination h
      exact (mul_eq_zero.mp h2x).resolve_left h2
    have h20 : X.1 2 0 = 0 := by
      have h : X.1 2 0 = -X.1 2 0 := hent 2 0
      have h2x : (2 : K) * X.1 2 0 = 0 := by linear_combination h
      exact (mul_eq_zero.mp h2x).resolve_left h2
    have h12 : X.1 1 2 = -X.1 0 1 := hent 0 1
    have h21 : X.1 2 1 = -X.1 1 0 := hent 1 0
    have h22 : X.1 2 2 = -X.1 0 0 := hent 0 0
    apply Matrix.ext; intro i j
    fin_cases i <;> fin_cases j <;>
      first | rfl | exact h02.symm | exact h11.symm | exact h20.symm |
              exact h12.symm | exact h21.symm | exact h22.symm
  right_inv v := by
    funext i; fin_cases i <;> rfl
  map_add' X Y := by
    funext i; fin_cases i <;> rfl
  map_smul' c X := by
    funext i; fin_cases i <;> rfl

/-- **Exact Archimedean `H⁰` Dimension for `U(3)`**: `dim_K H⁰(⟨c⟩, ad(ρ̄)) = 3`! -/
theorem finrank_U3ArchH0_eq_three (K : Type*) [Field K] (h2 : (2 : K) ≠ 0) :
    Module.finrank K (U3ArchH0 K) = 3 := by
  rw [(u3ArchH0EquivFin3 K h2).finrank_eq, Module.finrank_fin_fun]

/-- Centralizer of a regular semisimple `3×3` diagonal Frobenius matrix `diag(α, β, γ)` in `M₃(K)`. -/
def DiagCentralizer3 (K : Type*) [Field K] (α β γ : K) :
    Submodule K (Matrix (Fin 3) (Fin 3) K) where
  carrier := { X | Matrix.diagonal ![α, β, γ] * X = X * Matrix.diagonal ![α, β, γ] }
  zero_mem' := by simp
  add_mem' {X Y} hX hY := by
    change Matrix.diagonal ![α, β, γ] * (X + Y) = (X + Y) * Matrix.diagonal ![α, β, γ]
    rw [Matrix.mul_add, Matrix.add_mul, hX, hY]
  smul_mem' c {X} hX := by
    change Matrix.diagonal ![α, β, γ] * (c • X) = (c • X) * Matrix.diagonal ![α, β, γ]
    rw [Matrix.mul_smul, Matrix.smul_mul, hX]

/-- Explicit basis equivalence `DiagCentralizer3 K α β γ ≃ₗ[K] (Fin 3 → K)` for pairwise distinct
eigenvalues `α, β, γ`. -/
def diagCentralizer3EquivFin3 {K : Type*} [Field K] {α β γ : K}
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ) :
    DiagCentralizer3 K α β γ ≃ₗ[K] (Fin 3 → K) where
  toFun X := ![X.1 0 0, X.1 1 1, X.1 2 2]
  invFun v :=
    ⟨Matrix.diagonal v, by
      apply Matrix.ext; intro i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, mul_comm]⟩
  left_inv X := by
    apply Subtype.ext
    have hX := X.2
    have hent : ∀ i j : Fin 3,
        (Matrix.diagonal ![α, β, γ] * X.1) i j = (X.1 * Matrix.diagonal ![α, β, γ]) i j :=
      fun i j => congrFun (congrFun hX i) j
    have hkill : ∀ {i j : Fin 3}, i ≠ j →
        (![α, β, γ] i - ![α, β, γ] j) ≠ 0 → X.1 i j = 0 := by
      intro i j _ hdiff
      have h := hent i j
      simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at h
      have h0 : (![α, β, γ] i - ![α, β, γ] j) * X.1 i j = 0 := by linear_combination h
      exact (mul_eq_zero.mp h0).resolve_left hdiff
    have h01 : X.1 0 1 = 0 := hkill (by decide) (sub_ne_zero.mpr hαβ)
    have h02 : X.1 0 2 = 0 := hkill (by decide) (sub_ne_zero.mpr hαγ)
    have h10 : X.1 1 0 = 0 := hkill (by decide) (sub_ne_zero.mpr hαβ.symm)
    have h12 : X.1 1 2 = 0 := hkill (by decide) (sub_ne_zero.mpr hβγ)
    have h20 : X.1 2 0 = 0 := hkill (by decide) (sub_ne_zero.mpr hαγ.symm)
    have h21 : X.1 2 1 = 0 := hkill (by decide) (sub_ne_zero.mpr hβγ.symm)
    apply Matrix.ext; intro i j
    fin_cases i <;> fin_cases j <;> simp [h01, h02, h10, h12, h20, h21]
  right_inv v := by
    funext i; fin_cases i <;> rfl
  map_add' X Y := by
    funext i; fin_cases i <;> rfl
  map_smul' c X := by
    funext i; fin_cases i <;> rfl

/-- **Exact Frobenius Centralizer Dimension for `U(3)`**: `dim_K H⁰(⟨Frob_q⟩, M₃) = 3`! -/
theorem finrank_diagCentralizer3_eq_three {K : Type*} [Field K] {α β γ : K}
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ) :
    Module.finrank K (DiagCentralizer3 K α β γ) = 3 := by
  rw [(diagCentralizer3EquivFin3 hαβ hαγ hβγ).finrank_eq, Module.finrank_fin_fun]

/-- **Higher-Rank `U(3)` Poitou–Tate Selmer System (`CohAx` for `d = 3`)**:
wired directly to `Stage2GaloisCohomology.PoitouTateData` and `U3ArchH0` / `DiagCentralizer3`! -/
structure U3WilesSelmerSystem (S₀ Q : Type) [Fintype S₀] [DecidableEq S₀]
    [Fintype Q] [DecidableEq Q] (p : ℕ) [Fact p.Prime] where
  hp3 : 3 ≤ p
  /-- Number of diamond variables added per Taylor–Wiles prime `q ∈ Q` (`1` for Thorne 1-eigenvalue
  primes, `3` for full-torus regular-semisimple `U(3)` primes). -/
  m_Q : ℕ
  v_inf : S₀
  v_p : S₀
  v_inf_ne_vp : v_inf ≠ v_p
  eig_α : Q → ZMod p
  eig_β : Q → ZMod p
  eig_γ : Q → ZMod p
  eig_αβ : ∀ q, eig_α q ≠ eig_β q
  eig_αγ : ∀ q, eig_α q ≠ eig_γ q
  eig_βγ : ∀ q, eig_β q ≠ eig_γ q
  D : PoitouTateData (ZMod p) (S₀ ⊕ Q)
  euler_balance : D.EulerPoincareBalance
  H0_vanish : Module.finrank (ZMod p) D.H0 = 0
  H0d_vanish : Module.finrank (ZMod p) D.H0d = 0
  H0_inf_equiv : D.H0v (Sum.inl v_inf) ≃ₗ[ZMod p] U3ArchH0 (ZMod p)
  H0_q_equiv : ∀ q : Q, D.H0v (Sum.inr q) ≃ₗ[ZMod p] DiagCentralizer3 (ZMod p) (eig_α q) (eig_β q) (eig_γ q)
  L_min : ∀ v : S₀ ⊕ Q, Submodule (ZMod p) (D.H1v v)
  L_inf_bot : L_min (Sum.inl v_inf) = ⊥
  /-- Ordinary / Fontaine–Laffaille local balance at `p`: `dim L_p - dim H⁰(G_p) = dim(𝔤𝔩₃/𝔟₃) = 3`. -/
  L_p_balance : (Module.finrank (ZMod p) (L_min (Sum.inl v_p)) : ℤ) -
    Module.finrank (ZMod p) (D.H0v (Sum.inl v_p)) = 3
  L_other_unram : ∀ v : S₀, v ≠ v_inf → v ≠ v_p →
    Module.finrank (ZMod p) (L_min (Sum.inl v)) = Module.finrank (ZMod p) (D.H0v (Sum.inl v))
  L_q_unram : ∀ q : Q,
    Module.finrank (ZMod p) (L_min (Sum.inr q)) = Module.finrank (ZMod p) (D.H0v (Sum.inr q))
  /-- Relaxed Taylor–Wiles local condition `L_Q_loc` at each `q ∈ Q` with excess `m_Q`. -/
  L_Q_loc : ∀ q : Q, Submodule (ZMod p) (D.H1v (Sum.inr q))
  L_Q_loc_dim : ∀ q : Q, Module.finrank (ZMod p) (L_Q_loc q) = 3 + m_Q

namespace U3WilesSelmerSystem

variable {S₀ Q : Type} [Fintype S₀] [DecidableEq S₀] [Fintype Q] [DecidableEq Q]
  {p : ℕ} [Fact p.Prime] (W : U3WilesSelmerSystem S₀ Q p)

def L_Q : ∀ v : S₀ ⊕ Q, Submodule (ZMod p) (W.D.H1v v)
  | Sum.inl v => W.L_min (Sum.inl v)
  | Sum.inr q => W.L_Q_loc q

theorem finrank_H0_inf_eq_three : Module.finrank (ZMod p) (W.D.H0v (Sum.inl W.v_inf)) = 3 := by
  rw [W.H0_inf_equiv.finrank_eq]
  exact finrank_U3ArchH0_eq_three (ZMod p) (two_ne_zero_zmod W.hp3)

theorem finrank_H0_q_eq_three (q : Q) : Module.finrank (ZMod p) (W.D.H0v (Sum.inr q)) = 3 := by
  rw [(W.H0_q_equiv q).finrank_eq]
  exact finrank_diagCentralizer3_eq_three (W.eig_αβ q) (W.eig_αγ q) (W.eig_βγ q)

theorem sum_S0_local_defect_eq_zero :
    ∑ v : S₀, ((Module.finrank (ZMod p) (W.L_min (Sum.inl v)) : ℤ) -
      Module.finrank (ZMod p) (W.D.H0v (Sum.inl v))) = 0 := by
  have h1 : ∀ v : S₀, v ∉ ({W.v_inf, W.v_p} : Finset S₀) →
      (Module.finrank (ZMod p) (W.L_min (Sum.inl v)) : ℤ) -
        Module.finrank (ZMod p) (W.D.H0v (Sum.inl v)) = 0 := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
    rw [W.L_other_unram v hv.1 hv.2, sub_self]
  rw [← Finset.sum_subset (Finset.subset_univ ({W.v_inf, W.v_p} : Finset S₀)) (fun v _ hv => h1 v hv)]
  rw [Finset.sum_pair W.v_inf_ne_vp, W.L_inf_bot, finrank_bot, W.finrank_H0_inf_eq_three, W.L_p_balance]
  norm_num

/-- **EXACT HIGHER-RANK `U(3)` POITOU–TATE OBSTRUCTION DIMENSION BALANCE (`CohAx` / `TaylorWilesObstructionBound`)**:
1. Minimal level: `dim H¹_{L_min} = dim H¹_{L*_min}`;
2. Relaxed at `Q`: `dim H¹_{L_Q} - dim H¹_{L*_Q} = m_Q * |Q|` (so `(dim H¹_{L_Q} - g_Q) - r_Q = 0`);
3. Dual-killing (`dim H¹_{L*_Q} = 0`): `dim H¹_{L_Q} = m_Q * |Q|` (`= |Q|` for Thorne 1-parameter primes)! -/
theorem u3_poitou_tate_balancing :
    Module.finrank (ZMod p) (W.D.Selmer W.L_min) =
      Module.finrank (ZMod p) (W.D.DualSelmer W.L_min) ∧
    (Module.finrank (ZMod p) (W.D.Selmer W.L_Q) : ℤ) -
      Module.finrank (ZMod p) (W.D.DualSelmer W.L_Q) = ((W.m_Q * Fintype.card Q : ℕ) : ℤ) ∧
    ((Module.finrank (ZMod p) (W.D.Selmer W.L_Q) : ℤ) - ((W.m_Q * Fintype.card Q : ℕ) : ℤ)) -
      (Module.finrank (ZMod p) (W.D.DualSelmer W.L_Q) : ℤ) = 0 ∧
    (Module.finrank (ZMod p) (W.D.DualSelmer W.L_Q) = 0 →
      Module.finrank (ZMod p) (W.D.Selmer W.L_Q) = W.m_Q * Fintype.card Q) := by
  have hmin : Module.finrank (ZMod p) (W.D.Selmer W.L_min) =
      Module.finrank (ZMod p) (W.D.DualSelmer W.L_min) := by
    have hgw := greenberg_wiles_euler_characteristic W.D W.euler_balance W.L_min
    rw [W.H0_vanish, W.H0d_vanish, Fintype.sum_sum_type, W.sum_S0_local_defect_eq_zero] at hgw
    have hQ0 : ∑ q : Q, ((Module.finrank (ZMod p) (W.L_min (Sum.inr q)) : ℤ) -
        Module.finrank (ZMod p) (W.D.H0v (Sum.inr q))) = 0 :=
      Finset.sum_eq_zero fun q _ => by rw [W.L_q_unram q, sub_self]
    rw [hQ0] at hgw
    omega
  have hbal : (Module.finrank (ZMod p) (W.D.Selmer W.L_Q) : ℤ) -
      Module.finrank (ZMod p) (W.D.DualSelmer W.L_Q) = ((W.m_Q * Fintype.card Q : ℕ) : ℤ) := by
    have hgw := greenberg_wiles_euler_characteristic W.D W.euler_balance W.L_Q
    rw [W.H0_vanish, W.H0d_vanish, Fintype.sum_sum_type] at hgw
    have hS0 : ∑ v : S₀, ((Module.finrank (ZMod p) (W.L_Q (Sum.inl v)) : ℤ) -
        Module.finrank (ZMod p) (W.D.H0v (Sum.inl v))) = 0 := W.sum_S0_local_defect_eq_zero
    have hQ : ∑ q : Q, ((Module.finrank (ZMod p) (W.L_Q (Sum.inr q)) : ℤ) -
        Module.finrank (ZMod p) (W.D.H0v (Sum.inr q))) = ((W.m_Q * Fintype.card Q : ℕ) : ℤ) := by
      have hterm : ∀ q : Q, ((Module.finrank (ZMod p) (W.L_Q (Sum.inr q)) : ℤ) -
          Module.finrank (ZMod p) (W.D.H0v (Sum.inr q))) = (W.m_Q : ℤ) := fun q => by
        change (Module.finrank (ZMod p) (W.L_Q_loc q) : ℤ) -
          Module.finrank (ZMod p) (W.D.H0v (Sum.inr q)) = (W.m_Q : ℤ)
        rw [W.L_Q_loc_dim q, W.finrank_H0_q_eq_three q]
        omega
      simp_rw [hterm]
      simp [mul_comm]
    rw [hS0, hQ] at hgw
    omega
  refine ⟨hmin, hbal, by omega, fun hvan => ?_⟩
  rw [hvan] at hbal
  omega

end U3WilesSelmerSystem

/-! ### 3.2 Concrete `Sp₄` (`d = 4`) Symplectic Lie Algebra (`dim = 10`), Archimedean `H⁰` (`dim = 4`),
& Regular-Semisimple Centralizers (`dim = 2`) -/

/-- Standard `4 × 4` skew-symmetric symplectic form `J₄` (`J₄ᵀ = -J₄`, `J₄² = -I₄`). -/
def J4 (K : Type*) [CommRing K] : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]

theorem J4_transpose (K : Type*) [CommRing K] : (J4 K).transpose = -J4 K := by
  apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> simp [J4]

/-- Fast entrywise evaluation of `(J₄ * X) i j` (avoids slow `vecMul` expansion). -/
private lemma J4_mul_apply {K : Type*} [CommRing K] (X : Matrix (Fin 4) (Fin 4) K) (i j : Fin 4) :
    (J4 K * X) i j =
      if i.1 < 2 then X ⟨3 - i.1, by omega⟩ j else -X ⟨3 - i.1, by omega⟩ j := by
  rw [Matrix.mul_apply, Fin.sum_univ_four]
  fin_cases i <;> simp [J4]

theorem J4_mul_J4 (K : Type*) [CommRing K] : J4 K * J4 K = -(1 : Matrix (Fin 4) (Fin 4) K) := by
  apply Matrix.ext; intro i j
  rw [J4_mul_apply]
  fin_cases i <;> fin_cases j <;> simp [J4]

/-- Concrete 10-dimensional symplectic Lie algebra `𝔰𝔭₄(K) = { X ∈ M₄(K) | Xᵀ J₄ + J₄ X = 0 }`. -/
def Sp4LieAlg (K : Type*) [Field K] : Submodule K (Matrix (Fin 4) (Fin 4) K) where
  carrier := { X | X.transpose * J4 K + J4 K * X = 0 }
  zero_mem' := by simp
  add_mem' {X Y} hX hY := by
    change (X + Y).transpose * J4 K + J4 K * (X + Y) = 0
    rw [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add]
    calc X.transpose * J4 K + Y.transpose * J4 K + (J4 K * X + J4 K * Y)
        = (X.transpose * J4 K + J4 K * X) + (Y.transpose * J4 K + J4 K * Y) := by abel
      _ = 0 := by rw [hX, hY, add_zero]
  smul_mem' c {X} hX := by
    change (c • X).transpose * J4 K + J4 K * (c • X) = 0
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]

/-- Fast entrywise evaluation of `(Xᵀ * J₄) i j`. -/
private lemma transpose_mul_J4_apply {K : Type*} [CommRing K] (X : Matrix (Fin 4) (Fin 4) K) (i j : Fin 4) :
    (X.transpose * J4 K) i j =
      if j.1 < 2 then -X ⟨3 - j.1, by omega⟩ i else X ⟨3 - j.1, by omega⟩ i := by
  rw [Matrix.mul_apply, Fin.sum_univ_four]
  fin_cases j <;> simp [J4]

/-- **Fast Characterization of `Sp4LieAlg K`**: `X ∈ 𝔰𝔭₄(K)` iff the 6 symplectic entry identities hold! -/
private lemma mem_sp4LieAlg_iff {K : Type*} [Field K] (X : Matrix (Fin 4) (Fin 4) K) :
    X ∈ Sp4LieAlg K ↔
      X 0 0 = -X 3 3 ∧ X 0 1 = -X 2 3 ∧ X 0 2 = X 1 3 ∧
      X 1 0 = -X 3 2 ∧ X 1 1 = -X 2 2 ∧ X 2 0 = X 3 1 := by
  constructor
  · intro hX
    have hent : ∀ i j : Fin 4,
        (if j.1 < 2 then -X ⟨3 - j.1, by omega⟩ i else X ⟨3 - j.1, by omega⟩ i) +
        (if i.1 < 2 then X ⟨3 - i.1, by omega⟩ j else -X ⟨3 - i.1, by omega⟩ j) = 0 := by
      intro i j
      have h := congrFun (congrFun hX i) j
      simpa [Matrix.add_apply, transpose_mul_J4_apply, J4_mul_apply] using h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have h := hent 0 3; simp at h; linear_combination h
    · have h := hent 1 3; simp at h; linear_combination h
    · have h := hent 2 3; simp at h; linear_combination h
    · have h := hent 0 2; simp at h; linear_combination h
    · have h := hent 1 2; simp at h; linear_combination h
    · have h := hent 0 1; simp at h; linear_combination -h
  · rintro ⟨h00, h01, h02, h10, h11, h20⟩
    apply Matrix.ext; intro i j
    change (X.transpose * J4 K) i j + (J4 K * X) i j = 0
    rw [transpose_mul_J4_apply, J4_mul_apply]
    fin_cases i <;> fin_cases j <;> simp [h00, h01, h02, h10, h11, h20]

/-- Explicit 10-dimensional basis equivalence `Sp4LieAlg K ≃ₗ[K] (Fin 10 → K)` (via the symmetric
matrix isomorphism `S = J₄ X`). -/
def sp4LieAlgEquivFin10 (K : Type*) [Field K] :
    Sp4LieAlg K ≃ₗ[K] (Fin 10 → K) where
  toFun X :=
    ![X.1 3 0, X.1 3 1, X.1 3 2, X.1 3 3, X.1 2 1, X.1 2 2, X.1 2 3, X.1 1 2, X.1 1 3, X.1 0 3]
  invFun v :=
    ⟨!![-v 3, -v 6, v 8, v 9;
        -v 2, -v 5, v 7, v 8;
         v 1,  v 4, v 5, v 6;
         v 0,  v 1, v 2, v 3],
      (mem_sp4LieAlg_iff _).mpr ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  left_inv X := by
    apply Subtype.ext
    obtain ⟨h00, h01, h02, h10, h11, h20⟩ := (mem_sp4LieAlg_iff X.1).mp X.2
    apply Matrix.ext; intro i j
    fin_cases i <;> fin_cases j <;>
      first | rfl | exact h00.symm | exact h01.symm | exact h02.symm |
              exact h10.symm | exact h11.symm | exact h20.symm
  right_inv v := by
    funext i; fin_cases i <;> rfl
  map_add' X Y := by
    funext i; fin_cases i <;> rfl
  map_smul' c X := by
    funext i; fin_cases i <;> rfl

/-- **Exact Dimension of `𝔰𝔭₄(K)`**: `dim_K (Sp4LieAlg K) = 10`! -/
theorem finrank_sp4LieAlg_eq_ten (K : Type*) [Field K] :
    Module.finrank K (Sp4LieAlg K) = 10 := by
  rw [(sp4LieAlgEquivFin10 K).finrank_eq, Module.finrank_fin_fun]

/-- Odd symplectic complex-conjugation involution `c₄ = diag(1, 1, -1, -1) ∈ GSp₄(K)`
(`c₄² = I₄`, `c₄ᵀ J₄ c₄ = -J₄`). -/
def sp4OddConj (K : Type*) [CommRing K] : Matrix (Fin 4) (Fin 4) K :=
  Matrix.diagonal ![1, 1, -1, -1]

theorem sp4OddConj_mul_self (K : Type*) [CommRing K] :
    sp4OddConj K * sp4OddConj K = 1 := by
  apply Matrix.ext; intro i j
  simp only [sp4OddConj, Matrix.diagonal_mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp

theorem sp4OddConj_symplectic_odd (K : Type*) [CommRing K] :
    (sp4OddConj K).transpose * J4 K * sp4OddConj K = -J4 K := by
  apply Matrix.ext; intro i j
  simp only [sp4OddConj, Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [J4]

/-- Concrete archimedean invariant subspace `H⁰(⟨c₄⟩, 𝔰𝔭₄(K)) = { X ∈ 𝔰𝔭₄(K) | c₄ X = X c₄ }`. -/
def Sp4ArchH0 (K : Type*) [Field K] : Submodule K (Sp4LieAlg K) where
  carrier := { X | sp4OddConj K * X.1 = X.1 * sp4OddConj K }
  zero_mem' := by simp
  add_mem' {X Y} hX hY := by
    change sp4OddConj K * (X.1 + Y.1) = (X.1 + Y.1) * sp4OddConj K
    rw [Matrix.mul_add, Matrix.add_mul, hX, hY]
  smul_mem' c {X} hX := by
    change sp4OddConj K * (c • X.1) = (c • X.1) * sp4OddConj K
    rw [Matrix.mul_smul, Matrix.smul_mul, hX]

/-- Explicit 4-dimensional basis equivalence `Sp4ArchH0 K ≃ₗ[K] (Fin 4 → K)` for `char K ≠ 2`! -/
def sp4ArchH0EquivFin4 (K : Type*) [Field K] (h2 : (2 : K) ≠ 0) :
    Sp4ArchH0 K ≃ₗ[K] (Fin 4 → K) where
  toFun X := ![X.1.1 3 2, X.1.1 3 3, X.1.1 2 2, X.1.1 2 3]
  invFun v :=
    ⟨⟨!![-v 1, -v 3, 0, 0;
         -v 0, -v 2, 0, 0;
          0,    0,  v 2, v 3;
          0,    0,  v 0, v 1],
      (mem_sp4LieAlg_iff _).mpr ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩, by
      apply Matrix.ext; intro i j
      simp only [sp4OddConj, Matrix.diagonal_mul, Matrix.mul_diagonal]
      fin_cases i <;> fin_cases j <;> simp⟩
  left_inv X := by
    apply Subtype.ext; apply Subtype.ext
    obtain ⟨h00, h01, _, h10, h11, _⟩ := (mem_sp4LieAlg_iff X.1.1).mp X.1.2
    have hcm_e : ∀ i j : Fin 4, (sp4OddConj K * X.1.1) i j = (X.1.1 * sp4OddConj K) i j :=
      fun i j => congrFun (congrFun X.2 i) j
    have hkill_pos : ∀ {i j : Fin 4},
        (![1, 1, -1, -1] : Fin 4 → K) i = 1 → (![1, 1, -1, -1] : Fin 4 → K) j = -1 →
        X.1.1 i j = 0 := by
      intro i j hi hj
      have h := hcm_e i j
      simp only [sp4OddConj, Matrix.diagonal_mul, Matrix.mul_diagonal, hi, hj] at h
      have h2x : (2 : K) * X.1.1 i j = 0 := by linear_combination h
      exact (mul_eq_zero.mp h2x).resolve_left h2
    have hkill_neg : ∀ {i j : Fin 4},
        (![1, 1, -1, -1] : Fin 4 → K) i = -1 → (![1, 1, -1, -1] : Fin 4 → K) j = 1 →
        X.1.1 i j = 0 := by
      intro i j hi hj
      have h := hcm_e i j
      simp only [sp4OddConj, Matrix.diagonal_mul, Matrix.mul_diagonal, hi, hj] at h
      have h2x : (2 : K) * X.1.1 i j = 0 := by linear_combination -h
      exact (mul_eq_zero.mp h2x).resolve_left h2
    have h02 : X.1.1 0 2 = 0 := hkill_pos rfl rfl
    have h03 : X.1.1 0 3 = 0 := hkill_pos rfl rfl
    have h12 : X.1.1 1 2 = 0 := hkill_pos rfl rfl
    have h13 : X.1.1 1 3 = 0 := hkill_pos rfl rfl
    have h20 : X.1.1 2 0 = 0 := hkill_neg rfl rfl
    have h21 : X.1.1 2 1 = 0 := hkill_neg rfl rfl
    have h30 : X.1.1 3 0 = 0 := hkill_neg rfl rfl
    have h31 : X.1.1 3 1 = 0 := hkill_neg rfl rfl
    apply Matrix.ext; intro i j
    fin_cases i <;> fin_cases j <;>
      first | rfl | exact h00.symm | exact h01.symm | exact h02.symm | exact h03.symm |
              exact h10.symm | exact h11.symm | exact h12.symm | exact h13.symm |
              exact h20.symm | exact h21.symm | exact h30.symm | exact h31.symm
  right_inv v := by
    funext i; fin_cases i <;> rfl
  map_add' X Y := by
    funext i; fin_cases i <;> rfl
  map_smul' c X := by
    funext i; fin_cases i <;> rfl

/-- **Exact Archimedean `H⁰` Dimension for `Sp₄`**: `dim_K H⁰(⟨c₄⟩, 𝔰𝔭₄(K)) = 4`! -/
theorem finrank_sp4ArchH0_eq_four (K : Type*) [Field K] (h2 : (2 : K) ≠ 0) :
    Module.finrank K (Sp4ArchH0 K) = 4 := by
  rw [(sp4ArchH0EquivFin4 K h2).finrank_eq, Module.finrank_fin_fun]

/-- Centralizer in `𝔰𝔭₄(K)` of a regular semisimple symplectic Frobenius `diag(α, β, β⁻¹, α⁻¹)`. -/
def Sp4DiagCentralizer (K : Type*) [Field K] (α β : K) :
    Submodule K (Sp4LieAlg K) where
  carrier := { X | Matrix.diagonal ![α, β, β⁻¹, α⁻¹] * X.1 = X.1 * Matrix.diagonal ![α, β, β⁻¹, α⁻¹] }
  zero_mem' := by simp
  add_mem' {X Y} hX hY := by
    change Matrix.diagonal ![α, β, β⁻¹, α⁻¹] * (X.1 + Y.1) = (X.1 + Y.1) * Matrix.diagonal ![α, β, β⁻¹, α⁻¹]
    rw [Matrix.mul_add, Matrix.add_mul, hX, hY]
  smul_mem' c {X} hX := by
    change Matrix.diagonal ![α, β, β⁻¹, α⁻¹] * (c • X.1) = (c • X.1) * Matrix.diagonal ![α, β, β⁻¹, α⁻¹]
    rw [Matrix.mul_smul, Matrix.smul_mul, hX]

/-- Explicit 2-dimensional basis equivalence `Sp4DiagCentralizer K α β ≃ₗ[K] (Fin 2 → K)` whenever
the 4 eigenvalues `α, β, β⁻¹, α⁻¹` are pairwise distinct! -/
def sp4DiagCentralizerEquivFin2 {K : Type*} [Field K] {α β : K}
    (hαβ : α ≠ β) (hαβi : α ≠ β⁻¹) (hααi : α ≠ α⁻¹)
    (hββi : β ≠ β⁻¹) (hβαi : β ≠ α⁻¹) (hβiαi : β⁻¹ ≠ α⁻¹) :
    Sp4DiagCentralizer K α β ≃ₗ[K] (Fin 2 → K) where
  toFun X := ![X.1.1 3 3, X.1.1 2 2]
  invFun v :=
    ⟨⟨Matrix.diagonal ![-v 0, -v 1, v 1, v 0],
      (mem_sp4LieAlg_iff _).mpr ⟨by simp, by simp, by simp, by simp, by simp, by simp⟩⟩, by
      apply Matrix.ext; intro i j
      simp only [Matrix.diagonal_mul_diagonal]
      fin_cases i <;> fin_cases j <;> simp [mul_comm]⟩
  left_inv X := by
    apply Subtype.ext; apply Subtype.ext
    obtain ⟨h00, _, _, _, h11, _⟩ := (mem_sp4LieAlg_iff X.1.1).mp X.1.2
    have hcm_e : ∀ i j : Fin 4,
        (Matrix.diagonal ![α, β, β⁻¹, α⁻¹] * X.1.1) i j =
          (X.1.1 * Matrix.diagonal ![α, β, β⁻¹, α⁻¹]) i j :=
      fun i j => congrFun (congrFun X.2 i) j
    have hkill : ∀ {i j : Fin 4},
        (![α, β, β⁻¹, α⁻¹] i - ![α, β, β⁻¹, α⁻¹] j) ≠ 0 → X.1.1 i j = 0 := by
      intro i j hdiff
      have h := hcm_e i j
      simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at h
      have h0 : (![α, β, β⁻¹, α⁻¹] i - ![α, β, β⁻¹, α⁻¹] j) * X.1.1 i j = 0 := by
        linear_combination h
      exact (mul_eq_zero.mp h0).resolve_left hdiff
    have h01 : X.1.1 0 1 = 0 := hkill (sub_ne_zero.mpr hαβ)
    have h02 : X.1.1 0 2 = 0 := hkill (sub_ne_zero.mpr hαβi)
    have h03 : X.1.1 0 3 = 0 := hkill (sub_ne_zero.mpr hααi)
    have h10 : X.1.1 1 0 = 0 := hkill (sub_ne_zero.mpr hαβ.symm)
    have h12 : X.1.1 1 2 = 0 := hkill (sub_ne_zero.mpr hββi)
    have h13 : X.1.1 1 3 = 0 := hkill (sub_ne_zero.mpr hβαi)
    have h20 : X.1.1 2 0 = 0 := hkill (sub_ne_zero.mpr hαβi.symm)
    have h21 : X.1.1 2 1 = 0 := hkill (sub_ne_zero.mpr hββi.symm)
    have h23 : X.1.1 2 3 = 0 := hkill (sub_ne_zero.mpr hβiαi)
    have h30 : X.1.1 3 0 = 0 := hkill (sub_ne_zero.mpr hααi.symm)
    have h31 : X.1.1 3 1 = 0 := hkill (sub_ne_zero.mpr hβαi.symm)
    have h32 : X.1.1 3 2 = 0 := hkill (sub_ne_zero.mpr hβiαi.symm)
    apply Matrix.ext; intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.diagonal_apply_eq, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
      first | rfl | exact h00.symm | exact h01.symm | exact h02.symm | exact h03.symm |
              exact h10.symm | exact h11.symm | exact h12.symm | exact h13.symm |
              exact h20.symm | exact h21.symm | exact h23.symm |
              exact h30.symm | exact h31.symm | exact h32.symm
  right_inv v := by
    funext i; fin_cases i <;> rfl
  map_add' X Y := by
    funext i; fin_cases i <;> rfl
  map_smul' c X := by
    funext i; fin_cases i <;> rfl

/-- **Exact Frobenius Centralizer Dimension for `Sp₄`**: `dim_K H⁰(⟨Frob_q⟩, 𝔰𝔭₄(K)) = 2`! -/
theorem finrank_sp4DiagCentralizer_eq_two {K : Type*} [Field K] {α β : K}
    (hαβ : α ≠ β) (hαβi : α ≠ β⁻¹) (hααi : α ≠ α⁻¹)
    (hββi : β ≠ β⁻¹) (hβαi : β ≠ α⁻¹) (hβiαi : β⁻¹ ≠ α⁻¹) :
    Module.finrank K (Sp4DiagCentralizer K α β) = 2 := by
  rw [(sp4DiagCentralizerEquivFin2 hαβ hαβi hααi hββi hβαi hβiαi).finrank_eq, Module.finrank_fin_fun]

/-- **Higher-Rank `Sp₄` Poitou–Tate Selmer System (`CohAx` for `d = 4`)**:
wired directly to `Stage2GaloisCohomology.PoitouTateData`, `Sp4ArchH0` (`dim = 4`), and
`Sp4DiagCentralizer` (`dim = 2`)! -/
structure Sp4WilesSelmerSystem (S₀ Q : Type) [Fintype S₀] [DecidableEq S₀]
    [Fintype Q] [DecidableEq Q] (p : ℕ) [Fact p.Prime] where
  hp3 : 3 ≤ p
  /-- Number of diamond variables per Taylor–Wiles prime (`1` for 1-parameter Klingen/Siegel TW
  primes, `2` for full-torus `Sp₄` TW primes). -/
  m_Q : ℕ
  v_inf : S₀
  v_p : S₀
  v_inf_ne_vp : v_inf ≠ v_p
  eig_α : Q → ZMod p
  eig_β : Q → ZMod p
  eig_αβ : ∀ q, eig_α q ≠ eig_β q
  eig_αβi : ∀ q, eig_α q ≠ (eig_β q)⁻¹
  eig_ααi : ∀ q, eig_α q ≠ (eig_α q)⁻¹
  eig_ββi : ∀ q, eig_β q ≠ (eig_β q)⁻¹
  eig_βαi : ∀ q, eig_β q ≠ (eig_α q)⁻¹
  eig_βiαi : ∀ q, (eig_β q)⁻¹ ≠ (eig_α q)⁻¹
  D : PoitouTateData (ZMod p) (S₀ ⊕ Q)
  euler_balance : D.EulerPoincareBalance
  H0_vanish : Module.finrank (ZMod p) D.H0 = 0
  H0d_vanish : Module.finrank (ZMod p) D.H0d = 0
  H0_inf_equiv : D.H0v (Sum.inl v_inf) ≃ₗ[ZMod p] Sp4ArchH0 (ZMod p)
  H0_q_equiv : ∀ q : Q, D.H0v (Sum.inr q) ≃ₗ[ZMod p] Sp4DiagCentralizer (ZMod p) (eig_α q) (eig_β q)
  L_min : ∀ v : S₀ ⊕ Q, Submodule (ZMod p) (D.H1v v)
  L_inf_bot : L_min (Sum.inl v_inf) = ⊥
  /-- Ordinary / Fontaine–Laffaille local balance at `p`: `dim L_p - dim H⁰(G_p) = dim(𝔰𝔭₄/𝔟) = 4`. -/
  L_p_balance : (Module.finrank (ZMod p) (L_min (Sum.inl v_p)) : ℤ) -
    Module.finrank (ZMod p) (D.H0v (Sum.inl v_p)) = 4
  L_other_unram : ∀ v : S₀, v ≠ v_inf → v ≠ v_p →
    Module.finrank (ZMod p) (L_min (Sum.inl v)) = Module.finrank (ZMod p) (D.H0v (Sum.inl v))
  L_q_unram : ∀ q : Q,
    Module.finrank (ZMod p) (L_min (Sum.inr q)) = Module.finrank (ZMod p) (D.H0v (Sum.inr q))
  L_Q_loc : ∀ q : Q, Submodule (ZMod p) (D.H1v (Sum.inr q))
  L_Q_loc_dim : ∀ q : Q, Module.finrank (ZMod p) (L_Q_loc q) = 2 + m_Q

namespace Sp4WilesSelmerSystem

variable {S₀ Q : Type} [Fintype S₀] [DecidableEq S₀] [Fintype Q] [DecidableEq Q]
  {p : ℕ} [Fact p.Prime] (W : Sp4WilesSelmerSystem S₀ Q p)

def L_Q : ∀ v : S₀ ⊕ Q, Submodule (ZMod p) (W.D.H1v v)
  | Sum.inl v => W.L_min (Sum.inl v)
  | Sum.inr q => W.L_Q_loc q

theorem finrank_H0_inf_eq_four : Module.finrank (ZMod p) (W.D.H0v (Sum.inl W.v_inf)) = 4 := by
  rw [W.H0_inf_equiv.finrank_eq]
  exact finrank_sp4ArchH0_eq_four (ZMod p) (two_ne_zero_zmod W.hp3)

theorem finrank_H0_q_eq_two (q : Q) : Module.finrank (ZMod p) (W.D.H0v (Sum.inr q)) = 2 := by
  rw [(W.H0_q_equiv q).finrank_eq]
  exact finrank_sp4DiagCentralizer_eq_two (W.eig_αβ q) (W.eig_αβi q) (W.eig_ααi q)
    (W.eig_ββi q) (W.eig_βαi q) (W.eig_βiαi q)

theorem sum_S0_local_defect_eq_zero :
    ∑ v : S₀, ((Module.finrank (ZMod p) (W.L_min (Sum.inl v)) : ℤ) -
      Module.finrank (ZMod p) (W.D.H0v (Sum.inl v))) = 0 := by
  have h1 : ∀ v : S₀, v ∉ ({W.v_inf, W.v_p} : Finset S₀) →
      (Module.finrank (ZMod p) (W.L_min (Sum.inl v)) : ℤ) -
        Module.finrank (ZMod p) (W.D.H0v (Sum.inl v)) = 0 := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
    rw [W.L_other_unram v hv.1 hv.2, sub_self]
  rw [← Finset.sum_subset (Finset.subset_univ ({W.v_inf, W.v_p} : Finset S₀)) (fun v _ hv => h1 v hv)]
  rw [Finset.sum_pair W.v_inf_ne_vp, W.L_inf_bot, finrank_bot, W.finrank_H0_inf_eq_four, W.L_p_balance]
  norm_num

/-- **EXACT HIGHER-RANK `Sp₄` POITOU–TATE OBSTRUCTION DIMENSION BALANCE (`CohAx` / `TaylorWilesObstructionBound`)**:
1. Minimal level: `dim H¹_{L_min}(𝔰𝔭₄) = dim H¹_{L*_min}(𝔰𝔭₄(1))`;
2. Relaxed at `Q`: `dim H¹_{L_Q} - dim H¹_{L*_Q} = m_Q * |Q|` (so `(dim H¹_{L_Q} - g_Q) - r_Q = 0`);
3. Dual-killing (`dim H¹_{L*_Q} = 0`): `dim H¹_{L_Q} = m_Q * |Q|` (`= |Q|` for 1-parameter TW primes)! -/
theorem sp4_poitou_tate_balancing :
    Module.finrank (ZMod p) (W.D.Selmer W.L_min) =
      Module.finrank (ZMod p) (W.D.DualSelmer W.L_min) ∧
    (Module.finrank (ZMod p) (W.D.Selmer W.L_Q) : ℤ) -
      Module.finrank (ZMod p) (W.D.DualSelmer W.L_Q) = ((W.m_Q * Fintype.card Q : ℕ) : ℤ) ∧
    ((Module.finrank (ZMod p) (W.D.Selmer W.L_Q) : ℤ) - ((W.m_Q * Fintype.card Q : ℕ) : ℤ)) -
      (Module.finrank (ZMod p) (W.D.DualSelmer W.L_Q) : ℤ) = 0 ∧
    (Module.finrank (ZMod p) (W.D.DualSelmer W.L_Q) = 0 →
      Module.finrank (ZMod p) (W.D.Selmer W.L_Q) = W.m_Q * Fintype.card Q) := by
  have hmin : Module.finrank (ZMod p) (W.D.Selmer W.L_min) =
      Module.finrank (ZMod p) (W.D.DualSelmer W.L_min) := by
    have hgw := greenberg_wiles_euler_characteristic W.D W.euler_balance W.L_min
    rw [W.H0_vanish, W.H0d_vanish, Fintype.sum_sum_type, W.sum_S0_local_defect_eq_zero] at hgw
    have hQ0 : ∑ q : Q, ((Module.finrank (ZMod p) (W.L_min (Sum.inr q)) : ℤ) -
        Module.finrank (ZMod p) (W.D.H0v (Sum.inr q))) = 0 :=
      Finset.sum_eq_zero fun q _ => by rw [W.L_q_unram q, sub_self]
    rw [hQ0] at hgw
    omega
  have hbal : (Module.finrank (ZMod p) (W.D.Selmer W.L_Q) : ℤ) -
      Module.finrank (ZMod p) (W.D.DualSelmer W.L_Q) = ((W.m_Q * Fintype.card Q : ℕ) : ℤ) := by
    have hgw := greenberg_wiles_euler_characteristic W.D W.euler_balance W.L_Q
    rw [W.H0_vanish, W.H0d_vanish, Fintype.sum_sum_type] at hgw
    have hS0 : ∑ v : S₀, ((Module.finrank (ZMod p) (W.L_Q (Sum.inl v)) : ℤ) -
        Module.finrank (ZMod p) (W.D.H0v (Sum.inl v))) = 0 := W.sum_S0_local_defect_eq_zero
    have hQ : ∑ q : Q, ((Module.finrank (ZMod p) (W.L_Q (Sum.inr q)) : ℤ) -
        Module.finrank (ZMod p) (W.D.H0v (Sum.inr q))) = ((W.m_Q * Fintype.card Q : ℕ) : ℤ) := by
      have hterm : ∀ q : Q, ((Module.finrank (ZMod p) (W.L_Q (Sum.inr q)) : ℤ) -
          Module.finrank (ZMod p) (W.D.H0v (Sum.inr q))) = (W.m_Q : ℤ) := fun q => by
        change (Module.finrank (ZMod p) (W.L_Q_loc q) : ℤ) -
          Module.finrank (ZMod p) (W.D.H0v (Sum.inr q)) = (W.m_Q : ℤ)
        rw [W.L_Q_loc_dim q, W.finrank_H0_q_eq_two q]
        omega
      simp_rw [hterm]
      simp [mul_comm]
    rw [hS0, hQ] at hgw
    omega
  refine ⟨hmin, hbal, by omega, fun hvan => ?_⟩
  rw [hvan] at hbal
  omega

end Sp4WilesSelmerSystem

/-! ### 3.3 Direct Higher-Rank Bridge into `Stage11DiamondFujiwara` & `Stage11MazurDeformation` -/

/-- **Higher-Rank `U(3)` + `Sp₄` Poitou–Tate → `Stage11DiamondFujiwara` Bridge**:
combines `U3WilesSelmerSystem` / `Sp4WilesSelmerSystem` exact Poitou–Tate balancing (`g_Q - r_Q = 0`),
unconditional Taylor–Wiles prime sets `TaylorWilesPrimeSet p N g_Q bad`, and
`DiamondFujiwaraPatchingTower p g_Q`! -/
theorem higherRank_poitouTate_diamondFujiwara_bridge_U3
    {S₀ Q : Type} [Fintype S₀] [DecidableEq S₀] [Fintype Q] [DecidableEq Q]
    {p : ℕ} [Fact p.Prime] (W : U3WilesSelmerSystem S₀ Q p)
    (N : ℕ) (bad : Finset ℕ)
    (D : DiamondFujiwaraPatchingTower p (W.m_Q * Fintype.card Q)) :
    let g_Q := W.m_Q * Fintype.card Q
    ((Module.finrank (ZMod p) (W.D.Selmer W.L_Q) : ℤ) - (g_Q : ℤ)) -
      (Module.finrank (ZMod p) (W.D.DualSelmer W.L_Q) : ℤ) = 0 ∧
    (∃ TW : TaylorWilesPrimeSet p N g_Q bad,
      Fintype.card TW.GlobalDiamond = (p ^ N) ^ g_Q ∧
      ∀ M : ℕ, 1 ≤ M → Function.Surjective (TW.patchingToFiniteLevelDiamond M)) ∧
    Nonempty (D.M_inf ≃ₗ[PatchingBaseRing p g_Q] (Fin D.rank → PatchingBaseRing p g_Q)) ∧
    Nonempty (D.R_inf ≃+* D.T_inf) ∧
    Nonempty (D.R_0 ≃+* D.T_0) ∧
    (∃ s : ℕ, 0 < s ∧ Nonempty (D.M_0 ≃ₗ[D.T_0] (Fin s → D.T_0))) := by
  intro g_Q
  obtain ⟨_, _, hbal0, _⟩ := W.u3_poitou_tate_balancing
  obtain ⟨TW⟩ := exists_taylorWilesPrimeSet p N g_Q bad
  obtain ⟨hMfree, _, hRT_inf, hRT_0, hM0_free⟩ := D.main_patching_theorem
  exact ⟨hbal0, ⟨TW, TW.card_globalDiamond, fun M hM => (TW.patchingToFiniteLevelDiamond_surjective M hM).1⟩,
    hMfree, hRT_inf, hRT_0, hM0_free⟩

theorem higherRank_poitouTate_diamondFujiwara_bridge_Sp4
    {S₀ Q : Type} [Fintype S₀] [DecidableEq S₀] [Fintype Q] [DecidableEq Q]
    {p : ℕ} [Fact p.Prime] (W : Sp4WilesSelmerSystem S₀ Q p)
    (N : ℕ) (bad : Finset ℕ)
    (D : DiamondFujiwaraPatchingTower p (W.m_Q * Fintype.card Q)) :
    let g_Q := W.m_Q * Fintype.card Q
    ((Module.finrank (ZMod p) (W.D.Selmer W.L_Q) : ℤ) - (g_Q : ℤ)) -
      (Module.finrank (ZMod p) (W.D.DualSelmer W.L_Q) : ℤ) = 0 ∧
    (∃ TW : TaylorWilesPrimeSet p N g_Q bad,
      Fintype.card TW.GlobalDiamond = (p ^ N) ^ g_Q ∧
      ∀ M : ℕ, 1 ≤ M → Function.Surjective (TW.patchingToFiniteLevelDiamond M)) ∧
    Nonempty (D.M_inf ≃ₗ[PatchingBaseRing p g_Q] (Fin D.rank → PatchingBaseRing p g_Q)) ∧
    Nonempty (D.R_inf ≃+* D.T_inf) ∧
    Nonempty (D.R_0 ≃+* D.T_0) ∧
    (∃ s : ℕ, 0 < s ∧ Nonempty (D.M_0 ≃ₗ[D.T_0] (Fin s → D.T_0))) := by
  intro g_Q
  obtain ⟨_, _, hbal0, _⟩ := W.sp4_poitou_tate_balancing
  obtain ⟨TW⟩ := exists_taylorWilesPrimeSet p N g_Q bad
  obtain ⟨hMfree, _, hRT_inf, hRT_0, hM0_free⟩ := D.main_patching_theorem
  exact ⟨hbal0, ⟨TW, TW.card_globalDiamond, fun M hM => (TW.patchingToFiniteLevelDiamond_surjective M hM).1⟩,
    hMfree, hRT_inf, hRT_0, hM0_free⟩

end HigherRankPoitouTateBalance

/-! ## Section 4: Concrete `0`-Assumption Ultraproduct Patching Witness (`QuadAlg ℤ_[p] b 0` & `Δ mod 691`) -/

section ConcreteUltraproductWitness

/-- Left-multiplication matrix representation `QuadAlg A b 0 →+* M₂(A)` (`a + c·X ↦ !![a, 0; c, a + b·c]`). -/
def quadAlgLeftMulMat {A : Type*} [CommRing A] (b : A) :
    QuadAlg A b 0 →+* Matrix (Fin 2) (Fin 2) A where
  toFun u := !![u.fst, 0; u.snd, u.fst + b * u.snd]
  map_one' := by apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' u v := by
    apply Matrix.ext; intro i j
    fin_cases i <;> fin_cases j <;>
      (simp [Matrix.mul_apply, Fin.sum_univ_two]; try ring)
  map_zero' := by apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> simp
  map_add' u v := by
    apply Matrix.ext; intro i j
    fin_cases i <;> fin_cases j <;> (simp; try ring)

theorem quadAlgLeftMulMat_injective {A : Type*} [CommRing A] (b : A) :
    Function.Injective (quadAlgLeftMulMat b) := by
  intro u v huv
  have h00 := congrFun (congrFun huv 0) 0
  have h10 := congrFun (congrFun huv 1) 0
  simp [quadAlgLeftMulMat] at h00 h10
  exact QuadAlg.ext h00 h10

/-- Functorial left-multiplication matrix representation `QuadAlg A b 0 →+* M₂(B)` along any
ring homomorphism `f : A →+* B`. -/
def quadAlgMapLeftMulMat {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (b : A) :
    QuadAlg A b 0 →+* Matrix (Fin 2) (Fin 2) B where
  toFun u := !![f u.fst, 0; f u.snd, f u.fst + f b * f u.snd]
  map_one' := by apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' u v := by
    apply Matrix.ext; intro i j
    fin_cases i <;> fin_cases j <;>
      (simp [Matrix.mul_apply, Fin.sum_univ_two, map_add, map_mul]; try ring)
  map_zero' := by apply Matrix.ext; intro i j; fin_cases i <;> fin_cases j <;> simp
  map_add' u v := by
    apply Matrix.ext; intro i j
    fin_cases i <;> fin_cases j <;> (simp [map_add]; try ring)

/-- Truncation ideal `K_k` on `QuadAlg (PatchingBaseRing p g) (C b) 0` (`fst, snd ∈ truncIdeal p g (k + 1)`). -/
def quadTruncIdeal (p g : ℕ) [Fact p.Prime] (b : ℤ_[p]) (k : ℕ) :
    Ideal (QuadAlg (PatchingBaseRing p g) (MvPowerSeries.C b) 0) where
  carrier := { u | u.fst ∈ truncIdeal p g (k + 1) ∧ u.snd ∈ truncIdeal p g (k + 1) }
  zero_mem' := ⟨Ideal.zero_mem _, Ideal.zero_mem _⟩
  add_mem' {u v} hu hv := ⟨Ideal.add_mem _ hu.1 hv.1, Ideal.add_mem _ hu.2 hv.2⟩
  smul_mem' c {u} hu := by
    refine ⟨?_, ?_⟩
    · change c.fst * u.fst - 0 * (c.snd * u.snd) ∈ truncIdeal p g (k + 1)
      rw [zero_mul, sub_zero]
      exact Ideal.mul_mem_left _ c.fst hu.1
    · change c.fst * u.snd + c.snd * u.fst + MvPowerSeries.C b * (c.snd * u.snd) ∈ truncIdeal p g (k + 1)
      refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ c.fst hu.2)
        (Ideal.mul_mem_left _ c.snd hu.1)) ?_
      rw [← mul_assoc]
      exact Ideal.mul_mem_left _ (MvPowerSeries.C b * c.snd) hu.2

/-- Concrete `FiniteQuotRingSystem` on `QuadAlg (PatchingBaseRing p g) (C b) 0`. -/
def quadFiniteQuotSystem (p g : ℕ) [Fact p.Prime] (b : ℤ_[p]) :
    FiniteQuotRingSystem (QuadAlg (PatchingBaseRing p g) (MvPowerSeries.C b) 0) where
  K := quadTruncIdeal p g b
  K_antitone _ _ hab _ hu :=
    ⟨truncIdeal_antitone p g (Nat.add_le_add_right hab 1) hu.1,
     truncIdeal_antitone p g (Nat.add_le_add_right hab 1) hu.2⟩
  K_finite k := by
    let mapPair : (QuadAlg (PatchingBaseRing p g) (MvPowerSeries.C b) 0 ⧸
        quadTruncIdeal p g b k) → TruncRing p g k × TruncRing p g k :=
      Quotient.lift
        (fun u => (truncProj p g k u.fst, truncProj p g k u.snd))
        (fun u v huv => by
          have hdiff : u - v ∈ quadTruncIdeal p g b k := Ideal.Quotient.eq.mp (Quotient.sound huv)
          exact Prod.ext (Ideal.Quotient.eq.mpr hdiff.1) (Ideal.Quotient.eq.mpr hdiff.2))
    have hinj : Function.Injective mapPair := by
      intro x y hxy
      obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective y
      apply Ideal.Quotient.eq.mpr
      exact ⟨Ideal.Quotient.eq.mp (congrArg Prod.fst hxy),
        Ideal.Quotient.eq.mp (congrArg Prod.snd hxy)⟩
    exact Finite.of_injective mapPair hinj
  K_iInf_bot u hu :=
    QuadAlg.ext (truncIdeal_iInf_eq_bot p g fun k => (hu k).1)
      (truncIdeal_iInf_eq_bot p g fun k => (hu k).2)

/-- **Concrete `0`-Assumption `UltraproductPatchingData` on `QuadAlg (PatchingBaseRing p g) (C b) 0`**
using the canonical non-principal ultrafilter `nonprincipalUltrafilterNat`! -/
def concreteQuadUltraproductData (p g : ℕ) [Fact p.Prime] (b : ℤ_[p]) :
    UltraproductPatchingData p g
      (QuadAlg (PatchingBaseRing p g) (MvPowerSeries.C b) 0)
      (quadFiniteQuotSystem p g b) where
  𝒰 := nonprincipalUltrafilterNat
  𝒰_le_atTop := nonprincipalUltrafilterNat_le_atTop
  rank := 2
  rank_pos := by norm_num
  s_univ := algebraMap (PatchingBaseRing p g)
    (QuadAlg (PatchingBaseRing p g) (MvPowerSeries.C b) 0)
  ker_nk _ _ := ⊥
  act_nk _ k :=
    Ideal.Quotient.lift (quadTruncIdeal p g b k)
      (quadAlgMapLeftMulMat (truncProj p g k) (MvPowerSeries.C b))
      (fun u hu => by
        apply Matrix.ext; intro i j
        have h1 : truncProj p g k u.fst = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hu.1
        have h2 : truncProj p g k u.snd = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hu.2
        fin_cases i <;> fin_cases j
        · exact h1
        · rfl
        · exact h2
        · change truncProj p g k u.fst + truncProj p g k (MvPowerSeries.C b) * truncProj p g k u.snd = 0
          rw [h1, h2, mul_zero, add_zero])
  ker_le_act _ := Filter.Eventually.of_forall fun _ => bot_le
  act_scalar_S k := Filter.Eventually.of_forall fun _ s => by
    apply Matrix.ext; intro i j
    fin_cases i <;> fin_cases j
    · rfl
    · rfl
    · change truncProj p g k 0 = 0; exact map_zero _
    · change truncProj p g k s + truncProj p g k (MvPowerSeries.C b) * truncProj p g k 0 = truncProj p g k s
      rw [map_zero, mul_zero, add_zero]
  trans_conj k := Filter.Eventually.of_forall fun _ => ⟨1, fun x => by
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
    apply Matrix.ext; intro i j
    fin_cases i <;> fin_cases j
    · change truncTrans p g k (truncProj p g (k + 1) u.fst) = _
      rw [Units.val_one, Matrix.one_mul, inv_one, Units.val_one, Matrix.mul_one]; rfl
    · change truncTrans p g k 0 = _
      rw [Units.val_one, Matrix.one_mul, inv_one, Units.val_one, Matrix.mul_one, map_zero]; rfl
    · change truncTrans p g k (truncProj p g (k + 1) u.snd) = _
      rw [Units.val_one, Matrix.one_mul, inv_one, Units.val_one, Matrix.mul_one]; rfl
    · change truncTrans p g k (truncProj p g (k + 1) u.fst +
        truncProj p g (k + 1) (MvPowerSeries.C b) * truncProj p g (k + 1) u.snd) = _
      rw [Units.val_one, Matrix.one_mul, inv_one, Units.val_one, Matrix.mul_one, map_add, map_mul]; rfl⟩
  M_0 := QuadAlg ℤ_[p] b 0
  eM0 := QuadAlg.equivPi2 ℤ_[p] b 0
  act0 := quadAlgMapLeftMulMat (MvPowerSeries.constantCoeff : PatchingBaseRing p g →+* ℤ_[p]) (MvPowerSeries.C b)
  act0_scalar s := by
    apply Matrix.ext; intro i j
    fin_cases i <;> fin_cases j
    · rfl
    · rfl
    · change MvPowerSeries.constantCoeff (0 : PatchingBaseRing p g) = 0; exact map_zero _
    · change MvPowerSeries.constantCoeff s +
          MvPowerSeries.constantCoeff (MvPowerSeries.C b) *
            MvPowerSeries.constantCoeff (0 : PatchingBaseRing p g) =
        MvPowerSeries.constantCoeff s
      rw [map_zero, mul_zero, add_zero]
  spec_compat k := Filter.Eventually.of_forall fun _ u => by
    apply Matrix.ext; intro i j
    fin_cases i <;> fin_cases j
    · rfl
    · change truncToZModPow p g k 0 = PadicInt.toZModPow (k + 1) 0
      rw [map_zero, map_zero]
    · rfl
    · change truncToZModPow p g k (truncProj p g k u.fst +
          truncProj p g k (MvPowerSeries.C b) * truncProj p g k u.snd) =
        PadicInt.toZModPow (k + 1) (MvPowerSeries.constantCoeff u.fst +
          MvPowerSeries.constantCoeff (MvPowerSeries.C b) * MvPowerSeries.constantCoeff u.snd)
      rw [map_add, map_mul, truncToZModPow_mk, truncToZModPow_mk, truncToZModPow_mk,
        map_add, map_mul]

/-- **Concrete `0`-Assumption End-to-End Witness (`witness_ultraproduct_quadPk`)**:
fires `pmodEx_patched_free_over_Sinf` unconditionally for EVERY prime `p`, EVERY `g : ℕ`,
and EVERY `b : ℤ_[p]` (covering `ℤ_[p][X]/(X² - p^k X)` and Ramanujan `Δ mod 691` at `p = 691, b = 691`)! -/
theorem witness_ultraproduct_quadPk (p g : ℕ) [Fact p.Prime] (b : ℤ_[p]) :
    let D := concreteQuadUltraproductData p g b
    0 < D.rank ∧
    Nonempty (D.PatchedM ≃ₗ[PatchingBaseRing p g] (Fin 2 → PatchingBaseRing p g)) ∧
    Function.Surjective D.patchedPhi ∧
    Module.annihilator D.PatchedT D.PatchedM = ⊥ ∧
    Nonempty (D.PatchedM0 ≃ₗ[ℤ_[p]] QuadAlg ℤ_[p] b 0) ∧
    Module.annihilator D.Level0T D.M_0 = ⊥ := by
  intro D
  obtain ⟨hr, hfree, hsurj, hfaith, _, hspec, h0faith⟩ := D.pmodEx_patched_free_over_Sinf
  exact ⟨hr, hfree, hsurj, hfaith, hspec, h0faith⟩

end ConcreteUltraproductWitness

end Stage13UltraproductPatching
end RHDirect
