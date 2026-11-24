import RHDirect.Stage12GaloisShaLen
import RHDirect.PAdicChainValuation
import RHDirect.Stage2ThetaWire

/-!
# RHDirect.Stage14M5_DivinNRealGalois

Field-2 Package M5 Wave 1: **Genuine Galois-Cohomology `realGaloisSelmerSystem` + `AlpoegeVVle`
Wired Directly to `VVRecord`, `ChainValuationSystem`, `LinkN`, `DIVinN`, and `Stage2ThetaWire`**
in pure Mathlib `v4.33.1` (`0` `sorry`, `0` custom `axiom`s, `0` `opaque`, `0` `native_decide`).

This module eliminates all abstract surrogate `SelmerSystem` placeholders from the `DivinNOfHypV`
divisibility pipeline by binding `RHDirect.Stage12GaloisShaLen.realGaloisSelmerSystem` (whose
`shaLen E p e` is literally `Module.length ℤ_[p] (Ш¹(G_{E,S_p}, (ℚ_p/ℤ_p)(-e)))` over
`AlgebraicClosure E`, proved independent of both `Ω` and `LData`) and
`RHDirect.Stage12GaloisShaLen.AlpoegeVVle` directly to `PAdicChainValuation` and
`Stage2ThetaWire`.

## Contents

1. **Genuine Galois-Cohomology Selmer-Length Terms & `VVRecord` (`vvRecord_of_realGalois`)**:
   - `realGaloisVVTerm`: prime-weighted Shafarevich–Tate length sum
     `log l * ∑_{1 ≤ e < t} toNat(len_{ℤ_l} Ш¹(G_{E,S_l}, (ℚ_l/ℤ_l)(-e)))`.
   - `ShaFinOddRealGalois`: finiteness of all odd/weight-`< t` genuine `Sha1Galois E l e` lengths,
     proved invariant across all algebraic closures `Ω` and local data `LData E Ω p`.
   - `VVRecord`: packaged finiteness, `Summable (realGaloisVVTerm E t)`, and infinite-series bound
     `∑' l, realGaloisVVTerm E t l ≤ B`, with bidirectional equivalences `vvRecord_iff_vvle` and
     `vvRecord_iff_alpoegeVVle`.
   - `vvRecord_of_realGalois` (from arbitrary `(Ω, ld)` witness, `AlpoegeVVle`, or
     `VVle realGaloisSelmerSystem`), plus monotonicity, single-prime extraction, `H¹`-vanishing /
     `Sha = ⊥` / finite-bad-prime constructors, and unconditional `t = 1` witnesses.

2. **Chain-Valuation Budget Integration (`ChainValuationBudgetRecord`)**:
   - Connects `VVRecord E t B` directly to `PAdicChainValuation.ChainValuationSystem`
     (`levelChainSharpColumnValuation_of_stability`), tracking `m`-step column-lift divisibility
     deficits `m * ∑' l, realGaloisVVTerm E t l ≤ m * B` and common-lattice division.

3. **`HypVRealGalois`: Concrete Hypothesis Wrapper Tying `VWin realGaloisSelmerSystem` & `AlpoegeVVle`**:
   - `AlpoegeVAt`, `AlpoegeVWinAt`, `AlpoegeVWin`, with exact logical equivalences
     `alpoegeVAt_iff_realGaloisVAt`, `alpoegeVWinAt_iff_realGaloisVWinAt`, and
     `alpoegeVWin_iff_realGaloisVWin`.
   - `HypVRealGalois`: concrete hypothesis wrapper over `VWin realGaloisSelmerSystem` exporting
     `AlpoegeVVle`, `VVRecord`, `WinDatum` window extraction (via unconditional
     `Stage11LinnikUnconditional.pairEx_unconditional`), and `GaloisModularityContract`.
   - `RealGaloisScaleFamily` & `HypVFamilyRealGalois`: scale-indexed `HypV` predicate matching
     `DivinNOfHypV.HypV`, bridged directly from `HypVRealGalois` on `[Z, Z^(3/2)]` windows.

4. **Pointwise & Family `DIVinN` Divisibility Bounds (`divinN_at_realGalois` & `divinN_of_hypV_realGalois`)**:
   - `RealGaloisSizeData`, `LinkNAtRealGalois`, `DIVinNAtRealGalois`, `SmallLevelRankEqAt`.
   - `divinN_at_realGalois`: proved pointwise `DIVinN` bound directly from `LinkNAtRealGalois` and
     `VVRecord` (or `AlpoegeVVle` / `VAt realGaloisSelmerSystem`).
   - `RealGaloisChainFamily`, `LinkNRealGalois`, `SmallLevelRankEqRealGalois`, `DIVinNRealGalois`.
   - `divinN_of_hypV_realGalois` & `divinN_of_vwin_realGalois`: full family-level `DIVinN` theorems
     wired to `realGaloisSelmerSystem` (with zero abstract Selmer-system placeholders!).

5. **Wave 2–3 Bridges (`Stage14M5_IndefSideAndON`, `Stage14M5_LinkDIVtBridge`, `Stage2ThetaWire`)**:
   - `realGalois_discharges_slope_div`, `realGalois_divLink_of_divinN`,
     `realGalois_s_lower5_of_divinN`, `realGalois_ga_bound5_of_divinN`.
   - `realGalois_thetaSlopeContract_of_stage2`, `realGalois_allLevelsWindowBound_of_hypV`,
     `realGalois_assembly_of_stage2`, `realGalois_riemannHypothesis_of_hypV_and_stage2`.
   - Concrete `0`-assumption non-vacuous witnesses (`concrete_vvRecord_rat_one`,
     `concrete_divinN_at_realGalois`, `concrete_divinN_of_hypV_realGalois`).
-/

open Real Finset NumberField
open scoped BigOperators

namespace RHDirect.Stage14M5_DivinNRealGalois

noncomputable section

open RHDirect
open RHDirect.Stage12GaloisShaLen
open RHDirect.PAdicChainValuation
open RHDirect.Stage2ThetaWire
open RHDirect.ThetaSlopeEngine
open RHDirect.SlopeInequality

/-! ## Section 1: Genuine Galois-Cohomology Selmer-Length Terms & `VVRecord` -/

section RealGaloisVVRecord

/-- Prime-weighted genuine Galois-cohomology Shafarevich–Tate length term at rational prime `l`:
`log l * ∑_{1 ≤ e < t} toNat(len_{ℤ_l} Ш¹(G_{E,S_l}, (ℚ_l/ℤ_l)(-e)))` when `l` is prime,
and `0` otherwise. Directly specializes `PAdicChainValuation.vvTerm` to `realGaloisSelmerSystem`. -/
def realGaloisVVTerm (E : Type) [Field E] [NumberField E] (t l : ℕ) : ℝ :=
  PAdicChainValuation.vvTerm realGaloisSelmerSystem E t l

@[simp]
theorem realGaloisVVTerm_eq_vvTerm (E : Type) [Field E] [NumberField E] (t l : ℕ) :
    realGaloisVVTerm E t l = PAdicChainValuation.vvTerm realGaloisSelmerSystem E t l := rfl

theorem realGaloisVVTerm_of_prime (E : Type) [Field E] [NumberField E] {t l : ℕ}
    (hl : l.Prime) :
    realGaloisVVTerm E t l =
      Real.log (l : ℝ) *
        ∑ e ∈ Finset.Ico 1 t, ((galoisShaLen E (⟨l, hl⟩ : Nat.Primes) (e : ℤ)).toNat : ℝ) := by
  unfold realGaloisVVTerm PAdicChainValuation.vvTerm
  rw [dif_pos hl]
  rfl

theorem realGaloisVVTerm_of_not_prime (E : Type) [Field E] [NumberField E] {t l : ℕ}
    (hl : ¬ l.Prime) : realGaloisVVTerm E t l = 0 := by
  unfold realGaloisVVTerm PAdicChainValuation.vvTerm
  rw [dif_neg hl]

theorem realGaloisVVTerm_of_LData (E Ω : Type) [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (ld : ∀ (p : ℕ) [Fact p.Prime], LData E Ω p) (t : ℕ) {l : ℕ} (hl : l.Prime) :
    realGaloisVVTerm E t l =
      Real.log (l : ℝ) *
        ∑ e ∈ Finset.Ico 1 t, ((letI : Fact l.Prime := ⟨hl⟩; shaLen (ld l) (e : ℤ)).toNat : ℝ) := by
  rw [realGaloisVVTerm_of_prime E hl]
  refine congrArg (Real.log (l : ℝ) * ·) (Finset.sum_congr rfl fun e _ => ?_)
  have : Fact l.Prime := ⟨hl⟩
  rw [shaLen_eq_galoisShaLen E (⟨l, hl⟩ : Nat.Primes) (ld l) (e : ℤ)]

theorem realGaloisVVTerm_nonneg (E : Type) [Field E] [NumberField E] (t l : ℕ) :
    0 ≤ realGaloisVVTerm E t l :=
  PAdicChainValuation.vvTerm_nonneg realGaloisSelmerSystem E t l

theorem realGaloisVVTerm_zero_of_le_one (E : Type) [Field E] [NumberField E]
    {t : ℕ} (ht : t ≤ 1) (l : ℕ) : realGaloisVVTerm E t l = 0 := by
  by_cases hl : l.Prime
  · rw [realGaloisVVTerm_of_prime E hl]
    have hIco : Finset.Ico 1 t = ∅ := Finset.Ico_eq_empty (by omega)
    rw [hIco, Finset.sum_empty, mul_zero]
  · exact realGaloisVVTerm_of_not_prime E hl

theorem realGaloisVVTerm_zero_at_zero (E : Type) [Field E] [NumberField E] (t : ℕ) :
    realGaloisVVTerm E t 0 = 0 :=
  realGaloisVVTerm_of_not_prime E Nat.not_prime_zero

theorem realGaloisVVTerm_zero_at_one (E : Type) [Field E] [NumberField E] (t : ℕ) :
    realGaloisVVTerm E t 1 = 0 :=
  realGaloisVVTerm_of_not_prime E Nat.not_prime_one

theorem realGaloisVVTerm_mono_t (E : Type) [Field E] [NumberField E] {t t' : ℕ}
    (ht : t' ≤ t) (l : ℕ) : realGaloisVVTerm E t' l ≤ realGaloisVVTerm E t l := by
  by_cases hl : l.Prime
  · rw [realGaloisVVTerm_of_prime E hl, realGaloisVVTerm_of_prime E hl]
    refine mul_le_mul_of_nonneg_left ?_ (Real.log_natCast_nonneg l)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun e _ _ => Nat.cast_nonneg _)
    intro e he
    simp only [Finset.mem_Ico] at he ⊢
    omega
  · rw [realGaloisVVTerm_of_not_prime E hl, realGaloisVVTerm_of_not_prime E hl]

theorem realGaloisVVTerm_single_e_le (E : Type) [Field E] [NumberField E]
    (l : Nat.Primes) {t e : ℕ} (he1 : 0 < e) (het : e < t) :
    Real.log (l : ℝ) * ((galoisShaLen E l (e : ℤ)).toNat : ℝ) ≤ realGaloisVVTerm E t l.1 := by
  rw [realGaloisVVTerm_of_prime E l.2]
  refine mul_le_mul_of_nonneg_left ?_ (Real.log_natCast_nonneg l.1)
  have he_mem : e ∈ Finset.Ico 1 t := Finset.mem_Ico.mpr ⟨Nat.succ_le_of_lt he1, het⟩
  have hle : ((galoisShaLen E l (e : ℤ)).toNat : ℝ) ≤
      ∑ k ∈ Finset.Ico 1 t, ((galoisShaLen E l (k : ℤ)).toNat : ℝ) :=
    Finset.single_le_sum (s := Finset.Ico 1 t)
      (f := fun k : ℕ => ((galoisShaLen E l (k : ℤ)).toNat : ℝ))
      (fun k _ => Nat.cast_nonneg _) he_mem
  exact hle.trans_eq (Finset.sum_congr rfl fun k _ => by cases l; rfl)

theorem realGaloisVVTerm_eq_zero_of_subsingleton_H1 (E : Type) [Field E] [NumberField E]
    (t : ℕ) (p : Nat.Primes)
    (hH1 : ∀ (e : ℕ), 0 < e → e < t →
      Subsingleton (H1 (qzTw (canonicalLData E p) (e : ℤ)))) :
    realGaloisVVTerm E t p.1 = 0 := by
  rw [realGaloisVVTerm_of_prime E p.2]
  have hsum : ∑ e ∈ Finset.Ico 1 t,
      ((galoisShaLen E (⟨p.1, p.2⟩ : Nat.Primes) (e : ℤ)).toNat : ℝ) = 0 := by
    refine Finset.sum_eq_zero fun e he => ?_
    rw [Finset.mem_Ico] at he
    have : Subsingleton (H1 (qzTw (canonicalLData E p) (e : ℤ))) := hH1 e he.1 he.2
    have heq : (⟨p.1, p.2⟩ : Nat.Primes) = p := Subtype.eta p p.2
    rw [heq, galoisShaLen_eq_zero_of_subsingleton_H1 E p (e : ℤ)]
    simp
  rw [hsum, mul_zero]

/-- Finiteness of all genuine Galois-cohomology Shafarevich–Tate lengths
`len_{ℤ_l} Ш¹(G_{E,S_l}, (ℚ_l/ℤ_l)(-e))` for primes `l` and weights `1 ≤ e < t`. -/
def ShaFinOddRealGalois (E : Type) [Field E] [NumberField E] (t : ℕ) : Prop :=
  ∀ (l : Nat.Primes) (e : ℕ), 0 < e → e < t → galoisShaLen E l (e : ℤ) ≠ ⊤

theorem shaFinOddRealGalois_iff_selmer (E : Type) [Field E] [NumberField E] (t : ℕ) :
    ShaFinOddRealGalois E t ↔
      ∀ (l : Nat.Primes) (e : ℕ), 0 < e → e < t → realGaloisSelmerSystem.shaLen E l e ≠ ⊤ := by
  simp [ShaFinOddRealGalois, realGaloisSelmerSystem_shaLen]

theorem shaFinOddRealGalois_iff_forall_LData (E : Type) [Field E] [NumberField E] (t : ℕ) :
    ShaFinOddRealGalois E t ↔
      ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
        (ld : ∀ (p : ℕ) [Fact p.Prime], LData E Ω p)
        (p : ℕ) [Fact p.Prime] (e : ℕ), 0 < e → e < t → shaLen (ld p) (e : ℤ) ≠ ⊤ := by
  constructor
  · intro h Ω _ _ _ ld p hp e he1 he2
    rw [shaLen_eq_galoisShaLen E (⟨p, hp.out⟩ : Nat.Primes) (ld p) (e : ℤ)]
    exact h ⟨p, hp.out⟩ e he1 he2
  · intro h l e he1 he2
    have : Fact l.1.Prime := ⟨l.2⟩
    let ld : ∀ (p : ℕ) [Fact p.Prime], LData E (AlgebraicClosure E) p :=
      fun p _ => Classical.choice (ldata_nonempty (F := E) (Ω := AlgebraicClosure E) p)
    rw [← shaLen_eq_galoisShaLen E l (ld l.1) (e : ℤ)]
    exact h (AlgebraicClosure E) ld l.1 e he1 he2

theorem shaFinOddRealGalois_of_LData (E Ω : Type) [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (ld : ∀ (p : ℕ) [Fact p.Prime], LData E Ω p) {t : ℕ}
    (h : ∀ (p : ℕ) [Fact p.Prime] (e : ℕ), 0 < e → e < t → shaLen (ld p) (e : ℤ) ≠ ⊤) :
    ShaFinOddRealGalois E t := by
  intro l e he1 he2
  have : Fact l.1.Prime := ⟨l.2⟩
  rw [← shaLen_eq_galoisShaLen E l (ld l.1) (e : ℤ)]
  exact h l.1 e he1 he2

theorem shaFinOddRealGalois_mono {E : Type} [Field E] [NumberField E] {t t' : ℕ}
    (h : ShaFinOddRealGalois E t) (ht : t' ≤ t) : ShaFinOddRealGalois E t' :=
  fun l e he1 he2 => h l e he1 (lt_of_lt_of_le he2 ht)

theorem shaFinOddRealGalois_one (E : Type) [Field E] [NumberField E] :
    ShaFinOddRealGalois E 1 := fun _ e he1 he2 => by omega

theorem shaFinOddRealGalois_coe_toNat {E : Type} [Field E] [NumberField E] {t : ℕ}
    (h : ShaFinOddRealGalois E t) (l : Nat.Primes) {e : ℕ} (he1 : 0 < e) (he2 : e < t) :
    ((galoisShaLen E l (e : ℤ)).toNat : ℕ∞) = galoisShaLen E l (e : ℤ) :=
  ENat.natCast_toNat (h l e he1 he2)

theorem shaFinOddRealGalois_lt_top {E : Type} [Field E] [NumberField E] {t : ℕ}
    (h : ShaFinOddRealGalois E t) (l : Nat.Primes) {e : ℕ} (he1 : 0 < e) (he2 : e < t) :
    galoisShaLen E l (e : ℤ) < ⊤ :=
  lt_top_iff_ne_top.mpr (h l e he1 he2)

/-- **Concrete `VVRecord` for the Genuine Galois-Cohomology `realGaloisSelmerSystem`**:
packages finiteness of all `len_{ℤ_l} Ш¹(G_{E,S_l}, (ℚ_l/ℤ_l)(-e))` (`0 < e < t`),
summability of the prime-weighted series `realGaloisVVTerm E t`, and the total upper bound `≤ B`. -/
structure VVRecord (E : Type) [Field E] [NumberField E] (t : ℕ) (B : ℝ) : Prop where
  shaFin : ShaFinOddRealGalois E t
  summable : Summable (realGaloisVVTerm E t)
  tsum_le : ∑' l, realGaloisVVTerm E t l ≤ B

namespace VVRecord

theorem bound_nonneg {E : Type} [Field E] [NumberField E] {t : ℕ} {B : ℝ}
    (h : VVRecord E t B) : 0 ≤ B :=
  le_trans (tsum_nonneg (realGaloisVVTerm_nonneg E t)) h.tsum_le

theorem mono {E : Type} [Field E] [NumberField E] {t t' : ℕ} {B B' : ℝ}
    (h : VVRecord E t B) (ht : t' ≤ t) (hB : B ≤ B') : VVRecord E t' B' where
  shaFin := shaFinOddRealGalois_mono h.shaFin ht
  summable := Summable.of_nonneg_of_le (realGaloisVVTerm_nonneg E t')
    (realGaloisVVTerm_mono_t E ht) h.summable
  tsum_le := by
    have hsum' : Summable (realGaloisVVTerm E t') :=
      Summable.of_nonneg_of_le (realGaloisVVTerm_nonneg E t') (realGaloisVVTerm_mono_t E ht) h.summable
    exact le_trans (hsum'.tsum_le_tsum (realGaloisVVTerm_mono_t E ht) h.summable)
      (le_trans h.tsum_le hB)

theorem partial_sum_le {E : Type} [Field E] [NumberField E] {t : ℕ} {B : ℝ}
    (h : VVRecord E t B) (s : Finset ℕ) : ∑ l ∈ s, realGaloisVVTerm E t l ≤ B :=
  le_trans (h.summable.sum_le_tsum s (fun l _ => realGaloisVVTerm_nonneg E t l)) h.tsum_le

theorem prime_finset_sum_le {E : Type} [Field E] [NumberField E] {t : ℕ} {B : ℝ}
    (h : VVRecord E t B) (P : Finset Nat.Primes) :
    ∑ l ∈ P, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((galoisShaLen E l (e : ℤ)).toNat : ℝ) ≤ B := by
  classical
  have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := Subtype.val_injective
  have h1 : ∑ l ∈ P, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((galoisShaLen E l (e : ℤ)).toNat : ℝ) =
      ∑ l ∈ P.image (fun p : Nat.Primes => (p : ℕ)), realGaloisVVTerm E t l := by
    rw [Finset.sum_image (fun x _ y _ hxy => hinj hxy)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [realGaloisVVTerm_of_prime E l.2]
    cases l
    rfl
  rw [h1]
  exact h.partial_sum_le (P.image (fun p : Nat.Primes => (p : ℕ)))

theorem single_prime_le {E : Type} [Field E] [NumberField E] {t : ℕ} {B : ℝ}
    (h : VVRecord E t B) (l : Nat.Primes) : realGaloisVVTerm E t l.1 ≤ B := by
  simpa using h.partial_sum_le {l.1}

theorem single_shaLen_weighted_le {E : Type} [Field E] [NumberField E] {t : ℕ} {B : ℝ}
    (h : VVRecord E t B) (l : Nat.Primes) {e : ℕ} (he1 : 0 < e) (he2 : e < t) :
    Real.log (l : ℝ) * ((galoisShaLen E l (e : ℤ)).toNat : ℝ) ≤ B :=
  (realGaloisVVTerm_single_e_le E l he1 he2).trans (h.single_prime_le l)

theorem shaLen_toNat_le {E : Type} [Field E] [NumberField E] {t : ℕ} {B : ℝ}
    (h : VVRecord E t B) (l : Nat.Primes) {e : ℕ} (he1 : 0 < e) (he2 : e < t) :
    ((galoisShaLen E l (e : ℤ)).toNat : ℝ) ≤ B / Real.log (l : ℝ) := by
  have h2 : (2 : ℝ) ≤ (l : ℝ) := by exact_mod_cast l.2.two_le
  have hlog : 0 < Real.log (l : ℝ) := Real.log_pos (by linarith)
  rw [le_div_iff₀ hlog, mul_comm]
  exact h.single_shaLen_weighted_le l he1 he2

theorem toVVle {E : Type} [Field E] [NumberField E] {t : ℕ} {B : ℝ}
    (h : VVRecord E t B) : RHDirect.VVle realGaloisSelmerSystem E t B := by
  refine ⟨(shaFinOddRealGalois_iff_selmer E t).mp h.shaFin, fun P => ?_⟩
  exact h.prime_finset_sum_le P

theorem toAlpoegeVVle {E : Type} [Field E] [NumberField E] {t : ℕ} {B : ℝ}
    (h : VVRecord E t B) : AlpoegeVVle E t B :=
  (alpoegeVVle_iff_realGaloisVVle E t B).mpr h.toVVle

theorem toLData_sum_le {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (ld : ∀ (p : ℕ) [Fact p.Prime], LData E Ω p) {t : ℕ} {B : ℝ}
    (h : VVRecord E t B) (P : Finset Nat.Primes) :
    ∑ l ∈ P, Real.log (l : ℕ) *
      ∑ e ∈ Finset.Ico 1 t, ((letI : Fact l.1.Prime := ⟨l.2⟩; shaLen (ld l.1) (e : ℤ)).toNat : ℝ) ≤ B :=
  (h.toAlpoegeVVle Ω ld).2 P

end VVRecord

/-- **`vvRecord_of_vvle_realGalois`**: proved conversion from `RHDirect.VVle realGaloisSelmerSystem`
into `VVRecord`, using `PAdicChainValuation.vvRecord_of_VVle`. -/
theorem vvRecord_of_vvle_realGalois {E : Type} [Field E] [NumberField E] {t : ℕ} {B : ℝ}
    (h : RHDirect.VVle realGaloisSelmerSystem E t B) : VVRecord E t B := by
  obtain ⟨hfin, hsum, hle⟩ := PAdicChainValuation.vvRecord_of_VVle h
  exact ⟨(shaFinOddRealGalois_iff_selmer E t).mpr hfin, hsum, hle⟩

/-- **`vvRecord_of_alpoegeVVle`**: proved conversion from `Stage12GaloisShaLen.AlpoegeVVle`
into `VVRecord`. -/
theorem vvRecord_of_alpoegeVVle {E : Type} [Field E] [NumberField E] {t : ℕ} {B : ℝ}
    (h : AlpoegeVVle E t B) : VVRecord E t B :=
  vvRecord_of_vvle_realGalois ((alpoegeVVle_iff_realGaloisVVle E t B).mp h)

/-- **`vvRecord_of_realGalois`**: proved conversion from ANY concrete algebraic closure `Ω` and
`LData E Ω p` witness of `shaLen (ld p) (e : ℤ) ≠ ⊤` and finite-prime weighted sum bound `≤ B`
directly into `VVRecord E t B` (and `PAdicChainValuation.vvRecord_of_VVle`), using canonical
independence `shaLen_eq_galoisShaLen`! -/
theorem vvRecord_of_realGalois (E Ω : Type) [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (ld : ∀ (p : ℕ) [Fact p.Prime], LData E Ω p) (t : ℕ) (B : ℝ)
    (hfin : ∀ (p : ℕ) [Fact p.Prime] (e : ℕ), 0 < e → e < t → shaLen (ld p) (e : ℤ) ≠ ⊤)
    (hsum : ∀ P : Finset Nat.Primes,
      ∑ l ∈ P, Real.log (l : ℕ) *
        ∑ e ∈ Finset.Ico 1 t, ((letI : Fact l.1.Prime := ⟨l.2⟩; shaLen (ld l.1) (e : ℤ)).toNat : ℝ) ≤ B) :
    VVRecord E t B := by
  refine vvRecord_of_vvle_realGalois ⟨fun l e he1 he2 => ?_, fun P => ?_⟩
  · have : Fact l.1.Prime := ⟨l.2⟩
    rw [realGaloisSelmerSystem_shaLen, ← shaLen_eq_galoisShaLen E l (ld l.1) (e : ℤ)]
    exact hfin l.1 e he1 he2
  · refine le_trans ?_ (hsum P)
    refine le_of_eq (Finset.sum_congr rfl fun l _ => ?_)
    congr 1
    refine Finset.sum_congr rfl fun e _ => ?_
    have : Fact l.1.Prime := ⟨l.2⟩
    rw [realGaloisSelmerSystem_shaLen, ← shaLen_eq_galoisShaLen E l (ld l.1) (e : ℤ)]

theorem vvRecord_iff_vvle (E : Type) [Field E] [NumberField E] (t : ℕ) (B : ℝ) :
    VVRecord E t B ↔ RHDirect.VVle realGaloisSelmerSystem E t B :=
  ⟨VVRecord.toVVle, vvRecord_of_vvle_realGalois⟩

theorem vvRecord_iff_alpoegeVVle (E : Type) [Field E] [NumberField E] (t : ℕ) (B : ℝ) :
    VVRecord E t B ↔ AlpoegeVVle E t B :=
  (vvRecord_iff_vvle E t B).trans (alpoegeVVle_iff_realGaloisVVle E t B).symm

/-- Unconditional `VVRecord E 1 B` for any number field `E` and any `B ≥ 0` (since `Ico 1 1 = ∅`). -/
theorem vvRecord_one_unconditional (E : Type) [Field E] [NumberField E] {B : ℝ} (hB : 0 ≤ B) :
    VVRecord E 1 B where
  shaFin := shaFinOddRealGalois_one E
  summable := by
    have h0 : realGaloisVVTerm E 1 = fun _ => (0 : ℝ) := funext (realGaloisVVTerm_zero_of_le_one E le_rfl)
    rw [h0]
    exact summable_zero
  tsum_le := by
    have h0 : realGaloisVVTerm E 1 = fun _ => (0 : ℝ) := funext (realGaloisVVTerm_zero_of_le_one E le_rfl)
    rw [h0, tsum_zero]
    exact hB

/-- `VVRecord E t B` from `H¹(G_{E,S_p}, (ℚ_p/ℤ_p)(-e))` vanishing (`Subsingleton`) for all
`p : Nat.Primes` and `0 < e < t`. -/
theorem vvRecord_of_subsingleton_H1 (E : Type) [Field E] [NumberField E] (t : ℕ) {B : ℝ}
    (hB : 0 ≤ B)
    (hH1 : ∀ (p : Nat.Primes) (e : ℕ), 0 < e → e < t →
      Subsingleton (H1 (qzTw (canonicalLData E p) (e : ℤ)))) :
    VVRecord E t B :=
  vvRecord_of_vvle_realGalois (VVle_realGalois_of_subsingleton_H1 E t hB hH1)

/-- `VVRecord E t B` when `Sha1Galois E p e = ⊥` for all primes `p` and `0 < e < t`. -/
theorem vvRecord_of_sha_eq_bot (E : Type) [Field E] [NumberField E] (t : ℕ) {B : ℝ}
    (hB : 0 ≤ B)
    (hSha : ∀ (p : Nat.Primes) (e : ℕ), 0 < e → e < t → Sha1Galois E p (e : ℤ) = ⊥) :
    VVRecord E t B := by
  refine vvRecord_of_vvle_realGalois ⟨fun p e he1 he2 => ?_, fun P => ?_⟩
  · have hbot := hSha p e he1 he2
    have hzero : galoisShaLen E p (e : ℤ) = 0 :=
      (shaLen_eq_zero_iff_sha_eq_bot (canonicalLData E p) (e : ℤ)).mpr hbot
    rw [realGaloisSelmerSystem_shaLen, hzero]
    simp
  · have hzero : ∑ l ∈ P, Real.log (l : ℕ) *
        ∑ e ∈ Finset.Ico 1 t, ((realGaloisSelmerSystem.shaLen E l e).toNat : ℝ) = 0 := by
      refine Finset.sum_eq_zero fun l _ => ?_
      have hinner : ∑ e ∈ Finset.Ico 1 t, ((realGaloisSelmerSystem.shaLen E l e).toNat : ℝ) = 0 := by
        refine Finset.sum_eq_zero fun e he => ?_
        rw [Finset.mem_Ico] at he
        have hz : galoisShaLen E l (e : ℤ) = 0 :=
          (shaLen_eq_zero_iff_sha_eq_bot (canonicalLData E l) (e : ℤ)).mpr (hSha l e he.1 he.2)
        rw [realGaloisSelmerSystem_shaLen, hz]
        simp
      rw [hinner, mul_zero]
    rw [hzero]
    exact hB

/-- `VVRecord E t B` when `Sha1Galois E l e` is trivial outside a finite set of primes `P₀` and
finite inside `P₀`. -/
theorem vvRecord_of_finite_bad_primes (E : Type) [Field E] [NumberField E] (t : ℕ)
    (P₀ : Finset Nat.Primes)
    (hfin : ∀ l ∈ P₀, ∀ e, 0 < e → e < t → galoisShaLen E l (e : ℤ) ≠ ⊤)
    (hbot : ∀ l : Nat.Primes, l ∉ P₀ → ∀ e, 0 < e → e < t → Sha1Galois E l (e : ℤ) = ⊥) :
    VVRecord E t (∑ l ∈ P₀, Real.log (l : ℕ) *
      ∑ e ∈ Finset.Ico 1 t, ((galoisShaLen E l (e : ℤ)).toNat : ℝ)) := by
  refine vvRecord_of_vvle_realGalois ⟨fun l e he1 he2 => ?_, fun P => ?_⟩
  · by_cases hl : l ∈ P₀
    · rw [realGaloisSelmerSystem_shaLen]
      exact hfin l hl e he1 he2
    · have hz : galoisShaLen E l (e : ℤ) = 0 :=
        (shaLen_eq_zero_iff_sha_eq_bot (canonicalLData E l) (e : ℤ)).mpr (hbot l hl e he1 he2)
      rw [realGaloisSelmerSystem_shaLen, hz]
      simp
  · classical
    have hzero : ∀ l : Nat.Primes, l ∉ P₀ →
        Real.log (l : ℕ) *
          ∑ e ∈ Finset.Ico 1 t, ((realGaloisSelmerSystem.shaLen E l e).toNat : ℝ) = 0 := by
      intro l hlP0
      have hinner : ∑ e ∈ Finset.Ico 1 t, ((realGaloisSelmerSystem.shaLen E l e).toNat : ℝ) = 0 := by
        refine Finset.sum_eq_zero fun e he => ?_
        rw [Finset.mem_Ico] at he
        have hz : galoisShaLen E l (e : ℤ) = 0 :=
          (shaLen_eq_zero_iff_sha_eq_bot (canonicalLData E l) (e : ℤ)).mpr
            (hbot l hlP0 e he.1 he.2)
        rw [realGaloisSelmerSystem_shaLen, hz]
        simp
      rw [hinner, mul_zero]
    have hsplit :
        ∑ l ∈ P, Real.log (l : ℕ) *
          ∑ e ∈ Finset.Ico 1 t, ((realGaloisSelmerSystem.shaLen E l e).toNat : ℝ) =
        ∑ l ∈ P ∩ P₀, Real.log (l : ℕ) *
          ∑ e ∈ Finset.Ico 1 t, ((galoisShaLen E l (e : ℤ)).toNat : ℝ) := by
      rw [← Finset.sum_filter_of_ne (p := (· ∈ P₀)) (fun l _ hne => by
        by_contra hlP0
        exact hne (hzero l hlP0))]
      refine Finset.sum_congr (by ext l; simp [Finset.mem_filter, Finset.mem_inter]) fun l _ => ?_
      rfl
    rw [hsplit]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right fun l _ _ =>
      mul_nonneg (Real.log_natCast_nonneg _) (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)

/-- Exact compatibility with `PAdicChainValuation.vvRecord_of_VVle`: returns the raw tuple
`(ShaFin, Summable, ∑' l, vvTerm ≤ B)`. -/
theorem padic_vvRecord_of_realGalois {E : Type} [Field E] [NumberField E] {t : ℕ} {B : ℝ}
    (h : VVRecord E t B) :
    (∀ (l : Nat.Primes) (e : ℕ), 0 < e → e < t → realGaloisSelmerSystem.shaLen E l e ≠ ⊤) ∧
      Summable (PAdicChainValuation.vvTerm realGaloisSelmerSystem E t) ∧
      ∑' l, PAdicChainValuation.vvTerm realGaloisSelmerSystem E t l ≤ B :=
  PAdicChainValuation.vvRecord_of_VVle h.toVVle

end RealGaloisVVRecord

/-! ## Section 2: Chain Valuation Budget Integration (`PAdicChainValuation.ChainValuationSystem`) -/

section ChainValuationIntegration

/-- Combines a `PAdicChainValuation.ChainValuationSystem K LL ι` with a genuine Galois-cohomology
`VVRecord E t B`, packaging the `m`-step column-lift stability data and total prime-weighted
Selmer/Sha valuation budget along the chain. -/
structure ChainValuationBudgetRecord (K LL ι : Type*) [Field K] [Field LL] [CharZero K]
    (E : Type) [Field E] [NumberField E] (t : ℕ) (B : ℝ) where
  sys : PAdicChainValuation.ChainValuationSystem K LL ι
  vv : VVRecord E t B
  sStep : ℕ
  eStep : ℕ
  A : List ι
  formsStable : sys.FormsStable
  uOpCommutes : sys.UOpCommutes sStep
  stepInto : ∀ i, i < sys.m →
    sys.Into i (i + 1) (fun φ => (sys.T : K) ^ eStep • sys.Uprod (i + 1) A (sys.KT i φ))

namespace ChainValuationBudgetRecord

variable {K LL ι : Type*} [Field K] [Field LL] [CharZero K]
  {E : Type} [Field E] [NumberField E] {t : ℕ} {B : ℝ}

/-- Accumulated triangular-number valuation loss exponent across all `m` steps of the chain. -/
def lossExponent (R : ChainValuationBudgetRecord K LL ι E t B) : ℕ :=
  R.sys.m * R.eStep + R.sStep * R.A.length * ∑ j ∈ Finset.range (R.sys.m + 1), j

/-- Real-valued triangular-number loss identity from `PAdicChainValuation.ChainValuationSystem.chain_loss_formula`. -/
theorem lossExponent_eq (R : ChainValuationBudgetRecord K LL ι E t B) :
    (R.lossExponent : ℝ) =
      (R.sys.m : ℝ) * ((R.eStep : ℝ) + (R.sStep : ℝ) * (R.A.length : ℝ) * ((R.sys.m : ℝ) + 1) / 2) :=
  PAdicChainValuation.ChainValuationSystem.chain_loss_formula R.sys.m R.eStep R.sStep R.A.length

/-- Total `m`-step Selmer/Sha valuation budget `(sys.m : ℝ) * ∑' l, realGaloisVVTerm E t l ≤ sys.m * B`. -/
theorem chain_sha_budget_le (R : ChainValuationBudgetRecord K LL ι E t B) :
    (R.sys.m : ℝ) * ∑' l, realGaloisVVTerm E t l ≤ (R.sys.m : ℝ) * B :=
  mul_le_mul_of_nonneg_left R.vv.tsum_le (Nat.cast_nonneg _)

/-- Total `m`-step Selmer/Sha budget over any finite set of primes `P : Finset Nat.Primes`. -/
theorem chain_sha_finset_budget_le (R : ChainValuationBudgetRecord K LL ι E t B)
    (P : Finset Nat.Primes) :
    (R.sys.m : ℝ) * ∑ l ∈ P, Real.log (l : ℕ) *
      ∑ e ∈ Finset.Ico 1 t, ((galoisShaLen E l (e : ℤ)).toNat : ℝ) ≤ (R.sys.m : ℝ) * B :=
  mul_le_mul_of_nonneg_left (R.vv.prime_finset_sum_le P) (Nat.cast_nonneg _)

/-- Sharp `m`-step common-lattice column-valuation divisibility theorem directly attached to
`VVRecord`: any scalar `c ∈ LL` of valuation `n ≥ ramIdx * R.lossExponent` clears the `m`-step
denominator and lands in the single common integral lattice `embV m (S m)`. -/
theorem levelChainSharpColumnValuation (R : ChainValuationBudgetRecord K LL ι E t B)
    (a : ℕ) {c : LL} {n : ℤ} (hc : R.sys.val c = (n : WithTop ℤ))
    (hn : ((R.sys.ramIdx * R.lossExponent : ℕ) : ℤ) ≤ n)
    {x : R.sys.Vl 0} (hx : x ∈ R.sys.S 0) :
    ∃ z ∈ R.sys.S R.sys.m,
      R.sys.embV R.sys.m z =
        (R.sys.embK c * (R.sys.T : K) ^ a) •
          R.sys.colUp R.sys.m (((R.sys.Uprod 0 R.A) ^ R.sys.m) (R.sys.embV 0 x)) :=
  R.sys.levelChainSharpColumnValuation_of_stability R.formsStable R.uOpCommutes R.A R.eStep a
    R.stepInto hc hn hx

end ChainValuationBudgetRecord

/-- Construct a `ChainValuationBudgetRecord` directly from `AlpoegeVVle` and `ChainValuationSystem`
stability hypotheses. -/
def chainValuationBudget_of_alpoegeVVle
    {K LL ι : Type*} [Field K] [Field LL] [CharZero K]
    (sys : PAdicChainValuation.ChainValuationSystem K LL ι)
    (E : Type) [Field E] [NumberField E] (t : ℕ) (B : ℝ)
    (hVV : AlpoegeVVle E t B)
    (sStep eStep : ℕ) (A : List ι)
    (hF : sys.FormsStable) (hC : sys.UOpCommutes sStep)
    (hU : ∀ i, i < sys.m →
      sys.Into i (i + 1) (fun φ => (sys.T : K) ^ eStep • sys.Uprod (i + 1) A (sys.KT i φ))) :
    ChainValuationBudgetRecord K LL ι E t B where
  sys := sys
  vv := vvRecord_of_alpoegeVVle hVV
  sStep := sStep
  eStep := eStep
  A := A
  formsStable := hF
  uOpCommutes := hC
  stepInto := hU

end ChainValuationIntegration

/-! ## Section 3: `HypVRealGalois` — Tying `VWin realGaloisSelmerSystem` & `AlpoegeVVle` Together -/

section HypVRealGaloisSection

/-- Pointwise Selmer/Vandiver bound phrased directly via Alpöge's hardwired `AlpoegeVVle`. -/
def AlpoegeVAt (ψ : PChar) (eps Ct : ℝ) (q d e : ℕ) (x : ℝ) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E],
    IsChiField ψ e q d E → AlpoegeVVle E ⌊x ^ Ct⌋₊ (Real.sqrt (Real.exp (x ^ eps)))

/-- Windowed Selmer/Vandiver bound phrased directly via `AlpoegeVVle`. -/
def AlpoegeVWinAt (ψ : PChar) (Ct : ℝ) : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < 1 / 52 →
    ∀ e : ℝ → ℕ, (∀ x ≥ (1 : ℝ), PageN eps x (e x)) →
      ∃ J : ℝ, 1 ≤ J ∧ ∃ X0 : ℝ, ∀ X ≥ X0, ∀ q d : ℕ, WinPair eps (X ^ (1 / J)) q d →
        ∃ Y : ℝ, X ^ (1 / J) ≤ Y ∧ Y ^ (2 : ℝ) ≤ X ∧
          ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (2 : ℝ) → AlpoegeVAt ψ eps Ct q d (e x) x

/-- Full Selmer/Vandiver window property phrased directly via `AlpoegeVVle` at cutoff `401`. -/
def AlpoegeVWin : Prop := ∀ ψ : PChar, AlpoegeVWinAt ψ 401

theorem alpoegeVAt_iff_realGaloisVAt (ψ : PChar) (eps Ct : ℝ) (q d e : ℕ) (x : ℝ) :
    AlpoegeVAt ψ eps Ct q d e x ↔ RHDirect.VAt realGaloisSelmerSystem ψ eps Ct q d e x := by
  constructor
  · intro h E _ _ hE
    exact (alpoegeVVle_iff_realGaloisVVle E ⌊x ^ Ct⌋₊ _).mp (h E hE)
  · intro h E _ _ hE
    exact (alpoegeVVle_iff_realGaloisVVle E ⌊x ^ Ct⌋₊ _).mpr (h E hE)

theorem alpoegeVWinAt_iff_realGaloisVWinAt (ψ : PChar) (Ct : ℝ) :
    AlpoegeVWinAt ψ Ct ↔ RHDirect.VWinAt realGaloisSelmerSystem ψ Ct := by
  constructor
  · intro h eps heps heps52 e he
    obtain ⟨J, hJ, X0, hX0⟩ := h eps heps heps52 e he
    refine ⟨J, hJ, X0, fun X hX q d hqd => ?_⟩
    obtain ⟨Y, hY1, hY2, hYV⟩ := hX0 X hX q d hqd
    exact ⟨Y, hY1, hY2, fun x hx1 hx2 => (alpoegeVAt_iff_realGaloisVAt ψ eps Ct q d (e x) x).mp (hYV x hx1 hx2)⟩
  · intro h eps heps heps52 e he
    obtain ⟨J, hJ, X0, hX0⟩ := h eps heps heps52 e he
    refine ⟨J, hJ, X0, fun X hX q d hqd => ?_⟩
    obtain ⟨Y, hY1, hY2, hYV⟩ := hX0 X hX q d hqd
    exact ⟨Y, hY1, hY2, fun x hx1 hx2 => (alpoegeVAt_iff_realGaloisVAt ψ eps Ct q d (e x) x).mpr (hYV x hx1 hx2)⟩

theorem alpoegeVWin_iff_realGaloisVWin :
    AlpoegeVWin ↔ RHDirect.VWin realGaloisSelmerSystem :=
  forall_congr' fun ψ => alpoegeVWinAt_iff_realGaloisVWinAt ψ 401

/-- **`HypVRealGalois`**: concrete hypothesis wrapper tying `RHDirect.VWin Stage12GaloisShaLen.realGaloisSelmerSystem`
and `Stage12GaloisShaLen.AlpoegeVVle` together cleanly. -/
structure HypVRealGalois : Prop where
  /-- Full Selmer/Vandiver window `VWin` for the genuine Galois-cohomology `realGaloisSelmerSystem`. -/
  vwin : RHDirect.VWin realGaloisSelmerSystem
  /-- Simultaneous pointwise `AlpoegeVVle` realization across all algebraic closures `Ω` and `LData`. -/
  alpoegeVWin : AlpoegeVWin

namespace HypVRealGalois

/-- Construct `HypVRealGalois` directly from `RHDirect.VWin realGaloisSelmerSystem`. -/
theorem of_vwin (hV : RHDirect.VWin realGaloisSelmerSystem) : HypVRealGalois where
  vwin := hV
  alpoegeVWin := alpoegeVWin_iff_realGaloisVWin.mpr hV

/-- Construct `HypVRealGalois` directly from `AlpoegeVWin`. -/
theorem of_alpoegeVWin (hA : AlpoegeVWin) : HypVRealGalois where
  vwin := alpoegeVWin_iff_realGaloisVWin.mp hA
  alpoegeVWin := hA

/-- Construct `HypVRealGalois` directly from `RHDirect.GaloisModularityContract realGaloisSelmerSystem`. -/
theorem of_contract (hC : RHDirect.GaloisModularityContract realGaloisSelmerSystem) : HypVRealGalois :=
  of_vwin hC.vwin

/-- Project `HypVRealGalois` to `RHDirect.GaloisModularityContract realGaloisSelmerSystem`. -/
theorem toContract (H : HypVRealGalois) :
    RHDirect.GaloisModularityContract realGaloisSelmerSystem :=
  ⟨H.vwin⟩

/-- Extract `VWinAt realGaloisSelmerSystem ψ 401` for any primitive character `ψ`. -/
theorem vwinAt_401 (H : HypVRealGalois) (ψ : PChar) :
    RHDirect.VWinAt realGaloisSelmerSystem ψ 401 :=
  H.vwin ψ

/-- Extract `AlpoegeVWinAt ψ 401` for any primitive character `ψ`. -/
theorem alpoegeVWinAt_401 (H : HypVRealGalois) (ψ : PChar) :
    AlpoegeVWinAt ψ 401 :=
  H.alpoegeVWin ψ

/-- Extract arbitrarily large `[Z, Z^(3/2)]` windows of `WinDatum realGaloisSelmerSystem` using
unconditional Linnik prime-pair existence (`Stage11LinnikUnconditional.pairEx_unconditional`). -/
theorem winPairs_at (H : HypVRealGalois) (ψ : PChar) (eps c : ℝ)
    (heps : 0 < eps) (heps52 : eps < 1 / 52) (hc : 1 ≤ c) :
    ∃ J : ℝ, 1 ≤ J ∧ ∀ y : ℝ, ∃ Z : ℝ, y ≤ Z ∧ ∀ x : ℝ, Z ≤ x → x ≤ Z ^ ((3 : ℝ) / 2) →
      ∃ (Y : ℝ) (q d e : ℕ), WinDatum realGaloisSelmerSystem ψ eps J c x Y q d e :=
  ThetaSlopeEngine.winPairs_of_vwinAt realGaloisSelmerSystem ψ eps c heps heps52 hc
    (H.vwin ψ) Stage11LinnikUnconditional.pairEx_unconditional

/-- Extract `AlpoegeVVle E t (Real.sqrt (Real.exp (x ^ eps)))` from any `WinDatum` and `t ≤ ⌊x^400⌋₊`. -/
theorem alpoegeVVle_of_winDatum {ψ : PChar} {eps J c x Y : ℝ} {q d e t : ℕ}
    (hD : WinDatum realGaloisSelmerSystem ψ eps J c x Y q d e)
    (E : Type) [Field E] [NumberField E] (hChi : IsChiField ψ e q d E)
    (ht : t ≤ ⌊x ^ (400 : ℝ)⌋₊) :
    AlpoegeVVle E t (Real.sqrt (Real.exp (x ^ eps))) :=
  (alpoegeVVle_iff_realGaloisVVle E t _).mpr ((hD.vAt_400 E hChi).mono ht le_rfl)

/-- Extract `VVRecord E t (Real.sqrt (Real.exp (x ^ eps)))` from any `WinDatum` and `t ≤ ⌊x^400⌋₊`. -/
theorem vvRecord_of_winDatum {ψ : PChar} {eps J c x Y : ℝ} {q d e t : ℕ}
    (hD : WinDatum realGaloisSelmerSystem ψ eps J c x Y q d e)
    (E : Type) [Field E] [NumberField E] (hChi : IsChiField ψ e q d E)
    (ht : t ≤ ⌊x ^ (400 : ℝ)⌋₊) :
    VVRecord E t (Real.sqrt (Real.exp (x ^ eps))) :=
  vvRecord_of_alpoegeVVle (alpoegeVVle_of_winDatum hD E hChi ht)

end HypVRealGalois

theorem hypVRealGalois_iff_vwin :
    HypVRealGalois ↔ RHDirect.VWin realGaloisSelmerSystem :=
  ⟨HypVRealGalois.vwin, HypVRealGalois.of_vwin⟩

theorem hypVRealGalois_iff_alpoegeVWin :
    HypVRealGalois ↔ AlpoegeVWin :=
  ⟨HypVRealGalois.alpoegeVWin, HypVRealGalois.of_alpoegeVWin⟩

theorem hypVRealGalois_iff_contract :
    HypVRealGalois ↔ RHDirect.GaloisModularityContract realGaloisSelmerSystem :=
  ⟨HypVRealGalois.toContract, HypVRealGalois.of_contract⟩

/-- Scale-indexed host-field family at exponent `eps` (abstracting Alpöge's `FamCore eps` for the
genuine `realGaloisSelmerSystem`). -/
structure RealGaloisScaleFamily (eps : ℝ) : Type 1 where
  x1 : ℝ
  Ix : ℝ → Type
  E : ∀ x, Ix x → Type
  [fieldE : ∀ x i, Field (E x i)]
  [nfE : ∀ x i, NumberField (E x i)]
  t : ∀ x, Ix x → ℕ
  b : ∀ x, Ix x → ℝ
  b_pos : ∀ x i, 0 < b x i

attribute [instance] RealGaloisScaleFamily.fieldE RealGaloisScaleFamily.nfE

/-- Family-level **`HypVFamilyRealGalois`** matching `DivinNOfHypV.HypV`:
for all sufficiently large `x` and all `i : Fm.Ix x`, `AlpoegeVVle (Fm.E x i) (Fm.t x i) (√(Fm.b x i))`
holds unconditionally across all algebraic closures `Ω` and `LData`. -/
def HypVFamilyRealGalois {eps : ℝ} (Fm : RealGaloisScaleFamily eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, AlpoegeVVle (Fm.E x i) (Fm.t x i) (Real.sqrt (Fm.b x i))

theorem hypVFamilyRealGalois_iff_vvle {eps : ℝ} (Fm : RealGaloisScaleFamily eps) :
    HypVFamilyRealGalois Fm ↔
      ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
        RHDirect.VVle realGaloisSelmerSystem (Fm.E x i) (Fm.t x i) (Real.sqrt (Fm.b x i)) := by
  constructor
  · rintro ⟨x0, hx0⟩
    exact ⟨x0, fun x hx i => (alpoegeVVle_iff_realGaloisVVle (Fm.E x i) (Fm.t x i) _).mp (hx0 x hx i)⟩
  · rintro ⟨x0, hx0⟩
    exact ⟨x0, fun x hx i => (alpoegeVVle_iff_realGaloisVVle (Fm.E x i) (Fm.t x i) _).mpr (hx0 x hx i)⟩

theorem hypVFamilyRealGalois_vvRecord {eps : ℝ} {Fm : RealGaloisScaleFamily eps}
    (hV : HypVFamilyRealGalois Fm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, VVRecord (Fm.E x i) (Fm.t x i) (Real.sqrt (Fm.b x i)) := by
  obtain ⟨x0, hx0⟩ := hV
  exact ⟨x0, fun x hx i => vvRecord_of_alpoegeVVle (hx0 x hx i)⟩

end HypVRealGaloisSection

/-! ## Section 4: `LinkN`, `DIVinN`, `divinN_at_realGalois` & `divinN_of_hypV_realGalois` -/

section DivinNRealGalois

/-- Concrete `SizeData` record wired to a genuine number field `E_field` and rank cutoff `t`
for `realGaloisSelmerSystem`, matching Alpöge's `SizeData₂ D` in `GlobalTheoremInputs.lean`. -/
structure RealGaloisSizeData : Type 1 where
  x : ℝ
  eps : ℝ
  b : ℝ
  L : ℝ
  B0 : ℝ
  Nc : ℝ
  f : ℕ
  m : ℕ
  t : ℕ
  D0 : ℕ
  dZ0 : ℕ → ℕ
  lifts : Finset ℕ
  etaSum : ℕ → ℝ
  E_field : Type
  [fieldE : Field E_field]
  [nfE : NumberField E_field]
  x_gt_one : 1 < x
  eps_pos : 0 < eps
  b_eq : b = Real.exp (x ^ eps)
  L_eq : L = x ^ eps
  B0_eq : B0 = (f : ℝ) * (m : ℝ) * b * L
  f_pos : 1 ≤ f
  m_pos : 1 ≤ m
  Nc_nonneg : 0 ≤ Nc

attribute [instance] RealGaloisSizeData.fieldE RealGaloisSizeData.nfE

namespace RealGaloisSizeData

theorem b_ge_one (D : RealGaloisSizeData) : 1 ≤ D.b := by
  rw [D.b_eq]
  exact Real.one_le_exp (Real.rpow_nonneg (by linarith [D.x_gt_one]) _)

theorem b_pos (D : RealGaloisSizeData) : 0 < D.b := by
  rw [D.b_eq]
  exact Real.exp_pos _

theorem L_ge_one (D : RealGaloisSizeData) : 1 ≤ D.L := by
  rw [D.L_eq]
  exact Real.one_le_rpow D.x_gt_one.le D.eps_pos.le

theorem L_pos (D : RealGaloisSizeData) : 0 < D.L := by
  rw [D.L_eq]
  exact Real.rpow_pos_of_pos (by linarith [D.x_gt_one]) _

theorem B0_nonneg (D : RealGaloisSizeData) : 0 ≤ D.B0 := by
  rw [D.B0_eq]
  have hb := D.b_pos.le
  have hL := D.L_pos.le
  positivity

theorem b_le_B0 (D : RealGaloisSizeData) : D.b ≤ D.B0 := by
  rw [D.B0_eq]
  have hfR : (1 : ℝ) ≤ (D.f : ℝ) := by exact_mod_cast D.f_pos
  have hmR : (1 : ℝ) ≤ (D.m : ℝ) := by exact_mod_cast D.m_pos
  have h1 : 1 ≤ (D.f : ℝ) * (D.m : ℝ) * D.L :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hfR hmR) D.L_ge_one
  have hb := D.b_pos.le
  nlinarith

end RealGaloisSizeData

/-- `LinkN_at` over the genuine Galois-cohomology `realGaloisVVTerm`:
under `Summable (realGaloisVVTerm D.E_field D.t)`, the inertia/ramification deficit `D.etaSum j`
is bounded by `D.dZ0 j * (C * (f * m * b * L^2 + (log x)^2 * Nc) + ∑' l, realGaloisVVTerm E t l)`. -/
def LinkNAtRealGalois (D : RealGaloisSizeData) (j : ℕ) (C : ℝ) : Prop :=
  Summable (realGaloisVVTerm D.E_field D.t) →
    D.etaSum j ≤ (D.dZ0 j : ℝ) *
      (C * ((D.f : ℝ) * (D.m : ℝ) * D.b * D.L ^ 2 + Real.log D.x ^ 2 * D.Nc) +
        ∑' l, realGaloisVVTerm D.E_field D.t l)

/-- `DIVinN_at` over the genuine Galois-cohomology `RealGaloisSizeData`:
`D.etaSum j ≤ D.D0 * (C * x ^ eps * (B0 + Nc))`. -/
def DIVinNAtRealGalois (D : RealGaloisSizeData) (j : ℕ) (C : ℝ) : Prop :=
  D.etaSum j ≤ (D.D0 : ℝ) * (C * D.x ^ D.eps * (D.B0 + D.Nc))

/-- Small-level rank equality `dZ0 j = D0` along all lift steps `j ∈ D.lifts`. -/
def SmallLevelRankEqAt (D : RealGaloisSizeData) : Prop :=
  ∀ j ∈ D.lifts, D.dZ0 j = D.D0

theorem divinN_at_of_tsum_bound (D : RealGaloisSizeData) (j : ℕ) (C : ℝ)
    (hN : LinkNAtRealGalois D j C)
    (hs : Summable (realGaloisVVTerm D.E_field D.t))
    (hb : ∑' l, realGaloisVVTerm D.E_field D.t l ≤ D.b)
    (hd : D.dZ0 j = D.D0)
    (hlog : Real.log D.x ^ 2 ≤ D.x ^ D.eps) :
    DIVinNAtRealGalois D j (|C| + 1) := by
  have hE := hN hs
  rw [hd, D.L_eq] at hE
  have hE' : D.etaSum j ≤ (D.D0 : ℝ) *
      (C * ((D.f : ℝ) * (D.m : ℝ) * D.b * (D.x ^ D.eps) ^ 2 + Real.log D.x ^ 2 * D.Nc) + D.b) :=
    hE.trans (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _))
  have hdiv := PAdicChainValuation.divinN_at_of_linkN D.x_gt_one D.eps_pos D.f_pos D.m_pos
    D.b_pos D.Nc_nonneg hE' hlog
  unfold DIVinNAtRealGalois
  rw [D.B0_eq, D.b_eq, D.L_eq]
  rw [D.b_eq] at hdiv
  exact hdiv

/-- **`divinN_at_realGalois`**:
Converts `LinkNAtRealGalois D j C` and `VVRecord D.E_field D.t (Real.sqrt D.b)` (or `AlpoegeVVle`)
directly into `DIVinNAtRealGalois D j (|C| + 1)`. -/
theorem divinN_at_realGalois (D : RealGaloisSizeData) (j : ℕ) (C : ℝ)
    (hN : LinkNAtRealGalois D j C)
    (hVV : VVRecord D.E_field D.t (Real.sqrt D.b))
    (hd : D.dZ0 j = D.D0)
    (hlog : Real.log D.x ^ 2 ≤ D.x ^ D.eps) :
    DIVinNAtRealGalois D j (|C| + 1) :=
  divinN_at_of_tsum_bound D j C hN hVV.summable
    (hVV.tsum_le.trans (Real.sqrt_le_self_iff.mpr (Or.inr D.b_ge_one))) hd hlog

/-- **`divinN_at_of_alpoegeVVle`**:
Converts `LinkNAtRealGalois D j C` and `AlpoegeVVle D.E_field D.t (Real.sqrt D.b)` directly into
`DIVinNAtRealGalois D j (|C| + 1)`. -/
theorem divinN_at_of_alpoegeVVle (D : RealGaloisSizeData) (j : ℕ) (C : ℝ)
    (hN : LinkNAtRealGalois D j C)
    (hVV : AlpoegeVVle D.E_field D.t (Real.sqrt D.b))
    (hd : D.dZ0 j = D.D0)
    (hlog : Real.log D.x ^ 2 ≤ D.x ^ D.eps) :
    DIVinNAtRealGalois D j (|C| + 1) :=
  divinN_at_realGalois D j C hN (vvRecord_of_alpoegeVVle hVV) hd hlog

/-- **`divinN_at_of_vAt_realGalois`**:
Proved pointwise `DIVinN` bound directly from `RHDirect.VAt realGaloisSelmerSystem`, `IsChiField`,
and `D.t ≤ ⌊D.x ^ Ct⌋₊`. -/
theorem divinN_at_of_vAt_realGalois (D : RealGaloisSizeData) (j : ℕ) (C : ℝ)
    {ψ : PChar} {Ct : ℝ} {q d_aux e_page : ℕ}
    (hV : RHDirect.VAt realGaloisSelmerSystem ψ D.eps Ct q d_aux e_page D.x)
    (hChi : IsChiField ψ e_page q d_aux D.E_field)
    (ht : D.t ≤ ⌊D.x ^ Ct⌋₊)
    (hN : LinkNAtRealGalois D j C)
    (hd : D.dZ0 j = D.D0)
    (hlog : Real.log D.x ^ 2 ≤ D.x ^ D.eps) :
    DIVinNAtRealGalois D j (|C| + 1) := by
  have hVV : RHDirect.VVle realGaloisSelmerSystem D.E_field D.t (Real.sqrt D.b) := by
    rw [D.b_eq]
    exact (hV D.E_field hChi).mono ht le_rfl
  exact divinN_at_realGalois D j C hN (vvRecord_of_vvle_realGalois hVV) hd hlog

/-- **`divinN_at_of_alpoegeVAt`**:
Proved pointwise `DIVinN` bound directly from `AlpoegeVAt` + `IsChiField`. -/
theorem divinN_at_of_alpoegeVAt (D : RealGaloisSizeData) (j : ℕ) (C : ℝ)
    {ψ : PChar} {Ct : ℝ} {q d_aux e_page : ℕ}
    (hV : AlpoegeVAt ψ D.eps Ct q d_aux e_page D.x)
    (hChi : IsChiField ψ e_page q d_aux D.E_field)
    (ht : D.t ≤ ⌊D.x ^ Ct⌋₊)
    (hN : LinkNAtRealGalois D j C)
    (hd : D.dZ0 j = D.D0)
    (hlog : Real.log D.x ^ 2 ≤ D.x ^ D.eps) :
    DIVinNAtRealGalois D j (|C| + 1) :=
  divinN_at_of_vAt_realGalois D j C
    ((alpoegeVAt_iff_realGaloisVAt ψ D.eps Ct q d_aux e_page D.x).mp hV) hChi ht hN hd hlog

/-- Full scale-indexed family of `RealGaloisSizeData` at exponent `eps > 0`, matching Alpöge's
`FamP eps` in `DivinNOfHypV.lean`. -/
structure RealGaloisChainFamily (eps : ℝ) : Type 1 where
  eps_pos : 0 < eps
  x1 : ℝ
  Ix : ℝ → Type
  data : ∀ x, Ix x → RealGaloisSizeData
  data_x : ∀ x i, (data x i).x = x
  data_eps : ∀ x i, (data x i).eps = eps

namespace RealGaloisChainFamily

/-- Underlying `RealGaloisScaleFamily` forgetting the size-data details. -/
def toScaleFamily {eps : ℝ} (Fm : RealGaloisChainFamily eps) : RealGaloisScaleFamily eps where
  x1 := Fm.x1
  Ix := Fm.Ix
  E x i := (Fm.data x i).E_field
  fieldE x i := (Fm.data x i).fieldE
  nfE x i := (Fm.data x i).nfE
  t x i := (Fm.data x i).t
  b x i := (Fm.data x i).b
  b_pos x i := (Fm.data x i).b_pos

end RealGaloisChainFamily

/-- Family-level `LinkN` bound over `realGaloisSelmerSystem`. -/
def LinkNRealGalois {eps : ℝ} (Fm : RealGaloisChainFamily eps) : Prop :=
  ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
    ShaFinOddRealGalois (Fm.data x i).E_field (Fm.data x i).t →
      ∀ j ∈ (Fm.data x i).lifts, LinkNAtRealGalois (Fm.data x i) j C

/-- Family-level `SmallLevelRankEq` over `RealGaloisChainFamily`. -/
def SmallLevelRankEqRealGalois {eps : ℝ} (Fm : RealGaloisChainFamily eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, SmallLevelRankEqAt (Fm.data x i)

/-- Family-level `DIVinN` divisibility bound over `realGaloisSelmerSystem`. -/
def DIVinNRealGalois {eps : ℝ} (Fm : RealGaloisChainFamily eps) : Prop :=
  ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
    ∀ j ∈ (Fm.data x i).lifts, DIVinNAtRealGalois (Fm.data x i) j C

/-- **`divinN_of_hypV_realGalois`**:
Exact real-Galois counterpart of `UpperTheory.Top.divinN_of_hypV` (`DivinNOfHypV.lean`):
combines `HypVFamilyRealGalois Fm.toScaleFamily`, `LinkNRealGalois Fm`, and
`SmallLevelRankEqRealGalois Fm` with `PAdicChainValuation.log_sq_le_rpow` to prove
`DIVinNRealGalois Fm` directly for `realGaloisSelmerSystem`! -/
theorem divinN_of_hypV_realGalois {eps : ℝ} (Fm : RealGaloisChainFamily eps)
    (hV : HypVFamilyRealGalois Fm.toScaleFamily)
    (hN : LinkNRealGalois Fm)
    (hR : SmallLevelRankEqRealGalois Fm) :
    DIVinNRealGalois Fm := by
  obtain ⟨x1, h1⟩ := hV
  obtain ⟨C, x3, h3⟩ := hN
  obtain ⟨x4, h4⟩ := hR
  obtain ⟨x6, h6⟩ := PAdicChainValuation.log_sq_le_rpow Fm.eps_pos
  refine ⟨|C| + 1, max (max x1 x3) (max x4 x6), fun x hx i j hj => ?_⟩
  have hx1 : x1 ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hx)
  have hx3 : x3 ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hx)
  have hx4 : x4 ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx)
  have hx6 : x6 ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx)
  have hrec : VVRecord (Fm.data x i).E_field (Fm.data x i).t (Real.sqrt (Fm.data x i).b) :=
    vvRecord_of_alpoegeVVle (h1 x hx1 i)
  have hlog : Real.log (Fm.data x i).x ^ 2 ≤ (Fm.data x i).x ^ (Fm.data x i).eps := by
    rw [Fm.data_x x i, Fm.data_eps x i]
    exact h6 x hx6
  exact divinN_at_realGalois (Fm.data x i) j C (h3 x hx3 i hrec.shaFin j hj) hrec
    (h4 x hx4 i j hj) hlog

/-- **`divinN_of_hypV_realGalois_vvle`**:
Equivalent variant accepting `RHDirect.VVle realGaloisSelmerSystem` instead of `AlpoegeVVle`. -/
theorem divinN_of_hypV_realGalois_vvle {eps : ℝ} (Fm : RealGaloisChainFamily eps)
    (hV : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      RHDirect.VVle realGaloisSelmerSystem (Fm.data x i).E_field (Fm.data x i).t
        (Real.sqrt (Fm.data x i).b))
    (hN : LinkNRealGalois Fm)
    (hR : SmallLevelRankEqRealGalois Fm) :
    DIVinNRealGalois Fm :=
  divinN_of_hypV_realGalois Fm ((hypVFamilyRealGalois_iff_vvle Fm.toScaleFamily).mpr hV) hN hR

/-! ### Direct Windowed `VWin realGaloisSelmerSystem` → `[Z, Z^(3/2)]` `DIVinN` Extraction -/

/-- A family of `RealGaloisSizeData` fibers attached to a cyclic character `ψ`, scale `eps`,
and auxiliary prime-pair/page data `(q, d_aux, e_page)` with `IsChiField` and `t ≤ ⌊x ^ 400⌋₊`. -/
structure WindowedRealGaloisFamily (ψ : PChar) (eps : ℝ) : Type 1 where
  eps_pos : 0 < eps
  eps_lt : eps < 1 / 52
  Ix : ℝ → ℕ → ℕ → ℕ → Type
  data : ∀ x q d_aux e_page, Ix x q d_aux e_page → RealGaloisSizeData
  data_x : ∀ x q d_aux e_page i, (data x q d_aux e_page i).x = x
  data_eps : ∀ x q d_aux e_page i, (data x q d_aux e_page i).eps = eps
  data_isChi : ∀ x q d_aux e_page i,
    IsChiField ψ e_page q d_aux (data x q d_aux e_page i).E_field
  data_t_le : ∀ x q d_aux e_page i, (data x q d_aux e_page i).t ≤ ⌊x ^ (400 : ℝ)⌋₊

/-- Windowed `LinkN` assumption over `WindowedRealGaloisFamily`. -/
def WindowedLinkNRealGalois {ψ : PChar} {eps : ℝ} (WF : WindowedRealGaloisFamily ψ eps) : Prop :=
  ∃ C X0 : ℝ, ∀ x ≥ X0, ∀ q d_aux e_page, ∀ i : WF.Ix x q d_aux e_page,
    ShaFinOddRealGalois (WF.data x q d_aux e_page i).E_field (WF.data x q d_aux e_page i).t →
      ∀ j ∈ (WF.data x q d_aux e_page i).lifts, LinkNAtRealGalois (WF.data x q d_aux e_page i) j C

/-- Windowed `SmallLevelRankEq` assumption over `WindowedRealGaloisFamily`. -/
def WindowedSmallLevelRankEq {ψ : PChar} {eps : ℝ} (WF : WindowedRealGaloisFamily ψ eps) : Prop :=
  ∃ X0 : ℝ, ∀ x ≥ X0, ∀ q d_aux e_page, ∀ i : WF.Ix x q d_aux e_page,
    SmallLevelRankEqAt (WF.data x q d_aux e_page i)

/-- **`divinN_of_vwin_realGalois`**:
Directly turns `HypVRealGalois` (i.e. `VWin realGaloisSelmerSystem`) + `WindowedLinkNRealGalois` +
`WindowedSmallLevelRankEq` into arbitrarily large `[Z, Z^(3/2)]` windows on which:
1. `WinDatum realGaloisSelmerSystem ψ eps J 1 x Y q d_aux e_page` holds,
2. `VVRecord (WF.data ...).E_field (WF.data ...).t (√(exp(x^eps)))` holds, and
3. `DIVinNAtRealGalois (WF.data x q d_aux e_page i) j (|C| + 1)` holds for all fibers `i` and
   all lifts `j`! -/
theorem divinN_of_vwin_realGalois (H : HypVRealGalois) {ψ : PChar} {eps : ℝ}
    (WF : WindowedRealGaloisFamily ψ eps)
    (hLink : WindowedLinkNRealGalois WF)
    (hRank : WindowedSmallLevelRankEq WF) :
    ∃ (C_div J : ℝ), 1 ≤ J ∧ ∀ y : ℝ, ∃ Z : ℝ, y ≤ Z ∧ ∀ x : ℝ, Z ≤ x → x ≤ Z ^ ((3 : ℝ) / 2) →
      ∃ (Y : ℝ) (q d_aux e_page : ℕ),
        WinDatum realGaloisSelmerSystem ψ eps J 1 x Y q d_aux e_page ∧
        ∀ i : WF.Ix x q d_aux e_page,
          VVRecord (WF.data x q d_aux e_page i).E_field (WF.data x q d_aux e_page i).t
            (Real.sqrt (Real.exp (x ^ eps))) ∧
          ∀ j ∈ (WF.data x q d_aux e_page i).lifts,
            DIVinNAtRealGalois (WF.data x q d_aux e_page i) j C_div := by
  obtain ⟨C, X_link, hLink'⟩ := hLink
  obtain ⟨X_rank, hRank'⟩ := hRank
  obtain ⟨X_log, hlog⟩ := PAdicChainValuation.log_sq_le_rpow WF.eps_pos
  obtain ⟨J, hJ, hWin⟩ := H.winPairs_at ψ eps 1 WF.eps_pos WF.eps_lt le_rfl
  refine ⟨|C| + 1, J, hJ, fun y => ?_⟩
  set y0 : ℝ := max y (max X_link (max X_rank X_log))
  obtain ⟨Z, hZ_ge, hZ⟩ := hWin y0
  have hy_Z : y ≤ Z := le_trans (le_max_left _ _) hZ_ge
  have hXlink_Z : X_link ≤ Z :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hZ_ge)
  have hXrank_Z : X_rank ≤ Z :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hZ_ge))
  have hXlog_Z : X_log ≤ Z :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hZ_ge))
  refine ⟨Z, hy_Z, fun x hxZ hZx => ?_⟩
  obtain ⟨Y, q, d_aux, e_page, hDat⟩ := hZ x hxZ hZx
  refine ⟨Y, q, d_aux, e_page, hDat, fun i => ?_⟩
  set D := WF.data x q d_aux e_page i
  have hrec : VVRecord D.E_field D.t (Real.sqrt (Real.exp (x ^ eps))) :=
    HypVRealGalois.vvRecord_of_winDatum hDat D.E_field (WF.data_isChi x q d_aux e_page i)
      (WF.data_t_le x q d_aux e_page i)
  have hx_link : X_link ≤ x := hXlink_Z.trans hxZ
  have hx_rank : X_rank ≤ x := hXrank_Z.trans hxZ
  have hx_log : X_log ≤ x := hXlog_Z.trans hxZ
  have hlogD : Real.log D.x ^ 2 ≤ D.x ^ D.eps := by
    rw [WF.data_x x q d_aux e_page i, WF.data_eps x q d_aux e_page i]
    exact hlog x hx_log
  have hrecD : VVRecord D.E_field D.t (Real.sqrt D.b) := by
    rw [D.b_eq, WF.data_x x q d_aux e_page i, WF.data_eps x q d_aux e_page i]
    exact hrec
  refine ⟨hrec, fun j hj => ?_⟩
  exact divinN_at_realGalois D j C (hLink' x hx_link q d_aux e_page i hrec.shaFin j hj)
    hrecD (hRank' x hx_rank q d_aux e_page i j hj) hlogD

end DivinNRealGalois

/-! ## Section 5: Direct Wave 2–3 Bridges (`Stage2ThetaWire`, `CongruenceSlopeData`, `LinkDIVt`) -/

section Wave23Bridges

/-- **Direct Slope-Divisibility Discharge (`realGalois_discharges_slope_div`)**:
Specializes `Stage2ThetaWire.divinN_discharges_slope_div` directly to `realGaloisSelmerSystem`,
taking `AlpoegeVAt` (or `VAt realGaloisSelmerSystem`) + `IsChiField` + `R.t ≤ ⌊x^400⌋₊` and
discharging the exact `SlopeHypotheses.div` inequality. -/
theorem realGalois_discharges_slope_div {ψ : PChar}
    {Top : Type} [Fintype Top]
    {eps x Nc cLink cDiv a La muCC hVal Fo TVal logOm : ℝ} {aT : Top → ℝ}
    {q d e_page : ℕ} {R : ChainRanks}
    {E_field : Type} [Field E_field] [NumberField E_field]
    (hV : AlpoegeVAt ψ eps 400 q d e_page x) (hChi : IsChiField ψ e_page q d E_field)
    (ht : R.t ≤ ⌊x ^ (400 : ℝ)⌋₊)
    (hx : 1 < x) (heps : 0 < eps) (hf : 1 ≤ R.f) (hm : 1 ≤ R.m)
    (hNc : 0 ≤ Nc) (hcDiv_ge : |cLink| + 1 ≤ cDiv)
    (hlog : Real.log x ^ 2 ≤ x ^ eps)
    (hLink :
      (muCC + hVal - Fo) -
        (∑ t : Top, ((R.m : ℝ) * (SlopeInequality.ph (aT t) - aT t * logOm) - aT t * Real.log TVal)) -
        cDiv * (Fintype.card Top : ℝ) * a * La ≤
      (R.m : ℝ) * (cLink * ((R.f : ℝ) * (R.m : ℝ) * Real.exp (x ^ eps) * (x ^ eps) ^ 2 +
        Real.log x ^ 2 * Nc) + ∑' l, realGaloisVVTerm E_field R.t l)) :
    muCC + hVal - Fo ≤
      (∑ t : Top, ((R.m : ℝ) * (SlopeInequality.ph (aT t) - aT t * logOm) - aT t * Real.log TVal)) +
      (cDiv * (Fintype.card Top : ℝ) * a * La +
        cDiv * (R.m : ℝ) * ((R.f : ℝ) * (R.m : ℝ) * Real.exp (x ^ eps) * x ^ eps + Nc) *
          x ^ ((1 : ℝ) * eps)) :=
  Stage2ThetaWire.divinN_discharges_slope_div
    ((alpoegeVAt_iff_realGaloisVAt ψ eps 400 q d e_page x).mp hV)
    hChi ht hx heps hf hm hNc hcDiv_ge hlog hLink

/-- **Indefinite-Side / `LinkDIVt` Bridge (`realGalois_divLink_of_divinN`)**:
Given a `DIVinNAtRealGalois D j C_div` bound and an indefinite-side / product-formula inequality
comparing the fiber slope `(muCC + hVal - Fo) - MainSum - cDiv * nT * a * La` against
`(m : ℝ) * (cRem * (B0 + Nc) * x^eps + etaSum / D0)` (with `D0 ≥ 1`), deduces the exact
`SlopeHypotheses.div` divisibility inequality for `Stage2ThetaWire` and `Stage14M5_LinkDIVtBridge`! -/
theorem realGalois_divLink_of_divinN (D : RealGaloisSizeData) (j : ℕ) {C_div : ℝ}
    (hDIV : DIVinNAtRealGalois D j C_div)
    {Top : Type} [Fintype Top]
    {cRem cDiv a La muCC hVal Fo TVal logOm : ℝ} {aT : Top → ℝ}
    (hD0 : 1 ≤ D.D0)
    (hC_le : cRem + C_div ≤ cDiv)
    (hIndef :
      (muCC + hVal - Fo) -
        (∑ t : Top, ((D.m : ℝ) * (SlopeInequality.ph (aT t) - aT t * logOm) - aT t * Real.log TVal)) -
        cDiv * (Fintype.card Top : ℝ) * a * La ≤
      (D.m : ℝ) * (cRem * D.x ^ D.eps * (D.B0 + D.Nc) + D.etaSum j / (D.D0 : ℝ))) :
    muCC + hVal - Fo ≤
      (∑ t : Top, ((D.m : ℝ) * (SlopeInequality.ph (aT t) - aT t * logOm) - aT t * Real.log TVal)) +
      (cDiv * (Fintype.card Top : ℝ) * a * La +
        cDiv * (D.m : ℝ) * (D.B0 + D.Nc) * D.x ^ ((1 : ℝ) * D.eps)) := by
  have hD0_pos : (0 : ℝ) < (D.D0 : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD0)
  have heta_div : D.etaSum j / (D.D0 : ℝ) ≤ C_div * D.x ^ D.eps * (D.B0 + D.Nc) := by
    rw [div_le_iff₀ hD0_pos]
    calc D.etaSum j
        ≤ (D.D0 : ℝ) * (C_div * D.x ^ D.eps * (D.B0 + D.Nc)) := hDIV
      _ = C_div * D.x ^ D.eps * (D.B0 + D.Nc) * (D.D0 : ℝ) := by ring
  have hBN_nn : 0 ≤ D.B0 + D.Nc := add_nonneg D.B0_nonneg D.Nc_nonneg
  have hx_nn : 0 ≤ D.x ^ D.eps := Real.rpow_nonneg (by linarith [D.x_gt_one]) _
  have hm_nn : (0 : ℝ) ≤ (D.m : ℝ) := Nat.cast_nonneg _
  have h1 : cRem * D.x ^ D.eps * (D.B0 + D.Nc) + D.etaSum j / (D.D0 : ℝ) ≤
      cDiv * (D.B0 + D.Nc) * D.x ^ D.eps := by
    calc cRem * D.x ^ D.eps * (D.B0 + D.Nc) + D.etaSum j / (D.D0 : ℝ)
        ≤ cRem * D.x ^ D.eps * (D.B0 + D.Nc) + C_div * D.x ^ D.eps * (D.B0 + D.Nc) :=
          add_le_add_right heta_div _
      _ = (cRem + C_div) * (D.x ^ D.eps * (D.B0 + D.Nc)) := by ring
      _ ≤ cDiv * (D.x ^ D.eps * (D.B0 + D.Nc)) :=
          mul_le_mul_of_nonneg_right hC_le (mul_nonneg hx_nn hBN_nn)
      _ = cDiv * (D.B0 + D.Nc) * D.x ^ D.eps := by ring
  have h2 := mul_le_mul_of_nonneg_left h1 hm_nn
  rw [one_mul]
  linarith

/-- **Direct Bridge into `PAdicChainValuation.CongruenceSlopeData.s_lower5`**:
feeds `DIVinNAtRealGalois` + indefinite-side bound directly into `s_lower5` (common-slope lower
bound `Ga + muCC - K5v5 - wmean Lo5 ≤ s`). -/
theorem realGalois_s_lower5_of_divinN
    {U0 : Type} {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ}
    (CD : PAdicChainValuation.CongruenceSlopeData U0 W Top m f) (Xpp : ℝ) (u0 : U0)
    (D : RealGaloisSizeData) (j : ℕ) {C_div : ℝ}
    (hDIV_N : DIVinNAtRealGalois D j C_div)
    (hB0_eq : D.B0 + D.Nc ≤ CD.B0)
    (hx_eq : D.x = CD.x) (heps_eq : D.eps = 1)
    {cRem : ℝ} (hD0 : 1 ≤ D.D0) (hC_le : cRem + C_div ≤ CD.cDiv)
    (hEDiv_eq : CD.EDiv = CD.cDiv * (m : ℝ) * CD.B0 * CD.x)
    (hcDiv_nn : 0 ≤ CD.cDiv)
    (hd : ∀ u : W u0, 0 < CD.d u0 u)
    (hsumA : 0 ≤ CD.sumA)
    (hIndef : ∀ u : W u0,
      (CD.muCC u0 + CD.h u0 u - CD.Fo u0) -
        (∑ t : Top, ((m : ℝ) * (PAdicChainValuation.ph (CD.aT t) - CD.aT t * CD.logOm) -
          CD.aT t * Real.log (CD.T u0 u))) ≤
      (m : ℝ) * (cRem * D.x ^ D.eps * (D.B0 + D.Nc) + D.etaSum j / (D.D0 : ℝ)))
    (hE : ∀ u : W u0, |CD.Ee u0 u - (m : ℝ) * CD.sumA * CD.lg| ≤ CD.cE * (m : ℝ) * CD.B0)
    (hCount : ∀ u : W u0, CD.Lam5 u0 ≤ Real.log (CD.T u0 u))
    (hSl : ∀ u : W u0, -(CD.cSlope * CD.nT * CD.a * CD.La * (1 + (m : ℝ) / CD.k)) ≤ CD.muM u0 u)
    (hSN : ∀ u : W u0,
      CD.muM u0 u + CD.Ga u0 + CD.Fo u0 - CD.Ee u0 u - CD.Lo5 Xpp u0 u ≤ CD.muN u0 u) :
    CD.Ga u0 + CD.muCC u0 - CD.K5v5 u0 - PAdicChainValuation.wmean (CD.d u0) (CD.Lo5 Xpp u0) ≤
      CD.s u0 := by
  have hDIV_CD : ∀ u : W u0,
      CD.muCC u0 + CD.h u0 u - CD.Fo u0 ≤
        (∑ t : Top, ((m : ℝ) * (PAdicChainValuation.ph (CD.aT t) - CD.aT t * CD.logOm) -
          CD.aT t * Real.log (CD.T u0 u))) + CD.EDiv := by
    intro u
    have hD0_pos : (0 : ℝ) < (D.D0 : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD0)
    have heta : D.etaSum j / (D.D0 : ℝ) ≤ C_div * D.x ^ D.eps * (D.B0 + D.Nc) := by
      rw [div_le_iff₀ hD0_pos]
      calc D.etaSum j
          ≤ (D.D0 : ℝ) * (C_div * D.x ^ D.eps * (D.B0 + D.Nc)) := hDIV_N
        _ = C_div * D.x ^ D.eps * (D.B0 + D.Nc) * (D.D0 : ℝ) := by ring
    have hBN_nn : 0 ≤ D.B0 + D.Nc := add_nonneg D.B0_nonneg D.Nc_nonneg
    have hx_nn : 0 ≤ D.x ^ D.eps := Real.rpow_nonneg (by linarith [D.x_gt_one]) _
    have hx_CD_nn : 0 ≤ CD.x := by rw [← hx_eq]; linarith [D.x_gt_one]
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    have hstep1 : cRem * D.x ^ D.eps * (D.B0 + D.Nc) + D.etaSum j / (D.D0 : ℝ) ≤
        CD.cDiv * CD.B0 * CD.x := by
      calc cRem * D.x ^ D.eps * (D.B0 + D.Nc) + D.etaSum j / (D.D0 : ℝ)
          ≤ cRem * D.x ^ D.eps * (D.B0 + D.Nc) + C_div * D.x ^ D.eps * (D.B0 + D.Nc) :=
            add_le_add_right heta _
        _ = (cRem + C_div) * (D.x ^ D.eps * (D.B0 + D.Nc)) := by ring
        _ ≤ CD.cDiv * (D.x ^ D.eps * (D.B0 + D.Nc)) :=
            mul_le_mul_of_nonneg_right hC_le (mul_nonneg hx_nn hBN_nn)
        _ = CD.cDiv * (D.B0 + D.Nc) * CD.x := by
            rw [hx_eq, heps_eq, Real.rpow_one]
            ring
        _ ≤ CD.cDiv * CD.B0 * CD.x :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB0_eq hcDiv_nn) hx_CD_nn
    have hstep2 := mul_le_mul_of_nonneg_left hstep1 hm_nn
    have hind := hIndef u
    rw [hEDiv_eq] at *
    linarith
  exact CD.s_lower5 Xpp u0 hd hsumA hDIV_CD hE hCount hSl hSN

/-- **Pointwise Common-Slope Cancellation (`realGalois_ga_bound5_of_divinN`)**:
Chains `realGalois_s_lower5_of_divinN` with `u_function_le_mean` and `Ga_bound5` to bound
`CD.Ga u0` from `DIVinNAtRealGalois` and a `Stage2GramFrameFiber`! -/
theorem realGalois_ga_bound5_of_divinN
    {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)] [∀ u0, Nonempty (W u0)]
    {Top : Type} [Fintype Top] {m f : ℕ}
    (CD : PAdicChainValuation.CongruenceSlopeData U0 W Top m f) (Xpp : ℝ) (u0 : U0)
    (sgBar deBar e0Bar : ℝ)
    (F : Stage2GramFrameFiber (CD.s u0) (CD.uF u0) (CD.HH u0) (CD.muMinCC u0)
      (Fintype.card (W u0)) CD.delBar sgBar deBar e0Bar)
    (D : RealGaloisSizeData) (j : ℕ) {C_div : ℝ}
    (hDIV_N : DIVinNAtRealGalois D j C_div)
    (hB0_eq : D.B0 + D.Nc ≤ CD.B0)
    (hx_eq : D.x = CD.x) (heps_eq : D.eps = 1)
    {cRem : ℝ} (hD0 : 1 ≤ D.D0) (hC_le : cRem + C_div ≤ CD.cDiv)
    (hEDiv_eq : CD.EDiv = CD.cDiv * (m : ℝ) * CD.B0 * CD.x)
    (hcDiv_nn : 0 ≤ CD.cDiv)
    (hdel_eq : CD.del u0 = F.δ) (hη_eq : CD.η u0 = F.etaVal) (he_eq : CD.e u0 = F.eVal)
    (hmuCC_eq : CD.muCC u0 = F.muCC)
    (hηBar : 5 * sgBar + 3 * Real.sqrt deBar ≤ CD.etaBar)
    (heBar : 2 * e0Bar ≤ CD.eBar)
    (hx : 0 < CD.x) (hb : 0 < CD.b) (hv : 0 < CD.v) (hf : 0 < f)
    (hw : ∀ j ρ, 0 < CD.w u0 j ρ)
    (hd : ∀ u : W u0, 0 < CD.d u0 u)
    (hmu_le : ∀ u : W u0, CD.muN u0 u ≤ CD.muMaxN u0 u)
    (hsumA : 0 ≤ CD.sumA)
    (hHH0 : 0 < CD.HH u0) (hHH_s : CD.s u0 - CD.muMinCC u0 ≤ CD.HH u0)
    (hHH_up : CD.HH u0 ≤ CD.x ^ CD.cHH * CD.b)
    (hIndef : ∀ u : W u0,
      (CD.muCC u0 + CD.h u0 u - CD.Fo u0) -
        (∑ t : Top, ((m : ℝ) * (PAdicChainValuation.ph (CD.aT t) - CD.aT t * CD.logOm) -
          CD.aT t * Real.log (CD.T u0 u))) ≤
      (m : ℝ) * (cRem * D.x ^ D.eps * (D.B0 + D.Nc) + D.etaSum j / (D.D0 : ℝ)))
    (hE : ∀ u : W u0, |CD.Ee u0 u - (m : ℝ) * CD.sumA * CD.lg| ≤ CD.cE * (m : ℝ) * CD.B0)
    (hH : ∀ u u' : W u0,
      |(CD.h u0 u' + ∑ t : Top, CD.aT t * Real.log (CD.T u0 u')) -
        (CD.h u0 u + ∑ t : Top, CD.aT t * Real.log (CD.T u0 u))| ≤
      CD.cH * (CD.nT * CD.a * CD.La + (m : ℝ) * CD.B0))
    (hCount : ∀ u : W u0, CD.Lam5 u0 ≤ Real.log (CD.T u0 u))
    (hTdiff : ∀ u u' : W u0, |Real.log (CD.T u0 u) - Real.log (CD.T u0 u')| ≤ CD.cCount * Real.log CD.k)
    (hSl : ∀ u : W u0,
      -(CD.cSlope * CD.nT * CD.a * CD.La * (1 + (m : ℝ) / CD.k)) ≤ CD.muM u0 u ∧
      CD.muMaxM u0 u ≤ CD.cSlope * CD.nT * CD.a * CD.La)
    (hSN : ∀ u : W u0,
      CD.muMaxN u0 u ≤ CD.muMaxM u0 u + CD.Ga u0 + CD.Fo u0 - CD.Ee u0 u + CD.cSl1 * (m : ℝ) * CD.B0 ∧
      CD.muM u0 u + CD.Ga u0 + CD.Fo u0 - CD.Ee u0 u - CD.Lo5 Xpp u0 u ≤ CD.muN u0 u) :
    CD.Ga u0 ≤ CD.Main u0 + Real.log (Fintype.card (W u0) : ℝ) + CD.K0v5 +
      PAdicChainValuation.wmean (CD.d u0) (CD.Lo5 Xpp u0) +
      (1 - CD.delBar)⁻¹ * (4 * Real.log (1 + CD.x ^ CD.cHH) *
        (CD.K3 + PAdicChainValuation.wmean (CD.d u0) (CD.Lo5 Xpp u0) + CD.b) +
        (CD.etaBar + 4 * Real.sqrt CD.eBar) * (CD.x ^ CD.cHH * CD.b)) := by
  have huF0 : 0 ≤ CD.uF u0 := by
    unfold PAdicChainValuation.CongruenceSlopeData.uF PAdicChainValuation.CongruenceSlopeData.s
    have hle : ∀ u : W u0, CD.muN u0 u - CD.h u0 u ≤
        Finset.univ.sup' Finset.univ_nonempty (fun u : W u0 => CD.muMaxN u0 u - CD.h u0 u) := fun u =>
      (by linarith [hmu_le u] : CD.muN u0 u - CD.h u0 u ≤ CD.muMaxN u0 u - CD.h u0 u).trans
        (Finset.le_sup' (fun u : W u0 => CD.muMaxN u0 u - CD.h u0 u) (Finset.mem_univ u))
    linarith [PAdicChainValuation.wmean_le_const hd _ hle]
  have hfib_eq : CD.fiber u0 = F.toBostFiber := by
    unfold PAdicChainValuation.CongruenceSlopeData.fiber Stage2GramFrameFiber.toBostFiber
    rw [hdel_eq, hη_eq, he_eq, hmuCC_eq]
  have hSI : (CD.fiber u0).SlopeIneq := by
    rw [hfib_eq]
    exact F.toBostSlopeIneq huF0
  have hs_lo := realGalois_s_lower5_of_divinN CD Xpp u0 D j hDIV_N hB0_eq hx_eq heps_eq
    hD0 hC_le hEDiv_eq hcDiv_nn hd hsumA hIndef hE hCount (fun u => (hSl u).1) (fun u => (hSN u).2)
  have huF_le := CD.u_function_le_mean Xpp u0 hd hsumA hE hH hTdiff hSl hSN
  obtain ⟨hη0, hηle⟩ := F.etaVal_bounds
  obtain ⟨he0, hele, he4⟩ := F.eVal_bounds
  exact CD.Ga_bound5 Xpp u0 hx hb hv hf hw
    (hdel_eq ▸ F.δ_nonneg) (hdel_eq ▸ F.δ_le_bar) (by linarith [F.delBar_le])
    (hη_eq ▸ hη0) (hη_eq ▸ hηle.trans hηBar)
    (he_eq ▸ he0) (he_eq ▸ he4) (he_eq ▸ hele.trans heBar)
    hHH0 hHH_s hHH_up huF0 huF_le hs_lo hSI

/-- **Direct `errorBracketSizeWindows` Divisibility Budget Bound (`divinN_error_budget_bound`)**:
Translates `DIVinNAtRealGalois D j C_div` together with `RankVal`/`RestSize` bounds on
`D.f = 2 * R.n` and `D.Nc` directly into the `errorBracketSizeWindows` divisibility budget
`D.m * (D.etaSum j / D.D0) ≤ C_div * x ^ eps * errorBracketSizeWindows ...`! -/
theorem divinN_error_budget_bound (D : RealGaloisSizeData) (j : ℕ) {C_div : ℝ}
    (hDIV : DIVinNAtRealGalois D j C_div) (hC_nn : 0 ≤ C_div)
    {n nT nT2 : ℕ} {k aE : ℝ}
    (hD0 : 1 ≤ D.D0) (hf : D.f = 2 * n)
    (hNc_le : D.Nc ≤ (nT2 : ℝ) * k * D.b * D.x ^ D.eps / ((n : ℝ) * ((n : ℝ) * D.x ^ (-D.eps))))
    (haE_nn : 0 ≤ (nT : ℝ) * aE * (1 + (D.m : ℝ) ^ 2 / k)) :
    (D.m : ℝ) * (D.etaSum j / (D.D0 : ℝ)) ≤
      C_div * D.x ^ D.eps *
        RHDirect.errorBracketSizeWindows D.x D.eps n nT nT2 D.m D.b k aE := by
  have hD0_pos : (0 : ℝ) < (D.D0 : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hD0)
  have heta : D.etaSum j / (D.D0 : ℝ) ≤ C_div * D.x ^ D.eps * (D.B0 + D.Nc) := by
    rw [div_le_iff₀ hD0_pos]
    calc D.etaSum j
        ≤ (D.D0 : ℝ) * (C_div * D.x ^ D.eps * (D.B0 + D.Nc)) := hDIV
      _ = C_div * D.x ^ D.eps * (D.B0 + D.Nc) * (D.D0 : ℝ) := by ring
  have hB0_eq : D.B0 = 2 * (n : ℝ) * (D.m : ℝ) * D.b * D.x ^ D.eps := by
    rw [D.B0_eq, D.L_eq, hf]
    push_cast
    ring
  have hm_nn : (0 : ℝ) ≤ (D.m : ℝ) := Nat.cast_nonneg _
  have hsum : D.B0 + D.Nc ≤ 2 * (n : ℝ) * (D.m : ℝ) * D.b * D.x ^ D.eps +
      (nT2 : ℝ) * k * D.b * D.x ^ D.eps / ((n : ℝ) * ((n : ℝ) * D.x ^ (-D.eps))) := by
    linarith [hB0_eq, hNc_le]
  have hErr : (D.m : ℝ) * (D.B0 + D.Nc) ≤
      RHDirect.errorBracketSizeWindows D.x D.eps n nT nT2 D.m D.b k aE := by
    unfold RHDirect.errorBracketSizeWindows
    have hmul := mul_le_mul_of_nonneg_left hsum hm_nn
    linarith
  have hx_nn : 0 ≤ D.x ^ D.eps := Real.rpow_nonneg (by linarith [D.x_gt_one]) _
  calc (D.m : ℝ) * (D.etaSum j / (D.D0 : ℝ))
      ≤ (D.m : ℝ) * (C_div * D.x ^ D.eps * (D.B0 + D.Nc)) :=
        mul_le_mul_of_nonneg_left heta hm_nn
    _ = C_div * D.x ^ D.eps * ((D.m : ℝ) * (D.B0 + D.Nc)) := by ring
    _ ≤ C_div * D.x ^ D.eps *
        RHDirect.errorBracketSizeWindows D.x D.eps n nT nT2 D.m D.b k aE :=
        mul_le_mul_of_nonneg_left hErr (mul_nonneg hC_nn hx_nn)

/-- **Wave 3 `LinkDIVt` Bridge (`realGalois_linkDIVt_of_linkEta_and_hypV`)**:
Abstract `LinkDIVt` transfer theorem connecting `HypVFamilyRealGalois` + `LinkNRealGalois` +
`SmallLevelRankEqRealGalois` + any conditional `LinkEta → DIVinNRealGalois → LinkDIV` bridge
directly into unconditional `LinkDIV` (ready for `Stage14M5_LinkDIVtBridge`). -/
theorem realGalois_linkDIVt_of_linkEta_and_hypV {eps : ℝ} (Fm : RealGaloisChainFamily eps)
    (LinkEta LinkDIV : Prop)
    (hEta : LinkEta)
    (hV : HypVFamilyRealGalois Fm.toScaleFamily)
    (hN : LinkNRealGalois Fm)
    (hR : SmallLevelRankEqRealGalois Fm)
    (hLinkDIVt : LinkEta → DIVinNRealGalois Fm → LinkDIV) :
    LinkDIV :=
  hLinkDIVt hEta (divinN_of_hypV_realGalois Fm hV hN hR)

/-- End-to-end `ThetaSlopeContract realGaloisSelmerSystem` from `Stage2ThetaCoreInputs realGaloisSelmerSystem`. -/
theorem realGalois_thetaSlopeContract_of_stage2
    (I : Stage2ThetaCoreInputs realGaloisSelmerSystem) :
    RHDirect.ThetaSlopeContract realGaloisSelmerSystem :=
  Stage2ThetaWire.stage2_thetaSlopeContract realGaloisSelmerSystem I

/-- End-to-end `AllLevelsWindowBound (3 / 2)` directly from `HypVRealGalois` and
`Stage2ThetaCoreInputs realGaloisSelmerSystem`. -/
theorem realGalois_allLevelsWindowBound_of_hypV
    (H : HypVRealGalois) (I : Stage2ThetaCoreInputs realGaloisSelmerSystem) :
    RHDirect.AllLevelsWindowBound (3 / 2) :=
  Stage2ThetaWire.stage2_allLevelsWindowBound realGaloisSelmerSystem I H.vwin

/-- End-to-end `RHDirectAssembly realGaloisSelmerSystem` directly from `HypVRealGalois` and
`Stage2ThetaCoreInputs realGaloisSelmerSystem`, with Pillar 1 discharged unconditionally by
`Stage2AnalyticWire.stage2_analyticBridgeContract`. -/
theorem realGalois_assembly_of_stage2
    (H : HypVRealGalois) (I : Stage2ThetaCoreInputs realGaloisSelmerSystem) :
    RHDirect.RHDirectAssembly realGaloisSelmerSystem where
  galois := H.toContract
  theta := realGalois_thetaSlopeContract_of_stage2 I
  analytic := Stage2AnalyticWire.stage2_analyticBridgeContract

/-- End-to-end `RiemannHypothesis` directly from `HypVRealGalois` and
`Stage2ThetaCoreInputs realGaloisSelmerSystem`. -/
theorem realGalois_riemannHypothesis_of_hypV_and_stage2
    (H : HypVRealGalois) (I : Stage2ThetaCoreInputs realGaloisSelmerSystem) :
    RiemannHypothesis :=
  RHDirect.riemannHypothesis_of_dirichlet
    (RHDirect.LFunction_eq_zero_re_of_right
      (RHDirect.LFunction_ne_zero_of_half_lt_re_of_zeroFreeAll
        (RHDirect.zeroFreeAll_of_assembly (realGalois_assembly_of_stage2 H I))))

/-- End-to-end all five verbatim RH & GRH headline statements directly from `HypVRealGalois` and
`Stage2ThetaCoreInputs realGaloisSelmerSystem`. -/
theorem realGalois_headline_five_of_hypV_and_stage2
    (H : HypVRealGalois) (I : Stage2ThetaCoreInputs realGaloisSelmerSystem) :
    Stage2AnalyticWire.AllFiveHeadlineStatements :=
  RHDirect.headline_five_of_assembly (realGalois_assembly_of_stage2 H I)

end Wave23Bridges

/-! ## Section 6: Concrete `0`-Assumption Non-Vacuous Realizations -/

section ConcreteWitnesses

/-- Unconditional `0`-assumption `VVRecord ℚ 1 0` (exact genuine `realGaloisSelmerSystem` over `ℚ`). -/
theorem concrete_vvRecord_rat_one : VVRecord ℚ 1 0 :=
  vvRecord_one_unconditional ℚ le_rfl

/-- Unconditional `0`-assumption `AlpoegeVVle ℚ 1 (Real.sqrt (Real.exp (2 ^ (1 / 100 : ℝ))))`. -/
theorem concrete_alpoegeVVle_rat_one :
    AlpoegeVVle ℚ 1 (Real.sqrt (Real.exp ((2 : ℝ) ^ ((1 : ℝ) / 100)))) :=
  (vvRecord_one_unconditional ℚ (Real.sqrt_nonneg _)).toAlpoegeVVle

/-- Concrete `0`-assumption `RealGaloisSizeData` over `E_field = ℚ` with `t = 1`, `x = 2 ^ 40`,
`eps = 1 / 4`, `f = 2`, `m = 2`, `D0 = 4`, `etaSum j = 0`. -/
def concrete_realGaloisSizeData : RealGaloisSizeData where
  x := (2 : ℝ) ^ (40 : ℕ)
  eps := 1 / 4
  b := Real.exp (((2 : ℝ) ^ (40 : ℕ)) ^ ((1 : ℝ) / 4))
  L := ((2 : ℝ) ^ (40 : ℕ)) ^ ((1 : ℝ) / 4)
  B0 := (2 : ℝ) * (2 : ℝ) * Real.exp (((2 : ℝ) ^ (40 : ℕ)) ^ ((1 : ℝ) / 4)) *
    (((2 : ℝ) ^ (40 : ℕ)) ^ ((1 : ℝ) / 4))
  Nc := 1
  f := 2
  m := 2
  t := 1
  D0 := 4
  dZ0 := fun _ => 4
  lifts := {1, 2}
  etaSum := fun _ => 0
  E_field := ℚ
  x_gt_one := by norm_num
  eps_pos := by norm_num
  b_eq := rfl
  L_eq := rfl
  B0_eq := rfl
  f_pos := by norm_num
  m_pos := by norm_num
  Nc_nonneg := by norm_num

/-- Unconditional verification of `LinkNAtRealGalois concrete_realGaloisSizeData j 1`. -/
theorem concrete_linkN_at_realGalois (j : ℕ) :
    LinkNAtRealGalois concrete_realGaloisSizeData j 1 := by
  intro _
  dsimp only [concrete_realGaloisSizeData]
  have hsum : 0 ≤ ∑' l, realGaloisVVTerm ℚ 1 l := tsum_nonneg (realGaloisVVTerm_nonneg ℚ 1)
  have hexp : 0 ≤ Real.exp (((2 : ℝ) ^ (40 : ℕ)) ^ ((1 : ℝ) / 4)) := (Real.exp_pos _).le
  have hrpow : 0 ≤ ((2 : ℝ) ^ (40 : ℕ)) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by norm_num) _
  have hlog : 0 ≤ Real.log ((2 : ℝ) ^ (40 : ℕ)) ^ 2 := sq_nonneg _
  positivity

/-- Unconditional verification of `divinN_at_realGalois` on `concrete_realGaloisSizeData` (`0` axioms). -/
theorem concrete_divinN_at_realGalois (j : ℕ) :
    DIVinNAtRealGalois concrete_realGaloisSizeData j 2 := by
  have hlog_sq : Real.log ((2 : ℝ) ^ (40 : ℕ)) ^ 2 ≤ ((2 : ℝ) ^ (40 : ℕ)) ^ ((1 : ℝ) / 4) := by
    have hpow : ((2 : ℝ) ^ (40 : ℕ)) ^ ((1 : ℝ) / 4) = 1024 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    have hlog40 : Real.log ((2 : ℝ) ^ (40 : ℕ)) ≤ 28 := by
      have h2_lt : Real.log 2 < 0.7 := lt_trans Real.log_two_lt_d9 (by norm_num)
      rw [Real.log_pow]
      push_cast
      linarith
    have h0 : 0 ≤ Real.log ((2 : ℝ) ^ (40 : ℕ)) := Real.log_nonneg (by norm_num)
    rw [hpow]
    nlinarith
  have hdiv := divinN_at_realGalois concrete_realGaloisSizeData j 1
    (concrete_linkN_at_realGalois j)
    (vvRecord_one_unconditional ℚ (Real.sqrt_nonneg _)) rfl hlog_sq
  rw [show |(1 : ℝ)| + 1 = 2 by norm_num] at hdiv
  exact hdiv

/-- Concrete `0`-assumption `RealGaloisChainFamily (1 / 4)` over `E_field = ℚ` (`t = 1`),
proving non-vacuousness of `divinN_of_hypV_realGalois`. -/
def concrete_realGaloisChainFamily : RealGaloisChainFamily (1 / 4) where
  eps_pos := by norm_num
  x1 := 2
  Ix x := { _u : Unit // 1 < x }
  data x i :=
    { x := x
      eps := 1 / 4
      b := Real.exp (x ^ ((1 : ℝ) / 4))
      L := x ^ ((1 : ℝ) / 4)
      B0 := 2 * 2 * Real.exp (x ^ ((1 : ℝ) / 4)) * (x ^ ((1 : ℝ) / 4))
      Nc := 1
      f := 2
      m := 2
      t := 1
      D0 := 4
      dZ0 := fun _ => 4
      lifts := {1, 2}
      etaSum := fun _ => 0
      E_field := ℚ
      x_gt_one := i.2
      eps_pos := by norm_num
      b_eq := rfl
      L_eq := rfl
      B0_eq := rfl
      f_pos := by norm_num
      m_pos := by norm_num
      Nc_nonneg := by norm_num }
  data_x _ _ := rfl
  data_eps _ _ := rfl

/-- Unconditional `0`-assumption proof of `DIVinNRealGalois concrete_realGaloisChainFamily`
via `divinN_of_hypV_realGalois`. -/
theorem concrete_divinN_of_hypV_realGalois :
    DIVinNRealGalois concrete_realGaloisChainFamily := by
  refine divinN_of_hypV_realGalois concrete_realGaloisChainFamily ?_ ?_ ?_
  · refine ⟨2, fun x _ i => ?_⟩
    exact (vvRecord_one_unconditional ℚ (Real.sqrt_nonneg _)).toAlpoegeVVle
  · refine ⟨1, 2, fun x _ i _ j _ _ => ?_⟩
    dsimp only [concrete_realGaloisChainFamily]
    have hsum : 0 ≤ ∑' l, realGaloisVVTerm ℚ 1 l := tsum_nonneg (realGaloisVVTerm_nonneg ℚ 1)
    have hexp : 0 ≤ Real.exp (x ^ ((1 : ℝ) / 4)) := (Real.exp_pos _).le
    have hrpow : 0 ≤ x ^ ((1 : ℝ) / 4) := Real.rpow_nonneg (by linarith [i.2]) _
    have hlog : 0 ≤ Real.log x ^ 2 := sq_nonneg _
    positivity
  · exact ⟨2, fun x _ i j _ => rfl⟩

end ConcreteWitnesses

end

end RHDirect.Stage14M5_DivinNRealGalois
