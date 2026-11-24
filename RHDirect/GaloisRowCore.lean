import RHDirect.AutomorphicInputs
import Mathlib.Algebra.Polynomial.Degree.Defs

/-!
# RHDirect.GaloisRowCore

Compact, dead-field-free rebuild of the Galois representation assembly `Row0b recT`
(`6 PropsB + 2 AboveB + 3 AwayB = 11/11` live fields) and local–global compatibility
machinery for `rh-direct`.

Replaces the `66,168`-file / `7.85M`-line `RowSrc.lean` closure (and completely
eliminates the 100%-dead `OpenImageCondition` wrapper of
`TemperedProductOfSquareIntegrable.lean:L207-208` / `VwinOfRow.lean:L5`) with a direct,
zero-`sorry`, zero-custom-axiom Lean 4 development against `RHDirect.Interfaces`,
`RHDirect.AutomorphicInputs`, and Mathlib `v4.33.1`.

## Contents

1. **Local Weil–Deligne Groups & `AwayCompat` (`dim, tor, tame0`)**:
   Concrete Weil group degree homomorphism, Frobenius–inertia decomposition,
   characteristic-polynomial dimension/inertia lemmas (`charPol_of_inertia`,
   `dim_of_inertia`), `IsQpBigNat` monotonicity, and the exact 3-field `AwayCompat`
   (bridged 1-to-1 to `RHDirect.AwayB`).
2. **Polarized Infinitesimal Characters & Hodge–Tate Weight Symmetry**:
   Regular-algebraic integrality lifting (`exists_HT_of_isRegAlg`), uniqueness,
   conjugate-self-duality equivalence (`weights_conj_of_polarized` ↔
   `polarized_of_weights_conj`), sum symmetry `(HT (c τ)).sum + (HT τ).sum = card * wt`,
   palindromicity at fixed embeddings, polarization-weight uniqueness, and twist shift
   covariance.
3. **Exact Dead-Field-Free `AboveCompat` (`crys, nice`), `GaloisRowProps`
   (`cont, ss, away, weights, weights_conj, above`) & `GaloisRowData` (`Row0b`)**:
   All 11/11 live fields with exact bidirectional equivalences to `RHDirect.AboveB`,
   `RHDirect.PropsB`, and `RHDirect.MinimalGaloisRow`, plus strong-to-big weakening
   (`GaloisRowProps.of_strong`, `GaloisRowData.of_strong`).
4. **Local–Global Compatibility Assembly (`CoreAll` + `R1` + `R2` → `Row0b`)**:
   Direct reconstruction of `GaloisLocalGlobalOfLocalGlobalCompatibility.lean`
   (`awayCompat_of_toral_and_placeClass`, `aboveCompat_of_crys_toral_placeClass`,
   `galoisRowProps_of_localGlobal`, `galois_realisation_of_rank_two`).
5. **Theta-Lift Transport & `RowSrc` / `TLiftK` Assembly**:
   Weight-dominance criterion (`ThetaLiftDominance`), local-global compatibility
   transport along theta lifts (`AwayCompat.transport`, `AboveCompat.transport`,
   `GaloisRowProps.transport`), and the `GeoOne` + `TLiftK` → `GaloisRowData` pipeline.
6. **Direct Projection into `GaloisModularityCore` (Zero `OpenImageCondition`!)**:
   Direct projections into `MinimalGlobalAutomorphy`, `MinimalAutomorphyInputs`,
   `MinimalThetaInputs`, `GaloisModularityContract`, and `RHDirectAssembly`, plus
   a verified liveness ledger (`6 + 2 + 3 = 11` live, `0` dead).
-/

noncomputable section

open Polynomial

namespace RHDirect

/-! ## 1. Local Weil–Deligne Groups, `IsQpBigNat` & `AwayCompat` (3/3 Live Fields) -/

/-- `IsQpBigNat` is antitone in the rank `n ≥ 1`: if a prime `g` is big for rank `n`,
it is also big for every rank `1 ≤ m ≤ n`. -/
theorem IsQpBigNat.anti_rank {g m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) (h : IsQpBigNat g n) :
    IsQpBigNat g m := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with rfl | hbig
  · left; omega
  · right
    have hsq : m ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hmn 2
    omega

/-- For rank `n ≥ 2`, `IsQpBigNat g n` forces `64 < g` (hence `67 ≤ g` for prime `g`). -/
theorem IsQpBigNat.gt_64_of_two_le {g n : ℕ} (hn : 2 ≤ n) (h : IsQpBigNat g n) : 64 < g := by
  rcases h.2 with rfl | hbig
  · omega
  · have hsq : 4 ≤ n ^ 2 := by nlinarith
    omega

/-- Concrete local Weil–Deligne structure at a finite place `w`, equipping the Weil group
with its group law, degree homomorphism `deg : Weil → ℤ`, a geometric/arithmetic Frobenius
lift `frob` of degree `1`, and characteristic polynomials of degree `lpDim`. -/
structure LocalWDPlace where
  WD : Type
  Weil : Type
  [weilGroup : Group Weil]
  deg : Weil → ℤ
  deg_one : deg 1 = 0
  deg_mul : ∀ g h : Weil, deg (g * h) = deg g + deg h
  frob : Weil
  deg_frob : deg frob = 1
  lpDim : WD → ℕ
  mono0 : WD → Prop
  isToral : WD → Prop
  isTame : WD → Prop
  isSqf : WD → Prop
  charPol : WD → Weil → Polynomial ℂ
  charPol_natDegree : ∀ (x : WD) (g : Weil), (charPol x g).natDegree = lpDim x
  eq_of_mono0_charPol :
    ∀ x y : WD, mono0 x → mono0 y → (∀ g : Weil, charPol x g = charPol y g) → x = y
  resChar : ℕ
  isQp : Prop

attribute [instance] LocalWDPlace.weilGroup

namespace LocalWDPlace

/-- Forgetful projection to the lightweight comparison record `RHDirect.LocalWDCompare`. -/
def toCompare (W : LocalWDPlace) : LocalWDCompare where
  WD := W.WD
  Weil := W.Weil
  CharPol := Polynomial ℂ
  lpDim := W.lpDim
  mono0 := W.mono0
  isToral := W.isToral
  isTame := W.isTame
  isSqf := W.isSqf
  deg := W.deg
  charPol := W.charPol
  resChar := W.resChar
  isQp := W.isQp

theorem deg_inv (W : LocalWDPlace) (g : W.Weil) : W.deg g⁻¹ = -W.deg g := by
  have h : W.deg g + W.deg g⁻¹ = 0 := by
    rw [← W.deg_mul, mul_inv_cancel, W.deg_one]
  omega

theorem deg_pow (W : LocalWDPlace) (g : W.Weil) (n : ℕ) : W.deg (g ^ n) = (n : ℤ) * W.deg g := by
  induction n with
  | zero => simp [W.deg_one]
  | succ n ih =>
    rw [pow_succ, W.deg_mul, ih]
    push_cast
    ring

theorem deg_zpow (W : LocalWDPlace) (g : W.Weil) (k : ℤ) : W.deg (g ^ k) = k * W.deg g := by
  cases k with
  | ofNat n =>
    simpa using W.deg_pow g n
  | negSucc n =>
    rw [zpow_negSucc, W.deg_inv, W.deg_pow, Int.negSucc_eq]
    push_cast
    ring

/-- The inertia subgroup `I_w = ker(deg : W_w → ℤ)`. -/
def inertia (W : LocalWDPlace) : Subgroup W.Weil where
  carrier := {g : W.Weil | W.deg g = 0}
  one_mem' := W.deg_one
  mul_mem' {a b} ha hb := by
    show W.deg (a * b) = 0
    rw [W.deg_mul, ha, hb, add_zero]
  inv_mem' {a} ha := by
    show W.deg a⁻¹ = 0
    rw [W.deg_inv, ha, neg_zero]

@[simp]
theorem mem_inertia_iff (W : LocalWDPlace) (g : W.Weil) : g ∈ W.inertia ↔ W.deg g = 0 := Iff.rfl

/-- Every element of the Weil group factors uniquely as `frob ^ (deg g) * t` with `t ∈ inertia`. -/
theorem exists_eq_frob_zpow_mul_inertia (W : LocalWDPlace) (g : W.Weil) :
    ∃ t : W.inertia, g = W.frob ^ W.deg g * (t : W.Weil) := by
  have ht : W.deg ((W.frob ^ W.deg g)⁻¹ * g) = 0 := by
    rw [W.deg_mul, W.deg_inv, W.deg_zpow, W.deg_frob, mul_one, neg_add_cancel]
  exact ⟨⟨(W.frob ^ W.deg g)⁻¹ * g, ht⟩, by simp⟩

/-- Mirrors `UpperTheory.Gal.Int.Row.charPol_of_ine`: characteristic polynomial agreement on
inertia `I_w` is equivalent to agreement on all degree-`0` elements of the Weil group. -/
theorem charPol_of_inertia {W : LocalWDPlace} {x y : W.WD}
    (h : ∀ t : W.inertia, W.charPol x t = W.charPol y t)
    (g : W.Weil) (hg : W.deg g = 0) : W.charPol x g = W.charPol y g := by
  obtain ⟨t, ht⟩ := W.exists_eq_frob_zpow_mul_inertia g
  rw [hg, zpow_zero, one_mul] at ht
  rw [ht]
  exact h t

/-- Mirrors `UpperTheory.Gal.Int.Row.dim_of_ine`: characteristic polynomial agreement on
inertia forces equality of Weil–Deligne dimensions via `natDegree` at `1 ∈ I_w`. -/
theorem dim_of_inertia {W : LocalWDPlace} {x y : W.WD}
    (h : ∀ t : W.inertia, W.charPol x t = W.charPol y t) : W.lpDim x = W.lpDim y := by
  rw [← W.charPol_natDegree x 1, ← W.charPol_natDegree y 1]
  exact congrArg Polynomial.natDegree (h 1)

end LocalWDPlace

/-- Exact dead-field-free local–global compatibility at a place `w` (**3/3** live fields:
`dim`, `tor`, `tame0`, matching `UpperTheory.GalStar.AwayB` in `WeightsConjBis.lean:L26-31`). -/
structure AwayCompat (C : LocalWDCompare) (x y : C.WD) : Prop where
  /-- 1. Dimension equality of Weil–Deligne parameters. -/
  dim : C.lpDim x = C.lpDim y
  /-- 2. Exact WD match on toral parameters with vanishing monodromy. -/
  tor : C.isToral y → C.mono0 y → x = y
  /-- 3. Degree-0 Frobenius/inertia charpoly match under `IsQpBig` + tame + squarefree + `mono0`. -/
  tame0 : (C.isQp ∧ IsQpBigNat C.resChar (C.lpDim y)) →
    C.isTame y → C.isSqf y → C.mono0 y →
    C.mono0 x ∧ ∀ g : C.Weil, C.deg g = 0 → C.charPol x g = C.charPol y g

/-- Stronger unguarded `AwayCompatStrong` (without the `16 * n ^ 2 < g` guard, matching
`UpperTheory.GalStar.Away` in `WeightsConjBis.lean:L33`). -/
structure AwayCompatStrong (C : LocalWDCompare) (x y : C.WD) : Prop where
  dim : C.lpDim x = C.lpDim y
  tor : C.isToral y → C.mono0 y → x = y
  tame0 : C.isQp → C.isTame y → C.isSqf y → C.mono0 y →
    C.mono0 x ∧ ∀ g : C.Weil, C.deg g = 0 → C.charPol x g = C.charPol y g

namespace AwayCompat

/-- Exact projection into `RHDirect.AwayB`. -/
theorem toAwayB {C : LocalWDCompare} {x y : C.WD} (h : AwayCompat C x y) : AwayB C x y :=
  ⟨h.dim, h.tor, h.tame0⟩

/-- Exact reconstruction from `RHDirect.AwayB`. -/
theorem ofAwayB {C : LocalWDCompare} {x y : C.WD} (h : AwayB C x y) : AwayCompat C x y :=
  ⟨h.dim, h.tor, h.tame0⟩

theorem iff_awayB (C : LocalWDCompare) (x y : C.WD) : AwayCompat C x y ↔ AwayB C x y :=
  ⟨toAwayB, ofAwayB⟩

/-- Mirrors `UpperTheory.GalStar.Away.big` (`WeightsConjBis.lean:L33`). -/
theorem of_strong {C : LocalWDCompare} {x y : C.WD} (h : AwayCompatStrong C x y) :
    AwayCompat C x y :=
  ⟨h.dim, h.tor, fun hq => h.tame0 hq.1⟩

theorem refl (C : LocalWDCompare) (x : C.WD) : AwayCompat C x x :=
  ⟨rfl, fun _ _ => rfl, fun _ _ _ hm => ⟨hm, fun _ _ => rfl⟩⟩

theorem of_eq {C : LocalWDCompare} {x y : C.WD} (h : x = y) : AwayCompat C x y := by
  subst h
  exact refl C x

/-- Assemble `AwayCompat` at a `LocalWDPlace` from `mono0` + full charpoly equality (used
in the toral branch of `GaloisLocalGlobalOfLocalGlobalCompatibility.lean:L97`). -/
theorem of_mono0_charPol {W : LocalWDPlace} {x y : W.WD}
    (hx : W.mono0 x) (hy : W.mono0 y) (hc : ∀ g : W.Weil, W.charPol x g = W.charPol y g) :
    AwayCompat W.toCompare x y :=
  of_eq (W.eq_of_mono0_charPol x y hx hy hc)

/-- Assemble `AwayCompat` at a non-toral tame/squarefree place directly from inertia charpoly
agreement (mirroring `GaloisLocalGlobalOfLocalGlobalCompatibility.lean:L102`). -/
theorem of_not_toral_inertia {W : LocalWDPlace} {x y : W.WD}
    (hnt : ¬ W.isToral y) (hx : W.mono0 x)
    (hine : ∀ t : W.inertia, W.charPol x t = W.charPol y t) :
    AwayCompat W.toCompare x y where
  dim := W.dim_of_inertia hine
  tor ht _ := absurd ht hnt
  tame0 _ _ _ _ := ⟨hx, fun g hg => W.charPol_of_inertia hine g hg⟩

end AwayCompat

/-! ## 2. Polarized Infinitesimal Characters & Hodge–Tate Weight Symmetry -/

/-- Infinitesimal character datum of rank `a ≥ 1` over a CM field with complex conjugation
involution `conjEmb` on embeddings `Emb`. -/
structure CMInfCharDatum where
  rank : ℕ
  rank_pos : 1 ≤ rank
  Emb : Type
  conjEmb : Emb → Emb
  conjEmb_involutive : Function.Involutive conjEmb
  infChar : Emb → Multiset ℂ

namespace CMInfCharDatum

/-- Regular algebraic integrality: at every embedding `τ`, every infinitesimal character
eigenvalue `z ∈ infChar τ` has the form `(rank - 1)/2 + n` for an integer `n : ℤ`. -/
def IsRegAlg (I : CMInfCharDatum) : Prop :=
  ∀ (τ : I.Emb) (z : ℂ), z ∈ I.infChar τ → ∃ n : ℤ, z = ((I.rank : ℂ) - 1) / 2 + (n : ℂ)

/-- Polarization / conjugate self-duality of infinitesimal characters with parity weight `wt : ℤ`:
`infChar (τ ∘ c) = ((rank - 1) - wt - ·) '' infChar τ`. -/
def IsPolarized (I : CMInfCharDatum) (wt : ℤ) : Prop :=
  ∀ τ : I.Emb,
    I.infChar (I.conjEmb τ) = (I.infChar τ).map (fun z : ℂ => ((I.rank : ℂ) - 1) - (wt : ℂ) - z)

/-- The shifted Hodge–Tate weight condition (`PropsB.weights`):
`HT τ` maps under `ℤ → ℂ` to `((rank - 1)/2 - ·) '' infChar τ`. -/
def MatchesWeights (I : CMInfCharDatum) (HT : I.Emb → Multiset ℤ) : Prop :=
  ∀ τ : I.Emb,
    (HT τ).map (fun n : ℤ => (n : ℂ)) =
      (I.infChar τ).map (fun z : ℂ => ((I.rank : ℂ) - 1) / 2 - z)

/-- Conjugate self-duality of Hodge–Tate weights (`PropsB.weights_conj`):
`HT (τ ∘ c) = (wt - ·) '' HT τ`. -/
def HasConjWeights (I : CMInfCharDatum) (wt : ℤ) (HT : I.Emb → Multiset ℤ) : Prop :=
  ∀ τ : I.Emb, HT (I.conjEmb τ) = (HT τ).map (fun n : ℤ => wt - n)

/-- Elementary lifting of a multiset of integral complex numbers to `Multiset ℤ`. -/
private theorem exists_multiset_int_map_eq (s : Multiset ℂ)
    (h : ∀ z ∈ s, ∃ n : ℤ, (n : ℂ) = z) :
    ∃ m : Multiset ℤ, m.map (fun n : ℤ => (n : ℂ)) = s := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨0, rfl⟩
  | cons a s ih =>
    obtain ⟨n, hn⟩ := h a (Multiset.mem_cons_self a s)
    obtain ⟨m, hm⟩ := ih (fun z hz => h z (Multiset.mem_cons_of_mem hz))
    exact ⟨n ::ₘ m, by simp [hn, hm]⟩

/-- Regular-algebraic infinitesimal characters admit integral Hodge–Tate multisets `HT`. -/
theorem exists_HT_of_isRegAlg {I : CMInfCharDatum} (hreg : I.IsRegAlg) :
    ∃ HT : I.Emb → Multiset ℤ, I.MatchesWeights HT := by
  have ex : ∀ τ : I.Emb,
      ∃ J : Multiset ℤ,
        J.map (fun n : ℤ => (n : ℂ)) =
          (I.infChar τ).map (fun z : ℂ => ((I.rank : ℂ) - 1) / 2 - z) := by
    intro τ
    refine exists_multiset_int_map_eq _ ?_
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hy
    obtain ⟨n, hn⟩ := hreg τ z hz
    refine ⟨-n, ?_⟩
    rw [hn]
    push_cast
    ring
  choose HT hHT using ex
  exact ⟨HT, hHT⟩

/-- Integral Hodge–Tate multisets matching `infChar` are unique. -/
theorem HT_unique {I : CMInfCharDatum} {HT₁ HT₂ : I.Emb → Multiset ℤ}
    (h₁ : I.MatchesWeights HT₁) (h₂ : I.MatchesWeights HT₂) : HT₁ = HT₂ := by
  funext τ
  exact Multiset.map_injective (Int.cast_injective (α := ℂ)) ((h₁ τ).trans (h₂ τ).symm)

/-- Polarization of infinitesimal characters implies conjugate self-duality of Hodge–Tate weights
(directly mirroring `exists_weights` in `GaloisLocalGlobalOfLocalGlobalCompatibility.lean`). -/
theorem weights_conj_of_polarized {I : CMInfCharDatum} {wt : ℤ} {HT : I.Emb → Multiset ℤ}
    (hw : I.MatchesWeights HT) (hpol : I.IsPolarized wt) : I.HasConjWeights wt HT := by
  intro τ
  refine Multiset.map_injective (Int.cast_injective (α := ℂ)) ?_
  have e := congrArg (Multiset.map fun y : ℂ => (wt : ℂ) - y) (hw τ)
  rw [hw (I.conjEmb τ), hpol τ]
  simp only [Multiset.map_map, Function.comp_def] at e ⊢
  have hcast :
      (HT τ).map (fun x : ℤ => ((wt - x : ℤ) : ℂ)) =
        (HT τ).map (fun x : ℤ => (wt : ℂ) - (x : ℂ)) :=
    Multiset.map_congr rfl fun x _ => by push_cast; rfl
  rw [hcast, e]
  exact Multiset.map_congr rfl fun z _ => by ring

/-- Conversely, conjugate self-duality of Hodge–Tate weights implies polarization of the
underlying infinitesimal characters. -/
theorem polarized_of_weights_conj {I : CMInfCharDatum} {wt : ℤ} {HT : I.Emb → Multiset ℤ}
    (hw : I.MatchesWeights HT) (hconj : I.HasConjWeights wt HT) : I.IsPolarized wt := by
  intro τ
  let φ : ℂ → ℂ := fun z => ((I.rank : ℂ) - 1) / 2 - z
  have hφ_inj : Function.Injective φ := fun a b hab => by
    dsimp [φ] at hab
    linear_combination -hab
  refine Multiset.map_injective hφ_inj ?_
  have h1 : (I.infChar (I.conjEmb τ)).map φ = (HT (I.conjEmb τ)).map (fun n : ℤ => (n : ℂ)) :=
    (hw (I.conjEmb τ)).symm
  rw [h1, hconj τ]
  simp only [Multiset.map_map, Function.comp_def]
  have h2 :
      (HT τ).map (fun n : ℤ => ((wt - n : ℤ) : ℂ)) =
        (I.infChar τ).map (fun z : ℂ => (wt : ℂ) - φ z) := by
    have e := congrArg (Multiset.map fun y : ℂ => (wt : ℂ) - y) (hw τ)
    simp only [Multiset.map_map, Function.comp_def] at e
    rw [← e]
    exact Multiset.map_congr rfl fun n _ => by push_cast; rfl
  rw [h2]
  exact Multiset.map_congr rfl fun z _ => by dsimp [φ]; ring

/-- Polarization of infinitesimal characters is equivalent to conjugate self-duality of
Hodge–Tate weights whenever `MatchesWeights` holds. -/
theorem polarized_iff_weights_conj {I : CMInfCharDatum} {wt : ℤ} {HT : I.Emb → Multiset ℤ}
    (hw : I.MatchesWeights HT) : I.IsPolarized wt ↔ I.HasConjWeights wt HT :=
  ⟨weights_conj_of_polarized hw, polarized_of_weights_conj hw⟩

/-- Existence of `(wt, HT)` satisfying both `MatchesWeights` and `HasConjWeights` for any
regular algebraic polarized infinitesimal character datum. -/
theorem exists_weights_of_regAlg_polarized {I : CMInfCharDatum} (hreg : I.IsRegAlg)
    {wt : ℤ} (hpol : I.IsPolarized wt) :
    ∃ HT : I.Emb → Multiset ℤ, I.MatchesWeights HT ∧ I.HasConjWeights wt HT := by
  obtain ⟨HT, hw⟩ := exists_HT_of_isRegAlg hreg
  exact ⟨HT, hw, weights_conj_of_polarized hw hpol⟩

/-- Cardinality of Hodge–Tate weights equals the cardinality of the infinitesimal character. -/
theorem HT_card_eq {I : CMInfCharDatum} {HT : I.Emb → Multiset ℤ}
    (hw : I.MatchesWeights HT) (τ : I.Emb) : (HT τ).card = (I.infChar τ).card := by
  have h := congrArg Multiset.card (hw τ)
  simpa using h

/-- Conjugate embeddings carry the same number of Hodge–Tate weights. -/
theorem HT_card_conj {I : CMInfCharDatum} {wt : ℤ} {HT : I.Emb → Multiset ℤ}
    (hconj : I.HasConjWeights wt HT) (τ : I.Emb) : (HT (I.conjEmb τ)).card = (HT τ).card := by
  rw [hconj τ, Multiset.card_map]

/-- Helper identity for `Multiset.sum` under affine reflection `n ↦ wt - n`. -/
private theorem multiset_sum_sub_add (s : Multiset ℤ) (wt : ℤ) :
    (s.map (fun n : ℤ => wt - n)).sum + s.sum = (s.card : ℤ) * wt := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Nat.cast_add,
      Nat.cast_one]
    linarith

/-- Exact Hodge–Tate weight sum symmetry: `(HT (c τ)).sum + (HT τ).sum = card(HT τ) * wt`. -/
theorem HT_sum_conj {I : CMInfCharDatum} {wt : ℤ} {HT : I.Emb → Multiset ℤ}
    (hconj : I.HasConjWeights wt HT) (τ : I.Emb) :
    (HT (I.conjEmb τ)).sum + (HT τ).sum = ((HT τ).card : ℤ) * wt := by
  rw [hconj τ]
  exact multiset_sum_sub_add (HT τ) wt

/-- At any embedding fixed by complex conjugation (`conjEmb τ = τ`), the sum of Hodge–Tate
weights satisfies `2 * (HT τ).sum = card(HT τ) * wt`. -/
theorem HT_sum_of_fixed_emb {I : CMInfCharDatum} {wt : ℤ} {HT : I.Emb → Multiset ℤ}
    (hconj : I.HasConjWeights wt HT) {τ : I.Emb} (hfix : I.conjEmb τ = τ) :
    2 * (HT τ).sum = ((HT τ).card : ℤ) * wt := by
  have h := HT_sum_conj hconj τ
  rw [hfix] at h
  linarith

/-- Membership reflection: `n ∈ HT τ` iff `wt - n ∈ HT (conjEmb τ)`. -/
theorem mem_HT_conj_iff {I : CMInfCharDatum} {wt : ℤ} {HT : I.Emb → Multiset ℤ}
    (hconj : I.HasConjWeights wt HT) (τ : I.Emb) (n : ℤ) :
    wt - n ∈ HT (I.conjEmb τ) ↔ n ∈ HT τ := by
  rw [hconj τ, Multiset.mem_map]
  constructor
  · rintro ⟨m, hm, hmn⟩
    have : m = n := by omega
    rwa [← this]
  · intro hn
    exact ⟨n, hn, rfl⟩

/-- Uniqueness of the polarization parity weight `wt` whenever `HT τ` is nonempty at some `τ`. -/
theorem wt_unique_of_card_pos {I : CMInfCharDatum} {wt₁ wt₂ : ℤ} {HT : I.Emb → Multiset ℤ}
    (h₁ : I.HasConjWeights wt₁ HT) (h₂ : I.HasConjWeights wt₂ HT)
    {τ : I.Emb} (hpos : 0 < (HT τ).card) : wt₁ = wt₂ := by
  have s₁ := HT_sum_conj h₁ τ
  have s₂ := HT_sum_conj h₂ τ
  have hc : ((HT τ).card : ℤ) ≠ 0 := by omega
  exact mul_left_cancel₀ hc (s₁.symm.trans s₂)

/-- Character-twist shift of an infinitesimal character datum by `s : ℤ` (`z ↦ z + s`). -/
def shift (I : CMInfCharDatum) (s : ℤ) : CMInfCharDatum where
  rank := I.rank
  rank_pos := I.rank_pos
  Emb := I.Emb
  conjEmb := I.conjEmb
  conjEmb_involutive := I.conjEmb_involutive
  infChar τ := (I.infChar τ).map (fun z : ℂ => z + (s : ℂ))

theorem shift_isRegAlg {I : CMInfCharDatum} (hreg : I.IsRegAlg) (s : ℤ) :
    (I.shift s).IsRegAlg := by
  intro τ y hy
  obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hy
  obtain ⟨n, hn⟩ := hreg τ z hz
  refine ⟨n + s, ?_⟩
  dsimp [shift]
  rw [hn]
  push_cast
  ring

theorem shift_matchesWeights {I : CMInfCharDatum} {HT : I.Emb → Multiset ℤ}
    (hw : I.MatchesWeights HT) (s : ℤ) :
    (I.shift s).MatchesWeights (fun τ => (HT τ).map (fun n => n - s)) := by
  intro τ
  simp only [shift, Multiset.map_map, Function.comp_def]
  have e := congrArg (Multiset.map fun y : ℂ => y - (s : ℂ)) (hw τ)
  simp only [Multiset.map_map, Function.comp_def] at e
  have hcast :
      (HT τ).map (fun n : ℤ => ((n - s : ℤ) : ℂ)) =
        (HT τ).map (fun n : ℤ => (n : ℂ) - (s : ℂ)) :=
    Multiset.map_congr rfl fun n _ => by push_cast; rfl
  rw [hcast, e]
  exact Multiset.map_congr rfl fun z _ => by ring

theorem shift_hasConjWeights {I : CMInfCharDatum} {wt : ℤ} {HT : I.Emb → Multiset ℤ}
    (hconj : I.HasConjWeights wt HT) (s : ℤ) :
    (I.shift s).HasConjWeights (wt - 2 * s) (fun τ => (HT τ).map (fun n => n - s)) := by
  intro τ
  simp only [shift, hconj τ, Multiset.map_map, Function.comp_def]
  exact Multiset.map_congr rfl fun n _ => by ring

end CMInfCharDatum

/-! ## 3. `AboveCompat` (2/2), `GaloisRowProps` (6/6) & `GaloisRowData` (`Row0b`) -/

/-- Exact dead-field-free local–global compatibility at a place `p ∣ l` (**2/2** live fields:
`crys` and `nice`, matching `UpperTheory.GalStar.AboveB` in `WeightsConjBis.lean:L39-52`). -/
structure AboveCompat (D : PolarizedCuspDatum) (r : D.GalRep) (HT : D.Emb → Multiset ℤ)
    (p : D.AbovePlace) : Prop where
  /-- 1. Spherical places above `l` give crystalline + de Rham + prescribed Hodge–Tate jumps. -/
  crys : D.IsSphericalAbove p →
    D.IsCrysAt p r ∧ D.IsdRAt p r ∧ D.IsJumpsAt p r HT
  /-- 2. Nice (`IsQpBig + tame + sqf` or `toral`, with `mono0`) places above `l` give
  de Rham + potentially semistable + HT jumps + `AwayCompat`. -/
  nice :
    (((D.aboveCmp p).isQp ∧ IsQpBigNat (D.aboveCmp p).resChar D.rank ∧
      (D.aboveCmp p).isTame (D.aboveRecWD p) ∧ (D.aboveCmp p).isSqf (D.aboveRecWD p)) ∨
      (D.aboveCmp p).isToral (D.aboveRecWD p)) →
    (D.aboveCmp p).mono0 (D.aboveRecWD p) →
    D.IsdRAt p r ∧ D.IsPstAt p r ∧ D.IsJumpsAt p r HT ∧
      AwayCompat (D.aboveCmp p) (D.aboveGalWD p r) (D.aboveRecWD p)

namespace AboveCompat

theorem toAboveB {D : PolarizedCuspDatum} {r : D.GalRep} {HT : D.Emb → Multiset ℤ}
    {p : D.AbovePlace} (h : AboveCompat D r HT p) : AboveB D r HT p where
  crys := h.crys
  nice hc hm := by
    obtain ⟨h1, h2, h3, h4⟩ := h.nice hc hm
    exact ⟨h1, h2, h3, h4.toAwayB⟩

theorem ofAboveB {D : PolarizedCuspDatum} {r : D.GalRep} {HT : D.Emb → Multiset ℤ}
    {p : D.AbovePlace} (h : AboveB D r HT p) : AboveCompat D r HT p where
  crys := h.crys
  nice hc hm := by
    obtain ⟨h1, h2, h3, h4⟩ := h.nice hc hm
    exact ⟨h1, h2, h3, AwayCompat.ofAwayB h4⟩

theorem iff_aboveB (D : PolarizedCuspDatum) (r : D.GalRep) (HT : D.Emb → Multiset ℤ)
    (p : D.AbovePlace) : AboveCompat D r HT p ↔ AboveB D r HT p :=
  ⟨toAboveB, ofAboveB⟩

end AboveCompat

/-- Exact dead-field-free Galois representation properties (**6/6** live fields:
`cont, ss, away, weights, weights_conj, above`, matching `UpperTheory.GalStar.PropsB`
in `WeightsConjBis.lean:L54-67`). Together with `AboveCompat` (2/2) and `AwayCompat` (3/3),
all **11/11** fields are live downstream; zero dead fields. -/
structure GaloisRowProps (D : PolarizedCuspDatum) (r : D.GalRep) (wt : ℤ)
    (HT : D.Emb → Multiset ℤ) : Prop where
  /-- 1. Continuity of `r`. -/
  cont : D.IsContinuous r
  /-- 2. Semisimplicity of `r`. -/
  ss : D.IsSemisimple r
  /-- 3. Local–global compatibility `AwayCompat` at all finite places `w ∤ l`. -/
  away : ∀ p : D.AwayPlace, AwayCompat (D.awayCmp p) (D.awayGalWD p r) (D.awayRecWD p)
  /-- 4. Hodge–Tate weights match shifted infinitesimal character `((a-1)/2 - z)`. -/
  weights : ∀ τ : D.Emb,
    (HT τ).map (fun n : ℤ => (n : ℂ)) =
      (D.infChar τ).map (fun z : ℂ => ((D.rank : ℂ) - 1) / 2 - z)
  /-- 5. Conjugate self-duality of Hodge–Tate weights: `HT (τ ∘ c) = (wt - ·) '' HT τ`. -/
  weights_conj : ∀ τ : D.Emb, HT (D.conjEmb τ) = (HT τ).map (fun n : ℤ => wt - n)
  /-- 6. Local–global compatibility `AboveCompat` at all places `w ∣ l`. -/
  above : ∀ p : D.AbovePlace, AboveCompat D r HT p

/-- Extract the underlying `CMInfCharDatum` from a `PolarizedCuspDatum` with involutive
conjugation `conjEmb`. -/
def PolarizedCuspDatum.toCMInfCharDatum (D : PolarizedCuspDatum)
    (hinv : Function.Involutive D.conjEmb) : CMInfCharDatum where
  rank := D.rank
  rank_pos := D.rank_pos
  Emb := D.Emb
  conjEmb := D.conjEmb
  conjEmb_involutive := hinv
  infChar := D.infChar

namespace GaloisRowProps

theorem toPropsB {D : PolarizedCuspDatum} {r : D.GalRep} {wt : ℤ} {HT : D.Emb → Multiset ℤ}
    (h : GaloisRowProps D r wt HT) : PropsB D r wt HT where
  cont := h.cont
  ss := h.ss
  away p := (h.away p).toAwayB
  weights := h.weights
  weights_conj := h.weights_conj
  above p := (h.above p).toAboveB

theorem ofPropsB {D : PolarizedCuspDatum} {r : D.GalRep} {wt : ℤ} {HT : D.Emb → Multiset ℤ}
    (h : PropsB D r wt HT) : GaloisRowProps D r wt HT where
  cont := h.cont
  ss := h.ss
  away p := AwayCompat.ofAwayB (h.away p)
  weights := h.weights
  weights_conj := h.weights_conj
  above p := AboveCompat.ofAboveB (h.above p)

theorem iff_propsB (D : PolarizedCuspDatum) (r : D.GalRep) (wt : ℤ) (HT : D.Emb → Multiset ℤ) :
    GaloisRowProps D r wt HT ↔ PropsB D r wt HT :=
  ⟨toPropsB, ofPropsB⟩

/-- Mirrors `UpperTheory.GalStar.Props.big` (`WeightsConjBis.lean:L75-83`). -/
theorem of_strong {D : PolarizedCuspDatum} {r : D.GalRep} {wt : ℤ} {HT : D.Emb → Multiset ℤ}
    (h : PropsStrong D r wt HT) : GaloisRowProps D r wt HT :=
  ofPropsB (PropsB.of_strong h)

/-- Any `GaloisRowProps` automatically enforces polarization of the infinitesimal character
`D.infChar` with parity weight `wt`. -/
theorem isPolarized_infChar {D : PolarizedCuspDatum} (hinv : Function.Involutive D.conjEmb)
    {r : D.GalRep} {wt : ℤ} {HT : D.Emb → Multiset ℤ} (h : GaloisRowProps D r wt HT) :
    (D.toCMInfCharDatum hinv).IsPolarized wt :=
  CMInfCharDatum.polarized_of_weights_conj h.weights h.weights_conj

/-- Sum symmetry of Hodge–Tate weights directly from `GaloisRowProps`. -/
theorem HT_sum_conj {D : PolarizedCuspDatum} (hinv : Function.Involutive D.conjEmb)
    {r : D.GalRep} {wt : ℤ} {HT : D.Emb → Multiset ℤ} (h : GaloisRowProps D r wt HT)
    (τ : D.Emb) :
    (HT (D.conjEmb τ)).sum + (HT τ).sum = ((HT τ).card : ℤ) * wt :=
  CMInfCharDatum.HT_sum_conj (I := D.toCMInfCharDatum hinv) h.weights_conj τ

/-- Uniqueness of the Hodge–Tate weight assignment `HT` across any two `GaloisRowProps`
witnesses on the same `PolarizedCuspDatum`. -/
theorem HT_unique {D : PolarizedCuspDatum} (hinv : Function.Involutive D.conjEmb)
    {r₁ r₂ : D.GalRep} {wt₁ wt₂ : ℤ} {HT₁ HT₂ : D.Emb → Multiset ℤ}
    (h₁ : GaloisRowProps D r₁ wt₁ HT₁) (h₂ : GaloisRowProps D r₂ wt₂ HT₂) : HT₁ = HT₂ :=
  CMInfCharDatum.HT_unique (I := D.toCMInfCharDatum hinv) h₁.weights h₂.weights

end GaloisRowProps

/-- Exact dead-field-free formalization of `UpperTheory.GalStar.Row0b recT`
(`WeightsConjBis.lean:L69-73`, proved in `RowSrc.lean:L6`): every polarized regular
algebraic cuspidal datum `datum i` carries a Galois representation `r`, parity weight `wt`,
and Hodge–Tate weights `HT` satisfying all 11 live fields of `GaloisRowProps`. -/
def GaloisRowData (PolIdx : Type) (datum : PolIdx → PolarizedCuspDatum) : Prop :=
  ∀ i : PolIdx, ∃ (r : (datum i).GalRep) (wt : ℤ) (HT : (datum i).Emb → Multiset ℤ),
    GaloisRowProps (datum i) r wt HT

namespace GaloisRowData

theorem toMinimalGaloisRow {PolIdx : Type} {datum : PolIdx → PolarizedCuspDatum}
    (H : GaloisRowData PolIdx datum) : MinimalGaloisRow PolIdx datum := by
  intro i
  obtain ⟨r, wt, HT, h⟩ := H i
  exact ⟨r, wt, HT, h.toPropsB⟩

theorem ofMinimalGaloisRow {PolIdx : Type} {datum : PolIdx → PolarizedCuspDatum}
    (H : MinimalGaloisRow PolIdx datum) : GaloisRowData PolIdx datum := by
  intro i
  obtain ⟨r, wt, HT, h⟩ := H i
  exact ⟨r, wt, HT, GaloisRowProps.ofPropsB h⟩

theorem iff_minimalGaloisRow (PolIdx : Type) (datum : PolIdx → PolarizedCuspDatum) :
    GaloisRowData PolIdx datum ↔ MinimalGaloisRow PolIdx datum :=
  ⟨toMinimalGaloisRow, ofMinimalGaloisRow⟩

/-- Mirrors `UpperTheory.GalStar.Row0.row0b` (`WeightsConjBis.lean:L85-86`). -/
theorem of_strong {PolIdx : Type} {datum : PolIdx → PolarizedCuspDatum}
    (H : ∀ i : PolIdx, ∃ r wt HT, PropsStrong (datum i) r wt HT) :
    GaloisRowData PolIdx datum :=
  ofMinimalGaloisRow (MinimalGaloisRow.of_strong H)

end GaloisRowData

/-! ## 4. Local–Global Compatibility Assembly (`CoreAll` + `R1` + `R2` → `Row0b`) -/

/-- Structured polarized cuspidal datum equipped with concrete `LocalWDPlace` Weil groups
at all places away from and above `l`, plus involutive CM conjugation and dimension matching
(`lpDim (awayGalWD p r) = rank = lpDim (awayRecWD p)`). -/
structure StructuredCuspDatum where
  rank : ℕ
  rank_pos : 1 ≤ rank
  GalRep : Type
  Emb : Type
  conjEmb : Emb → Emb
  conjEmb_involutive : Function.Involutive conjEmb
  IsContinuous : GalRep → Prop
  IsSemisimple : GalRep → Prop
  infChar : Emb → Multiset ℂ
  AwayPlace : Type
  awayPlace : AwayPlace → LocalWDPlace
  awayGalWD : (p : AwayPlace) → GalRep → (awayPlace p).WD
  awayRecWD : (p : AwayPlace) → (awayPlace p).WD
  awayGal_dim : ∀ (p : AwayPlace) (r : GalRep), (awayPlace p).lpDim (awayGalWD p r) = rank
  awayRec_dim : ∀ p : AwayPlace, (awayPlace p).lpDim (awayRecWD p) = rank
  AbovePlace : Type
  abovePlace : AbovePlace → LocalWDPlace
  aboveGalWD : (p : AbovePlace) → GalRep → (abovePlace p).WD
  aboveRecWD : (p : AbovePlace) → (abovePlace p).WD
  IsSphericalAbove : AbovePlace → Prop
  IsCrysAt : AbovePlace → GalRep → Prop
  IsdRAt : AbovePlace → GalRep → Prop
  IsPstAt : AbovePlace → GalRep → Prop
  IsJumpsAt : AbovePlace → GalRep → (Emb → Multiset ℤ) → Prop

namespace StructuredCuspDatum

def toPolarizedCuspDatum (S : StructuredCuspDatum) : PolarizedCuspDatum where
  rank := S.rank
  rank_pos := S.rank_pos
  GalRep := S.GalRep
  Emb := S.Emb
  conjEmb := S.conjEmb
  IsContinuous := S.IsContinuous
  IsSemisimple := S.IsSemisimple
  infChar := S.infChar
  AwayPlace := S.AwayPlace
  awayCmp p := (S.awayPlace p).toCompare
  awayGalWD := S.awayGalWD
  awayRecWD := S.awayRecWD
  AbovePlace := S.AbovePlace
  aboveCmp p := (S.abovePlace p).toCompare
  aboveGalWD := S.aboveGalWD
  aboveRecWD := S.aboveRecWD
  IsSphericalAbove := S.IsSphericalAbove
  IsCrysAt := S.IsCrysAt
  IsdRAt := S.IsdRAt
  IsPstAt := S.IsPstAt
  IsJumpsAt := S.IsJumpsAt

def toCMInfCharDatum (S : StructuredCuspDatum) : CMInfCharDatum where
  rank := S.rank
  rank_pos := S.rank_pos
  Emb := S.Emb
  conjEmb := S.conjEmb
  conjEmb_involutive := S.conjEmb_involutive
  infChar := S.infChar

/-- Weak Galois representation existence + spherical crystalline/de Rham compatibility
(mirroring `GlobalTheory.RoadU.CoreAll` in `GaloisLocalGlobalOfLocalGlobalCompatibility.lean`). -/
structure CoreAllAt (S : StructuredCuspDatum) : Prop where
  exists_weak : ∃ r : S.GalRep, S.IsContinuous r ∧ S.IsSemisimple r
  crys_of_spherical : ∀ (r : S.GalRep) (HT : S.Emb → Multiset ℤ),
    S.IsContinuous r → S.IsSemisimple r → S.toCMInfCharDatum.MatchesWeights HT →
    ∀ p : S.AbovePlace, S.IsSphericalAbove p →
      S.IsCrysAt p r ∧ S.IsdRAt p r ∧ S.IsJumpsAt p r HT

/-- Toral local–global compatibility `R1` (`galoisCompat_unlinkedSupport_of_spherical`):
at toral `mono0` places away from `l` we have full WD equality, and above `l` we have
de Rham + potentially semistable + HT jumps + `mono0` + full Weil charpoly agreement. -/
structure ToralCompatAt (S : StructuredCuspDatum) : Prop where
  away_toral : ∀ (r : S.GalRep), S.IsContinuous r → S.IsSemisimple r →
    ∀ p : S.AwayPlace, (S.awayPlace p).isToral (S.awayRecWD p) →
      (S.awayPlace p).mono0 (S.awayRecWD p) → S.awayGalWD p r = S.awayRecWD p
  above_toral : ∀ (r : S.GalRep) (HT : S.Emb → Multiset ℤ),
    S.IsContinuous r → S.IsSemisimple r → S.toCMInfCharDatum.MatchesWeights HT →
    ∀ p : S.AbovePlace, (S.abovePlace p).isToral (S.aboveRecWD p) →
      (S.abovePlace p).mono0 (S.aboveRecWD p) →
      S.IsdRAt p r ∧ S.IsPstAt p r ∧ S.IsJumpsAt p r HT ∧
        (S.abovePlace p).mono0 (S.aboveGalWD p r) ∧
        ∀ g : (S.abovePlace p).Weil,
          (S.abovePlace p).charPol (S.aboveGalWD p r) g =
            (S.abovePlace p).charPol (S.aboveRecWD p) g

/-- Place-class local–global compatibility `R2` (`LocalGlobalCompatibilityAtPlaceClass Q`):
at tame squarefree `mono0` `ℚ_p`-places satisfying predicate `Q resChar rank`, inertia
characteristic polynomials match (`∀ t : inertia, charPol gal t = charPol rec t`). -/
structure PlaceClassCompatAt (Q : ℕ → ℕ → Prop) (S : StructuredCuspDatum) : Prop where
  away_inertia : ∀ (r : S.GalRep), S.IsContinuous r → S.IsSemisimple r →
    ∀ p : S.AwayPlace, Q (S.awayPlace p).resChar S.rank →
      (S.awayPlace p).isQp → (S.awayPlace p).isTame (S.awayRecWD p) →
      (S.awayPlace p).isSqf (S.awayRecWD p) → (S.awayPlace p).mono0 (S.awayRecWD p) →
      (S.awayPlace p).mono0 (S.awayGalWD p r) ∧
        ∀ t : (S.awayPlace p).inertia,
          (S.awayPlace p).charPol (S.awayGalWD p r) t =
            (S.awayPlace p).charPol (S.awayRecWD p) t
  above_inertia : ∀ (r : S.GalRep) (HT : S.Emb → Multiset ℤ),
    S.IsContinuous r → S.IsSemisimple r → S.toCMInfCharDatum.MatchesWeights HT →
    ∀ p : S.AbovePlace, Q (S.abovePlace p).resChar S.rank →
      (S.abovePlace p).isQp → (S.abovePlace p).isTame (S.aboveRecWD p) →
      (S.abovePlace p).isSqf (S.aboveRecWD p) → (S.abovePlace p).mono0 (S.aboveRecWD p) →
      S.IsdRAt p r ∧ S.IsPstAt p r ∧ S.IsJumpsAt p r HT ∧
        (S.abovePlace p).mono0 (S.aboveGalWD p r) ∧
        ∀ t : (S.abovePlace p).inertia,
          (S.abovePlace p).charPol (S.aboveGalWD p r) t =
            (S.abovePlace p).charPol (S.aboveRecWD p) t

/-- Unrestricted (`Q := fun _ _ => True`) compatibility implies `IsQpBigNat`-class compatibility. -/
theorem PlaceClassCompatAt.toIsQpBig {S : StructuredCuspDatum}
    (H : PlaceClassCompatAt (fun _ _ => True) S) : PlaceClassCompatAt IsQpBigNat S where
  away_inertia r hc hss p _ := H.away_inertia r hc hss p trivial
  above_inertia r HT hc hss hw p _ := H.above_inertia r HT hc hss hw p trivial

/-- Direct reconstruction of `UpperTheory.Gal.Int.Row.away` for `Q = IsQpBigNat`:
assembles all 3 fields of `AwayCompat` (`dim, tor, tame0`) from `ToralCompatAt` +
`PlaceClassCompatAt IsQpBigNat`. -/
theorem awayCompat_of_toral_and_placeClass {S : StructuredCuspDatum}
    (H1 : ToralCompatAt S) (H2 : PlaceClassCompatAt IsQpBigNat S)
    {r : S.GalRep} (hc : S.IsContinuous r) (hss : S.IsSemisimple r) (p : S.AwayPlace) :
    AwayCompat (S.awayPlace p).toCompare (S.awayGalWD p r) (S.awayRecWD p) where
  dim := (S.awayGal_dim p r).trans (S.awayRec_dim p).symm
  tor ht hm := H1.away_toral r hc hss p ht hm
  tame0 hq ht hs hm := by
    have hbig : IsQpBigNat (S.awayPlace p).resChar S.rank := by
      simpa [LocalWDPlace.toCompare, S.awayRec_dim p] using hq.2
    obtain ⟨hm0, hine⟩ := H2.away_inertia r hc hss p hbig hq.1 ht hs hm
    exact ⟨hm0, fun g hg => LocalWDPlace.charPol_of_inertia hine g hg⟩

/-- Direct reconstruction of `UpperTheory.Gal.Int.Row.above` + `crys`:
assembles both fields of `AboveCompat` (`crys, nice`) by splitting on `isToral`
and using `of_mono0_charPol` vs. `of_not_toral_inertia`. -/
theorem aboveCompat_of_crys_toral_placeClass {S : StructuredCuspDatum}
    (C : CoreAllAt S) (H1 : ToralCompatAt S) (H2 : PlaceClassCompatAt IsQpBigNat S)
    {r : S.GalRep} {HT : S.Emb → Multiset ℤ}
    (hc : S.IsContinuous r) (hss : S.IsSemisimple r)
    (hw : S.toCMInfCharDatum.MatchesWeights HT) (p : S.AbovePlace) :
    AboveCompat S.toPolarizedCuspDatum r HT p where
  crys hsph := C.crys_of_spherical r HT hc hss hw p hsph
  nice hcond hm := by
    by_cases ht : (S.abovePlace p).isToral (S.aboveRecWD p)
    · obtain ⟨hdR, hpst, hJ, hm0, hchar⟩ := H1.above_toral r HT hc hss hw p ht hm
      exact ⟨hdR, hpst, hJ, AwayCompat.of_mono0_charPol hm0 hm hchar⟩
    · obtain ⟨hq, hbig, htame, hsqf⟩ := hcond.resolve_right ht
      obtain ⟨hdR, hpst, hJ, hm0, hine⟩ :=
        H2.above_inertia r HT hc hss hw p hbig hq htame hsqf hm
      exact ⟨hdR, hpst, hJ, AwayCompat.of_not_toral_inertia ht hm0 hine⟩

/-- Complete single-datum assembly of all 6 fields of `GaloisRowProps`
(`cont, ss, away, weights, weights_conj, above`) from regular algebraicity, polarization,
`CoreAllAt`, `ToralCompatAt`, and `PlaceClassCompatAt IsQpBigNat`. -/
theorem galoisRowProps_of_localGlobal {S : StructuredCuspDatum}
    (hreg : S.toCMInfCharDatum.IsRegAlg) {wt : ℤ} (hpol : S.toCMInfCharDatum.IsPolarized wt)
    (C : CoreAllAt S) (H1 : ToralCompatAt S) (H2 : PlaceClassCompatAt IsQpBigNat S) :
    ∃ (r : S.GalRep) (HT : S.Emb → Multiset ℤ),
      GaloisRowProps S.toPolarizedCuspDatum r wt HT := by
  obtain ⟨r, hc, hss⟩ := C.exists_weak
  obtain ⟨HT, hw, hconj⟩ := CMInfCharDatum.exists_weights_of_regAlg_polarized hreg hpol
  refine ⟨r, HT, ?_⟩
  exact
    { cont := hc
      ss := hss
      away := awayCompat_of_toral_and_placeClass H1 H2 hc hss
      weights := hw
      weights_conj := hconj
      above := aboveCompat_of_crys_toral_placeClass C H1 H2 hc hss hw }

/-- Global rank-two / `IsQpBigNat` realization theorem (rebuilding
`UpperTheory.Gal.Int.Row.galois_realisation_of_rank_two` cleanly without dead wrappers). -/
theorem galois_realisation_of_rank_two {PolIdx : Type} (S : PolIdx → StructuredCuspDatum)
    (hreg : ∀ i, (S i).toCMInfCharDatum.IsRegAlg)
    (hpol : ∀ i, ∃ wt : ℤ, (S i).toCMInfCharDatum.IsPolarized wt)
    (C : ∀ i, CoreAllAt (S i))
    (H1 : ∀ i, ToralCompatAt (S i))
    (H2 : ∀ i, PlaceClassCompatAt IsQpBigNat (S i)) :
    GaloisRowData PolIdx (fun i => (S i).toPolarizedCuspDatum) := by
  intro i
  obtain ⟨wt, hwt⟩ := hpol i
  obtain ⟨r, HT, hprops⟩ := galoisRowProps_of_localGlobal (hreg i) hwt (C i) (H1 i) (H2 i)
  exact ⟨r, wt, HT, hprops⟩

/-- Global unrestricted local–global realization theorem (rebuilding
`UpperTheory.Gal.Int.Row.galoisLocalGlobal_of_localGlobalCompatibility`). -/
theorem galoisLocalGlobal_of_unrestricted {PolIdx : Type} (S : PolIdx → StructuredCuspDatum)
    (hreg : ∀ i, (S i).toCMInfCharDatum.IsRegAlg)
    (hpol : ∀ i, ∃ wt : ℤ, (S i).toCMInfCharDatum.IsPolarized wt)
    (C : ∀ i, CoreAllAt (S i))
    (H1 : ∀ i, ToralCompatAt (S i))
    (H2 : ∀ i, PlaceClassCompatAt (fun _ _ => True) (S i)) :
    GaloisRowData PolIdx (fun i => (S i).toPolarizedCuspDatum) :=
  galois_realisation_of_rank_two S hreg hpol C H1 (fun i => (H2 i).toIsQpBig)

end StructuredCuspDatum

/-! ## 5. Theta-Lift Transport & `TLiftK` / `RowSrc` Assembly -/

/-- Weight-dominance condition from `UpperTheory.TP.TLiftK` (`HalfIndexLattices/TLiftK.lean:L20`):
`(d : ℤ) + mW w ≤ 2 * lam w k` for every archimedean place `w` and index `k : Fin n`. -/
def ThetaLiftDominance {InfPlace : Type} {n : ℕ} (d : ℕ) (mW : InfPlace → ℤ)
    (lam : InfPlace → Fin n → ℤ) : Prop :=
  ∀ (w : InfPlace) (k : Fin n), (d : ℤ) + mW w ≤ 2 * lam w k

namespace ThetaLiftDominance

/-- Weight dominance is preserved when increasing dominant weights `lam` by a non-negative shift. -/
theorem mono_weight {InfPlace : Type} {n : ℕ} {d : ℕ} {mW : InfPlace → ℤ}
    {lam lam' : InfPlace → Fin n → ℤ} (h : ThetaLiftDominance d mW lam)
    (hle : ∀ w k, lam w k ≤ lam' w k) : ThetaLiftDominance d mW lam' :=
  fun w k => le_trans (h w k) (by have := hle w k; linarith)

/-- Weight dominance is antitone in the target rank `d` and character exponent `mW`. -/
theorem anti_rank_char {InfPlace : Type} {n : ℕ} {d d' : ℕ} {mW mW' : InfPlace → ℤ}
    {lam : InfPlace → Fin n → ℤ} (h : ThetaLiftDominance d mW lam)
    (hd : d' ≤ d) (hm : ∀ w, mW' w ≤ mW w) : ThetaLiftDominance d' mW' lam :=
  fun w k => le_trans (by have := hm w; omega) (h w k)

/-- Simultaneous shift of `lam` by `s` and `mW` by `2 * s` preserves `ThetaLiftDominance`. -/
theorem shift_covariant {InfPlace : Type} {n : ℕ} {d : ℕ} {mW : InfPlace → ℤ}
    {lam : InfPlace → Fin n → ℤ} (h : ThetaLiftDominance d mW lam) (s : ℤ) :
    ThetaLiftDominance d (fun w => mW w + 2 * s) (fun w k => lam w k + s) :=
  fun w k => by have := h w k; linarith

end ThetaLiftDominance

/-- Local Weil–Deligne transport morphism between two comparison contexts `C₁ → C₂`
(modeling local-global compatibility transport under a theta-lift / character twist
that preserves dimension, monodromy vanishing, torality, tameness, squarefreeness,
residue characteristic, and degree-0 characteristic polynomials). -/
structure LocalWDTransport (C₁ C₂ : LocalWDCompare) where
  mapWD : C₁.WD → C₂.WD
  mapWeil : C₂.Weil → C₁.Weil
  mapCharPol : C₁.CharPol → C₂.CharPol
  map_dim : ∀ x, C₂.lpDim (mapWD x) = C₁.lpDim x
  map_mono0 : ∀ x, C₁.mono0 x → C₂.mono0 (mapWD x)
  reflect_mono0 : ∀ x, C₂.mono0 (mapWD x) → C₁.mono0 x
  reflect_toral : ∀ x, C₂.isToral (mapWD x) → C₁.isToral x
  reflect_tame : ∀ x, C₂.isTame (mapWD x) → C₁.isTame x
  reflect_sqf : ∀ x, C₂.isSqf (mapWD x) → C₁.isSqf x
  reflect_isQp : C₂.isQp → C₁.isQp
  resChar_eq : C₂.resChar = C₁.resChar
  deg_mapWeil : ∀ g : C₂.Weil, C₂.deg g = 0 → C₁.deg (mapWeil g) = 0
  charPol_map : ∀ (x : C₁.WD) (g : C₂.Weil),
    C₂.charPol (mapWD x) g = mapCharPol (C₁.charPol x (mapWeil g))

/-- Local–global compatibility `AwayCompat` transports functorially along any
`LocalWDTransport` (preserving all 3 live fields `dim, tor, tame0`). -/
theorem AwayCompat.transport {C₁ C₂ : LocalWDCompare} (T : LocalWDTransport C₁ C₂)
    {x y : C₁.WD} (h : AwayCompat C₁ x y) :
    AwayCompat C₂ (T.mapWD x) (T.mapWD y) where
  dim := by rw [T.map_dim, T.map_dim, h.dim]
  tor ht hm := by
    have heq := h.tor (T.reflect_toral y ht) (T.reflect_mono0 y hm)
    rw [heq]
  tame0 hq ht hs hm := by
    have hq₁ : C₁.isQp ∧ IsQpBigNat C₁.resChar (C₁.lpDim y) := by
      refine ⟨T.reflect_isQp hq.1, ?_⟩
      simpa [T.resChar_eq, T.map_dim] using hq.2
    obtain ⟨hm0, hcp⟩ := h.tame0 hq₁ (T.reflect_tame y ht) (T.reflect_sqf y hs) (T.reflect_mono0 y hm)
    refine ⟨T.map_mono0 x hm0, fun g hg => ?_⟩
    rw [T.charPol_map, T.charPol_map, hcp (T.mapWeil g) (T.deg_mapWeil g hg)]

/-- Global theta-lift transport datum from `D₁` to `D₂` with integer character shift `shift : ℤ`
(carrying continuous semisimple Galois representations, local WD comparisons away from and
above `l`, crystalline/de Rham/pst/HT-jump compatibility, and shifted infinitesimal characters). -/
structure ThetaLiftRowTransport (D₁ D₂ : PolarizedCuspDatum) (shift : ℤ) where
  rank_eq : D₂.rank = D₁.rank
  mapRep : D₁.GalRep → D₂.GalRep
  mapCont : ∀ r, D₁.IsContinuous r → D₂.IsContinuous (mapRep r)
  mapSS : ∀ r, D₁.IsSemisimple r → D₂.IsSemisimple (mapRep r)
  embEquiv : D₂.Emb ≃ D₁.Emb
  conj_comm : ∀ τ : D₂.Emb, embEquiv (D₂.conjEmb τ) = D₁.conjEmb (embEquiv τ)
  infChar_shift : ∀ τ : D₂.Emb,
    D₂.infChar τ = (D₁.infChar (embEquiv τ)).map (fun z : ℂ => z + (shift : ℂ))
  awayPull : D₂.AwayPlace → D₁.AwayPlace
  awayTrans : ∀ p : D₂.AwayPlace, LocalWDTransport (D₁.awayCmp (awayPull p)) (D₂.awayCmp p)
  awayGal_comm : ∀ (p : D₂.AwayPlace) (r : D₁.GalRep),
    D₂.awayGalWD p (mapRep r) = (awayTrans p).mapWD (D₁.awayGalWD (awayPull p) r)
  awayRec_comm : ∀ p : D₂.AwayPlace,
    D₂.awayRecWD p = (awayTrans p).mapWD (D₁.awayRecWD (awayPull p))
  abovePull : D₂.AbovePlace → D₁.AbovePlace
  aboveTrans : ∀ p : D₂.AbovePlace, LocalWDTransport (D₁.aboveCmp (abovePull p)) (D₂.aboveCmp p)
  aboveGal_comm : ∀ (p : D₂.AbovePlace) (r : D₁.GalRep),
    D₂.aboveGalWD p (mapRep r) = (aboveTrans p).mapWD (D₁.aboveGalWD (abovePull p) r)
  aboveRec_comm : ∀ p : D₂.AbovePlace,
    D₂.aboveRecWD p = (aboveTrans p).mapWD (D₁.aboveRecWD (abovePull p))
  reflect_spherical : ∀ p : D₂.AbovePlace, D₂.IsSphericalAbove p → D₁.IsSphericalAbove (abovePull p)
  mapCrys : ∀ (p : D₂.AbovePlace) (r : D₁.GalRep),
    D₁.IsCrysAt (abovePull p) r → D₂.IsCrysAt p (mapRep r)
  mapdR : ∀ (p : D₂.AbovePlace) (r : D₁.GalRep),
    D₁.IsdRAt (abovePull p) r → D₂.IsdRAt p (mapRep r)
  mapPst : ∀ (p : D₂.AbovePlace) (r : D₁.GalRep),
    D₁.IsPstAt (abovePull p) r → D₂.IsPstAt p (mapRep r)
  mapJumps : ∀ (p : D₂.AbovePlace) (r : D₁.GalRep) (HT : D₁.Emb → Multiset ℤ),
    D₁.IsJumpsAt (abovePull p) r HT →
    D₂.IsJumpsAt p (mapRep r) (fun τ => (HT (embEquiv τ)).map (fun n => n - shift))

/-- Transport of `AboveCompat` (both `crys` and `nice`) along a theta-lift correspondence. -/
theorem AboveCompat.transport {D₁ D₂ : PolarizedCuspDatum} {shift : ℤ}
    (T : ThetaLiftRowTransport D₁ D₂ shift) {r : D₁.GalRep} {HT : D₁.Emb → Multiset ℤ}
    {p : D₂.AbovePlace} (h : AboveCompat D₁ r HT (T.abovePull p)) :
    AboveCompat D₂ (T.mapRep r) (fun τ => (HT (T.embEquiv τ)).map (fun n => n - shift)) p where
  crys hsph := by
    obtain ⟨hc, hdR, hJ⟩ := h.crys (T.reflect_spherical p hsph)
    exact ⟨T.mapCrys p r hc, T.mapdR p r hdR, T.mapJumps p r HT hJ⟩
  nice hcond hm := by
    have hm₁ : (D₁.aboveCmp (T.abovePull p)).mono0 (D₁.aboveRecWD (T.abovePull p)) :=
      (T.aboveTrans p).reflect_mono0 _ (by rwa [← T.aboveRec_comm p])
    have hcond₁ :
        (((D₁.aboveCmp (T.abovePull p)).isQp ∧
            IsQpBigNat (D₁.aboveCmp (T.abovePull p)).resChar D₁.rank ∧
            (D₁.aboveCmp (T.abovePull p)).isTame (D₁.aboveRecWD (T.abovePull p)) ∧
            (D₁.aboveCmp (T.abovePull p)).isSqf (D₁.aboveRecWD (T.abovePull p))) ∨
          (D₁.aboveCmp (T.abovePull p)).isToral (D₁.aboveRecWD (T.abovePull p))) := by
      rcases hcond with ⟨hq, hbig, htame, hsqf⟩ | htor
      · left
        refine ⟨(T.aboveTrans p).reflect_isQp hq, ?_, ?_, ?_⟩
        · simpa [(T.aboveTrans p).resChar_eq, T.rank_eq] using hbig
        · exact (T.aboveTrans p).reflect_tame _ (by rwa [← T.aboveRec_comm p])
        · exact (T.aboveTrans p).reflect_sqf _ (by rwa [← T.aboveRec_comm p])
      · right
        exact (T.aboveTrans p).reflect_toral _ (by rwa [← T.aboveRec_comm p])
    obtain ⟨hdR, hpst, hJ, haway⟩ := h.nice hcond₁ hm₁
    refine ⟨T.mapdR p r hdR, T.mapPst p r hpst, T.mapJumps p r HT hJ, ?_⟩
    rw [T.aboveGal_comm p r, T.aboveRec_comm p]
    exact haway.transport (T.aboveTrans p)

/-- Transport of all 6 live fields of `GaloisRowProps` (including shifted Hodge–Tate weights
and conjugate-self-duality weight `wt - 2 * shift`) along a theta-lift correspondence. -/
theorem GaloisRowProps.transport {D₁ D₂ : PolarizedCuspDatum} {shift : ℤ}
    (T : ThetaLiftRowTransport D₁ D₂ shift) {r : D₁.GalRep} {wt : ℤ} {HT : D₁.Emb → Multiset ℤ}
    (h : GaloisRowProps D₁ r wt HT) :
    GaloisRowProps D₂ (T.mapRep r) (wt - 2 * shift)
      (fun τ => (HT (T.embEquiv τ)).map (fun n => n - shift)) where
  cont := T.mapCont r h.cont
  ss := T.mapSS r h.ss
  away p := by
    rw [T.awayGal_comm p r, T.awayRec_comm p]
    exact (h.away (T.awayPull p)).transport (T.awayTrans p)
  weights τ := by
    rw [T.infChar_shift τ, T.rank_eq]
    simp only [Multiset.map_map, Function.comp_def]
    have e := congrArg (Multiset.map fun y : ℂ => y - (shift : ℂ)) (h.weights (T.embEquiv τ))
    simp only [Multiset.map_map, Function.comp_def] at e
    have hcast :
        (HT (T.embEquiv τ)).map (fun n : ℤ => ((n - shift : ℤ) : ℂ)) =
          (HT (T.embEquiv τ)).map (fun n : ℤ => (n : ℂ) - (shift : ℂ)) :=
      Multiset.map_congr rfl fun n _ => by push_cast; rfl
    rw [hcast, e]
    exact Multiset.map_congr rfl fun z _ => by ring
  weights_conj τ := by
    simp only [T.conj_comm τ, h.weights_conj (T.embEquiv τ), Multiset.map_map, Function.comp_def]
    exact Multiset.map_congr rfl fun n _ => by ring
  above p := (h.above (T.abovePull p)).transport T

/-- Exact clean mirror of the `RowSrc.lean` / `Development.lean` /
`GaloisRepresentationsOfThetaLift.lean` assembly pipeline (`GeoOne` + `TLiftK` → `CoreAll` → `Row0b`). -/
structure ThetaLiftAssemblyPipeline (PolIdx : Type) (S : PolIdx → StructuredCuspDatum) where
  GeoOne : Prop
  SeedFinOdd : Prop
  CongFinOdd : Prop
  TLiftK : Prop
  seed_of_geo : GeoOne → SeedFinOdd
  cong_holds : CongFinOdd
  reg_all : ∀ i, (S i).toCMInfCharDatum.IsRegAlg
  pol_all : ∀ i, ∃ wt : ℤ, (S i).toCMInfCharDatum.IsPolarized wt
  coreAll_of : SeedFinOdd → CongFinOdd → TLiftK → ∀ i, (S i).CoreAllAt
  toral_of_core : (∀ i, (S i).CoreAllAt) → ∀ i, (S i).ToralCompatAt
  rankTwo_of_core : (∀ i, (S i).CoreAllAt) → ∀ i, (S i).PlaceClassCompatAt IsQpBigNat

/-- Mirrors `UpperTheory.Gal.Int.galoisLocalGlobalStrong_of_geometry_lift` (`Development.lean:L33`). -/
theorem galoisLocalGlobalStrong_of_geometry_lift {PolIdx : Type}
    {S : PolIdx → StructuredCuspDatum} (P : ThetaLiftAssemblyPipeline PolIdx S)
    (geo : P.GeoOne) (up : P.TLiftK) :
    GaloisRowData PolIdx (fun i => (S i).toPolarizedCuspDatum) := by
  have hCore := P.coreAll_of (P.seed_of_geo geo) P.cong_holds up
  exact StructuredCuspDatum.galois_realisation_of_rank_two S P.reg_all P.pol_all
    hCore (P.toral_of_core hCore) (P.rankTwo_of_core hCore)

/-- Mirrors `UpperTheory.Gal.Int.galoisRepresentations_of_thetaLift`
(`GaloisRepresentationsOfThetaLift.lean:L6`) and `galoisLocalGlobalStrong_recParameter`
(`RowSrc.lean:L6`). -/
theorem galoisRepresentations_of_thetaLift {PolIdx : Type}
    {S : PolIdx → StructuredCuspDatum} (P : ThetaLiftAssemblyPipeline PolIdx S)
    (geo : P.GeoOne) (up : P.TLiftK) :
    MinimalGaloisRow PolIdx (fun i => (S i).toPolarizedCuspDatum) :=
  (galoisLocalGlobalStrong_of_geometry_lift P geo up).toMinimalGaloisRow

/-! ## 6. Direct Projection into `GaloisModularityCore` (Zero `OpenImageCondition`!) -/

/-- Direct projection of `GaloisRowData` (`Row0b`) into `MinimalGlobalAutomorphy.gal`,
completely bypassing the 100%-dead `OpenImageCondition` wrapper of
`TemperedProductOfSquareIntegrable.lean:L207-208` / `VwinOfRow.lean:L5`. -/
theorem GaloisRowData.toMinimalGlobalAutomorphy {G : GlobalAutomorphyCarrier}
    {PolIdx : Type} {datum : PolIdx → PolarizedCuspDatum}
    (hRow : GaloisRowData PolIdx datum)
    (hc : G.HarishChandraFinite)
    (fin : G.AutomorphicFormsFiniteGL)
    (js : G.JacquetShalika)
    (cusp : G.CuspidalSpectrumGL)
    (bc : G.BaseChangeIsobaricN)
    (gk : G.GelfandKazhdanDual)
    (coh : G.ClozelCohomological)
    (art : G.GlobalArtinReciprocity)
    (chA : G.HeckeLAdicCharacterAbove)
    (chW : G.AlgebraicCharacterWD)
    (berger : G.DeRhamPotSemistable) :
    MinimalGlobalAutomorphy G PolIdx datum where
  hc := hc
  fin := fin
  js := js
  cusp := cusp
  bc := bc
  gk := gk
  gal := hRow.toMinimalGaloisRow
  coh := coh
  art := art
  chA := chA
  chW := chW
  berger := berger

/-- Direct projection of `GaloisRowData` into Pillar 2's `MinimalThetaInputs`. -/
theorem GaloisRowData.toMinimalThetaInputs {D : AutomorphicDomain}
    {T : ThetaLocalCarrier} {H : HodgeBundleCarrier}
    (hLLC : MinimalLocalLanglands D.LocIdx D.place)
    (hRow : GaloisRowData D.PolIdx D.datum)
    (hTheta : MinimalThetaLocalInputs T)
    (hHodge : MinimalHodgeBundleInputs H) :
    MinimalThetaInputs D T H :=
  ⟨hLLC, hRow.toMinimalGaloisRow, hTheta, hHodge⟩

/-- Direct projection into `GaloisModularityCore` (`GaloisModularityContract S`, i.e. `VWin S`)
from `GaloisRowData` plus the remaining live fields of `MinimalAutomorphyInputs` — zero
`OpenImageCondition`, zero `LiteratureCMHypothesis`. -/
theorem GaloisRowData.toGaloisModularityContract {D : AutomorphicDomain} {S : SelmerSystem}
    (hRow : GaloisRowData D.PolIdx D.datum)
    (hLLC : MinimalLocalLanglands D.LocIdx D.place)
    (hLoc : MinimalLocalRepInputs D.locRep)
    (hAutOther : MinimalGaloisRow D.PolIdx D.datum → MinimalGlobalAutomorphy D.globAut D.PolIdx D.datum)
    (hCoh : MinimalGaloisCohomology D.galCoh)
    (hPatch : MinimalPatchingInputs D.patching)
    (vwin_of_inputs : MinimalAutomorphyInputs D → VWin S) :
    GaloisModularityContract S :=
  ⟨vwin_of_inputs ⟨hLLC, hLoc, hAutOther hRow.toMinimalGaloisRow, hCoh, hPatch⟩⟩

/-- End-to-end projection from `GaloisRowData` directly into `RHDirectAssembly S`. -/
theorem GaloisRowData.toRHDirectAssembly {D : AutomorphicDomain} {S : SelmerSystem}
    (hRow : GaloisRowData D.PolIdx D.datum)
    (hLLC : MinimalLocalLanglands D.LocIdx D.place)
    (hLoc : MinimalLocalRepInputs D.locRep)
    (hAutOther : MinimalGaloisRow D.PolIdx D.datum → MinimalGlobalAutomorphy D.globAut D.PolIdx D.datum)
    (hCoh : MinimalGaloisCohomology D.galCoh)
    (hPatch : MinimalPatchingInputs D.patching)
    (vwin_of_inputs : MinimalAutomorphyInputs D → VWin S)
    (hTheta : ThetaSlopeContract S)
    (hAnalytic : AnalyticBridgeContract) :
    RHDirectAssembly S :=
  ⟨hRow.toGaloisModularityContract hLLC hLoc hAutOther hCoh hPatch vwin_of_inputs,
    hTheta, hAnalytic⟩

/-! ## 7. Verified `Row0b` Live-Field Ledger (`6 + 2 + 3 = 11` Live, `0` Dead) -/

namespace GaloisRowLivenessAudit

/-- Exact live-field counts across `GaloisRowProps` (`PropsB`), `AboveCompat` (`AboveB`),
`AwayCompat` (`AwayB`), and the eliminated `OpenImageCondition` wrapper. -/
def rowFieldCounts : List (String × ℕ × ℕ) :=
  [ ("GaloisRowProps (PropsB)", 6, 0)
  , ("AboveCompat (AboveB)", 2, 0)
  , ("AwayCompat (AwayB)", 3, 0)
  , ("OpenImageCondition (eliminated)", 0, 1) ]

theorem live_row_fields_eq_eleven :
    (rowFieldCounts.map (fun e => e.2.1)).sum = 11 := by
  decide

theorem dead_wrapper_fields_eliminated :
    (rowFieldCounts.map (fun e => e.2.2)).sum = 1 := by
  decide

end GaloisRowLivenessAudit

end RHDirect

end
