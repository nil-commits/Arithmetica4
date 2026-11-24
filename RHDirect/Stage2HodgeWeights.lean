import RHDirect.GaloisRowCore
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.Data.Multiset.Sort

/-!
# RHDirect.Stage2HodgeWeights

Hodge–Tate / Sen-weight filtration theory, Newton & Hodge polygon convexity, Fontaine's
weakly admissible filtered `φ`-modules, polarization reflection symmetry `w ↦ c - w`,
Fontaine–Laffaille / Sen distinct-weight regularity (`RegularAlgebraic`), and direct
construction of `CMInfCharDatum` and `GaloisRowProps.weights` / `GaloisRowProps.weights_conj`
underneath `RHDirect.GaloisRowCore` (`GeoOne`).

## Contents

1. **Exhaustive Bounded Decreasing Filtrations & Hodge–Tate Weight Multisets**:
   - `HodgeFiltration K V` on a finite-dimensional `K`-vector space `V`, graded jump
     dimensions `jump i = finrank (Fil^i V / Fil^{i+1} V)`, weight multiset `weights : Multiset ℤ`,
     and Hodge number `tH : ℤ := weights.sum`.
   - Exact telescoping dimension identity (`weights_card`), count characterization
     (`weights_count`), and summation-by-parts formula (`tH_eq_sum_finrank`).
   - Monotonicity and **Fontaine strictness** (`tH_le_of_fil_le`, `fil_eq_of_le_of_tH_eq`):
     if `F₁.fil i ≤ F₂.fil i` for all `i`, then `F₁.tH ≤ F₂.tH`, with equality iff `F₁.fil = F₂.fil`.
   - Induced subspace filtration (`inducedSub`), pullback/pushforward (`comapInj`, `mapSurj`),
     Tate twist shift (`shift`), and exact multiset/Hodge-number additivity on strict
     short exact sequences (`StrictFilteredSES`).
2. **Newton & Hodge Polygons, Convexity, Additivity & Reflection Duality**:
   - `polygon S k` (partial sum of the `k` smallest slopes in `S : Multiset ℚ`),
     convexity (`polygon_convex`), Ky Fan variational lower bound (`polygon_le_sum_of_le`),
     and exact Minkowski-sum convolution (`exists_split_polygon_add`).
   - Hodge-below-Newton dominance `PolygonLe H N`: reflexivity, transitivity, direct-sum /
     short-exact-sequence stability (`PolygonLe.add`), and **polarization reflection
     equivalence** `PolygonLe H N ↔ PolygonLe (reflectSlopes c H) (reflectSlopes c N)`.
3. **Filtered `φ`-Modules, Determinant Weight Sum & Fontaine Weak Admissibility**:
   - `FilteredPhiMod K`, determinant rank-1 module `det` with `det.tH = M.fil.weights.sum`
     and `det.tN = M.newton.sum`, Tate twist `twist`, and `IsWeaklyAdmissible`
     (`t_N(M) = t_H(M)` and `t_H(U) ≤ t_N(U)` for all `φ`-stable `U ≤ M`).
   - Short exact sequences `FilteredPhiSES M₁ M₂ M₃`: exact additivity of Hodge weights,
     `t_H`, `t_N`, determinant weight sums, and Newton/Hodge polygons; **Fontaine's
     extension theorem** (`isWeaklyAdmissible_mid`), **subobject/quotient admissibility**
     (`isWeaklyAdmissible_left`, `isWeaklyAdmissible_right`), and **strictness of
     injective morphisms between weakly admissible modules** (`strict_of_weaklyAdmissible`).
4. **Polarization Reflection `w ↦ c - w`, Fontaine–Laffaille / Sen Regularity (`RegularAlgebraic`)**:
   - `reflectWeights c W := W.map (c - ·)`: involution, cardinality, sum symmetry, twist
     covariance, and regularity preservation.
   - `IsRegularWeights W := W.Nodup`: jump-`≤ 1` characterization (`isRegular_iff_jump_le_one`),
     strict spacing of sorted weights (`sortedWeights_add_le_of_regular`), spread lower bound
     `max - min ≥ card - 1`, and Fontaine–Laffaille width bound (`card < p`).
   - `RegularAlgebraic I` on `CMInfCharDatum`: equivalence with `∀ τ, (HT τ).Nodup`,
     integer separation `1 ≤ |z₁.re - z₂.re|` of distinct eigenvalues, and twist invariance.
5. **Direct Construction of `CMInfCharDatum`, `GaloisRowProps.weights` & `weights_conj`**:
   - `CrystallineWeightFamily`: a CM-indexed family of crystalline Hodge–Tate filtrations
     satisfying polarization reflection `(F (c τ)).weights = reflectWeights wt (F τ).weights`.
   - Direct unconditional construction of `CMInfCharDatum` satisfying `IsRegAlg`,
     `MatchesWeights`, `IsPolarized wt`, `HasConjWeights wt`, `RegularAlgebraic` (when
     jumps `≤ 1`), and determinant sum symmetry, plus direct assembly of `GaloisRowProps`
     (`galoisRowProps_of_crystallineFamily`, `galoisRowProps_of_crystalline_localGlobal`)
     into `RHDirect.GaloisRowCore`.

Zero `sorry`, zero custom `axiom`s.
-/

noncomputable section

open Polynomial

namespace RHDirect
namespace Stage2HodgeWeights

/-! ## 1. Exhaustive Bounded Decreasing Filtrations & Hodge–Tate Weight Multisets -/

/-- An exhaustive, separated, bounded decreasing `ℤ`-filtration on a finite-dimensional
vector space `V` over a field `K`. -/
structure HodgeFiltration (K : Type*) [Field K] (V : Type*)
    [AddCommGroup V] [Module K V] [Module.Finite K V] where
  fil : ℤ → Submodule K V
  antitone : ∀ ⦃i j : ℤ⦄, i ≤ j → fil j ≤ fil i
  botBound : ℤ
  topBound : ℤ
  bot_le_top : botBound ≤ topBound
  eq_top_of_le : ∀ i : ℤ, i ≤ botBound → fil i = ⊤
  eq_bot_of_gt : ∀ i : ℤ, topBound < i → fil i = ⊥

namespace HodgeFiltration

section Basic

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]

/-- Dimension of the `i`-th filtration step `Fil^i V`. -/
def dimAt (F : HodgeFiltration K V) (i : ℤ) : ℕ :=
  Module.finrank K (F.fil i)

/-- The `i`-th Hodge–Tate jump multiplicity `dim(Fil^i V) - dim(Fil^{i+1} V)`. -/
def jump (F : HodgeFiltration K V) (i : ℤ) : ℕ :=
  F.dimAt i - F.dimAt (i + 1)

theorem dimAt_antitone (F : HodgeFiltration K V) {i j : ℤ} (hij : i ≤ j) :
    F.dimAt j ≤ F.dimAt i :=
  Submodule.finrank_mono (F.antitone hij)

theorem dimAt_succ_le (F : HodgeFiltration K V) (i : ℤ) :
    F.dimAt (i + 1) ≤ F.dimAt i :=
  F.dimAt_antitone (by omega)

theorem dimAt_of_le_bot (F : HodgeFiltration K V) {i : ℤ} (hi : i ≤ F.botBound) :
    F.dimAt i = Module.finrank K V := by
  unfold dimAt
  rw [F.eq_top_of_le i hi, finrank_top]

theorem dimAt_of_gt_top (F : HodgeFiltration K V) {i : ℤ} (hi : F.topBound < i) :
    F.dimAt i = 0 := by
  unfold dimAt
  rw [F.eq_bot_of_gt i hi, finrank_bot]

theorem jump_eq_zero_of_lt_bot (F : HodgeFiltration K V) {i : ℤ} (hi : i < F.botBound) :
    F.jump i = 0 := by
  unfold jump
  rw [F.dimAt_of_le_bot (by omega), F.dimAt_of_le_bot (by omega), Nat.sub_self]

theorem jump_eq_zero_of_gt_top (F : HodgeFiltration K V) {i : ℤ} (hi : F.topBound < i) :
    F.jump i = 0 := by
  unfold jump
  rw [F.dimAt_of_gt_top hi, F.dimAt_of_gt_top (by omega), Nat.sub_self]

theorem jump_cast_int (F : HodgeFiltration K V) (i : ℤ) :
    (F.jump i : ℤ) = (F.dimAt i : ℤ) - (F.dimAt (i + 1) : ℤ) := by
  unfold jump
  exact Nat.cast_sub (F.dimAt_succ_le i)

/-- The `i`-th Hodge jump equals the exact dimension of the graded piece
`Gr^i V = Fil^i V / Fil^{i+1} V`. -/
theorem jump_eq_finrank_graded (F : HodgeFiltration K V) (i : ℤ) :
    F.jump i = Module.finrank K (F.fil i ⧸ (F.fil (i + 1)).comap (F.fil i).subtype) := by
  have hle : F.fil (i + 1) ≤ F.fil i := F.antitone (by omega)
  have hq := Submodule.finrank_quotient_add_finrank ((F.fil (i + 1)).comap (F.fil i).subtype)
  have hsub : Module.finrank K ((F.fil (i + 1)).comap (F.fil i).subtype) = F.dimAt (i + 1) := by
    have hker :
        LinearMap.ker
          ((F.fil i).subtype.domRestrict ((F.fil (i + 1)).comap (F.fil i).subtype)) = ⊥ := by
      ext x
      simp
    have hrange :
        LinearMap.range
          ((F.fil i).subtype.domRestrict ((F.fil (i + 1)).comap (F.fil i).subtype)) =
          F.fil (i + 1) := by
      ext y
      constructor
      · rintro ⟨⟨⟨z, _⟩, hz2⟩, rfl⟩
        exact hz2
      · intro hy
        exact ⟨⟨⟨y, hle hy⟩, hy⟩, rfl⟩
    have hrank := LinearMap.finrank_range_add_finrank_ker
      ((F.fil i).subtype.domRestrict ((F.fil (i + 1)).comap (F.fil i).subtype))
    rw [hrange, hker, finrank_bot, add_zero] at hrank
    exact hrank.symm
  unfold jump dimAt at *
  omega

/-- The Hodge–Tate weight multiset of `F`, recording each integer `i` with multiplicity
`F.jump i = dim(Gr^i V)`. -/
def weights (F : HodgeFiltration K V) : Multiset ℤ :=
  (Finset.Icc F.botBound F.topBound).sum fun i => Multiset.replicate (F.jump i) i

/-- The Hodge number `t_H(F) = ∑_{w ∈ weights F} w = ∑_i i · dim(Gr^i V)`. -/
def tH (F : HodgeFiltration K V) : ℤ :=
  F.weights.sum

/-- General telescoping sum for `d (a + k) - d (a + k + 1)` over `k ∈ Finset.range n`. -/
private theorem sum_range_sub_step (d : ℤ → ℤ) (a : ℤ) (n : ℕ) :
    (Finset.range n).sum (fun k => d (a + (k : ℤ)) - d (a + (k : ℤ) + 1)) =
      d a - d (a + (n : ℤ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hstep : a + ((n + 1 : ℕ) : ℤ) = a + (n : ℤ) + 1 := by push_cast; ring
    rw [hstep]
    ring

/-- General summation-by-parts identity for weighted filtration jumps:
`∑_{k=0}^{n-1} (a + k) (d(a+k) - d(a+k+1)) = a · d(a) - (a + n) · d(a + n) + ∑_{k=0}^{n-1} d(a + k + 1)`. -/
private theorem sum_range_weighted_sub_step (d : ℤ → ℤ) (a : ℤ) (n : ℕ) :
    (Finset.range n).sum (fun k => (a + (k : ℤ)) * (d (a + (k : ℤ)) - d (a + (k : ℤ) + 1))) =
      a * d a - (a + (n : ℤ)) * d (a + (n : ℤ)) +
        (Finset.range n).sum (fun k => d (a + (k : ℤ) + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have hstep : a + ((n + 1 : ℕ) : ℤ) = a + (n : ℤ) + 1 := by push_cast; ring
    rw [hstep]
    ring

/-- Reindexing an integer closed interval `Finset.Icc a b` (`a ≤ b`) to `Finset.range ((b - a + 1).toNat)`. -/
private theorem sum_Icc_eq_sum_range {M : Type*} [AddCommMonoid M]
    (a b : ℤ) (hab : a ≤ b) (f : ℤ → M) :
    (Finset.Icc a b).sum f =
      (Finset.range (b - a + 1).toNat).sum (fun k => f (a + (k : ℤ))) := by
  symm
  refine Finset.sum_nbij' (fun k => a + (k : ℤ)) (fun i => (i - a).toNat) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_range] at hk
    rw [Finset.mem_Icc]
    omega
  · intro i hi
    rw [Finset.mem_Icc] at hi
    rw [Finset.mem_range]
    omega
  · intro k hk
    rw [Finset.mem_range] at hk
    omega
  · intro i hi
    rw [Finset.mem_Icc] at hi
    omega
  · intro k _
    rfl

private theorem multiset_card_finset_sum {ι α : Type*} (s : Finset ι) (f : ι → Multiset α) :
    (s.sum f).card = s.sum (fun i => (f i).card) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Multiset.card_add, ih]

/-- Exact multiplicity formula: the multiplicity of any `i : ℤ` in `F.weights` is `F.jump i`,
independent of the bounding interval `[botBound, topBound]`. -/
theorem weights_count (F : HodgeFiltration K V) (i : ℤ) :
    F.weights.count i = F.jump i := by
  unfold weights
  rw [Multiset.count_sum']
  by_cases hi : i ∈ Finset.Icc F.botBound F.topBound
  · rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Multiset.count_replicate, hji]
    · intro hni
      exact absurd hi hni
  · rw [Finset.sum_eq_zero]
    · rw [Finset.mem_Icc] at hi
      by_cases hlt : i < F.botBound
      · exact (F.jump_eq_zero_of_lt_bot hlt).symm
      · have hgt : F.topBound < i := by omega
        exact (F.jump_eq_zero_of_gt_top hgt).symm
    · intro j hj
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      simp [Multiset.count_replicate, hji]

/-- The weight multiset `F.weights` can be computed over any bounding interval `[a, b]`
containing `[F.botBound, F.topBound]`. -/
theorem weights_eq_sum_Icc (F : HodgeFiltration K V) {a b : ℤ}
    (ha : a ≤ F.botBound) (hb : F.topBound ≤ b) :
    F.weights = (Finset.Icc a b).sum (fun i => Multiset.replicate (F.jump i) i) := by
  ext i
  rw [F.weights_count i, Multiset.count_sum']
  by_cases hi : i ∈ Finset.Icc a b
  · rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Multiset.count_replicate, hji]
    · intro hni
      exact absurd hi hni
  · rw [Finset.sum_eq_zero]
    · rw [Finset.mem_Icc] at hi
      by_cases hlt : i < a
      · exact F.jump_eq_zero_of_lt_bot (lt_of_lt_of_le hlt ha)
      · have hgt : b < i := by omega
        exact F.jump_eq_zero_of_gt_top (lt_of_le_of_lt hb hgt)
    · intro j hj
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      simp [Multiset.count_replicate, hji]

/-- **Telescoping Dimension Theorem**: the cardinality of `F.weights` equals `finrank K V`. -/
theorem weights_card (F : HodgeFiltration K V) :
    F.weights.card = Module.finrank K V := by
  have hcard : (F.weights.card : ℤ) = (Module.finrank K V : ℤ) := by
    unfold weights
    rw [multiset_card_finset_sum]
    simp only [Multiset.card_replicate]
    rw [Nat.cast_sum]
    have hcast :
        (Finset.Icc F.botBound F.topBound).sum (fun i => (F.jump i : ℤ)) =
          (Finset.Icc F.botBound F.topBound).sum
            (fun i => (F.dimAt i : ℤ) - (F.dimAt (i + 1) : ℤ)) :=
      Finset.sum_congr rfl fun i _ => F.jump_cast_int i
    rw [hcast, sum_Icc_eq_sum_range F.botBound F.topBound F.bot_le_top,
      sum_range_sub_step (fun i => (F.dimAt i : ℤ))]
    have htop : F.topBound < F.botBound + ((F.topBound - F.botBound + 1).toNat : ℤ) := by
      have := F.bot_le_top
      omega
    rw [F.dimAt_of_le_bot le_rfl, F.dimAt_of_gt_top htop]
    simp
  exact Nat.cast_injective hcard

/-- Exact formula for `t_H(F)` over any bounding interval `[a, b]` containing `[botBound, topBound]`. -/
theorem tH_eq_sum_Icc (F : HodgeFiltration K V) {a b : ℤ}
    (ha : a ≤ F.botBound) (hb : F.topBound ≤ b) :
    F.tH = (Finset.Icc a b).sum (fun i => (F.jump i : ℤ) * i) := by
  unfold tH
  rw [F.weights_eq_sum_Icc ha hb, Multiset.sum_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Multiset.sum_replicate]

/-- **Summation-by-Parts Formula for `t_H(F)`**:
for any `a ≤ F.botBound` and `F.topBound ≤ b`,
`t_H(F) = a · finrank K V + ∑_{k=0}^{b-a} dim(Fil^{a+k+1} V)`. -/
theorem tH_eq_sum_finrank (F : HodgeFiltration K V) {a b : ℤ}
    (ha : a ≤ F.botBound) (hb : F.topBound ≤ b) :
    F.tH = a * (Module.finrank K V : ℤ) +
      (Finset.range (b - a + 1).toNat).sum (fun k => (F.dimAt (a + (k : ℤ) + 1) : ℤ)) := by
  have hab : a ≤ b := le_trans ha (le_trans F.bot_le_top hb)
  rw [F.tH_eq_sum_Icc ha hb]
  have h1 :
      (Finset.Icc a b).sum (fun i => (F.jump i : ℤ) * i) =
        (Finset.Icc a b).sum (fun i => i * ((F.dimAt i : ℤ) - (F.dimAt (i + 1) : ℤ))) :=
    Finset.sum_congr rfl fun i _ => by rw [F.jump_cast_int i]; ring
  rw [h1, sum_Icc_eq_sum_range a b hab,
    sum_range_weighted_sub_step (fun i => (F.dimAt i : ℤ))]
  have hgt : F.topBound < a + ((b - a + 1).toNat : ℤ) := by omega
  rw [F.dimAt_of_le_bot ha, F.dimAt_of_gt_top hgt]
  simp

/-- **Monotonicity of `t_H`**: strengthening a filtration (`F₁.fil i ≤ F₂.fil i` for all `i`)
can only increase `t_H`. -/
theorem tH_le_of_fil_le {F₁ F₂ : HodgeFiltration K V} (hle : ∀ i : ℤ, F₁.fil i ≤ F₂.fil i) :
    F₁.tH ≤ F₂.tH := by
  set a := min F₁.botBound F₂.botBound
  set b := max F₁.topBound F₂.topBound
  rw [F₁.tH_eq_sum_finrank (min_le_left _ _) (le_max_left _ _),
    F₂.tH_eq_sum_finrank (min_le_right _ _) (le_max_right _ _)]
  gcongr with k _
  exact Submodule.finrank_mono (hle _)

/-- **Fontaine Strictness Lemma**: if `F₁.fil i ≤ F₂.fil i` for all `i` and `F₁.tH = F₂.tH`,
then the two filtrations coincide identically (`∀ i, F₁.fil i = F₂.fil i`). -/
theorem fil_eq_of_le_of_tH_eq {F₁ F₂ : HodgeFiltration K V}
    (hle : ∀ i : ℤ, F₁.fil i ≤ F₂.fil i) (heq : F₁.tH = F₂.tH) :
    ∀ i : ℤ, F₁.fil i = F₂.fil i := by
  set a := min F₁.botBound F₂.botBound
  set b := max F₁.topBound F₂.topBound
  have ha₁ : a ≤ F₁.botBound := min_le_left _ _
  have ha₂ : a ≤ F₂.botBound := min_le_right _ _
  have hb₁ : F₁.topBound ≤ b := le_max_left _ _
  have hb₂ : F₂.topBound ≤ b := le_max_right _ _
  have hab : a ≤ b := le_trans ha₁ (le_trans F₁.bot_le_top hb₁)
  have hsum :
      (Finset.range (b - a + 1).toNat).sum (fun k => (F₁.dimAt (a + (k : ℤ) + 1) : ℤ)) =
        (Finset.range (b - a + 1).toNat).sum (fun k => (F₂.dimAt (a + (k : ℤ) + 1) : ℤ)) := by
    have h1 := F₁.tH_eq_sum_finrank ha₁ hb₁
    have h2 := F₂.tH_eq_sum_finrank ha₂ hb₂
    linarith
  have hdiff_zero :
      (Finset.range (b - a + 1).toNat).sum
        (fun k => (F₂.dimAt (a + (k : ℤ) + 1) : ℤ) - (F₁.dimAt (a + (k : ℤ) + 1) : ℤ)) = 0 := by
    rw [Finset.sum_sub_distrib, hsum, sub_self]
  have hterm :
      ∀ k ∈ Finset.range (b - a + 1).toNat,
        (F₂.dimAt (a + (k : ℤ) + 1) : ℤ) - (F₁.dimAt (a + (k : ℤ) + 1) : ℤ) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun k _ => by
      have h := Submodule.finrank_mono (hle (a + (k : ℤ) + 1))
      exact sub_nonneg.mpr (Int.ofNat_le.mpr h)).mp hdiff_zero
  intro i
  by_cases hi1 : i ≤ a
  · rw [F₁.eq_top_of_le i (le_trans hi1 ha₁), F₂.eq_top_of_le i (le_trans hi1 ha₂)]
  · by_cases hi2 : b < i
    · rw [F₁.eq_bot_of_gt i (lt_of_le_of_lt hb₁ hi2), F₂.eq_bot_of_gt i (lt_of_le_of_lt hb₂ hi2)]
    · have hk_mem : (i - a - 1).toNat ∈ Finset.range (b - a + 1).toNat := by
        rw [Finset.mem_range]
        omega
      have hk_eq : a + ((i - a - 1).toNat : ℤ) + 1 = i := by omega
      have h0 := hterm (i - a - 1).toNat hk_mem
      rw [hk_eq] at h0
      have hdim : F₁.dimAt i = F₂.dimAt i := by omega
      exact Submodule.eq_of_le_of_finrank_eq (hle i) hdim

/-- Tate twist / index shift of a filtration by `r : ℤ`: `(F.shift r).fil i = F.fil (i - r)`.
Shifts every Hodge–Tate weight `w ↦ w + r` and adds `finrank K V * r` to `t_H`. -/
def shift (F : HodgeFiltration K V) (r : ℤ) : HodgeFiltration K V where
  fil i := F.fil (i - r)
  antitone _ _ hij := F.antitone (by omega)
  botBound := F.botBound + r
  topBound := F.topBound + r
  bot_le_top := by linarith [F.bot_le_top]
  eq_top_of_le i hi := F.eq_top_of_le (i - r) (by omega)
  eq_bot_of_gt i hi := F.eq_bot_of_gt (i - r) (by omega)

theorem shift_jump (F : HodgeFiltration K V) (r i : ℤ) :
    (F.shift r).jump i = F.jump (i - r) := by
  have h : i + 1 - r = (i - r) + 1 := by omega
  have hdim : (F.shift r).dimAt (i + 1) = F.dimAt (i - r + 1) :=
    congrArg (fun j : ℤ => F.dimAt j) h
  unfold jump
  rw [hdim]
  rfl

theorem shift_weights (F : HodgeFiltration K V) (r : ℤ) :
    (F.shift r).weights = F.weights.map (fun w => w + r) := by
  ext j
  rw [(F.shift r).weights_count j, F.shift_jump r j]
  have hinj : Function.Injective (fun w : ℤ => w + r) := fun x y hxy => by dsimp at hxy; omega
  have hmap := Multiset.count_map_eq_count' (fun w : ℤ => w + r) F.weights hinj (j - r)
  have hsub : (j - r) + r = j := by omega
  rw [hsub, F.weights_count (j - r)] at hmap
  exact hmap.symm

theorem shift_tH (F : HodgeFiltration K V) (r : ℤ) :
    (F.shift r).tH = F.tH + (Module.finrank K V : ℤ) * r := by
  unfold tH
  rw [F.shift_weights r]
  have hsum : ∀ s : Multiset ℤ, (s.map (fun w : ℤ => w + r)).sum = s.sum + (s.card : ℤ) * r := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Nat.cast_add,
        Nat.cast_one]
      linarith
  rw [hsum F.weights, F.weights_card]

/-- Induced subspace filtration on a submodule `U ≤ V`: `Fil^i U = (Fil^i V).comap U.subtype`. -/
def inducedSub (F : HodgeFiltration K V) (U : Submodule K V) : HodgeFiltration K U where
  fil i := (F.fil i).comap U.subtype
  antitone _ _ hij := Submodule.comap_mono (F.antitone hij)
  botBound := F.botBound
  topBound := F.topBound
  bot_le_top := F.bot_le_top
  eq_top_of_le i hi := by simp [F.eq_top_of_le i hi]
  eq_bot_of_gt i hi := by
    rw [F.eq_bot_of_gt i hi]
    ext x
    simp

/-- Shifting commutes with taking the induced subspace filtration. -/
theorem inducedSub_shift (F : HodgeFiltration K V) (U : Submodule K V) (r : ℤ) :
    (F.shift r).inducedSub U = (F.inducedSub U).shift r := rfl

/-- Induced filtration on `⊥ : Submodule K V` has weight multiset `0` and `t_H = 0`. -/
theorem inducedSub_bot_tH (F : HodgeFiltration K V) :
    (F.inducedSub ⊥).tH = 0 := by
  have hcard : (F.inducedSub ⊥).weights.card = 0 := by
    rw [(F.inducedSub ⊥).weights_card, finrank_bot]
  have hw : (F.inducedSub ⊥).weights = 0 := Multiset.card_eq_zero.mp hcard
  simp [tH, hw]

/-- Induced filtration on `⊤ : Submodule K V` has the exact same weights and `t_H` as `F`. -/
theorem inducedSub_top_weights (F : HodgeFiltration K V) :
    (F.inducedSub ⊤).weights = F.weights := by
  ext i
  rw [(F.inducedSub ⊤).weights_count i, F.weights_count i]
  have hdim : ∀ j : ℤ, (F.inducedSub ⊤).dimAt j = F.dimAt j := by
    intro j
    unfold dimAt inducedSub
    dsimp
    have hrank := LinearMap.finrank_range_add_finrank_ker
      ((⊤ : Submodule K V).subtype.domRestrict ((F.fil j).comap (⊤ : Submodule K V).subtype))
    have hker :
        LinearMap.ker
          ((⊤ : Submodule K V).subtype.domRestrict
            ((F.fil j).comap (⊤ : Submodule K V).subtype)) = ⊥ := by
      ext x; simp
    have hrange :
        LinearMap.range
          ((⊤ : Submodule K V).subtype.domRestrict
            ((F.fil j).comap (⊤ : Submodule K V).subtype)) = F.fil j := by
      ext y
      constructor
      · rintro ⟨⟨⟨z, _⟩, hz⟩, rfl⟩; exact hz
      · intro hy; exact ⟨⟨⟨y, trivial⟩, hy⟩, rfl⟩
    rw [hrange, hker, finrank_bot, add_zero] at hrank
    exact hrank.symm
  simp [jump, hdim]

theorem inducedSub_top_tH (F : HodgeFiltration K V) :
    (F.inducedSub ⊤).tH = F.tH := by
  unfold tH
  rw [F.inducedSub_top_weights]

/-- Pullback filtration along an injective linear map `f : U →ₗ[K] V`. -/
def comapInj {U : Type*} [AddCommGroup U] [Module K U] [Module.Finite K U]
    (F : HodgeFiltration K V) (f : U →ₗ[K] V) (hf : Function.Injective f) :
    HodgeFiltration K U where
  fil i := (F.fil i).comap f
  antitone _ _ hij := Submodule.comap_mono (F.antitone hij)
  botBound := F.botBound
  topBound := F.topBound
  bot_le_top := F.bot_le_top
  eq_top_of_le i hi := by simp [F.eq_top_of_le i hi]
  eq_bot_of_gt i hi := by
    rw [F.eq_bot_of_gt i hi]
    ext x
    simp [LinearMap.map_eq_zero_iff f hf]

/-- Pushforward (quotient) filtration along a surjective linear map `g : V →ₗ[K] W`. -/
def mapSurj {W : Type*} [AddCommGroup W] [Module K W] [Module.Finite K W]
    (F : HodgeFiltration K V) (g : V →ₗ[K] W) (hg : Function.Surjective g) :
    HodgeFiltration K W where
  fil i := (F.fil i).map g
  antitone _ _ hij := Submodule.map_mono (F.antitone hij)
  botBound := F.botBound
  topBound := F.topBound
  bot_le_top := F.bot_le_top
  eq_top_of_le i hi := by
    rw [F.eq_top_of_le i hi, Submodule.map_top, LinearMap.range_eq_top.mpr hg]
  eq_bot_of_gt i hi := by
    rw [F.eq_bot_of_gt i hi, Submodule.map_bot]

/-- Pulling back `F` along an injective `f : U →ₗ[K] V` yields the exact same weight multiset
as restricting `F` to `LinearMap.range f`. -/
theorem comapInj_weights_eq_inducedSub_range
    {U : Type*} [AddCommGroup U] [Module K U] [Module.Finite K U]
    (F : HodgeFiltration K V) (f : U →ₗ[K] V) (hf : Function.Injective f) :
    (F.comapInj f hf).weights = (F.inducedSub (LinearMap.range f)).weights := by
  ext i
  rw [(F.comapInj f hf).weights_count i, (F.inducedSub (LinearMap.range f)).weights_count i]
  have hdim : ∀ j : ℤ, (F.comapInj f hf).dimAt j = (F.inducedSub (LinearMap.range f)).dimAt j := by
    intro j
    unfold dimAt comapInj inducedSub
    dsimp
    have hker₁ : LinearMap.ker (f.domRestrict ((F.fil j).comap f)) = ⊥ := by
      ext ⟨u, hu⟩
      simp [LinearMap.map_eq_zero_iff f hf]
    have hrange₁ : LinearMap.range (f.domRestrict ((F.fil j).comap f)) =
        F.fil j ⊓ LinearMap.range f := by
      ext v
      constructor
      · rintro ⟨⟨u, hu⟩, rfl⟩
        exact ⟨hu, ⟨u, rfl⟩⟩
      · rintro ⟨hv, ⟨u, rfl⟩⟩
        exact ⟨⟨u, hv⟩, rfl⟩
    have hr₁ := LinearMap.finrank_range_add_finrank_ker (f.domRestrict ((F.fil j).comap f))
    rw [hrange₁, hker₁, finrank_bot, add_zero] at hr₁
    have hker₂ : LinearMap.ker
        ((LinearMap.range f).subtype.domRestrict
          ((F.fil j).comap (LinearMap.range f).subtype)) = ⊥ := by
      ext x; simp
    have hrange₂ : LinearMap.range
        ((LinearMap.range f).subtype.domRestrict
          ((F.fil j).comap (LinearMap.range f).subtype)) =
        F.fil j ⊓ LinearMap.range f := by
      ext v
      constructor
      · rintro ⟨⟨⟨w, hw⟩, hwf⟩, rfl⟩
        exact ⟨hwf, hw⟩
      · rintro ⟨hvf, hvr⟩
        exact ⟨⟨⟨v, hvr⟩, hvf⟩, rfl⟩
    have hr₂ := LinearMap.finrank_range_add_finrank_ker
      ((LinearMap.range f).subtype.domRestrict ((F.fil j).comap (LinearMap.range f).subtype))
    rw [hrange₂, hker₂, finrank_bot, add_zero] at hr₂
    exact hr₁.symm.trans hr₂
  simp [jump, hdim]

theorem comapInj_tH_eq_inducedSub_range
    {U : Type*} [AddCommGroup U] [Module K U] [Module.Finite K U]
    (F : HodgeFiltration K V) (f : U →ₗ[K] V) (hf : Function.Injective f) :
    (F.comapInj f hf).tH = (F.inducedSub (LinearMap.range f)).tH := by
  unfold tH
  rw [F.comapInj_weights_eq_inducedSub_range f hf]

/-- Every weight in `F.weights` lies in `[F.botBound, F.topBound]`. -/
theorem mem_weights_bounds (F : HodgeFiltration K V) {w : ℤ} (hw : w ∈ F.weights) :
    F.botBound ≤ w ∧ w ≤ F.topBound := by
  have hpos : 0 < F.weights.count w := Multiset.count_pos.mpr hw
  rw [F.weights_count w] at hpos
  constructor
  · by_contra h
    have hlt : w < F.botBound := by omega
    have := F.jump_eq_zero_of_lt_bot hlt
    omega
  · by_contra h
    have hgt : F.topBound < w := by omega
    have := F.jump_eq_zero_of_gt_top hgt
    omega

/-- Single-jump rank-1 filtration on `K` concentrated at weight `w : ℤ`. -/
def singleJump (K : Type*) [Field K] (w : ℤ) : HodgeFiltration K K where
  fil i := if i ≤ w then ⊤ else ⊥
  antitone i j hij := by
    by_cases hj : j ≤ w
    · have hi : i ≤ w := le_trans hij hj
      simp [hi, hj]
    · simp [hj]
  botBound := w
  topBound := w
  bot_le_top := le_rfl
  eq_top_of_le i hi := by simp [hi]
  eq_bot_of_gt i hi := by
    have hnot : ¬ i ≤ w := not_le.mpr hi
    simp [hnot]

theorem singleJump_weights (K : Type*) [Field K] (w : ℤ) :
    (singleJump K w).weights = {w} := by
  have hdim : ∀ j : ℤ, (singleJump K w).dimAt j = if j ≤ w then 1 else 0 := by
    intro j
    by_cases hj : j ≤ w
    · rw [if_pos hj, (singleJump K w).dimAt_of_le_bot hj, Module.finrank_self]
    · rw [if_neg hj, (singleJump K w).dimAt_of_gt_top (show (singleJump K w).topBound < j by change w < j; omega)]
  ext i
  rw [(singleJump K w).weights_count i]
  unfold jump
  rw [hdim i, hdim (i + 1)]
  by_cases hi : i = w
  · subst hi
    have h2 : ¬ i + 1 ≤ i := by omega
    simp [h2]
  · by_cases hlt : i < w
    · have h1 : i ≤ w := le_of_lt hlt
      have h2 : i + 1 ≤ w := by omega
      simp [h1, h2, hi]
    · have h1 : ¬ i ≤ w := by omega
      have h2 : ¬ i + 1 ≤ w := by omega
      simp [h1, h2, hi]

theorem singleJump_tH (K : Type*) [Field K] (w : ℤ) :
    (singleJump K w).tH = w := by
  simp [tH, singleJump_weights]

end Basic

end HodgeFiltration

/-- A strict short exact sequence of filtered finite-dimensional `K`-vector spaces
`0 → U →[f] V →[g] W → 0`, where `U` carries the induced subspace filtration and `W` carries
the quotient filtration. -/
structure StrictFilteredSES (K : Type*) [Field K]
    {U V W : Type*}
    [AddCommGroup U] [Module K U] [Module.Finite K U]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    [AddCommGroup W] [Module K W] [Module.Finite K W]
    (FU : HodgeFiltration K U) (FV : HodgeFiltration K V) (FW : HodgeFiltration K W) where
  f : U →ₗ[K] V
  g : V →ₗ[K] W
  f_inj : Function.Injective f
  g_surj : Function.Surjective g
  exact : LinearMap.range f = LinearMap.ker g
  strict_sub : ∀ i : ℤ, FU.fil i = (FV.fil i).comap f
  strict_quot : ∀ i : ℤ, FW.fil i = (FV.fil i).map g

namespace StrictFilteredSES

variable {K : Type*} [Field K]
  {U V W : Type*}
  [AddCommGroup U] [Module K U] [Module.Finite K U]
  [AddCommGroup V] [Module K V] [Module.Finite K V]
  [AddCommGroup W] [Module K W] [Module.Finite K W]
  {FU : HodgeFiltration K U} {FV : HodgeFiltration K V} {FW : HodgeFiltration K W}

/-- **Exact Dimension Additivity at Every Filtration Step `i : ℤ`**:
`dim(Fil^i V) = dim(Fil^i U) + dim(Fil^i W)`. -/
theorem dimAt_add (E : StrictFilteredSES K FU FV FW) (i : ℤ) :
    FV.dimAt i = FU.dimAt i + FW.dimAt i := by
  have hrank := LinearMap.finrank_range_add_finrank_ker (E.g.domRestrict (FV.fil i))
  have hrange : LinearMap.range (E.g.domRestrict (FV.fil i)) = FW.fil i := by
    rw [E.strict_quot i]
    ext w
    constructor
    · rintro ⟨⟨v, hv⟩, rfl⟩; exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩; exact ⟨⟨v, hv⟩, rfl⟩
  have hker : Module.finrank K (LinearMap.ker (E.g.domRestrict (FV.fil i))) = FU.dimAt i := by
    have hker_f : LinearMap.ker (E.f.domRestrict (FU.fil i)) = ⊥ := by
      ext ⟨u, hu⟩
      simp [LinearMap.map_eq_zero_iff E.f E.f_inj]
    have hrange_f :
        LinearMap.range (E.f.domRestrict (FU.fil i)) = FV.fil i ⊓ LinearMap.ker E.g := by
      rw [← E.exact, E.strict_sub i]
      ext v
      constructor
      · rintro ⟨⟨u, hu⟩, rfl⟩; exact ⟨hu, ⟨u, rfl⟩⟩
      · rintro ⟨hv, ⟨u, rfl⟩⟩; exact ⟨⟨u, hv⟩, rfl⟩
    have hr₁ := LinearMap.finrank_range_add_finrank_ker (E.f.domRestrict (FU.fil i))
    rw [hrange_f, hker_f, finrank_bot, add_zero] at hr₁
    have hker_s :
        LinearMap.ker
          ((FV.fil i).subtype.domRestrict (LinearMap.ker (E.g.domRestrict (FV.fil i)))) = ⊥ := by
      ext x; simp
    have hrange_s :
        LinearMap.range
          ((FV.fil i).subtype.domRestrict (LinearMap.ker (E.g.domRestrict (FV.fil i)))) =
          FV.fil i ⊓ LinearMap.ker E.g := by
      ext v
      constructor
      · rintro ⟨⟨⟨w, hw⟩, hwg⟩, rfl⟩
        exact ⟨hw, hwg⟩
      · rintro ⟨hvf, hvg⟩
        exact ⟨⟨⟨v, hvf⟩, hvg⟩, rfl⟩
    have hr₂ := LinearMap.finrank_range_add_finrank_ker
      ((FV.fil i).subtype.domRestrict (LinearMap.ker (E.g.domRestrict (FV.fil i))))
    rw [hrange_s, hker_s, finrank_bot, add_zero] at hr₂
    exact hr₂.symm.trans hr₁
  rw [hrange, hker] at hrank
  unfold HodgeFiltration.dimAt at *
  omega

/-- **Exact Jump Additivity**: `jump_V i = jump_U i + jump_W i` for all `i : ℤ`. -/
theorem jump_add (E : StrictFilteredSES K FU FV FW) (i : ℤ) :
    FV.jump i = FU.jump i + FW.jump i := by
  have h0 := E.dimAt_add i
  have h1 := E.dimAt_add (i + 1)
  have hu := FU.dimAt_succ_le i
  have hw := FW.dimAt_succ_le i
  unfold HodgeFiltration.jump
  omega

/-- **Exact Hodge–Tate Weight Multiset Additivity on Short Exact Sequences**:
`weights(V) = weights(U) + weights(W)`. -/
theorem weights_add (E : StrictFilteredSES K FU FV FW) :
    FV.weights = FU.weights + FW.weights := by
  ext i
  rw [Multiset.count_add, FV.weights_count i, FU.weights_count i, FW.weights_count i, E.jump_add i]

/-- **Exact Hodge Number Additivity**: `t_H(V) = t_H(U) + t_H(W)`. -/
theorem tH_add (E : StrictFilteredSES K FU FV FW) :
    FV.tH = FU.tH + FW.tH := by
  unfold HodgeFiltration.tH
  rw [E.weights_add, Multiset.sum_add]

end StrictFilteredSES

/-! ## 2. Newton & Hodge Polygons, Convexity, Additivity & Reflection Duality -/

/-- The ascending sorted list of slopes of a finite multiset `S : Multiset ℚ`. -/
def sortedSlopes (S : Multiset ℚ) : List ℚ :=
  S.sort (· ≤ ·)

/-- The Newton or Hodge polygon function `polygon S k` evaluated at integer abscissa `k`,
defined as the sum of the `k` smallest slopes in `S`. -/
def polygon (S : Multiset ℚ) (k : ℕ) : ℚ :=
  ((sortedSlopes S).take k).sum

/-- Reflection of a rational slope multiset `S` across `c / 2`: `x ↦ c - x`. -/
def reflectSlopes (c : ℚ) (S : Multiset ℚ) : Multiset ℚ :=
  S.map (fun x => c - x)

theorem sortedSlopes_length (S : Multiset ℚ) : (sortedSlopes S).length = S.card :=
  Multiset.length_sort (· ≤ ·)

theorem sortedSlopes_coe (S : Multiset ℚ) : ((sortedSlopes S : List ℚ) : Multiset ℚ) = S :=
  Multiset.sort_eq S (· ≤ ·)

theorem sortedSlopes_pairwise (S : Multiset ℚ) : (sortedSlopes S).Pairwise (· ≤ ·) :=
  Multiset.pairwise_sort S (· ≤ ·)

theorem polygon_zero (S : Multiset ℚ) : polygon S 0 = 0 := by
  simp [polygon]

theorem polygon_card (S : Multiset ℚ) : polygon S S.card = S.sum := by
  unfold polygon
  rw [← sortedSlopes_length S, List.take_length]
  have h := congrArg Multiset.sum (sortedSlopes_coe S)
  simpa using h

/-- **Convexity of Newton / Hodge Polygons**: slopes are non-decreasing, so
`polygon S (k + 1) - polygon S k ≤ polygon S (k + 2) - polygon S (k + 1)`
for all `k + 1 < S.card`. -/
theorem polygon_convex (S : Multiset ℚ) {k : ℕ} (hk : k + 1 < S.card) :
    polygon S (k + 1) - polygon S k ≤ polygon S (k + 2) - polygon S (k + 1) := by
  set L := sortedSlopes S
  have hlen : L.length = S.card := sortedSlopes_length S
  have hk1 : k < L.length := by omega
  have hk2 : k + 1 < L.length := by omega
  have htake1 : (L.take (k + 1)).sum = (L.take k).sum + L[k] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hk1, Option.toList_some, List.sum_append,
      List.sum_singleton]
  have htake2 : (L.take (k + 2)).sum = (L.take (k + 1)).sum + L[k + 1] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hk2, Option.toList_some, List.sum_append,
      List.sum_singleton]
  have hpair := List.pairwise_iff_getElem.mp (sortedSlopes_pairwise S) k (k + 1) hk1 hk2 (by omega)
  unfold polygon
  change (L.take (k + 1)).sum - (L.take k).sum ≤ (L.take (k + 2)).sum - (L.take (k + 1)).sum
  linarith

private theorem coe_take_le {α : Type*} (L : List α) (k : ℕ) :
    ((L.take k : List α) : Multiset α) ≤ (L : Multiset α) := by
  conv_rhs => rw [← List.take_append_drop k L]
  rw [← Multiset.coe_add]
  exact Multiset.le_add_right _ _

private theorem riesz_decomp {α : Type*} [DecidableEq α] {T S₁ S₂ : Multiset α}
    (h : T ≤ S₁ + S₂) : ∃ T₁ T₂ : Multiset α, T = T₁ + T₂ ∧ T₁ ≤ S₁ ∧ T₂ ≤ S₂ := by
  refine ⟨T ∩ S₁, T - (T ∩ S₁), ?_, Multiset.inter_le_right, ?_⟩
  · exact (add_tsub_cancel_of_le Multiset.inter_le_left).symm
  · rw [Multiset.le_iff_count] at h ⊢
    intro x
    have hx := h x
    rw [Multiset.count_add] at hx
    rw [Multiset.count_sub, Multiset.count_inter]
    omega

/-- Helper for the Ky Fan / variational inequality on sorted lists. -/
private theorem take_sum_le_of_le_sorted :
    ∀ (L : List ℚ), L.Pairwise (· ≤ ·) →
      ∀ (T : Multiset ℚ), T ≤ (L : Multiset ℚ) → (L.take T.card).sum ≤ T.sum
  | [], _, T, hT => by
    have h0 : T = 0 := Multiset.le_zero.mp hT
    simp [h0]
  | a :: L', hpair, T, hT => by
    rw [List.pairwise_cons] at hpair
    rcases hpair with ⟨ha, hL'⟩
    by_cases hT0 : T = 0
    · simp [hT0]
    · by_cases haT : a ∈ T
      · obtain ⟨T', rfl⟩ := Multiset.exists_cons_of_mem haT
        have hT' : T' ≤ (L' : Multiset ℚ) := by
          have : a ::ₘ T' ≤ a ::ₘ (L' : Multiset ℚ) := by simpa using hT
          exact (Multiset.cons_le_cons_iff a).mp this
        have ih := take_sum_le_of_le_sorted L' hL' T' hT'
        simp only [Multiset.card_cons, List.take_succ_cons, List.sum_cons, Multiset.sum_cons]
        linarith
      · have hTL' : T ≤ (L' : Multiset ℚ) := by
          rw [Multiset.le_iff_count] at hT ⊢
          intro x
          have hx : T.count x ≤ (a ::ₘ (L' : Multiset ℚ)).count x := by simpa using hT x
          by_cases hxa : x = a
          · subst hxa
            have h0 : T.count x = 0 := Multiset.count_eq_zero.mpr haT
            omega
          · rw [Multiset.count_cons_of_ne hxa] at hx
            exact hx
        obtain ⟨x, hxT⟩ := Multiset.exists_mem_of_ne_zero hT0
        obtain ⟨T', rfl⟩ := Multiset.exists_cons_of_mem hxT
        have hxL' : x ∈ L' := by
          have : x ∈ (L' : Multiset ℚ) := Multiset.mem_of_le hTL' hxT
          simpa using this
        have hax : a ≤ x := ha x hxL'
        have hT'L' : T' ≤ (L' : Multiset ℚ) := le_trans (Multiset.le_cons_self T' x) hTL'
        have ih := take_sum_le_of_le_sorted L' hL' T' hT'L'
        simp only [Multiset.card_cons, List.take_succ_cons, List.sum_cons, Multiset.sum_cons]
        linarith

/-- **Variational (Ky Fan) Characterization of Polygons**: for any sub-multiset `T ≤ S`,
`polygon S T.card ≤ T.sum`. -/
theorem polygon_le_sum_of_le {S T : Multiset ℚ} (hT : T ≤ S) :
    polygon S T.card ≤ T.sum := by
  have hT' : T ≤ ((sortedSlopes S : List ℚ) : Multiset ℚ) := by
    rwa [sortedSlopes_coe S]
  exact take_sum_le_of_le_sorted (sortedSlopes S) (sortedSlopes_pairwise S) T hT'

/-- **Subadditivity / Minkowski Upper Bound for Polygon Sums**:
for `k₁ ≤ S₁.card` and `k₂ ≤ S₂.card`,
`polygon (S₁ + S₂) (k₁ + k₂) ≤ polygon S₁ k₁ + polygon S₂ k₂`. -/
theorem polygon_add_le (S₁ S₂ : Multiset ℚ) {k₁ k₂ : ℕ}
    (hk₁ : k₁ ≤ S₁.card) (hk₂ : k₂ ≤ S₂.card) :
    polygon (S₁ + S₂) (k₁ + k₂) ≤ polygon S₁ k₁ + polygon S₂ k₂ := by
  let T₁ : Multiset ℚ := (((sortedSlopes S₁).take k₁ : List ℚ) : Multiset ℚ)
  let T₂ : Multiset ℚ := (((sortedSlopes S₂).take k₂ : List ℚ) : Multiset ℚ)
  have hT₁ : T₁ ≤ S₁ := by
    rw [← sortedSlopes_coe S₁]
    exact coe_take_le (sortedSlopes S₁) k₁
  have hT₂ : T₂ ≤ S₂ := by
    rw [← sortedSlopes_coe S₂]
    exact coe_take_le (sortedSlopes S₂) k₂
  have hc₁ : T₁.card = k₁ := by
    simp [T₁, List.length_take, sortedSlopes_length S₁, hk₁]
  have hc₂ : T₂.card = k₂ := by
    simp [T₂, List.length_take, sortedSlopes_length S₂, hk₂]
  have hle := polygon_le_sum_of_le (add_le_add hT₁ hT₂)
  rw [Multiset.card_add, hc₁, hc₂, Multiset.sum_add] at hle
  simpa [polygon, T₁, T₂] using hle

/-- **Exact Minkowski-Sum Convolution for Polygons**: for every `k ≤ (S₁ + S₂).card`,
there exist `k₁ ≤ S₁.card` and `k₂ ≤ S₂.card` with `k₁ + k₂ = k` attaining
`polygon (S₁ + S₂) k = polygon S₁ k₁ + polygon S₂ k₂`. -/
theorem exists_split_polygon_add (S₁ S₂ : Multiset ℚ) {k : ℕ}
    (hk : k ≤ (S₁ + S₂).card) :
    ∃ k₁ k₂ : ℕ, k₁ ≤ S₁.card ∧ k₂ ≤ S₂.card ∧ k₁ + k₂ = k ∧
      polygon (S₁ + S₂) k = polygon S₁ k₁ + polygon S₂ k₂ := by
  let T : Multiset ℚ := (((sortedSlopes (S₁ + S₂)).take k : List ℚ) : Multiset ℚ)
  have hT_le : T ≤ S₁ + S₂ := by
    rw [← sortedSlopes_coe (S₁ + S₂)]
    exact coe_take_le (sortedSlopes (S₁ + S₂)) k
  have hT_card : T.card = k := by
    simp only [T, Multiset.coe_card, List.length_take, sortedSlopes_length (S₁ + S₂)]
    omega
  have hT_sum : T.sum = polygon (S₁ + S₂) k := by
    simp [T, polygon]
  obtain ⟨T₁, T₂, hT_eq, hT₁, hT₂⟩ := riesz_decomp hT_le
  have hk₁ : T₁.card ≤ S₁.card := Multiset.card_le_card hT₁
  have hk₂ : T₂.card ≤ S₂.card := Multiset.card_le_card hT₂
  have hk_sum : T₁.card + T₂.card = k := by
    rw [← Multiset.card_add, ← hT_eq, hT_card]
  have hlow : polygon S₁ T₁.card + polygon S₂ T₂.card ≤ polygon (S₁ + S₂) k := by
    calc polygon S₁ T₁.card + polygon S₂ T₂.card
        ≤ T₁.sum + T₂.sum := add_le_add (polygon_le_sum_of_le hT₁) (polygon_le_sum_of_le hT₂)
      _ = (T₁ + T₂).sum := (Multiset.sum_add T₁ T₂).symm
      _ = T.sum := by rw [← hT_eq]
      _ = polygon (S₁ + S₂) k := hT_sum
  have hhigh : polygon (S₁ + S₂) k ≤ polygon S₁ T₁.card + polygon S₂ T₂.card := by
    rw [← hk_sum]
    exact polygon_add_le S₁ S₂ hk₁ hk₂
  exact ⟨T₁.card, T₂.card, hk₁, hk₂, hk_sum, le_antisymm hhigh hlow⟩

/-- Exact endpoint additivity of polygons on sums of slope multisets (short exact sequences). -/
theorem polygon_add_endpoint (S₁ S₂ : Multiset ℚ) :
    polygon (S₁ + S₂) (S₁ + S₂).card = polygon S₁ S₁.card + polygon S₂ S₂.card := by
  rw [polygon_card, polygon_card, polygon_card, Multiset.sum_add]

/-- Exact sorted list of a reflected multiset `S.map (c - ·)`. -/
theorem sortedSlopes_reflect (c : ℚ) (S : Multiset ℚ) :
    sortedSlopes (reflectSlopes c S) = ((sortedSlopes S).map (fun x => c - x)).reverse := by
  set L := sortedSlopes S
  set L' := (L.map (fun x => c - x)).reverse
  have hperm : List.Perm (sortedSlopes (reflectSlopes c S)) L' := by
    rw [← Multiset.coe_eq_coe, sortedSlopes_coe]
    change reflectSlopes c S = (((L.map (fun x => c - x)).reverse : List ℚ) : Multiset ℚ)
    rw [Multiset.coe_reverse]
    simp [reflectSlopes, L, ← Multiset.map_coe, sortedSlopes_coe]
  have hp1 : (sortedSlopes (reflectSlopes c S)).Pairwise (· ≤ ·) :=
    sortedSlopes_pairwise (reflectSlopes c S)
  have hp2 : L'.Pairwise (· ≤ ·) := by
    dsimp [L']
    rw [List.pairwise_reverse, List.pairwise_map]
    exact (sortedSlopes_pairwise S).imp fun {a b} hab => by linarith
  exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => le_antisymm h1 h2) hp1 hp2

private theorem list_sum_map_sub (c : ℚ) (L : List ℚ) :
    (L.map (fun x => c - x)).sum = (L.length : ℚ) * c - L.sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

private theorem reverse_take_eq_drop_reverse {α : Type*} (M : List α) {k : ℕ} (hk : k ≤ M.length) :
    M.reverse.take k = (M.drop (M.length - k)).reverse := by
  have hsplit : M.reverse = (M.drop (M.length - k)).reverse ++ (M.take (M.length - k)).reverse := by
    conv_lhs => rw [← List.take_append_drop (M.length - k) M]
    rw [List.reverse_append]
  rw [hsplit]
  have hlen : ((M.drop (M.length - k)).reverse).length = k := by
    rw [List.length_reverse, List.length_drop]
    omega
  rw [List.take_left' hlen]

/-- **Reflection Formula for Polygons (`x ↦ c - x`)**:
for every `k ≤ S.card`,
`polygon (reflectSlopes c S) k = k · c - S.sum + polygon S (S.card - k)`. -/
theorem polygon_reflect (c : ℚ) (S : Multiset ℚ) {k : ℕ} (hk : k ≤ S.card) :
    polygon (reflectSlopes c S) k = (k : ℚ) * c - S.sum + polygon S (S.card - k) := by
  unfold polygon
  rw [sortedSlopes_reflect c S]
  set L := sortedSlopes S
  have hlen : L.length = S.card := sortedSlopes_length S
  have hmlen : (L.map (fun x => c - x)).length = S.card := by simp [hlen]
  rw [reverse_take_eq_drop_reverse (L.map (fun x => c - x)) (by omega), List.sum_reverse, hmlen,
    ← List.map_drop, list_sum_map_sub]
  have hdroplen : (L.drop (S.card - k)).length = k := by
    rw [List.length_drop, hlen]
    omega
  have hsum_split : (L.take (S.card - k)).sum + (L.drop (S.card - k)).sum = L.sum := by
    rw [← List.sum_append, List.take_append_drop]
  have hLsum : L.sum = S.sum := by
    have h := congrArg Multiset.sum (sortedSlopes_coe S)
    simpa [L] using h
  rw [hdroplen]
  linarith

/-- **Hodge-below-Newton Polygon Dominance** (`PolygonLe H N`):
`H` and `N` have equal cardinality, `polygon H k ≤ polygon N k` at every abscissa `k ≤ |H|`,
and share the same endpoint `H.sum = N.sum` (`t_H = t_N`). -/
def PolygonLe (H N : Multiset ℚ) : Prop :=
  H.card = N.card ∧ (∀ k : ℕ, k ≤ H.card → polygon H k ≤ polygon N k) ∧ H.sum = N.sum

namespace PolygonLe

theorem refl (S : Multiset ℚ) : PolygonLe S S :=
  ⟨rfl, fun _ _ => le_rfl, rfl⟩

theorem trans {S₁ S₂ S₃ : Multiset ℚ} (h₁₂ : PolygonLe S₁ S₂) (h₂₃ : PolygonLe S₂ S₃) :
    PolygonLe S₁ S₃ :=
  ⟨h₁₂.1.trans h₂₃.1,
    fun k hk => le_trans (h₁₂.2.1 k hk) (h₂₃.2.1 k (h₁₂.1 ▸ hk)),
    h₁₂.2.2.trans h₂₃.2.2⟩

/-- **Exact Stability of Hodge-below-Newton Dominance on Direct Sums / Short Exact Sequences**. -/
theorem add {H₁ N₁ H₂ N₂ : Multiset ℚ} (h₁ : PolygonLe H₁ N₁) (h₂ : PolygonLe H₂ N₂) :
    PolygonLe (H₁ + H₂) (N₁ + N₂) := by
  refine ⟨by simp [h₁.1, h₂.1], ?_, by simp [h₁.2.2, h₂.2.2]⟩
  intro k hk
  have hkN : k ≤ (N₁ + N₂).card := by simpa [h₁.1, h₂.1] using hk
  obtain ⟨k₁, k₂, hk₁, hk₂, hksum, hNeq⟩ := exists_split_polygon_add N₁ N₂ hkN
  rw [hNeq, ← hksum]
  calc polygon (H₁ + H₂) (k₁ + k₂)
      ≤ polygon H₁ k₁ + polygon H₂ k₂ :=
        polygon_add_le H₁ H₂ (h₁.1.symm ▸ hk₁) (h₂.1.symm ▸ hk₂)
    _ ≤ polygon N₁ k₁ + polygon N₂ k₂ :=
        add_le_add (h₁.2.1 k₁ (h₁.1.symm ▸ hk₁)) (h₂.2.1 k₂ (h₂.1.symm ▸ hk₂))

theorem reflectSlopes_sum (c : ℚ) (S : Multiset ℚ) :
    (reflectSlopes c S).sum = (S.card : ℚ) * c - S.sum := by
  induction S using Multiset.induction_on with
  | empty => simp [reflectSlopes]
  | cons a s ih =>
    simp only [reflectSlopes, Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons,
      Nat.cast_add, Nat.cast_one] at ih ⊢
    linarith

/-- **Polarization Reflection Preserves Hodge-below-Newton Dominance (`w ↦ c - w`)**. -/
theorem reflect (c : ℚ) {H N : Multiset ℚ} (h : PolygonLe H N) :
    PolygonLe (reflectSlopes c H) (reflectSlopes c N) := by
  refine ⟨by simp [reflectSlopes, h.1], ?_, ?_⟩
  · intro k hk
    have hkH : k ≤ H.card := by simpa [reflectSlopes] using hk
    have hkN : k ≤ N.card := h.1 ▸ hkH
    rw [polygon_reflect c H hkH, polygon_reflect c N hkN, h.1, h.2.2]
    have hle := h.2.1 (N.card - k) (by rw [h.1]; exact Nat.sub_le N.card k)
    linarith
  · rw [reflectSlopes_sum, reflectSlopes_sum, h.1, h.2.2]

theorem reflectSlopes_involutive (c : ℚ) (S : Multiset ℚ) :
    reflectSlopes c (reflectSlopes c S) = S := by
  unfold reflectSlopes
  rw [Multiset.map_map]
  simp

/-- Polarization reflection `w ↦ c - w` is an exact equivalence on `PolygonLe`. -/
theorem reflect_iff (c : ℚ) (H N : Multiset ℚ) :
    PolygonLe (reflectSlopes c H) (reflectSlopes c N) ↔ PolygonLe H N := by
  constructor
  · intro h
    have h' := reflect c h
    rwa [reflectSlopes_involutive, reflectSlopes_involutive] at h'
  · exact reflect c

end PolygonLe

/-! ## 3. Filtered `φ`-Modules, Determinant Weight Sum & Fontaine Weak Admissibility -/

universe u

/-- A finite-dimensional filtered `φ`-module over a field `K`: a finite-dimensional
`K`-vector space equipped with a Hodge filtration `fil`, a rational Newton slope multiset
`newton` of cardinality `finrank K V`, and restricted Newton slopes on `φ`-stable subspaces. -/
structure FilteredPhiMod (K : Type u) [Field K] where
  V : Type u
  [addCommGroup : AddCommGroup V]
  [module : Module K V]
  [finite : Module.Finite K V]
  fil : HodgeFiltration K V
  newton : Multiset ℚ
  newton_card : newton.card = Module.finrank K V
  IsPhiStable : Submodule K V → Prop
  subNewton : ∀ U : Submodule K V, IsPhiStable U → Multiset ℚ
  subNewton_card : ∀ U hU, (subNewton U hU).card = Module.finrank K U
  top_phiStable : IsPhiStable ⊤
  subNewton_top : subNewton ⊤ top_phiStable = newton
  bot_phiStable : IsPhiStable ⊥
  subNewton_bot : subNewton ⊥ bot_phiStable = 0

attribute [instance] FilteredPhiMod.addCommGroup FilteredPhiMod.module FilteredPhiMod.finite

namespace FilteredPhiMod

variable {K : Type u} [Field K]

/-- Total Hodge number `t_H(M) = ∑_{w ∈ weights M} w ∈ ℤ`. -/
def tH (M : FilteredPhiMod K) : ℤ := M.fil.tH

/-- Total Newton slope sum `t_N(M) = ∑_{s ∈ newton M} s ∈ ℚ`. -/
def tN (M : FilteredPhiMod K) : ℚ := M.newton.sum

/-- Hodge weights embedded in `ℚ` for direct Newton-vs-Hodge polygon comparison. -/
def hodgeSlopes (M : FilteredPhiMod K) : Multiset ℚ :=
  M.fil.weights.map (fun w : ℤ => (w : ℚ))

theorem hodgeSlopes_card (M : FilteredPhiMod K) :
    M.hodgeSlopes.card = Module.finrank K M.V := by
  simp [hodgeSlopes, M.fil.weights_card]

theorem hodgeSlopes_sum (M : FilteredPhiMod K) :
    M.hodgeSlopes.sum = (M.tH : ℚ) := by
  unfold hodgeSlopes tH HodgeFiltration.tH
  generalize M.fil.weights = s
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.sum_cons, Int.cast_add, ih]

/-- **Fontaine Weak Admissibility**:
`t_N(M) = t_H(M)` and for every `φ`-stable subspace `U ≤ M`, `t_H(U) ≤ t_N(U)`. -/
def IsWeaklyAdmissible (M : FilteredPhiMod K) : Prop :=
  M.tN = (M.tH : ℚ) ∧
    ∀ (U : Submodule K M.V) (hU : M.IsPhiStable U),
      ((M.fil.inducedSub U).tH : ℚ) ≤ (M.subNewton U hU).sum

/-- **Determinant (Top Exterior Power) Rank-1 Filtered `φ`-Module `det(M)`**:
carries the single Hodge weight `t_H(M) = ∑ w` and single Newton slope `t_N(M) = ∑ s`. -/
def det (M : FilteredPhiMod K) : FilteredPhiMod K where
  V := K
  fil := HodgeFiltration.singleJump K M.tH
  newton := {M.tN}
  newton_card := by simp [Module.finrank_self]
  IsPhiStable _ := True
  subNewton U _ := if U = ⊥ then 0 else {M.tN}
  subNewton_card U _ := by
    by_cases hU : U = ⊥
    · subst hU
      simp [finrank_bot]
    · have hle : Module.finrank K U ≤ 1 := by
        simpa [Module.finrank_self] using Submodule.finrank_le U
      have hne : Module.finrank K U ≠ 0 := by
        intro h0
        exact hU ((Submodule.finrank_eq_zero).mp h0)
      have h1 : Module.finrank K U = 1 := by omega
      simp [hU, h1]
  top_phiStable := trivial
  subNewton_top := by
    have hne : (⊤ : Submodule K K) ≠ ⊥ := top_ne_bot
    simp [hne]
  bot_phiStable := trivial
  subNewton_bot := by simp

/-- **Determinant Hodge Weight Sum**: `det(M).tH = M.fil.weights.sum = M.tH`. -/
theorem det_tH (M : FilteredPhiMod K) : M.det.tH = M.fil.weights.sum :=
  HodgeFiltration.singleJump_tH K M.tH

/-- **Determinant Newton Slope Sum**: `det(M).tN = M.newton.sum = M.tN`. -/
theorem det_tN (M : FilteredPhiMod K) : M.det.tN = M.newton.sum := by
  simp [det, tN]

/-- Weak admissibility descends to the determinant `det(M)` (and is in fact equivalent to
`t_N(M) = t_H(M)` on `det(M)`). -/
theorem det_isWeaklyAdmissible_iff (M : FilteredPhiMod K) :
    M.det.IsWeaklyAdmissible ↔ M.tN = (M.tH : ℚ) := by
  constructor
  · intro h
    have h1 := h.1
    rw [M.det_tN, M.det_tH] at h1
    exact h1
  · intro hEq
    refine ⟨by rw [M.det_tN, M.det_tH]; exact hEq, ?_⟩
    intro U _
    by_cases hU : U = ⊥
    · subst hU
      change (((HodgeFiltration.singleJump K M.tH).inducedSub ⊥).tH : ℚ) ≤
        (if (⊥ : Submodule K K) = ⊥ then (0 : Multiset ℚ) else {M.tN}).sum
      rw [HodgeFiltration.inducedSub_bot_tH]
      simp
    · have hle : Module.finrank K U ≤ Module.finrank K K := Submodule.finrank_le U
      have hne : Module.finrank K U ≠ 0 := fun h0 => hU (Submodule.finrank_eq_zero.mp h0)
      have hfin : Module.finrank K U = Module.finrank K K := by
        rw [Module.finrank_self] at hle ⊢
        omega
      have htop : U = ⊤ := Submodule.eq_top_of_finrank_eq hfin
      subst htop
      change (((HodgeFiltration.singleJump K M.tH).inducedSub ⊤).tH : ℚ) ≤
        (if (⊤ : Submodule K K) = ⊥ then (0 : Multiset ℚ) else {M.tN}).sum
      rw [if_neg top_ne_bot, HodgeFiltration.inducedSub_top_tH, HodgeFiltration.singleJump_tH,
        Multiset.sum_singleton, hEq]

theorem isWeaklyAdmissible_det {M : FilteredPhiMod K} (hM : M.IsWeaklyAdmissible) :
    M.det.IsWeaklyAdmissible :=
  (M.det_isWeaklyAdmissible_iff).mpr hM.1

/-- **Tate Twist `M.twist r`** shifting Hodge filtration by `r : ℤ` and Newton slopes by `r : ℚ`. -/
def twist (M : FilteredPhiMod K) (r : ℤ) : FilteredPhiMod K where
  V := M.V
  fil := M.fil.shift r
  newton := M.newton.map (fun s => s + (r : ℚ))
  newton_card := by simp [M.newton_card]
  IsPhiStable := M.IsPhiStable
  subNewton U hU := (M.subNewton U hU).map (fun s => s + (r : ℚ))
  subNewton_card U hU := by simp [M.subNewton_card U hU]
  top_phiStable := M.top_phiStable
  subNewton_top := by simp [M.subNewton_top]
  bot_phiStable := M.bot_phiStable
  subNewton_bot := by simp [M.subNewton_bot]

private theorem multiset_sum_add_const_rat (s : Multiset ℚ) (c : ℚ) :
    (s.map (fun x => x + c)).sum = s.sum + (s.card : ℚ) * c := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Nat.cast_add,
      Nat.cast_one]
    linarith

theorem twist_tH (M : FilteredPhiMod K) (r : ℤ) :
    (M.twist r).tH = M.tH + (Module.finrank K M.V : ℤ) * r :=
  M.fil.shift_tH r

theorem twist_tN (M : FilteredPhiMod K) (r : ℤ) :
    (M.twist r).tN = M.tN + (Module.finrank K M.V : ℚ) * (r : ℚ) := by
  unfold twist tN
  dsimp
  rw [multiset_sum_add_const_rat, M.newton_card]

/-- Tate twists preserve weak admissibility. -/
theorem isWeaklyAdmissible_twist {M : FilteredPhiMod K} (hM : M.IsWeaklyAdmissible) (r : ℤ) :
    (M.twist r).IsWeaklyAdmissible := by
  refine ⟨?_, ?_⟩
  · rw [M.twist_tN r, M.twist_tH r, hM.1]
    push_cast
    ring
  · intro (U : Submodule K M.V) hU
    change (((M.fil.shift r).inducedSub U).tH : ℚ) ≤ ((M.subNewton U hU).map (· + (r : ℚ))).sum
    have htH_shift :
        ((M.fil.shift r).inducedSub U).tH =
          (M.fil.inducedSub U).tH + (Module.finrank K U : ℤ) * r :=
      (M.fil.inducedSub U).shift_tH r
    rw [htH_shift, multiset_sum_add_const_rat, M.subNewton_card U hU]
    have hU_ad := hM.2 U hU
    push_cast
    linarith

/-- **Fontaine Strictness Theorem for Weakly Admissible Subobjects**:
if `M₁` and `M₂` are weakly admissible and `f : M₁.V →ₗ[K] M₂.V` is an injective filtered
`φ`-morphism (`M₁.fil i ≤ (M₂.fil i).comap f`, `range f` is `φ`-stable with Newton slopes
`M₁.newton`), then `f` is automatically **strict**: `M₁.fil i = (M₂.fil i).comap f` for all `i`. -/
theorem strict_of_weaklyAdmissible {M₁ M₂ : FilteredPhiMod K}
    (h₁ : M₁.IsWeaklyAdmissible) (h₂ : M₂.IsWeaklyAdmissible)
    (f : M₁.V →ₗ[K] M₂.V) (hf : Function.Injective f)
    (hfil : ∀ i : ℤ, M₁.fil.fil i ≤ (M₂.fil.fil i).comap f)
    (hstab : M₂.IsPhiStable (LinearMap.range f))
    (hnewt : M₂.subNewton (LinearMap.range f) hstab = M₁.newton) :
    ∀ i : ℤ, M₁.fil.fil i = (M₂.fil.fil i).comap f := by
  have hle_tH : M₁.fil.tH ≤ (M₂.fil.comapInj f hf).tH :=
    HodgeFiltration.tH_le_of_fil_le hfil
  have hge_tH : ((M₂.fil.comapInj f hf).tH : ℚ) ≤ (M₁.fil.tH : ℚ) := by
    rw [M₂.fil.comapInj_tH_eq_inducedSub_range f hf]
    calc ((M₂.fil.inducedSub (LinearMap.range f)).tH : ℚ)
        ≤ (M₂.subNewton (LinearMap.range f) hstab).sum := h₂.2 (LinearMap.range f) hstab
      _ = M₁.tN := by rw [hnewt]; rfl
      _ = (M₁.fil.tH : ℚ) := h₁.1
  have hge_int : (M₂.fil.comapInj f hf).tH ≤ M₁.fil.tH := by
    exact_mod_cast hge_tH
  exact HodgeFiltration.fil_eq_of_le_of_tH_eq hfil (le_antisymm hle_tH hge_int)

end FilteredPhiMod

/-- A short exact sequence `0 → M₁ →[f] M₂ →[g] M₃ → 0` of filtered `φ`-modules with strict
filtrations and additive Newton slope multisets on `φ`-stable submodules. -/
structure FilteredPhiSES {K : Type u} [Field K] (M₁ M₂ M₃ : FilteredPhiMod K) where
  ses : StrictFilteredSES K M₁.fil M₂.fil M₃.fil
  newton_add : M₂.newton = M₁.newton + M₃.newton
  comap_phiStable : ∀ U : Submodule K M₂.V, M₂.IsPhiStable U → M₁.IsPhiStable (U.comap ses.f)
  map_phiStable : ∀ U : Submodule K M₂.V, M₂.IsPhiStable U → M₃.IsPhiStable (U.map ses.g)
  subNewton_add : ∀ (U : Submodule K M₂.V) (hU : M₂.IsPhiStable U),
    M₂.subNewton U hU =
      M₁.subNewton (U.comap ses.f) (comap_phiStable U hU) +
        M₃.subNewton (U.map ses.g) (map_phiStable U hU)
  push_left_phiStable : ∀ U₁ : Submodule K M₁.V, M₁.IsPhiStable U₁ → M₂.IsPhiStable (U₁.map ses.f)
  pull_right_phiStable : ∀ U₃ : Submodule K M₃.V, M₃.IsPhiStable U₃ → M₂.IsPhiStable (U₃.comap ses.g)

namespace FilteredPhiSES

variable {K : Type u} [Field K] {M₁ M₂ M₃ : FilteredPhiMod K}

/-- Exact Hodge–Tate weight multiset additivity on a `FilteredPhiSES`. -/
theorem weights_add (E : FilteredPhiSES M₁ M₂ M₃) :
    M₂.fil.weights = M₁.fil.weights + M₃.fil.weights :=
  E.ses.weights_add

/-- Exact additivity of Hodge numbers `t_H` on a `FilteredPhiSES`. -/
theorem tH_add (E : FilteredPhiSES M₁ M₂ M₃) :
    M₂.tH = M₁.tH + M₃.tH :=
  E.ses.tH_add

/-- Exact additivity of Newton slope sums `t_N` on a `FilteredPhiSES`. -/
theorem tN_add (E : FilteredPhiSES M₁ M₂ M₃) :
    M₂.tN = M₁.tN + M₃.tN := by
  unfold FilteredPhiMod.tN
  rw [E.newton_add, Multiset.sum_add]

/-- Exact additivity of determinant Hodge weights `det(M₂).tH = det(M₁).tH + det(M₃).tH`. -/
theorem det_tH_add (E : FilteredPhiSES M₁ M₂ M₃) :
    M₂.det.tH = M₁.det.tH + M₃.det.tH := by
  rw [M₂.det_tH, M₁.det_tH, M₃.det_tH]
  exact E.tH_add

/-- Exact additivity of determinant Newton slopes `det(M₂).tN = det(M₁).tN + det(M₃).tN`. -/
theorem det_tN_add (E : FilteredPhiSES M₁ M₂ M₃) :
    M₂.det.tN = M₁.det.tN + M₃.det.tN := by
  rw [M₂.det_tN, M₁.det_tN, M₃.det_tN]
  exact E.tN_add

/-- Exact additivity of Hodge slope multisets `M₂.hodgeSlopes = M₁.hodgeSlopes + M₃.hodgeSlopes`. -/
theorem hodgeSlopes_add (E : FilteredPhiSES M₁ M₂ M₃) :
    M₂.hodgeSlopes = M₁.hodgeSlopes + M₃.hodgeSlopes := by
  unfold FilteredPhiMod.hodgeSlopes
  rw [E.weights_add, Multiset.map_add]

/-- Exact endpoint additivity of both the Newton and Hodge polygons on a `FilteredPhiSES`. -/
theorem polygon_endpoints_add (E : FilteredPhiSES M₁ M₂ M₃) :
    polygon M₂.newton M₂.newton.card =
        polygon M₁.newton M₁.newton.card + polygon M₃.newton M₃.newton.card ∧
      polygon M₂.hodgeSlopes M₂.hodgeSlopes.card =
        polygon M₁.hodgeSlopes M₁.hodgeSlopes.card + polygon M₃.hodgeSlopes M₃.hodgeSlopes.card := by
  rw [E.newton_add, E.hodgeSlopes_add]
  exact ⟨polygon_add_endpoint M₁.newton M₃.newton, polygon_add_endpoint M₁.hodgeSlopes M₃.hodgeSlopes⟩

/-- Hodge-below-Newton polygon dominance is preserved on extensions in a `FilteredPhiSES`. -/
theorem polygonLe_mid (E : FilteredPhiSES M₁ M₂ M₃)
    (h₁ : PolygonLe M₁.hodgeSlopes M₁.newton) (h₃ : PolygonLe M₃.hodgeSlopes M₃.newton) :
    PolygonLe M₂.hodgeSlopes M₂.newton := by
  rw [E.hodgeSlopes_add, E.newton_add]
  exact PolygonLe.add h₁ h₃

/-- **Fontaine's Extension Theorem**: if `M₁` and `M₃` are weakly admissible in a
`FilteredPhiSES M₁ M₂ M₃`, then the middle extension `M₂` is weakly admissible. -/
theorem isWeaklyAdmissible_mid (E : FilteredPhiSES M₁ M₂ M₃)
    (h₁ : M₁.IsWeaklyAdmissible) (h₃ : M₃.IsWeaklyAdmissible) :
    M₂.IsWeaklyAdmissible := by
  refine ⟨?_, ?_⟩
  · rw [E.tN_add, E.tH_add, h₁.1, h₃.1]
    push_cast
    ring
  · intro U hU
    set U₁ : Submodule K M₁.V := U.comap E.ses.f
    set U₃ : Submodule K M₃.V := U.map E.ses.g
    let fU : U₁ →ₗ[K] U :=
      { toFun := fun x => ⟨E.ses.f x.1, x.2⟩
        map_add' := fun x y => Subtype.ext (map_add E.ses.f x.1 y.1)
        map_smul' := fun c x => Subtype.ext (map_smul E.ses.f c x.1) }
    let gU : U →ₗ[K] U₃ :=
      { toFun := fun y => ⟨E.ses.g y.1, ⟨y.1, y.2, rfl⟩⟩
        map_add' := fun x y => Subtype.ext (map_add E.ses.g x.1 y.1)
        map_smul' := fun c x => Subtype.ext (map_smul E.ses.g c x.1) }
    have hfU_inj : Function.Injective fU := fun x y hxy =>
      Subtype.ext (E.ses.f_inj (congrArg Subtype.val hxy))
    have hgU_surj : Function.Surjective gU := by
      rintro ⟨w, ⟨v, hv, rfl⟩⟩
      exact ⟨⟨v, hv⟩, rfl⟩
    have hexactU : LinearMap.range fU = LinearMap.ker gU := by
      ext ⟨v, hv⟩
      constructor
      · rintro ⟨⟨u, hu⟩, hEq⟩
        have hfv : E.ses.f u = v := congrArg Subtype.val hEq
        change gU ⟨v, hv⟩ = 0
        apply Subtype.ext
        change E.ses.g v = 0
        have : v ∈ LinearMap.ker E.ses.g := by
          rw [← E.ses.exact]
          exact ⟨u, hfv⟩
        exact this
      · intro hker
        have hgv : E.ses.g v = 0 := congrArg Subtype.val hker
        have hv_range : v ∈ LinearMap.range E.ses.f := by
          rw [E.ses.exact]
          exact hgv
        obtain ⟨u, hu⟩ := hv_range
        have huU : u ∈ U₁ := by
          show E.ses.f u ∈ U
          rwa [hu]
        exact ⟨⟨u, huU⟩, Subtype.ext hu⟩
    let Fquot : HodgeFiltration K U₃ := (M₂.fil.inducedSub U).mapSurj gU hgU_surj
    let sesU : StrictFilteredSES K (M₁.fil.inducedSub U₁) (M₂.fil.inducedSub U) Fquot :=
      { f := fU
        g := gU
        f_inj := hfU_inj
        g_surj := hgU_surj
        exact := hexactU
        strict_sub := fun i => by
          ext ⟨u, hu⟩
          simp [HodgeFiltration.inducedSub, E.ses.strict_sub i, fU]
        strict_quot := fun _ => rfl }
    have htH_eq : (M₂.fil.inducedSub U).tH = (M₁.fil.inducedSub U₁).tH + Fquot.tH :=
      sesU.tH_add
    have hquot_le : ∀ i : ℤ, Fquot.fil i ≤ (M₃.fil.inducedSub U₃).fil i := by
      intro i w hw
      rcases hw with ⟨⟨v, hvU⟩, hvfil, rfl⟩
      show E.ses.g v ∈ M₃.fil.fil i
      rw [E.ses.strict_quot i]
      exact ⟨v, hvfil, rfl⟩
    have htH_quot_le : Fquot.tH ≤ (M₃.fil.inducedSub U₃).tH :=
      HodgeFiltration.tH_le_of_fil_le hquot_le
    have hN_eq :
        (M₂.subNewton U hU).sum =
          (M₁.subNewton U₁ (E.comap_phiStable U hU)).sum +
            (M₃.subNewton U₃ (E.map_phiStable U hU)).sum := by
      rw [E.subNewton_add U hU, Multiset.sum_add]
    have h1U := h₁.2 U₁ (E.comap_phiStable U hU)
    have h3U := h₃.2 U₃ (E.map_phiStable U hU)
    have htH_le_rat :
        ((M₂.fil.inducedSub U).tH : ℚ) ≤
          ((M₁.fil.inducedSub U₁).tH : ℚ) + ((M₃.fil.inducedSub U₃).tH : ℚ) := by
      rw [htH_eq]
      push_cast
      have hq : (Fquot.tH : ℚ) ≤ ((M₃.fil.inducedSub U₃).tH : ℚ) := by exact_mod_cast htH_quot_le
      linarith
    linarith

/-- **Subobject Admissibility Criterion**: if `M₂` is weakly admissible in a `FilteredPhiSES`
and `M₁.tN = M₁.tH`, then the subobject `M₁` is weakly admissible. -/
theorem isWeaklyAdmissible_left (E : FilteredPhiSES M₁ M₂ M₃)
    (h₂ : M₂.IsWeaklyAdmissible) (hEq₁ : M₁.tN = (M₁.tH : ℚ)) :
    M₁.IsWeaklyAdmissible := by
  refine ⟨hEq₁, ?_⟩
  intro U₁ hU₁
  set U : Submodule K M₂.V := U₁.map E.ses.f
  have hU : M₂.IsPhiStable U := E.push_left_phiStable U₁ hU₁
  have hcomap : U.comap E.ses.f = U₁ := Submodule.comap_map_eq_of_injective E.ses.f_inj U₁
  have hmap_bot : U.map E.ses.g = ⊥ := by
    ext w
    simp only [Submodule.mem_map, Submodule.mem_bot]
    constructor
    · rintro ⟨v, ⟨u, _, rfl⟩, rfl⟩
      have hv : E.ses.f u ∈ LinearMap.ker E.ses.g := by
        rw [← E.ses.exact]
        exact ⟨u, rfl⟩
      exact LinearMap.mem_ker.mp hv
    · rintro rfl
      exact ⟨0, U.zero_mem, map_zero E.ses.g⟩
  let fR : U₁ →ₗ[K] M₂.V := E.ses.f.domRestrict U₁
  have hfR_inj : Function.Injective fR := fun x y hxy =>
    Subtype.ext (E.ses.f_inj hxy)
  have hrange_fR : LinearMap.range fR = U := by
    ext v
    constructor
    · rintro ⟨⟨u, hu⟩, rfl⟩; exact ⟨u, hu, rfl⟩
    · rintro ⟨u, hu, rfl⟩; exact ⟨⟨u, hu⟩, rfl⟩
  have hfil_eq : ∀ i : ℤ, (M₁.fil.inducedSub U₁).fil i = (M₂.fil.comapInj fR hfR_inj).fil i := by
    intro i
    ext ⟨u, hu⟩
    simp [HodgeFiltration.inducedSub, HodgeFiltration.comapInj, E.ses.strict_sub i, fR]
  have htH_eq : (M₁.fil.inducedSub U₁).tH = (M₂.fil.inducedSub U).tH := by
    have h1 : (M₁.fil.inducedSub U₁).tH ≤ (M₂.fil.comapInj fR hfR_inj).tH :=
      HodgeFiltration.tH_le_of_fil_le fun i => le_of_eq (hfil_eq i)
    have h2 : (M₂.fil.comapInj fR hfR_inj).tH ≤ (M₁.fil.inducedSub U₁).tH :=
      HodgeFiltration.tH_le_of_fil_le fun i => le_of_eq (hfil_eq i).symm
    rw [le_antisymm h1 h2, M₂.fil.comapInj_tH_eq_inducedSub_range fR hfR_inj, hrange_fR]
  have hN_eq : M₂.subNewton U hU = M₁.subNewton U₁ hU₁ := by
    rw [E.subNewton_add U hU]
    have h1 : M₁.subNewton (U.comap E.ses.f) (E.comap_phiStable U hU) = M₁.subNewton U₁ hU₁ := by
      congr 1
    have h3 : M₃.subNewton (U.map E.ses.g) (E.map_phiStable U hU) = 0 := by
      rw [← M₃.subNewton_bot]
      congr 1
    rw [h1, h3, add_zero]
  rw [htH_eq, ← hN_eq]
  exact h₂.2 U hU

/-- **Quotient Admissibility Criterion**: if `M₂` is weakly admissible in a `FilteredPhiSES`
and `M₁.tN = M₁.tH`, then the quotient `M₃` is weakly admissible. -/
theorem isWeaklyAdmissible_right (E : FilteredPhiSES M₁ M₂ M₃)
    (h₂ : M₂.IsWeaklyAdmissible) (hEq₁ : M₁.tN = (M₁.tH : ℚ)) :
    M₃.IsWeaklyAdmissible := by
  have hEq₃ : M₃.tN = (M₃.tH : ℚ) := by
    have h2eq := h₂.1
    rw [E.tN_add, E.tH_add] at h2eq
    push_cast at h2eq
    linarith
  refine ⟨hEq₃, ?_⟩
  intro U₃ hU₃
  set U : Submodule K M₂.V := U₃.comap E.ses.g
  have hU : M₂.IsPhiStable U := E.pull_right_phiStable U₃ hU₃
  have hcomap_top : U.comap E.ses.f = ⊤ := by
    ext u
    simp only [U, Submodule.mem_comap, Submodule.mem_top, iff_true]
    have hker : E.ses.f u ∈ LinearMap.ker E.ses.g := by
      rw [← E.ses.exact]
      exact ⟨u, rfl⟩
    rw [LinearMap.mem_ker.mp hker]
    exact U₃.zero_mem
  have hmap_eq : U.map E.ses.g = U₃ := Submodule.map_comap_eq_of_surjective E.ses.g_surj U₃
  let fU : M₁.V →ₗ[K] U :=
    { toFun := fun u => ⟨E.ses.f u, by
        show E.ses.g (E.ses.f u) ∈ U₃
        have hker : E.ses.f u ∈ LinearMap.ker E.ses.g := by
          rw [← E.ses.exact]; exact ⟨u, rfl⟩
        rw [LinearMap.mem_ker.mp hker]; exact U₃.zero_mem⟩
      map_add' := fun x y => Subtype.ext (map_add E.ses.f x y)
      map_smul' := fun c x => Subtype.ext (map_smul E.ses.f c x) }
  let gU : U →ₗ[K] U₃ :=
    { toFun := fun y => ⟨E.ses.g y.1, y.2⟩
      map_add' := fun x y => Subtype.ext (map_add E.ses.g x.1 y.1)
      map_smul' := fun c x => Subtype.ext (map_smul E.ses.g c x.1) }
  have hfU_inj : Function.Injective fU := fun x y hxy =>
    E.ses.f_inj (congrArg Subtype.val hxy)
  have hgU_surj : Function.Surjective gU := by
    rintro ⟨w, hw⟩
    obtain ⟨v, rfl⟩ := E.ses.g_surj w
    exact ⟨⟨v, hw⟩, rfl⟩
  have hexactU : LinearMap.range fU = LinearMap.ker gU := by
    ext ⟨v, hv⟩
    constructor
    · rintro ⟨u, hEq⟩
      have hfv : E.ses.f u = v := congrArg Subtype.val hEq
      change gU ⟨v, hv⟩ = 0
      apply Subtype.ext
      change E.ses.g v = 0
      have : v ∈ LinearMap.ker E.ses.g := by
        rw [← E.ses.exact]; exact ⟨u, hfv⟩
      exact this
    · intro hker
      have hgv : E.ses.g v = 0 := congrArg Subtype.val hker
      have hv_range : v ∈ LinearMap.range E.ses.f := by
        rw [E.ses.exact]; exact hgv
      obtain ⟨u, hu⟩ := hv_range
      exact ⟨u, Subtype.ext hu⟩
  let sesU : StrictFilteredSES K M₁.fil (M₂.fil.inducedSub U) (M₃.fil.inducedSub U₃) :=
    { f := fU
      g := gU
      f_inj := hfU_inj
      g_surj := hgU_surj
      exact := hexactU
      strict_sub := fun i => by
        ext u
        simp [HodgeFiltration.inducedSub, E.ses.strict_sub i, fU]
      strict_quot := fun i => by
        ext ⟨w, hw⟩
        constructor
        · intro hwfil
          change w ∈ M₃.fil.fil i at hwfil
          rw [E.ses.strict_quot i] at hwfil
          rcases hwfil with ⟨v, hvfil, rfl⟩
          exact ⟨⟨v, hw⟩, hvfil, rfl⟩
        · rintro ⟨⟨v, _⟩, hvfil, hEq⟩
          have hgv : E.ses.g v = w := congrArg Subtype.val hEq
          change w ∈ M₃.fil.fil i
          rw [E.ses.strict_quot i]
          exact ⟨v, hvfil, hgv⟩ }
  have htH_U : (M₂.fil.inducedSub U).tH = M₁.tH + (M₃.fil.inducedSub U₃).tH := sesU.tH_add
  have hN_U : (M₂.subNewton U hU).sum = M₁.tN + (M₃.subNewton U₃ hU₃).sum := by
    rw [E.subNewton_add U hU, Multiset.sum_add]
    have h1 : M₁.subNewton (U.comap E.ses.f) (E.comap_phiStable U hU) = M₁.newton := by
      rw [← M₁.subNewton_top]
      congr 1
    have h3 : M₃.subNewton (U.map E.ses.g) (E.map_phiStable U hU) = M₃.subNewton U₃ hU₃ := by
      congr 1
    rw [h1, h3]
    rfl
  have hU_ad := h₂.2 U hU
  rw [htH_U, hN_U] at hU_ad
  push_cast at hU_ad
  linarith

end FilteredPhiSES

/-! ## 4. Polarization Reflection `w ↦ c - w`, Fontaine–Laffaille & Regular-Algebraic Separation -/

/-- Polarization reflection on an integer Hodge–Tate weight multiset: `w ↦ c - w`. -/
def reflectWeights (c : ℤ) (W : Multiset ℤ) : Multiset ℤ :=
  W.map (fun w => c - w)

theorem reflectWeights_card (c : ℤ) (W : Multiset ℤ) :
    (reflectWeights c W).card = W.card :=
  Multiset.card_map _ _

theorem reflectWeights_involutive (c : ℤ) (W : Multiset ℤ) :
    reflectWeights c (reflectWeights c W) = W := by
  unfold reflectWeights
  rw [Multiset.map_map]
  simp

theorem reflectWeights_sum (c : ℤ) (W : Multiset ℤ) :
    (reflectWeights c W).sum + W.sum = (W.card : ℤ) * c := by
  induction W using Multiset.induction_on with
  | empty => simp [reflectWeights]
  | cons a s ih =>
    simp only [reflectWeights, Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons,
      Nat.cast_add, Nat.cast_one] at ih ⊢
    linarith

theorem reflectWeights_shift (c s : ℤ) (W : Multiset ℤ) :
    reflectWeights (c - 2 * s) (W.map (fun w => w - s)) =
      (reflectWeights c W).map (fun w => w - s) := by
  unfold reflectWeights
  rw [Multiset.map_map, Multiset.map_map]
  exact Multiset.map_congr rfl fun w _ => by dsimp; ring

theorem reflectWeights_map_cast_rat (c : ℤ) (W : Multiset ℤ) :
    (reflectWeights c W).map (fun w : ℤ => (w : ℚ)) =
      reflectSlopes (c : ℚ) (W.map (fun w : ℤ => (w : ℚ))) := by
  unfold reflectWeights reflectSlopes
  rw [Multiset.map_map, Multiset.map_map]
  exact Multiset.map_congr rfl fun w _ => by dsimp; push_cast; rfl

/-- **Fontaine–Laffaille / Sen Regularity** of a Hodge–Tate weight multiset:
all weights are pairwise distinct (`W.Nodup`, equivalently `∀ w, W.count w ≤ 1`). -/
def IsRegularWeights (W : Multiset ℤ) : Prop :=
  W.Nodup

theorem isRegularWeights_iff_count_le_one (W : Multiset ℤ) :
    IsRegularWeights W ↔ ∀ w : ℤ, W.count w ≤ 1 :=
  Multiset.nodup_iff_count_le_one

/-- For a Hodge filtration `F`, its Hodge–Tate weights are regular (distinct) iff every
graded piece `Gr^i V` has dimension `≤ 1`. -/
theorem isRegular_iff_jump_le_one {K : Type*} [Field K] {V : Type*}
    [AddCommGroup V] [Module K V] [Module.Finite K V] (F : HodgeFiltration K V) :
    IsRegularWeights F.weights ↔ ∀ i : ℤ, F.jump i ≤ 1 := by
  rw [isRegularWeights_iff_count_le_one]
  exact forall_congr' fun i => by rw [F.weights_count i]

theorem isRegularWeights_reflect_iff (c : ℤ) (W : Multiset ℤ) :
    IsRegularWeights (reflectWeights c W) ↔ IsRegularWeights W := by
  unfold IsRegularWeights reflectWeights
  have hinj : Function.Injective (fun w : ℤ => c - w) := fun a b hab => by dsimp at hab; omega
  exact Multiset.nodup_map_iff_of_injective hinj

theorem isRegularWeights_shift_iff (s : ℤ) (W : Multiset ℤ) :
    IsRegularWeights (W.map (fun w => w - s)) ↔ IsRegularWeights W := by
  unfold IsRegularWeights
  have hinj : Function.Injective (fun w : ℤ => w - s) := fun a b hab => by dsimp at hab; omega
  exact Multiset.nodup_map_iff_of_injective hinj

/-- Ascending sorted list of integer Hodge–Tate weights. -/
def sortedWeights (W : Multiset ℤ) : List ℤ :=
  W.sort (· ≤ ·)

theorem sortedWeights_length (W : Multiset ℤ) : (sortedWeights W).length = W.card :=
  Multiset.length_sort (· ≤ ·)

theorem sortedWeights_coe (W : Multiset ℤ) : ((sortedWeights W : List ℤ) : Multiset ℤ) = W :=
  Multiset.sort_eq W (· ≤ ·)

theorem sortedWeights_pairwise_le (W : Multiset ℤ) : (sortedWeights W).Pairwise (· ≤ ·) :=
  Multiset.pairwise_sort W (· ≤ ·)

/-- Regularity implies the ascending sorted list of weights is strictly increasing
(`Pairwise (· < ·)`). -/
theorem sortedWeights_pairwise_lt {W : Multiset ℤ} (hreg : IsRegularWeights W) :
    (sortedWeights W).Pairwise (· < ·) := by
  have hnodup : (sortedWeights W).Nodup := by
    rw [← Multiset.coe_nodup, sortedWeights_coe]
    exact hreg
  have hle := sortedWeights_pairwise_le W
  exact (hle.and hnodup).imp fun ⟨h1, h2⟩ => lt_of_le_of_ne h1 h2

private theorem list_pairwise_lt_add_le {L : List ℤ} (hlt : L.Pairwise (· < ·))
    {i j : ℕ} (hij : i ≤ j) (hj : j < L.length) :
    L[i]'(lt_of_le_of_lt hij hj) + ((j - i : ℕ) : ℤ) ≤ L[j] := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction d with
  | zero => simp
  | succ d ih =>
    have hj' : i + d < L.length := by omega
    have hprev := ih (by omega) hj'
    have hstep : L[i + d] < L[i + (d + 1)] :=
      List.pairwise_iff_getElem.mp hlt (i + d) (i + (d + 1)) hj' hj (by omega)
    have hsub1 : i + d - i = d := by omega
    have hsub2 : i + (d + 1) - i = d + 1 := by omega
    rw [hsub1] at hprev
    rw [hsub2]
    push_cast
    omega

/-- **Strict Integer Spacing of Regular Weights**: if `W` is regular, then for all
`i ≤ j < W.card`, `(sortedWeights W)[i] + (j - i) ≤ (sortedWeights W)[j]`. -/
theorem sortedWeights_add_le_of_regular {W : Multiset ℤ} (hreg : IsRegularWeights W)
    {i j : ℕ} (hij : i ≤ j) (hj : j < (sortedWeights W).length) :
    (sortedWeights W)[i]'(lt_of_le_of_lt hij hj) + ((j - i : ℕ) : ℤ) ≤ (sortedWeights W)[j] :=
  list_pairwise_lt_add_le (sortedWeights_pairwise_lt hreg) hij hj

/-- **Fontaine–Laffaille Spread Lower Bound** (for nonempty regular weight multisets):
if `W` is regular, `1 ≤ W.card`, and every `w ∈ W` lies in `[a, b]`, then
`(W.card : ℤ) ≤ b - a + 1` (equivalently `W.card - 1 ≤ b - a`). -/
theorem card_le_span_of_regular_nonempty {W : Multiset ℤ} (hreg : IsRegularWeights W)
    (hne : 1 ≤ W.card) {a b : ℤ} (hbounds : ∀ w ∈ W, a ≤ w ∧ w ≤ b) :
    (W.card : ℤ) ≤ b - a + 1 := by
  set L := sortedWeights W
  have hlen : L.length = W.card := sortedWeights_length W
  have hpos : 0 < L.length := by omega
  have hlast : L.length - 1 < L.length := by omega
  have hgap := sortedWeights_add_le_of_regular hreg (i := 0) (j := L.length - 1) (Nat.zero_le _) hlast
  have hmem0 : L[0]'hpos ∈ W := by
    rw [← sortedWeights_coe W]
    exact Multiset.mem_coe.mpr (List.getElem_mem hpos)
  have hmemLast : L[L.length - 1]'hlast ∈ W := by
    rw [← sortedWeights_coe W]
    exact Multiset.mem_coe.mpr (List.getElem_mem hlast)
  have ha : a ≤ L[0]'hpos := (hbounds _ hmem0).1
  have hb : L[L.length - 1]'hlast ≤ b := (hbounds _ hmemLast).2
  change L[0]'hpos + ((L.length - 1 - 0 : ℕ) : ℤ) ≤ L[L.length - 1]'hlast at hgap
  omega

/-- **Fontaine–Laffaille Range Theorem**: if `W` is a nonempty regular Hodge–Tate weight
multiset lying in a Fontaine–Laffaille window `[a, a + p - 2]` (width `< p - 1`), then
`W.card < p` (`W.card ≤ p - 1`). -/
theorem fontaine_laffaille_card_lt_prime {W : Multiset ℤ} (hreg : IsRegularWeights W)
    (hne : 1 ≤ W.card) {a : ℤ} {p : ℕ}
    (hwin : ∀ w ∈ W, a ≤ w ∧ w ≤ a + (p : ℤ) - 2) :
    W.card < p := by
  have hspan := card_le_span_of_regular_nonempty hreg hne hwin
  omega

/-- **Regular-Algebraic Infinitesimal Character (`RegularAlgebraic`)**:
regular algebraic integrality (`I.IsRegAlg`) together with Sen / Fontaine–Laffaille
distinct-weight regularity (`∀ τ, (I.infChar τ).Nodup`). -/
def RegularAlgebraic (I : CMInfCharDatum) : Prop :=
  I.IsRegAlg ∧ ∀ τ : I.Emb, (I.infChar τ).Nodup

/-- For any `CMInfCharDatum` matching integral Hodge–Tate weights `HT`, `RegularAlgebraic I`
holds iff `I.IsRegAlg` and every `HT τ` is regular (`IsRegularWeights (HT τ)`). -/
theorem regularAlgebraic_iff_HT_regular {I : CMInfCharDatum} {HT : I.Emb → Multiset ℤ}
    (hreg : I.IsRegAlg) (hw : I.MatchesWeights HT) :
    RegularAlgebraic I ↔ ∀ τ : I.Emb, IsRegularWeights (HT τ) := by
  unfold RegularAlgebraic IsRegularWeights
  refine ⟨fun h τ => ?_, fun h => ⟨hreg, fun τ => ?_⟩⟩
  · have hφ_inj : Function.Injective (fun z : ℂ => ((I.rank : ℂ) - 1) / 2 - z) :=
      fun a b hab => by linear_combination -hab
    have hnodup_map : ((HT τ).map (fun n : ℤ => (n : ℂ))).Nodup := by
      rw [hw τ]
      exact (Multiset.nodup_map_iff_of_injective hφ_inj).mpr (h.2 τ)
    exact (Multiset.nodup_map_iff_of_injective (Int.cast_injective (α := ℂ))).mp hnodup_map
  · have hφ_inj : Function.Injective (fun z : ℂ => ((I.rank : ℂ) - 1) / 2 - z) :=
      fun a b hab => by linear_combination -hab
    have hnodup_map : ((I.infChar τ).map (fun z : ℂ => ((I.rank : ℂ) - 1) / 2 - z)).Nodup := by
      rw [← hw τ]
      exact (Multiset.nodup_map_iff_of_injective (Int.cast_injective (α := ℂ))).mpr (h τ)
    exact (Multiset.nodup_map_iff_of_injective hφ_inj).mp hnodup_map

/-- **Regular-Algebraic Eigenvalue Separation**: if `I.IsRegAlg`, any two distinct
eigenvalues `z₁ ≠ z₂` in `I.infChar τ` have real parts separated by at least `1`. -/
theorem infChar_re_sep_of_isRegAlg {I : CMInfCharDatum} (hreg : I.IsRegAlg)
    {τ : I.Emb} {z₁ z₂ : ℂ} (h₁ : z₁ ∈ I.infChar τ) (h₂ : z₂ ∈ I.infChar τ) (hne : z₁ ≠ z₂) :
    (1 : ℝ) ≤ |z₁.re - z₂.re| := by
  obtain ⟨n₁, rfl⟩ := hreg τ z₁ h₁
  obtain ⟨n₂, rfl⟩ := hreg τ z₂ h₂
  have hn : n₁ ≠ n₂ := by
    intro h
    apply hne
    rw [h]
  have hre :
      (((I.rank : ℂ) - 1) / 2 + (n₁ : ℂ)).re - (((I.rank : ℂ) - 1) / 2 + (n₂ : ℂ)).re =
        ((n₁ - n₂ : ℤ) : ℝ) := by
    simp
  rw [hre]
  have hdiff : (1 : ℤ) ≤ |n₁ - n₂| := by
    rcases abs_cases (n₁ - n₂) with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have hcast : ((1 : ℤ) : ℝ) ≤ ((|n₁ - n₂| : ℤ) : ℝ) := Int.cast_le.mpr hdiff
  simpa [Int.cast_abs] using hcast

/-- Regular algebraicity is preserved under character-twist shifts `I.shift s`. -/
theorem regularAlgebraic_shift {I : CMInfCharDatum} (h : RegularAlgebraic I) (s : ℤ) :
    RegularAlgebraic (I.shift s) := by
  refine ⟨CMInfCharDatum.shift_isRegAlg h.1 s, fun τ => ?_⟩
  have hinj : Function.Injective (fun z : ℂ => z + (s : ℂ)) := fun a b hab => by
    linear_combination hab
  exact (Multiset.nodup_map_iff_of_injective hinj).mpr (h.2 τ)

/-! ## 5. Direct Construction of `CMInfCharDatum`, `GaloisRowProps.weights` & `weights_conj` -/

/-- A CM-indexed crystalline Hodge–Tate filtration family of rank `rank ≥ 1` and polarization
parity weight `wt : ℤ`: at each embedding `τ : Emb`, `fil τ` is a Hodge filtration on a
`rank`-dimensional `K`-vector space whose Hodge–Tate weight multiset satisfies exact
polarization reflection under `conjEmb`. -/
structure CrystallineWeightFamily (K : Type*) [Field K] where
  rank : ℕ
  rank_pos : 1 ≤ rank
  Emb : Type
  conjEmb : Emb → Emb
  conjEmb_involutive : Function.Involutive conjEmb
  V : Emb → Type*
  [addCommGroup : ∀ τ, AddCommGroup (V τ)]
  [module : ∀ τ, Module K (V τ)]
  [finite : ∀ τ, Module.Finite K (V τ)]
  dim_eq_rank : ∀ τ, Module.finrank K (V τ) = rank
  fil : ∀ τ, HodgeFiltration K (V τ)
  wt : ℤ
  pol_reflect : ∀ τ, (fil (conjEmb τ)).weights = reflectWeights wt (fil τ).weights

attribute [instance]
  CrystallineWeightFamily.addCommGroup
  CrystallineWeightFamily.module
  CrystallineWeightFamily.finite

namespace CrystallineWeightFamily

variable {K : Type*} [Field K]

/-- The Hodge–Tate weight function `Emb → Multiset ℤ` extracted from the filtration family. -/
def HT (F : CrystallineWeightFamily K) (τ : F.Emb) : Multiset ℤ :=
  (F.fil τ).weights

/-- Direct construction of a `RHDirect.CMInfCharDatum` from a crystalline filtration family:
`infChar τ = ((rank - 1)/2 - ·) '' (fil τ).weights`. -/
def toCMInfCharDatum (F : CrystallineWeightFamily K) : CMInfCharDatum where
  rank := F.rank
  rank_pos := F.rank_pos
  Emb := F.Emb
  conjEmb := F.conjEmb
  conjEmb_involutive := F.conjEmb_involutive
  infChar τ := (F.fil τ).weights.map (fun m : ℤ => ((F.rank : ℂ) - 1) / 2 - (m : ℂ))

theorem HT_card (F : CrystallineWeightFamily K) (τ : F.Emb) :
    (F.HT τ).card = F.rank := by
  rw [HT, (F.fil τ).weights_card, F.dim_eq_rank τ]

theorem infChar_card (F : CrystallineWeightFamily K) (τ : F.Emb) :
    (F.toCMInfCharDatum.infChar τ).card = F.rank := by
  simp [toCMInfCharDatum, (F.fil τ).weights_card, F.dim_eq_rank τ]

/-- Every `CrystallineWeightFamily` produces a regular-algebraic integral `CMInfCharDatum`. -/
theorem toCMInfCharDatum_isRegAlg (F : CrystallineWeightFamily K) :
    F.toCMInfCharDatum.IsRegAlg := by
  intro τ z hz
  dsimp [toCMInfCharDatum] at hz ⊢
  obtain ⟨m, _, rfl⟩ := Multiset.mem_map.mp hz
  refine ⟨-m, ?_⟩
  push_cast
  ring

/-- The crystalline filtration weights match `F.toCMInfCharDatum` (`MatchesWeights`). -/
theorem toCMInfCharDatum_matchesWeights (F : CrystallineWeightFamily K) :
    F.toCMInfCharDatum.MatchesWeights F.HT := by
  intro τ
  simp only [toCMInfCharDatum, HT, Multiset.map_map, Function.comp_def]
  exact Multiset.map_congr rfl fun m _ => by ring

/-- The crystalline filtration weights satisfy `HasConjWeights F.wt` (`weights_conj`). -/
theorem toCMInfCharDatum_hasConjWeights (F : CrystallineWeightFamily K) :
    F.toCMInfCharDatum.HasConjWeights F.wt F.HT :=
  F.pol_reflect

/-- Every `CrystallineWeightFamily` produces a polarized `CMInfCharDatum` of parity weight `F.wt`. -/
theorem toCMInfCharDatum_isPolarized (F : CrystallineWeightFamily K) :
    F.toCMInfCharDatum.IsPolarized F.wt :=
  CMInfCharDatum.polarized_of_weights_conj
    F.toCMInfCharDatum_matchesWeights
    F.toCMInfCharDatum_hasConjWeights

/-- Determinant Hodge-number symmetry across conjugate embeddings:
`t_H(fil (c τ)) + t_H(fil τ) = rank * wt`. -/
theorem det_tH_conj (F : CrystallineWeightFamily K) (τ : F.Emb) :
    (F.fil (F.conjEmb τ)).tH + (F.fil τ).tH = (F.rank : ℤ) * F.wt := by
  have h := CMInfCharDatum.HT_sum_conj F.toCMInfCharDatum_hasConjWeights τ
  rw [F.HT_card τ] at h
  exact h

/-- If every crystalline filtration step has jump `≤ 1`, then the constructed `CMInfCharDatum`
is `RegularAlgebraic` (both integral and pairwise distinct). -/
theorem toCMInfCharDatum_regularAlgebraic (F : CrystallineWeightFamily K)
    (hjump : ∀ (τ : F.Emb) (i : ℤ), (F.fil τ).jump i ≤ 1) :
    RegularAlgebraic F.toCMInfCharDatum :=
  (regularAlgebraic_iff_HT_regular F.toCMInfCharDatum_isRegAlg
    F.toCMInfCharDatum_matchesWeights).mpr fun (τ : F.Emb) =>
    (isRegular_iff_jump_le_one (F.fil τ)).mpr (hjump τ)

/-- **Direct Construction of `GaloisRowProps` from a Crystalline Weight Family**:
given a `PolarizedCuspDatum D` whose infinitesimal characters arise from a
`CrystallineWeightFamily F` via a conjugation-equivariant embedding bijection
`e : D.Emb ≃ F.Emb`, any continuous semisimple `r : D.GalRep` with local–global
compatibility `away` and `above` directly satisfies all 6 live fields of
`GaloisRowProps D r F.wt (fun τ => F.HT (e τ))` (discharging `weights` and
`weights_conj` directly from the crystalline filtrations!). -/
theorem galoisRowProps_of_crystallineFamily
    (F : CrystallineWeightFamily K)
    (D : PolarizedCuspDatum)
    (hrank : D.rank = F.rank)
    (e : D.Emb ≃ F.Emb)
    (hconj : ∀ τ : D.Emb, e (D.conjEmb τ) = F.conjEmb (e τ))
    (hinf : ∀ τ : D.Emb, D.infChar τ = F.toCMInfCharDatum.infChar (e τ))
    (r : D.GalRep)
    (hcont : D.IsContinuous r)
    (hss : D.IsSemisimple r)
    (haway : ∀ p : D.AwayPlace, AwayCompat (D.awayCmp p) (D.awayGalWD p r) (D.awayRecWD p))
    (habove : ∀ p : D.AbovePlace, AboveCompat D r (fun τ => F.HT (e τ)) p) :
    GaloisRowProps D r F.wt (fun τ => F.HT (e τ)) where
  cont := hcont
  ss := hss
  away := haway
  weights τ := by
    rw [hinf τ, hrank]
    exact F.toCMInfCharDatum_matchesWeights (e τ)
  weights_conj τ := by
    rw [hconj τ]
    exact F.toCMInfCharDatum_hasConjWeights (e τ)
  above := habove

end CrystallineWeightFamily

/-- **Direct `StructuredCuspDatum` Assembly from Crystalline Filtrations**:
if a `StructuredCuspDatum S` has its infinitesimal characters realized by a
`CrystallineWeightFamily F` via a conjugation-equivariant bijection `e : S.Emb ≃ F.Emb`,
then `S` automatically satisfies both `IsRegAlg` and `IsPolarized F.wt`, directly feeding
`StructuredCuspDatum.galoisRowProps_of_localGlobal` to produce all 6 fields of
`GaloisRowProps`! -/
theorem galoisRowProps_of_crystalline_localGlobal {K : Type*} [Field K]
    (S : StructuredCuspDatum)
    (F : CrystallineWeightFamily K)
    (hrank : S.rank = F.rank)
    (e : S.Emb ≃ F.Emb)
    (hconj : ∀ τ : S.Emb, e (S.conjEmb τ) = F.conjEmb (e τ))
    (hinf : ∀ τ : S.Emb, S.infChar τ = F.toCMInfCharDatum.infChar (e τ))
    (C : S.CoreAllAt)
    (H1 : S.ToralCompatAt)
    (H2 : S.PlaceClassCompatAt IsQpBigNat) :
    ∃ r : S.GalRep,
      GaloisRowProps S.toPolarizedCuspDatum r F.wt (fun τ => F.HT (e τ)) := by
  have hreg : S.toCMInfCharDatum.IsRegAlg := by
    intro τ z hz
    change z ∈ S.infChar τ at hz
    change ∃ n : ℤ, z = ((S.rank : ℂ) - 1) / 2 + (n : ℂ)
    rw [hinf τ] at hz
    rw [hrank]
    exact F.toCMInfCharDatum_isRegAlg (e τ) z hz
  have hpol : S.toCMInfCharDatum.IsPolarized F.wt := by
    intro τ
    change S.infChar (S.conjEmb τ) =
      (S.infChar τ).map (fun z : ℂ => ((S.rank : ℂ) - 1) - (F.wt : ℂ) - z)
    rw [hinf (S.conjEmb τ), hconj τ, hinf τ, hrank]
    exact F.toCMInfCharDatum_isPolarized (e τ)
  obtain ⟨r, HT', hprops⟩ :=
    StructuredCuspDatum.galoisRowProps_of_localGlobal hreg hpol C H1 H2
  have hmatchF : S.toCMInfCharDatum.MatchesWeights (fun τ => F.HT (e τ)) := by
    intro τ
    change ((F.HT (e τ)).map fun n : ℤ => (n : ℂ)) =
      (S.infChar τ).map fun z : ℂ => ((S.rank : ℂ) - 1) / 2 - z
    rw [hinf τ, hrank]
    exact F.toCMInfCharDatum_matchesWeights (e τ)
  have hHT_eq : HT' = fun τ => F.HT (e τ) :=
    CMInfCharDatum.HT_unique (I := S.toCMInfCharDatum) hprops.weights hmatchF
  exact ⟨r, hHT_eq ▸ hprops⟩

/-- **Downstream Consequences of `GaloisRowProps` under Regular Algebraicity**:
any `GaloisRowProps D r wt HT` on a `RegularAlgebraic` `PolarizedCuspDatum` automatically
has pairwise distinct Hodge–Tate weights at every embedding, reflection symmetry under
`reflectWeights wt`, and determinant Hodge–Tate weight sum symmetry. -/
theorem galoisRowProps_regular_consequences
    {D : PolarizedCuspDatum} (hinv : Function.Involutive D.conjEmb)
    {r : D.GalRep} {wt : ℤ} {HT : D.Emb → Multiset ℤ}
    (h : GaloisRowProps D r wt HT)
    (hreg : RegularAlgebraic (D.toCMInfCharDatum hinv)) :
    (∀ τ : D.Emb, IsRegularWeights (HT τ)) ∧
    (∀ τ : D.Emb, HT (D.conjEmb τ) = reflectWeights wt (HT τ)) ∧
    (∀ τ : D.Emb, (HT (D.conjEmb τ)).sum + (HT τ).sum = ((HT τ).card : ℤ) * wt) := by
  refine ⟨?_, h.weights_conj, h.HT_sum_conj hinv⟩
  exact (regularAlgebraic_iff_HT_regular hreg.1 h.weights).mp hreg

end Stage2HodgeWeights
end RHDirect

end
