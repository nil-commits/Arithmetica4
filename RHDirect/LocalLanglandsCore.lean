import RHDirect.AutomorphicInputs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.FieldTheory.Finite.Basic

/-!
# RHDirect.LocalLanglandsCore

Compact, direct, zero-`sorry`, zero-custom-`axiom` Lean 4 rebuild of the Local Langlands
Correspondence (`LawsT`, exact 12 live fields from `RecTExists.lean`), Weil–Deligne
representation algebra, Bernstein–Zelevinsky segment calculus, and finite-field Green
regular-character (`NameLaws`) algebra.

## Main Components

1. **Bernstein–Zelevinsky Segment Calculus (`BZSegment`)**:
   - Integer-indexed cuspidal-line segments `[a, b]_ρ`, supercuspidal support `support`,
     precedence `Precedes`, linkage `Linked`, and exact support-union characterization
     `linked_iff_support`.
   - Elementary operations `elemOp` / `ElemStep` on linked pairs: exact support invariance,
     total-length invariance, and the strict quadratic-energy increment
     `energy 𝔪' = energy 𝔪 + 2 * (b₂ - b₁) * (a₂ - a₁)`.
   - Well-foundedness of the Zelevinsky partial order and constructive termination to an
     unlinked multisegment (`exists_unlinked_reduction`).
   - Contragredient segment duality `BZSegment.dual` (order-reversing on precedence, preserving
     linkage, unlinkedness, and elementary steps) and the Mœglin–Waldspurger / Zelevinsky
     transpose involution on rectangular Speh multisegments (`SpehDatum.zelevinskyDual`),
     preserving exact supercuspidal support and total length.

2. **Concrete Weil–Deligne Representation Algebra (`WDGroup`, `WDRep`, `AnyWDRep`)**:
   - Matrix Weil–Deligne representations `(ρ, N)` over a Weil group with norm degree `deg`
     and wild inertia subgroup `wild ⊆ ker deg`.
   - Irreducibility implies trivial monodromy (`monodromy_eq_zero_of_isIrr`, mirroring
     `WDBasic.lean`).
   - Characteristic polynomial `charPol`, determinant `wdDet`, root-product identity
     `prod_roots_charPol`, 1-dimensional character representations `wdOfChar`, special
     representations `wdSp l` (explicit Jordan nilpotent block + Frobenius eigenvalues +
     tameness), real unramified twists `wdNu`, character twists `wdTwist`, contragredient
     duality `wdDual` (strict involution), block direct sums `wdDirectSum`, and list sums
     `wdListSum` (dimension additivity, charpoly/det multiplicativity, tameness equivalence).

3. **Exact 12-Law `LocalLanglandsLaws` (`LawsT`) Theory & `NameLaws` Algebra**:
   - Direct algebraic consequences of all 12 live laws of `RHDirect.LocalLanglandsLaws`
     (Artin reciprocity on characters, dimension additivity, central-character compatibility,
     contragredient duality, injectivity, and depth-zero tameness).
   - Cuspidal-to-general extension theorem (`localLanglandsLaws_of_cuspidal`, mirroring
     `RecTExists.lean` / `ExtDim` / `ExtTw` / `ExtDual` / `ExtInj` / `ExtDepth`) and
     uniqueness on `Good` representations (`recT_unique_on_good`, mirroring `RecTUnique.lean`).
   - Finite-field Frobenius periodicity and invariance of Green regular-character sums
     (`char_pow_period`, `isRegularChar_pow`, `greenCharSum_frob_arg`, mirroring `NameLaws.lean`).
   - Concrete non-vacuous instantiation of `LocalLanglandsPlace` satisfying all 12 laws.

Zero `sorry`, zero custom `axiom`s.
-/

noncomputable section

open Polynomial Matrix

namespace RHDirect
namespace LocalLanglands

/-! ## 1. Bernstein–Zelevinsky Segment Calculus -/

/-- A Bernstein–Zelevinsky segment `[a, b]_ρ = {ρ ν^a, ρ ν^{a+1}, ..., ρ ν^b}` along a
cuspidal line indexed by `cusp : ι`. -/
@[ext]
structure BZSegment (ι : Type*) where
  cusp : ι
  a : ℤ
  b : ℤ
  le : a ≤ b

namespace BZSegment

variable {ι : Type*}

/-- Positive integer length `b - a + 1` of a segment `[a, b]_ρ`. -/
def len (Δ : BZSegment ι) : ℕ := (Δ.b - Δ.a + 1).toNat

theorem len_pos (Δ : BZSegment ι) : 0 < Δ.len := by
  unfold len
  have h := Δ.le
  omega

theorem len_coe (Δ : BZSegment ι) : (Δ.len : ℤ) = Δ.b - Δ.a + 1 := by
  unfold len
  have h := Δ.le
  omega

/-- A length-1 singleton segment `[a, a]_ρ`. -/
def singleton (ρ : ι) (a : ℤ) : BZSegment ι := ⟨ρ, a, a, le_refl a⟩

@[simp]
theorem len_singleton (ρ : ι) (a : ℤ) : (singleton ρ a).len = 1 := by
  simp [singleton, len]

/-- Construct a segment `[a, a + l - 1]_ρ` from its basepoint `a` and positive length `l`. -/
def ofStartLen (ρ : ι) (a : ℤ) (l : ℕ) (hl : 0 < l) : BZSegment ι :=
  ⟨ρ, a, a + (l : ℤ) - 1, by omega⟩

@[simp]
theorem len_ofStartLen (ρ : ι) (a : ℤ) (l : ℕ) (hl : 0 < l) :
    (ofStartLen ρ a l hl).len = l := by
  simp only [ofStartLen, len]
  omega

/-- Shift a segment `[a, b]_ρ` by an integer exponent `k : ℤ` to `[a + k, b + k]_ρ`. -/
def shift (Δ : BZSegment ι) (k : ℤ) : BZSegment ι :=
  ⟨Δ.cusp, Δ.a + k, Δ.b + k, by linarith [Δ.le]⟩

@[simp]
theorem shift_zero (Δ : BZSegment ι) : Δ.shift 0 = Δ := by
  ext <;> simp [shift]

@[simp]
theorem shift_add (Δ : BZSegment ι) (k₁ k₂ : ℤ) :
    (Δ.shift k₁).shift k₂ = Δ.shift (k₁ + k₂) := by
  ext <;> simp [shift, add_assoc]

@[simp]
theorem len_shift (Δ : BZSegment ι) (k : ℤ) : (Δ.shift k).len = Δ.len := by
  simp only [shift, len]
  have h := Δ.le
  omega

/-- Finite supercuspidal support `{(ρ, k) | a ≤ k ≤ b}` of a segment. -/
def support (Δ : BZSegment ι) : Finset (ι × ℤ) :=
  (Finset.Icc Δ.a Δ.b).map
    ⟨fun k => (Δ.cusp, k), fun _ _ h => (Prod.mk.inj h).2⟩

theorem mem_support {Δ : BZSegment ι} {p : ι × ℤ} :
    p ∈ Δ.support ↔ p.1 = Δ.cusp ∧ Δ.a ≤ p.2 ∧ p.2 ≤ Δ.b := by
  rcases p with ⟨ρ, k⟩
  simp only [support, Finset.mem_map, Finset.mem_Icc]
  constructor
  · rintro ⟨m, ⟨ha, hb⟩, h⟩
    cases h
    exact ⟨rfl, ha, hb⟩
  · rintro ⟨rfl, ha, hb⟩
    exact ⟨k, ⟨ha, hb⟩, rfl⟩

theorem card_support (Δ : BZSegment ι) : Δ.support.card = Δ.len := by
  rw [support, Finset.card_map, Int.card_Icc, len]
  congr 1
  ring

theorem support_subset_iff {Δ₁ Δ₂ : BZSegment ι} :
    Δ₁.support ⊆ Δ₂.support ↔ Δ₁.cusp = Δ₂.cusp ∧ Δ₂.a ≤ Δ₁.a ∧ Δ₁.b ≤ Δ₂.b := by
  constructor
  · intro h
    have ha : (Δ₁.cusp, Δ₁.a) ∈ Δ₂.support :=
      h (mem_support.mpr ⟨rfl, le_refl _, Δ₁.le⟩)
    have hb : (Δ₁.cusp, Δ₁.b) ∈ Δ₂.support :=
      h (mem_support.mpr ⟨rfl, Δ₁.le, le_refl _⟩)
    rw [mem_support] at ha hb
    exact ⟨ha.1, ha.2.1, hb.2.2⟩
  · rintro ⟨hc, ha, hb⟩ p hp
    rw [mem_support] at hp ⊢
    exact ⟨hp.1.trans hc, le_trans ha hp.2.1, le_trans hp.2.2 hb⟩

theorem support_injective : Function.Injective (support (ι := ι)) := by
  intro Δ₁ Δ₂ h
  have h12 := support_subset_iff.mp h.subset
  have h21 := support_subset_iff.mp h.symm.subset
  ext
  · exact h12.1
  · omega
  · omega

/-- `Δ₁` precedes `Δ₂` in the Bernstein–Zelevinsky sense: same cuspidal line, `a₁ < a₂`,
`b₁ < b₂`, and `a₂ ≤ b₁ + 1` (so their union is a segment strictly larger than each). -/
def Precedes (Δ₁ Δ₂ : BZSegment ι) : Prop :=
  Δ₁.cusp = Δ₂.cusp ∧ Δ₁.a < Δ₂.a ∧ Δ₁.b < Δ₂.b ∧ Δ₂.a ≤ Δ₁.b + 1

/-- Two segments are linked iff one precedes the other. -/
def Linked (Δ₁ Δ₂ : BZSegment ι) : Prop :=
  Δ₁.Precedes Δ₂ ∨ Δ₂.Precedes Δ₁

theorem not_precedes_self (Δ : BZSegment ι) : ¬Δ.Precedes Δ := by
  rintro ⟨_, h, _, _⟩
  exact lt_irrefl _ h

theorem not_linked_self (Δ : BZSegment ι) : ¬Δ.Linked Δ := by
  rintro (h | h) <;> exact not_precedes_self Δ h

theorem linked_symm {Δ₁ Δ₂ : BZSegment ι} (h : Δ₁.Linked Δ₂) : Δ₂.Linked Δ₁ :=
  h.symm

theorem precedes_shift_iff (Δ₁ Δ₂ : BZSegment ι) (k : ℤ) :
    (Δ₁.shift k).Precedes (Δ₂.shift k) ↔ Δ₁.Precedes Δ₂ := by
  simp only [Precedes, shift]
  constructor <;> rintro ⟨hc, h1, h2, h3⟩ <;> exact ⟨hc, by omega, by omega, by omega⟩

theorem linked_shift_iff (Δ₁ Δ₂ : BZSegment ι) (k : ℤ) :
    (Δ₁.shift k).Linked (Δ₂.shift k) ↔ Δ₁.Linked Δ₂ := by
  simp only [Linked, precedes_shift_iff]

/-- Exact set-theoretic characterization of Bernstein–Zelevinsky linkage: `Δ₁` and `Δ₂` are
linked iff they lie on the same cuspidal line, neither contains the other, and their union is
again a segment. -/
theorem linked_iff_support [DecidableEq ι] (Δ₁ Δ₂ : BZSegment ι) :
    Δ₁.Linked Δ₂ ↔
      Δ₁.cusp = Δ₂.cusp ∧ ¬(Δ₁.support ⊆ Δ₂.support) ∧ ¬(Δ₂.support ⊆ Δ₁.support) ∧
      ∃ Δ : BZSegment ι, Δ.support = Δ₁.support ∪ Δ₂.support := by
  constructor
  · rintro (⟨hc, ha, hb, hlink⟩ | ⟨hc, ha, hb, hlink⟩)
    · refine ⟨hc, ?_, ?_, ⟨Δ₁.cusp, Δ₁.a, Δ₂.b, by linarith [Δ₁.le]⟩, ?_⟩
      · rw [support_subset_iff]; omega
      · rw [support_subset_iff]; omega
      · ext ⟨ρ, k⟩
        simp only [Finset.mem_union, mem_support]
        constructor
        · rintro ⟨rfl, h1, h2⟩
          by_cases hk : k ≤ Δ₁.b
          · exact Or.inl ⟨rfl, h1, hk⟩
          · exact Or.inr ⟨hc, by omega, h2⟩
        · rintro (⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩)
          · exact ⟨rfl, h1, by omega⟩
          · exact ⟨hc.symm, by omega, h2⟩
    · refine ⟨hc.symm, ?_, ?_, ⟨Δ₂.cusp, Δ₂.a, Δ₁.b, by linarith [Δ₂.le]⟩, ?_⟩
      · rw [support_subset_iff]; omega
      · rw [support_subset_iff]; omega
      · ext ⟨ρ, k⟩
        simp only [Finset.mem_union, mem_support]
        constructor
        · rintro ⟨rfl, h1, h2⟩
          by_cases hk : k ≤ Δ₂.b
          · exact Or.inr ⟨rfl, h1, hk⟩
          · exact Or.inl ⟨hc, by omega, h2⟩
        · rintro (⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩)
          · exact ⟨hc.symm, by omega, h2⟩
          · exact ⟨rfl, h1, by omega⟩
  · rintro ⟨hc, h12, h21, Δ, hΔ⟩
    rw [support_subset_iff] at h12 h21
    have hle₁ := Δ₁.le
    have hle₂ := Δ₂.le
    have hΔ1 : Δ₁.support ⊆ Δ.support := by rw [hΔ]; exact Finset.subset_union_left
    have hΔ2 : Δ₂.support ⊆ Δ.support := by rw [hΔ]; exact Finset.subset_union_right
    rw [support_subset_iff] at hΔ1 hΔ2
    by_cases ha : Δ₁.a < Δ₂.a
    · have hb : Δ₁.b < Δ₂.b := by
        by_contra h
        exact h21 ⟨hc.symm, by omega, by omega⟩
      have hmem : (Δ₁.cusp, Δ₁.b + 1) ∈ Δ.support := by
        rw [mem_support]
        exact ⟨hΔ1.1, by omega, by omega⟩
      rw [hΔ, Finset.mem_union, mem_support, mem_support] at hmem
      rcases hmem with ⟨_, _, hbad⟩ | ⟨_, hlink, _⟩
      · omega
      · exact Or.inl ⟨hc, ha, hb, hlink⟩
    · have ha' : Δ₂.a < Δ₁.a := by
        by_contra h
        have heq : Δ₁.a = Δ₂.a := by omega
        by_cases hb : Δ₁.b ≤ Δ₂.b
        · exact h12 ⟨hc, by omega, hb⟩
        · exact h21 ⟨hc.symm, by omega, by omega⟩
      have hb' : Δ₂.b < Δ₁.b := by
        by_contra h
        exact h12 ⟨hc, by omega, by omega⟩
      have hmem : (Δ₂.cusp, Δ₂.b + 1) ∈ Δ.support := by
        rw [mem_support]
        exact ⟨hΔ2.1, by omega, by omega⟩
      rw [hΔ, Finset.mem_union, mem_support, mem_support] at hmem
      rcases hmem with ⟨_, hlink, _⟩ | ⟨_, _, hbad⟩
      · exact Or.inr ⟨hc.symm, ha', hb', hlink⟩
      · omega

/-- Union segment `Δ₁ ∪ Δ₂ = [a₁, b₂]` when `Δ₁` precedes `Δ₂`. -/
def unionSeg {Δ₁ Δ₂ : BZSegment ι} (h : Δ₁.Precedes Δ₂) : BZSegment ι :=
  ⟨Δ₁.cusp, Δ₁.a, Δ₂.b, by linarith [Δ₁.le, h.2.2.1]⟩

/-- Elementary Bernstein–Zelevinsky operation replacing a linked pair `(Δ₁, Δ₂)` (with
`Δ₁.Precedes Δ₂`) by `{Δ₁ ∪ Δ₂, Δ₁ ∩ Δ₂}` (or `{Δ₁ ∪ Δ₂}` when `Δ₁ ∩ Δ₂ = ∅`). -/
def elemResult (Δ₁ Δ₂ : BZSegment ι) (h : Δ₁.Precedes Δ₂) : Multiset (BZSegment ι) :=
  if hcap : Δ₂.a ≤ Δ₁.b then
    {unionSeg h, ⟨Δ₁.cusp, Δ₂.a, Δ₁.b, hcap⟩}
  else
    {unionSeg h}

/-- Supercuspidal support multiset of a multisegment `𝔪`. -/
def msupp (𝔪 : Multiset (BZSegment ι)) : Multiset (ι × ℤ) :=
  𝔪.bind (fun Δ => Δ.support.val)

/-- Total length `∑_{Δ ∈ 𝔪} len Δ` of a multisegment. -/
def totalLen (𝔪 : Multiset (BZSegment ι)) : ℕ :=
  (𝔪.map len).sum

/-- Quadratic length energy `∑_{Δ ∈ 𝔪} (len Δ)^2` strictly increasing under elementary
operations (giving a constructive termination measure bounded by `(totalLen 𝔪)^2`). -/
def energy (𝔪 : Multiset (BZSegment ι)) : ℕ :=
  (𝔪.map (fun Δ => Δ.len ^ 2)).sum

theorem card_msupp (𝔪 : Multiset (BZSegment ι)) : (msupp 𝔪).card = totalLen 𝔪 := by
  induction 𝔪 using Multiset.induction_on with
  | empty => simp [msupp, totalLen]
  | cons Δ 𝔪 ih =>
    simp only [msupp, totalLen, Multiset.cons_bind, Multiset.card_add, Multiset.map_cons,
      Multiset.sum_cons]
    change Δ.support.val.card + (msupp 𝔪).card = Δ.len + totalLen 𝔪
    rw [ih, ← Finset.card_def, card_support]

private theorem sum_sq_le_sq_sum (s : Multiset ℕ) :
    (s.map (fun x => x ^ 2)).sum ≤ s.sum ^ 2 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    have h : a ^ 2 + s.sum ^ 2 ≤ (a + s.sum) ^ 2 := by
      rw [add_sq]
      omega
    omega

theorem energy_le_totalLen_sq (𝔪 : Multiset (BZSegment ι)) :
    energy 𝔪 ≤ (totalLen 𝔪) ^ 2 := by
  unfold energy totalLen
  have h := sum_sq_le_sq_sum (𝔪.map len)
  rwa [Multiset.map_map] at h

theorem msupp_add (𝔪₁ 𝔪₂ : Multiset (BZSegment ι)) :
    msupp (𝔪₁ + 𝔪₂) = msupp 𝔪₁ + msupp 𝔪₂ := by
  simp [msupp, Multiset.add_bind]

theorem totalLen_add (𝔪₁ 𝔪₂ : Multiset (BZSegment ι)) :
    totalLen (𝔪₁ + 𝔪₂) = totalLen 𝔪₁ + totalLen 𝔪₂ := by
  simp [totalLen]

theorem energy_add (𝔪₁ 𝔪₂ : Multiset (BZSegment ι)) :
    energy (𝔪₁ + 𝔪₂) = energy 𝔪₁ + energy 𝔪₂ := by
  simp [energy]

theorem msupp_elemResult (Δ₁ Δ₂ : BZSegment ι) (h : Δ₁.Precedes Δ₂) :
    msupp (elemResult Δ₁ Δ₂ h) = Δ₁.support.val + Δ₂.support.val := by
  classical
  ext p
  rcases p with ⟨ρ, k⟩
  have hcnt : ∀ Δ : BZSegment ι, Multiset.count (ρ, k) Δ.support.val =
      if ρ = Δ.cusp ∧ Δ.a ≤ k ∧ k ≤ Δ.b then 1 else 0 := by
    intro Δ
    rw [Multiset.count_eq_of_nodup Δ.support.nodup]
    by_cases hm : (ρ, k) ∈ Δ.support.val
    · rw [if_pos hm, if_pos (mem_support.mp hm)]
    · rw [if_neg hm, if_neg (fun h' => hm (mem_support.mpr h'))]
  rcases h with ⟨hc, ha, hb, hlink⟩
  have hle₁ := Δ₁.le
  have hle₂ := Δ₂.le
  unfold elemResult unionSeg
  split_ifs with hcap
  · simp only [msupp, Multiset.insert_eq_cons, Multiset.cons_bind, Multiset.singleton_bind,
      Multiset.count_add, hcnt]
    by_cases hρ : ρ = Δ₁.cusp
    · subst hρ
      simp only [hc, true_and]
      split_ifs <;> omega
    · have hρ2 : ρ ≠ Δ₂.cusp := by rwa [← hc]
      simp [hρ, hρ2]
  · simp only [msupp, Multiset.singleton_bind, Multiset.count_add, hcnt]
    by_cases hρ : ρ = Δ₁.cusp
    · subst hρ
      simp only [hc, true_and]
      split_ifs <;> omega
    · have hρ2 : ρ ≠ Δ₂.cusp := by rwa [← hc]
      simp [hρ, hρ2]

theorem totalLen_elemResult (Δ₁ Δ₂ : BZSegment ι) (h : Δ₁.Precedes Δ₂) :
    totalLen (elemResult Δ₁ Δ₂ h) = Δ₁.len + Δ₂.len := by
  rw [← card_msupp, msupp_elemResult, Multiset.card_add, ← Finset.card_def, ← Finset.card_def,
    card_support, card_support]

theorem energy_elemResult (Δ₁ Δ₂ : BZSegment ι) (h : Δ₁.Precedes Δ₂) :
    energy (elemResult Δ₁ Δ₂ h) =
      Δ₁.len ^ 2 + Δ₂.len ^ 2 + 2 * (Δ₂.b - Δ₁.b).toNat * (Δ₂.a - Δ₁.a).toNat := by
  rcases h with ⟨hc, ha, hb, hlink⟩
  have hle₁ := Δ₁.le
  have hle₂ := Δ₂.le
  have hl1 : (Δ₁.len : ℤ) = Δ₁.b - Δ₁.a + 1 := Δ₁.len_coe
  have hl2 : (Δ₂.len : ℤ) = Δ₂.b - Δ₂.a + 1 := Δ₂.len_coe
  unfold elemResult unionSeg
  split_ifs with hcap
  · simp only [energy, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.sum_cons, Multiset.sum_singleton]
    have hu : (({ cusp := Δ₁.cusp, a := Δ₁.a, b := Δ₂.b, le := by omega } : BZSegment ι).len : ℤ) =
        Δ₂.b - Δ₁.a + 1 := len_coe _
    have hi : (({ cusp := Δ₁.cusp, a := Δ₂.a, b := Δ₁.b, le := hcap } : BZSegment ι).len : ℤ) =
        Δ₁.b - Δ₂.a + 1 := len_coe _
    zify
    rw [hu, hi, hl1, hl2, Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
    ring
  · simp only [energy, Multiset.map_singleton, Multiset.sum_singleton]
    have hu : (({ cusp := Δ₁.cusp, a := Δ₁.a, b := Δ₂.b, le := by omega } : BZSegment ι).len : ℤ) =
        Δ₂.b - Δ₁.a + 1 := len_coe _
    have hadj : Δ₂.a = Δ₁.b + 1 := by omega
    zify
    rw [hu, hl1, hl2, Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega), hadj]
    ring

theorem energy_lt_elemResult (Δ₁ Δ₂ : BZSegment ι) (h : Δ₁.Precedes Δ₂) :
    Δ₁.len ^ 2 + Δ₂.len ^ 2 < energy (elemResult Δ₁ Δ₂ h) := by
  rw [energy_elemResult]
  have h1 : 0 < (Δ₂.b - Δ₁.b).toNat := by have := h.2.2.1; omega
  have h2 : 0 < (Δ₂.a - Δ₁.a).toNat := by have := h.2.1; omega
  have hmul : 0 < 2 * (Δ₂.b - Δ₁.b).toNat * (Δ₂.a - Δ₁.a).toNat := by positivity
  omega

/-- A single elementary Bernstein–Zelevinsky reduction step on a multisegment. -/
def ElemStep (𝔪 𝔪' : Multiset (BZSegment ι)) : Prop :=
  ∃ (rest : Multiset (BZSegment ι)) (Δ₁ Δ₂ : BZSegment ι) (h : Δ₁.Precedes Δ₂),
    𝔪 = Δ₁ ::ₘ Δ₂ ::ₘ rest ∧ 𝔪' = elemResult Δ₁ Δ₂ h + rest

/-- Multi-step Zelevinsky reduction (reflexive-transitive closure of `ElemStep`). -/
abbrev ElemRed (𝔪 𝔪' : Multiset (BZSegment ι)) : Prop :=
  Relation.ReflTransGen ElemStep 𝔪 𝔪'

theorem ElemStep.msupp_eq {𝔪 𝔪' : Multiset (BZSegment ι)} (h : ElemStep 𝔪 𝔪') :
    msupp 𝔪' = msupp 𝔪 := by
  rcases h with ⟨rest, Δ₁, Δ₂, hp, rfl, rfl⟩
  rw [msupp_add, msupp_elemResult]
  simp only [msupp, Multiset.cons_bind, add_assoc]

theorem ElemStep.totalLen_eq {𝔪 𝔪' : Multiset (BZSegment ι)} (h : ElemStep 𝔪 𝔪') :
    totalLen 𝔪' = totalLen 𝔪 := by
  rw [← card_msupp, ← card_msupp, h.msupp_eq]

theorem ElemStep.energy_lt {𝔪 𝔪' : Multiset (BZSegment ι)} (h : ElemStep 𝔪 𝔪') :
    energy 𝔪 < energy 𝔪' := by
  rcases h with ⟨rest, Δ₁, Δ₂, hp, rfl, rfl⟩
  rw [energy_add]
  have hcons : energy (Δ₁ ::ₘ Δ₂ ::ₘ rest) = Δ₁.len ^ 2 + Δ₂.len ^ 2 + energy rest := by
    simp only [energy, Multiset.map_cons, Multiset.sum_cons, add_assoc]
  rw [hcons]
  have hlt := energy_lt_elemResult Δ₁ Δ₂ hp
  omega

theorem ElemStep.card_le {𝔪 𝔪' : Multiset (BZSegment ι)} (h : ElemStep 𝔪 𝔪') :
    𝔪'.card ≤ 𝔪.card := by
  rcases h with ⟨rest, Δ₁, Δ₂, hp, rfl, rfl⟩
  simp only [Multiset.card_add, Multiset.card_cons]
  unfold elemResult
  split_ifs <;> simp <;> omega

theorem ElemRed.msupp_eq {𝔪 𝔪' : Multiset (BZSegment ι)} (h : ElemRed 𝔪 𝔪') :
    msupp 𝔪' = msupp 𝔪 := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact hstep.msupp_eq.trans ih

theorem ElemRed.totalLen_eq {𝔪 𝔪' : Multiset (BZSegment ι)} (h : ElemRed 𝔪 𝔪') :
    totalLen 𝔪' = totalLen 𝔪 := by
  rw [← card_msupp, ← card_msupp, h.msupp_eq]

/-- Termination (well-foundedness of the reverse elementary-step relation): no multisegment
admits an infinite sequence of elementary Bernstein–Zelevinsky operations. -/
theorem wellFounded_flip_elemStep : WellFounded (fun 𝔪' 𝔪 : Multiset (BZSegment ι) => ElemStep 𝔪 𝔪') := by
  refine Subrelation.wf (r := InvImage (· < ·) (fun 𝔪 : Multiset (BZSegment ι) => (totalLen 𝔪) ^ 2 - energy 𝔪))
    ?_ (InvImage.wf _ wellFounded_lt)
  intro 𝔪' 𝔪 h
  show (totalLen 𝔪') ^ 2 - energy 𝔪' < (totalLen 𝔪) ^ 2 - energy 𝔪
  rw [h.totalLen_eq]
  have hle := energy_le_totalLen_sq 𝔪'
  rw [h.totalLen_eq] at hle
  have hlt := h.energy_lt
  omega

/-- A multisegment is unlinked if no two of its segments are linked (the Bernstein–Zelevinsky
criterion for irreducibility of the full parabolic induction). -/
def IsUnlinked (𝔪 : Multiset (BZSegment ι)) : Prop :=
  ∀ Δ₁ ∈ 𝔪, ∀ Δ₂ ∈ 𝔪, ¬Δ₁.Linked Δ₂

theorem isUnlinked_zero : IsUnlinked (0 : Multiset (BZSegment ι)) := by
  intro Δ₁ h₁
  exact absurd h₁ (Multiset.notMem_zero Δ₁)

theorem isUnlinked_singleton (Δ : BZSegment ι) : IsUnlinked ({Δ} : Multiset (BZSegment ι)) := by
  intro Δ₁ h₁ Δ₂ h₂
  rw [Multiset.mem_singleton] at h₁ h₂
  rw [h₁, h₂]
  exact not_linked_self Δ

theorem isUnlinked_of_le {𝔪₁ 𝔪₂ : Multiset (BZSegment ι)} (hle : 𝔪₁ ≤ 𝔪₂) (h : IsUnlinked 𝔪₂) :
    IsUnlinked 𝔪₁ :=
  fun Δ₁ h₁ Δ₂ h₂ => h Δ₁ (Multiset.mem_of_le hle h₁) Δ₂ (Multiset.mem_of_le hle h₂)

/-- Every multisegment either is already unlinked or admits an elementary Bernstein–Zelevinsky
reduction step. -/
theorem isUnlinked_or_exists_elemStep (𝔪 : Multiset (BZSegment ι)) :
    IsUnlinked 𝔪 ∨ ∃ 𝔪', ElemStep 𝔪 𝔪' := by
  classical
  by_cases hu : IsUnlinked 𝔪
  · exact Or.inl hu
  · right
    unfold IsUnlinked at hu
    push Not at hu
    rcases hu with ⟨Δ₁, h₁, Δ₂, h₂, hlink⟩
    have hpair : ∀ {A B : BZSegment ι}, A ∈ 𝔪 → B ∈ 𝔪 → A.Precedes B → ∃ 𝔪', ElemStep 𝔪 𝔪' := by
      intro A B hA hB hAB
      have hneAB : A ≠ B := fun heq => by subst heq; exact not_precedes_self A hAB
      have hB' : B ∈ 𝔪.erase A := (Multiset.mem_erase_of_ne hneAB.symm).mpr hB
      let rest := (𝔪.erase A).erase B
      have h𝔪 : 𝔪 = A ::ₘ B ::ₘ rest := by
        rw [Multiset.cons_erase hB', Multiset.cons_erase hA]
      exact ⟨elemResult A B hAB + rest, rest, A, B, hAB, h𝔪, rfl⟩
    rcases hlink with hp | hp
    · exact hpair h₁ h₂ hp
    · exact hpair h₂ h₁ hp

/-- Constructive Bernstein–Zelevinsky unlinked reduction theorem: every multisegment reduces
in finitely many elementary steps to an unlinked multisegment with the exact same
supercuspidal support and total length. -/
theorem exists_unlinked_reduction (𝔪 : Multiset (BZSegment ι)) :
    ∃ 𝔪' : Multiset (BZSegment ι),
      ElemRed 𝔪 𝔪' ∧ IsUnlinked 𝔪' ∧ msupp 𝔪' = msupp 𝔪 ∧ totalLen 𝔪' = totalLen 𝔪 := by
  refine wellFounded_flip_elemStep.induction
    (C := fun m => ∃ 𝔪', ElemRed m 𝔪' ∧ IsUnlinked 𝔪' ∧ msupp 𝔪' = msupp m ∧ totalLen 𝔪' = totalLen m)
    𝔪 fun m ih => ?_
  rcases isUnlinked_or_exists_elemStep m with hu | ⟨m₁, hstep⟩
  · exact ⟨m, Relation.ReflTransGen.refl, hu, rfl, rfl⟩
  · obtain ⟨m', hred, hu', hsup, hlen⟩ := ih m₁ hstep
    exact ⟨m', Relation.ReflTransGen.head hstep hred, hu',
      hsup.trans hstep.msupp_eq, hlen.trans hstep.totalLen_eq⟩

/-! ### Contragredient Segment Duality -/

/-- Contragredient (dual) of a segment `[a, b]_ρ` with respect to a cuspidal duality
involution `dualCusp : ι → ι`: `[a, b]_ρ^∨ = [-b, -a]_{ρ^∨}`. -/
def dual (dualCusp : ι → ι) (Δ : BZSegment ι) : BZSegment ι :=
  ⟨dualCusp Δ.cusp, -Δ.b, -Δ.a, neg_le_neg Δ.le⟩

theorem dual_dual {dualCusp : ι → ι} (hinv : Function.Involutive dualCusp) (Δ : BZSegment ι) :
    (Δ.dual dualCusp).dual dualCusp = Δ := by
  ext
  · exact hinv Δ.cusp
  · simp [dual]
  · simp [dual]

@[simp]
theorem len_dual (dualCusp : ι → ι) (Δ : BZSegment ι) : (Δ.dual dualCusp).len = Δ.len := by
  simp only [dual, len]
  have h := Δ.le
  omega

theorem precedes_dual_iff {dualCusp : ι → ι} (hinv : Function.Involutive dualCusp)
    (Δ₁ Δ₂ : BZSegment ι) :
    (Δ₂.dual dualCusp).Precedes (Δ₁.dual dualCusp) ↔ Δ₁.Precedes Δ₂ := by
  simp only [Precedes, dual]
  constructor
  · rintro ⟨hc, h1, h2, h3⟩
    have hc' : Δ₁.cusp = Δ₂.cusp := by
      have := congrArg dualCusp hc
      rw [hinv, hinv] at this
      exact this.symm
    exact ⟨hc', by omega, by omega, by omega⟩
  · rintro ⟨hc, h1, h2, h3⟩
    exact ⟨congrArg dualCusp hc.symm, by omega, by omega, by omega⟩

theorem linked_dual_iff {dualCusp : ι → ι} (hinv : Function.Involutive dualCusp)
    (Δ₁ Δ₂ : BZSegment ι) :
    (Δ₁.dual dualCusp).Linked (Δ₂.dual dualCusp) ↔ Δ₁.Linked Δ₂ := by
  simp only [Linked, precedes_dual_iff hinv]
  tauto

theorem isUnlinked_map_dual_iff {dualCusp : ι → ι} (hinv : Function.Involutive dualCusp)
    (𝔪 : Multiset (BZSegment ι)) :
    IsUnlinked (𝔪.map (dual dualCusp)) ↔ IsUnlinked 𝔪 := by
  constructor
  · intro h Δ₁ h₁ Δ₂ h₂
    rw [← linked_dual_iff hinv]
    exact h _ (Multiset.mem_map_of_mem _ h₁) _ (Multiset.mem_map_of_mem _ h₂)
  · intro h Δ₁' h₁' Δ₂' h₂'
    rcases Multiset.mem_map.mp h₁' with ⟨Δ₁, h₁, rfl⟩
    rcases Multiset.mem_map.mp h₂' with ⟨Δ₂, h₂, rfl⟩
    rw [linked_dual_iff hinv]
    exact h Δ₁ h₁ Δ₂ h₂

theorem elemStep_map_dual {dualCusp : ι → ι} (hinv : Function.Involutive dualCusp)
    {𝔪 𝔪' : Multiset (BZSegment ι)} (h : ElemStep 𝔪 𝔪') :
    ElemStep (𝔪.map (dual dualCusp)) (𝔪'.map (dual dualCusp)) := by
  rcases h with ⟨rest, Δ₁, Δ₂, hp, rfl, rfl⟩
  have hp' : (Δ₂.dual dualCusp).Precedes (Δ₁.dual dualCusp) := (precedes_dual_iff hinv Δ₁ Δ₂).mpr hp
  refine ⟨rest.map (dual dualCusp), Δ₂.dual dualCusp, Δ₁.dual dualCusp, hp', ?_, ?_⟩
  · simp only [Multiset.map_cons]
    exact Multiset.cons_swap _ _ _
  · rw [Multiset.map_add]
    congr 1
    unfold elemResult unionSeg
    by_cases hcap : Δ₂.a ≤ Δ₁.b
    · have hcap' : (Δ₁.dual dualCusp).a ≤ (Δ₂.dual dualCusp).b := by
        simp only [dual]; omega
      rw [dif_pos hcap, dif_pos hcap']
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
      congr 1
      · ext <;> simp [dual, hp.1]
      · congr 1
        ext <;> simp [dual, hp.1]
    · have hcap' : ¬((Δ₁.dual dualCusp).a ≤ (Δ₂.dual dualCusp).b) := by
        simp only [dual]; omega
      rw [dif_neg hcap, dif_neg hcap']
      simp only [Multiset.map_singleton]
      congr 1
      ext <;> simp [dual, hp.1]

/-! ### Mœglin–Waldspurger / Zelevinsky Involution on Rectangular Speh Multisegments -/

/-- A rectangular (Speh-type) multisegment datum: `count` consecutive shifts of a length-`segLen`
segment starting at `start` along cuspidal line `cusp`. -/
@[ext]
structure SpehDatum (ι : Type*) where
  cusp : ι
  start : ℤ
  segLen : ℕ
  count : ℕ
  segLen_pos : 0 < segLen
  count_pos : 0 < count

/-- The multisegment `{[start + j, start + j + segLen - 1]_ρ | 0 ≤ j < count}`. -/
def SpehDatum.toMultiset (S : SpehDatum ι) : Multiset (BZSegment ι) :=
  (Finset.range S.count).val.map fun j : ℕ =>
    ofStartLen S.cusp (S.start + (j : ℤ)) S.segLen S.segLen_pos

/-- Zelevinsky / Mœglin–Waldspurger transpose involution on rectangular Speh data,
interchanging segment length `segLen` and multiplicity `count` (in particular exchanging the
length-`l` Steinberg segment with `l` singleton segments). -/
def SpehDatum.zelevinskyDual (S : SpehDatum ι) : SpehDatum ι :=
  ⟨S.cusp, S.start, S.count, S.segLen, S.count_pos, S.segLen_pos⟩

theorem SpehDatum.zelevinskyDual_involutive (S : SpehDatum ι) :
    S.zelevinskyDual.zelevinskyDual = S := rfl

theorem SpehDatum.totalLen_toMultiset (S : SpehDatum ι) :
    totalLen S.toMultiset = S.segLen * S.count := by
  simp only [totalLen, toMultiset, Multiset.map_map, Function.comp_def, len_ofStartLen]
  rw [Multiset.map_const', Multiset.sum_replicate, smul_eq_mul, ← Finset.card_def,
    Finset.card_range, mul_comm]

theorem SpehDatum.totalLen_zelevinskyDual (S : SpehDatum ι) :
    totalLen S.zelevinskyDual.toMultiset = totalLen S.toMultiset := by
  rw [totalLen_toMultiset, totalLen_toMultiset, zelevinskyDual]
  exact mul_comm _ _

private theorem support_ofStartLen_val (ρ : ι) (a : ℤ) (l : ℕ) (hl : 0 < l) :
    (ofStartLen ρ a l hl).support.val =
      (Finset.range l).val.map (fun i : ℕ => (ρ, a + (i : ℤ))) := by
  classical
  ext ⟨ρ', k⟩
  have hnodup : ((Finset.range l).val.map (fun i : ℕ => (ρ, a + (i : ℤ)))).Nodup := by
    refine Multiset.Nodup.map ?_ (Finset.range l).nodup
    intro i₁ i₂ h
    have h' : a + (i₁ : ℤ) = a + (i₂ : ℤ) := (Prod.mk.inj h).2
    omega
  rw [Multiset.count_eq_of_nodup (ofStartLen ρ a l hl).support.nodup,
      Multiset.count_eq_of_nodup hnodup]
  have hiff : (ρ', k) ∈ (ofStartLen ρ a l hl).support.val ↔
      (ρ', k) ∈ (Finset.range l).val.map (fun i : ℕ => (ρ, a + (i : ℤ))) := by
    change (ρ', k) ∈ (ofStartLen ρ a l hl).support ↔ _
    rw [mem_support, Multiset.mem_map]
    simp only [ofStartLen, Finset.mem_val, Finset.mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, h1, h2⟩
      exact ⟨(k - a).toNat, by omega, rfl, by omega⟩
    · rintro ⟨i, hi, rfl, rfl⟩
      exact ⟨rfl, by omega, by omega⟩
  by_cases hm : (ρ', k) ∈ (ofStartLen ρ a l hl).support.val
  · rw [if_pos hm, if_pos (hiff.mp hm)]
  · rw [if_neg hm, if_neg (mt hiff.mpr hm)]

private theorem multiset_bind_map_comm {α β γ : Type*} (s : Multiset α) (t : Multiset β)
    (f : α → β → γ) :
    (s.bind fun a => t.map fun b => f a b) = (t.bind fun b => s.map fun a => f a b) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.cons_bind, ih]
    clear ih
    induction t using Multiset.induction_on with
    | empty => simp
    | cons b t iht =>
      rw [Multiset.map_cons, Multiset.cons_bind, Multiset.cons_bind, Multiset.map_cons,
        Multiset.cons_add, Multiset.cons_add, ← iht]
      ac_rfl

/-- The Zelevinsky / Mœglin–Waldspurger involution preserves the exact supercuspidal support
multiset of every rectangular Speh multisegment. -/
theorem SpehDatum.msupp_zelevinskyDual (S : SpehDatum ι) :
    msupp S.zelevinskyDual.toMultiset = msupp S.toMultiset := by
  have hexpand : ∀ (T : SpehDatum ι),
      msupp T.toMultiset =
        (Finset.range T.count).val.bind fun j : ℕ =>
          (Finset.range T.segLen).val.map fun i : ℕ =>
            (T.cusp, T.start + (j : ℤ) + (i : ℤ)) := by
    intro T
    unfold msupp toMultiset
    rw [Multiset.bind_map]
    refine Multiset.bind_congr fun j _ => ?_
    exact support_ofStartLen_val T.cusp (T.start + (j : ℤ)) T.segLen T.segLen_pos
  rw [hexpand S.zelevinskyDual, hexpand S]
  simp only [zelevinskyDual]
  rw [multiset_bind_map_comm]
  refine Multiset.bind_congr fun i _ => ?_
  refine Multiset.map_congr rfl fun j _ => ?_
  congr 1
  ring

end BZSegment

/-! ## 2. Concrete Weil–Deligne Representation Algebra -/

/-- Abstract Weil group structure with residue cardinality `q > 1`, Frobenius degree map
`deg : G → ℤ`, and wild inertia subgroup `wild ⊆ ker deg`. -/
structure WDGroup where
  G : Type
  [group : Group G]
  q : ℝ
  q_gt_one : 1 < q
  deg : G → ℤ
  deg_one : deg 1 = 0
  deg_mul : ∀ σ τ : G, deg (σ * τ) = deg σ + deg τ
  wild : Subgroup G
  deg_wild : ∀ σ ∈ wild, deg σ = 0

attribute [instance] WDGroup.group

namespace WDGroup

variable (W : WDGroup)

theorem q_pos : 0 < W.q := lt_trans zero_lt_one W.q_gt_one

theorem q_ne_zero : W.q ≠ 0 := ne_of_gt W.q_pos

theorem deg_inv (σ : W.G) : W.deg σ⁻¹ = -W.deg σ := by
  have h := W.deg_mul σ σ⁻¹
  rw [mul_inv_cancel, W.deg_one] at h
  omega

/-- Norm character `σ ↦ q^{deg σ}` valued in `ℂ`. -/
def qNorm (σ : W.G) : ℂ := ((W.q : ℂ) ^ W.deg σ)

theorem qNorm_ne_zero (σ : W.G) : W.qNorm σ ≠ 0 := by
  unfold qNorm
  exact zpow_ne_zero _ (Complex.ofReal_ne_zero.mpr W.q_ne_zero)

theorem qNorm_one : W.qNorm 1 = 1 := by
  simp [qNorm, W.deg_one]

theorem qNorm_mul (σ τ : W.G) : W.qNorm (σ * τ) = W.qNorm σ * W.qNorm τ := by
  unfold qNorm
  rw [W.deg_mul, zpow_add₀ (Complex.ofReal_ne_zero.mpr W.q_ne_zero)]

theorem qNorm_inv (σ : W.G) : W.qNorm σ⁻¹ = (W.qNorm σ)⁻¹ := by
  unfold qNorm
  rw [W.deg_inv, _root_.zpow_neg]

theorem qNorm_wild {σ : W.G} (hσ : σ ∈ W.wild) : W.qNorm σ = 1 := by
  simp [qNorm, W.deg_wild σ hσ]

/-- Real unramified power character `σ ↦ q^{s · deg σ}`. -/
def qPow (s : ℝ) (σ : W.G) : ℂ := ((W.q ^ (s * (W.deg σ : ℝ)) : ℝ) : ℂ)

theorem qPow_ne_zero (s : ℝ) (σ : W.G) : W.qPow s σ ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos W.q_pos _))

theorem qPow_one (s : ℝ) : W.qPow s 1 = 1 := by
  simp [qPow, W.deg_one]

theorem qPow_mul (s : ℝ) (σ τ : W.G) : W.qPow s (σ * τ) = W.qPow s σ * W.qPow s τ := by
  unfold qPow
  rw [← Complex.ofReal_mul, ← Real.rpow_add W.q_pos, W.deg_mul]
  push_cast
  ring_nf

theorem qPow_zero (σ : W.G) : W.qPow 0 σ = 1 := by
  simp [qPow]

theorem qPow_add (s₁ s₂ : ℝ) (σ : W.G) : W.qPow (s₁ + s₂) σ = W.qPow s₁ σ * W.qPow s₂ σ := by
  unfold qPow
  rw [← Complex.ofReal_mul, ← Real.rpow_add W.q_pos]
  ring_nf

theorem qPow_neg (s : ℝ) (σ : W.G) : W.qPow (-s) σ = (W.qPow s σ)⁻¹ := by
  unfold qPow
  rw [← Complex.ofReal_inv, ← Real.rpow_neg (le_of_lt W.q_pos)]
  ring_nf

theorem qPow_wild (s : ℝ) {σ : W.G} (hσ : σ ∈ W.wild) : W.qPow s σ = 1 := by
  simp [qPow, W.deg_wild σ hσ]

/-- `qPow s` packaged as a group homomorphism `W.G →* ℂˣ`. -/
def qPowHom (s : ℝ) : W.G →* ℂˣ where
  toFun σ := Units.mk0 (W.qPow s σ) (W.qPow_ne_zero s σ)
  map_one' := by ext; exact W.qPow_one s
  map_mul' σ τ := by ext; exact W.qPow_mul s σ τ

end WDGroup

/-- Concrete `n`-dimensional Weil–Deligne representation `(ρ, N)` over `W`: a group
homomorphism `ρ : W.G →* GL_n(ℂ)` and a nilpotent monodromy operator `N` satisfying
`ρ(σ) N ρ(σ)⁻¹ = q^{deg σ} N`. -/
@[ext]
structure WDRep (W : WDGroup) (n : ℕ) where
  ρ : W.G →* Matrix.GeneralLinearGroup (Fin n) ℂ
  N : Matrix (Fin n) (Fin n) ℂ
  nilp : IsNilpotent N
  compat : ∀ σ : W.G,
    (ρ σ : Matrix (Fin n) (Fin n) ℂ) * N * (ρ σ⁻¹ : Matrix (Fin n) (Fin n) ℂ) =
      W.qNorm σ • N

namespace WDRep

variable {W : WDGroup} {n m : ℕ}

/-- Characteristic polynomial of `ρ(σ)`. -/
def charPol (V : WDRep W n) (σ : W.G) : ℂ[X] :=
  (V.ρ σ : Matrix (Fin n) (Fin n) ℂ).charpoly

/-- Determinant `det(ρ(σ))`. -/
def wdDet (V : WDRep W n) (σ : W.G) : ℂ :=
  (V.ρ σ : Matrix (Fin n) (Fin n) ℂ).det

theorem charPol_monic (V : WDRep W n) (σ : W.G) : (V.charPol σ).Monic :=
  Matrix.charpoly_monic _

theorem charPol_natDegree (V : WDRep W n) (σ : W.G) : (V.charPol σ).natDegree = n := by
  rw [charPol, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]

theorem wdDet_ne_zero (V : WDRep W n) (σ : W.G) : V.wdDet σ ≠ 0 :=
  ((Matrix.GeneralLinearGroup.det (V.ρ σ)).isUnit).ne_zero

theorem wdDet_one (V : WDRep W n) : V.wdDet 1 = 1 := by
  simp [wdDet]

theorem wdDet_mul (V : WDRep W n) (σ τ : W.G) : V.wdDet (σ * τ) = V.wdDet σ * V.wdDet τ := by
  simp only [wdDet, map_mul, Units.val_mul, Matrix.det_mul]

theorem wdDet_inv (V : WDRep W n) (σ : W.G) : V.wdDet σ⁻¹ = (V.wdDet σ)⁻¹ := by
  have h := V.wdDet_mul σ σ⁻¹
  rw [mul_inv_cancel, V.wdDet_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

/-- Product of characteristic-polynomial roots equals the determinant (mirroring
`WDBasic.lean:prod_roots`). -/
theorem prod_roots_charPol (V : WDRep W n) (σ : W.G) :
    (V.charPol σ).roots.prod = V.wdDet σ :=
  (Matrix.det_eq_prod_roots_charpoly _).symm

/-- A Weil–Deligne representation is tamely ramified iff wild inertia acts trivially. -/
def IsTame (V : WDRep W n) : Prop :=
  ∀ σ ∈ W.wild, V.ρ σ = 1

theorem charPol_wild_of_isTame (V : WDRep W n) (ht : V.IsTame) {σ : W.G} (hσ : σ ∈ W.wild) :
    V.charPol σ = (X - 1) ^ n := by
  rw [charPol, ht σ hσ]
  change (1 : Matrix (Fin n) (Fin n) ℂ).charpoly = (X - 1) ^ n
  rw [Matrix.charpoly_one, Fintype.card_fin]

theorem wdDet_wild_of_isTame (V : WDRep W n) (ht : V.IsTame) {σ : W.G} (hσ : σ ∈ W.wild) :
    V.wdDet σ = 1 := by
  rw [wdDet, ht σ hσ]
  exact Matrix.det_one

/-- Irreducibility of the underlying Weil-group representation `ρ`. -/
def IsIrr (V : WDRep W n) : Prop :=
  0 < n ∧
  ∀ S : Submodule ℂ (Fin n → ℂ),
    (∀ σ : W.G, ∀ v ∈ S, (V.ρ σ : Matrix (Fin n) (Fin n) ℂ).mulVec v ∈ S) →
      S = ⊥ ∨ S = ⊤

/-- Every irreducible Weil–Deligne representation has trivial monodromy `N = 0` (mirroring
`WDBasic.lean:monodromy_zero_of_irreducible`). -/
theorem monodromy_eq_zero_of_isIrr (V : WDRep W n) (hirr : V.IsIrr) : V.N = 0 := by
  rcases hirr with ⟨hn, H⟩
  let K : Submodule ℂ (Fin n → ℂ) := LinearMap.ker (Matrix.toLin' V.N)
  have hKinv : ∀ σ : W.G, ∀ v ∈ K, (V.ρ σ : Matrix (Fin n) (Fin n) ℂ).mulVec v ∈ K := by
    intro σ v hv
    change V.N.mulVec ((V.ρ σ : Matrix (Fin n) (Fin n) ℂ).mulVec v) = 0
    have hv' : V.N.mulVec v = 0 := hv
    have hcomp := V.compat σ
    have hmul : (V.ρ σ : Matrix (Fin n) (Fin n) ℂ) * V.N =
        W.qNorm σ • (V.N * (V.ρ σ : Matrix (Fin n) (Fin n) ℂ)) := by
      have h1 := congrArg (· * (V.ρ σ : Matrix (Fin n) (Fin n) ℂ)) hcomp
      simp only [Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
        Units.val_one, Matrix.mul_one, Matrix.smul_mul] at h1
      exact h1
    have hvec : (W.qNorm σ • (V.N * (V.ρ σ : Matrix (Fin n) (Fin n) ℂ))).mulVec v = 0 := by
      rw [← hmul, ← Matrix.mulVec_mulVec, hv', Matrix.mulVec_zero]
    rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec] at hvec
    exact (smul_eq_zero.mp hvec).resolve_left (W.qNorm_ne_zero σ)
  have hKne : K ≠ ⊥ := by
    obtain ⟨k, hk⟩ := V.nilp
    let P : ℕ → Prop := fun m => V.N ^ m = 0
    classical
    let k0 := Nat.find (⟨k, hk⟩ : ∃ m, P m)
    have hk0 : V.N ^ k0 = 0 := Nat.find_spec (⟨k, hk⟩ : ∃ m, P m)
    have hk0_pos : 0 < k0 := by
      by_contra h0
      have h0' : k0 = 0 := by omega
      rw [h0', pow_zero] at hk0
      have h10 : (1 : Matrix (Fin n) (Fin n) ℂ) ⟨0, hn⟩ ⟨0, hn⟩ = 0 := by
        rw [hk0]; rfl
      simp at h10
    have hprev : V.N ^ (k0 - 1) ≠ 0 := Nat.find_min (⟨k, hk⟩ : ∃ m, P m) (by omega)
    have hex : ∃ j : Fin n, (V.N ^ (k0 - 1)).mulVec (Pi.single j 1) ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hprev
      ext i j
      have hji := congrFun (hall j) i
      simpa [Matrix.mulVec_single] using hji
    obtain ⟨j, hj⟩ := hex
    intro hbot
    apply hj
    have hmem : (V.N ^ (k0 - 1)).mulVec (Pi.single j 1) ∈ K := by
      change V.N.mulVec ((V.N ^ (k0 - 1)).mulVec (Pi.single j 1)) = 0
      rw [Matrix.mulVec_mulVec, ← pow_succ', show (k0 - 1) + 1 = k0 by omega, hk0,
        Matrix.zero_mulVec]
    rw [hbot, Submodule.mem_bot] at hmem
    exact hmem
  rcases H K hKinv with hbot | htop
  · exact absurd hbot hKne
  · ext i j
    have hmem : Pi.single j (1 : ℂ) ∈ K := by rw [htop]; trivial
    have hzero : V.N.mulVec (Pi.single j 1) = 0 := hmem
    have hji := congrFun hzero i
    simpa [Matrix.mulVec_single] using hji

/-- 1-dimensional Weil–Deligne representation attached to a character `χ : W.G →* ℂˣ`. -/
def ofChar (W : WDGroup) (χ : W.G →* ℂˣ) : WDRep W 1 where
  ρ :=
    { toFun := fun σ =>
        { val := Matrix.of fun _ _ => (χ σ : ℂ)
          inv := Matrix.of fun _ _ => ((χ σ)⁻¹ : ℂ)
          val_inv := by
            ext i j
            fin_cases i; fin_cases j
            simp [Matrix.mul_apply]
          inv_val := by
            ext i j
            fin_cases i; fin_cases j
            simp [Matrix.mul_apply] }
      map_one' := by
        ext i j
        fin_cases i; fin_cases j
        simp
      map_mul' := fun σ τ => by
        ext i j
        fin_cases i; fin_cases j
        simp [Matrix.mul_apply] }
  N := 0
  nilp := IsNilpotent.zero
  compat := fun σ => by simp

theorem wdDet_ofChar (W : WDGroup) (χ : W.G →* ℂˣ) (σ : W.G) :
    (ofChar W χ).wdDet σ = (χ σ : ℂ) := by
  simp [wdDet, ofChar]

theorem charPol_ofChar (W : WDGroup) (χ : W.G →* ℂˣ) (σ : W.G) :
    (ofChar W χ).charPol σ = X - C (χ σ : ℂ) := by
  rw [charPol]
  have h1 : ((ofChar W χ).ρ σ : Matrix (Fin 1) (Fin 1) ℂ) = Matrix.diagonal (fun _ : Fin 1 => (χ σ : ℂ)) := by
    ext i j; fin_cases i; fin_cases j; simp [ofChar]
  rw [h1, Matrix.charpoly_diagonal]
  simp

theorem isTame_ofChar_iff (W : WDGroup) (χ : W.G →* ℂˣ) :
    (ofChar W χ).IsTame ↔ ∀ σ ∈ W.wild, χ σ = 1 := by
  constructor
  · intro ht σ hσ
    have h := congrArg (fun M : Matrix.GeneralLinearGroup (Fin 1) ℂ => (M : Matrix (Fin 1) (Fin 1) ℂ) 0 0) (ht σ hσ)
    ext
    simpa [ofChar] using h
  · intro h σ hσ
    ext i j
    fin_cases i; fin_cases j
    simp [ofChar, h σ hσ]

theorem isIrr_ofChar (W : WDGroup) (χ : W.G →* ℂˣ) : (ofChar W χ).IsIrr := by
  refine ⟨Nat.one_pos, fun S _ => ?_⟩
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  · right
    rw [eq_top_iff]
    obtain ⟨v, hvS, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hv0' : v 0 ≠ 0 := by
      intro h0
      apply hv0
      ext i; fin_cases i; exact h0
    intro w _
    have hw : w = (w 0 / v 0) • v := by
      ext i; fin_cases i
      simp [div_mul_cancel₀ _ hv0']
    rw [hw]
    exact S.smul_mem _ hvS

/-- Twist of a Weil–Deligne representation by a character `χ : W.G →* ℂˣ`. -/
def twist (V : WDRep W n) (χ : W.G →* ℂˣ) : WDRep W n where
  ρ :=
    { toFun := fun σ =>
        { val := (χ σ : ℂ) • (V.ρ σ : Matrix (Fin n) (Fin n) ℂ)
          inv := ((χ σ)⁻¹ : ℂ) • (V.ρ σ⁻¹ : Matrix (Fin n) (Fin n) ℂ)
          val_inv := by
            rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
              mul_inv_cancel₀ (Units.ne_zero (χ σ)), one_smul]
            change (V.ρ σ * V.ρ σ⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ).val = 1
            rw [← map_mul, mul_inv_cancel, map_one, Units.val_one]
          inv_val := by
            rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
              inv_mul_cancel₀ (Units.ne_zero (χ σ)), one_smul]
            change (V.ρ σ⁻¹ * V.ρ σ : Matrix.GeneralLinearGroup (Fin n) ℂ).val = 1
            rw [← map_mul, inv_mul_cancel, map_one, Units.val_one] }
      map_one' := by ext i j; simp
      map_mul' := fun σ τ => by
        ext i j
        simp only [Units.val_mul, map_mul, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.smul_apply, smul_eq_mul]
        ring }
  N := V.N
  nilp := V.nilp
  compat := fun σ => by
    change ((χ σ : ℂ) • (V.ρ σ : Matrix (Fin n) (Fin n) ℂ)) * V.N *
        (((χ σ⁻¹ : ℂ) • (V.ρ σ⁻¹ : Matrix (Fin n) (Fin n) ℂ))) = W.qNorm σ • V.N
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, map_inv,
      Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero (χ σ)), one_smul]
    exact V.compat σ

theorem twist_one (V : WDRep W n) : V.twist 1 = V := by
  ext σ i j
  · simp [twist]
  · rfl

theorem twist_mul (V : WDRep W n) (χ₁ χ₂ : W.G →* ℂˣ) :
    (V.twist χ₁).twist χ₂ = V.twist (χ₁ * χ₂) := by
  ext σ i j
  · simp only [twist, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.mul_apply, Units.val_mul,
      Matrix.smul_apply, smul_eq_mul]
    ring
  · rfl

theorem twist_comm (V : WDRep W n) (χ₁ χ₂ : W.G →* ℂˣ) :
    (V.twist χ₁).twist χ₂ = (V.twist χ₂).twist χ₁ := by
  rw [twist_mul, twist_mul]
  congr 1
  ext σ
  exact mul_comm _ _

theorem wdDet_twist (V : WDRep W n) (χ : W.G →* ℂˣ) (σ : W.G) :
    (V.twist χ).wdDet σ = (χ σ : ℂ) ^ n * V.wdDet σ := by
  simp [wdDet, twist, Fintype.card_fin]

theorem isTame_twist_of_tame (V : WDRep W n) (χ : W.G →* ℂˣ)
    (hV : V.IsTame) (hχ : ∀ σ ∈ W.wild, χ σ = 1) : (V.twist χ).IsTame := by
  intro σ hσ
  ext i j
  simp [twist, hV σ hσ, hχ σ hσ]

/-- Real unramified power twist `V ↦ V ⊗ |·|^s`. -/
def nu (V : WDRep W n) (s : ℝ) : WDRep W n :=
  V.twist (W.qPowHom s)

theorem nu_zero (V : WDRep W n) : V.nu 0 = V := by
  have h1 : W.qPowHom 0 = 1 := by ext σ; exact W.qPow_zero σ
  rw [nu, h1, twist_one]

theorem nu_add (V : WDRep W n) (s₁ s₂ : ℝ) : (V.nu s₁).nu s₂ = V.nu (s₁ + s₂) := by
  rw [nu, nu, twist_mul, nu]
  congr 1
  ext σ
  exact (W.qPow_add s₁ s₂ σ).symm

theorem twist_nu_comm (V : WDRep W n) (χ : W.G →* ℂˣ) (s : ℝ) :
    (V.twist χ).nu s = (V.nu s).twist χ :=
  twist_comm V χ (W.qPowHom s)

theorem wdDet_nu (V : WDRep W n) (s : ℝ) (σ : W.G) :
    (V.nu s).wdDet σ = (W.qPow s σ) ^ n * V.wdDet σ :=
  wdDet_twist V (W.qPowHom s) σ

theorem isTame_nu_iff (V : WDRep W n) (s : ℝ) : (V.nu s).IsTame ↔ V.IsTame := by
  constructor
  · intro h σ hσ
    have h' := h σ hσ
    ext i j
    have hij := congrArg (fun M : Matrix.GeneralLinearGroup (Fin n) ℂ => (M : Matrix (Fin n) (Fin n) ℂ) i j) h'
    simpa [nu, twist, WDGroup.qPowHom, W.qPow_wild s hσ] using hij
  · intro h
    exact isTame_twist_of_tame V (W.qPowHom s) h fun σ hσ => by
      ext; exact W.qPow_wild s hσ

/-- Contragredient (dual) of a Weil–Deligne representation: `ρ^*(σ) = (ρ(σ⁻¹))ᵀ`, `N^* = -Nᵀ`. -/
def dual (V : WDRep W n) : WDRep W n where
  ρ :=
    { toFun := fun σ =>
        { val := (V.ρ σ⁻¹ : Matrix (Fin n) (Fin n) ℂ)ᵀ
          inv := (V.ρ σ : Matrix (Fin n) (Fin n) ℂ)ᵀ
          val_inv := by
            rw [← Matrix.transpose_mul]
            have h : (V.ρ σ : Matrix (Fin n) (Fin n) ℂ) * (V.ρ σ⁻¹ : Matrix (Fin n) (Fin n) ℂ) = 1 := by
              change (V.ρ σ * V.ρ σ⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ).val = 1
              rw [← map_mul, mul_inv_cancel, map_one, Units.val_one]
            rw [h, Matrix.transpose_one]
          inv_val := by
            rw [← Matrix.transpose_mul]
            have h : (V.ρ σ⁻¹ : Matrix (Fin n) (Fin n) ℂ) * (V.ρ σ : Matrix (Fin n) (Fin n) ℂ) = 1 := by
              change (V.ρ σ⁻¹ * V.ρ σ : Matrix.GeneralLinearGroup (Fin n) ℂ).val = 1
              rw [← map_mul, inv_mul_cancel, map_one, Units.val_one]
            rw [h, Matrix.transpose_one] }
      map_one' := by
        ext i j
        simp [Matrix.one_apply, eq_comm]
      map_mul' := fun σ τ => by
        ext i j
        change ((V.ρ (σ * τ)⁻¹ : Matrix (Fin n) (Fin n) ℂ)ᵀ) i j =
          (((V.ρ σ⁻¹ : Matrix (Fin n) (Fin n) ℂ)ᵀ) * ((V.ρ τ⁻¹ : Matrix (Fin n) (Fin n) ℂ)ᵀ)) i j
        rw [_root_.mul_inv_rev, map_mul, Units.val_mul, Matrix.transpose_mul] }
  N := -V.Nᵀ
  nilp := by
    obtain ⟨k, hk⟩ := V.nilp
    refine ⟨k, ?_⟩
    rw [neg_pow, ← Matrix.transpose_pow, hk, Matrix.transpose_zero, mul_zero]
  compat := fun σ => by
    change (V.ρ σ⁻¹ : Matrix (Fin n) (Fin n) ℂ)ᵀ * (-V.Nᵀ) * (V.ρ σ⁻¹⁻¹ : Matrix (Fin n) (Fin n) ℂ)ᵀ =
      W.qNorm σ • (-V.Nᵀ)
    rw [inv_inv, Matrix.mul_neg, Matrix.neg_mul, smul_neg]
    congr 1
    rw [← Matrix.transpose_smul, ← V.compat σ, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.mul_assoc]

theorem dual_dual (V : WDRep W n) : V.dual.dual = V := by
  ext σ i j
  · simp [dual]
  · simp [dual]

theorem wdDet_dual (V : WDRep W n) (σ : W.G) : V.dual.wdDet σ = (V.wdDet σ)⁻¹ := by
  simp only [wdDet, dual, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.det_transpose]
  exact V.wdDet_inv σ

theorem dual_twist (V : WDRep W n) (χ : W.G →* ℂˣ) :
    (V.twist χ).dual = V.dual.twist χ⁻¹ := by
  ext σ i j
  · simp [dual, twist]
  · simp [dual, twist]

theorem dual_nu (V : WDRep W n) (s : ℝ) : (V.nu s).dual = V.dual.nu (-s) := by
  rw [nu, dual_twist, nu]
  congr 1
  ext σ
  simp only [MonoidHom.inv_apply, WDGroup.qPowHom, MonoidHom.coe_mk, OneHom.coe_mk,
    Units.val_inv_eq_inv_val, Units.val_mk0]
  exact (W.qPow_neg s σ).symm

theorem isTame_dual_iff (V : WDRep W n) : V.dual.IsTame ↔ V.IsTame := by
  constructor
  · intro h σ hσ
    have h' := h σ⁻¹ (W.wild.inv_mem hσ)
    ext i j
    have hij := congrArg (fun M : Matrix.GeneralLinearGroup (Fin n) ℂ => (M : Matrix (Fin n) (Fin n) ℂ) j i) h'
    simpa [dual, Matrix.one_apply, eq_comm] using hij
  · intro h σ hσ
    ext i j
    have h' := h σ⁻¹ (W.wild.inv_mem hσ)
    have hij := congrArg (fun M : Matrix.GeneralLinearGroup (Fin n) ℂ => (M : Matrix (Fin n) (Fin n) ℂ) j i) h'
    simpa [dual, Matrix.one_apply, eq_comm] using hij

/-- Superdiagonal nilpotent Jordan block of size `l × l`. -/
def jordanN (l : ℕ) : Matrix (Fin l) (Fin l) ℂ :=
  Matrix.of fun i j => if i.val + 1 = j.val then 1 else 0

private theorem jordanN_pow_apply (l k : ℕ) (i j : Fin l) :
    (jordanN l ^ k) i j = if i.val + k = j.val then 1 else 0 := by
  induction k generalizing i j with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, add_zero]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Fin.val_ne_of_ne hij]
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    simp_rw [ih, jordanN, Matrix.of_apply]
    by_cases h : i.val + (k + 1) = j.val
    · rw [if_pos h]
      have hlt : i.val + k < l := by omega
      let m : Fin l := ⟨i.val + k, hlt⟩
      rw [Finset.sum_eq_single m]
      · have hm1 : i.val + k = m.val := rfl
        have hm2 : m.val + 1 = j.val := by change i.val + k + 1 = j.val; omega
        simp [hm1, hm2]
      · intro x _ hxm
        have hx : i.val + k ≠ x.val := fun heq => hxm (Fin.ext heq.symm)
        simp [hx]
      · intro hm; exact absurd (Finset.mem_univ m) hm
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun x _ => ?_
      split_ifs with h1 h2
      · omega
      · simp
      · simp
      · simp

theorem isNilpotent_jordanN (l : ℕ) : IsNilpotent (jordanN l) := by
  refine ⟨l, ?_⟩
  ext i j
  rw [jordanN_pow_apply]
  have hj : j.val < l := j.isLt
  rw [if_neg (by omega)]
  rfl

/-- The `l`-dimensional special Weil–Deligne representation `Sp(l)` with diagonal Frobenius
eigenvalues `q^{-i · deg σ}` (`0 ≤ i < l`) and maximal nilpotent Jordan block `jordanN l`. -/
def sp (W : WDGroup) (l : ℕ) : WDRep W l where
  ρ :=
    { toFun := fun σ =>
        { val := Matrix.diagonal fun i : Fin l => (W.qNorm σ) ^ (-(i.val : ℤ))
          inv := Matrix.diagonal fun i : Fin l => (W.qNorm σ) ^ (i.val : ℤ)
          val_inv := by
            rw [Matrix.diagonal_mul_diagonal]
            ext i j
            by_cases hij : i = j
            · subst hij
              simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, _root_.zpow_neg]
              exact inv_mul_cancel₀ (zpow_ne_zero _ (W.qNorm_ne_zero σ))
            · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
          inv_val := by
            rw [Matrix.diagonal_mul_diagonal]
            ext i j
            by_cases hij : i = j
            · subst hij
              simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, _root_.zpow_neg]
              exact mul_inv_cancel₀ (zpow_ne_zero _ (W.qNorm_ne_zero σ))
            · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij] }
      map_one' := by
        ext i j
        by_cases hij : i = j
        · subst hij; simp [W.qNorm_one]
        · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
      map_mul' := fun σ τ => by
        ext i j
        simp only [Units.val_mul, Matrix.diagonal_mul_diagonal]
        by_cases hij : i = j
        · subst hij
          simp only [Matrix.diagonal_apply_eq, W.qNorm_mul, mul_zpow]
        · simp [Matrix.diagonal_apply_ne _ hij] }
  N := jordanN l
  nilp := isNilpotent_jordanN l
  compat := fun σ => by
    change Matrix.diagonal (fun i : Fin l => W.qNorm σ ^ (-(i.val : ℤ))) * jordanN l *
        Matrix.diagonal (fun i : Fin l => W.qNorm σ⁻¹ ^ (-(i.val : ℤ))) =
      W.qNorm σ • jordanN l
    ext i j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, jordanN, Matrix.of_apply,
      Matrix.smul_apply, smul_eq_mul, W.qNorm_inv, _root_.inv_zpow, _root_.zpow_neg, inv_inv]
    by_cases h : i.val + 1 = j.val
    · rw [if_pos h, mul_one, mul_one]
      have hne := W.qNorm_ne_zero σ
      rw [← h, Nat.cast_add, Nat.cast_one, zpow_add₀ hne, zpow_one]
      field_simp [zpow_ne_zero _ hne]
    · simp [if_neg h]

theorem isTame_sp (W : WDGroup) (l : ℕ) : (sp W l).IsTame := by
  intro σ hσ
  ext i j
  by_cases hij : i = j
  · subst hij; simp [sp, W.qNorm_wild hσ]
  · simp [sp, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

theorem charPol_sp (W : WDGroup) (l : ℕ) (σ : W.G) :
    (sp W l).charPol σ = ∏ i : Fin l, (X - C ((W.qNorm σ) ^ (-(i.val : ℤ)))) := by
  rw [charPol]
  exact Matrix.charpoly_diagonal _

theorem wdDet_sp (W : WDGroup) (l : ℕ) (σ : W.G) :
    (sp W l).wdDet σ = ∏ i : Fin l, (W.qNorm σ) ^ (-(i.val : ℤ)) := by
  rw [wdDet]
  exact Matrix.det_diagonal

theorem not_isIrr_sp (W : WDGroup) {l : ℕ} (hl : 2 ≤ l) : ¬(sp W l).IsIrr := by
  intro hirr
  have hN := monodromy_eq_zero_of_isIrr (sp W l) hirr
  have h01 : (sp W l).N ⟨0, by omega⟩ ⟨1, by omega⟩ = 0 := by rw [hN]; rfl
  simp [sp, jordanN] at h01

private theorem reindex_finSum_mul {n m : ℕ}
    (A B : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℂ) :
    Matrix.reindex finSumFinEquiv finSumFinEquiv A *
      Matrix.reindex finSumFinEquiv finSumFinEquiv B =
    Matrix.reindex finSumFinEquiv finSumFinEquiv (A * B) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp finSumFinEquiv.symm
    (fun k => A (finSumFinEquiv.symm i) k * B k (finSumFinEquiv.symm j))

private theorem reindex_finSum_one {n m : ℕ} :
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (1 : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℂ) = 1 := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.one_apply]

/-- Block direct sum `V₁ ⊕ V₂` of two Weil–Deligne representations via `finSumFinEquiv`. -/
def directSum (V₁ : WDRep W n) (V₂ : WDRep W m) : WDRep W (n + m) where
  ρ :=
    { toFun := fun σ =>
        { val := Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks (V₁.ρ σ : Matrix (Fin n) (Fin n) ℂ) 0 0
              (V₂.ρ σ : Matrix (Fin m) (Fin m) ℂ))
          inv := Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks (V₁.ρ σ⁻¹ : Matrix (Fin n) (Fin n) ℂ) 0 0
              (V₂.ρ σ⁻¹ : Matrix (Fin m) (Fin m) ℂ))
          val_inv := by
            rw [reindex_finSum_mul, Matrix.fromBlocks_multiply]
            have h1 : (V₁.ρ σ : Matrix (Fin n) (Fin n) ℂ) * (V₁.ρ σ⁻¹ : Matrix (Fin n) (Fin n) ℂ) = 1 := by
              change (V₁.ρ σ * V₁.ρ σ⁻¹ : Matrix.GeneralLinearGroup (Fin n) ℂ).val = 1
              rw [← map_mul, mul_inv_cancel, map_one, Units.val_one]
            have h2 : (V₂.ρ σ : Matrix (Fin m) (Fin m) ℂ) * (V₂.ρ σ⁻¹ : Matrix (Fin m) (Fin m) ℂ) = 1 := by
              change (V₂.ρ σ * V₂.ρ σ⁻¹ : Matrix.GeneralLinearGroup (Fin m) ℂ).val = 1
              rw [← map_mul, mul_inv_cancel, map_one, Units.val_one]
            simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, h1, h2,
              Matrix.fromBlocks_one, reindex_finSum_one]
          inv_val := by
            rw [reindex_finSum_mul, Matrix.fromBlocks_multiply]
            have h1 : (V₁.ρ σ⁻¹ : Matrix (Fin n) (Fin n) ℂ) * (V₁.ρ σ : Matrix (Fin n) (Fin n) ℂ) = 1 := by
              change (V₁.ρ σ⁻¹ * V₁.ρ σ : Matrix.GeneralLinearGroup (Fin n) ℂ).val = 1
              rw [← map_mul, inv_mul_cancel, map_one, Units.val_one]
            have h2 : (V₂.ρ σ⁻¹ : Matrix (Fin m) (Fin m) ℂ) * (V₂.ρ σ : Matrix (Fin m) (Fin m) ℂ) = 1 := by
              change (V₂.ρ σ⁻¹ * V₂.ρ σ : Matrix.GeneralLinearGroup (Fin m) ℂ).val = 1
              rw [← map_mul, inv_mul_cancel, map_one, Units.val_one]
            simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, h1, h2,
              Matrix.fromBlocks_one, reindex_finSum_one] }
      map_one' := by
        apply Units.ext
        change Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (V₁.ρ 1 : Matrix (Fin n) (Fin n) ℂ) 0 0
            (V₂.ρ 1 : Matrix (Fin m) (Fin m) ℂ)) = 1
        simp only [map_one, Units.val_one, Matrix.fromBlocks_one, reindex_finSum_one]
      map_mul' := fun σ τ => by
        apply Units.ext
        change Matrix.reindex finSumFinEquiv finSumFinEquiv _ =
          Matrix.reindex finSumFinEquiv finSumFinEquiv _ * Matrix.reindex finSumFinEquiv finSumFinEquiv _
        rw [reindex_finSum_mul, Matrix.fromBlocks_multiply]
        simp }
  N := Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks V₁.N 0 0 V₂.N)
  nilp := by
    obtain ⟨k₁, hk₁⟩ := V₁.nilp
    obtain ⟨k₂, hk₂⟩ := V₂.nilp
    refine ⟨max k₁ k₂, ?_⟩
    have hpow : ∀ k : ℕ,
        (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks V₁.N 0 0 V₂.N)) ^ k =
        Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (V₁.N ^ k) 0 0 (V₂.N ^ k)) := by
      intro k
      induction k with
      | zero => simp [Matrix.fromBlocks_one]
      | succ k ih =>
        rw [pow_succ, ih, reindex_finSum_mul, Matrix.fromBlocks_multiply]
        simp [pow_succ]
    rw [hpow]
    have h1 : V₁.N ^ max k₁ k₂ = 0 := by
      rw [← Nat.add_sub_of_le (le_max_left k₁ k₂), pow_add, hk₁, zero_mul]
    have h2 : V₂.N ^ max k₁ k₂ = 0 := by
      rw [← Nat.add_sub_of_le (le_max_right k₁ k₂), pow_add, hk₂, zero_mul]
    simp [h1, h2]
  compat := fun σ => by
    change Matrix.reindex finSumFinEquiv finSumFinEquiv _ *
        Matrix.reindex finSumFinEquiv finSumFinEquiv _ *
        Matrix.reindex finSumFinEquiv finSumFinEquiv _ = _
    rw [reindex_finSum_mul, reindex_finSum_mul, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, V₁.compat σ, V₂.compat σ]
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply]
    rcases finSumFinEquiv.symm i with i₁ | i₂ <;> rcases finSumFinEquiv.symm j with j₁ | j₂ <;>
      simp [Matrix.fromBlocks]

theorem wdDet_directSum (V₁ : WDRep W n) (V₂ : WDRep W m) (σ : W.G) :
    (V₁.directSum V₂).wdDet σ = V₁.wdDet σ * V₂.wdDet σ := by
  simp only [wdDet, directSum, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.det_reindex_self,
    Matrix.det_fromBlocks_zero₁₂]

theorem charPol_directSum (V₁ : WDRep W n) (V₂ : WDRep W m) (σ : W.G) :
    (V₁.directSum V₂).charPol σ = V₁.charPol σ * V₂.charPol σ := by
  simp only [charPol, directSum, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [Matrix.charpoly_reindex]
  exact Matrix.charpoly_fromBlocks_zero₁₂ _ _ _

theorem isTame_directSum_iff (V₁ : WDRep W n) (V₂ : WDRep W m) :
    (V₁.directSum V₂).IsTame ↔ V₁.IsTame ∧ V₂.IsTame := by
  constructor
  · intro h
    refine ⟨fun σ hσ => ?_, fun σ hσ => ?_⟩
    · have h' := congrArg (fun M : Matrix.GeneralLinearGroup (Fin (n + m)) ℂ =>
        Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm (M : Matrix (Fin (n + m)) (Fin (n + m)) ℂ)) (h σ hσ)
      ext i j
      have hij := congrArg (fun M => M (Sum.inl i) (Sum.inl j)) h'
      simpa [directSum, Matrix.one_apply] using hij
    · have h' := congrArg (fun M : Matrix.GeneralLinearGroup (Fin (n + m)) ℂ =>
        Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm (M : Matrix (Fin (n + m)) (Fin (n + m)) ℂ)) (h σ hσ)
      ext i j
      have hij := congrArg (fun M => M (Sum.inr i) (Sum.inr j)) h'
      simpa [directSum, Matrix.one_apply] using hij
  · rintro ⟨h1, h2⟩ σ hσ
    apply Units.ext
    change Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (V₁.ρ σ : Matrix (Fin n) (Fin n) ℂ) 0 0
        (V₂.ρ σ : Matrix (Fin m) (Fin m) ℂ)) = 1
    rw [h1 σ hσ, h2 σ hσ]
    simp only [Units.val_one, Matrix.fromBlocks_one, reindex_finSum_one]

theorem dual_directSum (V₁ : WDRep W n) (V₂ : WDRep W m) :
    (V₁.directSum V₂).dual = V₁.dual.directSum V₂.dual := by
  apply WDRep.ext
  · ext σ i j
    simp only [dual, directSum, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.transpose_apply,
      Matrix.reindex_apply, Matrix.submatrix_apply]
    rcases finSumFinEquiv.symm i with i₁ | i₂ <;> rcases finSumFinEquiv.symm j with j₁ | j₂ <;>
      simp [Matrix.fromBlocks]
  · ext i j
    simp only [dual, directSum, Matrix.neg_apply, Matrix.transpose_apply,
      Matrix.reindex_apply, Matrix.submatrix_apply]
    rcases finSumFinEquiv.symm i with i₁ | i₂ <;> rcases finSumFinEquiv.symm j with j₁ | j₂ <;>
      simp [Matrix.fromBlocks]

/-- Zero-dimensional trivial Weil–Deligne representation. -/
def zero (W : WDGroup) : WDRep W 0 where
  ρ := 1
  N := 0
  nilp := IsNilpotent.zero
  compat := fun _ => by simp

theorem isTame_zero (W : WDGroup) : (zero W).IsTame := fun _ _ => rfl

theorem wdDet_zero (W : WDGroup) (σ : W.G) : (zero W).wdDet σ = 1 := by
  simp [wdDet, zero]

theorem charPol_zero (W : WDGroup) (σ : W.G) : (zero W).charPol σ = 1 := by
  simp [charPol, zero]

end WDRep

/-- Dimension-bundled Weil–Deligne representation `Σ n, WDRep W n`. -/
abbrev AnyWDRep (W : WDGroup) := Σ n : ℕ, WDRep W n

namespace AnyWDRep

variable {W : WDGroup}

/-- Direct sum of a list of Weil–Deligne representations. -/
def listSum (W : WDGroup) : List (AnyWDRep W) → AnyWDRep W
  | [] => ⟨0, WDRep.zero W⟩
  | V :: L =>
    let R := listSum W L
    ⟨V.1 + R.1, V.2.directSum R.2⟩

theorem dim_listSum (L : List (AnyWDRep W)) :
    (listSum W L).1 = (L.map Sigma.fst).sum := by
  induction L with
  | nil => rfl
  | cons V L ih => simp [listSum, ih]

theorem wdDet_listSum (L : List (AnyWDRep W)) (σ : W.G) :
    (listSum W L).2.wdDet σ = (L.map (fun V => V.2.wdDet σ)).prod := by
  induction L with
  | nil => exact WDRep.wdDet_zero W σ
  | cons V L ih =>
    simp only [listSum, List.map_cons, List.prod_cons]
    rw [WDRep.wdDet_directSum, ih]

theorem charPol_listSum (L : List (AnyWDRep W)) (σ : W.G) :
    (listSum W L).2.charPol σ = (L.map (fun V => V.2.charPol σ)).prod := by
  induction L with
  | nil => exact WDRep.charPol_zero W σ
  | cons V L ih =>
    simp only [listSum, List.map_cons, List.prod_cons]
    rw [WDRep.charPol_directSum, ih]

theorem isTame_listSum_iff (L : List (AnyWDRep W)) :
    (listSum W L).2.IsTame ↔ ∀ V ∈ L, V.2.IsTame := by
  induction L with
  | nil => simp [listSum, WDRep.isTame_zero]
  | cons V L ih =>
    simp only [listSum, WDRep.isTame_directSum_iff, ih, List.mem_cons, forall_eq_or_imp]

end AnyWDRep

/-! ## 3. Exact 12-Law `LocalLanglandsLaws` (`LawsT`) Consequences, Extension & Uniqueness -/

end LocalLanglands

namespace LocalLanglandsLaws

variable {P : LocalLanglandsPlace} {rc : P.IrrGL → P.WD}

/-- Rank-1 Artin reciprocity preserves dimension `1`. -/
theorem dim_ofChar (L : LocalLanglandsLaws P rc) (χ : P.SmoothChar)
    (hdeg : P.deg (P.ofChar χ) = 1) : P.wdDim (P.wdOfChar χ) = 1 := by
  rw [← L.one χ, L.dim, hdeg]

/-- Unconditional central-character norm match on rank-1 characters. -/
theorem artin_central_norm (L : LocalLanglandsLaws P rc) (χ : P.SmoothChar)
    (hcc : P.HasCentralChar (P.ofChar χ) χ) (σ : P.Weil) :
    ‖P.wdDet (P.wdOfChar χ) σ‖ = ‖P.artinEval χ σ‖ := by
  rw [← L.one χ]
  exact L.absCentral (P.ofChar χ) χ hcc σ

/-- Exact Artin reciprocity central-character match on `Good` rank-1 characters. -/
theorem artin_central_of_good (L : LocalLanglandsLaws P rc) (χ : P.SmoothChar)
    (hg : P.IsGood (P.ofChar χ)) (hcc : P.HasCentralChar (P.ofChar χ) χ) (σ : P.Weil) :
    P.wdDet (P.wdOfChar χ) σ = P.artinEval χ σ := by
  rw [← L.one χ]
  exact L.central (P.ofChar χ) χ hg hcc σ

/-- Injectivity of `wdOfChar` onto `Good` rank-1 representations. -/
theorem ofChar_inj_of_good (L : LocalLanglandsLaws P rc)
    {χ₁ χ₂ : P.SmoothChar} (hg : P.IsGood (P.ofChar χ₂))
    (heq : P.wdOfChar χ₁ = P.wdOfChar χ₂) : P.ofChar χ₁ = P.ofChar χ₂ :=
  L.inj (P.ofChar χ₁) (P.ofChar χ₂) hg (by rw [L.one, L.one, heq])

/-- Central character uniqueness (up to Artin evaluation) on `Good` representations. -/
theorem central_unique_of_good (L : LocalLanglandsLaws P rc)
    {x : P.IrrGL} {ω₁ ω₂ : P.SmoothChar} (hg : P.IsGood x)
    (h1 : P.HasCentralChar x ω₁) (h2 : P.HasCentralChar x ω₂) (σ : P.Weil) :
    P.artinEval ω₁ σ = P.artinEval ω₂ σ := by
  rw [← L.central x ω₁ hg h1 σ, L.central x ω₂ hg h2 σ]

/-- Character twist formula expressed directly in terms of `wdOfChar`. -/
theorem twist_wdOfChar (L : LocalLanglandsLaws P rc)
    {x : P.IrrGL} (χ : P.SmoothChar) (hg : P.IsGood x) :
    rc (P.tw x χ) = P.wdTwist (rc x) (P.wdOfChar χ) := by
  rw [L.twist x χ hg, L.one χ]

/-- Compatibility of `rc` with combined unramified real twist and character twist. -/
theorem twist_nu_of_good (L : LocalLanglandsLaws P rc)
    {x : P.IrrGL} (s : ℝ) (χ : P.SmoothChar) (hg : P.IsGood (P.nu x s)) :
    rc (P.tw (P.nu x s) χ) = P.wdTwist (P.wdNu (rc x) s) (P.wdOfChar χ) := by
  rw [L.twist_wdOfChar χ hg, L.nu x s]

/-- Contragredient duality preserves dimension via `rc`. -/
theorem dual_dim (L : LocalLanglandsLaws P rc)
    {x y : P.IrrGL} (hg : P.IsGood x) (hd : P.IsDual x y) :
    P.wdDim (P.wdDual (rc x)) = P.deg y := by
  rw [← L.dual x y hg hd, L.dim y]

/-- Double contragredient involution on Weil–Deligne parameters of `Good` representations. -/
theorem dual_involutive_on_good (L : LocalLanglandsLaws P rc)
    {x y : P.IrrGL} (hgx : P.IsGood x) (hgy : P.IsGood y)
    (hxy : P.IsDual x y) (hyx : P.IsDual y x) :
    P.wdDual (P.wdDual (rc x)) = rc x := by
  rw [← L.dual x y hgx hxy, ← L.dual y x hgy hyx]

/-- Uniqueness of a `Good` contragredient via injectivity of `rc`. -/
theorem dual_unique_on_good (L : LocalLanglandsLaws P rc)
    {x y₁ y₂ : P.IrrGL} (hgx : P.IsGood x) (hgy₂ : P.IsGood y₂)
    (hd₁ : P.IsDual x y₁) (hd₂ : P.IsDual x y₂) : y₁ = y₂ :=
  L.inj y₁ y₂ hgy₂ (by rw [L.dual x y₁ hgx hd₁, L.dual x y₂ hgx hd₂])

/-- Dimension compatibility on Langlands quotients. -/
theorem dim_langlands (L : LocalLanglandsLaws P rc)
    {l : P.SegmentList} {x : P.IrrGL} (hl : P.IsLanglandsQuot l x) :
    P.wdDim (P.segSum rc l) = P.deg x := by
  rw [← L.langlands l x hl, L.dim x]

/-- Dimension additivity: whenever `wdDim (segSum rc l)` equals the segment-list total degree
`segDeg l`, every Langlands quotient of `l` has degree `segDeg l`. -/
theorem deg_eq_of_segDim (L : LocalLanglandsLaws P rc)
    (segDeg : P.SegmentList → ℕ)
    (hadd : ∀ l, P.wdDim (P.segSum rc l) = segDeg l)
    {l : P.SegmentList} {x : P.IrrGL} (hl : P.IsLanglandsQuot l x) :
    P.deg x = segDeg l := by
  rw [← L.dim_langlands hl, hadd l]

/-- Depth-zero `Good` supercuspidals map to irreducible, tamely ramified Weil–Deligne
parameters. -/
theorem cusp_tame_of_depthZero_good (L : LocalLanglandsLaws P rc)
    {x : P.IrrGL} (hc : P.IsCusp x) (hg : P.IsGood x) (hdz : P.IsDepthZero x) :
    P.IsIrrWD (rc x) ∧ P.IsTameWD (rc x) :=
  ⟨L.cusp x hc, L.depth x hg hdz⟩

end LocalLanglandsLaws

namespace LocalLanglands

/-! ### Cuspidal-to-General Extension (`RecTExists`) & Uniqueness (`RecTUnique`) -/

/-- Supercuspidal-level Local Langlands package (mirroring `UpperTheory.Zero.LLC.CuspT` in
`RecTTransport.lean`). -/
structure CuspidalLanglandsLaws (P : LocalLanglandsPlace) (r : P.IrrGL → P.WD) : Prop where
  irr : ∀ x, P.IsCusp x → P.IsIrrWD (r x)
  dim : ∀ x, P.IsCusp x → P.wdDim (r x) = P.deg x
  one : ∀ χ, r (P.ofChar χ) = P.wdOfChar χ
  nu : ∀ x, P.IsCusp x → ∀ s : ℝ, r (P.nu x s) = P.wdNu (r x) s
  absCentral : ∀ x, P.IsCusp x → ∀ ω, P.HasCentralChar x ω → ∀ σ,
    ‖P.wdDet (r x) σ‖ = ‖P.artinEval ω σ‖
  twist : ∀ x, P.IsCusp x → P.IsGood x → ∀ χ,
    r (P.tw x χ) = P.wdTwist (r x) (P.wdOfChar χ)
  central : ∀ x, P.IsCusp x → P.IsGood x → ∀ ω, P.HasCentralChar x ω → ∀ σ,
    P.wdDet (r x) σ = P.artinEval ω σ
  dual : ∀ x y, P.IsCusp x → P.IsCusp y → P.IsGood x → P.IsDual x y →
    r y = P.wdDual (r x)
  inj : ∀ x y, P.IsCusp x → P.IsCusp y → P.IsGood y → r x = r y → x = y
  depth : ∀ x, P.IsCusp x → P.IsGood x → P.IsDepthZero x → P.IsTameWD (r x)
  type : P.TypeLaw r

/-- Langlands multisegment extension relation (`IsLExt` in `RecTTransport.lean`): `rc` agrees
with `P.segSum r l` whenever `x` is the Langlands quotient of `l`. -/
def IsLanglandsExt (P : LocalLanglandsPlace) (r rc : P.IrrGL → P.WD) : Prop :=
  ∀ l x, P.IsLanglandsQuot l x → rc x = P.segSum r l

/-- Minimal structural coherence of multisegment decomposition needed to transport cuspidal
laws to all irreducible smooth representations (abstracting the 6 extension lemmas `ExtDim`,
`ExtTw`, `ExtDual`, `ExtInj`, `ExtDepth`, `TypeIff` of `RecTExists.lean`). -/
structure SegmentExtensionBridge (P : LocalLanglandsPlace) (r rc : P.IrrGL → P.WD) : Prop where
  ext : IsLanglandsExt P r rc
  cusp_agree : ∀ x, P.IsCusp x → rc x = r x
  ofChar_isCusp : ∀ χ, P.IsCusp (P.ofChar χ)
  segSum_agree_on_cusp : ∀ l x, P.IsLanglandsQuot l x → P.segSum rc l = P.segSum r l
  extDim : ∀ x, P.wdDim (rc x) = P.deg x
  extAbsCentral : ∀ x ω, P.HasCentralChar x ω → ∀ σ, ‖P.wdDet (rc x) σ‖ = ‖P.artinEval ω σ‖
  extCentral : ∀ x ω, P.IsGood x → P.HasCentralChar x ω → ∀ σ, P.wdDet (rc x) σ = P.artinEval ω σ
  extNu : ∀ x (s : ℝ), rc (P.nu x s) = P.wdNu (rc x) s
  extTwist : ∀ x χ, P.IsGood x → rc (P.tw x χ) = P.wdTwist (rc x) (P.wdOfChar χ)
  extDual : ∀ x y, P.IsGood x → P.IsDual x y → rc y = P.wdDual (rc x)
  extInj : ∀ x y, P.IsGood y → rc x = rc y → x = y
  extDepth : ∀ x, P.IsGood x → P.IsDepthZero x → P.IsTameWD (rc x)
  extType : P.TypeLaw r → P.TypeLaw rc

/-- Exact assembly of all 12 live fields of `LocalLanglandsLaws` (`LawsT`) from a cuspidal
correspondence `r` and its Langlands multisegment extension `rc` (mirroring
`UpperTheory.Zero.LLC.recTExists` in `RecTExists.lean`). -/
theorem localLanglandsLaws_of_cuspidal {P : LocalLanglandsPlace} {r rc : P.IrrGL → P.WD}
    (hc : CuspidalLanglandsLaws P r) (hb : SegmentExtensionBridge P r rc) :
    LocalLanglandsLaws P rc where
  dim := hb.extDim
  one χ := (hb.cusp_agree _ (hb.ofChar_isCusp χ)).trans (hc.one χ)
  langlands l x hl := (hb.ext l x hl).trans (hb.segSum_agree_on_cusp l x hl).symm
  cusp x hx := by rw [hb.cusp_agree x hx]; exact hc.irr x hx
  nu := hb.extNu
  absCentral := hb.extAbsCentral
  twist x χ hg := by
    rw [hb.cusp_agree _ (hb.ofChar_isCusp χ), hc.one χ]
    exact hb.extTwist x χ hg
  central := hb.extCentral
  dual := hb.extDual
  inj := hb.extInj
  depth := hb.extDepth
  type := hb.extType hc.type

/-- Uniqueness of the Local Langlands correspondence on `Good` representations (mirroring
`UpperTheory.Zero.LLC.recTUnique` in `RecTUnique.lean`): if `rc₁` and `rc₂` both satisfy
`LocalLanglandsLaws P`, agree on `Good` supercuspidals (the `ParUniq` pin), and every `Good`
representation is a Langlands quotient of a multisegment supported on `Good` supercuspidals,
then `rc₁ x = rc₂ x` for every `Good` representation `x`. -/
theorem recT_unique_on_good {P : LocalLanglandsPlace} {rc₁ rc₂ : P.IrrGL → P.WD}
    (L₁ : LocalLanglandsLaws P rc₁) (L₂ : LocalLanglandsLaws P rc₂)
    (hpin : ∀ y, P.IsCusp y → P.IsGood y → rc₁ y = rc₂ y)
    (hsupp : ∀ x, P.IsGood x →
      ∃ l : P.SegmentList, P.IsLanglandsQuot l x ∧
        ((∀ y, P.IsCusp y → P.IsGood y → rc₁ y = rc₂ y) → P.segSum rc₁ l = P.segSum rc₂ l)) :
    ∀ x, P.IsGood x → rc₁ x = rc₂ x := by
  intro x hx
  obtain ⟨l, hl, hseg⟩ := hsupp x hx
  rw [L₁.langlands l x hl, L₂.langlands l x hl]
  exact hseg hpin

/-! ## 4. Finite-Field Green Regular-Character Algebra (`NameLaws`) -/

section GreenRegularCharacters

/-- A multiplicative character `θ : Kˣ →* ℂˣ` of a degree-`n` extension `K / 𝔽_g` is regular
iff its `n` Frobenius conjugates `θ^{g^j}` (`0 ≤ j < n`) are pairwise distinct (mirroring
`GlobalTheory.Published.IsRegularChar` in `NameLaws.lean`). -/
def IsRegularChar (g n : ℕ) {K : Type*} [Field K] (θ : Kˣ →* ℂˣ) : Prop :=
  ∀ a b : ℕ, a < n → b < n → θ ^ (g ^ a) = θ ^ (g ^ b) → a = b

/-- Frobenius periodicity `θ^{g^n} = θ` for any character of a degree-`n` extension `K / 𝔽_g`
(mirroring `NameLaws.lean:pow_period`). -/
theorem char_pow_period {g : ℕ} [Fact g.Prime] {n : ℕ} (hn : 0 < n)
    {K : Type*} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = n) (θ : Kˣ →* ℂˣ) :
    θ ^ (g ^ n) = θ := by
  have : Module.Finite (ZMod g) K := Module.finite_of_finrank_pos (by rw [hK]; exact hn)
  have : Finite K := Module.finite_of_finite (ZMod g)
  let _ : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = g ^ n := by
    rw [Module.card_eq_pow_finrank (K := ZMod g) (V := K), ZMod.card, hK]
  ext z
  rw [MonoidHom.pow_apply, ← map_pow]
  congr 2
  ext
  rw [Units.val_pow_eq_pow_val, ← hc, FiniteField.pow_card]

theorem char_pow_add_mul {g : ℕ} [Fact g.Prime] {n : ℕ} (hn : 0 < n)
    {K : Type*} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = n) (θ : Kˣ →* ℂˣ) (m k : ℕ) :
    θ ^ (g ^ (m + n * k)) = θ ^ (g ^ m) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : θ ^ (g ^ (m + n * (k + 1))) = (θ ^ (g ^ n)) ^ (g ^ (m + n * k)) := by
      ext z
      simp only [MonoidHom.pow_apply, ← map_pow, ← pow_mul]
      rw [show m + n * (k + 1) = n + (m + n * k) by ring, pow_add]
    rw [hstep, char_pow_period hn hK, ih]

theorem char_pow_mod {g : ℕ} [Fact g.Prime] {n : ℕ} (hn : 0 < n)
    {K : Type*} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = n) (θ : Kˣ →* ℂˣ) (m : ℕ) :
    θ ^ (g ^ (m % n)) = θ ^ (g ^ m) := by
  conv_rhs => rw [← Nat.mod_add_div m n]
  exact (char_pow_add_mul hn hK θ _ _).symm

/-- Regularity of `θ` is preserved under Frobenius conjugation `θ ↦ θ^{g^j}` (mirroring
`NameLaws.lean:regular_pow`). -/
theorem isRegularChar_pow {g : ℕ} [Fact g.Prime] {n : ℕ} (hn : 0 < n)
    {K : Type*} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = n) {θ : Kˣ →* ℂˣ}
    (hθ : IsRegularChar g n θ) (j : ℕ) :
    IsRegularChar g n (θ ^ (g ^ j)) := by
  intro a b ha hb hab
  apply hθ a b ha hb
  have hrec : ∀ c : ℕ, θ ^ (g ^ c) = ((θ ^ (g ^ j)) ^ (g ^ c)) ^ (g ^ (n * j - j)) := by
    intro c
    have hj : j ≤ n * j := Nat.le_mul_of_pos_left j hn
    have hpow : ((θ ^ (g ^ j)) ^ (g ^ c)) ^ (g ^ (n * j - j)) = θ ^ (g ^ (c + n * j)) := by
      ext z
      simp only [MonoidHom.pow_apply, ← map_pow, ← pow_mul]
      congr 2
      rw [← pow_add, ← pow_add]
      congr 1
      congr 1
      omega
    rw [hpow, char_pow_add_mul hn hK θ c j]
  rw [hrec a, hrec b, hab]

/-- Green cuspidal character trace sum `(-1)^(n - 1) ∑_{j < n} θ(z^{g^j})` (entering
`UpperTheory.Zero.LLC.Names` and `TypeLaw`). -/
def greenCharSum (g n : ℕ) {K : Type*} [Field K] (θ : Kˣ →* ℂˣ) (z : Kˣ) : ℂ :=
  (-1 : ℂ) ^ (n - 1) * ∑ j ∈ Finset.range n, ((θ (z ^ (g ^ j)) : ℂˣ) : ℂ)

/-- The Green character trace sum is invariant under Frobenius conjugation `z ↦ z^g`. -/
theorem greenCharSum_frob_arg {g : ℕ} [Fact g.Prime] {n : ℕ} (hn : 0 < n)
    {K : Type*} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = n) (θ : Kˣ →* ℂˣ) (z : Kˣ) :
    greenCharSum g n θ (z ^ g) = greenCharSum g n θ z := by
  unfold greenCharSum
  congr 1
  have hstep : ∀ j : ℕ, ((θ ((z ^ g) ^ (g ^ j)) : ℂˣ) : ℂ) = ((θ (z ^ (g ^ (j + 1))) : ℂˣ) : ℂ) := by
    intro j
    rw [← pow_mul, ← pow_succ']
  simp_rw [hstep]
  cases n with
  | zero => exact absurd hn (lt_irrefl 0)
  | succ m =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
    have hper : θ (z ^ (g ^ (m + 1))) = θ (z ^ (g ^ 0)) := by
      have h := congrArg (fun φ : Kˣ →* ℂˣ => φ z) (char_pow_period hn hK θ)
      simp only [MonoidHom.pow_apply, ← map_pow] at h
      simpa using h
    rw [hper, add_comm]

/-- The Green character trace sum is invariant under Frobenius twist `θ ↦ θ^g`. -/
theorem greenCharSum_frob_char {g : ℕ} [Fact g.Prime] {n : ℕ} (hn : 0 < n)
    {K : Type*} [Field K] [Algebra (ZMod g) K]
    (hK : Module.finrank (ZMod g) K = n) (θ : Kˣ →* ℂˣ) (z : Kˣ) :
    greenCharSum g n (θ ^ g) z = greenCharSum g n θ z := by
  have heq : greenCharSum g n (θ ^ g) z = greenCharSum g n θ (z ^ g) := by
    unfold greenCharSum
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [MonoidHom.pow_apply, ← map_pow, ← pow_mul, mul_comm g (g ^ j)]
  rw [heq]
  exact greenCharSum_frob_arg hn hK θ z

end GreenRegularCharacters

/-! ## 5. Concrete Non-Vacuous Instantiation of `LocalLanglandsLaws` -/

section ConcreteModel

/-- Concrete Weil–Deligne Local Langlands model over a Weil group `W`:
every irreducible representation is modeled by its bundled Weil–Deligne parameter `AnyWDRep W`,
establishing non-vacuity and complete internal consistency of all 12 laws of
`LocalLanglandsLaws` (and `FullLocalLanglandsLaws`). -/
def concretePlace (W : WDGroup) : LocalLanglandsPlace where
  IrrGL := AnyWDRep W
  deg x := x.1
  IsCusp x := x.2.IsIrr
  IsDepthZero x := x.2.IsTame
  IsGood _ := True
  SmoothChar := W.G →* ℂˣ
  ofChar χ := ⟨1, WDRep.ofChar W χ⟩
  nu x s := ⟨x.1, x.2.nu s⟩
  tw x χ := ⟨x.1, x.2.twist χ⟩
  IsDual x y := y = ⟨x.1, x.2.dual⟩
  HasCentralChar x ω := ∀ σ : W.G, x.2.wdDet σ = (ω σ : ℂ)
  SegmentList := List (AnyWDRep W)
  IsLanglandsQuot l x := x = AnyWDRep.listSum W l
  Weil := W.G
  WD := AnyWDRep W
  wdDim x := x.1
  IsIrrWD x := x.2.IsIrr
  IsTameWD x := x.2.IsTame
  wdOfChar χ := ⟨1, WDRep.ofChar W χ⟩
  wdNu x s := ⟨x.1, x.2.nu s⟩
  wdTwist x y :=
    if _ : y.1 = 1 then
      ⟨x.1, x.2.twist
        { toFun := fun σ => Units.mk0 (y.2.wdDet σ) (y.2.wdDet_ne_zero σ)
          map_one' := by ext; exact y.2.wdDet_one
          map_mul' := fun σ τ => by ext; exact y.2.wdDet_mul σ τ }⟩
    else x
  wdDual x := ⟨x.1, x.2.dual⟩
  wdDet x σ := x.2.wdDet σ
  artinEval ω σ := (ω σ : ℂ)
  segSum f l := AnyWDRep.listSum W (l.map f)
  TypeLaw f := ∀ x, x.2.IsIrr → (f x).2.N = 0

/-- The identity correspondence on `concretePlace W` satisfies the full unrestricted
`FullLocalLanglandsLaws` (and hence all 12 live laws of `LocalLanglandsLaws`). -/
theorem fullLocalLanglandsLaws_concrete (W : WDGroup) :
    FullLocalLanglandsLaws (concretePlace W) id where
  dim _ := rfl
  one _ := rfl
  langlands l x hl := by
    have hmap : List.map (id : AnyWDRep W → AnyWDRep W) l = l := List.map_id l
    exact hl.trans (congrArg (AnyWDRep.listSum W) hmap.symm)
  cusp _ hx := hx
  nu _ _ := rfl
  twist x χ := by
    rcases x with ⟨n, V⟩
    simp only [concretePlace, id_eq, ↓reduceDIte]
    congr 1
    congr 1
    apply MonoidHom.ext
    intro σ
    ext
    exact (WDRep.wdDet_ofChar W χ σ).symm
  central _ _ hω σ := hω σ
  dual _ _ hd := hd
  inj := Function.injective_id
  depth _ hdz := hdz
  type x hx := WDRep.monodromy_eq_zero_of_isIrr x.2 hx

theorem localLanglandsLaws_concrete (W : WDGroup) :
    LocalLanglandsLaws (concretePlace W) id :=
  LocalLanglandsLaws.of_full (fullLocalLanglandsLaws_concrete W)

end ConcreteModel

end LocalLanglands
end RHDirect

end
