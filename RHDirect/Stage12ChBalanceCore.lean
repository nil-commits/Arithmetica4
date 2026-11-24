import RHDirect.Interfaces
import RHDirect.CosetWeights
import RHDirect.ZeroDensityWindow
import RHDirect.Stage2AnalyticWire
import RHDirect.Stage4ExplicitFormula
import RHDirect.Stage5ContourExplicit
import RHDirect.Stage5ZetaZeroFree
import RHDirect.Stage5DirichletLZeroFree
import RHDirect.Stage7SiegelWalfisz
import RHDirect.Stage8UniformAP
import RHDirect.Stage9LandauSiegel
import RHDirect.Stage10SiegelWalfiszFull
import RHDirect.Stage11BombieriVinogradov
import RHDirect.Stage11LogFreeDensity
import RHDirect.Stage11LinnikBridge
import RHDirect.Stage11LinnikUnconditional
import RHDirect.Stage11SecondMomentFrame

/-!
# RHDirect.Stage12ChBalanceCore

**Phase C / Stage 12 (6 of 9) — Unconditional Exact Galois Fourier Inversion (`ch_balance`),
Coset-Average Bridge (`ch_core` → `core_gm`), and Unconditional Quadratic-Twist Mean-Square &
`PairGood` Prime-Pair Existence (`MSqMain` / `BoxOfS` / `SigALe`)**
in pure Mathlib `v4.33.1` (`0` `sorry`, `0` custom `axiom`s, `0` `native_decide`, targeted imports).

## Main Components

1. **Section 1 — Unconditional Galois Fourier Inversion (`ch_balance`: `ASK - MAIN = De`)**:
   - Exact finite-abelian character orthogonality on `E0 × H` where `E0 := ZMod 2 × ZMod 2`
     indexes the quadratic character pair `(χ_q, χ_d)` via `(i, j) ∈ Fin 2 × Fin 2`.
   - Exact inert-prime ramp sum `ASK D N a t w`, main term `MAIN ell a w`, and oscillatory
     character-twist decomposition `De D ell a t w`.
   - **`ch_balance`** (`0` assumptions!): `(ASK D N a t w : ℂ) - MAIN ell a w = De D ell a t w`.
   - Concrete splitting-field instantiation `quadPairArithData` over `(q, d)` and exact `Fin 2 × Fin 2`
     quadratic-twist decomposition `ch_balance_quadPair`.

2. **Section 2 — Unconditional Coset-Average Bridge (`ch_core`, `sigA_le`, `core_gm`)**:
   - Thick-place projection `Th`, exact subgroup-coset cancellation `sum_Th`, and averaged
     bound `ch_core_average`.
   - **`ch_core`**: combines `ch_balance`, `CosetWeights.CosetFrame.fourier_clear_perturbed_le`,
     and `ZeroDensityWindow.growth_bound_of_restSize` to deduce `GmA ≤ x^(1/2 + (C + 3) * ε) + SigA`.
   - **`sigA_le` & `core_gm`**: proves `SigA ≤ 4 * L.o * x^(1/2 + ε)` and deduces
     `L.Gm x ≤ x^(1/2 + (eD + eL + 7) * ε)` (matching `UpperTheory.Comparison₂.core_gm` and feeding
     directly into `Stage2AnalyticWire.level_window_coupling` / `stage2_analyticBridgeContract`),
     eliminating `mainBalance` as an abstract field (`levelBracketData_of_ch_balance`).

3. **Section 3 — Quadratic-Twist Primitivity, Unconditional `ZeroFreeBox`, Borel–Carathéodory & `BoxOfS`**
4. **Section 4 — Unconditional Quadratic-Twist Mean-Square Bounds (`MSqMain`, Large Sieve + Reciprocity)**
5. **Section 5 — Unconditional `PairGood` Prime-Pair Existence (`pairGood_exists_unconditional`)**
-/

noncomputable section

open Complex DirichletCharacter Finset Real MeasureTheory Set Filter Topology
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHDirect.Stage12ChBalanceCore

open RHDirect

/-! ## Section 1: Unconditional Exact Galois Fourier Inversion (`ch_balance`) -/

private lemma zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

private lemma zmod2_add_one_add_one (x : ZMod 2) : x + 1 + 1 = x := by
  rw [add_assoc, zmod2_one_add_one, add_zero]

private lemma zmod2_eq_one_of_ne_zero {x : ZMod 2} (h : x ≠ 0) : x = 1 :=
  (zmod2_cases x).resolve_left h

/-- Exact Klein four-group `ℤ/2ℤ × ℤ/2ℤ` indexing the quadratic character pair `(χ_q, χ_d)`
of the splitting field `E(q, d)` (`(i, j) ∈ Fin 2 × Fin 2`). -/
abbrev E0 : Type := ZMod 2 × ZMod 2

/-- The split half-group `InPhi` (`g.1.1 = 0`); its complement `¬ InPhi` (`g.1.1 = 1`) is the
inert coset of the CM quadratic extension. -/
def InPhi {H : Type} (g : E0 × H) : Prop := g.1.1 = 0

instance {H : Type} : DecidablePred (@InPhi H) := fun g =>
  inferInstanceAs (Decidable (g.1.1 = 0))

/-- Finite set of split elements `Φ ⊆ E0 × H`. -/
def PhiSet {H : Type} [Fintype H] [DecidableEq H] : Finset (E0 × H) :=
  Finset.univ.filter InPhi

/-- Finite set of inert elements `(E0 × H) \ Φ`. -/
def NotPhiSet {H : Type} [Fintype H] [DecidableEq H] : Finset (E0 × H) :=
  Finset.univ.filter fun g => ¬ InPhi g

theorem mem_PhiSet {H : Type} [Fintype H] [DecidableEq H] {g : E0 × H} :
    g ∈ PhiSet (H := H) ↔ InPhi g := by
  simp [PhiSet]

theorem mem_NotPhiSet {H : Type} [Fintype H] [DecidableEq H] {g : E0 × H} :
    g ∈ NotPhiSet (H := H) ↔ ¬ InPhi g := by
  simp [NotPhiSet]

/-- Shift-involution pairing inert elements `g ∉ Φ` bijectively with split elements `ρ ∈ Φ`. -/
def partner {H : Type} [AddCommGroup H] (t : H) (g : E0 × H) : E0 × H :=
  ((g.1.1 + 1, g.1.2), g.2 + t)

/-- The non-trivial element `((1, 0), 0) ∈ E0 × H` generating inertia at the ramified prime `d`. -/
def sgc0 {H : Type} [AddCommGroup H] : E0 × H := ((1, 0), 0)

theorem sgc0_add_self {H : Type} [AddCommGroup H] :
    sgc0 (H := H) + sgc0 = 0 := by
  ext
  · exact zmod2_one_add_one
  · simp [sgc0]
  · simp [sgc0]

/-- The canonical CM inertness ("colour") character `chC : AddChar (E0 × H) ℂ` sending
`Φ` to `+1` and `¬ Φ` to `-1`. -/
def chC {H : Type} [AddCommGroup H] : AddChar (E0 × H) ℂ where
  toFun := fun g => if g.1.1 = 0 then (1 : ℂ) else -1
  map_zero_eq_one' := by simp
  map_add_eq_mul' := fun a b => by
    rcases zmod2_cases a.1.1 with h1 | h1 <;> rcases zmod2_cases b.1.1 with h2 | h2 <;>
      simp [h1, h2, zmod2_one_add_one]

theorem chC_apply {H : Type} [AddCommGroup H] (g : E0 × H) :
    chC g = if InPhi g then (1 : ℂ) else -1 := rfl

theorem chC_ne_zero {H : Type} [AddCommGroup H] : (chC (H := H)) ≠ 0 := by
  intro h
  have h1 := DFunLike.congr_fun h (sgc0 (H := H))
  simp [chC, sgc0] at h1
  norm_num at h1

theorem inPhi_add {H : Type} [AddCommGroup H] {a b : E0 × H}
    (ha : InPhi a) (hb : InPhi b) : InPhi (a + b) := by
  simp only [InPhi, Prod.fst_add] at ha hb ⊢
  rw [ha, hb, add_zero]

theorem inPhi_zero {H : Type} [AddCommGroup H] : InPhi (0 : E0 × H) := rfl

theorem inPhi_nsmul {H : Type} [AddCommGroup H] {a : E0 × H} (ha : InPhi a) (n : ℕ) :
    InPhi (n • a) := by
  induction n with
  | zero => simp [inPhi_zero]
  | succ k ih => rw [succ_nsmul]; exact inPhi_add ih ha

theorem partner_inPhi {H : Type} [AddCommGroup H] (t : H) {g : E0 × H} (hg : ¬ InPhi g) :
    InPhi (partner t g) := by
  have h1 : g.1.1 = 1 := zmod2_eq_one_of_ne_zero hg
  change g.1.1 + 1 = 0
  rw [h1, zmod2_one_add_one]

theorem card_PhiSet {H : Type} [Fintype H] [DecidableEq H] :
    (PhiSet (H := H)).card = 2 * Fintype.card H := by
  have eqv : PhiSet (H := H) ≃ ZMod 2 × H :=
    { toFun := fun g => (g.1.1.2, g.1.2)
      invFun := fun p => ⟨((0, p.1), p.2), mem_PhiSet.mpr rfl⟩
      left_inv := fun g => by
        ext
        · exact (mem_PhiSet.mp g.2).symm
        · rfl
        · rfl
      right_inv := fun _ => rfl }
  have hc := Fintype.card_congr eqv
  simp only [Fintype.card_coe, Fintype.card_prod, ZMod.card] at hc
  exact hc

theorem card_notPhi {H : Type} [Fintype H] [DecidableEq H] :
    (NotPhiSet (H := H)).card = (PhiSet (H := H)).card := by
  have eqv : NotPhiSet (H := H) ≃ PhiSet (H := H) :=
    { toFun := fun g => ⟨((g.1.1.1 + 1, g.1.1.2), g.1.2), by
        have h1 : g.1.1.1 = 1 := zmod2_eq_one_of_ne_zero (mem_NotPhiSet.mp g.2)
        exact mem_PhiSet.mpr (by change g.1.1.1 + 1 = 0; rw [h1, zmod2_one_add_one])⟩
      invFun := fun g => ⟨((g.1.1.1 + 1, g.1.1.2), g.1.2), by
        have h0 : g.1.1.1 = 0 := mem_PhiSet.mp g.2
        exact mem_NotPhiSet.mpr (by change g.1.1.1 + 1 ≠ 0; rw [h0, zero_add]; decide)⟩
      left_inv := fun g => by
        ext
        · exact zmod2_add_one_add_one _
        · rfl
        · rfl
      right_inv := fun g => by
        ext
        · exact zmod2_add_one_add_one _
        · rfl
        · rfl }
  have hc := Fintype.card_congr eqv
  simpa only [Fintype.card_coe] using hc

theorem phi_card_pos {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] :
    0 < (PhiSet (H := H)).card := by
  rw [card_PhiSet]
  have : 0 < Fintype.card H := Fintype.card_pos_iff.mpr ⟨0⟩
  omega

theorem card_E0_prod {H : Type} [Fintype H] [DecidableEq H] :
    Fintype.card (E0 × H) = 2 * (PhiSet (H := H)).card := by
  rw [card_PhiSet, Fintype.card_prod, Fintype.card_prod, ZMod.card]
  ring

theorem sum_partner {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    {α : Type*} [AddCommMonoid α] (t : H) (f : E0 × H → α) :
    ∑ g ∈ NotPhiSet (H := H), f (partner t g) = ∑ ρ ∈ PhiSet (H := H), f ρ := by
  refine Finset.sum_bij (fun g _ => partner t g) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro g hg
    exact mem_PhiSet.mpr (partner_inPhi t (mem_NotPhiSet.mp hg))
  · intro a _ b _ hab
    unfold partner at hab
    have h1 := congrArg (fun x : E0 × H => x.1.1) hab
    have h2 := congrArg (fun x : E0 × H => x.1.2) hab
    have h3 := congrArg Prod.snd hab
    dsimp only at h1 h2 h3
    ext
    · exact add_right_cancel h1
    · exact h2
    · exact add_right_cancel h3
  · intro ρ hρ
    refine ⟨((ρ.1.1 + 1, ρ.1.2), ρ.2 - t), ?_, ?_⟩
    · have h0 : ρ.1.1 = 0 := mem_PhiSet.mp hρ
      exact mem_NotPhiSet.mpr (by change ρ.1.1 + 1 ≠ 0; rw [h0, zero_add]; decide)
    · unfold partner
      ext
      · exact zmod2_add_one_add_one _
      · rfl
      · simp

/-- Exact colour-character orthogonality over the inert coset `NotPhiSet`:
`∑_{g ∉ Φ} conj(ψ g)` equals `|Φ|` for `ψ = 0`, `-|Φ|` for `ψ = chC`, and `0` otherwise. -/
theorem colour_sum {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (ψ : AddChar (E0 × H) ℂ) :
    ∑ g ∈ NotPhiSet (H := H), starRingEnd ℂ (ψ g) =
      if ψ = 0 then ((PhiSet (H := H)).card : ℂ)
      else if ψ = chC then -((PhiSet (H := H)).card : ℂ)
      else 0 := by
  classical
  by_cases h0 : ψ = 0
  · subst h0
    rw [if_pos rfl]
    simp [card_notPhi]
  · rw [if_neg h0]
    by_cases hC : ψ = chC
    · subst hC
      rw [if_pos rfl]
      have hval : ∀ g ∈ NotPhiSet (H := H), starRingEnd ℂ (chC g) = -1 := by
        intro g hg
        rw [chC_apply, if_neg (mem_NotPhiSet.mp hg), map_neg, map_one]
      rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul, card_notPhi]
      ring
    · rw [if_neg hC]
      have hnt : ∃ s : E0 × H, InPhi s ∧ ψ s ≠ 1 := by
        by_contra hall
        push Not at hall
        have hval_sgc : ψ (sgc0 (H := H)) = 1 ∨ ψ (sgc0 (H := H)) = -1 := by
          have hsq : ψ (sgc0 (H := H)) * ψ (sgc0 (H := H)) = 1 := by
            rw [← AddChar.map_add_eq_mul, sgc0_add_self, AddChar.map_zero_eq_one]
          exact mul_self_eq_one_iff.mp hsq
        rcases hval_sgc with h1 | h1
        · apply h0
          ext g
          by_cases hg : InPhi g
          · exact hall g hg
          · have hg1 : g.1.1 = 1 := zmod2_eq_one_of_ne_zero hg
            have hdec : g = sgc0 + ((0, g.1.2), g.2) := by ext <;> simp [sgc0, hg1]
            have hphi0 : InPhi (((0, g.1.2) : E0), g.2) := rfl
            rw [hdec, AddChar.map_add_eq_mul, h1, one_mul, hall _ hphi0]
            rfl
        · apply hC
          ext g
          rw [chC_apply]
          by_cases hg : InPhi g
          · rw [if_pos hg]; exact hall g hg
          · rw [if_neg hg]
            have hg1 : g.1.1 = 1 := zmod2_eq_one_of_ne_zero hg
            have hdec : g = sgc0 + ((0, g.1.2), g.2) := by ext <;> simp [sgc0, hg1]
            have hphi0 : InPhi (((0, g.1.2) : E0), g.2) := rfl
            rw [hdec, AddChar.map_add_eq_mul, h1, hall _ hphi0, mul_one]
      obtain ⟨s, hsPhi, hsne⟩ := hnt
      set S : ℂ := ∑ g ∈ NotPhiSet (H := H), starRingEnd ℂ (ψ g)
      have hshift : starRingEnd ℂ (ψ s) * S = S := by
        dsimp only [S]
        rw [Finset.mul_sum]
        refine Finset.sum_bij (fun g _ => s + g) ?_ ?_ ?_ ?_
        · intro g hg
          have hg' : g.1.1 ≠ 0 := mem_NotPhiSet.mp hg
          exact mem_NotPhiSet.mpr (by
            change s.1.1 + g.1.1 ≠ 0
            rw [show s.1.1 = 0 from hsPhi, zero_add]
            exact hg')
        · intro a _ b _ hab; exact add_left_cancel hab
        · intro g hg
          have hg' : g.1.1 ≠ 0 := mem_NotPhiSet.mp hg
          refine ⟨g - s, ?_, by abel⟩
          exact mem_NotPhiSet.mpr (by
            change g.1.1 - s.1.1 ≠ 0
            rw [show s.1.1 = 0 from hsPhi, sub_zero]
            exact hg')
        · intro g _
          rw [AddChar.map_add_eq_mul, map_mul]
      have hne1 : starRingEnd ℂ (ψ s) - 1 ≠ 0 := by
        intro hz
        apply hsne
        have hconj : starRingEnd ℂ (ψ s) = 1 := sub_eq_zero.mp hz
        have := congrArg (starRingEnd ℂ) hconj
        simpa using this
      exact (mul_eq_zero.mp (by linear_combination hshift : (starRingEnd ℂ (ψ s) - 1) * S = 0)).resolve_left hne1

/-- Arithmetic Frobenius and inertia data on the finite abelian Galois group `E0 × H`. -/
structure ArithData (H : Type) [AddCommGroup H] where
  frob : ℕ → E0 × H
  inertia : ℕ → AddSubgroup (E0 × H)
  q1 : ℕ
  d : ℕ

/-- Host splitting-field ramification facts on `ArithData H`:
- unramified outside `S0 ∪ {D.d}` (`inertia p = ⊥`),
- completely split (`InPhi`) on `S0` (containing `2` and `D.q1`),
- tamely ramified of degree `2` at the prime `D.d` with `inertia D.d = {0, sgc0}`. -/
structure HostFactsS {H : Type} [AddCommGroup H] (D : ArithData H) (S0 : Finset ℕ) : Prop where
  d_prime : D.d.Prime
  two_mem : 2 ∈ S0
  q1_mem : D.q1 ∈ S0
  d_not_mem : D.d ∉ S0
  unram : ∀ p : ℕ, p.Prime → p ∉ S0 → p ≠ D.d → D.inertia p = ⊥
  split_frob : ∀ p ∈ S0, InPhi (D.frob p)
  split_inertia : ∀ p ∈ S0, ∀ x ∈ D.inertia p, InPhi x
  inertia_d : ∀ x : E0 × H, x ∈ D.inertia D.d ↔ x = 0 ∨ x = sgc0

/-- Inert prime predicate in `ArithData H`: unramified prime `p ∉ {2, q1, d}` with `¬ InPhi (frob p)`. -/
def IsInert {H : Type} [AddCommGroup H] (D : ArithData H) (p : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧ p ≠ D.q1 ∧ p ≠ D.d ∧ ¬ InPhi (D.frob p)

open Classical in
/-- Primitive character evaluation `primVal D ψ n` at prime powers `n = p^i` (`i ≥ 1`):
equals `ψ(i • frob p)` when `ψ` is unramified at `p` (trivial on `inertia p`), and `0` otherwise. -/
def primVal {H : Type} [AddCommGroup H] (D : ArithData H) (ψ : AddChar (E0 × H) ℂ) (n : ℕ) : ℂ :=
  if IsPrimePow n then
    let p := n.minFac
    let i := n.factorization p
    if ∀ x ∈ D.inertia p, ψ x = 1 then ψ (i • D.frob p) else 0
  else 0

open Classical in
theorem primVal_primePow {H : Type} [AddCommGroup H] (D : ArithData H)
    (ψ : AddChar (E0 × H) ℂ) {p i : ℕ} (hp : p.Prime) (hi : 1 ≤ i) :
    primVal D ψ (p ^ i) = if ∀ x ∈ D.inertia p, ψ x = 1 then ψ (i • D.frob p) else 0 := by
  have hpp : IsPrimePow (p ^ i) := (isPrimePow_nat_iff _).mpr ⟨p, i, hp, by omega, rfl⟩
  have hmf : (p ^ i).minFac = p := hp.pow_minFac (by omega)
  have hfac : (p ^ i).factorization p = i := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hp.factorization_self, mul_one]
  unfold primVal
  rw [if_pos hpp]
  dsimp only
  rw [hmf, hfac]

theorem primVal_zero_char {H : Type} [AddCommGroup H] (D : ArithData H)
    {p i : ℕ} (hp : p.Prime) (hi : 1 ≤ i) :
    primVal D (0 : AddChar (E0 × H) ℂ) (p ^ i) = 1 := by
  classical
  rw [primVal_primePow D 0 hp hi]
  simp

theorem norm_primVal_le_one {H : Type} [AddCommGroup H] [Fintype H] (D : ArithData H)
    (ψ : AddChar (E0 × H) ℂ) (n : ℕ) : ‖primVal D ψ n‖ ≤ 1 := by
  classical
  unfold primVal
  by_cases h1 : IsPrimePow n
  · rw [if_pos h1]
    dsimp only
    split_ifs
    · exact (addChar_norm_eq_one ψ _).le
    · simp
  · rw [if_neg h1]; simp

/-- Exact character-orthogonality kernel `Kc D n g = (1 / |Φ|) * ∑_ψ conj(ψ g) * primVal D ψ n`. -/
def Kc {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (D : ArithData H) (n : ℕ) (g : E0 × H) : ℂ :=
  (1 / ((PhiSet (H := H)).card : ℂ)) *
    ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) * primVal D ψ n

open Classical in
/-- Exact dual-group orthogonality with inertia subgroup `I`:
summing `conj(ψ g) * ψ h` over all characters `ψ` trivial on `I` detects the coset `g - h ∈ I`
with weight `|G| / |I|`. -/
theorem dual_orthogonality_subgroup {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (I : AddSubgroup G) (g h : G) :
    ∑ ψ : AddChar G ℂ,
        (if ∀ x ∈ I, ψ x = 1 then starRingEnd ℂ (ψ g) * ψ h else 0) =
      if g - h ∈ I then ((Fintype.card G : ℂ) / (Nat.card I : ℂ)) else 0 := by
  let qmap : G →+ G ⧸ I := QuotientAddGroup.mk' I
  have hqmap : Function.Surjective qmap := QuotientAddGroup.mk'_surjective I
  have hinj : Function.Injective (fun χ : AddChar (G ⧸ I) ℂ => χ.compAddMonoidHom qmap) := by
    intro χ₁ χ₂ heq
    ext q
    obtain ⟨x, rfl⟩ := hqmap q
    exact DFunLike.congr_fun heq x
  have himg : Finset.univ.filter (fun ψ : AddChar G ℂ => ∀ x ∈ I, ψ x = 1) =
      Finset.univ.image (fun χ : AddChar (G ⧸ I) ℂ => χ.compAddMonoidHom qmap) := by
    ext ψ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro htriv
      have wd : ∀ x y : G, qmap x = qmap y → ψ x = ψ y := fun x y hxy => by
        have hsub : x - y ∈ I := by
          rw [← QuotientAddGroup.eq_zero_iff]
          change qmap (x - y) = 0
          rw [map_sub, hxy, sub_self]
        calc ψ x = ψ (y + (x - y)) := by rw [add_sub_cancel]
          _ = ψ y * ψ (x - y) := AddChar.map_add_eq_mul ψ _ _
          _ = ψ y := by rw [htriv _ hsub, mul_one]
      let s := Function.surjInv hqmap
      have hs : ∀ q, qmap (s q) = q := Function.surjInv_eq hqmap
      refine ⟨{ toFun := fun q => ψ (s q)
                map_zero_eq_one' := by rw [wd (s 0) 0 (by rw [hs, map_zero]), AddChar.map_zero_eq_one]
                map_add_eq_mul' := fun a b => by
                  rw [← AddChar.map_add_eq_mul, wd (s (a + b)) (s a + s b) (by rw [hs, map_add, hs, hs])] }, ?_⟩
      ext x; exact wd _ _ (hs _)
    · rintro ⟨χ, rfl⟩ x hx
      show χ (qmap x) = 1
      have : qmap x = 0 := (QuotientAddGroup.eq_zero_iff x).mpr hx
      rw [this, AddChar.map_zero_eq_one]
  rw [← Finset.sum_filter, himg, Finset.sum_image (fun _ _ _ _ heq => hinj heq)]
  have hterm : ∀ χ : AddChar (G ⧸ I) ℂ,
      starRingEnd ℂ ((χ.compAddMonoidHom qmap) g) * (χ.compAddMonoidHom qmap) h =
        χ (qmap (h - g)) := fun χ => by
    change starRingEnd ℂ (χ (qmap g)) * χ (qmap h) = χ (qmap (h - g))
    have hinv : starRingEnd ℂ (χ (qmap g)) = χ (-qmap g) := by
      have hmul : χ (-qmap g) * χ (qmap g) = 1 := by
        rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
      have hnorm : ‖χ (qmap g)‖ = 1 := addChar_norm_eq_one χ (qmap g)
      have hconj : starRingEnd ℂ (χ (qmap g)) * χ (qmap g) = 1 := by
        rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm, one_pow, Complex.ofReal_one]
      have hne : χ (qmap g) ≠ 0 := fun hz => by rw [hz, norm_zero] at hnorm; exact zero_ne_one hnorm
      exact mul_right_cancel₀ hne (hconj.trans hmul.symm)
    rw [hinv, ← AddChar.map_add_eq_mul, map_sub, neg_add_eq_sub]
  simp_rw [hterm]
  have horth : ∑ χ : AddChar (G ⧸ I) ℂ, χ (qmap (h - g)) =
      if qmap (h - g) = 0 then (Fintype.card (G ⧸ I) : ℂ) else 0 := by
    by_cases h0 : qmap (h - g) = 0
    · rw [if_pos h0]
      simp [h0, AddChar.card_eq]
    · rw [if_neg h0]
      have hdu := Stage11SecondMomentFrame.addChar_orthogonality_dual (qmap (h - g)) 0
      rw [if_neg h0] at hdu
      simpa using hdu
  rw [horth]
  have hiff : qmap (h - g) = 0 ↔ g - h ∈ I := by
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    constructor
    · intro hm; simpa [neg_sub] using I.neg_mem hm
    · intro hm; simpa [neg_sub] using I.neg_mem hm
  have hlag : (Fintype.card (G ⧸ I) : ℂ) = (Fintype.card G : ℂ) / (Nat.card I : ℂ) := by
    have hnat : Fintype.card (G ⧸ I) * Nat.card I = Fintype.card G := by
      have h1 := AddSubgroup.index_mul_card I
      rw [AddSubgroup.index_eq_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h1
      simpa only [Nat.card_eq_fintype_card] using h1
    have hIpos : (Nat.card I : ℂ) ≠ 0 := by
      have : 0 < Nat.card I := Nat.card_pos_iff.mpr ⟨⟨0, I.zero_mem⟩, Finite.of_fintype _⟩
      exact_mod_cast this.ne'
    rw [eq_div_iff hIpos]
    exact_mod_cast hnat
  by_cases hmem : g - h ∈ I
  · rw [if_pos (hiff.mpr hmem), if_pos hmem, hlag]
  · rw [if_neg (fun hm => hmem (hiff.mp hm)), if_neg hmem]

open Classical in
/-- Exact ramified character orthogonality on `E0 × H`:
`Kc D (p^i) g = if g - i • D.frob p ∈ D.inertia p then 2 / |D.inertia p| else 0`. -/
theorem orthogonality_ramified {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (D : ArithData H) (p i : ℕ) (hp : p.Prime) (hi : 1 ≤ i) (g : E0 × H) :
    Kc D (p ^ i) g =
      if g - i • D.frob p ∈ D.inertia p then (2 : ℂ) / (Nat.card (D.inertia p) : ℂ) else 0 := by
  unfold Kc
  have hrew : ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) * primVal D ψ (p ^ i) =
      ∑ ψ : AddChar (E0 × H) ℂ,
        if ∀ x ∈ D.inertia p, ψ x = 1 then starRingEnd ℂ (ψ g) * ψ (i • D.frob p) else 0 := by
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [primVal_primePow D ψ hp hi]
    split_ifs <;> simp
  rw [hrew, dual_orthogonality_subgroup (D.inertia p) g (i • D.frob p)]
  have hphi_ne : ((PhiSet (H := H)).card : ℂ) ≠ 0 := by exact_mod_cast (phi_card_pos (H := H)).ne'
  split_ifs
  · rw [card_E0_prod]
    push_cast
    field_simp [hphi_ne]
  · simp

/-- Reindexing any von Mangoldt sum over `Icc 1 N` into primes `p ≤ N` and prime powers `p^i`. -/
theorem sum_vonMangoldt_primePow (N : ℕ) (F : ℕ → ℂ)
    (hF : ∀ p i : ℕ, p.Prime → 1 ≤ i → N < p ^ i → F (p ^ i) = 0) :
    ∑ n ∈ Finset.Icc 1 N, (Λ n : ℂ) * F n =
      ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
        ∑ i ∈ Finset.Icc 1 N, (Real.log p : ℂ) * F (p ^ i) := by
  classical
  let P := (Finset.range (N + 1)).filter Nat.Prime
  let S := (Finset.Icc 1 N).filter IsPrimePow
  have h1 : ∑ n ∈ Finset.Icc 1 N, (Λ n : ℂ) * F n = ∑ n ∈ S, (Λ n : ℂ) * F n := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun n hn hns => ?_
    have hnot : ¬ IsPrimePow n := fun hpp => hns (Finset.mem_filter.mpr ⟨hn, hpp⟩)
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnot, Complex.ofReal_zero, zero_mul]
  rw [h1]
  have h2 : ∑ p ∈ P, ∑ i ∈ Finset.Icc 1 N, (Real.log p : ℂ) * F (p ^ i) =
      ∑ p ∈ P, ∑ i ∈ (Finset.Icc 1 N).filter (fun i => p ^ i ≤ N), (Real.log p : ℂ) * F (p ^ i) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun i hi his => ?_
    have hgt : N < p ^ i := by
      by_contra hle; push Not at hle; exact his (Finset.mem_filter.mpr ⟨hi, hle⟩)
    rw [hF p i (Finset.mem_filter.mp hp).2 (Finset.mem_Icc.mp hi).1 hgt, mul_zero]
  rw [h2]
  have hsig :
      ∑ p ∈ P, ∑ i ∈ (Finset.Icc 1 N).filter (fun i => p ^ i ≤ N), (Real.log p : ℂ) * F (p ^ i) =
        ∑ x ∈ P.sigma (fun p => (Finset.Icc 1 N).filter (fun i => p ^ i ≤ N)),
          (Real.log x.1 : ℂ) * F (x.1 ^ x.2) :=
    (Finset.sum_sigma P (fun p => (Finset.Icc 1 N).filter (fun i => p ^ i ≤ N))
      (fun x => (Real.log x.1 : ℂ) * F (x.1 ^ x.2))).symm
  rw [hsig]
  refine Finset.sum_bij (fun n _ => ⟨n.minFac, n.factorization n.minFac⟩) ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hnI, hpp⟩ := Finset.mem_filter.mp hn
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    have hmf : (p ^ k).minFac = p := hp.pow_minFac (by omega)
    have hfac : (p ^ k).factorization p = k := by
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hp.factorization_self, mul_one]
    have hpkN : p ^ k ≤ N := (Finset.mem_Icc.mp hnI).2
    have hpN : p ≤ N := le_trans (Nat.le_self_pow (by omega) p) hpkN
    have hkN : k ≤ N := le_trans (Nat.lt_pow_self hp.one_lt (n := k)).le hpkN
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, P, hmf, hfac]
    exact ⟨⟨by omega, hp⟩, ⟨⟨by omega, hkN⟩, hpkN⟩⟩
  · intro a ha b hb heq
    obtain ⟨_, hppa⟩ := Finset.mem_filter.mp ha
    obtain ⟨_, hppb⟩ := Finset.mem_filter.mp hb
    obtain ⟨pa, ka, hpa, hka, rfl⟩ := (isPrimePow_nat_iff a).mp hppa
    obtain ⟨pb, kb, hpb, hkb, rfl⟩ := (isPrimePow_nat_iff b).mp hppb
    have hmfa : (pa ^ ka).minFac = pa := hpa.pow_minFac (by omega)
    have hmfb : (pb ^ kb).minFac = pb := hpb.pow_minFac (by omega)
    have hfaca : (pa ^ ka).factorization pa = ka := by
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hpa.factorization_self, mul_one]
    have hfacb : (pb ^ kb).factorization pb = kb := by
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hpb.factorization_self, mul_one]
    simp only [hmfa, hmfb, hfaca, hfacb, Sigma.mk.inj_iff, heq_eq_eq] at heq
    rw [heq.1, heq.2]
  · intro x hx
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, P] at hx
    obtain ⟨⟨_, hp⟩, ⟨⟨hi1, _⟩, hpiN⟩⟩ := hx
    refine ⟨x.1 ^ x.2, ?_, ?_⟩
    · simp only [S, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨Nat.one_le_pow _ _ hp.pos, hpiN⟩, (isPrimePow_nat_iff _).mpr ⟨x.1, x.2, hp, by omega, rfl⟩⟩
    · have hmf : (x.1 ^ x.2).minFac = x.1 := hp.pow_minFac (by omega)
      have hfac : (x.1 ^ x.2).factorization x.1 = x.2 := by
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hp.factorization_self, mul_one]
      ext
      · exact hmf
      · dsimp only; rw [hmf, hfac]
  · intro n hn
    obtain ⟨_, hpp⟩ := Finset.mem_filter.mp hn
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
    have hmf : (p ^ k).minFac = p := hp.pow_minFac (by omega)
    have hfac : (p ^ k).factorization p = k := by
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hp.factorization_self, mul_one]
    simp only [hmf, hfac, ArithmeticFunction.vonMangoldt_apply_pow (by omega : k ≠ 0),
      ArithmeticFunction.vonMangoldt_apply_prime hp]

open Classical in
/-- Subtracted Cesàro-1 character functional `GPsi D ell ψ y` on `E0 × H`. -/
def GPsi {H : Type} [AddCommGroup H] (D : ArithData H)
    (ell : AddChar (E0 × H) ℂ → ℂ) (ψ : AddChar (E0 × H) ℂ) (y : ℝ) : ℂ :=
  if ψ = 0 then (Gz y : ℂ)
  else (∑ n ∈ Finset.Icc 1 ⌊y⌋₊,
    (Λ n : ℂ) * primVal D ψ n * ((y / (n : ℝ) - 1 : ℝ) : ℂ)) + (y : ℂ) * ell ψ

/-- Inert-prime ramp contribution at a single prime `p`. -/
def askP {H : Type} [AddCommGroup H] (D : ArithData H) (N : ℕ) (a : ℝ) (t : H)
    (w : E0 × H → ℝ) (p : ℕ) : ℝ :=
  ∑ i ∈ (Finset.Icc 1 N).filter (fun i => ¬ InPhi (i • D.frob p)),
    max (a / (p : ℝ) ^ i - w (partner t (i • D.frob p))) 0

open Classical in
/-- Ramified-prime ramp contribution at `D.d`. -/
def askD {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (D : ArithData H) (N : ℕ) (a : ℝ) (t : H) (w : E0 × H → ℝ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 N,
    ∑ g ∈ (NotPhiSet (H := H)).filter (fun g => g - i • D.frob D.d ∈ D.inertia D.d),
      max (a / (D.d : ℝ) ^ i - w (partner t g)) 0

open Classical in
/-- Exact inert-prime von Mangoldt ramp sum `ASK D N a t w` over the splitting field `E(q, d)`. -/
def ASK {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (D : ArithData H) (N : ℕ) (a : ℝ) (t : H) (w : E0 × H → ℝ) : ℝ :=
  (∑ p ∈ (Finset.range (N + 1)).filter (IsInert D), 2 * Real.log p * askP D N a t w p) +
    Real.log D.d * askD D N a t w

/-- Exact main term `MAIN ell a w` extracted from the `ψ = 0` and `ψ = chC` Fourier modes. -/
def MAIN {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (ell : AddChar (E0 × H) ℂ → ℂ) (a : ℝ) (w : E0 × H → ℝ) : ℂ :=
  ((a * Real.log a - (1 + Real.eulerMascheroniConstant) * a -
    a / ((PhiSet (H := H)).card : ℝ) * ∑ ρ ∈ PhiSet (H := H), Real.log (w ρ) : ℝ) : ℂ) +
    (a : ℂ) * ell chC

/-- Exact oscillatory character-twist decomposition `De D ell a t w`. -/
def De {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (a : ℝ) (t : H) (w : E0 × H → ℝ) : ℂ :=
  (1 / ((PhiSet (H := H)).card : ℂ)) *
    ∑ g ∈ NotPhiSet (H := H),
      ∑ ψ : AddChar (E0 × H) ℂ,
        starRingEnd ℂ (ψ g) * ((w (partner t g) : ℂ) * GPsi D ell ψ (a / w (partner t g)))

private lemma max_zero_of_gt {H : Type} [AddCommGroup H] {a : ℝ} {t : H} {w : E0 × H → ℝ}
    {N : ℕ} {g : E0 × H} (hw : ∀ ρ, InPhi ρ → 0 < w ρ) (hN : ∀ ρ, InPhi ρ → a / w ρ ≤ N)
    (hg : ¬ InPhi g) {m : ℝ} (hm : (N : ℝ) < m) :
    max (a / m - w (partner t g)) 0 = 0 := by
  have hw0 : 0 < w (partner t g) := hw _ (partner_inPhi t hg)
  have hle : a / w (partner t g) ≤ N := hN _ (partner_inPhi t hg)
  have hm0 : 0 < m := lt_of_le_of_lt (Nat.cast_nonneg N) hm
  have hdiv : a / m ≤ w (partner t g) := by
    rw [div_le_iff₀ hm0]
    have ha : a ≤ (N : ℝ) * w (partner t g) := (div_le_iff₀ hw0).mp hle
    nlinarith
  exact max_eq_right (by linarith)

private lemma card_inertia_d {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (D : ArithData H) {S0 : Finset ℕ} (hD : HostFactsS D S0) :
    (Nat.card (D.inertia D.d) : ℂ) = 2 := by
  classical
  have hset : Finset.univ.filter (fun x : E0 × H => x ∈ D.inertia D.d) = {0, sgc0} := by
    ext x; simp [hD.inertia_d]
  have hne : (0 : E0 × H) ≠ sgc0 := by
    intro h
    have := congrArg (fun x : E0 × H => x.1.1) h
    simp [sgc0] at this
  have hcard : Nat.card (D.inertia D.d) = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hset, Finset.card_pair hne]
  rw [hcard]; norm_num

private lemma ask_fourier_expansion {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (D : ArithData H) {S0 : Finset ℕ} (hD : HostFactsS D S0)
    (a : ℝ) (t : H) (w : E0 × H → ℝ) (hw : ∀ ρ, InPhi ρ → 0 < w ρ)
    (N : ℕ) (hN : ∀ ρ, InPhi ρ → a / w ρ ≤ N) :
    (ASK D N a t w : ℂ) =
      (1 / ((PhiSet (H := H)).card : ℂ)) *
        ∑ g ∈ NotPhiSet (H := H),
          ∑ ψ : AddChar (E0 × H) ℂ,
            starRingEnd ℂ (ψ g) *
              ∑ n ∈ Finset.Icc 1 N,
                (Λ n : ℂ) * primVal D ψ n * ((max (a / (n : ℝ) - w (partner t g)) 0 : ℝ) : ℂ) := by
  classical
  let Fc : ℕ → E0 × H → ℂ := fun n g => ((max (a / (n : ℝ) - w (partner t g)) 0 : ℝ) : ℂ)
  have hswap :
      (1 / ((PhiSet (H := H)).card : ℂ)) *
          ∑ g ∈ NotPhiSet (H := H), ∑ ψ : AddChar (E0 × H) ℂ,
            starRingEnd ℂ (ψ g) * ∑ n ∈ Finset.Icc 1 N, (Λ n : ℂ) * primVal D ψ n * Fc n g =
        ∑ n ∈ Finset.Icc 1 N, (Λ n : ℂ) * ∑ g ∈ NotPhiSet (H := H), Kc D n g * Fc n g := by
    calc _ = ∑ g ∈ NotPhiSet (H := H), ∑ ψ : AddChar (E0 × H) ℂ, ∑ n ∈ Finset.Icc 1 N,
              (1 / ((PhiSet (H := H)).card : ℂ)) *
                (starRingEnd ℂ (ψ g) * ((Λ n : ℂ) * primVal D ψ n * Fc n g)) := by
            simp only [Finset.mul_sum]
      _ = ∑ g ∈ NotPhiSet (H := H), ∑ n ∈ Finset.Icc 1 N, ∑ ψ : AddChar (E0 × H) ℂ,
              (1 / ((PhiSet (H := H)).card : ℂ)) *
                (starRingEnd ℂ (ψ g) * ((Λ n : ℂ) * primVal D ψ n * Fc n g)) :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ n ∈ Finset.Icc 1 N, ∑ g ∈ NotPhiSet (H := H), ∑ ψ : AddChar (E0 × H) ℂ,
              (1 / ((PhiSet (H := H)).card : ℂ)) *
                (starRingEnd ℂ (ψ g) * ((Λ n : ℂ) * primVal D ψ n * Fc n g)) :=
            Finset.sum_comm
      _ = _ := by
            simp only [Kc, Finset.mul_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun g _ =>
              Finset.sum_congr rfl fun ψ _ => by ring
  rw [hswap]
  rw [sum_vonMangoldt_primePow N (fun n => ∑ g ∈ NotPhiSet (H := H), Kc D n g * Fc n g) (by
    intro p i hp hi hgt
    refine Finset.sum_eq_zero fun g hg => ?_
    have hg' := mem_NotPhiSet.mp hg
    dsimp only [Fc]
    rw [max_zero_of_gt hw hN hg' (by exact_mod_cast hgt : (N : ℝ) < ((p ^ i : ℕ) : ℝ))]
    simp)]
  let P := (Finset.range (N + 1)).filter Nat.Prime
  have hperP : ∀ p ∈ P,
      (∑ i ∈ Finset.Icc 1 N, (Real.log p : ℂ) *
          ∑ g ∈ NotPhiSet (H := H), Kc D (p ^ i) g * Fc (p ^ i) g) =
        (if IsInert D p then ((2 * Real.log p * askP D N a t w p : ℝ) : ℂ) else 0) +
        (if p = D.d then ((Real.log D.d * askD D N a t w : ℝ) : ℂ) else 0) := by
    intro p hpP
    have hp : p.Prime := (Finset.mem_filter.mp hpP).2
    by_cases hd : p = D.d
    · subst hd
      rw [if_neg (fun h => h.2.2.2.1 rfl), if_pos rfl, zero_add]
      unfold askD
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      congr 1
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [orthogonality_ramified D D.d i hD.d_prime hi1 g, card_inertia_d D hD]
      dsimp only [Fc]
      split_ifs <;> simp
    · rw [if_neg hd, add_zero]
      by_cases hS : p ∈ S0
      · rw [if_neg (fun h => h.2.2.2.2 (hD.split_frob p hS))]
        refine Finset.sum_eq_zero fun i hi => ?_
        have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
        rw [Finset.sum_eq_zero, mul_zero]
        intro g hg
        have hg' := mem_NotPhiSet.mp hg
        rw [orthogonality_ramified D p i hp hi1 g]
        have hnot : g - i • D.frob p ∉ D.inertia p := fun hm =>
          hg' (by
            have hx := hD.split_inertia p hS _ hm
            have hf := inPhi_nsmul (hD.split_frob p hS) i
            simpa using inPhi_add hx hf)
        rw [if_neg hnot, zero_mul]
      · have hp2 : p ≠ 2 := fun e => hS (e ▸ hD.two_mem)
        have hpq : p ≠ D.q1 := fun e => hS (e ▸ hD.q1_mem)
        have hunr : ∑ i ∈ Finset.Icc 1 N, (Real.log p : ℂ) *
            ∑ g ∈ NotPhiSet (H := H), Kc D (p ^ i) g * Fc (p ^ i) g =
            ((2 * Real.log p * askP D N a t w p : ℝ) : ℂ) := by
          have hR : ((2 * Real.log p * askP D N a t w p : ℝ) : ℂ) =
              ∑ i ∈ Finset.Icc 1 N,
                if ¬ InPhi (i • D.frob p) then
                  2 * (Real.log p : ℂ) * Fc (p ^ i) (i • D.frob p)
                else 0 := by
            unfold askP
            rw [Finset.sum_filter, Finset.mul_sum]
            push_cast
            refine Finset.sum_congr rfl fun i _ => ?_
            dsimp only [Fc]
            split_ifs <;> simp
          rw [hR]
          refine Finset.sum_congr rfl fun i hi => ?_
          have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
          have hK : ∀ g : E0 × H, Kc D (p ^ i) g = if i • D.frob p = g then 2 else 0 := fun g => by
            rw [orthogonality_ramified D p i hp hi1 g, hD.unram p hp hS hd]
            by_cases he : i • D.frob p = g
            · rw [if_pos he, if_pos (by rw [he, sub_self]; exact AddSubgroup.zero_mem _)]
              have hbot : Nat.card (⊥ : AddSubgroup (E0 × H)) = 1 := by
                rw [Nat.card_eq_fintype_card]; exact Fintype.card_unique
              rw [hbot]; norm_num
            · rw [if_neg he, if_neg (by rw [AddSubgroup.mem_bot, sub_eq_zero]; exact fun e => he e.symm)]
          simp only [hK, ite_mul, zero_mul]
          rw [Finset.sum_ite_eq]
          by_cases hnp : ¬ InPhi (i • D.frob p)
          · rw [if_pos (mem_NotPhiSet.mpr hnp), if_pos hnp]; ring
          · rw [if_neg (fun hm => hnp (mem_NotPhiSet.mp hm)), if_neg hnp, mul_zero]
        rw [hunr]
        by_cases hin : IsInert D p
        · rw [if_pos hin]
        · rw [if_neg hin]
          have hphi : InPhi (D.frob p) := by
            by_contra hc; exact hin ⟨hp, hp2, hpq, hd, hc⟩
          have hask0 : askP D N a t w p = 0 := by
            unfold askP
            refine Finset.sum_eq_zero fun i hi =>
              absurd (inPhi_nsmul hphi i) (Finset.mem_filter.mp hi).2
          rw [hask0]; simp
  rw [Finset.sum_congr rfl hperP, Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_ite_eq']
  have hfilt : (Finset.range (N + 1)).filter (IsInert D) = P.filter (IsInert D) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun p _ => ⟨fun h => ⟨h.1, h⟩, fun h => h.2⟩
  unfold ASK
  rw [hfilt]
  push_cast
  congr 1
  by_cases hdP : D.d ∈ P
  · rw [if_pos hdP]
  · rw [if_neg hdP]
    have hdN : N < D.d := by
      by_contra hle; push Not at hle
      exact hdP (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hD.d_prime⟩)
    have haskD0 : askD D N a t w = 0 := by
      unfold askD
      refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun g hg => ?_
      have hg' := mem_NotPhiSet.mp (Finset.mem_filter.mp hg).1
      have h1 : (D.d : ℝ) ≤ (D.d : ℝ) ^ i := by
        have hd1 : (1 : ℝ) ≤ D.d := by exact_mod_cast hD.d_prime.one_lt.le
        calc (D.d : ℝ) = (D.d : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (D.d : ℝ) ^ i := pow_le_pow_right₀ hd1 (Finset.mem_Icc.mp hi).1
      exact max_zero_of_gt hw hN hg' (lt_of_lt_of_le (by exact_mod_cast hdN) h1)
    rw [haskD0]; simp

open Classical in
private lemma inner_ramp_eq_GPsi {H : Type} [AddCommGroup H]
    (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (ψ : AddChar (E0 × H) ℂ)
    (N : ℕ) (a W : ℝ) (ha : 0 < a) (hW : 0 < W) (hN : a / W ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, (Λ n : ℂ) * primVal D ψ n * ((max (a / (n : ℝ) - W) 0 : ℝ) : ℂ) =
      (W : ℂ) * GPsi D ell ψ (a / W) +
        if ψ = 0 then
          ((a * Real.log a - a * Real.log W - (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ)
        else -(a : ℂ) * ell ψ := by
  have hflN : ⌊a / W⌋₊ ≤ N := Nat.floor_le_of_le hN
  have hcut :
      ∑ n ∈ Finset.Icc 1 N, (Λ n : ℂ) * primVal D ψ n * ((max (a / (n : ℝ) - W) 0 : ℝ) : ℂ) =
        (W : ℂ) * ∑ n ∈ Finset.Icc 1 ⌊a / W⌋₊,
          (Λ n : ℂ) * primVal D ψ n * (((a / W) / (n : ℝ) - 1 : ℝ) : ℂ) := by
    rw [Finset.mul_sum]
    have hsub : Finset.Icc 1 ⌊a / W⌋₊ ⊆ Finset.Icc 1 N := Finset.Icc_subset_Icc_right hflN
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun n hn => ?_
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hn_le : (n : ℝ) ≤ a / W :=
        (by exact_mod_cast (Finset.mem_Icc.mp hn).2 : (n : ℝ) ≤ (⌊a / W⌋₊ : ℝ)).trans
          (Nat.floor_le (div_nonneg ha.le hW.le))
      have hge0 : 0 ≤ a / (n : ℝ) - W := by
        have h1 : W * (n : ℝ) ≤ a := by
          have := mul_le_mul_of_nonneg_left hn_le hW.le
          rwa [mul_div_cancel₀ _ hW.ne'] at this
        have h2 : W ≤ a / (n : ℝ) := (le_div_iff₀ hn_pos).mpr (by linarith)
        linarith
      rw [max_eq_left hge0]
      have halg : a / (n : ℝ) - W = W * ((a / W) / (n : ℝ) - 1) := by
        field_simp [hW.ne', hn_pos.ne']
      rw [halg]
      push_cast
      ring
    · intro n hn hnot
      have hgt : ⌊a / W⌋₊ < n := by
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        by_contra hle; push Not at hle
        exact hnot (Finset.mem_Icc.mpr ⟨hn1, hle⟩)
      have hlt : a / W < (n : ℝ) :=
        lt_of_lt_of_le (Nat.lt_floor_add_one (a / W)) (by exact_mod_cast hgt)
      have hn_pos : (0 : ℝ) < (n : ℝ) := lt_trans (div_pos ha hW) hlt
      have hle0 : a / (n : ℝ) - W ≤ 0 := by
        have h1 : a < (n : ℝ) * W := (div_lt_iff₀ hW).mp hlt
        have h2 : a / (n : ℝ) ≤ W := (div_le_iff₀ hn_pos).mpr (by linarith)
        linarith
      rw [max_eq_right hle0]
      simp
  rw [hcut]
  by_cases h0 : ψ = 0
  · subst h0
    rw [if_pos rfl]
    unfold GPsi
    rw [if_pos rfl]
    have hramp_eq :
        ∑ n ∈ Finset.Icc 1 ⌊a / W⌋₊,
          (Λ n : ℂ) * primVal D 0 n * (((a / W) / (n : ℝ) - 1 : ℝ) : ℂ) =
        ((ramp (fun _ => 1) (a / W)).re : ℂ) := by
      unfold ramp
      have hre : (∑ n ∈ Finset.range (⌊a / W⌋₊ + 1),
          (Λ n : ℂ) * 1 * ((max ((a / W) / (n : ℝ) - 1) 0 : ℝ) : ℂ)).re =
          ∑ n ∈ Finset.Icc 1 ⌊a / W⌋₊, Λ n * ((a / W) / (n : ℝ) - 1) := by
        rw [Complex.re_sum]
        have hsplit : Finset.range (⌊a / W⌋₊ + 1) = insert 0 (Finset.Icc 1 ⌊a / W⌋₊) := by
          ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
        rw [hsplit, Finset.sum_insert (by simp)]
        simp only [ArithmeticFunction.map_zero, Complex.ofReal_zero, zero_mul, Complex.zero_re, zero_add]
        refine Finset.sum_congr rfl fun n hn => ?_
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
        have hn_le : (n : ℝ) ≤ a / W :=
          (by exact_mod_cast (Finset.mem_Icc.mp hn).2 : (n : ℝ) ≤ (⌊a / W⌋₊ : ℝ)).trans
            (Nat.floor_le (div_nonneg ha.le hW.le))
        have hge : 0 ≤ (a / W) / (n : ℝ) - 1 := by
          rw [sub_nonneg, one_le_div hn_pos]; exact hn_le
        rw [mul_one, max_eq_left hge, ← Complex.ofReal_mul, Complex.ofReal_re]
      rw [hre, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      by_cases hpp : IsPrimePow n
      · obtain ⟨p, i, hp, hi, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
        rw [primVal_zero_char D hp (by omega), mul_one, ← Complex.ofReal_mul]
      · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]
        simp
    rw [hramp_eq]
    unfold Gz
    rw [Real.log_div ha.ne' hW.ne']
    push_cast
    field_simp [hW.ne']
    ring
  · rw [if_neg h0]
    unfold GPsi
    rw [if_neg h0]
    have hWa : (W : ℂ) * ((a / W : ℝ) : ℂ) = (a : ℂ) := by
      push_cast; field_simp [hW.ne']
    calc (W : ℂ) * ∑ n ∈ Finset.Icc 1 ⌊a / W⌋₊,
            (Λ n : ℂ) * primVal D ψ n * (((a / W) / (n : ℝ) - 1 : ℝ) : ℂ)
        = (W : ℂ) * ((∑ n ∈ Finset.Icc 1 ⌊a / W⌋₊,
            (Λ n : ℂ) * primVal D ψ n * (((a / W) / (n : ℝ) - 1 : ℝ) : ℂ)) +
            ((a / W : ℝ) : ℂ) * ell ψ) - (a : ℂ) * ell ψ := by
            rw [mul_add, ← mul_assoc, hWa]; ring
      _ = _ := by ring

/-- **UNCONDITIONAL EXACT GALOIS FOURIER INVERSION (`ch_balance`, `0` ASSUMPTIONS!)**:
for EVERY finite abelian group `H`, EVERY splitting-field datum `D : ArithData H` satisfying
`HostFactsS D S0`, EVERY `ell`, `a > 0`, `t : H`, positive weights `w` on `PhiSet`, and cutoff
`N ≥ a / w ρ`, the exact inert-prime ramp sum minus the main term equals the oscillatory
character-twist sum:
`(ASK D N a t w : ℂ) - MAIN ell a w = De D ell a t w`. -/
theorem ch_balance {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (D : ArithData H) (S0 : Finset ℕ) (hD : HostFactsS D S0)
    (ell : AddChar (E0 × H) ℂ → ℂ) (a : ℝ) (t : H) (w : E0 × H → ℝ)
    (ha : 0 < a) (hw : ∀ ρ, InPhi ρ → 0 < w ρ)
    (N : ℕ) (hN : ∀ ρ, InPhi ρ → a / w ρ ≤ N) :
    (ASK D N a t w : ℂ) - MAIN ell a w = De D ell a t w := by
  classical
  have hf0 : ((PhiSet (H := H)).card : ℂ) ≠ 0 := by exact_mod_cast (phi_card_pos (H := H)).ne'
  rw [ask_fourier_expansion D hD a t w hw N hN]
  have hin : ∀ g ∈ NotPhiSet (H := H), ∀ ψ : AddChar (E0 × H) ℂ,
      starRingEnd ℂ (ψ g) *
          ∑ n ∈ Finset.Icc 1 N,
            (Λ n : ℂ) * primVal D ψ n * ((max (a / (n : ℝ) - w (partner t g)) 0 : ℝ) : ℂ) =
        starRingEnd ℂ (ψ g) * ((w (partner t g) : ℂ) * GPsi D ell ψ (a / w (partner t g))) +
        starRingEnd ℂ (ψ g) * (if ψ = 0 then
          ((a * Real.log a - a * Real.log (w (partner t g)) -
            (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ)
          else -(a : ℂ) * ell ψ) := by
    intro g hg ψ
    have hg' := mem_NotPhiSet.mp hg
    have hW := hw _ (partner_inPhi t hg')
    rw [inner_ramp_eq_GPsi D ell ψ N a _ ha hW (hN _ (partner_inPhi t hg')), mul_add]
  rw [Finset.sum_congr rfl fun g hg => Finset.sum_congr rfl fun ψ _ => hin g hg ψ]
  simp only [Finset.sum_add_distrib, mul_add]
  have hDe : (1 / ((PhiSet (H := H)).card : ℂ)) *
      ∑ g ∈ NotPhiSet (H := H), ∑ ψ : AddChar (E0 × H) ℂ,
        starRingEnd ℂ (ψ g) * ((w (partner t g) : ℂ) * GPsi D ell ψ (a / w (partner t g))) =
      De D ell a t w := rfl
  rw [hDe]
  have hsplit : ∀ g : E0 × H,
      (∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) * (if ψ = 0 then
        ((a * Real.log a - a * Real.log (w (partner t g)) -
          (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ)
        else -(a : ℂ) * ell ψ)) =
      ((a * Real.log a - a * Real.log (w (partner t g)) -
        (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ) +
      ∑ ψ ∈ Finset.univ.erase (0 : AddChar (E0 × H) ℂ),
        starRingEnd ℂ (ψ g) * (-(a : ℂ) * ell ψ) := by
    intro g
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : AddChar (E0 × H) ℂ)),
      if_pos rfl, AddChar.zero_apply, map_one, one_mul]
    congr 1
    refine Finset.sum_congr rfl fun ψ hψ => by rw [if_neg (Finset.ne_of_mem_erase hψ)]
  have hcol :
      (∑ g ∈ NotPhiSet (H := H),
        ∑ ψ ∈ Finset.univ.erase (0 : AddChar (E0 × H) ℂ),
          starRingEnd ℂ (ψ g) * (-(a : ℂ) * ell ψ)) =
      ((PhiSet (H := H)).card : ℂ) * ((a : ℂ) * ell chC) := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun ψ hψ => by
      rw [← Finset.sum_mul, colour_sum ψ, if_neg (Finset.ne_of_mem_erase hψ)]]
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_erase.mpr ⟨chC_ne_zero (H := H), Finset.mem_univ _⟩)]
    ring
  have hreal :
      (∑ g ∈ NotPhiSet (H := H),
        ((a * Real.log a - a * Real.log (w (partner t g)) -
          (1 + Real.eulerMascheroniConstant) * a : ℝ) : ℂ)) =
      ((((PhiSet (H := H)).card : ℝ) * (a * Real.log a - (1 + Real.eulerMascheroniConstant) * a) -
        a * ∑ ρ ∈ PhiSet (H := H), Real.log (w ρ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sum]
    congr 1
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
      card_notPhi, ← Finset.mul_sum, sum_partner t (fun ρ => Real.log (w ρ))]
    simp only [nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun g _ => hsplit g, Finset.sum_add_distrib, hreal, hcol]
  unfold MAIN
  push_cast
  field_simp [hf0]
  ring

/-- Canonical `Fin 2 × Fin 2` quadratic-twist character `e0Char i j : AddChar E0 ℂ` sending
`(u, v) ∈ ZMod 2 × ZMod 2` to `(-1)^(i * u + j * v)`. -/
def e0Char (i j : Fin 2) : AddChar E0 ℂ where
  toFun := fun x =>
    (if i.val = 1 ∧ x.1 = 1 then (-1 : ℂ) else 1) *
    (if j.val = 1 ∧ x.2 = 1 then (-1 : ℂ) else 1)
  map_zero_eq_one' := by simp
  map_add_eq_mul' := fun a b => by
    rcases zmod2_cases a.1 with h1 | h1 <;> rcases zmod2_cases a.2 with h2 | h2 <;>
    rcases zmod2_cases b.1 with h3 | h3 <;> rcases zmod2_cases b.2 with h4 | h4 <;>
    fin_cases i <;> fin_cases j <;>
    simp [h1, h2, h3, h4, zmod2_one_add_one]

/-- Pair a quadratic-twist index `(i, j) : Fin 2 × Fin 2` with a character `η : AddChar H ℂ`. -/
def prodAddChar {H : Type} [AddCommGroup H] (i j : Fin 2) (η : AddChar H ℂ) :
    AddChar (E0 × H) ℂ where
  toFun := fun g => e0Char i j g.1 * η g.2
  map_zero_eq_one' := by simp
  map_add_eq_mul' := fun a b => by
    simp only [Prod.fst_add, Prod.snd_add, AddChar.map_add_eq_mul]
    ring

theorem prodAddChar_bijective {H : Type} [AddCommGroup H] :
    Function.Bijective (fun p : (Fin 2 × Fin 2) × AddChar H ℂ => prodAddChar p.1.1 p.1.2 p.2) := by
  constructor
  · rintro ⟨⟨i₁, j₁⟩, η₁⟩ ⟨⟨i₂, j₂⟩, η₂⟩ heq
    have hη : η₁ = η₂ := by
      ext h
      have := DFunLike.congr_fun heq ((0, 0), h)
      simpa [prodAddChar, e0Char] using this
    have hi : i₁ = i₂ := by
      have hval := DFunLike.congr_fun heq ((1, 0), 0)
      simp only [prodAddChar, e0Char] at hval
      fin_cases i₁ <;> fin_cases i₂ <;> simp at hval ⊢ <;> norm_num at hval
    have hj : j₁ = j₂ := by
      have hval := DFunLike.congr_fun heq ((0, 1), 0)
      simp only [prodAddChar, e0Char] at hval
      fin_cases j₁ <;> fin_cases j₂ <;> simp at hval ⊢ <;> norm_num at hval
    rw [hi, hj, hη]
  · intro ψ
    have h10 : ψ ((1, 0), 0) = 1 ∨ ψ ((1, 0), 0) = -1 := by
      have hsq : ψ ((1, 0), 0) * ψ ((1, 0), 0) = 1 := by
        rw [← AddChar.map_add_eq_mul]
        have h2 : (((1, 0) : E0), (0 : H)) + (((1, 0) : E0), (0 : H)) = 0 := by
          ext
          · exact zmod2_one_add_one
          · simp
          · simp
        rw [h2, AddChar.map_zero_eq_one]
      exact mul_self_eq_one_iff.mp hsq
    have h01 : ψ ((0, 1), 0) = 1 ∨ ψ ((0, 1), 0) = -1 := by
      have hsq : ψ ((0, 1), 0) * ψ ((0, 1), 0) = 1 := by
        rw [← AddChar.map_add_eq_mul]
        have h2 : (((0, 1) : E0), (0 : H)) + (((0, 1) : E0), (0 : H)) = 0 := by
          ext
          · simp
          · exact zmod2_one_add_one
          · simp
        rw [h2, AddChar.map_zero_eq_one]
      exact mul_self_eq_one_iff.mp hsq
    let i : Fin 2 := if ψ ((1, 0), 0) = 1 then 0 else 1
    let j : Fin 2 := if ψ ((0, 1), 0) = 1 then 0 else 1
    let η : AddChar H ℂ :=
      { toFun := fun h => ψ ((0, 0), h)
        map_zero_eq_one' := ψ.map_zero_eq_one
        map_add_eq_mul' := fun a b => by
          have : (((0, 0) : E0), a + b) = (((0, 0) : E0), a) + (((0, 0) : E0), b) := by
            ext <;> simp
          rw [this, AddChar.map_add_eq_mul] }
    refine ⟨((i, j), η), ?_⟩
    ext ⟨⟨u, v⟩, h⟩
    have hdec : (((u, v) : E0), h) =
        (((u, 0) : E0), (0 : H)) + (((0, v) : E0), (0 : H)) + (((0, 0) : E0), h) := by
      ext <;> simp
    have h00 : ψ (((0, 0) : E0), (0 : H)) = 1 := ψ.map_zero_eq_one
    have hrhs : ψ (((u, v) : E0), h) =
        ψ (((u, 0) : E0), (0 : H)) * ψ (((0, v) : E0), (0 : H)) * ψ (((0, 0) : E0), h) := by
      rw [hdec, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
    rw [hrhs]
    change e0Char i j (u, v) * ψ ((0, 0), h) = _
    have hne : (-1 : ℂ) ≠ 1 := by norm_num
    rcases h10 with h1 | h1 <;> rcases h01 with h2 | h2 <;>
    rcases zmod2_cases u with rfl | rfl <;> rcases zmod2_cases v with rfl | rfl <;>
    simp [e0Char, i, j, h1, h2, h00, hne]

/-- **Concrete Quadratic-Pair Splitting-Field `ArithData` (`quadPairArithData`)**:
attaches to an auxiliary prime pair `(q, d)` and any base Frobenius map `fH : ℕ → H` the
splitting-field Frobenius on `E0 × H` whose first coordinate detects `(p | d) = -1` (inert in
`ℚ(√(-d))`), second coordinate detects `(p | q) = -1`, and inertia is `{0, sgc0}` at `d` and `⊥`
at all primes outside `S0 ∪ {d}`. -/
def quadPairArithData {H : Type} [AddCommGroup H] (q d : ℕ) (S0 : Finset ℕ) (fH : ℕ → H) :
    ArithData H where
  frob := fun p =>
    if p ∈ S0 then ((0, 0), fH p)
    else
      ((if jacobiSym (p : ℤ) d = -1 then (1 : ZMod 2) else 0,
        if jacobiSym (p : ℤ) q = -1 then (1 : ZMod 2) else 0), fH p)
  inertia := fun p =>
    if p = d then AddSubgroup.zmultiples (sgc0 (H := H)) else ⊥
  q1 := q
  d := d

theorem quadPairArithData_hostFactsS {H : Type} [AddCommGroup H]
    (q d : ℕ) (S0 : Finset ℕ) (fH : ℕ → H)
    (hd : d.Prime) (h2 : 2 ∈ S0) (hq : q ∈ S0) (hdS : d ∉ S0) :
    HostFactsS (quadPairArithData q d S0 fH) S0 where
  d_prime := hd
  two_mem := h2
  q1_mem := hq
  d_not_mem := hdS
  unram := fun p _ _ hpd => by
    change (if p = d then AddSubgroup.zmultiples (sgc0 (H := H)) else ⊥) = ⊥
    exact if_neg hpd
  split_frob := fun p hp => by simp [quadPairArithData, InPhi, hp]
  split_inertia := fun p hp x hx => by
    have hpd : p ≠ d := fun e => hdS (e ▸ hp)
    simp only [quadPairArithData, if_neg hpd, AddSubgroup.mem_bot] at hx
    subst hx; exact inPhi_zero
  inertia_d := fun x => by
    change x ∈ (if d = d then AddSubgroup.zmultiples (sgc0 (H := H)) else ⊥) ↔ x = 0 ∨ x = sgc0
    rw [if_pos rfl, AddSubgroup.mem_zmultiples_iff]
    constructor
    · rintro ⟨k, rfl⟩
      rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
      · left
        change (m + m) • sgc0 (H := H) = 0
        rw [show (m + m) • sgc0 (H := H) = m • (sgc0 + sgc0) by rw [add_zsmul, zsmul_add],
          sgc0_add_self, smul_zero]
      · right
        change (2 * m + 1) • sgc0 (H := H) = sgc0
        rw [add_zsmul, one_zsmul, show (2 * m) • sgc0 (H := H) = m • (sgc0 + sgc0) by
          rw [mul_comm, mul_zsmul, two_zsmul], sgc0_add_self, smul_zero, zero_add]
    · rintro (rfl | rfl)
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩

/-- **Exact `Fin 2 × Fin 2` Quadratic-Twist Decomposition of `ASK - MAIN` (`ch_balance_quadPair`)**:
splits `De` explicitly into the `(0, 0)` un-twisted part plus the three off-diagonal quadratic
twists `(i, j) ∈ Fin 2 × Fin 2` (`(i, j) ≠ (0, 0)`) for `(χ_d, χ_q)`. -/
theorem ch_balance_quadPair {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (D : ArithData H) (S0 : Finset ℕ) (hD : HostFactsS D S0)
    (ell : AddChar (E0 × H) ℂ → ℂ) (a : ℝ) (t : H) (w : E0 × H → ℝ)
    (ha : 0 < a) (hw : ∀ ρ, InPhi ρ → 0 < w ρ)
    (N : ℕ) (hN : ∀ ρ, InPhi ρ → a / w ρ ≤ N) :
    (ASK D N a t w : ℂ) - MAIN ell a w =
      (1 / ((PhiSet (H := H)).card : ℂ)) *
        ∑ g ∈ NotPhiSet (H := H),
          (∑ η : AddChar H ℂ,
            starRingEnd ℂ (prodAddChar 0 0 η g) *
              ((w (partner t g) : ℂ) * GPsi D ell (prodAddChar 0 0 η) (a / w (partner t g)))) +
      (1 / ((PhiSet (H := H)).card : ℂ)) *
        ∑ g ∈ NotPhiSet (H := H),
          ∑ ij ∈ (Finset.univ : Finset (Fin 2 × Fin 2)).erase (0, 0),
            ∑ η : AddChar H ℂ,
              starRingEnd ℂ (prodAddChar ij.1 ij.2 η g) *
                ((w (partner t g) : ℂ) * GPsi D ell (prodAddChar ij.1 ij.2 η) (a / w (partner t g))) := by
  classical
  rw [ch_balance D S0 hD ell a t w ha hw N hN]
  unfold De
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  let e : (Fin 2 × Fin 2) × AddChar H ℂ ≃ AddChar (E0 × H) ℂ :=
    Equiv.ofBijective _ prodAddChar_bijective
  rw [← Equiv.sum_comp e, Fintype.sum_prod_type]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ((0 : Fin 2), (0 : Fin 2)))]
  rfl

/-! ## Section 2: Unconditional Coset-Average Bridge (`ch_core`, `sigA_le`, `core_gm`) -/

open Classical in
/-- Annihilator `PsiA A0 ⊆ AddChar (E0 × H) ℂ` of characters trivial on `0 × A0`. -/
def PsiA {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (A0 : AddSubgroup H) : Finset (AddChar (E0 × H) ℂ) :=
  Finset.univ.filter fun ψ : AddChar (E0 × H) ℂ => ∀ s ∈ A0, ψ (0, s) = 1

theorem mem_PsiA {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    {A0 : AddSubgroup H} {ψ : AddChar (E0 × H) ℂ} :
    ψ ∈ PsiA A0 ↔ ∀ s ∈ A0, ψ (0, s) = 1 := by
  classical
  simp [PsiA]

theorem card_PsiA (φ : CosetFrame) : (PsiA φ.A0).card = 4 * φ.o := by
  classical
  let e : (Fin 2 × Fin 2) × AddChar φ.A ℂ ≃ AddChar (E0 × φ.A) ℂ :=
    Equiv.ofBijective _ prodAddChar_bijective
  have hmem : ∀ p : (Fin 2 × Fin 2) × AddChar φ.A ℂ,
      e p ∈ PsiA φ.A0 ↔ p.2 ∈ φ.annihilator := fun ⟨⟨i, j⟩, η⟩ => by
    rw [mem_PsiA, φ.mem_annihilator]
    simp [e, prodAddChar, e0Char]
  have himg : PsiA φ.A0 =
      ((Finset.univ : Finset (Fin 2 × Fin 2)) ×ˢ φ.annihilator).image e := by
    ext ψ
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_univ, true_and]
    constructor
    · intro hψ
      refine ⟨e.symm ψ, ?_, e.apply_symm_apply ψ⟩
      rw [← hmem, e.apply_symm_apply]
      exact hψ
    · rintro ⟨p, hp, rfl⟩
      exact (hmem p).mpr hp
  rw [himg, Finset.card_image_of_injective _ e.injective, Finset.card_product,
    Finset.card_univ, Fintype.card_prod, Fintype.card_fin, φ.card_annihilator]

/-- Thick-place density `delta2 T2 = |T2| / |H|`. -/
def delta2 {H : Type} [Fintype H] (T2 : Finset H) : ℝ :=
  (T2.card : ℝ) / (Fintype.card H : ℝ)

/-- Slope-engine gap sum `gapA` across `t ∈ TT` and chain steps `j : Fin m`. -/
def gapA {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {m : ℕ}
    (D : ArithData H) (N : ℕ) (ell : AddChar (E0 × H) ℂ → ℂ)
    (TT : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ) (u0 : H) : ℝ :=
  ∑ t ∈ TT, ∑ j : Fin m, (ASK D N (a t) t (w u0 j) - (MAIN ell (a t) (w u0 j)).re)

/-- Thick-place projection `Th D ell T2 b y u0 t` (restricting `De` to `partner t g` in the
thick slice `0 × (u0 + T2)` with constant weight `b`). -/
def Th {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ) (T2 : Finset H)
    (b y : ℝ) (u0 t : H) : ℂ :=
  (1 / ((PhiSet (H := H)).card : ℂ)) *
    ∑ g ∈ (NotPhiSet (H := H)).filter (fun g => (partner t g).1.2 = 0 ∧ (partner t g).2 - u0 ∈ T2),
      ∑ ψ : AddChar (E0 × H) ℂ, starRingEnd ℂ (ψ g) * ((b : ℂ) * GPsi D ell ψ y)

open Classical in
/-- Kept-character weighted sum `GmA` on `E0 × H`. -/
def GmA {H : Type} [AddCommGroup H] (D : ArithData H)
    (ell : AddChar (E0 × H) ℂ → ℂ) (Kp : Finset (AddChar (E0 × H) ℂ))
    (c y : ℝ) : ℝ :=
  ∑ ψ ∈ Kp, (if ψ = 0 then (1 : ℝ) else c) * (GPsi D ell ψ y).re

open Classical in
/-- Off-kept character error norm `SigA` on `PsiA A0 \ Kp`. -/
def SigA {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ)
    (A0 : AddSubgroup H) (Kp : Finset (AddChar (E0 × H) ℂ)) (y : ℝ) : ℝ :=
  ∑ ψ ∈ PsiA A0 \ Kp, ‖GPsi D ell ψ y‖

/-- **Exact Coset-Averaging Cancellation (`sum_Th`)**:
averaging `Th D ell T2 b y u0 t` over `u0 ∈ A0` annihilates all characters outside `PsiA A0`
and isolates `|A0| * b * (delta2 T2 / 2) * ∑_{ψ ∈ PsiA A0} ψ ((1, 0), t) * GPsi D ell ψ y`! -/
theorem sum_Th {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (A0 : AddSubgroup H) [Fintype A0] (D : ArithData H) (ell : AddChar (E0 × H) ℂ → ℂ)
    (T2 : Finset H) (hT2 : ∀ s ∈ T2, s ∈ A0) (b y : ℝ) (t : H) :
    ∑ u : A0, Th D ell T2 b y u.1 t =
      (((Fintype.card A0 : ℝ) * (b * (delta2 T2 / 2)) : ℝ) : ℂ) *
        ∑ ψ ∈ PsiA A0, ψ ((1, 0), t) * GPsi D ell ψ y := by
  classical
  have hH_ne : (Fintype.card H : ℂ) ≠ 0 := by
    have : 0 < Fintype.card H := Fintype.card_pos_iff.mpr ⟨0⟩
    exact_mod_cast this.ne'
  have hinner : ∀ u : A0,
      Th D ell T2 b y u.1 t =
        (1 / ((PhiSet (H := H)).card : ℂ)) *
          ∑ ψ : AddChar (E0 × H) ℂ,
            (∑ s ∈ T2, starRingEnd ℂ (ψ ((1, 0), u.1 + s - t))) * ((b : ℂ) * GPsi D ell ψ y) := by
    intro u
    unfold Th
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ψ _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_bij (fun g _ => (partner t g).2 - u.1) ?_ ?_ ?_ ?_
    · intro g hg; exact (Finset.mem_filter.mp hg).2.2
    · intro g₁ hg₁ g₂ hg₂ heq
      have h1 := Finset.mem_filter.mp hg₁
      have h2 := Finset.mem_filter.mp hg₂
      have hg1_1 : g₁.1.1 = 1 := zmod2_eq_one_of_ne_zero (mem_NotPhiSet.mp h1.1)
      have hg2_1 : g₂.1.1 = 1 := zmod2_eq_one_of_ne_zero (mem_NotPhiSet.mp h2.1)
      have hg1_2 : g₁.1.2 = 0 := h1.2.1
      have hg2_2 : g₂.1.2 = 0 := h2.2.1
      have hsnd : g₁.2 = g₂.2 := by
        dsimp only [partner] at heq
        exact add_right_cancel (sub_left_inj.mp heq)
      ext
      · rw [hg1_1, hg2_1]
      · rw [hg1_2, hg2_2]
      · exact hsnd
    · intro s hs
      refine ⟨((1, 0), u.1 + s - t), ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨mem_NotPhiSet.mpr (show (1 : ZMod 2) ≠ 0 by decide), ?_, ?_⟩
        · rfl
        · simp [partner, hs]
      · simp [partner]
    · intro g hg
      have h1 := Finset.mem_filter.mp hg
      have hg1 : g.1.1 = 1 := zmod2_eq_one_of_ne_zero (mem_NotPhiSet.mp h1.1)
      have hg2 : g.1.2 = 0 := h1.2.1
      have heq : g = ((1, 0), u.1 + ((partner t g).2 - u.1) - t) := by
        ext
        · exact hg1
        · exact hg2
        · simp [partner]
      conv_lhs => rw [heq]
  rw [Finset.sum_congr rfl fun u _ => hinner u, ← Finset.mul_sum, Finset.sum_comm]
  have hchar : ∀ ψ : AddChar (E0 × H) ℂ,
      ∑ u : A0, (∑ s ∈ T2, starRingEnd ℂ (ψ ((1, 0), u.1 + s - t))) * ((b : ℂ) * GPsi D ell ψ y) =
        if ψ ∈ PsiA A0 then
          ((Fintype.card A0 : ℂ) * (T2.card : ℂ) * (b : ℂ)) * (ψ ((1, 0), t) * GPsi D ell ψ y)
        else 0 := by
    intro ψ
    rw [← Finset.sum_mul, Finset.sum_comm]
    have hsplit : ∀ s ∈ T2,
        ∑ u : A0, starRingEnd ℂ (ψ ((1, 0), u.1 + s - t)) =
          starRingEnd ℂ (ψ ((1, 0), s - t)) * ∑ u : A0, starRingEnd ℂ (ψ (0, u.1)) := by
      intro s _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      have hadd : (((1, 0) : E0), u.1 + s - t) = (((1, 0) : E0), s - t) + (0, u.1) := by
        ext <;> simp; abel
      rw [hadd, AddChar.map_add_eq_mul, map_mul]
    rw [Finset.sum_congr rfl hsplit, ← Finset.sum_mul]
    have horthA0 : ∑ u : A0, starRingEnd ℂ (ψ (0, u.1)) =
        if ψ ∈ PsiA A0 then (Fintype.card A0 : ℂ) else 0 := by
      let θ : AddChar H ℂ :=
        { toFun := fun h => ψ (0, h)
          map_zero_eq_one' := ψ.map_zero_eq_one
          map_add_eq_mul' := fun x y => by
            have : ((0 : E0), x + y) = ((0 : E0), x) + ((0 : E0), y) := by ext <;> simp
            rw [this, AddChar.map_add_eq_mul] }
      have hconj : ∑ u : A0, starRingEnd ℂ (ψ (0, u.1)) = starRingEnd ℂ (∑ u : A0, θ u.1) := by
        rw [map_sum]; rfl
      rw [hconj, addChar_sum_subgroup_orthog A0 θ]
      have hiff : (∀ s ∈ A0, θ s = 1) ↔ ψ ∈ PsiA A0 := by
        rw [mem_PsiA]; rfl
      by_cases h : ψ ∈ PsiA A0
      · rw [if_pos (hiff.mpr h), if_pos h, map_natCast]
      · rw [if_neg (fun hm => h (hiff.mp hm)), if_neg h, map_zero]
    rw [horthA0]
    by_cases hψ : ψ ∈ PsiA A0
    · rw [if_pos hψ, if_pos hψ]
      have hT2_val : ∀ s ∈ T2, starRingEnd ℂ (ψ ((1, 0), s - t)) = ψ ((1, 0), t) := by
        intro s hs
        have htriv : ψ (0, s) = 1 := (mem_PsiA.mp hψ) s (hT2 s hs)
        have hdec : (((1, 0) : E0), s - t) = (0, s) + (((1, 0) : E0), -t) := by
          ext <;> simp [sub_eq_add_neg]
        rw [hdec, AddChar.map_add_eq_mul, htriv, one_mul]
        have hneg : (((1, 0) : E0), -t) = -(((1, 0) : E0), t) := by
          ext
          · change (1 : ZMod 2) = -1; decide
          · simp
          · simp
        rw [hneg]
        have hnorm : ‖ψ ((1, 0), t)‖ = 1 := addChar_norm_eq_one ψ _
        have hmul1 : ψ (-(((1, 0) : E0), t)) * ψ ((1, 0), t) = 1 := by
          rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
        have hmul2 : starRingEnd ℂ (ψ ((1, 0), t)) * ψ ((1, 0), t) = 1 := by
          rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm, one_pow, Complex.ofReal_one]
        have hne : ψ ((1, 0), t) ≠ 0 := fun hz => by rw [hz, norm_zero] at hnorm; exact zero_ne_one hnorm
        have hconj_eq : ψ (-(((1, 0) : E0), t)) = starRingEnd ℂ (ψ ((1, 0), t)) :=
          mul_right_cancel₀ hne (hmul1.trans hmul2.symm)
        rw [hconj_eq]
        exact Complex.conj_conj _
      rw [Finset.sum_congr rfl hT2_val, Finset.sum_const, nsmul_eq_mul]
      ring
    · rw [if_neg hψ, if_neg hψ, mul_zero, zero_mul]
  rw [Finset.sum_congr rfl fun ψ _ => hchar ψ, ← Finset.sum_filter, Finset.filter_mem_eq_inter,
    Finset.univ_inter, ← Finset.mul_sum, ← mul_assoc]
  congr 1
  unfold delta2
  rw [card_PhiSet]
  push_cast
  field_simp [hH_ne]

/-- **Coset-Average Bridge (`ch_core_average`)**:
from pointwise slope-engine upper bounds `gapA D N ell TT a w u0 ≤ Err` across `u0 ∈ A0`
and thick-place approximation `(Th ...).re ≤ (De ...).re + 2 * b / x`, applies `ch_balance`
and `sum_Th` unconditionally to deduce:
`(TT.card : ℝ) * m * b * (delta2 T2 / 2) * Y ≤ Err + 2 * (TT.card : ℝ) * m * b / x`. -/
theorem ch_core_average {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (A0 : AddSubgroup H) [Fintype A0] (D : ArithData H) (S0 : Finset ℕ) (hD : HostFactsS D S0)
    (ell : AddChar (E0 × H) ℂ → ℂ) (N m : ℕ)
    (TT T2 : Finset H) (a : H → ℝ) (w : H → Fin m → E0 × H → ℝ)
    {x b Err Y : ℝ} (hb : 0 < b) (hT2 : ∀ s ∈ T2, s ∈ A0)
    (ha : ∀ t ∈ TT, 0 < a t)
    (hw : ∀ u0 ∈ A0, ∀ j : Fin m, ∀ ρ, InPhi ρ → 0 < w u0 j ρ)
    (hN : ∀ u0 ∈ A0, ∀ j : Fin m, ∀ t ∈ TT, ∀ ρ, InPhi ρ → a t / w u0 j ρ ≤ N)
    (hTh_le : ∀ u0 ∈ A0, ∀ t ∈ TT, ∀ j : Fin m,
      (Th D ell T2 b (a t / b) u0 t).re ≤ (De D ell (a t) t (w u0 j)).re + 2 * b / x)
    (hTop : ∀ u0 ∈ A0, gapA D N ell TT a w u0 ≤ Err)
    (hY : (TT.card : ℝ) * Y ≤
      ∑ t ∈ TT, (∑ ψ ∈ PsiA A0, ψ ((1, 0), t) * GPsi D ell ψ (a t / b)).re) :
    (TT.card : ℝ) * (m : ℝ) * b * (delta2 T2 / 2) * Y ≤
      Err + 2 * (TT.card : ℝ) * (m : ℝ) * b / x := by
  classical
  have hu : ∀ u0 ∈ A0,
      ∑ t ∈ TT, ∑ _j : Fin m, (Th D ell T2 b (a t / b) u0 t).re ≤
        Err + 2 * (TT.card : ℝ) * (m : ℝ) * b / x := by
    intro u0 hu0
    have h1 :
        ∑ t ∈ TT, ∑ _j : Fin m, (Th D ell T2 b (a t / b) u0 t).re ≤
          ∑ t ∈ TT, ∑ j : Fin m,
            (ASK D N (a t) t (w u0 j) - (MAIN ell (a t) (w u0 j)).re + 2 * b / x) := by
      refine Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun j _ => ?_
      have hbal := congrArg Complex.re
        (ch_balance D S0 hD ell (a t) t (w u0 j) (ha t ht) (hw u0 hu0 j) N
          (fun ρ hρ => hN u0 hu0 j t ht ρ hρ))
      rw [Complex.sub_re, Complex.ofReal_re] at hbal
      linarith [hTh_le u0 hu0 t ht j]
    simp only [Finset.sum_add_distrib] at h1
    have hc : ∑ _t ∈ TT, ∑ _j : Fin m, (2 * b / x) = 2 * (TT.card : ℝ) * (m : ℝ) * b / x := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
      ring
    rw [hc] at h1
    have hgap := hTop u0 hu0
    unfold gapA at hgap
    linarith
  have hA_pos : (0 : ℝ) < (Fintype.card A0 : ℝ) :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨⟨0, A0.zero_mem⟩⟩)
  have hsum_le :
      ∑ u : A0, ∑ t ∈ TT, ∑ _j : Fin m, (Th D ell T2 b (a t / b) u.1 t).re ≤
        (Fintype.card A0 : ℝ) * (Err + 2 * (TT.card : ℝ) * (m : ℝ) * b / x) := by
    refine (Finset.sum_le_sum fun u _ => hu u.1 u.2).trans (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hsum_eq :
      ∑ u : A0, ∑ t ∈ TT, ∑ _j : Fin m, (Th D ell T2 b (a t / b) u.1 t).re =
        (Fintype.card A0 : ℝ) * ((m : ℝ) * b * (delta2 T2 / 2) *
          ∑ t ∈ TT, (∑ ψ ∈ PsiA A0, ψ ((1, 0), t) * GPsi D ell ψ (a t / b)).re) := by
    rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
    rw [← Finset.mul_sum, ← Complex.re_sum, sum_Th A0 D ell T2 hT2, Complex.re_ofReal_mul]
    ring
  rw [hsum_eq] at hsum_le
  have hcancel := le_of_mul_le_mul_left hsum_le hA_pos
  have hcoeff_nn : 0 ≤ (m : ℝ) * b * (delta2 T2 / 2) := by
    unfold delta2; positivity
  have hmul := mul_le_mul_of_nonneg_left hY hcoeff_nn
  linarith

/-- **Unconditional Off-Kept Character Error Bound (`sigA_le`, matching `PrimitiveCosets.SigALe`)**:
given a `CosetFrame φ` with `φ.o = L.o` and uniform bounds `‖GPsi D ell ψ x‖ ≤ x^(1/2 + ε)` on
all off-kept characters `ψ ∈ PsiA φ.A0 \ Kp`, proves `SigA D ell φ.A0 Kp x ≤ 4 * L.o * x^(1/2 + ε)`. -/
theorem sigA_le (L : Level) (φ : CosetFrame) (ho : φ.o = L.o)
    (D : ArithData φ.A) (ell : AddChar (E0 × φ.A) ℂ → ℂ)
    (Kp : Finset (AddChar (E0 × φ.A) ℂ)) {x ε : ℝ} (hx : 0 < x)
    (hbd : ∀ ψ ∈ PsiA φ.A0 \ Kp, ‖GPsi D ell ψ x‖ ≤ x ^ ((1 : ℝ) / 2 + ε)) :
    SigA D ell φ.A0 Kp x ≤ 4 * (L.o : ℝ) * x ^ ((1 : ℝ) / 2 + ε) := by
  classical
  unfold SigA
  calc ∑ ψ ∈ PsiA φ.A0 \ Kp, ‖GPsi D ell ψ x‖
      ≤ ∑ _ψ ∈ PsiA φ.A0 \ Kp, x ^ ((1 : ℝ) / 2 + ε) := Finset.sum_le_sum hbd
    _ = ((PsiA φ.A0 \ Kp).card : ℝ) * x ^ ((1 : ℝ) / 2 + ε) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((PsiA φ.A0).card : ℝ) * x ^ ((1 : ℝ) / 2 + ε) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hx.le _)
          exact_mod_cast Finset.card_le_card Finset.sdiff_subset
    _ = 4 * (L.o : ℝ) * x ^ ((1 : ℝ) / 2 + ε) := by
          rw [card_PsiA φ, ho]; push_cast; ring

/-- **Unconditional `ch_core` (Eliminating `mainBalance` via `ch_balance` + `CosetWeights` + `RestSize`)**:
from `gapA ≤ x^(C * ε) * errorBracketSizeWindows`, `RestSize`, thick-place approximation, and
character-clearing lower bound, proves
`GmA D ell Kp (3 * φ.o + 1)⁻¹ x ≤ x ^ (1 / 2 + (C + 3) * ε) + SigA D ell φ.A0 Kp x`! -/
theorem ch_core (φ : CosetFrame) (D : ArithData φ.A) (S0 : Finset ℕ) (hD : HostFactsS D S0)
    (ell : AddChar (E0 × φ.A) ℂ → ℂ) (N m : ℕ)
    (TT T2 : Finset φ.A) (a : φ.A → ℝ) (w : φ.A → Fin m → E0 × φ.A → ℝ)
    (Kp : Finset (AddChar (E0 × φ.A) ℂ))
    {C ε x b k aE : ℝ}
    (hx : 3 ≤ x) (hε : 0 < ε) (hC : 0 ≤ C) (hb : 0 < b)
    (hm_hi : (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2))
    (hk_lo : x * (m : ℝ) ≤ k)
    (hX26 : 26 ≤ x ^ (3 * ε / 8))
    (hT2 : ∀ s ∈ T2, s ∈ φ.A0)
    (hRest : RestSize ε x (Fintype.card φ.A) TT.card T2.card m b k aE)
    (ha : ∀ t ∈ TT, 0 < a t)
    (hw : ∀ u0 ∈ φ.A0, ∀ j : Fin m, ∀ ρ, InPhi ρ → 0 < w u0 j ρ)
    (hN : ∀ u0 ∈ φ.A0, ∀ j : Fin m, ∀ t ∈ TT, ∀ ρ, InPhi ρ → a t / w u0 j ρ ≤ N)
    (hTh_le : ∀ u0 ∈ φ.A0, ∀ t ∈ TT, ∀ j : Fin m,
      (Th D ell T2 b (a t / b) u0 t).re ≤ (De D ell (a t) t (w u0 j)).re + 2 * b / x)
    (hTop : ∀ u0 ∈ φ.A0,
      gapA D N ell TT a w u0 ≤
        x ^ (C * ε) * errorBracketSizeWindows x ε (Fintype.card φ.A) TT.card T2.card m b k aE)
    (hClear :
      (TT.card : ℝ) *
          (GmA D ell Kp (3 * (φ.o : ℝ) + 1)⁻¹ x - SigA D ell φ.A0 Kp x - 4 * x ^ ((1 : ℝ) / 2 + ε)) ≤
        ∑ t ∈ TT, (∑ ψ ∈ PsiA φ.A0, ψ ((1, 0), t) * GPsi D ell ψ (a t / b)).re) :
    GmA D ell Kp (3 * (φ.o : ℝ) + 1)⁻¹ x ≤
      x ^ ((1 : ℝ) / 2 + (C + 3) * ε) + SigA D ell φ.A0 Kp x := by
  set Err := x ^ (C * ε) * errorBracketSizeWindows x ε (Fintype.card φ.A) TT.card T2.card m b k aE
  set G := GmA D ell Kp (3 * (φ.o : ℝ) + 1)⁻¹ x - SigA D ell φ.A0 Kp x
  have havg := ch_core_average φ.A0 D S0 hD ell N m TT T2 a w hb hT2 ha hw hN hTh_le hTop hClear
  have hgrowth := ZeroDensityWindow.growth_bound_of_restSize (C := C) (ε := ε) (x := x)
    (n := Fintype.card φ.A) (nT := TT.card) (nT2 := T2.card) (m := m)
    (b := b) (k := k) (aE := aE) (Err := Err) (Gx := G)
    hx hε hC φ.card_A_pos (Finset.card_le_univ T2) hb hm_hi hk_lo hX26 hRest le_rfl
    (by simpa only [delta2] using havg)
  linarith

/-- **Exact Unconditional Coset-Clearing Inequality (`coset_clear_psiA`)**:
using `CosetWeights.CosetFrame.tops_sum`, discharges the `hClear` hypothesis of `ch_core`
directly from `CosetFrame.Shares TT δ` and character-evaluation stability on `a t / b ≈ x`! -/
theorem coset_clear_psiA (φ : CosetFrame) (D : ArithData φ.A)
    (ell : AddChar (E0 × φ.A) ℂ → ℂ)
    (TT : Finset φ.A) (a : φ.A → ℝ) {δ x b : ℝ}
    (hsh : φ.Shares TT δ)
    (Kp : Finset (AddChar (E0 × φ.A) ℂ))
    (hKp_sub : Kp ⊆ PsiA φ.A0)
    (hKp_even : ∀ ψ ∈ Kp, ψ ((1, 0), 0) = 1)
    (hKp_zero : ∀ ψ ∈ Kp, (∀ h : φ.A, ψ (0, h) = 1) → ψ = 0)
    (Err : AddChar (E0 × φ.A) ℂ → ℝ)
    (hpert : ∀ t ∈ TT, ∀ ψ ∈ PsiA φ.A0,
      ‖GPsi D ell ψ (a t / b) - GPsi D ell ψ x‖ ≤ Err ψ)
    (hbudget :
      (φ.o : ℝ) * δ * (∑ ψ ∈ Kp.erase 0, ‖GPsi D ell ψ x‖) +
        ∑ ψ ∈ PsiA φ.A0, Err ψ ≤ 4 * x ^ ((1 : ℝ) / 2 + δ)) :
    (TT.card : ℝ) *
        (GmA D ell Kp (3 * (φ.o : ℝ) + 1)⁻¹ x - SigA D ell φ.A0 Kp x -
          4 * x ^ ((1 : ℝ) / 2 + δ)) ≤
      ∑ t ∈ TT, (∑ ψ ∈ PsiA φ.A0, ψ ((1, 0), t) * GPsi D ell ψ (a t / b)).re := by
  classical
  have hdiff :
      ∑ t ∈ TT, (∑ ψ ∈ PsiA φ.A0, ψ ((1, 0), t) * GPsi D ell ψ x).re -
        ∑ t ∈ TT, (∑ ψ ∈ PsiA φ.A0, ψ ((1, 0), t) * GPsi D ell ψ (a t / b)).re ≤
      (TT.card : ℝ) * ∑ ψ ∈ PsiA φ.A0, Err ψ := by
    rw [← Finset.sum_sub_distrib, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun t ht => ?_
    simp_rw [Complex.re_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun ψ hψ => ?_
    have hnorm : ‖ψ ((1, 0), t) * (GPsi D ell ψ x - GPsi D ell ψ (a t / b))‖ ≤ Err ψ := by
      rw [norm_mul, addChar_norm_eq_one, one_mul, norm_sub_rev]
      exact hpert t ht ψ hψ
    have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans hnorm)).2
    have heq : (ψ ((1, 0), t) * GPsi D ell ψ x).re -
        (ψ ((1, 0), t) * GPsi D ell ψ (a t / b)).re =
        (ψ ((1, 0), t) * (GPsi D ell ψ x - GPsi D ell ψ (a t / b))).re := by
      rw [← Complex.sub_re, ← mul_sub]
    rwa [heq]
  have hswap :
      ∑ t ∈ TT, (∑ ψ ∈ PsiA φ.A0, ψ ((1, 0), t) * GPsi D ell ψ x).re =
        ∑ ψ ∈ Kp, ((∑ t ∈ TT, ψ ((1, 0), t)) * GPsi D ell ψ x).re +
        ∑ ψ ∈ PsiA φ.A0 \ Kp, ((∑ t ∈ TT, ψ ((1, 0), t)) * GPsi D ell ψ x).re := by
    simp_rw [Complex.re_sum]
    rw [Finset.sum_comm]
    have hpart : PsiA φ.A0 = Kp ∪ (PsiA φ.A0 \ Kp) := (Finset.union_sdiff_of_subset hKp_sub).symm
    conv_lhs => rw [hpart, Finset.sum_union Finset.disjoint_sdiff]
    congr 1 <;> refine Finset.sum_congr rfl fun ψ _ => by rw [Finset.sum_mul, Complex.re_sum]
  have hkept :
      (TT.card : ℝ) *
          (GmA D ell Kp (3 * (φ.o : ℝ) + 1)⁻¹ x -
            (φ.o : ℝ) * δ * ∑ ψ ∈ Kp.erase 0, ‖GPsi D ell ψ x‖) ≤
        ∑ ψ ∈ Kp, ((∑ t ∈ TT, ψ ((1, 0), t)) * GPsi D ell ψ x).re := by
    have hterm : ∀ ψ ∈ Kp,
        (TT.card : ℝ) *
            ((if ψ = 0 then (1 : ℝ) else (3 * (φ.o : ℝ) + 1)⁻¹) * (GPsi D ell ψ x).re -
              if ψ = 0 then 0 else (φ.o : ℝ) * δ * ‖GPsi D ell ψ x‖) ≤
          ((∑ t ∈ TT, ψ ((1, 0), t)) * GPsi D ell ψ x).re := by
      intro ψ hψ
      have hfac : ∀ t : φ.A, ψ ((1, 0), t) = ψ (0, t) := fun t => by
        have hdec : (((1, 0) : E0), t) = (((1, 0) : E0), (0 : φ.A)) + (0, t) := by ext <;> simp
        rw [hdec, AddChar.map_add_eq_mul, hKp_even ψ hψ, one_mul]
      simp_rw [hfac]
      by_cases h0 : ψ = 0
      · subst h0
        simp only [↓reduceIte, one_mul, sub_zero, AddChar.zero_apply, Finset.sum_const, nsmul_eq_mul,
          mul_one]
        rw [show (TT.card : ℂ) = ((TT.card : ℝ) : ℂ) by norm_cast, Complex.re_ofReal_mul]
      · rw [if_neg h0, if_neg h0]
        let θ : AddChar φ.A ℂ :=
          { toFun := fun h => ψ (0, h)
            map_zero_eq_one' := ψ.map_zero_eq_one
            map_add_eq_mul' := fun x y => by
              have : ((0 : E0), x + y) = ((0 : E0), x) + ((0 : E0), y) := by ext <;> simp
              rw [this, AddChar.map_add_eq_mul] }
        have hθ0 : ∀ s ∈ φ.A0, θ s = 1 := mem_PsiA.mp (hKp_sub hψ)
        have hθne : θ ≠ 0 := fun hz => h0 (hKp_zero ψ hψ fun h => by
          have := DFunLike.congr_fun hz h; simpa [θ] using this)
        have hts := φ.tops_sum hsh hθ0 hθne
        set c : ℝ := (3 * (φ.o : ℝ) + 1)⁻¹
        have hnorm :
            ‖(∑ t ∈ TT, θ t) * GPsi D ell ψ x - (c : ℂ) * (TT.card : ℂ) * GPsi D ell ψ x‖ ≤
              (φ.o : ℝ) * δ * (TT.card : ℝ) * ‖GPsi D ell ψ x‖ := by
          rw [show (∑ t ∈ TT, θ t) * GPsi D ell ψ x - (c : ℂ) * (TT.card : ℂ) * GPsi D ell ψ x =
              ((∑ t ∈ TT, θ t) - (c : ℂ) * (TT.card : ℂ)) * GPsi D ell ψ x by ring, norm_mul]
          exact mul_le_mul_of_nonneg_right hts (norm_nonneg _)
        have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans hnorm)).1
        have hmain : ((c : ℂ) * (TT.card : ℂ) * GPsi D ell ψ x).re =
            (TT.card : ℝ) * (c * (GPsi D ell ψ x).re) := by
          rw [show (c : ℂ) * (TT.card : ℂ) = ((c * (TT.card : ℝ) : ℝ) : ℂ) by push_cast; ring,
            Complex.re_ofReal_mul]
          ring
        rw [Complex.sub_re, hmain] at hre
        change _ ≤ ((∑ t ∈ TT, θ t) * GPsi D ell ψ x).re
        linarith
    calc (TT.card : ℝ) *
            (GmA D ell Kp (3 * (φ.o : ℝ) + 1)⁻¹ x -
              (φ.o : ℝ) * δ * ∑ ψ ∈ Kp.erase 0, ‖GPsi D ell ψ x‖)
        = ∑ ψ ∈ Kp, (TT.card : ℝ) *
            ((if ψ = 0 then (1 : ℝ) else (3 * (φ.o : ℝ) + 1)⁻¹) * (GPsi D ell ψ x).re -
              if ψ = 0 then 0 else (φ.o : ℝ) * δ * ‖GPsi D ell ψ x‖) := by
          unfold GmA
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib, Finset.mul_sum]
          congr 1
          have hite :
              ∑ ψ ∈ Kp, (TT.card : ℝ) * (if ψ = 0 then (0 : ℝ) else (φ.o : ℝ) * δ * ‖GPsi D ell ψ x‖) =
                ∑ ψ ∈ Kp.erase 0, (TT.card : ℝ) * ((φ.o : ℝ) * δ * ‖GPsi D ell ψ x‖) := by
            have hstep : ∀ ψ : AddChar (E0 × φ.A) ℂ,
                (TT.card : ℝ) * (if ψ = 0 then (0 : ℝ) else (φ.o : ℝ) * δ * ‖GPsi D ell ψ x‖) =
                  if ψ ≠ 0 then (TT.card : ℝ) * ((φ.o : ℝ) * δ * ‖GPsi D ell ψ x‖) else 0 := fun ψ => by
              by_cases h : ψ = 0 <;> simp [h]
            rw [Finset.sum_congr rfl fun ψ _ => hstep ψ, ← Finset.sum_filter]
            refine Finset.sum_congr ?_ fun _ _ => rfl
            ext ψ; simp [and_comm]
          rw [hite, Finset.mul_sum, Finset.mul_sum]
      _ ≤ ∑ ψ ∈ Kp, ((∑ t ∈ TT, ψ ((1, 0), t)) * GPsi D ell ψ x).re := Finset.sum_le_sum hterm
  have hoff :
      -((TT.card : ℝ) * SigA D ell φ.A0 Kp x) ≤
        ∑ ψ ∈ PsiA φ.A0 \ Kp, ((∑ t ∈ TT, ψ ((1, 0), t)) * GPsi D ell ψ x).re := by
    unfold SigA
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun ψ _ => ?_
    have hts : ‖∑ t ∈ TT, ψ ((1, 0), t)‖ ≤ (TT.card : ℝ) := by
      calc ‖∑ t ∈ TT, ψ ((1, 0), t)‖
          ≤ ∑ t ∈ TT, ‖ψ ((1, 0), t)‖ := norm_sum_le _ _
        _ = (TT.card : ℝ) := by
            simp only [addChar_norm_eq_one, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hnorm : ‖(∑ t ∈ TT, ψ ((1, 0), t)) * GPsi D ell ψ x‖ ≤
        (TT.card : ℝ) * ‖GPsi D ell ψ x‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hts (norm_nonneg _)
    exact (abs_le.mp ((Complex.abs_re_le_norm _).trans hnorm)).1
  have hmul_b := mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg TT.card)
  linarith

/-- **Unconditional `core_gm` (`UpperTheory.Comparison₂.core_gm` Counterpart)**:
combines `ch_core` + `sigA_le` + kept-sum identification `GmA = L.Gm x` to deduce directly:
`L.Gm x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 7) * ε)`! -/
theorem core_gm (L : Level) (φ : CosetFrame) (ho : φ.o = L.o)
    (D : ArithData φ.A) (S0 : Finset ℕ) (hD : HostFactsS D S0)
    (ell : AddChar (E0 × φ.A) ℂ → ℂ) (N m : ℕ)
    (TT T2 : Finset φ.A) (a : φ.A → ℝ) (w : φ.A → Fin m → E0 × φ.A → ℝ)
    (Kp : Finset (AddChar (E0 × φ.A) ℂ))
    {eD eL ε x b k aE : ℝ}
    (hx : 3 ≤ x) (hε : 0 < ε) (heD : 0 ≤ eD) (heL : 0 ≤ eL) (hb : 0 < b)
    (hm_hi : (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2))
    (hk_lo : x * (m : ℝ) ≤ k)
    (hX26 : 26 ≤ x ^ (3 * ε / 8))
    (hXo : 1 + 4 * (L.o : ℝ) ≤ x ^ ε)
    (hT2 : ∀ s ∈ T2, s ∈ φ.A0)
    (hRest : RestSize ε x (Fintype.card φ.A) TT.card T2.card m b k aE)
    (ha : ∀ t ∈ TT, 0 < a t)
    (hw : ∀ u0 ∈ φ.A0, ∀ j : Fin m, ∀ ρ, InPhi ρ → 0 < w u0 j ρ)
    (hN : ∀ u0 ∈ φ.A0, ∀ j : Fin m, ∀ t ∈ TT, ∀ ρ, InPhi ρ → a t / w u0 j ρ ≤ N)
    (hTh_le : ∀ u0 ∈ φ.A0, ∀ t ∈ TT, ∀ j : Fin m,
      (Th D ell T2 b (a t / b) u0 t).re ≤ (De D ell (a t) t (w u0 j)).re + 2 * b / x)
    (hTop : ∀ u0 ∈ φ.A0,
      gapA D N ell TT a w u0 ≤
        x ^ ((eD + eL + 3) * ε) *
          errorBracketSizeWindows x ε (Fintype.card φ.A) TT.card T2.card m b k aE)
    (hClear :
      (TT.card : ℝ) *
          (GmA D ell Kp (3 * (φ.o : ℝ) + 1)⁻¹ x - SigA D ell φ.A0 Kp x - 4 * x ^ ((1 : ℝ) / 2 + ε)) ≤
        ∑ t ∈ TT, (∑ ψ ∈ PsiA φ.A0, ψ ((1, 0), t) * GPsi D ell ψ (a t / b)).re)
    (hGm_eq : GmA D ell Kp (3 * (φ.o : ℝ) + 1)⁻¹ x = L.Gm x)
    (hOff : ∀ ψ ∈ PsiA φ.A0 \ Kp, ‖GPsi D ell ψ x‖ ≤ x ^ ((1 : ℝ) / 2 + ε)) :
    L.Gm x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 7) * ε) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hmain := ch_core φ D S0 hD ell N m TT T2 a w Kp (C := eD + eL + 3)
    hx hε (by linarith) hb hm_hi hk_lo hX26 hT2 hRest ha hw hN hTh_le hTop hClear
  rw [hGm_eq] at hmain
  have hsig := sigA_le L φ ho D ell Kp hx0 hOff
  have h1 : x ^ ((1 : ℝ) / 2 + ε) ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 3 + 3) * ε) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by nlinarith)
  have h2 : x ^ ((1 : ℝ) / 2 + (eD + eL + 7) * ε) =
      x ^ ε * x ^ ((1 : ℝ) / 2 + (eD + eL + 3 + 3) * ε) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have h3 := mul_le_mul_of_nonneg_right hXo
    (Real.rpow_nonneg hx0.le ((1 : ℝ) / 2 + (eD + eL + 3 + 3) * ε))
  have h4 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 4 * (L.o : ℝ) by positivity)
  rw [h2]
  linarith

/-- **Elimination of `mainBalance` as an Abstract Field (`levelBracketData_of_ch_balance`)**:
directly constructs `ZeroDensityWindow.LevelBracketData L C ε x` (feeding straight into
`Stage2AnalyticWire.level_window_coupling` and `Stage2AnalyticWire.stage2_analyticBridgeContract`)
from `ch_balance`, `ch_core_average`, `sigA_le`, and `RestSize` — with ZERO `mainBalance` assumption! -/
def levelBracketData_of_ch_balance (L : Level) (φ : CosetFrame) (ho : φ.o = L.o)
    (D : ArithData φ.A) (S0 : Finset ℕ) (hD : HostFactsS D S0)
    (ell : AddChar (E0 × φ.A) ℂ → ℂ) (N m : ℕ)
    (TT T2 : Finset φ.A) (a : φ.A → ℝ) (w : φ.A → Fin m → E0 × φ.A → ℝ)
    (Kp : Finset (AddChar (E0 × φ.A) ℂ))
    {C ε x b k aE : ℝ}
    (hx : 3 ≤ x) (_hε : 0 < ε) (hb : 0 < b) (haE : 0 ≤ aE)
    (hm_hi : (m : ℝ) ≤ x ^ ((1 : ℝ) / 2 + ε / 2))
    (hk_lo : x * (m : ℝ) ≤ k)
    (hXo : 4 * (L.o : ℝ) ≤ 2 * x ^ (ε / 2))
    (hT2 : ∀ s ∈ T2, s ∈ φ.A0)
    (hRest : RestSize ε x (Fintype.card φ.A) TT.card T2.card m b k aE)
    (ha : ∀ t ∈ TT, 0 < a t)
    (hw : ∀ u0 ∈ φ.A0, ∀ j : Fin m, ∀ ρ, InPhi ρ → 0 < w u0 j ρ)
    (hN : ∀ u0 ∈ φ.A0, ∀ j : Fin m, ∀ t ∈ TT, ∀ ρ, InPhi ρ → a t / w u0 j ρ ≤ N)
    (hTh_le : ∀ u0 ∈ φ.A0, ∀ t ∈ TT, ∀ j : Fin m,
      (Th D ell T2 b (a t / b) u0 t).re ≤ (De D ell (a t) t (w u0 j)).re + 2 * b / x)
    (hTop : ∀ u0 ∈ φ.A0,
      gapA D N ell TT a w u0 ≤
        x ^ (C * ε) * errorBracketSizeWindows x ε (Fintype.card φ.A) TT.card T2.card m b k aE)
    (hClear :
      (TT.card : ℝ) *
          (GmA D ell Kp (3 * (φ.o : ℝ) + 1)⁻¹ x - SigA D ell φ.A0 Kp x - 2 * x ^ ((1 : ℝ) / 2 + ε)) ≤
        ∑ t ∈ TT, (∑ ψ ∈ PsiA φ.A0, ψ ((1, 0), t) * GPsi D ell ψ (a t / b)).re)
    (hGm_eq : GmA D ell Kp (3 * (φ.o : ℝ) + 1)⁻¹ x = L.Gm x)
    (hOff : ∀ ψ ∈ PsiA φ.A0 \ Kp, ‖GPsi D ell ψ x‖ ≤ x ^ ((1 : ℝ) / 2 + ε / 2)) :
    ZeroDensityWindow.LevelBracketData L C ε x where
  n := Fintype.card φ.A
  nT := TT.card
  nT2 := T2.card
  m := m
  b := b
  k := k
  aE := aE
  Err := x ^ (C * ε) * errorBracketSizeWindows x ε (Fintype.card φ.A) TT.card T2.card m b k aE
  n_pos := φ.card_A_pos
  nT2_le := Finset.card_le_univ T2
  b_pos := hb
  aE_nonneg := haE
  m_hi := hm_hi
  k_lo := hk_lo
  rest := hRest
  err_le := le_rfl
  main_le := by
    have hx0 : 0 < x := by linarith
    have hsig : SigA D ell φ.A0 Kp x ≤ 4 * (L.o : ℝ) * x ^ ((1 : ℝ) / 2 + ε / 2) :=
      sigA_le L φ ho D ell Kp hx0 hOff
    have hsig2 : SigA D ell φ.A0 Kp x ≤ 2 * x ^ ((1 : ℝ) / 2 + ε) := by
      calc SigA D ell φ.A0 Kp x
          ≤ 4 * (L.o : ℝ) * x ^ ((1 : ℝ) / 2 + ε / 2) := hsig
        _ ≤ (2 * x ^ (ε / 2)) * x ^ ((1 : ℝ) / 2 + ε / 2) :=
            mul_le_mul_of_nonneg_right hXo (Real.rpow_nonneg hx0.le _)
        _ = 2 * (x ^ (ε / 2) * x ^ ((1 : ℝ) / 2 + ε / 2)) := by ring
        _ = 2 * x ^ ((1 : ℝ) / 2 + ε) := by
            rw [← Real.rpow_add hx0]; congr 2; ring
    have hClear' :
        (TT.card : ℝ) * (L.Gm x - 4 * x ^ ((1 : ℝ) / 2 + ε)) ≤
          ∑ t ∈ TT, (∑ ψ ∈ PsiA φ.A0, ψ ((1, 0), t) * GPsi D ell ψ (a t / b)).re := by
      refine le_trans ?_ hClear
      rw [hGm_eq]
      exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
    simpa only [delta2] using
      ch_core_average φ.A0 D S0 hD ell N m TT T2 a w hb hT2 ha hw hN hTh_le hTop hClear'

/-! ## Section 3: Quadratic-Twist Primitivity, Unconditional `ZeroFreeBox`, Borel–Carathéodory & `BoxOfS` -/

/-- Canonical primitive quadratic Dirichlet character `χ_p(n) = (n | p)` for any odd prime `p`. -/
def quadCharOfPrime (p : ℕ) [NeZero p] (hp : p.Prime) : DirichletCharacter ℂ p where
  toFun := fun a => ((jacobiSym (a.val : ℤ) p : ℤ) : ℂ)
  map_one' := by
    have hp1 : 1 < p := hp.one_lt
    have : Fact (1 < p) := ⟨hp1⟩
    rw [ZMod.val_one, Nat.cast_one, jacobiSym.one_left]
    simp
  map_mul' := fun a b => by
    have hmod : ((a * b).val : ℤ) ≡ (a.val : ℤ) * (b.val : ℤ) [ZMOD (p : ℤ)] := by
      rw [← Int.natCast_mul, Int.natCast_modEq_iff, ZMod.val_mul]
      exact Nat.mod_modEq _ _
    rw [jacobiSym.mod_left' hmod, jacobiSym.mul_left, Int.cast_mul]
  map_nonunit' := fun a ha => by
    have hnotcop : ¬ Nat.Coprime a.val p := by
      intro hcop
      apply ha
      have h1 : IsUnit ((a.val : ℕ) : ZMod p) := (ZMod.isUnit_iff_coprime a.val p).mpr hcop
      rwa [ZMod.natCast_zmod_val] at h1
    have hdvd : p ∣ a.val := by
      have h := (Nat.Prime.coprime_iff_not_dvd hp).not.mp (fun h => hnotcop h.symm)
      exact not_not.mp h
    have hmod : (a.val : ℤ) ≡ 0 [ZMOD (p : ℤ)] :=
      Int.modEq_zero_iff_dvd.mpr (Int.natCast_dvd_natCast.mpr hdvd)
    rw [jacobiSym.mod_left' hmod, jacobiSym.zero_left hp.one_lt]
    simp

theorem quadCharOfPrime_apply_nat {p : ℕ} [NeZero p] (hp : p.Prime) (n : ℕ) :
    quadCharOfPrime p hp (n : ZMod p) = ((jacobiSym (n : ℤ) p : ℤ) : ℂ) := by
  change ((jacobiSym (((n : ZMod p).val : ℤ)) p : ℤ) : ℂ) = _
  have hmod : (((n : ZMod p).val : ℤ)) ≡ (n : ℤ) [ZMOD (p : ℤ)] := by
    rw [Int.natCast_modEq_iff, ZMod.val_natCast]
    exact Nat.mod_modEq n p
  rw [jacobiSym.mod_left' hmod]

theorem quadCharOfPrime_ne_one_of_mod_four {p : ℕ} [NeZero p] (hp : p.Prime) (hp4 : p % 4 = 3) :
    quadCharOfPrime p hp ≠ 1 := by
  intro h1
  have hval := congrArg (fun χ : DirichletCharacter ℂ p => χ ((-1 : ℤ) : ZMod p)) h1
  have hneg_unit : IsUnit ((-1 : ℤ) : ZMod p) := by
    rw [Int.cast_neg, Int.cast_one]; exact isUnit_one.neg
  rw [MulChar.one_apply hneg_unit] at hval
  have hnat : ((-1 : ℤ) : ZMod p) = ((p - 1 : ℕ) : ZMod p) := by
    rw [Int.cast_neg, Int.cast_one, Nat.cast_sub hp.one_lt.le, ZMod.natCast_self, zero_sub, Nat.cast_one]
  rw [hnat, quadCharOfPrime_apply_nat hp (p - 1)] at hval
  have hmod : ((p - 1 : ℕ) : ℤ) ≡ (-1 : ℤ) [ZMOD (p : ℤ)] := by
    have : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by omega
    rw [this]; exact Int.modEq_iff_dvd.mpr ⟨-1, by ring⟩
  rw [jacobiSym.mod_left' hmod, jacobiSym.at_neg_one (Nat.odd_iff.mpr (by omega)),
    ZMod.χ₄_nat_three_mod_four hp4] at hval
  norm_num at hval

private lemma eq_one_of_conductor_eq_one {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (h1 : χ.conductor = 1) : χ = 1 := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hprim1 : χ.primitiveCharacter = 1 := by
    have haux : ∀ (m : ℕ) [NeZero m] (ψ : DirichletCharacter ℂ m), m = 1 → ψ = 1 := by
      rintro _ _ ψ rfl; exact DirichletCharacter.level_one ψ
    exact haux χ.conductor χ.primitiveCharacter h1
  rw [← χ.changeLevel_primitiveCharacter, hprim1, map_one]

theorem isPrimitive_of_prime_ne_one {p : ℕ} [NeZero p] (hp : p.Prime)
    {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) : χ.IsPrimitive := by
  have hdvd : χ.conductor ∣ p := χ.conductor_dvd_level
  rcases hp.eq_one_or_self_of_dvd χ.conductor hdvd with h1 | hp_eq
  · exact absurd (eq_one_of_conductor_eq_one h1) hχ
  · exact hp_eq

theorem quadCharOfPrime_isPrimitive_of_mod_four {p : ℕ} [NeZero p] (hp : p.Prime)
    (hp4 : p % 4 = 3) : (quadCharOfPrime p hp).IsPrimitive :=
  isPrimitive_of_prime_ne_one hp (quadCharOfPrime_ne_one_of_mod_four hp hp4)

/-- **Primitivity of Coprime Twisted Product (`twistedChar_isPrimitive`)**:
if `ψ : DirichletCharacter ℂ M` and `χ : DirichletCharacter ℂ q` are primitive with `Coprime M q`,
then `Stage11SecondMomentFrame.twistedChar ψ χ : DirichletCharacter ℂ (M * q)` is primitive! -/
theorem twistedChar_isPrimitive {M q : ℕ} [NeZero M] [NeZero q] (hcop : Nat.Coprime M q)
    {ψ : DirichletCharacter ℂ M} {χ : DirichletCharacter ℂ q}
    (hψ : ψ.IsPrimitive) (hχ : χ.IsPrimitive) :
    (Stage11SecondMomentFrame.twistedChar ψ χ).IsPrimitive := by
  set η := Stage11SecondMomentFrame.twistedChar ψ χ
  set f := η.conductor
  have hf_dvd : f ∣ M * q := η.conductor_dvd_level
  have : NeZero f := ⟨η.conductor_ne_zero⟩
  set f₁ := Nat.gcd f M
  set f₂ := Nat.gcd f q
  have hf₁_dvd : f₁ ∣ M := Nat.gcd_dvd_right f M
  have hf₂_dvd : f₂ ∣ q := Nat.gcd_dvd_right f q
  have hM_pos : 0 < M := NeZero.pos M
  have hq_pos : 0 < q := NeZero.pos q
  have hf_pos : 0 < f := NeZero.pos f
  have hf₁_pos : 0 < f₁ := Nat.gcd_pos_of_pos_right f hM_pos
  have hf₂_pos : 0 < f₂ := Nat.gcd_pos_of_pos_right f hq_pos
  have : NeZero f₁ := ⟨hf₁_pos.ne'⟩
  have : NeZero f₂ := ⟨hf₂_pos.ne'⟩
  have hcop_f : Nat.Coprime f₁ f₂ :=
    (hcop.coprime_dvd_left hf₁_dvd).coprime_dvd_right hf₂_dvd
  have hf_eq : f = f₁ * f₂ := by
    have h1 : f ∣ f₁ * f₂ := by
      have hmul := Nat.gcd_mul_right_dvd_mul_gcd f M q
      rwa [Nat.gcd_eq_left hf_dvd] at hmul
    have h2 : f₁ * f₂ ∣ f :=
      hcop_f.mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_left f M) (Nat.gcd_dvd_left f q)
    exact Nat.dvd_antisymm h1 h2
  have hη_ker : MonoidHom.ker (ZMod.unitsMap hf_dvd) ≤ MonoidHom.ker η.toUnitHom :=
    (DirichletCharacter.factorsThrough_iff_ker_unitsMap hf_dvd).mp
      (DirichletCharacter.factorsThrough_conductor η)
  -- Show `f₁ = M` via `ψ.FactorsThrough f₁`
  have hf₁_eq : f₁ = M := by
    have hfac : ψ.FactorsThrough f₁ := by
      refine (DirichletCharacter.factorsThrough_iff_ker_unitsMap hf₁_dvd).mpr fun a ha => ?_
      rw [MonoidHom.mem_ker] at ha
      let cr := Nat.chineseRemainder hcop (a : ZMod M).val 1
      set n := cr.val
      have hnM : (n : ZMod M) = (a : ZMod M) := by
        have h1 := (ZMod.natCast_eq_natCast_iff n (a : ZMod M).val M).mpr cr.property.1
        rwa [ZMod.natCast_zmod_val] at h1
      have hnq : (n : ZMod q) = 1 := by
        simpa using (ZMod.natCast_eq_natCast_iff n 1 q).mpr cr.property.2
      have ha1_f₁ : (a : ZMod M).val ≡ 1 [MOD f₁] := by
        have hc := congrArg (Units.val : (ZMod f₁)ˣ → ZMod f₁) ha
        change ZMod.castHom hf₁_dvd (ZMod f₁) (a : ZMod M) = 1 at hc
        rw [← ZMod.natCast_zmod_val (a : ZMod M), map_natCast] at hc
        exact (ZMod.natCast_eq_natCast_iff _ 1 f₁).mp (by simpa using hc)
      have hn1_f : n ≡ 1 [MOD f] := by
        rw [hf_eq]
        exact (Nat.modEq_and_modEq_iff_modEq_mul hcop_f).mp
          ⟨(cr.property.1.of_dvd hf₁_dvd).trans ha1_f₁, cr.property.2.of_dvd hf₂_dvd⟩
      have hcop_n : Nat.Coprime n (M * q) :=
        ((ZMod.isUnit_iff_coprime n M).mp (hnM ▸ a.isUnit)).mul_right
          ((ZMod.isUnit_iff_coprime n q).mp (hnq ▸ isUnit_one))
      have hu : IsUnit (n : ZMod (M * q)) := (ZMod.isUnit_iff_coprime n (M * q)).mpr hcop_n
      have hu_ker : hu.unit ∈ MonoidHom.ker (ZMod.unitsMap hf_dvd) := by
        rw [MonoidHom.mem_ker]; apply Units.ext
        change ZMod.castHom hf_dvd (ZMod f) (n : ZMod (M * q)) = 1
        rw [map_natCast]
        simpa using (ZMod.natCast_eq_natCast_iff n 1 f).mpr hn1_f
      have hη1 : η (n : ZMod (M * q)) = 1 := by
        have h1 := hη_ker hu_ker
        rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one] at h1
        simpa [IsUnit.unit_spec] using h1
      rw [Stage11SecondMomentFrame.twistedChar_apply_nat_of_coprime ψ χ hcop_n,
        hnM, hnq, map_one, mul_one] at hη1
      rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
      exact hη1
    have hc0 : ψ.conductor ≤ f₁ := Nat.sInf_le hfac
    have hψ' : ψ.conductor = M := hψ
    rw [hψ'] at hc0
    exact le_antisymm (Nat.le_of_dvd hM_pos hf₁_dvd) hc0
  -- Show `f₂ = q` via `χ.FactorsThrough f₂`
  have hf₂_eq : f₂ = q := by
    have hfac : χ.FactorsThrough f₂ := by
      refine (DirichletCharacter.factorsThrough_iff_ker_unitsMap hf₂_dvd).mpr fun a ha => ?_
      rw [MonoidHom.mem_ker] at ha
      let cr := Nat.chineseRemainder hcop 1 (a : ZMod q).val
      set n := cr.val
      have hnM : (n : ZMod M) = 1 := by
        simpa using (ZMod.natCast_eq_natCast_iff n 1 M).mpr cr.property.1
      have hnq : (n : ZMod q) = (a : ZMod q) := by
        have h1 := (ZMod.natCast_eq_natCast_iff n (a : ZMod q).val q).mpr cr.property.2
        rwa [ZMod.natCast_zmod_val] at h1
      have ha1_f₂ : (a : ZMod q).val ≡ 1 [MOD f₂] := by
        have hc := congrArg (Units.val : (ZMod f₂)ˣ → ZMod f₂) ha
        change ZMod.castHom hf₂_dvd (ZMod f₂) (a : ZMod q) = 1 at hc
        rw [← ZMod.natCast_zmod_val (a : ZMod q), map_natCast] at hc
        exact (ZMod.natCast_eq_natCast_iff _ 1 f₂).mp (by simpa using hc)
      have hn1_f : n ≡ 1 [MOD f] := by
        rw [hf_eq]
        exact (Nat.modEq_and_modEq_iff_modEq_mul hcop_f).mp
          ⟨cr.property.1.of_dvd hf₁_dvd, (cr.property.2.of_dvd hf₂_dvd).trans ha1_f₂⟩
      have hcop_n : Nat.Coprime n (M * q) :=
        ((ZMod.isUnit_iff_coprime n M).mp (hnM ▸ isUnit_one)).mul_right
          ((ZMod.isUnit_iff_coprime n q).mp (hnq ▸ a.isUnit))
      have hu : IsUnit (n : ZMod (M * q)) := (ZMod.isUnit_iff_coprime n (M * q)).mpr hcop_n
      have hu_ker : hu.unit ∈ MonoidHom.ker (ZMod.unitsMap hf_dvd) := by
        rw [MonoidHom.mem_ker]; apply Units.ext
        change ZMod.castHom hf_dvd (ZMod f) (n : ZMod (M * q)) = 1
        rw [map_natCast]
        simpa using (ZMod.natCast_eq_natCast_iff n 1 f).mpr hn1_f
      have hη1 : η (n : ZMod (M * q)) = 1 := by
        have h1 := hη_ker hu_ker
        rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one] at h1
        simpa [IsUnit.unit_spec] using h1
      rw [Stage11SecondMomentFrame.twistedChar_apply_nat_of_coprime ψ χ hcop_n,
        hnM, hnq, map_one, one_mul] at hη1
      rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
      exact hη1
    have hc0 : χ.conductor ≤ f₂ := Nat.sInf_le hfac
    have hχ' : χ.conductor = q := hχ
    rw [hχ'] at hc0
    exact le_antisymm (Nat.le_of_dvd hq_pos hf₂_dvd) hc0
  show f = M * q
  rw [hf_eq, hf₁_eq, hf₂_eq]

/-- Parametric zero-free box `Re(s) > 1 - δ, |Im(s)| ≤ Q` for a Dirichlet character `χ`. -/
def ZeroFreeBoxDelta (δ Q : ℝ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, 1 - δ < s.re → |s.im| ≤ Q → DirichletCharacter.LFunction χ s ≠ 0

/-- **UNCONDITIONAL ZERO-DENSITY BOX BOUND (`zeroDensityBox_unconditional`, `0` ASSUMPTIONS!)**:
directly from `Stage11LogFreeDensity.gallagher_logfree_zero_density_sum`, there exist absolute
constants `0 < δ₀ ≤ 1 / 400` and `C_zd > 0` such that for every `Q ≥ 3`, any finite family `F` of
primitive Dirichlet characters of conductor `≤ Q` failing `ZeroFreeBoxDelta δ₀ Q` has cardinality
`≤ C_zd * Q ^ (1 / 4 : ℝ)`. -/
theorem zeroDensityBox_unconditional :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 400 ∧ ∃ C_zd : ℝ, 0 < C_zd ∧
      ∀ (Q : ℝ) (F : Finset (Σ k : ℕ, DirichletCharacter ℂ (k + 1))), 3 ≤ Q →
        (∀ p ∈ F, p.2.IsPrimitive ∧ ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧ ¬ ZeroFreeBoxDelta δ₀ Q p.2) →
        (F.card : ℝ) ≤ C_zd * Q ^ (1 / 4 : ℝ) := by
  classical
  obtain ⟨C_LF, hCLF_pos, A_LF, hALF_pos, hlf⟩ :=
    Stage11LogFreeDensity.gallagher_logfree_zero_density_sum
  set δ₀ : ℝ := min (1 / 400) (1 / (16 * A_LF))
  have hδ₀_pos : 0 < δ₀ := lt_min (by norm_num) (by positivity)
  have hδ₀_400 : δ₀ ≤ 1 / 400 := min_le_left _ _
  have hδ₀_A : A_LF * δ₀ ≤ 1 / 16 := by
    have h1 : δ₀ ≤ 1 / (16 * A_LF) := min_le_right _ _
    have h2 := mul_le_mul_of_nonneg_left h1 hALF_pos.le
    have h3 : A_LF * (1 / (16 * A_LF)) = 1 / 16 := by field_simp [hALF_pos.ne']
    linarith
  refine ⟨δ₀, hδ₀_pos, hδ₀_400, 3 * C_LF, by positivity, fun Q F hQ hF => ?_⟩
  set Qn : ℕ := ⌊Q⌋₊
  have hQn_ge3 : 3 ≤ Qn := Nat.le_floor hQ
  have hQn_ge1 : 1 ≤ Qn := by omega
  have hQn_le_Q : (Qn : ℝ) ≤ Q := Nat.floor_le (by linarith)
  have hQ0 : 0 < Q := by linarith
  -- Every `p ∈ F` contributes at least `1` zero to `zerosOfLInBox p.2 (1 - δ₀) Q`
  have hone_le : ∀ p ∈ F, 1 ≤ (Stage11LogFreeDensity.zerosOfLInBox p.2 (1 - δ₀) Q).card := by
    intro p hp
    obtain ⟨_, _, hnz⟩ := hF p hp
    unfold ZeroFreeBoxDelta at hnz
    push Not at hnz
    obtain ⟨s, hs_re, hs_im, hs_zero⟩ := hnz
    have hs_pos : 0 < s.re := by linarith
    have hs_lt1 : s.re < 1 := by
      by_contra hge; push Not at hge
      have hne1 : p.2 ≠ 1 ∨ s ≠ 1 := by
        by_cases h1 : p.2 = 1
        · right
          intro hs1; subst hs1
          have hlev1 : p.1 + 1 = 1 := by
            have hpr : p.2.conductor = p.1 + 1 := (hF p hp).1
            rw [h1, DirichletCharacter.conductor_one] at hpr
            exact hpr.symm
          exact absurd hs_zero (by
            have hlev : p.1 = 0 := by omega
            cases p with | mk k χ =>
              dsimp only at hlev h1 ⊢; subst hlev; rw [h1]
              rw [DirichletCharacter.LFunction_modOne_eq]
              exact riemannZeta_ne_zero_of_one_le_re (by simp))
        · exact Or.inl h1
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re p.2 hne1 hge hs_zero
    have hs_mem : s ∈ (Stage11LogFreeDensity.finite_LFunction_zeros_in_box p.2 (1 - δ₀) Q).toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact ⟨hs_pos, hs_re.le, hs_lt1, hs_im, hs_zero⟩
    have hord_pos : 1 ≤ analyticOrderNatAt (DirichletCharacter.LFunction p.2) s := by
      have hdiff : DifferentiableOn ℂ (DirichletCharacter.LFunction p.2) {z : ℂ | z ≠ 1} :=
        fun z hz => (DirichletCharacter.differentiableAt_LFunction p.2 z (.inl hz)).differentiableWithinAt
      have han : AnalyticAt ℂ (DirichletCharacter.LFunction p.2) s :=
        hdiff.analyticAt (isOpen_ne.mem_nhds (fun h => by subst h; simp at hs_lt1))
      have hne_top : analyticOrderAt (DirichletCharacter.LFunction p.2) s ≠ ⊤ := by
        intro htop
        rw [analyticOrderAt_eq_top] at htop
        have hopen : IsOpen {z : ℂ | z ≠ 1} := isOpen_ne
        have hconn : IsPreconnected ({z : ℂ | z ≠ 1} : Set ℂ) :=
          (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
        have hanOn : AnalyticOnNhd ℂ (DirichletCharacter.LFunction p.2) {z : ℂ | z ≠ 1} :=
          fun z hz => hdiff.analyticAt (hopen.mem_nhds hz)
        have hzero2 := hanOn.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn
          (show s ∈ {z : ℂ | z ≠ 1} from fun h => by subst h; simp at hs_lt1) htop
          (show (2 : ℂ) ∈ {z : ℂ | z ≠ 1} by norm_num)
        exact DirichletCharacter.LFunction_ne_zero_of_one_le_re p.2 (.inr (by norm_num)) (by norm_num) hzero2
      obtain ⟨h, _, hh_ne, hh_eq⟩ := han.analyticOrderAt_ne_top.mp hne_top
      have hne0 : analyticOrderNatAt (DirichletCharacter.LFunction p.2) s ≠ 0 := by
        intro h0
        have hself := hh_eq.self_of_nhds
        simp only [h0, pow_zero, one_smul] at hself
        exact hh_ne (hself.symm.trans hs_zero)
      exact Nat.pos_of_ne_zero hne0
    rw [Stage11LogFreeDensity.zerosOfLInBox_card_eq_sum]
    exact hord_pos.trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hs_mem)
  -- Embed `F` into the sigma finset of `primitiveZeroBoxCount Qn (1 - δ₀) Q`
  let All : Finset (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) :=
    (Finset.range Qn).sigma fun k =>
      Finset.univ.filter fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive
  have hsub : F ⊆ All := by
    intro p hp
    obtain ⟨hprim, hle, _⟩ := hF p hp
    have hnat : p.1 + 1 ≤ Qn := Nat.le_floor hle
    exact Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr (by omega),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hprim⟩⟩
  have hcard_le : F.card ≤ Stage11LogFreeDensity.primitiveZeroBoxCount Qn (1 - δ₀) Q := by
    unfold Stage11LogFreeDensity.primitiveZeroBoxCount
    rw [← Finset.sum_sigma (Finset.range Qn)
      (fun k => Finset.univ.filter fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive)
      (fun p => (Stage11LogFreeDensity.zerosOfLInBox p.2 (1 - δ₀) Q).card)]
    calc F.card = ∑ _p ∈ F, 1 := by simp
      _ ≤ ∑ p ∈ F, (Stage11LogFreeDensity.zerosOfLInBox p.2 (1 - δ₀) Q).card :=
          Finset.sum_le_sum hone_le
      _ ≤ ∑ p ∈ All, (Stage11LogFreeDensity.zerosOfLInBox p.2 (1 - δ₀) Q).card :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.zero_le _
  have hdens := hlf Qn hQn_ge1 Q (by linarith) (1 - δ₀) (by linarith) (by linarith)
  have hsub_eq : 1 - (1 - δ₀) = δ₀ := by ring
  rw [hsub_eq] at hdens
  have hbase_le : (Qn : ℝ) ^ 2 * (Q + 2) ≤ 3 * Q ^ 3 := by
    have h1 : (Qn : ℝ) ^ 2 ≤ Q ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hQn_le_Q 2
    have h2 : Q + 2 ≤ 3 * Q := by linarith
    calc (Qn : ℝ) ^ 2 * (Q + 2) ≤ Q ^ 2 * (3 * Q) := by gcongr
      _ = 3 * Q ^ 3 := by ring
  have hbase_ge1 : (1 : ℝ) ≤ (Qn : ℝ) ^ 2 * (Q + 2) := by
    have h1 : (1 : ℝ) ≤ (Qn : ℝ) := by exact_mod_cast hQn_ge1
    nlinarith
  have hrpow_le : ((Qn : ℝ) ^ 2 * (Q + 2)) ^ (A_LF * δ₀) ≤ 3 * Q ^ (1 / 4 : ℝ) := by
    calc ((Qn : ℝ) ^ 2 * (Q + 2)) ^ (A_LF * δ₀)
        ≤ (3 * Q ^ 3) ^ (A_LF * δ₀) := Real.rpow_le_rpow (by positivity) hbase_le (by positivity)
      _ ≤ (3 * Q ^ 3) ^ (1 / 16 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by nlinarith) hδ₀_A
      _ = (3 : ℝ) ^ (1 / 16 : ℝ) * (Q ^ 3) ^ (1 / 16 : ℝ) :=
          Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ 3 * Q ^ (1 / 4 : ℝ) := by
          have h3 : (3 : ℝ) ^ (1 / 16 : ℝ) ≤ 3 := by
            calc (3 : ℝ) ^ (1 / 16 : ℝ) ≤ (3 : ℝ) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 3 := Real.rpow_one 3
          have hQ3 : (Q ^ 3) ^ (1 / 16 : ℝ) ≤ Q ^ (1 / 4 : ℝ) := by
            rw [show Q ^ (3 : ℕ) = Q ^ (3 : ℝ) by norm_cast, ← Real.rpow_mul hQ0.le]
            exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
          exact mul_le_mul h3 hQ3 (by positivity) (by norm_num)
  calc (F.card : ℝ)
      ≤ (Stage11LogFreeDensity.primitiveZeroBoxCount Qn (1 - δ₀) Q : ℝ) := by exact_mod_cast hcard_le
    _ ≤ C_LF * ((Qn : ℝ) ^ 2 * (Q + 2)) ^ (A_LF * δ₀) := hdens
    _ ≤ C_LF * (3 * Q ^ (1 / 4 : ℝ)) := mul_le_mul_of_nonneg_left hrpow_le hCLF_pos.le
    _ = (3 * C_LF) * Q ^ (1 / 4 : ℝ) := by ring

/-- **Unconditional Borel–Carathéodory Log-Derivative Bound from `ZeroFreeBoxDelta`**:
if `0 < δ ≤ 1/4`, `Q ≥ 16`, `q ≤ Q`, `χ ≠ 1`, and `ZeroFreeBoxDelta δ Q χ`, then for every
`s` with `1 - δ / 2 ≤ s.re ≤ 2` and `|s.im| ≤ Q / 2`:
`LFunction χ s ≠ 0` and `‖(-L'/L)(s, χ)‖ ≤ C_ld * Real.log Q` with an explicit `C_ld(δ) > 0`. -/
theorem negLogDerivL_bound_of_zeroFreeBox {δ Q : ℝ} (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4) (hQ : 16 ≤ Q)
    {q : ℕ} [NeZero q] (hqQ : (q : ℝ) ≤ Q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (hbox : ZeroFreeBoxDelta δ Q χ) :
    let C_ld : ℝ := max (8 / δ + 1) ((96 / δ) * (Real.log (512 / δ) + 4))
    ∀ s : ℂ, 1 - δ / 2 ≤ s.re → s.re ≤ 2 → |s.im| ≤ Q / 2 →
      DirichletCharacter.LFunction χ s ≠ 0 ∧
      ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤
        C_ld * Real.log Q := by
  intro C_ld s hre_lo hre_hi him
  have hQ0 : 0 < Q := by linarith
  have hLQ_gt1 : 1 < Real.log Q := by
    have : Real.exp 1 < Q := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) this)
  have hLQ_pos : 0 < Real.log Q := zero_lt_one.trans hLQ_gt1
  have hsnz : DirichletCharacter.LFunction χ s ≠ 0 :=
    hbox s (by linarith) (by linarith [abs_nonneg s.im])
  refine ⟨hsnz, ?_⟩
  by_cases hright : 1 + δ / 8 ≤ s.re
  · have hs_gt1 : 1 < s.re := by linarith
    have hs_eq : (s.re : ℂ) + I * (s.im : ℂ) = s := by
      simp [mul_comm I, Complex.re_add_im]
    have hbd := (Stage5ZetaZeroFree.norm_LFunction_and_inv_and_logDeriv_of_one_lt_re χ hs_gt1 s.im).2.2
    unfold Stage3ZeroFreeRegion.negLogDerivL at hbd
    rw [hs_eq] at hbd
    have hinv : 1 / (s.re - 1) ≤ 8 / δ := by
      rw [div_le_div_iff₀ (by linarith) hδ0]; linarith
    have h1 : 1 / (s.re - 1) + 1 ≤ (8 / δ + 1) * Real.log Q :=
      calc 1 / (s.re - 1) + 1 ≤ 8 / δ + 1 := by linarith
        _ ≤ (8 / δ + 1) * Real.log Q := le_mul_of_one_le_right (by positivity) hLQ_gt1.le
    exact hbd.trans (h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hLQ_pos.le))
  · push Not at hright
    set η : ℝ := δ / 8
    have hη_pos : 0 < η := by positivity
    set R_open : ℝ := 7 * η
    set R : ℝ := 6 * η
    set r : ℝ := 5 * η
    have hR_open_pos : 0 < R_open := by positivity
    have hR_pos : 0 < R := by positivity
    have hrR : r < R := by dsimp only [r, R]; linarith
    set s₀ : ℂ := ((1 + η : ℝ) : ℂ) + I * (s.im : ℂ)
    have hs₀_re : s₀.re = 1 + η := by simp [s₀]
    have hs₀_im : s₀.im = s.im := by simp [s₀]
    have hball_nz : ∀ z ∈ Metric.ball s₀ R_open, DirichletCharacter.LFunction χ z ≠ 0 := by
      intro z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have hre_d := abs_le.mp ((Complex.abs_re_le_norm (z - s₀)).trans hz.le)
      have him_d := abs_le.mp ((Complex.abs_im_le_norm (z - s₀)).trans hz.le)
      rw [Complex.sub_re, hs₀_re] at hre_d
      rw [Complex.sub_im, hs₀_im] at him_d
      have hzim : |z.im| ≤ Q := by
        have htri : |z.im| ≤ |s.im| + |z.im - s.im| := by simpa [add_sub_cancel] using abs_add_le s.im (z.im - s.im)
        have hRo_le : R_open ≤ 1 := by dsimp only [R_open, η]; linarith
        linarith [abs_le.mpr him_d]
      exact hbox z (by dsimp only [R_open, η] at hre_d ⊢; linarith) hzim
    have hball_diff : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) (Metric.ball s₀ R_open) :=
      (DirichletCharacter.differentiable_LFunction hχ).differentiableOn
    obtain ⟨Log, hLog0, hLog_d, hLog_exp⟩ :=
      Stage5ZetaZeroFree.exists_holomorphic_log_ball hR_open_pos hball_diff hball_nz
    have hcb_sub : Metric.closedBall s₀ R ⊆ Metric.ball s₀ R_open :=
      Metric.closedBall_subset_ball (by dsimp only [R, R_open]; linarith)
    have hLog_diff_cb : DifferentiableOn ℂ Log (Metric.closedBall s₀ R) := fun z hz =>
      (hLog_d z (hcb_sub hz)).differentiableAt.differentiableWithinAt
    set M : ℝ := (Real.log (512 / δ) + 4) * Real.log Q
    have hLog_re_le : ∀ z ∈ Metric.closedBall s₀ R, (Log z).re ≤ M := by
      intro z hz
      have hz_ball := hcb_sub hz
      have hznz := hball_nz z hz_ball
      have hs₀_nz := hball_nz s₀ (Metric.mem_ball_self hR_open_pos)
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      have hre_d := abs_le.mp ((Complex.abs_re_le_norm (z - s₀)).trans hz)
      have him_d := abs_le.mp ((Complex.abs_im_le_norm (z - s₀)).trans hz)
      rw [Complex.sub_re, hs₀_re] at hre_d
      rw [Complex.sub_im, hs₀_im] at him_d
      have hR_le : R ≤ 1 / 4 := by dsimp only [R, η]; linarith
      have hz_re_lo : 1 / 2 ≤ z.re := by dsimp only [R, η] at hre_d; linarith
      have hz_im_le : |z.im| ≤ Q := by
        have htri : |z.im| ≤ |s.im| + |z.im - s.im| := by simpa [add_sub_cancel] using abs_add_le s.im (z.im - s.im)
        linarith [abs_le.mpr him_d]
      have hz_bd : ‖DirichletCharacter.LFunction χ z‖ ≤ 4 * Q ^ 2 := by
        have h1 := Stage5DirichletLZeroFree.norm_LFunction_le_of_stepSum_bound hχ (Nat.cast_nonneg q)
          (fun u _ => Stage5DirichletLZeroFree.norm_stepSum_dirichletChar_le_modulus hχ u)
          (by linarith : 0 < z.re)
        calc ‖DirichletCharacter.LFunction χ z‖
            ≤ (q : ℝ) * (z.re + |z.im|) / z.re := h1
          _ ≤ Q * (2 + Q) / (1 / 2) := by
              refine div_le_div₀ (by positivity)
                (mul_le_mul hqQ (by linarith) (by linarith [abs_nonneg z.im]) (by linarith))
                (by norm_num) hz_re_lo
          _ ≤ 4 * Q ^ 2 := by nlinarith
      have hinv_s₀ : ‖1 / DirichletCharacter.LFunction χ s₀‖ ≤ 16 / δ := by
        have h := (Stage5ZetaZeroFree.norm_LFunction_and_inv_and_logDeriv_of_one_lt_re χ
          (by linarith : 1 < 1 + η) s.im).2.1
        have hsub : (1 + η) - 1 = η := by ring
        rw [hsub] at h
        have h2 : (1 + η) / η ≤ 2 / η := div_le_div_of_nonneg_right (by dsimp only [η]; linarith) hη_pos.le
        have h3 : 2 / η = 16 / δ := by dsimp only [η]; field_simp [hδ0.ne']; ring
        exact h.trans (h2.trans h3.le)
      have hratio_le : ‖DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀‖ ≤
          (512 / δ) * Q ^ 2 := by
        rw [show DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀ =
            DirichletCharacter.LFunction χ z * (1 / DirichletCharacter.LFunction χ s₀) by ring, norm_mul]
        calc ‖DirichletCharacter.LFunction χ z‖ * ‖1 / DirichletCharacter.LFunction χ s₀‖
            ≤ (4 * Q ^ 2) * (16 / δ) := mul_le_mul hz_bd hinv_s₀ (norm_nonneg _) (by positivity)
          _ ≤ (512 / δ) * Q ^ 2 := by
              rw [show 4 * Q ^ 2 * (16 / δ) = (64 / δ) * Q ^ 2 by ring]
              have h64 : 64 / δ ≤ 512 / δ := div_le_div_of_nonneg_right (by norm_num) hδ0.le
              exact mul_le_mul_of_nonneg_right h64 (sq_nonneg Q)
      have hre_eq : (Log z).re =
          Real.log ‖DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀‖ := by
        have hexp : Real.exp (Log z).re =
            ‖DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀‖ := by
          rw [← Complex.norm_exp, hLog_exp z hz_ball]
        rw [← hexp, Real.log_exp]
      rw [hre_eq]
      have hratio_pos : 0 < ‖DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀‖ :=
        norm_pos_iff.mpr (div_ne_zero hznz hs₀_nz)
      have h512_gt1 : (1 : ℝ) < 512 / δ := by rw [one_lt_div hδ0]; linarith
      have hlog512_pos : 0 < Real.log (512 / δ) := Real.log_pos h512_gt1
      calc Real.log ‖DirichletCharacter.LFunction χ z / DirichletCharacter.LFunction χ s₀‖
          ≤ Real.log ((512 / δ) * Q ^ 2) := Real.log_le_log hratio_pos hratio_le
        _ = Real.log (512 / δ) + 2 * Real.log Q := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
        _ ≤ Real.log (512 / δ) * Real.log Q + 4 * Real.log Q := by nlinarith
        _ = M := by dsimp only [M]; ring
    have hs_dist : ‖s - s₀‖ ≤ r := by
      have hdiff : s - s₀ = (((s.re - (1 + η) : ℝ) : ℂ)) :=
        Complex.ext (by simp [s₀]) (by simp [s₀])
      rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_le]
      dsimp only [r, η] at hright ⊢
      constructor <;> linarith
    have hbc := Stage5ZetaZeroFree.borelCaratheodory_deriv_le hR_pos hrR hLog_diff_cb hLog_re_le hs_dist
    have hs_ball : s ∈ Metric.ball s₀ R_open :=
      hcb_sub (Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact hs_dist.trans hrR.le))
    rw [(hLog_d s hs_ball).deriv, hLog0, Complex.zero_re, sub_zero] at hbc
    have hcoeff : 2 * R / (R - r) ^ 2 = 96 / δ := by
      dsimp only [R, r, η]; field_simp [hδ0.ne']; ring
    rw [hcoeff] at hbc
    have hneg_norm :
        ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ =
          ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ := by
      rw [neg_div, norm_neg]
    rw [hneg_norm]
    calc ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖
        ≤ (96 / δ) * M := hbc
      _ = ((96 / δ) * (Real.log (512 / δ) + 4)) * Real.log Q := by dsimp only [M]; ring
      _ ≤ C_ld * Real.log Q := mul_le_mul_of_nonneg_right (le_max_right _ _) hLQ_pos.le

/-- **Unconditional Perron Contour-Shift Bound for `Gchi χ u` from `ZeroFreeBoxDelta`**:
given `0 < δ ≤ 1/4`, `Q ≥ 16`, `q ≤ Q`, `χ ≠ 1`, `ZeroFreeBoxDelta δ Q χ`, and `u ≥ 4`,
shifts `Stage4ExplicitFormula.truncatedPerronRamp` across the simple pole at `s = 1` (residue
`-u * L'(χ,1)/L(χ,1)`) to the vertical line `Re(s) = 1 - δ / 2` up to height `T = Q / 2`, proving:
`‖Gchi χ u‖ ≤ C_per * (Real.log Q * u ^ (1 - δ / 2) + u * Real.log u * Real.log Q / Q)`. -/
theorem norm_Gchi_perron_le_of_zeroFreeBox {δ Q u : ℝ}
    (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4) (hQ : 16 ≤ Q) (hu : 4 ≤ u)
    {q : ℕ} [NeZero q] (hqQ : (q : ℝ) ≤ Q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (hbox : ZeroFreeBoxDelta δ Q χ) :
    let C_ld : ℝ := max (8 / δ + 1) ((96 / δ) * (Real.log (512 / δ) + 4))
    let C_per : ℝ := 48 / Real.pi + (4 * C_ld / δ) + 4 * C_ld
    ‖Gchi χ u‖ ≤ C_per * (Real.log Q * u ^ (1 - δ / 2) + u * Real.log u * Real.log Q / Q) := by
  intro C_ld C_per
  have hQ0 : 0 < Q := by linarith
  have hu0 : 0 < u := by linarith
  have hLu_gt1 : 1 < Real.log u := by
    have : Real.exp 1 < u := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) this)
  have hLu_pos : 0 < Real.log u := zero_lt_one.trans hLu_gt1
  have hLQ_gt1 : 1 < Real.log Q := by
    have : Real.exp 1 < Q := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) this)
  have hLQ_pos : 0 < Real.log Q := zero_lt_one.trans hLQ_gt1
  have hCld_pos : 0 < C_ld := lt_of_lt_of_le (by positivity : 0 < 8 / δ + 1) (le_max_left _ _)
  set σ₀ : ℝ := 1 - δ / 2
  set c : ℝ := 1 + 1 / Real.log u
  set T : ℝ := Q / 2
  have hσ₀_gt_half : 1 / 2 < σ₀ := by dsimp only [σ₀]; linarith
  have hσ₀_lt1 : σ₀ < 1 := by dsimp only [σ₀]; linarith
  have hc_gt1 : 1 < c := by dsimp only [c]; linarith [div_pos one_pos hLu_pos]
  have hc_le2 : c ≤ 2 := by
    have : 1 / Real.log u ≤ 1 := (div_le_one hLu_pos).mpr hLu_gt1.le
    dsimp only [c]; linarith
  have hσc : σ₀ < c := by linarith
  have hT_ge8 : 8 ≤ T := by dsimp only [T]; linarith
  have hT_pos : 0 < T := by linarith
  have huc : u ^ c ≤ 3 * u := by
    have h1 : u ^ c = u * u ^ (1 / Real.log u) := by
      rw [show c = (1 : ℝ) + 1 / Real.log u from rfl, Real.rpow_add hu0, Real.rpow_one]
    have h2 : u ^ (1 / Real.log u) = Real.exp 1 := by
      rw [Real.rpow_def_of_pos hu0, mul_one_div_cancel hLu_pos.ne']
    rw [h1, h2]
    calc u * Real.exp 1 ≤ u * 3 :=
          mul_le_mul_of_nonneg_left (by linarith [Real.exp_one_lt_d9]) hu0.le
      _ = 3 * u := mul_comm u 3
  -- (A) Truncation error from `Stage4ExplicitFormula.norm_rampChar_sub_truncatedPerron_le`
  have htrunc : ‖ramp (fun n => χ n) u - Stage4ExplicitFormula.truncatedPerronRamp χ u c T‖ ≤
      (48 / Real.pi) * (u * Real.log u * Real.log Q / Q) := by
    have h0 := Stage4ExplicitFormula.norm_rampChar_sub_truncatedPerron_le χ hu0 hc_gt1 hT_pos
    have hcm1 : c - 1 = 1 / Real.log u := by dsimp only [c]; ring
    have hden : (c - 1) * T = Q / (2 * Real.log u) := by rw [hcm1]; dsimp only [T]; ring
    have h6c : 6 * c / Real.pi ≤ 12 / Real.pi :=
      div_le_div_of_nonneg_right (by linarith) Real.pi_pos.le
    calc ‖ramp (fun n => χ n) u - Stage4ExplicitFormula.truncatedPerronRamp χ u c T‖
        ≤ (6 * c / Real.pi) * u ^ c / ((c - 1) * T) := h0
      _ ≤ (12 / Real.pi) * (3 * u) / (Q / (2 * Real.log u)) := by
          rw [hden]
          have hpos_d : 0 < Q / (2 * Real.log u) := by positivity
          exact div_le_div_of_nonneg_right
            (mul_le_mul h6c huc (Real.rpow_nonneg hu0.le _) (by positivity)) hpos_d.le
      _ = (72 / Real.pi) * (u * Real.log u / Q) := by field_simp [Real.pi_ne_zero, hQ0.ne', hLu_pos.ne']; ring
      _ ≤ (48 / Real.pi) * (u * Real.log u * Real.log Q / Q) := by
          have hlog16 : (2 : ℝ) ≤ Real.log Q := by
            have he2 : Real.exp 2 ≤ 16 := by
              have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
              rw [hsq]; nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
            exact (Real.log_exp 2).symm.trans_le (Real.log_le_log (Real.exp_pos 2) (he2.trans hQ))
          have hnn : 0 ≤ u * Real.log u / Q := by positivity
          have h72 : 72 / Real.pi ≤ 48 / Real.pi * Real.log Q := by
            have : (72 : ℝ) ≤ 48 * Real.log Q := by linarith
            rw [div_mul_eq_mul_div]
            exact div_le_div_of_nonneg_right this Real.pi_pos.le
          calc (72 / Real.pi) * (u * Real.log u / Q)
              ≤ (48 / Real.pi * Real.log Q) * (u * Real.log u / Q) :=
                mul_le_mul_of_nonneg_right h72 hnn
            _ = (48 / Real.pi) * (u * Real.log u * Real.log Q / Q) := by ring
  -- (B) Log-derivative bound on the closed rectangle `[σ₀, c] × [-T, T]`
  have hrect_bd : ∀ z ∈ Stage5ContourExplicit.closedRect σ₀ c (-T) T,
      DirichletCharacter.LFunction χ z ≠ 0 ∧
      ‖Stage3ZeroFreeRegion.negLogDerivL χ z‖ ≤ C_ld * Real.log Q := by
    intro z hz
    have hre1 : σ₀ ≤ z.re := hz.1.1
    have hre2 : z.re ≤ c := hz.1.2
    have him1 : |z.im| ≤ T := abs_le.mpr hz.2
    exact negLogDerivL_bound_of_zeroFreeBox hδ0 hδ4 hQ hqQ hχ hbox z hre1 (hre2.trans hc_le2) him1
  -- (C) Vertical contour shift via `Stage5ContourExplicit.vertical_contour_shift_mul_eq_sum_residues`
  let Lfn : ℂ → ℂ := fun s => (s - 1)⁻¹
  let Wfn : ℂ → ℂ := fun s =>
    Stage3ZeroFreeRegion.negLogDerivL χ s * (u : ℂ) ^ s / s
  have hLdiff : DifferentiableOn ℂ (fun s => Lfn s - ∑ _j ∈ ({()} : Finset Unit), (1 : ℂ) / (s - 1))
      (Stage5ContourExplicit.closedRect σ₀ c (-T) T) := by
    have hzero : (fun s : ℂ => Lfn s - ∑ _j ∈ ({()} : Finset Unit), (1 : ℂ) / (s - 1)) = fun _ => 0 := by
      ext s; simp [Lfn, one_div]
    rw [hzero]
    exact differentiableOn_const 0
  have hWdiff : DifferentiableOn ℂ Wfn (Stage5ContourExplicit.closedRect σ₀ c (-T) T) := by
    intro z hz
    have hLnz : DirichletCharacter.LFunction χ z ≠ 0 := (hrect_bd z hz).1
    have hznz : z ≠ 0 := fun h => by subst h; have := hz.1.1; simp at this; linarith
    have hLd : DifferentiableAt ℂ (DirichletCharacter.LFunction χ) z :=
      DirichletCharacter.differentiable_LFunction hχ z
    have hL'd : DifferentiableAt ℂ (deriv (DirichletCharacter.LFunction χ)) z :=
      (DirichletCharacter.differentiable_LFunction hχ).deriv z
    have hnegd : DifferentiableAt ℂ (Stage3ZeroFreeRegion.negLogDerivL χ) z := by
      unfold Stage3ZeroFreeRegion.negLogDerivL
      exact hL'd.neg.div hLd hLnz
    have huC : (u : ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
    have hpowd : DifferentiableAt ℂ (fun s : ℂ => (u : ℂ) ^ s) z := by
      have hEq : (fun s : ℂ => (u : ℂ) ^ s) = fun s => cexp (Complex.log (u : ℂ) * s) :=
        funext fun s => Complex.cpow_def_of_ne_zero huC s
      rw [hEq]; fun_prop
    exact ((hnegd.mul hpowd).div differentiableAt_id hznz).differentiableWithinAt
  have hshift := Stage5ContourExplicit.vertical_contour_shift_mul_eq_sum_residues
    Lfn Wfn hσc hT_pos ({()} : Finset Unit) (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ))
    (fun _ _ => ⟨⟨hσ₀_lt1, hc_gt1⟩, ⟨by simp; linarith, by simp; linarith⟩⟩)
    hLdiff hWdiff
  have hF_eq : ∀ s : ℂ, Lfn s * Wfn s =
      Stage3ZeroFreeRegion.negLogDerivL χ s * (u : ℂ) ^ s / (s * (s - 1)) := fun s => by
    dsimp only [Lfn, Wfn]
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
    ring
  have hLHS_eq : ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      (∫ t in (-T)..T, Lfn ((c : ℂ) + I * (t : ℂ)) * Wfn ((c : ℂ) + I * (t : ℂ))) =
      Stage4ExplicitFormula.truncatedPerronRamp χ u c T := by
    unfold Stage4ExplicitFormula.truncatedPerronRamp
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [hF_eq]; congr 1; ring
  have hRes_eq : ∑ _j ∈ ({()} : Finset Unit), (1 : ℂ) * Wfn 1 =
      -(u : ℂ) * (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1) := by
    simp only [Finset.sum_singleton, one_mul, Wfn, Stage3ZeroFreeRegion.negLogDerivL,
      Complex.cpow_one, div_one]
    ring
  rw [hLHS_eq, hRes_eq] at hshift
  -- `Gchi χ u = (ramp - truncatedPerronRamp) + (left vertical) + (top horiz) - (bot horiz)`
  have hGchi_eq : Gchi χ u =
      (ramp (fun n => χ n) u - Stage4ExplicitFormula.truncatedPerronRamp χ u c T) +
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        (∫ t in (-T)..T, Lfn ((σ₀ : ℂ) + I * (t : ℂ)) * Wfn ((σ₀ : ℂ) + I * (t : ℂ))) +
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        (∫ σ in σ₀..c, Lfn ((σ : ℂ) + I * (T : ℂ)) * Wfn ((σ : ℂ) + I * (T : ℂ))) -
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        (∫ σ in σ₀..c, Lfn ((σ : ℂ) - I * (T : ℂ)) * Wfn ((σ : ℂ) - I * (T : ℂ))) := by
    unfold Gchi
    rw [if_neg hχ]
    linear_combination hshift
  -- (D) Bound left vertical integral along `Re(s) = σ₀`
  have hleft_bd :
      ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        (∫ t in (-T)..T, Lfn ((σ₀ : ℂ) + I * (t : ℂ)) * Wfn ((σ₀ : ℂ) + I * (t : ℂ)))‖ ≤
        (4 * C_ld / δ) * (Real.log Q * u ^ σ₀) := by
    have hpt : ∀ t ∈ Set.Ioc (-T) T,
        ‖Lfn ((σ₀ : ℂ) + I * (t : ℂ)) * Wfn ((σ₀ : ℂ) + I * (t : ℂ))‖ ≤
          (C_ld * Real.log Q * u ^ σ₀) * (2 / δ) * (1 / (1 / 4 + t ^ 2)) := by
      intro t ht
      have hmem : (σ₀ : ℂ) + I * (t : ℂ) ∈ Stage5ContourExplicit.closedRect σ₀ c (-T) T :=
        ⟨⟨by simp, by simp [hσc.le]⟩, ⟨by simp; linarith [ht.1], by simp; exact ht.2⟩⟩
      rw [hF_eq, norm_div, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
      have hre : ((σ₀ : ℂ) + I * (t : ℂ)).re = σ₀ := by simp
      rw [hre]
      have hld := (hrect_bd _ hmem).2
      have hden1 : Real.sqrt (1 / 4 + t ^ 2) ≤ ‖(σ₀ : ℂ) + I * (t : ℂ)‖ := by
        rw [Complex.norm_def, Complex.normSq_apply]
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, zero_mul,
          Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero,
          Complex.add_im, Complex.mul_im, one_mul, zero_add]
        exact Real.sqrt_le_sqrt (by nlinarith)
      have hden2 : (δ / 2) * Real.sqrt (1 / 4 + t ^ 2) ≤ ‖((σ₀ : ℂ) + I * (t : ℂ)) - 1‖ := by
        have h1 : (δ / 2) ^ 2 * (1 / 4 + t ^ 2) ≤ (σ₀ - 1) ^ 2 + t ^ 2 := by
          have hδ1 : (δ / 2) ^ 2 ≤ 1 := by nlinarith
          have hsub : (σ₀ - 1) ^ 2 = (δ / 2) ^ 2 := by dsimp only [σ₀]; ring
          rw [hsub]; nlinarith [sq_nonneg t]
        have hsq : ((δ / 2) * Real.sqrt (1 / 4 + t ^ 2)) ^ 2 ≤ ‖((σ₀ : ℂ) + I * (t : ℂ)) - 1‖ ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by positivity), ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
          simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
            zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero, Complex.one_re,
            Complex.sub_im, Complex.add_im, Complex.mul_im, one_mul, zero_add, Complex.one_im, sub_zero]
          linarith
        exact le_of_sq_le_sq hsq (norm_nonneg _)
      have hprod_den : (δ / 2) * (1 / 4 + t ^ 2) ≤
          ‖(σ₀ : ℂ) + I * (t : ℂ)‖ * ‖((σ₀ : ℂ) + I * (t : ℂ)) - 1‖ := by
        have hpos_s : 0 ≤ Real.sqrt (1 / 4 + t ^ 2) := Real.sqrt_nonneg _
        calc (δ / 2) * (1 / 4 + t ^ 2)
            = Real.sqrt (1 / 4 + t ^ 2) * ((δ / 2) * Real.sqrt (1 / 4 + t ^ 2)) := by
                rw [mul_left_comm, Real.mul_self_sqrt (by positivity)]
          _ ≤ ‖(σ₀ : ℂ) + I * (t : ℂ)‖ * ‖((σ₀ : ℂ) + I * (t : ℂ)) - 1‖ :=
                mul_le_mul hden1 hden2 (by positivity) (norm_nonneg _)
      calc ‖Stage3ZeroFreeRegion.negLogDerivL χ ((σ₀ : ℂ) + I * (t : ℂ))‖ * u ^ σ₀ /
              (‖(σ₀ : ℂ) + I * (t : ℂ)‖ * ‖((σ₀ : ℂ) + I * (t : ℂ)) - 1‖)
          ≤ (C_ld * Real.log Q * u ^ σ₀) / ((δ / 2) * (1 / 4 + t ^ 2)) :=
              div_le_div₀ (by positivity)
                (mul_le_mul_of_nonneg_right hld (Real.rpow_nonneg hu0.le _))
                (by positivity) hprod_den
        _ = (C_ld * Real.log Q * u ^ σ₀) * (2 / δ) * (1 / (1 / 4 + t ^ 2)) := by
              field_simp [hδ0.ne', show (1 / 4 : ℝ) + t ^ 2 ≠ 0 by positivity]
    have hint_g : IntervalIntegrable (fun t : ℝ => (C_ld * Real.log Q * u ^ σ₀) * (2 / δ) * (1 / (1 / 4 + t ^ 2)))
        volume (-T) T := by
      refine Continuous.intervalIntegrable ?_ (-T) T
      exact continuous_const.mul (continuous_const.div (continuous_const.add (continuous_pow 2))
        (fun t => by positivity))
    have hint_val : ∫ t in (-T)..T, (1 : ℝ) / (1 / 4 + t ^ 2) ≤ 2 * Real.pi := by
      have hderiv : ∀ t : ℝ, HasDerivAt (fun x : ℝ => 2 * Real.arctan (2 * x)) (1 / (1 / 4 + t ^ 2)) t := by
        intro t
        have h1 : HasDerivAt (fun x : ℝ => 2 * x) 2 t := by simpa using (hasDerivAt_id t).const_mul 2
        have h2 := (Real.hasDerivAt_arctan (2 * t)).comp t h1
        have h3 := h2.const_mul 2
        refine h3.congr_deriv ?_
        field_simp [show (1 / 4 : ℝ) + t ^ 2 ≠ 0 by positivity, show (1 : ℝ) + (2 * t) ^ 2 ≠ 0 by positivity]
        ring
      have hcont : Continuous (fun t : ℝ => (1 : ℝ) / (1 / 4 + t ^ 2)) :=
        continuous_const.div (continuous_const.add (continuous_pow 2)) (fun t => by positivity)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) (hcont.intervalIntegrable _ _)]
      have h1 := Real.arctan_lt_pi_div_two (2 * T)
      have h2 := Real.neg_pi_div_two_lt_arctan (2 * (-T))
      linarith
    have hnorm_int :
        ‖∫ t in (-T)..T, Lfn ((σ₀ : ℂ) + I * (t : ℂ)) * Wfn ((σ₀ : ℂ) + I * (t : ℂ))‖ ≤
          (C_ld * Real.log Q * u ^ σ₀) * (2 / δ) * (2 * Real.pi) := by
      have h1 := intervalIntegral.norm_integral_le_of_norm_le (show -T ≤ T by linarith)
        (Filter.Eventually.of_forall hpt) hint_g
      rw [intervalIntegral.integral_const_mul] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left hint_val (by positivity))
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    calc (2 * Real.pi)⁻¹ *
          ‖∫ t in (-T)..T, Lfn ((σ₀ : ℂ) + I * (t : ℂ)) * Wfn ((σ₀ : ℂ) + I * (t : ℂ))‖
        ≤ (2 * Real.pi)⁻¹ * ((C_ld * Real.log Q * u ^ σ₀) * (2 / δ) * (2 * Real.pi)) :=
          mul_le_mul_of_nonneg_left hnorm_int (by positivity)
      _ = (2 * C_ld / δ) * (Real.log Q * u ^ σ₀) := by field_simp [Real.pi_ne_zero, hδ0.ne']
      _ ≤ (4 * C_ld / δ) * (Real.log Q * u ^ σ₀) :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by linarith) hδ0.le) (by positivity)
  -- (E) Bound top and bottom horizontal integrals along `Im(s) = ± T`
  have hhoriz_bd : ∀ sgn : ℝ, sgn = 1 ∨ sgn = -1 →
      ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
        (∫ σ in σ₀..c, Lfn ((σ : ℂ) + I * ((sgn * T : ℝ) : ℂ)) *
          Wfn ((σ : ℂ) + I * ((sgn * T : ℝ) : ℂ)))‖ ≤
        2 * C_ld * (u * Real.log u * Real.log Q / Q) := by
    intro sgn hsgn
    have hsgn_abs : |sgn * T| = T := by
      rw [abs_mul, abs_of_pos hT_pos]
      rcases hsgn with rfl | rfl <;> simp
    have hpt : ∀ σ ∈ Set.uIoc σ₀ c,
        ‖Lfn ((σ : ℂ) + I * ((sgn * T : ℝ) : ℂ)) * Wfn ((σ : ℂ) + I * ((sgn * T : ℝ) : ℂ))‖ ≤
          C_ld * Real.log Q * (3 * u) / T ^ 2 := by
      intro σ hσ
      rw [Set.uIoc_of_le hσc.le] at hσ
      have hmem : (σ : ℂ) + I * ((sgn * T : ℝ) : ℂ) ∈ Stage5ContourExplicit.closedRect σ₀ c (-T) T := by
        refine ⟨⟨by simp [hσ.1.le], by simp [hσ.2]⟩, ?_⟩
        change ((σ : ℂ) + I * ((sgn * T : ℝ) : ℂ)).im ∈ Set.Icc (-T) T
        have him : ((σ : ℂ) + I * ((sgn * T : ℝ) : ℂ)).im = sgn * T := by simp
        rw [him]
        exact abs_le.mp (le_of_eq hsgn_abs)
      rw [hF_eq, norm_div, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0]
      have hre : ((σ : ℂ) + I * ((sgn * T : ℝ) : ℂ)).re = σ := by simp
      rw [hre]
      have huσ : u ^ σ ≤ 3 * u :=
        (Real.rpow_le_rpow_of_exponent_le (by linarith) hσ.2).trans huc
      have hden1 : T ≤ ‖(σ : ℂ) + I * ((sgn * T : ℝ) : ℂ)‖ := by
        have h1 := Complex.abs_im_le_norm ((σ : ℂ) + I * ((sgn * T : ℝ) : ℂ))
        simpa [hsgn_abs] using h1
      have hden2 : T ≤ ‖((σ : ℂ) + I * ((sgn * T : ℝ) : ℂ)) - 1‖ := by
        have h1 := Complex.abs_im_le_norm (((σ : ℂ) + I * ((sgn * T : ℝ) : ℂ)) - 1)
        simpa [hsgn_abs] using h1
      have hprod : T ^ 2 ≤ ‖(σ : ℂ) + I * ((sgn * T : ℝ) : ℂ)‖ *
          ‖((σ : ℂ) + I * ((sgn * T : ℝ) : ℂ)) - 1‖ := by
        rw [sq]; exact mul_le_mul hden1 hden2 hT_pos.le (norm_nonneg _)
      exact div_le_div₀ (by positivity)
        (mul_le_mul (hrect_bd _ hmem).2 huσ (Real.rpow_nonneg hu0.le _) (by positivity))
        (sq_pos_of_pos hT_pos) hprod
    have hnorm_int := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    rw [abs_of_pos (sub_pos.mpr hσc)] at hnorm_int
    have hlen : c - σ₀ ≤ 2 := by dsimp only [c, σ₀]; linarith
    have hinv_norm : ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ ≤ 1 := by
      rw [norm_inv, norm_mul, norm_mul, Complex.norm_two, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one]
      exact inv_le_one_of_one_le₀ (by linarith [Real.pi_gt_three])
    rw [norm_mul]
    calc ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
          ‖∫ σ in σ₀..c, Lfn ((σ : ℂ) + I * ((sgn * T : ℝ) : ℂ)) *
            Wfn ((σ : ℂ) + I * ((sgn * T : ℝ) : ℂ))‖
        ≤ 1 * (C_ld * Real.log Q * (3 * u) / T ^ 2 * (c - σ₀)) :=
          mul_le_mul hinv_norm hnorm_int (norm_nonneg _) zero_le_one
      _ ≤ C_ld * Real.log Q * (3 * u) / T ^ 2 * 2 := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_left hlen (by positivity)
      _ = 24 * C_ld * Real.log Q * u / Q ^ 2 := by
          dsimp only [T]; field_simp [hQ0.ne']; ring
      _ ≤ 2 * C_ld * (u * Real.log u * Real.log Q / Q) := by
          have h24 : 24 / Q ≤ 2 * Real.log u := by
            have h1 : 24 / Q ≤ 24 / 16 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hQ
            linarith
          have hEq : 24 * C_ld * Real.log Q * u / Q ^ 2 = (24 / Q) * (C_ld * u * Real.log Q / Q) := by
            field_simp [hQ0.ne']
          rw [hEq]
          calc (24 / Q) * (C_ld * u * Real.log Q / Q)
              ≤ (2 * Real.log u) * (C_ld * u * Real.log Q / Q) :=
                mul_le_mul_of_nonneg_right h24 (by positivity)
            _ = 2 * C_ld * (u * Real.log u * Real.log Q / Q) := by ring
  have htop := hhoriz_bd 1 (Or.inl rfl)
  have hbot := hhoriz_bd (-1) (Or.inr rfl)
  simp only [one_mul, neg_mul, Complex.ofReal_neg, mul_neg] at htop hbot
  have hbot' :
      ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
        (∫ σ in σ₀..c, Lfn ((σ : ℂ) - I * (T : ℂ)) * Wfn ((σ : ℂ) - I * (T : ℂ)))‖ ≤
        2 * C_ld * (u * Real.log u * Real.log Q / Q) := by
    simpa only [sub_eq_add_neg] using hbot
  -- Combine all four pieces
  rw [hGchi_eq]
  have htri1 := norm_sub_le
    ((ramp (fun n => χ n) u - Stage4ExplicitFormula.truncatedPerronRamp χ u c T) +
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        (∫ t in (-T)..T, Lfn ((σ₀ : ℂ) + I * (t : ℂ)) * Wfn ((σ₀ : ℂ) + I * (t : ℂ))) +
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        (∫ σ in σ₀..c, Lfn ((σ : ℂ) + I * (T : ℂ)) * Wfn ((σ : ℂ) + I * (T : ℂ))))
    ((2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ σ in σ₀..c, Lfn ((σ : ℂ) - I * (T : ℂ)) * Wfn ((σ : ℂ) - I * (T : ℂ))))
  have htri2 := norm_add_le
    ((ramp (fun n => χ n) u - Stage4ExplicitFormula.truncatedPerronRamp χ u c T) +
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        (∫ t in (-T)..T, Lfn ((σ₀ : ℂ) + I * (t : ℂ)) * Wfn ((σ₀ : ℂ) + I * (t : ℂ))))
    ((2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ σ in σ₀..c, Lfn ((σ : ℂ) + I * (T : ℂ)) * Wfn ((σ : ℂ) + I * (T : ℂ))))
  have htri3 := norm_add_le
    (ramp (fun n => χ n) u - Stage4ExplicitFormula.truncatedPerronRamp χ u c T)
    (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      (∫ t in (-T)..T, Lfn ((σ₀ : ℂ) + I * (t : ℂ)) * Wfn ((σ₀ : ℂ) + I * (t : ℂ))))
  have hnnA : 0 ≤ Real.log Q * u ^ σ₀ := by positivity
  have hnnB : 0 ≤ u * Real.log u * Real.log Q / Q := by positivity
  have hsum4 :
      ‖ramp (fun n => χ n) u - Stage4ExplicitFormula.truncatedPerronRamp χ u c T‖ +
      ‖((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        (∫ t in (-T)..T, Lfn ((σ₀ : ℂ) + I * (t : ℂ)) * Wfn ((σ₀ : ℂ) + I * (t : ℂ)))‖ +
      ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
        (∫ σ in σ₀..c, Lfn ((σ : ℂ) + I * (T : ℂ)) * Wfn ((σ : ℂ) + I * (T : ℂ)))‖ +
      ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
        (∫ σ in σ₀..c, Lfn ((σ : ℂ) - I * (T : ℂ)) * Wfn ((σ : ℂ) - I * (T : ℂ)))‖ ≤
      C_per * (Real.log Q * u ^ σ₀ + u * Real.log u * Real.log Q / Q) := by
    have hA_le : (4 * C_ld / δ) * (Real.log Q * u ^ σ₀) ≤ C_per * (Real.log Q * u ^ σ₀) := by
      refine mul_le_mul_of_nonneg_right ?_ hnnA
      dsimp only [C_per]
      have h1 : 0 ≤ 48 / Real.pi := by positivity
      have h2 : 0 ≤ 4 * C_ld := by positivity
      linarith
    have hB_le : (48 / Real.pi + 4 * C_ld) * (u * Real.log u * Real.log Q / Q) ≤
        C_per * (u * Real.log u * Real.log Q / Q) := by
      refine mul_le_mul_of_nonneg_right ?_ hnnB
      dsimp only [C_per]
      have h1 : 0 ≤ 4 * C_ld / δ := by positivity
      linarith
    calc _ ≤ (48 / Real.pi) * (u * Real.log u * Real.log Q / Q) +
            (4 * C_ld / δ) * (Real.log Q * u ^ σ₀) +
            2 * C_ld * (u * Real.log u * Real.log Q / Q) +
            2 * C_ld * (u * Real.log u * Real.log Q / Q) := by
              linarith [htrunc, hleft_bd, htop, hbot']
      _ = (4 * C_ld / δ) * (Real.log Q * u ^ σ₀) +
          (48 / Real.pi + 4 * C_ld) * (u * Real.log u * Real.log Q / Q) := by ring
      _ ≤ C_per * (Real.log Q * u ^ σ₀) + C_per * (u * Real.log u * Real.log Q / Q) :=
          add_le_add hA_le hB_le
      _ = C_per * (Real.log Q * u ^ σ₀ + u * Real.log u * Real.log Q / Q) := by ring
  linarith [htri1, htri2, htri3, hsum4]

/-- Truncated weighted von Mangoldt sum `Sz χ y Z = ∑_{n=1}^{⌊Z⌋₊} cN(y, n) * χ(n)` matching
`MeanSquareBounds.S` and `ZeroDensityWindow.cN`. -/
def Sz {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y Z : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊Z⌋₊,
    ((ZeroDensityWindow.cN y n : ℝ) : ℂ) * χ (n : ZMod N)

/-- **Exact Finite-Difference Truncation Identity (`Gchi_add_Sz_eq_diff`, `0` Measure Theory!)**:
for EVERY non-principal `χ ≠ 1`, `0 < y ≤ Z`, and `0 < h`:
1. `Gchi χ y + Sz χ y Z = (y : ℂ) * (∑_{n=1}^{⌊Z⌋₊} Λ(n) χ(n) / n + L'(χ, 1) / L(χ, 1))`, and
2. `∑_{n=1}^{⌊Z⌋₊} Λ(n) χ(n) / n + L'(χ, 1) / L(χ, 1) = (Gchi χ (Z + h) - Gchi χ Z) / h - (1 / h) * ∑_{n ∈ Ioc ⌊Z⌋₊ ⌊Z + h⌋₊} Λ(n) χ(n) ((Z + h) / n - 1)`. -/
theorem Gchi_add_Sz_eq_diff {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    {y Z h : ℝ} (hy : 0 < y) (hyZ : y ≤ Z) (hh : 0 < h) :
    (Gchi χ y + Sz χ y Z =
      (y : ℂ) * ((∑ n ∈ Finset.Icc 1 ⌊Z⌋₊, (Λ n : ℂ) * χ (n : ZMod N) / (n : ℂ)) +
        deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1)) ∧
    ((∑ n ∈ Finset.Icc 1 ⌊Z⌋₊, (Λ n : ℂ) * χ (n : ZMod N) / (n : ℂ)) +
        deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1 =
      (Gchi χ (Z + h) - Gchi χ Z) / (h : ℂ) -
        ((h : ℂ))⁻¹ * ∑ n ∈ Finset.Ioc ⌊Z⌋₊ ⌊Z + h⌋₊,
          (Λ n : ℂ) * χ (n : ZMod N) * (((Z + h) / (n : ℝ) - 1 : ℝ) : ℂ)) := by
  have hZ0 : 0 < Z := lt_of_lt_of_le hy hyZ
  have hfl_yZ : ⌊y⌋₊ ≤ ⌊Z⌋₊ := Nat.floor_mono hyZ
  have hfl_Zh : ⌊Z⌋₊ ≤ ⌊Z + h⌋₊ := Nat.floor_mono (by linarith)
  -- Helper: `ramp (fun n => χ n) u = ∑ n ∈ Icc 1 ⌊u⌋₊, Λ n * χ n * (u / n - 1)` for `u > 0`
  have hramp_Icc : ∀ u : ℝ, 0 < u →
      ramp (fun n => χ n) u =
        ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, (Λ n : ℂ) * χ (n : ZMod N) * ((u / (n : ℝ) - 1 : ℝ) : ℂ) := by
    intro u hu
    unfold ramp
    have hsplit : Finset.range (⌊u⌋₊ + 1) = insert 0 (Finset.Icc 1 ⌊u⌋₊) := by
      ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hsplit, Finset.sum_insert (by simp)]
    simp only [ArithmeticFunction.map_zero, Complex.ofReal_zero, zero_mul, zero_add]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hn_le : (n : ℝ) ≤ u :=
      (by exact_mod_cast (Finset.mem_Icc.mp hn).2 : (n : ℝ) ≤ (⌊u⌋₊ : ℝ)).trans (Nat.floor_le hu.le)
    have hge : 0 ≤ u / (n : ℝ) - 1 := by rw [sub_nonneg, one_le_div hn_pos]; exact hn_le
    rw [max_eq_left hge]
  constructor
  · -- Part 1: `Gchi χ y + Sz χ y Z`
    unfold Gchi Sz
    rw [if_neg hχ, hramp_Icc y hy]
    have hsplit_Z :
        ∑ n ∈ Finset.Icc 1 ⌊Z⌋₊, ((ZeroDensityWindow.cN y n : ℝ) : ℂ) * χ (n : ZMod N) =
          (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ((ZeroDensityWindow.cN y n : ℝ) : ℂ) * χ (n : ZMod N)) +
          (∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊Z⌋₊, ((ZeroDensityWindow.cN y n : ℝ) : ℂ) * χ (n : ZMod N)) := by
      have hunion : Finset.Icc 1 ⌊Z⌋₊ = Finset.Icc 1 ⌊y⌋₊ ∪ Finset.Ioc ⌊y⌋₊ ⌊Z⌋₊ := by
        ext n; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]; omega
      have hdisj : Disjoint (Finset.Icc 1 ⌊y⌋₊) (Finset.Ioc ⌊y⌋₊ ⌊Z⌋₊) := by
        rw [Finset.disjoint_left]; intro n h1 h2
        simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2; omega
      rw [hunion, Finset.sum_union hdisj]
    have hlo_sum :
        ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ((ZeroDensityWindow.cN y n : ℝ) : ℂ) * χ (n : ZMod N) =
          ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (Λ n : ℂ) * χ (n : ZMod N) := by
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hn_le : (n : ℝ) ≤ y :=
        (by exact_mod_cast (Finset.mem_Icc.mp hn).2 : (n : ℝ) ≤ (⌊y⌋₊ : ℝ)).trans (Nat.floor_le hy.le)
      have hmin : min 1 (y / (n : ℝ)) = 1 := min_eq_left ((one_le_div hn_pos).mpr hn_le)
      unfold ZeroDensityWindow.cN
      rw [hmin, mul_one]
    have hhi_sum :
        ∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊Z⌋₊, ((ZeroDensityWindow.cN y n : ℝ) : ℂ) * χ (n : ZMod N) =
          (y : ℂ) * ∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊Z⌋₊, (Λ n : ℂ) * χ (n : ZMod N) / (n : ℂ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hgt : ⌊y⌋₊ < n := (Finset.mem_Ioc.mp hn).1
      have hyn : y < (n : ℝ) := lt_of_lt_of_le (Nat.lt_floor_add_one y) (by exact_mod_cast hgt)
      have hn_pos : (0 : ℝ) < (n : ℝ) := lt_trans hy hyn
      have hmin : min 1 (y / (n : ℝ)) = y / (n : ℝ) := min_eq_right ((div_le_one hn_pos).mpr hyn.le)
      unfold ZeroDensityWindow.cN
      rw [hmin]
      push_cast
      ring
    have hcomb_lo :
        (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (Λ n : ℂ) * χ (n : ZMod N) * ((y / (n : ℝ) - 1 : ℝ) : ℂ)) +
          (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (Λ n : ℂ) * χ (n : ZMod N)) =
          (y : ℂ) * ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (Λ n : ℂ) * χ (n : ZMod N) / (n : ℂ) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      push_cast; ring
    have hsplit_RHS :
        ∑ n ∈ Finset.Icc 1 ⌊Z⌋₊, (Λ n : ℂ) * χ (n : ZMod N) / (n : ℂ) =
          (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (Λ n : ℂ) * χ (n : ZMod N) / (n : ℂ)) +
          (∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊Z⌋₊, (Λ n : ℂ) * χ (n : ZMod N) / (n : ℂ)) := by
      have hunion : Finset.Icc 1 ⌊Z⌋₊ = Finset.Icc 1 ⌊y⌋₊ ∪ Finset.Ioc ⌊y⌋₊ ⌊Z⌋₊ := by
        ext n; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]; omega
      have hdisj : Disjoint (Finset.Icc 1 ⌊y⌋₊) (Finset.Ioc ⌊y⌋₊ ⌊Z⌋₊) := by
        rw [Finset.disjoint_left]; intro n h1 h2
        simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2; omega
      rw [hunion, Finset.sum_union hdisj]
    rw [hsplit_Z, hlo_sum, hhi_sum, hsplit_RHS]
    linear_combination hcomb_lo
  · -- Part 2: Finite difference `(Gchi χ (Z + h) - Gchi χ Z) / h`
    have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
    unfold Gchi
    rw [if_neg hχ, if_neg hχ, hramp_Icc (Z + h) (by linarith), hramp_Icc Z hZ0]
    have hsplit_Zh :
        ∑ n ∈ Finset.Icc 1 ⌊Z + h⌋₊,
            (Λ n : ℂ) * χ (n : ZMod N) * (((Z + h) / (n : ℝ) - 1 : ℝ) : ℂ) =
          (∑ n ∈ Finset.Icc 1 ⌊Z⌋₊,
            (Λ n : ℂ) * χ (n : ZMod N) * (((Z + h) / (n : ℝ) - 1 : ℝ) : ℂ)) +
          (∑ n ∈ Finset.Ioc ⌊Z⌋₊ ⌊Z + h⌋₊,
            (Λ n : ℂ) * χ (n : ZMod N) * (((Z + h) / (n : ℝ) - 1 : ℝ) : ℂ)) := by
      have hunion : Finset.Icc 1 ⌊Z + h⌋₊ = Finset.Icc 1 ⌊Z⌋₊ ∪ Finset.Ioc ⌊Z⌋₊ ⌊Z + h⌋₊ := by
        ext n; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]; omega
      have hdisj : Disjoint (Finset.Icc 1 ⌊Z⌋₊) (Finset.Ioc ⌊Z⌋₊ ⌊Z + h⌋₊) := by
        rw [Finset.disjoint_left]; intro n h1 h2
        simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2; omega
      rw [hunion, Finset.sum_union hdisj]
    have hsub_Z :
        (∑ n ∈ Finset.Icc 1 ⌊Z⌋₊,
            (Λ n : ℂ) * χ (n : ZMod N) * (((Z + h) / (n : ℝ) - 1 : ℝ) : ℂ)) -
          (∑ n ∈ Finset.Icc 1 ⌊Z⌋₊,
            (Λ n : ℂ) * χ (n : ZMod N) * ((Z / (n : ℝ) - 1 : ℝ) : ℂ)) =
          (h : ℂ) * ∑ n ∈ Finset.Icc 1 ⌊Z⌋₊, (Λ n : ℂ) * χ (n : ZMod N) / (n : ℂ) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      push_cast; ring
    rw [hsplit_Zh]
    have hnum :
        ((∑ n ∈ Finset.Icc 1 ⌊Z⌋₊,
            (Λ n : ℂ) * χ (n : ZMod N) * (((Z + h) / (n : ℝ) - 1 : ℝ) : ℂ)) +
          (∑ n ∈ Finset.Ioc ⌊Z⌋₊ ⌊Z + h⌋₊,
            (Λ n : ℂ) * χ (n : ZMod N) * (((Z + h) / (n : ℝ) - 1 : ℝ) : ℂ)) +
          ((Z + h : ℝ) : ℂ) *
            (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1)) -
        ((∑ n ∈ Finset.Icc 1 ⌊Z⌋₊,
            (Λ n : ℂ) * χ (n : ZMod N) * ((Z / (n : ℝ) - 1 : ℝ) : ℂ)) +
          (Z : ℂ) *
            (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1)) =
        (h : ℂ) * ((∑ n ∈ Finset.Icc 1 ⌊Z⌋₊, (Λ n : ℂ) * χ (n : ZMod N) / (n : ℂ)) +
            deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1) +
          ∑ n ∈ Finset.Ioc ⌊Z⌋₊ ⌊Z + h⌋₊,
            (Λ n : ℂ) * χ (n : ZMod N) * (((Z + h) / (n : ℝ) - 1 : ℝ) : ℂ) := by
      rw [Complex.ofReal_add]
      linear_combination hsub_Z
    rw [hnum]
    field_simp [hhC]
    ring

/-- Elementary Chebyshev/Mertens bound via summation by parts:
`∑_{n=1}^{⌊Z⌋₊} Λ(n) / n ≤ 7 * log Z` whenever `4 ≤ Z` and `6 ≤ log Z`. -/
private lemma sum_vonMangoldt_div_le_seven_log {Z : ℝ} (hZ4 : 4 ≤ Z) (h6 : 6 ≤ Real.log Z) :
    ∑ n ∈ Finset.Icc 1 ⌊Z⌋₊, Λ n / (n : ℝ) ≤ 7 * Real.log Z := by
  have hZ0 : 0 < Z := by linarith
  set M : ℕ := ⌊Z⌋₊
  have hM_ge4 : 4 ≤ M := Nat.le_floor hZ4
  have hM_le_Z : (M : ℝ) ≤ Z := Nat.floor_le hZ0.le
  have hparts : ∑ n ∈ Finset.Icc 1 M, Λ n / (n : ℝ) =
      RHDirect.chebyshevPsi (M : ℝ) / (M : ℝ) +
      ∑ k ∈ Finset.Icc 1 (M - 1), RHDirect.chebyshevPsi (k : ℝ) * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) := by
    have hstep : ∀ m : ℕ, 1 ≤ m →
        ∑ n ∈ Finset.Icc 1 m, Λ n / (n : ℝ) =
          RHDirect.chebyshevPsi (m : ℝ) / (m : ℝ) +
          ∑ k ∈ Finset.Icc 1 (m - 1),
            RHDirect.chebyshevPsi (k : ℝ) * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) := by
      intro m hm
      induction m with
      | zero => omega
      | succ m ih =>
        rcases Nat.eq_zero_or_pos m with rfl | hm_pos
        · simp [RHDirect.chebyshevPsi, Finset.sum_range_succ]
        · have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
            ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          have hIcc' : Finset.Icc 1 m = insert m (Finset.Icc 1 (m - 1)) := by
            ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hIcc, Finset.sum_insert (by simp), ih hm_pos]
          have hpsi_succ : RHDirect.chebyshevPsi ((m + 1 : ℕ) : ℝ) =
              RHDirect.chebyshevPsi (m : ℝ) + Λ (m + 1) := by
            unfold RHDirect.chebyshevPsi
            rw [Nat.floor_natCast, Nat.floor_natCast, Finset.sum_range_succ]
          have hsub : m + 1 - 1 = m := by omega
          rw [hsub, hIcc', Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), hpsi_succ]
          push_cast; ring
    exact hstep M (by omega)
  rw [hparts]
  have hpsi_bd : ∀ k : ℕ, 1 ≤ k → RHDirect.chebyshevPsi (k : ℝ) ≤ 6 * (k : ℝ) := fun k hk =>
    Stage4ExplicitFormula.chebyshevPsi_le_six_mul (by exact_mod_cast hk)
  have h1' : RHDirect.chebyshevPsi (M : ℝ) / (M : ℝ) ≤ 6 := by
    rw [div_le_iff₀ (by exact_mod_cast (by omega : 0 < M))]
    exact hpsi_bd M (by omega)
  have h2' : ∑ k ∈ Finset.Icc 1 (M - 1),
      RHDirect.chebyshevPsi (k : ℝ) * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) ≤
        6 * Real.log (M : ℝ) := by
    have hterm : ∀ k ∈ Finset.Icc 1 (M - 1),
        RHDirect.chebyshevPsi (k : ℝ) * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) ≤
          6 * (Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ)) := by
      intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
      have hdiff_nn : 0 ≤ 1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ) := by
        rw [sub_nonneg]
        exact one_div_le_one_div_of_le hk_pos (by exact_mod_cast Nat.le_succ k)
      have hlog_ge : 1 / ((k + 1 : ℕ) : ℝ) ≤ Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) := by
        have h1'' : Real.log ((k : ℝ) / ((k + 1 : ℕ) : ℝ)) ≤ (k : ℝ) / ((k + 1 : ℕ) : ℝ) - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
        rw [Real.log_div hk_pos.ne' (by positivity)] at h1''
        have halg : 1 - (k : ℝ) / ((k + 1 : ℕ) : ℝ) = 1 / ((k + 1 : ℕ) : ℝ) := by
          push_cast; field_simp [show (k : ℝ) + 1 ≠ 0 by positivity]; ring
        linarith
      calc RHDirect.chebyshevPsi (k : ℝ) * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))
          ≤ (6 * (k : ℝ)) * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_right (hpsi_bd k hk1) hdiff_nn
        _ = 6 * (1 / ((k + 1 : ℕ) : ℝ)) := by
            push_cast; field_simp [hk_pos.ne', show (k : ℝ) + 1 ≠ 0 by positivity]; ring
        _ ≤ 6 * (Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ)) :=
            mul_le_mul_of_nonneg_left hlog_ge (by norm_num)
    have htele : ∑ k ∈ Finset.Icc 1 (M - 1), (Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ)) =
        Real.log (M : ℝ) := by
      have hstep : ∀ n : ℕ, 1 ≤ n →
          ∑ k ∈ Finset.Icc 1 (n - 1), (Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ)) =
            Real.log (n : ℝ) := by
        intro n hn
        induction n with
        | zero => omega
        | succ n ih =>
          rcases Nat.eq_zero_or_pos n with rfl | hn_pos
          · simp
          · have hsub : n + 1 - 1 = n := by omega
            have hIcc : Finset.Icc 1 n = insert n (Finset.Icc 1 (n - 1)) := by
              ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
            rw [hsub, hIcc, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), ih hn_pos]
            ring
      exact hstep M (by omega)
    calc ∑ k ∈ Finset.Icc 1 (M - 1),
          RHDirect.chebyshevPsi (k : ℝ) * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ))
        ≤ ∑ k ∈ Finset.Icc 1 (M - 1), 6 * (Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = 6 * Real.log (M : ℝ) := by rw [← Finset.mul_sum, htele]
  have hlogM_le : Real.log (M : ℝ) ≤ Real.log Z :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < M)) hM_le_Z
  linarith

/-- Helper for `boxOfS_unconditional`: bounds the truncated Euler-product tail
`‖∑_{n ≤ Z} Λ(n) χ(n) / n + L'(χ, 1) / L(χ, 1)‖ ≤ 1 / X`. -/
private lemma boxOfS_tail_le {δ ε K Y Q : ℝ} {K_Z N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4) (_hε0 : 0 < ε) (hε4 : ε ≤ 1 / 4) (hK1 : 1 ≤ K)
    (hKZ_def : K_Z = ⌈8 / δ⌉₊ + 1) (hY16 : 16 ≤ Y) (hQ16 : 16 ≤ Q) (hNQ : (N : ℝ) ≤ Q)
    (hχ : χ ≠ 1) (hQ_lo : Y ^ (ε / 6) ≤ Real.log Q) (hQ_hi : Real.log Q ≤ Y ^ (ε / 4))
    (hbox : ZeroFreeBoxDelta δ Q χ)
    (h2 : 16 * (48 / Real.pi + (4 * max (8 / δ + 1) ((96 / δ) * (Real.log (512 / δ) + 4)) / δ) +
      4 * max (8 / δ + 1) ((96 / δ) * (Real.log (512 / δ) + 4))) ≤ Y ^ (1 / 2 : ℝ))
    (h3 : 16 * (48 / Real.pi + (4 * max (8 / δ + 1) ((96 / δ) * (Real.log (512 / δ) + 4)) / δ) +
      4 * max (8 / δ + 1) ((96 / δ) * (Real.log (512 / δ) + 4))) * (2 * (K_Z : ℝ) * K + 1) *
      (Y ^ ((K_Z + 4) * K) * Real.exp (-(Y ^ (ε / 6)))) ≤ 1 / 3)
    (h4 : 2 * (2 * (K_Z : ℝ) * K * Real.log Y + 2) ≤ Y ^ (1 / 2 : ℝ)) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊(Y ^ K) ^ K_Z⌋₊, (Λ n : ℂ) * χ (n : ZMod N) / (n : ℂ)) +
      deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1‖ ≤
      1 / (Y ^ K) := by
  set C_ld : ℝ := max (8 / δ + 1) ((96 / δ) * (Real.log (512 / δ) + 4))
  set C_per : ℝ := 48 / Real.pi + (4 * C_ld / δ) + 4 * C_ld
  have hCld_pos : 0 < C_ld := lt_of_lt_of_le (by positivity : 0 < 8 / δ + 1) (le_max_left _ _)
  have hCper_pos : 0 < C_per := by dsimp only [C_per]; positivity
  have hY0 : 0 < Y := by linarith
  have hY1' : 1 ≤ Y := by linarith
  have hQ0 : 0 < Q := by linarith
  have hLY_pos : 0 < Real.log Y := Real.log_pos (by linarith)
  have hLQ_nn : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
  have hQ_exp : Real.exp (Y ^ (ε / 6)) ≤ Q := (Real.le_log_iff_exp_le hQ0).mp hQ_lo
  have hKZ_ge8 : 8 / δ ≤ (K_Z : ℝ) := by
    rw [hKZ_def]; have := Nat.le_ceil (8 / δ); push_cast; linarith
  have hKZ_ge2 : 2 ≤ K_Z := by
    have h32 : (32 : ℝ) ≤ 8 / δ := by rw [le_div_iff₀ hδ0]; linarith
    have h2' : (2 : ℝ) ≤ (K_Z : ℝ) := by linarith
    exact_mod_cast h2'
  have hKZ_ge1 : (1 : ℝ) ≤ (K_Z : ℝ) := by rw [hKZ_def]; push_cast; linarith
  have hKZ_delta : 4 ≤ (K_Z : ℝ) * (δ / 2) := by
    have h1 := mul_le_mul_of_nonneg_right hKZ_ge8 (by positivity : 0 ≤ δ / 2)
    have h2' : 8 / δ * (δ / 2) = 4 := by field_simp [hδ0.ne']; ring
    linarith
  set X : ℝ := Y ^ K
  have hX_ge_Y : Y ≤ X := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hY1' hK1
  have hX16 : 16 ≤ X := hY16.trans hX_ge_Y
  have hX0 : 0 < X := by linarith
  have hLX_eq : Real.log X = K * Real.log Y := Real.log_rpow hY0 K
  set Z : ℝ := X ^ K_Z
  have hZ_ge_X : X ≤ Z := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ K_Z := pow_le_pow_right₀ (by linarith) (by omega)
  have hZ4 : 4 ≤ Z := by linarith
  have hZ0 : 0 < Z := by linarith
  set h : ℝ := Z / X ^ 2
  have hh_pos : 0 < h := by positivity
  have hh_le_Z : h ≤ Z := div_le_self hZ0.le (by nlinarith)
  have hZh_le_2Z : Z + h ≤ 2 * Z := by linarith
  have hLZh_nn : 0 ≤ Real.log (Z + h) := Real.log_nonneg (by linarith)
  have hLZ_eq : Real.log Z = (K_Z : ℝ) * K * Real.log Y := by
    rw [show Z = X ^ K_Z from rfl, Real.log_pow, hLX_eq]; ring
  have hLZh_le : Real.log (Z + h) ≤ 2 * (K_Z : ℝ) * K * Real.log Y := by
    have h1' : Real.log (Z + h) ≤ Real.log (2 * Z) := Real.log_le_log (by linarith) hZh_le_2Z
    rw [Real.log_mul (by norm_num) hZ0.ne', hLZ_eq] at h1'
    have hlog2_le : Real.log 2 ≤ (K_Z : ℝ) * K * Real.log Y := by
      have h2Y : Real.log 2 ≤ Real.log Y := Real.log_le_log (by norm_num) (by linarith)
      have hKK : 1 ≤ (K_Z : ℝ) * K := by nlinarith
      nlinarith
    linarith
  have hid := (Gchi_add_Sz_eq_diff hχ hX0 hZ_ge_X hh_pos).2
  have hZ_bd := norm_Gchi_perron_le_of_zeroFreeBox hδ0 hδ4 hQ16 hZ4 hNQ hχ hbox
  have hZh_bd := norm_Gchi_perron_le_of_zeroFreeBox hδ0 hδ4 hQ16 (by linarith : 4 ≤ Z + h) hNQ hχ hbox
  -- (1) Perron bound on `‖(Gchi χ (Z + h) - Gchi χ Z) / h‖`
  have hG_diff : ‖(Gchi χ (Z + h) - Gchi χ Z) / (h : ℂ)‖ ≤ 2 / (3 * X) := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hh_pos.le]
    have hsum_G : ‖Gchi χ (Z + h) - Gchi χ Z‖ ≤ ‖Gchi χ (Z + h)‖ + ‖Gchi χ Z‖ := norm_sub_le _ _
    have hZh_pow : (Z + h) ^ (1 - δ / 2) ≤ 2 * Z ^ (1 - δ / 2) := by
      calc (Z + h) ^ (1 - δ / 2) ≤ (2 * Z) ^ (1 - δ / 2) :=
            Real.rpow_le_rpow (by linarith) hZh_le_2Z (by linarith)
        _ = 2 ^ (1 - δ / 2) * Z ^ (1 - δ / 2) := Real.mul_rpow (by norm_num) hZ0.le
        _ ≤ 2 * Z ^ (1 - δ / 2) := by
            have h2p : (2 : ℝ) ^ (1 - δ / 2) ≤ 2 :=
              (Real.rpow_le_rpow_of_exponent_le (by norm_num) (show 1 - δ / 2 ≤ 1 by linarith)).trans (Real.rpow_one 2).le
            exact mul_le_mul_of_nonneg_right h2p (Real.rpow_nonneg hZ0.le _)
    have hterm1 : 3 * C_per * Real.log Q * Z ^ (1 - δ / 2) / h ≤ 1 / (3 * X) := by
      have hZ_delta : Z ^ (1 - δ / 2) / Z = Z ^ (-(δ / 2)) := by
        rw [Real.rpow_sub hZ0, Real.rpow_one, Real.rpow_neg hZ0.le]
        field_simp [hZ0.ne', (Real.rpow_pos_of_pos hZ0 _).ne']
      have hZ_neg : Z ^ (-(δ / 2)) ≤ X ^ (-4 : ℝ) := by
        rw [show Z = X ^ (K_Z : ℝ) by rw [Real.rpow_natCast], ← Real.rpow_mul hX0.le]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      have hLQ_le_Y : Real.log Q ≤ Y ^ (1 / 4 : ℝ) :=
        hQ_hi.trans (Real.rpow_le_rpow_of_exponent_le hY1' (by linarith))
      have hC_LQ : 3 * C_per * Real.log Q ≤ Y ^ (3 / 4 : ℝ) / 3 := by
        have h1' : 3 * C_per ≤ Y ^ (1 / 2 : ℝ) / 5 := by linarith
        have hmul := mul_le_mul h1' hLQ_le_Y hLQ_nn (by positivity)
        have hrp : Y ^ (1 / 2 : ℝ) * Y ^ (1 / 4 : ℝ) = Y ^ (3 / 4 : ℝ) := by
          rw [← Real.rpow_add hY0]; norm_num
        have hrew : Y ^ (1 / 2 : ℝ) / 5 * Y ^ (1 / 4 : ℝ) = Y ^ (3 / 4 : ℝ) / 5 := by
          rw [div_mul_eq_mul_div, hrp]
        have hY34_nn : 0 ≤ Y ^ (3 / 4 : ℝ) := Real.rpow_nonneg hY0.le _
        linarith
      have hX_inv : X ^ 2 * X ^ (-4 : ℝ) = X ^ (-2 : ℝ) := by
        rw [show X ^ (2 : ℕ) = X ^ (2 : ℝ) by norm_cast, ← Real.rpow_add hX0]; norm_num
      have hX_split : X ^ (-2 : ℝ) = (1 / X) * (1 / X) := by
        rw [Real.rpow_neg hX0.le, show X ^ (2 : ℝ) = X ^ (2 : ℕ) by norm_cast, sq]
        field_simp [hX0.ne']
      have hY_le_X : Y ^ (3 / 4 : ℝ) ≤ X :=
        (Real.rpow_le_rpow_of_exponent_le hY1' (by norm_num)).trans ((Real.rpow_one Y).le.trans hX_ge_Y)
      calc 3 * C_per * Real.log Q * Z ^ (1 - δ / 2) / h
          = (3 * C_per * Real.log Q) * (X ^ 2 * (Z ^ (1 - δ / 2) / Z)) := by
              dsimp only [h]; field_simp [hZ0.ne', hX0.ne']
        _ = (3 * C_per * Real.log Q) * (X ^ 2 * Z ^ (-(δ / 2))) := by rw [hZ_delta]
        _ ≤ (Y ^ (3 / 4 : ℝ) / 3) * (X ^ 2 * X ^ (-4 : ℝ)) :=
              mul_le_mul hC_LQ (mul_le_mul_of_nonneg_left hZ_neg (sq_nonneg X)) (by positivity) (by positivity)
        _ = (Y ^ (3 / 4 : ℝ) / X) * (1 / (3 * X)) := by
              rw [hX_inv, hX_split]; field_simp [hX0.ne']
        _ ≤ 1 * (1 / (3 * X)) :=
              mul_le_mul_of_nonneg_right ((div_le_one hX0).mpr hY_le_X) (by positivity)
        _ = 1 / (3 * X) := one_mul _
    have hterm2 :
        C_per * ((Z + h) * Real.log (Z + h) * Real.log Q / Q + Z * Real.log Z * Real.log Q / Q) / h ≤
          1 / (3 * X) := by
      have hLQ_le_Y : Real.log Q ≤ Y :=
        hQ_hi.trans ((Real.rpow_le_rpow_of_exponent_le hY1' (show ε / 4 ≤ 1 by linarith)).trans (Real.rpow_one Y).le)
      have hLY_le_Y : Real.log Y ≤ Y := (Real.log_le_sub_one_of_pos hY0).trans (by linarith)
      have hinvQ : 1 / Q ≤ Real.exp (-(Y ^ (ε / 6))) := by
        rw [Real.exp_neg, ← one_div]
        exact one_div_le_one_div_of_le (Real.exp_pos _) hQ_exp
      have hX3 : X ^ 3 * Y * Y ≤ Y ^ ((K_Z + 4) * K) := by
        have h1' : X ^ 3 * Y * Y ≤ X ^ 5 :=
          calc X ^ 3 * Y * Y ≤ X ^ 3 * X * X := by gcongr
            _ = X ^ 5 := by ring
        have h5 : (5 : ℝ) ≤ (K_Z + 4 : ℝ) := by linarith
        calc X ^ 3 * Y * Y ≤ X ^ 5 := h1'
          _ = X ^ (5 : ℝ) := by norm_cast
          _ ≤ X ^ ((K_Z + 4 : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by linarith) h5
          _ = Y ^ ((K_Z + 4) * K) := by
              rw [show X = Y ^ K from rfl, ← Real.rpow_mul hY0.le]; congr 1; ring
      have hnum_le :
          (Z + h) * Real.log (Z + h) * Real.log Q + Z * Real.log Z * Real.log Q ≤
            3 * Z * (2 * (K_Z : ℝ) * K * Real.log Y) * Real.log Q := by
        have hLZ_le' : Real.log Z ≤ 2 * (K_Z : ℝ) * K * Real.log Y := by
          rw [hLZ_eq]
          have hnn : 0 ≤ (K_Z : ℝ) * K * Real.log Y := by positivity
          linarith
        have h1' : (Z + h) * Real.log (Z + h) ≤ 2 * Z * (2 * (K_Z : ℝ) * K * Real.log Y) :=
          mul_le_mul hZh_le_2Z hLZh_le hLZh_nn (by positivity)
        have h2' : Z * Real.log Z ≤ Z * (2 * (K_Z : ℝ) * K * Real.log Y) :=
          mul_le_mul_of_nonneg_left hLZ_le' hZ0.le
        have h3' := mul_le_mul_of_nonneg_right (add_le_add h1' h2') hLQ_nn
        linarith
      have hmain_mul :
          X * (C_per * ((Z + h) * Real.log (Z + h) * Real.log Q / Q + Z * Real.log Z * Real.log Q / Q) / h) ≤
            1 / 3 := by
        have hEq : X * (C_per * ((Z + h) * Real.log (Z + h) * Real.log Q / Q + Z * Real.log Z * Real.log Q / Q) / h) =
            C_per * (((Z + h) * Real.log (Z + h) * Real.log Q + Z * Real.log Z * Real.log Q) / Z) * (X ^ 3 * (1 / Q)) := by
          dsimp only [h]; field_simp [hZ0.ne', hX0.ne', hQ0.ne']
        rw [hEq]
        have hdivZ : ((Z + h) * Real.log (Z + h) * Real.log Q + Z * Real.log Z * Real.log Q) / Z ≤
            3 * (2 * (K_Z : ℝ) * K * Real.log Y) * Real.log Q := by
          rw [div_le_iff₀ hZ0]; linarith
        have hnn_mid : 0 ≤ C_per * (3 * (2 * (K_Z : ℝ) * K * Real.log Y) * Real.log Q) := by positivity
        calc C_per * (((Z + h) * Real.log (Z + h) * Real.log Q + Z * Real.log Z * Real.log Q) / Z) * (X ^ 3 * (1 / Q))
            ≤ C_per * (3 * (2 * (K_Z : ℝ) * K * Real.log Y) * Real.log Q) * (X ^ 3 * Real.exp (-(Y ^ (ε / 6)))) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hdivZ hCper_pos.le)
                (mul_le_mul_of_nonneg_left hinvQ (by positivity)) (by positivity) hnn_mid
          _ = 3 * C_per * (2 * (K_Z : ℝ) * K) * ((X ^ 3 * Real.log Y * Real.log Q) * Real.exp (-(Y ^ (ε / 6)))) := by ring
          _ ≤ 16 * C_per * (2 * (K_Z : ℝ) * K + 1) * (Y ^ ((K_Z + 4) * K) * Real.exp (-(Y ^ (ε / 6)))) := by
              have hXY : X ^ 3 * Real.log Y * Real.log Q ≤ Y ^ ((K_Z + 4) * K) := by
                have h1' : X ^ 3 * Real.log Y * Real.log Q ≤ X ^ 3 * Y * Y := by gcongr
                exact h1'.trans hX3
              have hC16 : 3 * C_per * (2 * (K_Z : ℝ) * K) ≤ 16 * C_per * (2 * (K_Z : ℝ) * K + 1) := by
                have hKK : 0 ≤ (K_Z : ℝ) * K := by positivity
                nlinarith
              have hnn1 : 0 ≤ (X ^ 3 * Real.log Y * Real.log Q) * Real.exp (-(Y ^ (ε / 6))) := by positivity
              have hnn2 : 0 ≤ 16 * C_per * (2 * (K_Z : ℝ) * K + 1) := by positivity
              exact mul_le_mul hC16 (mul_le_mul_of_nonneg_right hXY (Real.exp_pos _).le) hnn1 hnn2
          _ ≤ 1 / 3 := h3
      rw [le_div_iff₀ (by positivity : 0 < 3 * X)]
      linarith [show 3 * X * (C_per * ((Z + h) * Real.log (Z + h) * Real.log Q / Q + Z * Real.log Z * Real.log Q / Q) / h) =
        3 * (X * (C_per * ((Z + h) * Real.log (Z + h) * Real.log Q / Q + Z * Real.log Z * Real.log Q / Q) / h)) by ring]
    have hcomb : (‖Gchi χ (Z + h)‖ + ‖Gchi χ Z‖) / h ≤
        3 * C_per * Real.log Q * Z ^ (1 - δ / 2) / h +
        C_per * ((Z + h) * Real.log (Z + h) * Real.log Q / Q + Z * Real.log Z * Real.log Q / Q) / h := by
      rw [← add_div]
      refine div_le_div_of_nonneg_right ?_ hh_pos.le
      have h1' : C_per * (Real.log Q * (Z + h) ^ (1 - δ / 2)) ≤ 2 * C_per * Real.log Q * Z ^ (1 - δ / 2) := by
        have := mul_le_mul_of_nonneg_left hZh_pow (mul_nonneg hCper_pos.le hLQ_nn)
        linarith
      linarith [hZ_bd, hZh_bd]
    calc ‖Gchi χ (Z + h) - Gchi χ Z‖ / h
        ≤ (‖Gchi χ (Z + h)‖ + ‖Gchi χ Z‖) / h := div_le_div_of_nonneg_right hsum_G hh_pos.le
      _ ≤ 3 * C_per * Real.log Q * Z ^ (1 - δ / 2) / h +
          C_per * ((Z + h) * Real.log (Z + h) * Real.log Q / Q + Z * Real.log Z * Real.log Q / Q) / h := hcomb
      _ ≤ 1 / (3 * X) + 1 / (3 * X) := add_le_add hterm1 hterm2
      _ = 2 / (3 * X) := by ring
  -- (2) Trivial bound on `(1 / h) * ∑_{Z < n ≤ Z + h} Λ(n) χ(n) ((Z + h) / n - 1)`
  have htriv :
      ‖((h : ℂ))⁻¹ * ∑ n ∈ Finset.Ioc ⌊Z⌋₊ ⌊Z + h⌋₊,
          (Λ n : ℂ) * χ (n : ZMod N) * (((Z + h) / (n : ℝ) - 1 : ℝ) : ℂ)‖ ≤ 1 / (3 * X) := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hh_pos.le]
    have hterm : ∀ n ∈ Finset.Ioc ⌊Z⌋₊ ⌊Z + h⌋₊,
        ‖(Λ n : ℂ) * χ (n : ZMod N) * (((Z + h) / (n : ℝ) - 1 : ℝ) : ℂ)‖ ≤
          Real.log (Z + h) * (h / Z) := by
      intro n hn
      obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hn
      have hn_gt_Z : Z < (n : ℝ) := lt_of_lt_of_le (Nat.lt_floor_add_one Z) (by exact_mod_cast hlo)
      have hn_le_Zh : (n : ℝ) ≤ Z + h := (by exact_mod_cast hhi : (n : ℝ) ≤ (⌊Z + h⌋₊ : ℝ)).trans
        (Nat.floor_le (by linarith))
      have hn_pos : (0 : ℝ) < (n : ℝ) := lt_trans hZ0 hn_gt_Z
      have hΛ_le : Λ n ≤ Real.log (Z + h) :=
        (ArithmeticFunction.vonMangoldt_le_log).trans (Real.log_le_log hn_pos hn_le_Zh)
      have hratio_nn : 0 ≤ (Z + h) / (n : ℝ) - 1 := by
        rw [sub_nonneg, one_le_div hn_pos]; exact hn_le_Zh
      have hratio_le : (Z + h) / (n : ℝ) - 1 ≤ h / Z := by
        have h1' : (Z + h) / (n : ℝ) ≤ (Z + h) / Z :=
          div_le_div_of_nonneg_left (by linarith) hZ0 hn_gt_Z.le
        have h2' : (Z + h) / Z - 1 = h / Z := by field_simp [hZ0.ne']; ring
        linarith
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        Complex.norm_real, Real.norm_of_nonneg hratio_nn]
      calc Λ n * ‖χ (n : ZMod N)‖ * ((Z + h) / (n : ℝ) - 1)
          ≤ Real.log (Z + h) * 1 * (h / Z) :=
            mul_le_mul (mul_le_mul hΛ_le (χ.norm_le_one _) (norm_nonneg _) hLZh_nn)
              hratio_le hratio_nn (mul_nonneg hLZh_nn zero_le_one)
        _ = Real.log (Z + h) * (h / Z) := by ring
    have hcard_le : ((Finset.Ioc ⌊Z⌋₊ ⌊Z + h⌋₊).card : ℝ) ≤ h + 1 := by
      rw [Nat.card_Ioc]
      have h1' : (⌊Z + h⌋₊ : ℝ) ≤ Z + h := Nat.floor_le (by linarith)
      have h2' : Z - 1 < (⌊Z⌋₊ : ℝ) := by linarith [Nat.lt_floor_add_one Z]
      have hcast : ((⌊Z + h⌋₊ - ⌊Z⌋₊ : ℕ) : ℝ) = (⌊Z + h⌋₊ : ℝ) - (⌊Z⌋₊ : ℝ) :=
        Nat.cast_sub (Nat.floor_mono (by linarith))
      linarith
    have hsum_le :
        ‖∑ n ∈ Finset.Ioc ⌊Z⌋₊ ⌊Z + h⌋₊,
            (Λ n : ℂ) * χ (n : ZMod N) * (((Z + h) / (n : ℝ) - 1 : ℝ) : ℂ)‖ ≤
          (h + 1) * (Real.log (Z + h) * (h / Z)) := by
      calc ‖∑ n ∈ Finset.Ioc ⌊Z⌋₊ ⌊Z + h⌋₊, _‖
          ≤ ∑ n ∈ Finset.Ioc ⌊Z⌋₊ ⌊Z + h⌋₊, ‖_‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.Ioc ⌊Z⌋₊ ⌊Z + h⌋₊, (Real.log (Z + h) * (h / Z)) := Finset.sum_le_sum hterm
        _ = ((Finset.Ioc ⌊Z⌋₊ ⌊Z + h⌋₊).card : ℝ) * (Real.log (Z + h) * (h / Z)) := by simp
        _ ≤ (h + 1) * (Real.log (Z + h) * (h / Z)) :=
            mul_le_mul_of_nonneg_right hcard_le (by positivity)
    have hh1_le : h + 1 ≤ 2 * h := by
      have h1_le_h : 1 ≤ h := by
        dsimp only [h]
        rw [one_le_div (sq_pos_of_pos hX0)]
        exact pow_le_pow_right₀ (by linarith) hKZ_ge2
      linarith
    have hlog_le_X : 6 * Real.log (Z + h) ≤ X := by
      have h3' : 6 * Real.log (Z + h) ≤ 3 * Y ^ (1 / 2 : ℝ) := by linarith
      have h4' : 3 * Y ^ (1 / 2 : ℝ) ≤ Y := by
        have hYsq : Y = Y ^ (1 / 2 : ℝ) * Y ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_add hY0]; norm_num
        have h4le : (4 : ℝ) ≤ Y ^ (1 / 2 : ℝ) := by
          have h16 : (16 : ℝ) ^ (1 / 2 : ℝ) = 4 := by
            rw [show (16 : ℝ) = 4 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
          rw [← h16]; exact Real.rpow_le_rpow (by norm_num) hY16 (by norm_num)
        nlinarith
      linarith
    calc h⁻¹ * ‖∑ n ∈ Finset.Ioc ⌊Z⌋₊ ⌊Z + h⌋₊, _‖
        ≤ h⁻¹ * ((h + 1) * (Real.log (Z + h) * (h / Z))) :=
          mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr hh_pos.le)
      _ ≤ h⁻¹ * ((2 * h) * (Real.log (Z + h) * (h / Z))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hh1_le (by positivity)) (inv_nonneg.mpr hh_pos.le)
      _ = 2 * Real.log (Z + h) / X ^ 2 := by
          dsimp only [h]; field_simp [hZ0.ne', hX0.ne']
      _ ≤ (X / 3) / X ^ 2 := div_le_div_of_nonneg_right (by linarith) (sq_nonneg X)
      _ = 1 / (3 * X) := by field_simp [hX0.ne']
  rw [hid]
  calc ‖(Gchi χ (Z + h) - Gchi χ Z) / (h : ℂ) -
        ((h : ℂ))⁻¹ * ∑ n ∈ Finset.Ioc ⌊Z⌋₊ ⌊Z + h⌋₊,
          (Λ n : ℂ) * χ (n : ZMod N) * (((Z + h) / (n : ℝ) - 1 : ℝ) : ℂ)‖
      ≤ ‖(Gchi χ (Z + h) - Gchi χ Z) / (h : ℂ)‖ +
        ‖((h : ℂ))⁻¹ * ∑ n ∈ Finset.Ioc ⌊Z⌋₊ ⌊Z + h⌋₊,
          (Λ n : ℂ) * χ (n : ZMod N) * (((Z + h) / (n : ℝ) - 1 : ℝ) : ℂ)‖ := norm_sub_le _ _
    _ ≤ 2 / (3 * X) + 1 / (3 * X) := add_le_add hG_diff htriv
    _ = 1 / X := by ring

/-- **UNCONDITIONAL `BoxOfS` (`boxOfS_unconditional`, `0` ASSUMPTIONS!)**:
for EVERY `0 < δ ≤ 1/4`, let `K_Z := ⌈8 / δ⌉₊ + 1`. Then for EVERY `ε ∈ (0, 1/4]`, `τ > 0`, `K ≥ 1`,
for all sufficiently large `Y`, ANY non-principal character `χ mod N` (`N ≤ Q`) satisfying:
1. `Y ^ (ε / 6) ≤ Real.log Q` and `Real.log Q ≤ Y ^ (ε / 4)`,
2. `ZeroFreeBoxDelta δ Q χ`, and
3. `∀ y ∈ Set.Icc Y (Y ^ K), ‖Sz χ y ((Y ^ K) ^ K_Z)‖ ≤ y ^ (1 / 2 + τ) / 2`
automatically satisfies BOTH:
- **Pointwise Cesàro bound**: `∀ y ∈ Set.Icc Y (Y ^ K), ‖Gchi χ y‖ ≤ y ^ (1 / 2 + τ)`, AND
- **Log-derivative bound at `s = 1`**: `‖deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1‖ ≤ 8 * (K_Z : ℝ) * K * Real.log Y`! -/
theorem boxOfS_unconditional {δ : ℝ} (hδ0 : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    let K_Z : ℕ := ⌈8 / δ⌉₊ + 1
    ∀ (ε τ K : ℝ), 0 < ε → ε ≤ 1 / 4 → 0 < τ → 1 ≤ K →
      ∃ Y₀ : ℝ, 16 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
        ∀ (Q : ℝ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
          (N : ℝ) ≤ Q → χ ≠ 1 →
          Y ^ (ε / 6) ≤ Real.log Q → Real.log Q ≤ Y ^ (ε / 4) →
          ZeroFreeBoxDelta δ Q χ →
          (∀ y ∈ Set.Icc Y (Y ^ K), ‖Sz χ y ((Y ^ K) ^ K_Z)‖ ≤ y ^ ((1 : ℝ) / 2 + τ) / 2) →
          (∀ y ∈ Set.Icc Y (Y ^ K), ‖Gchi χ y‖ ≤ y ^ ((1 : ℝ) / 2 + τ)) ∧
          ‖deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1‖ ≤
            8 * (K_Z : ℝ) * K * Real.log Y := by
  intro K_Z ε τ K hε0 hε4 hτ0 hK1
  have hKZ_ge8 : 8 / δ ≤ (K_Z : ℝ) := by
    dsimp only [K_Z]; have := Nat.le_ceil (8 / δ); push_cast; linarith
  set C_ld : ℝ := max (8 / δ + 1) ((96 / δ) * (Real.log (512 / δ) + 4))
  set C_per : ℝ := 48 / Real.pi + (4 * C_ld / δ) + 4 * C_ld
  have hCld_pos : 0 < C_ld := lt_of_lt_of_le (by positivity : 0 < 8 / δ + 1) (le_max_left _ _)
  have hCper_pos : 0 < C_per := by dsimp only [C_per]; positivity
  have hev1 : ∀ᶠ Y : ℝ in Filter.atTop, Real.log 16 ≤ Y ^ (ε / 6) :=
    (tendsto_rpow_atTop (by positivity : 0 < ε / 6)).eventually_ge_atTop _
  have hev2 : ∀ᶠ Y : ℝ in Filter.atTop, 16 * C_per ≤ Y ^ (1 / 2 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually_ge_atTop _
  have hev3 : ∀ᶠ Y : ℝ in Filter.atTop,
      16 * C_per * (2 * (K_Z : ℝ) * K + 1) * (Y ^ ((K_Z + 4) * K) * Real.exp (-(Y ^ (ε / 6)))) ≤ 1 / 3 := by
    have hc : 0 < ε / 6 := by positivity
    have hlim0 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (((K_Z + 4) * K) / (ε / 6)) 1 one_pos).comp
      (tendsto_rpow_atTop hc)
    have hlim : Tendsto (fun Y : ℝ =>
        16 * C_per * (2 * (K_Z : ℝ) * K + 1) * (Y ^ ((K_Z + 4) * K) * Real.exp (-(Y ^ (ε / 6)))))
        atTop (𝓝 0) := by
      have hm := hlim0.const_mul (16 * C_per * (2 * (K_Z : ℝ) * K + 1))
      rw [mul_zero] at hm
      refine hm.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with Y hY
      simp only [Function.comp_apply, neg_mul, one_mul]
      rw [← Real.rpow_mul hY.le, mul_div_cancel₀ _ hc.ne']
    exact hlim.eventually (ge_mem_nhds (by norm_num))
  have hev4 : ∀ᶠ Y : ℝ in Filter.atTop, 2 * (2 * (K_Z : ℝ) * K * Real.log Y + 2) ≤ Y ^ (1 / 2 : ℝ) := by
    have h1 := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).bound
      (show (0 : ℝ) < 1 / (8 * (K_Z : ℝ) * K) by positivity)
    have h2 : ∀ᶠ Y : ℝ in Filter.atTop, 8 ≤ Y ^ (1 / 2 : ℝ) :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually_ge_atTop 8
    filter_upwards [h1, h2, Filter.eventually_gt_atTop (1 : ℝ)] with Y hY1 hY2 hYgt
    rw [Real.norm_of_nonneg (Real.log_nonneg hYgt.le),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hY1
    have hmul := mul_le_mul_of_nonneg_left hY1 (show 0 ≤ 4 * (K_Z : ℝ) * K by positivity)
    have hsimp : 4 * (K_Z : ℝ) * K * (1 / (8 * (K_Z : ℝ) * K) * Y ^ (1 / 2 : ℝ)) = Y ^ (1 / 2 : ℝ) / 2 := by
      field_simp [show (K_Z : ℝ) ≠ 0 by positivity, show K ≠ 0 by positivity]; ring
    linarith
  obtain ⟨Y₁, hY₁⟩ := Filter.eventually_atTop.mp (hev1.and (hev2.and (hev3.and hev4)))
  refine ⟨max Y₁ 16, le_max_right _ _, fun Y hY Q N _ χ hNQ hχ hQ_lo hQ_hi hbox hSz => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hY₁ Y ((le_max_left _ _).trans hY)
  have hY16 : 16 ≤ Y := (le_max_right _ _).trans hY
  have hY0 : 0 < Y := by linarith
  have hQpos : 0 < Q := lt_of_lt_of_le (Nat.cast_pos.mpr (NeZero.pos N)) hNQ
  have hQ16 : 16 ≤ Q := (Real.log_le_log_iff (by norm_num) hQpos).mp (h1.trans hQ_lo)
  set X : ℝ := Y ^ K
  have hX_ge_Y : Y ≤ X := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by linarith) hK1
  have hX0 : 0 < X := by linarith
  set Z : ℝ := X ^ K_Z
  have hZ_ge_X : X ≤ Z :=
    (pow_one X).symm.le.trans (pow_le_pow_right₀ (by linarith) (by dsimp only [K_Z]; omega))
  have hZ4 : 4 ≤ Z := by linarith
  have hZ0 : 0 < Z := by linarith
  have hLZ_eq : Real.log Z = (K_Z : ℝ) * K * Real.log Y := by
    rw [show Z = X ^ K_Z from rfl, Real.log_pow, Real.log_rpow hY0 K]; ring
  set T_tail : ℂ :=
    (∑ n ∈ Finset.Icc 1 ⌊Z⌋₊, (Λ n : ℂ) * χ (n : ZMod N) / (n : ℂ)) +
      deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1
  have hTail_le : ‖T_tail‖ ≤ 1 / X :=
    boxOfS_tail_le hδ0 hδ4 hε0 hε4 hK1 rfl hY16 hQ16 hNQ hχ hQ_lo hQ_hi hbox h2 h3 h4
  refine ⟨fun y hy => ?_, ?_⟩
  · have hy0 : 0 < y := lt_of_lt_of_le hY0 hy.1
    have hyZ : y ≤ Z := hy.2.trans hZ_ge_X
    have hid1 := (Gchi_add_Sz_eq_diff hχ hy0 hyZ one_pos).1
    have hG_eq : Gchi χ y = -Sz χ y Z + (y : ℂ) * T_tail := by linear_combination hid1
    have hy_tail : ‖(y : ℂ) * T_tail‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hy0.le]
      calc y * ‖T_tail‖ ≤ X * (1 / X) := mul_le_mul hy.2 hTail_le (norm_nonneg _) hX0.le
        _ = 1 := mul_one_div_cancel hX0.ne'
    have hone_le : (1 : ℝ) ≤ y ^ ((1 : ℝ) / 2 + τ) / 2 := by
      have h16y : 16 ≤ y := hY16.trans hy.1
      have h4' : (4 : ℝ) ≤ y ^ ((1 : ℝ) / 2) := by
        have h16 : (16 : ℝ) ^ ((1 : ℝ) / 2) = 4 := by
          rw [show (16 : ℝ) = 4 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
        rw [← h16]; exact Real.rpow_le_rpow (by norm_num) h16y (by norm_num)
      have hmono : y ^ ((1 : ℝ) / 2) ≤ y ^ ((1 : ℝ) / 2 + τ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      linarith
    rw [hG_eq]
    calc ‖-Sz χ y Z + (y : ℂ) * T_tail‖
        ≤ ‖-Sz χ y Z‖ + ‖(y : ℂ) * T_tail‖ := norm_add_le _ _
      _ = ‖Sz χ y Z‖ + ‖(y : ℂ) * T_tail‖ := by rw [norm_neg]
      _ ≤ y ^ ((1 : ℝ) / 2 + τ) / 2 + 1 := add_le_add (hSz y hy) hy_tail
      _ ≤ y ^ ((1 : ℝ) / 2 + τ) := by linarith
  · have hld_eq : deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1 =
        T_tail - ∑ n ∈ Finset.Icc 1 ⌊Z⌋₊, (Λ n : ℂ) * χ (n : ZMod N) / (n : ℂ) := by
      dsimp only [T_tail]; ring
    have hsum_le :
        ‖∑ n ∈ Finset.Icc 1 ⌊Z⌋₊, (Λ n : ℂ) * χ (n : ZMod N) / (n : ℂ)‖ ≤
          ∑ n ∈ Finset.Icc 1 ⌊Z⌋₊, Λ n / (n : ℝ) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        Complex.norm_natCast]
      exact div_le_div_of_nonneg_right
        (mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _))
        (Nat.cast_nonneg n)
    have h6_le_logZ : 6 ≤ Real.log Z := by
      rw [hLZ_eq]
      have hlog16 : (2 : ℝ) ≤ Real.log Y := by
        have he2 : Real.exp 2 ≤ 16 := by
          have hsq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
          rw [hsq]; nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]
        exact (Real.log_exp 2).symm.trans_le (Real.log_le_log (Real.exp_pos 2) (he2.trans hY16))
      have hKZ_ge32 : (32 : ℝ) ≤ (K_Z : ℝ) := by
        have : (32 : ℝ) ≤ 8 / δ := by rw [le_div_iff₀ hδ0]; linarith
        linarith
      calc (6 : ℝ) ≤ 32 * 1 * 2 := by norm_num
        _ ≤ (K_Z : ℝ) * K * Real.log Y := by gcongr
    have hmertens : ∑ n ∈ Finset.Icc 1 ⌊Z⌋₊, Λ n / (n : ℝ) ≤ 7 * Real.log Z :=
      sum_vonMangoldt_div_le_seven_log hZ4 h6_le_logZ
    have htail1 : ‖T_tail‖ ≤ Real.log Z :=
      hTail_le.trans (((div_le_one hX0).mpr (by linarith)).trans (by linarith))
    rw [hld_eq]
    calc ‖T_tail - ∑ n ∈ Finset.Icc 1 ⌊Z⌋₊, (Λ n : ℂ) * χ (n : ZMod N) / (n : ℂ)‖
        ≤ ‖T_tail‖ + ‖∑ n ∈ Finset.Icc 1 ⌊Z⌋₊, (Λ n : ℂ) * χ (n : ZMod N) / (n : ℂ)‖ := norm_sub_le _ _
      _ ≤ Real.log Z + 7 * Real.log Z := add_le_add htail1 (hsum_le.trans hmertens)
      _ = 8 * (K_Z : ℝ) * K * Real.log Y := by rw [hLZ_eq]; ring

/-! ## Section 4: Unconditional Quadratic-Twist Mean-Square Bounds (`MSqMain`, Large Sieve + Reciprocity) -/

/-! ### Section 4a: Unconditional Multiplicative Large Sieve Over Quadratic Twists & L² Norm of `cN` -/

open Classical in
private lemma norm_sum_twisted_sq_le_lsTerm {M q M₁ M₂ : ℕ} [NeZero M] [NeZero q]
    (ψ : DirichletCharacter ℂ M) (χ : DirichletCharacter ℂ q) (a : ℕ → ℂ)
    (hprim : (Stage11SecondMomentFrame.twistedChar ψ χ).IsPrimitive) :
    ‖∑ n ∈ Finset.Ioc M₁ M₂,
        a n * Stage11SecondMomentFrame.twistedChar ψ χ (n : ZMod (M * q))‖ ^ 2 ≤
      ((((M * q - 1) + 1 : ℕ) : ℝ) / (((M * q - 1) + 1).totient : ℝ)) *
        ∑ η ∈ Finset.univ.filter (fun η : DirichletCharacter ℂ ((M * q - 1) + 1) => η.IsPrimitive),
          ‖∑ n ∈ Finset.Ioc M₁ M₂, a n * η (n : ZMod ((M * q - 1) + 1))‖ ^ 2 := by
  classical
  have hpos : 1 ≤ M * q := Nat.mul_pos (NeZero.pos M) (NeZero.pos q)
  set k : ℕ := M * q - 1
  have hk : k + 1 = M * q := Nat.sub_add_cancel hpos
  have hmain : ∀ (N : ℕ) (η0 : DirichletCharacter ℂ N), N = k + 1 → η0.IsPrimitive →
      ‖∑ n ∈ Finset.Ioc M₁ M₂, a n * η0 (n : ZMod N)‖ ^ 2 ≤
        (((k + 1 : ℕ) : ℝ) / ((k + 1).totient : ℝ)) *
          ∑ η ∈ Finset.univ.filter (fun η : DirichletCharacter ℂ (k + 1) => η.IsPrimitive),
            ‖∑ n ∈ Finset.Ioc M₁ M₂, a n * η (n : ZMod (k + 1))‖ ^ 2 := by
    rintro _ η0 rfl hprim
    have hmem : η0 ∈ Finset.univ.filter (fun η : DirichletCharacter ℂ (k + 1) => η.IsPrimitive) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hprim⟩
    have hsingle : ‖∑ n ∈ Finset.Ioc M₁ M₂, a n * η0 (n : ZMod (k + 1))‖ ^ 2 ≤
        ∑ η ∈ Finset.univ.filter (fun η : DirichletCharacter ℂ (k + 1) => η.IsPrimitive),
          ‖∑ n ∈ Finset.Ioc M₁ M₂, a n * η (n : ZMod (k + 1))‖ ^ 2 :=
      Finset.single_le_sum
        (f := fun η : DirichletCharacter ℂ (k + 1) => ‖∑ n ∈ Finset.Ioc M₁ M₂, a n * η (n : ZMod (k + 1))‖ ^ 2)
        (fun _ _ => sq_nonneg _) hmem
    have htot_pos : (0 : ℝ) < ((k + 1).totient : ℝ) :=
      Nat.cast_pos.mpr (Nat.totient_pos.mpr (Nat.succ_pos k))
    have htot_le : ((k + 1).totient : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.totient_le (k + 1)
    have hge1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) / ((k + 1).totient : ℝ) :=
      (one_le_div htot_pos).mpr htot_le
    exact hsingle.trans (le_mul_of_one_le_left (Finset.sum_nonneg fun _ _ => sq_nonneg _) hge1)
  exact hmain (M * q) (Stage11SecondMomentFrame.twistedChar ψ χ) hk.symm hprim

/-- **UNCONDITIONAL MULTIPLICATIVE LARGE SIEVE OVER QUADRATIC TWISTS (`quadTwist_largeSieve_meanSquare`)**:
for any primitive character `ψ : DirichletCharacter ℂ M`, any `Q, M₁, M₂ : ℕ`, any complex weights
`a : ℕ → ℂ`, and any finite set `S` of primes `q ≤ Q` with `q % 4 = 3` and `Coprime M q`:
`∑_{q ∈ S} ‖∑_{n ∈ Ioc M₁ M₂} a n * (ψ · χ_q)(n)‖² ≤ ((M₂ - M₁) + 3 (M Q)²) * ∑_{n ∈ Ioc M₁ M₂} ‖a n‖²`. -/
theorem quadTwist_largeSieve_meanSquare {M : ℕ} [NeZero M] {ψ : DirichletCharacter ℂ M}
    (hψ : ψ.IsPrimitive) (Q M₁ M₂ : ℕ) (a : ℕ → ℂ)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime ∧ q ≤ Q ∧ q % 4 = 3 ∧ Nat.Coprime M q) :
    ∑ q ∈ S.attach,
        ‖∑ n ∈ Finset.Ioc M₁ M₂,
          a n * Stage11SecondMomentFrame.twistedChar ψ
            (@quadCharOfPrime q.1 ⟨(hS q.1 q.2).1.ne_zero⟩ (hS q.1 q.2).1)
            (n : ZMod (M * q.1))‖ ^ 2 ≤
      (((M₂ - M₁ : ℕ) : ℝ) + 3 * ((M * Q : ℕ) : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M₁ M₂, ‖a n‖ ^ 2 := by
  classical
  let lsTerm : ℕ → ℝ := fun k =>
    (((k + 1 : ℕ) : ℝ) / ((k + 1).totient : ℝ)) *
      ∑ η ∈ Finset.univ.filter (fun η : DirichletCharacter ℂ (k + 1) => η.IsPrimitive),
        ‖∑ n ∈ Finset.Ioc M₁ M₂, a n * η (n : ZMod (k + 1))‖ ^ 2
  have hterm_le : ∀ q ∈ S.attach,
      ‖∑ n ∈ Finset.Ioc M₁ M₂,
          a n * Stage11SecondMomentFrame.twistedChar ψ
            (@quadCharOfPrime q.1 ⟨(hS q.1 q.2).1.ne_zero⟩ (hS q.1 q.2).1)
            (n : ZMod (M * q.1))‖ ^ 2 ≤ lsTerm (M * q.1 - 1) := by
    intro q _
    obtain ⟨hq_pr, _, hq4, hcop⟩ := hS q.1 q.2
    have : NeZero q.1 := ⟨hq_pr.ne_zero⟩
    have hχ_prim := quadCharOfPrime_isPrimitive_of_mod_four hq_pr hq4
    have htw_prim := twistedChar_isPrimitive hcop hψ hχ_prim
    exact norm_sum_twisted_sq_le_lsTerm ψ (quadCharOfPrime q.1 hq_pr) a htw_prim
  have hinj : Set.InjOn (fun q : {x // x ∈ S} => M * q.1 - 1) (S.attach : Set {x // x ∈ S}) := by
    intro q₁ _ q₂ _ heq
    dsimp only at heq
    have hMpos : 0 < M := NeZero.pos M
    have h1 : 1 ≤ M * q₁.1 := Nat.mul_pos hMpos (hS q₁.1 q₁.2).1.pos
    have h2 : 1 ≤ M * q₂.1 := Nat.mul_pos hMpos (hS q₂.1 q₂.2).1.pos
    have hmul : M * q₁.1 = M * q₂.1 := by omega
    exact Subtype.ext (Nat.eq_of_mul_eq_mul_left hMpos hmul)
  have hsub : S.attach.image (fun q => M * q.1 - 1) ⊆ Finset.range (M * Q) := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨q, _, rfl⟩
    have hMpos : 0 < M := NeZero.pos M
    have hq_le : q.1 ≤ Q := (hS q.1 q.2).2.1
    have hq_pos : 0 < q.1 := (hS q.1 q.2).1.pos
    have hmul_le : M * q.1 ≤ M * Q := Nat.mul_le_mul_left M hq_le
    have hmul_pos : 1 ≤ M * q.1 := Nat.mul_pos hMpos hq_pos
    exact Finset.mem_range.mpr (by omega)
  calc ∑ q ∈ S.attach, _
      ≤ ∑ q ∈ S.attach, lsTerm (M * q.1 - 1) := Finset.sum_le_sum hterm_le
    _ = ∑ k ∈ S.attach.image (fun q => M * q.1 - 1), lsTerm k :=
        (Finset.sum_image (fun x hx y hy h => hinj hx hy h)).symm
    _ ≤ ∑ k ∈ Finset.range (M * Q), lsTerm k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => by
          dsimp only [lsTerm]
          exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ ≤ (((M₂ - M₁ : ℕ) : ℝ) + 3 * ((M * Q : ℕ) : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M₁ M₂, ‖a n‖ ^ 2 :=
        Stage11BombieriVinogradov.multiplicative_large_sieve_Ioc_interval (M * Q) M₁ M₂ a

/-- Elementary telescoping bound `∑_{n ∈ Ioc a b} (1 / n^2) ≤ 1 / a` for `1 ≤ a`. -/
private lemma sum_inv_sq_Ioc_le {a b : ℕ} (ha : 1 ≤ a) :
    ∑ n ∈ Finset.Ioc a b, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / (a : ℝ) := by
  have hle_diff : ∀ n ∈ Finset.Ioc a b,
      (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / ((n - 1 : ℕ) : ℝ) - 1 / (n : ℝ) := by
    intro n hn
    have hgt : a < n := (Finset.mem_Ioc.mp hn).1
    have hn2 : 2 ≤ n := by omega
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hnm1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - 1)
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by exact_mod_cast Nat.cast_sub (by omega : 1 ≤ n)
    have hdiff : 1 / ((n - 1 : ℕ) : ℝ) - 1 / (n : ℝ) = 1 / (((n - 1 : ℕ) : ℝ) * (n : ℝ)) := by
      field_simp [hnm1_pos.ne', hn_pos.ne']; rw [hcast]; ring
    rw [hdiff]
    refine one_div_le_one_div_of_le (mul_pos hnm1_pos hn_pos) ?_
    rw [sq, hcast]; nlinarith
  have htele : ∀ m : ℕ, a ≤ m →
      ∑ n ∈ Finset.Ioc a m, (1 / ((n - 1 : ℕ) : ℝ) - 1 / (n : ℝ)) = 1 / (a : ℝ) - 1 / (m : ℝ) := by
    intro m hm
    induction m with
    | zero => omega
    | succ m ih =>
      rcases eq_or_lt_of_le hm with rfl | hlt
      · simp
      · have hIoc : Finset.Ioc a (m + 1) = insert (m + 1) (Finset.Ioc a m) := by
          ext x; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
        rw [hIoc, Finset.sum_insert (by simp), ih (by omega)]
        simp only [Nat.add_sub_cancel]; ring
  by_cases hab : a ≤ b
  · calc ∑ n ∈ Finset.Ioc a b, (1 : ℝ) / (n : ℝ) ^ 2
        ≤ ∑ n ∈ Finset.Ioc a b, (1 / ((n - 1 : ℕ) : ℝ) - 1 / (n : ℝ)) := Finset.sum_le_sum hle_diff
      _ = 1 / (a : ℝ) - 1 / (b : ℝ) := htele b hab
      _ ≤ 1 / (a : ℝ) := by linarith [show (0 : ℝ) ≤ 1 / (b : ℝ) by positivity]
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]; positivity

/-- Elementary L² norm bound on the `ZeroDensityWindow.cN` kernel:
`∑_{n=1}^{⌊Z⌋₊} (cN y n)^2 ≤ 8 * y * (Real.log Z + 2)^2` for all `1 ≤ y ≤ Z`. -/
theorem sum_cN_sq_le {y Z : ℝ} (hy : 1 ≤ y) (hyZ : y ≤ Z) :
    ∑ n ∈ Finset.Icc 1 ⌊Z⌋₊, (ZeroDensityWindow.cN y n) ^ 2 ≤ 8 * y * (Real.log Z + 2) ^ 2 := by
  have hy0 : 0 < y := by linarith
  have hZ0 : 0 < Z := by linarith
  have hLZ_nn : 0 ≤ Real.log Z := Real.log_nonneg (by linarith)
  have hfl : ⌊y⌋₊ ≤ ⌊Z⌋₊ := Nat.floor_mono hyZ
  have hunion : Finset.Icc 1 ⌊Z⌋₊ = Finset.Icc 1 ⌊y⌋₊ ∪ Finset.Ioc ⌊y⌋₊ ⌊Z⌋₊ := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.Icc 1 ⌊y⌋₊) (Finset.Ioc ⌊y⌋₊ ⌊Z⌋₊) := by
    rw [Finset.disjoint_left]; intro n h1 h2; simp only [Finset.mem_Icc, Finset.mem_Ioc] at h1 h2; omega
  rw [hunion, Finset.sum_union hdisj]
  have hlo : ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (ZeroDensityWindow.cN y n) ^ 2 ≤ 6 * y * (Real.log Z + 2) ^ 2 := by
    have hpt : ∀ n ∈ Finset.Icc 1 ⌊y⌋₊, (ZeroDensityWindow.cN y n) ^ 2 ≤ Real.log Z * Λ n := by
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hn_le : (n : ℝ) ≤ y := (by exact_mod_cast (Finset.mem_Icc.mp hn).2 : (n : ℝ) ≤ (⌊y⌋₊ : ℝ)).trans
        (Nat.floor_le hy0.le)
      have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hmin : min 1 (y / (n : ℝ)) = 1 := min_eq_left ((one_le_div hn_pos).mpr hn_le)
      unfold ZeroDensityWindow.cN
      rw [hmin, mul_one, sq]
      have hΛ_le : Λ n ≤ Real.log Z :=
        ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hn_pos (hn_le.trans hyZ))
      exact mul_le_mul_of_nonneg_right hΛ_le ArithmeticFunction.vonMangoldt_nonneg
    have hpsi : ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, Λ n ≤ 6 * y := by
      have hsub : Finset.Icc 1 ⌊y⌋₊ ⊆ Finset.range (⌊y⌋₊ + 1) := fun n hn => by
        simp only [Finset.mem_Icc, Finset.mem_range] at hn ⊢; omega
      exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg).trans
        (Stage4ExplicitFormula.chebyshevPsi_le_six_mul hy)
    calc ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (ZeroDensityWindow.cN y n) ^ 2
        ≤ ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, Real.log Z * Λ n := Finset.sum_le_sum hpt
      _ = Real.log Z * ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, Λ n := (Finset.mul_sum _ _ _).symm
      _ ≤ Real.log Z * (6 * y) := mul_le_mul_of_nonneg_left hpsi hLZ_nn
      _ ≤ 6 * y * (Real.log Z + 2) ^ 2 := by nlinarith [sq_nonneg (Real.log Z + 1)]
  have hhi : ∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊Z⌋₊, (ZeroDensityWindow.cN y n) ^ 2 ≤ 2 * y * (Real.log Z + 2) ^ 2 := by
    have hpt : ∀ n ∈ Finset.Ioc ⌊y⌋₊ ⌊Z⌋₊,
        (ZeroDensityWindow.cN y n) ^ 2 ≤ (Real.log Z ^ 2 * y ^ 2) * (1 / (n : ℝ) ^ 2) := by
      intro n hn
      obtain ⟨hgt, hle⟩ := Finset.mem_Ioc.mp hn
      have hyn : y < (n : ℝ) := lt_of_lt_of_le (Nat.lt_floor_add_one y) (by exact_mod_cast hgt)
      have hn_le_Z : (n : ℝ) ≤ Z := (by exact_mod_cast hle : (n : ℝ) ≤ (⌊Z⌋₊ : ℝ)).trans (Nat.floor_le hZ0.le)
      have hn_pos : (0 : ℝ) < (n : ℝ) := lt_trans hy0 hyn
      have hmin : min 1 (y / (n : ℝ)) = y / (n : ℝ) := min_eq_right ((div_le_one hn_pos).mpr hyn.le)
      unfold ZeroDensityWindow.cN
      rw [hmin]
      have hΛ_le : Λ n ≤ Real.log Z :=
        ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hn_pos hn_le_Z)
      have h1 : Λ n * (y / (n : ℝ)) ≤ Real.log Z * (y / (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hΛ_le (by positivity)
      calc (Λ n * (y / (n : ℝ))) ^ 2
          ≤ (Real.log Z * (y / (n : ℝ))) ^ 2 :=
            pow_le_pow_left₀ (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)) h1 2
        _ = (Real.log Z ^ 2 * y ^ 2) * (1 / (n : ℝ) ^ 2) := by ring
    have hfl_ge1 : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by norm_cast : ((1 : ℕ) : ℝ) ≤ y)
    have hfl_half : y / 2 ≤ (⌊y⌋₊ : ℝ) := by
      rcases le_or_gt 2 y with h2 | hlt2
      · linarith [Nat.lt_floor_add_one y]
      · have h1 : (1 : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hfl_ge1
        linarith
    have hinv_fl : 1 / (⌊y⌋₊ : ℝ) ≤ 2 / y := by
      have hfl_pos : (0 : ℝ) < (⌊y⌋₊ : ℝ) := by exact_mod_cast (by omega : 0 < ⌊y⌋₊)
      rw [div_le_div_iff₀ hfl_pos hy0]; linarith
    calc ∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊Z⌋₊, (ZeroDensityWindow.cN y n) ^ 2
        ≤ ∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊Z⌋₊, (Real.log Z ^ 2 * y ^ 2) * (1 / (n : ℝ) ^ 2) := Finset.sum_le_sum hpt
      _ = (Real.log Z ^ 2 * y ^ 2) * ∑ n ∈ Finset.Ioc ⌊y⌋₊ ⌊Z⌋₊, (1 : ℝ) / (n : ℝ) ^ 2 :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ (Real.log Z ^ 2 * y ^ 2) * (1 / (⌊y⌋₊ : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_inv_sq_Ioc_le hfl_ge1) (by positivity)
      _ ≤ (Real.log Z ^ 2 * y ^ 2) * (2 / y) := mul_le_mul_of_nonneg_left hinv_fl (by positivity)
      _ = 2 * y * Real.log Z ^ 2 := by field_simp [hy0.ne']
      _ ≤ 2 * y * (Real.log Z + 2) ^ 2 := by nlinarith
  linarith

/-! ### Section 4b: Odd-Squarefree Quadratic Characters, Exact Reciprocity Factorization & Diagonal Bounds -/

/-- Canonical primitive quadratic Dirichlet character `χ_s(n) = (n | s)` for any odd squarefree `s ≥ 1`. -/
def quadCharOfOddSqf (s : ℕ) [NeZero s] (hs_odd : Odd s) : DirichletCharacter ℂ s where
  toFun := fun a => ((jacobiSym (a.val : ℤ) s : ℤ) : ℂ)
  map_one' := by
    by_cases hs1 : s = 1
    · subst hs1; simp [jacobiSym.one_right]
    · have hs_gt1 : 1 < s := by have := NeZero.pos s; omega
      have : Fact (1 < s) := ⟨hs_gt1⟩
      rw [ZMod.val_one, Nat.cast_one, jacobiSym.one_left]; simp
  map_mul' := fun a b => by
    have hmod : ((a * b).val : ℤ) ≡ (a.val : ℤ) * (b.val : ℤ) [ZMOD (s : ℤ)] := by
      rw [← Int.natCast_mul, Int.natCast_modEq_iff, ZMod.val_mul]; exact Nat.mod_modEq _ _
    rw [jacobiSym.mod_left' hmod, jacobiSym.mul_left, Int.cast_mul]
  map_nonunit' := fun a ha => by
    have hnotcop : ¬ Nat.Coprime a.val s := by
      intro hcop; apply ha
      have h1 : IsUnit ((a.val : ℕ) : ZMod s) := (ZMod.isUnit_iff_coprime a.val s).mpr hcop
      rwa [ZMod.natCast_zmod_val] at h1
    have hne1 : Nat.gcd a.val s ≠ 1 := hnotcop
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne1
    have hpa : p ∣ a.val := hpg.trans (Nat.gcd_dvd_left a.val s)
    have hps : p ∣ s := hpg.trans (Nat.gcd_dvd_right a.val s)
    rcases hps with ⟨s', hs'⟩
    have : NeZero p := ⟨hp.ne_zero⟩
    have : NeZero s' := ⟨by intro h0; rw [h0, mul_zero] at hs'; exact NeZero.ne s hs'⟩
    have hmod : (a.val : ℤ) ≡ 0 [ZMOD (p : ℤ)] :=
      Int.modEq_zero_iff_dvd.mpr (Int.natCast_dvd_natCast.mpr hpa)
    have hj0_aux : ∀ v : ℕ, (v : ℤ) ≡ 0 [ZMOD (p : ℤ)] → jacobiSym (v : ℤ) s = 0 := fun v hv => by
      rw [hs', jacobiSym.mul_right, jacobiSym.mod_left' hv, jacobiSym.zero_left hp.one_lt, zero_mul]
    rw [hj0_aux a.val hmod]; simp

theorem quadCharOfOddSqf_apply_nat {s : ℕ} [NeZero s] (hs_odd : Odd s) (n : ℕ) :
    quadCharOfOddSqf s hs_odd (n : ZMod s) = ((jacobiSym (n : ℤ) s : ℤ) : ℂ) := by
  change ((jacobiSym (((n : ZMod s).val : ℤ)) s : ℤ) : ℂ) = _
  have hmod : (((n : ZMod s).val : ℤ)) ≡ (n : ℤ) [ZMOD (s : ℤ)] := by
    rw [Int.natCast_modEq_iff, ZMod.val_natCast]; exact Nat.mod_modEq n s
  rw [jacobiSym.mod_left' hmod]

/-- Every odd prime `p` has a quadratic non-residue `g : ℕ` with `jacobiSym (g : ℤ) p = -1`. -/
private lemma exists_jacobiSym_neg_one_of_odd_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ g : ℕ, Nat.Coprime g p ∧ jacobiSym (g : ℤ) p = -1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hsq_not_inj : ¬ Function.Injective (fun u : (ZMod p)ˣ => u ^ 2) := by
    intro hinj
    have hneg_ne : (-1 : (ZMod p)ˣ) ≠ 1 := by
      intro h
      have hval : ((-1 : ZMod p)) = (1 : ZMod p) := congrArg Units.val h
      have h2 : (2 : ZMod p) = 0 := by linear_combination -hval
      have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h2)
      have := Nat.le_of_dvd (by norm_num) hdvd
      have := hp.two_le
      omega
    exact hneg_ne (hinj (by simp))
  have hsq_not_surj : ¬ Function.Surjective (fun u : (ZMod p)ˣ => u ^ 2) :=
    fun hsurj => hsq_not_inj (Finite.injective_iff_surjective.mpr hsurj)
  unfold Function.Surjective at hsq_not_surj
  push Not at hsq_not_surj
  obtain ⟨u, hu⟩ := hsq_not_surj
  refine ⟨(u : ZMod p).val, ZMod.val_coe_unit_coprime u, ?_⟩
  have hnot_sq : ¬ IsSquare ((u : ZMod p)) := by
    rintro ⟨x, hx⟩
    have hx_nz : x ≠ 0 := fun h0 => by rw [h0, mul_zero] at hx; exact Units.ne_zero u hx
    have hxu : IsUnit x := isUnit_iff_ne_zero.mpr hx_nz
    apply hu hxu.unit
    apply Units.ext
    change x ^ 2 = (u : ZMod p)
    rw [sq]; exact hx.symm
  have hleg : legendreSym p (((u : ZMod p).val : ℕ) : ℤ) = -1 := by
    rw [legendreSym.eq_neg_one_iff]
    simpa [ZMod.natCast_zmod_val] using hnot_sq
  rwa [← jacobiSym.legendreSym.to_jacobiSym]

/-- **Primitivity of `quadCharOfOddSqf`**: for any odd squarefree `s ≥ 1`, `quadCharOfOddSqf s` is primitive! -/
theorem quadCharOfOddSqf_isPrimitive {s : ℕ} [NeZero s] (hs_odd : Odd s) (hs_sqf : Squarefree s) :
    (quadCharOfOddSqf s hs_odd).IsPrimitive := by
  set χ := quadCharOfOddSqf s hs_odd
  set f := χ.conductor
  have hf_dvd : f ∣ s := χ.conductor_dvd_level
  have hf_pos : 0 < f := Nat.pos_of_ne_zero χ.conductor_ne_zero
  have : NeZero f := ⟨hf_pos.ne'⟩
  have hker : MonoidHom.ker (ZMod.unitsMap hf_dvd) ≤ MonoidHom.ker χ.toUnitHom :=
    (DirichletCharacter.factorsThrough_iff_ker_unitsMap hf_dvd).mp (DirichletCharacter.factorsThrough_conductor χ)
  by_contra hne
  have hf_lt : f < s := lt_of_le_of_ne (Nat.le_of_dvd (NeZero.pos s) hf_dvd) hne
  have ⟨k, hk⟩ := hf_dvd
  have hk_gt1 : 1 < k := by nlinarith
  obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd (by omega : k ≠ 1)
  have hps : p ∣ s := hk ▸ dvd_mul_of_dvd_right hpk f
  rcases hps with ⟨s', hs'⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero s' := ⟨by intro h0; rw [h0, mul_zero] at hs'; exact NeZero.ne s hs'⟩
  have hp_not_s' : ¬ p ∣ s' := by
    intro hps'
    have hp2 : p * p ∣ s := hs' ▸ Nat.mul_dvd_mul_left p hps'
    exact hp.not_isUnit (hs_sqf p hp2)
  have hcop_ps' : Nat.Coprime p s' := (Nat.Prime.coprime_iff_not_dvd hp).mpr hp_not_s'
  have hf_dvd_s' : f ∣ s' := by
    have h1 : f ∣ p * s' := hs' ▸ ⟨k, hk⟩
    have hnot_pf : ¬ p ∣ f := by
      intro hpf
      have hp2 : p * p ∣ s := hk ▸ Nat.mul_dvd_mul hpf hpk
      exact hp.not_isUnit (hs_sqf p hp2)
    have hcop_fp : Nat.Coprime f p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnot_pf).symm
    exact hcop_fp.dvd_of_dvd_mul_left h1
  have hp2 : p ≠ 2 := by
    rintro rfl; obtain ⟨t, ht⟩ := hs_odd; omega
  obtain ⟨g, hcop_gp, hjac_g⟩ := exists_jacobiSym_neg_one_of_odd_prime hp hp2
  let cr := Nat.chineseRemainder hcop_ps' g 1
  set n := cr.val
  have hcop_np : Nat.Coprime n p := cr.property.1.gcd_eq.trans hcop_gp
  have hcop_ns' : Nat.Coprime n s' := cr.property.2.gcd_eq.trans (Nat.coprime_one_left s')
  have hcop_ns : Nat.Coprime n s := hs' ▸ hcop_np.mul_right hcop_ns'
  have hu : IsUnit (n : ZMod s) := (ZMod.isUnit_iff_coprime n s).mpr hcop_ns
  have hn1_f : n ≡ 1 [MOD f] := cr.property.2.of_dvd hf_dvd_s'
  have hu_ker : hu.unit ∈ MonoidHom.ker (ZMod.unitsMap hf_dvd) := by
    rw [MonoidHom.mem_ker]; apply Units.ext
    change ZMod.castHom hf_dvd (ZMod f) (n : ZMod s) = 1
    rw [map_natCast]
    simpa using (ZMod.natCast_eq_natCast_iff n 1 f).mpr hn1_f
  have hχ1 : χ (n : ZMod s) = 1 := by
    have h1 := hker hu_ker
    rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one] at h1
    simpa [IsUnit.unit_spec] using h1
  have hχ_neg : χ (n : ZMod s) = -1 := by
    rw [show χ = quadCharOfOddSqf s hs_odd from rfl, quadCharOfOddSqf_apply_nat hs_odd n, hs',
      jacobiSym.mul_right]
    have hmod_p : (n : ℤ) ≡ (g : ℤ) [ZMOD (p : ℤ)] := Int.natCast_modEq_iff.mpr cr.property.1
    have hmod_s' : (n : ℤ) ≡ (1 : ℤ) [ZMOD (s' : ℤ)] := Int.natCast_modEq_iff.mpr cr.property.2
    rw [jacobiSym.mod_left' hmod_p, jacobiSym.mod_left' hmod_s', hjac_g, jacobiSym.one_left]
    simp
  rw [hχ1] at hχ_neg
  norm_num at hχ_neg

/-- Odd squarefree part of `k` coprime to `m₀` (product of odd primes `p ∣ k` with `¬ p ∣ m₀` and odd `v_p(k)`). -/
def soutPart (m₀ k : ℕ) : ℕ :=
  ∏ p ∈ k.primeFactors.filter (fun p => p ≠ 2 ∧ ¬ p ∣ m₀ ∧ Odd (k.factorization p)), p

/-- Odd squarefree part of `k` dividing `m₀` (product of odd primes `p ∣ k` with `p ∣ m₀` and odd `v_p(k)`). -/
def sinPart (m₀ k : ℕ) : ℕ :=
  ∏ p ∈ k.primeFactors.filter (fun p => p ≠ 2 ∧ p ∣ m₀ ∧ Odd (k.factorization p)), p

/-- Odd square-root part of `k`: `∏_{p ∈ k.primeFactors, p ≠ 2} p^(v_p(k) / 2)`. -/
private def oddSqRootPart (k : ℕ) : ℕ :=
  ∏ p ∈ k.primeFactors.filter (fun p => p ≠ 2), p ^ (k.factorization p / 2)

private lemma prod_primes_squarefree {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    Squarefree (∏ p ∈ S, p) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have ha_pr : a.Prime := hS a (Finset.mem_insert_self _ _)
    have hs_pr : ∀ p ∈ s, p.Prime := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have hcop : Nat.Coprime a (∏ p ∈ s, p) :=
      Nat.Coprime.prod_right fun p hp =>
        (Nat.coprime_primes ha_pr (hs_pr p hp)).mpr fun h => ha (h ▸ hp)
    exact (Nat.squarefree_mul hcop).mpr ⟨ha_pr.squarefree, ih hs_pr⟩

private lemma prod_odd_of_forall_odd {S : Finset ℕ} (hS : ∀ p ∈ S, Odd p) :
    Odd (∏ p ∈ S, p) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hS a (Finset.mem_insert_self _ _)).mul (ih fun p hp => hS p (Finset.mem_insert_of_mem hp))

theorem soutPart_props (m₀ k : ℕ) :
    Odd (soutPart m₀ k) ∧ Squarefree (soutPart m₀ k) ∧ Nat.Coprime (soutPart m₀ k) m₀ ∧
      (1 ≤ k → soutPart m₀ k ≤ k) := by
  unfold soutPart
  have hpr : ∀ p ∈ k.primeFactors.filter (fun p => p ≠ 2 ∧ ¬ p ∣ m₀ ∧ Odd (k.factorization p)), p.Prime :=
    fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  refine ⟨prod_odd_of_forall_odd fun p hp => (hpr p hp).odd_of_ne_two (Finset.mem_filter.mp hp).2.1,
    prod_primes_squarefree hpr,
    Nat.Coprime.prod_left fun p hp =>
      (Nat.Prime.coprime_iff_not_dvd (hpr p hp)).mpr (Finset.mem_filter.mp hp).2.2.1,
    fun hk => ?_⟩
  have hdvd : (∏ p ∈ k.primeFactors.filter (fun p => p ≠ 2 ∧ ¬ p ∣ m₀ ∧ Odd (k.factorization p)), p) ∣ k := by
    have hsub : k.primeFactors.filter (fun p => p ≠ 2 ∧ ¬ p ∣ m₀ ∧ Odd (k.factorization p)) ⊆ k.primeFactors :=
      Finset.filter_subset _ _
    exact (Finset.prod_dvd_prod_of_subset _ _ _ hsub).trans (Nat.prod_primeFactors_dvd k)
  exact Nat.le_of_dvd hk hdvd

private lemma sinPart_props (m₀ k : ℕ) :
    Odd (sinPart m₀ k) ∧ sinPart m₀ k ∣ m₀ := by
  unfold sinPart
  have hpr : ∀ p ∈ k.primeFactors.filter (fun p => p ≠ 2 ∧ p ∣ m₀ ∧ Odd (k.factorization p)), p.Prime :=
    fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  refine ⟨prod_odd_of_forall_odd fun p hp => (hpr p hp).odd_of_ne_two (Finset.mem_filter.mp hp).2.1, ?_⟩
  have hgen : ∀ (S : Finset ℕ), (∀ p ∈ S, p.Prime ∧ p ∣ m₀) → (∏ p ∈ S, p) ∣ m₀ := by
    intro S
    classical
    induction S using Finset.induction_on with
    | empty => intro _; simp
    | insert a s ha ih =>
      intro hS
      rw [Finset.prod_insert ha]
      have ha' := hS a (Finset.mem_insert_self _ _)
      have hs' : ∀ p ∈ s, p.Prime ∧ p ∣ m₀ := fun p hp => hS p (Finset.mem_insert_of_mem hp)
      have hcop : Nat.Coprime a (∏ p ∈ s, p) :=
        Nat.Coprime.prod_right fun p hp =>
          (Nat.coprime_primes ha'.1 (hs' p hp).1).mpr fun h => ha (h ▸ hp)
      exact hcop.mul_dvd_of_dvd_of_dvd ha'.2 (ih hs')
  exact hgen _ fun p hp => ⟨hpr p hp, (Finset.mem_filter.mp hp).2.2.1⟩

private lemma exact_factor_soutPart (m₀ : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    k = 2 ^ (k.factorization 2) * sinPart m₀ k * soutPart m₀ k * (oddSqRootPart k) ^ 2 := by
  have hk_ne : k ≠ 0 := by omega
  have hself : ∏ p ∈ k.primeFactors, p ^ (k.factorization p) = k := by
    simpa [Finsupp.prod, Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hk_ne
  conv_lhs => rw [← hself]
  set S_odd := k.primeFactors.filter (fun p => p ≠ 2)
  have hsplit2 : ∏ p ∈ k.primeFactors, p ^ (k.factorization p) =
      2 ^ (k.factorization 2) * ∏ p ∈ S_odd, p ^ (k.factorization p) := by
    by_cases h2 : 2 ∈ k.primeFactors
    · have hunion : k.primeFactors = insert 2 S_odd := by
        ext p; simp only [S_odd, Finset.mem_insert, Finset.mem_filter]
        constructor
        · intro hp
          by_cases hp2 : p = 2
          · exact Or.inl hp2
          · exact Or.inr ⟨hp, hp2⟩
        · rintro (rfl | ⟨hp, _⟩)
          · exact h2
          · exact hp
      rw [hunion, Finset.prod_insert (by simp [S_odd])]
    · have h0 : k.factorization 2 = 0 := by
        by_contra hne; exact h2 (Nat.mem_primeFactors.mpr ⟨Nat.prime_two,
          (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hk_ne).mpr (by omega), hk_ne⟩)
      have heq : S_odd = k.primeFactors := by
        ext p; simp only [S_odd, Finset.mem_filter, and_iff_left_iff_imp]; rintro hp rfl; exact h2 hp
      rw [h0, pow_zero, one_mul, heq]
  have hodd_part : ∀ p ∈ S_odd,
      p ^ (k.factorization p) =
        (if p ∣ m₀ ∧ Odd (k.factorization p) then p else 1) *
        (if ¬ p ∣ m₀ ∧ Odd (k.factorization p) then p else 1) *
        (p ^ (k.factorization p / 2)) ^ 2 := by
    intro p _
    by_cases hodd : Odd (k.factorization p)
    · have hdiv : 2 * (k.factorization p / 2) + 1 = k.factorization p := by
        obtain ⟨t, ht⟩ := hodd; omega
      by_cases hm : p ∣ m₀
      · simp only [hm, hodd, and_self, ↓reduceIte, not_true_eq_false, false_and, mul_one]
        rw [← pow_mul, mul_comm (k.factorization p / 2) 2, mul_comm p, ← pow_succ, hdiv]
      · simp only [hm, hodd, false_and, ↓reduceIte, not_false_eq_true, and_self, one_mul]
        rw [← pow_mul, mul_comm (k.factorization p / 2) 2, mul_comm p, ← pow_succ, hdiv]
    · have heven : Even (k.factorization p) := Nat.not_odd_iff_even.mp hodd
      have hdiv : 2 * (k.factorization p / 2) = k.factorization p := by obtain ⟨t, ht⟩ := heven; omega
      simp only [hodd, and_false, ↓reduceIte, one_mul]
      rw [← pow_mul, mul_comm (k.factorization p / 2) 2, hdiv]
  have hodd_eq : ∏ p ∈ S_odd, p ^ (k.factorization p) =
      sinPart m₀ k * soutPart m₀ k * (oddSqRootPart k) ^ 2 := by
    calc ∏ p ∈ S_odd, p ^ (k.factorization p)
        = ∏ p ∈ S_odd,
            ((if p ∣ m₀ ∧ Odd (k.factorization p) then p else 1) *
             (if ¬ p ∣ m₀ ∧ Odd (k.factorization p) then p else 1) *
             (p ^ (k.factorization p / 2)) ^ 2) := Finset.prod_congr rfl hodd_part
      _ = (∏ p ∈ S_odd, if p ∣ m₀ ∧ Odd (k.factorization p) then p else 1) *
          (∏ p ∈ S_odd, if ¬ p ∣ m₀ ∧ Odd (k.factorization p) then p else 1) *
          (∏ p ∈ S_odd, (p ^ (k.factorization p / 2)) ^ 2) := by
          simp only [Finset.prod_mul_distrib]
      _ = sinPart m₀ k * soutPart m₀ k * (oddSqRootPart k) ^ 2 := by
          rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_ite, Finset.prod_const_one, mul_one,
            Finset.prod_pow]
          unfold sinPart soutPart oddSqRootPart S_odd
          congr 1
          congr 1
          · congr 1; ext p; simp only [Finset.mem_filter]; tauto
          · congr 1; ext p; simp only [Finset.mem_filter]; tauto
  rw [hsplit2, hodd_eq]; ring

/-- **Exact Quadratic-Reciprocity Factorization (`jacobiSym_factor_soutPart`)**:
for `8 ∣ m₀`, `a₀ % 4 = 3`, `r ≡ a₀ [MOD m₀]`, `Odd r`, and `1 ≤ k` with `Coprime k r`,
there exists a sign `ε ∈ {-1, 1}` (depending ONLY on `m₀, a₀, k`, independent of `r`) such that
`jacobiSym (k : ℤ) r = ε * jacobiSym (r : ℤ) (soutPart m₀ k)`! -/
theorem jacobiSym_factor_soutPart {m₀ a₀ : ℕ} (h8 : 8 ∣ m₀) (ha4 : a₀ % 4 = 3)
    {k : ℕ} (hk : 1 ≤ k) :
    ∃ ε : ℤ, |ε| = 1 ∧ ∀ r : ℕ, Odd r → r ≡ a₀ [MOD m₀] → Nat.Coprime k r →
      jacobiSym (k : ℤ) r = ε * jacobiSym (r : ℤ) (soutPart m₀ k) := by
  have ha_odd : Odd a₀ := Nat.odd_iff.mpr (by omega)
  have hsin := sinPart_props m₀ k
  have hsout := soutPart_props m₀ k
  set ε : ℤ :=
    (ZMod.χ₈ (a₀ : ZMod 8)) ^ (k.factorization 2) *
    (ZMod.χ₄ (sinPart m₀ k : ZMod 4) * jacobiSym (a₀ : ℤ) (sinPart m₀ k)) *
    ZMod.χ₄ (soutPart m₀ k : ZMod 4)
  -- Helper: `|ZMod.χ₄ n| = 1` for odd `n`
  have hχ4_abs : ∀ n : ℕ, Odd n → |ZMod.χ₄ (n : ZMod 4)| = 1 := fun n hn => by
    have h4 : n % 4 = 1 ∨ n % 4 = 3 := by obtain ⟨t, rfl⟩ := hn; omega
    rcases h4 with h1 | h3
    · rw [ZMod.χ₄_nat_one_mod_four h1]; norm_num
    · rw [ZMod.χ₄_nat_three_mod_four h3]; norm_num
  have hχ8_abs : |ZMod.χ₈ (a₀ : ZMod 8)| = 1 := by
    have h8a : a₀ % 8 = 3 ∨ a₀ % 8 = 7 := by omega
    rcases h8a with h3 | h7
    · have : (a₀ : ZMod 8) = (3 : ZMod 8) := by
        rw [← Nat.cast_ofNat (n := 3), ZMod.natCast_eq_natCast_iff]; change a₀ % 8 = 3 % 8; omega
      rw [this]; decide
    · have : (a₀ : ZMod 8) = (7 : ZMod 8) := by
        rw [← Nat.cast_ofNat (n := 7), ZMod.natCast_eq_natCast_iff]; change a₀ % 8 = 7 % 8; omega
      rw [this]; decide
  -- Wait: if `¬ Coprime a₀ (sinPart m₀ k)`, then for ANY `r ≡ a₀ [MOD m₀]`, `¬ Coprime r (sinPart m₀ k)`,
  -- which is impossible when `Coprime k r` since `sinPart m₀ k ∣ k`!
  -- So case-split on `Nat.Coprime a₀ (sinPart m₀ k)`!
  by_cases hcop_as : Nat.Coprime a₀ (sinPart m₀ k)
  · refine ⟨ε, ?_, fun r hr_odd hr_mod hcop_kr => ?_⟩
    · have hjac_abs : |jacobiSym (a₀ : ℤ) (sinPart m₀ k)| = 1 := by
        rcases jacobiSym.eq_one_or_neg_one (a := (a₀ : ℤ)) (b := sinPart m₀ k)
          (by rw [Int.gcd_natCast_natCast]; exact hcop_as) with h1 | h1 <;> rw [h1] <;> norm_num
      dsimp only [ε]
      rw [abs_mul, abs_mul, abs_mul, abs_pow, hχ8_abs, one_pow, hχ4_abs _ hsin.1, hjac_abs,
        hχ4_abs _ hsout.1]
      norm_num
    · have hr8 : r ≡ a₀ [MOD 8] := hr_mod.of_dvd h8
      have hr4 : r % 4 = 3 := by
        have : r ≡ a₀ [MOD 4] := hr8.of_dvd (by norm_num)
        change r % 4 = a₀ % 4 at this; omega
      have hfac := exact_factor_soutPart m₀ hk
      have hcop_sq : Nat.Coprime (oddSqRootPart k) r := by
        have hdvd_k : oddSqRootPart k ∣ k := by
          have : (oddSqRootPart k) ^ 2 ∣ k := ⟨2 ^ (k.factorization 2) * sinPart m₀ k * soutPart m₀ k, by linarith [hfac]⟩
          exact (dvd_pow_self _ (by norm_num)).trans this
        exact hcop_kr.coprime_dvd_left hdvd_k
      have hjac_2 : jacobiSym ((2 : ℤ) ^ k.factorization 2) r =
          (ZMod.χ₈ (a₀ : ZMod 8)) ^ (k.factorization 2) := by
        rw [jacobiSym.pow_left, jacobiSym.at_two hr_odd]
        have hcast8 : (r : ZMod 8) = (a₀ : ZMod 8) := (ZMod.natCast_eq_natCast_iff r a₀ 8).mpr hr8
        rw [hcast8]
      have hrec_3 : ∀ b : ℕ, Odd b → jacobiSym (b : ℤ) r = ZMod.χ₄ (b : ZMod 4) * jacobiSym (r : ℤ) b := by
        intro b hb
        have hb4 : b % 4 = 1 ∨ b % 4 = 3 := by obtain ⟨t, rfl⟩ := hb; omega
        rcases hb4 with h1 | h3
        · rw [ZMod.χ₄_nat_one_mod_four h1, one_mul, jacobiSym.quadratic_reciprocity_one_mod_four h1 hr_odd]
        · rw [ZMod.χ₄_nat_three_mod_four h3, neg_one_mul]
          linarith [jacobiSym.quadratic_reciprocity_three_mod_four h3 hr4]
      have hjac_sin : jacobiSym (sinPart m₀ k : ℤ) r =
          ZMod.χ₄ (sinPart m₀ k : ZMod 4) * jacobiSym (a₀ : ℤ) (sinPart m₀ k) := by
        rw [hrec_3 _ hsin.1]
        have hmod_sin : (r : ℤ) ≡ (a₀ : ℤ) [ZMOD (sinPart m₀ k : ℤ)] :=
          Int.natCast_modEq_iff.mpr (hr_mod.of_dvd hsin.2)
        rw [jacobiSym.mod_left' hmod_sin]
      have hjac_sout : jacobiSym (soutPart m₀ k : ℤ) r =
          ZMod.χ₄ (soutPart m₀ k : ZMod 4) * jacobiSym (r : ℤ) (soutPart m₀ k) :=
        hrec_3 _ hsout.1
      have hjac_sq : jacobiSym ((oddSqRootPart k : ℤ) ^ 2) r = 1 := by
        rw [jacobiSym.pow_left]
        rcases jacobiSym.eq_one_or_neg_one (a := (oddSqRootPart k : ℤ)) (b := r)
          (by rw [Int.gcd_natCast_natCast]; exact hcop_sq) with h1 | h1 <;> rw [h1] <;> norm_num
      conv_lhs => rw [hfac]
      push_cast
      rw [jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.mul_left,
        hjac_2, hjac_sin, hjac_sout, hjac_sq, mul_one]
      dsimp only [ε]; ring
  · refine ⟨1, by norm_num, fun r _ hr_mod hcop_kr => ?_⟩
    exfalso; apply hcop_as
    have hfac := exact_factor_soutPart m₀ hk
    have hdvd_k : sinPart m₀ k ∣ k := by
      conv_rhs => rw [hfac]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _
    have hcop_sr : Nat.Coprime (sinPart m₀ k) r := hcop_kr.coprime_dvd_left hdvd_k
    exact ((hr_mod.of_dvd hsin.2).symm.gcd_eq.trans hcop_sr.symm)

open Classical in
/-- Sum of `cN y (p ^ a)` over all powers `a ≥ 1` of a single prime `p` with `p ^ a ≤ Z`:
- Always `≤ 2 * (Real.log Z + 2)` (for any prime `p` and `1 ≤ Z`), AND
- For `y < p`: `≤ 2 * (Real.log Z + 2) * (y / p)`. -/
private lemma sum_cN_prime_powers_le {y Z : ℝ} (hy : 1 ≤ y) (hyZ : y ≤ Z) {p : ℕ} (hp : p.Prime) :
    (∑ n ∈ (Finset.Icc 1 ⌊Z⌋₊).filter (fun n => ∃ a : ℕ, 1 ≤ a ∧ n = p ^ a),
        ZeroDensityWindow.cN y n ≤ 2 * (Real.log Z + 2)) ∧
    (y < (p : ℝ) →
      ∑ n ∈ (Finset.Icc 1 ⌊Z⌋₊).filter (fun n => ∃ a : ℕ, 1 ≤ a ∧ n = p ^ a),
        ZeroDensityWindow.cN y n ≤ 2 * (Real.log Z + 2) * (y / (p : ℝ))) := by
  have hy0 : 0 < y := by linarith
  have hZ0 : 0 < Z := by linarith
  have hLZ_nn : 0 ≤ Real.log Z := Real.log_nonneg (by linarith)
  have hp2 : 2 ≤ p := hp.two_le
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hlogp_pos : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  set S_p := (Finset.Icc 1 ⌊Z⌋₊).filter (fun n => ∃ a : ℕ, 1 ≤ a ∧ n = p ^ a)
  set Kmax : ℕ := ⌊Real.log Z / Real.log (p : ℝ)⌋₊
  have hsub_img : S_p ⊆ (Finset.Icc 1 Kmax).image (fun a => p ^ a) := by
    intro n hn
    obtain ⟨hn_icc, a, ha1, rfl⟩ := Finset.mem_filter.mp hn
    have hpa_le : ((p ^ a : ℕ) : ℝ) ≤ Z :=
      (by exact_mod_cast (Finset.mem_Icc.mp hn_icc).2 : ((p ^ a : ℕ) : ℝ) ≤ (⌊Z⌋₊ : ℝ)).trans (Nat.floor_le hZ0.le)
    have hlog_le : (a : ℝ) * Real.log (p : ℝ) ≤ Real.log Z := by
      have h1 := Real.log_le_log (by positivity) hpa_le
      rwa [Nat.cast_pow, Real.log_pow] at h1
    have ha_le : a ≤ Kmax := Nat.le_floor ((le_div_iff₀ hlogp_pos).mpr hlog_le)
    exact Finset.mem_image.mpr ⟨a, Finset.mem_Icc.mpr ⟨ha1, ha_le⟩, rfl⟩
  have hsum_le_img : ∑ n ∈ S_p, ZeroDensityWindow.cN y n ≤
      ∑ a ∈ Finset.Icc 1 Kmax, ZeroDensityWindow.cN y (p ^ a) := by
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg (f := ZeroDensityWindow.cN y) hsub_img fun n _ _ =>
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (le_min zero_le_one (by positivity))
    exact h1.trans (Finset.sum_image_le_of_nonneg fun a _ =>
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (le_min zero_le_one (by positivity)))
  have hΛ_pa : ∀ a : ℕ, 1 ≤ a → Λ (p ^ a) = Real.log (p : ℝ) := fun a ha => by
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega : a ≠ 0), ArithmeticFunction.vonMangoldt_apply_prime hp]
  constructor
  · -- Bound 1: `≤ 2 * (Real.log Z + 2)` via `cN y (p^a) ≤ log p` and `Kmax ≤ log Z / log p`
    have hterm : ∀ a ∈ Finset.Icc 1 Kmax, ZeroDensityWindow.cN y (p ^ a) ≤ Real.log (p : ℝ) := by
      intro a ha
      unfold ZeroDensityWindow.cN
      rw [hΛ_pa a (Finset.mem_Icc.mp ha).1]
      exact mul_le_of_le_one_right hlogp_pos.le (min_le_left _ _)
    have hK_le : (Kmax : ℝ) * Real.log (p : ℝ) ≤ Real.log Z :=
      (le_div_iff₀ hlogp_pos).mp (Nat.floor_le (by positivity))
    calc ∑ n ∈ S_p, ZeroDensityWindow.cN y n
        ≤ ∑ a ∈ Finset.Icc 1 Kmax, ZeroDensityWindow.cN y (p ^ a) := hsum_le_img
      _ ≤ ∑ _a ∈ Finset.Icc 1 Kmax, Real.log (p : ℝ) := Finset.sum_le_sum hterm
      _ = ((Finset.Icc 1 Kmax).card : ℝ) * Real.log (p : ℝ) := by simp
      _ = (Kmax : ℝ) * Real.log (p : ℝ) := by rw [Nat.card_Icc]; simp
      _ ≤ Real.log Z := hK_le
      _ ≤ 2 * (Real.log Z + 2) := by linarith
  · -- Bound 2: for `y < p`, geometric series `∑_{a=1}^{Kmax} (1/p)^a ≤ 2 / p`
    intro _hyp
    by_cases hpZ : (p : ℝ) ≤ Z
    · have hlogp_leZ : Real.log (p : ℝ) ≤ Real.log Z := Real.log_le_log hp_pos hpZ
      have hterm : ∀ a ∈ Finset.Icc 1 Kmax,
          ZeroDensityWindow.cN y (p ^ a) ≤ Real.log Z * y * ((1 / (p : ℝ)) ^ a) := by
        intro a ha
        have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
        unfold ZeroDensityWindow.cN
        rw [hΛ_pa a ha1]
        have hmin_le : min 1 (y / ((p ^ a : ℕ) : ℝ)) ≤ y / ((p ^ a : ℕ) : ℝ) := min_le_right _ _
        calc Real.log (p : ℝ) * min 1 (y / ((p ^ a : ℕ) : ℝ))
            ≤ Real.log Z * (y / ((p ^ a : ℕ) : ℝ)) :=
              mul_le_mul hlogp_leZ hmin_le (le_min zero_le_one (by positivity)) hLZ_nn
          _ = Real.log Z * y * ((1 / (p : ℝ)) ^ a) := by
              rw [Nat.cast_pow, one_div, inv_pow, div_eq_mul_inv]; ring
      have hgeom : ∑ a ∈ Finset.Icc 1 Kmax, (1 / (p : ℝ)) ^ a ≤ 2 / (p : ℝ) := by
        have hle_half : ∀ a : ℕ, 1 ≤ a → (1 / (p : ℝ)) ^ a ≤ (1 / (p : ℝ)) * (1 / 2 : ℝ) ^ (a - 1) := by
          intro a ha
          have ha_eq : a = (a - 1) + 1 := by omega
          conv_lhs => rw [ha_eq, pow_succ']
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact pow_le_pow_left₀ (by positivity) (one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp2)) _
        have hsum_half : ∑ a ∈ Finset.Icc 1 Kmax, (1 / 2 : ℝ) ^ (a - 1) ≤ 2 := by
          have hstep : ∀ m : ℕ, ∑ a ∈ Finset.Icc 1 m, (1 / 2 : ℝ) ^ (a - 1) = 2 - 2 * (1 / 2 : ℝ) ^ m := by
            intro m
            induction m with
            | zero => simp
            | succ m ih =>
              have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
                ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
              rw [hIcc, Finset.sum_insert (by simp), ih, Nat.add_sub_cancel, pow_succ]; ring
          rw [hstep Kmax]; linarith [show (0 : ℝ) ≤ 2 * (1 / 2 : ℝ) ^ Kmax by positivity]
        calc ∑ a ∈ Finset.Icc 1 Kmax, (1 / (p : ℝ)) ^ a
            ≤ ∑ a ∈ Finset.Icc 1 Kmax, (1 / (p : ℝ)) * (1 / 2 : ℝ) ^ (a - 1) :=
              Finset.sum_le_sum fun a ha => hle_half a (Finset.mem_Icc.mp ha).1
          _ = (1 / (p : ℝ)) * ∑ a ∈ Finset.Icc 1 Kmax, (1 / 2 : ℝ) ^ (a - 1) := (Finset.mul_sum _ _ _).symm
          _ ≤ (1 / (p : ℝ)) * 2 := mul_le_mul_of_nonneg_left hsum_half (by positivity)
          _ = 2 / (p : ℝ) := by ring
      calc ∑ n ∈ S_p, ZeroDensityWindow.cN y n
          ≤ ∑ a ∈ Finset.Icc 1 Kmax, ZeroDensityWindow.cN y (p ^ a) := hsum_le_img
        _ ≤ ∑ a ∈ Finset.Icc 1 Kmax, Real.log Z * y * ((1 / (p : ℝ)) ^ a) := Finset.sum_le_sum hterm
        _ = (Real.log Z * y) * ∑ a ∈ Finset.Icc 1 Kmax, (1 / (p : ℝ)) ^ a := (Finset.mul_sum _ _ _).symm
        _ ≤ (Real.log Z * y) * (2 / (p : ℝ)) := mul_le_mul_of_nonneg_left hgeom (by positivity)
        _ = 2 * Real.log Z * (y / (p : ℝ)) := by ring
        _ ≤ 2 * (Real.log Z + 2) * (y / (p : ℝ)) := by
            have : 0 ≤ y / (p : ℝ) := by positivity
            nlinarith
    · push Not at hpZ
      have hempty : S_p = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro n hn
        obtain ⟨hn_icc, a, ha1, rfl⟩ := Finset.mem_filter.mp hn
        have hpa_le : ((p ^ a : ℕ) : ℝ) ≤ Z :=
          (by exact_mod_cast (Finset.mem_Icc.mp hn_icc).2 : ((p ^ a : ℕ) : ℝ) ≤ (⌊Z⌋₊ : ℝ)).trans (Nat.floor_le hZ0.le)
        have hp_le_pa : (p : ℝ) ≤ ((p ^ a : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_self_pow (by omega : a ≠ 0) p
        linarith
      rw [hempty, Finset.sum_empty]; positivity

open Classical in
/-- Sum of `cN y (p ^ a)` over higher prime powers `a ≥ 2` for a single prime `p > √y`:
`≤ 2 * (Real.log Z + 2) * (y / p^2)`. -/
private lemma sum_cN_higher_powers_le {y Z : ℝ} (hy : 1 ≤ y) (hyZ : y ≤ Z) {p : ℕ} (hp : p.Prime) :
    ∑ n ∈ (Finset.Icc 1 ⌊Z⌋₊).filter (fun n => ∃ a : ℕ, 2 ≤ a ∧ n = p ^ a),
      ZeroDensityWindow.cN y n ≤ 2 * (Real.log Z + 2) * (y / (p : ℝ) ^ 2) := by
  have hy0 : 0 < y := by linarith
  have hZ0 : 0 < Z := by linarith
  have hLZ_nn : 0 ≤ Real.log Z := Real.log_nonneg (by linarith)
  have hp2 : 2 ≤ p := hp.two_le
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hlogp_pos : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  set S_p := (Finset.Icc 1 ⌊Z⌋₊).filter (fun n => ∃ a : ℕ, 2 ≤ a ∧ n = p ^ a)
  by_cases hpZ : (p : ℝ) ≤ Z
  · set Kmax : ℕ := ⌊Real.log Z / Real.log (p : ℝ)⌋₊
    have hsub_img : S_p ⊆ (Finset.Icc 2 Kmax).image (fun a => p ^ a) := by
      intro n hn
      obtain ⟨hn_icc, a, ha2, rfl⟩ := Finset.mem_filter.mp hn
      have hpa_le : ((p ^ a : ℕ) : ℝ) ≤ Z :=
        (by exact_mod_cast (Finset.mem_Icc.mp hn_icc).2 : ((p ^ a : ℕ) : ℝ) ≤ (⌊Z⌋₊ : ℝ)).trans (Nat.floor_le hZ0.le)
      have hlog_le : (a : ℝ) * Real.log (p : ℝ) ≤ Real.log Z := by
        have h1 := Real.log_le_log (by positivity) hpa_le
        rwa [Nat.cast_pow, Real.log_pow] at h1
      have ha_le : a ≤ Kmax := Nat.le_floor ((le_div_iff₀ hlogp_pos).mpr hlog_le)
      exact Finset.mem_image.mpr ⟨a, Finset.mem_Icc.mpr ⟨ha2, ha_le⟩, rfl⟩
    have hsum_le_img : ∑ n ∈ S_p, ZeroDensityWindow.cN y n ≤
        ∑ a ∈ Finset.Icc 2 Kmax, ZeroDensityWindow.cN y (p ^ a) :=
      (Finset.sum_le_sum_of_subset_of_nonneg hsub_img fun _ _ _ =>
        mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (le_min zero_le_one (by positivity))).trans
        (Finset.sum_image_le_of_nonneg fun _ _ =>
          mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (le_min zero_le_one (by positivity)))
    have hlogp_leZ : Real.log (p : ℝ) ≤ Real.log Z := Real.log_le_log hp_pos hpZ
    have hterm : ∀ a ∈ Finset.Icc 2 Kmax,
        ZeroDensityWindow.cN y (p ^ a) ≤ Real.log Z * y * ((1 / (p : ℝ)) ^ a) := by
      intro a ha
      have ha2 : 2 ≤ a := (Finset.mem_Icc.mp ha).1
      unfold ZeroDensityWindow.cN
      rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega : a ≠ 0), ArithmeticFunction.vonMangoldt_apply_prime hp]
      calc Real.log (p : ℝ) * min 1 (y / ((p ^ a : ℕ) : ℝ))
          ≤ Real.log Z * (y / ((p ^ a : ℕ) : ℝ)) :=
            mul_le_mul hlogp_leZ (min_le_right _ _) (le_min zero_le_one (by positivity)) hLZ_nn
        _ = Real.log Z * y * ((1 / (p : ℝ)) ^ a) := by
            rw [Nat.cast_pow, one_div, inv_pow, div_eq_mul_inv]; ring
    have hgeom : ∑ a ∈ Finset.Icc 2 Kmax, (1 / (p : ℝ)) ^ a ≤ 2 / (p : ℝ) ^ 2 := by
      have hle_half : ∀ a : ℕ, 2 ≤ a → (1 / (p : ℝ)) ^ a ≤ (1 / (p : ℝ) ^ 2) * (1 / 2 : ℝ) ^ (a - 2) := by
        intro a ha
        have ha_eq : a = 2 + (a - 2) := by omega
        conv_lhs => rw [ha_eq, pow_add]
        rw [one_div_pow]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact pow_le_pow_left₀ (by positivity) (one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp2)) _
      have hsum_half : ∑ a ∈ Finset.Icc 2 Kmax, (1 / 2 : ℝ) ^ (a - 2) ≤ 2 := by
        have hstep : ∀ m : ℕ, ∑ a ∈ Finset.Icc 2 m, (1 / 2 : ℝ) ^ (a - 2) ≤ 2 := by
          intro m
          induction m with
          | zero => simp
          | succ m ih =>
            by_cases hm : 1 ≤ m
            · have hIcc : Finset.Icc 2 (m + 1) = insert (m + 1) (Finset.Icc 2 m) := by
                ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
              have hexact : ∀ k : ℕ, ∑ a ∈ Finset.Icc 2 (k + 1), (1 / 2 : ℝ) ^ (a - 2) =
                  2 - 2 * (1 / 2 : ℝ) ^ k := by
                intro k
                induction k with
                | zero => simp
                | succ k ihk =>
                  have hI : Finset.Icc 2 (k + 2) = insert (k + 2) (Finset.Icc 2 (k + 1)) := by
                    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
                  rw [hI, Finset.sum_insert (by simp), ihk, show k + 2 - 2 = k by omega, pow_succ]; ring
              rw [hexact m]; linarith [show (0 : ℝ) ≤ 2 * (1 / 2 : ℝ) ^ m by positivity]
            · have hm0 : m = 0 := by omega
              subst hm0; simp
        exact hstep Kmax
      calc ∑ a ∈ Finset.Icc 2 Kmax, (1 / (p : ℝ)) ^ a
          ≤ ∑ a ∈ Finset.Icc 2 Kmax, (1 / (p : ℝ) ^ 2) * (1 / 2 : ℝ) ^ (a - 2) :=
            Finset.sum_le_sum fun a ha => hle_half a (Finset.mem_Icc.mp ha).1
        _ = (1 / (p : ℝ) ^ 2) * ∑ a ∈ Finset.Icc 2 Kmax, (1 / 2 : ℝ) ^ (a - 2) := (Finset.mul_sum _ _ _).symm
        _ ≤ (1 / (p : ℝ) ^ 2) * 2 := mul_le_mul_of_nonneg_left hsum_half (by positivity)
        _ = 2 / (p : ℝ) ^ 2 := by ring
    calc ∑ n ∈ S_p, ZeroDensityWindow.cN y n
        ≤ ∑ a ∈ Finset.Icc 2 Kmax, ZeroDensityWindow.cN y (p ^ a) := hsum_le_img
      _ ≤ ∑ a ∈ Finset.Icc 2 Kmax, Real.log Z * y * ((1 / (p : ℝ)) ^ a) := Finset.sum_le_sum hterm
      _ = (Real.log Z * y) * ∑ a ∈ Finset.Icc 2 Kmax, (1 / (p : ℝ)) ^ a := (Finset.mul_sum _ _ _).symm
      _ ≤ (Real.log Z * y) * (2 / (p : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hgeom (by positivity)
      _ = 2 * Real.log Z * (y / (p : ℝ) ^ 2) := by ring
      _ ≤ 2 * (Real.log Z + 2) * (y / (p : ℝ) ^ 2) := by
          have : 0 ≤ y / (p : ℝ) ^ 2 := by positivity
          nlinarith
  · push Not at hpZ
    have hempty : S_p = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro n hn
      obtain ⟨hn_icc, a, ha2, rfl⟩ := Finset.mem_filter.mp hn
      have hpa_le : ((p ^ a : ℕ) : ℝ) ≤ Z :=
        (by exact_mod_cast (Finset.mem_Icc.mp hn_icc).2 : ((p ^ a : ℕ) : ℝ) ≤ (⌊Z⌋₊ : ℝ)).trans (Nat.floor_le hZ0.le)
      have hp_le_pa : (p : ℝ) ≤ ((p ^ a : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_self_pow (by omega : a ≠ 0) p
      linarith
    rw [hempty, Finset.sum_empty]; positivity

/-- Helper: finite union sum inequality for non-negative functions. -/
private lemma sum_union_le_of_nonneg {α : Type*} [DecidableEq α] {s t : Finset α}
    {f : α → ℝ} (hf : ∀ x ∈ s ∪ t, 0 ≤ f x) :
    ∑ x ∈ s ∪ t, f x ≤ (∑ x ∈ s, f x) + ∑ x ∈ t, f x := by
  have h := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := f)
  have hinter : 0 ≤ ∑ x ∈ s ∩ t, f x :=
    Finset.sum_nonneg fun x hx => hf x (Finset.mem_union_left _ (Finset.mem_inter.mp hx).1)
  linarith

/-- Helper: finite `biUnion` sum inequality for non-negative functions. -/
private lemma sum_biUnion_le_of_nonneg {α β : Type*} [DecidableEq α] {s : Finset β}
    {t : β → Finset α} {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ b ∈ s, ∑ x ∈ t b, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hb]
    exact (sum_union_le_of_nonneg fun x _ => hf x).trans (add_le_add le_rfl ih)

/-- Helper: every prime power `n` satisfies `n.minFac.Prime` and `∃ a ≥ 1, n = n.minFac ^ a`. -/
private lemma isPrimePow_eq_minFac_pow {n : ℕ} (hn : IsPrimePow n) :
    n.minFac.Prime ∧ ∃ a : ℕ, 1 ≤ a ∧ n = n.minFac ^ a := by
  rw [isPrimePow_nat_iff] at hn
  obtain ⟨p, a, hp, ha, rfl⟩ := hn
  have hmf : (p ^ a).minFac = p := by
    have h1 : (p ^ a).minFac ∣ p ^ a := Nat.minFac_dvd (p ^ a)
    have hgt1 : 1 < p ^ a :=
      calc 1 < p := hp.one_lt
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ a := Nat.pow_le_pow_right hp.pos ha
    have hpr : (p ^ a).minFac.Prime := Nat.minFac_prime (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hpr hp).mp (hpr.dvd_of_dvd_pow h1)
  rw [hmf]; exact ⟨hp, a, ha, rfl⟩

/-- Bound the bad prime-power pair sum (same base prime + higher prime powers + small primes + `s_exc`). -/
private lemma sum_bad_primePow_pairs_le
    {m₀ B s_exc : ℕ} (hB2 : 2 ≤ B) {y Z : ℝ} (hy : 1 ≤ y) (hyZ : y ≤ Z) (hB2_le : ((B : ℝ)) ^ 2 ≤ y)
    (hsmall : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ m₀ → (p : ℝ) ≤ Z → p ≤ B) :
    ∑ x ∈ ((Finset.Icc 1 ⌊Z⌋₊) ×ˢ (Finset.Icc 1 ⌊Z⌋₊)).filter
        (fun x => IsPrimePow x.1 ∧ IsPrimePow x.2 ∧
          (soutPart m₀ (x.1 * x.2) = 1 ∨ soutPart m₀ (x.1 * x.2) = s_exc)),
        ZeroDensityWindow.cN y x.1 * ZeroDensityWindow.cN y x.2 ≤
      100 * y * (Real.log Z + 2) ^ 2 := by
  classical
  have hy0 : 0 < y := by linarith
  have hZ0 : 0 < Z := by linarith
  have hLZ_nn : 0 ≤ Real.log Z := Real.log_nonneg (by linarith)
  have hsqrt_ge1 : 1 ≤ Real.sqrt y := Real.one_le_sqrt.mpr hy
  set I := Finset.Icc 1 ⌊Z⌋₊
  set s_cap : ℕ := if s_exc ≠ 0 ∧ s_exc.primeFactors.card ≤ 2 then s_exc else 1
  set E : Finset ℕ := I.filter fun n => IsPrimePow n ∧ (¬ n.Prime ∨ n ≤ B ∨ n ∣ s_cap)
  set Same : Finset (ℕ × ℕ) := (I ×ˢ I).filter fun x => IsPrimePow x.1 ∧ IsPrimePow x.2 ∧ x.1.minFac = x.2.minFac
  -- Every bad prime-power pair lies in `Same ∪ (E ×ˢ E)`!
  have hsub_cover :
      (I ×ˢ I).filter (fun x => IsPrimePow x.1 ∧ IsPrimePow x.2 ∧
        (soutPart m₀ (x.1 * x.2) = 1 ∨ soutPart m₀ (x.1 * x.2) = s_exc)) ⊆ Same ∪ (E ×ˢ E) := by
    intro x hx
    obtain ⟨hx_prod, hpp1, hpp2, hsout_bad⟩ := Finset.mem_filter.mp hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_product.mp hx_prod
    by_cases hsame : x.1.minFac = x.2.minFac
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx_prod, hpp1, hpp2, hsame⟩)
    · refine Finset.mem_union_right _ (Finset.mem_product.mpr ⟨?_, ?_⟩)
      all_goals
        obtain ⟨hp1, a1, ha1, h1_eq⟩ := isPrimePow_eq_minFac_pow hpp1
        obtain ⟨hp2, a2, ha2, h2_eq⟩ := isPrimePow_eq_minFac_pow hpp2
        have hmem_E : ∀ (u v : ℕ) (huI : u ∈ I) (hppu : IsPrimePow u) (p q : ℕ)
            (hp : p.Prime) (hq : q.Prime) (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
            (hu_eq : u = p ^ a) (hv_eq : v = q ^ b) (hpq : p ≠ q)
            (hbad : soutPart m₀ (u * v) = 1 ∨ soutPart m₀ (u * v) = s_exc),
            u ∈ E := by
          intro u v huI hppu p q hp hq a b ha hb hu_eq hv_eq hpq hbad
          refine Finset.mem_filter.mpr ⟨huI, hppu, ?_⟩
          by_cases hu_pr : u.Prime
          · right
            have ha_eq1 : a = 1 := by
              by_contra hne
              have ha2 : 2 ≤ a := by omega
              have hpd : p ∣ u := hu_eq ▸ dvd_pow_self p (by omega)
              rcases hu_pr.eq_one_or_self_of_dvd p hpd with hp1 | hpu
              · exact absurd hp1 hp.ne_one
              · have hlt : p < p ^ a := by
                  calc p = p ^ 1 := (pow_one p).symm
                    _ < p ^ a := Nat.pow_lt_pow_right hp.one_lt (by omega)
                omega
            have hup : u = p := by rw [hu_eq, ha_eq1, pow_one]
            by_cases hpB : p ≤ B
            · left; rwa [hup]
            · right
              have hp_gtB : B < p := Nat.lt_of_not_ge hpB
              have hp2 : p ≠ 2 := by omega
              have hp_leZ : (p : ℝ) ≤ Z := by
                have h1 : (u : ℝ) ≤ (⌊Z⌋₊ : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp huI).2
                rw [hup] at h1; exact h1.trans (Nat.floor_le hZ0.le)
              have hp_not_m0 : ¬ p ∣ m₀ := fun hdm => hpB (hsmall p hp hp2 hdm hp_leZ)
              have hv_ne0 : v ≠ 0 := by rw [hv_eq]; exact pow_ne_zero b hq.ne_zero
              have hu_ne0 : u ≠ 0 := by rw [hup]; exact hp.ne_zero
              have hfac_p : (u * v).factorization p = 1 := by
                have hq_fac0 : q.factorization p = 0 :=
                  Nat.factorization_eq_zero_of_not_dvd fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)
                rw [Nat.factorization_mul hu_ne0 hv_ne0, Finsupp.add_apply, hup, hp.factorization_self,
                  hv_eq, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
                  hq_fac0, mul_zero, add_zero]
              have hp_mem_sout : p ∈ (u * v).primeFactors.filter (fun l => l ≠ 2 ∧ ¬ l ∣ m₀ ∧ Odd ((u * v).factorization l)) := by
                refine Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hup ▸ dvd_mul_right u v, mul_ne_zero hu_ne0 hv_ne0⟩,
                  hp2, hp_not_m0, by rw [hfac_p]; exact odd_one⟩
              have hp_dvd_sout : p ∣ soutPart m₀ (u * v) := Finset.dvd_prod_of_mem _ hp_mem_sout
              rcases hbad with h1 | hse
              · rw [h1] at hp_dvd_sout
                have := Nat.le_of_dvd one_pos hp_dvd_sout; have := hp.two_le; omega
              · have hcard2 : s_exc.primeFactors.card ≤ 2 := by
                  have hpf_sub : s_exc.primeFactors ⊆ {p, q} := by
                    intro l hl
                    have hl_pr : l.Prime := Nat.prime_of_mem_primeFactors hl
                    have hl_dvd : l ∣ u * v := by
                      have h1 : l ∣ soutPart m₀ (u * v) := hse.symm ▸ Nat.dvd_of_mem_primeFactors hl
                      have h2 : soutPart m₀ (u * v) ∣ u * v :=
                        (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)).trans
                          (Nat.prod_primeFactors_dvd _)
                      exact h1.trans h2
                    rcases hl_pr.dvd_mul.mp hl_dvd with hl_u | hl_v
                    · rw [hup] at hl_u
                      have := (Nat.prime_dvd_prime_iff_eq hl_pr hp).mp hl_u
                      simp [this]
                    · rw [hv_eq] at hl_v
                      have := (Nat.prime_dvd_prime_iff_eq hl_pr hq).mp (hl_pr.dvd_of_dvd_pow hl_v)
                      simp [this]
                  exact (Finset.card_le_card hpf_sub).trans Finset.card_le_two
                have hse_ne0 : s_exc ≠ 0 := by
                  have hodd := (soutPart_props m₀ (u * v)).1
                  rw [hse] at hodd; obtain ⟨t, ht⟩ := hodd; omega
                have hcap : s_cap = s_exc := if_pos ⟨hse_ne0, hcard2⟩
                rw [hup, hcap, ← hse]; exact hp_dvd_sout
          · left; exact hu_pr
      · exact hmem_E x.1 x.2 hx1 hpp1 x.1.minFac x.2.minFac hp1 hp2 a1 a2 ha1 ha2 h1_eq h2_eq hsame hsout_bad
      · exact hmem_E x.2 x.1 hx2 hpp2 x.2.minFac x.1.minFac hp2 hp1 a2 a1 ha2 ha1 h2_eq h1_eq (Ne.symm hsame)
          (by rwa [mul_comm])
  have hcN_nn : ∀ n : ℕ, 0 ≤ ZeroDensityWindow.cN y n := fun n =>
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (le_min zero_le_one (by positivity))
  -- Bound 1: `∑ x ∈ Same, cN y x.1 * cN y x.2 ≤ 12 * y * (Real.log Z + 2) ^ 2`
  have hSame_le : ∑ x ∈ Same, ZeroDensityWindow.cN y x.1 * ZeroDensityWindow.cN y x.2 ≤
      12 * y * (Real.log Z + 2) ^ 2 := by
    let S_p : ℕ → Finset ℕ := fun p => I.filter fun n => ∃ a : ℕ, 1 ≤ a ∧ n = p ^ a
    let Pr : Finset ℕ := I.filter Nat.Prime
    have hSame_sub : Same ⊆ Pr.biUnion (fun p => S_p p ×ˢ S_p p) := by
      intro x hx
      obtain ⟨hx_prod, hpp1, hpp2, hmf_eq⟩ := Finset.mem_filter.mp hx
      obtain ⟨hx1, hx2⟩ := Finset.mem_product.mp hx_prod
      obtain ⟨hp1, a1, ha1, h1_eq⟩ := isPrimePow_eq_minFac_pow hpp1
      obtain ⟨_, a2, ha2, h2_eq⟩ := isPrimePow_eq_minFac_pow hpp2
      refine Finset.mem_biUnion.mpr ⟨x.1.minFac, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp1.pos, ?_⟩, hp1⟩
        exact (Nat.le_of_dvd (Finset.mem_Icc.mp hx1).1 (Nat.minFac_dvd x.1)).trans (Finset.mem_Icc.mp hx1).2
      · exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hx1, a1, ha1, h1_eq⟩,
          Finset.mem_filter.mpr ⟨hx2, a2, ha2, hmf_eq ▸ h2_eq⟩⟩
    have hsum_sq : ∑ x ∈ Same, ZeroDensityWindow.cN y x.1 * ZeroDensityWindow.cN y x.2 ≤
        ∑ p ∈ Pr, (∑ n ∈ S_p p, ZeroDensityWindow.cN y n) ^ 2 := by
      calc ∑ x ∈ Same, ZeroDensityWindow.cN y x.1 * ZeroDensityWindow.cN y x.2
          ≤ ∑ x ∈ Pr.biUnion (fun p => S_p p ×ˢ S_p p),
              ZeroDensityWindow.cN y x.1 * ZeroDensityWindow.cN y x.2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hSame_sub fun _ _ _ => mul_nonneg (hcN_nn _) (hcN_nn _)
        _ ≤ ∑ p ∈ Pr, ∑ x ∈ S_p p ×ˢ S_p p, ZeroDensityWindow.cN y x.1 * ZeroDensityWindow.cN y x.2 :=
            sum_biUnion_le_of_nonneg fun x => mul_nonneg (hcN_nn x.1) (hcN_nn x.2)
        _ = ∑ p ∈ Pr, (∑ n ∈ S_p p, ZeroDensityWindow.cN y n) ^ 2 :=
            Finset.sum_congr rfl fun p _ => by
              rw [Finset.sum_product, sq, Finset.sum_mul]
              exact Finset.sum_congr rfl fun _ _ => by dsimp only; exact (Finset.mul_sum _ _ _).symm
    have hPr_split : Pr = Pr.filter (fun p => p ≤ ⌊y⌋₊) ∪ Pr.filter (fun p => ⌊y⌋₊ < p) := by
      ext p; simp only [Finset.mem_union, Finset.mem_filter]
      exact ⟨fun h => (le_or_gt p ⌊y⌋₊).imp (fun hle => ⟨h, hle⟩) (fun hgt => ⟨h, hgt⟩),
        fun h => h.elim And.left And.left⟩
    have hPr_disj : Disjoint (Pr.filter (fun p => p ≤ ⌊y⌋₊)) (Pr.filter (fun p => ⌊y⌋₊ < p)) :=
      Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega
    have hlo : ∑ p ∈ Pr.filter (fun p => p ≤ ⌊y⌋₊), (∑ n ∈ S_p p, ZeroDensityWindow.cN y n) ^ 2 ≤
        4 * y * (Real.log Z + 2) ^ 2 := by
      have hterm : ∀ p ∈ Pr.filter (fun p => p ≤ ⌊y⌋₊),
          (∑ n ∈ S_p p, ZeroDensityWindow.cN y n) ^ 2 ≤ 4 * (Real.log Z + 2) ^ 2 := by
        intro p hp
        have hpr : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
        have h1 := (sum_cN_prime_powers_le hy hyZ hpr).1
        calc (∑ n ∈ S_p p, ZeroDensityWindow.cN y n) ^ 2
            ≤ (2 * (Real.log Z + 2)) ^ 2 :=
              pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => hcN_nn _) h1 2
          _ = 4 * (Real.log Z + 2) ^ 2 := by ring
      have hcard_le : ((Pr.filter (fun p => p ≤ ⌊y⌋₊)).card : ℝ) ≤ y := by
        have hsub : Pr.filter (fun p => p ≤ ⌊y⌋₊) ⊆ Finset.Icc 1 ⌊y⌋₊ := fun p hp =>
          Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1,
            (Finset.mem_filter.mp hp).2⟩
        have h1 : (Pr.filter (fun p => p ≤ ⌊y⌋₊)).card ≤ ⌊y⌋₊ := by
          simpa [Nat.card_Icc] using Finset.card_le_card hsub
        exact (by exact_mod_cast h1 : ((Pr.filter (fun p => p ≤ ⌊y⌋₊)).card : ℝ) ≤ (⌊y⌋₊ : ℝ)).trans
          (Nat.floor_le hy0.le)
      calc ∑ p ∈ Pr.filter (fun p => p ≤ ⌊y⌋₊), (∑ n ∈ S_p p, ZeroDensityWindow.cN y n) ^ 2
          ≤ ∑ _p ∈ Pr.filter (fun p => p ≤ ⌊y⌋₊), 4 * (Real.log Z + 2) ^ 2 := Finset.sum_le_sum hterm
        _ = ((Pr.filter (fun p => p ≤ ⌊y⌋₊)).card : ℝ) * (4 * (Real.log Z + 2) ^ 2) := by simp
        _ ≤ y * (4 * (Real.log Z + 2) ^ 2) := mul_le_mul_of_nonneg_right hcard_le (by positivity)
        _ = 4 * y * (Real.log Z + 2) ^ 2 := by ring
    have hhi : ∑ p ∈ Pr.filter (fun p => ⌊y⌋₊ < p), (∑ n ∈ S_p p, ZeroDensityWindow.cN y n) ^ 2 ≤
        8 * y * (Real.log Z + 2) ^ 2 := by
      have hterm : ∀ p ∈ Pr.filter (fun p => ⌊y⌋₊ < p),
          (∑ n ∈ S_p p, ZeroDensityWindow.cN y n) ^ 2 ≤
            4 * (Real.log Z + 2) ^ 2 * y ^ 2 * (1 / (p : ℝ) ^ 2) := by
        intro p hp
        have hpr : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
        have hgt : ⌊y⌋₊ < p := (Finset.mem_filter.mp hp).2
        have hyp : y < (p : ℝ) := lt_of_lt_of_le (Nat.lt_floor_add_one y) (by exact_mod_cast hgt)
        have h1 := (sum_cN_prime_powers_le hy hyZ hpr).2 hyp
        calc (∑ n ∈ S_p p, ZeroDensityWindow.cN y n) ^ 2
            ≤ (2 * (Real.log Z + 2) * (y / (p : ℝ))) ^ 2 :=
              pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => hcN_nn _) h1 2
          _ = 4 * (Real.log Z + 2) ^ 2 * y ^ 2 * (1 / (p : ℝ) ^ 2) := by ring
      have hsub : Pr.filter (fun p => ⌊y⌋₊ < p) ⊆ Finset.Ioc ⌊y⌋₊ ⌊Z⌋₊ := fun p hp =>
        Finset.mem_Ioc.mpr ⟨(Finset.mem_filter.mp hp).2,
          (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).2⟩
      have hfl_ge1 : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by norm_cast : ((1 : ℕ) : ℝ) ≤ y)
      have hinv_fl : 1 / (⌊y⌋₊ : ℝ) ≤ 2 / y := by
        have hfl_pos : (0 : ℝ) < (⌊y⌋₊ : ℝ) := by exact_mod_cast (by omega : 0 < ⌊y⌋₊)
        have hfl_half : y / 2 ≤ (⌊y⌋₊ : ℝ) := by
          rcases le_or_gt 2 y with h2 | hlt2
          · linarith [Nat.lt_floor_add_one y]
          · have h1 : (1 : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hfl_ge1
            linarith
        rw [div_le_div_iff₀ hfl_pos hy0]; linarith
      calc ∑ p ∈ Pr.filter (fun p => ⌊y⌋₊ < p), (∑ n ∈ S_p p, ZeroDensityWindow.cN y n) ^ 2
          ≤ ∑ p ∈ Pr.filter (fun p => ⌊y⌋₊ < p), 4 * (Real.log Z + 2) ^ 2 * y ^ 2 * (1 / (p : ℝ) ^ 2) :=
            Finset.sum_le_sum hterm
        _ ≤ ∑ p ∈ Finset.Ioc ⌊y⌋₊ ⌊Z⌋₊, 4 * (Real.log Z + 2) ^ 2 * y ^ 2 * (1 / (p : ℝ) ^ 2) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
        _ = (4 * (Real.log Z + 2) ^ 2 * y ^ 2) * ∑ p ∈ Finset.Ioc ⌊y⌋₊ ⌊Z⌋₊, (1 : ℝ) / (p : ℝ) ^ 2 :=
            (Finset.mul_sum _ _ _).symm
        _ ≤ (4 * (Real.log Z + 2) ^ 2 * y ^ 2) * (1 / (⌊y⌋₊ : ℝ)) :=
            mul_le_mul_of_nonneg_left (sum_inv_sq_Ioc_le hfl_ge1) (by positivity)
        _ ≤ (4 * (Real.log Z + 2) ^ 2 * y ^ 2) * (2 / y) := mul_le_mul_of_nonneg_left hinv_fl (by positivity)
        _ = 8 * y * (Real.log Z + 2) ^ 2 := by field_simp [hy0.ne']; ring
    calc ∑ x ∈ Same, ZeroDensityWindow.cN y x.1 * ZeroDensityWindow.cN y x.2
        ≤ ∑ p ∈ Pr, (∑ n ∈ S_p p, ZeroDensityWindow.cN y n) ^ 2 := hsum_sq
      _ = (∑ p ∈ Pr.filter (fun p => p ≤ ⌊y⌋₊), _) + (∑ p ∈ Pr.filter (fun p => ⌊y⌋₊ < p), _) := by
          conv_lhs => rw [hPr_split]
          exact Finset.sum_union hPr_disj
      _ ≤ 12 * y * (Real.log Z + 2) ^ 2 := by linarith
  -- Bound 2: `∑ n ∈ E, cN y n ≤ 9 * Real.sqrt y * (Real.log Z + 2)` (hence squared `≤ 81 * y * (Real.log Z + 2)^2`)
  have hE_le : ∑ n ∈ E, ZeroDensityWindow.cN y n ≤ 9 * Real.sqrt y * (Real.log Z + 2) := by
    set E_pp := I.filter fun n => IsPrimePow n ∧ ¬ n.Prime
    set E_sm := I.filter fun n => n.Prime ∧ n ≤ B
    set E_ex := I.filter fun n => n.Prime ∧ n ∣ s_cap
    have hE_sub : E ⊆ E_pp ∪ (E_sm ∪ E_ex) := by
      intro n hn
      obtain ⟨hnI, hpp, h1 | h2 | h3⟩ := Finset.mem_filter.mp hn
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnI, hpp, h1⟩)
      · by_cases hpr : n.Prime
        · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnI, hpr, h2⟩))
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnI, hpp, hpr⟩)
      · by_cases hpr : n.Prime
        · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnI, hpr, h3⟩))
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnI, hpp, hpr⟩)
    -- (2a) `E_pp` bound: `≤ 6 * Real.sqrt y * (Real.log Z + 2)`
    have hEpp_le : ∑ n ∈ E_pp, ZeroDensityWindow.cN y n ≤ 6 * Real.sqrt y * (Real.log Z + 2) := by
      let H_p : ℕ → Finset ℕ := fun p => I.filter fun n => ∃ a : ℕ, 2 ≤ a ∧ n = p ^ a
      let Pr : Finset ℕ := I.filter Nat.Prime
      have hsub : E_pp ⊆ Pr.biUnion H_p := by
        intro n hn
        obtain ⟨hnI, hpp, hnotpr⟩ := Finset.mem_filter.mp hn
        obtain ⟨hp, a, ha1, hneq⟩ := isPrimePow_eq_minFac_pow hpp
        have ha2 : 2 ≤ a := by
          by_contra hlt; have ha_eq : a = 1 := by omega
          rw [ha_eq, pow_one] at hneq; exact hnotpr (hneq ▸ hp)
        refine Finset.mem_biUnion.mpr ⟨n.minFac, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.pos,
          (Nat.le_of_dvd (Finset.mem_Icc.mp hnI).1 (Nat.minFac_dvd n)).trans (Finset.mem_Icc.mp hnI).2⟩, hp⟩,
          Finset.mem_filter.mpr ⟨hnI, a, ha2, hneq⟩⟩
      set s_fl : ℕ := ⌊Real.sqrt y⌋₊
      have hsfl_ge1 : 1 ≤ s_fl := Nat.le_floor (by norm_cast : ((1 : ℕ) : ℝ) ≤ Real.sqrt y)
      have hPr_split : Pr = Pr.filter (fun p => p ≤ s_fl) ∪ Pr.filter (fun p => s_fl < p) := by
        ext p; simp only [Finset.mem_union, Finset.mem_filter]
        exact ⟨fun h => (le_or_gt p s_fl).imp (fun hle => ⟨h, hle⟩) (fun hgt => ⟨h, hgt⟩),
          fun h => h.elim And.left And.left⟩
      have hPr_disj : Disjoint (Pr.filter (fun p => p ≤ s_fl)) (Pr.filter (fun p => s_fl < p)) :=
        Finset.disjoint_filter.mpr fun _ _ h1 h2 => by omega
      have hlo : ∑ p ∈ Pr.filter (fun p => p ≤ s_fl), ∑ n ∈ H_p p, ZeroDensityWindow.cN y n ≤
          2 * Real.sqrt y * (Real.log Z + 2) := by
        have hterm : ∀ p ∈ Pr.filter (fun p => p ≤ s_fl),
            ∑ n ∈ H_p p, ZeroDensityWindow.cN y n ≤ 2 * (Real.log Z + 2) := by
          intro p hp
          have hpr : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
          have hsub_p : H_p p ⊆ I.filter fun n => ∃ a : ℕ, 1 ≤ a ∧ n = p ^ a := fun n hn => by
            obtain ⟨hnI, a, ha2, hEq⟩ := Finset.mem_filter.mp hn
            exact Finset.mem_filter.mpr ⟨hnI, a, by omega, hEq⟩
          exact (Finset.sum_le_sum_of_subset_of_nonneg hsub_p fun _ _ _ => hcN_nn _).trans
            (sum_cN_prime_powers_le hy hyZ hpr).1
        have hcard_le : ((Pr.filter (fun p => p ≤ s_fl)).card : ℝ) ≤ Real.sqrt y := by
          have hsub_c : Pr.filter (fun p => p ≤ s_fl) ⊆ Finset.Icc 1 s_fl := fun p hp =>
            Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).1,
              (Finset.mem_filter.mp hp).2⟩
          have h1 : (Pr.filter (fun p => p ≤ s_fl)).card ≤ s_fl := by
            simpa [Nat.card_Icc] using Finset.card_le_card hsub_c
          exact (by exact_mod_cast h1 : ((Pr.filter (fun p => p ≤ s_fl)).card : ℝ) ≤ (s_fl : ℝ)).trans
            (Nat.floor_le (Real.sqrt_nonneg y))
        calc ∑ p ∈ Pr.filter (fun p => p ≤ s_fl), ∑ n ∈ H_p p, ZeroDensityWindow.cN y n
            ≤ ∑ _p ∈ Pr.filter (fun p => p ≤ s_fl), 2 * (Real.log Z + 2) := Finset.sum_le_sum hterm
          _ = ((Pr.filter (fun p => p ≤ s_fl)).card : ℝ) * (2 * (Real.log Z + 2)) := by simp
          _ ≤ Real.sqrt y * (2 * (Real.log Z + 2)) := mul_le_mul_of_nonneg_right hcard_le (by positivity)
          _ = 2 * Real.sqrt y * (Real.log Z + 2) := by ring
      have hhi : ∑ p ∈ Pr.filter (fun p => s_fl < p), ∑ n ∈ H_p p, ZeroDensityWindow.cN y n ≤
          4 * Real.sqrt y * (Real.log Z + 2) := by
        have hsub_c : Pr.filter (fun p => s_fl < p) ⊆ Finset.Ioc s_fl ⌊Z⌋₊ := fun p hp =>
          Finset.mem_Ioc.mpr ⟨(Finset.mem_filter.mp hp).2,
            (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1).2⟩
        have hinv_s : 1 / (s_fl : ℝ) ≤ 2 / Real.sqrt y := by
          have hsfl_pos : (0 : ℝ) < (s_fl : ℝ) := by exact_mod_cast (by omega : 0 < s_fl)
          have hhalf : Real.sqrt y / 2 ≤ (s_fl : ℝ) := by
            rcases le_or_gt 2 (Real.sqrt y) with h2 | hlt2
            · linarith [Nat.lt_floor_add_one (Real.sqrt y)]
            · have h1 : (1 : ℝ) ≤ (s_fl : ℝ) := by exact_mod_cast hsfl_ge1
              linarith
          rw [div_le_div_iff₀ hsfl_pos (Real.sqrt_pos.mpr hy0)]; linarith
        calc ∑ p ∈ Pr.filter (fun p => s_fl < p), ∑ n ∈ H_p p, ZeroDensityWindow.cN y n
            ≤ ∑ p ∈ Pr.filter (fun p => s_fl < p), (2 * (Real.log Z + 2) * y) * (1 / (p : ℝ) ^ 2) :=
              Finset.sum_le_sum fun p hp => by
                have hpr : p.Prime := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
                simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using sum_cN_higher_powers_le hy hyZ hpr
          _ ≤ ∑ p ∈ Finset.Ioc s_fl ⌊Z⌋₊, (2 * (Real.log Z + 2) * y) * (1 / (p : ℝ) ^ 2) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub_c fun _ _ _ => by positivity
          _ = (2 * (Real.log Z + 2) * y) * ∑ p ∈ Finset.Ioc s_fl ⌊Z⌋₊, (1 : ℝ) / (p : ℝ) ^ 2 :=
              (Finset.mul_sum _ _ _).symm
          _ ≤ (2 * (Real.log Z + 2) * y) * (1 / (s_fl : ℝ)) :=
              mul_le_mul_of_nonneg_left (sum_inv_sq_Ioc_le hsfl_ge1) (by positivity)
          _ ≤ (2 * (Real.log Z + 2) * y) * (2 / Real.sqrt y) := mul_le_mul_of_nonneg_left hinv_s (by positivity)
          _ = 4 * Real.sqrt y * (Real.log Z + 2) := by
              have hdiv : y / Real.sqrt y = Real.sqrt y := by
                rw [div_eq_iff (Real.sqrt_pos.mpr hy0).ne', Real.mul_self_sqrt hy0.le]
              calc (2 * (Real.log Z + 2) * y) * (2 / Real.sqrt y)
                  = 4 * (y / Real.sqrt y) * (Real.log Z + 2) := by ring
                _ = 4 * Real.sqrt y * (Real.log Z + 2) := by rw [hdiv]
      calc ∑ n ∈ E_pp, ZeroDensityWindow.cN y n
          ≤ ∑ n ∈ Pr.biUnion H_p, ZeroDensityWindow.cN y n :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => hcN_nn _
        _ ≤ ∑ p ∈ Pr, ∑ n ∈ H_p p, ZeroDensityWindow.cN y n :=
            sum_biUnion_le_of_nonneg fun x => hcN_nn x
        _ = (∑ p ∈ Pr.filter (fun p => p ≤ s_fl), _) + (∑ p ∈ Pr.filter (fun p => s_fl < p), _) := by
            conv_lhs => rw [hPr_split]; exact Finset.sum_union hPr_disj
        _ ≤ 6 * Real.sqrt y * (Real.log Z + 2) := by linarith
    -- (2b) `E_sm` bound: `≤ Real.sqrt y * (Real.log Z + 2)`
    have hEsm_le : ∑ n ∈ E_sm, ZeroDensityWindow.cN y n ≤ Real.sqrt y * (Real.log Z + 2) := by
      have hB_le_sqrt : (B : ℝ) ≤ Real.sqrt y := Real.le_sqrt_of_sq_le hB2_le
      have hterm : ∀ n ∈ E_sm, ZeroDensityWindow.cN y n ≤ Real.log Z + 2 := fun n hn => by
        have hnI := (Finset.mem_filter.mp hn).1
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by have := (Finset.mem_Icc.mp hnI).1; omega : 0 < n)
        have hn_leZ : (n : ℝ) ≤ Z := (by exact_mod_cast (Finset.mem_Icc.mp hnI).2 : (n : ℝ) ≤ (⌊Z⌋₊ : ℝ)).trans (Nat.floor_le hZ0.le)
        unfold ZeroDensityWindow.cN
        calc Λ n * min 1 (y / (n : ℝ)) ≤ Λ n * 1 := mul_le_mul_of_nonneg_left (min_le_left _ _) ArithmeticFunction.vonMangoldt_nonneg
          _ ≤ Real.log Z := by rw [mul_one]; exact ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hn_pos hn_leZ)
          _ ≤ Real.log Z + 2 := by linarith
      have hcard : (E_sm.card : ℝ) ≤ (B : ℝ) := by
        have hsub : E_sm ⊆ Finset.Icc 1 B := fun n hn =>
          Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1, (Finset.mem_filter.mp hn).2.2⟩
        have h1 : E_sm.card ≤ B := by simpa [Nat.card_Icc] using Finset.card_le_card hsub
        exact_mod_cast h1
      calc ∑ n ∈ E_sm, ZeroDensityWindow.cN y n
          ≤ ∑ _n ∈ E_sm, (Real.log Z + 2) := Finset.sum_le_sum hterm
        _ = (E_sm.card : ℝ) * (Real.log Z + 2) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ Real.sqrt y * (Real.log Z + 2) := mul_le_mul_of_nonneg_right (hcard.trans hB_le_sqrt) (by positivity)
    -- (2c) `E_ex` bound: `≤ 2 * Real.sqrt y * (Real.log Z + 2)`
    have hEex_le : ∑ n ∈ E_ex, ZeroDensityWindow.cN y n ≤ 2 * Real.sqrt y * (Real.log Z + 2) := by
      have hterm : ∀ n ∈ E_ex, ZeroDensityWindow.cN y n ≤ Real.log Z + 2 := fun n hn => by
        have hnI := (Finset.mem_filter.mp hn).1
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by have := (Finset.mem_Icc.mp hnI).1; omega : 0 < n)
        have hn_leZ : (n : ℝ) ≤ Z := (by exact_mod_cast (Finset.mem_Icc.mp hnI).2 : (n : ℝ) ≤ (⌊Z⌋₊ : ℝ)).trans (Nat.floor_le hZ0.le)
        unfold ZeroDensityWindow.cN
        calc Λ n * min 1 (y / (n : ℝ)) ≤ Λ n * 1 := mul_le_mul_of_nonneg_left (min_le_left _ _) ArithmeticFunction.vonMangoldt_nonneg
          _ ≤ Real.log Z := by rw [mul_one]; exact ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hn_pos hn_leZ)
          _ ≤ Real.log Z + 2 := by linarith
      have hcard : E_ex.card ≤ 2 := by
        have hcap_ne0 : s_cap ≠ 0 := by
          dsimp only [s_cap]; split_ifs with h
          · exact h.1
          · norm_num
        have hsub : E_ex ⊆ s_cap.primeFactors := fun n hn =>
          Nat.mem_primeFactors.mpr ⟨(Finset.mem_filter.mp hn).2.1, (Finset.mem_filter.mp hn).2.2, hcap_ne0⟩
        have hle2 : s_cap.primeFactors.card ≤ 2 := by
          dsimp only [s_cap]; split_ifs with h
          · exact h.2
          · simp
        exact (Finset.card_le_card hsub).trans hle2
      calc ∑ n ∈ E_ex, ZeroDensityWindow.cN y n
          ≤ ∑ _n ∈ E_ex, (Real.log Z + 2) := Finset.sum_le_sum hterm
        _ = (E_ex.card : ℝ) * (Real.log Z + 2) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 2 * (Real.log Z + 2) := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
        _ ≤ 2 * Real.sqrt y * (Real.log Z + 2) := by
            have : 0 ≤ Real.log Z + 2 := by positivity
            nlinarith
    calc ∑ n ∈ E, ZeroDensityWindow.cN y n
        ≤ ∑ n ∈ E_pp ∪ (E_sm ∪ E_ex), ZeroDensityWindow.cN y n :=
          Finset.sum_le_sum_of_subset_of_nonneg hE_sub fun _ _ _ => hcN_nn _
      _ ≤ (∑ n ∈ E_pp, ZeroDensityWindow.cN y n) + ∑ n ∈ E_sm ∪ E_ex, ZeroDensityWindow.cN y n :=
          sum_union_le_of_nonneg fun x _ => hcN_nn x
      _ ≤ (∑ n ∈ E_pp, ZeroDensityWindow.cN y n) +
          ((∑ n ∈ E_sm, ZeroDensityWindow.cN y n) + ∑ n ∈ E_ex, ZeroDensityWindow.cN y n) :=
          add_le_add le_rfl (sum_union_le_of_nonneg fun x _ => hcN_nn x)
      _ ≤ 9 * Real.sqrt y * (Real.log Z + 2) := by linarith
  -- Combine `Same` (`≤ 12 y (log Z + 2)^2`) and `E ×ˢ E` (`≤ 81 y (log Z + 2)^2`) → `≤ 100 y (log Z + 2)^2`!
  have hEE_le : ∑ x ∈ E ×ˢ E, ZeroDensityWindow.cN y x.1 * ZeroDensityWindow.cN y x.2 ≤
      81 * y * (Real.log Z + 2) ^ 2 := by
    have hprod_eq : ∑ x ∈ E ×ˢ E, ZeroDensityWindow.cN y x.1 * ZeroDensityWindow.cN y x.2 =
        (∑ n ∈ E, ZeroDensityWindow.cN y n) ^ 2 := by
      rw [Finset.sum_product, sq, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by dsimp only; exact (Finset.mul_sum _ _ _).symm
    rw [hprod_eq]
    calc (∑ n ∈ E, ZeroDensityWindow.cN y n) ^ 2
        ≤ (9 * Real.sqrt y * (Real.log Z + 2)) ^ 2 :=
          pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => hcN_nn _) hE_le 2
      _ = 81 * (Real.sqrt y) ^ 2 * (Real.log Z + 2) ^ 2 := by ring
      _ = 81 * y * (Real.log Z + 2) ^ 2 := by rw [Real.sq_sqrt hy0.le]
  calc ∑ x ∈ (I ×ˢ I).filter _, ZeroDensityWindow.cN y x.1 * ZeroDensityWindow.cN y x.2
      ≤ ∑ x ∈ Same ∪ (E ×ˢ E), ZeroDensityWindow.cN y x.1 * ZeroDensityWindow.cN y x.2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub_cover fun _ _ _ => mul_nonneg (hcN_nn _) (hcN_nn _)
    _ ≤ (∑ x ∈ Same, ZeroDensityWindow.cN y x.1 * ZeroDensityWindow.cN y x.2) +
        (∑ x ∈ E ×ˢ E, ZeroDensityWindow.cN y x.1 * ZeroDensityWindow.cN y x.2) :=
        sum_union_le_of_nonneg fun x _ => mul_nonneg (hcN_nn x.1) (hcN_nn x.2)
    _ ≤ 100 * y * (Real.log Z + 2) ^ 2 := by
        have : 0 ≤ y * (Real.log Z + 2) ^ 2 := by positivity
        linarith

/-- **Unified Prime-Power Diagonal + Small-Prime + Exceptional-`s*` Mean-Square Bound
(`weighted_reciprocity_meansq_of_twist_bound`)**:
Given a prime set `P` with non-negative weights `w r ≥ 0` (`W_tot := ∑ r ∈ P, w r`) where every
`r ∈ P` is prime with `r ≡ a₀ [MOD m₀]` (`8 ∣ m₀, a₀ % 4 = 3`) and `Z < r`, suppose:
- Every odd prime `p ∣ m₀` with `p ≤ Z` satisfies `p ≤ B` (with `2 ≤ B` and `(B : ℝ)^2 ≤ y`), and
- At most one odd squarefree `s_exc > 1` coprime to `m₀` fails `|∑_{r ∈ P} w r * (r | s)| ≤ (1 / Z^2) * W_tot`.
Then for EVERY sequence `κ : ℕ → ℂ` supported on prime powers with `‖κ n‖ ≤ ZeroDensityWindow.cN y n`:
`∑_{r ∈ P} w r * ‖∑_{n ∈ Icc 1 ⌊Z⌋₊} κ n * (n | r)‖^2 ≤ 150 * W_tot * y * (Real.log Z + 2)^2`! -/
theorem weighted_reciprocity_meansq_of_twist_bound
    {m₀ a₀ B : ℕ} (h8 : 8 ∣ m₀) (ha4 : a₀ % 4 = 3) (hB2 : 2 ≤ B)
    {y Z : ℝ} (hy : 1 ≤ y) (hyZ : y ≤ Z) (hB2_le : ((B : ℝ)) ^ 2 ≤ y)
    (hsmall : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ m₀ → (p : ℝ) ≤ Z → p ≤ B)
    (P : Finset ℕ) (w : ℕ → ℝ) (hw_nn : ∀ r ∈ P, 0 ≤ w r)
    (hP : ∀ r ∈ P, r.Prime ∧ r ≡ a₀ [MOD m₀] ∧ Z < (r : ℝ))
    (s_exc : ℕ)
    (htwist : ∀ s : ℕ, 1 < s → Odd s → Squarefree s → Nat.Coprime s m₀ → (s : ℝ) ≤ Z ^ 2 → s ≠ s_exc →
      |∑ r ∈ P, w r * (jacobiSym (r : ℤ) s : ℝ)| ≤ (1 / Z ^ 2) * (∑ r ∈ P, w r))
    (κ : ℕ → ℂ) (hκ_pp : ∀ n : ℕ, κ n ≠ 0 → IsPrimePow n)
    (hκ_le : ∀ n ∈ Finset.Icc 1 ⌊Z⌋₊, ‖κ n‖ ≤ ZeroDensityWindow.cN y n) :
    ∑ r ∈ P, w r * ‖∑ n ∈ Finset.Icc 1 ⌊Z⌋₊, κ n * ((jacobiSym (n : ℤ) r : ℤ) : ℂ)‖ ^ 2 ≤
      150 * (∑ r ∈ P, w r) * y * (Real.log Z + 2) ^ 2 := by
  classical
  set W : ℝ := ∑ r ∈ P, w r
  have hW_nn : 0 ≤ W := Finset.sum_nonneg hw_nn
  have hy0 : 0 < y := by linarith
  have hZ0 : 0 < Z := by linarith
  have hLZ_nn : 0 ≤ Real.log Z := Real.log_nonneg (by linarith)
  set I := Finset.Icc 1 ⌊Z⌋₊
  -- Step 1: Expand `‖∑ κ n * (n | r)‖²` and swap sums into pairs `(n, n') ∈ I ×ˢ I`
  have hexpand :
      ∑ r ∈ P, w r * ‖∑ n ∈ I, κ n * ((jacobiSym (n : ℤ) r : ℤ) : ℂ)‖ ^ 2 ≤
        ∑ x ∈ I ×ˢ I, ‖κ x.1‖ * ‖κ x.2‖ *
          |∑ r ∈ P, w r * (jacobiSym (r : ℤ) (soutPart m₀ (x.1 * x.2)) : ℝ)| := by
    have hsq_eq : ∀ r ∈ P,
        ((w r * ‖∑ n ∈ I, κ n * ((jacobiSym (n : ℤ) r : ℤ) : ℂ)‖ ^ 2 : ℝ) : ℂ) =
          ∑ x ∈ I ×ˢ I, (w r : ℂ) * (κ x.1 * starRingEnd ℂ (κ x.2)) *
            ((jacobiSym ((x.1 * x.2 : ℕ) : ℤ) r : ℤ) : ℂ) := by
      intro r _
      rw [Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj', Finset.sum_mul, Finset.mul_sum, Finset.sum_product]
      simp only [map_sum, map_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
      have hconj_int : ∀ z : ℤ, starRingEnd ℂ (z : ℂ) = (z : ℂ) := fun z => by simp
      rw [hconj_int, Nat.cast_mul, jacobiSym.mul_left, Int.cast_mul]; ring
    have hre_eq : ∑ r ∈ P, w r * ‖∑ n ∈ I, κ n * ((jacobiSym (n : ℤ) r : ℤ) : ℂ)‖ ^ 2 =
        (∑ x ∈ I ×ˢ I, (κ x.1 * starRingEnd ℂ (κ x.2)) *
          ((∑ r ∈ P, w r * (jacobiSym ((x.1 * x.2 : ℕ) : ℤ) r : ℝ) : ℝ) : ℂ)).re := by
      have hC : ((∑ r ∈ P, w r * ‖∑ n ∈ I, κ n * ((jacobiSym (n : ℤ) r : ℤ) : ℂ)‖ ^ 2 : ℝ) : ℂ) =
          ∑ x ∈ I ×ˢ I, (κ x.1 * starRingEnd ℂ (κ x.2)) *
            ((∑ r ∈ P, w r * (jacobiSym ((x.1 * x.2 : ℕ) : ℤ) r : ℝ) : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum]
        calc ∑ r ∈ P, ((w r * ‖∑ n ∈ I, κ n * ((jacobiSym (n : ℤ) r : ℤ) : ℂ)‖ ^ 2 : ℝ) : ℂ)
            = ∑ r ∈ P, ∑ x ∈ I ×ˢ I, (w r : ℂ) * (κ x.1 * starRingEnd ℂ (κ x.2)) *
                ((jacobiSym ((x.1 * x.2 : ℕ) : ℤ) r : ℤ) : ℂ) := Finset.sum_congr rfl hsq_eq
          _ = ∑ x ∈ I ×ˢ I, ∑ r ∈ P, (w r : ℂ) * (κ x.1 * starRingEnd ℂ (κ x.2)) *
                ((jacobiSym ((x.1 * x.2 : ℕ) : ℤ) r : ℤ) : ℂ) := Finset.sum_comm
          _ = _ := Finset.sum_congr rfl fun x _ => by
                rw [Complex.ofReal_sum, Finset.mul_sum]
                refine Finset.sum_congr rfl fun r _ => by push_cast; ring
      have hre := congrArg Complex.re hC
      rw [Complex.ofReal_re] at hre
      exact hre
    rw [hre_eq]
    refine (Complex.re_le_norm _).trans ((norm_sum_le _ _).trans (Finset.sum_le_sum fun x hx => ?_))
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
    have hx1_pos : 1 ≤ x.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp hx).1).1
    have hx2_pos : 1 ≤ x.2 := (Finset.mem_Icc.mp (Finset.mem_product.mp hx).2).1
    obtain ⟨ε, hε_abs, hε_eq⟩ := jacobiSym_factor_soutPart h8 ha4 (Nat.mul_pos hx1_pos hx2_pos)
    have hsum_fac : ∑ r ∈ P, w r * (jacobiSym ((x.1 * x.2 : ℕ) : ℤ) r : ℝ) =
        (ε : ℝ) * ∑ r ∈ P, w r * (jacobiSym (r : ℤ) (soutPart m₀ (x.1 * x.2)) : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r hr => ?_
      obtain ⟨hr_pr, hr_mod, hr_gtZ⟩ := hP r hr
      have hr_odd : Odd r := by
        have h4 : r ≡ a₀ [MOD 4] := (hr_mod.of_dvd h8).of_dvd (by norm_num)
        change r % 4 = a₀ % 4 at h4
        exact Nat.odd_iff.mpr (by omega)
      have hcop_x : ∀ u ∈ I, Nat.Coprime u r := fun u hu => by
        have hu_le : (u : ℝ) ≤ Z := (by exact_mod_cast (Finset.mem_Icc.mp hu).2 : (u : ℝ) ≤ (⌊Z⌋₊ : ℝ)).trans
          (Nat.floor_le hZ0.le)
        have hlt : u < r := by exact_mod_cast lt_of_le_of_lt hu_le hr_gtZ
        have hu_pos : 0 < u := (Finset.mem_Icc.mp hu).1
        exact ((Nat.Prime.coprime_iff_not_dvd hr_pr).mpr fun hdvd =>
          absurd (Nat.le_of_dvd hu_pos hdvd) (by omega)).symm
      have hcop_mul : Nat.Coprime (x.1 * x.2) r :=
        (hcop_x x.1 (Finset.mem_product.mp hx).1).mul_left (hcop_x x.2 (Finset.mem_product.mp hx).2)
      have hje := hε_eq r hr_odd hr_mod hcop_mul
      have hjeR : (jacobiSym ((x.1 * x.2 : ℕ) : ℤ) r : ℝ) =
          (ε : ℝ) * (jacobiSym (r : ℤ) (soutPart m₀ (x.1 * x.2)) : ℝ) := by exact_mod_cast hje
      rw [hjeR]; ring
    rw [hsum_fac, abs_mul]
    have hεR : |(ε : ℝ)| = 1 := by exact_mod_cast hε_abs
    rw [hεR, one_mul]
  -- Step 2: Split `I ×ˢ I` into bad prime-power pairs (`soutPart ∈ {1, s_exc}`) vs good pairs
  set Bad := (I ×ˢ I).filter fun x =>
    IsPrimePow x.1 ∧ IsPrimePow x.2 ∧ (soutPart m₀ (x.1 * x.2) = 1 ∨ soutPart m₀ (x.1 * x.2) = s_exc)
  set Good := (I ×ˢ I).filter fun x =>
    ¬ (IsPrimePow x.1 ∧ IsPrimePow x.2 ∧ (soutPart m₀ (x.1 * x.2) = 1 ∨ soutPart m₀ (x.1 * x.2) = s_exc))
  have hsplit : I ×ˢ I = Bad ∪ Good := by
    ext x; simp only [Bad, Good, Finset.mem_union, Finset.mem_filter]; tauto
  have hdisj : Disjoint Bad Good := Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1
  have htriv_jac : ∀ s : ℕ, |∑ r ∈ P, w r * (jacobiSym (r : ℤ) s : ℝ)| ≤ W := fun s => by
    calc |∑ r ∈ P, w r * (jacobiSym (r : ℤ) s : ℝ)|
        ≤ ∑ r ∈ P, |w r * (jacobiSym (r : ℤ) s : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r ∈ P, w r := Finset.sum_le_sum fun r hr => by
          rw [abs_mul, abs_of_nonneg (hw_nn r hr)]
          have hj1 : |(jacobiSym (r : ℤ) s : ℝ)| ≤ 1 := by
            have h1 : |jacobiSym (r : ℤ) s| ≤ 1 := by
              rcases jacobiSym.trichotomy (r : ℤ) s with h | h | h <;> rw [h] <;> norm_num
            exact_mod_cast h1
          exact mul_le_of_le_one_right (hw_nn r hr) hj1
  have hBad_bd : ∑ x ∈ Bad, ‖κ x.1‖ * ‖κ x.2‖ *
      |∑ r ∈ P, w r * (jacobiSym (r : ℤ) (soutPart m₀ (x.1 * x.2)) : ℝ)| ≤
      100 * W * y * (Real.log Z + 2) ^ 2 := by
    calc ∑ x ∈ Bad, _
        ≤ ∑ x ∈ Bad, (ZeroDensityWindow.cN y x.1 * ZeroDensityWindow.cN y x.2) * W :=
          Finset.sum_le_sum fun x hx => by
            have hx_prod := (Finset.mem_filter.mp hx).1
            exact mul_le_mul
              (mul_le_mul (hκ_le x.1 (Finset.mem_product.mp hx_prod).1)
                (hκ_le x.2 (Finset.mem_product.mp hx_prod).2) (norm_nonneg _)
                (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (le_min zero_le_one (by positivity))))
              (htriv_jac _) (abs_nonneg _) (mul_nonneg
                (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (le_min zero_le_one (by positivity)))
                (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (le_min zero_le_one (by positivity))))
      _ = (∑ x ∈ Bad, ZeroDensityWindow.cN y x.1 * ZeroDensityWindow.cN y x.2) * W :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ (100 * y * (Real.log Z + 2) ^ 2) * W :=
          mul_le_mul_of_nonneg_right (sum_bad_primePow_pairs_le hB2 hy hyZ hB2_le hsmall) hW_nn
      _ = 100 * W * y * (Real.log Z + 2) ^ 2 := by ring
  have hGood_bd : ∑ x ∈ Good, ‖κ x.1‖ * ‖κ x.2‖ *
      |∑ r ∈ P, w r * (jacobiSym (r : ℤ) (soutPart m₀ (x.1 * x.2)) : ℝ)| ≤
      36 * W * y * (Real.log Z + 2) ^ 2 := by
    have hterm : ∀ x ∈ Good, ‖κ x.1‖ * ‖κ x.2‖ *
        |∑ r ∈ P, w r * (jacobiSym (r : ℤ) (soutPart m₀ (x.1 * x.2)) : ℝ)| ≤
        (Λ x.1 * Λ x.2) * ((1 / Z ^ 2) * W) := by
      intro x hx
      obtain ⟨hx_prod, hnotbad⟩ := Finset.mem_filter.mp hx
      by_cases hnz : κ x.1 = 0 ∨ κ x.2 = 0
      · rcases hnz with h1 | h2
        · simp only [h1, norm_zero, zero_mul]
          exact mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg) (by positivity)
        · simp only [h2, norm_zero, mul_zero, zero_mul]
          exact mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg) (by positivity)
      · push Not at hnz
        have hpp1 : IsPrimePow x.1 := hκ_pp x.1 hnz.1
        have hpp2 : IsPrimePow x.2 := hκ_pp x.2 hnz.2
        have hsne : soutPart m₀ (x.1 * x.2) ≠ 1 ∧ soutPart m₀ (x.1 * x.2) ≠ s_exc := by
          constructor <;> intro h <;> apply hnotbad <;> exact ⟨hpp1, hpp2, by tauto⟩
        have hprops := soutPart_props m₀ (x.1 * x.2)
        have hprod_pos : 1 ≤ x.1 * x.2 :=
          Nat.mul_pos (Finset.mem_Icc.mp (Finset.mem_product.mp hx_prod).1).1
            (Finset.mem_Icc.mp (Finset.mem_product.mp hx_prod).2).1
        have hs_pos : 1 ≤ soutPart m₀ (x.1 * x.2) := by obtain ⟨k, hk⟩ := hprops.1; omega
        have hs_gt1 : 1 < soutPart m₀ (x.1 * x.2) := by omega
        have hs_leZ2 : (soutPart m₀ (x.1 * x.2) : ℝ) ≤ Z ^ 2 := by
          have hx1_le : (x.1 : ℝ) ≤ Z := (by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_product.mp hx_prod).1).2 :
            (x.1 : ℝ) ≤ (⌊Z⌋₊ : ℝ)).trans (Nat.floor_le hZ0.le)
          have hx2_le : (x.2 : ℝ) ≤ Z := (by exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_product.mp hx_prod).2).2 :
            (x.2 : ℝ) ≤ (⌊Z⌋₊ : ℝ)).trans (Nat.floor_le hZ0.le)
          calc (soutPart m₀ (x.1 * x.2) : ℝ)
              ≤ ((x.1 * x.2 : ℕ) : ℝ) := by exact_mod_cast hprops.2.2.2 hprod_pos
            _ = (x.1 : ℝ) * (x.2 : ℝ) := by push_cast; rfl
            _ ≤ Z * Z := mul_le_mul hx1_le hx2_le (Nat.cast_nonneg _) hZ0.le
            _ = Z ^ 2 := (sq Z).symm
        have htw := htwist (soutPart m₀ (x.1 * x.2)) hs_gt1 hprops.1 hprops.2.1 hprops.2.2.1 hs_leZ2 hsne.2
        have hκ1 : ‖κ x.1‖ ≤ Λ x.1 :=
          (hκ_le x.1 (Finset.mem_product.mp hx_prod).1).trans
            (mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (min_le_left _ _))
        have hκ2 : ‖κ x.2‖ ≤ Λ x.2 :=
          (hκ_le x.2 (Finset.mem_product.mp hx_prod).2).trans
            (mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (min_le_left _ _))
        exact mul_le_mul (mul_le_mul hκ1 hκ2 (norm_nonneg _) ArithmeticFunction.vonMangoldt_nonneg)
          htw (abs_nonneg _) (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg)
    have hpsi : ∑ n ∈ I, Λ n ≤ 6 * Z := by
      have hsub : I ⊆ Finset.range (⌊Z⌋₊ + 1) := fun n hn => by
        simp only [I, Finset.mem_Icc, Finset.mem_range] at hn ⊢; omega
      exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg).trans
        (Stage4ExplicitFormula.chebyshevPsi_le_six_mul (by linarith))
    calc ∑ x ∈ Good, _
        ≤ ∑ x ∈ Good, (Λ x.1 * Λ x.2) * ((1 / Z ^ 2) * W) := Finset.sum_le_sum hterm
      _ ≤ ∑ x ∈ I ×ˢ I, (Λ x.1 * Λ x.2) * ((1 / Z ^ 2) * W) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ =>
            mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg) (by positivity)
      _ = (∑ n ∈ I, Λ n) ^ 2 * ((1 / Z ^ 2) * W) := by
          have hsq : ∑ x ∈ I ×ˢ I, Λ x.1 * Λ x.2 = (∑ n ∈ I, Λ n) ^ 2 := by
            rw [Finset.sum_product, sq, Finset.sum_mul]
            exact Finset.sum_congr rfl fun n _ => (Finset.mul_sum I (fun y => Λ y) (Λ n)).symm
          rw [← Finset.sum_mul, hsq]
      _ ≤ (6 * Z) ^ 2 * ((1 / Z ^ 2) * W) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg) hpsi 2) (by positivity)
      _ = 36 * W := by field_simp [hZ0.ne']; ring
      _ ≤ 36 * W * y * (Real.log Z + 2) ^ 2 := by
          have h1 : (1 : ℝ) ≤ y * (Real.log Z + 2) ^ 2 := by nlinarith
          nlinarith
  calc ∑ r ∈ P, w r * ‖∑ n ∈ I, κ n * ((jacobiSym (n : ℤ) r : ℤ) : ℂ)‖ ^ 2
      ≤ ∑ x ∈ I ×ˢ I, ‖κ x.1‖ * ‖κ x.2‖ *
          |∑ r ∈ P, w r * (jacobiSym (r : ℤ) (soutPart m₀ (x.1 * x.2)) : ℝ)| := hexpand
    _ = (∑ x ∈ Bad, _) + (∑ x ∈ Good, _) := by rw [hsplit, Finset.sum_union hdisj]
    _ ≤ 100 * W * y * (Real.log Z + 2) ^ 2 + 36 * W * y * (Real.log Z + 2) ^ 2 := add_le_add hBad_bd hGood_bd
    _ ≤ 150 * W * y * (Real.log Z + 2) ^ 2 := by
        have : 0 ≤ W * y * (Real.log Z + 2) ^ 2 := by positivity
        linarith

/-! ### Section 4c: Unconditional Tent-Weighted Prime Lower Bound & Twist Cancellation -/

/-- Tent weight `tentWt X n = Λ(n) * (max(2X-n, 0) - 2 max(3X/2-n, 0) + max(X-n, 0))`
matching `Stage11LinnikBridge.dyadic2Real (psi1AP m₀ a₀) X`. -/
def tentWt (X : ℝ) (n : ℕ) : ℝ :=
  Λ n * (max (2 * X - (n : ℝ)) 0 - 2 * max ((3 / 2 : ℝ) * X - (n : ℝ)) 0 + max (X - (n : ℝ)) 0)

/-- Finset of primes `p ∈ (X, 2 X]` with `p ≡ a₀ [MOD m₀]`. -/
def apPrimes (m₀ a₀ : ℕ) (X : ℝ) : Finset ℕ :=
  (Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter fun p => p.Prime ∧ p ≡ a₀ [MOD m₀]

private lemma tent_factor_bounds {X : ℝ} (hX : 0 ≤ X) (t : ℝ) :
    let w := max (2 * X - t) 0 - 2 * max ((3 / 2 : ℝ) * X - t) 0 + max (X - t) 0
    0 ≤ w ∧ w ≤ X / 2 ∧ (t ≤ X → w = 0) ∧ (2 * X ≤ t → w = 0) := by
  intro w
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [w]
    by_cases h1 : t ≤ X
    · rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
    · by_cases h2 : t ≤ (3 / 2 : ℝ) * X
      · rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_right (by linarith)]; linarith
      · by_cases h3 : t ≤ 2 * X
        · rw [max_eq_left (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]; linarith
        · rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]; norm_num
  · dsimp only [w]
    by_cases h1 : t ≤ X
    · rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
    · by_cases h2 : t ≤ (3 / 2 : ℝ) * X
      · rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_right (by linarith)]; linarith
      · by_cases h3 : t ≤ 2 * X
        · rw [max_eq_left (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]; linarith
        · rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]; linarith
  · intro ht; dsimp only [w]
    rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith)]; ring
  · intro ht; dsimp only [w]
    rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]; ring

theorem tentWt_nonneg {X : ℝ} (hX : 0 ≤ X) (n : ℕ) : 0 ≤ tentWt X n :=
  mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (tent_factor_bounds hX n).1

theorem tentWt_le_half_mul_log {X : ℝ} (hX : 1 ≤ X) {n : ℕ} (hn1 : 1 ≤ n) (hn2 : (n : ℝ) ≤ 2 * X) :
    tentWt X n ≤ (X / 2) * Real.log (2 * X) := by
  have h1 : tentWt X n ≤ Λ n * (X / 2) :=
    mul_le_mul_of_nonneg_left (tent_factor_bounds (by linarith) n).2.1 ArithmeticFunction.vonMangoldt_nonneg
  have h2 : Λ n ≤ Real.log (2 * X) :=
    ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log (by exact_mod_cast (by omega : 0 < n)) hn2)
  have h3 : Λ n * (X / 2) ≤ Real.log (2 * X) * (X / 2) :=
    mul_le_mul_of_nonneg_right h2 (by linarith)
  linarith

/-- Exact identity: `dyadic2Real (psi1AP m₀ a₀) X = ∑_{n ∈ Ioc ⌊X⌋₊ ⌊2X⌋₊, n ≡ a₀ [MOD m₀]} tentWt X n`. -/
private lemma dyadic2Real_psi1AP_eq_sum_tentWt (m₀ a₀ : ℕ) {X : ℝ} (hX : 0 ≤ X) :
    Stage11LinnikBridge.dyadic2Real (Stage11LinnikBridge.psi1AP m₀ a₀) X =
      ∑ n ∈ (Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter (fun n => n ≡ a₀ [MOD m₀]), tentWt X n := by
  have hext : ∀ y : ℝ, 0 ≤ y → y ≤ 2 * X →
      Stage11LinnikBridge.psi1AP m₀ a₀ y = ∑ n ∈ Finset.range (⌊2 * X⌋₊ + 1),
        if n ≡ a₀ [MOD m₀] then Λ n * max (y - (n : ℝ)) 0 else 0 := fun y hy hy2 => by
    unfold Stage11LinnikBridge.psi1AP
    refine Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right (Nat.floor_mono hy2) 1)) ?_
    intro n _ hn
    simp only [Finset.mem_range, not_lt] at hn
    have hyn : y < (n : ℝ) := lt_of_lt_of_le (Nat.lt_floor_add_one y) (by exact_mod_cast hn)
    simp [max_eq_right (by linarith : y - (n : ℝ) ≤ 0)]
  have hrew : Stage11LinnikBridge.dyadic2Real (Stage11LinnikBridge.psi1AP m₀ a₀) X =
      ∑ n ∈ Finset.range (⌊2 * X⌋₊ + 1), if n ≡ a₀ [MOD m₀] then tentWt X n else 0 := by
    unfold Stage11LinnikBridge.dyadic2Real tentWt
    rw [hext (2 * X) (by linarith) le_rfl, hext ((3 / 2 : ℝ) * X) (by linarith) (by linarith),
      hext X hX (by linarith), Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => by split_ifs <;> ring
  rw [hrew, ← Finset.sum_filter]
  have hsub : (Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter (fun n => n ≡ a₀ [MOD m₀]) ⊆
      (Finset.range (⌊2 * X⌋₊ + 1)).filter (fun n => n ≡ a₀ [MOD m₀]) := by
    intro n hn
    obtain ⟨hI, hm⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := (Finset.mem_Ioc.mp hI).2; omega), hm⟩
  symm
  refine Finset.sum_subset hsub fun n hn1 hn2 => ?_
  obtain ⟨hr, hm⟩ := Finset.mem_filter.mp hn1
  have hle : n ≤ ⌊X⌋₊ := by
    by_contra hgt
    exact hn2 (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, by simp only [Finset.mem_range] at hr; omega⟩, hm⟩)
  have hn_leX : (n : ℝ) ≤ X := (by exact_mod_cast hle : (n : ℝ) ≤ (⌊X⌋₊ : ℝ)).trans (Nat.floor_le hX)
  unfold tentWt
  rw [(tent_factor_bounds hX n).2.2.1 hn_leX, mul_zero]

/-- Universal multiplicativity of `twistedChar` for coprime moduli `Coprime m₀ s` (even for non-coprime `n`!). -/
private lemma twistedChar_apply_nat_all {m₀ s : ℕ} [NeZero m₀] [NeZero s] (_hcop : Nat.Coprime m₀ s)
    (χ : DirichletCharacter ℂ m₀) (ψ : DirichletCharacter ℂ s) (n : ℕ) :
    Stage11SecondMomentFrame.twistedChar χ ψ (n : ZMod (m₀ * s)) = χ (n : ZMod m₀) * ψ (n : ZMod s) := by
  by_cases hcn : Nat.Coprime n (m₀ * s)
  · exact Stage11SecondMomentFrame.twistedChar_apply_nat_of_coprime χ ψ hcn
  · have hleft : Stage11SecondMomentFrame.twistedChar χ ψ (n : ZMod (m₀ * s)) = 0 :=
      MulChar.map_nonunit _ (fun hu => hcn ((ZMod.isUnit_iff_coprime n (m₀ * s)).mp hu))
    have hnot : ¬ Nat.Coprime n m₀ ∨ ¬ Nat.Coprime n s := by
      by_contra h; push Not at h; exact hcn (h.1.mul_right h.2)
    rw [hleft]
    rcases hnot with h1 | h2
    · rw [MulChar.map_nonunit χ (fun hu => h1 ((ZMod.isUnit_iff_coprime n m₀).mp hu)), zero_mul]
    · rw [MulChar.map_nonunit ψ (fun hu => h2 ((ZMod.isUnit_iff_coprime n s).mp hu)), mul_zero]

/-- Exact character-orthogonality identity for the twisted tent sum:
`(φ(m₀))⁻¹ ∑_{χ mod m₀} conj(χ a₀) dyadic2 (psi1Char (twistedChar χ χ_s)) X
  = ∑_{n ∈ Ioc ⌊X⌋₊ ⌊2X⌋₊, n ≡ a₀ [MOD m₀]} tentWt X n * (n | s)`. -/
private lemma dyadic2_psi1Char_twisted_eq_sum_tentWt {m₀ a₀ s : ℕ} [NeZero m₀] [NeZero s]
    (hcop_am : Nat.Coprime a₀ m₀) (hcop_ms : Nat.Coprime m₀ s) (hs_odd : Odd s) {X : ℝ} (hX : 0 ≤ X) :
    (m₀.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ m₀,
          starRingEnd ℂ (χ (a₀ : ZMod m₀)) *
            Stage11LinnikBridge.dyadic2
              (Stage4ExplicitFormula.psi1Char
                (Stage11SecondMomentFrame.twistedChar χ (quadCharOfOddSqf s hs_odd))) X =
      ∑ n ∈ (Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter (fun n => n ≡ a₀ [MOD m₀]),
        (tentWt X n : ℂ) * ((jacobiSym (n : ℤ) s : ℤ) : ℂ) := by
  have hext : ∀ (χ : DirichletCharacter ℂ m₀) (y : ℝ), 0 ≤ y → y ≤ 2 * X →
      Stage4ExplicitFormula.psi1Char
          (Stage11SecondMomentFrame.twistedChar χ (quadCharOfOddSqf s hs_odd)) y =
        ∑ n ∈ Finset.range (⌊2 * X⌋₊ + 1),
          (Λ n : ℂ) * (χ (n : ZMod m₀) * ((jacobiSym (n : ℤ) s : ℤ) : ℂ)) *
            ((max (y - (n : ℝ)) 0 : ℝ) : ℂ) := fun χ y hy hy2 => by
    unfold Stage4ExplicitFormula.psi1Char
    have hsub := Finset.range_mono (Nat.add_le_add_right (Nat.floor_mono hy2) 1)
    rw [Finset.sum_subset hsub (fun n _ hn => by
      simp only [Finset.mem_range, not_lt] at hn
      have hyn : y < (n : ℝ) := lt_of_lt_of_le (Nat.lt_floor_add_one y) (by exact_mod_cast hn)
      simp [max_eq_right (by linarith : y - (n : ℝ) ≤ 0)])]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [twistedChar_apply_nat_all hcop_ms, quadCharOfOddSqf_apply_nat hs_odd]
  have hdy : ∀ χ : DirichletCharacter ℂ m₀,
      Stage11LinnikBridge.dyadic2
          (Stage4ExplicitFormula.psi1Char
            (Stage11SecondMomentFrame.twistedChar χ (quadCharOfOddSqf s hs_odd))) X =
        ∑ n ∈ Finset.range (⌊2 * X⌋₊ + 1),
          (tentWt X n : ℂ) * (χ (n : ZMod m₀) * ((jacobiSym (n : ℤ) s : ℤ) : ℂ)) := fun χ => by
    unfold Stage11LinnikBridge.dyadic2 tentWt
    rw [hext χ (2 * X) (by linarith) le_rfl, hext χ ((3 / 2 : ℝ) * X) (by linarith) (by linarith),
      hext χ X hX (by linarith), Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => by push_cast; ring
  simp_rw [hdy, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm : ∀ n ∈ Finset.range (⌊2 * X⌋₊ + 1),
      ∑ χ : DirichletCharacter ℂ m₀,
          (m₀.totient : ℂ)⁻¹ *
            (starRingEnd ℂ (χ (a₀ : ZMod m₀)) *
              ((tentWt X n : ℂ) * (χ (n : ZMod m₀) * ((jacobiSym (n : ℤ) s : ℤ) : ℂ)))) =
        if n ≡ a₀ [MOD m₀] then (tentWt X n : ℂ) * ((jacobiSym (n : ℤ) s : ℤ) : ℂ) else 0 := by
    intro n _
    have hrearr :
        ∑ χ : DirichletCharacter ℂ m₀,
            (m₀.totient : ℂ)⁻¹ *
              (starRingEnd ℂ (χ (a₀ : ZMod m₀)) *
                ((tentWt X n : ℂ) * (χ (n : ZMod m₀) * ((jacobiSym (n : ℤ) s : ℤ) : ℂ)))) =
          ((m₀.totient : ℂ)⁻¹ *
            ∑ χ : DirichletCharacter ℂ m₀, starRingEnd ℂ (χ (a₀ : ZMod m₀)) * χ (n : ZMod m₀)) *
            ((tentWt X n : ℂ) * ((jacobiSym (n : ℤ) s : ℤ) : ℂ)) := by
      rw [← Finset.mul_sum, mul_assoc]; congr 1
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun χ _ => by ring
    rw [hrearr, Stage2DirichletAP.char_orthogonality_indicator_nat hcop_am n]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  have hsub : (Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter (fun n => n ≡ a₀ [MOD m₀]) ⊆
      (Finset.range (⌊2 * X⌋₊ + 1)).filter (fun n => n ≡ a₀ [MOD m₀]) := by
    intro n hn
    obtain ⟨hI, hm⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := (Finset.mem_Ioc.mp hI).2; omega), hm⟩
  symm
  refine Finset.sum_subset hsub fun n hn1 hn2 => ?_
  obtain ⟨hr, hm⟩ := Finset.mem_filter.mp hn1
  have hle : n ≤ ⌊X⌋₊ := by
    by_contra hgt
    exact hn2 (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, by simp only [Finset.mem_range] at hr; omega⟩, hm⟩)
  have hn_leX : (n : ℝ) ≤ X := (by exact_mod_cast hle : (n : ℝ) ≤ (⌊X⌋₊ : ℝ)).trans (Nat.floor_le hX)
  unfold tentWt
  rw [(tent_factor_bounds hX n).2.2.1 hn_leX, mul_zero]; simp

/-- Non-prime prime-power contribution to the tent sum on `(X, 2 X]`:
`∑_{n ∈ Ioc ⌊X⌋₊ ⌊2X⌋₊, ¬ n.Prime} tentWt X n ≤ 3 * X * √(2 X) * (log (2 X) + 2)`. -/
private lemma sum_tentWt_nonprime_le {X : ℝ} (hX : 1 ≤ X) :
    ∑ n ∈ (Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter (fun n => ¬ n.Prime), tentWt X n ≤
      3 * X * Real.sqrt (2 * X) * (Real.log (2 * X) + 2) := by
  classical
  have h2X : 1 ≤ 2 * X := by linarith
  have h2X0 : 0 < 2 * X := by linarith
  have hL2X_nn : 0 ≤ Real.log (2 * X) := Real.log_nonneg h2X
  -- Every non-prime `n ∈ Ioc ⌊X⌋₊ ⌊2X⌋₊` with `Λ n ≠ 0` is `p^a` with `p ≤ √(2X)` and `a ≥ 2`!
  let S_pp := (Finset.Icc 1 ⌊2 * X⌋₊).filter fun n => IsPrimePow n ∧ ¬ n.Prime
  have hle_sum : ∑ n ∈ (Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter (fun n => ¬ n.Prime), tentWt X n ≤
      (X / 2) * ∑ n ∈ S_pp, Λ n := by
    rw [Finset.mul_sum]
    have hsplit : ∑ n ∈ (Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter (fun n => ¬ n.Prime), tentWt X n =
        ∑ n ∈ ((Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter (fun n => ¬ n.Prime)).filter IsPrimePow, tentWt X n := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun n _ hn2 => ?_
      have hnotpp : ¬ IsPrimePow n := fun hpp => hn2 (Finset.mem_filter.mpr ⟨‹_›, hpp⟩)
      unfold tentWt
      rw [ArithmeticFunction.vonMangoldt_apply, if_neg hnotpp, zero_mul]
    rw [hsplit]
    have hsub : ((Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter (fun n => ¬ n.Prime)).filter IsPrimePow ⊆ S_pp := by
      intro n hn
      obtain ⟨h1, hpp⟩ := Finset.mem_filter.mp hn
      obtain ⟨hI, hnp⟩ := Finset.mem_filter.mp h1
      have hn1 : 1 ≤ n := by have := (Finset.mem_Ioc.mp hI).1; omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn1, (Finset.mem_Ioc.mp hI).2⟩, hpp, hnp⟩
    calc ∑ n ∈ ((Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter (fun n => ¬ n.Prime)).filter IsPrimePow, tentWt X n
        ≤ ∑ n ∈ ((Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter (fun n => ¬ n.Prime)).filter IsPrimePow, (X / 2) * Λ n :=
          Finset.sum_le_sum fun n _ => by
            unfold tentWt
            have h1 := mul_le_mul_of_nonneg_left (tent_factor_bounds (X := X) (by linarith) (n : ℝ)).2.1
              (ArithmeticFunction.vonMangoldt_nonneg (n := n))
            linarith
      _ ≤ ∑ n ∈ S_pp, (X / 2) * Λ n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
            mul_nonneg (by linarith) ArithmeticFunction.vonMangoldt_nonneg
  -- Bound `∑ n ∈ S_pp, Λ n ≤ 2 * √(2 X) * (Real.log (2 X) + 2)` (every `n = p^a` with `a ≥ 2` has `p ≤ √(2X)`!)
  have hSpp_le : ∑ n ∈ S_pp, Λ n ≤ 2 * Real.sqrt (2 * X) * (Real.log (2 * X) + 2) := by
    let P_sm := (Finset.Icc 1 ⌊Real.sqrt (2 * X)⌋₊).filter Nat.Prime
    let H_p : ℕ → Finset ℕ := fun p => (Finset.Icc 1 ⌊2 * X⌋₊).filter fun n => ∃ a : ℕ, 1 ≤ a ∧ n = p ^ a
    have hsub : S_pp ⊆ P_sm.biUnion H_p := by
      intro n hn
      obtain ⟨hnI, hpp, hnp⟩ := Finset.mem_filter.mp hn
      obtain ⟨hp, a, ha1, hneq⟩ := isPrimePow_eq_minFac_pow hpp
      have ha2 : 2 ≤ a := by
        by_contra hlt; have ha_eq : a = 1 := by omega
        rw [ha_eq, pow_one] at hneq; exact hnp (hneq ▸ hp)
      have hp_sq_le : ((n.minFac : ℝ)) ^ 2 ≤ 2 * X := by
        have h1 : n.minFac ^ 2 ≤ n := by
          conv_rhs => rw [hneq]
          exact Nat.pow_le_pow_right hp.pos ha2
        have h2 : (n : ℝ) ≤ 2 * X := (by exact_mod_cast (Finset.mem_Icc.mp hnI).2 : (n : ℝ) ≤ (⌊2 * X⌋₊ : ℝ)).trans
          (Nat.floor_le h2X0.le)
        exact (by exact_mod_cast h1 : ((n.minFac : ℝ)) ^ 2 ≤ (n : ℝ)).trans h2
      have hp_le_sqrt : n.minFac ≤ ⌊Real.sqrt (2 * X)⌋₊ :=
        Nat.le_floor (Real.le_sqrt_of_sq_le hp_sq_le)
      exact Finset.mem_biUnion.mpr ⟨n.minFac,
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.pos, hp_le_sqrt⟩, hp⟩,
        Finset.mem_filter.mpr ⟨hnI, a, ha1, hneq⟩⟩
    have hterm : ∀ p ∈ P_sm, ∑ n ∈ H_p p, Λ n ≤ 2 * (Real.log (2 * X) + 2) := fun p hp => by
      have hpr : p.Prime := (Finset.mem_filter.mp hp).2
      have hEq : ∑ n ∈ H_p p, Λ n = ∑ n ∈ H_p p, ZeroDensityWindow.cN (2 * X) n := by
        refine Finset.sum_congr rfl fun n hn => ?_
        have hnI := (Finset.mem_filter.mp hn).1
        have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by have := (Finset.mem_Icc.mp hnI).1; omega : 0 < n)
        have hn_le : (n : ℝ) ≤ 2 * X := (by exact_mod_cast (Finset.mem_Icc.mp hnI).2 : (n : ℝ) ≤ (⌊2 * X⌋₊ : ℝ)).trans
          (Nat.floor_le h2X0.le)
        unfold ZeroDensityWindow.cN
        rw [min_eq_left ((one_le_div hn_pos).mpr hn_le), mul_one]
      rw [hEq]
      exact (sum_cN_prime_powers_le h2X le_rfl hpr).1
    have hcard : (P_sm.card : ℝ) ≤ Real.sqrt (2 * X) := by
      have h1 : P_sm.card ≤ ⌊Real.sqrt (2 * X)⌋₊ := by
        have hsub_c := Finset.card_le_card (Finset.filter_subset Nat.Prime (Finset.Icc 1 ⌊Real.sqrt (2 * X)⌋₊))
        rw [Nat.card_Icc] at hsub_c
        dsimp only [P_sm]
        omega
      exact (by exact_mod_cast h1 : (P_sm.card : ℝ) ≤ (⌊Real.sqrt (2 * X)⌋₊ : ℝ)).trans
        (Nat.floor_le (Real.sqrt_nonneg _))
    calc ∑ n ∈ S_pp, Λ n
        ≤ ∑ n ∈ P_sm.biUnion H_p, Λ n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg
      _ ≤ ∑ p ∈ P_sm, ∑ n ∈ H_p p, Λ n := sum_biUnion_le_of_nonneg fun _ => ArithmeticFunction.vonMangoldt_nonneg
      _ ≤ ∑ _p ∈ P_sm, 2 * (Real.log (2 * X) + 2) := Finset.sum_le_sum hterm
      _ = (P_sm.card : ℝ) * (2 * (Real.log (2 * X) + 2)) := by simp
      _ ≤ Real.sqrt (2 * X) * (2 * (Real.log (2 * X) + 2)) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 2 * Real.sqrt (2 * X) * (Real.log (2 * X) + 2) := by ring
  calc ∑ n ∈ (Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter (fun n => ¬ n.Prime), tentWt X n
      ≤ (X / 2) * ∑ n ∈ S_pp, Λ n := hle_sum
    _ ≤ (X / 2) * (2 * Real.sqrt (2 * X) * (Real.log (2 * X) + 2)) :=
        mul_le_mul_of_nonneg_left hSpp_le (by linarith)
    _ = X * Real.sqrt (2 * X) * (Real.log (2 * X) + 2) := by ring
    _ ≤ 3 * X * Real.sqrt (2 * X) * (Real.log (2 * X) + 2) := by
        have : 0 ≤ X * Real.sqrt (2 * X) * (Real.log (2 * X) + 2) := by positivity
        linarith

/-- For coprime `m₀, s`, `twistedChar χ ψ` with primitive `ψ : DirichletCharacter ℂ s` has `s ∣ conductor`. -/
private lemma right_dvd_conductor_twistedChar {m₀ s : ℕ} [NeZero m₀] [NeZero s]
    (hcop : Nat.Coprime m₀ s) (χ : DirichletCharacter ℂ m₀) {ψ : DirichletCharacter ℂ s}
    (hψ : ψ.IsPrimitive) :
    s ∣ (Stage11SecondMomentFrame.twistedChar χ ψ).conductor := by
  set η := Stage11SecondMomentFrame.twistedChar χ ψ
  set f := η.conductor
  have hf_dvd : f ∣ m₀ * s := η.conductor_dvd_level
  have : NeZero f := ⟨η.conductor_ne_zero⟩
  set f₁ := Nat.gcd f m₀
  set f₂ := Nat.gcd f s
  have hf₁_dvd : f₁ ∣ m₀ := Nat.gcd_dvd_right f m₀
  have hf₂_dvd : f₂ ∣ s := Nat.gcd_dvd_right f s
  have hf₁_pos : 0 < f₁ := Nat.gcd_pos_of_pos_right f (NeZero.pos m₀)
  have hf₂_pos : 0 < f₂ := Nat.gcd_pos_of_pos_right f (NeZero.pos s)
  have : NeZero f₁ := ⟨hf₁_pos.ne'⟩
  have : NeZero f₂ := ⟨hf₂_pos.ne'⟩
  have hcop_f : Nat.Coprime f₁ f₂ :=
    (hcop.coprime_dvd_left hf₁_dvd).coprime_dvd_right hf₂_dvd
  have hf_eq : f = f₁ * f₂ := by
    have h1 : f ∣ f₁ * f₂ := by
      have hmul := Nat.gcd_mul_right_dvd_mul_gcd f m₀ s
      rwa [Nat.gcd_eq_left hf_dvd] at hmul
    exact Nat.dvd_antisymm h1 (hcop_f.mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_left f m₀) (Nat.gcd_dvd_left f s))
  have hη_ker : MonoidHom.ker (ZMod.unitsMap hf_dvd) ≤ MonoidHom.ker η.toUnitHom :=
    (DirichletCharacter.factorsThrough_iff_ker_unitsMap hf_dvd).mp (DirichletCharacter.factorsThrough_conductor η)
  have hf₂_eq : f₂ = s := by
    have hfac : ψ.FactorsThrough f₂ := by
      refine (DirichletCharacter.factorsThrough_iff_ker_unitsMap hf₂_dvd).mpr fun a ha => ?_
      rw [MonoidHom.mem_ker] at ha
      let cr := Nat.chineseRemainder hcop 1 (a : ZMod s).val
      set n := cr.val
      have hnM : (n : ZMod m₀) = 1 := by simpa using (ZMod.natCast_eq_natCast_iff n 1 m₀).mpr cr.property.1
      have hns : (n : ZMod s) = (a : ZMod s) := by
        have h1 := (ZMod.natCast_eq_natCast_iff n (a : ZMod s).val s).mpr cr.property.2
        rwa [ZMod.natCast_zmod_val] at h1
      have ha1_f₂ : (a : ZMod s).val ≡ 1 [MOD f₂] := by
        have hc := congrArg (Units.val : (ZMod f₂)ˣ → ZMod f₂) ha
        change ZMod.castHom hf₂_dvd (ZMod f₂) (a : ZMod s) = 1 at hc
        rw [← ZMod.natCast_zmod_val (a : ZMod s), map_natCast] at hc
        exact (ZMod.natCast_eq_natCast_iff _ 1 f₂).mp (by simpa using hc)
      have hn1_f : n ≡ 1 [MOD f] := by
        rw [hf_eq]
        exact (Nat.modEq_and_modEq_iff_modEq_mul hcop_f).mp
          ⟨cr.property.1.of_dvd hf₁_dvd, (cr.property.2.of_dvd hf₂_dvd).trans ha1_f₂⟩
      have hcop_n : Nat.Coprime n (m₀ * s) :=
        ((ZMod.isUnit_iff_coprime n m₀).mp (hnM ▸ isUnit_one)).mul_right
          ((ZMod.isUnit_iff_coprime n s).mp (hns ▸ a.isUnit))
      have hu : IsUnit (n : ZMod (m₀ * s)) := (ZMod.isUnit_iff_coprime n (m₀ * s)).mpr hcop_n
      have hu_ker : hu.unit ∈ MonoidHom.ker (ZMod.unitsMap hf_dvd) := by
        rw [MonoidHom.mem_ker]; apply Units.ext
        change ZMod.castHom hf_dvd (ZMod f) (n : ZMod (m₀ * s)) = 1
        rw [map_natCast]; simpa using (ZMod.natCast_eq_natCast_iff n 1 f).mpr hn1_f
      have hη1 : η (n : ZMod (m₀ * s)) = 1 := by
        have h1 := hη_ker hu_ker
        rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one] at h1
        simpa [IsUnit.unit_spec] using h1
      rw [Stage11SecondMomentFrame.twistedChar_apply_nat_of_coprime χ ψ hcop_n, hnM, hns, map_one, one_mul] at hη1
      rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]; exact hη1
    have hc0 : ψ.conductor ≤ f₂ := Nat.sInf_le hfac
    have hψ' : ψ.conductor = s := hψ
    rw [hψ'] at hc0
    exact le_antisymm (Nat.le_of_dvd (NeZero.pos s) hf₂_dvd) hc0
  rw [hf_eq, hf₂_eq]
  exact dvd_mul_left s f₁

/-- Injectivity of `χ ↦ twistedChar χ ψ` on `DirichletCharacter ℂ m₀` for coprime `m₀, s`. -/
private lemma twistedChar_injective_left {m₀ s : ℕ} [NeZero m₀] [NeZero s]
    (hcop : Nat.Coprime m₀ s) (ψ : DirichletCharacter ℂ s) :
    Function.Injective (fun χ : DirichletCharacter ℂ m₀ => Stage11SecondMomentFrame.twistedChar χ ψ) := by
  intro χ₁ χ₂ heq
  ext u
  let cr := Nat.chineseRemainder hcop (u : ZMod m₀).val 1
  set n := cr.val
  have hnM : (n : ZMod m₀) = (u : ZMod m₀) := by
    have h1 := (ZMod.natCast_eq_natCast_iff n (u : ZMod m₀).val m₀).mpr cr.property.1
    rwa [ZMod.natCast_zmod_val] at h1
  have hns : (n : ZMod s) = 1 := by simpa using (ZMod.natCast_eq_natCast_iff n 1 s).mpr cr.property.2
  have hval := congrArg (fun η : DirichletCharacter ℂ (m₀ * s) => η (n : ZMod (m₀ * s))) heq
  rw [twistedChar_apply_nat_all hcop, twistedChar_apply_nat_all hcop, hnM, hns, map_one, mul_one, mul_one] at hval
  exact hval

/-- Helper: `lZeroMult χ ρ = lZeroMult χ.primitiveCharacter ρ` for `χ ≠ 1` and `0 < ρ.re`. -/
private lemma lZeroMult_eq_primitive_local {m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ m}
    (hχ : χ ≠ 1) {ρ : ℂ} (h0 : 0 < ρ.re) :
    haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    Stage11LinnikBridge.lZeroMult χ ρ = Stage11LinnikBridge.lZeroMult χ.primitiveCharacter ρ := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  set ψ := χ.primitiveCharacter
  have hψ : ψ ≠ 1 := fun h1 => hχ (by dsimp only [ψ] at h1; rw [← χ.changeLevel_primitiveCharacter, h1, map_one])
  let euler : ℂ → ℂ := fun z => ∏ p ∈ m.primeFactors, (1 - ψ (p : ZMod χ.conductor) * (p : ℂ) ^ (-z))
  have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 ρ] fun z => DirichletCharacter.LFunction ψ z * euler z := by
    filter_upwards [Filter.univ_mem] with z _
    have h := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter (.inl hψ) (s := z)
    rw [χ.changeLevel_primitiveCharacter] at h
    exact h
  have hLψ_an : AnalyticAt ℂ (DirichletCharacter.LFunction ψ) ρ :=
    ((DirichletCharacter.differentiable_LFunction hψ).differentiableOn.analyticOnNhd isOpen_univ) _ (Set.mem_univ _)
  have heuler_an : AnalyticAt ℂ euler ρ := by
    have hdiff : Differentiable ℂ euler := by
      have hgen : ∀ (S : Finset ℕ), (∀ p ∈ S, p.Prime) →
          Differentiable ℂ (fun z : ℂ => ∏ p ∈ S, (1 - ψ (p : ZMod χ.conductor) * (p : ℂ) ^ (-z))) := by
        intro S
        classical
        induction S using Finset.induction_on with
        | empty => intro _; simp only [Finset.prod_empty]; exact differentiable_const _
        | insert a s ha ih =>
          intro hS
          simp_rw [Finset.prod_insert ha]
          have ha_pos : (0 : ℝ) < (a : ℝ) := Nat.cast_pos.mpr (hS a (Finset.mem_insert_self _ _)).pos
          have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha_pos.ne'
          have h1 : Differentiable ℂ (fun z : ℂ => 1 - ψ (a : ZMod χ.conductor) * (a : ℂ) ^ (-z)) := by
            have hrew : (fun z : ℂ => (a : ℂ) ^ (-z)) = fun z => cexp (Complex.log (a : ℂ) * (-z)) :=
              funext fun z => Complex.cpow_def_of_ne_zero haC (-z)
            rw [show (fun z : ℂ => 1 - ψ (a : ZMod χ.conductor) * (a : ℂ) ^ (-z)) =
                fun z => 1 - ψ (a : ZMod χ.conductor) * cexp (Complex.log (a : ℂ) * (-z)) from
                funext fun z => by rw [Complex.cpow_def_of_ne_zero haC (-z)]]
            fun_prop
          exact h1.mul (ih fun p hp => hS p (Finset.mem_insert_of_mem hp))
      exact hgen m.primeFactors fun p hp => Nat.prime_of_mem_primeFactors hp
    exact (hdiff.differentiableOn.analyticOnNhd isOpen_univ) _ (Set.mem_univ _)
  have heuler_ne : euler ρ ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
    have hp_ge2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
    have hlt1 : ‖ψ (p : ZMod χ.conductor) * (p : ℂ) ^ (-ρ)‖ < 1 := by
      rw [norm_mul, ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hp_pos, Complex.neg_re]
      have hpow_lt1 : (p : ℝ) ^ (-ρ.re) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
      calc ‖ψ (p : ZMod χ.conductor)‖ * (p : ℝ) ^ (-ρ.re)
          ≤ 1 * (p : ℝ) ^ (-ρ.re) := mul_le_mul_of_nonneg_right (ψ.norm_le_one _) (Real.rpow_nonneg hp_pos.le _)
        _ < 1 := by linarith
    intro h0'; have h1 : ψ (p : ZMod χ.conductor) * (p : ℂ) ^ (-ρ) = 1 := sub_eq_zero.mp h0' |>.symm
    rw [h1, norm_one] at hlt1; exact lt_irrefl 1 hlt1
  unfold Stage11LinnikBridge.lZeroMult
  have hcongr : analyticOrderAt (DirichletCharacter.LFunction χ) ρ =
      analyticOrderAt (fun z => DirichletCharacter.LFunction ψ z * euler z) ρ :=
    analyticOrderAt_congr hev
  simp only [analyticOrderNatAt, hcongr]
  by_cases htop : analyticOrderAt (DirichletCharacter.LFunction ψ) ρ = ⊤
  · have hfg_top : analyticOrderAt (fun z => DirichletCharacter.LFunction ψ z * euler z) ρ = ⊤ := by
      rw [analyticOrderAt_eq_top] at htop ⊢
      filter_upwards [htop] with z hz; simp [hz]
    simp [htop, hfg_top]
  · obtain ⟨h, hh_an, hh_ne, hh_eq⟩ := hLψ_an.analyticOrderAt_ne_top.mp htop
    have hfg_eq : (fun z => DirichletCharacter.LFunction ψ z * euler z) =ᶠ[𝓝 ρ]
        fun z => (z - ρ) ^ analyticOrderNatAt (DirichletCharacter.LFunction ψ) ρ • (h z * euler z) := by
      filter_upwards [hh_eq] with z hz
      simp only [smul_eq_mul] at hz ⊢; rw [hz]; ring
    have hord : analyticOrderAt (fun z => DirichletCharacter.LFunction ψ z * euler z) ρ =
        (analyticOrderNatAt (DirichletCharacter.LFunction ψ) ρ : ℕ∞) :=
      (hLψ_an.mul heuler_an).analyticOrderAt_eq_natCast.mpr
        ⟨fun z => h z * euler z, hh_an.mul heuler_an, mul_ne_zero hh_ne heuler_ne, hfg_eq⟩
    simp [hord, analyticOrderNatAt]

/-- Helper: elementary `1 / 2 * min 1 u ≤ 1 - exp (-u)` for `u ≥ 0`. -/
private lemma half_min_le_one_sub_exp_neg {u : ℝ} (hu : 0 ≤ u) :
    (1 / 2 : ℝ) * min 1 u ≤ 1 - Real.exp (-u) := by
  have h1 : Real.exp (-u) ≤ 1 / (1 + u) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by linarith) (by linarith [Real.add_one_le_exp u])
  have h2 : u / (1 + u) ≤ 1 - Real.exp (-u) := by
    have hsub : 1 - 1 / (1 + u) = u / (1 + u) := by field_simp [(by linarith : (0 : ℝ) < 1 + u).ne']; ring
    linarith
  rcases le_total u 1 with hle | hge
  · rw [min_eq_right hle]
    have h3 : (1 / 2 : ℝ) * u ≤ u / (1 + u) := by rw [le_div_iff₀ (by linarith)]; nlinarith
    linarith
  · rw [min_eq_left hge]
    have h3 : (1 / 2 : ℝ) * 1 ≤ u / (1 + u) := by rw [le_div_iff₀ (by linarith)]; linarith
    linarith

/-- Helper: `log x ≤ 4 * x ^ (1/4)` for `x ≥ 1`. -/
private lemma log_le_four_rpow_qtr {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ 4 * x ^ (1 / 4 : ℝ) := by
  have h := Real.log_le_rpow_div (by linarith : 0 ≤ x) (by norm_num : (0 : ℝ) < 1 / 4)
  linarith [show x ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) = 4 * x ^ (1 / 4 : ℝ) by ring]

open Classical in
/-- **Shared Explicit-Formula Tail + Left-Half + Error Bound Helper (`ef_nonright_error_le`)**:
for ANY `m ≥ 2`, `Q_all ≥ m`, `T₀ = C_T0 * Q_all^4`, `X ≥ Q_all^20`, bounds the sum over left-half
zeros (`ρ.re < 1/2, |ρ.im| ≤ T₀`), high-`|γ|` tail (`T₀ < |ρ.im| ≤ X^2`), explicit-formula error,
and prime-power error for ANY single character `η : DirichletCharacter ℂ m`! -/
private lemma ef_nonright_error_le
    {C_exp C_tail C_cnt c_S' : ℝ} (hCexp : 0 < C_exp) (hCtail : 0 < C_tail) (hCcnt : 0 < C_cnt) (hcS' : 0 < c_S')
    (hexp : ∀ (m : ℕ) [NeZero m], 2 ≤ m → ∀ (χ : DirichletCharacter ℂ m) (X T : ℝ), 4 ≤ X → 4 ≤ T →
      ‖Stage11LinnikBridge.dyadic2 (Stage4ExplicitFormula.psi1Char χ) X -
          ((if χ = 1 then (1 / 4 : ℂ) * (X : ℂ) ^ 2 else 0) -
            ∑ ρ ∈ Stage11LinnikBridge.lZerosInBox χ T,
              (Stage11LinnikBridge.lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ)‖ ≤
        C_exp * (X ^ 2 * (Real.log ((m : ℝ) * X) + Real.log T) ^ 2 / T + X * Real.log ((m : ℝ) * X)))
    (htail : ∀ (m : ℕ) [NeZero m], 2 ≤ m → ∀ (χ : DirichletCharacter ℂ m) (T₀ T : ℝ), 1 ≤ T₀ → T₀ ≤ T →
      ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox χ T).filter (fun ρ => T₀ < |ρ.im|),
          (Stage11LinnikBridge.lZeroMult χ ρ : ℝ) / (1 + ρ.im ^ 2) ≤
        C_tail * Real.log ((m : ℝ) * (T₀ + 2)) / T₀)
    (hcnt : ∀ (m : ℕ) [NeZero m], 2 ≤ m → ∀ (χ : DirichletCharacter ℂ m) (T : ℝ), 1 ≤ T →
      ∑ ρ ∈ Stage11LinnikBridge.lZerosInBox χ T, (Stage11LinnikBridge.lZeroMult χ ρ : ℝ) ≤
        C_cnt * T * Real.log ((m : ℝ) * (T + 2)))
    {C_T0 : ℝ} (hCT0 : max 16 ((8192 * 128 * C_tail / c_S') ^ 2) ≤ C_T0)
    {m Q_all : ℕ} [NeZero m] (hm : 2 ≤ m) (hmQ : m ≤ Q_all)
    {X : ℝ} (hX_ge : (Q_all : ℝ) ^ (24 : ℝ) ≤ X)
    (hT0_le_X : C_T0 * (Q_all : ℝ) ^ 4 ≤ X)
    (hX_err : (260 * C_exp + 24 + C_cnt * C_T0 * 64) * (Q_all : ℝ) ^ (8 : ℝ) ≤ (c_S' / 4096) * X ^ (1 / 4 : ℝ))
    (η : DirichletCharacter ℂ m) :
    let T₀ : ℝ := C_T0 * (Q_all : ℝ) ^ 4
    ‖Stage11LinnikBridge.dyadic2 (Stage4ExplicitFormula.psi1Char η) X -
        ((if η = 1 then (1 / 4 : ℂ) * (X : ℂ) ^ 2 else 0) -
          ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox η T₀).filter (fun ρ => 1 / 2 ≤ ρ.re),
            (Stage11LinnikBridge.lZeroMult η ρ : ℂ) * (X : ℂ) ^ (ρ + 1) *
              Stage11LinnikBridge.dyadicKernel ρ)‖ ≤
      (c_S' / (1024 * (Q_all : ℝ) ^ 2)) * X ^ 2 := by
  intro T₀
  have hQ2 : (2 : ℝ) ≤ (Q_all : ℝ) := by exact_mod_cast (hm.trans hmQ)
  have hQ0 : (0 : ℝ) < (Q_all : ℝ) := by linarith
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmQ_R : (m : ℝ) ≤ (Q_all : ℝ) := by exact_mod_cast hmQ
  have hCT0_ge16 : 16 ≤ C_T0 := (le_max_left _ _).trans hCT0
  have hCT0_pos : 0 < C_T0 := by linarith
  have hX4 : 4 ≤ X := by
    have h1 : (4 : ℝ) ≤ (Q_all : ℝ) ^ (24 : ℝ) := by
      rw [show (24 : ℝ) = ((24 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact (by norm_num : (4 : ℝ) ≤ 2 ^ 24).trans (pow_le_pow_left₀ (by norm_num) hQ2 24)
    linarith
  have hX0 : 0 < X := by linarith
  have hT0_ge4 : 4 ≤ T₀ := by
    have hQ4 : (16 : ℝ) ≤ (Q_all : ℝ) ^ 4 :=
      (by norm_num : (16 : ℝ) ≤ 2 ^ 4).trans (pow_le_pow_left₀ (by norm_num) hQ2 4)
    dsimp only [T₀]; nlinarith
  set T_big : ℝ := X ^ 2
  have hTbig_ge_T0 : T₀ ≤ T_big := hT0_le_X.trans (by dsimp only [T_big]; nlinarith)
  have hTbig_ge4 : 4 ≤ T_big := by linarith
  have hef := hexp m hm η X T_big hX4 hTbig_ge4
  -- Split `lZerosInBox η T_big` into right-half (`≤ T₀`), left-half (`≤ T₀`), and tail (`> T₀`)
  have hsplit : ∑ ρ ∈ Stage11LinnikBridge.lZerosInBox η T_big,
      (Stage11LinnikBridge.lZeroMult η ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ =
      (∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox η T₀).filter (fun ρ => 1 / 2 ≤ ρ.re),
        (Stage11LinnikBridge.lZeroMult η ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ) +
      (∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox η T₀).filter (fun ρ => ρ.re < 1 / 2),
        (Stage11LinnikBridge.lZeroMult η ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ) +
      (∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox η T_big).filter (fun ρ => T₀ < |ρ.im|),
        (Stage11LinnikBridge.lZeroMult η ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ) := by
    have hdisj1 : Disjoint (Stage11LinnikBridge.lZerosInBox η T₀)
        ((Stage11LinnikBridge.lZerosInBox η T_big).filter (fun ρ => T₀ < |ρ.im|)) := by
      rw [Finset.disjoint_left]; intro ρ h1 h2
      linarith [(Stage11LinnikBridge.mem_lZerosInBox.mp h1).2.2.2, (Finset.mem_filter.mp h2).2]
    have hu1 : Stage11LinnikBridge.lZerosInBox η T₀ ∪
        (Stage11LinnikBridge.lZerosInBox η T_big).filter (fun ρ => T₀ < |ρ.im|) =
        Stage11LinnikBridge.lZerosInBox η T_big := by
      ext ρ; simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (h | ⟨h, _⟩)
        · exact Stage11LinnikBridge.lZerosInBox_mono η hTbig_ge_T0 h
        · exact h
      · intro h; have hm' := Stage11LinnikBridge.mem_lZerosInBox.mp h
        rcases le_or_gt |ρ.im| T₀ with hle | hgt
        · exact Or.inl (Stage11LinnikBridge.mem_lZerosInBox.mpr ⟨hm'.1, hm'.2.1, hm'.2.2.1, hle⟩)
        · exact Or.inr ⟨h, hgt⟩
    have hdisj2 : Disjoint ((Stage11LinnikBridge.lZerosInBox η T₀).filter (fun ρ => 1 / 2 ≤ ρ.re))
        ((Stage11LinnikBridge.lZerosInBox η T₀).filter (fun ρ => ρ.re < 1 / 2)) :=
      Finset.disjoint_filter.mpr fun _ _ h1 h2 => by linarith
    have hu2 : (Stage11LinnikBridge.lZerosInBox η T₀).filter (fun ρ => 1 / 2 ≤ ρ.re) ∪
        (Stage11LinnikBridge.lZerosInBox η T₀).filter (fun ρ => ρ.re < 1 / 2) =
        Stage11LinnikBridge.lZerosInBox η T₀ := by
      ext ρ; simp only [Finset.mem_union, Finset.mem_filter]
      exact ⟨fun h => h.elim And.left And.left, fun h => (le_or_gt (1 / 2 : ℝ) ρ.re).imp (fun h1 => ⟨h, h1⟩) (fun h2 => ⟨h, h2⟩)⟩
    conv_lhs => rw [← hu1, Finset.sum_union hdisj1, ← hu2, Finset.sum_union hdisj2]
  -- (1) High-`|γ|` tail bound: `≤ (c_S' / (4096 * Q_all^2)) * X^2`
  have hTail_bd :
      ‖∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox η T_big).filter (fun ρ => T₀ < |ρ.im|),
          (Stage11LinnikBridge.lZeroMult η ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ‖ ≤
        (c_S' / (4096 * (Q_all : ℝ) ^ 2)) * X ^ 2 := by
    have hpt : ∀ ρ ∈ (Stage11LinnikBridge.lZerosInBox η T_big).filter (fun ρ => T₀ < |ρ.im|),
        ‖(Stage11LinnikBridge.lZeroMult η ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ‖ ≤
          (20 * X ^ 2) * ((Stage11LinnikBridge.lZeroMult η ρ : ℝ) / (1 + ρ.im ^ 2)) := by
      intro ρ hρ
      have hm' := Stage11LinnikBridge.mem_lZerosInBox.mp (Finset.mem_filter.mp hρ).1
      rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hX0]
      have hre : (ρ + 1).re = ρ.re + 1 := by simp
      rw [hre]
      have hX_le : X ^ (ρ.re + 1) ≤ X ^ 2 := by
        rw [show X ^ (2 : ℕ) = X ^ (2 : ℝ) by norm_cast]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [hm'.2.1])
      have hK := Stage11LinnikBridge.norm_dyadicKernel_le_inv_sq (s := ρ) (by linarith [hm'.1]) hm'.2.1.le
      calc (Stage11LinnikBridge.lZeroMult η ρ : ℝ) * X ^ (ρ.re + 1) * ‖Stage11LinnikBridge.dyadicKernel ρ‖
          ≤ (Stage11LinnikBridge.lZeroMult η ρ : ℝ) * X ^ 2 * (20 / (1 + ρ.im ^ 2)) := by gcongr
        _ = (20 * X ^ 2) * ((Stage11LinnikBridge.lZeroMult η ρ : ℝ) / (1 + ρ.im ^ 2)) := by ring
    have hts := htail m hm η T₀ T_big (by linarith) hTbig_ge_T0
    have hlog_le : Real.log ((m : ℝ) * (T₀ + 2)) ≤ 4 * ((Q_all : ℝ) * (T₀ + 2)) ^ (1 / 4 : ℝ) :=
      (Real.log_le_log (by positivity) (by gcongr)).trans (log_le_four_rpow_qtr (by nlinarith))
    have hQT_le : (Q_all : ℝ) * (T₀ + 2) ≤ 2 * C_T0 * (Q_all : ℝ) ^ 5 := by
      have hQ4 : (1 : ℝ) ≤ (Q_all : ℝ) ^ 4 := one_le_pow₀ (by linarith)
      dsimp only [T₀]; nlinarith
    have hlog_sqrt : Real.log ((m : ℝ) * (T₀ + 2)) ≤ 8 * C_T0 ^ (1 / 4 : ℝ) * (Q_all : ℝ) ^ (5 / 4 : ℝ) := by
      have h1 : ((Q_all : ℝ) * (T₀ + 2)) ^ (1 / 4 : ℝ) ≤ (2 * C_T0 * (Q_all : ℝ) ^ 5) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hQT_le (by norm_num)
      have h1_rhs : (2 * C_T0 * (Q_all : ℝ) ^ 5) ^ (1 / 4 : ℝ) =
          (2 : ℝ) ^ (1 / 4 : ℝ) * C_T0 ^ (1 / 4 : ℝ) * (Q_all : ℝ) ^ (5 / 4 : ℝ) := by
        rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by norm_num) hCT0_pos.le,
          show (Q_all : ℝ) ^ (5 : ℕ) = (Q_all : ℝ) ^ (5 : ℝ) by norm_cast,
          ← Real.rpow_mul hQ0.le]
        norm_num
      rw [h1_rhs] at h1
      have h2q : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 :=
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num : (1 / 4 : ℝ) ≤ 1)).trans (Real.rpow_one 2).le
      have hprod : 4 * ((2 : ℝ) ^ (1 / 4 : ℝ) * C_T0 ^ (1 / 4 : ℝ) * (Q_all : ℝ) ^ (5 / 4 : ℝ)) ≤
          8 * C_T0 ^ (1 / 4 : ℝ) * (Q_all : ℝ) ^ (5 / 4 : ℝ) := by
        have hnn : 0 ≤ C_T0 ^ (1 / 4 : ℝ) * (Q_all : ℝ) ^ (5 / 4 : ℝ) := by positivity
        nlinarith
      linarith
    have hdiv_le : 20 * (C_tail * Real.log ((m : ℝ) * (T₀ + 2)) / T₀) ≤ c_S' / (4096 * (Q_all : ℝ) ^ 2) := by
      have hCT_rt : 8192 * 128 * C_tail / c_S' ≤ C_T0 ^ (1 / 2 : ℝ) := by
        have h1 : (8192 * 128 * C_tail / c_S') ^ 2 ≤ C_T0 := (le_max_right _ _).trans hCT0
        rw [← Real.sqrt_eq_rpow]; exact Real.le_sqrt_of_sq_le h1
      have hCT_34 : C_T0 ^ (1 / 2 : ℝ) ≤ C_T0 ^ (3 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      have hQ_pow : (Q_all : ℝ) ^ (2 : ℝ) ≤ (Q_all : ℝ) ^ (11 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      have hfrac : C_T0 ^ (1 / 4 : ℝ) * (Q_all : ℝ) ^ (5 / 4 : ℝ) / (C_T0 * (Q_all : ℝ) ^ 4) =
          1 / (C_T0 ^ (3 / 4 : ℝ) * (Q_all : ℝ) ^ (11 / 4 : ℝ)) := by
        have hC_sp : C_T0 = C_T0 ^ (1 / 4 : ℝ) * C_T0 ^ (3 / 4 : ℝ) := by
          rw [← Real.rpow_add hCT0_pos]; norm_num
        have hQ_sp : (Q_all : ℝ) ^ 4 = (Q_all : ℝ) ^ (5 / 4 : ℝ) * (Q_all : ℝ) ^ (11 / 4 : ℝ) := by
          rw [← Real.rpow_add hQ0, show (5 / 4 : ℝ) + 11 / 4 = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        conv_lhs => rhs; rw [hC_sp, hQ_sp]
        field_simp [(Real.rpow_pos_of_pos hCT0_pos _).ne', (Real.rpow_pos_of_pos hQ0 _).ne']
      calc 20 * (C_tail * Real.log ((m : ℝ) * (T₀ + 2)) / T₀)
          ≤ 20 * (C_tail * (8 * C_T0 ^ (1 / 4 : ℝ) * (Q_all : ℝ) ^ (5 / 4 : ℝ)) / (C_T0 * (Q_all : ℝ) ^ 4)) := by
            dsimp only [T₀]; gcongr
        _ = (160 * C_tail) * (C_T0 ^ (1 / 4 : ℝ) * (Q_all : ℝ) ^ (5 / 4 : ℝ) / (C_T0 * (Q_all : ℝ) ^ 4)) := by ring
        _ = (160 * C_tail) / (C_T0 ^ (3 / 4 : ℝ) * (Q_all : ℝ) ^ (11 / 4 : ℝ)) := by rw [hfrac]; ring
        _ ≤ (160 * C_tail) / ((8192 * 128 * C_tail / c_S') * (Q_all : ℝ) ^ (2 : ℝ)) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity)
              (mul_le_mul (hCT_rt.trans hCT_34) hQ_pow (by positivity) (by positivity))
        _ ≤ c_S' / (4096 * (Q_all : ℝ) ^ 2) := by
            rw [show (Q_all : ℝ) ^ (2 : ℝ) = (Q_all : ℝ) ^ (2 : ℕ) by norm_cast]
            have hEq : (160 * C_tail) / ((8192 * 128 * C_tail / c_S') * (Q_all : ℝ) ^ 2) =
                (160 / 256 : ℝ) * (c_S' / (4096 * (Q_all : ℝ) ^ 2)) := by
              field_simp [hCtail.ne', hcS'.ne', hQ0.ne']; ring
            rw [hEq]
            have : (0 : ℝ) ≤ c_S' / (4096 * (Q_all : ℝ) ^ 2) := by positivity
            linarith
    calc ‖∑ ρ ∈ _, _‖
        ≤ ∑ ρ ∈ _, ‖_‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ _, (20 * X ^ 2) * ((Stage11LinnikBridge.lZeroMult η ρ : ℝ) / (1 + ρ.im ^ 2)) := Finset.sum_le_sum hpt
      _ = (20 * X ^ 2) * ∑ ρ ∈ _, (Stage11LinnikBridge.lZeroMult η ρ : ℝ) / (1 + ρ.im ^ 2) := (Finset.mul_sum _ _ _).symm
      _ ≤ (20 * X ^ 2) * (C_tail * Real.log ((m : ℝ) * (T₀ + 2)) / T₀) := mul_le_mul_of_nonneg_left hts (by positivity)
      _ = (20 * (C_tail * Real.log ((m : ℝ) * (T₀ + 2)) / T₀)) * X ^ 2 := by ring
      _ ≤ (c_S' / (4096 * (Q_all : ℝ) ^ 2)) * X ^ 2 := mul_le_mul_of_nonneg_right hdiv_le (sq_nonneg X)
  -- (2) Left-half zero bound (`ρ.re < 1/2, |ρ.im| ≤ T₀`): `≤ (c_S' / (4096 * Q_all^2)) * X^2`
  have hLeft_bd :
      ‖∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox η T₀).filter (fun ρ => ρ.re < 1 / 2),
          (Stage11LinnikBridge.lZeroMult η ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ‖ ≤
        (c_S' / (4096 * (Q_all : ℝ) ^ 2)) * X ^ 2 := by
    have hpt : ∀ ρ ∈ (Stage11LinnikBridge.lZerosInBox η T₀).filter (fun ρ => ρ.re < 1 / 2),
        ‖(Stage11LinnikBridge.lZeroMult η ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ‖ ≤
          ((1 / 4 : ℝ) * X ^ (3 / 2 : ℝ)) * (Stage11LinnikBridge.lZeroMult η ρ : ℝ) := by
      intro ρ hρ
      obtain ⟨hmem, hlt⟩ := Finset.mem_filter.mp hρ
      have hm' := Stage11LinnikBridge.mem_lZerosInBox.mp hmem
      rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hX0]
      have hre : (ρ + 1).re = ρ.re + 1 := by simp
      rw [hre]
      have hX_le : X ^ (ρ.re + 1) ≤ X ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      have hK := Stage11LinnikBridge.norm_dyadicKernel_le_quarter (s := ρ) (by linarith [hm'.1]) hm'.2.1.le
      calc (Stage11LinnikBridge.lZeroMult η ρ : ℝ) * X ^ (ρ.re + 1) * ‖Stage11LinnikBridge.dyadicKernel ρ‖
          ≤ (Stage11LinnikBridge.lZeroMult η ρ : ℝ) * X ^ (3 / 2 : ℝ) * (1 / 4) := by gcongr
        _ = ((1 / 4 : ℝ) * X ^ (3 / 2 : ℝ)) * (Stage11LinnikBridge.lZeroMult η ρ : ℝ) := by ring
    have hcnt' := hcnt m hm η T₀ (by linarith)
    have hlog_le16 : Real.log ((m : ℝ) * (T₀ + 2)) ≤ 16 * X ^ (1 / 4 : ℝ) := by
      have h1 : (m : ℝ) * (T₀ + 2) ≤ 2 * X ^ 2 := by
        have hmX : (m : ℝ) ≤ X := hmQ_R.trans (
          (Real.rpow_one (Q_all : ℝ)).symm.le.trans
            ((Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num : (1 : ℝ) ≤ 24)).trans hX_ge))
        nlinarith [hT0_le_X]
      calc Real.log ((m : ℝ) * (T₀ + 2)) ≤ Real.log (2 * X ^ 2) := Real.log_le_log (by positivity) h1
        _ = Real.log 2 + 2 * Real.log X := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
        _ ≤ 3 * Real.log X := by linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : (2 : ℝ) ≤ X)]
        _ ≤ 12 * X ^ (1 / 4 : ℝ) := by linarith [log_le_four_rpow_qtr (by linarith : 1 ≤ X)]
        _ ≤ 16 * X ^ (1 / 4 : ℝ) := by linarith [Real.rpow_nonneg hX0.le (1 / 4 : ℝ)]
    have hX_split : X ^ (3 / 2 : ℝ) * X ^ (1 / 4 : ℝ) = X ^ (-(1 / 4 : ℝ)) * X ^ 2 := by
      rw [← Real.rpow_add hX0, ← Real.rpow_two X, ← Real.rpow_add hX0]; congr 1; norm_num
    have hcoeff : 4 * C_cnt * T₀ ≤ (c_S' / (4096 * (Q_all : ℝ) ^ 2)) * X ^ (1 / 4 : ℝ) := by
      have hQ_p : (Q_all : ℝ) ^ 2 * (Q_all : ℝ) ^ 4 ≤ (Q_all : ℝ) ^ (8 : ℝ) := by
        rw [← pow_add, show (Q_all : ℝ) ^ (6 : ℕ) = (Q_all : ℝ) ^ (6 : ℝ) by norm_cast]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      have hmul : (Q_all : ℝ) ^ 2 * (4 * C_cnt * T₀) ≤ (c_S' / 4096) * X ^ (1 / 4 : ℝ) := by
        have h1 : (Q_all : ℝ) ^ 2 * (4 * C_cnt * T₀) = (4 * C_cnt * C_T0) * ((Q_all : ℝ) ^ 2 * (Q_all : ℝ) ^ 4) := by
          dsimp only [T₀]; ring
        rw [h1]
        have h2 : 4 * C_cnt * C_T0 ≤ 260 * C_exp + 24 + C_cnt * C_T0 * 64 := by nlinarith
        exact (mul_le_mul h2 hQ_p (by positivity) (by positivity)).trans hX_err
      have hEq : (c_S' / (4096 * (Q_all : ℝ) ^ 2)) * X ^ (1 / 4 : ℝ) =
          ((c_S' / 4096) * X ^ (1 / 4 : ℝ)) / (Q_all : ℝ) ^ 2 := by field_simp [hQ0.ne']
      rw [hEq, le_div_iff₀ (sq_pos_of_pos hQ0)]; linarith
    calc ‖∑ ρ ∈ _, _‖
        ≤ ∑ ρ ∈ _, ‖_‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ _, ((1 / 4 : ℝ) * X ^ (3 / 2 : ℝ)) * (Stage11LinnikBridge.lZeroMult η ρ : ℝ) := Finset.sum_le_sum hpt
      _ = ((1 / 4 : ℝ) * X ^ (3 / 2 : ℝ)) * ∑ ρ ∈ _, (Stage11LinnikBridge.lZeroMult η ρ : ℝ) := (Finset.mul_sum _ _ _).symm
      _ ≤ ((1 / 4 : ℝ) * X ^ (3 / 2 : ℝ)) * ∑ ρ ∈ Stage11LinnikBridge.lZerosInBox η T₀, (Stage11LinnikBridge.lZeroMult η ρ : ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => Nat.cast_nonneg _) (by positivity)
      _ ≤ ((1 / 4 : ℝ) * X ^ (3 / 2 : ℝ)) * (C_cnt * T₀ * Real.log ((m : ℝ) * (T₀ + 2))) :=
          mul_le_mul_of_nonneg_left hcnt' (by positivity)
      _ ≤ ((1 / 4 : ℝ) * X ^ (3 / 2 : ℝ)) * (C_cnt * T₀ * (16 * X ^ (1 / 4 : ℝ))) := by gcongr
      _ = (4 * C_cnt * T₀) * (X ^ (-(1 / 4 : ℝ)) * X ^ 2) := by rw [← hX_split]; ring
      _ ≤ ((c_S' / (4096 * (Q_all : ℝ) ^ 2)) * X ^ (1 / 4 : ℝ)) * (X ^ (-(1 / 4 : ℝ)) * X ^ 2) := by gcongr
      _ = (c_S' / (4096 * (Q_all : ℝ) ^ 2)) * X ^ 2 := by
          have h1 : X ^ (1 / 4 : ℝ) * X ^ (-(1 / 4 : ℝ)) = 1 := by rw [← Real.rpow_add hX0]; norm_num
          calc _ = (c_S' / (4096 * (Q_all : ℝ) ^ 2)) * (X ^ (1 / 4 : ℝ) * X ^ (-(1 / 4 : ℝ))) * X ^ 2 := by ring
            _ = (c_S' / (4096 * (Q_all : ℝ) ^ 2)) * X ^ 2 := by rw [h1, mul_one]
  -- (3) Explicit-formula error at `T_big = X^2`: `≤ (c_S' / (4096 * Q_all^2)) * X^2`
  have hEF_bd :
      C_exp * (X ^ 2 * (Real.log ((m : ℝ) * X) + Real.log T_big) ^ 2 / T_big + X * Real.log ((m : ℝ) * X)) ≤
        (c_S' / (4096 * (Q_all : ℝ) ^ 2)) * X ^ 2 := by
    have hmX_le : (m : ℝ) * X ≤ X ^ 2 := by
      have hmX : (m : ℝ) ≤ X := hmQ_R.trans (
        (Real.rpow_one (Q_all : ℝ)).symm.le.trans
          ((Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num : (1 : ℝ) ≤ 24)).trans hX_ge))
      nlinarith
    have hlmX : Real.log ((m : ℝ) * X) ≤ 8 * X ^ (1 / 4 : ℝ) := by
      calc Real.log ((m : ℝ) * X) ≤ Real.log (X ^ 2) := Real.log_le_log (by positivity) hmX_le
        _ = 2 * Real.log X := by rw [Real.log_pow]; push_cast; ring
        _ ≤ 8 * X ^ (1 / 4 : ℝ) := by linarith [log_le_four_rpow_qtr (by linarith : 1 ≤ X)]
    have hlTbig : Real.log T_big ≤ 8 * X ^ (1 / 4 : ℝ) := by
      dsimp only [T_big]; rw [Real.log_pow]; push_cast
      linarith [log_le_four_rpow_qtr (by linarith : 1 ≤ X)]
    have hsum_log : Real.log ((m : ℝ) * X) + Real.log T_big ≤ 16 * X ^ (1 / 4 : ℝ) := by linarith
    have hsq_log : (Real.log ((m : ℝ) * X) + Real.log T_big) ^ 2 ≤ 256 * X ^ (1 / 2 : ℝ) := by
      have hnn : 0 ≤ Real.log ((m : ℝ) * X) + Real.log T_big :=
        add_nonneg (Real.log_nonneg (by nlinarith)) (Real.log_nonneg (by linarith))
      have h := pow_le_pow_left₀ hnn hsum_log 2
      rw [mul_pow, ← Real.rpow_natCast (X ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul hX0.le] at h
      norm_num at h; exact h
    have ht1 : X ^ 2 * (Real.log ((m : ℝ) * X) + Real.log T_big) ^ 2 / T_big ≤ 256 * X ^ (-(1 / 4 : ℝ)) * X ^ 2 := by
      have hX12 : X ^ (1 / 2 : ℝ) ≤ X ^ (-(1 / 4 : ℝ)) * X ^ 2 := by
        rw [← Real.rpow_two X, ← Real.rpow_add hX0]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      calc X ^ 2 * (Real.log ((m : ℝ) * X) + Real.log T_big) ^ 2 / T_big
          ≤ X ^ 2 * (256 * X ^ (1 / 2 : ℝ)) / X ^ 2 := by dsimp only [T_big]; gcongr
        _ = 256 * X ^ (1 / 2 : ℝ) := by field_simp [hX0.ne']
        _ ≤ 256 * (X ^ (-(1 / 4 : ℝ)) * X ^ 2) := mul_le_mul_of_nonneg_left hX12 (by norm_num)
        _ = 256 * X ^ (-(1 / 4 : ℝ)) * X ^ 2 := by ring
    have ht2 : X * Real.log ((m : ℝ) * X) ≤ 4 * X ^ (-(1 / 4 : ℝ)) * X ^ 2 := by
      have h1 : X * X ^ (1 / 4 : ℝ) ≤ (1 / 2 : ℝ) * (X ^ (-(1 / 4 : ℝ)) * X ^ 2) := by
        have hX54 : X * X ^ (1 / 4 : ℝ) = X ^ (5 / 4 : ℝ) := by
          conv_lhs => lhs; rw [← Real.rpow_one X]
          rw [← Real.rpow_add hX0]; norm_num
        have hX74 : X ^ (-(1 / 4 : ℝ)) * X ^ 2 = X ^ (7 / 4 : ℝ) := by
          rw [← Real.rpow_two X, ← Real.rpow_add hX0]; norm_num
        have hX12 : (2 : ℝ) ≤ X ^ (1 / 2 : ℝ) := by
          rw [← Real.sqrt_eq_rpow]; exact Real.le_sqrt_of_sq_le (by linarith)
        rw [hX54, hX74]
        have hsp : X ^ (7 / 4 : ℝ) = X ^ (5 / 4 : ℝ) * X ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_add hX0]; norm_num
        rw [hsp]; nlinarith [Real.rpow_nonneg hX0.le (5 / 4 : ℝ)]
      calc X * Real.log ((m : ℝ) * X) ≤ X * (8 * X ^ (1 / 4 : ℝ)) := mul_le_mul_of_nonneg_left hlmX hX0.le
        _ = 8 * (X * X ^ (1 / 4 : ℝ)) := by ring
        _ ≤ 8 * ((1 / 2 : ℝ) * (X ^ (-(1 / 4 : ℝ)) * X ^ 2)) := mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ = 4 * X ^ (-(1 / 4 : ℝ)) * X ^ 2 := by ring
    have hcoeff : 260 * C_exp ≤ (c_S' / (4096 * (Q_all : ℝ) ^ 2)) * X ^ (1 / 4 : ℝ) := by
      have hQ_p : (Q_all : ℝ) ^ 2 ≤ (Q_all : ℝ) ^ (8 : ℝ) := by
        rw [show (Q_all : ℝ) ^ (2 : ℕ) = (Q_all : ℝ) ^ (2 : ℝ) by norm_cast]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      have h1 : (Q_all : ℝ) ^ 2 * (260 * C_exp) ≤ (c_S' / 4096) * X ^ (1 / 4 : ℝ) :=
        calc (Q_all : ℝ) ^ 2 * (260 * C_exp)
            ≤ (260 * C_exp + 24 + C_cnt * C_T0 * 64) * (Q_all : ℝ) ^ (8 : ℝ) := by
              rw [mul_comm]
              exact mul_le_mul (by linarith [show 0 ≤ 24 + C_cnt * C_T0 * 64 by positivity]) hQ_p (by positivity) (by positivity)
          _ ≤ (c_S' / 4096) * X ^ (1 / 4 : ℝ) := hX_err
      have hEq : (c_S' / (4096 * (Q_all : ℝ) ^ 2)) * X ^ (1 / 4 : ℝ) =
          ((c_S' / 4096) * X ^ (1 / 4 : ℝ)) / (Q_all : ℝ) ^ 2 := by field_simp [hQ0.ne']
      rw [hEq, le_div_iff₀ (sq_pos_of_pos hQ0)]; linarith
    calc C_exp * (X ^ 2 * (Real.log ((m : ℝ) * X) + Real.log T_big) ^ 2 / T_big + X * Real.log ((m : ℝ) * X))
        ≤ C_exp * (256 * X ^ (-(1 / 4 : ℝ)) * X ^ 2 + 4 * X ^ (-(1 / 4 : ℝ)) * X ^ 2) :=
          mul_le_mul_of_nonneg_left (add_le_add ht1 ht2) hCexp.le
      _ = (260 * C_exp) * (X ^ (-(1 / 4 : ℝ)) * X ^ 2) := by ring
      _ ≤ ((c_S' / (4096 * (Q_all : ℝ) ^ 2)) * X ^ (1 / 4 : ℝ)) * (X ^ (-(1 / 4 : ℝ)) * X ^ 2) := by gcongr
      _ = (c_S' / (4096 * (Q_all : ℝ) ^ 2)) * X ^ 2 := by
          have h1 : X ^ (1 / 4 : ℝ) * X ^ (-(1 / 4 : ℝ)) = 1 := by rw [← Real.rpow_add hX0]; norm_num
          calc _ = (c_S' / (4096 * (Q_all : ℝ) ^ 2)) * (X ^ (1 / 4 : ℝ) * X ^ (-(1 / 4 : ℝ))) * X ^ 2 := by ring
            _ = (c_S' / (4096 * (Q_all : ℝ) ^ 2)) * X ^ 2 := by rw [h1, mul_one]
  -- Combine (1) + (2) + (3) via triangle inequality
  have hrew :
      Stage11LinnikBridge.dyadic2 (Stage4ExplicitFormula.psi1Char η) X -
        ((if η = 1 then (1 / 4 : ℂ) * (X : ℂ) ^ 2 else 0) -
          ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox η T₀).filter (fun ρ => 1 / 2 ≤ ρ.re),
            (Stage11LinnikBridge.lZeroMult η ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ) =
      (Stage11LinnikBridge.dyadic2 (Stage4ExplicitFormula.psi1Char η) X -
        ((if η = 1 then (1 / 4 : ℂ) * (X : ℂ) ^ 2 else 0) -
          ∑ ρ ∈ Stage11LinnikBridge.lZerosInBox η T_big,
            (Stage11LinnikBridge.lZeroMult η ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ)) -
      (∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox η T₀).filter (fun ρ => ρ.re < 1 / 2),
        (Stage11LinnikBridge.lZeroMult η ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ) -
      (∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox η T_big).filter (fun ρ => T₀ < |ρ.im|),
        (Stage11LinnikBridge.lZeroMult η ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ) := by
    rw [hsplit]; ring
  rw [hrew]
  calc ‖_ - _ - _‖
      ≤ ‖_ - _‖ + ‖∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox η T_big).filter (fun ρ => T₀ < |ρ.im|), _‖ := norm_sub_le _ _
    _ ≤ ‖Stage11LinnikBridge.dyadic2 (Stage4ExplicitFormula.psi1Char η) X - _‖ +
        ‖∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox η T₀).filter (fun ρ => ρ.re < 1 / 2), _‖ +
        ‖∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox η T_big).filter (fun ρ => T₀ < |ρ.im|), _‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ (c_S' / (4096 * (Q_all : ℝ) ^ 2)) * X ^ 2 +
        (c_S' / (4096 * (Q_all : ℝ) ^ 2)) * X ^ 2 +
        (c_S' / (4096 * (Q_all : ℝ) ^ 2)) * X ^ 2 :=
        add_le_add (add_le_add (hef.trans hEF_bd) hLeft_bd) hTail_bd
    _ ≤ (c_S' / (1024 * (Q_all : ℝ) ^ 2)) * X ^ 2 := by
        have : 0 ≤ (c_S' / (4096 * (Q_all : ℝ) ^ 2)) * X ^ 2 := by positivity
        have h4 : (c_S' / (1024 * (Q_all : ℝ) ^ 2)) * X ^ 2 = 4 * ((c_S' / (4096 * (Q_all : ℝ) ^ 2)) * X ^ 2) := by
          field_simp [hQ0.ne']; ring
        linarith

/-- Classical zero-free gap for any character `η mod m` (`m ≤ Q_all`) with no real zero in
`(1 - δ / L_M, 1)`. -/
private lemma zero_re_gap_of_no_real_zero
    {c_ζ δ : ℝ} (hcζ : 0 < c_ζ) (hδ0 : 0 < δ) (hδ60k : δ ≤ 1 / 60000) (hδζ : δ ≤ c_ζ)
    (hzf_ζ : ∀ s : ℂ, 1 - c_ζ / Real.log (|s.im| + 2) ≤ s.re → s ≠ 1 → riemannZeta s ≠ 0)
    {m Q_all : ℕ} [NeZero m] (hm : 2 ≤ m) (hmQ : m ≤ Q_all) {T₀ : ℝ} (hT₀ : 4 ≤ T₀)
    {η : DirichletCharacter ℂ m}
    (hno_real : ∀ β : ℝ, 1 - δ / Real.log ((Q_all : ℝ) * (T₀ + 2)) < β → β < 1 →
      DirichletCharacter.LFunction η (β : ℂ) ≠ 0)
    {ρ : ℂ} (hρ : ρ ∈ Stage11LinnikBridge.lZerosInBox η T₀) :
    δ / Real.log ((Q_all : ℝ) * (T₀ + 2)) ≤ 1 - ρ.re := by
  have hm' := Stage11LinnikBridge.mem_lZerosInBox.mp hρ
  have hQ2 : (2 : ℝ) ≤ (Q_all : ℝ) := by exact_mod_cast (hm.trans hmQ)
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmQ_R : (m : ℝ) ≤ (Q_all : ℝ) := by exact_mod_cast hmQ
  set L_M := Real.log ((Q_all : ℝ) * (T₀ + 2))
  have hLM_pos : 0 < L_M := Real.log_pos (by nlinarith)
  have hlog_pos : 0 < Real.log ((m : ℝ) * (|ρ.im| + 2)) :=
    Real.log_pos (by nlinarith [abs_nonneg ρ.im])
  have hlog_le : Real.log ((m : ℝ) * (|ρ.im| + 2)) ≤ L_M :=
    Real.log_le_log (by positivity) (mul_le_mul hmQ_R (by linarith [hm'.2.2.2]) (by linarith [abs_nonneg ρ.im]) (by linarith))
  by_cases hη1 : η = 1
  · subst hη1
    have hρ_ne1 : ρ ≠ 1 := fun h => by subst h; simp at hm'
    have hζ0 := (RHDirect.LFunction_trivChar_eq_zero_iff_riemannZeta_of_re_pos (N := m) hm'.1 hρ_ne1).mp hm'.2.2.1
    have hlogρ_pos : 0 < Real.log (|ρ.im| + 2) := Real.log_pos (by linarith [abs_nonneg ρ.im])
    have hlogρ_le : Real.log (|ρ.im| + 2) ≤ L_M :=
      Real.log_le_log (by linarith [abs_nonneg ρ.im]) (by nlinarith [hm'.2.2.2, abs_nonneg ρ.im])
    have hlt : ρ.re < 1 - c_ζ / Real.log (|ρ.im| + 2) := by
      by_contra hge; push Not at hge; exact hzf_ζ ρ hge hρ_ne1 hζ0
    have hdiv : δ / L_M ≤ c_ζ / Real.log (|ρ.im| + 2) :=
      (div_le_div_of_nonneg_right hδζ hLM_pos.le).trans (div_le_div_of_nonneg_left hcζ.le hlogρ_pos hlogρ_le)
    linarith
  · by_cases hη2 : η ^ 2 ≠ 1
    · have hlt : ρ.re < 1 - 1 / (14000 * Real.log ((m : ℝ) * (|ρ.im| + 2))) := by
        by_contra hge; push Not at hge
        exact Stage5ZetaZeroFree.LFunction_complex_char_deLaValleePoussin_zeroFree η hη2 hge hm'.2.2.1
      have hdiv : δ / L_M ≤ 1 / (14000 * Real.log ((m : ℝ) * (|ρ.im| + 2))) := by
        calc δ / L_M ≤ (1 / 14000 : ℝ) / L_M := div_le_div_of_nonneg_right (hδ60k.trans (by norm_num)) hLM_pos.le
          _ ≤ (1 / 14000 : ℝ) / Real.log ((m : ℝ) * (|ρ.im| + 2)) := div_le_div_of_nonneg_left (by norm_num) hlog_pos hlog_le
          _ = 1 / (14000 * Real.log ((m : ℝ) * (|ρ.im| + 2))) := by ring
      linarith
    · push Not at hη2
      by_cases him : ρ.im ≠ 0
      · have hlt : ρ.re < 1 - 1 / (60000 * Real.log ((m : ℝ) * (|ρ.im| + 2))) := by
          by_contra hge; push Not at hge
          exact Stage8UniformAP.LFunction_real_char_nonreal_zeroFree hη1 hη2 him hge hm'.2.2.1
        have hdiv : δ / L_M ≤ 1 / (60000 * Real.log ((m : ℝ) * (|ρ.im| + 2))) := by
          calc δ / L_M ≤ (1 / 60000 : ℝ) / L_M := div_le_div_of_nonneg_right hδ60k hLM_pos.le
            _ ≤ (1 / 60000 : ℝ) / Real.log ((m : ℝ) * (|ρ.im| + 2)) := div_le_div_of_nonneg_left (by norm_num) hlog_pos hlog_le
            _ = 1 / (60000 * Real.log ((m : ℝ) * (|ρ.im| + 2))) := by ring
        linarith
      · push Not at him
        have hρ_eq : ρ = (ρ.re : ℂ) := Complex.ext rfl (by simp [him])
        by_contra hlt; push Not at hlt
        exact hno_real ρ.re (by linarith) hm'.2.1 (hρ_eq ▸ hm'.2.2.1)

/-- Helper: if `s ∣ f`, `f ∣ m₀ * s`, `Squarefree s`, and `Coprime s m₀`, then
`∏ p ∈ f.primeFactors.filter (fun p => ¬ p ∣ m₀), p = s`. -/
private lemma prod_primeFactors_not_dvd_eq_of_dvd_mul {m₀ s f : ℕ}
    (hs_sqf : Squarefree s) (hcop : Nat.Coprime s m₀) (hsf : s ∣ f) (hfm : f ∣ m₀ * s) (hf0 : f ≠ 0) :
    ∏ p ∈ f.primeFactors.filter (fun p => ¬ p ∣ m₀), p = s := by
  have heq_set : f.primeFactors.filter (fun p => ¬ p ∣ m₀) = s.primeFactors := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hp, hpf, _⟩, hnotm⟩
      have hps : p ∣ s := (hp.dvd_mul.mp (hpf.trans hfm)).resolve_left hnotm
      have hs0 : s ≠ 0 := fun h0 => by subst h0; exact hs_sqf.ne_zero rfl
      exact ⟨hp, hps, hs0⟩
    · rintro ⟨hp, hps, _⟩
      have hnotm : ¬ p ∣ m₀ := fun hpm =>
        hp.not_isUnit (Nat.isUnit_iff.mpr (Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd hps hpm)))
      exact ⟨⟨hp, hps.trans hsf, hf0⟩, hnotm⟩
  rw [heq_set]
  exact Nat.prod_primeFactors_of_squarefree hs_sqf

/-- Helper: at modulus `m`, `Fintype.card (DirichletCharacter ℂ m) = m.totient`. -/
private lemma card_dirichletChar_eq_totient (m : ℕ) [NeZero m] :
    (Fintype.card (DirichletCharacter ℂ m) : ℝ) = (m.totient : ℝ) := by
  have horth := Stage2DirichletAP.char_orthogonality_indicator_nat (q := m) (a := 1) (Nat.coprime_one_left m) 1
  simp only [Nat.ModEq.refl, ↓reduceIte, Nat.cast_one, map_one, mul_one, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at horth
  have htot_ne : (m.totient : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (NeZero.pos m)).ne'
  have hC : (Fintype.card (DirichletCharacter ℂ m) : ℂ) = (m.totient : ℂ) := by
    have h := congrArg (fun z : ℂ => (m.totient : ℂ) * z) horth
    rw [← mul_assoc, mul_inv_cancel₀ htot_ne, one_mul, mul_one] at h
    exact h
  have hre := congrArg Complex.re hC
  simpa using hre

/-- Helper: right-half zero sum bound for the twisted character sum `∑_{χ mod m₀} conj(χ a₀) * ∑_{ρ} ...`
given a uniform gap `lam₀ / L_M ≤ 1 - ρ.re` for every right-half zero of every `twistedChar χ χ_s`! -/
private lemma norm_twisted_right_half_le_of_logfree
    {C_D A : ℝ} (hCD : 0 < C_D) (hA : 1 ≤ A)
    (hLF : ∀ (m : ℕ) [NeZero m], 2 ≤ m → ∀ σ T : ℝ, 1 / 2 ≤ σ → σ ≤ 1 → 1 ≤ T →
      (Stage11LinnikBridge.dirichletZeroBoxCount m σ T : ℝ) ≤ C_D * ((m : ℝ) * (T + 2)) ^ (A * (1 - σ)))
    {m₀ a₀ s : ℕ} [NeZero m₀] [NeZero s] (hm₀ : 2 ≤ m₀) (hcop_ms : Nat.Coprime m₀ s) (hs_odd : Odd s)
    {T₀ X lam₀ : ℝ} (hT₀ : 1 ≤ T₀) (hX : 4 ≤ X) (hlam₀ : 0 ≤ lam₀)
    (hgap : ∀ (χ : DirichletCharacter ℂ m₀) (ρ : ℂ),
      ρ ∈ Stage11LinnikBridge.lZerosInBox (Stage11SecondMomentFrame.twistedChar χ (quadCharOfOddSqf s hs_odd)) T₀ →
      1 / 2 ≤ ρ.re →
      lam₀ / Real.log (((m₀ * s : ℕ) : ℝ) * (T₀ + 2)) ≤ 1 - ρ.re)
    (hR : max (2 * A) 2 ≤ Real.log X / Real.log (((m₀ * s : ℕ) : ℝ) * (T₀ + 2))) :
    ‖∑ χ : DirichletCharacter ℂ m₀,
        starRingEnd ℂ (χ (a₀ : ZMod m₀)) *
          ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox
              (Stage11SecondMomentFrame.twistedChar χ (quadCharOfOddSqf s hs_odd)) T₀).filter (fun ρ => 1 / 2 ≤ ρ.re),
            (Stage11LinnikBridge.lZeroMult
              (Stage11SecondMomentFrame.twistedChar χ (quadCharOfOddSqf s hs_odd)) ρ : ℂ) *
              (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ‖ ≤
      ((1 / 2 : ℝ) * C_D * Real.exp A *
        Real.exp (-(Real.log X / Real.log (((m₀ * s : ℕ) : ℝ) * (T₀ + 2)) / 2) * lam₀)) * X ^ 2 := by
  classical
  have hX0 : 0 < X := by linarith
  have hs_pos : 1 ≤ s := NeZero.pos s
  have hm_ge2 : 2 ≤ m₀ * s := by nlinarith
  set χ_s := quadCharOfOddSqf s hs_odd
  let emb : DirichletCharacter ℂ m₀ → DirichletCharacter ℂ (m₀ * s) :=
    fun χ => Stage11SecondMomentFrame.twistedChar χ χ_s
  have hemb_inj : Function.Injective emb := twistedChar_injective_left hcop_ms χ_s
  let bad : DirichletCharacter ℂ (m₀ * s) → ℂ → Prop := fun η _ => ∃ χ : DirichletCharacter ℂ m₀, emb χ = η
  have hbad_gap : ∀ (η : DirichletCharacter ℂ (m₀ * s)) (ρ : ℂ),
      ρ ∈ Stage11LinnikBridge.lZerosInBox η T₀ → 1 / 2 ≤ ρ.re → bad η ρ →
      lam₀ / Real.log (((m₀ * s : ℕ) : ℝ) * (T₀ + 2)) ≤ 1 - ρ.re := by
    rintro η ρ hρ hre ⟨χ, rfl⟩
    exact hgap χ ρ hρ hre
  have hlf_bd := Stage11LinnikBridge.sum_right_half_zeros_le_of_logfree hCD hA hLF hm_ge2 hT₀ hX hlam₀ bad hbad_gap hR
  have hterm : ∀ χ : DirichletCharacter ℂ m₀,
      ‖starRingEnd ℂ (χ (a₀ : ZMod m₀)) *
        ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox (emb χ) T₀).filter (fun ρ => 1 / 2 ≤ ρ.re),
          (Stage11LinnikBridge.lZeroMult (emb χ) ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ‖ ≤
      ((1 / 4 : ℝ) * X ^ 2) *
        ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox (emb χ) T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ bad (emb χ) ρ),
          (Stage11LinnikBridge.lZeroMult (emb χ) ρ : ℝ) * X ^ (ρ.re - 1) := by
    intro χ
    have hfilt : (Stage11LinnikBridge.lZerosInBox (emb χ) T₀).filter (fun ρ => 1 / 2 ≤ ρ.re) =
        (Stage11LinnikBridge.lZerosInBox (emb χ) T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ bad (emb χ) ρ) := by
      ext ρ; simp only [Finset.mem_filter, bad]; exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2, χ, rfl⟩, fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩⟩
    rw [norm_mul, Complex.norm_conj, hfilt]
    have hsum_le :
        ‖∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox (emb χ) T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ bad (emb χ) ρ),
            (Stage11LinnikBridge.lZeroMult (emb χ) ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ‖ ≤
        ((1 / 4 : ℝ) * X ^ 2) *
          ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox (emb χ) T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ bad (emb χ) ρ),
            (Stage11LinnikBridge.lZeroMult (emb χ) ρ : ℝ) * X ^ (ρ.re - 1) := by
      rw [Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
      have hm' := Stage11LinnikBridge.mem_lZerosInBox.mp (Finset.mem_filter.mp hρ).1
      rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hX0]
      have hre : (ρ + 1).re = ρ.re + 1 := by simp
      rw [hre]
      have hX_sp : X ^ (ρ.re + 1) = X ^ 2 * X ^ (ρ.re - 1) := by
        rw [← Real.rpow_two X, ← Real.rpow_add hX0]; congr 1; ring
      have hK := Stage11LinnikBridge.norm_dyadicKernel_le_quarter (s := ρ) (by linarith [hm'.1]) hm'.2.1.le
      rw [hX_sp]
      calc (Stage11LinnikBridge.lZeroMult (emb χ) ρ : ℝ) * (X ^ 2 * X ^ (ρ.re - 1)) * ‖Stage11LinnikBridge.dyadicKernel ρ‖
          ≤ (Stage11LinnikBridge.lZeroMult (emb χ) ρ : ℝ) * (X ^ 2 * X ^ (ρ.re - 1)) * (1 / 4) := by gcongr
        _ = ((1 / 4 : ℝ) * X ^ 2) * ((Stage11LinnikBridge.lZeroMult (emb χ) ρ : ℝ) * X ^ (ρ.re - 1)) := by ring
    exact (mul_le_mul (χ.norm_le_one _) hsum_le (norm_nonneg _) zero_le_one).trans (by rw [one_mul])
  have hsum_emb :
      ∑ χ : DirichletCharacter ℂ m₀,
        ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox (emb χ) T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ bad (emb χ) ρ),
          (Stage11LinnikBridge.lZeroMult (emb χ) ρ : ℝ) * X ^ (ρ.re - 1) ≤
      ∑ η : DirichletCharacter ℂ (m₀ * s),
        ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox η T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ bad η ρ),
          (Stage11LinnikBridge.lZeroMult η ρ : ℝ) * X ^ (ρ.re - 1) := by
    rw [← Finset.sum_image (f := fun η : DirichletCharacter ℂ (m₀ * s) =>
      ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox η T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ bad η ρ),
        (Stage11LinnikBridge.lZeroMult η ρ : ℝ) * X ^ (ρ.re - 1))
      (fun x _ y _ h => hemb_inj h)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ =>
      Finset.sum_nonneg fun _ _ => by positivity
  calc ‖∑ χ : DirichletCharacter ℂ m₀, _‖
      ≤ ∑ χ : DirichletCharacter ℂ m₀, ‖_‖ := norm_sum_le _ _
    _ ≤ ∑ χ : DirichletCharacter ℂ m₀, ((1 / 4 : ℝ) * X ^ 2) * _ := Finset.sum_le_sum fun χ _ => hterm χ
    _ = ((1 / 4 : ℝ) * X ^ 2) * ∑ χ : DirichletCharacter ℂ m₀, _ := (Finset.mul_sum _ _ _).symm
    _ ≤ ((1 / 4 : ℝ) * X ^ 2) * ∑ η : DirichletCharacter ℂ (m₀ * s), _ :=
        mul_le_mul_of_nonneg_left hsum_emb (by positivity)
    _ ≤ ((1 / 4 : ℝ) * X ^ 2) *
          (2 * C_D * Real.exp A * Real.exp (-(Real.log X / Real.log (((m₀ * s : ℕ) : ℝ) * (T₀ + 2)) / 2) * lam₀)) :=
        mul_le_mul_of_nonneg_left hlf_bd (by positivity)
    _ = ((1 / 2 : ℝ) * C_D * Real.exp A *
          Real.exp (-(Real.log X / Real.log (((m₀ * s : ℕ) : ℝ) * (T₀ + 2)) / 2) * lam₀)) * X ^ 2 := by ring

/-- Helper: Deuring–Heilbronn exponential decay `(1 / 2) C_D exp(A) * exp(-(R/2) * c₁ * log(c₂/λ)) ≤ (1 / (64 Z^2)) * min 1 (R * λ)`
when `0 < λ < δ_L ≤ c₂ / 4` and `R ≥ max R_c2 (16 / c₁) * (Real.log Z + 1)`. -/
private lemma dh_exp_decay_le {C_D A c₁ c₂ B_rt Z R lam : ℝ}
    (hCD : 0 < C_D) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hZ4 : 4 ≤ Z)
    (hBrt : 256 * C_D * Real.exp A * (1 + 2 / c₂) ≤ B_rt) (hBrt1 : 1 ≤ B_rt)
    (hlam0 : 0 < lam) (hlam_hi : lam ≤ c₂ / 4)
    (hR_c2 : ((4 / c₁) * (4 + Real.log (2 * B_rt) / Real.log 2)) * (Real.log Z + 1) ≤ R)
    (_hR_16 : (16 / c₁) * (Real.log Z + 1) ≤ R) (hR_ge1 : 1 ≤ R) :
    (1 / 2 : ℝ) * C_D * Real.exp A * Real.exp (-(R / 2) * (c₁ * Real.log (c₂ / lam))) ≤
      (1 / (64 * Z ^ 2)) * min 1 (R * lam) := by
  have hZ0 : 0 < Z := by linarith
  have hLZ_pos : 0 < Real.log Z := Real.log_pos (by linarith)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hu_pos : 0 < lam / c₂ := by positivity
  have hu_le : lam / c₂ ≤ 1 / 4 := by rw [div_le_iff₀ hc₂]; linarith
  have hc2_div : c₂ / lam = (lam / c₂)⁻¹ := by field_simp [hlam0.ne', hc₂.ne']
  have hpow_eq : Real.exp (-(R / 2) * (c₁ * Real.log (c₂ / lam))) = (lam / c₂) ^ (c₁ * R / 2) := by
    rw [Real.rpow_def_of_pos hu_pos, hc2_div, Real.log_inv]; congr 1; ring
  rw [hpow_eq]
  have hexp_ge : 2 + 2 * Real.log Z / Real.log 2 + Real.log (2 * B_rt) / Real.log 2 ≤ c₁ * R / 2 := by
    have h1 := mul_le_mul_of_nonneg_left hR_c2 (by positivity : 0 ≤ c₁ / 2)
    have hsimp : (c₁ / 2) * (((4 / c₁) * (4 + Real.log (2 * B_rt) / Real.log 2)) * (Real.log Z + 1)) =
        2 * (4 + Real.log (2 * B_rt) / Real.log 2) * (Real.log Z + 1) := by
      field_simp [hc₁.ne']; ring
    rw [hsimp] at h1
    have hnn1 : 0 ≤ Real.log (2 * B_rt) / Real.log 2 := div_nonneg (Real.log_nonneg (by linarith)) hlog2_pos.le
    have h2logZ : 2 * Real.log Z / Real.log 2 ≤ 4 * Real.log Z := by
      have hlog2_gt : (1 / 2 : ℝ) ≤ Real.log 2 := by
        have : Real.exp (1 / 2 : ℝ) ≤ 2 := by
          have h1' : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
            rw [sq, ← Real.exp_add]; norm_num
          have h2' : Real.exp (1 / 2 : ℝ) ^ 2 ≤ 2 ^ 2 := by linarith [Real.exp_one_lt_d9]
          exact le_of_sq_le_sq h2' (by norm_num)
        exact (Real.log_exp (1 / 2 : ℝ)).symm.trans_le (Real.log_le_log (Real.exp_pos _) this)
      rw [div_le_iff₀ hlog2_pos]; nlinarith
    nlinarith
  have hexp_ge1 : 1 ≤ c₁ * R / 2 := by
    have : 0 ≤ 2 * Real.log Z / Real.log 2 + Real.log (2 * B_rt) / Real.log 2 :=
      add_nonneg (div_nonneg (by linarith) hlog2_pos.le) (div_nonneg (Real.log_nonneg (by linarith)) hlog2_pos.le)
    linarith
  have hsplit : (lam / c₂) ^ (c₁ * R / 2) = (lam / c₂) * (lam / c₂) ^ (c₁ * R / 2 - 1) := by
    conv_lhs => rw [show c₁ * R / 2 = 1 + (c₁ * R / 2 - 1) by ring]
    rw [Real.rpow_add hu_pos, Real.rpow_one]
  have htail_pow : (lam / c₂) ^ (c₁ * R / 2 - 1) ≤ 1 / (2 * B_rt * Z ^ 2) := by
    have h1 : (lam / c₂) ^ (c₁ * R / 2 - 1) ≤ (1 / 2 : ℝ) ^ (c₁ * R / 2 - 1) :=
      Real.rpow_le_rpow hu_pos.le (by linarith) (by linarith)
    have h2 : (1 / 2 : ℝ) ^ (c₁ * R / 2 - 1) ≤ (1 / 2 : ℝ) ^ (2 * Real.log Z / Real.log 2 + Real.log (2 * B_rt) / Real.log 2) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
    have h3 : (1 / 2 : ℝ) ^ (2 * Real.log Z / Real.log 2 + Real.log (2 * B_rt) / Real.log 2) = 1 / (2 * B_rt * Z ^ 2) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 2), one_div, Real.log_inv]
      have hmul : -Real.log 2 * (2 * Real.log Z / Real.log 2 + Real.log (2 * B_rt) / Real.log 2) =
          -(Real.log (2 * B_rt * Z ^ 2)) := by
        conv_rhs => rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
        push_cast; field_simp [hlog2_pos.ne']; ring
      rw [hmul, Real.exp_neg, Real.exp_log (by positivity), one_div]
    exact (h1.trans h2).trans h3.le
  have hlam_min : lam / c₂ ≤ (1 + 2 / c₂) * min 1 (R * lam) := by
    rcases le_total 1 (R * lam) with hge | hle
    · rw [min_eq_left hge, mul_one]
      have : 0 ≤ 2 / c₂ := by positivity
      linarith
    · rw [min_eq_right hle]
      have h1 : lam ≤ R * lam := le_mul_of_one_le_left hlam0.le hR_ge1
      have h2 : lam / c₂ = (1 / c₂) * lam := by ring
      have hc2_inv : 1 / c₂ ≤ 1 + 2 / c₂ := by
        have h2c : 2 / c₂ = 2 * (1 / c₂) := by ring
        linarith [show (0 : ℝ) < 1 / c₂ by positivity]
      have h3 : (1 / c₂) * lam ≤ (1 + 2 / c₂) * (R * lam) :=
        mul_le_mul hc2_inv h1 hlam0.le (by positivity)
      linarith
  calc (1 / 2 : ℝ) * C_D * Real.exp A * ((lam / c₂) ^ (c₁ * R / 2))
      = (1 / 2 : ℝ) * C_D * Real.exp A * ((lam / c₂) * (lam / c₂) ^ (c₁ * R / 2 - 1)) := by rw [hsplit]
    _ ≤ (1 / 2 : ℝ) * C_D * Real.exp A * (((1 + 2 / c₂) * min 1 (R * lam)) * (1 / (2 * B_rt * Z ^ 2))) := by
        have hmin_nn : 0 ≤ min 1 (R * lam) := le_min zero_le_one (by positivity)
        have hmul := mul_le_mul hlam_min htail_pow (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hmul (by positivity)
    _ = ((1 / 2 : ℝ) * C_D * Real.exp A * (1 + 2 / c₂) / (2 * B_rt)) * ((1 / Z ^ 2) * min 1 (R * lam)) := by ring
    _ ≤ (1 / 64 : ℝ) * ((1 / Z ^ 2) * min 1 (R * lam)) := by
        have hmin_nn : 0 ≤ (1 / Z ^ 2) * min 1 (R * lam) := mul_nonneg (by positivity) (le_min zero_le_one (by positivity))
        refine mul_le_mul_of_nonneg_right ?_ hmin_nn
        rw [div_le_iff₀ (by positivity)]; linarith
    _ = (1 / (64 * Z ^ 2)) * min 1 (R * lam) := by ring

/-- Helper: given `dyadic2Real (psi1AP m₀ a₀) X` approximated to within `E` by `main`, deduce `W ≥ main - E - NP`. -/
private lemma tentWt_apPrimes_ge_sub_nonprime {m₀ a₀ : ℕ} {X : ℝ} (hX : 1 ≤ X) :
    Stage11LinnikBridge.dyadic2Real (Stage11LinnikBridge.psi1AP m₀ a₀) X -
      3 * X * Real.sqrt (2 * X) * (Real.log (2 * X) + 2) ≤
      ∑ r ∈ apPrimes m₀ a₀ X, tentWt X r := by
  rw [dyadic2Real_psi1AP_eq_sum_tentWt m₀ a₀ (by linarith)]
  set S := (Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter (fun n => n ≡ a₀ [MOD m₀])
  have hsplit : S = apPrimes m₀ a₀ X ∪ S.filter (fun n => ¬ n.Prime) := by
    ext n; simp only [S, apPrimes, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hp : n.Prime
      · exact Or.inl ⟨h1, hp, h2⟩
      · exact Or.inr ⟨⟨h1, h2⟩, hp⟩
    · rintro (⟨h1, _, h2⟩ | ⟨⟨h1, h2⟩, _⟩) <;> exact ⟨h1, h2⟩
  have hdisj : Disjoint (apPrimes m₀ a₀ X) (S.filter (fun n => ¬ n.Prime)) := by
    rw [Finset.disjoint_left]; intro n h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2.1
  have hnp_le : ∑ n ∈ S.filter (fun n => ¬ n.Prime), tentWt X n ≤
      3 * X * Real.sqrt (2 * X) * (Real.log (2 * X) + 2) := by
    have hsub : S.filter (fun n => ¬ n.Prime) ⊆ (Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter (fun n => ¬ n.Prime) :=
      fun n hn => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1, (Finset.mem_filter.mp hn).2⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => tentWt_nonneg (by linarith) n).trans
      (sum_tentWt_nonprime_le hX)
  rw [hsplit, Finset.sum_union hdisj]; linarith

/-- Helper: difference between the prime-restricted twisted tent sum and the full character sum is
bounded by the non-prime tent sum `3 * X * √(2 X) * (log (2 X) + 2)`. -/
private lemma abs_tentWt_twist_sub_char_sum_le {m₀ a₀ s : ℕ} [NeZero m₀] [NeZero s]
    (hcop_am : Nat.Coprime a₀ m₀) (hcop_ms : Nat.Coprime m₀ s) (hs_odd : Odd s) {X : ℝ} (hX : 1 ≤ X) :
    |∑ r ∈ apPrimes m₀ a₀ X, tentWt X r * (jacobiSym (r : ℤ) s : ℝ)| ≤
      ‖(m₀.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ m₀,
          starRingEnd ℂ (χ (a₀ : ZMod m₀)) *
            Stage11LinnikBridge.dyadic2
              (Stage4ExplicitFormula.psi1Char
                (Stage11SecondMomentFrame.twistedChar χ (quadCharOfOddSqf s hs_odd))) X‖ +
      3 * X * Real.sqrt (2 * X) * (Real.log (2 * X) + 2) := by
  rw [dyadic2_psi1Char_twisted_eq_sum_tentWt hcop_am hcop_ms hs_odd (by linarith)]
  set S := (Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter (fun n => n ≡ a₀ [MOD m₀])
  have hsplit : S = apPrimes m₀ a₀ X ∪ S.filter (fun n => ¬ n.Prime) := by
    ext n; simp only [S, apPrimes, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hp : n.Prime
      · exact Or.inl ⟨h1, hp, h2⟩
      · exact Or.inr ⟨⟨h1, h2⟩, hp⟩
    · rintro (⟨h1, _, h2⟩ | ⟨⟨h1, h2⟩, _⟩) <;> exact ⟨h1, h2⟩
  have hdisj : Disjoint (apPrimes m₀ a₀ X) (S.filter (fun n => ¬ n.Prime)) := by
    rw [Finset.disjoint_left]; intro n h1 h2
    exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2.1
  have hcast :
      ((∑ r ∈ apPrimes m₀ a₀ X, tentWt X r * (jacobiSym (r : ℤ) s : ℝ) : ℝ) : ℂ) =
        (∑ n ∈ S, (tentWt X n : ℂ) * ((jacobiSym (n : ℤ) s : ℤ) : ℂ)) -
        (∑ n ∈ S.filter (fun n => ¬ n.Prime), (tentWt X n : ℂ) * ((jacobiSym (n : ℤ) s : ℤ) : ℂ)) := by
    conv_rhs => lhs; rw [hsplit, Finset.sum_union hdisj]
    rw [add_sub_cancel_right, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun n _ => by push_cast; rfl
  have hnp_norm :
      ‖∑ n ∈ S.filter (fun n => ¬ n.Prime), (tentWt X n : ℂ) * ((jacobiSym (n : ℤ) s : ℤ) : ℂ)‖ ≤
        3 * X * Real.sqrt (2 * X) * (Real.log (2 * X) + 2) := by
    have hsub : S.filter (fun n => ¬ n.Prime) ⊆ (Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter (fun n => ¬ n.Prime) :=
      fun n hn => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1, (Finset.mem_filter.mp hn).2⟩
    calc ‖∑ n ∈ S.filter (fun n => ¬ n.Prime), _‖
        ≤ ∑ n ∈ S.filter (fun n => ¬ n.Prime), ‖(tentWt X n : ℂ) * ((jacobiSym (n : ℤ) s : ℤ) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ S.filter (fun n => ¬ n.Prime), tentWt X n := Finset.sum_le_sum fun n _ => by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (tentWt_nonneg (by linarith) n), Complex.norm_intCast]
          have hj1 : |(jacobiSym (n : ℤ) s : ℝ)| ≤ 1 := by
            have h1 : |jacobiSym (n : ℤ) s| ≤ 1 := by
              rcases jacobiSym.trichotomy (n : ℤ) s with h | h | h <;> rw [h] <;> norm_num
            exact_mod_cast h1
          exact mul_le_of_le_one_right (tentWt_nonneg (by linarith) n) hj1
      _ ≤ ∑ n ∈ (Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter (fun n => ¬ n.Prime), tentWt X n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => tentWt_nonneg (by linarith) n
      _ ≤ 3 * X * Real.sqrt (2 * X) * (Real.log (2 * X) + 2) := sum_tentWt_nonprime_le hX
  have habs : |∑ r ∈ apPrimes m₀ a₀ X, tentWt X r * (jacobiSym (r : ℤ) s : ℝ)| =
      ‖((∑ r ∈ apPrimes m₀ a₀ X, tentWt X r * (jacobiSym (r : ℤ) s : ℝ) : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [habs, hcast]
  exact (norm_sub_le _ _).trans (add_le_add le_rfl hnp_norm)

/-- Helper: right-half zero-sum bound for any predicate `P_bad` on `DirichletCharacter ℂ m₀ × ℂ`. -/
private lemma re_sum_right_half_le_of_logfree_sum {m₀ a₀ : ℕ} [NeZero m₀]
    {T₀ X B : ℝ} (hX0 : 0 < X) (P_bad : DirichletCharacter ℂ m₀ → ℂ → Prop)
    [∀ χ, DecidablePred fun ρ => 1 / 2 ≤ ρ.re ∧ P_bad χ ρ]
    (hsum : ∑ χ : DirichletCharacter ℂ m₀,
        ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ P_bad χ ρ),
          (Stage11LinnikBridge.lZeroMult χ ρ : ℝ) * X ^ (ρ.re - 1) ≤ B) :
    (∑ χ : DirichletCharacter ℂ m₀, starRingEnd ℂ (χ (a₀ : ZMod m₀)) *
      ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ P_bad χ ρ),
        (Stage11LinnikBridge.lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ).re ≤
      ((1 / 4 : ℝ) * X ^ 2) * B := by
  have hterm_le : ∀ χ : DirichletCharacter ℂ m₀,
      ‖starRingEnd ℂ (χ (a₀ : ZMod m₀)) *
        ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ P_bad χ ρ),
          (Stage11LinnikBridge.lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ‖ ≤
      ((1 / 4 : ℝ) * X ^ 2) *
        ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ P_bad χ ρ),
          (Stage11LinnikBridge.lZeroMult χ ρ : ℝ) * X ^ (ρ.re - 1) := fun χ => by
    rw [norm_mul, Complex.norm_conj]
    have h1 : ‖∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ P_bad χ ρ),
          (Stage11LinnikBridge.lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ‖ ≤
        ((1 / 4 : ℝ) * X ^ 2) *
          ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ P_bad χ ρ),
            (Stage11LinnikBridge.lZeroMult χ ρ : ℝ) * X ^ (ρ.re - 1) := by
      rw [Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
      have hm' := Stage11LinnikBridge.mem_lZerosInBox.mp (Finset.mem_filter.mp hρ).1
      rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hX0]
      have hre : (ρ + 1).re = ρ.re + 1 := by simp
      rw [hre, show X ^ (ρ.re + 1) = X ^ 2 * X ^ (ρ.re - 1) by rw [← Real.rpow_two X, ← Real.rpow_add hX0]; congr 1; ring]
      have hK := Stage11LinnikBridge.norm_dyadicKernel_le_quarter (s := ρ) (by linarith [hm'.1]) hm'.2.1.le
      calc (Stage11LinnikBridge.lZeroMult χ ρ : ℝ) * (X ^ 2 * X ^ (ρ.re - 1)) * ‖Stage11LinnikBridge.dyadicKernel ρ‖
          ≤ (Stage11LinnikBridge.lZeroMult χ ρ : ℝ) * (X ^ 2 * X ^ (ρ.re - 1)) * (1 / 4) := by gcongr
        _ = ((1 / 4 : ℝ) * X ^ 2) * ((Stage11LinnikBridge.lZeroMult χ ρ : ℝ) * X ^ (ρ.re - 1)) := by ring
    exact (mul_le_mul (χ.norm_le_one _) h1 (norm_nonneg _) zero_le_one).trans (by rw [one_mul])
  calc (∑ χ : DirichletCharacter ℂ m₀, starRingEnd ℂ (χ (a₀ : ZMod m₀)) *
          ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ P_bad χ ρ),
            (Stage11LinnikBridge.lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ).re
      ≤ ‖∑ χ : DirichletCharacter ℂ m₀, starRingEnd ℂ (χ (a₀ : ZMod m₀)) *
          ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ P_bad χ ρ),
            (Stage11LinnikBridge.lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ‖ :=
          Complex.re_le_norm _
    _ ≤ ∑ χ : DirichletCharacter ℂ m₀, ‖starRingEnd ℂ (χ (a₀ : ZMod m₀)) *
          ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ P_bad χ ρ),
            (Stage11LinnikBridge.lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ‖ :=
          norm_sum_le _ _
    _ ≤ ∑ χ : DirichletCharacter ℂ m₀, ((1 / 4 : ℝ) * X ^ 2) *
          ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ P_bad χ ρ),
            (Stage11LinnikBridge.lZeroMult χ ρ : ℝ) * X ^ (ρ.re - 1) := Finset.sum_le_sum fun χ _ => hterm_le χ
    _ = ((1 / 4 : ℝ) * X ^ 2) * ∑ χ : DirichletCharacter ℂ m₀,
          ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ P_bad χ ρ),
            (Stage11LinnikBridge.lZeroMult χ ρ : ℝ) * X ^ (ρ.re - 1) := (Finset.mul_sum _ _ _).symm
    _ ≤ ((1 / 4 : ℝ) * X ^ 2) * B := mul_le_mul_of_nonneg_left hsum (by positivity)

/-- **UNCONDITIONAL TENT-WEIGHTED PRIME LOWER BOUND & QUADRATIC-TWIST CANCELLATION
(`tentWt_main_and_twist_unconditional`, `0` ASSUMPTIONS!)**:
There exist absolute constants `C_tw ≥ 30`, `c_w > 0` such that for EVERY modulus `m₀ ≥ 2`,
EVERY residue `a₀` coprime to `m₀`, EVERY cutoff `Z ≥ 4`, and EVERY scale `X ≥ 1` satisfying
`Real.log X ≥ C_tw * Real.log ((m₀ : ℝ) * Z ^ 2) * (Real.log Z + 1)`:
letting `P := apPrimes m₀ a₀ X` and `W := ∑ r ∈ P, tentWt X r`:
1. `c_w * X ^ 2 / ((m₀ : ℝ) ^ (3 / 2 : ℝ)) ≤ W` (and `0 < W`), AND
2. There exists at most ONE exceptional `s_exc : ℕ` such that for EVERY odd squarefree `s > 1` with
   `Coprime s m₀`, `(s : ℝ) ≤ Z ^ 2`, and `s ≠ s_exc`:
   `|∑ r ∈ P, tentWt X r * (jacobiSym (r : ℤ) s : ℝ)| ≤ (1 / Z ^ 2) * W`! -/
theorem tentWt_main_and_twist_unconditional :
    ∃ C_tw c_w : ℝ, 30 ≤ C_tw ∧ 0 < c_w ∧
      ∀ (m₀ a₀ : ℕ), 2 ≤ m₀ → Nat.Coprime a₀ m₀ →
        ∀ Z X : ℝ, 4 ≤ Z → 1 ≤ X →
          C_tw * Real.log ((m₀ : ℝ) * Z ^ 2) * (Real.log Z + 1) ≤ Real.log X →
          let P := apPrimes m₀ a₀ X
          let W := ∑ r ∈ P, tentWt X r
          c_w * X ^ 2 / ((m₀ : ℝ) ^ ((3 : ℝ) / 2)) ≤ W ∧
          ∃ s_exc : ℕ, ∀ s : ℕ, 1 < s → Odd s → Squarefree s → Nat.Coprime s m₀ →
            (s : ℝ) ≤ Z ^ 2 → s ≠ s_exc →
            |∑ r ∈ P, tentWt X r * (jacobiSym (r : ℤ) s : ℝ)| ≤ (1 / Z ^ 2) * W := by
  classical
  obtain ⟨c₁, c₂, hc₁_pos, hc₂_pos, hdh⟩ := Stage11LinnikUnconditional.deuringHeilbronnHypothesis_unconditional
  obtain ⟨C_D, A, hCD_pos, hA_ge1, hlf⟩ := Stage11LinnikUnconditional.logFreeZeroDensityHypothesis_unconditional
  obtain ⟨C_exp, hCexp_pos, hexp⟩ := Stage11LinnikBridge.explicit_formula_dyadic2_psi1Char
  obtain ⟨C_tail, hCtail_pos, htail⟩ := Stage11LinnikBridge.sum_tail_inv_im_sq_lZeros_le
  obtain ⟨C_cnt, hCcnt_pos, hcnt⟩ := Stage11LinnikBridge.lZeroCount_box_le
  obtain ⟨c_ζ, hcζ_pos, hzf_ζ⟩ := Stage5ZetaZeroFree.riemannZeta_deLaValleePoussin_zeroFree
  obtain ⟨c_simp, hcsimp_pos, hsimp⟩ := Stage11LinnikBridge.siegel_zero_simple_unconditional
  obtain ⟨c_S, hcS_pos, hsiegel⟩ := Stage9LandauSiegel.siegel_real_zero_exclusion (1 / 2) (by norm_num)
  obtain ⟨c_P, hcP_pos, hpage1, hpage2⟩ := Stage7SiegelWalfisz.page_at_most_one_siegel_zero_unconditional
  set δ_L : ℝ := min (1 / 60000) (min c_ζ (min (c_simp / 4) (min (c₂ / 4) (min (c_P / 4) (1 / 4)))))
  have hδL_pos : 0 < δ_L := by positivity
  have hδL_60k : δ_L ≤ 1 / 60000 := min_le_left _ _
  have hδL_ζ : δ_L ≤ c_ζ := (min_le_right _ _).trans (min_le_left _ _)
  have hδL_simp : δ_L ≤ c_simp / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδL_c2 : δ_L ≤ c₂ / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδL_cP : δ_L ≤ c_P / 4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hδL_qtr : δ_L ≤ 1 / 4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  set c_S' : ℝ := min 1 c_S
  have hcS'_pos : 0 < c_S' := by positivity
  set C_T0 : ℝ := max 16 ((8192 * 128 * C_tail / c_S') ^ 2)
  have hCT0_ge16 : 16 ≤ C_T0 := le_max_left _ _
  have hCT0_pos : 0 < C_T0 := by linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K_M : ℝ := 12 + Real.log (4 * C_T0 + 8) / Real.log 2
  have hKM_ge12 : 12 ≤ K_M := by
    have : 0 ≤ Real.log (4 * C_T0 + 8) / Real.log 2 := div_nonneg (Real.log_nonneg (by linarith)) hlog2_pos.le
    dsimp only [K_M]; linarith
  set B_rt : ℝ := max 1 (256 * C_D * Real.exp A * (1 + 2 / c₂))
  have hBrt_ge1 : 1 ≤ B_rt := le_max_left _ _
  have hBrt_ge : 256 * C_D * Real.exp A * (1 + 2 / c₂) ≤ B_rt := le_max_right _ _
  set R_c1 : ℝ := (2 / δ_L) * (Real.log (2 * B_rt) + 4)
  set R_c2 : ℝ := (16 / c₁) * (4 + Real.log (2 * B_rt) / Real.log 2)
  set K_err : ℝ := 4 * (12 + Real.log ((4096 / c_S') * (260 * C_exp + 24 + C_cnt * C_T0 * 64 + C_T0) + 1) / Real.log 2)
  set R₀ : ℝ := max (max (2 * A) 32) (max (max R_c1 R_c2) (max (64 / c₁) K_err))
  have hR0_2A : 2 * A ≤ R₀ := (le_max_left _ _).trans (le_max_left _ _)
  have hR0_32 : 32 ≤ R₀ := (le_max_right _ _).trans (le_max_left _ _)
  have hR0_c1 : R_c1 ≤ R₀ := ((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _)
  have hR0_c2 : R_c2 ≤ R₀ := ((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _)
  have hR0_64c1 : 64 / c₁ ≤ R₀ := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hR0_Kerr : K_err ≤ R₀ := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  set C_tw : ℝ := max 30 (K_M * R₀)
  refine ⟨C_tw, c_S' / 16, le_max_left _ _, by positivity, fun m₀ a₀ hm₀ hcop_am Z X hZ4 hX1 hlogX_ge => ?_⟩
  have : NeZero m₀ := ⟨by omega⟩
  have hm₀R : (2 : ℝ) ≤ (m₀ : ℝ) := by exact_mod_cast hm₀
  have hm₀_pos : (0 : ℝ) < (m₀ : ℝ) := by linarith
  have htot_pos : (0 : ℝ) < (m₀.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega))
  have htot_le : (m₀.totient : ℝ) ≤ (m₀ : ℝ) := by exact_mod_cast Nat.totient_le m₀
  have hZ0 : 0 < Z := by linarith
  have hLZ_gt1 : 1 < Real.log Z := by
    have : Real.exp 1 < Z := by linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) this)
  have hLZ_pos : 0 < Real.log Z := zero_lt_one.trans hLZ_gt1
  set mZ2 : ℝ := (m₀ : ℝ) * Z ^ 2
  have hmZ2_ge32 : 32 ≤ mZ2 := by dsimp only [mZ2]; nlinarith only [hm₀R, hZ4]
  have hlmZ2_pos : 0 < Real.log mZ2 := Real.log_pos (by linarith)
  set Q_all : ℕ := m₀ * (⌊Z ^ 2⌋₊ + 1)
  have hm₀_le_Q : m₀ ≤ Q_all := Nat.le_mul_of_pos_right m₀ (by positivity)
  have hQ_le_2mZ2 : (Q_all : ℝ) ≤ 2 * mZ2 := by
    have hfl : (⌊Z ^ 2⌋₊ : ℝ) ≤ Z ^ 2 := Nat.floor_le (sq_nonneg Z)
    have hfl2 : ((⌊Z ^ 2⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * Z ^ 2 := by push_cast; nlinarith only [hZ4, hfl]
    calc (Q_all : ℝ) = (m₀ : ℝ) * ((⌊Z ^ 2⌋₊ + 1 : ℕ) : ℝ) := by dsimp only [Q_all]; push_cast; rfl
      _ ≤ (m₀ : ℝ) * (2 * Z ^ 2) := mul_le_mul_of_nonneg_left hfl2 hm₀_pos.le
      _ = 2 * mZ2 := by dsimp only [mZ2]; ring
  have hQ_ge2 : (2 : ℝ) ≤ (Q_all : ℝ) := by exact_mod_cast (hm₀.trans hm₀_le_Q)
  have hQ0 : (0 : ℝ) < (Q_all : ℝ) := by linarith
  set T₀ : ℝ := C_T0 * (Q_all : ℝ) ^ 4
  have hT0_ge4 : 4 ≤ T₀ := by
    have h16 : (16 : ℝ) ≤ (Q_all : ℝ) ^ 4 :=
      (by norm_num : (16 : ℝ) ≤ 2 ^ 4).trans (pow_le_pow_left₀ (by norm_num) hQ_ge2 4)
    dsimp only [T₀]; nlinarith only [hCT0_ge16, h16]
  set M : ℝ := (Q_all : ℝ) * (T₀ + 2)
  set L_M : ℝ := Real.log M
  have hM_ge12 : 12 ≤ M := by dsimp only [M]; nlinarith only [hQ_ge2, hT0_ge4]
  have hM_pos : 0 < M := by linarith
  have hLM_gt1 : 1 < L_M := by
    have : Real.exp 1 < M := by dsimp only [M]; linarith [Real.exp_one_lt_d9]
    exact (Real.log_exp 1).symm.trans_lt (Real.log_lt_log (Real.exp_pos 1) this)
  have hLM_pos : 0 < L_M := zero_lt_one.trans hLM_gt1
  have hM_le_pow : M ≤ mZ2 ^ K_M := by
    have hM_step : M ≤ (4 * C_T0 + 8) * (2 * mZ2) ^ 5 := by
      have hQ5 : (Q_all : ℝ) ^ 5 ≤ (2 * mZ2) ^ 5 := pow_le_pow_left₀ hQ0.le hQ_le_2mZ2 5
      have hQ1 : (Q_all : ℝ) ≤ (2 * mZ2) ^ 5 :=
        hQ_le_2mZ2.trans (le_self_pow₀ (by linarith) (by norm_num))
      dsimp only [M, T₀]; nlinarith only [hQ5, hQ1, hCT0_pos, hQ0]
    have h25 : (2 * mZ2) ^ 5 = 32 * mZ2 ^ 5 := by ring
    have hC_pow : (4 * C_T0 + 8) * 32 ≤ mZ2 ^ (K_M - 5) := by
      have hlog_mZ2 : Real.log 2 ≤ Real.log mZ2 := Real.log_le_log (by norm_num) (by linarith)
      have h1 : Real.log (4 * C_T0 + 8) ≤ (Real.log (4 * C_T0 + 8) / Real.log 2) * Real.log mZ2 := by
        have hnn : 0 ≤ Real.log (4 * C_T0 + 8) / Real.log 2 := div_nonneg (Real.log_nonneg (by linarith)) hlog2_pos.le
        conv_lhs => rw [show Real.log (4 * C_T0 + 8) = (Real.log (4 * C_T0 + 8) / Real.log 2) * Real.log 2 from
          (div_mul_cancel₀ _ hlog2_pos.ne').symm]
        exact mul_le_mul_of_nonneg_left hlog_mZ2 hnn
      have h2 : Real.log 32 ≤ 5 * Real.log mZ2 := by linarith [Real.log_le_log (by norm_num) hmZ2_ge32]
      have hsum : Real.log ((4 * C_T0 + 8) * 32) ≤ (K_M - 5) * Real.log mZ2 := by
        rw [Real.log_mul (by linarith) (by norm_num)]
        have : K_M - 5 = 7 + Real.log (4 * C_T0 + 8) / Real.log 2 := by dsimp only [K_M]; ring
        rw [this]; nlinarith only [h1, h2, hlmZ2_pos]
      rw [Real.rpow_def_of_pos (by linarith), mul_comm (Real.log mZ2)]
      exact (Real.log_le_iff_le_exp (by positivity)).mp hsum
    calc M ≤ (4 * C_T0 + 8) * (2 * mZ2) ^ 5 := hM_step
      _ = ((4 * C_T0 + 8) * 32) * mZ2 ^ 5 := by rw [h25]; ring
      _ ≤ mZ2 ^ (K_M - 5) * mZ2 ^ (5 : ℝ) := by
          rw [show mZ2 ^ (5 : ℝ) = mZ2 ^ (5 : ℕ) by norm_cast]
          exact mul_le_mul_of_nonneg_right hC_pow (by positivity)
      _ = mZ2 ^ K_M := by rw [← Real.rpow_add (by linarith)]; congr 1; ring
  have hLM_le : L_M ≤ K_M * Real.log mZ2 :=
    (Real.log_le_log hM_pos hM_le_pow).trans (Real.log_rpow (by linarith) K_M).le
  set R : ℝ := Real.log X / L_M
  have hR_ge : R₀ * (Real.log Z + 1) ≤ R := by
    dsimp only [R]; rw [le_div_iff₀ hLM_pos]
    have hR0_nn : 0 ≤ R₀ := by linarith
    have h1 : R₀ * (Real.log Z + 1) * L_M ≤ (K_M * R₀) * Real.log mZ2 * (Real.log Z + 1) := by
      have := mul_le_mul_of_nonneg_left hLM_le (show 0 ≤ R₀ * (Real.log Z + 1) by positivity)
      linarith
    have h2 : (K_M * R₀) * Real.log mZ2 * (Real.log Z + 1) ≤ C_tw * Real.log mZ2 * (Real.log Z + 1) := by
      gcongr; exact le_max_right _ _
    exact (h1.trans h2).trans hlogX_ge
  have hR_ge_R0 : R₀ ≤ R := by
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ Real.log Z + 1 by linarith) (show 0 ≤ R₀ by linarith)
    linarith
  have hR_pos : 0 < R := by linarith
  have hX0 : 0 < X := by linarith
  have hX_ge_MR : M ^ R₀ ≤ X := by
    rw [Real.rpow_def_of_pos hM_pos, ← Real.le_log_iff_exp_le hX0]
    have h1 := (le_div_iff₀ hLM_pos).mp hR_ge_R0; linarith only [h1]
  have hX_ge_Q24 : (Q_all : ℝ) ^ (24 : ℝ) ≤ X :=
    (Real.rpow_le_rpow hQ0.le (by dsimp only [M]; nlinarith only [hQ0, hT0_ge4]) (by norm_num)).trans
      ((Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)).trans hX_ge_MR)
  have hX4 : 4 ≤ X := by
    have h1 : (4 : ℝ) ≤ (Q_all : ℝ) ^ (24 : ℝ) := by
      rw [show (24 : ℝ) = ((24 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact (by norm_num : (4 : ℝ) ≤ 2 ^ 24).trans (pow_le_pow_left₀ (by norm_num) hQ_ge2 24)
    linarith
  have hT0_le_X : C_T0 * (Q_all : ℝ) ^ 4 ≤ X := by
    have h1 : C_T0 * (Q_all : ℝ) ^ 4 ≤ M := by
      have hT0_nn : 0 ≤ C_T0 * (Q_all : ℝ) ^ 4 := by positivity
      dsimp only [M, T₀]; nlinarith only [hQ_ge2, hT0_nn]
    have h2 : M ≤ M ^ R₀ := (Real.rpow_one M).symm.le.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith))
    linarith
  have hX_err : (260 * C_exp + 24 + C_cnt * C_T0 * 64) * (Q_all : ℝ) ^ (8 : ℝ) ≤ (c_S' / 4096) * X ^ (1 / 4 : ℝ) := by
    set E_c : ℝ := (4096 / c_S') * (260 * C_exp + 24 + C_cnt * C_T0 * 64 + C_T0) + 1
    have hK_le : Real.log E_c / Real.log 2 ≤ R₀ / 4 - 12 := by dsimp only [K_err] at hR0_Kerr; linarith
    have hEc_pow : E_c ≤ M ^ (R₀ / 4 - 12) := by
      have h1 : Real.log E_c ≤ (R₀ / 4 - 12) * Real.log M := by
        have hlm2 : Real.log 2 ≤ Real.log M := Real.log_le_log (by norm_num) (by linarith)
        have hEc_ge1 : 1 ≤ E_c := by
          dsimp only [E_c]
          linarith [show 0 ≤ (4096 / c_S') * (260 * C_exp + 24 + C_cnt * C_T0 * 64 + C_T0) by positivity]
        have hnn : 0 ≤ Real.log E_c / Real.log 2 := div_nonneg (Real.log_nonneg hEc_ge1) hlog2_pos.le
        have hstep : Real.log E_c ≤ (Real.log E_c / Real.log 2) * Real.log M := by
          conv_lhs => rw [show Real.log E_c = (Real.log E_c / Real.log 2) * Real.log 2 from (div_mul_cancel₀ _ hlog2_pos.ne').symm]
          exact mul_le_mul_of_nonneg_left hlm2 hnn
        exact hstep.trans (mul_le_mul_of_nonneg_right hK_le hLM_pos.le)
      rw [Real.rpow_def_of_pos hM_pos, mul_comm (Real.log M)]
      exact (Real.log_le_iff_le_exp (by dsimp only [E_c]; positivity)).mp h1
    have hQ8_le : (Q_all : ℝ) ^ (8 : ℝ) ≤ M ^ (12 : ℝ) :=
      (Real.rpow_le_rpow hQ0.le (by dsimp only [M]; nlinarith only [hQ0, hT0_ge4]) (by norm_num)).trans
        (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))
    have hMR4 : M ^ (R₀ / 4) ≤ X ^ (1 / 4 : ℝ) := by
      have h1 := Real.rpow_le_rpow (Real.rpow_nonneg hM_pos.le _) hX_ge_MR (by norm_num : (0 : ℝ) ≤ 1 / 4)
      rwa [← Real.rpow_mul hM_pos.le, show R₀ * (1 / 4 : ℝ) = R₀ / 4 by ring] at h1
    have hprod : E_c * (Q_all : ℝ) ^ (8 : ℝ) ≤ X ^ (1 / 4 : ℝ) :=
      (mul_le_mul hEc_pow hQ8_le (by positivity) (by positivity)).trans
        (by rw [← Real.rpow_add hM_pos, show R₀ / 4 - 12 + 12 = R₀ / 4 by ring]; exact hMR4)
    have hEc_ge : (4096 / c_S') * (260 * C_exp + 24 + C_cnt * C_T0 * 64) ≤ E_c := by
      dsimp only [E_c]; nlinarith only [div_pos (by norm_num : (0 : ℝ) < 4096) hcS'_pos, hCT0_pos]
    have h1 := (mul_le_mul_of_nonneg_right hEc_ge (by positivity : 0 ≤ (Q_all : ℝ) ^ (8 : ℝ))).trans hprod
    have h2 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ c_S' / 4096 by positivity)
    have hcancel : (c_S' / 4096) * ((4096 / c_S') * (260 * C_exp + 24 + C_cnt * C_T0 * 64) * (Q_all : ℝ) ^ (8 : ℝ)) =
        (260 * C_exp + 24 + C_cnt * C_T0 * 64) * (Q_all : ℝ) ^ (8 : ℝ) := by field_simp [hcS'_pos.ne']
    linarith
  have hNonPrime_bd :
      3 * X * Real.sqrt (2 * X) * (Real.log (2 * X) + 2) ≤ (c_S' / (1024 * (Q_all : ℝ) ^ 2)) * X ^ 2 := by
    have hrt2 : Real.sqrt (2 * X) ≤ 2 * X ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow X]
      exact mul_le_mul_of_nonneg_right (Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩) (by positivity)
    have hlog2X : Real.log (2 * X) + 2 ≤ 12 * X ^ (1 / 4 : ℝ) := by
      have h1 : Real.log (2 * X) ≤ 2 * Real.log X := by
        rw [Real.log_mul (by norm_num) hX0.ne']
        linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : (2 : ℝ) ≤ X)]
      have h2 : (2 : ℝ) ≤ 4 * X ^ (1 / 4 : ℝ) := by linarith [Real.one_le_rpow hX1 (by norm_num : (0 : ℝ) ≤ 1 / 4)]
      linarith [log_le_four_rpow_qtr hX1]
    have hX_sp : X * X ^ (1 / 2 : ℝ) * X ^ (1 / 4 : ℝ) = X ^ (-(1 / 4 : ℝ)) * X ^ 2 := by
      conv_lhs => lhs; lhs; rw [← Real.rpow_one X]
      rw [← Real.rpow_add hX0, ← Real.rpow_add hX0, ← Real.rpow_two X, ← Real.rpow_add hX0]; congr 1; norm_num
    have h72 : 72 ≤ (c_S' / (1024 * (Q_all : ℝ) ^ 2)) * X ^ (1 / 4 : ℝ) := by
      have hQ_p : (Q_all : ℝ) ^ 2 ≤ (Q_all : ℝ) ^ (8 : ℝ) := by
        rw [show (Q_all : ℝ) ^ (2 : ℕ) = (Q_all : ℝ) ^ (2 : ℝ) by norm_cast]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      have h1 : 18 * (Q_all : ℝ) ^ 2 ≤ (c_S' / 4096) * X ^ (1 / 4 : ℝ) :=
        (mul_le_mul (by linarith [show 0 ≤ 260 * C_exp + C_cnt * C_T0 * 64 by positivity]) hQ_p (by positivity) (by positivity)).trans hX_err
      have hEq : (c_S' / (1024 * (Q_all : ℝ) ^ 2)) * X ^ (1 / 4 : ℝ) =
          4 * ((c_S' / 4096) * X ^ (1 / 4 : ℝ)) / (Q_all : ℝ) ^ 2 := by field_simp [hQ0.ne']; ring
      rw [hEq, le_div_iff₀ (sq_pos_of_pos hQ0)]; linarith
    have hlog2X_nn : 0 ≤ Real.log (2 * X) + 2 := by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * X)]
    calc 3 * X * Real.sqrt (2 * X) * (Real.log (2 * X) + 2)
        ≤ 3 * X * (2 * X ^ (1 / 2 : ℝ)) * (12 * X ^ (1 / 4 : ℝ)) := by gcongr
      _ = 72 * (X ^ (-(1 / 4 : ℝ)) * X ^ 2) := by rw [← hX_sp]; ring
      _ ≤ ((c_S' / (1024 * (Q_all : ℝ) ^ 2)) * X ^ (1 / 4 : ℝ)) * (X ^ (-(1 / 4 : ℝ)) * X ^ 2) := by gcongr
      _ = (c_S' / (1024 * (Q_all : ℝ) ^ 2)) * X ^ 2 := by
          have h1 : X ^ (1 / 4 : ℝ) * X ^ (-(1 / 4 : ℝ)) = 1 := by rw [← Real.rpow_add hX0]; norm_num
          calc _ = (c_S' / (1024 * (Q_all : ℝ) ^ 2)) * (X ^ (1 / 4 : ℝ) * X ^ (-(1 / 4 : ℝ))) * X ^ 2 := by ring
            _ = (c_S' / (1024 * (Q_all : ℝ) ^ 2)) * X ^ 2 := by rw [h1, mul_one]
  have hErr_vs_W :
      (c_S' / (512 * (Q_all : ℝ) ^ 2)) * X ^ 2 ≤
        (1 / (4 * Z ^ 2)) * ((c_S' / 16) * X ^ 2 / ((m₀ : ℝ) ^ ((3 : ℝ) / 2))) := by
    have hm32_le : (m₀ : ℝ) ^ ((3 : ℝ) / 2) ≤ (m₀ : ℝ) ^ 2 := by
      rw [show (m₀ : ℝ) ^ (2 : ℕ) = (m₀ : ℝ) ^ (2 : ℝ) by norm_cast]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have hQ2_ge : (m₀ : ℝ) ^ ((3 : ℝ) / 2) * Z ^ 2 ≤ (Q_all : ℝ) ^ 2 := by
      have h1 : Z ^ 2 ≤ ((⌊Z ^ 2⌋₊ + 1 : ℕ) : ℝ) := by push_cast; linarith [Nat.lt_floor_add_one (Z ^ 2)]
      have h2 : (16 : ℝ) ≤ ((⌊Z ^ 2⌋₊ + 1 : ℕ) : ℝ) := by linarith only [h1, show (16 : ℝ) ≤ Z ^ 2 by nlinarith only [hZ4]]
      have h3 : 4 * Z ^ 2 ≤ ((⌊Z ^ 2⌋₊ + 1 : ℕ) : ℝ) ^ 2 := by nlinarith only [h1, h2]
      have hQeq : (Q_all : ℝ) ^ 2 = (m₀ : ℝ) ^ 2 * ((⌊Z ^ 2⌋₊ + 1 : ℕ) : ℝ) ^ 2 := by
        dsimp only [Q_all]; push_cast; ring
      rw [hQeq]
      calc (m₀ : ℝ) ^ ((3 : ℝ) / 2) * Z ^ 2 ≤ (m₀ : ℝ) ^ 2 * (4 * Z ^ 2) := by
            nlinarith only [hm32_le, sq_nonneg Z, sq_nonneg (m₀ : ℝ)]
        _ ≤ (m₀ : ℝ) ^ 2 * ((⌊Z ^ 2⌋₊ + 1 : ℕ) : ℝ) ^ 2 := mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
    have hdiv : c_S' / (512 * (Q_all : ℝ) ^ 2) ≤ c_S' / (64 * ((m₀ : ℝ) ^ ((3 : ℝ) / 2) * Z ^ 2)) :=
      div_le_div_of_nonneg_left hcS'_pos.le (by positivity) (by nlinarith only [hQ2_ge, sq_nonneg (Q_all : ℝ)])
    calc (c_S' / (512 * (Q_all : ℝ) ^ 2)) * X ^ 2
        ≤ (c_S' / (64 * ((m₀ : ℝ) ^ ((3 : ℝ) / 2) * Z ^ 2))) * X ^ 2 := mul_le_mul_of_nonneg_right hdiv (sq_nonneg X)
      _ = (1 / (4 * Z ^ 2)) * ((c_S' / 16) * X ^ 2 / ((m₀ : ℝ) ^ ((3 : ℝ) / 2))) := by
          field_simp [hZ0.ne', (Real.rpow_pos_of_pos hm₀_pos _).ne']; ring
  have hexp_c1 : (1 / 2 : ℝ) * C_D * Real.exp A * Real.exp (-(R / 2) * δ_L) ≤ 1 / (64 * Z ^ 2) := by
    have hlog_bd : Real.log (2 * B_rt) + 2 * Real.log Z ≤ (R / 2) * δ_L := by
      have h1 : R_c1 * (Real.log Z + 1) ≤ R := (mul_le_mul_of_nonneg_right hR0_c1 (by linarith)).trans hR_ge
      have h2 : R_c1 * (Real.log Z + 1) * (δ_L / 2) = (Real.log (2 * B_rt) + 4) * (Real.log Z + 1) := by
        dsimp only [R_c1]; field_simp [hδL_pos.ne']
      have h3 := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ δ_L / 2)
      rw [h2] at h3
      have hnn : 0 ≤ Real.log (2 * B_rt) := Real.log_nonneg (by linarith)
      nlinarith only [h3, hnn, hLZ_pos]
    have hexp_le : Real.exp (-(R / 2) * δ_L) ≤ 1 / (2 * B_rt * Z ^ 2) := by
      have hlog_eq : Real.log (2 * B_rt * Z ^ 2) = Real.log (2 * B_rt) + 2 * Real.log Z := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
      rw [show -(R / 2) * δ_L = -((R / 2) * δ_L) by ring, Real.exp_neg, one_div]
      exact inv_anti₀ (by positivity) ((Real.log_le_iff_le_exp (by positivity)).mp (by linarith))
    have hB_ge : 256 * C_D * Real.exp A ≤ B_rt := by
      have h1 : 256 * C_D * Real.exp A * 1 ≤ 256 * C_D * Real.exp A * (1 + 2 / c₂) :=
        mul_le_mul_of_nonneg_left (by linarith [div_pos (by norm_num : (0 : ℝ) < 2) hc₂_pos]) (by positivity)
      rw [mul_one] at h1; exact h1.trans hBrt_ge
    calc (1 / 2 : ℝ) * C_D * Real.exp A * Real.exp (-(R / 2) * δ_L)
        ≤ (1 / 2 : ℝ) * C_D * Real.exp A * (1 / (2 * B_rt * Z ^ 2)) := mul_le_mul_of_nonneg_left hexp_le (by positivity)
      _ = ((1 / 2 : ℝ) * C_D * Real.exp A / (2 * B_rt)) / Z ^ 2 := by ring
      _ ≤ (1 / 64 : ℝ) / Z ^ 2 := div_le_div_of_nonneg_right (by rw [div_le_iff₀ (by positivity)]; linarith) (sq_nonneg Z)
      _ = 1 / (64 * Z ^ 2) := by ring
  -- Shared sum of `ef_nonright_error_le` for `psi1AP m₀ a₀`
  have hsum_ef_m0 :
      ‖((Stage11LinnikBridge.dyadic2Real (Stage11LinnikBridge.psi1AP m₀ a₀) X : ℝ) : ℂ) -
          (m₀.totient : ℂ)⁻¹ * ((1 / 4 : ℂ) * (X : ℂ) ^ 2 -
            ∑ χ : DirichletCharacter ℂ m₀, starRingEnd ℂ (χ (a₀ : ZMod m₀)) *
              ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re),
                (Stage11LinnikBridge.lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ)‖ ≤
        (c_S' / (1024 * (Q_all : ℝ) ^ 2)) * X ^ 2 := by
    rw [Stage11LinnikBridge.dyadic2Real_psi1AP_eq_char_sum hcop_am X]
    have h1_ap : (1 : DirichletCharacter ℂ m₀) (a₀ : ZMod m₀) = 1 := by
      rw [Stage2DirichletAP.principal_char_apply_nat a₀, if_pos hcop_am]
    have hmain : ∑ χ : DirichletCharacter ℂ m₀,
        starRingEnd ℂ (χ (a₀ : ZMod m₀)) * (if χ = 1 then (1 / 4 : ℂ) * (X : ℂ) ^ 2 else 0) =
        (1 / 4 : ℂ) * (X : ℂ) ^ 2 := by
      rw [Finset.sum_eq_single (1 : DirichletCharacter ℂ m₀)]
      · rw [if_pos rfl, h1_ap, map_one, one_mul]
      · intro χ _ hne; rw [if_neg hne, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hdiff :
        (m₀.totient : ℂ)⁻¹ * (∑ χ : DirichletCharacter ℂ m₀, starRingEnd ℂ (χ (a₀ : ZMod m₀)) *
          Stage11LinnikBridge.dyadic2 (Stage4ExplicitFormula.psi1Char χ) X) -
        (m₀.totient : ℂ)⁻¹ * ((1 / 4 : ℂ) * (X : ℂ) ^ 2 -
          ∑ χ : DirichletCharacter ℂ m₀, starRingEnd ℂ (χ (a₀ : ZMod m₀)) *
            ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re),
              (Stage11LinnikBridge.lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ) =
        (m₀.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ m₀, starRingEnd ℂ (χ (a₀ : ZMod m₀)) *
          (Stage11LinnikBridge.dyadic2 (Stage4ExplicitFormula.psi1Char χ) X -
            ((if χ = 1 then (1 / 4 : ℂ) * (X : ℂ) ^ 2 else 0) -
              ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re),
                (Stage11LinnikBridge.lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ)) := by
      rw [← mul_sub]; congr 1
      conv_lhs => rw [← hmain]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun χ _ => by ring
    rw [hdiff, norm_mul, norm_inv, Complex.norm_natCast]
    let err : DirichletCharacter ℂ m₀ → ℂ := fun χ =>
      Stage11LinnikBridge.dyadic2 (Stage4ExplicitFormula.psi1Char χ) X -
        ((if χ = 1 then (1 / 4 : ℂ) * (X : ℂ) ^ 2 else 0) -
          ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re),
            (Stage11LinnikBridge.lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ)
    have hsum_le :
        ‖∑ χ : DirichletCharacter ℂ m₀, starRingEnd ℂ (χ (a₀ : ZMod m₀)) * err χ‖ ≤
          (m₀.totient : ℝ) * ((c_S' / (1024 * (Q_all : ℝ) ^ 2)) * X ^ 2) := by
      calc ‖∑ χ : DirichletCharacter ℂ m₀, starRingEnd ℂ (χ (a₀ : ZMod m₀)) * err χ‖
          ≤ ∑ χ : DirichletCharacter ℂ m₀, ‖starRingEnd ℂ (χ (a₀ : ZMod m₀))‖ * ‖err χ‖ :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => by rw [norm_mul])
        _ ≤ ∑ _χ : DirichletCharacter ℂ m₀, (c_S' / (1024 * (Q_all : ℝ) ^ 2)) * X ^ 2 :=
            Finset.sum_le_sum fun χ _ => by
              have h1 : ‖starRingEnd ℂ (χ (a₀ : ZMod m₀))‖ ≤ 1 := by rw [Complex.norm_conj]; exact χ.norm_le_one _
              have h2 : ‖err χ‖ ≤ (c_S' / (1024 * (Q_all : ℝ) ^ 2)) * X ^ 2 :=
                ef_nonright_error_le hCexp_pos hCtail_pos hCcnt_pos hcS'_pos hexp htail hcnt le_rfl
                  hm₀ hm₀_le_Q hX_ge_Q24 hT0_le_X hX_err χ
              exact (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one).trans (by rw [one_mul])
        _ = (m₀.totient : ℝ) * ((c_S' / (1024 * (Q_all : ℝ) ^ 2)) * X ^ 2) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_dirichletChar_eq_totient m₀]
    calc (m₀.totient : ℝ)⁻¹ * ‖∑ χ : DirichletCharacter ℂ m₀, starRingEnd ℂ (χ (a₀ : ZMod m₀)) * err χ‖
        ≤ (m₀.totient : ℝ)⁻¹ * ((m₀.totient : ℝ) * ((c_S' / (1024 * (Q_all : ℝ) ^ 2)) * X ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum_le (by positivity)
      _ = (c_S' / (1024 * (Q_all : ℝ) ^ 2)) * X ^ 2 := inv_mul_cancel_left₀ htot_pos.ne' _
  -- Helper A: Given `hno_m0`, prove `W ≥ (1/16) X^2 / φ(m₀)` (and hence `≥ (c_S' / 16) X^2 / m₀^(3/2)`)
  have hMain_noSiegel :
      (∀ (χ : DirichletCharacter ℂ m₀) (β : ℝ), 1 - δ_L / L_M < β → β < 1 →
        DirichletCharacter.LFunction χ (β : ℂ) ≠ 0) →
      (1 / 16 : ℝ) * X ^ 2 / (m₀.totient : ℝ) ≤ ∑ r ∈ apPrimes m₀ a₀ X, tentWt X r := by
    intro hno
    set L0 := Real.log ((m₀ : ℝ) * (T₀ + 2))
    have hL0_pos : 0 < L0 := Real.log_pos (by nlinarith only [hm₀R, hT0_ge4])
    have hL0_le : L0 ≤ L_M := Real.log_le_log (by positivity) (by dsimp only [M]; gcongr)
    have hRm0 : max (2 * A) 2 ≤ Real.log X / L0 := by
      have h1 : R ≤ Real.log X / L0 := div_le_div_of_nonneg_left (Real.log_nonneg hX1) hL0_pos hL0_le
      have h2 : max (2 * A) 2 ≤ R₀ := max_le hR0_2A (by linarith)
      linarith
    set lam₀ : ℝ := δ_L * (L0 / L_M)
    have hgap0 : ∀ (χ : DirichletCharacter ℂ m₀) (ρ : ℂ),
        ρ ∈ Stage11LinnikBridge.lZerosInBox χ T₀ → 1 / 2 ≤ ρ.re → True → lam₀ / L0 ≤ 1 - ρ.re := fun χ ρ hρ _ _ => by
      have h1 := zero_re_gap_of_no_real_zero hcζ_pos hδL_pos hδL_60k hδL_ζ hzf_ζ hm₀ hm₀_le_Q hT0_ge4 (hno χ) hρ
      have hEq : lam₀ / L0 = δ_L / L_M := by dsimp only [lam₀]; field_simp [hL0_pos.ne', hLM_pos.ne']
      rwa [hEq]
    have hlf0 := Stage11LinnikBridge.sum_right_half_zeros_le_of_logfree hCD_pos hA_ge1 hlf hm₀ (by linarith) hX4
      (by positivity : 0 ≤ lam₀) (fun _ _ => True) hgap0 hRm0
    have hExp_eq : -(Real.log X / L0 / 2) * lam₀ = -(R / 2) * δ_L := by
      dsimp only [lam₀, R]; field_simp [hL0_pos.ne', hLM_pos.ne']
    rw [hExp_eq] at hlf0
    have hRight_le :
        (∑ χ : DirichletCharacter ℂ m₀, starRingEnd ℂ (χ (a₀ : ZMod m₀)) *
          ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re),
            (Stage11LinnikBridge.lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ).re ≤
          (1 / 32 : ℝ) * X ^ 2 := by
      have h16 : (1 / (64 * Z ^ 2) : ℝ) ≤ 1 / 32 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith only [hZ4]
      have hre_bd := re_sum_right_half_le_of_logfree_sum (a₀ := a₀) hX0 (fun _ _ => True) hlf0
      simp only [and_true] at hre_bd
      calc _ ≤ ((1 / 4 : ℝ) * X ^ 2) * (2 * C_D * Real.exp A * Real.exp (-(R / 2) * δ_L)) := hre_bd
        _ = ((1 / 2 : ℝ) * C_D * Real.exp A * Real.exp (-(R / 2) * δ_L)) * X ^ 2 := by ring
        _ ≤ (1 / (64 * Z ^ 2)) * X ^ 2 := mul_le_mul_of_nonneg_right hexp_c1 (sq_nonneg X)
        _ ≤ (1 / 32 : ℝ) * X ^ 2 := mul_le_mul_of_nonneg_right h16 (sq_nonneg X)
    have hre_ef : Stage11LinnikBridge.dyadic2Real (Stage11LinnikBridge.psi1AP m₀ a₀) X ≥
        (m₀.totient : ℝ)⁻¹ * ((1 / 4 : ℝ) * X ^ 2 - (1 / 32 : ℝ) * X ^ 2) -
        (c_S' / (1024 * (Q_all : ℝ) ^ 2)) * X ^ 2 := by
      have h1 := (abs_le.mp ((Complex.abs_re_le_norm _).trans hsum_ef_m0)).1
      rw [Complex.sub_re, Complex.ofReal_re, Complex.mul_re] at h1
      have hinv_re : ((m₀.totient : ℂ)⁻¹).re = (m₀.totient : ℝ)⁻¹ := by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]
      have hinv_im : ((m₀.totient : ℂ)⁻¹).im = 0 := by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_im]
      rw [hinv_re, hinv_im, zero_mul, sub_zero, Complex.sub_re] at h1
      have hq_re : ((1 / 4 : ℂ) * (X : ℂ) ^ 2).re = (1 / 4 : ℝ) * X ^ 2 := by
        rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
      rw [hq_re] at h1
      have h2 := mul_le_mul_of_nonneg_left (sub_le_sub_left hRight_le ((1 / 4 : ℝ) * X ^ 2)) (inv_nonneg.mpr htot_pos.le)
      linarith
    have herr_sm : (c_S' / (512 * (Q_all : ℝ) ^ 2)) * X ^ 2 ≤ (1 / 16 : ℝ) * X ^ 2 / (m₀.totient : ℝ) := by
      have h1 : (c_S' / 16) * X ^ 2 / ((m₀ : ℝ) ^ ((3 : ℝ) / 2)) ≤ (1 / 16 : ℝ) * X ^ 2 / (m₀.totient : ℝ) := by
        have hc1 : c_S' ≤ 1 := min_le_left _ _
        have hm1 : (m₀.totient : ℝ) ≤ (m₀ : ℝ) ^ ((3 : ℝ) / 2) :=
          htot_le.trans ((Real.rpow_one (m₀ : ℝ)).symm.le.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)))
        calc (c_S' / 16) * X ^ 2 / ((m₀ : ℝ) ^ ((3 : ℝ) / 2))
            ≤ (1 / 16 : ℝ) * X ^ 2 / ((m₀ : ℝ) ^ ((3 : ℝ) / 2)) := by gcongr
          _ ≤ (1 / 16 : ℝ) * X ^ 2 / (m₀.totient : ℝ) := div_le_div_of_nonneg_left (by positivity) htot_pos hm1
      have hZ1 : (1 / (4 * Z ^ 2) : ℝ) ≤ 1 := (div_le_one (by positivity)).mpr (by nlinarith only [hZ4])
      calc (c_S' / (512 * (Q_all : ℝ) ^ 2)) * X ^ 2
          ≤ (1 / (4 * Z ^ 2)) * ((c_S' / 16) * X ^ 2 / ((m₀ : ℝ) ^ ((3 : ℝ) / 2))) := hErr_vs_W
        _ ≤ 1 * ((c_S' / 16) * X ^ 2 / ((m₀ : ℝ) ^ ((3 : ℝ) / 2))) := mul_le_mul_of_nonneg_right hZ1 (by positivity)
        _ ≤ (1 / 16 : ℝ) * X ^ 2 / (m₀.totient : ℝ) := by rw [one_mul]; exact h1
    have hW_ge := tentWt_apPrimes_ge_sub_nonprime (m₀ := m₀) (a₀ := a₀) hX1
    have h2x : (c_S' / (1024 * (Q_all : ℝ) ^ 2)) * X ^ 2 + (c_S' / (1024 * (Q_all : ℝ) ^ 2)) * X ^ 2 =
        (c_S' / (512 * (Q_all : ℝ) ^ 2)) * X ^ 2 := by field_simp [hQ0.ne']; ring
    have hmain_eq : (m₀.totient : ℝ)⁻¹ * ((1 / 4 : ℝ) * X ^ 2 - (1 / 32 : ℝ) * X ^ 2) =
        (7 / 32 : ℝ) * (X ^ 2 / (m₀.totient : ℝ)) := by ring
    have herr_sm' : (c_S' / (512 * (Q_all : ℝ) ^ 2)) * X ^ 2 ≤ (1 / 16 : ℝ) * (X ^ 2 / (m₀.totient : ℝ)) := by
      linarith [herr_sm, show (1 / 16 : ℝ) * X ^ 2 / (m₀.totient : ℝ) = (1 / 16 : ℝ) * (X ^ 2 / (m₀.totient : ℝ)) by ring]
    have hgoal_eq : (1 / 16 : ℝ) * X ^ 2 / (m₀.totient : ℝ) = (1 / 16 : ℝ) * (X ^ 2 / (m₀.totient : ℝ)) := by ring
    have hX2_tot_nn : 0 ≤ X ^ 2 / (m₀.totient : ℝ) := by positivity
    linarith only [hW_ge, hre_ef, hNonPrime_bd, herr_sm', h2x, hmain_eq, hgoal_eq, hX2_tot_nn]
  -- Helper B: Given `hRH_bd` for an odd squarefree `s > 1` (`Coprime s m₀, s ≤ Z^2`), bound `|twist(s)|`!
  have hTwist_of_rh : ∀ (s : ℕ) [NeZero s] (hs1 : 1 < s) (hs_odd : Odd s) (hs_sqf : Squarefree s)
      (hcop_sm : Nat.Coprime s m₀) (hs_le : (s : ℝ) ≤ Z ^ 2) (B_rh : ℝ)
      (hRH_bd : ‖∑ χ : DirichletCharacter ℂ m₀,
          starRingEnd ℂ (χ (a₀ : ZMod m₀)) *
            ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox
                (Stage11SecondMomentFrame.twistedChar χ (quadCharOfOddSqf s hs_odd)) T₀).filter (fun ρ => 1 / 2 ≤ ρ.re),
              (Stage11LinnikBridge.lZeroMult
                (Stage11SecondMomentFrame.twistedChar χ (quadCharOfOddSqf s hs_odd)) ρ : ℂ) *
                (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ‖ ≤ B_rh * X ^ 2),
      |∑ r ∈ apPrimes m₀ a₀ X, tentWt X r * (jacobiSym (r : ℤ) s : ℝ)| ≤
        (B_rh / (m₀.totient : ℝ)) * X ^ 2 + (c_S' / (512 * (Q_all : ℝ) ^ 2)) * X ^ 2 := by
    intro s _ hs1 hs_odd hs_sqf hcop_sm hs_le B_rh hRH_bd
    have hms_ge2 : 2 ≤ m₀ * s := hm₀.trans (Nat.le_mul_of_pos_right m₀ (by omega))
    have hms_le_Q : m₀ * s ≤ Q_all := Nat.mul_le_mul_left m₀ ((Nat.le_floor hs_le).trans (Nat.le_succ _))
    have hχs_prim : (quadCharOfOddSqf s hs_odd).IsPrimitive := quadCharOfOddSqf_isPrimitive hs_odd hs_sqf
    have htw_ne1 : ∀ χ : DirichletCharacter ℂ m₀,
        Stage11SecondMomentFrame.twistedChar χ (quadCharOfOddSqf s hs_odd) ≠ 1 := fun χ h1 => by
      have hs_dvd := right_dvd_conductor_twistedChar hcop_sm.symm χ hχs_prim
      rw [h1, DirichletCharacter.conductor_one] at hs_dvd
      have := Nat.le_of_dvd one_pos hs_dvd; omega
    have hchar_bd :
        ‖(m₀.totient : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ m₀, starRingEnd ℂ (χ (a₀ : ZMod m₀)) *
            Stage11LinnikBridge.dyadic2
              (Stage4ExplicitFormula.psi1Char
                (Stage11SecondMomentFrame.twistedChar χ (quadCharOfOddSqf s hs_odd))) X‖ ≤
          (B_rh / (m₀.totient : ℝ)) * X ^ 2 + (c_S' / (1024 * (Q_all : ℝ) ^ 2)) * X ^ 2 := by
      have hdecomp :
          ∑ χ : DirichletCharacter ℂ m₀, starRingEnd ℂ (χ (a₀ : ZMod m₀)) *
            Stage11LinnikBridge.dyadic2
              (Stage4ExplicitFormula.psi1Char
                (Stage11SecondMomentFrame.twistedChar χ (quadCharOfOddSqf s hs_odd))) X =
          (∑ χ : DirichletCharacter ℂ m₀, starRingEnd ℂ (χ (a₀ : ZMod m₀)) *
            (Stage11LinnikBridge.dyadic2
              (Stage4ExplicitFormula.psi1Char
                (Stage11SecondMomentFrame.twistedChar χ (quadCharOfOddSqf s hs_odd))) X -
              ((if Stage11SecondMomentFrame.twistedChar χ (quadCharOfOddSqf s hs_odd) = 1 then (1 / 4 : ℂ) * (X : ℂ) ^ 2 else 0) -
                ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox
                    (Stage11SecondMomentFrame.twistedChar χ (quadCharOfOddSqf s hs_odd)) T₀).filter (fun ρ => 1 / 2 ≤ ρ.re),
                  (Stage11LinnikBridge.lZeroMult
                    (Stage11SecondMomentFrame.twistedChar χ (quadCharOfOddSqf s hs_odd)) ρ : ℂ) *
                    (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ))) -
          (∑ χ : DirichletCharacter ℂ m₀, starRingEnd ℂ (χ (a₀ : ZMod m₀)) *
            ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox
                (Stage11SecondMomentFrame.twistedChar χ (quadCharOfOddSqf s hs_odd)) T₀).filter (fun ρ => 1 / 2 ≤ ρ.re),
              (Stage11LinnikBridge.lZeroMult
                (Stage11SecondMomentFrame.twistedChar χ (quadCharOfOddSqf s hs_odd)) ρ : ℂ) *
                (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [if_neg (htw_ne1 χ)]; ring
      rw [hdecomp, norm_mul, norm_inv, Complex.norm_natCast]
      let errS : DirichletCharacter ℂ m₀ → ℂ := fun χ =>
        Stage11LinnikBridge.dyadic2
            (Stage4ExplicitFormula.psi1Char
              (Stage11SecondMomentFrame.twistedChar χ (quadCharOfOddSqf s hs_odd))) X -
          ((if Stage11SecondMomentFrame.twistedChar χ (quadCharOfOddSqf s hs_odd) = 1 then (1 / 4 : ℂ) * (X : ℂ) ^ 2 else 0) -
            ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox
                (Stage11SecondMomentFrame.twistedChar χ (quadCharOfOddSqf s hs_odd)) T₀).filter (fun ρ => 1 / 2 ≤ ρ.re),
              (Stage11LinnikBridge.lZeroMult
                (Stage11SecondMomentFrame.twistedChar χ (quadCharOfOddSqf s hs_odd)) ρ : ℂ) *
                (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ)
      have hEF_sum : ‖∑ χ : DirichletCharacter ℂ m₀, starRingEnd ℂ (χ (a₀ : ZMod m₀)) * errS χ‖ ≤
          (m₀.totient : ℝ) * ((c_S' / (1024 * (Q_all : ℝ) ^ 2)) * X ^ 2) := by
        calc ‖∑ χ : DirichletCharacter ℂ m₀, starRingEnd ℂ (χ (a₀ : ZMod m₀)) * errS χ‖
            ≤ ∑ χ : DirichletCharacter ℂ m₀, ‖starRingEnd ℂ (χ (a₀ : ZMod m₀))‖ * ‖errS χ‖ :=
              (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => by rw [norm_mul])
          _ ≤ ∑ _χ : DirichletCharacter ℂ m₀, (c_S' / (1024 * (Q_all : ℝ) ^ 2)) * X ^ 2 :=
              Finset.sum_le_sum fun χ _ => by
                have h1 : ‖starRingEnd ℂ (χ (a₀ : ZMod m₀))‖ ≤ 1 := by rw [Complex.norm_conj]; exact χ.norm_le_one _
                have h2 : ‖errS χ‖ ≤ (c_S' / (1024 * (Q_all : ℝ) ^ 2)) * X ^ 2 :=
                  ef_nonright_error_le hCexp_pos hCtail_pos hCcnt_pos hcS'_pos hexp htail hcnt le_rfl
                    hms_ge2 hms_le_Q hX_ge_Q24 hT0_le_X hX_err
                    (Stage11SecondMomentFrame.twistedChar χ (quadCharOfOddSqf s hs_odd))
                exact (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one).trans (by rw [one_mul])
          _ = (m₀.totient : ℝ) * ((c_S' / (1024 * (Q_all : ℝ) ^ 2)) * X ^ 2) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_dirichletChar_eq_totient m₀]
      calc (m₀.totient : ℝ)⁻¹ * ‖(∑ χ : DirichletCharacter ℂ m₀, starRingEnd ℂ (χ (a₀ : ZMod m₀)) * errS χ) - _‖
          ≤ (m₀.totient : ℝ)⁻¹ * (‖_‖ + ‖_‖) := mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
        _ ≤ (m₀.totient : ℝ)⁻¹ * ((m₀.totient : ℝ) * ((c_S' / (1024 * (Q_all : ℝ) ^ 2)) * X ^ 2) + B_rh * X ^ 2) :=
            mul_le_mul_of_nonneg_left (add_le_add hEF_sum hRH_bd) (by positivity)
        _ = (B_rh / (m₀.totient : ℝ)) * X ^ 2 + (c_S' / (1024 * (Q_all : ℝ) ^ 2)) * X ^ 2 := by
            field_simp [htot_pos.ne']; ring
    have htri := abs_tentWt_twist_sub_char_sum_le hcop_am hcop_sm.symm hs_odd hX1
    have h2x : (c_S' / (1024 * (Q_all : ℝ) ^ 2)) * X ^ 2 + (c_S' / (1024 * (Q_all : ℝ) ^ 2)) * X ^ 2 =
        (c_S' / (512 * (Q_all : ℝ) ^ 2)) * X ^ 2 := by field_simp [hQ0.ne']; ring
    linarith [htri, hchar_bd, hNonPrime_bd, h2x]
  -- Helper C: From `hno_s` (no real zero > 1 - δ_L / L_M for any `twistedChar χ χ_s`), bound `|twist(s)|`
  have hTwist_noSiegel : ∀ (s : ℕ) [NeZero s] (hs1 : 1 < s) (hs_odd : Odd s) (hs_sqf : Squarefree s)
      (hcop_sm : Nat.Coprime s m₀) (hs_le : (s : ℝ) ≤ Z ^ 2),
      (∀ (χ : DirichletCharacter ℂ m₀) (β : ℝ), 1 - δ_L / L_M < β → β < 1 →
        DirichletCharacter.LFunction
          (Stage11SecondMomentFrame.twistedChar χ (quadCharOfOddSqf s hs_odd)) (β : ℂ) ≠ 0) →
      |∑ r ∈ apPrimes m₀ a₀ X, tentWt X r * (jacobiSym (r : ℤ) s : ℝ)| ≤
        ((1 / (64 * Z ^ 2)) / (m₀.totient : ℝ)) * X ^ 2 + (c_S' / (512 * (Q_all : ℝ) ^ 2)) * X ^ 2 := by
    intro s _ hs1 hs_odd hs_sqf hcop_sm hs_le hno_s
    have hms_ge2 : 2 ≤ m₀ * s := hm₀.trans (Nat.le_mul_of_pos_right m₀ (by omega))
    have hms_le_Q : m₀ * s ≤ Q_all := Nat.mul_le_mul_left m₀ ((Nat.le_floor hs_le).trans (Nat.le_succ _))
    set Ls := Real.log (((m₀ * s : ℕ) : ℝ) * (T₀ + 2))
    have hLs_pos : 0 < Ls := by
      have h2 : (2 : ℝ) ≤ ((m₀ * s : ℕ) : ℝ) := by exact_mod_cast hms_ge2
      exact Real.log_pos (by nlinarith only [h2, hT0_ge4])
    have hLs_le : Ls ≤ L_M := Real.log_le_log (by positivity) (by dsimp only [M]; gcongr)
    have hRs : max (2 * A) 2 ≤ Real.log X / Ls := by
      have h1 : R ≤ Real.log X / Ls := div_le_div_of_nonneg_left (Real.log_nonneg hX1) hLs_pos hLs_le
      have h2 : max (2 * A) 2 ≤ R₀ := max_le hR0_2A (by linarith)
      linarith
    set lam_s : ℝ := δ_L * (Ls / L_M)
    have hgap_s : ∀ (χ : DirichletCharacter ℂ m₀) (ρ : ℂ),
        ρ ∈ Stage11LinnikBridge.lZerosInBox
          (Stage11SecondMomentFrame.twistedChar χ (quadCharOfOddSqf s hs_odd)) T₀ →
        1 / 2 ≤ ρ.re → lam_s / Ls ≤ 1 - ρ.re := fun χ ρ hρ _ => by
      have h1 := zero_re_gap_of_no_real_zero hcζ_pos hδL_pos hδL_60k hδL_ζ hzf_ζ hms_ge2 hms_le_Q hT0_ge4 (hno_s χ) hρ
      have hEq : lam_s / Ls = δ_L / L_M := by dsimp only [lam_s]; field_simp [hLs_pos.ne', hLM_pos.ne']
      rwa [hEq]
    have hrh := norm_twisted_right_half_le_of_logfree (a₀ := a₀) hCD_pos hA_ge1 hlf hm₀ hcop_sm.symm hs_odd
      (by linarith) hX4 (by positivity : 0 ≤ lam_s) hgap_s hRs
    have hExp_eq : -(Real.log X / Ls / 2) * lam_s = -(R / 2) * δ_L := by
      dsimp only [lam_s, R]; field_simp [hLs_pos.ne', hLM_pos.ne']
    rw [hExp_eq] at hrh
    exact hTwist_of_rh s hs1 hs_odd hs_sqf hcop_sm hs_le (1 / (64 * Z ^ 2))
      (hrh.trans (mul_le_mul_of_nonneg_right hexp_c1 (sq_nonneg X)))
  -- Useful lower bound: `(c_S' / 16) * X^2 / m₀^(3/2) ≤ (1 / 16) * X^2 / φ(m₀)`
  have hW_cS_le_main : (c_S' / 16) * X ^ 2 / ((m₀ : ℝ) ^ ((3 : ℝ) / 2)) ≤ (1 / 16 : ℝ) * X ^ 2 / (m₀.totient : ℝ) := by
    have hc1 : c_S' ≤ 1 := min_le_left _ _
    have hm1 : (m₀.totient : ℝ) ≤ (m₀ : ℝ) ^ ((3 : ℝ) / 2) :=
      htot_le.trans ((Real.rpow_one (m₀ : ℝ)).symm.le.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)))
    calc (c_S' / 16) * X ^ 2 / ((m₀ : ℝ) ^ ((3 : ℝ) / 2))
        ≤ (1 / 16 : ℝ) * X ^ 2 / ((m₀ : ℝ) ^ ((3 : ℝ) / 2)) := by gcongr
      _ ≤ (1 / 16 : ℝ) * X ^ 2 / (m₀.totient : ℝ) := div_le_div_of_nonneg_left (by positivity) htot_pos hm1
  -- Case split on whether ANY primitive character `ψ₁` (`ψ₁.N ≤ Q_all`) has a real zero `β₁ ∈ (1 - δ_L / L_M, 1)`!
  by_cases hSiegel : ∃ (ψ₁ : PChar) (β₁ : ℝ),
      ψ₁.N ≤ Q_all ∧ 1 - δ_L / L_M < β₁ ∧ β₁ < 1 ∧ DirichletCharacter.LFunction ψ₁.χ (β₁ : ℂ) = 0
  · obtain ⟨ψ₁, β₁, hψ₁_leQ, hβ₁_lo, hβ₁_hi, hLψ₁_0⟩ := hSiegel
    have hlog2Q_le : Real.log (2 * (Q_all : ℝ)) ≤ L_M :=
      Real.log_le_log (by positivity) (by dsimp only [M]; nlinarith only [hQ0, hT0_ge4])
    have hlog2Q_pos : 0 < Real.log (2 * (Q_all : ℝ)) := Real.log_pos (by linarith)
    have hβ₁_page : 1 - c_P / Real.log (2 * (Q_all : ℝ)) < β₁ := by
      have h1 : δ_L / L_M ≤ c_P / Real.log (2 * (Q_all : ℝ)) :=
        (div_le_div_of_nonneg_right (hδL_cP.trans (by linarith)) hLM_pos.le).trans
          (div_le_div_of_nonneg_left hcP_pos.le hlog2Q_pos hlog2Q_le)
      linarith
    have hψ₁_real_ne1 := hpage1 Q_all (hm₀.trans hm₀_le_Q) ψ₁ β₁ hψ₁_leQ hLψ₁_0 hβ₁_page
    have hψ₁_sq : ψ₁.χ ^ 2 = 1 := HostFieldSupply.real_pchar_sq_eq_one hψ₁_real_ne1.1
    have hψ₁_ne1 : ψ₁.χ ≠ 1 := hψ₁_real_ne1.2
    have hβ₁_gt_half : 1 / 2 < β₁ := by
      have : δ_L / L_M ≤ 1 / 4 := (div_le_self hδL_pos.le hLM_gt1.le).trans hδL_qtr
      linarith
    -- Subcase B vs Subcase C: does `ψ₁.N ∣ m₀`?
    by_cases hψ₁_dvd : ψ₁.N ∣ m₀
    · -- **SUBCASE B (`ψ₁.N ∣ m₀`)**: Deuring–Heilbronn kills ALL `s > 1` coprime to `m₀` (ZERO exceptions `s_exc = 0`!)
      set lam : ℝ := (1 - β₁) * L_M
      have hlam_pos : 0 < lam := mul_pos (by linarith) hLM_pos
      have hlam_lt : lam < δ_L := by
        dsimp only [lam]; rw [← lt_div_iff₀ hLM_pos]; linarith
      have hlam_c2 : lam ≤ c₂ / 4 := hlam_lt.le.trans hδL_c2
      have hRlam_eq : R * lam = (1 - β₁) * Real.log X := by
        dsimp only [R, lam]; field_simp [hLM_pos.ne']
      have h1mβ_ge : c_S / Real.sqrt (m₀ : ℝ) ≤ 1 - β₁ := by
        have hnot := hsiegel ψ₁.N ψ₁.χ ψ₁.prim hψ₁_sq hψ₁_ne1 β₁
        have hlt : β₁ < 1 - c_S / (ψ₁.N : ℝ) ^ (1 / 2 : ℝ) := by
          by_contra hge; push Not at hge; exact hnot hge hLψ₁_0
        have hN_le : (ψ₁.N : ℝ) ≤ (m₀ : ℝ) := by exact_mod_cast Nat.le_of_dvd (by omega) hψ₁_dvd
        have hrt : (ψ₁.N : ℝ) ^ (1 / 2 : ℝ) ≤ Real.sqrt (m₀ : ℝ) := by
          rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow (Nat.cast_nonneg _) hN_le (by norm_num)
        have hN_pos : (0 : ℝ) < (ψ₁.N : ℝ) := Nat.cast_pos.mpr (NeZero.pos ψ₁.N)
        have hdiv : c_S / Real.sqrt (m₀ : ℝ) ≤ c_S / (ψ₁.N : ℝ) ^ (1 / 2 : ℝ) :=
          div_le_div_of_nonneg_left hcS_pos.le (Real.rpow_pos_of_pos hN_pos _) hrt
        linarith
      have hmin_ge : c_S' / Real.sqrt (m₀ : ℝ) ≤ min 1 (R * lam) := by
        refine le_min ?_ ?_
        · calc c_S' / Real.sqrt (m₀ : ℝ) ≤ 1 / Real.sqrt (m₀ : ℝ) :=
                div_le_div_of_nonneg_right (min_le_left _ _) (Real.sqrt_nonneg _)
            _ ≤ 1 := div_le_one_of_le₀ (Real.le_sqrt_of_sq_le (by linarith)) (Real.sqrt_nonneg _)
        · rw [hRlam_eq]
          have hlogX_ge1 : 1 ≤ Real.log X := by
            have : Real.exp 1 ≤ X := by linarith [Real.exp_one_lt_d9]
            exact (Real.log_exp 1).symm.trans_le (Real.log_le_log (Real.exp_pos 1) this)
          calc c_S' / Real.sqrt (m₀ : ℝ) ≤ c_S / Real.sqrt (m₀ : ℝ) :=
                div_le_div_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _)
            _ ≤ 1 - β₁ := h1mβ_ge
            _ ≤ (1 - β₁) * Real.log X := le_mul_of_one_le_right (by linarith) hlogX_ge1
      have hW_min_ge_cS : (c_S' / 16) * X ^ 2 / ((m₀ : ℝ) ^ ((3 : ℝ) / 2)) ≤
          ((1 / 16 : ℝ) * min 1 (R * lam)) * X ^ 2 / (m₀.totient : ℝ) := by
        have hm32 : (m₀ : ℝ) ^ ((3 : ℝ) / 2) = (m₀ : ℝ) * Real.sqrt (m₀ : ℝ) := by
          rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hm₀_pos, Real.rpow_one]
        calc (c_S' / 16) * X ^ 2 / ((m₀ : ℝ) ^ ((3 : ℝ) / 2))
            = ((1 / 16 : ℝ) * (c_S' / Real.sqrt (m₀ : ℝ))) * X ^ 2 / (m₀ : ℝ) := by
                rw [hm32]; field_simp [hm₀_pos.ne', (Real.sqrt_pos.mpr hm₀_pos).ne']
          _ ≤ ((1 / 16 : ℝ) * min 1 (R * lam)) * X ^ 2 / (m₀ : ℝ) := by gcongr
          _ ≤ ((1 / 16 : ℝ) * min 1 (R * lam)) * X ^ 2 / (m₀.totient : ℝ) := by
              have hmin_nn : 0 ≤ min 1 (R * lam) := le_min zero_le_one (by positivity)
              exact div_le_div_of_nonneg_left (by positivity) htot_pos htot_le
      -- Shared Deuring–Heilbronn gap for any `(η mod m)` (`m ≤ Q_all`) and `ρ ∈ lZerosInBox η T₀` with `(PChar.of η ≠ ψ₁ ∨ ρ ≠ β₁)`!
      have hDH_gap : ∀ (m : ℕ) [NeZero m] (_hm : 2 ≤ m) (hmQ : m ≤ Q_all) (η : DirichletCharacter ℂ m)
          (ρ : ℂ), ρ ∈ Stage11LinnikBridge.lZerosInBox η T₀ →
          (PChar.of η ≠ ψ₁ ∨ ρ ≠ (β₁ : ℂ)) →
          (c₁ / 4) * Real.log (c₂ / lam) / L_M ≤ 1 - ρ.re := by
        intro m _ hm hmQ η ρ hρ hne
        have hm' := Stage11LinnikBridge.mem_lZerosInBox.mp hρ
        have : NeZero η.conductor := ⟨η.conductor_ne_zero⟩
        have hL_prim : DirichletCharacter.LFunction η.primitiveCharacter ρ = 0 := by
          by_cases hη1 : η = 1
          · subst hη1
            have hρ_ne1 : ρ ≠ 1 := fun h => by subst h; simp at hm'
            have hζ0 := (RHDirect.LFunction_trivChar_eq_zero_iff_riemannZeta_of_re_pos (N := m) hm'.1 hρ_ne1).mp hm'.2.2.1
            have hcond1 : (1 : DirichletCharacter ℂ m).conductor = 1 := DirichletCharacter.conductor_one
            have haux : ∀ (k : ℕ) [NeZero k] (χ : DirichletCharacter ℂ k), k = 1 →
                DirichletCharacter.LFunction χ ρ = riemannZeta ρ := by
              rintro _ _ χ rfl; rw [DirichletCharacter.level_one χ, DirichletCharacter.LFunction_modOne_eq]
            rw [haux _ _ hcond1]; exact hζ0
          · exact (RHDirect.LFunction_eq_zero_iff_primitive_of_re_pos η hm'.1 (.inl hη1)).mp hm'.2.2.1
        have hPeq : PChar.of η.primitiveCharacter = PChar.of η := PChar.of_self (PChar.of η)
        have hPeq1 : PChar.of ψ₁.χ = ψ₁ := PChar.of_self ψ₁
        have hcond_le : (η.conductor : ℝ) ≤ (Q_all : ℝ) := by
          exact_mod_cast (Nat.le_of_dvd (NeZero.pos m) η.conductor_dvd_level).trans hmQ
        have hψ₁_le : (ψ₁.N : ℝ) ≤ (Q_all : ℝ) := by exact_mod_cast hψ₁_leQ
        have harg_le : (η.conductor : ℝ) * (ψ₁.N : ℝ) * T₀ ≤ M ^ 2 := by
          have h1 : (η.conductor : ℝ) * (ψ₁.N : ℝ) * T₀ ≤ (Q_all : ℝ) * (Q_all : ℝ) * T₀ := by gcongr
          have h2 : (Q_all : ℝ) * (Q_all : ℝ) * T₀ ≤ ((Q_all : ℝ) * (T₀ + 2)) ^ 2 := by
            have hTsq : T₀ ≤ (T₀ + 2) ^ 2 := by nlinarith only [hT0_ge4]
            nlinarith only [hTsq, sq_nonneg (Q_all : ℝ)]
          exact h1.trans h2
        have harg_pos : 0 < (η.conductor : ℝ) * (ψ₁.N : ℝ) * T₀ := by
          have h1 : (0 : ℝ) < (η.conductor : ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
          have h2 : (0 : ℝ) < (ψ₁.N : ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
          positivity
        have hlog_arg_pos : 0 < Real.log ((η.conductor : ℝ) * (ψ₁.N : ℝ) * T₀) := by
          have h1 : (1 : ℝ) ≤ (η.conductor : ℝ) := Nat.one_le_cast.mpr (Nat.succ_le_of_lt (NeZero.pos _))
          have h2 : (1 : ℝ) ≤ (ψ₁.N : ℝ) := Nat.one_le_cast.mpr (Nat.succ_le_of_lt (NeZero.pos _))
          have h12 : (1 : ℝ) ≤ (η.conductor : ℝ) * (ψ₁.N : ℝ) := one_le_mul_of_one_le_of_one_le h1 h2
          exact Real.log_pos (by nlinarith only [h12, hT0_ge4])
        have hlog_arg_le : Real.log ((η.conductor : ℝ) * (ψ₁.N : ℝ) * T₀) ≤ 2 * L_M := by
          calc Real.log ((η.conductor : ℝ) * (ψ₁.N : ℝ) * T₀)
              ≤ Real.log (M ^ 2) := Real.log_le_log harg_pos harg_le
            _ = 2 * L_M := by rw [Real.log_pow]; push_cast; rfl
        have h1mβ_lt : 1 - β₁ < c₂ / Real.log ((η.conductor : ℝ) * (ψ₁.N : ℝ) * T₀) := by
          have h1 : δ_L / L_M ≤ c₂ / (2 * L_M) := by
            calc δ_L / L_M ≤ (c₂ / 4) / L_M := div_le_div_of_nonneg_right hδL_c2 hLM_pos.le
              _ ≤ (c₂ / 2) / L_M := div_le_div_of_nonneg_right (by linarith) hLM_pos.le
              _ = c₂ / (2 * L_M) := by ring
          have h2 : c₂ / (2 * L_M) ≤ c₂ / Real.log ((η.conductor : ℝ) * (ψ₁.N : ℝ) * T₀) :=
            div_le_div_of_nonneg_left hc₂_pos.le hlog_arg_pos hlog_arg_le
          linarith
        have hdh_raw := hdh ψ₁.N ψ₁.χ ψ₁.prim hψ₁_sq hψ₁_ne1 β₁ hβ₁_gt_half hβ₁_hi hLψ₁_0
          η.conductor η.primitiveCharacter η.primitiveCharacter_isPrimitive ρ hm'.1 hm'.2.1 hL_prim
          (by rwa [hPeq, hPeq1]) T₀ (by linarith) hm'.2.2.2 h1mβ_lt
        have hlog_mono : Real.log (c₂ / (2 * lam)) ≤ Real.log (c₂ / ((1 - β₁) * Real.log ((η.conductor : ℝ) * (ψ₁.N : ℝ) * T₀))) := by
          refine Real.log_le_log (by positivity) (div_le_div_of_nonneg_left hc₂_pos.le (mul_pos (by linarith) hlog_arg_pos) ?_)
          have : (1 - β₁) * Real.log ((η.conductor : ℝ) * (ψ₁.N : ℝ) * T₀) ≤ (1 - β₁) * (2 * L_M) :=
            mul_le_mul_of_nonneg_left hlog_arg_le (by linarith)
          dsimp only [lam]; linarith
        have hlog_half : (1 / 2 : ℝ) * Real.log (c₂ / lam) ≤ Real.log (c₂ / (2 * lam)) := by
          have h4_le : (4 : ℝ) ≤ c₂ / lam := by rw [le_div_iff₀ hlam_pos]; linarith
          have hlog4 : 2 * Real.log 2 ≤ Real.log (c₂ / lam) := by
            have h1 : Real.log (2 ^ 2 : ℝ) ≤ Real.log (c₂ / lam) := Real.log_le_log (by norm_num) (by norm_num; exact h4_le)
            rwa [Real.log_pow, Nat.cast_ofNat] at h1
          have hEq : c₂ / (2 * lam) = (c₂ / lam) / 2 := by ring
          conv_rhs => rw [hEq, Real.log_div (by positivity) (by norm_num)]
          linarith
        calc (c₁ / 4) * Real.log (c₂ / lam) / L_M
            = c₁ * ((1 / 2 : ℝ) * Real.log (c₂ / lam)) / (2 * L_M) := by ring
          _ ≤ c₁ * Real.log (c₂ / (2 * lam)) / (2 * L_M) := by gcongr
          _ ≤ c₁ * Real.log (c₂ / ((1 - β₁) * Real.log ((η.conductor : ℝ) * (ψ₁.N : ℝ) * T₀))) /
                Real.log ((η.conductor : ℝ) * (ψ₁.N : ℝ) * T₀) := by
              have hnn_log : 0 ≤ Real.log (c₂ / (2 * lam)) :=
                Real.log_nonneg ((one_le_div (by positivity)).mpr (by linarith))
              exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlog_mono hc₁_pos.le) (by positivity)).trans
                (div_le_div_of_nonneg_left (mul_nonneg hc₁_pos.le (hnn_log.trans hlog_mono)) hlog_arg_pos hlog_arg_le)
          _ ≤ 1 - ρ.re := hdh_raw
      -- Exponential decay constant from `dh_exp_decay_le` with `c₁ / 4`:
      have hDH_decay :
          (1 / 2 : ℝ) * C_D * Real.exp A * Real.exp (-(R / 2) * ((c₁ / 4) * Real.log (c₂ / lam))) ≤
            (1 / (64 * Z ^ 2)) * min 1 (R * lam) := by
        refine dh_exp_decay_le hCD_pos (by positivity : 0 < c₁ / 4) hc₂_pos hZ4 hBrt_ge hBrt_ge1
          hlam_pos hlam_c2 ?_ ?_ (by linarith)
        · have hEq : 4 / (c₁ / 4) = 16 / c₁ := by field_simp [hc₁_pos.ne']; ring
          rw [hEq]
          exact (mul_le_mul_of_nonneg_right hR0_c2 (by linarith)).trans hR_ge
        · have hEq : 16 / (c₁ / 4) = 64 / c₁ := by field_simp [hc₁_pos.ne']; ring
          rw [hEq]
          exact (mul_le_mul_of_nonneg_right hR0_64c1 (by linarith)).trans hR_ge
      -- First prove `W ≥ ((1/16) * min 1 (R * lam)) * X^2 / φ(m₀)` (by splitting on whether `ψ₁` lifts to `m₀`!)
      have hW_subB : ((1 / 16 : ℝ) * min 1 (R * lam)) * X ^ 2 / (m₀.totient : ℝ) ≤
          ∑ r ∈ apPrimes m₀ a₀ X, tentWt X r := by
        by_cases hHas : ∃ χ₀ : DirichletCharacter ℂ m₀, PChar.of χ₀ = ψ₁
        · obtain ⟨χ₀, hPχ₀⟩ := hHas
          have huniq : ∀ χ : DirichletCharacter ℂ m₀, PChar.of χ = ψ₁ → χ = χ₀ := by
            intro χ hP
            have heq : PChar.of χ = PChar.of χ₀ := hP.trans hPχ₀.symm
            ext u
            have hnat : (((u : ZMod m₀).val : ℕ) : ZMod m₀) = (u : ZMod m₀) := ZMod.natCast_zmod_val _
            have h1 := DirichletCharacter.changeLevel_eq_cast_of_dvd χ.primitiveCharacter χ.conductor_dvd_level u
            have h2 := DirichletCharacter.changeLevel_eq_cast_of_dvd χ₀.primitiveCharacter χ₀.conductor_dvd_level u
            rw [χ.changeLevel_primitiveCharacter] at h1
            rw [χ₀.changeLevel_primitiveCharacter] at h2
            rw [h1, h2, ← hnat, ZMod.cast_natCast χ.conductor_dvd_level, ZMod.cast_natCast χ₀.conductor_dvd_level]
            exact congrArg (fun P : PChar => P.χ ((u : ZMod m₀).val : ZMod P.N)) heq
          have hχ₀_ne1 : χ₀ ≠ 1 := fun h1 => hψ₁_ne1 (by
            have hP1 : (PChar.of χ₀).N = 1 := by simp [PChar.of, h1, DirichletCharacter.conductor_one]
            rw [hPχ₀] at hP1
            have haux : ∀ (k : ℕ) [NeZero k] (χ : DirichletCharacter ℂ k), k = 1 → χ = 1 := by
              rintro _ _ χ rfl; exact DirichletCharacter.level_one χ
            exact haux ψ₁.N ψ₁.χ hP1)
          have hLχ₀_0 : DirichletCharacter.LFunction χ₀ (β₁ : ℂ) = 0 := by
            have hLp : DirichletCharacter.LFunction (PChar.of χ₀).χ (β₁ : ℂ) = 0 := hPχ₀ ▸ hLψ₁_0
            exact (RHDirect.LFunction_eq_zero_iff_primitive_of_re_pos χ₀ (by simp; linarith) (.inl hχ₀_ne1)).mpr hLp
          have hmult1 : Stage11LinnikBridge.lZeroMult χ₀ (β₁ : ℂ) = 1 := by
            have hψ₁_pos : (0 : ℝ) < (ψ₁.N : ℝ) := Nat.cast_pos.mpr (NeZero.pos ψ₁.N)
            have hlog2q₁_le : Real.log (2 * (ψ₁.N : ℝ)) ≤ L_M :=
              Real.log_le_log (by positivity) (by dsimp only [M]; nlinarith only [hT0_ge4, hQ0, show (ψ₁.N : ℝ) ≤ (Q_all : ℝ) by exact_mod_cast hψ₁_leQ])
            have hq₁_ge2 : (2 : ℝ) ≤ (ψ₁.N : ℝ) := by
              by_contra hlt; push Not at hlt
              have hN1 : ψ₁.N = 1 := by
                have hpos := NeZero.pos ψ₁.N
                have hlt2 : ψ₁.N < 2 := by exact_mod_cast hlt
                omega
              have haux : ∀ (k : ℕ) [NeZero k] (χ : DirichletCharacter ℂ k), k = 1 → χ = 1 := by
                rintro _ _ χ rfl; exact DirichletCharacter.level_one χ
              exact hψ₁_ne1 (haux ψ₁.N ψ₁.χ hN1)
            have hlog2q₁_pos : 0 < Real.log (2 * (ψ₁.N : ℝ)) := Real.log_pos (by linarith)
            have hβ_simp : 1 - c_simp / Real.log (2 * (ψ₁.N : ℝ)) ≤ β₁ := by
              have h1 : δ_L / L_M ≤ c_simp / Real.log (2 * (ψ₁.N : ℝ)) :=
                (div_le_div_of_nonneg_right (hδL_simp.trans (by linarith)) hLM_pos.le).trans
                  (div_le_div_of_nonneg_left hcsimp_pos.le hlog2q₁_pos hlog2q₁_le)
              linarith
            have hs1 := hsimp ψ₁.N ψ₁.χ ψ₁.prim hψ₁_ne1 hψ₁_sq β₁ hβ_simp hLψ₁_0
            have heq_m := lZeroMult_eq_primitive_local hχ₀_ne1 (by simp; linarith : 0 < (β₁ : ℂ).re)
            have heq_p : Stage11LinnikBridge.lZeroMult (PChar.of χ₀).χ (β₁ : ℂ) = Stage11LinnikBridge.lZeroMult ψ₁.χ (β₁ : ℂ) := by
              rw [hPχ₀]
            exact heq_m.trans (heq_p.trans hs1)
          have hβ₁_mem : (β₁ : ℂ) ∈ (Stage11LinnikBridge.lZerosInBox χ₀ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re) :=
            Finset.mem_filter.mpr ⟨Stage11LinnikBridge.mem_lZerosInBox.mpr
              ⟨by simp; linarith, by simp [hβ₁_hi], hLχ₀_0, by simp; linarith⟩, by rw [Complex.ofReal_re]; exact hβ₁_gt_half.le⟩
          -- Right-half sum over ALL `(χ, ρ) ≠ (χ₀, β₁)` bounded by `((1/64 Z^2) * min 1 (R * lam)) * X^2`
          set L0 := Real.log ((m₀ : ℝ) * (T₀ + 2))
          have hL0_pos : 0 < L0 := Real.log_pos (by nlinarith only [hm₀R, hT0_ge4])
          have hL0_le : L0 ≤ L_M := Real.log_le_log (by positivity) (by dsimp only [M]; gcongr)
          have hRm0 : max (2 * A) 2 ≤ Real.log X / L0 := by
            have h1 : R ≤ Real.log X / L0 := div_le_div_of_nonneg_left (Real.log_nonneg hX1) hL0_pos hL0_le
            have h2 : max (2 * A) 2 ≤ R₀ := max_le hR0_2A (by linarith)
            linarith
          set lam_dh : ℝ := ((c₁ / 4) * Real.log (c₂ / lam)) * (L0 / L_M)
          have hlam_dh_nn : 0 ≤ lam_dh := by
            have hlog_nn : 0 ≤ Real.log (c₂ / lam) := Real.log_nonneg ((one_le_div hlam_pos).mpr (by linarith))
            dsimp only [lam_dh]; positivity
          let bad0 : DirichletCharacter ℂ m₀ → ℂ → Prop := fun χ ρ => ¬ (χ = χ₀ ∧ ρ = (β₁ : ℂ))
          have hgap0 : ∀ (χ : DirichletCharacter ℂ m₀) (ρ : ℂ),
              ρ ∈ Stage11LinnikBridge.lZerosInBox χ T₀ → 1 / 2 ≤ ρ.re → bad0 χ ρ →
              lam_dh / L0 ≤ 1 - ρ.re := fun χ ρ hρ _ hbad => by
            have hne : PChar.of χ ≠ ψ₁ ∨ ρ ≠ (β₁ : ℂ) := by
              by_cases hP : PChar.of χ = ψ₁
              · right; intro hρeq; exact hbad ⟨huniq χ hP, hρeq⟩
              · exact Or.inl hP
            have h1 := hDH_gap m₀ hm₀ hm₀_le_Q χ ρ hρ hne
            have hEq : lam_dh / L0 = (c₁ / 4) * Real.log (c₂ / lam) / L_M := by
              dsimp only [lam_dh]; field_simp [hL0_pos.ne', hLM_pos.ne']
            rwa [hEq]
          have hlf0 := Stage11LinnikBridge.sum_right_half_zeros_le_of_logfree hCD_pos hA_ge1 hlf hm₀ (by linarith) hX4
            hlam_dh_nn bad0 hgap0 hRm0
          have hExp_eq : -(Real.log X / L0 / 2) * lam_dh = -(R / 2) * ((c₁ / 4) * Real.log (c₂ / lam)) := by
            dsimp only [lam_dh, R]; field_simp [hL0_pos.ne', hLM_pos.ne']
          rw [hExp_eq] at hlf0
          -- Isolate the single Siegel term `(χ₀, β₁)` from the sum
          have hsum_split :
              (∑ χ : DirichletCharacter ℂ m₀, starRingEnd ℂ (χ (a₀ : ZMod m₀)) *
                ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re),
                  (Stage11LinnikBridge.lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ) =
              (starRingEnd ℂ (χ₀ (a₀ : ZMod m₀)) * ((X : ℂ) ^ ((β₁ : ℂ) + 1) * Stage11LinnikBridge.dyadicKernel (β₁ : ℂ))) +
              (∑ χ : DirichletCharacter ℂ m₀, starRingEnd ℂ (χ (a₀ : ZMod m₀)) *
                ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ bad0 χ ρ),
                  (Stage11LinnikBridge.lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ) := by
            have hterm : ∀ χ : DirichletCharacter ℂ m₀,
                starRingEnd ℂ (χ (a₀ : ZMod m₀)) *
                  ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re),
                    (Stage11LinnikBridge.lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ =
                (if χ = χ₀ then starRingEnd ℂ (χ₀ (a₀ : ZMod m₀)) * ((X : ℂ) ^ ((β₁ : ℂ) + 1) * Stage11LinnikBridge.dyadicKernel (β₁ : ℂ)) else 0) +
                starRingEnd ℂ (χ (a₀ : ZMod m₀)) *
                  ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ bad0 χ ρ),
                    (Stage11LinnikBridge.lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ := by
              intro χ
              by_cases hχ : χ = χ₀
              · subst hχ
                rw [if_pos rfl]
                have herase : (Stage11LinnikBridge.lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ bad0 χ ρ) =
                    ((Stage11LinnikBridge.lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re)).erase (β₁ : ℂ) := by
                  ext ρ; simp only [Finset.mem_filter, Finset.mem_erase, bad0]; tauto
                rw [herase, ← Finset.add_sum_erase _ _ hβ₁_mem, hmult1, Nat.cast_one, one_mul]; ring
              · rw [if_neg hχ, zero_add]
                congr 2; ext ρ; simp only [Finset.mem_filter, bad0]; exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2, fun h => hχ h.1⟩, fun ⟨h1, h2, _⟩ => ⟨h1, h2⟩⟩
            simp_rw [hterm, Finset.sum_add_distrib]
            congr 1; simp
          have hRest_re :
              (∑ χ : DirichletCharacter ℂ m₀, starRingEnd ℂ (χ (a₀ : ZMod m₀)) *
                ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ bad0 χ ρ),
                  (Stage11LinnikBridge.lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ).re ≤
                ((1 / 32 : ℝ) * min 1 (R * lam)) * X ^ 2 := by
            have h16 : (1 / (64 * Z ^ 2) : ℝ) ≤ 1 / 32 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith only [hZ4]
            have hmin_nn : 0 ≤ min 1 (R * lam) := le_min zero_le_one (by positivity)
            have hre_bd := re_sum_right_half_le_of_logfree_sum (a₀ := a₀) hX0 bad0 hlf0
            calc _ ≤ ((1 / 4 : ℝ) * X ^ 2) * (2 * C_D * Real.exp A * Real.exp (-(R / 2) * ((c₁ / 4) * Real.log (c₂ / lam)))) := hre_bd
              _ = ((1 / 2 : ℝ) * C_D * Real.exp A * Real.exp (-(R / 2) * ((c₁ / 4) * Real.log (c₂ / lam)))) * X ^ 2 := by ring
              _ ≤ ((1 / (64 * Z ^ 2)) * min 1 (R * lam)) * X ^ 2 := mul_le_mul_of_nonneg_right hDH_decay (sq_nonneg X)
              _ ≤ ((1 / 32 : ℝ) * min 1 (R * lam)) * X ^ 2 :=
                  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h16 hmin_nn) (sq_nonneg X)
          -- Main-minus-Siegel lower bound via `siegel_main_sub_kernel_ge` + `half_min_le_one_sub_exp_neg`
          have hSiegel_main :
              ((1 / 8 : ℝ) * min 1 (R * lam)) * X ^ 2 ≤
                (1 / 4 : ℝ) * X ^ 2 - (starRingEnd ℂ (χ₀ (a₀ : ZMod m₀)) *
                  ((X : ℂ) ^ ((β₁ : ℂ) + 1) * Stage11LinnikBridge.dyadicKernel (β₁ : ℂ))).re := by
            have hc1 : ‖starRingEnd ℂ (χ₀ (a₀ : ZMod m₀))‖ ≤ 1 := by rw [Complex.norm_conj]; exact χ₀.norm_le_one _
            have hsm := Stage11LinnikBridge.siegel_main_sub_kernel_ge (by linarith : 0 < β₁) hβ₁_hi hX1 hc1
            have hrew : starRingEnd ℂ (χ₀ (a₀ : ZMod m₀)) * ((X : ℂ) ^ ((β₁ : ℂ) + 1) * Stage11LinnikBridge.dyadicKernel (β₁ : ℂ)) =
                starRingEnd ℂ (χ₀ (a₀ : ZMod m₀)) * (X : ℂ) ^ ((β₁ : ℂ) + 1) * Stage11LinnikBridge.dyadicKernel (β₁ : ℂ) := by ring
            rw [hrew]
            have hXpow : X ^ (β₁ - 1) = Real.exp (-(R * lam)) := by
              rw [Real.rpow_def_of_pos hX0, hRlam_eq]; congr 1; ring
            have hhalf := half_min_le_one_sub_exp_neg (show 0 ≤ R * lam by positivity)
            rw [← hXpow] at hhalf
            calc ((1 / 8 : ℝ) * min 1 (R * lam)) * X ^ 2
                = (1 / 4 : ℝ) * X ^ 2 * ((1 / 2 : ℝ) * min 1 (R * lam)) := by ring
              _ ≤ (1 / 4 : ℝ) * X ^ 2 * (1 - X ^ (β₁ - 1)) := mul_le_mul_of_nonneg_left hhalf (by positivity)
              _ ≤ _ := hsm
          have hre_ef : Stage11LinnikBridge.dyadic2Real (Stage11LinnikBridge.psi1AP m₀ a₀) X ≥
              (m₀.totient : ℝ)⁻¹ * (((1 / 8 : ℝ) * min 1 (R * lam)) * X ^ 2 - ((1 / 32 : ℝ) * min 1 (R * lam)) * X ^ 2) -
              (c_S' / (1024 * (Q_all : ℝ) ^ 2)) * X ^ 2 := by
            have h1 := (abs_le.mp ((Complex.abs_re_le_norm _).trans hsum_ef_m0)).1
            rw [Complex.sub_re, Complex.ofReal_re, Complex.mul_re] at h1
            have hinv_re : ((m₀.totient : ℂ)⁻¹).re = (m₀.totient : ℝ)⁻¹ := by
              rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]
            have hinv_im : ((m₀.totient : ℂ)⁻¹).im = 0 := by
              rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_im]
            rw [hinv_re, hinv_im, zero_mul, sub_zero, Complex.sub_re, hsum_split, Complex.add_re] at h1
            have hq_re : ((1 / 4 : ℂ) * (X : ℂ) ^ 2).re = (1 / 4 : ℝ) * X ^ 2 := by
              rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
            rw [hq_re] at h1
            have hsub_ge : ((1 / 8 : ℝ) * min 1 (R * lam)) * X ^ 2 - ((1 / 32 : ℝ) * min 1 (R * lam)) * X ^ 2 ≤
                (1 / 4 : ℝ) * X ^ 2 - ((starRingEnd ℂ (χ₀ (a₀ : ZMod m₀)) *
                  ((X : ℂ) ^ ((β₁ : ℂ) + 1) * Stage11LinnikBridge.dyadicKernel (β₁ : ℂ))).re +
                  (∑ χ : DirichletCharacter ℂ m₀, starRingEnd ℂ (χ (a₀ : ZMod m₀)) *
                    ∑ ρ ∈ (Stage11LinnikBridge.lZerosInBox χ T₀).filter (fun ρ => 1 / 2 ≤ ρ.re ∧ bad0 χ ρ),
                      (Stage11LinnikBridge.lZeroMult χ ρ : ℂ) * (X : ℂ) ^ (ρ + 1) * Stage11LinnikBridge.dyadicKernel ρ).re) := by
              linarith [hSiegel_main, hRest_re]
            have h2 := mul_le_mul_of_nonneg_left hsub_ge (inv_nonneg.mpr htot_pos.le)
            linarith
          have herr_sm : (c_S' / (512 * (Q_all : ℝ) ^ 2)) * X ^ 2 ≤
              ((1 / 32 : ℝ) * min 1 (R * lam)) * X ^ 2 / (m₀.totient : ℝ) := by
            have hZ1 : (1 / (4 * Z ^ 2) : ℝ) ≤ 1 / 2 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith only [hZ4]
            calc (c_S' / (512 * (Q_all : ℝ) ^ 2)) * X ^ 2
                ≤ (1 / (4 * Z ^ 2)) * ((c_S' / 16) * X ^ 2 / ((m₀ : ℝ) ^ ((3 : ℝ) / 2))) := hErr_vs_W
              _ ≤ (1 / 2 : ℝ) * (((1 / 16 : ℝ) * min 1 (R * lam)) * X ^ 2 / (m₀.totient : ℝ)) :=
                  mul_le_mul hZ1 hW_min_ge_cS (by positivity) (by norm_num)
              _ = ((1 / 32 : ℝ) * min 1 (R * lam)) * X ^ 2 / (m₀.totient : ℝ) := by ring
          have hW_ge := tentWt_apPrimes_ge_sub_nonprime (m₀ := m₀) (a₀ := a₀) hX1
          have h2x : (c_S' / (1024 * (Q_all : ℝ) ^ 2)) * X ^ 2 + (c_S' / (1024 * (Q_all : ℝ) ^ 2)) * X ^ 2 =
              (c_S' / (512 * (Q_all : ℝ) ^ 2)) * X ^ 2 := by field_simp [hQ0.ne']; ring
          have hmain_eq : (m₀.totient : ℝ)⁻¹ * (((1 / 8 : ℝ) * min 1 (R * lam)) * X ^ 2 -
              ((1 / 32 : ℝ) * min 1 (R * lam)) * X ^ 2) =
              (3 / 32 : ℝ) * (min 1 (R * lam) * X ^ 2 / (m₀.totient : ℝ)) := by ring
          have herr_sm' : (c_S' / (512 * (Q_all : ℝ) ^ 2)) * X ^ 2 ≤
              (1 / 32 : ℝ) * (min 1 (R * lam) * X ^ 2 / (m₀.totient : ℝ)) := by
            linarith [herr_sm, show ((1 / 32 : ℝ) * min 1 (R * lam)) * X ^ 2 / (m₀.totient : ℝ) =
              (1 / 32 : ℝ) * (min 1 (R * lam) * X ^ 2 / (m₀.totient : ℝ)) by ring]
          have hgoal_eq : ((1 / 16 : ℝ) * min 1 (R * lam)) * X ^ 2 / (m₀.totient : ℝ) =
              (1 / 16 : ℝ) * (min 1 (R * lam) * X ^ 2 / (m₀.totient : ℝ)) := by ring
          linarith only [hW_ge, hre_ef, hNonPrime_bd, herr_sm', h2x, hmain_eq, hgoal_eq]
        · -- `¬ hHas`: no `χ mod m₀` has `PChar.of χ = ψ₁` → `hMain_noSiegel` applies directly!
          push Not at hHas
          have hno_m0 : ∀ (χ : DirichletCharacter ℂ m₀) (β : ℝ), 1 - δ_L / L_M < β → β < 1 →
              DirichletCharacter.LFunction χ (β : ℂ) ≠ 0 := by
            intro χ β hβ_lo hβ_hi hzero
            have hβ_pos : 0 < β := by have : δ_L / L_M ≤ 1 / 4 := (div_le_self hδL_pos.le hLM_gt1.le).trans hδL_qtr; linarith
            have hχ_ne1 : χ ≠ 1 := by
              intro h1; subst h1
              have hβ_ne1 : (β : ℂ) ≠ 1 := fun h => by have := congrArg Complex.re h; simp at this; linarith
              have hζ0 := (RHDirect.LFunction_trivChar_eq_zero_iff_riemannZeta_of_re_pos (N := m₀) (by simpa using hβ_pos) hβ_ne1).mp hzero
              have hneg := Stage9LandauSiegel.riemannZeta_neg_on_Ioo hβ_pos hβ_hi
              have := congrArg Complex.re hζ0; simp at this; linarith [hneg.1]
            have hL_p : DirichletCharacter.LFunction (PChar.of χ).χ (β : ℂ) = 0 :=
              (RHDirect.LFunction_eq_zero_iff_primitive_of_re_pos χ (by simpa using hβ_pos) (.inl hχ_ne1)).mp hzero
            have hβ_pg : 1 - c_P / Real.log (2 * (Q_all : ℝ)) < β := by
              have h1 : δ_L / L_M ≤ c_P / Real.log (2 * (Q_all : ℝ)) :=
                (div_le_div_of_nonneg_right (hδL_cP.trans (by linarith)) hLM_pos.le).trans
                  (div_le_div_of_nonneg_left hcP_pos.le hlog2Q_pos hlog2Q_le)
              linarith
            have hcond_leQ : (PChar.of χ).N ≤ Q_all := (Nat.le_of_dvd (by omega) χ.conductor_dvd_level).trans hm₀_le_Q
            exact hHas χ (hpage2 Q_all (hm₀.trans hm₀_le_Q) (PChar.of χ) ψ₁ β β₁ hcond_leQ hψ₁_leQ hL_p hLψ₁_0 hβ_pg hβ₁_page).1
          have hW_full := hMain_noSiegel hno_m0
          have hle1 : ((1 / 16 : ℝ) * min 1 (R * lam)) * X ^ 2 / (m₀.totient : ℝ) ≤ (1 / 16 : ℝ) * X ^ 2 / (m₀.totient : ℝ) := by
            have h1 : min 1 (R * lam) ≤ 1 := min_le_left _ _
            have hnn : 0 ≤ (1 / 16 : ℝ) * X ^ 2 / (m₀.totient : ℝ) := by positivity
            calc ((1 / 16 : ℝ) * min 1 (R * lam)) * X ^ 2 / (m₀.totient : ℝ)
                = min 1 (R * lam) * ((1 / 16 : ℝ) * X ^ 2 / (m₀.totient : ℝ)) := by ring
              _ ≤ 1 * ((1 / 16 : ℝ) * X ^ 2 / (m₀.totient : ℝ)) := mul_le_mul_of_nonneg_right h1 hnn
              _ = _ := one_mul _
          exact hle1.trans hW_full
      -- Now bound ALL twists `s > 1` (`Coprime s m₀, s ≤ Z^2`) with ZERO exceptions (`s_exc = 0`)!
      refine ⟨hW_min_ge_cS.trans hW_subB, 0, fun s hs1 hs_odd hs_sqf hcop_sm hs_le _ => ?_⟩
      have : NeZero s := ⟨by omega⟩
      have hms_ge2 : 2 ≤ m₀ * s := hm₀.trans (Nat.le_mul_of_pos_right m₀ (by omega))
      have hms_leQ : m₀ * s ≤ Q_all := Nat.mul_le_mul_left m₀ ((Nat.le_floor hs_le).trans (Nat.le_succ _))
      have hχs_prim := quadCharOfOddSqf_isPrimitive hs_odd hs_sqf
      set Ls := Real.log (((m₀ * s : ℕ) : ℝ) * (T₀ + 2))
      have hLs_pos : 0 < Ls := by
        have h2 : (2 : ℝ) ≤ ((m₀ * s : ℕ) : ℝ) := by exact_mod_cast hms_ge2
        exact Real.log_pos (by nlinarith only [h2, hT0_ge4])
      have hLs_le : Ls ≤ L_M := Real.log_le_log (by positivity) (by dsimp only [M]; gcongr)
      have hRs : max (2 * A) 2 ≤ Real.log X / Ls := by
        have h1 : R ≤ Real.log X / Ls := div_le_div_of_nonneg_left (Real.log_nonneg hX1) hLs_pos hLs_le
        have h2 : max (2 * A) 2 ≤ R₀ := max_le hR0_2A (by linarith)
        linarith
      set lam_dh_s : ℝ := ((c₁ / 4) * Real.log (c₂ / lam)) * (Ls / L_M)
      have hlam_dh_s_nn : 0 ≤ lam_dh_s := by
        have hlog_nn : 0 ≤ Real.log (c₂ / lam) := Real.log_nonneg ((one_le_div hlam_pos).mpr (by linarith))
        dsimp only [lam_dh_s]; positivity
      have hgap_s : ∀ (χ : DirichletCharacter ℂ m₀) (ρ : ℂ),
          ρ ∈ Stage11LinnikBridge.lZerosInBox
            (Stage11SecondMomentFrame.twistedChar χ (quadCharOfOddSqf s hs_odd)) T₀ →
          1 / 2 ≤ ρ.re → lam_dh_s / Ls ≤ 1 - ρ.re := fun χ ρ hρ _ => by
        have hne_ψ₁ : PChar.of (Stage11SecondMomentFrame.twistedChar χ (quadCharOfOddSqf s hs_odd)) ≠ ψ₁ := by
          intro heq
          have hs_dvd : s ∣ (Stage11SecondMomentFrame.twistedChar χ (quadCharOfOddSqf s hs_odd)).conductor :=
            right_dvd_conductor_twistedChar hcop_sm.symm χ hχs_prim
          have hN_eq : (Stage11SecondMomentFrame.twistedChar χ (quadCharOfOddSqf s hs_odd)).conductor = ψ₁.N :=
            congrArg PChar.N heq
          have hs_m0 : s ∣ m₀ := (hN_eq ▸ hs_dvd).trans hψ₁_dvd
          have hs1' : s = 1 := Nat.dvd_one.mp (hcop_sm.gcd_eq_one ▸ Nat.dvd_gcd dvd_rfl hs_m0)
          omega
        have h1 := hDH_gap (m₀ * s) hms_ge2 hms_leQ _ ρ hρ (Or.inl hne_ψ₁)
        have hEq : lam_dh_s / Ls = (c₁ / 4) * Real.log (c₂ / lam) / L_M := by
          dsimp only [lam_dh_s]; field_simp [hLs_pos.ne', hLM_pos.ne']
        rwa [hEq]
      have hrh := norm_twisted_right_half_le_of_logfree (a₀ := a₀) hCD_pos hA_ge1 hlf hm₀ hcop_sm.symm hs_odd
        (by linarith) hX4 hlam_dh_s_nn hgap_s hRs
      have hExp_eq : -(Real.log X / Ls / 2) * lam_dh_s = -(R / 2) * ((c₁ / 4) * Real.log (c₂ / lam)) := by
        dsimp only [lam_dh_s, R]; field_simp [hLs_pos.ne', hLM_pos.ne']
      rw [hExp_eq] at hrh
      have htw := hTwist_of_rh s hs1 hs_odd hs_sqf hcop_sm hs_le ((1 / (64 * Z ^ 2)) * min 1 (R * lam))
        (hrh.trans (mul_le_mul_of_nonneg_right hDH_decay (sq_nonneg X)))
      have h1 : (((1 / (64 * Z ^ 2)) * min 1 (R * lam)) / (m₀.totient : ℝ)) * X ^ 2 =
          (1 / (4 * Z ^ 2)) * (((1 / 16 : ℝ) * min 1 (R * lam)) * X ^ 2 / (m₀.totient : ℝ)) := by
        field_simp [hZ0.ne', htot_pos.ne']; ring
      have h2 : (c_S' / (512 * (Q_all : ℝ) ^ 2)) * X ^ 2 ≤
          (1 / (4 * Z ^ 2)) * (((1 / 16 : ℝ) * min 1 (R * lam)) * X ^ 2 / (m₀.totient : ℝ)) :=
        hErr_vs_W.trans (mul_le_mul_of_nonneg_left hW_min_ge_cS (by positivity))
      have h3 : (1 / (4 * Z ^ 2) + 1 / (4 * Z ^ 2)) * (((1 / 16 : ℝ) * min 1 (R * lam)) * X ^ 2 / (m₀.totient : ℝ)) ≤
          (1 / Z ^ 2) * ∑ r ∈ apPrimes m₀ a₀ X, tentWt X r := by
        have hhalf : (1 / (4 * Z ^ 2) + 1 / (4 * Z ^ 2) : ℝ) ≤ 1 / Z ^ 2 := by
          have : (1 / (4 * Z ^ 2) + 1 / (4 * Z ^ 2) : ℝ) = (1 / 2) * (1 / Z ^ 2) := by ring
          linarith [show (0 : ℝ) < 1 / Z ^ 2 by positivity]
        have hmin_nn : 0 ≤ min 1 (R * lam) := le_min zero_le_one (by positivity)
        exact mul_le_mul hhalf hW_subB (by positivity) (by positivity)
      linarith [htw, h1, h2, h3]
    · -- **SUBCASE C (`¬ ψ₁.N ∣ m₀`)**: `s_exc := ∏ p ∈ ψ₁.N.primeFactors.filter (fun p => ¬ p ∣ m₀), p`!
      have hno_m0 : ∀ (χ : DirichletCharacter ℂ m₀) (β : ℝ), 1 - δ_L / L_M < β → β < 1 →
          DirichletCharacter.LFunction χ (β : ℂ) ≠ 0 := by
        intro χ β hβ_lo hβ_hi hzero
        have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
        have hβ_pos : 0 < β := by have : δ_L / L_M ≤ 1 / 4 := (div_le_self hδL_pos.le hLM_gt1.le).trans hδL_qtr; linarith
        have hχ_ne1 : χ ≠ 1 := by
          intro h1; subst h1
          have hβ_ne1 : (β : ℂ) ≠ 1 := fun h => by have := congrArg Complex.re h; simp at this; linarith
          have hζ0 := (RHDirect.LFunction_trivChar_eq_zero_iff_riemannZeta_of_re_pos (N := m₀) (by simpa using hβ_pos) hβ_ne1).mp hzero
          have hneg := Stage9LandauSiegel.riemannZeta_neg_on_Ioo hβ_pos hβ_hi
          have := congrArg Complex.re hζ0; simp at this; linarith [hneg.1]
        have hL_p : DirichletCharacter.LFunction (PChar.of χ).χ (β : ℂ) = 0 :=
          (RHDirect.LFunction_eq_zero_iff_primitive_of_re_pos χ (by simpa using hβ_pos) (.inl hχ_ne1)).mp hzero
        have hβ_pg : 1 - c_P / Real.log (2 * (Q_all : ℝ)) < β := by
          have h1 : δ_L / L_M ≤ c_P / Real.log (2 * (Q_all : ℝ)) :=
            (div_le_div_of_nonneg_right (hδL_cP.trans (by linarith)) hLM_pos.le).trans
              (div_le_div_of_nonneg_left hcP_pos.le hlog2Q_pos hlog2Q_le)
          linarith
        have hcond_leQ : (PChar.of χ).N ≤ Q_all := (Nat.le_of_dvd (by omega) χ.conductor_dvd_level).trans hm₀_le_Q
        have heq := (hpage2 Q_all (hm₀.trans hm₀_le_Q) (PChar.of χ) ψ₁ β β₁ hcond_leQ hψ₁_leQ hL_p hLψ₁_0 hβ_pg hβ₁_page).1
        have hN_eq : χ.conductor = ψ₁.N := congrArg PChar.N heq
        exact hψ₁_dvd (hN_eq ▸ χ.conductor_dvd_level)
      have hW_main := hMain_noSiegel hno_m0
      refine ⟨hW_cS_le_main.trans hW_main,
        ∏ p ∈ ψ₁.N.primeFactors.filter (fun p => ¬ p ∣ m₀), p,
        fun s hs1 hs_odd hs_sqf hcop_sm hs_le hs_ne => ?_⟩
      have hno_s : ∀ (χ : DirichletCharacter ℂ m₀) (β : ℝ), 1 - δ_L / L_M < β → β < 1 →
          haveI : NeZero s := ⟨by omega⟩
          DirichletCharacter.LFunction
            (Stage11SecondMomentFrame.twistedChar χ (quadCharOfOddSqf s hs_odd)) (β : ℂ) ≠ 0 := by
        intro χ β hβ_lo hβ_hi
        have : NeZero s := ⟨by omega⟩
        intro hzero
        set η := Stage11SecondMomentFrame.twistedChar χ (quadCharOfOddSqf s hs_odd)
        have hχs_prim := quadCharOfOddSqf_isPrimitive hs_odd hs_sqf
        have hs_dvd : s ∣ η.conductor := right_dvd_conductor_twistedChar hcop_sm.symm χ hχs_prim
        have hη_ne1 : η ≠ 1 := fun h1 => by
          rw [h1, DirichletCharacter.conductor_one] at hs_dvd; have := Nat.le_of_dvd one_pos hs_dvd; omega
        have hβ_pos : 0 < β := by have : δ_L / L_M ≤ 1 / 4 := (div_le_self hδL_pos.le hLM_gt1.le).trans hδL_qtr; linarith
        have hL_p : DirichletCharacter.LFunction (PChar.of η).χ (β : ℂ) = 0 :=
          (RHDirect.LFunction_eq_zero_iff_primitive_of_re_pos η (by simpa using hβ_pos) (.inl hη_ne1)).mp hzero
        have hms_leQ : m₀ * s ≤ Q_all := Nat.mul_le_mul_left m₀ ((Nat.le_floor hs_le).trans (Nat.le_succ _))
        have hcond_leQ : (PChar.of η).N ≤ Q_all :=
          (Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) η.conductor_dvd_level).trans hms_leQ
        have hβ_pg : 1 - c_P / Real.log (2 * (Q_all : ℝ)) < β := by
          have h1 : δ_L / L_M ≤ c_P / Real.log (2 * (Q_all : ℝ)) :=
            (div_le_div_of_nonneg_right (hδL_cP.trans (by linarith)) hLM_pos.le).trans
              (div_le_div_of_nonneg_left hcP_pos.le hlog2Q_pos hlog2Q_le)
          linarith
        have heq := (hpage2 Q_all (hm₀.trans hm₀_le_Q) (PChar.of η) ψ₁ β β₁ hcond_leQ hψ₁_leQ hL_p hLψ₁_0 hβ_pg hβ₁_page).1
        have hN_eq : η.conductor = ψ₁.N := congrArg PChar.N heq
        have hs_eq : ∏ p ∈ ψ₁.N.primeFactors.filter (fun p => ¬ p ∣ m₀), p = s := by
          rw [← hN_eq]
          exact prod_primeFactors_not_dvd_eq_of_dvd_mul hs_sqf hcop_sm hs_dvd η.conductor_dvd_level η.conductor_ne_zero
        exact hs_ne hs_eq.symm
      have : NeZero s := ⟨by omega⟩
      have htw := hTwist_noSiegel s hs1 hs_odd hs_sqf hcop_sm hs_le (fun χ β hlo hhi => hno_s χ β hlo hhi)
      have h1 : ((1 / (64 * Z ^ 2)) / (m₀.totient : ℝ)) * X ^ 2 = (1 / (4 * Z ^ 2)) * ((1 / 16 : ℝ) * X ^ 2 / (m₀.totient : ℝ)) := by
        field_simp [hZ0.ne', htot_pos.ne']; ring
      have h2 : (c_S' / (512 * (Q_all : ℝ) ^ 2)) * X ^ 2 ≤ (1 / (4 * Z ^ 2)) * ((1 / 16 : ℝ) * X ^ 2 / (m₀.totient : ℝ)) :=
        hErr_vs_W.trans (mul_le_mul_of_nonneg_left hW_cS_le_main (by positivity))
      have h3 : (1 / (4 * Z ^ 2) + 1 / (4 * Z ^ 2)) * ((1 / 16 : ℝ) * X ^ 2 / (m₀.totient : ℝ)) ≤
          (1 / Z ^ 2) * ∑ r ∈ apPrimes m₀ a₀ X, tentWt X r := by
        have hhalf : (1 / (4 * Z ^ 2) + 1 / (4 * Z ^ 2) : ℝ) ≤ 1 / Z ^ 2 := by
          have : (1 / (4 * Z ^ 2) + 1 / (4 * Z ^ 2) : ℝ) = (1 / 2) * (1 / Z ^ 2) := by ring
          linarith [show (0 : ℝ) < 1 / Z ^ 2 by positivity]
        exact mul_le_mul hhalf hW_main (by positivity) (by positivity)
      linarith [htw, h1, h2, h3]
  · -- **SUBCASE A (NO SIEGEL ZERO)**: `s_exc = 0`!
    push Not at hSiegel
    have hno_any : ∀ (m : ℕ) [NeZero m] (hmQ : m ≤ Q_all) (η : DirichletCharacter ℂ m) (β : ℝ),
        1 - δ_L / L_M < β → β < 1 → DirichletCharacter.LFunction η (β : ℂ) ≠ 0 := by
      intro m _ hmQ η β hβ_lo hβ_hi hzero
      have hβ_pos : 0 < β := by have : δ_L / L_M ≤ 1 / 4 := (div_le_self hδL_pos.le hLM_gt1.le).trans hδL_qtr; linarith
      have hη_ne1 : η ≠ 1 := by
        intro h1; subst h1
        have hβ_ne1 : (β : ℂ) ≠ 1 := fun h => by have := congrArg Complex.re h; simp at this; linarith
        have hζ0 := (RHDirect.LFunction_trivChar_eq_zero_iff_riemannZeta_of_re_pos (N := m) (by simpa using hβ_pos) hβ_ne1).mp hzero
        have hneg := Stage9LandauSiegel.riemannZeta_neg_on_Ioo hβ_pos hβ_hi
        have := congrArg Complex.re hζ0; simp at this; linarith [hneg.1]
      have hL_p : DirichletCharacter.LFunction (PChar.of η).χ (β : ℂ) = 0 :=
        (RHDirect.LFunction_eq_zero_iff_primitive_of_re_pos η (by simpa using hβ_pos) (.inl hη_ne1)).mp hzero
      exact hSiegel (PChar.of η) β ((Nat.le_of_dvd (NeZero.pos m) η.conductor_dvd_level).trans hmQ) hβ_lo hβ_hi hL_p
    have hW_main := hMain_noSiegel (hno_any m₀ hm₀_le_Q)
    refine ⟨hW_cS_le_main.trans hW_main, 0, fun s hs1 hs_odd hs_sqf hcop_sm hs_le _ => ?_⟩
    have : NeZero s := ⟨by omega⟩
    have hms_leQ : m₀ * s ≤ Q_all := Nat.mul_le_mul_left m₀ ((Nat.le_floor hs_le).trans (Nat.le_succ _))
    have htw := hTwist_noSiegel s hs1 hs_odd hs_sqf hcop_sm hs_le (fun χ => hno_any (m₀ * s) hms_leQ _)
    have h1 : ((1 / (64 * Z ^ 2)) / (m₀.totient : ℝ)) * X ^ 2 = (1 / (4 * Z ^ 2)) * ((1 / 16 : ℝ) * X ^ 2 / (m₀.totient : ℝ)) := by
      field_simp [hZ0.ne', htot_pos.ne']; ring
    have h2 : (c_S' / (512 * (Q_all : ℝ) ^ 2)) * X ^ 2 ≤ (1 / (4 * Z ^ 2)) * ((1 / 16 : ℝ) * X ^ 2 / (m₀.totient : ℝ)) :=
      hErr_vs_W.trans (mul_le_mul_of_nonneg_left hW_cS_le_main (by positivity))
    have h3 : (1 / (4 * Z ^ 2) + 1 / (4 * Z ^ 2)) * ((1 / 16 : ℝ) * X ^ 2 / (m₀.totient : ℝ)) ≤
        (1 / Z ^ 2) * ∑ r ∈ apPrimes m₀ a₀ X, tentWt X r := by
      have hhalf : (1 / (4 * Z ^ 2) + 1 / (4 * Z ^ 2) : ℝ) ≤ 1 / Z ^ 2 := by
        have : (1 / (4 * Z ^ 2) + 1 / (4 * Z ^ 2) : ℝ) = (1 / 2) * (1 / Z ^ 2) := by ring
        linarith [show (0 : ℝ) < 1 / Z ^ 2 by positivity]
      exact mul_le_mul hhalf hW_main (by positivity) (by positivity)
    linarith [htw, h1, h2, h3]

/-! ### Section 4d: Sobolev–Gallagher Dyadic `BadShare` & Unconditional `MSqMain` -/

/-- Piecewise-constant derivative of `y ↦ Sz χ y Z`:
`SzDeriv χ v Z = ∑_{n=1}^{⌊Z⌋₊} (if v < n then (Λ(n) / n) * χ(n) else 0)`. -/
def SzDeriv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (v Z : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊Z⌋₊,
    if v < (n : ℝ) then ((Λ n / (n : ℝ) : ℝ) : ℂ) * χ (n : ZMod N) else 0

/-- Elementary piecewise-linear integral identity:
`min 1 (y / n) - min 1 (a / n) = ∫ v in a..y, (if v < n then 1 / n else 0)` for `0 < a ≤ y`, `n ≥ 1`. -/
private lemma min_div_sub_eq_integral {a y : ℝ} (_ha : 0 < a) (hay : a ≤ y) {n : ℕ} (hn : 1 ≤ n) :
    min 1 (y / (n : ℝ)) - min 1 (a / (n : ℝ)) =
      ∫ v in a..y, (if v < (n : ℝ) then (1 / (n : ℝ) : ℝ) else 0) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hint_const : ∀ u w : ℝ, u ≤ w →
      (w ≤ (n : ℝ) → ∫ v in u..w, (if v < (n : ℝ) then (1 / (n : ℝ) : ℝ) else 0) = (w - u) / (n : ℝ)) ∧
      ((n : ℝ) ≤ u → ∫ v in u..w, (if v < (n : ℝ) then (1 / (n : ℝ) : ℝ) else 0) = 0) := fun u w huw => by
    constructor
    · intro hwn
      have hae : ∀ᵐ v ∂volume, v ∈ Set.uIoc u w →
          (if v < (n : ℝ) then (1 / (n : ℝ) : ℝ) else 0) = 1 / (n : ℝ) := by
        have hne : ∀ᵐ v ∂volume, v ≠ (n : ℝ) := by
          rw [ae_iff]; simp
        filter_upwards [hne] with v hv hmem
        rw [Set.uIoc_of_le huw] at hmem
        have hlt : v < (n : ℝ) := lt_of_le_of_ne (hmem.2.trans hwn) hv
        rw [if_pos hlt]
      rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const, smul_eq_mul]
      ring
    · intro hnu
      have hcongr : ∀ v ∈ Set.uIoc u w, (if v < (n : ℝ) then (1 / (n : ℝ) : ℝ) else 0) = 0 := fun v hv => by
        rw [Set.uIoc_of_le huw] at hv
        rw [if_neg (by linarith [hv.1])]
      rw [intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall hcongr), intervalIntegral.integral_zero]
  by_cases hna : (n : ℝ) ≤ a
  · rw [min_eq_left ((one_le_div hn_pos).mpr (hna.trans hay)),
      min_eq_left ((one_le_div hn_pos).mpr hna), sub_self, (hint_const a y hay).2 hna]
  · push Not at hna
    by_cases hyn : y ≤ (n : ℝ)
    · rw [min_eq_right ((div_le_one hn_pos).mpr hyn),
        min_eq_right ((div_le_one hn_pos).mpr hna.le), (hint_const a y hay).1 hyn, sub_div]
    · push Not at hyn
      have hint1 : IntervalIntegrable (fun v : ℝ => if v < (n : ℝ) then (1 / (n : ℝ) : ℝ) else 0) volume a (n : ℝ) := by
        have hae : ∀ᵐ v ∂volume, v ∈ Set.uIoc a (n : ℝ) →
            (if v < (n : ℝ) then (1 / (n : ℝ) : ℝ) else 0) = 1 / (n : ℝ) := by
          have hne : ∀ᵐ v ∂volume, v ≠ (n : ℝ) := by rw [ae_iff]; simp
          filter_upwards [hne] with v hv hmem
          rw [Set.uIoc_of_le hna.le] at hmem
          rw [if_pos (lt_of_le_of_ne hmem.2 hv)]
        exact (intervalIntegrable_const (c := 1 / (n : ℝ))).congr_ae (by
          rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]; exact hae.mono fun v hv h => (hv h).symm)
      have hint2 : IntervalIntegrable (fun v : ℝ => if v < (n : ℝ) then (1 / (n : ℝ) : ℝ) else 0) volume (n : ℝ) y := by
        have hcongr : Set.EqOn (fun v : ℝ => if v < (n : ℝ) then (1 / (n : ℝ) : ℝ) else 0) (fun _ => 0) (Set.uIoc (n : ℝ) y) := by
          intro v hv; rw [Set.uIoc_of_le hyn.le] at hv; simp [not_lt.mpr hv.1.le]
        exact (intervalIntegrable_const (c := (0 : ℝ))).congr hcongr.symm
      rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2,
        (hint_const a (n : ℝ) hna.le).1 le_rfl, (hint_const (n : ℝ) y hyn.le).2 le_rfl, add_zero,
        min_eq_left ((one_le_div hn_pos).mpr hyn.le), min_eq_right ((div_le_one hn_pos).mpr hna.le)]
      field_simp [hn_pos.ne']

/-- Integrability of `v ↦ SzDeriv χ v Z` and `v ↦ ‖SzDeriv χ v Z‖ ^ 2` on any `[a, b]`. -/
private lemma intervalIntegrable_SzDeriv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (Z a b : ℝ) :
    IntervalIntegrable (fun v : ℝ => SzDeriv χ v Z) volume a b ∧
    IntervalIntegrable (fun v : ℝ => ‖SzDeriv χ v Z‖ ^ 2) volume a b := by
  have hmeas_term : ∀ n ∈ Finset.Icc 1 ⌊Z⌋₊,
      Measurable (fun v : ℝ => if v < (n : ℝ) then ((Λ n / (n : ℝ) : ℝ) : ℂ) * χ (n : ZMod N) else 0) :=
    fun n _ => Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const measurable_const
  have hmeas : Measurable (fun v : ℝ => SzDeriv χ v Z) := by
    unfold SzDeriv
    exact Finset.measurable_sum _ hmeas_term
  have hbd : ∀ v : ℝ, ‖SzDeriv χ v Z‖ ≤ ∑ n ∈ Finset.Icc 1 ⌊Z⌋₊, Λ n / (n : ℝ) := fun v => by
    unfold SzDeriv
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    split_ifs
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n))]
      exact mul_le_of_le_one_right (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)) (χ.norm_le_one _)
    · rw [norm_zero]; exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)
  set C := ∑ n ∈ Finset.Icc 1 ⌊Z⌋₊, Λ n / (n : ℝ)
  have hC_nn : 0 ≤ C := Finset.sum_nonneg fun _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
  refine ⟨?_, ?_⟩
  · exact (intervalIntegrable_const (c := C)).mono_fun' hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hbd)
  · have hmeas_sq : Measurable (fun v : ℝ => ‖SzDeriv χ v Z‖ ^ 2) := (hmeas.norm).pow_const 2
    exact (intervalIntegrable_const (c := C ^ 2)).mono_fun' hmeas_sq.aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => by
        dsimp only
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hbd v) 2)

/-- **Exact Integral Identity (`Sz_sub_eq_integral_SzDeriv`)**:
`Sz χ y Z - Sz χ a Z = ∫ v in a..y, SzDeriv χ v Z` for all `0 < a ≤ y`. -/
theorem Sz_sub_eq_integral_SzDeriv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {a y Z : ℝ} (ha : 0 < a) (hay : a ≤ y) :
    Sz χ y Z - Sz χ a Z = ∫ v in a..y, SzDeriv χ v Z := by
  unfold Sz SzDeriv
  rw [← Finset.sum_sub_distrib]
  have hint : ∀ n ∈ Finset.Icc 1 ⌊Z⌋₊,
      IntervalIntegrable (fun v : ℝ => if v < (n : ℝ) then ((Λ n / (n : ℝ) : ℝ) : ℂ) * χ (n : ZMod N) else 0) volume a y := by
    intro n _
    have hm : Measurable (fun v : ℝ => if v < (n : ℝ) then ((Λ n / (n : ℝ) : ℝ) : ℂ) * χ (n : ZMod N) else 0) :=
      Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const measurable_const
    exact (intervalIntegrable_const (c := ‖((Λ n / (n : ℝ) : ℝ) : ℂ) * χ (n : ZMod N)‖)).mono_fun'
      hm.aestronglyMeasurable (Filter.Eventually.of_forall fun v => by
        dsimp only
        split_ifs
        · exact le_rfl
        · rw [norm_zero]; exact norm_nonneg _)
  rw [intervalIntegral.integral_finsetSum hint]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have h1 := min_div_sub_eq_integral ha hay hn1
  have hterm :
      (fun v : ℝ => if v < (n : ℝ) then ((Λ n / (n : ℝ) : ℝ) : ℂ) * χ (n : ZMod N) else 0) =
      fun v : ℝ => ((Λ n : ℂ) * χ (n : ZMod N)) * ((if v < (n : ℝ) then (1 / (n : ℝ) : ℝ) else 0 : ℝ) : ℂ) := by
    ext v
    split_ifs
    · push_cast; ring
    · simp
  rw [hterm, intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, ← h1]
  unfold ZeroDensityWindow.cN; push_cast; ring

/-- **Unconditional Sobolev–Gallagher Pointwise Sup Bound on `[a, 2a]` (`norm_Sz_sq_le_sobolev`)**:
for every `0 < a`, every `y ∈ [a, 2 * a]`, and every `χ, Z`:
`‖Sz χ y Z‖^2 ≤ 2 * ‖Sz χ a Z‖^2 + 2 * a * ∫ v in a..(2 * a), ‖SzDeriv χ v Z‖^2`. -/
theorem norm_Sz_sq_le_sobolev {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {a y Z : ℝ} (ha : 0 < a) (hy_lo : a ≤ y) (hy_hi : y ≤ 2 * a) :
    ‖Sz χ y Z‖ ^ 2 ≤ 2 * ‖Sz χ a Z‖ ^ 2 + 2 * a * ∫ v in a..(2 * a), ‖SzDeriv χ v Z‖ ^ 2 := by
  have hid := Sz_sub_eq_integral_SzDeriv χ ha hy_lo (Z := Z)
  have hsplit : Sz χ y Z = Sz χ a Z + ∫ v in a..y, SzDeriv χ v Z := by linear_combination hid
  have htri : ‖Sz χ y Z‖ ^ 2 ≤ 2 * ‖Sz χ a Z‖ ^ 2 + 2 * ‖∫ v in a..y, SzDeriv χ v Z‖ ^ 2 := by
    rw [hsplit]
    have h1 := norm_add_le (Sz χ a Z) (∫ v in a..y, SzDeriv χ v Z)
    have h2 : (‖Sz χ a Z‖ + ‖∫ v in a..y, SzDeriv χ v Z‖) ^ 2 ≤
        2 * ‖Sz χ a Z‖ ^ 2 + 2 * ‖∫ v in a..y, SzDeriv χ v Z‖ ^ 2 := by
      nlinarith [sq_nonneg (‖Sz χ a Z‖ - ‖∫ v in a..y, SzDeriv χ v Z‖)]
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  have hcs : ‖∫ v in a..y, SzDeriv χ v Z‖ ^ 2 ≤ a * ∫ v in a..(2 * a), ‖SzDeriv χ v Z‖ ^ 2 := by
    have h1 : ‖∫ v in a..y, SzDeriv χ v Z‖ ≤ ∫ v in a..y, ‖SzDeriv χ v Z‖ :=
      intervalIntegral.norm_integral_le_integral_norm hy_lo
    have hint_n : IntervalIntegrable (fun v => ‖SzDeriv χ v Z‖) volume a y :=
      (intervalIntegrable_SzDeriv χ Z a y).1.norm
    have hint_sq : IntervalIntegrable (fun v => ‖SzDeriv χ v Z‖ ^ 2) volume a y :=
      (intervalIntegrable_SzDeriv χ Z a y).2
    -- Cauchy–Schwarz on `[a, y]`: `(∫_a^y f)^2 ≤ (y - a) * ∫_a^y f^2` via `0 ≤ ∫_a^y (t * f - 1)^2`
    have hcs_real : (∫ v in a..y, ‖SzDeriv χ v Z‖) ^ 2 ≤ (y - a) * ∫ v in a..y, ‖SzDeriv χ v Z‖ ^ 2 := by
      have hquad : ∀ t : ℝ, 0 ≤ t ^ 2 * (∫ v in a..y, ‖SzDeriv χ v Z‖ ^ 2) -
          2 * t * (∫ v in a..y, ‖SzDeriv χ v Z‖) + (y - a) := fun t => by
        have hnn : 0 ≤ ∫ v in a..y, (t * ‖SzDeriv χ v Z‖ - 1) ^ 2 :=
          intervalIntegral.integral_nonneg hy_lo fun v _ => sq_nonneg _
        have hexp : (fun v : ℝ => (t * ‖SzDeriv χ v Z‖ - 1) ^ 2) =
            fun v => (t ^ 2 * ‖SzDeriv χ v Z‖ ^ 2 - 2 * t * ‖SzDeriv χ v Z‖) + 1 := by ext v; ring
        rw [hexp, intervalIntegral.integral_add ((hint_sq.const_mul (t ^ 2)).sub (hint_n.const_mul (2 * t)))
          intervalIntegrable_const, intervalIntegral.integral_sub (hint_sq.const_mul (t ^ 2)) (hint_n.const_mul (2 * t)),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const, smul_eq_mul, mul_one] at hnn
        exact hnn
      set I2 := ∫ v in a..y, ‖SzDeriv χ v Z‖ ^ 2
      set I1 := ∫ v in a..y, ‖SzDeriv χ v Z‖
      have hI2_nn : 0 ≤ I2 := intervalIntegral.integral_nonneg hy_lo fun v _ => sq_nonneg _
      rcases eq_or_lt_of_le hI2_nn with hI2_0 | hI2_pos
      · -- If `I2 = 0`, `hquad t` gives `2 * t * I1 ≤ y - a` for all `t`, so `I1 = 0`!
        have hI1_0 : I1 = 0 := by
          by_contra hne
          have hq := hquad ((y - a + 1) / (2 * I1))
          rw [← hI2_0, mul_zero, zero_sub] at hq
          have hcancel : 2 * ((y - a + 1) / (2 * I1)) * I1 = y - a + 1 := by field_simp [hne]
          linarith
        rw [hI1_0, ← hI2_0]; norm_num
      · have hq := hquad (I1 / I2)
        have hmul := mul_le_mul_of_nonneg_left hq hI2_pos.le
        have halg : I2 * ((I1 / I2) ^ 2 * I2 - 2 * (I1 / I2) * I1 + (y - a)) = (y - a) * I2 - I1 ^ 2 := by
          field_simp [hI2_pos.ne']; ring
        linarith
    have hmono : ∫ v in a..y, ‖SzDeriv χ v Z‖ ^ 2 ≤ ∫ v in a..(2 * a), ‖SzDeriv χ v Z‖ ^ 2 := by
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_SzDeriv χ Z a y).2 (intervalIntegrable_SzDeriv χ Z y (2 * a)).2]
      have hnn : 0 ≤ ∫ v in y..(2 * a), ‖SzDeriv χ v Z‖ ^ 2 :=
        intervalIntegral.integral_nonneg hy_hi fun _ _ => sq_nonneg _
      linarith
    have hI_nn : 0 ≤ ∫ v in a..y, ‖SzDeriv χ v Z‖ ^ 2 :=
      intervalIntegral.integral_nonneg hy_lo fun _ _ => sq_nonneg _
    calc ‖∫ v in a..y, SzDeriv χ v Z‖ ^ 2
        ≤ (∫ v in a..y, ‖SzDeriv χ v Z‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (y - a) * ∫ v in a..y, ‖SzDeriv χ v Z‖ ^ 2 := hcs_real
      _ ≤ a * ∫ v in a..(2 * a), ‖SzDeriv χ v Z‖ ^ 2 := mul_le_mul (by linarith) hmono hI_nn ha.le
  linarith

/-- Shorthand for `Sz` of a quadratic prime twist `ψ · χ_r` (encapsulating `NeZero r` and `NeZero (ψ.N * r)`). -/
private def szOfPrime (ψ : PChar) {r : ℕ} (hr : r.Prime) (y Z : ℝ) : ℂ :=
  haveI : NeZero r := ⟨hr.ne_zero⟩
  Sz (Stage11SecondMomentFrame.twistedChar ψ.χ (quadCharOfPrime r hr)) y Z

/-- Shorthand for `SzDeriv` of a quadratic prime twist `ψ · χ_r`. -/
private def szDerivOfPrime (ψ : PChar) {r : ℕ} (hr : r.Prime) (v Z : ℝ) : ℂ :=
  haveI : NeZero r := ⟨hr.ne_zero⟩
  SzDeriv (Stage11SecondMomentFrame.twistedChar ψ.χ (quadCharOfPrime r hr)) v Z

/-- Helper: finite sum of `IntervalIntegrable` functions is `IntervalIntegrable`. -/
private lemma intervalIntegrable_finsetSum_local {ι : Type*} [DecidableEq ι] (s : Finset ι)
    {f : ι → ℝ → ℝ} {a b : ℝ} (hf : ∀ i ∈ s, IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun v : ℝ => ∑ i ∈ s, f i v) volume a b := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact intervalIntegrable_const (c := (0 : ℝ))
  | insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

open Classical in
/-- **UNCONDITIONAL `MSqMain` + SOBOLEV DYADIC `BadShare` (`msqMain_unconditional`, `0` ASSUMPTIONS!)**:
There exist absolute constants `C_tw ≥ 30` and `c_w > 0` such that for EVERY modulus `m₀ ≥ 2` with
`8 ∣ m₀`, EVERY `a₀` with `Coprime a₀ m₀` and `a₀ % 4 = 3`, EVERY small-prime bound `B ≥ 2`,
EVERY primitive character `ψ : PChar`, EVERY `Y ≥ 16, K ≥ 1, τ > 0, Z ≥ Y ^ K` with `(B : ℝ) ^ 2 ≤ Y`
and `hsmall`, and EVERY scale `X ≥ max (Z + 1) ((ψ.N : ℝ) + 1)` satisfying
`C_tw * Real.log ((m₀ : ℝ) * Z ^ 2) * (Real.log Z + 1) ≤ Real.log X`:
letting `P := apPrimes m₀ a₀ X` and `W := ∑ r ∈ P, tentWt X r`:
1. `c_w * X ^ 2 / ((m₀ : ℝ) ^ (3 / 2 : ℝ)) ≤ W` (and `0 < W`), AND
2. The bad prime set
   `B_MS := P.filter (fun r => ¬ ∀ y ∈ Set.Icc Y (Y ^ K), ‖Sz (twistedChar ψ.χ χ_r) y Z‖ ≤ y ^ (1/2 + τ) / 2)`
   satisfies the sharp weighted `BadShare` bound:
   `∑ r ∈ B_MS, tentWt X r ≤ ((⌈K * Real.log Y / Real.log 2⌉₊ + 1 : ℕ) : ℝ) * (2400 * (Real.log Z + 2) ^ 2 / Y ^ (2 * τ)) * W`! -/
theorem msqMain_unconditional :
    ∃ C_tw c_w : ℝ, 30 ≤ C_tw ∧ 0 < c_w ∧
      ∀ (m₀ a₀ B : ℕ), 8 ∣ m₀ → Nat.Coprime a₀ m₀ → a₀ % 4 = 3 → 2 ≤ B →
        ∀ (ψ : PChar) (Y K τ Z X : ℝ),
          16 ≤ Y → 1 ≤ K → 0 < τ → Y ^ K ≤ Z → ((B : ℝ)) ^ 2 ≤ Y →
          (∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ m₀ → (p : ℝ) ≤ Z → p ≤ B) →
          Z < X → (ψ.N : ℝ) < X →
          C_tw * Real.log ((m₀ : ℝ) * Z ^ 2) * (Real.log Z + 1) ≤ Real.log X →
          let P := apPrimes m₀ a₀ X
          let W := ∑ r ∈ P, tentWt X r
          c_w * X ^ 2 / ((m₀ : ℝ) ^ ((3 : ℝ) / 2)) ≤ W ∧
          ∑ r ∈ P.filter (fun r => ∃ hr : r.Prime,
              haveI : NeZero r := ⟨hr.ne_zero⟩
              ¬ ∀ y ∈ Set.Icc Y (Y ^ K),
                ‖Sz (Stage11SecondMomentFrame.twistedChar ψ.χ (quadCharOfPrime r hr)) y Z‖ ≤
                  y ^ ((1 : ℝ) / 2 + τ) / 2),
            tentWt X r ≤
              ((⌈K * Real.log Y / Real.log 2⌉₊ + 1 : ℕ) : ℝ) * (2400 * (Real.log Z + 2) ^ 2 / Y ^ (2 * τ)) * W := by
  classical
  obtain ⟨C_tw, c_w, hCtw30, hcw_pos, htent⟩ := tentWt_main_and_twist_unconditional
  refine ⟨C_tw, c_w, hCtw30, hcw_pos, fun m₀ a₀ B h8 hcop_am ha4 hB2 ψ Y K τ Z X
      hY16 hK1 hτ0 hYK_Z hB2_Y hsmall hZX hNX hlogX => ?_⟩
  have hm₀_ge2 : 2 ≤ m₀ := by
    obtain ⟨k, hk⟩ := h8
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hk
      rw [hk, Nat.coprime_zero_right] at hcop_am
      omega
    omega
  have hY0 : 0 < Y := by linarith
  have hY_le_YK : Y ≤ Y ^ K := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by linarith) hK1
  have hZ4 : 4 ≤ Z := by linarith
  have hX1 : 1 ≤ X := by linarith
  set P := apPrimes m₀ a₀ X
  set W := ∑ r ∈ P, tentWt X r
  obtain ⟨hW_ge, s_exc, htwist⟩ := htent m₀ a₀ hm₀_ge2 hcop_am Z X hZ4 hX1 hlogX
  refine ⟨hW_ge, ?_⟩
  have hW_nn : 0 ≤ W := Finset.sum_nonneg fun r _ => tentWt_nonneg (by linarith) r
  have hP_props : ∀ r ∈ P, r.Prime ∧ r ≡ a₀ [MOD m₀] ∧ Z < (r : ℝ) := fun r hr => by
    obtain ⟨hI, hpr, hmod⟩ := Finset.mem_filter.mp hr
    have hXr : X < (r : ℝ) := lt_of_lt_of_le (Nat.lt_floor_add_one X) (by exact_mod_cast (Finset.mem_Ioc.mp hI).1)
    exact ⟨hpr, hmod, hZX.trans hXr⟩
  -- For any `r ∈ P` (`r.Prime, ψ.N < r`), `szOfPrime ψ hpr v Z` has exact Jacobi-sum form!
  have hSz_eq_jac : ∀ (r : ℕ) (hr : r ∈ P) (hpr : r.Prime) (v : ℝ),
      szOfPrime ψ hpr v Z =
        ∑ n ∈ Finset.Icc 1 ⌊Z⌋₊,
          (((ZeroDensityWindow.cN v n : ℝ) : ℂ) * ψ.χ (n : ZMod ψ.N)) * ((jacobiSym (n : ℤ) r : ℤ) : ℂ) := by
    intro r hr hpr v
    have : NeZero r := ⟨hpr.ne_zero⟩
    have hXr : X < (r : ℝ) := lt_of_lt_of_le (Nat.lt_floor_add_one X) (by exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hr).1).1)
    have hNr : ψ.N < r := by exact_mod_cast (hNX.trans hXr)
    have hcop_Nr : Nat.Coprime ψ.N r := Stage2PrimePairs.coprime_of_prime_gt (NeZero.pos ψ.N) hpr hNr
    unfold szOfPrime Sz
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [twistedChar_apply_nat_all hcop_Nr, quadCharOfPrime_apply_nat hpr n]; ring
  have hSzD_eq_jac : ∀ (r : ℕ) (hr : r ∈ P) (hpr : r.Prime) (v : ℝ), 0 < v →
      (v : ℂ) * szDerivOfPrime ψ hpr v Z =
        ∑ n ∈ Finset.Icc 1 ⌊Z⌋₊,
          (if v < (n : ℝ) then ((ZeroDensityWindow.cN v n : ℝ) : ℂ) * ψ.χ (n : ZMod ψ.N) else 0) *
            ((jacobiSym (n : ℤ) r : ℤ) : ℂ) := by
    intro r hr hpr v hv
    have : NeZero r := ⟨hpr.ne_zero⟩
    have hXr : X < (r : ℝ) := lt_of_lt_of_le (Nat.lt_floor_add_one X) (by exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hr).1).1)
    have hNr : ψ.N < r := by exact_mod_cast (hNX.trans hXr)
    have hcop_Nr : Nat.Coprime ψ.N r := Stage2PrimePairs.coprime_of_prime_gt (NeZero.pos ψ.N) hpr hNr
    unfold szDerivOfPrime SzDeriv
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs with hvn
    · rw [twistedChar_apply_nat_all hcop_Nr, quadCharOfPrime_apply_nat hpr n]
      unfold ZeroDensityWindow.cN
      have hn_pos : (0 : ℝ) < (n : ℝ) := lt_trans hv hvn
      rw [min_eq_right ((div_le_one hn_pos).mpr hvn.le)]
      push_cast; ring
    · simp
  -- Dyadic block bound: for EVERY `a ∈ [Y, Z]`, weighted sum of Sobolev energy is `≤ 600 * W * a * (log Z + 2)^2`!
  have hBlock_msq : ∀ a : ℝ, Y ≤ a → a ≤ Z →
      ∑ r ∈ P.attach,
          tentWt X r.1 *
            (2 * ‖szOfPrime ψ (hP_props r.1 r.2).1 a Z‖ ^ 2 +
             2 * a * ∫ v in a..(2 * a), ‖szDerivOfPrime ψ (hP_props r.1 r.2).1 v Z‖ ^ 2) ≤
        600 * W * a * (Real.log Z + 2) ^ 2 := by
    intro a haY haZ
    have ha1 : 1 ≤ a := by linarith
    have ha0 : 0 < a := by linarith
    have hB2_a : ((B : ℝ)) ^ 2 ≤ a := hB2_Y.trans haY
    -- Part 1: Endpoint mean square at `a` (`≤ 150 * W * a * (log Z + 2)^2`)
    have hpt_a :
        ∑ r ∈ P.attach, tentWt X r.1 * ‖szOfPrime ψ (hP_props r.1 r.2).1 a Z‖ ^ 2 ≤
          150 * W * a * (Real.log Z + 2) ^ 2 := by
      have heq : ∑ r ∈ P.attach, tentWt X r.1 * ‖szOfPrime ψ (hP_props r.1 r.2).1 a Z‖ ^ 2 =
          ∑ r ∈ P, tentWt X r * ‖∑ n ∈ Finset.Icc 1 ⌊Z⌋₊,
            (((ZeroDensityWindow.cN a n : ℝ) : ℂ) * ψ.χ (n : ZMod ψ.N)) * ((jacobiSym (n : ℤ) r : ℤ) : ℂ)‖ ^ 2 := by
        rw [← Finset.sum_attach P]
        exact Finset.sum_congr rfl fun r _ => by rw [hSz_eq_jac r.1 r.2 (hP_props r.1 r.2).1 a]
      rw [heq]
      refine weighted_reciprocity_meansq_of_twist_bound h8 ha4 hB2 ha1 haZ hB2_a hsmall P (tentWt X)
        (fun r _ => tentWt_nonneg (by linarith) r) hP_props s_exc htwist
        (fun n => ((ZeroDensityWindow.cN a n : ℝ) : ℂ) * ψ.χ (n : ZMod ψ.N)) ?_ ?_
      · intro n hne
        by_contra hnotpp
        apply hne
        unfold ZeroDensityWindow.cN
        rw [ArithmeticFunction.vonMangoldt_apply, if_neg hnotpp, zero_mul]; simp
      · intro n _
        have hc_nn : 0 ≤ ZeroDensityWindow.cN a n :=
          mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (le_min zero_le_one (by positivity))
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc_nn]
        exact mul_le_of_le_one_right hc_nn (ψ.χ.norm_le_one _)
    -- Part 2: Integrated derivative mean square on `[a, 2a]` (`≤ 150 * W * (log Z + 2)^2 / a` pointwise!)
    have hderiv_pt : ∀ v ∈ Set.Icc a (2 * a),
        ∑ r ∈ P.attach, tentWt X r.1 * ‖szDerivOfPrime ψ (hP_props r.1 r.2).1 v Z‖ ^ 2 ≤
          150 * W * (Real.log Z + 2) ^ 2 / a := by
      intro v hv
      have hv0 : 0 < v := lt_of_lt_of_le ha0 hv.1
      have hv1 : 1 ≤ v := by linarith [hv.1]
      by_cases hvZ : v ≤ Z
      · have hB2_v : ((B : ℝ)) ^ 2 ≤ v := hB2_a.trans hv.1
        have hmul_v2 :
            v ^ 2 * ∑ r ∈ P.attach, tentWt X r.1 * ‖szDerivOfPrime ψ (hP_props r.1 r.2).1 v Z‖ ^ 2 ≤
            150 * W * v * (Real.log Z + 2) ^ 2 := by
          have heq :
              v ^ 2 * ∑ r ∈ P.attach, tentWt X r.1 * ‖szDerivOfPrime ψ (hP_props r.1 r.2).1 v Z‖ ^ 2 =
              ∑ r ∈ P, tentWt X r * ‖∑ n ∈ Finset.Icc 1 ⌊Z⌋₊,
                (if v < (n : ℝ) then ((ZeroDensityWindow.cN v n : ℝ) : ℂ) * ψ.χ (n : ZMod ψ.N) else 0) *
                  ((jacobiSym (n : ℤ) r : ℤ) : ℂ)‖ ^ 2 := by
            rw [Finset.mul_sum, ← Finset.sum_attach P]
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [← hSzD_eq_jac r.1 r.2 (hP_props r.1 r.2).1 v hv0, norm_mul, mul_pow,
              Complex.norm_real, Real.norm_of_nonneg hv0.le]; ring
          rw [heq]
          refine weighted_reciprocity_meansq_of_twist_bound h8 ha4 hB2 hv1 hvZ hB2_v hsmall P (tentWt X)
            (fun r _ => tentWt_nonneg (by linarith) r) hP_props s_exc htwist
            (fun n => if v < (n : ℝ) then ((ZeroDensityWindow.cN v n : ℝ) : ℂ) * ψ.χ (n : ZMod ψ.N) else 0) ?_ ?_
          · intro n hne
            split_ifs at hne with hvn
            · by_contra hnotpp; apply hne; unfold ZeroDensityWindow.cN
              rw [ArithmeticFunction.vonMangoldt_apply, if_neg hnotpp, zero_mul]; simp
            · exact absurd rfl hne
          · intro n _
            have hc_nn : 0 ≤ ZeroDensityWindow.cN v n :=
              mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (le_min zero_le_one (by positivity))
            split_ifs
            · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc_nn]
              exact mul_le_of_le_one_right hc_nn (ψ.χ.norm_le_one _)
            · rw [norm_zero]; exact hc_nn
        have hdiv_v : ∑ r ∈ P.attach, tentWt X r.1 * ‖szDerivOfPrime ψ (hP_props r.1 r.2).1 v Z‖ ^ 2 ≤
            150 * W * (Real.log Z + 2) ^ 2 / v := by
          rw [le_div_iff₀ hv0]
          have h1 := mul_le_mul_of_nonneg_left hmul_v2 (inv_nonneg.mpr hv0.le)
          have hL : v⁻¹ * (v ^ 2 * ∑ r ∈ P.attach, tentWt X r.1 * ‖szDerivOfPrime ψ (hP_props r.1 r.2).1 v Z‖ ^ 2) =
              (∑ r ∈ P.attach, tentWt X r.1 * ‖szDerivOfPrime ψ (hP_props r.1 r.2).1 v Z‖ ^ 2) * v := by
            field_simp [hv0.ne']
          have hR : v⁻¹ * (150 * W * v * (Real.log Z + 2) ^ 2) = 150 * W * (Real.log Z + 2) ^ 2 := by
            field_simp [hv0.ne']
          linarith
        exact hdiv_v.trans (div_le_div_of_nonneg_left (by positivity) ha0 hv.1)
      · push Not at hvZ
        have hzero : ∀ r ∈ P.attach, szDerivOfPrime ψ (hP_props r.1 r.2).1 v Z = 0 := by
          intro r _
          unfold szDerivOfPrime SzDeriv
          refine Finset.sum_eq_zero fun n hn => ?_
          have hn_leZ : (n : ℝ) ≤ Z := (by exact_mod_cast (Finset.mem_Icc.mp hn).2 : (n : ℝ) ≤ (⌊Z⌋₊ : ℝ)).trans (Nat.floor_le (by linarith))
          rw [if_neg (by linarith)]
        have hsum0 : ∑ r ∈ P.attach, tentWt X r.1 * ‖szDerivOfPrime ψ (hP_props r.1 r.2).1 v Z‖ ^ 2 = 0 :=
          Finset.sum_eq_zero fun r hr => by rw [hzero r hr, norm_zero, sq, mul_zero, mul_zero]
        rw [hsum0]; positivity
    have hint_r : ∀ r ∈ P.attach,
        IntervalIntegrable (fun v : ℝ => tentWt X r.1 * ‖szDerivOfPrime ψ (hP_props r.1 r.2).1 v Z‖ ^ 2) volume a (2 * a) := by
      intro r _
      have : NeZero r.1 := ⟨(hP_props r.1 r.2).1.ne_zero⟩
      exact ((intervalIntegrable_SzDeriv _ Z a (2 * a)).2).const_mul (tentWt X r.1)
    have hint_sum :
        ∑ r ∈ P.attach, tentWt X r.1 * (∫ v in a..(2 * a), ‖szDerivOfPrime ψ (hP_props r.1 r.2).1 v Z‖ ^ 2) ≤
          150 * W * (Real.log Z + 2) ^ 2 := by
      have hswap :
          ∑ r ∈ P.attach, tentWt X r.1 * (∫ v in a..(2 * a), ‖szDerivOfPrime ψ (hP_props r.1 r.2).1 v Z‖ ^ 2) =
            ∫ v in a..(2 * a), ∑ r ∈ P.attach, tentWt X r.1 * ‖szDerivOfPrime ψ (hP_props r.1 r.2).1 v Z‖ ^ 2 := by
        simp_rw [← intervalIntegral.integral_const_mul]
        exact (intervalIntegral.integral_finsetSum hint_r).symm
      rw [hswap]
      have hint_all := intervalIntegrable_finsetSum_local P.attach hint_r
      have hle_c := intervalIntegral.integral_mono_on (by linarith : a ≤ 2 * a) hint_all intervalIntegrable_const hderiv_pt
      rw [intervalIntegral.integral_const, smul_eq_mul] at hle_c
      have halg : (2 * a - a) * (150 * W * (Real.log Z + 2) ^ 2 / a) = 150 * W * (Real.log Z + 2) ^ 2 := by
        field_simp [ha0.ne']; ring
      linarith
    have hsplit_sum :
        ∑ r ∈ P.attach, tentWt X r.1 *
            (2 * ‖szOfPrime ψ (hP_props r.1 r.2).1 a Z‖ ^ 2 +
             2 * a * ∫ v in a..(2 * a), ‖szDerivOfPrime ψ (hP_props r.1 r.2).1 v Z‖ ^ 2) =
          2 * (∑ r ∈ P.attach, tentWt X r.1 * ‖szOfPrime ψ (hP_props r.1 r.2).1 a Z‖ ^ 2) +
          (2 * a) * (∑ r ∈ P.attach, tentWt X r.1 * ∫ v in a..(2 * a), ‖szDerivOfPrime ψ (hP_props r.1 r.2).1 v Z‖ ^ 2) := by
      simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hsplit_sum]
    have h2 : (2 * a) * (∑ r ∈ P.attach, tentWt X r.1 * ∫ v in a..(2 * a), ‖szDerivOfPrime ψ (hP_props r.1 r.2).1 v Z‖ ^ 2) ≤
        (2 * a) * (150 * W * (Real.log Z + 2) ^ 2) :=
      mul_le_mul_of_nonneg_left hint_sum (by positivity)
    linarith [hpt_a, h2]
  -- Dyadic covering of `[Y, Y ^ K]` by `J := ⌈K * log Y / log 2⌉₊ + 1` blocks `a_j = 2^j * Y` (capped at `Y^K`)
  set J : ℕ := ⌈K * Real.log Y / Real.log 2⌉₊ + 1
  let a_j : ℕ → ℝ := fun j => min (Y ^ K) ((2 : ℝ) ^ j * Y)
  let B_j : ℕ → Finset ℕ := fun j =>
    P.filter fun r => ∃ hr : r.Prime,
      (a_j j) ^ ((1 : ℝ) + 2 * τ) / 4 <
        2 * ‖szOfPrime ψ hr (a_j j) Z‖ ^ 2 +
        2 * a_j j * ∫ v in (a_j j)..(2 * a_j j), ‖szDerivOfPrime ψ hr v Z‖ ^ 2
  -- Step A: Every bad `r` belongs to `⋃_{j < J} B_j j`!
  have hcover : P.filter (fun r => ∃ hr : r.Prime,
      haveI : NeZero r := ⟨hr.ne_zero⟩
      ¬ ∀ y ∈ Set.Icc Y (Y ^ K),
        ‖Sz (Stage11SecondMomentFrame.twistedChar ψ.χ (quadCharOfPrime r hr)) y Z‖ ≤
          y ^ ((1 : ℝ) / 2 + τ) / 2) ⊆ (Finset.range J).biUnion B_j := by
    intro r hr
    obtain ⟨hrP, hpr, hnot⟩ := Finset.mem_filter.mp hr
    push Not at hnot
    obtain ⟨y, ⟨hy_lo, hy_hi⟩, hy_gt⟩ := hnot
    have hy0 : 0 < y := lt_of_lt_of_le hY0 hy_lo
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    set j : ℕ := ⌊Real.log (y / Y) / Real.log 2⌋₊
    have hj_lt : j < J := by
      have h1 : Real.log (y / Y) ≤ K * Real.log Y := by
        have hy_div : y / Y ≤ Y ^ K := (div_le_self hy0.le (by linarith)).trans hy_hi
        exact (Real.log_le_log (by positivity) hy_div).trans (Real.log_rpow hY0 K).le
      have h2 : Real.log (y / Y) / Real.log 2 ≤ K * Real.log Y / Real.log 2 :=
        div_le_div_of_nonneg_right h1 hlog2_pos.le
      have h3 : (j : ℝ) ≤ K * Real.log Y / Real.log 2 :=
        (Nat.floor_le (div_nonneg (Real.log_nonneg ((one_le_div hY0).mpr hy_lo)) hlog2_pos.le)).trans h2
      have h4 : (j : ℝ) ≤ (⌈K * Real.log Y / Real.log 2⌉₊ : ℝ) := h3.trans (Nat.le_ceil _)
      have h5 : j ≤ ⌈K * Real.log Y / Real.log 2⌉₊ := by exact_mod_cast h4
      dsimp only [J]; omega
    have h2j_lo : (2 : ℝ) ^ j * Y ≤ y := by
      have hfl : (j : ℝ) ≤ Real.log (y / Y) / Real.log 2 :=
        Nat.floor_le (div_nonneg (Real.log_nonneg ((one_le_div hY0).mpr hy_lo)) hlog2_pos.le)
      have hlog : Real.log ((2 : ℝ) ^ j) ≤ Real.log (y / Y) := by
        rw [Real.log_pow]; exact (le_div_iff₀ hlog2_pos).mp hfl
      have hpow : (2 : ℝ) ^ j ≤ y / Y := (Real.log_le_log_iff (by positivity) (by positivity)).mp hlog
      exact (le_div_iff₀ hY0).mp hpow
    have h2j_hi : y ≤ 2 * ((2 : ℝ) ^ j * Y) := by
      have hlt : Real.log (y / Y) / Real.log 2 < (j : ℝ) + 1 := Nat.lt_floor_add_one _
      have hlog : Real.log (y / Y) < Real.log ((2 : ℝ) ^ (j + 1)) := by
        rw [Real.log_pow]; push_cast; exact (div_lt_iff₀ hlog2_pos).mp hlt
      have hpow : y / Y < (2 : ℝ) ^ (j + 1) := (Real.log_lt_log_iff (by positivity) (by positivity)).mp hlog
      have hmul : y < (2 : ℝ) ^ (j + 1) * Y := (div_lt_iff₀ hY0).mp hpow
      rw [pow_succ'] at hmul; linarith
    have haj_eq : a_j j = (2 : ℝ) ^ j * Y := min_eq_right (h2j_lo.trans hy_hi)
    have haj_pos : 0 < a_j j := by rw [haj_eq]; positivity
    have : NeZero r := ⟨hpr.ne_zero⟩
    have hsob : ‖szOfPrime ψ hpr y Z‖ ^ 2 ≤
        2 * ‖szOfPrime ψ hpr (a_j j) Z‖ ^ 2 +
        2 * a_j j * ∫ v in (a_j j)..(2 * a_j j), ‖szDerivOfPrime ψ hpr v Z‖ ^ 2 :=
      norm_Sz_sq_le_sobolev (Stage11SecondMomentFrame.twistedChar ψ.χ (quadCharOfPrime r hpr))
        haj_pos (by rw [haj_eq]; exact h2j_lo) (by rw [haj_eq]; exact h2j_hi) (Z := Z)
    have hgt_sq : y ^ ((1 : ℝ) + 2 * τ) / 4 < ‖szOfPrime ψ hpr y Z‖ ^ 2 := by
      have hsq : (y ^ ((1 : ℝ) / 2 + τ) / 2) ^ 2 = y ^ ((1 : ℝ) + 2 * τ) / 4 := by
        rw [div_pow, ← Real.rpow_natCast (y ^ ((1 : ℝ) / 2 + τ)) 2, ← Real.rpow_mul hy0.le]
        congr 1
        · congr 1; ring
        · norm_num
      rw [← hsq]
      exact pow_lt_pow_left₀ hy_gt (by positivity) (by norm_num)
    have ha_le_y : (a_j j) ^ ((1 : ℝ) + 2 * τ) / 4 ≤ y ^ ((1 : ℝ) + 2 * τ) / 4 :=
      div_le_div_of_nonneg_right (Real.rpow_le_rpow haj_pos.le (by rw [haj_eq]; exact h2j_lo) (by linarith)) (by norm_num)
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj_lt,
      Finset.mem_filter.mpr ⟨hrP, hpr, lt_of_le_of_lt ha_le_y (lt_of_lt_of_le hgt_sq hsob)⟩⟩
  -- Step B: Weighted Markov on each block `B_j j`: `≤ (2400 * (Real.log Z + 2)^2 / Y^(2 * τ)) * W`!
  have hMarkov_j : ∀ j : ℕ, ∑ r ∈ B_j j, tentWt X r ≤ (2400 * (Real.log Z + 2) ^ 2 / Y ^ (2 * τ)) * W := by
    intro j
    have haj_ge_Y : Y ≤ a_j j := le_min hY_le_YK (le_mul_of_one_le_left hY0.le (one_le_pow₀ (by norm_num)))
    have haj_le_Z : a_j j ≤ Z := (min_le_left _ _).trans hYK_Z
    have haj_pos : 0 < a_j j := lt_of_lt_of_le hY0 haj_ge_Y
    have hthr_pos : 0 < (a_j j) ^ ((1 : ℝ) + 2 * τ) / 4 := by positivity
    have hmul_le : ((a_j j) ^ ((1 : ℝ) + 2 * τ) / 4) * ∑ r ∈ B_j j, tentWt X r ≤
        600 * W * a_j j * (Real.log Z + 2) ^ 2 := by
      rw [Finset.mul_sum]
      have hsub_att : (B_j j).attach.image (fun x => (⟨x.1, (Finset.mem_filter.mp x.2).1⟩ : {r // r ∈ P})) ⊆ P.attach :=
        Finset.subset_univ _
      have hsum_B : ∑ r ∈ B_j j, ((a_j j) ^ ((1 : ℝ) + 2 * τ) / 4) * tentWt X r ≤
          ∑ r ∈ P.attach, tentWt X r.1 *
            (2 * ‖szOfPrime ψ (hP_props r.1 r.2).1 (a_j j) Z‖ ^ 2 +
             2 * a_j j * ∫ v in (a_j j)..(2 * a_j j), ‖szDerivOfPrime ψ (hP_props r.1 r.2).1 v Z‖ ^ 2) := by
        let g : {r // r ∈ P} → ℝ := fun r => tentWt X r.1 *
          (2 * ‖szOfPrime ψ (hP_props r.1 r.2).1 (a_j j) Z‖ ^ 2 +
           2 * a_j j * ∫ v in (a_j j)..(2 * a_j j), ‖szDerivOfPrime ψ (hP_props r.1 r.2).1 v Z‖ ^ 2)
        have hg_nn : ∀ r : {r // r ∈ P}, 0 ≤ g r := fun r =>
          mul_nonneg (tentWt_nonneg (by linarith) r.1)
            (add_nonneg (by positivity) (mul_nonneg (by positivity)
              (intervalIntegral.integral_nonneg (by linarith) fun _ _ => sq_nonneg _)))
        have hinj : Set.InjOn (fun x : {r // r ∈ B_j j} => (⟨x.1, (Finset.mem_filter.mp x.2).1⟩ : {r // r ∈ P}))
            ((B_j j).attach : Set {r // r ∈ B_j j}) := fun x _ y _ h => by
          dsimp only at h
          exact Subtype.ext (congrArg (Subtype.val : {r // r ∈ P} → ℕ) h)
        calc ∑ r ∈ B_j j, ((a_j j) ^ ((1 : ℝ) + 2 * τ) / 4) * tentWt X r
            = ∑ x ∈ (B_j j).attach, ((a_j j) ^ ((1 : ℝ) + 2 * τ) / 4) * tentWt X x.1 := (Finset.sum_attach _ _).symm
          _ ≤ ∑ x ∈ (B_j j).attach, g ⟨x.1, (Finset.mem_filter.mp x.2).1⟩ := Finset.sum_le_sum fun x _ => by
              obtain ⟨_, hpr, hgt⟩ := Finset.mem_filter.mp x.2
              rw [mul_comm]; exact mul_le_mul_of_nonneg_left hgt.le (tentWt_nonneg (by linarith) x.1)
          _ = ∑ r ∈ (B_j j).attach.image (fun x => (⟨x.1, (Finset.mem_filter.mp x.2).1⟩ : {r // r ∈ P})), g r :=
              (Finset.sum_image (fun x hx y hy h => hinj hx hy h)).symm
          _ ≤ ∑ r ∈ P.attach, g r := Finset.sum_le_sum_of_subset_of_nonneg hsub_att fun r _ _ => hg_nn r
      exact hsum_B.trans (hBlock_msq (a_j j) haj_ge_Y haj_le_Z)
    have hsp : (a_j j) ^ ((1 : ℝ) + 2 * τ) = a_j j * (a_j j) ^ (2 * τ) := by
      rw [Real.rpow_add haj_pos, Real.rpow_one]
    have hpow_ge : Y ^ (2 * τ) ≤ (a_j j) ^ (2 * τ) := Real.rpow_le_rpow hY0.le haj_ge_Y (by linarith)
    calc ∑ r ∈ B_j j, tentWt X r
        ≤ (600 * W * a_j j * (Real.log Z + 2) ^ 2) / ((a_j j) ^ ((1 : ℝ) + 2 * τ) / 4) := (le_div_iff₀' hthr_pos).mpr hmul_le
      _ = (2400 * (Real.log Z + 2) ^ 2 / (a_j j) ^ (2 * τ)) * W := by
          rw [hsp]; field_simp [haj_pos.ne', (Real.rpow_pos_of_pos haj_pos (2 * τ)).ne']; ring
      _ ≤ (2400 * (Real.log Z + 2) ^ 2 / Y ^ (2 * τ)) * W :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hY0 _) hpow_ge) hW_nn
  -- Step C: Union bound over `j ∈ Finset.range J`
  calc ∑ r ∈ P.filter _, tentWt X r
      ≤ ∑ r ∈ (Finset.range J).biUnion B_j, tentWt X r :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover fun r _ _ => tentWt_nonneg (by linarith) r
    _ ≤ ∑ j ∈ Finset.range J, ∑ r ∈ B_j j, tentWt X r :=
        sum_biUnion_le_of_nonneg fun r => tentWt_nonneg (by linarith) r
    _ ≤ ∑ _j ∈ Finset.range J, (2400 * (Real.log Z + 2) ^ 2 / Y ^ (2 * τ)) * W :=
        Finset.sum_le_sum fun j _ => hMarkov_j j
    _ = (J : ℝ) * (2400 * (Real.log Z + 2) ^ 2 / Y ^ (2 * τ)) * W := by simp [mul_assoc]

/-! ## Section 5: Unconditional `PairGood` Prime-Pair Existence, `SigALe` Discharge & Master Theorem -/

/-- The 4 quadratic-twist primitive characters `(ψ, ψ · χ_q, ψ · χ_d, ψ · χ_q · χ_d)` indexed
by `(i, j) : Fin 2 × Fin 2` for coprime odd primes `q, d ≡ 3 (mod 4)` coprime to `ψ.N`. -/
def pairTwist (ψ : PChar) (q d : ℕ) [NeZero q] [NeZero d]
    (hq : q.Prime) (hq4 : q % 4 = 3) (hd : d.Prime) (hd4 : d % 4 = 3)
    (hcop_Nq : Nat.Coprime ψ.N q) (hcop_Nd : Nat.Coprime ψ.N d) (hcop_qd : Nat.Coprime q d) :
    Fin 2 × Fin 2 → PChar
  | (0, 0) => ψ
  | (1, 0) =>
      ⟨ψ.N * q,
        Stage11SecondMomentFrame.twistedChar ψ.χ (quadCharOfPrime q hq),
        twistedChar_isPrimitive hcop_Nq ψ.prim (quadCharOfPrime_isPrimitive_of_mod_four hq hq4)⟩
  | (0, 1) =>
      ⟨ψ.N * d,
        Stage11SecondMomentFrame.twistedChar ψ.χ (quadCharOfPrime d hd),
        twistedChar_isPrimitive hcop_Nd ψ.prim (quadCharOfPrime_isPrimitive_of_mod_four hd hd4)⟩
  | (1, 1) =>
      ⟨(ψ.N * q) * d,
        Stage11SecondMomentFrame.twistedChar
          (Stage11SecondMomentFrame.twistedChar ψ.χ (quadCharOfPrime q hq)) (quadCharOfPrime d hd),
        twistedChar_isPrimitive (hcop_Nd.mul_left hcop_qd)
          (twistedChar_isPrimitive hcop_Nq ψ.prim (quadCharOfPrime_isPrimitive_of_mod_four hq hq4))
          (quadCharOfPrime_isPrimitive_of_mod_four hd hd4)⟩

/-- **Full `PairGood` Prime-Pair Certification Predicate**:
upgrades `WinPair eps Y q d` with coprimality to `ψ.N` AND unconditional `ZeroFreeBoxDelta`,
`O(K * log Y)` log-derivative bound at `s = 1`, and pointwise Cesàro ramp bound
`‖Gchi χ_{i,j} y‖ ≤ y ^ (1/2 + τ)` across the entire window `y ∈ [Y, Y ^ K]` for ALL THREE
off-diagonal quadratic twists `(i, j) ≠ (0, 0)`! -/
structure PairGood (ψ : PChar) (δ₀ C_L eps τ K Y : ℝ) (q d : ℕ) : Prop where
  win : WinPair eps Y q d
  gt_N : ψ.N < q
  cop_Nq : Nat.Coprime ψ.N q
  cop_Nd : Nat.Coprime ψ.N d
  cop_qd : Nat.Coprime q d
  offDiag_good :
    haveI : NeZero q := ⟨win.q_prime.ne_zero⟩
    haveI : NeZero d := ⟨win.d_prime.ne_zero⟩
    ∀ ij : Fin 2 × Fin 2, ij ≠ (0, 0) →
      let χ_ij := pairTwist ψ q d win.q_prime (by have := win.q_mod; omega)
        win.d_prime (by have := win.d_mod; omega) cop_Nq cop_Nd cop_qd ij
      (∃ Q : ℝ, (χ_ij.N : ℝ) ≤ Q ∧ Y ^ (eps / 6) ≤ Real.log Q ∧ ZeroFreeBoxDelta δ₀ Q χ_ij.χ) ∧
      ‖deriv (DirichletCharacter.LFunction χ_ij.χ) 1 / DirichletCharacter.LFunction χ_ij.χ 1‖ ≤
        C_L * K * Real.log Y ∧
      ∀ y ∈ Set.Icc Y (Y ^ K), ‖Gchi χ_ij.χ y‖ ≤ y ^ ((1 : ℝ) / 2 + τ)

private lemma cast_dirichletChar_spec {N k : ℕ} [NeZero N] (hN : k + 1 = N)
    (η : DirichletCharacter ℂ N) {δ₀ Q : ℝ}
    (h1 : η.IsPrimitive) (h2 : (N : ℝ) ≤ Q) (h3 : ¬ ZeroFreeBoxDelta δ₀ Q η) :
    let η' : DirichletCharacter ℂ (k + 1) := hN.symm ▸ η
    η'.IsPrimitive ∧ ((k + 1 : ℕ) : ℝ) ≤ Q ∧ ¬ ZeroFreeBoxDelta δ₀ Q η' := by
  subst hN; exact ⟨h1, h2, h3⟩

open Classical in
/-- Helper: weighted zero-free-box bad-set bound for quadratic twists `ψ · χ_r` over `r ∈ P`. -/
private lemma tentWt_badZF_le {δ₀ C_zd : ℝ}
    (hzd : ∀ (Q : ℝ) (F : Finset (Σ k : ℕ, DirichletCharacter ℂ (k + 1))), 3 ≤ Q →
      (∀ p ∈ F, p.2.IsPrimitive ∧ ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧ ¬ ZeroFreeBoxDelta δ₀ Q p.2) →
      (F.card : ℝ) ≤ C_zd * Q ^ (1 / 4 : ℝ))
    {ψ : PChar} {X Q : ℝ} (hX1 : 1 ≤ X) (hQ3 : 3 ≤ Q) (hNX : (ψ.N : ℝ) < X)
    (hQ_ge : 2 * (ψ.N : ℝ) * X ≤ Q)
    (P : Finset ℕ) (hP : ∀ r ∈ P, r.Prime ∧ r % 4 = 3 ∧ X < (r : ℝ) ∧ (r : ℝ) ≤ 2 * X) :
    ∑ r ∈ P.filter (fun r => ∃ hr : r.Prime,
        haveI : NeZero r := ⟨hr.ne_zero⟩
        ¬ ZeroFreeBoxDelta δ₀ Q (Stage11SecondMomentFrame.twistedChar ψ.χ (quadCharOfPrime r hr))),
      tentWt X r ≤ C_zd * Q ^ (1 / 4 : ℝ) * ((X / 2) * Real.log (2 * X)) := by
  classical
  set B := P.filter fun r => ∃ hr : r.Prime,
    haveI : NeZero r := ⟨hr.ne_zero⟩
    ¬ ZeroFreeBoxDelta δ₀ Q (Stage11SecondMomentFrame.twistedChar ψ.χ (quadCharOfPrime r hr))
  -- Map each `r ∈ B` injectively into `Σ k, DirichletCharacter ℂ (k + 1)`
  let embed : {r // r ∈ B} → (Σ k : ℕ, DirichletCharacter ℂ (k + 1)) := fun r =>
    have hpr : r.1.Prime := (hP r.1 (Finset.mem_filter.mp r.2).1).1
    haveI : NeZero r.1 := ⟨hpr.ne_zero⟩
    have hpos : 1 ≤ ψ.N * r.1 := Nat.mul_pos (NeZero.pos ψ.N) hpr.pos
    ⟨ψ.N * r.1 - 1,
      (Nat.sub_add_cancel hpos).symm ▸
        Stage11SecondMomentFrame.twistedChar ψ.χ (quadCharOfPrime r.1 hpr)⟩
  have hinj : Set.InjOn embed (B.attach : Set {r // r ∈ B}) := by
    intro r₁ _ r₂ _ heq
    have h1 : ψ.N * r₁.1 - 1 = ψ.N * r₂.1 - 1 := congrArg Sigma.fst heq
    have hp1 : 1 ≤ ψ.N * r₁.1 := Nat.mul_pos (NeZero.pos ψ.N) (hP r₁.1 (Finset.mem_filter.mp r₁.2).1).1.pos
    have hp2 : 1 ≤ ψ.N * r₂.1 := Nat.mul_pos (NeZero.pos ψ.N) (hP r₂.1 (Finset.mem_filter.mp r₂.2).1).1.pos
    have hmul : ψ.N * r₁.1 = ψ.N * r₂.1 := by omega
    exact Subtype.ext (Nat.eq_of_mul_eq_mul_left (NeZero.pos ψ.N) hmul)
  set F := B.attach.image embed
  have hF_spec : ∀ p ∈ F, p.2.IsPrimitive ∧ ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧ ¬ ZeroFreeBoxDelta δ₀ Q p.2 := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨r, _, rfl⟩
    obtain ⟨hrP, hpr', hnz⟩ := Finset.mem_filter.mp r.2
    obtain ⟨hpr, hr4, hXr, hr2X⟩ := hP r.1 hrP
    have hNr : ψ.N < r.1 := by exact_mod_cast (hNX.trans hXr)
    have hcop : Nat.Coprime ψ.N r.1 := Stage2PrimePairs.coprime_of_prime_gt (NeZero.pos ψ.N) hpr hNr
    have : NeZero r.1 := ⟨hpr.ne_zero⟩
    have hprim : (Stage11SecondMomentFrame.twistedChar ψ.χ (quadCharOfPrime r.1 hpr)).IsPrimitive :=
      twistedChar_isPrimitive hcop ψ.prim (quadCharOfPrime_isPrimitive_of_mod_four hpr hr4)
    have hpos : 1 ≤ ψ.N * r.1 := Nat.mul_pos (NeZero.pos ψ.N) hpr.pos
    have hleQ : ((ψ.N * r.1 : ℕ) : ℝ) ≤ Q := by
      calc ((ψ.N * r.1 : ℕ) : ℝ) = (ψ.N : ℝ) * (r.1 : ℝ) := by push_cast; rfl
        _ ≤ (ψ.N : ℝ) * (2 * X) := mul_le_mul_of_nonneg_left hr2X (Nat.cast_nonneg _)
        _ = 2 * (ψ.N : ℝ) * X := by ring
        _ ≤ Q := hQ_ge
    dsimp only [embed]
    exact cast_dirichletChar_spec (Nat.sub_add_cancel hpos) _ hprim hleQ hnz
  have hcard_eq : F.card = B.card := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_attach]
  have hcard_bd : (B.card : ℝ) ≤ C_zd * Q ^ (1 / 4 : ℝ) := by
    rw [← hcard_eq]; exact hzd Q F hQ3 hF_spec
  have hterm : ∀ r ∈ B, tentWt X r ≤ (X / 2) * Real.log (2 * X) := fun r hr => by
    obtain ⟨hpr, _, _, hr2X⟩ := hP r (Finset.mem_filter.mp hr).1
    exact tentWt_le_half_mul_log hX1 hpr.pos hr2X
  calc ∑ r ∈ B, tentWt X r
      ≤ ∑ _r ∈ B, ((X / 2) * Real.log (2 * X)) := Finset.sum_le_sum hterm
    _ = (B.card : ℝ) * ((X / 2) * Real.log (2 * X)) := by simp
    _ ≤ C_zd * Q ^ (1 / 4 : ℝ) * ((X / 2) * Real.log (2 * X)) :=
        mul_le_mul_of_nonneg_right hcard_bd (mul_nonneg (by linarith) (Real.log_nonneg (by linarith)))

/-- Helper: elementary asymptotic `rpow` dominance `c * Y ^ a * exp (-b * Y ^ d) → 0` for `b > 0, d > 0`. -/
private lemma eventually_rpow_exp_neg_rpow_le {c a b d η : ℝ} (hb : 0 < b) (hd : 0 < d) (hη : 0 < η) :
    ∀ᶠ Y : ℝ in Filter.atTop, c * Y ^ a * Real.exp (-(b * Y ^ d)) ≤ η := by
  have h0 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (a / d) b hb).comp (tendsto_rpow_atTop hd)
  have h1 : Tendsto (fun Y : ℝ => c * Y ^ a * Real.exp (-(b * Y ^ d))) atTop (𝓝 0) := by
    have hm := h0.const_mul c
    rw [mul_zero] at hm
    refine hm.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with Y hY
    simp only [Function.comp_apply, mul_assoc]
    rw [← Real.rpow_mul hY.le, mul_div_cancel₀ _ hd.ne']
    ring_nf
  exact h1.eventually (ge_mem_nhds hη)

/-- Helper: elementary asymptotic `c * (Real.log Y) ^ k ≤ η * Y ^ d` for `d > 0, η > 0`. -/
private lemma eventually_log_pow_le_rpow {c η d : ℝ} (k : ℕ) (hd : 0 < d) (hη : 0 < η) :
    ∀ᶠ Y : ℝ in Filter.atTop, c * (Real.log Y) ^ k ≤ η * Y ^ d := by
  have h1 : Tendsto (fun Y : ℝ => c * (Real.log Y) ^ k / Y ^ d) atTop (𝓝 0) := by
    rcases eq_or_ne k 0 with rfl | hk0
    · simp only [pow_zero, mul_one]
      have h := (tendsto_const_nhds (x := c)).div_atTop (tendsto_rpow_atTop hd)
      simpa using h
    · have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk0)
      have hsub := (isLittleO_log_rpow_atTop (show (0 : ℝ) < d / (k : ℝ) by positivity)).tendsto_div_nhds_zero
      have hpow := hsub.pow k
      rw [zero_pow hk0] at hpow
      have hmul := hpow.const_mul c
      rw [mul_zero] at hmul
      refine hmul.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with Y hY
      rw [div_pow, ← Real.rpow_natCast (Y ^ (d / (k : ℝ))) k, ← Real.rpow_mul hY.le,
        div_mul_cancel₀ _ hk_pos.ne', mul_div_assoc]
  filter_upwards [h1.eventually (ge_mem_nhds hη), Filter.eventually_gt_atTop (0 : ℝ)] with Y hY hY0
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hY0 d)).mp hY

/-- **UNCONDITIONAL `PairGood` PRIME-PAIR EXISTENCE FOR ANY FINITE CHARACTER FAMILY
(`pairGood_family_exists_unconditional`, `0` ASSUMPTIONS!)**:
There exist absolute constants `0 < δ₀ ≤ 1 / 400` and `C_L > 0` such that for EVERY finite family
`Ψ : Finset PChar` of primitive Dirichlet characters, EVERY `ε ∈ (0, 1 / 4]`, EVERY `τ > 0`, and
EVERY `K ≥ 1`, there exists `Y₀ ≥ 16` such that for ALL `Y ≥ Y₀`, there exist primes `(q, d)`
satisfying `WinPair ε Y q d` AND `∀ ψ ∈ Ψ, PairGood ψ δ₀ C_L ε τ K Y q d`! -/
theorem pairGood_family_exists_unconditional :
    ∃ δ₀ C_L : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 400 ∧ 0 < C_L ∧
      ∀ (Ψ : Finset PChar) (ε τ K : ℝ), 0 < ε → ε ≤ 1 / 4 → 0 < τ → 1 ≤ K →
        ∃ Y₀ : ℝ, 16 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
          ∃ q d : ℕ, WinPair ε Y q d ∧ ∀ ψ ∈ Ψ, PairGood ψ δ₀ C_L ε τ K Y q d := by
  classical
  obtain ⟨δ₀, hδ₀_pos, hδ₀_400, C_zd, hCzd_pos, hzd⟩ := zeroDensityBox_unconditional
  obtain ⟨C_tw, c_w, hCtw30, hcw_pos, hmsq⟩ := msqMain_unconditional
  set K_Z : ℕ := ⌈8 / δ₀⌉₊ + 1
  have hKZ_pos : (0 : ℝ) < (K_Z : ℝ) := by positivity
  refine ⟨δ₀, 8 * (K_Z : ℝ), hδ₀_pos, hδ₀_400, by positivity, fun Ψ ε τ K hε0 hε4 hτ0 hK1 => ?_⟩
  obtain ⟨Y_box, hYbox16, hboxOfS⟩ := boxOfS_unconditional hδ₀_pos (hδ₀_400.trans (by norm_num)) ε τ K hε0 hε4 hτ0 hK1
  set N_max : ℕ := Ψ.sup PChar.N + 2
  have hNmax_pos : (0 : ℝ) < (N_max : ℝ) := by positivity
  set m_fam : ℝ := max 1 (Ψ.card : ℝ)
  have hmfam_ge1 : 1 ≤ m_fam := le_max_left _ _
  have hmfam_pos : 0 < m_fam := by linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- Collect all elementary asymptotic thresholds on `Y` (all `∀ᶠ Y in atTop`, finite conjunction!)
  have hev_base : ∀ᶠ Y : ℝ in Filter.atTop,
      Y_box ≤ Y ∧ 3 ≤ Y ^ (ε / 5) ∧ (2 : ℝ) * Real.log 2 ≤ Y ^ (ε / 5) ∧
      ((N_max : ℝ) : ℝ) < Real.exp (Y ^ (ε / 5) / 2) ∧
      (Y ^ K) ^ K_Z < Real.exp (Y ^ (ε / 5) / 2) ∧
      ((max 2 ⌊Y ^ (ε / 5)⌋₊ : ℕ) : ℝ) ^ 2 ≤ Y ∧
      2 ≤ Real.log Y := by
    have h1 := Filter.eventually_ge_atTop Y_box
    have h2 := (tendsto_rpow_atTop (by positivity : 0 < ε / 5)).eventually_ge_atTop (max 3 (2 * Real.log 2 + 2 * Real.log (N_max + 2)))
    have h3 := eventually_rpow_exp_neg_rpow_le (c := 1) (a := (K_Z : ℝ) * K) (b := 1 / 2) (d := ε / 5) (η := 1 / 2)
      (by norm_num) (by positivity) (by norm_num)
    have h4 : ∀ᶠ Y : ℝ in Filter.atTop, (Y ^ (ε / 5) + 2) ^ 2 ≤ Y := by
      have hlt : 2 * (ε / 5) < 1 := by linarith
      have hd : 0 < 1 - 2 * (ε / 5) := by linarith
      have ha := (tendsto_rpow_atTop hd).eventually_ge_atTop 4
      have hb := (tendsto_rpow_atTop (by positivity : 0 < ε / 5)).eventually_ge_atTop 2
      filter_upwards [ha, hb, Filter.eventually_gt_atTop (1 : ℝ)] with Y hYa hYb hY1
      have hle : Y ^ (ε / 5) + 2 ≤ 2 * Y ^ (ε / 5) := by linarith
      calc (Y ^ (ε / 5) + 2) ^ 2 ≤ (2 * Y ^ (ε / 5)) ^ 2 := pow_le_pow_left₀ (by positivity) hle 2
        _ = 4 * Y ^ (2 * (ε / 5)) := by rw [mul_pow, ← Real.rpow_natCast (Y ^ (ε / 5)) 2, ← Real.rpow_mul (by linarith)]; norm_num; ring
        _ ≤ Y ^ (1 - 2 * (ε / 5)) * Y ^ (2 * (ε / 5)) := mul_le_mul_of_nonneg_right hYa (by positivity)
        _ = Y := by rw [← Real.rpow_add (by linarith), sub_add_cancel, Real.rpow_one]
    have h5 := Filter.eventually_ge_atTop (Real.exp 2)
    filter_upwards [h1, h2, h3, h4, h5] with Y hY1 hY2 hY3 hY4 hY5
    have hY0 : 0 < Y := by linarith
    have hY_ge16 : 16 ≤ Y := hYbox16.trans hY1
    have hU_ge3 : 3 ≤ Y ^ (ε / 5) := (le_max_left _ _).trans hY2
    have hU_big : 2 * Real.log 2 + 2 * Real.log (N_max + 2) ≤ Y ^ (ε / 5) := (le_max_right _ _).trans hY2
    have hN_lt : (N_max : ℝ) < Real.exp (Y ^ (ε / 5) / 2) := by
      have hlogN : Real.log (N_max : ℝ) < Y ^ (ε / 5) / 2 := by
        have h1' : Real.log (N_max : ℝ) < Real.log ((N_max : ℝ) + 2) := Real.log_lt_log hNmax_pos (by linarith)
        have h2' : 0 ≤ Real.log ((N_max : ℝ) + 2) := Real.log_nonneg (by linarith)
        linarith
      exact (Real.log_lt_iff_lt_exp hNmax_pos).mp hlogN
    have hZ_lt : (Y ^ K) ^ K_Z < Real.exp (Y ^ (ε / 5) / 2) := by
      have hZ_eq : (Y ^ K) ^ K_Z = Y ^ ((K_Z : ℝ) * K) := by
        rw [← Real.rpow_natCast (Y ^ K) K_Z, ← Real.rpow_mul hY0.le]; congr 1; ring
      rw [hZ_eq]
      rw [one_mul, Real.exp_neg] at hY3
      have h1' := mul_le_mul_of_nonneg_right hY3 (Real.exp_pos (1 / 2 * Y ^ (ε / 5))).le
      rw [mul_assoc, inv_mul_cancel₀ (Real.exp_pos _).ne', mul_one] at h1'
      have hEq : 1 / 2 * Y ^ (ε / 5) = Y ^ (ε / 5) / 2 := by ring
      rw [hEq] at h1'; linarith [Real.exp_pos (Y ^ (ε / 5) / 2)]
    have hB_sq : ((max 2 ⌊Y ^ (ε / 5)⌋₊ : ℕ) : ℝ) ^ 2 ≤ Y := by
      have h1' : ((max 2 ⌊Y ^ (ε / 5)⌋₊ : ℕ) : ℝ) ≤ Y ^ (ε / 5) + 2 := by
        rw [Nat.cast_max]; push_cast
        exact max_le (by linarith) ((Nat.floor_le (by positivity)).trans (by linarith))
      exact (pow_le_pow_left₀ (Nat.cast_nonneg _) h1' 2).trans hY4
    have hL2 : 2 ≤ Real.log Y := (Real.log_exp 2).symm.trans_le (Real.log_le_log (Real.exp_pos 2) hY5)
    exact ⟨hY1, hU_ge3, by linarith [Real.log_nonneg (show (1 : ℝ) ≤ (N_max : ℝ) + 2 by linarith)], hN_lt, hZ_lt, hB_sq, hL2⟩
  -- Asymptotics for `log Q₁, log Q₂` bounds (`Y^(ε/6) ≤ log Q ≤ Y^(ε/4)`), Linnik log-scale conditions, and `BadShare`!
  have hev_scales : ∀ᶠ Y : ℝ in Filter.atTop,
      -- (1) Stage 1 & 2 `log Q` sandwich:
      Y ^ (ε / 6) ≤ Y ^ (ε / 5) / 2 ∧
      Real.log (2 * (N_max : ℝ)) + Y ^ (ε / 5) + Y ^ (ε / 5) * Real.log Y ^ 2 ≤ Y ^ (ε / 4) ∧
      -- (2) Stage 1 & 2 `C_tw` scale conditions:
      C_tw * (Real.log 8 + 2 * (K_Z : ℝ) * K * Real.log Y) * ((K_Z : ℝ) * K * Real.log Y + 1) ≤ Y ^ (ε / 5) / 2 ∧
      C_tw * (4 * Y ^ (ε / 5) + 2 * (K_Z : ℝ) * K * Real.log Y) * ((K_Z : ℝ) * K * Real.log Y + 1) ≤
        Y ^ (ε / 5) * Real.log Y ^ 2 / 2 ∧
      -- (3) `BadShare` MSq fraction `≤ 1 / (8 * m_fam)`:
      ((⌈K * Real.log Y / Real.log 2⌉₊ + 1 : ℕ) : ℝ) * (2400 * ((K_Z : ℝ) * K * Real.log Y + 2) ^ 2 / Y ^ (2 * τ)) ≤
        1 / (8 * m_fam) ∧
      -- (4) Stage 1 & 2 `BadShare` ZeroFreeBox fraction `≤ 1 / (8 * m_fam)`:
      C_zd * (2 * (N_max : ℝ) * Real.exp (Y ^ (ε / 5) / 2)) ^ (1 / 4 : ℝ) *
        (Real.exp (Y ^ (ε / 5) / 2) / 2 * (Real.log 2 + Y ^ (ε / 5) / 2)) ≤
        (1 / (8 * m_fam)) * (c_w * Real.exp (Y ^ (ε / 5) / 2) ^ 2 / ((8 : ℝ) ^ ((3 : ℝ) / 2))) ∧
      C_zd * (2 * (N_max : ℝ) * Real.exp (Y ^ (ε / 5)) * Real.exp (Y ^ (ε / 5) * Real.log Y ^ 2 / 2)) ^ (1 / 4 : ℝ) *
        (Real.exp (Y ^ (ε / 5) * Real.log Y ^ 2 / 2) / 2 * (Real.log 2 + Y ^ (ε / 5) * Real.log Y ^ 2 / 2)) ≤
        (1 / (8 * m_fam)) * (c_w * Real.exp (Y ^ (ε / 5) * Real.log Y ^ 2 / 2) ^ 2 / Real.exp (6 * Y ^ (ε / 5))) := by
    have hs1 : ∀ᶠ Y : ℝ in Filter.atTop, Y ^ (ε / 6) ≤ Y ^ (ε / 5) / 2 := by
      have hd : 0 < ε / 5 - ε / 6 := by linarith
      filter_upwards [(tendsto_rpow_atTop hd).eventually_ge_atTop 2, Filter.eventually_gt_atTop (0 : ℝ)] with Y hY hY0
      calc Y ^ (ε / 6) ≤ (1 / 2 : ℝ) * Y ^ (ε / 5 - ε / 6) * Y ^ (ε / 6) := by nlinarith [Real.rpow_nonneg hY0.le (ε / 6)]
        _ = Y ^ (ε / 5) / 2 := by rw [mul_assoc, ← Real.rpow_add hY0, sub_add_cancel]; ring
    have hs2 : ∀ᶠ Y : ℝ in Filter.atTop,
        Real.log (2 * (N_max : ℝ)) + Y ^ (ε / 5) + Y ^ (ε / 5) * Real.log Y ^ 2 ≤ Y ^ (ε / 4) := by
      have hd : 0 < ε / 4 - ε / 5 := by linarith
      have h1 := eventually_log_pow_le_rpow (c := 1) (η := 1 / 3) (d := ε / 4 - ε / 5) 2 hd (by norm_num)
      have h2 := (tendsto_rpow_atTop hd).eventually_ge_atTop 3
      have h3 := (tendsto_rpow_atTop (by positivity : 0 < ε / 4)).eventually_ge_atTop (3 * |Real.log (2 * (N_max : ℝ))| + 3)
      filter_upwards [h1, h2, h3, Filter.eventually_gt_atTop (0 : ℝ)] with Y h1' h2' h3' hY0
      have hsp : Y ^ (ε / 5) * Y ^ (ε / 4 - ε / 5) = Y ^ (ε / 4) := by rw [← Real.rpow_add hY0, add_sub_cancel]
      have ha : Real.log (2 * (N_max : ℝ)) ≤ Y ^ (ε / 4) / 3 := by linarith [le_abs_self (Real.log (2 * (N_max : ℝ)))]
      have hb : Y ^ (ε / 5) ≤ Y ^ (ε / 4) / 3 := by
        have := mul_le_mul_of_nonneg_left h2' (Real.rpow_nonneg hY0.le (ε / 5)); linarith
      have hc : Y ^ (ε / 5) * Real.log Y ^ 2 ≤ Y ^ (ε / 4) / 3 := by
        rw [one_mul] at h1'
        have := mul_le_mul_of_nonneg_left h1' (Real.rpow_nonneg hY0.le (ε / 5)); linarith
      linarith
    have hs3 : ∀ᶠ Y : ℝ in Filter.atTop,
        C_tw * (Real.log 8 + 2 * (K_Z : ℝ) * K * Real.log Y) * ((K_Z : ℝ) * K * Real.log Y + 1) ≤ Y ^ (ε / 5) / 2 := by
      have h1 := eventually_log_pow_le_rpow (c := C_tw * (Real.log 8 + 2 * (K_Z : ℝ) * K) * ((K_Z : ℝ) * K + 1))
        (η := 1 / 2) (d := ε / 5) 2 (by positivity) (by norm_num)
      filter_upwards [h1, Filter.eventually_ge_atTop (Real.exp 1)] with Y hY1 hYe
      have hL1 : 1 ≤ Real.log Y := (Real.log_exp 1).symm.trans_le (Real.log_le_log (Real.exp_pos 1) hYe)
      have ha : Real.log 8 + 2 * (K_Z : ℝ) * K * Real.log Y ≤ (Real.log 8 + 2 * (K_Z : ℝ) * K) * Real.log Y := by
        have : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num); nlinarith
      have hb : (K_Z : ℝ) * K * Real.log Y + 1 ≤ ((K_Z : ℝ) * K + 1) * Real.log Y := by nlinarith
      calc C_tw * (Real.log 8 + 2 * (K_Z : ℝ) * K * Real.log Y) * ((K_Z : ℝ) * K * Real.log Y + 1)
          ≤ C_tw * ((Real.log 8 + 2 * (K_Z : ℝ) * K) * Real.log Y) * (((K_Z : ℝ) * K + 1) * Real.log Y) := by
            have hnn1 : 0 ≤ Real.log 8 + 2 * (K_Z : ℝ) * K * Real.log Y := add_nonneg (Real.log_nonneg (by norm_num)) (by positivity)
            exact mul_le_mul (mul_le_mul_of_nonneg_left ha (by linarith)) hb (by positivity) (by positivity)
        _ = C_tw * (Real.log 8 + 2 * (K_Z : ℝ) * K) * ((K_Z : ℝ) * K + 1) * Real.log Y ^ 2 := by ring
        _ ≤ (1 / 2 : ℝ) * Y ^ (ε / 5) := hY1
        _ = Y ^ (ε / 5) / 2 := by ring
    have hs4 : ∀ᶠ Y : ℝ in Filter.atTop,
        C_tw * (4 * Y ^ (ε / 5) + 2 * (K_Z : ℝ) * K * Real.log Y) * ((K_Z : ℝ) * K * Real.log Y + 1) ≤
          Y ^ (ε / 5) * Real.log Y ^ 2 / 2 := by
      have h1 := eventually_log_pow_le_rpow (c := 2 * (K_Z : ℝ) * K) (η := 1) (d := ε / 5) 1 (by positivity) one_pos
      have h2 := Filter.eventually_ge_atTop (Real.exp (max 1 (10 * C_tw * ((K_Z : ℝ) * K + 1))))
      filter_upwards [h1, h2, Filter.eventually_gt_atTop (0 : ℝ)] with Y hY1 hY2 hY0
      have hL_ge : max 1 (10 * C_tw * ((K_Z : ℝ) * K + 1)) ≤ Real.log Y :=
        (Real.log_exp _).symm.trans_le (Real.log_le_log (Real.exp_pos _) hY2)
      have hL1 : 1 ≤ Real.log Y := (le_max_left _ _).trans hL_ge
      have hLbig : 10 * C_tw * ((K_Z : ℝ) * K + 1) ≤ Real.log Y := (le_max_right _ _).trans hL_ge
      rw [pow_one, one_mul] at hY1
      have ha : 4 * Y ^ (ε / 5) + 2 * (K_Z : ℝ) * K * Real.log Y ≤ 5 * Y ^ (ε / 5) := by linarith
      have hb : (K_Z : ℝ) * K * Real.log Y + 1 ≤ ((K_Z : ℝ) * K + 1) * Real.log Y := by nlinarith
      calc C_tw * (4 * Y ^ (ε / 5) + 2 * (K_Z : ℝ) * K * Real.log Y) * ((K_Z : ℝ) * K * Real.log Y + 1)
          ≤ C_tw * (5 * Y ^ (ε / 5)) * (((K_Z : ℝ) * K + 1) * Real.log Y) :=
            mul_le_mul (mul_le_mul_of_nonneg_left ha (by linarith)) hb (by positivity) (by positivity)
        _ = (1 / 2 : ℝ) * Y ^ (ε / 5) * ((10 * C_tw * ((K_Z : ℝ) * K + 1)) * Real.log Y) := by ring
        _ ≤ (1 / 2 : ℝ) * Y ^ (ε / 5) * (Real.log Y * Real.log Y) := by gcongr
        _ = Y ^ (ε / 5) * Real.log Y ^ 2 / 2 := by ring
    have hs5 : ∀ᶠ Y : ℝ in Filter.atTop,
        ((⌈K * Real.log Y / Real.log 2⌉₊ + 1 : ℕ) : ℝ) * (2400 * ((K_Z : ℝ) * K * Real.log Y + 2) ^ 2 / Y ^ (2 * τ)) ≤
          1 / (8 * m_fam) := by
      have h1 := eventually_log_pow_le_rpow
        (c := (K / Real.log 2 + 2) * (2400 * ((K_Z : ℝ) * K + 2) ^ 2))
        (η := 1 / (8 * m_fam)) (d := 2 * τ) 3 (by positivity) (by positivity)
      filter_upwards [h1, Filter.eventually_ge_atTop (Real.exp 1)] with Y hY1 hYe
      have hY0 : 0 < Y := lt_of_lt_of_le (Real.exp_pos 1) hYe
      have hL1 : 1 ≤ Real.log Y := (Real.log_exp 1).symm.trans_le (Real.log_le_log (Real.exp_pos 1) hYe)
      have hJ_le : ((⌈K * Real.log Y / Real.log 2⌉₊ + 1 : ℕ) : ℝ) ≤ (K / Real.log 2 + 2) * Real.log Y := by
        have hceil : (⌈K * Real.log Y / Real.log 2⌉₊ : ℝ) ≤ K * Real.log Y / Real.log 2 + 1 :=
          (Nat.ceil_lt_add_one (by positivity)).le
        push_cast
        have hEq : K * Real.log Y / Real.log 2 = (K / Real.log 2) * Real.log Y := by ring
        nlinarith
      have hsq_le : ((K_Z : ℝ) * K * Real.log Y + 2) ^ 2 ≤ ((K_Z : ℝ) * K + 2) ^ 2 * Real.log Y ^ 2 := by
        have h1' : (K_Z : ℝ) * K * Real.log Y + 2 ≤ ((K_Z : ℝ) * K + 2) * Real.log Y := by nlinarith
        calc ((K_Z : ℝ) * K * Real.log Y + 2) ^ 2 ≤ (((K_Z : ℝ) * K + 2) * Real.log Y) ^ 2 :=
              pow_le_pow_left₀ (by positivity) h1' 2
          _ = ((K_Z : ℝ) * K + 2) ^ 2 * Real.log Y ^ 2 := by ring
      have hnum : ((⌈K * Real.log Y / Real.log 2⌉₊ + 1 : ℕ) : ℝ) * (2400 * ((K_Z : ℝ) * K * Real.log Y + 2) ^ 2) ≤
          (1 / (8 * m_fam)) * Y ^ (2 * τ) := by
        calc ((⌈K * Real.log Y / Real.log 2⌉₊ + 1 : ℕ) : ℝ) * (2400 * ((K_Z : ℝ) * K * Real.log Y + 2) ^ 2)
            ≤ ((K / Real.log 2 + 2) * Real.log Y) * (2400 * (((K_Z : ℝ) * K + 2) ^ 2 * Real.log Y ^ 2)) :=
              mul_le_mul hJ_le (mul_le_mul_of_nonneg_left hsq_le (by norm_num)) (by positivity) (by positivity)
          _ = (K / Real.log 2 + 2) * (2400 * ((K_Z : ℝ) * K + 2) ^ 2) * Real.log Y ^ 3 := by ring
          _ ≤ (1 / (8 * m_fam)) * Y ^ (2 * τ) := hY1
      rw [mul_div_assoc', div_le_iff₀ (Real.rpow_pos_of_pos hY0 _)]; exact hnum
    have hs6 : ∀ᶠ Y : ℝ in Filter.atTop,
        C_zd * (2 * (N_max : ℝ) * Real.exp (Y ^ (ε / 5) / 2)) ^ (1 / 4 : ℝ) *
          (Real.exp (Y ^ (ε / 5) / 2) / 2 * (Real.log 2 + Y ^ (ε / 5) / 2)) ≤
          (1 / (8 * m_fam)) * (c_w * Real.exp (Y ^ (ε / 5) / 2) ^ 2 / ((8 : ℝ) ^ ((3 : ℝ) / 2))) := by
      set C1 : ℝ := C_zd * (2 * (N_max : ℝ)) ^ (1 / 4 : ℝ) * (Real.log 2 + 1) * (8 * m_fam * (8 : ℝ) ^ ((3 : ℝ) / 2) / c_w)
      have h1 := eventually_rpow_exp_neg_rpow_le (c := C1) (a := ε / 5) (b := 3 / 8) (d := ε / 5) (η := 1)
        (by norm_num) (by positivity) one_pos
      filter_upwards [h1, (tendsto_rpow_atTop (by positivity : 0 < ε / 5)).eventually_ge_atTop 2] with Y hY1 hU2
      set X1 := Real.exp (Y ^ (ε / 5) / 2)
      have hX1_pos : 0 < X1 := Real.exp_pos _
      have hX1_rpow : X1 ^ (1 / 4 : ℝ) * X1 / X1 ^ 2 = Real.exp (-(3 / 8 * Y ^ (ε / 5))) := by
        rw [show X1 = Real.exp (Y ^ (ε / 5) / 2) from rfl, ← Real.exp_mul, ← Real.exp_add,
          sq, ← Real.exp_add, ← Real.exp_sub]
        congr 1; ring
      have hlog_le : (Real.log 2 + Y ^ (ε / 5) / 2) / 2 ≤ (Real.log 2 + 1) * Y ^ (ε / 5) := by
        have : 0 ≤ Real.log 2 := hlog2_pos.le; nlinarith
      have hLHS_le : C_zd * (2 * (N_max : ℝ) * X1) ^ (1 / 4 : ℝ) * (X1 / 2 * (Real.log 2 + Y ^ (ε / 5) / 2)) ≤
          (C_zd * (2 * (N_max : ℝ)) ^ (1 / 4 : ℝ) * (Real.log 2 + 1)) * Y ^ (ε / 5) * (X1 ^ (1 / 4 : ℝ) * X1) := by
        rw [Real.mul_rpow (by positivity) hX1_pos.le]
        have hEq1 : C_zd * ((2 * (N_max : ℝ)) ^ (1 / 4 : ℝ) * X1 ^ (1 / 4 : ℝ)) * (X1 / 2 * (Real.log 2 + Y ^ (ε / 5) / 2)) =
            (C_zd * (2 * (N_max : ℝ)) ^ (1 / 4 : ℝ)) * ((Real.log 2 + Y ^ (ε / 5) / 2) / 2) * (X1 ^ (1 / 4 : ℝ) * X1) := by ring
        rw [hEq1]
        have h1' := mul_le_mul_of_nonneg_left hlog_le (show 0 ≤ C_zd * (2 * (N_max : ℝ)) ^ (1 / 4 : ℝ) by positivity)
        have h2' := mul_le_mul_of_nonneg_right h1' (show 0 ≤ X1 ^ (1 / 4 : ℝ) * X1 by positivity)
        linarith
      have hratio : C1 * Y ^ (ε / 5) * (X1 ^ (1 / 4 : ℝ) * X1 / X1 ^ 2) ≤ 1 := by rw [hX1_rpow]; exact hY1
      have hmul := mul_le_mul_of_nonneg_right hratio (show 0 ≤ (1 / (8 * m_fam)) * (c_w * X1 ^ 2 / ((8 : ℝ) ^ ((3 : ℝ) / 2))) by positivity)
      rw [one_mul] at hmul
      have hcancel : C1 * Y ^ (ε / 5) * (X1 ^ (1 / 4 : ℝ) * X1 / X1 ^ 2) *
          ((1 / (8 * m_fam)) * (c_w * X1 ^ 2 / ((8 : ℝ) ^ ((3 : ℝ) / 2)))) =
          (C_zd * (2 * (N_max : ℝ)) ^ (1 / 4 : ℝ) * (Real.log 2 + 1)) * Y ^ (ε / 5) * (X1 ^ (1 / 4 : ℝ) * X1) := by
        dsimp only [C1]
        field_simp [hmfam_pos.ne', hcw_pos.ne', (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 8) _).ne', hX1_pos.ne']
      linarith
    have hs7 : ∀ᶠ Y : ℝ in Filter.atTop,
        C_zd * (2 * (N_max : ℝ) * Real.exp (Y ^ (ε / 5)) * Real.exp (Y ^ (ε / 5) * Real.log Y ^ 2 / 2)) ^ (1 / 4 : ℝ) *
          (Real.exp (Y ^ (ε / 5) * Real.log Y ^ 2 / 2) / 2 * (Real.log 2 + Y ^ (ε / 5) * Real.log Y ^ 2 / 2)) ≤
          (1 / (8 * m_fam)) * (c_w * Real.exp (Y ^ (ε / 5) * Real.log Y ^ 2 / 2) ^ 2 / Real.exp (6 * Y ^ (ε / 5))) := by
      set C2 : ℝ := C_zd * (2 * (N_max : ℝ)) ^ (1 / 4 : ℝ) * (Real.log 2 + 1) * (8 * m_fam / c_w)
      have h1 := eventually_rpow_exp_neg_rpow_le (c := C2) (a := ε / 5 + 1) (b := 1) (d := ε / 5) (η := 1)
        one_pos (by positivity) one_pos
      have h2 := Filter.eventually_ge_atTop (Real.exp 8)
      have h3 := eventually_log_pow_le_rpow (c := 1) (η := 1) (d := 1) 2 one_pos one_pos
      filter_upwards [h1, h2, h3, (tendsto_rpow_atTop (by positivity : 0 < ε / 5)).eventually_ge_atTop 2] with Y hY1 hYe8 hL2Y hU2
      have hY0 : 0 < Y := lt_of_lt_of_le (Real.exp_pos 8) hYe8
      have hL8 : 8 ≤ Real.log Y := (Real.log_exp 8).symm.trans_le (Real.log_le_log (Real.exp_pos 8) hYe8)
      set U := Y ^ (ε / 5)
      set X2 := Real.exp (U * Real.log Y ^ 2 / 2)
      have hX2_pos : 0 < X2 := Real.exp_pos _
      have hU_pos : 0 < U := by linarith
      have hexp_combo : Real.exp U ^ (1 / 4 : ℝ) * X2 ^ (1 / 4 : ℝ) * X2 / (X2 ^ 2 / Real.exp (6 * U)) ≤ Real.exp (-U) := by
        rw [show X2 = Real.exp (U * Real.log Y ^ 2 / 2) from rfl, div_div_eq_mul_div,
          ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
          ← Real.exp_nat_mul, ← Real.exp_sub]
        refine Real.exp_le_exp.mpr ?_
        push_cast
        have h64 : 64 ≤ Real.log Y ^ 2 := by nlinarith
        nlinarith
      have hlog_le : (Real.log 2 + U * Real.log Y ^ 2 / 2) / 2 ≤ (Real.log 2 + 1) * Y ^ (ε / 5 + 1) := by
        rw [one_mul, one_mul, Real.rpow_one] at hL2Y
        have hUY : U * Real.log Y ^ 2 ≤ Y ^ (ε / 5 + 1) := by
          rw [Real.rpow_add hY0, Real.rpow_one]
          exact mul_le_mul_of_nonneg_left hL2Y hU_pos.le
        have h1_le : (1 : ℝ) ≤ Y ^ (ε / 5 + 1) := Real.one_le_rpow (by linarith [Real.add_one_le_exp (8 : ℝ)]) (by positivity)
        have h0_l2 : 0 ≤ Real.log 2 := hlog2_pos.le
        nlinarith
      have hLHS_le :
          C_zd * (2 * (N_max : ℝ) * Real.exp U * X2) ^ (1 / 4 : ℝ) * (X2 / 2 * (Real.log 2 + U * Real.log Y ^ 2 / 2)) ≤
          (C_zd * (2 * (N_max : ℝ)) ^ (1 / 4 : ℝ) * (Real.log 2 + 1)) * Y ^ (ε / 5 + 1) *
            (Real.exp U ^ (1 / 4 : ℝ) * X2 ^ (1 / 4 : ℝ) * X2) := by
        rw [Real.mul_rpow (by positivity) hX2_pos.le, Real.mul_rpow (by positivity) (Real.exp_pos _).le]
        have hEq1 : C_zd * ((2 * (N_max : ℝ)) ^ (1 / 4 : ℝ) * Real.exp U ^ (1 / 4 : ℝ) * X2 ^ (1 / 4 : ℝ)) *
            (X2 / 2 * (Real.log 2 + U * Real.log Y ^ 2 / 2)) =
            (C_zd * (2 * (N_max : ℝ)) ^ (1 / 4 : ℝ)) * ((Real.log 2 + U * Real.log Y ^ 2 / 2) / 2) *
              (Real.exp U ^ (1 / 4 : ℝ) * X2 ^ (1 / 4 : ℝ) * X2) := by ring
        rw [hEq1]
        have h1' := mul_le_mul_of_nonneg_left hlog_le (show 0 ≤ C_zd * (2 * (N_max : ℝ)) ^ (1 / 4 : ℝ) by positivity)
        have h2' := mul_le_mul_of_nonneg_right h1' (show 0 ≤ Real.exp U ^ (1 / 4 : ℝ) * X2 ^ (1 / 4 : ℝ) * X2 by positivity)
        linarith
      have hratio : C2 * Y ^ (ε / 5 + 1) * (Real.exp U ^ (1 / 4 : ℝ) * X2 ^ (1 / 4 : ℝ) * X2 / (X2 ^ 2 / Real.exp (6 * U))) ≤ 1 := by
        have h1' : C2 * Y ^ (ε / 5 + 1) * Real.exp (-U) ≤ 1 := by simpa only [one_mul] using hY1
        exact (mul_le_mul_of_nonneg_left hexp_combo (by positivity)).trans h1'
      have hmul := mul_le_mul_of_nonneg_right hratio
        (show 0 ≤ (1 / (8 * m_fam)) * (c_w * X2 ^ 2 / Real.exp (6 * U)) by positivity)
      rw [one_mul] at hmul
      have hcancel :
          C2 * Y ^ (ε / 5 + 1) * (Real.exp U ^ (1 / 4 : ℝ) * X2 ^ (1 / 4 : ℝ) * X2 / (X2 ^ 2 / Real.exp (6 * U))) *
            ((1 / (8 * m_fam)) * (c_w * X2 ^ 2 / Real.exp (6 * U))) =
          (C_zd * (2 * (N_max : ℝ)) ^ (1 / 4 : ℝ) * (Real.log 2 + 1)) * Y ^ (ε / 5 + 1) *
            (Real.exp U ^ (1 / 4 : ℝ) * X2 ^ (1 / 4 : ℝ) * X2) := by
        dsimp only [C2]
        field_simp [hmfam_pos.ne', hcw_pos.ne', hX2_pos.ne', (Real.exp_pos (6 * U)).ne']
      linarith
    filter_upwards [hs1, hs2, hs3, hs4, hs5, hs6, hs7] with Y h1 h2 h3 h4 h5 h6 h7
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨Y₁, hY₁⟩ := Filter.eventually_atTop.mp (hev_base.and hev_scales)
  refine ⟨max Y₁ 16, le_max_right _ _, fun Y hY => ?_⟩
  obtain ⟨⟨hY_box, hU3, h2log2, hN_lt_X1, hZ_lt_X1, hB2_Y, hLY2⟩,
    ⟨hU6, hQ_hi_all, htw1, htw2, hmsq_frac, hzf1_frac, hzf2_frac⟩⟩ := hY₁ Y ((le_max_left _ _).trans hY)
  have hY16 : 16 ≤ Y := (le_max_right _ _).trans hY
  have hY0 : 0 < Y := by linarith
  set U : ℝ := Y ^ (ε / 5)
  set Z : ℝ := (Y ^ K) ^ K_Z
  have hYK_Z : Y ^ K ≤ Z := (pow_one (Y ^ K)).symm.le.trans (pow_le_pow_right₀ (by
    have := Real.one_le_rpow (by linarith : 1 ≤ Y) (by linarith : 0 ≤ K); exact this) (by dsimp only [K_Z]; omega))
  have hLZ_eq : Real.log Z = (K_Z : ℝ) * K * Real.log Y := by
    rw [show Z = (Y ^ K) ^ K_Z from rfl, Real.log_pow, Real.log_rpow hY0 K]; ring
  -- =========================================================================
  -- STAGE 1: Pick prime `q ∈ apPrimes 8 3 X₁` good for EVERY `ψ ∈ Ψ`!
  -- =========================================================================
  set X₁ : ℝ := Real.exp (U / 2)
  have hX1_pos : 0 < X₁ := Real.exp_pos _
  have hX1_ge1 : 1 ≤ X₁ := Real.one_le_exp (by linarith)
  set P₁ := apPrimes 8 3 X₁
  set W₁ := ∑ r ∈ P₁, tentWt X₁ r
  set Q₁ : ℝ := 2 * (N_max : ℝ) * X₁
  have hQ1_ge3 : 3 ≤ Q₁ := by
    have hN2 : (2 : ℝ) ≤ (N_max : ℝ) := by dsimp only [N_max]; exact_mod_cast (by omega : 2 ≤ Ψ.sup PChar.N + 2)
    dsimp only [Q₁]; nlinarith only [hN2, hX1_ge1]
  have hQ1_lo : Y ^ (ε / 6) ≤ Real.log Q₁ := by
    have h1 : X₁ ≤ Q₁ := by
      have hN2 : (2 : ℝ) ≤ (N_max : ℝ) := by dsimp only [N_max]; exact_mod_cast (by omega : 2 ≤ Ψ.sup PChar.N + 2)
      dsimp only [Q₁]; nlinarith only [hN2, hX1_pos]
    calc Y ^ (ε / 6) ≤ U / 2 := hU6
      _ = Real.log X₁ := (Real.log_exp _).symm
      _ ≤ Real.log Q₁ := Real.log_le_log hX1_pos h1
  have hQ1_hi : Real.log Q₁ ≤ Y ^ (ε / 4) := by
    rw [show Q₁ = (2 * (N_max : ℝ)) * X₁ from rfl, Real.log_mul (by positivity) hX1_pos.ne', Real.log_exp]
    have hnn : 0 ≤ U * Real.log Y ^ 2 := by positivity
    linarith
  have hP1_props : ∀ r ∈ P₁, r.Prime ∧ r % 4 = 3 ∧ X₁ < (r : ℝ) ∧ (r : ℝ) ≤ 2 * X₁ := fun r hr => by
    obtain ⟨hI, hpr, hmod⟩ := Finset.mem_filter.mp hr
    have h8 : r % 8 = 3 := hmod
    exact ⟨hpr, by omega,
      lt_of_lt_of_le (Nat.lt_floor_add_one X₁) (by exact_mod_cast (Finset.mem_Ioc.mp hI).1),
      (by exact_mod_cast (Finset.mem_Ioc.mp hI).2 : (r : ℝ) ≤ (⌊2 * X₁⌋₊ : ℝ)).trans (Nat.floor_le (by linarith))⟩
  have hlogX1_tw : C_tw * Real.log ((8 : ℝ) * Z ^ 2) * (Real.log Z + 1) ≤ Real.log X₁ := by
    rw [Real.log_exp, Real.log_mul (by norm_num) (by positivity), Real.log_pow, hLZ_eq]; push_cast
    simpa [mul_assoc] using htw1
  have hW1_ge : c_w * X₁ ^ 2 / ((8 : ℝ) ^ ((3 : ℝ) / 2)) ≤ W₁ := by
    have hP1N_lt : (PChar.one.N : ℝ) < X₁ := by
      change ((1 : ℕ) : ℝ) < X₁
      have h2_le : (2 : ℝ) ≤ (N_max : ℝ) := by dsimp only [N_max]; exact_mod_cast (by omega : 2 ≤ Ψ.sup PChar.N + 2)
      push_cast; linarith
    exact (hmsq 8 3 2 dvd_rfl (by norm_num) (by norm_num) le_rfl PChar.one Y K τ Z X₁
      hY16 hK1 hτ0 hYK_Z (by norm_num; linarith) (fun p hp hp2 hdvd _ => by
        have h2 : p ∣ 2 ^ 3 := by simpa using hdvd
        exact absurd (hp.dvd_of_dvd_pow h2) (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)))
      hZ_lt_X1 hP1N_lt hlogX1_tw).1
  have hW1_pos : 0 < W₁ := lt_of_lt_of_le (by positivity) hW1_ge
  let Bad1_MS : PChar → Finset ℕ := fun ψ =>
    P₁.filter fun r => ∃ hr : r.Prime,
      haveI : NeZero r := ⟨hr.ne_zero⟩
      ¬ ∀ y ∈ Set.Icc Y (Y ^ K),
        ‖Sz (Stage11SecondMomentFrame.twistedChar ψ.χ (quadCharOfPrime r hr)) y Z‖ ≤
          y ^ ((1 : ℝ) / 2 + τ) / 2
  let Bad1_ZF : PChar → Finset ℕ := fun ψ =>
    P₁.filter fun r => ∃ hr : r.Prime,
      haveI : NeZero r := ⟨hr.ne_zero⟩
      ¬ ZeroFreeBoxDelta δ₀ Q₁ (Stage11SecondMomentFrame.twistedChar ψ.χ (quadCharOfPrime r hr))
  have hBad1_le : ∑ r ∈ Ψ.biUnion (fun ψ => Bad1_MS ψ ∪ Bad1_ZF ψ), tentWt X₁ r < W₁ := by
    have hper : ∀ ψ ∈ Ψ, ∑ r ∈ Bad1_MS ψ ∪ Bad1_ZF ψ, tentWt X₁ r ≤ (1 / (4 * m_fam)) * W₁ := by
      intro ψ hψ
      have hψN_lt : (ψ.N : ℝ) < X₁ := by
        have hle : ψ.N ≤ Ψ.sup PChar.N := Finset.le_sup (f := PChar.N) hψ
        have hlt : (ψ.N : ℝ) < (N_max : ℝ) := by dsimp only [N_max]; exact_mod_cast (by omega : ψ.N < Ψ.sup PChar.N + 2)
        exact hlt.trans hN_lt_X1
      have hms1 := (hmsq 8 3 2 dvd_rfl (by norm_num) (by norm_num) le_rfl ψ Y K τ Z X₁
        hY16 hK1 hτ0 hYK_Z (by norm_num; linarith) (fun p hp hp2 hdvd _ => by
          have h2 : p ∣ 2 ^ 3 := by simpa using hdvd
          exact absurd (hp.dvd_of_dvd_pow h2) (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)))
        hZ_lt_X1 hψN_lt hlogX1_tw).2
      rw [hLZ_eq] at hms1
      have hms1' : ∑ r ∈ Bad1_MS ψ, tentWt X₁ r ≤ (1 / (8 * m_fam)) * W₁ :=
        hms1.trans (mul_le_mul_of_nonneg_right hmsq_frac hW1_pos.le)
      have hQ1_ge_ψ : 2 * (ψ.N : ℝ) * X₁ ≤ Q₁ := by
        have hle : (ψ.N : ℝ) ≤ (N_max : ℝ) := by
          have := Finset.le_sup (f := PChar.N) hψ
          dsimp only [N_max]; exact_mod_cast (by omega : ψ.N ≤ Ψ.sup PChar.N + 2)
        dsimp only [Q₁]; gcongr
      have hzf1 := tentWt_badZF_le hzd hX1_ge1 hQ1_ge3 hψN_lt hQ1_ge_ψ P₁ hP1_props
      have hlog2X1 : Real.log (2 * X₁) = Real.log 2 + U / 2 := by
        rw [Real.log_mul (by norm_num) hX1_pos.ne', Real.log_exp]
      rw [hlog2X1] at hzf1
      have hzf1' : ∑ r ∈ Bad1_ZF ψ, tentWt X₁ r ≤ (1 / (8 * m_fam)) * W₁ :=
        hzf1.trans (hzf1_frac.trans (mul_le_mul_of_nonneg_left hW1_ge (by positivity)))
      calc ∑ r ∈ Bad1_MS ψ ∪ Bad1_ZF ψ, tentWt X₁ r
          ≤ (∑ r ∈ Bad1_MS ψ, tentWt X₁ r) + ∑ r ∈ Bad1_ZF ψ, tentWt X₁ r :=
            sum_union_le_of_nonneg fun r _ => tentWt_nonneg hX1_pos.le r
        _ ≤ (1 / (8 * m_fam)) * W₁ + (1 / (8 * m_fam)) * W₁ := add_le_add hms1' hzf1'
        _ = (1 / (4 * m_fam)) * W₁ := by ring
    calc ∑ r ∈ Ψ.biUnion (fun ψ => Bad1_MS ψ ∪ Bad1_ZF ψ), tentWt X₁ r
        ≤ ∑ ψ ∈ Ψ, ∑ r ∈ Bad1_MS ψ ∪ Bad1_ZF ψ, tentWt X₁ r :=
          sum_biUnion_le_of_nonneg fun r => tentWt_nonneg hX1_pos.le r
      _ ≤ ∑ _ψ ∈ Ψ, (1 / (4 * m_fam)) * W₁ := Finset.sum_le_sum hper
      _ = (Ψ.card : ℝ) * ((1 / (4 * m_fam)) * W₁) := by simp
      _ ≤ m_fam * ((1 / (4 * m_fam)) * W₁) := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      _ = (1 / 4 : ℝ) * W₁ := by field_simp [hmfam_pos.ne']
      _ < W₁ := by linarith
  -- Extract a good prime `q ∈ P₁ \ ⋃_ψ (Bad1_MS ψ ∪ Bad1_ZF ψ)`!
  obtain ⟨q, hq_mem⟩ : (P₁ \ Ψ.biUnion (fun ψ => Bad1_MS ψ ∪ Bad1_ZF ψ)).Nonempty := by
    by_contra hemp; rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hsub : P₁ ⊆ Ψ.biUnion (fun ψ => Bad1_MS ψ ∪ Bad1_ZF ψ) := Finset.sdiff_eq_empty_iff_subset.mp hemp
    have hle : W₁ ≤ ∑ r ∈ Ψ.biUnion (fun ψ => Bad1_MS ψ ∪ Bad1_ZF ψ), tentWt X₁ r :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun r _ _ => tentWt_nonneg hX1_pos.le r
    linarith
  obtain ⟨hq_P1, hq_notBad1⟩ := Finset.mem_sdiff.mp hq_mem
  obtain ⟨hq_pr, hq4, hq_gt_X1, hq_le_2X1⟩ := hP1_props q hq_P1
  have hq8 : q % 8 = 3 := (Finset.mem_filter.mp hq_P1).2.2
  have hq_le_expU : (q : ℝ) ≤ Real.exp U := by
    calc (q : ℝ) ≤ 2 * Real.exp (U / 2) := hq_le_2X1
      _ = Real.exp (Real.log 2 + U / 2) := by rw [Real.exp_add, Real.exp_log (by norm_num)]
      _ ≤ Real.exp U := Real.exp_le_exp.mpr (by linarith)
  have hq_log_up : Real.log (q : ℝ) ≤ U := (Real.log_le_iff_le_exp (Nat.cast_pos.mpr hq_pr.pos)).mpr hq_le_expU
  have : NeZero q := ⟨hq_pr.ne_zero⟩
  -- =========================================================================
  -- STAGE 2: Given `q`, pick prime `d ∈ apPrimes m₀ a₀ X₂` good for ALL `ψ, ψ · χ_q`!
  -- =========================================================================
  set m₀ : ℕ := Stage2PrimePairs.pairModulus q ⌊U⌋₊
  set a₀ : ℕ := Stage2PrimePairs.pairResidue q ⌊U⌋₊
  set B : ℕ := max 2 ⌊U⌋₊
  have h8_m0 : 8 ∣ m₀ := ⟨2 * (q * Stage2PrimePairs.oddPrimorial ⌊U⌋₊), by dsimp only [m₀, Stage2PrimePairs.pairModulus]; ring⟩
  have hcop_a0m0 : Nat.Coprime a₀ m₀ := Stage2PrimePairs.coprime_pairResidue_pairModulus hq8
  have ha0_mod4 : a₀ % 4 = 3 := by
    have h16 : a₀ % 16 = 7 := Stage2PrimePairs.eight_mul_sub_one_mod_sixteen (Stage2PrimePairs.odd_mul_oddPrimorial hq8)
    omega
  have hm0_le_exp4U : (m₀ : ℝ) ≤ Real.exp (4 * U) :=
    Stage2PrimePairs.pairModulus_le_exp_four_mul hU3 hq_pr.pos hq_log_up
  have hm0_pos : (0 : ℝ) < (m₀ : ℝ) := by
    have := Stage2PrimePairs.two_le_pairModulus (n := ⌊U⌋₊) hq8; exact_mod_cast (by omega : 0 < m₀)
  set V : ℝ := U * Real.log Y ^ 2
  set X₂ : ℝ := Real.exp (V / 2)
  have hX2_pos : 0 < X₂ := Real.exp_pos _
  have hX2_ge1 : 1 ≤ X₂ := Real.one_le_exp (by positivity)
  have hX1_le_X2 : X₁ ≤ X₂ := Real.exp_le_exp.mpr (by
    have h1 : (1 : ℝ) ≤ Real.log Y ^ 2 := by nlinarith only [hLY2]
    dsimp only [V]; nlinarith only [hU3, h1])
  set P₂ := apPrimes m₀ a₀ X₂
  set W₂ := ∑ r ∈ P₂, tentWt X₂ r
  set Q₂ : ℝ := 2 * (N_max : ℝ) * (q : ℝ) * X₂
  have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq_pr.pos
  have hQ2_ge3 : 3 ≤ Q₂ := by
    have h1 : (2 : ℝ) ≤ (N_max : ℝ) := by dsimp only [N_max]; exact_mod_cast (by omega : 2 ≤ Ψ.sup PChar.N + 2)
    have h2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq_pr.two_le
    have hNq : (4 : ℝ) ≤ (N_max : ℝ) * (q : ℝ) := by nlinarith only [h1, h2]
    dsimp only [Q₂]; nlinarith only [hNq, hX2_ge1]
  have hQ2_lo : Y ^ (ε / 6) ≤ Real.log Q₂ := by
    have h1 : X₁ ≤ Q₂ := by
      have h1' : (2 : ℝ) ≤ (N_max : ℝ) := by dsimp only [N_max]; exact_mod_cast (by omega : 2 ≤ Ψ.sup PChar.N + 2)
      have h2' : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq_pr.two_le
      have hNq : (4 : ℝ) ≤ (N_max : ℝ) * (q : ℝ) := by nlinarith only [h1', h2']
      dsimp only [Q₂]; nlinarith only [hNq, hX1_le_X2, hX1_pos]
    calc Y ^ (ε / 6) ≤ U / 2 := hU6
      _ = Real.log X₁ := (Real.log_exp _).symm
      _ ≤ Real.log Q₂ := Real.log_le_log hX1_pos h1
  have hQ2_hi : Real.log Q₂ ≤ Y ^ (ε / 4) := by
    rw [show Q₂ = ((2 * (N_max : ℝ)) * (q : ℝ)) * X₂ from rfl,
      Real.log_mul (by positivity) hX2_pos.ne', Real.log_mul (by positivity) hq_pos.ne',
      Real.log_exp]
    have hnn : 0 ≤ V / 2 := by positivity
    linarith [hq_log_up, hQ_hi_all]
  have hP2_props : ∀ r ∈ P₂, r.Prime ∧ r % 4 = 3 ∧ X₂ < (r : ℝ) ∧ (r : ℝ) ≤ 2 * X₂ := fun r hr => by
    obtain ⟨hI, hpr, hmod⟩ := Finset.mem_filter.mp hr
    have h4 : r ≡ a₀ [MOD 4] := (hmod.of_dvd h8_m0).of_dvd (by norm_num)
    change r % 4 = a₀ % 4 at h4
    exact ⟨hpr, by omega,
      lt_of_lt_of_le (Nat.lt_floor_add_one X₂) (by exact_mod_cast (Finset.mem_Ioc.mp hI).1),
      (by exact_mod_cast (Finset.mem_Ioc.mp hI).2 : (r : ℝ) ≤ (⌊2 * X₂⌋₊ : ℝ)).trans (Nat.floor_le (by linarith))⟩
  have hsmall_m0 : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ m₀ → (p : ℝ) ≤ Z → p ≤ B := by
    intro p hp hp2 hdvd hpZ
    dsimp only [m₀, Stage2PrimePairs.pairModulus] at hdvd
    have hnot16 : ¬ p ∣ 16 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 4 by simpa using h)))
    rcases hp.dvd_mul.mp ((hp.dvd_mul.mp hdvd).resolve_left hnot16) with hpq | hp_prim
    · have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq_pr).mp hpq
      subst heq; linarith [hZ_lt_X1, hq_gt_X1]
    · -- `p ∣ oddPrimorial ⌊U⌋₊`, so `p ≤ ⌊U⌋₊ ≤ B`!
      have hmem : p ∈ Stage2PrimePairs.oddPrimesUpTo ⌊U⌋₊ := by
        by_contra hnot
        have hcop_p : Nat.Coprime p (Stage2PrimePairs.oddPrimorial ⌊U⌋₊) := by
          unfold Stage2PrimePairs.oddPrimorial
          exact Nat.Coprime.prod_right fun l hl =>
            (Nat.coprime_primes hp (Stage2PrimePairs.mem_oddPrimesUpTo.mp hl).2.1).mpr fun h => hnot (h ▸ hl)
        exact hp.not_isUnit (Nat.isUnit_iff.mpr (Nat.dvd_one.mp (hcop_p.gcd_eq_one ▸ Nat.dvd_gcd dvd_rfl hp_prim)))
      exact (Stage2PrimePairs.mem_oddPrimesUpTo.mp hmem).1.trans (le_max_right _ _)
  have hlogX2_tw : C_tw * Real.log ((m₀ : ℝ) * Z ^ 2) * (Real.log Z + 1) ≤ Real.log X₂ := by
    rw [Real.log_exp, Real.log_mul hm0_pos.ne' (by positivity), Real.log_pow, hLZ_eq]; push_cast
    have hlogm0 : Real.log (m₀ : ℝ) ≤ 4 * U := (Real.log_le_iff_le_exp hm0_pos).mpr hm0_le_exp4U
    have hsum_le : Real.log (m₀ : ℝ) + 2 * ((K_Z : ℝ) * K * Real.log Y) ≤ 4 * U + 2 * (K_Z : ℝ) * K * Real.log Y := by linarith
    have h1 : C_tw * (Real.log (m₀ : ℝ) + 2 * ((K_Z : ℝ) * K * Real.log Y)) * ((K_Z : ℝ) * K * Real.log Y + 1) ≤
        C_tw * (4 * U + 2 * (K_Z : ℝ) * K * Real.log Y) * ((K_Z : ℝ) * K * Real.log Y + 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum_le (by linarith)) (by positivity)
    exact h1.trans htw2
  have hNq_lt_X2 : ((N_max : ℝ) * (q : ℝ)) < X₂ := by
    calc (N_max : ℝ) * (q : ℝ) < Real.exp (U / 2) * (2 * Real.exp (U / 2)) :=
          mul_lt_mul hN_lt_X1 hq_le_2X1 hq_pos hX1_pos.le
      _ = Real.exp (Real.log 2 + U) := by
          calc Real.exp (U / 2) * (2 * Real.exp (U / 2))
              = 2 * (Real.exp (U / 2) * Real.exp (U / 2)) := by ring
            _ = Real.exp (Real.log 2) * Real.exp (U / 2 + U / 2) := by rw [Real.exp_log (by norm_num), ← Real.exp_add]
            _ = Real.exp (Real.log 2 + U) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (V / 2) := Real.exp_le_exp.mpr (by
          have h4 : (4 : ℝ) ≤ Real.log Y ^ 2 := by nlinarith only [hLY2]
          dsimp only [V]; nlinarith only [hU3, h2log2, h4])
  have hW2_ge : c_w * X₂ ^ 2 / Real.exp (6 * U) ≤ W₂ := by
    have hP1N_lt2 : (PChar.one.N : ℝ) < X₂ := by
      change ((1 : ℕ) : ℝ) < X₂
      have h1' : (2 : ℝ) ≤ (N_max : ℝ) := by dsimp only [N_max]; exact_mod_cast (by omega : 2 ≤ Ψ.sup PChar.N + 2)
      have h2' : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq_pr.two_le
      have hNq : (4 : ℝ) ≤ (N_max : ℝ) * (q : ℝ) := by nlinarith only [h1', h2']
      push_cast; linarith
    have h1 := (hmsq m₀ a₀ B h8_m0 hcop_a0m0 ha0_mod4 (le_max_left _ _) PChar.one Y K τ Z X₂
      hY16 hK1 hτ0 hYK_Z hB2_Y hsmall_m0 (hZ_lt_X1.trans_le hX1_le_X2) hP1N_lt2 hlogX2_tw).1
    have hm32 : (m₀ : ℝ) ^ ((3 : ℝ) / 2) ≤ Real.exp (6 * U) := by
      calc (m₀ : ℝ) ^ ((3 : ℝ) / 2) ≤ (Real.exp (4 * U)) ^ ((3 : ℝ) / 2) :=
            Real.rpow_le_rpow hm0_pos.le hm0_le_exp4U (by norm_num)
        _ = Real.exp (6 * U) := by rw [← Real.exp_mul]; congr 1; ring
    exact (div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hm0_pos _) hm32).trans h1
  have hW2_pos : 0 < W₂ := lt_of_lt_of_le (by positivity) hW2_ge
  -- For each `ψ ∈ Ψ`, define the twisted character `ψ_q := twistedChar ψ.χ χ_q` (primitive!) and its 4 bad sets in `P₂`!
  have hψ_cop_q : ∀ ψ ∈ Ψ, ψ.N < q ∧ Nat.Coprime ψ.N q := fun ψ hψ => by
    have hle : ψ.N ≤ Ψ.sup PChar.N := Finset.le_sup (f := PChar.N) hψ
    have hlt_R : (ψ.N : ℝ) < (q : ℝ) :=
      (by dsimp only [N_max]; exact_mod_cast (by omega : ψ.N < Ψ.sup PChar.N + 2) : (ψ.N : ℝ) < (N_max : ℝ)).trans
        (hN_lt_X1.trans hq_gt_X1)
    have hlt : ψ.N < q := by exact_mod_cast hlt_R
    exact ⟨hlt, Stage2PrimePairs.coprime_of_prime_gt (NeZero.pos ψ.N) hq_pr hlt⟩
  let psiQ : {ψ // ψ ∈ Ψ} → PChar := fun ψ =>
    ⟨ψ.1.N * q,
      Stage11SecondMomentFrame.twistedChar ψ.1.χ (quadCharOfPrime q hq_pr),
      twistedChar_isPrimitive (hψ_cop_q ψ.1 ψ.2).2 ψ.1.prim (quadCharOfPrime_isPrimitive_of_mod_four hq_pr hq4)⟩
  let Bad2_MS : PChar → Finset ℕ := fun χP =>
    P₂.filter fun r => ∃ hr : r.Prime,
      haveI : NeZero r := ⟨hr.ne_zero⟩
      ¬ ∀ y ∈ Set.Icc Y (Y ^ K),
        ‖Sz (Stage11SecondMomentFrame.twistedChar χP.χ (quadCharOfPrime r hr)) y Z‖ ≤
          y ^ ((1 : ℝ) / 2 + τ) / 2
  let Bad2_ZF : PChar → Finset ℕ := fun χP =>
    P₂.filter fun r => ∃ hr : r.Prime,
      haveI : NeZero r := ⟨hr.ne_zero⟩
      ¬ ZeroFreeBoxDelta δ₀ Q₂ (Stage11SecondMomentFrame.twistedChar χP.χ (quadCharOfPrime r hr))
  have hBad2_single : ∀ (χP : PChar), (χP.N : ℝ) ≤ (N_max : ℝ) * (q : ℝ) →
      ∑ r ∈ Bad2_MS χP ∪ Bad2_ZF χP, tentWt X₂ r ≤ (1 / (4 * m_fam)) * W₂ := by
    intro χP hχN
    have hχ_lt_X2 : (χP.N : ℝ) < X₂ := lt_of_le_of_lt hχN hNq_lt_X2
    have hms2 := (hmsq m₀ a₀ B h8_m0 hcop_a0m0 ha0_mod4 (le_max_left _ _) χP Y K τ Z X₂
      hY16 hK1 hτ0 hYK_Z hB2_Y hsmall_m0 (hZ_lt_X1.trans_le hX1_le_X2) hχ_lt_X2 hlogX2_tw).2
    rw [hLZ_eq] at hms2
    have hms2' : ∑ r ∈ Bad2_MS χP, tentWt X₂ r ≤ (1 / (8 * m_fam)) * W₂ :=
      hms2.trans (mul_le_mul_of_nonneg_right hmsq_frac hW2_pos.le)
    have hQ2_ge_χ : 2 * (χP.N : ℝ) * X₂ ≤ Q₂ := by dsimp only [Q₂]; nlinarith only [hχN, hX2_pos]
    have hzf2 := tentWt_badZF_le hzd hX2_ge1 hQ2_ge3 hχ_lt_X2 hQ2_ge_χ P₂ hP2_props
    have hlog2X2 : Real.log (2 * X₂) = Real.log 2 + V / 2 := by
      rw [Real.log_mul (by norm_num) hX2_pos.ne', Real.log_exp]
    rw [hlog2X2] at hzf2
    have hQ2_le : Q₂ ≤ 2 * (N_max : ℝ) * Real.exp U * X₂ := by dsimp only [Q₂]; gcongr
    have hzf2' : ∑ r ∈ Bad2_ZF χP, tentWt X₂ r ≤ (1 / (8 * m_fam)) * W₂ := by
      calc ∑ r ∈ Bad2_ZF χP, tentWt X₂ r
          ≤ C_zd * Q₂ ^ (1 / 4 : ℝ) * (X₂ / 2 * (Real.log 2 + V / 2)) := hzf2
        _ ≤ C_zd * (2 * (N_max : ℝ) * Real.exp U * X₂) ^ (1 / 4 : ℝ) * (X₂ / 2 * (Real.log 2 + V / 2)) := by
            have hnn : 0 ≤ X₂ / 2 * (Real.log 2 + V / 2) := by positivity
            gcongr
        _ ≤ (1 / (8 * m_fam)) * (c_w * X₂ ^ 2 / Real.exp (6 * U)) := hzf2_frac
        _ ≤ (1 / (8 * m_fam)) * W₂ := mul_le_mul_of_nonneg_left hW2_ge (by positivity)
    calc ∑ r ∈ Bad2_MS χP ∪ Bad2_ZF χP, tentWt X₂ r
        ≤ (∑ r ∈ Bad2_MS χP, tentWt X₂ r) + ∑ r ∈ Bad2_ZF χP, tentWt X₂ r :=
          sum_union_le_of_nonneg fun r _ => tentWt_nonneg hX2_pos.le r
      _ ≤ (1 / (8 * m_fam)) * W₂ + (1 / (8 * m_fam)) * W₂ := add_le_add hms2' hzf2'
      _ = (1 / (4 * m_fam)) * W₂ := by ring
  let AllBad2 : Finset ℕ := Ψ.attach.biUnion fun ψ => (Bad2_MS ψ.1 ∪ Bad2_ZF ψ.1) ∪ (Bad2_MS (psiQ ψ) ∪ Bad2_ZF (psiQ ψ))
  have hBad2_lt : ∑ r ∈ AllBad2, tentWt X₂ r < W₂ := by
    have hper : ∀ ψ ∈ Ψ.attach,
        ∑ r ∈ (Bad2_MS ψ.1 ∪ Bad2_ZF ψ.1) ∪ (Bad2_MS (psiQ ψ) ∪ Bad2_ZF (psiQ ψ)), tentWt X₂ r ≤
          (1 / (2 * m_fam)) * W₂ := by
      intro ψ _
      have hψN_le : (ψ.1.N : ℝ) ≤ (N_max : ℝ) := by
        have := Finset.le_sup (f := PChar.N) ψ.2
        dsimp only [N_max]; exact_mod_cast (by omega : ψ.1.N ≤ Ψ.sup PChar.N + 2)
      have h1 := hBad2_single ψ.1 (hψN_le.trans (le_mul_of_one_le_right hNmax_pos.le (by exact_mod_cast hq_pr.pos)))
      have h2 := hBad2_single (psiQ ψ) (by change ((ψ.1.N * q : ℕ) : ℝ) ≤ (N_max : ℝ) * (q : ℝ); push_cast; gcongr)
      calc _ ≤ (∑ r ∈ Bad2_MS ψ.1 ∪ Bad2_ZF ψ.1, tentWt X₂ r) +
              ∑ r ∈ Bad2_MS (psiQ ψ) ∪ Bad2_ZF (psiQ ψ), tentWt X₂ r :=
            sum_union_le_of_nonneg fun r _ => tentWt_nonneg hX2_pos.le r
        _ ≤ (1 / (4 * m_fam)) * W₂ + (1 / (4 * m_fam)) * W₂ := add_le_add h1 h2
        _ = (1 / (2 * m_fam)) * W₂ := by ring
    calc ∑ r ∈ AllBad2, tentWt X₂ r
        ≤ ∑ ψ ∈ Ψ.attach, ∑ r ∈ (Bad2_MS ψ.1 ∪ Bad2_ZF ψ.1) ∪ (Bad2_MS (psiQ ψ) ∪ Bad2_ZF (psiQ ψ)), tentWt X₂ r :=
          sum_biUnion_le_of_nonneg fun r => tentWt_nonneg hX2_pos.le r
      _ ≤ ∑ _ψ ∈ Ψ.attach, (1 / (2 * m_fam)) * W₂ := Finset.sum_le_sum hper
      _ = (Ψ.card : ℝ) * ((1 / (2 * m_fam)) * W₂) := by simp
      _ ≤ m_fam * ((1 / (2 * m_fam)) * W₂) := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      _ = (1 / 2 : ℝ) * W₂ := by field_simp [hmfam_pos.ne']
      _ < W₂ := by linarith
  obtain ⟨d, hd_mem⟩ : (P₂ \ AllBad2).Nonempty := by
    by_contra hemp; rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hsub : P₂ ⊆ AllBad2 := Finset.sdiff_eq_empty_iff_subset.mp hemp
    have hle : W₂ ≤ ∑ r ∈ AllBad2, tentWt X₂ r :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun r _ _ => tentWt_nonneg hX2_pos.le r
    linarith
  obtain ⟨hd_P2, hd_notBad2⟩ := Finset.mem_sdiff.mp hd_mem
  obtain ⟨hd_pr, hd4, hd_gt_X2, hd_le_2X2⟩ := hP2_props d hd_P2
  have hd_mod : d ≡ a₀ [MOD m₀] := (Finset.mem_filter.mp hd_P2).2.2
  have hd_le_expV : (d : ℝ) ≤ Real.exp V := by
    calc (d : ℝ) ≤ 2 * Real.exp (V / 2) := hd_le_2X2
      _ = Real.exp (Real.log 2 + V / 2) := by rw [Real.exp_add, Real.exp_log (by norm_num)]
      _ ≤ Real.exp V := Real.exp_le_exp.mpr (by
          have h4 : (4 : ℝ) ≤ Real.log Y ^ 2 := by nlinarith only [hLY2]
          dsimp only [V]; nlinarith only [hU3, h2log2, h4])
  have hWin : WinPair ε Y q d :=
    Stage2PrimePairs.winPair_of_congr_and_bounds hq_pr (show q ≡ 3 [MOD 8] from hq8) hq_gt_X1 hq_le_expU
      hd_pr hd_mod hd_gt_X2 hd_le_expV
  have : NeZero d := ⟨hd_pr.ne_zero⟩
  have hcop_qd : Nat.Coprime q d := by
    have hlt : q < d := by
      have h1 : (q : ℝ) < (d : ℝ) := by
        have hq2X : (q : ℝ) ≤ 2 * X₁ := hq_le_2X1
        have h2X1_le_X2 : 2 * X₁ ≤ X₂ := by
          calc 2 * Real.exp (U / 2) = Real.exp (Real.log 2 + U / 2) := by rw [Real.exp_add, Real.exp_log (by norm_num)]
            _ ≤ Real.exp (V / 2) := Real.exp_le_exp.mpr (by
                have h4 : (4 : ℝ) ≤ Real.log Y ^ 2 := by nlinarith only [hLY2]
                dsimp only [V]; nlinarith only [hU3, h2log2, h4])
        exact lt_of_le_of_lt (hq2X.trans h2X1_le_X2) hd_gt_X2
      exact_mod_cast h1
    exact Stage2PrimePairs.coprime_of_prime_gt hq_pr.pos hd_pr hlt
  -- Assemble `PairGood` for EVERY `ψ ∈ Ψ` using `boxOfS_unconditional` on all 3 off-diagonal twists!
  refine ⟨q, d, hWin, fun ψ hψ => ?_⟩
  obtain ⟨hψ_lt_q, hcop_Nq⟩ := hψ_cop_q ψ hψ
  have hcop_Nd : Nat.Coprime ψ.N d := by
    have hlt : ψ.N < d := by
      have h1 : (ψ.N : ℝ) < (d : ℝ) := by
        have hle := Finset.le_sup (f := PChar.N) hψ
        have hN_lt : (ψ.N : ℝ) < (N_max : ℝ) := by dsimp only [N_max]; exact_mod_cast (by omega : ψ.N < Ψ.sup PChar.N + 2)
        exact (hN_lt.trans (hN_lt_X1.trans_le hX1_le_X2)).trans hd_gt_X2
      exact_mod_cast h1
    exact Stage2PrimePairs.coprime_of_prime_gt (NeZero.pos ψ.N) hd_pr hlt
  refine ⟨hWin, hψ_lt_q, hcop_Nq, hcop_Nd, hcop_qd, fun ij hij => ?_⟩
  have hψN_le : (ψ.N : ℝ) ≤ (N_max : ℝ) := by
    have := Finset.le_sup (f := PChar.N) hψ
    dsimp only [N_max]; exact_mod_cast (by omega : ψ.N ≤ Ψ.sup PChar.N + 2)
  rcases ij with ⟨i, j⟩
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · -- `(0, 1)`: `twistedChar ψ.χ χ_d`
    set η := Stage11SecondMomentFrame.twistedChar ψ.χ (quadCharOfPrime d hd_pr)
    have hη_ne1 : η ≠ 1 := fun h1 => by
      have hpr := twistedChar_isPrimitive hcop_Nd ψ.prim (quadCharOfPrime_isPrimitive_of_mod_four hd_pr hd4)
      have hcond : η.conductor = ψ.N * d := hpr
      rw [h1, DirichletCharacter.conductor_one] at hcond
      have hd2 := hd_pr.two_le; have hN1 := NeZero.pos ψ.N; nlinarith only [hd2, hN1, hcond]
    have hnot_ms : ∀ y ∈ Set.Icc Y (Y ^ K), ‖Sz η y Z‖ ≤ y ^ ((1 : ℝ) / 2 + τ) / 2 := by
      by_contra h
      apply hd_notBad2
      exact Finset.mem_biUnion.mpr ⟨⟨ψ, hψ⟩, Finset.mem_attach _ _,
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hd_P2, hd_pr, h⟩))⟩
    have hzf : ZeroFreeBoxDelta δ₀ Q₂ η := by
      by_contra h
      apply hd_notBad2
      exact Finset.mem_biUnion.mpr ⟨⟨ψ, hψ⟩, Finset.mem_attach _ _,
        Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hd_P2, hd_pr, h⟩))⟩
    have hN_leQ : ((ψ.N * d : ℕ) : ℝ) ≤ Q₂ := by
      have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq_pr.pos
      have h2NX : 0 ≤ 2 * (N_max : ℝ) * X₂ := by positivity
      calc ((ψ.N * d : ℕ) : ℝ) = (ψ.N : ℝ) * (d : ℝ) := by push_cast; rfl
        _ ≤ (N_max : ℝ) * (2 * X₂) := mul_le_mul hψN_le hd_le_2X2 (Nat.cast_nonneg _) hNmax_pos.le
        _ ≤ 2 * (N_max : ℝ) * (q : ℝ) * X₂ := by nlinarith only [hq1, h2NX]
    have hbox := hboxOfS Y hY_box Q₂ (ψ.N * d) η hN_leQ hη_ne1 hQ2_lo hQ2_hi hzf hnot_ms
    exact ⟨⟨Q₂, hN_leQ, hQ2_lo, hzf⟩, hbox.2, hbox.1⟩
  · -- `(1, 0)`: `twistedChar ψ.χ χ_q`
    set η := Stage11SecondMomentFrame.twistedChar ψ.χ (quadCharOfPrime q hq_pr)
    have hη_ne1 : η ≠ 1 := fun h1 => by
      have hpr := twistedChar_isPrimitive hcop_Nq ψ.prim (quadCharOfPrime_isPrimitive_of_mod_four hq_pr hq4)
      have hcond : η.conductor = ψ.N * q := hpr
      rw [h1, DirichletCharacter.conductor_one] at hcond
      have hq2 := hq_pr.two_le; have hN1 := NeZero.pos ψ.N; nlinarith only [hq2, hN1, hcond]
    have hnot_ms : ∀ y ∈ Set.Icc Y (Y ^ K), ‖Sz η y Z‖ ≤ y ^ ((1 : ℝ) / 2 + τ) / 2 := by
      by_contra h
      apply hq_notBad1
      exact Finset.mem_biUnion.mpr ⟨ψ, hψ, Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hq_P1, hq_pr, h⟩)⟩
    have hzf : ZeroFreeBoxDelta δ₀ Q₁ η := by
      by_contra h
      apply hq_notBad1
      exact Finset.mem_biUnion.mpr ⟨ψ, hψ, Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hq_P1, hq_pr, h⟩)⟩
    have hN_leQ : ((ψ.N * q : ℕ) : ℝ) ≤ Q₁ := by
      calc ((ψ.N * q : ℕ) : ℝ) = (ψ.N : ℝ) * (q : ℝ) := by push_cast; rfl
        _ ≤ (N_max : ℝ) * (2 * X₁) := mul_le_mul hψN_le hq_le_2X1 (Nat.cast_nonneg _) hNmax_pos.le
        _ = Q₁ := by dsimp only [Q₁]; ring
    have hbox := hboxOfS Y hY_box Q₁ (ψ.N * q) η hN_leQ hη_ne1 hQ1_lo hQ1_hi hzf hnot_ms
    exact ⟨⟨Q₁, hN_leQ, hQ1_lo, hzf⟩, hbox.2, hbox.1⟩
  · -- `(1, 1)`: `twistedChar (twistedChar ψ.χ χ_q) χ_d`
    set η := Stage11SecondMomentFrame.twistedChar (psiQ ⟨ψ, hψ⟩).χ (quadCharOfPrime d hd_pr)
    have hη_ne1 : η ≠ 1 := fun h1 => by
      have hpr := twistedChar_isPrimitive (hcop_Nd.mul_left hcop_qd) (psiQ ⟨ψ, hψ⟩).prim
        (quadCharOfPrime_isPrimitive_of_mod_four hd_pr hd4)
      have hcond : η.conductor = (ψ.N * q) * d := hpr
      rw [h1, DirichletCharacter.conductor_one] at hcond
      have hd2 := hd_pr.two_le; have hq1 := hq_pr.pos; have hN1 := NeZero.pos ψ.N
      have hNq1 : 1 ≤ ψ.N * q := Nat.mul_pos hN1 hq1
      nlinarith only [hd2, hNq1, hcond]
    have hnot_ms : ∀ y ∈ Set.Icc Y (Y ^ K), ‖Sz η y Z‖ ≤ y ^ ((1 : ℝ) / 2 + τ) / 2 := by
      by_contra h
      apply hd_notBad2
      exact Finset.mem_biUnion.mpr ⟨⟨ψ, hψ⟩, Finset.mem_attach _ _,
        Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hd_P2, hd_pr, h⟩))⟩
    have hzf : ZeroFreeBoxDelta δ₀ Q₂ η := by
      by_contra h
      apply hd_notBad2
      exact Finset.mem_biUnion.mpr ⟨⟨ψ, hψ⟩, Finset.mem_attach _ _,
        Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hd_P2, hd_pr, h⟩))⟩
    have hN_leQ : (((ψ.N * q) * d : ℕ) : ℝ) ≤ Q₂ := by
      calc (((ψ.N * q) * d : ℕ) : ℝ) = (ψ.N : ℝ) * (q : ℝ) * (d : ℝ) := by push_cast; rfl
        _ ≤ (N_max : ℝ) * (q : ℝ) * (2 * X₂) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hψN_le (Nat.cast_nonneg _)) hd_le_2X2 (Nat.cast_nonneg _) (by positivity)
        _ = Q₂ := by dsimp only [Q₂]; ring
    have hbox := hboxOfS Y hY_box Q₂ ((ψ.N * q) * d) η hN_leQ hη_ne1 hQ2_lo hQ2_hi hzf hnot_ms
    exact ⟨⟨Q₂, hN_leQ, hQ2_lo, hzf⟩, hbox.2, hbox.1⟩

/-- **UNCONDITIONAL SINGLE-CHARACTER `PairGood` EXISTENCE (`pairGood_exists_unconditional`)**:
specialization of `pairGood_family_exists_unconditional` to any single primitive `ψ : PChar`! -/
theorem pairGood_exists_unconditional :
    ∃ δ₀ C_L : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 400 ∧ 0 < C_L ∧
      ∀ (ψ : PChar) (ε τ K : ℝ), 0 < ε → ε ≤ 1 / 4 → 0 < τ → 1 ≤ K →
        ∃ Y₀ : ℝ, 16 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
          ∃ q d : ℕ, PairGood ψ δ₀ C_L ε τ K Y q d := by
  obtain ⟨δ₀, C_L, hδ₀_pos, hδ₀_400, hCL_pos, hfam⟩ := pairGood_family_exists_unconditional
  refine ⟨δ₀, C_L, hδ₀_pos, hδ₀_400, hCL_pos, fun ψ ε τ K hε0 hε4 hτ0 hK1 => ?_⟩
  obtain ⟨Y₀, hY₀16, hY₀⟩ := hfam {ψ} ε τ K hε0 hε4 hτ0 hK1
  refine ⟨Y₀, hY₀16, fun Y hY => ?_⟩
  obtain ⟨q, d, _, hpg⟩ := hY₀ Y hY
  exact ⟨q, d, hpg ψ (Finset.mem_singleton_self ψ)⟩

/-- **`PairGood` Discharges `SigALe` & `CoreGm` (`pairGood_discharges_sigA_le`)**:
for any coset frame `φ` and arithmetic data `D` whose off-diagonal character twists `GPsi D ell ψ x`
for `ψ ∈ PsiA φ.A0 \ Kp` are realized by `Gchi` of `PairGood` twists over `(q, d)`, the unconditional
`PairGood` bound immediately discharges `SigA D ell φ.A0 Kp x ≤ 4 * L.o * x ^ (1/2 + eps)` (via `sigA_le`)! -/
theorem pairGood_discharges_sigA_le (L : Level) (φ : CosetFrame) (ho : φ.o = L.o)
    (D : ArithData φ.A) (ell : AddChar (E0 × φ.A) ℂ → ℂ)
    (Kp : Finset (AddChar (E0 × φ.A) ℂ)) {δ₀ C_L eps τ K Y x : ℝ}
    {q d : ℕ} (base_of : AddChar (E0 × φ.A) ℂ → PChar) (idx_of : AddChar (E0 × φ.A) ℂ → Fin 2 × Fin 2)
    (hPG : ∀ ψ ∈ PsiA φ.A0 \ Kp, PairGood (base_of ψ) δ₀ C_L eps τ K Y q d)
    (hidx_ne : ∀ ψ ∈ PsiA φ.A0 \ Kp, idx_of ψ ≠ (0, 0))
    (hx_win : x ∈ Set.Icc Y (Y ^ K)) (hτ_le : τ ≤ eps) (hY1 : 1 ≤ Y)
    (hmatch : ∀ ψ (hψ : ψ ∈ PsiA φ.A0 \ Kp),
      haveI : NeZero q := ⟨(hPG ψ hψ).win.q_prime.ne_zero⟩
      haveI : NeZero d := ⟨(hPG ψ hψ).win.d_prime.ne_zero⟩
      ‖GPsi D ell ψ x‖ =
        ‖Gchi (pairTwist (base_of ψ) q d (hPG ψ hψ).win.q_prime (by have := (hPG ψ hψ).win.q_mod; omega)
          (hPG ψ hψ).win.d_prime (by have := (hPG ψ hψ).win.d_mod; omega)
          (hPG ψ hψ).cop_Nq (hPG ψ hψ).cop_Nd (hPG ψ hψ).cop_qd (idx_of ψ)).χ x‖) :
    SigA D ell φ.A0 Kp x ≤ 4 * (L.o : ℝ) * x ^ ((1 : ℝ) / 2 + eps) := by
  refine sigA_le L φ ho D ell Kp (by linarith [hx_win.1]) fun ψ hψ => ?_
  have hpg := hPG ψ hψ
  have : NeZero q := ⟨hpg.win.q_prime.ne_zero⟩
  have : NeZero d := ⟨hpg.win.d_prime.ne_zero⟩
  have hbd := (hpg.offDiag_good (idx_of ψ) (hidx_ne ψ hψ)).2.2 x hx_win
  rw [hmatch ψ hψ]
  exact hbd.trans (Real.rpow_le_rpow_of_exponent_le (hY1.trans hx_win.1) (by linarith))

/-- **STAGE 12 (6 OF 9) MASTER CERTIFICATION (`stage12_chBalanceCore_master`, `0` ASSUMPTIONS!)**:
Bundles all three unconditional Stage 12 deliverables:
1. Exact Galois Fourier Inversion (`ch_balance`: `ASK - MAIN = De`, `0` assumptions!),
2. Unconditional `ZeroFreeBox` + `BoxOfS` + Multiplicative Large Sieve + `MSqMain` Sobolev `BadShare`,
3. Unconditional `PairGood` prime-pair existence for arbitrary finite character families `Ψ : Finset PChar`. -/
theorem stage12_chBalanceCore_master :
    -- (1) Exact Galois Fourier Inversion (`ch_balance`, `0` assumptions)
    (∀ {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
      (D : ArithData H) (S0 : Finset ℕ) (_hD : HostFactsS D S0)
      (ell : AddChar (E0 × H) ℂ → ℂ) (a : ℝ) (t : H) (w : E0 × H → ℝ)
      (_ha : 0 < a) (_hw : ∀ ρ, InPhi ρ → 0 < w ρ)
      (N : ℕ) (_hN : ∀ ρ, InPhi ρ → a / w ρ ≤ N),
      (ASK D N a t w : ℂ) - MAIN ell a w = De D ell a t w) ∧
    -- (2) Unconditional `ZeroDensityBox` + `MSqMain` + `PairGood` prime-pair family existence
    (∃ δ₀ C_L : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 400 ∧ 0 < C_L ∧
      ∀ (Ψ : Finset PChar) (ε τ K : ℝ), 0 < ε → ε ≤ 1 / 4 → 0 < τ → 1 ≤ K →
        ∃ Y₀ : ℝ, 16 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y →
          ∃ q d : ℕ, WinPair ε Y q d ∧ ∀ ψ ∈ Ψ, PairGood ψ δ₀ C_L ε τ K Y q d) :=
  ⟨fun D S0 hD ell a t w ha hw N hN => ch_balance D S0 hD ell a t w ha hw N hN,
    pairGood_family_exists_unconditional⟩

end RHDirect.Stage12ChBalanceCore
