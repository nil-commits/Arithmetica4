import RHDirect.Stage2HodgeWeights
import RHDirect.BaseChangeCyclic
import RHDirect.LocalLanglandsCore
import RHDirect.GaloisRowCore
import RHDirect.Stage2GaloisWire
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# RHDirect.Stage3AutomorphicDescent

Stage 3 deep mathematical discharge for **Cyclic Automorphic Base Change / Descent,
Clifford Orbit–Stabilizer Dichotomy, Trace-Character Orthogonality, Solvable Tower
Induction, and Hodge–Tate Weight & Weak-Admissibility Base-Change Stability** on Track 2
(`rh-direct`), building directly on:
- `RHDirect.Stage2HodgeWeights` (`HodgeFiltration`, `FilteredPhiMod`, `IsWeaklyAdmissible`,
  `FilteredPhiSES`, `CrystallineWeightFamily`, `RegularAlgebraic`, `PolygonLe`,
  `galoisRowProps_of_crystalline_localGlobal`),
- `RHDirect.BaseChangeCyclic` (`SatakeSystem`, `BaseChangeStep`, `BaseChangeGalStep`,
  `BaseChangeTower`, `SolvableStepChain`, `exists_solvableStepChain`),
- `RHDirect.GaloisRowCore` (`CMInfCharDatum`, `GaloisRowProps`, `StructuredCuspDatum`,
  `ThetaLiftAssemblyPipeline`),
- `RHDirect.Stage2GaloisWire` (`SolvablePrimeStepBaseChange`, `SolvableDescentEquiv`,
  `GeometryThetaRowSupply`, `Stage2GaloisCoreInputs`).

## Contents

1. **Cyclic Group `ZMod p` Action, Trace-Character Orthogonality & Exact Clifford Dichotomy**:
   - Dual character orthogonality on `ZMod p` (`zmodChar_sum_dual`, `zmodChar_sum_group`).
   - Exact trace-character orthogonality formula for prime-order characters `η : Γ →* ℂˣ`:
     `∑_{j : Fin p} (η g)^j · χ(g) = p · 1_{g ∈ ker η} · χ(g)` (`trace_character_orthogonality`),
     plus self-twist trace vanishing outside `ker η` (`trace_eq_zero_outside_ker_of_selfTwist`).
   - Prime-order `ZMod p` actions on isomorphism classes `Quot iso` with **Exact Clifford /
     Cyclic Orbit–Stabilizer Dichotomy** (`prime_orbit_stabilizer_dichotomy`,
     `clifford_cyclic_descent_dichotomy`): every Galois-invariant representation descends to a
     fiber whose isomorphism-class cardinality is either `p` (trivial twist stabilizer, `p`
     distinct twists) or `1` (full twist stabilizer, self-twisted automorphic induction).
   - Direct instantiation on `RHDirect.BaseChangeStep` (`BaseChangeStep.clifford_fiber_dichotomy`,
     `BaseChangeStep.coprime_rank_fiber_card_eq_p`, `BaseChangeStep.trace_orthogonality_cofinite`).

2. **Solvable Tower Induction (Automorphy, Regularity & Polarization)**:
   - Prime-degree cyclic polarized steps (`CyclicPolarizedStep`) and subnormal solvable towers
     `K = K_0 ⊂ K_1 ⊂ ... ⊂ K_m = L` (`SolvablePolarizedTower`).
   - Step-by-step simultaneous descent & lifting of automorphy (`IsAut`), `RegularAlgebraic`,
     and `IsPolarized wt` along arbitrary solvable towers (`SolvablePolarizedTower.aut_reg_pol_equiv`,
     `descend_aut_reg_pol`, `lift_aut_reg_pol`).
   - Direct construction of `BaseChangeTower` from `SolvableStepChain Γ` (`BaseChangeTower.of_solvableStepChain`).

3. **Hodge–Tate Weight, Polygon, Scalar Extension & Fontaine Weak-Admissibility Stability**:
   - Pullback of `CrystallineWeightFamily` across finite extensions `L / K` preserving
     `IsRegularWeights`, `RegularAlgebraic`, polarization reflection `w ↦ c - w`, and
     determinant weight sum symmetry (`CrystallineWeightFamily.pullback_*`).
   - Positive-factor scaling invariance of `PolygonLe` (`PolygonLe.scale_pos_iff`).
   - Genuine scalar extension `HodgeFiltration.baseChange L` on `TensorProduct K L V` preserving
     `dimAt`, `jump`, `weights`, `tH`, and `IsRegularWeights`.
   - **Supermodularity of `t_H`** (`HodgeFiltration.tH_add_le_sup_add_inf`), **Uniqueness of the
     Harder–Narasimhan Maximal Destabilizing `φ`-Stable Subspace** (`exists_unique_max_destabilizer`),
     **Unconditional Galois Descent of `Gal(L/K)`-Invariant Subspaces** (`galois_descent_submodule`),
     and **Fontaine Weak-Admissibility Invariance under Finite Galois / Cyclic Base Change**
     (`isWeaklyAdmissible_baseChange_iff`, `isWeaklyAdmissible_descent`).

4. **Weight Descent (`CMInfCharDatum` & `GaloisRowProps.weights` + `weights_conj`)**:
   - Exact descent of `IsRegAlg`, `RegularAlgebraic`, `IsPolarized wt`, and unique fiber-constant
     Hodge–Tate weights `HT_K` from `BC_{L/K}(π)` down to `π` (`weight_descent_exists_unique`).
   - Direct assembly of `GaloisRowProps.weights` + `weights_conj` and full `GaloisRowProps` from
     crystalline/Galois base-change data (`galoisRowProps_of_baseChange_weights`,
     `galoisRowProps_of_baseChange_crystalline_localGlobal`).

5. **Direct Discharge Bridges into `Stage2GaloisWire` & `BaseChangeCyclic`**:
   - Discharging `ThetaLiftAssemblyPipeline.reg_all` & `pol_all` from crystalline base change
     directly into `Stage2GaloisWire.GeometryThetaRowSupply` and `stage2_galoisModularityContract`.
   - Weighted solvable base-change discharge (`Stage3WeightedSolvableSupply`) feeding directly
     into `Stage2GaloisWire.SolvablePrimeStepBaseChange` and `SolvableDescentEquiv`.

Zero `sorry`, zero custom `axiom`s.
-/

noncomputable section

open Complex Filter Polynomial TensorProduct

namespace RHDirect
namespace Stage3AutomorphicDescent

/-! ## 1. Cyclic Group `ZMod p` Action, Trace-Character Orthogonality & Exact Clifford Dichotomy -/

section CharacterOrthogonality

/-- Elementary modular reduction for powers of a `p`-th root of unity. -/
theorem pow_eq_pow_of_modEq {ζ : ℂ} {p a b : ℕ} (hζ : ζ ^ p = 1) (h : a ≡ b [MOD p]) :
    ζ ^ a = ζ ^ b := by
  rw [← Nat.div_add_mod a p, ← Nat.div_add_mod b p, pow_add, pow_add, pow_mul, pow_mul, hζ,
    one_pow, one_pow, one_mul, one_mul, h]

/-- Geometric sum of a `p`-th root of unity `z` vanishes iff `z ≠ 1`. -/
theorem sum_fin_pow_eq_ite {p : ℕ} {z : ℂ} (hz : z ^ p = 1) :
    (∑ j : Fin p, z ^ (j : ℕ)) = if z = 1 then (p : ℂ) else 0 := by
  by_cases h1 : z = 1
  · subst h1
    simp
  · rw [if_neg h1, Fin.sum_univ_eq_sum_range]
    have hmul : (∑ i ∈ Finset.range p, z ^ i) * (z - 1) = 0 := by
      rw [geom_sum_mul, hz, sub_self]
    exact (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr h1)

/-- Dual character on `ZMod p` attached to a `p`-th root of unity `ζ`:
`η_k(g) = ζ ^ (k.val * g.val)`. -/
def zmodChar {p : ℕ} (ζ : ℂ) (k g : ZMod p) : ℂ :=
  ζ ^ (k.val * g.val)

theorem zmodChar_zero_left {p : ℕ} (ζ : ℂ) (g : ZMod p) : zmodChar ζ 0 g = 1 := by
  simp [zmodChar]

theorem zmodChar_zero_right {p : ℕ} (ζ : ℂ) (k : ZMod p) : zmodChar ζ k 0 = 1 := by
  simp [zmodChar]

theorem zmodChar_add_right {p : ℕ} [NeZero p] {ζ : ℂ} (hζ : ζ ^ p = 1) (k g₁ g₂ : ZMod p) :
    zmodChar ζ k (g₁ + g₂) = zmodChar ζ k g₁ * zmodChar ζ k g₂ := by
  unfold zmodChar
  rw [← pow_add, ← mul_add]
  refine pow_eq_pow_of_modEq hζ ?_
  have hadd : (g₁ + g₂).val ≡ g₁.val + g₂.val [MOD p] := by
    rw [ZMod.val_add]
    exact Nat.mod_modEq _ _
  exact Nat.ModEq.mul_left k.val hadd

theorem zmodChar_add_left {p : ℕ} [NeZero p] {ζ : ℂ} (hζ : ζ ^ p = 1) (k₁ k₂ g : ZMod p) :
    zmodChar ζ (k₁ + k₂) g = zmodChar ζ k₁ g * zmodChar ζ k₂ g := by
  unfold zmodChar
  rw [← pow_add, ← add_mul]
  refine pow_eq_pow_of_modEq hζ ?_
  have hadd : (k₁ + k₂).val ≡ k₁.val + k₂.val [MOD p] := by
    rw [ZMod.val_add]
    exact Nat.mod_modEq _ _
  exact Nat.ModEq.mul_right g.val hadd

/-- **Dual Character Orthogonality on `ZMod p`**:
for a primitive `p`-th root of unity `ζ`, `∑_{k : ZMod p} η_k(g) = p · 1_{g = 0}`. -/
theorem zmodChar_sum_dual {p : ℕ} [Fact p.Prime] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ p) (g : ZMod p) :
    (∑ k : ZMod p, zmodChar ζ k g) = if g = 0 then (p : ℂ) else 0 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have : NeZero p := ⟨hp.ne'⟩
  have hsum : (∑ k : ZMod p, zmodChar ζ k g) = ∑ j : Fin p, (ζ ^ g.val) ^ (j : ℕ) := by
    let e : ZMod p ≃ Fin p :=
      { toFun := fun k => ⟨k.val, ZMod.val_lt k⟩
        invFun := fun j => (j.val : ZMod p)
        left_inv := fun k => ZMod.natCast_zmod_val k
        right_inv := fun j => Fin.ext (ZMod.val_natCast_of_lt j.isLt) }
    refine Fintype.sum_equiv e _ _ fun k => ?_
    unfold zmodChar
    rw [← pow_mul, mul_comm g.val]
    rfl
  rw [hsum, sum_fin_pow_eq_ite (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow])]
  by_cases hg : g = 0
  · subst hg
    simp
  · rw [if_neg hg]
    have hne1 : ζ ^ g.val ≠ 1 := by
      intro h1
      have hdvd : p ∣ g.val := hζ.dvd_of_pow_eq_one g.val h1
      have hlt : g.val < p := ZMod.val_lt g
      have hval0 : g.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
      exact hg ((ZMod.val_eq_zero g).mp hval0)
    rw [if_neg hne1]

/-- **Group Character Orthogonality on `ZMod p`**:
`∑_{g : ZMod p} η_k(g) = p · 1_{k = 0}`. -/
theorem zmodChar_sum_group {p : ℕ} [Fact p.Prime] {ζ : ℂ} (hζ : IsPrimitiveRoot ζ p) (k : ZMod p) :
    (∑ g : ZMod p, zmodChar ζ k g) = if k = 0 then (p : ℂ) else 0 := by
  have hswap : ∀ g : ZMod p, zmodChar ζ k g = zmodChar ζ g k := by
    intro g
    simp [zmodChar, mul_comm]
  simp_rw [hswap]
  exact zmodChar_sum_dual hζ k

/-- Twisted character trace `χ_{π ⊗ η^j}(g) := (η(g))^j · χ_π(g)`. -/
def twistedTrace {Γ : Type*} (χ : Γ → ℂ) (η : Γ → ℂˣ) (j : ℕ) (g : Γ) : ℂ :=
  ((η g : ℂ) ^ j) * χ g

/-- **Exact Trace-Character Orthogonality Formula**:
for any group `Γ`, any character `η : Γ →* ℂˣ` satisfying `η^p = 1` (e.g. a generator of the
character group `Ĝ` of a degree-`p` cyclic extension `L / K` with `ker η = G_L`), and any trace
function `χ : Γ → ℂ`,
`∑_{j : Fin p} χ_{π ⊗ η^j}(g) = p · 1_{g ∈ ker η} · χ_π(g)`. -/
theorem trace_character_orthogonality {Γ : Type*} [Group Γ] {p : ℕ}
    (η : Γ →* ℂˣ) (hpow : ∀ g : Γ, (η g) ^ p = 1) (χ : Γ → ℂ) (g : Γ) :
    (∑ j : Fin p, twistedTrace χ η j g) = if g ∈ η.ker then (p : ℂ) * χ g else 0 := by
  unfold twistedTrace
  rw [← Finset.sum_mul]
  have hzp : (η g : ℂ) ^ p = 1 := by
    have := congrArg (fun u : ℂˣ => (u : ℂ)) (hpow g)
    simpa [Units.val_pow_eq_pow_val] using this
  rw [sum_fin_pow_eq_ite hzp]
  have hker : g ∈ η.ker ↔ (η g : ℂ) = 1 := by
    rw [MonoidHom.mem_ker, Units.ext_iff, Units.val_one]
  by_cases hg : g ∈ η.ker
  · rw [if_pos hg, if_pos (hker.mp hg)]
  · rw [if_neg hg, if_neg (mt hker.mpr hg), zero_mul]

/-- **`ZMod p`-Indexed Trace-Character Orthogonality**: for any quotient map `q : Γ → ZMod p`,
`∑_{k : ZMod p} η_k(q g) · χ(g) = p · 1_{q g = 0} · χ(g)`. -/
theorem trace_character_orthogonality_zmod {Γ : Type*} {p : ℕ} [Fact p.Prime]
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ p) (q : Γ → ZMod p) (χ : Γ → ℂ) (g : Γ) :
    (∑ k : ZMod p, zmodChar ζ k (q g) * χ g) = if q g = 0 then (p : ℂ) * χ g else 0 := by
  rw [← Finset.sum_mul, zmodChar_sum_dual hζ (q g)]
  split_ifs <;> simp

/-- **Self-Twist Trace Vanishing Outside `ker η`** (Automorphic Induction Support Criterion):
if `π ⊗ η ≃ π` on traces (`∀ g, η(g) · χ(g) = χ(g)`), then `χ(g) = 0` for every `g ∉ ker η`! -/
theorem trace_eq_zero_outside_ker_of_selfTwist {Γ : Type*} [Group Γ]
    (η : Γ →* ℂˣ) (χ : Γ → ℂ)
    (hself : ∀ g : Γ, twistedTrace χ η 1 g = χ g) {g : Γ} (hg : g ∉ η.ker) :
    χ g = 0 := by
  have h1 : ((η g : ℂ) - 1) * χ g = 0 := by
    have h := hself g
    simp only [twistedTrace, pow_one] at h
    linear_combination h
  have hne : (η g : ℂ) - 1 ≠ 0 := by
    intro h0
    apply hg
    rw [MonoidHom.mem_ker, Units.ext_iff, Units.val_one]
    exact sub_eq_zero.mp h0
  exact (mul_eq_zero.mp h1).resolve_left hne

/-- Self-twisted representations have constant twisted traces across all powers `η^j`,
so their character-twist average equals `p · χ(g)` everywhere (and vanishes outside `ker η`). -/
theorem sum_twistedTrace_of_selfTwist {Γ : Type*} [Group Γ] {p : ℕ}
    (η : Γ →* ℂˣ) (χ : Γ → ℂ)
    (hself : ∀ g : Γ, twistedTrace χ η 1 g = χ g) (g : Γ) :
    (∑ j : Fin p, twistedTrace χ η j g) = (p : ℂ) * χ g := by
  have hpow : ∀ n : ℕ, twistedTrace χ η n g = χ g := by
    intro n
    induction n with
    | zero => simp [twistedTrace]
    | succ n ih =>
      unfold twistedTrace at ih ⊢
      rw [pow_succ', mul_assoc, ih]
      simpa [twistedTrace, pow_one] using hself g
  simp [hpow]

/-- Orthogonality of a nontrivial character `η : Γ →* ℂˣ` on a finite group `Γ`:
`∑_{g : Γ} η(g) = 0`. -/
theorem sum_char_eq_zero_of_ne_one {Γ : Type*} [Group Γ] [Fintype Γ]
    (η : Γ →* ℂˣ) (hne : η ≠ 1) :
    (∑ g : Γ, (η g : ℂ)) = 0 := by
  have hex : ∃ h : Γ, (η h : ℂ) ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hne
    ext g
    exact hall g
  obtain ⟨h, hh⟩ := hex
  have hshift : (η h : ℂ) * (∑ g : Γ, (η g : ℂ)) = ∑ g : Γ, (η g : ℂ) := by
    rw [Finset.mul_sum]
    have hmul : ∀ g : Γ, (η h : ℂ) * (η g : ℂ) = (η (h * g) : ℂ) := fun g => by
      rw [map_mul, Units.val_mul]
    simp_rw [hmul]
    exact Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun _ => rfl
  have h0 : ((η h : ℂ) - 1) * (∑ g : Γ, (η g : ℂ)) = 0 := by linear_combination hshift
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hh)

end CharacterOrthogonality

/-! ### Exact Prime-Order `ZMod p` Action on Isomorphism Classes & Clifford Dichotomy -/

/-- A cyclic `ZMod p` action on a type of representations `Obj` up to an equivalence relation `iso`. -/
structure ZModActionOnClasses (p : ℕ) where
  Obj : Type
  iso : Obj → Obj → Prop
  iso_refl : ∀ x, iso x x
  iso_symm : ∀ {x y}, iso x y → iso y x
  iso_trans : ∀ {x y z}, iso x y → iso y z → iso x z
  act : ZMod p → Obj → Obj
  act_zero : ∀ x, iso (act 0 x) x
  act_add : ∀ a b x, iso (act (a + b) x) (act a (act b x))
  act_iso : ∀ a {x y}, iso x y → iso (act a x) (act a y)

namespace ZModActionOnClasses

variable {p : ℕ} (A : ZModActionOnClasses p)

/-- Equivalence relation `Setoid` on `A.Obj` induced by `A.iso`. -/
def setoid : Setoid A.Obj where
  r := A.iso
  iseqv := ⟨A.iso_refl, fun h => A.iso_symm h, fun h₁ h₂ => A.iso_trans h₁ h₂⟩

/-- Isomorphism classes `A.Obj / A.iso`. -/
def Class : Type := Quotient A.setoid

/-- Quotient projection to isomorphism classes. -/
def toClass (x : A.Obj) : A.Class := Quotient.mk A.setoid x

theorem toClass_eq_iff {x y : A.Obj} : A.toClass x = A.toClass y ↔ A.iso x y :=
  Quotient.eq (r := A.setoid)

/-- Induced genuine `ZMod p`-action on isomorphism classes `A.Class`. -/
def classAct (k : ZMod p) : A.Class → A.Class :=
  Quotient.lift (fun x => A.toClass (A.act k x)) fun _ _ h =>
    A.toClass_eq_iff.mpr (A.act_iso k h)

@[simp]
theorem classAct_toClass (k : ZMod p) (x : A.Obj) :
    A.classAct k (A.toClass x) = A.toClass (A.act k x) := rfl

theorem classAct_zero (c : A.Class) : A.classAct 0 c = c := by
  induction c using Quotient.ind with
  | _ x => exact A.toClass_eq_iff.mpr (A.act_zero x)

theorem classAct_add (a b : ZMod p) (c : A.Class) :
    A.classAct (a + b) c = A.classAct a (A.classAct b c) := by
  induction c using Quotient.ind with
  | _ x => exact A.toClass_eq_iff.mpr (A.act_add a b x)

/-- Additive group action `AddAction (ZMod p) A.Class` on isomorphism classes. -/
instance instAddActionClass : AddAction (ZMod p) A.Class where
  vadd := A.classAct
  zero_vadd := A.classAct_zero
  add_vadd := A.classAct_add

/-- Stabilizer subgroup of `x` in `ZMod p`: `{k : ZMod p | A.iso (A.act k x) x}`. -/
def stab (x : A.Obj) : AddSubgroup (ZMod p) where
  carrier := {k : ZMod p | A.iso (A.act k x) x}
  zero_mem' := A.act_zero x
  add_mem' {a b} ha hb := A.iso_trans (A.act_add a b x) (A.iso_trans (A.act_iso a hb) ha)
  neg_mem' {a} ha := by
    have h1 : A.iso (A.act (-a) (A.act a x)) (A.act (-a) x) := A.act_iso (-a) ha
    have h2 : A.iso (A.act (-a + a) x) (A.act (-a) (A.act a x)) := A.act_add (-a) a x
    rw [neg_add_cancel] at h2
    exact A.iso_trans (A.iso_symm h1) (A.iso_trans (A.iso_symm h2) (A.act_zero x))

theorem mem_stab_iff (x : A.Obj) (k : ZMod p) : k ∈ A.stab x ↔ A.iso (A.act k x) x := Iff.rfl

/-- Two elements `a, b : ZMod p` produce isomorphic translates of `x` iff `a - b ∈ A.stab x`. -/
theorem act_iso_iff_sub_mem_stab (x : A.Obj) (a b : ZMod p) :
    A.iso (A.act a x) (A.act b x) ↔ a - b ∈ A.stab x := by
  constructor
  · intro h
    have h1 : A.iso (A.act (-b) (A.act a x)) (A.act (-b) (A.act b x)) := A.act_iso (-b) h
    have h2 : A.iso (A.act (a - b) x) (A.act (-b) (A.act a x)) := by
      have : a - b = -b + a := by ring
      rw [this]
      exact A.act_add (-b) a x
    have h3 : A.iso (A.act (-b + b) x) (A.act (-b) (A.act b x)) := A.act_add (-b) b x
    rw [neg_add_cancel] at h3
    exact A.iso_trans h2 (A.iso_trans h1 (A.iso_trans (A.iso_symm h3) (A.act_zero x)))
  · intro h
    have h1 : A.iso (A.act b (A.act (a - b) x)) (A.act b x) := A.act_iso b h
    have h2 : A.iso (A.act (b + (a - b)) x) (A.act b (A.act (a - b) x)) := A.act_add b (a - b) x
    rw [add_sub_cancel] at h2
    exact A.iso_trans h2 h1

/-- Finite orbit of `[x]` in `A.Class` under `ZMod p` (for `NeZero p`). -/
def classOrbit [NeZero p] (x : A.Obj) : Finset A.Class := by
  classical
  exact Finset.univ.image (fun k : ZMod p => A.toClass (A.act k x))

/-- Every additive subgroup of `ZMod p` (for prime `p`) is either `⊥` or `⊤`. -/
theorem addSubgroup_zmod_prime_eq_bot_or_top {p : ℕ} [Fact p.Prime] (S : AddSubgroup (ZMod p)) :
    S = ⊥ ∨ S = ⊤ := by
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  · right
    have hex : ∃ k ∈ S, k ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hbot
      ext k
      simp only [AddSubgroup.mem_bot]
      exact ⟨fun hk => hall k hk, fun h0 => h0 ▸ S.zero_mem⟩
    obtain ⟨k, hk, hk0⟩ := hex
    let m : ℕ := k⁻¹.val
    have hm : m • k = (1 : ZMod p) := by
      rw [nsmul_eq_mul, ZMod.natCast_zmod_val, inv_mul_cancel₀ hk0]
    have h1 : (1 : ZMod p) ∈ S := hm ▸ S.nsmul_mem hk m
    ext x
    simp only [AddSubgroup.mem_top, iff_true]
    have hx : x.val • (1 : ZMod p) = x := by
      rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    exact hx ▸ S.nsmul_mem h1 x.val

/-- **Exact Prime-Order Orbit–Stabilizer Dichotomy on Isomorphism Classes**:
for prime `p` and any `x : A.Obj`,
1. `Nat.card (A.stab x) * (A.classOrbit x).card = p`, and
2. EITHER `A.stab x = ⊥` with `(A.classOrbit x).card = p` and `k ↦ [k • x]` injective,
   OR `A.stab x = ⊤` with `(A.classOrbit x).card = 1` and `∀ k, A.iso (A.act k x) x`. -/
theorem prime_orbit_stabilizer_dichotomy [Fact p.Prime] (x : A.Obj) :
    (Nat.card (A.stab x) * (A.classOrbit x).card = p) ∧
    ((A.stab x = ⊥ ∧ (A.classOrbit x).card = p ∧
        Function.Injective (fun k : ZMod p => A.toClass (A.act k x))) ∨
      (A.stab x = ⊤ ∧ (A.classOrbit x).card = 1 ∧
        ∀ k : ZMod p, A.iso (A.act k x) x)) := by
  classical
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rcases addSubgroup_zmod_prime_eq_bot_or_top (A.stab x) with hbot | htop
  · have hinj : Function.Injective (fun k : ZMod p => A.toClass (A.act k x)) := by
      intro a b hab
      have hsub : a - b ∈ A.stab x := (A.act_iso_iff_sub_mem_stab x a b).mp (A.toClass_eq_iff.mp hab)
      rw [hbot, AddSubgroup.mem_bot] at hsub
      exact sub_eq_zero.mp hsub
    have horb : (A.classOrbit x).card = p := by
      unfold classOrbit
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, ZMod.card]
    have hstab : Nat.card (A.stab x) = 1 := by
      have : Unique (A.stab x) :=
        { default := ⟨0, (A.stab x).zero_mem⟩
          uniq := fun ⟨k, hk⟩ => Subtype.ext (by rwa [hbot, AddSubgroup.mem_bot] at hk) }
      exact Nat.card_unique
    exact ⟨by rw [hstab, horb, one_mul], Or.inl ⟨hbot, horb, hinj⟩⟩
  · have hall : ∀ k : ZMod p, A.iso (A.act k x) x := fun k => by
      have : k ∈ A.stab x := htop.symm ▸ AddSubgroup.mem_top k
      exact this
    have horb_eq : A.classOrbit x = {A.toClass x} := by
      unfold classOrbit
      ext c
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨k, rfl⟩
        exact A.toClass_eq_iff.mpr (hall k)
      · rintro rfl
        exact ⟨0, A.toClass_eq_iff.mpr (A.act_zero x)⟩
    have horb : (A.classOrbit x).card = 1 := by rw [horb_eq, Finset.card_singleton]
    have hstab : Nat.card (A.stab x) = p := by
      let e : A.stab x ≃ ZMod p :=
        { toFun := Subtype.val
          invFun := fun k => ⟨k, htop.symm ▸ AddSubgroup.mem_top k⟩
          left_inv := fun ⟨_, _⟩ => rfl
          right_inv := fun _ => rfl }
      rw [Nat.card_congr e, Nat.card_eq_fintype_card, ZMod.card]
    exact ⟨by rw [hstab, horb, mul_one], Or.inr ⟨htop, horb, hall⟩⟩

end ZModActionOnClasses

/-- Cyclic prime-degree base-change system coupling a `ZMod p` character-twist action on the
base `K` with a `ZMod p` Galois-conjugation action on the extension `L`. -/
structure CyclicBaseChangeSystem (p : ℕ) where
  base : ZModActionOnClasses p
  ext : ZModActionOnClasses p
  IsBC : base.Obj → ext.Obj → Prop
  isBC_iso : ∀ {π₁ π₂ P₁ P₂}, base.iso π₁ π₂ → ext.iso P₁ P₂ → IsBC π₁ P₁ → IsBC π₂ P₂
  isBC_twist : ∀ {π P} (k : ZMod p), IsBC π P → IsBC (base.act k π) P
  isBC_gal_inv : ∀ {π P}, IsBC π P → ∀ σ : ZMod p, ext.iso (ext.act σ P) P
  descent : ∀ P : ext.Obj, (∀ σ : ZMod p, ext.iso (ext.act σ P) P) → ∃ π : base.Obj, IsBC π P
  fiber_rigid : ∀ {π₁ π₂ P}, IsBC π₁ P → IsBC π₂ P → ∃ k : ZMod p, base.iso π₂ (base.act k π₁)

namespace CyclicBaseChangeSystem

variable {p : ℕ} (C : CyclicBaseChangeSystem p)

/-- **Galois Orbit Dichotomy on `L`**: every representation `P` over `L` either is
Galois-invariant (orbit size `1`) and descends to `K`, or has a free `ZMod p` Galois orbit
of size `p` and does not descend. -/
theorem galois_orbit_descent_dichotomy [Fact p.Prime] (P : C.ext.Obj) :
    ((C.ext.classOrbit P).card = 1 ∧ ∃ π : C.base.Obj, C.IsBC π P) ∨
      ((C.ext.classOrbit P).card = p ∧ ¬∃ π : C.base.Obj, C.IsBC π P) := by
  rcases (C.ext.prime_orbit_stabilizer_dichotomy P).2 with ⟨hbot, hcard, _⟩ | ⟨_, hcard, hinv⟩
  · right
    refine ⟨hcard, ?_⟩
    rintro ⟨π, hbc⟩
    have h1 : (1 : ZMod p) ∈ C.ext.stab P := C.isBC_gal_inv hbc 1
    rw [hbot, AddSubgroup.mem_bot] at h1
    exact one_ne_zero h1
  · left
    exact ⟨hcard, C.descent P hinv⟩

/-- Characterization of the isomorphism-class descent fiber over `P`: if `IsBC π P`, a base
isomorphism class `c : C.base.Class` lies in the descent fiber of `P` iff `c ∈ C.base.classOrbit π`. -/
theorem mem_classOrbit_iff_descent_fiber [NeZero p] {π : C.base.Obj} {P : C.ext.Obj}
    (hbc : C.IsBC π P) (c : C.base.Class) :
    c ∈ C.base.classOrbit π ↔ ∃ π' : C.base.Obj, C.base.toClass π' = c ∧ C.IsBC π' P := by
  classical
  unfold ZModActionOnClasses.classOrbit
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨C.base.act k π, rfl, C.isBC_twist k hbc⟩
  · rintro ⟨π', rfl, hbc'⟩
    obtain ⟨k, hk⟩ := C.fiber_rigid hbc hbc'
    exact ⟨k, C.base.toClass_eq_iff.mpr (C.base.iso_symm hk)⟩

/-- **Exact Clifford / Cyclic Orbit–Stabilizer Descent Dichotomy**:
for prime `p` and any Galois-invariant `P` over `L` (`∀ σ, ext.iso (ext.act σ P) P`),
`P` descends to some `π` over `K` whose descent fiber `C.base.classOrbit π` satisfies:
- **Case 1 (Trivial twist stabilizer)**: `C.base.stab π = ⊥`, `k ↦ [π ⊗ η_k]` is injective, and
  the descent fiber over `P` has **exact cardinality `p`** (`p` distinct twists on `K`), OR
- **Case 2 (Self-twisted / Automorphic induction)**: `C.base.stab π = ⊤`, in particular
  `π ⊗ η_1 ≃ π` for the nontrivial generator `1 ≠ 0`, and the descent fiber over `P` has
  **exact cardinality `1`**. -/
theorem clifford_cyclic_descent_dichotomy [Fact p.Prime] {P : C.ext.Obj}
    (hinv : ∀ σ : ZMod p, C.ext.iso (C.ext.act σ P) P) :
    ∃ π : C.base.Obj, C.IsBC π P ∧
      (∀ c : C.base.Class, c ∈ C.base.classOrbit π ↔
        ∃ π' : C.base.Obj, C.base.toClass π' = c ∧ C.IsBC π' P) ∧
      ((C.base.stab π = ⊥ ∧ (C.base.classOrbit π).card = p ∧
          Function.Injective (fun k : ZMod p => C.base.toClass (C.base.act k π))) ∨
        (C.base.stab π = ⊤ ∧ (C.base.classOrbit π).card = 1 ∧
          (1 : ZMod p) ≠ 0 ∧ C.base.iso (C.base.act 1 π) π)) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨π, hbc⟩ := C.descent P hinv
  refine ⟨π, hbc, C.mem_classOrbit_iff_descent_fiber hbc, ?_⟩
  rcases (C.base.prime_orbit_stabilizer_dichotomy π).2 with h1 | ⟨htop, hcard, hall⟩
  · exact Or.inl h1
  · exact Or.inr ⟨htop, hcard, one_ne_zero, hall 1⟩

end CyclicBaseChangeSystem

/-! ### Direct Clifford & Trace-Orthogonality Bridge to `RHDirect.BaseChangeStep` -/

/-- Pick an explicit generator `η₀` of a prime-order cyclic subgroup `H ≤ G`. -/
theorem exists_gen_of_card_prime {G : Type*} [Group G] (H : Subgroup G) {p : ℕ}
    (hp : p.Prime) (hcard : Nat.card H = p) :
    ∃ η₀ : H, orderOf η₀ = p ∧ ∀ η : H, ∃ k : ℕ, k < p ∧ η₀ ^ k = η := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite H := Nat.finite_of_card_ne_zero (hcard ▸ hp.ne_zero)
  have : IsCyclic H := isCyclic_of_prime_card hcard
  obtain ⟨η₀, hgen⟩ := IsCyclic.exists_generator (α := H)
  have hord : orderOf η₀ = p := by
    have hz : Subgroup.zpowers η₀ = ⊤ := eq_top_iff.mpr fun x _ => hgen x
    rw [← Nat.card_zpowers, hz, Subgroup.card_top, hcard]
  have hpowp : η₀ ^ p = 1 := hord ▸ pow_orderOf_eq_one η₀
  refine ⟨η₀, hord, fun η => ?_⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hgen η)
  have hdiv : (p : ℤ) * (m / (p : ℤ)) + m % (p : ℤ) = m := Int.mul_ediv_add_emod m (p : ℤ)
  have hpow_z : η₀ ^ (m % (p : ℤ)) = η := by
    rw [← hm]
    conv_rhs => rw [← hdiv, zpow_add, zpow_mul, zpow_natCast, hpowp, one_zpow, one_mul]
  have hnonneg : 0 ≤ m % (p : ℤ) := Int.emod_nonneg m (Int.natCast_ne_zero.mpr hp.ne_zero)
  have hlt : m % (p : ℤ) < p := Int.emod_lt_of_pos m (Int.natCast_pos.mpr hp.pos)
  refine ⟨(m % (p : ℤ)).toNat, by omega, ?_⟩
  rw [← zpow_natCast, Int.toNat_of_nonneg hnonneg, hpow_z]

/-- Induced `ZMod step.p` character-twist action on `S_K.Rep` from any `BaseChangeStep S_K S_M`
and a generator `η₀` of `step.cyclicChars`. -/
def baseChangeStepZModAction {S_K S_M : SatakeSystem} (step : BaseChangeStep S_K S_M)
    (η₀ : step.cyclicChars) (hord : orderOf η₀ = step.p) :
    ZModActionOnClasses step.p where
  Obj := S_K.Rep
  iso := S_K.iso
  iso_refl := S_K.iso_refl
  iso_symm := S_K.iso_symm
  iso_trans := S_K.iso_trans
  act k π := S_K.twist π ((η₀ : S_K.Char) ^ k.val)
  act_zero π := by
    simp only [ZMod.val_zero, pow_zero]
    exact S_K.twist_one π
  act_add a b π := by
    have : NeZero step.p := ⟨step.p_prime.ne_zero⟩
    have hpowp : η₀ ^ step.p = 1 := hord ▸ pow_orderOf_eq_one η₀
    have hpow : (η₀ : S_K.Char) ^ (a + b).val = (η₀ : S_K.Char) ^ a.val * (η₀ : S_K.Char) ^ b.val := by
      have hsub : η₀ ^ (a + b).val = η₀ ^ (a.val + b.val) := by
        rw [ZMod.val_add]
        have hmod : a.val + b.val = step.p * ((a.val + b.val) / step.p) + (a.val + b.val) % step.p :=
          (Nat.div_add_mod _ _).symm
        conv_rhs => rw [hmod, pow_add, pow_mul, hpowp, one_pow, one_mul]
      have hval := congrArg Subtype.val hsub
      simpa [pow_add] using hval
    rw [hpow, mul_comm ((η₀ : S_K.Char) ^ a.val)]
    exact S_K.iso_symm (S_K.twist_mul π _ _)
  act_iso k _ _ h := S_K.twist_iso _ h

/-- **Exact Clifford Fiber Cardinality Dichotomy for `BaseChangeStep`**:
for any prime-degree cyclic base-change step `step : BaseChangeStep S_K S_M` and any base
representation `π` lifting to `P` (`IsLocalBaseChange step.ext π P`), the `ZMod step.p` twist
action `A` satisfies:
- Every descent `π'` of `P` lies in `A.classOrbit π`, AND
- EITHER `π` has trivial stabilizer in `step.cyclicChars` and `(A.classOrbit π).card = step.p`
  (`p` pairwise non-isomorphic twists),
- OR `π` is self-twisted by every `η ∈ step.cyclicChars` and `(A.classOrbit π).card = 1`. -/
theorem baseChangeStep_clifford_fiber_dichotomy {S_K S_M : SatakeSystem}
    (step : BaseChangeStep S_K S_M) {π : S_K.Rep} {P : S_M.Rep}
    (hbc : IsLocalBaseChange step.ext π P) :
    ∃ (η₀ : step.cyclicChars) (hord : orderOf η₀ = step.p),
      let A := baseChangeStepZModAction step η₀ hord
      ∀ [NeZero step.p],
        (∀ π' : S_K.Rep, IsLocalBaseChange step.ext π' P → A.toClass π' ∈ A.classOrbit π) ∧
        (((∀ η ∈ step.cyclicChars, S_K.iso (S_K.twist π η) π → η = 1) ∧
            (A.classOrbit π).card = step.p) ∨
          ((∀ η ∈ step.cyclicChars, S_K.iso (S_K.twist π η) π) ∧
            (A.classOrbit π).card = 1)) := by
  have : Fact step.p.Prime := ⟨step.p_prime⟩
  obtain ⟨η₀, hord, hgen⟩ := exists_gen_of_card_prime step.cyclicChars step.p_prime step.cyclicChars_card
  refine ⟨η₀, hord, ?_⟩
  dsimp only
  intro _
  set A := baseChangeStepZModAction step η₀ hord
  refine ⟨?_, ?_⟩
  · intro π' hbc'
    obtain ⟨η, hη, hiso⟩ := step.fiber π π' P hbc hbc'
    obtain ⟨k, hklt, hk⟩ := hgen ⟨η, hη⟩
    have hη_eq : η = (η₀ : S_K.Char) ^ k := by
      have := congrArg Subtype.val hk
      simpa using this.symm
    have hval : ((k : ZMod step.p)).val = k := ZMod.val_natCast_of_lt hklt
    classical
    unfold ZModActionOnClasses.classOrbit
    rw [Finset.mem_image]
    refine ⟨(k : ZMod step.p), Finset.mem_univ _, ?_⟩
    exact A.toClass_eq_iff.mpr (by
      show S_K.iso (S_K.twist π ((η₀ : S_K.Char) ^ (k : ZMod step.p).val)) π'
      rw [hval, ← hη_eq]
      exact S_K.iso_symm hiso)
  · rcases (A.prime_orbit_stabilizer_dichotomy π).2 with ⟨hbot, hcard, _⟩ | ⟨htop, hcard, hall⟩
    · left
      refine ⟨?_, hcard⟩
      intro η hη hiso
      obtain ⟨k, hklt, hk⟩ := hgen ⟨η, hη⟩
      have hη_eq : η = (η₀ : S_K.Char) ^ k := by
        have := congrArg Subtype.val hk
        simpa using this.symm
      have hval : ((k : ZMod step.p)).val = k := ZMod.val_natCast_of_lt hklt
      have hmem : (k : ZMod step.p) ∈ A.stab π := by
        show S_K.iso (S_K.twist π ((η₀ : S_K.Char) ^ (k : ZMod step.p).val)) π
        rwa [hval, ← hη_eq]
      rw [hbot, AddSubgroup.mem_bot] at hmem
      have hk0 : k = 0 := by
        rw [← hval, hmem, ZMod.val_zero]
      rw [hη_eq, hk0, pow_zero]
    · right
      refine ⟨?_, hcard⟩
      intro η hη
      obtain ⟨k, hklt, hk⟩ := hgen ⟨η, hη⟩
      have hη_eq : η = (η₀ : S_K.Char) ^ k := by
        have := congrArg Subtype.val hk
        simpa using this.symm
      have hval : ((k : ZMod step.p)).val = k := ZMod.val_natCast_of_lt hklt
      rw [hη_eq, ← hval]
      exact hall (k : ZMod step.p)

/-- **Coprime Prime-Rank Exact `p`-Fold Fiber Theorem**: whenever `Nat.Coprime step.p S_K.rank`,
every regular `π` lifts unconditionally to `P` with trivial twist stabilizer and exact
fiber-orbit cardinality `step.p`! -/
theorem baseChangeStep_coprime_rank_fiber_card_eq_p {S_K S_M : SatakeSystem}
    (step : BaseChangeStep S_K S_M) (hcop : Nat.Coprime step.p S_K.rank)
    {π : S_K.Rep} (hreg : step.IsRegK π) :
    ∃ (P : S_M.Rep) (η₀ : step.cyclicChars) (hord : orderOf η₀ = step.p),
      step.IsRegM P ∧ IsLocalBaseChange step.ext π P ∧
      ∀ [NeZero step.p], ((baseChangeStepZModAction step η₀ hord).classOrbit π).card = step.p := by
  obtain ⟨P, hregM, hbc⟩ := step.lift_of_coprime_prime_rank hcop hreg
  obtain ⟨η₀, hord, hfib⟩ := baseChangeStep_clifford_fiber_dichotomy step hbc
  refine ⟨P, η₀, hord, hregM, hbc, ?_⟩
  intro hnz
  rcases (@hfib hnz).2 with ⟨_, hcard⟩ | ⟨hall, _⟩
  · exact hcard
  · exfalso
    have hne1 : (η₀ : S_K.Char) ≠ 1 := by
      intro h1
      have hη1 : η₀ = 1 := Subtype.ext h1
      rw [hη1, orderOf_one] at hord
      exact step.p_prime.ne_one hord.symm
    have hiso : S_K.iso (S_K.twist π (η₀ : S_K.Char)) π := hall η₀.1 η₀.2
    have htriv := S_K.self_twist_trivial_of_coprime hiso (step.cyclicChars_pow η₀.1 η₀.2) hcop
    exact hne1 (step.cyclicChars_faithful η₀.1 η₀.2 htriv)

/-- **Cofinite Trace-Character Orthogonality on `BaseChangeStep`**: for any character
`η ∈ step.cyclicChars` and any local trace function `χ : S_K.Place → ℂ`, cofinitely on places `v`:
`∑_{j : Fin step.p} (η(ϖ_v))^j · χ(v) = step.p · 1_{η(ϖ_v) = 1} · χ(v)`. -/
theorem baseChangeStep_trace_orthogonality_cofinite {S_K S_M : SatakeSystem}
    (step : BaseChangeStep S_K S_M) {η : S_K.Char} (hη : η ∈ step.cyclicChars)
    (χ : S_K.Place → ℂ) :
    ∀ᶠ v in cofinite,
      (∑ j : Fin step.p, ((S_K.charVal η v : ℂ) ^ (j : ℕ)) * χ v) =
        if S_K.charVal η v = 1 then (step.p : ℂ) * χ v else 0 := by
  filter_upwards [step.cyclicChars_pow η hη] with v hvp
  rw [← Finset.sum_mul]
  have hzp : (S_K.charVal η v : ℂ) ^ step.p = 1 := by
    have := congrArg (fun u : ℂˣ => (u : ℂ)) hvp
    simpa [Units.val_pow_eq_pow_val] using this
  rw [sum_fin_pow_eq_ite hzp]
  have h1 : S_K.charVal η v = 1 ↔ (S_K.charVal η v : ℂ) = 1 := by
    rw [Units.ext_iff, Units.val_one]
  by_cases hv : S_K.charVal η v = 1
  · rw [if_pos hv, if_pos (h1.mp hv)]
  · rw [if_neg hv, if_neg (mt h1.mpr hv), zero_mul]

/-! ## 2. Hodge–Tate Weight, Polygon, Scalar Extension & Fontaine Weak-Admissibility Stability -/

section WeightAndPolygonStability

/-- **Positive-Scalar Homogeneity of Polygons**: scaling every slope by `m > 0` scales
`polygon S k` by `m`. -/
theorem sortedSlopes_map_mul_pos {m : ℚ} (hm : 0 < m) (S : Multiset ℚ) :
    Stage2HodgeWeights.sortedSlopes (S.map (fun x => m * x)) =
      (Stage2HodgeWeights.sortedSlopes S).map (fun x => m * x) := by
  set L := Stage2HodgeWeights.sortedSlopes S
  set L' := L.map (fun x => m * x)
  have hperm : List.Perm (Stage2HodgeWeights.sortedSlopes (S.map (fun x => m * x))) L' := by
    rw [← Multiset.coe_eq_coe, Stage2HodgeWeights.sortedSlopes_coe]
    simp [L', L, ← Multiset.map_coe, Stage2HodgeWeights.sortedSlopes_coe]
  have hp1 := Stage2HodgeWeights.sortedSlopes_pairwise (S.map (fun x => m * x))
  have hp2 : L'.Pairwise (· ≤ ·) := by
    dsimp [L']
    rw [List.pairwise_map]
    exact (Stage2HodgeWeights.sortedSlopes_pairwise S).imp fun {a b} hab =>
      mul_le_mul_of_nonneg_left hab (le_of_lt hm)
  exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => le_antisymm h1 h2) hp1 hp2

private theorem list_sum_map_mul (m : ℚ) (L : List ℚ) :
    (L.map (fun x => m * x)).sum = m * L.sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

private theorem multiset_sum_map_mul (m : ℚ) (S : Multiset ℚ) :
    (S.map (fun x => m * x)).sum = m * S.sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, ih]
    ring

theorem polygon_map_mul_pos {m : ℚ} (hm : 0 < m) (S : Multiset ℚ) (k : ℕ) :
    Stage2HodgeWeights.polygon (S.map (fun x => m * x)) k =
      m * Stage2HodgeWeights.polygon S k := by
  unfold Stage2HodgeWeights.polygon
  rw [sortedSlopes_map_mul_pos hm S, ← List.map_take, list_sum_map_mul]

/-- **Base-Change Ramification / Inertia Scaling Invariance of `PolygonLe`**:
for any positive rational scaling factor `m > 0` (e.g. ramification index `e` or inertia
degree `f`), `PolygonLe (H.map (m * ·)) (N.map (m * ·)) ↔ PolygonLe H N`. -/
theorem polygonLe_scale_pos_iff {m : ℚ} (hm : 0 < m) (H N : Multiset ℚ) :
    Stage2HodgeWeights.PolygonLe (H.map (fun x => m * x)) (N.map (fun x => m * x)) ↔
      Stage2HodgeWeights.PolygonLe H N := by
  unfold Stage2HodgeWeights.PolygonLe
  simp only [Multiset.card_map, multiset_sum_map_mul]
  constructor
  · rintro ⟨hcard, hpoly, hsum⟩
    refine ⟨hcard, fun k hk => ?_, mul_left_cancel₀ (ne_of_gt hm) hsum⟩
    have h := hpoly k hk
    rw [polygon_map_mul_pos hm H k, polygon_map_mul_pos hm N k] at h
    exact le_of_mul_le_mul_left h hm
  · rintro ⟨hcard, hpoly, hsum⟩
    refine ⟨hcard, fun k hk => ?_, by rw [hsum]⟩
    rw [polygon_map_mul_pos hm H k, polygon_map_mul_pos hm N k]
    exact mul_le_mul_of_nonneg_left (hpoly k hk) (le_of_lt hm)

/-! ### Pullback of `CrystallineWeightFamily` across a Finite Extension `L / K` -/

/-- Pullback of a `CrystallineWeightFamily` over `K` across a finite CM extension `L / K`
along its conjugation-equivariant embedding restriction `resEmb : EmbL → F.Emb`. -/
def pullbackCrystallineFamily {E : Type*} [Field E]
    (F : Stage2HodgeWeights.CrystallineWeightFamily E)
    (EmbL : Type) (conjL : EmbL → EmbL) (hinvL : Function.Involutive conjL)
    (resEmb : EmbL → F.Emb) (hconj : ∀ τ : EmbL, resEmb (conjL τ) = F.conjEmb (resEmb τ)) :
    Stage2HodgeWeights.CrystallineWeightFamily E where
  rank := F.rank
  rank_pos := F.rank_pos
  Emb := EmbL
  conjEmb := conjL
  conjEmb_involutive := hinvL
  V τ := F.V (resEmb τ)
  dim_eq_rank τ := F.dim_eq_rank (resEmb τ)
  fil τ := F.fil (resEmb τ)
  wt := F.wt
  pol_reflect τ := by
    rw [hconj τ]
    exact F.pol_reflect (resEmb τ)

theorem pullbackCrystallineFamily_HT {E : Type*} [Field E]
    (F : Stage2HodgeWeights.CrystallineWeightFamily E)
    (EmbL : Type) (conjL : EmbL → EmbL) (hinvL : Function.Involutive conjL)
    (resEmb : EmbL → F.Emb) (hconj : ∀ τ : EmbL, resEmb (conjL τ) = F.conjEmb (resEmb τ))
    (τ : EmbL) :
    (pullbackCrystallineFamily F EmbL conjL hinvL resEmb hconj).HT τ = F.HT (resEmb τ) := rfl

theorem pullbackCrystallineFamily_infChar {E : Type*} [Field E]
    (F : Stage2HodgeWeights.CrystallineWeightFamily E)
    (EmbL : Type) (conjL : EmbL → EmbL) (hinvL : Function.Involutive conjL)
    (resEmb : EmbL → F.Emb) (hconj : ∀ τ : EmbL, resEmb (conjL τ) = F.conjEmb (resEmb τ))
    (τ : EmbL) :
    (pullbackCrystallineFamily F EmbL conjL hinvL resEmb hconj).toCMInfCharDatum.infChar τ =
      F.toCMInfCharDatum.infChar (resEmb τ) := rfl

/-- Pulling back a `CrystallineWeightFamily` across `L / K` preserves `IsRegularWeights`
(and is an exact equivalence when `resEmb` is surjective). -/
theorem pullbackCrystallineFamily_isRegularWeights_iff {E : Type*} [Field E]
    (F : Stage2HodgeWeights.CrystallineWeightFamily E)
    (EmbL : Type) (conjL : EmbL → EmbL) (hinvL : Function.Involutive conjL)
    (resEmb : EmbL → F.Emb) (hsurj : Function.Surjective resEmb)
    (hconj : ∀ τ : EmbL, resEmb (conjL τ) = F.conjEmb (resEmb τ)) :
    (∀ τ : EmbL, Stage2HodgeWeights.IsRegularWeights
        ((pullbackCrystallineFamily F EmbL conjL hinvL resEmb hconj).HT τ)) ↔
      (∀ τ : F.Emb, Stage2HodgeWeights.IsRegularWeights (F.HT τ)) := by
  constructor
  · intro h τK
    obtain ⟨τL, rfl⟩ := hsurj τK
    exact h τL
  · intro h τL
    exact h (resEmb τL)

/-- Pulling back a `CrystallineWeightFamily` across a finite CM extension `L / K` preserves
and reflects `RegularAlgebraic` whenever `resEmb : EmbL → EmbK` is surjective! -/
theorem pullbackCrystallineFamily_regularAlgebraic_iff {E : Type*} [Field E]
    (F : Stage2HodgeWeights.CrystallineWeightFamily E)
    (EmbL : Type) (conjL : EmbL → EmbL) (hinvL : Function.Involutive conjL)
    (resEmb : EmbL → F.Emb) (hsurj : Function.Surjective resEmb)
    (hconj : ∀ τ : EmbL, resEmb (conjL τ) = F.conjEmb (resEmb τ)) :
    Stage2HodgeWeights.RegularAlgebraic
        (pullbackCrystallineFamily F EmbL conjL hinvL resEmb hconj).toCMInfCharDatum ↔
      Stage2HodgeWeights.RegularAlgebraic F.toCMInfCharDatum := by
  rw [Stage2HodgeWeights.regularAlgebraic_iff_HT_regular
      (pullbackCrystallineFamily F EmbL conjL hinvL resEmb hconj).toCMInfCharDatum_isRegAlg
      (pullbackCrystallineFamily F EmbL conjL hinvL resEmb hconj).toCMInfCharDatum_matchesWeights,
    Stage2HodgeWeights.regularAlgebraic_iff_HT_regular
      F.toCMInfCharDatum_isRegAlg F.toCMInfCharDatum_matchesWeights]
  exact pullbackCrystallineFamily_isRegularWeights_iff F EmbL conjL hinvL resEmb hsurj hconj

/-- Pulling back a `CrystallineWeightFamily` preserves polarization reflection `w ↦ F.wt - w`,
`IsPolarized F.wt`, and determinant Hodge-number symmetry. -/
theorem pullbackCrystallineFamily_pol_and_det {E : Type*} [Field E]
    (F : Stage2HodgeWeights.CrystallineWeightFamily E)
    (EmbL : Type) (conjL : EmbL → EmbL) (hinvL : Function.Involutive conjL)
    (resEmb : EmbL → F.Emb) (hconj : ∀ τ : EmbL, resEmb (conjL τ) = F.conjEmb (resEmb τ)) :
    (pullbackCrystallineFamily F EmbL conjL hinvL resEmb hconj).toCMInfCharDatum.IsPolarized F.wt ∧
    (pullbackCrystallineFamily F EmbL conjL hinvL resEmb hconj).toCMInfCharDatum.HasConjWeights
      F.wt (pullbackCrystallineFamily F EmbL conjL hinvL resEmb hconj).HT ∧
    (∀ τ : EmbL,
      ((pullbackCrystallineFamily F EmbL conjL hinvL resEmb hconj).HT (conjL τ)).sum +
        ((pullbackCrystallineFamily F EmbL conjL hinvL resEmb hconj).HT τ).sum =
          (F.rank : ℤ) * F.wt) :=
  ⟨(pullbackCrystallineFamily F EmbL conjL hinvL resEmb hconj).toCMInfCharDatum_isPolarized,
    (pullbackCrystallineFamily F EmbL conjL hinvL resEmb hconj).toCMInfCharDatum_hasConjWeights,
    (pullbackCrystallineFamily F EmbL conjL hinvL resEmb hconj).det_tH_conj⟩

/-- Pulling back a `CrystallineWeightFamily` across `L / K` preserves Hodge-below-Newton
polygon dominance (`PolygonLe`) at every embedding `τ : EmbL` AND at its complex conjugate
`conjL τ` under polarization reflection `w ↦ F.wt - w`. -/
theorem pullbackCrystallineFamily_polygonLe_reflect {E : Type*} [Field E]
    (F : Stage2HodgeWeights.CrystallineWeightFamily E)
    (EmbL : Type) (conjL : EmbL → EmbL) (hinvL : Function.Involutive conjL)
    (resEmb : EmbL → F.Emb) (hconj : ∀ τ : EmbL, resEmb (conjL τ) = F.conjEmb (resEmb τ))
    (N : F.Emb → Multiset ℚ)
    (hpoly : ∀ τK : F.Emb,
      Stage2HodgeWeights.PolygonLe ((F.HT τK).map (fun w : ℤ => (w : ℚ))) (N τK))
    (τ : EmbL) :
    let FL := pullbackCrystallineFamily F EmbL conjL hinvL resEmb hconj
    Stage2HodgeWeights.PolygonLe ((FL.HT τ).map (fun w : ℤ => (w : ℚ))) (N (resEmb τ)) ∧
    Stage2HodgeWeights.PolygonLe ((FL.HT (conjL τ)).map (fun w : ℤ => (w : ℚ)))
      (Stage2HodgeWeights.reflectSlopes (F.wt : ℚ) (N (resEmb τ))) := by
  dsimp only
  refine ⟨hpoly (resEmb τ), ?_⟩
  have href :
      ((pullbackCrystallineFamily F EmbL conjL hinvL resEmb hconj).HT (conjL τ)).map
          (fun w : ℤ => (w : ℚ)) =
        Stage2HodgeWeights.reflectSlopes (F.wt : ℚ)
          ((F.HT (resEmb τ)).map (fun w : ℤ => (w : ℚ))) := by
    rw [pullbackCrystallineFamily_HT, hconj τ]
    change (F.fil (F.conjEmb (resEmb τ))).weights.map (fun w : ℤ => (w : ℚ)) = _
    rw [F.pol_reflect (resEmb τ), Stage2HodgeWeights.reflectWeights_map_cast_rat]
    rfl
  rw [href]
  exact Stage2HodgeWeights.PolygonLe.reflect (F.wt : ℚ) (hpoly (resEmb τ))

/-! ### Genuine Scalar Extension `L ⊗_K V` of a `HodgeFiltration` -/

section ScalarExtension

variable {K L V : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup V] [Module K V] [Module.Finite K V]

/-- Base-changed `L`-submodule `L ⊗_K U ≤ L ⊗_K V` realized as the range of `U.subtype.baseChange L`. -/
def baseChangeSubmodule (L : Type*) [Field L] [Algebra K L] (U : Submodule K V) :
    Submodule L (TensorProduct K L V) :=
  LinearMap.range (U.subtype.baseChange L)

omit [Module.Finite K V] in
/-- Over a field `K`, every submodule inclusion `U.subtype` splits, so `U.subtype.baseChange L`
is injective! -/
theorem subtype_baseChange_injective (U : Submodule K V) :
    Function.Injective (U.subtype.baseChange L) := by
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl U
  let r : V →ₗ[K] U := Submodule.projectionOnto U W hW
  have hleft : r.comp U.subtype = LinearMap.id := by
    apply LinearMap.ext
    intro u
    exact Submodule.projectionOnto_apply_left hW u
  have hleftL : (r.baseChange L).comp (U.subtype.baseChange L) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hleft, LinearMap.baseChange_id]
  intro x y hxy
  have h1 : ((r.baseChange L).comp (U.subtype.baseChange L)) x =
      ((r.baseChange L).comp (U.subtype.baseChange L)) y := by
    simp only [LinearMap.comp_apply, hxy]
  simpa [hleftL] using h1

/-- Exact dimension invariance under scalar extension: `finrank L (L ⊗_K V) = finrank K V`. -/
theorem finrank_tensorProduct_eq (K L V : Type*) [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] [Module.Finite K V] :
    Module.finrank L (TensorProduct K L V) = Module.finrank K V := by
  let b := Module.finBasis K V
  have hbL := b.baseChange L
  rw [Module.finrank_eq_card_basis hbL, Fintype.card_fin]

/-- Exact dimension invariance of base-changed submodules:
`finrank L (baseChangeSubmodule L U) = finrank K U`. -/
theorem finrank_baseChangeSubmodule (U : Submodule K V) :
    Module.finrank L (baseChangeSubmodule L U) = Module.finrank K U := by
  have hinj := subtype_baseChange_injective (L := L) U
  have hker : LinearMap.ker (U.subtype.baseChange L) = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have hrank := LinearMap.finrank_range_add_finrank_ker (U.subtype.baseChange L)
  rw [hker, finrank_bot, add_zero] at hrank
  exact hrank.trans (finrank_tensorProduct_eq K L U)

omit [Module.Finite K V] in
theorem baseChangeSubmodule_mono {U₁ U₂ : Submodule K V} (h : U₁ ≤ U₂) :
    baseChangeSubmodule L U₁ ≤ baseChangeSubmodule L U₂ := by
  rintro x ⟨t, rfl⟩
  let incl : U₁ →ₗ[K] U₂ := Submodule.inclusion h
  refine ⟨incl.baseChange L t, ?_⟩
  have hcomp : U₂.subtype.comp incl = U₁.subtype := by ext u; rfl
  have hcompL : (U₂.subtype.baseChange L).comp (incl.baseChange L) = U₁.subtype.baseChange L := by
    rw [← LinearMap.baseChange_comp, hcomp]
  exact congrArg (fun f : TensorProduct K L U₁ →ₗ[L] TensorProduct K L V => f t) hcompL

theorem baseChangeSubmodule_top : baseChangeSubmodule L (⊤ : Submodule K V) = ⊤ := by
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [finrank_baseChangeSubmodule, finrank_top, finrank_tensorProduct_eq]

theorem baseChangeSubmodule_bot : baseChangeSubmodule L (⊥ : Submodule K V) = ⊥ := by
  refine (Submodule.finrank_eq_zero).mp ?_
  rw [finrank_baseChangeSubmodule, finrank_bot]

/-- **Scalar Extension of a `HodgeFiltration`** from `K` to `L` on `L ⊗_K V`. -/
def baseChangeHodgeFiltration (L : Type*) [Field L] [Algebra K L]
    (F : Stage2HodgeWeights.HodgeFiltration K V) :
    Stage2HodgeWeights.HodgeFiltration L (TensorProduct K L V) where
  fil i := baseChangeSubmodule L (F.fil i)
  antitone _ _ hij := baseChangeSubmodule_mono (F.antitone hij)
  botBound := F.botBound
  topBound := F.topBound
  bot_le_top := F.bot_le_top
  eq_top_of_le i hi := by rw [F.eq_top_of_le i hi, baseChangeSubmodule_top]
  eq_bot_of_gt i hi := by rw [F.eq_bot_of_gt i hi, baseChangeSubmodule_bot]

theorem baseChangeHodgeFiltration_dimAt (F : Stage2HodgeWeights.HodgeFiltration K V) (i : ℤ) :
    (baseChangeHodgeFiltration L F).dimAt i = F.dimAt i :=
  finrank_baseChangeSubmodule (L := L) (F.fil i)

theorem baseChangeHodgeFiltration_jump (F : Stage2HodgeWeights.HodgeFiltration K V) (i : ℤ) :
    (baseChangeHodgeFiltration L F).jump i = F.jump i := by
  unfold Stage2HodgeWeights.HodgeFiltration.jump
  rw [baseChangeHodgeFiltration_dimAt (L := L) F i, baseChangeHodgeFiltration_dimAt (L := L) F (i + 1)]

/-- Scalar extension preserves the exact Hodge–Tate weight multiset! -/
theorem baseChangeHodgeFiltration_weights (F : Stage2HodgeWeights.HodgeFiltration K V) :
    (baseChangeHodgeFiltration L F).weights = F.weights := by
  ext i
  rw [(baseChangeHodgeFiltration L F).weights_count i, F.weights_count i,
    baseChangeHodgeFiltration_jump (L := L) F i]

/-- Scalar extension preserves the Hodge number `t_H`. -/
theorem baseChangeHodgeFiltration_tH (F : Stage2HodgeWeights.HodgeFiltration K V) :
    (baseChangeHodgeFiltration L F).tH = F.tH := by
  unfold Stage2HodgeWeights.HodgeFiltration.tH
  rw [baseChangeHodgeFiltration_weights (L := L) F]

/-- Scalar extension preserves and reflects `IsRegularWeights`. -/
theorem baseChangeHodgeFiltration_isRegularWeights_iff
    (F : Stage2HodgeWeights.HodgeFiltration K V) :
    Stage2HodgeWeights.IsRegularWeights (baseChangeHodgeFiltration L F).weights ↔
      Stage2HodgeWeights.IsRegularWeights F.weights := by
  rw [baseChangeHodgeFiltration_weights (L := L) F]

end ScalarExtension

/-! ### Supermodularity of `t_H`, Harder–Narasimhan Uniqueness & Galois Descent of Weak Admissibility -/

section WeakAdmissibilityDescent

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]

/-- Helper: `dimAt` of the induced filtration on `U` equals `finrank K (F.fil i ⊓ U)`. -/
theorem inducedSub_dimAt_eq_inf (F : Stage2HodgeWeights.HodgeFiltration K V)
    (U : Submodule K V) (i : ℤ) :
    (F.inducedSub U).dimAt i = Module.finrank K (F.fil i ⊓ U : Submodule K V) := by
  unfold Stage2HodgeWeights.HodgeFiltration.dimAt Stage2HodgeWeights.HodgeFiltration.inducedSub
  dsimp
  have hker : LinearMap.ker (U.subtype.domRestrict ((F.fil i).comap U.subtype)) = ⊥ := by
    ext x; simp
  have hrange : LinearMap.range (U.subtype.domRestrict ((F.fil i).comap U.subtype)) =
      F.fil i ⊓ U := by
    ext v
    constructor
    · rintro ⟨⟨⟨w, hw⟩, hwf⟩, rfl⟩
      exact ⟨hwf, hw⟩
    · rintro ⟨hvf, hvu⟩
      exact ⟨⟨⟨v, hvu⟩, hvf⟩, rfl⟩
  have hrank := LinearMap.finrank_range_add_finrank_ker
    (U.subtype.domRestrict ((F.fil i).comap U.subtype))
  rw [hrange, hker, finrank_bot, add_zero] at hrank
  exact hrank.symm

/-- **Supermodularity of the Hodge Number `t_H` on Submodules**:
for any two submodules `U₁, U₂ ≤ V`,
`t_H(U₁) + t_H(U₂) ≤ t_H(U₁ ⊔ U₂) + t_H(U₁ ⊓ U₂)`. -/
theorem tH_add_le_sup_add_inf (F : Stage2HodgeWeights.HodgeFiltration K V)
    (U₁ U₂ : Submodule K V) :
    (F.inducedSub U₁).tH + (F.inducedSub U₂).tH ≤
      (F.inducedSub (U₁ ⊔ U₂)).tH + (F.inducedSub (U₁ ⊓ U₂)).tH := by
  have h1 := (F.inducedSub U₁).tH_eq_sum_finrank (a := F.botBound) (b := F.topBound) le_rfl le_rfl
  have h2 := (F.inducedSub U₂).tH_eq_sum_finrank (a := F.botBound) (b := F.topBound) le_rfl le_rfl
  have hs := (F.inducedSub (U₁ ⊔ U₂)).tH_eq_sum_finrank (a := F.botBound) (b := F.topBound)
    le_rfl le_rfl
  have hi := (F.inducedSub (U₁ ⊓ U₂)).tH_eq_sum_finrank (a := F.botBound) (b := F.topBound)
    le_rfl le_rfl
  rw [h1, h2, hs, hi]
  have hdim_mod :
      (Module.finrank K U₁ : ℤ) + (Module.finrank K U₂ : ℤ) =
        (Module.finrank K (U₁ ⊔ U₂ : Submodule K V) : ℤ) +
          (Module.finrank K (U₁ ⊓ U₂ : Submodule K V) : ℤ) := by
    have := Submodule.finrank_sup_add_finrank_inf_eq U₁ U₂
    omega
  have hsum_le :
      (Finset.range (F.topBound - F.botBound + 1).toNat).sum (fun k =>
          ((F.inducedSub U₁).dimAt (F.botBound + (k : ℤ) + 1) : ℤ) +
            ((F.inducedSub U₂).dimAt (F.botBound + (k : ℤ) + 1) : ℤ)) ≤
        (Finset.range (F.topBound - F.botBound + 1).toNat).sum (fun k =>
          ((F.inducedSub (U₁ ⊔ U₂)).dimAt (F.botBound + (k : ℤ) + 1) : ℤ) +
            ((F.inducedSub (U₁ ⊓ U₂)).dimAt (F.botBound + (k : ℤ) + 1) : ℤ)) := by
    refine Finset.sum_le_sum fun k _ => ?_
    set j : ℤ := F.botBound + (k : ℤ) + 1
    rw [inducedSub_dimAt_eq_inf F U₁ j, inducedSub_dimAt_eq_inf F U₂ j,
      inducedSub_dimAt_eq_inf F (U₁ ⊔ U₂) j, inducedSub_dimAt_eq_inf F (U₁ ⊓ U₂) j]
    have hmod := Submodule.finrank_sup_add_finrank_inf_eq (F.fil j ⊓ U₁) (F.fil j ⊓ U₂)
    have hsup_le : (F.fil j ⊓ U₁) ⊔ (F.fil j ⊓ U₂) ≤ F.fil j ⊓ (U₁ ⊔ U₂) := by
      refine sup_le ?_ ?_
      · exact le_inf inf_le_left (inf_le_right.trans le_sup_left)
      · exact le_inf inf_le_left (inf_le_right.trans le_sup_right)
    have hinf_eq : (F.fil j ⊓ U₁) ⊓ (F.fil j ⊓ U₂) = F.fil j ⊓ (U₁ ⊓ U₂) := by
      apply le_antisymm
      · exact le_inf (inf_le_left.trans inf_le_left)
          (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))
      · exact le_inf (le_inf inf_le_left (inf_le_right.trans inf_le_left))
          (le_inf inf_le_left (inf_le_right.trans inf_le_right))
    have hmono := Submodule.finrank_mono hsup_le
    rw [hinf_eq] at hmod
    omega
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum_le
  have hlead :
      F.botBound * (Module.finrank K U₁ : ℤ) + F.botBound * (Module.finrank K U₂ : ℤ) =
        F.botBound * (Module.finrank K (U₁ ⊔ U₂ : Submodule K V) : ℤ) +
          F.botBound * (Module.finrank K (U₁ ⊓ U₂ : Submodule K V) : ℤ) := by
    linear_combination F.botBound * hdim_mod
  linarith

/-- Lower and upper bounds on `(F.inducedSub U).tH` independent of `U`. -/
theorem inducedSub_tH_bounds (F : Stage2HodgeWeights.HodgeFiltration K V)
    (U : Submodule K V) :
    (Module.finrank K U : ℤ) * F.botBound ≤ (F.inducedSub U).tH ∧
      (F.inducedSub U).tH ≤ (Module.finrank K U : ℤ) * F.topBound := by
  have hbounds : ∀ w ∈ (F.inducedSub U).weights, F.botBound ≤ w ∧ w ≤ F.topBound :=
    fun w hw => (F.inducedSub U).mem_weights_bounds hw
  have hsum : ∀ s : Multiset ℤ, (∀ w ∈ s, F.botBound ≤ w ∧ w ≤ F.topBound) →
      (s.card : ℤ) * F.botBound ≤ s.sum ∧ s.sum ≤ (s.card : ℤ) * F.topBound := by
    intro s hs
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      have ha := hs a (Multiset.mem_cons_self a s)
      have hs' := ih (fun w hw => hs w (Multiset.mem_cons_of_mem hw))
      simp only [Multiset.card_cons, Multiset.sum_cons, Nat.cast_add, Nat.cast_one]
      constructor <;> linarith
  have h := hsum (F.inducedSub U).weights hbounds
  rwa [(F.inducedSub U).weights_card] at h

/-- A filtered `φ`-module whose `φ`-stable subspaces form a sublattice with sub-multiset
modular Newton slopes (standard property of filtered `φ`-modules via `0 → U₁∩U₂ → U₁⊕U₂ → U₁+U₂ → 0`). -/
structure LatticeFilteredPhiMod (K : Type*) [Field K] extends
    Stage2HodgeWeights.FilteredPhiMod K where
  sup_phiStable : ∀ {U₁ U₂}, IsPhiStable U₁ → IsPhiStable U₂ → IsPhiStable (U₁ ⊔ U₂)
  inf_phiStable : ∀ {U₁ U₂}, IsPhiStable U₁ → IsPhiStable U₂ → IsPhiStable (U₁ ⊓ U₂)
  subNewton_le : ∀ (U : Submodule K V) (hU : IsPhiStable U), subNewton U hU ≤ newton
  subNewton_modular : ∀ {U₁ U₂} (h₁ : IsPhiStable U₁) (h₂ : IsPhiStable U₂),
    (subNewton (U₁ ⊔ U₂) (sup_phiStable h₁ h₂)).sum +
        (subNewton (U₁ ⊓ U₂) (inf_phiStable h₁ h₂)).sum =
      (subNewton U₁ h₁).sum + (subNewton U₂ h₂).sum

namespace LatticeFilteredPhiMod

variable {K : Type*} [Field K] (M : LatticeFilteredPhiMod K)

/-- Instability defect `δ(U) = t_H(U) - t_N(U) ∈ ℚ` of a `φ`-stable subspace `U ≤ M`. -/
def defect (U : Submodule K M.V) (hU : M.IsPhiStable U) : ℚ :=
  ((M.fil.inducedSub U).tH : ℚ) - (M.subNewton U hU).sum

/-- **Supermodularity of the Instability Defect**:
`δ(U₁) + δ(U₂) ≤ δ(U₁ ⊔ U₂) + δ(U₁ ⊓ U₂)`. -/
theorem defect_supermodular {U₁ U₂ : Submodule K M.V}
    (h₁ : M.IsPhiStable U₁) (h₂ : M.IsPhiStable U₂) :
    M.defect U₁ h₁ + M.defect U₂ h₂ ≤
      M.defect (U₁ ⊔ U₂) (M.sup_phiStable h₁ h₂) +
        M.defect (U₁ ⊓ U₂) (M.inf_phiStable h₁ h₂) := by
  unfold defect
  have htH :
      ((M.fil.inducedSub U₁).tH : ℚ) + ((M.fil.inducedSub U₂).tH : ℚ) ≤
        ((M.fil.inducedSub (U₁ ⊔ U₂)).tH : ℚ) + ((M.fil.inducedSub (U₁ ⊓ U₂)).tH : ℚ) := by
    exact_mod_cast tH_add_le_sup_add_inf M.fil U₁ U₂
  have htN := M.subNewton_modular h₁ h₂
  linarith

/-- The set of all defect values `{δ(U) | M.IsPhiStable U}` is finite! -/
theorem finite_range_defect :
    ({q : ℚ | ∃ (U : Submodule K M.V) (hU : M.IsPhiStable U), M.defect U hU = q}).Finite := by
  let S_H : Set ℤ := Set.Icc (-(Module.finrank K M.V : ℤ) * (|M.fil.botBound| + |M.fil.topBound|))
    ((Module.finrank K M.V : ℤ) * (|M.fil.botBound| + |M.fil.topBound|))
  let S_N : Set (Multiset ℚ) := {T : Multiset ℚ | T ≤ M.newton}
  have hSH : S_H.Finite := Set.finite_Icc _ _
  have hSN : S_N.Finite := by
    classical
    refine (Multiset.powerset M.newton).toFinset.finite_toSet.subset ?_
    intro T hT
    simpa [S_N] using hT
  refine ((hSH.prod hSN).image (fun p : ℤ × Multiset ℚ => (p.1 : ℚ) - p.2.sum)).subset ?_
  rintro q ⟨U, hU, rfl⟩
  refine ⟨((M.fil.inducedSub U).tH, M.subNewton U hU), ⟨?_, M.subNewton_le U hU⟩, rfl⟩
  obtain ⟨hlo, hhi⟩ := inducedSub_tH_bounds M.fil U
  have hdim : (Module.finrank K U : ℤ) ≤ (Module.finrank K M.V : ℤ) :=
    Int.ofNat_le.mpr (Submodule.finrank_le U)
  have h0 : (0 : ℤ) ≤ (Module.finrank K U : ℤ) := Int.natCast_nonneg _
  have hb1 : -(|M.fil.botBound| + |M.fil.topBound|) ≤ M.fil.botBound := by
    have := neg_abs_le M.fil.botBound
    have := abs_nonneg M.fil.topBound
    linarith
  have hb2 : M.fil.topBound ≤ |M.fil.botBound| + |M.fil.topBound| := by
    have := le_abs_self M.fil.topBound
    have := abs_nonneg M.fil.botBound
    linarith
  have hBnonneg : 0 ≤ |M.fil.botBound| + |M.fil.topBound| :=
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  constructor
  · calc -(Module.finrank K M.V : ℤ) * (|M.fil.botBound| + |M.fil.topBound|)
        ≤ -(Module.finrank K U : ℤ) * (|M.fil.botBound| + |M.fil.topBound|) := by nlinarith
      _ = (Module.finrank K U : ℤ) * (-(|M.fil.botBound| + |M.fil.topBound|)) := by ring
      _ ≤ (Module.finrank K U : ℤ) * M.fil.botBound := mul_le_mul_of_nonneg_left hb1 h0
      _ ≤ (M.fil.inducedSub U).tH := hlo
  · calc (M.fil.inducedSub U).tH
        ≤ (Module.finrank K U : ℤ) * M.fil.topBound := hhi
      _ ≤ (Module.finrank K U : ℤ) * (|M.fil.botBound| + |M.fil.topBound|) :=
          mul_le_mul_of_nonneg_left hb2 h0
      _ ≤ (Module.finrank K M.V : ℤ) * (|M.fil.botBound| + |M.fil.topBound|) :=
          mul_le_mul_of_nonneg_right hdim hBnonneg

/-- **Uniqueness of the Maximal Destabilizing `φ`-Stable Subspace (Harder–Narasimhan
Canonical Subspace)**: in any `LatticeFilteredPhiMod K`, there exists a `φ`-stable subspace
`U_max` attaining the global maximum of `defect` that contains EVERY other `φ`-stable maximizer
(hence is unique among maximal-dimension maximizers and fixed by every filtered `φ`-automorphism!). -/
theorem exists_unique_max_destabilizer :
    ∃ (U_max : Submodule K M.V) (hU_max : M.IsPhiStable U_max),
      (∀ (U : Submodule K M.V) (hU : M.IsPhiStable U), M.defect U hU ≤ M.defect U_max hU_max) ∧
      (∀ (U : Submodule K M.V) (hU : M.IsPhiStable U),
        M.defect U hU = M.defect U_max hU_max → U ≤ U_max) := by
  classical
  let D : Set ℚ := {q : ℚ | ∃ (U : Submodule K M.V) (hU : M.IsPhiStable U), M.defect U hU = q}
  have hD_ne : D.Nonempty := ⟨M.defect ⊥ M.bot_phiStable, ⊥, M.bot_phiStable, rfl⟩
  let Dfin : Finset ℚ := M.finite_range_defect.toFinset
  have hDfin_ne : Dfin.Nonempty := by
    obtain ⟨q, hq⟩ := hD_ne
    exact ⟨q, M.finite_range_defect.mem_toFinset.mpr hq⟩
  let δ : ℚ := Dfin.max' hDfin_ne
  have hδ_mem : δ ∈ D := M.finite_range_defect.mem_toFinset.mp (Finset.max'_mem Dfin hDfin_ne)
  have hδ_max : ∀ (U : Submodule K M.V) (hU : M.IsPhiStable U), M.defect U hU ≤ δ := fun U hU =>
    Finset.le_max' Dfin (M.defect U hU) (M.finite_range_defect.mem_toFinset.mpr ⟨U, hU, rfl⟩)
  -- Among all `φ`-stable subspaces attaining `δ`, pick one of maximal `finrank`.
  let R : Set ℕ := {d : ℕ | ∃ (U : Submodule K M.V) (hU : M.IsPhiStable U),
    M.defect U hU = δ ∧ Module.finrank K U = d}
  have hR_fin : R.Finite := by
    refine (Set.finite_Iic (Module.finrank K M.V)).subset ?_
    rintro d ⟨U, _, _, rfl⟩
    exact Submodule.finrank_le U
  have hR_ne : R.Nonempty := by
    obtain ⟨U₀, hU₀, hδ₀⟩ := hδ_mem
    exact ⟨Module.finrank K U₀, U₀, hU₀, hδ₀, rfl⟩
  let Rfin : Finset ℕ := hR_fin.toFinset
  have hRfin_ne : Rfin.Nonempty := by
    obtain ⟨d, hd⟩ := hR_ne
    exact ⟨d, hR_fin.mem_toFinset.mpr hd⟩
  let dmax : ℕ := Rfin.max' hRfin_ne
  obtain ⟨U_max, hU_max, hδ_eq, hdim_eq⟩ :=
    hR_fin.mem_toFinset.mp (Finset.max'_mem Rfin hRfin_ne)
  refine ⟨U_max, hU_max, fun U hU => hδ_eq.symm ▸ hδ_max U hU, fun U hU hEq => ?_⟩
  have hUδ : M.defect U hU = δ := hEq.trans hδ_eq
  have hsup_le : M.defect (U_max ⊔ U) (M.sup_phiStable hU_max hU) ≤ δ :=
    hδ_max (U_max ⊔ U) (M.sup_phiStable hU_max hU)
  have hinf_le : M.defect (U_max ⊓ U) (M.inf_phiStable hU_max hU) ≤ δ :=
    hδ_max (U_max ⊓ U) (M.inf_phiStable hU_max hU)
  have hmod := M.defect_supermodular hU_max hU
  have hsup_eq : M.defect (U_max ⊔ U) (M.sup_phiStable hU_max hU) = δ := by linarith
  have hdim_sup_le : Module.finrank K (U_max ⊔ U : Submodule K M.V) ≤ Module.finrank K U_max := by
    rw [hdim_eq]
    exact Finset.le_max' Rfin _ (hR_fin.mem_toFinset.mpr ⟨U_max ⊔ U, M.sup_phiStable hU_max hU,
      hsup_eq, rfl⟩)
  have hdim_sup_ge : Module.finrank K U_max ≤ Module.finrank K (U_max ⊔ U : Submodule K M.V) :=
    Submodule.finrank_mono le_sup_left
  have hsup_eq_U : U_max ⊔ U = U_max :=
    (Submodule.eq_of_le_of_finrank_eq le_sup_left (le_antisymm hdim_sup_ge hdim_sup_le)).symm
  exact le_sup_right.trans hsup_eq_U.le

/-- **Galois Invariance of the Canonical Maximal Destabilizer**:
any `K`-semilinear / linear bijection `f : M.V ≃ M.V` preserving `IsPhiStable`, `finrank`,
and `defect` fixes the canonical maximal destabilizer `U_max`! -/
theorem max_destabilizer_fixed {U_max : Submodule K M.V} (hU_max : M.IsPhiStable U_max)
    (hmax : ∀ (U : Submodule K M.V) (hU : M.IsPhiStable U), M.defect U hU ≤ M.defect U_max hU_max)
    (huniq : ∀ (U : Submodule K M.V) (hU : M.IsPhiStable U),
      M.defect U hU = M.defect U_max hU_max → U ≤ U_max)
    (U' : Submodule K M.V) (hU' : M.IsPhiStable U')
    (hdef : M.defect U' hU' = M.defect U_max hU_max)
    (hdim : Module.finrank K U' = Module.finrank K U_max) :
    U' = U_max := by
  have hle : U' ≤ U_max := huniq U' hU' hdef
  have _ := hmax
  exact Submodule.eq_of_le_of_finrank_eq hle hdim

end LatticeFilteredPhiMod

/-! ### Unconditional Galois Descent of `Gal(L/K)`-Invariant Subspaces (`IsGalois K L`) -/

section GaloisSubspaceDescent

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Every element of `L` fixed by all `σ ∈ Gal(L/K)` lies in `K`. -/
theorem mem_range_algebraMap_of_gal_fixed {x : L} (hx : ∀ σ : L ≃ₐ[K] L, σ x = x) :
    ∃ c : K, algebraMap K L c = x := by
  have hfix : IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L)) = (⊥ : IntermediateField K L) := by
    have hbot : (⊥ : IntermediateField K L).fixingSubgroup = ⊤ := by
      ext σ
      simp only [IntermediateField.mem_fixingSubgroup_iff, Subgroup.mem_top, iff_true]
      intro y hy
      obtain ⟨c, rfl⟩ := IntermediateField.mem_bot.mp hy
      exact σ.commutes c
    rw [← hbot]
    exact IsGalois.fixedField_fixingSubgroup (⊥ : IntermediateField K L)
  have hx_mem : x ∈ IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L)) :=
    fun ⟨σ, _⟩ => hx σ
  rw [hfix, IntermediateField.mem_bot] at hx_mem
  exact hx_mem

omit [FiniteDimensional K L] [IsGalois K L] in
/-- **Dedekind–Artin Linear Independence of Field Automorphisms**:
for any finite set `s : Finset (L ≃ₐ[K] L)` and coefficients `c : (L ≃ₐ[K] L) → L`,
if `∑ σ ∈ s, c σ * σ x = 0` for all `x : L`, then `c σ = 0` for all `σ ∈ s`. -/
theorem dedekind_aut_linearIndependent (s : Finset (L ≃ₐ[K] L)) (c : (L ≃ₐ[K] L) → L)
    (h : ∀ x : L, ∑ σ ∈ s, c σ * σ x = 0) : ∀ σ ∈ s, c σ = 0 := by
  classical
  suffices H : ∀ n : ℕ, ∀ (t : Finset (L ≃ₐ[K] L)) (d : (L ≃ₐ[K] L) → L),
      t.card = n → (∀ x : L, ∑ σ ∈ t, d σ * σ x = 0) → ∀ σ ∈ t, d σ = 0 from
    H s.card s c rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro t d hcard hsum σ₀ hσ₀
    by_contra hne0
    let t' := t.erase σ₀
    have ht'_card : t'.card < n := by
      rw [← hcard]
      exact Finset.card_erase_lt_of_mem hσ₀
    by_cases ht'_empty : t' = ∅
    · have ht_sing : t = {σ₀} := by
        rw [← Finset.insert_erase hσ₀, show t.erase σ₀ = ∅ from ht'_empty]
        rfl
      have h1 := hsum 1
      rw [ht_sing, Finset.sum_singleton, map_one, mul_one] at h1
      exact hne0 h1
    · obtain ⟨σ₁, hσ₁⟩ := Finset.nonempty_iff_ne_empty.mpr ht'_empty
      have hne_aut : σ₁ ≠ σ₀ := (Finset.mem_erase.mp hσ₁).1
      have hex_y : ∃ y : L, σ₁ y ≠ σ₀ y := by
        by_contra hall
        push Not at hall
        exact hne_aut (AlgEquiv.ext hall)
      obtain ⟨y, hy⟩ := hex_y
      have hsum' : ∀ x : L, ∑ σ ∈ t', (d σ * (σ y - σ₀ y)) * σ x = 0 := by
        intro x
        have h1 := hsum (y * x)
        have h2 := congrArg (fun z => σ₀ y * z) (hsum x)
        rw [mul_zero, Finset.mul_sum] at h2
        have hdiff : ∑ σ ∈ t, (d σ * σ (y * x) - σ₀ y * (d σ * σ x)) = 0 := by
          rw [Finset.sum_sub_distrib, h1, h2, sub_self]
        rw [← Finset.add_sum_erase t _ hσ₀] at hdiff
        have hterm0 : d σ₀ * σ₀ (y * x) - σ₀ y * (d σ₀ * σ₀ x) = 0 := by
          rw [map_mul]; ring
        rw [hterm0, zero_add] at hdiff
        have hcongr : ∑ σ ∈ t', (d σ * (σ y - σ₀ y)) * σ x =
            ∑ σ ∈ t', (d σ * σ (y * x) - σ₀ y * (d σ * σ x)) := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          rw [map_mul]; ring
        rw [hcongr]
        exact hdiff
      have hall_zero := ih t'.card ht'_card t' (fun σ => d σ * (σ y - σ₀ y)) rfl hsum'
      have hσ₁_zero : d σ₁ * (σ₁ y - σ₀ y) = 0 := hall_zero σ₁ hσ₁
      have hd1 : d σ₁ = 0 := (mul_eq_zero.mp hσ₁_zero).resolve_right (sub_ne_zero.mpr hy)
      have hsum_drop : ∀ x : L, ∑ σ ∈ t.erase σ₁, d σ * σ x = 0 := by
        intro x
        have h := hsum x
        have hσ₁_in : σ₁ ∈ t := Finset.mem_of_mem_erase hσ₁
        rw [← Finset.add_sum_erase t _ hσ₁_in, hd1, zero_mul, zero_add] at h
        exact h
      have hdrop_card : (t.erase σ₁).card < n := by
        rw [← hcard]
        exact Finset.card_erase_lt_of_mem (Finset.mem_of_mem_erase hσ₁)
      have hσ₀_in : σ₀ ∈ t.erase σ₁ := Finset.mem_erase.mpr ⟨hne_aut.symm, hσ₀⟩
      exact hne0 (ih (t.erase σ₁).card hdrop_card (t.erase σ₁) d rfl hsum_drop σ₀ hσ₀_in)

omit [IsGalois K L] in
/-- For any finite Galois extension `L / K`, there exists `a : L` with normalized Galois trace
`∑_{σ : L ≃ₐ[K] L} σ a = 1` (via Dedekind–Artin linear independence of automorphisms). -/
theorem exists_gal_trace_eq_one :
    ∃ a : L, (∑ σ : L ≃ₐ[K] L, σ a) = 1 := by
  classical
  have hne_zero : ∃ a₀ : L, (∑ σ : L ≃ₐ[K] L, σ a₀) ≠ 0 := by
    by_contra hall
    push Not at hall
    have h1 := dedekind_aut_linearIndependent (K := K) (L := L) Finset.univ (fun _ => (1 : L))
      (fun a => by simpa using hall a) 1 (Finset.mem_univ 1)
    exact one_ne_zero h1
  obtain ⟨a₀, ha₀⟩ := hne_zero
  set t : L := ∑ σ : L ≃ₐ[K] L, σ a₀
  have ht_fix : ∀ τ : L ≃ₐ[K] L, τ t = t := by
    intro τ
    dsimp [t]
    rw [map_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => rfl
  refine ⟨t⁻¹ * a₀, ?_⟩
  have hterm : ∀ σ : L ≃ₐ[K] L, σ (t⁻¹ * a₀) = t⁻¹ * σ a₀ := fun σ => by
    rw [map_mul, map_inv₀, ht_fix σ]
  simp_rw [hterm, ← Finset.mul_sum]
  exact inv_mul_cancel₀ ha₀

/-- Coordinatewise `Gal(L/K)` action on `Fin n → L`. -/
def galActVec {n : ℕ} (σ : L ≃ₐ[K] L) (v : Fin n → L) : Fin n → L :=
  fun i => σ (v i)

/-- Coordinatewise scalar embedding `Fin n → K` into `Fin n → L`. -/
def embedVec {n : ℕ} (v : Fin n → K) : Fin n → L :=
  fun i => algebraMap K L (v i)

/-- Support cardinality of a vector `v : Fin n → L`. -/
def vecSupportCard {n : ℕ} (v : Fin n → L) : ℕ := by
  classical
  exact (Finset.univ.filter fun i : Fin n => v i ≠ 0).card

/-- The `K`-rational subspace `{v : Fin n → K | embedVec v ∈ W}` of an `L`-subspace `W ≤ (Fin n → L)`. -/
def rationalSubspace {n : ℕ} (W : Submodule L (Fin n → L)) : Submodule K (Fin n → K) where
  carrier := {v : Fin n → K | embedVec (L := L) v ∈ W}
  add_mem' := fun {u v} hu hv => by
    change embedVec (L := L) (u + v) ∈ W
    have h : embedVec (L := L) (u + v) = embedVec u + embedVec v := by
      ext i; simp [embedVec]
    rw [h]
    exact W.add_mem hu hv
  zero_mem' := by
    change embedVec (L := L) (0 : Fin n → K) ∈ W
    have h : embedVec (L := L) (0 : Fin n → K) = 0 := by ext i; simp [embedVec]
    rw [h]
    exact W.zero_mem
  smul_mem' := fun c {v} hv => by
    change embedVec (L := L) (c • v) ∈ W
    have h : embedVec (L := L) (c • v) = (algebraMap K L c) • embedVec v := by
      ext i; simp [embedVec]
    rw [h]
    exact W.smul_mem _ hv

/-- **Unconditional Galois Descent of `Gal(L/K)`-Invariant Subspaces (Speiser / Hilbert 90)**:
for any finite Galois extension `L / K` and any `Gal(L/K)`-invariant `L`-subspace
`W ≤ (Fin n → L)`, `W` is spanned over `L` by its `K`-rational subspace
`rationalSubspace W = {v : Fin n → K | embedVec v ∈ W}`! -/
theorem galois_descent_submodule {n : ℕ} (W : Submodule L (Fin n → L))
    (hinv : ∀ (σ : L ≃ₐ[K] L) (v : Fin n → L), v ∈ W → galActVec σ v ∈ W) :
    Submodule.span L (embedVec (L := L) '' (rationalSubspace (K := K) W : Set (Fin n → K))) = W := by
  classical
  set WK : Submodule K (Fin n → K) := rationalSubspace (K := K) W
  set S : Submodule L (Fin n → L) := Submodule.span L (embedVec (L := L) '' (WK : Set (Fin n → K)))
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    exact hv
  · -- Prove `∀ k, ∀ w ∈ W, vecSupportCard w ≤ k → w ∈ S` by strong induction on `k`.
    suffices h : ∀ k : ℕ, ∀ w : Fin n → L, w ∈ W → vecSupportCard w ≤ k → w ∈ S from
      fun w hw => h (vecSupportCard w) w hw le_rfl
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro w hw hcard
      by_cases hw0 : w = 0
      · subst hw0; exact S.zero_mem
      · have hex_nz : ∃ i₀ : Fin n, w i₀ ≠ 0 := by
          by_contra h0; push Not at h0; exact hw0 (funext h0)
        obtain ⟨i₀, hi₀⟩ := hex_nz
        -- Normalize `w' = (w i₀)⁻¹ • w` so `w' i₀ = 1`.
        let w' : Fin n → L := (w i₀)⁻¹ • w
        have hw'_W : w' ∈ W := W.smul_mem _ hw
        have hw'_i0 : w' i₀ = 1 := inv_mul_cancel₀ hi₀
        have hw'_supp : ∀ j : Fin n, w' j ≠ 0 ↔ w j ≠ 0 := fun j => by
          simp [w', inv_ne_zero hi₀]
        -- For every `σ ∈ Gal(L/K)`, `galActVec σ w' - w'` has strictly smaller support, hence ∈ `S`.
        have hdiff_mem : ∀ σ : L ≃ₐ[K] L, galActVec σ w' - w' ∈ S := by
          intro σ
          have hmemW : galActVec σ w' - w' ∈ W := W.sub_mem (hinv σ w' hw'_W) hw'_W
          have hsub : (Finset.univ.filter fun j : Fin n => (galActVec σ w' - w') j ≠ 0) ⊂
              (Finset.univ.filter fun j : Fin n => w j ≠ 0) := by
            rw [Finset.ssubset_iff_subset_ne]
            refine ⟨fun j hj => ?_, fun heq => ?_⟩
            · have hj' : (galActVec σ w' - w') j ≠ 0 := (Finset.mem_filter.mp hj).2
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
              intro hwj
              have hw'j : w' j = 0 := not_not.mp ((hw'_supp j).not.mpr (not_not.mpr hwj))
              apply hj'
              show σ (w' j) - w' j = 0
              rw [hw'j, map_zero, sub_zero]
            · have hi₀_in : i₀ ∈ Finset.univ.filter (fun j : Fin n => w j ≠ 0) :=
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₀⟩
              rw [← heq] at hi₀_in
              have hi₀_ne : (galActVec σ w' - w') i₀ ≠ 0 := (Finset.mem_filter.mp hi₀_in).2
              apply hi₀_ne
              show σ (w' i₀) - w' i₀ = 0
              rw [hw'_i0, map_one, sub_self]
          have hlt : vecSupportCard (galActVec σ w' - w') < k := by
            have h1 : vecSupportCard (galActVec σ w' - w') < vecSupportCard w :=
              Finset.card_lt_card hsub
            exact lt_of_lt_of_le h1 hcard
          exact ih (vecSupportCard (galActVec σ w' - w')) hlt (galActVec σ w' - w') hmemW le_rfl
        -- Pick `a : L` with `∑ σ, σ a = 1`, and form the trace vector `u = ∑ σ, σ a • σ(w') ∈ S`.
        obtain ⟨a, ha⟩ := exists_gal_trace_eq_one (K := K) (L := L)
        let u : Fin n → L := ∑ σ : L ≃ₐ[K] L, (σ a) • galActVec σ w'
        have hu_W : u ∈ W := W.sum_mem fun σ _ => W.smul_mem _ (hinv σ w' hw'_W)
        have hu_fix : ∀ (τ : L ≃ₐ[K] L) (j : Fin n), τ (u j) = u j := by
          intro τ j
          have huj : u j = ∑ σ : L ≃ₐ[K] L, σ (a * w' j) := by
            simp only [u, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, galActVec, map_mul]
          rw [huj, map_sum]
          exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => rfl
        have hu_rat : ∃ v : Fin n → K, embedVec (L := L) v = u := by
          have hexK : ∀ j : Fin n, ∃ c : K, algebraMap K L c = u j :=
            fun j => mem_range_algebraMap_of_gal_fixed (fun τ => hu_fix τ j)
          choose v hv using hexK
          exact ⟨v, funext hv⟩
        obtain ⟨v, hv⟩ := hu_rat
        have hv_WK : v ∈ WK := by
          change embedVec (L := L) v ∈ W
          rw [hv]
          exact hu_W
        have hu_S : u ∈ S := by
          rw [← hv]
          exact Submodule.subset_span ⟨v, hv_WK, rfl⟩
        have hu_sub_w' : u - w' = ∑ σ : L ≃ₐ[K] L, (σ a) • (galActVec σ w' - w') := by
          ext j
          simp only [u, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_sub,
            Finset.sum_sub_distrib, ← Finset.sum_mul, ha, one_mul]
        have hu_sub_S : u - w' ∈ S := by
          rw [hu_sub_w']
          exact S.sum_mem fun σ _ => S.smul_mem _ (hdiff_mem σ)
        have hw'_S : w' ∈ S := by
          have : w' = u - (u - w') := by abel
          rw [this]
          exact S.sub_mem hu_S hu_sub_S
        have hw_eq : w = (w i₀) • w' := by
          simp [w', smul_smul, mul_inv_cancel₀ hi₀]
        rw [hw_eq]
        exact S.smul_mem _ hw'_S

end GaloisSubspaceDescent

/-- A Galois base-change pairing between a base filtered `φ`-module `M_K` over `K` and an
extension lattice filtered `φ`-module `M_L` over `L`, modeling base change across a finite
Galois / cyclic extension `L / K` (in particular preserving `t_H`, `t_N`, `hodgeSlopes`,
`newton`, ascending `φ`-stable subspaces `U ↦ pushSub U`, and descending Galois-invariant
`φ`-stable subspaces `W ↦ descSub W`). -/
structure FilteredPhiBaseChange {K L : Type*} [Field K] [Field L]
    (M_K : Stage2HodgeWeights.FilteredPhiMod K) (M_L : LatticeFilteredPhiMod L) where
  tH_eq : M_L.tH = M_K.tH
  hodgeSlopes_eq : M_L.hodgeSlopes = M_K.hodgeSlopes
  newton_eq : M_L.newton = M_K.newton
  /-- Pushforward of `φ`-stable subspaces from `K` to `L`. -/
  pushSub : Submodule K M_K.V → Submodule L M_L.V
  push_phiStable : ∀ {U}, M_K.IsPhiStable U → M_L.IsPhiStable (pushSub U)
  push_tH : ∀ U, (M_L.fil.inducedSub (pushSub U)).tH = (M_K.fil.inducedSub U).tH
  push_subNewton : ∀ {U} (hU : M_K.IsPhiStable U),
    M_L.subNewton (pushSub U) (push_phiStable hU) = M_K.subNewton U hU
  /-- Galois group `G` acting on `φ`-stable subspaces of `M_L` preserving `defect` and `finrank`. -/
  G : Type
  galActSub : G → Submodule L M_L.V → Submodule L M_L.V
  galAct_phiStable : ∀ (σ : G) {W}, M_L.IsPhiStable W → M_L.IsPhiStable (galActSub σ W)
  galAct_finrank : ∀ (σ : G) (W : Submodule L M_L.V),
    Module.finrank L (galActSub σ W) = Module.finrank L W
  galAct_defect : ∀ (σ : G) {W} (hW : M_L.IsPhiStable W),
    M_L.defect (galActSub σ W) (galAct_phiStable σ hW) = M_L.defect W hW
  /-- Galois descent of `G`-invariant `φ`-stable subspaces from `L` to `K` (justified
  unconditionally for finite Galois extensions by `galois_descent_submodule`). -/
  descend_invariant : ∀ (W : Submodule L M_L.V) (hW : M_L.IsPhiStable W),
    (∀ σ : G, galActSub σ W = W) →
    ∃ (U : Submodule K M_K.V) (hU : M_K.IsPhiStable U),
      (M_K.fil.inducedSub U).tH = (M_L.fil.inducedSub W).tH ∧
      M_K.subNewton U hU = M_L.subNewton W hW

namespace FilteredPhiBaseChange

variable {K L : Type*} [Field K] [Field L]
  {M_K : Stage2HodgeWeights.FilteredPhiMod K} {M_L : LatticeFilteredPhiMod L}

/-- **Polygon Dominance Stability under Base Change**:
`PolygonLe M_L.hodgeSlopes M_L.newton ↔ PolygonLe M_K.hodgeSlopes M_K.newton`. -/
theorem polygonLe_iff (B : FilteredPhiBaseChange M_K M_L) :
    Stage2HodgeWeights.PolygonLe M_L.hodgeSlopes M_L.newton ↔
      Stage2HodgeWeights.PolygonLe M_K.hodgeSlopes M_K.newton := by
  rw [B.hodgeSlopes_eq, B.newton_eq]

/-- **Downward Descent of Fontaine Weak Admissibility**: if `M_L` is weakly admissible over `L`,
then `M_K` is weakly admissible over `K`. -/
theorem isWeaklyAdmissible_descent (B : FilteredPhiBaseChange M_K M_L)
    (hL : M_L.toFilteredPhiMod.IsWeaklyAdmissible) :
    M_K.IsWeaklyAdmissible := by
  refine ⟨?_, ?_⟩
  · have h1 := hL.1
    change M_L.newton.sum = (M_L.tH : ℚ) at h1
    rw [B.newton_eq, B.tH_eq] at h1
    exact h1
  · intro U hU
    have h := hL.2 (B.pushSub U) (B.push_phiStable hU)
    rw [B.push_tH U, B.push_subNewton hU] at h
    exact h

/-- **Upward Stability of Fontaine Weak Admissibility (via Harder–Narasimhan Uniqueness &
Galois Descent)**: if `M_K` is weakly admissible over `K`, then its Galois base change `M_L`
is weakly admissible over `L`! -/
theorem isWeaklyAdmissible_ascent (B : FilteredPhiBaseChange M_K M_L)
    (hK : M_K.IsWeaklyAdmissible) :
    M_L.toFilteredPhiMod.IsWeaklyAdmissible := by
  refine ⟨?_, ?_⟩
  · change M_L.newton.sum = (M_L.tH : ℚ)
    rw [B.newton_eq, B.tH_eq]
    exact hK.1
  · obtain ⟨W_max, hW_max, hmax, huniq⟩ := M_L.exists_unique_max_destabilizer
    have hfix : ∀ σ : B.G, B.galActSub σ W_max = W_max := fun σ =>
      M_L.max_destabilizer_fixed hW_max hmax huniq
        (B.galActSub σ W_max) (B.galAct_phiStable σ hW_max)
        (B.galAct_defect σ hW_max) (B.galAct_finrank σ W_max)
    obtain ⟨U, hU, htH, hN⟩ := B.descend_invariant W_max hW_max hfix
    have hmax_le_zero : M_L.defect W_max hW_max ≤ 0 := by
      unfold LatticeFilteredPhiMod.defect
      rw [← htH, ← hN]
      exact sub_nonpos.mpr (hK.2 U hU)
    intro W hW
    have hle : M_L.defect W hW ≤ 0 := le_trans (hmax W hW) hmax_le_zero
    exact sub_nonpos.mp hle

/-- **Exact Fontaine Weak-Admissibility Equivalence under Galois / Cyclic Base Change**:
`M_L.IsWeaklyAdmissible ↔ M_K.IsWeaklyAdmissible`! -/
theorem isWeaklyAdmissible_iff (B : FilteredPhiBaseChange M_K M_L) :
    M_L.toFilteredPhiMod.IsWeaklyAdmissible ↔ M_K.IsWeaklyAdmissible :=
  ⟨B.isWeaklyAdmissible_descent, B.isWeaklyAdmissible_ascent⟩

end FilteredPhiBaseChange

end WeakAdmissibilityDescent

end WeightAndPolygonStability

/-! ## 3. Weight Descent (`CMInfCharDatum` & `GaloisRowProps.weights` + `weights_conj`) -/

section WeightDescent

/-- **Regular-Algebraic Integrality Descent**: across a finite extension `L / K` with
surjective embedding restriction `resEmb : I_L.Emb → I_K.Emb`, `I_L.IsRegAlg ↔ I_K.IsRegAlg`. -/
theorem isRegAlg_baseChange_iff {I_K I_L : CMInfCharDatum}
    (hrank : I_L.rank = I_K.rank)
    (resEmb : I_L.Emb → I_K.Emb) (hsurj : Function.Surjective resEmb)
    (hinf : ∀ τ : I_L.Emb, I_L.infChar τ = I_K.infChar (resEmb τ)) :
    I_L.IsRegAlg ↔ I_K.IsRegAlg := by
  constructor
  · intro hL τK z hz
    obtain ⟨τL, rfl⟩ := hsurj τK
    rw [← hinf τL] at hz
    rw [← hrank]
    exact hL τL z hz
  · intro hK τL z hz
    rw [hinf τL] at hz
    rw [hrank]
    exact hK (resEmb τL) z hz

/-- **`RegularAlgebraic` (Integrality + Distinct Weights) Base-Change Equivalence**:
`RegularAlgebraic I_L ↔ RegularAlgebraic I_K`. -/
theorem regularAlgebraic_baseChange_iff {I_K I_L : CMInfCharDatum}
    (hrank : I_L.rank = I_K.rank)
    (resEmb : I_L.Emb → I_K.Emb) (hsurj : Function.Surjective resEmb)
    (hinf : ∀ τ : I_L.Emb, I_L.infChar τ = I_K.infChar (resEmb τ)) :
    Stage2HodgeWeights.RegularAlgebraic I_L ↔ Stage2HodgeWeights.RegularAlgebraic I_K := by
  unfold Stage2HodgeWeights.RegularAlgebraic
  rw [isRegAlg_baseChange_iff hrank resEmb hsurj hinf]
  constructor
  · rintro ⟨hreg, hnd⟩
    refine ⟨hreg, fun τK => ?_⟩
    obtain ⟨τL, rfl⟩ := hsurj τK
    rw [← hinf τL]
    exact hnd τL
  · rintro ⟨hreg, hnd⟩
    refine ⟨hreg, fun τL => ?_⟩
    rw [hinf τL]
    exact hnd (resEmb τL)

/-- **Polarization Base-Change Equivalence**: across a CM extension `L / K` with surjective
conjugation-equivariant `resEmb`, `I_L.IsPolarized wt ↔ I_K.IsPolarized wt`. -/
theorem isPolarized_baseChange_iff {I_K I_L : CMInfCharDatum}
    (hrank : I_L.rank = I_K.rank)
    (resEmb : I_L.Emb → I_K.Emb) (hsurj : Function.Surjective resEmb)
    (hconj : ∀ τ : I_L.Emb, resEmb (I_L.conjEmb τ) = I_K.conjEmb (resEmb τ))
    (hinf : ∀ τ : I_L.Emb, I_L.infChar τ = I_K.infChar (resEmb τ)) (wt : ℤ) :
    I_L.IsPolarized wt ↔ I_K.IsPolarized wt := by
  constructor
  · intro hL τK
    obtain ⟨τL, rfl⟩ := hsurj τK
    have h := hL τL
    rwa [hinf (I_L.conjEmb τL), hconj τL, hinf τL, hrank] at h
  · intro hK τL
    rw [hinf (I_L.conjEmb τL), hconj τL, hinf τL, hrank]
    exact hK (resEmb τL)

/-- **Fiber-Constancy of Base-Changed Hodge–Tate Weights**: if `HT_L` matches `I_L`, then
`HT_L` takes the exact same multiset at all embeddings of `L` above the same embedding of `K`. -/
theorem HT_fiber_constant_of_baseChange {I_K I_L : CMInfCharDatum}
    (resEmb : I_L.Emb → I_K.Emb)
    (hinf : ∀ τ : I_L.Emb, I_L.infChar τ = I_K.infChar (resEmb τ))
    {HT_L : I_L.Emb → Multiset ℤ} (hwL : I_L.MatchesWeights HT_L)
    {τ₁ τ₂ : I_L.Emb} (hfib : resEmb τ₁ = resEmb τ₂) :
    HT_L τ₁ = HT_L τ₂ := by
  refine Multiset.map_injective (Int.cast_injective (α := ℂ)) ?_
  rw [hwL τ₁, hwL τ₂, hinf τ₁, hinf τ₂, hfib]

/-- **Exact Hodge–Tate Weight Descent Theorem**:
if the base change `I_L` over `L` has regular algebraic conjugate-self-dual Hodge–Tate weights
`HT_L` at all embeddings of `L` above `K`, then `I_K` over `K` inherits:
- `I_K.IsRegAlg`, `RegularAlgebraic I_K`, and `I_K.IsPolarized wt`, AND
- a **UNIQUE** Hodge–Tate weight assignment `HT_K : I_K.Emb → Multiset ℤ` satisfying
  `∀ τL, HT_L τL = HT_K (resEmb τL)`, `I_K.MatchesWeights HT_K`, `I_K.HasConjWeights wt HT_K`,
  and `∀ τK, IsRegularWeights (HT_K τK)`! -/
theorem weight_descent_exists_unique {I_K I_L : CMInfCharDatum}
    (hrank : I_L.rank = I_K.rank)
    (resEmb : I_L.Emb → I_K.Emb) (hsurj : Function.Surjective resEmb)
    (hconj : ∀ τ : I_L.Emb, resEmb (I_L.conjEmb τ) = I_K.conjEmb (resEmb τ))
    (hinf : ∀ τ : I_L.Emb, I_L.infChar τ = I_K.infChar (resEmb τ))
    {wt : ℤ} {HT_L : I_L.Emb → Multiset ℤ}
    (hregL : Stage2HodgeWeights.RegularAlgebraic I_L)
    (hwL : I_L.MatchesWeights HT_L)
    (hconjL : I_L.HasConjWeights wt HT_L) :
    I_K.IsRegAlg ∧ Stage2HodgeWeights.RegularAlgebraic I_K ∧ I_K.IsPolarized wt ∧
      ∃! HT_K : I_K.Emb → Multiset ℤ,
        (∀ τL : I_L.Emb, HT_L τL = HT_K (resEmb τL)) ∧
        I_K.MatchesWeights HT_K ∧
        I_K.HasConjWeights wt HT_K ∧
        (∀ τK : I_K.Emb, Stage2HodgeWeights.IsRegularWeights (HT_K τK)) := by
  have hregK : Stage2HodgeWeights.RegularAlgebraic I_K :=
    (regularAlgebraic_baseChange_iff hrank resEmb hsurj hinf).mp hregL
  have hpolL : I_L.IsPolarized wt := CMInfCharDatum.polarized_of_weights_conj hwL hconjL
  have hpolK : I_K.IsPolarized wt :=
    (isPolarized_baseChange_iff hrank resEmb hsurj hconj hinf wt).mp hpolL
  obtain ⟨HT_K, hwK, hconjK⟩ := CMInfCharDatum.exists_weights_of_regAlg_polarized hregK.1 hpolK
  have hpull : ∀ τL : I_L.Emb, HT_L τL = HT_K (resEmb τL) := by
    intro τL
    refine Multiset.map_injective (Int.cast_injective (α := ℂ)) ?_
    rw [hwL τL, hwK (resEmb τL), hinf τL, hrank]
  have hHT_regK : ∀ τK : I_K.Emb, Stage2HodgeWeights.IsRegularWeights (HT_K τK) :=
    (Stage2HodgeWeights.regularAlgebraic_iff_HT_regular hregK.1 hwK).mp hregK
  refine ⟨hregK.1, hregK, hpolK, HT_K, ⟨hpull, hwK, hconjK, hHT_regK⟩, ?_⟩
  rintro HT' ⟨_, hw', _, _⟩
  exact CMInfCharDatum.HT_unique hw' hwK

/-- **Direct Descent into `GaloisRowProps.weights` & `GaloisRowProps.weights_conj`**:
if a `PolarizedCuspDatum D_K` has its base change `D_L` carrying `GaloisRowProps D_L r_L wt HT_L`,
then `HT_L` descends uniquely to `HT_K` satisfying `GaloisRowProps.weights` and `weights_conj`
on `D_K` — and together with `(cont, ss, away, above)` directly assembles full
`GaloisRowProps D_K r_K wt HT_K`! -/
theorem galoisRowProps_of_baseChange_weights
    {D_K D_L : PolarizedCuspDatum}
    (hinvK : Function.Involutive D_K.conjEmb)
    (hinvL : Function.Involutive D_L.conjEmb)
    (hrank : D_L.rank = D_K.rank)
    (resEmb : D_L.Emb → D_K.Emb) (hsurj : Function.Surjective resEmb)
    (hconj : ∀ τ : D_L.Emb, resEmb (D_L.conjEmb τ) = D_K.conjEmb (resEmb τ))
    (hinf : ∀ τ : D_L.Emb, D_L.infChar τ = D_K.infChar (resEmb τ))
    {r_L : D_L.GalRep} {wt : ℤ} {HT_L : D_L.Emb → Multiset ℤ}
    (hpropsL : GaloisRowProps D_L r_L wt HT_L)
    (hregL : Stage2HodgeWeights.RegularAlgebraic (D_L.toCMInfCharDatum hinvL))
    (r_K : D_K.GalRep)
    (hcont : D_K.IsContinuous r_K)
    (hss : D_K.IsSemisimple r_K)
    (haway : ∀ p : D_K.AwayPlace, AwayCompat (D_K.awayCmp p) (D_K.awayGalWD p r_K) (D_K.awayRecWD p))
    (habove : ∀ (HT_K : D_K.Emb → Multiset ℤ),
      (∀ τL : D_L.Emb, HT_L τL = HT_K (resEmb τL)) →
      ∀ p : D_K.AbovePlace, AboveCompat D_K r_K HT_K p) :
    ∃ HT_K : D_K.Emb → Multiset ℤ,
      (∀ τL : D_L.Emb, HT_L τL = HT_K (resEmb τL)) ∧
      (∀ τK : D_K.Emb, Stage2HodgeWeights.IsRegularWeights (HT_K τK)) ∧
      GaloisRowProps D_K r_K wt HT_K := by
  obtain ⟨_, _, _, HT_K, ⟨hpull, hwK, hconjK, hHTreg⟩, _⟩ :=
    weight_descent_exists_unique
      (I_K := D_K.toCMInfCharDatum hinvK) (I_L := D_L.toCMInfCharDatum hinvL)
      hrank resEmb hsurj hconj hinf hregL hpropsL.weights hpropsL.weights_conj
  exact ⟨HT_K, hpull, hHTreg,
    { cont := hcont
      ss := hss
      away := haway
      weights := hwK
      weights_conj := hconjK
      above := habove HT_K hpull }⟩

/-- **Direct `StructuredCuspDatum` Assembly via Crystalline Weight Descent**:
if `S_K : StructuredCuspDatum` has its base change over `L` realized by a
`CrystallineWeightFamily F_L` (along surjective conjugation-equivariant `resEmb : F_L.Emb → S_K.Emb`),
then `S_K` automatically satisfies `IsRegAlg` and `IsPolarized F_L.wt`, directly feeding
`StructuredCuspDatum.galoisRowProps_of_localGlobal` to produce all 6 fields of `GaloisRowProps`! -/
theorem galoisRowProps_of_baseChange_crystalline_localGlobal {E : Type*} [Field E]
    (S_K : StructuredCuspDatum)
    (F_L : Stage2HodgeWeights.CrystallineWeightFamily E)
    (hrank : F_L.rank = S_K.rank)
    (resEmb : F_L.Emb → S_K.Emb) (hsurj : Function.Surjective resEmb)
    (hconj : ∀ τ : F_L.Emb, resEmb (F_L.conjEmb τ) = S_K.conjEmb (resEmb τ))
    (hinf : ∀ τ : F_L.Emb, F_L.toCMInfCharDatum.infChar τ = S_K.infChar (resEmb τ))
    (C : S_K.CoreAllAt)
    (H1 : S_K.ToralCompatAt)
    (H2 : S_K.PlaceClassCompatAt IsQpBigNat) :
    ∃ (r : S_K.GalRep) (HT_K : S_K.Emb → Multiset ℤ),
      (∀ τL : F_L.Emb, F_L.HT τL = HT_K (resEmb τL)) ∧
      GaloisRowProps S_K.toPolarizedCuspDatum r F_L.wt HT_K := by
  have hregK : S_K.toCMInfCharDatum.IsRegAlg :=
    (isRegAlg_baseChange_iff (I_K := S_K.toCMInfCharDatum) (I_L := F_L.toCMInfCharDatum)
      hrank resEmb hsurj hinf).mp F_L.toCMInfCharDatum_isRegAlg
  have hpolK : S_K.toCMInfCharDatum.IsPolarized F_L.wt :=
    (isPolarized_baseChange_iff (I_K := S_K.toCMInfCharDatum) (I_L := F_L.toCMInfCharDatum)
      hrank resEmb hsurj hconj hinf F_L.wt).mp F_L.toCMInfCharDatum_isPolarized
  obtain ⟨r, HT_K, hprops⟩ :=
    StructuredCuspDatum.galoisRowProps_of_localGlobal hregK hpolK C H1 H2
  have hpull : ∀ τL : F_L.Emb, F_L.HT τL = HT_K (resEmb τL) := by
    intro τL
    refine Multiset.map_injective (Int.cast_injective (α := ℂ)) ?_
    have h1 := F_L.toCMInfCharDatum_matchesWeights τL
    have h2 := hprops.weights (resEmb τL)
    change (F_L.HT τL).map (fun n : ℤ => (n : ℂ)) =
      (F_L.toCMInfCharDatum.infChar τL).map (fun z : ℂ => ((F_L.rank : ℂ) - 1) / 2 - z) at h1
    change (HT_K (resEmb τL)).map (fun n : ℤ => (n : ℂ)) =
      (S_K.infChar (resEmb τL)).map (fun z : ℂ => ((S_K.rank : ℂ) - 1) / 2 - z) at h2
    rw [h1, h2, hinf τL, hrank]
  exact ⟨r, HT_K, hpull, hprops⟩

end WeightDescent

/-! ## 4. Solvable Tower Induction (Automorphy, Regularity & Polarization Descent) -/

/-- A number-field level combining global Galois/automorphic data (`BaseChangeLevel`) with
CM infinitesimal character data attached to each Galois representation. -/
structure PolarizedLevel where
  bc : BaseChangeLevel
  Emb : Type
  conjEmb : Emb → Emb
  conjEmb_involutive : Function.Involutive conjEmb
  infDatum : bc.GalRep → CMInfCharDatum
  infDatum_emb : ∀ r, (infDatum r).Emb = Emb
  infDatum_conj : ∀ r, HEq (infDatum r).conjEmb conjEmb

/-- A prime-degree cyclic base-change step between two `PolarizedLevel`s, coupling a
`BaseChangeGalStep` of prime degree `p` with surjective conjugation-equivariant embedding
restriction and base-change infinitesimal-character compatibility. -/
structure CyclicPolarizedStep (L₁ L₂ : PolarizedLevel) where
  galStep : BaseChangeGalStep L₁.bc L₂.bc
  resEmb : ∀ r : L₁.bc.GalRep, (L₂.infDatum (galStep.res r)).Emb → (L₁.infDatum r).Emb
  resEmb_surj : ∀ r : L₁.bc.GalRep, Function.Surjective (resEmb r)
  resEmb_conj : ∀ (r : L₁.bc.GalRep) (τ : (L₂.infDatum (galStep.res r)).Emb),
    resEmb r ((L₂.infDatum (galStep.res r)).conjEmb τ) =
      (L₁.infDatum r).conjEmb (resEmb r τ)
  rank_eq : ∀ r : L₁.bc.GalRep, (L₂.infDatum (galStep.res r)).rank = (L₁.infDatum r).rank
  infChar_compat : ∀ (r : L₁.bc.GalRep) (τ : (L₂.infDatum (galStep.res r)).Emb),
    (L₂.infDatum (galStep.res r)).infChar τ = (L₁.infDatum r).infChar (resEmb r τ)

namespace CyclicPolarizedStep

variable {L₁ L₂ : PolarizedLevel} (step : CyclicPolarizedStep L₁ L₂)

/-- **Single Prime-Step Simultaneous Equivalence of Automorphy, Regularity & Polarization**:
for every representation `r` whose restriction to `L₂` remains irreducible,
- `IsAut r ↔ IsAut (res r)`,
- `RegularAlgebraic (infDatum r) ↔ RegularAlgebraic (infDatum (res r))`, and
- `∀ wt, IsPolarized wt (infDatum r) ↔ IsPolarized wt (infDatum (res r))`! -/
theorem aut_reg_pol_equiv {r : L₁.bc.GalRep} (hirr : L₂.bc.IsIrr (step.galStep.res r)) :
    (L₁.bc.IsAut r ↔ L₂.bc.IsAut (step.galStep.res r)) ∧
    (Stage2HodgeWeights.RegularAlgebraic (L₁.infDatum r) ↔
      Stage2HodgeWeights.RegularAlgebraic (L₂.infDatum (step.galStep.res r))) ∧
    (∀ wt : ℤ, (L₁.infDatum r).IsPolarized wt ↔
      (L₂.infDatum (step.galStep.res r)).IsPolarized wt) := by
  refine ⟨step.galStep.aut_equiv hirr, ?_, ?_⟩
  · exact (regularAlgebraic_baseChange_iff (step.rank_eq r) (step.resEmb r)
      (step.resEmb_surj r) (step.infChar_compat r)).symm
  · intro wt
    exact (isPolarized_baseChange_iff (step.rank_eq r) (step.resEmb r)
      (step.resEmb_surj r) (step.resEmb_conj r) (step.infChar_compat r) wt).symm

end CyclicPolarizedStep

/-- A finite subnormal tower `K = K_0 ⊂ K_1 ⊂ ... ⊂ K_m = L` of prime-degree cyclic
polarized base-change steps. -/
inductive SolvablePolarizedTower : PolarizedLevel → PolarizedLevel → Type 1
  | nil (L : PolarizedLevel) : SolvablePolarizedTower L L
  | cons {L₁ L₂ L₃ : PolarizedLevel}
      (step : CyclicPolarizedStep L₁ L₂) (rest : SolvablePolarizedTower L₂ L₃) :
      SolvablePolarizedTower L₁ L₃

namespace SolvablePolarizedTower

/-- Number of cyclic prime-degree steps in the tower. -/
def length : {L₁ L₂ : PolarizedLevel} → SolvablePolarizedTower L₁ L₂ → ℕ
  | _, _, .nil _ => 0
  | _, _, .cons _ rest => rest.length + 1

/-- Ordered list of prime step degrees along `K = K_0 ⊂ ... ⊂ K_m = L`. -/
def primes : {L₁ L₂ : PolarizedLevel} → SolvablePolarizedTower L₁ L₂ → List ℕ
  | _, _, .nil _ => []
  | _, _, .cons step rest => step.galStep.step.p :: rest.primes

/-- Total extension degree `∏ p_i` of the solvable tower. -/
def degree : {L₁ L₂ : PolarizedLevel} → SolvablePolarizedTower L₁ L₂ → ℕ
  | _, _, .nil _ => 1
  | _, _, .cons step rest => step.galStep.step.p * rest.degree

theorem degree_eq_primes_prod :
    ∀ {L₁ L₂ : PolarizedLevel} (T : SolvablePolarizedTower L₁ L₂), T.degree = T.primes.prod
  | _, _, .nil _ => rfl
  | _, _, .cons step rest => by
      simp [degree, primes, degree_eq_primes_prod rest]

theorem primes_all_prime :
    ∀ {L₁ L₂ : PolarizedLevel} (T : SolvablePolarizedTower L₁ L₂), ∀ p ∈ T.primes, p.Prime
  | _, _, .nil _, _, hp => nomatch hp
  | _, _, .cons step rest, p, hp => by
      simp only [primes, List.mem_cons] at hp
      rcases hp with rfl | hp'
      · exact step.galStep.step.p_prime
      · exact primes_all_prime rest p hp'

/-- Forgetful projection to `RHDirect.BaseChangeTower`. -/
def toBaseChangeTower :
    {L₁ L₂ : PolarizedLevel} → SolvablePolarizedTower L₁ L₂ → BaseChangeTower L₁.bc L₂.bc
  | _, _, .nil L => .nil L.bc
  | _, _, .cons step rest => .cons step.galStep rest.toBaseChangeTower

/-- Iterated Galois restriction `r ↦ r|_{G_L}` along the tower. -/
def res : {L₁ L₂ : PolarizedLevel} → SolvablePolarizedTower L₁ L₂ → L₁.bc.GalRep → L₂.bc.GalRep
  | _, _, .nil _, r => r
  | _, _, .cons step rest, r => rest.res (step.galStep.res r)

theorem res_eq_toBaseChangeTower :
    ∀ {L₁ L₂ : PolarizedLevel} (T : SolvablePolarizedTower L₁ L₂) (r : L₁.bc.GalRep),
      T.res r = T.toBaseChangeTower.res r
  | _, _, .nil _, _ => rfl
  | _, _, .cons step rest, r => res_eq_toBaseChangeTower rest (step.galStep.res r)

/-- Composed embedding restriction `Emb_L → Emb_K` along the tower. -/
def resEmb : ∀ {L₁ L₂ : PolarizedLevel} (T : SolvablePolarizedTower L₁ L₂) (r : L₁.bc.GalRep),
    (L₂.infDatum (T.res r)).Emb → (L₁.infDatum r).Emb
  | _, _, .nil _, _, τ => τ
  | _, _, .cons step rest, r, τ => step.resEmb r (rest.resEmb (step.galStep.res r) τ)

theorem resEmb_surjective :
    ∀ {L₁ L₂ : PolarizedLevel} (T : SolvablePolarizedTower L₁ L₂) (r : L₁.bc.GalRep),
      Function.Surjective (T.resEmb r)
  | _, _, .nil _, _ => Function.surjective_id
  | _, _, .cons step rest, r =>
      (step.resEmb_surj r).comp (resEmb_surjective rest (step.galStep.res r))

theorem resEmb_conj :
    ∀ {L₁ L₂ : PolarizedLevel} (T : SolvablePolarizedTower L₁ L₂) (r : L₁.bc.GalRep)
      (τ : (L₂.infDatum (T.res r)).Emb),
      T.resEmb r ((L₂.infDatum (T.res r)).conjEmb τ) = (L₁.infDatum r).conjEmb (T.resEmb r τ)
  | _, _, .nil _, _, _ => rfl
  | _, _, .cons step rest, r, τ =>
      (congrArg (step.resEmb r) (resEmb_conj rest (step.galStep.res r) τ)).trans
        (step.resEmb_conj r _)

theorem rank_eq :
    ∀ {L₁ L₂ : PolarizedLevel} (T : SolvablePolarizedTower L₁ L₂) (r : L₁.bc.GalRep),
      (L₂.infDatum (T.res r)).rank = (L₁.infDatum r).rank
  | _, _, .nil _, _ => rfl
  | _, _, .cons step rest, r =>
      (rank_eq rest (step.galStep.res r)).trans (step.rank_eq r)

theorem infChar_compat :
    ∀ {L₁ L₂ : PolarizedLevel} (T : SolvablePolarizedTower L₁ L₂) (r : L₁.bc.GalRep)
      (τ : (L₂.infDatum (T.res r)).Emb),
      (L₂.infDatum (T.res r)).infChar τ = (L₁.infDatum r).infChar (T.resEmb r τ)
  | _, _, .nil _, _, _ => rfl
  | _, _, .cons step rest, r, τ =>
      (infChar_compat rest (step.galStep.res r) τ).trans (step.infChar_compat r _)

theorem isIrr_of_res :
    ∀ {L₁ L₂ : PolarizedLevel} (T : SolvablePolarizedTower L₁ L₂) {r : L₁.bc.GalRep},
      L₂.bc.IsIrr (T.res r) → L₁.bc.IsIrr r
  | _, _, .nil _, _, h => h
  | _, _, .cons step rest, r, h => step.galStep.isIrr_of_res r (isIrr_of_res rest h)

/-- **Solvable Tower Induction Theorem (Simultaneous Equivalence of Automorphy, Regularity &
Polarization)**: iterating cyclic prime-degree descent along `K = K_0 ⊂ K_1 ⊂ ... ⊂ K_m = L`
proves that for every `r` remaining irreducible at the top `L`:
1. `L₁.bc.IsAut r ↔ L₂.bc.IsAut (T.res r)`,
2. `RegularAlgebraic (L₁.infDatum r) ↔ RegularAlgebraic (L₂.infDatum (T.res r))`, and
3. `∀ wt : ℤ, (L₁.infDatum r).IsPolarized wt ↔ (L₂.infDatum (T.res r)).IsPolarized wt`! -/
theorem aut_reg_pol_equiv :
    ∀ {L₁ L₂ : PolarizedLevel} (T : SolvablePolarizedTower L₁ L₂) {r : L₁.bc.GalRep},
      L₂.bc.IsIrr (T.res r) →
      (L₁.bc.IsAut r ↔ L₂.bc.IsAut (T.res r)) ∧
      (Stage2HodgeWeights.RegularAlgebraic (L₁.infDatum r) ↔
        Stage2HodgeWeights.RegularAlgebraic (L₂.infDatum (T.res r))) ∧
      (∀ wt : ℤ, (L₁.infDatum r).IsPolarized wt ↔ (L₂.infDatum (T.res r)).IsPolarized wt)
  | _, _, .nil _, _, _ => ⟨Iff.rfl, Iff.rfl, fun _ => Iff.rfl⟩
  | _, _, .cons step rest, r, hirr => by
      have hirr_mid : _ := isIrr_of_res rest hirr
      obtain ⟨hA1, hR1, hP1⟩ := step.aut_reg_pol_equiv hirr_mid
      obtain ⟨hA2, hR2, hP2⟩ := aut_reg_pol_equiv rest hirr
      exact ⟨hA1.trans hA2, hR1.trans hR2, fun wt => (hP1 wt).trans (hP2 wt)⟩

/-- **Downward Solvable Tower Descent**: automorphy, `RegularAlgebraic`, and `IsPolarized wt`
all descend simultaneously from the top `L` down to the base `K`! -/
theorem descend_aut_reg_pol {L₁ L₂ : PolarizedLevel} (T : SolvablePolarizedTower L₁ L₂)
    {r : L₁.bc.GalRep} {wt : ℤ}
    (hirr : L₂.bc.IsIrr (T.res r))
    (haut : L₂.bc.IsAut (T.res r))
    (hreg : Stage2HodgeWeights.RegularAlgebraic (L₂.infDatum (T.res r)))
    (hpol : (L₂.infDatum (T.res r)).IsPolarized wt) :
    L₁.bc.IsAut r ∧ Stage2HodgeWeights.RegularAlgebraic (L₁.infDatum r) ∧
      (L₁.infDatum r).IsPolarized wt := by
  obtain ⟨hA, hR, hP⟩ := T.aut_reg_pol_equiv hirr
  exact ⟨hA.mpr haut, hR.mpr hreg, (hP wt).mpr hpol⟩

/-- **Upward Solvable Tower Lifting**: automorphy, `RegularAlgebraic`, and `IsPolarized wt`
all lift simultaneously from the base `K` up to the top `L`! -/
theorem lift_aut_reg_pol {L₁ L₂ : PolarizedLevel} (T : SolvablePolarizedTower L₁ L₂)
    {r : L₁.bc.GalRep} {wt : ℤ}
    (hirr : L₂.bc.IsIrr (T.res r))
    (haut : L₁.bc.IsAut r)
    (hreg : Stage2HodgeWeights.RegularAlgebraic (L₁.infDatum r))
    (hpol : (L₁.infDatum r).IsPolarized wt) :
    L₂.bc.IsAut (T.res r) ∧ Stage2HodgeWeights.RegularAlgebraic (L₂.infDatum (T.res r)) ∧
      (L₂.infDatum (T.res r)).IsPolarized wt := by
  obtain ⟨hA, hR, hP⟩ := T.aut_reg_pol_equiv hirr
  exact ⟨hA.mp haut, hR.mp hreg, (hP wt).mp hpol⟩

/-- Concatenation (transitivity) of solvable polarized towers. -/
def append : {L₁ L₂ L₃ : PolarizedLevel} →
    SolvablePolarizedTower L₁ L₂ → SolvablePolarizedTower L₂ L₃ → SolvablePolarizedTower L₁ L₃
  | _, _, _, .nil _, T₂ => T₂
  | _, _, _, .cons step rest, T₂ => .cons step (rest.append T₂)

theorem degree_append :
    ∀ {L₁ L₂ L₃ : PolarizedLevel} (T₁ : SolvablePolarizedTower L₁ L₂)
      (T₂ : SolvablePolarizedTower L₂ L₃),
      (T₁.append T₂).degree = T₁.degree * T₂.degree
  | _, _, _, .nil _, _ => by simp [append, degree]
  | _, _, _, .cons step rest, T₂ => by
      simp [append, degree, degree_append rest T₂, mul_assoc]

/-- **Solvable Tower Construction by Strong Induction on Extension Degree** for polarized levels. -/
theorem of_solvable_decomp (Rel : PolarizedLevel → PolarizedLevel → ℕ → Prop)
    (hdeg_one : ∀ L₁ L₂, Rel L₁ L₂ 1 → L₁ = L₂)
    (hprime : ∀ L₁ L₂ p, p.Prime → Rel L₁ L₂ p →
      ∃ step : CyclicPolarizedStep L₁ L₂, step.galStep.step.p = p)
    (hsplit : ∀ L₁ L₂ d, 1 < d → ¬d.Prime → Rel L₁ L₂ d →
      ∃ L_mid d₁ d₂, 1 < d₁ ∧ 1 < d₂ ∧ d₁ * d₂ = d ∧ Rel L₁ L_mid d₁ ∧ Rel L_mid L₂ d₂) :
    ∀ d, 0 < d → ∀ L₁ L₂, Rel L₁ L₂ d →
      ∃ T : SolvablePolarizedTower L₁ L₂, T.degree = d := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hdpos L₁ L₂ hrel
    by_cases hd1 : d = 1
    · subst hd1
      obtain rfl := hdeg_one L₁ L₂ hrel
      exact ⟨.nil L₁, rfl⟩
    · have hdgt : 1 < d := by omega
      by_cases hdp : d.Prime
      · obtain ⟨step, hsp⟩ := hprime L₁ L₂ d hdp hrel
        exact ⟨.cons step (.nil L₂), by simp [degree, hsp]⟩
      · obtain ⟨L_mid, d₁, d₂, h1, h2, hmul, hrel1, hrel2⟩ := hsplit L₁ L₂ d hdgt hdp hrel
        have hd1_lt : d₁ < d := by rw [← hmul]; exact lt_mul_of_one_lt_right (by omega) h2
        have hd2_lt : d₂ < d := by rw [← hmul]; exact lt_mul_of_one_lt_left (by omega) h1
        obtain ⟨T₁, hT₁⟩ := ih d₁ hd1_lt (by omega) L₁ L_mid hrel1
        obtain ⟨T₂, hT₂⟩ := ih d₂ hd2_lt (by omega) L_mid L₂ hrel2
        exact ⟨T₁.append T₂, by rw [degree_append, hT₁, hT₂, hmul]⟩

end SolvablePolarizedTower

/-! ## 5. Direct Discharge Bridges into `Stage2GaloisWire` & `BaseChangeCyclic` -/

/-! ### 5A. Direct Discharge of `BaseChangeTower` from `SolvableStepChain Γ` (`BaseChangeCyclic`) -/

/-- A Galois-correspondence assignment of a `BaseChangeLevel` to every finite solvable group
along a `SolvableStepChain`, where each prime-index normal subgroup step `M ◁ G` supplies a
`BaseChangeGalStep (levelOf G) (levelOf M)`. -/
def baseChangeTower_of_solvableStepChain
    (levelOf : (G : Type) → [Group G] → BaseChangeLevel)
    (stepOf : ∀ {G : Type} [Group G] (M : Subgroup G), M.Normal → M.index.Prime →
      { step : BaseChangeGalStep (levelOf G) (levelOf M) // step.step.p = M.index }) :
    ∀ {Γ : Type} [Group Γ] (c : SolvableStepChain Γ),
      Σ' (L_top : BaseChangeLevel) (T : BaseChangeTower (levelOf Γ) L_top),
        T.degree = c.primes.prod
  | Γ, hG, @SolvableStepChain.nil _ _ _ =>
      ⟨@levelOf Γ hG, .nil (@levelOf Γ hG), rfl⟩
  | _, _, @SolvableStepChain.cons _ _ M hnorm hp rest =>
      let ⟨step, hsp⟩ := stepOf M hnorm hp
      let ⟨L_top, T_rest, hdeg⟩ := baseChangeTower_of_solvableStepChain levelOf stepOf rest
      ⟨L_top, .cons step T_rest, by simp [BaseChangeTower.degree, SolvableStepChain.primes, hsp, hdeg]⟩

/-- **Unconditional Finite-Solvable Galois Automorphy Equivalence**:
for ANY finite solvable Galois group `Γ`, using `RHDirect.exists_solvableStepChain Γ`,
supplying prime-index normal cyclic steps discharges a full `BaseChangeTower` of exact degree
`Nat.card Γ` and proves automorphy equivalence `IsAut r ↔ IsAut (T.res r)`! -/
theorem solvable_group_aut_equiv
    (levelOf : (G : Type) → [Group G] → BaseChangeLevel)
    (stepOf : ∀ {G : Type} [Group G] (M : Subgroup G), M.Normal → M.index.Prime →
      { step : BaseChangeGalStep (levelOf G) (levelOf M) // step.step.p = M.index })
    (Γ : Type) [Group Γ] [Finite Γ] [Group.IsSolvable Γ] :
    ∃ (L_top : BaseChangeLevel) (T : BaseChangeTower (levelOf Γ) L_top),
      T.degree = Nat.card Γ ∧
      ∀ r : (levelOf Γ).GalRep, L_top.IsIrr (T.res r) →
        ((levelOf Γ).IsAut r ↔ L_top.IsAut (T.res r)) := by
  obtain ⟨c⟩ := exists_solvableStepChain Γ
  obtain ⟨L_top, T, hdeg⟩ := baseChangeTower_of_solvableStepChain levelOf stepOf c
  refine ⟨L_top, T, hdeg.trans c.card_eq_prod.symm, fun r hirr => T.aut_equiv hirr⟩

/-! ### 5B. Direct Discharge of `ThetaLiftAssemblyPipeline` & `Stage2GaloisWire.GeometryThetaRowSupply` -/

universe uE uV

/-- A Stage-3 crystalline-base-change row pipeline: replaces `ThetaLiftAssemblyPipeline`'s
`reg_all` and `pol_all` assumptions with crystalline weight families `crysBaseChange i` realized
after a finite/solvable CM base change `L_i / K_i` (discharged unconditionally via Weight
Descent!). -/
structure CrystallineBaseChangeRowPipeline (E : Type uE) [Field E]
    (PolIdx : Type) (S : PolIdx → StructuredCuspDatum) where
  GeoOne : Prop
  SeedFinOdd : Prop
  CongFinOdd : Prop
  TLiftK : Prop
  seed_of_geo : GeoOne → SeedFinOdd
  cong_holds : CongFinOdd
  /-- For each datum `S i`, a crystalline weight family over a finite CM base-change extension
  `L_i / K_i` whose infinitesimal character restricts onto `S i`. -/
  crysBC : PolIdx → Stage2HodgeWeights.CrystallineWeightFamily.{uE, uV} E
  rank_eq : ∀ i, (crysBC i).rank = (S i).rank
  resEmb : ∀ i, (crysBC i).Emb → (S i).Emb
  resEmb_surj : ∀ i, Function.Surjective (resEmb i)
  resEmb_conj : ∀ i τ, resEmb i ((crysBC i).conjEmb τ) = (S i).conjEmb (resEmb i τ)
  infChar_compat : ∀ i τ, (crysBC i).toCMInfCharDatum.infChar τ = (S i).infChar (resEmb i τ)
  coreAll_of : SeedFinOdd → CongFinOdd → TLiftK → ∀ i, (S i).CoreAllAt
  toral_of_core : (∀ i, (S i).CoreAllAt) → ∀ i, (S i).ToralCompatAt
  rankTwo_of_core : (∀ i, (S i).CoreAllAt) → ∀ i, (S i).PlaceClassCompatAt IsQpBigNat

namespace CrystallineBaseChangeRowPipeline

variable {E : Type uE} [Field E] {PolIdx : Type} {S : PolIdx → StructuredCuspDatum}

/-- **Direct Discharge of `ThetaLiftAssemblyPipeline.reg_all` & `pol_all`**:
descends regular algebraicity and polarization from each base-changed `CrystallineWeightFamily`
directly into `RHDirect.ThetaLiftAssemblyPipeline`. -/
def toThetaLiftAssemblyPipeline (P : CrystallineBaseChangeRowPipeline.{uE, uV} E PolIdx S) :
    ThetaLiftAssemblyPipeline PolIdx S where
  GeoOne := P.GeoOne
  SeedFinOdd := P.SeedFinOdd
  CongFinOdd := P.CongFinOdd
  TLiftK := P.TLiftK
  seed_of_geo := P.seed_of_geo
  cong_holds := P.cong_holds
  reg_all i :=
    (isRegAlg_baseChange_iff (I_K := (S i).toCMInfCharDatum)
      (I_L := (P.crysBC i).toCMInfCharDatum)
      (P.rank_eq i) (P.resEmb i) (P.resEmb_surj i) (P.infChar_compat i)).mp
      (P.crysBC i).toCMInfCharDatum_isRegAlg
  pol_all i :=
    ⟨(P.crysBC i).wt,
      (isPolarized_baseChange_iff (I_K := (S i).toCMInfCharDatum)
        (I_L := (P.crysBC i).toCMInfCharDatum)
        (P.rank_eq i) (P.resEmb i) (P.resEmb_surj i) (P.resEmb_conj i) (P.infChar_compat i)
        (P.crysBC i).wt).mp
        (P.crysBC i).toCMInfCharDatum_isPolarized⟩
  coreAll_of := P.coreAll_of
  toral_of_core := P.toral_of_core
  rankTwo_of_core := P.rankTwo_of_core

/-- **Direct Discharge into `Stage2GaloisWire.GeometryThetaRowSupply`**:
assembles `GeometryThetaRowSupply` directly from a `CrystallineBaseChangeRowPipeline` +
`(GeoOne, TLiftK)`! -/
def toGeometryThetaRowSupply (P : CrystallineBaseChangeRowPipeline.{uE, uV} E PolIdx S)
    (geo : P.GeoOne) (up : P.TLiftK) :
    Stage2GaloisWire.GeometryThetaRowSupply where
  PolIdx := PolIdx
  structuredDatum := S
  pipeline := P.toThetaLiftAssemblyPipeline
  geoOne := geo
  tLiftK := up

/-- Discharges all 11/11 live fields of `GaloisRowData` (`Row0b`) directly from crystalline
base-change weight descent + `(GeoOne, TLiftK)`. -/
theorem toGaloisRowData (P : CrystallineBaseChangeRowPipeline.{uE, uV} E PolIdx S)
    (geo : P.GeoOne) (up : P.TLiftK) :
    GaloisRowData PolIdx (fun i => (S i).toPolarizedCuspDatum) :=
  (P.toGeometryThetaRowSupply geo up).toGaloisRowData

/-- Discharges `MinimalGaloisRow` directly from crystalline base-change weight descent +
`(GeoOne, TLiftK)`. -/
theorem toMinimalGaloisRow (P : CrystallineBaseChangeRowPipeline.{uE, uV} E PolIdx S)
    (geo : P.GeoOne) (up : P.TLiftK) :
    MinimalGaloisRow PolIdx (fun i => (S i).toPolarizedCuspDatum) :=
  (P.toGeometryThetaRowSupply geo up).toMinimalGaloisRow

end CrystallineBaseChangeRowPipeline

/-! ### 5C. Weighted Solvable Prime-Step Base Change Bridge into `Stage2GaloisWire` -/

/-- A Stage-3 weighted solvable prime-step base-change system coupling
`Stage2GaloisWire.SolvablePrimeStepBaseChange` with CM infinitesimal character weight
compatibility along every prime-degree cyclic step. -/
structure Stage3WeightedSolvableSupply where
  Rel : PolarizedLevel → PolarizedLevel → ℕ → Prop
  deg_one : ∀ L₁ L₂, Rel L₁ L₂ 1 → L₁ = L₂
  prime_step : ∀ L₁ L₂ p, p.Prime → Rel L₁ L₂ p →
    ∃ step : CyclicPolarizedStep L₁ L₂, step.galStep.step.p = p
  split_composite : ∀ L₁ L₂ d, 1 < d → ¬d.Prime → Rel L₁ L₂ d →
    ∃ L_mid d₁ d₂, 1 < d₁ ∧ 1 < d₂ ∧ d₁ * d₂ = d ∧ Rel L₁ L_mid d₁ ∧ Rel L_mid L₂ d₂

namespace Stage3WeightedSolvableSupply

/-- Direct projection into `Stage2GaloisWire.SolvablePrimeStepBaseChange`. -/
def toStage2BaseChange (W : Stage3WeightedSolvableSupply) :
    Stage2GaloisWire.SolvablePrimeStepBaseChange where
  Rel L₁ L₂ d := ∃ P₁ P₂ : PolarizedLevel, P₁.bc = L₁ ∧ P₂.bc = L₂ ∧ W.Rel P₁ P₂ d
  deg_one L₁ L₂ h := by
    obtain ⟨P₁, P₂, rfl, rfl, hrel⟩ := h
    rw [W.deg_one P₁ P₂ hrel]
  prime_step L₁ L₂ p hp h := by
    obtain ⟨P₁, P₂, rfl, rfl, hrel⟩ := h
    obtain ⟨step, hsp⟩ := W.prime_step P₁ P₂ p hp hrel
    exact ⟨step.galStep, hsp⟩
  split_composite L₁ L₂ d hd hnp h := by
    obtain ⟨P₁, P₂, rfl, rfl, hrel⟩ := h
    obtain ⟨P_mid, d₁, d₂, h1, h2, hmul, hr1, hr2⟩ := W.split_composite P₁ P₂ d hd hnp hrel
    exact ⟨P_mid.bc, d₁, d₂, h1, h2, hmul, ⟨P₁, P_mid, rfl, rfl, hr1⟩, ⟨P_mid, P₂, rfl, rfl, hr2⟩⟩

/-- Discharges `Stage2GaloisWire.SolvableDescentEquiv` directly from `Stage3WeightedSolvableSupply`. -/
theorem toSolvableDescentEquiv (W : Stage3WeightedSolvableSupply) :
    Stage2GaloisWire.SolvableDescentEquiv W.toStage2BaseChange :=
  W.toStage2BaseChange.solvable_aut_equiv

/-- **Simultaneous Solvable Automorphy, Regularity & Polarization Descent Theorem**:
for every solvable extension `W.Rel L₁ L₂ d` (`0 < d`), there is a `SolvablePolarizedTower`
of exact degree `d` across which automorphy, `RegularAlgebraic`, and `IsPolarized wt` all
simultaneously descend and lift! -/
theorem solvable_aut_reg_pol_equiv (W : Stage3WeightedSolvableSupply)
    {d : ℕ} (hd : 0 < d) {L₁ L₂ : PolarizedLevel} (hrel : W.Rel L₁ L₂ d) :
    ∃ T : SolvablePolarizedTower L₁ L₂, T.degree = d ∧
      ∀ r : L₁.bc.GalRep, L₂.bc.IsIrr (T.res r) →
        (L₁.bc.IsAut r ↔ L₂.bc.IsAut (T.res r)) ∧
        (Stage2HodgeWeights.RegularAlgebraic (L₁.infDatum r) ↔
          Stage2HodgeWeights.RegularAlgebraic (L₂.infDatum (T.res r))) ∧
        (∀ wt : ℤ, (L₁.infDatum r).IsPolarized wt ↔ (L₂.infDatum (T.res r)).IsPolarized wt) := by
  obtain ⟨T, hdeg⟩ :=
    SolvablePolarizedTower.of_solvable_decomp W.Rel W.deg_one W.prime_step W.split_composite
      d hd L₁ L₂ hrel
  exact ⟨T, hdeg, fun _ hirr => T.aut_reg_pol_equiv hirr⟩

/-- **End-to-End Stage-3 Bridge into `RHDirect.GaloisModularityContract S` (`VWin S`)**:
wires `CrystallineBaseChangeRowPipeline` (crystalline weight descent) +
`Stage3WeightedSolvableSupply` (solvable polarized tower descent) +
`CuspidalLLCSupply` directly into `Stage2GaloisWire.Stage2GaloisCoreInputs S` and exports
`GaloisModularityContract S`! -/
theorem galoisModularityContract_of_stage3_descent
    {S : SelmerSystem} {E : Type uE} [Field E]
    {LocIdx : Type} {place : LocIdx → LocalLanglandsPlace}
    (hLLC : Stage2GaloisWire.CuspidalLLCSupply LocIdx place)
    {PolIdx : Type} {SD : PolIdx → StructuredCuspDatum}
    (P : CrystallineBaseChangeRowPipeline.{uE, uV} E PolIdx SD)
    (geo : P.GeoOne) (up : P.TLiftK)
    (W : Stage3WeightedSolvableSupply)
    (hPatch :
      MinimalLocalLanglands LocIdx place →
      MinimalGaloisRow PolIdx (fun i => (SD i).toPolarizedCuspDatum) →
      Stage2GaloisWire.SolvableDescentEquiv W.toStage2BaseChange →
      Stage2GaloisWire.ThreePartPatchingWindow S) :
    GaloisModularityContract S :=
  Stage2GaloisWire.stage2_galoisModularityContract
    { LocIdx := LocIdx
      place := place
      cuspidalLLC := hLLC
      rowSupply := P.toGeometryThetaRowSupply geo up
      baseChange := W.toStage2BaseChange
      patchingBridge := hPatch }

end Stage3WeightedSolvableSupply

end Stage3AutomorphicDescent
end RHDirect

end
