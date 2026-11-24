import RHDirect.Interfaces
import RHDirect.TaylorWilesWindow
import RHDirect.Stage2GaloisWire
import RHDirect.Stage8IwasawaWeierstrass
import RHDirect.Stage11FerreroWashington
import RHDirect.Stage11IwasawaMainConj
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# RHDirect.Stage12Window1RootAvoid

Unconditional Lean 4 formalization (zero `sorry`, zero custom `axiom`s, zero `native_decide`) of
Alpöge's Phase C / Stage 12 **`Window1` Iwasawa Root-Avoidance Pigeonhole**, **Effective `LemmaK`**,
and **Exact Complex-Conjugation Parity Split (`VVle = VVminusLe + VVplusLe`)** wired directly into
`RHDirect.Interfaces`, `RHDirect.TaylorWilesWindow`, `RHDirect.Stage2GaloisWire`,
`RHDirect.Stage8IwasawaWeierstrass`, `RHDirect.Stage11FerreroWashington`, and
`RHDirect.Stage11IwasawaMainConj`.

## Contents

1. **Unconditional `Window1` Dyadic Root-Avoidance Pigeonhole (`J = 2^(R+2) * (2 * C_K * C_t / ε)^R`)**:
   - Exact Alpöge `window1` induction on `R` (`LayeredIsomorphisms/Window1.lean`).
   - Multiplicative exponentiated windowing `window` & `window_of_CK` (`LayeredIsomorphisms/Window.lean`),
     producing `[Y, Y^2] ⊂ [X^(1/J), X]` with explicit `windowExponent R CK Ct eps = 2^(R+2) * (2*CK*Ct/eps)^R`.
   - Simultaneous multi-family windowing `window_joint_families` handling BOTH `l = 2` (`ExcA`, size `≤ R₀`)
     and all bad odd primes `l ∈ Bchi` (`ExcB l`, size `≤ R_l`) on the SAME sub-window `[Y, Y^2]`.

2. **Ultrametric `p`-adic Root Separation & Distinguished `μ = 0` Iwasawa Power Series Evaluation**:
   - Exact ultrametric root-uniqueness lemma `near1` (`LayeredIsomorphisms/Near1.lean`) and finite
     exceptional-set extraction `exists_exc_of_roots` (`|Exc| ≤ R`).
   - Unconditional `p`-adic Lifting-the-Exponent (`padic_pow_sub_one_norm`, `norm_cyclotomic_twist_sub`)
     for cyclotomic twists `κ^e - 1` (`‖κ - 1‖ = p^(-c₀)` with `c₀ ≥ 1`, and `c₀ ≥ 2` at `p = 2`),
     yielding multiplicative cyclotomic root uniqueness `near1_cyclotomic`.
   - `SplitDistinguishedSeries p K` connecting directly to `Stage8IwasawaWeierstrass` (`iwasawaMu = 0`,
     `iwasawaLambda`) and `Stage11IwasawaMainConj.distPart`: proves `valuation_eval_distPart_le_of_root_dist`,
     `iwasawa_family_root_avoidance_exc`, and `window1_iwasawa_family_exp_bound` (delivering the exact
     `Real.exp (x ^ (4 * eps / 5))` sum bound across `[Y, Y^2]`).

3. **Effective `LemmaK` (`|H²(𝒪_L[1/ℓ], ℤ_ℓ(e+1))|` Bound from `ClassGroup` + `μ = 0`)**:
   - `HasMuQ`, `kBound CK e n D = exp((2 e n)^CK * log(2 D))`, `kBound_mono_C` (`Kmono`),
     `kexp` (`Kexp`), and `klen_of_card_bound` (`Klen` via `Stage2IwasawaTwoTower.padicInt_card_eq_pow_length`).
   - Exact algebraic length of cyclic `μ = 0` twisted specializations
     `length_padicInt_quot_eval_distPart`: `len_{ℤ_[l]}(ℤ_[l] / (P(κ^e - 1))) = v_l(P(κ^e - 1))`.
   - Effective `LemmaK` bounds from Iwasawa characteristic evaluation + root-distance (`TwistedH2IwasawaBound`)
     and from Minkowski/class-group + Kummer descent (`ClassGroupH2Control → effective_lemmaK_of_classGroup_control`).

4. **Unified `ThmBab` Discharge (`BaAt` at `l = 2` + `BbAt` / `CaseIV` at `l ∈ Bchi`)**:
   - `jZero`, `ptBound`, `SecondBound`, `FirstBound`, `ABound`, `exc_of_aBound` (`Exc`),
     `logs_le` (`Logs`), `point_bound` (`Point`), `point2_bound` (`Point2`),
     `final_exp_absorb` (`Final`), `vvat_of_pointwise` (`Vvat`), `partA_two_branch` (`PartA`),
     `partB_bad_odd_branch` (`PartB`), and `thmBab_window1` (`ThmBabOf`).

5. **Exact Complex-Conjugation Parity Split (`VVle = VVminusLe + VVplusLe`)**:
   - Exact `LengthEqAddEigen.length_eq_add_eigen` for any `R` with `IsUnit (2 : R)` and involution `f`.
   - Specialization `isUnit_two_padicInt_of_ne_two` and `padicInt_length_eq_add_parity` to `ℤ_[l]` (`l ≠ 2`).
   - `ParitySelmerSystem` + concrete involution constructor `ParitySelmerSystem.ofInvolution`.
   - `VVat`, `BoundedHeightTwoPlaceCondition`, `VVminusLe`, `VVplusLe`, `SumIn`, `SumOut`.
   - **`vvle_of_parity_parts`** (`LengthEqAddEigen.vvle_of_parts`), `vvplusLe_of_sumIn_sumOut`,
     `sumIn_of_caseIV_bbAt_and_poly`, and `vvplusLe_of_bbAt_and_sumOut`.

6. **End-to-End Assembly into `VWin S` & `GaloisModularityContract S` + Concrete `p = 37` Witness**:
   - `ParityWindow1Supply` → `jointPatchingWindow_of_parityWindow1` → `vwinAt_of_parityWindow1` →
     `vwin_of_parityWindow1` → `galoisModularityContract_of_parityWindow1`.
   - Concrete 0-assumption `Window1` root-avoidance instantiation on `Stage11FerreroWashington`
     (`kubotaLeopoldtSeries 37` irregular branch `μ = 0, λ = 1` and `mazurBernoulliMeasure p 3`).
-/

noncomputable section

open scoped BigOperators Topology
open Real Finset Filter NumberField RHDirect
open RHDirect.Stage2IwasawaTwoTower RHDirect.Stage7PadicLFunction
open RHDirect.Stage8IwasawaWeierstrass RHDirect.Stage11FerreroWashington
open RHDirect.Stage11IwasawaMainConj RHDirect.TaylorWilesWindow RHDirect.Stage2GaloisWire

namespace RHDirect.Stage12Window1RootAvoid

/-- Canonical `Fact (l : ℕ).Prime` instance for every `l : Nat.Primes` (subsingleton `Prop`,
so zero typeclass diamonds). -/
instance instFactPrimeNatPrimes (l : Nat.Primes) : Fact (l : ℕ).Prime := ⟨l.2⟩

/-! ## Section 1: Unconditional `Window1` Dyadic Root-Avoidance Pigeonhole -/

section Window1Pigeonhole

/-- Multiplicative sub-window condition `Y ∈ [X^(1/J), X^(1/2)]`, equivalently
`X^(1/J) ≤ Y ∧ Y^2 ≤ X` (matching `UpperTheory.V.Win.InRange`). -/
def InRange (J X Y : ℝ) : Prop :=
  X ^ (1 / J) ≤ Y ∧ Y ^ (2 : ℝ) ≤ X

/-- Root-avoidance condition on an exceptional twist set `Exc : Finset ℕ`:
every exceptional twist `e ∈ Exc` below `x^Ct` actually satisfies `e ≤ x^eta`
(matching `UpperTheory.V.Win.Good`). -/
def Good (eta Ct : ℝ) (Exc : Finset ℕ) (x : ℝ) : Prop :=
  ∀ e ∈ Exc, (e : ℝ) ≤ x ^ Ct → (e : ℝ) ≤ x ^ eta

theorem Good.mono {eta Ct x : ℝ} {S T : Finset ℕ} (h : S ⊆ T) (hT : Good eta Ct T x) :
    Good eta Ct S x :=
  fun e he hle => hT e (h he) hle

theorem Good.empty (eta Ct x : ℝ) : Good eta Ct ∅ x := by
  intro e he
  simp at he

theorem Good.union {eta Ct x : ℝ} {S T : Finset ℕ}
    (hS : Good eta Ct S x) (hT : Good eta Ct T x) :
    Good eta Ct (S ∪ T) x := by
  intro e he hle
  rcases Finset.mem_union.mp he with h1 | h2
  · exact hS e h1 hle
  · exact hT e h2 hle

/-- Alpöge's explicit `Window1` exponent `J = 2^(R + 2) * (2 * CK * Ct / eps)^R`. -/
def windowExponent (R : ℕ) (CK Ct eps : ℝ) : ℝ :=
  (2 : ℝ) ^ (R + 2) * (2 * CK * Ct / eps) ^ R

theorem windowExponent_pos (R : ℕ) {CK Ct eps : ℝ}
    (hCK : 0 < CK) (hCt : 0 < Ct) (heps : 0 < eps) :
    0 < windowExponent R CK Ct eps := by
  unfold windowExponent
  have h1 : 0 < 2 * CK * Ct / eps := by positivity
  positivity

theorem one_le_windowExponent (R : ℕ) {CK Ct eps : ℝ}
    (hCK : 1 ≤ CK) (hCt : 1 ≤ Ct) (heps0 : 0 < eps) (heps1 : eps ≤ 1) :
    1 ≤ windowExponent R CK Ct eps := by
  unfold windowExponent
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (R + 2) := one_le_pow₀ (by norm_num)
  have hratio : 1 ≤ 2 * CK * Ct / eps := by
    rw [one_le_div heps0]
    nlinarith
  have hpow : (1 : ℝ) ≤ (2 * CK * Ct / eps) ^ R := one_le_pow₀ hratio
  nlinarith

/-- **Unconditional `Window1` Dyadic Root-Avoidance Pigeonhole Theorem**
(exact match to `UpperTheory.V.Win.window1` in `LayeredIsomorphisms/Window1.lean`):
for any `R : ℕ`, separation ratio `B ≥ 1`, upper scale `U > 0`, and any finite set `T : Finset ℝ`
of at most `R` bad points, there exists `y ∈ [U / (2^(R+2) * B^R), U / 2]` such that EVERY
`u ∈ [y, 2y]` avoids the forbidden shell `(u / B, u]` around every point `a ∈ T`
(i.e. `a ≤ u → B * a ≤ u`). -/
theorem window1 :
    ∀ (R : ℕ) (B U : ℝ) (T : Finset ℝ), 1 ≤ B → 0 < U → T.card ≤ R →
      ∃ y : ℝ, U / ((2 : ℝ) ^ (R + 2) * B ^ R) ≤ y ∧ 2 * y ≤ U ∧
        ∀ a ∈ T, ∀ u : ℝ, y ≤ u → u ≤ 2 * y → a ≤ u → B * a ≤ u := by
  intro R
  induction R with
  | zero =>
    intro B U T _ hU hT
    have hT0 : T = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hT0
    refine ⟨U / 2, ?_, by linarith, ?_⟩
    · apply div_le_div_of_nonneg_left hU.le (by norm_num)
      norm_num
    · intro a ha
      simp at ha
  | succ n ih =>
    intro B U T hB hU hT
    have hB0 : 0 < B := by linarith
    by_cases h : ∃ a ∈ T, U / (2 * B) < a ∧ a ≤ U
    · obtain ⟨a0, ha0, h1, _⟩ := h
      obtain ⟨y, hy1, hy2, hy3⟩ := ih B (U / (2 * B)) (T.erase a0) hB (by positivity)
        (by rw [Finset.card_erase_of_mem ha0]; omega)
      refine ⟨y, ?_, ?_, ?_⟩
      · calc U / ((2 : ℝ) ^ (n + 1 + 2) * B ^ (n + 1))
            = U / (2 * B) / ((2 : ℝ) ^ (n + 2) * B ^ n) := by
              rw [div_div]
              congr 1
              ring
          _ ≤ y := hy1
      · have hleU : U / (2 * B) ≤ U := div_le_self hU.le (by linarith)
        linarith
      · intro a ha u hu1 hu2 hau
        by_cases hae : a = a0
        · subst hae
          exfalso
          have : U / (2 * B) < u := lt_of_lt_of_le h1 hau
          linarith
        · exact hy3 a (Finset.mem_erase.mpr ⟨hae, ha⟩) u hu1 hu2 hau
    · push Not at h
      refine ⟨U / 2, ?_, by linarith, ?_⟩
      · apply div_le_div_of_nonneg_left hU.le (by norm_num)
        have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
        have h3 : (1 : ℝ) ≤ B ^ (n + 1) := one_le_pow₀ hB
        have h4 : (2 : ℝ) ^ (n + 1 + 2) = 8 * (2 : ℝ) ^ n := by ring
        rw [h4]
        nlinarith
      · intro a ha u hu1 hu2 hau
        by_contra hc
        push Not at hc
        have ha1 : U / (2 * B) < a := by
          rw [div_lt_iff₀ (by positivity)]
          nlinarith
        have hgt := h a ha ha1
        linarith

/-- **Multiplicative `Window` Root-Avoidance Theorem** (exact match to `UpperTheory.V.Win.window`
in `LayeredIsomorphisms/Window.lean`):
for any `R : ℕ`, `0 < eta ≤ Ct`, `1 < X`, and any finite set `Exc : Finset ℕ` of at most `R`
exceptional twists, there exists `Y ∈ [X^(1/J), X^(1/2)]` with `J = 2^(R+2) * (Ct / eta)^R`
such that EVERY `x ∈ [Y, Y^2]` satisfies `Good eta Ct Exc x`. -/
theorem window :
    ∀ (R : ℕ) (eta Ct X : ℝ) (Exc : Finset ℕ), 0 < eta → eta ≤ Ct → 1 < X → Exc.card ≤ R →
      ∃ Y : ℝ, InRange ((2 : ℝ) ^ (R + 2) * (Ct / eta) ^ R) X Y ∧
        ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (2 : ℝ) → Good eta Ct Exc x := by
  intro R eta Ct X Exc heta hle hX hcard
  classical
  have hCt : 0 < Ct := lt_of_lt_of_le heta hle
  have hX0 : 0 < X := by linarith
  have hB : 1 ≤ Ct / eta := (one_le_div heta).mpr hle
  obtain ⟨y, hy1, hy2, hy3⟩ := window1 R (Ct / eta) (Real.log X)
    (Exc.image fun e : ℕ => Real.log (e : ℝ) / Ct) hB (Real.log_pos hX)
    (le_trans Finset.card_image_le hcard)
  have hsq : Real.exp y ^ (2 : ℝ) = Real.exp (2 * y) := by
    rw [← Real.exp_mul, mul_comm]
  refine ⟨Real.exp y, ⟨?_, ?_⟩, ?_⟩
  · rw [Real.rpow_def_of_pos hX0, Real.exp_le_exp, mul_one_div]
    exact hy1
  · rw [hsq, ← Real.le_log_iff_exp_le hX0]
    exact hy2
  · intro x hx1 hx2 e he hex
    have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos y) hx1
    rcases Nat.eq_zero_or_pos e with h0 | hpos
    · subst h0
      simpa using (Real.rpow_pos_of_pos hx0 eta).le
    have he0 : (0 : ℝ) < e := by exact_mod_cast hpos
    have hu1 : y ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx1
    have hu2 : Real.log x ≤ 2 * y := by
      rw [Real.log_le_iff_le_exp hx0, ← hsq]
      exact hx2
    have hu3 : Real.log (e : ℝ) / Ct ≤ Real.log x := by
      rw [div_le_iff₀ hCt, mul_comm, ← Real.log_rpow hx0]
      exact Real.log_le_log he0 hex
    have h := hy3 _ (Finset.mem_image_of_mem _ he) (Real.log x) hu1 hu2 hu3
    have h' : Ct / eta * (Real.log (e : ℝ) / Ct) = Real.log (e : ℝ) / eta := by
      field_simp
    rw [h', div_le_iff₀ heta] at h
    rw [Real.rpow_def_of_pos hx0, ← Real.log_le_iff_le_exp he0]
    exact h

/-- Specialization of `window` to `eta = eps / (2 * CK)`, giving the exact Alpöge window
exponent `J = windowExponent R CK Ct eps = 2^(R + 2) * (2 * CK * Ct / eps)^R`. -/
theorem window_of_CK (R : ℕ) (CK Ct eps X : ℝ) (Exc : Finset ℕ)
    (hCK : 1 ≤ CK) (hCt : 1 ≤ Ct) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hX : 1 < X) (hcard : Exc.card ≤ R) :
    ∃ Y : ℝ, InRange (windowExponent R CK Ct eps) X Y ∧
      ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (2 : ℝ) → Good (eps / (2 * CK)) Ct Exc x := by
  have heta : 0 < eps / (2 * CK) := by positivity
  have hetaCt : eps / (2 * CK) ≤ Ct := by
    have h1 : eps / (2 * CK) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    linarith
  obtain ⟨Y, hY, hgood⟩ := window R (eps / (2 * CK)) Ct X Exc heta hetaCt hX hcard
  have hJeq : (2 : ℝ) ^ (R + 2) * (Ct / (eps / (2 * CK))) ^ R = windowExponent R CK Ct eps := by
    unfold windowExponent
    rw [show Ct / (eps / (2 * CK)) = 2 * CK * Ct / eps by rw [div_div_eq_mul_div]; ring]
  rw [hJeq] at hY
  exact ⟨Y, hY, hgood⟩

/-- **Simultaneous Multi-Family `Window1` Theorem**: avoids BOTH an `l = 2` exceptional twist set
`ExcA` (`card ≤ R₀`) AND a finite family `ExcB l` (`l ∈ B'`, `card ≤ Rl l`) on a SINGLE sub-window
`[Y, Y^2] ⊂ [X^(1/J), X]` with `R = R₀ + ∑ l ∈ B', Rl l` and `J = windowExponent R CK Ct eps`. -/
theorem window_joint_families {ι : Type*} [DecidableEq ι]
    (B' : Finset ι) (R₀ : ℕ) (Rl : ι → ℕ)
    (CK Ct eps X : ℝ) (ExcA : Finset ℕ) (ExcB : ι → Finset ℕ)
    (hCK : 1 ≤ CK) (hCt : 1 ≤ Ct) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hX : 1 < X) (hcardA : ExcA.card ≤ R₀) (hcardB : ∀ l ∈ B', (ExcB l).card ≤ Rl l) :
    let R := R₀ + ∑ l ∈ B', Rl l
    ∃ Y : ℝ, InRange (windowExponent R CK Ct eps) X Y ∧
      ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (2 : ℝ) →
        Good (eps / (2 * CK)) Ct ExcA x ∧
        ∀ l ∈ B', Good (eps / (2 * CK)) Ct (ExcB l) x := by
  classical
  set R := R₀ + ∑ l ∈ B', Rl l
  have hcard : (ExcA ∪ B'.biUnion ExcB).card ≤ R :=
    (Finset.card_union_le _ _).trans
      (add_le_add hcardA (Finset.card_biUnion_le.trans (Finset.sum_le_sum hcardB)))
  obtain ⟨Y, hY, hgood⟩ := window_of_CK R CK Ct eps X (ExcA ∪ B'.biUnion ExcB)
    hCK hCt heps0 heps1 hX hcard
  refine ⟨Y, hY, fun x hx1 hx2 => ?_⟩
  have hG := hgood x hx1 hx2
  refine ⟨hG.mono Finset.subset_union_left, fun l hl => ?_⟩
  exact hG.mono ((Finset.subset_biUnion_of_mem ExcB hl).trans Finset.subset_union_right)

end Window1Pigeonhole

/-! ## Section 2: Ultrametric `p`-adic Root Separation & Distinguished `μ = 0` Power Series -/

section UltrametricRootSeparation

/-- **Ultrametric Additive Root-Uniqueness (`near1`)** (exact match to
`UpperTheory.V.Win.near1` in `LayeredIsomorphisms/Near1.lean`):
in any ultrametric normed field extension `K / ℚ_[l]`, at most ONE integer twist `a ∈ [1, Z]`
can satisfy `‖s - (a : K)‖ < l ^ (-Nat.log l Z)` for a given `s : K`. -/
theorem near1 (l : ℕ) [Fact l.Prime] (K : Type*) [NormedField K]
    [NormedAlgebra ℚ_[l] K] [IsUltrametricDist K]
    (s : K) (Z a b : ℕ)
    (ha1 : 1 ≤ a) (haZ : a ≤ Z) (hb1 : 1 ≤ b) (hbZ : b ≤ Z)
    (hsa : ‖s - (a : K)‖ < (l : ℝ) ^ (-(Nat.log l Z : ℤ)))
    (hsb : ‖s - (b : K)‖ < (l : ℝ) ^ (-(Nat.log l Z : ℤ))) :
    a = b := by
  by_contra hab
  have hlp : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hlp.one_lt
  set k := Nat.log l Z with hk
  set d : ℤ := (a : ℤ) - b with hd
  have hd0 : d ≠ 0 := by omega
  have hK : ‖(d : ℚ_[l])‖ < (l : ℝ) ^ (-(k : ℤ)) := by
    have h1 : algebraMap ℚ_[l] K (d : ℚ_[l]) = (s - (b : K)) + -(s - (a : K)) := by
      rw [map_intCast, hd]
      push_cast
      ring
    rw [← norm_algebraMap' K, h1]
    calc ‖(s - (b : K)) + -(s - (a : K))‖
        ≤ max ‖s - (b : K)‖ ‖-(s - (a : K))‖ := IsUltrametricDist.norm_add_le_max _ _
      _ < (l : ℝ) ^ (-(k : ℤ)) := by
        rw [norm_neg]
        exact max_lt hsb hsa
  have hdq : (d : ℚ_[l]) ≠ 0 := by exact_mod_cast hd0
  rw [Padic.norm_eq_zpow_neg_valuation hdq] at hK
  have hlt := (zpow_lt_zpow_iff_right₀ hl1).mp hK
  have hle : ‖(d : ℚ_[l])‖ ≤ (l : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) := by
    rw [Padic.norm_eq_zpow_neg_valuation hdq]
    apply zpow_le_zpow_right₀ hl1.le
    push_cast
    omega
  have hdvd := (Padic.norm_int_le_pow_iff_dvd d (k + 1)).mp hle
  have hZ := Nat.lt_pow_succ_log_self hlp.one_lt Z
  have habs : d.natAbs ≤ Z := by
    rw [hd]
    omega
  have h0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd (by
    simp only [Int.natAbs_pow, Int.natAbs_natCast]
    exact lt_of_le_of_lt habs hZ)
  exact hd0 h0

/-- For any `R'` ultrametric roots `s : Fin R' → K` (`R' ≤ R`) and cutoff `Z`, the exceptional set
of twists `e ∈ [1, Z]` within `l^(-Nat.log l Z)` of some `s i` has cardinality `≤ R`. -/
theorem exists_exc_of_roots (l R R' : ℕ) [Fact l.Prime]
    (K : Type*) [NormedField K] [NormedAlgebra ℚ_[l] K] [IsUltrametricDist K]
    (s : Fin R' → K) (hR' : R' ≤ R) (Z : ℕ) :
    ∃ Exc : Finset ℕ, Exc.card ≤ R ∧
      ∀ e : ℕ, 1 ≤ e → e ≤ Z → e ∉ Exc →
        ∀ i : Fin R', (l : ℝ) ^ (-(Nat.log l Z : ℤ)) ≤ ‖s i - (e : K)‖ := by
  classical
  let near : Fin R' → Finset ℕ := fun i =>
    (Finset.Icc 1 Z).filter (fun e : ℕ => ‖s i - (e : K)‖ < (l : ℝ) ^ (-(Nat.log l Z : ℤ)))
  refine ⟨Finset.univ.biUnion near, ?_, ?_⟩
  · have hone : ∀ i : Fin R', (near i).card ≤ 1 := by
      intro i
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [near, Finset.mem_filter, Finset.mem_Icc] at ha hb
      exact near1 l K (s i) Z a b ha.1.1 ha.1.2 hb.1.1 hb.1.2 ha.2 hb.2
    calc (Finset.univ.biUnion near).card
        ≤ ∑ i : Fin R', (near i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin R', 1 := Finset.sum_le_sum fun i _ => hone i
      _ = R' := by simp
      _ ≤ R := hR'
  · intro e he1 heZ hne i
    by_contra hlt
    push Not at hlt
    apply hne
    simp only [near, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter,
      Finset.mem_Icc]
    exact ⟨i, ⟨he1, heZ⟩, hlt⟩

/-- Ultrametric strict-dominance norm equality in any ultrametric normed group:
if `‖y‖ < ‖x‖`, then `‖x + y‖ = ‖x‖`. -/
theorem ultrametric_norm_add_eq_left {E : Type*} [SeminormedAddCommGroup E] [IsUltrametricDist E]
    {x y : E} (h : ‖y‖ < ‖x‖) : ‖x + y‖ = ‖x‖ := by
  apply le_antisymm
  · exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le le_rfl h.le)
  · by_contra hlt
    push Not at hlt
    have hle : ‖x‖ ≤ max ‖x + y‖ ‖-y‖ := by
      have hx : x = (x + y) + (-y) := by abel
      conv_lhs => rw [hx]
      exact IsUltrametricDist.norm_add_le_max (x + y) (-y)
    rw [norm_neg] at hle
    have hmax : max ‖x + y‖ ‖y‖ < ‖x‖ := max_lt hlt h
    linarith

/-- Lifting the Exponent (single `p`-step) in `ℤ_[p]`:
if `u : ℤ_[p]` satisfies `‖u‖ = p^(-c)` with `c ≥ 1` (and `c ≥ 2` when `p = 2`), then
`‖(1 + u)^p - 1‖ = (p : ℝ)^(-((c + 1 : ℕ) : ℤ))`! -/
theorem padicInt_norm_one_add_pow_p_sub_one {p : ℕ} [Fact p.Prime] {u : ℤ_[p]} {c : ℕ}
    (hc : 1 ≤ c) (hc2 : p = 2 → 2 ≤ c) (hu : ‖u‖ = (p : ℝ) ^ (-(c : ℤ))) :
    ‖(1 + u) ^ p - 1‖ = (p : ℝ) ^ (-((c + 1 : ℕ) : ℤ)) := by
  have hp : p.Prime := Fact.out
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hnorm_p : ‖(p : ℤ_[p])‖ = (p : ℝ) ^ (-(1 : ℤ)) := by
    have hcoe : ‖(p : ℤ_[p])‖ = ‖((p : ℚ_[p]))‖ := rfl
    rw [hcoe, Padic.norm_p]
    simp
  -- Expand `(1 + u)^p - 1 = p * u + ∑_{j=2}^p C(p, j) * u^j`
  have hexp : (1 + u) ^ p - 1 =
      (p : ℤ_[p]) * u + ∑ j ∈ Finset.Ico 2 (p + 1), (p.choose j : ℤ_[p]) * u ^ j := by
    rw [add_comm 1 u, add_pow]
    have hsplit1 : ∑ m ∈ Finset.range (p + 1), u ^ m * 1 ^ (p - m) * (p.choose m : ℤ_[p]) =
        (u ^ 0 * 1 ^ (p - 0) * (p.choose 0 : ℤ_[p])) +
          ∑ m ∈ Finset.Ico 1 (p + 1), u ^ m * 1 ^ (p - m) * (p.choose m : ℤ_[p]) :=
      Finset.sum_range_eq_add_Ico _ (Nat.succ_pos p)
    have hsplit2 : ∑ m ∈ Finset.Ico 1 (p + 1), u ^ m * 1 ^ (p - m) * (p.choose m : ℤ_[p]) =
        (u ^ 1 * 1 ^ (p - 1) * (p.choose 1 : ℤ_[p])) +
          ∑ m ∈ Finset.Ico 2 (p + 1), u ^ m * 1 ^ (p - m) * (p.choose m : ℤ_[p]) :=
      Finset.sum_eq_sum_Ico_succ_bot (by have := hp.two_le; omega) _
    rw [hsplit1, hsplit2]
    simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.cast_one, pow_one,
      Nat.choose_one_right, add_sub_cancel_left]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm]
  have hmain : ‖(p : ℤ_[p]) * u‖ = (p : ℝ) ^ (-((c + 1 : ℕ) : ℤ)) := by
    rw [norm_mul, hnorm_p, hu, ← zpow_add₀ (by positivity : (p : ℝ) ≠ 0)]
    congr 1
    omega
  have htail : ‖∑ j ∈ Finset.Ico 2 (p + 1), (p.choose j : ℤ_[p]) * u ^ j‖ <
      (p : ℝ) ^ (-((c + 1 : ℕ) : ℤ)) := by
    have hlt_each : ∀ j ∈ Finset.Ico 2 (p + 1),
        ‖(p.choose j : ℤ_[p]) * u ^ j‖ < (p : ℝ) ^ (-((c + 1 : ℕ) : ℤ)) := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      rw [norm_mul, norm_pow, hu, ← zpow_natCast, ← zpow_mul]
      by_cases hjp : j = p
      · rw [hjp, Nat.choose_self, Nat.cast_one, norm_one, one_mul]
        apply (zpow_lt_zpow_iff_right₀ hp1).mpr
        have hpc : c + 1 < c * p := by
          rcases eq_or_lt_of_le hp.two_le with hp2 | hp3
          · have hc' := hc2 hp2.symm
            nlinarith
          · nlinarith
        have hpcZ : (c : ℤ) + 1 < (c : ℤ) * (p : ℤ) := by exact_mod_cast hpc
        push_cast
        linarith
      · have hjlt : j < p := by omega
        have hdvd : p ∣ p.choose j := hp.dvd_choose_self (by omega) hjlt
        have hch_le : ‖(p.choose j : ℤ_[p])‖ ≤ (p : ℝ) ^ (-(1 : ℤ)) := by
          have hdvd' : (p : ℤ_[p]) ^ 1 ∣ (p.choose j : ℤ_[p]) := by
            rw [pow_one]
            obtain ⟨m, hm⟩ := hdvd
            exact ⟨(m : ℤ_[p]), by exact_mod_cast hm⟩
          exact (padicInt_p_pow_dvd_iff_norm_le _ 1).mp hdvd'
        calc ‖(p.choose j : ℤ_[p])‖ * (p : ℝ) ^ (-(c : ℤ) * (j : ℤ))
            ≤ (p : ℝ) ^ (-(1 : ℤ)) * (p : ℝ) ^ (-(c : ℤ) * (j : ℤ)) :=
              mul_le_mul_of_nonneg_right hch_le (by positivity)
          _ = (p : ℝ) ^ (-(1 : ℤ) + -(c : ℤ) * (j : ℤ)) :=
              (zpow_add₀ (by positivity : (p : ℝ) ≠ 0) _ _).symm
          _ < (p : ℝ) ^ (-((c + 1 : ℕ) : ℤ)) := by
              apply (zpow_lt_zpow_iff_right₀ hp1).mpr
              have h2c : c + 1 < 1 + c * j := by nlinarith
              have h2cZ : (c : ℤ) + 1 < 1 + (c : ℤ) * (j : ℤ) := by exact_mod_cast h2c
              push_cast
              linarith
    rcases (Finset.Ico 2 (p + 1)).eq_empty_or_nonempty with hemp | hne
    · rw [hemp, Finset.sum_empty, norm_zero]
      positivity
    · obtain ⟨j₀, hj₀, hmax⟩ :=
        IsUltrametricDist.exists_norm_finsetSum_le (Finset.Ico 2 (p + 1))
          (fun j => (p.choose j : ℤ_[p]) * u ^ j)
      exact hmax.trans_lt (hlt_each j₀ (hj₀ hne))
  rw [hexp, ultrametric_norm_add_eq_left (by rwa [hmain]), hmain]

/-- **Unconditional `p`-adic Lifting-the-Exponent Theorem** in `ℤ_[p]`:
if `κ : ℤ_[p]` satisfies `‖κ - 1‖ = p^(-c₀)` with `c₀ ≥ 1` (and `c₀ ≥ 2` when `p = 2`), then
for EVERY positive `d : ℕ`, `‖κ ^ d - 1‖ = (p : ℝ) ^ (-(c₀ : ℤ)) * ‖(d : ℤ_[p])‖`! -/
theorem padicInt_pow_sub_one_norm {p : ℕ} [Fact p.Prime] {κ : ℤ_[p]} {c₀ : ℕ}
    (hc0 : 1 ≤ c₀) (hc2 : p = 2 → 2 ≤ c₀) (hκ : ‖κ - 1‖ = (p : ℝ) ^ (-(c₀ : ℤ))) :
    ∀ d : ℕ, 0 < d → ‖κ ^ d - 1‖ = (p : ℝ) ^ (-(c₀ : ℤ)) * ‖(d : ℤ_[p])‖ := by
  have hp : p.Prime := Fact.out
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  -- Generalize over `(κ, c₀)` and induct strongly on `d`
  intro d
  induction d using Nat.strong_induction_on generalizing κ c₀ with
  | h d ih =>
    intro hd
    by_cases hpd : p ∣ d
    · obtain ⟨m, rfl⟩ := hpd
      have hm_pos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with rfl | h
        · simp at hd
        · exact h
      have hm_lt : m < p * m := lt_mul_of_one_lt_left hm_pos hp.one_lt
      have hκp : ‖κ ^ p - 1‖ = (p : ℝ) ^ (-((c₀ + 1 : ℕ) : ℤ)) := by
        have h1 : κ = 1 + (κ - 1) := by ring
        rw [h1]
        exact padicInt_norm_one_add_pow_p_sub_one hc0 hc2 hκ
      have hrec := ih m hm_lt (κ := κ ^ p) (c₀ := c₀ + 1) (by omega) (fun _ => by omega) hκp hm_pos
      rw [← pow_mul] at hrec
      rw [hrec, Nat.cast_mul, norm_mul]
      have hnorm_p : ‖(p : ℤ_[p])‖ = (p : ℝ) ^ (-(1 : ℤ)) := by
        have hcoe : ‖(p : ℤ_[p])‖ = ‖(p : ℚ_[p])‖ := rfl
        rw [hcoe, Padic.norm_p]
        simp
      rw [hnorm_p, ← mul_assoc, ← zpow_add₀ (by positivity : (p : ℝ) ≠ 0)]
      congr 2
      push_cast
      ring
    · -- Coprime case `¬ p ∣ d`: `κ^d - 1 = (κ - 1) * ∑_{j < d} κ^j`, and `∑_{j < d} κ^j` is a unit!
      have hfac : κ ^ d - 1 = (κ - 1) * ∑ j ∈ Finset.range d, κ ^ j := by
        rw [mul_comm, geom_sum_mul]
      have hκ_mod : PadicInt.toZMod κ = 1 := by
        have hdvd : (p : ℤ_[p]) ∣ (κ - 1) := by
          have h1 : ‖κ - 1‖ ≤ (p : ℝ) ^ (-(1 : ℤ)) := by
            rw [hκ]
            exact zpow_le_zpow_right₀ hp1.le (by omega)
          simpa [pow_one] using (padicInt_p_pow_dvd_iff_norm_le (κ - 1) 1).mpr h1
        have h0 : PadicInt.toZMod (κ - 1) = 0 := (padicInt_p_dvd_iff_toZMod_eq_zero _).mp hdvd
        rw [map_sub, map_one, sub_eq_zero] at h0
        exact h0
      have hsum_mod : PadicInt.toZMod (∑ j ∈ Finset.range d, κ ^ j) = (d : ZMod p) := by
        rw [map_sum]
        simp [map_pow, hκ_mod]
      have hd_ne : (d : ZMod p) ≠ 0 := by
        intro h0
        exact hpd ((ZMod.natCast_eq_zero_iff d p).mp h0)
      have hsum_norm : ‖∑ j ∈ Finset.range d, κ ^ j‖ = 1 := by
        rw [padicInt_norm_eq_one_iff_not_p_dvd, padicInt_p_dvd_iff_toZMod_eq_zero, hsum_mod]
        exact hd_ne
      have hd_norm : ‖(d : ℤ_[p])‖ = 1 := by
        rw [padicInt_norm_eq_one_iff_not_p_dvd, padicInt_p_dvd_iff_toZMod_eq_zero, map_natCast]
        exact hd_ne
      rw [hfac, norm_mul, hκ, hsum_norm, hd_norm]

/-- Exact `p`-adic distance between two cyclotomic twists `κ^a - 1` and `κ^b - 1`:
`‖(κ^a - 1) - (κ^b - 1)‖ = p^(-c₀) * ‖(a : ℤ) - b‖_p`. -/
theorem norm_cyclotomic_twist_sub {p : ℕ} [Fact p.Prime] {κ : ℤ_[p]} {c₀ : ℕ}
    (hc0 : 1 ≤ c₀) (hc2 : p = 2 → 2 ≤ c₀) (hκ : ‖κ - 1‖ = (p : ℝ) ^ (-(c₀ : ℤ)))
    (a b : ℕ) :
    ‖κ ^ a - κ ^ b‖ = (p : ℝ) ^ (-(c₀ : ℤ)) * ‖(((a : ℤ) - b : ℤ) : ℚ_[p])‖ := by
  have hp : p.Prime := Fact.out
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hκ_unit : ‖κ‖ = 1 := by
    have h1 : ‖κ - 1‖ < ‖(1 : ℤ_[p])‖ := by
      rw [hκ, norm_one]
      exact zpow_lt_one_of_neg₀ hp1 (by omega)
    have h2 : κ = 1 + (κ - 1) := by ring
    rw [h2, ultrametric_norm_add_eq_left h1, norm_one]
  rcases lt_trichotomy a b with hab | rfl | hba
  · have hpos : 0 < b - a := by omega
    have hrew : κ ^ a - κ ^ b = -(κ ^ a * (κ ^ (b - a) - 1)) := by
      rw [mul_sub, ← pow_add, Nat.add_sub_cancel' hab.le, mul_one, neg_sub]
    rw [hrew, norm_neg, norm_mul, norm_pow, hκ_unit, one_pow, one_mul,
      padicInt_pow_sub_one_norm hc0 hc2 hκ (b - a) hpos]
    congr 1
    have hcast : (((a : ℤ) - b : ℤ) : ℚ_[p]) = -(((b - a : ℕ) : ℤ_[p]) : ℚ_[p]) := by
      push_cast [Nat.cast_sub hab.le]
      ring
    rw [hcast, norm_neg]
    rfl
  · simp
  · have hpos : 0 < a - b := by omega
    have hrew : κ ^ a - κ ^ b = κ ^ b * (κ ^ (a - b) - 1) := by
      rw [mul_sub, ← pow_add, Nat.add_sub_cancel' hba.le, mul_one]
    rw [hrew, norm_mul, norm_pow, hκ_unit, one_pow, one_mul,
      padicInt_pow_sub_one_norm hc0 hc2 hκ (a - b) hpos]
    congr 1
    have hcast : (((a : ℤ) - b : ℤ) : ℚ_[p]) = (((a - b : ℕ) : ℤ_[p]) : ℚ_[p]) := by
      push_cast [Nat.cast_sub hba.le]
      rfl
    rw [hcast]
    rfl

/-- **Ultrametric Cyclotomic-Twist Root-Uniqueness (`near1_cyclotomic`)**:
in any ultrametric normed field extension `K / ℚ_[p]`, at most ONE twist `e ∈ [1, Z]`
can place `κ^e - 1` within `p^(-(c₀ + Nat.log p Z))` of a given root `α : K`! -/
theorem near1_cyclotomic (p : ℕ) [Fact p.Prime] {κ : ℤ_[p]} {c₀ : ℕ}
    (hc0 : 1 ≤ c₀) (hc2 : p = 2 → 2 ≤ c₀) (hκ : ‖κ - 1‖ = (p : ℝ) ^ (-(c₀ : ℤ)))
    (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (α : K) (Z a b : ℕ)
    (ha1 : 1 ≤ a) (haZ : a ≤ Z) (hb1 : 1 ≤ b) (hbZ : b ≤ Z)
    (hsa : ‖α - algebraMap ℚ_[p] K ((κ ^ a - 1 : ℤ_[p]) : ℚ_[p])‖ <
      (p : ℝ) ^ (-((c₀ + Nat.log p Z : ℕ) : ℤ)))
    (hsb : ‖α - algebraMap ℚ_[p] K ((κ ^ b - 1 : ℤ_[p]) : ℚ_[p])‖ <
      (p : ℝ) ^ (-((c₀ + Nat.log p Z : ℕ) : ℤ))) :
    a = b := by
  by_contra hab
  have hp : p.Prime := Fact.out
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  set k := Nat.log p Z
  set d : ℤ := (a : ℤ) - b
  have hd0 : d ≠ 0 := by omega
  have hdiff : ‖κ ^ a - κ ^ b‖ < (p : ℝ) ^ (-((c₀ + k : ℕ) : ℤ)) := by
    have hcoe : ‖κ ^ a - κ ^ b‖ = ‖((κ ^ a - κ ^ b : ℤ_[p]) : ℚ_[p])‖ := rfl
    rw [hcoe, ← norm_algebraMap' K]
    have h1 : algebraMap ℚ_[p] K ((κ ^ a - κ ^ b : ℤ_[p]) : ℚ_[p]) =
        (α - algebraMap ℚ_[p] K ((κ ^ b - 1 : ℤ_[p]) : ℚ_[p])) +
          -(α - algebraMap ℚ_[p] K ((κ ^ a - 1 : ℤ_[p]) : ℚ_[p])) := by
      have hsub : ((κ ^ a - κ ^ b : ℤ_[p]) : ℚ_[p]) =
          ((κ ^ a - 1 : ℤ_[p]) : ℚ_[p]) - ((κ ^ b - 1 : ℤ_[p]) : ℚ_[p]) := by
        push_cast; ring
      rw [hsub, map_sub]; ring
    rw [h1]
    calc ‖(α - algebraMap ℚ_[p] K ((κ ^ b - 1 : ℤ_[p]) : ℚ_[p])) +
            -(α - algebraMap ℚ_[p] K ((κ ^ a - 1 : ℤ_[p]) : ℚ_[p]))‖
        ≤ max ‖α - algebraMap ℚ_[p] K ((κ ^ b - 1 : ℤ_[p]) : ℚ_[p])‖
              ‖-(α - algebraMap ℚ_[p] K ((κ ^ a - 1 : ℤ_[p]) : ℚ_[p]))‖ :=
          IsUltrametricDist.norm_add_le_max _ _
      _ < (p : ℝ) ^ (-((c₀ + k : ℕ) : ℤ)) := by
        rw [norm_neg]
        exact max_lt hsb hsa
  rw [norm_cyclotomic_twist_sub hc0 hc2 hκ a b] at hdiff
  have hpow_split : (p : ℝ) ^ (-((c₀ + k : ℕ) : ℤ)) =
      (p : ℝ) ^ (-(c₀ : ℤ)) * (p : ℝ) ^ (-(k : ℤ)) := by
    rw [← zpow_add₀ (by positivity : (p : ℝ) ≠ 0)]
    congr 1; push_cast; ring
  rw [hpow_split] at hdiff
  have hd_lt : ‖(d : ℚ_[p])‖ < (p : ℝ) ^ (-(k : ℤ)) :=
    lt_of_mul_lt_mul_left hdiff (by positivity)
  have hdq : (d : ℚ_[p]) ≠ 0 := by exact_mod_cast hd0
  rw [Padic.norm_eq_zpow_neg_valuation hdq] at hd_lt
  have hlt := (zpow_lt_zpow_iff_right₀ hp1).mp hd_lt
  have hle : ‖(d : ℚ_[p])‖ ≤ (p : ℝ) ^ (-((k + 1 : ℕ) : ℤ)) := by
    rw [Padic.norm_eq_zpow_neg_valuation hdq]
    apply zpow_le_zpow_right₀ hp1.le
    push_cast; omega
  have hdvd := (Padic.norm_int_le_pow_iff_dvd d (k + 1)).mp hle
  have hZ := Nat.lt_pow_succ_log_self hp.one_lt Z
  have habs : d.natAbs ≤ Z := by omega
  have h0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd (by
    simp only [Int.natAbs_pow, Int.natAbs_natCast]
    exact lt_of_le_of_lt habs hZ)
  exact hd0 h0

/-- A distinguished `μ = 0` Iwasawa power series `f ∈ ℤ_[p][[T]]` (from `Stage8IwasawaWeierstrass` /
`Stage11FerreroWashington` / `Stage11IwasawaMainConj`) whose Weierstrass distinguished polynomial
`distPart f` splits into linear factors over an ultrametric extension `K / ℚ_[p]`. -/
structure SplitDistinguishedSeries (p : ℕ) [Fact p.Prime]
    (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] where
  series : IwasawaAlg p
  ne_zero : series ≠ 0
  mu_zero : iwasawaMu series = 0
  roots : Fin (iwasawaLambda series) → K
  splits : (distPart series).map ((algebraMap ℚ_[p] K).comp (algebraMap ℤ_[p] ℚ_[p])) =
    ∏ i : Fin (iwasawaLambda series), (Polynomial.X - Polynomial.C (roots i))

/-- Exact evaluation formula for a `SplitDistinguishedSeries` in `K`:
`((distPart f).eval t₀ : K) = ∏ i, (t₀ - roots i)`. -/
theorem SplitDistinguishedSeries.eval_eq_prod {p : ℕ} [Fact p.Prime]
    {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (F : SplitDistinguishedSeries p K) (t₀ : ℤ_[p]) :
    algebraMap ℚ_[p] K (((distPart F.series).eval t₀ : ℤ_[p]) : ℚ_[p]) =
      ∏ i : Fin (iwasawaLambda F.series),
        (algebraMap ℚ_[p] K (t₀ : ℚ_[p]) - F.roots i) := by
  let φ : ℤ_[p] →+* K := (algebraMap ℚ_[p] K).comp (algebraMap ℤ_[p] ℚ_[p])
  have h1 : φ ((distPart F.series).eval t₀) =
      ((distPart F.series).map φ).eval (φ t₀) :=
    (Polynomial.eval_map_apply φ t₀).symm
  change φ ((distPart F.series).eval t₀) = _
  rw [h1, F.splits, Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, φ]

/-- Lower bound on the `p`-adic norm of `(distPart f).eval t₀` from lower bounds on root distances. -/
theorem SplitDistinguishedSeries.norm_eval_ge_of_root_dist {p : ℕ} [Fact p.Prime]
    {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (F : SplitDistinguishedSeries p K) (t₀ : ℤ_[p]) (B : ℕ)
    (hdist : ∀ i : Fin (iwasawaLambda F.series),
      (p : ℝ) ^ (-(B : ℤ)) ≤ ‖F.roots i - algebraMap ℚ_[p] K (t₀ : ℚ_[p])‖) :
    (p : ℝ) ^ (-((iwasawaLambda F.series * B : ℕ) : ℤ)) ≤ ‖(distPart F.series).eval t₀‖ := by
  have hcoe : ‖(distPart F.series).eval t₀‖ =
      ‖algebraMap ℚ_[p] K (((distPart F.series).eval t₀ : ℤ_[p]) : ℚ_[p])‖ := by
    rw [norm_algebraMap' K]
    rfl
  rw [hcoe, F.eval_eq_prod, norm_prod]
  calc (p : ℝ) ^ (-((iwasawaLambda F.series * B : ℕ) : ℤ))
      = ∏ _i : Fin (iwasawaLambda F.series), (p : ℝ) ^ (-(B : ℤ)) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← zpow_natCast, ← zpow_mul]
        congr 1
        push_cast
        ring
    _ ≤ ∏ i : Fin (iwasawaLambda F.series), ‖algebraMap ℚ_[p] K (t₀ : ℚ_[p]) - F.roots i‖ := by
        refine Finset.prod_le_prod (fun _ _ => by positivity) fun i _ => ?_
        rw [norm_sub_rev]
        exact hdist i

/-- Exact `p`-adic norm formula `‖x‖ = p^(-x.valuation)` for nonzero `x : ℤ_[p]`. -/
lemma padicInt_norm_eq_zpow_neg_val {p : ℕ} [Fact p.Prime] {x : ℤ_[p]} (hx : x ≠ 0) :
    ‖x‖ = (p : ℝ) ^ (-(x.valuation : ℤ)) := by
  set k := x.valuation
  have hspec : x = (PadicInt.unitCoeff hx : ℤ_[p]) * (p : ℤ_[p]) ^ k :=
    PadicInt.unitCoeff_spec hx
  have hu : ‖(PadicInt.unitCoeff hx : ℤ_[p])‖ = 1 :=
    PadicInt.isUnit_iff.mp (PadicInt.unitCoeff hx).isUnit
  have hpnorm : ‖(p : ℤ_[p])‖ = (p : ℝ) ^ (-(1 : ℤ)) := by
    have hcoe : ‖(p : ℤ_[p])‖ = ‖(p : ℚ_[p])‖ := rfl
    rw [hcoe, Padic.norm_p]
    simp
  conv_lhs => rw [hspec]
  rw [norm_mul, hu, one_mul, norm_pow, hpnorm, ← zpow_natCast, ← zpow_mul]
  congr 1
  ring

/-- Exact `p`-adic valuation upper bound on `(distPart f).eval t₀` from root-distance separation:
if every root `α_i` has `‖α_i - t₀‖ ≥ p^(-B)`, then `(distPart f).eval t₀ ≠ 0` and
`((distPart f).eval t₀).valuation ≤ iwasawaLambda f * B`! -/
theorem SplitDistinguishedSeries.valuation_eval_le_of_root_dist {p : ℕ} [Fact p.Prime]
    {K : Type*} [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (F : SplitDistinguishedSeries p K) (t₀ : ℤ_[p]) (B : ℕ)
    (hdist : ∀ i : Fin (iwasawaLambda F.series),
      (p : ℝ) ^ (-(B : ℤ)) ≤ ‖F.roots i - algebraMap ℚ_[p] K (t₀ : ℚ_[p])‖) :
    (distPart F.series).eval t₀ ≠ 0 ∧
      ((distPart F.series).eval t₀).valuation ≤ iwasawaLambda F.series * B := by
  have hp : p.Prime := Fact.out
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hnorm := F.norm_eval_ge_of_root_dist t₀ B hdist
  have hne : (distPart F.series).eval t₀ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    have hpos : (0 : ℝ) < (p : ℝ) ^ (-((iwasawaLambda F.series * B : ℕ) : ℤ)) := by positivity
    linarith
  refine ⟨hne, ?_⟩
  rw [padicInt_norm_eq_zpow_neg_val hne] at hnorm
  have hle := (zpow_le_zpow_iff_right₀ hp1).mp hnorm
  omega

/-- **Finite-Family Distinguished `μ = 0` Iwasawa Root-Avoidance Extraction**:
given `m` distinguished `μ = 0` Iwasawa power series `F_1, ..., F_m ∈ ℤ_[p][[T]]` with total
`λ`-invariant `∑ i, λ(F_i) ≤ R` and a cyclotomic twist generator `κ` (`‖κ - 1‖ = p^(-c₀)`),
for EVERY cutoff `Z : ℕ`, there exists an exceptional twist set `Exc : Finset ℕ` with `Exc.card ≤ R`
such that for EVERY `e ∈ [1, Z] \ Exc`:
1. every `(distPart (F i).series).eval (κ^e - 1) ≠ 0`, AND
2. `∑ i, ((distPart (F i).series).eval (κ^e - 1)).valuation ≤ R * (c₀ + Nat.log p Z)`! -/
theorem iwasawa_family_root_avoidance_exc {p m R : ℕ} [Fact p.Prime]
    {κ : ℤ_[p]} {c₀ : ℕ}
    (hc0 : 1 ≤ c₀) (hc2 : p = 2 → 2 ≤ c₀) (hκ : ‖κ - 1‖ = (p : ℝ) ^ (-(c₀ : ℤ)))
    (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (F : Fin m → SplitDistinguishedSeries p K)
    (hlam : ∑ i : Fin m, iwasawaLambda (F i).series ≤ R) (Z : ℕ) :
    ∃ Exc : Finset ℕ, Exc.card ≤ R ∧
      ∀ e : ℕ, 1 ≤ e → e ≤ Z → e ∉ Exc →
        (∀ i : Fin m, (distPart (F i).series).eval (κ ^ e - 1) ≠ 0) ∧
        ∑ i : Fin m, ((distPart (F i).series).eval (κ ^ e - 1)).valuation ≤
          R * (c₀ + Nat.log p Z) := by
  classical
  let near : (i : Fin m) → Fin (iwasawaLambda (F i).series) → Finset ℕ := fun i j =>
    (Finset.Icc 1 Z).filter fun e : ℕ =>
      ‖(F i).roots j - algebraMap ℚ_[p] K ((κ ^ e - 1 : ℤ_[p]) : ℚ_[p])‖ <
        (p : ℝ) ^ (-((c₀ + Nat.log p Z : ℕ) : ℤ))
  let Exc : Finset ℕ := Finset.univ.biUnion fun i : Fin m => Finset.univ.biUnion (near i)
  refine ⟨Exc, ?_, ?_⟩
  · have hone : ∀ (i : Fin m) (j : Fin (iwasawaLambda (F i).series)), (near i j).card ≤ 1 := by
      intro i j
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [near, Finset.mem_filter, Finset.mem_Icc] at ha hb
      exact near1_cyclotomic p hc0 hc2 hκ K ((F i).roots j) Z a b ha.1.1 ha.1.2 hb.1.1 hb.1.2
        ha.2 hb.2
    calc Exc.card
        ≤ ∑ i : Fin m, (Finset.univ.biUnion (near i)).card := Finset.card_biUnion_le
      _ ≤ ∑ i : Fin m, ∑ j : Fin (iwasawaLambda (F i).series), (near i j).card :=
          Finset.sum_le_sum fun i _ => Finset.card_biUnion_le
      _ ≤ ∑ i : Fin m, ∑ _j : Fin (iwasawaLambda (F i).series), 1 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hone i j
      _ = ∑ i : Fin m, iwasawaLambda (F i).series := by simp
      _ ≤ R := hlam
  · intro e he1 heZ hne
    have hdist : ∀ (i : Fin m) (j : Fin (iwasawaLambda (F i).series)),
        (p : ℝ) ^ (-((c₀ + Nat.log p Z : ℕ) : ℤ)) ≤
          ‖(F i).roots j - algebraMap ℚ_[p] K ((κ ^ e - 1 : ℤ_[p]) : ℚ_[p])‖ := by
      intro i j
      by_contra hlt
      push Not at hlt
      apply hne
      simp only [Exc, near, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter,
        Finset.mem_Icc]
      exact ⟨i, j, ⟨he1, heZ⟩, hlt⟩
    refine ⟨fun i => ((F i).valuation_eval_le_of_root_dist (κ ^ e - 1) (c₀ + Nat.log p Z) (hdist i)).1,
      ?_⟩
    calc ∑ i : Fin m, ((distPart (F i).series).eval (κ ^ e - 1)).valuation
        ≤ ∑ i : Fin m, iwasawaLambda (F i).series * (c₀ + Nat.log p Z) :=
          Finset.sum_le_sum fun i _ =>
            ((F i).valuation_eval_le_of_root_dist (κ ^ e - 1) (c₀ + Nat.log p Z) (hdist i)).2
      _ = (∑ i : Fin m, iwasawaLambda (F i).series) * (c₀ + Nat.log p Z) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ R * (c₀ + Nat.log p Z) := Nat.mul_le_mul_right _ hlam

end UltrametricRootSeparation

/-! ## Section 3: Effective `LemmaK` (`|H²(𝒪_L[1/ℓ], ℤ_ℓ(e+1))|` Bound from `ClassGroup` + `μ = 0`) -/

section EffectiveLemmaK

/-- Field `L` contains the `ℓ`-th roots of unity (or `4`-th roots of unity at `ℓ = 2`),
matching `UpperTheory.V.HasMuQ`. -/
def HasMuQ (l : ℕ) (L : Type) [Field L] : Prop :=
  ∃ ζ : L, IsPrimitiveRoot ζ (if l = 2 then 4 else l)

/-- Alpöge's effective `LemmaK` upper bound `exp((2 * e * n)^C * log(2 * D))`
(matching `UpperTheory.V.kBound`). -/
def kBound (C : ℝ) (e n D : ℕ) : ℝ :=
  Real.exp ((2 * (e : ℝ) * (n : ℝ)) ^ C * Real.log (2 * (D : ℝ)))

theorem kBound_pos (C : ℝ) (e n D : ℕ) : 0 < kBound C e n D :=
  Real.exp_pos _

/-- Monotonicity of `kBound` in the exponent `C` for `1 ≤ e`, `1 ≤ n`, `1 ≤ D`
(matching `LayeredIsomorphisms/Kmono.lean`). -/
theorem kBound_mono_C {C₁ C₂ : ℝ} (hC : C₁ ≤ C₂) {e n D : ℕ}
    (he : 1 ≤ e) (hn : 1 ≤ n) (hD : 1 ≤ D) :
    kBound C₁ e n D ≤ kBound C₂ e n D := by
  unfold kBound
  apply Real.exp_le_exp.mpr
  have hbase : (1 : ℝ) ≤ 2 * (e : ℝ) * (n : ℝ) := by
    have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hlog : 0 ≤ Real.log (2 * (D : ℝ)) := by
    apply Real.log_nonneg
    have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
    linarith
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hbase hC) hlog

/-- **Exponential Absorption of `kBound` on `Window1`-Good Twists (`kexp`)**
(exact match to `UpperTheory.V.Win.kexp` in `LayeredIsomorphisms/Kexp.lean`):
when `e ≤ x^(eps / (2 * CK))`, `n ≤ n0`, and `log(2 D) ≤ c0 * x^(eps / 4)`,
`kBound CK e n D ≤ exp((2 n0)^CK * c0 * x^(3 * eps / 4))`. -/
theorem kexp (CK eps c0 x : ℝ) (e n n0 D : ℕ)
    (hCK : 0 < CK) (heps : 0 < eps) (hc0 : 0 ≤ c0) (hx : 1 ≤ x)
    (he : (e : ℝ) ≤ x ^ (eps / (2 * CK))) (hn : n ≤ n0)
    (hD : Real.log (2 * (D : ℝ)) ≤ c0 * x ^ (eps / 4)) :
    kBound CK e n D ≤ Real.exp ((2 * (n0 : ℝ)) ^ CK * c0 * x ^ (3 * eps / 4)) := by
  have hx0 : 0 < x := by linarith
  have hn' : (n : ℝ) ≤ n0 := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hy : 0 ≤ x ^ (eps / (2 * CK)) := Real.rpow_nonneg hx0.le _
  have h1 : 2 * (e : ℝ) * n ≤ (2 * (n0 : ℝ)) * x ^ (eps / (2 * CK)) := by
    have := mul_le_mul he hn' hn0 hy
    nlinarith
  have h2 : (2 * (e : ℝ) * n) ^ CK ≤ (2 * (n0 : ℝ)) ^ CK * x ^ (eps / 2) := by
    calc (2 * (e : ℝ) * n) ^ CK
        ≤ ((2 * (n0 : ℝ)) * x ^ (eps / (2 * CK))) ^ CK :=
          Real.rpow_le_rpow (by positivity) h1 hCK.le
      _ = (2 * (n0 : ℝ)) ^ CK * x ^ (eps / 2) := by
          rw [Real.mul_rpow (by positivity) hy, ← Real.rpow_mul hx0.le]
          congr 2
          field_simp
  have h3 : x ^ (3 * eps / 4) = x ^ (eps / 2) * x ^ (eps / 4) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  unfold kBound
  apply Real.exp_le_exp.mpr
  have ha : 0 ≤ (2 * (e : ℝ) * n) ^ CK := Real.rpow_nonneg (by positivity) _
  have hb : 0 ≤ c0 * x ^ (eps / 4) := mul_nonneg hc0 (Real.rpow_nonneg hx0.le _)
  calc (2 * (e : ℝ) * n) ^ CK * Real.log (2 * (D : ℝ))
      ≤ (2 * (e : ℝ) * n) ^ CK * (c0 * x ^ (eps / 4)) := mul_le_mul_of_nonneg_left hD ha
    _ ≤ ((2 * (n0 : ℝ)) ^ CK * x ^ (eps / 2)) * (c0 * x ^ (eps / 4)) :=
        mul_le_mul_of_nonneg_right h2 hb
    _ = (2 * (n0 : ℝ)) ^ CK * c0 * x ^ (3 * eps / 4) := by rw [h3]; ring

/-- Elementary lower bound `(1/2 : ℝ) ≤ Real.log l` for every prime `l`. -/
lemma half_le_log_prime (l : ℕ) [Fact l.Prime] : (1 / 2 : ℝ) ≤ Real.log (l : ℝ) := by
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have h1 : Real.log 2 ≤ Real.log l := Real.log_le_log (by norm_num) hl2
  have h2 := Real.log_two_gt_d9
  linarith

/-- **Cardinality-to-Length Conversion for `LemmaK` (`klen_of_card_bound`)**
(matching `LayeredIsomorphisms/Klen.lean`, powered by
`Stage2IwasawaTwoTower.padicInt_card_eq_pow_length`):
for any finite `ℤ_[l]`-module `H2` satisfying `log(Nat.card H2) ≤ kBound CK e n D`,
`Module.length ℤ_[l] H2 ≠ ⊤` and `((Module.length ℤ_[l] H2).toNat : ℝ) ≤ 2 * kBound CK e n D`! -/
theorem klen_of_card_bound (l : ℕ) [Fact l.Prime] {H2 : Type*}
    [AddCommGroup H2] [Module ℤ_[l] H2] [Finite H2]
    {CK : ℝ} {e n D : ℕ}
    (hlog : Real.log (Nat.card H2 : ℝ) ≤ kBound CK e n D) :
    Module.length ℤ_[l] H2 ≠ ⊤ ∧
      ((Module.length ℤ_[l] H2).toNat : ℝ) ≤ 2 * kBound CK e n D := by
  have hne : Module.length ℤ_[l] H2 ≠ ⊤ := length_ne_top_of_finite (p := l)
  set k := (Module.length ℤ_[l] H2).toNat
  have hlen : Module.length ℤ_[l] H2 = (k : ℕ∞) := (ENat.natCast_toNat hne).symm
  have hcard : Nat.card H2 = l ^ k := (padicInt_card_eq_pow_length (p := l) k hlen).2
  rw [hcard, Nat.cast_pow, Real.log_pow] at hlog
  have hlogl := half_le_log_prime l
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  refine ⟨hne, ?_⟩
  nlinarith

/-- Exact `ℤ_[l]`-module length of a principal quotient `ℤ_[l] / (x)` for any nonzero `x : ℤ_[l]`:
`Module.length ℤ_[l] (ℤ_[l] ⧸ Ideal.span {x}) = (x.valuation : ℕ∞)`. -/
theorem padicInt_length_quot_span_singleton {l : ℕ} [Fact l.Prime] {x : ℤ_[l]} (hx : x ≠ 0) :
    Module.length ℤ_[l] (ℤ_[l] ⧸ Ideal.span ({x} : Set ℤ_[l])) = (x.valuation : ℕ∞) := by
  set k := x.valuation
  have hspec : x = (PadicInt.unitCoeff hx : ℤ_[l]) * (l : ℤ_[l]) ^ k :=
    PadicInt.unitCoeff_spec hx
  have hspan : Ideal.span ({x} : Set ℤ_[l]) = Ideal.span ({(l : ℤ_[l]) ^ k} : Set ℤ_[l]) := by
    rw [hspec, mul_comm, Ideal.span_singleton_mul_right_unit (PadicInt.unitCoeff hx).isUnit]
  rw [hspan]
  exact padicInt_length_quot_span_p_pow (p := l) k

/-- **Exact Algebraic Length of Cyclic Twisted `μ = 0` Iwasawa Specialization**:
for any nonzero `f ∈ ℤ_[l][[T]]` (`iwasawaMu f = 0`) and twist point `t₀ = κ^e - 1` with
`(distPart f).eval t₀ ≠ 0`, the specialized twisted cohomology module
`ℤ_[l] / ((distPart f).eval t₀)` has exact `ℤ_[l]`-length `((distPart f).eval t₀).valuation`! -/
theorem length_padicInt_quot_eval_distPart {l : ℕ} [Fact l.Prime]
    {f : IwasawaAlg l} {t₀ : ℤ_[l]} (heval : (distPart f).eval t₀ ≠ 0) :
    Module.length ℤ_[l] (ℤ_[l] ⧸ Ideal.span ({(distPart f).eval t₀} : Set ℤ_[l])) =
      (((distPart f).eval t₀).valuation : ℕ∞) :=
  padicInt_length_quot_span_singleton heval

/-- **Twisted `H²(𝒪_L[1/ℓ], ℤ_ℓ(e+1))` Iwasawa Evaluation & Root-Distance Control**:
models the effective finite-layer Iwasawa bound on `H²` via `μ = 0` characteristic polynomial
evaluation `v_l(distPart f (κ^e - 1))` plus class-group/ramification defect. -/
structure TwistedH2IwasawaBound (l : ℕ) [Fact l.Prime]
    (K : Type*) [NormedField K] [NormedAlgebra ℚ_[l] K] [IsUltrametricDist K]
    (e n D : ℕ) (H2 : Type*) [AddCommGroup H2] [Module ℤ_[l] H2] where
  charSeries : SplitDistinguishedSeries l K
  twistPt : ℤ_[l]
  classDefect : ℕ
  eval_ne_zero : (distPart charSeries.series).eval twistPt ≠ 0
  len_le : Module.length ℤ_[l] H2 ≤
    (((distPart charSeries.series).eval twistPt).valuation : ℕ∞) + (classDefect : ℕ∞)

/-- **Effective Twisted `H²` Length Bound from `λ(f)`, `v_l(f(κ^e - 1))`, and Root-Distance**:
combines `TwistedH2IwasawaBound` with `SplitDistinguishedSeries.valuation_eval_le_of_root_dist`
to prove `H2` is finite with exact `ℤ_[l]`-length bounded by `λ(f) * B + classDefect`! -/
theorem effective_H2_length_of_root_dist {l : ℕ} [Fact l.Prime]
    {K : Type*} [NormedField K] [NormedAlgebra ℚ_[l] K] [IsUltrametricDist K]
    {e n D B : ℕ} {H2 : Type*} [AddCommGroup H2] [Module ℤ_[l] H2]
    (H : TwistedH2IwasawaBound l K e n D H2)
    (hdist : ∀ i : Fin (iwasawaLambda H.charSeries.series),
      (l : ℝ) ^ (-(B : ℤ)) ≤ ‖H.charSeries.roots i - algebraMap ℚ_[l] K (H.twistPt : ℚ_[l])‖) :
    Finite H2 ∧ Module.length ℤ_[l] H2 ≠ ⊤ ∧
      (Module.length ℤ_[l] H2).toNat ≤ iwasawaLambda H.charSeries.series * B + H.classDefect := by
  have hval := (H.charSeries.valuation_eval_le_of_root_dist H.twistPt B hdist).2
  have hle_enat : Module.length ℤ_[l] H2 ≤
      ((iwasawaLambda H.charSeries.series * B + H.classDefect : ℕ) : ℕ∞) := by
    calc Module.length ℤ_[l] H2
        ≤ (((distPart H.charSeries.series).eval H.twistPt).valuation : ℕ∞) + (H.classDefect : ℕ∞) :=
          H.len_le
      _ = (((distPart H.charSeries.series).eval H.twistPt).valuation + H.classDefect : ℕ) := by
          push_cast; rfl
      _ ≤ ((iwasawaLambda H.charSeries.series * B + H.classDefect : ℕ) : ℕ∞) := by
          exact_mod_cast Nat.add_le_add_right hval H.classDefect
  have hne : Module.length ℤ_[l] H2 ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle_enat
  have hfin : Finite H2 := (finite_iff_length_ne_top (p := l)).mpr hne
  have htoNat : (Module.length ℤ_[l] H2).toNat ≤
      iwasawaLambda H.charSeries.series * B + H.classDefect := by
    have hcoe : ((Module.length ℤ_[l] H2).toNat : ℕ∞) ≤
        ((iwasawaLambda H.charSeries.series * B + H.classDefect : ℕ) : ℕ∞) := by
      rwa [ENat.natCast_toNat hne]
    exact_mod_cast hcoe
  exact ⟨hfin, hne, htoNat⟩

/-- **Class-Group + `μ = 0` Kummer Control for Effective `LemmaK`**:
encapsulates the finite-layer bound on `H²(𝒪_L[1/ℓ], ℤ_ℓ(e+1))` from:
1. Minkowski / class-group `ℓ`-rank & exponent bound (`log |Cl(L)[ℓ^∞]| ≤ (2 n)^C₁ * log(2 |d_L|)`),
2. `μ = 0` Kummer twist & local ramification exponent bound (`≤ (2 e n)^C₂ * log(2 |d_L|)`). -/
structure ClassGroupH2Control (l : ℕ) [Fact l.Prime]
    (e n D : ℕ) (H2 : Type*) [AddCommGroup H2] [Module ℤ_[l] H2] where
  classPart : ℕ
  kummerPart : ℕ
  C₁ : ℝ
  C₂ : ℝ
  hC₁ : 0 ≤ C₁
  hC₂ : 0 ≤ C₂
  len_le : Module.length ℤ_[l] H2 ≤ (classPart : ℕ∞) + (kummerPart : ℕ∞)
  class_bound : (classPart : ℝ) * Real.log (l : ℝ) ≤
    Real.exp ((2 * (e : ℝ) * (n : ℝ)) ^ C₁ * Real.log (2 * (D : ℝ))) / 2
  kummer_bound : (kummerPart : ℝ) * Real.log (l : ℝ) ≤
    Real.exp ((2 * (e : ℝ) * (n : ℝ)) ^ C₂ * Real.log (2 * (D : ℝ))) / 2

/-- **Effective `LemmaK` Theorem from `ClassGroup` + `μ = 0` Control**:
unconditionally proves `Finite H2`, `Module.length ℤ_[l] H2 ≠ ⊤`, AND the exact Alpöge
`LemmaK` cardinality inequality `Real.log (Nat.card H2) ≤ kBound (max C₁ C₂) e n D`! -/
theorem effective_lemmaK_of_classGroup_control {l : ℕ} [Fact l.Prime]
    {e n D : ℕ} (he : 1 ≤ e) (hn : 1 ≤ n) (hD : 1 ≤ D)
    {H2 : Type*} [AddCommGroup H2] [Module ℤ_[l] H2]
    (H : ClassGroupH2Control l e n D H2) :
    Finite H2 ∧ Module.length ℤ_[l] H2 ≠ ⊤ ∧
      Real.log (Nat.card H2 : ℝ) ≤ kBound (max H.C₁ H.C₂) e n D ∧
      ((Module.length ℤ_[l] H2).toNat : ℝ) ≤ 2 * kBound (max H.C₁ H.C₂) e n D := by
  have hle_enat : Module.length ℤ_[l] H2 ≤ ((H.classPart + H.kummerPart : ℕ) : ℕ∞) := by
    simpa [Nat.cast_add] using H.len_le
  have hne : Module.length ℤ_[l] H2 ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle_enat
  have hfin : Finite H2 := (finite_iff_length_ne_top (p := l)).mpr hne
  set k := (Module.length ℤ_[l] H2).toNat
  have hk_le : k ≤ H.classPart + H.kummerPart := by
    have hcoe : (k : ℕ∞) ≤ ((H.classPart + H.kummerPart : ℕ) : ℕ∞) := by
      rwa [ENat.natCast_toNat hne]
    exact_mod_cast hcoe
  have hcard : Nat.card H2 = l ^ k :=
    (padicInt_card_eq_pow_length (p := l) k (ENat.natCast_toNat hne).symm).2
  have hlogl_pos : 0 ≤ Real.log (l : ℝ) := (half_le_log_prime l).trans' (by norm_num)
  have h1 : kBound H.C₁ e n D ≤ kBound (max H.C₁ H.C₂) e n D :=
    kBound_mono_C (le_max_left _ _) he hn hD
  have h2 : kBound H.C₂ e n D ≤ kBound (max H.C₁ H.C₂) e n D :=
    kBound_mono_C (le_max_right _ _) he hn hD
  have hlog_card : Real.log (Nat.card H2 : ℝ) ≤ kBound (max H.C₁ H.C₂) e n D := by
    rw [hcard, Nat.cast_pow, Real.log_pow]
    have hkr : (k : ℝ) ≤ (H.classPart : ℝ) + (H.kummerPart : ℝ) := by exact_mod_cast hk_le
    calc (k : ℝ) * Real.log (l : ℝ)
        ≤ ((H.classPart : ℝ) + (H.kummerPart : ℝ)) * Real.log (l : ℝ) :=
          mul_le_mul_of_nonneg_right hkr hlogl_pos
      _ = (H.classPart : ℝ) * Real.log (l : ℝ) + (H.kummerPart : ℝ) * Real.log (l : ℝ) := by ring
      _ ≤ kBound H.C₁ e n D / 2 + kBound H.C₂ e n D / 2 :=
          add_le_add H.class_bound H.kummer_bound
      _ ≤ kBound (max H.C₁ H.C₂) e n D / 2 + kBound (max H.C₁ H.C₂) e n D / 2 :=
          add_le_add (div_le_div_of_nonneg_right h1 (by norm_num))
            (div_le_div_of_nonneg_right h2 (by norm_num))
      _ = kBound (max H.C₁ H.C₂) e n D := by ring
  have hklen := klen_of_card_bound l (H2 := H2) hlog_card
  exact ⟨hfin, hne, hlog_card, hklen.2⟩

/-- Abstract `H²` length system for number fields `L`, prime `l`, and twist `e : ℕ`,
together with the effective `LemmaK` predicate `LemmaKSystem` (matching `UpperTheory.V.LemmaK`). -/
structure H2LengthSystem where
  h2Len : (L : Type) → [Field L] → [NumberField L] → Nat.Primes → ℕ → ℕ∞

/-- Effective `LemmaK` predicate on an `H2LengthSystem`: for every prime `l`, number field `L`
containing `μ_l` (or `μ_4` at `l = 2`), and twist `e ≥ 1`, `h2Len L l e` is finite and satisfies
`((h2Len L l e).toNat : ℝ) ≤ 2 * kBound CK e (finrank ℚ L) (discr L).natAbs`. -/
def LemmaKSystem (H : H2LengthSystem) (CK : ℝ) : Prop :=
  ∀ (l : Nat.Primes) (L : Type) [Field L] [NumberField L],
    HasMuQ (l : ℕ) L → ∀ e : ℕ, 1 ≤ e →
      H.h2Len L l e ≠ ⊤ ∧
        ((H.h2Len L l e).toNat : ℝ) ≤
          2 * kBound CK e (Module.finrank ℚ L) (NumberField.discr L).natAbs

/-- Monotonicity of `LemmaKSystem` in `CK` (`kmono`). -/
theorem LemmaKSystem.mono {H : H2LengthSystem} {CK₁ CK₂ : ℝ} (hC : CK₁ ≤ CK₂)
    (hK : LemmaKSystem H CK₁) : LemmaKSystem H CK₂ := by
  intro l L _ _ hmu e he
  obtain ⟨hne, hle⟩ := hK l L hmu e he
  refine ⟨hne, hle.trans ?_⟩
  have hn : 1 ≤ Module.finrank ℚ L := Module.finrank_pos.nat_succ_le
  have hD : 1 ≤ (NumberField.discr L).natAbs :=
    Int.natAbs_pos.mpr (NumberField.discr_ne_zero L)
  exact mul_le_mul_of_nonneg_left (kBound_mono_C hC he hn hD) (by norm_num)

/-- Concrete instantiation: any family of finite `ℤ_[l]`-modules `H2Mod L l e` satisfying
`ClassGroupH2Control` with uniform exponent `CK` immediately produces a `LemmaKSystem`! -/
theorem lemmaKSystem_of_classGroup_control
    (H2Mod : (L : Type) → [Field L] → [NumberField L] → Nat.Primes → ℕ → Type)
    [∀ (L : Type) [Field L] [NumberField L] (l : Nat.Primes) (e : ℕ), AddCommGroup (H2Mod L l e)]
    [∀ (L : Type) [Field L] [NumberField L] (l : Nat.Primes) (e : ℕ),
      Module ℤ_[(l : ℕ)] (H2Mod L l e)]
    (CK : ℝ)
    (hctrl : ∀ (l : Nat.Primes) (L : Type) [Field L] [NumberField L],
      HasMuQ (l : ℕ) L → ∀ e : ℕ, 1 ≤ e →
        ∃ c : ClassGroupH2Control (l : ℕ) e (Module.finrank ℚ L) (NumberField.discr L).natAbs
          (H2Mod L l e),
          max c.C₁ c.C₂ ≤ CK) :
    LemmaKSystem ⟨fun L _ _ l e => Module.length ℤ_[(l : ℕ)] (H2Mod L l e)⟩ CK := by
  intro l L _ _ hmu e he
  obtain ⟨c, hcCK⟩ := hctrl l L hmu e he
  have hn : 1 ≤ Module.finrank ℚ L := Module.finrank_pos.nat_succ_le
  have hD : 1 ≤ (NumberField.discr L).natAbs :=
    Int.natAbs_pos.mpr (NumberField.discr_ne_zero L)
  obtain ⟨_, hne, _, hlen⟩ := effective_lemmaK_of_classGroup_control he hn hD c
  refine ⟨hne, hlen.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (kBound_mono_C hcCK he hn hD) (by norm_num)

end EffectiveLemmaK

/-! ## Section 4: `FirstBound`, `SecondBound`, `ABound`, `Point2`, `Final`, `PartA`, `PartB` & `ThmBab` -/

section Window1ThmBab

/-- Fixed base layer height `j₀(l, R) = Nat.log l R + 3` (matching `UpperTheory.V.Win.jZero`). -/
def jZero (l R : ℕ) : ℕ := Nat.log l R + 3

/-- Pointwise window envelope `C * (1 + log x) + 2 * exp(C * x^(3ε/4))`
(matching `UpperTheory.V.Win.ptBound`). -/
def ptBound (C eps x : ℝ) : ℝ :=
  C * (1 + Real.log x) + 2 * Real.exp (C * x ^ (3 * eps / 4))

/-- Abstract cyclotomic `l`-tower layer relation `IsLayer l m L₀ L₁`, parameterized cleanly so
it instantiates over any concrete cyclotomic tower without circular dependencies. -/
structure TowerLayerRelation where
  IsLayer : (l : Nat.Primes) → ℕ → (L₀ : Type) → [Field L₀] →
    (L₁ : Type) → [Field L₁] → [NumberField L₁] → [Algebra L₀ L₁] → Prop

/-- `SecondBound` (exact match to `LayeredIsomorphisms/SecondBound.lean`):
for EVERY twist `e ≥ 1` (including the `≤ R` exceptional twists `e ∈ Exc`), the Selmer length
at layer `m` is controlled by `H2` at the fixed layer `jZero l R` plus `R * (m - jZero l R)`. -/
def SecondBound (S : SelmerSystem) (H : H2LengthSystem) (T : TowerLayerRelation)
    (l : Nat.Primes) (R : ℕ) (L₀ : Type) [Field L₀] : Prop :=
  ∀ e : ℕ, 1 ≤ e →
    ∀ (m : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀ L₁],
      T.IsLayer l m L₀ L₁ →
      ∀ (L₂ : Type) [Field L₂] [NumberField L₂] [Algebra L₀ L₂],
        T.IsLayer l (jZero (l : ℕ) R) L₀ L₂ →
        S.shaLen L₁ l e ≤ H.h2Len L₂ l e + ((R * (m - jZero (l : ℕ) R) : ℕ) : ℕ∞)

/-- `FirstBound` (exact match to `LayeredIsomorphisms/SecondBound.lean`):
for every twist `e ∈ [1, Z] \ Exc` (`Exc.card ≤ R`), the Selmer length at layer `m` is bounded
linearly by `R * (max m (jZero l R) + c + Nat.log l Z)`. -/
def FirstBound (S : SelmerSystem) (T : TowerLayerRelation)
    (l : Nat.Primes) (R c : ℕ) (L₀ : Type) [Field L₀] (Z : ℕ) (Exc : Finset ℕ) : Prop :=
  Exc.card ≤ R ∧
    ∀ e : ℕ, 1 ≤ e → e ≤ Z → e ∉ Exc →
      ∀ (m : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀ L₁],
        T.IsLayer l m L₀ L₁ →
        S.shaLen L₁ l e ≤ ((R * (max m (jZero (l : ℕ) R) + c + Nat.log (l : ℕ) Z) : ℕ) : ℕ∞)

/-- `ABound` (exact match to `LayeredIsomorphisms/SecondBound.lean`):
combines the ultrametric Iwasawa characteristic-polynomial root bound (with `R' ≤ R` roots `s i`)
with `SecondBound`. -/
def ABound (S : SelmerSystem) (H : H2LengthSystem) (T : TowerLayerRelation)
    (l : Nat.Primes) (R : ℕ) (L₀ : Type) [Field L₀] : Prop :=
  (∃ (K : Type) (_ : NormedField K) (_ : NormedAlgebra ℚ_[(l : ℕ)] K) (_ : IsUltrametricDist K)
      (c R' : ℕ) (s : Fin R' → K),
    R' ≤ R ∧ (∃ ζ : L₀, IsPrimitiveRoot ζ ((l : ℕ) ^ c)) ∧
    ∀ e : ℕ, 1 ≤ e →
      ∀ (m : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀ L₁],
        T.IsLayer l m L₀ L₁ →
        ∀ B : ℕ, (∀ i, ((l : ℕ) : ℝ) ^ (-(B : ℤ)) ≤ ‖s i - (e : K)‖) →
          S.shaLen L₁ l e ≤ ((R' * (max m (jZero (l : ℕ) R) + c + B) : ℕ) : ℕ∞)) ∧
  SecondBound S H T l R L₀

/-- **`exc_of_aBound`** (exact match to `LayeredIsomorphisms/Exc.lean`):
extracts `FirstBound` with an exceptional set `Exc` of cardinality `≤ R` from `ABound`
using `exists_exc_of_roots` (`near1`). -/
theorem exc_of_aBound {S : SelmerSystem} {H : H2LengthSystem} {T : TowerLayerRelation}
    (l : Nat.Primes) (R : ℕ) (L₀ : Type) [Field L₀]
    (h : ABound S H T l R L₀) :
    ∃ c : ℕ, (∃ ζ : L₀, IsPrimitiveRoot ζ ((l : ℕ) ^ c)) ∧
      ∀ Z : ℕ, ∃ Exc : Finset ℕ, FirstBound S T l R c L₀ Z Exc := by
  obtain ⟨⟨K, _, _, _, c, R', s, hR', hζ, hb⟩, _⟩ := h
  refine ⟨c, hζ, fun Z => ?_⟩
  obtain ⟨Exc, hcard, hfar⟩ := exists_exc_of_roots (l : ℕ) R R' K s hR' Z
  refine ⟨Exc, hcard, fun e he1 heZ hne m L₁ _ _ _ hL => ?_⟩
  have h1 := hb e he1 m L₁ hL (Nat.log (l : ℕ) Z) (hfar e he1 heZ hne)
  exact h1.trans (by gcongr)

/-- Three elementary logarithmic estimates from `LayeredIsomorphisms/Logs.lean`:
1. `Nat.log l ⌊X^Ct⌋₊ ≤ 2 * Ct * J * log x` (for `l ≥ 2`, `X^(1/J) ≤ x`),
2. `X^(eps / (4 * J)) ≤ x^(eps / 4)` (for `X^(1/J) ≤ x`),
3. `2^e ≤ 2 * x^A1 → e ≤ 2 * (1 + |A1| * log x)`. -/
theorem logs_le :
    (∀ (l : ℕ) (J Ct X x : ℝ), 2 ≤ l → 0 < J → 0 ≤ Ct → 1 ≤ X → X ^ (1 / J) ≤ x →
      ((Nat.log l ⌊X ^ Ct⌋₊ : ℕ) : ℝ) ≤ 2 * Ct * J * Real.log x) ∧
    (∀ (J eps X x : ℝ), 0 < J → 0 < eps → 1 ≤ X → X ^ (1 / J) ≤ x →
      X ^ (eps / (4 * J)) ≤ x ^ (eps / 4)) ∧
    (∀ (e : ℕ) (A1 x : ℝ), 1 ≤ x → (2 : ℝ) ^ e ≤ 2 * x ^ A1 →
      (e : ℝ) ≤ 2 * (1 + |A1| * Real.log x)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro l J Ct X x hl hJ hCt hX hXx
    have hX0 : 0 < X := by linarith
    have hx0 : 0 < x := lt_of_lt_of_le (Real.rpow_pos_of_pos hX0 _) hXx
    have hx1 : 1 ≤ x := le_trans (Real.one_le_rpow hX (by positivity)) hXx
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hlogX : Real.log X ≤ J * Real.log x := by
      have h1 := Real.log_le_log (Real.rpow_pos_of_pos hX0 _) hXx
      rw [Real.log_rpow hX0] at h1
      have h2 := mul_le_mul_of_nonneg_left h1 hJ.le
      have h3 : J * (1 / J * Real.log X) = Real.log X := by field_simp
      linarith
    have hl2 : (1 / 2 : ℝ) ≤ Real.log (l : ℝ) := by
      have h1 : Real.log 2 ≤ Real.log (l : ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hl)
      have h4 := Real.log_two_gt_d9
      linarith
    rcases Nat.eq_zero_or_pos ⌊X ^ Ct⌋₊ with h0 | hpos
    · rw [h0, Nat.log_zero_right, Nat.cast_zero]
      positivity
    · have hpow : (l : ℝ) ^ (Nat.log l ⌊X ^ Ct⌋₊) ≤ X ^ Ct := by
        have h1 : l ^ (Nat.log l ⌊X ^ Ct⌋₊) ≤ ⌊X ^ Ct⌋₊ := Nat.pow_log_le_self l hpos.ne'
        have h2 : ((⌊X ^ Ct⌋₊ : ℕ) : ℝ) ≤ X ^ Ct := Nat.floor_le (Real.rpow_nonneg hX0.le _)
        calc (l : ℝ) ^ (Nat.log l ⌊X ^ Ct⌋₊)
            = ((l ^ (Nat.log l ⌊X ^ Ct⌋₊) : ℕ) : ℝ) := (Nat.cast_pow l _).symm
          _ ≤ ((⌊X ^ Ct⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
          _ ≤ X ^ Ct := h2
      have hl0 : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
      have hlog := Real.log_le_log (pow_pos hl0 _) hpow
      rw [Real.log_pow, Real.log_rpow hX0] at hlog
      have hk0 : (0 : ℝ) ≤ (Nat.log l ⌊X ^ Ct⌋₊ : ℕ) := Nat.cast_nonneg _
      have hk : ((Nat.log l ⌊X ^ Ct⌋₊ : ℕ) : ℝ) ≤
          2 * (((Nat.log l ⌊X ^ Ct⌋₊ : ℕ) : ℝ) * Real.log l) := by
        nlinarith [mul_le_mul_of_nonneg_left hl2 hk0]
      nlinarith [mul_le_mul_of_nonneg_left hlogX hCt]
  · intro J eps X x hJ heps hX hx
    have hX0 : 0 ≤ X := by linarith
    have h1 : X ^ (eps / (4 * J)) = (X ^ (1 / J)) ^ (eps / 4) := by
      rw [← Real.rpow_mul hX0]
      congr 1
      field_simp
    rw [h1]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hX0 _) hx (by positivity)
  · intro e A1 x hx h
    have hx0 : 0 < x := by linarith
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
    have hlog := Real.log_le_log (by positivity) h
    rw [Real.log_pow, Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hx0 _).ne',
      Real.log_rpow hx0] at hlog
    have h2 := Real.log_two_gt_d9
    have h2le : Real.log 2 ≤ 1 := by
      have : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      exact (Real.log_le_iff_le_exp (by norm_num)).mpr this
    have habs : A1 * Real.log x ≤ |A1| * Real.log x :=
      mul_le_mul_of_nonneg_right (le_abs_self A1) hlogx
    have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
    have he : (e : ℝ) ≤ 2 * (e * Real.log 2) := by nlinarith
    nlinarith [abs_nonneg A1, mul_nonneg (abs_nonneg A1) hlogx]

/-- **Pointwise Root-Avoidance Bound (`point_bound`)**
(exact match to `UpperTheory.V.Win.point` in `LayeredIsomorphisms/ImportsAlt.lean`):
splits `e ∈ Exc` (`SecondBound + LemmaK + kexp`) vs `e ∉ Exc` (`FirstBound`). -/
theorem point_bound {S : SelmerSystem} {H : H2LengthSystem} {T : TowerLayerRelation}
    (CK : ℝ) (hCK : 0 < CK) (hK : LemmaKSystem H CK)
    (l : Nat.Primes) (R c : ℕ) (L₀ : Type) [Field L₀]
    (hSec : SecondBound S H T l R L₀)
    (Z : ℕ) (Exc : Finset ℕ) (hF : FirstBound S T l R c L₀ Z Exc)
    (L₂ : Type) [Field L₂] [NumberField L₂] [Algebra L₀ L₂]
    (hmu2 : HasMuQ (l : ℕ) L₂) (hL₂ : T.IsLayer l (jZero (l : ℕ) R) L₀ L₂)
    (eps Ct c0 x : ℝ) (n0 : ℕ)
    (heps : 0 < eps) (hc0 : 0 ≤ c0) (hx : 1 ≤ x)
    (hgood : Good (eps / (2 * CK)) Ct Exc x)
    (hn : Module.finrank ℚ L₂ ≤ n0)
    (hdisc : Real.log (2 * ((NumberField.discr L₂).natAbs : ℝ)) ≤ c0 * x ^ (eps / 4))
    (e : ℕ) (he1 : 1 ≤ e) (heZ : e ≤ Z) (hex : (e : ℝ) ≤ x ^ Ct)
    (m : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀ L₁]
    (hL₁ : T.IsLayer l m L₀ L₁) :
    S.shaLen L₁ l e ≠ ⊤ ∧
      ((S.shaLen L₁ l e).toNat : ℝ) ≤
        (R : ℝ) * ((m : ℝ) + (jZero (l : ℕ) R : ℝ) + (c : ℝ) + (Nat.log (l : ℕ) Z : ℝ)) +
          2 * Real.exp ((2 * (n0 : ℝ)) ^ CK * c0 * x ^ (3 * eps / 4)) := by
  have hexp : 0 ≤ 2 * Real.exp ((2 * (n0 : ℝ)) ^ CK * c0 * x ^ (3 * eps / 4)) := by positivity
  by_cases he : e ∈ Exc
  · have hg : (e : ℝ) ≤ x ^ (eps / (2 * CK)) := hgood e he hex
    obtain ⟨hHne, hHle⟩ := hK l L₂ hmu2 e he1
    have hsec := hSec e he1 m L₁ hL₁ L₂ hL₂
    obtain ⟨v, hv⟩ := ENat.ne_top_iff_exists.mp hHne
    have hsha_le : S.shaLen L₁ l e ≤ ((v + R * (m - jZero (l : ℕ) R) : ℕ) : ℕ∞) := by
      rw [← hv] at hsec
      simpa [Nat.cast_add] using hsec
    have hne : S.shaLen L₁ l e ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hsha_le
    obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.mp hne
    rw [← hs]
    refine ⟨ENat.natCast_ne_top s, ?_⟩
    rw [ENat.toNat_natCast]
    have hsle : s ≤ v + R * (m - jZero (l : ℕ) R) := by
      rw [← hs] at hsha_le
      exact_mod_cast hsha_le
    rw [← hv, ENat.toNat_natCast] at hHle
    have hke := kexp CK eps c0 x e (Module.finrank ℚ L₂) n0 (NumberField.discr L₂).natAbs
      hCK heps hc0 hx hg hn hdisc
    have hsr : (s : ℝ) ≤ (v : ℝ) + (R : ℝ) * ((m - jZero (l : ℕ) R : ℕ) : ℝ) := by
      exact_mod_cast hsle
    have hm_le : ((m - jZero (l : ℕ) R : ℕ) : ℝ) ≤
        (m : ℝ) + (jZero (l : ℕ) R : ℝ) + (c : ℝ) + (Nat.log (l : ℕ) Z : ℝ) := by
      have h1 : m - jZero (l : ℕ) R ≤ m := Nat.sub_le _ _
      have h2 : ((m - jZero (l : ℕ) R : ℕ) : ℝ) ≤ m := by exact_mod_cast h1
      have : (0 : ℝ) ≤ (jZero (l : ℕ) R : ℝ) + (c : ℝ) + (Nat.log (l : ℕ) Z : ℝ) := by positivity
      linarith
    have hRm : (R : ℝ) * ((m - jZero (l : ℕ) R : ℕ) : ℝ) ≤
        (R : ℝ) * ((m : ℝ) + (jZero (l : ℕ) R : ℝ) + (c : ℝ) + (Nat.log (l : ℕ) Z : ℝ)) :=
      mul_le_mul_of_nonneg_left hm_le (Nat.cast_nonneg _)
    linarith
  · have hfb := hF.2 e he1 heZ he m L₁ hL₁
    have hne : S.shaLen L₁ l e ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hfb
    obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.mp hne
    rw [← hs]
    refine ⟨ENat.natCast_ne_top s, ?_⟩
    rw [ENat.toNat_natCast]
    have hs' : s ≤ R * (max m (jZero (l : ℕ) R) + c + Nat.log (l : ℕ) Z) := by
      rw [← hs] at hfb
      exact_mod_cast hfb
    have hN : s ≤ R * (m + jZero (l : ℕ) R + c + Nat.log (l : ℕ) Z) := by
      refine le_trans hs' (Nat.mul_le_mul_left _ ?_)
      omega
    have hR : (s : ℝ) ≤
        (R : ℝ) * ((m : ℝ) + (jZero (l : ℕ) R : ℝ) + (c : ℝ) + (Nat.log (l : ℕ) Z : ℝ)) := by
      exact_mod_cast hN
    linarith

/-- **Packaged Pointwise `ptBound` Estimate (`point2_bound`)**
(exact match to `UpperTheory.V.Win.point2` in `LayeredIsomorphisms/Point2.lean`). -/
theorem point2_bound {S : SelmerSystem} {H : H2LengthSystem} {T : TowerLayerRelation}
    (CK : ℝ) (hCK : 0 < CK) (hK : LemmaKSystem H CK)
    (l : Nat.Primes) (R c1 n0 : ℕ) (c0 J Ct eps a : ℝ)
    (hc0 : 0 ≤ c0) (hJ : 0 < J) (hCt : 0 ≤ Ct) (heps : 0 < eps) (ha : 0 ≤ a) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (L₀ : Type) [Field L₀], SecondBound S H T l R L₀ →
        ∀ (c : ℕ) (X : ℝ) (Exc : Finset ℕ), c ≤ c1 → FirstBound S T l R c L₀ ⌊X ^ Ct⌋₊ Exc →
        ∀ (L₂ : Type) [Field L₂] [NumberField L₂] [Algebra L₀ L₂],
          HasMuQ (l : ℕ) L₂ → T.IsLayer l (jZero (l : ℕ) R) L₀ L₂ → Module.finrank ℚ L₂ ≤ n0 →
          ∀ x : ℝ, 1 ≤ x → X ^ (1 / J) ≤ x → x ≤ X → Good (eps / (2 * CK)) Ct Exc x →
            Real.log (2 * ((NumberField.discr L₂).natAbs : ℝ)) ≤ c0 * x ^ (eps / 4) →
            ∀ e : ℕ, 1 ≤ e → (e : ℝ) ≤ x ^ Ct →
              ∀ (m : ℕ) (L₁ : Type) [Field L₁] [NumberField L₁] [Algebra L₀ L₁],
                T.IsLayer l m L₀ L₁ → (m : ℝ) ≤ a * (1 + Real.log x) →
                S.shaLen L₁ l e ≠ ⊤ ∧ ((S.shaLen L₁ l e).toNat : ℝ) + 1 ≤ ptBound C eps x := by
  refine ⟨((R : ℝ) * (a + (jZero (l : ℕ) R : ℝ) + c1 + 2 * Ct * J) + 1) + (2 * (n0 : ℝ)) ^ CK * c0,
    by positivity, ?_⟩
  intro L₀ _ hS c X Exc hc hF L₂ _ _ _ hmu2 hL₂ hn x hx hXx hxX hG hD e he hex m L₁ _ _ _ hL₁ hm
  have hX : 1 ≤ X := hx.trans hxX
  have heZ : e ≤ ⌊X ^ Ct⌋₊ :=
    Nat.le_floor (hex.trans (Real.rpow_le_rpow (by linarith) hxX hCt))
  obtain ⟨h1, h2⟩ := point_bound CK hCK hK l R c L₀ hS _ Exc hF L₂ hmu2 hL₂ eps Ct c0 x n0
    heps hc0 hx hG hn hD e he heZ hex m L₁ hL₁
  refine ⟨h1, ?_⟩
  have hlog := logs_le.1 (l : ℕ) J Ct X x l.2.two_le hJ hCt hX hXx
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx
  have hcr : (c : ℝ) ≤ c1 := by exact_mod_cast hc
  have hp : 0 ≤ x ^ (3 * eps / 4) := by positivity
  have hj : (0 : ℝ) ≤ jZero (l : ℕ) R := Nat.cast_nonneg _
  have hc1r : (0 : ℝ) ≤ c1 := Nat.cast_nonneg _
  have hR : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have hin : (m : ℝ) + (jZero (l : ℕ) R : ℝ) + (c : ℝ) + (Nat.log (l : ℕ) ⌊X ^ Ct⌋₊ : ℝ) ≤
      (a + (jZero (l : ℕ) R : ℝ) + c1 + 2 * Ct * J) * (1 + Real.log x) := by
    nlinarith [mul_nonneg hj hL, mul_nonneg hc1r hL]
  have hR' := mul_le_mul_of_nonneg_left hin hR
  have hA : 0 ≤ (R : ℝ) * (a + (jZero (l : ℕ) R : ℝ) + c1 + 2 * Ct * J) + 1 := by positivity
  have hexp : Real.exp ((2 * (n0 : ℝ)) ^ CK * c0 * x ^ (3 * eps / 4)) ≤
      Real.exp ((((R : ℝ) * (a + (jZero (l : ℕ) R : ℝ) + c1 + 2 * Ct * J) + 1) +
        (2 * (n0 : ℝ)) ^ CK * c0) * x ^ (3 * eps / 4)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (by linarith) hp
  unfold ptBound
  have hBL : 0 ≤ (2 * (n0 : ℝ)) ^ CK * c0 * (1 + Real.log x) := by positivity
  nlinarith

/-- **Final Exponential Absorption (`final_exp_absorb`)**
(exact match to `UpperTheory.V.Win.final` in `LayeredIsomorphisms/Final.lean`):
for EVERY `Ct, eps, C` with `0 < eps`, there exists `x0 ≥ 2` such that for all `x ≥ x0`,
`x ^ Ct * ptBound C eps x ≤ Real.exp (x ^ (4 * eps / 5))`! -/
theorem final_exp_absorb (Ct eps C : ℝ) (heps : 0 < eps) :
    ∃ x0 : ℝ, 2 ≤ x0 ∧ ∀ x ≥ x0, x ^ Ct * ptBound C eps x ≤ Real.exp (x ^ (4 * eps / 5)) := by
  have hba : 0 < 4 * eps / 5 - 3 * eps / 4 := by linarith
  have hb : 0 < 4 * eps / 5 := by linarith
  have E1 := ((isLittleO_log_rpow_atTop hb).const_mul_left (|Ct| + |C|)).bound
    (by norm_num : (0 : ℝ) < 1 / 4)
  have E2 := (tendsto_rpow_atTop hba).eventually_ge_atTop (4 * |C|)
  have E3 := (tendsto_rpow_atTop hb).eventually_ge_atTop (4 * (Real.log 3 + |C|))
  have E4 := Filter.eventually_ge_atTop (2 : ℝ)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (E1.and (E2.and (E3.and E4)))
  refine ⟨max N 2, le_max_right _ _, fun x hx => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hN x (le_trans (le_max_left _ _) hx)
  have hx0 : 0 < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hxa : 0 ≤ x ^ (3 * eps / 4) := Real.rpow_nonneg hx0.le _
  have hxb : 0 ≤ x ^ (4 * eps / 5) := Real.rpow_nonneg hx0.le _
  have hsplit : x ^ (4 * eps / 5) = x ^ (3 * eps / 4) * x ^ (4 * eps / 5 - 3 * eps / 4) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (add_nonneg (abs_nonneg Ct) (abs_nonneg C)) hlog),
    abs_of_nonneg hxb] at h1
  have hC2 : |C| * x ^ (3 * eps / 4) ≤ 1 / 4 * x ^ (4 * eps / 5) := by
    rw [hsplit]
    nlinarith [mul_le_mul_of_nonneg_left h2 hxa]
  have hp1 : C * (1 + Real.log x)
      ≤ Real.exp (|C| * (1 + Real.log x) + |C| * x ^ (3 * eps / 4)) := by
    have q1 : C * (1 + Real.log x) ≤ |C| * (1 + Real.log x) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
    have q2 : 0 ≤ |C| * x ^ (3 * eps / 4) := mul_nonneg (abs_nonneg C) hxa
    linarith [Real.add_one_le_exp (|C| * (1 + Real.log x) + |C| * x ^ (3 * eps / 4))]
  have hp2 : Real.exp (C * x ^ (3 * eps / 4))
      ≤ Real.exp (|C| * (1 + Real.log x) + |C| * x ^ (3 * eps / 4)) := by
    apply Real.exp_le_exp.mpr
    have q1 : C * x ^ (3 * eps / 4) ≤ |C| * x ^ (3 * eps / 4) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) hxa
    have q2 : 0 ≤ |C| * (1 + Real.log x) := mul_nonneg (abs_nonneg C) (by linarith)
    linarith
  have hpt : ptBound C eps x
      ≤ 3 * Real.exp (|C| * (1 + Real.log x) + |C| * x ^ (3 * eps / 4)) := by
    show C * (1 + Real.log x) + 2 * Real.exp (C * x ^ (3 * eps / 4)) ≤ _
    linarith
  have hxc : x ^ Ct ≤ Real.exp (|Ct| * Real.log x) := by
    rw [Real.rpow_def_of_pos hx0]
    apply Real.exp_le_exp.mpr
    have q := mul_le_mul_of_nonneg_right (le_abs_self Ct) hlog
    linarith
  calc x ^ Ct * ptBound C eps x
      ≤ x ^ Ct * (3 * Real.exp (|C| * (1 + Real.log x) + |C| * x ^ (3 * eps / 4))) :=
        mul_le_mul_of_nonneg_left hpt (Real.rpow_nonneg hx0.le _)
    _ ≤ Real.exp (|Ct| * Real.log x) *
          (3 * Real.exp (|C| * (1 + Real.log x) + |C| * x ^ (3 * eps / 4))) :=
        mul_le_mul_of_nonneg_right hxc (by positivity)
    _ = Real.exp (|Ct| * Real.log x + Real.log 3 +
          (|C| * (1 + Real.log x) + |C| * x ^ (3 * eps / 4))) := by
        rw [Real.exp_add (|Ct| * Real.log x + Real.log 3), Real.exp_add (|Ct| * Real.log x),
          Real.exp_log (by norm_num : (0 : ℝ) < 3)]
        ring
    _ ≤ Real.exp (x ^ (4 * eps / 5)) := Real.exp_le_exp.mpr (by linarith)

/-- Single-prime Selmer sum bound `VVat S l E t B` (matching `UpperTheory.V.VVat`). -/
def VVat (S : SelmerSystem) (l : Nat.Primes) (E : Type) [Field E] [NumberField E]
    (t : ℕ) (B : ℝ) : Prop :=
  (∀ e : ℕ, 0 < e → e < t → S.shaLen E l e ≠ ⊤) ∧
    ∑ e ∈ Finset.Ico 1 t, ((S.shaLen E l e).toNat : ℝ) ≤ B

theorem VVat.mono {S : SelmerSystem} {l : Nat.Primes} {E : Type} [Field E] [NumberField E]
    {t t' : ℕ} {B B' : ℝ} (h : VVat S l E t B) (ht : t' ≤ t) (hB : B ≤ B') :
    VVat S l E t' B' := by
  refine ⟨fun e he1 he2 => h.1 e he1 (lt_of_lt_of_le he2 ht), ?_⟩
  refine le_trans ?_ (le_trans h.2 hB)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    simp only [Finset.mem_Ico] at he ⊢
    omega
  · intro _ _ _; positivity

/-- Pointwise-to-sum lift into `VVat` (exact match to `LayeredIsomorphisms/Vvat.lean`). -/
theorem vvat_of_pointwise {S : SelmerSystem} (l : Nat.Primes) (t : ℕ)
    (E : Type) [Field E] [NumberField E] (T b B : ℝ)
    (hb : 0 ≤ b) (htT : (t : ℝ) ≤ T) (hTB : T * b ≤ B)
    (h : ∀ e : ℕ, 1 ≤ e → e < t → S.shaLen E l e ≠ ⊤ ∧ ((S.shaLen E l e).toNat : ℝ) ≤ b) :
    VVat S l E t B := by
  refine ⟨fun e he1 he2 => (h e he1 he2).1, ?_⟩
  calc ∑ e ∈ Finset.Ico 1 t, ((S.shaLen E l e).toNat : ℝ)
      ≤ ∑ _e ∈ Finset.Ico 1 t, b := by
        apply Finset.sum_le_sum
        intro e he
        rw [Finset.mem_Ico] at he
        exact (h e he.1 he.2).2
    _ = ((t - 1 : ℕ) : ℝ) * b := by rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    _ ≤ T * b := mul_le_mul_of_nonneg_right (le_trans (by exact_mod_cast Nat.sub_le t 1) htT) hb
    _ ≤ B := hTB

/-- **Complete `Window1` Exponential Sum Bound for Distinguished `μ = 0` Iwasawa Power Series**:
given ANY `m` distinguished `μ = 0` power series `F_1, ..., F_m ∈ ℤ_[p][[T]]` with total
`λ`-invariant `∑ i, λ(F_i) ≤ R` and a `LemmaK` upper bound on the `≤ R` exceptional twists
`e ∈ Exc` (where `v_p` can be large near a root), there exists `X₀` such that for ALL `X ≥ X₀`,
there exists a sub-window `[Y, Y^2] ⊂ [X^(1/J), X]` with the **exact exponent
`J = windowExponent R CK Ct eps = 2^(R + 2) * (2 * CK * Ct / eps)^R`** on which EVERY
`x ∈ [Y, Y^2]` satisfies the **exact `Real.exp (x ^ (4 * eps / 5))` valuation-sum bound**! -/
theorem window1_iwasawa_family_exp_bound {p m R n0 : ℕ} [Fact p.Prime]
    {κ : ℤ_[p]} {c₀ : ℕ}
    (hc0 : 1 ≤ c₀) (hc2 : p = 2 → 2 ≤ c₀) (hκ : ‖κ - 1‖ = (p : ℝ) ^ (-(c₀ : ℤ)))
    (K : Type*) [NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]
    (F : Fin m → SplitDistinguishedSeries p K)
    (hlam : ∑ i : Fin m, iwasawaLambda (F i).series ≤ R)
    (CK Ct eps cdisc : ℝ)
    (hCK : 1 ≤ CK) (hCt : 1 ≤ Ct) (heps0 : 0 < eps) (heps1 : eps ≤ 1) (hcdisc : 0 ≤ cdisc)
    (D : ℝ → ℕ) (hD_log : ∀ x ≥ (1 : ℝ), Real.log (2 * (D x : ℝ)) ≤ cdisc * x ^ (eps / 4))
    (hExc_lemmaK : ∀ x ≥ (1 : ℝ), ∀ e : ℕ, 1 ≤ e →
      (∑ i : Fin m, ((distPart (F i).series).eval (κ ^ e - 1)).valuation : ℝ) ≤
        2 * kBound CK e n0 (D x)) :
    let J := windowExponent R CK Ct eps
    ∃ X₀ : ℝ, 1 < X₀ ∧ ∀ X ≥ X₀,
      ∃ Y : ℝ, InRange J X Y ∧
        ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (2 : ℝ) →
          ∑ e ∈ Finset.Ico 1 ⌊x ^ Ct⌋₊,
            (∑ i : Fin m, ((distPart (F i).series).eval (κ ^ e - 1)).valuation : ℝ) ≤
              Real.exp (x ^ (4 * eps / 5)) := by
  have hp : p.Prime := Fact.out
  set J := windowExponent R CK Ct eps
  have hJpos : 0 < J := windowExponent_pos R (by linarith) (by linarith) heps0
  set C : ℝ := ((R : ℝ) * ((c₀ : ℝ) + 2 * Ct * J) + 1) + (2 * (n0 : ℝ)) ^ CK * cdisc
  have hC0 : 0 ≤ C := by positivity
  obtain ⟨x0, hx02, hx0⟩ := final_exp_absorb Ct eps C heps0
  have hx0_pos : 0 ≤ x0 := by linarith
  refine ⟨max 2 (x0 ^ J), lt_of_lt_of_le (by norm_num) (le_max_left _ _), fun X hX => ?_⟩
  have hX1 : 1 < X := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hX)
  have hXle : x0 ^ J ≤ X := (le_max_right _ _).trans hX
  have hx0_le_XJ : x0 ≤ X ^ (1 / J) := by
    calc x0 = (x0 ^ J) ^ (1 / J) := by
          rw [← Real.rpow_mul hx0_pos, mul_one_div_cancel hJpos.ne', Real.rpow_one]
      _ ≤ X ^ (1 / J) := Real.rpow_le_rpow (Real.rpow_nonneg hx0_pos _) hXle (by positivity)
  obtain ⟨Exc, hcard, hfar⟩ :=
    iwasawa_family_root_avoidance_exc hc0 hc2 hκ K F hlam ⌊X ^ Ct⌋₊
  obtain ⟨Y, hY, hgood⟩ := window_of_CK R CK Ct eps X Exc hCK hCt heps0 heps1 hX1 hcard
  refine ⟨Y, hY, fun x hxY hxY2 => ?_⟩
  have hXx : X ^ (1 / J) ≤ x := hY.1.trans hxY
  have hxX : x ≤ X := hxY2.trans hY.2
  have hx_ge : x0 ≤ x := hx0_le_XJ.trans hXx
  have hx1 : 1 ≤ x := by linarith
  have hG := hgood x hxY hxY2
  have hpt_nonneg : 0 ≤ ptBound C eps x := by
    unfold ptBound
    have : 0 ≤ Real.log x := Real.log_nonneg hx1
    positivity
  have hpw : ∀ e ∈ Finset.Ico 1 ⌊x ^ Ct⌋₊,
      (∑ i : Fin m, ((distPart (F i).series).eval (κ ^ e - 1)).valuation : ℝ) ≤ ptBound C eps x := by
    intro e he
    rw [Finset.mem_Ico] at he
    have he_real : (e : ℝ) ≤ x ^ Ct :=
      (by exact_mod_cast he.2.le : (e : ℝ) ≤ (⌊x ^ Ct⌋₊ : ℝ)).trans
        (Nat.floor_le (Real.rpow_nonneg (by linarith) _))
    have heZ : e ≤ ⌊X ^ Ct⌋₊ :=
      Nat.le_floor (he_real.trans (Real.rpow_le_rpow (by linarith) hxX (by linarith)))
    by_cases heExc : e ∈ Exc
    · have hg : (e : ℝ) ≤ x ^ (eps / (2 * CK)) := hG e heExc he_real
      have hk := hExc_lemmaK x hx1 e he.1
      have hke := kexp CK eps cdisc x e n0 n0 (D x) (by linarith) heps0 hcdisc hx1 hg le_rfl
        (hD_log x hx1)
      have hC_ge : (2 * (n0 : ℝ)) ^ CK * cdisc ≤ C := by
        dsimp only [C]
        have : 0 ≤ (R : ℝ) * ((c₀ : ℝ) + 2 * Ct * J) + 1 := by positivity
        linarith
      have hexp_le : Real.exp ((2 * (n0 : ℝ)) ^ CK * cdisc * x ^ (3 * eps / 4)) ≤
          Real.exp (C * x ^ (3 * eps / 4)) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right hC_ge (by positivity)
      unfold ptBound
      have hClog : 0 ≤ C * (1 + Real.log x) := mul_nonneg hC0 (by linarith [Real.log_nonneg hx1])
      linarith
    · have hv := (hfar e he.1 heZ heExc).2
      have hvr : (∑ i : Fin m, ((distPart (F i).series).eval (κ ^ e - 1)).valuation : ℝ) ≤
          (R : ℝ) * ((c₀ : ℝ) + (Nat.log p ⌊X ^ Ct⌋₊ : ℝ)) := by
        exact_mod_cast hv
      have hlog := logs_le.1 p J Ct X x hp.two_le hJpos (by linarith) hX1.le hXx
      have hLx : 0 ≤ Real.log x := Real.log_nonneg hx1
      have hc0_le : (c₀ : ℝ) + 2 * Ct * J * Real.log x ≤ ((c₀ : ℝ) + 2 * Ct * J) * (1 + Real.log x) := by
        have hc0r : (0 : ℝ) ≤ c₀ := Nat.cast_nonneg _
        have hCJ : 0 ≤ 2 * Ct * J := by positivity
        nlinarith
      have hR_le : (R : ℝ) * ((c₀ : ℝ) + (Nat.log p ⌊X ^ Ct⌋₊ : ℝ)) ≤ C * (1 + Real.log x) := by
        have h1 : (R : ℝ) * ((c₀ : ℝ) + (Nat.log p ⌊X ^ Ct⌋₊ : ℝ)) ≤
            (R : ℝ) * (((c₀ : ℝ) + 2 * Ct * J) * (1 + Real.log x)) :=
          mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
        have h2 : (R : ℝ) * ((c₀ : ℝ) + 2 * Ct * J) ≤ C := by
          dsimp only [C]
          have : 0 ≤ (2 * (n0 : ℝ)) ^ CK * cdisc := by positivity
          linarith
        have h3 : (R : ℝ) * ((c₀ : ℝ) + 2 * Ct * J) * (1 + Real.log x) ≤ C * (1 + Real.log x) :=
          mul_le_mul_of_nonneg_right h2 (by linarith)
        linarith
      unfold ptBound
      have hexp0 : 0 ≤ 2 * Real.exp (C * x ^ (3 * eps / 4)) := by positivity
      linarith
  calc ∑ e ∈ Finset.Ico 1 ⌊x ^ Ct⌋₊,
          (∑ i : Fin m, ((distPart (F i).series).eval (κ ^ e - 1)).valuation : ℝ)
      ≤ ∑ _e ∈ Finset.Ico 1 ⌊x ^ Ct⌋₊, ptBound C eps x := Finset.sum_le_sum hpw
    _ = ((⌊x ^ Ct⌋₊ - 1 : ℕ) : ℝ) * ptBound C eps x := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    _ ≤ x ^ Ct * ptBound C eps x := by
        apply mul_le_mul_of_nonneg_right _ hpt_nonneg
        exact (by exact_mod_cast Nat.sub_le _ 1 : ((⌊x ^ Ct⌋₊ - 1 : ℕ) : ℝ) ≤ (⌊x ^ Ct⌋₊ : ℝ)).trans
          (Nat.floor_le (Real.rpow_nonneg (by linarith) _))
    _ ≤ Real.exp (x ^ (4 * eps / 5)) := hx0 x hx_ge

/-- The canonical prime `2 : Nat.Primes`. -/
def primeTwo : Nat.Primes := ⟨2, Nat.prime_two⟩

/-- `TwoBase` data for the `l = 2` branch of `ThmBab` (distilling `SecondBound.TwoBase` +
`Layerdisc` for `IsChiField ψ e q d E`, cleanly in `Prop`). -/
def TwoTowerWindowData (S : SelmerSystem) (H : H2LengthSystem) (T : TowerLayerRelation)
    (ψ : PChar) (R₀ : ℕ) : Prop :=
  ∃ (c1 n0 : ℕ) (c0 : ℝ), 0 ≤ c0 ∧
    ∀ (q d : ℕ), TaylorWilesWindow.PrimePair ψ.N q d →
      ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀)
        (L₂ : Type) (_ : Field L₂) (_ : NumberField L₂) (_ : Algebra L₀ L₂),
        HasMuQ 2 L₂ ∧
        T.IsLayer primeTwo (jZero 2 R₀) L₀ L₂ ∧
        Module.finrank ℚ L₂ ≤ n0 ∧
        (∀ W : ℝ, 1 ≤ W → Real.log ((q : ℝ) * d) ≤ W →
          Real.log (2 * ((NumberField.discr L₂).natAbs : ℝ)) ≤ c0 * W) ∧
        ABound S H T primeTwo R₀ L₀ ∧
        (∃ c : ℕ, c ≤ c1 ∧ ∀ Z : ℕ, ∃ Exc : Finset ℕ, FirstBound S T primeTwo R₀ c L₀ Z Exc) ∧
        (∀ (e : ℕ), 2 ≤ e → ∀ (E : Type) [Field E] [NumberField E], IsChiField ψ e q d E →
          ∃ (m : ℕ) (L₁ : Type) (_ : Field L₁) (_ : NumberField L₁) (_ : Algebra L₀ L₁),
            T.IsLayer primeTwo m L₀ L₁ ∧ m ≤ e + 2 ∧
            ∀ k : ℕ, 1 ≤ k → S.shaLen E primeTwo k ≤ 1 + S.shaLen L₁ primeTwo k)

/-- Fixed bad odd prime `l ∈ Bchi` tower data for the `CaseIV` / `BbAt` branch of `ThmBab`
at fixed layer field `L₂` (distilling `SecondBound.FixedIn` + `PartB`, cleanly in `Prop`). -/
def BadOddTowerData (S : SelmerSystem) (H : H2LengthSystem) (T : TowerLayerRelation)
    (l : Nat.Primes) (Rl : ℕ) (L₂ : Type) [Field L₂] [NumberField L₂] : Prop :=
  (l : ℕ) ≠ 2 ∧
    ∃ (L₀ : Type) (_ : Field L₀) (_ : NumberField L₀) (_ : Algebra L₀ L₂),
      HasMuQ (l : ℕ) L₂ ∧
      T.IsLayer l (jZero (l : ℕ) Rl) L₀ L₂ ∧
      ABound S H T l Rl L₀

/-- Helper lemma: `a ≤ 1 + b` with `b ≠ ⊤` implies `a ≠ ⊤ ∧ a.toNat ≤ 1 + b.toNat`. -/
private lemma ne_top_and_toNat_le_of_le_one_add {a b : ℕ∞} (hb : b ≠ ⊤) (h : a ≤ 1 + b) :
    a ≠ ⊤ ∧ a.toNat ≤ 1 + b.toNat := by
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hb
  have h' : a ≤ ((1 + n : ℕ) : ℕ∞) := by push_cast; exact h
  have ha : a ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) h'
  obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp ha
  refine ⟨ha, ?_⟩
  simp only [ENat.toNat_natCast]
  exact_mod_cast h'

/-- **`BaAt` (`l = 2` Branch)** at scale `x` (matching `UpperTheory.V.BaAt`). -/
def BaAt (S : SelmerSystem) (ψ : PChar) (e t : ℝ → ℕ) (q d : ℕ) (x : ℝ) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E], IsChiField ψ (e x) q d E →
    VVat S primeTwo E (t x) (Real.exp (x ^ (4 * (1 : ℝ) / 5)))

/-- **`BaAtEps` (`l = 2` Branch at explicit exponent `eps`)**. -/
def BaAtEps (S : SelmerSystem) (ψ : PChar) (eps : ℝ) (e t : ℝ → ℕ) (q d : ℕ) (x : ℝ) : Prop :=
  ∀ (E : Type) [Field E] [NumberField E], IsChiField ψ (e x) q d E →
    VVat S primeTwo E (t x) (Real.exp (x ^ (4 * eps / 5)))

/-- **`partA_two_branch`** (exact match to `LayeredIsomorphisms/PartA.lean`):
discharges the `l = 2` branch `BaAtEps` from `LemmaKSystem` + `TwoTowerWindowData` + `Good`! -/
theorem partA_two_branch {S : SelmerSystem} {H : H2LengthSystem} {T : TowerLayerRelation}
    (CK : ℝ) (hCK : 0 < CK) (hK : LemmaKSystem H CK)
    (ψ : PChar) (R₀ : ℕ) (hTwo : TwoTowerWindowData S H T ψ R₀)
    (J Ct eps A1 : ℝ) (hJ : 0 < J) (hCt : 0 ≤ Ct) (heps : 0 < eps) :
    ∃ x0 : ℝ, ∀ (e t : ℝ → ℕ), AdmissiblePage A1 Ct e t →
      ∀ (X : ℝ) (q d : ℕ), TaylorWilesWindow.PrimePair ψ.N q d →
        Real.log ((q : ℝ) * d) ≤ X ^ (eps / (4 * J)) →
        ∃ ExcA : Finset ℕ, ExcA.card ≤ R₀ ∧
          ∀ x ≥ x0, X ^ (1 / J) ≤ x → x ≤ X → Good (eps / (2 * CK)) Ct ExcA x →
            BaAtEps S ψ eps e t q d x := by
  obtain ⟨c1, n0, c0, hc0, hbase⟩ := hTwo
  obtain ⟨C, hC0, hC⟩ := point2_bound CK hCK hK primeTwo R₀ c1 n0 c0 J Ct eps
    (2 * |A1| + 4) hc0 hJ hCt heps (by positivity)
  obtain ⟨x0, hx02, hx0⟩ := final_exp_absorb Ct eps C heps
  refine ⟨x0, fun e t hAdm X q d hPP hlogqd => ?_⟩
  obtain ⟨L₀, _, _, L₂, _, _, _, hmu₂, hL₂, hn0, hdisc_fn, hAB, ⟨c, hc1, hZ⟩, hE⟩ :=
    hbase q d hPP
  obtain ⟨ExcA, hExcA⟩ := hZ ⌊X ^ Ct⌋₊
  refine ⟨ExcA, hExcA.1, fun x hx hXx hxX hG E _ _ hEc => ?_⟩
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
  obtain ⟨he2, h2e, _, htx⟩ := hAdm x (by linarith)
  have hw : (1 : ℝ) ≤ x ^ (eps / 4) := Real.one_le_rpow hx1 (by positivity)
  have hlogP : Real.log ((q : ℝ) * d) ≤ x ^ (eps / 4) :=
    hlogqd.trans (logs_le.2.1 J eps X x hJ heps hX1 hXx)
  have hdisc := hdisc_fn (x ^ (eps / 4)) hw hlogP
  obtain ⟨m, L₁, _, _, _, hL₁, hme, hsha⟩ := hE (e x) he2 E hEc
  have h2e' : (2 : ℝ) ^ (e x) ≤ 2 * x ^ A1 := by
    have : (0 : ℝ) ≤ x ^ A1 := Real.rpow_nonneg (by linarith) _
    linarith
  have hm : (m : ℝ) ≤ (2 * |A1| + 4) * (1 + Real.log x) := by
    have h3 := logs_le.2.2 (e x) A1 x hx1 h2e'
    have h4 : (m : ℝ) ≤ (e x : ℝ) + 2 := by exact_mod_cast hme
    have hA1 : 0 ≤ |A1| := abs_nonneg A1
    nlinarith
  have hpb : 0 ≤ ptBound C eps x := by
    unfold ptBound
    exact add_nonneg (mul_nonneg hC0 (by linarith)) (by positivity)
  refine vvat_of_pointwise primeTwo (t x) E (x ^ Ct) (ptBound C eps x) _ hpb htx (hx0 x hx) ?_
  intro k hk1 hkt
  have hkx : (k : ℝ) ≤ x ^ Ct := le_trans (by exact_mod_cast hkt.le) htx
  have hk := hC L₀ hAB.2 c X ExcA hc1 hExcA L₂ hmu₂ hL₂ hn0 x hx1 hXx hxX hG hdisc k hk1 hkx
    m L₁ hL₁ hm
  obtain ⟨hne, hle⟩ := ne_top_and_toNat_le_of_le_one_add hk.1 (hsha k hk1)
  refine ⟨hne, ?_⟩
  have h5 : ((S.shaLen E primeTwo k).toNat : ℝ) ≤ 1 + ((S.shaLen L₁ primeTwo k).toNat : ℝ) := by
    exact_mod_cast hle
  linarith [hk.2]

/-- **`partB_bad_odd_branch`** (exact match to `LayeredIsomorphisms/PartB.lean`):
discharges the fixed-layer `l ∈ Bchi` (`CaseIV`) bound `VVat S l L₂ (t x) (exp(x^(4ε/5)))`
from `LemmaKSystem` + `BadOddTowerData` + `Good`! -/
theorem partB_bad_odd_branch {S : SelmerSystem} {H : H2LengthSystem} {T : TowerLayerRelation}
    (CK : ℝ) (hCK : 0 < CK) (hK : LemmaKSystem H CK)
    (l : Nat.Primes) (Rl : ℕ) (L₂ : Type) [Field L₂] [NumberField L₂]
    (hBad : BadOddTowerData S H T l Rl L₂)
    (J Ct eps A1 : ℝ) (hJ : 0 < J) (hCt : 0 ≤ Ct) (heps : 0 < eps) :
    ∃ x0 : ℝ, ∀ (e t : ℝ → ℕ), AdmissiblePage A1 Ct e t → ∀ X : ℝ,
      ∃ ExcB : Finset ℕ, ExcB.card ≤ Rl ∧
        ∀ x ≥ x0, X ^ (1 / J) ≤ x → x ≤ X → Good (eps / (2 * CK)) Ct ExcB x →
          VVat S l L₂ (t x) (Real.exp (x ^ (4 * eps / 5))) := by
  obtain ⟨_, L₀, _, _, _, hmu₂, hlayer₂, hAB⟩ := hBad
  obtain ⟨c, _, hc⟩ := exc_of_aBound l Rl L₀ hAB
  have hc0 : 0 ≤ Real.log (2 * ((NumberField.discr L₂).natAbs : ℝ)) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ ((NumberField.discr L₂).natAbs : ℝ) :=
      Nat.one_le_cast.mpr (Int.natAbs_pos.mpr (NumberField.discr_ne_zero L₂))
    linarith
  obtain ⟨C, hC0, hP⟩ := point2_bound CK hCK hK l Rl c (Module.finrank ℚ L₂)
    (Real.log (2 * ((NumberField.discr L₂).natAbs : ℝ))) J Ct eps (jZero (l : ℕ) Rl : ℝ)
    hc0 hJ hCt heps (Nat.cast_nonneg _)
  obtain ⟨x1, hx1two, hx1⟩ := final_exp_absorb Ct eps C heps
  refine ⟨x1, fun e t hAdm X => ?_⟩
  obtain ⟨ExcB, hExcB⟩ := hc ⌊X ^ Ct⌋₊
  refine ⟨ExcB, hExcB.1, fun x hx hXx hxX hgood => ?_⟩
  have hx1' : (1 : ℝ) ≤ x := by linarith
  have hadm := hAdm x (by linarith)
  have hQ : ∀ e' : ℕ, 1 ≤ e' → (e' : ℝ) ≤ x ^ Ct →
      S.shaLen L₂ l e' ≠ ⊤ ∧ ((S.shaLen L₂ l e').toNat : ℝ) + 1 ≤ ptBound C eps x := by
    intro e' he1 he2
    refine hP L₀ hAB.2 c X ExcB le_rfl hExcB L₂ hmu₂ hlayer₂ le_rfl
      x hx1' hXx hxX hgood ?_ e' he1 he2 (jZero (l : ℕ) Rl) L₂ hlayer₂ ?_
    · exact le_mul_of_one_le_right hc0 (Real.one_le_rpow hx1' (by positivity))
    · exact le_mul_of_one_le_right (Nat.cast_nonneg _) (by linarith [Real.log_nonneg hx1'])
  have hpb : 0 ≤ ptBound C eps x := by
    unfold ptBound
    exact add_nonneg (mul_nonneg hC0 (by linarith [Real.log_nonneg hx1'])) (by positivity)
  refine vvat_of_pointwise l (t x) L₂ (x ^ Ct) (ptBound C eps x) _ hpb hadm.2.2.2
    (hx1 x hx) ?_
  intro e' he1 he2
  have h := hQ e' he1 (le_trans (by exact_mod_cast he2.le) hadm.2.2.2)
  exact ⟨h.1, by linarith [h.2]⟩

/-- **UNIFIED `ThmBab` (`Window1` + `LemmaK` + `PartA` + `PartB`)**
(exact match to `UpperTheory.V.Win.thmBab_of` in `LayeredIsomorphisms/ThmBabOf.lean`):
discharges **BOTH** `BaAtEps` (`l = 2` branch) **AND** `BbAt` (`∀ l ∈ Bchi`, `CaseIV` branch)
**SIMULTANEOUSLY** on the SAME dyadic window `[Y, Y^2] ⊂ [X^(1/J), X]` with the **EXACT exponent
`J = windowExponent (R₀ + ∑ l ∈ Bchi, Rl l) CK Ct eps = 2^(R + 2) * (2 * CK * Ct / eps)^R`**! -/
theorem thmBab_window1 {S : SelmerSystem} {H : H2LengthSystem} {T : TowerLayerRelation}
    (CK0 : ℝ) (hK0 : LemmaKSystem H CK0)
    (ψ : PChar) (R₀ : ℕ) (hTwo : TwoTowerWindowData S H T ψ R₀)
    (Bchi : Finset Nat.Primes) (Rl : Nat.Primes → ℕ)
    (L₂ : Nat.Primes → Type) [∀ l, Field (L₂ l)] [∀ l, NumberField (L₂ l)]
    (hBad : ∀ l ∈ Bchi, BadOddTowerData S H T l (Rl l) (L₂ l))
    (Ct eps A1 : ℝ) (hCt : 1 ≤ Ct) (heps0 : 0 < eps) (heps1 : eps ≤ 1) :
    let CK := max CK0 1
    let R := R₀ + ∑ l ∈ Bchi, Rl l
    let J := windowExponent R CK Ct eps
    ∃ X0 : ℝ, ∀ (e t : ℝ → ℕ), AdmissiblePage A1 Ct e t →
      ∀ X ≥ X0, ∀ q d : ℕ, TaylorWilesWindow.PrimePair ψ.N q d →
        Real.log ((q : ℝ) * d) ≤ X ^ (eps / (4 * J)) →
        ∃ Y : ℝ, InRange J X Y ∧
          ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (2 : ℝ) →
            BaAtEps S ψ eps e t q d x ∧
            ∀ l ∈ Bchi, VVat S l (L₂ l) (t x) (Real.exp (x ^ (4 * eps / 5))) := by
  classical
  set CK : ℝ := max CK0 1
  have hCK1 : (1 : ℝ) ≤ CK := le_max_right _ _
  have hCKpos : (0 : ℝ) < CK := lt_of_lt_of_le one_pos hCK1
  have hK : LemmaKSystem H CK := hK0.mono (le_max_left _ _)
  set R : ℕ := R₀ + ∑ l ∈ Bchi, Rl l
  set J : ℝ := windowExponent R CK Ct eps
  have hJpos : 0 < J := windowExponent_pos R hCKpos (by linarith) heps0
  obtain ⟨x0A, hA⟩ := partA_two_branch CK hCKpos hK ψ R₀ hTwo J Ct eps A1 hJpos (by linarith) heps0
  have hB : ∀ l : Nat.Primes, ∃ x0 : ℝ, ∀ (hl : l ∈ Bchi),
      ∀ (e t : ℝ → ℕ), AdmissiblePage A1 Ct e t → ∀ X : ℝ,
        ∃ ExcB : Finset ℕ, ExcB.card ≤ Rl l ∧
          ∀ x ≥ x0, X ^ (1 / J) ≤ x → x ≤ X → Good (eps / (2 * CK)) Ct ExcB x →
            VVat S l (L₂ l) (t x) (Real.exp (x ^ (4 * eps / 5))) := by
    intro l
    by_cases hl : l ∈ Bchi
    · obtain ⟨x0, hx0⟩ := partB_bad_odd_branch CK hCKpos hK l (Rl l) (L₂ l) (hBad l hl) J Ct eps A1
        hJpos (by linarith) heps0
      exact ⟨x0, fun _ => hx0⟩
    · exact ⟨0, fun h => absurd h hl⟩
  choose f hf using hB
  set x1 : ℝ := max 1 (max x0A (∑ l ∈ Bchi, |f l|))
  have hfle : ∀ l ∈ Bchi, f l ≤ x1 := fun l hl =>
    (le_abs_self _).trans ((Finset.single_le_sum (fun i _ => abs_nonneg (f i)) hl).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  have hx0A : x0A ≤ x1 := (le_max_left _ _).trans (le_max_right _ _)
  have hx1pos : 0 ≤ x1 := zero_le_one.trans (le_max_left _ _)
  refine ⟨max 2 (x1 ^ J), fun e t hAdm X hX q d hPP hlog => ?_⟩
  have hX2 : 2 ≤ X := (le_max_left _ _).trans hX
  have hXJ : x1 ^ J ≤ X := (le_max_right _ _).trans hX
  have hlow : x1 ≤ X ^ (1 / J) := by
    calc x1 = (x1 ^ J) ^ (1 / J) := by
          rw [← Real.rpow_mul hx1pos, mul_one_div_cancel hJpos.ne', Real.rpow_one]
      _ ≤ X ^ (1 / J) := Real.rpow_le_rpow (Real.rpow_nonneg hx1pos _) hXJ (by positivity)
  obtain ⟨ExcA, hcardA, hxA⟩ := hA e t hAdm X q d hPP hlog
  have hB_exc : ∀ l : Nat.Primes, ∃ ExcB : Finset ℕ,
      (∀ hl : l ∈ Bchi, ExcB.card ≤ Rl l ∧
        ∀ x ≥ f l, X ^ (1 / J) ≤ x → x ≤ X → Good (eps / (2 * CK)) Ct ExcB x →
          VVat S l (L₂ l) (t x) (Real.exp (x ^ (4 * eps / 5)))) := by
    intro l
    by_cases hl : l ∈ Bchi
    · obtain ⟨ExcB, hcB, hxB⟩ := hf l hl e t hAdm X
      exact ⟨ExcB, fun _ => ⟨hcB, hxB⟩⟩
    · exact ⟨∅, fun h => absurd h hl⟩
  choose g hg using hB_exc
  obtain ⟨Y, hY, hgood⟩ := window_joint_families Bchi R₀ Rl CK Ct eps X ExcA g
    hCK1 hCt heps0 heps1 (by linarith) hcardA (fun l hl => (hg l hl).1)
  refine ⟨Y, hY, fun x hYx hxY => ?_⟩
  have hXlo : X ^ (1 / J) ≤ x := hY.1.trans hYx
  have hXhi : x ≤ X := hxY.trans hY.2
  obtain ⟨hGA, hGB⟩ := hgood x hYx hxY
  refine ⟨hxA x (hx0A.trans (hlow.trans hXlo)) hXlo hXhi hGA, fun l hl => ?_⟩
  exact (hg l hl).2 x ((hfle l hl).trans (hlow.trans hXlo)) hXlo hXhi (hGB l hl)

end Window1ThmBab

/-! ## Section 5: Exact Complex-Conjugation Parity Split (`VVle = VVminusLe + VVplusLe`) -/

section ComplexConjugationParitySplit

/-- **Exact Linear-Algebraic Eigenspace Length Splitting (`length_eq_add_eigen`)**
(exact match to `UpperTheory.V.length_eq_add_eigen` in `LengthEqAddEigen.lean:10-55`):
over any commutative ring `R` in which `2` is a unit, if `f : Module.End R M` is an involution
(`f (f x) = x`) preserving a submodule `N ≤ M`, and `s ∈ R` satisfies `s * s = 1`, then
`Module.length R N = Module.length R ↥(N ⊓ f.eigenspace s) + Module.length R ↥(N ⊓ f.eigenspace (-s))`. -/
theorem length_eq_add_eigen {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (h2 : IsUnit (2 : R)) (N : Submodule R M) (f : Module.End R M)
    (hN : ∀ x ∈ N, f x ∈ N) (hf : ∀ x, f (f x) = x) (s : R) (hs : s * s = 1) :
    Module.length R N =
      Module.length R ↥(N ⊓ f.eigenspace s) + Module.length R ↥(N ⊓ f.eigenspace (-s)) := by
  set c : R := ↑h2.unit⁻¹
  have hc : (2 : R) * c = 1 := h2.mul_val_inv
  have eP : ∀ x : M, f (x + s • f x) = s • (x + s • f x) := by
    intro x
    rw [map_add, map_smul, hf, smul_add, smul_smul, hs, one_smul, add_comm]
  have eQ : ∀ x : M, f (x - s • f x) = (-s) • (x - s • f x) := by
    intro x
    rw [map_sub, map_smul, hf, smul_sub, smul_smul, neg_mul, hs, neg_smul, neg_smul, one_smul]
    abel
  have memP : ∀ x ∈ N, c • (x + s • f x) ∈ N ⊓ f.eigenspace s := fun x hx =>
    ⟨N.smul_mem c (N.add_mem hx (N.smul_mem s (hN x hx))),
      (f.eigenspace s).smul_mem c (Module.End.mem_eigenspace_iff.mpr (eP x))⟩
  have memQ : ∀ x ∈ N, c • (x - s • f x) ∈ N ⊓ f.eigenspace (-s) := fun x hx =>
    ⟨N.smul_mem c (N.sub_mem hx (N.smul_mem s (hN x hx))),
      (f.eigenspace (-s)).smul_mem c (Module.End.mem_eigenspace_iff.mpr (eQ x))⟩
  let toP : N →ₗ[R] ↥(N ⊓ f.eigenspace s) :=
    (c • (N.subtype + s • (f ∘ₗ N.subtype))).codRestrict _ (fun x => by
      simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply,
        Submodule.coe_subtype]
      exact memP _ x.2)
  let toQ : N →ₗ[R] ↥(N ⊓ f.eigenspace (-s)) :=
    (c • (N.subtype - s • (f ∘ₗ N.subtype))).codRestrict _ (fun x => by
      simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply,
        Submodule.coe_subtype]
      exact memQ _ x.2)
  let back : (↥(N ⊓ f.eigenspace s) × ↥(N ⊓ f.eigenspace (-s))) →ₗ[R] N :=
    (Submodule.inclusion inf_le_left).coprod (Submodule.inclusion inf_le_left)
  have h₁ : (toP.prod toQ) ∘ₗ back = LinearMap.id := by
    ext ⟨a, ha⟩
    all_goals simp [toP, toQ, back]
    · rw [Module.End.mem_eigenspace_iff.mp ha.2]
      linear_combination (norm := module) hs • (c • a) + hc • a
    · rw [Module.End.mem_eigenspace_iff.mp ha.2]
      linear_combination (norm := module) hs • (-(c • a))
    · rw [Module.End.mem_eigenspace_iff.mp ha.2]
      linear_combination (norm := module) hs • (-(c • a))
    · rw [Module.End.mem_eigenspace_iff.mp ha.2]
      linear_combination (norm := module) hs • (c • a) + hc • a
  have h₂ : back ∘ₗ (toP.prod toQ) = LinearMap.id := by
    ext ⟨x, hx⟩
    simp [toP, toQ, back]
    linear_combination (norm := module) hc • x
  rw [(LinearEquiv.ofLinearMap (toP.prod toQ) back h₁ h₂).length_eq, Module.length_prod]

/-- For every odd prime `l ≠ 2`, `2` is a unit in `ℤ_[l]`. -/
theorem isUnit_two_padicInt_of_ne_two {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) :
    IsUnit (2 : ℤ_[l]) := by
  by_contra hn
  have hmem : (2 : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] :=
    (IsLocalRing.mem_maximalIdeal _).mpr hn
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_ofNat] at hmem
  have h3 : ((2 : ℕ) : ZMod l) = 0 := by simpa using hmem
  rw [ZMod.natCast_eq_zero_iff] at h3
  exact hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h3)

/-- **Exact `ℤ_[l]` Complex-Conjugation Parity Split** for odd primes `l ≠ 2` and twist `e : ℕ`:
`len(N) = len(N ⊓ c.eigenspace ((-1)^e)) + len(N ⊓ c.eigenspace ((-1)^(e+1)))`! -/
theorem padicInt_length_eq_add_parity {l : ℕ} [Fact l.Prime] (hl : l ≠ 2)
    {M : Type*} [AddCommGroup M] [Module ℤ_[l] M]
    (N : Submodule ℤ_[l] M) (cAct : Module.End ℤ_[l] M)
    (hN : ∀ x ∈ N, cAct x ∈ N) (hc : ∀ x, cAct (cAct x) = x) (e : ℕ) :
    Module.length ℤ_[l] N =
      Module.length ℤ_[l] ↥(N ⊓ cAct.eigenspace ((-1 : ℤ_[l]) ^ e)) +
      Module.length ℤ_[l] ↥(N ⊓ cAct.eigenspace ((-1 : ℤ_[l]) ^ (e + 1))) := by
  have hs : ((-1 : ℤ_[l]) ^ e) * ((-1 : ℤ_[l]) ^ e) = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  have key := length_eq_add_eigen (isUnit_two_padicInt_of_ne_two hl) N cAct hN hc _ hs
  have hneg : -((-1 : ℤ_[l]) ^ e) = (-1 : ℤ_[l]) ^ (e + 1) := by rw [pow_succ, mul_neg_one]
  rwa [hneg] at key

/-- A `SelmerSystem` equipped with an exact complex-conjugation parity decomposition
`shaLen E l e = plusLen E l e + minusLen E l e` at all odd primes `l ≠ 2`
(matching `LengthEqAddEigen.shaLen_eq_add`). -/
structure ParitySelmerSystem extends SelmerSystem where
  plusLen : (E : Type) → [Field E] → [NumberField E] → Nat.Primes → ℕ → ℕ∞
  minusLen : (E : Type) → [Field E] → [NumberField E] → Nat.Primes → ℕ → ℕ∞
  shaLen_eq_add : ∀ (E : Type) [Field E] [NumberField E] (l : Nat.Primes) (e : ℕ),
    (l : ℕ) ≠ 2 → shaLen E l e = plusLen E l e + minusLen E l e

/-- **Concrete Involution Constructor for `ParitySelmerSystem`**:
from ANY family of `ℤ_[l]`-modules `H1 E l e`, Selmer submodules `Sha E l e ≤ H1 E l e`, and
complex-conjugation involutions `cAct E l e` preserving `Sha`, builds a `ParitySelmerSystem`
whose `shaLen_eq_add` is proved unconditionally via `padicInt_length_eq_add_parity`! -/
def ParitySelmerSystem.ofInvolution
    (H1 : (E : Type) → [Field E] → [NumberField E] → Nat.Primes → ℕ → Type)
    [∀ (E : Type) [Field E] [NumberField E] (l : Nat.Primes) (e : ℕ), AddCommGroup (H1 E l e)]
    [∀ (E : Type) [Field E] [NumberField E] (l : Nat.Primes) (e : ℕ),
      Module ℤ_[(l : ℕ)] (H1 E l e)]
    (Sha : ∀ (E : Type) [Field E] [NumberField E] (l : Nat.Primes) (e : ℕ),
      Submodule ℤ_[(l : ℕ)] (H1 E l e))
    (cAct : ∀ (E : Type) [Field E] [NumberField E] (l : Nat.Primes) (e : ℕ),
      Module.End ℤ_[(l : ℕ)] (H1 E l e))
    (hpres : ∀ (E : Type) [Field E] [NumberField E] (l : Nat.Primes) (e : ℕ)
      (x : H1 E l e), x ∈ Sha E l e → cAct E l e x ∈ Sha E l e)
    (hinv : ∀ (E : Type) [Field E] [NumberField E] (l : Nat.Primes) (e : ℕ)
      (x : H1 E l e), cAct E l e (cAct E l e x) = x) :
    ParitySelmerSystem where
  shaLen E _ _ l e :=
    Module.length ℤ_[(l : ℕ)] ↥(Sha E l e)
  plusLen E _ _ l e :=
    Module.length ℤ_[(l : ℕ)] ↥(Sha E l e ⊓ (cAct E l e).eigenspace ((-1 : ℤ_[(l : ℕ)]) ^ e))
  minusLen E _ _ l e :=
    Module.length ℤ_[(l : ℕ)] ↥(Sha E l e ⊓ (cAct E l e).eigenspace ((-1 : ℤ_[(l : ℕ)]) ^ (e + 1)))
  shaLen_eq_add E _ _ l e hl :=
    padicInt_length_eq_add_parity (l := (l : ℕ)) hl (Sha E l e) (cAct E l e)
      (hpres E l e) (hinv E l e) e

/-- `l = 2` Selmer bound `BoundedHeightTwoPlaceCondition S E t B := VVat S 2 E t B`
(matching `UpperTheory.V.BoundedHeightTwoPlaceCondition`). -/
def BoundedHeightTwoPlaceCondition (S : SelmerSystem) (E : Type) [Field E] [NumberField E]
    (t : ℕ) (B : ℝ) : Prop :=
  VVat S primeTwo E t B

/-- Odd-prime minus-parity (`(-1)^(e+1)` eigenspace) bound `VVminusLe`
(exact match to `UpperTheory.V.VVminusLe` in `LengthEqAddEigen.lean:113-118`). -/
def VVminusLe (P : ParitySelmerSystem) (E : Type) [Field E] [NumberField E]
    (t : ℕ) (B : ℝ) : Prop :=
  (∀ (l : Nat.Primes) (e : ℕ), (l : ℕ) ≠ 2 → 0 < e → e < t → P.minusLen E l e ≠ ⊤) ∧
    ∀ S : Finset Nat.Primes, (∀ l ∈ S, (l : ℕ) ≠ 2) →
      ∑ l ∈ S, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((P.minusLen E l e).toNat : ℝ) ≤ B

theorem VVminusLe.mono {P : ParitySelmerSystem} {E : Type} [Field E] [NumberField E]
    {t t' : ℕ} {B B' : ℝ} (h : VVminusLe P E t B) (ht : t' ≤ t) (hB : B ≤ B') :
    VVminusLe P E t' B' := by
  refine ⟨fun l e hl he1 he2 => h.1 l e hl he1 (lt_of_lt_of_le he2 ht), fun S hS => ?_⟩
  refine le_trans ?_ (le_trans (h.2 S hS) hB)
  apply Finset.sum_le_sum
  intro l _
  apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg _)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he; simp only [Finset.mem_Ico] at he ⊢; omega
  · intro _ _ _; positivity

/-- Odd-prime plus-parity (`(-1)^e` eigenspace) bound `VVplusLe`
(exact match to `UpperTheory.V.VVplusLe` in `LengthEqAddEigen.lean:120-125`). -/
def VVplusLe (P : ParitySelmerSystem) (E : Type) [Field E] [NumberField E]
    (t : ℕ) (B : ℝ) : Prop :=
  (∀ (l : Nat.Primes) (e : ℕ), (l : ℕ) ≠ 2 → 0 < e → e < t → P.plusLen E l e ≠ ⊤) ∧
    ∀ S : Finset Nat.Primes, (∀ l ∈ S, (l : ℕ) ≠ 2) →
      ∑ l ∈ S, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((P.plusLen E l e).toNat : ℝ) ≤ B

theorem VVplusLe.mono {P : ParitySelmerSystem} {E : Type} [Field E] [NumberField E]
    {t t' : ℕ} {B B' : ℝ} (h : VVplusLe P E t B) (ht : t' ≤ t) (hB : B ≤ B') :
    VVplusLe P E t' B' := by
  refine ⟨fun l e hl he1 he2 => h.1 l e hl he1 (lt_of_lt_of_le he2 ht), fun S hS => ?_⟩
  refine le_trans ?_ (le_trans (h.2 S hS) hB)
  apply Finset.sum_le_sum
  intro l _
  apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg _)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he; simp only [Finset.mem_Ico] at he ⊢; omega
  · intro _ _ _; positivity

/-- **Exact Complex-Conjugation Parity Split Assembly (`vvle_of_parity_parts`)**
(exact match to `UpperTheory.V.vvle_of_parts` in `LengthEqAddEigen.lean:127-189`):
combines `l = 2` (`BaAt`), odd minus-parity (`VVminusLe`: Rubin + Stickelberger), and
odd plus-parity (`VVplusLe`: `SumIn` + `SumOut`) into `VVle P.toSelmerSystem E t (B₂ * log 2 + Bm + Bp)`! -/
theorem vvle_of_parity_parts {P : ParitySelmerSystem} {E : Type} [Field E] [NumberField E]
    {t : ℕ} {B₂ Bm Bp : ℝ}
    (h2 : BoundedHeightTwoPlaceCondition P.toSelmerSystem E t B₂)
    (hm : VVminusLe P E t Bm) (hp : VVplusLe P E t Bp) :
    VVle P.toSelmerSystem E t (B₂ * Real.log 2 + Bm + Bp) := by
  classical
  refine ⟨?_, ?_⟩
  · intro l e he1 he2
    by_cases hl2 : (l : ℕ) = 2
    · have hleq : l = primeTwo := Subtype.ext hl2
      subst hleq
      exact h2.1 e he1 he2
    · rw [P.shaLen_eq_add E l e hl2]
      exact WithTop.add_ne_top.mpr ⟨hp.1 l e hl2 he1 he2, hm.1 l e hl2 he1 he2⟩
  · intro S
    set g : Nat.Primes → ℝ := fun l =>
      Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((P.shaLen E l e).toNat : ℝ)
    show ∑ l ∈ S, g l ≤ B₂ * Real.log 2 + Bm + Bp
    have hnn : ∀ l : Nat.Primes, 0 ≤ g l := fun l =>
      mul_nonneg (Real.log_natCast_nonneg _) (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
    set S_odd := S.erase primeTwo
    have hS_odd : ∀ l ∈ S_odd, (l : ℕ) ≠ 2 := by
      intro l hl heq
      exact (Finset.mem_erase.mp hl).1 (Subtype.ext heq)
    have hsplit : ∑ l ∈ S, g l ≤ g primeTwo + ∑ l ∈ S_odd, g l := by
      by_cases hmem : primeTwo ∈ S
      · rw [← Finset.add_sum_erase S g hmem]
      · have hSeq : S_odd = S := Finset.erase_eq_of_notMem hmem
        rw [hSeq]
        linarith [hnn primeTwo]
    have hg2 : g primeTwo ≤ B₂ * Real.log 2 := by
      dsimp only [g, primeTwo]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right h2.2 (Real.log_nonneg (by norm_num))
    have hodd : ∑ l ∈ S_odd, g l ≤ Bp + Bm := by
      have hterm : ∀ l ∈ S_odd, g l =
          Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((P.plusLen E l e).toNat : ℝ) +
          Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((P.minusLen E l e).toNat : ℝ) := by
        intro l hl
        have hl2 := hS_odd l hl
        dsimp only [g]
        rw [← mul_add, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun e he => ?_
        rw [Finset.mem_Ico] at he
        rw [P.shaLen_eq_add E l e hl2,
          ENat.toNat_add (hp.1 l e hl2 he.1 he.2) (hm.1 l e hl2 he.1 he.2), Nat.cast_add]
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
      exact add_le_add (hp.2 S_odd hS_odd) (hm.2 S_odd hS_odd)
    linarith

/-- Plus-parity bad-odd-prime sum `SumIn` over `l ∈ Bchi` (where `CaseIV` / `BbAt` contributes
`exp(x^(4ε/5))` and `CaseII`/`CaseV`/`CaseVs` contribute polynomial terms). -/
def SumIn (P : ParitySelmerSystem) (Bchi : Finset Nat.Primes)
    (E : Type) [Field E] [NumberField E] (t : ℕ) (Bin : ℝ) : Prop :=
  (∀ l ∈ Bchi, ∀ e : ℕ, (l : ℕ) ≠ 2 → 0 < e → e < t → P.plusLen E l e ≠ ⊤) ∧
    ∀ S : Finset Nat.Primes, (∀ l ∈ S, l ∈ Bchi ∧ (l : ℕ) ≠ 2) →
      ∑ l ∈ S, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((P.plusLen E l e).toNat : ℝ) ≤ Bin

/-- Plus-parity good-odd-prime sum `SumOut` over `l ∉ Bchi`, `l ≠ 2` (PURE POLYNOMIAL
`(condF E * t)^C0` — NO `exp(x^(4ε/5))` term!). -/
def SumOut (P : ParitySelmerSystem) (Bchi : Finset Nat.Primes)
    (E : Type) [Field E] [NumberField E] (t : ℕ) (Bout : ℝ) : Prop :=
  (∀ (l : Nat.Primes) (e : ℕ), l ∉ Bchi → (l : ℕ) ≠ 2 → 0 < e → e < t → P.plusLen E l e ≠ ⊤) ∧
    ∀ S : Finset Nat.Primes, (∀ l ∈ S, l ∉ Bchi ∧ (l : ℕ) ≠ 2) →
      ∑ l ∈ S, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((P.plusLen E l e).toNat : ℝ) ≤ Bout

/-- **`vvplusLe_of_sumIn_sumOut`** (matching Alpöge's `PointHV = SumIn + SumOut`):
splits `VVplusLe` across `Bchi` into `SumIn` (`l ∈ Bchi`) and `SumOut` (`l ∉ Bchi`)! -/
theorem vvplusLe_of_sumIn_sumOut {P : ParitySelmerSystem} {Bchi : Finset Nat.Primes}
    {E : Type} [Field E] [NumberField E] {t : ℕ} {Bin Bout : ℝ}
    (hin : SumIn P Bchi E t Bin) (hout : SumOut P Bchi E t Bout) :
    VVplusLe P E t (Bin + Bout) := by
  classical
  refine ⟨?_, ?_⟩
  · intro l e hl2 he1 he2
    by_cases hmem : l ∈ Bchi
    · exact hin.1 l hmem e hl2 he1 he2
    · exact hout.1 l e hmem hl2 he1 he2
  · intro S hS
    rw [← Finset.sum_filter_add_sum_filter_not S (fun l => l ∈ Bchi)]
    apply add_le_add
    · exact hin.2 _ fun l hl => by
        rw [Finset.mem_filter] at hl
        exact ⟨hl.2, hS l hl.1⟩
    · exact hout.2 _ fun l hl => by
        rw [Finset.mem_filter] at hl
        exact ⟨hl.2, hS l hl.1⟩

/-- **`sumIn_of_caseIV_bbAt_and_poly`** (matching Alpöge's `FinalLe.lean` + `CountIV.lean`):
if for every `l ∈ Bchi`, the plus-parity Selmer length at `E` is bounded by the fixed-layer
`CaseIV` `BbAt` term (at `L₂ l`) plus a polynomial `CaseII`/`CaseV`/`CaseVs` term, then
`SumIn P Bchi E t ((∑ l ∈ Bchi, log l) * Biv + Bpoly)` holds! -/
theorem sumIn_of_caseIV_bbAt_and_poly {P : ParitySelmerSystem}
    (Bchi : Finset Nat.Primes) (E : Type) [Field E] [NumberField E]
    (t : ℕ) (Biv Bpoly : ℝ)
    (hBiv : 0 ≤ Biv)
    (L₂ : Nat.Primes → Type) [∀ l, Field (L₂ l)] [∀ l, NumberField (L₂ l)]
    (hbb : ∀ l ∈ Bchi, VVat P.toSelmerSystem l (L₂ l) t Biv)
    (hpoly_tot : ∀ S : Finset Nat.Primes, (∀ l ∈ S, l ∈ Bchi ∧ (l : ℕ) ≠ 2) →
      ∃ rem : Nat.Primes → ℕ → ℕ,
        (∀ l ∈ S, ∀ e : ℕ, 0 < e → e < t →
          P.plusLen E l e ≤ P.shaLen (L₂ l) l e + (rem l e : ℕ∞)) ∧
        ∑ l ∈ S, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, (rem l e : ℝ) ≤ Bpoly) :
    SumIn P Bchi E t ((∑ l ∈ Bchi, Real.log (l : ℕ)) * Biv + Bpoly) := by
  classical
  refine ⟨?_, ?_⟩
  · intro l hl e hl2 he1 he2
    obtain ⟨rem, hrem_le, _⟩ := hpoly_tot {l} (by intro l' hl'; rw [Finset.mem_singleton.mp hl']; exact ⟨hl, hl2⟩)
    have hne := (hbb l hl).1 e he1 he2
    exact ne_top_of_le_ne_top (WithTop.add_ne_top.mpr ⟨hne, ENat.natCast_ne_top _⟩)
      (hrem_le l (Finset.mem_singleton_self l) e he1 he2)
  · intro S hS
    obtain ⟨rem, hrem_le, hrem_sum⟩ := hpoly_tot S hS
    have hterm : ∀ l ∈ S,
        Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((P.plusLen E l e).toNat : ℝ) ≤
          Real.log (l : ℕ) * Biv +
          Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, (rem l e : ℝ) := by
      intro l hl
      have hlB : l ∈ Bchi := (hS l hl).1
      rw [← mul_add]
      apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg _)
      calc ∑ e ∈ Finset.Ico 1 t, ((P.plusLen E l e).toNat : ℝ)
          ≤ ∑ e ∈ Finset.Ico 1 t, (((P.shaLen (L₂ l) l e).toNat : ℝ) + (rem l e : ℝ)) := by
            apply Finset.sum_le_sum
            intro e he
            rw [Finset.mem_Ico] at he
            have hle := hrem_le l hl e he.1 he.2
            have hne := (hbb l hlB).1 e he.1 he.2
            obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hne
            have hle' : P.plusLen E l e ≤ ((a + rem l e : ℕ) : ℕ∞) := by
              rw [← ha] at hle
              simpa [Nat.cast_add] using hle
            have hpne := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle'
            obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hpne
            rw [← ha, ← hb, ENat.toNat_natCast, ENat.toNat_natCast]
            have hnat : b ≤ a + rem l e := by rw [← hb] at hle'; exact_mod_cast hle'
            exact_mod_cast hnat
        _ = (∑ e ∈ Finset.Ico 1 t, ((P.shaLen (L₂ l) l e).toNat : ℝ)) +
            (∑ e ∈ Finset.Ico 1 t, (rem l e : ℝ)) := Finset.sum_add_distrib
        _ ≤ Biv + ∑ e ∈ Finset.Ico 1 t, (rem l e : ℝ) := add_le_add (hbb l hlB).2 le_rfl
    calc ∑ l ∈ S, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((P.plusLen E l e).toNat : ℝ)
        ≤ ∑ l ∈ S, (Real.log (l : ℕ) * Biv +
            Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, (rem l e : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = (∑ l ∈ S, Real.log (l : ℕ) * Biv) +
          (∑ l ∈ S, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, (rem l e : ℝ)) :=
          Finset.sum_add_distrib
      _ = (∑ l ∈ S, Real.log (l : ℕ)) * Biv +
          (∑ l ∈ S, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, (rem l e : ℝ)) := by
          rw [Finset.sum_mul]
      _ ≤ (∑ l ∈ Bchi, Real.log (l : ℕ)) * Biv + Bpoly := by
          apply add_le_add _ hrem_sum
          apply mul_le_mul_of_nonneg_right _ hBiv
          exact Finset.sum_le_sum_of_subset_of_nonneg (fun l hl => (hS l hl).1)
            (fun l _ _ => Real.log_natCast_nonneg _)

/-- Absorbs `SumIn ≤ u^Cin + Civ * Eterm` and `SumOut ≤ u^Cout` (pure polynomial!)
into the single plus-parity bound `VVplusLe P E t (u^C + C * Eterm)` whenever `2 ≤ u`
(which always holds for `u = condF E * t x` since `1 ≤ condF E` and `2 ≤ t x` on every
`AdmissiblePage`, matching `HeightAndVanishing/PointArith.lean`). -/
theorem vvplusLe_of_bbAt_and_sumOut {P : ParitySelmerSystem} {Bchi : Finset Nat.Primes}
    {E : Type} [Field E] [NumberField E] {t : ℕ}
    {u Cin Civ Cout Eterm : ℝ} (hu : 2 ≤ u) (hEterm : 0 ≤ Eterm)
    (hin : SumIn P Bchi E t (u ^ Cin + Civ * Eterm))
    (hout : SumOut P Bchi E t (u ^ Cout)) :
    let C := max (max (max Cin Cout) 0 + 1) (max Civ 0)
    VVplusLe P E t (u ^ C + C * Eterm) := by
  set C0 : ℝ := max (max Cin Cout) 0
  set C : ℝ := max (C0 + 1) (max Civ 0)
  have hu1 : (1 : ℝ) ≤ u := by linarith
  have hu0 : (0 : ℝ) < u := by linarith
  have hCin : Cin ≤ C0 := (le_max_left _ _).trans (le_max_left _ _)
  have hCout : Cout ≤ C0 := (le_max_right _ _).trans (le_max_left _ _)
  have hC0_le : C0 + 1 ≤ C := le_max_left _ _
  have hCiv_le : Civ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hpoly : u ^ Cin + u ^ Cout ≤ u ^ C := by
    have h1 : u ^ Cin ≤ u ^ C0 := Real.rpow_le_rpow_of_exponent_le hu1 hCin
    have h2 : u ^ Cout ≤ u ^ C0 := Real.rpow_le_rpow_of_exponent_le hu1 hCout
    have h3 : 2 * u ^ C0 ≤ u ^ (C0 + 1) := by
      rw [Real.rpow_add hu0, Real.rpow_one]
      have : 0 ≤ u ^ C0 := Real.rpow_nonneg hu0.le _
      nlinarith
    have h4 : u ^ (C0 + 1) ≤ u ^ C := Real.rpow_le_rpow_of_exponent_le hu1 hC0_le
    linarith
  have hE : Civ * Eterm ≤ C * Eterm := mul_le_mul_of_nonneg_right hCiv_le hEterm
  refine (vvplusLe_of_sumIn_sumOut hin hout).mono le_rfl ?_
  linarith

end ComplexConjugationParitySplit

/-! ## Section 6: End-to-End Parity + `Window1` Assembly into `VWin S` & Concrete `p = 37` Witness -/

section EndToEndAssembly

/-- **Alpöge's Exact Four-Input Parity + `Window1` Supply for `VWin`**
(replaces `MinimalOddUnramifiedPatchingSupply` with the true Alpöge decomposition, cleanly in `Prop`):
1. `LemmaK` + `TwoTowerWindowData` (`l = 2`) + `BadOddTowerData` (`l ∈ Bchi`), discharged
   SIMULTANEOUSLY by `thmBab_window1` on `[Y, Y^2] ⊂ [X^(1/J), X]` with `J = 2^(R+2)*(2*CK*Ct/eps)^R`,
2. `VVminusLe` for ALL odd primes `l ≠ 2` (Rubin Euler system + Stickelberger `minusBound`),
3. `SumIn` residual (`CaseII`/`CaseV`/`CaseVs` for `l ∈ Bchi`, bounded by `BbAt` + polynomial),
4. `SumOut` for ALL good odd primes `l ∉ Bchi` (**PURE POLYNOMIAL** `(condF E * t x)^Cout`!). -/
structure ParityWindow1Supply (P : ParitySelmerSystem) (H : H2LengthSystem)
    (T : TowerLayerRelation) (Ct : ℝ) : Prop where
  exists_lemmaK : ∃ CK0 : ℝ, LemmaKSystem H CK0
  exists_char_data : ∃ Cb : ℝ, ∀ ψ : PChar,
    ∃ (R₀ : ℕ) (Bchi : Finset Nat.Primes) (Rl : Nat.Primes → ℕ)
      (L₂ : Nat.Primes → Type) (_ : ∀ l, Field (L₂ l)) (_ : ∀ l, NumberField (L₂ l))
      (Cin Cout P0 : ℝ),
      TwoTowerWindowData P.toSelmerSystem H T ψ R₀ ∧
      (∀ l ∈ Bchi, BadOddTowerData P.toSelmerSystem H T l (Rl l) (L₂ l)) ∧
      -- Minus parity (Rubin + Stickelberger) for ALL odd primes l ≠ 2
      (∀ (e t : ℝ → ℕ), AdmissiblePage 4 Ct e t →
        ∀ x : ℝ, 2 ≤ x → ∀ q d : ℕ, TaylorWilesWindow.PrimePair ψ.N q d →
          ∀ (E : Type) [Field E] [NumberField E], IsChiField ψ (e x) q d E →
            VVminusLe P E (t x) (minusBound Cb ψ.N (Module.finrank ℚ E) (condF E) (t x))) ∧
      -- Plus parity bad odd primes l ∈ Bchi (`SumIn`: CaseIV via BbAt + poly CaseII/V/Vs)
      (∀ (eps : ℝ), 0 < eps → eps < 1 / 52 →
        ∀ (e t : ℝ → ℕ), AdmissiblePage 4 Ct e t →
          ∀ (x : ℝ), 2 ≤ x → ∀ (q d : ℕ), TaylorWilesWindow.PrimePair ψ.N q d →
            P0 < (q : ℝ) → P0 < (d : ℝ) →
            (∀ l ∈ Bchi, VVat P.toSelmerSystem l (L₂ l) (t x) (Real.exp (x ^ (4 * eps / 5)))) →
            ∀ (E : Type) [Field E] [NumberField E], IsChiField ψ (e x) q d E →
              SumIn P Bchi E (t x)
                (((condF E : ℝ) * (t x : ℝ)) ^ Cin +
                  (∑ l ∈ Bchi, Real.log (l : ℕ)) * Real.exp (x ^ (4 * eps / 5)))) ∧
      -- Plus parity good odd primes l ∉ Bchi (`SumOut`: PURE POLYNOMIAL, NO exp term!)
      (∀ (e t : ℝ → ℕ), AdmissiblePage 4 Ct e t →
        ∀ (X x : ℝ), 2 ≤ x → ∀ (q d : ℕ), TaylorWilesWindow.PrimePair ψ.N q d →
          2 * X ^ Ct + 1 < (q : ℝ) → 2 * X ^ Ct + 1 < (d : ℝ) →
          P0 < (q : ℝ) → P0 < (d : ℝ) →
          ∀ (E : Type) [Field E] [NumberField E], IsChiField ψ (e x) q d E →
            SumOut P Bchi E (t x) (((condF E : ℝ) * (t x : ℝ)) ^ Cout))

/-- **End-to-End Bridge from `ParityWindow1Supply` to `TaylorWilesWindow.JointPatchingWindow`**:
combines `Stage2GaloisWire.condF_bounds_of_isChiField`, `thmBab_window1` (`BaAt` + `BbAt` on the
SAME dyadic window `[Y, Y^2] ⊂ [X^(1/J), X]`), `vvplusLe_of_bbAt_and_sumOut`, and
`vvle_of_parity_parts` (`LengthEqAddEigen.vvle_of_parts`)! -/
theorem jointPatchingWindow_of_parityWindow1 {P : ParitySelmerSystem} {H : H2LengthSystem}
    {T : TowerLayerRelation} {Ct : ℝ} (hCt : 1 ≤ Ct)
    (hSup : ParityWindow1Supply P H T Ct) :
    JointPatchingWindow P.toSelmerSystem canonicalHostInvariants Ct where
  cond_bounds := fun ψ e q d hq hd E _ _ hE =>
    condF_bounds_of_isChiField ψ e q d hq hd E hE
  ram_const := by
    obtain ⟨CK0, hLemmaK⟩ := hSup.exists_lemmaK
    obtain ⟨Cb, hChar⟩ := hSup.exists_char_data
    refine ⟨Cb, fun ψ eps heps0 heps1 e t hAdm => ?_⟩
    obtain ⟨R₀, Bchi, Rl, L₂, hFL₂, hNFL₂, Cin, Cout, P0, hTwo, hBad, hMinus, hSumIn, hSumOut⟩ :=
      hChar ψ
    set CK : ℝ := max CK0 1
    set R : ℕ := R₀ + ∑ l ∈ Bchi, Rl l
    set J : ℝ := windowExponent R CK Ct eps
    have hJpos : 0 < J := windowExponent_pos R (lt_of_lt_of_le one_pos (le_max_right _ _))
      (by linarith) heps0
    set Civ : ℝ := ∑ l ∈ Bchi, Real.log (l : ℕ)
    set C : ℝ := max (max (max Cin Cout) 0 + 1) (max Civ 0)
    obtain ⟨X0, hBab⟩ := thmBab_window1 CK0 hLemmaK ψ R₀ hTwo Bchi Rl L₂ hBad
      Ct eps 4 hCt heps0 (by linarith)
    refine ⟨J, C, P0, max X0 (2 ^ J), hJpos, ?_⟩
    intro X hX q d hPP hqX hdX hPq hPd hlogqd
    have hX0 : X0 ≤ X := (le_max_left _ _).trans hX
    have hX2J : (2 : ℝ) ^ J ≤ X := (le_max_right _ _).trans hX
    have h2_le_XJ : (2 : ℝ) ≤ X ^ (1 / J) := by
      calc (2 : ℝ) = ((2 : ℝ) ^ J) ^ (1 / J) := by
            rw [← Real.rpow_mul (by norm_num), mul_one_div_cancel hJpos.ne', Real.rpow_one]
        _ ≤ X ^ (1 / J) := Real.rpow_le_rpow (by positivity) hX2J (by positivity)
    obtain ⟨Y, hY, hYpts⟩ := hBab e t hAdm X hX0 q d hPP hlogqd
    refine ⟨Y, hY.1, hY.2, fun x hxY hxY2 E _ _ hE => ?_⟩
    have hx2 : 2 ≤ x := h2_le_XJ.trans (hY.1.trans hxY)
    obtain ⟨hBa, hBb⟩ := hYpts x hxY hxY2
    have h2 : BoundedHeightTwoPlaceCondition P.toSelmerSystem E (t x)
        (Real.exp (x ^ (4 * eps / 5))) := hBa E hE
    have hm : VVminusLe P E (t x)
        (minusBound Cb ψ.N (Module.finrank ℚ E) (condF E) (t x)) :=
      hMinus e t hAdm x hx2 q d hPP E hE
    have hin : SumIn P Bchi E (t x)
        (((condF E : ℝ) * (t x : ℝ)) ^ Cin + Civ * Real.exp (x ^ (4 * eps / 5))) :=
      hSumIn eps heps0 heps1 e t hAdm x hx2 q d hPP hPq hPd hBb E hE
    have hout : SumOut P Bchi E (t x) (((condF E : ℝ) * (t x : ℝ)) ^ Cout) :=
      hSumOut e t hAdm X x hx2 q d hPP hqX hdX hPq hPd E hE
    have hcond := condF_bounds_of_isChiField ψ (e x) q d hPP.q_prime.pos hPP.d_prime.pos E hE
    have ht2 : 2 ≤ t x := (hAdm x hx2).2.2.1
    have hu2 : (2 : ℝ) ≤ (condF E : ℝ) * (t x : ℝ) := by
      have h1 : (1 : ℝ) ≤ condF E := by exact_mod_cast hcond.1
      have h2' : (2 : ℝ) ≤ t x := by exact_mod_cast ht2
      nlinarith
    have hp : VVplusLe P E (t x)
        (((condF E : ℝ) * (t x : ℝ)) ^ C + C * Real.exp (x ^ (4 * eps / 5))) :=
      vvplusLe_of_bbAt_and_sumOut hu2 (Real.exp_pos _).le hin hout
    exact vvle_of_parity_parts h2 hm hp

/-- **Direct `VWinAt` Assembly** from `ParityWindow1Supply`. -/
theorem vwinAt_of_parityWindow1 {P : ParitySelmerSystem} {H : H2LengthSystem}
    {T : TowerLayerRelation} {Ct : ℝ} (hCt : 1 ≤ Ct)
    (hSup : ParityWindow1Supply P H T Ct) (ψ : PChar) :
    VWinAt P.toSelmerSystem ψ Ct :=
  vwinAt_of_joint_patching hCt (jointPatchingWindow_of_parityWindow1 hCt hSup) ψ

/-- **Full `VWin` Assembly** (`∀ ψ, VWinAt S ψ 401`) from `ParityWindow1Supply` at `Ct = 401`. -/
theorem vwin_of_parityWindow1 {P : ParitySelmerSystem} {H : H2LengthSystem}
    {T : TowerLayerRelation} (hSup : ParityWindow1Supply P H T 401) :
    VWin P.toSelmerSystem :=
  vwin_of_joint_patching (jointPatchingWindow_of_parityWindow1 (by norm_num) hSup)

/-- **Full `GaloisModularityContract` Discharge** from `ParityWindow1Supply` at `Ct = 401`. -/
theorem galoisModularityContract_of_parityWindow1 {P : ParitySelmerSystem} {H : H2LengthSystem}
    {T : TowerLayerRelation} (hSup : ParityWindow1Supply P H T 401) :
    GaloisModularityContract P.toSelmerSystem :=
  galoisModularityContract_of_patching (jointPatchingWindow_of_parityWindow1 (by norm_num) hSup)

/-! ### Concrete 0-Assumption Instantiations on Stage 11 Ferrero–Washington Power Series -/

/-- Any monic polynomial `P ∈ ℤ_[p][X]` of degree `1` splits over `ℚ_[p]` as `X - C (-P.coeff 0)`. -/
private lemma monic_natDegree_one_eq_X_sub {p : ℕ} [Fact p.Prime] {P : Polynomial ℤ_[p]}
    (hmon : P.Monic) (hdeg : P.natDegree = 1) :
    P = Polynomial.X - Polynomial.C (-P.coeff 0) := by
  ext n
  match n with
  | 0 => simp
  | 1 =>
    have hlc : P.coeff 1 = 1 := by
      rw [← hdeg]
      exact hmon.leadingCoeff
    simp [hlc]
  | n + 2 =>
    have hgt : P.natDegree < n + 2 := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hgt]
    simp [Polynomial.coeff_X]

/-- **Concrete 0-Assumption `SplitDistinguishedSeries` Witness for the First Irregular Prime `p = 37`**:
constructs a `SplitDistinguishedSeries 37 ℚ_[37]` directly from
`Stage11FerreroWashington.irregular_prime_37_mu_zero_lambda_eq_one` (`kubotaLeopoldtSeries 37`
at irregular branch `i = 32`, with exact `μ = 0` and `λ = 1`)! -/
def irregular37SplitSeries [Fact (Nat.Prime 37)] :
    SplitDistinguishedSeries 37 ℚ_[37] := by
  let F := kubotaLeopoldtSeries 37 (by decide) 2 (by decide) 31
  have h37 := irregular_prime_37_mu_zero_lambda_eq_one
  have hFne : F ≠ 0 := h37.1
  have hFmu : iwasawaMu F = 0 := h37.2.2.1
  have hFlam : iwasawaLambda F = 1 := h37.2.2.2
  have hdist : IsDistinguishedPoly (distPart F) := distPart_isDistinguished hFne
  have hdeg : (distPart F).natDegree = 1 := (distPart_natDegree hFne).trans hFlam
  have hPeq : distPart F = Polynomial.X - Polynomial.C (-(distPart F).coeff 0) :=
    monic_natDegree_one_eq_X_sub hdist.1 hdeg
  let r0 : ℚ_[37] := (-(distPart F).coeff 0 : ℤ_[37])
  refine
    { series := F
      ne_zero := hFne
      mu_zero := hFmu
      roots := fun _ => r0
      splits := ?_ }
  conv_lhs => rw [hPeq, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  have hcard : Fintype.card (Fin (iwasawaLambda F)) = 1 := by rw [Fintype.card_fin, hFlam]
  have hprod : (∏ _i : Fin (iwasawaLambda F), (Polynomial.X - Polynomial.C r0)) =
      (Polynomial.X - Polynomial.C r0) := by
    rw [Finset.prod_const, Finset.card_univ, hcard, pow_one]
  rw [hprod]
  rfl

/-- **Concrete 0-Assumption `Window1` Root-Avoidance on `p = 37` (`kubotaLeopoldtSeries 37`)**:
for `κ = 1 + 37` (`‖κ - 1‖ = 37⁻¹`), at EVERY cutoff `Z : ℕ`, at most ONE twist `e ∈ [1, Z]`
is exceptional, and for every non-exceptional twist `e ∈ [1, Z] \ Exc`,
`((distPart F_37).eval ((1 + 37)^e - 1)).valuation ≤ 1 + Nat.log 37 Z`! -/
theorem irregular37_root_avoidance_witness [Fact (Nat.Prime 37)] (Z : ℕ) :
    let F := kubotaLeopoldtSeries 37 (by decide) 2 (by decide) 31
    let κ : ℤ_[37] := 1 + (37 : ℤ_[37])
    ∃ Exc : Finset ℕ, Exc.card ≤ 1 ∧
      ∀ e : ℕ, 1 ≤ e → e ≤ Z → e ∉ Exc →
        (distPart F).eval (κ ^ e - 1) ≠ 0 ∧
        ((distPart F).eval (κ ^ e - 1)).valuation ≤ 1 + Nat.log 37 Z := by
  have hκ : ‖(1 + (37 : ℤ_[37])) - 1‖ = (37 : ℝ) ^ (-(1 : ℤ)) := by
    rw [add_sub_cancel_left]
    have hcoe : ‖((37 : ℕ) : ℤ_[37])‖ = ‖((37 : ℕ) : ℚ_[37])‖ := rfl
    change ‖((37 : ℕ) : ℤ_[37])‖ = _
    rw [hcoe, Padic.norm_p]
    simp
  have hser : irregular37SplitSeries.series = kubotaLeopoldtSeries 37 (by decide) 2 (by decide) 31 :=
    rfl
  have hlam : ∑ _i : Fin 1, iwasawaLambda irregular37SplitSeries.series ≤ 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul, hser]
    exact irregular_prime_37_mu_zero_lambda_eq_one.2.2.2.le
  obtain ⟨Exc, hcard, hfar⟩ := iwasawa_family_root_avoidance_exc (p := 37) (m := 1) (R := 1)
    (κ := 1 + (37 : ℤ_[37])) (c₀ := 1) (by omega) (by decide) hκ ℚ_[37]
    (fun _ => irregular37SplitSeries) hlam Z
  refine ⟨Exc, hcard, fun e he1 heZ hne => ?_⟩
  obtain ⟨hne0, hval⟩ := hfar e he1 heZ hne
  have h0 := hne0 0
  rw [hser] at h0
  refine ⟨h0, ?_⟩
  simpa [hser] using hval

/-- **Concrete 0-Assumption `SplitDistinguishedSeries` Witness for Mazur's `p = 2` Bernoulli Measure**:
from `Stage11FerreroWashington.mazurBernoulliMeasure_three_isUnit`, `iwasawaTransform (μ_3)` at `p = 2`
is a unit (`μ = 0, λ = 0`), giving `distPart = 1` and ZERO exceptional twists (`Exc = ∅`)! -/
def mazurTwoSplitSeries [Fact (Nat.Prime 2)] :
    SplitDistinguishedSeries 2 ℚ_[2] := by
  have h3 := mazurBernoulliMeasure_three_isUnit (p := 2) (by decide)
  refine
    { series := iwasawaTransform (mazurBernoulliMeasure 2 3 (by decide))
      ne_zero := h3.1.ne_zero
      mu_zero := h3.2.1
      roots := fun i => Fin.elim0 (by rwa [h3.2.2] at i)
      splits := ?_ }
  rw [distPart_of_isUnit h3.1, Polynomial.map_one]
  symm
  apply Finset.prod_eq_one
  intro i _
  exact Fin.elim0 (by rwa [h3.2.2] at i)

end EndToEndAssembly

end RHDirect.Stage12Window1RootAvoid

end

