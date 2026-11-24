import RHDirect.Stage2IwasawaTwoTower
import RHDirect.Stage2DworkExp
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.Padics.MahlerBasis
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Nat.Totient
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Topology.MetricSpace.Ultra.ContinuousMaps

/-!
# RHDirect.Stage7PadicLFunction

Unconditional Lean 4 formalization (zero `sorry`, zero custom `axiom`s) of:

1. **Concrete $p$-adic Measures `PadicMeasure p` on `ℤ_[p]` & Exact Amice–Mahler–Iwasawa
   Isomorphism `PadicMeasure p ≃+* ℤ_[p][[T]]` (and `≃ₐ[ℤ_[p]]`, `≃ₗ[ℤ_[p]]`)**:
   - Compatible projective families `μ : ∀ n, ZMod (p^n) → ℤ_[p]` with convolution multiplication,
     Riemann-sum integration `measureIntegral μ f` for continuous `f : ℤ_[p] → ℤ_[p]`,
     additivity, `ℤ_[p]`-linearity, sup-norm / congruence continuity, and pushforward measures.
   - Exact ring/algebra isomorphism `iwasawaTransform : PadicMeasure p ≃ₐ[ℤ_[p]] IwasawaAlg p`
     sending `δ_1 ↦ 1 + T`, convolution to power series multiplication, and matching
     `μ n a` with coefficients modulo `ω_n = (1 + T)^(p^n) - 1`.
   - Amice–Iwasawa analytic evaluation identity `evalIwasawa (iwasawaTransform μ) y = ∫ (1 + y)^x dμ`.

2. **Concrete Mazur Regularized Bernoulli Measure `μ_c` & Exact $k$-th Moment Identity**:
   - Raabe's multiplication formula for `Polynomial.bernoulli`.
   - Concrete Mazur regularized Bernoulli distribution `E_{1,c}(a, p^n)` (proved integral in `ℤ_[p]`
     for all primes `p` and `c ≥ 2` with `p ∤ c`, and literally in `ℤ` for odd `c`).
   - Exact $k$-th moment identity `∫_{ℤ_p} x^k dμ_c = (1 - c^{k+1}) B_{k+1}/(k + 1)` and
     self-similar Euler-factor unit restriction `∫_{ℤ_pˣ} x^k dμ_c = (1 - p^k)(1 - c^{k+1}) B_{k+1}/(k + 1)`.

3. **Unconditional Kummer's Congruences for Bernoulli Numbers & Kubota–Leopoldt $p$-adic Zeta**:
   - von Staudt–Clausen / Adams $p$-integrality of `B_{k+1}/(k + 1)` for `(p - 1) ∤ (k + 1)`.
   - Full unconditional Kummer congruences for all odd primes `p`, `m ≥ 1`, `k, k' ≥ 1` with
     `(p - 1) ∤ (k + 1)` and `k ≡ k' [MOD (p - 1) * p^(m - 1)]`.
   - Concrete Kubota–Leopoldt Iwasawa power series `kubotaLeopoldtSeries` and $p$-adic zeta
     function `kubotaLeopoldtZeta`, evaluated at `T = (1 + p)^s - 1`, interpolating
     `-(1 - p^k) B_{k+1} / (k + 1)` at all `k ≥ 1` with `k ≡ i [MOD p - 1]`.
-/

noncomputable section

open scoped BigOperators Topology
open Finset Filter Topology RHDirect.Stage2IwasawaTwoTower RHDirect.Stage2DworkExp

namespace RHDirect.Stage7PadicLFunction

/-! ## Section 1: Concrete $p$-adic Measures `PadicMeasure p` & Integration on `ℤ_[p]` -/

section PadicMeasureCore

variable {p : ℕ} [Fact p.Prime]

/-- Transition ring homomorphism `ZMod (p ^ n) →+* ZMod (p ^ m)` for `m ≤ n`. -/
def zmodPowCast {m n : ℕ} (h : m ≤ n) : ZMod (p ^ n) →+* ZMod (p ^ m) :=
  ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))

/-- One-step transition `ZMod (p ^ (n + 1)) →+* ZMod (p ^ n)`. -/
def zmodPowStep (n : ℕ) : ZMod (p ^ (n + 1)) →+* ZMod (p ^ n) :=
  zmodPowCast (Nat.le_succ n)

omit [Fact p.Prime] in
lemma zmodPowCast_refl (n : ℕ) (x : ZMod (p ^ n)) :
    zmodPowCast (p := p) (le_refl n) x = x := by
  simp [zmodPowCast]

omit [Fact p.Prime] in
lemma zmodPowCast_comp {k m n : ℕ} (hkm : k ≤ m) (hmn : m ≤ n) (x : ZMod (p ^ n)) :
    zmodPowCast (p := p) hkm (zmodPowCast (p := p) hmn x) =
      zmodPowCast (p := p) (hkm.trans hmn) x := by
  have h : (zmodPowCast (p := p) hkm).comp (zmodPowCast (p := p) hmn) =
      zmodPowCast (p := p) (hkm.trans hmn) := by
    simp only [zmodPowCast, ZMod.castHom_comp]
  exact congrArg (fun f => f x) h

omit [Fact p.Prime] in
lemma zmod_pow_zero_eq (a b : ZMod (p ^ 0)) : a = b := by
  have hsub : Subsingleton (ZMod (p ^ 0)) := by
    rw [pow_zero]; infer_instance
  exact hsub.elim a b

lemma zmodPowCast_toZModPow {m n : ℕ} (h : m ≤ n) (x : ℤ_[p]) :
    zmodPowCast (p := p) h (PadicInt.toZModPow n x) = PadicInt.toZModPow m x := by
  rw [zmodPowCast, ← RingHom.comp_apply, PadicInt.zmod_cast_comp_toZModPow m n h]

lemma zmodPowCast_val_modEq {m n : ℕ} (h : m ≤ n) (b : ZMod (p ^ n)) :
    b.val ≡ (zmodPowCast (p := p) h b).val [MOD p ^ m] := by
  have : NeZero (p ^ m) := ⟨pow_ne_zero m (Fact.out : p.Prime).ne_zero⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  rw [ZMod.natCast_zmod_val, zmodPowCast, ← map_natCast (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))),
    ZMod.natCast_zmod_val]

lemma padicInt_toZModPow_val_eq {m n : ℕ} (h : m ≤ n) (b : ZMod (p ^ n)) :
    PadicInt.toZModPow m (b.val : ℤ_[p]) = zmodPowCast (p := p) h b := by
  have : NeZero (p ^ m) := ⟨pow_ne_zero m (Fact.out : p.Prime).ne_zero⟩
  rw [map_natCast, zmodPowCast, ← map_natCast (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))),
    ZMod.natCast_zmod_val]

lemma padicInt_norm_le_pow_of_toZModPow_eq {n : ℕ} {x y : ℤ_[p]}
    (h : PadicInt.toZModPow n x = PadicInt.toZModPow n y) :
    ‖x - y‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
  have hker : x - y ∈ RingHom.ker (PadicInt.toZModPow n) := by
    rw [RingHom.mem_ker, map_sub, h, sub_self]
  rw [PadicInt.ker_toZModPow] at hker
  exact (PadicInt.norm_le_pow_iff_mem_span_pow (x - y) n).mpr hker

lemma padicInt_toZModPow_eq_of_norm_le_pow {n : ℕ} {x y : ℤ_[p]}
    (h : ‖x - y‖ ≤ (p : ℝ) ^ (-(n : ℤ))) :
    PadicInt.toZModPow n x = PadicInt.toZModPow n y := by
  have hmem : x - y ∈ Ideal.span ({(p : ℤ_[p]) ^ n} : Set ℤ_[p]) :=
    (PadicInt.norm_le_pow_iff_mem_span_pow (x - y) n).mp h
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at hmem
  exact hmem

lemma padicInt_norm_le_pow_iff_toZModPow_eq (n : ℕ) (x y : ℤ_[p]) :
    ‖x - y‖ ≤ (p : ℝ) ^ (-(n : ℤ)) ↔ PadicInt.toZModPow n x = PadicInt.toZModPow n y :=
  ⟨padicInt_toZModPow_eq_of_norm_le_pow, padicInt_norm_le_pow_of_toZModPow_eq⟩

lemma padicInt_eq_of_forall_norm_le_pow {x y : ℤ_[p]}
    (h : ∀ n : ℕ, ‖x - y‖ ≤ (p : ℝ) ^ (-(n : ℤ))) : x = y := by
  by_contra hne
  have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt p hpos
  exact not_lt_of_ge (h k) hk

lemma padicInt_norm_sub_le_max (x y : ℤ_[p]) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg]
  simpa [norm_neg] using IsUltrametricDist.norm_add_le_max x (-y)

/-- Ultrametric finite-sum norm bound in `ℤ_[p]`. -/
lemma padicInt_norm_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℤ_[p]) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ B) : ‖∑ i ∈ s, f i‖ ≤ B :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB hf

/-- Concrete `ℤ_[p]`-valued $p$-adic measure on `ℤ_[p]`: a projective family of additive
distributions `μ n : ZMod (p ^ n) → ℤ_[p]` satisfying the distribution law
`μ n a = ∑_{b ≡ a mod p^n} μ (n + 1) b`. -/
@[ext]
structure PadicMeasure (p : ℕ) [Fact p.Prime] where
  toFun : ∀ n : ℕ, ZMod (p ^ n) → ℤ_[p]
  compat : ∀ (n : ℕ) (a : ZMod (p ^ n)),
    toFun n a = ∑ b ∈ Finset.univ.filter (fun b : ZMod (p ^ (n + 1)) =>
      zmodPowStep (p := p) n b = a), toFun (n + 1) b

instance : CoeFun (PadicMeasure p) (fun _ => ∀ n : ℕ, ZMod (p ^ n) → ℤ_[p]) where
  coe := PadicMeasure.toFun

/-- Multi-step distribution law: for `m ≤ n`, `μ m a = ∑_{b ≡ a mod p^m} μ n b`. -/
theorem PadicMeasure.compat_le (μ : PadicMeasure p) {m n : ℕ} (h : m ≤ n) (a : ZMod (p ^ m)) :
    μ m a = ∑ b ∈ Finset.univ.filter (fun b : ZMod (p ^ n) =>
      zmodPowCast (p := p) h b = a), μ n b := by
  induction n with
  | zero =>
    obtain rfl : m = 0 := Nat.le_zero.mp h
    have hfilt : Finset.univ.filter (fun b : ZMod (p ^ 0) =>
        zmodPowCast (p := p) (le_refl 0) b = a) = {a} := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [zmodPowCast_refl]
    rw [hfilt, Finset.sum_singleton]
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · have hfilt : Finset.univ.filter (fun b : ZMod (p ^ (k + 1)) =>
          zmodPowCast (p := p) (le_refl (k + 1)) b = a) = {a} := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        rw [zmodPowCast_refl]
      rw [hfilt, Finset.sum_singleton]
    · have hmk : m ≤ k := Nat.lt_succ_iff.mp hlt
      rw [ih hmk]
      have hstep : ∀ x : ZMod (p ^ k),
          μ k x = ∑ b ∈ Finset.univ.filter (fun b : ZMod (p ^ (k + 1)) =>
            zmodPowStep (p := p) k b = x), μ (k + 1) b := μ.compat k
      simp_rw [hstep]
      have hdisj : Set.PairwiseDisjoint
          (↑(Finset.univ.filter (fun x : ZMod (p ^ k) => zmodPowCast (p := p) hmk x = a)))
          (fun x : ZMod (p ^ k) =>
            Finset.univ.filter (fun b : ZMod (p ^ (k + 1)) => zmodPowStep (p := p) k b = x)) := by
        intro x _ y _ hxy
        rw [Function.onFun, Finset.disjoint_left]
        intro b hbx hby
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hbx hby
        exact hxy (hbx.symm.trans hby)
      rw [← Finset.sum_biUnion hdisj]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext b
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [← hx]
        exact (zmodPowCast_comp hmk (Nat.le_succ k) b).symm
      · intro hb
        refine ⟨zmodPowStep (p := p) k b, ?_, rfl⟩
        rw [zmodPowStep, zmodPowCast_comp hmk (Nat.le_succ k) b]
        exact hb

/-- Total mass law: `∑ a : ZMod (p ^ n), μ n a = μ 0 0`. -/
theorem PadicMeasure.sum_univ (μ : PadicMeasure p) (n : ℕ) :
    ∑ a : ZMod (p ^ n), μ n a = μ 0 0 := by
  rw [μ.compat_le (Nat.zero_le n) 0]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext b
  simp only [Finset.mem_univ, Finset.mem_filter, true_and, true_iff]
  exact zmod_pow_zero_eq _ _

/-- Zero measure. -/
instance : Zero (PadicMeasure p) where
  zero := ⟨fun _ _ => 0, fun _ _ => by simp⟩

/-- Sum of two $p$-adic measures. -/
instance : Add (PadicMeasure p) where
  add μ₁ μ₂ :=
    { toFun := fun n a => μ₁ n a + μ₂ n a
      compat := fun n a => by
        rw [Finset.sum_add_distrib, ← μ₁.compat n a, ← μ₂.compat n a] }

/-- Negation of a $p$-adic measure. -/
instance : Neg (PadicMeasure p) where
  neg μ :=
    { toFun := fun n a => -μ n a
      compat := fun n a => by
        rw [Finset.sum_neg_distrib, ← μ.compat n a] }

/-- Difference of two $p$-adic measures. -/
instance : Sub (PadicMeasure p) where
  sub μ₁ μ₂ :=
    { toFun := fun n a => μ₁ n a - μ₂ n a
      compat := fun n a => by
        rw [Finset.sum_sub_distrib, ← μ₁.compat n a, ← μ₂.compat n a] }

/-- Scalar multiplication by `ℤ_[p]`. -/
instance : SMul ℤ_[p] (PadicMeasure p) where
  smul r μ :=
    { toFun := fun n a => r * μ n a
      compat := fun n a => by
        rw [← Finset.mul_sum, ← μ.compat n a] }

@[simp] lemma PadicMeasure.zero_apply (n : ℕ) (a : ZMod (p ^ n)) : (0 : PadicMeasure p) n a = 0 := rfl
@[simp] lemma PadicMeasure.add_apply (μ₁ μ₂ : PadicMeasure p) (n : ℕ) (a : ZMod (p ^ n)) :
    (μ₁ + μ₂) n a = μ₁ n a + μ₂ n a := rfl
@[simp] lemma PadicMeasure.neg_apply (μ : PadicMeasure p) (n : ℕ) (a : ZMod (p ^ n)) :
    (-μ) n a = -μ n a := rfl
@[simp] lemma PadicMeasure.sub_apply (μ₁ μ₂ : PadicMeasure p) (n : ℕ) (a : ZMod (p ^ n)) :
    (μ₁ - μ₂) n a = μ₁ n a - μ₂ n a := rfl
@[simp] lemma PadicMeasure.smul_apply (r : ℤ_[p]) (μ : PadicMeasure p) (n : ℕ) (a : ZMod (p ^ n)) :
    (r • μ) n a = r * μ n a := rfl

instance : AddCommGroup (PadicMeasure p) where
  add_assoc _ _ _ := by ext n a; exact add_assoc _ _ _
  zero_add _ := by ext n a; exact zero_add _
  add_zero _ := by ext n a; exact add_zero _
  add_comm _ _ := by ext n a; exact add_comm _ _
  neg_add_cancel _ := by ext n a; exact neg_add_cancel _
  sub_eq_add_neg _ _ := by ext n a; exact sub_eq_add_neg _ _
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module ℤ_[p] (PadicMeasure p) where
  one_smul _ := by ext n a; exact one_mul _
  mul_smul _ _ _ := by ext n a; exact mul_assoc _ _ _
  smul_zero _ := by ext n a; exact mul_zero _
  smul_add _ _ _ := by ext n a; exact mul_add _ _ _
  add_smul _ _ _ := by ext n a; exact add_mul _ _ _
  zero_smul _ := by ext n a; exact zero_mul _

/-- Dirac measure `δ_x` supported at `x : ℤ_[p]`. -/
def diracMeasure (x : ℤ_[p]) : PadicMeasure p where
  toFun n a := if PadicInt.toZModPow n x = a then 1 else 0
  compat n a := by
    have hstep : zmodPowStep (p := p) n (PadicInt.toZModPow (n + 1) x) =
        PadicInt.toZModPow n x := zmodPowCast_toZModPow (Nat.le_succ n) x
    by_cases h : PadicInt.toZModPow n x = a
    · rw [if_pos h]
      rw [Finset.sum_eq_single (PadicInt.toZModPow (n + 1) x)]
      · simp
      · intro b _ hne
        rw [if_neg hne.symm]
      · intro hnot
        exfalso
        apply hnot
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hstep, h]
    · rw [if_neg h]
      symm
      refine Finset.sum_eq_zero fun b hb => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      have hne : PadicInt.toZModPow (n + 1) x ≠ b := by
        intro heq
        apply h
        rw [← hstep, heq, hb]
      rw [if_neg hne]

@[simp] lemma diracMeasure_apply (x : ℤ_[p]) (n : ℕ) (a : ZMod (p ^ n)) :
    diracMeasure x n a = if PadicInt.toZModPow n x = a then 1 else 0 := rfl

/-- Convolution product of two $p$-adic measures. -/
instance : Mul (PadicMeasure p) where
  mul μ₁ μ₂ :=
    { toFun := fun n c => ∑ a : ZMod (p ^ n), μ₁ n a * μ₂ n (c - a)
      compat := fun n c => by
        rw [Finset.sum_comm]
        have hinner : ∀ a' : ZMod (p ^ (n + 1)),
            ∑ c' ∈ Finset.univ.filter (fun c' : ZMod (p ^ (n + 1)) =>
              zmodPowStep (p := p) n c' = c),
              μ₁ (n + 1) a' * μ₂ (n + 1) (c' - a') =
            μ₁ (n + 1) a' * μ₂ n (c - zmodPowStep (p := p) n a') := by
          intro a'
          rw [← Finset.mul_sum]
          congr 1
          rw [μ₂.compat n (c - zmodPowStep (p := p) n a')]
          refine Finset.sum_bij (fun c' _ => c' - a') ?_ ?_ ?_ ?_
          · intro c' hc'
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc' ⊢
            rw [map_sub, hc']
          · intro c₁ _ c₂ _ heq
            exact sub_left_inj.mp heq
          · intro b' hb'
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb'
            refine ⟨b' + a', ?_, add_sub_cancel_right b' a'⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_add]
            rw [hb', sub_add_cancel]
          · intro _ _; rfl
        have hsum_eq :
            ∑ a' : ZMod (p ^ (n + 1)),
              ∑ c' ∈ Finset.univ.filter (fun c' : ZMod (p ^ (n + 1)) =>
                zmodPowStep (p := p) n c' = c),
                μ₁ (n + 1) a' * μ₂ (n + 1) (c' - a') =
            ∑ a' : ZMod (p ^ (n + 1)),
              μ₁ (n + 1) a' * μ₂ n (c - zmodPowStep (p := p) n a') :=
          Finset.sum_congr rfl fun a' _ => hinner a'
        rw [hsum_eq]
        have hgroup : ∑ a' : ZMod (p ^ (n + 1)),
              μ₁ (n + 1) a' * μ₂ n (c - zmodPowStep (p := p) n a') =
            ∑ a : ZMod (p ^ n),
              ∑ a' ∈ Finset.univ.filter (fun a' : ZMod (p ^ (n + 1)) =>
                zmodPowStep (p := p) n a' = a),
                μ₁ (n + 1) a' * μ₂ n (c - zmodPowStep (p := p) n a') := by
          rw [← Finset.sum_fiberwise_of_maps_to (g := zmodPowStep (p := p) n)
            (fun _ _ => Finset.mem_univ _)]
        rw [hgroup]
        refine Finset.sum_congr rfl fun a _ => ?_
        have hconst : ∑ a' ∈ Finset.univ.filter (fun a' : ZMod (p ^ (n + 1)) =>
              zmodPowStep (p := p) n a' = a),
            μ₁ (n + 1) a' * μ₂ n (c - zmodPowStep (p := p) n a') =
            (∑ a' ∈ Finset.univ.filter (fun a' : ZMod (p ^ (n + 1)) =>
              zmodPowStep (p := p) n a' = a),
              μ₁ (n + 1) a') * μ₂ n (c - a) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun a' ha' => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha'
          rw [ha']
        rw [hconst, ← μ₁.compat n a] }

/-- Multiplicative identity `1 = δ_0` in `PadicMeasure p`. -/
instance : One (PadicMeasure p) where
  one := diracMeasure 0

@[simp] lemma PadicMeasure.mul_apply (μ₁ μ₂ : PadicMeasure p) (n : ℕ) (c : ZMod (p ^ n)) :
    (μ₁ * μ₂) n c = ∑ a : ZMod (p ^ n), μ₁ n a * μ₂ n (c - a) := rfl

@[simp] lemma PadicMeasure.one_apply (n : ℕ) (c : ZMod (p ^ n)) :
    (1 : PadicMeasure p) n c = if (0 : ZMod (p ^ n)) = c then 1 else 0 := by
  change diracMeasure (0 : ℤ_[p]) n c = _
  simp [diracMeasure]

instance : CommRing (PadicMeasure p) where
  mul_assoc μ₁ μ₂ μ₃ := by
    ext n d
    simp only [PadicMeasure.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_bij (fun b _ => b - a) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro b₁ _ b₂ _ h; exact sub_left_inj.mp h
    · intro b _; exact ⟨b + a, Finset.mem_univ _, add_sub_cancel_right b a⟩
    · intro b _
      have heq : d - b = d - a - (b - a) := by abel
      rw [mul_assoc, heq]
  one_mul μ := by
    ext n c
    simp only [PadicMeasure.mul_apply, PadicMeasure.one_apply]
    rw [Finset.sum_eq_single (0 : ZMod (p ^ n))]
    · simp
    · intro a _ ha; simp [ha.symm]
    · intro h; exact absurd (Finset.mem_univ _) h
  mul_one μ := by
    ext n c
    simp only [PadicMeasure.mul_apply, PadicMeasure.one_apply]
    rw [Finset.sum_eq_single c]
    · simp
    · intro a _ ha
      have hne : (0 : ZMod (p ^ n)) ≠ c - a := by
        intro h
        exact ha (sub_eq_zero.mp h.symm).symm
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  mul_comm μ₁ μ₂ := by
    ext n c
    simp only [PadicMeasure.mul_apply]
    refine Finset.sum_bij (fun a _ => c - a) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro a₁ _ a₂ _ h; exact sub_right_inj.mp h
    · intro b _; exact ⟨c - b, Finset.mem_univ _, sub_sub_cancel c b⟩
    · intro a _; rw [sub_sub_cancel, mul_comm]
  left_distrib μ₁ μ₂ μ₃ := by
    ext n c
    simp only [PadicMeasure.mul_apply, PadicMeasure.add_apply, mul_add, Finset.sum_add_distrib]
  right_distrib μ₁ μ₂ μ₃ := by
    ext n c
    simp only [PadicMeasure.mul_apply, PadicMeasure.add_apply, add_mul, Finset.sum_add_distrib]
  zero_mul μ := by ext n c; simp
  mul_zero μ := by ext n c; simp

instance : Algebra ℤ_[p] (PadicMeasure p) :=
  Algebra.ofModule (fun r μ₁ μ₂ => by
    ext n c
    simp only [PadicMeasure.smul_apply, PadicMeasure.mul_apply, Finset.mul_sum, mul_assoc])
    (fun r μ₁ μ₂ => by
    ext n c
    simp only [PadicMeasure.smul_apply, PadicMeasure.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => by ring)

theorem diracMeasure_mul (x y : ℤ_[p]) :
    diracMeasure (p := p) x * diracMeasure y = diracMeasure (x + y) := by
  ext n c
  simp only [PadicMeasure.mul_apply, diracMeasure_apply, map_add]
  rw [Finset.sum_eq_single (PadicInt.toZModPow n x)]
  · simp only [↓reduceIte, one_mul]
    congr 1
    exact propext eq_sub_iff_add_eq'
  · intro a _ ha
    simp [ha.symm]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ### Riemann-Sum Integration of Continuous Functions on `ℤ_[p]` -/

/-- Level-`n` Riemann sum of `f : ℤ_[p] → ℤ_[p]` against a $p$-adic measure `μ`. -/
def riemannSum (μ : PadicMeasure p) (f : ℤ_[p] → ℤ_[p]) (n : ℕ) : ℤ_[p] :=
  ∑ a : ZMod (p ^ n), f (a.val : ℤ_[p]) * μ n a

lemma riemannSum_add_fun (μ : PadicMeasure p) (f g : ℤ_[p] → ℤ_[p]) (n : ℕ) :
    riemannSum μ (fun x => f x + g x) n = riemannSum μ f n + riemannSum μ g n := by
  simp only [riemannSum, add_mul, Finset.sum_add_distrib]

lemma riemannSum_sub_fun (μ : PadicMeasure p) (f g : ℤ_[p] → ℤ_[p]) (n : ℕ) :
    riemannSum μ (fun x => f x - g x) n = riemannSum μ f n - riemannSum μ g n := by
  simp only [riemannSum, sub_mul, Finset.sum_sub_distrib]

lemma riemannSum_smul_fun (μ : PadicMeasure p) (c : ℤ_[p]) (f : ℤ_[p] → ℤ_[p]) (n : ℕ) :
    riemannSum μ (fun x => c * f x) n = c * riemannSum μ f n := by
  simp only [riemannSum, mul_assoc, ← Finset.mul_sum]

lemma riemannSum_add_measure (μ₁ μ₂ : PadicMeasure p) (f : ℤ_[p] → ℤ_[p]) (n : ℕ) :
    riemannSum (μ₁ + μ₂) f n = riemannSum μ₁ f n + riemannSum μ₂ f n := by
  simp only [riemannSum, PadicMeasure.add_apply, mul_add, Finset.sum_add_distrib]

lemma riemannSum_sub_measure (μ₁ μ₂ : PadicMeasure p) (f : ℤ_[p] → ℤ_[p]) (n : ℕ) :
    riemannSum (μ₁ - μ₂) f n = riemannSum μ₁ f n - riemannSum μ₂ f n := by
  simp only [riemannSum, PadicMeasure.sub_apply, mul_sub, Finset.sum_sub_distrib]

lemma riemannSum_smul_measure (c : ℤ_[p]) (μ : PadicMeasure p) (f : ℤ_[p] → ℤ_[p]) (n : ℕ) :
    riemannSum (c • μ) f n = c * riemannSum μ f n := by
  simp only [riemannSum, PadicMeasure.smul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => by ring

/-- Exact refinement difference formula for Riemann sums across levels `m ≤ n`. -/
lemma riemannSum_sub_of_le (μ : PadicMeasure p) (f : ℤ_[p] → ℤ_[p]) {m n : ℕ} (h : m ≤ n) :
    riemannSum μ f n - riemannSum μ f m =
      ∑ b : ZMod (p ^ n),
        (f (b.val : ℤ_[p]) - f ((zmodPowCast (p := p) h b).val : ℤ_[p])) * μ n b := by
  have hm : riemannSum μ f m =
      ∑ b : ZMod (p ^ n), f ((zmodPowCast (p := p) h b).val : ℤ_[p]) * μ n b := by
    unfold riemannSum
    have h1 : ∀ a : ZMod (p ^ m),
        f (a.val : ℤ_[p]) * μ m a =
          ∑ b ∈ Finset.univ.filter (fun b : ZMod (p ^ n) => zmodPowCast (p := p) h b = a),
            f ((zmodPowCast (p := p) h b).val : ℤ_[p]) * μ n b := by
      intro a
      rw [μ.compat_le h a, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b hb => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      rw [hb]
    rw [Finset.sum_congr rfl (fun a _ => h1 a)]
    exact Finset.sum_fiberwise_of_maps_to (g := zmodPowCast (p := p) h)
      (f := fun b : ZMod (p ^ n) => f ((zmodPowCast (p := p) h b).val : ℤ_[p]) * μ n b)
      (fun _ _ => Finset.mem_univ _)
  rw [hm]
  unfold riemannSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => by ring

/-- Uniform continuity modulus for any continuous function `f : ℤ_[p] → ℤ_[p]` (via compactness
of `ℤ_[p]`). -/
theorem exists_level_of_continuous {f : ℤ_[p] → ℤ_[p]} (hf : Continuous f) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ x y : ℤ_[p],
      PadicInt.toZModPow N x = PadicInt.toZModPow N y → ‖f x - f y‖ ≤ ε := by
  have huc : UniformContinuous f := CompactSpace.uniformContinuous_of_continuous hf
  obtain ⟨δ, hδ, hdist⟩ := Metric.uniformContinuous_iff.mp huc ε hε
  obtain ⟨N, hN⟩ := PadicInt.exists_pow_neg_lt p hδ
  refine ⟨N, fun x y hxy => ?_⟩
  have hnorm : ‖x - y‖ ≤ (p : ℝ) ^ (-(N : ℤ)) := padicInt_norm_le_pow_of_toZModPow_eq hxy
  have hlt : dist x y < δ := by
    rw [dist_eq_norm]
    exact hnorm.trans_lt hN
  have hfl : dist (f x) (f y) < ε := hdist hlt
  rw [dist_eq_norm] at hfl
  exact hfl.le

/-- Uniform norm bound on Riemann-sum refinement when `f` varies by at most `B` on balls of
level `m`. Note this bound is **independent of `μ`**. -/
lemma norm_riemannSum_sub_le_of_le (μ : PadicMeasure p) {f : ℤ_[p] → ℤ_[p]} {m n : ℕ} (h : m ≤ n)
    {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ x y : ℤ_[p], PadicInt.toZModPow m x = PadicInt.toZModPow m y → ‖f x - f y‖ ≤ B) :
    ‖riemannSum μ f n - riemannSum μ f m‖ ≤ B := by
  rw [riemannSum_sub_of_le μ f h]
  refine padicInt_norm_sum_le _ _ hB fun b _ => ?_
  rw [norm_mul]
  have hmod : PadicInt.toZModPow m (b.val : ℤ_[p]) =
      PadicInt.toZModPow m ((zmodPowCast (p := p) h b).val : ℤ_[p]) := by
    have : NeZero (p ^ m) := ⟨pow_ne_zero m (Fact.out : p.Prime).ne_zero⟩
    rw [padicInt_toZModPow_val_eq h b, map_natCast, ZMod.natCast_zmod_val]
  calc ‖f (b.val : ℤ_[p]) - f ((zmodPowCast (p := p) h b).val : ℤ_[p])‖ * ‖μ n b‖
      ≤ B * 1 := mul_le_mul (hf _ _ hmod) (PadicInt.norm_le_one _) (norm_nonneg _) hB
    _ = B := mul_one B

/-- For every continuous `f : ℤ_[p] → ℤ_[p]` and every measure `μ`, the Riemann sums form a
Cauchy sequence in `ℤ_[p]`. -/
theorem cauchySeq_riemannSum (μ : PadicMeasure p) {f : ℤ_[p] → ℤ_[p]} (hf : Continuous f) :
    CauchySeq (riemannSum μ f) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_level_of_continuous hf (ε / 2) (half_pos hε)
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [dist_eq_norm]
  have h1 : ‖riemannSum μ f m - riemannSum μ f N‖ ≤ ε / 2 :=
    norm_riemannSum_sub_le_of_le μ hm (half_pos hε).le hN
  have h2 : ‖riemannSum μ f n - riemannSum μ f N‖ ≤ ε / 2 :=
    norm_riemannSum_sub_le_of_le μ hn (half_pos hε).le hN
  have hsub : riemannSum μ f m - riemannSum μ f n =
      (riemannSum μ f m - riemannSum μ f N) - (riemannSum μ f n - riemannSum μ f N) := by ring
  rw [hsub]
  calc ‖(riemannSum μ f m - riemannSum μ f N) - (riemannSum μ f n - riemannSum μ f N)‖
      ≤ max ‖riemannSum μ f m - riemannSum μ f N‖ ‖riemannSum μ f n - riemannSum μ f N‖ :=
        padicInt_norm_sub_le_max _ _
    _ ≤ ε / 2 := max_le h1 h2
    _ < ε := half_lt_self hε

/-- Concrete $p$-adic integral `∫_{ℤ_[p]} f(x) dμ(x) ∈ ℤ_[p]`, defined as the limit of the
Riemann sums `∑_{a : ZMod (p^n)} f(a.val) * μ n a`. -/
def measureIntegral (μ : PadicMeasure p) (f : ℤ_[p] → ℤ_[p]) : ℤ_[p] :=
  limUnder atTop (riemannSum μ f)

theorem tendsto_riemannSum_measureIntegral (μ : PadicMeasure p) {f : ℤ_[p] → ℤ_[p]}
    (hf : Continuous f) :
    Tendsto (riemannSum μ f) atTop (nhds (measureIntegral μ f)) :=
  (cauchySeq_tendsto_of_complete (cauchySeq_riemannSum μ hf)).choose_spec |> fun h => by
    exact tendsto_nhds_limUnder ⟨_, h⟩

theorem measureIntegral_eq_of_tendsto (μ : PadicMeasure p) {f : ℤ_[p] → ℤ_[p]}
    {L : ℤ_[p]} (hL : Tendsto (riemannSum μ f) atTop (nhds L)) :
    measureIntegral μ f = L :=
  tendsto_nhds_unique (tendsto_nhds_limUnder ⟨L, hL⟩) hL

/-- Exact evaluation of `measureIntegral` on locally constant functions of level `m`. -/
theorem measureIntegral_eq_riemannSum_of_locallyConstant (μ : PadicMeasure p)
    {f : ℤ_[p] → ℤ_[p]} (m : ℕ)
    (hf : ∀ x y : ℤ_[p], PadicInt.toZModPow m x = PadicInt.toZModPow m y → f x = f y) :
    measureIntegral μ f = riemannSum μ f m := by
  refine measureIntegral_eq_of_tendsto μ ?_
  refine tendsto_atTop_of_eventually_const (i₀ := m) fun n hn => ?_
  have h0 : ‖riemannSum μ f n - riemannSum μ f m‖ ≤ 0 :=
    norm_riemannSum_sub_le_of_le μ hn le_rfl (fun x y hxy => by rw [hf x y hxy, sub_self, norm_zero])
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h0 (norm_nonneg _)))

/-- Uniform approximation bound: `‖measureIntegral μ f - riemannSum μ f m‖ ≤ B` whenever `f`
varies by at most `B` on balls of level `m` (independent of `μ`!). -/
theorem norm_measureIntegral_sub_riemannSum_le (μ : PadicMeasure p) {f : ℤ_[p] → ℤ_[p]}
    (hf : Continuous f) (m : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hmod : ∀ x y : ℤ_[p], PadicInt.toZModPow m x = PadicInt.toZModPow m y → ‖f x - f y‖ ≤ B) :
    ‖measureIntegral μ f - riemannSum μ f m‖ ≤ B := by
  have hlim : Tendsto (fun n => ‖riemannSum μ f n - riemannSum μ f m‖) atTop
      (nhds ‖measureIntegral μ f - riemannSum μ f m‖) :=
    ((tendsto_riemannSum_measureIntegral μ hf).sub_const _).norm
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop m] with n hn
  exact norm_riemannSum_sub_le_of_le μ hn hB hmod

theorem measureIntegral_zero_fun (μ : PadicMeasure p) :
    measureIntegral μ (fun _ => 0) = 0 := by
  rw [measureIntegral_eq_riemannSum_of_locallyConstant μ 0 (fun _ _ _ => rfl)]
  simp [riemannSum]

theorem measureIntegral_const (μ : PadicMeasure p) (c : ℤ_[p]) :
    measureIntegral μ (fun _ => c) = c * μ 0 0 := by
  rw [measureIntegral_eq_riemannSum_of_locallyConstant μ 0 (fun _ _ _ => rfl)]
  unfold riemannSum
  rw [Finset.sum_eq_single (0 : ZMod (p ^ 0))]
  · intro a _ ha; exact absurd (zmod_pow_zero_eq a 0) ha
  · intro h; exact absurd (Finset.mem_univ _) h

theorem measureIntegral_add_fun (μ : PadicMeasure p) {f g : ℤ_[p] → ℤ_[p]}
    (hf : Continuous f) (hg : Continuous g) :
    measureIntegral μ (fun x => f x + g x) = measureIntegral μ f + measureIntegral μ g := by
  refine measureIntegral_eq_of_tendsto μ ?_
  have hfun : riemannSum μ (fun x => f x + g x) = fun n => riemannSum μ f n + riemannSum μ g n :=
    funext (riemannSum_add_fun μ f g)
  rw [hfun]
  exact (tendsto_riemannSum_measureIntegral μ hf).add (tendsto_riemannSum_measureIntegral μ hg)

theorem measureIntegral_sub_fun (μ : PadicMeasure p) {f g : ℤ_[p] → ℤ_[p]}
    (hf : Continuous f) (hg : Continuous g) :
    measureIntegral μ (fun x => f x - g x) = measureIntegral μ f - measureIntegral μ g := by
  refine measureIntegral_eq_of_tendsto μ ?_
  have hfun : riemannSum μ (fun x => f x - g x) = fun n => riemannSum μ f n - riemannSum μ g n :=
    funext (riemannSum_sub_fun μ f g)
  rw [hfun]
  exact (tendsto_riemannSum_measureIntegral μ hf).sub (tendsto_riemannSum_measureIntegral μ hg)

theorem measureIntegral_smul_fun (μ : PadicMeasure p) (c : ℤ_[p]) {f : ℤ_[p] → ℤ_[p]}
    (hf : Continuous f) :
    measureIntegral μ (fun x => c * f x) = c * measureIntegral μ f := by
  refine measureIntegral_eq_of_tendsto μ ?_
  have hfun : riemannSum μ (fun x => c * f x) = fun n => c * riemannSum μ f n :=
    funext (riemannSum_smul_fun μ c f)
  rw [hfun]
  exact tendsto_const_nhds.mul (tendsto_riemannSum_measureIntegral μ hf)

theorem measureIntegral_sum_fun {ι : Type*} (s : Finset ι) (μ : PadicMeasure p)
    (f : ι → ℤ_[p] → ℤ_[p]) (hf : ∀ i ∈ s, Continuous (f i)) :
    measureIntegral μ (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, measureIntegral μ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [measureIntegral_zero_fun]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have hfa : Continuous (f a) := hf a (Finset.mem_insert_self a s)
    have hfs : Continuous (fun x => ∑ i ∈ s, f i x) :=
      continuous_finsetSum s fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [measureIntegral_add_fun μ hfa hfs, ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

theorem measureIntegral_add_measure (μ₁ μ₂ : PadicMeasure p) {f : ℤ_[p] → ℤ_[p]}
    (hf : Continuous f) :
    measureIntegral (μ₁ + μ₂) f = measureIntegral μ₁ f + measureIntegral μ₂ f := by
  refine measureIntegral_eq_of_tendsto (μ₁ + μ₂) ?_
  have hfun : riemannSum (μ₁ + μ₂) f = fun n => riemannSum μ₁ f n + riemannSum μ₂ f n :=
    funext (riemannSum_add_measure μ₁ μ₂ f)
  rw [hfun]
  exact (tendsto_riemannSum_measureIntegral μ₁ hf).add (tendsto_riemannSum_measureIntegral μ₂ hf)

theorem measureIntegral_sub_measure (μ₁ μ₂ : PadicMeasure p) {f : ℤ_[p] → ℤ_[p]}
    (hf : Continuous f) :
    measureIntegral (μ₁ - μ₂) f = measureIntegral μ₁ f - measureIntegral μ₂ f := by
  refine measureIntegral_eq_of_tendsto (μ₁ - μ₂) ?_
  have hfun : riemannSum (μ₁ - μ₂) f = fun n => riemannSum μ₁ f n - riemannSum μ₂ f n :=
    funext (riemannSum_sub_measure μ₁ μ₂ f)
  rw [hfun]
  exact (tendsto_riemannSum_measureIntegral μ₁ hf).sub (tendsto_riemannSum_measureIntegral μ₂ hf)

theorem measureIntegral_smul_measure (c : ℤ_[p]) (μ : PadicMeasure p) {f : ℤ_[p] → ℤ_[p]}
    (hf : Continuous f) :
    measureIntegral (c • μ) f = c * measureIntegral μ f := by
  refine measureIntegral_eq_of_tendsto (c • μ) ?_
  have hfun : riemannSum (c • μ) f = fun n => c * riemannSum μ f n :=
    funext (riemannSum_smul_measure c μ f)
  rw [hfun]
  exact tendsto_const_nhds.mul (tendsto_riemannSum_measureIntegral μ hf)

theorem measureIntegral_zero_measure (f : ℤ_[p] → ℤ_[p]) :
    measureIntegral (0 : PadicMeasure p) f = 0 := by
  refine measureIntegral_eq_of_tendsto (0 : PadicMeasure p) ?_
  have h : riemannSum (0 : PadicMeasure p) f = fun _ => 0 := by
    ext n; simp [riemannSum]
  rw [h]
  exact tendsto_const_nhds

/-- Sup-norm continuity of $p$-adic integration:
`∀ x, ‖f x - g x‖ ≤ B` implies `‖∫ f dμ - ∫ g dμ‖ ≤ B`. -/
theorem norm_measureIntegral_sub_le (μ : PadicMeasure p) {f g : ℤ_[p] → ℤ_[p]}
    (hf : Continuous f) (hg : Continuous g) {B : ℝ} (hB : 0 ≤ B)
    (hfg : ∀ x : ℤ_[p], ‖f x - g x‖ ≤ B) :
    ‖measureIntegral μ f - measureIntegral μ g‖ ≤ B := by
  have hlim : Tendsto (fun n => ‖riemannSum μ f n - riemannSum μ g n‖) atTop
      (nhds ‖measureIntegral μ f - measureIntegral μ g‖) :=
    ((tendsto_riemannSum_measureIntegral μ hf).sub
      (tendsto_riemannSum_measureIntegral μ hg)).norm
  refine le_of_tendsto' hlim fun n => ?_
  rw [← riemannSum_sub_fun]
  refine padicInt_norm_sum_le _ _ hB fun a _ => ?_
  rw [norm_mul]
  calc ‖f (a.val : ℤ_[p]) - g (a.val : ℤ_[p])‖ * ‖μ n a‖
      ≤ B * 1 := mul_le_mul (hfg _) (PadicInt.norm_le_one _) (norm_nonneg _) hB
    _ = B := mul_one B

theorem norm_measureIntegral_le (μ : PadicMeasure p) {f : ℤ_[p] → ℤ_[p]}
    (hf : Continuous f) {B : ℝ} (hB : 0 ≤ B) (h : ∀ x : ℤ_[p], ‖f x‖ ≤ B) :
    ‖measureIntegral μ f‖ ≤ B := by
  have hsub := norm_measureIntegral_sub_le μ hf (g := fun _ => 0) continuous_const hB
    (fun x => by simpa using h x)
  rwa [measureIntegral_zero_fun, sub_zero] at hsub

/-- Integration against a Dirac measure evaluates the function at the point. -/
theorem measureIntegral_dirac (x : ℤ_[p]) {f : ℤ_[p] → ℤ_[p]} (hf : Continuous f) :
    measureIntegral (diracMeasure x) f = f x := by
  refine measureIntegral_eq_of_tendsto (diracMeasure x) ?_
  have hr : riemannSum (diracMeasure x) f = fun n => f ((PadicInt.toZModPow n x).val : ℤ_[p]) := by
    ext n
    unfold riemannSum
    rw [Finset.sum_eq_single (PadicInt.toZModPow n x)]
    · simp [diracMeasure]
    · intro a _ ha; simp [diracMeasure, ha.symm]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hr]
  have hseq : Tendsto (fun n : ℕ => ((PadicInt.toZModPow n x).val : ℤ_[p])) atTop (nhds x) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := PadicInt.exists_pow_neg_lt p hε
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    have hmod : PadicInt.toZModPow n ((PadicInt.toZModPow n x).val : ℤ_[p]) =
        PadicInt.toZModPow n x := by
      have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
      rw [map_natCast, ZMod.natCast_zmod_val]
    have hle : ‖((PadicInt.toZModPow n x).val : ℤ_[p]) - x‖ ≤ (p : ℝ) ^ (-(n : ℤ)) :=
      padicInt_norm_le_pow_of_toZModPow_eq hmod
    have hmono : (p : ℝ) ^ (-(n : ℤ)) ≤ (p : ℝ) ^ (-(N : ℤ)) := by
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_le
      exact zpow_le_zpow_right₀ hp1 (by omega)
    exact (hle.trans hmono).trans_lt hN
  exact (hf.tendsto x).comp hseq

/-- Locally constant indicator function of a residue class mod `p ^ n`. -/
def ballIndicator (n : ℕ) (a : ZMod (p ^ n)) (x : ℤ_[p]) : ℤ_[p] :=
  if PadicInt.toZModPow n x = a then 1 else 0

lemma continuous_ballIndicator (n : ℕ) (a : ZMod (p ^ n)) :
    Continuous (ballIndicator (p := p) n a) := by
  rw [Metric.continuous_iff]
  intro x ε hε
  refine ⟨(p : ℝ) ^ (-(n : ℤ)), zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _, fun y hy => ?_⟩
  have hnorm : ‖y - x‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
    rw [dist_eq_norm] at hy; exact hy.le
  have hmod : PadicInt.toZModPow n y = PadicInt.toZModPow n x :=
    padicInt_toZModPow_eq_of_norm_le_pow hnorm
  simp [ballIndicator, hmod, hε]

theorem measureIntegral_ballIndicator (μ : PadicMeasure p) (n : ℕ) (a : ZMod (p ^ n)) :
    measureIntegral μ (ballIndicator n a) = μ n a := by
  rw [measureIntegral_eq_riemannSum_of_locallyConstant μ n
    (fun x y hxy => by simp [ballIndicator, hxy])]
  unfold riemannSum
  rw [Finset.sum_eq_single a]
  · have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
    simp [ballIndicator]
  · intro b _ hb
    have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
    simp [ballIndicator, hb]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Pushforward of a $p$-adic measure along a continuous map `φ : ℤ_[p] → ℤ_[p]`. -/
def pushforwardMeasure (φ : ℤ_[p] → ℤ_[p]) (hφ : Continuous φ) (μ : PadicMeasure p) :
    PadicMeasure p where
  toFun n a := measureIntegral μ (fun x => ballIndicator n a (φ x))
  compat n a := by
    have hcont : ∀ b : ZMod (p ^ (n + 1)), Continuous (fun x => ballIndicator (p := p) (n + 1) b (φ x)) :=
      fun b => (continuous_ballIndicator (n + 1) b).comp hφ
    rw [← measureIntegral_sum_fun _ μ _ (fun b _ => hcont b)]
    congr 1
    ext x
    by_cases h : PadicInt.toZModPow n (φ x) = a
    · simp only [ballIndicator, if_pos h]
      rw [Finset.sum_eq_single (PadicInt.toZModPow (n + 1) (φ x))]
      · simp
      · intro b _ hb; simp [hb.symm]
      · intro hnot
        exfalso
        apply hnot
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [zmodPowStep, zmodPowCast_toZModPow (Nat.le_succ n), h]
    · simp only [ballIndicator, if_neg h]
      symm
      refine Finset.sum_eq_zero fun b hb => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      have hne : PadicInt.toZModPow (n + 1) (φ x) ≠ b := by
        intro heq
        apply h
        have hstep := zmodPowCast_toZModPow (p := p) (Nat.le_succ n) (φ x)
        rw [heq] at hstep
        exact hstep.symm.trans hb
      simp [hne]

/-- Change-of-variables theorem for pushforward measures:
`∫ g d(φ_* μ) = ∫ (g ∘ φ) dμ` for every continuous `g : ℤ_[p] → ℤ_[p]`. -/
theorem measureIntegral_pushforward {φ : ℤ_[p] → ℤ_[p]} (hφ : Continuous φ)
    (μ : PadicMeasure p) {g : ℤ_[p] → ℤ_[p]} (hg : Continuous g) :
    measureIntegral (pushforwardMeasure φ hφ μ) g = measureIntegral μ (fun x => g (φ x)) := by
  refine padicInt_eq_of_forall_norm_le_pow fun m => ?_
  have hp_pos : (0 : ℝ) < (p : ℝ) ^ (-(m : ℤ)) :=
    zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  obtain ⟨N, hN⟩ := exists_level_of_continuous hg ((p : ℝ) ^ (-(m : ℤ))) hp_pos
  have h1 : ‖measureIntegral (pushforwardMeasure φ hφ μ) g -
      riemannSum (pushforwardMeasure φ hφ μ) g N‖ ≤ (p : ℝ) ^ (-(m : ℤ)) :=
    norm_measureIntegral_sub_riemannSum_le _ hg N hp_pos.le hN
  have hsum_eq : riemannSum (pushforwardMeasure φ hφ μ) g N =
      measureIntegral μ (fun x => ∑ a : ZMod (p ^ N),
        g (a.val : ℤ_[p]) * ballIndicator N a (φ x)) := by
    rw [measureIntegral_sum_fun]
    · unfold riemannSum pushforwardMeasure
      refine Finset.sum_congr rfl fun a _ => ?_
      exact (measureIntegral_smul_fun μ (g (a.val : ℤ_[p]))
        ((continuous_ballIndicator N a).comp hφ)).symm
    · intro a _
      exact continuous_const.mul ((continuous_ballIndicator N a).comp hφ)
  have h2 : ‖measureIntegral μ (fun x => ∑ a : ZMod (p ^ N),
      g (a.val : ℤ_[p]) * ballIndicator N a (φ x)) -
      measureIntegral μ (fun x => g (φ x))‖ ≤ (p : ℝ) ^ (-(m : ℤ)) := by
    have hf1 : Continuous (fun x => ∑ a : ZMod (p ^ N),
        g (a.val : ℤ_[p]) * ballIndicator N a (φ x)) :=
      continuous_finsetSum _ fun a _ => continuous_const.mul ((continuous_ballIndicator N a).comp hφ)
    refine norm_measureIntegral_sub_le μ hf1 (hg.comp hφ) hp_pos.le fun x => ?_
    have heval : ∑ a : ZMod (p ^ N), g (a.val : ℤ_[p]) * ballIndicator N a (φ x) =
        g ((PadicInt.toZModPow N (φ x)).val : ℤ_[p]) := by
      rw [Finset.sum_eq_single (PadicInt.toZModPow N (φ x))]
      · simp [ballIndicator]
      · intro a _ ha; simp [ballIndicator, ha.symm]
      · intro h; exact absurd (Finset.mem_univ _) h
    change ‖(∑ a : ZMod (p ^ N), g (a.val : ℤ_[p]) * ballIndicator N a (φ x)) - g (φ x)‖ ≤ _
    rw [heval]
    refine hN _ _ ?_
    have : NeZero (p ^ N) := ⟨pow_ne_zero N (Fact.out : p.Prime).ne_zero⟩
    rw [map_natCast, ZMod.natCast_zmod_val]
  have hdecomp : measureIntegral (pushforwardMeasure φ hφ μ) g -
      measureIntegral μ (fun x => g (φ x)) =
      (measureIntegral (pushforwardMeasure φ hφ μ) g -
        riemannSum (pushforwardMeasure φ hφ μ) g N) +
      (riemannSum (pushforwardMeasure φ hφ μ) g N -
        measureIntegral μ (fun x => g (φ x))) := by ring
  rw [hdecomp]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ?_)
  rwa [hsum_eq]

/-- Indicator of the unit group `ℤ_[p]ˣ` (elements with nonzero residue mod `p`). -/
def unitIndicator (x : ℤ_[p]) : ℤ_[p] :=
  if PadicInt.toZMod x ≠ 0 then 1 else 0

lemma continuous_unitIndicator : Continuous (unitIndicator (p := p)) := by
  have h1 : unitIndicator (p := p) = fun x => 1 - ballIndicator 1 0 x := by
    ext x
    have heq : (PadicInt.toZModPow 1 x = 0) ↔ (PadicInt.toZMod x = 0) := by
      have h10 : (PadicInt.toZModPow 1 x = 0) ↔ x ∈ Ideal.span ({(p : ℤ_[p]) ^ 1} : Set ℤ_[p]) := by
        rw [← PadicInt.ker_toZModPow, RingHom.mem_ker]
      have h20 : (PadicInt.toZMod x = 0) ↔ x ∈ Ideal.span ({(p : ℤ_[p])} : Set ℤ_[p]) := by
        rw [← padicInt_ker_toZMod_eq_span_p, RingHom.mem_ker]
      rw [h10, h20, pow_one]
    unfold unitIndicator ballIndicator
    by_cases hx : PadicInt.toZMod x = 0
    · rw [if_neg (not_not.mpr hx), if_pos (heq.mpr hx), sub_self]
    · rw [if_pos hx, if_neg (fun h => hx (heq.mp h)), sub_zero]
  rw [h1]
  exact continuous_const.sub (continuous_ballIndicator 1 0)

/-- Restriction of a $p$-adic measure `μ` to the unit group `ℤ_[p]ˣ` (removing `p ℤ_[p]`). -/
def PadicMeasure.restrictUnits (μ : PadicMeasure p) : PadicMeasure p where
  toFun n a := measureIntegral μ (fun x => unitIndicator x * ballIndicator n a x)
  compat n a := by
    have hcont : ∀ b : ZMod (p ^ (n + 1)),
        Continuous (fun x => unitIndicator x * ballIndicator (p := p) (n + 1) b x) :=
      fun b => continuous_unitIndicator.mul (continuous_ballIndicator (n + 1) b)
    rw [← measureIntegral_sum_fun _ μ _ (fun b _ => hcont b)]
    congr 1
    ext x
    rw [← Finset.mul_sum]
    congr 1
    by_cases h : PadicInt.toZModPow n x = a
    · simp only [ballIndicator, if_pos h]
      rw [Finset.sum_eq_single (PadicInt.toZModPow (n + 1) x)]
      · simp
      · intro b _ hb; simp [hb.symm]
      · intro hnot
        exfalso
        apply hnot
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [zmodPowStep, zmodPowCast_toZModPow (Nat.le_succ n), h]
    · simp only [ballIndicator, if_neg h]
      symm
      refine Finset.sum_eq_zero fun b hb => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      have hne : PadicInt.toZModPow (n + 1) x ≠ b := by
        intro heq
        apply h
        have hstep := zmodPowCast_toZModPow (p := p) (Nat.le_succ n) x
        rw [heq] at hstep
        exact hstep.symm.trans hb
      simp [hne]

/-- Explicit level-`(n + 1)` formula for `μ.restrictUnits`. -/
theorem PadicMeasure.restrictUnits_succ (μ : PadicMeasure p) (n : ℕ) (a : ZMod (p ^ (n + 1))) :
    μ.restrictUnits (n + 1) a =
      if zmodPowCast (p := p) (Nat.succ_le_succ (Nat.zero_le n)) a ≠ 0 then μ (n + 1) a else 0 := by
  change measureIntegral μ (fun x => unitIndicator x * ballIndicator (n + 1) a x) = _
  have hloc : ∀ x y : ℤ_[p], PadicInt.toZModPow (n + 1) x = PadicInt.toZModPow (n + 1) y →
      unitIndicator x * ballIndicator (n + 1) a x = unitIndicator y * ballIndicator (n + 1) a y := by
    intro x y hxy
    have h1 : PadicInt.toZModPow 1 x = PadicInt.toZModPow 1 y := by
      rw [← zmodPowCast_toZModPow (Nat.succ_le_succ (Nat.zero_le n)) x,
        ← zmodPowCast_toZModPow (Nat.succ_le_succ (Nat.zero_le n)) y, hxy]
    have h0 : (PadicInt.toZMod x = 0) ↔ (PadicInt.toZMod y = 0) := by
      have hx : PadicInt.toZMod x = 0 ↔ PadicInt.toZModPow 1 x = 0 := by
        rw [← RingHom.mem_ker, ← RingHom.mem_ker, padicInt_ker_toZMod_eq_span_p,
          PadicInt.ker_toZModPow, pow_one]
      have hy : PadicInt.toZMod y = 0 ↔ PadicInt.toZModPow 1 y = 0 := by
        rw [← RingHom.mem_ker, ← RingHom.mem_ker, padicInt_ker_toZMod_eq_span_p,
          PadicInt.ker_toZModPow, pow_one]
      rw [hx, hy, h1]
    simp [unitIndicator, ballIndicator, hxy, h0]
  rw [measureIntegral_eq_riemannSum_of_locallyConstant μ (n + 1) hloc]
  unfold riemannSum
  rw [Finset.sum_eq_single a]
  · dsimp only
    have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero (n + 1) (Fact.out : p.Prime).ne_zero⟩
    have hba : ballIndicator (p := p) (n + 1) a (a.val : ℤ_[p]) = 1 := by
      simp [ballIndicator]
    rw [hba, mul_one]
    have hcond : (PadicInt.toZMod (a.val : ℤ_[p]) ≠ 0) ↔
        (zmodPowCast (p := p) (Nat.succ_le_succ (Nat.zero_le n)) a ≠ 0) := by
      rw [not_iff_not]
      have hx : PadicInt.toZMod (a.val : ℤ_[p]) = 0 ↔ PadicInt.toZModPow 1 (a.val : ℤ_[p]) = 0 := by
        rw [← RingHom.mem_ker, ← RingHom.mem_ker, padicInt_ker_toZMod_eq_span_p,
          PadicInt.ker_toZModPow, pow_one]
      rw [hx, padicInt_toZModPow_val_eq (Nat.succ_le_succ (Nat.zero_le n)) a]
    unfold unitIndicator
    by_cases h1 : PadicInt.toZMod (a.val : ℤ_[p]) ≠ 0
    · rw [if_pos h1, if_pos (hcond.mp h1), one_mul]
    · rw [if_neg h1, if_neg (fun h2 => h1 (hcond.mpr h2)), zero_mul]
  · intro b _ hb
    dsimp only
    have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero (n + 1) (Fact.out : p.Prime).ne_zero⟩
    simp [ballIndicator, hb]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Integration against `μ.restrictUnits` equals integration of `unitIndicator * f` against `μ`. -/
theorem measureIntegral_restrictUnits (μ : PadicMeasure p) {f : ℤ_[p] → ℤ_[p]}
    (hf : Continuous f) :
    measureIntegral μ.restrictUnits f = measureIntegral μ (fun x => unitIndicator x * f x) := by
  refine padicInt_eq_of_forall_norm_le_pow fun m => ?_
  have hp_pos : (0 : ℝ) < (p : ℝ) ^ (-(m : ℤ)) :=
    zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  obtain ⟨N, hN⟩ := exists_level_of_continuous hf ((p : ℝ) ^ (-(m : ℤ))) hp_pos
  have h1 : ‖measureIntegral μ.restrictUnits f - riemannSum μ.restrictUnits f N‖ ≤
      (p : ℝ) ^ (-(m : ℤ)) :=
    norm_measureIntegral_sub_riemannSum_le μ.restrictUnits hf N hp_pos.le hN
  have hsum_eq : riemannSum μ.restrictUnits f N =
      measureIntegral μ (fun x => unitIndicator x *
        ∑ a : ZMod (p ^ N), f (a.val : ℤ_[p]) * ballIndicator N a x) := by
    have hfun : (fun x => unitIndicator x *
        ∑ a : ZMod (p ^ N), f (a.val : ℤ_[p]) * ballIndicator N a x) =
        (fun x => ∑ a : ZMod (p ^ N), f (a.val : ℤ_[p]) * (unitIndicator x * ballIndicator N a x)) := by
      ext x; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => by ring
    rw [hfun, measureIntegral_sum_fun]
    · unfold riemannSum PadicMeasure.restrictUnits
      refine Finset.sum_congr rfl fun a _ => ?_
      exact (measureIntegral_smul_fun μ (f (a.val : ℤ_[p]))
        (continuous_unitIndicator.mul (continuous_ballIndicator N a))).symm
    · intro a _
      exact continuous_const.mul (continuous_unitIndicator.mul (continuous_ballIndicator N a))
  have h2 : ‖measureIntegral μ (fun x => unitIndicator x *
        ∑ a : ZMod (p ^ N), f (a.val : ℤ_[p]) * ballIndicator N a x) -
      measureIntegral μ (fun x => unitIndicator x * f x)‖ ≤ (p : ℝ) ^ (-(m : ℤ)) := by
    have hf1 : Continuous (fun x => unitIndicator x *
        ∑ a : ZMod (p ^ N), f (a.val : ℤ_[p]) * ballIndicator N a x) :=
      continuous_unitIndicator.mul (continuous_finsetSum _ fun a _ =>
        continuous_const.mul (continuous_ballIndicator N a))
    refine norm_measureIntegral_sub_le μ hf1 (continuous_unitIndicator.mul hf) hp_pos.le fun x => ?_
    change ‖unitIndicator x * (∑ a : ZMod (p ^ N), f (a.val : ℤ_[p]) * ballIndicator N a x) -
      unitIndicator x * f x‖ ≤ _
    have heval : ∑ a : ZMod (p ^ N), f (a.val : ℤ_[p]) * ballIndicator N a x =
        f ((PadicInt.toZModPow N x).val : ℤ_[p]) := by
      rw [Finset.sum_eq_single (PadicInt.toZModPow N x)]
      · simp [ballIndicator]
      · intro a _ ha; simp [ballIndicator, ha.symm]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [heval, ← mul_sub, norm_mul]
    have hmod : PadicInt.toZModPow N ((PadicInt.toZModPow N x).val : ℤ_[p]) =
        PadicInt.toZModPow N x := by
      have : NeZero (p ^ N) := ⟨pow_ne_zero N (Fact.out : p.Prime).ne_zero⟩
      rw [map_natCast, ZMod.natCast_zmod_val]
    calc ‖unitIndicator x‖ * ‖f ((PadicInt.toZModPow N x).val : ℤ_[p]) - f x‖
        ≤ 1 * (p : ℝ) ^ (-(m : ℤ)) :=
          mul_le_mul (PadicInt.norm_le_one _) (hN _ _ hmod) (norm_nonneg _) zero_le_one
      _ = (p : ℝ) ^ (-(m : ℤ)) := one_mul _
  have hdecomp : measureIntegral μ.restrictUnits f -
      measureIntegral μ (fun x => unitIndicator x * f x) =
      (measureIntegral μ.restrictUnits f - riemannSum μ.restrictUnits f N) +
      (riemannSum μ.restrictUnits f N - measureIntegral μ (fun x => unitIndicator x * f x)) := by ring
  rw [hdecomp]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ?_)
  rwa [hsum_eq]

/-- Sup-norm continuity of unit-restricted integration: only values on `ℤ_[p]ˣ` matter! -/
theorem norm_measureIntegral_restrictUnits_sub_le (μ : PadicMeasure p) {f g : ℤ_[p] → ℤ_[p]}
    (hf : Continuous f) (hg : Continuous g) {B : ℝ} (hB : 0 ≤ B)
    (hfg : ∀ x : ℤ_[p], PadicInt.toZMod x ≠ 0 → ‖f x - g x‖ ≤ B) :
    ‖measureIntegral μ.restrictUnits f - measureIntegral μ.restrictUnits g‖ ≤ B := by
  rw [measureIntegral_restrictUnits μ hf, measureIntegral_restrictUnits μ hg]
  refine norm_measureIntegral_sub_le μ (continuous_unitIndicator.mul hf)
    (continuous_unitIndicator.mul hg) hB fun x => ?_
  change ‖unitIndicator x * f x - unitIndicator x * g x‖ ≤ B
  unfold unitIndicator
  split_ifs with hx
  · simpa using hfg x hx
  · simp [hB]

end PadicMeasureCore

/-! ## Section 2: Concrete Amice–Mahler–Iwasawa Isomorphism `PadicMeasure p ≃+* IwasawaAlg p` -/

section AmiceMahlerIwasawa

variable {p : ℕ} [Fact p.Prime]

/-- The `k`-th Mahler binomial function `x ↦ C(x, k)` on `ℤ_[p]`, agreeing with `n.choose k` on `ℕ`. -/
def mahlerBinom (k : ℕ) (x : ℤ_[p]) : ℤ_[p] :=
  mahler k x

lemma continuous_mahlerBinom (k : ℕ) : Continuous (mahlerBinom (p := p) k) :=
  (mahler k).continuous

@[simp] lemma mahlerBinom_natCast (k n : ℕ) :
    mahlerBinom (p := p) k (n : ℤ_[p]) = (n.choose k : ℤ_[p]) :=
  mahler_natCast_eq k n

lemma mahlerBinom_zero (x : ℤ_[p]) : mahlerBinom (p := p) 0 x = 1 := by
  have hcont : Continuous (fun y : ℤ_[p] => mahlerBinom (p := p) 0 y) := continuous_mahlerBinom 0
  have heq : (fun y : ℤ_[p] => mahlerBinom (p := p) 0 y) = fun _ => 1 :=
    PadicInt.denseRange_natCast.equalizer hcont continuous_const (by ext n; simp [mahlerBinom_natCast])
  exact congrFun heq x

lemma mahlerBinom_one (x : ℤ_[p]) : mahlerBinom (p := p) 1 x = x := by
  have hcont : Continuous (fun y : ℤ_[p] => mahlerBinom (p := p) 1 y) := continuous_mahlerBinom 1
  have heq : (fun y : ℤ_[p] => mahlerBinom (p := p) 1 y) = id :=
    PadicInt.denseRange_natCast.equalizer hcont continuous_id (by ext n; simp [mahlerBinom_natCast])
  exact congrFun heq x

lemma mahlerBinom_eval_zero (k : ℕ) :
    mahlerBinom (p := p) k 0 = if k = 0 then 1 else 0 := by
  have h := mahlerBinom_natCast (p := p) k 0
  rw [Nat.cast_zero] at h
  rw [h]
  cases k with
  | zero => simp
  | succ k => simp

lemma mahlerBinom_eval_one (k : ℕ) :
    mahlerBinom (p := p) k 1 = if k ≤ 1 then 1 else 0 := by
  have h := mahlerBinom_natCast (p := p) k 1
  rw [Nat.cast_one] at h
  rw [h]
  rcases k with _ | _ | k
  · simp
  · simp
  · simp [Nat.choose_eq_zero_of_lt]

/-- Vandermonde's identity for Mahler binomial functions on ALL of `ℤ_[p] × ℤ_[p]`:
`C(x + y, k) = ∑_{i + j = k} C(x, i) * C(y, j)`. -/
theorem mahlerBinom_add (k : ℕ) (x y : ℤ_[p]) :
    mahlerBinom (p := p) k (x + y) =
      ∑ ab ∈ Finset.antidiagonal k, mahlerBinom (p := p) ab.1 x * mahlerBinom (p := p) ab.2 y := by
  have hnat_y : ∀ (n : ℕ) (z : ℤ_[p]),
      mahlerBinom (p := p) k ((n : ℤ_[p]) + z) =
        ∑ ab ∈ Finset.antidiagonal k,
          mahlerBinom (p := p) ab.1 (n : ℤ_[p]) * mahlerBinom (p := p) ab.2 z := by
    intro n
    have hL : Continuous (fun z : ℤ_[p] => mahlerBinom (p := p) k ((n : ℤ_[p]) + z)) :=
      (continuous_mahlerBinom k).comp (continuous_const.add continuous_id)
    have hR : Continuous (fun z : ℤ_[p] => ∑ ab ∈ Finset.antidiagonal k,
        mahlerBinom (p := p) ab.1 (n : ℤ_[p]) * mahlerBinom (p := p) ab.2 z) :=
      continuous_finsetSum _ fun ab _ => continuous_const.mul (continuous_mahlerBinom ab.2)
    have heq := PadicInt.denseRange_natCast.equalizer hL hR (by
      ext m
      dsimp only [Function.comp_apply]
      rw [← Nat.cast_add, mahlerBinom_natCast]
      simp_rw [mahlerBinom_natCast, ← Nat.cast_mul, ← Nat.cast_sum]
      exact congrArg Nat.cast (Nat.add_choose_eq n m k))
    exact congrFun heq
  have hL : Continuous (fun w : ℤ_[p] => mahlerBinom (p := p) k (w + y)) :=
    (continuous_mahlerBinom k).comp (continuous_id.add continuous_const)
  have hR : Continuous (fun w : ℤ_[p] => ∑ ab ∈ Finset.antidiagonal k,
      mahlerBinom (p := p) ab.1 w * mahlerBinom (p := p) ab.2 y) :=
    continuous_finsetSum _ fun ab _ => (continuous_mahlerBinom ab.1).mul continuous_const
  have heq := PadicInt.denseRange_natCast.equalizer hL hR (by
    ext n
    exact hnat_y n y)
  exact congrFun heq x

/-- The **Amice–Mahler–Iwasawa Transform** `PadicMeasure p → ℤ_[p][[T]]`:
`μ ↦ ∑_{k ≥ 0} (∫_{ℤ_[p]} C(x, k) dμ(x)) T^k`. -/
def iwasawaTransform (μ : PadicMeasure p) : IwasawaAlg p :=
  PowerSeries.mk (fun k => measureIntegral μ (mahlerBinom k))

@[simp] lemma coeff_iwasawaTransform (μ : PadicMeasure p) (k : ℕ) :
    PowerSeries.coeff k (iwasawaTransform μ) = measureIntegral μ (mahlerBinom k) :=
  PowerSeries.coeff_mk k _

theorem iwasawaTransform_zero : iwasawaTransform (0 : PadicMeasure p) = 0 := by
  ext k
  rw [coeff_iwasawaTransform, map_zero, measureIntegral_zero_measure]

theorem iwasawaTransform_add (μ₁ μ₂ : PadicMeasure p) :
    iwasawaTransform (μ₁ + μ₂) = iwasawaTransform μ₁ + iwasawaTransform μ₂ := by
  ext k
  rw [coeff_iwasawaTransform, map_add, coeff_iwasawaTransform, coeff_iwasawaTransform,
    measureIntegral_add_measure μ₁ μ₂ (continuous_mahlerBinom k)]

theorem iwasawaTransform_smul (c : ℤ_[p]) (μ : PadicMeasure p) :
    iwasawaTransform (c • μ) = PowerSeries.C c * iwasawaTransform μ := by
  ext k
  rw [coeff_iwasawaTransform, PowerSeries.coeff_C_mul, coeff_iwasawaTransform,
    measureIntegral_smul_measure c μ (continuous_mahlerBinom k)]

theorem iwasawaTransform_one : iwasawaTransform (1 : PadicMeasure p) = 1 := by
  ext k
  rw [coeff_iwasawaTransform, PowerSeries.coeff_one]
  change measureIntegral (diracMeasure 0) (mahlerBinom k) = _
  rw [measureIntegral_dirac 0 (continuous_mahlerBinom k), mahlerBinom_eval_zero]

/-- `iwasawaTransform (δ_1) = 1 + T`. -/
theorem iwasawaTransform_dirac_one :
    iwasawaTransform (diracMeasure (p := p) 1) = 1 + PowerSeries.X := by
  ext k
  rw [coeff_iwasawaTransform, measureIntegral_dirac 1 (continuous_mahlerBinom k),
    mahlerBinom_eval_one, map_add, PowerSeries.coeff_one, PowerSeries.coeff_X]
  rcases k with _ | _ | k
  · simp
  · simp
  · simp

/-- **Exact Convolution = Multiplication Theorem**:
`iwasawaTransform (μ₁ * μ₂) = iwasawaTransform μ₁ * iwasawaTransform μ₂`. -/
theorem iwasawaTransform_mul (μ₁ μ₂ : PadicMeasure p) :
    iwasawaTransform (μ₁ * μ₂) = iwasawaTransform μ₁ * iwasawaTransform μ₂ := by
  ext k
  rw [coeff_iwasawaTransform, PowerSeries.coeff_mul]
  simp_rw [coeff_iwasawaTransform]
  refine padicInt_eq_of_forall_norm_le_pow fun m => ?_
  have hp_pos : (0 : ℝ) < (p : ℝ) ^ (-(m : ℤ)) :=
    zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  have hlimL : Tendsto (fun n => riemannSum (μ₁ * μ₂) (mahlerBinom k) n) atTop
      (nhds (measureIntegral (μ₁ * μ₂) (mahlerBinom k))) :=
    tendsto_riemannSum_measureIntegral (μ₁ * μ₂) (continuous_mahlerBinom k)
  have hlimR : Tendsto (fun n => ∑ ab ∈ Finset.antidiagonal k,
      riemannSum μ₁ (mahlerBinom ab.1) n * riemannSum μ₂ (mahlerBinom ab.2) n) atTop
      (nhds (∑ ab ∈ Finset.antidiagonal k,
        measureIntegral μ₁ (mahlerBinom ab.1) * measureIntegral μ₂ (mahlerBinom ab.2))) :=
    tendsto_finsetSum _ fun ab _ =>
      (tendsto_riemannSum_measureIntegral μ₁ (continuous_mahlerBinom ab.1)).mul
        (tendsto_riemannSum_measureIntegral μ₂ (continuous_mahlerBinom ab.2))
  have hlimDiff : Tendsto (fun n => ‖riemannSum (μ₁ * μ₂) (mahlerBinom k) n -
      ∑ ab ∈ Finset.antidiagonal k,
        riemannSum μ₁ (mahlerBinom ab.1) n * riemannSum μ₂ (mahlerBinom ab.2) n‖) atTop
      (nhds ‖measureIntegral (μ₁ * μ₂) (mahlerBinom k) -
        ∑ ab ∈ Finset.antidiagonal k,
          measureIntegral μ₁ (mahlerBinom ab.1) * measureIntegral μ₂ (mahlerBinom ab.2)‖) :=
    (hlimL.sub hlimR).norm
  obtain ⟨N, hN⟩ := exists_level_of_continuous (continuous_mahlerBinom (p := p) k)
    ((p : ℝ) ^ (-(m : ℤ))) hp_pos
  refine le_of_tendsto hlimDiff ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  have hL_eq : riemannSum (μ₁ * μ₂) (mahlerBinom k) n =
      ∑ a : ZMod (p ^ n), ∑ b : ZMod (p ^ n),
        mahlerBinom k (((a + b).val : ℤ_[p])) * (μ₁ n a * μ₂ n b) := by
    unfold riemannSum
    simp only [PadicMeasure.mul_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_bij (fun c _ => c - a) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro c₁ _ c₂ _ h; exact sub_left_inj.mp h
    · intro b _; exact ⟨a + b, Finset.mem_univ _, add_sub_cancel_left a b⟩
    · intro c _; rw [add_sub_cancel]
  have hR_eq : ∑ ab ∈ Finset.antidiagonal k,
      riemannSum μ₁ (mahlerBinom ab.1) n * riemannSum μ₂ (mahlerBinom ab.2) n =
      ∑ a : ZMod (p ^ n), ∑ b : ZMod (p ^ n),
        mahlerBinom k ((a.val : ℤ_[p]) + (b.val : ℤ_[p])) * (μ₁ n a * μ₂ n b) := by
    have h1 : ∀ ab : ℕ × ℕ,
        riemannSum μ₁ (mahlerBinom ab.1) n * riemannSum μ₂ (mahlerBinom ab.2) n =
        ∑ a : ZMod (p ^ n), ∑ b : ZMod (p ^ n),
          (mahlerBinom ab.1 (a.val : ℤ_[p]) * mahlerBinom ab.2 (b.val : ℤ_[p])) *
            (μ₁ n a * μ₂ n b) := by
      intro ab
      unfold riemannSum
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => by ring
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_mul, ← mahlerBinom_add k (a.val : ℤ_[p]) (b.val : ℤ_[p])]
  rw [hL_eq, hR_eq, ← Finset.sum_sub_distrib]
  refine padicInt_norm_sum_le _ _ hp_pos.le fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine padicInt_norm_sum_le _ _ hp_pos.le fun b _ => ?_
  rw [← sub_mul, norm_mul]
  have hmod : PadicInt.toZModPow N (((a + b).val : ℤ_[p])) =
      PadicInt.toZModPow N ((a.val : ℤ_[p]) + (b.val : ℤ_[p])) := by
    rw [padicInt_toZModPow_val_eq hn (a + b), map_add,
      map_add, padicInt_toZModPow_val_eq hn a, padicInt_toZModPow_val_eq hn b]
  have hdiff : ‖mahlerBinom (p := p) k (((a + b).val : ℤ_[p])) -
      mahlerBinom (p := p) k ((a.val : ℤ_[p]) + (b.val : ℤ_[p]))‖ ≤ (p : ℝ) ^ (-(m : ℤ)) :=
    hN _ _ hmod
  calc ‖mahlerBinom (p := p) k (((a + b).val : ℤ_[p])) -
        mahlerBinom (p := p) k ((a.val : ℤ_[p]) + (b.val : ℤ_[p]))‖ * ‖μ₁ n a * μ₂ n b‖
      ≤ (p : ℝ) ^ (-(m : ℤ)) * 1 :=
        mul_le_mul hdiff (PadicInt.norm_le_one _) (norm_nonneg _) hp_pos.le
    _ = (p : ℝ) ^ (-(m : ℤ)) := mul_one _

/-- The Amice–Mahler–Iwasawa ring homomorphism `PadicMeasure p →+* IwasawaAlg p`. -/
def iwasawaTransformRingHom : PadicMeasure p →+* IwasawaAlg p where
  toFun := iwasawaTransform
  map_one' := iwasawaTransform_one
  map_mul' := iwasawaTransform_mul
  map_zero' := iwasawaTransform_zero
  map_add' := iwasawaTransform_add

/-- The Amice–Mahler–Iwasawa `ℤ_[p]`-algebra homomorphism `PadicMeasure p →ₐ[ℤ_[p]] IwasawaAlg p`. -/
def iwasawaTransformAlgHom : PadicMeasure p →ₐ[ℤ_[p]] IwasawaAlg p where
  toRingHom := iwasawaTransformRingHom
  commutes' c := by
    change iwasawaTransform (c • (1 : PadicMeasure p)) = PowerSeries.C c
    rw [iwasawaTransform_smul, iwasawaTransform_one, mul_one]

/-! ### Finite-Level Convolution Algebra `LevelAlg p n` & Exact Inverse `iwasawaInv` -/

/-- Level-`n` finite group algebra `ℤ_[p][ZMod (p ^ n)]` with convolution multiplication. -/
@[ext]
structure LevelAlg (p : ℕ) [Fact p.Prime] (n : ℕ) where
  toFun : ZMod (p ^ n) → ℤ_[p]

instance (n : ℕ) : CoeFun (LevelAlg p n) (fun _ => ZMod (p ^ n) → ℤ_[p]) where
  coe := LevelAlg.toFun

instance (n : ℕ) : Zero (LevelAlg p n) where zero := ⟨fun _ => 0⟩
instance (n : ℕ) : Add (LevelAlg p n) where add u v := ⟨fun a => u a + v a⟩
instance (n : ℕ) : Neg (LevelAlg p n) where neg u := ⟨fun a => -u a⟩
instance (n : ℕ) : Sub (LevelAlg p n) where sub u v := ⟨fun a => u a - v a⟩
instance (n : ℕ) : SMul ℤ_[p] (LevelAlg p n) where smul r u := ⟨fun a => r * u a⟩

/-- Basis element `δ_x` in `LevelAlg p n`. -/
def levelDirac (n : ℕ) (x : ZMod (p ^ n)) : LevelAlg p n :=
  ⟨fun a => if x = a then 1 else 0⟩

instance (n : ℕ) : One (LevelAlg p n) where one := levelDirac n 0
instance (n : ℕ) : Mul (LevelAlg p n) where
  mul u v := ⟨fun c => ∑ a : ZMod (p ^ n), u a * v (c - a)⟩

@[simp] lemma LevelAlg.zero_apply (n : ℕ) (a : ZMod (p ^ n)) : (0 : LevelAlg p n) a = 0 := rfl
@[simp] lemma LevelAlg.add_apply (n : ℕ) (u v : LevelAlg p n) (a : ZMod (p ^ n)) :
    (u + v) a = u a + v a := rfl
@[simp] lemma LevelAlg.neg_apply (n : ℕ) (u : LevelAlg p n) (a : ZMod (p ^ n)) :
    (-u) a = -u a := rfl
@[simp] lemma LevelAlg.sub_apply (n : ℕ) (u v : LevelAlg p n) (a : ZMod (p ^ n)) :
    (u - v) a = u a - v a := rfl
@[simp] lemma LevelAlg.smul_apply (n : ℕ) (r : ℤ_[p]) (u : LevelAlg p n) (a : ZMod (p ^ n)) :
    (r • u) a = r * u a := rfl
@[simp] lemma LevelAlg.mul_apply (n : ℕ) (u v : LevelAlg p n) (c : ZMod (p ^ n)) :
    (u * v) c = ∑ a : ZMod (p ^ n), u a * v (c - a) := rfl
@[simp] lemma levelDirac_apply (n : ℕ) (x a : ZMod (p ^ n)) :
    levelDirac (p := p) n x a = if x = a then 1 else 0 := rfl
@[simp] lemma LevelAlg.one_apply (n : ℕ) (a : ZMod (p ^ n)) :
    (1 : LevelAlg p n) a = if (0 : ZMod (p ^ n)) = a then 1 else 0 := rfl

instance (n : ℕ) : CommRing (LevelAlg p n) where
  add_assoc _ _ _ := by ext a; exact add_assoc _ _ _
  zero_add _ := by ext a; exact zero_add _
  add_zero _ := by ext a; exact add_zero _
  add_comm _ _ := by ext a; exact add_comm _ _
  neg_add_cancel _ := by ext a; exact neg_add_cancel _
  sub_eq_add_neg _ _ := by ext a; exact sub_eq_add_neg _ _
  nsmul := nsmulRec
  zsmul := zsmulRec
  mul_assoc u v w := by
    ext d
    simp only [LevelAlg.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_bij (fun b _ => b - a) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro b₁ _ b₂ _ h; exact sub_left_inj.mp h
    · intro b _; exact ⟨b + a, Finset.mem_univ _, add_sub_cancel_right b a⟩
    · intro b _
      have heq : d - b = d - a - (b - a) := by abel
      rw [mul_assoc, heq]
  one_mul u := by
    ext c
    simp only [LevelAlg.mul_apply, LevelAlg.one_apply]
    rw [Finset.sum_eq_single (0 : ZMod (p ^ n))]
    · simp
    · intro a _ ha; simp [ha.symm]
    · intro h; exact absurd (Finset.mem_univ _) h
  mul_one u := by
    ext c
    simp only [LevelAlg.mul_apply, LevelAlg.one_apply]
    rw [Finset.sum_eq_single c]
    · simp
    · intro a _ ha
      have hne : (0 : ZMod (p ^ n)) ≠ c - a := fun h => ha (sub_eq_zero.mp h.symm).symm
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  mul_comm u v := by
    ext c
    simp only [LevelAlg.mul_apply]
    refine Finset.sum_bij (fun a _ => c - a) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro a₁ _ a₂ _ h; exact sub_right_inj.mp h
    · intro b _; exact ⟨c - b, Finset.mem_univ _, sub_sub_cancel c b⟩
    · intro a _; rw [sub_sub_cancel, mul_comm]
  left_distrib u v w := by
    ext c; simp only [LevelAlg.mul_apply, LevelAlg.add_apply, mul_add, Finset.sum_add_distrib]
  right_distrib u v w := by
    ext c; simp only [LevelAlg.mul_apply, LevelAlg.add_apply, add_mul, Finset.sum_add_distrib]
  zero_mul u := by ext c; simp
  mul_zero u := by ext c; simp

instance (n : ℕ) : Module ℤ_[p] (LevelAlg p n) where
  one_smul _ := by ext a; exact one_mul _
  mul_smul _ _ _ := by ext a; exact mul_assoc _ _ _
  smul_zero _ := by ext a; exact mul_zero _
  smul_add _ _ _ := by ext a; exact mul_add _ _ _
  add_smul _ _ _ := by ext a; exact add_mul _ _ _
  zero_smul _ := by ext a; exact zero_mul _

lemma levelAlg_sum_apply {ι : Type*} (s : Finset ι) (n : ℕ) (f : ι → LevelAlg p n)
    (a : ZMod (p ^ n)) :
    (∑ i ∈ s, f i) a = ∑ i ∈ s, f i a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, LevelAlg.add_apply, ih]

lemma levelAlg_natCast_apply (n : ℕ) (m : ℕ) (a : ZMod (p ^ n)) :
    (m : LevelAlg p n) a = if (0 : ZMod (p ^ n)) = a then (m : ℤ_[p]) else 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.cast_succ, LevelAlg.add_apply, ih, LevelAlg.one_apply, Nat.cast_succ]
    split_ifs <;> simp

lemma levelAlg_intCast_apply (n : ℕ) (z : ℤ) (a : ZMod (p ^ n)) :
    (z : LevelAlg p n) a = if (0 : ZMod (p ^ n)) = a then (z : ℤ_[p]) else 0 := by
  cases z with
  | ofNat m => simpa using levelAlg_natCast_apply (p := p) n m a
  | negSucc m =>
    rw [Int.cast_negSucc, Int.cast_negSucc, LevelAlg.neg_apply, levelAlg_natCast_apply]
    split_ifs <;> simp

lemma levelDirac_mul (n : ℕ) (x y : ZMod (p ^ n)) :
    levelDirac (p := p) n x * levelDirac n y = levelDirac n (x + y) := by
  ext c
  simp only [LevelAlg.mul_apply, levelDirac_apply]
  rw [Finset.sum_eq_single x]
  · simp only [↓reduceIte, one_mul]
    congr 1
    exact propext eq_sub_iff_add_eq'
  · intro a _ ha; simp [ha.symm]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma levelDirac_pow (n : ℕ) (x : ZMod (p ^ n)) (m : ℕ) :
    levelDirac (p := p) n x ^ m = levelDirac n ((m : ZMod (p ^ n)) * x) := by
  induction m with
  | zero => simp; rfl
  | succ m ih =>
    rw [pow_succ, ih, levelDirac_mul, Nat.cast_succ, add_mul, one_mul]

/-- The uniformizer element `t_n = δ_1 - δ_0 ∈ LevelAlg p n`. -/
def levelT (n : ℕ) : LevelAlg p n :=
  levelDirac n 1 - 1

/-- Transition projection `LevelAlg p (n + 1) →+* LevelAlg p n`. -/
def projLevel (n : ℕ) : LevelAlg p (n + 1) →+* LevelAlg p n where
  toFun u := ⟨fun a => ∑ b ∈ Finset.univ.filter (fun b : ZMod (p ^ (n + 1)) =>
      zmodPowStep (p := p) n b = a), u b⟩
  map_one' := by
    ext a
    simp only [LevelAlg.one_apply]
    by_cases h : (0 : ZMod (p ^ n)) = a
    · rw [if_pos h]
      rw [Finset.sum_eq_single (0 : ZMod (p ^ (n + 1)))]
      · simp
      · intro b _ hb; simp [hb.symm]
      · intro hnot; exfalso; apply hnot
        simp [map_zero, h]
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun b hb => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      have hne : (0 : ZMod (p ^ (n + 1))) ≠ b := by
        intro heq; apply h; rw [← hb, ← heq, map_zero]
      simp [hne]
  map_mul' u v := by
    ext c
    dsimp only [LevelAlg.mul_apply]
    rw [Finset.sum_comm]
    have hinner : ∀ a' : ZMod (p ^ (n + 1)),
        ∑ c' ∈ Finset.univ.filter (fun c' : ZMod (p ^ (n + 1)) =>
          zmodPowStep (p := p) n c' = c),
          u a' * v (c' - a') =
        u a' * (∑ b' ∈ Finset.univ.filter (fun b' : ZMod (p ^ (n + 1)) =>
          zmodPowStep (p := p) n b' = c - zmodPowStep (p := p) n a'), v b') := by
      intro a'
      rw [← Finset.mul_sum]
      congr 1
      refine Finset.sum_bij (fun c' _ => c' - a') ?_ ?_ ?_ ?_
      · intro c' hc'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc' ⊢
        rw [map_sub, hc']
      · intro c₁ _ c₂ _ h; exact sub_left_inj.mp h
      · intro b' hb'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb'
        refine ⟨b' + a', ?_, add_sub_cancel_right b' a'⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_add]
        rw [hb', sub_add_cancel]
      · intro _ _; rfl
    rw [Finset.sum_congr rfl (fun a' _ => hinner a')]
    rw [← Finset.sum_fiberwise_of_maps_to (g := zmodPowStep (p := p) n)
      (f := fun a' => u a' * ∑ b' ∈ Finset.univ.filter (fun b' : ZMod (p ^ (n + 1)) =>
        zmodPowStep (p := p) n b' = c - zmodPowStep (p := p) n a'), v b')
      (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a' ha' => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha'
    rw [ha']
  map_zero' := by ext a; simp
  map_add' u v := by ext a; exact Finset.sum_add_distrib

lemma projLevel_dirac (n : ℕ) (x : ZMod (p ^ (n + 1))) :
    projLevel (p := p) n (levelDirac (n + 1) x) = levelDirac n (zmodPowStep (p := p) n x) := by
  ext a
  change (∑ b ∈ Finset.univ.filter (fun b : ZMod (p ^ (n + 1)) => zmodPowStep (p := p) n b = a),
    if x = b then (1 : ℤ_[p]) else 0) = if zmodPowStep (p := p) n x = a then 1 else 0
  by_cases h : zmodPowStep (p := p) n x = a
  · rw [if_pos h]
    rw [Finset.sum_eq_single x]
    · simp
    · intro b _ hb; simp [hb.symm]
    · intro hnot; exfalso; apply hnot; simp [h]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun b hb => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    have hne : x ≠ b := fun heq => h (heq ▸ hb)
    simp [hne]

lemma projLevel_levelT (n : ℕ) : projLevel (p := p) n (levelT (n + 1)) = levelT n := by
  unfold levelT
  rw [map_sub, map_one, projLevel_dirac, map_one]

/-- Every middle binomial coefficient `(p ^ n).choose j` (`0 < j < p ^ n`) is divisible by `p`. -/
lemma prime_dvd_choose_prime_pow {n j : ℕ} (hj0 : 0 < j) (hjn : j < p ^ n) :
    p ∣ (p ^ n).choose j := by
  have hchar : CharP (Polynomial (ZMod p)) p := by
    refine ⟨fun k => ?_⟩
    rw [← Polynomial.C_eq_natCast, ← map_zero Polynomial.C, Polynomial.C_inj]
    exact CharP.cast_eq_zero_iff (ZMod p) p k
  have hpow : (Polynomial.X + 1 : Polynomial (ZMod p)) ^ (p ^ n) = Polynomial.X ^ (p ^ n) + 1 := by
    rw [add_pow_char_pow, one_pow]
  have hcoeff := congrArg (fun f : Polynomial (ZMod p) => f.coeff j) hpow
  rw [add_pow, Polynomial.finsetSum_coeff] at hcoeff
  have hL : (∑ m ∈ Finset.range (p ^ n + 1),
      ((Polynomial.X : Polynomial (ZMod p)) ^ m * 1 ^ (p ^ n - m) *
        (((p ^ n).choose m : ℕ) : Polynomial (ZMod p))).coeff j) =
      ((p ^ n).choose j : ZMod p) := by
    rw [Finset.sum_eq_single j]
    · simp [Polynomial.coeff_X_pow]
    · intro m _ hm
      simp [Polynomial.coeff_X_pow, hm.symm]
    · intro hnot; exfalso; apply hnot; exact Finset.mem_range.mpr (Nat.lt_succ_of_lt hjn)
  have hR : (Polynomial.X ^ (p ^ n) + 1 : Polynomial (ZMod p)).coeff j = 0 := by
    rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_one,
      if_neg (ne_of_lt hjn), if_neg (ne_of_gt hj0), add_zero]
  rw [hL, hR] at hcoeff
  exact (ZMod.natCast_eq_zero_iff _ _).mp hcoeff

/-- **Topological Nilpotency of `t_n = δ_1 - 1` in `LevelAlg p n`**:
every coefficient of `t_n ^ (p ^ n)` has `p`-adic norm `≤ p⁻¹`. -/
theorem norm_levelT_pow_prime_pow (n : ℕ) (a : ZMod (p ^ n)) :
    ‖((levelT (p := p) n) ^ (p ^ n)) a‖ ≤ (p : ℝ) ^ (-(1 : ℤ)) := by
  have hp : p.Prime := Fact.out
  rcases n with _ | n
  · have ht0 : levelT (p := p) 0 = 0 := by
      ext b
      simp only [levelT, LevelAlg.sub_apply, levelDirac_apply, LevelAlg.one_apply, LevelAlg.zero_apply]
      rw [zmod_pow_zero_eq 1 b, zmod_pow_zero_eq 0 b]
      simp
    rw [ht0, pow_zero, pow_one, LevelAlg.zero_apply, norm_zero]
    positivity
  · let N := p ^ (n + 1)
    have hNpos : 0 < N := pow_pos hp.pos _
    have hsub : (levelT (p := p) (n + 1)) ^ N =
        ∑ j ∈ Finset.range (N + 1),
          (((-1 : ℤ) ^ (N - j) * ((N.choose j : ℕ) : ℤ)) : ℤ_[p]) •
            (levelDirac (n + 1) 1 ^ j) := by
      unfold levelT
      rw [sub_eq_add_neg, add_pow]
      refine Finset.sum_congr rfl fun j _ => ?_
      ext b
      have hneg : ((-1 : LevelAlg p (n + 1)) ^ (N - j)) = (((-1 : ℤ) ^ (N - j) : ℤ) : LevelAlg p (n + 1)) := by
        push_cast; rfl
      rw [hneg]
      simp only [LevelAlg.mul_apply, LevelAlg.smul_apply, levelAlg_intCast_apply, levelAlg_natCast_apply]
      rw [Finset.sum_eq_single b]
      · rw [Finset.sum_eq_single b]
        · simp only [sub_self, ↓reduceIte, Int.cast_pow, Int.cast_neg,
            Int.cast_one, Int.cast_natCast]
          ring
        · intro x _ hx
          have hne : (0 : ZMod (p ^ (n + 1))) ≠ b - x := fun h => hx (sub_eq_zero.mp h.symm).symm
          simp [hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro x _ hx
        have hne : (0 : ZMod (p ^ (n + 1))) ≠ b - x := fun h => hx (sub_eq_zero.mp h.symm).symm
        simp [hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    change ‖((levelT (p := p) (n + 1)) ^ N) a‖ ≤ (p : ℝ) ^ (-(1 : ℤ))
    rw [hsub, levelAlg_sum_apply, Finset.sum_range_succ]
    have hdirN : levelDirac (p := p) (n + 1) 1 ^ N = levelDirac (n + 1) 0 := by
      rw [levelDirac_pow, mul_one]
      have hN0 : (N : ZMod (p ^ (n + 1))) = 0 := by simp [N]
      rw [hN0]
    have hdir0 : levelDirac (p := p) (n + 1) 1 ^ 0 = levelDirac (n + 1) 0 := pow_zero _
    simp only [LevelAlg.smul_apply, Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one,
      mul_one, Int.cast_one, one_mul, hdirN]
    have hrange : N - 1 + 1 = N := Nat.sub_add_cancel hNpos
    have hrearr :
        (∑ k ∈ Finset.range (N - 1),
            (((-1 : ℤ) ^ (N - (k + 1)) * ↑(N.choose (k + 1))) : ℤ_[p]) *
              (levelDirac (p := p) (n + 1) 1 ^ (k + 1)) a) +
          (((-1 : ℤ) ^ N : ℤ_[p]) * levelDirac (n + 1) 0 a) +
          levelDirac (n + 1) 0 a =
        (∑ k ∈ Finset.range (N - 1),
            (((-1 : ℤ) ^ (N - (k + 1)) * ↑(N.choose (k + 1))) : ℤ_[p]) *
              (levelDirac (p := p) (n + 1) 1 ^ (k + 1)) a) +
          ((((-1 : ℤ) ^ N + 1 : ℤ) : ℤ_[p]) * levelDirac (n + 1) 0 a) := by
      push_cast; ring
    have hp_le0 : (0 : ℝ) ≤ (p : ℝ) ^ (-(1 : ℤ)) := by positivity
    have hbd_end : ‖((((-1 : ℤ) ^ N + 1 : ℤ) : ℤ_[p]) * levelDirac (n + 1) 0 a)‖ ≤
        (p : ℝ) ^ (-(1 : ℤ)) := by
      have hdvd : (p : ℤ) ∣ ((-1 : ℤ) ^ N + 1) := by
        rcases hp.eq_two_or_odd with rfl | hodd
        · have heven : Even (2 ^ (n + 1)) := Even.pow_of_ne_zero even_two (Nat.succ_ne_zero n)
          rw [Even.neg_one_pow heven]
          norm_num
        · have hNodd : Odd N := Odd.pow (Nat.odd_iff.mpr hodd)
          rw [Odd.neg_one_pow hNodd]
          norm_num
      obtain ⟨q, hq⟩ := hdvd
      rw [hq, Int.cast_mul, Int.cast_natCast, mul_assoc, norm_mul]
      have hnp : ‖(p : ℤ_[p])‖ = (p : ℝ) ^ (-(1 : ℤ)) := by
        change ‖(p : ℚ_[p])‖ = _
        rw [Padic.norm_p, zpow_neg_one]
      rw [hnp]
      calc (p : ℝ) ^ (-(1 : ℤ)) * ‖(q : ℤ_[p]) * levelDirac (n + 1) 0 a‖
          ≤ (p : ℝ) ^ (-(1 : ℤ)) * 1 :=
            mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) hp_le0
        _ = (p : ℝ) ^ (-(1 : ℤ)) := mul_one _
    have hbd_mid : ∀ k ∈ Finset.range (N - 1),
        ‖(((-1 : ℤ) ^ (N - (k + 1)) * ↑(N.choose (k + 1))) : ℤ_[p]) *
          (levelDirac (p := p) (n + 1) 1 ^ (k + 1)) a‖ ≤ (p : ℝ) ^ (-(1 : ℤ)) := by
      intro k hk
      have hklt : k + 1 < N := by have := Finset.mem_range.mp hk; omega
      obtain ⟨q, hq⟩ := prime_dvd_choose_prime_pow (p := p) (n := n + 1) (Nat.succ_pos k) hklt
      have hq' : (N.choose (k + 1) : ℤ_[p]) = (p : ℤ_[p]) * (q : ℤ_[p]) := by
        exact_mod_cast hq
      have hfac : (((-1 : ℤ) ^ (N - (k + 1)) * ↑(N.choose (k + 1))) : ℤ_[p]) *
          (levelDirac (p := p) (n + 1) 1 ^ (k + 1)) a =
          (p : ℤ_[p]) * (((-1 : ℤ) ^ (N - (k + 1)) : ℤ_[p]) * (q : ℤ_[p]) *
            (levelDirac (p := p) (n + 1) 1 ^ (k + 1)) a) := by
        push_cast; rw [hq']; ring
      rw [hfac, norm_mul]
      have hnp : ‖(p : ℤ_[p])‖ = (p : ℝ) ^ (-(1 : ℤ)) := by
        change ‖(p : ℚ_[p])‖ = _
        rw [Padic.norm_p, zpow_neg_one]
      rw [hnp]
      calc (p : ℝ) ^ (-(1 : ℤ)) * ‖_‖
          ≤ (p : ℝ) ^ (-(1 : ℤ)) * 1 :=
            mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) hp_le0
        _ = (p : ℝ) ^ (-(1 : ℤ)) := mul_one _
    have hgoal_eq :
        (∑ x ∈ Finset.range N,
          (((-1 : ℤ) ^ (N - x) * ((N.choose x : ℕ) : ℤ)) : ℤ_[p]) *
            (levelDirac (p := p) (n + 1) 1 ^ x) a) =
        (∑ k ∈ Finset.range (N - 1),
            (((-1 : ℤ) ^ (N - (k + 1)) * ((N.choose (k + 1) : ℕ) : ℤ)) : ℤ_[p]) *
              (levelDirac (p := p) (n + 1) 1 ^ (k + 1)) a) +
          (((-1 : ℤ) ^ N : ℤ_[p]) * levelDirac (n + 1) 0 a) := by
      conv_lhs => rw [← hrange]
      rw [Finset.sum_range_succ', hrange]
      simp
    rw [hgoal_eq]
    have hrearr' :
        (∑ k ∈ Finset.range (N - 1),
            (((-1 : ℤ) ^ (N - (k + 1)) * ((N.choose (k + 1) : ℕ) : ℤ)) : ℤ_[p]) *
              (levelDirac (p := p) (n + 1) 1 ^ (k + 1)) a) +
          (((-1 : ℤ) ^ N : ℤ_[p]) * levelDirac (n + 1) 0 a) +
          levelDirac (n + 1) 0 a =
        (∑ k ∈ Finset.range (N - 1),
            (((-1 : ℤ) ^ (N - (k + 1)) * ↑(N.choose (k + 1))) : ℤ_[p]) *
              (levelDirac (p := p) (n + 1) 1 ^ (k + 1)) a) +
          ((((-1 : ℤ) ^ N + 1 : ℤ) : ℤ_[p]) * levelDirac (n + 1) 0 a) := by
      rw [← hrearr]
      exact congrArg (fun s => s + (((-1 : ℤ) ^ N : ℤ_[p]) * levelDirac (n + 1) 0 a) +
        levelDirac (n + 1) 0 a) (Finset.sum_congr rfl fun k _ => by rw [Int.cast_natCast])
    rw [hrearr']
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hbd_end)
    exact padicInt_norm_sum_le _ _ hp_le0 hbd_mid

/-- Submultiplicativity of the sup-norm on `LevelAlg p n`. -/
lemma norm_levelAlg_mul_le {n : ℕ} {u v : LevelAlg p n} {B₁ B₂ : ℝ} (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hu : ∀ a, ‖u a‖ ≤ B₁) (hv : ∀ a, ‖v a‖ ≤ B₂) (c : ZMod (p ^ n)) :
    ‖(u * v) c‖ ≤ B₁ * B₂ := by
  refine padicInt_norm_sum_le _ _ (mul_nonneg hB₁ hB₂) fun a _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hu a) (hv (c - a)) (norm_nonneg _) hB₁

/-- General nilpotency bound: for `m * p ^ n ≤ k`, `‖(t_n ^ k) a‖ ≤ p ^ (-m)`. -/
theorem norm_levelT_pow_le (n m k : ℕ) (hk : m * p ^ n ≤ k) (a : ZMod (p ^ n)) :
    ‖((levelT (p := p) n) ^ k) a‖ ≤ (p : ℝ) ^ (-(m : ℤ)) := by
  have hmul : ∀ r : ℕ, ∀ b : ZMod (p ^ n),
      ‖((levelT (p := p) n) ^ (r * p ^ n)) b‖ ≤ (p : ℝ) ^ (-(r : ℤ)) := by
    intro r
    induction r with
    | zero =>
      intro b
      simp only [zero_mul, pow_zero, CharP.cast_eq_zero, neg_zero, zpow_zero]
      exact PadicInt.norm_le_one _
    | succ r ih =>
      intro b
      rw [Nat.succ_mul, pow_add]
      have hbd := norm_levelAlg_mul_le (B₁ := (p : ℝ) ^ (-(r : ℤ))) (B₂ := (p : ℝ) ^ (-(1 : ℤ)))
        (by positivity) (by positivity) ih (norm_levelT_pow_prime_pow n) b
      refine hbd.trans_eq ?_
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
      rw [← zpow_add₀ hp0]
      congr 1
      omega
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add]
  have hbd := norm_levelAlg_mul_le (u := (levelT (p := p) n) ^ (m * p ^ n))
    (v := (levelT (p := p) n) ^ d) (B₁ := (p : ℝ) ^ (-(m : ℤ))) (B₂ := 1)
    (by positivity) zero_le_one (hmul m) (fun b => PadicInt.norm_le_one (((levelT (p := p) n) ^ d) b)) a
  rwa [mul_one] at hbd

/-- Summability of the power-series evaluation at `t_n` in `LevelAlg p n`. -/
lemma summable_evalLevel_term (n : ℕ) (F : IwasawaAlg p) (a : ZMod (p ^ n)) :
    Summable (fun k : ℕ => PowerSeries.coeff k F * ((levelT (p := p) n) ^ k) a) := by
  have hp : p.Prime := Fact.out
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hN_pos : 0 < p ^ n := pow_pos hp.pos n
  have hq_pos : (0 : ℝ) < ((p : ℝ) ^ (-(1 : ℤ))) ^ ((1 : ℝ) / (p ^ n : ℝ)) := by positivity
  -- Direct geometric bound: `(p⁻¹)^(k / p^n) ≤ p * (p^(-1 / p^n))^k`
  set r : ℝ := (p : ℝ) ^ (-(1 : ℝ) / (p ^ n : ℝ))
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    refine Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) ?_
    exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  have hnorm : Summable (fun k : ℕ => ‖PowerSeries.coeff k F * ((levelT (p := p) n) ^ k) a‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
      ((summable_geometric_of_lt_one hr0 hr1).mul_left (p : ℝ))
    rw [norm_mul]
    have hdiv : (k / p ^ n) * p ^ n ≤ k := Nat.div_mul_le_self k (p ^ n)
    have hbd1 : ‖((levelT (p := p) n) ^ k) a‖ ≤ (p : ℝ) ^ (-((k / p ^ n : ℕ) : ℤ)) :=
      norm_levelT_pow_le n (k / p ^ n) k hdiv a
    have hbd2 : ‖PowerSeries.coeff k F‖ * ‖((levelT (p := p) n) ^ k) a‖ ≤
        (p : ℝ) ^ (-((k / p ^ n : ℕ) : ℤ)) := by
      calc ‖PowerSeries.coeff k F‖ * ‖((levelT (p := p) n) ^ k) a‖
          ≤ 1 * (p : ℝ) ^ (-((k / p ^ n : ℕ) : ℤ)) :=
            mul_le_mul (PadicInt.norm_le_one _) hbd1 (norm_nonneg _) zero_le_one
        _ = (p : ℝ) ^ (-((k / p ^ n : ℕ) : ℤ)) := one_mul _
    refine hbd2.trans ?_
    have hexp_nat : k < (k / p ^ n + 1) * p ^ n := by
      have hmod : k % p ^ n < p ^ n := Nat.mod_lt k hN_pos
      have hdiv_eq : p ^ n * (k / p ^ n) + k % p ^ n = k := Nat.div_add_mod k (p ^ n)
      nlinarith
    have hexp : (k : ℝ) / (p ^ n : ℝ) - 1 ≤ ((k / p ^ n : ℕ) : ℝ) := by
      have hR : (k : ℝ) < (((k / p ^ n : ℕ) : ℝ) + 1) * (p ^ n : ℝ) := by exact_mod_cast hexp_nat
      have hNpR : (0 : ℝ) < (p ^ n : ℝ) := by exact_mod_cast hN_pos
      rw [sub_le_iff_le_add, div_le_iff₀ hNpR]
      exact hR.le
    have hr_pow : (p : ℝ) * r ^ k = (p : ℝ) ^ (1 - (k : ℝ) / (p ^ n : ℝ)) := by
      dsimp only [r]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hp_pos.le]
      conv_lhs => arg 1; rw [← Real.rpow_one (p : ℝ)]
      rw [← Real.rpow_add hp_pos]
      congr 1
      ring
    rw [hr_pow, ← Real.rpow_intCast]
    refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_le) ?_
    rw [Int.cast_neg, Int.cast_natCast]
    linarith
  exact hnorm.of_norm

/-- Level-`n` evaluation `IwasawaAlg p → LevelAlg p n`: `F ↦ ∑' k, coeff k F • t_n^k`. -/
def evalLevel (n : ℕ) (F : IwasawaAlg p) : LevelAlg p n :=
  ⟨fun a => ∑' k : ℕ, PowerSeries.coeff k F * ((levelT (p := p) n) ^ k) a⟩

lemma evalLevel_apply (n : ℕ) (F : IwasawaAlg p) (a : ZMod (p ^ n)) :
    evalLevel n F a = ∑' k : ℕ, PowerSeries.coeff k F * ((levelT (p := p) n) ^ k) a := rfl

/-- Mod-`p ^ m` finite-sum truncation of `evalLevel n F`: terms with `k ≥ m * p ^ n` have norm `≤ p ^ (-m)`. -/
theorem norm_evalLevel_sub_trunc_le (n m K : ℕ) (hK : m * p ^ n ≤ K) (F : IwasawaAlg p)
    (a : ZMod (p ^ n)) :
    ‖evalLevel n F a - ∑ k ∈ Finset.range K, PowerSeries.coeff k F * ((levelT (p := p) n) ^ k) a‖ ≤
      (p : ℝ) ^ (-(m : ℤ)) := by
  have hs := summable_evalLevel_term (p := p) n F a
  have hsplit : evalLevel n F a -
      ∑ k ∈ Finset.range K, PowerSeries.coeff k F * ((levelT (p := p) n) ^ k) a =
      ∑' k : ℕ, PowerSeries.coeff (k + K) F * ((levelT (p := p) n) ^ (k + K)) a := by
    rw [evalLevel_apply, ← hs.sum_add_tsum_nat_add K]
    ring
  rw [hsplit]
  have hs' : Summable (fun k : ℕ =>
      PowerSeries.coeff (k + K) F * ((levelT (p := p) n) ^ (k + K)) a) :=
    (summable_nat_add_iff K).mpr hs
  have hlim : Tendsto (fun N => ‖∑ k ∈ Finset.range N,
      PowerSeries.coeff (k + K) F * ((levelT (p := p) n) ^ (k + K)) a‖) atTop
      (nhds ‖∑' k : ℕ, PowerSeries.coeff (k + K) F * ((levelT (p := p) n) ^ (k + K)) a‖) :=
    hs'.hasSum.tendsto_sum_nat.norm
  refine le_of_tendsto' hlim fun N => ?_
  refine padicInt_norm_sum_le _ _ (by positivity) fun k _ => ?_
  rw [norm_mul]
  calc ‖PowerSeries.coeff (k + K) F‖ * ‖((levelT (p := p) n) ^ (k + K)) a‖
      ≤ 1 * (p : ℝ) ^ (-(m : ℤ)) :=
        mul_le_mul (PadicInt.norm_le_one _)
          (norm_levelT_pow_le n m (k + K) (by omega) a) (norm_nonneg _) zero_le_one
    _ = (p : ℝ) ^ (-(m : ℤ)) := one_mul _

lemma evalLevel_add (n : ℕ) (F G : IwasawaAlg p) :
    evalLevel n (F + G) = evalLevel n F + evalLevel n G := by
  ext a
  simp only [evalLevel_apply, LevelAlg.add_apply, map_add, add_mul]
  exact (summable_evalLevel_term n F a).tsum_add (summable_evalLevel_term n G a)

lemma evalLevel_sub (n : ℕ) (F G : IwasawaAlg p) :
    evalLevel n (F - G) = evalLevel n F - evalLevel n G := by
  ext a
  simp only [evalLevel_apply, LevelAlg.sub_apply, map_sub, sub_mul]
  exact (summable_evalLevel_term n F a).tsum_sub (summable_evalLevel_term n G a)

lemma evalLevel_smul (n : ℕ) (c : ℤ_[p]) (F : IwasawaAlg p) :
    evalLevel n (PowerSeries.C c * F) = c • evalLevel n F := by
  ext a
  simp only [evalLevel_apply, LevelAlg.smul_apply, PowerSeries.coeff_C_mul, mul_assoc]
  exact (summable_evalLevel_term n F a).tsum_mul_left c

lemma evalLevel_C_mul_X_pow (n : ℕ) (c : ℤ_[p]) (k : ℕ) :
    evalLevel n (PowerSeries.C c * PowerSeries.X ^ k) = c • (levelT n ^ k) := by
  ext a
  simp only [evalLevel_apply, LevelAlg.smul_apply, PowerSeries.coeff_C_mul_X_pow]
  rw [tsum_eq_single k]
  · simp
  · intro j hj; simp [hj]

lemma evalLevel_one (n : ℕ) : evalLevel (p := p) n 1 = 1 := by
  have h := evalLevel_C_mul_X_pow (p := p) n 1 0
  simpa using h

lemma evalLevel_X (n : ℕ) : evalLevel (p := p) n PowerSeries.X = levelT n := by
  have h := evalLevel_C_mul_X_pow (p := p) n 1 1
  simpa using h

lemma evalLevel_one_add_X_pow (n m : ℕ) :
    evalLevel (p := p) n ((1 + PowerSeries.X) ^ m) = levelDirac n (m : ZMod (p ^ n)) := by
  have hsum : (1 + PowerSeries.X : IwasawaAlg p) ^ m =
      ∑ k ∈ Finset.range (m + 1), PowerSeries.C (m.choose k : ℤ_[p]) * PowerSeries.X ^ k := by
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [one_pow, mul_one, mul_comm, map_natCast]
  rw [hsum]
  have hlin : ∀ s : Finset ℕ, evalLevel (p := p) n
      (∑ k ∈ s, PowerSeries.C (m.choose k : ℤ_[p]) * PowerSeries.X ^ k) =
      ∑ k ∈ s, (m.choose k : ℤ_[p]) • (levelT (p := p) n ^ k) := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty => ext a; simp [evalLevel_apply]
    | insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx, evalLevel_add, evalLevel_C_mul_X_pow, ih]
  rw [hlin]
  have hbin : (1 + levelT (p := p) n) ^ m =
      ∑ k ∈ Finset.range (m + 1), (m.choose k : ℤ_[p]) • (levelT (p := p) n ^ k) := by
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [one_pow, mul_one]
    ext a
    simp only [LevelAlg.mul_apply, LevelAlg.smul_apply, levelAlg_natCast_apply]
    rw [Finset.sum_eq_single a]
    · simp [mul_comm]
    · intro b _ hb
      have hne : (0 : ZMod (p ^ n)) ≠ a - b := fun h => hb (sub_eq_zero.mp h.symm).symm
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [← hbin]
  have h1t : 1 + levelT (p := p) n = levelDirac n 1 := by unfold levelT; abel
  rw [h1t, levelDirac_pow, mul_one]

/-- Compatibility across levels: `projLevel n (evalLevel (n + 1) F) = evalLevel n F`. -/
theorem projLevel_evalLevel (n : ℕ) (F : IwasawaAlg p) :
    projLevel (p := p) n (evalLevel (n + 1) F) = evalLevel n F := by
  ext a
  change (∑ b ∈ Finset.univ.filter (fun b : ZMod (p ^ (n + 1)) => zmodPowStep (p := p) n b = a),
      ∑' k : ℕ, PowerSeries.coeff k F * ((levelT (p := p) (n + 1)) ^ k) b) =
    ∑' k : ℕ, PowerSeries.coeff k F * ((levelT (p := p) n) ^ k) a
  rw [← Summable.tsum_finsetSum (fun b _ => summable_evalLevel_term (n + 1) F b)]
  refine tsum_congr fun k => ?_
  rw [← Finset.mul_sum]
  congr 1
  have hproj := congrArg (fun u : LevelAlg p n => u a)
    ((map_pow (projLevel (p := p) n) (levelT (n + 1)) k).trans (by rw [projLevel_levelT]))
  exact hproj

/-- **Inverse Amice–Mahler–Iwasawa Map** `IwasawaAlg p → PadicMeasure p`:
reconstructs the measure `μ` from its power series `F ∈ ℤ_[p][[T]]`. -/
def iwasawaInv (F : IwasawaAlg p) : PadicMeasure p where
  toFun n a := evalLevel n F a
  compat n a := by
    have h := congrArg (fun u : LevelAlg p n => u a) (projLevel_evalLevel (p := p) n F)
    exact h.symm

lemma iwasawaInv_apply (F : IwasawaAlg p) (n : ℕ) (a : ZMod (p ^ n)) :
    iwasawaInv F n a = evalLevel n F a := rfl

lemma iwasawaInv_add (F G : IwasawaAlg p) : iwasawaInv (F + G) = iwasawaInv F + iwasawaInv G := by
  ext n a
  exact congrArg (fun u : LevelAlg p n => u a) (evalLevel_add n F G)

lemma iwasawaInv_sub (F G : IwasawaAlg p) : iwasawaInv (F - G) = iwasawaInv F - iwasawaInv G := by
  ext n a
  exact congrArg (fun u : LevelAlg p n => u a) (evalLevel_sub n F G)

lemma iwasawaInv_C_mul_X_pow (c : ℤ_[p]) (k : ℕ) :
    iwasawaInv (PowerSeries.C c * PowerSeries.X ^ k) =
      c • ((diracMeasure (p := p) 1 - 1) ^ k) := by
  have h1 : ∀ j : ℕ, ∀ n : ℕ, ∀ a : ZMod (p ^ n),
      ((diracMeasure (p := p) 1 - 1) ^ j) n a = (levelT (p := p) n ^ j) a := by
    intro j
    induction j with
    | zero => intro n a; simp [PadicMeasure.one_apply, LevelAlg.one_apply]
    | succ j ih =>
      intro n a
      rw [pow_succ, pow_succ, PadicMeasure.mul_apply, LevelAlg.mul_apply]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [ih n b]
      congr 1
      simp only [PadicMeasure.sub_apply, diracMeasure_apply, PadicMeasure.one_apply,
        levelT, LevelAlg.sub_apply, levelDirac_apply, LevelAlg.one_apply, map_one]
  ext n a
  rw [iwasawaInv_apply, evalLevel_C_mul_X_pow, LevelAlg.smul_apply, PadicMeasure.smul_apply, h1]

/-- **Left Inverse Theorem**: `iwasawaInv (iwasawaTransform μ) = μ` for EVERY `μ : PadicMeasure p`! -/
theorem iwasawaInv_iwasawaTransform (μ : PadicMeasure p) :
    iwasawaInv (iwasawaTransform μ) = μ := by
  ext n a
  refine padicInt_eq_of_forall_norm_le_pow fun m => ?_
  have hp_pos : (0 : ℝ) < (p : ℝ) ^ (-(m : ℤ)) :=
    zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  set K := m * p ^ n
  have htrunc : ‖evalLevel n (iwasawaTransform μ) a -
      ∑ k ∈ Finset.range K,
        measureIntegral μ (mahlerBinom k) * ((levelT (p := p) n) ^ k) a‖ ≤
      (p : ℝ) ^ (-(m : ℤ)) := by
    simpa [coeff_iwasawaTransform] using
      norm_evalLevel_sub_trunc_le n m K le_rfl (iwasawaTransform μ) a
  -- Choose N ≥ n large enough so all mahlerBinom k (k < K) are within p^(-m) of level-N Riemann sums
  have hmod_all : ∀ k : ℕ, ∃ Nk : ℕ, ∀ x y : ℤ_[p],
      PadicInt.toZModPow Nk x = PadicInt.toZModPow Nk y →
      ‖mahlerBinom (p := p) k x - mahlerBinom (p := p) k y‖ ≤ (p : ℝ) ^ (-(m : ℤ)) :=
    fun k => exists_level_of_continuous (continuous_mahlerBinom k) ((p : ℝ) ^ (-(m : ℤ))) hp_pos
  choose Nk hNk using hmod_all
  set N := max n ((Finset.range K).sup Nk)
  have hnN : n ≤ N := le_max_left _ _
  have hriem_bd : ∀ k ∈ Finset.range K,
      ‖measureIntegral μ (mahlerBinom k) - riemannSum μ (mahlerBinom k) N‖ ≤
        (p : ℝ) ^ (-(m : ℤ)) := by
    intro k hk
    have hNkN : Nk k ≤ N := (Finset.le_sup hk).trans (le_max_right _ _)
    refine norm_measureIntegral_sub_riemannSum_le μ (continuous_mahlerBinom k) N hp_pos.le ?_
    intro x y hxy
    exact hNk k x y (by rw [← zmodPowCast_toZModPow hNkN x, ← zmodPowCast_toZModPow hNkN y, hxy])
  have hstep2 : ‖(∑ k ∈ Finset.range K,
      measureIntegral μ (mahlerBinom k) * ((levelT (p := p) n) ^ k) a) -
      (∑ k ∈ Finset.range K,
        riemannSum μ (mahlerBinom k) N * ((levelT (p := p) n) ^ k) a)‖ ≤
      (p : ℝ) ^ (-(m : ℤ)) := by
    rw [← Finset.sum_sub_distrib]
    refine padicInt_norm_sum_le _ _ hp_pos.le fun k hk => ?_
    rw [← sub_mul, norm_mul]
    calc ‖measureIntegral μ (mahlerBinom k) - riemannSum μ (mahlerBinom k) N‖ *
          ‖((levelT (p := p) n) ^ k) a‖
        ≤ (p : ℝ) ^ (-(m : ℤ)) * 1 :=
          mul_le_mul (hriem_bd k hk) (PadicInt.norm_le_one _) (norm_nonneg _) hp_pos.le
      _ = (p : ℝ) ^ (-(m : ℤ)) := mul_one _
  -- Rewrite the Riemann-sum expression and compare with μ n a via binomial theorem `(1 + t_n)^b.val = δ_b`
  have hswap : ∑ k ∈ Finset.range K,
      riemannSum μ (mahlerBinom k) N * ((levelT (p := p) n) ^ k) a =
      ∑ b : ZMod (p ^ N), μ N b *
        (∑ k ∈ Finset.range K, (b.val.choose k : ℤ_[p]) * ((levelT (p := p) n) ^ k) a) := by
    unfold riemannSum
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mahlerBinom_natCast]
    ring
  have hmu_eq : μ n a = ∑ b : ZMod (p ^ N), μ N b *
      (levelDirac (p := p) n (zmodPowCast (p := p) hnN b) a) := by
    rw [μ.compat_le hnN a]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun b : ZMod (p ^ N) => zmodPowCast (p := p) hnN b = a)]
    have h1 : ∑ b ∈ Finset.univ.filter (fun b : ZMod (p ^ N) => zmodPowCast (p := p) hnN b = a),
        μ N b * levelDirac (p := p) n (zmodPowCast (p := p) hnN b) a =
        ∑ b ∈ Finset.univ.filter (fun b : ZMod (p ^ N) => zmodPowCast (p := p) hnN b = a),
          μ N b := by
      refine Finset.sum_congr rfl fun b hb => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      simp [levelDirac, hb]
    have h2 : ∑ b ∈ Finset.univ.filter (fun b : ZMod (p ^ N) => ¬ zmodPowCast (p := p) hnN b = a),
        μ N b * levelDirac (p := p) n (zmodPowCast (p := p) hnN b) a = 0 := by
      refine Finset.sum_eq_zero fun b hb => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      simp [levelDirac, hb]
    rw [h1, h2, add_zero]
  have hstep3 : ‖(∑ k ∈ Finset.range K,
      riemannSum μ (mahlerBinom k) N * ((levelT (p := p) n) ^ k) a) - μ n a‖ ≤
      (p : ℝ) ^ (-(m : ℤ)) := by
    rw [hswap, hmu_eq, ← Finset.sum_sub_distrib]
    refine padicInt_norm_sum_le _ _ hp_pos.le fun b _ => ?_
    rw [← mul_sub, norm_mul]
    have hdir_eq : levelDirac (p := p) n (zmodPowCast (p := p) hnN b) a =
        ∑ k ∈ Finset.range (b.val + 1),
          (b.val.choose k : ℤ_[p]) * ((levelT (p := p) n) ^ k) a := by
      have hcast : (b.val : ZMod (p ^ n)) = zmodPowCast (p := p) hnN b := by
        have : NeZero (p ^ N) := ⟨pow_ne_zero N (Fact.out : p.Prime).ne_zero⟩
        rw [zmodPowCast, ← map_natCast (ZMod.castHom (pow_dvd_pow p hnN) (ZMod (p ^ n))),
          ZMod.natCast_zmod_val]
      have hbin : levelDirac (p := p) n (b.val : ZMod (p ^ n)) =
          ∑ k ∈ Finset.range (b.val + 1), (b.val.choose k : ℤ_[p]) • (levelT (p := p) n ^ k) := by
        have h1 : (1 + levelT (p := p) n) ^ b.val =
            ∑ k ∈ Finset.range (b.val + 1), (b.val.choose k : ℤ_[p]) • (levelT (p := p) n ^ k) := by
          rw [add_comm, add_pow]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [one_pow, mul_one]
          ext c
          simp only [LevelAlg.mul_apply, LevelAlg.smul_apply, levelAlg_natCast_apply]
          rw [Finset.sum_eq_single c]
          · simp [mul_comm]
          · intro x _ hx
            have hne : (0 : ZMod (p ^ n)) ≠ c - x := fun h => hx (sub_eq_zero.mp h.symm).symm
            simp [hne]
          · intro h; exact absurd (Finset.mem_univ _) h
        have h2 : 1 + levelT (p := p) n = levelDirac n 1 := by unfold levelT; abel
        rw [h2, levelDirac_pow, mul_one] at h1
        exact h1
      rw [← hcast, hbin, levelAlg_sum_apply]
      rfl
    rw [hdir_eq]
    have hdiff_bd : ‖(∑ k ∈ Finset.range K, (b.val.choose k : ℤ_[p]) * ((levelT (p := p) n) ^ k) a) -
        (∑ k ∈ Finset.range (b.val + 1), (b.val.choose k : ℤ_[p]) * ((levelT (p := p) n) ^ k) a)‖ ≤
        (p : ℝ) ^ (-(m : ℤ)) := by
      rcases le_or_gt K (b.val + 1) with hle | hgt
      · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
        rw [hd, Finset.sum_range_add, sub_add_eq_sub_sub, sub_self, zero_sub, norm_neg]
        refine padicInt_norm_sum_le _ _ hp_pos.le fun j _ => ?_
        rw [norm_mul]
        calc ‖(b.val.choose (K + j) : ℤ_[p])‖ * ‖((levelT (p := p) n) ^ (K + j)) a‖
            ≤ 1 * (p : ℝ) ^ (-(m : ℤ)) :=
              mul_le_mul (PadicInt.norm_le_one _)
                (norm_levelT_pow_le n m (K + j) (by omega) a) (norm_nonneg _) zero_le_one
          _ = (p : ℝ) ^ (-(m : ℤ)) := one_mul _
      · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hgt.le
        rw [hd, Finset.sum_range_add, add_sub_cancel_left]
        have hzero : ∑ j ∈ Finset.range d,
            (b.val.choose (b.val + 1 + j) : ℤ_[p]) * ((levelT (p := p) n) ^ (b.val + 1 + j)) a = 0 := by
          refine Finset.sum_eq_zero fun j _ => ?_
          rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
        rw [hzero, norm_zero]
        exact hp_pos.le
    calc ‖μ N b‖ * ‖_‖
        ≤ 1 * (p : ℝ) ^ (-(m : ℤ)) :=
          mul_le_mul (PadicInt.norm_le_one _) hdiff_bd (norm_nonneg _) zero_le_one
      _ = (p : ℝ) ^ (-(m : ℤ)) := one_mul _
  have htri : iwasawaInv (iwasawaTransform μ) n a - μ n a =
      (evalLevel n (iwasawaTransform μ) a -
        ∑ k ∈ Finset.range K, measureIntegral μ (mahlerBinom k) * ((levelT (p := p) n) ^ k) a) +
      ((∑ k ∈ Finset.range K, measureIntegral μ (mahlerBinom k) * ((levelT (p := p) n) ^ k) a) -
        (∑ k ∈ Finset.range K, riemannSum μ (mahlerBinom k) N * ((levelT (p := p) n) ^ k) a)) +
      ((∑ k ∈ Finset.range K, riemannSum μ (mahlerBinom k) N * ((levelT (p := p) n) ^ k) a) -
        μ n a) := by
    rw [iwasawaInv_apply]; ring
  rw [htri]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hstep3)
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le htrunc hstep2)

/-- **Right Inverse Theorem**: `iwasawaTransform (iwasawaInv F) = F` for EVERY `F : IwasawaAlg p`! -/
theorem iwasawaTransform_iwasawaInv (F : IwasawaAlg p) :
    iwasawaTransform (iwasawaInv F) = F := by
  ext j
  rw [coeff_iwasawaTransform]
  refine padicInt_eq_of_forall_norm_le_pow fun m => ?_
  have hp_pos : (0 : ℝ) < (p : ℝ) ^ (-(m : ℤ)) :=
    zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  obtain ⟨n, hn⟩ := exists_level_of_continuous (continuous_mahlerBinom (p := p) j)
    ((p : ℝ) ^ (-(m : ℤ))) hp_pos
  set K := max (j + 1) (m * p ^ n)
  let P : IwasawaAlg p := ∑ k ∈ Finset.range K, PowerSeries.C (PowerSeries.coeff k F) * PowerSeries.X ^ k
  let R : IwasawaAlg p := F - P
  have hcoeffP : ∀ k : ℕ, PowerSeries.coeff k P = if k < K then PowerSeries.coeff k F else 0 := by
    intro k
    dsimp only [P]
    rw [map_sum]
    simp_rw [PowerSeries.coeff_C_mul_X_pow]
    by_cases hk : k < K
    · rw [if_pos hk, Finset.sum_eq_single k]
      · simp
      · intro i _ hi; simp [hi.symm]
      · intro hnot; exact absurd (Finset.mem_range.mpr hk) hnot
    · rw [if_neg hk]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hik : i ≠ k := ne_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hi) (not_lt.mp hk))
      simp [hik.symm]
  have hP_inv : iwasawaTransform (iwasawaInv P) = P := by
    dsimp only [P]
    have haux : ∀ s : Finset ℕ,
        iwasawaTransform (iwasawaInv (∑ k ∈ s, PowerSeries.C (PowerSeries.coeff k F) * PowerSeries.X ^ k)) =
          ∑ k ∈ s, PowerSeries.C (PowerSeries.coeff k F) * PowerSeries.X ^ k := by
      intro s
      classical
      induction s using Finset.induction_on with
      | empty =>
        rw [Finset.sum_empty]
        have h0 : iwasawaInv (0 : IwasawaAlg p) = 0 := by ext r a; simp [iwasawaInv, evalLevel]
        rw [h0, iwasawaTransform_zero]
      | insert k s hk ih =>
        rw [Finset.sum_insert hk, iwasawaInv_add, iwasawaTransform_add, ih]
        congr 1
        rw [iwasawaInv_C_mul_X_pow, iwasawaTransform_smul]
        congr 1
        change iwasawaTransformRingHom ((diracMeasure (p := p) 1 - 1) ^ k) = PowerSeries.X ^ k
        rw [map_pow, map_sub, map_one]
        change (iwasawaTransform (diracMeasure (p := p) 1) - 1) ^ k = PowerSeries.X ^ k
        rw [iwasawaTransform_dirac_one, add_sub_cancel_left]
    exact haux (Finset.range K)
  have hjK : j < K := lt_of_lt_of_le (Nat.lt_succ_self j) (le_max_left _ _)
  have hP_int : measureIntegral (iwasawaInv P) (mahlerBinom j) = PowerSeries.coeff j F := by
    have := congrArg (PowerSeries.coeff j) hP_inv
    rw [coeff_iwasawaTransform, hcoeffP j, if_pos hjK] at this
    exact this
  have hF_split : F = P + R := by dsimp only [R]; ring
  have hF_int : measureIntegral (iwasawaInv F) (mahlerBinom j) =
      measureIntegral (iwasawaInv P) (mahlerBinom j) +
      measureIntegral (iwasawaInv R) (mahlerBinom j) := by
    conv_lhs => rw [hF_split]
    rw [iwasawaInv_add, measureIntegral_add_measure _ _ (continuous_mahlerBinom j)]
  have hdiff_eq : measureIntegral (iwasawaInv F) (mahlerBinom j) - PowerSeries.coeff j F =
      measureIntegral (iwasawaInv R) (mahlerBinom j) := by
    rw [hF_int, hP_int]
    ring
  rw [hdiff_eq]
  have hR_coeff : ∀ k < K, PowerSeries.coeff k R = 0 := by
    intro k hk
    dsimp only [R]
    rw [map_sub, hcoeffP k, if_pos hk, sub_self]
  have hR_eval : ∀ a : ZMod (p ^ n), ‖iwasawaInv R n a‖ ≤ (p : ℝ) ^ (-(m : ℤ)) := by
    intro a
    rw [iwasawaInv_apply]
    have htrunc := norm_evalLevel_sub_trunc_le n m K (le_max_right _ _) R a
    have hzero : ∑ k ∈ Finset.range K, PowerSeries.coeff k R * ((levelT (p := p) n) ^ k) a = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [hR_coeff k (Finset.mem_range.mp hk), zero_mul]
    rwa [hzero, sub_zero] at htrunc
  have hriem_R : ‖riemannSum (iwasawaInv R) (mahlerBinom j) n‖ ≤ (p : ℝ) ^ (-(m : ℤ)) := by
    refine padicInt_norm_sum_le _ _ hp_pos.le fun a _ => ?_
    rw [norm_mul]
    calc ‖mahlerBinom (p := p) j (a.val : ℤ_[p])‖ * ‖iwasawaInv R n a‖
        ≤ 1 * (p : ℝ) ^ (-(m : ℤ)) :=
          mul_le_mul (PadicInt.norm_le_one _) (hR_eval a) (norm_nonneg _) zero_le_one
      _ = (p : ℝ) ^ (-(m : ℤ)) := one_mul _
  have happrox := norm_measureIntegral_sub_riemannSum_le (iwasawaInv R) (continuous_mahlerBinom j)
    n hp_pos.le hn
  have hdecomp : measureIntegral (iwasawaInv R) (mahlerBinom j) =
      (measureIntegral (iwasawaInv R) (mahlerBinom j) - riemannSum (iwasawaInv R) (mahlerBinom j) n) +
      riemannSum (iwasawaInv R) (mahlerBinom j) n := by ring
  rw [hdecomp]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le happrox hriem_R)

/-- **Concrete Amice–Mahler–Iwasawa Ring Isomorphism**: `PadicMeasure p ≃+* ℤ_[p][[T]]`. -/
def amiceMahlerIwasawaRingEquiv : PadicMeasure p ≃+* IwasawaAlg p :=
  RingEquiv.ofBijective iwasawaTransformRingHom
    ⟨Function.LeftInverse.injective iwasawaInv_iwasawaTransform,
     Function.RightInverse.surjective iwasawaTransform_iwasawaInv⟩

/-- **Concrete Amice–Mahler–Iwasawa `ℤ_[p]`-Algebra Isomorphism**:
`PadicMeasure p ≃ₐ[ℤ_[p]] ℤ_[p][[T]]`. -/
def amiceMahlerIwasawaAlgEquiv : PadicMeasure p ≃ₐ[ℤ_[p]] IwasawaAlg p :=
  AlgEquiv.ofBijective iwasawaTransformAlgHom
    ⟨Function.LeftInverse.injective iwasawaInv_iwasawaTransform,
     Function.RightInverse.surjective iwasawaTransform_iwasawaInv⟩

/-- **Concrete Amice–Mahler–Iwasawa `ℤ_[p]`-Linear Isomorphism**:
`PadicMeasure p ≃ₗ[ℤ_[p]] ℤ_[p][[T]]`. -/
def amiceMahlerIwasawaLinearEquiv : PadicMeasure p ≃ₗ[ℤ_[p]] IwasawaAlg p :=
  amiceMahlerIwasawaAlgEquiv.toLinearEquiv

/-! ### Mod-`ω_n` Weierstrass Division & Exact Level-`n` Coefficient Matching -/

lemma evalLevel_omegaElem (n : ℕ) : evalLevel (p := p) n (omegaElem p n) = 0 := by
  unfold omegaElem
  rw [evalLevel_sub, evalLevel_one_add_X_pow, evalLevel_one]
  have h0 : ((p ^ n : ℕ) : ZMod (p ^ n)) = 0 := ZMod.natCast_self (p ^ n)
  rw [h0]
  exact sub_self _

/-- Power-series shift-down `q_d(F)` and truncation `r_d(F)` so `F = r_d(F) + X^d * q_d(F)`. -/
def psTrunc (d : ℕ) (F : IwasawaAlg p) : IwasawaAlg p :=
  ∑ k ∈ Finset.range d, PowerSeries.C (PowerSeries.coeff k F) * PowerSeries.X ^ k

def psShift (d : ℕ) (F : IwasawaAlg p) : IwasawaAlg p :=
  PowerSeries.mk (fun k => PowerSeries.coeff (k + d) F)

lemma ps_eq_trunc_add_X_pow_mul_shift (d : ℕ) (F : IwasawaAlg p) :
    F = psTrunc d F + PowerSeries.X ^ d * psShift d F := by
  ext k
  rw [map_add]
  have h1 : PowerSeries.coeff k (psTrunc d F) = if k < d then PowerSeries.coeff k F else 0 := by
    unfold psTrunc
    rw [map_sum]
    simp_rw [PowerSeries.coeff_C_mul_X_pow]
    by_cases hk : k < d
    · rw [if_pos hk, Finset.sum_eq_single k]
      · simp
      · intro i _ hi; simp [hi.symm]
      · intro hnot; exact absurd (Finset.mem_range.mpr hk) hnot
    · rw [if_neg hk]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hik : i ≠ k := ne_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hi) (not_lt.mp hk))
      simp [hik.symm]
  have h2 : PowerSeries.coeff k (PowerSeries.X ^ d * psShift d F) =
      if d ≤ k then PowerSeries.coeff k F else 0 := by
    rw [PowerSeries.coeff_X_pow_mul']
    split_ifs with h
    · rw [psShift, PowerSeries.coeff_mk, Nat.sub_add_cancel h]
    · rfl
  rw [h1, h2]
  by_cases hk : k < d
  · rw [if_pos hk, if_neg (not_le.mpr hk), add_zero]
  · rw [if_neg hk, if_pos (not_lt.mp hk), zero_add]

lemma evalLevel_mul (n : ℕ) (F G : IwasawaAlg p) :
    evalLevel (p := p) n (F * G) = evalLevel n F * evalLevel n G := by
  have h1 : iwasawaTransform (iwasawaInv F * iwasawaInv G) = F * G := by
    rw [iwasawaTransform_mul, iwasawaTransform_iwasawaInv, iwasawaTransform_iwasawaInv]
  have h2 : iwasawaInv (F * G) = iwasawaInv F * iwasawaInv G := by
    rw [← h1, iwasawaInv_iwasawaTransform]
  ext a
  have h3 := congrArg (fun μ : PadicMeasure p => μ n a) h2
  simpa [iwasawaInv, PadicMeasure.mul_apply, LevelAlg.mul_apply] using h3

/-- **Weierstrass Division by `ω_n = (1 + T)^(p^n) - 1` in `ℤ_[p][[T]]`**:
every `F ∈ ℤ_[p][[T]]` splits as `F = R + ω_n * Q` where `R` is a polynomial of degree `< p^n`. -/
theorem weierstrass_div_omegaElem (n : ℕ) (F : IwasawaAlg p) :
    ∃ (r : Fin (p ^ n) → ℤ_[p]) (Q : IwasawaAlg p),
      F = (∑ j : Fin (p ^ n), PowerSeries.C (r j) * PowerSeries.X ^ (j : ℕ)) +
        omegaElem p n * Q := by
  obtain ⟨g, hg⟩ := exists_omegaElem_eq_X_pow_add_p_mul p n
  set d := p ^ n
  let step : ℕ → IwasawaAlg p := Nat.rec F (fun _ G => -(g * psShift d G))
  have hstep_succ : ∀ m, step (m + 1) = -(g * psShift d (step m)) := fun _ => rfl
  have hstep_zero : step 0 = F := rfl
  have hp_lt1 : ‖(p : ℤ_[p])‖ < 1 := by
    change ‖(p : ℚ_[p])‖ < 1
    rw [Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have hsum_coeff : ∀ (seq : ℕ → ℤ_[p]), Summable (fun m : ℕ => (p : ℤ_[p]) ^ m * seq m) := by
    intro seq
    have hnorm : Summable (fun m : ℕ => ‖(p : ℤ_[p]) ^ m * seq m‖) := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
        (summable_geometric_of_lt_one (norm_nonneg _) hp_lt1)
      rw [norm_mul, norm_pow]
      calc ‖(p : ℤ_[p])‖ ^ m * ‖seq m‖ ≤ ‖(p : ℤ_[p])‖ ^ m * 1 :=
            mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (pow_nonneg (norm_nonneg _) m)
        _ = ‖(p : ℤ_[p])‖ ^ m := mul_one _
    exact hnorm.of_norm
  let r : Fin d → ℤ_[p] := fun j => ∑' m : ℕ, (p : ℤ_[p]) ^ m * PowerSeries.coeff (j : ℕ) (step m)
  let Q : IwasawaAlg p := PowerSeries.mk (fun k =>
    ∑' m : ℕ, (p : ℤ_[p]) ^ m * PowerSeries.coeff k (psShift d (step m)))
  refine ⟨r, Q, ?_⟩
  -- Check coefficient-by-coefficient via partial sums mod p^M!
  have hpart : ∀ M : ℕ,
      F = (∑ m ∈ Finset.range M, PowerSeries.C ((p : ℤ_[p]) ^ m) * psTrunc d (step m)) +
          omegaElem p n * (∑ m ∈ Finset.range M, PowerSeries.C ((p : ℤ_[p]) ^ m) * psShift d (step m)) +
          PowerSeries.C ((p : ℤ_[p]) ^ M) * step M := by
    intro M
    induction M with
    | zero => simp [hstep_zero]
    | succ M ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add]
      have hsplitM : step M = psTrunc d (step M) + omegaElem p n * psShift d (step M) +
          PowerSeries.C (p : ℤ_[p]) * step (M + 1) := by
        rw [hstep_succ, hg]
        conv_lhs => rw [ps_eq_trunc_add_X_pow_mul_shift d (step M)]
        ring
      conv_lhs => rw [ih, hsplitM]
      rw [pow_succ, map_mul]
      ring
  ext k
  refine padicInt_eq_of_forall_norm_le_pow fun M => ?_
  have hM := congrArg (PowerSeries.coeff k) (hpart M)
  rw [hM]
  have hR_coeff : PowerSeries.coeff k
      (∑ j : Fin d, PowerSeries.C (r j) * PowerSeries.X ^ (j : ℕ)) =
      if hk : k < d then r ⟨k, hk⟩ else 0 := by
    rw [map_sum]
    simp_rw [PowerSeries.coeff_C_mul_X_pow]
    by_cases hk : k < d
    · rw [dif_pos hk, Finset.sum_eq_single ⟨k, hk⟩]
      · simp
      · intro j _ hj
        have hne : (j : ℕ) ≠ k := fun h => hj (Fin.ext h)
        simp [hne.symm]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [dif_neg hk]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hne : (j : ℕ) ≠ k := ne_of_lt (lt_of_lt_of_le j.2 (not_lt.mp hk))
      simp [hne.symm]
  have hR_part : PowerSeries.coeff k
      (∑ m ∈ Finset.range M, PowerSeries.C ((p : ℤ_[p]) ^ m) * psTrunc d (step m)) =
      if k < d then ∑ m ∈ Finset.range M, (p : ℤ_[p]) ^ m * PowerSeries.coeff k (step m) else 0 := by
    rw [map_sum]
    by_cases hk : k < d
    · rw [if_pos hk]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [PowerSeries.coeff_C_mul]
      congr 1
      unfold psTrunc
      rw [map_sum]
      simp_rw [PowerSeries.coeff_C_mul_X_pow]
      rw [Finset.sum_eq_single k]
      · simp
      · intro i _ hi; simp [hi.symm]
      · intro hnot; exact absurd (Finset.mem_range.mpr hk) hnot
    · rw [if_neg hk]
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [PowerSeries.coeff_C_mul]
      have hz : PowerSeries.coeff k (psTrunc d (step m)) = 0 := by
        unfold psTrunc
        rw [map_sum]
        simp_rw [PowerSeries.coeff_C_mul_X_pow]
        refine Finset.sum_eq_zero fun i hi => ?_
        have hne : i ≠ k := ne_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hi) (not_lt.mp hk))
        simp [hne.symm]
      rw [hz, mul_zero]
  have htail_bd : ∀ (seq : ℕ → ℤ_[p]),
      ‖(∑' m : ℕ, (p : ℤ_[p]) ^ m * seq m) - ∑ m ∈ Finset.range M, (p : ℤ_[p]) ^ m * seq m‖ ≤
        (p : ℝ) ^ (-(M : ℤ)) := by
    intro seq
    have hs := hsum_coeff seq
    have hsp : (∑' m : ℕ, (p : ℤ_[p]) ^ m * seq m) - ∑ m ∈ Finset.range M, (p : ℤ_[p]) ^ m * seq m =
        ∑' m : ℕ, (p : ℤ_[p]) ^ (m + M) * seq (m + M) := by
      rw [← hs.sum_add_tsum_nat_add M]; ring
    rw [hsp]
    have hs' := (summable_nat_add_iff M).mpr hs
    have hlim : Tendsto (fun N => ‖∑ m ∈ Finset.range N, (p : ℤ_[p]) ^ (m + M) * seq (m + M)‖)
        atTop (nhds ‖∑' m : ℕ, (p : ℤ_[p]) ^ (m + M) * seq (m + M)‖) :=
      hs'.hasSum.tendsto_sum_nat.norm
    refine le_of_tendsto' hlim fun N => ?_
    refine padicInt_norm_sum_le _ _ (by positivity) fun m _ => ?_
    rw [pow_add, mul_assoc, norm_mul, norm_pow]
    have hnp : ‖(p : ℤ_[p])‖ ^ M = (p : ℝ) ^ (-(M : ℤ)) := by
      change ‖(p : ℚ_[p])‖ ^ M = _
      rw [Padic.norm_p, inv_pow, zpow_neg, zpow_natCast]
    have hmul_comm : ‖(p : ℤ_[p])‖ ^ m * ‖(p : ℤ_[p]) ^ M * seq (m + M)‖ ≤ (p : ℝ) ^ (-(M : ℤ)) := by
      rw [norm_mul, norm_pow, hnp]
      calc ‖(p : ℤ_[p])‖ ^ m * ((p : ℝ) ^ (-(M : ℤ)) * ‖seq (m + M)‖)
          ≤ 1 * ((p : ℝ) ^ (-(M : ℤ)) * 1) :=
            mul_le_mul (pow_le_one₀ (norm_nonneg _) hp_lt1.le)
              (mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (by positivity))
              (by positivity) zero_le_one
        _ = (p : ℝ) ^ (-(M : ℤ)) := by ring
    exact hmul_comm
  have hQ_coeff : ∀ j : ℕ,
      ‖PowerSeries.coeff j (∑ m ∈ Finset.range M, PowerSeries.C ((p : ℤ_[p]) ^ m) * psShift d (step m)) -
        PowerSeries.coeff j Q‖ ≤ (p : ℝ) ^ (-(M : ℤ)) := by
    intro j
    rw [map_sum]
    simp_rw [PowerSeries.coeff_C_mul]
    rw [PowerSeries.coeff_mk, ← norm_neg, neg_sub]
    exact htail_bd (fun m => PowerSeries.coeff j (psShift d (step m)))
  -- Combine all three error terms!
  simp only [map_add]
  have hdiff_split :
      (PowerSeries.coeff k (∑ m ∈ Finset.range M, PowerSeries.C ((p : ℤ_[p]) ^ m) * psTrunc d (step m)) +
        PowerSeries.coeff k (omegaElem p n * ∑ m ∈ Finset.range M, PowerSeries.C ((p : ℤ_[p]) ^ m) * psShift d (step m)) +
        PowerSeries.coeff k (PowerSeries.C ((p : ℤ_[p]) ^ M) * step M)) -
      (PowerSeries.coeff k (∑ j : Fin d, PowerSeries.C (r j) * PowerSeries.X ^ (j : ℕ)) +
        PowerSeries.coeff k (omegaElem p n * Q)) =
      (PowerSeries.coeff k (∑ m ∈ Finset.range M, PowerSeries.C ((p : ℤ_[p]) ^ m) * psTrunc d (step m)) -
        PowerSeries.coeff k (∑ j : Fin d, PowerSeries.C (r j) * PowerSeries.X ^ (j : ℕ))) +
      (PowerSeries.coeff k (omegaElem p n * ∑ m ∈ Finset.range M, PowerSeries.C ((p : ℤ_[p]) ^ m) * psShift d (step m)) -
        PowerSeries.coeff k (omegaElem p n * Q)) +
      PowerSeries.coeff k (PowerSeries.C ((p : ℤ_[p]) ^ M) * step M) := by ring
  rw [hdiff_split]
  have hbd1 : ‖PowerSeries.coeff k (∑ m ∈ Finset.range M, PowerSeries.C ((p : ℤ_[p]) ^ m) * psTrunc d (step m)) -
      PowerSeries.coeff k (∑ j : Fin d, PowerSeries.C (r j) * PowerSeries.X ^ (j : ℕ))‖ ≤
      (p : ℝ) ^ (-(M : ℤ)) := by
    rw [hR_part, hR_coeff]
    by_cases hk : k < d
    · rw [if_pos hk, dif_pos hk, ← norm_neg, neg_sub]
      exact htail_bd (fun m => PowerSeries.coeff k (step m))
    · rw [if_neg hk, dif_neg hk, sub_self, norm_zero]
      positivity
  have hbd2 : ‖PowerSeries.coeff k (omegaElem p n * ∑ m ∈ Finset.range M, PowerSeries.C ((p : ℤ_[p]) ^ m) * psShift d (step m)) -
      PowerSeries.coeff k (omegaElem p n * Q)‖ ≤ (p : ℝ) ^ (-(M : ℤ)) := by
    rw [← map_sub, ← mul_sub, PowerSeries.coeff_mul]
    refine padicInt_norm_sum_le _ _ (by positivity) fun ab _ => ?_
    rw [norm_mul, map_sub]
    calc ‖PowerSeries.coeff ab.1 (omegaElem p n)‖ *
          ‖PowerSeries.coeff ab.2 (∑ m ∈ Finset.range M, PowerSeries.C ((p : ℤ_[p]) ^ m) * psShift d (step m)) -
            PowerSeries.coeff ab.2 Q‖
        ≤ 1 * (p : ℝ) ^ (-(M : ℤ)) :=
          mul_le_mul (PadicInt.norm_le_one _) (hQ_coeff ab.2) (norm_nonneg _) zero_le_one
      _ = (p : ℝ) ^ (-(M : ℤ)) := one_mul _
  have hbd3 : ‖PowerSeries.coeff k (PowerSeries.C ((p : ℤ_[p]) ^ M) * step M)‖ ≤
      (p : ℝ) ^ (-(M : ℤ)) := by
    rw [PowerSeries.coeff_C_mul, norm_mul, norm_pow]
    have hnp : ‖(p : ℤ_[p])‖ ^ M = (p : ℝ) ^ (-(M : ℤ)) := by
      change ‖(p : ℚ_[p])‖ ^ M = _
      rw [Padic.norm_p, inv_pow, zpow_neg, zpow_natCast]
    rw [hnp]
    calc (p : ℝ) ^ (-(M : ℤ)) * ‖PowerSeries.coeff k (step M)‖
        ≤ (p : ℝ) ^ (-(M : ℤ)) * 1 :=
          mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (by positivity)
      _ = (p : ℝ) ^ (-(M : ℤ)) := mul_one _
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hbd3)
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hbd1 hbd2)

/-- Change of basis from `X^j` to `(1 + X)^j` for polynomials of degree `< d` in `ℤ_[p][[T]]`. -/
lemma exists_pow_one_add_X_repr (d : ℕ) (r : Fin d → ℤ_[p]) :
    ∃ b : Fin d → ℤ_[p],
      (∑ j : Fin d, PowerSeries.C (r j) * PowerSeries.X ^ (j : ℕ)) =
        ∑ i : Fin d, PowerSeries.C (b i) * (1 + PowerSeries.X) ^ (i : ℕ) := by
  let b : Fin d → ℤ_[p] := fun i =>
    ∑ j : Fin d, if (i : ℕ) ≤ (j : ℕ) then
      r j * ((-1 : ℤ_[p]) ^ ((j : ℕ) - (i : ℕ)) * ((j : ℕ).choose (i : ℕ) : ℤ_[p]))
    else 0
  refine ⟨b, ?_⟩
  have hX : ∀ j : Fin d,
      PowerSeries.X ^ (j : ℕ) =
        ∑ i : Fin d, if (i : ℕ) ≤ (j : ℕ) then
          PowerSeries.C (((-1 : ℤ_[p]) ^ ((j : ℕ) - (i : ℕ)) * ((j : ℕ).choose (i : ℕ) : ℤ_[p]))) *
            (1 + PowerSeries.X) ^ (i : ℕ)
        else 0 := by
    intro j
    have hbin : (PowerSeries.X : IwasawaAlg p) ^ (j : ℕ) = ((1 + PowerSeries.X) + (-1)) ^ (j : ℕ) := by
      ring
    rw [hbin, add_pow]
    have hsplit : ∑ i ∈ Finset.range ((j : ℕ) + 1),
        (1 + PowerSeries.X : IwasawaAlg p) ^ i * (-1 : IwasawaAlg p) ^ ((j : ℕ) - i) *
          (((j : ℕ).choose i : ℕ) : IwasawaAlg p) =
        ∑ i : Fin d, if (i : ℕ) ≤ (j : ℕ) then
          PowerSeries.C (((-1 : ℤ_[p]) ^ ((j : ℕ) - (i : ℕ)) * ((j : ℕ).choose (i : ℕ) : ℤ_[p]))) *
            (1 + PowerSeries.X) ^ (i : ℕ)
        else 0 := by
      rw [← Finset.sum_filter]
      refine Finset.sum_bij (fun i hi => ⟨i, Nat.lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) j.2⟩)
        ?_ ?_ ?_ ?_
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      · intro i₁ _ i₂ _ h; exact congrArg Fin.val h
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact ⟨i.1, Finset.mem_range.mpr (Nat.lt_succ_of_le hi), Fin.ext rfl⟩
      · intro i _
        simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
        ring
    exact hsplit
  calc ∑ j : Fin d, PowerSeries.C (r j) * PowerSeries.X ^ (j : ℕ)
      = ∑ j : Fin d, PowerSeries.C (r j) *
          (∑ i : Fin d, if (i : ℕ) ≤ (j : ℕ) then
            PowerSeries.C (((-1 : ℤ_[p]) ^ ((j : ℕ) - (i : ℕ)) * ((j : ℕ).choose (i : ℕ) : ℤ_[p]))) *
              (1 + PowerSeries.X) ^ (i : ℕ)
          else 0) := Finset.sum_congr rfl fun j _ => by rw [hX j]
    _ = ∑ j : Fin d, ∑ i : Fin d,
          PowerSeries.C (if (i : ℕ) ≤ (j : ℕ) then
            r j * ((-1 : ℤ_[p]) ^ ((j : ℕ) - (i : ℕ)) * ((j : ℕ).choose (i : ℕ) : ℤ_[p]))
          else 0) * (1 + PowerSeries.X) ^ (i : ℕ) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs
        · simp only [map_mul, mul_assoc]
        · simp
    _ = ∑ i : Fin d, PowerSeries.C (b i) * (1 + PowerSeries.X) ^ (i : ℕ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        dsimp only [b]
        rw [map_sum, Finset.sum_mul]

/-- **Exact Mod-`ω_n` Matching Theorem**:
for every `μ : PadicMeasure p` and level `n : ℕ`,
`iwasawaTransform μ ≡ ∑_{a : ZMod (p^n)} μ n a * (1 + T)^(a.val) [mod ω_n]`! -/
theorem exists_iwasawaTransform_eq_sum_add_omegaElem_mul (μ : PadicMeasure p) (n : ℕ) :
    ∃ Q : IwasawaAlg p,
      iwasawaTransform μ =
        (∑ a : ZMod (p ^ n), PowerSeries.C (μ n a) * (1 + PowerSeries.X) ^ a.val) +
          omegaElem p n * Q := by
  obtain ⟨r, Q, hQ⟩ := weierstrass_div_omegaElem n (iwasawaTransform μ)
  obtain ⟨b, hb⟩ := exists_pow_one_add_X_repr (p ^ n) r
  refine ⟨Q, ?_⟩
  rw [hQ, hb]
  congr 1
  -- Evaluate both sides at level n via evalLevel to identify b i = μ n (i : ZMod (p^n))!
  have heval := congrArg (evalLevel (p := p) n) (hQ.trans (by rw [hb]))
  rw [evalLevel_add, evalLevel_mul, evalLevel_omegaElem, zero_mul, add_zero] at heval
  have hL : evalLevel (p := p) n (iwasawaTransform μ) = ⟨μ n⟩ := by
    ext a
    exact congrArg (fun ν : PadicMeasure p => ν n a) (iwasawaInv_iwasawaTransform μ)
  have hR : evalLevel (p := p) n (∑ i : Fin (p ^ n), PowerSeries.C (b i) * (1 + PowerSeries.X) ^ (i : ℕ)) =
      ∑ i : Fin (p ^ n), b i • levelDirac n ((i : ℕ) : ZMod (p ^ n)) := by
    have haux : ∀ s : Finset (Fin (p ^ n)),
        evalLevel (p := p) n (∑ i ∈ s, PowerSeries.C (b i) * (1 + PowerSeries.X) ^ (i : ℕ)) =
          ∑ i ∈ s, b i • levelDirac n ((i : ℕ) : ZMod (p ^ n)) := by
      intro s
      classical
      induction s using Finset.induction_on with
      | empty => ext a; simp [evalLevel_apply]
      | insert x s hx ih =>
        rw [Finset.sum_insert hx, Finset.sum_insert hx, evalLevel_add, evalLevel_smul,
          evalLevel_one_add_X_pow, ih]
    exact haux Finset.univ
  rw [hL, hR] at heval
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  have hb_eq : ∀ i : Fin (p ^ n), b i = μ n ((i : ℕ) : ZMod (p ^ n)) := by
    intro i
    have hpt := congrArg (fun u : LevelAlg p n => u ((i : ℕ) : ZMod (p ^ n))) heval
    rw [levelAlg_sum_apply] at hpt
    rw [Finset.sum_eq_single i] at hpt
    · simpa [levelDirac] using hpt.symm
    · intro j _ hj
      simp only [LevelAlg.smul_apply, levelDirac_apply]
      have hne : ((j : ℕ) : ZMod (p ^ n)) ≠ ((i : ℕ) : ZMod (p ^ n)) := by
        intro heq
        apply hj
        apply Fin.ext
        have h1 := congrArg ZMod.val heq
        rw [ZMod.val_natCast_of_lt j.2, ZMod.val_natCast_of_lt i.2] at h1
        exact h1
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  refine Finset.sum_bij (fun (i : Fin (p ^ n)) _ => ((i : ℕ) : ZMod (p ^ n))) ?_ ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · intro i₁ _ i₂ _ h
    apply Fin.ext
    have h1 := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt i₁.2, ZMod.val_natCast_of_lt i₂.2] at h1
    exact h1
  · intro a _
    refine ⟨⟨a.val, ZMod.val_lt a⟩, Finset.mem_univ _, ?_⟩
    exact ZMod.natCast_zmod_val a
  · intro i _
    rw [hb_eq i, ZMod.val_natCast_of_lt i.2]

/-- Exact kernel characterization: `ω_n ∣ iwasawaTransform μ ↔ μ n = 0`. -/
theorem omegaElem_dvd_iwasawaTransform_iff (μ : PadicMeasure p) (n : ℕ) :
    omegaElem p n ∣ iwasawaTransform μ ↔ ∀ a : ZMod (p ^ n), μ n a = 0 := by
  constructor
  · rintro ⟨Q, hQ⟩ a
    have h1 := congrArg (evalLevel (p := p) n) hQ
    rw [evalLevel_mul, evalLevel_omegaElem, zero_mul] at h1
    have h2 : evalLevel (p := p) n (iwasawaTransform μ) a = μ n a :=
      congrArg (fun ν : PadicMeasure p => ν n a) (iwasawaInv_iwasawaTransform μ)
    rw [← h2, h1, LevelAlg.zero_apply]
  · intro h0
    obtain ⟨Q, hQ⟩ := exists_iwasawaTransform_eq_sum_add_omegaElem_mul μ n
    refine ⟨Q, ?_⟩
    rw [hQ]
    have hsum0 : ∑ a : ZMod (p ^ n), PowerSeries.C (μ n a) * (1 + PowerSeries.X) ^ a.val = 0 := by
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [h0 a, map_zero, zero_mul]
    rw [hsum0, zero_add]

/-! ### Analytic Evaluation of Iwasawa Power Series & Amice–Iwasawa Character Formula -/

/-- Continuous $p$-adic power `(1 + y) ^ x = ∑' k, C(x, k) * y ^ k` for `y ∈ p ℤ_[p]` (`‖y‖ < 1`). -/
def padicPowOneAdd (y x : ℤ_[p]) : ℤ_[p] :=
  ∑' k : ℕ, mahlerBinom k x * y ^ k

/-- Analytic evaluation of an Iwasawa power series `F ∈ ℤ_[p][[T]]` at `y ∈ p ℤ_[p]`:
`evalIwasawa F y = ∑' k, coeff k F * y ^ k`. -/
def evalIwasawa (F : IwasawaAlg p) (y : ℤ_[p]) : ℤ_[p] :=
  ∑' k : ℕ, PowerSeries.coeff k F * y ^ k

lemma summable_padicPowOneAdd_term {y : ℤ_[p]} (hy : ‖y‖ < 1) (x : ℤ_[p]) :
    Summable (fun k : ℕ => mahlerBinom (p := p) k x * y ^ k) := by
  have hnorm : Summable (fun k : ℕ => ‖mahlerBinom (p := p) k x * y ^ k‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
      (summable_geometric_of_lt_one (norm_nonneg _) hy)
    rw [norm_mul, norm_pow]
    calc ‖mahlerBinom (p := p) k x‖ * ‖y‖ ^ k ≤ 1 * ‖y‖ ^ k :=
          mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _) (pow_nonneg (norm_nonneg _) k)
      _ = ‖y‖ ^ k := one_mul _
  exact hnorm.of_norm

lemma summable_evalIwasawa_term (F : IwasawaAlg p) {y : ℤ_[p]} (hy : ‖y‖ < 1) :
    Summable (fun k : ℕ => PowerSeries.coeff k F * y ^ k) := by
  have hnorm : Summable (fun k : ℕ => ‖PowerSeries.coeff k F * y ^ k‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
      (summable_geometric_of_lt_one (norm_nonneg _) hy)
    rw [norm_mul, norm_pow]
    calc ‖PowerSeries.coeff k F‖ * ‖y‖ ^ k ≤ 1 * ‖y‖ ^ k :=
          mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _) (pow_nonneg (norm_nonneg _) k)
      _ = ‖y‖ ^ k := one_mul _
  exact hnorm.of_norm

lemma norm_padicPowOneAdd_sub_trunc_le {y : ℤ_[p]} (hy : ‖y‖ < 1) (x : ℤ_[p]) (K : ℕ) :
    ‖padicPowOneAdd y x - ∑ k ∈ Finset.range K, mahlerBinom k x * y ^ k‖ ≤ ‖y‖ ^ K := by
  have hs := summable_padicPowOneAdd_term hy x
  have hsp : padicPowOneAdd y x - ∑ k ∈ Finset.range K, mahlerBinom k x * y ^ k =
      ∑' k : ℕ, mahlerBinom (k + K) x * y ^ (k + K) := by
    unfold padicPowOneAdd
    rw [← hs.sum_add_tsum_nat_add K]
    ring
  rw [hsp]
  have hs' := (summable_nat_add_iff K).mpr hs
  have hlim : Tendsto (fun N => ‖∑ k ∈ Finset.range N, mahlerBinom (k + K) x * y ^ (k + K)‖)
      atTop (nhds ‖∑' k : ℕ, mahlerBinom (k + K) x * y ^ (k + K)‖) :=
    hs'.hasSum.tendsto_sum_nat.norm
  refine le_of_tendsto' hlim fun N => ?_
  refine padicInt_norm_sum_le _ _ (pow_nonneg (norm_nonneg _) K) fun k _ => ?_
  rw [norm_mul, norm_pow, pow_add]
  calc ‖mahlerBinom (p := p) (k + K) x‖ * (‖y‖ ^ k * ‖y‖ ^ K)
      ≤ 1 * (1 * ‖y‖ ^ K) :=
        mul_le_mul (PadicInt.norm_le_one _)
          (mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hy.le)
            (pow_nonneg (norm_nonneg _) K))
          (by positivity) zero_le_one
    _ = ‖y‖ ^ K := by ring

theorem continuous_padicPowOneAdd {y : ℤ_[p]} (hy : ‖y‖ < 1) :
    Continuous (padicPowOneAdd (p := p) y) := by
  rw [Metric.continuous_iff]
  intro x ε hε
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hε hy
  have hcont_trunc : Continuous (fun z : ℤ_[p] => ∑ k ∈ Finset.range K, mahlerBinom (p := p) k z * y ^ k) :=
    continuous_finsetSum _ fun k _ => (continuous_mahlerBinom k).mul continuous_const
  obtain ⟨δ, hδ, hδ_bound⟩ := Metric.continuous_iff.mp hcont_trunc x ε hε
  refine ⟨δ, hδ, fun z hz => ?_⟩
  rw [dist_eq_norm]
  have h1 := norm_padicPowOneAdd_sub_trunc_le hy z K
  have h2 := norm_padicPowOneAdd_sub_trunc_le hy x K
  have h3 : ‖(∑ k ∈ Finset.range K, mahlerBinom (p := p) k z * y ^ k) -
      (∑ k ∈ Finset.range K, mahlerBinom (p := p) k x * y ^ k)‖ < ε := by
    have := hδ_bound z hz; rwa [dist_eq_norm] at this
  have hdecomp : padicPowOneAdd y z - padicPowOneAdd y x =
      (padicPowOneAdd y z - ∑ k ∈ Finset.range K, mahlerBinom k z * y ^ k) +
      ((∑ k ∈ Finset.range K, mahlerBinom k z * y ^ k) -
        (∑ k ∈ Finset.range K, mahlerBinom k x * y ^ k)) -
      (padicPowOneAdd y x - ∑ k ∈ Finset.range K, mahlerBinom k x * y ^ k) := by ring
  rw [hdecomp]
  refine (padicInt_norm_sub_le_max _ _).trans_lt (max_lt ?_ (h2.trans_lt hK))
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (h1.trans_lt hK) h3)

theorem padicPowOneAdd_natCast {y : ℤ_[p]} (n : ℕ) :
    padicPowOneAdd (p := p) y (n : ℤ_[p]) = (1 + y) ^ n := by
  unfold padicPowOneAdd
  rw [tsum_eq_sum (s := Finset.range (n + 1))]
  · rw [add_comm 1 y, add_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mahlerBinom_natCast, one_pow, mul_one, mul_comm]
  · intro k hk
    have hlt : n < k := by
      rw [Finset.mem_range, not_lt] at hk
      omega
    rw [mahlerBinom_natCast, Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero, zero_mul]

theorem padicPowOneAdd_add {y : ℤ_[p]} (hy : ‖y‖ < 1) (x₁ x₂ : ℤ_[p]) :
    padicPowOneAdd (p := p) y (x₁ + x₂) = padicPowOneAdd y x₁ * padicPowOneAdd y x₂ := by
  have hnat : ∀ (n : ℕ) (z : ℤ_[p]),
      padicPowOneAdd (p := p) y ((n : ℤ_[p]) + z) =
        padicPowOneAdd y (n : ℤ_[p]) * padicPowOneAdd y z := by
    intro n
    have hL : Continuous (fun z : ℤ_[p] => padicPowOneAdd (p := p) y ((n : ℤ_[p]) + z)) :=
      (continuous_padicPowOneAdd hy).comp (continuous_const.add continuous_id)
    have hR : Continuous (fun z : ℤ_[p] => padicPowOneAdd (p := p) y (n : ℤ_[p]) * padicPowOneAdd y z) :=
      continuous_const.mul (continuous_padicPowOneAdd hy)
    exact congrFun (PadicInt.denseRange_natCast.equalizer hL hR (by
      ext m
      dsimp only [Function.comp_apply]
      rw [← Nat.cast_add, padicPowOneAdd_natCast, padicPowOneAdd_natCast, padicPowOneAdd_natCast,
        pow_add]))
  have hL : Continuous (fun w : ℤ_[p] => padicPowOneAdd (p := p) y (w + x₂)) :=
    (continuous_padicPowOneAdd hy).comp (continuous_id.add continuous_const)
  have hR : Continuous (fun w : ℤ_[p] => padicPowOneAdd (p := p) y w * padicPowOneAdd y x₂) :=
    (continuous_padicPowOneAdd hy).mul continuous_const
  exact congrFun (PadicInt.denseRange_natCast.equalizer hL hR (by ext n; exact hnat n x₂)) x₁

/-- **Amice–Iwasawa Analytic Evaluation Theorem**:
for every `μ : PadicMeasure p` and every `y ∈ p ℤ_[p]` (`‖y‖ < 1`),
`evalIwasawa (iwasawaTransform μ) y = ∫_{ℤ_[p]} (1 + y)^x dμ(x)`. -/
theorem evalIwasawa_iwasawaTransform (μ : PadicMeasure p) {y : ℤ_[p]} (hy : ‖y‖ < 1) :
    evalIwasawa (iwasawaTransform μ) y = measureIntegral μ (padicPowOneAdd y) := by
  have hs := summable_evalIwasawa_term (iwasawaTransform μ) hy
  have hlimL : Tendsto (fun K => ∑ k ∈ Finset.range K,
      PowerSeries.coeff k (iwasawaTransform μ) * y ^ k) atTop
      (nhds (evalIwasawa (iwasawaTransform μ) y)) := hs.hasSum.tendsto_sum_nat
  have hlimR : Tendsto (fun K => ∑ k ∈ Finset.range K,
      PowerSeries.coeff k (iwasawaTransform μ) * y ^ k) atTop
      (nhds (measureIntegral μ (padicPowOneAdd y))) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨K₀, hK₀⟩ := exists_pow_lt_of_lt_one hε hy
    refine ⟨K₀, fun K hK => ?_⟩
    rw [dist_eq_norm, ← norm_neg, neg_sub]
    have hsum_int : ∑ k ∈ Finset.range K, PowerSeries.coeff k (iwasawaTransform μ) * y ^ k =
        measureIntegral μ (fun x => ∑ k ∈ Finset.range K, mahlerBinom k x * y ^ k) := by
      rw [measureIntegral_sum_fun]
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [coeff_iwasawaTransform, mul_comm,
          ← measureIntegral_smul_fun μ (y ^ k) (continuous_mahlerBinom k)]
        congr 1; ext x; ring
      · intro k _; exact (continuous_mahlerBinom k).mul continuous_const
    rw [hsum_int]
    have hbd : ‖measureIntegral μ (padicPowOneAdd y) -
        measureIntegral μ (fun x => ∑ k ∈ Finset.range K, mahlerBinom k x * y ^ k)‖ ≤ ‖y‖ ^ K :=
      norm_measureIntegral_sub_le μ (continuous_padicPowOneAdd hy)
        (continuous_finsetSum _ fun k _ => (continuous_mahlerBinom k).mul continuous_const)
        (pow_nonneg (norm_nonneg _) K) (fun x => norm_padicPowOneAdd_sub_trunc_le hy x K)
    exact (hbd.trans (pow_le_pow_of_le_one (norm_nonneg _) hy.le hK)).trans_lt hK₀
  exact tendsto_nhds_unique hlimL hlimR

end AmiceMahlerIwasawa

/-! ## Section 3: Concrete Mazur Regularized Bernoulli Measure `μ_c` & Exact $k$-th Moment Identity -/

section MazurBernoulliMeasure

/-! ### Raabe's Multiplication Formula for Bernoulli Polynomials -/

/-- The Raabe discrepancy polynomial `M^(m - 1) ∑_{j < M} B_m((X + j) / M) - B_m(X) ∈ ℚ[X]`. -/
def raabePoly (M m : ℕ) : Polynomial ℚ :=
  Polynomial.C ((M : ℚ) ^ (m - 1)) *
    (∑ j ∈ Finset.range M,
      (Polynomial.bernoulli m).comp
        (Polynomial.C ((M : ℚ)⁻¹) * (Polynomial.X + Polynomial.C (j : ℚ)))) -
    Polynomial.bernoulli m

lemma raabePoly_one {M : ℕ} (hM : 0 < M) : raabePoly M 1 = 0 := by
  have hM0 : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  unfold raabePoly
  simp only [Nat.sub_self, pow_zero, map_one, one_mul, Polynomial.bernoulli_one,
    Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_add, Finset.sum_add_distrib]
  have hsum_j : ∑ j ∈ Finset.range M, (Polynomial.C ((M : ℚ)⁻¹) * Polynomial.C (j : ℚ)) =
      Polynomial.C (((M : ℚ) - 1) / 2) := by
    rw [← Finset.mul_sum]
    have hnat : (∑ j ∈ Finset.range M, (j : ℚ)) = (M : ℚ) * ((M : ℚ) - 1) / 2 := by
      have h2 := Finset.sum_range_id_mul_two M
      have h2Q : (∑ j ∈ Finset.range M, (j : ℚ)) * 2 = (M : ℚ) * ((M : ℚ) - 1) := by
        have hcast : ((∑ j ∈ Finset.range M, j) * 2 : ℕ) = M * (M - 1) := h2
        have hcastQ : (((∑ j ∈ Finset.range M, j) * 2 : ℕ) : ℚ) = ((M * (M - 1) : ℕ) : ℚ) := by
          exact_mod_cast hcast
        rw [Nat.cast_mul, Nat.cast_sum, Nat.cast_mul, Nat.cast_sub hM, Nat.cast_one] at hcastQ
        simpa using hcastQ
      linarith
    have hCsum : ∑ j ∈ Finset.range M, Polynomial.C (j : ℚ) = Polynomial.C (∑ j ∈ Finset.range M, (j : ℚ)) := by
      rw [map_sum]
    rw [hCsum, hnat, ← map_mul]
    congr 1
    field_simp [hM0]
  rw [hsum_j]
  have h1 : (M : Polynomial ℚ) * (Polynomial.C ((M : ℚ)⁻¹) * Polynomial.X) = Polynomial.X := by
    rw [← Polynomial.C_eq_natCast, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hM0, map_one, one_mul]
  have h2 : (M : Polynomial ℚ) * Polynomial.C (2⁻¹ : ℚ) = Polynomial.C ((M : ℚ) / 2) := by
    rw [← Polynomial.C_eq_natCast, ← map_mul, div_eq_mul_inv]
  rw [h1, h2]
  have h3 : Polynomial.C (((M : ℚ) - 1) / 2) - Polynomial.C ((M : ℚ) / 2) = -Polynomial.C (2⁻¹ : ℚ) := by
    rw [← map_sub, ← map_neg]
    congr 1
    ring
  calc Polynomial.X + Polynomial.C (((M : ℚ) - 1) / 2) - Polynomial.C ((M : ℚ) / 2) -
        (Polynomial.X - Polynomial.C (2⁻¹ : ℚ))
      = (Polynomial.C (((M : ℚ) - 1) / 2) - Polynomial.C ((M : ℚ) / 2)) + Polynomial.C (2⁻¹ : ℚ) := by ring
    _ = -Polynomial.C (2⁻¹ : ℚ) + Polynomial.C (2⁻¹ : ℚ) := by rw [h3]
    _ = 0 := neg_add_cancel _

lemma derivative_raabePoly {M : ℕ} (hM : 0 < M) {m : ℕ} (hm : 1 ≤ m) :
    Polynomial.derivative (raabePoly M (m + 1)) =
      Polynomial.C ((m + 1 : ℕ) : ℚ) * raabePoly M m := by
  have hM0 : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  unfold raabePoly
  rw [map_sub, Polynomial.derivative_C_mul, Polynomial.derivative_bernoulli_add_one, map_sum]
  have hterm : ∀ j : ℕ,
      Polynomial.derivative ((Polynomial.bernoulli (m + 1)).comp
        (Polynomial.C ((M : ℚ)⁻¹) * (Polynomial.X + Polynomial.C (j : ℚ)))) =
      Polynomial.C ((M : ℚ)⁻¹) * Polynomial.C ((m + 1 : ℕ) : ℚ) *
        (Polynomial.bernoulli m).comp
          (Polynomial.C ((M : ℚ)⁻¹) * (Polynomial.X + Polynomial.C (j : ℚ))) := by
    intro j
    rw [Polynomial.derivative_comp, Polynomial.derivative_bernoulli_add_one,
      Polynomial.derivative_C_mul, map_add, Polynomial.derivative_X, Polynomial.derivative_C,
      add_zero, mul_one, Polynomial.mul_comp]
    have hC : ((m + 1 : Polynomial ℚ)).comp
        (Polynomial.C ((M : ℚ)⁻¹) * (Polynomial.X + Polynomial.C (j : ℚ))) =
        Polynomial.C ((m + 1 : ℕ) : ℚ) := by
      have : (m + 1 : Polynomial ℚ) = Polynomial.C ((m + 1 : ℕ) : ℚ) := by
        rw [Nat.cast_add, Nat.cast_one, map_add, map_one, Polynomial.C_eq_natCast]
      rw [this, Polynomial.C_comp]
    rw [hC]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have hpow : (M : ℚ) ^ (m + 1 - 1) * (M : ℚ)⁻¹ = (M : ℚ) ^ (m - 1) := by
    have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
    rw [Nat.add_sub_cancel]
    conv_lhs => rw [← hm', pow_succ]
    rw [mul_assoc, mul_inv_cancel₀ hM0, mul_one]
  have hC1 : Polynomial.C ((M : ℚ) ^ (m + 1 - 1)) * (Polynomial.C ((M : ℚ)⁻¹) * Polynomial.C ((m + 1 : ℕ) : ℚ)) =
      Polynomial.C ((m + 1 : ℕ) : ℚ) * Polynomial.C ((M : ℚ) ^ (m - 1)) := by
    rw [← mul_assoc, ← map_mul, hpow, mul_comm]
  rw [← mul_assoc, hC1]
  have hC2 : ((m + 1 : Polynomial ℚ)) * Polynomial.bernoulli m =
      Polynomial.C ((m + 1 : ℕ) : ℚ) * Polynomial.bernoulli m := by
    have : (m + 1 : Polynomial ℚ) = Polynomial.C ((m + 1 : ℕ) : ℚ) := by
      rw [Nat.cast_add, Nat.cast_one, map_add, map_one, Polynomial.C_eq_natCast]
    rw [this]
  rw [hC2]
  ring

lemma raabePoly_eval_one_sub_zero {M : ℕ} (hM : 0 < M) {m : ℕ} (hm : 2 ≤ m) :
    (raabePoly M m).eval 1 - (raabePoly M m).eval 0 = 0 := by
  have hM0 : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hB10 : (Polynomial.bernoulli m).eval 1 = (Polynomial.bernoulli m).eval 0 := by
    have h := Polynomial.bernoulli_eval_one_add m 0
    rw [add_zero, zero_pow (by omega), mul_zero, add_zero] at h
    exact h
  unfold raabePoly
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finsetSum,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X]
  rw [hB10]
  have htele : ∑ j ∈ Finset.range M,
      ((Polynomial.bernoulli m).eval ((M : ℚ)⁻¹ * (1 + (j : ℚ))) -
        (Polynomial.bernoulli m).eval ((M : ℚ)⁻¹ * (0 + (j : ℚ)))) = 0 := by
    have hrew : ∀ j : ℕ,
        (Polynomial.bernoulli m).eval ((M : ℚ)⁻¹ * (1 + (j : ℚ))) -
          (Polynomial.bernoulli m).eval ((M : ℚ)⁻¹ * (0 + (j : ℚ))) =
        (Polynomial.bernoulli m).eval ((M : ℚ)⁻¹ * ((j + 1 : ℕ) : ℚ)) -
          (Polynomial.bernoulli m).eval ((M : ℚ)⁻¹ * (j : ℚ)) := by
      intro j; push_cast; ring_nf
    simp_rw [hrew]
    rw [Finset.sum_range_sub (fun j : ℕ => (Polynomial.bernoulli m).eval ((M : ℚ)⁻¹ * (j : ℚ))) M]
    rw [inv_mul_cancel₀ hM0, Nat.cast_zero, mul_zero, hB10, sub_self]
  calc (M : ℚ) ^ (m - 1) * ∑ j ∈ Finset.range M, (Polynomial.bernoulli m).eval ((M : ℚ)⁻¹ * (1 + ↑j)) -
          (Polynomial.bernoulli m).eval 0 -
        ((M : ℚ) ^ (m - 1) * ∑ j ∈ Finset.range M, (Polynomial.bernoulli m).eval ((M : ℚ)⁻¹ * (0 + ↑j)) -
          (Polynomial.bernoulli m).eval 0)
      = (M : ℚ) ^ (m - 1) * ∑ j ∈ Finset.range M,
          ((Polynomial.bernoulli m).eval ((M : ℚ)⁻¹ * (1 + ↑j)) -
            (Polynomial.bernoulli m).eval ((M : ℚ)⁻¹ * (0 + ↑j))) := by
        rw [Finset.sum_sub_distrib]; ring
    _ = 0 := by rw [htele, mul_zero]

lemma poly_eq_C_of_derivative_eq_zero {f : Polynomial ℚ} (hf : Polynomial.derivative f = 0) :
    f = Polynomial.C (f.coeff 0) := by
  ext k
  cases k with
  | zero => simp
  | succ k =>
    have hk := congrArg (fun g : Polynomial ℚ => g.coeff k) hf
    rw [Polynomial.coeff_derivative, Polynomial.coeff_zero] at hk
    have hne : ((k : ℚ) + 1) ≠ 0 := by positivity
    have h0 : f.coeff (k + 1) = 0 := (mul_eq_zero.mp hk).resolve_right hne
    rw [h0, Polynomial.coeff_C_succ]

/-- **Raabe's Multiplication Formula for Bernoulli Polynomials**:
for every `M ≥ 1` and `m ≥ 1`, `M^(m - 1) ∑_{j=0}^{M-1} B_m((X + j) / M) = B_m(X)`. -/
theorem raabePoly_eq_zero {M : ℕ} (hM : 0 < M) :
    ∀ {m : ℕ}, 1 ≤ m → raabePoly M m = 0
  | 0, hm => absurd hm (by omega)
  | 1, _ => raabePoly_one hM
  | m + 2, _ => by
    have ih : raabePoly M (m + 1) = 0 := raabePoly_eq_zero hM (by omega)
    have hderiv1 : Polynomial.derivative (raabePoly M (m + 2)) = 0 := by
      rw [derivative_raabePoly hM (by omega), ih, mul_zero]
    set c : ℚ := (raabePoly M (m + 2)).coeff 0
    have hC1 : raabePoly M (m + 2) = Polynomial.C c := poly_eq_C_of_derivative_eq_zero hderiv1
    have hderiv2 : Polynomial.derivative (raabePoly M (m + 3) -
        Polynomial.C (((m + 3 : ℕ) : ℚ) * c) * Polynomial.X) = 0 := by
      rw [map_sub, derivative_raabePoly hM (by omega), hC1, Polynomial.derivative_C_mul,
        Polynomial.derivative_X, mul_one, ← map_mul, sub_self]
    have hC2 := poly_eq_C_of_derivative_eq_zero hderiv2
    have hlin : raabePoly M (m + 3) =
        Polynomial.C ((raabePoly M (m + 3) - Polynomial.C (((m + 3 : ℕ) : ℚ) * c) * Polynomial.X).coeff 0) +
          Polynomial.C (((m + 3 : ℕ) : ℚ) * c) * Polynomial.X := eq_add_of_sub_eq hC2
    have hev := raabePoly_eval_one_sub_zero hM (m := m + 3) (by omega)
    rw [hlin] at hev
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      mul_one, mul_zero, add_zero, add_sub_cancel_left] at hev
    have hne : ((m + 3 : ℕ) : ℚ) ≠ 0 := by positivity
    have hc0 : c = 0 := (mul_eq_zero.mp hev).resolve_left hne
    rw [hC1, hc0, map_zero]

theorem raabe_bernoulli_eval {M : ℕ} (hM : 0 < M) {m : ℕ} (hm : 1 ≤ m) (x : ℚ) :
    (M : ℚ) ^ (m - 1) * ∑ j ∈ Finset.range M, (Polynomial.bernoulli m).eval ((x + (j : ℚ)) / (M : ℚ)) =
      (Polynomial.bernoulli m).eval x := by
  have h0 := congrArg (Polynomial.eval x) (raabePoly_eq_zero hM hm)
  unfold raabePoly at h0
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finsetSum,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_zero, sub_eq_zero] at h0
  simpa [div_eq_inv_mul] using h0

/-! ### Classical Bernoulli Distribution & Concrete Mazur Regularized Bernoulli Measure `μ_c` -/

section ConcreteMazur

variable (p : ℕ) [Fact p.Prime]

/-- Classical rational Bernoulli distribution `E_m(a, p^n) = (p^n)^(m - 1) * B_m(a.val / p^n)`. -/
def bernoulliDist (m n : ℕ) (a : ZMod (p ^ n)) : ℚ :=
  ((p ^ n : ℕ) : ℚ) ^ (m - 1) * (Polynomial.bernoulli m).eval ((a.val : ℚ) / ((p ^ n : ℕ) : ℚ))

/-- Explicit fiber parameterization of `{b : ZMod (p^(n+1)) | zmodPowStep n b = a}` by `j ∈ range p`. -/
lemma sum_fiber_zmodPowStep {M : Type*} [AddCommMonoid M] (n : ℕ) (a : ZMod (p ^ n))
    (f : ZMod (p ^ (n + 1)) → M) :
    (∑ b ∈ Finset.univ.filter (fun b : ZMod (p ^ (n + 1)) => zmodPowStep (p := p) n b = a), f b) =
      ∑ j ∈ Finset.range p, f (((a.val + j * p ^ n : ℕ) : ZMod (p ^ (n + 1)))) := by
  have hp : p.Prime := Fact.out
  have : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero (n + 1) hp.ne_zero⟩
  have hlt : ∀ j ∈ Finset.range p, a.val + j * p ^ n < p ^ (n + 1) := by
    intro j hj
    have hjlt : j < p := Finset.mem_range.mp hj
    have halt : a.val < p ^ n := ZMod.val_lt a
    rw [pow_succ']
    nlinarith
  symm
  refine Finset.sum_bij (fun j _ => ((a.val + j * p ^ n : ℕ) : ZMod (p ^ (n + 1)))) ?_ ?_ ?_ ?_
  · intro j _
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [zmodPowStep, zmodPowCast, map_natCast, Nat.cast_add, Nat.cast_mul,
      ZMod.natCast_zmod_val, ZMod.natCast_self, mul_zero, add_zero]
  · intro j₁ hj₁ j₂ hj₂ heq
    have hval := congrArg ZMod.val heq
    rw [ZMod.val_natCast_of_lt (hlt j₁ hj₁), ZMod.val_natCast_of_lt (hlt j₂ hj₂)] at hval
    have hmul : j₁ * p ^ n = j₂ * p ^ n := Nat.add_left_cancel hval
    exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos n) hmul
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    have hmod : b.val % p ^ n = a.val := by
      have hcast : ((b.val : ℕ) : ZMod (p ^ n)) = a := by
        rw [← hb, zmodPowStep, zmodPowCast,
          ← map_natCast (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))),
          ZMod.natCast_zmod_val]
      have hv := congrArg ZMod.val hcast
      rwa [ZMod.val_natCast] at hv
    refine ⟨b.val / p ^ n, Finset.mem_range.mpr ?_, ?_⟩
    · have hblt : b.val < p ^ n * p := by
        calc b.val < p ^ (n + 1) := ZMod.val_lt b
          _ = p ^ n * p := pow_succ p n
      exact Nat.div_lt_of_lt_mul hblt
    · have hdiv : a.val + b.val / p ^ n * p ^ n = b.val := by
        rw [← hmod, mul_comm, add_comm]
        exact Nat.div_add_mod b.val (p ^ n)
      rw [hdiv, ZMod.natCast_zmod_val]
  · intro _ _; rfl

/-- Exact distribution law for the `m`-th Bernoulli distribution `E_m` (`m ≥ 1`). -/
theorem bernoulliDist_compat {m : ℕ} (hm : 1 ≤ m) (n : ℕ) (a : ZMod (p ^ n)) :
    bernoulliDist p m n a =
      ∑ b ∈ Finset.univ.filter (fun b : ZMod (p ^ (n + 1)) => zmodPowStep (p := p) n b = a),
        bernoulliDist p m (n + 1) b := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpn0 : ((p ^ n : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero n hp.ne_zero)
  have : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero (n + 1) hp.ne_zero⟩
  rw [sum_fiber_zmodPowStep]
  unfold bernoulliDist
  have harg : ∀ j ∈ Finset.range p,
      ((((a.val + j * p ^ n : ℕ) : ZMod (p ^ (n + 1))).val : ℚ) / ((p ^ (n + 1) : ℕ) : ℚ)) =
        (((a.val : ℚ) / ((p ^ n : ℕ) : ℚ)) + (j : ℚ)) / (p : ℚ) := by
    intro j hj
    have hjlt : j < p := Finset.mem_range.mp hj
    have halt : a.val < p ^ n := ZMod.val_lt a
    have hlt : a.val + j * p ^ n < p ^ (n + 1) := by rw [pow_succ']; nlinarith
    rw [ZMod.val_natCast_of_lt hlt]
    push_cast
    rw [pow_succ]
    field_simp [hp0, hpn0]
  rw [← Finset.mul_sum]
  have hsum_congr :
      ∑ j ∈ Finset.range p, (Polynomial.bernoulli m).eval
        ((((a.val + j * p ^ n : ℕ) : ZMod (p ^ (n + 1))).val : ℚ) / ((p ^ (n + 1) : ℕ) : ℚ)) =
      ∑ j ∈ Finset.range p, (Polynomial.bernoulli m).eval
        ((((a.val : ℚ) / ((p ^ n : ℕ) : ℚ)) + (j : ℚ)) / (p : ℚ)) :=
    Finset.sum_congr rfl fun j hj => by rw [harg j hj]
  rw [hsum_congr]
  have hpow : ((p ^ (n + 1) : ℕ) : ℚ) ^ (m - 1) = ((p ^ n : ℕ) : ℚ) ^ (m - 1) * (p : ℚ) ^ (m - 1) := by
    rw [pow_succ, Nat.cast_mul, mul_pow]
  rw [hpow, mul_assoc, raabe_bernoulli_eval hp.pos hm]

/-- Exact total sum of the `m`-th Bernoulli distribution at any level `n`:
`∑_{a : ZMod (p^n)} E_m(a, p^n) = bernoulli m`. -/
theorem sum_bernoulliDist {m : ℕ} (hm : 1 ≤ m) (n : ℕ) :
    ∑ a : ZMod (p ^ n), bernoulliDist p m n a = bernoulli m := by
  induction n with
  | zero =>
    rw [Finset.sum_eq_single (0 : ZMod (p ^ 0))]
    · unfold bernoulliDist
      simp only [pow_zero, Nat.cast_one, one_pow, one_mul, div_one, ZMod.val_zero, Nat.cast_zero,
        Polynomial.bernoulli_eval_zero]
    · intro a _ ha; exact absurd (zmod_pow_zero_eq a 0) ha
    · intro h; exact absurd (Finset.mem_univ _) h
  | succ n ih =>
    rw [← ih]
    simp_rw [bernoulliDist_compat p hm n]
    symm
    exact Finset.sum_fiberwise_of_maps_to (g := zmodPowStep (p := p) n)
      (f := bernoulliDist p m (n + 1)) (fun _ _ => Finset.mem_univ _)

/-- The unit `(c : ZMod (p ^ n))ˣ` when `¬ p ∣ c`. -/
def cUnit (c : ℕ) (hc : ¬ p ∣ c) (n : ℕ) : (ZMod (p ^ n))ˣ :=
  ZMod.unitOfCoprime c (((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hc).symm.pow_right n)

/-- Multiplicative inverse of `c` in `ZMod (p ^ n)` when `¬ p ∣ c`. -/
def cInv (c : ℕ) (hc : ¬ p ∣ c) (n : ℕ) : ZMod (p ^ n) :=
  ((cUnit p c hc n)⁻¹ : (ZMod (p ^ n))ˣ)

lemma c_mul_cInv (c : ℕ) (hc : ¬ p ∣ c) (n : ℕ) :
    (c : ZMod (p ^ n)) * cInv p c hc n = 1 := by
  have hcoe : ((cUnit p c hc n : (ZMod (p ^ n))ˣ) : ZMod (p ^ n)) = (c : ZMod (p ^ n)) :=
    ZMod.coe_unitOfCoprime c _
  rw [← hcoe, cInv, Units.mul_inv]

lemma cInv_mul_c (c : ℕ) (hc : ¬ p ∣ c) (n : ℕ) :
    cInv p c hc n * (c : ZMod (p ^ n)) = 1 := by
  rw [mul_comm, c_mul_cInv]

lemma zmodPowStep_cInv (c : ℕ) (hc : ¬ p ∣ c) (n : ℕ) :
    zmodPowStep (p := p) n (cInv p c hc (n + 1)) = cInv p c hc n := by
  have h1 : (c : ZMod (p ^ n)) * zmodPowStep (p := p) n (cInv p c hc (n + 1)) = 1 := by
    rw [← map_natCast (zmodPowStep (p := p) n), ← map_mul, c_mul_cInv, map_one]
  calc zmodPowStep (p := p) n (cInv p c hc (n + 1))
      = cInv p c hc n * ((c : ZMod (p ^ n)) * zmodPowStep (p := p) n (cInv p c hc (n + 1))) := by
        rw [← mul_assoc, cInv_mul_c, one_mul]
    _ = cInv p c hc n := by rw [h1, mul_one]

/-- Regularized `m`-th Mazur–Bernoulli distribution in `ℚ`:
`E_{m, c}(a, p^n) = E_m(a, p^n) - c^m * E_m(c⁻¹ a, p^n)`. -/
def mazurBernoulliDist (c : ℕ) (hc : ¬ p ∣ c) (m n : ℕ) (a : ZMod (p ^ n)) : ℚ :=
  bernoulliDist p m n a - (c : ℚ) ^ m * bernoulliDist p m n (cInv p c hc n * a)

/-- Distribution law for `mazurBernoulliDist p c hc m` (`m ≥ 1`). -/
theorem mazurBernoulliDist_compat (c : ℕ) (hc : ¬ p ∣ c) {m : ℕ} (hm : 1 ≤ m)
    (n : ℕ) (a : ZMod (p ^ n)) :
    mazurBernoulliDist p c hc m n a =
      ∑ b ∈ Finset.univ.filter (fun b : ZMod (p ^ (n + 1)) => zmodPowStep (p := p) n b = a),
        mazurBernoulliDist p c hc m (n + 1) b := by
  unfold mazurBernoulliDist
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← bernoulliDist_compat p hm n a]
  congr 2
  rw [bernoulliDist_compat p hm n (cInv p c hc n * a)]
  symm
  refine Finset.sum_bij (fun b _ => cInv p c hc (n + 1) * b) ?_ ?_ ?_ ?_
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    rw [map_mul, zmodPowStep_cInv, hb]
  · intro b₁ _ b₂ _ heq
    calc b₁ = (c : ZMod (p ^ (n + 1))) * (cInv p c hc (n + 1) * b₁) := by
          rw [← mul_assoc, c_mul_cInv, one_mul]
      _ = (c : ZMod (p ^ (n + 1))) * (cInv p c hc (n + 1) * b₂) := by rw [heq]
      _ = b₂ := by rw [← mul_assoc, c_mul_cInv, one_mul]
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    refine ⟨(c : ZMod (p ^ (n + 1))) * y, ?_, by rw [← mul_assoc, cInv_mul_c, one_mul]⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_mul, map_natCast, hy,
      ← mul_assoc, c_mul_cInv, one_mul]
  · intro _ _; rfl

/-- Exact total sum of `mazurBernoulliDist p c hc m` at any level `n`:
`∑_{a : ZMod (p^n)} E_{m, c}(a, p^n) = (1 - c^m) * bernoulli m`. -/
theorem sum_mazurBernoulliDist (c : ℕ) (hc : ¬ p ∣ c) {m : ℕ} (hm : 1 ≤ m) (n : ℕ) :
    ∑ a : ZMod (p ^ n), mazurBernoulliDist p c hc m n a =
      (1 - (c : ℚ) ^ m) * bernoulli m := by
  unfold mazurBernoulliDist
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_bernoulliDist p hm n]
  have hbij : ∑ a : ZMod (p ^ n), bernoulliDist p m n (cInv p c hc n * a) =
      ∑ b : ZMod (p ^ n), bernoulliDist p m n b := by
    refine Finset.sum_bij (fun a _ => cInv p c hc n * a) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro a₁ _ a₂ _ heq
      calc a₁ = (c : ZMod (p ^ n)) * (cInv p c hc n * a₁) := by rw [← mul_assoc, c_mul_cInv, one_mul]
        _ = (c : ZMod (p ^ n)) * (cInv p c hc n * a₂) := by rw [heq]
        _ = a₂ := by rw [← mul_assoc, c_mul_cInv, one_mul]
    · intro b _
      exact ⟨(c : ZMod (p ^ n)) * b, Finset.mem_univ _, by rw [← mul_assoc, cInv_mul_c, one_mul]⟩
    · intro _ _; rfl
  rw [hbij, sum_bernoulliDist p hm n]
  ring

/-- Key Euclidean division identity linking `a.val` and `b = c⁻¹ * a` in `ZMod (p ^ n)`:
`c * b.val = a.val + p^n * (c * b.val / p^n)`. -/
lemma c_mul_cInv_val_eq (c : ℕ) (hc : ¬ p ∣ c) (n : ℕ) (a : ZMod (p ^ n)) :
    c * (cInv p c hc n * a).val = a.val + p ^ n * (c * (cInv p c hc n * a).val / p ^ n) := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  have hcast : ((c * (cInv p c hc n * a).val : ℕ) : ZMod (p ^ n)) = a := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, ← mul_assoc, c_mul_cInv, one_mul]
  have hmod : c * (cInv p c hc n * a).val % p ^ n = a.val := by
    have hv := congrArg ZMod.val hcast
    rwa [ZMod.val_natCast] at hv
  rw [← hmod, add_comm]
  exact (Nat.div_add_mod (c * (cInv p c hc n * a).val) (p ^ n)).symm

/-- **Exact Integer / Half-Integer Formula for Mazur's Regularized Bernoulli Distribution**:
`E_{1, c}(a, p^n) = (c - 1) / 2 - ⌊c * (c⁻¹ a mod p^n) / p^n⌋`! -/
theorem mazurBernoulliDist_one_eq (c : ℕ) (hc : ¬ p ∣ c) (n : ℕ) (a : ZMod (p ^ n)) :
    mazurBernoulliDist p c hc 1 n a =
      ((c : ℚ) - 1) / 2 - ((c * (cInv p c hc n * a).val / p ^ n : ℕ) : ℚ) := by
  have hpn0 : ((p ^ n : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero n (Fact.out : p.Prime).ne_zero)
  unfold mazurBernoulliDist bernoulliDist
  simp only [Nat.sub_self, pow_zero, one_mul, pow_one, Polynomial.bernoulli_one,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hdiv := c_mul_cInv_val_eq p c hc n a
  have hdivQ : (c : ℚ) * ((cInv p c hc n * a).val : ℚ) =
      (a.val : ℚ) + ((p ^ n : ℕ) : ℚ) * ((c * (cInv p c hc n * a).val / p ^ n : ℕ) : ℚ) := by
    exact_mod_cast hdiv
  field_simp [hpn0]
  linarith

/-- When `c` is odd, `E_{1, c}(a, p^n)` is literally an integer in `ℤ`! -/
theorem mazurBernoulliDist_one_eq_int_of_odd (c : ℕ) (hc : ¬ p ∣ c) (hodd : Odd c)
    (n : ℕ) (a : ZMod (p ^ n)) :
    mazurBernoulliDist p c hc 1 n a =
      ((((((c - 1) / 2 : ℕ) : ℤ) - ((c * (cInv p c hc n * a).val / p ^ n : ℕ) : ℤ) : ℤ) : ℚ)) := by
  rw [mazurBernoulliDist_one_eq]
  obtain ⟨k, hk⟩ := hodd
  have hhalf : (((c - 1) / 2 : ℕ) : ℚ) = ((c : ℚ) - 1) / 2 := by
    have hk1 : (c - 1) / 2 = k := by omega
    rw [hk1, hk]
    push_cast
    ring
  rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, hhalf]

lemma padic_norm_nat_le_one (m : ℕ) : ‖(m : ℚ_[p])‖ ≤ 1 := by
  simpa using Padic.norm_int_le_one (p := p) (m : ℤ)

/-- **Unconditional $p$-adic Integrality of Mazur's Regularized Bernoulli Distribution**:
for EVERY prime `p` (including `p = 2`!) and EVERY `c` with `¬ p ∣ c`,
`‖(E_{1, c}(a, p^n) : ℚ_[p])‖ ≤ 1`. -/
theorem norm_mazurBernoulliDist_one_le_one (c : ℕ) (hc : ¬ p ∣ c) (n : ℕ) (a : ZMod (p ^ n)) :
    ‖(mazurBernoulliDist p c hc 1 n a : ℚ_[p])‖ ≤ 1 := by
  have hp : p.Prime := Fact.out
  rcases hp.eq_two_or_odd with rfl | hodd_p
  · have hodd_c : Odd c := Nat.odd_iff.mpr (by omega)
    rw [mazurBernoulliDist_one_eq_int_of_odd 2 c hc hodd_c n a, Rat.cast_intCast]
    exact Padic.norm_int_le_one _
  · rw [mazurBernoulliDist_one_eq p c hc n a]
    push_cast
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_div]
      have h2_norm : ‖(2 : ℚ_[p])‖ = 1 := by
        have hcop : p.Coprime 2 := hp.coprime_iff_not_dvd.mpr fun h => by
          have hle := Nat.le_of_dvd (by decide) h
          have hp2 := hp.two_le
          omega
        exact Padic.norm_natCast_eq_one_iff.mpr hcop
      rw [h2_norm, div_one]
      have hsub_int : ((c : ℚ_[p]) - 1) = (((c : ℤ) - 1 : ℤ) : ℚ_[p]) := by push_cast; rfl
      rw [hsub_int]
      exact Padic.norm_int_le_one _
    · rw [norm_neg]
      exact padic_norm_nat_le_one p _

def mazurBernoulliVal (c : ℕ) (hc : ¬ p ∣ c) (n : ℕ) (a : ZMod (p ^ n)) : ℤ_[p] :=
  ⟨(mazurBernoulliDist p c hc 1 n a : ℚ_[p]), norm_mazurBernoulliDist_one_le_one p c hc n a⟩

/-- **Concrete Mazur Regularized Bernoulli Measure `μ_c` on `ℤ_[p]`** (for any prime `p` and any `c`
with `p ∤ c`). -/
def mazurBernoulliMeasure (c : ℕ) (hc : ¬ p ∣ c) : PadicMeasure p where
  toFun n a := mazurBernoulliVal p c hc n a
  compat n a := by
    apply Subtype.ext
    rw [PadicInt.coe_sum]
    change (mazurBernoulliDist p c hc 1 n a : ℚ_[p]) =
      ∑ b ∈ Finset.univ.filter (fun b : ZMod (p ^ (n + 1)) => zmodPowStep (p := p) n b = a),
        (mazurBernoulliDist p c hc 1 (n + 1) b : ℚ_[p])
    rw [← Rat.cast_sum]
    exact congrArg (Rat.cast : ℚ → ℚ_[p]) (mazurBernoulliDist_compat p c hc le_rfl n a)

lemma mazurBernoulliMeasure_coe (c : ℕ) (hc : ¬ p ∣ c) (n : ℕ) (a : ZMod (p ^ n)) :
    ((mazurBernoulliMeasure p c hc n a : ℤ_[p]) : ℚ_[p]) =
      (mazurBernoulliDist p c hc 1 n a : ℚ_[p]) := rfl

/-! ### Exact $k$-th Moment Identity `∫_{ℤ_[p]} x^k dμ_c = (1 - c^{k+1}) B_{k+1}/(k + 1)` -/

/-- Exact rational expansion of `N^k * B_{k+1}(x / N)` separating the `O(1/N)` and `O(1)` terms
from the `O(N)` remainder. -/
lemma pow_mul_bernoulli_eval_div (k : ℕ) (x : ℚ) {N : ℚ} (hN : N ≠ 0) :
    N ^ k * (Polynomial.bernoulli (k + 1)).eval (x / N) =
      x ^ (k + 1) / N - ((k + 1 : ℕ) : ℚ) / 2 * x ^ k +
      N * ∑ j ∈ Finset.range k,
        bernoulli (j + 2) * (((k + 1).choose (j + 2) : ℕ) : ℚ) * x ^ (k - 1 - j) * N ^ j := by
  unfold Polynomial.bernoulli
  rw [Polynomial.eval_finsetSum, Finset.mul_sum]
  have hterm : ∀ i ∈ Finset.range (k + 2),
      N ^ k * (Polynomial.monomial (k + 1 - i) (bernoulli i * ((k + 1).choose i : ℚ))).eval (x / N) =
        bernoulli i * ((k + 1).choose i : ℚ) * x ^ (k + 1 - i) * N ^ k / N ^ (k + 1 - i) := by
    intro i _
    rw [Polynomial.eval_monomial, div_pow]
    ring
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, bernoulli_zero, one_mul,
    Nat.add_sub_add_right, zero_add, Nat.add_sub_cancel, Nat.choose_one_right, bernoulli_one]
  have h0 : x ^ (k + 1) * N ^ k / N ^ (k + 1) = x ^ (k + 1) / N := by
    rw [pow_succ N k]; field_simp [hN]
  have h1 : (-1 : ℚ) / 2 * ((k + 1 : ℕ) : ℚ) * x ^ k * N ^ k / N ^ k = -(((k + 1 : ℕ) : ℚ) / 2 * x ^ k) := by
    field_simp [hN]
  rw [h0, h1]
  have hrem :
      ∑ j ∈ Finset.range k,
        bernoulli (j + 1 + 1) * (((k + 1).choose (j + 1 + 1) : ℕ) : ℚ) *
          x ^ (k - (j + 1)) * N ^ k / N ^ (k - (j + 1)) =
      N * ∑ j ∈ Finset.range k,
        bernoulli (j + 2) * (((k + 1).choose (j + 2) : ℕ) : ℚ) * x ^ (k - 1 - j) * N ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjlt : j < k := Finset.mem_range.mp hj
    have hsub : k - (j + 1) = k - 1 - j := by omega
    have hpow : N ^ k = N ^ (k - 1 - j) * (N * N ^ j) := by
      rw [← pow_succ', ← pow_add]
      congr 1; omega
    rw [hsub, hpow]
    have hNpow : N ^ (k - 1 - j) ≠ 0 := pow_ne_zero _ hN
    field_simp [hNpow]
  rw [hrem]
  ring

/-- Pointwise $p$-adic error bound comparing `E_{k+1, c}(a, p^n)` with
`(k + 1) * (a.val)^k * E_{1, c}(a, p^n)`: uniform `O(p^{-n})` independent of `n` and `a`! -/
lemma exists_bound_mazurBernoulliDist_sub (c : ℕ) (hc : ¬ p ∣ c) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (a : ZMod (p ^ n)),
      ‖(mazurBernoulliDist p c hc (k + 1) n a -
          ((k + 1 : ℕ) : ℚ) * (a.val : ℚ) ^ k * mazurBernoulliDist p c hc 1 n a : ℚ_[p])‖ ≤
        C * (p : ℝ) ^ (-(n : ℤ)) := by
  let B : ℝ := 1 + ‖(((k + 1 : ℕ) : ℚ) / 2 : ℚ_[p])‖ +
    ∑ j ∈ Finset.range k, ‖(bernoulli (j + 2) : ℚ_[p])‖
  have hB0 : 0 ≤ B := by
    have hsum0 : 0 ≤ ∑ j ∈ Finset.range k, ‖(bernoulli (j + 2) : ℚ_[p])‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have h1 := norm_nonneg (((k + 1 : ℕ) : ℚ) / 2 : ℚ_[p])
    linarith
  have h1_le_B : 1 ≤ B := by
    have hsum0 : 0 ≤ ∑ j ∈ Finset.range k, ‖(bernoulli (j + 2) : ℚ_[p])‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have h1 := norm_nonneg (((k + 1 : ℕ) : ℚ) / 2 : ℚ_[p])
    linarith
  have hhalf_le_B : ‖(((k + 1 : ℕ) : ℚ) / 2 : ℚ_[p])‖ ≤ B := by
    have hsum0 : 0 ≤ ∑ j ∈ Finset.range k, ‖(bernoulli (j + 2) : ℚ_[p])‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  have hbern_le_B : ∀ j ∈ Finset.range k, ‖(bernoulli (j + 2) : ℚ_[p])‖ ≤ B := by
    intro j hj
    have hle : ‖(bernoulli (j + 2) : ℚ_[p])‖ ≤ ∑ i ∈ Finset.range k, ‖(bernoulli (i + 2) : ℚ_[p])‖ :=
      Finset.single_le_sum (f := fun i => ‖(bernoulli (i + 2) : ℚ_[p])‖)
        (fun i _ => norm_nonneg _) hj
    have h1 := norm_nonneg (((k + 1 : ℕ) : ℚ) / 2 : ℚ_[p])
    linarith
  refine ⟨B, hB0, fun n a => ?_⟩
  let N : ℕ := p ^ n
  have hN0 : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero n (Fact.out : p.Prime).ne_zero)
  let b : ZMod (p ^ n) := cInv p c hc n * a
  let q : ℕ := c * b.val / p ^ n
  have hcb : (c : ℚ) * (b.val : ℚ) = (a.val : ℚ) + (N : ℚ) * (q : ℚ) := by
    exact_mod_cast c_mul_cInv_val_eq p c hc n a
  have hEa : bernoulliDist p (k + 1) n a =
      (a.val : ℚ) ^ (k + 1) / (N : ℚ) - ((k + 1 : ℕ) : ℚ) / 2 * (a.val : ℚ) ^ k +
      (N : ℚ) * ∑ j ∈ Finset.range k,
        bernoulli (j + 2) * (((k + 1).choose (j + 2) : ℕ) : ℚ) * (a.val : ℚ) ^ (k - 1 - j) * (N : ℚ) ^ j := by
    unfold bernoulliDist
    simpa [N] using pow_mul_bernoulli_eval_div k (a.val : ℚ) hN0
  have hEb : (c : ℚ) ^ (k + 1) * bernoulliDist p (k + 1) n b =
      ((c : ℚ) * (b.val : ℚ)) ^ (k + 1) / (N : ℚ) -
        ((k + 1 : ℕ) : ℚ) / 2 * (c : ℚ) * ((c : ℚ) * (b.val : ℚ)) ^ k +
      (N : ℚ) * ∑ j ∈ Finset.range k,
        bernoulli (j + 2) * (((k + 1).choose (j + 2) : ℕ) : ℚ) * (c : ℚ) ^ (k + 1) *
          (b.val : ℚ) ^ (k - 1 - j) * (N : ℚ) ^ j := by
    have hEb0 : bernoulliDist p (k + 1) n b =
        (b.val : ℚ) ^ (k + 1) / (N : ℚ) - ((k + 1 : ℕ) : ℚ) / 2 * (b.val : ℚ) ^ k +
        (N : ℚ) * ∑ j ∈ Finset.range k,
          bernoulli (j + 2) * (((k + 1).choose (j + 2) : ℕ) : ℚ) * (b.val : ℚ) ^ (k - 1 - j) * (N : ℚ) ^ j := by
      unfold bernoulliDist
      simpa [N] using pow_mul_bernoulli_eval_div k (b.val : ℚ) hN0
    rw [hEb0, mul_pow, mul_pow, mul_add, mul_sub, mul_left_comm ((c : ℚ) ^ (k + 1)) (N : ℚ), Finset.mul_sum]
    have hpowc : (c : ℚ) ^ (k + 1) = (c : ℚ) * (c : ℚ) ^ k := by rw [pow_succ']
    congr 1
    · rw [hpowc]; ring
    · congr 1
      refine Finset.sum_congr rfl fun j _ => by ring
  have hbin1 : ((a.val : ℚ) + (N : ℚ) * (q : ℚ)) ^ (k + 1) / (N : ℚ) =
      (a.val : ℚ) ^ (k + 1) / (N : ℚ) + ((k + 1 : ℕ) : ℚ) * (a.val : ℚ) ^ k * (q : ℚ) +
      (N : ℚ) * ∑ r ∈ Finset.range k,
        (((k + 1).choose (r + 2) : ℕ) : ℚ) * (a.val : ℚ) ^ (k - 1 - r) * (q : ℚ) ^ (r + 2) * (N : ℚ) ^ r := by
    rw [add_comm (a.val : ℚ), add_pow, Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [Nat.sub_zero, pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one,
      Nat.add_sub_add_right, zero_add, Nat.add_sub_cancel, pow_one, Nat.choose_one_right]
    rw [add_div, add_div, Finset.sum_div, Finset.mul_sum]
    have hmid : (N : ℚ) * (q : ℚ) * (a.val : ℚ) ^ k * ((k + 1 : ℕ) : ℚ) / (N : ℚ) =
        ((k + 1 : ℕ) : ℚ) * (a.val : ℚ) ^ k * (q : ℚ) := by field_simp [hN0]
    rw [hmid]
    have htail :
        ∑ r ∈ Finset.range k,
          ((N : ℚ) * (q : ℚ)) ^ (r + 1 + 1) * (a.val : ℚ) ^ (k - (r + 1)) *
            (((k + 1).choose (r + 1 + 1) : ℕ) : ℚ) / (N : ℚ) =
        ∑ r ∈ Finset.range k,
          (N : ℚ) * ((((k + 1).choose (r + 2) : ℕ) : ℚ) * (a.val : ℚ) ^ (k - 1 - r) *
            (q : ℚ) ^ (r + 2) * (N : ℚ) ^ r) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      have hsub : k - (r + 1) = k - 1 - r := by omega
      rw [hsub, show r + 1 + 1 = r + 2 from rfl, mul_pow, pow_add (N : ℚ) r 2, sq]
      field_simp [hN0]
    rw [htail]
    ring
  have hbin2 : ((a.val : ℚ) + (N : ℚ) * (q : ℚ)) ^ k =
      (a.val : ℚ) ^ k +
      (N : ℚ) * ∑ r ∈ Finset.range k,
        ((k.choose (r + 1) : ℕ) : ℚ) * (a.val : ℚ) ^ (k - 1 - r) * (q : ℚ) ^ (r + 1) * (N : ℚ) ^ r := by
    rw [add_comm (a.val : ℚ), add_pow, Finset.sum_range_succ']
    simp only [Nat.sub_zero, pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one]
    rw [Finset.mul_sum]
    have htail :
        ∑ r ∈ Finset.range k,
          ((N : ℚ) * (q : ℚ)) ^ (r + 1) * (a.val : ℚ) ^ (k - (r + 1)) * ((k.choose (r + 1) : ℕ) : ℚ) =
        ∑ r ∈ Finset.range k,
          (N : ℚ) * (((k.choose (r + 1) : ℕ) : ℚ) * (a.val : ℚ) ^ (k - 1 - r) *
            (q : ℚ) ^ (r + 1) * (N : ℚ) ^ r) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      have hsub : k - (r + 1) = k - 1 - r := by omega
      rw [hsub, mul_pow, pow_succ (N : ℚ) r]
      ring
    rw [htail, add_comm]
  let R1 : ℚ := ∑ j ∈ Finset.range k,
    bernoulli (j + 2) * (((k + 1).choose (j + 2) : ℕ) : ℚ) * (a.val : ℚ) ^ (k - 1 - j) * (N : ℚ) ^ j
  let R2 : ℚ := ∑ j ∈ Finset.range k,
    bernoulli (j + 2) * (((k + 1).choose (j + 2) : ℕ) : ℚ) * (c : ℚ) ^ (k + 1) *
      (b.val : ℚ) ^ (k - 1 - j) * (N : ℚ) ^ j
  let R3 : ℚ := ∑ r ∈ Finset.range k,
    (((k + 1).choose (r + 2) : ℕ) : ℚ) * (a.val : ℚ) ^ (k - 1 - r) * (q : ℚ) ^ (r + 2) * (N : ℚ) ^ r
  let R4 : ℚ := ((k + 1 : ℕ) : ℚ) / 2 * (c : ℚ) * ∑ r ∈ Finset.range k,
    ((k.choose (r + 1) : ℕ) : ℚ) * (a.val : ℚ) ^ (k - 1 - r) * (q : ℚ) ^ (r + 1) * (N : ℚ) ^ r
  have halg : mazurBernoulliDist p c hc (k + 1) n a -
      ((k + 1 : ℕ) : ℚ) * (a.val : ℚ) ^ k * mazurBernoulliDist p c hc 1 n a =
      (N : ℚ) * (R1 - R2 - R3 + R4) := by
    rw [mazurBernoulliDist, hEa, hEb, hcb, hbin1, hbin2, mazurBernoulliDist_one_eq p c hc n a]
    dsimp only [R1, R2, R3, R4, b, q]
    ring
  rw [← Rat.cast_pow, ← Rat.cast_mul, ← Rat.cast_mul, ← Rat.cast_sub, halg, Rat.cast_mul, norm_mul]
  have hnormN : ‖((N : ℚ) : ℚ_[p])‖ = (p : ℝ) ^ (-(n : ℤ)) := by
    rw [Rat.cast_natCast]
    change ‖((p ^ n : ℕ) : ℚ_[p])‖ = _
    rw [Nat.cast_pow, norm_pow, Padic.norm_p, inv_pow, zpow_neg, zpow_natCast]
  rw [hnormN, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have hR1 : ‖(R1 : ℚ_[p])‖ ≤ B := by
    dsimp only [R1]
    rw [Rat.cast_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB0 fun j hj => ?_
    simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, norm_mul]
    have hint : ‖(((k + 1).choose (j + 2) : ℕ) : ℚ_[p]) * (a.val : ℚ_[p]) ^ (k - 1 - j) * (N : ℚ_[p]) ^ j‖ ≤ 1 := by
      have : (((k + 1).choose (j + 2) : ℕ) : ℚ_[p]) * (a.val : ℚ_[p]) ^ (k - 1 - j) * (N : ℚ_[p]) ^ j =
          (((k + 1).choose (j + 2) * a.val ^ (k - 1 - j) * N ^ j : ℕ) : ℚ_[p]) := by push_cast; rfl
      rw [this]; exact padic_norm_nat_le_one p _
    calc ‖(bernoulli (j + 2) : ℚ_[p])‖ * ‖(((k + 1).choose (j + 2) : ℕ) : ℚ_[p])‖ *
          ‖(a.val : ℚ_[p]) ^ (k - 1 - j)‖ * ‖(N : ℚ_[p]) ^ j‖
        = ‖(bernoulli (j + 2) : ℚ_[p])‖ *
          ‖(((k + 1).choose (j + 2) : ℕ) : ℚ_[p]) * (a.val : ℚ_[p]) ^ (k - 1 - j) * (N : ℚ_[p]) ^ j‖ := by
          simp only [norm_mul]; ring
      _ ≤ B * 1 := mul_le_mul (hbern_le_B j hj) hint (norm_nonneg _) hB0
      _ = B := mul_one B
  have hR2 : ‖(R2 : ℚ_[p])‖ ≤ B := by
    dsimp only [R2]
    rw [Rat.cast_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB0 fun j hj => ?_
    simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast]
    have hint : ‖(((k + 1).choose (j + 2) : ℕ) : ℚ_[p]) * (c : ℚ_[p]) ^ (k + 1) *
        (b.val : ℚ_[p]) ^ (k - 1 - j) * (N : ℚ_[p]) ^ j‖ ≤ 1 := by
      have : (((k + 1).choose (j + 2) : ℕ) : ℚ_[p]) * (c : ℚ_[p]) ^ (k + 1) *
          (b.val : ℚ_[p]) ^ (k - 1 - j) * (N : ℚ_[p]) ^ j =
          (((k + 1).choose (j + 2) * c ^ (k + 1) * b.val ^ (k - 1 - j) * N ^ j : ℕ) : ℚ_[p]) := by
        push_cast; rfl
      rw [this]; exact padic_norm_nat_le_one p _
    have hmul : ‖(bernoulli (j + 2) : ℚ_[p]) * (((k + 1).choose (j + 2) : ℕ) : ℚ_[p]) *
          (c : ℚ_[p]) ^ (k + 1) * (b.val : ℚ_[p]) ^ (k - 1 - j) * (N : ℚ_[p]) ^ j‖ =
        ‖(bernoulli (j + 2) : ℚ_[p])‖ *
          ‖(((k + 1).choose (j + 2) : ℕ) : ℚ_[p]) * (c : ℚ_[p]) ^ (k + 1) *
            (b.val : ℚ_[p]) ^ (k - 1 - j) * (N : ℚ_[p]) ^ j‖ := by
      simp only [norm_mul]; ring
    rw [hmul]
    calc ‖(bernoulli (j + 2) : ℚ_[p])‖ * _
        ≤ B * 1 := mul_le_mul (hbern_le_B j hj) hint (norm_nonneg _) hB0
      _ = B := mul_one B
  have hR3 : ‖(R3 : ℚ_[p])‖ ≤ B := by
    dsimp only [R3]
    have hnat : (R3 : ℚ_[p]) = ((∑ r ∈ Finset.range k,
        (k + 1).choose (r + 2) * a.val ^ (k - 1 - r) * q ^ (r + 2) * N ^ r : ℕ) : ℚ_[p]) := by
      dsimp only [R3]; push_cast; rfl
    rw [hnat]
    exact (padic_norm_nat_le_one p _).trans h1_le_B
  have hR4 : ‖(R4 : ℚ_[p])‖ ≤ B := by
    dsimp only [R4]
    have hnatQ : (c : ℚ) * ∑ r ∈ Finset.range k,
        ((k.choose (r + 1) : ℕ) : ℚ) * (a.val : ℚ) ^ (k - 1 - r) * (q : ℚ) ^ (r + 1) * (N : ℚ) ^ r =
        ((c * ∑ r ∈ Finset.range k, k.choose (r + 1) * a.val ^ (k - 1 - r) * q ^ (r + 1) * N ^ r : ℕ) : ℚ) := by
      push_cast; rfl
    have heq : (R4 : ℚ_[p]) = (((k + 1 : ℕ) : ℚ) / 2 : ℚ_[p]) *
        (((c * ∑ r ∈ Finset.range k, k.choose (r + 1) * a.val ^ (k - 1 - r) * q ^ (r + 1) * N ^ r : ℕ) : ℚ) : ℚ_[p]) := by
      rw [← hnatQ]
      dsimp only [R4]
      push_cast; ring
    rw [heq, norm_mul, Rat.cast_natCast]
    calc ‖(((k + 1 : ℕ) : ℚ) / 2 : ℚ_[p])‖ * ‖((c * ∑ r ∈ Finset.range k,
          k.choose (r + 1) * a.val ^ (k - 1 - r) * q ^ (r + 1) * N ^ r : ℕ) : ℚ_[p])‖
        ≤ B * 1 := mul_le_mul hhalf_le_B (padic_norm_nat_le_one p _) (norm_nonneg _) hB0
      _ = B := mul_one B
  simp only [Rat.cast_add, Rat.cast_sub]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hR4)
  rw [sub_eq_add_neg, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (by rwa [norm_neg]))
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hR1 (by rwa [norm_neg]))

/-- **Exact $k$-th Moment Identity for Mazur's Regularized Bernoulli Measure `μ_c`**:
`∫_{ℤ_[p]} x^k dμ_c(x) = (1 - c^{k+1}) * B_{k+1} / (k + 1)` in `ℚ_[p]`! -/
theorem mazurBernoulliMeasure_moment (c : ℕ) (hc : ¬ p ∣ c) (k : ℕ) :
    ((measureIntegral (mazurBernoulliMeasure p c hc) (fun x : ℤ_[p] => x ^ k) : ℤ_[p]) : ℚ_[p]) =
      (((1 - (c : ℚ) ^ (k + 1)) * (bernoulli (k + 1) / ((k + 1 : ℕ) : ℚ)) : ℚ) : ℚ_[p]) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_mazurBernoulliDist_sub p c hc k
  have hp : p.Prime := Fact.out
  have hcont : Continuous (fun x : ℤ_[p] => x ^ k) := continuous_pow k
  have hlim_int : Tendsto (fun n => ((riemannSum (mazurBernoulliMeasure p c hc) (fun x => x ^ k) n : ℤ_[p]) : ℚ_[p]))
      atTop (nhds ((measureIntegral (mazurBernoulliMeasure p c hc) (fun x => x ^ k) : ℤ_[p]) : ℚ_[p])) :=
    (continuous_subtype_val.tendsto _).comp (tendsto_riemannSum_measureIntegral _ hcont)
  have hlim_mul : Tendsto (fun n => (((k + 1 : ℕ) : ℚ_[p]) *
      ((riemannSum (mazurBernoulliMeasure p c hc) (fun x => x ^ k) n : ℤ_[p]) : ℚ_[p])))
      atTop (nhds (((k + 1 : ℕ) : ℚ_[p]) *
        ((measureIntegral (mazurBernoulliMeasure p c hc) (fun x => x ^ k) : ℤ_[p]) : ℚ_[p]))) :=
    tendsto_const_nhds.mul hlim_int
  have hlim_target : Tendsto (fun n => (((k + 1 : ℕ) : ℚ_[p]) *
      ((riemannSum (mazurBernoulliMeasure p c hc) (fun x => x ^ k) n : ℤ_[p]) : ℚ_[p])))
      atTop (nhds ((((1 - (c : ℚ) ^ (k + 1)) * bernoulli (k + 1) : ℚ) : ℚ_[p]))) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hpow_zero : Tendsto (fun n : ℕ => C * (p : ℝ) ^ (-(n : ℤ))) atTop (nhds 0) := by
      have hinv : Tendsto (fun n : ℕ => ((p : ℝ)⁻¹) ^ n) atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
          (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt))
      simpa [inv_pow, zpow_neg, zpow_natCast] using hinv.const_mul C
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hpow_zero.eventually (gt_mem_nhds hε))
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm, ← norm_neg, neg_sub]
    have hsum_eq : (((1 - (c : ℚ) ^ (k + 1)) * bernoulli (k + 1) : ℚ) : ℚ_[p]) -
        ((k + 1 : ℕ) : ℚ_[p]) *
          ((riemannSum (mazurBernoulliMeasure p c hc) (fun x => x ^ k) n : ℤ_[p]) : ℚ_[p]) =
        ∑ a : ZMod (p ^ n),
          ((mazurBernoulliDist p c hc (k + 1) n a -
            ((k + 1 : ℕ) : ℚ) * (a.val : ℚ) ^ k * mazurBernoulliDist p c hc 1 n a : ℚ) : ℚ_[p]) := by
      rw [← sum_mazurBernoulliDist p c hc (Nat.succ_pos k) n]
      unfold riemannSum
      simp only [PadicInt.coe_sum, PadicInt.coe_mul, PadicInt.coe_pow, PadicInt.coe_natCast,
        mazurBernoulliMeasure_coe, Finset.mul_sum, Rat.cast_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      push_cast; ring
    rw [hsum_eq]
    have hbd : ‖∑ a : ZMod (p ^ n),
        ((mazurBernoulliDist p c hc (k + 1) n a -
          ((k + 1 : ℕ) : ℚ) * (a.val : ℚ) ^ k * mazurBernoulliDist p c hc 1 n a : ℚ) : ℚ_[p])‖ ≤
        C * (p : ℝ) ^ (-(n : ℤ)) :=
      IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun a _ => hC n a
    exact hbd.trans_lt (hN n hn)
  have heq : ((k + 1 : ℕ) : ℚ_[p]) *
      ((measureIntegral (mazurBernoulliMeasure p c hc) (fun x => x ^ k) : ℤ_[p]) : ℚ_[p]) =
      (((1 - (c : ℚ) ^ (k + 1)) * bernoulli (k + 1) : ℚ) : ℚ_[p]) :=
    tendsto_nhds_unique hlim_mul hlim_target
  have hk1 : ((k + 1 : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
  calc ((measureIntegral (mazurBernoulliMeasure p c hc) (fun x => x ^ k) : ℤ_[p]) : ℚ_[p])
      = (((1 - (c : ℚ) ^ (k + 1)) * bernoulli (k + 1) : ℚ) : ℚ_[p]) / ((k + 1 : ℕ) : ℚ_[p]) :=
        eq_div_of_mul_eq hk1 (by rw [mul_comm]; exact heq)
    _ = (((1 - (c : ℚ) ^ (k + 1)) * (bernoulli (k + 1) / ((k + 1 : ℕ) : ℚ)) : ℚ) : ℚ_[p]) := by
        push_cast; ring

/-! ### Self-Similarity under Multiplication by `p` & Unit-Restricted Euler Factor `(1 - p^k)` -/

/-- Exact self-similarity of Mazur's measure under `p`: `μ_c (n + 1) (p * a) = μ_c n a`. -/
theorem mazurBernoulliMeasure_mul_p (c : ℕ) (hc : ¬ p ∣ c) (n : ℕ) (a : ZMod (p ^ n)) :
    mazurBernoulliMeasure p c hc (n + 1) ((p * a.val : ℕ) : ZMod (p ^ (n + 1))) =
      mazurBernoulliMeasure p c hc n a := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hpn0 : ((p ^ n : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero n hp.ne_zero)
  have : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero (n + 1) hp.ne_zero⟩
  apply Subtype.ext
  simp only [mazurBernoulliMeasure_coe]
  congr 1
  unfold mazurBernoulliDist bernoulliDist
  simp only [Nat.sub_self, pow_zero, one_mul, pow_one]
  have halt : p * a.val < p ^ (n + 1) := by
    rw [pow_succ']
    exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt a) hp.pos
  have hval1 : (((p * a.val : ℕ) : ZMod (p ^ (n + 1))).val : ℚ) / ((p ^ (n + 1) : ℕ) : ℚ) =
      (a.val : ℚ) / ((p ^ n : ℕ) : ℚ) := by
    rw [ZMod.val_natCast_of_lt halt, pow_succ']
    push_cast
    field_simp [hp0, hpn0]
  have hb_eq : cInv p c hc (n + 1) * ((p * a.val : ℕ) : ZMod (p ^ (n + 1))) =
      ((p * (cInv p c hc n * a).val : ℕ) : ZMod (p ^ (n + 1))) := by
    have hmul : (c : ZMod (p ^ (n + 1))) *
        ((p * (cInv p c hc n * a).val : ℕ) : ZMod (p ^ (n + 1))) =
        ((p * a.val : ℕ) : ZMod (p ^ (n + 1))) := by
      have hdiv := c_mul_cInv_val_eq p c hc n a
      have hmul_p : c * (p * (cInv p c hc n * a).val) =
          p * a.val + p ^ (n + 1) * (c * (cInv p c hc n * a).val / p ^ n) := by
        rw [pow_succ']
        nlinarith
      have hcast : ((c * (p * (cInv p c hc n * a).val) : ℕ) : ZMod (p ^ (n + 1))) =
          ((p * a.val : ℕ) : ZMod (p ^ (n + 1))) := by
        rw [hmul_p, Nat.cast_add, Nat.cast_mul (p ^ (n + 1)), ZMod.natCast_self, zero_mul, add_zero]
      simpa [Nat.cast_mul] using hcast
    calc cInv p c hc (n + 1) * ((p * a.val : ℕ) : ZMod (p ^ (n + 1)))
        = cInv p c hc (n + 1) * ((c : ZMod (p ^ (n + 1))) *
            ((p * (cInv p c hc n * a).val : ℕ) : ZMod (p ^ (n + 1)))) := by rw [hmul]
      _ = ((p * (cInv p c hc n * a).val : ℕ) : ZMod (p ^ (n + 1))) := by
            rw [← mul_assoc, cInv_mul_c, one_mul]
  have hblt : p * (cInv p c hc n * a).val < p ^ (n + 1) := by
    rw [pow_succ']
    exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt _) hp.pos
  have hval2 : ((cInv p c hc (n + 1) * ((p * a.val : ℕ) : ZMod (p ^ (n + 1)))).val : ℚ) /
      ((p ^ (n + 1) : ℕ) : ℚ) =
      ((cInv p c hc n * a).val : ℚ) / ((p ^ n : ℕ) : ℚ) := by
    rw [hb_eq, ZMod.val_natCast_of_lt hblt, pow_succ']
    push_cast
    field_simp [hp0, hpn0]
  rw [hval1, hval2]

/-- Integral of any continuous function over `p ℤ_[p]` against `μ_c` equals `∫ f(p x) dμ_c(x)`. -/
theorem measureIntegral_mazur_nonUnits (c : ℕ) (hc : ¬ p ∣ c) {f : ℤ_[p] → ℤ_[p]}
    (hf : Continuous f) :
    measureIntegral (mazurBernoulliMeasure p c hc) (fun x => (1 - unitIndicator x) * f x) =
      measureIntegral (mazurBernoulliMeasure p c hc) (fun x => f ((p : ℤ_[p]) * x)) := by
  have hp : p.Prime := Fact.out
  have hcontL : Continuous (fun x : ℤ_[p] => (1 - unitIndicator x) * f x) :=
    (continuous_const.sub continuous_unitIndicator).mul hf
  have hcontR : Continuous (fun x : ℤ_[p] => f ((p : ℤ_[p]) * x)) :=
    hf.comp (continuous_const.mul continuous_id)
  have hlimL := (tendsto_riemannSum_measureIntegral (mazurBernoulliMeasure p c hc) hcontL).comp
    (tendsto_add_atTop_nat 1)
  have hlimR := tendsto_riemannSum_measureIntegral (mazurBernoulliMeasure p c hc) hcontR
  have heq_seq : ∀ n : ℕ,
      riemannSum (mazurBernoulliMeasure p c hc) (fun x => (1 - unitIndicator x) * f x) (n + 1) =
        riemannSum (mazurBernoulliMeasure p c hc) (fun x => f ((p : ℤ_[p]) * x)) n := by
    intro n
    have : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
    have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero (n + 1) hp.ne_zero⟩
    unfold riemannSum
    have hfilt : ∑ b : ZMod (p ^ (n + 1)),
        (1 - unitIndicator (b.val : ℤ_[p])) * f (b.val : ℤ_[p]) *
          mazurBernoulliMeasure p c hc (n + 1) b =
        ∑ b ∈ Finset.univ.filter (fun b : ZMod (p ^ (n + 1)) => p ∣ b.val),
          f (b.val : ℤ_[p]) * mazurBernoulliMeasure p c hc (n + 1) b := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun b : ZMod (p ^ (n + 1)) => p ∣ b.val)]
      have h1 : ∀ b ∈ Finset.univ.filter (fun b : ZMod (p ^ (n + 1)) => p ∣ b.val),
          (1 - unitIndicator (b.val : ℤ_[p])) * f (b.val : ℤ_[p]) *
            mazurBernoulliMeasure p c hc (n + 1) b =
          f (b.val : ℤ_[p]) * mazurBernoulliMeasure p c hc (n + 1) b := by
        intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        have h0 : PadicInt.toZMod (b.val : ℤ_[p]) = 0 := by
          rw [map_natCast, ZMod.natCast_eq_zero_iff]; exact hb
        rw [unitIndicator, if_neg (not_not.mpr h0), sub_zero, one_mul]
      have h2 : ∑ b ∈ Finset.univ.filter (fun b : ZMod (p ^ (n + 1)) => ¬ p ∣ b.val),
          (1 - unitIndicator (b.val : ℤ_[p])) * f (b.val : ℤ_[p]) *
            mazurBernoulliMeasure p c hc (n + 1) b = 0 := by
        refine Finset.sum_eq_zero fun b hb => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        have hne : PadicInt.toZMod (b.val : ℤ_[p]) ≠ 0 := by
          rw [map_natCast, Ne, ZMod.natCast_eq_zero_iff]; exact hb
        rw [unitIndicator, if_pos hne, sub_self, zero_mul, zero_mul]
      rw [Finset.sum_congr rfl h1, h2, add_zero]
    rw [hfilt]
    symm
    refine Finset.sum_bij (fun (a : ZMod (p ^ n)) _ => ((p * a.val : ℕ) : ZMod (p ^ (n + 1)))) ?_ ?_ ?_ ?_
    · intro a _
      have halt : p * a.val < p ^ (n + 1) := by
        rw [pow_succ']; exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt a) hp.pos
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, ZMod.val_natCast_of_lt halt]
      exact dvd_mul_right p a.val
    · intro a₁ _ a₂ _ heq
      have hlt1 : p * a₁.val < p ^ (n + 1) := by
        rw [pow_succ']; exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt a₁) hp.pos
      have hlt2 : p * a₂.val < p ^ (n + 1) := by
        rw [pow_succ']; exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt a₂) hp.pos
      have hv := congrArg ZMod.val heq
      rw [ZMod.val_natCast_of_lt hlt1, ZMod.val_natCast_of_lt hlt2] at hv
      have hva : a₁.val = a₂.val := Nat.eq_of_mul_eq_mul_left hp.pos hv
      rw [← ZMod.natCast_zmod_val a₁, ← ZMod.natCast_zmod_val a₂, hva]
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      obtain ⟨k, hk⟩ := hb
      have hklt : k < p ^ n := by
        have hblt : b.val < p ^ (n + 1) := ZMod.val_lt b
        rw [hk, pow_succ'] at hblt
        exact Nat.lt_of_mul_lt_mul_left hblt
      refine ⟨(k : ZMod (p ^ n)), Finset.mem_univ _, ?_⟩
      rw [ZMod.val_natCast_of_lt hklt, ← hk, ZMod.natCast_zmod_val]
    · intro a _
      have halt : p * a.val < p ^ (n + 1) := by
        rw [pow_succ']; exact Nat.mul_lt_mul_of_pos_left (ZMod.val_lt a) hp.pos
      rw [ZMod.val_natCast_of_lt halt, mazurBernoulliMeasure_mul_p, Nat.cast_mul]
  exact tendsto_nhds_unique (hlimL.congr heq_seq) hlimR

/-- **Euler Factor at `p` for Mazur's Regularized Bernoulli Measure**:
`∫_{ℤ_[p]ˣ} x^k dμ_c = (1 - p^k) * ∫_{ℤ_[p]} x^k dμ_c`. -/
theorem measureIntegral_mazur_restrictUnits_pow (c : ℕ) (hc : ¬ p ∣ c) (k : ℕ) :
    measureIntegral (mazurBernoulliMeasure p c hc).restrictUnits (fun x : ℤ_[p] => x ^ k) =
      (1 - (p : ℤ_[p]) ^ k) *
        measureIntegral (mazurBernoulliMeasure p c hc) (fun x : ℤ_[p] => x ^ k) := by
  have hcont : Continuous (fun x : ℤ_[p] => x ^ k) := continuous_pow k
  have hcont2 : Continuous (fun x : ℤ_[p] => (1 - unitIndicator x) * x ^ k) :=
    (continuous_const.sub continuous_unitIndicator).mul hcont
  rw [measureIntegral_restrictUnits _ hcont]
  have hsplit : (fun x : ℤ_[p] => unitIndicator x * x ^ k) =
      fun x : ℤ_[p] => x ^ k - (1 - unitIndicator x) * x ^ k := by
    ext x; ring
  rw [hsplit, measureIntegral_sub_fun _ hcont hcont2,
    measureIntegral_mazur_nonUnits p c hc hcont]
  have hpow : (fun x : ℤ_[p] => ((p : ℤ_[p]) * x) ^ k) = fun x : ℤ_[p] => (p : ℤ_[p]) ^ k * x ^ k := by
    ext x; exact mul_pow _ _ k
  rw [hpow, measureIntegral_smul_fun _ ((p : ℤ_[p]) ^ k) hcont]
  ring

/-- **Exact Unit-Restricted $k$-th Moment Identity**:
`∫_{ℤ_[p]ˣ} x^k dμ_c = (1 - p^k)(1 - c^{k+1}) B_{k+1} / (k + 1)` in `ℚ_[p]`! -/
theorem mazurBernoulliMeasure_restrictUnits_moment (c : ℕ) (hc : ¬ p ∣ c) (k : ℕ) :
    ((measureIntegral (mazurBernoulliMeasure p c hc).restrictUnits (fun x : ℤ_[p] => x ^ k) : ℤ_[p]) : ℚ_[p]) =
      (((1 - (p : ℚ) ^ k) * (1 - (c : ℚ) ^ (k + 1)) *
        (bernoulli (k + 1) / ((k + 1 : ℕ) : ℚ)) : ℚ) : ℚ_[p]) := by
  rw [measureIntegral_mazur_restrictUnits_pow p c hc k, PadicInt.coe_mul, PadicInt.coe_sub,
    PadicInt.coe_one, PadicInt.coe_pow, PadicInt.coe_natCast, mazurBernoulliMeasure_moment p c hc k]
  push_cast
  ring

end ConcreteMazur

end MazurBernoulliMeasure

/-! ## Section 4: Unconditional Kummer's Congruences & Concrete Kubota–Leopoldt $p$-adic Zeta -/

section KummerAndKubotaLeopoldt

/-! ### Fermat–Euler Congruence on `ℤ_[p]ˣ` & Primitive Roots -/

/-- Direct link to `Stage2DworkExp.padic_pow_prime_sub_le` in `ℤ_[p]`:
every `x : ℤ_[p]` satisfies `‖x ^ p - x‖ ≤ p⁻¹`. -/
theorem padicInt_pow_prime_sub_norm_le {p : ℕ} [Fact p.Prime] (x : ℤ_[p]) :
    ‖x ^ p - x‖ ≤ (p : ℝ) ^ (-(1 : ℤ)) := by
  have h := padic_pow_prime_sub_le p (c := (x : ℚ_[p])) (PadicInt.norm_le_one x)
  rw [Padic.norm_p, ← zpow_neg_one] at h
  exact h

/-- **Fermat–Euler Congruence on `ℤ_[p]ˣ`**:
for every prime `p`, every `m ≥ 1`, every unit `x ∈ ℤ_[p]ˣ` (`toZMod x ≠ 0`), and all `k, k' : ℕ`
with `k ≡ k' [MOD (p - 1) * p ^ (m - 1)]`, we have `x ^ k' ≡ x ^ k [mod p ^ m]`. -/
theorem padicInt_pow_sub_norm_le_of_modEq {p : ℕ} [Fact p.Prime] {m k k' : ℕ} (hm : 1 ≤ m)
    {x : ℤ_[p]} (hx : PadicInt.toZMod x ≠ 0)
    (hcong : k ≡ k' [MOD (p - 1) * p ^ (m - 1)]) :
    ‖x ^ k' - x ^ k‖ ≤ (p : ℝ) ^ (-(m : ℤ)) := by
  have hp : p.Prime := Fact.out
  have hunit : IsUnit (PadicInt.toZModPow m x) :=
    (padicInt_isUnit_of_toZMod_ne_zero hx).map (PadicInt.toZModPow m)
  obtain ⟨u, hu⟩ := hunit
  have hcard : Fintype.card (ZMod (p ^ m))ˣ = (p - 1) * p ^ (m - 1) := by
    have : NeZero (p ^ m) := ⟨pow_ne_zero m hp.ne_zero⟩
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow hp hm, mul_comm]
  have hpow1 : (PadicInt.toZModPow m x) ^ ((p - 1) * p ^ (m - 1)) = 1 := by
    rw [← hu, ← Units.val_pow_eq_pow_val, ← hcard, pow_card_eq_one, Units.val_one]
  have hmod_eq : PadicInt.toZModPow m (x ^ k') = PadicInt.toZModPow m (x ^ k) := by
    rw [map_pow, map_pow]
    rcases le_total k k' with hle | hle
    · have hdvd : (p - 1) * p ^ (m - 1) ∣ k' - k :=
        (Nat.modEq_iff_dvd' hle).mp hcong
      obtain ⟨q, hq⟩ := hdvd
      have hk' : k' = k + (p - 1) * p ^ (m - 1) * q := by omega
      rw [hk', pow_add, pow_mul, hpow1, one_pow, mul_one]
    · have hdvd : (p - 1) * p ^ (m - 1) ∣ k - k' :=
        (Nat.modEq_iff_dvd' hle).mp hcong.symm
      obtain ⟨q, hq⟩ := hdvd
      have hk : k = k' + (p - 1) * p ^ (m - 1) * q := by omega
      rw [hk, pow_add, pow_mul, hpow1, one_pow, mul_one]
  exact padicInt_norm_le_pow_of_toZModPow_eq hmod_eq

/-- For any odd prime `p`, there exists `c : ℕ` with `2 ≤ c < p` (so `¬ p ∣ c`) such that for EVERY
`r : ℕ` with `¬ (p - 1) ∣ r`, `1 - c ^ r` is a unit in `ℤ_[p]` (norm `= 1`). -/
theorem exists_primitive_root_padic (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ c : ℕ, 2 ≤ c ∧ ¬ p ∣ c ∧
      ∀ r : ℕ, ¬ (p - 1) ∣ r →
        IsUnit (1 - (c : ℤ_[p]) ^ r) ∧ ‖((1 - (c : ℚ) ^ r : ℚ) : ℚ_[p])‖ = 1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  let c : ℕ := ((g : ZMod p)).val
  have hc_lt : c < p := ZMod.val_lt _
  have hc_ne0 : c ≠ 0 := by
    intro h0
    have hg0 : (g : ZMod p) = 0 := by
      rw [← ZMod.natCast_zmod_val (g : ZMod p)]
      change (c : ZMod p) = 0
      rw [h0, Nat.cast_zero]
    exact g.ne_zero hg0
  have hc_ne1 : c ≠ 1 := by
    intro h1
    have hg1 : g = 1 := by
      apply Units.ext
      rw [← ZMod.natCast_zmod_val (g : ZMod p)]
      change (c : ZMod p) = 1
      rw [h1, Nat.cast_one]
    rw [hg1, orderOf_one] at hord
    have := hp.two_le
    omega
  have hc2 : 2 ≤ c := by omega
  have hndvd : ¬ p ∣ c := Nat.not_dvd_of_pos_of_lt (by omega) hc_lt
  refine ⟨c, hc2, hndvd, fun r hr => ?_⟩
  have hgr_ne1 : g ^ r ≠ 1 := by
    intro h1
    exact hr (hord ▸ orderOf_dvd_of_pow_eq_one h1)
  have hcr_ne1 : (c : ZMod p) ^ r ≠ 1 := by
    intro h1
    apply hgr_ne1
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    have hgc : (g : ZMod p) = (c : ZMod p) := (ZMod.natCast_zmod_val (g : ZMod p)).symm
    rw [hgc, h1]
  have hres_ne0 : PadicInt.toZMod (1 - (c : ℤ_[p]) ^ r) ≠ 0 := by
    rw [map_sub, map_one, map_pow, map_natCast, sub_ne_zero]
    exact hcr_ne1.symm
  have hunit : IsUnit (1 - (c : ℤ_[p]) ^ r) := padicInt_isUnit_of_toZMod_ne_zero hres_ne0
  have hnorm1 : ‖((1 - (c : ℚ) ^ r : ℚ) : ℚ_[p])‖ = 1 := by
    have hcoe : ((1 - (c : ℤ_[p]) ^ r : ℤ_[p]) : ℚ_[p]) = ((1 - (c : ℚ) ^ r : ℚ) : ℚ_[p]) := by
      push_cast; rfl
    rw [← hcoe]
    exact (PadicInt.isUnit_iff.mp hunit)
  exact ⟨hunit, hnorm1⟩

/-! ### Unconditional Adams / von Staudt–Clausen $p$-Integrality & Kummer's Congruences -/

/-- **Adams / von Staudt–Clausen $p$-Integrality of `(1 - p^k) B_{k+1}/(k + 1)` and `B_{k+1}/(k + 1)`**:
for every odd prime `p` and every `k ≥ 1` with `(p - 1) ∤ (k + 1)`, both
`(1 - p^k) * bernoulli (k + 1) / (k + 1)` and `bernoulli (k + 1) / (k + 1)` are `p`-adic integers! -/
theorem bernoulli_div_norm_le_one (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {k : ℕ} (hk : 1 ≤ k) (hndvd : ¬ (p - 1) ∣ (k + 1)) :
    ‖(((1 - (p : ℚ) ^ k) * (bernoulli (k + 1) / ((k + 1 : ℕ) : ℚ)) : ℚ) : ℚ_[p])‖ ≤ 1 ∧
      ‖((bernoulli (k + 1) / ((k + 1 : ℕ) : ℚ) : ℚ) : ℚ_[p])‖ ≤ 1 := by
  obtain ⟨c, _, hc, hprim⟩ := exists_primitive_root_padic p hp2
  obtain ⟨_, hc_norm⟩ := hprim (k + 1) hndvd
  have hmom := mazurBernoulliMeasure_restrictUnits_moment p c hc k
  have hprod_le : ‖(((1 - (c : ℚ) ^ (k + 1)) : ℚ) : ℚ_[p]) *
      (((1 - (p : ℚ) ^ k) * (bernoulli (k + 1) / ((k + 1 : ℕ) : ℚ)) : ℚ) : ℚ_[p])‖ ≤ 1 := by
    have hrearr : (((1 - (c : ℚ) ^ (k + 1)) : ℚ) : ℚ_[p]) *
        (((1 - (p : ℚ) ^ k) * (bernoulli (k + 1) / ((k + 1 : ℕ) : ℚ)) : ℚ) : ℚ_[p]) =
        (((1 - (p : ℚ) ^ k) * (1 - (c : ℚ) ^ (k + 1)) *
          (bernoulli (k + 1) / ((k + 1 : ℕ) : ℚ)) : ℚ) : ℚ_[p]) := by
      push_cast; ring
    rw [hrearr, ← hmom]
    exact PadicInt.norm_le_one _
  rw [norm_mul, hc_norm, one_mul] at hprod_le
  have hp_unit : ‖(((1 - (p : ℚ) ^ k) : ℚ) : ℚ_[p])‖ = 1 := by
    have hres : PadicInt.toZMod (1 - (p : ℤ_[p]) ^ k) ≠ 0 := by
      rw [map_sub, map_one, map_pow, map_natCast, ZMod.natCast_self, zero_pow (by omega), sub_zero]
      exact one_ne_zero
    have hu := PadicInt.isUnit_iff.mp (padicInt_isUnit_of_toZMod_ne_zero hres)
    have hcoe : ((1 - (p : ℤ_[p]) ^ k : ℤ_[p]) : ℚ_[p]) = (((1 - (p : ℚ) ^ k) : ℚ) : ℚ_[p]) := by
      push_cast; rfl
    rwa [← hcoe]
  have hB_le : ‖((bernoulli (k + 1) / ((k + 1 : ℕ) : ℚ) : ℚ) : ℚ_[p])‖ ≤ 1 := by
    have hmul : ‖(((1 - (p : ℚ) ^ k) : ℚ) : ℚ_[p])‖ *
        ‖((bernoulli (k + 1) / ((k + 1 : ℕ) : ℚ) : ℚ) : ℚ_[p])‖ ≤ 1 := by
      rw [← norm_mul, ← Rat.cast_mul]
      exact hprod_le
    rwa [hp_unit, one_mul] at hmul
  exact ⟨hprod_le, hB_le⟩

/-- The `p`-adic integer `(1 - p^k) * bernoulli (k + 1) / (k + 1) ∈ ℤ_[p]` for odd prime `p`,
`k ≥ 1`, and `(p - 1) ∤ (k + 1)`. -/
def kummerBernoulliInt (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {k : ℕ} (hk : 1 ≤ k) (hndvd : ¬ (p - 1) ∣ (k + 1)) : ℤ_[p] :=
  ⟨(((1 - (p : ℚ) ^ k) * (bernoulli (k + 1) / ((k + 1 : ℕ) : ℚ)) : ℚ) : ℚ_[p]),
    (bernoulli_div_norm_le_one p hp2 hk hndvd).1⟩

/-- **KUMMER'S CONGRUENCES FOR BERNOULLI NUMBERS (COMPLETELY UNCONDITIONAL, 0 ASSUMPTIONS!)**:
For EVERY odd prime `p` (`p ≠ 2`), EVERY `m ≥ 1`, EVERY `k, k' ≥ 1` with `(p - 1) ∤ (k + 1)` and
`k ≡ k' [MOD (p - 1) * p ^ (m - 1)]`:
`‖(1 - p^k) B_{k+1}/(k + 1) - (1 - p^{k'}) B_{k'+1}/(k' + 1)‖_p ≤ p^{-m}`! -/
theorem kummer_congruence_bernoulli (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {m k k' : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (_hk' : 1 ≤ k')
    (hndvd : ¬ (p - 1) ∣ (k + 1))
    (hcong : k ≡ k' [MOD (p - 1) * p ^ (m - 1)]) :
    ‖(((1 - (p : ℚ) ^ k) * (bernoulli (k + 1) / ((k + 1 : ℕ) : ℚ)) : ℚ) : ℚ_[p]) -
      (((1 - (p : ℚ) ^ k') * (bernoulli (k' + 1) / ((k' + 1 : ℕ) : ℚ)) : ℚ) : ℚ_[p])‖ ≤
      (p : ℝ) ^ (-(m : ℤ)) := by
  have hp : p.Prime := Fact.out
  have hndvd' : ¬ (p - 1) ∣ (k' + 1) := by
    have hmod1 : k ≡ k' [MOD (p - 1)] := hcong.of_dvd (dvd_mul_right (p - 1) (p ^ (m - 1)))
    have hmod2 : k + 1 ≡ k' + 1 [MOD (p - 1)] := hmod1.add_right 1
    intro hdvd'
    apply hndvd
    exact (Nat.ModEq.dvd_iff hmod2 dvd_rfl).mpr hdvd'
  obtain ⟨c, _, hc, hprim⟩ := exists_primitive_root_padic p hp2
  obtain ⟨_, huc'_norm⟩ := hprim (k' + 1) hndvd'
  set L := (((1 - (p : ℚ) ^ k) * (bernoulli (k + 1) / ((k + 1 : ℕ) : ℚ)) : ℚ) : ℚ_[p])
  set L' := (((1 - (p : ℚ) ^ k') * (bernoulli (k' + 1) / ((k' + 1 : ℕ) : ℚ)) : ℚ) : ℚ_[p])
  set u := (((1 - (c : ℚ) ^ (k + 1)) : ℚ) : ℚ_[p])
  set u' := (((1 - (c : ℚ) ^ (k' + 1)) : ℚ) : ℚ_[p])
  have hL_le1 : ‖L‖ ≤ 1 := (bernoulli_div_norm_le_one p hp2 hk hndvd).1
  have huL : u * L =
      ((measureIntegral (mazurBernoulliMeasure p c hc).restrictUnits (fun x : ℤ_[p] => x ^ k) : ℤ_[p]) : ℚ_[p]) := by
    rw [mazurBernoulliMeasure_restrictUnits_moment p c hc k]
    dsimp only [u, L]; push_cast; ring
  have hu'L' : u' * L' =
      ((measureIntegral (mazurBernoulliMeasure p c hc).restrictUnits (fun x : ℤ_[p] => x ^ k') : ℤ_[p]) : ℚ_[p]) := by
    rw [mazurBernoulliMeasure_restrictUnits_moment p c hc k']
    dsimp only [u', L']; push_cast; ring
  -- Integral congruence from Fermat–Euler on ℤ_[p]ˣ:
  have hint_cong : ‖u' * L' - u * L‖ ≤ (p : ℝ) ^ (-(m : ℤ)) := by
    rw [hu'L', huL, ← PadicInt.coe_sub]
    exact norm_measureIntegral_restrictUnits_sub_le (mazurBernoulliMeasure p c hc)
      (continuous_pow k') (continuous_pow k) (by positivity)
      (fun x hx => padicInt_pow_sub_norm_le_of_modEq hm hx hcong)
  -- Congruence of regularizing factor u' - u = c^(k+1) - c^(k'+1) mod p^m:
  have hu_cong : ‖u' - u‖ ≤ (p : ℝ) ^ (-(m : ℤ)) := by
    have hc_unit : PadicInt.toZMod (c : ℤ_[p]) ≠ 0 := by
      rw [map_natCast, Ne, ZMod.natCast_eq_zero_iff]; exact hc
    have hfe := padicInt_pow_sub_norm_le_of_modEq hm hc_unit (hcong.add_right 1)
    have hcoe : (((c : ℤ_[p]) ^ (k' + 1) - (c : ℤ_[p]) ^ (k + 1) : ℤ_[p]) : ℚ_[p]) = -(u' - u) := by
      dsimp only [u, u']; push_cast; ring
    rw [← norm_neg, ← hcoe]
    exact hfe
  -- Combine via u' * (L' - L) = (u' * L' - u * L) - (u' - u) * L!
  have hdecomp : u' * (L' - L) = (u' * L' - u * L) - (u' - u) * L := by ring
  have hprod_bd : ‖u' * (L' - L)‖ ≤ (p : ℝ) ^ (-(m : ℤ)) := by
    rw [hdecomp, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hint_cong ?_)
    rw [norm_neg, norm_mul]
    calc ‖u' - u‖ * ‖L‖ ≤ (p : ℝ) ^ (-(m : ℤ)) * 1 :=
          mul_le_mul hu_cong hL_le1 (norm_nonneg _) (by positivity)
      _ = (p : ℝ) ^ (-(m : ℤ)) := mul_one _
  rw [norm_mul, huc'_norm, one_mul] at hprod_bd
  rwa [← norm_neg, neg_sub]

/-- **Kummer's Congruence in `ℤ_[p]` (`ZMod (p ^ m)` equality & `p ^ m` divisibility)**. -/
theorem kummer_congruence_bernoulli_toZModPow (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {m k k' : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (hk' : 1 ≤ k')
    (hndvd : ¬ (p - 1) ∣ (k + 1))
    (hndvd' : ¬ (p - 1) ∣ (k' + 1))
    (hcong : k ≡ k' [MOD (p - 1) * p ^ (m - 1)]) :
    PadicInt.toZModPow m (kummerBernoulliInt p hp2 hk hndvd) =
      PadicInt.toZModPow m (kummerBernoulliInt p hp2 hk' hndvd') ∧
    (p : ℤ_[p]) ^ m ∣ (kummerBernoulliInt p hp2 hk' hndvd' - kummerBernoulliInt p hp2 hk hndvd) := by
  have hnorm : ‖kummerBernoulliInt p hp2 hk hndvd - kummerBernoulliInt p hp2 hk' hndvd'‖ ≤
      (p : ℝ) ^ (-(m : ℤ)) :=
    kummer_congruence_bernoulli p hp2 hm hk hk' hndvd hcong
  have hmod : PadicInt.toZModPow m (kummerBernoulliInt p hp2 hk hndvd) =
      PadicInt.toZModPow m (kummerBernoulliInt p hp2 hk' hndvd') :=
    padicInt_toZModPow_eq_of_norm_le_pow hnorm
  have hdvd : (p : ℤ_[p]) ^ m ∣
      (kummerBernoulliInt p hp2 hk' hndvd' - kummerBernoulliInt p hp2 hk hndvd) := by
    have hker : kummerBernoulliInt p hp2 hk' hndvd' - kummerBernoulliInt p hp2 hk hndvd ∈
        Ideal.span ({(p : ℤ_[p]) ^ m} : Set ℤ_[p]) := by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, hmod, sub_self]
    exact Ideal.mem_span_singleton.mp hker
  exact ⟨hmod, hdvd⟩

/-! ### Teichmüller Character `ω`, 1-Unit Projection `⟨x⟩`, & Discrete Log `κ : (1 + p ℤ_[p]) → ℤ_[p]` -/

section TeichmullerAndLog

variable {p : ℕ} [Fact p.Prime]

/-- Hensel/Binomial lifting step in `ℤ_[p]`:
if `‖a - b‖ ≤ p ^ (-n)` (`n ≥ 1`), then `‖a ^ p - b ^ p‖ ≤ p ^ (-(n + 1))`. -/
lemma padicInt_pow_prime_lift {n : ℕ} (hn : 1 ≤ n) {a b : ℤ_[p]}
    (hab : ‖a - b‖ ≤ (p : ℝ) ^ (-(n : ℤ))) :
    ‖a ^ p - b ^ p‖ ≤ (p : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by
  have hp : p.Prime := Fact.out
  set d := a - b
  have ha : a = d + b := by simp [d]
  rw [ha, add_pow, Finset.sum_range_succ']
  simp only [Nat.sub_zero, pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one, mul_one,
    add_sub_cancel_right]
  have hrange : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_le
  have hsum_split : ∑ k ∈ Finset.range p, d ^ (k + 1) * b ^ (p - (k + 1)) * (p.choose (k + 1) : ℤ_[p]) =
      (∑ k ∈ Finset.range (p - 1), d ^ (k + 1) * b ^ (p - (k + 1)) * (p.choose (k + 1) : ℤ_[p])) +
      d ^ p * b ^ (p - p) * (p.choose p : ℤ_[p]) := by
    have h1 := Finset.sum_range_succ
      (fun k => d ^ (k + 1) * b ^ (p - (k + 1)) * (p.choose (k + 1) : ℤ_[p])) (p - 1)
    rwa [hrange] at h1
  rw [hsum_split]
  have h1 : ‖d ^ p * b ^ (p - p) * (p.choose p : ℤ_[p])‖ ≤ (p : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by
    simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, norm_pow]
    have hpow : ‖d‖ ^ p ≤ ((p : ℝ) ^ (-(n : ℤ))) ^ p :=
      pow_le_pow_left₀ (norm_nonneg _) hab p
    refine hpow.trans ?_
    rw [← zpow_natCast, ← zpow_mul]
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
    refine zpow_le_zpow_right₀ hp1 ?_
    have hp2 : 2 ≤ p := hp.two_le
    have hnp : n + 1 ≤ n * p := by nlinarith
    have hnpZ : ((n + 1 : ℕ) : ℤ) ≤ (n : ℤ) * (p : ℤ) := by exact_mod_cast hnp
    rw [neg_mul]
    linarith
  have hmid : ‖∑ x ∈ Finset.range (p - 1),
      d ^ (x + 1) * b ^ (p - (x + 1)) * (p.choose (x + 1) : ℤ_[p])‖ ≤
      (p : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by
    refine padicInt_norm_sum_le _ _ (by positivity) fun x hx => ?_
    have hxlt : x + 1 < p := by have := Finset.mem_range.mp hx; omega
    obtain ⟨q, hq⟩ := hp.dvd_choose_self (Nat.succ_ne_zero x) hxlt
    have hq' : (p.choose (x + 1) : ℤ_[p]) = (p : ℤ_[p]) * (q : ℤ_[p]) := by exact_mod_cast hq
    rw [hq', norm_mul, norm_mul, norm_mul, norm_pow]
    have hnp : ‖(p : ℤ_[p])‖ = (p : ℝ) ^ (-(1 : ℤ)) := by
      change ‖(p : ℚ_[p])‖ = _; rw [Padic.norm_p, zpow_neg_one]
    have hdx : ‖d‖ ^ (x + 1) ≤ (p : ℝ) ^ (-(n : ℤ)) := by
      calc ‖d‖ ^ (x + 1) = ‖d‖ ^ x * ‖d‖ := pow_succ _ _
        _ ≤ 1 * (p : ℝ) ^ (-(n : ℤ)) :=
            mul_le_mul (pow_le_one₀ (norm_nonneg _) (PadicInt.norm_le_one _)) hab (norm_nonneg _) zero_le_one
        _ = (p : ℝ) ^ (-(n : ℤ)) := one_mul _
    calc ‖d‖ ^ (x + 1) * ‖b ^ (p - (x + 1))‖ * (‖(p : ℤ_[p])‖ * ‖(q : ℤ_[p])‖)
        ≤ (p : ℝ) ^ (-(n : ℤ)) * 1 * ((p : ℝ) ^ (-(1 : ℤ)) * 1) := by
          rw [hnp]
          exact mul_le_mul
            (mul_le_mul hdx (PadicInt.norm_le_one _) (norm_nonneg _) (by positivity))
            (mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (by positivity))
            (by positivity) (by positivity)
      _ = (p : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by
          have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
          rw [mul_one, mul_one, ← zpow_add₀ hp0]
          congr 1; omega
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hmid h1)

lemma norm_pow_prime_pow_sub_le (x : ℤ_[p]) (n : ℕ) :
    ‖x ^ (p ^ (n + 1)) - x ^ (p ^ n)‖ ≤ (p : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by
  induction n with
  | zero =>
    simpa using padicInt_pow_prime_sub_norm_le (p := p) x
  | succ n ih =>
    have hrew : x ^ (p ^ (n + 2)) - x ^ (p ^ (n + 1)) = (x ^ (p ^ (n + 1))) ^ p - (x ^ (p ^ n)) ^ p := by
      rw [← pow_mul, ← pow_mul, ← pow_succ, ← pow_succ]
    rw [hrew]
    exact padicInt_pow_prime_lift (Nat.succ_pos n) ih

lemma cauchySeq_pow_prime_pow (x : ℤ_[p]) : CauchySeq (fun n : ℕ => x ^ (p ^ n)) := by
  have hp : p.Prime := Fact.out
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := PadicInt.exists_pow_neg_lt p hε
  have hstep_le : ∀ m k : ℕ, N ≤ m → ‖x ^ (p ^ (m + k)) - x ^ (p ^ m)‖ ≤ (p : ℝ) ^ (-(N : ℤ)) := by
    intro m k hm
    induction k with
    | zero => simp
    | succ k ih =>
      have hdecomp : x ^ (p ^ (m + (k + 1))) - x ^ (p ^ m) =
          (x ^ (p ^ (m + k + 1)) - x ^ (p ^ (m + k))) + (x ^ (p ^ (m + k)) - x ^ (p ^ m)) := by
        ring
      rw [hdecomp]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
      have hbd := norm_pow_prime_pow_sub_le x (m + k)
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
      exact hbd.trans (zpow_le_zpow_right₀ hp1 (by omega))
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [dist_eq_norm]
  rcases le_total m n with hmn | hnm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [← norm_neg, neg_sub]
    exact (hstep_le m k hm).trans_lt hN
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    exact (hstep_le n k hn).trans_lt hN

/-- Concrete **Teichmüller representative** `ω(x) = lim_{n → ∞} x ^ (p ^ n) ∈ ℤ_[p]`. -/
def teichmuller (x : ℤ_[p]) : ℤ_[p] :=
  limUnder atTop (fun n : ℕ => x ^ (p ^ n))

theorem tendsto_pow_prime_pow_teichmuller (x : ℤ_[p]) :
    Tendsto (fun n : ℕ => x ^ (p ^ n)) atTop (nhds (teichmuller x)) :=
  (cauchySeq_tendsto_of_complete (cauchySeq_pow_prime_pow x)).choose_spec |> fun h =>
    tendsto_nhds_limUnder ⟨_, h⟩

theorem teichmuller_mul (x y : ℤ_[p]) :
    teichmuller (x * y) = teichmuller x * teichmuller y := by
  have h1 := tendsto_pow_prime_pow_teichmuller (x * y)
  have h2 := (tendsto_pow_prime_pow_teichmuller x).mul (tendsto_pow_prime_pow_teichmuller y)
  have heq : (fun n : ℕ => (x * y) ^ (p ^ n)) = fun n : ℕ => x ^ (p ^ n) * y ^ (p ^ n) := by
    ext n; exact mul_pow x y (p ^ n)
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

theorem teichmuller_pow_p (x : ℤ_[p]) : teichmuller x ^ p = teichmuller x := by
  have h1 := (tendsto_pow_prime_pow_teichmuller x).pow p
  have h2 := (tendsto_pow_prime_pow_teichmuller x).comp (tendsto_add_atTop_nat 1)
  have heq : (fun n : ℕ => (x ^ (p ^ n)) ^ p) = (fun n : ℕ => x ^ (p ^ n)) ∘ (· + 1) := by
    ext n; simp [pow_succ, pow_mul]
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

theorem teichmuller_eq_of_toZMod_eq {x y : ℤ_[p]} (h : PadicInt.toZMod x = PadicInt.toZMod y) :
    teichmuller x = teichmuller y := by
  have h1 : ‖x - y‖ ≤ (p : ℝ) ^ (-(1 : ℤ)) := by
    have hmem : x - y ∈ Ideal.span ({(p : ℤ_[p]) ^ 1} : Set ℤ_[p]) := by
      rw [pow_one, ← padicInt_ker_toZMod_eq_span_p, RingHom.mem_ker, map_sub, h, sub_self]
    exact (PadicInt.norm_le_pow_iff_mem_span_pow (x - y) 1).mpr hmem
  have hind : ∀ n : ℕ, ‖x ^ (p ^ n) - y ^ (p ^ n)‖ ≤ (p : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by
    intro n
    induction n with
    | zero => simpa using h1
    | succ n ih =>
      have hrew : x ^ (p ^ (n + 1)) - y ^ (p ^ (n + 1)) = (x ^ (p ^ n)) ^ p - (y ^ (p ^ n)) ^ p := by
        rw [← pow_mul, ← pow_mul, ← pow_succ]
      rw [hrew]
      exact padicInt_pow_prime_lift (Nat.succ_pos n) ih
  have hdiff : Tendsto (fun n : ℕ => x ^ (p ^ n) - y ^ (p ^ n)) atTop
      (nhds (teichmuller x - teichmuller y)) :=
    (tendsto_pow_prime_pow_teichmuller x).sub (tendsto_pow_prime_pow_teichmuller y)
  have hzero : Tendsto (fun n : ℕ => x ^ (p ^ n) - y ^ (p ^ n)) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) hind ?_
    have hp : p.Prime := Fact.out
    have hinv : Tendsto (fun n : ℕ => ((p : ℝ)⁻¹) ^ (n + 1)) atTop (nhds 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
        (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt))).comp (tendsto_add_atTop_nat 1)
    refine hinv.congr fun n => ?_
    rw [inv_pow, ← zpow_natCast, ← zpow_neg]
  exact sub_eq_zero.mp (tendsto_nhds_unique hdiff hzero)

theorem continuous_teichmuller : Continuous (teichmuller (p := p)) := by
  rw [Metric.continuous_iff]
  intro x ε hε
  refine ⟨(p : ℝ) ^ (-(1 : ℤ)), zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _, fun y hy => ?_⟩
  rw [dist_eq_norm] at hy
  have h1 : PadicInt.toZModPow 1 y = PadicInt.toZModPow 1 x :=
    padicInt_toZModPow_eq_of_norm_le_pow hy.le
  have h0 : PadicInt.toZMod y = PadicInt.toZMod x := by
    have hmem : y - x ∈ Ideal.span ({(p : ℤ_[p]) ^ 1} : Set ℤ_[p]) := by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, h1, sub_self]
    rw [pow_one, ← padicInt_ker_toZMod_eq_span_p, RingHom.mem_ker, map_sub, sub_eq_zero] at hmem
    exact hmem
  rw [teichmuller_eq_of_toZMod_eq h0, dist_self]
  exact hε

theorem toZMod_teichmuller (x : ℤ_[p]) : PadicInt.toZMod (teichmuller x) = PadicInt.toZMod x := by
  have hp : p.Prime := Fact.out
  have hnorm : ‖teichmuller x - x‖ ≤ (p : ℝ) ^ (-(1 : ℤ)) := by
    have hlim : Tendsto (fun n => ‖x ^ (p ^ n) - x‖) atTop (nhds ‖teichmuller x - x‖) :=
      ((tendsto_pow_prime_pow_teichmuller x).sub_const x).norm
    refine le_of_tendsto' hlim fun n => ?_
    induction n with
    | zero => simp
    | succ n ih =>
      have hdecomp : x ^ (p ^ (n + 1)) - x = (x ^ (p ^ (n + 1)) - x ^ (p ^ n)) + (x ^ (p ^ n) - x) := by ring
      rw [hdecomp]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
      exact (norm_pow_prime_pow_sub_le x n).trans (zpow_le_zpow_right₀ hp1 (by omega))
  have hmem : teichmuller x - x ∈ Ideal.span ({(p : ℤ_[p])} : Set ℤ_[p]) := by
    simpa [pow_one] using (PadicInt.norm_le_pow_iff_mem_span_pow (teichmuller x - x) 1).mp hnorm
  rw [← padicInt_ker_toZMod_eq_span_p, RingHom.mem_ker, map_sub, sub_eq_zero] at hmem
  exact hmem

theorem teichmuller_pow_sub_one {x : ℤ_[p]} (hx : PadicInt.toZMod x ≠ 0) :
    teichmuller x ^ (p - 1) = 1 := by
  have hp : p.Prime := Fact.out
  have hne0 : teichmuller x ≠ 0 := by
    intro h0
    apply hx
    rw [← toZMod_teichmuller, h0, map_zero]
  have hmul : teichmuller x * teichmuller x ^ (p - 1) = teichmuller x * 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hp.one_le, teichmuller_pow_p, mul_one]
  exact mul_left_cancel₀ hne0 hmul

/-- Concrete 1-unit projection `⟨x⟩ = x * ω(x)^{-1} ∈ 1 + p ℤ_[p]` on `ℤ_[p]ˣ` (extended by `1` on
`p ℤ_[p]`). -/
def diamond (x : ℤ_[p]) : ℤ_[p] :=
  if PadicInt.toZMod x ≠ 0 then x * teichmuller x ^ (p - 2) else 1

theorem continuous_diamond : Continuous (diamond (p := p)) := by
  have heq : diamond (p := p) = fun x => unitIndicator x * (x * teichmuller x ^ (p - 2)) + (1 - unitIndicator x) := by
    ext x
    unfold diamond unitIndicator
    split_ifs <;> ring
  rw [heq]
  exact (continuous_unitIndicator.mul (continuous_id.mul (continuous_teichmuller.pow (p - 2)))).add
    (continuous_const.sub continuous_unitIndicator)

theorem teichmuller_mul_diamond (hp2 : p ≠ 2) {x : ℤ_[p]} (hx : PadicInt.toZMod x ≠ 0) :
    teichmuller x * diamond x = x := by
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  rw [diamond, if_pos hx, ← mul_assoc, mul_comm (teichmuller x) x, mul_assoc, ← pow_succ',
    show p - 2 + 1 = p - 1 by omega, teichmuller_pow_sub_one hx, mul_one]

theorem toZMod_diamond (hp2 : p ≠ 2) (x : ℤ_[p]) : PadicInt.toZMod (diamond x) = 1 := by
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  unfold diamond
  split_ifs with hx
  · have hmul : PadicInt.toZMod (teichmuller x) * PadicInt.toZMod (x * teichmuller x ^ (p - 2)) =
        PadicInt.toZMod x := by
      rw [← map_mul, ← mul_assoc, mul_comm (teichmuller x) x, mul_assoc, ← pow_succ',
        show p - 2 + 1 = p - 1 by omega, teichmuller_pow_sub_one hx, mul_one]
    rw [toZMod_teichmuller] at hmul
    exact mul_left_cancel₀ hx (hmul.trans (mul_one _).symm)
  · exact map_one _

theorem norm_diamond_sub_one_lt_one (hp2 : p ≠ 2) (x : ℤ_[p]) : ‖diamond x - 1‖ < 1 := by
  have hp : p.Prime := Fact.out
  have hmem : diamond x - 1 ∈ Ideal.span ({(p : ℤ_[p]) ^ 1} : Set ℤ_[p]) := by
    rw [pow_one, ← padicInt_ker_toZMod_eq_span_p, RingHom.mem_ker, map_sub, toZMod_diamond hp2, map_one, sub_self]
  have hle : ‖diamond x - 1‖ ≤ (p : ℝ) ^ (-(1 : ℤ)) :=
    (PadicInt.norm_le_pow_iff_mem_span_pow (diamond x - 1) 1).mpr hmem
  exact hle.trans_lt (by rw [zpow_neg_one]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt))

/-- **Lifting-the-Exponent Lemma for `1 + p`** (odd prime `p`):
for every `k : ℕ`, `(1 + p) ^ (p ^ k) = 1 + u * p ^ (k + 1)` with `¬ p ∣ u`! -/
lemma lte_one_add_prime (hp2 : p ≠ 2) (k : ℕ) :
    ∃ u : ℕ, ¬ p ∣ u ∧ (1 + p) ^ (p ^ k) = 1 + u * p ^ (k + 1) := by
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  induction k with
  | zero =>
    refine ⟨1, hp.not_dvd_one, by ring⟩
  | succ k ih =>
    obtain ⟨u, hu, heq⟩ := ih
    rw [pow_succ, pow_mul, heq, add_comm 1 (u * p ^ (k + 1)), add_pow, Finset.sum_range_succ']
    have hrange_eq : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_le
    rw [← hrange_eq, Finset.sum_range_succ', hrange_eq]
    simp only [Nat.sub_zero, pow_zero, one_mul, Nat.choose_zero_right, mul_one,
      zero_add, pow_one, Nat.choose_one_right, Nat.one_pow]
    have hdvd_tail_p : ∀ j ∈ Finset.range (p - 1),
        p ^ (k + 3) ∣ (u * p ^ (k + 1)) ^ (j + 2) * p.choose (j + 2) := by
      intro j hj
      rw [mul_pow, ← pow_mul]
      have hjlt : j < p - 1 := Finset.mem_range.mp hj
      by_cases hlast : j + 2 = p
      · have hle : k + 3 ≤ (k + 1) * (j + 2) := by rw [hlast]; nlinarith
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (pow_dvd_pow p hle) _) _
      · have hltp : j + 2 < p := by omega
        obtain ⟨q, hq⟩ := hp.dvd_choose_self (by omega : j + 2 ≠ 0) hltp
        have hle : k + 2 ≤ (k + 1) * (j + 2) := by nlinarith
        have h1 : p ^ (k + 2) ∣ p ^ ((k + 1) * (j + 2)) := pow_dvd_pow p hle
        have h2 : p ^ (k + 2) * p ∣ p ^ ((k + 1) * (j + 2)) * p.choose (j + 2) := by
          rw [hq]
          exact mul_dvd_mul h1 (dvd_mul_right p q)
        rw [← pow_succ] at h2
        have hre : u ^ (j + 2) * p ^ ((k + 1) * (j + 2)) * p.choose (j + 2) =
            u ^ (j + 2) * (p ^ ((k + 1) * (j + 2)) * p.choose (j + 2)) := by ring
        rw [hre]
        exact dvd_mul_of_dvd_right h2 _
    have hsum_dvd : p ^ (k + 3) ∣ ∑ x ∈ Finset.range (p - 1),
        (u * p ^ (k + 1)) ^ (x + 1 + 1) * p.choose (x + 1 + 1) := by
      refine Finset.dvd_sum fun x hx => ?_
      exact hdvd_tail_p x hx
    obtain ⟨w, hw⟩ := hsum_dvd
    refine ⟨u + w * p, ?_, ?_⟩
    · intro hdvd
      have hu_dvd : p ∣ u := (Nat.dvd_add_left (dvd_mul_left p w)).mp hdvd
      exact hu hu_dvd
    · simp only [Nat.cast_id]
      rw [hw, pow_succ p (k + 2), pow_succ p (k + 1)]
      ring

/-- Exact bijection `ZMod (p ^ n) ≃ {u : ZMod (p^(n+1)) | u ≡ 1 mod p}` via `s ↦ (1 + p)^s` for
odd prime `p`. -/
lemma exists_unique_log_mod_prime_pow (hp2 : p ≠ 2) (n : ℕ) (u : ZMod (p ^ (n + 1)))
    (hu : zmodPowCast (p := p) (Nat.succ_le_succ (Nat.zero_le n)) u = 1) :
    ∃! s : ZMod (p ^ n), ((1 + p : ZMod (p ^ (n + 1))) ^ s.val) = u := by
  have hp : p.Prime := Fact.out
  have : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero (n + 1) hp.ne_zero⟩
  -- Fiber S = {u : ZMod (p^(n+1)) | cast u = 1} has cardinality p^n
  let S : Finset (ZMod (p ^ (n + 1))) :=
    Finset.univ.filter (fun v : ZMod (p ^ (n + 1)) =>
      zmodPowCast (p := p) (Nat.succ_le_succ (Nat.zero_le n)) v = 1)
  have hScard : S.card = p ^ n := by
    have hbij : S = (Finset.range (p ^ n)).image (fun k => ((1 + p * k : ℕ) : ZMod (p ^ (n + 1)))) := by
      ext v
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_range]
      constructor
      · intro hv
        have hv1 : v.val % p = 1 := by
          have h1 : (v.val : ZMod p) = 1 := by
            have := zmodPowCast_val_modEq (p := p) (Nat.succ_le_succ (Nat.zero_le n)) v
            rw [hv] at this
            have hcast : ((v.val : ℕ) : ZMod (p ^ 1)) = 1 := by
              rw [← hv, zmodPowCast,
                ← map_natCast (ZMod.castHom (pow_dvd_pow p (Nat.succ_le_succ (Nat.zero_le n))) (ZMod (p ^ 1))),
                ZMod.natCast_zmod_val]
            have h1' := congrArg ZMod.val hcast
            rw [ZMod.val_natCast, pow_one, ZMod.val_one] at h1'
            rw [← ZMod.natCast_zmod_val (1 : ZMod p), ZMod.val_one]
            exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (by rw [h1', Nat.one_mod_eq_one.mpr hp.ne_one])
          have := congrArg ZMod.val h1
          rwa [ZMod.val_natCast, ZMod.val_one] at this
        refine ⟨v.val / p, ?_, ?_⟩
        · have hvlt : v.val < p * p ^ n := by rw [← pow_succ']; exact ZMod.val_lt v
          exact Nat.div_lt_of_lt_mul hvlt
        · have hdiv : v.val % p + p * (v.val / p) = v.val := by
            rw [add_comm]; exact Nat.div_add_mod v.val p
          rw [hv1] at hdiv
          rw [hdiv, ZMod.natCast_zmod_val]
      · rintro ⟨k, _, rfl⟩
        rw [zmodPowCast, map_natCast, Nat.cast_add, Nat.cast_mul, pow_one, ZMod.natCast_self,
          zero_mul, add_zero, Nat.cast_one]
    rw [hbij, Finset.card_image_of_injOn]
    · exact Finset.card_range _
    · intro k₁ hk₁ k₂ hk₂ heq
      have h1lt : 1 + p * k₁ < p ^ (n + 1) := by
        have := Finset.mem_range.mp hk₁
        have hp2' := hp.two_le
        rw [pow_succ']
        nlinarith
      have h2lt : 1 + p * k₂ < p ^ (n + 1) := by
        have := Finset.mem_range.mp hk₂
        have hp2' := hp.two_le
        rw [pow_succ']
        nlinarith
      have hv := congrArg ZMod.val heq
      rw [ZMod.val_natCast_of_lt h1lt, ZMod.val_natCast_of_lt h2lt] at hv
      exact Nat.eq_of_mul_eq_mul_left hp.pos (Nat.add_left_cancel hv)
  -- The map f : ZMod (p^n) → ZMod (p^(n+1)), s ↦ (1 + p)^s.val lands in S and is injective!
  let f : ZMod (p ^ n) → ZMod (p ^ (n + 1)) := fun s => (1 + p : ZMod (p ^ (n + 1))) ^ s.val
  have hf_mem : ∀ s : ZMod (p ^ n), f s ∈ S := by
    intro s
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    dsimp only [f]
    rw [map_pow, map_add, map_one, map_natCast]
    have hp0 : (p : ZMod (p ^ 1)) = 0 := by rw [pow_one, ZMod.natCast_self]
    rw [hp0, add_zero, one_pow]
  -- Order of (1 + p) in (ZMod (p^(n+1)))ˣ is p^n by LTE!
  have hcop : Nat.Coprime (1 + p) (p ^ (n + 1)) :=
    ((hp.coprime_iff_not_dvd.mpr (fun hd => hp.not_dvd_one ((Nat.dvd_add_left dvd_rfl).mp hd))).symm).pow_right _
  let g : (ZMod (p ^ (n + 1)))ˣ := ZMod.unitOfCoprime (1 + p) hcop
  have hg_coe : ((g : ZMod (p ^ (n + 1)))) = (1 + p : ZMod (p ^ (n + 1))) := by
    dsimp only [g]
    rw [ZMod.coe_unitOfCoprime, Nat.cast_add, Nat.cast_one]
  have hg_pow_pn : g ^ (p ^ n) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, hg_coe]
    obtain ⟨w, _, hw⟩ := lte_one_add_prime (p := p) hp2 n
    have hcast : (((1 + p) ^ (p ^ n) : ℕ) : ZMod (p ^ (n + 1))) = 1 := by
      rw [hw, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero, Nat.cast_one]
    simpa [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hcast
  have hg_ord : orderOf g = p ^ n := by
    have hdvd : orderOf g ∣ p ^ n := orderOf_dvd_of_pow_eq_one hg_pow_pn
    obtain ⟨k, hkn, hord⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    rcases Nat.eq_or_lt_of_le hkn with rfl | hlt
    · exact hord
    · exfalso
      have h1 : g ^ (p ^ k) = 1 := by rw [← hord]; exact pow_orderOf_eq_one g
      have h1' : ((1 + p : ZMod (p ^ (n + 1))) ^ (p ^ k)) = 1 := by
        rw [← hg_coe, ← Units.val_pow_eq_pow_val, h1, Units.val_one]
      obtain ⟨w, hw_ndvd, hw⟩ := lte_one_add_prime (p := p) hp2 k
      have hcast : ((1 + w * p ^ (k + 1) : ℕ) : ZMod (p ^ (n + 1))) = 1 := by
        rw [← hw]
        simpa [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using h1'
      have hzero : ((w * p ^ (k + 1) : ℕ) : ZMod (p ^ (n + 1))) = 0 := by
        rw [Nat.cast_add, Nat.cast_one, add_eq_left] at hcast
        exact hcast
      have hdvd_n : p ^ (n + 1) ∣ w * p ^ (k + 1) := (ZMod.natCast_eq_zero_iff _ _).mp hzero
      have hpow_le : p ^ (k + 2) ∣ p ^ (n + 1) := pow_dvd_pow p (by omega)
      have hdvd_k2 : p ^ (k + 2) ∣ w * p ^ (k + 1) := hpow_le.trans hdvd_n
      rw [pow_succ, mul_comm (p ^ (k + 1)) p] at hdvd_k2
      have hp_dvd_w : p ∣ w := (mul_dvd_mul_iff_right (pow_ne_zero (k + 1) hp.ne_zero)).mp hdvd_k2
      exact hw_ndvd hp_dvd_w
  have hf_inj : Function.Injective f := by
    intro s₁ s₂ heq
    have hpow : g ^ s₁.val = g ^ s₂.val := by
      apply Units.ext
      simpa [Units.val_pow_eq_pow_val, hg_coe, f] using heq
    rcases le_total s₁.val s₂.val with hle | hle
    · have h1 : g ^ (s₂.val - s₁.val) = 1 := by
        have hmul : g ^ s₁.val * g ^ (s₂.val - s₁.val) = g ^ s₁.val * 1 := by
          rw [← pow_add, Nat.add_sub_cancel' hle, hpow, mul_one]
        exact mul_left_cancel hmul
      have hdvd0 : orderOf g ∣ s₂.val - s₁.val := orderOf_dvd_of_pow_eq_one h1
      have hdvd : p ^ n ∣ s₂.val - s₁.val := by rwa [hg_ord] at hdvd0
      have hlt : s₂.val - s₁.val < p ^ n := by have := ZMod.val_lt s₂; omega
      have h0 : s₂.val - s₁.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
      have hv : s₁.val = s₂.val := by omega
      rw [← ZMod.natCast_zmod_val s₁, ← ZMod.natCast_zmod_val s₂, hv]
    · have h1 : g ^ (s₁.val - s₂.val) = 1 := by
        have hmul : g ^ s₂.val * g ^ (s₁.val - s₂.val) = g ^ s₂.val * 1 := by
          rw [← pow_add, Nat.add_sub_cancel' hle, ← hpow, mul_one]
        exact mul_left_cancel hmul
      have hdvd0 : orderOf g ∣ s₁.val - s₂.val := orderOf_dvd_of_pow_eq_one h1
      have hdvd : p ^ n ∣ s₁.val - s₂.val := by rwa [hg_ord] at hdvd0
      have hlt : s₁.val - s₂.val < p ^ n := by have := ZMod.val_lt s₁; omega
      have h0 : s₁.val - s₂.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
      have hv : s₁.val = s₂.val := by omega
      rw [← ZMod.natCast_zmod_val s₁, ← ZMod.natCast_zmod_val s₂, hv]
  have himg_eq : Finset.univ.image f = S := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro y hy
      obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hy
      exact hf_mem s
    · rw [Finset.card_image_of_injective _ hf_inj, Finset.card_univ, ZMod.card, hScard]
  have huS : u ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩
  rw [← himg_eq, Finset.mem_image] at huS
  obtain ⟨s, _, hs⟩ := huS
  exact ⟨s, hs, fun s' hs' => hf_inj (hs'.trans hs.symm)⟩

/-- Level-`n` discrete logarithm `κ_n(u) ∈ ZMod (p^n)` base `1 + p` for `u ∈ 1 + p ℤ_[p]`. -/
def padicLogLevel (hp2 : p ≠ 2) (n : ℕ) (u : ℤ_[p]) : ZMod (p ^ n) :=
  if hu : zmodPowCast (p := p) (Nat.succ_le_succ (Nat.zero_le n)) (PadicInt.toZModPow (n + 1) u) = 1 then
    (exists_unique_log_mod_prime_pow hp2 n (PadicInt.toZModPow (n + 1) u) hu).choose
  else 0

lemma padicLogLevel_spec (hp2 : p ≠ 2) (n : ℕ) {u : ℤ_[p]} (hu : PadicInt.toZMod u = 1) :
    ((1 + p : ZMod (p ^ (n + 1))) ^ (padicLogLevel hp2 n u).val) = PadicInt.toZModPow (n + 1) u := by
  have hu1 : zmodPowCast (p := p) (Nat.succ_le_succ (Nat.zero_le n)) (PadicInt.toZModPow (n + 1) u) = 1 := by
    rw [zmodPowCast_toZModPow]
    have hmem : u - 1 ∈ Ideal.span ({(p : ℤ_[p]) ^ 1} : Set ℤ_[p]) := by
      rw [pow_one, ← padicInt_ker_toZMod_eq_span_p, RingHom.mem_ker, map_sub, hu, map_one, sub_self]
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hmem
    exact hmem
  unfold padicLogLevel
  rw [dif_pos hu1]
  exact (exists_unique_log_mod_prime_pow hp2 n (PadicInt.toZModPow (n + 1) u) hu1).choose_spec.1

lemma padicLogLevel_compat (hp2 : p ≠ 2) (n : ℕ) {u : ℤ_[p]} (hu : PadicInt.toZMod u = 1) :
    zmodPowStep (p := p) n (padicLogLevel hp2 (n + 1) u) = padicLogLevel hp2 n u := by
  have hp : p.Prime := Fact.out
  have : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  have hu1 : zmodPowCast (p := p) (Nat.succ_le_succ (Nat.zero_le n)) (PadicInt.toZModPow (n + 1) u) = 1 := by
    rw [zmodPowCast_toZModPow]
    have hmem : u - 1 ∈ Ideal.span ({(p : ℤ_[p]) ^ 1} : Set ℤ_[p]) := by
      rw [pow_one, ← padicInt_ker_toZMod_eq_span_p, RingHom.mem_ker, map_sub, hu, map_one, sub_self]
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hmem
    exact hmem
  have huniq := (exists_unique_log_mod_prime_pow hp2 n (PadicInt.toZModPow (n + 1) u) hu1).choose_spec.2
  have hstep_eq : ((1 + p : ZMod (p ^ (n + 1))) ^ (zmodPowStep (p := p) n (padicLogLevel hp2 (n + 1) u)).val) =
      PadicInt.toZModPow (n + 1) u := by
    have hmod : (padicLogLevel hp2 (n + 1) u).val ≡
        (zmodPowStep (p := p) n (padicLogLevel hp2 (n + 1) u)).val [MOD p ^ n] :=
      zmodPowCast_val_modEq (Nat.le_succ n) _
    have hpow_pn : (1 + p : ZMod (p ^ (n + 1))) ^ (p ^ n) = 1 := by
      obtain ⟨w, _, hw⟩ := lte_one_add_prime (p := p) hp2 n
      have hcast : (((1 + p) ^ (p ^ n) : ℕ) : ZMod (p ^ (n + 1))) = 1 := by
        rw [hw, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero, Nat.cast_one]
      simpa [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hcast
    have hpow_eq : (1 + p : ZMod (p ^ (n + 1))) ^ (zmodPowStep (p := p) n (padicLogLevel hp2 (n + 1) u)).val =
        (1 + p : ZMod (p ^ (n + 1))) ^ (padicLogLevel hp2 (n + 1) u).val := by
      rcases le_total (zmodPowStep (p := p) n (padicLogLevel hp2 (n + 1) u)).val
          (padicLogLevel hp2 (n + 1) u).val with hle | hle
      · obtain ⟨q, hq⟩ := (Nat.modEq_iff_dvd' hle).mp hmod.symm
        have heq : (padicLogLevel hp2 (n + 1) u).val =
            (zmodPowStep (p := p) n (padicLogLevel hp2 (n + 1) u)).val + p ^ n * q := by omega
        conv_rhs => rw [heq]
        rw [pow_add (1 + (p : ZMod (p ^ (n + 1)))) _ _, pow_mul, hpow_pn, one_pow, mul_one]
      · obtain ⟨q, hq⟩ := (Nat.modEq_iff_dvd' hle).mp hmod
        have heq : (zmodPowStep (p := p) n (padicLogLevel hp2 (n + 1) u)).val =
            (padicLogLevel hp2 (n + 1) u).val + p ^ n * q := by omega
        conv_lhs => rw [heq]
        rw [pow_add (1 + (p : ZMod (p ^ (n + 1)))) _ _, pow_mul, hpow_pn, one_pow, mul_one]
    rw [hpow_eq]
    have hspec := congrArg (zmodPowStep (p := p) (n + 1)) (padicLogLevel_spec hp2 (n + 1) hu)
    rw [zmodPowStep, zmodPowCast_toZModPow, map_pow, map_add, map_one, map_natCast] at hspec
    exact hspec
  have hch := huniq (zmodPowStep (p := p) n (padicLogLevel hp2 (n + 1) u)) hstep_eq
  simpa [padicLogLevel, dif_pos hu1] using hch

lemma padicLogLevel_compat_le (hp2 : p ≠ 2) {m n : ℕ} (h : m ≤ n) {u : ℤ_[p]}
    (hu : PadicInt.toZMod u = 1) :
    zmodPowCast (p := p) h (padicLogLevel hp2 n u) = padicLogLevel hp2 m u := by
  induction n with
  | zero =>
    obtain rfl : m = 0 := Nat.le_zero.mp h
    exact zmodPowCast_refl 0 _
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact zmodPowCast_refl (k + 1) _
    · have hmk : m ≤ k := Nat.lt_succ_iff.mp hlt
      rw [← zmodPowCast_comp hmk (Nat.le_succ k), ← zmodPowStep, padicLogLevel_compat hp2 k hu, ih hmk]

/-- Concrete **base-`(1 + p)` discrete logarithm** `κ : 1 + p ℤ_[p] → ℤ_[p]` (for odd prime `p`),
defined as the projective limit of `padicLogLevel hp2 n u`. -/
def padicLogBase (hp2 : p ≠ 2) (u : ℤ_[p]) : ℤ_[p] :=
  limUnder atTop (fun n : ℕ => ((padicLogLevel hp2 n u).val : ℤ_[p]))

lemma tendsto_padicLogLevel_padicLogBase (hp2 : p ≠ 2) {u : ℤ_[p]} (hu : PadicInt.toZMod u = 1) :
    Tendsto (fun n : ℕ => ((padicLogLevel hp2 n u).val : ℤ_[p])) atTop (nhds (padicLogBase hp2 u)) := by
  have hcauchy : CauchySeq (fun n : ℕ => ((padicLogLevel hp2 n u).val : ℤ_[p])) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := PadicInt.exists_pow_neg_lt p hε
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    have hmod : PadicInt.toZModPow N ((padicLogLevel hp2 m u).val : ℤ_[p]) =
        PadicInt.toZModPow N ((padicLogLevel hp2 n u).val : ℤ_[p]) := by
      rw [padicInt_toZModPow_val_eq hm, padicInt_toZModPow_val_eq hn,
        padicLogLevel_compat_le hp2 hm hu, padicLogLevel_compat_le hp2 hn hu]
    exact (padicInt_norm_le_pow_of_toZModPow_eq hmod).trans_lt hN
  exact (cauchySeq_tendsto_of_complete hcauchy).choose_spec |> fun h => tendsto_nhds_limUnder ⟨_, h⟩

theorem padicInt_toZModPow_padicLogBase (hp2 : p ≠ 2) (n : ℕ) {u : ℤ_[p]}
    (hu : PadicInt.toZMod u = 1) :
    PadicInt.toZModPow n (padicLogBase hp2 u) = padicLogLevel hp2 n u := by
  have hnorm : ‖padicLogBase hp2 u - ((padicLogLevel hp2 n u).val : ℤ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
    have hlim : Tendsto (fun m => ‖((padicLogLevel hp2 m u).val : ℤ_[p]) - ((padicLogLevel hp2 n u).val : ℤ_[p])‖)
        atTop (nhds ‖padicLogBase hp2 u - ((padicLogLevel hp2 n u).val : ℤ_[p])‖) :=
      ((tendsto_padicLogLevel_padicLogBase hp2 hu).sub_const _).norm
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop n] with m hm
    refine padicInt_norm_le_pow_of_toZModPow_eq ?_
    have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
    rw [padicInt_toZModPow_val_eq hm, padicLogLevel_compat_le hp2 hm hu, map_natCast, ZMod.natCast_zmod_val]
  have hmod := padicInt_toZModPow_eq_of_norm_le_pow hnorm
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  rwa [map_natCast, ZMod.natCast_zmod_val] at hmod

/-- **Exact Exponential-Logarithm Inversion**: `(1 + p) ^ (padicLogBase u) = u` for every
`u ∈ 1 + p ℤ_[p]`. -/
theorem padicPowOneAdd_padicLogBase (hp2 : p ≠ 2) {u : ℤ_[p]} (hu : PadicInt.toZMod u = 1) :
    padicPowOneAdd (p : ℤ_[p]) (padicLogBase hp2 u) = u := by
  have hp : p.Prime := Fact.out
  have hp_lt1 : ‖(p : ℤ_[p])‖ < 1 := by
    change ‖(p : ℚ_[p])‖ < 1; rw [Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hlimL : Tendsto (fun n : ℕ => padicPowOneAdd (p : ℤ_[p]) ((padicLogLevel hp2 n u).val : ℤ_[p]))
      atTop (nhds (padicPowOneAdd (p : ℤ_[p]) (padicLogBase hp2 u))) :=
    ((continuous_padicPowOneAdd hp_lt1).tendsto _).comp (tendsto_padicLogLevel_padicLogBase hp2 hu)
  have hlimR : Tendsto (fun n : ℕ => padicPowOneAdd (p : ℤ_[p]) ((padicLogLevel hp2 n u).val : ℤ_[p]))
      atTop (nhds u) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := PadicInt.exists_pow_neg_lt p hε
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm, padicPowOneAdd_natCast]
    have hmod : PadicInt.toZModPow (n + 1) ((1 + (p : ℤ_[p])) ^ (padicLogLevel hp2 n u).val) =
        PadicInt.toZModPow (n + 1) u := by
      rw [map_pow, map_add, map_one, map_natCast]
      exact padicLogLevel_spec hp2 n hu
    have hbd := padicInt_norm_le_pow_of_toZModPow_eq hmod
    have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
    exact (hbd.trans (zpow_le_zpow_right₀ hp1 (by omega))).trans_lt hN
  exact tendsto_nhds_unique hlimL hlimR

/-- Continuity of `x ↦ padicLogBase (diamond x)` on all of `ℤ_[p]`. -/
theorem continuous_padicLogBase_diamond (hp2 : p ≠ 2) :
    Continuous (fun x : ℤ_[p] => padicLogBase hp2 (diamond x)) := by
  rw [Metric.continuous_iff]
  intro x ε hε
  obtain ⟨N, hN⟩ := PadicInt.exists_pow_neg_lt p hε
  have hcont_d : Continuous (diamond (p := p)) := continuous_diamond
  obtain ⟨δ, hδ, hδ_d⟩ := Metric.continuous_iff.mp hcont_d x ((p : ℝ) ^ (-((N + 1 : ℕ) : ℤ)))
    (zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _)
  refine ⟨δ, hδ, fun y hy => ?_⟩
  rw [dist_eq_norm]
  have hd_lt := hδ_d y hy
  rw [dist_eq_norm] at hd_lt
  have hmod_d : PadicInt.toZModPow (N + 1) (diamond y) = PadicInt.toZModPow (N + 1) (diamond x) :=
    padicInt_toZModPow_eq_of_norm_le_pow hd_lt.le
  have hmod_log : PadicInt.toZModPow N (padicLogBase hp2 (diamond y)) =
      PadicInt.toZModPow N (padicLogBase hp2 (diamond x)) := by
    rw [padicInt_toZModPow_padicLogBase hp2 N (toZMod_diamond hp2 y),
      padicInt_toZModPow_padicLogBase hp2 N (toZMod_diamond hp2 x)]
    simp only [padicLogLevel, hmod_d]
  exact (padicInt_norm_le_pow_of_toZModPow_eq hmod_log).trans_lt hN

/-- Norm of `padicPowOneAdd p s - 1` is `< 1` for all `s : ℤ_[p]`. -/
lemma norm_padicPowOneAdd_prime_sub_one_lt_one (s : ℤ_[p]) :
    ‖padicPowOneAdd (p : ℤ_[p]) s - 1‖ < 1 := by
  have hp : p.Prime := Fact.out
  have hp_lt1 : ‖(p : ℤ_[p])‖ < 1 := by
    change ‖(p : ℚ_[p])‖ < 1; rw [Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hbd := norm_padicPowOneAdd_sub_trunc_le hp_lt1 s 1
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one, mahlerBinom_zero, pow_one] at hbd
  exact hbd.trans_lt hp_lt1

/-- Exact exponent-multiplication law:
`padicPowOneAdd ((1 + p)^s - 1) t = (1 + p)^(s * t)` for all `s, t : ℤ_[p]`! -/
theorem padicPowOneAdd_mul_exp (s t : ℤ_[p]) :
    padicPowOneAdd (padicPowOneAdd (p : ℤ_[p]) s - 1) t = padicPowOneAdd (p : ℤ_[p]) (s * t) := by
  have hp : p.Prime := Fact.out
  have hp_lt1 : ‖(p : ℤ_[p])‖ < 1 := by
    change ‖(p : ℚ_[p])‖ < 1; rw [Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hys : ‖padicPowOneAdd (p : ℤ_[p]) s - 1‖ < 1 := norm_padicPowOneAdd_prime_sub_one_lt_one s
  have hL : Continuous (fun z : ℤ_[p] => padicPowOneAdd (padicPowOneAdd (p : ℤ_[p]) s - 1) z) :=
    continuous_padicPowOneAdd hys
  have hR : Continuous (fun z : ℤ_[p] => padicPowOneAdd (p : ℤ_[p]) (s * z)) :=
    (continuous_padicPowOneAdd hp_lt1).comp (continuous_const.mul continuous_id)
  have heq := PadicInt.denseRange_natCast.equalizer hL hR (by
    ext n
    dsimp only [Function.comp_apply]
    rw [padicPowOneAdd_natCast, add_sub_cancel]
    induction n with
    | zero =>
      simp only [pow_zero, Nat.cast_zero, mul_zero]
      have h0 := padicPowOneAdd_natCast (p := p) (y := (p : ℤ_[p])) 0
      simpa using h0.symm
    | succ n ih =>
      rw [pow_succ, ih, Nat.cast_succ, mul_add, mul_one, padicPowOneAdd_add hp_lt1])
  exact congrFun heq t

end TeichmullerAndLog

/-! ### Concrete Kubota–Leopoldt Iwasawa Power Series & $p$-adic Zeta Function `ζ_p(1 - k)` -/

section KubotaLeopoldtZeta

variable (p : ℕ) [Fact p.Prime]

/-- Weighting a $p$-adic measure `μ` by a continuous function `w : ℤ_[p] → ℤ_[p]`:
`(w • μ)(U) = ∫_U w dμ`. -/
def weightMeasure (w : ℤ_[p] → ℤ_[p]) (hw : Continuous w) (μ : PadicMeasure p) : PadicMeasure p where
  toFun n a := measureIntegral μ (fun x => w x * ballIndicator n a x)
  compat n a := by
    have hcont : ∀ b : ZMod (p ^ (n + 1)),
        Continuous (fun x => w x * ballIndicator (p := p) (n + 1) b x) :=
      fun b => hw.mul (continuous_ballIndicator (n + 1) b)
    rw [← measureIntegral_sum_fun _ μ _ (fun b _ => hcont b)]
    congr 1
    ext x
    rw [← Finset.mul_sum]
    congr 1
    by_cases h : PadicInt.toZModPow n x = a
    · simp only [ballIndicator, if_pos h]
      rw [Finset.sum_eq_single (PadicInt.toZModPow (n + 1) x)]
      · simp
      · intro b _ hb; simp [hb.symm]
      · intro hnot; exfalso; apply hnot
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [zmodPowStep, zmodPowCast_toZModPow (Nat.le_succ n), h]
    · simp only [ballIndicator, if_neg h]
      symm
      refine Finset.sum_eq_zero fun b hb => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      have hne : PadicInt.toZModPow (n + 1) x ≠ b := by
        intro heq; apply h
        have hstep := zmodPowCast_toZModPow (p := p) (Nat.le_succ n) x
        rw [heq] at hstep; exact hstep.symm.trans hb
      simp [hne]

theorem measureIntegral_weightMeasure {w : ℤ_[p] → ℤ_[p]} (hw : Continuous w)
    (μ : PadicMeasure p) {g : ℤ_[p] → ℤ_[p]} (hg : Continuous g) :
    measureIntegral (weightMeasure p w hw μ) g = measureIntegral μ (fun x => w x * g x) := by
  refine padicInt_eq_of_forall_norm_le_pow fun m => ?_
  have hp_pos : (0 : ℝ) < (p : ℝ) ^ (-(m : ℤ)) :=
    zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  obtain ⟨N, hN⟩ := exists_level_of_continuous hg ((p : ℝ) ^ (-(m : ℤ))) hp_pos
  have h1 := norm_measureIntegral_sub_riemannSum_le (weightMeasure p w hw μ) hg N hp_pos.le hN
  have hsum_eq : riemannSum (weightMeasure p w hw μ) g N =
      measureIntegral μ (fun x => w x * ∑ a : ZMod (p ^ N), g (a.val : ℤ_[p]) * ballIndicator N a x) := by
    have hfun : (fun x => w x * ∑ a : ZMod (p ^ N), g (a.val : ℤ_[p]) * ballIndicator N a x) =
        fun x => ∑ a : ZMod (p ^ N), g (a.val : ℤ_[p]) * (w x * ballIndicator N a x) := by
      ext x; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => by ring
    rw [hfun, measureIntegral_sum_fun]
    · unfold riemannSum weightMeasure
      refine Finset.sum_congr rfl fun a _ => ?_
      exact (measureIntegral_smul_fun μ (g (a.val : ℤ_[p])) (hw.mul (continuous_ballIndicator N a))).symm
    · intro a _; exact continuous_const.mul (hw.mul (continuous_ballIndicator N a))
  have h2 : ‖measureIntegral μ (fun x => w x * ∑ a : ZMod (p ^ N), g (a.val : ℤ_[p]) * ballIndicator N a x) -
      measureIntegral μ (fun x => w x * g x)‖ ≤ (p : ℝ) ^ (-(m : ℤ)) := by
    have hf1 : Continuous (fun x => w x * ∑ a : ZMod (p ^ N), g (a.val : ℤ_[p]) * ballIndicator N a x) :=
      hw.mul (continuous_finsetSum _ fun a _ => continuous_const.mul (continuous_ballIndicator N a))
    refine norm_measureIntegral_sub_le μ hf1 (hw.mul hg) hp_pos.le fun x => ?_
    change ‖w x * (∑ a : ZMod (p ^ N), g (a.val : ℤ_[p]) * ballIndicator N a x) - w x * g x‖ ≤ _
    have heval : ∑ a : ZMod (p ^ N), g (a.val : ℤ_[p]) * ballIndicator N a x =
        g ((PadicInt.toZModPow N x).val : ℤ_[p]) := by
      rw [Finset.sum_eq_single (PadicInt.toZModPow N x)]
      · simp [ballIndicator]
      · intro a _ ha; simp [ballIndicator, ha.symm]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [heval, ← mul_sub, norm_mul]
    have hmod : PadicInt.toZModPow N ((PadicInt.toZModPow N x).val : ℤ_[p]) = PadicInt.toZModPow N x := by
      have : NeZero (p ^ N) := ⟨pow_ne_zero N (Fact.out : p.Prime).ne_zero⟩
      rw [map_natCast, ZMod.natCast_zmod_val]
    calc ‖w x‖ * ‖g ((PadicInt.toZModPow N x).val : ℤ_[p]) - g x‖
        ≤ 1 * (p : ℝ) ^ (-(m : ℤ)) :=
          mul_le_mul (PadicInt.norm_le_one _) (hN _ _ hmod) (norm_nonneg _) zero_le_one
      _ = (p : ℝ) ^ (-(m : ℤ)) := one_mul _
  have hdecomp : measureIntegral (weightMeasure p w hw μ) g - measureIntegral μ (fun x => w x * g x) =
      (measureIntegral (weightMeasure p w hw μ) g - riemannSum (weightMeasure p w hw μ) g N) +
      (riemannSum (weightMeasure p w hw μ) g N - measureIntegral μ (fun x => w x * g x)) := by ring
  rw [hdecomp]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ?_)
  rwa [hsum_eq]

/-- **Concrete Kubota–Leopoldt Iwasawa Power Series** `G_{c, i}(T) ∈ ℤ_[p][[T]]` (for odd prime `p`,
regularizing parameter `c` coprime to `p`, and Teichmüller branch `i : ℕ`):
defined as the Amice–Mahler–Iwasawa transform of the pushforward of `ω^i • μ_c|_{ℤ_[p]ˣ}` along
`x ↦ log_{1+p}(⟨x⟩)`. -/
def kubotaLeopoldtSeries (hp2 : p ≠ 2) (c : ℕ) (hc : ¬ p ∣ c) (i : ℕ) : IwasawaAlg p :=
  iwasawaTransform
    (pushforwardMeasure (fun x : ℤ_[p] => padicLogBase hp2 (diamond x))
      (continuous_padicLogBase_diamond hp2)
      (weightMeasure p (fun x : ℤ_[p] => teichmuller x ^ i)
        (continuous_teichmuller.pow i)
        (mazurBernoulliMeasure p c hc).restrictUnits))

/-- **Concrete Kubota–Leopoldt $p$-adic Zeta Function** `ζ_{p, ω^{i+1}}(1 - (s + 1))` (for odd
prime `p`, `c ≥ 2` coprime to `p`, branch `i : ℕ`, evaluated at `T = (1 + p)^s - 1`):
interpolates `-(1 - p^k) B_{k+1}/(k + 1) = (1 - p^k) ζ(-k)` at all `k ≥ 1` with `k ≡ i [MOD p - 1]`! -/
def kubotaLeopoldtZeta (hp2 : p ≠ 2) (c : ℕ) (hc : ¬ p ∣ c) (i : ℕ) (s : ℤ_[p]) : ℚ_[p] :=
  - ((evalIwasawa (kubotaLeopoldtSeries p hp2 c hc i) (padicPowOneAdd (p : ℤ_[p]) s - 1) : ℤ_[p]) : ℚ_[p]) /
    (1 - (c : ℚ_[p]) * ((teichmuller (c : ℤ_[p]) ^ i : ℤ_[p]) : ℚ_[p]) *
      ((padicPowOneAdd (diamond (c : ℤ_[p]) - 1) s : ℤ_[p]) : ℚ_[p]))

/-- Exact numerator evaluation of `kubotaLeopoldtSeries` at `T = (1 + p)^k - 1` for `k ≡ i [MOD p - 1]`. -/
theorem evalIwasawa_kubotaLeopoldtSeries_nat (hp2 : p ≠ 2) (c : ℕ) (hc : ¬ p ∣ c)
    (i k : ℕ) (hki : k ≡ i [MOD (p - 1)]) :
    ((evalIwasawa (kubotaLeopoldtSeries p hp2 c hc i)
        (padicPowOneAdd (p : ℤ_[p]) (k : ℤ_[p]) - 1) : ℤ_[p]) : ℚ_[p]) =
      (((1 - (p : ℚ) ^ k) * (1 - (c : ℚ) ^ (k + 1)) *
        (bernoulli (k + 1) / ((k + 1 : ℕ) : ℚ)) : ℚ) : ℚ_[p]) := by
  have hy : ‖padicPowOneAdd (p : ℤ_[p]) (k : ℤ_[p]) - 1‖ < 1 :=
    norm_padicPowOneAdd_prime_sub_one_lt_one (k : ℤ_[p])
  unfold kubotaLeopoldtSeries
  have hwm := measureIntegral_weightMeasure p (w := fun x : ℤ_[p] => teichmuller x ^ i)
    (continuous_teichmuller.pow i) (mazurBernoulliMeasure p c hc).restrictUnits
    (g := fun x : ℤ_[p] => padicPowOneAdd (padicPowOneAdd (p : ℤ_[p]) (k : ℤ_[p]) - 1)
      (padicLogBase hp2 (diamond x)))
    ((continuous_padicPowOneAdd hy).comp (continuous_padicLogBase_diamond hp2))
  rw [evalIwasawa_iwasawaTransform _ hy,
    measureIntegral_pushforward _ _ (continuous_padicPowOneAdd hy), hwm]
  have hfun_eq : ∀ x : ℤ_[p], PadicInt.toZMod x ≠ 0 →
      teichmuller x ^ i * padicPowOneAdd (padicPowOneAdd (p : ℤ_[p]) (k : ℤ_[p]) - 1)
        (padicLogBase hp2 (diamond x)) = x ^ k := by
    intro x hx
    rw [padicPowOneAdd_mul_exp, mul_comm (k : ℤ_[p]), ← padicPowOneAdd_mul_exp,
      padicPowOneAdd_padicLogBase hp2 (toZMod_diamond hp2 x), padicPowOneAdd_natCast, add_sub_cancel]
    have hteich_eq : teichmuller x ^ i = teichmuller x ^ k := by
      have h1 : teichmuller x ^ (p - 1) = 1 := teichmuller_pow_sub_one hx
      rcases le_total i k with hle | hle
      · obtain ⟨q, hq⟩ := (Nat.modEq_iff_dvd' hle).mp hki.symm
        have hk : k = i + (p - 1) * q := by omega
        rw [hk, pow_add, pow_mul, h1, one_pow, mul_one]
      · obtain ⟨q, hq⟩ := (Nat.modEq_iff_dvd' hle).mp hki
        have hi : i = k + (p - 1) * q := by omega
        rw [hi, pow_add, pow_mul, h1, one_pow, mul_one]
    rw [hteich_eq, ← mul_pow, teichmuller_mul_diamond hp2 hx]
  have hint_eq :
      measureIntegral (mazurBernoulliMeasure p c hc).restrictUnits
        (fun x : ℤ_[p] => teichmuller x ^ i *
          padicPowOneAdd (padicPowOneAdd (p : ℤ_[p]) (k : ℤ_[p]) - 1) (padicLogBase hp2 (diamond x))) =
      measureIntegral (mazurBernoulliMeasure p c hc).restrictUnits (fun x : ℤ_[p] => x ^ k) := by
    have hcont_f : Continuous (fun x : ℤ_[p] => teichmuller x ^ i *
        padicPowOneAdd (padicPowOneAdd (p : ℤ_[p]) (k : ℤ_[p]) - 1) (padicLogBase hp2 (diamond x))) :=
      (continuous_teichmuller.pow i).mul
        ((continuous_padicPowOneAdd hy).comp (continuous_padicLogBase_diamond hp2))
    have h0 : ‖measureIntegral (mazurBernoulliMeasure p c hc).restrictUnits
        (fun x : ℤ_[p] => teichmuller x ^ i *
          padicPowOneAdd (padicPowOneAdd (p : ℤ_[p]) (k : ℤ_[p]) - 1) (padicLogBase hp2 (diamond x))) -
        measureIntegral (mazurBernoulliMeasure p c hc).restrictUnits (fun x : ℤ_[p] => x ^ k)‖ ≤ 0 :=
      norm_measureIntegral_restrictUnits_sub_le _ hcont_f
        (continuous_pow k) le_rfl (fun x hx => by rw [hfun_eq x hx, sub_self, norm_zero])
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h0 (norm_nonneg _)))
  rw [hint_eq]
  exact mazurBernoulliMeasure_restrictUnits_moment p c hc k

/-- **UNCONDITIONAL KUBOTA–LEOPOLDT INTERPOLATION THEOREM**:
for EVERY odd prime `p`, EVERY `c ≥ 2` with `¬ p ∣ c`, EVERY branch `i : ℕ`, and EVERY `k ≥ 1`
with `k ≡ i [MOD p - 1]`,
`ζ_p(1 - (k + 1)) = kubotaLeopoldtZeta p hp2 c hc i k = -(1 - p^k) * B_{k+1} / (k + 1)`! -/
theorem kubotaLeopoldtZeta_eval_nat (hp2 : p ≠ 2) {c : ℕ} (hc2 : 2 ≤ c) (hc : ¬ p ∣ c)
    (i k : ℕ) (hki : k ≡ i [MOD (p - 1)]) :
    kubotaLeopoldtZeta p hp2 c hc i (k : ℤ_[p]) =
      - (((1 - (p : ℚ) ^ k) * (bernoulli (k + 1) / ((k + 1 : ℕ) : ℚ)) : ℚ) : ℚ_[p]) := by
  unfold kubotaLeopoldtZeta
  rw [evalIwasawa_kubotaLeopoldtSeries_nat p hp2 c hc i k hki]
  have hc_res : PadicInt.toZMod (c : ℤ_[p]) ≠ 0 := by
    rw [map_natCast, Ne, ZMod.natCast_eq_zero_iff]; exact hc
  have hteich_c : teichmuller (c : ℤ_[p]) ^ i = teichmuller (c : ℤ_[p]) ^ k := by
    have h1 : teichmuller (c : ℤ_[p]) ^ (p - 1) = 1 := teichmuller_pow_sub_one hc_res
    rcases le_total i k with hle | hle
    · obtain ⟨q, hq⟩ := (Nat.modEq_iff_dvd' hle).mp hki.symm
      have hk : k = i + (p - 1) * q := by omega
      rw [hk, pow_add, pow_mul, h1, one_pow, mul_one]
    · obtain ⟨q, hq⟩ := (Nat.modEq_iff_dvd' hle).mp hki
      have hi : i = k + (p - 1) * q := by omega
      rw [hi, pow_add, pow_mul, h1, one_pow, mul_one]
  have hden_eq :
      (1 : ℚ_[p]) - (c : ℚ_[p]) * ((teichmuller (c : ℤ_[p]) ^ i : ℤ_[p]) : ℚ_[p]) *
        ((padicPowOneAdd (diamond (c : ℤ_[p]) - 1) (k : ℤ_[p]) : ℤ_[p]) : ℚ_[p]) =
      (((1 - (c : ℚ) ^ (k + 1)) : ℚ) : ℚ_[p]) := by
    have hmul_c : ((teichmuller (c : ℤ_[p]) ^ k : ℤ_[p]) : ℚ_[p]) *
        ((diamond (c : ℤ_[p]) ^ k : ℤ_[p]) : ℚ_[p]) =
        (((teichmuller (c : ℤ_[p]) * diamond (c : ℤ_[p])) ^ k : ℤ_[p]) : ℚ_[p]) := by
      rw [mul_pow, PadicInt.coe_mul]
    rw [hteich_c, padicPowOneAdd_natCast, add_sub_cancel, mul_assoc (c : ℚ_[p]), hmul_c,
      teichmuller_mul_diamond hp2 hc_res, PadicInt.coe_pow, PadicInt.coe_natCast, ← pow_succ']
    push_cast; ring
  have hden_ne : (((1 - (c : ℚ) ^ (k + 1)) : ℚ) : ℚ_[p]) ≠ 0 := by
    have hneQ : (1 - (c : ℚ) ^ (k + 1) : ℚ) ≠ 0 := by
      have hgt : (1 : ℚ) < (c : ℚ) ^ (k + 1) := one_lt_pow₀ (by exact_mod_cast (by omega : 1 < c)) (Nat.succ_ne_zero k)
      linarith
    exact_mod_cast hneQ
  rw [hden_eq]
  have hnum_eq :
      - ((((1 - (p : ℚ) ^ k) * (1 - (c : ℚ) ^ (k + 1)) *
        (bernoulli (k + 1) / ((k + 1 : ℕ) : ℚ)) : ℚ) : ℚ_[p])) =
      (- (((1 - (p : ℚ) ^ k) * (bernoulli (k + 1) / ((k + 1 : ℕ) : ℚ)) : ℚ) : ℚ_[p])) *
        (((1 - (c : ℚ) ^ (k + 1)) : ℚ) : ℚ_[p]) := by
    push_cast; ring
  rw [hnum_eq, mul_div_cancel_right₀ _ hden_ne]

/-- Independence of `kubotaLeopoldtZeta` from the choice of regularizing parameter `c ≥ 2` at all
interpolated integers `k ≡ i [MOD p - 1]`. -/
theorem kubotaLeopoldtZeta_indep_c (hp2 : p ≠ 2) {c₁ c₂ : ℕ}
    (hc₁2 : 2 ≤ c₁) (hc₁ : ¬ p ∣ c₁) (hc₂2 : 2 ≤ c₂) (hc₂ : ¬ p ∣ c₂)
    (i k : ℕ) (hki : k ≡ i [MOD (p - 1)]) :
    kubotaLeopoldtZeta p hp2 c₁ hc₁ i (k : ℤ_[p]) =
      kubotaLeopoldtZeta p hp2 c₂ hc₂ i (k : ℤ_[p]) := by
  rw [kubotaLeopoldtZeta_eval_nat p hp2 hc₁2 hc₁ i k hki,
    kubotaLeopoldtZeta_eval_nat p hp2 hc₂2 hc₂ i k hki]

end KubotaLeopoldtZeta

end KummerAndKubotaLeopoldt

end RHDirect.Stage7PadicLFunction
