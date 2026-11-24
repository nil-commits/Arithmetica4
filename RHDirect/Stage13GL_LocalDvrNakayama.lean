import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.FiniteLength
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Module.SnakeLemma
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.MahlerBasis
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Semisimple
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.Topology.MetricSpace.Perfect
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Group.Units

/-!
# RHDirect.Stage13GL_LocalDvrNakayama

Unconditional Lean 4 formalization (`0 sorry`, `0 custom axioms`, `0 opaque`, `0 native_decide`)
consolidating local-ring adic completion, DVR structure & integral closure, power-series
Weierstrass preparation / `μ`-`λ` invariants, Nakayama's lemma, `p`-adic lifting the exponent,
snake-lemma module lengths, isotypic submodule descent, finite-order matrix diagonalization,
conjugate integrality criteria, and `ℚ̄` / `PadicAlgCl` / `ℂ` arithmetic bridges directly on
concrete Mathlib types.
-/

noncomputable section

namespace RHDirect.Stage13GL_LocalDvrNakayama

open PowerSeries IsLocalRing
open IsDiscreteValuationRing (addVal)
open scoped Pointwise TensorProduct Topology Matrix

/-! ## Section 1: Adic Power Series Lift, One-Units, Evaluation & Iwasawa Invariants -/

section Lift

variable {O R : Type*} [CommRing O] [CommRing R] [Algebra O R]

theorem aeval_sub_mem {I : Ideal R} {x : R} (hx : x ∈ I) {p q : Polynomial O} {n : ℕ}
    (h : ∀ i < n, p.coeff i = q.coeff i) : Polynomial.aeval x p - Polynomial.aeval x q ∈ I ^ n := by
  obtain ⟨r, hr⟩ : Polynomial.X ^ n ∣ p - q := Polynomial.X_pow_dvd_iff.2 fun i hi => by simp [h i hi]
  rw [← map_sub, hr, map_mul, map_pow, Polynomial.aeval_X]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hx n)

theorem eq_of_sub_mem_pow (I : Ideal R) [IsHausdorff I R] {a b : R} (h : ∀ n, a - b ∈ I ^ n) : a = b :=
  sub_eq_zero.mp <| IsHausdorff.haus ‹IsHausdorff I R› (a - b) fun n => by
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]; exact h n

theorem exists_lim (I : Ideal R) [IsAdicComplete I R] (x : I) (f : O⟦X⟧) :
    ∃ y : R, ∀ n, y - Polynomial.aeval (x : R) (trunc n f) ∈ I ^ n := by
  obtain ⟨y, hy⟩ := IsPrecomplete.prec' (I := I) (fun n => Polynomial.aeval (x : R) (trunc n f))
    fun {m n} hmn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      exact aeval_sub_mem x.2 fun i hi => by simp [coeff_trunc, hi, hi.trans_le hmn]
  exact ⟨y, fun n => by have := (hy n).symm; rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this⟩

def lift (I : Ideal R) [IsAdicComplete I R] (x : I) : O⟦X⟧ →ₐ[O] R where
  toFun f := (exists_lim I x f).choose
  map_one' := eq_of_sub_mem_pow I fun n => by
    simpa using (I ^ n).add_mem ((exists_lim I x (1 : O⟦X⟧)).choose_spec n)
      (aeval_sub_mem (p := trunc n 1) (q := (1 : Polynomial O)) x.2 fun i hi => by
        simp [coeff_trunc, hi, coeff_one, Polynomial.coeff_one])
  map_mul' f g := eq_of_sub_mem_pow I fun n => by
    have h4 := aeval_sub_mem (p := trunc n (f * g)) (q := trunc n f * trunc n g) (n := n) x.2 fun i hi => by
      rw [coeff_trunc, if_pos hi, ← Polynomial.coeff_coe, Polynomial.coe_mul, coeff_mul_eq_coeff_trunc_mul_trunc _ _ hi]
    have h := (I ^ n).sub_mem ((I ^ n).sub_mem ((I ^ n).add_mem ((exists_lim I x (f * g)).choose_spec n) h4)
      (Ideal.mul_mem_right (exists_lim I x g).choose _ ((exists_lim I x f).choose_spec n)))
      (Ideal.mul_mem_left _ (Polynomial.aeval (x : R) (trunc n f)) ((exists_lim I x g).choose_spec n))
    rw [map_mul (Polynomial.aeval (x : R))] at h; convert h using 1; ring
  map_zero' := eq_of_sub_mem_pow I fun n => by simpa using (exists_lim I x (0 : O⟦X⟧)).choose_spec n
  map_add' f g := eq_of_sub_mem_pow I fun n => by
    have h := (I ^ n).sub_mem ((I ^ n).sub_mem ((exists_lim I x (f + g)).choose_spec n)
      ((exists_lim I x f).choose_spec n)) ((exists_lim I x g).choose_spec n)
    rw [map_add, map_add] at h; convert h using 1; ring
  commutes' r := eq_of_sub_mem_pow I fun n => by
    simpa using (I ^ n).add_mem ((exists_lim I x (algebraMap O O⟦X⟧ r)).choose_spec n)
      (aeval_sub_mem (p := trunc n (algebraMap O O⟦X⟧ r)) (q := Polynomial.C r) x.2 fun i hi => by
        simp [coeff_trunc, hi, coeff_C, Polynomial.coeff_C])

theorem lift_sub_trunc_mem (I : Ideal R) [IsAdicComplete I R] (x : I) (f : O⟦X⟧) (n : ℕ) :
    lift I x f - Polynomial.aeval (x : R) (trunc n f) ∈ I ^ n := (exists_lim I x f).choose_spec n

theorem lift_coe (I : Ideal R) [IsAdicComplete I R] (x : I) (p : Polynomial O) :
    lift I x (p : O⟦X⟧) = Polynomial.aeval (x : R) p :=
  eq_of_sub_mem_pow I fun n => by
    simpa using (I ^ n).add_mem (lift_sub_trunc_mem I x (p : O⟦X⟧) n)
      (aeval_sub_mem (p := trunc n (p : O⟦X⟧)) (q := p) x.2 fun i hi => by simp [coeff_trunc, hi])

@[simp] theorem lift_X (I : Ideal R) [IsAdicComplete I R] (x : I) : lift I x (X : O⟦X⟧) = x := by
  simpa using lift_coe I x (Polynomial.X : Polynomial O)

@[simp] theorem lift_C (I : Ideal R) [IsAdicComplete I R] (x : I) (r : O) :
    lift I x (C r) = algebraMap O R r := (lift I x).commutes r

theorem algHom_ext (I : Ideal R) [IsHausdorff I R] {φ ψ : O⟦X⟧ →ₐ[O] R} (hI : φ X ∈ I)
    (h : φ X = ψ X) : φ = ψ := by
  refine AlgHom.ext fun f => eq_of_sub_mem_pow I fun n => ?_
  obtain ⟨g, hg⟩ : (X : O⟦X⟧) ^ n ∣ f - (trunc n f : O⟦X⟧) := X_pow_dvd_iff.2 fun i hi => by simp [coeff_trunc, hi]
  have hp : φ (trunc n f : O⟦X⟧) = ψ (trunc n f : O⟦X⟧) := by
    have : φ.comp (Polynomial.coeToPowerSeries.algHom O) = ψ.comp (Polynomial.coeToPowerSeries.algHom O) :=
      Polynomial.algHom_ext (by simpa using h)
    simpa using DFunLike.congr_fun this (trunc n f)
  have : φ f - ψ f = φ X ^ n * (φ g - ψ g) := by
    rw [sub_eq_iff_eq_add.1 hg]; simp only [map_add, map_mul, map_pow, hp, h]; ring
  rw [this]; exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hI n)

end Lift

section Local

variable {O : Type*} [CommRing O] [IsLocalRing O]

def oneUnits (O : Type*) [CommRing O] [IsLocalRing O] : Subgroup Oˣ where
  carrier := {u | (u : O) - 1 ∈ maximalIdeal O}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by simpa [sub_mul] using (maximalIdeal O).add_mem (Ideal.mul_mem_right (b : O) _ ha) hb
  inv_mem' {a} ha := by simpa [sub_mul] using (maximalIdeal O).neg_mem (Ideal.mul_mem_right ((a⁻¹ : Oˣ) : O) _ ha)

def pt {O : Type*} [CommRing O] [IsLocalRing O] (u : oneUnits O) : maximalIdeal O := ⟨((u : Oˣ) : O) - 1, u.2⟩

@[simp] theorem coe_pt (u : oneUnits O) : (pt u : O) = ((u : Oˣ) : O) - 1 := rfl

def ofPt {O : Type*} [CommRing O] [IsLocalRing O] (a : maximalIdeal O) : oneUnits O :=
  ⟨(IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-(a : O)) ((maximalIdeal O).neg_mem a.2)).unit, by
    change _ - 1 ∈ maximalIdeal O; simp⟩

@[simp] theorem pt_ofPt (a : maximalIdeal O) : pt (ofPt a) = a := Subtype.ext (by simp [ofPt])

def ev [IsAdicComplete (maximalIdeal O) O] (a : maximalIdeal O) : O⟦X⟧ →ₐ[O] O := lift (maximalIdeal O) a

@[simp] theorem ev_X [IsAdicComplete (maximalIdeal O) O] (a : maximalIdeal O) : ev a X = a := lift_X _ a
@[simp] theorem ev_C [IsAdicComplete (maximalIdeal O) O] (a : maximalIdeal O) (r : O) : ev a (C r) = r := lift_C _ a r

def upow [IsAdicComplete (maximalIdeal O) O] {l : ℕ} [Fact l.Prime] [Algebra ℤ_[l] O]
    (u : oneUnits O) (s : ℤ_[l]) : O := ev (pt u) (binomialSeries O s)

end Local

section MuLam

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def mu (f : O⟦X⟧) : ℕ∞ := ⨅ n, IsDiscreteValuationRing.addVal O (coeff n f)

def lam (f : O⟦X⟧) : ℕ := sInf {n | IsDiscreteValuationRing.addVal O (coeff n f) = mu f}

theorem mu_le (f : O⟦X⟧) (n : ℕ) : mu f ≤ IsDiscreteValuationRing.addVal O (coeff n f) := iInf_le _ n

theorem addVal_coeff_lam (f : O⟦X⟧) : IsDiscreteValuationRing.addVal O (coeff (lam f) f) = mu f := by
  have hne : {n | IsDiscreteValuationRing.addVal O (coeff n f) = mu f}.Nonempty := by
    obtain ⟨n, hn⟩ := csInf_mem (Set.range_nonempty fun n => IsDiscreteValuationRing.addVal O (coeff n f))
    exact ⟨n, hn⟩
  exact Nat.sInf_mem hne

theorem mu_eq_top_iff {f : O⟦X⟧} : mu f = ⊤ ↔ f = 0 := by
  unfold mu
  rw [iInf_eq_top, PowerSeries.ext_iff]
  simp [IsDiscreteValuationRing.addVal_eq_top_iff]

end MuLam

def omega (R : Type*) [CommRing R] (l n : ℕ) : Polynomial R := (1 + Polynomial.X) ^ (l ^ n) - 1

section Char

variable {R : Type*} [CommRing R]

def locLen (P : Ideal R) [P.IsPrime] (M : Type*) [AddCommGroup M] [Module R M] : ℕ∞ :=
  Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M)

def IsChar (M : Type*) [AddCommGroup M] [Module R M] (f : R) : Prop :=
  f ≠ 0 ∧ ∀ (p : R) (P : Ideal R) [P.IsPrime], p ≠ 0 → P = Ideal.span {p} → locLen P M = emultiplicity p f

def IsPseudoIso {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φ : M →ₗ[R] N) : Prop :=
  Module.length R (LinearMap.ker φ) ≠ ⊤ ∧ Module.length R (N ⧸ LinearMap.range φ) ≠ ⊤

def coinvLen (g : R) (M : Type*) [AddCommGroup M] [Module R M] : ℕ∞ :=
  Module.length R (QuotSMulTop g M)

def invLen (g : R) (M : Type*) [AddCommGroup M] [Module R M] : ℕ∞ :=
  Module.length R (Submodule.torsionBy R M g)

def interLen (f g : R) : ℕ∞ := Module.length R (R ⧸ Ideal.span {f, g})

end Char

/-! ## Section 2: Power Series Maximal Ideal, Adic Completeness & Weierstrass Preparation -/

private theorem mem_max_iff {O : Type*} [CommRing O] [IsLocalRing O] (f : O⟦X⟧) :
    f ∈ maximalIdeal O⟦X⟧ ↔ constantCoeff f ∈ maximalIdeal O := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
    PowerSeries.isUnit_iff_constantCoeff]

private theorem C_mem_pow {O : Type*} [CommRing O] [IsLocalRing O] (k : ℕ) (a : O)
    (ha : a ∈ maximalIdeal O ^ k) : (C a : O⟦X⟧) ∈ maximalIdeal O⟦X⟧ ^ k := by
  have h1 : Ideal.map (C : O →+* O⟦X⟧) (maximalIdeal O) ≤ maximalIdeal O⟦X⟧ :=
    Ideal.map_le_iff_le_comap.2 fun x hx => by rw [Ideal.mem_comap, mem_max_iff]; simpa using hx
  exact Ideal.pow_right_mono h1 k (Ideal.map_pow (C : O →+* O⟦X⟧) _ k ▸ Ideal.mem_map_of_mem _ ha)

theorem mem_max_pow :
    ∀ (O : Type*) [CommRing O] [IsLocalRing O] (f : O⟦X⟧) (n : ℕ),
      f ∈ maximalIdeal O⟦X⟧ ^ n ↔ ∀ i, coeff i f ∈ maximalIdeal O ^ (n - i) := by
  intro O _ _ f n
  refine ⟨fun hf => ?_, fun h => ?_⟩
  · induction n generalizing f with
    | zero => intro i; simp
    | succ n ih =>
      rw [pow_succ] at hf
      refine Submodule.mul_induction_on hf (fun a ha b hb i => ?_) fun x y hx hy i => ?_
      · rw [PowerSeries.coeff_mul]
        refine Ideal.sum_mem _ fun p hp => ?_
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
        have h2 : coeff p.2 b ∈ maximalIdeal O ^ (1 - p.2) := by
          rcases Nat.eq_zero_or_pos p.2 with h | h
          · rw [h, PowerSeries.coeff_zero_eq_constantCoeff_apply]; simpa using (mem_max_iff b).1 hb
          · rw [Nat.sub_eq_zero_of_le h]; simp
        have h3 := Ideal.mul_mem_mul (ih a ha p.1) h2
        rw [← pow_add] at h3; exact Ideal.pow_le_pow_right (by omega) h3
      · rw [map_add]; exact Ideal.add_mem _ (hx i) (hy i)
  · induction n generalizing f with
    | zero => simp
    | succ n ih =>
      rw [PowerSeries.eq_X_mul_shift_add_const f]
      refine Ideal.add_mem _ ?_ (C_mem_pow _ _ (by simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using h 0))
      rw [pow_succ']
      exact Ideal.mul_mem_mul ((mem_max_iff X).2 (by simp)) (ih _ fun i => by rw [PowerSeries.coeff_mk]; simpa using h (i + 1))

theorem adicComplete :
    ∀ (O : Type*) [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O],
      IsAdicComplete (maximalIdeal O⟦X⟧) O⟦X⟧ := by
  intro O _ _ _
  have key : ∀ (x y : O⟦X⟧) (n : ℕ),
      x ≡ y [SMOD (maximalIdeal O⟦X⟧) ^ n • (⊤ : Submodule O⟦X⟧ O⟦X⟧)] ↔
        ∀ i, coeff i x - coeff i y ∈ maximalIdeal O ^ (n - i) := fun x y n => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_max_pow]; simp only [map_sub]
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx; ext i; exact eq_of_sub_mem_pow (maximalIdeal O) fun n => by simpa using (key x 0 (n + i)).1 (hx (n + i)) i
  intro f hf
  have hc : ∀ i, ∃ L : O, ∀ n, coeff i (f (n + i)) - L ∈ maximalIdeal O ^ n := fun i => by
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := maximalIdeal O) (M := O) (fun m => coeff i (f (m + i))) fun {m n} hmn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      simpa using (key _ _ (m + i)).1 (hf (Nat.add_le_add_right hmn i)) i
    exact ⟨L, fun n => by have h := hL n; rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h⟩
  choose L hL using hc
  refine ⟨PowerSeries.mk L, fun n => (key _ _ n).2 fun i => ?_⟩
  rw [coeff_mk]
  rcases le_or_gt i n with hin | hin
  · have h := hL i (n - i); rwa [Nat.sub_add_cancel hin] at h
  · rw [Nat.sub_eq_zero_of_le hin.le, pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top

theorem mu_dvd (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ)
    (f : O⟦X⟧) :
    (∀ m : ℕ, (m : ℕ∞) ≤ mu f ↔ C ϖ ^ m ∣ f) ∧ (mu f = 0 ↔ map (residue O) f ≠ 0) ∧
      (mu f = 0 → lam f = (map (residue O) f).order.toNat) ∧
      ∀ m : ℕ, mu (C ϖ ^ m * f) = m + mu f ∧ lam (C ϖ ^ m * f) = lam f := by
  have hpow : ∀ m : ℕ, addVal O (ϖ ^ m) = m := fun m => by
    rw [IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ]; simp
  have hdvd : ∀ m : ℕ, C ϖ ^ m ∣ f ↔ ∀ n, ϖ ^ m ∣ coeff n f := fun m =>
    ⟨fun ⟨g, hg⟩ n => by rw [hg, ← map_pow, PowerSeries.coeff_C_mul]; exact dvd_mul_right _ _,
     fun h => by choose g hg using h; exact ⟨PowerSeries.mk g, PowerSeries.ext fun n => by rw [← map_pow, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, ← hg n]⟩⟩
  have h1 : ∀ m : ℕ, (m : ℕ∞) ≤ mu f ↔ C ϖ ^ m ∣ f := fun m => by
    rw [hdvd, mu, le_iInf_iff]; exact forall_congr' fun n => by rw [← hpow m, IsDiscreteValuationRing.addVal_le_iff_dvd]
  have hmu0 : mu f = 0 → map (residue O) f ≠ 0 := fun h hzero => by
    have hc := addVal_coeff_lam f
    rw [h, IsDiscreteValuationRing.addVal_eq_zero_iff, ← residue_ne_zero_iff_isUnit] at hc
    exact hc (by rw [← PowerSeries.coeff_map, hzero, map_zero])
  refine ⟨h1, ⟨hmu0, fun h => ?_⟩, fun h => ?_, fun m => ?_⟩
  · obtain ⟨n, hn⟩ : ∃ n, coeff n (map (residue O) f) ≠ 0 := by
      by_contra hall; push Not at hall; exact h (PowerSeries.ext fun n => by simpa using hall n)
    rw [PowerSeries.coeff_map, residue_ne_zero_iff_isUnit, ← IsDiscreteValuationRing.addVal_eq_zero_iff] at hn
    exact le_antisymm (hn ▸ mu_le f n) bot_le
  · have hord : (map (residue O) f).order = (lam f : ℕ∞) := by
      rw [PowerSeries.order_eq_nat]
      refine ⟨by rw [PowerSeries.coeff_map, residue_ne_zero_iff_isUnit, ← IsDiscreteValuationRing.addVal_eq_zero_iff, addVal_coeff_lam, h],
        fun i hi => ?_⟩
      rw [PowerSeries.coeff_map]; by_contra hne
      have hu : IsUnit (coeff i f) := (residue_ne_zero_iff_isUnit _).1 hne
      rw [← IsDiscreteValuationRing.addVal_eq_zero_iff] at hu
      have hli : lam f ≤ i := Nat.sInf_le (show addVal O (coeff i f) = mu f by rw [hu, h])
      omega
    rw [hord, ENat.toNat_natCast]
  · have hcoeff : ∀ n, addVal O (coeff n (C ϖ ^ m * f)) = m + addVal O (coeff n f) := fun n => by
      rw [← map_pow, PowerSeries.coeff_C_mul, IsDiscreteValuationRing.addVal_mul, hpow]
    have hmu : mu (C ϖ ^ m * f) = m + mu f := by rw [mu, mu, ENat.add_iInf]; exact iInf_congr hcoeff
    refine ⟨hmu, ?_⟩
    rw [lam, lam]; congr 1; ext n; simp only [Set.mem_ofPred_eq, hcoeff, hmu]
    exact ⟨fun h => WithTop.add_left_cancel (ENat.natCast_ne_top m) h, fun h => by rw [h]⟩

theorem weier (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    (ϖ : O) (hϖ : Irreducible ϖ) (f : O⟦X⟧) (hf : f ≠ 0) :
    ∃ (m : ℕ) (P : Polynomial O) (U : O⟦X⟧), mu f = m ∧ P.IsDistinguishedAt (maximalIdeal O) ∧ P.natDegree = lam f ∧
      IsUnit U ∧ f = C ϖ ^ m * (P : O⟦X⟧) * U := by
  have htop : mu f ≠ ⊤ := fun h => hf (mu_eq_top_iff.mp h)
  have hM := mu_dvd O ϖ hϖ
  obtain ⟨m, hmf⟩ : ∃ m : ℕ, (m : ℕ∞) = mu f := ⟨(mu f).toNat, ENat.natCast_toNat htop⟩
  obtain ⟨g, hgf⟩ := ((hM f).1 m).mp hmf.le
  subst hgf
  obtain ⟨-, hzero, hlam, hshift⟩ := hM g
  obtain ⟨hmu, hl⟩ := hshift m
  have hg0 : mu g = 0 := by
    have h1 : (m : ℕ∞) + mu g = (m : ℕ∞) + 0 := by rw [add_zero, ← hmu, hmf]
    exact (WithTop.add_left_cancel (ENat.natCast_ne_top m) h1)
  have hmap : (map (residue O)) g ≠ 0 := hzero.mp hg0
  obtain ⟨P, U, H⟩ := exists_isWeierstrassFactorization hmap
  refine ⟨m, P, U, hmf.symm, H.isDistinguishedAt, ?_, H.isUnit, ?_⟩
  · rw [hl, hlam hg0, H.natDegree_eq_toNat_order_map]
  · rw [mul_assoc, ← H.eq_mul]

/-! ## Section 3: DVR Finite Extensions, Integral Closure, Nakayama, LTE & Snake Length -/

private theorem isIntegral_iff_norm_le_one_bis {l : ℕ} [Fact l.Prime] {K : Type*} [Field K]
    [Algebra ℚ_[l] K] [Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
    (φ : K →ₐ[ℚ_[l]] PadicAlgCl l) (x : K) : IsIntegral ℤ_[l] x ↔ ‖φ x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖φ x‖ = spectralValue (minpoly ℚ_[l] (φ x)) := rfl
  rw [h0, minpoly.algHom_eq φ φ.injective, spectralValue_le_one_iff (minpoly.monic hi)]
  refine ⟨fun h n => by rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]; exact PadicInt.norm_le_one _,
    fun h => ?_⟩
  have hl' : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) :=
    (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
  exact ⟨q, hqm, by rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

theorem dvr_intClosure :
    ∀ (l : ℕ) [Fact l.Prime] (K : Type*) [Field K] [Algebra ℚ_[l] K] [Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K]
      [FiniteDimensional ℚ_[l] K],
      IsDiscreteValuationRing (integralClosure ℤ_[l] K) ∧ Module.Finite ℤ_[l] (integralClosure ℤ_[l] K) ∧
        IsFractionRing (integralClosure ℤ_[l] K) K := by
  intro l hl K _ _ _ _ _
  let φ : K →ₐ[ℚ_[l]] PadicAlgCl l := IsAlgClosed.lift
  have hint := isIntegral_iff_norm_le_one_bis φ
  have hunit : ∀ a : integralClosure ℤ_[l] K, ‖φ a‖ = 1 → IsUnit a := fun a ha => by
    have h0 : (a : K) ≠ 0 := fun h => by rw [h] at ha; simp at ha
    exact IsUnit.of_mul_eq_one (⟨_, (hint _).2 (by rw [map_inv₀, norm_inv, ha, inv_one])⟩ : integralClosure ℤ_[l] K)
      (Subtype.ext (mul_inv_cancel₀ h0))
  have hloc : IsLocalRing (integralClosure ℤ_[l] K) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    rcases ((hint _).1 a.2).eq_or_lt with h | h
    · exact Or.inl (hunit a h)
    · refine Or.inr (hunit _ (le_antisymm ((hint _).1 (1 - a).2) ?_))
      by_contra hlt; push Not at hlt
      have h1 : φ ((1 - a : integralClosure ℤ_[l] K) : K) + φ a = 1 := by simp
      have h2 := (PadicAlgCl.isNonarchimedean l _ _).trans_lt (max_lt hlt h)
      simp only [h1] at h2; simp at h2
  have hded : IsDedekindDomain (integralClosure ℤ_[l] K) :=
    IsIntegralClosure.isDedekindDomain ℤ_[l] ℚ_[l] K (integralClosure ℤ_[l] K)
  have hinj : Function.Injective (algebraMap ℤ_[l] (integralClosure ℤ_[l] K)) := fun a b hab => by
    have h := congrArg (fun x : integralClosure ℤ_[l] K => (x : K)) hab
    simp only [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] K] at h
    exact IsFractionRing.injective ℤ_[l] ℚ_[l] ((algebraMap ℚ_[l] K).injective h)
  have hnf : ¬ IsField (integralClosure ℤ_[l] K) := fun hf =>
    IsDiscreteValuationRing.not_isField ℤ_[l] ((Algebra.IsIntegral.isField_iff_isField hinj).2 hf)
  exact ⟨((IsDiscreteValuationRing.TFAE _ hnf).out 0 2).mpr hded,
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] K (integralClosure ℤ_[l] K),
    integralClosure.isFractionRing_of_finite_extension ℚ_[l] K⟩

private theorem mem_smul_top_iff_repr {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] (b : Module.Basis ι R M) (I : Ideal R) (x : M) :
    x ∈ I • (⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ I :=
  ⟨fun hx i => Submodule.smul_induction_on hx
      (fun r hr _ _ => by rw [map_smul, Finsupp.smul_apply, smul_eq_mul]; exact I.mul_mem_right _ hr)
      (fun _ _ ha hc => by rw [map_add, Finsupp.add_apply]; exact I.add_mem ha hc),
   fun h => b.sum_repr x ▸ Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) trivial⟩

private theorem prec_free {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (I : Ideal R) [IsPrecomplete I R] : IsPrecomplete I M := ⟨fun f hf => by
  let b := Module.Free.chooseBasis R M
  have key : ∀ i, ∃ L : R, ∀ k, b.repr (f k) i - L ∈ I ^ k := fun i => by
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) (fun k => b.repr (f k) i) fun {m n} hmn => by
      have h := hf hmn; rw [SModEq.sub_mem, mem_smul_top_iff_repr b] at h
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]; simpa using h i
    exact ⟨L, fun k => by have := hL k; rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this⟩
  choose L hL using key
  refine ⟨b.equivFun.symm L, fun n => ?_⟩
  rw [SModEq.sub_mem, mem_smul_top_iff_repr b]; intro i
  rw [map_sub, Finsupp.sub_apply, show b.repr (b.equivFun.symm L) i = L i from by
    rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]]
  exact hL i n⟩

private theorem prec_cofinal {R : Type*} [CommRing R] {I J : Ideal R} (hJI : J ≤ I) {e : ℕ}
    (he : I ^ e ≤ J) (hJ : IsPrecomplete J R) : IsPrecomplete I R := ⟨fun f hf => by
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hf ⊢
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := J) (fun k => f ((e + 1) * k)) fun {m n} hmn => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    have h := hf (Nat.mul_le_mul_left (e + 1) hmn); rw [pow_mul] at h
    exact Ideal.pow_right_mono ((Ideal.pow_le_pow_right (Nat.le_succ e)).trans he) m h
  refine ⟨L, fun n => ?_⟩
  have h1 := hL n; rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
  simpa using (I ^ n).add_mem (hf (m := n) (n := (e + 1) * n) (Nat.le_mul_of_pos_left n (Nat.succ_pos e)))
    (Ideal.pow_right_mono hJI n h1)⟩

theorem dvr_finite (l : ℕ) [hl : Fact l.Prime] (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] :
    IsAdicComplete (maximalIdeal O) O ∧ Finite (ResidueField O) ∧ (l : O) ∈ maximalIdeal O ∧
      Function.Injective (algebraMap ℤ_[l] O) ∧ Module.Free ℤ_[l] O ∧ IsLocalHom (algebraMap ℤ_[l] O) := by
  have hl0 : (l : O) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  have hinj : Function.Injective (algebraMap ℤ_[l] O) := (injective_iff_map_eq_zero _).2 fun x hx => by
    by_contra h0; rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hx
    exact mul_ne_zero ((PadicInt.unitCoeff h0).isUnit.map _).ne_zero (pow_ne_zero _ hl0) hx
  have : FaithfulSMul ℤ_[l] O := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have hlm : (l : O) ∈ maximalIdeal O := by
    have h : (l : ℤ_[l]) ∈ maximalIdeal ℤ_[l] := by rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
    have := map_nonunit (algebraMap ℤ_[l] O) _ h; rwa [map_natCast] at this
  have hres : Finite (ResidueField O) := by
    have : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField (p := l)).symm.toEquiv
    exact Module.finite_of_finite (ResidueField ℤ_[l])
  refine ⟨{ toIsHausdorff := inferInstance, toIsPrecomplete := ?_ }, hres, hlm, hinj,
    Module.free_of_finite_type_torsion_free', inferInstance⟩
  have h1 : IsPrecomplete ((maximalIdeal ℤ_[l]).map (algebraMap ℤ_[l] O)) O :=
    IsPrecomplete.map_algebraMap_iff.2 (prec_free _)
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast] at h1
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible (s := Ideal.span {(l : O)}) (by simpa using hl0) hϖ
  exact prec_cofinal ((Ideal.span_singleton_le_iff_mem _).2 hlm) (e := e)
    (by rw [he, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]) h1

private theorem mem_smul_top_pi {R : Type*} [CommRing R] (J : Ideal R) {r : ℕ} (x : Fin r → R) :
    x ∈ J • (⊤ : Submodule R (Fin r → R)) ↔ ∀ i, x i ∈ J :=
  ⟨fun hx _i => Submodule.smul_induction_on hx (fun _ ha _ _ => J.mul_mem_right _ ha)
      (fun _ _ ha hb => J.add_mem ha hb),
   fun hx => pi_eq_sum_univ x ▸ Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top⟩

private theorem isPrecomplete_pi {R : Type*} [CommRing R] (I : Ideal R) [IsPrecomplete I R] (r : ℕ) :
    IsPrecomplete I (Fin r → R) := ⟨fun {f} hf => by
  have hc : ∀ i : Fin r, ∃ L : R, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := fun i =>
    IsPrecomplete.prec' (f := fun n => f n i) fun {m n} hmn => by
      have h := hf hmn; rw [SModEq.sub_mem, mem_smul_top_pi] at h
      rw [SModEq.sub_mem]; simpa [Ideal.smul_top_eq_map, smul_eq_mul, Ideal.mul_top] using h i
  choose L hL using hc
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, mem_smul_top_pi]; intro i
  have := hL i n; rw [SModEq.sub_mem] at this; simpa [smul_eq_mul, Ideal.mul_top] using this⟩

theorem nakayama :
    ∀ (R : Type*) [CommRing R] (I : Ideal R) [IsPrecomplete I R] (M : Type*) [AddCommGroup M] [Module R M] [IsHausdorff I M],
      (∀ (r : ℕ) (s : Fin r → M), Submodule.span R (Set.range s) ⊔ I • (⊤ : Submodule R M) = ⊤ →
        Submodule.span R (Set.range s) = ⊤) ∧
      (Module.Finite R (M ⧸ I • (⊤ : Submodule R M)) → Module.Finite R M) := by
  intro R _ I _ M _ _ _
  have part1 : ∀ (r : ℕ) (s : Fin r → M), Submodule.span R (Set.range s) ⊔ I • (⊤ : Submodule R M) = ⊤ →
      Submodule.span R (Set.range s) = ⊤ := fun r s hs => by
    rw [← Fintype.range_linearCombination, LinearMap.range_eq_top]
    have := isPrecomplete_pi I r
    apply surjective_of_mkQ_comp_surjective (I := I)
    intro q; obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (hs ▸ Submodule.mem_top : m ∈ _)
    obtain ⟨c, rfl⟩ := (Fintype.range_linearCombination R s ▸ ha)
    refine ⟨c, ?_⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]; simpa using Submodule.neg_mem _ hb
  refine ⟨part1, fun hfin => ?_⟩
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M ⧸ I • (⊤ : Submodule R M))
  choose t ht using fun i => Submodule.Quotient.mk_surjective (I • (⊤ : Submodule R M)) (s i)
  have hsup : Submodule.span R (Set.range t) ⊔ I • (⊤ : Submodule R M) = ⊤ := by
    rw [sup_comm, ← Submodule.comap_map_mkQ, Submodule.map_span, ← Set.range_comp,
      show (I • (⊤ : Submodule R M)).mkQ ∘ t = s from funext ht, hs, Submodule.comap_top]
  exact ⟨Submodule.fg_def.2 ⟨Set.range t, Set.finite_range t, part1 r t hsup⟩⟩

private theorem binom_prime {R : Type*} [CommRing R] {l : ℕ} (hl : l.Prime) (y : R) :
    ∃ s : R, (1 + y) ^ l - 1 = y ^ l + l * y * (1 + y * s) := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hl (1 : Polynomial ℤ) Polynomial.X
  have h1 := congrArg (fun p : Polynomial ℤ => p.coeff 1) hr
  have hl1 : (1 : ℕ) ≠ l := hl.one_lt.ne
  have e : ((l : Polynomial ℤ) * 1 * Polynomial.X * r) = Polynomial.C (l : ℤ) * (Polynomial.X * r) := by
    simp [mul_assoc]
  simp only [Polynomial.coeff_one_add_X_pow, Nat.choose_one_right, one_pow, Polynomial.coeff_add,
    Polynomial.coeff_X_pow, if_neg hl1, e, Polynomial.coeff_C_mul, Polynomial.coeff_one] at h1
  have h2 : (Polynomial.X * r).coeff 1 = r.coeff 0 := Polynomial.coeff_X_mul r 0
  rw [h2] at h1
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne_zero
  have h3 : r.coeff 0 = 1 := by
    apply mul_left_cancel₀ hl0
    simpa using h1.symm
  have h4 : r = 1 + Polynomial.X * r.divX := by
    have := Polynomial.X_mul_divX_add r
    rw [h3] at this
    rw [add_comm]
    simpa using this.symm
  refine ⟨Polynomial.aeval y r.divX, ?_⟩
  have h5 := congrArg (Polynomial.aeval y) hr
  rw [h4] at h5
  simp only [map_pow, map_add, map_one, Polynomial.aeval_X, map_mul, map_natCast] at h5
  rw [h5]
  ring

private theorem binom_one {R : Type*} [CommRing R] (y : R) (n : ℕ) :
    ∃ s : R, (1 + y) ^ n - 1 = y * (n + y * s) := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨s, hs⟩ := ih
    refine ⟨n + s + y * s, ?_⟩
    rw [pow_succ, sub_eq_iff_eq_add.1 hs]
    push_cast
    ring

private theorem isUnit_add_mem {O : Type*} [CommRing O] [IsLocalRing O] {a b : O} (ha : IsUnit a)
    (hb : b ∈ maximalIdeal O) : IsUnit (a + b) := by
  by_contra h
  have h1 : a + b ∈ maximalIdeal O := h
  have h2 : a ∈ maximalIdeal O := by simpa using (maximalIdeal O).sub_mem h1 hb
  exact h2 ha

private theorem step_prime {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {l : ℕ} (hl : l.Prime) {y : O} (hy : y ∈ maximalIdeal O)
    (h : addVal O (l : O) < ((l - 1 : ℕ) : ℕ∞) * addVal O y) :
    addVal O ((1 + y) ^ l - 1) = addVal O y + addVal O (l : O) := by
  have h' : addVal O (l : O) < addVal O (y ^ (l - 1)) := by
    rwa [IsDiscreteValuationRing.addVal_pow, nsmul_eq_mul]
  obtain ⟨c, hc⟩ := IsDiscreteValuationRing.addVal_le_iff_dvd.1 h'.le
  have hcm : c ∈ maximalIdeal O := by
    intro hu
    rw [hc, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_eq_zero_iff.2 hu,
      add_zero] at h'
    exact lt_irrefl _ h'
  obtain ⟨s, hs⟩ := binom_prime hl y
  have e : y ^ l = y * (l * c) := by
    rw [← hc, ← pow_succ', Nat.sub_add_cancel hl.one_lt.le]
  have hu : IsUnit (1 + (y * s + c)) :=
    isUnit_add_mem isUnit_one ((maximalIdeal O).add_mem (Ideal.mul_mem_right _ _ hy) hcm)
  have e2 : (1 + y) ^ l - 1 = y * l * (1 + (y * s + c)) := by rw [hs, e]; ring
  rw [e2, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_eq_zero_iff.2 hu, add_zero]

private theorem lte_nat {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {l : ℕ} (hl : l.Prime) (hlm : (l : O) ∈ maximalIdeal O) (n : ℕ) :
    ∀ y : O, y ∈ maximalIdeal O → addVal O (l : O) < ((l - 1 : ℕ) : ℕ∞) * addVal O y →
      addVal O ((1 + y) ^ n - 1) = addVal O y + addVal O (n : O) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro y hy h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    by_cases hd : l ∣ n
    · obtain ⟨k, rfl⟩ := hd
      have hk : 0 < k := Nat.pos_of_mul_pos_left hn
      have hlt : k < l * k := lt_mul_of_one_lt_left hk hl.one_lt
      have h1 := step_prime hl hy h
      have hy' : (1 + y) ^ l - 1 ∈ maximalIdeal O := by
        obtain ⟨s, hs⟩ := binom_one y l
        rw [hs]
        exact Ideal.mul_mem_right _ _ hy
      have h2 := ih k hlt _ hy' (h.trans_le (by
        rw [h1]
        gcongr
        exact le_self_add))
      rw [add_sub_cancel, ← pow_mul, h1] at h2
      rw [h2, Nat.cast_mul, IsDiscreteValuationRing.addVal_mul, add_assoc]
    · have hu : IsUnit (n : O) := by
        by_contra hnu
        have hnm : (n : O) ∈ maximalIdeal O := hnu
        have hc : IsCoprime (l : O) (n : O) := ((Nat.Prime.coprime_iff_not_dvd hl).2 hd).cast
        obtain ⟨a, b, hab⟩ := hc
        have : (1 : O) ∈ maximalIdeal O :=
          hab ▸ (maximalIdeal O).add_mem (Ideal.mul_mem_left _ _ hlm) (Ideal.mul_mem_left _ _ hnm)
        exact this isUnit_one
      obtain ⟨s, hs⟩ := binom_one y n
      rw [hs, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_eq_zero_iff.2 hu,
        IsDiscreteValuationRing.addVal_eq_zero_iff.2 (isUnit_add_mem hu (Ideal.mul_mem_right _ _ hy))]

theorem lte (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (l : ℕ)
    (hl : l.Prime) (hlm : (l : O) ∈ maximalIdeal O) (u : oneUnits O)
    (h : addVal O (l : O) < ((l - 1 : ℕ) : ℕ∞) * addVal O (pt u : O)) (n : ℤ) :
    addVal O (pt (u ^ n) : O) = addVal O (pt u : O) + addVal O (n : O) := by
  have key : ∀ k : ℕ, addVal O (((u : Oˣ) : O) ^ k - 1) = addVal O (pt u : O) + addVal O (k : O) := by
    intro k
    have := lte_nat hl hlm k _ (pt u).2 h
    rwa [coe_pt, add_sub_cancel] at this
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [zpow_natCast, Int.cast_natCast, ← key k, coe_pt]
    simp
  · have e : (pt (u ^ (-(k : ℤ))) : O) = ((-((u : Oˣ) ^ k)⁻¹ : Oˣ) : O) * (((u : Oˣ) : O) ^ k - 1) := by
      rw [coe_pt, zpow_neg, zpow_natCast, ← Units.val_pow_eq_pow_val, Units.val_neg, neg_mul, mul_sub,
        Units.inv_mul, mul_one, neg_sub]
      simp
    rw [e, IsDiscreteValuationRing.addVal_mul, key k,
      IsDiscreteValuationRing.addVal_eq_zero_iff.2 (Units.isUnit _), zero_add, Int.cast_neg,
      Int.cast_natCast, AddValuation.map_neg]

private theorem len_mid {R M N P : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (h : N →ₗ[R] P)
    (e : Function.Exact f h) :
    Module.length R N = Module.length R (LinearMap.range f) + Module.length R (LinearMap.range h) :=
  Module.length_eq_add_of_exact (LinearMap.range f).subtype h.rangeRestrict
    (Submodule.injective_subtype _) h.surjective_rangeRestrict fun n => by
    rw [Subtype.ext_iff, ZeroMemClass.coe_zero]; change h n = 0 ↔ _; rw [e n]
    exact ⟨fun ⟨m, hm⟩ => ⟨⟨f m, m, rfl⟩, hm⟩, fun ⟨⟨_, m, hm⟩, hmn⟩ => ⟨m, hm.trans hmn⟩⟩

private def tmap {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (g : R) (f : M →ₗ[R] N) :
    Submodule.torsionBy R M g →ₗ[R] Submodule.torsionBy R N g :=
  f.restrict fun _ hx => by rw [Submodule.mem_torsionBy_iff] at hx ⊢; rw [← map_smul, hx, map_zero]

private theorem ex_tors {R : Type*} (M : Type*) [CommRing R] [AddCommGroup M] [Module R M] (g : R) :
    Function.Exact (Submodule.torsionBy R M g).subtype (g • (LinearMap.id : M →ₗ[R] M)) := fun x =>
  ⟨fun hx => ⟨⟨x, (Submodule.mem_torsionBy_iff _ _).2 (by simpa using hx)⟩, rfl⟩,
   fun ⟨⟨_, hy⟩, hxy⟩ => by subst hxy; simpa using (Submodule.mem_torsionBy_iff _ _).1 hy⟩

private theorem ex_quot {R : Type*} (M : Type*) [CommRing R] [AddCommGroup M] [Module R M] (g : R) :
    Function.Exact (g • (LinearMap.id : M →ₗ[R] M)) (g • (⊤ : Submodule R M)).mkQ := fun x => by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨fun hx => let ⟨b, _, hb⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx; ⟨b, by simpa using hb⟩,
   fun ⟨b, hb⟩ => (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨b, Submodule.mem_top, by simpa using hb⟩⟩

theorem snake_len :
    ∀ (R : Type*) [CommRing R] (g : R) (A B D : Type*) [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
      [AddCommGroup D] [Module R D] (i : A →ₗ[R] B) (j : B →ₗ[R] D),
      Function.Injective i → Function.Surjective j → Function.Exact i j →
      invLen g A + invLen g D + coinvLen g B = invLen g B + coinvLen g A + coinvLen g D ∧
        invLen g B ≤ invLen g A + invLen g D ∧ coinvLen g B ≤ coinvLen g A + coinvLen g D ∧
        invLen g A ≤ invLen g B ∧ coinvLen g D ≤ coinvLen g B ∧
        coinvLen g A ≤ invLen g D + coinvLen g B ∧ invLen g D ≤ invLen g B + coinvLen g A := by
  intro R _ g A B D _ _ _ _ _ _ i j hi hj hij
  have h₁ : i ∘ₗ (g • LinearMap.id : A →ₗ[R] A) = (g • LinearMap.id : B →ₗ[R] B) ∘ₗ i := by ext a; simp
  have h₂ : j ∘ₗ (g • LinearMap.id : B →ₗ[R] B) = (g • LinearMap.id : D →ₗ[R] D) ∘ₗ j := by ext b; simp
  let G : QuotSMulTop g A →ₗ[R] QuotSMulTop g B := Submodule.mapQ _ _ i fun a ha => by
    rw [Submodule.mem_comap]; obtain ⟨b, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 ha
    rw [map_smul]; exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  let H : QuotSMulTop g B →ₗ[R] QuotSMulTop g D := Submodule.mapQ _ _ j fun a ha => by
    rw [Submodule.mem_comap]; obtain ⟨b, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 ha
    rw [map_smul]; exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  have hG : G ∘ₗ (g • ⊤ : Submodule R A).mkQ = (g • ⊤ : Submodule R B).mkQ ∘ₗ i := by ext a; rfl
  have hδr := SnakeLemma.exact_δ'_right (g • LinearMap.id) (g • LinearMap.id)
    (g • LinearMap.id) i j hij i j hij h₁ h₂ (Submodule.torsionBy R B g).subtype (ex_tors B g)
    (Submodule.torsionBy R D g).subtype (ex_tors D g) (g • ⊤ : Submodule R A).mkQ (ex_quot A g)
    hj hi (tmap g j) (by ext x; rfl) (Submodule.injective_subtype _)
  have hδl := SnakeLemma.exact_δ'_left (g • LinearMap.id) (g • LinearMap.id)
    (g • LinearMap.id) i j hij i j hij h₁ h₂
    (Submodule.torsionBy R D g).subtype (ex_tors D g) (g • ⊤ : Submodule R A).mkQ (ex_quot A g)
    (g • ⊤ : Submodule R B).mkQ (ex_quot B g) hj hi G hG (Submodule.mkQ_surjective _)
  have e1 : Function.Exact (tmap g i) (tmap g j) := fun x =>
    ⟨fun hx => by
      obtain ⟨a, ha⟩ := (hij x.1).1 (congrArg Subtype.val hx)
      refine ⟨⟨a, (Submodule.mem_torsionBy_iff _ _).2 (hi (by
        rw [map_smul, ha, map_zero]; exact (Submodule.mem_torsionBy_iff _ _).1 x.2))⟩, Subtype.ext ha⟩,
     fun ⟨a, ha⟩ => ha ▸ Subtype.ext (hij.apply_apply_eq_zero a.1)⟩
  have i1 : Function.Injective (tmap g i) := fun _ _ hxy => Subtype.ext (hi (congrArg Subtype.val hxy))
  have e4 : Function.Exact G H := fun y => by
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ y
    refine ⟨fun hy => ?_, fun ⟨x, hx⟩ => ?_⟩
    · change Submodule.Quotient.mk (j b) = 0 at hy
      rw [Submodule.Quotient.mk_eq_zero] at hy
      obtain ⟨d, -, hd⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
      obtain ⟨b', rfl⟩ := hj d
      obtain ⟨a, ha⟩ := (hij (b - g • b')).1 (by rw [map_sub, map_smul, hd, sub_self])
      refine ⟨Submodule.Quotient.mk a, ?_⟩
      change Submodule.Quotient.mk (i a) = Submodule.Quotient.mk b
      rw [ha, Submodule.Quotient.eq, sub_sub_cancel_left]
      exact Submodule.neg_mem _ (Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)
    · rw [← hx]; obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ x
      change Submodule.Quotient.mk (j (i a)) = 0
      rw [hij.apply_apply_eq_zero, Submodule.Quotient.mk_zero]
  have s4 : Function.Surjective H := fun y => by
    obtain ⟨d, rfl⟩ := Submodule.mkQ_surjective _ y; obtain ⟨b, rfl⟩ := hj d
    exact ⟨Submodule.Quotient.mk b, rfl⟩
  have r1 : Module.length R (LinearMap.range (tmap g i)) = Module.length R (Submodule.torsionBy R A g) :=
    (LinearEquiv.ofInjective _ i1).length_eq.symm
  have r4 : Module.length R (LinearMap.range H) = Module.length R (QuotSMulTop g D) := by
    rw [LinearMap.range_eq_top.2 s4, Module.length_top]
  have arith : ∀ p x y z q : ℕ∞,
      p + (x + y) + (z + q) = p + x + (y + z) + q ∧ p + x ≤ p + (x + y) ∧
        z + q ≤ y + z + q ∧ p ≤ p + x ∧ q ≤ z + q ∧ y + z ≤ x + y + (z + q) ∧
        x + y ≤ p + x + (y + z) := fun p x y z q =>
    ⟨by ring, le_iff_exists_add.2 ⟨y, by ring⟩, le_iff_exists_add.2 ⟨y, by ring⟩,
      le_iff_exists_add.2 ⟨x, by ring⟩, le_iff_exists_add.2 ⟨z, by ring⟩,
      le_iff_exists_add.2 ⟨x + q, by ring⟩, le_iff_exists_add.2 ⟨p + z, by ring⟩⟩
  unfold invLen coinvLen
  rw [len_mid (tmap g i) (tmap g j) e1, len_mid _ _ hδr, len_mid _ _ hδl, len_mid G H e4, r1, r4]
  exact arith _ _ _ _ _

/-! ## Section 4: Isotypic Submodules, Equivariant Projections & Finite-Order Diagonalization -/

theorem mem_isotypic_of_injective {R S Y V : Type*} [Ring R] [AddCommGroup S] [Module R S] [AddCommGroup Y] [Module R Y]
    [AddCommGroup V] [Module R V] [IsSimpleModule R S] (j : Y →ₗ[R] V) (hj : Function.Injective j)
    (h : ∀ y, j y ∈ isotypicComponent R V S) : isotypicComponent R Y S = ⊤ := by
  classical
  have hf : Function.Injective (j.codRestrict (isotypicComponent R V S) h) :=
    fun a b hab => hj (congrArg Subtype.val hab)
  have hiso : IsIsotypicOfType R Y S :=
    (IsIsotypicOfType.isotypicComponent R V S).of_injective _ hf
  have : IsSemisimpleModule R Y := IsSemisimpleModule.of_injective _ hf
  rw [eq_top_iff, ← IsSemisimpleModule.sSup_simples_eq_top]
  refine sSup_le fun m hm => ?_
  have : IsSimpleModule R m := hm
  exact le_sSup (hiso m)

theorem iso_sub {H S Y V : Type*} [Group H] [AddCommGroup S] [Module ℂ S] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ H S) (π : Representation ℂ H Y) (ρ : Representation ℂ H V)
    (hσ : σ.IsIrreducible) (j : Y →ₗ[ℂ] V) (hj : Function.Injective j) (he : ∀ g y, j (π g y) = ρ g (j y))
    (h : ∀ y, j y ∈ ⨆ f : {f : S →ₗ[ℂ] V // ∀ g v, f (σ g v) = ρ g (f v)}, LinearMap.range f.1) (y : Y) :
    y ∈ ⨆ f : {f : S →ₗ[ℂ] Y // ∀ g v, f (σ g v) = π g (f v)}, LinearMap.range f.1 := by
  classical
  have : σ.IsIrreducible := hσ
  let J : Representation.IntertwiningMap π ρ := j.intertwiningMap_of_isIntertwiningMap π ρ he
  let j' := Representation.IntertwiningMap.equivLinearMapAsModule π ρ J
  have h' : ∀ z, j' z ∈ isotypicComponent (MonoidAlgebra ℂ H) ρ.asModule σ.asModule := fun z =>
    Submodule.iSup_induction _ (motive := fun x => ρ.asModuleEquiv.symm x ∈
      isotypicComponent (MonoidAlgebra ℂ H) ρ.asModule σ.asModule) (h z)
      (fun f _ hx => by
        obtain ⟨v, rfl⟩ := hx
        let F := Representation.IntertwiningMap.equivLinearMapAsModule σ ρ
          (f.1.intertwiningMap_of_isIntertwiningMap σ ρ f.2)
        have hle : LinearMap.range F ≤ isotypicComponent (MonoidAlgebra ℂ H) ρ.asModule σ.asModule := by
          rcases F.injective_or_eq_zero with hF | hF
          · exact le_sSup ⟨(LinearEquiv.ofInjective F hF).symm⟩
          · rw [hF, LinearMap.range_zero]; exact bot_le
        exact hle ⟨σ.asModuleEquiv.symm v, rfl⟩)
      (by simp) (fun _ _ hx hy => by rw [map_add]; exact Submodule.add_mem _ hx hy)
  have hy : π.asModuleEquiv.symm y ∈ isotypicComponent (MonoidAlgebra ℂ H) π.asModule σ.asModule :=
    (mem_isotypic_of_injective j' hj h') ▸ Submodule.mem_top
  rw [isotypicComponent, sSup_eq_iSup'] at hy
  simpa using Submodule.iSup_induction _ (motive := fun x => π.asModuleEquiv x ∈
      ⨆ f : {f : S →ₗ[ℂ] Y // ∀ g v, f (σ g v) = π g (f v)}, LinearMap.range f.1) hy
    (fun ⟨m, ⟨e⟩⟩ x hx => by
      let L : σ.asModule →ₗ[MonoidAlgebra ℂ H] π.asModule := m.subtype ∘ₗ e.symm.toLinearMap
      let F := (Representation.IntertwiningMap.equivLinearMapAsModule σ π).symm L
      refine Submodule.mem_iSup_of_mem
        ⟨F.toLinearMap, fun g v => Representation.IntertwiningMap.isIntertwining σ π F g v⟩
        ⟨σ.asModuleEquiv (e ⟨x, hx⟩), ?_⟩
      show (L (e ⟨x, hx⟩) : π.asModule) = x; simp [L])
    (by simp) (fun _ _ hx hz => by rw [map_add]; exact Submodule.add_mem _ hx hz)

theorem exists_desc {M V : Type*} [AddCommGroup V] [Module ℂ V] (s s' : M → V)
    (h : ∀ c : M →₀ ℂ, Finsupp.linearCombination ℂ s c = 0 → Finsupp.linearCombination ℂ s' c = 0) :
    ∃ T : V →ₗ[ℂ] V, ∀ m, T (s m) = s' m := by
  classical
  have hk : LinearMap.ker (Finsupp.linearCombination ℂ s) ≤ LinearMap.ker (Finsupp.linearCombination ℂ s') :=
    fun c hc => LinearMap.mem_ker.mpr (h c (LinearMap.mem_ker.mp hc))
  obtain ⟨g, hg⟩ := LinearMap.exists_extend
    ((LinearMap.ker (Finsupp.linearCombination ℂ s)).liftQ (Finsupp.linearCombination ℂ s') hk ∘ₗ
      (Finsupp.linearCombination ℂ s).quotKerEquivRange.symm.toLinearMap)
  refine ⟨g, fun m => ?_⟩
  have := LinearMap.congr_fun hg ⟨_, LinearMap.mem_range_self _ (Finsupp.single m (1 : ℂ))⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply] at this
  rw [show s m = Finsupp.linearCombination ℂ s (Finsupp.single m 1) by simp, this]; simp

private theorem exists_equivariant_projection_onto_invariant_submodule {R V ι : Type*} [AddCommGroup V] [Module ℂ V]
    (T : R → V →ₗ[ℂ] V) (χ : ι → R → ℂ) (a : R → ℂ) (s : Finset ι) (v : ι → V)
    (hv : ∀ i ∈ s, ∀ t, T t (v i) = χ i t • v i) (ha : ∀ i ∈ s, χ i ≠ a)
    (hx : ∀ t, T t (∑ i ∈ s, v i) = a t • ∑ i ∈ s, v i) : ∑ i ∈ s, v i = 0 := by
  classical
  induction s using Finset.induction_on generalizing v with
  | empty => simp
  | insert b s hb ih =>
    obtain ⟨t, ht⟩ := Function.ne_iff.mp (ha b (Finset.mem_insert_self b s))
    have hvs : ∀ i ∈ s, ∀ t, T t (v i) = χ i t • v i := fun i hi => hv i (Finset.mem_insert_of_mem hi)
    have key : (a t - χ b t) • ∑ i ∈ insert b s, v i = ∑ i ∈ s, (χ i t - χ b t) • v i := by
      rw [sub_smul, ← hx t, Finset.sum_insert hb, map_add, map_sum,
        Finset.sum_congr rfl (fun i hi => hvs i hi t), hv b (Finset.mem_insert_self b s) t]
      simp only [sub_smul, Finset.sum_sub_distrib, Finset.smul_sum, smul_add]; abel
    have hz := ih (fun i => (χ i t - χ b t) • v i) (fun i hi t' => by rw [map_smul, hvs i hi t', smul_comm])
      (fun i hi => ha i (Finset.mem_insert_of_mem hi)) (fun t' => by rw [← key, map_smul, hx t', smul_comm])
    rw [← key] at hz
    exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (Ne.symm ht))

theorem exists_proj {R G V J : Type*} [AddCommGroup V] [Module ℂ V] (T : R → V →ₗ[ℂ] V) (π : G → V →ₗ[ℂ] V)
    (E : Submodule ℂ V) (hE : ∀ g, ∀ F ∈ E, π g F ∈ E) (hc : ∀ t g, ∀ F ∈ E, T t (π g F) = π g (T t F))
    (W : J → Submodule ℂ V) (χ : J → R → ℂ) (hW : ∀ j t, ∀ F ∈ W j, T t F = χ j t • F) (hsup : E = ⨆ j, W j)
    (F0 : V) (h0 : F0 ∈ E) (hne : F0 ≠ 0) :
    ∃ (j0 : J) (Y : Submodule ℂ V) (p : V →ₗ[ℂ] Y), W j0 ≠ ⊥ ∧ (∀ g, ∀ F ∈ Y, π g F ∈ Y) ∧ p F0 ≠ 0 ∧
      (∀ t, ∀ F ∈ E, p (T t F) = χ j0 t • p F) ∧ (∀ g, ∀ F ∈ E, (p (π g F) : V) = π g (p F)) ∧
      Y ≤ ⨆ j : {j // χ j = χ j0}, W j := by
  classical
  have hYe : ∀ c, ∀ x ∈ ⨆ j : {j // χ j = c}, W j, ∀ t, T t x = c t • x := fun c x hx t =>
    Submodule.iSup_induction _ (motive := fun x => T t x = c t • x) hx
      (fun j y hy => by rw [hW j.1 t y hy, j.2]) (by simp) fun _ _ hy hz => by rw [map_add, hy, hz, smul_add]
  have hKz : ∀ c, ∀ x ∈ ⨆ j : {j // χ j ≠ c}, W j, (∀ t, T t x = c t • x) → x = 0 := fun c x hx hxe => by
    obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hx
    obtain ⟨μ, rfl⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ _).mp hs
    exact exists_equivariant_projection_onto_invariant_submodule T (fun j : {j // χ j ≠ c} => χ j.1) c s
      (fun j => (μ j : V)) (fun j _ t => hW j.1 t _ (μ j).2) (fun j _ => j.2) hxe
  have hsplit : ∀ c, E = (⨆ j : {j // χ j = c}, W j) ⊔ ⨆ j : {j // χ j ≠ c}, W j := fun c => by
    rw [hsup, iSup_split W (fun j => χ j = c), iSup_subtype', iSup_subtype']
  have hTK : ∀ c t, ∀ x ∈ ⨆ j : {j // χ j ≠ c}, W j, T t x ∈ ⨆ j : {j // χ j ≠ c}, W j := fun c t x hx =>
    Submodule.iSup_induction _ (motive := fun x => T t x ∈ ⨆ j : {j // χ j ≠ c}, W j) hx
      (fun j y hy => by rw [hW j.1 t y hy]; exact Submodule.mem_iSup_of_mem j (Submodule.smul_mem _ _ hy))
      (by simp) fun _ _ hy hz => by rw [map_add]; exact Submodule.add_mem _ hy hz
  have hEY : ∀ c, ∀ F ∈ E, (∀ t, T t F = c t • F) → F ∈ ⨆ j : {j // χ j = c}, W j := fun c F hF hFe => by
    rw [hsplit c] at hF; obtain ⟨y, hy, k, hk, rfl⟩ := Submodule.mem_sup.mp hF
    have hke : ∀ t, T t k = c t • k := fun t => by
      have h1 := hFe t; rw [map_add, hYe c y hy t, smul_add] at h1; exact add_left_cancel h1
    rw [hKz c k hk hke, add_zero]; exact hy
  have hYE : ∀ c, (⨆ j : {j // χ j = c}, W j) ≤ E := fun c => by rw [hsplit c]; exact le_sup_left
  have hKE : ∀ c, (⨆ j : {j // χ j ≠ c}, W j) ≤ E := fun c => by rw [hsplit c]; exact le_sup_right
  have hπY : ∀ c g, ∀ F ∈ ⨆ j : {j // χ j = c}, W j, π g F ∈ ⨆ j : {j // χ j = c}, W j := fun c g F hF =>
    hEY c _ (hE g F (hYE c hF)) fun t => by rw [hc t g F (hYE c hF), hYe c F hF t, map_smul]
  have hπK : ∀ c g, ∀ x ∈ ⨆ j : {j // χ j ≠ c}, W j, π g x ∈ ⨆ j : {j // χ j ≠ c}, W j := fun c g x hx =>
    Submodule.iSup_induction _ (motive := fun x => π g x ∈ ⨆ j : {j // χ j ≠ c}, W j) hx
      (fun j y hy => (iSup_le fun i : {i // χ i = χ j.1} =>
        le_iSup (fun j : {j // χ j ≠ c} => W j.1) ⟨i.1, by rw [i.2]; exact j.2⟩)
        (hπY (χ j.1) g y (Submodule.mem_iSup_of_mem (⟨j.1, rfl⟩ : {i // χ i = χ j.1}) hy)))
      (by simp) fun _ _ hy hz => by rw [map_add]; exact Submodule.add_mem _ hy hz
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp (hsup ▸ h0)
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ _).mp hs
  obtain ⟨j1, -, hu⟩ : ∃ j1 ∈ s, ∑ i ∈ s.filter (fun i => χ i = χ j1), (μ i : V) ≠ 0 := by
    by_contra hcon; push Not at hcon; apply hne
    rw [← hμ, ← Finset.sum_fiberwise_of_maps_to (g := χ) (t := s.image χ) (fun i hi => Finset.mem_image_of_mem χ hi)]
    exact Finset.sum_eq_zero fun c hc => let ⟨j, hj, hjc⟩ := Finset.mem_image.mp hc; hjc ▸ hcon j hj
  obtain ⟨j0, hj0, hμ0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hu
  rw [← (Finset.mem_filter.mp hj0).2] at hu
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl E
  have hYK : IsCompl (⨆ j : {j // χ j = χ j0}, W j) ((⨆ j : {j // χ j ≠ χ j0}, W j) ⊔ C) := by
    refine ⟨Submodule.disjoint_def.2 fun x hxY hxKC => ?_,
      by rw [codisjoint_iff, ← sup_assoc, ← hsplit (χ j0)]; exact hC.sup_eq_top⟩
    obtain ⟨k, hk, c', hc', rfl⟩ := Submodule.mem_sup.mp hxKC
    have hc'0 : c' = 0 := (Submodule.disjoint_def.mp hC.disjoint) c'
      (by rw [show c' = (k + c') - k by abel]; exact Submodule.sub_mem _ (hYE _ hxY) (hKE _ hk)) hc'
    subst hc'0; rw [add_zero] at hxY ⊢; exact hKz (χ j0) k hk (hYe (χ j0) k hxY)
  have hpY : ∀ y (hy : y ∈ ⨆ j : {j // χ j = χ j0}, W j), Submodule.projectionOnto _ _ hYK y = ⟨y, hy⟩ :=
    fun y hy => Submodule.projectionOnto_apply_of_mem_left hYK hy
  have hpK : ∀ k ∈ ⨆ j : {j // χ j ≠ χ j0}, W j, Submodule.projectionOnto _ _ hYK k = 0 :=
    fun k hk => Submodule.projectionOnto_apply_of_mem_right hYK (Submodule.mem_sup_left hk)
  refine ⟨j0, _, Submodule.projectionOnto _ _ hYK, fun hbot => hμ0 ((Submodule.eq_bot_iff _).mp hbot _ (μ j0).2),
    hπY (χ j0), ?_, ?_, ?_, le_rfl⟩
  · have huY : (∑ i ∈ s.filter (fun i => χ i = χ j0), (μ i : V)) ∈ ⨆ j : {j // χ j = χ j0}, W j :=
      Submodule.sum_mem _ fun i hi => Submodule.mem_iSup_of_mem (⟨i, (Finset.mem_filter.mp hi).2⟩ : {j // χ j = χ j0}) (μ i).2
    have hrK : (∑ i ∈ s.filter (fun i => ¬ χ i = χ j0), (μ i : V)) ∈ ⨆ j : {j // χ j ≠ χ j0}, W j :=
      Submodule.sum_mem _ fun i hi => Submodule.mem_iSup_of_mem (⟨i, (Finset.mem_filter.mp hi).2⟩ : {j // χ j ≠ χ j0}) (μ i).2
    intro hp; apply hu
    rw [← hμ, ← Finset.sum_filter_add_sum_filter_not s (fun i => χ i = χ j0), map_add, hpK _ hrK, add_zero, hpY _ huY] at hp
    simpa using congrArg Subtype.val hp
  · intro t F hF; rw [hsplit (χ j0)] at hF; obtain ⟨y, hy, k, hk, rfl⟩ := Submodule.mem_sup.mp hF
    simp only [map_add, map_smul, hYe _ y hy t, hpK _ hk, hpK _ (hTK _ t k hk), add_zero]
  · intro g F hF; rw [hsplit (χ j0)] at hF; obtain ⟨y, hy, k, hk, rfl⟩ := Submodule.mem_sup.mp hF
    simp [hpK _ hk, hpK _ (hπK _ g k hk), hpY _ hy, hpY _ (hπY _ g y hy)]

section FinChar

open Polynomial

variable {k : Type*} [Field k] [IsAlgClosed k] [CharZero k] {n : ℕ}

theorem exists_eigenbasis (f : Module.End k (Fin n → k)) {m : ℕ} (hm : 0 < m) (hfm : f ^ m = 1) :
    ∃ (b : Module.Basis (Fin n) k (Fin n → k)) (d : Fin n → k), ∀ i, f (b i) = d i • b i := by
  classical
  have hmk : ((m : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hsep : (Polynomial.X ^ m - Polynomial.C (1 : k)).Separable :=
    separable_X_pow_sub_C 1 hmk one_ne_zero
  have hss : f.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree (by simp [hfm])
  have hint : DirectSum.IsInternal f.eigenspace :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top f.eigenspaces_iSupIndep
      hss.iSup_eigenspace_eq_top
  let v := fun μ => Module.Basis.ofVectorSpace k (f.eigenspace μ)
  let B := hint.collectedBasis v
  let e := B.indexEquiv (Pi.basisFun k (Fin n))
  refine ⟨B.reindex e, fun i => (e.symm i).1, fun i => ?_⟩
  have hmem := hint.collectedBasis_mem v (e.symm i)
  rw [Module.End.mem_eigenspace_iff] at hmem
  simpa [Module.Basis.reindex_apply, B] using hmem

theorem exists_eigenframe (T : (Matrix (Fin n) (Fin n) k)ˣ) {m : ℕ} (hm : 0 < m) (hT : T ^ m = 1) :
    ∃ (u : (Matrix (Fin n) (Fin n) k)ˣ) (d : Fin n → k), T.val * u.val = u.val * Matrix.diagonal d := by
  classical
  obtain ⟨b, d, hb⟩ := exists_eigenbasis (Matrix.toLinAlgEquiv' T.val) hm
    (by rw [← map_pow, ← Units.val_pow_eq_pow_val, hT, Units.val_one, map_one])
  let := (Pi.basisFun k (Fin n)).invertibleToMatrix b
  refine ⟨unitOfInvertible ((Pi.basisFun k (Fin n)).toMatrix b), d, ?_⟩
  ext i j
  rw [Matrix.mul_diagonal]
  have hj := congrFun (hb j) i
  simp only [Matrix.toLinAlgEquiv'_apply, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hj
  simp [Matrix.mul_apply, Module.Basis.toMatrix_apply, hj, mul_comm]

theorem charpoly_powers (T : (Matrix (Fin n) (Fin n) k)ˣ) {m : ℕ} (hm : 0 < m) (hT : T ^ m = 1) :
    ∃ d : Fin n → k, (∀ i, d i ^ m = 1) ∧
      ∀ a : ℕ, (T ^ a).val.charpoly = ∏ i, (Polynomial.X - Polynomial.C (d i ^ a)) := by
  classical
  obtain ⟨u, d, hu⟩ := exists_eigenframe T hm hT
  have hc : ∀ a : ℕ, T.val ^ a * u.val = u.val * Matrix.diagonal d ^ a := by
    intro a
    induction a with
    | zero => simp
    | succ a ih => rw [pow_succ', mul_assoc, ih, ← mul_assoc, hu, mul_assoc, ← pow_succ']
  refine ⟨d, fun i => ?_, fun a => ?_⟩
  · have h1 : u.val * Matrix.diagonal (d ^ m) = u.val * 1 := by
      rw [← Matrix.diagonal_pow, ← hc m, ← Units.val_pow_eq_pow_val, hT, Units.val_one, one_mul,
        mul_one]
    have h2 := (Units.mul_right_inj u).mp h1
    have h3 := congrFun (congrFun h2 i) i
    simpa using h3
  · have hdet : IsUnit u.val.det := (Matrix.isUnit_iff_isUnit_det _).mp u.isUnit
    have h1 : (T ^ a).val = u.val * Matrix.diagonal d ^ a * (u.val)⁻¹ := by
      rw [Units.val_pow_eq_pow_val, ← hc a, mul_assoc, Matrix.mul_nonsing_inv _ hdet, mul_one]
    rw [h1, Matrix.charpoly_units_conj, Matrix.diagonal_pow, Matrix.charpoly_diagonal]
    simp [Pi.pow_apply]

theorem charpoly_of_ker {Γ : Type*} [Group Γ] (r : Γ →* (Matrix (Fin n) (Fin n) k)ˣ) (χ : Γ →* kˣ) (I : Subgroup Γ)
    (hf : (χ '' (I : Set Γ)).Finite) (hk : ∀ g ∈ I, χ g = 1 → r g = 1) :
    ∃ j : Fin n → ℕ, ∀ g ∈ I, (r g).val.charpoly = ∏ i, (Polynomial.X - Polynomial.C ((χ g : k) ^ j i)) := by
  classical
  set S : Subgroup kˣ := I.map χ with hS
  have hSf : (S : Set kˣ).Finite := by rw [hS, Subgroup.coe_map]; exact hf
  have : Finite S := hSf.to_subtype
  obtain ⟨x, hx⟩ := IsCyclic.exists_monoid_generator (α := S)
  obtain ⟨g0, hg0I, hg0⟩ := Subgroup.mem_map.mp x.2
  set N := orderOf x with hN
  have hNpos : 0 < N := orderOf_pos x
  have hxN : (x : kˣ) ^ N = 1 := by
    have h := congrArg Subtype.val (pow_orderOf_eq_one x)
    exact_mod_cast h
  have hrN : r g0 ^ N = 1 := by
    rw [← map_pow]
    apply hk _ (I.pow_mem hg0I N)
    rw [map_pow, hg0, hxN]
  obtain ⟨d, hd, hchar⟩ := charpoly_powers (r g0) hNpos hrN
  have hprim : IsPrimitiveRoot ((x : kˣ) : k) N := by
    rw [IsPrimitiveRoot.coe_units_iff, hN, ← Subgroup.orderOf_coe]
    exact IsPrimitiveRoot.orderOf _
  have : NeZero N := ⟨hNpos.ne'⟩
  have hj : ∀ i, ∃ j, ((x : kˣ) : k) ^ j = d i := fun i =>
    let ⟨j, _, h⟩ := hprim.eq_pow_of_pow_eq_one (hd i); ⟨j, h⟩
  choose j hj using hj
  refine ⟨j, fun g hg => ?_⟩
  obtain ⟨a, ha⟩ := (Submonoid.mem_powers_iff _ _).mp (hx ⟨χ g, Subgroup.mem_map_of_mem χ hg⟩)
  have hχa : χ g = (x : kˣ) ^ a := by
    rw [← SubgroupClass.coe_pow, ha]
  have hrg : r g = r g0 ^ a := by
    have h1 : χ (g * (g0 ^ a)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_pow, hg0, hχa, mul_inv_cancel]
    have h2 := hk _ (I.mul_mem hg (I.inv_mem (I.pow_mem hg0I a))) h1
    rw [map_mul, map_inv, map_pow, mul_inv_eq_one] at h2
    exact h2
  rw [hrg, hchar a]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [← hj i, hχa, Units.val_pow_eq_pow_val, ← pow_mul, ← pow_mul, Nat.mul_comm]

end FinChar

/-! ## Section 5: `AlgebraicClosure ℚ`, Conjugate Integrality, Cyclotomic Powers & `PadicAlgCl` Norms -/

namespace QbarInst

theorem charZero : CharZero (AlgebraicClosure ℚ) := inferInstance
theorem torsionFree : Module.IsTorsionFree ℚ (AlgebraicClosure ℚ) := inferInstance
theorem algClosure : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ

end QbarInst

section TranscAndConjugates

open Cardinal Polynomial IntermediateField

private theorem isTranscendenceBasis_extendScalars_of_isAlgebraic {Ω F E : Type*} [Field Ω] [Field F] [Field E]
    [Algebra F Ω] [Algebra F E] [Algebra E Ω] [IsScalarTower F E Ω] [Algebra.IsAlgebraic F E]
    {ι : Type*} {v : ι → Ω} (hv : IsTranscendenceBasis F v) : IsTranscendenceBasis E v := by
  refine (hv.1.extendScalars E).isTranscendenceBasis_iff_isAlgebraic.mpr ⟨fun z => ?_⟩
  have le : Algebra.adjoin F (Set.range v) ≤ (Algebra.adjoin E (Set.range v)).restrictScalars F :=
    Algebra.adjoin_le fun z hz => (Subalgebra.mem_restrictScalars _).mpr (Algebra.subset_adjoin hz)
  exact (hv.isAlgebraic.isAlgebraic z).tower_top_of_subalgebra_le le

private theorem exists_ringEquiv_extend_of_isTranscendenceBasis {Ω F₁ F₂ : Type*} [Field Ω] [IsAlgClosed Ω]
    [Field F₁] [Field F₂] [Algebra F₁ Ω] [Algebra F₂ Ω]
    (e : F₁ ≃+* F₂) {ι κ : Type*} {v₁ : ι → Ω} {v₂ : κ → Ω}
    (h₁ : IsTranscendenceBasis F₁ v₁) (h₂ : IsTranscendenceBasis F₂ v₂) (φ : ι ≃ κ) :
    ∃ σ : Ω ≃+* Ω, (∀ a : F₁, σ (algebraMap F₁ Ω a) = algebraMap F₂ Ω (e a)) ∧
      ∀ i, σ (v₁ i) = v₂ (φ i) := by
  have := IsAlgClosed.isAlgClosure_of_transcendence_basis v₁ h₁
  have := IsAlgClosed.isAlgClosure_of_transcendence_basis v₂ h₂
  let e' : Algebra.adjoin F₁ (Set.range v₁) ≃+* Algebra.adjoin F₂ (Set.range v₂) :=
    h₁.1.aevalEquiv.symm.toRingEquiv.trans <| (MvPolynomial.mapEquiv ι e).trans <|
      (MvPolynomial.renameEquiv F₂ φ).toRingEquiv.trans h₂.1.aevalEquiv.toRingEquiv
  have key : ∀ p : MvPolynomial ι F₁,
      IsAlgClosure.equivOfEquiv Ω Ω e' (MvPolynomial.aeval v₁ p) =
        MvPolynomial.aeval v₂ (MvPolynomial.rename φ (MvPolynomial.map (e : F₁ →+* F₂) p)) := by
    intro p
    rw [← h₁.1.algebraMap_aevalEquiv, IsAlgClosure.equivOfEquiv_algebraMap,
      ← h₂.1.algebraMap_aevalEquiv]
    congr 1
    simp [e']
  refine ⟨IsAlgClosure.equivOfEquiv Ω Ω e', fun a => ?_, fun i => ?_⟩
  · simpa using key (MvPolynomial.C a)
  · simpa using key (MvPolynomial.X i)

private theorem exists_algEquiv_apply_eq_of_transcendental {Ω F : Type*} [Field Ω] [IsAlgClosed Ω]
    [Field F] [Algebra F Ω] {x y : Ω} (hx : Transcendental F x) (hy : Transcendental F y) :
    ∃ σ : Ω ≃ₐ[F] Ω, σ x = y := by
  classical
  have ind : ∀ z : Ω, Transcendental F z → AlgebraicIndepOn F id ({z} : Set Ω) := fun z hz =>
    (algebraicIndependent_singleton_iff (⟨z, rfl⟩ : ({z} : Set Ω))).mpr hz
  obtain ⟨t₁, hxt, ht₁⟩ := exists_isTranscendenceBasis_superset (ind x hx)
  obtain ⟨t₂, hyt, ht₂⟩ := exists_isTranscendenceBasis_superset (ind y hy)
  have hx₁ : x ∈ t₁ := Set.singleton_subset_iff.mp hxt
  have hy₂ : y ∈ t₂ := Set.singleton_subset_iff.mp hyt
  obtain ⟨f⟩ := Cardinal.eq.1 (ht₁.cardinalMk_eq_trdeg.trans ht₂.cardinalMk_eq_trdeg.symm)
  let φ : t₁ ≃ t₂ := f.trans (Equiv.swap (f ⟨x, hx₁⟩) ⟨y, hy₂⟩)
  obtain ⟨σ, hσF, hσv⟩ :=
    exists_ringEquiv_extend_of_isTranscendenceBasis (RingEquiv.refl F) ht₁ ht₂ φ
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) fun a => hσF a, ?_⟩
  have := hσv ⟨x, hx₁⟩
  simp only [φ, Equiv.trans_apply, Equiv.swap_apply_left] at this
  exact this

private theorem exists_algEquiv_apply_eq_of_minpoly_eq {Ω F : Type*} [Field Ω] [IsAlgClosed Ω]
    [Field F] [Algebra F Ω] {x y : Ω} (hx : IsAlgebraic F x) (h : minpoly F x = minpoly F y) :
    ∃ σ : Ω ≃ₐ[F] Ω, σ x = y := by
  have hy : IsAlgebraic F y := ⟨minpoly F x, minpoly.ne_zero hx.isIntegral, h ▸ minpoly.aeval _ _⟩
  have := isAlgebraic_adjoin_simple hx.isIntegral
  have := isAlgebraic_adjoin_simple hy.isIntegral
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F Ω
  obtain ⟨σ, hσ, -⟩ := exists_ringEquiv_extend_of_isTranscendenceBasis
    (minpoly.algEquiv hx h).toRingEquiv
    (isTranscendenceBasis_extendScalars_of_isAlgebraic (E := F⟮x⟯) hs)
    (isTranscendenceBasis_extendScalars_of_isAlgebraic (E := F⟮y⟯) hs) (Equiv.refl s)
  refine ⟨AlgEquiv.ofRingEquiv (f := σ) fun a => ?_, ?_⟩
  · have h1 := hσ (algebraMap F F⟮x⟯ a)
    rw [AlgEquiv.coe_ringEquiv, AlgEquiv.commutes] at h1
    rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h1
  · have := hσ (AdjoinSimple.gen F x)
    rw [AlgEquiv.coe_ringEquiv, minpoly.algEquiv_apply] at this
    simpa using this

private theorem mem_bot_iff_forall_algEquiv_apply_eq {Ω F : Type*} [Field Ω] [IsAlgClosed Ω]
    [Field F] [Algebra F Ω] [PerfectField F] {x : Ω} :
    x ∈ (⊥ : IntermediateField F Ω) ↔ ∀ σ : Ω ≃ₐ[F] Ω, σ x = x := by
  refine ⟨fun hx σ => ?_, fun h => ?_⟩
  · obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.mp hx
    exact σ.commutes a
  by_contra hx
  by_cases halg : IsAlgebraic F x
  · have hsep : IsSeparable F x :=
      PerfectField.separable_of_irreducible (minpoly.irreducible halg.isIntegral)
    have hx' : x ∉ (⊥ : Subalgebra F Ω) := by
      rwa [Algebra.mem_bot, ← IntermediateField.mem_bot]
    obtain ⟨y, hne, hy⟩ :=
      (notMem_iff_exists_ne_and_isConjRoot hsep (IsAlgClosed.splits _)).mp hx'
    obtain ⟨σ, hσ⟩ := exists_algEquiv_apply_eq_of_minpoly_eq halg hy
    exact hne (hσ ▸ h σ).symm
  · have htr : Transcendental F x := halg
    have htr' : Transcendental F (x + 1) := fun h' =>
      htr (by simpa using (h'.isIntegral.sub isIntegral_one).isAlgebraic)
    obtain ⟨σ, hσ⟩ := exists_algEquiv_apply_eq_of_transcendental htr htr'
    have := hσ.symm.trans (h σ)
    simp at this

private theorem charpoly_smul_inv_of_charpoly_eq_prod (n : ℕ) (M : GL (Fin n) ℂ) (t : ℂ) (s : Multiset ℂ)
    (h : (M : Matrix (Fin n) (Fin n) ℂ).charpoly = (s.map fun a => Polynomial.X - Polynomial.C a).prod) :
    (t • ((M⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)).charpoly
      = (s.map fun a => Polynomial.X - Polynomial.C (t * a⁻¹)).prod := by
  set A : Matrix (Fin n) (Fin n) ℂ := (M : Matrix (Fin n) (Fin n) ℂ) with hA
  set B : Matrix (Fin n) (Fin n) ℂ := ((M⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) with hB
  have hAB : A * B = 1 := by simp [hA, hB]
  have hcard : Multiset.card s = n := by
    have h1 := Matrix.charpoly_natDegree_eq_dim A
    rw [h, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card] at h1
    simpa using h1
  have hev : ∀ y : ℂ, (Matrix.scalar (Fin n) y - A).det = (s.map fun a => y - a).prod := by
    intro y
    rw [← Matrix.eval_charpoly, h, Polynomial.eval_multiset_prod, Multiset.map_map]
    simp
  have hdet : A.det * B.det = 1 := by rw [← Matrix.det_mul, hAB, Matrix.det_one]
  have hneg : (-A).det = (s.map fun a => -a).prod := by simpa using hev 0
  have hne : (-A).det ≠ 0 := by
    rw [Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (left_ne_zero_of_mul_eq_one hdet)
  have hs : ∀ a ∈ s, a ≠ 0 := by
    intro a ha h0
    apply hne
    rw [hneg]
    exact Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨a, ha, by simp [h0]⟩)
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.Infinite.mono (s := ({0} : Set ℂ)ᶜ) ?_ (Set.finite_singleton _).infinite_compl
  intro x hx
  have hx0 : x ≠ 0 := hx
  simp only [Set.mem_ofPred_eq]
  rw [Matrix.eval_charpoly, Polynomial.eval_multiset_prod, Multiset.map_map]
  apply mul_left_cancel₀ hne
  have key : (-A) * (Matrix.scalar (Fin n) x - t • B)
      = x • (Matrix.scalar (Fin n) (t / x) - A) := by
    rw [Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
      ← Matrix.smul_one_eq_diagonal, mul_sub, Matrix.mul_smul, Matrix.mul_smul, neg_mul, neg_mul, hAB, mul_one,
      smul_sub, smul_smul, mul_div_cancel₀ _ hx0, smul_neg, smul_neg]
    abel
  rw [← Matrix.det_mul, key, Matrix.det_smul, hev, hneg, ← Multiset.prod_map_mul, Fintype.card_fin,
    ← hcard, ← Multiset.prod_replicate, ← Multiset.map_const', ← Multiset.prod_map_mul]
  congr 1
  apply Multiset.map_congr rfl
  intro a ha
  have := hs a ha
  simp only [Function.comp, eval_sub, eval_X, eval_C]
  field_simp
  ring

theorem exists_int_of_fixed {x : ℂ} (hx : IsIntegral ℤ x) (h : ∀ σ : ℂ ≃+* ℂ, σ x = x) : ∃ n : ℤ, (n : ℂ) = x := by
  have h1 : x ∈ (⊥ : IntermediateField ℚ ℂ) :=
    mem_bot_iff_forall_algEquiv_apply_eq.2 fun σ => h σ.toRingEquiv
  obtain ⟨q, rfl⟩ := IntermediateField.mem_bot.1 h1
  have h2 : IsIntegral ℤ q := (isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).1 hx
  obtain ⟨n, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  exact ⟨n, by simp⟩

theorem exists_int_prod {S : Type*} [Fintype S] (f : S → ℂ) (hi : ∀ s, IsIntegral ℤ (f s))
    (hc : ∀ σ : ℂ ≃+* ℂ, ∃ e : S ≃ S, ∀ s, f (e s) = σ (f s)) : ∃ n : ℤ, (n : ℂ) = ∏ s, f s := by
  refine exists_int_of_fixed (IsIntegral.prod _ fun s _ => hi s) fun σ => ?_
  obtain ⟨e, he⟩ := hc σ
  rw [map_prod, ← e.prod_comp f]
  exact Finset.prod_congr rfl fun s _ => (he s).symm

theorem log_abs_le {S : Type*} [Fintype S] (f : S → ℂ) (n : ℤ) (hn : (n : ℂ) = ∏ s, f s) (h0 : ∀ s, f s ≠ 0)
    (R : ℝ) (hR : ∀ s, ‖f s‖ ≤ R) : n ≠ 0 ∧ Real.log |(n : ℝ)| ≤ Fintype.card S * Real.log R := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact Finset.prod_ne_zero_iff.2 (fun s _ => h0 s) (by rw [← hn]; simp)
  refine ⟨hn0, ?_⟩
  have e : |(n : ℝ)| = ∏ s, ‖f s‖ := by rw [← norm_prod, ← hn, Complex.norm_intCast]
  rw [e, Real.log_prod (fun s _ => norm_ne_zero_iff.2 (h0 s))]
  calc ∑ s, Real.log ‖f s‖ ≤ ∑ _s : S, Real.log R :=
        Finset.sum_le_sum fun s _ => Real.log_le_log (norm_pos_iff.2 (h0 s)) (hR s)
    _ = _ := by simp

theorem norm_le_one {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) {x : ℂ} (hx : IsIntegral ℤ x) : ‖ι.symm x‖ ≤ 1 := by
  have h0 : IsIntegral ℤ (ι.symm x) := by
    convert map_isIntegral_int (ι.symm : ℂ →+* PadicAlgCl l) hx using 1 <;> first | exact Subsingleton.elim _ _ | rfl
  have h1 : IsIntegral (NormedField.valuation (K := PadicAlgCl l)).integer (ι.symm x) := h0.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := PadicAlgCl l))).mem_of_integral h1
  have h3 : ‖ι.symm x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem norm_le_prod {l : ℕ} [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ) {S : Type*} [Fintype S] (f : S → ℂ)
    (hi : ∀ s, IsIntegral ℤ (f s)) (n : ℤ) (hn : (n : ℂ) = ∏ s, f s) {T : Type*} [Fintype T] (j : T → S)
    (hj : Function.Injective j) : ‖(n : PadicAlgCl l)‖ ≤ ∏ t, ‖ι.symm (f (j t))‖ := by
  classical
  have e : (n : PadicAlgCl l) = ∏ s, ι.symm (f s) := by rw [← map_prod, ← hn, map_intCast]
  rw [e, norm_prod, ← Finset.prod_image (s := Finset.univ) (g := j) (f := fun s => ‖ι.symm (f s)‖) hj.injOn]
  exact Finset.prod_le_prod_of_subset_of_le_one (Finset.subset_univ _) (fun _ _ => norm_nonneg _)
    fun s _ _ => norm_le_one ι (hi s)

theorem exists_unit_pow (k : ℕ) [NeZero k] (σ : ℂ ≃+* ℂ) :
    ∃ b : (ZMod k)ˣ, ∀ z : ℂ, z ^ k = 1 → σ z = z ^ (b : ZMod k).val := by
  refine ⟨modularCyclotomicCharacter ℂ (n := k) (by simpa using Complex.card_rootsOfUnity k) σ, fun z hz => ?_⟩
  exact modularCyclotomicCharacter.spec ℂ _ σ (rootsOfUnity.mkOfPowEq z hz).2

theorem pow_val_mul {k : ℕ} [NeZero k] {z : ℂ} (hz : z ^ k = 1) (a b : ZMod k) : z ^ (a * b).val = (z ^ a.val) ^ b.val := by
  rw [← pow_mul, ZMod.val_mul, ← pow_eq_pow_mod _ hz]

theorem trace_eq_sum {K : Type*} [Field K] (ι : K ≃+* ℂ) {n : ℕ} (g : Matrix (Fin n) (Fin n) K) (B : Multiset ℂ)
    (h : g.charpoly.map ι.toRingHom = (B.map fun b => Polynomial.X - Polynomial.C b).prod) :
    g.trace = ι.symm B.sum := by
  rw [← Matrix.charpoly_map] at h
  have h1 := Matrix.trace_eq_sum_roots_charpoly (g.map ι.toRingHom)
  rw [h, roots_multiset_prod_X_sub_C] at h1
  rw [← h1, RingEquiv.eq_symm_apply]
  simp [Matrix.trace]

theorem trace_eq_sum_of_inv {K : Type*} [Field K] (ι : K ≃+* ℂ) {n : ℕ} (g : GL (Fin n) K) (B : Multiset ℂ)
    (h : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).charpoly.map ι.toRingHom =
      ((B.map (·⁻¹)).map fun b => Polynomial.X - Polynomial.C b).prod) :
    (g : Matrix (Fin n) (Fin n) K).trace = ι.symm B.sum := by
  refine trace_eq_sum ι _ B ?_
  rw [← Matrix.charpoly_map] at h ⊢
  have h1 := charpoly_smul_inv_of_charpoly_eq_prod n (Matrix.GeneralLinearGroup.map ι.toRingHom g⁻¹) 1 _ h
  rw [map_inv, inv_inv, one_smul, Multiset.map_map] at h1
  simpa using h1

private theorem cardinalMk_padic_eq_continuum (l : ℕ) [Fact l.Prime] : #ℚ_[l] = 𝔠 := by
  apply le_antisymm
  · have hd := Padic.denseRange_ratCast l
    have h : ∀ x : ℚ_[l], ∃ u : ℕ → ℚ, Filter.Tendsto (fun n => (u n : ℚ_[l])) Filter.atTop (nhds x) := fun x => by
      obtain ⟨v, hv, hx⟩ := mem_closure_iff_seq_limit.1 (hd x); choose u hu using hv
      exact ⟨u, by simpa only [hu] using hx⟩
    choose u hu using h
    have hi : Function.Injective u := fun x y hxy => tendsto_nhds_unique (hu x) (hxy ▸ hu y)
    exact (Cardinal.mk_le_of_injective hi).trans (by simp)
  · obtain ⟨g, -, -, hg⟩ := (PerfectSpace.univ_perfect (α := ℚ_[l])).exists_nat_bool_injection Set.univ_nonempty
    calc 𝔠 = #(ℕ → Bool) := by rw [← Cardinal.power_def, Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.two_power_aleph0]
      _ ≤ #ℚ_[l] := Cardinal.mk_le_of_injective hg

private theorem cardinalMk_padicAlgCl_eq_continuum (l : ℕ) [Fact l.Prime] : #(PadicAlgCl l) = 𝔠 :=
  le_antisymm
    ((Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[l] (PadicAlgCl l)).trans
      (max_le (cardinalMk_padic_eq_continuum l).le Cardinal.aleph0_le_continuum))
    (cardinalMk_padic_eq_continuum l ▸ Cardinal.mk_le_of_injective (algebraMap ℚ_[l] (PadicAlgCl l)).injective)

private theorem nonempty_padicAlgCl_ringEquiv_complex (l : ℕ) [Fact l.Prime] :
    Nonempty (PadicAlgCl l ≃+* ℂ) :=
  IsAlgClosed.ringEquiv_of_equiv_of_charZero
    (by rw [cardinalMk_padicAlgCl_eq_continuum]; exact Cardinal.aleph0_lt_continuum)
    (Cardinal.eq.mp (by rw [cardinalMk_padicAlgCl_eq_continuum, Cardinal.mk_complex]))

private theorem exists_ringEquiv_over (R K L : Type) [Field R] [Field K] [Field L] [IsAlgClosed K]
    [IsAlgClosed L] [Algebra R K] [Algebra R L] (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K) (hKL : #K = #L) :
    ∃ e : K ≃+* L, ∀ x : R, e (algebraMap R K x) = algebraMap R L x := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis R L
  obtain ⟨e⟩ : Nonempty (s ≃ t) := Cardinal.eq.1
    ((IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs hR hK).symm.trans
      (hKL.trans (IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hR (hKL ▸ hK))))
  let _ := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  let _ := IsAlgClosed.isAlgClosure_of_transcendence_basis _ ht
  let e0 : Algebra.adjoin R (Set.range ((↑) : s → K)) ≃ₐ[R] Algebra.adjoin R (Set.range ((↑) : t → L)) :=
    hs.1.aevalEquiv.symm.trans ((MvPolynomial.renameEquiv R e).trans ht.1.aevalEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv K L e0.toRingEquiv, fun x => ?_⟩
  rw [IsScalarTower.algebraMap_apply R (Algebra.adjoin R (Set.range ((↑) : s → K))) K,
    IsAlgClosure.equivOfEquiv_algebraMap, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]

private theorem move {F : Type} [Field F] [Countable F] (l : ℕ) [Fact l.Prime] (f : F →+* ℂ) (g : F →+* PadicAlgCl l) :
    ∃ ι : PadicAlgCl l ≃+* ℂ, ∀ a, ι.symm (f a) = g a := by
  let := f.toAlgebra; let := g.toAlgebra; obtain ⟨ι₀⟩ := nonempty_padicAlgCl_ringEquiv_complex l
  obtain ⟨e, he⟩ := exists_ringEquiv_over F ℂ (PadicAlgCl l) Cardinal.mk_le_aleph0
    (Cardinal.mk_complex ▸ Cardinal.aleph0_lt_continuum) (Cardinal.mk_congr ι₀.symm.toEquiv)
  exact ⟨e.symm, he⟩

private theorem move_transc (l : ℕ) [Fact l.Prime] {z : ℂ} (hz : Transcendental ℚ z) {t : PadicAlgCl l}
    (ht : Transcendental ℚ t) : ∃ ι : PadicAlgCl l ≃+* ℂ, ι.symm z = t := by
  let F := FractionRing (Polynomial ℚ)
  have hP : Countable (Polynomial ℚ) :=
    Cardinal.mk_le_aleph0_iff.1 (by have := Polynomial.cardinalMk_le_max (R := ℚ); rwa [Cardinal.mkRat, max_self] at this)
  have hF : Countable F := (IsLocalization.mk'_surjective (nonZeroDivisors (Polynomial ℚ))).countable
  obtain ⟨e, he⟩ := move (F := F) l (IsFractionRing.lift (transcendental_iff_injective.1 hz))
    (IsFractionRing.lift (transcendental_iff_injective.1 ht))
  exact ⟨e, by simpa using he (algebraMap (Polynomial ℚ) F Polynomial.X)⟩

private theorem move_alg (l : ℕ) [Fact l.Prime] {z : ℂ} (hz : IsIntegral ℚ z) {t : PadicAlgCl l}
    (ht : t ∈ (minpoly ℚ z).aroots (PadicAlgCl l)) : ∃ ι : PadicAlgCl l ≃+* ℂ, ι.symm z = t := by
  have := IntermediateField.adjoin.finiteDimensional hz
  have : Countable ℚ⟮z⟯ := Countable.of_equiv _ (Module.finBasis ℚ ℚ⟮z⟯).equivFun.toEquiv.symm
  obtain ⟨e, he⟩ := move (F := ℚ⟮z⟯) l (algebraMap _ ℂ)
    ((IntermediateField.algHomAdjoinIntegralEquiv ℚ hz).symm ⟨t, ht⟩).toRingHom
  exact ⟨e, (he (IntermediateField.AdjoinSimple.gen ℚ z)).trans
    (IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hz ⟨t, ht⟩)⟩

private theorem norm_rat (l : ℕ) [Fact l.Prime] (q : ℚ) : ‖(q : PadicAlgCl l)‖ = ‖(q : ℚ_[l])‖ := by
  rw [← map_ratCast (algebraMap ℚ_[l] (PadicAlgCl l))]
  exact norm_algebraMap' _ _

theorem isIntegral_of_norm_le (x : ℂ) (h : ∀ (l : ℕ) [Fact l.Prime] (ι : PadicAlgCl l ≃+* ℂ), ‖ι.symm x‖ ≤ 1) :
    IsIntegral ℤ x := by
  have halg : IsAlgebraic ℚ x := by
    by_contra hx
    obtain ⟨ι₀⟩ := nonempty_padicAlgCl_ringEquiv_complex 2
    have ht : Transcendental ℚ (ι₀.symm x + ((1 / 4 : ℚ) : PadicAlgCl 2)) := fun h1 => hx (by
      have h2 : IsAlgebraic ℚ (ι₀.symm x) := by
        simpa using h1.sub (isAlgebraic_ratCast ℚ (1 / 4 : ℚ))
      simpa using h2.algHom ({ ι₀.toRingHom with commutes' := fun r => by simp } : PadicAlgCl 2 →ₐ[ℚ] ℂ))
    obtain ⟨ι, hι⟩ := move_transc 2 hx ht
    have h1 := h 2 ι
    have h2 := h 2 ι₀
    rw [hι] at h1
    have h3 := norm_sub_le (ι₀.symm x + ((1 / 4 : ℚ) : PadicAlgCl 2)) (ι₀.symm x)
    rw [add_sub_cancel_left, norm_rat] at h3
    have h4 : ‖((1 / 4 : ℚ) : ℚ_[2])‖ = 4 := by
      have := Padic.norm_p_zpow (p := 2) (-2)
      norm_num at this ⊢
      rw [← this]
    linarith
  have hx := halg.isIntegral
  have hm := minpoly.monic hx
  have hc : ∀ i, (minpoly ℚ x).coeff i ∈ Set.range (algebraMap ℤ ℚ) := by
    intro i
    set q := (minpoly ℚ x).coeff i with hq
    refine ⟨q.num, Rat.coe_int_num_of_den_eq_one ?_⟩
    by_contra hd
    obtain ⟨l, hl, hld⟩ := Nat.exists_prime_and_dvd hd
    have := Fact.mk hl
    let S : Subring (PadicAlgCl l) := (NormedField.valuation (K := PadicAlgCl l)).integer
    have hS : ∀ y, y ∈ S ↔ ‖y‖ ≤ 1 := fun y => Iff.rfl
    have h1 : (minpoly ℚ x).map (algebraMap ℚ (PadicAlgCl l)) ∈ lifts S.subtype := by
      rw [(IsAlgClosed.splits _).eq_prod_roots_of_monic (hm.map _)]
      refine Subsemiring.multiset_prod_mem _ _ fun y hy => ?_
      obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hy
      obtain ⟨ι, hι⟩ := move_alg l hx ht
      exact ⟨Polynomial.X - Polynomial.C ⟨t, (hS t).2 (hι ▸ h l ι)⟩, by simp⟩
    obtain ⟨y, hy⟩ := (lifts_iff_coeff_lifts _).1 h1 i
    have h2 : ‖(q : ℚ_[l])‖ ≤ 1 := by
      rw [← norm_rat, ← hS]
      rw [Polynomial.coeff_map] at hy
      exact (show (q : PadicAlgCl l) = y from hy.symm) ▸ y.2
    have h3 := PadicInt.isUnit_den q h2
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff] at h3
    exact (Nat.Prime.coprime_iff_not_dvd hl).1 h3 hld
  obtain ⟨f, hf, -, hfm⟩ := lifts_and_natDegree_eq_and_monic ((lifts_iff_coeff_lifts _).2 hc) hm
  exact ⟨f, hfm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ, hf, minpoly.aeval]⟩

theorem norm_root_eq_one {Γ k : Type*} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [NormedField k] {n : ℕ}
    (r : Γ →* GL (Fin n) k) (hr : Continuous r) (g : Γ) (b : k)
    (hb : (r g : Matrix (Fin n) (Fin n) k).charpoly.IsRoot b) : ‖b‖ = 1 := by
  rw [IsRoot, Matrix.eval_charpoly, ← Matrix.exists_mulVec_eq_zero_iff] at hb
  obtain ⟨v, hv, e⟩ := hb
  have e1 : (r g : Matrix (Fin n) (Fin n) k) *ᵥ v = b • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at e
    rw [← e]; ext i; simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  let f : Γ → ℝ := fun s => ‖(r s : Matrix (Fin n) (Fin n) k) *ᵥ v‖
  have hf : Continuous f := ((Units.continuous_val.comp hr).matrix_mulVec continuous_const).norm
  have hpos : ∀ s, 0 < f s := fun s => norm_pos_iff.2 fun h0 => hv (by
    have := congrArg (fun y => (r s⁻¹ : Matrix (Fin n) (Fin n) k) *ᵥ y) h0
    simpa only [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec,
      Matrix.mulVec_zero] using this)
  have hm : ∀ s, f (s * g) = ‖b‖ * f s := fun s => by
    simp only [f, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, e1, Matrix.mulVec_smul, norm_smul]
  obtain ⟨s, -, hs⟩ := isCompact_univ.exists_isMaxOn ⟨1, trivial⟩ hf.continuousOn
  obtain ⟨t, -, ht⟩ := isCompact_univ.exists_isMinOn ⟨1, trivial⟩ hf.continuousOn
  have h1 : f (s * g) ≤ f s := hs trivial
  have h2 : f t ≤ f (t * g) := ht trivial
  rw [hm] at h1 h2
  have := hpos s
  have := hpos t
  apply le_antisymm <;> nlinarith

end TranscAndConjugates

end RHDirect.Stage13GL_LocalDvrNakayama
