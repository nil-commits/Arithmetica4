import RHDirect.CapelliCore
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Primorial
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity

/-!
# RHDirect.Stage13GL_BernoulliAndWeylAlg
Option-C GaloisLibrary Wave 1 (Module 2 of 3): **Generalized Bernoulli Numbers,
Weyl Algebra Quantum Determinants, and Infinitesimal Character Pullback**,
surgically ported and compressed onto concrete Mathlib types and `RHDirect.CapelliCore`
(zero invented proxy structures, zero open parameters, zero `sorry`, zero custom axioms).
## Contents
1. **Generalized Bernoulli Numbers, Special Values & Ultrametric Bounds** (`38` source files):
   - Concrete `bcoef`, `genB`, `primVal`, `Bprim`, `Lprim`, `charSet`, `parKer`, `den`, `bnd`.
   - Exponential generating function (`b_egf`), Raabe multiplication (`b_raabe`), shift/scaling/
     reflection (`b_shift`), binomial expansion (`b_expand`), `k = 1` formula (`b_one`),
     distribution (`b_comp`), prime & general level-raising Euler factors (`b_step`, `b_level`,
     `b_primlevel`), character transport & Galois bijection (`b_condmap`, `b_primmap`, `b_charbij`,
     `b_parity`).
   - Primorial denominators & `ℤ`-integrality (`b_primden`, `b_denint`, `b_denchar`, `b_primmem`),
     analytic upper bounds (`b_polybound`, `b_upper`, `b_denupper`), Galois-descent rational &
     nonzero-integer character products (`b_ratprod`, `b_prodint`).
   - Hurwitz zeta & Dirichlet `L`-function special values (`b_taylor2`, `b_termsum`, `b_termdiff`,
     `b_hurzero`, `b_lval`, `b_lprim`), Gauss sum & functional equation (`b_gauss`, `b_fe`),
     characteristic-0 nonvanishing (`b_nzC`, `b_nzany`), and ultrametric valuation bounds
     (`b_ultra`, `b_sumval`).
2. **Quantum Determinant Foundations on `RHDirect.CapelliCore`**:
   - Row/column skew-symmetry (`qminor_swap_adjacent`, `qminor_comp_perm`, `qminor_eq_zero`),
     `GL_n`-conjugation invariance (`qdet_conj`), semiconjugation (`qdet_semiconj`), centrality
     (`qdet_central`), highest-weight eigenvalue (`qdet_hw`), functoriality (`map_qdet`),
     spectral shift (`qdet_shift`), and Zariski density of `GL_n(ℂ)` (`eq_of_eval_eq_on_gl`).
3. **Weyl Algebra, Polynomial Representations & Highest-Weight Quantum Determinants** (`25` source files):
   - Concrete polynomial `GL_n(ℂ)`-representations `Pre n`, infinitesimal Lie action `Pre.D` /
     `Pre.E`, `HasWt`, `IsTop`, `Pol n`, `rtr`, `minor`.
   - Curve differentiation (`coefDiff`, `curve`, `adEq`, `invCurve`, `bracket`, `glRel`),
     quantum determinant commutation & intertwining (`qdetComm`, `qdetHW`, `qdetRect`, `commAll`),
     submodule matrix reduction (`subMat`, `preSub`, `irrSub`), highest-weight minor theory
     (`topLie`, `minorDeg`, `minorRtr`, `topPol`, `rtrMul`, `rtrDeg`, `rtrPoly`, `polPre`, `degRank`),
     and scalar quantum-determinant realization (`scalar`, `existsScalar`).
4. **Adelic Smooth Representations & Infinitesimal Character Pullback** (`HasInfCharPullSub`):
   - Concrete Mathlib-backed `Cinf E`, `Ad E`, `Af E`, `GA E a`, `Lie E a`, `Sm E a`, `rt`,
     `lie`, `lieS`, `Eop`, `cap` (via `CapelliCore.qdet`), `Zalg`, `CuspSub`, `CG`, `HasInfChar`,
     `IsRegAlg`, `HasSatGL`, `HasSat`.
   - Ring-isomorphism pullback `cinf`, `finMap`, `adm`, `gaMap`, `pull`, `pullSub`, proving
     `cap_pull`, `isAutForm_pull`, `isCuspidal_pull`, `hasInfChar_pullSub`, `isRegAlg_pullSub`,
     `hasSatGL_of_equiv`, and `hasSat_pullSub`.
-/
noncomputable section

namespace RHDirect.Stage13GL_BernoulliAndWeylAlg

/-! ## Section 1: Generalized Bernoulli Numbers, Special Values & Ultrametric Bounds -/

section BernoulliNumbers
open Finset
/-- Rational generalized Bernoulli summand `N^{k-1} B_k(a/N)`. -/
def bcoef (N k a : ℕ) : ℚ :=
  (N : ℚ) ^ ((k : ℤ) - 1) * (Polynomial.bernoulli k).eval ((a : ℚ) / N)
/-- Generalized Bernoulli number `B_{k, Φ} = ∑_{a=1}^N Φ(a) bcoef(N, k, a)`. -/
def genB {R : Type*} [CommRing R] [Algebra ℚ R] {N : ℕ} (k : ℕ) (Φ : ZMod N → R) : R :=
  ∑ a ∈ Icc 1 N, Φ (a : ZMod N) * algebraMap ℚ R (bcoef N k a)
/-- Primitive character evaluation `χ.primitiveCharacter (a : ZMod χ.conductor)`. -/
def primVal {R : Type*} [CommRing R] {N : ℕ} (χ : DirichletCharacter R N) (a : ℕ) : R :=
  χ.primitiveCharacter (a : ZMod χ.conductor)
/-- Primitive generalized Bernoulli number `B_{k, χ_0}`. -/
def Bprim {R : Type*} [CommRing R] [Algebra ℚ R] {N : ℕ} (k : ℕ) (χ : DirichletCharacter R N) : R :=
  genB k (χ.primitiveCharacter : ZMod χ.conductor → R)
/-- Primitive Dirichlet `L`-function `L(s, χ_0)`. -/
def Lprim {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  χ.primitiveCharacter.LFunction s
/-- Dirichlet characters modulo `N` whose kernel lies in `P`. -/
def charSet (Ω : Type*) [CommRing Ω] {N : ℕ} (P : Set (Subgroup (ZMod N)ˣ)) :
    Set (DirichletCharacter Ω N) :=
  {χ | χ.toUnitHom.ker ∈ P}
/-- Kernel-parity predicate selecting characters with `χ(-1) = (-1)^k`. -/
def parKer (N k : ℕ) : Set (Subgroup (ZMod N)ˣ) :=
  {K | (-1 : (ZMod N)ˣ) ∈ K ↔ Even k}
/-- Universal denominator `N * primorial (k + 1)` clearing `genB k Φ` and `Bprim k χ`. -/
def den (N k : ℕ) : ℕ := N * primorial (k + 1)
/-- Explicit archimedean upper bound `16 * N^{k+1} * k!`. -/
def bnd (N k : ℕ) : ℝ := 16 * (N : ℝ) ^ (k + 1) * (k.factorial : ℝ)
theorem map_genB {R S : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S]
    {N : ℕ} (f : R →+* S) (k : ℕ) (Φ : ZMod N → R) :
    f (genB k Φ) = genB k (fun a => f (Φ a)) := by
  unfold genB
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, RingHom.map_rat_algebraMap]
theorem map_genB_char {R S : Type*} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S]
    {N : ℕ} (f : R →+* S) (k : ℕ) (χ : DirichletCharacter R N) :
    f (genB k χ) = genB k (χ.ringHomComp f : ZMod N → S) := by
  rw [map_genB]
  congr 1
theorem genB_mem {R : Type*} [CommRing R] [Algebra ℚ R] {N : ℕ} (k : ℕ)
    (Φ : ZMod N → R) (A : Subalgebra ℚ R) (h : ∀ a, Φ a ∈ A) : genB k Φ ∈ A := by
  unfold genB
  exact A.sum_mem fun a _ => A.mul_mem (h _) (A.algebraMap_mem _)
theorem Bprim_eq {R : Type*} [CommRing R] [Algebra ℚ R] {N : ℕ} (k : ℕ)
    (χ : DirichletCharacter R N) :
    Bprim k χ = ∑ a ∈ Icc 1 χ.conductor, primVal χ a * algebraMap ℚ R (bcoef χ.conductor k a) :=
  rfl
theorem den_pos {N : ℕ} (hN : 0 < N) (k : ℕ) : 0 < den N k :=
  Nat.mul_pos hN (primorial_pos _)
theorem den_dvd {M N : ℕ} (h : M ∣ N) (k : ℕ) : den M k ∣ den N k :=
  Nat.mul_dvd_mul_right h _
theorem b_sumicc :
    ∀ {M : Type} [AddCommMonoid M] {N : ℕ} [NeZero N] (G : ZMod N → M),
      ∑ a ∈ Icc 1 N, G (a : ZMod N) = ∑ a : ZMod N, G a := by
  intro M _ N _ G
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  refine Finset.sum_nbij' (fun a : ℕ => (a : ZMod N))
    (fun x : ZMod N => if x.val = 0 then N else x.val) ?_ ?_ ?_ ?_ ?_
  · intro a _; exact Finset.mem_univ _
  · intro x _
    have hx := ZMod.val_lt x
    refine Finset.mem_Icc.2 ?_
    split_ifs with h0
    · exact ⟨hN, le_rfl⟩
    · exact ⟨Nat.pos_of_ne_zero h0, hx.le⟩
  · intro a ha
    have ha' := Finset.mem_Icc.1 ha
    simp only [ZMod.val_natCast]
    rcases Nat.lt_or_ge a N with h | h
    · rw [Nat.mod_eq_of_lt h, if_neg (by omega)]
    · have hEq : a = N := by omega
      subst hEq; simp
  · intro x _
    split_ifs with h0
    · rw [ZMod.natCast_self]; exact ((ZMod.val_eq_zero x).1 h0).symm
    · exact ZMod.natCast_zmod_val x
  · intro _ _; rfl
theorem b_egf :
    ∀ (N a : ℕ), 0 < N →
      (PowerSeries.mk fun k => bcoef N k a / (k.factorial : ℚ)) *
          (PowerSeries.rescale (N : ℚ) (PowerSeries.exp ℚ) - 1) =
        PowerSeries.X * PowerSeries.rescale (a : ℚ) (PowerSeries.exp ℚ) := by
  intro N a hN
  have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have h := congrArg (PowerSeries.rescale (N : ℚ))
    (Polynomial.bernoulli_generating_function ((a : ℚ) / N))
  rw [map_mul, map_mul, map_sub, map_one, PowerSeries.rescale_mk, PowerSeries.rescale_X,
    PowerSeries.rescale_rescale] at h
  have hc : ((a : ℚ) / N) * N = a := by field_simp
  rw [hc] at h
  have hmk : (PowerSeries.mk fun k => bcoef N k a / (k.factorial : ℚ)) =
      PowerSeries.C (1 / (N : ℚ)) * PowerSeries.mk (fun n => (N : ℚ) ^ n *
        (Polynomial.aeval ((a : ℚ) / N)) ((1 / (n.factorial : ℚ)) • Polynomial.bernoulli n)) := by
    ext n
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    simp only [bcoef, map_smul, Polynomial.coe_aeval_eq_eval, smul_eq_mul]
    rw [zpow_sub_one₀ hN', zpow_natCast]
    have hf : (n.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
    field_simp
  rw [hmk, mul_assoc, h, ← mul_assoc, ← mul_assoc, ← map_mul, one_div_mul_cancel hN', map_one, one_mul]
theorem b_raabe :
    ∀ (N m k a : ℕ), 0 < N → 0 < m →
      bcoef N k a = ∑ j ∈ range m, bcoef (N * m) k (a + j * N) := by
  intro N m k a hN hm
  let F : ℕ → ℕ → PowerSeries ℚ := fun M c => PowerSeries.mk fun i => bcoef M i c / (i.factorial : ℚ)
  let y : PowerSeries ℚ := PowerSeries.rescale (N : ℚ) (PowerSeries.exp ℚ)
  let E : PowerSeries ℚ := PowerSeries.rescale ((N * m : ℕ) : ℚ) (PowerSeries.exp ℚ) - 1
  have hpow : ∀ j : ℕ, y ^ j = PowerSeries.rescale ((j : ℚ) * N) (PowerSeries.exp ℚ) := by
    intro j; simp only [y]
    rw [← map_pow, PowerSeries.exp_pow_eq_rescale_exp, PowerSeries.rescale_rescale]
  have hE : E = (∑ j ∈ range m, y ^ j) * (y - 1) := by
    rw [geom_sum_mul, hpow]; simp only [E]; push_cast; rw [mul_comm (m : ℚ)]
  have hE0 : E ≠ 0 := by
    intro h
    have h1 := congrArg (PowerSeries.coeff 1) h
    simp [E, PowerSeries.coeff_rescale, PowerSeries.coeff_exp] at h1
    rcases h1 with h1 | h1
    · exact hN.ne' h1
    · exact hm.ne' h1
  suffices h : F N a = ∑ j ∈ range m, F (N * m) (a + j * N) by
    have h2 := congrArg (PowerSeries.coeff k) h
    rw [map_sum] at h2
    simp only [F, PowerSeries.coeff_mk] at h2
    rw [← Finset.sum_div, div_left_inj' (by positivity)] at h2
    exact h2
  apply mul_right_cancel₀ hE0
  calc F N a * E = F N a * (y - 1) * ∑ j ∈ range m, y ^ j := by rw [hE]; ring
    _ = PowerSeries.X * PowerSeries.rescale (a : ℚ) (PowerSeries.exp ℚ) * ∑ j ∈ range m, y ^ j := by
        rw [b_egf N a hN]
    _ = ∑ j ∈ range m, PowerSeries.X * PowerSeries.rescale ((a + j * N : ℕ) : ℚ) (PowerSeries.exp ℚ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hpow, mul_assoc, PowerSeries.exp_mul_exp_eq_exp_add]; push_cast; rfl
    _ = ∑ j ∈ range m, F (N * m) (a + j * N) * E := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [b_egf (N * m) (a + j * N) (Nat.mul_pos hN hm)]
    _ = (∑ j ∈ range m, F (N * m) (a + j * N)) * E := by rw [Finset.sum_mul]
theorem b_shift :
    ∀ (N k a : ℕ), 0 < N →
      bcoef N k (a + N) = bcoef N k a + (k : ℚ) * (a : ℚ) ^ (k - 1) ∧
      (∀ m : ℕ, 0 < m → bcoef (m * N) k (m * a) = (m : ℚ) ^ ((k : ℤ) - 1) * bcoef N k a) ∧
      (a ≤ N → bcoef N k (N - a) = (-1) ^ k * bcoef N k a) := by
  intro N k a hN
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨?_, ?_, ?_⟩
  · unfold bcoef
    have e : ((a + N : ℕ) : ℚ) / N = 1 + (a : ℚ) / N := by push_cast; field_simp; ring
    rw [e, Polynomial.bernoulli_eval_one_add, mul_add]
    congr 1
    rcases k with _ | k
    · simp
    · have : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by push_cast; ring
      rw [this, zpow_natCast, Nat.add_sub_cancel, div_pow]; field_simp
  · intro m hm
    have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    unfold bcoef
    have e : ((m * a : ℕ) : ℚ) / ((m * N : ℕ) : ℚ) = (a : ℚ) / N := by push_cast; field_simp
    rw [e, Nat.cast_mul, mul_zpow, mul_assoc]
  · intro h
    unfold bcoef
    have e : ((N - a : ℕ) : ℚ) / N = 1 - (a : ℚ) / N := by rw [Nat.cast_sub h]; field_simp
    rw [e, Polynomial.bernoulli_eval_one_sub]; ring
theorem b_expand :
    ∀ (N k a : ℕ), 0 < N →
      bcoef N k a = ∑ j ∈ range (k + 1), (k.choose j : ℚ) * bernoulli j * (N : ℚ) ^ ((j : ℤ) - 1) * (a : ℚ) ^ (k - j) := by
  intro N k a hN
  have hN' : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  simp only [bcoef]
  rw [Polynomial.bernoulli, Polynomial.eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [Polynomial.eval_monomial, div_pow]
  have hsplit : (N : ℚ) ^ ((k : ℤ) - 1) = (N : ℚ) ^ ((j : ℤ) - 1) * (N : ℚ) ^ ((k - j : ℕ) : ℤ) := by
    rw [← zpow_add₀ hN']; congr 1; push_cast [hjk]; ring
  rw [hsplit, zpow_natCast]
  have hp : (N : ℚ) ^ (k - j) ≠ 0 := pow_ne_zero _ hN'
  field_simp
private theorem b_one_sum {R : Type} [AddCommMonoid R] {N : ℕ} [NeZero N] (Φ : ZMod N → R) :
    ∑ a ∈ Icc 1 N, Φ (a : ZMod N) = ∑ a : ZMod N, Φ a :=
  b_sumicc Φ
theorem b_one :
    ∀ {R : Type} [CommRing R] [Algebra ℚ R] {N : ℕ} [NeZero N] (Φ : ZMod N → R),
      ∑ a : ZMod N, Φ a = 0 → (N : R) * genB 1 Φ = ∑ a ∈ Icc 1 N, Φ (a : ZMod N) * (a : R) := by
  intro R _ _ N _ Φ hΦ
  simp only [genB, bcoef, Polynomial.bernoulli_one]
  have hs : ∑ a ∈ Icc 1 N, Φ (a : ZMod N) = 0 := (b_one_sum Φ).trans hΦ
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have key : ∀ x : ℕ, (N : R) * (Φ (x : ZMod N) * algebraMap ℚ R
      ((N : ℚ) ^ ((1 : ℕ) - 1 : ℤ) * Polynomial.eval ((x : ℚ) / N) (Polynomial.X - Polynomial.C 2⁻¹))) =
      Φ (x : ZMod N) * (x : R) - algebraMap ℚ R ((N : ℚ) / 2) * Φ (x : ZMod N) := by
    intro x
    have e : (N : ℚ) * ((N : ℚ) ^ ((1 : ℕ) - 1 : ℤ) *
        Polynomial.eval ((x : ℚ) / N) (Polynomial.X - Polynomial.C 2⁻¹)) = (x : ℚ) - (N : ℚ) / 2 := by
      simp; field_simp
    calc (N : R) * (Φ (x : ZMod N) * algebraMap ℚ R ((N : ℚ) ^ ((1 : ℕ) - 1 : ℤ) *
          Polynomial.eval ((x : ℚ) / N) (Polynomial.X - Polynomial.C 2⁻¹)))
        = Φ (x : ZMod N) * algebraMap ℚ R ((N : ℚ) * ((N : ℚ) ^ ((1 : ℕ) - 1 : ℤ) *
            Polynomial.eval ((x : ℚ) / N) (Polynomial.X - Polynomial.C 2⁻¹))) := by
          rw [map_mul (algebraMap ℚ R) (N : ℚ), map_natCast]; ring
      _ = _ := by rw [e, map_sub, map_natCast]; ring
  rw [Finset.mul_sum]
  simp_rw [key]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hs, mul_zero, sub_zero]
private theorem sum_Icc_one_eq {R : Type} [AddCommMonoid R] (f : ℕ → R) (n : ℕ) :
    ∑ x ∈ Icc 1 n, f x = ∑ i ∈ range n, f (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
private theorem sum_Icc_mul_eq {R : Type} [AddCommMonoid R] (f : ℕ → R) (N m : ℕ) :
    ∑ x ∈ Icc 1 (N * m), f x = ∑ j ∈ range m, ∑ a ∈ Icc 1 N, f (a + j * N) := by
  simp_rw [sum_Icc_one_eq]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1; ring
theorem b_comp :
    ∀ {R : Type} [CommRing R] [Algebra ℚ R] {N M : ℕ} (h : N ∣ M) (k : ℕ) (Φ : ZMod N → R),
      0 < M → genB k (fun a : ZMod M => Φ (ZMod.castHom h (ZMod N) a)) = genB k Φ := by
  intro R _ _ N M h k Φ hM
  obtain ⟨m, rfl⟩ := h
  have hN : 0 < N := Nat.pos_of_ne_zero (by rintro rfl; simp at hM)
  have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hM)
  unfold genB
  rw [sum_Icc_mul_eq]
  simp_rw [b_raabe N m k _ hN hm, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
  congr 2; rw [map_natCast]; simp
private theorem valuation_power_identity {R : Type} [CommRing R] {N p : ℕ}
    (χ : DirichletCharacter R N) (hp : p.Prime) (a : ℕ) :
    DirichletCharacter.changeLevel (dvd_mul_right N p) χ (a : ZMod (N * p)) =
      χ (a : ZMod N) - if p ∣ a then χ (a : ZMod N) else 0 := by
  by_cases hc : a.Coprime (N * p)
  · have hpa : ¬ p ∣ a := fun h =>
      (Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.Coprime.coprime_mul_left_right hc).symm h
    rw [if_neg hpa, sub_zero]
    have := DirichletCharacter.changeLevel_eq_cast_of_dvd χ (dvd_mul_right N p) (ZMod.unitOfCoprime a hc)
    rw [ZMod.coe_unitOfCoprime, ZMod.cast_natCast (dvd_mul_right N p)] at this
    exact this
  · rw [MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])]
    split_ifs with h
    · simp
    · have : ¬ a.Coprime N := fun h' =>
        hc (Nat.Coprime.mul_right h' ((Nat.Prime.coprime_iff_not_dvd hp).2 h).symm)
      rw [MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime]), sub_zero]
private theorem sum_divisible_eq_sum_mul {R : Type} [AddCommMonoid R] {N p : ℕ} (hp : 0 < p)
    (f : ℕ → R) :
    ∑ a ∈ Icc 1 (N * p), (if p ∣ a then f a else 0) = ∑ b ∈ Icc 1 N, f (p * b) := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun b _ => p * b) ?_ ?_ ?_ ?_
  · intro b hb
    simp only [mem_Icc, mem_filter] at hb ⊢
    refine ⟨⟨Nat.mul_pos hp hb.1, ?_⟩, dvd_mul_right _ _⟩
    rw [mul_comm]; exact Nat.mul_le_mul_right _ hb.2
  · intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_left hp h
  · intro a ha
    simp only [mem_Icc, mem_filter] at ha
    obtain ⟨⟨h1, h2⟩, b, rfl⟩ := ha
    refine ⟨b, ?_, rfl⟩
    simp only [mem_Icc]
    exact ⟨Nat.pos_of_mul_pos_left h1, by rw [mul_comm] at h2; exact Nat.le_of_mul_le_mul_right h2 hp⟩
  · intro _ _; rfl
theorem b_step :
    ∀ {R : Type} [CommRing R] [Algebra ℚ R] {N p : ℕ} (k : ℕ) (χ : DirichletCharacter R N),
      0 < N → p.Prime → 1 ≤ k →
      genB k (DirichletCharacter.changeLevel (dvd_mul_right N p) χ : ZMod (N * p) → R) =
        (1 - χ (p : ZMod N) * (p : R) ^ (k - 1)) * genB k χ := by
  intro R _ _ N p k χ hN hp hk
  have hc := b_comp (dvd_mul_right N p) k (χ : ZMod N → R) (Nat.mul_pos hN hp.pos)
  rw [sub_mul, one_mul]
  nth_rewrite 1 [← hc]
  unfold genB
  simp only [valuation_power_identity χ hp, map_natCast, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul]
  congr 1
  rw [sum_divisible_eq_sum_mul hp.pos (fun a => χ (a : ZMod N) * algebraMap ℚ R (bcoef (N * p) k a)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hs := (b_shift N k b hN).2.1 p hp.pos
  have e : ((k : ℤ) - 1) = ((k - 1 : ℕ) : ℤ) := by omega
  rw [e, zpow_natCast, mul_comm p N] at hs
  rw [hs, Nat.cast_mul, map_mul, map_mul, map_pow, map_natCast (algebraMap ℚ R)]
  ring
private theorem level_zero {R : Type} [CommRing R] {N p : ℕ} (χ : DirichletCharacter R N)
    (hp : p.Prime) (hpN : p ∣ N) : χ (p : ZMod N) = 0 := by
  apply MulChar.map_nonunit
  rw [ZMod.isUnit_iff_coprime]
  intro hc
  exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc hpN)
private theorem level_val {R : Type} [CommRing R] {N M p : ℕ} (h : N ∣ M)
    (χ : DirichletCharacter R N) (hp : p.Prime) (hpM : ¬ p ∣ M) :
    DirichletCharacter.changeLevel h χ (p : ZMod M) = χ (p : ZMod N) := by
  have hc : p.Coprime M := (Nat.Prime.coprime_iff_not_dvd hp).2 hpM
  have := DirichletCharacter.changeLevel_eq_cast_of_dvd χ h (ZMod.unitOfCoprime p hc)
  rw [ZMod.coe_unitOfCoprime, ZMod.cast_natCast h] at this
  exact this
private theorem generalized_bernoulli_change_level {R : Type} [CommRing R] [Algebra ℚ R] {N : ℕ}
    (k : ℕ) (χ : DirichletCharacter R N) (hN : 0 < N) (hk : 1 ≤ k) (m : ℕ) :
    0 < m → ∀ (M : ℕ) (h : N ∣ M), M = N * m →
      genB k (DirichletCharacter.changeLevel h χ : ZMod M → R) =
        genB k χ * ∏ p ∈ M.primeFactors, (1 - χ (p : ZMod N) * (p : R) ^ (k - 1)) := by
  induction m using induction_on_primes with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | one =>
    intro _ M h hM
    rw [mul_one] at hM; subst hM
    rw [DirichletCharacter.changeLevel_self, Finset.prod_eq_one, mul_one]
    intro p hp
    rw [level_zero χ (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp), zero_mul, sub_zero]
  | prime_mul p a hp ih =>
    intro hpa M h hM
    have ha : 0 < a := Nat.pos_of_mul_pos_left hpa
    have hM' : M = N * a * p := by rw [hM]; ring
    subst hM'
    have hNa : 0 < N * a := Nat.mul_pos hN ha
    have ih' := ih ha (N * a) (dvd_mul_right N a) rfl
    have hs := b_step k (DirichletCharacter.changeLevel (dvd_mul_right N a) χ) hNa hp hk
    rw [← DirichletCharacter.changeLevel_trans] at hs
    rw [hs, ih', Nat.primeFactors_mul hNa.ne' hp.ne_zero, hp.primeFactors]
    by_cases hd : p ∣ N * a
    · rw [level_zero _ hp hd, Finset.union_eq_left.2 (by simpa using ⟨hp, hd, hN.ne', ha.ne'⟩)]; ring
    · rw [level_val _ χ hp hd, Finset.prod_union (by
        rw [Finset.disjoint_singleton_right]
        exact fun hh => hd (Nat.dvd_of_mem_primeFactors hh)), Finset.prod_singleton]
      ring
theorem b_level :
    ∀ {R : Type} [CommRing R] [Algebra ℚ R] {N M : ℕ} (h : N ∣ M) (k : ℕ)
      (χ : DirichletCharacter R N), 0 < M → 1 ≤ k →
      genB k (DirichletCharacter.changeLevel h χ : ZMod M → R) =
        genB k χ * ∏ p ∈ M.primeFactors, (1 - χ (p : ZMod N) * (p : R) ^ (k - 1)) := by
  intro R _ _ N M h k χ hM hk
  obtain ⟨m, hm⟩ := id h
  have hpos : 0 < N * m := hm ▸ hM
  exact generalized_bernoulli_change_level k χ (Nat.pos_of_mul_pos_right hpos) hk m
    (Nat.pos_of_mul_pos_left hpos) M h hm
theorem b_primlevel :
    ∀ {R : Type} [CommRing R] [Algebra ℚ R] {N : ℕ} (k : ℕ) (χ : DirichletCharacter R N),
      0 < N → 1 ≤ k →
      genB k χ = Bprim k χ * ∏ p ∈ N.primeFactors, (1 - primVal χ p * (p : R) ^ (k - 1)) := by
  intro R _ _ N k χ hN hk
  have h := b_level χ.conductor_dvd_level k χ.primitiveCharacter hN hk
  rw [DirichletCharacter.changeLevel_primitiveCharacter] at h
  rw [h]; rfl
theorem b_primval :
    ∀ {R : Type} [CommRing R] {N : ℕ} [NeZero N] (χ : DirichletCharacter R N)
      (x : ZMod χ.conductor), χ.primitiveCharacter x = 0 ∨ ∃ u : (ZMod N)ˣ, χ.primitiveCharacter x = χ u := by
  intro R _ N _ χ x
  by_cases hx : IsUnit x
  · right
    obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective χ.conductor_dvd_level hx.unit
    refine ⟨u, ?_⟩
    conv_rhs => rw [← χ.changeLevel_primitiveCharacter]
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, ← ZMod.unitsMap_val, hu]
    · simp
    · exact χ.conductor_dvd_level
  · left; exact MulChar.map_nonunit _ hx
private theorem key_primeq {R : Type} [CommRing R] [Algebra ℚ R] {M c c' : ℕ} [NeZero M] (k : ℕ)
    (ψ : DirichletCharacter R c) (ψ' : DirichletCharacter R c') (e : c = c') (h : c ∣ M) (h' : c' ∣ M)
    (hψ : DirichletCharacter.changeLevel h ψ = DirichletCharacter.changeLevel h' ψ') :
    genB k (ψ : ZMod c → R) = genB k (ψ' : ZMod c' → R) ∧ ∀ a : ℕ, ψ (a : ZMod c) = ψ' (a : ZMod c') := by
  subst e
  have hψψ : ψ = ψ' := DirichletCharacter.changeLevel_injective h hψ
  subst hψψ
  exact ⟨rfl, fun _ => rfl⟩
theorem b_primeq :
    ∀ {R : Type} [CommRing R] [Algebra ℚ R] {N : ℕ} [NeZero N] (k : ℕ)
      (χ : DirichletCharacter R N),
      (χ.IsPrimitive → Bprim k χ = genB k χ ∧ ∀ a : ℕ, primVal χ a = χ (a : ZMod N)) ∧
      ∀ (M : ℕ) [NeZero M] (h : N ∣ M),
        Bprim k (DirichletCharacter.changeLevel h χ) = Bprim k χ ∧
        ∀ a : ℕ, primVal (DirichletCharacter.changeLevel h χ) a = primVal χ a := by
  intro R _ _ N _ k χ
  refine ⟨fun hp => ?_, fun M _ h => ?_⟩
  · exact key_primeq k χ.primitiveCharacter χ hp χ.conductor_dvd_level (dvd_refl N)
      (by rw [DirichletCharacter.changeLevel_primitiveCharacter, DirichletCharacter.changeLevel_self])
  · refine key_primeq k (DirichletCharacter.changeLevel h χ).primitiveCharacter χ.primitiveCharacter
      (DirichletCharacter.conductor_changeLevel χ h) (DirichletCharacter.conductor_dvd_level _)
      (χ.conductor_dvd_level.trans h) ?_
    rw [DirichletCharacter.changeLevel_primitiveCharacter,
      DirichletCharacter.changeLevel_trans _ χ.conductor_dvd_level h,
      DirichletCharacter.changeLevel_primitiveCharacter]
private theorem change_level_value_eq {R S : Type} [CommRing R] [CommRing S] {N : ℕ} [NeZero N]
    (f : R →+* S) {d e : ℕ} (hde : e = d) (hd : d ∣ N) (he : e ∣ N)
    (φ : DirichletCharacter R d) (ψ : DirichletCharacter S e)
    (h : DirichletCharacter.changeLevel he ψ = (DirichletCharacter.changeLevel hd φ).ringHomComp f)
    (a : ℕ) : ψ (a : ZMod e) = f (φ (a : ZMod d)) := by
  subst hde
  have hc : (DirichletCharacter.changeLevel hd φ).ringHomComp f =
      DirichletCharacter.changeLevel hd (φ.ringHomComp f) := by
    ext u; simp [MulChar.ringHomComp_apply, DirichletCharacter.changeLevel_eq_cast_of_dvd]
  have hψ : ψ = φ.ringHomComp f := DirichletCharacter.changeLevel_injective hd (h.trans hc)
  subst hψ
  simp [MulChar.ringHomComp_apply]
theorem b_condmap :
    ∀ {R S : Type} [CommRing R] [CommRing S] {N : ℕ} [NeZero N] (f : R →+* S),
      Function.Injective f → ∀ χ : DirichletCharacter R N,
      DirichletCharacter.conductor (χ.ringHomComp f) = χ.conductor ∧
      (∀ a : ℕ, primVal (χ.ringHomComp f) a = f (primVal χ a)) ∧
      (χ.ringHomComp f).toUnitHom.ker = χ.toUnitHom.ker := by
  intro R S _ _ N _ f hf χ
  have hker : (χ.ringHomComp f).toUnitHom.ker = χ.toUnitHom.ker := by
    ext u
    simp only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one,
      MulChar.ringHomComp_apply]
    exact ⟨fun h => hf (h.trans (map_one f).symm), fun h => by rw [h, map_one]⟩
  have hset : DirichletCharacter.conductorSet (χ.ringHomComp f) = χ.conductorSet := by
    ext d
    simp only [DirichletCharacter.mem_conductorSet_iff]
    constructor
    · intro h
      have h' := (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mp h
      rw [hker] at h'
      exact (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mpr h'
    · intro h
      have h' := (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mp h
      rw [← hker] at h'
      exact (DirichletCharacter.factorsThrough_iff_ker_unitsMap h.dvd).mpr h'
  have hcond : DirichletCharacter.conductor (χ.ringHomComp f) = χ.conductor := by
    unfold DirichletCharacter.conductor; rw [hset]
  refine ⟨hcond, fun a => ?_, hker⟩
  unfold primVal
  exact change_level_value_eq f hcond χ.conductor_dvd_level
    (DirichletCharacter.conductor_dvd_level (χ.ringHomComp f))
    χ.primitiveCharacter (DirichletCharacter.primitiveCharacter (χ.ringHomComp f))
    (by rw [DirichletCharacter.changeLevel_primitiveCharacter,
      DirichletCharacter.changeLevel_primitiveCharacter]) a
theorem b_primmap :
    ∀ {R S : Type} [CommRing R] [Algebra ℚ R] [CommRing S] [Algebra ℚ S] {N : ℕ} [NeZero N]
      (f : R →+* S), Function.Injective f → ∀ (k : ℕ) (χ : DirichletCharacter R N),
      f (Bprim k χ) = Bprim k (χ.ringHomComp f) := by
  intro R S _ _ _ _ N _ f hf k χ
  obtain ⟨hcond, hval, -⟩ := b_condmap f hf χ
  rw [Bprim_eq, Bprim_eq, hcond, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, hval a, RingHom.map_rat_algebraMap]
theorem b_charbij :
    ∀ {N : ℕ} [NeZero N] {K Ω : Type} [Field K] [Field Ω]
      [HasEnoughRootsOfUnity K (Monoid.exponent (ZMod N)ˣ)] (f : K →+* Ω)
      (P : Set (Subgroup (ZMod N)ˣ)),
      Set.BijOn (fun χ : DirichletCharacter K N => (χ.ringHomComp f : DirichletCharacter Ω N))
        (charSet K P) (charSet Ω P) := by
  intro N _ K Ω _ _ _ f P
  have hf : Function.Injective f := f.injective
  have hker : ∀ χ : DirichletCharacter K N,
      (MulChar.toUnitHom (χ.ringHomComp f)).ker = (MulChar.toUnitHom χ).ker := by
    intro χ; ext u
    simp only [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one,
      MulChar.ringHomComp_apply]
    exact ⟨fun h => hf (h.trans (map_one f).symm), fun h => by rw [h, map_one]⟩
  refine ⟨?_, ?_, ?_⟩
  · intro χ hχ
    simp only [charSet, Set.mem_ofPred_eq] at hχ ⊢
    rwa [hker]
  · intro χ₁ _ χ₂ _ h
    ext u
    have h' := congrArg (fun ψ : DirichletCharacter Ω N => ψ u) h
    simp only [MulChar.ringHomComp_apply] at h'
    exact hf h'
  · intro χ' hχ'
    have he : NeZero (Monoid.exponent (ZMod N)ˣ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K (Monoid.exponent (ZMod N)ˣ)
    have hne : (primitiveRoots (Monoid.exponent (ZMod N)ˣ) K).Nonempty :=
      ⟨ζ, (mem_primitiveRoots (NeZero.pos _)).mpr hζ⟩
    have hmem : ∀ u, MulChar.toUnitHom χ' u ∈ rootsOfUnity (Monoid.exponent (ZMod N)ˣ) Ω := by
      intro u; rw [mem_rootsOfUnity, ← map_pow, Monoid.pow_exponent_eq_one, map_one]
    let ψ : (ZMod N)ˣ →* Kˣ := (rootsOfUnity (Monoid.exponent (ZMod N)ˣ) K).subtype.comp
      ((rootsOfUnityEquivOfPrimitiveRoots hf hne).symm.toMonoidHom.comp
        ((MulChar.toUnitHom χ').codRestrict _ hmem))
    have hcomp : (MulChar.ofUnitHom ψ).ringHomComp f = χ' := by
      ext u
      rw [MulChar.ringHomComp_apply, MulChar.ofUnitHom_coe]
      show f (((rootsOfUnityEquivOfPrimitiveRoots hf hne).symm
        ⟨MulChar.toUnitHom χ' u, hmem u⟩ : Kˣ) : K) = χ' u
      rw [rootsOfUnityEquivOfPrimitiveRoots_symm_apply]
      simp
    refine ⟨MulChar.ofUnitHom ψ, ?_, hcomp⟩
    simp only [charSet, Set.mem_ofPred_eq] at hχ' ⊢
    rw [← hker, hcomp]; exact hχ'
theorem b_parity :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] {N : ℕ} [NeZero N] (k : ℕ) (χ : DirichletCharacter Ω N),
      (χ.toUnitHom.ker ∈ parKer N k ↔ χ (-1) = (-1) ^ k) ∧ χ.primitiveCharacter (-1) = χ (-1) := by
  intro Ω _ _ N _ k χ
  have hne : (-1 : Ω) ≠ 1 := by norm_num
  refine ⟨?_, ?_⟩
  · have hval : χ.toUnitHom (-1) = 1 ↔ χ (-1) = 1 := by
      rw [← Units.val_inj, MulChar.coe_toUnitHom, Units.val_neg, Units.val_one, Units.val_one]
    show ((-1 : (ZMod N)ˣ) ∈ χ.toUnitHom.ker ↔ Even k) ↔ _
    rw [MonoidHom.mem_ker, hval]
    rcases Nat.even_or_odd k with hk | hk
    · rw [hk.neg_one_pow]; simp [hk]
    · rw [hk.neg_one_pow]
      have hk' : ¬ Even k := Nat.not_even_iff_odd.mpr hk
      rcases χ.even_or_odd with h | h
      · have h1 : χ (-1) = 1 := h; simp [hk', h1, hne.symm]
      · have h1 : χ (-1) = -1 := h; simp [hk', h1, hne]
  · have hd := DirichletCharacter.conductor_dvd_level χ
    have h := DirichletCharacter.changeLevel_eq_cast_of_dvd χ.primitiveCharacter hd (-1)
    rw [DirichletCharacter.changeLevel_primitiveCharacter, Units.val_neg, Units.val_one,
      ZMod.cast_neg hd, ZMod.cast_one hd] at h
    exact h.symm
theorem b_primden :
    ∀ (k j : ℕ), j ≤ k → ∃ z : ℤ, (primorial (k + 1) : ℚ) * bernoulli j = z := by
  intro k j hjk
  have hdvd : ∀ p : ℕ, p.Prime → p ≤ k + 1 → p ∣ primorial (k + 1) := fun p hp hpk =>
    Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hp⟩)
  rcases Nat.even_or_odd j with ⟨m, rfl⟩ | hodd
  · obtain ⟨z0, hz0⟩ := Bernoulli.vonStaudt_clausen m
    have h2 : m + m = 2 * m := by ring
    rw [h2]
    have hB : bernoulli (2 * m) =
        (z0 : ℚ) - ∑ p ∈ range (2 * m + 2) with Nat.Prime p ∧ p - 1 ∣ 2 * m, (1 : ℚ) / p := by
      rw [hz0]; ring
    refine ⟨(primorial (k + 1) : ℤ) * z0 -
        ∑ p ∈ range (2 * m + 2) with Nat.Prime p ∧ p - 1 ∣ 2 * m, ((primorial (k + 1) / p : ℕ) : ℤ), ?_⟩
    rw [Int.cast_sub, Int.cast_mul, Int.cast_sum]
    simp only [Int.cast_natCast]
    rw [hB, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_filter, Finset.mem_range] at hp
    have hpd : p ∣ primorial (k + 1) := hdvd p hp.2.1 (by omega)
    rw [Nat.cast_div hpd (Nat.cast_ne_zero.2 hp.2.1.ne_zero)]
    ring
  · rcases Nat.lt_or_ge 1 j with h1 | h1
    · exact ⟨0, by rw [bernoulli_eq_zero_of_odd hodd h1]; simp⟩
    · have hj : j = 1 := by obtain ⟨r, rfl⟩ := hodd; omega
      subst hj
      obtain ⟨t, ht⟩ := hdvd 2 Nat.prime_two (by omega)
      refine ⟨-(t : ℤ), ?_⟩
      rw [bernoulli_one, ht]; push_cast; ring
theorem b_denint :
    ∀ (N k a : ℕ), 0 < N → ∃ z : ℤ, (den N k : ℚ) * bcoef N k a = z := by
  intro N k a hN
  suffices h : (den N k : ℚ) * bcoef N k a ∈ (Int.castRingHom ℚ).range by
    obtain ⟨z, hz⟩ := h; exact ⟨z, hz.symm⟩
  rw [b_expand N k a hN, Finset.mul_sum]
  refine Subring.sum_mem _ fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  obtain ⟨z, hz⟩ := b_primden k j hjk
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpow : (N : ℚ) * (N : ℚ) ^ ((j : ℤ) - 1) = (N : ℚ) ^ j := by
    rw [← zpow_one_add₀ hN', add_sub_cancel, zpow_natCast]
  refine ⟨(k.choose j : ℤ) * z * (N : ℤ) ^ j * (a : ℤ) ^ (k - j), ?_⟩
  unfold den; rw [eq_intCast]; push_cast; rw [← hz, ← hpow]; ring
theorem b_denchar :
    ∀ {R : Type} [CommRing R] [Algebra ℚ R] {N : ℕ} (k : ℕ) (Φ : ZMod N → R) (A : Subring R),
      0 < N → (∀ a, Φ a ∈ A) → (den N k : R) * genB k Φ ∈ A := by
  intro R _ _ N k Φ A hN hΦ
  unfold genB
  rw [Finset.mul_sum]
  refine A.sum_mem fun a _ => ?_
  obtain ⟨z, hz⟩ := b_denint N k a hN
  have h : (den N k : R) * algebraMap ℚ R (bcoef N k a) = (z : R) := by
    rw [← map_natCast (algebraMap ℚ R), ← map_mul, hz, map_intCast]
  rw [mul_left_comm, h]
  exact A.mul_mem (hΦ _) (intCast_mem A z)
private theorem dirichletCharacter_unit_isIntegral {R : Type} [CommRing R] {N : ℕ} [NeZero N]
    (χ : DirichletCharacter R N) (u : (ZMod N)ˣ) : IsIntegral ℤ (χ u) := by
  refine IsIntegral.of_pow (orderOf_pos u) ?_
  have h1 : χ (u : ZMod N) ^ orderOf u = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one, map_one]
  rw [h1]; exact isIntegral_one
theorem b_primmem :
    ∀ {R : Type} [CommRing R] [Algebra ℚ R] {N : ℕ} [NeZero N] (k : ℕ) (χ : DirichletCharacter R N),
      (∀ A : Subalgebra ℚ R, (∀ u : (ZMod N)ˣ, χ u ∈ A) → Bprim k χ ∈ A) ∧
      (∀ A : Subring R, (∀ u : (ZMod N)ˣ, χ u ∈ A) → (den N k : R) * Bprim k χ ∈ A) ∧
      IsIntegral ℤ ((den N k : R) * Bprim k χ) ∧ IsIntegral ℤ ((den N k : R) * genB k χ) := by
  intro R _ _ N _ k χ
  have hN : N ≠ 0 := NeZero.ne N
  have hc : 0 < χ.conductor :=
    Nat.pos_of_ne_zero fun h => hN (Nat.eq_zero_of_zero_dvd (h ▸ χ.conductor_dvd_level))
  have hdvd : den χ.conductor k ∣ den N k := den_dvd χ.conductor_dvd_level k
  have hB : Bprim k χ = genB k (⇑χ.primitiveCharacter) := rfl
  have hint : ∀ a : ZMod N, IsIntegral ℤ (χ a) := by
    intro a
    by_cases ha : IsUnit a
    · obtain ⟨u, rfl⟩ := ha; exact dirichletCharacter_unit_isIntegral χ u
    · rw [MulChar.map_nonunit χ ha]; exact isIntegral_zero
  have part2 : ∀ A : Subring R, (∀ u : (ZMod N)ˣ, χ u ∈ A) → (den N k : R) * Bprim k χ ∈ A := by
    intro A hA
    obtain ⟨m, hm⟩ := hdvd
    have hmem : (den χ.conductor k : R) * genB k (⇑χ.primitiveCharacter) ∈ A := by
      refine b_denchar k _ A hc fun x => ?_
      rcases b_primval χ x with h | ⟨u, h⟩
      · rw [h]; exact A.zero_mem
      · rw [h]; exact hA u
    rw [hB, hm, Nat.cast_mul, mul_comm ((den χ.conductor k : ℕ) : R) (m : R), mul_assoc]
    exact A.mul_mem (natCast_mem A m) hmem
  refine ⟨?_, part2, ?_, ?_⟩
  · intro A hA
    rw [hB]
    refine genB_mem k _ A fun x => ?_
    rcases b_primval χ x with h | ⟨u, h⟩
    · rw [h]; exact A.zero_mem
    · rw [h]; exact hA u
  · exact part2 (integralClosure ℤ R).toSubring fun u => dirichletCharacter_unit_isIntegral χ u
  · exact b_denchar k (⇑χ) (integralClosure ℤ R).toSubring (Nat.pos_of_ne_zero hN) hint
private theorem polybound_cast (k : ℕ) (x : ℚ) :
    (((Polynomial.bernoulli k).eval x : ℚ) : ℝ) = bernoulliFun k (x : ℝ) := by
  rw [bernoulliFun, Polynomial.eval_map_algebraMap, ← eq_ratCast (algebraMap ℚ ℝ) x,
    Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, eq_ratCast]
private theorem polybound_big {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (2 * Real.pi) ^ k / (k.factorial : ℝ) * |bernoulliFun k x| ≤ 4 := by
  have hs := hasSum_one_div_nat_pow_mul_fourier hk hx
  have hnorm_f : ∀ (n : ℤ) (y : UnitAddCircle), ‖fourier n y‖ = 1 := fun n y => by
    rw [fourier_apply]; exact Circle.norm_coe _
  have h2 : ∀ (m : ℤ) (y : UnitAddCircle), ‖fourier m y + (-1) ^ k * fourier (-m) y‖ ≤ 2 := by
    intro m y
    calc _ ≤ ‖fourier m y‖ + ‖(-1 : ℂ) ^ k * fourier (-m) y‖ := norm_add_le _ _
      _ = 2 := by
        rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, hnorm_f, hnorm_f]
        norm_num
  have hbound : ‖-(2 * (Real.pi : ℂ) * Complex.I) ^ k / (k.factorial : ℂ) * (bernoulliFun k x : ℂ)‖ ≤
      2 * (Real.pi ^ 2 / 6) := by
    rw [← hs.tsum_eq]
    refine tsum_of_norm_bounded (hasSum_zeta_two.mul_left 2) fun n ↦ ?_
    rw [norm_mul]
    have h1 : ‖1 / (n : ℂ) ^ k‖ ≤ 1 / (n : ℝ) ^ 2 := by
      rw [norm_div, norm_one, norm_pow, Complex.norm_natCast]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [zero_pow (by omega : k ≠ 0)]
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hn1 hk)
    calc _ ≤ 1 / (n : ℝ) ^ 2 * 2 := mul_le_mul h1 (h2 _ _) (norm_nonneg _) (by positivity)
      _ = 2 * (1 / (n : ℝ) ^ 2) := mul_comm _ _
  have hnorm : ‖-(2 * (Real.pi : ℂ) * Complex.I) ^ k / (k.factorial : ℂ) * (bernoulliFun k x : ℂ)‖ =
      (2 * Real.pi) ^ k / (k.factorial : ℝ) * |bernoulliFun k x| := by
    rw [norm_mul, norm_div, norm_neg, norm_pow, norm_mul, norm_mul, Complex.norm_I,
      Complex.norm_real, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one, Complex.norm_two]
  rw [← hnorm]
  exact hbound.trans (by nlinarith [Real.pi_pos, Real.pi_lt_d2])
theorem b_polybound :
    ∀ (k : ℕ) (x : ℚ), 0 ≤ x → x ≤ 1 →
      |(((Polynomial.bernoulli k).eval x : ℚ) : ℝ)| ≤ 4 * (k.factorial : ℝ) / (2 * Real.pi) ^ k := by
  intro k x h0 h1
  have hx0 : (0 : ℝ) ≤ x := by exact_mod_cast h0
  have hx1 : (x : ℝ) ≤ 1 := by exact_mod_cast h1
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  rcases lt_or_ge k 2 with hk | hk
  · interval_cases k
    · simp [Polynomial.bernoulli_zero]
    · simp only [Polynomial.bernoulli_one, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, Rat.cast_sub, Nat.factorial_one, Nat.cast_one, pow_one]
      have key : |(x : ℝ) - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      have : (1 : ℝ) / 2 ≤ 4 * 1 / (2 * Real.pi) := by rw [le_div_iff₀ hpi]; nlinarith [Real.pi_lt_d2]
      linarith
  · have hb := polybound_big hk (x := (x : ℝ)) ⟨hx0, hx1⟩
    rw [polybound_cast]
    have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    rw [div_mul_eq_mul_div, div_le_iff₀ hf] at hb
    rw [le_div_iff₀ (pow_pos hpi k)]
    linarith [mul_comm (|bernoulliFun k x|) ((2 * Real.pi) ^ k)]
theorem b_upper :
    ∀ {N : ℕ} (k : ℕ) (Φ : ZMod N → ℂ), 0 < N → (∀ a, ‖Φ a‖ ≤ 1) →
      ‖genB k Φ‖ ≤ 4 * (N : ℝ) ^ k * (k.factorial : ℝ) / (2 * Real.pi) ^ k := by
  intro N k Φ hN hΦ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set C : ℝ := 4 * (k.factorial : ℝ) / (2 * Real.pi) ^ k with hC
  have hterm : ∀ a ∈ Icc 1 N,
      ‖Φ (a : ZMod N) * algebraMap ℚ ℂ (bcoef N k a)‖ ≤ (N : ℝ) ^ ((k : ℤ) - 1) * C := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    have hx0 : (0 : ℚ) ≤ (a : ℚ) / N := by positivity
    have hx1 : (a : ℚ) / N ≤ 1 := by rw [div_le_one (by exact_mod_cast hN)]; exact_mod_cast ha.2
    have hb : ‖algebraMap ℚ ℂ (bcoef N k a)‖ =
        (N : ℝ) ^ ((k : ℤ) - 1) * |((Polynomial.eval ((a : ℚ) / N) (Polynomial.bernoulli k) : ℚ) : ℝ)| := by
      rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs, bcoef]
      push_cast; rw [abs_mul, abs_of_pos (zpow_pos hNr _)]
    rw [norm_mul, hb]
    have hp := b_polybound k ((a : ℚ) / N) hx0 hx1
    calc ‖Φ (a : ZMod N)‖ * ((N : ℝ) ^ ((k : ℤ) - 1) *
          |((Polynomial.eval ((a : ℚ) / N) (Polynomial.bernoulli k) : ℚ) : ℝ)|)
        ≤ 1 * ((N : ℝ) ^ ((k : ℤ) - 1) * C) :=
          mul_le_mul (hΦ _) (mul_le_mul_of_nonneg_left hp (zpow_pos hNr _).le) (by positivity) zero_le_one
      _ = (N : ℝ) ^ ((k : ℤ) - 1) * C := one_mul _
  calc ‖genB k Φ‖ ≤ ∑ a ∈ Icc 1 N, ‖Φ (a : ZMod N) * algebraMap ℚ ℂ (bcoef N k a)‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ Icc 1 N, (N : ℝ) ^ ((k : ℤ) - 1) * C := Finset.sum_le_sum hterm
    _ = 4 * (N : ℝ) ^ k * (k.factorial : ℝ) / (2 * Real.pi) ^ k := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul,
          zpow_sub_one₀ hNr.ne', zpow_natCast, hC]
        field_simp
private theorem bernoulli_denominator_bound {N M : ℕ} (k : ℕ) (Φ : ZMod M → ℂ) (hM : 0 < M)
    (hMN : M ≤ N) (hΦ : ∀ a, ‖Φ a‖ ≤ 1) : ‖(den N k : ℂ) * genB k Φ‖ ≤ bnd N k := by
  have hb := b_upper k Φ hM hΦ
  have hp : (primorial (k + 1) : ℝ) ≤ 4 ^ (k + 1) := by exact_mod_cast primorial_le_four_pow (k + 1)
  have h4 : (4 : ℝ) ^ k ≤ (2 * Real.pi) ^ k :=
    pow_le_pow_left₀ (by norm_num) (by linarith [Real.pi_gt_three]) k
  have hpi : 0 < (2 * Real.pi) ^ k := by positivity
  have hMN' : (M : ℝ) ≤ N := by exact_mod_cast hMN
  rw [norm_mul, Complex.norm_natCast, den, bnd]
  push_cast
  calc (N : ℝ) * (primorial (k + 1) : ℝ) * ‖genB k Φ‖
      ≤ N * 4 ^ (k + 1) * (4 * (N : ℝ) ^ k * k.factorial / (2 * Real.pi) ^ k) := by
        gcongr; exact hb.trans (by gcongr)
    _ = 16 * (N : ℝ) ^ (k + 1) * k.factorial * (4 ^ k / (2 * Real.pi) ^ k) := by ring
    _ ≤ 16 * (N : ℝ) ^ (k + 1) * k.factorial * 1 := by
        gcongr; rwa [div_le_one hpi]
    _ = _ := mul_one _
theorem b_denupper :
    ∀ {N : ℕ} [NeZero N] (k : ℕ) (χ : DirichletCharacter ℂ N),
      ‖(den N k : ℂ) * genB k χ‖ ≤ bnd N k ∧ ‖(den N k : ℂ) * Bprim k χ‖ ≤ bnd N k ∧ 1 ≤ bnd N k := by
  intro N _ k χ
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  refine ⟨bernoulli_denominator_bound k _ hN le_rfl (fun a => χ.norm_le_one a),
    bernoulli_denominator_bound k _ (Nat.pos_of_ne_zero χ.conductor_ne_zero)
      (Nat.le_of_dvd hN χ.conductor_dvd_level) (fun a => χ.primitiveCharacter.norm_le_one a), ?_⟩
  have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (k + 1) := one_le_pow₀ (by exact_mod_cast hN)
  have h2 : (1 : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast k.factorial_pos
  unfold bnd
  nlinarith [mul_le_mul h1 h2 zero_le_one (zero_le_one.trans h1)]
theorem b_ratprod :
    ∀ {N : ℕ} [NeZero N] (P : Set (Subgroup (ZMod N)ˣ))
      (F : ∀ (Ω : Type) [Field Ω] [CharZero Ω], DirichletCharacter Ω N → Ω),
      (∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [CharZero Ω] (f : K →+* Ω)
        (χ : DirichletCharacter K N), f (F K χ) = F Ω (χ.ringHomComp f)) →
      ∃ q : ℚ, ∀ (Ω : Type) [Field Ω] [CharZero Ω]
        [HasEnoughRootsOfUnity Ω (Monoid.exponent (ZMod N)ˣ)],
        ∏ᶠ χ ∈ charSet Ω P, F Ω χ = (q : Ω) := by
  intro N _ P F hF
  set e := Monoid.exponent (ZMod N)ˣ
  have he : NeZero e := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have : NeZero (e : ℚ) := ⟨by exact_mod_cast he.out⟩
  have : IsCyclotomicExtension {e} ℚ (CyclotomicField e ℚ) :=
    CyclotomicField.isCyclotomicExtension e ℚ
  have : IsGalois ℚ (CyclotomicField e ℚ) := IsCyclotomicExtension.isGalois {e} ℚ _
  have : FiniteDimensional ℚ (CyclotomicField e ℚ) :=
    IsCyclotomicExtension.finiteDimensional {e} ℚ _
  have hζ := IsCyclotomicExtension.zeta_spec e ℚ (CyclotomicField e ℚ)
  have : HasEnoughRootsOfUnity (CyclotomicField e ℚ) e :=
    ⟨⟨_, hζ⟩, rootsOfUnity.isCyclic (CyclotomicField e ℚ) e⟩
  have hfin : ∀ (Ω : Type) [Field Ω], (charSet Ω P).Finite := fun _ _ => Set.toFinite _
  have hfix : ∀ σ : CyclotomicField e ℚ ≃ₐ[ℚ] CyclotomicField e ℚ,
      σ (∏ᶠ χ ∈ charSet (CyclotomicField e ℚ) P, F (CyclotomicField e ℚ) χ) =
        ∏ᶠ χ ∈ charSet (CyclotomicField e ℚ) P, F (CyclotomicField e ℚ) χ := by
    intro σ
    have h1 := (σ.toRingHom.toMonoidHom).map_finprod_mem
      (fun χ => F (CyclotomicField e ℚ) χ) (hfin (CyclotomicField e ℚ))
    refine h1.trans ?_
    exact finprod_mem_eq_of_bijOn _ (b_charbij σ.toRingHom P) (fun χ _ => hF _ _ σ.toRingHom χ)
  have hbot := (IsGalois.mem_bot_iff_fixed _).2 hfix
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.1 hbot
  refine ⟨q, fun Ω _ _ _ => ?_⟩
  obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω e
  have hmin : Polynomial.aeval ω (minpoly ℚ (hζ.powerBasis ℚ).gen) = 0 := by
    rw [IsPrimitiveRoot.powerBasis_gen, ← hζ.minpoly_eq_cyclotomic_of_irreducible
      (Polynomial.cyclotomic.irreducible_rat (NeZero.pos e)), Polynomial.aeval_def,
      Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hω.isRoot_cyclotomic (NeZero.pos e)
  let g := (hζ.powerBasis ℚ).lift ω hmin
  calc ∏ᶠ χ ∈ charSet Ω P, F Ω χ
      = ∏ᶠ χ ∈ charSet (CyclotomicField e ℚ) P, g.toRingHom (F (CyclotomicField e ℚ) χ) :=
        (finprod_mem_eq_of_bijOn _ (b_charbij g.toRingHom P) (fun χ _ => hF _ _ g.toRingHom χ)).symm
    _ = g.toRingHom (∏ᶠ χ ∈ charSet (CyclotomicField e ℚ) P, F (CyclotomicField e ℚ) χ) :=
        (g.toRingHom.toMonoidHom.map_finprod_mem _ (hfin _)).symm
    _ = (q : Ω) := by rw [← hq]; exact (g.commutes q).trans (eq_ratCast _ q)
private lemma hd_cpow (c : ℂ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => (x : ℂ) ^ c) (c * (t : ℂ) ^ (c - 1)) t :=
  (Complex.hasStrictDerivAt_cpow_const (c := c) (Complex.ofReal_mem_slitPlane.2 ht)).hasDerivAt.comp_ofReal
private lemma lip (s : ℂ) (a x y : ℝ) (ha : 0 < a) (hx : a ≤ x) (hy : a ≤ y) (hs : -2 ≤ s.re) :
    ‖(y : ℂ) ^ (-s - 1) - (x : ℂ) ^ (-s - 1)‖ ≤ ‖s + 1‖ * a ^ (-s.re - 2) * ‖y - x‖ := by
  have hge : ∀ z ∈ Set.uIcc x y, a ≤ z := fun z hz =>
    (Set.mem_uIcc.1 hz).elim (fun h => le_trans hx h.1) (fun h => le_trans hy h.1)
  have hder : ∀ z ∈ Set.uIcc x y, HasDerivWithinAt (fun w : ℝ => (w : ℂ) ^ (-s - 1))
      ((-s - 1) * (z : ℂ) ^ (-s - 1 - 1)) (Set.uIcc x y) z := fun z hz =>
    (hd_cpow (-s - 1) z (lt_of_lt_of_le ha (hge z hz))).hasDerivWithinAt
  have hbd : ∀ z ∈ Set.uIcc x y, ‖(-s - 1) * (z : ℂ) ^ (-s - 1 - 1)‖ ≤ ‖s + 1‖ * a ^ (-s.re - 2) := by
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le ha (hge z hz)
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hz0,
      show ‖-s - 1‖ = ‖s + 1‖ from by rw [show -s - 1 = -(s + 1) by ring, norm_neg],
      show (-s - 1 - 1).re = -s.re - 2 from by simp; ring]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ha (hge z hz) (by linarith)) (norm_nonneg _)
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd (convex_uIcc x y)
    Set.left_mem_uIcc Set.right_mem_uIcc
theorem b_taylor2 :
    ∀ (s : ℂ) (a u v : ℝ), 0 < a → a ≤ u → a ≤ v → -2 ≤ s.re →
      ‖(v : ℂ) ^ (-s) - (u : ℂ) ^ (-s) + s * ((v : ℂ) - u) * (u : ℂ) ^ (-s - 1)‖ ≤
        ‖s‖ * ‖s + 1‖ * a ^ (-s.re - 2) * (v - u) ^ 2 := by
  intro s a u v ha hu hv hs
  have hge : ∀ z ∈ Set.uIcc u v, a ≤ z := fun z hz =>
    (Set.mem_uIcc.1 hz).elim (fun h => le_trans hu h.1) (fun h => le_trans hv h.1)
  set g : ℝ → ℂ := fun x => (x : ℂ) ^ (-s) - (u : ℂ) ^ (-s) + s * ((x : ℂ) - u) * (u : ℂ) ^ (-s - 1)
  have hder : ∀ z ∈ Set.uIcc u v, HasDerivWithinAt g
      (-s * (z : ℂ) ^ (-s - 1) + s * (u : ℂ) ^ (-s - 1)) (Set.uIcc u v) z := by
    intro z hz
    have hz0 : 0 < z := lt_of_lt_of_le ha (hge z hz)
    have h1 := hd_cpow (-s) z hz0
    have h2 : HasDerivAt (fun x : ℝ => s * ((x : ℂ) - u) * (u : ℂ) ^ (-s - 1))
        (s * 1 * (u : ℂ) ^ (-s - 1)) z :=
      (((hasDerivAt_id z).ofReal_comp.sub_const (u : ℂ)).const_mul s).mul_const _
    have hd : HasDerivWithinAt (fun x : ℝ => ((x : ℂ) ^ (-s) - (u : ℂ) ^ (-s)) +
        s * ((x : ℂ) - u) * (u : ℂ) ^ (-s - 1))
        (-s * (z : ℂ) ^ (-s - 1) + s * 1 * (u : ℂ) ^ (-s - 1)) (Set.uIcc u v) z :=
      ((h1.sub_const ((u : ℂ) ^ (-s))).add h2).hasDerivWithinAt
    rw [mul_one] at hd; exact hd
  have hbd : ∀ z ∈ Set.uIcc u v, ‖-s * (z : ℂ) ^ (-s - 1) + s * (u : ℂ) ^ (-s - 1)‖ ≤
      ‖s‖ * ‖s + 1‖ * a ^ (-s.re - 2) * ‖v - u‖ := by
    intro z hz
    rw [show -s * (z : ℂ) ^ (-s - 1) + s * (u : ℂ) ^ (-s - 1) =
        s * ((u : ℂ) ^ (-s - 1) - (z : ℂ) ^ (-s - 1)) by ring, norm_mul]
    have hl := lip s a z u ha (hge z hz) hu hs
    have hd : ‖u - z‖ ≤ ‖v - u‖ := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm]; exact Set.abs_sub_left_of_mem_uIcc hz
    have hC : 0 ≤ ‖s + 1‖ * a ^ (-s.re - 2) := by positivity
    calc ‖s‖ * ‖(u : ℂ) ^ (-s - 1) - (z : ℂ) ^ (-s - 1)‖
        ≤ ‖s‖ * (‖s + 1‖ * a ^ (-s.re - 2) * ‖u - z‖) := by gcongr
      _ ≤ ‖s‖ * (‖s + 1‖ * a ^ (-s.re - 2) * ‖v - u‖) := by gcongr
      _ = ‖s‖ * ‖s + 1‖ * a ^ (-s.re - 2) * ‖v - u‖ := by ring
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hbd (convex_uIcc u v)
    Set.left_mem_uIcc Set.right_mem_uIcc
  have hgu : g u = 0 := by simp [g]
  rw [hgu, sub_zero] at key
  calc _ ≤ _ := key
    _ = ‖s‖ * ‖s + 1‖ * a ^ (-s.re - 2) * (v - u) ^ 2 := by
        rw [Real.norm_eq_abs, mul_assoc _ |v - u| |v - u|, ← sq, sq_abs]
private theorem hasSum_hurwitzZeta (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun n : ℕ => (((n : ℝ) + x : ℝ) : ℂ) ^ (-s)) (HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s) := by
  convert HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re ⟨h0, h1⟩ hs using 1
  ext1 n; rw [Complex.cpow_neg, one_div]; push_cast; rfl
theorem b_termsum :
    ∀ (x : ℝ), 0 < x → x ≤ 1 → ∀ s : ℂ, 1 < s.re →
      ∑' n : ℕ, ((((n : ℝ) + x : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) -
        (1 - (x : ℂ)) * ((((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 2 : ℝ) : ℂ) ^ (-s))) =
      HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s - HurwitzZeta.hurwitzZeta ((1 : ℝ) : UnitAddCircle) s - (1 - (x : ℂ)) := by
  intro x hx0 hx1 s hs
  have hA := hasSum_hurwitzZeta x hx0.le hx1 s hs
  have hB := hasSum_hurwitzZeta 1 zero_le_one le_rfl s hs
  have hC : HasSum (fun n : ℕ => ((((n : ℝ) + 2 : ℝ)) : ℂ) ^ (-s))
      (HurwitzZeta.hurwitzZeta ((1 : ℝ) : UnitAddCircle) s - 1) := by
    have h := (hasSum_nat_add_iff' 1).mpr hB
    have e1 : (fun n : ℕ => ((((n : ℝ) + 2 : ℝ)) : ℂ) ^ (-s)) =
        fun n : ℕ => (((((n + 1 : ℕ) : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) := by
      funext n; congr 1; push_cast; ring
    have e2 : ∑ i ∈ range 1, (((((i : ℕ) : ℝ) + 1 : ℝ)) : ℂ) ^ (-s) = 1 := by simp
    rw [e1, ← e2]; exact h
  have hT := (hA.sub hB).sub ((hB.sub hC).mul_left (1 - (x : ℂ)))
  rw [hT.tsum_eq]; ring
private theorem termdiff_rpow_le {a e : ℝ} (ha : 0 < a) (h1 : -5 ≤ e) (h2 : e ≤ -(3 / 2)) :
    a ^ e ≤ 1 / |a| ^ (3 / 2 : ℝ) + 1 / |a| ^ (5 : ℝ) := by
  rw [abs_of_pos ha]
  have p1 : 0 ≤ 1 / a ^ (3 / 2 : ℝ) := by positivity
  have p2 : 0 ≤ 1 / a ^ (5 : ℝ) := by positivity
  rcases le_or_gt 1 a with h | h
  · have h' := Real.rpow_le_rpow_of_exponent_le h h2
    rw [Real.rpow_neg ha.le, ← one_div] at h'; linarith
  · have h' := Real.rpow_le_rpow_of_exponent_ge ha h.le h1
    rw [Real.rpow_neg ha.le, ← one_div] at h'; linarith
theorem b_termdiff :
    ∀ (x : ℝ), 0 < x → x ≤ 1 →
      DifferentiableOn ℂ (fun s : ℂ => ∑' n : ℕ, ((((n : ℝ) + x : ℝ) : ℂ) ^ (-s) -
        (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (1 - (x : ℂ)) *
          ((((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 2 : ℝ) : ℂ) ^ (-s))))
        ({s : ℂ | -1 / 2 < s.re} ∩ Metric.ball 0 3) := by
  intro x hx0 hx1
  have hU : IsOpen ({s : ℂ | -1 / 2 < s.re} ∩ Metric.ball 0 3) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  refine Complex.differentiableOn_tsum_of_summable_norm
    (u := fun n : ℕ => 24 * (1 / |(n : ℝ) + x| ^ (3 / 2 : ℝ) + 1 / |(n : ℝ) + x| ^ (5 : ℝ)))
    ?_ ?_ hU ?_
  · exact (((Real.summable_one_div_nat_add_rpow x (3 / 2)).2 (by norm_num)).add
      ((Real.summable_one_div_nat_add_rpow x 5).2 (by norm_num))).mul_left 24
  · intro n
    have hb : ∀ b : ℝ, 0 < b → Differentiable ℂ (fun s : ℂ => (b : ℂ) ^ (-s)) := fun b hb =>
      Differentiable.const_cpow differentiable_id.neg (Or.inl (by exact_mod_cast hb.ne'))
    exact (((hb _ (by positivity)).sub (hb _ (by positivity))).sub
      ((differentiable_const _).mul ((hb _ (by positivity)).sub (hb _ (by positivity))))).differentiableOn
  · intro n s hs
    obtain ⟨hre, hball⟩ := hs
    simp only [Set.mem_ofPred_eq] at hre
    rw [mem_ball_zero_iff] at hball
    have ha : (0 : ℝ) < (n : ℝ) + x := by positivity
    have hre2 : -2 ≤ s.re := by linarith
    have hR1 := b_taylor2 s ((n : ℝ) + x) ((n : ℝ) + 1) ((n : ℝ) + x) ha (by linarith) le_rfl hre2
    have hR2 := b_taylor2 s ((n : ℝ) + x) ((n : ℝ) + 1) ((n : ℝ) + 2) ha (by linarith) (by linarith) hre2
    have hA := termdiff_rpow_le ha (e := -s.re - 2) (by linarith [Complex.re_le_norm s]) (by linarith)
    have hA0 : 0 ≤ ((n : ℝ) + x) ^ (-s.re - 2) := Real.rpow_nonneg ha.le _
    have hs1 : ‖s + 1‖ ≤ 4 := by have := norm_add_le s 1; rw [norm_one] at this; linarith
    have hP : ‖s‖ * ‖s + 1‖ ≤ 3 * 4 := mul_le_mul hball.le hs1 (norm_nonneg _) (by norm_num)
    set B := 1 / |(n : ℝ) + x| ^ (3 / 2 : ℝ) + 1 / |(n : ℝ) + x| ^ (5 : ℝ)
    have hB0 : 0 ≤ B := hA0.trans hA
    have hsq1 : ((n : ℝ) + x - ((n : ℝ) + 1)) ^ 2 ≤ 1 := by nlinarith
    have hsq2 : ((n : ℝ) + 2 - ((n : ℝ) + 1)) ^ 2 ≤ 1 := by nlinarith
    have hR1' := hR1.trans (mul_le_mul (mul_le_mul hP hA hA0 (by norm_num)) hsq1 (sq_nonneg _) (by positivity))
    have hR2' := hR2.trans (mul_le_mul (mul_le_mul hP hA hA0 (by norm_num)) hsq2 (sq_nonneg _) (by positivity))
    have hnx : ‖(1 : ℂ) - (x : ℂ)‖ ≤ 1 := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    calc _ = ‖((((n : ℝ) + x : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)
              + s * ((((n : ℝ) + x : ℝ) : ℂ) - (((n : ℝ) + 1 : ℝ) : ℂ)) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s - 1))
            + (1 - (x : ℂ)) * ((((n : ℝ) + 2 : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)
              + s * ((((n : ℝ) + 2 : ℝ) : ℂ) - (((n : ℝ) + 1 : ℝ) : ℂ)) * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s - 1))‖ := by
          congr 1; push_cast; ring
      _ ≤ 3 * 4 * B * 1 + 1 * (3 * 4 * B * 1) :=
          (norm_add_le _ _).trans (by rw [norm_mul]; exact add_le_add hR1' (mul_le_mul hnx hR2' (norm_nonneg _) zero_le_one))
      _ = 24 * B := by ring
theorem b_hurzero :
    ∀ (x : ℝ), 0 < x → x ≤ 1 → HurwitzZeta.hurwitzZeta (x : UnitAddCircle) 0 = 1 / 2 - (x : ℂ) := by
  intro x hx0 hx1
  set U : Set ℂ := {s | -1 / 2 < s.re} ∩ Metric.ball 0 3
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hUc : IsPreconnected U := ((convex_halfSpace_re_gt _).inter (convex_ball _ _)).isPreconnected
  have hG : DifferentiableOn ℂ (fun s => HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s -
      HurwitzZeta.hurwitzZeta ((1 : ℝ) : UnitAddCircle) s - (1 - (x : ℂ))) U := by
    intro s _
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.sub_const
    rcases eq_or_ne s 1 with rfl | hs
    · exact ((HurwitzZeta.differentiableAt_hurwitzZeta_sub_one_div (x : UnitAddCircle)).sub
        (HurwitzZeta.differentiableAt_hurwitzZeta_sub_one_div ((1 : ℝ) : UnitAddCircle))).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun t => by simp only [Pi.sub_apply]; ring)
    · exact (HurwitzZeta.differentiableAt_hurwitzZeta _ hs).sub (HurwitzZeta.differentiableAt_hurwitzZeta _ hs)
  have hev : ∀ᶠ s in nhds (2 : ℂ), 1 < s.re :=
    (Complex.continuous_re.tendsto 2).eventually (lt_mem_nhds (by norm_num))
  have h2 : (2 : ℂ) ∈ U := ⟨by simp; norm_num, by simp; norm_num⟩
  have heq := ((b_termdiff x hx0 hx1).analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
    (hG.analyticOnNhd hUo) hUc h2 (hev.mono fun s hs => b_termsum x hx0 hx1 s hs)
  have h0 := heq (show (0 : ℂ) ∈ U from ⟨by simp; norm_num, by simp⟩)
  have h1 : HurwitzZeta.hurwitzZeta ((1 : ℝ) : UnitAddCircle) 0 = -1 / 2 := by
    rw [AddCircle.coe_period, HurwitzZeta.hurwitzZeta_zero, riemannZeta_zero]
  simp only [neg_zero, Complex.cpow_zero, sub_self, mul_zero, tsum_zero] at h0
  rw [h1] at h0
  linear_combination -h0
private theorem hurwitzZeta_one_sub_eq_bernoulli (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (h0 : 0 < x) (h1 : x ≤ 1) :
    HurwitzZeta.hurwitzZeta (x : UnitAddCircle) (1 - k) =
      -1 / k * ((Polynomial.bernoulli k).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have e : (1 : ℂ) - ((0 + 1 : ℕ) : ℂ) = 0 := by push_cast; ring
    rw [e, b_hurzero x h0 h1]; simp [Polynomial.bernoulli_one]
  · have := HurwitzZeta.hurwitzZeta_neg_nat (k := m) (x := x) hm.ne' ⟨h0.le, h1⟩
    have e : (1 : ℂ) - ((m + 1 : ℕ) : ℂ) = -(m : ℂ) := by push_cast; ring
    rw [e, this]; push_cast; ring
theorem b_lval :
    ∀ {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) (k : ℕ), 1 ≤ k →
      ZMod.LFunction Φ (1 - k) = -genB k Φ / k := by
  intro N _ Φ k hk
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hpow : (N : ℂ) ^ (-(1 - (k : ℂ))) = (N : ℂ) ^ ((k : ℤ) - 1) := by
    rw [show -(1 - (k : ℂ)) = (((k : ℤ) - 1 : ℤ) : ℂ) by push_cast; ring, Complex.cpow_intCast]
  rw [ZMod.LFunction, hpow, ← b_sumicc, genB, Finset.mul_sum, neg_div, Finset.sum_div,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mem_Icc] at ha
  have hx0 : (0 : ℝ) < a / N := div_pos (by exact_mod_cast ha.1) hN
  have hx1 : (a : ℝ) / N ≤ 1 := (div_le_one hN).mpr (by exact_mod_cast ha.2)
  rw [ZMod.toAddCircle_natCast, hurwitzZeta_one_sub_eq_bernoulli k hk _ hx0 hx1, bcoef, map_mul, map_zpow₀,
    map_natCast, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hq : (algebraMap ℚ ℂ) ((a : ℚ) / N) = (((a : ℝ) / N : ℝ) : ℂ) := by simp
  rw [hq]; field_simp
theorem b_lprim :
    ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (k : ℕ), 1 ≤ k →
      χ.LFunction (1 - k) = -genB k χ / k ∧ Lprim χ (1 - k) = -Bprim k χ / k := by
  intro N _ χ k hk
  refine ⟨b_lval χ k hk, ?_⟩
  unfold Lprim Bprim
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  exact b_lval _ k hk
private theorem gauss_mul_gauss_inv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar * χ (-1) = N := by
  have hF : ZMod.dft (⇑χ) = fun k ↦ (fun j ↦ (⇑χ⁻¹) (-j)) k * gaussSum χ ZMod.stdAddChar :=
    funext fun k ↦ hχ.fourierTransform_eq_inv_mul_gaussSum k
  have h1 := congr_fun (ZMod.dft_dft (⇑χ)) 1
  rw [hF, ZMod.dft_mul_const, ZMod.dft_comp_neg] at h1
  simp only at h1
  rw [DirichletCharacter.fourierTransform_eq_gaussSum_mulShift, neg_neg, AddChar.mulShift_one,
    smul_eq_mul] at h1
  have hsq : χ (-1) * χ (-1) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
  rw [mul_comm (gaussSum χ _), h1, mul_assoc, hsq, mul_one]
private theorem conj_gauss {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    (starRingEnd ℂ) (gaussSum χ ZMod.stdAddChar) = gaussSum χ⁻¹ ZMod.stdAddChar * χ (-1) := by
  have h := gaussSum_mulShift_eq χ⁻¹ ZMod.stdAddChar (-1)
  rw [inv_inv, Units.val_neg, Units.val_one] at h
  rw [starRingEnd_apply, star_gaussSum_eq, AddChar.inv_mulShift, h, mul_comm]
theorem b_gauss :
    ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt N ∧ ‖χ.rootNumber‖ = 1 := by
  intro N _ χ hχ
  have hns : (Complex.normSq (gaussSum χ ZMod.stdAddChar) : ℂ) = N := by
    rw [← Complex.mul_conj, conj_gauss, ← mul_assoc, gauss_mul_gauss_inv χ hχ]
  have hns' : Complex.normSq (gaussSum χ ZMod.stdAddChar) = N := by exact_mod_cast hns
  have hg : ‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt N := by rw [Complex.norm_def, hns']
  refine ⟨hg, ?_⟩
  have hpos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  rw [DirichletCharacter.rootNumber, norm_div, norm_div, norm_pow, Complex.norm_I, one_pow, div_one,
    hg, Complex.norm_natCast_cpow_of_pos (NeZero.pos N),
    show (1 / 2 : ℂ).re = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  exact div_self (Real.sqrt_ne_zero'.mpr hpos)
private lemma fe_LFunction_const_mul {N : ℕ} [NeZero N] (c : ℂ) (Φ : ZMod N → ℂ) (s : ℂ) :
    ZMod.LFunction (fun j => c * Φ j) s = c * ZMod.LFunction Φ s := by
  simp only [ZMod.LFunction, Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
theorem b_fe :
    ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (k : ℕ),
      χ.IsPrimitive → 1 ≤ k → χ (-1) = (-1) ^ k →
      ‖χ.LFunction (1 - k)‖ =
        2 * ((k - 1).factorial : ℝ) * (N : ℝ) ^ ((k : ℝ) - 1 / 2) / (2 * Real.pi) ^ k * ‖χ⁻¹.LFunction k‖ := by
  intro N _ χ k hχ hk hpar
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  set g := gaussSum χ ZMod.stdAddChar
  have hinv1 : χ⁻¹ (-1) = χ (-1) := by
    rw [MulChar.inv_apply_eq_inv', hpar, ← inv_pow, inv_neg_one]
  have hF : ZMod.dft (χ : ZMod N → ℂ) = fun j => (χ (-1) * g) * χ⁻¹ j := by
    funext j; rw [hχ.fourierTransform_eq_inv_mul_gaussSum, show -j = -1 * j by ring, map_mul, hinv1]; ring
  have hF' : ZMod.dft (fun x => χ (-x)) = fun j => g * χ⁻¹ j := by
    rw [ZMod.dft_comp_neg]; funext j; rw [hχ.fourierTransform_eq_inv_mul_gaussSum, neg_neg]; ring
  have hs : ∀ n : ℕ, ((m + 1 : ℕ) : ℂ) ≠ -n := fun n h => by
    have h2 := congrArg Complex.re h; simp at h2; linarith
  have hs' : χ 0 = 0 ∨ ((m + 1 : ℕ) : ℂ) ≠ 1 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · left
      apply χ.map_zero'
      rintro rfl
      have h1 : (-1 : ZMod 1) = 1 := Subsingleton.elim _ _
      rw [h1, map_one] at hpar; norm_num at hpar
    · right; exact_mod_cast (by omega : m + 1 ≠ 1)
  have hfe := ZMod.LFunction_one_sub (χ : ZMod N → ℂ) hs hs'
  rw [hF, hF', fe_LFunction_const_mul, fe_LFunction_const_mul] at hfe
  have he1 : Complex.exp ((Real.pi : ℂ) * Complex.I * ((m + 1 : ℕ) : ℂ) / 2) = Complex.I ^ (m + 1) := by
    rw [show (Real.pi : ℂ) * Complex.I * ((m + 1 : ℕ) : ℂ) / 2 =
        ((m + 1 : ℕ) : ℂ) * ((Real.pi : ℂ) / 2 * Complex.I) by ring,
      Complex.exp_nat_mul, Complex.exp_pi_div_two_mul_I]
  have he2 : Complex.exp (-(Real.pi : ℂ) * Complex.I * ((m + 1 : ℕ) : ℂ) / 2) = (-Complex.I) ^ (m + 1) := by
    rw [show -(Real.pi : ℂ) * Complex.I * ((m + 1 : ℕ) : ℂ) / 2 =
        ((m + 1 : ℕ) : ℂ) * (-(Real.pi : ℂ) / 2 * Complex.I) by ring,
      Complex.exp_nat_mul, Complex.exp_neg_pi_div_two_mul_I]
  have hGam : Complex.Gamma ((m + 1 : ℕ) : ℂ) = (m.factorial : ℂ) := by
    rw [Nat.cast_succ, Complex.Gamma_nat_eq_factorial]
  have h2pi : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  have key : ZMod.LFunction (χ : ZMod N → ℂ) (1 - ((m + 1 : ℕ) : ℂ)) =
      (N : ℂ) ^ (((m + 1 : ℕ) : ℂ) - 1) * ((2 * Real.pi : ℝ) : ℂ) ^ (-((m + 1 : ℕ) : ℂ)) *
        (m.factorial : ℂ) * g * ZMod.LFunction ⇑(χ⁻¹) ((m + 1 : ℕ) : ℂ) * (2 * (-Complex.I) ^ (m + 1)) := by
    rw [hfe, he1, he2, hGam, hpar, ← h2pi, neg_pow Complex.I]; ring
  show ‖ZMod.LFunction (χ : ZMod N → ℂ) (1 - ((m + 1 : ℕ) : ℂ))‖ = _
  rw [key]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul,
    Complex.norm_natCast_cpow_of_pos (NeZero.pos N),
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), (b_gauss χ hχ).1]
  simp only [norm_mul, norm_pow, norm_neg, Complex.norm_I, one_pow, mul_one, Complex.norm_natCast]
  have hre1 : (((m + 1 : ℕ) : ℂ) - 1).re = ((m : ℕ) : ℝ) := by simp
  have hre2 : (-((m + 1 : ℕ) : ℂ)).re = -((m + 1 : ℕ) : ℝ) := by simp
  have hL : DirichletCharacter.LFunction χ⁻¹ ((m + 1 : ℕ) : ℂ) = ZMod.LFunction ⇑(χ⁻¹) ((m + 1 : ℕ) : ℂ) := rfl
  have hNr : (N : ℝ) ^ (((m + 1 : ℕ) : ℝ) - 1 / 2) = (N : ℝ) ^ m * √(N : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hNpos]
    congr 1; push_cast; ring
  rw [hre1, hre2, Real.rpow_neg (by positivity), Real.rpow_natCast, Real.rpow_natCast, hL, hNr,
    Nat.add_sub_cancel, Complex.norm_two]
  have hpi : (0 : ℝ) < (2 * Real.pi) ^ (m + 1) := by positivity
  field_simp
theorem b_nzC :
    ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (k : ℕ), 1 ≤ k →
      χ (-1) = (-1) ^ k → Bprim k χ ≠ 0 ∧ (2 ≤ k → genB k χ ≠ 0) := by
  intro N _ χ k hk hpar
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hprim := χ.primitiveCharacter_isPrimitive
  have hpar' : χ.primitiveCharacter (-1) = (-1) ^ k := by rw [(b_parity k χ).2, hpar]
  have hne1 : χ.primitiveCharacter⁻¹ ≠ 1 ∨ (k : ℂ) ≠ 1 := by
    rcases Nat.lt_or_ge 1 k with h | h
    · right; exact_mod_cast (ne_of_gt h)
    · left
      have hk1 : k = 1 := le_antisymm h hk
      intro h1
      have h1' : χ.primitiveCharacter = 1 := inv_eq_one.mp h1
      rw [h1', MulChar.one_apply isUnit_one.neg, hk1, pow_one] at hpar'
      norm_num at hpar'
  have hL := b_fe χ.primitiveCharacter k hprim hk hpar'
  have hLne : DirichletCharacter.LFunction χ.primitiveCharacter⁻¹ (k : ℂ) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re _ hne1 (by simp; exact_mod_cast hk)
  have hB : Bprim k χ ≠ 0 := by
    intro h0
    have hl := (b_lprim χ.primitiveCharacter k hk).1
    have hg : genB k ⇑χ.primitiveCharacter = 0 := h0
    rw [hg, neg_zero, zero_div] at hl
    rw [hl, norm_zero] at hL
    have hc : (0 : ℝ) < (χ.conductor : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero χ.conductor_ne_zero
    have hpos : (0 : ℝ) < 2 * ((k - 1).factorial : ℝ) * (χ.conductor : ℝ) ^ ((k : ℝ) - 1 / 2) /
        (2 * Real.pi) ^ k * ‖DirichletCharacter.LFunction χ.primitiveCharacter⁻¹ (k : ℂ)‖ :=
      mul_pos (div_pos (mul_pos (by positivity) (Real.rpow_pos_of_pos hc _)) (by positivity))
        (norm_pos_iff.mpr hLne)
    linarith
  refine ⟨hB, fun hk2 => ?_⟩
  rw [b_primlevel k χ (Nat.pos_of_ne_zero (NeZero.ne N)) hk]
  refine mul_ne_zero hB ?_
  rw [Finset.prod_ne_zero_iff]
  intro p hp h0
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have heq : primVal χ p * (p : ℂ) ^ (k - 1) = 1 := by linear_combination -h0
  have hv : ‖primVal χ p‖ = 0 ∨ ‖primVal χ p‖ = 1 := by
    by_cases hu : IsUnit (p : ZMod χ.conductor)
    · right; have := χ.primitiveCharacter.unit_norm_eq_one hu.unit; rwa [IsUnit.unit_spec] at this
    · left; simp [primVal, MulChar.map_nonunit _ hu]
  have hn := congrArg norm heq
  rw [norm_mul, norm_pow, Complex.norm_natCast, norm_one] at hn
  rcases hv with h | h
  · rw [h, zero_mul] at hn; exact zero_ne_one hn
  · rw [h, one_mul] at hn
    have hn' : p ^ (k - 1) = 1 := by exact_mod_cast hn
    rcases Nat.pow_eq_one.mp hn' with h1 | h1
    · exact hpp.one_lt.ne' h1
    · omega
private theorem nz_iff {R S : Type} [Field R] [Algebra ℚ R] [Field S] [Algebra ℚ S] {N : ℕ} [NeZero N]
    (f : R →+* S) (χ : DirichletCharacter R N) (k : ℕ) :
    ((χ.ringHomComp f : DirichletCharacter S N) (-1) = (-1) ^ k ↔ χ (-1) = (-1) ^ k) ∧
    (Bprim k (χ.ringHomComp f : DirichletCharacter S N) ≠ 0 ↔ Bprim k χ ≠ 0) ∧
    (genB k (χ.ringHomComp f : ZMod N → S) ≠ 0 ↔ genB k χ ≠ 0) := by
  have hinj : Function.Injective f := f.injective
  refine ⟨?_, ?_, ?_⟩
  · rw [MulChar.ringHomComp_apply]
    have e : ((-1 : S)) ^ k = f ((-1 : R) ^ k) := by simp
    rw [e]; exact hinj.eq_iff
  · rw [← b_primmap f hinj k χ]; exact map_ne_zero_iff f hinj
  · rw [← map_genB_char f k χ]; exact map_ne_zero_iff f hinj
theorem b_nzany :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] {N : ℕ} [NeZero N] (χ : DirichletCharacter Ω N) (k : ℕ),
      1 ≤ k → χ (-1) = (-1) ^ k → Bprim k χ ≠ 0 ∧ (2 ≤ k → genB k χ ≠ 0) := by
  intro Ω _ _ N _ χ k hk hχ
  have : NeZero (Monoid.exponent (ZMod N)ˣ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  let i : Ω →+* AlgebraicClosure Ω := algebraMap _ _
  let f : AlgebraicClosure ℚ →+* AlgebraicClosure Ω :=
    (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure Ω).toRingHom
  let g : AlgebraicClosure ℚ →+* ℂ :=
    (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] ℂ).toRingHom
  obtain ⟨ψ, -, hψ⟩ := (b_charbij (N := N) f Set.univ).surjOn
    (show (χ.ringHomComp i : DirichletCharacter _ N) ∈ charSet (AlgebraicClosure Ω) Set.univ from Set.mem_univ _)
  obtain ⟨a1, a2, a3⟩ := nz_iff i χ k
  obtain ⟨b1, b2, b3⟩ := nz_iff f ψ k
  obtain ⟨c1, c2, c3⟩ := nz_iff g ψ k
  simp only at hψ
  rw [hψ] at b1 b2 b3
  obtain ⟨h1, h2⟩ := b_nzC (ψ.ringHomComp g) k hk (c1.2 (b1.1 (a1.2 hχ)))
  exact ⟨a2.1 (b2.2 (c2.1 h1)), fun h => a3.1 (b3.2 (c3.1 (h2 h)))⟩
theorem b_prodint :
    ∀ {N : ℕ} [NeZero N] (k : ℕ) (P : Set (Subgroup (ZMod N)ˣ)),
      1 ≤ k → P ⊆ parKer N k →
      ∃ M : ℤ, M ≠ 0 ∧ Real.log |(M : ℝ)| ≤ (charSet ℂ P).ncard * Real.log (bnd N k) ∧
        ∀ (Ω : Type) [Field Ω] [CharZero Ω] [HasEnoughRootsOfUnity Ω (Monoid.exponent (ZMod N)ˣ)],
          ∏ᶠ χ ∈ charSet Ω P, (den N k : Ω) * Bprim k χ = (M : Ω) := by
  intro N _ k P hk hP
  obtain ⟨q, hq⟩ := b_ratprod P (fun Ω _ _ χ => (den N k : Ω) * Bprim k χ) (by
    intro K Ω _ _ _ _ f χ; simp only [map_mul, map_natCast]; rw [b_primmap f f.injective])
  have hfin : (charSet ℂ P).Finite := Set.toFinite _
  have : NeZero (Monoid.exponent (ZMod N)ˣ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have hC := hq ℂ
  rw [finprod_mem_eq_finite_toFinset_prod _ hfin] at hC
  have hint : IsIntegral ℤ (q : ℂ) := by
    rw [← hC]; exact IsIntegral.prod _ fun χ _ => (b_primmem k χ).2.2.1
  have hint' : IsIntegral ℤ q := by
    have : (q : ℂ) = algebraMap ℚ ℂ q := rfl
    rw [this] at hint
    exact (isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).mp hint
  obtain ⟨M, hM⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint'
  have hM' : (M : ℚ) = q := by simpa using hM
  subst hM'
  have hC' : ∏ χ ∈ hfin.toFinset, (den N k : ℂ) * Bprim k χ = (M : ℂ) := by rw [hC]; simp
  have hM0 : M ≠ 0 := by
    have : (M : ℂ) ≠ 0 := by
      rw [← hC']
      refine Finset.prod_ne_zero_iff.mpr fun χ hχ => mul_ne_zero
        (Nat.cast_ne_zero.mpr (den_pos (NeZero.pos N) k).ne') ?_
      have hχ' : χ.toUnitHom.ker ∈ P := hfin.mem_toFinset.mp hχ
      exact (b_nzC χ k hk ((b_parity k χ).1.mp (hP hχ'))).1
    exact_mod_cast this
  refine ⟨M, hM0, ?_, fun Ω _ _ _ => ?_⟩
  · have hle : |(M : ℝ)| ≤ bnd N k ^ (charSet ℂ P).ncard := by
      have h1 : |(M : ℝ)| = ‖(M : ℂ)‖ := by simp
      rw [h1, ← hC', norm_prod, Set.ncard_eq_toFinset_card _ hfin, ← Finset.prod_const]
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun χ _ => (b_denupper k χ).2.1
    rw [← Real.log_pow]
    exact Real.log_le_log (abs_pos.mpr (Int.cast_ne_zero.mpr hM0)) hle
  · rw [hq Ω]; simp
private theorem b_ultra_int {Ω : Type} [NormedField Ω] [IsUltrametricDist Ω] {y : Ω}
    (h : IsIntegral ℤ y) : ‖y‖ ≤ 1 := by
  obtain ⟨p, hp, hpy⟩ := h
  exact CapelliCore.norm_le_one_of_monic_root (Int.castRingHom Ω)
    (fun a => IsUltrametricDist.norm_intCast_le_one Ω a) y p hp hpy
private theorem b_ultra_unit {Ω : Type} [NormedField Ω] [IsUltrametricDist Ω] (l : ℕ)
    [hl : Fact l.Prime] (hn : ‖(l : Ω)‖ = (l : ℝ)⁻¹) (m : ℤ) (hm : ¬ (l : ℤ) ∣ m) :
    ‖(m : Ω)‖ = 1 := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl.out
  obtain ⟨a, b, hab⟩ := (hp.irreducible.coprime_iff_not_dvd).mpr hm
  have h1 : (a : Ω) * l + b * m = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hlt : ‖(l : Ω)‖ < 1 := by rw [hn]; exact inv_lt_one_of_one_lt₀ hl1
  refine le_antisymm (IsUltrametricDist.norm_intCast_le_one Ω m) ?_
  by_contra hc
  push Not at hc
  have ha := IsUltrametricDist.norm_intCast_le_one Ω a
  have hb := IsUltrametricDist.norm_intCast_le_one Ω b
  have h2 := IsUltrametricDist.norm_add_le_max ((a : Ω) * l) ((b : Ω) * m)
  rw [h1, norm_one, norm_mul, norm_mul] at h2
  have h3 : ‖(a : Ω)‖ * ‖(l : Ω)‖ < 1 := mul_lt_one_of_nonneg_of_lt_one_right ha (norm_nonneg _) hlt
  have h4 : ‖(b : Ω)‖ * ‖(m : Ω)‖ < 1 := mul_lt_one_of_nonneg_of_lt_one_right hb (norm_nonneg _) hc
  exact absurd h2 (not_le.mpr (max_lt h3 h4))
private theorem b_ultra_log {Ω : Type} [NormedField Ω] [IsUltrametricDist Ω] (l : ℕ)
    [hl : Fact l.Prime] (hn : ‖(l : Ω)‖ = (l : ℝ)⁻¹) (M : ℤ) (hM : M ≠ 0) :
    -Real.log ‖(M : Ω)‖ = (padicValInt l M : ℝ) * Real.log l := by
  obtain ⟨m, hm⟩ := padicValInt_dvd (p := l) M
  have hnd : ¬ (l : ℤ) ∣ m := by
    rintro ⟨c, hc⟩
    have hd : (l : ℤ) ^ (padicValInt l M + 1) ∣ M :=
      ⟨c, by rw [pow_succ]; (conv_lhs => rw [hm, hc]); ring⟩
    have hdN : l ^ (padicValInt l M + 1) ∣ M.natAbs := by
      simpa [Int.natAbs_pow] using Int.natAbs_dvd_natAbs.mpr hd
    have hle := (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hM)).mp hdN
    change padicValNat l M.natAbs + 1 ≤ padicValNat l M.natAbs at hle
    omega
  have h1 : (M : Ω) = (l : Ω) ^ padicValInt l M * m := by
    exact_mod_cast congrArg (Int.cast : ℤ → Ω) hm
  rw [h1, norm_mul, b_ultra_unit l hn m hnd, mul_one, norm_pow, hn, Real.log_pow, Real.log_inv]
  ring
theorem b_ultra :
    ∀ {Ω ι : Type} [NormedField Ω] [IsUltrametricDist Ω] [CharZero Ω] (l : ℕ) [Fact l.Prime],
      ‖(l : Ω)‖ = (l : ℝ)⁻¹ → ∀ (S : Set ι) (x : ι → Ω) (D : ℕ) (M : ℤ),
      S.Finite → M ≠ 0 → (∀ i ∈ S, IsIntegral ℤ ((D : Ω) * x i)) →
      ∏ᶠ i ∈ S, (D : Ω) * x i = (M : Ω) →
      ∑ᶠ i ∈ S, max 0 (-Real.log ‖x i‖) ≤ (padicValInt l M : ℝ) * Real.log l := by
  intro Ω ι _ _ _ l _ hn S x D M hS hM hint hprod
  rw [finprod_mem_eq_finite_toFinset_prod _ hS] at hprod
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, ← b_ultra_log l hn M hM, ← hprod, norm_prod]
  have hM' : (M : Ω) ≠ 0 := by exact_mod_cast hM
  have hne : ∀ i ∈ hS.toFinset, (D : Ω) * x i ≠ 0 := by
    rw [← Finset.prod_ne_zero_iff, hprod]; exact hM'
  rw [Real.log_prod (fun i hi => norm_ne_zero_iff.mpr (hne i hi)), ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ∈ S := by simpa using hi
  have h0 := hne i hi
  have hD : (D : Ω) ≠ 0 := left_ne_zero_of_mul h0
  have hx : x i ≠ 0 := right_ne_zero_of_mul h0
  refine max_le ?_ ?_
  · have := Real.log_nonpos (norm_nonneg _) (b_ultra_int (hint i hi'))
    linarith
  · rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hD) (norm_ne_zero_iff.mpr hx)]
    have := Real.log_nonpos (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one Ω D)
    linarith
theorem b_sumval :
    ∀ (M : ℤ), M ≠ 0 → ∀ T : Finset ℕ, (∀ l ∈ T, l.Prime) →
      ∑ l ∈ T, (padicValInt l M : ℝ) * Real.log l ≤ Real.log |(M : ℝ)| := by
  intro M hM T hT
  have hN : M.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hM
  have hlog : Real.log |(M : ℝ)| = Real.log (M.natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hlog, Real.log_nat_eq_sum_factorization, Finsupp.sum]
  calc ∑ l ∈ T, (padicValInt l M : ℝ) * Real.log l
      = ∑ l ∈ T, (M.natAbs.factorization l : ℝ) * Real.log l := by
        refine Finset.sum_congr rfl fun l hl => ?_
        rw [Nat.factorization_def _ (hT l hl)]; rfl
    _ = ∑ l ∈ T.filter (· ∈ M.natAbs.factorization.support),
          (M.natAbs.factorization l : ℝ) * Real.log l := by
        refine (Finset.sum_filter_of_ne fun l _ h => ?_).symm
        rw [Finsupp.mem_support_iff]; intro h0; apply h; simp [h0]
    _ ≤ ∑ p ∈ M.natAbs.factorization.support,
          (M.natAbs.factorization p : ℝ) * Real.log p := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => (Finset.mem_filter.mp hx).2)
          (fun p _ _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p))

end BernoulliNumbers

/-! ## Section 2: Quantum Determinant Foundations on `RHDirect.CapelliCore` -/

section QuantumDeterminantFoundations
open CapelliCore
/-- Highest-weight module predicate for `𝔤𝔩_n` generators. -/
def IsHW {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (ν : Fin n → ℂ) (v : V) : Prop :=
  (∀ a, E a a v = ν a • v) ∧ ∀ a b, a < b → E a b v = 0
lemma map_qdet {A B : Type*} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] {n : ℕ}
    (φ : A →ₐ[ℂ] B) (X : Fin n → Fin n → A) (u : ℂ) :
    φ (qdet X u) = qdet (fun a b => φ (X a b)) u := by
  have hT : ∀ v a b, φ (capelliTm X v a b) = capelliTm (fun a b => φ (X a b)) v a b := by
    intro v a b; unfold capelliTm; split_ifs <;> simp
  simp only [qdet, qminor, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn,
    Function.comp_def, hT]
lemma qdet_shift {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
    (X : Fin n → Fin n → A) (s u : ℂ) :
    qdet (fun i j => X i j + if i = j then algebraMap ℂ A s else 0) u = qdet X (u + s) := by
  simp only [qdet, qminor]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 3; funext k
  simp only [capelliTm]
  split_ifs with h
  · simp only [map_sub, map_add]; abel
  · rw [add_zero]
lemma qdet_semiconj {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
    (E E' : Fin n → Fin n → A) (R : A) (h : ∀ a b, R * E a b = E' a b * R) (u : ℂ) :
    R * qdet E u = qdet E' u * R := by
  have hp : ∀ {t : ℕ} (x y : Fin t → A), (∀ k, R * x k = y k * R) →
      R * (List.ofFn x).prod = (List.ofFn y).prod * R := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      intro x y hxy
      simp only [List.ofFn_succ, List.prod_cons]
      rw [← mul_assoc, hxy, mul_assoc, ih _ _ (fun k => hxy k.succ), mul_assoc]
  simp only [qdet, qminor, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← mul_assoc, ← (Int.cast_commute _ R).eq, mul_assoc, mul_assoc, hp]
  intro k
  simp only [capelliTm, mul_add, add_mul, h]
  split_ifs
  · rw [Algebra.commutes]
  · simp
private lemma prod_ofFn_sum_smul {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} {ι : Type*} [Fintype ι]
    (a : Fin n → ι → ℂ) (T : Fin n → ι → A) :
    (List.ofFn fun k => ∑ c, a k c • T k c).prod =
      ∑ c : Fin n → ι, (∏ k, a k (c k)) • (List.ofFn fun k => T k (c k)).prod := by
  classical
  have h := (MultilinearMap.mkPiAlgebraFin ℂ n A).map_sum (fun k c => a k c • T k c)
  simp only [MultilinearMap.map_smul_univ, MultilinearMap.mkPiAlgebraFin_apply] at h
  exact h
private lemma prod_ofFn_adjacent {A : Type*} [Ring A] :
    ∀ (m : ℕ) (i : Fin m) (g₁ g₂ g₃ g₄ : Fin (m + 1) → A),
      (∀ k, k ≠ i.castSucc → k ≠ i.succ → g₂ k = g₁ k ∧ g₃ k = g₁ k ∧ g₄ k = g₁ k) →
      g₁ i.castSucc * g₁ i.succ + g₂ i.castSucc * g₂ i.succ =
        g₃ i.castSucc * g₃ i.succ + g₄ i.castSucc * g₄ i.succ →
      (List.ofFn g₁).prod + (List.ofFn g₂).prod = (List.ofFn g₃).prod + (List.ofFn g₄).prod
  | 0, i, _, _, _, _, _, _ => i.elim0
  | m + 1, i, g₁, g₂, g₃, g₄, h, e => by
    refine Fin.cases (motive := fun i : Fin (m + 1) =>
      (∀ k, k ≠ i.castSucc → k ≠ i.succ → g₂ k = g₁ k ∧ g₃ k = g₁ k ∧ g₄ k = g₁ k) →
      g₁ i.castSucc * g₁ i.succ + g₂ i.castSucc * g₂ i.succ =
        g₃ i.castSucc * g₃ i.succ + g₄ i.castSucc * g₄ i.succ →
      (List.ofFn g₁).prod + (List.ofFn g₂).prod = (List.ofFn g₃).prod + (List.ofFn g₄).prod)
      ?_ ?_ i h e
    · intro h e
      have hk : ∀ k : Fin m, g₂ k.succ.succ = g₁ k.succ.succ ∧ g₃ k.succ.succ = g₁ k.succ.succ ∧
          g₄ k.succ.succ = g₁ k.succ.succ := fun k =>
        h _ (Fin.succ_ne_zero _) (fun hh => Fin.succ_ne_zero _ (Fin.succ_injective _ hh))
      rw [List.ofFn_succ (f := g₁), List.ofFn_succ (f := g₂), List.ofFn_succ (f := g₃),
        List.ofFn_succ (f := g₄), List.ofFn_succ (f := fun k => g₁ (Fin.succ k)),
        List.ofFn_succ (f := fun k => g₂ (Fin.succ k)),
        List.ofFn_succ (f := fun k => g₃ (Fin.succ k)),
        List.ofFn_succ (f := fun k => g₄ (Fin.succ k))]
      simp only [List.prod_cons, (hk _).1, (hk _).2.1, (hk _).2.2, ← mul_assoc, ← add_mul]
      congr 1
    · intro j h e
      have h0 := h 0 (by rw [← Fin.succ_castSucc]; exact (Fin.succ_ne_zero _).symm) (Fin.succ_ne_zero _).symm
      have ih := prod_ofFn_adjacent m j (fun k => g₁ k.succ) (fun k => g₂ k.succ)
        (fun k => g₃ k.succ) (fun k => g₄ k.succ)
        (fun k h1 h2 => h _
          (by rw [← Fin.succ_castSucc]; exact fun hh => h1 (Fin.succ_injective _ hh))
          (fun hh => h2 (Fin.succ_injective _ hh)))
        (by simpa only [Fin.succ_castSucc] using e)
      rw [List.ofFn_succ (f := g₁), List.ofFn_succ (f := g₂), List.ofFn_succ (f := g₃),
        List.ofFn_succ (f := g₄)]
      simp only [List.prod_cons, h0.1, h0.2.1, h0.2.2, ← mul_add, ih]
private lemma two_rel_capelliTm {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
    (E : Fin n → Fin n → A) (hE : GlRel E) (y : ℂ) (a b c d : Fin n) :
    capelliTm E (y + 1) a d * capelliTm E y c b + capelliTm E (y + 1) a b * capelliTm E y c d =
      capelliTm E (y + 1) c d * capelliTm E y a b + capelliTm E (y + 1) c b * capelliTm E y a d := by
  let S : Fin n → Fin n → ℂ := fun p q => if p = q then 1 else 0
  have key : ∀ (x : ℂ) (p q : Fin n), capelliTm E x p q = (x * S p q) • (1 : A) + E p q := by
    intro x p q; unfold capelliTm; dsimp only [S]; split_ifs <;> simp [Algebra.algebraMap_eq_smul_one]
  have h1 := hE a b c d
  have h2 := hE a d c b
  have h1' : E a b * E c d = E c d * E a b + S c b • E a d - S a d • E c b := by
    rw [sub_eq_iff_eq_add'] at h1; rw [h1, add_sub_assoc]
    dsimp only [S]
    by_cases hbc : b = c <;> by_cases hda : d = a
    · simp [hbc, hda]
    · simp [hbc, hda, Ne.symm hda]
    · simp [hbc, hda, Ne.symm hbc]
    · simp [hbc, hda, Ne.symm hbc, Ne.symm hda]
  have h2' : E a d * E c b = E c b * E a d + S c d • E a b - S a b • E c d := by
    rw [sub_eq_iff_eq_add'] at h2; rw [h2, add_sub_assoc]
    dsimp only [S]
    by_cases hdc : d = c <;> by_cases hba : b = a
    · simp [hdc, hba]
    · simp [hdc, hba, Ne.symm hba]
    · simp [hdc, hba, Ne.symm hdc]
    · simp [hdc, hba, Ne.symm hdc, Ne.symm hba]
  simp only [key]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  rw [h1', h2']
  simp only [add_smul, smul_add, smul_smul]
  rw [show (y * S c b) * (y * S a d) = (y * S a d) * (y * S c b) by ring,
    show (y * S c d) * (y * S a b) = (y * S a b) * (y * S c d) by ring,
    show (y * S c b) * S a d = (y * S a d) * S c b by ring,
    show (y * S c d) * S a b = (y * S a b) * S c d by ring]
  abel
private lemma cast_sign_mul {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (x : A) :
    ((Equiv.Perm.sign σ : ℤ) : A) * x = (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) • x := by
  rw [Algebra.smul_def, map_intCast]
private lemma swap_mem_closure_adjacent (m : ℕ) :
    ∀ (x y : Fin (m + 1)),
      Equiv.swap x y ∈ Submonoid.closure
        {σ : Equiv.Perm (Fin (m + 1)) | ∃ i : Fin m, σ = Equiv.swap i.castSucc i.succ} := by
  let S := Submonoid.closure
    {σ : Equiv.Perm (Fin (m + 1)) | ∃ i : Fin m, σ = Equiv.swap i.castSucc i.succ}
  have hadj : ∀ (a b : ℕ) (ha : a < m + 1) (hb : b < m + 1), a ≤ b →
      Equiv.swap ⟨a, ha⟩ ⟨b, hb⟩ ∈ S := by
    intro a b ha hb hab
    induction h : b - a generalizing a b with
    | zero =>
      have : a = b := by omega
      subst this; rw [Equiv.swap_self]; exact S.one_mem
    | succ d ih =>
      rcases eq_or_ne d 0 with rfl | hd
      · have : b = a + 1 := by omega
        subst this
        exact Submonoid.subset_closure ⟨⟨a, by omega⟩, rfl⟩
      · have hb1 : a ≤ b - 1 := by omega
        have hlt : b - 1 < m + 1 := by omega
        have hadj1 : Equiv.swap (⟨b - 1, hlt⟩ : Fin (m + 1)) ⟨b, hb⟩ ∈ S := by
          have : (⟨b, hb⟩ : Fin (m + 1)) = (⟨b - 1, by omega⟩ : Fin m).succ := Fin.ext (by simp; omega)
          rw [this]; exact Submonoid.subset_closure ⟨⟨b - 1, by omega⟩, rfl⟩
        have ih1 := ih a (b - 1) ha hlt hb1 (by omega)
        have hconj : Equiv.swap (⟨a, ha⟩ : Fin (m + 1)) ⟨b, hb⟩ =
            Equiv.swap ⟨b - 1, hlt⟩ ⟨b, hb⟩ * Equiv.swap ⟨a, ha⟩ ⟨b - 1, hlt⟩ *
              Equiv.swap ⟨b - 1, hlt⟩ ⟨b, hb⟩ := by
          have hne1 : (⟨b - 1, hlt⟩ : Fin (m + 1)) ≠ ⟨b, hb⟩ := by simp [Fin.ext_iff]; omega
          have hne2 : (⟨a, ha⟩ : Fin (m + 1)) ≠ ⟨b - 1, hlt⟩ := by simp [Fin.ext_iff]; omega
          have hne3 : (⟨a, ha⟩ : Fin (m + 1)) ≠ ⟨b, hb⟩ := by simp [Fin.ext_iff]; omega
          ext k
          simp only [Equiv.Perm.mul_apply]
          by_cases hk1 : k = ⟨b - 1, hlt⟩
          · subst hk1; rw [Equiv.swap_apply_of_ne_of_ne hne2.symm hne1,
              Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hne3.symm hne1.symm,
              Equiv.swap_apply_right]
          · by_cases hk2 : k = ⟨b, hb⟩
            · subst hk2; rw [Equiv.swap_apply_right, Equiv.swap_apply_right,
                Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hne2 hne3]
            · by_cases hk3 : k = ⟨a, ha⟩
              · subst hk3; rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hne2 hne3,
                  Equiv.swap_apply_left, Equiv.swap_apply_left]
              · rw [Equiv.swap_apply_of_ne_of_ne hk3 hk2, Equiv.swap_apply_of_ne_of_ne hk1 hk2,
                  Equiv.swap_apply_of_ne_of_ne hk3 hk1, Equiv.swap_apply_of_ne_of_ne hk1 hk2]
        rw [hconj]
        exact S.mul_mem (S.mul_mem hadj1 ih1) hadj1
  intro x y
  rcases le_total x.val y.val with h | h
  · exact hadj x.val y.val x.isLt y.isLt h
  · rw [Equiv.swap_comm]; exact hadj y.val x.val y.isLt x.isLt h
private lemma qminor_swap_adjacent {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ}
    (E : Fin n → Fin n → A) (hE : GlRel E) (a : Fin (m + 1) → Fin n) (u : ℂ)
    (i : Fin m) (b : Fin (m + 1) → Fin n) :
    qminor E a (b ∘ Equiv.swap i.castSucc i.succ) u = -qminor E a b u := by
  let s : Equiv.Perm (Fin (m + 1)) := Equiv.swap i.castSucc i.succ
  have hne : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ (i := i)).ne
  have hs : Equiv.Perm.sign s = -1 := Equiv.Perm.sign_swap hne
  have hpair : ∀ σ : Equiv.Perm (Fin (m + 1)),
      (List.ofFn fun k : Fin (m + 1) => capelliTm E (u - (k : ℕ)) (a (σ k)) (b (s k))).prod +
      (List.ofFn fun k : Fin (m + 1) => capelliTm E (u - (k : ℕ)) (a (σ k)) (b k)).prod =
      (List.ofFn fun k : Fin (m + 1) => capelliTm E (u - (k : ℕ)) (a ((σ * s) k)) (b k)).prod +
      (List.ofFn fun k : Fin (m + 1) => capelliTm E (u - (k : ℕ)) (a ((σ * s) k)) (b (s k))).prod := by
    intro σ
    apply prod_ofFn_adjacent m i
    · intro k h1 h2
      have hsk : s k = k := Equiv.swap_apply_of_ne_of_ne h1 h2
      simp only [Equiv.Perm.mul_apply, hsk, and_self]
    · simp only [Equiv.Perm.mul_apply, s, Equiv.swap_apply_left, Equiv.swap_apply_right,
        Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
      have hy : u - (i : ℕ) = (u - ((i : ℕ) + 1)) + 1 := by ring
      rw [hy]
      exact (two_rel_capelliTm E hE (u - ((i : ℕ) + 1))
        (a (σ i.castSucc)) (b i.castSucc) (a (σ i.succ)) (b i.succ)).trans (add_comm _ _)
  have hsum : qminor E a (b ∘ s) u + qminor E a b u = -(qminor E a b u + qminor E a (b ∘ s) u) := by
    unfold qminor
    rw [← Finset.sum_add_distrib]
    have hl : (∑ σ : Equiv.Perm (Fin (m + 1)),
        (((Equiv.Perm.sign σ : ℤ) : A) * (List.ofFn fun k => capelliTm E (u - (k : ℕ)) (a (σ k)) ((b ∘ s) k)).prod +
         ((Equiv.Perm.sign σ : ℤ) : A) * (List.ofFn fun k => capelliTm E (u - (k : ℕ)) (a (σ k)) (b k)).prod)) =
        ∑ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : A) *
          ((List.ofFn fun k => capelliTm E (u - (k : ℕ)) (a ((σ * s) k)) (b k)).prod +
           (List.ofFn fun k => capelliTm E (u - (k : ℕ)) (a ((σ * s) k)) (b (s k))).prod) :=
      Finset.sum_congr rfl fun σ _ => by rw [← mul_add]; exact congrArg _ (hpair σ)
    rw [hl]
    have hneg : ∀ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : A) = -((Equiv.Perm.sign (σ * s) : ℤ) : A) := by
      intro σ; rw [Equiv.Perm.sign_mul, hs, Units.val_mul, Units.val_neg, Units.val_one]
      simp only [mul_neg, mul_one, Int.cast_neg, neg_neg]
    rw [Finset.sum_congr rfl (fun σ _ => by rw [hneg σ, neg_mul]), Finset.sum_neg_distrib]
    congr 1
    rw [← Finset.sum_add_distrib, Fintype.sum_equiv (Equiv.mulRight s) _
      (fun σ : Equiv.Perm (Fin (m + 1)) => ((Equiv.Perm.sign σ : ℤ) : A) *
        ((List.ofFn fun k => capelliTm E (u - (k : ℕ)) (a (σ k)) (b k)).prod +
         (List.ofFn fun k => capelliTm E (u - (k : ℕ)) (a (σ k)) ((b ∘ s) k)).prod))
      fun σ => by simp only [Equiv.coe_mulRight, mul_add, Function.comp_apply, Equiv.Perm.mul_apply]]
    exact Finset.sum_congr rfl fun _ _ => mul_add _ _ _
  have h2 : (2 : ℂ) • (qminor E a (b ∘ s) u + qminor E a b u) = 0 := by
    rw [two_smul]; nth_rw 2 [hsum]; rw [add_comm (qminor E a b u), add_neg_cancel]
  have h0 : qminor E a (b ∘ s) u + qminor E a b u = 0 := by
    have := congrArg ((2 : ℂ)⁻¹ • ·) h2
    simpa [smul_smul] using this
  exact eq_neg_of_add_eq_zero_left h0
lemma qminor_comp_perm {A : Type*} [Ring A] [Algebra ℂ A] {n t : ℕ}
    (E : Fin n → Fin n → A) (hE : GlRel E) (a : Fin t → Fin n) (u : ℂ)
    (τ : Equiv.Perm (Fin t)) (b : Fin t → Fin n) :
    qminor E a (b ∘ τ) u = (((Equiv.Perm.sign τ : ℤˣ) : ℤ) : ℂ) • qminor E a b u := by
  induction t with
  | zero =>
    have hτ : τ = 1 := Subsingleton.elim _ _
    subst hτ; simp
  | succ m =>
    have hmem : τ ∈ Submonoid.closure
        {σ : Equiv.Perm (Fin (m + 1)) | ∃ i : Fin m, σ = Equiv.swap i.castSucc i.succ} := by
      induction τ using Equiv.Perm.swap_induction_on with
      | one => exact Submonoid.one_mem _
      | swap_mul σ x y hxy ih =>
        exact Submonoid.mul_mem _ (swap_mem_closure_adjacent m x y) ih
    induction hmem using Submonoid.closure_induction generalizing b with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      have hne : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ (i := i)).ne
      rw [qminor_swap_adjacent E hE]; simp [Equiv.Perm.sign_swap hne]
    | one => simp
    | mul x y _ _ hx hy =>
      rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hy, hx, smul_smul]
      simp [mul_comm]
lemma qminor_eq_zero {A : Type*} [Ring A] [Algebra ℂ A] {n t : ℕ}
    (E : Fin n → Fin n → A) (hE : GlRel E) (a : Fin t → Fin n) (u : ℂ)
    (b : Fin t → Fin n) (hb : ¬ Function.Injective b) :
    qminor E a b u = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.1 hb
  have h := qminor_comp_perm E hE a u (Equiv.swap i j) b
  have hb' : b ∘ Equiv.swap i j = b := funext fun k => Equiv.apply_swap_eq_self hij k
  rw [hb', Equiv.Perm.sign_swap hne] at h
  have h2 : (2 : ℂ) • qminor E a b u = 0 := by
    rw [two_smul]
    calc qminor E a b u + qminor E a b u = qminor E a b u + (-qminor E a b u) := by
          conv_rhs => rw [← show (-1 : ℂ) • qminor E a b u = -qminor E a b u from neg_one_smul ℂ _]
          exact congrArg (qminor E a b u + ·) (by simpa using h)
      _ = 0 := add_neg_cancel _
  have := congrArg ((2 : ℂ)⁻¹ • ·) h2
  simpa [smul_smul] using this
private lemma sum_eq_sum_perm {n : ℕ} {V : Type*} [AddCommMonoid V] (F : (Fin n → Fin n) → V)
    (hF : ∀ d, ¬ Function.Injective d → F d = 0) :
    ∑ d, F d = ∑ σ : Equiv.Perm (Fin n), F σ := by
  classical
  symm
  refine Finset.sum_of_injOn (fun σ : Equiv.Perm (Fin n) => (σ : Fin n → Fin n))
    (fun _ _ _ _ h => DFunLike.coe_injective h) (fun _ _ => Finset.mem_univ _)
    (fun d _ hd => hF d fun hinj =>
      hd ⟨Equiv.ofBijective d (Finite.injective_iff_bijective.1 hinj), Finset.mem_univ _, rfl⟩)
    (fun _ _ => rfl)
private lemma capelliTm_conj {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
    (E : Fin n → Fin n → A) (P Q : Matrix (Fin n) (Fin n) ℂ) (h : Q * P = 1) (x : ℂ) (a b : Fin n) :
    capelliTm (fun a b : Fin n => ∑ c : Fin n, ∑ d : Fin n, (P c a * Q b d) • E c d) x a b =
      ∑ d, Q b d • ∑ c, P c a • capelliTm E x c d := by
  have h1 : ∑ d, Q b d * P d a = if a = b then 1 else 0 := by
    have := congrFun (congrFun h b) a
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [this]; simp [eq_comm]
  simp only [capelliTm, smul_add, Finset.sum_add_distrib]
  congr 1
  · simp only [smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, smul_smul,
      ← Finset.sum_smul, h1]
    split_ifs <;> simp
  · rw [Finset.sum_comm]; simp only [Finset.smul_sum, smul_smul, mul_comm]
theorem qdet_conj {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (hE : GlRel E) (P Q : Matrix (Fin n) (Fin n) ℂ) (h : Q * P = 1) (u : ℂ) :
    qdet (fun a b : Fin n => ∑ c : Fin n, ∑ d : Fin n, (P c a * Q b d) • E c d) u = qdet E u := by
  have hrow : ∀ d : Fin n → Fin n,
      ∑ σ : Equiv.Perm (Fin n), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) •
        (List.ofFn fun k : Fin n => ∑ c, P c (σ k) • capelliTm E (u - (k : ℕ)) c (d k)).prod =
      P.det • qminor E id d u := by
    intro d
    simp only [prod_ofFn_sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    have hdet : ∀ c : Fin n → Fin n,
        ∑ σ : Equiv.Perm (Fin n), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * ∏ k, P (c k) (σ k) =
          (P.submatrix c id).det := by
      intro c; rw [← Matrix.det_transpose, Matrix.det_apply']; rfl
    simp only [hdet]
    rw [sum_eq_sum_perm]
    · simp only [qminor, cast_sign_mul, Finset.smul_sum, smul_smul, Matrix.det_permute, id, mul_comm]
    · intro c hc
      obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.1 hc
      rw [Matrix.det_zero_of_row_eq hne (by funext k; simp [hij]), zero_smul]
  have h1 : qdet (fun a b : Fin n => ∑ c : Fin n, ∑ d : Fin n, (P c a * Q b d) • E c d) u =
      ∑ d : Fin n → Fin n, (∏ k, Q k (d k)) • P.det • qminor E id d u := by
    simp only [← hrow, Finset.smul_sum]
    rw [Finset.sum_comm]
    unfold qdet qminor
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [id, capelliTm_conj E P Q h, cast_sign_mul]
    rw [prod_ofFn_sum_smul (fun k d => Q k d)
      (fun k d => ∑ c, P c (σ k) • capelliTm E (u - ((k : Fin n) : ℂ)) c d)]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun d _ => smul_comm _ _ _
  rw [h1, sum_eq_sum_perm]
  · have h2 : ∀ σ : Equiv.Perm (Fin n), qminor E id σ u =
        (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) • qdet E u := fun σ => qminor_comp_perm E hE id u σ id
    simp only [h2, smul_smul, ← Finset.sum_smul]
    have h3 : ∑ σ : Equiv.Perm (Fin n),
        (∏ k, Q k (σ k)) * (P.det * (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)) = Q.det * P.det := by
      rw [← Matrix.det_transpose Q, Matrix.det_apply' Q.transpose, Finset.sum_mul]
      refine Finset.sum_congr rfl fun σ _ => ?_
      simp only [Matrix.transpose_apply]; ring
    rw [h3, ← Matrix.det_mul, h, Matrix.det_one, one_smul]
  · intro d hd
    rw [qminor_eq_zero E hE id u d hd, smul_zero, smul_zero]
private lemma prod_ofFn_apply_of_eigen {V : Type*} [AddCommGroup V] [Module ℂ V] :
    ∀ (m : ℕ) (F : Fin m → Module.End ℂ V) (c : Fin m → ℂ) (v : V),
      (∀ k, F k v = c k • v) → (List.ofFn F).prod v = (∏ k, c k) • v
  | 0, _, _, _, _ => by simp
  | m + 1, F, c, v, h => by
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply,
      prod_ofFn_apply_of_eigen m (fun i => F i.succ) (fun i => c i.succ) v (fun i => h i.succ),
      map_smul, h 0, smul_smul, Fin.prod_univ_succ, mul_comm (c 0)]
private lemma prod_ofFn_apply_eq_zero {V : Type*} [AddCommGroup V] [Module ℂ V] :
    ∀ (m : ℕ) (F : Fin m → Module.End ℂ V) (c : Fin m → ℂ) (v : V) (j : Fin m),
      F j v = 0 → (∀ k, j < k → F k v = c k • v) → (List.ofFn F).prod v = 0
  | 0, _, _, _, j, _, _ => j.elim0
  | m + 1, F, c, v, j, hj, hk => by
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply]
    cases j using Fin.cases with
    | zero =>
      rw [prod_ofFn_apply_of_eigen m (fun i => F i.succ) (fun i => c i.succ) v
        (fun i => hk i.succ (Fin.succ_pos i)), map_smul, hj, smul_zero]
    | succ j' =>
      rw [prod_ofFn_apply_eq_zero m (fun i => F i.succ) (fun i => c i.succ) v j' hj
        (fun i hi => hk i.succ (Fin.succ_lt_succ_iff.mpr hi)), map_zero]
theorem qdet_hw {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (ν : Fin n → ℂ) (v : V)
    (_hE : GlRel E) (hv : IsHW E ν v) (u : ℂ) :
    qdet E u v = (∏ k : Fin n, (u - (k : ℂ) + ν k)) • v := by
  obtain ⟨hdiag, hup⟩ := hv
  have hdiag' : ∀ k : Fin n, capelliTm E (u - (k : ℕ)) k k v = (u - (k : ℂ) + ν k) • v := fun k => by
    rw [capelliTm, if_pos rfl, LinearMap.add_apply, Module.algebraMap_end_apply, hdiag k, add_smul]
  have hoff : ∀ j k : Fin n, j < k → capelliTm E (u - (k : ℕ)) j k v = 0 := fun j k hjk => by
    simp [capelliTm, ne_of_lt hjk, hup j k hjk]
  unfold qdet qminor
  rw [LinearMap.sum_apply, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
  · simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, id_eq, Equiv.Perm.one_apply]
    exact prod_ofFn_apply_of_eigen n _ _ v hdiag'
  · intro σ _ hσ
    have hne : (Finset.univ.filter fun k => σ k ≠ k).Nonempty := by
      by_contra hc; apply hσ; refine Equiv.ext fun k => ?_; by_contra hk
      exact hc ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
    set j := (Finset.univ.filter fun k => σ k ≠ k).max' hne
    have hjmove : σ j ≠ j := (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
    have hfix : ∀ k, j < k → σ k = k := fun k hk => by
      by_contra h
      exact (not_lt.mpr (Finset.le_max' (Finset.univ.filter fun k => σ k ≠ k) k
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))) hk
    have hlt : σ j < j := by
      rcases lt_or_gt_of_ne hjmove with h | h
      · exact h
      · exact absurd (σ.injective (hfix (σ j) h)) hjmove
    have hP : (List.ofFn fun k : Fin n => capelliTm E (u - (k : ℕ)) (id (σ k)) (id k)).prod v = 0 := by
      simp only [id_eq]
      apply prod_ofFn_apply_eq_zero n (fun k : Fin n => capelliTm E (u - (k : ℕ)) (σ k) k)
        (fun k => u - (k : ℂ) + ν k) v j (hoff _ _ hlt)
      intro k hk; rw [hfix k hk]; exact hdiag' k
    rw [Module.End.mul_apply, hP, map_zero]
  · intro h; exact absurd (Finset.mem_univ _) h
lemma eq_of_eval_eq_on_gl {n : ℕ} {p : MvPolynomial (Fin n × Fin n) ℂ}
    (hp : ∀ g : GL (Fin n) ℂ, MvPolynomial.eval (fun ab => g ab.1 ab.2) p = 0) : p = 0 := by
  let D : MvPolynomial (Fin n × Fin n) ℂ := (Matrix.of fun i j => MvPolynomial.X (i, j)).det
  have hD : D ≠ 0 := by
    intro h
    have h1 := congrArg (MvPolynomial.eval (fun ab : Fin n × Fin n => if ab.1 = ab.2 then (1 : ℂ) else 0)) h
    rw [map_zero] at h1
    have hmat : ((Matrix.of fun i j => MvPolynomial.X (i, j) : Matrix (Fin n) (Fin n) _).map
        (MvPolynomial.eval (fun ab : Fin n × Fin n => if ab.1 = ab.2 then (1 : ℂ) else 0))) = 1 := by
      ext i j; simp [Matrix.one_apply]
    rw [RingHom.map_det, show (RingHom.mapMatrix _) _ = (1 : Matrix (Fin n) (Fin n) ℂ) from hmat,
      Matrix.det_one] at h1
    exact one_ne_zero h1
  have hmul : p * D = 0 := by
    refine MvPolynomial.funext fun x => ?_
    rw [map_mul, map_zero]
    by_cases hx : IsUnit (Matrix.of fun i j => x (i, j)).det
    · let g : GL (Fin n) ℂ := (Matrix.isUnit_iff_isUnit_det _).2 hx |>.unit
      have hpg : MvPolynomial.eval x p = 0 := by
        rw [show x = fun ab => (g : Matrix (Fin n) (Fin n) ℂ) ab.1 ab.2 from rfl]
        exact hp g
      rw [hpg, zero_mul]
    · have hdet : MvPolynomial.eval x D = 0 := by
        rw [show MvPolynomial.eval x D = (Matrix.of fun i j => x (i, j)).det from by
          rw [RingHom.map_det]; congr 1; ext i j; simp]
        exact Classical.not_not.1 fun h0 => hx (Ne.isUnit h0)
      rw [hdet, mul_zero]
  exact (mul_eq_zero.mp hmul).resolve_right hD

end QuantumDeterminantFoundations

/-! ## Section 3: Weyl Algebra, Polynomial Representations & Highest-Weight Quantum Determinants -/

section WeylAlgebraQuantumDet
open Matrix CapelliCore
/-- Polynomial finite-dimensional `GL_n(ℂ)`-representation `Pre n`. -/
structure Pre (n : ℕ) where
  d : ℕ
  mat : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin d) (Fin d) ℂ
  poly : ∀ i j, ∃ p : MvPolynomial (Fin n × Fin n) ℂ,
    ∀ g, mat g i j = MvPolynomial.eval (fun ab => g ab.1 ab.2) p
variable {n : ℕ}
def Pre.coef (Ξ : Pre n) (i j : Fin Ξ.d) (x : Fin n → Fin n → ℂ) : ℂ := Ξ.mat (Matrix.of x) i j
abbrev oneM (n : ℕ) : Fin n → Fin n → ℂ := Matrix.of.symm 1
def Pre.D (Ξ : Pre n) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ where
  toFun X := Matrix.of fun i j => fderiv ℂ (Ξ.coef i j) (oneM n) (Matrix.of.symm X)
  map_add' X Y := by ext i j; exact map_add (fderiv ℂ (Ξ.coef i j) (oneM n)) X Y
  map_smul' c X := by ext i j; exact map_smul (fderiv ℂ (Ξ.coef i j) (oneM n)) c X
def Pre.E (Ξ : Pre n) (a b : Fin n) : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ := Ξ.D (Matrix.single a b 1)
def Pre.HasWt (Ξ : Pre n) (ν : Fin n → ℂ) : Prop :=
  ∀ u : ℂ, qdet Ξ.E u = (∏ k : Fin n, (u - (k : ℂ) + ν k)) • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)
def Pre.IsTop (Ξ : Pre n) (ν : Fin n → ℕ) (v : Fin Ξ.d → ℂ) : Prop :=
  ∀ b : Matrix (Fin n) (Fin n) ℂ, (∀ i j, j < i → b i j = 0) → Ξ.mat b *ᵥ v = (∏ k, b k k ^ ν k) • v
def Pre.std (n : ℕ) : Pre n where
  d := n
  mat := MonoidHom.id _
  poly i j := ⟨MvPolynomial.X (i, j), fun g => by simp⟩
instance : Inhabited (Pre n) := ⟨Pre.std n⟩
abbrev Pol (n : ℕ) : Type := MvPolynomial (Fin n × Fin n) ℂ
def rtr (g : Matrix (Fin n) (Fin n) ℂ) : Pol n →ₐ[ℂ] Pol n :=
  MvPolynomial.aeval fun ij => ∑ k, MvPolynomial.X (ij.1, k) * MvPolynomial.C (g k ij.2)
def minor (k : Fin n) : Pol n :=
  (Matrix.of fun i j : Fin (k + 1) =>
    (MvPolynomial.X (Fin.castLE k.2 i, Fin.castLE k.2 j) : Pol n)).det
private theorem differentiable_eval_polynomial_entries (n : ℕ) (p : MvPolynomial (Fin n × Fin n) ℂ) :
    Differentiable ℂ (fun x : Fin n → Fin n → ℂ => MvPolynomial.eval (fun ab => x ab.1 ab.2) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.eval_C]; fun_prop
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p ab hp => simp only [map_mul, MvPolynomial.eval_X]; exact hp.mul (by fun_prop)
theorem coefDiff : ∀ (n : ℕ) (Ξ : Pre n) (i j : Fin Ξ.d), Differentiable ℂ (Ξ.coef i j) := by
  intro n Ξ i j
  obtain ⟨p, hp⟩ := Ξ.poly i j
  have h : Ξ.coef i j = fun x : Fin n → Fin n → ℂ => MvPolynomial.eval (fun ab => x ab.1 ab.2) p := by
    funext x; exact hp (Matrix.of x)
  rw [h]; exact differentiable_eval_polynomial_entries n p
theorem commAll :
    ∀ (n : ℕ) (Ξ : Pre n) (Z : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ),
      (∀ y, IsUnit y → Ξ.mat y * Z = Z * Ξ.mat y) → ∀ y, Ξ.mat y * Z = Z * Ξ.mat y := by
  intro n Ξ Z hZ y
  choose P hP using Ξ.poly
  let Q : Fin Ξ.d → Fin Ξ.d → MvPolynomial (Fin n × Fin n) ℂ := fun i j =>
    ∑ l, P i l * MvPolynomial.C (Z l j) - ∑ l, MvPolynomial.C (Z i l) * P l j
  have hent : ∀ (g : Matrix (Fin n) (Fin n) ℂ) i j,
      (Ξ.mat g * Z - Z * Ξ.mat g) i j = MvPolynomial.eval (fun ab => g ab.1 ab.2) (Q i j) := by
    intro g i j; simp [Q, Matrix.mul_apply, hP, map_sum, mul_comm]
  rw [← sub_eq_zero]; ext i j; rw [hent, Matrix.zero_apply]
  have hQ : Q i j = 0 := eq_of_eval_eq_on_gl fun g => by
    rw [← hent, hZ (g : Matrix (Fin n) (Fin n) ℂ) g.isUnit, sub_self, Matrix.zero_apply]
  rw [hQ, map_zero]
theorem curve :
    ∀ (n : ℕ) (Ξ : Pre n) (c : ℂ → Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin n) (Fin n) ℂ),
      c 0 = 1 → (∀ a b, HasDerivAt (fun t => c t a b) (X a b) 0) →
      ∀ i j, HasDerivAt (fun t => Ξ.mat (c t) i j) (Ξ.D X i j) 0 := by
  intro n Ξ c X h0 hd i j
  have hγ : HasDerivAt (fun t => (of.symm (c t) : Fin n → Fin n → ℂ)) (of.symm X) 0 :=
    hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => hd a b
  have hγ0 : (of.symm (c 0) : Fin n → Fin n → ℂ) = oneM n := by rw [h0]
  have hf : HasFDerivAt (Ξ.coef i j) (fderiv ℂ (Ξ.coef i j) (oneM n))
      ((fun t => (of.symm (c t) : Fin n → Fin n → ℂ)) 0) := by
    show HasFDerivAt (Ξ.coef i j) (fderiv ℂ (Ξ.coef i j) (oneM n)) (of.symm (c 0))
    rw [hγ0]; exact ((coefDiff n Ξ i j) (oneM n)).hasFDerivAt
  exact hf.comp_hasDerivAt (0 : ℂ) hγ
private theorem pre_coef_differentiableAt {n : ℕ} (Ξ : Pre n) (i j : Fin Ξ.d) (x : Fin n → Fin n → ℂ) :
    DifferentiableAt ℂ (Ξ.coef i j) x :=
  coefDiff n Ξ i j x
private theorem hasDerivAt_pre_mat_one_add_smul {n : ℕ} (Ξ : Pre n) (X : Matrix (Fin n) (Fin n) ℂ)
    (k j : Fin Ξ.d) :
    HasDerivAt (fun t : ℂ => Ξ.mat (of (oneM n + t • of.symm X)) k j) (Ξ.D X k j) 0 := by
  have hc : HasDerivAt (fun t : ℂ => oneM n + t • of.symm X) (of.symm X) 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (of.symm X)).const_add (oneM n)
  have hf := (pre_coef_differentiableAt Ξ k j (oneM n + (0 : ℂ) • of.symm X)).hasFDerivAt.comp_hasDerivAt (0 : ℂ) hc
  simp only [zero_smul, add_zero] at hf
  exact hf
theorem adEq :
    ∀ (n : ℕ) (Ξ : Pre n) (P Z W : Matrix (Fin n) (Fin n) ℂ),
      P * Z = W * P → Ξ.mat P * Ξ.D Z = Ξ.D W * Ξ.mat P := by
  intro n Ξ P Z W h
  have key : ∀ t : ℂ, P * of (oneM n + t • of.symm Z) = of (oneM n + t • of.symm W) * P := by
    intro t; change P * (1 + t • Z) = (1 + t • W) * P
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, h, mul_one, one_mul]
  ext i j
  have hZ : HasDerivAt (fun t : ℂ => (Ξ.mat P * Ξ.mat (of (oneM n + t • of.symm Z))) i j)
      ((Ξ.mat P * Ξ.D Z) i j) 0 := by
    simp only [Matrix.mul_apply]; exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_pre_mat_one_add_smul Ξ Z k j).const_mul _
  have hW : HasDerivAt (fun t : ℂ => (Ξ.mat (of (oneM n + t • of.symm W)) * Ξ.mat P) i j)
      ((Ξ.D W * Ξ.mat P) i j) 0 := by
    simp only [Matrix.mul_apply]; exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_pre_mat_one_add_smul Ξ W i k).mul_const _
  have hfun : (fun t : ℂ => (Ξ.mat P * Ξ.mat (of (oneM n + t • of.symm Z))) i j) =
      fun t : ℂ => (Ξ.mat (of (oneM n + t • of.symm W)) * Ξ.mat P) i j := by
    funext t; rw [← map_mul, ← map_mul, key]
  rw [hfun] at hZ; exact hZ.unique hW
theorem invCurve :
    ∀ (n : ℕ) (a b : Fin n), ∃ P Q : ℂ → Matrix (Fin n) (Fin n) ℂ, P 0 = 1 ∧ Q 0 = 1 ∧
      (∀ t, Q t * P t = 1) ∧ ∀ i j,
        HasDerivAt (fun t => P t i j) (Matrix.single a b (1 : ℂ) i j) 0 ∧
        HasDerivAt (fun t => Q t i j) (-Matrix.single a b (1 : ℂ) i j) 0 := by
  intro n a b
  by_cases hab : a = b
  · subst hab
    set E : Matrix (Fin n) (Fin n) ℂ := Matrix.single a a 1
    have hE : E * E = E := by rw [Matrix.single_mul_single_same, one_mul]
    refine ⟨fun t => 1 + (Complex.exp t - 1) • E, fun t => 1 + (Complex.exp (-t) - 1) • E,
      by simp, by simp, ?_, ?_⟩
    · intro t
      have key : (Complex.exp (-t) - 1) + ((Complex.exp t - 1) + (Complex.exp (-t) - 1) * (Complex.exp t - 1)) = 0 := by
        have h1 : Complex.exp (-t) * Complex.exp t = 1 := by rw [← Complex.exp_add]; simp
        linear_combination h1
      simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, hE]
      rw [add_assoc, ← add_smul, ← add_smul, key, zero_smul, add_zero]
    · intro i j; constructor
      · simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using
          (((Complex.hasDerivAt_exp 0).sub_const 1).mul_const (E i j)).const_add ((1 : Matrix (Fin n) (Fin n) ℂ) i j)
      · have h0 : HasDerivAt (fun t : ℂ => Complex.exp (-t)) (-1) 0 := by simpa using (hasDerivAt_neg (0 : ℂ)).cexp
        simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using
          ((h0.sub_const 1).mul_const (E i j)).const_add ((1 : Matrix (Fin n) (Fin n) ℂ) i j)
  · set E : Matrix (Fin n) (Fin n) ℂ := Matrix.single a b 1
    have hE : E * E = 0 := by simp [E, Ne.symm hab]
    refine ⟨fun t => 1 + t • E, fun t => 1 - t • E, by simp, by simp, ?_, ?_⟩
    · intro t; simp only [sub_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, hE, smul_zero]; abel
    · intro i j; constructor
      · simpa [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using
          ((hasDerivAt_id (0 : ℂ)).mul_const (E i j)).const_add ((1 : Matrix (Fin n) (Fin n) ℂ) i j)
      · simpa [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] using
          ((hasDerivAt_id (0 : ℂ)).mul_const (E i j)).const_sub ((1 : Matrix (Fin n) (Fin n) ℂ) i j)
private theorem hasDerivAt_mul_mul_entry {n : ℕ} (P Q : ℂ → Matrix (Fin n) (Fin n) ℂ)
    (P' Q' Y : Matrix (Fin n) (Fin n) ℂ) (hP : ∀ i j, HasDerivAt (fun t => P t i j) (P' i j) 0)
    (hQ : ∀ i j, HasDerivAt (fun t => Q t i j) (Q' i j) 0) (p q : Fin n) :
    HasDerivAt (fun t => (P t * Y * Q t) p q) ((P' * Y * Q 0 + P 0 * Y * Q') p q) 0 := by
  have h : HasDerivAt (fun t => ∑ m, (∑ l, P t p l * Y l m) * Q t m q)
      (∑ m, ((∑ l, P' p l * Y l m) * Q 0 m q + (∑ l, P 0 p l * Y l m) * Q' m q)) 0 :=
    HasDerivAt.fun_sum fun m _ => (HasDerivAt.fun_sum fun l _ => (hP p l).mul_const (Y l m)).mul (hQ m q)
  have e : (P' * Y * Q 0 + P 0 * Y * Q') p q =
      ∑ m, ((∑ l, P' p l * Y l m) * Q 0 m q + (∑ l, P 0 p l * Y l m) * Q' m q) := by
    rw [Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
    simp only [Matrix.mul_apply]
  have ef : (fun t => (P t * Y * Q t) p q) = fun t => ∑ m, (∑ l, P t p l * Y l m) * Q t m q := by
    funext t; simp only [Matrix.mul_apply]
  rw [e, ef]; exact h
private theorem pre_D_eq_sum_single {n : ℕ} (Ξ : Pre n) (M : Matrix (Fin n) (Fin n) ℂ) (i k : Fin Ξ.d) :
    Ξ.D M i k = ∑ p, ∑ q, M p q * Ξ.D (Matrix.single p q 1) i k := by
  have hM : M = ∑ p, ∑ q, M p q • Matrix.single p q (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single M]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  conv_lhs => rw [hM]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
theorem bracket :
    ∀ (n : ℕ) (Ξ : Pre n) (a b : Fin n) (Y : Matrix (Fin n) (Fin n) ℂ),
      Ξ.E a b * Ξ.D Y - Ξ.D Y * Ξ.E a b = Ξ.D (Matrix.single a b 1 * Y - Y * Matrix.single a b 1) := by
  intro n Ξ a b Y
  obtain ⟨P, Q, hP0, hQ0, hQP, hd⟩ := invCurve n a b
  set s : Matrix (Fin n) (Fin n) ℂ := Matrix.single a b 1
  set c : Matrix (Fin n) (Fin n) ℂ := s * Y - Y * s
  have hE : ∀ t, Ξ.mat (P t) * Ξ.D Y = Ξ.D (P t * Y * Q t) * Ξ.mat (P t) := fun t =>
    adEq n Ξ (P t) Y (P t * Y * Q t) (by rw [Matrix.mul_assoc (P t * Y), hQP t, Matrix.mul_one])
  have hmat := curve n Ξ P s hP0 (fun i j => (hd i j).1)
  have hM : ∀ p q, HasDerivAt (fun t => (P t * Y * Q t) p q) (c p q) 0 := fun p q => by
    have h := hasDerivAt_mul_mul_entry P Q s (-s) Y
      (fun i j => (hd i j).1) (fun i j => by simpa using (hd i j).2) p q
    simpa [hP0, hQ0, c, sub_eq_add_neg, Matrix.mul_neg] using h
  have hdD : ∀ i k, HasDerivAt (fun t => Ξ.D (P t * Y * Q t) i k) (Ξ.D c i k) 0 := by
    intro i k
    have h : HasDerivAt (fun t => ∑ p, ∑ q, (P t * Y * Q t) p q * Ξ.D (Matrix.single p q 1) i k)
        (∑ p, ∑ q, c p q * Ξ.D (Matrix.single p q 1) i k) 0 :=
      HasDerivAt.fun_sum fun p _ => HasDerivAt.fun_sum fun q _ => (hM p q).mul_const _
    rw [pre_D_eq_sum_single Ξ c i k]
    convert h using 1; funext t; exact pre_D_eq_sum_single Ξ _ i k
  ext i j
  have hL : HasDerivAt (fun t => (Ξ.mat (P t) * Ξ.D Y) i j) (∑ k, Ξ.D s i k * Ξ.D Y k j) 0 := by
    simp only [Matrix.mul_apply]; exact HasDerivAt.fun_sum fun k _ => (hmat i k).mul_const _
  have hR : HasDerivAt (fun t => (Ξ.D (P t * Y * Q t) * Ξ.mat (P t)) i j)
      (∑ k, (Ξ.D c i k * Ξ.mat (P 0) k j + Ξ.D (P 0 * Y * Q 0) i k * Ξ.D s k j)) 0 := by
    simp only [Matrix.mul_apply]; exact HasDerivAt.fun_sum fun k _ => (hdD i k).mul (hmat k j)
  have hfun : (fun t => (Ξ.mat (P t) * Ξ.D Y) i j) = fun t => (Ξ.D (P t * Y * Q t) * Ξ.mat (P t)) i j :=
    funext fun t => by rw [hE t]
  rw [hfun] at hL
  have hu := hL.unique hR
  simp only [hP0, hQ0, Matrix.mul_one, Matrix.one_mul, map_one, Finset.sum_add_distrib] at hu
  simp only [Matrix.sub_apply, Pre.E, Matrix.mul_apply]
  rw [hu]; simp [Matrix.one_apply, s]
theorem glRel : ∀ (n : ℕ) (Ξ : Pre n), GlRel Ξ.E := by
  intro n Ξ a b c d
  have h := bracket n Ξ a b (Matrix.single c d 1)
  have h1 : Ξ.D (Matrix.single a b (1 : ℂ) * Matrix.single c d 1) = if b = c then Ξ.E a d else 0 := by
    split_ifs with hbc
    · subst hbc; rw [Matrix.single_mul_single_same, mul_one]; rfl
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ hbc, map_zero]
  have h2 : Ξ.D (Matrix.single c d (1 : ℂ) * Matrix.single a b 1) = if d = a then Ξ.E c b else 0 := by
    split_ifs with hbc
    · subst hbc; rw [Matrix.single_mul_single_same, mul_one]; rfl
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ hbc, map_zero]
  rw [map_sub, h1, h2] at h; exact h
theorem qdetComm :
    ∀ (n : ℕ) (Ξ : Pre n) (u : ℂ) (y : Matrix (Fin n) (Fin n) ℂ),
      IsUnit y → Ξ.mat y * qdet Ξ.E u = qdet Ξ.E u * Ξ.mat y := by
  intro n Ξ u y hy
  obtain ⟨Q, hQ⟩ := hy.exists_left_inv
  have hW : ∀ a b : Fin n, y * Matrix.single a b (1 : ℂ) * Q =
      ∑ c, ∑ d, (y c a * Q b d) • Matrix.single c d (1 : ℂ) := by
    intro a b
    rw [Matrix.matrix_eq_sum_single (y * Matrix.single a b (1 : ℂ) * Q)]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.smul_single]; congr 1; simp [Matrix.mul_apply, Matrix.single_apply, ite_and]
  have h : ∀ a b : Fin n, Ξ.mat y * Ξ.E a b = (∑ c, ∑ d, (y c a * Q b d) • Ξ.E c d) * Ξ.mat y := by
    intro a b
    have h1 := adEq n Ξ y (Matrix.single a b 1) (y * Matrix.single a b (1 : ℂ) * Q)
      (by rw [mul_assoc, hQ, mul_one])
    rw [hW] at h1; simp only [map_sum, map_smul] at h1; exact h1
  rw [qdet_semiconj _ _ _ h u, qdet_conj _ (glRel n Ξ) y Q hQ u]
theorem qdetHW :
    ∀ (n d : ℕ) (E : Fin n → Fin n → Matrix (Fin d) (Fin d) ℂ) (ν : Fin n → ℂ) (v : Fin d → ℂ),
      GlRel E → (∀ a, E a a *ᵥ v = ν a • v) → (∀ a b, a < b → E a b *ᵥ v = 0) →
      ∀ u : ℂ, qdet E u *ᵥ v = (∏ k : Fin n, (u - (k : ℂ) + ν k)) • v := by
  intro n d E ν v hgl h1 h2 u
  let φ : Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] Module.End ℂ (Fin d → ℂ) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℂ ≃ₐ[ℂ] _).toAlgHom
  have hφ : ∀ M w, φ M w = M *ᵥ w := fun M w => Matrix.toLinAlgEquiv'_apply M w
  have hgl' : GlRel (fun a b => φ (E a b)) := fun a b c e => by
    simpa only [map_sub, map_mul, apply_ite φ, map_zero] using congrArg φ (hgl a b c e)
  have hw : IsHW (fun a b => φ (E a b)) ν v :=
    ⟨fun a => (hφ _ _).trans (h1 a), fun a b hab => (hφ _ _).trans (h2 a b hab)⟩
  rw [← hφ, map_qdet]; exact qdet_hw _ ν v hgl' hw u
theorem qdetRect :
    ∀ (n d d' : ℕ) (E : Fin n → Fin n → Matrix (Fin d) (Fin d) ℂ)
      (E' : Fin n → Fin n → Matrix (Fin d') (Fin d') ℂ) (A : Matrix (Fin d) (Fin d') ℂ),
      (∀ a b, E a b * A = A * E' a b) → ∀ u : ℂ, qdet E u * A = A * qdet E' u := by
  intro n d d' E E' A h u
  have hs : ∀ v : ℂ, (algebraMap ℂ (Matrix (Fin d) (Fin d) ℂ) v) * A =
      A * algebraMap ℂ (Matrix (Fin d') (Fin d') ℂ) v := fun v => by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
  have hT : ∀ (v : ℂ) a b, capelliTm E v a b * A = A * capelliTm E' v a b := by
    intro v a b; simp only [capelliTm]; rw [Matrix.add_mul, Matrix.mul_add, h]
    split_ifs
    · rw [hs]
    · rw [Matrix.zero_mul, Matrix.mul_zero]
  have hL : ∀ (m : ℕ) (f : Fin m → Matrix (Fin d) (Fin d) ℂ) (g : Fin m → Matrix (Fin d') (Fin d') ℂ),
      (∀ k, f k * A = A * g k) → (List.ofFn f).prod * A = A * (List.ofFn g).prod := by
    intro m; induction m with
    | zero => intro f g _; simp
    | succ m ih =>
      intro f g hfg
      rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Matrix.mul_assoc,
        ih _ _ (fun k => hfg k.succ), ← Matrix.mul_assoc, hfg 0, Matrix.mul_assoc]
  have hz : ∀ z : ℤ, (z : Matrix (Fin d) (Fin d) ℂ) * A = A * (z : Matrix (Fin d') (Fin d') ℂ) := fun z => by
    rw [← map_intCast (algebraMap ℂ (Matrix (Fin d) (Fin d) ℂ)),
      ← map_intCast (algebraMap ℂ (Matrix (Fin d') (Fin d') ℂ))]; exact hs _
  simp only [qdet, qminor]
  rw [Matrix.sum_mul, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Matrix.mul_assoc, hL _ _ _ (fun k => hT _ _ _), ← Matrix.mul_assoc, hz, Matrix.mul_assoc]
theorem subMat :
    ∀ (G : Type) [Monoid G] (d : ℕ) (ρ : G →* Matrix (Fin d) (Fin d) ℂ)
      (S : Submodule ℂ (Fin d → ℂ)), (∀ y, ∀ v ∈ S, ρ y *ᵥ v ∈ S) →
      ∃ (d' : ℕ) (A : Matrix (Fin d) (Fin d') ℂ) (B : Matrix (Fin d') (Fin d) ℂ)
        (ρ' : G →* Matrix (Fin d') (Fin d') ℂ),
        d' = Module.finrank ℂ S ∧ B * A = 1 ∧ (∀ w, A *ᵥ w ∈ S) ∧
        (∀ y, ρ' y = B * ρ y * A) ∧ ∀ y, ρ y * A = A * ρ' y := by
  intro G _ d ρ S hS
  obtain ⟨T, hT⟩ := Submodule.exists_isCompl S
  let b := Module.finBasis ℂ S
  let P : (Fin d → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℂ S) → ℂ) :=
    b.equivFun.toLinearMap ∘ₗ Submodule.projectionOnto S T hT
  let I : (Fin (Module.finrank ℂ S) → ℂ) →ₗ[ℂ] (Fin d → ℂ) := S.subtype ∘ₗ b.equivFun.symm.toLinearMap
  have hIP : ∀ v, v ∈ S → I (P v) = v := by
    intro v hv
    have e : S.projectionOnto T hT v = ⟨v, hv⟩ := Submodule.projectionOnto_apply_left hT ⟨v, hv⟩
    show ((b.equivFun.symm (b.equivFun (S.projectionOnto T hT v)) : S) : Fin d → ℂ) = v
    rw [e, LinearEquiv.symm_apply_apply]
  have hPI : P ∘ₗ I = LinearMap.id := by
    apply LinearMap.ext; intro w
    have e : S.projectionOnto T hT ((b.equivFun.symm w : S) : Fin d → ℂ) = b.equivFun.symm w :=
      Submodule.projectionOnto_apply_left hT _
    show b.equivFun (S.projectionOnto T hT ((b.equivFun.symm w : S) : Fin d → ℂ)) = w
    rw [e, LinearEquiv.apply_symm_apply]
  let A := LinearMap.toMatrix' I
  let B := LinearMap.toMatrix' P
  have hAw : ∀ w, A *ᵥ w = I w := fun w => LinearMap.toMatrix'_mulVec I w
  have hBw : ∀ v, B *ᵥ v = P v := fun v => LinearMap.toMatrix'_mulVec P v
  have hBA : B * A = 1 := by rw [← LinearMap.toMatrix'_comp, hPI, LinearMap.toMatrix'_id]
  have key : ∀ M : Matrix (Fin d) (Fin (Module.finrank ℂ S)) ℂ, (∀ w, M *ᵥ w ∈ S) → A * (B * M) = M := by
    intro M hM; apply Matrix.toLin'.injective; apply LinearMap.ext; intro w
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hBw, hAw, hIP _ (hM w)]
  have hAS : ∀ w, A *ᵥ w ∈ S := fun w => by rw [hAw]; exact (b.equivFun.symm w).2
  have hcol : ∀ y w, (ρ y * A) *ᵥ w ∈ S := fun y w => by rw [← Matrix.mulVec_mulVec]; exact hS y _ (hAS w)
  let ρ' : G →* Matrix (Fin (Module.finrank ℂ S)) (Fin (Module.finrank ℂ S)) ℂ :=
    { toFun := fun y => B * ρ y * A
      map_one' := by simp only [map_one, Matrix.mul_one, hBA]
      map_mul' := fun x y => by simp only [map_mul, Matrix.mul_assoc]; rw [key _ (hcol y)] }
  refine ⟨_, A, B, ρ', rfl, hBA, hAS, fun y => rfl, fun y => ?_⟩
  show ρ y * A = A * (B * ρ y * A)
  rw [Matrix.mul_assoc B, key _ (hcol y)]
theorem preSub :
    ∀ (n : ℕ) (Ξ : Pre n) (S : Submodule ℂ (Fin Ξ.d → ℂ)), (∀ y, ∀ v ∈ S, Ξ.mat y *ᵥ v ∈ S) →
      ∃ (Ξ' : Pre n) (A : Matrix (Fin Ξ.d) (Fin Ξ'.d) ℂ) (B : Matrix (Fin Ξ'.d) (Fin Ξ.d) ℂ),
        Ξ'.d = Module.finrank ℂ S ∧ B * A = 1 ∧ (∀ w, A *ᵥ w ∈ S) ∧ ∀ X, Ξ.D X * A = A * Ξ'.D X := by
  intro n Ξ S hS
  obtain ⟨d', A, B, ρ', hd, hBA, hA, hρ, hcomm⟩ := subMat (Matrix (Fin n) (Fin n) ℂ) Ξ.d Ξ.mat S hS
  have hpoly : ∀ i j, ∃ p : MvPolynomial (Fin n × Fin n) ℂ, ∀ g,
      ρ' g i j = MvPolynomial.eval (fun ab => g ab.1 ab.2) p := by
    choose p hp using Ξ.poly; intro i j
    refine ⟨∑ l, (∑ k, MvPolynomial.C (B i k) * p k l) * MvPolynomial.C (A l j), fun g => ?_⟩
    rw [hρ]; simp only [Matrix.mul_apply, map_sum, map_mul, MvPolynomial.eval_C, hp]
  let Ξ' : Pre n := ⟨d', ρ', hpoly⟩
  refine ⟨Ξ', A, B, hd, hBA, hA, fun X => ?_⟩
  have h0 : (fun t : ℂ => (1 : Matrix (Fin n) (Fin n) ℂ) + t • X) 0 = 1 := by simp
  have hc : ∀ a b, HasDerivAt (fun t : ℂ => ((1 : Matrix (Fin n) (Fin n) ℂ) + t • X) a b) (X a b) 0 := fun a b => by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (X a b)).const_add ((1 : Matrix (Fin n) (Fin n) ℂ) a b)
  have h1 := curve n Ξ _ X h0 hc
  have h2 := curve n Ξ' _ X h0 hc
  ext i j
  have e1 : HasDerivAt (fun t : ℂ => (Ξ.mat (1 + t • X) * A) i j) ((Ξ.D X * A) i j) 0 := by
    simp only [Matrix.mul_apply]; exact HasDerivAt.fun_sum fun k _ => (h1 i k).mul_const (A k j)
  have e2 : HasDerivAt (fun t : ℂ => (A * ρ' (1 + t • X)) i j) ((A * Ξ'.D X) i j) 0 := by
    simp only [Matrix.mul_apply]; exact HasDerivAt.fun_sum fun k _ => (h2 k j).const_mul (A i k)
  simp only [hcomm] at e1; exact e1.unique e2
theorem irrSub :
    ∀ (G : Type) [Monoid G] (d : ℕ) (ρ : G →* Matrix (Fin d) (Fin d) ℂ), 0 < d →
      ∃ (d' : ℕ) (A : Matrix (Fin d) (Fin d') ℂ) (B : Matrix (Fin d') (Fin d) ℂ)
        (ρ' : G →* Matrix (Fin d') (Fin d') ℂ),
        0 < d' ∧ d' ≤ d ∧ B * A = 1 ∧ (∀ y, ρ' y = B * ρ y * A) ∧ (∀ y, ρ y * A = A * ρ' y) ∧
        ∀ W : Submodule ℂ (Fin d' → ℂ), (∀ y, ∀ v ∈ W, ρ' y *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro G _ d ρ hd
  classical
  have hex : ∃ m, ∃ S : Submodule ℂ (Fin d → ℂ), (∀ y, ∀ v ∈ S, ρ y *ᵥ v ∈ S) ∧ S ≠ ⊥ ∧
      Module.finrank ℂ S = m := by
    refine ⟨_, ⊤, fun y v _ => Submodule.mem_top, fun h => ?_, rfl⟩
    have h1 : Module.finrank ℂ (⊤ : Submodule ℂ (Fin d → ℂ)) = 0 := by rw [h]; exact finrank_bot ℂ (Fin d → ℂ)
    rw [finrank_top, Module.finrank_fin_fun] at h1; omega
  obtain ⟨S, hSinv, hSne, hSrank⟩ := Nat.find_spec hex
  obtain ⟨d', A, B, ρ', hd', hBA, -, hρ', hint⟩ := subMat G d ρ S hSinv
  have hSpos : Module.finrank ℂ S ≠ 0 := fun h => hSne (Submodule.finrank_eq_zero.mp h)
  refine ⟨d', A, B, ρ', by omega, ?_, hBA, hρ', hint, fun W hW => ?_⟩
  · have hle := Submodule.finrank_le S; rw [Module.finrank_fin_fun] at hle; omega
  · by_cases hWb : W = ⊥
    · exact Or.inl hWb
    · right
      have hinj : Function.Injective A.mulVecLin := fun v w h => by
        simpa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hBA] using congrArg (fun u => B *ᵥ u) h
      have hrank : Module.finrank ℂ (W.map A.mulVecLin) = Module.finrank ℂ W :=
        (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj W)).symm
      have hW'inv : ∀ y, ∀ v ∈ W.map A.mulVecLin, ρ y *ᵥ v ∈ W.map A.mulVecLin := by
        rintro y _ ⟨w, hw, rfl⟩
        exact Submodule.mem_map.mpr ⟨ρ' y *ᵥ w, hW y w hw, by simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hint]⟩
      have hW'ne : W.map A.mulVecLin ≠ ⊥ := fun h => by
        apply hWb; rw [← Submodule.finrank_eq_zero, ← hrank, h]; exact finrank_bot ℂ (Fin d → ℂ)
      have hmin := Nat.find_min' hex ⟨W.map A.mulVecLin, hW'inv, hW'ne, rfl⟩
      apply Submodule.eq_top_of_finrank_eq
      have hle := Submodule.finrank_le W; rw [Module.finrank_fin_fun] at hle ⊢; omega
private theorem top_weight_lie_action (n : ℕ) (Ξ : Pre n) (ν : Fin n → ℕ) (v : Fin Ξ.d → ℂ)
    (h : Ξ.IsTop ν v) (a b : Fin n) (hab : a ≤ b) (f : ℂ → ℂ) (f' : ℂ) (hf : HasDerivAt f f' 0)
    (hfe : ∀ t : ℂ, ∏ k, ((1 : Matrix (Fin n) (Fin n) ℂ) + t • single a b (1 : ℂ)) k k ^ ν k = f t) :
    Ξ.E a b *ᵥ v = f' • v := by
  have hc := curve n Ξ (fun t => 1 + t • single a b (1 : ℂ)) (single a b 1) (by simp) fun i j => by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (single a b (1 : ℂ) i j)).const_add
      ((1 : Matrix (Fin n) (Fin n) ℂ) i j)
  funext i
  have h1 : HasDerivAt (fun t : ℂ => (Ξ.mat (1 + t • single a b (1 : ℂ)) *ᵥ v) i) ((Ξ.E a b *ᵥ v) i) 0 := by
    simp only [Matrix.mulVec, dotProduct]; exact HasDerivAt.fun_sum fun j _ => (hc i j).mul_const (v j)
  have h2 : (fun t : ℂ => (Ξ.mat (1 + t • single a b (1 : ℂ)) *ᵥ v) i) = fun t => f t * v i := by
    funext t
    rw [h _ (fun p q hpq => by
      have : ¬ (a = p ∧ b = q) := by rintro ⟨rfl, rfl⟩; exact absurd hab (not_le.mpr hpq)
      simp [Matrix.one_apply_ne hpq.ne', this]), hfe]
    rfl
  rw [h2] at h1; exact h1.unique (hf.mul_const (v i))
theorem topLie :
    ∀ (n : ℕ) (Ξ : Pre n) (ν : Fin n → ℕ) (v : Fin Ξ.d → ℂ), Ξ.IsTop ν v →
      (∀ a, Ξ.E a a *ᵥ v = (ν a : ℂ) • v) ∧ ∀ a b, a < b → Ξ.E a b *ᵥ v = 0 := by
  intro n Ξ ν v h
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · refine top_weight_lie_action n Ξ ν v h a a le_rfl (fun t => (1 + t) ^ ν a) _
      (by simpa using ((hasDerivAt_id (0 : ℂ)).const_add 1).fun_pow (ν a)) fun t => ?_
    rw [Finset.prod_eq_single a]
    · simp
    · intro k _ hk; simp [hk.symm]
    · simp
  · simpa using top_weight_lie_action n Ξ ν v h a b hab.le (fun _ => 1) 0 (hasDerivAt_const _ _) fun t =>
      Finset.prod_eq_one fun k _ => by
        have : ¬ (a = k ∧ b = k) := by rintro ⟨rfl, rfl⟩; exact lt_irrefl _ hab
        simp [this]
theorem minorDeg : ∀ (n : ℕ) (k : Fin n), minor k ≠ 0 ∧ (minor k).totalDegree ≤ (k : ℕ) + 1 := by
  intro n k; constructor
  · intro h
    have h0 := congrArg (MvPolynomial.eval (fun ab : Fin n × Fin n => if ab.1 = ab.2 then (1 : ℂ) else 0)) h
    rw [minor, RingHom.map_det, map_zero] at h0
    rw [show (RingHom.mapMatrix _) _ = (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) from by
      ext i j; simp [Matrix.one_apply, Fin.castLE_inj]] at h0
    simp at h0
  · rw [minor, Matrix.det_apply]
    refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun σ _ => ?_)
    rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ]
    refine (MvPolynomial.totalDegree_smul_le _ _).trans
      ((MvPolynomial.totalDegree_finsetProd _ _).trans (by simp [MvPolynomial.totalDegree_X]))
private theorem prod_fin_castLE_eq_prod_le {M : Type*} [CommMonoid M] {n : ℕ} (k : Fin n) (f : Fin n → M) :
    ∏ l : Fin ((k : ℕ) + 1), f (Fin.castLE k.isLt l) = ∏ i : Fin n with i ≤ k, f i := by
  apply Finset.prod_bij (fun l _ => Fin.castLE k.isLt l)
  · intro l _; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_iff_val_le_val, Fin.val_castLE]; omega
  · intro a _ b _ h; exact Fin.castLE_injective _ h
  · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_iff_val_le_val] at hi
    exact ⟨⟨i.val, by omega⟩, Finset.mem_univ _, Fin.ext (by simp)⟩
  · intro _ _; rfl
private theorem sum_fin_castLE_eq_sum_le {M : Type*} [AddCommMonoid M] {n : ℕ} (k : Fin n) (f : Fin n → M) :
    ∑ l : Fin ((k : ℕ) + 1), f (Fin.castLE k.isLt l) = ∑ i : Fin n with i ≤ k, f i := by
  apply Finset.sum_bij (fun l _ => Fin.castLE k.isLt l)
  · intro l _; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_iff_val_le_val, Fin.val_castLE]; omega
  · intro a _ b _ h; exact Fin.castLE_injective _ h
  · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_iff_val_le_val] at hi
    exact ⟨⟨i.val, by omega⟩, Finset.mem_univ _, Fin.ext (by simp)⟩
  · intro _ _; rfl
theorem minorRtr :
    ∀ (n : ℕ) (k : Fin n) (b : Matrix (Fin n) (Fin n) ℂ), (∀ i j, j < i → b i j = 0) →
      rtr b (minor k) = (∏ i : Fin n with i ≤ k, b i i) • minor k := by
  intro n k b hb
  have hmat : (rtr b).mapMatrix (Matrix.of fun i j : Fin ((k : ℕ) + 1) =>
        (MvPolynomial.X (Fin.castLE k.isLt i, Fin.castLE k.isLt j) : Pol n)) =
      (Matrix.of fun i j : Fin ((k : ℕ) + 1) =>
        (MvPolynomial.X (Fin.castLE k.isLt i, Fin.castLE k.isLt j) : Pol n)) *
      (Matrix.of fun i j : Fin ((k : ℕ) + 1) => b (Fin.castLE k.isLt i) (Fin.castLE k.isLt j)).map
        (MvPolynomial.C : ℂ →+* Pol n) := by
    refine Matrix.ext fun i j => ?_
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, rtr, MvPolynomial.aeval_X]
    rw [sum_fin_castLE_eq_sum_le k (fun m => MvPolynomial.X (Fin.castLE k.isLt i, m) *
      MvPolynomial.C (b m (Fin.castLE k.isLt j)))]
    symm; apply Finset.sum_filter_of_ne; intro m _ hm; by_contra hmk; apply hm
    rw [hb m (Fin.castLE k.isLt j) (by
      simp only [not_le] at hmk; rw [Fin.lt_def] at hmk ⊢; simp only [Fin.val_castLE]; omega),
      map_zero, mul_zero]
  have hup : (Matrix.of fun i j : Fin ((k : ℕ) + 1) =>
      b (Fin.castLE k.isLt i) (Fin.castLE k.isLt j)).det = ∏ i : Fin n with i ≤ k, b i i := by
    rw [Matrix.det_of_isUpperTriangular, ← prod_fin_castLE_eq_prod_le k (fun i => b i i)]
    · rfl
    · intro i j hij; simp only [Matrix.of_apply]; apply hb; rw [Fin.lt_def] at hij ⊢; simpa using hij
  have hC : ((Matrix.of fun i j : Fin ((k : ℕ) + 1) =>
      b (Fin.castLE k.isLt i) (Fin.castLE k.isLt j)).map (MvPolynomial.C : ℂ →+* Pol n)).det =
      MvPolynomial.C (∏ i : Fin n with i ≤ k, b i i) := by rw [← hup, RingHom.map_det]; rfl
  unfold minor; rw [AlgHom.map_det, hmat, Matrix.det_mul, hC, MvPolynomial.smul_eq_C_mul, mul_comm]
theorem topPol :
    ∀ (n : ℕ) (ν : Fin n → ℕ), Antitone ν → ∀ H : ℕ, (∀ k, ν k ≤ H) →
      ∃ f : Pol n, f ≠ 0 ∧ f.totalDegree ≤ n * H ∧
        ∀ b : Matrix (Fin n) (Fin n) ℂ, (∀ i j, j < i → b i j = 0) → rtr b f = (∏ k, b k k ^ ν k) • f := by
  intro n ν hν H hH
  classical
  have hmem : ∀ (h : ℕ) (hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty) (i : Fin n),
      i ∈ Finset.univ.filter (fun i : Fin n => h < ν i) ↔ i ≤ (Finset.univ.filter (fun i : Fin n => h < ν i)).max' hs := by
    intro h hs i; constructor
    · intro hi; exact Finset.le_max' _ _ hi
    · intro hi; have hm := Finset.max'_mem _ hs; rw [Finset.mem_filter] at hm ⊢
      exact ⟨Finset.mem_univ _, lt_of_lt_of_le hm.2 (hν hi)⟩
  obtain ⟨g, hg1, hg2, hg3⟩ : ∃ g : ℕ → Pol n, (∀ h, g h ≠ 0) ∧ (∀ h, (g h).totalDegree ≤ n) ∧
      ∀ b : Matrix (Fin n) (Fin n) ℂ, (∀ i j, j < i → b i j = 0) → ∀ h,
        rtr b (g h) = (∏ i ∈ Finset.univ.filter (fun i : Fin n => h < ν i), b i i) • g h := by
    refine ⟨fun h => if hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty then
      minor ((Finset.univ.filter (fun i : Fin n => h < ν i)).max' hs) else 1, ?_, ?_, ?_⟩
    · intro h; by_cases hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty
      · simp only [dif_pos hs]; exact (minorDeg n _).1
      · simp only [dif_neg hs]; exact one_ne_zero
    · intro h; by_cases hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty
      · simp only [dif_pos hs]
        have h1 := (minorDeg n ((Finset.univ.filter (fun i : Fin n => h < ν i)).max' hs)).2
        have h2 := ((Finset.univ.filter (fun i : Fin n => h < ν i)).max' hs).isLt; omega
      · simp only [dif_neg hs, MvPolynomial.totalDegree_one]; exact Nat.zero_le _
    · intro b hb h; by_cases hs : (Finset.univ.filter (fun i : Fin n => h < ν i)).Nonempty
      · simp only [dif_pos hs]; rw [minorRtr n _ b hb]; congr 1
        apply Finset.prod_congr _ (fun _ _ => rfl); ext i; rw [hmem h hs i, Finset.mem_filter]; simp
      · simp only [dif_neg hs]; rw [Finset.not_nonempty_iff_eq_empty.mp hs]; simp
  refine ⟨∏ h ∈ Finset.range H, g h, Finset.prod_ne_zero_iff.mpr (fun h _ => hg1 h), ?_, ?_⟩
  · calc (∏ h ∈ Finset.range H, g h).totalDegree ≤ ∑ h ∈ Finset.range H, (g h).totalDegree :=
          MvPolynomial.totalDegree_finsetProd _ _
      _ ≤ ∑ _h ∈ Finset.range H, n := Finset.sum_le_sum (fun h _ => hg2 h)
      _ = n * H := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]
  · intro b hb
    have key : ∏ h ∈ Finset.range H, ∏ i ∈ Finset.univ.filter (fun i : Fin n => h < ν i), b i i =
        ∏ k, b k k ^ ν k := by
      calc ∏ h ∈ Finset.range H, ∏ i ∈ Finset.univ.filter (fun i : Fin n => h < ν i), b i i
          = ∏ h ∈ Finset.range H, ∏ i, (if h < ν i then b i i else 1) :=
            Finset.prod_congr rfl fun h _ => Finset.prod_filter _ _
        _ = ∏ i, ∏ h ∈ Finset.range H, (if h < ν i then b i i else 1) := Finset.prod_comm
        _ = ∏ k, b k k ^ ν k := by
            refine Finset.prod_congr rfl fun i _ => ?_
            rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
            congr 1
            have hf : (Finset.range H).filter (fun h => h < ν i) = Finset.range (ν i) := by
              ext h; simp only [Finset.mem_filter, Finset.mem_range]; have := hH i; omega
            rw [hf, Finset.card_range]
    rw [map_prod, Finset.prod_congr rfl (fun h _ => hg3 b hb h), ← key]
    simp only [Algebra.smul_def, map_prod, Finset.prod_mul_distrib]
theorem rtrMul :
    ∀ (n : ℕ), (∀ f : Pol n, rtr 1 f = f) ∧
      ∀ (g h : Matrix (Fin n) (Fin n) ℂ) (f : Pol n), rtr (g * h) f = rtr g (rtr h f) := by
  intro n; constructor
  · intro f
    have e : (rtr (1 : Matrix (Fin n) (Fin n) ℂ) : Pol n →ₐ[ℂ] Pol n) = AlgHom.id ℂ (Pol n) := by
      apply MvPolynomial.algHom_ext; rintro ⟨i, j⟩; simp [rtr, Matrix.one_apply, mul_ite, Finset.sum_ite_eq']
    rw [e]; rfl
  · intro g h f
    have e : (rtr (g * h) : Pol n →ₐ[ℂ] Pol n) = (rtr g).comp (rtr h) := by
      apply MvPolynomial.algHom_ext; rintro ⟨i, j⟩
      rw [AlgHom.comp_apply]; simp only [rtr, MvPolynomial.aeval_X, map_sum]
      have hx : ∀ x, (MvPolynomial.aeval (fun ij : Fin n × Fin n => ∑ k, MvPolynomial.X (ij.1, k) *
          MvPolynomial.C (g k ij.2)) : Pol n →ₐ[ℂ] Pol n)
          (MvPolynomial.X (i, x) * MvPolynomial.C (h x j)) =
          ∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (g k x * h x j) := fun x => by
        rw [map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Finset.sum_mul]
        simp only [mul_assoc, ← map_mul]
      simp only [hx, Matrix.mul_apply, map_sum, Finset.mul_sum]; rw [Finset.sum_comm]
    rw [e]; rfl
theorem rtrDeg : ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) (f : Pol n), (rtr g f).totalDegree ≤ f.totalDegree := by
  intro n g f
  have hY : ∀ ij : Fin n × Fin n,
      (∑ k, MvPolynomial.X (ij.1, k) * MvPolynomial.C (g k ij.2) : Pol n).totalDegree ≤ 1 := fun ij =>
    (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun k _ =>
      (MvPolynomial.totalDegree_mul _ _).trans (by rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]))
  conv_lhs => rw [MvPolynomial.as_sum f]
  simp only [rtr, map_sum, MvPolynomial.aeval_monomial]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.algebraMap_eq, MvPolynomial.totalDegree_C, zero_add]
  refine le_trans ?_ (MvPolynomial.le_totalDegree hs)
  unfold Finsupp.prod Finsupp.sum
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  calc s i * _ ≤ s i * 1 := Nat.mul_le_mul_left _ (hY i)
    _ = s i := mul_one _
theorem rtrPoly :
    ∀ (n : ℕ) (f : Pol n) (φ : Pol n →ₗ[ℂ] ℂ),
      ∃ p : Pol n, ∀ g : Matrix (Fin n) (Fin n) ℂ, φ (rtr g f) = MvPolynomial.eval (fun ab => g ab.1 ab.2) p := by
  intro n f
  induction f using MvPolynomial.induction_on with
  | C a =>
    intro φ; refine ⟨MvPolynomial.C (φ (MvPolynomial.C a)), fun g => ?_⟩
    have hc := (rtr g).commutes a; rw [MvPolynomial.algebraMap_eq] at hc; rw [hc, MvPolynomial.eval_C]
  | add p q hp hq =>
    intro φ; obtain ⟨p1, h1⟩ := hp φ; obtain ⟨p2, h2⟩ := hq φ
    exact ⟨p1 + p2, fun g => by rw [map_add, map_add, h1, h2, map_add]⟩
  | mul_X p ij hp =>
    intro φ
    choose P hP using fun k : Fin n => hp (φ.comp (LinearMap.mulRight ℂ (MvPolynomial.X (ij.1, k) : Pol n)))
    refine ⟨∑ k, MvPolynomial.X (k, ij.2) * P k, fun g => ?_⟩
    have hX : rtr g (MvPolynomial.X ij : Pol n) =
        ∑ k, (MvPolynomial.X (ij.1, k) : Pol n) * MvPolynomial.C (g k ij.2) := by simp [rtr]
    rw [map_mul, hX, Finset.mul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk := hP k g
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply] at hk
    rw [show rtr g p * ((MvPolynomial.X (ij.1, k) : Pol n) * MvPolynomial.C (g k ij.2)) =
        MvPolynomial.C (g k ij.2) * (rtr g p * MvPolynomial.X (ij.1, k)) by ring,
      MvPolynomial.C_mul', map_smul, smul_eq_mul, hk, MvPolynomial.eval_mul, MvPolynomial.eval_X]
theorem polPre :
    ∀ (n N : ℕ), ∃ (Ξ : Pre n) (e : MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ N ≃ₗ[ℂ] (Fin Ξ.d → ℂ)),
      ∀ (g : Matrix (Fin n) (Fin n) ℂ) (f f' : MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ N),
        (f' : Pol n) = rtr g f → Ξ.mat g *ᵥ e f = e f' := by
  intro n N
  let V := MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ N
  have mem : ∀ (g : Matrix (Fin n) (Fin n) ℂ) (f : V), rtr g (f : Pol n) ∈ V := fun g f =>
    (MvPolynomial.mem_restrictTotalDegree _ _ _).2 ((rtrDeg n g f).trans ((MvPolynomial.mem_restrictTotalDegree _ _ _).1 f.2))
  let R : Matrix (Fin n) (Fin n) ℂ → V →ₗ[ℂ] V := fun g =>
    LinearMap.codRestrict V ((rtr g).toLinearMap.comp V.subtype) (mem g)
  have hR : ∀ g (f : V), ((R g f : V) : Pol n) = rtr g (f : Pol n) := fun _ _ => rfl
  let b := Module.finBasis ℂ V
  let M : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
    fun g => LinearMap.toMatrix b b (R g)
  have hR1 : R 1 = LinearMap.id := by ext f; rw [hR, (rtrMul n).1]; rfl
  have hRm : ∀ g h, R (g * h) = R g ∘ₗ R h := fun g h => by ext f; rw [hR, (rtrMul n).2]; rfl
  let mat : Matrix (Fin n) (Fin n) ℂ →* Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
    { toFun := M
      map_one' := by show LinearMap.toMatrix b b (R 1) = 1; rw [hR1, LinearMap.toMatrix_id]
      map_mul' := fun g h => by
        show LinearMap.toMatrix b b (R (g * h)) = LinearMap.toMatrix b b (R g) * LinearMap.toMatrix b b (R h)
        rw [hRm]; exact LinearMap.toMatrix_comp b b b (R g) (R h) }
  have poly : ∀ i j : Fin (Module.finrank ℂ V), ∃ p : Pol n, ∀ g : Matrix (Fin n) (Fin n) ℂ,
      mat g i j = MvPolynomial.eval (fun ab => g ab.1 ab.2) p := by
    intro i j
    obtain ⟨φ, hφ⟩ := LinearMap.exists_extend (b.coord i)
    obtain ⟨p, hp⟩ := rtrPoly n ((b j : V) : Pol n) φ
    refine ⟨p, fun g => ?_⟩
    rw [← hp]; show LinearMap.toMatrix b b (R g) i j = _
    rw [LinearMap.toMatrix_apply, ← hR, ← b.coord_apply, ← hφ]; rfl
  refine ⟨⟨Module.finrank ℂ V, mat, poly⟩, b.equivFun, fun g f f' hf => ?_⟩
  show LinearMap.toMatrix b b (R g) *ᵥ b.repr f = b.repr f'
  rw [LinearMap.toMatrix_mulVec_repr]; congr 2; exact Subtype.ext (by rw [hR, hf])
theorem degRank :
    ∀ (n N : ℕ), Module.finrank ℂ (MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ N) ≤ (N + 1) ^ (n * n) := by
  intro n N
  change Module.finrank ℂ (MvPolynomial.restrictSupport ℂ
    {m : Fin n × Fin n →₀ ℕ | (m.sum fun _ e => e) ≤ N}) ≤ _
  rw [Module.finrank_eq_nat_card_basis (MvPolynomial.basisRestrictSupport ℂ _)]
  have key : ∀ m : {m : Fin n × Fin n →₀ ℕ | (m.sum fun _ e => e) ≤ N},
      ∀ i, (m : Fin n × Fin n →₀ ℕ) i < N + 1 := fun m i => by
    have h1 := Finsupp.le_degree i (m : Fin n × Fin n →₀ ℕ)
    have h2 : Finsupp.degree (m : Fin n × Fin n →₀ ℕ) = (m : Fin n × Fin n →₀ ℕ).sum fun _ e => e := rfl
    have h3 := m.2; simp only [Set.mem_ofPred_eq] at h3; omega
  calc Nat.card {m : Fin n × Fin n →₀ ℕ | (m.sum fun _ e => e) ≤ N}
      ≤ Nat.card (Fin n × Fin n → Fin (N + 1)) :=
        Nat.card_le_card_of_injective (fun m i => ⟨(m : Fin n × Fin n →₀ ℕ) i, key m i⟩)
          (fun a b h => Subtype.ext (Finsupp.ext fun i => by simpa using congrArg Fin.val (congrFun h i)))
    _ = (N + 1) ^ (n * n) := by simp [Nat.card_eq_fintype_card]
theorem scalar :
    ∀ (n : ℕ) (Ξ : Pre n) (ν : Fin n → ℕ) (v : Fin Ξ.d → ℂ), v ≠ 0 → Ξ.IsTop ν v →
      ∃ Ξ' : Pre n, 0 < Ξ'.d ∧ Ξ'.d ≤ Ξ.d ∧ Ξ'.HasWt fun k => (ν k : ℂ) := by
  intro n Ξ ν v hv htop
  let S : Submodule ℂ (Fin Ξ.d → ℂ) :=
    Submodule.span ℂ (Set.range fun y : Matrix (Fin n) (Fin n) ℂ => Ξ.mat y *ᵥ v)
  have hS : ∀ y, ∀ w ∈ S, Ξ.mat y *ᵥ w ∈ S := by
    intro y w hw
    induction hw using Submodule.span_induction with
    | mem _ hx => obtain ⟨z, rfl⟩ := hx; rw [Matrix.mulVec_mulVec, ← map_mul]; exact Submodule.subset_span ⟨y * z, rfl⟩
    | zero => simp
    | add _ _ _ _ hx hz => rw [Matrix.mulVec_add]; exact S.add_mem hx hz
    | smul a _ _ hx => rw [Matrix.mulVec_smul]; exact S.smul_mem a hx
  have hvS : v ∈ S := by simpa using (Submodule.subset_span ⟨1, rfl⟩ : Ξ.mat 1 *ᵥ v ∈ S)
  obtain ⟨Ξ', A, B, hd, hBA, hA, hD⟩ := preSub n Ξ S hS
  obtain ⟨hdiag, hup⟩ := topLie n Ξ ν v htop
  refine ⟨Ξ', ?_, ?_, fun u => ?_⟩
  · rw [hd]; exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨v, hvS⟩, fun h => hv (congrArg Subtype.val h)⟩
  · rw [hd]; simpa using Submodule.finrank_le S
  · set c : ℂ := ∏ k : Fin n, (u - ((k : ℕ) : ℂ) + (ν k : ℂ))
    have hQv : qdet Ξ.E u *ᵥ v = c • v :=
      qdetHW n Ξ.d Ξ.E (fun k => (ν k : ℂ)) v (glRel n Ξ) hdiag hup u
    have hcomm : ∀ y, Ξ.mat y * qdet Ξ.E u = qdet Ξ.E u * Ξ.mat y :=
      commAll n Ξ _ (fun y hy => qdetComm n Ξ u y hy)
    have hQS : ∀ w ∈ S, qdet Ξ.E u *ᵥ w = c • w := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem _ hx =>
        obtain ⟨y, rfl⟩ := hx
        rw [Matrix.mulVec_mulVec, ← hcomm y, ← Matrix.mulVec_mulVec, hQv, Matrix.mulVec_smul]
      | zero => simp
      | add _ _ _ _ hx hz => rw [Matrix.mulVec_add, hx, hz, smul_add]
      | smul _ _ _ hx => rw [Matrix.mulVec_smul, hx, smul_comm]
    have hR := qdetRect n Ξ.d Ξ'.d Ξ.E Ξ'.E A (fun a b => hD _) u
    have hcA : qdet Ξ.E u * A = c • A := by
      refine Matrix.toLin'.injective (LinearMap.ext fun w => ?_)
      simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hQS _ (hA w), Matrix.smul_mulVec]
    show qdet Ξ'.E u = c • 1
    calc qdet Ξ'.E u = (B * A) * qdet Ξ'.E u := by rw [hBA, Matrix.one_mul]
      _ = B * (qdet Ξ.E u * A) := by rw [Matrix.mul_assoc, hR]
      _ = c • 1 := by rw [hcA, Matrix.mul_smul, hBA]
theorem existsScalar :
    ∀ (n : ℕ) (ν : Fin n → ℕ), Antitone ν → ∀ H : ℕ, (∀ k, ν k ≤ H) →
      ∃ Ξ : Pre n, 0 < Ξ.d ∧ Ξ.d ≤ (n * H + 1) ^ (n * n) ∧ Ξ.HasWt fun k => (ν k : ℂ) := by
  intro n ν hν H hH
  obtain ⟨f, hf0, hdeg, hf⟩ := topPol n ν hν H hH
  obtain ⟨Ξ, e, he⟩ := polPre n (n * H)
  let F : MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ (n * H) :=
    ⟨f, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hdeg⟩
  have hF : F ≠ 0 := fun h => hf0 (congrArg Subtype.val h)
  have hv : e F ≠ 0 := fun h => hF (e.injective (h.trans e.map_zero.symm))
  have htop : Ξ.IsTop ν (e F) := fun b hb => by
    rw [he b F ((∏ k, b k k ^ ν k) • F) (hf b hb).symm, map_smul]
  obtain ⟨Ξ', h0, hle, hw⟩ := scalar n Ξ ν (e F) hv htop
  refine ⟨Ξ', h0, hle.trans ?_, hw⟩
  have h1 := e.finrank_eq
  have h2 := degRank n (n * H)
  rw [h1] at h2; simpa using h2

end WeylAlgebraQuantumDet

/-! ## Section 4: Adelic Smooth Representations & Infinitesimal Character Pullback -/

section InfinitesimalCharacterPullback
open NumberField IsDedekindDomain Topology Matrix MeasureTheory CapelliCore
open scoped ContDiff

/-! ### 4.1 Place Transport (`plMap`, `compEquiv`, `finMap`) -/

section PlaceTransport
variable {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F]
def plMap (j : E ≃+* F) (w : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 F) :=
  HeightOneSpectrum.comap ((RingOfIntegers.mapRingEquiv j).symm : 𝓞 F →+* 𝓞 E)
    (RingOfIntegers.mapRingEquiv j).symm.surjective w
omit [NumberField E] [NumberField F] in
theorem mem_plMap (j : E ≃+* F) (w : HeightOneSpectrum (𝓞 E)) (x : 𝓞 E) :
    RingOfIntegers.mapRingEquiv j x ∈ (plMap j w).asIdeal ↔ x ∈ w.asIdeal := by
  unfold plMap; simp [HeightOneSpectrum.comap]
omit [NumberField E] [NumberField F] in
theorem mapRingEquiv_symm_apply (j : E ≃+* F) (x : 𝓞 E) :
    RingOfIntegers.mapRingEquiv j.symm (RingOfIntegers.mapRingEquiv j x) = x := by
  apply RingOfIntegers.ext; simp [RingOfIntegers.mapRingEquiv]
omit [NumberField E] [NumberField F] in
omit [NumberField E] [NumberField F] in
theorem plMap_symm_plMap (j : E ≃+* F) (w : HeightOneSpectrum (𝓞 E)) :
    plMap j.symm (plMap j w) = w := by
  apply HeightOneSpectrum.ext; ext y
  have h := mem_plMap j.symm (plMap j w) (RingOfIntegers.mapRingEquiv j y)
  rw [mapRingEquiv_symm_apply] at h; rw [h, mem_plMap]
omit [NumberField E] [NumberField F] in
theorem plMap_plMap_symm (j : E ≃+* F) (v : HeightOneSpectrum (𝓞 F)) :
    plMap j (plMap j.symm v) = v := by
  have h := plMap_symm_plMap j.symm v; rwa [RingEquiv.symm_symm] at h
omit [NumberField E] [NumberField F] in
theorem plMap_injective (j : E ≃+* F) : Function.Injective (plMap j) := fun a b h => by
  rw [← plMap_symm_plMap j a, h, plMap_symm_plMap]
omit [NumberField E] [NumberField F] in
theorem asIdeal_plMap (j : E ≃+* F) (w : HeightOneSpectrum (𝓞 E)) :
    (plMap j w).asIdeal = w.asIdeal.map (RingOfIntegers.mapRingEquiv j) := by
  ext y; rw [Ideal.mem_map_of_equiv]
  constructor
  · intro hy; refine ⟨(RingOfIntegers.mapRingEquiv j).symm y, ?_, RingEquiv.apply_symm_apply _ _⟩
    rw [← mem_plMap j w, RingEquiv.apply_symm_apply]; exact hy
  · rintro ⟨x, hx, rfl⟩; exact (mem_plMap j w x).2 hx
omit [NumberField E] [NumberField F] in
theorem mem_plMap_pow (j : E ≃+* F) (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (x : 𝓞 E) :
    RingOfIntegers.mapRingEquiv j x ∈ (plMap j w).asIdeal ^ n ↔ x ∈ w.asIdeal ^ n := by
  rw [asIdeal_plMap, ← Ideal.map_pow, Ideal.mem_map_of_equiv]
  exact ⟨fun ⟨_, hy, hxy⟩ => by rwa [(RingOfIntegers.mapRingEquiv j).injective hxy] at hy, fun hx => ⟨x, hx, rfl⟩⟩
private theorem eq_of_forall_le_exp {a b : WithZero (Multiplicative ℤ)} (ha : a ≠ 0) (hb : b ≠ 0)
    (ha1 : a ≤ 1) (hb1 : b ≤ 1) (h : ∀ n : ℕ, a ≤ WithZero.exp (-(n : ℤ)) ↔ b ≤ WithZero.exp (-(n : ℤ))) :
    a = b := by
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, WithZero.exp m = a := ⟨_, WithZero.exp_log ha⟩
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, WithZero.exp k = b := ⟨_, WithZero.exp_log hb⟩
  have hm : m ≤ 0 := by rwa [← WithZero.exp_zero, WithZero.exp_le_exp] at ha1
  have hk : k ≤ 0 := by rwa [← WithZero.exp_zero, WithZero.exp_le_exp] at hb1
  have e1 : (((-m).toNat : ℕ) : ℤ) = -m := Int.toNat_of_nonneg (by omega)
  have e2 : (((-k).toNat : ℕ) : ℤ) = -k := Int.toNat_of_nonneg (by omega)
  have h1 := h (-m).toNat; have h2 := h (-k).toNat
  rw [WithZero.exp_le_exp, WithZero.exp_le_exp, e1] at h1
  rw [WithZero.exp_le_exp, WithZero.exp_le_exp, e2] at h2
  have i1 := h1.1 (by omega); have i2 := h2.2 (by omega)
  congr 1; omega
theorem intValuation_plMap (j : E ≃+* F) (w : HeightOneSpectrum (𝓞 E)) (x : 𝓞 E) :
    (plMap j w).intValuation (RingOfIntegers.mapRingEquiv j x) = w.intValuation x := by
  by_cases hx : x = 0
  · subst hx; simp
  have hx' : RingOfIntegers.mapRingEquiv j x ≠ 0 :=
    (map_ne_zero_iff _ (RingOfIntegers.mapRingEquiv j).injective).2 hx
  refine eq_of_forall_le_exp ((plMap j w).intValuation_ne_zero _ hx') (w.intValuation_ne_zero _ hx)
    ((plMap j w).intValuation_le_one _) (w.intValuation_le_one _) fun n => ?_
  rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem, mem_plMap_pow]
theorem valuation_plMap (j : E ≃+* F) (w : HeightOneSpectrum (𝓞 E)) (x : E) :
    (plMap j w).valuation F (j x) = w.valuation E x := by
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  have key : ∀ c : 𝓞 E, j (algebraMap (𝓞 E) E c) = algebraMap (𝓞 F) F (RingOfIntegers.mapRingEquiv j c) :=
    fun _ => rfl
  rw [map_div₀, key, key, map_div₀, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_plMap, intValuation_plMap]
open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀ in
private theorem continuous_withVal {R S : Type} [Field R] [Field S]
    {v : Valuation R (WithZero (Multiplicative ℤ))} {v' : Valuation S (WithZero (Multiplicative ℤ))}
    (hs : Function.Surjective v) (f : WithVal v →+* WithVal v') (hf : ∀ x, Valued.v (f x) = Valued.v x) :
    Continuous f := by
  refine continuous_of_continuousAt_zero f fun s hs' => ?_
  rw [map_zero] at hs'
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hs'
  obtain ⟨x0, hx0⟩ := hs (embedding (γ : ValueGroup₀ (.ofClass (Valued.v : Valuation (WithVal v') _))))
  have hpos : 0 < embedding (γ : ValueGroup₀ (.ofClass (Valued.v : Valuation (WithVal v') _))) := by
    rw [← map_zero (embedding (f := .ofClass (Valued.v : Valuation (WithVal v') _)))]
    exact embedding_strictMono (Units.zero_lt γ)
  have hx0' : 0 < Valued.v.restrict (WithVal.toVal v x0) := by
    rw [Valuation.restrict_pos_iff, WithVal.valued_toVal, hx0]; exact hpos
  refine Filter.mem_map.mpr (Valued.mem_nhds_zero.mpr ⟨Units.mk0 _ hx0'.ne', fun x hx => hγ ?_⟩)
  have hx1 : Valued.v.restrict x < Valued.v.restrict (WithVal.toVal v x0) := hx
  rw [Valuation.restrict_lt_iff] at hx1
  have e0 : Valued.v (WithVal.toVal v x0) = v x0 := WithVal.valued_toVal _ _
  rw [e0, hx0] at hx1
  show Valued.v.restrict (f x) < (γ : ValueGroup₀ _)
  rw [Valuation.restrict_lt_iff_lt_embedding, hf]; exact hx1
theorem continuous_congrVal (j : E ≃+* F) (w : HeightOneSpectrum (𝓞 E)) :
    Continuous (WithVal.congr (w.valuation E) ((plMap j w).valuation F) j) :=
  continuous_withVal (HeightOneSpectrum.valuation_surjective E w) (WithVal.congr _ _ j).toRingHom fun x => by
    show Valued.v (WithVal.toVal _ (j x.ofVal)) = _
    rw [WithVal.valued_toVal, valuation_plMap, WithVal.apply_ofVal]
theorem continuous_congrVal_symm (j : E ≃+* F) (w : HeightOneSpectrum (𝓞 E)) :
    Continuous (WithVal.congr (w.valuation E) ((plMap j w).valuation F) j).symm :=
  continuous_withVal (HeightOneSpectrum.valuation_surjective F (plMap j w))
    (WithVal.congr (w.valuation E) ((plMap j w).valuation F) j).symm.toRingHom fun x => by
    show Valued.v (WithVal.toVal _ (j.symm x.ofVal)) = _
    rw [WithVal.valued_toVal, ← WithVal.apply_ofVal, ← valuation_plMap j w, RingEquiv.apply_symm_apply]
def compEquiv (j : E ≃+* F) (w : HeightOneSpectrum (𝓞 E)) :
    w.adicCompletion E ≃+* (plMap j w).adicCompletion F :=
  (HeightOneSpectrum.adicCompletion.equiv E w).trans ((UniformSpace.Completion.mapRingEquiv
    (WithVal.congr (w.valuation E) ((plMap j w).valuation F) j) (continuous_congrVal j w)
    (continuous_congrVal_symm j w)).trans (HeightOneSpectrum.adicCompletion.equiv F (plMap j w)).symm)
theorem continuous_compEquiv (j : E ≃+* F) (w : HeightOneSpectrum (𝓞 E)) : Continuous (compEquiv j w) :=
  ((HeightOneSpectrum.adicCompletion.continuous_ofCompletion F (plMap j w)).comp
    (UniformSpace.Completion.continuous_map.comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion E w))).congr fun _ => rfl
theorem continuous_compEquiv_symm (j : E ≃+* F) (w : HeightOneSpectrum (𝓞 E)) :
    Continuous (compEquiv j w).symm :=
  ((HeightOneSpectrum.adicCompletion.continuous_ofCompletion E w).comp
    (UniformSpace.Completion.continuous_map.comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion F (plMap j w)))).congr fun _ => rfl
theorem compEquiv_algebraMap (j : E ≃+* F) (w : HeightOneSpectrum (𝓞 E)) (x : E) :
    compEquiv j w (algebraMap E (w.adicCompletion E) x) = algebraMap F ((plMap j w).adicCompletion F) (j x) := by
  apply HeightOneSpectrum.adicCompletion.ext
  show UniformSpace.Completion.map (WithVal.congr (w.valuation E) ((plMap j w).valuation F) j)
    ((algebraMap E (w.adicCompletion E) x).toCompletion) = _
  rw [HeightOneSpectrum.algebraMap_adicCompletion_toCompletion,
    HeightOneSpectrum.algebraMap_adicCompletion_toCompletion, UniformSpace.Completion.algebraMap_def,
    UniformSpace.Completion.algebraMap_def,
    UniformSpace.Completion.map_coe (uniformContinuous_addMonoidHom_of_continuous (continuous_congrVal j w))]
  rfl
theorem compEquiv_symm_algebraMap (j : E ≃+* F) (w : HeightOneSpectrum (𝓞 E)) (x : E) :
    (compEquiv j w).symm (algebraMap F ((plMap j w).adicCompletion F) (j x)) =
      algebraMap E (w.adicCompletion E) x := by
  rw [← compEquiv_algebraMap, RingEquiv.symm_apply_apply]
theorem absNorm_plMap (j : E ≃+* F) (w : HeightOneSpectrum (𝓞 E)) :
    Ideal.absNorm (plMap j w).asIdeal = Ideal.absNorm w.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv j) (asIdeal_plMap j w)).toEquiv).symm
private theorem toNNReal_congr {a b : NNReal} (ha : a ≠ 0) (hb : b ≠ 0) (h : a = b)
    (z : WithZero (Multiplicative ℤ)) : WithZeroMulInt.toNNReal ha z = WithZeroMulInt.toNNReal hb z := by
  subst h; rfl
theorem norm_compEquiv (j : E ≃+* F) (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    ‖compEquiv j w y‖ = ‖y‖ := by
  have h := (HeightOneSpectrum.denseRange_algebraMap E w).equalizer
    (continuous_norm.comp (continuous_compEquiv j w)) continuous_norm (funext fun x => ?_)
  · exact congrFun h y
  simp only [Function.comp_apply, compEquiv_algebraMap]
  show ‖NumberField.FinitePlace.embedding (plMap j w) (j x)‖ = ‖NumberField.FinitePlace.embedding w x‖
  rw [NumberField.FinitePlace.norm_embedding, NumberField.FinitePlace.norm_embedding,
    HeightOneSpectrum.adicAbv_def, HeightOneSpectrum.adicAbv_def, valuation_plMap]
  congr 1; exact toNNReal_congr _ _ (by rw [absNorm_plMap]) _
theorem valued_le_one_iff (j : E ≃+* F) (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) :
    Valued.v (compEquiv j w y) ≤ 1 ↔ Valued.v y ≤ 1 := by
  have h1 : ‖compEquiv j w y‖ ≤ 1 ↔ Valued.v (compEquiv j w y) ≤ 1 := Valued.toNormedField.norm_le_one_iff
  have h2 : ‖y‖ ≤ 1 ↔ Valued.v y ≤ 1 := Valued.toNormedField.norm_le_one_iff
  rw [← h1, ← h2, norm_compEquiv]
theorem mapsTo_integers (j : E ≃+* F) (v : HeightOneSpectrum (𝓞 F)) :
    Set.MapsTo (compEquiv j.symm v).symm ((plMap j.symm v).adicCompletionIntegers E : Set _)
      (v.adicCompletionIntegers F : Set _) := fun x hx => by
  have h := valued_le_one_iff j.symm v ((compEquiv j.symm v).symm x)
  rw [RingEquiv.apply_symm_apply] at h; exact h.1 hx
def finMap (j : E ≃+* F) : FiniteAdeleRing (𝓞 E) E →+* FiniteAdeleRing (𝓞 F) F :=
  RestrictedProduct.mapAlongRingHom (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletion E)
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (plMap j.symm)
    (plMap_injective j.symm).tendsto_cofinite (fun v => (compEquiv j.symm v).symm.toRingHom)
    (Filter.Eventually.of_forall fun v => mapsTo_integers j v)
theorem continuous_finMap (j : E ≃+* F) : Continuous (finMap j) :=
  RestrictedProduct.mapAlong_continuous (fun w : HeightOneSpectrum (𝓞 E) => w.adicCompletion E)
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F) (plMap j.symm)
    (plMap_injective j.symm).tendsto_cofinite (fun v => (compEquiv j.symm v).symm)
    (Filter.Eventually.of_forall fun v => mapsTo_integers j v)
    fun v => continuous_compEquiv_symm j.symm v

end PlaceTransport

/-! ### 4.2 Concrete Adelic Groups, Smooth Functions, Capelli Algebra & Cuspidal Submodules -/

section ConcreteCuspRep

section Corner
variable {R S T : Type}
def corner [Ring R] [Ring S] (s : R →ₙ+* S) : R →* S where
  toFun x := 1 - s 1 + s x
  map_one' := by simp
  map_mul' x y := by
    have h1 : s 1 * s y = s y := by rw [← map_mul, one_mul]
    have h2 : s x * s 1 = s x := by rw [← map_mul, mul_one]
    have h3 : s 1 * s 1 = s 1 := by rw [← map_mul, mul_one]
    rw [map_mul]; simp only [mul_add, add_mul, sub_mul, mul_sub, one_mul, mul_one, h1, h2, h3]; abel
variable [CommRing R] [CommRing S] [CommRing T] {a : ℕ}
def matN (a : ℕ) (s : R →ₙ+* S) : Matrix (Fin a) (Fin a) R →ₙ+* Matrix (Fin a) (Fin a) S where
  toFun x := x.map s
  map_mul' _ _ := by ext i j; simp [Matrix.mul_apply, map_sum]
  map_zero' := by ext i j; simp
  map_add' _ _ := by ext i j; simp
def cornerGL (a : ℕ) (s : R →ₙ+* S) : GL (Fin a) R →* GL (Fin a) S := Units.map (corner (matN a s))
theorem map_cornerGL_of_zero (s : R →ₙ+* S) (p : S →+* T) (h : ∀ x, p (s x) = 0) (g : GL (Fin a) R) :
    GeneralLinearGroup.map p (cornerGL a s g) = 1 := by
  ext i j
  change p ((1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s (g i j)) = _
  simp [h, Matrix.one_apply, apply_ite p]
theorem map_cornerGL_of_hom (s : R →ₙ+* S) (p : S →+* T) (q : R →+* T) (h : ∀ x, p (s x) = q x)
    (g : GL (Fin a) R) :
    GeneralLinearGroup.map p (cornerGL a s g) = GeneralLinearGroup.map q g := by
  ext i j
  change p ((1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s (g i j)) = q (g i j)
  simp [h, Matrix.one_apply, apply_ite p, apply_ite q]

end Corner
variable (E : Type) [Field E] [NumberField E]
abbrev Ad : Type := AdeleRing (𝓞 E) E
abbrev Af : Type := FiniteAdeleRing (𝓞 E) E
abbrev Cinf : Type := InfinitePlace E → ℂ
abbrev GA (a : ℕ) : Type := GL (Fin a) (Ad E)
abbrev Lie (a : ℕ) : Type := Fin a → Fin a → Cinf E
abbrev Kinf (E : Type) [Field E] (a : ℕ) : Type := Matrix.unitaryGroup (Fin a) (Cinf E)
def pFin : Ad E →+* Af E := RingHom.snd (InfiniteAdeleRing E) (Af E)
def sFin : Af E →ₙ+* Ad E where
  toFun x := ((0, x) : InfiniteAdeleRing E × Af E)
  map_mul' _ _ := Prod.ext (mul_zero _).symm rfl
  map_zero' := rfl
  map_add' _ _ := Prod.ext (add_zero _).symm rfl
def pLoc (w : HeightOneSpectrum (𝓞 E)) : Af E →+* w.adicCompletion E :=
  RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w
open Classical in
def sLoc (w : HeightOneSpectrum (𝓞 E)) : w.adicCompletion E →ₙ+* Af E where
  toFun x := ⟨Pi.single w x, by
    filter_upwards [(Set.finite_singleton w).compl_mem_cofinite] with v hv
    rw [Pi.single_eq_of_ne hv]; exact zero_mem _⟩
  map_mul' x y := Subtype.ext (Pi.single_mul (α := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w x y)
  map_zero' := Subtype.ext (Pi.single_zero (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w)
  map_add' x y := Subtype.ext (Pi.single_add (f := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w x y)
def ratGL (a : ℕ) : GL (Fin a) E →* GA E a := GeneralLinearGroup.map (algebraMap E (Ad E))
def finGL (a : ℕ) : GL (Fin a) (Af E) →* GA E a := cornerGL a (sFin E)
def locGL (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) : GL (Fin a) (w.adicCompletion E) →* GL (Fin a) (Af E) :=
  cornerGL a (sLoc E w)
variable {E} in
theorem pLoc_locGL {a : ℕ} (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (w.adicCompletion E)) :
    GeneralLinearGroup.map (pLoc E w) (locGL E a w g) = g := by
  classical
  rw [locGL, map_cornerGL_of_hom _ _ (RingHom.id _) fun x =>
    Pi.single_eq_same (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w x]; rfl
variable {E} in
theorem pLoc_locGL_of_ne {a : ℕ} {w v : HeightOneSpectrum (𝓞 E)} (h : v ≠ w)
    (g : GL (Fin a) (w.adicCompletion E)) :
    GeneralLinearGroup.map (pLoc E v) (locGL E a w g) = 1 := by
  classical
  exact map_cornerGL_of_zero _ _ (fun x =>
    Pi.single_eq_of_ne (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) h x) g
variable [IsTotallyComplex E]
def infEq : Cinf E ≃+* InfiniteAdeleRing E :=
  RingEquiv.piCongrRight fun w =>
    (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm
omit [NumberField E] in
theorem continuous_infEq : Continuous (infEq E) :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm.continuous.comp
      (continuous_apply w)
def pInf : Ad E →+* Cinf E := (infEq E).symm.toRingHom.comp (RingHom.fst (InfiniteAdeleRing E) (Af E))
def sInf : Cinf E →ₙ+* Ad E where
  toFun x := ((infEq E x, 0) : InfiniteAdeleRing E × Af E)
  map_mul' x y := Prod.ext (map_mul (infEq E) x y) (mul_zero _).symm
  map_zero' := Prod.ext (map_zero (infEq E)) rfl
  map_add' x y := Prod.ext (map_add (infEq E) x y) (add_zero _).symm
def infGL (a : ℕ) : GL (Fin a) (Cinf E) →* GA E a := cornerGL a (sInf E)
variable {E} {a : ℕ}
theorem pInf_algebraMap (x : E) (w : InfinitePlace E) : pInf E (algebraMap E (Ad E) x) w = w.embedding x :=
  InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ x)
theorem ad_ext {x y : Ad E} (h1 : pInf E x = pInf E y) (h2 : pFin E x = pFin E y) : x = y :=
  Prod.ext ((infEq E).symm.injective h1) h2
theorem ga_ext {g h : GA E a} (h1 : GeneralLinearGroup.map (pInf E) g = GeneralLinearGroup.map (pInf E) h)
    (h2 : GeneralLinearGroup.map (pFin E) g = GeneralLinearGroup.map (pFin E) h) : g = h := by
  ext i j
  exact ad_ext (congrArg (fun x : GL (Fin a) (Cinf E) => x i j) h1)
    (congrArg (fun x : GL (Fin a) (Af E) => x i j) h2)
@[simp] theorem pInf_infGL (y : GL (Fin a) (Cinf E)) : GeneralLinearGroup.map (pInf E) (infGL E a y) = y := by
  rw [infGL, map_cornerGL_of_hom _ _ (RingHom.id _) fun x => (infEq E).symm_apply_apply x]; rfl
@[simp] theorem pFin_infGL (y : GL (Fin a) (Cinf E)) : GeneralLinearGroup.map (pFin E) (infGL E a y) = 1 :=
  map_cornerGL_of_zero _ _ (fun _ => rfl) y
@[simp] theorem pInf_finGL (k : GL (Fin a) (Af E)) : GeneralLinearGroup.map (pInf E) (finGL E a k) = 1 :=
  map_cornerGL_of_zero _ _ (fun _ => map_zero (infEq E).symm) k
omit [IsTotallyComplex E] in
@[simp] theorem pFin_finGL (k : GL (Fin a) (Af E)) : GeneralLinearGroup.map (pFin E) (finGL E a k) = k := by
  rw [finGL, map_cornerGL_of_hom _ _ (RingHom.id _) fun _ => rfl]; rfl
theorem infGL_comm (y : GL (Fin a) (Cinf E)) (k : GL (Fin a) (Af E)) :
    infGL E a y * finGL E a k = finGL E a k * infGL E a y :=
  ga_ext (by simp) (by simp)
abbrev toL (x : Matrix (Fin a) (Fin a) (Cinf E)) : Lie E a := Matrix.of.symm x
abbrev oneL (E : Type) [Field E] (a : ℕ) : Lie E a := toL 1
def invSet (E : Type) [Field E] (a : ℕ) : Set (Lie E a) := {x | IsUnit (Matrix.of x)}
omit [IsTotallyComplex E] in
theorem contDiff_det : ContDiff ℝ ∞ fun x : Lie E a => (Matrix.of x).det := by
  simp only [Matrix.det_apply', Matrix.of_apply]
  refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => ?_)
  exact (contDiff_apply ℝ _ i).comp (contDiff_apply ℝ _ (σ i))
omit [IsTotallyComplex E] in
theorem isOpen_invSet : IsOpen (invSet E a) := by
  have : invSet E a = (fun x : Lie E a => (Matrix.of x).det) ⁻¹' {u | IsUnit u} := by
    ext x; exact Matrix.isUnit_iff_isUnit_det _
  rw [this]; exact Units.isOpen.preimage contDiff_det.continuous
omit [NumberField E] [IsTotallyComplex E] in
theorem val_mem_invSet (y : GL (Fin a) (Cinf E)) : (toL y.val) ∈ invSet E a := y.isUnit
open Classical in
def chart (φ : GA E a → ℂ) (g : GA E a) (x : Lie E a) : ℂ :=
  if h : IsUnit (Matrix.of x) then φ (g * infGL E a h.unit) else 0
theorem chart_val (φ : GA E a → ℂ) (g : GA E a) (y : GL (Fin a) (Cinf E)) :
    chart φ g (toL y.val) = φ (g * infGL E a y) := by
  have h : IsUnit (Matrix.of (toL y.val)) := y.isUnit
  have e : h.unit = y := Units.ext h.unit_spec
  rw [chart, dif_pos h, e]
def lmul (y : Lie E a) : Lie E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => toL (Matrix.of y * Matrix.of x)
      map_add' := fun x z => by show toL (Matrix.of y * (Matrix.of x + Matrix.of z)) = _; rw [Matrix.mul_add]; rfl
      map_smul' := fun c x => by show toL (Matrix.of y * (c • Matrix.of x)) = _; rw [Matrix.mul_smul]; rfl }
def rmul (y : Lie E a) : Lie E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => toL (Matrix.of x * Matrix.of y)
      map_add' := fun x z => by show toL ((Matrix.of x + Matrix.of z) * Matrix.of y) = _; rw [Matrix.add_mul]; rfl
      map_smul' := fun c x => by show toL ((c • Matrix.of x) * Matrix.of y) = _; rw [Matrix.smul_mul]; rfl }
theorem chart_mul (φ : GA E a → ℂ) (g : GA E a) (y : GL (Fin a) (Cinf E)) :
    chart φ (g * infGL E a y) = chart φ g ∘ lmul (toL y.val) := by
  funext x
  change chart φ (g * infGL E a y) x = chart φ g (lmul (toL y.val) x)
  unfold chart
  have e : Matrix.of (lmul (toL y.val) x) = y.val * Matrix.of x := rfl
  by_cases hx : IsUnit (Matrix.of x)
  · have hyx : IsUnit (Matrix.of (lmul (toL y.val) x)) := by rw [e]; exact y.isUnit.mul hx
    rw [dif_pos hx, dif_pos hyx, mul_assoc, ← map_mul,
      show y * hx.unit = hyx.unit from Units.ext (by simp [e])]
  · have hyx : ¬ IsUnit (Matrix.of (lmul (toL y.val) x)) := fun h => by
      rw [e] at h; exact hx (by simpa [← mul_assoc] using (y⁻¹).isUnit.mul h)
    rw [dif_neg hx, dif_neg hyx]
variable (E a) in
def Sm : Submodule ℂ (GA E a → ℂ) where
  carrier := {φ | ∀ g, ContDiffOn ℝ ∞ (chart φ g) (invSet E a)}
  add_mem' := fun {φ ψ} h h' g => ((h g).add (h' g)).congr fun x hx => by
    have hx' : IsUnit (Matrix.of x) := hx; simp [chart, hx']
  zero_mem' g := contDiffOn_const.congr (f := fun _ => 0) fun x _ => by simp [chart]
  smul_mem' c φ h g := ((h g).const_smul c).congr fun x _ => by simp [chart]
private theorem rt_mem_Sm (h : GA E a) {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) :
    (fun g => φ (g * h)) ∈ Sm E a := by
  let y : GL (Fin a) (Cinf E) := GeneralLinearGroup.map (pInf E) h
  let k : GL (Fin a) (Af E) := GeneralLinearGroup.map (pFin E) h
  have hga : infGL E a y * finGL E a k = h := ga_ext (by simp [y]) (by simp [k])
  intro g
  have h1 : chart (fun g => φ (g * h)) g = chart φ (g * finGL E a k) ∘ rmul (toL y.val) := by
    funext x
    change chart (fun g => φ (g * h)) g x = chart φ (g * finGL E a k) (rmul (toL y.val) x)
    unfold chart
    have e : Matrix.of (rmul (toL y.val) x) = Matrix.of x * y.val := rfl
    by_cases hx : IsUnit (Matrix.of x)
    · have hxy : IsUnit (Matrix.of (rmul (toL y.val) x)) := by rw [e]; exact hx.mul y.isUnit
      rw [dif_pos hx, dif_pos hxy]
      have hu : hx.unit * y = hxy.unit := Units.ext (by simp [e])
      dsimp only
      rw [← hga, infGL_comm, show g * infGL E a hx.unit * (finGL E a k * infGL E a y) =
        g * finGL E a k * (infGL E a hx.unit * infGL E a y) from by
          rw [mul_assoc g, ← mul_assoc (infGL E a hx.unit), infGL_comm]; simp only [mul_assoc],
        ← map_mul, hu]
    · have hxy : ¬ IsUnit (Matrix.of (rmul (toL y.val) x)) := fun h0 => by
        rw [e] at h0; exact hx (by simpa [mul_assoc] using h0.mul (y⁻¹).isUnit)
      rw [dif_neg hx, dif_neg hxy]
  rw [h1]
  refine (hφ (g * finGL E a k)).comp (rmul (toL y.val)).contDiff.contDiffOn fun x hx => ?_
  exact ((hx : IsUnit (Matrix.of x)).mul y.isUnit : IsUnit (Matrix.of (rmul (toL y.val) x)))
variable (E a) in
def rt : Representation ℂ (GA E a) (Sm E a) where
  toFun h :=
    { toFun := fun φ => ⟨fun g => φ.1 (g * h), rt_mem_Sm h φ.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := LinearMap.ext fun φ => Subtype.ext <| funext fun g => by simp
  map_mul' h₁ h₂ := LinearMap.ext fun φ => Subtype.ext <| funext fun g => by simp [mul_assoc]
@[simp] theorem rt_apply (h g : GA E a) (φ : Sm E a) : (rt E a h φ).1 g = φ.1 (g * h) := rfl
def lieD (X : Lie E a) (φ : GA E a → ℂ) (g : GA E a) : ℂ := fderiv ℝ (chart φ g) (oneL E a) X
theorem contDiffAt_chart {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    ContDiffAt ℝ ∞ (chart φ g) x := (hφ g).contDiffAt (isOpen_invSet.mem_nhds hx)
theorem differentiableAt_chart {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) (g : GA E a) :
    DifferentiableAt ℝ (chart φ g) (oneL E a) := (contDiffAt_chart hφ g isUnit_one).differentiableAt (by simp)
theorem chart_lieD {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) (X : Lie E a) (g : GA E a) {x : Lie E a}
    (hx : x ∈ invSet E a) : chart (lieD X φ) g x = fderiv ℝ (chart φ g) x (rmul X x) := by
  obtain ⟨u, hu⟩ := id hx; have e : x = toL u.val := hu.symm; subst e
  rw [chart_val, lieD, chart_mul]
  have e1 : lmul (toL u.val) (oneL E a) = toL u.val := mul_one u.val
  rw [fderiv_comp _ (by rw [e1]; exact (contDiffAt_chart hφ g hx).differentiableAt (by simp))
    (lmul (toL u.val)).differentiableAt, e1, ContinuousLinearMap.fderiv]; rfl
theorem lieD_mem_Sm (X : Lie E a) {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) : lieD X φ ∈ Sm E a := fun g =>
  (((hφ g).fderiv_of_isOpen isOpen_invSet (by simp)).clm_apply (rmul X).contDiff.contDiffOn).congr
    fun _ hx => chart_lieD hφ X g hx
variable (E a) in
def lie : Lie E a →ₗ[ℝ] Module.End ℂ (Sm E a) where
  toFun X :=
    { toFun := fun φ => ⟨lieD X φ.1, lieD_mem_Sm X φ.2⟩
      map_add' := fun φ ψ => Subtype.ext <| funext fun g => by
        have e : chart (φ.1 + ψ.1) g = chart φ.1 g + chart ψ.1 g := by
          funext x; by_cases h : IsUnit (Matrix.of x) <;> simp [chart, h]
        change fderiv ℝ (chart (φ.1 + ψ.1) g) _ X = _
        rw [e, fderiv_add (differentiableAt_chart φ.2 g) (differentiableAt_chart ψ.2 g)]; rfl
      map_smul' := fun c φ => Subtype.ext <| funext fun g => by
        have e : chart (c • φ.1) g = c • chart φ.1 g := by funext x; simp [chart]
        change fderiv ℝ (chart (c • φ.1) g) _ X = _
        rw [e, fderiv_const_smul (differentiableAt_chart φ.2 g)]; rfl }
  map_add' X Y := LinearMap.ext fun φ => Subtype.ext <| funext fun g => map_add (fderiv ℝ (chart φ.1 g) _) X Y
  map_smul' c X := LinearMap.ext fun φ => Subtype.ext <| funext fun g => map_smul (fderiv ℝ (chart φ.1 g) _) c X
@[simp] theorem lie_apply (X : Lie E a) (φ : Sm E a) (g : GA E a) : (lie E a X φ).1 g = lieD X φ.1 g := rfl
open Classical in
def coord (τ : E →+* ℂ) : Cinf E →+* ℂ :=
  if (InfinitePlace.mk τ).embedding = τ then Pi.evalRingHom (fun _ => ℂ) (InfinitePlace.mk τ)
  else (starRingEnd ℂ).comp (Pi.evalRingHom (fun _ => ℂ) (InfinitePlace.mk τ))
theorem coord_algebraMap (τ : E →+* ℂ) (x : E) : coord τ (pInf E (algebraMap E (Ad E) x)) = τ x := by
  unfold coord
  split_ifs with h
  · exact (pInf_algebraMap x _).trans (by rw [h])
  · have h' := (InfinitePlace.embedding_mk_eq τ).resolve_left h
    change starRingEnd ℂ (pInf E _ _) = _; rw [pInf_algebraMap, h']; simp
open Classical in
def atEmb (τ : E →+* ℂ) (z : ℂ) : Cinf E :=
  Pi.single (InfinitePlace.mk τ) (if (InfinitePlace.mk τ).embedding = τ then z else starRingEnd ℂ z)
omit [NumberField E] [IsTotallyComplex E] in
theorem coord_atEmb (τ : E →+* ℂ) (z : ℂ) : coord τ (atEmb τ z) = z := by
  unfold coord atEmb; split_ifs <;> simp
omit [NumberField E] [IsTotallyComplex E] in
theorem atEmb_eq (τ : E →+* ℂ) (z : ℂ) : atEmb τ z = z.re • atEmb τ 1 + z.im • atEmb τ Complex.I := by
  classical
  unfold atEmb; funext w
  simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul, Pi.single_apply]
  by_cases hw : w = InfinitePlace.mk τ
  · subst hw; by_cases he : (InfinitePlace.mk τ).embedding = τ <;> simp [he, Complex.ext_iff]
  · simp [hw]
variable (E a) in
def lieS (i j : Fin a) : Cinf E →ₗ[ℝ] Module.End ℂ (Sm E a) :=
  (lie E a).comp (Matrix.singleLinearMap ℝ i j : Cinf E →ₗ[ℝ] Matrix (Fin a) (Fin a) (Cinf E))
theorem lieS_apply (i j : Fin a) (x : Cinf E) : lieS E a i j x = lie E a (toL (Matrix.single i j x)) := rfl
def Eop (τ : E →+* ℂ) (i j : Fin a) : Module.End ℂ (Sm E a) :=
  (1 / 2 : ℂ) • (lieS E a i j (atEmb τ 1) - Complex.I • lieS E a i j (atEmb τ Complex.I))
def cap (τ : E →+* ℂ) (u : ℂ) : Module.End ℂ (Sm E a) :=
  qdet (Eop τ) (u + ((a : ℂ) - 1) / 2)
variable (E a) in
def Zalg : Subalgebra ℂ (Module.End ℂ (Sm E a)) := Algebra.adjoin ℂ {z | ∃ τ u, z = cap τ u}
inductive Op (E : Type) [Field E] [NumberField E] (a : ℕ) : Type
  | fin (k : GL (Fin a) (Af E))
  | cpt (k : Kinf E a)
  | lie (X : Lie E a)
variable (E a) in
def finRep : Representation ℂ (GL (Fin a) (Af E)) (Sm E a) := (rt E a).comp (finGL E a)
variable (E a) in
def cptRep : Representation ℂ (Kinf E a) (Sm E a) := (rt E a).comp ((infGL E a).comp Unitary.toUnits)
def act : Op E a → Module.End ℂ (Sm E a)
  | .fin k => finRep E a k
  | .cpt k => cptRep E a k
  | .lie X => lie E a X
def IsStable (V : Submodule ℂ (Sm E a)) : Prop := ∀ o, ∀ φ ∈ V, act o φ ∈ V
def height (y : GL (Fin a) (Cinf E)) : ℝ := 1 + ‖toL y.val‖ + ‖toL (y⁻¹).val‖
omit [IsTotallyComplex E] in
theorem one_le_height (y : GL (Fin a) (Cinf E)) : 1 ≤ height y := by
  unfold height; linarith [norm_nonneg (toL y.val), norm_nonneg (toL (y⁻¹).val)]
structure IsAutForm (φ : Sm E a) : Prop where
  left : ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g
  level : IsOpen {k | finRep E a k φ = φ}
  kfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ))
  zfin : FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a))
  growth : ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ.1 (g * infGL E a y)‖ ≤ C * height y ^ N
abbrev BlockIx (a r : ℕ) : Type := {p : Fin a × Fin a // (p.1 : ℕ) < r ∧ r ≤ (p.2 : ℕ)}
def nilM {R : Type} [Zero R] {r : ℕ} (x : BlockIx a r → R) : Matrix (Fin a) (Fin a) R :=
  Matrix.of fun i j => if h : (i : ℕ) < r ∧ r ≤ (j : ℕ) then x ⟨(i, j), h⟩ else 0
private lemma nilM_mul {R : Type} [Semiring R] {r : ℕ} (x y : BlockIx a r → R) :
    nilM x * nilM y = 0 := by
  ext i j; simp only [Matrix.mul_apply, nilM, Matrix.of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  split_ifs with h1 h2
  · omega
  · simp
  · simp
  · simp
def unip {R : Type} [CommRing R] {r : ℕ} (x : BlockIx a r → R) : GL (Fin a) R :=
  ⟨1 + nilM x, 1 - nilM x,
    by simp [add_mul, mul_sub, nilM_mul],
    by simp [sub_mul, mul_add, nilM_mul]⟩
def ratN (E : Type) [Field E] [NumberField E] (a r : ℕ) : AddSubgroup (BlockIx a r → Ad E) :=
  (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (BlockIx a r)).range
def IsCuspidal (φ : GA E a → ℂ) : Prop :=
  ∀ r : ℕ, 0 < r → r < a → ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)]
    (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure →
    IsAddFundamentalDomain (ratN E a r) 𝓕 μ → ∀ g, ∫ x in 𝓕, φ (unip x * g) ∂μ = 0
def IsCuspForm (φ : Sm E a) : Prop := IsAutForm φ ∧ IsCuspidal φ.1
variable (E a) in
@[ext] structure CuspSub where
  V : Submodule ℂ (Sm E a)
  cusp : ∀ φ ∈ V, IsCuspForm φ
  stable : IsStable V
  ne_bot : V ≠ ⊥
  irred : ∀ W ≤ V, IsStable W → W = ⊥ ∨ W = V

namespace CuspSub
def op (π : CuspSub E a) (o : Op E a) : Module.End ℂ π.V := (act o).restrict (π.stable o)
def Iso (π π' : CuspSub E a) : Prop := ∃ T : π.V ≃ₗ[ℂ] π'.V, ∀ o φ, T (π.op o φ) = π'.op o (T φ)
variable (E a) in
instance setoid : Setoid (CuspSub E a) where
  r := Iso
  iseqv := ⟨fun π => ⟨.refl _ _, fun _ _ => rfl⟩,
    fun ⟨T, h⟩ => ⟨T.symm, fun o φ => T.injective (by rw [h]; simp)⟩,
    fun ⟨T, h⟩ ⟨T', h'⟩ => ⟨T.trans T', fun o φ => by simp [h, h']⟩⟩
def HasInfChar (π : CuspSub E a) (τ : E →+* ℂ) (m : Multiset ℂ) : Prop :=
  Multiset.card m = a ∧ ∀ u, ∀ φ ∈ π.V, cap τ u φ = (m.map (u + ·)).prod • φ
theorem HasInfChar.unique {π : CuspSub E a} {τ : E →+* ℂ} {m m' : Multiset ℂ}
    (h : π.HasInfChar τ m) (h' : π.HasInfChar τ m') : m = m' := by
  obtain ⟨φ, hφ, hne⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  have hpoly : (m.map (fun z => Polynomial.X + Polynomial.C z)).prod =
      (m'.map (fun z => Polynomial.X + Polynomial.C z)).prod := by
    refine Polynomial.funext fun u => ?_
    simp only [Polynomial.eval_multiset_prod, Multiset.map_map, Function.comp_def,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    have h1 := h.2 u φ hφ
    have h2 := h'.2 u φ hφ
    exact smul_left_injective ℂ hne (h1.symm.trans h2)
  have hroots := congrArg Polynomial.roots hpoly
  have hproots : ∀ s : Multiset ℂ, (s.map (fun z => Polynomial.X + Polynomial.C z)).prod.roots = s.map (-·) := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons z s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      have hne0 : (s.map (fun w => Polynomial.X + Polynomial.C w)).prod ≠ 0 := fun h0 => by
        obtain ⟨w, _, hw⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp h0)
        exact Polynomial.X_add_C_ne_zero w hw
      rw [Polynomial.roots_mul (mul_ne_zero (Polynomial.X_add_C_ne_zero z) hne0),
        show Polynomial.X + Polynomial.C z = Polynomial.X - Polynomial.C (-z) by simp [sub_neg_eq_add],
        Polynomial.roots_X_sub_C, ih, Multiset.singleton_add]
  rw [hproots m, hproots m'] at hroots
  have hneg := congrArg (Multiset.map (-·)) hroots
  simpa [Multiset.map_map, Function.comp_def] using hneg
theorem iso_cap {π π' : CuspSub E a} (T : π.V ≃ₗ[ℂ] π'.V)
    (hT : ∀ o φ, T (π.op o φ) = π'.op o (T φ)) (τ : E →+* ℂ) (u : ℂ) (φ : π.V) :
    ∃ h : cap τ u φ.1 ∈ π.V, (T ⟨_, h⟩).1 = cap τ u (T φ).1 := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) :=
    { carrier := {z | ∀ φ : π.V, ∃ h : z φ.1 ∈ π.V, (T ⟨_, h⟩).1 = z (T φ).1}
      mul_mem' := fun {x y} hx hy φ => by
        obtain ⟨h1, e1⟩ := hy φ; obtain ⟨h2, e2⟩ := hx ⟨_, h1⟩
        exact ⟨h2, e2.trans (congrArg x e1)⟩
      add_mem' := fun {x y} hx hy φ => by
        obtain ⟨h1, e1⟩ := hx φ; obtain ⟨h2, e2⟩ := hy φ
        exact ⟨add_mem h1 h2, (congrArg Subtype.val (map_add T ⟨_, h1⟩ ⟨_, h2⟩)).trans (congrArg₂ (· + ·) e1 e2)⟩
      algebraMap_mem' := fun c φ => ⟨π.V.smul_mem c φ.2, congrArg Subtype.val (map_smul T c φ)⟩ }
  have hL : ∀ X, lie E a X ∈ S := fun X φ => ⟨π.stable (.lie X) _ φ.2, congrArg Subtype.val (hT (.lie X) φ)⟩
  have hE : ∀ i j, Eop τ i j ∈ S := fun i j => S.smul_mem (S.sub_mem (hL _) (S.smul_mem (hL _) _)) _
  have : cap τ u ∈ S := S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => by
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine S.add_mem ?_ (hE _ _); split_ifs
    · exact S.algebraMap_mem _
    · exact S.zero_mem)
  exact this φ
theorem Iso.hasInfChar {π π' : CuspSub E a} (h : Iso π π') {τ : E →+* ℂ} {m : Multiset ℂ}
    (hm : π.HasInfChar τ m) : π'.HasInfChar τ m := by
  obtain ⟨T, hT⟩ := h
  refine ⟨hm.1, fun u φ hφ => ?_⟩
  obtain ⟨ψ, hψ⟩ := T.surjective ⟨φ, hφ⟩
  obtain ⟨h1, e⟩ := iso_cap T hT τ u ψ
  have e2 : (⟨_, h1⟩ : π.V) = (m.map (u + ·)).prod • ψ := Subtype.ext (hm.2 u _ ψ.2)
  rw [e2, map_smul, hψ] at e; exact e.symm

end CuspSub
variable (E a) in
def CG : Type := Quotient (CuspSub.setoid E a)

namespace CG
def mk (π : CuspSub E a) : CG E a := Quotient.mk _ π
def HasInfChar (π : CG E a) (τ : E →+* ℂ) (m : Multiset ℂ) : Prop :=
  Quotient.liftOn π (fun π => π.HasInfChar τ m) fun _ _ h =>
    propext ⟨fun x => CuspSub.Iso.hasInfChar h x, fun x => CuspSub.Iso.hasInfChar (Setoid.symm h) x⟩
open Classical in
def infChar (π : CG E a) (τ : E →+* ℂ) : Multiset ℂ :=
  if h : ∃ m, π.HasInfChar τ m then h.choose else Multiset.replicate a 0
theorem HasInfChar.infChar_eq {π : CG E a} {τ : E →+* ℂ} {m : Multiset ℂ} (h : π.HasInfChar τ m) :
    π.infChar τ = m := by
  have h' : ∃ m, π.HasInfChar τ m := ⟨m, h⟩
  rw [infChar, dif_pos h']
  have h2 := h'.choose_spec; generalize h'.choose = m' at h2
  induction π using Quotient.inductionOn
  exact CuspSub.HasInfChar.unique h2 h
def IsRegAlg (π : CG E a) : Prop :=
  ∀ τ, (π.infChar τ).Nodup ∧ ∀ z ∈ π.infChar τ, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2
theorem isRegAlg_iff (π : CG E a) :
    π.IsRegAlg ↔ ∀ τ, (π.infChar τ).Nodup ∧ ∀ z ∈ π.infChar τ, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2 :=
  Iff.rfl

end CG

end ConcreteCuspRep

/-! ### 4.3 Local Integral Groups, Hecke Algebra, Satake Parameters -/

section SatakeDefinitions

section GroupHelpers
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
def fixed (ρ : Representation ℂ G V) (H : Subgroup G) : Submodule ℂ V where
  carrier := {v | ∀ h ∈ H, ρ h v = v}
  add_mem' ha hb h hh := by rw [map_add, ha h hh, hb h hh]
  zero_mem' _ _ := map_zero _
  smul_mem' c _ ha h hh := by rw [map_smul, ha h hh]
theorem mem_fixed {ρ : Representation ℂ G V} {H : Subgroup G} {x : V} :
    x ∈ fixed ρ H ↔ ∀ h ∈ H, ρ h x = x := Iff.rfl
def IsBiInv {k : Type} (K : Subgroup G) (f : G → k) : Prop :=
  ∀ a b : K, ∀ g : G, f ((a : G) * g * b) = f g
def heckeVec (ρ : Representation ℂ G V) (K : Subgroup G) (h : G → ℂ) (x : V) : V :=
  ∑ᶠ c : G ⧸ K, h c.out • ρ c.out x
theorem heckeVec_eq_of_section {ρ : Representation ℂ G V} {K : Subgroup G} {h : G → ℂ} {x : V}
    (hh : IsBiInv K h) (hx : x ∈ fixed ρ K) (s : G ⧸ K → G) (hs : ∀ c, (s c : G ⧸ K) = c) :
    heckeVec ρ K h x = ∑ᶠ c, h (s c) • ρ (s c) x := by
  refine finsum_congr fun c => ?_
  have hk : (c.out)⁻¹ * s c ∈ K := QuotientGroup.eq.1 (c.out_eq'.trans (hs c).symm)
  have e : s c = c.out * ((c.out)⁻¹ * s c) := by group
  have e1 := hh 1 ⟨_, hk⟩ c.out
  simp only [OneMemClass.coe_one, one_mul] at e1
  rw [e, e1, map_mul, Module.End.mul_apply, mem_fixed.1 hx _ hk]
theorem heckeVec_comp_symm {H : Type} [Group H]
    {ρ : Representation ℂ G V} {K : Subgroup G} {x : V}
    (e : G ≃* H) {K' : Subgroup H} (hK : ∀ g, g ∈ K ↔ e g ∈ K') {h' : H → ℂ}
    (hh : IsBiInv K' h') (hx : x ∈ fixed ρ K) :
    heckeVec (ρ.comp e.symm.toMonoidHom) K' h' x = heckeVec ρ K (h' ∘ e) x := by
  let q : G ⧸ K ≃ H ⧸ K' := Quotient.congr e.toEquiv fun a b => by
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply, hK]; simp
  have hx' : x ∈ fixed (ρ.comp e.symm.toMonoidHom) K' :=
    mem_fixed.2 fun k hk => mem_fixed.1 hx _ ((hK _).2 (by simpa using hk))
  rw [heckeVec_eq_of_section hh hx' (fun c => e (q.symm c).out) fun c => by
    change q (Quotient.mk'' (q.symm c).out) = c
    rw [(q.symm c).out_eq', q.apply_symm_apply]]
  rw [← finsum_comp_equiv q]
  simp [heckeVec]
theorem mem_fixed_comp_symm {H : Type} [Group H] {ρ : Representation ℂ G V} {K : Subgroup G} {x : V}
    (e : G ≃* H) {K' : Subgroup H} (hK : ∀ g, g ∈ K ↔ e g ∈ K') :
    x ∈ fixed (ρ.comp e.symm.toMonoidHom) K' ↔ x ∈ fixed ρ K := by
  simp only [mem_fixed]
  exact ⟨fun h k hk => by simpa using h _ ((hK k).1 hk), fun h k hk => h _ ((hK _).2 (by simpa using hk))⟩

end GroupHelpers

section SatakeSetup
open NumberField IsDedekindDomain
def bc {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n]
    (φ : A →+* B) : GL n A →* GL n B := Units.map (RingHom.mapMatrix φ).toMonoidHom
def GLint (n : Type) [Fintype n] [DecidableEq n] {K : Type} [Field K] (O : Subring K) : Subgroup (GL n K) :=
  (bc (n := n) O.subtype).range
theorem mem_GLint_iff {K : Type} [Field K] {m : Type} [Fintype m] [DecidableEq m]
    {O : Subring K} {x : GL m K} :
    x ∈ GLint m O ↔ (∀ i j, x.1 i j ∈ O) ∧ ∀ i j, (x⁻¹).1 i j ∈ O := by
  refine ⟨?_, fun h => ⟨⟨Matrix.of fun i j => ⟨_, h.1 i j⟩, Matrix.of fun i j => ⟨_, h.2 i j⟩, ?_, ?_⟩, rfl⟩⟩
  · rintro ⟨y, rfl⟩; exact ⟨fun i j => (y.1 i j).2, fun i j => ((y⁻¹).1 i j).2⟩
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only; rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]; exact x.mul_inv
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only; rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]; exact x.inv_mul
def diagJ {K : Type} [Field K] (n : ℕ) (ϖ : K) (j : ℕ) : Matrix (Fin n) (Fin n) K :=
  Matrix.diagonal fun i : Fin n => if (i : ℕ) < j then ϖ else 1
def dGL {K : Type} [Field K] (n : ℕ) (ϖ : Kˣ) (j : ℕ) : GL (Fin n) K :=
  ⟨diagJ n (ϖ : K) j, diagJ n ((ϖ⁻¹ : Kˣ) : K) j,
    by rw [diagJ, diagJ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; split_ifs <;> simp,
    by rw [diagJ, diagJ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; split_ifs <;> simp⟩
def Tj (k : Type) [CommRing k] {L : Type} [Field L] (n : ℕ) (O : Subring L) (ϖ : L) (j : ℕ) : GL (Fin n) L → k :=
  Set.indicator {g : GL (Fin n) L | ∃ a ∈ GLint (Fin n) O, ∃ b ∈ GLint (Fin n) O,
    (g : Matrix (Fin n) (Fin n) L) = (a : Matrix (Fin n) (Fin n) L) * diagJ n ϖ j * (b : Matrix (Fin n) (Fin n) L)} 1
open Classical in
theorem Tj_apply {L : Type} [Field L] {n : ℕ} (O : Subring L) (ϖ : Lˣ) (j : ℕ) (g : GL (Fin n) L) :
    Tj ℂ n O (ϖ : L) j g =
      if ∃ a ∈ GLint (Fin n) O, ∃ b ∈ GLint (Fin n) O, g = a * dGL n ϖ j * b then 1 else 0 := by
  simp only [Tj, dGL, Set.indicator_apply, Set.mem_ofPred_eq, Units.ext_iff, Units.val_mul, Pi.one_apply]
open Classical in
theorem isBiInv_Tj {L : Type} [Field L] {n : ℕ} (O : Subring L) (ϖ : L) (j : ℕ) :
    IsBiInv (GLint (Fin n) O) (Tj ℂ n O ϖ j) := by
  intro a b g
  simp only [Tj, Set.indicator_apply, Set.mem_ofPred_eq, Units.val_mul, Pi.one_apply]
  congr 1; refine propext ⟨?_, ?_⟩
  · rintro ⟨a', ha', b', hb', h⟩
    refine ⟨(a : GL (Fin n) L)⁻¹ * a', (GLint (Fin n) O).mul_mem ((GLint (Fin n) O).inv_mem a.2) ha',
      b' * (b : GL (Fin n) L)⁻¹, (GLint (Fin n) O).mul_mem hb' ((GLint (Fin n) O).inv_mem b.2), ?_⟩
    have ha1 : (((a : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
        ((a : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hb1 : ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
        (((b : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc (g : Matrix (Fin n) (Fin n) L)
        = ((((a : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
              ((a : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) * (g : Matrix (Fin n) (Fin n) L) *
            (((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
              (((b : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) := by
          rw [ha1, hb1, Matrix.one_mul, Matrix.mul_one]
      _ = (((a : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
            (((a : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (g : Matrix (Fin n) (Fin n) L) *
              ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) *
            (((b : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
          simp only [Matrix.mul_assoc]
      _ = (((a : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
            ((a' : Matrix (Fin n) (Fin n) L) * diagJ n ϖ j * (b' : Matrix (Fin n) (Fin n) L)) *
            (((b : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
          rw [← h]
      _ = (((a : GL (Fin n) L)⁻¹ * a' : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * diagJ n ϖ j *
            ((b' * (b : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
          simp only [Units.val_mul, Matrix.mul_assoc]
  · rintro ⟨a', ha', b', hb', h⟩
    refine ⟨(a : GL (Fin n) L) * a', (GLint (Fin n) O).mul_mem a.2 ha',
      b' * (b : GL (Fin n) L), (GLint (Fin n) O).mul_mem hb' b.2, ?_⟩
    simp only [Units.val_mul, h, Matrix.mul_assoc]
def Ov (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) : Subring (w.adicCompletion E) :=
  (w.adicCompletionIntegers E).toSubring
def KGL {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) :
    Subgroup (GL (Fin a) (w.adicCompletion E)) := GLint (Fin a) (Ov E w)
def qV (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) : ℕ :=
  Ideal.absNorm w.asIdeal
def IsUnifV (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (ϖ : w.adicCompletion E) : Prop :=
  Valued.v ϖ = WithZero.exp (-1 : ℤ)
def satEig (q n : ℕ) (B : Multiset ℂˣ) (j : ℕ) : ℂ :=
  (q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2) * (B.map fun b : ℂˣ => (b : ℂ)).esymm j
def IsSatVecGL {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {a : ℕ} {V : Type}
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V)
    (x : V) (B : Multiset ℂˣ) : Prop :=
  x ≠ 0 ∧ x ∈ fixed ρ (KGL w a) ∧ B.card = a ∧
    ∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ a,
      heckeVec ρ (KGL w a) (Tj ℂ a (Ov E w) ϖ j) x = satEig (qV E w) a B j • x
theorem IsSatVecGL.mapEquiv {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {a : ℕ}
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V}
    {ρ' : Representation ℂ (GL (Fin a) (w.adicCompletion E)) W}
    {x : V} {B : Multiset ℂˣ} (h : IsSatVecGL w ρ x B) (T : V ≃ₗ[ℂ] W)
    (hT : ∀ g y, T (ρ g y) = ρ' g (T y)) :
    IsSatVecGL w ρ' (T x) B := by
  have h0 : T x ≠ 0 := (map_ne_zero_iff T T.injective).2 h.1
  refine ⟨h0, mem_fixed.2 fun k hk => by rw [← hT, mem_fixed.1 h.2.1 k hk], h.2.2.1, fun ϖ hϖ j hj => ?_⟩
  have h1 := h.2.2.2 ϖ hϖ j hj
  have hmap : T (heckeVec ρ (KGL w a) (Tj ℂ a (Ov E w) ϖ j) x) =
      heckeVec ρ' (KGL w a) (Tj ℂ a (Ov E w) ϖ j) (T x) := by
    unfold heckeVec
    change T.toAddEquiv (∑ᶠ c : GL (Fin a) (w.adicCompletion E) ⧸ KGL w a, Tj ℂ a (Ov E w) ϖ j c.out • ρ c.out x) = _
    rw [T.toAddEquiv.map_finsum]
    refine finsum_congr fun c => by change T _ = _; rw [map_smul, hT]
  rw [← hmap, h1, map_smul]
def HasSatGL {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {a : ℕ} {V : Type}
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V)
    (B : Multiset ℂˣ) : Prop :=
  fixed ρ (KGL w a) ≠ ⊥ ∧ ∀ x ∈ fixed ρ (KGL w a), x ≠ 0 → IsSatVecGL w ρ x B
theorem HasSatGL.exists_vec {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)}
    {a : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V} {B : Multiset ℂˣ}
    (h : HasSatGL w ρ B) : ∃ x, IsSatVecGL w ρ x B := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 h.1
  exact ⟨x, h.2 x hx hx0⟩
def CuspSub.finPart {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    (π : CuspSub E a) : Representation ℂ (GL (Fin a) (Af E)) π.V where
  toFun k := π.op (.fin k)
  map_one' := by
    apply LinearMap.ext; rintro ⟨φ, hφ⟩; apply Subtype.ext
    change act (.fin 1) φ = φ; simp [act, finRep]
  map_mul' k₁ k₂ := by
    apply LinearMap.ext; rintro ⟨φ, hφ⟩; apply Subtype.ext
    change act (.fin (k₁ * k₂)) φ = act (.fin k₁) (act (.fin k₂) φ); simp [act, finRep]
def CuspSub.locRep {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) :
    Representation ℂ (GL (Fin a) (w.adicCompletion E)) π.V :=
  π.finPart.comp (locGL E a w)
def CuspSub.HasSat {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) : Prop :=
  HasSatGL w (π.locRep w) B
theorem CuspSub.Iso.hasSatGL {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    {π π' : CuspSub E a} (h : CuspSub.Iso π π') {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}
    (hs : π.HasSat w B) : π'.HasSat w B := by
  obtain ⟨T, hT⟩ := h
  have hrep : ∀ g x, T (π.locRep w g x) = π'.locRep w g (T x) := fun g x => by
    change T (π.op (.fin (locGL E a w g)) x) = π'.op (.fin (locGL E a w g)) (T x)
    exact hT (.fin (locGL E a w g)) x
  refine ⟨?_, fun y hy hy0 => ?_⟩
  · obtain ⟨x, hx⟩ := hs.exists_vec
    have hx' := hx.mapEquiv T hrep
    exact (Submodule.ne_bot_iff _).2 ⟨_, hx'.2.1, hx'.1⟩
  · obtain ⟨x, rfl⟩ := T.surjective y
    refine (hs.2 x (mem_fixed.2 fun k hk => T.injective ?_) ((map_ne_zero_iff T T.injective).1 hy0)).mapEquiv T hrep
    have := mem_fixed.1 hy k hk; rwa [← hrep] at this
def CG.HasSat {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    (π : CG E a) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) : Prop :=
  Quotient.liftOn π (fun π => π.HasSat w B) fun _ _ h =>
    propext ⟨fun x => CuspSub.Iso.hasSatGL h x, fun x => CuspSub.Iso.hasSatGL (Setoid.symm h) x⟩
theorem CG.hasSat_mk {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) :
    (CG.mk π).HasSat w B ↔ HasSatGL w (π.locRep w) B := Iff.rfl

end SatakeSetup

end SatakeDefinitions

/-! ### 4.4 Infinitesimal Character & Satake Pullback (`HasInfCharPullSub`) -/

section FieldIsoPullback
open NumberField IsDedekindDomain Topology Matrix MeasureTheory CapelliCore
open scoped ContDiff
variable {E F : Type} [Field E] [NumberField E] [IsTotallyComplex E]
  [Field F] [NumberField F] [IsTotallyComplex F] {a : ℕ}
omit [NumberField E] in
theorem coord_conj (τ : E →+* ℂ) (x : Cinf E) :
    coord (ComplexEmbedding.conjugate τ) x = starRingEnd ℂ (coord τ x) := by
  have hne : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
    InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 h))
  unfold coord
  simp only [InfinitePlace.mk_conjugate_eq]
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · rw [if_pos h, if_neg (by rw [InfinitePlace.mk_conjugate_eq, h]; exact hne.symm)]; rfl
  · rw [if_pos (by rw [InfinitePlace.mk_conjugate_eq, h]), if_neg (by rw [h]; exact hne)]; simp
omit [NumberField E] [IsTotallyComplex E] in
theorem coord_embedding (w : InfinitePlace E) (x : Cinf E) : coord w.embedding x = x w := by
  unfold coord; rw [if_pos (by rw [InfinitePlace.mk_embedding])]; simp [InfinitePlace.mk_embedding]
omit [NumberField E] [IsTotallyComplex E] in
theorem coord_smul (τ : E →+* ℂ) (t : ℝ) (x : Cinf E) : coord τ (t • x) = t • coord τ x := by
  unfold coord; split_ifs <;> simp
omit [NumberField E] [IsTotallyComplex E] in
theorem coord_star (τ : E →+* ℂ) (x : Cinf E) : coord τ (star x) = star (coord τ x) := by
  unfold coord; split_ifs <;> simp
omit [IsTotallyComplex E] in
theorem norm_coord_le (τ : E →+* ℂ) (x : Cinf E) : ‖coord τ x‖ ≤ ‖x‖ := by
  unfold coord; split_ifs
  · exact norm_le_pi_norm x _
  · exact (Complex.norm_conj _).trans_le (norm_le_pi_norm x _)
omit [NumberField E] [IsTotallyComplex E] in
theorem coord_atEmb_of_ne {τ τ' : E →+* ℂ} (h : InfinitePlace.mk τ' ≠ InfinitePlace.mk τ) (z : ℂ) :
    coord τ' (atEmb τ z) = 0 := by
  classical
  unfold coord atEmb; split_ifs <;> simp [Pi.single_eq_of_ne h]
variable (j : E ≃+* F)
omit [NumberField E] [IsTotallyComplex E] [NumberField F] [IsTotallyComplex F] in
def cinf : Cinf E →+* Cinf F := RingHom.pi fun u => coord (u.embedding.comp (j : E →+* F))
omit [NumberField E] [NumberField F] [IsTotallyComplex F] in
theorem coord_cinf (τ : F →+* ℂ) (x : Cinf E) : coord τ (cinf j x) = coord (τ.comp (j : E →+* F)) x := by
  have h0 : cinf j x (InfinitePlace.mk τ) = coord ((InfinitePlace.mk τ).embedding.comp (j : E →+* F)) x := rfl
  conv_lhs => unfold coord
  split_ifs with h
  · exact h0.trans (by rw [h])
  · have h' := (InfinitePlace.embedding_mk_eq τ).resolve_left h
    change starRingEnd ℂ (cinf j x _) = _
    rw [h0, h']
    exact (congrArg (starRingEnd ℂ) (coord_conj (τ.comp (j : E →+* F)) x)).trans (starRingEnd_self_apply _)
omit [NumberField E] [NumberField F] [IsTotallyComplex F] in
theorem cinf_cinf (x : Cinf E) : cinf j.symm (cinf j x) = x := by
  funext w; change coord (w.embedding.comp _) _ = _
  rw [coord_cinf, ← coord_embedding w x]; congr 2; ext y; simp
omit [NumberField E] [NumberField F] in
theorem cinf_atEmb (τ : F →+* ℂ) (z : ℂ) : cinf j (atEmb (τ.comp (j : E →+* F)) z) = atEmb τ z := by
  funext u; rw [← coord_embedding u (atEmb τ z)]; change coord (u.embedding.comp _) _ = _
  generalize u.embedding = σ
  by_cases h : InfinitePlace.mk σ = InfinitePlace.mk τ
  · rcases InfinitePlace.mk_eq_iff.1 h.symm with rfl | rfl
    · rw [coord_atEmb, coord_atEmb]
    · rw [coord_conj, coord_atEmb]; exact (coord_conj (τ.comp (j : E →+* F)) _).trans (by rw [coord_atEmb])
  · rw [coord_atEmb_of_ne h, coord_atEmb_of_ne]
    intro h'; apply h; ext y
    simpa [InfinitePlace.apply] using congrArg (fun w : InfinitePlace E => w (j.symm y)) h'
def adm : Ad E →+* Ad F :=
  RingHom.prodMap ((infEq F).toRingHom.comp ((cinf j).comp (infEq E).symm.toRingHom)) (finMap j)
theorem pInf_adm (x : Ad E) : pInf F (adm j x) = cinf j (pInf E x) := (infEq F).symm_apply_apply _
theorem pFin_adm (x : Ad E) : pFin F (adm j x) = finMap j (pFin E x) := rfl
omit [IsTotallyComplex E] [IsTotallyComplex F] in
theorem finMap_algebraMap (k : E) : finMap j (algebraMap E (Af E) k) = algebraMap F (Af F) (j k) :=
  FiniteAdeleRing.ext _ fun v => by
    have h := compEquiv_symm_algebraMap j.symm v (j k)
    rw [RingEquiv.symm_apply_apply] at h; exact h
omit [IsTotallyComplex E] [IsTotallyComplex F] in
theorem finMap_finMap (x : Af E) : finMap j.symm (finMap j x) = x := by
  have key : ∀ (v w : HeightOneSpectrum (𝓞 E)) (_ : w = v) (f : w.adicCompletion E → v.adicCompletion E),
      Continuous f → (∀ k : E, f (algebraMap E _ k) = algebraMap E _ k) → f (pLoc E w x) = pLoc E v x := by
    rintro _ v rfl f hf h
    exact congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf continuous_id (funext h)) _
  refine FiniteAdeleRing.ext _ fun v => key v _ (plMap_symm_plMap j v)
    ((compEquiv j v).symm ∘ (compEquiv j.symm (plMap j v)).symm)
    ((continuous_compEquiv_symm _ _).comp (continuous_compEquiv_symm _ _)) fun k => ?_
  have h := compEquiv_symm_algebraMap j.symm (plMap j v) (j k)
  rw [RingEquiv.symm_apply_apply] at h
  rw [Function.comp_apply, h, compEquiv_symm_algebraMap]
theorem adm_adm (x : Ad E) : adm j.symm (adm j x) = x :=
  ad_ext (by rw [pInf_adm, pInf_adm, cinf_cinf]) (finMap_finMap j _)
theorem adm_algebraMap (k : E) : adm j (algebraMap E (Ad E) k) = algebraMap F (Ad F) (j k) :=
  ad_ext (funext fun u => by rw [pInf_adm, pInf_algebraMap]; exact coord_algebraMap _ k) (finMap_algebraMap j k)
omit [IsTotallyComplex E] [IsTotallyComplex F] in
theorem norm_cinf_le (x : Cinf E) : ‖cinf j x‖ ≤ ‖x‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun _ => norm_coord_le _ x
omit [IsTotallyComplex E] [IsTotallyComplex F] in
variable (a) in
def lieMap : Lie E a →L[ℝ] Lie F a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X i k => cinf j (X i k)
      map_add' := fun _ _ => funext fun _ => funext fun _ => map_add (cinf j) _ _
      map_smul' := fun t _ => funext fun _ => funext fun _ => funext fun _ => coord_smul _ t _ }
omit [IsTotallyComplex E] [IsTotallyComplex F] in
theorem continuous_cinf : Continuous (cinf j) :=
  AddMonoidHomClass.continuous_of_bound (cinf j) 1 fun x => by simpa using norm_cinf_le j x
theorem continuous_adm : Continuous (adm j) := by
  have h : Continuous (infEq E).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)
  exact ((continuous_infEq F).comp ((continuous_cinf j).comp h)).prodMap (continuous_finMap j)
variable (a) in
def gaMap : GA E a →* GA F a := GeneralLinearGroup.map (adm j)
theorem gaMap_gaMap (g : GA E a) : gaMap a j.symm (gaMap a j g) = g :=
  Units.ext (Matrix.ext fun _ _ => adm_adm j _)
theorem pInf_gaMap (g : GA E a) : GeneralLinearGroup.map (pInf F) (gaMap a j g) =
    GeneralLinearGroup.map (cinf j) (GeneralLinearGroup.map (pInf E) g) :=
  Units.ext (Matrix.ext fun _ _ => pInf_adm j _)
theorem pFin_gaMap (g : GA E a) : GeneralLinearGroup.map (pFin F) (gaMap a j g) =
    GeneralLinearGroup.map (finMap j) (GeneralLinearGroup.map (pFin E) g) := rfl
theorem gaMap_infGL (y : GL (Fin a) (Cinf E)) :
    gaMap a j (infGL E a y) = infGL F a (GeneralLinearGroup.map (cinf j) y) :=
  ga_ext (by rw [pInf_gaMap, pInf_infGL, pInf_infGL]) (by rw [pFin_gaMap, pFin_infGL, pFin_infGL, map_one])
theorem gaMap_finGL (k : GL (Fin a) (Af E)) :
    gaMap a j (finGL E a k) = finGL F a (GeneralLinearGroup.map (finMap j) k) :=
  ga_ext (by rw [pInf_gaMap, pInf_finGL, pInf_finGL, map_one]) (by rw [pFin_gaMap, pFin_finGL, pFin_finGL])
theorem gaMap_ratGL (γ : GL (Fin a) E) :
    gaMap a j (ratGL E a γ) = ratGL F a (GeneralLinearGroup.map (j : E →+* F) γ) :=
  Units.ext (Matrix.ext fun _ _ => adm_algebraMap j _)
theorem chart_gaMap (φ : GA F a → ℂ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    chart (fun g => φ (gaMap a j g)) g x = chart φ (gaMap a j g) (lieMap a j x) ∧ lieMap a j x ∈ invSet F a := by
  obtain ⟨u, hu⟩ := id hx; obtain rfl : x = toL u.val := hu.symm
  have e : lieMap a j (toL u.val) = toL (GeneralLinearGroup.map (cinf j) u).val := rfl
  rw [e, chart_val, chart_val, map_mul, gaMap_infGL]; exact ⟨rfl, val_mem_invSet _⟩
theorem gaMap_mem_Sm {φ : GA F a → ℂ} (hφ : φ ∈ Sm F a) : (fun g => φ (gaMap a j g)) ∈ Sm E a := fun g =>
  ((hφ (gaMap a j g)).comp (lieMap a j).contDiff.contDiffOn
    fun _ hx => (chart_gaMap j φ g hx).2).congr fun _ hx => (chart_gaMap j φ g hx).1
variable (a) in
def pull : Sm F a ≃ₗ[ℂ] Sm E a where
  toFun φ := ⟨fun g => φ.1 (gaMap a j g), gaMap_mem_Sm j φ.2⟩
  invFun φ := ⟨fun g => φ.1 (gaMap a j.symm g), gaMap_mem_Sm j.symm φ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv φ := Subtype.ext <| funext fun g => congrArg φ.1 (gaMap_gaMap j.symm g)
  right_inv φ := Subtype.ext <| funext fun g => congrArg φ.1 (gaMap_gaMap j g)
theorem pull_apply (φ : Sm F a) (g : GA E a) : (pull a j φ).1 g = φ.1 (gaMap a j g) := rfl
theorem pull_pull (φ : Sm F a) : pull a j.symm (pull a j φ) = φ := (pull a j).left_inv φ
theorem rt_pull (h : GA E a) (φ : Sm F a) : rt E a h (pull a j φ) = pull a j (rt F a (gaMap a j h) φ) :=
  Subtype.ext <| funext fun g => congrArg φ.1 (map_mul (gaMap a j) g h)
theorem lie_pull (X : Lie E a) (φ : Sm F a) : lie E a X (pull a j φ) = pull a j (lie F a (lieMap a j X) φ) := by
  refine Subtype.ext <| funext fun g => ?_
  have e : chart (pull a j φ).1 g =ᶠ[𝓝 (oneL E a)] chart φ.1 (gaMap a j g) ∘ lieMap a j :=
    Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun x hx => (chart_gaMap j φ.1 g hx).1
  have h1 : lieMap a j (oneL E a) = oneL F a := map_one (cinf j).mapMatrix
  have h2 := HasFDerivAt.comp (oneL E a) (f := lieMap a j)
    (by rw [h1]; exact (differentiableAt_chart φ.2 (gaMap a j g)).hasFDerivAt) (lieMap a j).hasFDerivAt
  change fderiv ℝ _ _ X = fderiv ℝ _ _ _
  rw [e.fderiv_eq, h2.fderiv]; rfl
omit [IsTotallyComplex E] [IsTotallyComplex F] in
def opMap : Op E a → Op F a
  | .fin k => .fin (GeneralLinearGroup.map (finMap j) k)
  | .cpt k => .cpt ⟨(cinf j).mapMatrix k.1, Matrix.mem_unitaryGroup_iff.2 (by
      have e : star ((cinf j).mapMatrix k.1) = (cinf j).mapMatrix (star k.1) :=
        Matrix.ext fun _ _ => funext fun u => (coord_star _ _).symm
      rw [e, ← map_mul, Matrix.mem_unitaryGroup_iff.1 k.2, map_one])⟩
  | .lie X => .lie (lieMap a j X)
theorem act_pull (o : Op E a) (φ : Sm F a) : act o (pull a j φ) = pull a j (act (opMap j o) φ) := by
  cases o with
  | fin k => exact (rt_pull j _ φ).trans (by rw [gaMap_finGL]; rfl)
  | cpt k =>
    refine (rt_pull j (infGL E a (Unitary.toUnits k)) φ).trans ?_
    rw [gaMap_infGL]; exact congrArg (fun y => pull a j (rt F a (infGL F a y) φ)) (Units.ext rfl)
  | lie X => exact lie_pull j X φ
theorem pull_act (o : Op F a) (φ : Sm F a) : pull a j (act o φ) = act (opMap j.symm o) (pull a j φ) := by
  conv_lhs => rw [← pull_pull j φ, act_pull]
  exact pull_pull j.symm _
theorem Eop_pull (τ : F →+* ℂ) (i k : Fin a) (φ : Sm F a) :
    Eop (τ.comp (j : E →+* F)) i k (pull a j φ) = pull a j (Eop τ i k φ) := by
  have h : ∀ z, lieMap a j (toL (Matrix.single i k (atEmb (τ.comp (j : E →+* F)) z))) =
      toL (Matrix.single i k (atEmb τ z)) := fun z => by
    rw [← cinf_atEmb j τ z]; exact Matrix.map_single i k _ (cinf j)
  simp only [Eop, lieS_apply, LinearMap.smul_apply, LinearMap.sub_apply, lie_pull, h, map_smul, map_sub]
theorem cap_pull (τ : F →+* ℂ) (u : ℂ) (φ : Sm F a) :
    cap (τ.comp (j : E →+* F)) u (pull a j φ) = pull a j (cap τ u φ) := by
  let conjHom : Module.End ℂ (Sm F a) →ₐ[ℂ] Module.End ℂ (Sm E a) :=
    { toFun := fun f => (pull a j).toLinearMap ∘ₗ f ∘ₗ (pull a j).symm.toLinearMap
      map_one' := by ext ψ; simp
      map_mul' := fun f g => by ext ψ; simp
      map_zero' := by ext ψ; simp
      map_add' := fun f g => by ext ψ; simp
      commutes' := fun c => by ext ψ; simp }
  have h := map_qdet conjHom (Eop (a := a) τ) (u + ((a : ℂ) - 1) / 2)
  have e : (fun i k => conjHom (Eop τ i k)) = Eop (τ.comp (j : E →+* F)) := by
    funext i k; refine LinearMap.ext fun ψ => ?_
    obtain ⟨ψ, rfl⟩ := (pull a j).surjective ψ
    rw [Eop_pull]; change pull a j (Eop τ i k ((pull a j).symm (pull a j ψ))) = _
    rw [LinearEquiv.symm_apply_apply]
  rw [e] at h
  rw [cap, ← h, cap]
  generalize qdet (Eop (a := a) τ) (u + ((a : ℂ) - 1) / 2) = z
  change pull a j (z ((pull a j).symm (pull a j φ))) = _
  rw [LinearEquiv.symm_apply_apply]
omit [NumberField E] [IsTotallyComplex E] [NumberField F] [IsTotallyComplex F] in
theorem exists_comp (τ : E →+* ℂ) : ∃ σ : F →+* ℂ, σ.comp (j : E →+* F) = τ :=
  ⟨τ.comp (j.symm : F →+* E), RingHom.ext fun x => by simp⟩
theorem Zalg_pull {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    ∃ z' ∈ Zalg F a, ∀ φ, z (pull a j φ) = pull a j (z' φ) := by
  induction hz using Algebra.adjoin_induction with
  | mem _ hx =>
    obtain ⟨τ, u, rfl⟩ := hx; obtain ⟨σ, rfl⟩ := exists_comp j τ
    exact ⟨_, Algebra.subset_adjoin ⟨_, _, rfl⟩, cap_pull j σ u⟩
  | algebraMap c => exact ⟨_, Subalgebra.algebraMap_mem _ c, fun φ => by simp⟩
  | add _ _ _ _ hx hy =>
    obtain ⟨x', h1, h2⟩ := hx; obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' + y', add_mem h1 h3, fun φ => by simp [h2, h4]⟩
  | mul _ _ _ _ hx hy =>
    obtain ⟨x', h1, h2⟩ := hx; obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' * y', mul_mem h1 h3, fun φ => by simp [h2, h4]⟩
omit [IsTotallyComplex E] [IsTotallyComplex F] in
theorem height_le (y : GL (Fin a) (Cinf E)) : height (GeneralLinearGroup.map (cinf j) y) ≤ height y := by
  have h1 : ∀ y : GL (Fin a) (Cinf E), ‖toL (GeneralLinearGroup.map (cinf j) y).val‖ ≤ ‖toL y.val‖ := fun y =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun k =>
      (norm_cinf_le j _).trans ((norm_le_pi_norm _ _).trans (norm_le_pi_norm (toL y.val) _))
  have h3 := h1 y⁻¹; rw [map_inv] at h3; unfold height; linarith [h1 y]
theorem isAutForm_pull {φ : Sm F a} (h : IsAutForm φ) : IsAutForm (pull a j φ) where
  left γ g := by rw [pull_apply, map_mul, gaMap_ratGL, h.left, pull_apply]
  level := by
    have hc : Continuous (GeneralLinearGroup.map (n := Fin a) (finMap j)) :=
      Continuous.units_map _ (continuous_id.matrix_map (continuous_finMap j))
    convert h.level.preimage hc using 1
    ext k; exact (Eq.congr_left (act_pull j (.fin k) φ)).trans (pull a j).injective.eq_iff
  kfin := by
    have := h.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep F a k φ)).map
      (pull a j).toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩; exact ⟨_, Submodule.subset_span ⟨_, rfl⟩, (act_pull j (.cpt k) φ).symm⟩
  zfin := by
    have := h.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm F a) => z φ) ''
      Zalg F a)).map (pull a j).toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩; obtain ⟨z', h1, h2⟩ := Zalg_pull j hz
    exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 φ).symm⟩
  growth g := by
    obtain ⟨C, N, h1⟩ := h.growth (gaMap a j g)
    refine ⟨|C|, N, fun y => ?_⟩
    rw [pull_apply, map_mul, gaMap_infGL]
    have h0 := one_le_height (GeneralLinearGroup.map (cinf j) y)
    exact (h1 _).trans (mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (by linarith) (height_le j y) N)
      (by positivity) (abs_nonneg C))
theorem gaMap_unip {r : ℕ} (x : BlockIx a r → Ad E) : gaMap a j (unip x) = unip fun p => adm j (x p) := by
  ext i k
  change adm j ((1 + nilM x : Matrix (Fin a) (Fin a) (Ad E)) i k) =
    (1 + nilM fun p => adm j (x p) : Matrix (Fin a) (Fin a) (Ad F)) i k
  simp only [nilM, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply, map_add]
  split_ifs <;> simp
theorem mem_ratN {r : ℕ} {x : BlockIx a r → Ad E} (hx : x ∈ ratN E a r) :
    (fun p => adm j (x p)) ∈ ratN F a r := by
  obtain ⟨y, rfl⟩ := hx; exact ⟨fun p => j (y p), funext fun p => (adm_algebraMap j _).symm⟩
theorem isCuspidal_pull {φ : GA F a → ℂ} (hφ : IsCuspidal φ) : IsCuspidal fun g => φ (gaMap a j g) := by
  intro r h0 h1 _ _ μ 𝓕 hμ hF g
  let β : (BlockIx a r → Ad E) ≃ₜ+ (BlockIx a r → Ad F) :=
    { toFun := fun x p => adm j (x p)
      invFun := fun x p => adm j.symm (x p)
      left_inv := fun x => funext fun p => adm_adm j _
      right_inv := fun x => funext fun p => adm_adm j.symm _
      map_add' := fun x y => funext fun p => map_add (adm j) _ _
      continuous_toFun := continuous_pi fun p => (continuous_adm j).comp (continuous_apply p)
      continuous_invFun := continuous_pi fun p => (continuous_adm j.symm).comp (continuous_apply p) }
  let e : ratN F a r ≃ ratN E a r :=
    { toFun := fun y => ⟨β.symm y, mem_ratN j.symm y.2⟩
      invFun := fun x => ⟨β x, mem_ratN j x.2⟩
      left_inv := fun y => Subtype.ext (β.apply_symm_apply y)
      right_inv := fun x => Subtype.ext (β.symm_apply_apply x) }
  borelize (BlockIx a r → Ad F)
  let m := β.toHomeomorph.toMeasurableEquiv
  have h2 := hφ r h0 h1 (μ.map m) (m '' 𝓕) (β.isAddHaarMeasure_map μ)
    (hF.image_of_equiv m.toEquiv (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving e
      fun y x => by change β (β.symm y + x) = y + β x; rw [map_add, β.apply_symm_apply])
    (gaMap a j g)
  rw [m.measurableEmbedding.setIntegral_map, m.injective.preimage_image] at h2
  rw [← h2]; congr 1; funext x; beta_reduce; rw [map_mul, gaMap_unip]; rfl
def pullSub (π : CuspSub F a) : CuspSub E a where
  V := π.V.map (pull a j).toLinearMap
  cusp := by rintro _ ⟨φ, hφ, rfl⟩; exact ⟨isAutForm_pull j (π.cusp φ hφ).1, isCuspidal_pull j (π.cusp φ hφ).2⟩
  stable := by rintro o _ ⟨φ, hφ, rfl⟩; exact ⟨_, π.stable _ φ hφ, (act_pull j o φ).symm⟩
  ne_bot h := π.ne_bot ((Submodule.map_eq_bot_iff (e := pull a j)).1 h)
  irred W hW hs := by
    have h := π.irred (W.comap (pull a j).toLinearMap) (fun φ hφ => by
      obtain ⟨ψ, h1, h2⟩ := hW hφ; rwa [← (pull a j).injective h2]) fun o φ hφ => by
      change pull a j (act o φ) ∈ W; rw [pull_act]; exact hs _ _ hφ
    have e := Submodule.map_comap_eq_of_surjective (f := (pull a j).toLinearMap) (pull a j).surjective W
    exact h.imp (fun h => by rw [← e, h, Submodule.map_bot]) fun h => by rw [← e, h]
theorem hasInfChar_pullSub (π : CuspSub F a) (τ : F →+* ℂ) (m : Multiset ℂ) :
    (pullSub j π).HasInfChar (τ.comp (j : E →+* F)) m ↔ π.HasInfChar τ m := by
  refine and_congr_right fun _ => forall_congr' fun u => ⟨fun h φ hφ => (pull a j).injective ?_, ?_⟩
  · rw [← cap_pull, map_smul]; exact h _ ⟨φ, hφ, rfl⟩
  · rintro h _ ⟨φ, hφ, rfl⟩; change cap _ u (pull a j φ) = _ • pull a j φ
    rw [cap_pull, h φ hφ, map_smul]
theorem isRegAlg_pullSub {π : CuspSub F a} (h : (CG.mk π).IsRegAlg) : (CG.mk (pullSub j π)).IsRegAlg := by
  rw [CG.isRegAlg_iff] at h ⊢
  intro τ; obtain ⟨σ, rfl⟩ := exists_comp j τ
  have e : (CG.mk (pullSub j π)).infChar (σ.comp (j : E →+* F)) = (CG.mk π).infChar σ := by
    by_cases h1 : ∃ m, (CG.mk π).HasInfChar σ m
    · obtain ⟨m, hm⟩ := h1
      rw [hm.infChar_eq]; exact CG.HasInfChar.infChar_eq (π := CG.mk (pullSub j π)) ((hasInfChar_pullSub j π σ m).2 hm)
    · rw [CG.infChar, CG.infChar, dif_neg h1, dif_neg]
      rintro ⟨m, hm⟩; exact h1 ⟨m, (hasInfChar_pullSub j π σ m).1 hm⟩
  rw [e]; exact h σ

section SatPullback

section Doset
variable {K K' : Type} [Field K] [Field K'] (c : K ≃+* K') {O : Subring K} {O' : Subring K'}
  (hO : ∀ x, c x ∈ O' ↔ x ∈ O)
include hO in
theorem mem_iff_mapEquiv (g : GL (Fin a) K) :
    g ∈ GLint (Fin a) O ↔ Units.mapEquiv c.mapMatrix.toMulEquiv g ∈ GLint (Fin a) O' := by
  rw [mem_GLint_iff, mem_GLint_iff]
  exact (and_congr (forall₂_congr fun _ _ => hO _) (forall₂_congr fun _ _ => hO _)).symm
theorem mapEquiv_dGL (ϖ : Kˣ) (i : ℕ) :
    Units.mapEquiv c.mapMatrix.toMulEquiv (dGL a ϖ i) = dGL a (Units.map (c : K →* K') ϖ) i :=
  Units.ext (Matrix.ext fun p q => by
    change c ((dGL a ϖ i).1 p q) = _
    simp only [dGL, diagJ, Matrix.diagonal_apply]; split_ifs <;> simp)
include hO in
theorem Tj_mapEquiv (ϖ : Kˣ) (i : ℕ) (g : GL (Fin a) K) :
    Tj ℂ a O' (c ϖ) i (Units.mapEquiv c.mapMatrix.toMulEquiv g) = Tj ℂ a O ϖ i g := by
  classical
  have hK := mem_iff_mapEquiv (a := a) c hO
  refine (Tj_apply O' (Units.map (c : K →* K') ϖ) i _).trans ?_
  rw [Tj_apply, ← mapEquiv_dGL]
  generalize (Units.mapEquiv c.mapMatrix.toMulEquiv : GL (Fin a) K ≃* GL (Fin a) K') = e at hK ⊢
  refine if_congr ⟨?_, ?_⟩ rfl rfl
  · rintro ⟨x, hx, y, hy, H⟩
    obtain ⟨x, rfl⟩ := e.surjective x; obtain ⟨y, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, e.apply_eq_iff_eq] at H
    exact ⟨x, (hK x).2 hx, y, (hK y).2 hy, H⟩
  · rintro ⟨x, hx, y, hy, H⟩
    exact ⟨_, (hK x).1 hx, _, (hK y).1 hy, by rw [H, map_mul, map_mul]⟩

end Doset
omit [IsTotallyComplex E] [IsTotallyComplex F] in
theorem hasSatGL_of_equiv {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}
    (c : v.adicCompletion F ≃+* w.adicCompletion E) (hc : ∀ x, Valued.v (c x) = Valued.v x)
    (hq : qV E w = qV F v) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin a) (v.adicCompletion F)) V}
    {ρ' : Representation ℂ (GL (Fin a) (w.adicCompletion E)) W}
    (T : V ≃ₗ[ℂ] W) (hT : ∀ g x, ρ' (Units.mapEquiv c.mapMatrix.toMulEquiv g) (T x) = T (ρ g x))
    {B : Multiset ℂˣ} (h : HasSatGL v ρ B) : HasSatGL w ρ' B := by
  set e : GL (Fin a) (v.adicCompletion F) ≃* GL (Fin a) (w.adicCompletion E) := Units.mapEquiv c.mapMatrix.toMulEquiv
  have hO : ∀ x, c x ∈ Ov E w ↔ x ∈ Ov F v := fun x => by
    change Valued.v (c x) ≤ 1 ↔ Valued.v x ≤ 1; rw [hc]
  have hK : ∀ g, g ∈ KGL v a ↔ e g ∈ KGL w a := mem_iff_mapEquiv c hO
  have hTj : ∀ (ϖ : (v.adicCompletion F)ˣ) (i : ℕ) g, Tj ℂ a (Ov E w) (c ϖ) i (e g) = Tj ℂ a (Ov F v) ϖ i g :=
    Tj_mapEquiv c hO
  clear_value e
  have h1 : ∀ x, IsSatVecGL v ρ x B → IsSatVecGL w (ρ.comp e.symm.toMonoidHom) x B := by
    rintro x ⟨h0, hf, hB, hTx⟩
    refine ⟨h0, (mem_fixed_comp_symm e hK).2 hf, hB, fun ϖ' hϖ' i hi => ?_⟩
    obtain ⟨p, rfl⟩ := c.surjective ϖ'
    have hp : IsUnifV F v p := (hc p).symm.trans hϖ'
    obtain ⟨ϖ, rfl⟩ : ∃ ϖ : (v.adicCompletion F)ˣ, (ϖ : v.adicCompletion F) = p :=
      ⟨Units.mk0 p fun e0 => WithZero.exp_ne_zero (by rw [← hp, e0, map_zero]), rfl⟩
    rw [heckeVec_comp_symm e hK (isBiInv_Tj (Ov E w) _ i) hf, hq, ← hTx _ hp i hi]
    congr 1; exact funext (hTj ϖ i)
  have hf : ∀ g y, T ((ρ.comp e.symm.toMonoidHom) g y) = ρ' g (T y) := fun g y => by
    change T (ρ (e.symm g) y) = ρ' g (T y); rw [← hT, MulEquiv.apply_symm_apply]
  have key : ∀ x, IsSatVecGL v ρ x B → IsSatVecGL w ρ' (T x) B := fun x hx =>
    (h1 x hx).mapEquiv T hf
  refine ⟨?_, fun y hy h0 => ?_⟩
  · obtain ⟨x, hx⟩ := h.exists_vec; exact (Submodule.ne_bot_iff _).2 ⟨_, (key x hx).2.1, (key x hx).1⟩
  · obtain ⟨x, rfl⟩ := T.surjective y
    refine key x (h.2 x (mem_fixed.2 fun k hk => T.injective ?_) ((map_ne_zero_iff T T.injective).1 h0))
    have := mem_fixed.1 hy _ ((hK k).1 hk); rwa [hT] at this
open scoped WithZeroTopology in
omit [IsTotallyComplex E] [IsTotallyComplex F] in
theorem valued_compEquiv (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E) :
    Valued.v (compEquiv j w x) = Valued.v x := by
  refine (HeightOneSpectrum.denseRange_algebraMap E w).induction_on
    (p := fun x => Valued.v (compEquiv j w x) = Valued.v x) x
    (isClosed_eq ((Valued.continuous_valuation_of_surjective ((plMap j w).valuedAdicCompletion_surjective F)).comp
      (continuous_compEquiv j w))
      (Valued.continuous_valuation_of_surjective (w.valuedAdicCompletion_surjective E))) fun k => ?_
  rw [compEquiv_algebraMap]
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' _ _).trans
    ((valuation_plMap j w k).trans (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).symm)
omit [IsTotallyComplex E] [IsTotallyComplex F] in
theorem finMap_locGL (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin a) (v.adicCompletion F)) :
    GeneralLinearGroup.map (finMap j)
      (locGL E a (plMap j.symm v) (Units.mapEquiv (compEquiv j.symm v).mapMatrix.toMulEquiv g)) = locGL F a v g := by
  have key : ∀ u (k : GL (Fin a) (Af E)), GeneralLinearGroup.map (pLoc F u) (GeneralLinearGroup.map (finMap j) k) =
      GeneralLinearGroup.map (compEquiv j.symm u).symm.toRingHom
        (GeneralLinearGroup.map (pLoc E (plMap j.symm u)) k) := fun _ _ => rfl
  have key2 : ∀ u, GeneralLinearGroup.map (pLoc F u) (GeneralLinearGroup.map (finMap j)
      (locGL E a (plMap j.symm v) (Units.mapEquiv (compEquiv j.symm v).mapMatrix.toMulEquiv g))) =
      GeneralLinearGroup.map (pLoc F u) (locGL F a v g) := fun u => by
    rw [key]
    by_cases h : u = v
    · subst h; rw [pLoc_locGL, pLoc_locGL]
      exact Units.ext (Matrix.ext fun _ _ => (compEquiv j.symm u).symm_apply_apply _)
    · rw [pLoc_locGL_of_ne h, pLoc_locGL_of_ne (fun e => h (plMap_injective _ e)), map_one]
  refine Units.ext (Matrix.ext fun i k => FiniteAdeleRing.ext _ fun u => ?_)
  exact congrArg (fun x : GL (Fin a) (u.adicCompletion F) => x.val i k) (key2 u)
theorem hasSat_pullSub {π : CuspSub F a} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}
    (h : (CG.mk π).HasSat (plMap j w) B) : (CG.mk (pullSub j π)).HasSat w B := by
  obtain ⟨v, rfl⟩ : ∃ v, plMap j.symm v = w := ⟨_, plMap_symm_plMap j w⟩
  rw [plMap_plMap_symm] at h
  rw [CG.hasSat_mk] at h ⊢
  refine hasSatGL_of_equiv (compEquiv j.symm v) (valued_compEquiv j.symm v) (absNorm_plMap j.symm v)
    ((pull a j).submoduleMap π.V) (fun g x => ?_) h
  refine Subtype.ext ?_
  change act (.fin (locGL E a (plMap j.symm v) (Units.mapEquiv (compEquiv j.symm v).mapMatrix.toMulEquiv g)))
      (pull a j x.1) =
    pull a j (act (.fin (locGL F a v g)) x.1)
  rw [act_pull j (.fin _) x.1, opMap, finMap_locGL]

end SatPullback

end FieldIsoPullback

end InfinitesimalCharacterPullback

end RHDirect.Stage13GL_BernoulliAndWeylAlg
end
