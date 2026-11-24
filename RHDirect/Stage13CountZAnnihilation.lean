import RHDirect.Stage13CountZLocalKummer
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification

/-!
# RHDirect.Stage13CountZAnnihilation

Stage 13 — **Unconditional `CountZ` / `PropZ` Trivial-Character Annihilation (Field #7e, `0` Open Parameters!)**:
Proves unconditionally from pure Mathlib (`0` `sorry`, `0` custom `axiom`s, `0` `opaque`, `0` `native_decide`)
that for EVERY odd prime `l ≠ 2` and EVERY `k ≥ 1` with `(l - 1) ∣ 2 * k`:
$$\operatorname{shaLen}_{\mathbb{Q}}(l, k)
  := \operatorname{length}_{\mathbb{Z}_l}\!\Bigl(\Sha^1\!\bigl(G_{\mathbb{Q}, S_l},\, (\mathbb{Q}_l / \mathbb{Z}_l)(-k)\bigr)\Bigr) = 0.$$

## Complete Proof Architecture (`0` Class Field Theory, `0` Open Parameters!)

- **Case 1 (`(l - 1) ∣ k`)**: Proved unconditionally in `RHDirect.Stage13CountZLocalKummer`
  (`Stage13CountZLocalKummer.galoisShaLen_rat_eq_zero_of_dvd_k`) via local Kummer filtration in
  `ℚ(ζ_l)`, Minkowski's discriminant bound over `ℚ`, and `cycZ_Ine_surjective`.
- **Section 5**: Quadratic subfield `K = ℚ(√l*) ⊂ ℚ(ζ_l)` (`l* = (-1)^((l-1)/2) l`) via quadratic
  Gauss sums, exact discriminant `discr K = l*`, and Minkowski's bound `classNumber K < l`
  (using `1 + Real.log (√l) < √l` for every `l ≥ 3`).
- **Section 6**: Furtwängler / Hilbert-90 + Herbrand Quotient (`dvd_classNumber_of_unramified_cyclic_prime_ext`:
  any everywhere-unramified cyclic Galois extension `H / K` of odd prime degree `l` over a
  quadratic field `K` satisfies `l ∣ classNumber K`) and **Case 2 (`(l - 1) ∣ 2 * k`, `¬ (l - 1) ∣ k`)**
  (`galoisShaLen_rat_eq_zero_of_dvd_two_mul_not_dvd`).
- **Section 7**: Headline Unconditional `CountZ` / `PropZ` Theorems (`0` Open Parameters):
  - `realGalois_shaLen_rat_eq_zero_of_dvd_two_mul_k`
  - `countZ_trivial_vlen_eq_zero`
  - `field1_7e_countZ_discharge` (discharges Field #7e of `Stage13Field1Unification.Field1RemainingHypotheses`
    verbatim with `0` open parameters!).
-/

noncomputable section

open scoped Pointwise NumberField nonZeroDivisors Real Matrix
open RHDirect.Stage12GaloisShaLen
open RHDirect.Stage13SixCaseVWinAssembly
open RHDirect.Stage13CountZLocalKummer
open NumberField IsDedekindDomain IntermediateField Polynomial Module Finset

namespace RHDirect.Stage13CountZAnnihilation

/-! ## Section 5: Quadratic Subfield `K = ℚ(√l*)`, Discriminant `|discr K| = l`, & `classNumber K < l` -/

section QuadraticSubfieldAndClassNumberBound

/-- Signed odd prime `l* = (-1)^((l-1)/2) * l`, satisfying `l* ≡ 1 (mod 4)` and `|l*| = l`. -/
def lStar (l : ℕ) : ℤ :=
  if l % 4 = 1 then (l : ℤ) else -(l : ℤ)

lemma lStar_mod_four {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) : lStar l % 4 = 1 := by
  have hodd : l % 2 = 1 := hl.eq_two_or_odd.resolve_left hl2
  unfold lStar
  split_ifs with h4 <;> omega

lemma lStar_squarefree {l : ℕ} (hl : l.Prime) : Squarefree (lStar l) := by
  have hp : Squarefree (l : ℤ) := (Nat.prime_iff_prime_int.mp hl).squarefree
  unfold lStar
  split_ifs
  · exact hp
  · exact fun x hx => hp x (dvd_neg.mp hx)

lemma lStar_ne_one {l : ℕ} (hl : l.Prime) : lStar l ≠ 1 := by
  have h2 := hl.two_le
  unfold lStar
  split_ifs <;> omega

lemma lStar_abs {l : ℕ} : |(lStar l : ℝ)| = (l : ℝ) := by
  unfold lStar
  split_ifs
  · simp [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) l)]
  · simp [abs_neg, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) l)]

/-- Quadratic Gauss sum: in any characteristic-zero field containing a primitive `l`-th root of
unity `ζ` (`l` odd prime), there exists `G ∈ ℚ⟮ζ⟯` with `G ^ 2 = lStar l` and
`σ G = (legendreSym l a : ℤ) * G` whenever `σ ζ = ζ ^ a`. -/
theorem exists_quadratic_gauss_sum {Ω : Type} [Field Ω] [CharZero Ω] {l : ℕ} [hl : Fact l.Prime]
    (hl2 : l ≠ 2) {ζ : Ω} (hζ : IsPrimitiveRoot ζ l) :
    ∃ G : Ω, G ^ 2 = (lStar l : Ω) ∧ G ∈ IntermediateField.adjoin ℚ ({ζ} : Set Ω) ∧
      ∀ (σ : Ω →+* Ω) (a : ℕ), σ ζ = ζ ^ a → σ G = (legendreSym l a : Ω) * G := by
  classical
  have : NeZero l := ⟨hl.out.ne_zero⟩
  have hζl : ζ ^ l = 1 := hζ.pow_eq_one
  let χ : MulChar (ZMod l) Ω := (quadraticChar (ZMod l)).ringHomComp (Int.castRingHom Ω)
  let ψ : AddChar (ZMod l) Ω := AddChar.zmodChar l hζl
  have hψp : ψ.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root l hζ
  have hchar : ringChar (ZMod l) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hl2
  have hχ1 : χ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff (f := Int.castRingHom Ω) Int.cast_injective).2
      (quadraticChar_ne_one hchar)
  have hχq : χ.IsQuadratic := (quadraticChar_isQuadratic (ZMod l)).comp _
  have hχa : ∀ a : ZMod l, χ a = ((quadraticChar (ZMod l) a : ℤ) : Ω) := fun a => by
    simp [χ, MulChar.ringHomComp_apply]
  have hψa : ∀ n : ℕ, ψ (n : ZMod l) = ζ ^ n := fun n => AddChar.zmodChar_apply' hζl n
  refine ⟨gaussSum χ ψ, ?_, ?_, ?_⟩
  · rw [gaussSum_sq hχ1 hχq hψp, hχa, ZMod.card]
    have h1 : quadraticChar (ZMod l) (-1) = legendreSym l (-1) := by simp [legendreSym]
    rw [h1, legendreSym.at_neg_one hl2, ZMod.χ₄_nat_eq_if_mod_four, lStar]
    have hodd : l % 2 = 1 := hl.out.eq_two_or_odd.resolve_left hl2
    have h4 : l % 4 = 1 ∨ l % 4 = 3 := by omega
    rcases h4 with h4 | h4
    · simp [hodd, h4]
    · simp [hodd, h4]
  · unfold gaussSum
    refine IntermediateField.sum_mem _ fun a _ => IntermediateField.mul_mem _ ?_ ?_
    · rw [hχa]; exact IntermediateField.intCast_mem _ _
    · rw [← ZMod.natCast_zmod_val a, hψa]
      exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ ζ) _
  · intro σ b hσ
    have hG : σ (gaussSum χ ψ) = gaussSum χ (ψ.mulShift (b : ZMod l)) := by
      unfold gaussSum
      rw [map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_mul, hχa, map_intCast, AddChar.mulShift_apply]
      congr 1
      rw [← ZMod.natCast_zmod_val a, hψa, map_pow, hσ, ← pow_mul, ← Nat.cast_mul, hψa]
    have hb : (b : ZMod l) ≠ 0 := by
      intro h0
      have h1 : σ ζ = 1 := by
        rw [hσ]
        rw [ZMod.natCast_eq_zero_iff] at h0
        obtain ⟨k, rfl⟩ := h0
        rw [pow_mul, hζl, one_pow]
      have h2 : ζ = 1 := σ.injective (by rw [h1, map_one])
      exact hζ.ne_one hl.out.one_lt h2
    have hmul : χ (b : ZMod l) * gaussSum χ (ψ.mulShift (b : ZMod l)) = gaussSum χ ψ :=
      gaussSum_mulShift χ ψ (Units.mk0 _ hb)
    have hu2 : χ (b : ZMod l) * χ (b : ZMod l) = 1 := by
      rw [hχa, ← Int.cast_mul, ← sq, quadraticChar_sq_one hb, Int.cast_one]
    have hleg : ((legendreSym l b : ℤ) : Ω) = χ (b : ZMod l) := by
      rw [hχa]; simp [legendreSym]
    rw [hG, hleg, ← hmul, ← mul_assoc, hu2, one_mul]

private lemma quad_not_sq_rat (a : ℤ) (ha : Squarefree a) (h1 : a ≠ 1) : ∀ b : ℚ, b ^ 2 ≠ (a : ℚ) := by
  intro b hb
  have hsq : IsSquare (a : ℚ) := ⟨b, by rw [← hb]; ring⟩
  obtain ⟨n, hn⟩ := Rat.isSquare_intCast_iff.1 hsq
  have hu : IsUnit n := ha n ⟨1, by rw [hn, mul_one]⟩
  rcases Int.isUnit_iff.1 hu with h | h <;> (subst h; simp at hn; exact h1 hn)

/-- Exact degree and discriminant of a quadratic field `ℚ(√a)` with `a` squarefree, `a ≡ 1 (mod 4)`,
`a ≠ 1`. Works uniformly for both real (`a > 0`) and imaginary (`a < 0`) quadratic fields. -/
theorem quadDiscr_eq (K : Type) [Field K] [NumberField K] (a : ℤ) (x : K)
    (hx : x ^ 2 = (a : K)) (hadj : IntermediateField.adjoin ℚ ({x} : Set K) = ⊤)
    (hsf : Squarefree a) (h4 : a % 4 = 1) (h1 : a ≠ 1) :
    Module.finrank ℚ K = 2 ∧ NumberField.discr K = a := by
  have hirr : Irreducible (X ^ 2 - C (a : ℚ)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (quad_not_sq_rat a hsf h1)
  have hmon : (X ^ 2 - C (a : ℚ)).Monic := monic_X_pow_sub_C _ two_ne_zero
  have hev : aeval x (X ^ 2 - C (a : ℚ)) = 0 := by simp [hx]
  have hmin : minpoly ℚ x = X ^ 2 - C (a : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirr hev hmon).symm
  have hint : IsIntegral ℚ x := .of_finite ℚ x
  have hrank : Module.finrank ℚ K = 2 := by
    have := IntermediateField.adjoin.finrank hint
    rw [hmin, natDegree_X_pow_sub_C, hadj, IntermediateField.finrank_top'] at this
    exact this
  refine ⟨hrank, ?_⟩
  have htrq : ∀ q : ℚ, Algebra.trace ℚ K (algebraMap ℚ K q) = 2 * q := by
    intro q; rw [Algebra.trace_algebraMap, hrank]; simp
  have htrlin : ∀ (q : ℚ) (z : K), Algebra.trace ℚ K (algebraMap ℚ K q * z) =
      q * Algebra.trace ℚ K z := by
    intro q z; rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have htrx : Algebra.trace ℚ K x = 0 := by
    have hnc : (X ^ 2 - C (a : ℚ)).nextCoeff = 0 := by
      rw [nextCoeff, natDegree_X_pow_sub_C, coeff_sub, coeff_X_pow, coeff_C]; norm_num
    rw [trace_eq_finrank_mul_minpoly_nextCoeff, hmin, hnc]; simp
  set ω : K := (1 + x) / 2 with hω
  have hω1 : ω = algebraMap ℚ K (1 / 2) + algebraMap ℚ K (1 / 2) * x := by
    rw [hω]; simp; ring
  have hω2 : ω * ω = algebraMap ℚ K ((1 + a) / 4) + algebraMap ℚ K (1 / 2) * x := by
    rw [hω]; simp; linear_combination (1 / 4 : K) * hx
  have htr1 : Algebra.trace ℚ K 1 = 2 := by
    rw [show (1 : K) = algebraMap ℚ K 1 by simp, htrq]; norm_num
  have htrω : Algebra.trace ℚ K ω = 1 := by
    rw [hω1, map_add, htrq, htrlin, htrx]; norm_num
  have htrωω : Algebra.trace ℚ K (ω * ω) = (1 + a) / 2 := by
    rw [hω2, map_add, htrq, htrlin, htrx]; ring
  have hdisc : Algebra.discr ℚ ![(1 : K), ω] = a := by
    rw [Algebra.discr_def, Matrix.det_fin_two]
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, one_mul, mul_one]
    rw [htr1, htrω, htrωω]; ring
  obtain ⟨c, hc⟩ : ∃ c : ℤ, a = 4 * c + 1 := ⟨a / 4, by omega⟩
  have hcK : (a : K) = 4 * c + 1 := by rw [hc]; push_cast; ring
  have hωint : IsIntegral ℤ ω := by
    refine ⟨X ^ 2 - X - C c, ?_, ?_⟩
    · monicity!
    · rw [eval₂_sub, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C, algebraMap_int_eq, eq_intCast, hω]
      linear_combination (1 / 4 : K) * hx + (1 / 4 : K) * hcK
  let B := RingOfIntegers.basis K
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 K)) = 2 := by
    rw [← hrank, Module.finrank_eq_card_basis (integralBasis K)]
  let e := Fintype.equivFinOfCardEq hcard
  let B' : Module.Basis (Fin 2) ℤ (𝓞 K) := B.reindex e
  let Cb : Module.Basis (Fin 2) ℚ K := (integralBasis K).reindex e
  have hC : ∀ i, Cb i = ((B' i : 𝓞 K) : K) := by
    intro i; simp [Cb, B', B, integralBasis_apply]
  let ω' : 𝓞 K := ⟨ω, hωint⟩
  let v : Fin 2 → 𝓞 K := ![1, ω']
  let P : Matrix (Fin 2) (Fin 2) ℤ := B'.toMatrix v
  have hv : ![(1 : K), ω] = Cb ᵥ* (P.map (Int.cast : ℤ → ℚ)).map (algebraMap ℚ K) := by
    have h0 := B'.toMatrix_map_vecMul v
    funext j
    have hj := congrArg (fun w : Fin 2 → 𝓞 K => ((w j : 𝓞 K) : K)) h0
    have hvj : ((v j : 𝓞 K) : K) = ![(1 : K), ω] j := by fin_cases j <;> rfl
    rw [← hvj, ← hj]
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hC, P]
  have key : (a : ℚ) = ((P.det : ℤ) : ℚ) ^ 2 * (NumberField.discr K : ℚ) := by
    rw [← hdisc, hv, Algebra.discr_of_matrix_vecMul, coe_discr, Module.Basis.coe_reindex,
      Algebra.discr_reindex]
    congr 2
    exact (RingHom.map_det (Int.castRingHom ℚ) P).symm
  have key' : a = P.det ^ 2 * NumberField.discr K := by exact_mod_cast key
  have hu : IsUnit P.det := hsf P.det ⟨NumberField.discr K, by rw [key']; ring⟩
  rcases Int.isUnit_iff.1 hu with h | h <;> (rw [key', h]; ring)

private theorem sum_zeta_pow_succ_le (k : ℕ) {X : ℝ} (hX : 1 ≤ X) (N : ℕ) (hN : (N : ℝ) ≤ X) :
    ((∑ n ∈ Ioc 0 N, (ArithmeticFunction.zeta ^ (k + 1) : ArithmeticFunction ℕ) n : ℕ) : ℝ)
      ≤ N * (1 + Real.log X) ^ k := by
  have hL : 0 ≤ 1 + Real.log X := by have := Real.log_nonneg hX; linarith
  induction k generalizing N with
  | zero => simp only [zero_add, pow_one, ArithmeticFunction.sum_Ioc_zeta, pow_zero, mul_one, le_refl]
  | succ k ih =>
    rw [pow_succ', ArithmeticFunction.sum_Ioc_mul_eq_sum_sum, Nat.cast_sum]
    have hH : ∑ n ∈ Ioc 0 N, (n : ℝ)⁻¹ ≤ 1 + Real.log X := by
      have h1 := harmonic_le_one_add_log N
      simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h1
      have h2 : Real.log N ≤ Real.log X := by
        rcases Nat.eq_zero_or_pos N with rfl | h
        · simpa using Real.log_nonneg hX
        · exact Real.log_le_log (by exact_mod_cast h) hN
      have h3 : Ioc 0 N = Icc 1 N := rfl
      rw [h3]; linarith
    calc _ ≤ ∑ n ∈ Ioc 0 N, (N * (1 + Real.log X) ^ k) * (n : ℝ)⁻¹ := by
          refine sum_le_sum fun n hn => ?_
          have hn0 : n ≠ 0 := (mem_Ioc.mp hn).1.ne'
          rw [ArithmeticFunction.zeta_apply_ne hn0, one_mul]
          refine (ih (N / n) (le_trans (by exact_mod_cast Nat.div_le_self N n) hN)).trans ?_
          have : ((N / n : ℕ) : ℝ) ≤ N * (n : ℝ)⁻¹ := by
            rw [← div_eq_mul_inv]; exact Nat.cast_div_le
          calc _ ≤ (N * (n : ℝ)⁻¹) * (1 + Real.log X) ^ k := by gcongr
            _ = _ := by ring
      _ ≤ (N * (1 + Real.log X) ^ k) * (1 + Real.log X) := by
          rw [← mul_sum]; gcongr
      _ = _ := by ring

private theorem sum_zeta_pow_le {k : ℕ} (hk : 1 ≤ k) {X : ℝ} (hX : 1 ≤ X) :
    ((∑ n ∈ Ioc 0 ⌊X⌋₊, (ArithmeticFunction.zeta ^ k : ArithmeticFunction ℕ) n : ℕ) : ℝ)
      ≤ X * (1 + Real.log X) ^ (k - 1) := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hL : 0 ≤ 1 + Real.log X := by have := Real.log_nonneg hX; linarith
  have h := Nat.floor_le (zero_le_one.trans hX)
  refine (sum_zeta_pow_succ_le k hX _ h).trans ?_
  rw [Nat.add_sub_cancel]
  gcongr

private theorem card_finMulAntidiag_eq_zeta_pow (k n : ℕ) :
    (Nat.finMulAntidiag k n).card = (ArithmeticFunction.zeta ^ k : ArithmeticFunction ℕ) n := by
  induction k generalizing n with
  | zero =>
    by_cases h : n = 1
    · subst h; simp [Nat.finMulAntidiag_one]
    · simp [Nat.finMulAntidiag_zero_left h, ArithmeticFunction.one_apply_ne h]
  | succ k ih =>
    rw [pow_succ', ArithmeticFunction.mul_apply]
    have : ∑ x ∈ n.divisorsAntidiagonal, (ArithmeticFunction.zeta : ArithmeticFunction ℕ) x.1 *
          (ArithmeticFunction.zeta ^ k : ArithmeticFunction ℕ) x.2
        = ∑ x ∈ n.divisorsAntidiagonal, (Nat.finMulAntidiag k x.2).card := by
      refine sum_congr rfl fun x hx => ?_
      rw [ArithmeticFunction.zeta_apply_ne (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hx),
        one_mul, ih]
    rw [this, ← card_sigma]
    refine card_nbij' (fun f => ⟨(f 0, ∏ i, f (Fin.succ i)), fun i => f (Fin.succ i)⟩)
      (fun y => Fin.cons y.1.1 y.2) ?_ ?_ ?_ ?_
    · intro f hf
      simp only [mem_coe, Nat.mem_finMulAntidiag, Fin.prod_univ_succ] at hf
      simp only [mem_coe, mem_sigma, Nat.mem_divisorsAntidiagonal, Nat.mem_finMulAntidiag]
      refine ⟨hf, trivial, ?_⟩
      intro h; exact hf.2 (by rw [← hf.1, h, mul_zero])
    · rintro ⟨⟨a, b⟩, g⟩ hy
      simp only [mem_coe, mem_sigma, Nat.mem_divisorsAntidiagonal, Nat.mem_finMulAntidiag] at hy
      simp only [mem_coe, Nat.mem_finMulAntidiag, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      rw [hy.2.1]; exact hy.1
    · intro f _; exact Fin.cons_self_tail f
    · rintro ⟨⟨a, b⟩, g⟩ hy
      simp only [mem_coe, mem_sigma, Nat.mem_divisorsAntidiagonal, Nat.mem_finMulAntidiag] at hy
      simp only [Fin.cons_zero, Fin.cons_succ, hy.2.1]

private theorem exists_colouring_maximal_ideals (K : Type) [Field K] [NumberField K] :
    ∃ c : Ideal (𝓞 K) → Fin (finrank ℚ K), ∀ p : ℕ, p.Prime → ∀ P Q : Ideal (𝓞 K),
      P.IsMaximal → Q.IsMaximal → (p : 𝓞 K) ∈ P → (p : 𝓞 K) ∈ Q → c P = c Q → P = Q := by
  classical
  have : Nonempty (Fin (finrank ℚ K)) := ⟨⟨0, finrank_pos⟩⟩
  have key : ∀ p : ℕ, ∃ e : Ideal (𝓞 K) → Fin (finrank ℚ K), p.Prime →
      Set.InjOn e {P | P.IsMaximal ∧ (p : 𝓞 K) ∈ P} := by
    intro p
    by_cases hp : p.Prime
    · have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
      have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
        ((Ideal.span_singleton_prime hp'.ne_zero).mpr hp').isMaximal hp0
      have : (Ideal.span {(p : ℤ)}).IsPrime := hmax.isPrime
      have hc : (IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K)).card ≤ finrank ℚ K := by
        have hfin_po : ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)).Finite :=
          IsDedekindDomain.primesOver_finite (Ideal.span {(p : ℤ)}) (𝓞 K)
        let : Fintype ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) := hfin_po.fintype
        have hcard_eq : (IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K)).card =
            Fintype.card ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K)) := by
          rw [← Fintype.card_coe]
          exact Fintype.card_congr (Equiv.setCongr (IsDedekindDomain.coe_primesOverFinset hp0 (𝓞 K)))
        have hsum := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {(p : ℤ)}) (𝓞 K)
        rw [hcard_eq, ← NumberField.RingOfIntegers.rank K, ← hsum]
        calc Fintype.card ((Ideal.span {(p : ℤ)}).primesOver (𝓞 K))
            = ∑ _q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K), 1 := by simp
          _ ≤ ∑ q : (Ideal.span {(p : ℤ)}).primesOver (𝓞 K), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
              refine Finset.sum_le_sum fun q _ => ?_
              have : q.1.IsPrime := q.2.1
              exact Nat.mul_pos (Ideal.ramificationIdx_pos q.1 ℤ) (Ideal.inertiaDeg_pos q.1 ℤ)
      have hsub : {P : Ideal (𝓞 K) | P.IsMaximal ∧ (p : 𝓞 K) ∈ P} ⊆
          (IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K) : Set _) := by
        rintro P ⟨hP, hpP⟩
        rw [mem_coe, IsDedekindDomain.mem_primesOverFinset_iff hp0]
        refine ⟨hP.isPrime, ⟨hmax.eq_of_le ?_ ?_⟩⟩
        · exact Ideal.comap_ne_top _ hP.ne_top
        · rw [Ideal.span_singleton_le_iff_mem, Ideal.under, Ideal.mem_comap]
          simpa using hpP
      obtain ⟨e, -, he⟩ := Set.Finite.exists_injOn_of_encard_le
        (t := (Set.univ : Set (Fin (finrank ℚ K))))
        (Finset.finite_toSet (IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K))) (by
          rw [Set.encard_coe_eq_coe_finsetCard, Set.encard_univ]
          simpa using hc)
      exact ⟨e, fun _ => he.mono hsub⟩
    · exact ⟨fun _ => Classical.arbitrary _, fun h => absurd h hp⟩
  choose e he using key
  have hmin : ∀ p : ℕ, p.Prime → ∀ P : Ideal (𝓞 K), P.IsMaximal → (p : 𝓞 K) ∈ P →
      (Ideal.absNorm P).minFac = p := by
    intro p hp P hP hpP
    obtain ⟨q, n, hn, hqP, hq, H⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
    rw [H, hq.pow_minFac hn.ne']
    by_contra hne
    have hco : IsCoprime (q : 𝓞 K) (p : 𝓞 K) :=
      Nat.Coprime.cast ((Nat.coprime_primes hq hp).mpr hne)
    obtain ⟨a, b, hab⟩ := hco
    exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr
      (hab ▸ P.add_mem (P.mul_mem_left a hqP) (P.mul_mem_left b hpP)))
  refine ⟨fun P => e (Ideal.absNorm P).minFac P, fun p hp P Q hP hQ hpP hpQ h => ?_⟩
  simp only [hmin p hp P hP hpP, hmin p hp Q hQ hpQ] at h
  exact he p hp ⟨hP, hpP⟩ ⟨hQ, hpQ⟩ h

private theorem ncard_ideal_absNorm_eq_le (K : Type) [Field K] [NumberField K] {n : ℕ} (hn : n ≠ 0) :
    {I : Ideal (𝓞 K) | Ideal.absNorm I = n}.ncard
      ≤ (ArithmeticFunction.zeta ^ finrank ℚ K : ArithmeticFunction ℕ) n := by
  classical
  obtain ⟨c, hc⟩ := exists_colouring_maximal_ideals K
  have key : ∀ (P : Ideal (𝓞 K)) (p f : ℕ), P.IsMaximal → p.Prime → (p : 𝓞 K) ∈ P →
      Ideal.absNorm P = p ^ f → ∀ s : Multiset (Ideal (𝓞 K)), (∀ Q ∈ s, Q.IsMaximal) →
      ((s.filter (fun Q => c Q = c P)).map Ideal.absNorm).prod ≠ 0 ∧
      (((s.filter (fun Q => c Q = c P)).map Ideal.absNorm).prod).factorization p
        = f * s.count P := by
    intro P p f hP hp hpP hN s
    induction s using Multiset.induction_on with
    | empty => intro _; simp
    | cons Q s ih =>
      intro hs
      obtain ⟨ih0, ih⟩ := ih fun R hR => hs R (Multiset.mem_cons_of_mem hR)
      have hQ : Q.IsMaximal := hs Q (Multiset.mem_cons_self Q s)
      obtain ⟨q, g, hg, hqQ, hq, H⟩ := Ideal.exists_prime_and_absNorm_eq_pow Q
      have hQ0 : Ideal.absNorm Q ≠ 0 := H ▸ pow_ne_zero _ hq.ne_zero
      by_cases hcol : c Q = c P
      · rw [Multiset.filter_cons_of_pos (p := fun Q => c Q = c P) s hcol, Multiset.map_cons,
          Multiset.prod_cons, Nat.factorization_mul hQ0 ih0, Finsupp.add_apply, ih]
        refine ⟨mul_ne_zero hQ0 ih0, ?_⟩
        by_cases hQP : Q = P
        · subst hQP
          rw [Multiset.count_cons_self, hN, hp.factorization_pow, Finsupp.single_eq_same]; ring
        · rw [Multiset.count_cons_of_ne (Ne.symm hQP), H, hq.factorization_pow,
            Finsupp.single_apply, if_neg, zero_add]
          rintro rfl
          exact hQP (hc q hq Q P hQ hP hqQ hpP hcol)
      · rw [Multiset.filter_cons_of_neg (p := fun Q => c Q = c P) s hcol]
        have hQP : P ≠ Q := by rintro rfl; exact hcol rfl
        rw [Multiset.count_cons_of_ne hQP]
        exact ⟨ih0, ih⟩
  have hprod : ∀ s : Multiset (Ideal (𝓞 K)),
      ∏ i, ((s.filter (fun Q => c Q = i)).map Ideal.absNorm).prod = Ideal.absNorm s.prod := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons Q s ih =>
      rw [Multiset.prod_cons, map_mul, ← ih]
      have : ∀ i, (((Q ::ₘ s).filter (fun Q => c Q = i)).map Ideal.absNorm).prod =
          (if c Q = i then Ideal.absNorm Q else 1) *
            ((s.filter (fun Q => c Q = i)).map Ideal.absNorm).prod := by
        intro i; rw [Multiset.filter_cons]; split_ifs <;> simp
      simp_rw [this]
      rw [prod_mul_distrib]; simp
  have hmax : ∀ I : Ideal (𝓞 K), ∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors I,
      Q.IsMaximal := by
    intro I Q hQ
    have hQ' := UniqueFactorizationMonoid.prime_of_normalized_factor Q hQ
    exact (Ideal.isPrime_of_prime hQ').isMaximal hQ'.ne_zero
  have hne : ∀ I : Ideal (𝓞 K), Ideal.absNorm I = n → I ≠ ⊥ := by
    rintro I hI rfl; exact hn (by rw [← hI]; simp)
  rw [← card_finMulAntidiag_eq_zeta_pow, ← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard_of_injOn
    (fun I i => (((UniqueFactorizationMonoid.normalizedFactors I).filter
      (fun Q => c Q = i)).map Ideal.absNorm).prod) ?_ ?_ (Finset.finite_toSet _)
  · intro I hI
    rw [mem_coe, Nat.mem_finMulAntidiag, hprod, Ideal.prod_normalizedFactors_eq_self (hne I hI)]
    exact ⟨hI, hn⟩
  · intro I hI J hJ h
    rw [← Ideal.prod_normalizedFactors_eq_self (hne I hI),
      ← Ideal.prod_normalizedFactors_eq_self (hne J hJ)]
    congr 1; ext P
    by_cases hP : P.IsMaximal
    · obtain ⟨p, f, hf, hpP, hp, H⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
      have h1 := (key P p f hP hp hpP H _ (hmax I)).2
      have h2 := (key P p f hP hp hpP H _ (hmax J)).2
      have h3 := congrFun h (c P)
      simp only at h3
      rw [h3, h2] at h1
      exact (Nat.eq_of_mul_eq_mul_left hf h1).symm
    · rw [Multiset.count_eq_zero_of_notMem fun h => hP (hmax I P h),
        Multiset.count_eq_zero_of_notMem fun h => hP (hmax J P h)]

private theorem minkowski_const_le_one (K : Type) [Field K] [NumberField K] :
    (4 / π) ^ InfinitePlace.nrComplexPlaces K *
      (((finrank ℚ K).factorial : ℝ) / (finrank ℚ K : ℝ) ^ finrank ℚ K) ≤ 1 := by
  have hr := InfinitePlace.card_add_two_mul_card_eq_rank K
  have hpos : 0 < finrank ℚ K := finrank_pos
  obtain ⟨n, hn⟩ : ∃ n, finrank ℚ K = n + 1 := ⟨finrank ℚ K - 1, by omega⟩
  rw [hn] at hr ⊢
  have h1 : (4 / π) ^ InfinitePlace.nrComplexPlaces K ≤ (2 : ℝ) ^ n := by
    have h4 : 4 / π ≤ 2 := by rw [div_le_iff₀ Real.pi_pos]; linarith [Real.pi_gt_three]
    calc _ ≤ (2 : ℝ) ^ InfinitePlace.nrComplexPlaces K := by gcongr
      _ ≤ _ := pow_le_pow_right₀ one_le_two (by omega)
  have h2 := two_pow_mul_factorial_succ_le n
  rw [← mul_div_assoc, div_le_one (by positivity)]
  push_cast
  refine le_trans ?_ h2
  gcongr

/-- For ANY quadratic field `K` (`finrank ℚ K = 2`) with `|discr K| = l` (`l` prime):
`classNumber K < l` (hence `¬ l ∣ classNumber K`)!
Uses `1 + Real.log (√l) < √l` (`Real.log_lt_sub_one_of_pos`), valid for EVERY `l ≥ 2`! -/
theorem classNumber_lt_of_quad_discr_prime (K : Type) [Field K] [NumberField K]
    {l : ℕ} (hl : l.Prime) (hrank : Module.finrank ℚ K = 2)
    (hdiscr : |(NumberField.discr K : ℝ)| = (l : ℝ)) :
    NumberField.classNumber K < l := by
  classical
  set X : ℝ := √|(NumberField.discr K : ℝ)| with hXdef
  have hl1 : (1 : ℝ) < (l : ℝ) := by exact_mod_cast hl.one_lt
  have hXeq : X = √(l : ℝ) := by rw [hXdef, hdiscr]
  have hXgt1 : 1 < X := by rw [hXeq, Real.lt_sqrt (by norm_num)]; linarith
  have hX1 : 1 ≤ X := hXgt1.le
  have hcn_le : (NumberField.classNumber K : ℝ) ≤ X * (1 + Real.log X) := by
    have hbound := sum_zeta_pow_le (k := finrank ℚ K) finrank_pos hX1
    rw [hrank, show 2 - 1 = 1 from rfl, pow_one] at hbound
    refine le_trans ?_ hbound
    rw [Nat.cast_le]
    have hex : ∀ C : ClassGroup (𝓞 K), ∃ I : (Ideal (𝓞 K))⁰,
        ClassGroup.mk0 I = C ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ X := by
      intro C
      obtain ⟨I, hI, hN⟩ := exists_ideal_in_class_of_norm_le C
      refine ⟨I, hI, hN.trans ?_⟩
      rw [← mul_assoc]
      exact mul_le_of_le_one_left (Real.sqrt_nonneg _) (minkowski_const_le_one K)
    choose g hg hN using hex
    have hginj : Function.Injective fun C => (g C : Ideal (𝓞 K)) := by
      intro C D h; rw [← hg C, ← hg D, Subtype.ext h]
    rw [NumberField.classNumber, ← card_univ, card_eq_sum_card_fiberwise
      (f := fun C => Ideal.absNorm (g C : Ideal (𝓞 K))) (t := Ioc 0 ⌊X⌋₊)]
    · refine sum_le_sum fun n hn => le_trans ?_
          (by simpa [hrank] using ncard_ideal_absNorm_eq_le K (mem_Ioc.mp hn).1.ne')
      rw [← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard_of_injOn (fun C => (g C : Ideal (𝓞 K)))
        (fun C hC => by simpa using hC) hginj.injOn (Ideal.finite_setOfPred_absNorm_eq n)
    · intro C _
      rw [mem_coe, mem_Ioc]
      exact ⟨Nat.pos_of_ne_zero (Ideal.absNorm_ne_zero_of_nonZeroDivisors _), Nat.le_floor (hN C)⟩
  have hlog : Real.log X < X - 1 := Real.log_lt_sub_one_of_pos (by linarith) hXgt1.ne'
  have hlt_real : (NumberField.classNumber K : ℝ) < (l : ℝ) := by
    calc (NumberField.classNumber K : ℝ)
        ≤ X * (1 + Real.log X) := hcn_le
      _ < X * X := mul_lt_mul_of_pos_left (by linarith) (by linarith)
      _ = (l : ℝ) := by rw [hXeq, Real.mul_self_sqrt (Nat.cast_nonneg l)]
  exact_mod_cast hlt_real

end QuadraticSubfieldAndClassNumberBound

/-! ## Section 6: Furtwängler / Hilbert-90 + Herbrand Quotient (`l ∣ classNumber K`) & Case 2 -/

section FurtwanglerHerbrandAndCaseTwo

/-! ### Part 6a: Multiplicative Hilbert 90 for Cyclic Extensions of Prime Order -/

/-- Multiplicative Hilbert 90 for a cyclic Galois automorphism `σ : H ≃ₐ[K] H` of order `m > 0`:
if `∏_{i < m} (σ ^ i) u = 1`, then `∃ α : Hˣ, σ α = u * α`. -/
theorem hilbert90_cyclic {K H : Type} [Field K] [Field H] [Algebra K H]
    (σ : H ≃ₐ[K] H) {m : ℕ} (hm : orderOf σ = m) (hm0 : 0 < m)
    (u : Hˣ) (hnorm : ∏ i ∈ Finset.range m, (σ ^ i) (u : H) = 1) :
    ∃ α : Hˣ, σ (α : H) = (u : H) * (α : H) := by
  classical
  let a : ℕ → H := fun i => ∏ j ∈ Finset.range i, (σ ^ j) (u : H)
  have ha0 : a 0 = 1 := by simp [a]
  have ham : a m = 1 := hnorm
  have ha_step : ∀ i, (u : H) * σ (a i) = a (i + 1) := by
    intro i
    simp only [a, map_prod, Finset.prod_range_succ', pow_zero, AlgEquiv.one_apply, pow_succ',
      AlgEquiv.mul_apply]
    ring
  have hσm : σ ^ m = 1 := by rw [← hm]; exact pow_orderOf_eq_one σ
  -- Show `∃ c : H, ∑ i ∈ range m, a i * (σ ^ i) c ≠ 0` by Dedekind's linear independence of characters
  have hex : ∃ c : H, ∑ i ∈ Finset.range m, a i * (σ ^ i) c ≠ 0 := by
    by_contra hall
    push Not at hall
    let f : Fin m → (H →* H) := fun i => ((σ ^ (i : ℕ) : H ≃ₐ[K] H) : H →* H)
    have hfinj : Function.Injective f := by
      intro i j hij
      have hpow : σ ^ (i : ℕ) = σ ^ (j : ℕ) := by
        ext x; exact congrArg (fun g : H →* H => g x) hij
      have hsub : (i : ℕ) = (j : ℕ) := by
        have hlt_i : (i : ℕ) < orderOf σ := hm.symm ▸ i.2
        have hlt_j : (j : ℕ) < orderOf σ := hm.symm ▸ j.2
        exact pow_injOn_Iio_orderOf hlt_i hlt_j hpow
      exact Fin.ext hsub
    have hli : LinearIndependent H (fun i : Fin m => ((f i : H →* H) : H → H)) :=
      (linearIndependent_monoidHom H H).comp f hfinj
    have hsum0 : ∑ i : Fin m, a i • ((f i : H →* H) : H → H) = 0 := by
      ext c
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      have hallc := hall c
      rw [← Fin.sum_univ_eq_sum_range (fun i => a i * (σ ^ i) c) m] at hallc
      exact hallc
    have ha0_eq0 := Fintype.linearIndependent_iff.mp hli (fun i => a i) hsum0 ⟨0, hm0⟩
    simp only [ha0] at ha0_eq0
    exact one_ne_zero ha0_eq0
  obtain ⟨c, hc⟩ := hex
  set θ : H := ∑ i ∈ Finset.range m, a i * (σ ^ i) c with hθ_def
  have hfix : (u : H) * σ θ = θ := by
    have h1 : (u : H) * σ θ = ∑ i ∈ Finset.range m, a (i + 1) * (σ ^ (i + 1)) c := by
      rw [hθ_def, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ← mul_assoc, ha_step i, pow_succ', AlgEquiv.mul_apply]
    have h2 := Finset.sum_range_succ' (fun i => a i * (σ ^ i) c) m
    rw [Finset.sum_range_succ, ham, ha0, hσm, pow_zero, AlgEquiv.one_apply] at h2
    rw [h1, hθ_def]
    linear_combination -h2
  refine ⟨(Units.mk0 θ hc)⁻¹, ?_⟩
  change σ θ⁻¹ = (u : H) * θ⁻¹
  rw [map_inv₀]
  have hσθ_ne0 : σ θ ≠ 0 := (map_ne_zero_iff σ σ.injective).mpr hc
  field_simp [hc, hσθ_ne0]
  rw [mul_comm, hfix]

/-! ### Part 6b: Cyclic Tate Cohomology (`H0hat`, `H1hat`) & 6-Term Herbrand Quotient -/

section TateHerbrand

/-- `n`-th iterate of an additive equivalence `φ : M ≃+ M` as an `AddMonoidHom`. -/
def iterAddEquiv {M : Type*} [AddCommGroup M] (φ : M ≃+ M) : ℕ → (M →+ M)
  | 0 => AddMonoidHom.id M
  | n + 1 => φ.toAddMonoidHom.comp (iterAddEquiv φ n)

lemma iterAddEquiv_zero {M : Type*} [AddCommGroup M] (φ : M ≃+ M) (x : M) :
    iterAddEquiv φ 0 x = x := rfl

lemma iterAddEquiv_succ {M : Type*} [AddCommGroup M] (φ : M ≃+ M) (n : ℕ) (x : M) :
    iterAddEquiv φ (n + 1) x = φ (iterAddEquiv φ n x) := rfl

lemma iterAddEquiv_add {M : Type*} [AddCommGroup M] (φ : M ≃+ M) (m n : ℕ) (x : M) :
    iterAddEquiv φ (m + n) x = iterAddEquiv φ m (iterAddEquiv φ n x) := by
  induction m with
  | zero => simp [iterAddEquiv]
  | succ m ih => rw [Nat.succ_add, iterAddEquiv_succ, ih, iterAddEquiv_succ]

lemma iterAddEquiv_comm_apply {M : Type*} [AddCommGroup M] (φ : M ≃+ M) (n : ℕ) (x : M) :
    iterAddEquiv φ n (φ x) = φ (iterAddEquiv φ n x) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterAddEquiv_succ, ih, iterAddEquiv_succ]

/-- Difference operator `D φ = id - φ` on an `AddCommGroup M`. -/
def tateD {M : Type*} [AddCommGroup M] (φ : M ≃+ M) : M →+ M :=
  AddMonoidHom.id M - φ.toAddMonoidHom

/-- Norm operator `N_l φ = ∑_{i < l} φ^i` on an `AddCommGroup M`. -/
def tateN {M : Type*} [AddCommGroup M] (l : ℕ) (φ : M ≃+ M) : M →+ M :=
  ∑ i ∈ Finset.range l, iterAddEquiv φ i

lemma tateD_apply {M : Type*} [AddCommGroup M] (φ : M ≃+ M) (x : M) :
    tateD φ x = x - φ x := rfl

lemma tateN_apply {M : Type*} [AddCommGroup M] (l : ℕ) (φ : M ≃+ M) (x : M) :
    tateN l φ x = ∑ i ∈ Finset.range l, iterAddEquiv φ i x := by
  simp [tateN]

lemma tateN_comp_tateD {M : Type*} [AddCommGroup M] (l : ℕ) (φ : M ≃+ M)
    (hφ : ∀ x, iterAddEquiv φ l x = x) (x : M) :
    tateN l φ (tateD φ x) = 0 := by
  rw [tateN_apply, tateD_apply]
  have hsub : ∀ i, iterAddEquiv φ i (x - φ x) = iterAddEquiv φ i x - iterAddEquiv φ (i + 1) x := by
    intro i; rw [map_sub, iterAddEquiv_comm_apply, iterAddEquiv_succ]
  simp_rw [hsub]
  rw [Finset.sum_range_sub' (fun i => iterAddEquiv φ i x) l, iterAddEquiv_zero, hφ x, sub_self]

lemma tateD_comp_tateN {M : Type*} [AddCommGroup M] (l : ℕ) (φ : M ≃+ M)
    (hφ : ∀ x, iterAddEquiv φ l x = x) (x : M) :
    tateD φ (tateN l φ x) = 0 := by
  rw [tateD_apply, tateN_apply, map_sum, ← Finset.sum_sub_distrib]
  have hstep : ∀ i, iterAddEquiv φ i x - φ (iterAddEquiv φ i x) =
      iterAddEquiv φ i x - iterAddEquiv φ (i + 1) x := fun _ => rfl
  simp_rw [hstep]
  rw [Finset.sum_range_sub' (fun i => iterAddEquiv φ i x) l, iterAddEquiv_zero, hφ x, sub_self]

/-- Tate `H^0(C_l, M) = ker(D) / im(N)`. -/
abbrev H0hat {M : Type*} [AddCommGroup M] (l : ℕ) (φ : M ≃+ M) : Type _ :=
  (tateD φ).ker ⧸ (tateN l φ).range.comap (tateD φ).ker.subtype

/-- Tate `H^1(C_l, M) = ker(N) / im(D)`. -/
abbrev H1hat {M : Type*} [AddCommGroup M] (l : ℕ) (φ : M ≃+ M) : Type _ :=
  (tateN l φ).ker ⧸ (tateD φ).range.comap (tateN l φ).ker.subtype

/-- For ANY finite `M` with `φ^l = id`, `Nat.card (H0hat l φ) = Nat.card (H1hat l φ)` (Herbrand
quotient of a finite module is `1`). -/
theorem herbrand_finite_eq {M : Type*} [AddCommGroup M] [Finite M]
    (l : ℕ) (φ : M ≃+ M) (hφ : ∀ x, iterAddEquiv φ l x = x) :
    Nat.card (H0hat l φ) = Nat.card (H1hat l φ) := by
  have hN_le : (tateN l φ).range ≤ (tateD φ).ker := by
    rintro _ ⟨x, rfl⟩; exact tateD_comp_tateN l φ hφ x
  have hD_le : (tateD φ).range ≤ (tateN l φ).ker := by
    rintro _ ⟨x, rfl⟩; exact tateN_comp_tateD l φ hφ x
  have hN_card : Nat.card ((tateN l φ).range.comap (tateD φ).ker.subtype) =
      Nat.card (tateN l φ).range := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun x : (tateN l φ).range.comap (tateD φ).ker.subtype =>
        (⟨x.1.1, x.2⟩ : (tateN l φ).range)) ⟨?_, ?_⟩)
    · intro a b hab; exact Subtype.ext (Subtype.ext (Subtype.mk.inj hab))
    · intro y; exact ⟨⟨⟨y.1, hN_le y.2⟩, y.2⟩, rfl⟩
  have hD_card : Nat.card ((tateD φ).range.comap (tateN l φ).ker.subtype) =
      Nat.card (tateD φ).range := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun x : (tateD φ).range.comap (tateN l φ).ker.subtype =>
        (⟨x.1.1, x.2⟩ : (tateD φ).range)) ⟨?_, ?_⟩)
    · intro a b hab; exact Subtype.ext (Subtype.ext (Subtype.mk.inj hab))
    · intro y; exact ⟨⟨⟨y.1, hD_le y.2⟩, y.2⟩, rfl⟩
  have h0 : Nat.card (tateD φ).ker = Nat.card (H0hat l φ) * Nat.card (tateN l φ).range := by
    rw [← hN_card]
    exact AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
  have h1 : Nat.card (tateN l φ).ker = Nat.card (H1hat l φ) * Nat.card (tateD φ).range := by
    rw [← hD_card]
    exact AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
  have hM_D : Nat.card M = Nat.card (tateD φ).range * Nat.card (tateD φ).ker := by
    have e := QuotientAddGroup.quotientKerEquivRange (tateD φ)
    rw [← Nat.card_congr e.toEquiv]
    exact AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (tateD φ).ker
  have hM_N : Nat.card M = Nat.card (tateN l φ).range * Nat.card (tateN l φ).ker := by
    have e := QuotientAddGroup.quotientKerEquivRange (tateN l φ)
    rw [← Nat.card_congr e.toEquiv]
    exact AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (tateN l φ).ker
  have hprod : Nat.card (H0hat l φ) * (Nat.card (tateD φ).range * Nat.card (tateN l φ).range) =
      Nat.card (H1hat l φ) * (Nat.card (tateD φ).range * Nat.card (tateN l φ).range) := by
    calc Nat.card (H0hat l φ) * (Nat.card (tateD φ).range * Nat.card (tateN l φ).range)
        = Nat.card (tateD φ).range * (Nat.card (H0hat l φ) * Nat.card (tateN l φ).range) := by ring
      _ = Nat.card (tateD φ).range * Nat.card (tateD φ).ker := by rw [← h0]
      _ = Nat.card M := hM_D.symm
      _ = Nat.card (tateN l φ).range * Nat.card (tateN l φ).ker := hM_N
      _ = Nat.card (tateN l φ).range * (Nat.card (H1hat l φ) * Nat.card (tateD φ).range) := by rw [h1]
      _ = Nat.card (H1hat l φ) * (Nat.card (tateD φ).range * Nat.card (tateN l φ).range) := by ring
  have hpos : 0 < Nat.card (tateD φ).range * Nat.card (tateN l φ).range :=
    mul_pos Nat.card_pos Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos hprod

private lemma card_eq_card_range_mul_card_ker {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    [Finite X] [Finite Y] (f : X →+ Y) :
    Nat.card X = Nat.card f.range * Nat.card f.ker := by
  rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv]
  exact AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker

/-- Exactness helper: in any 6-term exact cycle of finite additive groups
`G0 → G1 → G2 → G3 → G4 → G5 → G0`, the alternating products of cardinalities are equal:
`|G0| * |G2| * |G4| = |G1| * |G3| * |G5|`. -/
private theorem six_term_exact_card_eq
    {G0 G1 G2 G3 G4 G5 : Type*}
    [AddCommGroup G0] [AddCommGroup G1] [AddCommGroup G2]
    [AddCommGroup G3] [AddCommGroup G4] [AddCommGroup G5]
    [Finite G0] [Finite G1] [Finite G2] [Finite G3] [Finite G4] [Finite G5]
    (f0 : G0 →+ G1) (f1 : G1 →+ G2) (f2 : G2 →+ G3)
    (f3 : G3 →+ G4) (f4 : G4 →+ G5) (f5 : G5 →+ G0)
    (e0 : f0.ker = f5.range) (e1 : f1.ker = f0.range) (e2 : f2.ker = f1.range)
    (e3 : f3.ker = f2.range) (e4 : f4.ker = f3.range) (e5 : f5.ker = f4.range) :
    Nat.card G0 * Nat.card G2 * Nat.card G4 = Nat.card G1 * Nat.card G3 * Nat.card G5 := by
  have h0 := card_eq_card_range_mul_card_ker f0; rw [e0] at h0
  have h1 := card_eq_card_range_mul_card_ker f1; rw [e1] at h1
  have h2 := card_eq_card_range_mul_card_ker f2; rw [e2] at h2
  have h3 := card_eq_card_range_mul_card_ker f3; rw [e3] at h3
  have h4 := card_eq_card_range_mul_card_ker f4; rw [e4] at h4
  have h5 := card_eq_card_range_mul_card_ker f5; rw [e5] at h5
  rw [h0, h1, h2, h3, h4, h5]
  ring

/-- **Herbrand Quotient Multiplicativity on a Short Exact Sequence (`herbrand_ses_mul`)**:
for any equivariant short exact sequence `0 → A →[i] B →[p] C → 0` of `C_l`-modules whose 6 Tate
cohomology groups are finite:
`Nat.card (H0hat l φB) * Nat.card (H1hat l φA) * Nat.card (H1hat l φC) =
 Nat.card (H1hat l φB) * Nat.card (H0hat l φA) * Nat.card (H0hat l φC)`. -/
theorem herbrand_ses_mul {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (l : ℕ) (φA : A ≃+ A) (φB : B ≃+ B) (φC : C ≃+ C)
    (_hφA : ∀ a, iterAddEquiv φA l a = a)
    (hφB : ∀ b, iterAddEquiv φB l b = b)
    (_hφC : ∀ c, iterAddEquiv φC l c = c)
    (i : A →+ B) (p : B →+ C)
    (hi : Function.Injective i) (hp : Function.Surjective p) (hexact : p.ker = i.range)
    (hi_eq : ∀ a, i (φA a) = φB (i a)) (hp_eq : ∀ b, p (φB b) = φC (p b))
    [Finite (H0hat l φA)] [Finite (H0hat l φB)] [Finite (H0hat l φC)]
    [Finite (H1hat l φA)] [Finite (H1hat l φB)] [Finite (H1hat l φC)] :
    Nat.card (H0hat l φB) * Nat.card (H1hat l φA) * Nat.card (H1hat l φC) =
      Nat.card (H1hat l φB) * Nat.card (H0hat l φA) * Nat.card (H0hat l φC) := by
  classical
  have hi_iter : ∀ n a, i (iterAddEquiv φA n a) = iterAddEquiv φB n (i a) := fun n => by
    induction n with
    | zero => intro _; rfl
    | succ n ih => intro a; rw [iterAddEquiv_succ, hi_eq, ih, iterAddEquiv_succ]
  have hp_iter : ∀ n b, p (iterAddEquiv φB n b) = iterAddEquiv φC n (p b) := fun n => by
    induction n with
    | zero => intro _; rfl
    | succ n ih => intro b; rw [iterAddEquiv_succ, hp_eq, ih, iterAddEquiv_succ]
  have hiD : ∀ a, i (tateD φA a) = tateD φB (i a) := fun a => by
    rw [tateD_apply, map_sub, hi_eq, tateD_apply]
  have hpD : ∀ b, p (tateD φB b) = tateD φC (p b) := fun b => by
    rw [tateD_apply, map_sub, hp_eq, tateD_apply]
  have hiN : ∀ a, i (tateN l φA a) = tateN l φB (i a) := fun a => by
    simp only [tateN_apply, map_sum, hi_iter]
  have hpN : ∀ b, p (tateN l φB b) = tateN l φC (p b) := fun b => by
    simp only [tateN_apply, map_sum, hp_iter]
  -- Construct the 6 homomorphisms in the periodic exact sequence:
  -- H0 A →[i0] H0 B →[p0] H0 C →[δ0] H1 A →[i1] H1 B →[p1] H1 C →[δ1] H0 A
  let mk0A : (tateD φA).ker →+ H0hat l φA := QuotientAddGroup.mk' _
  let mk0B : (tateD φB).ker →+ H0hat l φB := QuotientAddGroup.mk' _
  let mk0C : (tateD φC).ker →+ H0hat l φC := QuotientAddGroup.mk' _
  let mk1A : (tateN l φA).ker →+ H1hat l φA := QuotientAddGroup.mk' _
  let mk1B : (tateN l φB).ker →+ H1hat l φB := QuotientAddGroup.mk' _
  let mk1C : (tateN l φC).ker →+ H1hat l φC := QuotientAddGroup.mk' _
  let i0 : H0hat l φA →+ H0hat l φB :=
    QuotientAddGroup.lift _ (mk0B.comp (AddMonoidHom.mk'
      (fun a : (tateD φA).ker => ⟨i a.1, by rw [AddMonoidHom.mem_ker, ← hiD, a.2, map_zero]⟩)
      (fun _ _ => Subtype.ext (map_add i _ _)))) (by
      rintro a ⟨a0, ha0⟩
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply]
      simp only [mk0B, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
      exact ⟨i a0, by rw [← hiN, ha0]; rfl⟩)
  let p0 : H0hat l φB →+ H0hat l φC :=
    QuotientAddGroup.lift _ (mk0C.comp (AddMonoidHom.mk'
      (fun b : (tateD φB).ker => ⟨p b.1, by rw [AddMonoidHom.mem_ker, ← hpD, b.2, map_zero]⟩)
      (fun _ _ => Subtype.ext (map_add p _ _)))) (by
      rintro b ⟨b0, hb0⟩
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply]
      simp only [mk0C, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
      exact ⟨p b0, by rw [← hpN, hb0]; rfl⟩)
  let i1 : H1hat l φA →+ H1hat l φB :=
    QuotientAddGroup.lift _ (mk1B.comp (AddMonoidHom.mk'
      (fun a : (tateN l φA).ker => ⟨i a.1, by rw [AddMonoidHom.mem_ker, ← hiN, a.2, map_zero]⟩)
      (fun _ _ => Subtype.ext (map_add i _ _)))) (by
      rintro a ⟨a0, ha0⟩
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply]
      simp only [mk1B, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
      exact ⟨i a0, by rw [← hiD, ha0]; rfl⟩)
  let p1 : H1hat l φB →+ H1hat l φC :=
    QuotientAddGroup.lift _ (mk1C.comp (AddMonoidHom.mk'
      (fun b : (tateN l φB).ker => ⟨p b.1, by rw [AddMonoidHom.mem_ker, ← hpN, b.2, map_zero]⟩)
      (fun _ _ => Subtype.ext (map_add p _ _)))) (by
      rintro b ⟨b0, hb0⟩
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply]
      simp only [mk1C, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
      exact ⟨p b0, by rw [← hpD, hb0]; rfl⟩)
  -- Connecting map `δ0 : H0 C →+ H1 A` via `D`
  have hδ0_ex : ∀ c : (tateD φC).ker, ∃ (b : B) (a : (tateN l φA).ker), p b = c.1 ∧ i a.1 = tateD φB b := by
    intro c
    obtain ⟨b, hb⟩ := hp c.1
    have hmem : tateD φB b ∈ i.range := by
      rw [← hexact, AddMonoidHom.mem_ker, hpD, hb]; exact c.2
    obtain ⟨a, ha⟩ := hmem
    have haN : tateN l φA a = 0 := hi (by rw [hiN, ha, tateN_comp_tateD l φB hφB, map_zero])
    exact ⟨b, ⟨a, haN⟩, hb, ha⟩
  have hδ0_wd : ∀ (c : (tateD φC).ker) (b₁ b₂ : B) (a₁ a₂ : (tateN l φA).ker),
      p b₁ = c.1 → i a₁.1 = tateD φB b₁ → p b₂ = c.1 → i a₂.1 = tateD φB b₂ →
      mk1A a₁ = mk1A a₂ := by
    intro c b₁ b₂ a₁ a₂ hb₁ ha₁ hb₂ ha₂
    have hdiff : b₁ - b₂ ∈ i.range := by
      rw [← hexact, AddMonoidHom.mem_ker, map_sub, hb₁, hb₂, sub_self]
    obtain ⟨a0, ha0⟩ := hdiff
    rw [← sub_eq_zero, ← map_sub]
    simp only [mk1A, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    refine ⟨a0, hi ?_⟩
    rw [hiD, ha0, map_sub]
    change (tateD φB) b₁ - (tateD φB) b₂ = i (a₁.1 - a₂.1)
    rw [map_sub, ha₁, ha₂]
  let δ0_raw : (tateD φC).ker →+ H1hat l φA :=
    AddMonoidHom.mk' (fun c => mk1A (Classical.choose (Classical.choose_spec (hδ0_ex c)))) (by
      intro c₁ c₂
      set b₁ := Classical.choose (hδ0_ex c₁)
      set a₁ := Classical.choose (Classical.choose_spec (hδ0_ex c₁))
      obtain ⟨hb₁, ha₁⟩ := Classical.choose_spec (Classical.choose_spec (hδ0_ex c₁))
      set b₂ := Classical.choose (hδ0_ex c₂)
      set a₂ := Classical.choose (Classical.choose_spec (hδ0_ex c₂))
      obtain ⟨hb₂, ha₂⟩ := Classical.choose_spec (Classical.choose_spec (hδ0_ex c₂))
      set b₁₂ := Classical.choose (hδ0_ex (c₁ + c₂))
      set a₁₂ := Classical.choose (Classical.choose_spec (hδ0_ex (c₁ + c₂)))
      obtain ⟨hb₁₂, ha₁₂⟩ := Classical.choose_spec (Classical.choose_spec (hδ0_ex (c₁ + c₂)))
      rw [← map_add]
      exact hδ0_wd (c₁ + c₂) b₁₂ (b₁ + b₂) a₁₂ (a₁ + a₂) hb₁₂ ha₁₂
        (by rw [map_add, hb₁, hb₂]; rfl) (by rw [AddSubgroup.coe_add, map_add, ha₁, ha₂, map_add]))
  have hδ0_spec : ∀ (c : (tateD φC).ker) (b : B) (a : (tateN l φA).ker),
      p b = c.1 → i a.1 = tateD φB b → δ0_raw c = mk1A a := fun c b a hb ha =>
    hδ0_wd c _ b _ a (Classical.choose_spec (Classical.choose_spec (hδ0_ex c))).1
      (Classical.choose_spec (Classical.choose_spec (hδ0_ex c))).2 hb ha
  let δ0 : H0hat l φC →+ H1hat l φA :=
    QuotientAddGroup.lift _ δ0_raw (by
      rintro c ⟨c0, hc0⟩
      obtain ⟨b0, hb0⟩ := hp c0
      have hpb : p (tateN l φB b0) = c.1 := (hpN b0).trans (by rw [hb0]; exact hc0)
      have hDb : i (0 : A) = tateD φB (tateN l φB b0) := by
        rw [map_zero, tateD_comp_tateN l φB hφB]
      rw [AddMonoidHom.mem_ker, hδ0_spec c (tateN l φB b0) 0 hpb hDb, map_zero])
  -- Connecting map `δ1 : H1 C →+ H0 A` via `N`
  have hδ1_ex : ∀ c : (tateN l φC).ker, ∃ (b : B) (a : (tateD φA).ker), p b = c.1 ∧ i a.1 = tateN l φB b := by
    intro c
    obtain ⟨b, hb⟩ := hp c.1
    have hmem : tateN l φB b ∈ i.range := by
      rw [← hexact, AddMonoidHom.mem_ker, hpN, hb]; exact c.2
    obtain ⟨a, ha⟩ := hmem
    have haD : tateD φA a = 0 := hi (by rw [hiD, ha, tateD_comp_tateN l φB hφB, map_zero])
    exact ⟨b, ⟨a, haD⟩, hb, ha⟩
  have hδ1_wd : ∀ (c : (tateN l φC).ker) (b₁ b₂ : B) (a₁ a₂ : (tateD φA).ker),
      p b₁ = c.1 → i a₁.1 = tateN l φB b₁ → p b₂ = c.1 → i a₂.1 = tateN l φB b₂ →
      mk0A a₁ = mk0A a₂ := by
    intro c b₁ b₂ a₁ a₂ hb₁ ha₁ hb₂ ha₂
    have hdiff : b₁ - b₂ ∈ i.range := by
      rw [← hexact, AddMonoidHom.mem_ker, map_sub, hb₁, hb₂, sub_self]
    obtain ⟨a0, ha0⟩ := hdiff
    rw [← sub_eq_zero, ← map_sub]
    simp only [mk0A, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    refine ⟨a0, hi ?_⟩
    rw [hiN, ha0, map_sub]
    change (tateN l φB) b₁ - (tateN l φB) b₂ = i (a₁.1 - a₂.1)
    rw [map_sub, ha₁, ha₂]
  let δ1_raw : (tateN l φC).ker →+ H0hat l φA :=
    AddMonoidHom.mk' (fun c => mk0A (Classical.choose (Classical.choose_spec (hδ1_ex c)))) (by
      intro c₁ c₂
      set b₁ := Classical.choose (hδ1_ex c₁)
      set a₁ := Classical.choose (Classical.choose_spec (hδ1_ex c₁))
      obtain ⟨hb₁, ha₁⟩ := Classical.choose_spec (Classical.choose_spec (hδ1_ex c₁))
      set b₂ := Classical.choose (hδ1_ex c₂)
      set a₂ := Classical.choose (Classical.choose_spec (hδ1_ex c₂))
      obtain ⟨hb₂, ha₂⟩ := Classical.choose_spec (Classical.choose_spec (hδ1_ex c₂))
      set b₁₂ := Classical.choose (hδ1_ex (c₁ + c₂))
      set a₁₂ := Classical.choose (Classical.choose_spec (hδ1_ex (c₁ + c₂)))
      obtain ⟨hb₁₂, ha₁₂⟩ := Classical.choose_spec (Classical.choose_spec (hδ1_ex (c₁ + c₂)))
      rw [← map_add]
      exact hδ1_wd (c₁ + c₂) b₁₂ (b₁ + b₂) a₁₂ (a₁ + a₂) hb₁₂ ha₁₂
        (by rw [map_add, hb₁, hb₂]; rfl) (by rw [AddSubgroup.coe_add, map_add, ha₁, ha₂, map_add]))
  have hδ1_spec : ∀ (c : (tateN l φC).ker) (b : B) (a : (tateD φA).ker),
      p b = c.1 → i a.1 = tateN l φB b → δ1_raw c = mk0A a := fun c b a hb ha =>
    hδ1_wd c _ b _ a (Classical.choose_spec (Classical.choose_spec (hδ1_ex c))).1
      (Classical.choose_spec (Classical.choose_spec (hδ1_ex c))).2 hb ha
  let δ1 : H1hat l φC →+ H0hat l φA :=
    QuotientAddGroup.lift _ δ1_raw (by
      rintro c ⟨c0, hc0⟩
      obtain ⟨b0, hb0⟩ := hp c0
      have hpb : p (tateD φB b0) = c.1 := (hpD b0).trans (by rw [hb0]; exact hc0)
      have hNb : i (0 : A) = tateN l φB (tateD φB b0) := by
        rw [map_zero, tateN_comp_tateD l φB hφB]
      rw [AddMonoidHom.mem_ker, hδ1_spec c (tateD φB b0) 0 hpb hNb, map_zero])
  -- Verify exactness at all 6 nodes
  have ex_i0 : i0.ker = δ1.range := by
    ext x; obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    constructor
    · intro h0
      have hmem : (⟨i a.1, by rw [AddMonoidHom.mem_ker, ← hiD, a.2, map_zero]⟩ : (tateD φB).ker) ∈
          (tateN l φB).range.comap (tateD φB).ker.subtype :=
        (QuotientAddGroup.eq_zero_iff _).mp h0
      obtain ⟨b, hb⟩ := hmem
      have hpc : tateN l φC (p b) = 0 := by
        rw [← hpN, hb]; exact AddMonoidHom.mem_ker.mp (hexact.symm ▸ ⟨a.1, rfl⟩)
      refine ⟨mk1C ⟨p b, hpc⟩, ?_⟩
      exact hδ1_spec ⟨p b, hpc⟩ b a rfl hb.symm
    · rintro ⟨y, hy⟩
      obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective _ y
      obtain ⟨b, a', hb, ha'⟩ := hδ1_ex c
      have heq : mk0A a' = mk0A a := (hδ1_spec c b a' hb ha').symm.trans hy
      have hdiff : a - a' ∈ (tateN l φA).range.comap (tateD φA).ker.subtype :=
        (QuotientAddGroup.eq_zero_iff _).mp (by
          change mk0A (a - a') = 0
          rw [map_sub, heq, sub_self])
      obtain ⟨a0, ha0⟩ := hdiff
      change mk0B ⟨i a.1, _⟩ = 0
      simp only [mk0B, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
      refine ⟨i a0 + b, ?_⟩
      change tateN l φB (i a0 + b) = i a.1
      rw [map_add, ← hiN, ha0, ← ha', ← map_add]
      congr 1; exact sub_add_cancel a.1 a'.1
  have ex_p0 : p0.ker = i0.range := by
    ext x; obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    constructor
    · intro h0
      obtain ⟨c0, hc0⟩ := (QuotientAddGroup.eq_zero_iff _).mp h0
      obtain ⟨b0, hb0⟩ := hp c0
      have hmem : b.1 - tateN l φB b0 ∈ i.range := by
        rw [← hexact, AddMonoidHom.mem_ker, map_sub, hpN, hb0]
        change p b.1 - tateN l φC c0 = 0
        rw [hc0]; exact sub_self _
      obtain ⟨a, ha⟩ := hmem
      have haD : tateD φA a = 0 := hi (by
        rw [hiD, ha, map_sub, b.2, tateD_comp_tateN l φB hφB, sub_self, map_zero])
      refine ⟨mk0A ⟨a, haD⟩, ?_⟩
      change mk0B ⟨i a, _⟩ = mk0B b
      rw [← sub_eq_zero, ← map_sub]
      simp only [mk0B, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
      refine ⟨-b0, ?_⟩
      change tateN l φB (-b0) = i a - b.1
      rw [map_neg, ha]; abel
    · rintro ⟨y, hy⟩
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective _ y
      rw [← hy]
      change mk0C ⟨p (i a.1), _⟩ = 0
      have hpia : p (i a.1) = 0 := AddMonoidHom.mem_ker.mp (hexact.symm ▸ ⟨a.1, rfl⟩)
      rw [← map_zero mk0C]; congr 1; exact Subtype.ext hpia
  have ex_δ0 : δ0.ker = p0.range := by
    ext x; obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    constructor
    · intro h0
      obtain ⟨b, a, hb, ha⟩ := hδ0_ex c
      have ha0 : mk1A a = 0 := (hδ0_spec c b a hb ha).symm.trans h0
      obtain ⟨a0, ha0'⟩ := (QuotientAddGroup.eq_zero_iff _).mp ha0
      have hDb' : tateD φB (b - i a0) = 0 := by
        rw [map_sub, ← hiD, ha0', ← ha]; exact sub_self _
      refine ⟨mk0B ⟨b - i a0, hDb'⟩, ?_⟩
      change mk0C ⟨p (b - i a0), _⟩ = mk0C c
      congr 1; apply Subtype.ext
      have hpia : p (i a0) = 0 := AddMonoidHom.mem_ker.mp (hexact.symm ▸ ⟨a0, rfl⟩)
      change p (b - i a0) = c.1
      rw [map_sub, hpia, sub_zero, hb]
    · rintro ⟨y, hy⟩
      obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective _ y
      rw [← hy]
      exact hδ0_spec ⟨p b.1, _⟩ b.1 0 rfl (by simp; exact b.2.symm)
  have ex_i1 : i1.ker = δ0.range := by
    ext x; obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    constructor
    · intro h0
      obtain ⟨b, hb⟩ := (QuotientAddGroup.eq_zero_iff _).mp h0
      have hpc : tateD φC (p b) = 0 := by
        rw [← hpD, hb]; exact AddMonoidHom.mem_ker.mp (hexact.symm ▸ ⟨a.1, rfl⟩)
      refine ⟨mk0C ⟨p b, hpc⟩, ?_⟩
      exact hδ0_spec ⟨p b, hpc⟩ b a rfl hb.symm
    · rintro ⟨y, hy⟩
      obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective _ y
      obtain ⟨b, a', hb, ha'⟩ := hδ0_ex c
      have heq : mk1A a' = mk1A a := (hδ0_spec c b a' hb ha').symm.trans hy
      obtain ⟨a0, ha0⟩ := (QuotientAddGroup.eq_zero_iff _).mp (by
        change mk1A (a - a') = 0
        rw [map_sub, heq, sub_self])
      change mk1B ⟨i a.1, _⟩ = 0
      simp only [mk1B, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
      refine ⟨i a0 + b, ?_⟩
      change tateD φB (i a0 + b) = i a.1
      rw [map_add, ← hiD, ha0, ← ha', ← map_add]
      congr 1; exact sub_add_cancel a.1 a'.1
  have ex_p1 : p1.ker = i1.range := by
    ext x; obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    constructor
    · intro h0
      obtain ⟨c0, hc0⟩ := (QuotientAddGroup.eq_zero_iff _).mp h0
      obtain ⟨b0, hb0⟩ := hp c0
      have hmem : b.1 - tateD φB b0 ∈ i.range := by
        rw [← hexact, AddMonoidHom.mem_ker, map_sub, hpD, hb0]
        change p b.1 - tateD φC c0 = 0
        rw [hc0]; exact sub_self _
      obtain ⟨a, ha⟩ := hmem
      have haN : tateN l φA a = 0 := hi (by
        rw [hiN, ha, map_sub, b.2, tateN_comp_tateD l φB hφB, sub_self, map_zero])
      refine ⟨mk1A ⟨a, haN⟩, ?_⟩
      change mk1B ⟨i a, _⟩ = mk1B b
      rw [← sub_eq_zero, ← map_sub]
      simp only [mk1B, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
      refine ⟨-b0, ?_⟩
      change tateD φB (-b0) = i a - b.1
      rw [map_neg, ha]; abel
    · rintro ⟨y, hy⟩
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective _ y
      rw [← hy]
      change mk1C ⟨p (i a.1), _⟩ = 0
      have hpia : p (i a.1) = 0 := AddMonoidHom.mem_ker.mp (hexact.symm ▸ ⟨a.1, rfl⟩)
      rw [← map_zero mk1C]; congr 1; exact Subtype.ext hpia
  have ex_δ1 : δ1.ker = p1.range := by
    ext x; obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    constructor
    · intro h0
      obtain ⟨b, a, hb, ha⟩ := hδ1_ex c
      have ha0 : mk0A a = 0 := (hδ1_spec c b a hb ha).symm.trans h0
      obtain ⟨a0, ha0'⟩ := (QuotientAddGroup.eq_zero_iff _).mp ha0
      have hNb' : tateN l φB (b - i a0) = 0 := by
        rw [map_sub, ← hiN, ha0', ← ha]; exact sub_self _
      refine ⟨mk1B ⟨b - i a0, hNb'⟩, ?_⟩
      change mk1C ⟨p (b - i a0), _⟩ = mk1C c
      congr 1; apply Subtype.ext
      have hpia : p (i a0) = 0 := AddMonoidHom.mem_ker.mp (hexact.symm ▸ ⟨a0, rfl⟩)
      change p (b - i a0) = c.1
      rw [map_sub, hpia, sub_zero, hb]
    · rintro ⟨y, hy⟩
      obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective _ y
      rw [← hy]
      exact hδ1_spec ⟨p b.1, _⟩ b.1 0 rfl (by simp; exact b.2.symm)
  have h6 := six_term_exact_card_eq i0 p0 δ0 i1 p1 δ1 ex_i0 ex_p0 ex_δ0 ex_i1 ex_p1 ex_δ1
  linarith

/-- For a finitely generated free `ℤ`-module `M` of rank `d` and `l > 0`,
`Nat.card (M ⧸ (nsmulAddMonoidHom l).range) = l ^ d` (and it is finite). -/
private theorem card_mod_l_free {M : Type*} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    {l : ℕ} (hl : 0 < l) :
    Finite (M ⧸ (nsmulAddMonoidHom l : M →+ M).range) ∧
      Nat.card (M ⧸ (nsmulAddMonoidHom l : M →+ M).range) = l ^ Module.finrank ℤ M := by
  classical
  have : NeZero l := ⟨hl.ne'⟩
  let B := Module.Free.chooseBasis ℤ M
  let ι := Module.Free.ChooseBasisIndex ℤ M
  have hcard : Fintype.card ι = Module.finrank ℤ M := (Module.finrank_eq_card_basis B).symm
  let f : M →+ (ι → ZMod l) :=
    AddMonoidHom.mk' (fun m i => (B.repr m i : ZMod l)) (fun a b => by
      ext i; simp only [map_add, Finsupp.add_apply, Int.cast_add, Pi.add_apply])
  have hf_surj : Function.Surjective f := by
    intro g
    refine ⟨∑ i : ι, ((g i).val : ℤ) • B i, ?_⟩
    ext j
    change (B.repr (∑ i : ι, ((g i).val : ℤ) • B i) j : ZMod l) = g j
    rw [map_sum, Finsupp.finsetSum_apply]
    simp only [map_zsmul, Finsupp.smul_apply, B.repr_self, Finsupp.single_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
      Int.cast_natCast, ZMod.natCast_zmod_val]
  have hf_ker : f.ker = (nsmulAddMonoidHom l : M →+ M).range := by
    ext m
    simp only [AddMonoidHom.mem_ker, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
    constructor
    · intro hm
      have hdiv : ∀ i : ι, (l : ℤ) ∣ B.repr m i := fun i =>
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ l).mp (congrFun hm i)
      choose c hc using hdiv
      refine ⟨∑ i : ι, c i • B i, ?_⟩
      symm
      rw [← B.sum_repr m, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hc i, mul_smul, natCast_zsmul]
    · rintro ⟨x, rfl⟩
      ext i
      change (B.repr (l • x) i : ZMod l) = 0
      rw [← natCast_zsmul, map_zsmul, Finsupp.smul_apply, smul_eq_mul, Int.cast_mul,
        Int.cast_natCast, ZMod.natCast_self, zero_mul]
  let e : (M ⧸ (nsmulAddMonoidHom l : M →+ M).range) ≃+ (ι → ZMod l) :=
    (QuotientAddGroup.quotientAddEquivOfEq hf_ker.symm).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective f hf_surj)
  refine ⟨Finite.of_equiv (ι → ZMod l) e.symm.toEquiv, ?_⟩
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, hcard]

/-- Polynomial identity in `ℤ[X]`: for prime `l`, `(∑ i ∈ range l, X ^ i) ∣ (∏ j ∈ Ico 1 l, (1 - X ^ j)) - l`. -/
private theorem poly_cyclotomic_dvd_prod_one_sub_pow (l : ℕ) [Fact l.Prime] :
    (∑ i ∈ Finset.range l, (X : Polynomial ℤ) ^ i) ∣
      (∏ j ∈ Finset.Ico 1 l, (1 - (X : Polynomial ℤ) ^ j)) - C (l : ℤ) := by
  have hl : l.Prime := Fact.out
  set Φ : Polynomial ℤ := ∑ i ∈ Finset.range l, (X : Polynomial ℤ) ^ i
  set P : Polynomial ℤ := (∏ j ∈ Finset.Ico 1 l, (1 - (X : Polynomial ℤ) ^ j)) - C (l : ℤ)
  have hΦ_eq : Φ = Polynomial.cyclotomic l ℤ := (Polynomial.cyclotomic_prime ℤ l).symm
  have hΦ_monic : Φ.Monic := hΦ_eq ▸ Polynomial.cyclotomic.monic l ℤ
  -- Perform monic division `P = Φ * q + r` in `ℤ[X]` and show `r = 0` by checking in `ℂ`
  set q := P /ₘ Φ
  set r := P %ₘ Φ
  have hdiv : P = r + Φ * q := (Polynomial.modByMonic_add_div P Φ).symm
  suffices hr0 : r = 0 by
    refine ⟨q, ?_⟩; rw [hdiv, hr0, zero_add]
  have hr_deg : r.degree < Φ.degree := Polynomial.degree_modByMonic_lt P hΦ_monic
  -- Over `ℚ`, `Φ.map (Int.castRingHom ℚ) = cyclotomic l ℚ` is irreducible, and `P.map _` vanishes
  -- at a primitive `l`-th root of unity in `ℂ`, hence `Φ_ℚ ∣ P_ℚ`, so `r_ℚ = 0`, so `r = 0`!
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / l)
  have hζ : IsPrimitiveRoot ζ l := Complex.isPrimitiveRoot_exp l hl.ne_zero
  have hΦ_ζ : aeval ζ (Φ.map (Int.castRingHom ℚ)) = 0 := by
    rw [hΦ_eq, Polynomial.map_cyclotomic, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
      Polynomial.map_cyclotomic]
    exact Polynomial.isRoot_cyclotomic_iff.mpr hζ
  have hP_ζ : aeval ζ (P.map (Int.castRingHom ℚ)) = 0 := by
    have hprod_eq : ∏ j ∈ Finset.Ico 1 l, (1 - ζ ^ j) = (l : ℂ) := by
      have h1 : (Polynomial.X : Polynomial ℂ) ^ l - 1 =
          (Polynomial.X - 1) * (∑ i ∈ Finset.range l, (Polynomial.X : Polynomial ℂ) ^ i) := by
        rw [mul_comm, geom_sum_mul]
      have h2 : (Polynomial.X : Polynomial ℂ) ^ l - 1 =
          ∏ j ∈ Finset.range l, (Polynomial.X - Polynomial.C (ζ ^ j)) := by
        have hmon : ((Polynomial.X : Polynomial ℂ) ^ l - 1).Monic :=
          Polynomial.monic_X_pow_sub_C 1 hl.ne_zero
        have hdeg : ((Polynomial.X : Polynomial ℂ) ^ l - 1).natDegree = l :=
          Polynomial.natDegree_X_pow_sub_C
        have hcard : (Finset.image (fun j : ℕ => ζ ^ j) (Finset.range l)).card = l := by
          rw [Finset.card_image_of_injOn, Finset.card_range]
          intro i hi j hj hij
          exact hζ.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
        have hsub : (Finset.image (fun j : ℕ => ζ ^ j) (Finset.range l)).val ⊆
            ((Polynomial.X : Polynomial ℂ) ^ l - 1).roots := by
          intro x hx; rw [Finset.mem_val, Finset.mem_image] at hx
          obtain ⟨j, _, rfl⟩ := hx
          rw [Polynomial.mem_roots hmon.ne_zero, Polynomial.IsRoot.def, Polynomial.eval_sub,
            Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one, ← pow_mul, mul_comm,
            pow_mul, hζ.pow_eq_one, one_pow, sub_self]
        have hroots : ((Polynomial.X : Polynomial ℂ) ^ l - 1).roots =
            (Finset.image (fun j : ℕ => ζ ^ j) (Finset.range l)).val :=
          (Multiset.eq_of_le_of_card_le ((Multiset.le_iff_subset (Finset.nodup _)).mpr hsub)
            (by rw [← Finset.card_def, hcard]; exact (Polynomial.card_roots' _).trans_eq hdeg)).symm
        rw [← Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon
          (by rw [hroots, ← Finset.card_def, hcard, hdeg]), hroots]
        change (Finset.image (fun j => ζ ^ j) (Finset.range l)).prod
            (fun x => Polynomial.X - Polynomial.C x) = _
        rw [Finset.prod_image]
        intro i hi j hj hij
        exact hζ.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
      rw [Finset.prod_range_eq_mul_Ico _ hl.pos, pow_zero, map_one] at h2
      have hcancel : (∑ i ∈ Finset.range l, (Polynomial.X : Polynomial ℂ) ^ i) =
          ∏ j ∈ Finset.Ico 1 l, (Polynomial.X - Polynomial.C (ζ ^ j)) :=
        mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero (1 : ℂ)) (h1.symm.trans h2)
      have hev := congrArg (Polynomial.eval (1 : ℂ)) hcancel
      simp only [Polynomial.eval_finsetSum, Polynomial.eval_pow, Polynomial.eval_X, one_pow,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Polynomial.eval_prod,
        Polynomial.eval_sub, Polynomial.eval_C] at hev
      exact hev.symm
    simp [P, Polynomial.map_prod, hprod_eq]
  have hr_ζ : aeval ζ (r.map (Int.castRingHom ℚ)) = 0 := by
    have hdivQ : P.map (Int.castRingHom ℚ) =
        r.map (Int.castRingHom ℚ) + Φ.map (Int.castRingHom ℚ) * q.map (Int.castRingHom ℚ) := by
      rw [hdiv, Polynomial.map_add, Polynomial.map_mul]
    have hev := congrArg (aeval ζ) hdivQ
    rw [map_add, map_mul, hP_ζ, hΦ_ζ, zero_mul, add_zero] at hev
    exact hev.symm
  have hmin : minpoly ℚ ζ = Φ.map (Int.castRingHom ℚ) := by
    have hcyc_ζ : aeval ζ (Polynomial.cyclotomic l ℚ) = 0 := by
      rw [← Polynomial.map_cyclotomic l (Int.castRingHom ℚ), ← hΦ_eq]; exact hΦ_ζ
    rw [hΦ_eq, Polynomial.map_cyclotomic]
    exact (minpoly.eq_of_irreducible_of_monic (Polynomial.cyclotomic.irreducible_rat hl.pos)
      hcyc_ζ (Polynomial.cyclotomic.monic l ℚ)).symm
  have hdvdQ : Φ.map (Int.castRingHom ℚ) ∣ r.map (Int.castRingHom ℚ) := by
    rw [← hmin]; exact minpoly.dvd ℚ ζ hr_ζ
  have hrQ0 : r.map (Int.castRingHom ℚ) = 0 := by
    by_contra hne
    have hle := Polynomial.degree_le_of_dvd hdvdQ hne
    have hdeg_r : (r.map (Int.castRingHom ℚ)).degree = r.degree :=
      Polynomial.degree_map_eq_of_injective Int.cast_injective r
    have hdeg_Φ : (Φ.map (Int.castRingHom ℚ)).degree = Φ.degree :=
      Polynomial.degree_map_eq_of_injective Int.cast_injective Φ
    rw [hdeg_r, hdeg_Φ] at hle
    exact not_lt_of_ge hle hr_deg
  exact Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective (by simpa using hrQ0)

/-- Core `(1 - σ)^{l-1} M = l M` lemma: for a finitely generated free `ℤ`-module `M` with
`φ : M ≃+ M`, `φ^l = id`, and `tateN l φ = 0` (`l` prime):
- `H0hat l φ` is trivial (`Nat.card (H0hat l φ) = 1`),
- `H1hat l φ` is finite and `(Nat.card (H1hat l φ)) ^ (l - 1) = l ^ Module.finrank ℤ M`! -/
private theorem tate_norm_zero_free_card {M : Type*} [AddCommGroup M]
    [Module.Free ℤ M] [Module.Finite ℤ M]
    {l : ℕ} [Fact l.Prime] (φ : M ≃+ M) (hφ : ∀ x, iterAddEquiv φ l x = x)
    (hN0 : ∀ x, tateN l φ x = 0) :
    Finite (H0hat l φ) ∧ Finite (H1hat l φ) ∧
      Nat.card (H0hat l φ) = 1 ∧
      Nat.card (H1hat l φ) ^ (l - 1) = l ^ Module.finrank ℤ M := by
  classical
  have hl : l.Prime := Fact.out
  have : NeZero l := ⟨hl.ne_zero⟩
  -- First: `tateD φ` is injective, so `ker (tateD φ) = ⊥` and `H0hat l φ` is subsingleton!
  have hD_inj : Function.Injective (tateD φ) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hfix : φ x = x := (sub_eq_zero.mp hx).symm
    have hiter : ∀ i : ℕ, iterAddEquiv φ i x = x := fun i => by
      induction i with
      | zero => rfl
      | succ i ih => rw [iterAddEquiv_succ, ih, hfix]
    have hlx : l • x = 0 := by
      have h0 := hN0 x
      rw [tateN_apply] at h0
      simp only [hiter, Finset.sum_const, Finset.card_range] at h0
      exact h0
    have hlz : (l : ℤ) • x = 0 := by rw [natCast_zsmul]; exact hlx
    exact (smul_eq_zero.mp hlz).resolve_left (Int.natCast_ne_zero.mpr hl.ne_zero)
  have h0_sub : Subsingleton (H0hat l φ) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective _ a
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective _ b
    congr 1; apply Subtype.ext
    exact (hD_inj (x.2.trans (map_zero _).symm)).trans (hD_inj (y.2.trans (map_zero _).symm)).symm
  have h0_fin : Finite (H0hat l φ) := inferInstance
  have h0_card : Nat.card (H0hat l φ) = 1 := Nat.card_unique
  -- Next: `tateN l φ = 0` means `(tateN l φ).ker = ⊤`, so `H1hat l φ ≃+ M ⧸ (tateD φ).range`
  have hkerN : (tateN l φ).ker = ⊤ := by
    ext x; simp [hN0 x]
  -- Define `D_pow n : M →+ M` as `n`-th iterate of `tateD φ`
  let D_pow : ℕ → (M →+ M) := fun n => Nat.rec (AddMonoidHom.id M) (fun _ f => (tateD φ).comp f) n
  have hD_pow_inj : ∀ n, Function.Injective (D_pow n) := fun n => by
    induction n with
    | zero => exact Function.injective_id
    | succ n ih => exact hD_inj.comp ih
  -- Show `(D_pow (l - 1)).range = l • ⊤`!
  -- Define `u j := ∑ i ∈ range j, φ^i` for `1 ≤ j < l`; each `u j` is an automorphism of `M`!
  let uHom : ℕ → (M →+ M) := fun j => ∑ i ∈ Finset.range j, iterAddEquiv φ i
  have huHom_apply : ∀ (j : ℕ) (x : M), uHom j x = ∑ i ∈ Finset.range j, iterAddEquiv φ i x := by
    intro j x; simp [uHom]
  have hiter_mod : ∀ (n : ℕ) (x : M), iterAddEquiv φ n x = iterAddEquiv φ (n % l) x := by
    intro n x
    have hdiv := Nat.div_add_mod n l
    conv_lhs => rw [← hdiv]
    induction (n / l) with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ, add_assoc, add_comm l, ← add_assoc, iterAddEquiv_add, hφ, ih]
  have hu_mul_l : ∀ (q : ℕ) (x : M), uHom (q * l) x = 0 := by
    intro q x
    induction q with
    | zero => simp [uHom]
    | succ q ih =>
      have hsplit : Finset.range ((q + 1) * l) =
          Finset.range (q * l) ∪ Finset.Ico (q * l) (q * l + l) := by
        ext t; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
        rw [add_mul, one_mul]; omega
      have hdisj : Disjoint (Finset.range (q * l)) (Finset.Ico (q * l) (q * l + l)) :=
        Finset.disjoint_left.mpr fun t ht1 ht2 => by
          rw [Finset.mem_range] at ht1; rw [Finset.mem_Ico] at ht2; omega
      rw [huHom_apply, hsplit, Finset.sum_union hdisj, ← huHom_apply, ih, zero_add]
      have hshift : ∑ i ∈ Finset.Ico (q * l) (q * l + l), iterAddEquiv φ i x =
          ∑ r ∈ Finset.range l, iterAddEquiv φ r x := by
        refine Finset.sum_nbij (fun i => i - q * l) ?_ ?_ ?_ ?_
        · intro i hi; rw [Finset.mem_Ico] at hi; rw [Finset.mem_range]; omega
        · intro i hi j hj hij; simp only [Finset.mem_coe, Finset.mem_Ico] at hi hj; simp only at hij; omega
        · intro r hr; simp only [Finset.mem_coe, Finset.mem_range] at hr
          exact ⟨q * l + r, Finset.mem_coe.mpr (Finset.mem_Ico.mpr ⟨by omega, by omega⟩), by simp only; omega⟩
        · intro i hi; rw [Finset.mem_Ico] at hi
          have hmod : i % l = (i - q * l) % l := by
            have : i = (i - q * l) + q * l := by omega
            conv_lhs => rw [this, Nat.add_mul_mod_self_right]
          rw [hiter_mod i, hmod, ← hiter_mod]
      rw [hshift, ← tateN_apply]
      exact hN0 x
  have hu_surj : ∀ j : ℕ, 1 ≤ j → j < l → Function.Bijective (uHom j) := by
    intro j hj1 hjl
    have hj_nz : (j : ZMod l) ≠ 0 := by
      intro h0; exact Nat.not_dvd_of_pos_of_lt (by omega) hjl ((ZMod.natCast_eq_zero_iff j l).mp h0)
    set j' := ((j : ZMod l)⁻¹).val
    have hjj' : (j * j') % l = 1 := by
      have h1 : ((j * j' : ℕ) : ZMod l) = 1 := by
        rw [Nat.cast_mul, ZMod.natCast_zmod_val, mul_inv_cancel₀ hj_nz]
      have h2 := (ZMod.natCast_eq_natCast_iff (j * j') 1 l).mp (by simpa using h1)
      rwa [Nat.ModEq, Nat.mod_eq_of_lt hl.one_lt] at h2
    let vHom : M →+ M := ∑ b ∈ Finset.range j', iterAddEquiv φ (j * b)
    have hvHom_apply : ∀ x : M, vHom x = ∑ b ∈ Finset.range j', iterAddEquiv φ (j * b) x := fun x => by
      simp [vHom]
    have hcomp_eq : ∀ x : M, uHom j (vHom x) = x ∧ vHom (uHom j x) = x := by
      intro x
      have hdouble : ∑ a ∈ Finset.range j, ∑ b ∈ Finset.range j', iterAddEquiv φ (a + j * b) x =
          uHom (j * j') x := by
        rw [huHom_apply, ← Finset.sum_product']
        refine Finset.sum_nbij (fun p : ℕ × ℕ => p.1 + j * p.2) ?_ ?_ ?_ ?_
        · rintro ⟨a, b⟩ hab
          rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hab
          rw [Finset.mem_range]; nlinarith
        · rintro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
          simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_range] at h₁ h₂
          have hb : b₁ = b₂ := by
            have := congrArg (· / j) heq
            simp only at this
            rw [Nat.add_mul_div_left _ _ (by omega), Nat.add_mul_div_left _ _ (by omega),
              Nat.div_eq_of_lt h₁.1, Nat.div_eq_of_lt h₂.1, zero_add, zero_add] at this
            exact this
          subst hb; simp only at heq; exact Prod.ext (by omega) rfl
        · intro t ht
          simp only [Finset.mem_coe, Finset.mem_range] at ht
          refine ⟨(t % j, t / j), Finset.mem_coe.mpr (Finset.mem_product.mpr
            ⟨Finset.mem_range.mpr (Nat.mod_lt t (by omega)),
             Finset.mem_range.mpr (Nat.div_lt_of_lt_mul ht)⟩), ?_⟩
          simp only; have := Nat.div_add_mod t j; omega
        · intro p _; rfl
      have hjj'_eq : j * j' = (j * j' / l) * l + 1 := by
        have := Nat.div_add_mod (j * j') l; rw [hjj'] at this; linarith
      have hu_jj' : uHom (j * j') x = x := by
        rw [hjj'_eq, huHom_apply, Finset.sum_range_succ, ← huHom_apply, hu_mul_l, zero_add,
          hiter_mod, Nat.mul_mod_left, iterAddEquiv_zero]
      constructor
      · rw [huHom_apply, hvHom_apply]
        simp only [map_sum]
        have hrew : ∀ a ∈ Finset.range j, ∑ b ∈ Finset.range j',
            iterAddEquiv φ a (iterAddEquiv φ (j * b) x) =
            ∑ b ∈ Finset.range j', iterAddEquiv φ (a + j * b) x := fun a _ =>
          Finset.sum_congr rfl fun b _ => (iterAddEquiv_add φ a (j * b) x).symm
        rw [Finset.sum_congr rfl hrew, hdouble, hu_jj']
      · rw [hvHom_apply, huHom_apply]
        simp only [map_sum]
        rw [Finset.sum_comm]
        have hrew : ∀ a ∈ Finset.range j, ∑ b ∈ Finset.range j',
            iterAddEquiv φ (j * b) (iterAddEquiv φ a x) =
            ∑ b ∈ Finset.range j', iterAddEquiv φ (a + j * b) x := fun a _ =>
          Finset.sum_congr rfl fun b _ => by rw [← iterAddEquiv_add, add_comm]
        rw [Finset.sum_congr rfl hrew, hdouble, hu_jj']
    exact ⟨Function.LeftInverse.injective (fun x => (hcomp_eq x).2),
      Function.RightInverse.surjective (fun x => (hcomp_eq x).1)⟩
  -- Use polynomial evaluation in `End_ℤ(M)` via `Polynomial.aeval` to evaluate `∏_{j=1}^{l-1} (1 - φ^j) = l`
  let φEnd : Module.End ℤ M := φ.toAddMonoidHom.toIntLinearMap
  have hφEnd_pow : ∀ (n : ℕ) (x : M), (φEnd ^ n) x = iterAddEquiv φ n x := fun n => by
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x; rw [pow_succ', Module.End.mul_apply, ih]; rfl
  have hN_eval : Polynomial.aeval φEnd (∑ i ∈ Finset.range l, (X : Polynomial ℤ) ^ i) = 0 := by
    ext x
    simp only [map_sum, map_pow, aeval_X, LinearMap.coe_sum, Finset.sum_apply, hφEnd_pow,
      LinearMap.zero_apply]
    rw [← tateN_apply]; exact hN0 x
  have hprod_eval : Polynomial.aeval φEnd (∏ j ∈ Finset.Ico 1 l, (1 - (X : Polynomial ℤ) ^ j)) =
      (l : Module.End ℤ M) := by
    obtain ⟨q, hq⟩ := poly_cyclotomic_dvd_prod_one_sub_pow l
    have hev := congrArg (Polynomial.aeval φEnd) hq
    rw [map_sub, map_mul, hN_eval, zero_mul, sub_eq_zero, aeval_C] at hev
    rw [hev]; ext x; simp
  have hfact_poly : ∀ j : ℕ, 1 - (X : Polynomial ℤ) ^ j =
      (1 - X) * (∑ i ∈ Finset.range j, (X : Polynomial ℤ) ^ i) := fun j => by
    rw [mul_comm, geom_sum_mul_neg]
  have hprod_fact : (∏ j ∈ Finset.Ico 1 l, (1 - (X : Polynomial ℤ) ^ j)) =
      (1 - X) ^ (l - 1) * (∏ j ∈ Finset.Ico 1 l, ∑ i ∈ Finset.range j, (X : Polynomial ℤ) ^ i) := by
    have h1 : ∏ j ∈ Finset.Ico 1 l, (1 - (X : Polynomial ℤ) ^ j) =
        ∏ j ∈ Finset.Ico 1 l, ((1 - X) * ∑ i ∈ Finset.range j, (X : Polynomial ℤ) ^ i) :=
      Finset.prod_congr rfl fun j _ => hfact_poly j
    rw [h1, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico]
  let UPoly : Polynomial ℤ := ∏ j ∈ Finset.Ico 1 l, ∑ i ∈ Finset.range j, (X : Polynomial ℤ) ^ i
  let UEnd : Module.End ℤ M := Polynomial.aeval φEnd UPoly
  have hUEnd_bij : Function.Bijective UEnd := by
    have hfac : ∀ s : Finset ℕ, (∀ j ∈ s, 1 ≤ j ∧ j < l) →
        Function.Bijective (Polynomial.aeval φEnd (∏ j ∈ s, ∑ i ∈ Finset.range j, (X : Polynomial ℤ) ^ i)) := by
      intro s
      induction s using Finset.induction_on with
      | empty => intro _; rw [Finset.prod_empty, map_one]; exact Function.bijective_id
      | insert j s hjs ih =>
        intro hs
        rw [Finset.prod_insert hjs, map_mul]
        have hj := hs j (Finset.mem_insert_self j s)
        have hbj : Function.Bijective (Polynomial.aeval φEnd (∑ i ∈ Finset.range j, (X : Polynomial ℤ) ^ i)) := by
          have heq : ⇑(Polynomial.aeval φEnd (∑ i ∈ Finset.range j, (X : Polynomial ℤ) ^ i)) = uHom j := by
            ext x
            rw [huHom_apply]
            simp only [map_sum, map_pow, aeval_X, LinearMap.coe_sum, Finset.sum_apply, hφEnd_pow]
          rw [heq]; exact hu_surj j hj.1 hj.2
        exact hbj.comp (ih fun k hk => hs k (Finset.mem_insert_of_mem hk))
    exact hfac (Finset.Ico 1 l) fun j hj => Finset.mem_Ico.mp hj
  have hD_pow_eval : ∀ (n : ℕ) (x : M), (Polynomial.aeval φEnd ((1 - (X : Polynomial ℤ)) ^ n)) x = D_pow n x := by
    intro n; induction n with
    | zero => intro x; simp [D_pow]
    | succ n ih =>
      intro x
      rw [pow_succ', map_mul, Module.End.mul_apply, ih]
      simp [D_pow, tateD_apply, φEnd]
  have hrange_eq : (D_pow (l - 1)).range = (nsmulAddMonoidHom l : M →+ M).range := by
    have hcomp_l : ∀ x : M, D_pow (l - 1) (UEnd x) = l • x := by
      intro x
      have hev := congrArg (fun f : Module.End ℤ M => f x)
        (hprod_eval.symm.trans (congrArg (Polynomial.aeval φEnd) hprod_fact))
      rw [map_mul, Module.End.mul_apply, hD_pow_eval] at hev
      simpa using hev.symm
    ext y
    simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := hUEnd_bij.2 z
      exact ⟨x, (hcomp_l x).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨UEnd x, hcomp_l x⟩
  -- Compare `M ⧸ D_pow (l - 1) M` (= `M ⧸ l M`) with `M ⧸ D M` using injectivity of `D`!
  obtain ⟨hfin_l, hcard_l⟩ := card_mod_l_free (M := M) hl.pos
  have hfin_pow : Finite (M ⧸ (D_pow (l - 1)).range) := by rw [hrange_eq]; exact hfin_l
  have hD_le_pow : ∀ n, (D_pow (n + 1)).range ≤ (D_pow n).range := by
    intro n; rintro _ ⟨x, rfl⟩; exact ⟨tateD φ x, by
      -- `D_pow (n + 1) x = D_pow n (D x)`
      have hcomm : ∀ k (y : M), D_pow (k + 1) y = D_pow k (tateD φ y) := fun k => by
        induction k with
        | zero => intro _; rfl
        | succ k ih => intro y; change tateD φ (D_pow (k + 1) y) = tateD φ (D_pow k (tateD φ y)); rw [ih]
      exact (hcomm n x).symm⟩
  -- `D_pow (l - 1) ≤ D_pow 1 = tateD φ`, so `M ⧸ (tateD φ).range` is a quotient of `M ⧸ (D_pow (l - 1)).range`, hence finite!
  have hle_1 : (D_pow (l - 1)).range ≤ (tateD φ).range := by
    have hstep : ∀ k, (D_pow (k + 1)).range ≤ (D_pow 1).range := fun k => by
      induction k with
      | zero => exact le_rfl
      | succ k ih => exact (hD_le_pow (k + 1)).trans ih
    have hl1 : l - 1 = (l - 2) + 1 := by have := hl.two_le; omega
    rw [hl1]; exact hstep (l - 2)
  have hfin_D : Finite (M ⧸ (tateD φ).range) :=
    Finite.of_surjective (QuotientAddGroup.map (D_pow (l - 1)).range (tateD φ).range
      (AddMonoidHom.id M) hle_1) (fun y => by
        obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective _ y
        exact ⟨QuotientAddGroup.mk' _ x, rfl⟩)
  -- Induction: `Nat.card (M ⧸ (D_pow n).range) = Nat.card (M ⧸ (tateD φ).range) ^ n`
  have hcomm_D : ∀ (k : ℕ) (y : M), D_pow (k + 1) y = D_pow k (tateD φ y) := fun k => by
    induction k with
    | zero => intro _; rfl
    | succ k ihk =>
      intro y
      change tateD φ (D_pow (k + 1) y) = tateD φ (D_pow k (tateD φ y))
      rw [ihk]
  have hcard_pow : ∀ n : ℕ, Finite (M ⧸ (D_pow n).range) ∧
      Nat.card (M ⧸ (D_pow n).range) = Nat.card (M ⧸ (tateD φ).range) ^ n := by
    intro n
    induction n with
    | zero =>
      have htop : (D_pow 0).range = ⊤ := by ext x; exact ⟨fun _ => trivial, fun _ => ⟨x, rfl⟩⟩
      rw [htop, pow_zero]
      have : Subsingleton (M ⧸ (⊤ : AddSubgroup M)) :=
        ⟨fun a b => by
          obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective _ a
          obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective _ b
          rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq]; trivial⟩
      exact ⟨inferInstance, Nat.card_unique⟩
    | succ n ih =>
      obtain ⟨hfin_n, hcard_n⟩ := ih
      let S := (D_pow (n + 1)).range.comap (D_pow n).range.subtype
      let g : M →+ ((D_pow n).range ⧸ S) :=
        (QuotientAddGroup.mk' S).comp (D_pow n).rangeRestrict
      have hg_surj : Function.Surjective g :=
        (QuotientAddGroup.mk'_surjective S).comp (D_pow n).rangeRestrict_surjective
      have hg_ker : g.ker = (tateD φ).range := by
        ext x
        simp only [g, AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
          QuotientAddGroup.eq_zero_iff, S, AddSubgroup.mem_comap, AddSubgroup.coe_subtype,
          AddMonoidHom.mem_range]
        constructor
        · rintro ⟨y, hy⟩; exact ⟨y, hD_pow_inj n ((hcomm_D n y).symm.trans hy)⟩
        · rintro ⟨y, rfl⟩; exact ⟨y, hcomm_D n y⟩
      let e_sub : (M ⧸ (tateD φ).range) ≃+ ((D_pow n).range ⧸ S) :=
        (QuotientAddGroup.quotientAddEquivOfEq hg_ker.symm).trans
          (QuotientAddGroup.quotientKerEquivOfSurjective g hg_surj)
      have hfin_sub : Finite ((D_pow n).range ⧸ S) := Finite.of_equiv _ e_sub.toEquiv
      let qmap : (M ⧸ (D_pow (n + 1)).range) →+ (M ⧸ (D_pow n).range) :=
        QuotientAddGroup.map (D_pow (n + 1)).range (D_pow n).range (AddMonoidHom.id M) (hD_le_pow n)
      have hqmap_surj : Function.Surjective qmap := fun y => by
        obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective _ y
        exact ⟨QuotientAddGroup.mk' _ x, rfl⟩
      let jmap : ((D_pow n).range ⧸ S) →+ (M ⧸ (D_pow (n + 1)).range) :=
        QuotientAddGroup.lift S ((QuotientAddGroup.mk' _).comp (D_pow n).range.subtype) (by
          intro x hx; exact (QuotientAddGroup.eq_zero_iff _).mpr hx)
      have hjmap_inj : Function.Injective jmap := by
        rw [injective_iff_map_eq_zero]
        intro a ha
        obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective S a
        have hx : (x : M) ∈ (D_pow (n + 1)).range :=
          (QuotientAddGroup.eq_zero_iff (x : M)).mp ha
        exact (QuotientAddGroup.eq_zero_iff x).mpr hx
      have hqmap_ker : qmap.ker = jmap.range := by
        ext a; obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective _ a
        simp only [AddMonoidHom.mem_ker, AddMonoidHom.mem_range, qmap]
        constructor
        · intro hx
          have hmem : x ∈ (D_pow n).range := (QuotientAddGroup.eq_zero_iff _).mp hx
          exact ⟨QuotientAddGroup.mk' S ⟨x, hmem⟩, rfl⟩
        · rintro ⟨b, hb⟩
          obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective S b
          rw [← hb]
          exact (QuotientAddGroup.eq_zero_iff _).mpr y.2
      have hker_eq : (qmap.ker : Type _) ≃ ((D_pow n).range ⧸ S) :=
        (Equiv.setCongr (congrArg SetLike.coe hqmap_ker)).trans
          (Equiv.ofBijective jmap.rangeRestrict
            ⟨fun a b h => hjmap_inj (Subtype.mk.inj h), jmap.rangeRestrict_surjective⟩).symm
      have hfin_ker : Finite qmap.ker := Finite.of_equiv _ hker_eq.symm
      have hfin_quot : Finite ((M ⧸ (D_pow (n + 1)).range) ⧸ qmap.ker) :=
        Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivOfSurjective qmap hqmap_surj).symm.toEquiv
      have hfin_next : Finite (M ⧸ (D_pow (n + 1)).range) := by
        let sec : ((M ⧸ (D_pow (n + 1)).range) ⧸ qmap.ker) → (M ⧸ (D_pow (n + 1)).range) :=
          fun q => Classical.choose (QuotientAddGroup.mk'_surjective qmap.ker q)
        refine Finite.of_surjective (fun p : ((M ⧸ (D_pow (n + 1)).range) ⧸ qmap.ker) × qmap.ker =>
            sec p.1 + p.2.1) (fun x => ?_)
        have hsec : QuotientAddGroup.mk' qmap.ker (sec (QuotientAddGroup.mk' qmap.ker x)) =
            QuotientAddGroup.mk' qmap.ker x :=
          Classical.choose_spec (QuotientAddGroup.mk'_surjective qmap.ker _)
        have hmem : x - sec (QuotientAddGroup.mk' qmap.ker x) ∈ qmap.ker := by
          rw [← QuotientAddGroup.eq_zero_iff]
          change QuotientAddGroup.mk' qmap.ker (x - sec (QuotientAddGroup.mk' qmap.ker x)) = 0
          rw [map_sub, hsec, sub_self]
        exact ⟨(QuotientAddGroup.mk' qmap.ker x, ⟨x - sec (QuotientAddGroup.mk' qmap.ker x), hmem⟩),
          add_sub_cancel _ _⟩
      refine ⟨hfin_next, ?_⟩
      have hmul := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup qmap.ker
      have hc1 : Nat.card ((M ⧸ (D_pow (n + 1)).range) ⧸ qmap.ker) = Nat.card (M ⧸ (D_pow n).range) :=
        Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective qmap hqmap_surj).toEquiv
      have hc2 : Nat.card qmap.ker = Nat.card (M ⧸ (tateD φ).range) :=
        (Nat.card_congr hker_eq).trans (Nat.card_congr e_sub.symm.toEquiv)
      rw [hmul, hc1, hc2, hcard_n, pow_succ]
  -- Transfer `M ⧸ (tateD φ).range` to `H1hat l φ` using `hkerN : (tateN l φ).ker = ⊤`
  let fH1 : M →+ H1hat l φ :=
    (QuotientAddGroup.mk' ((tateD φ).range.comap (tateN l φ).ker.subtype)).comp
      (AddMonoidHom.mk' (fun x : M => (⟨x, hN0 x⟩ : (tateN l φ).ker)) (fun _ _ => rfl))
  have hfH1_surj : Function.Surjective fH1 := fun y => by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective _ y
    exact ⟨x.1, rfl⟩
  have hfH1_ker : fH1.ker = (tateD φ).range := by
    ext x
    simp only [fH1, AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, AddMonoidHom.mk'_apply,
      QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_comap,
      AddSubgroup.coe_subtype]
  let eH1' : (M ⧸ (tateD φ).range) ≃+ H1hat l φ :=
    (QuotientAddGroup.quotientAddEquivOfEq hfH1_ker.symm).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective fH1 hfH1_surj)
  refine ⟨h0_fin, Finite.of_equiv _ eH1'.toEquiv, h0_card, ?_⟩
  rw [← Nat.card_congr eH1'.toEquiv, ← (hcard_pow (l - 1)).2, hrange_eq, hcard_l]

end TateHerbrand

/-! ### Part 6c: Unramified Ideal Extension Map `H1hat(𝓞 Hˣ) ↪ ClassGroup(𝓞 K)` -/

private lemma ideal_eq_of_associated {R : Type*} [CommRing R] {I J : Ideal R}
    (h : Associated I J) : I = J := by
  obtain ⟨u, rfl⟩ := h
  rw [Ideal.isUnit_iff.mp u.isUnit, Ideal.mul_top]

private lemma associates_count_factors_eq_normalizedFactors_count {R : Type*} [CommRing R]
    [IsDedekindDomain R] (p : HeightOneSpectrum R) {I : Ideal R} (hI : I ≠ ⊥) :
    (Associates.mk p.asIdeal).count (Associates.mk I).factors =
      (UniqueFactorizationMonoid.normalizedFactors I).count p.asIdeal := by
  classical
  have hp_irr : Irreducible (Associates.mk p.asIdeal) :=
    Associates.irreducible_mk.mpr (Ideal.prime_of_isPrime p.ne_bot p.isPrime).irreducible
  have hstep : ∀ s : Multiset (Ideal R), (∀ Q ∈ s, Q ≠ ⊥ ∧ Q.IsPrime) →
      (Associates.mk p.asIdeal).count (Associates.mk s.prod).factors = s.count p.asIdeal := by
    intro s
    induction s using Multiset.induction_on with
    | empty =>
      intro _
      simp only [Multiset.prod_zero, Associates.mk_one, Associates.factors_one, Multiset.count_zero]
      exact Associates.count_zero hp_irr
    | cons Q s ih =>
      intro hs
      obtain ⟨hQ0, hQp⟩ := hs Q (Multiset.mem_cons_self Q s)
      have hs' : ∀ P ∈ s, P ≠ ⊥ ∧ P.IsPrime := fun P hP => hs P (Multiset.mem_cons_of_mem hP)
      have hs0 : s.prod ≠ ⊥ := by
        intro h0
        rw [← Ideal.zero_eq_bot, Multiset.prod_eq_zero_iff] at h0
        exact (hs' 0 h0).1 rfl
      have hQ_irr : Irreducible (Associates.mk Q) :=
        Associates.irreducible_mk.mpr (Ideal.prime_of_isPrime hQ0 hQp).irreducible
      rw [Multiset.prod_cons, ← Associates.mk_mul_mk,
        Associates.count_mul (Associates.mk_ne_zero.mpr hQ0) (Associates.mk_ne_zero.mpr hs0) hp_irr,
        ih hs']
      by_cases hQp_eq : Q = p.asIdeal
      · subst hQp_eq
        rw [Multiset.count_cons_self, Associates.count_self hp_irr]
        ring
      · rw [Multiset.count_cons_of_ne (Ne.symm hQp_eq),
          Associates.count_eq_zero_of_ne hp_irr hQ_irr (fun h =>
            hQp_eq (ideal_eq_of_associated (Associates.mk_eq_mk_iff_associated.mp h.symm))),
          zero_add]
  conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hI]
  exact hstep _ fun Q hQ =>
    let hq := UniqueFactorizationMonoid.prime_of_normalized_factor Q hQ
    ⟨hq.ne_zero, Ideal.isPrime_of_prime hq⟩

private lemma ideal_mem_normalizedFactors_of_dvd {R : Type*} [CommRing R] [IsDedekindDomain R]
    {P I : Ideal R} (hP : Prime P) (hI : I ≠ ⊥) (hdvd : P ∣ I) :
    P ∈ UniqueFactorizationMonoid.normalizedFactors I := by
  obtain ⟨Q, hQ, hassoc⟩ :=
    UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hI hP.irreducible hdvd
  exact (ideal_eq_of_associated hassoc).symm ▸ hQ

private lemma fractionalIdeal_ext_count {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [IsDedekindDomain R] {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, FractionalIdeal.count K v I = FractionalIdeal.count K v J) :
    I = J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ]
  simp_rw [h]

/-- When `w.asIdeal.ramificationIdx (𝓞 K) = 1`, `w.valuation H (algebraMap K H x) = (w.under (𝓞 K)).valuation K x`. -/
private theorem valuation_algebraMap_eq_of_ramificationIdx_eq_one
    {K H : Type} [Field K] [NumberField K] [Field H] [NumberField H] [Algebra K H]
    (w : HeightOneSpectrum (𝓞 H)) (he : w.asIdeal.ramificationIdx (𝓞 K) = 1) (x : K) :
    w.valuation H (algebraMap K H x) = (w.under (𝓞 K)).valuation K x := by
  classical
  set v := w.under (𝓞 K)
  have hbase : ∀ a : 𝓞 K, a ≠ 0 →
      w.valuation H (algebraMap (𝓞 H) H (algebraMap (𝓞 K) (𝓞 H) a)) =
        v.valuation K (algebraMap (𝓞 K) K a) := by
    intro a ha
    have haH : algebraMap (𝓞 K) (𝓞 H) a ≠ 0 := by
      intro h0
      have h1 : algebraMap K H (algebraMap (𝓞 K) K a) = 0 := by
        rw [← IsScalarTower.algebraMap_apply (𝓞 K) K H,
          IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 H) H, h0, map_zero]
      exact ha (IsFractionRing.injective (𝓞 K) K ((algebraMap K H).injective (by simpa using h1)))
    have hspanK : Ideal.span {a} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
    have hspanH : Ideal.span {algebraMap (𝓞 K) (𝓞 H) a} ≠ ⊥ := by
      rwa [Ne, Ideal.span_singleton_eq_bot]
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.intValuation_if_neg w haH, HeightOneSpectrum.intValuation_if_neg v ha]
    congr 1; congr 1
    have hmap_span : Ideal.span {algebraMap (𝓞 K) (𝓞 H) a} =
        Ideal.map (algebraMap (𝓞 K) (𝓞 H)) (Ideal.span {a}) := by
      rw [Ideal.map_span, Set.image_singleton]
    have hfac := Ideal.prod_normalizedFactors_eq_self hspanK
    rw [associates_count_factors_eq_normalizedFactors_count v hspanK,
      associates_count_factors_eq_normalizedFactors_count w hspanH]
    -- Factor `Ideal.span {a}` into normalized factors and count `w.asIdeal` in `Ideal.map` of each factor!
    have hmap_count : ∀ s : Multiset (Ideal (𝓞 K)),
        (∀ P ∈ s, P ≠ ⊥ ∧ P.IsPrime) →
        (UniqueFactorizationMonoid.normalizedFactors (Ideal.map (algebraMap (𝓞 K) (𝓞 H)) s.prod)).count
          w.asIdeal = s.count v.asIdeal := by
      intro s
      induction s using Multiset.induction_on with
      | empty =>
        intro _
        simp only [Multiset.prod_zero, Ideal.one_eq_top, Ideal.map_top, Multiset.count_zero]
        have h1 : UniqueFactorizationMonoid.normalizedFactors (⊤ : Ideal (𝓞 H)) = 0 := by
          rw [← Ideal.one_eq_top]; exact UniqueFactorizationMonoid.normalizedFactors_one
        rw [h1]; simp
      | cons P s ih =>
        intro hs
        obtain ⟨hP0, hPp⟩ := hs P (Multiset.mem_cons_self P s)
        have hs' : ∀ Q ∈ s, Q ≠ ⊥ ∧ Q.IsPrime := fun Q hQ => hs Q (Multiset.mem_cons_of_mem hQ)
        have hs0 : s.prod ≠ ⊥ := by
          intro h0
          rw [← Ideal.zero_eq_bot, Multiset.prod_eq_zero_iff] at h0
          exact (hs' 0 h0).1 rfl
        have hmapP0 : Ideal.map (algebraMap (𝓞 K) (𝓞 H)) P ≠ ⊥ := by
          intro h0
          have : P ≤ Ideal.comap (algebraMap (𝓞 K) (𝓞 H)) ⊥ := Ideal.map_le_iff_le_comap.mp h0.le
          have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 H)) := by
            intro x y hxy
            apply IsFractionRing.injective (𝓞 K) K
            apply (algebraMap K H).injective
            rw [← IsScalarTower.algebraMap_apply (𝓞 K) K H, ← IsScalarTower.algebraMap_apply (𝓞 K) K H,
              IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 H) H, IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 H) H, hxy]
          have hcom : Ideal.comap (algebraMap (𝓞 K) (𝓞 H)) ⊥ = ⊥ :=
            Ideal.comap_bot_of_injective _ hinj
          rw [hcom, le_bot_iff] at this; exact hP0 this
        have hmaps0 : Ideal.map (algebraMap (𝓞 K) (𝓞 H)) s.prod ≠ ⊥ := by
          intro h0
          have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 H)) := by
            intro x y hxy
            apply IsFractionRing.injective (𝓞 K) K
            apply (algebraMap K H).injective
            rw [← IsScalarTower.algebraMap_apply (𝓞 K) K H, ← IsScalarTower.algebraMap_apply (𝓞 K) K H,
              IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 H) H, IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 H) H, hxy]
          have : s.prod ≤ ⊥ := by
            rw [← Ideal.comap_bot_of_injective (algebraMap (𝓞 K) (𝓞 H)) hinj]
            exact Ideal.map_le_iff_le_comap.mp h0.le
          exact hs0 (le_bot_iff.mp this)
        rw [Multiset.prod_cons, Ideal.map_mul,
          UniqueFactorizationMonoid.normalizedFactors_mul hmapP0 hmaps0, Multiset.count_add, ih hs']
        by_cases hPv : P = v.asIdeal
        · subst hPv
          rw [Multiset.count_cons_self]
          have : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
          have hram : (UniqueFactorizationMonoid.normalizedFactors
              (Ideal.map (algebraMap (𝓞 K) (𝓞 H)) v.asIdeal)).count w.asIdeal = 1 := by
            rw [HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hmapP0,
              ← Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity v.asIdeal w.asIdeal hmapP0]
            exact he
          rw [hram]; ring
        · rw [Multiset.count_cons_of_ne (Ne.symm hPv)]
          have hnotmem : w.asIdeal ∉ UniqueFactorizationMonoid.normalizedFactors
              (Ideal.map (algebraMap (𝓞 K) (𝓞 H)) P) := by
            intro hmem
            have hdvd : w.asIdeal ∣ Ideal.map (algebraMap (𝓞 K) (𝓞 H)) P :=
              UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hmem
            have hle : Ideal.map (algebraMap (𝓞 K) (𝓞 H)) P ≤ w.asIdeal := Ideal.le_of_dvd hdvd
            have hle_v : P ≤ v.asIdeal := Ideal.map_le_iff_le_comap.mp hle
            have hPmax : P.IsMaximal := hPp.isMaximal hP0
            exact hPv (hPmax.eq_of_le v.isPrime.ne_top hle_v)
          rw [Multiset.count_eq_zero_of_notMem hnotmem, zero_add]
    conv_lhs => rw [hmap_span, ← hfac]
    exact congrArg Nat.cast (hmap_count _ fun P hP =>
      let hp := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
      ⟨hp.ne_zero, Ideal.isPrime_of_prime hp⟩)
  by_cases hx0 : x = 0
  · subst hx0; simp
  · obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have ha0 : a ≠ 0 := by rintro rfl; simp at hx0
    rw [map_div₀, map_div₀, map_div₀]
    have ha' := hbase a ha0
    have hb' := hbase b hb0
    rw [← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 H) H,
      IsScalarTower.algebraMap_apply (𝓞 K) K H] at ha' hb'
    rw [ha', hb']

/-- Automorphism covariance of `HeightOneSpectrum.valuation`: if `τ : H ≃ₐ[K] H` maps
`w₁.asIdeal` to `w₂.asIdeal`, then `w₂.valuation H (τ x) = w₁.valuation H x`. -/
private theorem valuation_aut_eq {K H : Type} [Field K] [NumberField K]
    [Field H] [NumberField H] [Algebra K H]
    (τ : H ≃ₐ[K] H) (w₁ w₂ : HeightOneSpectrum (𝓞 H))
    (hτ : Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv τ).toRingHom w₁.asIdeal = w₂.asIdeal)
    (x : H) :
    w₂.valuation H (τ x) = w₁.valuation H x := by
  classical
  let τO : 𝓞 H ≃ₐ[𝓞 K] 𝓞 H := NumberField.RingOfIntegers.mapAlgEquiv τ
  have hbase : ∀ a : 𝓞 H, a ≠ 0 →
      w₂.valuation H (algebraMap (𝓞 H) H (τO a)) = w₁.valuation H (algebraMap (𝓞 H) H a) := by
    intro a ha
    have hτa : τO a ≠ 0 := (map_ne_zero_iff τO τO.injective).mpr ha
    have hspan1 : Ideal.span {a} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
    have hspan2 : Ideal.span {τO a} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.intValuation_if_neg w₂ hτa, HeightOneSpectrum.intValuation_if_neg w₁ ha]
    congr 1; congr 1
    rw [associates_count_factors_eq_normalizedFactors_count w₂ hspan2,
      associates_count_factors_eq_normalizedFactors_count w₁ hspan1]
    have hmap_span : Ideal.span {τO a} = Ideal.map τO.toRingHom (Ideal.span {a}) := by
      rw [Ideal.map_span, Set.image_singleton]; rfl
    have hiff : ∀ n : ℕ, w₂.asIdeal ^ n ∣ Ideal.span {τO a} ↔ w₁.asIdeal ^ n ∣ Ideal.span {a} := by
      intro n
      rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le, hmap_span, ← hτ, ← Ideal.map_pow]
      constructor
      · intro h
        have h1 := Ideal.map_mono (f := τO.symm.toRingHom) h
        rw [Ideal.map_map, Ideal.map_map] at h1
        have hid : τO.symm.toRingHom.comp τO.toRingHom = RingHom.id (𝓞 H) := by ext y; simp
        rwa [hid, Ideal.map_id, Ideal.map_id] at h1
      · intro h; exact Ideal.map_mono h
    have hfinMult : ∀ (p I : Ideal (𝓞 H)), Irreducible p → I ≠ 0 → FiniteMultiplicity p I := by
      intro p I hp hI
      refine ⟨(UniqueFactorizationMonoid.normalizedFactors I).card, ?_⟩
      rintro ⟨J, hJ⟩
      have hJ0 : J ≠ 0 := by rintro rfl; rw [mul_zero] at hJ; exact hI hJ
      have hcard := congrArg Multiset.card
        (UniqueFactorizationMonoid.normalizedFactors_mul
          (pow_ne_zero ((UniqueFactorizationMonoid.normalizedFactors I).card + 1) hp.ne_zero) hJ0)
      have hirr : (UniqueFactorizationMonoid.normalizedFactors p).card = 1 := by
        simp [UniqueFactorizationMonoid.normalizedFactors_irreducible hp]
      rw [← hJ, Multiset.card_add, UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.card_nsmul,
        hirr, mul_one] at hcard
      omega
    have hle1 : (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})).count w₁.asIdeal ≤
        (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {τO a})).count w₂.asIdeal := by
      rw [HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hspan1,
        HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hspan2]
      have hd1 : w₁.asIdeal ^ multiplicity w₁.asIdeal (Ideal.span {a}) ∣ Ideal.span {a} :=
        pow_multiplicity_dvd _ _
      exact (hfinMult w₂.asIdeal (Ideal.span {τO a}) w₂.irreducible hspan2).le_multiplicity_of_pow_dvd
        ((hiff _).mpr hd1)
    have hle2 : (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {τO a})).count w₂.asIdeal ≤
        (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})).count w₁.asIdeal := by
      rw [HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hspan1,
        HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hspan2]
      have hd2 : w₂.asIdeal ^ multiplicity w₂.asIdeal (Ideal.span {τO a}) ∣ Ideal.span {τO a} :=
        pow_multiplicity_dvd _ _
      exact (hfinMult w₁.asIdeal (Ideal.span {a}) w₁.irreducible hspan1).le_multiplicity_of_pow_dvd
        ((hiff _).mp hd2)
    exact congrArg Nat.cast (le_antisymm hle2 hle1)
  by_cases hx0 : x = 0
  · subst hx0; simp
  · obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 H) x
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have ha0 : a ≠ 0 := by rintro rfl; simp at hx0
    rw [map_div₀, map_div₀, map_div₀]
    have ha' : τ (algebraMap (𝓞 H) H a) = algebraMap (𝓞 H) H (τO a) := rfl
    have hb' : τ (algebraMap (𝓞 H) H b) = algebraMap (𝓞 H) H (τO b) := rfl
    rw [ha', hb', hbase a ha0, hbase b hb0]

/-- **Unramified Ideal Extension Injection (`card_H1_units_dvd_classNumber`)**:
if `H / K` is a cyclic Galois extension of prime degree `l` with generator `σ` and unramified at
every finite prime `w : HeightOneSpectrum (𝓞 H)`, then `H1hat l φ_E` injects into `ClassGroup (𝓞 K)`,
hence `Nat.card (H1hat l φ_E) ∣ NumberField.classNumber K` (and `H1hat l φ_E` is finite)! -/
private theorem card_H1_units_dvd_classNumber {K H : Type} [Field K] [NumberField K]
    [Field H] [NumberField H] [Algebra K H] [IsGalois K H]
    {l : ℕ} [Fact l.Prime] (hdeg : Module.finrank K H = l)
    (σ : H ≃ₐ[K] H) (hord : orderOf σ = l)
    (hunram : ∀ w : HeightOneSpectrum (𝓞 H), w.asIdeal.ramificationIdx (𝓞 K) = 1) :
    let σO : 𝓞 H ≃ₐ[𝓞 K] 𝓞 H := NumberField.RingOfIntegers.mapAlgEquiv σ
    let φE : Additive (𝓞 H)ˣ ≃+ Additive (𝓞 H)ˣ :=
      (Units.mapEquiv σO.toMulEquiv).toAdditive
    Finite (H1hat l φE) ∧ Nat.card (H1hat l φE) ∣ NumberField.classNumber K := by
  classical
  have hl : l.Prime := Fact.out
  let σO : 𝓞 H ≃ₐ[𝓞 K] 𝓞 H := NumberField.RingOfIntegers.mapAlgEquiv σ
  let φE : Additive (𝓞 H)ˣ ≃+ Additive (𝓞 H)ˣ :=
    (Units.mapEquiv σO.toMulEquiv).toAdditive
  have hσO_coe : ∀ x : 𝓞 H, ((σO x : 𝓞 H) : H) = σ (x : H) := fun _ => rfl
  have hiter_coe : ∀ (n : ℕ) (u : (𝓞 H)ˣ),
      (((Additive.toMul (iterAddEquiv φE n (Additive.ofMul u)) : (𝓞 H)ˣ) : 𝓞 H) : H) =
        (σ ^ n) ((u : 𝓞 H) : H) := fun n => by
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro u
      rw [iterAddEquiv_succ, pow_succ', AlgEquiv.mul_apply, ← ih u]
      rfl
  have hgen : ∀ τ : H ≃ₐ[K] H, ∃ i : ℕ, τ = σ ^ i := by
    have hcardG : Nat.card (H ≃ₐ[K] H) = l := by rw [IsGalois.card_aut_eq_finrank, hdeg]
    have htop : Subgroup.zpowers σ = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_zpowers, hord, hcardG]
    intro τ
    have hmem : τ ∈ Subgroup.zpowers σ := htop ▸ Subgroup.mem_top τ
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hpos : 0 < orderOf σ := hord ▸ hl.pos
    refine ⟨(n % (orderOf σ : ℤ)).toNat, ?_⟩
    have hnn : 0 ≤ n % (orderOf σ : ℤ) := Int.emod_nonneg n (by omega)
    rw [← zpow_natCast, Int.toNat_of_nonneg hnn]
    exact (zpow_mod_orderOf σ n).symm
  have : IsGaloisGroup (H ≃ₐ[K] H) (𝓞 K) (𝓞 H) := IsGaloisGroup.of_isFractionRing _ _ _ K H
  -- Step 1: Hilbert 90
  have hH90 : ∀ u : (tateN l φE).ker, ∃ α : Hˣ,
      σ (α : H) = (((Additive.toMul u.1 : (𝓞 H)ˣ) : 𝓞 H) : H) * (α : H) := by
    intro u
    set ε : (𝓞 H)ˣ := Additive.toMul u.1
    let εH : Hˣ := Units.map ((algebraMap (𝓞 H) H).toMonoidHom) ε
    have hnorm : ∏ i ∈ Finset.range l, (σ ^ i) (εH : H) = 1 := by
      have h0 : tateN l φE u.1 = 0 := u.2
      rw [tateN_apply] at h0
      have hprod_eq : ∏ i ∈ Finset.range l, (σ ^ i) (εH : H) =
          (((Additive.toMul (∑ i ∈ Finset.range l, iterAddEquiv φE i u.1) : (𝓞 H)ˣ) : 𝓞 H) : H) := by
        rw [toMul_sum, Units.coe_prod]
        change _ = algebraMap (𝓞 H) H (∏ i ∈ Finset.range l, _)
        rw [map_prod]
        refine Finset.prod_congr rfl fun i _ => (hiter_coe i ε).symm
      rw [hprod_eq, h0]; rfl
    exact hilbert90_cyclic σ hord hl.pos εH hnorm
  -- Step 2: Fiber-constancy of valuations of `α`
  have hval_fiber : ∀ (α : Hˣ) (ε : (𝓞 H)ˣ), σ (α : H) = ((ε : 𝓞 H) : H) * (α : H) →
      ∀ (w₁ w₂ : HeightOneSpectrum (𝓞 H)), w₁.under (𝓞 K) = w₂.under (𝓞 K) →
        w₁.valuation H (α : H) = w₂.valuation H (α : H) := by
    intro α ε hα w₁ w₂ hunder
    have hpow_α : ∀ n : ℕ, ∃ εn : (𝓞 H)ˣ, (σ ^ n) (α : H) = ((εn : 𝓞 H) : H) * (α : H) := fun n => by
      induction n with
      | zero => exact ⟨1, by simp⟩
      | succ n ih =>
        obtain ⟨εn, hεn⟩ := ih
        refine ⟨Units.map σO.toMonoidHom εn * ε, ?_⟩
        rw [pow_succ', AlgEquiv.mul_apply, hεn, map_mul, hα]
        change σ ((εn : 𝓞 H) : H) * (((ε : 𝓞 H) : H) * (α : H)) =
          (algebraMap (𝓞 H) H ((σO (εn : 𝓞 H)) * (ε : 𝓞 H))) * (α : H)
        rw [map_mul]
        change σ ((εn : 𝓞 H) : H) * (((ε : 𝓞 H) : H) * (α : H)) =
          σ ((εn : 𝓞 H) : H) * ((ε : 𝓞 H) : H) * (α : H)
        ring
    set v := w₁.under (𝓞 K)
    have h1 : w₁.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
    have h2 : w₂.asIdeal.LiesOver v.asIdeal := ⟨congrArg HeightOneSpectrum.asIdeal hunder⟩
    obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal w₁.asIdeal w₂.asIdeal (H ≃ₐ[K] H)
    obtain ⟨i, rfl⟩ := hgen τ
    obtain ⟨εi, hεi⟩ := hpow_α i
    have hτ_map : Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (σ ^ i)).toRingHom w₁.asIdeal =
        w₂.asIdeal := hτ
    have hval1 := valuation_aut_eq (σ ^ i) w₁ w₂ hτ_map (α : H)
    have hεi_val : w₂.valuation H ((εi : 𝓞 H) : H) = 1 := by
      rw [HeightOneSpectrum.valuation_eq_one_iff_notMem]
      intro hmem; exact w₂.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem εi.isUnit)
    rw [← hval1, hεi, map_mul, hεi_val, one_mul]
  -- Step 3: Pick `wOver v` over each `v : HeightOneSpectrum (𝓞 K)`
  have hwOver_ex : ∀ v : HeightOneSpectrum (𝓞 K),
      ∃ w : HeightOneSpectrum (𝓞 H), w.under (𝓞 K) = v := by
    intro v
    have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 H)) := by
      intro x y hxy
      apply IsFractionRing.injective (𝓞 K) K
      apply (algebraMap K H).injective
      rw [← IsScalarTower.algebraMap_apply (𝓞 K) K H, ← IsScalarTower.algebraMap_apply (𝓞 K) K H,
        IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 H) H, IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 H) H, hxy]
    have hker : RingHom.ker (algebraMap (𝓞 K) (𝓞 H)) ≤ v.asIdeal := by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le
    obtain ⟨P, hP, hPl⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 H) v.asIdeal hker
    have : P.LiesOver v.asIdeal := ⟨hPl.symm⟩
    have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
    exact ⟨⟨P, hP.isPrime, hPne⟩, HeightOneSpectrum.ext hPl⟩
  choose wOver hwOver using hwOver_ex
  -- Step 4: Fractional ideal `fracOf α` in `K`
  have hfin_supp : ∀ α : Hˣ, Set.Finite {v : HeightOneSpectrum (𝓞 K) |
      (wOver v).valuation H (α : H) ≠ 1} := by
    intro α
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 H) (α : H)
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have ha0 : a ≠ 0 := by rintro rfl; rw [map_zero, zero_div] at hab; exact α.ne_zero hab.symm
    have hspan_a : Ideal.span {a} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
    have hspan_b : Ideal.span {b} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
    let S_H : Finset (Ideal (𝓞 H)) :=
      (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})).toFinset ∪
      (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b})).toFinset
    have hsub : {v : HeightOneSpectrum (𝓞 K) | (wOver v).valuation H (α : H) ≠ 1} ⊆
        (S_H.image (fun P => Ideal.comap (algebraMap (𝓞 K) (𝓞 H)) P) : Set (Ideal (𝓞 K))).preimage
          HeightOneSpectrum.asIdeal := by
      intro v hv
      simp only [Set.mem_ofPred_eq] at hv
      have hnotboth : ¬ ((wOver v).valuation H (algebraMap (𝓞 H) H a) = 1 ∧
          (wOver v).valuation H (algebraMap (𝓞 H) H b) = 1) := by
        rintro ⟨ha1, hb1⟩; apply hv; rw [← hab, map_div₀, ha1, hb1, div_one]
      have hmem_SH : (wOver v).asIdeal ∈ S_H := by
        simp only [S_H, Finset.mem_union, Multiset.mem_toFinset]
        by_cases ha1 : (wOver v).valuation H (algebraMap (𝓞 H) H a) = 1
        · right
          have hbne : (wOver v).valuation H (algebraMap (𝓞 H) H b) ≠ 1 := fun h => hnotboth ⟨ha1, h⟩
          have hb_mem : b ∈ (wOver v).asIdeal := by
            by_contra hnot; exact hbne ((HeightOneSpectrum.valuation_eq_one_iff_notMem _).mpr hnot)
          have hdvd : (wOver v).asIdeal ∣ Ideal.span {b} :=
            Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hb_mem)
          exact ideal_mem_normalizedFactors_of_dvd (wOver v).prime hspan_b hdvd
        · left
          have ha_mem : a ∈ (wOver v).asIdeal := by
            by_contra hnot; exact ha1 ((HeightOneSpectrum.valuation_eq_one_iff_notMem _).mpr hnot)
          have hdvd : (wOver v).asIdeal ∣ Ideal.span {a} :=
            Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr ha_mem)
          exact ideal_mem_normalizedFactors_of_dvd (wOver v).prime hspan_a hdvd
      simp only [Set.mem_preimage, Finset.mem_coe, Finset.mem_image]
      exact ⟨(wOver v).asIdeal, hmem_SH, congrArg HeightOneSpectrum.asIdeal (hwOver v)⟩
    exact ((Finset.finite_toSet _).preimage
      (fun v₁ _ v₂ _ h => HeightOneSpectrum.ext h)).subset hsub
  let fracOf : Hˣ → (FractionalIdeal (𝓞 K)⁰ K)ˣ := fun α =>
    ∏ v ∈ (hfin_supp α).toFinset,
      (Units.mk0 (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) (by
        rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact v.ne_bot)) ^
      (-WithZero.log ((wOver v).valuation H (α : H)))
  have hfrac_count : ∀ (α : Hˣ) (v : HeightOneSpectrum (𝓞 K)),
      FractionalIdeal.count K v (fracOf α : FractionalIdeal (𝓞 K)⁰ K) =
        -WithZero.log ((wOver v).valuation H (α : H)) := by
    intro α v
    have hprod_val : (fracOf α : FractionalIdeal (𝓞 K)⁰ K) =
        ∏ u ∈ (hfin_supp α).toFinset,
          ((u.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
            (-WithZero.log ((wOver u).valuation H (α : H)))) := by
      simp [fracOf, Units.coe_prod]
    rw [hprod_val]
    have hsum : ∀ s : Finset (HeightOneSpectrum (𝓞 K)),
        FractionalIdeal.count K v (∏ u ∈ s, (u.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
          (-WithZero.log ((wOver u).valuation H (α : H)))) =
        ∑ u ∈ s, if u = v then -WithZero.log ((wOver u).valuation H (α : H)) else 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [FractionalIdeal.count_one]
      | insert u s hus ih =>
        have hu0 : (u.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
          rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact u.ne_bot
        have hpow0 : (u.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
            (-WithZero.log ((wOver u).valuation H (α : H))) ≠ 0 := zpow_ne_zero _ hu0
        have hs0 : (∏ w ∈ s, (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
            (-WithZero.log ((wOver w).valuation H (α : H)))) ≠ 0 :=
          Finset.prod_ne_zero_iff.mpr fun w _ => zpow_ne_zero _ (by
            rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact w.ne_bot)
        rw [Finset.prod_insert hus, FractionalIdeal.count_mul K v hpow0 hs0, ih,
          Finset.sum_insert hus, FractionalIdeal.count_zpow K v]
        congr 1
        rw [FractionalIdeal.count_maximal]
        split_ifs <;> simp
    rw [hsum, Finset.sum_ite_eq']
    split_ifs with hv
    · rfl
    · rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hv
      rw [hv, WithZero.log_one, neg_zero]
  have hfrac_mul : ∀ α β : Hˣ, fracOf (α * β) = fracOf α * fracOf β := by
    intro α β
    apply Units.ext
    apply fractionalIdeal_ext_count (Units.ne_zero _) (Units.ne_zero _)
    intro v
    rw [Units.val_mul, FractionalIdeal.count_mul K v (Units.ne_zero _) (Units.ne_zero _),
      hfrac_count (α * β) v, hfrac_count α v, hfrac_count β v]
    have hαne : (wOver v).valuation H (α : H) ≠ 0 := by simp
    have hβne : (wOver v).valuation H (β : H) ≠ 0 := by simp
    rw [Units.val_mul, map_mul, WithZero.log_mul hαne hβne, neg_add]
  have hfrac_algMap : ∀ k : Kˣ,
      (fracOf (Units.map (algebraMap K H).toMonoidHom k) : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (k : K) := by
    intro k
    apply fractionalIdeal_ext_count (Units.ne_zero _)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr k.ne_zero)
    intro v
    rw [hfrac_count]
    have hval := valuation_algebraMap_eq_of_ramificationIdx_eq_one (wOver v) (hunram (wOver v)) (k : K)
    rw [hwOver v] at hval
    change -WithZero.log ((wOver v).valuation H (algebraMap K H (k : K))) = _
    rw [hval]
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 K) (k : K)
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have ha0 : a ≠ 0 := by rintro rfl; rw [map_zero, zero_div] at hab; exact k.ne_zero hab.symm
    have hbK : algebraMap (𝓞 K) K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have haK : algebraMap (𝓞 K) K a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ha0
    have hspan_a : Ideal.span {a} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
    have hspan_b : Ideal.span {b} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
    have hs : FractionalIdeal.spanSingleton (𝓞 K)⁰ (k : K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K a) *
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K b))⁻¹ := by
      rw [← hab, div_eq_mul_inv, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
        FractionalIdeal.spanSingleton_inv]
    have hvc : v.valuation K (k : K) =
        WithZero.exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (k : K))) := by
      rw [hs, FractionalIdeal.count_mul K v (FractionalIdeal.spanSingleton_ne_zero_iff.mpr haK)
        (inv_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hbK)),
        FractionalIdeal.count_inv, ← hab, map_div₀,
        HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.intValuation_if_neg v ha0, HeightOneSpectrum.intValuation_if_neg v hb0,
        ← FractionalIdeal.coeIdeal_span_singleton, ← FractionalIdeal.coeIdeal_span_singleton,
        FractionalIdeal.count_coe K v hspan_a, FractionalIdeal.count_coe K v hspan_b,
        ← WithZero.exp_sub]
      congr 1; ring
    rw [hvc, WithZero.log_exp, neg_neg]
  -- Step 5: Homomorphism `ψ_raw : (tateN l φE).ker →+ Additive (ClassGroup (𝓞 K))`
  let mkCl : (FractionalIdeal (𝓞 K)⁰ K)ˣ →* ClassGroup (𝓞 K) := ClassGroup.mk K
  have hcl_indep : ∀ (u : (tateN l φE).ker) (α₁ α₂ : Hˣ),
      σ (α₁ : H) = (((Additive.toMul u.1 : (𝓞 H)ˣ) : 𝓞 H) : H) * (α₁ : H) →
      σ (α₂ : H) = (((Additive.toMul u.1 : (𝓞 H)ˣ) : 𝓞 H) : H) * (α₂ : H) →
      mkCl (fracOf α₁) = mkCl (fracOf α₂) := by
    intro u α₁ α₂ h₁ h₂
    have hfix : ∀ τ : H ≃ₐ[K] H, τ ((α₁ * α₂⁻¹ : Hˣ) : H) = ((α₁ * α₂⁻¹ : Hˣ) : H) := by
      have hσfix : σ ((α₁ * α₂⁻¹ : Hˣ) : H) = ((α₁ * α₂⁻¹ : Hˣ) : H) := by
        simp only [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, h₁, h₂]
        have hε0 : (((Additive.toMul u.1 : (𝓞 H)ˣ) : 𝓞 H) : H) ≠ 0 :=
          (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 H) H)).mpr (Units.ne_zero _)
        field_simp [hε0, α₂.ne_zero]
      intro τ
      obtain ⟨i, rfl⟩ := hgen τ
      induction i with
      | zero => simp
      | succ i ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hσfix]
    have hmemK : ((α₁ * α₂⁻¹ : Hˣ) : H) ∈ IntermediateField.fixedField (⊤ : Subgroup (H ≃ₐ[K] H)) := by
      rw [IntermediateField.mem_fixedField_iff]; intro τ _; exact hfix τ
    rw [IsGalois.fixedField_top] at hmemK
    obtain ⟨k, hk⟩ := IntermediateField.mem_bot.mp hmemK
    have hk0 : k ≠ 0 := by rintro rfl; rw [map_zero] at hk; exact (α₁ * α₂⁻¹).ne_zero hk.symm
    let kU : Kˣ := Units.mk0 k hk0
    have hαeq : α₁ * α₂⁻¹ = Units.map (algebraMap K H).toMonoidHom kU := Units.ext hk.symm
    have hpr : mkCl (fracOf (α₁ * α₂⁻¹)) = 1 := by
      rw [hαeq]
      change ClassGroup.mk K (fracOf (Units.map (algebraMap K H).toMonoidHom kU)) = 1
      rw [ClassGroup.mk_eq_one_iff]
      refine ⟨(kU : K), ?_⟩
      exact (congrArg FractionalIdeal.coeToSubmodule (hfrac_algMap kU)).trans
        (FractionalIdeal.coe_spanSingleton (𝓞 K)⁰ (kU : K))
    have hmul := congrArg mkCl (hfrac_mul α₁ α₂⁻¹)
    rw [hpr, map_mul] at hmul
    have hinv : fracOf α₂⁻¹ = (fracOf α₂)⁻¹ := by
      apply mul_left_cancel (a := fracOf α₂)
      rw [← hfrac_mul, mul_inv_cancel, mul_inv_cancel]
      apply Units.ext
      apply fractionalIdeal_ext_count (Units.ne_zero _) (Units.ne_zero (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ))
      intro v; rw [hfrac_count, Units.val_one, Units.val_one, map_one, WithZero.log_one, neg_zero,
        FractionalIdeal.count_one]
    rw [hinv, map_inv] at hmul
    exact eq_of_mul_inv_eq_one hmul.symm
  let ψ_raw : (tateN l φE).ker →+ Additive (ClassGroup (𝓞 K)) :=
    AddMonoidHom.mk' (fun u => Additive.ofMul (mkCl (fracOf (Classical.choose (hH90 u))))) (by
      intro u₁ u₂
      set α₁ := Classical.choose (hH90 u₁)
      have hα₁ := Classical.choose_spec (hH90 u₁)
      set α₂ := Classical.choose (hH90 u₂)
      have hα₂ := Classical.choose_spec (hH90 u₂)
      set α₁₂ := Classical.choose (hH90 (u₁ + u₂))
      have hα₁₂ := Classical.choose_spec (hH90 (u₁ + u₂))
      have hprod : σ ((α₁ * α₂ : Hˣ) : H) =
          (((Additive.toMul (u₁ + u₂).1 : (𝓞 H)ˣ) : 𝓞 H) : H) * ((α₁ * α₂ : Hˣ) : H) := by
        rw [Units.val_mul, map_mul, hα₁, hα₂]
        have hcoe : (((Additive.toMul (u₁ + u₂).1 : (𝓞 H)ˣ) : 𝓞 H) : H) =
            (((Additive.toMul u₁.1 : (𝓞 H)ˣ) : 𝓞 H) : H) *
            (((Additive.toMul u₂.1 : (𝓞 H)ˣ) : 𝓞 H) : H) := by
          change algebraMap (𝓞 H) H ((Additive.toMul (u₁.1 + u₂.1) : (𝓞 H)ˣ) : 𝓞 H) = _
          rw [toMul_add, Units.val_mul, map_mul]
        rw [hcoe]; ring
      rw [← ofMul_mul, ← map_mul, ← hfrac_mul]
      exact congrArg Additive.ofMul (hcl_indep (u₁ + u₂) α₁₂ (α₁ * α₂) hα₁₂ hprod))
  have hψ_ker : ψ_raw.ker = (tateD φE).range.comap (tateN l φE).ker.subtype := by
    ext u
    simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_comap, AddSubgroup.coe_subtype,
      AddMonoidHom.mem_range]
    set α := Classical.choose (hH90 u)
    have hα := Classical.choose_spec (hH90 u)
    constructor
    · intro h0
      have hcl1 : mkCl (fracOf α) = 1 := Additive.ofMul.injective h0
      rw [ClassGroup.mk_eq_one_iff] at hcl1
      obtain ⟨k, hk⟩ := hcl1
      have hfrac_eq : (fracOf α : FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.spanSingleton (𝓞 K)⁰ k :=
        FractionalIdeal.coe_ext (hk.trans (FractionalIdeal.coe_spanSingleton (𝓞 K)⁰ k).symm)
      have hk0 : k ≠ 0 := by
        intro h0; rw [h0, FractionalIdeal.spanSingleton_zero] at hfrac_eq
        exact (fracOf α).ne_zero hfrac_eq
      let kU : Kˣ := Units.mk0 k hk0
      let ηH : Hˣ := α * (Units.map (algebraMap K H).toMonoidHom kU)⁻¹
      have hη_val : ∀ w : HeightOneSpectrum (𝓞 H), w.valuation H (ηH : H) = 1 := by
        intro w
        set v := w.under (𝓞 K)
        have hvfib := hval_fiber α (Additive.toMul u.1) hα w (wOver v) (hwOver v).symm
        have hwk := valuation_algebraMap_eq_of_ramificationIdx_eq_one w (hunram w) (kU : K)
        have hwk' := valuation_algebraMap_eq_of_ramificationIdx_eq_one (wOver v) (hunram (wOver v)) (kU : K)
        rw [hwOver v] at hwk'
        have hcnt : FractionalIdeal.count K v (fracOf α : FractionalIdeal (𝓞 K)⁰ K) =
            FractionalIdeal.count K v (fracOf (Units.map (algebraMap K H).toMonoidHom kU) :
              FractionalIdeal (𝓞 K)⁰ K) := by
          rw [hfrac_algMap kU, hfrac_eq]
          rfl
        rw [hfrac_count, hfrac_count, neg_inj] at hcnt
        have hlog_eq : (wOver v).valuation H (α : H) =
            (wOver v).valuation H (algebraMap K H (kU : K)) := by
          have hαv : (wOver v).valuation H (α : H) ≠ 0 :=
            (Valuation.ne_zero_iff _).mpr α.ne_zero
          have hkHv : (wOver v).valuation H (algebraMap K H (kU : K)) ≠ 0 :=
            (Valuation.ne_zero_iff _).mpr ((map_ne_zero_iff _ (algebraMap K H).injective).mpr kU.ne_zero)
          rw [← WithZero.exp_log hαv, ← WithZero.exp_log hkHv, hcnt]
          rfl
        rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hvfib, hlog_eq]
        change (wOver v).valuation H (algebraMap K H (kU : K)) *
          (w.valuation H (algebraMap K H (kU : K)))⁻¹ = 1
        rw [hwk, hwk', mul_inv_cancel₀ ((Valuation.ne_zero_iff _).mpr kU.ne_zero)]
      obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 H) H (ηH : H)
        (fun w => (hη_val w).le)
      obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 H) H ((ηH⁻¹ : Hˣ) : H)
        (fun w => by rw [Units.val_inv_eq_inv_val, map_inv₀, hη_val w, inv_one])
      have hab : a * b = 1 := by
        apply IsFractionRing.injective (𝓞 H) H
        rw [map_mul, ha, hb, Units.val_inv_eq_inv_val, map_one]; exact mul_inv_cancel₀ ηH.ne_zero
      let η : (𝓞 H)ˣ := Units.mkOfMulEqOne a b hab
      have hη_coe : ((η : 𝓞 H) : H) = (ηH : H) := ha
      refine ⟨Additive.ofMul η⁻¹, ?_⟩
      apply Additive.toMul.injective; apply Units.ext
      apply IsFractionRing.injective (𝓞 H) H
      change (((Additive.toMul (tateD φE (Additive.ofMul η⁻¹)) : (𝓞 H)ˣ) : 𝓞 H) : H) = _
      have hD_coe : (((Additive.toMul (tateD φE (Additive.ofMul η⁻¹)) : (𝓞 H)ˣ) : 𝓞 H) : H) =
          (ηH : H)⁻¹ * σ (ηH : H) := by
        rw [tateD_apply, toMul_sub, div_eq_mul_inv]
        change algebraMap (𝓞 H) H (((η⁻¹ * (Units.mapEquiv σO.toMulEquiv η⁻¹)⁻¹ : (𝓞 H)ˣ) : 𝓞 H)) = _
        rw [Units.val_mul, map_mul, ← map_inv, inv_inv]
        have h1 : algebraMap (𝓞 H) H ((η⁻¹ : (𝓞 H)ˣ) : 𝓞 H) = (ηH : H)⁻¹ := by
          apply eq_inv_of_mul_eq_one_left
          have hm := congrArg (algebraMap (𝓞 H) H) (congrArg Units.val (inv_mul_cancel η))
          rw [Units.val_mul, map_mul, Units.val_one, map_one] at hm
          rwa [show algebraMap (𝓞 H) H (η : 𝓞 H) = (ηH : H) from hη_coe] at hm
        have h2 : algebraMap (𝓞 H) H ((Units.mapEquiv σO.toMulEquiv η : (𝓞 H)ˣ) : 𝓞 H) = σ (ηH : H) := by
          change σ ((η : 𝓞 H) : H) = _; rw [hη_coe]
        rw [h1, h2]
      rw [hD_coe]
      have hση : σ (ηH : H) = (((Additive.toMul u.1 : (𝓞 H)ˣ) : 𝓞 H) : H) * (ηH : H) := by
        have hcoe_ηH : (ηH : H) = (α : H) * (algebraMap K H (kU : K))⁻¹ := by
          simp [ηH, Units.val_mul, Units.val_inv_eq_inv_val]
        rw [hcoe_ηH, map_mul, map_inv₀, hα, σ.commutes]
        ring
      rw [hση, mul_left_comm, inv_mul_cancel₀ ηH.ne_zero, mul_one]
    · rintro ⟨ηA, hηA⟩
      set η : (𝓞 H)ˣ := Additive.toMul ηA
      let ηH : Hˣ := Units.map (algebraMap (𝓞 H) H).toMonoidHom η⁻¹
      have hσηH : σ (ηH : H) = (((Additive.toMul u.1 : (𝓞 H)ˣ) : 𝓞 H) : H) * (ηH : H) := by
        have h1 : (((Additive.toMul (tateD φE ηA) : (𝓞 H)ˣ) : 𝓞 H) : H) =
            (((Additive.toMul u.1 : (𝓞 H)ˣ) : 𝓞 H) : H) := by rw [hηA]
        rw [← h1, tateD_apply, toMul_sub, div_eq_mul_inv]
        have hcoe : (((Additive.toMul ηA * (Additive.toMul (φE ηA))⁻¹ : (𝓞 H)ˣ) : 𝓞 H) : H) =
            ((η : 𝓞 H) : H) * (σ ((η : 𝓞 H) : H))⁻¹ := by
          change algebraMap (𝓞 H) H ((η * (Units.mapEquiv σO.toMulEquiv η)⁻¹ : (𝓞 H)ˣ) : 𝓞 H) = _
          rw [Units.val_mul, map_mul]
          congr 1
          apply eq_inv_of_mul_eq_one_left
          have hm := congrArg (algebraMap (𝓞 H) H)
            (congrArg Units.val (inv_mul_cancel (Units.mapEquiv σO.toMulEquiv η)))
          rw [Units.val_mul, map_mul, Units.val_one, map_one] at hm
          exact hm
        rw [hcoe]
        have hηinv : (ηH : H) = ((η : 𝓞 H) : H)⁻¹ := by
          change algebraMap (𝓞 H) H ((η⁻¹ : (𝓞 H)ˣ) : 𝓞 H) = _
          apply eq_inv_of_mul_eq_one_left
          have hm := congrArg (algebraMap (𝓞 H) H) (congrArg Units.val (inv_mul_cancel η))
          rw [Units.val_mul, map_mul, Units.val_one, map_one] at hm
          exact hm
        have hη0 : ((η : 𝓞 H) : H) ≠ 0 :=
          (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 H) H)).mpr (Units.ne_zero _)
        rw [hηinv, map_inv₀]
        field_simp [hη0, (map_ne_zero_iff σ σ.injective).mpr hη0]
      have hcl_eq := hcl_indep u α ηH hα hσηH
      change Additive.ofMul (mkCl (fracOf α)) = 0
      rw [hcl_eq]
      have hfrac1 : fracOf ηH = 1 := by
        apply Units.ext
        apply fractionalIdeal_ext_count (Units.ne_zero _) (Units.ne_zero (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ))
        intro v
        rw [hfrac_count, Units.val_one, FractionalIdeal.count_one]
        have hval1 : (wOver v).valuation H (ηH : H) = 1 := by
          change (wOver v).valuation H (algebraMap (𝓞 H) H ((η⁻¹ : (𝓞 H)ˣ) : 𝓞 H)) = 1
          rw [HeightOneSpectrum.valuation_eq_one_iff_notMem]
          intro hmem; exact (wOver v).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem (η⁻¹).isUnit)
        rw [hval1, WithZero.log_one, neg_zero]
      rw [hfrac1, map_one]; rfl
  let ψ : H1hat l φE →+ Additive (ClassGroup (𝓞 K)) :=
    QuotientAddGroup.lift _ ψ_raw (fun u hu => AddMonoidHom.mem_ker.mp (hψ_ker.symm ▸ hu))
  have hψ_inj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
    have hu : u ∈ ψ_raw.ker := hx
    rw [hψ_ker] at hu
    exact (QuotientAddGroup.eq_zero_iff _).mpr hu
  have : Finite (H1hat l φE) := Finite.of_injective ψ hψ_inj
  refine ⟨inferInstance, ?_⟩
  have hdvd : Nat.card ψ.range ∣ Nat.card (Additive (ClassGroup (𝓞 K))) :=
    AddSubgroup.card_addSubgroup_dvd_card ψ.range
  have heq_card : Nat.card (H1hat l φE) = Nat.card ψ.range :=
    Nat.card_congr (Equiv.ofBijective ψ.rangeRestrict
      ⟨fun a b h => hψ_inj (Subtype.mk.inj h), ψ.rangeRestrict_surjective⟩)
  rw [← heq_card] at hdvd
  simpa [NumberField.classNumber, Nat.card_eq_fintype_card] using hdvd

/-! ### Part 6d: Infinite Places of Odd-Degree Extensions & Dirichlet Unit Herbrand Quotient (`l ∣ classNumber K`) -/

/-- For ANY odd-degree Galois extension `H / K` of a quadratic field `K` (`finrank ℚ K = 2`,
`finrank K H = l` odd prime): `Fintype.card (InfinitePlace H) = l * Fintype.card (InfinitePlace K)`! -/
private theorem card_infinitePlace_odd_galois_quad {K H : Type} [Field K] [NumberField K]
    [Field H] [NumberField H] [Algebra K H] [IsGalois K H]
    {l : ℕ} [Fact l.Prime] (hl2 : l ≠ 2)
    (hquad : Module.finrank ℚ K = 2) (hdeg : Module.finrank K H = l) :
    Fintype.card (InfinitePlace H) = l * Fintype.card (InfinitePlace K) := by
  classical
  have hl : l.Prime := Fact.out
  have hfinH : Module.finrank ℚ H = 2 * l := by
    rw [← Module.finrank_mul_finrank ℚ K H, hquad, hdeg]
  have hsumK := InfinitePlace.card_add_two_mul_card_eq_rank K
  have hsumH := InfinitePlace.card_add_two_mul_card_eq_rank H
  have htotK : Fintype.card (InfinitePlace K) =
      InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K :=
    InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
  have htotH : Fintype.card (InfinitePlace H) =
      InfinitePlace.nrRealPlaces H + InfinitePlace.nrComplexPlaces H :=
    InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces H
  rw [hquad] at hsumK
  rw [hfinH] at hsumH
  have hcases : InfinitePlace.nrRealPlaces K = 0 ∨ InfinitePlace.nrComplexPlaces K = 0 := by omega
  rcases hcases with hreal0 | hcomp0
  · have hHreal0 : InfinitePlace.nrRealPlaces H = 0 := by
      rw [InfinitePlace.nrRealPlaces, Fintype.card_eq_zero_iff]
      refine ⟨fun ⟨w, hw⟩ => ?_⟩
      have hv_real : (w.comap (algebraMap K H)).IsReal := hw.comap (algebraMap K H)
      have hcardK := hreal0
      rw [InfinitePlace.nrRealPlaces, Fintype.card_eq_zero_iff] at hcardK
      exact hcardK.false ⟨w.comap (algebraMap K H), hv_real⟩
    nlinarith
  · have hHcomp0 : InfinitePlace.nrComplexPlaces H = 0 := by
      rw [InfinitePlace.nrComplexPlaces, Fintype.card_eq_zero_iff]
      refine ⟨fun ⟨w, hw⟩ => ?_⟩
      have hv_real : (w.comap (algebraMap K H)).IsReal := by
        rcases (w.comap (algebraMap K H)).isReal_or_isComplex with hr | hc
        · exact hr
        · rw [InfinitePlace.nrComplexPlaces, Fintype.card_eq_zero_iff] at hcomp0
          exact (hcomp0.false ⟨w.comap (algebraMap K H), hc⟩).elim
      let φ : H →+* ℂ := w.embedding
      let ψ : H →+* ℂ := (starRingEnd ℂ).comp φ
      have hφK_real : ComplexEmbedding.IsReal (φ.comp (algebraMap K H)) := by
        have hmk : InfinitePlace.mk (φ.comp (algebraMap K H)) = w.comap (algebraMap K H) := by
          rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
        exact (InfinitePlace.isReal_mk_iff).mp (hmk.symm ▸ hv_real)
      have hagree : ∀ k : K, ψ (algebraMap K H k) = φ (algebraMap K H k) := fun k => by
        change starRingEnd ℂ (φ (algebraMap K H k)) = φ (algebraMap K H k)
        exact congrFun (congrArg DFunLike.coe (ComplexEmbedding.isReal_iff.mp hφK_real)) k
      let : Algebra K ℂ := (φ.comp (algebraMap K H)).toAlgebra
      let φA : H →ₐ[K] ℂ := { φ with commutes' := fun _ => rfl }
      let ψA : H →ₐ[K] ℂ := { ψ with commutes' := hagree }
      let φR : IntermediateField K ℂ := φA.fieldRange
      let φR_hom : H →ₐ[K] φR :=
        { toFun := fun y => ⟨φA y, ⟨y, rfl⟩⟩
          map_one' := Subtype.ext (map_one φA)
          map_mul' := fun a b => Subtype.ext (map_mul φA a b)
          map_zero' := Subtype.ext (map_zero φA)
          map_add' := fun a b => Subtype.ext (map_add φA a b)
          commutes' := fun c => Subtype.ext (φA.commutes c) }
      have hrange : ∀ x : H, ∃ y : H, φ y = ψ x := by
        intro x
        have hsplits : ((minpoly K x).map (algebraMap K φR)).Splits := by
          have hs := (Normal.splits (inferInstance : Normal K H) x).map φR_hom.toRingHom
          have h1 : φR_hom.toRingHom.comp (algebraMap K H) = algebraMap K φR := by
            ext k; exact congrArg Subtype.val (φR_hom.commutes k)
          rwa [Polynomial.map_map, h1] at hs
        have hroot : Polynomial.aeval (ψA x) (minpoly K x) = 0 := by
          rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
        have hmon : (minpoly K x).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)
        have hmem_roots : ψA x ∈ ((minpoly K x).map (algebraMap K ℂ)).roots := by
          rw [Polynomial.mem_roots (hmon.map _).ne_zero, Polynomial.IsRoot.def,
            Polynomial.eval_map, ← Polynomial.aeval_def]
          exact hroot
        have hmap_eq : ((minpoly K x).map (algebraMap K φR)).map φR.val.toRingHom =
            (minpoly K x).map (algebraMap K ℂ) := by
          rw [Polynomial.map_map]; congr 1
        have hsub : ((minpoly K x).map (algebraMap K ℂ)).roots =
            ((minpoly K x).map (algebraMap K φR)).roots.map (fun r : φR => (r : ℂ)) := by
          rw [← hmap_eq]
          exact hsplits.roots_map φR.val.toRingHom
        rw [hsub, Multiset.mem_map] at hmem_roots
        obtain ⟨r, -, hr⟩ := hmem_roots
        obtain ⟨y, hy⟩ := r.2
        exact ⟨y, hy.trans hr⟩
      let f : H → H := fun x => Classical.choose (hrange x)
      have hspec : ∀ x : H, φ (f x) = ψ x := fun x =>
        Classical.choose_spec (hrange x)
      have hinj : Function.Injective f := by
        intro x y hxy
        exact ψ.injective ((hspec x).symm.trans (congrArg φ hxy |>.trans (hspec y)))
      let L : H →ₗ[K] H :=
        { toFun := f
          map_add' := fun x y => φ.injective (by rw [map_add, hspec, hspec, hspec, map_add])
          map_smul' := fun c x => φ.injective (by
            simp only [RingHom.id_apply, Algebra.smul_def]
            rw [map_mul, hspec, map_mul, hspec, hagree]) }
      let τ : H ≃ₐ[K] H :=
        AlgEquiv.ofBijective
          { toFun := f
            map_one' := φ.injective (by rw [hspec, map_one, map_one])
            map_mul' := fun x y => φ.injective (by rw [map_mul, hspec, hspec, hspec, map_mul])
            map_zero' := φ.injective (by rw [hspec, map_zero, map_zero])
            map_add' := L.map_add'
            commutes' := fun c => φ.injective (by rw [hspec, hagree]) }
          ⟨hinj, (LinearMap.injective_iff_surjective (f := L)).mp hinj⟩
      have hτ_spec : ∀ x : H, φ (τ x) = starRingEnd ℂ (φ x) := fun x => hspec x
      have hτ2 : τ ^ 2 = 1 := by
        ext x; apply φ.injective
        rw [sq, AlgEquiv.mul_apply, hτ_spec, hτ_spec, starRingEnd_self_apply, AlgEquiv.one_apply]
      have hτ_ord_dvd2 : orderOf τ ∣ 2 := orderOf_dvd_of_pow_eq_one hτ2
      have hτ_ord_dvdl : orderOf τ ∣ l := by
        have hd := orderOf_dvd_card (x := τ)
        rwa [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hdeg] at hd
      have hcop : Nat.Coprime 2 l := (Nat.coprime_primes Nat.prime_two hl).mpr hl2.symm
      have hτ1 : τ = 1 := orderOf_eq_one_iff.mp
        (Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd hτ_ord_dvd2 hτ_ord_dvdl))
      have hw_real : w.IsReal := by
        rw [← InfinitePlace.mk_embedding w, InfinitePlace.isReal_mk_iff, ComplexEmbedding.isReal_iff]
        ext x; exact (hτ_spec x).symm.trans (by rw [hτ1, AlgEquiv.one_apply])
      exact (InfinitePlace.not_isReal_iff_isComplex.mpr hw) hw_real
    nlinarith

/-- Helper: for any finitely generated `ℤ`-module `A` and `l > 0`, `A ⧸ (nsmulAddMonoidHom l).range` is finite. -/
private lemma finite_quot_nsmul_of_fg {A : Type*} [AddCommGroup A] [Module.Finite ℤ A]
    {l : ℕ} (hl : 0 < l) : Finite (A ⧸ (nsmulAddMonoidHom l : A →+ A).range) := by
  classical
  have : NeZero l := ⟨hl.ne'⟩
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := A)
  let f : (s → ZMod l) → (A ⧸ (nsmulAddMonoidHom l : A →+ A).range) :=
    fun c => QuotientAddGroup.mk' _ (∑ x : s, ((c x).val : ℤ) • x.1)
  refine Finite.of_surjective f fun q => ?_
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective _ q
  have ha : a ∈ Submodule.span ℤ (s : Set A) := hs.symm ▸ trivial
  rw [Submodule.mem_span_finset] at ha
  obtain ⟨g, -, hga⟩ := ha
  refine ⟨fun x => (g x.1 : ZMod l), ?_⟩
  change QuotientAddGroup.mk' _ (∑ x : s, (((g x.1 : ZMod l).val : ℤ)) • x.1) = QuotientAddGroup.mk' _ a
  rw [← sub_eq_zero, ← map_sub, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  have hsub : (∑ x : s, (((g x.1 : ZMod l).val : ℤ)) • x.1) - a =
      ∑ x : s, (((g x.1 : ZMod l).val : ℤ) - g x.1) • x.1 := by
    rw [← hga, ← Finset.sum_attach s (fun y => g y • y), ← Finset.univ_eq_attach,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => (sub_smul _ _ _).symm
  have hdvd : ∀ x : s, ∃ qx : ℤ, (((g x.1 : ZMod l).val : ℤ) - g x.1) = (l : ℤ) * qx := fun x =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ l).mp (by push_cast; rw [ZMod.natCast_zmod_val, sub_self])
  choose qx hqx using hdvd
  rw [hsub]
  refine ⟨∑ x : s, qx x • x.1, ?_⟩
  simp only [nsmulAddMonoidHom_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← natCast_zsmul, ← mul_smul, hqx x]

/-- Product isomorphism for `H0hat` and `H1hat`. -/
private lemma tate_prod_equiv {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (l : ℕ) (φA : A ≃+ A) (φB : B ≃+ B) :
    Nonempty (H0hat l (φA.prodCongr φB) ≃+ H0hat l φA × H0hat l φB) ∧
    Nonempty (H1hat l (φA.prodCongr φB) ≃+ H1hat l φA × H1hat l φB) := by
  let φP := φA.prodCongr φB
  have hiter : ∀ n (p : A × B), iterAddEquiv φP n p = (iterAddEquiv φA n p.1, iterAddEquiv φB n p.2) :=
    fun n => by induction n with | zero => intro _; rfl | succ n ih => intro p; rw [iterAddEquiv_succ, ih]; rfl
  have hD : ∀ p : A × B, tateD φP p = (tateD φA p.1, tateD φB p.2) := fun _ => rfl
  have hN : ∀ p : A × B, tateN l φP p = (tateN l φA p.1, tateN l φB p.2) := fun p => by
    ext <;> simp [tateN_apply, hiter, Prod.fst_sum, Prod.snd_sum]
  constructor
  · let f0 : (tateD φP).ker →+ H0hat l φA × H0hat l φB :=
      AddMonoidHom.mk' (fun p =>
        (QuotientAddGroup.mk' _ ⟨p.1.1, congrArg Prod.fst p.2⟩,
         QuotientAddGroup.mk' _ ⟨p.1.2, congrArg Prod.snd p.2⟩))
        (fun _ _ => rfl)
    have hf0_surj : Function.Surjective f0 := by
      rintro ⟨x, y⟩
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
      obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective _ y
      exact ⟨⟨(a.1, b.1), Prod.ext a.2 b.2⟩, rfl⟩
    have hf0_ker : f0.ker = (tateN l φP).range.comap (tateD φP).ker.subtype := by
      ext p
      simp only [f0, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply, Prod.mk_eq_zero,
        QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_comap,
        AddSubgroup.coe_subtype, AddMonoidHom.mem_range]
      constructor
      · rintro ⟨⟨a0, ha0⟩, ⟨b0, hb0⟩⟩; exact ⟨(a0, b0), by rw [hN]; exact Prod.ext ha0 hb0⟩
      · rintro ⟨⟨a0, b0⟩, h⟩; rw [hN] at h; exact ⟨⟨a0, congrArg Prod.fst h⟩, ⟨b0, congrArg Prod.snd h⟩⟩
    exact ⟨(QuotientAddGroup.quotientAddEquivOfEq hf0_ker.symm).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective f0 hf0_surj)⟩
  · let f1 : (tateN l φP).ker →+ H1hat l φA × H1hat l φB :=
      AddMonoidHom.mk' (fun p =>
        (QuotientAddGroup.mk' _ ⟨p.1.1, by have := congrArg Prod.fst p.2; rwa [hN] at this⟩,
         QuotientAddGroup.mk' _ ⟨p.1.2, by have := congrArg Prod.snd p.2; rwa [hN] at this⟩))
        (fun _ _ => rfl)
    have hf1_surj : Function.Surjective f1 := by
      rintro ⟨x, y⟩
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
      obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective _ y
      exact ⟨⟨(a.1, b.1), by rw [AddMonoidHom.mem_ker, hN]; exact Prod.ext a.2 b.2⟩, rfl⟩
    have hf1_ker : f1.ker = (tateD φP).range.comap (tateN l φP).ker.subtype := by
      ext p
      simp only [f1, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply, Prod.mk_eq_zero,
        QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_comap,
        AddSubgroup.coe_subtype, AddMonoidHom.mem_range]
      constructor
      · rintro ⟨⟨a0, ha0⟩, ⟨b0, hb0⟩⟩; exact ⟨(a0, b0), Prod.ext ha0 hb0⟩
      · rintro ⟨⟨a0, b0⟩, h⟩; exact ⟨⟨a0, congrArg Prod.fst h⟩, ⟨b0, congrArg Prod.snd h⟩⟩
    exact ⟨(QuotientAddGroup.quotientAddEquivOfEq hf1_ker.symm).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective f1 hf1_surj)⟩

/-- **Furtwängler / Hilbert-90 + Herbrand Quotient Theorem (`dvd_classNumber_of_unramified_cyclic_prime_ext`)**:
if `H / K` is an everywhere-unramified cyclic Galois extension of odd prime degree `l` over a
quadratic field `K` (`finrank ℚ K = 2`), then **`l ∣ NumberField.classNumber K`**!
ZERO Class Field Theory, ZERO open parameters! -/
theorem dvd_classNumber_of_unramified_cyclic_prime_ext
    {K H : Type} [Field K] [NumberField K] [Field H] [NumberField H] [Algebra K H] [IsGalois K H]
    {l : ℕ} [Fact l.Prime] (hl2 : l ≠ 2)
    (hquad : Module.finrank ℚ K = 2) (hdeg : Module.finrank K H = l)
    (hunram : ∀ w : HeightOneSpectrum (𝓞 H), w.asIdeal.ramificationIdx (𝓞 K) = 1) :
    l ∣ NumberField.classNumber K := by
  classical
  have hl : l.Prime := Fact.out
  have hcardG : Nat.card (H ≃ₐ[K] H) = l := by rw [IsGalois.card_aut_eq_finrank, hdeg]
  have : IsCyclic (H ≃ₐ[K] H) := isCyclic_of_prime_card hcardG
  obtain ⟨σ, hσ_gen⟩ := IsCyclic.exists_generator (α := H ≃ₐ[K] H)
  have hord : orderOf σ = l := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hσ_gen, hcardG]
  let σO : 𝓞 H ≃ₐ[𝓞 K] 𝓞 H := NumberField.RingOfIntegers.mapAlgEquiv σ
  let φE : Additive (𝓞 H)ˣ ≃+ Additive (𝓞 H)ˣ := (Units.mapEquiv σO.toMulEquiv).toAdditive
  have hφE_iter : ∀ n (x : Additive (𝓞 H)ˣ),
      iterAddEquiv φE n x = Additive.ofMul (Units.mapEquiv (NumberField.RingOfIntegers.mapAlgEquiv (σ ^ n)).toMulEquiv (Additive.toMul x)) := by
    intro n; induction n with
    | zero => intro x; apply Additive.toMul.injective; apply Units.ext; apply Subtype.ext; rfl
    | succ n ih =>
      intro x; rw [iterAddEquiv_succ, ih]
      apply Additive.toMul.injective; apply Units.ext; apply Subtype.ext
      change σ ((σ ^ n) _) = (σ ^ (n + 1)) _
      rw [pow_succ', AlgEquiv.mul_apply]
  have hφE_l : ∀ x, iterAddEquiv φE l x = x := fun x => by
    rw [hφE_iter, ← hord, pow_orderOf_eq_one]
    apply Additive.toMul.injective; apply Units.ext; apply Subtype.ext; rfl
  -- Step 1: Unramified ideal extension
  obtain ⟨hfin_H1E, hH1E_dvd⟩ := card_H1_units_dvd_classNumber hdeg σ hord hunram
  -- Step 2: Torsion `T` and free quotient `U = E / T`
  let E := Additive (𝓞 H)ˣ
  let T : Submodule ℤ E := Submodule.torsion ℤ E
  have hT_fin : Finite T := by
    let fT : T → NumberField.Units.torsion H := fun x =>
      ⟨Additive.toMul x.1, by
        obtain ⟨⟨n, hn0⟩, hnx⟩ := x.2
        have hpos : 0 < n.natAbs := Int.natAbs_pos.mpr (nonZeroDivisors.ne_zero hn0)
        refine (isOfFinOrder_iff_pow_eq_one).mpr ⟨n.natAbs, hpos, ?_⟩
        apply Additive.ofMul.injective
        rw [ofMul_pow, ofMul_one, ← natCast_zsmul]
        rcases Int.natAbs_eq n with hn | hn
        · rw [← hn]; exact hnx
        · rw [← neg_eq_zero, ← neg_smul, ← hn]; exact hnx⟩
    exact Finite.of_injective fT fun a b h =>
      Subtype.ext (Additive.toMul.injective (Subtype.mk.inj h))
  have hφE_T : ∀ x : E, x ∈ T ↔ φE x ∈ T := fun x => by
    constructor
    · rintro ⟨⟨n, hn0⟩, hn⟩
      refine ⟨⟨n, hn0⟩, ?_⟩
      change n • x = 0 at hn
      change n • φE x = 0
      rw [← map_zsmul φE, hn, map_zero]
    · rintro ⟨⟨n, hn0⟩, hn⟩
      refine ⟨⟨n, hn0⟩, ?_⟩
      change n • φE x = 0 at hn
      change n • x = 0
      exact φE.injective (by rw [map_zsmul φE, map_zero]; exact hn)
  let φT : T ≃+ T :=
    { toFun := fun x => ⟨φE x.1, (hφE_T x.1).mp x.2⟩
      invFun := fun x => ⟨φE.symm x.1, (hφE_T (φE.symm x.1)).mpr (by simp [x.2])⟩
      left_inv := fun x => Subtype.ext (φE.symm_apply_apply x.1)
      right_inv := fun x => Subtype.ext (φE.apply_symm_apply x.1)
      map_add' := fun x y => Subtype.ext (map_add φE x.1 y.1) }
  have hφT_l : ∀ x, iterAddEquiv φT l x = x := fun x => by
    apply Subtype.ext
    have hcoe : ∀ n (y : T), (iterAddEquiv φT n y).1 = iterAddEquiv φE n y.1 := fun n => by
      induction n with
      | zero => intro _; rfl
      | succ n ih => intro y; rw [iterAddEquiv_succ, iterAddEquiv_succ, ← ih]; rfl
    rw [hcoe, hφE_l]
  let U := E ⧸ T.toAddSubgroup
  let qU : E →+ U := QuotientAddGroup.mk' T.toAddSubgroup
  let φU : U ≃+ U :=
    AddEquiv.ofBijective
      (QuotientAddGroup.map T.toAddSubgroup T.toAddSubgroup φE.toAddMonoidHom
        (fun x hx => (hφE_T x).mp hx))
      ⟨by
        rw [injective_iff_map_eq_zero]
        intro u hu
        obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective _ u
        exact (QuotientAddGroup.eq_zero_iff _).mpr ((hφE_T x).mpr ((QuotientAddGroup.eq_zero_iff _).mp hu)),
       fun y => by
         obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective _ y
         obtain ⟨x', hx'⟩ := φE.surjective x
         exact ⟨QuotientAddGroup.mk' _ x', by change QuotientAddGroup.mk' _ (φE x') = _; rw [hx']⟩⟩
  have hqU_eq : ∀ x : E, qU (φE x) = φU (qU x) := fun _ => rfl
  have hφU_l : ∀ u : U, iterAddEquiv φU l u = u := fun u => by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective _ u
    have hcoe : ∀ n (y : E), iterAddEquiv φU n (qU y) = qU (iterAddEquiv φE n y) := fun n => by
      induction n with
      | zero => intro _; rfl
      | succ n ih => intro y; rw [iterAddEquiv_succ, ih, ← hqU_eq, iterAddEquiv_succ]
    rw [hcoe, hφE_l]
  have hU_tf : NoZeroSMulDivisors ℤ U := by
    refine ⟨fun {c u} hcu => ?_⟩
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective _ u
      have hcx : c • x ∈ T := (QuotientAddGroup.eq_zero_iff _).mp (by rwa [← map_zsmul qU] at hcu)
      obtain ⟨⟨d, hd0⟩, hdx⟩ := hcx
      have hcd0 : d * c ≠ 0 := mul_ne_zero (nonZeroDivisors.ne_zero hd0) hc
      exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨⟨d * c, mem_nonZeroDivisors_of_ne_zero hcd0⟩, by
        change (d * c) • x = 0
        rw [mul_smul]; exact hdx⟩
  have : Module.Finite ℤ U := Module.Finite.of_surjective qU.toIntLinearMap (QuotientAddGroup.mk'_surjective _)
  have : Module.Free ℤ U := Module.free_of_finite_type_torsion_free'
  -- Step 3: Split `U` into `UG := ker (tateD φU)` and `M := ker (tateN l φU)`
  let UG : Submodule ℤ U := (tateD φU).toIntLinearMap.ker
  let M : Submodule ℤ U := (tateN l φU).toIntLinearMap.ker
  have : Module.Free ℤ UG := Module.free_of_finite_type_torsion_free'
  have : Module.Finite ℤ UG := inferInstance
  have : Module.Free ℤ M := Module.free_of_finite_type_torsion_free'
  have : Module.Finite ℤ M := inferInstance
  have hdisj : UG ⊓ M = ⊥ := by
    rw [eq_bot_iff]; intro u ⟨huG, huM⟩
    have hfix : φU u = u := (sub_eq_zero.mp huG).symm
    have hiter : ∀ i, iterAddEquiv φU i u = u := fun i => by
      induction i with | zero => rfl | succ i ih => rw [iterAddEquiv_succ, ih, hfix]
    have hlu : (l : ℤ) • u = 0 := by
      rw [natCast_zsmul]; have h0 : tateN l φU u = 0 := huM; rw [tateN_apply] at h0; simpa [hiter] using h0
    exact (smul_eq_zero.mp hlu).resolve_left (Int.natCast_ne_zero.mpr hl.ne_zero)
  have hindex : ∀ u : U, (l : ℤ) • u ∈ UG ⊔ M := by
    intro u
    have h1 : tateN l φU u ∈ UG := tateD_comp_tateN l φU hφU_l u
    have h2 : (l : ℤ) • u - tateN l φU u ∈ M := by
      show tateN l φU ((l : ℤ) • u - tateN l φU u) = 0
      have hfix : φU (tateN l φU u) = tateN l φU u := (sub_eq_zero.mp h1).symm
      have hiter : ∀ i, iterAddEquiv φU i (tateN l φU u) = tateN l φU u := fun i => by
        induction i with | zero => rfl | succ i ih => rw [iterAddEquiv_succ, ih, hfix]
      have hNN : tateN l φU (tateN l φU u) = l • tateN l φU u := by
        rw [tateN_apply]; simp [hiter]
      rw [map_sub, map_zsmul, natCast_zsmul, hNN, sub_self]
    have heq : (l : ℤ) • u = tateN l φU u + ((l : ℤ) • u - tateN l φU u) := by abel
    rw [heq]; exact Submodule.add_mem_sup h1 h2
  -- Ranks
  set rK : ℕ := Fintype.card (InfinitePlace K) - 1
  have hrK_pos : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos
  have hrank_U : Module.finrank ℤ U = l * (rK + 1) - 1 := by
    have h1 := Submodule.finrank_quotient_add_finrank T
    have hT0 : Module.finrank ℤ T = 0 := by
      rw [Module.finrank_eq_zero_iff]; intro x; obtain ⟨⟨n, hn0⟩, hnx⟩ := x.2
      exact ⟨n, nonZeroDivisors.ne_zero hn0, Subtype.ext hnx⟩
    have hE_rank : Module.finrank ℤ E = Fintype.card (InfinitePlace H) - 1 := by
      rw [NumberField.Units.finrank_eq, NumberField.Units.rank]
    have hU_eq : Module.finrank ℤ U = Module.finrank ℤ (E ⧸ T) := rfl
    rw [hT0, add_zero, hE_rank] at h1
    rw [hU_eq, h1, card_infinitePlace_odd_galois_quad hl2 hquad hdeg]
    have h1r : rK + 1 = Fintype.card (InfinitePlace K) := Nat.sub_add_cancel hrK_pos
    rw [h1r]
  have hrank_UG : Module.finrank ℤ UG = rK := by
    let incK : Additive (𝓞 K)ˣ →ₗ[ℤ] UG :=
      (AddMonoidHom.mk' (fun x : Additive (𝓞 K)ˣ =>
        (⟨qU (Additive.ofMul (Units.map (algebraMap (𝓞 K) (𝓞 H)).toMonoidHom (Additive.toMul x))), by
          show tateD φU (qU _) = 0
          rw [tateD_apply, ← hqU_eq, sub_eq_zero]; congr 1
          apply Additive.toMul.injective; apply Units.ext
          exact (σO.commutes ((Additive.toMul x : (𝓞 K)ˣ) : 𝓞 K)).symm⟩ : UG))
        (fun a b => Subtype.ext (by
          change qU (Additive.ofMul (Units.map _ (Additive.toMul a * Additive.toMul b))) = _
          rw [map_mul, ofMul_mul, map_add]; rfl))).toIntLinearMap
    have hker_rank : Module.finrank ℤ (LinearMap.ker incK) = 0 := by
      rw [Module.finrank_eq_zero_iff]
      intro ⟨x, hx⟩
      have hq0 : qU (Additive.ofMul (Units.map (algebraMap (𝓞 K) (𝓞 H)).toMonoidHom (Additive.toMul x))) = 0 :=
        congrArg Subtype.val hx
      obtain ⟨⟨n, hn0⟩, hnx⟩ := (QuotientAddGroup.eq_zero_iff _).mp hq0
      change n • Additive.ofMul (Units.map (algebraMap (𝓞 K) (𝓞 H)).toMonoidHom (Additive.toMul x)) = 0 at hnx
      have h3 : (Additive.toMul (n • Additive.ofMul (Units.map (algebraMap (𝓞 K) (𝓞 H)).toMonoidHom
          (Additive.toMul x))) : (𝓞 H)ˣ) = 1 := by
        rw [hnx]; rfl
      have h4 : Units.map (algebraMap (𝓞 K) (𝓞 H)).toMonoidHom (Additive.toMul x ^ n) = 1 := by
        rw [map_zpow]; simpa [toMul_zsmul] using h3
      have h5 : algebraMap (𝓞 K) (𝓞 H) ((Additive.toMul x ^ n : (𝓞 K)ˣ) : 𝓞 K) =
          algebraMap (𝓞 K) (𝓞 H) (1 : 𝓞 K) := by
        rw [map_one]
        exact congrArg Units.val h4
      have h6 : ((Additive.toMul x ^ n : (𝓞 K)ˣ) : 𝓞 K) = 1 :=
        (IsFractionRing.injective (𝓞 K) K) ((algebraMap K H).injective (by
          have h5' := congrArg (algebraMap (𝓞 H) H) h5
          simp only [← IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 H) H,
            IsScalarTower.algebraMap_apply (𝓞 K) K H] at h5'
          exact h5'))
      refine ⟨n, nonZeroDivisors.ne_zero hn0, Subtype.ext ?_⟩
      change n • x = 0
      apply Additive.toMul.injective; apply Units.ext
      rw [toMul_zsmul]; exact h6
    have hcoker_rank : Module.finrank ℤ (UG ⧸ LinearMap.range incK) = 0 := by
      rw [Module.finrank_eq_zero_iff]
      intro y
      obtain ⟨⟨u, hu⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨e, rfl⟩ := QuotientAddGroup.mk'_surjective _ u
      set m := Nat.card T
      have hm0 : (m : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr Nat.card_pos.ne'
      have hDeT : tateD φE e ∈ T := (QuotientAddGroup.eq_zero_iff _).mp hu
      have hmDe : m • tateD φE e = 0 :=
        congrArg Subtype.val (addOrderOf_dvd_iff_nsmul_eq_zero.mp (addOrderOf_dvd_natCard (⟨tateD φE e, hDeT⟩ : T)))
      have hfix_me : φE (m • e) = m • e := (sub_eq_zero.mp (by
        show tateD φE (m • e) = 0; rw [map_nsmul, hmDe])).symm
      set u0 : (𝓞 H)ˣ := Additive.toMul (m • e)
      have hσu0 : σ ((u0 : 𝓞 H) : H) = ((u0 : 𝓞 H) : H) :=
        congrArg (fun z : E => (((Additive.toMul z : (𝓞 H)ˣ) : 𝓞 H) : H)) hfix_me
      have hmemK : ((u0 : 𝓞 H) : H) ∈ IntermediateField.fixedField (⊤ : Subgroup (H ≃ₐ[K] H)) := by
        rw [IntermediateField.mem_fixedField_iff]
        intro τ _
        have htop : Subgroup.zpowers σ = ⊤ := by
          apply Subgroup.eq_top_of_card_eq; rw [Nat.card_zpowers, hord, hcardG]
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (htop ▸ Subgroup.mem_top τ)
        have hnn : 0 ≤ n % (orderOf σ : ℤ) := Int.emod_nonneg n (by rw [hord]; exact Int.natCast_ne_zero.mpr hl.ne_zero)
        have hpow : σ ^ n = σ ^ (n % (orderOf σ : ℤ)).toNat := by
          rw [← zpow_natCast, Int.toNat_of_nonneg hnn]; exact (zpow_mod_orderOf σ n).symm
        rw [hpow]
        induction (n % (orderOf σ : ℤ)).toNat with
        | zero => simp
        | succ i ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hσu0]
      rw [IsGalois.fixedField_top] at hmemK
      obtain ⟨k, hk⟩ := IntermediateField.mem_bot.mp hmemK
      have hk' : algebraMap K H k⁻¹ = (((u0⁻¹ : (𝓞 H)ˣ) : 𝓞 H) : H) := by
        rw [map_inv₀, hk]
        symm
        apply eq_inv_of_mul_eq_one_left
        simp
      let kO : 𝓞 K := ⟨k, (isIntegral_algebraMap_iff (algebraMap K H).injective).mp (hk ▸ u0.1.2)⟩
      let k'O : 𝓞 K := ⟨k⁻¹, (isIntegral_algebraMap_iff (algebraMap K H).injective).mp (hk' ▸ (u0⁻¹).1.2)⟩
      have hkk' : kO * k'O = 1 := by
        apply Subtype.ext; apply (algebraMap K H).injective
        change algebraMap K H (k * k⁻¹) = algebraMap K H 1
        rw [map_mul, map_one, hk, hk']
        simp
      let kUnit : (𝓞 K)ˣ := Units.mkOfMulEqOne kO k'O hkk'
      refine ⟨(m : ℤ), hm0, ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      refine ⟨Additive.ofMul kUnit, Subtype.ext ?_⟩
      change qU (Additive.ofMul (Units.map (algebraMap (𝓞 K) (𝓞 H)).toMonoidHom kUnit)) = (m : ℤ) • qU e
      rw [natCast_zsmul, ← map_nsmul qU]
      congr 1; apply Additive.toMul.injective; apply Units.ext; apply Subtype.ext; exact hk
    have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.ker incK)
    rw [hker_rank, add_zero, incK.quotKerEquivRange.finrank_eq] at h1
    have h2 := Submodule.finrank_quotient_add_finrank (LinearMap.range incK)
    rw [hcoker_rank, zero_add] at h2
    rw [← h2, h1, NumberField.Units.finrank_eq, NumberField.Units.rank]
  have hrank_M : Module.finrank ℤ M = (l - 1) * (rK + 1) := by
    have hsup_rank : Module.finrank ℤ (UG ⊔ M : Submodule ℤ U) = Module.finrank ℤ U := by
      have hq0 : Module.finrank ℤ (U ⧸ (UG ⊔ M)) = 0 := by
        rw [Module.finrank_eq_zero_iff]; intro y
        obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        exact ⟨(l : ℤ), Int.natCast_ne_zero.mpr hl.ne_zero, by
          rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]; exact hindex u⟩
      have h1 := Submodule.finrank_quotient_add_finrank (UG ⊔ M)
      rw [hq0, zero_add] at h1; exact h1
    let eSup : (UG × M) ≃ₗ[ℤ] ↥(UG ⊔ M) :=
      LinearEquiv.ofBijective
        { toFun := fun p => ⟨p.1.1 + p.2.1, Submodule.add_mem_sup p.1.2 p.2.2⟩
          map_add' := fun a b => Subtype.ext (by change (a.1.1 + b.1.1) + (a.2.1 + b.2.1) = (a.1.1 + a.2.1) + (b.1.1 + b.2.1); abel)
          map_smul' := fun r a => Subtype.ext (by change r • a.1.1 + r • a.2.1 = r • (a.1.1 + a.2.1); rw [smul_add]) }
        ⟨fun a b h => by
          have hab : a.1.1 + a.2.1 = b.1.1 + b.2.1 := congrArg Subtype.val h
          have hsub : a.1.1 - b.1.1 = -(a.2.1 - b.2.1) := by
            apply eq_neg_of_add_eq_zero_left
            calc (a.1.1 - b.1.1) + (a.2.1 - b.2.1) = (a.1.1 + a.2.1) - (b.1.1 + b.2.1) := by abel
              _ = 0 := sub_eq_zero.mpr hab
          have hmem : a.1.1 - b.1.1 ∈ UG ⊓ M :=
            ⟨UG.sub_mem a.1.2 b.1.2, hsub ▸ M.neg_mem (M.sub_mem a.2.2 b.2.2)⟩
          rw [hdisj, Submodule.mem_bot] at hmem
          have h1 : a.1 = b.1 := Subtype.ext (sub_eq_zero.mp hmem)
          have h2 : a.2 = b.2 := Subtype.ext (sub_eq_zero.mp (neg_eq_zero.mp (hsub.symm.trans hmem)))
          exact Prod.ext h1 h2,
         fun y => by
          obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp y.2
          exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩⟩
    have hadd : Module.finrank ℤ (UG ⊔ M : Submodule ℤ U) = Module.finrank ℤ UG + Module.finrank ℤ M := by
      rw [← eSup.finrank_eq, Module.finrank_prod]
    rw [hsup_rank, hrank_U, hrank_UG] at hadd
    have hl1 : 1 ≤ l := hl.one_le
    nlinarith [Nat.sub_add_cancel hl1, Nat.sub_add_cancel (show 1 ≤ l * (rK + 1) by nlinarith)]
  -- Step 4: Tate cardinalities on `UG`, `M`, `S := UG × M`, `U`, `E`
  let φUG : UG ≃+ UG := AddEquiv.refl UG
  have hφUG_l : ∀ x, iterAddEquiv φUG l x = x := fun x => by
    have hiter : ∀ k (y : UG), iterAddEquiv φUG k y = y := fun k y => by
      induction k with | zero => rfl | succ _ ih => exact ih
    exact hiter l x
  have hUG_H1_sub : Subsingleton (H1hat l φUG) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective _ a
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective _ b
    congr 1; apply Subtype.ext
    have hkill : ∀ z : (tateN l φUG).ker, z.1 = 0 := fun z => by
      have h0 : tateN l φUG z.1 = 0 := z.2
      have hiter : ∀ i, iterAddEquiv φUG i z.1 = z.1 := fun i => by
        induction i with | zero => rfl | succ _ ih => exact ih
      rw [tateN_apply] at h0; simp only [hiter, Finset.sum_const, Finset.card_range] at h0
      have hlz : (l : ℤ) • z.1 = 0 := by rw [natCast_zsmul]; exact h0
      exact (smul_eq_zero.mp hlz).resolve_left (Int.natCast_ne_zero.mpr hl.ne_zero)
    exact (hkill x).trans (hkill y).symm
  have hUG_H1_card : Nat.card (H1hat l φUG) = 1 := Nat.card_unique
  have hUG_H0 : Finite (H0hat l φUG) ∧ Nat.card (H0hat l φUG) = l ^ rK := by
    obtain ⟨hfin_l, hcard_l⟩ := card_mod_l_free (M := UG) hl.pos
    have hN_range : (tateN l φUG).range = (nsmulAddMonoidHom l : UG →+ UG).range := by
      have hiter : ∀ i (x : UG), iterAddEquiv φUG i x = x := fun i x => by
        induction i with | zero => rfl | succ _ ih => exact ih
      ext y
      simp only [AddMonoidHom.mem_range, tateN_apply, hiter, Finset.sum_const, Finset.card_range,
        nsmulAddMonoidHom_apply]
    let fUG : UG →+ H0hat l φUG :=
      (QuotientAddGroup.mk' ((tateN l φUG).range.comap (tateD φUG).ker.subtype)).comp
        (AddMonoidHom.mk' (fun x : UG => (⟨x, sub_self x⟩ : (tateD φUG).ker)) (fun _ _ => rfl))
    have hfUG_surj : Function.Surjective fUG := fun y => by
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective _ y; exact ⟨x.1, rfl⟩
    have hfUG_ker : fUG.ker = (nsmulAddMonoidHom l : UG →+ UG).range := by
      ext x
      simp only [fUG, AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, AddMonoidHom.mk'_apply,
        QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_comap,
        AddSubgroup.coe_subtype, hN_range]
    let e0 : (UG ⧸ (nsmulAddMonoidHom l : UG →+ UG).range) ≃+ H0hat l φUG :=
      (QuotientAddGroup.quotientAddEquivOfEq hfUG_ker.symm).trans
        (QuotientAddGroup.quotientKerEquivOfSurjective fUG hfUG_surj)
    refine ⟨Finite.of_equiv _ e0.toEquiv, ?_⟩
    rw [← Nat.card_congr e0.toEquiv, hcard_l, hrank_UG]
  have := hUG_H0.1
  have hφU_M : ∀ u : U, u ∈ M ↔ φU u ∈ M := fun u => by
    have hcomm : tateN l φU (φU u) = φU (tateN l φU u) := by
      rw [tateN_apply, tateN_apply, map_sum]
      exact Finset.sum_congr rfl fun i _ => iterAddEquiv_comm_apply φU i u
    constructor
    · intro hu; change tateN l φU u = 0 at hu; show tateN l φU (φU u) = 0; rw [hcomm, hu, map_zero]
    · intro hu; change tateN l φU (φU u) = 0 at hu; show tateN l φU u = 0; exact φU.injective (by rw [← hcomm, hu, map_zero])
  let φM : M ≃+ M :=
    { toFun := fun x => ⟨φU x.1, (hφU_M x.1).mp x.2⟩
      invFun := fun x => ⟨φU.symm x.1, (hφU_M (φU.symm x.1)).mpr (by simp [x.2])⟩
      left_inv := fun x => Subtype.ext (φU.symm_apply_apply x.1)
      right_inv := fun x => Subtype.ext (φU.apply_symm_apply x.1)
      map_add' := fun x y => Subtype.ext (map_add φU x.1 y.1) }
  have hφM_coe : ∀ n (x : M), (iterAddEquiv φM n x).1 = iterAddEquiv φU n x.1 := fun n => by
    induction n with
    | zero => intro _; rfl
    | succ n ih => intro x; rw [iterAddEquiv_succ, iterAddEquiv_succ, ← ih]; rfl
  have hφM_l : ∀ x, iterAddEquiv φM l x = x := fun x => Subtype.ext (by rw [hφM_coe, hφU_l])
  have hNM0 : ∀ x : M, tateN l φM x = 0 := fun x => Subtype.ext (by
    rw [tateN_apply]
    change M.subtype (∑ i ∈ Finset.range l, iterAddEquiv φM i x) = 0
    rw [map_sum]
    simp_rw [show ∀ i, M.subtype (iterAddEquiv φM i x) = iterAddEquiv φU i x.1 from fun i => hφM_coe i x]
    exact (tateN_apply l φU x.1).symm.trans x.2)
  obtain ⟨hM_H0_fin, hM_H1_fin, hM_H0_card, hM_H1_pow⟩ := tate_norm_zero_free_card φM hφM_l hNM0
  have := hM_H0_fin; have := hM_H1_fin
  have hM_H1_card : Nat.card (H1hat l φM) = l ^ (rK + 1) := by
    rw [hrank_M, mul_comm, pow_mul] at hM_H1_pow
    have hpos : 0 < l - 1 := by have := hl.two_le; omega
    exact (Nat.pow_left_inj hpos.ne').mp hM_H1_pow
  -- Product `S := UG × M`
  let φS : (UG × M) ≃+ (UG × M) := φUG.prodCongr φM
  have hφS_l : ∀ p : UG × M, iterAddEquiv φS l p = p := fun p => by
    have hiter : ∀ n (x : UG × M), iterAddEquiv φS n x = (iterAddEquiv φUG n x.1, iterAddEquiv φM n x.2) :=
      fun n => by induction n with | zero => intro _; rfl | succ n ih => intro x; rw [iterAddEquiv_succ, ih]; rfl
    rw [hiter, hφUG_l, hφM_l]
  obtain ⟨⟨eH0S⟩, ⟨eH1S⟩⟩ := tate_prod_equiv l φUG φM
  have : Finite (H0hat l φS) := Finite.of_equiv _ eH0S.symm.toEquiv
  have : Finite (H1hat l φS) := Finite.of_equiv _ eH1S.symm.toEquiv
  have hcard_H0S : Nat.card (H0hat l φS) = l ^ rK := by
    rw [Nat.card_congr eH0S.toEquiv, Nat.card_prod, hUG_H0.2, hM_H0_card, mul_one]
  have hcard_H1S : Nat.card (H1hat l φS) = l ^ (rK + 1) := by
    rw [Nat.card_congr eH1S.toEquiv, Nat.card_prod, hUG_H1_card, hM_H1_card, one_mul]
  -- SES `0 → S →[iS] U →[pQ] Q → 0`, where `Q := U ⧸ (UG ⊔ M)` is finite!
  let iS : (UG × M) →+ U :=
    AddMonoidHom.mk' (fun p => p.1.1 + p.2.1) (fun a b => by simp; abel)
  have hiS_inj : Function.Injective iS := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨a, b⟩ hab
    change a.1 + b.1 = 0 at hab
    have ha_eq : a.1 = -b.1 := eq_neg_of_add_eq_zero_left hab
    have hmem : a.1 ∈ UG ⊓ M := ⟨a.2, ha_eq ▸ M.neg_mem b.2⟩
    rw [hdisj, Submodule.mem_bot] at hmem
    have hb0 : b.1 = 0 := by rw [hmem, zero_add] at hab; exact hab
    exact Prod.ext (Subtype.ext hmem) (Subtype.ext hb0)
  have hiS_range : iS.range = (UG ⊔ M).toAddSubgroup := by
    ext u; simp only [AddMonoidHom.mem_range, Submodule.mem_toAddSubgroup, Submodule.mem_sup]
    constructor
    · rintro ⟨⟨a, b⟩, rfl⟩; exact ⟨a.1, a.2, b.1, b.2, rfl⟩
    · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  let Q := U ⧸ (UG ⊔ M).toAddSubgroup
  let pQ : U →+ Q := QuotientAddGroup.mk' (UG ⊔ M).toAddSubgroup
  have hφU_sup : ∀ u : U, u ∈ (UG ⊔ M).toAddSubgroup → φU u ∈ (UG ⊔ M).toAddSubgroup := by
    intro u hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
    rw [map_add]
    have hφa : φU a = a := (sub_eq_zero.mp ha).symm
    exact Submodule.add_mem_sup (hφa.symm ▸ ha) ((hφU_M b).mp hb)
  let φQ : Q ≃+ Q :=
    AddEquiv.ofBijective
      (QuotientAddGroup.map (UG ⊔ M).toAddSubgroup (UG ⊔ M).toAddSubgroup φU.toAddMonoidHom hφU_sup)
      ⟨by
        rw [injective_iff_map_eq_zero]
        intro q hq
        obtain ⟨u, rfl⟩ := QuotientAddGroup.mk'_surjective _ q
        have hmem : φU u ∈ UG ⊔ M := (QuotientAddGroup.eq_zero_iff _).mp hq
        have hinv : ∀ v : U, v ∈ UG ⊔ M → φU.symm v ∈ UG ⊔ M := by
          intro v hv
          obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
          rw [map_add]
          have hφa : φU.symm a = a := φU.injective (by rw [φU.apply_symm_apply]; exact sub_eq_zero.mp ha)
          exact Submodule.add_mem_sup (hφa.symm ▸ ha) ((hφU_M (φU.symm b)).mpr (by simpa using hb))
        have hu : u ∈ UG ⊔ M := by simpa using hinv (φU u) hmem
        exact (QuotientAddGroup.eq_zero_iff _).mpr hu,
       fun y => by
         obtain ⟨u, rfl⟩ := QuotientAddGroup.mk'_surjective _ y
         obtain ⟨u', hu'⟩ := φU.surjective u
         exact ⟨QuotientAddGroup.mk' _ u', by change QuotientAddGroup.mk' _ (φU u') = _; rw [hu']⟩⟩
  have hφQ_l : ∀ q : Q, iterAddEquiv φQ l q = q := fun q => by
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk'_surjective _ q
    have hcoe : ∀ n (y : U), iterAddEquiv φQ n (pQ y) = pQ (iterAddEquiv φU n y) := fun n => by
      induction n with | zero => intro _; rfl | succ n ih => intro y; rw [iterAddEquiv_succ, ih]; rfl
    rw [hcoe, hφU_l]
  have hQ_fin : Finite Q := by
    have hle : (nsmulAddMonoidHom l : U →+ U).range ≤ (UG ⊔ M).toAddSubgroup := by
      rintro _ ⟨u, rfl⟩; rw [nsmulAddMonoidHom_apply, ← natCast_zsmul]; exact hindex u
    have := (card_mod_l_free (M := U) hl.pos).1
    exact Finite.of_surjective
      (QuotientAddGroup.map (nsmulAddMonoidHom l : U →+ U).range (UG ⊔ M).toAddSubgroup
        (AddMonoidHom.id U) hle)
      (fun y => by obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective _ y; exact ⟨QuotientAddGroup.mk' _ x, rfl⟩)
  -- Finiteness of `H0hat l φU`, `H1hat l φU`, `H0hat l φE`
  have hH0U_fin : Finite (H0hat l φU) := by
    have hle : (nsmulAddMonoidHom l : (tateD φU).ker →+ (tateD φU).ker).range ≤
        (tateN l φU).range.comap (tateD φU).ker.subtype := by
      rintro _ ⟨x, rfl⟩
      refine ⟨x.1, ?_⟩
      have hfix : φU x.1 = x.1 := (sub_eq_zero.mp x.2).symm
      have hiter : ∀ i, iterAddEquiv φU i x.1 = x.1 := fun i => by
        induction i with | zero => rfl | succ _ ih => rw [iterAddEquiv_succ, ih, hfix]
      rw [tateN_apply]; simp [hiter]
    have : Module.Finite ℤ (tateD φU).ker := inferInstanceAs (Module.Finite ℤ UG)
    have := finite_quot_nsmul_of_fg (A := (tateD φU).ker) hl.pos
    exact Finite.of_surjective
      (QuotientAddGroup.map _ _ (AddMonoidHom.id _) hle)
      (fun y => by obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective _ y; exact ⟨QuotientAddGroup.mk' _ x, rfl⟩)
  have hH1U_fin : Finite (H1hat l φU) := by
    -- Surject `H1hat l φM → H1hat l φU` via `M = (tateN l φU).ker`
    let fM : H1hat l φM →+ H1hat l φU :=
      QuotientAddGroup.lift _ ((QuotientAddGroup.mk' _).comp
        (AddMonoidHom.mk' (fun x : (tateN l φM).ker => (⟨x.1.1, x.1.2⟩ : (tateN l φU).ker)) (fun _ _ => rfl)))
        (by
          rintro x ⟨m0, hm0⟩
          rw [AddMonoidHom.mem_ker]
          simp only [AddMonoidHom.comp_apply, AddMonoidHom.mk'_apply, QuotientAddGroup.mk'_apply,
            QuotientAddGroup.eq_zero_iff]
          exact ⟨m0.1, congrArg Subtype.val hm0⟩)
    have hfM_surj : Function.Surjective fM := by
      intro y; obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective _ y
      exact ⟨QuotientAddGroup.mk' _ ⟨⟨x.1, x.2⟩, hNM0 ⟨x.1, x.2⟩⟩, rfl⟩
    exact Finite.of_surjective fM hfM_surj
  have hH0E_fin : Finite (H0hat l φE) := by
    have hle : (nsmulAddMonoidHom l : (tateD φE).ker →+ (tateD φE).ker).range ≤
        (tateN l φE).range.comap (tateD φE).ker.subtype := by
      rintro _ ⟨x, rfl⟩
      refine ⟨x.1, ?_⟩
      have hfix : φE x.1 = x.1 := (sub_eq_zero.mp x.2).symm
      have hiter : ∀ i, iterAddEquiv φE i x.1 = x.1 := fun i => by
        induction i with | zero => rfl | succ _ ih => rw [iterAddEquiv_succ, ih, hfix]
      rw [tateN_apply]; simp [hiter]
    have : Module.Finite ℤ (tateD φE).ker :=
      inferInstanceAs (Module.Finite ℤ (tateD φE).toIntLinearMap.ker)
    have := finite_quot_nsmul_of_fg (A := (tateD φE).ker) hl.pos
    exact Finite.of_surjective
      (QuotientAddGroup.map _ _ (AddMonoidHom.id _) hle)
      (fun y => by obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective _ y; exact ⟨QuotientAddGroup.mk' _ x, rfl⟩)
  -- Apply `herbrand_ses_mul` to `0 → S → U → Q → 0`
  have hQ_eq := herbrand_finite_eq l φQ hφQ_l
  have hses1 := herbrand_ses_mul l φS φU φQ hφS_l hφU_l hφQ_l iS pQ hiS_inj
    (QuotientAddGroup.mk'_surjective _) (by rw [hiS_range]; exact QuotientAddGroup.ker_mk' _)
    (fun ⟨a, b⟩ => by
      have ha_fix : φU a.1 = a.1 := (sub_eq_zero.mp a.2).symm
      change (a.1 + (φM b).1) = φU (a.1 + b.1)
      rw [map_add, ha_fix]; rfl)
    (fun _ => rfl)
  rw [hcard_H0S, hcard_H1S, hQ_eq] at hses1
  have hU_ratio : Nat.card (H0hat l φU) * l = Nat.card (H1hat l φU) := by
    have hpos : 0 < l ^ rK * Nat.card (H1hat l φQ) := mul_pos (pow_pos hl.pos _) Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc (Nat.card (H0hat l φU) * l) * (l ^ rK * Nat.card (H1hat l φQ))
        = Nat.card (H0hat l φU) * l ^ (rK + 1) * Nat.card (H1hat l φQ) := by rw [pow_succ]; ring
      _ = Nat.card (H1hat l φU) * l ^ rK * Nat.card (H1hat l φQ) := hses1
      _ = Nat.card (H1hat l φU) * (l ^ rK * Nat.card (H1hat l φQ)) := by ring
  -- Apply `herbrand_ses_mul` to `0 → T → E → U → 0`
  have hT_eq := herbrand_finite_eq l φT hφT_l
  have hses2 := herbrand_ses_mul l φT φE φU hφT_l hφE_l hφU_l T.toAddSubgroup.subtype qU
    Subtype.val_injective (QuotientAddGroup.mk'_surjective _)
    (by
      rw [QuotientAddGroup.ker_mk']
      ext x
      exact ⟨fun h => ⟨⟨x, h⟩, rfl⟩, fun ⟨⟨a, ha⟩, hax⟩ => hax ▸ ha⟩)
    (fun _ => rfl) (fun _ => rfl)
  rw [hT_eq, ← hU_ratio] at hses2
  have hE_ratio : Nat.card (H1hat l φE) = l * Nat.card (H0hat l φE) := by
    have hpos : 0 < Nat.card (H1hat l φT) * Nat.card (H0hat l φU) := mul_pos Nat.card_pos Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc Nat.card (H1hat l φE) * (Nat.card (H1hat l φT) * Nat.card (H0hat l φU))
        = Nat.card (H1hat l φE) * Nat.card (H1hat l φT) * Nat.card (H0hat l φU) := by ring
      _ = Nat.card (H0hat l φE) * Nat.card (H1hat l φT) * (Nat.card (H0hat l φU) * l) := hses2.symm
      _ = (l * Nat.card (H0hat l φE)) * (Nat.card (H1hat l φT) * Nat.card (H0hat l φU)) := by ring
  exact dvd_trans ⟨Nat.card (H0hat l φE), hE_ratio⟩ hH1E_dvd

/-! ### Part 6e: Unconditional Case 2 (`(l - 1) ∣ 2 * k`, `¬ (l - 1) ∣ k`) -/

/-- For odd prime `l` and `k` with `(l - 1) ∣ 2 * k` and `¬ (l - 1) ∣ k`, every unit `u : (ZMod l)ˣ`
satisfies `(u : ZMod l) ^ k = (legendreSym l u.1.val : ZMod l)`. -/
private lemma zmod_pow_k_eq_legendreSym {l : ℕ} [Fact l.Prime] (hl2 : l ≠ 2) {k : ℕ}
    (hdvd2 : l - 1 ∣ 2 * k) (hndvd : ¬ l - 1 ∣ k) (u : (ZMod l)ˣ) :
    ((u : ZMod l) ^ k) = (legendreSym l (u : ZMod l).val : ZMod l) := by
  have hl : l.Prime := Fact.out
  have : NeZero l := ⟨hl.ne_zero⟩
  have hodd : l % 2 = 1 := hl.eq_two_or_odd.resolve_left hl2
  obtain ⟨m, hm⟩ := hdvd2
  have hm_odd : m % 2 = 1 := by
    by_contra heven
    have h2m : 2 ∣ m := Nat.dvd_of_mod_eq_zero (by omega)
    obtain ⟨m', rfl⟩ := h2m
    exact hndvd ⟨m', by linarith⟩
  have hk_eq : k = (l / 2) * m := by
    have h2l : l - 1 = 2 * (l / 2) := by omega
    rw [h2l] at hm; linarith
  have heuler := legendreSym.eq_pow l ((u : ZMod l).val : ℤ)
  rw [Int.cast_natCast, ZMod.natCast_zmod_val] at heuler
  have hsq : ((legendreSym l (u : ZMod l).val : ℤ) : ZMod l) ^ 2 = 1 := by
    have h1 : (legendreSym l (u : ZMod l).val : ℤ) ^ 2 = 1 := by
      rw [legendreSym.sq_one]
      intro h0
      simp at h0
    rw [← Int.cast_pow, h1, Int.cast_one]
  rw [hk_eq, pow_mul, ← heuler]
  obtain ⟨q, hq⟩ : ∃ q, m = 2 * q + 1 := ⟨m / 2, by omega⟩
  rw [hq, pow_succ, pow_mul, hsq, one_pow, one_mul]

/-- **UNCONDITIONAL CASE 2 OF `PropZ` (`galoisShaLen_rat_eq_zero_of_dvd_two_mul_not_dvd`, `0` OPEN PARAMETERS!)**:
for EVERY odd prime `l ≠ 2` and EVERY `k ≥ 1` with `(l - 1) ∣ 2 * k` and `¬ (l - 1) ∣ k`:
`galoisShaLen ℚ l (k : ℤ) = 0`! -/
theorem galoisShaLen_rat_eq_zero_of_dvd_two_mul_not_dvd (l : Nat.Primes) (hl2 : (l : ℕ) ≠ 2)
    (k : ℕ) (_hk : 0 < k) (hdvd2 : (l : ℕ) - 1 ∣ 2 * k) (hndvd : ¬ (l : ℕ) - 1 ∣ k) :
    galoisShaLen ℚ l (k : ℤ) = 0 := by
  classical
  have : Fact l.1.Prime := ⟨l.2⟩
  have hl : l.1.Prime := l.2
  have : NeZero l.1 := ⟨hl.ne_zero⟩
  suffices hgen : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (D : LData ℚ Ω l.1),
      shaLen D (k : ℤ) = 0 by
    exact hgen (AlgebraicClosure ℚ) (canonicalLData ℚ l)
  intro Ω _ _ _ D
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have : NeZero ((l.1 : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
  refine shaLen_eq_zero_of_l_torsion_eq_zero D (k : ℤ) fun x hx => ?_
  obtain ⟨z, hmk, htors, hloc⟩ := exists_l_torsion_cocycle_of_sha D (k : ℤ) x hx
  -- Step 1: Construct `K = ℚ(√l*) ⊂ ℚ(ζ_l) ⊂ Ω` via the quadratic Gauss sum!
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l.1
  obtain ⟨s, hs_sq, -, hs_act⟩ := exists_quadratic_gauss_sum (Ω := Ω) (l := l.1) hl2 hζ
  have hs_ne0 : s ≠ 0 := by
    intro h0; rw [h0, zero_pow (by norm_num)] at hs_sq
    have hne : (lStar l.1 : Ω) ≠ 0 := by
      unfold lStar; split_ifs <;> simp [hl.ne_zero]
    exact hne hs_sq.symm
  let K : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ ({s} : Set Ω)
  have eK : K.algebra' = (DivisionRing.toRatAlgebra : Algebra ℚ K) := Subsingleton.elim _ _
  have hK_fd : FiniteDimensional ℚ K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral s)
  have hK_fd_rat : @Module.Finite ℚ K _ _ (DivisionRing.toRatAlgebra (R := K)).toModule := by
    convert hK_fd
    exact congrArg (fun a : Algebra ℚ K => a.toModule) eK.symm
  have : NumberField K := @NumberField.of_module_finite ℚ K _ _ _ _ hK_fd_rat
  -- Compute `finrank ℚ K = 2` and `discr K = lStar l.1`, hence `classNumber K < l.1`!
  let sK : K := IntermediateField.AdjoinSimple.gen ℚ s
  have hsK_sq : sK ^ 2 = (lStar l.1 : K) := Subtype.ext (by simpa [sK] using hs_sq)
  have hsK_adj : IntermediateField.adjoin ℚ ({sK} : Set K) = ⊤ := by
    rw [eq_top_iff]; rintro ⟨y, hy⟩ _
    let fK : K →ₐ[ℚ] Ω :=
      { toFun := Subtype.val
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl
        commutes' := fun q =>
          congrFun (congrArg DFunLike.coe
            (Subsingleton.elim (K.toSubfield.subtype.comp (algebraMap ℚ K)) (algebraMap ℚ Ω))) q }
    have hmap : IntermediateField.adjoin ℚ ({s} : Set Ω) ≤
        (IntermediateField.adjoin ℚ ({sK} : Set K)).map fK := by
      rw [IntermediateField.adjoin_simple_le_iff]
      exact ⟨sK, IntermediateField.mem_adjoin_simple_self ℚ sK, rfl⟩
    obtain ⟨w, hw, hwy⟩ := hmap hy
    have heq : w = ⟨y, hy⟩ := Subtype.ext hwy
    rwa [← heq]
  obtain ⟨hK_rank, hK_discr⟩ := quadDiscr_eq K (lStar l.1) sK hsK_sq hsK_adj
    (lStar_squarefree hl) (lStar_mod_four hl hl2) (lStar_ne_one hl)
  have hK_cn_lt : NumberField.classNumber K < l.1 :=
    classNumber_lt_of_quad_discr_prime K hl hK_rank (by rw [hK_discr, lStar_abs])
  -- Step 2: Action of `G ℚ Ω` on `s` matches `(cycZ g)^{-k} mod l`!
  have hchi_mod : ∀ g : G ℚ Ω,
      PadicInt.toZMod ((cycZ ℚ Ω l.1 g ^ (-(k : ℤ)) : ℤ_[l.1]ˣ) : ℤ_[l.1]) =
        (legendreSym l.1 (PadicInt.toZMod ((cycZ ℚ Ω l.1 g : ℤ_[l.1]ˣ) : ℤ_[l.1])).val : ZMod l.1) ∧
      g s = (legendreSym l.1 (PadicInt.toZMod ((cycZ ℚ Ω l.1 g : ℤ_[l.1]ˣ) : ℤ_[l.1])).val : Ω) * s := by
    intro g
    let uZ : (ZMod l.1)ˣ := Units.map (PadicInt.toZMod : ℤ_[l.1] →+* ZMod l.1).toMonoidHom (cycZ ℚ Ω l.1 g)
    have huZ_val : (uZ : ZMod l.1) = PadicInt.toZMod ((cycZ ℚ Ω l.1 g : ℤ_[l.1]ˣ) : ℤ_[l.1]) := rfl
    have hpow := zmod_pow_k_eq_legendreSym hl2 hdvd2 hndvd uZ
    have hsq : ((uZ : ZMod l.1) ^ k) ^ 2 = 1 := by
      rw [hpow]
      have h1 : (legendreSym l.1 (uZ : ZMod l.1).val : ℤ) ^ 2 = 1 := by
        rw [legendreSym.sq_one]; intro h0; simp at h0
      rw [← Int.cast_pow, h1, Int.cast_one]
    have hinv_eq : (uZ : ZMod l.1) ^ (-(k : ℤ)) = (uZ : ZMod l.1) ^ k := by
      rw [zpow_neg, zpow_natCast]
      exact inv_eq_of_mul_eq_one_left (by rw [← sq]; exact hsq)
    constructor
    · have hmap : ((uZ ^ (-(k : ℤ)) : (ZMod l.1)ˣ) : ZMod l.1) =
          PadicInt.toZMod ((cycZ ℚ Ω l.1 g ^ (-(k : ℤ)) : ℤ_[l.1]ˣ) : ℤ_[l.1]) := by
        have h1 : uZ ^ (-(k : ℤ)) =
            Units.map (PadicInt.toZMod : ℤ_[l.1] →+* ZMod l.1).toMonoidHom (cycZ ℚ Ω l.1 g ^ (-(k : ℤ))) :=
          (map_zpow (Units.map (PadicInt.toZMod : ℤ_[l.1] →+* ZMod l.1).toMonoidHom) _ _).symm
        exact congrArg Units.val h1
      rw [← hmap, Units.val_zpow_eq_zpow_val, hinv_eq, hpow, huZ_val]
    · have : NeZero (l.1 ^ 1) := ⟨pow_ne_zero 1 hl.ne_zero⟩
      have : NeZero ((l.1 : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.ne_zero⟩
      have hspec : g ζ = ζ ^ (PadicInt.toZModPow 1 ((cycZ ℚ Ω l.1 g : ℤ_[l.1]ˣ) : ℤ_[l.1])).val :=
        cyclotomicCharacter.spec (L := Ω) l.1 (MulSemiringAction.toRingAut (G ℚ Ω) Ω g)
          ζ (by rw [pow_one]; exact hζ.pow_eq_one)
      have h1 := hs_act g.toRingHom _ hspec
      have hval_eq : (PadicInt.toZModPow 1 ((cycZ ℚ Ω l.1 g : ℤ_[l.1]ˣ) : ℤ_[l.1])).val =
          (PadicInt.toZMod ((cycZ ℚ Ω l.1 g : ℤ_[l.1]ˣ) : ℤ_[l.1])).val := by
        have hcast : ((PadicInt.toZModPow 1 ((cycZ ℚ Ω l.1 g : ℤ_[l.1]ˣ) : ℤ_[l.1])).val : ZMod l.1) =
            PadicInt.toZMod ((cycZ ℚ Ω l.1 g : ℤ_[l.1]ˣ) : ℤ_[l.1]) := by
          have h := congrFun (congrArg DFunLike.coe
            (PadicInt.zmod_cast_comp_toZModPow (p := l.1) (m := 1) (n := 1) le_rfl))
            ((cycZ ℚ Ω l.1 g : ℤ_[l.1]ˣ) : ℤ_[l.1])
          -- Compare via `PadicInt.toZMod_spec` / `toZModPow 1`:
          have hlt1 : (PadicInt.toZModPow 1 ((cycZ ℚ Ω l.1 g : ℤ_[l.1]ˣ) : ℤ_[l.1])).val < l.1 :=
            (ZMod.val_lt _).trans_eq (pow_one l.1)
          have hker : ((cycZ ℚ Ω l.1 g : ℤ_[l.1]ˣ) : ℤ_[l.1]) -
              ((PadicInt.toZModPow 1 ((cycZ ℚ Ω l.1 g : ℤ_[l.1]ˣ) : ℤ_[l.1])).val : ℤ_[l.1]) ∈
              RingHom.ker (PadicInt.toZModPow 1 : ℤ_[l.1] →+* ZMod (l.1 ^ 1)) := by
            rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
          rw [PadicInt.ker_toZModPow, pow_one, ← PadicInt.maximalIdeal_eq_span_p,
            ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_natCast, sub_eq_zero] at hker
          exact hker.symm
        have hlt1 : (PadicInt.toZModPow 1 ((cycZ ℚ Ω l.1 g : ℤ_[l.1]ˣ) : ℤ_[l.1])).val < l.1 :=
          (ZMod.val_lt _).trans_eq (pow_one l.1)
        have h2 := congrArg ZMod.val hcast
        rwa [ZMod.val_natCast_of_lt hlt1] at h2
      simpa [hval_eq] using h1
  have hfixK_iff : ∀ g : G ℚ Ω, g ∈ K.fixingSubgroup ↔ g s = s := by
    intro g
    constructor
    · intro hg; exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hg s
        (IntermediateField.mem_adjoin_simple_self ℚ s)
    · intro hgs
      have hle : K ≤ IntermediateField.fixedField (Subgroup.zpowers g) := by
        rw [IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_fixedField_iff]
        intro τ hτ; obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ
        have hp : ∀ m : ℕ, (g ^ m) s = s := fun m => by
          induction m with
          | zero => simp
          | succ m ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hgs]
        cases n with
        | ofNat m => exact hp m
        | negSucc m =>
          rw [zpow_negSucc]
          have h1 := congrArg (fun y => (g ^ (m + 1))⁻¹ y) (hp (m + 1))
          rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply] at h1
          exact h1.symm
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy; exact (IntermediateField.mem_fixedField_iff _ _).mp (hle hy) g (Subgroup.mem_zpowers g)
  have htriv_on_K : ∀ g ∈ K.fixingSubgroup, ∀ y : QZ l.1, (l.1 : ℤ_[l.1]) • y = 0 →
      (((cycZ ℚ Ω l.1 g ^ (-(k : ℤ)) : ℤ_[l.1]ˣ) : ℤ_[l.1]) • y) = y := by
    intro g hg y hy
    obtain ⟨hm1, hm2⟩ := hchi_mod g
    have hgs : g s = s := (hfixK_iff g).mp hg
    rw [hgs] at hm2
    have hleg1 : (legendreSym l.1 (PadicInt.toZMod ((cycZ ℚ Ω l.1 g : ℤ_[l.1]ˣ) : ℤ_[l.1])).val : Ω) = 1 :=
      mul_right_cancel₀ hs_ne0 (hm2.symm.trans (one_mul s).symm)
    have hlegZ : legendreSym l.1 (PadicInt.toZMod ((cycZ ℚ Ω l.1 g : ℤ_[l.1]ˣ) : ℤ_[l.1])).val = 1 := by
      exact_mod_cast hleg1
    rw [hlegZ, Int.cast_one] at hm1
    have hmem : ((cycZ ℚ Ω l.1 g ^ (-(k : ℤ)) : ℤ_[l.1]ˣ) : ℤ_[l.1]) - 1 ∈
        RingHom.ker (PadicInt.toZMod : ℤ_[l.1] →+* ZMod l.1) := by
      rw [RingHom.mem_ker, map_sub, map_one, hm1, sub_self]
    rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hsub : (((cycZ ℚ Ω l.1 g ^ (-(k : ℤ)) : ℤ_[l.1]ˣ) : ℤ_[l.1]) - 1) • y = 0 := by
      rw [hc, mul_comm, mul_smul, hy, smul_zero]
    rwa [sub_smul, one_smul, sub_eq_zero] at hsub
  -- Step 3: Pick `δ ∈ Ine A_l` with `δ ∉ K.fixingSubgroup` so `u_δ = (cycZ δ)^{-k} - 1` is a `ℤ_[l]`-unit!
  obtain ⟨v₀, hv₀, hv₀_iff⟩ := exists_heightOneSpectrum_rat Ω l.1 hl
  have hv₀_mem : v₀ ∈ D.S := Finset.mem_coe.mp (by rw [D.hS]; exact hv₀)
  let v_l : D.S := ⟨v₀, hv₀_mem⟩
  obtain ⟨m_l, hm_l⟩ := hloc v_l
  have hAl : (D.A v_l).valuation (l.1 : Ω) < 1 := (hv₀_iff (D.A v_l)).mp (D.hA v_l)
  -- Pick a non-square `a₀ : (ZMod l.1)ˣ` and lift it to `ℤ_[l.1]ˣ` and then via `cycZ_Ine_surjective` to `δ ∈ Ine (D.A v_l)`!
  obtain ⟨a₀, ha₀_leg⟩ : ∃ a₀ : (ZMod l.1)ˣ, legendreSym l.1 (a₀ : ZMod l.1).val = -1 := by
    obtain ⟨g0, hg0⟩ := IsCyclic.exists_generator (α := (ZMod l.1)ˣ)
    refine ⟨g0, ?_⟩
    have hord0 : orderOf g0 = l.1 - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg0, Nat.card_eq_fintype_card, ZMod.card_units]
    have hpow_ne1 : (g0 : ZMod l.1) ^ (l.1 / 2) ≠ 1 := by
      intro h1
      have hg1 : g0 ^ (l.1 / 2) = 1 := Units.ext (by simpa using h1)
      have hdvd := orderOf_dvd_of_pow_eq_one hg1
      rw [hord0] at hdvd
      have hpos : 0 < l.1 / 2 := by have := hl.two_le; omega
      have hle := Nat.le_of_dvd hpos hdvd
      omega
    have heuler := legendreSym.eq_pow l.1 ((g0 : ZMod l.1).val : ℤ)
    rw [Int.cast_natCast, ZMod.natCast_zmod_val] at heuler
    rcases legendreSym.eq_one_or_neg_one l.1 (by
        intro h0
        simp only [Int.cast_natCast, ZMod.natCast_zmod_val] at h0
        exact Units.ne_zero g0 h0 :
        (((g0 : ZMod l.1).val : ℤ) : ZMod l.1) ≠ 0) with h1 | hm1
    · exfalso; rw [h1, Int.cast_one] at heuler; exact hpow_ne1 heuler.symm
    · exact hm1
  have hu_padic : ∃ u₀ : ℤ_[l.1]ˣ, PadicInt.toZMod (u₀ : ℤ_[l.1]) = (a₀ : ZMod l.1) := by
    let x0 : ℤ_[l.1] := ((a₀ : ZMod l.1).val : ℤ_[l.1])
    have hx0_mod : PadicInt.toZMod x0 = (a₀ : ZMod l.1) := by
      simp [x0]
    have hx0_unit : IsUnit x0 := by
      by_contra hnu
      have hmem : x0 ∈ IsLocalRing.maximalIdeal ℤ_[l.1] := (IsLocalRing.mem_maximalIdeal x0).mpr hnu
      rw [← PadicInt.ker_toZMod, RingHom.mem_ker, hx0_mod] at hmem
      exact Units.ne_zero a₀ hmem
    obtain ⟨u₀, hu₀⟩ := hx0_unit
    exact ⟨u₀, hu₀.symm ▸ hx0_mod⟩
  obtain ⟨u₀, hu₀⟩ := hu_padic
  obtain ⟨δ, hδ_ine, hδ_cyc⟩ := cycZ_Ine_surjective Ω l.1 (D.A v_l) hAl u₀
  have hδ_mod : PadicInt.toZMod ((cycZ ℚ Ω l.1 δ ^ (-(k : ℤ)) : ℤ_[l.1]ˣ) : ℤ_[l.1]) = -1 := by
    rw [(hchi_mod δ).1, hδ_cyc, hu₀, ha₀_leg, Int.cast_neg, Int.cast_one]
  have hδ_s : δ s = -s := by
    have h2 := (hchi_mod δ).2
    rw [hδ_cyc, hu₀, ha₀_leg, Int.cast_neg, Int.cast_one, neg_one_mul] at h2
    exact h2
  have huδ_unit : IsUnit (((cycZ ℚ Ω l.1 δ ^ (-(k : ℤ)) : ℤ_[l.1]ˣ) : ℤ_[l.1]) - 1) := by
    by_contra hnu
    have hmem : ((cycZ ℚ Ω l.1 δ ^ (-(k : ℤ)) : ℤ_[l.1]ˣ) : ℤ_[l.1]) - 1 ∈ IsLocalRing.maximalIdeal ℤ_[l.1] :=
      (IsLocalRing.mem_maximalIdeal _).mpr hnu
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_one, hδ_mod] at hmem
    have h2 : (-2 : ZMod l.1) = 0 := by ring_nf at hmem ⊢; exact hmem
    have h2' : ((2 : ℕ) : ZMod l.1) = 0 := by
      have := neg_eq_zero.mp h2; simpa using this
    exact hl2 ((Nat.dvd_prime Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 l.1).mp h2') |>.resolve_left hl.ne_one)
  obtain ⟨uδ, huδ⟩ := huδ_unit
  -- Step 4: Normalize cocycle `z' := z - B1(m_l)`! Notice `m_l` is AUTOMATICALLY `l`-torsion?!
  -- Wait: check! `m₀ := uδ⁻¹ • z(δ)` IS `l`-torsion AND `uδ • (m_l - m₀) = 0 ⟹ m_l = m₀`!!
  let m₀ : QZ l.1 := ((uδ⁻¹ : ℤ_[l.1]ˣ) : ℤ_[l.1]) • z.1 (toGS Ω _ δ)
  have hm₀_tors : (l.1 : ℤ_[l.1]) • m₀ = 0 := by
    show (l.1 : ℤ_[l.1]) • (((uδ⁻¹ : ℤ_[l.1]ˣ) : ℤ_[l.1]) • z.1 (toGS Ω _ δ)) = 0
    rw [smul_comm, htors _, smul_zero]
  have hm_eq : m_l = m₀ := by
    have h1 := hm_l δ (Ine_le_Dec (F := ℚ) (D.A v_l) hδ_ine)
    have h2 : (uδ : ℤ_[l.1]) • m_l = z.1 (toGS Ω _ δ) := by
      rw [huδ, sub_smul, one_smul]; exact h1.symm
    calc m_l = ((uδ⁻¹ : ℤ_[l.1]ˣ) : ℤ_[l.1]) • ((uδ : ℤ_[l.1]) • m_l) := by
          rw [← mul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
      _ = m₀ := by rw [h2]
  -- Define `f' : G ℚ Ω → QZ l.1 := fun g => z(g) - ((cycZ g)^{-k} • m₀ - m₀)`!
  let f' : G ℚ Ω → QZ l.1 := fun g =>
    z.1 (toGS Ω _ g) - ((((cycZ ℚ Ω l.1 g ^ (-(k : ℤ)) : ℤ_[l.1]ˣ) : ℤ_[l.1]) • m₀) - m₀)
  have hf'_tors : ∀ g : G ℚ Ω, (l.1 : ℤ_[l.1]) • f' g = 0 := fun g => by
    simp only [f', smul_sub]
    rw [htors _, smul_comm, hm₀_tors, smul_zero, sub_self, sub_self]
  have hf'_coc : ∀ a b : G ℚ Ω, f' (a * b) = f' a +
      (((cycZ ℚ Ω l.1 a ^ (-(k : ℤ)) : ℤ_[l.1]ˣ) : ℤ_[l.1]) • f' b) := by
    intro a b
    have h1 := z.2.2 (toGS Ω _ a) (toGS Ω _ b)
    have hchi : D.chi (toGS Ω _ a) = cycZ ℚ Ω l.1 a := congrArg (fun f => f a) D.hchi
    have hmap : toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 ℚ))) (a * b) =
        toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 ℚ))) a *
        toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 ℚ))) b := map_mul _ a b
    have hzc : z.1 (toGS Ω _ (a * b)) = z.1 (toGS Ω _ a) +
        (((cycZ ℚ Ω l.1 a ^ (-(k : ℤ)) : ℤ_[l.1]ˣ) : ℤ_[l.1]) • z.1 (toGS Ω _ b)) := by
      rw [hmap, h1]; congr 1
      change (((D.chi (toGS Ω _ a) ^ (-(k : ℤ)) : ℤ_[l.1]ˣ) : ℤ_[l.1]) • z.1 (toGS Ω _ b)) = _
      rw [hchi]
    dsimp only [f']
    generalize m₀ = m
    rw [hzc, map_mul, mul_zpow, Units.val_mul, smul_sub, smul_sub, ← mul_smul]
    abel
  have hf'_dec_l : ∀ g ∈ Dec (F := ℚ) (D.A v_l), f' g = 0 := fun g hg => by
    simp only [f', ← hm_eq, hm_l g hg, sub_self]
  have hf'_unram_out : ∀ (A : ValuationSubring Ω), ¬ A.valuation (l.1 : Ω) < 1 →
      ∀ σ ∈ Ine (F := ℚ) A, σ ∈ K.fixingSubgroup → f' σ = 0 := by
    intro A hA σ hσ hσK
    have hmem : σ ∈ NS Ω (D.S : Set (HeightOneSpectrum (𝓞 ℚ))) := by
      rw [D.hS]; exact ine_le_NS_above_of_not_val_lt_one Ω l.1 A hA hσ
    have hto1 : toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 ℚ))) σ = 1 :=
      (QuotientGroup.eq_one_iff σ).mpr hmem
    have hz0 : z.1 (toGS Ω _ σ) = 0 := by rw [hto1]; exact cocycle1_one (qzTw D (k : ℤ)) z.2.2
    simp only [f', hz0, htriv_on_K σ hσK m₀ hm₀_tors, sub_self]
  have hf'_unram_in : ∀ (A : ValuationSubring Ω), A.valuation (l.1 : Ω) < 1 →
      ∀ σ ∈ Ine (F := ℚ) A, σ ∈ K.fixingSubgroup → f' σ = 0 := by
    intro A hAl_A σ hσ hσK
    have hA_over : IsPlaceOver A v₀ := (hv₀_iff A).mpr hAl_A
    obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (D.hA v_l) hA_over
    have hconj_dec : g⁻¹ * σ * g ∈ Dec (F := ℚ) (D.A v_l) := by
      rw [mem_Dec, mul_smul, mul_smul, hg, mem_Dec.mp hσ.1, ← hg, inv_smul_smul]
    have h0 : f' (g⁻¹ * σ * g) = 0 := hf'_dec_l _ hconj_dec
    have hsplit : g * (g⁻¹ * σ * g) = σ * g := by group
    have hL := hf'_coc g (g⁻¹ * σ * g)
    rw [h0, smul_zero, add_zero, hsplit] at hL
    have hR := hf'_coc σ g
    rw [htriv_on_K σ hσK (f' g) (hf'_tors g)] at hR
    have heq : f' σ + f' g = f' g := hR.symm.trans hL
    exact add_right_cancel (heq.trans (zero_add (f' g)).symm)
  -- Step 5: Restrict `φ := qzLTorsToZMod ∘ f'` to `K.fixingSubgroup`; show `φ = 0` via Furtwängler!
  let φ : K.fixingSubgroup → ZMod l.1 := fun g => qzLTorsToZMod l.1 ⟨f' g.1, hf'_tors g.1⟩
  have hφ_mul : ∀ a b : K.fixingSubgroup, φ (a * b) = φ a + φ b := by
    intro a b
    have hcoc : f' (a * b).1 = f' a.1 + f' b.1 := by
      change f' (a.1 * b.1) = _
      rw [hf'_coc a.1 b.1, htriv_on_K a.1 a.2 (f' b.1) (hf'_tors b.1)]
    have hsub : (⟨f' (a * b).1, hf'_tors _⟩ : {y : QZ l.1 // (l.1 : ℤ_[l.1]) • y = 0}) =
        ⟨f' a.1 + f' b.1, by rw [smul_add, hf'_tors _, hf'_tors _, add_zero]⟩ := Subtype.ext hcoc
    change qzLTorsToZMod l.1 ⟨f' (a * b).1, hf'_tors _⟩ = _
    rw [hsub]
    exact qzLTorsToZMod_add l.1 ⟨f' a.1, hf'_tors a.1⟩ ⟨f' b.1, hf'_tors b.1⟩
  have hφ_lc : IsLocallyConstant φ := by
    have hf'_cont : Continuous f' := by
      have hz_cont : Continuous (fun g : G ℚ Ω => z.1 (toGS Ω _ g)) :=
        z.2.1.comp (continuous_toGS Ω _)
      have hc_cont : Continuous (fun g : G ℚ Ω =>
          (((cycZ ℚ Ω l.1 g ^ (-(k : ℤ)) : ℤ_[l.1]ˣ) : ℤ_[l.1]) • m₀) - m₀) := by
        -- `g ↦ (cycZ g)^{-k} • m₀` depends only on `cycZ g mod l` (since `l • m₀ = 0`), wait: even simpler,
        -- `PadicInt` acts continuously on discrete `QZ l.1`? Or just show it's locally constant directly!
        have hlc_mod : IsLocallyConstant (fun g : G ℚ Ω =>
            PadicInt.toZMod ((cycZ ℚ Ω l.1 g : ℤ_[l.1]ˣ) : ℤ_[l.1])) := by
          rw [IsLocallyConstant.iff_isOpen_fiber]
          intro r
          by_cases hr : ∃ g₀ : G ℚ Ω, PadicInt.toZMod ((cycZ ℚ Ω l.1 g₀ : ℤ_[l.1]ˣ) : ℤ_[l.1]) = r
          · obtain ⟨g₀, rfl⟩ := hr
            have heq : (fun g : G ℚ Ω => PadicInt.toZMod ((cycZ ℚ Ω l.1 g : ℤ_[l.1]ˣ) : ℤ_[l.1])) ⁻¹'
                {PadicInt.toZMod ((cycZ ℚ Ω l.1 g₀ : ℤ_[l.1]ˣ) : ℤ_[l.1])} =
                (fun g : G ℚ Ω => ((cycZ ℚ Ω l.1 g : ℤ_[l.1]ˣ) : ℤ_[l.1])) ⁻¹'
                  Metric.closedBall ((cycZ ℚ Ω l.1 g₀ : ℤ_[l.1]ˣ) : ℤ_[l.1]) ((l.1 : ℝ) ^ (-((1 : ℕ) : ℤ))) := by
              ext g
              simp only [Set.mem_preimage, Set.mem_singleton_iff, Metric.mem_closedBall, dist_eq_norm]
              rw [PadicInt.norm_le_pow_iff_mem_span_pow, pow_one, ← PadicInt.maximalIdeal_eq_span_p,
                ← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, sub_eq_zero]
            rw [heq]
            exact (IsUltrametricDist.isOpen_closedBall _
              (zpow_pos (Nat.cast_pos.mpr hl.pos) _).ne').preimage
              (Units.continuous_val.comp (continuous_cycZ ℚ Ω l.1))
          · have hemp : (fun g : G ℚ Ω => PadicInt.toZMod ((cycZ ℚ Ω l.1 g : ℤ_[l.1]ˣ) : ℤ_[l.1])) ⁻¹'
                {r} = ∅ := by
              ext g; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
              intro h; exact hr ⟨g, h⟩
            rw [hemp]; exact isOpen_empty
        -- Show `g ↦ (cycZ g)^{-k} • m₀ - m₀` factors through `toZMod ∘ cycZ` (since `l • m₀ = 0`)!
        have hfact : ∀ g₁ g₂ : G ℚ Ω,
            PadicInt.toZMod ((cycZ ℚ Ω l.1 g₁ : ℤ_[l.1]ˣ) : ℤ_[l.1]) =
              PadicInt.toZMod ((cycZ ℚ Ω l.1 g₂ : ℤ_[l.1]ˣ) : ℤ_[l.1]) →
            (((cycZ ℚ Ω l.1 g₁ ^ (-(k : ℤ)) : ℤ_[l.1]ˣ) : ℤ_[l.1]) • m₀) - m₀ =
              (((cycZ ℚ Ω l.1 g₂ ^ (-(k : ℤ)) : ℤ_[l.1]ˣ) : ℤ_[l.1]) • m₀) - m₀ := by
          intro g₁ g₂ heq
          have hm12 : PadicInt.toZMod ((cycZ ℚ Ω l.1 g₁ ^ (-(k : ℤ)) : ℤ_[l.1]ˣ) : ℤ_[l.1]) =
              PadicInt.toZMod ((cycZ ℚ Ω l.1 g₂ ^ (-(k : ℤ)) : ℤ_[l.1]ˣ) : ℤ_[l.1]) := by
            rw [(hchi_mod g₁).1, (hchi_mod g₂).1, heq]
          have hmem : ((cycZ ℚ Ω l.1 g₁ ^ (-(k : ℤ)) : ℤ_[l.1]ˣ) : ℤ_[l.1]) -
              ((cycZ ℚ Ω l.1 g₂ ^ (-(k : ℤ)) : ℤ_[l.1]ˣ) : ℤ_[l.1]) ∈
              RingHom.ker (PadicInt.toZMod : ℤ_[l.1] →+* ZMod l.1) := by
            rw [RingHom.mem_ker, map_sub, hm12, sub_self]
          rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hmem
          obtain ⟨c, hc⟩ := hmem
          have hsub : (((cycZ ℚ Ω l.1 g₁ ^ (-(k : ℤ)) : ℤ_[l.1]ˣ) : ℤ_[l.1]) -
              ((cycZ ℚ Ω l.1 g₂ ^ (-(k : ℤ)) : ℤ_[l.1]ˣ) : ℤ_[l.1])) • m₀ = 0 := by
            rw [hc, mul_comm, mul_smul, hm₀_tors, smul_zero]
          rw [sub_smul, sub_eq_zero] at hsub
          rw [hsub]
        have hlc_c : IsLocallyConstant (fun g : G ℚ Ω =>
            (((cycZ ℚ Ω l.1 g ^ (-(k : ℤ)) : ℤ_[l.1]ˣ) : ℤ_[l.1]) • m₀) - m₀) := by
          rw [IsLocallyConstant.iff_isOpen_fiber]
          intro y
          have hunion : (fun g : G ℚ Ω =>
              (((cycZ ℚ Ω l.1 g ^ (-(k : ℤ)) : ℤ_[l.1]ˣ) : ℤ_[l.1]) • m₀) - m₀) ⁻¹' {y} =
              ⋃ (g₀ : G ℚ Ω) (_ : (((cycZ ℚ Ω l.1 g₀ ^ (-(k : ℤ)) : ℤ_[l.1]ˣ) : ℤ_[l.1]) • m₀) - m₀ = y),
                (fun g : G ℚ Ω => PadicInt.toZMod ((cycZ ℚ Ω l.1 g : ℤ_[l.1]ˣ) : ℤ_[l.1])) ⁻¹'
                  {PadicInt.toZMod ((cycZ ℚ Ω l.1 g₀ : ℤ_[l.1]ˣ) : ℤ_[l.1])} := by
            ext g
            simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion]
            constructor
            · intro h; exact ⟨g, h, rfl⟩
            · rintro ⟨g₀, hg₀, hmod⟩; rw [hfact g g₀ hmod, hg₀]
          rw [hunion]
          exact isOpen_iUnion fun g₀ => isOpen_iUnion fun _ => hlc_mod.isOpen_fiber _
        exact hlc_c.continuous
      exact hz_cont.sub hc_cont
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro r
    have hpre : φ ⁻¹' {r} = (fun g : K.fixingSubgroup => f' g.1) ⁻¹'
        {y : QZ l.1 | ∃ hy : (l.1 : ℤ_[l.1]) • y = 0, qzLTorsToZMod l.1 ⟨y, hy⟩ = r} := by
      ext g; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
      exact ⟨fun h => ⟨hf'_tors g.1, h⟩, fun ⟨_, h⟩ => h⟩
    rw [hpre]
    exact (isOpen_discrete _).preimage (hf'_cont.comp continuous_subtype_val)
  have hφ_zero : ∀ g : K.fixingSubgroup, φ g = 0 := by
    by_contra hne
    push Not at hne
    obtain ⟨g₀, hg₀⟩ := hne
    -- Build unramified cyclic degree-`l` extension `H / K` from `W := ker φ ≤ K.fixingSubgroup`!
    let φM : K.fixingSubgroup →* Multiplicative (ZMod l.1) :=
      MonoidHom.mk' (fun g => Multiplicative.ofAdd (φ g)) (fun a b => by rw [hφ_mul, ofAdd_add])
    let W_sub : Subgroup K.fixingSubgroup := φM.ker
    let W : Subgroup (G ℚ Ω) := W_sub.map K.fixingSubgroup.subtype
    have hW_mem : ∀ g : G ℚ Ω, g ∈ W ↔ ∃ hg : g ∈ K.fixingSubgroup, φ ⟨g, hg⟩ = 0 := by
      intro g; simp only [W, Subgroup.mem_map, Subgroup.coe_subtype]
      constructor
      · rintro ⟨⟨g', hg'⟩, hker, rfl⟩; exact ⟨hg', hker⟩
      · rintro ⟨hg, h0⟩; exact ⟨⟨g, hg⟩, h0, rfl⟩
    have hK_open : IsOpen (K.fixingSubgroup : Set (G ℚ Ω)) :=
      (InfiniteGalois.isOpen_iff_finite K).mpr inferInstance
    have hW_open : IsOpen (W : Set (G ℚ Ω)) := by
      have hsub_open : IsOpen (W_sub : Set K.fixingSubgroup) := by
        have hpre : (W_sub : Set K.fixingSubgroup) = φ ⁻¹' {0} := by ext g; exact Iff.rfl
        rw [hpre]; exact hφ_lc.isOpen_fiber 0
      rw [Topology.IsOpenEmbedding.isOpen_iff_image_isOpen hK_open.isOpenEmbedding_subtypeVal] at hsub_open
      change IsOpen ((W_sub.map K.fixingSubgroup.subtype : Subgroup (G ℚ Ω)) : Set (G ℚ Ω))
      rw [Subgroup.coe_map]
      exact hsub_open
    have hW_closed : IsClosed (W : Set (G ℚ Ω)) := Subgroup.isClosed_of_isOpen W hW_open
    let H : IntermediateField ℚ Ω := IntermediateField.fixedField W
    have hHW : H.fixingSubgroup = W := InfiniteGalois.fixingSubgroup_fixedField ⟨W, hW_closed⟩
    have eH : H.algebra' = (DivisionRing.toRatAlgebra : Algebra ℚ H) := Subsingleton.elim _ _
    have hH_fd : FiniteDimensional ℚ H := by rw [← InfiniteGalois.isOpen_iff_finite, hHW]; exact hW_open
    have hH_fd_rat : @Module.Finite ℚ H _ _ (DivisionRing.toRatAlgebra (R := H)).toModule := by
      convert hH_fd
      exact congrArg (fun a : Algebra ℚ H => a.toModule) eH.symm
    have : NumberField H := @NumberField.of_module_finite ℚ H _ _ _ _ hH_fd_rat
    have hK_le_H : K ≤ H := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup K]
      exact IntermediateField.fixedField_antitone (fun g hg => (hW_mem g).mp hg |>.1)
    let : Algebra K H :=
      RingHom.toAlgebra
        { toFun := fun y => ⟨y.1, hK_le_H y.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
    have : IsScalarTower ℚ K Ω := IsScalarTower.of_algebraMap_eq fun q =>
      (congrFun (congrArg DFunLike.coe
        (Subsingleton.elim (K.toSubfield.subtype.comp (algebraMap ℚ K)) (algebraMap ℚ Ω))) q).symm
    have : IsScalarTower ℚ K H := IsScalarTower.of_algebraMap_eq (fun q => Subtype.ext (by simp))
    have : IsScalarTower K H Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have : IsAlgClosure K Ω := IsAlgClosure.mk inferInstance (Algebra.IsAlgebraic.tower_top (K := ℚ) K)
    -- View `H` as an `IntermediateField K Ω` to use `IsGalois K H` and `ramificationIdx_eq_one_of_ine_fixes`!
    let HK : IntermediateField K Ω :=
      { carrier := H.carrier
        mul_mem' := H.mul_mem'
        one_mem' := H.one_mem'
        add_mem' := H.add_mem'
        zero_mem' := H.zero_mem'
        algebraMap_mem' := fun y => hK_le_H y.2
        inv_mem' := H.inv_mem' }
    have eHK_type : (HK : Type) = (H : Type) := rfl
    have hK_alg_eq : HK.algebra' = (inferInstance : Algebra K H) := rfl
    have hHK_fix : ∀ g : G K Ω, g ∈ HK.fixingSubgroup ↔ g.restrictScalars ℚ ∈ W := by
      intro g
      rw [IntermediateField.mem_fixingSubgroup_iff, ← hHW, IntermediateField.mem_fixingSubgroup_iff]
      rfl
    have hHK_normal : HK.fixingSubgroup.Normal := by
      refine ⟨fun g hg τ => ?_⟩
      rw [hHK_fix] at hg ⊢
      obtain ⟨hgK, hg0⟩ := (hW_mem _).mp hg
      have hτK : τ.restrictScalars ℚ ∈ K.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]; intro y hy; exact τ.commutes ⟨y, hy⟩
      have hconjK : (τ.restrictScalars ℚ * g.restrictScalars ℚ * (τ.restrictScalars ℚ)⁻¹) ∈ K.fixingSubgroup :=
        K.fixingSubgroup.mul_mem (K.fixingSubgroup.mul_mem hτK hgK) (K.fixingSubgroup.inv_mem hτK)
      refine (hW_mem _).mpr ⟨hconjK, ?_⟩
      have heq : (⟨(τ * g * τ⁻¹).restrictScalars ℚ, hconjK⟩ : K.fixingSubgroup) =
          ⟨τ.restrictScalars ℚ, hτK⟩ * ⟨g.restrictScalars ℚ, hgK⟩ * ⟨τ.restrictScalars ℚ, hτK⟩⁻¹ := by
        apply Subtype.ext; rfl
      have hφ1 : φ 1 = 0 := by have := hφ_mul 1 1; rw [mul_one] at this; exact left_eq_add.mp this
      have hφ_inv : ∀ u : K.fixingSubgroup, φ u⁻¹ = -φ u := fun u => by
        have h := hφ_mul u⁻¹ u; rw [inv_mul_cancel, hφ1] at h; exact eq_neg_of_add_eq_zero_left h.symm
      change φ ⟨(τ * g * τ⁻¹).restrictScalars ℚ, hconjK⟩ = 0
      rw [heq, hφ_mul, hφ_mul, hφ_inv, hg0]; ring
    have : IsGalois K Ω := IsGalois.tower_top_of_isGalois ℚ K Ω
    have : IsGalois K H := (InfiniteGalois.normal_iff_isGalois HK).mp hHK_normal
    -- Compute `Module.finrank K H = l.1` via `|Gal(H/K)| = [K.fixingSubgroup : W_sub] = l.1`!
    have hdeg_KH : Module.finrank K H = l.1 := by
      -- Map `G K Ω →* Multiplicative (ZMod l.1)` has kernel `HK.fixingSubgroup` and is surjective (since `φ g₀ ≠ 0`)!
      let θ : G K Ω →* Multiplicative (ZMod l.1) :=
        MonoidHom.mk' (fun g => Multiplicative.ofAdd (φ ⟨g.restrictScalars ℚ, by
          rw [IntermediateField.mem_fixingSubgroup_iff]; intro y hy; exact g.commutes ⟨y, hy⟩⟩))
          (fun a b => by
            have haK : a.restrictScalars ℚ ∈ K.fixingSubgroup := by
              rw [IntermediateField.mem_fixingSubgroup_iff]; intro y hy; exact a.commutes ⟨y, hy⟩
            have hbK : b.restrictScalars ℚ ∈ K.fixingSubgroup := by
              rw [IntermediateField.mem_fixingSubgroup_iff]; intro y hy; exact b.commutes ⟨y, hy⟩
            have habK : (a * b).restrictScalars ℚ ∈ K.fixingSubgroup := by
              rw [IntermediateField.mem_fixingSubgroup_iff]; intro y hy; exact (a * b).commutes ⟨y, hy⟩
            have hab : (⟨(a * b).restrictScalars ℚ, habK⟩ : K.fixingSubgroup) =
                ⟨a.restrictScalars ℚ, haK⟩ * ⟨b.restrictScalars ℚ, hbK⟩ := Subtype.ext rfl
            rw [hab, hφ_mul, ofAdd_add])
      have hθ_ker : θ.ker = HK.fixingSubgroup := by
        ext g
        rw [MonoidHom.mem_ker, hHK_fix, hW_mem]
        have hgK : g.restrictScalars ℚ ∈ K.fixingSubgroup := by
          rw [IntermediateField.mem_fixingSubgroup_iff]; intro y hy; exact g.commutes ⟨y, hy⟩
        constructor
        · intro h; exact ⟨hgK, Multiplicative.ofAdd.injective h⟩
        · rintro ⟨_, h0⟩; exact congrArg Multiplicative.ofAdd h0
      have hθ_surj : Function.Surjective θ := by
        intro r
        set c := Multiplicative.toAdd r
        -- Lift `g₀ : K.fixingSubgroup` to `G K Ω`
        let g₀K : G K Ω := { g₀.1.toRingEquiv with commutes' := fun y =>
          (IntermediateField.mem_fixingSubgroup_iff _ _).mp g₀.2 y.1 y.2 }
        have hφ_pow : ∀ (u : K.fixingSubgroup) (n : ℕ), φ (u ^ n) = (n : ZMod l.1) * φ u := fun u n => by
          induction n with
          | zero => have h := hφ_mul 1 1; rw [mul_one] at h; simpa using left_eq_add.mp h
          | succ n ih => rw [pow_succ, hφ_mul, ih, Nat.cast_add, Nat.cast_one]; ring
        let n := (c * (φ g₀)⁻¹).val
        refine ⟨g₀K ^ n, ?_⟩
        have hsub_pow : (⟨(g₀K ^ n).restrictScalars ℚ, by
            rw [IntermediateField.mem_fixingSubgroup_iff]
            intro y hy; exact (g₀K ^ n).commutes ⟨y, hy⟩⟩ : K.fixingSubgroup) = g₀ ^ n := by
          apply Subtype.ext
          change (g₀K ^ n).restrictScalars ℚ = (g₀ ^ n).1
          rw [Subgroup.coe_pow]
          induction n with
          | zero => rfl
          | succ m ih =>
            ext x
            change (g₀K ^ m) (g₀K x) = (g₀.1 ^ m) (g₀.1 x)
            exact congrArg (fun f : G ℚ Ω => f (g₀.1 x)) ih
        change Multiplicative.ofAdd (φ ⟨(g₀K ^ n).restrictScalars ℚ, _⟩) = r
        rw [hsub_pow, hφ_pow, ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hg₀, mul_one]
        rfl
      -- `G K Ω ⧸ HK.fixingSubgroup ≃* Gal(H/K)` and `G K Ω ⧸ θ.ker ≃* Multiplicative (ZMod l.1)`!
      let e1 : (G K Ω ⧸ HK.fixingSubgroup) ≃* Multiplicative (ZMod l.1) :=
        (QuotientGroup.quotientMulEquivOfEq hθ_ker.symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective θ hθ_surj)
      let resH : G K Ω →* (H ≃ₐ[K] H) := AlgEquiv.restrictNormalHom H
      have hresH_surj : Function.Surjective resH := AlgEquiv.restrictNormalHom_surjective Ω
      have hresH_ker : resH.ker = HK.fixingSubgroup := by
        ext g
        simp only [MonoidHom.mem_ker, IntermediateField.mem_fixingSubgroup_iff]
        constructor
        · intro h y hy
          have h1 := AlgEquiv.restrictNormal_commutes g H ⟨y, hy⟩
          have h2 : resH g ⟨y, hy⟩ = ⟨y, hy⟩ := by rw [h]; rfl
          change (resH g ⟨y, hy⟩ : Ω) = g y at h1
          rw [h2] at h1; exact h1.symm
        · intro h
          ext ⟨y, hy⟩
          have h1 := AlgEquiv.restrictNormal_commutes g H ⟨y, hy⟩
          change (resH g ⟨y, hy⟩ : Ω) = g y at h1
          rw [h1, h y hy]; rfl
      let e2 : (G K Ω ⧸ HK.fixingSubgroup) ≃* (H ≃ₐ[K] H) :=
        (QuotientGroup.quotientMulEquivOfEq hresH_ker.symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective resH hresH_surj)
      have hcard := Nat.card_congr (e2.symm.trans e1).toEquiv
      rw [IsGalois.card_aut_eq_finrank K H,
        Nat.card_eq_fintype_card, Fintype.card_congr Multiplicative.toAdd, ZMod.card] at hcard
      exact hcard
    -- Show `H / K` is unramified at EVERY finite prime `w : HeightOneSpectrum (𝓞 H)`!
    have hunram : ∀ w : HeightOneSpectrum (𝓞 H), w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
      intro w
      refine (ramificationIdx_eq_one_of_ine_fixes (K := K) (L := H) (Ω := Ω) (fun A σ hσ y => ?_) w).2
      have hσ_rat : σ.restrictScalars ℚ ∈ Ine (F := ℚ) A :=
        ⟨hσ.1, fun a ha => hσ.2 a ha⟩
      have hσK : σ.restrictScalars ℚ ∈ K.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]; intro z hz; exact σ.commutes ⟨z, hz⟩
      have hf'0 : f' (σ.restrictScalars ℚ) = 0 := by
        by_cases hAl_A : A.valuation (l.1 : Ω) < 1
        · exact hf'_unram_in A hAl_A _ hσ_rat hσK
        · exact hf'_unram_out A hAl_A _ hσ_rat hσK
      have hφ0 : φ ⟨σ.restrictScalars ℚ, hσK⟩ = 0 :=
        (qzLTorsToZMod_eq_zero_iff l.1 _).mpr hf'0
      have hmemW : σ.restrictScalars ℚ ∈ W := (hW_mem _).mpr ⟨hσK, hφ0⟩
      exact (IntermediateField.mem_fixingSubgroup_iff H (σ.restrictScalars ℚ)).mp (hHW.symm ▸ hmemW) y.1 y.2
    -- Contradiction: `l.1 ∣ classNumber K` vs `0 < classNumber K < l.1`!
    have hdvd_cn : l.1 ∣ NumberField.classNumber K :=
      dvd_classNumber_of_unramified_cyclic_prime_ext hl2 hK_rank hdeg_KH hunram
    have hcn_pos : 0 < NumberField.classNumber K := Fintype.card_pos
    exact Nat.not_dvd_of_pos_of_lt hcn_pos hK_cn_lt hdvd_cn
  -- Step 6: `f' = 0` on ALL of `G ℚ Ω`, hence `z = B1(m₀)` and `x = 0`!
  have hf'_all : ∀ g : G ℚ Ω, f' g = 0 := by
    intro g
    by_cases hgK : g ∈ K.fixingSubgroup
    · exact (qzLTorsToZMod_eq_zero_iff l.1 ⟨f' g, hf'_tors g⟩).mp (hφ_zero ⟨g, hgK⟩)
    · have hgs_neg : g s = -s := by
        have hsq_eq : (g s) ^ 2 = s ^ 2 := by rw [← map_pow, hs_sq, map_intCast]
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq_eq with hpos | hneg
        · exfalso; exact hgK ((hfixK_iff g).mpr hpos)
        · exact hneg
      have huK : δ⁻¹ * g ∈ K.fixingSubgroup := by
        rw [hfixK_iff]
        change δ⁻¹ (g s) = s
        rw [hgs_neg, map_neg]
        have h1 := congrArg (fun y => δ⁻¹ y) hδ_s
        rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply, map_neg] at h1
        exact h1.symm
      have hfu0 : f' (δ⁻¹ * g) = 0 :=
        (qzLTorsToZMod_eq_zero_iff l.1 ⟨f' _, hf'_tors _⟩).mp (hφ_zero ⟨δ⁻¹ * g, huK⟩)
      have hδ0 : f' δ = 0 := hf'_dec_l δ (Ine_le_Dec (F := ℚ) (D.A v_l) hδ_ine)
      have hsplit : g = δ * (δ⁻¹ * g) := by rw [mul_inv_cancel_left]
      rw [hsplit, hf'_coc, hδ0, hfu0, smul_zero, add_zero]
  apply Subtype.ext
  rw [← hmk]
  change (Submodule.Quotient.mk z : H1 (qzTw D (k : ℤ))) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  refine (mem_B1 (qzTw D (k : ℤ)) _).mpr ⟨m₀, fun gS => ?_⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gS
  have hchi_g : D.chi (toGS Ω _ g) = cycZ ℚ Ω l.1 g := congrArg (fun f => f g) D.hchi
  change z.1 (toGS Ω _ g) = (((D.chi (toGS Ω _ g) ^ (-(k : ℤ)) : ℤ_[l.1]ˣ) : ℤ_[l.1]) • m₀ - m₀)
  rw [hchi_g]
  exact sub_eq_zero.mp (hf'_all g)

end FurtwanglerHerbrandAndCaseTwo

/-! ## Section 7: Headline Unconditional `CountZ` / `PropZ` Theorems (`0` Open Parameters) -/

section HeadlineCountZAnnihilation

/-- Re-export of Case 1 (`(l - 1) ∣ k`) from `RHDirect.Stage13CountZLocalKummer`. -/
theorem galoisShaLen_rat_eq_zero_of_dvd_k (l : Nat.Primes) (hl2 : (l : ℕ) ≠ 2)
    (k : ℕ) (hk : 0 < k) (hdvd : (l : ℕ) - 1 ∣ k) :
    galoisShaLen ℚ l (k : ℤ) = 0 :=
  Stage13CountZLocalKummer.galoisShaLen_rat_eq_zero_of_dvd_k l hl2 k hk hdvd

/-- **UNCONDITIONAL `PropZ` (`galoisShaLen_rat_eq_zero_of_dvd_two_mul_k`, `0` OPEN PARAMETERS!)**:
for EVERY odd prime `l ≠ 2` and EVERY `k ≥ 1` with `(l - 1) ∣ 2 * k`:
`galoisShaLen ℚ l (k : ℤ) = 0`! -/
theorem galoisShaLen_rat_eq_zero_of_dvd_two_mul_k (l : Nat.Primes) (hl2 : (l : ℕ) ≠ 2)
    (k : ℕ) (hk : 0 < k) (hdvd : (l : ℕ) - 1 ∣ 2 * k) :
    galoisShaLen ℚ l (k : ℤ) = 0 := by
  by_cases h1 : (l : ℕ) - 1 ∣ k
  · exact galoisShaLen_rat_eq_zero_of_dvd_k l hl2 k hk h1
  · exact galoisShaLen_rat_eq_zero_of_dvd_two_mul_not_dvd l hl2 k hk hdvd h1

/-- **UNCONDITIONAL `realGaloisSelmerSystem.shaLen ℚ l k = 0` (`0` OPEN PARAMETERS!)**:
for EVERY odd prime `l ≠ 2` and EVERY `k ≥ 1` with `(l - 1) ∣ 2 * k`:
`Stage12GaloisShaLen.realGaloisSelmerSystem.shaLen ℚ l k = 0`! -/
theorem realGalois_shaLen_rat_eq_zero_of_dvd_two_mul_k (l : Nat.Primes) (hl2 : (l : ℕ) ≠ 2)
    (k : ℕ) (hk : 0 < k) (hdvd : (l : ℕ) - 1 ∣ 2 * k) :
    realGaloisSelmerSystem.shaLen ℚ l k = 0 :=
  galoisShaLen_rat_eq_zero_of_dvd_two_mul_k l hl2 k hk hdvd

/-- **UNCONDITIONAL `CountZ` TRIVIAL-CHARACTER ANNIHILATION (`countZ_trivial_vlen_eq_zero`, `0` OPEN PARAMETERS!)**:
for ANY `Vlen : ENat` bounded by `realGaloisSelmerSystem.shaLen ℚ l k` (such as
`Stage13MaschkeCharDecomp.Vlen E l k χ` on the trivial-character eigenspace via
`Vlen_trivial_le_sha_rat`), for EVERY odd prime `l ≠ 2` and `k ≥ 1` with `(l - 1) ∣ 2 * k`:
`Vlen = 0`! -/
theorem countZ_trivial_vlen_eq_zero (l : Nat.Primes) (hl2 : (l : ℕ) ≠ 2)
    (k : ℕ) (hk : 0 < k) (hdvd : (l : ℕ) - 1 ∣ 2 * k)
    {Vlen : ENat} (hVle : Vlen ≤ realGaloisSelmerSystem.shaLen ℚ l k) :
    Vlen = 0 := by
  rw [realGalois_shaLen_rat_eq_zero_of_dvd_two_mul_k l hl2 k hk hdvd] at hVle
  exact le_antisymm hVle (OrderBot.bot_le _)

/-- **DIRECT FIELD #7e (`CountZ`) DISCHARGE TEMPLATE (`0` OPEN PARAMETERS!)**:
given ANY trivial-character bound `Vlen E l k χ ≤ realGaloisSelmerSystem.shaLen ℚ l k`
(supplied unconditionally by `Stage13MaschkeCharDecomp.Vlen_trivial_le_sha_rat_of_isChiField`),
discharges lines 958–960 of `Stage13Field1Unification.lean` unconditionally with ZERO open parameters! -/
theorem field1_7e_countZ_discharge
    (Vlen : (E : Type) → [Field E] → [NumberField E] → Nat.Primes → ℕ → GalCharTag → ENat)
    {E : Type} [Field E] [NumberField E]
    (l : Nat.Primes) (k : ℕ)
    (hl2 : (l : ℕ) ≠ 2) (hk : 0 < k) (hdvd : (l : ℕ) - 1 ∣ 2 * k)
    (χ : GalCharTag)
    (_hpropZ : @PropZResidualBernoulliUnit l.1 k ⟨l.2⟩)
    (hVle : Vlen E l k χ ≤ realGaloisSelmerSystem.shaLen ℚ l k) :
    Vlen E l k χ = 0 :=
  countZ_trivial_vlen_eq_zero l hl2 k hk hdvd hVle

end HeadlineCountZAnnihilation

end RHDirect.Stage13CountZAnnihilation

end
