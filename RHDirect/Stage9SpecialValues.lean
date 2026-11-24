import RHDirect.Stage6ClassNumberFormula
import RHDirect.Stage7PadicLFunction
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# RHDirect.Stage9SpecialValues

Unconditional (0 `sorry`, 0 custom `axiom`, 0 warnings, 0 info) formalization of:

1. **Generalized Bernoulli Numbers `B_{k, χ}` & Exact Negative-Integer Special Values
   `DirichletCharacter.LFunction χ (1 - k) = -B_{k, χ} / k`**:
   - Concrete definition `genBernoulli χ k` (`q^{k-1} ∑_{a=1}^{q-1} χ(a) B_k(a/q)` for `q ≥ 2`,
     and `bernoulli k` for `q = 1`).
   - Exact parity vanishing (`genBernoulli_eq_zero_of_parity`), level-change Euler-factor identity
     (`genBernoulli_changeLevel` via Raabe's multiplication formula `raabe_bernoulli_eval`), and
     the full negative-integer evaluation `LFunction_one_sub_nat_eq_genBernoulli` for **every**
     `q ≥ 1`, **every** non-principal `χ ≠ 1` (primitive or imprimitive!), and **every** `k ≥ 1`
     (including `k = 1`, i.e., `L(0, χ) = -B_{1, χ}`!).
   - **Complex-to-$p$-adic Interpolation Bridge (`kubotaLeopoldtZeta_eq_riemannZeta_one_sub`)**:
     for every odd prime `p` and every `k ≥ 1` with `k ≡ i [MOD p - 1]`, the Kubota–Leopoldt
     $p$-adic zeta value `Stage7PadicLFunction.kubotaLeopoldtZeta` and the Euler-removed complex
     Riemann zeta value `(1 - p^k) * riemannZeta (1 - (k + 1))` are the exact $p$-adic and complex
     images of the same algebraic rational `(1 - p^k) * (-B_{k+1} / (k + 1)) ∈ ℚ`!

2. **Exact Positive-Integer Special Values of `L(k, χ)` & `riemannZeta`**:
   - General Euler–Dirichlet special value formula (`LFunction_pos_nat_eq_genBernoulli`) for every
     primitive `χ ≠ 1` and `k ≥ 1` with `χ(-1) = (-1)^k`:
     `L(k, χ) = -(χ(-1) * τ(χ) / (2 * k!)) * (2 * π * I / q)^k * genBernoulli χ⁻¹ k`.
   - Concrete primitive quadratic characters `chi4` (`χ₋₄` mod 4) and `chi3` (`χ₋₃` mod 3), with:
     - `LFunction_one_chi4_eq` (Leibniz–Madhava): `L(1, χ₋₄) = π / 4`,
     - `LFunction_three_chi4_eq` (Euler): `L(3, χ₋₄) = π³ / 32`,
     - `LFunction_one_chi3_eq`: `L(1, χ₋₃) = π / (3 * √3)`.
   - Exact values of Mathlib's `riemannZeta`:
     `riemannZeta_zero_eq` (`-1/2`), `riemannZeta_neg_one_eq` (`-1/12`),
     `riemannZeta_neg_three_eq` (`1/120`), `riemannZeta_two_eq` (`π²/6`),
     `riemannZeta_four_eq` (`π⁴/90`), `riemannZeta_six_eq` (`π⁶/945`).

3. **Unconditional Irrationality of `π²`, `π`, and `e^r` (`∀ r : ℚ, r ≠ 0`)**:
   - Niven's 1947 proof of `irrational_pi_sq : Irrational (Real.pi ^ 2)` and its corollary
     `irrational_pi : Irrational Real.pi`.
   - Unified Hermite–Niven proof of `irrational_exp_rat : ∀ r : ℚ, r ≠ 0 → Irrational (Real.exp r)`
     (including `irrational_exp_one : Irrational (Real.exp 1)`).
-/

noncomputable section

open Complex DirichletCharacter Finset MeasureTheory Set Filter Topology
open RHDirect.Stage3BombieriVinogradov RHDirect.Stage6ClassNumberFormula
open scoped BigOperators Nat

namespace RHDirect.Stage9SpecialValues

/-! ## Section 1: Generalized Bernoulli Numbers `B_{k, χ}` & `L(1 - k, χ) = -B_{k, χ} / k` -/

/-- The `k`-th generalized Bernoulli number `B_{k, χ}` attached to a Dirichlet character
`χ : DirichletCharacter ℂ q`:
`q^(k - 1) * ∑_{a = 1}^{q - 1} χ(a) * B_k(a / q)` for `q ≥ 2`, and `bernoulli k` for `q = 1`. -/
def genBernoulli {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (k : ℕ) : ℂ :=
  if q = 1 then
    (bernoulli k : ℂ)
  else
    (q : ℂ) ^ ((k : ℤ) - 1) *
      ∑ a ∈ Finset.Ico 1 q,
        χ (a : ZMod q) *
          ((Polynomial.bernoulli k).map (algebraMap ℚ ℂ)).eval ((a : ℂ) / (q : ℂ))

/-- Bridge between complex evaluation of `(Polynomial.bernoulli k).map (algebraMap ℚ ℂ)` at a
rational argument and rational evaluation of `Polynomial.bernoulli k`. -/
lemma eval_map_bernoulli_ratCast (k : ℕ) (x : ℚ) :
    ((Polynomial.bernoulli k).map (algebraMap ℚ ℂ)).eval (x : ℂ) =
      (((Polynomial.bernoulli k).eval x : ℚ) : ℂ) := by
  have h := (Polynomial.hom_eval₂ (Polynomial.bernoulli k) (RingHom.id ℚ) (algebraMap ℚ ℂ) x).symm
  simpa only [Polynomial.eval_map, RingHom.comp_id, Polynomial.eval₂_id, eq_ratCast] using h

lemma eval_map_bernoulli_natDiv (k a q : ℕ) :
    ((Polynomial.bernoulli k).map (algebraMap ℚ ℂ)).eval ((a : ℂ) / (q : ℂ)) =
      (((Polynomial.bernoulli k).eval ((a : ℚ) / (q : ℚ)) : ℚ) : ℂ) := by
  have h := eval_map_bernoulli_ratCast k ((a : ℚ) / (q : ℚ))
  simpa only [Rat.cast_div, Rat.cast_natCast] using h

/-- Reflection identity for `Polynomial.bernoulli k` evaluated at `(q - a) / q` in `ℂ`. -/
lemma eval_map_bernoulli_sub_div {q a : ℕ} (hq : q ≠ 0) (ha : a ≤ q) (k : ℕ) :
    ((Polynomial.bernoulli k).map (algebraMap ℚ ℂ)).eval (((q - a : ℕ) : ℂ) / (q : ℂ)) =
      (-1 : ℂ) ^ k *
        ((Polynomial.bernoulli k).map (algebraMap ℚ ℂ)).eval ((a : ℂ) / (q : ℂ)) := by
  rw [eval_map_bernoulli_natDiv, eval_map_bernoulli_natDiv]
  have hqQ : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have harg : ((q - a : ℕ) : ℚ) / (q : ℚ) = 1 - (a : ℚ) / (q : ℚ) := by
    rw [Nat.cast_sub ha]
    field_simp [hqQ]
  rw [harg, Polynomial.bernoulli_eval_one_sub]
  push_cast
  rfl

/-- Helper: reflection `a ↦ q - a` transforms `χ (q - a) = χ (-1) * χ a`. -/
private lemma char_sub_eq {q a : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ha : a ≤ q) :
    χ ((q - a : ℕ) : ZMod q) = χ (-1 : ZMod q) * χ (a : ZMod q) := by
  have hcast : ((q - a : ℕ) : ZMod q) = (-1 : ZMod q) * (a : ZMod q) := by
    rw [Nat.cast_sub ha, ZMod.natCast_self, zero_sub, neg_one_mul]
  rw [hcast, map_mul]

/-- Any non-principal character has modulus `q ≥ 2`. -/
private lemma two_le_of_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    2 ≤ q := by
  have hpos : 0 < q := NeZero.pos q
  by_contra hlt
  have hq1 : q = 1 := by omega
  subst hq1
  exact hχ (Subsingleton.elim χ 1)

/-- Any odd character is non-principal (and hence has modulus `q ≥ 2`). -/
private lemma ne_one_of_odd {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hodd : χ.Odd) :
    χ ≠ 1 := by
  intro h1
  have hpos : χ (-1 : ZMod q) = 1 := by rw [h1]; exact MulChar.one_apply isUnit_one.neg
  have hneg : χ (-1 : ZMod q) = -1 := hodd
  rw [hpos] at hneg
  norm_num at hneg

/-- For `q ≥ 2` and `χ ≠ 1`, `genBernoulli χ k` can be written as a sum over all `j : ZMod q`
(since `χ 0 = 0`). -/
theorem genBernoulli_eq_sum_zmod {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (k : ℕ) :
    genBernoulli χ k =
      (q : ℂ) ^ ((k : ℤ) - 1) *
        ∑ j : ZMod q,
          χ j * ((Polynomial.bernoulli k).map (algebraMap ℚ ℂ)).eval ((j.val : ℂ) / (q : ℂ)) := by
  have hq2 : 2 ≤ q := two_le_of_ne_one hχ
  have hq_ne1 : q ≠ 1 := by omega
  unfold genBernoulli
  rw [if_neg hq_ne1]
  congr 1
  have h0 : χ (0 : ZMod q) = 0 := χ.map_zero' hq_ne1
  have hrange : Finset.range q = insert 0 (Finset.Ico 1 q) := by
    ext a; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
  have hsum_range :
      ∑ a ∈ Finset.range q,
          χ (a : ZMod q) *
            ((Polynomial.bernoulli k).map (algebraMap ℚ ℂ)).eval ((a : ℂ) / (q : ℂ)) =
        ∑ a ∈ Finset.Ico 1 q,
          χ (a : ZMod q) *
            ((Polynomial.bernoulli k).map (algebraMap ℚ ℂ)).eval ((a : ℂ) / (q : ℂ)) := by
    rw [hrange, Finset.sum_insert (by simp), Nat.cast_zero, h0, zero_mul, zero_add]
  rw [← hsum_range]
  refine Finset.sum_bij (fun a _ => (a : ZMod q)) ?_ ?_ ?_ ?_
  · intro _ _; exact Finset.mem_univ _
  · intro a₁ ha₁ a₂ ha₂ h
    simp only [Finset.mem_range] at ha₁ ha₂
    have hv := congrArg ZMod.val h
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha₁, Nat.mod_eq_of_lt ha₂] at hv
  · intro j _
    exact ⟨j.val, Finset.mem_range.mpr (ZMod.val_lt j), ZMod.natCast_zmod_val j⟩
  · intro a ha
    simp only [Finset.mem_range] at ha
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt ha]

/-- **Parity vanishing (even character, odd `k`)**: for `q ≥ 2` and even `χ` (`χ(-1) = 1`),
`genBernoulli χ k = 0` for every odd `k` (including `k = 1`). -/
theorem genBernoulli_eq_zero_of_even_odd {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : q ≠ 1) (heven : χ.Even) {k : ℕ} (hk : Odd k) :
    genBernoulli χ k = 0 := by
  unfold genBernoulli
  rw [if_neg hq]
  set S : ℂ := ∑ a ∈ Finset.Ico 1 q,
    χ (a : ZMod q) * ((Polynomial.bernoulli k).map (algebraMap ℚ ℂ)).eval ((a : ℂ) / (q : ℂ))
  have hS : S = -S := by
    dsimp only [S]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_bij (fun a _ => q - a) ?_ ?_ ?_ ?_
    · intro a ha; simp only [Finset.mem_Ico] at ha ⊢; omega
    · intro a₁ ha₁ a₂ ha₂ h; simp only [Finset.mem_Ico] at ha₁ ha₂; omega
    · intro b hb; simp only [Finset.mem_Ico] at hb
      exact ⟨q - b, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro a ha
      have ha' := Finset.mem_Ico.mp ha
      rw [char_sub_eq χ ha'.2.le, heven, one_mul,
        eval_map_bernoulli_sub_div (NeZero.ne q) ha'.2.le k, hk.neg_one_pow]
      ring
  have hS0 : S = 0 := by
    have h2 : (2 : ℂ) * S = 0 := by linear_combination hS
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  rw [hS0, mul_zero]

/-- **Parity vanishing (odd character, even `k`)**: for every odd `χ` (`χ(-1) = -1`) and every
even `k : ℕ`, `genBernoulli χ k = 0`. -/
theorem genBernoulli_eq_zero_of_odd_even {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hodd : χ.Odd) {k : ℕ} (hk : Even k) :
    genBernoulli χ k = 0 := by
  have hq : q ≠ 1 := by
    have := two_le_of_ne_one (ne_one_of_odd hodd); omega
  unfold genBernoulli
  rw [if_neg hq]
  set S : ℂ := ∑ a ∈ Finset.Ico 1 q,
    χ (a : ZMod q) * ((Polynomial.bernoulli k).map (algebraMap ℚ ℂ)).eval ((a : ℂ) / (q : ℂ))
  have hS : S = -S := by
    dsimp only [S]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_bij (fun a _ => q - a) ?_ ?_ ?_ ?_
    · intro a ha; simp only [Finset.mem_Ico] at ha ⊢; omega
    · intro a₁ ha₁ a₂ ha₂ h; simp only [Finset.mem_Ico] at ha₁ ha₂; omega
    · intro b hb; simp only [Finset.mem_Ico] at hb
      exact ⟨q - b, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro a ha
      have ha' := Finset.mem_Ico.mp ha
      rw [char_sub_eq χ ha'.2.le, hodd,
        eval_map_bernoulli_sub_div (NeZero.ne q) ha'.2.le k, hk.neg_one_pow]
      ring
  have hS0 : S = 0 := by
    have h2 : (2 : ℂ) * S = 0 := by linear_combination hS
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  rw [hS0, mul_zero]

/-- **Combined Parity Vanishing Theorem for Generalized Bernoulli Numbers**:
for every non-principal `χ ≠ 1` and every `k ≥ 1`:
1. if `χ(-1) = 1` and `Odd k`, then `genBernoulli χ k = 0`;
2. if `χ(-1) = -1` and `Even k`, then `genBernoulli χ k = 0`. -/
theorem genBernoulli_eq_zero_of_parity {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {k : ℕ} (_hk : 1 ≤ k) :
    (χ (-1 : ZMod q) = 1 → Odd k → genBernoulli χ k = 0) ∧
    (χ (-1 : ZMod q) = -1 → Even k → genBernoulli χ k = 0) := by
  have hq : q ≠ 1 := by have := two_le_of_ne_one hχ; omega
  exact ⟨fun he ho => genBernoulli_eq_zero_of_even_odd hq he ho,
    fun ho he => genBernoulli_eq_zero_of_odd_even ho he⟩

/-- Explicit simplified formula for `genBernoulli χ 1` when `χ ≠ 1`:
`B_{1, χ} = (1 / q) * ∑_{a = 1}^{q - 1} a * χ(a)`. -/
theorem genBernoulli_one_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    genBernoulli χ 1 = (q : ℂ)⁻¹ * ∑ a ∈ Finset.Ico 1 q, (a : ℂ) * χ (a : ZMod q) := by
  have hq2 : 2 ≤ q := two_le_of_ne_one hχ
  have hq_ne1 : q ≠ 1 := by omega
  have hsum0 : ∑ a ∈ Finset.Ico 1 q, χ (a : ZMod q) = 0 := by
    have h0 : χ (0 : ZMod q) = 0 := χ.map_zero' hq_ne1
    have hrange : Finset.range q = insert 0 (Finset.Ico 1 q) := by
      ext a; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
    have hfull : ∑ a ∈ Finset.range q, χ (a : ZMod q) = ∑ a : ZMod q, χ a := by
      refine Finset.sum_bij (fun a _ => (a : ZMod q)) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro a₁ ha₁ a₂ ha₂ h
        simp only [Finset.mem_range] at ha₁ ha₂
        have hv := congrArg ZMod.val h
        rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha₁, Nat.mod_eq_of_lt ha₂] at hv
      · intro j _; exact ⟨j.val, Finset.mem_range.mpr (ZMod.val_lt j), ZMod.natCast_zmod_val j⟩
      · intro _ _; rfl
    have htot : ∑ a : ZMod q, χ a = 0 := χ.sum_eq_zero_of_ne_one hχ
    rw [← hfull, hrange, Finset.sum_insert (by simp), Nat.cast_zero, h0, zero_add] at htot
    exact htot
  unfold genBernoulli
  rw [if_neg hq_ne1]
  have hexp : ((1 : ℕ) : ℤ) - 1 = 0 := by norm_num
  rw [hexp, zpow_zero, one_mul]
  have hterm :
      ∑ a ∈ Finset.Ico 1 q,
          χ (a : ZMod q) *
            ((Polynomial.bernoulli 1).map (algebraMap ℚ ℂ)).eval ((a : ℂ) / (q : ℂ)) =
        (q : ℂ)⁻¹ * (∑ a ∈ Finset.Ico 1 q, (a : ℂ) * χ (a : ZMod q)) -
          (2 : ℂ)⁻¹ * ∑ a ∈ Finset.Ico 1 q, χ (a : ZMod q) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [eval_map_bernoulli_natDiv, Polynomial.bernoulli_one, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    push_cast
    ring
  rw [hterm, hsum0, mul_zero, sub_zero]

private lemma changeLevel_apply_nat_of_coprime {M N : ℕ} (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) {b : ℕ} (hb : Nat.Coprime b N) :
    DirichletCharacter.changeLevel hMN χ (b : ZMod N) = χ (b : ZMod M) := by
  have h := DirichletCharacter.changeLevel_eq_cast_of_dvd' χ hMN (a := (b : ℤ))
    (Nat.isCoprime_iff_coprime.mpr hb)
  simpa using h

private lemma changeLevel_apply_neg_one {M N : ℕ} (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) :
    DirichletCharacter.changeLevel hMN χ (-1 : ZMod N) = χ (-1 : ZMod M) := by
  have h := DirichletCharacter.changeLevel_eq_cast_of_dvd' χ hMN (a := (-1 : ℤ))
    isCoprime_one_left.neg_left
  simpa using h

private lemma genBernoulli_eq_sum_range {N : ℕ} [NeZero N] {ψ : DirichletCharacter ℂ N}
    (hψ : ψ ≠ 1) {k : ℕ} (hk : 1 ≤ k) :
    genBernoulli ψ k =
      (N : ℂ) ^ (k - 1) *
        ∑ b ∈ Finset.range N,
          ψ (b : ZMod N) * (((Polynomial.bernoulli k).eval ((b : ℚ) / (N : ℚ)) : ℚ) : ℂ) := by
  have hN2 := two_le_of_ne_one hψ
  unfold genBernoulli
  rw [if_neg (by omega : N ≠ 1)]
  have hexp : ((k : ℤ) - 1) = ((k - 1 : ℕ) : ℤ) := by omega
  rw [hexp, zpow_natCast]
  congr 1
  have h0 : ψ (0 : ZMod N) = 0 := ψ.map_zero' (by omega)
  have hrange : Finset.range N = insert 0 (Finset.Ico 1 N) := by
    ext a; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
  rw [hrange, Finset.sum_insert (by simp), Nat.cast_zero, h0, zero_mul, zero_add]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [eval_map_bernoulli_natDiv]

/-- One-prime level-change step for `genBernoulli` via Raabe's multiplication formula:
for any prime `p`, `M ≥ 1`, `χ ≠ 1` mod `M`, and `k ≥ 1`,
`B_{k, changeLevel (M ∣ p*M) χ} = (1 - χ(p) * p^{k-1}) * B_{k, χ}`. -/
private lemma genBernoulli_changeLevel_prime_mul {M p : ℕ} [NeZero M] [NeZero (p * M)]
    (hp : p.Prime) {χ : DirichletCharacter ℂ M} (hχ : χ ≠ 1) {k : ℕ} (hk : 1 ≤ k) :
    genBernoulli (DirichletCharacter.changeLevel (dvd_mul_left M p) χ) k =
      (1 - χ (p : ZMod M) * (p : ℂ) ^ (k - 1)) * genBernoulli χ k := by
  set ψ := DirichletCharacter.changeLevel (dvd_mul_left M p) χ
  have hψ : ψ ≠ 1 := fun h1 => hχ ((DirichletCharacter.changeLevel_eq_one_iff (dvd_mul_left M p)).mp h1)
  have hM2 : 2 ≤ M := two_le_of_ne_one hχ
  have hM_pos : 0 < M := NeZero.pos M
  rw [genBernoulli_eq_sum_range hψ hk, genBernoulli_eq_sum_range hχ hk]
  -- Raabe sum identity: `p^(k-1) * ∑_{b < p*M} χ(b) B_k(b / (p*M)) = ∑_{a < M} χ(a) B_k(a / M)`
  have hraabe :
      (p : ℂ) ^ (k - 1) *
          ∑ b ∈ Finset.range (p * M),
            χ (b : ZMod M) *
              (((Polynomial.bernoulli k).eval ((b : ℚ) / ((p * M : ℕ) : ℚ)) : ℚ) : ℂ) =
        ∑ a ∈ Finset.range M,
          χ (a : ZMod M) * (((Polynomial.bernoulli k).eval ((a : ℚ) / (M : ℚ)) : ℚ) : ℂ) := by
    have hbij :
        ∑ b ∈ Finset.range (p * M),
            χ (b : ZMod M) *
              (((Polynomial.bernoulli k).eval ((b : ℚ) / ((p * M : ℕ) : ℚ)) : ℚ) : ℂ) =
          ∑ a ∈ Finset.range M, ∑ j ∈ Finset.range p,
            χ ((a + j * M : ℕ) : ZMod M) *
              (((Polynomial.bernoulli k).eval (((a + j * M : ℕ) : ℚ) / ((p * M : ℕ) : ℚ)) : ℚ) : ℂ) := by
      rw [← Finset.sum_product']
      refine Finset.sum_bij (fun b _ => (b % M, b / M)) ?_ ?_ ?_ ?_
      · intro b hb
        simp only [Finset.mem_range] at hb
        simp only [Finset.mem_product, Finset.mem_range]
        exact ⟨Nat.mod_lt b hM_pos, (Nat.div_lt_iff_lt_mul hM_pos).mpr hb⟩
      · intro b₁ _ b₂ _ h
        have h1 := congrArg Prod.fst h
        have h2 := congrArg Prod.snd h
        dsimp only at h1 h2
        rw [← Nat.div_add_mod b₁ M, ← Nat.div_add_mod b₂ M, h1, h2]
      · intro ⟨a, j⟩ h
        simp only [Finset.mem_product, Finset.mem_range] at h
        refine ⟨a + j * M, Finset.mem_range.mpr (by nlinarith), ?_⟩
        ext
        · dsimp only
          rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h.1]
        · dsimp only
          rw [Nat.add_mul_div_right a j hM_pos, Nat.div_eq_of_lt h.1, zero_add]
      · intro b _
        have hdiv : b % M + b / M * M = b := by
          rw [add_comm, mul_comm]; exact Nat.div_add_mod b M
        rw [hdiv]
    rw [hbij, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hinner :
        ∑ j ∈ Finset.range p,
            χ ((a + j * M : ℕ) : ZMod M) *
              (((Polynomial.bernoulli k).eval (((a + j * M : ℕ) : ℚ) / ((p * M : ℕ) : ℚ)) : ℚ) : ℂ) =
          χ (a : ZMod M) *
            ∑ j ∈ Finset.range p,
              (((Polynomial.bernoulli k).eval ((((a : ℚ) / (M : ℚ)) + (j : ℚ)) / (p : ℚ)) : ℚ) : ℂ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hchar : ((a + j * M : ℕ) : ZMod M) = (a : ZMod M) := by
        simp [Nat.cast_add, Nat.cast_mul]
      have harg :
          ((a + j * M : ℕ) : ℚ) / ((p * M : ℕ) : ℚ) =
            ((a : ℚ) / (M : ℚ) + (j : ℚ)) / (p : ℚ) := by
        have hMq : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
        have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
        push_cast
        field_simp [hMq, hpq]
      rw [hchar, harg]
    rw [hinner]
    have hraabeQ := Stage7PadicLFunction.raabe_bernoulli_eval hp.pos hk ((a : ℚ) / (M : ℚ))
    have hraabeC :
        (p : ℂ) ^ (k - 1) *
            ∑ j ∈ Finset.range p,
              (((Polynomial.bernoulli k).eval ((((a : ℚ) / (M : ℚ)) + (j : ℚ)) / (p : ℚ)) : ℚ) : ℂ) =
          (((Polynomial.bernoulli k).eval ((a : ℚ) / (M : ℚ)) : ℚ) : ℂ) := by
      have hcast := congrArg (fun q : ℚ => (q : ℂ)) hraabeQ
      simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_sum] using hcast
    calc (p : ℂ) ^ (k - 1) *
          (χ (a : ZMod M) *
            ∑ j ∈ Finset.range p,
              (((Polynomial.bernoulli k).eval ((((a : ℚ) / (M : ℚ)) + (j : ℚ)) / (p : ℚ)) : ℚ) : ℂ))
        = χ (a : ZMod M) *
            ((p : ℂ) ^ (k - 1) *
              ∑ j ∈ Finset.range p,
                (((Polynomial.bernoulli k).eval ((((a : ℚ) / (M : ℚ)) + (j : ℚ)) / (p : ℚ)) : ℚ) : ℂ)) := by
          ring
      _ = χ (a : ZMod M) * (((Polynomial.bernoulli k).eval ((a : ℚ) / (M : ℚ)) : ℚ) : ℂ) := by
          rw [hraabeC]
  -- Evaluate `ψ (b : ZMod (p * M))` in terms of `χ (b : ZMod M)`
  have hψ_val : ∀ b : ℕ,
      ψ (b : ZMod (p * M)) = if p ∣ b then 0 else χ (b : ZMod M) := by
    intro b
    by_cases hpb : p ∣ b
    · rw [if_pos hpb]
      have hnu : ¬ IsUnit (b : ZMod (p * M)) := by
        rw [ZMod.isUnit_iff_coprime]
        intro hcop
        have hd : p ∣ Nat.gcd b (p * M) := Nat.dvd_gcd hpb (dvd_mul_right p M)
        rw [hcop.gcd_eq_one] at hd
        exact hp.not_dvd_one hd
      exact MulChar.map_nonunit ψ hnu
    · rw [if_neg hpb]
      have hcop_iff : Nat.Coprime b (p * M) ↔ Nat.Coprime b M := by
        rw [Nat.coprime_mul_iff_right]
        exact and_iff_right ((hp.coprime_iff_not_dvd.mpr hpb).symm)
      by_cases hcopM : Nat.Coprime b M
      · exact changeLevel_apply_nat_of_coprime (dvd_mul_left M p) χ (hcop_iff.mpr hcopM)
      · have hnu1 : ¬ IsUnit (b : ZMod (p * M)) := fun hu =>
          hcopM (hcop_iff.mp ((ZMod.isUnit_iff_coprime b (p * M)).mp hu))
        have hnu2 : ¬ IsUnit (b : ZMod M) := fun hu =>
          hcopM ((ZMod.isUnit_iff_coprime b M).mp hu)
        rw [MulChar.map_nonunit ψ hnu1, MulChar.map_nonunit χ hnu2]
  -- Split `∑_{b < p*M} ψ(b) B_k(b/(p*M))` as total `χ`-sum minus multiples of `p`
  have hsplit :
      ∑ b ∈ Finset.range (p * M),
          ψ (b : ZMod (p * M)) *
            (((Polynomial.bernoulli k).eval ((b : ℚ) / ((p * M : ℕ) : ℚ)) : ℚ) : ℂ) =
        (∑ b ∈ Finset.range (p * M),
          χ (b : ZMod M) *
            (((Polynomial.bernoulli k).eval ((b : ℚ) / ((p * M : ℕ) : ℚ)) : ℚ) : ℂ)) -
        χ (p : ZMod M) *
          ∑ c ∈ Finset.range M,
            χ (c : ZMod M) * (((Polynomial.bernoulli k).eval ((c : ℚ) / (M : ℚ)) : ℚ) : ℂ) := by
    have hdiff :
        (∑ b ∈ Finset.range (p * M),
          χ (b : ZMod M) *
            (((Polynomial.bernoulli k).eval ((b : ℚ) / ((p * M : ℕ) : ℚ)) : ℚ) : ℂ)) -
        (∑ b ∈ Finset.range (p * M),
          ψ (b : ZMod (p * M)) *
            (((Polynomial.bernoulli k).eval ((b : ℚ) / ((p * M : ℕ) : ℚ)) : ℚ) : ℂ)) =
        ∑ b ∈ (Finset.range (p * M)).filter (fun b => p ∣ b),
          χ (b : ZMod M) *
            (((Polynomial.bernoulli k).eval ((b : ℚ) / ((p * M : ℕ) : ℚ)) : ℚ) : ℂ) := by
      rw [← Finset.sum_sub_distrib, Finset.sum_filter]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hψ_val b]
      split_ifs <;> ring
    have hmult :
        ∑ b ∈ (Finset.range (p * M)).filter (fun b => p ∣ b),
            χ (b : ZMod M) *
              (((Polynomial.bernoulli k).eval ((b : ℚ) / ((p * M : ℕ) : ℚ)) : ℚ) : ℂ) =
          χ (p : ZMod M) *
            ∑ c ∈ Finset.range M,
              χ (c : ZMod M) * (((Polynomial.bernoulli k).eval ((c : ℚ) / (M : ℚ)) : ℚ) : ℂ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_bij (fun b _ => b / p) ?_ ?_ ?_ ?_
      · intro b hb
        simp only [Finset.mem_filter, Finset.mem_range] at hb ⊢
        exact (Nat.div_lt_iff_lt_mul hp.pos).mpr (by rw [mul_comm]; exact hb.1)
      · intro b₁ hb₁ b₂ hb₂ h
        simp only [Finset.mem_filter] at hb₁ hb₂
        rw [← Nat.mul_div_cancel' hb₁.2, ← Nat.mul_div_cancel' hb₂.2, h]
      · intro c hc
        simp only [Finset.mem_range] at hc
        refine ⟨p * c, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mul_lt_mul_of_pos_left hc hp.pos),
          dvd_mul_right p c⟩, Nat.mul_div_cancel_left c hp.pos⟩
      · intro b hb
        simp only [Finset.mem_filter] at hb
        have hbp : b = p * (b / p) := (Nat.mul_div_cancel' hb.2).symm
        have hchar : χ (b : ZMod M) = χ (p : ZMod M) * χ ((b / p : ℕ) : ZMod M) := by
          conv_lhs => rw [hbp]
          rw [Nat.cast_mul, map_mul]
        have harg : (b : ℚ) / ((p * M : ℕ) : ℚ) = ((b / p : ℕ) : ℚ) / (M : ℚ) := by
          have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
          have hMq : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
          conv_lhs => rw [hbp]
          push_cast
          field_simp [hpq, hMq]
        rw [hchar, harg]
        ring
    linear_combination -hdiff - hmult
  rw [hsplit, Nat.cast_mul, mul_pow]
  calc (p : ℂ) ^ (k - 1) * (M : ℂ) ^ (k - 1) *
        ((∑ b ∈ Finset.range (p * M),
            χ (b : ZMod M) *
              (((Polynomial.bernoulli k).eval ((b : ℚ) / ((p * M : ℕ) : ℚ)) : ℚ) : ℂ)) -
          χ (p : ZMod M) *
            ∑ c ∈ Finset.range M,
              χ (c : ZMod M) * (((Polynomial.bernoulli k).eval ((c : ℚ) / (M : ℚ)) : ℚ) : ℂ))
      = (M : ℂ) ^ (k - 1) *
          ((p : ℂ) ^ (k - 1) *
            ∑ b ∈ Finset.range (p * M),
              χ (b : ZMod M) *
                (((Polynomial.bernoulli k).eval ((b : ℚ) / ((p * M : ℕ) : ℚ)) : ℚ) : ℂ)) -
        χ (p : ZMod M) * (p : ℂ) ^ (k - 1) *
          ((M : ℂ) ^ (k - 1) *
            ∑ c ∈ Finset.range M,
              χ (c : ZMod M) * (((Polynomial.bernoulli k).eval ((c : ℚ) / (M : ℚ)) : ℚ) : ℂ)) := by
        ring
    _ = (1 - χ (p : ZMod M) * (p : ℂ) ^ (k - 1)) *
          ((M : ℂ) ^ (k - 1) *
            ∑ a ∈ Finset.range M,
              χ (a : ZMod M) * (((Polynomial.bernoulli k).eval ((a : ℚ) / (M : ℚ)) : ℚ) : ℂ)) := by
        rw [hraabe]; ring

/-- **Generalized Bernoulli Level-Change Formula**:
for any `M ∣ N` (`[NeZero M] [NeZero N]`), any non-principal `χ : DirichletCharacter ℂ M`, and
any `k ≥ 1`:
`genBernoulli (changeLevel hMN χ) k = genBernoulli χ k * ∏ p ∈ N.primeFactors, (1 - χ p * p^(k - 1))`. -/
theorem genBernoulli_changeLevel {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    {χ : DirichletCharacter ℂ M} (hχ : χ ≠ 1) {k : ℕ} (hk : 1 ≤ k) :
    genBernoulli (DirichletCharacter.changeLevel hMN χ) k =
      genBernoulli χ k * ∏ p ∈ N.primeFactors, (1 - χ (p : ZMod M) * (p : ℂ) ^ (k - 1)) := by
  obtain ⟨r, hr_eq⟩ := hMN
  have hr0 : r ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hr_eq; exact NeZero.ne N hr_eq
  revert N
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro N _ hr_eq
    have hMN : M ∣ N := ⟨r, hr_eq⟩
    by_cases hr1 : r = 1
    · subst hr1
      have hNM : N = M := by simpa using hr_eq
      subst hNM
      have hprod1 : ∏ p ∈ N.primeFactors, (1 - χ (p : ZMod N) * (p : ℂ) ^ (k - 1)) = 1 := by
        refine Finset.prod_eq_one fun p hp => ?_
        have hp_dvd : p ∣ N := Nat.dvd_of_mem_primeFactors hp
        have hnu : ¬ IsUnit (p : ZMod N) := by
          rw [ZMod.isUnit_iff_coprime]
          intro hcop
          have hd : p ∣ Nat.gcd p N := Nat.dvd_gcd dvd_rfl hp_dvd
          rw [hcop.gcd_eq_one] at hd
          exact (Nat.prime_of_mem_primeFactors hp).not_dvd_one hd
        rw [MulChar.map_nonunit χ hnu, zero_mul, sub_zero]
      rw [hprod1, mul_one, DirichletCharacter.changeLevel_self]
    · obtain ⟨p, hp, hpr⟩ := Nat.exists_prime_and_dvd hr1
      obtain ⟨r', rfl⟩ := hpr
      have hr'0 : r' ≠ 0 := right_ne_zero_of_mul hr0
      have hr'_lt : r' < p * r' := lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hr'0) hp.one_lt
      have : NeZero (M * r') := ⟨mul_ne_zero (NeZero.ne M) hr'0⟩
      have hN_eq : N = p * (M * r') := by rw [hr_eq]; ring
      have hM_dvd_Mr' : M ∣ M * r' := dvd_mul_right M r'
      have hMr'_dvd_N : M * r' ∣ N := ⟨p, by rw [hN_eq]; ring⟩
      have hcomp :
          DirichletCharacter.changeLevel hMN χ =
            DirichletCharacter.changeLevel hMr'_dvd_N
              (DirichletCharacter.changeLevel hM_dvd_Mr' χ) :=
        DirichletCharacter.changeLevel_trans χ hM_dvd_Mr' hMr'_dvd_N
      rw [hcomp]
      set χ' := DirichletCharacter.changeLevel hM_dvd_Mr' χ
      have hχ' : χ' ≠ 1 := fun h1 => hχ ((DirichletCharacter.changeLevel_eq_one_iff hM_dvd_Mr').mp h1)
      have hstep :
          genBernoulli (DirichletCharacter.changeLevel hMr'_dvd_N χ') k =
            (1 - χ' (p : ZMod (M * r')) * (p : ℂ) ^ (k - 1)) * genBernoulli χ' k := by
        have : NeZero (p * (M * r')) := ⟨mul_ne_zero hp.ne_zero (NeZero.ne (M * r'))⟩
        have hstep0 := genBernoulli_changeLevel_prime_mul (M := M * r') hp hχ' hk
        have hcast_eq :
            genBernoulli (DirichletCharacter.changeLevel hMr'_dvd_N χ') k =
              genBernoulli (DirichletCharacter.changeLevel (dvd_mul_left (M * r') p) χ') k := by
          unfold genBernoulli
          have hne1 : N ≠ 1 := by
            have := two_le_of_ne_one hχ; have := hp.two_le
            have : 0 < r' := Nat.pos_of_ne_zero hr'0
            nlinarith [hN_eq]
          have hne1' : p * (M * r') ≠ 1 := by omega
          rw [if_neg hne1, if_neg hne1']
          simp only [hN_eq]
          congr 1
          refine Finset.sum_congr rfl fun a _ => ?_
          congr 1
          by_cases hcop : Nat.Coprime a (p * (M * r'))
          · have hcopN : Nat.Coprime a N := by rwa [hN_eq]
            rw [changeLevel_apply_nat_of_coprime hMr'_dvd_N χ' hcopN,
              changeLevel_apply_nat_of_coprime (dvd_mul_left (M * r') p) χ' hcop]
          · have hnuN : ¬ IsUnit (a : ZMod N) := by
              rw [ZMod.isUnit_iff_coprime, hN_eq]; exact hcop
            have hnu' : ¬ IsUnit (a : ZMod (p * (M * r'))) := by
              rw [ZMod.isUnit_iff_coprime]; exact hcop
            rw [MulChar.map_nonunit _ hnuN, MulChar.map_nonunit _ hnu']
        rw [hcast_eq, hstep0]
      rw [hstep, ih r' hr'_lt hr'0 (N := M * r') rfl]
      -- Combine `(1 - χ'(p) p^{k-1})` with `∏_{q ∈ (M*r').primeFactors} (1 - χ(q) q^{k-1})`
      have hpf : N.primeFactors = insert p (M * r').primeFactors := by
        rw [hN_eq]
        ext q
        simp only [Nat.mem_primeFactors, Finset.mem_insert]
        constructor
        · rintro ⟨hq, hqdvd, _⟩
          rcases hq.dvd_mul.mp hqdvd with hqp | hqMr'
          · left; exact ((hp.dvd_iff_eq hq.ne_one).mp hqp).symm
          · right; exact ⟨hq, hqMr', NeZero.ne (M * r')⟩
        · rintro (hq_eq | ⟨hq, hqdvd, _⟩)
          · rw [hq_eq]; exact ⟨hp, dvd_mul_right p (M * r'), mul_ne_zero hp.ne_zero (NeZero.ne (M * r'))⟩
          · exact ⟨hq, dvd_mul_of_dvd_right hqdvd p, mul_ne_zero hp.ne_zero (NeZero.ne (M * r'))⟩
      rw [hpf]
      by_cases hp_mem : p ∈ (M * r').primeFactors
      · have hp_dvd : p ∣ M * r' := Nat.dvd_of_mem_primeFactors hp_mem
        have hnu : ¬ IsUnit (p : ZMod (M * r')) := by
          rw [ZMod.isUnit_iff_coprime]
          intro hcop
          have hd : p ∣ Nat.gcd p (M * r') := Nat.dvd_gcd dvd_rfl hp_dvd
          rw [hcop.gcd_eq_one] at hd
          exact hp.not_dvd_one hd
        rw [Finset.insert_eq_of_mem hp_mem, MulChar.map_nonunit χ' hnu, zero_mul, sub_zero, one_mul]
      · have hp_ndvd : ¬ p ∣ M * r' := fun hd =>
          hp_mem (Nat.mem_primeFactors.mpr ⟨hp, hd, NeZero.ne (M * r')⟩)
        have hcop : Nat.Coprime p (M * r') := hp.coprime_iff_not_dvd.mpr hp_ndvd
        have hχ'p : χ' (p : ZMod (M * r')) = χ (p : ZMod M) :=
          changeLevel_apply_nat_of_coprime hM_dvd_Mr' χ hcop
        rw [Finset.prod_insert hp_mem, hχ'p]
        ring

/-- Helper: `Complex.Gammaℝ 2 = (Real.pi : ℂ)⁻¹`. -/
lemma Gammaℝ_two_eq : Complex.Gammaℝ 2 = (Real.pi : ℂ)⁻¹ := by
  rw [Complex.Gammaℝ_def]
  have h1 : -(2 : ℂ) / 2 = -1 := by ring
  have h2 : (2 : ℂ) / 2 = 1 := by ring
  rw [h1, h2, Complex.Gamma_one, mul_one, Complex.cpow_neg_one]

/-- Exact value `LFunction χ 0 = -genBernoulli χ 1` for every primitive odd `χ`. -/
private lemma LFunction_zero_eq_neg_genBernoulli_one_of_primitive_odd {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hodd : χ.Odd) :
    DirichletCharacter.LFunction χ 0 = -genBernoulli χ 1 := by
  have hχ : χ ≠ 1 := ne_one_of_odd hodd
  have hq2 : 2 ≤ q := two_le_of_ne_one hχ
  have hq_ne1 : q ≠ 1 := by omega
  have hqC_ne : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hprim_inv : χ⁻¹.IsPrimitive := by
    show χ⁻¹.conductor = q
    rw [DirichletCharacter.conductor_inv, hprim]
  have hχ_inv : χ⁻¹ ≠ 1 := fun h1 => hχ (by simpa using congrArg Inv.inv h1)
  have hodd_inv : χ⁻¹.Odd := by
    show χ⁻¹ (-1 : ZMod q) = -1
    rw [MulChar.inv_apply_eq_inv', hodd]; norm_num
  -- Relate `L(0, χ)` to `completedLFunction χ 0`
  have hL0 : DirichletCharacter.LFunction χ 0 = DirichletCharacter.completedLFunction χ 0 := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ 0 (Or.inr hq_ne1),
      hodd.gammaFactor_def, zero_add, Complex.Gammaℝ_one, div_one]
  -- Apply functional equation at `s = 1`
  have hfe := hprim.completedLFunction_one_sub 1
  rw [sub_self] at hfe
  -- Relate `completedLFunction χ⁻¹ 1` to `LFunction χ⁻¹ 1`
  have hL1 : DirichletCharacter.completedLFunction χ⁻¹ 1 =
      (Real.pi : ℂ)⁻¹ * DirichletCharacter.LFunction χ⁻¹ 1 := by
    have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ 1 (Or.inl one_ne_zero)
    rw [hodd_inv.gammaFactor_def, (by norm_num : (1 : ℂ) + 1 = 2), Gammaℝ_two_eq] at h
    rw [h, mul_div_cancel₀ _ (inv_ne_zero hpi_ne)]
  -- Simplify `(q : ℂ)^(1 - 1/2) * rootNumber χ`
  have hroot : (q : ℂ) ^ ((1 : ℂ) - 1 / 2) * DirichletCharacter.rootNumber χ =
      gaussSum χ ZMod.stdAddChar / Complex.I := by
    unfold DirichletCharacter.rootNumber
    rw [if_neg hodd.not_even, pow_one]
    have hhalf : (1 : ℂ) - 1 / 2 = 1 / 2 := by ring
    rw [hhalf]
    have hqpow_ne : (q : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]
      exact fun h => hqC_ne h.1
    field_simp [hqpow_ne]
  -- Use `Stage6ClassNumberFormula.LFunction_one_eq_odd` for `χ⁻¹`
  have hL1_val := Stage6ClassNumberFormula.LFunction_one_eq_odd hprim_inv hχ_inv hodd_inv
  rw [inv_inv] at hL1_val
  rw [hL0, hfe, hroot, hL1, hL1_val, genBernoulli_one_eq hχ]
  have hprod : gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar = -(q : ℂ) := by
    have h := Stage6ClassNumberFormula.gaussSum_mul_gaussSum_inv hprim
    rw [hodd] at h
    simpa using h
  have hI_ne : Complex.I ≠ 0 := Complex.I_ne_zero
  calc gaussSum χ ZMod.stdAddChar / Complex.I *
        ((Real.pi : ℂ)⁻¹ *
          (Complex.I * (Real.pi : ℂ) * gaussSum χ⁻¹ ZMod.stdAddChar / (q : ℂ) ^ 2 *
            ∑ a ∈ Finset.Ico 1 q, (a : ℂ) * χ (a : ZMod q)))
      = (gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar / (q : ℂ) ^ 2) *
          (Complex.I / Complex.I) * ((Real.pi : ℂ) / (Real.pi : ℂ)) *
          ∑ a ∈ Finset.Ico 1 q, (a : ℂ) * χ (a : ZMod q) := by ring
    _ = (-(q : ℂ) / (q : ℂ) ^ 2) * 1 * 1 *
          ∑ a ∈ Finset.Ico 1 q, (a : ℂ) * χ (a : ZMod q) := by
        rw [hprod, div_self hI_ne, div_self hpi_ne]
    _ = -((q : ℂ)⁻¹ * ∑ a ∈ Finset.Ico 1 q, (a : ℂ) * χ (a : ZMod q)) := by
        field_simp [hqC_ne]

/-- **UNCONDITIONAL EXACT NEGATIVE-INTEGER SPECIAL VALUE THEOREM FOR ALL DIRICHLET `L`-FUNCTIONS**:
for EVERY `q ≥ 1` (`[NeZero q]`), EVERY non-principal `χ : DirichletCharacter ℂ q` (`χ ≠ 1`,
primitive or imprimitive), and EVERY `k ≥ 1`:
`DirichletCharacter.LFunction χ (1 - k) = -genBernoulli χ k / k`! -/
theorem LFunction_one_sub_nat_eq_genBernoulli {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {k : ℕ} (hk : 1 ≤ k) :
    DirichletCharacter.LFunction χ (1 - (k : ℂ)) = -(genBernoulli χ k) / (k : ℂ) := by
  have hq2 : 2 ≤ q := two_le_of_ne_one hχ
  have hq_ne1 : q ≠ 1 := by omega
  by_cases hk1 : k = 1
  · subst hk1
    simp only [Nat.cast_one, sub_self, div_one]
    rcases χ.even_or_odd with heven | hodd
    · -- Even non-principal character: both sides are `0`
      rw [genBernoulli_eq_zero_of_even_odd hq_ne1 heven odd_one, neg_zero]
      rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ 0 (Or.inr hq_ne1),
        heven.gammaFactor_def]
      have hG0 : Complex.Gammaℝ 0 = 0 := by
        rw [Complex.Gammaℝ_eq_zero_iff]; exact ⟨0, by simp⟩
      rw [hG0, div_zero]
    · -- Odd character (possibly imprimitive): reduce to `χ.primitiveCharacter`
      have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
      set χ₀ := χ.primitiveCharacter
      have hprim₀ : χ₀.IsPrimitive := χ.primitiveCharacter_isPrimitive
      have hχ₀ : χ₀ ≠ 1 := by
        intro h1
        apply hχ
        have hcond : χ.conductor = 1 := by
          have hp : χ₀.conductor = χ.conductor := hprim₀
          rw [h1, DirichletCharacter.conductor_one] at hp
          exact hp.symm
        exact DirichletCharacter.eq_one_iff_conductor_eq_one.mpr hcond
      have hodd₀ : χ₀.Odd := by
        show χ₀ (-1 : ZMod χ.conductor) = -1
        have hch : χ = DirichletCharacter.changeLevel χ.conductor_dvd_level χ₀ :=
          (DirichletCharacter.changeLevel_primitiveCharacter χ).symm
        have h1 : χ (-1 : ZMod q) = χ₀ (-1 : ZMod χ.conductor) := by
          conv_lhs => rw [hch]
          exact changeLevel_apply_neg_one χ.conductor_dvd_level χ₀
        rw [← h1]
        exact hodd
      have hch : χ = DirichletCharacter.changeLevel χ.conductor_dvd_level χ₀ :=
        (DirichletCharacter.changeLevel_primitiveCharacter χ).symm
      conv_lhs => rw [hch]
      conv_rhs => rw [hch]
      rw [DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ₀ (Or.inr zero_ne_one),
        genBernoulli_changeLevel χ.conductor_dvd_level hχ₀ le_rfl,
        LFunction_zero_eq_neg_genBernoulli_one_of_primitive_odd hprim₀ hodd₀]
      simp only [neg_zero, Complex.cpow_zero, mul_one, Nat.sub_self, pow_zero, neg_mul]
  · -- `k ≥ 2`: direct evaluation via `HurwitzZeta.hurwitzZeta_neg_nat`!
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, by omega⟩
    have hm : m ≠ 0 := by omega
    have h1sub : (1 : ℂ) - ((m + 1 : ℕ) : ℂ) = -(m : ℂ) := by push_cast; ring
    rw [h1sub, DirichletCharacter.LFunction, ZMod.LFunction, genBernoulli_eq_sum_zmod hχ (m + 1)]
    have hpow : (q : ℂ) ^ (-(-(m : ℂ))) = (q : ℂ) ^ (((m + 1 : ℕ) : ℤ) - 1) := by
      rw [neg_neg, show (((m + 1 : ℕ) : ℤ) - 1) = (m : ℤ) by omega,
        Complex.cpow_natCast, zpow_natCast]
    rw [hpow]
    have hsum :
        ∑ j : ZMod q, χ j * HurwitzZeta.hurwitzZeta (ZMod.toAddCircle j) (-(m : ℂ)) =
          -(1 / ((m + 1 : ℕ) : ℂ)) *
            ∑ j : ZMod q,
              χ j * ((Polynomial.bernoulli (m + 1)).map (algebraMap ℚ ℂ)).eval ((j.val : ℂ) / (q : ℂ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hx : ((j.val : ℝ) / (q : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
        refine ⟨by positivity, ?_⟩
        exact (div_le_one (Nat.cast_pos.mpr (NeZero.pos q))).mpr (Nat.cast_le.mpr (ZMod.val_lt j).le)
      rw [ZMod.toAddCircle_apply, HurwitzZeta.hurwitzZeta_neg_nat hm hx]
      push_cast
      ring
    rw [hsum]
    ring

/-! ### Complex-to-$p$-adic Interpolation Bridge (`kubotaLeopoldtZeta` ↔ `riemannZeta`) -/

/-- Exact negative-integer Riemann zeta formula in `-B_{k+1} / (k + 1)` form for all `k ≥ 1`. -/
theorem riemannZeta_one_sub_eq_neg_bernoulli_div {k : ℕ} (hk : 1 ≤ k) :
    riemannZeta (1 - ((k + 1 : ℕ) : ℂ)) =
      -(bernoulli (k + 1) : ℂ) / ((k + 1 : ℕ) : ℂ) := by
  have h1sub : (1 : ℂ) - ((k + 1 : ℕ) : ℂ) = -(k : ℂ) := by push_cast; ring
  rw [h1sub, riemannZeta_neg_nat_eq_bernoulli k]
  rcases Nat.even_or_odd k with hev | hodd
  · have hodd1 : _root_.Odd (k + 1) := hev.add_one
    have hgt1 : 1 < k + 1 := by omega
    rw [bernoulli_eq_zero_of_odd hodd1 hgt1]
    simp
  · rw [hodd.neg_one_pow]
    push_cast
    ring

/-- The algebraic rational Euler-removed zeta value `(1 - p^k) * (-B_{k+1} / (k + 1)) ∈ ℚ`. -/
def eulerRemovedZetaRat (p k : ℕ) : ℚ :=
  (1 - (p : ℚ) ^ k) * (-bernoulli (k + 1) / ((k + 1 : ℕ) : ℚ))

/-- **UNCONDITIONAL COMPLEX-TO-$p$-ADIC INTERPOLATION BRIDGE**:
for EVERY odd prime `p`, EVERY `c ≥ 2` with `¬ p ∣ c`, EVERY branch `i : ℕ`, and EVERY `k ≥ 1`
with `k ≡ i [MOD p - 1]`, the Kubota–Leopoldt $p$-adic zeta value
`Stage7PadicLFunction.kubotaLeopoldtZeta p hp2 c hc i k` and the complex Euler-removed Riemann
zeta value `(1 - p^k) * riemannZeta (1 - (k + 1))` are the exact $p$-adic and complex embeddings
of the **same** algebraic rational `r = (1 - p^k) * (-B_{k+1} / (k + 1)) ∈ ℚ`! -/
theorem kubotaLeopoldtZeta_eq_riemannZeta_one_sub (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {c : ℕ} (hc2 : 2 ≤ c) (hc : ¬ p ∣ c) (i : ℕ) {k : ℕ} (hk : 1 ≤ k)
    (hki : k ≡ i [MOD (p - 1)]) :
    ∃ r : ℚ,
      Stage7PadicLFunction.kubotaLeopoldtZeta p hp2 c hc i (k : ℤ_[p]) = (r : ℚ_[p]) ∧
      (1 - (p : ℂ) ^ k) * riemannZeta (1 - ((k + 1 : ℕ) : ℂ)) = (r : ℂ) ∧
      r = (1 - (p : ℚ) ^ k) * (-bernoulli (k + 1) / ((k + 1 : ℕ) : ℚ)) := by
  refine ⟨eulerRemovedZetaRat p k, ?_, ?_, rfl⟩
  · rw [Stage7PadicLFunction.kubotaLeopoldtZeta_eval_nat p hp2 hc2 hc i k hki]
    unfold eulerRemovedZetaRat
    push_cast
    ring
  · rw [riemannZeta_one_sub_eq_neg_bernoulli_div hk]
    unfold eulerRemovedZetaRat
    push_cast
    ring

/-! ## Section 2: General Positive-Integer `L(k, χ)` Formula & Explicit Special Values -/

/-- Exact ratio `Gammaℝ (1 - 2m) / Gammaℝ (2m)` for every `m ≥ 1` (by elementary induction via
`Complex.Gammaℝ_add_two`). -/
private lemma Gammaℝ_ratio_even {m : ℕ} (hm : 1 ≤ m) :
    Complex.Gammaℝ (1 - 2 * (m : ℂ)) / Complex.Gammaℝ (2 * (m : ℂ)) =
      (-1 : ℂ) ^ m * (2 : ℂ) ^ (2 * m - 1) * (Real.pi : ℂ) ^ (2 * m) /
        (((2 * m - 1)! : ℕ) : ℂ) := by
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  induction m, hm using Nat.le_induction with
  | base =>
    have hG1 : Complex.Gammaℝ (-1) = -2 * (Real.pi : ℂ) := by
      have h := Complex.Gammaℝ_add_two (s := (-1 : ℂ)) (by norm_num)
      rw [show (-1 : ℂ) + 2 = 1 by norm_num, Complex.Gammaℝ_one] at h
      have h1 : Complex.Gammaℝ (-1) * (-1) = 2 * (Real.pi : ℂ) := by
        have h' := congrArg (· * (Real.pi : ℂ) * 2) h
        field_simp [hpi_ne] at h'
        linear_combination -h'
      linear_combination -h1
    have hG2 : Complex.Gammaℝ 2 = (Real.pi : ℂ)⁻¹ := Gammaℝ_two_eq
    norm_num
    rw [hG1, hG2]
    field_simp [hpi_ne]
  | succ m hm ih =>
    have hm_pos : 0 < m := hm
    have h2m_ne : (2 * (m : ℂ)) ≠ 0 := by
      exact mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr hm_pos.ne')
    have hnum_step : Complex.Gammaℝ (1 - 2 * ((m + 1 : ℕ) : ℂ)) =
        (-2 * (Real.pi : ℂ) / (2 * (m : ℂ) + 1)) * Complex.Gammaℝ (1 - 2 * (m : ℂ)) := by
      have hne : (1 - 2 * ((m + 1 : ℕ) : ℂ)) ≠ 0 := by
        intro h0
        have hre := congrArg Complex.re h0
        simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.re_ofNat,
          Complex.natCast_re, Complex.im_ofNat, Complex.natCast_im, mul_zero, sub_zero,
          Complex.zero_re] at hre
        have : (2 : ℝ) * (m + 1 : ℕ) = 1 := by linarith
        have : 2 * (m + 1) = 1 := by exact_mod_cast this
        omega
      have h := Complex.Gammaℝ_add_two hne
      have hadd : (1 - 2 * ((m + 1 : ℕ) : ℂ)) + 2 = 1 - 2 * (m : ℂ) := by push_cast; ring
      rw [hadd] at h
      have hden : (2 * (m : ℂ) + 1) ≠ 0 := by
        intro h0
        have hre := congrArg Complex.re h0
        simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.natCast_re,
          Complex.im_ofNat, Complex.natCast_im, mul_zero, sub_zero, Complex.one_re,
          Complex.zero_re] at hre
        have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        linarith
      have hneg : 1 - 2 * ((m + 1 : ℕ) : ℂ) = -(2 * (m : ℂ) + 1) := by push_cast; ring
      rw [hneg] at h ⊢
      field_simp [hpi_ne, hden] at h ⊢
      linear_combination h
    have hden_step : Complex.Gammaℝ (2 * ((m + 1 : ℕ) : ℂ)) =
        Complex.Gammaℝ (2 * (m : ℂ)) * (m : ℂ) / (Real.pi : ℂ) := by
      have hadd : 2 * ((m + 1 : ℕ) : ℂ) = 2 * (m : ℂ) + 2 := by push_cast; ring
      rw [hadd, Complex.Gammaℝ_add_two h2m_ne]
      ring
    rw [hnum_step, hden_step]
    have hrearr :
        (-2 * (Real.pi : ℂ) / (2 * (m : ℂ) + 1)) * Complex.Gammaℝ (1 - 2 * (m : ℂ)) /
          (Complex.Gammaℝ (2 * (m : ℂ)) * (m : ℂ) / (Real.pi : ℂ)) =
        (-2 * (Real.pi : ℂ) ^ 2 / ((2 * (m : ℂ) + 1) * (m : ℂ))) *
          (Complex.Gammaℝ (1 - 2 * (m : ℂ)) / Complex.Gammaℝ (2 * (m : ℂ))) := by
      have hGne : Complex.Gammaℝ (2 * (m : ℂ)) ≠ 0 :=
        Complex.Gammaℝ_ne_zero_of_re_pos (by
          simp only [Complex.mul_re, Complex.re_ofNat, Complex.natCast_re, Complex.im_ofNat,
            Complex.natCast_im, mul_zero, sub_zero]
          positivity)
      have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm_pos.ne'
      have h2m1 : (2 * (m : ℂ) + 1) ≠ 0 := by
        intro h0
        have hre := congrArg Complex.re h0
        simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.natCast_re,
          Complex.im_ofNat, Complex.natCast_im, mul_zero, sub_zero, Complex.one_re,
          Complex.zero_re] at hre
        have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        linarith
      field_simp [hGne, hmC, h2m1, hpi_ne]
    rw [hrearr, ih]
    have hfac : ((2 * (m + 1) - 1)! : ℂ) =
        ((2 * (m : ℂ) + 1) * (2 * (m : ℂ))) * (((2 * m - 1)! : ℕ) : ℂ) := by
      have h1 : 2 * (m + 1) - 1 = (2 * m) + 1 := by omega
      have h2 : 2 * m = (2 * m - 1) + 1 := by omega
      rw [h1, Nat.factorial_succ]
      conv_lhs => rw [h2, Nat.factorial_succ]
      push_cast
      have h2' : ((2 * m - 1 : ℕ) : ℂ) + 1 = 2 * (m : ℂ) := by
        have : (2 * m - 1) + 1 = 2 * m := by omega
        exact_mod_cast this
      rw [h2']
      ring
    have hpow2 : (2 : ℂ) ^ (2 * (m + 1) - 1) = (2 : ℂ) ^ (2 * m - 1) * 4 := by
      have h1 : 2 * (m + 1) - 1 = (2 * m - 1) + 2 := by omega
      rw [h1, pow_add]; norm_num
    have hpowpi : (Real.pi : ℂ) ^ (2 * (m + 1)) = (Real.pi : ℂ) ^ (2 * m) * (Real.pi : ℂ) ^ 2 := by
      rw [show 2 * (m + 1) = 2 * m + 2 by omega, pow_add]
    have hfac_ne : (((2 * m - 1)! : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm_pos.ne'
    have h2m1 : (2 * (m : ℂ) + 1) ≠ 0 := by
      intro h0
      have hre := congrArg Complex.re h0
      simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.natCast_re,
        Complex.im_ofNat, Complex.natCast_im, mul_zero, sub_zero, Complex.one_re,
        Complex.zero_re] at hre
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    rw [hfac, hpow2, hpowpi, pow_succ]
    field_simp [hfac_ne, hmC, h2m1]
    ring

/-- Exact ratio `Gammaℝ (1 - 2m) / Gammaℝ (2m + 2)` for every `m : ℕ` (by elementary induction via
`Complex.Gammaℝ_add_two`). -/
private lemma Gammaℝ_ratio_odd (m : ℕ) :
    Complex.Gammaℝ (1 - 2 * (m : ℂ)) / Complex.Gammaℝ (2 * (m : ℂ) + 2) =
      (-1 : ℂ) ^ m * (2 : ℂ) ^ (2 * m) * (Real.pi : ℂ) ^ (2 * m + 1) /
        (((2 * m)! : ℕ) : ℂ) := by
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  induction m with
  | zero =>
    simp only [Nat.cast_zero, mul_zero, sub_zero, zero_add, pow_zero, one_mul, pow_one,
      Nat.factorial_zero, Nat.cast_one, div_one, Complex.Gammaℝ_one, Gammaℝ_two_eq, one_div, inv_inv]
  | succ m ih =>
    have h2m1 : (2 * (m : ℂ) + 1) ≠ 0 := by
      intro h0
      have hre := congrArg Complex.re h0
      simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.natCast_re,
        Complex.im_ofNat, Complex.natCast_im, mul_zero, sub_zero, Complex.one_re,
        Complex.zero_re] at hre
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hm1 : ((m : ℂ) + 1) ≠ 0 := by
      intro h0
      have hre := congrArg Complex.re h0
      simp only [Complex.add_re, Complex.natCast_re, Complex.one_re, Complex.zero_re] at hre
      have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hnum_step : Complex.Gammaℝ (1 - 2 * ((m + 1 : ℕ) : ℂ)) =
        (-2 * (Real.pi : ℂ) / (2 * (m : ℂ) + 1)) * Complex.Gammaℝ (1 - 2 * (m : ℂ)) := by
      have hneg : 1 - 2 * ((m + 1 : ℕ) : ℂ) = -(2 * (m : ℂ) + 1) := by push_cast; ring
      have hne : (1 - 2 * ((m + 1 : ℕ) : ℂ)) ≠ 0 := by rw [hneg]; exact neg_ne_zero.mpr h2m1
      have h := Complex.Gammaℝ_add_two hne
      have hadd : (1 - 2 * ((m + 1 : ℕ) : ℂ)) + 2 = 1 - 2 * (m : ℂ) := by push_cast; ring
      rw [hadd] at h
      rw [hneg] at h ⊢
      field_simp [hpi_ne, h2m1] at h ⊢
      linear_combination h
    have hden_step : Complex.Gammaℝ (2 * ((m + 1 : ℕ) : ℂ) + 2) =
        Complex.Gammaℝ (2 * (m : ℂ) + 2) * ((m : ℂ) + 1) / (Real.pi : ℂ) := by
      have hadd : 2 * ((m + 1 : ℕ) : ℂ) + 2 = (2 * (m : ℂ) + 2) + 2 := by push_cast; ring
      have hne : (2 * (m : ℂ) + 2) ≠ 0 := by
        rw [show 2 * (m : ℂ) + 2 = 2 * ((m : ℂ) + 1) by ring]
        exact mul_ne_zero two_ne_zero hm1
      rw [hadd, Complex.Gammaℝ_add_two hne]
      ring
    rw [hnum_step, hden_step]
    have hGne : Complex.Gammaℝ (2 * (m : ℂ) + 2) ≠ 0 :=
      Complex.Gammaℝ_ne_zero_of_re_pos (by
        simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.natCast_re,
          Complex.im_ofNat, Complex.natCast_im, mul_zero, sub_zero]
        have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        linarith)
    have hrearr :
        (-2 * (Real.pi : ℂ) / (2 * (m : ℂ) + 1)) * Complex.Gammaℝ (1 - 2 * (m : ℂ)) /
          (Complex.Gammaℝ (2 * (m : ℂ) + 2) * ((m : ℂ) + 1) / (Real.pi : ℂ)) =
        (-2 * (Real.pi : ℂ) ^ 2 / ((2 * (m : ℂ) + 1) * ((m : ℂ) + 1))) *
          (Complex.Gammaℝ (1 - 2 * (m : ℂ)) / Complex.Gammaℝ (2 * (m : ℂ) + 2)) := by
      field_simp [hGne, hm1, h2m1, hpi_ne]
    rw [hrearr, ih]
    have hfac : ((2 * (m + 1))! : ℂ) =
        ((2 * (m : ℂ) + 2) * (2 * (m : ℂ) + 1)) * (((2 * m)! : ℕ) : ℂ) := by
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
      push_cast; ring
    have hpow2 : (2 : ℂ) ^ (2 * (m + 1)) = (2 : ℂ) ^ (2 * m) * 4 := by
      rw [show 2 * (m + 1) = 2 * m + 2 by omega, pow_add]; norm_num
    have hpowpi : (Real.pi : ℂ) ^ (2 * (m + 1) + 1) =
        (Real.pi : ℂ) ^ (2 * m + 1) * (Real.pi : ℂ) ^ 2 := by
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by omega, pow_add]
    have hfac_ne : (((2 * m)! : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [hfac, hpow2, hpowpi, pow_succ]
    field_simp [hfac_ne, hm1, h2m1]
    ring

/-- **GENERAL EULER–DIRICHLET SPECIAL VALUE FORMULA AT POSITIVE CRITICAL INTEGERS (`0` ASSUMPTIONS!)**:
for EVERY primitive non-principal character `χ : DirichletCharacter ℂ q` (`χ.IsPrimitive`, `χ ≠ 1`)
and EVERY positive integer `k ≥ 1` matching the parity of `χ` (`χ (-1) = (-1)^k`):
`DirichletCharacter.LFunction χ k = -(χ (-1) * gaussSum χ stdAddChar / (2 * k!)) * (2 * π * I / q)^k * genBernoulli χ⁻¹ k`! -/
theorem LFunction_pos_nat_eq_genBernoulli {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {k : ℕ} (hk : 1 ≤ k) (hpar : χ (-1 : ZMod q) = (-1 : ℂ) ^ k) :
    DirichletCharacter.LFunction χ (k : ℂ) =
      -(χ (-1 : ZMod q) * gaussSum χ ZMod.stdAddChar / (2 * ((k ! : ℕ) : ℂ))) *
        (2 * (Real.pi : ℂ) * Complex.I / (q : ℂ)) ^ k *
        genBernoulli χ⁻¹ k := by
  have hq2 : 2 ≤ q := two_le_of_ne_one hχ
  have hq_ne1 : q ≠ 1 := by omega
  have hqC_ne : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hkC_ne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hprim_inv : χ⁻¹.IsPrimitive := by
    show χ⁻¹.conductor = q
    rw [DirichletCharacter.conductor_inv, hprim]
  have hχ_inv : χ⁻¹ ≠ 1 := fun h1 => hχ (by simpa using congrArg Inv.inv h1)
  have hneg1_inv : χ⁻¹ (-1 : ZMod q) = χ (-1 : ZMod q) := by
    rw [MulChar.inv_apply_eq_inv']
    have hsq : χ (-1 : ZMod q) * χ (-1 : ZMod q) = 1 := by
      rw [← map_mul, neg_mul_neg, one_mul, map_one]
    exact (eq_inv_of_mul_eq_one_left hsq).symm
  -- Apply functional equation to `χ⁻¹` at `s = k`
  have hfe := hprim_inv.completedLFunction_one_sub (k : ℂ)
  rw [inv_inv] at hfe
  -- Relate `completedLFunction` and `LFunction` at both `k` and `1 - k`
  have hLk := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ (k : ℂ) (Or.inl hkC_ne)
  have hL1k := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - (k : ℂ)) (Or.inr hq_ne1)
  have hL1k_val := LFunction_one_sub_nat_eq_genBernoulli hχ_inv hk
  have hg_inv_ne : gaussSum χ⁻¹ ZMod.stdAddChar ≠ 0 :=
    Stage6ClassNumberFormula.gaussSum_ne_zero_of_isPrimitive hprim_inv
  have hqpow_ne : (q : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hqC_ne h.1
  have hq_cpow : (q : ℂ) ^ ((k : ℂ) - 1 / 2) / (q : ℂ) ^ (1 / 2 : ℂ) = (q : ℂ) ^ (k - 1) := by
    rw [← Complex.cpow_sub _ _ hqC_ne,
      show ((k : ℂ) - 1 / 2) - 1 / 2 = ((k - 1 : ℕ) : ℂ) by
        rw [Nat.cast_sub hk, Nat.cast_one]; ring,
      Complex.cpow_natCast]
  have hfac_eq : ((k ! : ℕ) : ℂ) = (k : ℂ) * (((k - 1)! : ℕ) : ℂ) := by
    have hk_eq : k = (k - 1) + 1 := by omega
    conv_lhs => rw [hk_eq, Nat.factorial_succ]
    push_cast
    have : ((k - 1 : ℕ) : ℂ) + 1 = (k : ℂ) := by exact_mod_cast hk_eq.symm
    rw [this]
  have hfac_ne : (((k - 1)! : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  -- Split into even and odd parity cases
  rcases χ.even_or_odd with heven | hodd
  · -- Even character (`χ(-1) = 1`), hence `k = 2 * m` with `m ≥ 1`
    have heven_inv : χ⁻¹.Even := by show χ⁻¹ (-1 : ZMod q) = 1; rw [hneg1_inv]; exact heven
    have hk_even : Even k := by
      rcases Nat.even_or_odd k with h | h
      · exact h
      · exfalso
        have h1 : (1 : ℂ) = (-1 : ℂ) ^ k := by rw [← hpar]; exact heven.symm
        rw [h.neg_one_pow] at h1; norm_num at h1
    obtain ⟨m, rfl⟩ := hk_even
    have hm : 1 ≤ m := by omega
    have h2m : m + m = 2 * m := by omega
    have hGk_ne : DirichletCharacter.gammaFactor χ ((m + m : ℕ) : ℂ) ≠ 0 := by
      rw [heven.gammaFactor_def]
      exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; positivity)
    have hG1k_ne : DirichletCharacter.gammaFactor χ⁻¹ (1 - ((m + m : ℕ) : ℂ)) ≠ 0 := by
      rw [heven_inv.gammaFactor_def, Ne, Complex.Gammaℝ_eq_zero_iff]
      rintro ⟨n, hn⟩
      have hre := congrArg Complex.re hn
      simp only [Complex.sub_re, Complex.one_re, Complex.natCast_re, Complex.neg_re,
        Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.natCast_im, mul_zero,
        sub_zero] at hre
      have : (2 * n : ℤ) + 1 = (m + m : ℤ) := by exact_mod_cast (by linarith : (2 : ℝ) * n + 1 = (m + m : ℕ))
      omega
    have hcomp_k : DirichletCharacter.completedLFunction χ ((m + m : ℕ) : ℂ) =
        DirichletCharacter.gammaFactor χ ((m + m : ℕ) : ℂ) *
          DirichletCharacter.LFunction χ ((m + m : ℕ) : ℂ) := by
      rw [hLk, mul_div_cancel₀ _ hGk_ne]
    have hcomp_1k : DirichletCharacter.completedLFunction χ⁻¹ (1 - ((m + m : ℕ) : ℂ)) =
        DirichletCharacter.gammaFactor χ⁻¹ (1 - ((m + m : ℕ) : ℂ)) *
          (-(genBernoulli χ⁻¹ (m + m)) / ((m + m : ℕ) : ℂ)) := by
      rw [← hL1k_val, hL1k, mul_div_cancel₀ _ hG1k_ne]
    have hroot_inv :
        (q : ℂ) ^ (((m + m : ℕ) : ℂ) - 1 / 2) * DirichletCharacter.rootNumber χ⁻¹ =
          (q : ℂ) ^ (m + m - 1) * gaussSum χ⁻¹ ZMod.stdAddChar := by
      unfold DirichletCharacter.rootNumber
      rw [if_pos heven_inv, pow_zero, div_one, ← mul_div_assoc, mul_div_right_comm, hq_cpow]
    rw [hcomp_1k, hcomp_k, hroot_inv] at hfe
    have hcoef_ne : (q : ℂ) ^ (m + m - 1) * gaussSum χ⁻¹ ZMod.stdAddChar ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hqC_ne) hg_inv_ne
    have hsolve :
        DirichletCharacter.LFunction χ ((m + m : ℕ) : ℂ) =
          ((q : ℂ) ^ (m + m - 1) * gaussSum χ⁻¹ ZMod.stdAddChar)⁻¹ *
            (Complex.Gammaℝ (1 - 2 * (m : ℂ)) / Complex.Gammaℝ (2 * (m : ℂ))) *
            (-(genBernoulli χ⁻¹ (m + m)) / ((m + m : ℕ) : ℂ)) := by
      have hcast2m : ((m + m : ℕ) : ℂ) = 2 * (m : ℂ) := by push_cast; ring
      rw [heven.gammaFactor_def, heven_inv.gammaFactor_def] at hfe
      have hG2m_ne : Complex.Gammaℝ (2 * (m : ℂ)) ≠ 0 := by
        rw [← hcast2m]; simpa [heven.gammaFactor_def] using hGk_ne
      set G1 := Complex.Gammaℝ (1 - 2 * (m : ℂ))
      set G2 := Complex.Gammaℝ (2 * (m : ℂ))
      set C0 := (q : ℂ) ^ (m + m - 1) * gaussSum χ⁻¹ ZMod.stdAddChar
      set B0 := -(genBernoulli χ⁻¹ (m + m)) / ((m + m : ℕ) : ℂ)
      have hfe' : G1 * B0 = C0 * (G2 * DirichletCharacter.LFunction χ ((m + m : ℕ) : ℂ)) := by
        simpa only [G1, G2, C0, B0, hcast2m] using hfe
      field_simp [hcoef_ne, hG2m_ne]
      linear_combination -hfe'
    rw [hsolve, Gammaℝ_ratio_even hm, mul_inv, Stage6ClassNumberFormula.inv_gaussSum_inv_eq hprim,
      heven, one_mul, hfac_eq, h2m]
    have hI2m : Complex.I ^ (2 * m) = (-1 : ℂ) ^ m := by
      rw [pow_mul, Complex.I_sq]
    have hpow_rhs :
        (2 * (Real.pi : ℂ) * Complex.I / (q : ℂ)) ^ (2 * m) =
          (2 : ℂ) ^ (2 * m) * (Real.pi : ℂ) ^ (2 * m) * (-1 : ℂ) ^ m / (q : ℂ) ^ (2 * m) := by
      rw [div_pow, mul_pow, mul_pow, hI2m]
    have hpow2 : (2 : ℂ) ^ (2 * m) = 2 * (2 : ℂ) ^ (2 * m - 1) := by
      have h1 : 2 * m = (2 * m - 1) + 1 := by omega
      conv_lhs => rw [h1, pow_succ']
    have hpowq : (q : ℂ) ^ (2 * m) = (q : ℂ) * (q : ℂ) ^ (2 * m - 1) := by
      have h1 : 2 * m = (2 * m - 1) + 1 := by omega
      conv_lhs => rw [h1, pow_succ']
    have h2m_ne : ((2 * m : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hqpow2m_ne : (q : ℂ) ^ (2 * m - 1) ≠ 0 := pow_ne_zero _ hqC_ne
    have hfac2m_ne : (((2 * m - 1)! : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [hpow_rhs, hpow2, hpowq]
    field_simp [hqC_ne, hqpow2m_ne, h2m_ne, hfac2m_ne]
  · -- Odd character (`χ(-1) = -1`), hence `k = 2 * m + 1`
    have hodd_inv : χ⁻¹.Odd := by show χ⁻¹ (-1 : ZMod q) = -1; rw [hneg1_inv]; exact hodd
    have hk_odd : Odd k := by
      rcases Nat.even_or_odd k with h | h
      · exfalso
        have h1 : (-1 : ℂ) = (-1 : ℂ) ^ k := by rw [← hpar]; exact hodd.symm
        rw [h.neg_one_pow] at h1; norm_num at h1
      · exact h
    obtain ⟨m, rfl⟩ := hk_odd
    have hGk_ne : DirichletCharacter.gammaFactor χ ((2 * m + 1 : ℕ) : ℂ) ≠ 0 := by
      rw [hodd.gammaFactor_def]
      exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; positivity)
    have hG1k_ne : DirichletCharacter.gammaFactor χ⁻¹ (1 - ((2 * m + 1 : ℕ) : ℂ)) ≠ 0 := by
      rw [hodd_inv.gammaFactor_def, Ne, Complex.Gammaℝ_eq_zero_iff]
      rintro ⟨n, hn⟩
      have hre := congrArg Complex.re hn
      simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.natCast_re,
        Complex.neg_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.natCast_im,
        mul_zero, sub_zero] at hre
      push_cast at hre
      have : (2 * n : ℤ) + 1 = 2 * (m : ℤ) := by
        exact_mod_cast (by linarith : (2 : ℝ) * (n : ℝ) + 1 = 2 * (m : ℝ))
      omega
    have hcomp_k : DirichletCharacter.completedLFunction χ ((2 * m + 1 : ℕ) : ℂ) =
        DirichletCharacter.gammaFactor χ ((2 * m + 1 : ℕ) : ℂ) *
          DirichletCharacter.LFunction χ ((2 * m + 1 : ℕ) : ℂ) := by
      rw [hLk, mul_div_cancel₀ _ hGk_ne]
    have hcomp_1k : DirichletCharacter.completedLFunction χ⁻¹ (1 - ((2 * m + 1 : ℕ) : ℂ)) =
        DirichletCharacter.gammaFactor χ⁻¹ (1 - ((2 * m + 1 : ℕ) : ℂ)) *
          (-(genBernoulli χ⁻¹ (2 * m + 1)) / ((2 * m + 1 : ℕ) : ℂ)) := by
      rw [← hL1k_val, hL1k, mul_div_cancel₀ _ hG1k_ne]
    have hroot_inv :
        (q : ℂ) ^ (((2 * m + 1 : ℕ) : ℂ) - 1 / 2) * DirichletCharacter.rootNumber χ⁻¹ =
          (q : ℂ) ^ (2 * m) * gaussSum χ⁻¹ ZMod.stdAddChar / Complex.I := by
      unfold DirichletCharacter.rootNumber
      rw [if_neg hodd_inv.not_even, pow_one]
      have hI_ne : Complex.I ≠ 0 := Complex.I_ne_zero
      have hsub : (2 * m + 1) - 1 = 2 * m := by omega
      rw [show (q : ℂ) ^ (2 * m) = (q : ℂ) ^ ((2 * m + 1) - 1) by rw [hsub], ← hq_cpow]
      field_simp [hqpow_ne, hI_ne]
    rw [hcomp_1k, hcomp_k, hroot_inv] at hfe
    have hI_ne : Complex.I ≠ 0 := Complex.I_ne_zero
    have hcoef_ne : (q : ℂ) ^ (2 * m) * gaussSum χ⁻¹ ZMod.stdAddChar / Complex.I ≠ 0 :=
      div_ne_zero (mul_ne_zero (pow_ne_zero _ hqC_ne) hg_inv_ne) hI_ne
    have hsolve :
        DirichletCharacter.LFunction χ ((2 * m + 1 : ℕ) : ℂ) =
          ((q : ℂ) ^ (2 * m) * gaussSum χ⁻¹ ZMod.stdAddChar / Complex.I)⁻¹ *
            (Complex.Gammaℝ (1 - 2 * (m : ℂ)) / Complex.Gammaℝ (2 * (m : ℂ) + 2)) *
            (-(genBernoulli χ⁻¹ (2 * m + 1)) / ((2 * m + 1 : ℕ) : ℂ)) := by
      have h1 : (1 - ((2 * m + 1 : ℕ) : ℂ)) + 1 = 1 - 2 * (m : ℂ) := by push_cast; ring
      have h2 : ((2 * m + 1 : ℕ) : ℂ) + 1 = 2 * (m : ℂ) + 2 := by push_cast; ring
      rw [hodd.gammaFactor_def, hodd_inv.gammaFactor_def, h1, h2] at hfe
      have hG2m2_ne : Complex.Gammaℝ (2 * (m : ℂ) + 2) ≠ 0 := by
        rw [← h2]; simpa [hodd.gammaFactor_def] using hGk_ne
      set G1 := Complex.Gammaℝ (1 - 2 * (m : ℂ))
      set G2 := Complex.Gammaℝ (2 * (m : ℂ) + 2)
      set C0 := (q : ℂ) ^ (2 * m) * gaussSum χ⁻¹ ZMod.stdAddChar / Complex.I
      set B0 := -(genBernoulli χ⁻¹ (2 * m + 1)) / ((2 * m + 1 : ℕ) : ℂ)
      field_simp [hcoef_ne, hG2m2_ne]
      linear_combination -hfe
    rw [hsolve, Gammaℝ_ratio_odd m, inv_div, div_eq_mul_inv, mul_inv,
      Stage6ClassNumberFormula.inv_gaussSum_inv_eq hprim, hodd, hfac_eq]
    have hI2m1 : Complex.I ^ (2 * m + 1) = (-1 : ℂ) ^ m * Complex.I := by
      rw [pow_succ, pow_mul, Complex.I_sq]
    have hpow_rhs :
        (2 * (Real.pi : ℂ) * Complex.I / (q : ℂ)) ^ (2 * m + 1) =
          2 * (2 : ℂ) ^ (2 * m) * (Real.pi : ℂ) ^ (2 * m + 1) *
            ((-1 : ℂ) ^ m * Complex.I) / ((q : ℂ) * (q : ℂ) ^ (2 * m)) := by
      rw [div_pow, mul_pow, mul_pow, hI2m1, pow_succ' (2 : ℂ), pow_succ' (q : ℂ)]
    have hsub : (2 * m + 1) - 1 = 2 * m := by omega
    have h2m1_ne : ((2 * m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hqpow2m_ne : (q : ℂ) ^ (2 * m) ≠ 0 := pow_ne_zero _ hqC_ne
    have hfac2m_ne : (((2 * m)! : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [hsub, hpow_rhs]
    field_simp [hqC_ne, hqpow2m_ne, h2m1_ne, hfac2m_ne]

/-! ### Explicit Primitive Characters `χ₋₄` (mod 4) & `χ₋₃` (mod 3) and Special Values -/

/-- Integer value function for `χ₋₄` modulo `4`. -/
private def chi4Val (a : ZMod 4) : ℤ :=
  match a.val with
  | 1 => 1
  | 3 => -1
  | _ => 0

/-- The unique primitive quadratic Dirichlet character `χ₋₄` modulo `4` (`χ₋₄(1) = 1`, `χ₋₄(3) = -1`). -/
def chi4 : DirichletCharacter ℂ 4 where
  toFun a := (chi4Val a : ℂ)
  map_one' := by
    have h : chi4Val (1 : ZMod 4) = 1 := by decide
    exact_mod_cast h
  map_mul' a b := by
    have h : chi4Val (a * b) = chi4Val a * chi4Val b := by
      revert a b; decide
    exact_mod_cast h
  map_nonunit' a ha := by
    fin_cases a
    · have h : chi4Val (0 : ZMod 4) = 0 := by decide
      exact_mod_cast h
    · exfalso; exact ha isUnit_one
    · have h : chi4Val (2 : ZMod 4) = 0 := by decide
      exact_mod_cast h
    · exfalso; exact ha ((ZMod.isUnit_iff_coprime 3 4).mpr (by decide))

lemma chi4_odd : chi4.Odd := by
  change (chi4Val (-1 : ZMod 4) : ℂ) = -1
  have h : chi4Val (-1 : ZMod 4) = -1 := by decide
  exact_mod_cast h

lemma chi4_ne_one : chi4 ≠ 1 := ne_one_of_odd chi4_odd

lemma chi4_real : ∀ a : ZMod 4, (chi4 a).im = 0 := by
  intro a; exact Complex.intCast_im (chi4Val a)

lemma chi4_inv : chi4⁻¹ = chi4 :=
  Stage6ClassNumberFormula.dirichletChar_inv_eq_self_of_real chi4_real

lemma chi4_isPrimitive : chi4.IsPrimitive := by
  show chi4.conductor = 4
  have : NeZero chi4.conductor := ⟨chi4.conductor_ne_zero⟩
  have hdvd : chi4.conductor ∣ 4 := chi4.conductor_dvd_level
  have hne1 : chi4.conductor ≠ 1 := fun h1 =>
    chi4_ne_one (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h1)
  have hne2 : chi4.conductor ≠ 2 := by
    intro h2
    have hprim_eq : chi4.primitiveCharacter = 1 := by
      ext u
      have hu : u = 1 := by
        apply Units.ext
        have hcop := (ZMod.isUnit_iff_coprime (u : ZMod chi4.conductor).val chi4.conductor).mp
          (by rw [ZMod.natCast_zmod_val]; exact u.isUnit)
        have hlt : (u : ZMod chi4.conductor).val < 2 := by rw [← h2]; exact ZMod.val_lt _
        have hv0 : (u : ZMod chi4.conductor).val ≠ 0 := by
          intro h0
          have h1 := hcop.gcd_eq_one
          rw [h0, Nat.gcd_zero_left, h2] at h1
          omega
        have hv1 : (u : ZMod chi4.conductor).val = 1 := by omega
        rw [← ZMod.natCast_zmod_val (u : ZMod chi4.conductor), hv1, Nat.cast_one, Units.val_one]
      rw [hu, Units.val_one, map_one, map_one]
    have hcond : chi4.primitiveCharacter.conductor = chi4.conductor := chi4.primitiveCharacter_isPrimitive
    rw [hprim_eq, DirichletCharacter.conductor_one] at hcond
    exact hne1 hcond.symm
  have hle : chi4.conductor ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < chi4.conductor := Nat.pos_of_ne_zero chi4.conductor_ne_zero
  interval_cases h : chi4.conductor
  · exact (hne1 rfl).elim
  · exact (hne2 rfl).elim
  · norm_num at hdvd
  · rfl

lemma gaussSum_chi4 : gaussSum chi4 ZMod.stdAddChar = 2 * Complex.I := by
  have h := Stage6ClassNumberFormula.gaussSum_real_primitive_eq chi4_isPrimitive chi4_real
  rw [if_neg chi4_odd.not_even] at h
  have hsqrt : Real.sqrt ((4 : ℕ) : ℝ) = 2 := by
    rw [Nat.cast_ofNat, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h, hsqrt]; push_cast; ring

lemma genBernoulli_chi4_one : genBernoulli chi4 1 = -1 / 2 := by
  rw [genBernoulli_one_eq chi4_ne_one]
  have hIco : Finset.Ico 1 4 = {1, 2, 3} := by decide
  rw [hIco]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton,
    OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self, not_false_eq_true]
  have h1 : chi4 ((1 : ℕ) : ZMod 4) = 1 := by
    change (chi4Val ((1 : ℕ) : ZMod 4) : ℂ) = 1
    have h : chi4Val ((1 : ℕ) : ZMod 4) = 1 := by decide
    exact_mod_cast h
  have h2 : chi4 ((2 : ℕ) : ZMod 4) = 0 := by
    change (chi4Val ((2 : ℕ) : ZMod 4) : ℂ) = 0
    have h : chi4Val ((2 : ℕ) : ZMod 4) = 0 := by decide
    exact_mod_cast h
  have h3 : chi4 ((3 : ℕ) : ZMod 4) = -1 := by
    change (chi4Val ((3 : ℕ) : ZMod 4) : ℂ) = -1
    have h : chi4Val ((3 : ℕ) : ZMod 4) = -1 := by decide
    exact_mod_cast h
  rw [h1, h2, h3]
  norm_num

lemma genBernoulli_chi4_three : genBernoulli chi4 3 = 3 / 2 := by
  unfold genBernoulli
  rw [if_neg (by norm_num : (4 : ℕ) ≠ 1)]
  have hIco : Finset.Ico 1 4 = {1, 2, 3} := by decide
  rw [hIco]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton,
    OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self, not_false_eq_true]
  have h1 : chi4 ((1 : ℕ) : ZMod 4) = 1 := by
    change (chi4Val ((1 : ℕ) : ZMod 4) : ℂ) = 1
    have h : chi4Val ((1 : ℕ) : ZMod 4) = 1 := by decide
    exact_mod_cast h
  have h2 : chi4 ((2 : ℕ) : ZMod 4) = 0 := by
    change (chi4Val ((2 : ℕ) : ZMod 4) : ℂ) = 0
    have h : chi4Val ((2 : ℕ) : ZMod 4) = 0 := by decide
    exact_mod_cast h
  have h3 : chi4 ((3 : ℕ) : ZMod 4) = -1 := by
    change (chi4Val ((3 : ℕ) : ZMod 4) : ℂ) = -1
    have h : chi4Val ((3 : ℕ) : ZMod 4) = -1 := by decide
    exact_mod_cast h
  have hB1 : ((Polynomial.bernoulli 3).map (algebraMap ℚ ℂ)).eval ((1 : ℂ) / 4) = 3 / 64 := by
    have h := eval_map_bernoulli_natDiv 3 1 4
    norm_num [Polynomial.bernoulli_three_eval_one_quarter] at h ⊢
    exact h
  have hB3 : ((Polynomial.bernoulli 3).map (algebraMap ℚ ℂ)).eval ((3 : ℂ) / 4) = -3 / 64 := by
    have h := eval_map_bernoulli_sub_div (q := 4) (a := 1) (by norm_num) (by norm_num) 3
    simp only [Nat.reduceSub, Nat.cast_ofNat, Nat.cast_one] at h
    rw [h, hB1]
    norm_num
  rw [h1, h2, h3]
  simp only [Nat.cast_one, Nat.cast_ofNat]
  rw [hB1, hB3]
  norm_num

/-- **Leibniz–Madhava Formula (`0` Assumptions!)**:
`DirichletCharacter.LFunction chi4 1 = Real.pi / 4`. -/
theorem LFunction_one_chi4_eq :
    DirichletCharacter.LFunction chi4 1 = (Real.pi : ℂ) / 4 := by
  have h := LFunction_pos_nat_eq_genBernoulli chi4_isPrimitive chi4_ne_one (k := 1) le_rfl
    (by rw [pow_one]; exact chi4_odd)
  rw [Nat.cast_one, chi4_odd, chi4_inv, gaussSum_chi4, genBernoulli_chi4_one] at h
  rw [h]
  norm_num
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Euler's Cubic Beta Value (`0` Assumptions!)**:
`DirichletCharacter.LFunction chi4 3 = Real.pi ^ 3 / 32`. -/
theorem LFunction_three_chi4_eq :
    DirichletCharacter.LFunction chi4 3 = (Real.pi : ℂ) ^ 3 / 32 := by
  have h := LFunction_pos_nat_eq_genBernoulli chi4_isPrimitive chi4_ne_one (k := 3) (by norm_num)
    (by rw [chi4_odd]; norm_num)
  rw [Nat.cast_ofNat, chi4_odd, chi4_inv, gaussSum_chi4, genBernoulli_chi4_three] at h
  rw [h]
  have hfac3 : (3 ! : ℕ) = 6 := by decide
  rw [hfac3]
  have hI4 : Complex.I * Complex.I ^ 3 = 1 := by
    rw [show Complex.I * Complex.I ^ 3 = (Complex.I ^ 2) ^ 2 by ring, Complex.I_sq]; norm_num
  ring_nf
  rw [show Complex.I ^ 4 = (Complex.I ^ 2) ^ 2 by ring, Complex.I_sq]
  norm_num

/-- Integer value function for `χ₋₃` modulo `3`. -/
private def chi3Val (a : ZMod 3) : ℤ :=
  match a.val with
  | 1 => 1
  | 2 => -1
  | _ => 0

/-- The unique primitive quadratic Dirichlet character `χ₋₃` modulo `3` (`χ₋₃(1) = 1`, `χ₋₃(2) = -1`). -/
def chi3 : DirichletCharacter ℂ 3 where
  toFun a := (chi3Val a : ℂ)
  map_one' := by
    have h : chi3Val (1 : ZMod 3) = 1 := by decide
    exact_mod_cast h
  map_mul' a b := by
    have h : chi3Val (a * b) = chi3Val a * chi3Val b := by
      revert a b; decide
    exact_mod_cast h
  map_nonunit' a ha := by
    fin_cases a
    · have h : chi3Val (0 : ZMod 3) = 0 := by decide
      exact_mod_cast h
    · exfalso; exact ha isUnit_one
    · exfalso; exact ha ((ZMod.isUnit_iff_coprime 2 3).mpr (by decide))

lemma chi3_odd : chi3.Odd := by
  change (chi3Val (-1 : ZMod 3) : ℂ) = -1
  have h : chi3Val (-1 : ZMod 3) = -1 := by decide
  exact_mod_cast h

lemma chi3_ne_one : chi3 ≠ 1 := ne_one_of_odd chi3_odd

lemma chi3_real : ∀ a : ZMod 3, (chi3 a).im = 0 := by
  intro a; exact Complex.intCast_im (chi3Val a)

lemma chi3_inv : chi3⁻¹ = chi3 :=
  Stage6ClassNumberFormula.dirichletChar_inv_eq_self_of_real chi3_real

lemma chi3_isPrimitive : chi3.IsPrimitive := by
  show chi3.conductor = 3
  have hdvd : chi3.conductor ∣ 3 := chi3.conductor_dvd_level
  have hne1 : chi3.conductor ≠ 1 := fun h1 =>
    chi3_ne_one (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h1)
  exact ((Nat.prime_three.dvd_iff_eq hne1).mp hdvd).symm

lemma gaussSum_chi3 : gaussSum chi3 ZMod.stdAddChar = Complex.I * (Real.sqrt 3 : ℂ) := by
  have h := Stage6ClassNumberFormula.gaussSum_real_primitive_eq chi3_isPrimitive chi3_real
  rw [if_neg chi3_odd.not_even] at h
  simpa using h

lemma genBernoulli_chi3_one : genBernoulli chi3 1 = -1 / 3 := by
  rw [genBernoulli_one_eq chi3_ne_one]
  have hIco : Finset.Ico 1 3 = {1, 2} := by decide
  rw [hIco]
  simp only [Finset.sum_insert, Finset.mem_singleton, Finset.sum_singleton,
    OfNat.one_ne_ofNat, not_false_eq_true]
  have h1 : chi3 ((1 : ℕ) : ZMod 3) = 1 := by
    change (chi3Val ((1 : ℕ) : ZMod 3) : ℂ) = 1
    have h : chi3Val ((1 : ℕ) : ZMod 3) = 1 := by decide
    exact_mod_cast h
  have h2 : chi3 ((2 : ℕ) : ZMod 3) = -1 := by
    change (chi3Val ((2 : ℕ) : ZMod 3) : ℂ) = -1
    have h : chi3Val ((2 : ℕ) : ZMod 3) = -1 := by decide
    exact_mod_cast h
  rw [h1, h2]
  norm_num

/-- **Exact Quadratic `L(1, χ₋₃)` Formula (`0` Assumptions!)**:
`DirichletCharacter.LFunction chi3 1 = Real.pi / (3 * Real.sqrt 3)`. -/
theorem LFunction_one_chi3_eq :
    DirichletCharacter.LFunction chi3 1 = (Real.pi : ℂ) / (3 * (Real.sqrt 3 : ℂ)) := by
  have h := LFunction_pos_nat_eq_genBernoulli chi3_isPrimitive chi3_ne_one (k := 1) le_rfl
    (by rw [pow_one]; exact chi3_odd)
  rw [Nat.cast_one, chi3_odd, chi3_inv, gaussSum_chi3, genBernoulli_chi3_one] at h
  rw [h]
  have hsq : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hsq_ne : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  field_simp [hsq_ne]
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  ring_nf
  rw [hI2, show (Real.sqrt 3 : ℂ) ^ 2 = 3 by rw [sq]; exact hsq]
  ring

/-! ### Explicit Special Values of Mathlib's `riemannZeta` -/

lemma bernoulli_four_eq : bernoulli 4 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide : (4 : ℕ) ≠ 1), bernoulli'_four]

lemma bernoulli_six_eq : bernoulli 6 = 1 / 42 := by
  have h := sum_bernoulli 7
  have h7 : Finset.range 7 = {0, 1, 2, 3, 4, 5, 6} := by decide
  rw [h7] at h
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton,
    Nat.reduceEqDiff, or_self, not_false_eq_true, OfNat.zero_ne_ofNat, OfNat.one_ne_ofNat] at h
  have hb3 : bernoulli 3 = 0 := bernoulli_eq_zero_of_odd (by decide) (by norm_num)
  have hb5 : bernoulli 5 = 0 := bernoulli_eq_zero_of_odd (by decide) (by norm_num)
  rw [bernoulli_zero, bernoulli_one, bernoulli_two, hb3, bernoulli_four_eq, hb5] at h
  norm_num [Nat.choose] at h
  linarith

theorem riemannZeta_zero_eq : riemannZeta 0 = -1 / 2 := riemannZeta_zero

theorem riemannZeta_neg_one_eq : riemannZeta (-1) = -1 / 12 := by
  have h := riemannZeta_neg_nat_eq_bernoulli 1
  norm_num [bernoulli_two] at h ⊢
  exact h

theorem riemannZeta_neg_three_eq : riemannZeta (-3) = 1 / 120 := by
  have h := riemannZeta_neg_nat_eq_bernoulli 3
  norm_num [bernoulli_four_eq] at h ⊢
  exact h

theorem riemannZeta_two_eq : riemannZeta 2 = (Real.pi : ℂ) ^ 2 / 6 := riemannZeta_two

theorem riemannZeta_four_eq : riemannZeta 4 = (Real.pi : ℂ) ^ 4 / 90 := riemannZeta_four

theorem riemannZeta_six_eq : riemannZeta 6 = (Real.pi : ℂ) ^ 6 / 945 := by
  have h := riemannZeta_two_mul_nat (k := 3) (by decide)
  have hfac6 : (6 ! : ℕ) = 720 := by decide
  norm_num [bernoulli_six_eq, hfac6] at h ⊢
  rw [h]
  ring

/-! ## Section 3: Unconditional Irrationality of `π²`, `π`, and `e^r` (`∀ r : ℚ, r ≠ 0`) -/

section NivenIrrationality

/-- Niven's integer polynomial `P_n(X) = X^n * (1 - X)^n ∈ ℤ[X]`. -/
private def nivenPolyZ (n : ℕ) : Polynomial ℤ :=
  Polynomial.X ^ n * (1 - Polynomial.X) ^ n

/-- Niven's scaled real polynomial `f_n(X) = (n!)⁻¹ * P_n(X) ∈ ℝ[X]`. -/
private def nivenPolyR (n : ℕ) : Polynomial ℝ :=
  Polynomial.C ((n ! : ℝ)⁻¹) * (nivenPolyZ n).map (Int.castRingHom ℝ)

private lemma nivenPolyZ_comp_one_sub (n : ℕ) :
    (nivenPolyZ n).comp (1 - Polynomial.X) = nivenPolyZ n := by
  unfold nivenPolyZ
  simp only [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp,
    Polynomial.sub_comp, Polynomial.one_comp, sub_sub_cancel, mul_comm]

private lemma nivenPolyZ_natDegree_le (n : ℕ) : (nivenPolyZ n).natDegree ≤ 2 * n := by
  unfold nivenPolyZ
  have h1 : ((1 : Polynomial ℤ) - Polynomial.X).natDegree ≤ 1 := by
    calc ((1 : Polynomial ℤ) - Polynomial.X).natDegree
        ≤ max (1 : Polynomial ℤ).natDegree (Polynomial.X : Polynomial ℤ).natDegree :=
          Polynomial.natDegree_sub_le _ _
      _ = 1 := by simp
  calc ((Polynomial.X : Polynomial ℤ) ^ n * (1 - Polynomial.X) ^ n).natDegree
      ≤ ((Polynomial.X : Polynomial ℤ) ^ n).natDegree +
          (((1 : Polynomial ℤ) - Polynomial.X) ^ n).natDegree := Polynomial.natDegree_mul_le
    _ ≤ n + n * ((1 : Polynomial ℤ) - Polynomial.X).natDegree :=
        add_le_add (Polynomial.natDegree_X_pow_le n) Polynomial.natDegree_pow_le
    _ ≤ n + n * 1 := by gcongr
    _ = 2 * n := by omega

private lemma nivenPolyR_natDegree_le (n : ℕ) : (nivenPolyR n).natDegree ≤ 2 * n := by
  unfold nivenPolyR
  calc (Polynomial.C ((n ! : ℝ)⁻¹) * (nivenPolyZ n).map (Int.castRingHom ℝ)).natDegree
      ≤ (Polynomial.C ((n ! : ℝ)⁻¹)).natDegree +
          ((nivenPolyZ n).map (Int.castRingHom ℝ)).natDegree := Polynomial.natDegree_mul_le
    _ ≤ 0 + (nivenPolyZ n).natDegree := by
        rw [Polynomial.natDegree_C]
        gcongr
        exact Polynomial.natDegree_map_le
    _ ≤ 2 * n := by rw [zero_add]; exact nivenPolyZ_natDegree_le n

private lemma nivenPolyZ_coeff_eq_zero_of_lt (n k : ℕ) (hk : k < n) :
    (nivenPolyZ n).coeff k = 0 := by
  unfold nivenPolyZ
  rw [Polynomial.coeff_X_pow_mul']
  exact if_neg (by omega)

/-- Symmetry of iterated derivatives: `(derivative^[k] P).comp (1 - X) = (-1)^k * derivative^[k] P`
whenever `P.comp (1 - X) = P`. -/
private lemma iterate_derivative_comp_one_sub {R : Type*} [CommRing R]
    (P : Polynomial R) (hP : P.comp (1 - Polynomial.X) = P) (k : ℕ) :
    (Polynomial.derivative^[k] P).comp (1 - Polynomial.X) =
      (-1 : Polynomial R) ^ k * Polynomial.derivative^[k] P := by
  induction k with
  | zero => simpa using hP
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hderiv := congrArg Polynomial.derivative ih
    rw [Polynomial.derivative_comp, Polynomial.derivative_sub, Polynomial.derivative_one,
      Polynomial.derivative_X, zero_sub, Polynomial.derivative_mul,
      show Polynomial.derivative ((-1 : Polynomial R) ^ k) = 0 by
        rw [show (-1 : Polynomial R) ^ k = Polynomial.C ((-1 : R) ^ k) by simp,
          Polynomial.derivative_C],
      zero_mul, zero_add] at hderiv
    rw [pow_succ]
    linear_combination -hderiv

/-- Key integrality lemma: every `k`-th derivative of Niven's polynomial `nivenPolyR n` evaluates
to an **exact integer** at both `x = 0` and `x = 1`! -/
private lemma exists_int_iterate_derivative_nivenPolyR_zero (n k : ℕ) :
    ∃ m : ℤ, (Polynomial.derivative^[k] (nivenPolyR n)).eval 0 = (m : ℝ) := by
  have hderiv :
      Polynomial.derivative^[k] (nivenPolyR n) =
        Polynomial.C ((n ! : ℝ)⁻¹) *
          (Polynomial.derivative^[k] (nivenPolyZ n)).map (Int.castRingHom ℝ) := by
    unfold nivenPolyR
    rw [Polynomial.iterate_derivative_C_mul, Polynomial.iterate_derivative_map]
  rw [hderiv, Polynomial.eval_mul, Polynomial.eval_C, ← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_map, Polynomial.coeff_iterate_derivative, zero_add]
  by_cases hkn : k < n
  · refine ⟨0, ?_⟩
    rw [nivenPolyZ_coeff_eq_zero_of_lt n k hkn]
    simp
  · have hnk : n ≤ k := by omega
    have hdvd : n ! ∣ k ! := Nat.factorial_dvd_factorial hnk
    obtain ⟨q, hq⟩ := hdvd
    refine ⟨(q : ℤ) * (nivenPolyZ n).coeff k, ?_⟩
    rw [Nat.descFactorial_self, nsmul_eq_mul, eq_intCast]
    have hqR : (k ! : ℝ) = (n ! : ℝ) * (q : ℝ) := by exact_mod_cast hq
    have hfac_ne : (n ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    push_cast
    rw [hqR]
    field_simp [hfac_ne]

private lemma exists_int_iterate_derivative_nivenPolyR_one (n k : ℕ) :
    ∃ m : ℤ, (Polynomial.derivative^[k] (nivenPolyR n)).eval 1 = (m : ℝ) := by
  obtain ⟨m, hm⟩ := exists_int_iterate_derivative_nivenPolyR_zero n k
  refine ⟨(-1 : ℤ) ^ k * m, ?_⟩
  have hsymR : (nivenPolyR n).comp (1 - Polynomial.X) = nivenPolyR n := by
    have h := congrArg (Polynomial.map (Int.castRingHom ℝ)) (nivenPolyZ_comp_one_sub n)
    rw [Polynomial.map_comp, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X] at h
    unfold nivenPolyR
    rw [Polynomial.mul_comp, Polynomial.C_comp, h]
  have hcomp := congrArg (Polynomial.eval (0 : ℝ))
    (iterate_derivative_comp_one_sub (nivenPolyR n) hsymR k)
  simp only [Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X,
    sub_zero, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg] at hcomp
  rw [hcomp, hm]
  push_cast
  rfl

private lemma nivenPolyR_eval (n : ℕ) (x : ℝ) :
    (nivenPolyR n).eval x = x ^ n * (1 - x) ^ n / (n ! : ℝ) := by
  unfold nivenPolyR nivenPolyZ
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_sub, Polynomial.map_one, Polynomial.map_X, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X, div_eq_inv_mul]

/-- Helper: `c * A^n / n! < 1` for sufficiently large `n` (via `Real.summable_pow_div_factorial`). -/
private lemma exists_nat_mul_pow_div_factorial_lt_one (c A : ℝ) :
    ∃ n : ℕ, c * A ^ n / (n ! : ℝ) < 1 := by
  have htend : Tendsto (fun n : ℕ => c * (A ^ n / (n ! : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using (Real.summable_pow_div_factorial A).tendsto_atTop_zero.const_mul c
  have hev : ∀ᶠ n in atTop, c * (A ^ n / (n ! : ℝ)) < 1 :=
    htend.eventually (Iio_mem_nhds zero_lt_one)
  obtain ⟨n, hn⟩ := hev.exists
  exact ⟨n, by rwa [← mul_div_assoc] at hn⟩

/-- No integer lies strictly between `0` and `1`. -/
private lemma not_int_between_zero_and_one (m : ℤ) (h0 : (0 : ℝ) < (m : ℝ)) (h1 : (m : ℝ) < 1) :
    False := by
  have hm0 : (0 : ℤ) < m := by exact_mod_cast h0
  have hm1 : m < 1 := by exact_mod_cast h1
  omega

/-- **NIVEN'S 1947 THEOREM (`0` ASSUMPTIONS!)**: `π²` is irrational! -/
theorem irrational_pi_sq : Irrational (Real.pi ^ 2) := by
  rw [irrational_iff_ne_rational]
  intro a₀ b₀ hb₀ hrat
  -- Extract positive natural numbers `a, b` with `π² = a / b`
  have hpi2_pos : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have ha₀_ne : a₀ ≠ 0 := by
    intro h0; rw [h0, Int.cast_zero, zero_div] at hrat; linarith
  set a : ℕ := a₀.natAbs
  set b : ℕ := b₀.natAbs
  have ha_pos : 0 < a := Int.natAbs_pos.mpr ha₀_ne
  have hb_pos : 0 < b := Int.natAbs_pos.mpr hb₀
  have hpi2_eq : Real.pi ^ 2 = (a : ℝ) / (b : ℝ) := by
    have habs := congrArg abs hrat
    rw [abs_of_pos hpi2_pos, abs_div, ← Int.cast_abs, ← Int.cast_abs,
      Int.abs_eq_natAbs, Int.abs_eq_natAbs] at habs
    simpa [a, b] using habs
  -- Choose `n` large enough that `Real.pi * a^n / n! < 1`
  obtain ⟨n, hn_small⟩ := exists_nat_mul_pow_div_factorial_lt_one Real.pi (a : ℝ)
  -- Define Niven's alternating sum polynomial `F(X) = ∑_{j=0}^n (-1)^j * π^{2(n-j)} * f_n^{(2j)}(X)`
  let F : Polynomial ℝ :=
    ∑ j ∈ Finset.range (n + 1),
      Polynomial.C ((-1 : ℝ) ^ j * (Real.pi ^ 2) ^ (n - j)) *
        (Polynomial.derivative^[2 * j] (nivenPolyR n))
  -- Telescoping differential equation: `F'' + π² * F = π^{2(n+1)} * f_n`
  have hF_ode :
      Polynomial.derivative (Polynomial.derivative F) + Polynomial.C (Real.pi ^ 2) * F =
        Polynomial.C ((Real.pi ^ 2) ^ (n + 1)) * nivenPolyR n := by
    have hF2 :
        Polynomial.derivative (Polynomial.derivative F) =
          ∑ j ∈ Finset.range (n + 1),
            Polynomial.C ((-1 : ℝ) ^ j * (Real.pi ^ 2) ^ (n - j)) *
              (Polynomial.derivative^[2 * (j + 1)] (nivenPolyR n)) := by
      simp only [F, Polynomial.derivative_sum, Polynomial.derivative_C_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show 2 * (j + 1) = (2 * j + 1) + 1 by omega, Function.iterate_succ_apply',
        Function.iterate_succ_apply']
    have hFpi :
        Polynomial.C (Real.pi ^ 2) * F =
          ∑ j ∈ Finset.range (n + 1),
            Polynomial.C ((-1 : ℝ) ^ j * (Real.pi ^ 2) ^ (n + 1 - j)) *
              (Polynomial.derivative^[2 * j] (nivenPolyR n)) := by
      simp only [F, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj_le : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [← mul_assoc, ← map_mul]
      congr 2
      have hexp : n + 1 - j = (n - j) + 1 := by omega
      rw [hexp, pow_succ]; ring
    rw [hF2, hFpi]
    -- Peel off top term `j = n` from `hF2` (which is `0`) and bottom term `j = 0` from `hFpi`
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
    have htop0 : Polynomial.derivative^[2 * (n + 1)] (nivenPolyR n) = 0 :=
      Polynomial.iterate_derivative_eq_zero ((nivenPolyR_natDegree_le n).trans_lt (by omega))
    rw [htop0, mul_zero, add_zero]
    have hcancel :
        (∑ j ∈ Finset.range n,
            Polynomial.C ((-1 : ℝ) ^ j * (Real.pi ^ 2) ^ (n - j)) *
              (Polynomial.derivative^[2 * (j + 1)] (nivenPolyR n))) +
        (∑ j ∈ Finset.range n,
            Polynomial.C ((-1 : ℝ) ^ (j + 1) * (Real.pi ^ 2) ^ (n + 1 - (j + 1))) *
              (Polynomial.derivative^[2 * (j + 1)] (nivenPolyR n))) = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [show n + 1 - (j + 1) = n - j by omega, ← add_mul, ← map_add, pow_succ (-1 : ℝ)]
      have h0 : (-1 : ℝ) ^ j * (Real.pi ^ 2) ^ (n - j) +
          (-1 : ℝ) ^ j * -1 * (Real.pi ^ 2) ^ (n - j) = 0 := by ring
      rw [h0, map_zero, zero_mul]
    rw [← add_assoc, hcancel, zero_add]
    simp
  -- Antiderivative `H(x) = b^n * (π⁻¹ * F'(x) * sin(π x) - F(x) * cos(π x))`
  let H : ℝ → ℝ := fun x =>
    (b : ℝ) ^ n *
      (Real.pi⁻¹ * (Polynomial.derivative F).eval x * Real.sin (Real.pi * x) -
        F.eval x * Real.cos (Real.pi * x))
  have hH_deriv : ∀ x : ℝ,
      HasDerivAt H (Real.pi * (a : ℝ) ^ n * (nivenPolyR n).eval x * Real.sin (Real.pi * x)) x := by
    intro x
    have hF_d : HasDerivAt (fun t => F.eval t) ((Polynomial.derivative F).eval x) x :=
      F.hasDerivAt x
    have hF'_d : HasDerivAt (fun t => (Polynomial.derivative F).eval t)
        ((Polynomial.derivative (Polynomial.derivative F)).eval x) x :=
      (Polynomial.derivative F).hasDerivAt x
    have hlin : HasDerivAt (fun t : ℝ => Real.pi * t) Real.pi x :=
      ((hasDerivAt_id' x).const_mul Real.pi).congr_deriv (mul_one Real.pi)
    have hsin_d : HasDerivAt (fun t => Real.sin (Real.pi * t)) (Real.cos (Real.pi * x) * Real.pi) x :=
      (Real.hasDerivAt_sin (Real.pi * x)).comp x hlin
    have hcos_d : HasDerivAt (fun t => Real.cos (Real.pi * t)) (-Real.sin (Real.pi * x) * Real.pi) x :=
      (Real.hasDerivAt_cos (Real.pi * x)).comp x hlin
    have hraw := ((hF'_d.const_mul Real.pi⁻¹).mul hsin_d |>.sub (hF_d.mul hcos_d)).const_mul ((b : ℝ) ^ n)
    refine hraw.congr_deriv ?_
    have hode_x := congrArg (Polynomial.eval x) hF_ode
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at hode_x
    have hbn_pi : (b : ℝ) ^ n * (Real.pi ^ 2) ^ n = (a : ℝ) ^ n := by
      rw [← mul_pow, hpi2_eq, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hb_pos.ne')]
    have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
    calc (b : ℝ) ^ n *
          (Real.pi⁻¹ * (Polynomial.derivative (Polynomial.derivative F)).eval x * Real.sin (Real.pi * x) +
            Real.pi⁻¹ * (Polynomial.derivative F).eval x * (Real.cos (Real.pi * x) * Real.pi) -
            ((Polynomial.derivative F).eval x * Real.cos (Real.pi * x) +
              F.eval x * (-Real.sin (Real.pi * x) * Real.pi)))
        = (b : ℝ) ^ n * Real.pi⁻¹ *
            ((Polynomial.derivative (Polynomial.derivative F)).eval x + Real.pi ^ 2 * F.eval x) *
            Real.sin (Real.pi * x) := by field_simp [hpi_ne]; ring
      _ = (b : ℝ) ^ n * Real.pi⁻¹ * ((Real.pi ^ 2) ^ (n + 1) * (nivenPolyR n).eval x) *
            Real.sin (Real.pi * x) := by rw [hode_x]
      _ = Real.pi * ((b : ℝ) ^ n * (Real.pi ^ 2) ^ n) * (nivenPolyR n).eval x *
            Real.sin (Real.pi * x) := by rw [pow_succ]; field_simp [hpi_ne]
      _ = Real.pi * (a : ℝ) ^ n * (nivenPolyR n).eval x * Real.sin (Real.pi * x) := by rw [hbn_pi]
  -- Evaluate the integral `I = ∫_0^1 π * a^n * f_n(x) * sin(π x) dx = b^n * (F(1) + F(0))`
  set g : ℝ → ℝ := fun x => Real.pi * (a : ℝ) ^ n * (nivenPolyR n).eval x * Real.sin (Real.pi * x)
  have hg_cont : Continuous g := by
    dsimp only [g]
    exact (((continuous_const.mul (nivenPolyR n).continuous)).mul
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)))
  have hint_eq : ∫ x in (0 : ℝ)..1, g x = (b : ℝ) ^ n * F.eval 1 + (b : ℝ) ^ n * F.eval 0 := by
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hH_deriv x) (hg_cont.intervalIntegrable 0 1)
    rw [hftc]
    simp only [H, mul_one, mul_zero, Real.sin_pi, Real.sin_zero, Real.cos_pi, Real.cos_zero]
    ring
  -- Step 1: `b^n * F(0)` and `b^n * F(1)` are exact integers!
  have hbF_int : ∀ x : ℝ, (∀ k : ℕ, ∃ m : ℤ, (Polynomial.derivative^[k] (nivenPolyR n)).eval x = (m : ℝ)) →
      ∃ M : ℤ, (b : ℝ) ^ n * F.eval x = (M : ℝ) := by
    intro x hx
    have heval :
        (b : ℝ) ^ n * F.eval x =
          ∑ j ∈ Finset.range (n + 1),
            (-1 : ℝ) ^ j * (b : ℝ) ^ j * (a : ℝ) ^ (n - j) *
              (Polynomial.derivative^[2 * j] (nivenPolyR n)).eval x := by
      simp only [F, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj_le : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hbn : (b : ℝ) ^ n = (b : ℝ) ^ j * (b : ℝ) ^ (n - j) := by
        rw [← pow_add, Nat.add_sub_of_le hj_le]
      have hba : (b : ℝ) ^ (n - j) * (Real.pi ^ 2) ^ (n - j) = (a : ℝ) ^ (n - j) := by
        rw [← mul_pow, hpi2_eq, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hb_pos.ne')]
      calc (b : ℝ) ^ n * ((-1 : ℝ) ^ j * (Real.pi ^ 2) ^ (n - j) *
              (Polynomial.derivative^[2 * j] (nivenPolyR n)).eval x)
          = (-1 : ℝ) ^ j * (b : ℝ) ^ j * ((b : ℝ) ^ (n - j) * (Real.pi ^ 2) ^ (n - j)) *
              (Polynomial.derivative^[2 * j] (nivenPolyR n)).eval x := by rw [hbn]; ring
        _ = (-1 : ℝ) ^ j * (b : ℝ) ^ j * (a : ℝ) ^ (n - j) *
              (Polynomial.derivative^[2 * j] (nivenPolyR n)).eval x := by rw [hba]
    rw [heval]
    choose m hm using hx
    refine ⟨∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ j * (b : ℤ) ^ j * (a : ℤ) ^ (n - j) * m (2 * j), ?_⟩
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hm (2 * j)]
  obtain ⟨M₀, hM₀⟩ := hbF_int 0 (exists_int_iterate_derivative_nivenPolyR_zero n)
  obtain ⟨M₁, hM₁⟩ := hbF_int 1 (exists_int_iterate_derivative_nivenPolyR_one n)
  have hint_int : ∫ x in (0 : ℝ)..1, g x = ((M₁ + M₀ : ℤ) : ℝ) := by
    rw [hint_eq, hM₁, hM₀]; push_cast; rfl
  -- Step 2: `0 < ∫_0^1 g x`
  have hint_pos : 0 < ∫ x in (0 : ℝ)..1, g x := by
    refine intervalIntegral.integral_pos zero_lt_one hg_cont.continuousOn ?_ ?_
    · intro x hx
      dsimp only [g]
      rw [nivenPolyR_eval]
      have hx0 : 0 ≤ x := hx.1.le
      have hx1 : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
      have hsin : 0 ≤ Real.sin (Real.pi * x) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le hx0)
          (by nlinarith [Real.pi_pos, hx.2])
      positivity
    · refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
      dsimp only [g]
      rw [nivenPolyR_eval, show Real.pi * (1 / 2 : ℝ) = Real.pi / 2 by ring, Real.sin_pi_div_two]
      have h12 : (0 : ℝ) < 1 - 1 / 2 := by norm_num
      have hpi : 0 < Real.pi := Real.pi_pos
      have haR : (0 : ℝ) < (a : ℝ) := Nat.cast_pos.mpr ha_pos
      positivity
  -- Step 3: `∫_0^1 g x ≤ π * a^n / n! < 1`
  have hint_le : ∫ x in (0 : ℝ)..1, g x ≤ Real.pi * (a : ℝ) ^ n / (n ! : ℝ) := by
    have hconst : ∫ _x in (0 : ℝ)..1, (Real.pi * (a : ℝ) ^ n / (n ! : ℝ)) =
        Real.pi * (a : ℝ) ^ n / (n ! : ℝ) := by simp
    rw [← hconst]
    refine intervalIntegral.integral_mono_on zero_le_one (hg_cont.intervalIntegrable 0 1)
      intervalIntegrable_const fun x hx => ?_
    dsimp only [g]
    rw [nivenPolyR_eval]
    have hxn : x ^ n ≤ 1 := pow_le_one₀ hx.1 hx.2
    have h1xn : (1 - x) ^ n ≤ 1 := pow_le_one₀ (sub_nonneg.mpr hx.2) (by linarith [hx.1])
    have hsin : Real.sin (Real.pi * x) ≤ 1 := Real.sin_le_one _
    have hprod_le : x ^ n * (1 - x) ^ n ≤ 1 := by
      have : 0 ≤ x ^ n := pow_nonneg hx.1 n
      have : 0 ≤ (1 - x) ^ n := pow_nonneg (sub_nonneg.mpr hx.2) n
      nlinarith
    have hdiv_le : x ^ n * (1 - x) ^ n / (n ! : ℝ) ≤ 1 / (n ! : ℝ) :=
      div_le_div_of_nonneg_right hprod_le (Nat.cast_nonneg _)
    have hc_nn : 0 ≤ Real.pi * (a : ℝ) ^ n := by positivity
    have h1 : Real.pi * (a : ℝ) ^ n * (x ^ n * (1 - x) ^ n / (n ! : ℝ)) * Real.sin (Real.pi * x) ≤
        Real.pi * (a : ℝ) ^ n * (x ^ n * (1 - x) ^ n / (n ! : ℝ)) * 1 := by
      have hf_nn : 0 ≤ x ^ n * (1 - x) ^ n / (n ! : ℝ) := by
        have : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
        have : 0 ≤ x := hx.1
        positivity
      exact mul_le_mul_of_nonneg_left hsin (mul_nonneg hc_nn hf_nn)
    calc Real.pi * (a : ℝ) ^ n * (x ^ n * (1 - x) ^ n / (n ! : ℝ)) * Real.sin (Real.pi * x)
        ≤ Real.pi * (a : ℝ) ^ n * (x ^ n * (1 - x) ^ n / (n ! : ℝ)) := by simpa using h1
      _ ≤ Real.pi * (a : ℝ) ^ n * (1 / (n ! : ℝ)) := mul_le_mul_of_nonneg_left hdiv_le hc_nn
      _ = Real.pi * (a : ℝ) ^ n / (n ! : ℝ) := by ring
  exact not_int_between_zero_and_one (M₁ + M₀) (hint_int ▸ hint_pos)
    ((hint_int ▸ hint_le).trans_lt hn_small)

/-- **COROLLARY (`0` ASSUMPTIONS!)**: `π` is irrational! -/
theorem irrational_pi : Irrational Real.pi := by
  rintro ⟨q, hq⟩
  apply irrational_pi_sq
  refine ⟨q ^ 2, ?_⟩
  rw [Rat.cast_pow, hq]

/-- **HERMITE–NIVEN IRRATIONALITY OF `e^k` FOR EVERY POSITIVE INTEGER `k ≥ 1`**:
`Irrational (Real.exp k)` (reusing the exact same Niven polynomial `nivenPolyR n`!). -/
theorem irrational_exp_nat_pos {k : ℕ} (hk : 1 ≤ k) : Irrational (Real.exp (k : ℝ)) := by
  rw [irrational_iff_ne_rational]
  intro a₀ b₀ hb₀ hrat
  have hexp_pos : 0 < Real.exp (k : ℝ) := Real.exp_pos _
  have ha₀_ne : a₀ ≠ 0 := by
    intro h0; rw [h0, Int.cast_zero, zero_div] at hrat; linarith
  set a : ℕ := a₀.natAbs
  set b : ℕ := b₀.natAbs
  have ha_pos : 0 < a := Int.natAbs_pos.mpr ha₀_ne
  have hb_pos : 0 < b := Int.natAbs_pos.mpr hb₀
  have hexp_eq : Real.exp (k : ℝ) = (a : ℝ) / (b : ℝ) := by
    have habs := congrArg abs hrat
    rw [abs_of_pos hexp_pos, abs_div, ← Int.cast_abs, ← Int.cast_abs,
      Int.abs_eq_natAbs, Int.abs_eq_natAbs] at habs
    simpa [a, b] using habs
  -- Choose `n` large enough that `(b * k * e^k) * (k^2)^n / n! < 1`
  obtain ⟨n, hn_small⟩ :=
    exists_nat_mul_pow_div_factorial_lt_one ((b : ℝ) * (k : ℝ) * Real.exp (k : ℝ)) ((k : ℝ) ^ 2)
  -- Define `F(X) = ∑_{j=0}^{2n} (-1)^j * k^{2n - j} * f_n^{(j)}(X)`
  let F : Polynomial ℝ :=
    ∑ j ∈ Finset.range (2 * n + 1),
      Polynomial.C ((-1 : ℝ) ^ j * (k : ℝ) ^ (2 * n - j)) *
        (Polynomial.derivative^[j] (nivenPolyR n))
  -- Telescoping ODE: `F' + k * F = k^{2n + 1} * f_n`
  have hF_ode :
      Polynomial.derivative F + Polynomial.C (k : ℝ) * F =
        Polynomial.C ((k : ℝ) ^ (2 * n + 1)) * nivenPolyR n := by
    have hF1 :
        Polynomial.derivative F =
          ∑ j ∈ Finset.range (2 * n + 1),
            Polynomial.C ((-1 : ℝ) ^ j * (k : ℝ) ^ (2 * n - j)) *
              (Polynomial.derivative^[j + 1] (nivenPolyR n)) := by
      simp only [F, Polynomial.derivative_sum, Polynomial.derivative_C_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Function.iterate_succ_apply']
    have hFk :
        Polynomial.C (k : ℝ) * F =
          ∑ j ∈ Finset.range (2 * n + 1),
            Polynomial.C ((-1 : ℝ) ^ j * (k : ℝ) ^ (2 * n + 1 - j)) *
              (Polynomial.derivative^[j] (nivenPolyR n)) := by
      simp only [F, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj_le : j ≤ 2 * n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [← mul_assoc, ← map_mul]
      congr 2
      have hexp : 2 * n + 1 - j = (2 * n - j) + 1 := by omega
      rw [hexp, pow_succ]; ring
    rw [hF1, hFk, Finset.sum_range_succ, Finset.sum_range_succ']
    have htop0 : Polynomial.derivative^[2 * n + 1] (nivenPolyR n) = 0 :=
      Polynomial.iterate_derivative_eq_zero ((nivenPolyR_natDegree_le n).trans_lt (by omega))
    rw [htop0, mul_zero, add_zero]
    have hcancel :
        (∑ j ∈ Finset.range (2 * n),
            Polynomial.C ((-1 : ℝ) ^ j * (k : ℝ) ^ (2 * n - j)) *
              (Polynomial.derivative^[j + 1] (nivenPolyR n))) +
        (∑ j ∈ Finset.range (2 * n),
            Polynomial.C ((-1 : ℝ) ^ (j + 1) * (k : ℝ) ^ (2 * n + 1 - (j + 1))) *
              (Polynomial.derivative^[j + 1] (nivenPolyR n))) = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [show 2 * n + 1 - (j + 1) = 2 * n - j by omega, ← add_mul, ← map_add, pow_succ]
      have : (-1 : ℝ) ^ j * (k : ℝ) ^ (2 * n - j) +
          (-1 : ℝ) ^ j * -1 * (k : ℝ) ^ (2 * n - j) = 0 := by ring
      rw [this, map_zero, zero_mul]
    rw [← add_assoc, hcancel, zero_add]
    simp
  -- Antiderivative `H(x) = b * exp(k * x) * F(x)`
  let H : ℝ → ℝ := fun x => (b : ℝ) * Real.exp ((k : ℝ) * x) * F.eval x
  have hH_deriv : ∀ x : ℝ,
      HasDerivAt H ((b : ℝ) * (k : ℝ) ^ (2 * n + 1) * (nivenPolyR n).eval x * Real.exp ((k : ℝ) * x)) x := by
    intro x
    have hlin : HasDerivAt (fun t : ℝ => (k : ℝ) * t) (k : ℝ) x :=
      ((hasDerivAt_id' x).const_mul (k : ℝ)).congr_deriv (mul_one (k : ℝ))
    have hexp_d : HasDerivAt (fun t => Real.exp ((k : ℝ) * t)) (Real.exp ((k : ℝ) * x) * (k : ℝ)) x :=
      (Real.hasDerivAt_exp ((k : ℝ) * x)).comp x hlin
    have hF_d : HasDerivAt (fun t => F.eval t) ((Polynomial.derivative F).eval x) x := F.hasDerivAt x
    have hraw := ((hexp_d.const_mul (b : ℝ)).mul hF_d)
    refine hraw.congr_deriv ?_
    have hode_x := congrArg (Polynomial.eval x) hF_ode
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at hode_x
    calc (b : ℝ) * (Real.exp ((k : ℝ) * x) * (k : ℝ)) * F.eval x +
          (b : ℝ) * Real.exp ((k : ℝ) * x) * (Polynomial.derivative F).eval x
        = (b : ℝ) * ((Polynomial.derivative F).eval x + (k : ℝ) * F.eval x) * Real.exp ((k : ℝ) * x) := by
          ring
      _ = (b : ℝ) * ((k : ℝ) ^ (2 * n + 1) * (nivenPolyR n).eval x) * Real.exp ((k : ℝ) * x) := by
          rw [hode_x]
      _ = (b : ℝ) * (k : ℝ) ^ (2 * n + 1) * (nivenPolyR n).eval x * Real.exp ((k : ℝ) * x) := by
          ring
  set g : ℝ → ℝ := fun x =>
    (b : ℝ) * (k : ℝ) ^ (2 * n + 1) * (nivenPolyR n).eval x * Real.exp ((k : ℝ) * x)
  have hg_cont : Continuous g := by
    dsimp only [g]
    exact ((continuous_const.mul (nivenPolyR n).continuous).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
  have hint_eq : ∫ x in (0 : ℝ)..1, g x = (a : ℝ) * F.eval 1 - (b : ℝ) * F.eval 0 := by
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hH_deriv x) (hg_cont.intervalIntegrable 0 1)
    rw [hftc]
    simp only [H, mul_one, mul_zero, Real.exp_zero]
    rw [hexp_eq, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hb_pos.ne')]
  -- Step 1: `F(0)` and `F(1)` are exact integers!
  have hF_int : ∀ x : ℝ, (∀ j : ℕ, ∃ m : ℤ, (Polynomial.derivative^[j] (nivenPolyR n)).eval x = (m : ℝ)) →
      ∃ M : ℤ, F.eval x = (M : ℝ) := by
    intro x hx
    choose m hm using hx
    refine ⟨∑ j ∈ Finset.range (2 * n + 1), (-1 : ℤ) ^ j * (k : ℤ) ^ (2 * n - j) * m j, ?_⟩
    simp only [F, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hm j]
  obtain ⟨M₀, hM₀⟩ := hF_int 0 (exists_int_iterate_derivative_nivenPolyR_zero n)
  obtain ⟨M₁, hM₁⟩ := hF_int 1 (exists_int_iterate_derivative_nivenPolyR_one n)
  have hint_int : ∫ x in (0 : ℝ)..1, g x = (((a : ℤ) * M₁ - (b : ℤ) * M₀ : ℤ) : ℝ) := by
    rw [hint_eq, hM₁, hM₀]; push_cast; rfl
  -- Step 2: `0 < ∫_0^1 g x`
  have hint_pos : 0 < ∫ x in (0 : ℝ)..1, g x := by
    refine intervalIntegral.integral_pos zero_lt_one hg_cont.continuousOn ?_ ?_
    · intro x hx
      dsimp only [g]
      rw [nivenPolyR_eval]
      have hx0 : 0 ≤ x := hx.1.le
      have hx1 : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
      have hexp : 0 ≤ Real.exp ((k : ℝ) * x) := (Real.exp_pos _).le
      positivity
    · refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
      dsimp only [g]
      rw [nivenPolyR_eval]
      have hbR : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr hb_pos
      have hkR : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
      have h12 : (0 : ℝ) < 1 - 1 / 2 := by norm_num
      have hexp : 0 < Real.exp ((k : ℝ) * (1 / 2)) := Real.exp_pos _
      positivity
  -- Step 3: `∫_0^1 g x ≤ (b * k * e^k) * (k^2)^n / n! < 1`
  have hint_le :
      ∫ x in (0 : ℝ)..1, g x ≤
        ((b : ℝ) * (k : ℝ) * Real.exp (k : ℝ)) * ((k : ℝ) ^ 2) ^ n / (n ! : ℝ) := by
    have hconst :
        ∫ _x in (0 : ℝ)..1, (((b : ℝ) * (k : ℝ) * Real.exp (k : ℝ)) * ((k : ℝ) ^ 2) ^ n / (n ! : ℝ)) =
          ((b : ℝ) * (k : ℝ) * Real.exp (k : ℝ)) * ((k : ℝ) ^ 2) ^ n / (n ! : ℝ) := by simp
    rw [← hconst]
    refine intervalIntegral.integral_mono_on zero_le_one (hg_cont.intervalIntegrable 0 1)
      intervalIntegrable_const fun x hx => ?_
    dsimp only [g]
    rw [nivenPolyR_eval]
    have hxn : x ^ n ≤ 1 := pow_le_one₀ hx.1 hx.2
    have h1xn : (1 - x) ^ n ≤ 1 := pow_le_one₀ (sub_nonneg.mpr hx.2) (by linarith [hx.1])
    have hprod_le : x ^ n * (1 - x) ^ n ≤ 1 := by
      have : 0 ≤ x ^ n := pow_nonneg hx.1 n
      have : 0 ≤ (1 - x) ^ n := pow_nonneg (sub_nonneg.mpr hx.2) n
      nlinarith
    have hdiv_le : x ^ n * (1 - x) ^ n / (n ! : ℝ) ≤ 1 / (n ! : ℝ) :=
      div_le_div_of_nonneg_right hprod_le (Nat.cast_nonneg _)
    have hexp_le : Real.exp ((k : ℝ) * x) ≤ Real.exp (k : ℝ) := by
      refine Real.exp_le_exp.mpr ?_
      have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      nlinarith [hx.2]
    have hc_nn : 0 ≤ (b : ℝ) * (k : ℝ) ^ (2 * n + 1) := by positivity
    have hf_nn : 0 ≤ x ^ n * (1 - x) ^ n / (n ! : ℝ) := by
      have : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
      have : 0 ≤ x := hx.1
      positivity
    calc (b : ℝ) * (k : ℝ) ^ (2 * n + 1) * (x ^ n * (1 - x) ^ n / (n ! : ℝ)) * Real.exp ((k : ℝ) * x)
        ≤ (b : ℝ) * (k : ℝ) ^ (2 * n + 1) * (x ^ n * (1 - x) ^ n / (n ! : ℝ)) * Real.exp (k : ℝ) :=
          mul_le_mul_of_nonneg_left hexp_le (mul_nonneg hc_nn hf_nn)
      _ ≤ (b : ℝ) * (k : ℝ) ^ (2 * n + 1) * (1 / (n ! : ℝ)) * Real.exp (k : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdiv_le hc_nn) (Real.exp_pos _).le
      _ = ((b : ℝ) * (k : ℝ) * Real.exp (k : ℝ)) * ((k : ℝ) ^ 2) ^ n / (n ! : ℝ) := by
          rw [pow_succ, pow_mul]; ring
  exact not_int_between_zero_and_one ((a : ℤ) * M₁ - (b : ℤ) * M₀) (hint_int ▸ hint_pos)
    ((hint_int ▸ hint_le).trans_lt hn_small)

/-- **UNCONDITIONAL HERMITE–NIVEN IRRATIONALITY OF `e^r` FOR EVERY NONZERO RATIONAL `r : ℚ`
(`0` ASSUMPTIONS!)**: `∀ r : ℚ, r ≠ 0 → Irrational (Real.exp (r : ℝ))`. -/
theorem irrational_exp_rat {r : ℚ} (hr : r ≠ 0) : Irrational (Real.exp (r : ℝ)) := by
  rintro ⟨q, hq⟩
  have hnum_ne : r.num ≠ 0 := Rat.num_ne_zero.mpr hr
  have hk_pos : 1 ≤ r.num.natAbs := Int.natAbs_pos.mpr hnum_ne
  have hden_ne : (r.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr r.den_nz
  rcases lt_or_gt_of_ne hnum_ne with hneg | hpos
  · -- `r.num < 0`: `(-r) * r.den = r.num.natAbs ≥ 1`
    have hq_ne : q ≠ 0 := by
      intro h0
      rw [h0, Rat.cast_zero] at hq
      exact (Real.exp_pos _).ne hq
    have hr_mul : (r.den : ℝ) * (-(r : ℝ)) = (r.num.natAbs : ℝ) := by
      have h1 : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by exact_mod_cast (Rat.num_div_den r).symm
      rw [h1]
      have hnum_eq : -(r.num : ℝ) = (r.num.natAbs : ℝ) := by
        have h : -r.num = (r.num.natAbs : ℤ) := by omega
        have h' := congrArg (Int.cast (R := ℝ)) h
        simpa using h'
      field_simp [hden_ne]
      exact hnum_eq
    apply irrational_exp_nat_pos hk_pos
    refine ⟨(q⁻¹) ^ r.den, ?_⟩
    rw [← hr_mul, Real.exp_nat_mul, Real.exp_neg, ← hq]
    push_cast
    rfl
  · -- `0 < r.num`: `r * r.den = r.num.natAbs ≥ 1`
    have hr_mul : (r.den : ℝ) * (r : ℝ) = (r.num.natAbs : ℝ) := by
      have h1 : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := by exact_mod_cast (Rat.num_div_den r).symm
      rw [h1]
      have hnum_eq : (r.num : ℝ) = (r.num.natAbs : ℝ) := by
        have h : r.num = (r.num.natAbs : ℤ) := by omega
        have h' := congrArg (Int.cast (R := ℝ)) h
        simpa using h'
      field_simp [hden_ne]
      exact hnum_eq
    apply irrational_exp_nat_pos hk_pos
    refine ⟨q ^ r.den, ?_⟩
    rw [← hr_mul, Real.exp_nat_mul, ← hq]
    push_cast
    rfl

/-- **COROLLARY (`0` ASSUMPTIONS!)**: Euler's number `e = Real.exp 1` is irrational! -/
theorem irrational_exp_one : Irrational (Real.exp 1) := by
  simpa using irrational_exp_rat (r := 1) one_ne_zero

end NivenIrrationality

/-! ## Section 4: Master Unconditional Stage 9 Special Values Theorem -/

/-- **MASTER UNCONDITIONAL STAGE 9 SPECIAL VALUES & IRRATIONALITY THEOREM (`0` ASSUMPTIONS!)**:
simultaneously packages:
1. Exact negative-integer values `L(1 - k, χ) = -B_{k, χ} / k` for every `q ≥ 1`, non-principal
   `χ ≠ 1`, and `k ≥ 1`;
2. The complex-to-$p$-adic Kubota–Leopoldt interpolation bridge matching `kubotaLeopoldtZeta`
   with `(1 - p^k) * riemannZeta (1 - (k + 1))`;
3. The general Euler–Dirichlet positive-integer formula for `L(k, χ)` (`χ` primitive, `χ ≠ 1`,
   `χ(-1) = (-1)^k`) together with the iconic evaluations `L(1, χ₋₄) = π/4`, `L(3, χ₋₄) = π³/32`,
   `L(1, χ₋₃) = π/(3√3)`, `ζ(0) = -1/2`, `ζ(-1) = -1/12`, `ζ(-3) = 1/120`, `ζ(4) = π⁴/90`,
   and `ζ(6) = π⁶/945`;
4. Unconditional irrationality of `π²`, `π`, and `e^r` for every nonzero rational `r : ℚ`. -/
theorem stage9_specialValues_unconditional :
    (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ k : ℕ, 1 ≤ k →
      DirichletCharacter.LFunction χ (1 - (k : ℂ)) = -(genBernoulli χ k) / (k : ℂ)) ∧
    (∀ (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (c : ℕ), 2 ≤ c → ∀ (hc : ¬ p ∣ c) (i k : ℕ),
      1 ≤ k → k ≡ i [MOD (p - 1)] →
      ∃ r : ℚ,
        Stage7PadicLFunction.kubotaLeopoldtZeta p hp2 c hc i (k : ℤ_[p]) = (r : ℚ_[p]) ∧
        (1 - (p : ℂ) ^ k) * riemannZeta (1 - ((k + 1 : ℕ) : ℂ)) = (r : ℂ) ∧
        r = (1 - (p : ℚ) ^ k) * (-bernoulli (k + 1) / ((k + 1 : ℕ) : ℚ))) ∧
    (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 →
      ∀ k : ℕ, 1 ≤ k → χ (-1 : ZMod q) = (-1 : ℂ) ^ k →
      DirichletCharacter.LFunction χ (k : ℂ) =
        -(χ (-1 : ZMod q) * gaussSum χ ZMod.stdAddChar / (2 * ((k ! : ℕ) : ℂ))) *
          (2 * (Real.pi : ℂ) * Complex.I / (q : ℂ)) ^ k *
          genBernoulli χ⁻¹ k) ∧
    (DirichletCharacter.LFunction chi4 1 = (Real.pi : ℂ) / 4 ∧
      DirichletCharacter.LFunction chi4 3 = (Real.pi : ℂ) ^ 3 / 32 ∧
      DirichletCharacter.LFunction chi3 1 = (Real.pi : ℂ) / (3 * (Real.sqrt 3 : ℂ)) ∧
      riemannZeta 0 = -1 / 2 ∧
      riemannZeta (-1) = -1 / 12 ∧
      riemannZeta (-3) = 1 / 120 ∧
      riemannZeta 4 = (Real.pi : ℂ) ^ 4 / 90 ∧
      riemannZeta 6 = (Real.pi : ℂ) ^ 6 / 945) ∧
    (Irrational (Real.pi ^ 2) ∧ Irrational Real.pi ∧
      ∀ r : ℚ, r ≠ 0 → Irrational (Real.exp (r : ℝ))) :=
  ⟨fun _ _ _ hχ _ hk => LFunction_one_sub_nat_eq_genBernoulli hχ hk,
   fun p _ hp2 _ hc2 hc i _ hk hki =>
     kubotaLeopoldtZeta_eq_riemannZeta_one_sub p hp2 hc2 hc i hk hki,
   fun _ _ _ hprim hχ _ hk hpar => LFunction_pos_nat_eq_genBernoulli hprim hχ hk hpar,
   ⟨LFunction_one_chi4_eq, LFunction_three_chi4_eq, LFunction_one_chi3_eq,
    riemannZeta_zero_eq, riemannZeta_neg_one_eq, riemannZeta_neg_three_eq,
    riemannZeta_four_eq, riemannZeta_six_eq⟩,
   ⟨irrational_pi_sq, irrational_pi, fun _ hr => irrational_exp_rat hr⟩⟩

end RHDirect.Stage9SpecialValues
