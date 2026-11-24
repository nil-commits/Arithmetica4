import RHDirect.Interfaces
import RHDirect.LocalLanglandsCore
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.NumberTheory.ModularForms.LFunction
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# RHDirect.Stage5ModularHecke

Concrete Hecke Algebra, Diamond Operators, Slash-Action Fourier Compatibility,
Normalized Eigenform Multiplicativity, Exact Degree-2 `GL_2` Euler Product,
Ramanujan–Petersson Equivalence, and Unramified `GL_2` Satake Weil–Deligne Bridge
in pure Mathlib `v4.33.1`.

## Main Results

1. **Concrete Hecke Operators `heckeOp k χ n` on Formal `q`-Expansions & Full Hecke Algebra**:
   - `(heckeOp k χ n f) m = ∑ d ∈ (Nat.gcd m n).divisors, χ d * d ^ (k - 1) * f (m * n / d ^ 2)`
     packaged both as a function and a `ℂ`-linear endomorphism `heckeOpLin k χ n : Module.End ℂ (ℕ → ℂ)`.
   - Unconditional identities:
     - `heckeOp_one : heckeOp k χ 1 f = f`
     - `heckeOp_mul_of_coprime : Nat.Coprime m n → heckeOp k χ m (heckeOp k χ n f) = heckeOp k χ (m * n) f`
     - `heckeOp_prime_pow_recurrence : p.Prime → 1 ≤ r → heckeOp k χ (p ^ (r + 1)) f = heckeOp k χ p (heckeOp k χ (p ^ r) f) - (χ p * p ^ (k - 1)) • heckeOp k χ (p ^ (r - 1)) f`
     - `heckeOp_comm : heckeOp k χ m (heckeOp k χ n f) = heckeOp k χ n (heckeOp k χ m f)` for ALL `m, n : ℕ`.
2. **Diamond Operators `⟨d⟩`, Nebentypus Eigenspaces & Slash-Action Hecke Compatibility**:
   - Constructive lift `gamma0Lift N d ∈ CongruenceSubgroup.Gamma0 N` surjecting onto `(ZMod N)ˣ`
     under `CongruenceSubgroup.Gamma0Map N`.
   - Concrete diamond operator `diamondOp N k d` on `Γ₁(N)`-invariant functions on `UpperHalfPlane`,
     proving lift-independence (`diamondOp_eq_slash_of_gamma0`), multiplicativity (`diamondOp_mul`),
     commutativity (`diamondOp_comm`), and exact characterization of Nebentypus eigenspaces
     (`hasNebentypus_iff_diamondOp`).
   - Concrete upper-triangular Hecke coset matrices `heckeMat a b d : GL (Fin 2) ℝ`, concrete
     slash-action Hecke operator `slashHeckeOp k χ n` on `UpperHalfPlane → ℂ`, and the **exact
     Fourier-coefficient action theorem** (`slashHeckeOp_hasSum_qExpansion` and
     `modularForm_slashHeckeOp_hasSum_qExpansion` on Mathlib's `ModularForm` / `CuspForm`).
3. **Normalized Hecke Eigenforms ⇒ Exact `GL_2` Multiplicativity & Prime-Power Recurrence**:
   - `eigenvalue_eq_coeff`: `lam n = f n` for all `n ≥ 1`.
   - `eigenform_mul_eq_sum`: `f m * f n = ∑ d ∈ (Nat.gcd m n).divisors, χ d * d ^ (k - 1) * f (m * n / d ^ 2)`.
   - `eigenform_isMultiplicative`: `Nat.Coprime m n → f (m * n) = f m * f n` (plus Mathlib
     `ArithmeticFunction.IsMultiplicative` bridge `eigenform_arithFun_isMultiplicative`).
   - `eigenform_prime_pow_recurrence`: `f (p ^ (r + 2)) = f p * f (p ^ (r + 1)) - χ p * p ^ (k - 1) * f (p ^ r)`.
4. **Exact Prime-Power Generating Series & Satake Parameters `(α_p, β_p)`**:
   - Formal power series identity `primePow_eulerPoly_mul_powerSeries = 1` in `PowerSeries ℂ`.
   - Unconditional existence of Satake pairs `IsSatakePair a_p c_p α β` (`exists_satake_pair`),
     factorization `1 - a_p * z + c_p * z ^ 2 = (1 - α * z) * (1 - β * z)`, and exact symmetric
     power sum formula `eigenform_prime_pow_eq_satake_sum`.
   - Convergent generating-series identity `tsum_primePow_eq_inv_eulerPoly` and
     `tsum_primePow_eq_inv_satake` (both unconditionally from summability and from `‖α z‖, ‖β z‖ < 1`).
5. **Unconditional Convergence & Exact Degree-2 `GL_2` Euler Product**:
   - Master degree-2 Euler product `eigenform_LSeries_eulerProduct` (and finite-prime-product limit
     `eigenform_LSeries_eulerProduct_tendsto` and Satake form `eigenform_LSeries_eulerProduct_satake`)
     directly on Mathlib's `LSeries f s` whenever `LSeriesSummable f s`.
   - Unconditional convergence & Euler product from polynomial / Hecke / Ramanujan–Deligne bounds
     (`eigenform_LSeries_eulerProduct_of_poly_bound`), plus direct bridge to Mathlib's
     `CuspForm` and `ModularForm.L` (`cuspForm_eigenform_L_eulerProduct` on `Re(s) > k / 2 + 1`).
6. **Ramanujan–Petersson Equivalence & Unramified `GL_2` Satake Weil–Deligne Bridge**:
   - Exact Ramanujan–Petersson equivalence `ramanujan_petersson_iff` (and `ramanujan_petersson_iff_of_selfAdjoint`,
     `ramanujan_petersson_iff_real`): for unitary `χ(p)` (`Nat.Coprime p N`),
     `‖α_p‖ = p ^ ((k - 1) / 2) ∧ ‖β_p‖ = p ^ ((k - 1) / 2) ↔ ‖a_p‖ ≤ 2 * p ^ ((k - 1) / 2) ∧ star a_p = star (χ p) * a_p`.
   - Concrete unramified 2-dimensional Weil–Deligne representation `satakeWDRep W α β` in
     `RHDirect.LocalLanglands.WDRep W 2`, proving exact Frobenius trace `a_p`, determinant
     `χ(p) * p ^ (k - 1)`, characteristic polynomial `X ^ 2 - C a_p * X + C c_p`, matching local
     Euler factor, and pure weight `k - 1` / temperedness under Ramanujan–Petersson.
7. **Deligne Divisor Bound, Exact Eigenform Characterization & Non-Vacuous Eisenstein Witness**:
   - `divisors_card_le_two_mul_sqrt` and `eigenform_deligne_divisor_bound`
     (`‖f n‖ ≤ d(n) · n^((k - 1)/2)` from local Satake purity), yielding unconditional
     `LSeries` convergence and exact degree-2 Euler product on `Re(s) > k / 2 + 1`
     (`eigenform_LSeries_eulerProduct_of_ramanujan_petersson`).
   - Exact converse characterization `isNormalizedHeckeEigenform_of_mult_and_prime_pow` and
     concrete non-vacuous Eisenstein eigenform witness `eisensteinCoeff k χ`
     (`isNormalizedHeckeEigenform_eisensteinCoeff`, `eisensteinCoeff_isSatakePair`).

Zero `sorry`, zero custom `axiom`s.
-/

noncomputable section

open Complex Finset Matrix Polynomial PowerSeries RHDirect

namespace RHDirect.Stage5ModularHecke

/-! ## Section 1: Concrete Hecke Operators on Formal `q`-Expansions & Full Hecke Algebra -/

section HeckeAlgebra

/-- The multiplicative Hecke weight function `ψ(d) = χ(d) · d^(k - 1)`. -/
def heckeWeight {N : ℕ} (k : ℕ) (χ : DirichletCharacter ℂ N) (d : ℕ) : ℂ :=
  χ (d : ZMod N) * (d : ℂ) ^ (k - 1)

@[simp]
theorem heckeWeight_one {N : ℕ} (k : ℕ) (χ : DirichletCharacter ℂ N) :
    heckeWeight k χ 1 = 1 := by
  simp [heckeWeight]

theorem heckeWeight_mul {N : ℕ} (k : ℕ) (χ : DirichletCharacter ℂ N) (a b : ℕ) :
    heckeWeight k χ (a * b) = heckeWeight k χ a * heckeWeight k χ b := by
  simp only [heckeWeight, Nat.cast_mul, map_mul, mul_pow]
  ring

theorem heckeWeight_pow {N : ℕ} (k : ℕ) (χ : DirichletCharacter ℂ N) (a r : ℕ) :
    heckeWeight k χ (a ^ r) = (heckeWeight k χ a) ^ r := by
  induction r with
  | zero => simp
  | succ r ih => rw [pow_succ, heckeWeight_mul, ih, pow_succ]

/-- Concrete Hecke operator `T_n` of weight `k` and Nebentypus `χ` acting on formal `q`-expansions
`f : ℕ → ℂ`:
`(heckeOp k χ n f) m = ∑ d ∣ gcd(m, n), χ(d) · d^(k - 1) · f(m * n / d²)`. -/
def heckeOp {N : ℕ} (k : ℕ) (χ : DirichletCharacter ℂ N) (n : ℕ) (f : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ d ∈ (Nat.gcd m n).divisors, heckeWeight k χ d * f (m * n / d ^ 2)

theorem heckeOp_apply {N : ℕ} (k : ℕ) (χ : DirichletCharacter ℂ N) (n : ℕ)
    (f : ℕ → ℂ) (m : ℕ) :
    heckeOp k χ n f m =
      ∑ d ∈ (Nat.gcd m n).divisors, χ (d : ZMod N) * (d : ℂ) ^ (k - 1) * f (m * n / d ^ 2) :=
  rfl

theorem heckeOp_zero_fun {N : ℕ} (k : ℕ) (χ : DirichletCharacter ℂ N) (n : ℕ) :
    heckeOp k χ n 0 = 0 := by
  funext m
  simp [heckeOp]

theorem heckeOp_add {N : ℕ} (k : ℕ) (χ : DirichletCharacter ℂ N) (n : ℕ) (f g : ℕ → ℂ) :
    heckeOp k χ n (f + g) = heckeOp k χ n f + heckeOp k χ n g := by
  funext m
  simp only [heckeOp, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem heckeOp_sub {N : ℕ} (k : ℕ) (χ : DirichletCharacter ℂ N) (n : ℕ) (f g : ℕ → ℂ) :
    heckeOp k χ n (f - g) = heckeOp k χ n f - heckeOp k χ n g := by
  funext m
  simp only [heckeOp, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem heckeOp_smul {N : ℕ} (k : ℕ) (χ : DirichletCharacter ℂ N) (n : ℕ) (c : ℂ) (f : ℕ → ℂ) :
    heckeOp k χ n (c • f) = c • heckeOp k χ n f := by
  funext m
  simp only [heckeOp, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

/-- The concrete Hecke operator `T_n` packaged as a `ℂ`-linear endomorphism of `ℕ → ℂ`. -/
def heckeOpLin {N : ℕ} (k : ℕ) (χ : DirichletCharacter ℂ N) (n : ℕ) : Module.End ℂ (ℕ → ℂ) where
  toFun := heckeOp k χ n
  map_add' := heckeOp_add k χ n
  map_smul' := heckeOp_smul k χ n

@[simp]
theorem heckeOpLin_apply {N : ℕ} (k : ℕ) (χ : DirichletCharacter ℂ N) (n : ℕ) (f : ℕ → ℂ) :
    heckeOpLin k χ n f = heckeOp k χ n f :=
  rfl

/-- `T_1 = id` unconditionally. -/
theorem heckeOp_one {N : ℕ} (k : ℕ) (χ : DirichletCharacter ℂ N) (f : ℕ → ℂ) :
    heckeOp k χ 1 f = f := by
  funext m
  simp [heckeOp]

theorem heckeOpLin_one {N : ℕ} (k : ℕ) (χ : DirichletCharacter ℂ N) :
    heckeOpLin k χ 1 = 1 := by
  ext f m
  exact congrFun (heckeOp_one k χ f) m

/-- Evaluating `T_n f` at `m = 1` recovers the `n`-th Fourier coefficient `f n` for every `n ≥ 1`. -/
theorem heckeOp_apply_one {N : ℕ} (k : ℕ) (χ : DirichletCharacter ℂ N) {n : ℕ} (hn : 1 ≤ n)
    (f : ℕ → ℂ) :
    heckeOp k χ n f 1 = f n := by
  have _ : n ≠ 0 := by omega
  simp [heckeOp]

/-- Exact constant term `(T_n f) 0 = (∑ d ∣ n, χ(d) d^(k-1)) * f 0`. -/
theorem heckeOp_apply_zero {N : ℕ} (k : ℕ) (χ : DirichletCharacter ℂ N) (n : ℕ) (f : ℕ → ℂ) :
    heckeOp k χ n f 0 = (∑ d ∈ n.divisors, heckeWeight k χ d) * f 0 := by
  simp [heckeOp, Finset.sum_mul]

/-! ### Multiplicativity `T_m ∘ T_n = T_{m * n}` for Coprime `m, n` -/

private theorem div_sq_mul_div_sq_eq {M m n d₁ d₂ : ℕ}
    (h1M : d₁ ∣ M) (h1m : d₁ ∣ m) (h2M : d₂ ∣ M) (h2n : d₂ ∣ n)
    (hcop : Nat.Coprime d₁ d₂) (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) :
    M * m / d₁ ^ 2 * n / d₂ ^ 2 = M * (m * n) / (d₁ * d₂) ^ 2 := by
  have h12M : d₁ * d₂ ∣ M := hcop.mul_dvd_of_dvd_of_dvd h1M h2M
  rcases h12M with ⟨qM, rfl⟩
  rcases h1m with ⟨qm, rfl⟩
  rcases h2n with ⟨qn, rfl⟩
  have hd12 : d₁ ^ 2 ≠ 0 := pow_ne_zero 2 hd₁
  have hd22 : d₂ ^ 2 ≠ 0 := pow_ne_zero 2 hd₂
  have hd12p : (d₁ * d₂) ^ 2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero hd₁ hd₂)
  have hL1 : d₁ * d₂ * qM * (d₁ * qm) = d₁ ^ 2 * (d₂ * qM * qm) := by ring
  have hL2 : d₂ * qM * qm * (d₂ * qn) = d₂ ^ 2 * (qM * qm * qn) := by ring
  have hR : d₁ * d₂ * qM * (d₁ * qm * (d₂ * qn)) = (d₁ * d₂) ^ 2 * (qM * qm * qn) := by ring
  rw [hL1, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd12),
      hL2, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd22),
      hR, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd12p)]

private theorem gcd_div_sq_eq {M m n d₁ : ℕ}
    (h1M : d₁ ∣ M) (h1m : d₁ ∣ m) (hd₁ : d₁ ≠ 0) (hmn : Nat.Coprime m n) :
    Nat.gcd (M * m / d₁ ^ 2) n = Nat.gcd M n := by
  rcases h1M with ⟨qM, rfl⟩
  rcases h1m with ⟨qm, rfl⟩
  have hcop_d1 : Nat.Coprime d₁ n := hmn.coprime_dvd_left (dvd_mul_right d₁ qm)
  have hcop_qm : Nat.Coprime qm n := hmn.coprime_dvd_left (dvd_mul_left qm d₁)
  have harg : d₁ * qM * (d₁ * qm) / d₁ ^ 2 = qM * qm := by
    have h1 : d₁ * qM * (d₁ * qm) = d₁ ^ 2 * (qM * qm) := by ring
    rw [h1, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (pow_ne_zero 2 hd₁))]
  rw [harg, hcop_qm.gcd_mul_right_cancel qM, hcop_d1.gcd_mul_left_cancel qM]

private theorem gcd_mul_right_of_coprime (M m n : ℕ) (hmn : Nat.Coprime m n) :
    Nat.gcd M (m * n) = Nat.gcd M m * Nat.gcd M n :=
  hmn.gcd_mul M

/-- Exact Hecke multiplicativity for coprime indices: `Nat.Coprime m n → T_m (T_n f) = T_{m * n} f`. -/
theorem heckeOp_mul_of_coprime {N : ℕ} (k : ℕ) (χ : DirichletCharacter ℂ N)
    {m n : ℕ} (hmn : Nat.Coprime m n) (f : ℕ → ℂ) :
    heckeOp k χ m (heckeOp k χ n f) = heckeOp k χ (m * n) f := by
  by_cases hm0 : m = 0
  · subst hm0
    have hn1 : n = 1 := (Nat.coprime_zero_left n).mp hmn
    subst hn1
    simp [heckeOp_one]
  by_cases hn0 : n = 0
  · subst hn0
    have hm1 : m = 1 := (Nat.coprime_zero_right m).mp hmn
    subst hm1
    simp [heckeOp_one]
  funext M
  simp only [heckeOp]
  have hstep1 :
      ∑ d₁ ∈ (Nat.gcd M m).divisors,
          heckeWeight k χ d₁ *
            ∑ d₂ ∈ (Nat.gcd (M * m / d₁ ^ 2) n).divisors,
              heckeWeight k χ d₂ * f (M * m / d₁ ^ 2 * n / d₂ ^ 2) =
      ∑ p ∈ (Nat.gcd M m).divisors ×ˢ (Nat.gcd M n).divisors,
          heckeWeight k χ (p.1 * p.2) * f (M * (m * n) / (p.1 * p.2) ^ 2) := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun d₁ hd₁ => ?_
    have hd₁_dvd := (Nat.mem_divisors.mp hd₁).1
    have hd₁_ne : d₁ ≠ 0 := ne_of_gt (Nat.pos_of_dvd_of_pos hd₁_dvd
      (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd₁).2))
    have h1M : d₁ ∣ M := dvd_trans hd₁_dvd (Nat.gcd_dvd_left M m)
    have h1m : d₁ ∣ m := dvd_trans hd₁_dvd (Nat.gcd_dvd_right M m)
    rw [gcd_div_sq_eq h1M h1m hd₁_ne hmn, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d₂ hd₂ => ?_
    have hd₂_dvd := (Nat.mem_divisors.mp hd₂).1
    have hd₂_ne : d₂ ≠ 0 := ne_of_gt (Nat.pos_of_dvd_of_pos hd₂_dvd
      (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd₂).2))
    have h2M : d₂ ∣ M := dvd_trans hd₂_dvd (Nat.gcd_dvd_left M n)
    have h2n : d₂ ∣ n := dvd_trans hd₂_dvd (Nat.gcd_dvd_right M n)
    have hcop12 : Nat.Coprime d₁ d₂ := (hmn.coprime_dvd_left h1m).coprime_dvd_right h2n
    rw [← mul_assoc, ← heckeWeight_mul, div_sq_mul_div_sq_eq h1M h1m h2M h2n hcop12 hd₁_ne hd₂_ne]
  rw [hstep1]
  have hgcd_cop : Nat.Coprime (Nat.gcd M m) (Nat.gcd M n) :=
    (hmn.coprime_dvd_left (Nat.gcd_dvd_right M m)).coprime_dvd_right (Nat.gcd_dvd_right M n)
  rw [gcd_mul_right_of_coprime M m n hmn]
  refine Finset.sum_nbij' (fun p => p.1 * p.2)
    (fun d => (Nat.gcd d (Nat.gcd M m), Nat.gcd d (Nat.gcd M n))) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
    rcases Nat.mem_divisors.mp hp1 with ⟨h1, h1ne⟩
    rcases Nat.mem_divisors.mp hp2 with ⟨h2, h2ne⟩
    exact Nat.mem_divisors.mpr ⟨mul_dvd_mul h1 h2, mul_ne_zero h1ne h2ne⟩
  · intro d hd
    rcases Nat.mem_divisors.mp hd with ⟨_, hne⟩
    have hne1 : Nat.gcd M m ≠ 0 := left_ne_zero_of_mul hne
    have hne2 : Nat.gcd M n ≠ 0 := right_ne_zero_of_mul hne
    exact Finset.mem_product.mpr
      ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hne1⟩,
       Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hne2⟩⟩
  · intro p hp
    rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
    have h1 : p.1 ∣ Nat.gcd M m := (Nat.mem_divisors.mp hp1).1
    have h2 : p.2 ∣ Nat.gcd M n := (Nat.mem_divisors.mp hp2).1
    have hcop_p2_a : Nat.Coprime p.2 (Nat.gcd M m) :=
      (hgcd_cop.coprime_dvd_right h2).symm
    have hcop_p1_b : Nat.Coprime p.1 (Nat.gcd M n) :=
      hgcd_cop.coprime_dvd_left h1
    ext
    · dsimp only
      rw [hcop_p2_a.gcd_mul_right_cancel p.1, Nat.gcd_eq_left h1]
    · dsimp only
      rw [hcop_p1_b.gcd_mul_left_cancel p.2, Nat.gcd_eq_left h2]
  · intro d hd
    have hd_dvd : d ∣ Nat.gcd M m * Nat.gcd M n := (Nat.mem_divisors.mp hd).1
    rw [← gcd_mul_right_of_coprime d (Nat.gcd M m) (Nat.gcd M n) hgcd_cop,
        Nat.gcd_eq_left hd_dvd]
  · intro p _
    rfl

theorem heckeOpLin_mul_of_coprime {N : ℕ} (k : ℕ) (χ : DirichletCharacter ℂ N)
    {m n : ℕ} (hmn : Nat.Coprime m n) :
    heckeOpLin k χ m * heckeOpLin k χ n = heckeOpLin k χ (m * n) := by
  ext f M
  exact congrFun (heckeOp_mul_of_coprime k χ hmn f) M

/-! ### Prime-Power Hecke Recurrence `T_{p^{r+1}} = T_p ∘ T_{p^r} - χ(p) p^{k-1} T_{p^{r-1}}` -/

private theorem sum_divisors_prime_pow {p : ℕ} (hp : p.Prime) (a : ℕ) (g : ℕ → ℂ) :
    ∑ d ∈ (p ^ a).divisors, g d = ∑ j ∈ Finset.range (a + 1), g (p ^ j) := by
  rw [Nat.divisors_prime_pow hp, Finset.sum_map]
  rfl

private theorem gcd_prime_pow_eq {p : ℕ} (hp : p.Prime) {M : ℕ} (hM : M ≠ 0) (s : ℕ) :
    Nat.gcd M (p ^ s) = p ^ min (M.factorization p) s := by
  apply Nat.dvd_antisymm
  · have hdvd : Nat.gcd M (p ^ s) ∣ p ^ s := Nat.gcd_dvd_right M (p ^ s)
    rcases (Nat.dvd_prime_pow hp).mp hdvd with ⟨j, hjs, hj⟩
    rw [hj]
    apply pow_dvd_pow p
    refine le_min ?_ hjs
    have hjpM : p ^ j ∣ M := hj ▸ Nat.gcd_dvd_left M (p ^ s)
    exact (hp.pow_dvd_iff_le_factorization hM).mp hjpM
  · exact Nat.dvd_gcd
      ((hp.pow_dvd_iff_le_factorization hM).mpr (min_le_left _ _))
      (pow_dvd_pow p (min_le_right _ _))

private theorem heckeOp_prime_pow_eval_ne_zero {N : ℕ} (k : ℕ) (χ : DirichletCharacter ℂ N)
    {p : ℕ} (hp : p.Prime) {M : ℕ} (hM : M ≠ 0) (s : ℕ) (f : ℕ → ℂ) :
    heckeOp k χ (p ^ s) f M =
      ∑ j ∈ Finset.range (min (M.factorization p) s + 1),
        (heckeWeight k χ p) ^ j * f (M * p ^ s / p ^ (2 * j)) := by
  simp only [heckeOp, gcd_prime_pow_eq hp hM s, sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [heckeWeight_pow, ← pow_mul, mul_comm j 2]

/-- Exact prime-power Hecke recurrence for every prime `p` and `r ≥ 1`:
`T_{p^{r+1}} f = T_p (T_{p^r} f) - (χ(p) · p^(k - 1)) • T_{p^{r-1}} f`. -/
theorem heckeOp_prime_pow_recurrence {N : ℕ} (k : ℕ) (χ : DirichletCharacter ℂ N)
    {p : ℕ} (hp : p.Prime) {r : ℕ} (hr : 1 ≤ r) (f : ℕ → ℂ) :
    heckeOp k χ (p ^ (r + 1)) f =
      heckeOp k χ p (heckeOp k χ (p ^ r) f) -
        (χ (p : ZMod N) * (p : ℂ) ^ (k - 1)) • heckeOp k χ (p ^ (r - 1)) f := by
  have hgoal :
      heckeOp k χ (p ^ (r + 1)) f + heckeWeight k χ p • heckeOp k χ (p ^ (r - 1)) f =
        heckeOp k χ p (heckeOp k χ (p ^ r) f) := by
    funext M
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hM0 : M = 0
    · subst hM0
      have hr1 : r - 1 + 1 = r := by omega
      have hp_sum : ∑ d ∈ p.divisors, heckeWeight k χ d = 1 + heckeWeight k χ p := by
        rw [hp.divisors, Finset.sum_pair hp.ne_one.symm, heckeWeight_one]
      simp only [heckeOp_apply_zero, sum_divisors_prime_pow hp, hp_sum, heckeWeight_pow]
      have hsplit : ∀ m : ℕ,
          ∑ j ∈ Finset.range (m + 1), heckeWeight k χ p ^ j =
            1 + heckeWeight k χ p * ∑ j ∈ Finset.range m, heckeWeight k χ p ^ j := by
        intro m
        rw [Finset.sum_range_succ', pow_zero, add_comm]
        congr 1
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [pow_succ']
      rw [hsplit (r + 1), hsplit r, hr1]
      ring
    · have hp_pos : 0 < p := hp.pos
      have hp_ne : p ≠ 0 := hp.ne_zero
      by_cases hpdvd : p ∣ M
      · -- Case `p ∣ M` and `M ≠ 0`
        have hgcdMp : Nat.gcd M p = p := Nat.gcd_eq_right hpdvd
        have hTp : heckeOp k χ p (heckeOp k χ (p ^ r) f) M =
            heckeOp k χ (p ^ r) f (M * p) + heckeWeight k χ p * heckeOp k χ (p ^ r) f (M / p) := by
          simp only [heckeOp, hgcdMp]
          rw [show p = p ^ 1 from (pow_one p).symm, sum_divisors_prime_pow hp,
              Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one,
              heckeWeight_one, one_mul, one_pow, Nat.div_one,
              show M * p / p ^ 2 = M / p by
                rw [sq, Nat.mul_div_mul_right M p hp_pos]]
        rw [hTp]
        set v := M.factorization p with hv_def
        have hv1 : 1 ≤ v := (hp.dvd_iff_one_le_factorization hM0).mp hpdvd
        have hMp_ne : M * p ≠ 0 := mul_ne_zero hM0 hp_ne
        have hMdiv_ne : M / p ≠ 0 := by
          rcases hpdvd with ⟨q, hq⟩
          rw [hq, Nat.mul_div_cancel_left _ hp_pos]
          intro hq0
          exact hM0 (by simp [hq, hq0])
        have hvMp : (M * p).factorization p = v + 1 := by
          rw [Nat.factorization_mul hM0 hp_ne, Finsupp.add_apply, hp.factorization_self, hv_def]
        have hvMdiv : (M / p).factorization p = v - 1 := by
          rw [Nat.factorization_div hpdvd, Finsupp.tsub_apply, hp.factorization_self, hv_def]
        rw [heckeOp_prime_pow_eval_ne_zero k χ hp hM0 (r + 1) f,
            heckeOp_prime_pow_eval_ne_zero k χ hp hM0 (r - 1) f,
            heckeOp_prime_pow_eval_ne_zero k χ hp hMp_ne r f,
            heckeOp_prime_pow_eval_ne_zero k χ hp hMdiv_ne r f,
            hvMp, hvMdiv]
        set g : ℕ → ℂ := fun j => (heckeWeight k χ p) ^ j * f (M * p ^ (r + 1) / p ^ (2 * j))
        have hsum1 :
            ∑ j ∈ Finset.range (min v (r + 1) + 1),
                heckeWeight k χ p ^ j * f (M * p ^ (r + 1) / p ^ (2 * j)) =
              g 0 + ∑ i ∈ Finset.range (min v (r + 1)), g (i + 1) := by
          rw [Finset.sum_range_succ', add_comm]
        have hsum2 :
            heckeWeight k χ p *
              ∑ i ∈ Finset.range (min v (r - 1) + 1),
                heckeWeight k χ p ^ i * f (M * p ^ (r - 1) / p ^ (2 * i)) =
              ∑ i ∈ Finset.range (min (v + 1) r), g (i + 1) := by
          have hmin : min v (r - 1) + 1 = min (v + 1) r := by omega
          rw [hmin, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [g]
          have harg : M * p ^ (r - 1) / p ^ (2 * i) = M * p ^ (r + 1) / p ^ (2 * (i + 1)) := by
            have h1 : M * p ^ (r + 1) = M * p ^ (r - 1) * p ^ 2 := by
              rw [mul_assoc, ← pow_add]
              congr 2
              omega
            have h2 : p ^ (2 * (i + 1)) = p ^ (2 * i) * p ^ 2 := by
              rw [← pow_add, mul_add, mul_one]
            rw [h1, h2, Nat.mul_div_mul_right _ _ (pow_pos hp_pos 2)]
          rw [harg, ← mul_assoc, ← pow_succ']
        have hsum3 :
            ∑ j ∈ Finset.range (min (v + 1) r + 1),
                heckeWeight k χ p ^ j * f (M * p * p ^ r / p ^ (2 * j)) =
              g 0 + ∑ i ∈ Finset.range (min (v + 1) r), g (i + 1) := by
          rw [Finset.sum_range_succ', add_comm]
          have harg : M * p * p ^ r = M * p ^ (r + 1) := by
            rw [mul_assoc, pow_succ']
          simp only [g, harg]
        have hsum4 :
            heckeWeight k χ p *
              ∑ i ∈ Finset.range (min (v - 1) r + 1),
                heckeWeight k χ p ^ i * f (M / p * p ^ r / p ^ (2 * i)) =
              ∑ i ∈ Finset.range (min v (r + 1)), g (i + 1) := by
          have hmin : min (v - 1) r + 1 = min v (r + 1) := by omega
          rw [hmin, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [g]
          have harg : M / p * p ^ r / p ^ (2 * i) = M * p ^ (r + 1) / p ^ (2 * (i + 1)) := by
            rcases hpdvd with ⟨q, hq⟩
            rw [hq, Nat.mul_div_cancel_left _ hp_pos]
            have h1 : p * q * p ^ (r + 1) = q * p ^ r * p ^ 2 := by ring
            have h2 : p ^ (2 * (i + 1)) = p ^ (2 * i) * p ^ 2 := by
              rw [← pow_add, mul_add, mul_one]
            rw [h1, h2, Nat.mul_div_mul_right _ _ (pow_pos hp_pos 2)]
          rw [harg, ← mul_assoc, ← pow_succ']
        rw [hsum1, hsum2, hsum3, hsum4]
        ring
      · -- Case `¬ p ∣ M` and `M ≠ 0`
        have hv0 : M.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpdvd
        have hgcdMp : Nat.gcd M p = 1 := (hp.coprime_iff_not_dvd.mpr hpdvd).symm
        have hTp : heckeOp k χ p (heckeOp k χ (p ^ r) f) M = heckeOp k χ (p ^ r) f (M * p) := by
          simp [heckeOp, hgcdMp]
        rw [hTp]
        have hMp_ne : M * p ≠ 0 := mul_ne_zero hM0 hp_ne
        have hvMp : (M * p).factorization p = 1 := by
          rw [Nat.factorization_mul hM0 hp_ne, Finsupp.add_apply, hv0, zero_add,
              hp.factorization_self]
        rw [heckeOp_prime_pow_eval_ne_zero k χ hp hM0 (r + 1) f,
            heckeOp_prime_pow_eval_ne_zero k χ hp hM0 (r - 1) f,
            heckeOp_prime_pow_eval_ne_zero k χ hp hMp_ne r f,
            hv0, hvMp]
        have hmin1 : min 1 r = 1 := by omega
        simp only [Nat.zero_min, zero_add, hmin1, Finset.sum_range_succ, Finset.sum_range_zero,
          pow_zero, one_mul, mul_zero, Nat.div_one, pow_one, mul_one]
        have harg1 : M * p * p ^ r = M * p ^ (r + 1) := by rw [mul_assoc, pow_succ']
        have harg2 : M * p ^ (r + 1) / p ^ 2 = M * p ^ (r - 1) := by
          have h1 : M * p ^ (r + 1) = M * p ^ (r - 1) * p ^ 2 := by
            rw [mul_assoc, ← pow_add]
            congr 2; omega
          rw [h1, Nat.mul_div_cancel _ (pow_pos hp_pos 2)]
        rw [harg1, harg2]
  exact eq_sub_of_add_eq hgoal

theorem heckeOpLin_prime_pow_recurrence {N : ℕ} (k : ℕ) (χ : DirichletCharacter ℂ N)
    {p : ℕ} (hp : p.Prime) {r : ℕ} (hr : 1 ≤ r) :
    heckeOpLin k χ (p ^ (r + 1)) =
      heckeOpLin k χ p * heckeOpLin k χ (p ^ r) -
        (χ (p : ZMod N) * (p : ℂ) ^ (k - 1)) • heckeOpLin k χ (p ^ (r - 1)) := by
  ext f M
  exact congrFun (heckeOp_prime_pow_recurrence k χ hp hr f) M

/-! ### Full Hecke Algebra Commutativity `T_m ∘ T_n = T_n ∘ T_m` -/

private theorem heckeOp_prime_pow_comm_prime {N : ℕ} (k : ℕ) (χ : DirichletCharacter ℂ N)
    {p : ℕ} (hp : p.Prime) :
    ∀ a : ℕ, ∀ f : ℕ → ℂ,
      heckeOp k χ (p ^ a) (heckeOp k χ p f) = heckeOp k χ p (heckeOp k χ (p ^ a) f) := by
  intro a
  induction a using Nat.strong_induction_on with
  | h a ih =>
    match a with
    | 0 =>
      intro f
      simp [heckeOp_one]
    | 1 =>
      intro f
      simp
    | r + 2 =>
      intro f
      have hr : 1 ≤ r + 1 := by omega
      have hrec1 := heckeOp_prime_pow_recurrence k χ hp hr (heckeOp k χ p f)
      have hrec2 := heckeOp_prime_pow_recurrence k χ hp hr f
      rw [hrec1, hrec2, heckeOp_sub, heckeOp_smul]
      have ih1 := ih (r + 1) (by omega) f
      have ih0 := ih r (by omega) f
      simp only [Nat.add_sub_cancel] at hrec1 hrec2 ⊢
      rw [ih1, ih0]

theorem heckeOp_prime_pow_comm {N : ℕ} (k : ℕ) (χ : DirichletCharacter ℂ N)
    {p : ℕ} (hp : p.Prime) (a : ℕ) :
    ∀ b : ℕ, ∀ f : ℕ → ℂ,
      heckeOp k χ (p ^ a) (heckeOp k χ (p ^ b) f) =
        heckeOp k χ (p ^ b) (heckeOp k χ (p ^ a) f) := by
  intro b
  induction b using Nat.strong_induction_on with
  | h b ih =>
    match b with
    | 0 =>
      intro f
      simp [heckeOp_one]
    | 1 =>
      intro f
      simpa using heckeOp_prime_pow_comm_prime k χ hp a f
    | r + 2 =>
      intro f
      have hr : 1 ≤ r + 1 := by omega
      have hrec1 := heckeOp_prime_pow_recurrence k χ hp hr f
      have hrec2 := heckeOp_prime_pow_recurrence k χ hp hr (heckeOp k χ (p ^ a) f)
      simp only [Nat.add_sub_cancel] at hrec1 hrec2
      rw [hrec1, hrec2, heckeOp_sub, heckeOp_smul,
          heckeOp_prime_pow_comm_prime k χ hp a,
          ih (r + 1) (by omega), ih r (by omega)]

/-- Full commutativity of the concrete Hecke algebra: `T_m ∘ T_n = T_n ∘ T_m` for ALL `m, n ≥ 1`. -/
theorem heckeOp_comm {N : ℕ} (k : ℕ) (χ : DirichletCharacter ℂ N) :
    ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → ∀ f : ℕ → ℂ,
      heckeOp k χ m (heckeOp k χ n f) = heckeOp k χ n (heckeOp k χ m f) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro n hm hn f
    have hm0 : m ≠ 0 := by omega
    have hn0 : n ≠ 0 := by omega
    by_cases hm1 : m = 1
    · subst hm1; simp [heckeOp_one]
    obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
    set a := m.factorization p
    set b := n.factorization p
    have ha_pos : 1 ≤ a := (hp.dvd_iff_one_le_factorization hm0).mp hpm
    have hpa_dvd : p ^ a ∣ m := Nat.ordProj_dvd m p
    have hpb_dvd : p ^ b ∣ n := Nat.ordProj_dvd n p
    set m' := m / p ^ a
    set n' := n / p ^ b
    have hm_eq : m = p ^ a * m' := (Nat.mul_div_cancel' hpa_dvd).symm
    have hn_eq : n = p ^ b * n' := (Nat.mul_div_cancel' hpb_dvd).symm
    have hm'_pos : 1 ≤ m' := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hpa_dvd)
      (pow_pos hp.pos a)
    have hn'_pos : 1 ≤ n' := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpb_dvd)
      (pow_pos hp.pos b)
    have hp_not_m' : ¬ p ∣ m' := Nat.not_dvd_ordCompl hp hm0
    have hp_not_n' : ¬ p ∣ n' := Nat.not_dvd_ordCompl hp hn0
    have hcop_am' : Nat.Coprime (p ^ a) m' := (hp.coprime_iff_not_dvd.mpr hp_not_m').pow_left a
    have hcop_bn' : Nat.Coprime (p ^ b) n' := (hp.coprime_iff_not_dvd.mpr hp_not_n').pow_left b
    have hcop_an' : Nat.Coprime (p ^ a) n' := (hp.coprime_iff_not_dvd.mpr hp_not_n').pow_left a
    have hcop_m'b : Nat.Coprime m' (p ^ b) :=
      ((hp.coprime_iff_not_dvd.mpr hp_not_m').pow_left b).symm
    have hm'_lt : m' < m := by
      have hpa_gt : 1 < p ^ a := one_lt_pow₀ hp.one_lt (by omega)
      calc m' = 1 * m' := (one_mul m').symm
        _ < p ^ a * m' := Nat.mul_lt_mul_of_pos_right hpa_gt (by omega)
        _ = m := hm_eq.symm
    have hcomm_m'b : ∀ g, heckeOp k χ m' (heckeOp k χ (p ^ b) g) =
        heckeOp k χ (p ^ b) (heckeOp k χ m' g) := by
      intro g
      rw [heckeOp_mul_of_coprime k χ hcop_m'b, mul_comm,
          ← heckeOp_mul_of_coprime k χ hcop_m'b.symm]
    have hcomm_an' : ∀ g, heckeOp k χ (p ^ a) (heckeOp k χ n' g) =
        heckeOp k χ n' (heckeOp k χ (p ^ a) g) := by
      intro g
      rw [heckeOp_mul_of_coprime k χ hcop_an', mul_comm,
          ← heckeOp_mul_of_coprime k χ hcop_an'.symm]
    calc heckeOp k χ m (heckeOp k χ n f)
        = heckeOp k χ (p ^ a) (heckeOp k χ m' (heckeOp k χ (p ^ b) (heckeOp k χ n' f))) := by
            rw [hm_eq, hn_eq, ← heckeOp_mul_of_coprime k χ hcop_am',
                ← heckeOp_mul_of_coprime k χ hcop_bn']
      _ = heckeOp k χ (p ^ a) (heckeOp k χ (p ^ b) (heckeOp k χ m' (heckeOp k χ n' f))) := by
            rw [hcomm_m'b]
      _ = heckeOp k χ (p ^ b) (heckeOp k χ (p ^ a) (heckeOp k χ n' (heckeOp k χ m' f))) := by
            rw [ih m' hm'_lt n' hm'_pos hn'_pos f, heckeOp_prime_pow_comm k χ hp a b]
      _ = heckeOp k χ (p ^ b) (heckeOp k χ n' (heckeOp k χ (p ^ a) (heckeOp k χ m' f))) := by
            rw [hcomm_an']
      _ = heckeOp k χ n (heckeOp k χ m f) := by
            rw [hm_eq, hn_eq, ← heckeOp_mul_of_coprime k χ hcop_am',
                ← heckeOp_mul_of_coprime k χ hcop_bn']

theorem heckeOpLin_comm {N : ℕ} (k : ℕ) (χ : DirichletCharacter ℂ N)
    {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    heckeOpLin k χ m * heckeOpLin k χ n = heckeOpLin k χ n * heckeOpLin k χ m := by
  ext f M
  exact congrFun (heckeOp_comm k χ m n hm hn f) M

end HeckeAlgebra

/-! ## Section 2: Diamond Operators `⟨d⟩`, Nebentypus Eigenspaces & Slash-Action Hecke Compatibility -/

section DiamondAndSlash

/-- A function `f : UpperHalfPlane → ℂ` is `Γ₁(N)`-invariant of weight `k` if
`SlashAction.map k γ f = f` for every `γ ∈ CongruenceSubgroup.Gamma1 N`. -/
def IsGamma1Invariant (N : ℕ) (k : ℤ) (f : UpperHalfPlane → ℂ) : Prop :=
  ∀ γ ∈ CongruenceSubgroup.Gamma1 N, SlashAction.map k γ f = f

/-- A function `f : UpperHalfPlane → ℂ` has weight `k` and Nebentypus `χ : DirichletCharacter ℂ N`
on `Γ₀(N)` if `f ∣[k] γ = χ(γ 1 1) • f` for every `γ ∈ CongruenceSubgroup.Gamma0 N`. -/
def HasNebentypus {N : ℕ} (k : ℤ) (χ : DirichletCharacter ℂ N) (f : UpperHalfPlane → ℂ) : Prop :=
  ∀ (γ : CongruenceSubgroup.Gamma0 N),
    SlashAction.map k (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) f =
      χ (CongruenceSubgroup.Gamma0Map N γ) • f

/-- Every Nebentypus `Γ₀(N)`-form is `Γ₁(N)`-invariant. -/
theorem HasNebentypus.isGamma1Invariant {N : ℕ} {k : ℤ} {χ : DirichletCharacter ℂ N}
    {f : UpperHalfPlane → ℂ} (hf : HasNebentypus k χ f) :
    IsGamma1Invariant N k f := by
  intro γ hγ
  have hγ0 : γ ∈ CongruenceSubgroup.Gamma0 N := CongruenceSubgroup.Gamma1_in_Gamma0 N hγ
  have h := hf ⟨γ, hγ0⟩
  have h11 : CongruenceSubgroup.Gamma0Map N ⟨γ, hγ0⟩ = 1 :=
    ((CongruenceSubgroup.Gamma1_mem N γ).mp hγ).2.1
  rw [h11, map_one, one_smul] at h
  exact h

/-- Explicit constructive lift of any unit `d : (ZMod N)ˣ` to a matrix in `Γ₀(N)`
with lower-right entry congruent to `d` modulo `N`. -/
def gamma0Lift (N : ℕ) [NeZero N] (d : (ZMod N)ˣ) : CongruenceSubgroup.Gamma0 N := by
  let d0 : ℤ := (d.val.val : ℤ)
  let a0 : ℤ := ((d⁻¹).val.val : ℤ)
  have hmod : ((a0 * d0 - 1 : ℤ) : ZMod N) = 0 := by
    simp only [a0, d0, Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_one,
      ZMod.natCast_zmod_val, Units.inv_mul, sub_self]
  have hdvd : (N : ℤ) ∣ a0 * d0 - 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp hmod
  let b0 : ℤ := (a0 * d0 - 1) / (N : ℤ)
  have hdet : a0 * d0 - b0 * (N : ℤ) = 1 := by
    have hmul : (N : ℤ) * b0 = a0 * d0 - 1 := Int.mul_ediv_cancel' hdvd
    linarith
  let M : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![a0, b0; (N : ℤ), d0], by simp [Matrix.det_fin_two, hdet]⟩
  refine ⟨M, ?_⟩
  rw [CongruenceSubgroup.Gamma0_mem]
  simp [M]

@[simp]
theorem gamma0Lift_map (N : ℕ) [NeZero N] (d : (ZMod N)ˣ) :
    CongruenceSubgroup.Gamma0Map N (gamma0Lift N d) = (d : ZMod N) := by
  simp [gamma0Lift, CongruenceSubgroup.Gamma0Map]

/-- `CongruenceSubgroup.Gamma0Map N` maps `Γ₀(N)` onto `(ZMod N)ˣ`. -/
theorem gamma0Map_surjective_units (N : ℕ) [NeZero N] (d : (ZMod N)ˣ) :
    ∃ γ : CongruenceSubgroup.Gamma0 N, CongruenceSubgroup.Gamma0Map N γ = (d : ZMod N) :=
  ⟨gamma0Lift N d, gamma0Lift_map N d⟩

/-- Two elements of `Γ₀(N)` with the same lower-right entry modulo `N` differ by an element of `Γ₁(N)`. -/
theorem mul_inv_mem_Gamma1_of_gamma0Map_eq {N : ℕ}
    (γ₁ γ₂ : CongruenceSubgroup.Gamma0 N)
    (heq : CongruenceSubgroup.Gamma0Map N γ₁ = CongruenceSubgroup.Gamma0Map N γ₂) :
    (γ₁ : Matrix.SpecialLinearGroup (Fin 2) ℤ) * (γ₂ : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹ ∈
      CongruenceSubgroup.Gamma1 N := by
  have h10 : ((γ₁.1 : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod N) = 0 :=
    (CongruenceSubgroup.Gamma0_mem).mp γ₁.2
  have h20 : ((γ₂.1 : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod N) = 0 :=
    (CongruenceSubgroup.Gamma0_mem).mp γ₂.2
  have hdet1 : ((γ₁.1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod N) *
      ((γ₁.1 : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod N) = 1 := by
    have h := congrArg (Int.cast : ℤ → ZMod N) γ₁.1.prop
    rw [Matrix.det_fin_two] at h
    push_cast at h
    rw [h10, mul_zero, sub_zero] at h
    exact h
  have hdet2 : ((γ₂.1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod N) *
      ((γ₂.1 : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod N) = 1 := by
    have h := congrArg (Int.cast : ℤ → ZMod N) γ₂.1.prop
    rw [Matrix.det_fin_two] at h
    push_cast at h
    rw [h20, mul_zero, sub_zero] at h
    exact h
  have h11 : ((γ₁.1 : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod N) =
      ((γ₂.1 : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod N) := heq
  have h00 : ((γ₁.1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod N) =
      ((γ₂.1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod N) := by
    calc ((γ₁.1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod N)
        = ((γ₁.1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod N) *
            (((γ₂.1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod N) *
              ((γ₂.1 : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod N)) := by
            rw [hdet2, mul_one]
      _ = (((γ₁.1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod N) *
            ((γ₁.1 : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod N)) *
            ((γ₂.1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod N) := by
            rw [h11]; ring
      _ = ((γ₂.1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod N) := by rw [hdet1, one_mul]
  rw [CongruenceSubgroup.Gamma1_mem]
  have hinv_coe : ((γ₂.1⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![(γ₂.1 : Matrix (Fin 2) (Fin 2) ℤ) 1 1, -(γ₂.1 : Matrix (Fin 2) (Fin 2) ℤ) 0 1;
         -(γ₂.1 : Matrix (Fin 2) (Fin 2) ℤ) 1 0, (γ₂.1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Matrix.SpecialLinearGroup.coe_mul, hinv_coe, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_add,
      Int.cast_mul, Int.cast_neg, h20, neg_zero, mul_zero, add_zero, h00]
    exact hdet2
  · simp only [Matrix.SpecialLinearGroup.coe_mul, hinv_coe, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_add,
      Int.cast_mul, Int.cast_neg, h10, zero_mul, zero_add, h11, mul_comm]
    exact hdet2
  · simp only [Matrix.SpecialLinearGroup.coe_mul, hinv_coe, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_add,
      Int.cast_mul, Int.cast_neg, h10, h20, zero_mul, neg_zero, mul_zero, add_zero]

/-- Concrete diamond operator `⟨d⟩` of level `N` and weight `k` acting on functions on the
upper half-plane via the explicit lift `gamma0Lift N d ∈ Γ₀(N)`. -/
def diamondOp (N : ℕ) [NeZero N] (k : ℤ) (d : (ZMod N)ˣ) (f : UpperHalfPlane → ℂ) :
    UpperHalfPlane → ℂ :=
  SlashAction.map k (gamma0Lift N d : Matrix.SpecialLinearGroup (Fin 2) ℤ) f

/-- Lift-independence: on any `Γ₁(N)`-invariant function, `⟨d⟩ f = f ∣[k] γ` for EVERY
`γ ∈ Γ₀(N)` with `γ 1 1 ≡ d [MOD N]`. -/
theorem diamondOp_eq_slash_of_gamma0 {N : ℕ} [NeZero N] {k : ℤ} {f : UpperHalfPlane → ℂ}
    (hf : IsGamma1Invariant N k f) (γ : CongruenceSubgroup.Gamma0 N) (d : (ZMod N)ˣ)
    (hγ : CongruenceSubgroup.Gamma0Map N γ = (d : ZMod N)) :
    diamondOp N k d f = SlashAction.map k (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) f := by
  have hmem : (gamma0Lift N d : Matrix.SpecialLinearGroup (Fin 2) ℤ) *
      (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹ ∈ CongruenceSubgroup.Gamma1 N :=
    mul_inv_mem_Gamma1_of_gamma0Map_eq (gamma0Lift N d) γ (by rw [gamma0Lift_map, hγ])
  have hsplit : (gamma0Lift N d : Matrix.SpecialLinearGroup (Fin 2) ℤ) =
      ((gamma0Lift N d : Matrix.SpecialLinearGroup (Fin 2) ℤ) *
        (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)⁻¹) *
        (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) := by
    simp
  unfold diamondOp
  rw [hsplit, SlashAction.slash_mul, hf _ hmem]

/-- `⟨1⟩ f = f` for every `Γ₁(N)`-invariant function `f`. -/
theorem diamondOp_one {N : ℕ} [NeZero N] {k : ℤ} {f : UpperHalfPlane → ℂ}
    (hf : IsGamma1Invariant N k f) :
    diamondOp N k 1 f = f := by
  have h := diamondOp_eq_slash_of_gamma0 hf (1 : CongruenceSubgroup.Gamma0 N) 1 (by simp)
  rw [h, OneMemClass.coe_one, SlashAction.slash_one]

/-- Multiplicativity of diamond operators: `⟨d₁ * d₂⟩ f = ⟨d₂⟩ (⟨d₁⟩ f)`. -/
theorem diamondOp_mul {N : ℕ} [NeZero N] {k : ℤ} {f : UpperHalfPlane → ℂ}
    (hf : IsGamma1Invariant N k f) (d₁ d₂ : (ZMod N)ˣ) :
    diamondOp N k (d₁ * d₂) f = diamondOp N k d₂ (diamondOp N k d₁ f) := by
  have hmap : CongruenceSubgroup.Gamma0Map N (gamma0Lift N d₁ * gamma0Lift N d₂) =
      ((d₁ * d₂ : (ZMod N)ˣ) : ZMod N) := by
    rw [map_mul, gamma0Lift_map, gamma0Lift_map, Units.val_mul]
  rw [diamondOp_eq_slash_of_gamma0 hf (gamma0Lift N d₁ * gamma0Lift N d₂) (d₁ * d₂) hmap]
  simp only [Subgroup.coe_mul, SlashAction.slash_mul, diamondOp]

/-- Commutativity of diamond operators: `⟨d₁⟩ (⟨d₂⟩ f) = ⟨d₂⟩ (⟨d₁⟩ f)`. -/
theorem diamondOp_comm {N : ℕ} [NeZero N] {k : ℤ} {f : UpperHalfPlane → ℂ}
    (hf : IsGamma1Invariant N k f) (d₁ d₂ : (ZMod N)ˣ) :
    diamondOp N k d₁ (diamondOp N k d₂ f) = diamondOp N k d₂ (diamondOp N k d₁ f) := by
  rw [← diamondOp_mul hf d₂ d₁, mul_comm d₂ d₁, diamondOp_mul hf d₁ d₂]

/-- Exact characterization of Nebentypus eigenspaces via diamond operators:
for a `Γ₁(N)`-invariant function `f`, `HasNebentypus k χ f ↔ ∀ d : (ZMod N)ˣ, ⟨d⟩ f = χ d • f`. -/
theorem hasNebentypus_iff_diamondOp {N : ℕ} [NeZero N] {k : ℤ}
    {χ : DirichletCharacter ℂ N} {f : UpperHalfPlane → ℂ}
    (hf : IsGamma1Invariant N k f) :
    HasNebentypus k χ f ↔ ∀ d : (ZMod N)ˣ, diamondOp N k d f = χ (d : ZMod N) • f := by
  constructor
  · intro hneb d
    unfold diamondOp
    rw [hneb (gamma0Lift N d), gamma0Lift_map]
  · intro hdiam γ
    have hdet : ((γ.1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod N) *
        ((γ.1 : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod N) = 1 := by
      have h10 : ((γ.1 : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod N) = 0 :=
        (CongruenceSubgroup.Gamma0_mem).mp γ.2
      have h := congrArg (Int.cast : ℤ → ZMod N) γ.1.prop
      rw [Matrix.det_fin_two] at h
      push_cast at h
      rw [h10, mul_zero, sub_zero] at h
      exact h
    let d : (ZMod N)ˣ :=
      ⟨((γ.1 : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod N),
       ((γ.1 : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod N),
       by rw [mul_comm]; exact hdet, hdet⟩
    have hd : CongruenceSubgroup.Gamma0Map N γ = (d : ZMod N) := rfl
    rw [← diamondOp_eq_slash_of_gamma0 hf γ d hd, hdiam d, hd]

/-! ### Concrete Upper-Triangular Coset Representatives & Slash-Action Hecke Operator -/

/-- Upper-triangular Hecke coset representative `[[a, b], [0, d]] ∈ GL₂⁺(ℝ)` for `a, d > 0`. -/
def heckeMat (a b d : ℕ) (ha : 0 < a) (hd : 0 < d) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(a : ℝ), (b : ℝ); 0, (d : ℝ)] (by
    simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      mul_zero, sub_zero]
    exact mul_ne_zero (Nat.cast_ne_zero (R := ℝ).mpr (ne_of_gt ha))
      (Nat.cast_ne_zero (R := ℝ).mpr (ne_of_gt hd)))

theorem heckeMat_det (a b d : ℕ) (ha : 0 < a) (hd : 0 < d) :
    ((Matrix.GeneralLinearGroup.det (heckeMat a b d ha hd)) : ℝ) = (a : ℝ) * (d : ℝ) := by
  simp [heckeMat, Matrix.det_fin_two]

theorem heckeMat_det_pos (a b d : ℕ) (ha : 0 < a) (hd : 0 < d) :
    0 < ((Matrix.GeneralLinearGroup.det (heckeMat a b d ha hd)) : ℝ) := by
  rw [heckeMat_det]
  positivity

private theorem heckeMat_sigma_eq_refl (a b d : ℕ) (ha : 0 < a) (hd : 0 < d) :
    UpperHalfPlane.σ (heckeMat a b d ha hd) = ContinuousAlgEquiv.refl ℝ ℂ := by
  have hdet_pos : 0 < ((heckeMat a b d ha hd : Matrix (Fin 2) (Fin 2) ℝ).det) := by
    simpa [heckeMat, Matrix.det_fin_two] using (by positivity : (0 : ℝ) < (a : ℝ) * (d : ℝ))
  simp [UpperHalfPlane.σ, not_le.mpr hdet_pos]

theorem heckeMat_smul_coe (a b d : ℕ) (ha : 0 < a) (hd : 0 < d) (τ : UpperHalfPlane) :
    ((heckeMat a b d ha hd • τ : UpperHalfPlane) : ℂ) =
      ((a : ℂ) * (τ : ℂ) + (b : ℂ)) / (d : ℂ) := by
  rw [UpperHalfPlane.coe_smul, heckeMat_sigma_eq_refl, ContinuousAlgEquiv.refl_apply]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, heckeMat]

theorem heckeMat_slash_apply {k : ℕ} (hk : 1 ≤ k) (a b d : ℕ) (ha : 0 < a) (hd : 0 < d)
    (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    (SlashAction.map (k : ℤ) (heckeMat a b d ha hd) f) τ =
      f (heckeMat a b d ha hd • τ) * ((a : ℂ) ^ (k - 1) / (d : ℂ)) := by
  rw [ModularForm.slash_def]
  dsimp only
  have hdenom : UpperHalfPlane.denom (heckeMat a b d ha hd) (τ : ℂ) = (d : ℂ) := by
    simp [UpperHalfPlane.denom, heckeMat]
  rw [heckeMat_sigma_eq_refl, ContinuousAlgEquiv.refl_apply, hdenom, heckeMat_det,
      abs_of_pos (by positivity : (0 : ℝ) < (a : ℝ) * (d : ℝ))]
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hd)
  have hk' : ((k : ℤ) - 1) = ((k - 1 : ℕ) : ℤ) := by omega
  rw [hk', zpow_natCast, _root_.zpow_neg, zpow_natCast]
  push_cast
  rw [mul_pow]
  have hdk : (d : ℂ) ^ k = (d : ℂ) ^ (k - 1) * (d : ℂ) := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hdk, mul_inv, mul_assoc]
  congr 1
  have hdp : (d : ℂ) ^ (k - 1) ≠ 0 := pow_ne_zero _ hd0
  field_simp [hd0, hdp]

/-- Concrete slash-action Hecke operator `T_n` of weight `k` and Nebentypus `χ` on functions
`f : UpperHalfPlane → ℂ`, defined via the explicit coset representatives `[[a, b], [0, n / a]]`
for `a ∣ n` and `0 ≤ b < n / a`. -/
def slashHeckeOp {N : ℕ} (k : ℕ) (χ : DirichletCharacter ℂ N) (n : ℕ)
    (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) : ℂ :=
  ∑ a ∈ n.divisors, χ (a : ZMod N) *
    ∑ b ∈ Finset.range (n / a),
      if h : 0 < a ∧ 0 < n / a then
        (SlashAction.map (k : ℤ) (heckeMat a b (n / a) h.1 h.2) f) τ
      else 0

/-- Exact roots-of-unity orthogonality:
`∑_{b < d} exp(2πi m b / d) = if d ∣ m then d else 0` for every `d > 0`. -/
theorem sum_rootsOfUnity_eq_ite {d : ℕ} (hd : 0 < d) (m : ℕ) :
    ∑ b ∈ Finset.range d,
        Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (b : ℂ) / (d : ℂ)) =
      if d ∣ m then (d : ℂ) else 0 := by
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) / (d : ℂ))
  have hterm : ∀ b : ℕ,
      Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (b : ℂ) / (d : ℂ)) = ζ ^ b := by
    intro b
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  simp_rw [hterm]
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hd)
  by_cases hdm : d ∣ m
  · rw [if_pos hdm]
    rcases hdm with ⟨q, rfl⟩
    have hζ : ζ = 1 := by
      simp only [ζ, Nat.cast_mul]
      have harg : 2 * ↑Real.pi * Complex.I * (↑d * ↑q) / ↑d = (q : ℂ) * (2 * ↑Real.pi * Complex.I) := by
        field_simp [hd0]
      rw [harg, Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]
    simp [hζ]
  · rw [if_neg hdm]
    have hζ_ne : ζ ≠ 1 := by
      intro h1
      rw [Complex.exp_eq_one_iff] at h1
      rcases h1 with ⟨n, hn⟩
      have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
        refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero
        exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have hmn : (m : ℂ) / (d : ℂ) = (n : ℂ) := by
        apply mul_left_cancel₀ hpi
        have : 2 * ↑Real.pi * Complex.I * ((m : ℂ) / (d : ℂ)) =
            2 * ↑Real.pi * Complex.I * (m : ℂ) / (d : ℂ) := by ring
        rw [this, hn]
        ring
      have hmd : (m : ℂ) = (n : ℂ) * (d : ℂ) := (div_eq_iff hd0).mp hmn
      have hmdZ : (m : ℤ) = n * (d : ℤ) := by exact_mod_cast hmd
      have hdvdZ : (d : ℤ) ∣ (m : ℤ) := ⟨n, by linarith⟩
      exact hdm (Int.ofNat_dvd.mp hdvdZ)
    have hζd : ζ ^ d = 1 := by
      rw [← Complex.exp_nat_mul]
      have harg : (d : ℂ) * (2 * ↑Real.pi * Complex.I * (m : ℂ) / (d : ℂ)) =
          (m : ℂ) * (2 * ↑Real.pi * Complex.I) := by
        field_simp [hd0]
      rw [harg, Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]
    rw [geom_sum_eq hζ_ne, hζd, sub_self, zero_div]

private theorem qParam_heckeMat_pow (a b d : ℕ) (ha : 0 < a) (hd : 0 < d)
    (τ : UpperHalfPlane) (m : ℕ) :
    Function.Periodic.qParam 1 ((heckeMat a b d ha hd • τ : UpperHalfPlane) : ℂ) ^ m =
      Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (a : ℂ) * (τ : ℂ) / (d : ℂ)) *
        Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (b : ℂ) / (d : ℂ)) := by
  rw [Function.Periodic.qParam, Complex.ofReal_one, div_one, ← Complex.exp_nat_mul,
      ← Complex.exp_add, heckeMat_smul_coe]
  congr 1
  ring

private theorem qParam_one_pow (τ : UpperHalfPlane) (M : ℕ) :
    Function.Periodic.qParam 1 (τ : ℂ) ^ M =
      Complex.exp (2 * Real.pi * Complex.I * (M : ℂ) * (τ : ℂ)) := by
  rw [Function.Periodic.qParam, Complex.ofReal_one, div_one, ← Complex.exp_nat_mul]
  congr 1
  ring

/-- **Exact Fourier-Coefficient Action Theorem**:
If `f : UpperHalfPlane → ℂ` has convergent `q`-expansion `f τ = ∑' m, c m * q(τ)^m` everywhere on
the upper half-plane, then for every weight `k ≥ 1`, Nebentypus `χ`, and `n ≥ 1`, the concrete
slash-action Hecke operator `slashHeckeOp k χ n f` has the exact convergent `q`-expansion whose
`M`-th coefficient is `(heckeOp k χ n c) M`. -/
theorem slashHeckeOp_hasSum_qExpansion {N : ℕ} {k : ℕ} (hk : 1 ≤ k)
    (χ : DirichletCharacter ℂ N) {n : ℕ} (hn : 1 ≤ n)
    (f : UpperHalfPlane → ℂ) (c : ℕ → ℂ)
    (hf : ∀ τ : UpperHalfPlane,
      HasSum (fun m : ℕ => c m * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (f τ))
    (τ : UpperHalfPlane) :
    HasSum (fun M : ℕ => heckeOp k χ n c M * Function.Periodic.qParam 1 (τ : ℂ) ^ M)
      (slashHeckeOp k χ n f τ) := by
  have hn0 : n ≠ 0 := by omega
  -- For each divisor `a ∣ n`, establish the `HasSum` for the inner `b`-average.
  have hinner : ∀ a ∈ n.divisors,
      HasSum
        (fun M : ℕ =>
          (if a ∣ M then χ (a : ZMod N) * (a : ℂ) ^ (k - 1) * c (M * n / a ^ 2) else 0) *
            Function.Periodic.qParam 1 (τ : ℂ) ^ M)
        (χ (a : ZMod N) *
          ∑ b ∈ Finset.range (n / a),
            if h : 0 < a ∧ 0 < n / a then
              (SlashAction.map (k : ℤ) (heckeMat a b (n / a) h.1 h.2) f) τ
            else 0) := by
    intro a ha_mem
    have ha_dvd : a ∣ n := (Nat.mem_divisors.mp ha_mem).1
    have ha_pos : 0 < a := Nat.pos_of_dvd_of_pos ha_dvd (Nat.pos_of_ne_zero hn0)
    set d := n / a with hd_def
    have had : a * d = n := Nat.mul_div_cancel' ha_dvd
    have hd_pos : 0 < d := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) ha_dvd) ha_pos
    have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hd_pos)
    have hboth : 0 < a ∧ 0 < d := ⟨ha_pos, hd_pos⟩
    -- Sum `HasSum` over `b ∈ Finset.range d`.
    have hb_sum : ∀ b ∈ Finset.range d,
        HasSum
          (fun m : ℕ =>
            c m * Function.Periodic.qParam 1 ((heckeMat a b d ha_pos hd_pos • τ : UpperHalfPlane) : ℂ) ^ m *
              ((a : ℂ) ^ (k - 1) / (d : ℂ)))
          (if h : 0 < a ∧ 0 < d then
            (SlashAction.map (k : ℤ) (heckeMat a b d h.1 h.2) f) τ
           else 0) := by
      intro b _
      rw [dif_pos hboth, heckeMat_slash_apply hk]
      exact (hf (heckeMat a b d ha_pos hd_pos • τ)).mul_right _
    have hsum_b := hasSum_sum hb_sum
    have hsum_b_simp :
        HasSum
          (fun m : ℕ =>
            if d ∣ m then
              c m * (a : ℂ) ^ (k - 1) * Function.Periodic.qParam 1 (τ : ℂ) ^ (m / d * a)
            else 0)
          (∑ b ∈ Finset.range d,
            if h : 0 < a ∧ 0 < d then
              (SlashAction.map (k : ℤ) (heckeMat a b d h.1 h.2) f) τ
            else 0) := by
      refine hsum_b.congr_fun fun m => ?_
      have hfactor :
          (∑ b ∈ Finset.range d,
            c m * Function.Periodic.qParam 1 ((heckeMat a b d ha_pos hd_pos • τ : UpperHalfPlane) : ℂ) ^ m *
              ((a : ℂ) ^ (k - 1) / (d : ℂ))) =
          c m * ((a : ℂ) ^ (k - 1) / (d : ℂ)) *
            Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (a : ℂ) * (τ : ℂ) / (d : ℂ)) *
            (∑ b ∈ Finset.range d,
              Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) * (b : ℂ) / (d : ℂ))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [qParam_heckeMat_pow]
        ring
      rw [hfactor, sum_rootsOfUnity_eq_ite hd_pos m]
      split_ifs with hdm
      · rcases hdm with ⟨r, rfl⟩
        rw [Nat.mul_div_cancel_left r hd_pos, qParam_one_pow]
        push_cast
        have hexp :
            2 * ↑Real.pi * Complex.I * (↑d * ↑r) * ↑a * ↑τ / ↑d =
              2 * ↑Real.pi * Complex.I * (↑r * ↑a) * ↑τ := by
          field_simp [hd0]
        rw [hexp]
        field_simp [hd0]
      · simp
    -- Reindex `m = d * r` via the injection `r ↦ d * r`.
    have hinj_d : Function.Injective (fun r : ℕ => d * r) := mul_right_injective₀ (ne_of_gt hd_pos)
    have hsum_r :
        HasSum
          (fun r : ℕ => c (d * r) * (a : ℂ) ^ (k - 1) * Function.Periodic.qParam 1 (τ : ℂ) ^ (r * a))
          (∑ b ∈ Finset.range d,
            if h : 0 < a ∧ 0 < d then
              (SlashAction.map (k : ℤ) (heckeMat a b d h.1 h.2) f) τ
            else 0) := by
      have h1 := (hinj_d.hasSum_iff (f := fun m : ℕ =>
          if d ∣ m then
            c m * (a : ℂ) ^ (k - 1) * Function.Periodic.qParam 1 (τ : ℂ) ^ (m / d * a)
          else 0) (fun m hm => by
            rw [if_neg]
            intro hdm
            rcases hdm with ⟨r, rfl⟩
            exact hm ⟨r, rfl⟩)).mpr hsum_b_simp
      refine h1.congr_fun fun r => ?_
      simp [Nat.mul_div_cancel_left r hd_pos]
    -- Reindex `M = r * a` via the injection `r ↦ r * a`.
    have hinj_a : Function.Injective (fun r : ℕ => r * a) := mul_left_injective₀ (ne_of_gt ha_pos)
    have hsum_M :
        HasSum
          (fun M : ℕ =>
            if a ∣ M then
              c (M * n / a ^ 2) * (a : ℂ) ^ (k - 1) * Function.Periodic.qParam 1 (τ : ℂ) ^ M
            else 0)
          (∑ b ∈ Finset.range d,
            if h : 0 < a ∧ 0 < d then
              (SlashAction.map (k : ℤ) (heckeMat a b d h.1 h.2) f) τ
            else 0) := by
      refine (hinj_a.hasSum_iff (f := fun M : ℕ =>
          if a ∣ M then
            c (M * n / a ^ 2) * (a : ℂ) ^ (k - 1) * Function.Periodic.qParam 1 (τ : ℂ) ^ M
          else 0) (fun M hM => by
            rw [if_neg]
            intro haM
            rcases haM with ⟨r, rfl⟩
            exact hM ⟨r, mul_comm r a⟩)).mp ?_
      refine hsum_r.congr_fun fun r => ?_
      have hdvd : a ∣ r * a := dvd_mul_left a r
      simp only [Function.comp_def, if_pos hdvd]
      have harg : r * a * n / a ^ 2 = d * r := by
        have h1 : r * a * n = a ^ 2 * (d * r) := by
          calc r * a * n = r * a * (a * d) := by rw [had]
            _ = a ^ 2 * (d * r) := by ring
        rw [h1, Nat.mul_div_cancel_left _ (pow_pos ha_pos 2)]
      rw [harg]
    refine (hsum_M.mul_left (χ (a : ZMod N))).congr_fun fun M => ?_
    split_ifs <;> ring
  -- Sum over `a ∈ n.divisors`.
  have htotal := hasSum_sum hinner
  refine htotal.congr_fun fun M => ?_
  rw [← Finset.sum_mul]
  congr 1
  simp only [heckeOp, heckeWeight]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext a
  simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨⟨haM, han⟩, _⟩
    exact ⟨⟨han, hn0⟩, haM⟩
  · rintro ⟨⟨han, _⟩, haM⟩
    exact ⟨⟨haM, han⟩, fun h => hn0 (Nat.gcd_eq_zero_iff.mp h).2⟩

/-- Direct application of `slashHeckeOp_hasSum_qExpansion` to Mathlib's actual `ModularForm` /
`CuspForm` spaces (for any congruence subgroup `Γ` with `1 ∈ Γ.strictPeriods`, e.g., `Γ₀(N)` or
`Γ₁(N)`): the slash-action Hecke operator transforms `UpperHalfPlane.qExpansion 1 f` by `heckeOp`. -/
theorem modularForm_slashHeckeOp_hasSum_qExpansion
    {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℕ} (hk : 1 ≤ k)
    [ModularFormClass F Γ (k : ℤ)] [Fact (IsCusp OnePoint.infty Γ)]
    (h1 : (1 : ℝ) ∈ Γ.strictPeriods)
    {N : ℕ} (χ : DirichletCharacter ℂ N) {n : ℕ} (hn : 1 ≤ n)
    (f : F) (τ : UpperHalfPlane) :
    HasSum
      (fun M : ℕ =>
        heckeOp k χ n (fun m => PowerSeries.coeff m (UpperHalfPlane.qExpansion 1 (⇑f))) M *
          Function.Periodic.qParam 1 (τ : ℂ) ^ M)
      (slashHeckeOp k χ n (⇑f) τ) :=
  slashHeckeOp_hasSum_qExpansion hk χ hn (⇑f)
    (fun m => PowerSeries.coeff m (UpperHalfPlane.qExpansion 1 (⇑f)))
    (fun τ' => ModularForm.hasSum_qExpansion f zero_lt_one h1 τ') τ

end DiamondAndSlash

/-! ## Section 3: Normalized Hecke Eigenforms ⇒ Exact `GL_2` Multiplicativity -/

section Eigenforms

/-- `f : ℕ → ℂ` is a simultaneous Hecke eigenform of weight `k` and Nebentypus `χ` with
eigenvalue sequence `lam : ℕ → ℂ` if `T_n f = lam n • f` for all `n ≥ 1`. -/
def IsHeckeEigenform {N : ℕ} (k : ℕ) (χ : DirichletCharacter ℂ N)
    (f lam : ℕ → ℂ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → heckeOp k χ n f = lam n • f

/-- A normalized simultaneous Hecke eigenform satisfies `f 1 = 1` and `T_n f = lam n • f`. -/
def IsNormalizedHeckeEigenform {N : ℕ} (k : ℕ) (χ : DirichletCharacter ℂ N)
    (f lam : ℕ → ℂ) : Prop :=
  f 1 = 1 ∧ IsHeckeEigenform k χ f lam

/-- For a normalized Hecke eigenform, the `n`-th Hecke eigenvalue equals the `n`-th Fourier
coefficient: `lam n = f n` for every `n ≥ 1`. -/
theorem eigenvalue_eq_coeff {N : ℕ} {k : ℕ} {χ : DirichletCharacter ℂ N}
    {f lam : ℕ → ℂ} (hf : IsNormalizedHeckeEigenform k χ f lam) {n : ℕ} (hn : 1 ≤ n) :
    lam n = f n := by
  have h := congrFun (hf.2 n hn) 1
  rw [heckeOp_apply_one k χ hn, Pi.smul_apply, smul_eq_mul, hf.1, mul_one] at h
  exact h.symm

/-- Exact `GL_2` product formula for Fourier coefficients of a normalized Hecke eigenform:
`f m * f n = ∑ d ∣ gcd(m, n), χ(d) · d^(k - 1) · f(m * n / d²)` for all `m, n ≥ 1`. -/
theorem eigenform_mul_eq_sum {N : ℕ} {k : ℕ} {χ : DirichletCharacter ℂ N}
    {f lam : ℕ → ℂ} (hf : IsNormalizedHeckeEigenform k χ f lam)
    {m n : ℕ} (hn : 1 ≤ n) :
    f m * f n =
      ∑ d ∈ (Nat.gcd m n).divisors,
        χ (d : ZMod N) * (d : ℂ) ^ (k - 1) * f (m * n / d ^ 2) := by
  have h := congrFun (hf.2 n hn) m
  rw [Pi.smul_apply, smul_eq_mul, eigenvalue_eq_coeff hf hn, mul_comm] at h
  exact h.symm

/-- Unconditional multiplicativity of Fourier coefficients of a normalized Hecke eigenform:
`f (m * n) = f m * f n` whenever `Nat.Coprime m n` and `m, n ≥ 1`. -/
theorem eigenform_isMultiplicative {N : ℕ} {k : ℕ} {χ : DirichletCharacter ℂ N}
    {f lam : ℕ → ℂ} (hf : IsNormalizedHeckeEigenform k χ f lam)
    {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hcop : Nat.Coprime m n) :
    f (m * n) = f m * f n := by
  have h := eigenform_mul_eq_sum hf hn (m := m)
  have _ : m ≠ 0 := by omega
  rw [hcop.gcd_eq_one] at h
  simpa using h.symm

/-- Exact `GL_2` prime-power recurrence for Fourier coefficients of a normalized Hecke eigenform:
`f (p ^ (r + 2)) = f p * f (p ^ (r + 1)) - χ(p) · p^(k - 1) · f (p ^ r)` for every prime `p`
and every `r : ℕ`. -/
theorem eigenform_prime_pow_recurrence {N : ℕ} {k : ℕ} {χ : DirichletCharacter ℂ N}
    {f lam : ℕ → ℂ} (hf : IsNormalizedHeckeEigenform k χ f lam)
    {p : ℕ} (hp : p.Prime) (r : ℕ) :
    f (p ^ (r + 2)) =
      f p * f (p ^ (r + 1)) - χ (p : ZMod N) * (p : ℂ) ^ (k - 1) * f (p ^ r) := by
  have hrec := congrFun (heckeOp_prime_pow_recurrence k χ hp (r := r + 1) (by omega) f) 1
  have h1 : 1 ≤ p ^ (r + 2) := one_le_pow₀ hp.one_le
  have h2 : 1 ≤ p ^ (r + 1) := one_le_pow₀ hp.one_le
  have h3 : 1 ≤ p ^ r := one_le_pow₀ hp.one_le
  have hp1 : 1 ≤ p := hp.one_le
  simp only [Nat.add_sub_cancel, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hrec
  rw [heckeOp_apply_one k χ h1, heckeOp_apply_one k χ h3,
      hf.2 (p ^ (r + 1)) h2, heckeOp_smul, hf.2 p hp1] at hrec
  simp only [Pi.smul_apply, smul_eq_mul, hf.1, mul_one] at hrec
  rw [eigenvalue_eq_coeff hf h2, eigenvalue_eq_coeff hf hp1, mul_comm (f (p ^ (r + 1))) (f p)] at hrec
  exact hrec

/-- Associated `ArithmeticFunction ℂ` (zero at `0`, equal to `f n` for `n ≥ 1`). -/
def toArithFun (f : ℕ → ℂ) : ArithmeticFunction ℂ where
  toFun n := if n = 0 then 0 else f n
  map_zero' := if_pos rfl

@[simp]
theorem toArithFun_apply_of_pos (f : ℕ → ℂ) {n : ℕ} (hn : 1 ≤ n) :
    toArithFun f n = f n :=
  if_neg (by omega)

/-- The `ArithmeticFunction ℂ` attached to any normalized Hecke eigenform is multiplicative in
Mathlib's `ArithmeticFunction.IsMultiplicative` sense. -/
theorem eigenform_arithFun_isMultiplicative {N : ℕ} {k : ℕ} {χ : DirichletCharacter ℂ N}
    {f lam : ℕ → ℂ} (hf : IsNormalizedHeckeEigenform k χ f lam) :
    (toArithFun f).IsMultiplicative := by
  refine ⟨by simp [toArithFun, hf.1], fun {m n} hcop => ?_⟩
  by_cases hm : m = 0
  · subst hm; simp [toArithFun]
  by_cases hn : n = 0
  · subst hn; simp [toArithFun]
  have hmn : m * n ≠ 0 := mul_ne_zero hm hn
  simp only [toArithFun, ArithmeticFunction.coe_mk, if_neg hm, if_neg hn, if_neg hmn]
  exact eigenform_isMultiplicative hf (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn) hcop

end Eigenforms

/-! ## Section 4: Exact Prime-Power Generating Series & Satake Parameters `(α_p, β_p)` -/

section SatakeAndLocalSeries

/-- A pair `(α, β) ∈ ℂ²` is a **Satake parameter pair** for local Hecke data `(a_p, c_p)` if
`α + β = a_p` and `α * β = c_p`, i.e., `1 - a_p X + c_p X² = (1 - α X)(1 - β X)`. -/
def IsSatakePair (a_p c_p α β : ℂ) : Prop :=
  α + β = a_p ∧ α * β = c_p

/-- Unconditional existence of Satake parameters `(α, β)` over `ℂ` for any `(a_p, c_p)`. -/
theorem exists_satake_pair (a_p c_p : ℂ) : ∃ α β : ℂ, IsSatakePair a_p c_p α β := by
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (a_p ^ 2 - 4 * c_p) (by norm_num : 0 < 2)
  refine ⟨(a_p + δ) / 2, (a_p - δ) / 2, ?_, ?_⟩
  · ring
  · have h : (a_p + δ) / 2 * ((a_p - δ) / 2) = (a_p ^ 2 - δ ^ 2) / 4 := by ring
    rw [h, hδ]
    ring

/-- Exact factorization of the degree-2 local Euler polynomial in terms of Satake parameters. -/
theorem eulerPoly_eq_satake_prod {a_p c_p α β : ℂ} (hs : IsSatakePair a_p c_p α β) (z : ℂ) :
    1 - a_p * z + c_p * z ^ 2 = (1 - α * z) * (1 - β * z) := by
  rw [← hs.1, ← hs.2]
  ring

/-- Exact formal power series factorization of the degree-2 Euler polynomial in `PowerSeries ℂ`. -/
theorem eulerPowerSeries_eq_satake_prod {a_p c_p α β : ℂ} (hs : IsSatakePair a_p c_p α β) :
    (1 - PowerSeries.C a_p * PowerSeries.X + PowerSeries.C c_p * PowerSeries.X ^ 2 :
        PowerSeries ℂ) =
      (1 - PowerSeries.C α * PowerSeries.X) * (1 - PowerSeries.C β * PowerSeries.X) := by
  rw [← hs.1, ← hs.2, map_add, map_mul]
  ring

/-- Exact formal power series identity for a prime-power recurrence sequence:
`(1 - a_p X + c_p X²) · (∑_{r=0}^∞ f(p^r) X^r) = 1` in `PowerSeries ℂ`. -/
theorem primePow_eulerPoly_mul_powerSeries {a_p c_p : ℂ} {g : ℕ → ℂ}
    (hg0 : g 0 = 1) (hg1 : g 1 = a_p)
    (hrec : ∀ r : ℕ, g (r + 2) = a_p * g (r + 1) - c_p * g r) :
    (1 - PowerSeries.C a_p * PowerSeries.X + PowerSeries.C c_p * PowerSeries.X ^ 2) *
        PowerSeries.mk g = (1 : PowerSeries ℂ) := by
  ext n
  have h1 :
      (1 - PowerSeries.C a_p * PowerSeries.X + PowerSeries.C c_p * PowerSeries.X ^ 2) *
          PowerSeries.mk g =
        PowerSeries.mk g - PowerSeries.C a_p * (PowerSeries.X * PowerSeries.mk g) +
          PowerSeries.C c_p * (PowerSeries.X ^ 2 * PowerSeries.mk g) := by
    ring
  rw [h1]
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
  have hX0 : ∀ φ : PowerSeries ℂ, PowerSeries.coeff 0 (PowerSeries.X * φ) = 0 := by
    intro φ
    rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
    simp [PowerSeries.coeff_X]
  match n with
  | 0 =>
    rw [hX0, sq, mul_assoc, hX0, hg0]
    simp
  | 1 =>
    rw [PowerSeries.coeff_succ_X_mul, sq, mul_assoc, PowerSeries.coeff_succ_X_mul, hX0,
        PowerSeries.coeff_mk, hg0, hg1]
    simp
  | r + 2 =>
    have hX2 : PowerSeries.coeff (r + 2) (PowerSeries.X ^ 2 * PowerSeries.mk g) = g r := by
      rw [sq, mul_assoc, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul,
          PowerSeries.coeff_mk]
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk, hX2,
        PowerSeries.coeff_one, if_neg (by omega : r + 2 ≠ 0), hrec r]
    ring

/-- Formal power series identity specialized to a normalized Hecke eigenform at any prime `p`. -/
theorem eigenform_primePow_eulerPoly_mul_powerSeries {N : ℕ} {k : ℕ}
    {χ : DirichletCharacter ℂ N} {f lam : ℕ → ℂ}
    (hf : IsNormalizedHeckeEigenform k χ f lam) {p : ℕ} (hp : p.Prime) :
    (1 - PowerSeries.C (f p) * PowerSeries.X +
        PowerSeries.C (χ (p : ZMod N) * (p : ℂ) ^ (k - 1)) * PowerSeries.X ^ 2) *
        PowerSeries.mk (fun r => f (p ^ r)) = (1 : PowerSeries ℂ) :=
  primePow_eulerPoly_mul_powerSeries
    (by simp [hf.1]) (by simp) (fun r => eigenform_prime_pow_recurrence hf hp r)

/-- Exact closed formula for `g r` (and `f (p ^ r)`) as the complete homogeneous symmetric
polynomial in the Satake parameters `(α, β)`: `g r = ∑_{j=0}^r α^j β^{r - j}`. -/
theorem primePow_eq_satake_sum {a_p c_p α β : ℂ} (hs : IsSatakePair a_p c_p α β)
    {g : ℕ → ℂ} (hg0 : g 0 = 1) (hg1 : g 1 = a_p)
    (hrec : ∀ r : ℕ, g (r + 2) = a_p * g (r + 1) - c_p * g r) :
    ∀ r : ℕ, g r = ∑ j ∈ Finset.range (r + 1), α ^ j * β ^ (r - j) := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    match r with
    | 0 => simp [hg0]
    | 1 =>
      rw [hg1, ← hs.1, Finset.sum_range_succ, Finset.sum_range_one]
      simp [add_comm]
    | r + 2 =>
      rw [hrec r, ih (r + 1) (by omega), ih r (by omega), ← hs.1, ← hs.2]
      have hsplit1 :
          ∑ j ∈ Finset.range (r + 3), α ^ j * β ^ (r + 2 - j) =
            β ^ (r + 2) + ∑ j ∈ Finset.range (r + 2), α ^ (j + 1) * β ^ (r + 1 - j) := by
        rw [Finset.sum_range_succ', pow_zero, one_mul, Nat.sub_zero, add_comm]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 2; omega
      have hsplit2 :
          ∑ j ∈ Finset.range (r + 2), α ^ j * β ^ (r + 1 - j) =
            α ^ (r + 1) + ∑ j ∈ Finset.range (r + 1), α ^ j * β ^ (r + 1 - j) := by
        rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, add_comm]
      have hα : α * ∑ j ∈ Finset.range (r + 2), α ^ j * β ^ (r + 1 - j) =
          ∑ j ∈ Finset.range (r + 2), α ^ (j + 1) * β ^ (r + 1 - j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by rw [← mul_assoc, pow_succ']
      have hβ : β * ∑ j ∈ Finset.range (r + 2), α ^ j * β ^ (r + 1 - j) =
          β ^ (r + 2) + ∑ j ∈ Finset.range (r + 1), α ^ (j + 1) * β ^ (r + 1 - j) := by
        rw [Finset.sum_range_succ', pow_zero, one_mul, Nat.sub_zero, mul_add, add_comm (β * _),
            ← pow_succ', Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj' : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hsub : r + 1 - (j + 1) + 1 = r + 1 - j := by omega
        calc β * (α ^ (j + 1) * β ^ (r + 1 - (j + 1)))
            = α ^ (j + 1) * (β ^ (r + 1 - (j + 1)) * β) := by ring
          _ = α ^ (j + 1) * β ^ (r + 1 - j) := by rw [← pow_succ, hsub]
      have hαβ : α * β * ∑ j ∈ Finset.range (r + 1), α ^ j * β ^ (r - j) =
          ∑ j ∈ Finset.range (r + 1), α ^ (j + 1) * β ^ (r + 1 - j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hj' : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hsub : r - j + 1 = r + 1 - j := by omega
        calc α * β * (α ^ j * β ^ (r - j))
            = (α * α ^ j) * (β ^ (r - j) * β) := by ring
          _ = α ^ (j + 1) * β ^ (r + 1 - j) := by rw [← pow_succ', ← pow_succ, hsub]
      rw [hsplit1, add_mul, hα, hβ, hαβ]
      ring

theorem eigenform_prime_pow_eq_satake_sum {N : ℕ} {k : ℕ} {χ : DirichletCharacter ℂ N}
    {f lam : ℕ → ℂ} (hf : IsNormalizedHeckeEigenform k χ f lam)
    {p : ℕ} (hp : p.Prime) {α β : ℂ}
    (hs : IsSatakePair (f p) (χ (p : ZMod N) * (p : ℂ) ^ (k - 1)) α β) (r : ℕ) :
    f (p ^ r) = ∑ j ∈ Finset.range (r + 1), α ^ j * β ^ (r - j) :=
  primePow_eq_satake_sum hs (g := fun m => f (p ^ m)) (by rw [pow_zero, hf.1]) (by rw [pow_one])
    (fun m => eigenform_prime_pow_recurrence hf hp m) r

/-- **Analytic Prime-Power Generating Series Identity**:
Whenever `fun r => g r * z ^ r` is summable and `g` satisfies the degree-2 recurrence
`g 0 = 1`, `g 1 = a_p`, `g (r + 2) = a_p * g (r + 1) - c_p * g r`, we have unconditionally:
`(1 - a_p * z + c_p * z ^ 2) * (∑' r, g r * z ^ r) = 1`. -/
theorem eulerPoly_mul_tsum_primePow {a_p c_p z : ℂ} {g : ℕ → ℂ}
    (hg0 : g 0 = 1) (hg1 : g 1 = a_p)
    (hrec : ∀ r : ℕ, g (r + 2) = a_p * g (r + 1) - c_p * g r)
    (hsum : Summable (fun r : ℕ => g r * z ^ r)) :
    (1 - a_p * z + c_p * z ^ 2) * (∑' r : ℕ, g r * z ^ r) = 1 := by
  have h1 : Summable (fun r : ℕ => g (r + 1) * z ^ (r + 1)) :=
    (summable_nat_add_iff 1).mpr hsum
  have h2 : Summable (fun r : ℕ => g (r + 2) * z ^ (r + 2)) :=
    (summable_nat_add_iff 2).mpr hsum
  have hs0 : ∑' r : ℕ, g r * z ^ r = 1 + a_p * z + ∑' r : ℕ, g (r + 2) * z ^ (r + 2) := by
    rw [hsum.tsum_eq_zero_add, h1.tsum_eq_zero_add]
    simp [hg0, hg1, add_assoc]
  have hs1 : a_p * z * (∑' r : ℕ, g r * z ^ r) =
      a_p * z + ∑' r : ℕ, a_p * g (r + 1) * z ^ (r + 2) := by
    rw [hsum.tsum_eq_zero_add, hg0, pow_zero, mul_one, mul_add, mul_one, ← tsum_mul_left]
    congr 1
    refine tsum_congr fun r => ?_
    ring
  have hs2 : c_p * z ^ 2 * (∑' r : ℕ, g r * z ^ r) =
      ∑' r : ℕ, c_p * g r * z ^ (r + 2) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun r => ?_
    ring
  have h1' : Summable (fun r : ℕ => a_p * g (r + 1) * z ^ (r + 2)) := by
    refine (h1.mul_left (a_p * z)).congr fun r => ?_
    ring
  have h2' : Summable (fun r : ℕ => c_p * g r * z ^ (r + 2)) := by
    refine (hsum.mul_left (c_p * z ^ 2)).congr fun r => ?_
    ring
  have hcancel :
      (∑' r : ℕ, g (r + 2) * z ^ (r + 2)) -
        (∑' r : ℕ, a_p * g (r + 1) * z ^ (r + 2)) +
        (∑' r : ℕ, c_p * g r * z ^ (r + 2)) = 0 := by
    rw [← (h2.tsum_sub h1'), ← ((h2.sub h1').tsum_add h2')]
    convert tsum_zero with r
    rw [hrec r]
    ring
  calc (1 - a_p * z + c_p * z ^ 2) * (∑' r : ℕ, g r * z ^ r)
      = (∑' r : ℕ, g r * z ^ r) - a_p * z * (∑' r : ℕ, g r * z ^ r) +
          c_p * z ^ 2 * (∑' r : ℕ, g r * z ^ r) := by ring
    _ = (1 + a_p * z + ∑' r : ℕ, g (r + 2) * z ^ (r + 2)) -
          (a_p * z + ∑' r : ℕ, a_p * g (r + 1) * z ^ (r + 2)) +
          (∑' r : ℕ, c_p * g r * z ^ (r + 2)) := by rw [hs1, hs2, hs0]
    _ = 1 + ((∑' r : ℕ, g (r + 2) * z ^ (r + 2)) -
          (∑' r : ℕ, a_p * g (r + 1) * z ^ (r + 2)) +
          (∑' r : ℕ, c_p * g r * z ^ (r + 2))) := by ring
    _ = 1 := by rw [hcancel, add_zero]

/-- Exact convergent local Euler-factor identity:
`∑' r, g r * z ^ r = (1 - a_p * z + c_p * z ^ 2)⁻¹`. -/
theorem tsum_primePow_eq_inv_eulerPoly {a_p c_p z : ℂ} {g : ℕ → ℂ}
    (hg0 : g 0 = 1) (hg1 : g 1 = a_p)
    (hrec : ∀ r : ℕ, g (r + 2) = a_p * g (r + 1) - c_p * g r)
    (hsum : Summable (fun r : ℕ => g r * z ^ r)) :
    (∑' r : ℕ, g r * z ^ r) = (1 - a_p * z + c_p * z ^ 2)⁻¹ := by
  have hmul := eulerPoly_mul_tsum_primePow hg0 hg1 hrec hsum
  have hne : 1 - a_p * z + c_p * z ^ 2 ≠ 0 := left_ne_zero_of_mul_eq_one hmul
  exact eq_inv_of_mul_eq_one_right hmul

/-- Exact convergent Satake-factored local Euler-factor identity:
`∑' r, g r * z ^ r = ((1 - α * z) * (1 - β * z))⁻¹`. -/
theorem tsum_primePow_eq_inv_satake {a_p c_p α β z : ℂ}
    (hs : IsSatakePair a_p c_p α β) {g : ℕ → ℂ}
    (hg0 : g 0 = 1) (hg1 : g 1 = a_p)
    (hrec : ∀ r : ℕ, g (r + 2) = a_p * g (r + 1) - c_p * g r)
    (hsum : Summable (fun r : ℕ => g r * z ^ r)) :
    (∑' r : ℕ, g r * z ^ r) = ((1 - α * z) * (1 - β * z))⁻¹ := by
  rw [tsum_primePow_eq_inv_eulerPoly hg0 hg1 hrec hsum, eulerPoly_eq_satake_prod hs]

/-- Direct convergence from Satake norm bounds `‖α * z‖ < 1` and `‖β * z‖ < 1`, yielding
`HasSum (fun r => g r * z ^ r) (((1 - α * z) * (1 - β * z))⁻¹)`. -/
theorem hasSum_primePow_of_satake_norm_lt_one {a_p c_p α β z : ℂ}
    (hs : IsSatakePair a_p c_p α β) {g : ℕ → ℂ}
    (hg0 : g 0 = 1) (hg1 : g 1 = a_p)
    (hrec : ∀ r : ℕ, g (r + 2) = a_p * g (r + 1) - c_p * g r)
    (hα : ‖α * z‖ < 1) (hβ : ‖β * z‖ < 1) :
    HasSum (fun r : ℕ => g r * z ^ r) (((1 - α * z) * (1 - β * z))⁻¹) := by
  have hsumα : Summable (fun i : ℕ => ‖(α * z) ^ i‖) := by
    simp_rw [norm_pow]
    exact summable_geometric_of_lt_one (norm_nonneg _) hα
  have hsumβ : Summable (fun j : ℕ => ‖(β * z) ^ j‖) := by
    simp_rw [norm_pow]
    exact summable_geometric_of_lt_one (norm_nonneg _) hβ
  have hsum : Summable (fun r : ℕ => g r * z ^ r) := by
    have hnorm : Summable (fun r : ℕ => ‖g r * z ^ r‖) := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun r => ?_)
        (summable_sum_mul_antidiagonal_of_summable_mul
          (f := fun i : ℕ => ‖(α * z) ^ i‖) (g := fun j : ℕ => ‖(β * z) ^ j‖)
          (hsumα.mul_of_nonneg hsumβ (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)))
      rw [primePow_eq_satake_sum hs hg0 hg1 hrec r, Finset.sum_mul]
      calc ‖∑ j ∈ Finset.range (r + 1), α ^ j * β ^ (r - j) * z ^ r‖
          ≤ ∑ j ∈ Finset.range (r + 1), ‖α ^ j * β ^ (r - j) * z ^ r‖ := norm_sum_le _ _
        _ = ∑ p ∈ Finset.antidiagonal r, ‖(α * z) ^ p.1‖ * ‖(β * z) ^ p.2‖ := by
            rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
              (fun i j => ‖(α * z) ^ i‖ * ‖(β * z) ^ j‖)]
            refine Finset.sum_congr rfl fun j hj => ?_
            have hj' : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
            rw [← norm_mul, mul_pow, mul_pow]
            congr 1
            calc α ^ j * β ^ (r - j) * z ^ r
                = α ^ j * β ^ (r - j) * z ^ (j + (r - j)) := by rw [Nat.add_sub_of_le hj']
              _ = α ^ j * z ^ j * (β ^ (r - j) * z ^ (r - j)) := by rw [pow_add]; ring
    exact hnorm.of_norm
  rw [← tsum_primePow_eq_inv_satake hs hg0 hg1 hrec hsum]
  exact hsum.hasSum

end SatakeAndLocalSeries

/-! ## Section 5: Unconditional Convergence & Exact Degree-2 `GL_2` Euler Product -/

section Degree2EulerProduct

/-- Exact degree-2 local Euler factor at prime `p` for weight `k`, Nebentypus `χ`, and
coefficient `a_p`: `(1 - a_p · p^{-s} + χ(p) · p^{k - 1 - 2s})⁻¹`. -/
def degree2EulerFactor {N : ℕ} (k : ℕ) (χ : DirichletCharacter ℂ N)
    (a_p : ℂ) (p : ℕ) (s : ℂ) : ℂ :=
  (1 - a_p * (p : ℂ) ^ (-s) +
    χ (p : ZMod N) * (p : ℂ) ^ (((k - 1 : ℕ) : ℂ) - 2 * s))⁻¹

private theorem cpow_prime_pow_neg (p : ℕ) (s : ℂ) (r : ℕ) :
    (((p ^ r : ℕ) : ℂ) ^ s)⁻¹ = ((p : ℂ) ^ (-s)) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, Nat.cast_mul]
    have hmul : (((p ^ r : ℕ) : ℂ) * (p : ℂ)) ^ s = (((p ^ r : ℕ) : ℂ) ^ s) * ((p : ℂ) ^ s) := by
      simpa [Complex.ofReal_natCast] using
        Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg (p ^ r)) (Nat.cast_nonneg p) s
    rw [hmul, mul_inv, ih, ← Complex.cpow_neg, pow_succ]

private theorem cpow_k_sub_one_sub_two_mul {p : ℕ} (hp : p.Prime) (k : ℕ) (s : ℂ) :
    (p : ℂ) ^ (k - 1) * ((p : ℂ) ^ (-s)) ^ 2 =
      (p : ℂ) ^ (((k - 1 : ℕ) : ℂ) - 2 * s) := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  rw [← Complex.cpow_natCast (p : ℂ) (k - 1), ← Complex.cpow_nat_mul,
      ← Complex.cpow_add _ _ hp0]
  congr 1
  ring

private theorem LSeries_term_prime_pow {p : ℕ} (hp : p.Prime) (f : ℕ → ℂ) (s : ℂ) (r : ℕ) :
    LSeries.term f s (p ^ r) = f (p ^ r) * ((p : ℂ) ^ (-s)) ^ r := by
  have hne : p ^ r ≠ 0 := pow_ne_zero r hp.ne_zero
  rw [LSeries.term_of_ne_zero hne, div_eq_mul_inv, cpow_prime_pow_neg p s r]

private theorem LSeries_term_mul_of_coprime {N : ℕ} {k : ℕ} {χ : DirichletCharacter ℂ N}
    {f lam : ℕ → ℂ} (hf : IsNormalizedHeckeEigenform k χ f lam) (s : ℂ)
    {m n : ℕ} (hcop : Nat.Coprime m n) :
    LSeries.term f s (m * n) = LSeries.term f s m * LSeries.term f s n := by
  by_cases hm : m = 0
  · subst hm; simp
  by_cases hn : n = 0
  · subst hn; simp
  have hmn : m * n ≠ 0 := mul_ne_zero hm hn
  rw [LSeries.term_of_ne_zero hmn, LSeries.term_of_ne_zero hm, LSeries.term_of_ne_zero hn,
      eigenform_isMultiplicative hf (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn) hcop,
      Nat.cast_mul]
  have hcpow : ((m : ℂ) * (n : ℂ)) ^ s = (m : ℂ) ^ s * (n : ℂ) ^ s := by
    have hm' : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hn' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    simpa [Complex.ofReal_natCast] using Complex.mul_cpow_ofReal_nonneg hm' hn' s
  rw [hcpow, mul_div_mul_comm]

/-- Local prime-`p` sum of `LSeries.term f s (p ^ r)` equals the exact degree-2 Euler factor
for any normalized Hecke eigenform whenever `LSeriesSummable f s`. -/
theorem eigenform_tsum_prime_pow_LSeries_term {N : ℕ} {k : ℕ} {χ : DirichletCharacter ℂ N}
    {f lam : ℕ → ℂ} (hf : IsNormalizedHeckeEigenform k χ f lam)
    {s : ℂ} (hs : LSeriesSummable f s) {p : ℕ} (hp : p.Prime) :
    (∑' r : ℕ, LSeries.term f s (p ^ r)) = degree2EulerFactor k χ (f p) p s := by
  have hinj : Function.Injective (fun r : ℕ => p ^ r) := Nat.pow_right_injective hp.two_le
  have hsub : Summable (fun r : ℕ => LSeries.term f s (p ^ r)) := hs.comp_injective hinj
  have hsub' : Summable (fun r : ℕ => f (p ^ r) * ((p : ℂ) ^ (-s)) ^ r) := by
    simpa only [LSeries_term_prime_pow hp] using hsub
  simp_rw [LSeries_term_prime_pow hp]
  rw [tsum_primePow_eq_inv_eulerPoly (by simp [hf.1]) (by simp)
        (fun r => eigenform_prime_pow_recurrence hf hp r) hsub']
  simp only [degree2EulerFactor]
  congr 1
  rw [mul_assoc, cpow_k_sub_one_sub_two_mul hp k s]

/-- **Master Unconditional Degree-2 `GL_2` Euler Product Theorem** on Mathlib's `LSeries`:
for ANY normalized Hecke eigenform `(f, lam)` of weight `k` and Nebentypus `χ`, and ANY `s : ℂ`
with `LSeriesSummable f s`:
`∏' (p : Nat.Primes), (1 - f p * p^{-s} + χ p * p^{k - 1 - 2s})⁻¹ = LSeries f s`. -/
theorem eigenform_LSeries_eulerProduct {N : ℕ} {k : ℕ} {χ : DirichletCharacter ℂ N}
    {f lam : ℕ → ℂ} (hf : IsNormalizedHeckeEigenform k χ f lam)
    {s : ℂ} (hs : LSeriesSummable f s) :
    (∏' (p : Nat.Primes), degree2EulerFactor k χ (f p) p s) = LSeries f s := by
  have h1 : LSeries.term f s 1 = 1 := by simp [LSeries.term_of_ne_zero, hf.1]
  have h0 : LSeries.term f s 0 = 0 := LSeries.term_zero f s
  have hnorm : Summable (fun n : ℕ => ‖LSeries.term f s n‖) := hs.norm
  have heuler := EulerProduct.eulerProduct_tprod h1 (LSeries_term_mul_of_coprime hf s) hnorm h0
  rw [LSeries, ← heuler]
  refine tprod_congr fun p => ?_
  exact (eigenform_tsum_prime_pow_LSeries_term hf hs p.prop).symm

/-- Finite-prime-product convergence (`Filter.Tendsto`) form of the degree-2 `GL_2` Euler product. -/
theorem eigenform_LSeries_eulerProduct_tendsto {N : ℕ} {k : ℕ} {χ : DirichletCharacter ℂ N}
    {f lam : ℕ → ℂ} (hf : IsNormalizedHeckeEigenform k χ f lam)
    {s : ℂ} (hs : LSeriesSummable f s) :
    Filter.Tendsto
      (fun B : ℕ => ∏ p ∈ B.primesBelow, degree2EulerFactor k χ (f p) p s)
      Filter.atTop (nhds (LSeries f s)) := by
  have h1 : LSeries.term f s 1 = 1 := by simp [LSeries.term_of_ne_zero, hf.1]
  have h0 : LSeries.term f s 0 = 0 := LSeries.term_zero f s
  have hnorm : Summable (fun n : ℕ => ‖LSeries.term f s n‖) := hs.norm
  have heuler := EulerProduct.eulerProduct h1 (LSeries_term_mul_of_coprime hf s) hnorm h0
  refine heuler.congr fun B => ?_
  refine Finset.prod_congr rfl fun p hp => ?_
  exact eigenform_tsum_prime_pow_LSeries_term hf hs (Nat.prime_of_mem_primesBelow hp)

/-- Exact degree-2 Euler product expressed in terms of Satake parameters `(α p, β p)` at every prime. -/
theorem eigenform_LSeries_eulerProduct_satake {N : ℕ} {k : ℕ} {χ : DirichletCharacter ℂ N}
    {f lam : ℕ → ℂ} (hf : IsNormalizedHeckeEigenform k χ f lam)
    (α β : Nat.Primes → ℂ)
    (hsat : ∀ p : Nat.Primes,
      IsSatakePair (f p) (χ ((p : ℕ) : ZMod N) * ((p : ℕ) : ℂ) ^ (k - 1)) (α p) (β p))
    {s : ℂ} (hs : LSeriesSummable f s) :
    (∏' (p : Nat.Primes),
      ((1 - α p * ((p : ℕ) : ℂ) ^ (-s)) * (1 - β p * ((p : ℕ) : ℂ) ^ (-s)))⁻¹) =
      LSeries f s := by
  rw [← eigenform_LSeries_eulerProduct hf hs]
  refine tprod_congr fun p => ?_
  simp only [degree2EulerFactor]
  congr 1
  rw [← eulerPoly_eq_satake_prod (hsat p), mul_assoc,
      cpow_k_sub_one_sub_two_mul p.prop k s]

/-- Every local degree-2 Euler factor is nonzero in the region of absolute convergence. -/
theorem degree2EulerFactor_ne_zero {N : ℕ} {k : ℕ} {χ : DirichletCharacter ℂ N}
    {f lam : ℕ → ℂ} (hf : IsNormalizedHeckeEigenform k χ f lam)
    {s : ℂ} (hs : LSeriesSummable f s) {p : ℕ} (hp : p.Prime) :
    degree2EulerFactor k χ (f p) p s ≠ 0 := by
  have hinj : Function.Injective (fun r : ℕ => p ^ r) := Nat.pow_right_injective hp.two_le
  have hsub : Summable (fun r : ℕ => f (p ^ r) * ((p : ℂ) ^ (-s)) ^ r) := by
    simpa only [Function.comp_def, LSeries_term_prime_pow hp] using hs.comp_injective hinj
  have hmul := eulerPoly_mul_tsum_primePow (by simp [hf.1]) (by simp)
    (fun r => eigenform_prime_pow_recurrence hf hp r) hsub
  have hne : 1 - f p * (p : ℂ) ^ (-s) +
      χ (p : ZMod N) * (p : ℂ) ^ (k - 1) * ((p : ℂ) ^ (-s)) ^ 2 ≠ 0 :=
    left_ne_zero_of_mul_eq_one hmul
  rw [mul_assoc, cpow_k_sub_one_sub_two_mul hp k s] at hne
  exact inv_ne_zero hne

/-- Unconditional `LSeriesSummable` from any polynomial coefficient bound `‖f n‖ ≤ C * n^σ`
in the half-plane `Re(s) > σ + 1`. -/
theorem LSeriesSummable_of_poly_bound {f : ℕ → ℂ} {C σ : ℝ}
    (hbound : ∀ n : ℕ, 1 ≤ n → ‖f n‖ ≤ C * (n : ℝ) ^ σ)
    {s : ℂ} (hs : σ + 1 < s.re) :
    LSeriesSummable f s := by
  refine LSeriesSummable_of_isBigO_rpow (x := σ + 1) hs ?_
  rw [Asymptotics.isBigO_iff]
  refine ⟨C, Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩⟩
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) ^ σ := Real.rpow_nonneg (Nat.cast_nonneg n) σ
  simp only [add_sub_cancel_right, Real.norm_eq_abs, abs_of_nonneg hn_nonneg]
  exact hbound n hn

/-- Unconditional degree-2 `GL_2` Euler product in the half-plane `Re(s) > σ + 1` given any
polynomial coefficient bound `‖f n‖ ≤ C * n^σ` (covering Hecke `σ = k / 2`, Deligne
`σ = (k - 1) / 2 + ε`, and general modular forms `σ = k`). -/
theorem eigenform_LSeries_eulerProduct_of_poly_bound {N : ℕ} {k : ℕ}
    {χ : DirichletCharacter ℂ N} {f lam : ℕ → ℂ}
    (hf : IsNormalizedHeckeEigenform k χ f lam)
    {C σ : ℝ}
    (hbound : ∀ n : ℕ, 1 ≤ n → ‖f n‖ ≤ C * (n : ℝ) ^ σ)
    {s : ℂ} (hs : σ + 1 < s.re) :
    (∏' (p : Nat.Primes), degree2EulerFactor k χ (f p) p s) = LSeries f s :=
  eigenform_LSeries_eulerProduct hf (LSeriesSummable_of_poly_bound hbound hs)

/-- **Direct Bridge to Mathlib's `CuspForm` and `ModularForm.L`**:
For ANY Mathlib `CuspForm Γ k` (`0 < k`, `Γ.IsArithmetic`, `Γ.strictWidthInfty = 1`) whose
`q`-expansion coefficients form a normalized Hecke eigenform of weight `k.toNat` and Nebentypus
`χ`, Mathlib's analytic `ModularForm.L hk f s` equals the exact degree-2 `GL_2` Euler product
on the half-plane `Re(s) > k / 2 + 1` (unconditionally via Mathlib's `CuspFormClass.qExpansion_isBigO`
and `CuspForm.hasSum_L`). -/
theorem cuspForm_eigenform_L_eulerProduct
    {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (hwidth : Γ.strictWidthInfty = 1)
    {k : ℤ} (hk : 0 < k) (f : CuspForm Γ k)
    {N : ℕ} (χ : DirichletCharacter ℂ N) (lam : ℕ → ℂ)
    (heig : IsNormalizedHeckeEigenform k.toNat χ
      (fun n => PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (⇑f))) lam)
    {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    (∏' (p : Nat.Primes),
      degree2EulerFactor k.toNat χ
        (PowerSeries.coeff (p : ℕ) (UpperHalfPlane.qExpansion 1 (⇑f))) p s) =
      ModularForm.L hk f s := by
  set a : ℕ → ℂ := fun n => PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (⇑f))
  have hbigO : a =O[Filter.atTop] fun n : ℕ => ((n : ℝ) ^ ((k : ℝ) / 2)) := by
    have h := CuspFormClass.qExpansion_isBigO f
    rw [hwidth] at h
    exact h
  have hsum : LSeriesSummable a s := by
    refine LSeriesSummable_of_isBigO_rpow (x := (k : ℝ) / 2 + 1) hs ?_
    simpa [add_sub_cancel_right] using hbigO
  have hs_ne : s ≠ 0 := by
    intro hs0
    have hk_pos : (0 : ℝ) < (k : ℝ) := Int.cast_pos.mpr hk
    rw [hs0, Complex.zero_re] at hs
    linarith
  have hL : LSeries a s = ModularForm.L hk f s := by
    have hhas := CuspForm.hasSum_L hk f hs
    rw [hwidth, Complex.ofReal_one, Complex.one_cpow, one_mul] at hhas
    have hhas' : HasSum (LSeries.term a s) (ModularForm.L hk f s) := by
      refine hhas.congr_fun fun n => ?_
      by_cases hn : n = 0
      · subst hn
        simp [Complex.zero_cpow hs_ne]
      · simp [a, LSeries.term_of_ne_zero hn]
    exact hhas'.tsum_eq
  rw [← hL]
  exact eigenform_LSeries_eulerProduct heig hsum

end Degree2EulerProduct

/-! ## Section 6: Ramanujan–Petersson Equivalence & Unramified `GL_2` Satake Weil–Deligne Bridge -/

section RamanujanPeterssonAndSatakeWD

/-- Every Dirichlet character takes values of norm `1` on integers coprime to the modulus `N`. -/
theorem norm_dirichletChar_eq_one_of_coprime {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {n : ℕ} (hcop : Nat.Coprime n N) :
    ‖χ (n : ZMod N)‖ = 1 := by
  have hu : IsUnit (n : ZMod N) := (ZMod.isUnit_iff_coprime n N).mpr hcop
  rcases hu with ⟨u, hu⟩
  rw [← hu]
  have hord : ∃ m : ℕ, 0 < m ∧ (χ (u : ZMod N)) ^ m = 1 := by
    refine ⟨Fintype.card (ZMod N)ˣ, Fintype.card_pos, ?_⟩
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
  rcases hord with ⟨m, hm, hpow⟩
  have hnorm_pow : ‖χ (u : ZMod N)‖ ^ m = 1 := by
    rw [← norm_pow, hpow, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (ne_of_gt hm)).mp hnorm_pow

/-- **Core Ramanujan–Petersson Algebraic Equivalence**:
For any positive real radius `R > 0`, unit complex number `u` (`‖u‖ = 1`), and Satake pair
`α + β = a_p`, `α * β = u * R^2`:
`(‖α‖ = R ∧ ‖β‖ = R) ↔ (‖a_p‖ ≤ 2 * R ∧ star a_p = star u * a_p)`. -/
theorem ramanujan_petersson_core {R : ℝ} (hR : 0 < R) {u a_p α β : ℂ}
    (hu : ‖u‖ = 1) (hsum : α + β = a_p) (hprod : α * β = u * ((R : ℂ) ^ 2)) :
    (‖α‖ = R ∧ ‖β‖ = R) ↔ (‖a_p‖ ≤ 2 * R ∧ star a_p = star u * a_p) := by
  have hu_mul : u * star u = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hu, one_pow,
        Complex.ofReal_one]
  have hR_ne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hR)
  have hnorm_prod : ‖α‖ * ‖β‖ = R ^ 2 := by
    rw [← norm_mul, hprod, norm_mul, hu, one_mul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hR]
  have hα_pos : 0 < ‖α‖ := by
    by_contra h
    have h0 : ‖α‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg α)
    rw [h0, zero_mul] at hnorm_prod
    nlinarith
  have hβ_pos : 0 < ‖β‖ := by
    by_contra h
    have h0 : ‖β‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg β)
    rw [h0, mul_zero] at hnorm_prod
    nlinarith
  constructor
  · rintro ⟨hα, hβ⟩
    refine ⟨?_, ?_⟩
    · calc ‖a_p‖ = ‖α + β‖ := by rw [hsum]
        _ ≤ ‖α‖ + ‖β‖ := norm_add_le α β
        _ = 2 * R := by rw [hα, hβ]; ring
    · have hα_conj : α * star α = (R : ℂ) ^ 2 := by
        rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hα, Complex.ofReal_pow]
      have hβ_conj : β * star β = (R : ℂ) ^ 2 := by
        rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hβ, Complex.ofReal_pow]
      have h1 : u * (R : ℂ) ^ 2 * star a_p = (R : ℂ) ^ 2 * a_p := by
        calc u * (R : ℂ) ^ 2 * star a_p
            = α * β * (star α + star β) := by rw [← hprod, ← hsum, star_add]
          _ = (α * star α) * β + α * (β * star β) := by ring
          _ = (R : ℂ) ^ 2 * (α + β) := by rw [hα_conj, hβ_conj]; ring
          _ = (R : ℂ) ^ 2 * a_p := by rw [hsum]
      have h2 : u * star a_p = a_p := by
        apply mul_left_cancel₀ (pow_ne_zero 2 hR_ne)
        calc (R : ℂ) ^ 2 * (u * star a_p) = u * (R : ℂ) ^ 2 * star a_p := by ring
          _ = (R : ℂ) ^ 2 * a_p := h1
      calc star a_p = star u * (u * star a_p) := by rw [← mul_assoc, mul_comm (star u) u, hu_mul, one_mul]
        _ = star u * a_p := by rw [h2]
  · rintro ⟨hle, hsa⟩
    have hu_sa : u * star a_p = a_p := by
      rw [hsa, ← mul_assoc, hu_mul, one_mul]
    have hα_conj : α * star α = ((‖α‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hβ_conj : β * star β = ((‖β‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hrel :
        ((‖α‖ ^ 2 : ℝ) : ℂ) * β + ((‖β‖ ^ 2 : ℝ) : ℂ) * α =
          ((R ^ 2 : ℝ) : ℂ) * α + ((R ^ 2 : ℝ) : ℂ) * β := by
      have h1 : α * β * (star α + star β) = (R : ℂ) ^ 2 * (α + β) := by
        calc α * β * (star α + star β)
            = u * (R : ℂ) ^ 2 * star a_p := by rw [hprod, ← hsum, star_add]
          _ = (R : ℂ) ^ 2 * (u * star a_p) := by ring
          _ = (R : ℂ) ^ 2 * (α + β) := by rw [hu_sa, hsum]
      calc ((‖α‖ ^ 2 : ℝ) : ℂ) * β + ((‖β‖ ^ 2 : ℝ) : ℂ) * α
          = (α * star α) * β + (β * star β) * α := by rw [hα_conj, hβ_conj]
        _ = α * β * (star α + star β) := by ring
        _ = (R : ℂ) ^ 2 * (α + β) := h1
        _ = ((R ^ 2 : ℝ) : ℂ) * α + ((R ^ 2 : ℝ) : ℂ) * β := by push_cast; ring
    have hprod_sq : ((‖α‖ ^ 2 : ℝ) : ℂ) * ((‖β‖ ^ 2 : ℝ) : ℂ) =
        ((R ^ 2 : ℝ) : ℂ) * ((R ^ 2 : ℝ) : ℂ) := by
      exact_mod_cast (by nlinarith [hnorm_prod] : ‖α‖ ^ 2 * ‖β‖ ^ 2 = R ^ 2 * R ^ 2)
    have hfact :
        (((‖α‖ ^ 2 : ℝ) : ℂ) - ((R ^ 2 : ℝ) : ℂ)) *
          (((‖α‖ ^ 2 : ℝ) : ℂ) * β - ((R ^ 2 : ℝ) : ℂ) * α) = 0 := by
      have hcomb :
          ((‖α‖ ^ 2 : ℝ) : ℂ) *
              (((‖α‖ ^ 2 : ℝ) : ℂ) * β + ((‖β‖ ^ 2 : ℝ) : ℂ) * α -
                (((R ^ 2 : ℝ) : ℂ) * α + ((R ^ 2 : ℝ) : ℂ) * β)) = 0 := by
        rw [hrel, sub_self, mul_zero]
      calc (((‖α‖ ^ 2 : ℝ) : ℂ) - ((R ^ 2 : ℝ) : ℂ)) *
              (((‖α‖ ^ 2 : ℝ) : ℂ) * β - ((R ^ 2 : ℝ) : ℂ) * α)
          = ((‖α‖ ^ 2 : ℝ) : ℂ) * (((‖α‖ ^ 2 : ℝ) : ℂ) * β) +
              ((R ^ 2 : ℝ) : ℂ) * ((R ^ 2 : ℝ) : ℂ) * α -
              ((‖α‖ ^ 2 : ℝ) : ℂ) * (((R ^ 2 : ℝ) : ℂ) * α + ((R ^ 2 : ℝ) : ℂ) * β) := by ring
        _ = ((‖α‖ ^ 2 : ℝ) : ℂ) *
              (((‖α‖ ^ 2 : ℝ) : ℂ) * β + ((‖β‖ ^ 2 : ℝ) : ℂ) * α -
                (((R ^ 2 : ℝ) : ℂ) * α + ((R ^ 2 : ℝ) : ℂ) * β)) := by
            rw [← hprod_sq]; ring
        _ = 0 := hcomb
    have hα_eq_R : ‖α‖ = R := by
      rcases mul_eq_zero.mp hfact with hcase1 | hcase2
      · have hsq : ‖α‖ ^ 2 = R ^ 2 := by
          have : ((‖α‖ ^ 2 - R ^ 2 : ℝ) : ℂ) = 0 := by rw [Complex.ofReal_sub]; exact hcase1
          linarith [Complex.ofReal_eq_zero.mp this]
        nlinarith
      · have hβ_eq : ((‖α‖ ^ 2 : ℝ) : ℂ) * β = ((R ^ 2 : ℝ) : ℂ) * α := sub_eq_zero.mp hcase2
        have hap_eq : ((‖α‖ ^ 2 : ℝ) : ℂ) * a_p = ((‖α‖ ^ 2 + R ^ 2 : ℝ) : ℂ) * α := by
          calc ((‖α‖ ^ 2 : ℝ) : ℂ) * a_p
              = ((‖α‖ ^ 2 : ℝ) : ℂ) * α + ((‖α‖ ^ 2 : ℝ) : ℂ) * β := by rw [← hsum, mul_add]
            _ = ((‖α‖ ^ 2 : ℝ) : ℂ) * α + ((R ^ 2 : ℝ) : ℂ) * α := by rw [hβ_eq]
            _ = ((‖α‖ ^ 2 + R ^ 2 : ℝ) : ℂ) * α := by push_cast; ring
        have hnorm_eq := congrArg norm hap_eq
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs] at hnorm_eq
        rw [abs_of_nonneg (sq_nonneg ‖α‖), abs_of_nonneg (by positivity)] at hnorm_eq
        have hmul_le : ‖α‖ ^ 2 * ‖a_p‖ ≤ ‖α‖ ^ 2 * (2 * R) :=
          mul_le_mul_of_nonneg_left hle (sq_nonneg ‖α‖)
        have hsq_le : (‖α‖ ^ 2 + R ^ 2) * ‖α‖ ≤ ‖α‖ ^ 2 * (2 * R) := hnorm_eq ▸ hmul_le
        have hdiff : (‖α‖ - R) ^ 2 * ‖α‖ ≤ 0 := by nlinarith
        have hdiff0 : (‖α‖ - R) ^ 2 ≤ 0 := nonpos_of_mul_nonpos_left hdiff hα_pos
        nlinarith [sq_nonneg (‖α‖ - R)]
    refine ⟨hα_eq_R, ?_⟩
    rw [hα_eq_R] at hnorm_prod
    nlinarith

/-- **Ramanujan–Petersson Equivalence for Weight-`k` Modular Forms with Unitary Nebentypus `χ(p)`**:
At any prime `p` with `‖χ(p)‖ = 1` (in particular every unramified prime `p ∤ N`), for Satake
parameters `α + β = a_p`, `α * β = χ(p) * p^(k - 1)`:
`(‖α‖ = p^((k - 1)/2) ∧ ‖β‖ = p^((k - 1)/2)) ↔ (‖a_p‖ ≤ 2 * p^((k - 1)/2) ∧ star a_p = star (χ p) * a_p)`. -/
theorem ramanujan_petersson_iff {N : ℕ} {k : ℕ} (χ : DirichletCharacter ℂ N)
    {p : ℕ} (hp : p.Prime) (hu : ‖χ (p : ZMod N)‖ = 1)
    {a_p α β : ℂ} (hs : IsSatakePair a_p (χ (p : ZMod N) * (p : ℂ) ^ (k - 1)) α β) :
    (‖α‖ = (p : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2) ∧ ‖β‖ = (p : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) ↔
      (‖a_p‖ ≤ 2 * (p : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2) ∧
        star a_p = star (χ (p : ZMod N)) * a_p) := by
  set R : ℝ := (p : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  have hR_pos : 0 < R := Real.rpow_pos_of_pos hp_pos _
  have hR_sq : ((R : ℂ) ^ 2) = (p : ℂ) ^ (k - 1) := by
    have hR_sq_real : R ^ 2 = (p : ℝ) ^ (k - 1) := by
      simp only [R, ← Real.rpow_natCast (p : ℝ) (k - 1), ← Real.rpow_natCast _ 2,
        ← Real.rpow_mul hp_pos.le]
      congr 1
      ring
    exact_mod_cast hR_sq_real
  exact ramanujan_petersson_core hR_pos hu hs.1 (by rw [hs.2, hR_sq])

/-- Under Hecke self-adjointness `star a_p = star (χ p) * a_p` (e.g., for every cuspidal
Hecke eigenform by Petersson adjointness `T_p^* = χ(p)⁻¹ T_p`), Ramanujan–Petersson holds
iff `‖a_p‖ ≤ 2 * p^((k - 1) / 2)`. -/
theorem ramanujan_petersson_iff_of_selfAdjoint {N : ℕ} [NeZero N] {k : ℕ}
    (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p N)
    {a_p α β : ℂ} (hs : IsSatakePair a_p (χ (p : ZMod N) * (p : ℂ) ^ (k - 1)) α β)
    (hsa : star a_p = star (χ (p : ZMod N)) * a_p) :
    (‖α‖ = (p : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2) ∧ ‖β‖ = (p : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) ↔
      ‖a_p‖ ≤ 2 * (p : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2) := by
  have hu := norm_dirichletChar_eq_one_of_coprime χ hcop
  rw [ramanujan_petersson_iff χ hp hu hs]
  exact ⟨fun h => h.1, fun h => ⟨h, hsa⟩⟩

/-- For trivial/real-valued Nebentypus `χ(p) = 1` and real `a_p` (`a_p.im = 0`),
`‖α‖ = ‖β‖ = p^((k - 1)/2) ↔ ‖a_p‖ ≤ 2 * p^((k - 1)/2)`. -/
theorem ramanujan_petersson_iff_real {N : ℕ} {k : ℕ}
    (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (hχ : χ (p : ZMod N) = 1)
    {a_p α β : ℂ} (hs : IsSatakePair a_p (χ (p : ZMod N) * (p : ℂ) ^ (k - 1)) α β)
    (hreal : a_p.im = 0) :
    (‖α‖ = (p : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2) ∧ ‖β‖ = (p : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) ↔
      ‖a_p‖ ≤ 2 * (p : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2) := by
  have hu : ‖χ (p : ZMod N)‖ = 1 := by rw [hχ, norm_one]
  have hsa : star a_p = star (χ (p : ZMod N)) * a_p := by
    rw [hχ, star_one, one_mul]
    exact Complex.conj_eq_iff_im.mpr hreal
  rw [ramanujan_petersson_iff χ hp hu hs]
  exact ⟨fun h => h.1, fun h => ⟨h, hsa⟩⟩

/-! ### Unramified 2-Dimensional Satake Weil–Deligne Representation (`RHDirect.LocalLanglands.WDRep`) -/

/-- Diagonal `GL₂(ℂ)` matrix attached to nonzero `(u, v : ℂ)`. -/
def diagGL2 (u v : ℂ) (hu : u ≠ 0) (hv : v ≠ 0) : Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![u, 0; 0, v] (by
    simp [Matrix.det_fin_two, hu, hv])

/-- Concrete unramified 2-dimensional Weil–Deligne representation `WDRep W 2` attached to
nonzero Satake parameters `(α, β)` at a local Weil group `W : WDGroup`:
`ρ(σ) = diag(α^{deg σ}, β^{deg σ})` and trivial monodromy `N = 0`. -/
def satakeWDRep (W : RHDirect.LocalLanglands.WDGroup) (α β : ℂ) (hα : α ≠ 0) (hβ : β ≠ 0) :
    RHDirect.LocalLanglands.WDRep W 2 where
  ρ :=
    { toFun := fun σ => diagGL2 (α ^ W.deg σ) (β ^ W.deg σ) (zpow_ne_zero _ hα) (zpow_ne_zero _ hβ)
      map_one' := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [diagGL2, W.deg_one]
      map_mul' := fun σ τ => by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [diagGL2, W.deg_mul, zpow_add₀ hα, zpow_add₀ hβ, Matrix.mul_apply, Fin.sum_univ_two] }
  N := 0
  nilp := IsNilpotent.zero
  compat := fun σ => by simp

/-- At any Frobenius element `φ ∈ W.G` (`W.deg φ = 1`), the trace of `satakeWDRep` equals `a_p`. -/
theorem satakeWDRep_trace_frob (W : RHDirect.LocalLanglands.WDGroup)
    {a_p c_p α β : ℂ} (hα : α ≠ 0) (hβ : β ≠ 0) (hs : IsSatakePair a_p c_p α β)
    {φ : W.G} (hφ : W.deg φ = 1) :
    Matrix.trace ((satakeWDRep W α β hα hβ).ρ φ : Matrix (Fin 2) (Fin 2) ℂ) = a_p := by
  simp [satakeWDRep, diagGL2, Matrix.trace, Matrix.diag, Fin.sum_univ_two, hφ, hs.1]

/-- At any Frobenius element `φ ∈ W.G` (`W.deg φ = 1`), the Weil–Deligne determinant `wdDet`
equals `c_p = χ(p) · p^(k - 1)`. -/
theorem satakeWDRep_wdDet_frob (W : RHDirect.LocalLanglands.WDGroup)
    {a_p c_p α β : ℂ} (hα : α ≠ 0) (hβ : β ≠ 0) (hs : IsSatakePair a_p c_p α β)
    {φ : W.G} (hφ : W.deg φ = 1) :
    (satakeWDRep W α β hα hβ).wdDet φ = c_p := by
  simp [RHDirect.LocalLanglands.WDRep.wdDet, satakeWDRep, diagGL2, Matrix.det_fin_two, hφ, hs.2]

/-- `satakeWDRep` is unramified / tame (trivial on `W.wild`). -/
theorem satakeWDRep_isTame (W : RHDirect.LocalLanglands.WDGroup)
    (α β : ℂ) (hα : α ≠ 0) (hβ : β ≠ 0) :
    (satakeWDRep W α β hα hβ).IsTame := by
  intro σ hσ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [satakeWDRep, diagGL2, W.deg_wild σ hσ]

/-- Exact characteristic polynomial of Frobenius in `satakeWDRep`:
`charPol φ = (X - C α) * (X - C β) = X^2 - C a_p * X + C c_p`. -/
theorem satakeWDRep_charPol_frob (W : RHDirect.LocalLanglands.WDGroup)
    {a_p c_p α β : ℂ} (hα : α ≠ 0) (hβ : β ≠ 0) (hs : IsSatakePair a_p c_p α β)
    {φ : W.G} (hφ : W.deg φ = 1) :
    (satakeWDRep W α β hα hβ).charPol φ =
      Polynomial.X ^ 2 - Polynomial.C a_p * Polynomial.X + Polynomial.C c_p := by
  have hmat : ((satakeWDRep W α β hα hβ).ρ φ : Matrix (Fin 2) (Fin 2) ℂ) = !![α, 0; 0, β] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [satakeWDRep, diagGL2, hφ]
  rw [RHDirect.LocalLanglands.WDRep.charPol, hmat, Matrix.charpoly_fin_two]
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.det_fin_two, mul_zero, sub_zero, hs.1, hs.2]

/-- Exact Local Langlands `L`-factor match:
`(det (1 - p^{-s} • ρ(φ)))⁻¹ = degree2EulerFactor k χ a_p p s`. -/
theorem satakeWDRep_localLFactor_eq_degree2EulerFactor
    (W : RHDirect.LocalLanglands.WDGroup) {N : ℕ} {k : ℕ}
    (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime)
    {a_p α β : ℂ} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hs : IsSatakePair a_p (χ (p : ZMod N) * (p : ℂ) ^ (k - 1)) α β)
    {φ : W.G} (hφ : W.deg φ = 1) (s : ℂ) :
    (Matrix.det ((1 : Matrix (Fin 2) (Fin 2) ℂ) -
        ((p : ℂ) ^ (-s)) • ((satakeWDRep W α β hα hβ).ρ φ : Matrix (Fin 2) (Fin 2) ℂ)))⁻¹ =
      degree2EulerFactor k χ a_p p s := by
  have hmat : ((satakeWDRep W α β hα hβ).ρ φ : Matrix (Fin 2) (Fin 2) ℂ) = !![α, 0; 0, β] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [satakeWDRep, diagGL2, hφ]
  rw [hmat]
  simp only [degree2EulerFactor]
  congr 1
  have hdet : Matrix.det ((1 : Matrix (Fin 2) (Fin 2) ℂ) -
      ((p : ℂ) ^ (-s)) • !![α, 0; 0, β]) =
      (1 - (p : ℂ) ^ (-s) * α) * (1 - (p : ℂ) ^ (-s) * β) := by
    simp [Matrix.det_fin_two]
  rw [hdet]
  calc (1 - (p : ℂ) ^ (-s) * α) * (1 - (p : ℂ) ^ (-s) * β)
      = 1 - (α + β) * (p : ℂ) ^ (-s) + (α * β) * ((p : ℂ) ^ (-s)) ^ 2 := by ring
    _ = 1 - a_p * (p : ℂ) ^ (-s) +
          χ (p : ZMod N) * (p : ℂ) ^ (k - 1) * ((p : ℂ) ^ (-s)) ^ 2 := by rw [hs.1, hs.2]
    _ = 1 - a_p * (p : ℂ) ^ (-s) +
          χ (p : ZMod N) * (p : ℂ) ^ (((k - 1 : ℕ) : ℂ) - 2 * s) := by
        rw [mul_assoc, cpow_k_sub_one_sub_two_mul hp k s]

/-- Under Ramanujan–Petersson (`‖α‖ = ‖β‖ = p^((k - 1)/2)`), the twisted Satake representation
`wdNu (-(k - 1) / 2)` is **tempered / unitary**: both Frobenius eigenvalues have modulus `1`. -/
theorem satakeWDRep_tempered_of_ramanujan_petersson
    {p : ℕ} (hp : p.Prime) {k : ℕ} {α β : ℂ}
    (hrp : ‖α‖ = (p : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2) ∧ ‖β‖ = (p : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) :
    ‖α * ((p : ℂ) ^ (-(((k - 1 : ℕ) : ℂ) / 2)))‖ = 1 ∧
      ‖β * ((p : ℂ) ^ (-(((k - 1 : ℕ) : ℂ) / 2)))‖ = 1 := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  have hnorm_p : ‖(p : ℂ) ^ (-(((k - 1 : ℕ) : ℂ) / 2))‖ =
      (p : ℝ) ^ (-(((k - 1 : ℕ) : ℝ) / 2)) := by
    have h := Complex.norm_cpow_eq_rpow_re_of_pos hp_pos (-(((k - 1 : ℕ) : ℂ) / 2))
    simpa [Complex.ofReal_natCast] using h
  constructor
  · rw [norm_mul, hnorm_p, hrp.1, ← Real.rpow_add hp_pos, add_neg_cancel, Real.rpow_zero]
  · rw [norm_mul, hnorm_p, hrp.2, ← Real.rpow_add hp_pos, add_neg_cancel, Real.rpow_zero]

end RamanujanPeterssonAndSatakeWD

/-! ## Section 7: Deligne Divisor Bound, Exact Eigenform Characterization & Eisenstein Witness -/

section DeligneBoundAndCharacterization

/-- Elementary divisor-count bound: `(n.divisors.card : ℝ) ≤ 2 * Real.sqrt n` for every `n ≥ 1`. -/
theorem divisors_card_le_two_mul_sqrt {n : ℕ} (hn : 1 ≤ n) :
    (n.divisors.card : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  set S₁ := n.divisors.filter (fun d => d ≤ Nat.sqrt n)
  set S₂ := n.divisors.filter (fun d => Nat.sqrt n < d)
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_filter]
    intro d _ h1 h2
    omega
  have hunion : S₁ ∪ S₂ = n.divisors := by
    ext d
    simp only [S₁, S₂, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      by_cases hle : d ≤ Nat.sqrt n
      · exact Or.inl ⟨h, hle⟩
      · exact Or.inr ⟨h, not_le.mp hle⟩
  have hcard_eq : n.divisors.card = S₁.card + S₂.card := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  have hS1_sub : S₁ ⊆ Finset.Icc 1 (Nat.sqrt n) := by
    intro d hd
    rw [Finset.mem_filter] at hd
    rw [Finset.mem_Icc]
    exact ⟨Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd.1).1 (by omega), hd.2⟩
  have hS1_le : S₁.card ≤ Nat.sqrt n := by
    calc S₁.card ≤ (Finset.Icc 1 (Nat.sqrt n)).card := Finset.card_le_card hS1_sub
      _ = Nat.sqrt n := by simp
  have hS2_le : S₂.card ≤ S₁.card := by
    refine Finset.card_le_card_of_injOn (fun d => n / d) ?_ ?_
    · intro d hd
      rw [Finset.mem_coe, Finset.mem_filter] at hd ⊢
      have hdvd : d ∣ n := (Nat.mem_divisors.mp hd.1).1
      have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
      refine ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdvd, hn0⟩, ?_⟩
      have hmul : (n / d) * d = n := Nat.div_mul_cancel hdvd
      have hgt : Nat.sqrt n + 1 ≤ d := hd.2
      by_contra hlt
      have hge : Nat.sqrt n + 1 ≤ n / d := not_le.mp hlt
      have hsq : (Nat.sqrt n + 1) * (Nat.sqrt n + 1) ≤ (n / d) * d :=
        Nat.mul_le_mul hge hgt
      have hlt_sq : n < (Nat.sqrt n + 1) * (Nat.sqrt n + 1) := Nat.lt_succ_sqrt n
      omega
    · intro d₁ hd₁ d₂ hd₂ heq
      rw [Finset.mem_coe, Finset.mem_filter] at hd₁ hd₂
      have h1 : d₁ ∣ n := (Nat.mem_divisors.mp hd₁.1).1
      have h2 : d₂ ∣ n := (Nat.mem_divisors.mp hd₂.1).1
      have hpos : 0 < n / d₁ :=
        Nat.div_pos (Nat.le_of_dvd (by omega) h1) (Nat.pos_of_dvd_of_pos h1 (by omega))
      have hmul1 : (n / d₁) * d₁ = n := Nat.div_mul_cancel h1
      have hmul2 : (n / d₂) * d₂ = n := Nat.div_mul_cancel h2
      dsimp only at heq
      rw [← heq] at hmul2
      exact Nat.eq_of_mul_eq_mul_left hpos (hmul1.trans hmul2.symm)
  have hnat_le : n.divisors.card ≤ 2 * Nat.sqrt n := by omega
  have hsqrt_le : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _), sq]
    exact_mod_cast Nat.sqrt_le n
  calc (n.divisors.card : ℝ)
      ≤ ((2 * Nat.sqrt n : ℕ) : ℝ) := by exact_mod_cast hnat_le
    _ = 2 * (Nat.sqrt n : ℝ) := by push_cast; rfl
    _ ≤ 2 * Real.sqrt (n : ℝ) := by linarith

private theorem sum_divisors_mul_of_coprime {a b : ℕ} (hcop : Nat.Coprime a b) (g : ℕ → ℂ) :
    ∑ d ∈ (a * b).divisors, g d =
      ∑ p ∈ a.divisors ×ˢ b.divisors, g (p.1 * p.2) := by
  symm
  refine Finset.sum_nbij' (fun p => p.1 * p.2) (fun d => (Nat.gcd d a, Nat.gcd d b)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
    rcases Nat.mem_divisors.mp hp1 with ⟨h1, h1ne⟩
    rcases Nat.mem_divisors.mp hp2 with ⟨h2, h2ne⟩
    exact Nat.mem_divisors.mpr ⟨mul_dvd_mul h1 h2, mul_ne_zero h1ne h2ne⟩
  · intro d hd
    rcases Nat.mem_divisors.mp hd with ⟨_, hne⟩
    exact Finset.mem_product.mpr
      ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, left_ne_zero_of_mul hne⟩,
       Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, right_ne_zero_of_mul hne⟩⟩
  · intro p hp
    rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
    have h1 : p.1 ∣ a := (Nat.mem_divisors.mp hp1).1
    have h2 : p.2 ∣ b := (Nat.mem_divisors.mp hp2).1
    have hcop_p2_a : Nat.Coprime p.2 a := (hcop.coprime_dvd_right h2).symm
    have hcop_p1_b : Nat.Coprime p.1 b := hcop.coprime_dvd_left h1
    ext
    · dsimp only
      rw [hcop_p2_a.gcd_mul_right_cancel p.1, Nat.gcd_eq_left h1]
    · dsimp only
      rw [hcop_p1_b.gcd_mul_left_cancel p.2, Nat.gcd_eq_left h2]
  · intro d hd
    have hd_dvd : d ∣ a * b := (Nat.mem_divisors.mp hd).1
    rw [← hcop.gcd_mul d, Nat.gcd_eq_left hd_dvd]
  · intro _ _
    rfl

private theorem card_divisors_mul_of_coprime {a b : ℕ} (hcop : Nat.Coprime a b) :
    (a * b).divisors.card = a.divisors.card * b.divisors.card := by
  have h := sum_divisors_mul_of_coprime hcop (fun _ => (1 : ℂ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_product, Nat.cast_mul] at h
  exact_mod_cast h

/-- **Exact Deligne–Ramanujan Divisor Bound from Local Satake Purity**:
If a normalized Hecke eigenform `(f, lam)` of weight `k` and Nebentypus `χ` satisfies the
local Ramanujan–Petersson bound `‖α_p‖ ≤ p^((k - 1)/2)` and `‖β_p‖ ≤ p^((k - 1)/2)` at every
prime `p`, then for EVERY `n ≥ 1`:
`‖f n‖ ≤ (n.divisors.card : ℝ) * (n : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)`. -/
theorem eigenform_deligne_divisor_bound {N : ℕ} {k : ℕ} {χ : DirichletCharacter ℂ N}
    {f lam : ℕ → ℂ} (hf : IsNormalizedHeckeEigenform k χ f lam)
    (hsat : ∀ p : ℕ, p.Prime →
      ∃ α β : ℂ, IsSatakePair (f p) (χ (p : ZMod N) * (p : ℂ) ^ (k - 1)) α β ∧
        ‖α‖ ≤ (p : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2) ∧
        ‖β‖ ≤ (p : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) :
    ∀ n : ℕ, 1 ≤ n →
      ‖f n‖ ≤ (n.divisors.card : ℝ) * (n : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2) := by
  set θ : ℝ := ((k - 1 : ℕ) : ℝ) / 2
  have hpp : ∀ p : ℕ, p.Prime → ∀ r : ℕ,
      ‖f (p ^ r)‖ ≤ (((p ^ r).divisors.card : ℕ) : ℝ) * ((p ^ r : ℕ) : ℝ) ^ θ := by
    intro p hp r
    obtain ⟨α, β, hs, hα, hβ⟩ := hsat p hp
    rw [eigenform_prime_pow_eq_satake_sum hf hp hs r]
    have hp_nonneg : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
    have hcard : (p ^ r).divisors.card = r + 1 := by
      rw [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]
    rw [hcard, Nat.cast_pow, ← Real.rpow_natCast (p : ℝ) r, ← Real.rpow_mul hp_nonneg]
    calc ‖∑ j ∈ Finset.range (r + 1), α ^ j * β ^ (r - j)‖
        ≤ ∑ j ∈ Finset.range (r + 1), ‖α ^ j * β ^ (r - j)‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range (r + 1), (p : ℝ) ^ ((r : ℝ) * θ) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj' : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          rw [norm_mul, norm_pow, norm_pow]
          have h1 : ‖α‖ ^ j * ‖β‖ ^ (r - j) ≤
              ((p : ℝ) ^ θ) ^ j * ((p : ℝ) ^ θ) ^ (r - j) :=
            mul_le_mul (pow_le_pow_left₀ (norm_nonneg α) hα j)
              (pow_le_pow_left₀ (norm_nonneg β) hβ (r - j))
              (pow_nonneg (norm_nonneg β) _) (pow_nonneg (Real.rpow_nonneg hp_nonneg θ) _)
          refine h1.trans_eq ?_
          rw [← pow_add, Nat.add_sub_of_le hj', ← Real.rpow_natCast ((p : ℝ) ^ θ) r,
              ← Real.rpow_mul hp_nonneg, mul_comm θ (r : ℝ)]
      _ = ((r + 1 : ℕ) : ℝ) * (p : ℝ) ^ ((r : ℝ) * θ) := by
          simp [Finset.sum_const, nsmul_eq_mul]
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hn1 : n = 1
    · subst hn1; simp [hf.1]
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn1
    have hn0 : n ≠ 0 := by omega
    set a := n.factorization p
    have ha_pos : 1 ≤ a := (hp.dvd_iff_one_le_factorization hn0).mp hpn
    have hpa_dvd : p ^ a ∣ n := Nat.ordProj_dvd n p
    set n' := n / p ^ a
    have hn_eq : n = p ^ a * n' := (Nat.mul_div_cancel' hpa_dvd).symm
    have hn'_pos : 1 ≤ n' := Nat.div_pos (Nat.le_of_dvd (by omega) hpa_dvd) (pow_pos hp.pos a)
    have hcop : Nat.Coprime (p ^ a) n' :=
      (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_ordCompl hp hn0)).pow_left a
    have hn'_lt : n' < n := by
      have hpa_gt : 1 < p ^ a := one_lt_pow₀ hp.one_lt (by omega)
      calc n' = 1 * n' := (one_mul n').symm
        _ < p ^ a * n' := Nat.mul_lt_mul_of_pos_right hpa_gt (by omega)
        _ = n := hn_eq.symm
    have hcard_mul : n.divisors.card = (p ^ a).divisors.card * n'.divisors.card := by
      rw [hn_eq, card_divisors_mul_of_coprime hcop]
    have h1 := hpp p hp a
    have h2 := ih n' hn'_lt hn'_pos
    rw [hn_eq, eigenform_isMultiplicative hf (one_le_pow₀ hp.one_le) hn'_pos hcop, norm_mul,
        ← hn_eq, hcard_mul, Nat.cast_mul, hn_eq, Nat.cast_mul,
        Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    calc ‖f (p ^ a)‖ * ‖f n'‖
        ≤ ((p ^ a).divisors.card : ℝ) * ((p ^ a : ℕ) : ℝ) ^ θ *
            ((n'.divisors.card : ℝ) * (n' : ℝ) ^ θ) :=
          mul_le_mul h1 h2 (norm_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      _ = ((p ^ a).divisors.card : ℝ) * (n'.divisors.card : ℝ) *
            (((p ^ a : ℕ) : ℝ) ^ θ * (n' : ℝ) ^ θ) := by ring

/-- **Unconditional Convergence & Degree-2 Euler Product directly from Ramanujan–Petersson**:
For any normalized Hecke eigenform of weight `k ≥ 1` satisfying the Ramanujan–Petersson Satake
bound at every prime, `LSeries f s` converges absolutely and equals the exact degree-2 `GL_2`
Euler product throughout `Re(s) > k / 2 + 1` (and in particular throughout `Re(s) > (k + 1) / 2 + 1`). -/
theorem eigenform_LSeries_eulerProduct_of_ramanujan_petersson
    {N : ℕ} {k : ℕ} (hk : 1 ≤ k) {χ : DirichletCharacter ℂ N}
    {f lam : ℕ → ℂ} (hf : IsNormalizedHeckeEigenform k χ f lam)
    (hsat : ∀ p : ℕ, p.Prime →
      ∃ α β : ℂ, IsSatakePair (f p) (χ (p : ZMod N) * (p : ℂ) ^ (k - 1)) α β ∧
        ‖α‖ ≤ (p : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2) ∧
        ‖β‖ ≤ (p : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2))
    {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    (∏' (p : Nat.Primes), degree2EulerFactor k χ (f p) p s) = LSeries f s := by
  refine eigenform_LSeries_eulerProduct_of_poly_bound hf (C := 2) (σ := (k : ℝ) / 2) ?_ hs
  intro n hn
  have hdel := eigenform_deligne_divisor_bound hf hsat n hn
  have hdiv := divisors_card_le_two_mul_sqrt hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hsqrt : Real.sqrt (n : ℝ) = (n : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow (n : ℝ)
  have hexp : (1 : ℝ) / 2 + ((k - 1 : ℕ) : ℝ) / 2 = (k : ℝ) / 2 := by
    have hk' : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub hk, Nat.cast_one]
    rw [hk']
    ring
  calc ‖f n‖
      ≤ (n.divisors.card : ℝ) * (n : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2) := hdel
    _ ≤ (2 * Real.sqrt (n : ℝ)) * (n : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right hdiv (Real.rpow_nonneg hn_pos.le _)
    _ = 2 * ((n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) := by
        rw [hsqrt]; ring
    _ = 2 * (n : ℝ) ^ ((k : ℝ) / 2) := by
        rw [← Real.rpow_add hn_pos, hexp]

/-! ### Exact Converse Characterization of Normalized Hecke Eigenforms & Eisenstein Witness -/

private theorem primePow_mul_eq_sum_of_recurrence {N : ℕ} {k : ℕ} {χ : DirichletCharacter ℂ N}
    {f : ℕ → ℂ} {p : ℕ} (hf1 : f 1 = 1)
    (hrec : ∀ r : ℕ, f (p ^ (r + 2)) = f p * f (p ^ (r + 1)) - heckeWeight k χ p * f (p ^ r)) :
    ∀ b a : ℕ,
      ∑ j ∈ Finset.range (min a b + 1),
        (heckeWeight k χ p) ^ j * f (p ^ (a + b - 2 * j)) = f (p ^ a) * f (p ^ b) := by
  intro b
  induction b using Nat.strong_induction_on with
  | h b ih =>
    intro a
    match b with
    | 0 => simp [hf1]
    | 1 =>
      match a with
      | 0 => simp [hf1]
      | r + 1 =>
        have hmin : min (r + 1) 1 = 1 := by omega
        rw [hmin, Finset.sum_range_succ, Finset.sum_range_one]
        have he1 : r + 1 + 1 - 2 * 0 = r + 2 := by omega
        have he2 : r + 1 + 1 - 2 * 1 = r := by omega
        rw [he1, he2, pow_zero, one_mul, pow_one, pow_one, hrec r]
        ring
    | r + 2 =>
      rw [hrec r, mul_sub]
      have hstep1 := ih (r + 1) (by omega) a
      have hstep0 := ih r (by omega) a
      have hmul_p : f p * (f (p ^ a) * f (p ^ (r + 1))) =
          ∑ j ∈ Finset.range (min a (r + 1) + 1),
            (heckeWeight k χ p) ^ j * (f (p ^ (a + (r + 1) - 2 * j)) * f p) := by
        rw [← hstep1, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
      have hterm : ∀ j ∈ Finset.range (min a (r + 1) + 1),
          (heckeWeight k χ p) ^ j * (f (p ^ (a + (r + 1) - 2 * j)) * f p) =
            (heckeWeight k χ p) ^ j * f (p ^ (a + (r + 2) - 2 * j)) +
              if 1 ≤ a + (r + 1) - 2 * j then
                (heckeWeight k χ p) ^ (j + 1) * f (p ^ (a + r - 2 * j))
              else 0 := by
        intro j hj
        have hj_le : j ≤ min a (r + 1) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hja : j ≤ a := le_trans hj_le (min_le_left _ _)
        have hjr : j ≤ r + 1 := le_trans hj_le (min_le_right _ _)
        by_cases hpos : 1 ≤ a + (r + 1) - 2 * j
        · rw [if_pos hpos]
          set t := a + (r + 1) - 2 * j - 1
          have ht1 : a + (r + 1) - 2 * j = t + 1 := by omega
          have ht2 : a + (r + 2) - 2 * j = t + 2 := by omega
          have ht0 : a + r - 2 * j = t := by omega
          rw [ht1, ht2, ht0, hrec t, pow_succ]
          ring
        · rw [if_neg hpos, add_zero]
          have h0 : a + (r + 1) - 2 * j = 0 := by omega
          have h1 : a + (r + 2) - 2 * j = 1 := by omega
          rw [h0, h1, pow_zero, pow_one, hf1, one_mul]
      have hrew : f (p ^ a) * (f p * f (p ^ (r + 1))) =
          (∑ j ∈ Finset.range (min a (r + 1) + 1),
            (heckeWeight k χ p) ^ j * f (p ^ (a + (r + 2) - 2 * j))) +
          (∑ j ∈ Finset.range (min a (r + 1) + 1),
            if 1 ≤ a + (r + 1) - 2 * j then
              (heckeWeight k χ p) ^ (j + 1) * f (p ^ (a + r - 2 * j))
            else 0) := by
        calc f (p ^ a) * (f p * f (p ^ (r + 1)))
            = f p * (f (p ^ a) * f (p ^ (r + 1))) := by ring
          _ = ∑ j ∈ Finset.range (min a (r + 1) + 1),
                ((heckeWeight k χ p) ^ j * f (p ^ (a + (r + 2) - 2 * j)) +
                  if 1 ≤ a + (r + 1) - 2 * j then
                    (heckeWeight k χ p) ^ (j + 1) * f (p ^ (a + r - 2 * j))
                  else 0) := by
              rw [hmul_p]
              exact Finset.sum_congr rfl hterm
          _ = _ := Finset.sum_add_distrib
      have hsub_term : f (p ^ a) * (heckeWeight k χ p * f (p ^ r)) =
          ∑ j ∈ Finset.range (min a r + 1),
            (heckeWeight k χ p) ^ (j + 1) * f (p ^ (a + r - 2 * j)) := by
        calc f (p ^ a) * (heckeWeight k χ p * f (p ^ r))
            = heckeWeight k χ p * (f (p ^ a) * f (p ^ r)) := by ring
          _ = heckeWeight k χ p * ∑ j ∈ Finset.range (min a r + 1),
                (heckeWeight k χ p) ^ j * f (p ^ (a + r - 2 * j)) := by rw [← hstep0]
          _ = _ := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => by rw [← mul_assoc, ← pow_succ']
      rw [hrew, hsub_term]
      by_cases har : a ≤ r + 1
      · have hmin1 : min a (r + 2) = a := by omega
        have hmin2 : min a (r + 1) = a := by omega
        rw [hmin1, hmin2]
        by_cases har0 : a ≤ r
        · have hmin3 : min a r = a := by omega
          rw [hmin3]
          have hite : ∀ j ∈ Finset.range (a + 1),
              (if 1 ≤ a + (r + 1) - 2 * j then
                (heckeWeight k χ p) ^ (j + 1) * f (p ^ (a + r - 2 * j))
               else 0) = (heckeWeight k χ p) ^ (j + 1) * f (p ^ (a + r - 2 * j)) := by
            intro j hj
            have hj' : j ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
            exact if_pos (by omega)
          rw [Finset.sum_congr rfl hite, add_sub_cancel_right]
        · have haeq : a = r + 1 := by omega
          subst haeq
          have hmin3 : min (r + 1) r = r := by omega
          rw [hmin3, Finset.sum_range_succ (fun j => if 1 ≤ r + 1 + (r + 1) - 2 * j then
              (heckeWeight k χ p) ^ (j + 1) * f (p ^ (r + 1 + r - 2 * j)) else 0) (r + 1)]
          have hlast : ¬ (1 ≤ r + 1 + (r + 1) - 2 * (r + 1)) := by omega
          rw [if_neg hlast, add_zero]
          have hite : ∀ j ∈ Finset.range (r + 1),
              (if 1 ≤ r + 1 + (r + 1) - 2 * j then
                (heckeWeight k χ p) ^ (j + 1) * f (p ^ (r + 1 + r - 2 * j))
               else 0) = (heckeWeight k χ p) ^ (j + 1) * f (p ^ (r + 1 + r - 2 * j)) := by
            intro j hj
            have hj' : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
            exact if_pos (by omega)
          rw [Finset.sum_congr rfl hite, add_sub_cancel_right]
      · have hmin1 : min a (r + 2) = r + 2 := by omega
        have hmin2 : min a (r + 1) = r + 1 := by omega
        have hmin3 : min a r = r := by omega
        rw [hmin1, hmin2, hmin3]
        have hite : ∀ j ∈ Finset.range (r + 2),
            (if 1 ≤ a + (r + 1) - 2 * j then
              (heckeWeight k χ p) ^ (j + 1) * f (p ^ (a + r - 2 * j))
             else 0) = (heckeWeight k χ p) ^ (j + 1) * f (p ^ (a + r - 2 * j)) := by
          intro j hj
          have hj' : j ≤ r + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          exact if_pos (by omega)
        rw [Finset.sum_congr rfl hite,
            Finset.sum_range_succ (fun j => (heckeWeight k χ p) ^ (j + 1) * f (p ^ (a + r - 2 * j))) (r + 1),
            Finset.sum_range_succ (fun j => (heckeWeight k χ p) ^ j * f (p ^ (a + (r + 2) - 2 * j))) (r + 2)]
        have hlast_exp : a + r - 2 * (r + 1) = a + (r + 2) - 2 * (r + 2) := by omega
        rw [hlast_exp]
        ring

/-- **Exact Converse Characterization of Normalized Hecke Eigenforms**:
Any `q`-expansion `f : ℕ → ℂ` with `f 0 = 0`, `f 1 = 1`, coprime multiplicativity, and the
degree-2 prime-power recurrence is unconditionally a normalized simultaneous Hecke eigenform
`IsNormalizedHeckeEigenform k χ f f`. -/
theorem isNormalizedHeckeEigenform_of_mult_and_prime_pow
    {N : ℕ} {k : ℕ} {χ : DirichletCharacter ℂ N} {f : ℕ → ℂ}
    (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (hmult : ∀ {m n : ℕ}, 1 ≤ m → 1 ≤ n → Nat.Coprime m n → f (m * n) = f m * f n)
    (hrec : ∀ {p : ℕ}, p.Prime → ∀ r : ℕ,
      f (p ^ (r + 2)) = f p * f (p ^ (r + 1)) - χ (p : ZMod N) * (p : ℂ) ^ (k - 1) * f (p ^ r)) :
    IsNormalizedHeckeEigenform k χ f f := by
  refine ⟨hf1, fun n hn => ?_⟩
  funext m
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hm0 : m = 0
  · subst hm0
    simp [heckeOp_apply_zero, hf0]
  have hmain : ∀ n : ℕ, 1 ≤ n → ∀ m : ℕ, 1 ≤ m →
      heckeOp k χ n f m = f n * f m := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn m hm
      by_cases hn1 : n = 1
      · subst hn1; simp [heckeOp_one, hf1]
      obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn1
      have hn0 : n ≠ 0 := by omega
      have hm0' : m ≠ 0 := by omega
      set b := n.factorization p
      set a := m.factorization p
      have hb_pos : 1 ≤ b := (hp.dvd_iff_one_le_factorization hn0).mp hpn
      have hpb_dvd : p ^ b ∣ n := Nat.ordProj_dvd n p
      have hpa_dvd : p ^ a ∣ m := Nat.ordProj_dvd m p
      set n' := n / p ^ b
      set m' := m / p ^ a
      have hn_eq : n = p ^ b * n' := (Nat.mul_div_cancel' hpb_dvd).symm
      have hm_eq : m = p ^ a * m' := (Nat.mul_div_cancel' hpa_dvd).symm
      have hn'_pos : 1 ≤ n' := Nat.div_pos (Nat.le_of_dvd (by omega) hpb_dvd) (pow_pos hp.pos b)
      have hm'_pos : 1 ≤ m' := Nat.div_pos (Nat.le_of_dvd (by omega) hpa_dvd) (pow_pos hp.pos a)
      have hp_not_n' : ¬ p ∣ n' := Nat.not_dvd_ordCompl hp hn0
      have hp_not_m' : ¬ p ∣ m' := Nat.not_dvd_ordCompl hp hm0'
      have hcop_bn' : Nat.Coprime (p ^ b) n' := (hp.coprime_iff_not_dvd.mpr hp_not_n').pow_left b
      have hcop_am' : Nat.Coprime (p ^ a) m' := (hp.coprime_iff_not_dvd.mpr hp_not_m').pow_left a
      have hn'_lt : n' < n := by
        have hpb_gt : 1 < p ^ b := one_lt_pow₀ hp.one_lt (by omega)
        calc n' = 1 * n' := (one_mul n').symm
          _ < p ^ b * n' := Nat.mul_lt_mul_of_pos_right hpb_gt (by omega)
          _ = n := hn_eq.symm
      have hcop_pm'n' : ∀ s : ℕ, Nat.Coprime (p ^ s) (m' * n') := fun s =>
        ((hp.coprime_iff_not_dvd.mpr hp_not_m').mul_right (hp.coprime_iff_not_dvd.mpr hp_not_n')).pow_left s
      have hgcd_split : Nat.gcd m n = p ^ min a b * Nat.gcd m' n' := by
        have hc1 : Nat.Coprime (p ^ a) n' := (hp.coprime_iff_not_dvd.mpr hp_not_n').pow_left a
        have hc2 : Nat.Coprime m' (p ^ b) :=
          ((hp.coprime_iff_not_dvd.mpr hp_not_m').pow_left b).symm
        rw [hm_eq, hn_eq, hcop_bn'.gcd_mul, Nat.gcd_comm (p ^ a * m') (p ^ b),
            hcop_am'.gcd_mul, Nat.gcd_comm (p ^ a * m') n', hcop_am'.gcd_mul,
            hc2.symm.gcd_eq_one, mul_one, hc1.symm.gcd_eq_one, one_mul,
            Nat.gcd_comm (p ^ b) (p ^ a), Nat.gcd_comm n' m']
        congr 1
        rw [gcd_prime_pow_eq hp (pow_ne_zero a hp.ne_zero) b, hp.factorization_pow,
            Finsupp.single_eq_same]
      have hgcd_cop : Nat.Coprime (p ^ min a b) (Nat.gcd m' n') :=
        ((hp.coprime_iff_not_dvd.mpr hp_not_m').coprime_dvd_right (Nat.gcd_dvd_left m' n')).pow_left _
      have hpp_eq := primePow_mul_eq_sum_of_recurrence (p := p) hf1 (fun r => hrec hp r) b a
      have hih_eq := ih n' hn'_lt hn'_pos m' hm'_pos
      rw [heckeOp, hgcd_split, sum_divisors_mul_of_coprime hgcd_cop, Finset.sum_product,
          sum_divisors_prime_pow hp]
      have hfactor :
          (∑ j ∈ Finset.range (min a b + 1),
            ∑ d' ∈ (Nat.gcd m' n').divisors,
              heckeWeight k χ (p ^ j * d') * f (m * n / (p ^ j * d') ^ 2)) =
          (∑ j ∈ Finset.range (min a b + 1),
            (heckeWeight k χ p) ^ j * f (p ^ (a + b - 2 * j))) *
          (∑ d' ∈ (Nat.gcd m' n').divisors,
            heckeWeight k χ d' * f (m' * n' / d' ^ 2)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d' hd' => ?_
        have hj_le : j ≤ min a b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hd'_dvd : d' ∣ Nat.gcd m' n' := (Nat.mem_divisors.mp hd').1
        have hd'_m' : d' ∣ m' := dvd_trans hd'_dvd (Nat.gcd_dvd_left m' n')
        have hd'_n' : d' ∣ n' := dvd_trans hd'_dvd (Nat.gcd_dvd_right m' n')
        have hd'_sq : d' ^ 2 ∣ m' * n' := by
          rw [sq]; exact mul_dvd_mul hd'_m' hd'_n'
        have h2j_le : 2 * j ≤ a + b := by omega
        have hp_sq : (p ^ j) ^ 2 ∣ p ^ (a + b) := by
          rw [← pow_mul, mul_comm j 2]
          exact pow_dvd_pow p h2j_le
        have harg : m * n / (p ^ j * d') ^ 2 = p ^ (a + b - 2 * j) * (m' * n' / d' ^ 2) := by
          have hmn_eq : m * n = p ^ (a + b) * (m' * n') := by
            rw [hm_eq, hn_eq, pow_add]; ring
          have hden_eq : (p ^ j * d') ^ 2 = p ^ (2 * j) * d' ^ 2 := by
            rw [mul_pow, ← pow_mul, mul_comm j 2]
          rcases hd'_sq with ⟨q, hq⟩
          have hd'_ne : d' ≠ 0 := ne_of_gt (Nat.pos_of_dvd_of_pos hd'_m' (by omega))
          have hden_pos : 0 < p ^ (2 * j) * d' ^ 2 :=
            mul_pos (pow_pos hp.pos _) (pow_pos (Nat.pos_of_ne_zero hd'_ne) 2)
          rw [hmn_eq, hden_eq, hq, Nat.mul_div_cancel_left _ (pow_pos (Nat.pos_of_ne_zero hd'_ne) 2)]
          have hnum : p ^ (a + b) * (d' ^ 2 * q) =
              (p ^ (2 * j) * d' ^ 2) * (p ^ (a + b - 2 * j) * q) := by
            have hpow : p ^ (a + b) = p ^ (2 * j) * p ^ (a + b - 2 * j) := by
              rw [← pow_add, Nat.add_sub_of_le h2j_le]
            rw [hpow]; ring
          rw [hnum, Nat.mul_div_cancel_left _ hden_pos]
        have hq_pos : 1 ≤ m' * n' / d' ^ 2 := by
          rcases hd'_sq with ⟨q, hq⟩
          have hd'_ne : d' ≠ 0 := ne_of_gt (Nat.pos_of_dvd_of_pos hd'_m' (by omega))
          rw [hq, Nat.mul_div_cancel_left _ (pow_pos (Nat.pos_of_ne_zero hd'_ne) 2)]
          have hq0 : q ≠ 0 := by
            intro hq0; rw [hq0, mul_zero] at hq
            have : 0 < m' * n' := mul_pos (by omega) (by omega)
            omega
          omega
        have hcop_arg : Nat.Coprime (p ^ (a + b - 2 * j)) (m' * n' / d' ^ 2) :=
          (hcop_pm'n' (a + b - 2 * j)).coprime_dvd_right (Nat.div_dvd_of_dvd hd'_sq)
        rw [heckeWeight_mul, heckeWeight_pow, harg,
            hmult (one_le_pow₀ hp.one_le) hq_pos hcop_arg]
        ring
      rw [hfactor, hpp_eq]
      change f (p ^ a) * f (p ^ b) * heckeOp k χ n' f m' = f n * f m
      rw [hih_eq, hm_eq, hn_eq, hmult (one_le_pow₀ hp.one_le) hm'_pos hcop_am',
          hmult (one_le_pow₀ hp.one_le) hn'_pos hcop_bn']
      ring
  exact hmain n hn m (Nat.pos_of_ne_zero hm0)

/-- Concrete non-vacuous normalized Hecke eigenform witness: the weight-`k` Nebentypus-`χ`
divisor sum `σ_{k-1, χ}(n) = ∑ d ∣ n, χ(d) d^(k - 1)` (the Fourier coefficients of the normalized
Eisenstein series `E_{k, 1, χ}`). -/
def eisensteinCoeff {N : ℕ} (k : ℕ) (χ : DirichletCharacter ℂ N) (n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors, heckeWeight k χ d

/-- `eisensteinCoeff k χ` is unconditionally a normalized simultaneous Hecke eigenform of weight
`k` and Nebentypus `χ`, with Satake parameters `(1, χ(p) · p^(k - 1))` at every prime `p`. -/
theorem isNormalizedHeckeEigenform_eisensteinCoeff {N : ℕ} (k : ℕ) (χ : DirichletCharacter ℂ N) :
    IsNormalizedHeckeEigenform k χ (eisensteinCoeff k χ) (eisensteinCoeff k χ) := by
  refine isNormalizedHeckeEigenform_of_mult_and_prime_pow
    (by simp [eisensteinCoeff]) (by simp [eisensteinCoeff]) ?_ ?_
  · intro m n _ _ hcop
    simp only [eisensteinCoeff]
    rw [sum_divisors_mul_of_coprime hcop, Finset.sum_product, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d₂ _ => heckeWeight_mul k χ d₁ d₂
  · intro p hp r
    have hsum_p : eisensteinCoeff k χ p = 1 + heckeWeight k χ p := by
      simp only [eisensteinCoeff, hp.divisors, Finset.sum_pair hp.ne_one.symm, heckeWeight_one]
    simp only [eisensteinCoeff, sum_divisors_prime_pow hp, heckeWeight_pow] at hsum_p ⊢
    rw [hsum_p]
    have hsplit : ∀ m : ℕ,
        ∑ j ∈ Finset.range (m + 1), heckeWeight k χ p ^ j =
          1 + heckeWeight k χ p * ∑ j ∈ Finset.range m, heckeWeight k χ p ^ j := by
      intro m
      rw [Finset.sum_range_succ', pow_zero, add_comm]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by rw [pow_succ']
    rw [hsplit (r + 2), hsplit (r + 1)]
    simp only [heckeWeight]
    ring

/-- The local Satake parameters of `eisensteinCoeff k χ` at every prime `p` are `(1, χ(p) p^(k-1))`. -/
theorem eisensteinCoeff_isSatakePair {N : ℕ} (k : ℕ) (χ : DirichletCharacter ℂ N)
    {p : ℕ} (hp : p.Prime) :
    IsSatakePair (eisensteinCoeff k χ p) (χ (p : ZMod N) * (p : ℂ) ^ (k - 1))
      1 (χ (p : ZMod N) * (p : ℂ) ^ (k - 1)) := by
  refine ⟨?_, one_mul _⟩
  simp [eisensteinCoeff, hp.divisors, Finset.sum_pair hp.ne_one.symm, heckeWeight]

end DeligneBoundAndCharacterization

end RHDirect.Stage5ModularHecke

end
