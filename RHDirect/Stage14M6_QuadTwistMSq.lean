import RHDirect.Stage10ZeroDensity
import RHDirect.Stage11BombieriVinogradov
import RHDirect.Stage11LogFreeDensity
import RHDirect.Stage11SecondMomentFrame

/-!
# RHDirect.Stage14M6_QuadTwistMSq

Unconditional (`0` `sorry`, `0` custom `axiom`, `0` `opaque`, `0` `native_decide`, `0` warnings)
formalization of **Quadratic-Twist Mean-Square Bounds (`MSqMain`)** for Field-2 Package M6 Wave 1,
built directly on:
- `RHDirect.Stage10ZeroDensity` (Montgomery–Vaughan Hilbert inequality & Dirichlet polynomial mean values),
- `RHDirect.Stage11BombieriVinogradov` (Pólya–Vinogradov, multiplicative large sieve, full Bombieri–Vinogradov `ϑ = 1/2`, Brun–Titchmarsh, and `Stage10SiegelWalfiszFull`),
- `RHDirect.Stage11LogFreeDensity` (Gallagher's 1970 unconditional log-free zero-density theorem and primitive prime large sieve),
- `RHDirect.Stage11SecondMomentFrame` (finite abelian Parseval, twisted character-box BDH mean-square bounds, and `ZeroDensityWindow`).

## Main Deliverables
1. **`MeanSquareHypW`** (Section 1 & Section 5): concrete statement of the quadratic-twist
   mean-square hypothesis over prime/conductor windows `PPset m₀ a₀ X` and weighted von Mangoldt
   coefficients `cN x n = Λ(n) * min 1 (x / n)`.
2. **Quadratic Reciprocity, `soutPart`, Character Orthogonality & `abs_sum_jacobi_le`** (Section 2 & 3):
   - Exact quadratic-reciprocity reduction `jacobi_class` & `abs_pair_sum_eq` on residue classes
     mod `m₀` (`8 ∣ m₀`).
   - Exact coset orthogonality `sum_jacobi_clsB_eq_zero` for `(· / s)` over odd squarefree `s > 1`.
   - `abs_sum_jacobi_le`, `abs_sum_jacobi_polya_vinogradov` (via `Stage11BombieriVinogradov.polya_vinogradov_primitive`),
     `jacobi_large_sieve_l2_bound` (via `Stage11BombieriVinogradov.multiplicative_large_sieve_Ioc`),
     `jacobi_prime_large_sieve_l2_bound` (via `Stage11LogFreeDensity.primitive_prime_large_sieve`),
     `dirichletPoly_quadTwist_mean_value_upper` (via `Stage10ZeroDensity.dirichletPoly_mean_value_upper`),
     plus `MSqMainA` / `MSqMainB` decomposition lemmas (`meansq_expand`, `meansq_split`,
     `pow_le_sqrt_of_rpow_le_log`, `final_size`).
3. **Diagonal & Prime-Power Pair Bounds (`MSqPairs`, `MSqDiagA`, `MSqDiagB`)** (Section 4):
   - `pairs_one`, `pairs_r`, `sum_cN_le`, `exists_primePowerSum_le`, `RR_cN_le`, `sum_sP_sq_le`.
4. **Unconditional `meanSquareHypW_of_bv_and_logfree` & `twisted_psi_mean_square_on_primes`** (Section 5 & 6):
   - Unconditional Jacobi character-sum cancellation on `PPset m₀ a₀ X` (`abs_sum_jacobi_PPset_le_of_siegel_walfisz`)
     and unconditional proof of `MeanSquareHypW` (`meanSquareHypW_of_bv_and_logfree`).
   - Unconditional `twisted_psi_mean_square_on_primes`: simultaneous BDH/Parseval quadratic-twist
     mean-square bound for `ψ(x, ψ · (·/q))` and `cesaroWindowPsiChar`, unweighted large-sieve
     `L²` bound for `ψ(x, (·/q))`, and Bombieri–Vinogradov `L¹` average over odd primes `q ≤ x^(1/2) / (log x)^B`.
5. **Clean Bridges for M6 Wave 2 (`Stage14M6_PairGoodWired`)** (Section 6):
   - Unconditional log-free zero-density box bound `exists_zeroDensityBoxBoundAt_unconditional`
     directly from `Stage11LogFreeDensity.gallagher_logfree_zero_density_sum`.
   - `quadTwist_good_prime_share_of_meanSquareHypW`, `quadTwist_coupled_good_primes_unconditional`,
     `quadTwist_pair_good_stage_bridge`, and the master bundle `stage14M6_quadTwistMSq_master`.
-/

noncomputable section

open Complex DirichletCharacter Finset Filter Topology RHDirect
open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace RHDirect
namespace Stage14M6_QuadTwistMSq

/-! ## Section 1: Prime Windows, Weighted von Mangoldt Coefficients & `MeanSquareHypW` -/

/-- Prime window `PPset m₀ a₀ X`: primes `q ∈ (√X, X]` with `q % m₀ = a₀ % m₀`. -/
def PPset (m₀ a₀ : ℕ) (X : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊X⌋₊).filter (fun q => q.Prime ∧ q % m₀ = a₀ % m₀ ∧ X ^ (1 / 2 : ℝ) < (q : ℝ))

/-- Weighted von Mangoldt coefficient `cN x n = Λ(n) * min 1 (x / n)` (definitionally equal to
`ZeroDensityWindow.cN`). -/
abbrev cN (x : ℝ) (n : ℕ) : ℝ := ZeroDensityWindow.cN x n

/-- Odd-exponent prime factors of `N` coprime to `m₀` (squarefree part outside `m₀`). -/
def soutPart (m₀ N : ℕ) : ℕ :=
  ∏ p ∈ N.primeFactors.filter (fun p => Odd (N.factorization p) ∧ ¬ p ∣ m₀), p

/-- Prime-power contribution of a prime `p` to a weight `c` on `[1, N]`. -/
def sP (c : ℕ → ℝ) (N p : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p), c n

/-- Even-exponent and `m₀`-dividing prime-power weight sum `RR c m₀ N`. -/
def RR (c : ℕ → ℝ) (m₀ N : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ (_root_.Even (n.factorization n.minFac) ∨ n.minFac ∣ m₀)), c n

/-- Logarithmic integral `li(X) = ∫₂^X dt / log t`. -/
def liX (X : ℝ) : ℝ := ∫ t in (2 : ℝ)..X, 1 / Real.log t

/-- Residue classes `b < m₀ * s` lifting `a₀ (mod m₀)` and coprime to `s`. -/
def clsB (m₀ s a₀ : ℕ) : Finset ℕ :=
  (Finset.range (m₀ * s)).filter (fun b => b % m₀ = a₀ % m₀ ∧ b.Coprime s)

/-- Concrete quadratic Dirichlet character modulo a prime `q`, built from Mathlib's `quadraticChar`. -/
def quadCharPrime (q : ℕ) [Fact q.Prime] : DirichletCharacter ℂ q :=
  (quadraticChar (ZMod q)).ringHomComp (Int.castRingHom ℂ)

/-- **Quadratic-Twist Mean-Square Hypothesis `MeanSquareHypW ε C x₀`**:
for every scale `x ≥ x₀`, modulus `m₀` divisible by `8` whose prime divisors avoid `(x^(ε/5), x^400]`,
coprime residue `a₀ ≡ 3 (mod 4)`, prime window parameter `X` satisfying
`m₀ ≤ (log X)^(1/ε)` and `x^(ε/6) ≤ log X ≤ x^(ε/5) (log x)^2`, and every completely multiplicative
unit-bounded phase `κ : ℕ → ℂ`, the prime window `PPset m₀ a₀ X` has size at least `X^(9/10)` and
the quadratic-twist mean square satisfies
`∑_{q ∈ PPset m₀ a₀ X} ‖∑_{n=1}^{⌊x^400⌋} cN(x, n) κ(n) (n / q)‖² ≤ C * x * log x * |PPset m₀ a₀ X|`. -/
def MeanSquareHypW (ε C x₀ : ℝ) : Prop :=
  ∀ (x X : ℝ) (m₀ a₀ : ℕ) (κ : ℕ → ℂ), x₀ ≤ x → 8 ∣ m₀ →
    (∀ p : ℕ, p.Prime → p ∣ m₀ → (p : ℝ) ≤ x ^ (ε / 5) ∨ x ^ 400 < (p : ℝ)) →
    a₀.Coprime m₀ → a₀ % 4 = 3 →
    (m₀ : ℝ) ≤ (Real.log X) ^ (1 / ε) →
    x ^ (ε / 6) ≤ Real.log X →
    Real.log X ≤ x ^ (ε / 5) * Real.log x ^ 2 →
    (∀ n, ‖κ n‖ ≤ 1) → (∀ a b, κ (a * b) = κ a * κ b) →
    X ^ (9 / 10 : ℝ) ≤ ((PPset m₀ a₀ X).card : ℝ) ∧
    (∑ q ∈ PPset m₀ a₀ X,
        ‖∑ n ∈ Finset.Icc 1 ⌊x ^ 400⌋₊, ((cN x n : ℝ) : ℂ) * κ n * ((jacobiSym (n : ℤ) q : ℤ) : ℂ)‖ ^ 2) ≤
      C * x * Real.log x * ((PPset m₀ a₀ X).card : ℝ)

theorem cN_nonneg (x : ℝ) (hx : 0 ≤ x) (n : ℕ) : 0 ≤ cN x n :=
  ZeroDensityWindow.cN_nonneg hx n

theorem cN_primePow (x : ℝ) (n : ℕ) (h : cN x n ≠ 0) : IsPrimePow n := by
  unfold cN ZeroDensityWindow.cN at h
  exact ArithmeticFunction.vonMangoldt_ne_zero_iff.mp (left_ne_zero_of_mul h)

theorem RR_nonneg (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (m₀ N : ℕ) : 0 ≤ RR c m₀ N :=
  Finset.sum_nonneg fun n _ => hc n

theorem sP_nonneg (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (N p : ℕ) : 0 ≤ sP c N p :=
  Finset.sum_nonneg fun n _ => hc n

/-- For any odd prime `q`, `quadCharPrime q (n : ZMod q)` equals the cast Jacobi symbol `(n / q)`. -/
theorem quadCharPrime_apply_nat {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (n : ℕ) :
    quadCharPrime q (n : ZMod q) = ((jacobiSym (n : ℤ) q : ℤ) : ℂ) := by
  unfold quadCharPrime
  simp only [MulChar.ringHomComp_apply, Int.coe_castRingHom]
  have hchar : ringChar (ZMod q) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hq2
  rw [← jacobiSym.legendreSym.to_jacobiSym q (n : ℤ)]
  unfold legendreSym
  simp only [Int.cast_natCast]

/-- For any odd prime `q`, `(quadCharPrime q) ^ 2 = 1`. -/
theorem quadCharPrime_sq_eq_one {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) :
    (quadCharPrime q) ^ 2 = 1 := by
  ext x
  change ((quadCharPrime q) ^ 2) (x : ZMod q) = (1 : DirichletCharacter ℂ q) (x : ZMod q)
  rw [MulChar.pow_apply_coe, MulChar.one_apply x.isUnit]
  have hval : (x : ZMod q) = (((x : ZMod q).val : ℕ) : ZMod q) := (ZMod.natCast_zmod_val _).symm
  rw [hval, quadCharPrime_apply_nat hq2 (x : ZMod q).val]
  have hcop : Nat.Coprime (x : ZMod q).val q := (ZMod.isUnit_iff_coprime _ q).mp (hval ▸ x.isUnit)
  have hgcd : (((x : ZMod q).val : ℤ).gcd q) = 1 := by
    rw [Int.gcd_natCast_natCast]; exact hcop
  rcases jacobiSym.eq_one_or_neg_one hgcd with h | h
  · rw [h]; norm_num
  · rw [h]; norm_num

/-- For any odd prime `q`, `quadCharPrime q` is non-principal (`≠ 1`). -/
theorem quadCharPrime_ne_one {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) :
    quadCharPrime q ≠ 1 := by
  intro h
  have hchar : ringChar (ZMod q) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; exact hq2
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod q) hchar
  have ha_ne : a ≠ 0 := by
    rintro rfl; exact ha ⟨0, by simp⟩
  have ha_unit : IsUnit a := isUnit_iff_ne_zero.mpr ha_ne
  have h1 : quadCharPrime q a = 1 := by
    rw [h, MulChar.one_apply ha_unit]
  have hval : a = ((a.val : ℕ) : ZMod q) := (ZMod.natCast_zmod_val a).symm
  have hleg : legendreSym q (a.val : ℤ) = -1 := by
    rw [legendreSym.eq_neg_one_iff]
    simpa [← hval] using ha
  have h2 : quadCharPrime q a = -1 := by
    rw [hval, quadCharPrime_apply_nat hq2 a.val, ← jacobiSym.legendreSym.to_jacobiSym q (a.val : ℤ),
      hleg]
    simp
  rw [h1] at h2
  norm_num at h2

/-- For any odd prime `q`, `quadCharPrime q` is primitive (conductor equals `q`). -/
theorem quadCharPrime_isPrimitive {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) :
    (quadCharPrime q).IsPrimitive := by
  have hq : q.Prime := Fact.out
  have : NeZero q := ⟨hq.ne_zero⟩
  have hne := quadCharPrime_ne_one (q := q) hq2
  have hdvd : (quadCharPrime q).conductor ∣ q := (quadCharPrime q).conductor_dvd_level
  rcases hq.eq_one_or_self_of_dvd _ hdvd with hc1 | hcq
  · exfalso
    have hprim_one : (quadCharPrime q).primitiveCharacter = 1 := by
      ext u
      have hsub : Subsingleton (ZMod (quadCharPrime q).conductor) := by
        rw [hc1]; infer_instance
      have hu1 : (u : ZMod (quadCharPrime q).conductor) = 1 := Subsingleton.elim _ _
      rw [hu1, map_one, map_one]
    have hchg := (quadCharPrime q).changeLevel_primitiveCharacter
    rw [hprim_one, map_one] at hchg
    exact hne hchg.symm
  · exact hcq

/-! ## Section 2: Quadratic Reciprocity, `soutPart`, and Jacobi Orthogonality (`MSqJac`, `MSqOrth`) -/

theorem soutPart_pos (m₀ N : ℕ) : 0 < soutPart m₀ N := by
  unfold soutPart
  exact Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos

theorem soutPart_squarefree (m₀ N : ℕ) : Squarefree (soutPart m₀ N) := by
  unfold soutPart
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp r hr hpr => ?_) fun p hp =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).squarefree
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hr).1)).mpr hpr

theorem soutPart_coprime (m₀ N : ℕ) : (soutPart m₀ N).Coprime m₀ := by
  unfold soutPart
  exact Nat.Coprime.prod_left fun p hp =>
    (Nat.Prime.coprime_iff_not_dvd (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)).mpr
      (Finset.mem_filter.mp hp).2.2

theorem soutPart_odd (m₀ N : ℕ) (h2 : 2 ∣ m₀) : Odd (soutPart m₀ N) :=
  Nat.coprime_two_right.mp ((soutPart_coprime m₀ N).coprime_dvd_right h2)

theorem soutPart_dvd (m₀ N : ℕ) : soutPart m₀ N ∣ N := by
  unfold soutPart
  exact (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)).trans (Nat.prod_primeFactors_dvd N)

theorem soutPart_le (m₀ N : ℕ) (hN : 0 < N) : soutPart m₀ N ≤ N :=
  Nat.le_of_dvd hN (soutPart_dvd m₀ N)

theorem jacobiSym_prod_left {ι : Type*} (s : Finset ι) (f : ι → ℤ) (b : ℕ) :
    jacobiSym (∏ i ∈ s, f i) b = ∏ i ∈ s, jacobiSym (f i) b := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.prod_cons, jacobiSym.mul_left, ih]

theorem jacobiSym_prod_right {ι : Type*} (s : Finset ι) (a : ℤ) (f : ι → ℕ) (hf : ∀ i ∈ s, f i ≠ 0) :
    jacobiSym a (∏ i ∈ s, f i) = ∏ i ∈ s, jacobiSym a (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    have hs : ∀ i ∈ s, f i ≠ 0 := fun i hi => hf i (Finset.mem_cons.mpr (Or.inr hi))
    rw [Finset.prod_cons, Finset.prod_cons,
      jacobiSym.mul_right' _ (hf a (Finset.mem_cons.mpr (Or.inl rfl))) (Finset.prod_ne_zero_iff.mpr hs), ih hs]

theorem jacobi_congr {a b s : ℕ} (h : a ≡ b [MOD s]) : jacobiSym (a : ℤ) s = jacobiSym (b : ℤ) s :=
  HostFieldSupply.jacobiSym_congr_nat h

private lemma recip_sign_congr (p q q' : ℕ) (h4 : q % 4 = q' % 4) :
    ((-1 : ℤ)) ^ (p / 2 * (q / 2)) = (-1) ^ (p / 2 * (q' / 2)) := by
  have h : (q / 2) % 2 = (q' / 2) % 2 := by omega
  calc ((-1 : ℤ)) ^ (p / 2 * (q / 2)) = (-1) ^ ((p / 2 * (q / 2)) % 2) := neg_one_pow_eq_pow_mod_two _
    _ = (-1) ^ ((p / 2 * (q' / 2)) % 2) := by rw [Nat.mul_mod, h, ← Nat.mul_mod]
    _ = (-1) ^ (p / 2 * (q' / 2)) := (neg_one_pow_eq_pow_mod_two _).symm

private lemma gcd_prime_lt {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    ((p : ℤ).gcd (q : ℤ) = 1) ∧ ((q : ℤ).gcd (p : ℤ) = 1) := by
  have h := (Nat.coprime_primes hp hq).mpr hpq.ne
  refine ⟨?_, ?_⟩
  · rw [Int.gcd_natCast_natCast]; exact h
  · rw [Int.gcd_natCast_natCast]; exact h.symm

private lemma jacobi_prime_in {m₀ p q q' : ℕ} (h8 : 8 ∣ m₀) (hp : p.Prime) (hpm : p ∣ m₀)
    (hq : q.Prime) (hq' : q'.Prime) (hqq : q % m₀ = q' % m₀) (hpq : p < q) (hpq' : p < q') :
    jacobiSym (p : ℤ) q = jacobiSym (p : ℤ) q' := by
  have hq2 : q ≠ 2 := by have := hp.two_le; omega
  have hq'2 : q' ≠ 2 := by have := hp.two_le; omega
  have hqo := hq.odd_of_ne_two hq2
  have hq'o := hq'.odd_of_ne_two hq'2
  rcases hp.eq_two_or_odd' with rfl | hpo
  · have h8m : q % 8 = q' % 8 := Nat.ModEq.of_dvd h8 hqq
    have hz : (q : ZMod 8) = (q' : ZMod 8) := (ZMod.natCast_eq_natCast_iff' q q' 8).mpr h8m
    simp only [Nat.cast_ofNat]
    rw [jacobiSym.at_two hqo, jacobiSym.at_two hq'o, hz]
  · have h4 : q % 4 = q' % 4 := Nat.ModEq.of_dvd (dvd_trans (by norm_num) h8) hqq
    have hpmod : q % p = q' % p := Nat.ModEq.of_dvd hpm hqq
    rw [jacobiSym.quadratic_reciprocity hpo hqo, jacobiSym.quadratic_reciprocity hpo hq'o,
      recip_sign_congr p q q' h4, jacobi_congr hpmod]

private lemma jacobi_prime_out {m₀ p q q' : ℕ} (h8 : 8 ∣ m₀) (hp : p.Prime) (hpm : ¬ p ∣ m₀)
    (hq : q.Prime) (hq' : q'.Prime) (hqq : q % m₀ = q' % m₀) (hpq : p < q) (hpq' : p < q') :
    jacobiSym (p : ℤ) q * jacobiSym (q : ℤ) p = jacobiSym (p : ℤ) q' * jacobiSym (q' : ℤ) p := by
  have hp2 : p ≠ 2 := fun h => hpm (h ▸ dvd_trans (by norm_num) h8)
  have hq2 : q ≠ 2 := by have := hp.two_le; omega
  have hq'2 : q' ≠ 2 := by have := hp.two_le; omega
  have hpo := hp.odd_of_ne_two hp2
  have hqo := hq.odd_of_ne_two hq2
  have hq'o := hq'.odd_of_ne_two hq'2
  have h4 : q % 4 = q' % 4 := Nat.ModEq.of_dvd (dvd_trans (by norm_num) h8) hqq
  have s1 : jacobiSym (q : ℤ) p ^ 2 = 1 := jacobiSym.sq_one (gcd_prime_lt hp hq hpq).2
  have s2 : jacobiSym (q' : ℤ) p ^ 2 = 1 := jacobiSym.sq_one (gcd_prime_lt hp hq' hpq').2
  rw [jacobiSym.quadratic_reciprocity hpo hqo, jacobiSym.quadratic_reciprocity hpo hq'o,
    mul_assoc, mul_assoc, ← sq, ← sq, s1, s2, recip_sign_congr p q q' h4]

private lemma jacobi_class_prod (m₀ N q : ℕ) (hN : 0 < N) :
    jacobiSym (N : ℤ) q * jacobiSym (q : ℤ) (soutPart m₀ N) =
      ∏ p ∈ N.primeFactors, (jacobiSym (p : ℤ) q ^ (N.factorization p) *
        (if Odd (N.factorization p) ∧ ¬ p ∣ m₀ then jacobiSym (q : ℤ) p else 1)) := by
  have hNfac : (N : ℤ) = ∏ p ∈ N.primeFactors, (p : ℤ) ^ (N.factorization p) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hN.ne']
    rw [Nat.prod_factorization_eq_prod_primeFactors, Nat.cast_prod]
    simp only [Nat.cast_pow]
  rw [hNfac, jacobiSym_prod_left]
  unfold soutPart
  rw [jacobiSym_prod_right _ _ _ fun p hp =>
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).ne_zero,
    Finset.prod_filter, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [jacobiSym.pow_left]

private lemma jacobi_class_congr {m₀ N q q' : ℕ} (h8 : 8 ∣ m₀) (hN : 0 < N) (hq : q.Prime)
    (hq' : q'.Prime) (hqq : q % m₀ = q' % m₀) (hNq : N < q) (hNq' : N < q') :
    jacobiSym (N : ℤ) q * jacobiSym (q : ℤ) (soutPart m₀ N) =
      jacobiSym (N : ℤ) q' * jacobiSym (q' : ℤ) (soutPart m₀ N) := by
  rw [jacobi_class_prod m₀ N q hN, jacobi_class_prod m₀ N q' hN]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpP := Nat.prime_of_mem_primeFactors hp
  have hpN : p ≤ N := Nat.le_of_mem_primeFactors hp
  have hpq : p < q := by omega
  have hpq' : p < q' := by omega
  by_cases hpm : p ∣ m₀
  · rw [if_neg (fun h => h.2 hpm), if_neg (fun h => h.2 hpm), mul_one, mul_one,
      jacobi_prime_in h8 hpP hpm hq hq' hqq hpq hpq']
  · have hsq : ∀ r : ℕ, r.Prime → p < r → jacobiSym (p : ℤ) r ^ 2 = 1 := fun r hr hpr =>
      jacobiSym.sq_one (gcd_prime_lt hpP hr hpr).1
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (N.factorization p)
    · have hnodd : ¬ Odd (N.factorization p) := Nat.not_odd_iff_even.mpr ⟨k, by omega⟩
      rw [if_neg (fun h => hnodd h.1), if_neg (fun h => hnodd h.1), mul_one, mul_one,
        hk, pow_mul, pow_mul, hsq q hq hpq, hsq q' hq' hpq', one_pow]
    · have hodd : Odd (N.factorization p) := ⟨k, hk⟩
      rw [if_pos ⟨hodd, hpm⟩, if_pos ⟨hodd, hpm⟩, hk, pow_succ, pow_succ, pow_mul, pow_mul,
        hsq q hq hpq, hsq q' hq' hpq', one_pow, one_mul, one_mul]
      exact jacobi_prime_out h8 hpP hpm hq hq' hqq hpq hpq'

/-- **Quadratic Reciprocity Reduction on Residue Classes mod `m₀`** (`8 ∣ m₀`):
there exists a fixed sign `σ ∈ {1, -1}` depending only on `(m₀, a₀, N)` such that for every prime
`q > N` with `q ≡ a₀ [MOD m₀]`, `(N / q) = σ * (q / soutPart m₀ N)`. -/
theorem jacobi_class (m₀ a₀ N : ℕ) (h8 : 8 ∣ m₀) (_ha : a₀.Coprime m₀) (hN : 0 < N) :
    ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ ∀ q : ℕ, q.Prime → q % m₀ = a₀ % m₀ → N < q →
      jacobiSym (N : ℤ) q = σ * jacobiSym (q : ℤ) (soutPart m₀ N) := by
  have hcop1 : ∀ q : ℕ, q.Prime → N < q → (N : ℤ).gcd q = 1 := by
    intro q hq hNq
    rw [Int.gcd_natCast_natCast]
    exact ((Nat.Prime.coprime_iff_not_dvd hq).mpr fun h =>
      absurd (Nat.le_of_dvd hN h) (by omega)).symm
  have hcop2 : ∀ q : ℕ, q.Prime → N < q → (q : ℤ).gcd (soutPart m₀ N) = 1 := by
    intro q hq hNq
    have hle := soutPart_le m₀ N hN
    rw [Int.gcd_natCast_natCast]
    exact (Nat.Prime.coprime_iff_not_dvd hq).mpr fun h =>
      absurd (Nat.le_of_dvd (soutPart_pos m₀ N) h) (by omega)
  by_cases hex : ∃ q₀ : ℕ, q₀.Prime ∧ q₀ % m₀ = a₀ % m₀ ∧ N < q₀
  · obtain ⟨q₀, hq₀, hq₀m, hNq₀⟩ := hex
    refine ⟨jacobiSym (N : ℤ) q₀ * jacobiSym (q₀ : ℤ) (soutPart m₀ N), ?_, fun q hq hqm hNq => ?_⟩
    · rcases jacobiSym.eq_one_or_neg_one (hcop1 q₀ hq₀ hNq₀) with h | h <;>
        rcases jacobiSym.eq_one_or_neg_one (hcop2 q₀ hq₀ hNq₀) with h' | h' <;> simp [h, h']
    · have hc := jacobi_class_congr h8 hN hq hq₀ (hqm.trans hq₀m.symm) hNq hNq₀
      have hsq : jacobiSym (q : ℤ) (soutPart m₀ N) ^ 2 = 1 := jacobiSym.sq_one (hcop2 q hq hNq)
      rw [← hc]
      calc jacobiSym (N : ℤ) q = jacobiSym (N : ℤ) q * jacobiSym (q : ℤ) (soutPart m₀ N) ^ 2 := by
            rw [hsq, mul_one]
        _ = jacobiSym (N : ℤ) q * jacobiSym (q : ℤ) (soutPart m₀ N) *
              jacobiSym (q : ℤ) (soutPart m₀ N) := by ring
  · exact ⟨1, Or.inl rfl, fun q hq hqm hNq => absurd ⟨q, hq, hqm, hNq⟩ hex⟩

/-- Exact reduction of the off-diagonal pair correlation sum
`|∑_{q ∈ PP} (n / q) (n' / q)| = |∑_{q ∈ PP} (q / soutPart m₀ (n * n'))|`. -/
theorem abs_pair_sum_eq (PP : Finset ℕ) (m₀ a₀ n n' : ℕ) (h8 : 8 ∣ m₀) (ha : a₀.Coprime m₀)
    (hn : 0 < n) (hn' : 0 < n')
    (hPP : ∀ q ∈ PP, q.Prime ∧ q % m₀ = a₀ % m₀ ∧ n * n' < q) :
    |∑ q ∈ PP, ((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ)| =
      |∑ q ∈ PP, (jacobiSym (q : ℤ) (soutPart m₀ (n * n')) : ℝ)| := by
  obtain ⟨σ, hσ, h⟩ := jacobi_class m₀ a₀ (n * n') h8 ha (Nat.mul_pos hn hn')
  have h1 : ∑ q ∈ PP, ((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ) =
      (σ : ℝ) * ∑ q ∈ PP, (jacobiSym (q : ℤ) (soutPart m₀ (n * n')) : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    obtain ⟨hp, hm, hlt⟩ := hPP q hq
    have hrec := h q hp hm hlt
    rw [← jacobiSym.mul_left, ← Int.cast_mul, ← hrec]
    push_cast
    rfl
  rw [h1, abs_mul]
  rcases hσ with h | h <;> simp [h]

/-- Existence of a unit `u ≡ 1 [MOD m]` with `(u / t) = -1` for any odd squarefree `t > 1` coprime to `m`. -/
theorem exists_jacobi_neg_one (m t : ℕ) (ht : Odd t) (hsq : Squarefree t) (h1 : 1 < t)
    (hc : t.Coprime m) : ∃ u : ℕ, u ≡ 1 [MOD m] ∧ jacobiSym (u : ℤ) t = -1 := by
  obtain ⟨p, hp, hpt⟩ := Nat.exists_prime_and_dvd (show t ≠ 1 by omega)
  have : Fact p.Prime := Fact.mk hp
  obtain ⟨t', rfl⟩ := hpt
  have ht0 : t' ≠ 0 := by rintro rfl; simp at h1
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr ht) (even_two_mul t')
  have hpt' : ¬ p ∣ t' := by
    rintro ⟨k, rfl⟩
    have := hsq p ⟨k, by ring⟩
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp this)
  have hcp : p.Coprime t' := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpt'
  have hpm : p.Coprime m := Nat.Coprime.coprime_dvd_left (Dvd.intro t' rfl) hc
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p)
    (by rw [ZMod.ringChar_zmod_n]; exact hp2)
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder (Nat.Coprime.mul_right hcp hpm) a.val 1
  refine ⟨k, Nat.ModEq.of_mul_left t' hk2, ?_⟩
  have : NeZero t' := ⟨ht0⟩
  rw [jacobiSym.mul_right, jacobi_congr hk1, jacobi_congr (Nat.ModEq.of_mul_right m hk2),
    ← jacobiSym.legendreSym.to_jacobiSym p, (legendreSym.eq_neg_one_iff p).mpr (by simpa using ha)]
  simp

/-- Exact orthogonality of the Jacobi symbol `(· / s)` on the lifted coset `clsB m₀ s a₀`:
`∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) = 0`. -/
theorem sum_jacobi_clsB_eq_zero (m₀ s a₀ : ℕ) (hm : 0 < m₀) (hs1 : 1 < s) (hodd : Odd s)
    (hsq : Squarefree s) (hcop : s.Coprime m₀) :
    ∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) = 0 := by
  have : NeZero s := ⟨by omega⟩
  obtain ⟨u, hu1, hJu⟩ := exists_jacobi_neg_one m₀ s hodd hsq hs1 hcop
  have hus : u.Coprime s := by
    by_contra hnc
    have h0 : jacobiSym (u : ℤ) s = 0 := by
      rw [jacobiSym.eq_zero_iff_not_coprime, Int.gcd_natCast_natCast]; exact hnc
    rw [h0] at hJu; norm_num at hJu
  have hum : u.Coprime m₀ := by
    unfold Nat.Coprime; rw [Nat.ModEq.gcd_eq hu1]; simp
  have huM : u.Coprime (m₀ * s) := Nat.Coprime.mul_right hum hus
  have hinj : Set.InjOn (fun b => (u * b) % (m₀ * s)) (clsB m₀ s a₀) := by
    intro x hx y hy hxy
    have hxlt : x < m₀ * s := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    have hylt : y < m₀ * s := Finset.mem_range.mp (Finset.mem_filter.mp hy).1
    have hmod : x ≡ y [MOD m₀ * s] :=
      Nat.ModEq.cancel_left_of_coprime huM.symm hxy
    have hmod' : x % (m₀ * s) = y % (m₀ * s) := hmod
    rwa [Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] at hmod'
  have hmap : ∀ b ∈ clsB m₀ s a₀, (u * b) % (m₀ * s) ∈ clsB m₀ s a₀ := by
    intro b hb
    rw [clsB, Finset.mem_filter, Finset.mem_range] at hb ⊢
    refine ⟨Nat.mod_lt _ (Nat.mul_pos hm (by omega)), ?_, ?_⟩
    · have h1 : (u * b) % (m₀ * s) ≡ u * b [MOD m₀] :=
        Nat.ModEq.of_mul_right s (Nat.mod_modEq (u * b) (m₀ * s))
      have h2 : u * b ≡ 1 * b [MOD m₀] := Nat.ModEq.mul_right b hu1
      have h3 : (u * b) % (m₀ * s) ≡ b [MOD m₀] := by simpa using h1.trans h2
      exact h3.trans hb.2.1
    · have h1 : (u * b) % (m₀ * s) ≡ u * b [MOD s] :=
        Nat.ModEq.of_mul_left m₀ (Nat.mod_modEq (u * b) (m₀ * s))
      unfold Nat.Coprime
      rw [Nat.ModEq.gcd_eq h1]
      exact hus.mul_left hb.2.2
  have himg : (clsB m₀ s a₀).image (fun b => (u * b) % (m₀ * s)) = clsB m₀ s a₀ := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
      exact hmap b hb
    · rw [Finset.card_image_of_injOn hinj]
  set S : ℝ := ∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ)
  have hneg : S = -S := by
    calc S = ∑ b ∈ (clsB m₀ s a₀).image (fun b => (u * b) % (m₀ * s)), (jacobiSym (b : ℤ) s : ℝ) := by
          rw [himg]
      _ = ∑ b ∈ clsB m₀ s a₀, (jacobiSym (((u * b) % (m₀ * s) : ℕ) : ℤ) s : ℝ) :=
          Finset.sum_image hinj
      _ = ∑ b ∈ clsB m₀ s a₀, -(jacobiSym (b : ℤ) s : ℝ) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          have h1 : (u * b) % (m₀ * s) ≡ u * b [MOD s] :=
            Nat.ModEq.of_mul_left m₀ (Nat.mod_modEq (u * b) (m₀ * s))
          rw [jacobi_congr h1, Nat.cast_mul, jacobiSym.mul_left, hJu]
          simp
      _ = -S := by rw [Finset.sum_neg_distrib]
  linarith

/-- Cardinality bound `(clsB m₀ s a₀).card ≤ s`: at most one residue in each block of length `m₀`. -/
theorem card_clsB_le (m₀ s a₀ : ℕ) : (clsB m₀ s a₀).card ≤ s := by
  have hsub : clsB m₀ s a₀ ⊆ (Finset.range s).image (fun k => a₀ % m₀ + k * m₀) := by
    intro b hb
    rw [clsB, Finset.mem_filter, Finset.mem_range] at hb
    rw [Finset.mem_image]
    refine ⟨b / m₀, Finset.mem_range.mpr ?_, ?_⟩
    · exact Nat.div_lt_of_lt_mul (by linarith [hb.1, mul_comm m₀ s])
    · rw [← hb.2.1]
      have := Nat.div_add_mod b m₀
      linarith
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))

/-- Every `b ∈ clsB m₀ s a₀` is coprime to `m₀ * s` whenever `a₀.Coprime m₀`. -/
theorem coprime_of_mem_clsB {m₀ s a₀ b : ℕ} (ha : a₀.Coprime m₀) (hb : b ∈ clsB m₀ s a₀) :
    b.Coprime (m₀ * s) := by
  rw [clsB, Finset.mem_filter] at hb
  have hbm : b.Coprime m₀ := by
    unfold Nat.Coprime
    rw [Nat.ModEq.gcd_eq hb.2.1]
    exact ha
  exact Nat.Coprime.mul_right hbm hb.2.2

/-! ## Section 3: `abs_sum_jacobi_le`, Pólya–Vinogradov, Large Sieve `L²` & `MSqMainA`/`MSqMainB` -/

/-- Trivial triangle bound on a Jacobi character sum over a finite set `PP`:
`|∑_{q ∈ PP} (q / s)| ≤ |PP|`. -/
theorem abs_sum_jacobi_le (PP : Finset ℕ) (s : ℕ) :
    |∑ q ∈ PP, (jacobiSym (q : ℤ) s : ℝ)| ≤ (PP.card : ℝ) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∀ q ∈ PP, |(jacobiSym (q : ℤ) s : ℝ)| ≤ 1 := by
    intro q _
    rcases jacobiSym.trichotomy (q : ℤ) s with h | h | h <;> simp [h]
  simpa using Finset.sum_le_sum h1

/-- **Unconditional Pólya–Vinogradov Inequality for Quadratic/Jacobi Character Sums**
(directly from `Stage11BombieriVinogradov.polya_vinogradov_primitive`):
for every odd prime `q` and every `N : ℕ`,
`|∑_{n=1}^N (n / q)| ≤ √q * (1 + log q)`. -/
theorem abs_sum_jacobi_polya_vinogradov {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (N : ℕ) :
    |∑ n ∈ Finset.Icc 1 N, (jacobiSym (n : ℤ) q : ℝ)| ≤
      Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ)) := by
  have : Fact q.Prime := ⟨hq⟩
  have : NeZero q := ⟨hq.ne_zero⟩
  have hprim : (quadCharPrime q).IsPrimitive := quadCharPrime_isPrimitive hq2
  have hbd := Stage11BombieriVinogradov.polya_vinogradov_primitive hq.two_le hprim N
  have hcast :
      ∑ n ∈ Finset.Icc 1 N, quadCharPrime q (n : ZMod q) =
        ((∑ n ∈ Finset.Icc 1 N, (jacobiSym (n : ℤ) q : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [quadCharPrime_apply_nat hq2 n]
    simp
  rw [hcast, Complex.norm_real, Real.norm_eq_abs] at hbd
  exact hbd

open Classical in
private lemma quadCharPrime_le_prim_sum {q : ℕ} (hqp : q.Prime) (hq2 : q ≠ 2)
    (F : DirichletCharacter ℂ q → ℝ) (hF : ∀ χ, 0 ≤ F χ) :
    F (@quadCharPrime q ⟨hqp⟩) ≤
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive), F χ := by
  have : Fact q.Prime := ⟨hqp⟩
  exact Finset.single_le_sum (fun χ _ => hF χ)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, quadCharPrime_isPrimitive hq2⟩)

open Classical in
/-- **Unconditional Quadratic-Twist Multiplicative Large Sieve `L²` Bound over Odd Primes `q ≤ Q`**
(directly from `Stage11BombieriVinogradov.multiplicative_large_sieve_Ioc`):
for all `Q M N : ℕ` and any complex weights `a : ℕ → ℂ`,
`∑_{q ∈ [3, Q], q prime} ‖∑_{n ∈ (M, M+N]} a(n) (n / q)‖² ≤ (N + 3 Q²) * ∑_{n ∈ (M, M+N]} ‖a(n)‖²`. -/
theorem jacobi_large_sieve_l2_bound (Q M N : ℕ) (a : ℕ → ℂ) :
    ∑ q ∈ (Finset.Icc 3 Q).filter Nat.Prime,
        ‖∑ n ∈ Finset.Ioc M (M + N), a n * ((jacobiSym (n : ℤ) q : ℤ) : ℂ)‖ ^ 2 ≤
      ((N : ℝ) + 3 * (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  have hls := Stage11BombieriVinogradov.multiplicative_large_sieve_Ioc Q M N a
  refine le_trans ?_ hls
  have hterm : ∀ q ∈ (Finset.Icc 3 Q).filter Nat.Prime,
      ‖∑ n ∈ Finset.Ioc M (M + N), a n * ((jacobiSym (n : ℤ) q : ℤ) : ℂ)‖ ^ 2 ≤
        ((((q - 1) + 1 : ℕ) : ℝ) / (Nat.totient ((q - 1) + 1) : ℝ)) *
          ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ ((q - 1) + 1) => χ.IsPrimitive),
            ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ (n : ZMod ((q - 1) + 1))‖ ^ 2 := by
    intro q hq
    rw [Finset.mem_filter, Finset.mem_Icc] at hq
    obtain ⟨⟨hq3, _⟩, hqp⟩ := hq
    set q' := (q - 1) + 1 with hq'_def
    have hq_eq : q' = q := by omega
    have hqp' : q'.Prime := hq_eq.symm ▸ hqp
    have hq2' : q' ≠ 2 := by omega
    have hphi_pos : (0 : ℝ) < (q'.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hqp'.pos)
    have hratio_ge1 : (1 : ℝ) ≤ (q' : ℝ) / (q'.totient : ℝ) := by
      rw [one_le_div hphi_pos]
      exact_mod_cast Nat.totient_le q'
    have hle_sum := quadCharPrime_le_prim_sum hqp' hq2'
      (fun χ => ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ (n : ZMod q')‖ ^ 2)
      (fun _ => sq_nonneg _)
    have hcongr :
        ∑ n ∈ Finset.Ioc M (M + N), a n * ((jacobiSym (n : ℤ) q : ℤ) : ℂ) =
          ∑ n ∈ Finset.Ioc M (M + N), a n * (@quadCharPrime q' ⟨hqp'⟩) (n : ZMod q') := by
      refine Finset.sum_congr rfl fun n _ => ?_
      have : Fact q'.Prime := ⟨hqp'⟩
      rw [quadCharPrime_apply_nat hq2' n, hq_eq]
    rw [hcongr]
    calc ‖∑ n ∈ Finset.Ioc M (M + N), a n * (@quadCharPrime q' ⟨hqp'⟩) (n : ZMod q')‖ ^ 2
        = 1 * ‖∑ n ∈ Finset.Ioc M (M + N), a n * (@quadCharPrime q' ⟨hqp'⟩) (n : ZMod q')‖ ^ 2 := (one_mul _).symm
      _ ≤ ((q' : ℝ) / (q'.totient : ℝ)) *
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q' => χ.IsPrimitive),
              ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ (n : ZMod q')‖ ^ 2 :=
          mul_le_mul hratio_ge1 hle_sum (sq_nonneg _) (by positivity)
  have hsum1 := Finset.sum_le_sum hterm
  refine hsum1.trans ?_
  have hinj : Set.InjOn (fun q : ℕ => q - 1) ((Finset.Icc 3 Q).filter Nat.Prime) := by
    intro q₁ hq₁ q₂ hq₂ heq
    dsimp only at heq
    have h1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq₁).1).1
    have h2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq₂).1).1
    omega
  rw [← Finset.sum_image (f := fun k : ℕ =>
      (((k + 1 : ℕ) : ℝ) / (Nat.totient (k + 1) : ℝ)) *
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
          ‖∑ n ∈ Finset.Ioc M (M + N), a n * χ (n : ZMod (k + 1))‖ ^ 2) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => by positivity)
  intro k hk
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hk
  have hqI := Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1
  exact Finset.mem_range.mpr (by omega)

open Classical in
/-- **Unconditional Prime-Supported Quadratic-Twist Large Sieve `L²` Bound**
(directly from `Stage11LogFreeDensity.primitive_prime_large_sieve`):
saves the `1 / log H` Selberg-sieve factor over primes `p ∈ (x, x + H]` averaged over odd primes `q ≤ Q`. -/
theorem jacobi_prime_large_sieve_l2_bound (Q : ℕ) (hQ : 1 ≤ Q) (x H : ℕ)
    (hHQ : Q ^ 12 ≤ H) (hH16 : 16 ≤ H) (hzx : ⌊(H : ℝ) ^ (1 / 4 : ℝ)⌋₊ ≤ x) (a : ℕ → ℂ) :
    ∑ q ∈ (Finset.Icc 3 Q).filter Nat.Prime,
        ‖∑ p ∈ (Finset.Ioc x (x + H)).filter Nat.Prime, a p * ((jacobiSym (p : ℤ) q : ℤ) : ℂ)‖ ^ 2 ≤
      (20 * (H : ℝ) / Real.log (H : ℝ)) *
        ∑ p ∈ (Finset.Ioc x (x + H)).filter Nat.Prime, ‖a p‖ ^ 2 := by
  have hls := Stage11LogFreeDensity.primitive_prime_large_sieve Q hQ x H hHQ hH16 hzx a
  refine le_trans ?_ hls
  have hterm : ∀ q ∈ (Finset.Icc 3 Q).filter Nat.Prime,
      ‖∑ p ∈ (Finset.Ioc x (x + H)).filter Nat.Prime, a p * ((jacobiSym (p : ℤ) q : ℤ) : ℂ)‖ ^ 2 ≤
        ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ ((q - 1) + 1) => χ.IsPrimitive),
          ‖∑ p ∈ (Finset.Ioc x (x + H)).filter Nat.Prime, a p * χ (p : ZMod ((q - 1) + 1))‖ ^ 2 := by
    intro q hq
    rw [Finset.mem_filter, Finset.mem_Icc] at hq
    obtain ⟨⟨hq3, _⟩, hqp⟩ := hq
    set q' := (q - 1) + 1 with hq'_def
    have hq_eq : q' = q := by omega
    have hqp' : q'.Prime := hq_eq.symm ▸ hqp
    have hq2' : q' ≠ 2 := by omega
    have hcongr :
        ∑ p ∈ (Finset.Ioc x (x + H)).filter Nat.Prime, a p * ((jacobiSym (p : ℤ) q : ℤ) : ℂ) =
          ∑ p ∈ (Finset.Ioc x (x + H)).filter Nat.Prime, a p * (@quadCharPrime q' ⟨hqp'⟩) (p : ZMod q') := by
      refine Finset.sum_congr rfl fun p _ => ?_
      have : Fact q'.Prime := ⟨hqp'⟩
      rw [quadCharPrime_apply_nat hq2' p, hq_eq]
    rw [hcongr]
    exact quadCharPrime_le_prim_sum hqp' hq2'
      (fun χ => ‖∑ p ∈ (Finset.Ioc x (x + H)).filter Nat.Prime, a p * χ (p : ZMod q')‖ ^ 2)
      (fun _ => sq_nonneg _)
  refine (Finset.sum_le_sum hterm).trans ?_
  have hinj : Set.InjOn (fun q : ℕ => q - 1) ((Finset.Icc 3 Q).filter Nat.Prime) := by
    intro q₁ hq₁ q₂ hq₂ heq
    dsimp only at heq
    have h1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq₁).1).1
    have h2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq₂).1).1
    omega
  rw [← Finset.sum_image (f := fun k : ℕ =>
      ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
        ‖∑ p ∈ (Finset.Ioc x (x + H)).filter Nat.Prime, a p * χ (p : ZMod (k + 1))‖ ^ 2) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  intro k hk
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hk
  have hqI := Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1
  exact Finset.mem_range.mpr (by omega)

/-- **Montgomery–Vaughan Mean-Value Bound for Quadratic-Twist Dirichlet Polynomials**
(directly from `Stage10ZeroDensity.dirichletPoly_mean_value_upper`):
`∫_{-T}^T ‖∑_{n=1}^N a(n) (n / q) n^{-it}‖² dt ≤ (2 T + (8 π + 10) N) * ∑_{n=1}^N ‖a(n)‖²`. -/
theorem dirichletPoly_quadTwist_mean_value_upper (q N : ℕ) {T : ℝ} (hT : 0 ≤ T) (a : ℕ → ℂ) :
    ∫ t in (-T : ℝ)..T,
        ‖Stage10ZeroDensity.dirichletPoly (fun n => a n * ((jacobiSym (n : ℤ) q : ℤ) : ℂ)) N
          (Complex.I * (t : ℂ))‖ ^ 2 ≤
      (2 * T + (8 * Real.pi + 10) * (N : ℝ)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have hmv := Stage10ZeroDensity.dirichletPoly_mean_value_upper N T
    (fun n => a n * ((jacobiSym (n : ℤ) q : ℤ) : ℂ))
  refine hmv.trans ?_
  have hC : 0 ≤ 2 * T + (8 * Real.pi + 10) * (N : ℝ) := by positivity
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => ?_) hC
  rw [norm_mul, mul_pow]
  have hj : ‖((jacobiSym (n : ℤ) q : ℤ) : ℂ)‖ ^ 2 ≤ 1 := by
    rcases jacobiSym.trichotomy (n : ℤ) q with h | h | h <;> simp [h]
  nlinarith [sq_nonneg ‖a n‖]

/-! ### `MSqMainA` & `MSqMainB`: Quadratic Expansion, Diagonal Splitting & Scale Inequalities -/

/-- Exact quadratic expansion (`MSqMainA`, bridged to `ZeroDensityWindow.meansq_expand`). -/
theorem meansq_expand (PP I : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (κ : ℕ → ℂ)
    (hκ : ∀ n, ‖κ n‖ ≤ 1) (J : ℕ → ℕ → ℤ) :
    (∑ q ∈ PP, ‖∑ n ∈ I, ((c n : ℝ) : ℂ) * κ n * ((J n q : ℤ) : ℂ)‖ ^ 2) ≤
      ∑ n ∈ I, ∑ n' ∈ I, c n * c n' * |∑ q ∈ PP, ((J n q * J n' q : ℤ) : ℝ)| :=
  ZeroDensityWindow.meansq_expand PP I c (fun n _ => hc n) κ (fun n _ => hκ n) J

/-- Diagonal / exceptional-conductor / off-diagonal splitting (`MSqMainB`). -/
theorem meansq_split (I : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (r : ℕ → ℕ → ℕ) (A : ℕ → ℕ → ℝ)
    (P η : ℝ) (hP : 0 ≤ P) (hη : 0 ≤ η) (nstar : ℕ)
    (hA : ∀ n ∈ I, ∀ n' ∈ I, A n n' ≤ P)
    (hA' : ∀ n ∈ I, ∀ n' ∈ I, r n n' ≠ 1 → r n n' ≠ nstar → A n n' ≤ η * P) :
    ∑ n ∈ I, ∑ n' ∈ I, c n * c n' * A n n' ≤
      ((∑ n ∈ I, ∑ n' ∈ I, if r n n' = 1 then c n * c n' else 0) +
        (∑ n ∈ I, ∑ n' ∈ I, if r n n' = nstar then c n * c n' else 0) + η * (∑ n ∈ I, c n) ^ 2) * P := by
  have h1 := ZeroDensityWindow.meansq_split I c (fun n _ => hc n) r A P η hP hη nstar hA hA'
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ hP)
  have hmono :
      (∑ n ∈ I, ∑ n' ∈ I, if r n n' ≠ 1 ∧ r n n' = nstar then c n * c n' else 0) ≤
        ∑ n ∈ I, ∑ n' ∈ I, if r n n' = nstar then c n * c n' else 0 := by
    refine Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun n' _ => ?_
    have hcc : 0 ≤ c n * c n' := mul_nonneg (hc n) (hc n')
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd h1.2 h2
    · exact hcc
    · exact le_rfl
  linarith

/-- Scale inequality (`MSqMainB`): `x^(ε/6) ≤ log X` implies `x^800 ≤ X^(1/2)` for `x` large enough. -/
theorem pow_le_sqrt_of_rpow_le_log (ε : ℝ) (hε : 0 < ε) (x X : ℝ) (hx3 : 3 ≤ x)
    (hx : (19200 / ε) ^ (12 / ε) ≤ x) (hX : 0 < X) (hlog : x ^ (ε / 6) ≤ Real.log X) :
    x ^ 800 ≤ X ^ (1 / 2 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hε12 : 0 < ε / 12 := by positivity
  have hy1 : 1 < x ^ (ε / 12) := Real.one_lt_rpow hx1 hε12
  have hy0 : 0 < x ^ (ε / 12) := by linarith
  have hK0 : 0 < 19200 / ε := by positivity
  have hy : 19200 / ε ≤ x ^ (ε / 12) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hK0.le (12 / ε)) hx hε12.le
    rwa [← Real.rpow_mul hK0.le, show 12 / ε * (ε / 12) = 1 by field_simp, Real.rpow_one] at h
  have hlogx : Real.log x = 12 / ε * Real.log (x ^ (ε / 12)) := by
    rw [Real.log_rpow hx0]; field_simp
  have hy2 : x ^ (ε / 6) = (x ^ (ε / 12)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; congr 1; push_cast; ring
  have hlogy0 : 0 < Real.log (x ^ (ε / 12)) := Real.log_pos hy1
  have hlogy : Real.log (x ^ (ε / 12)) ≤ x ^ (ε / 12) :=
    (Real.log_le_sub_one_of_pos hy0).trans (by linarith)
  have key : 1600 * Real.log x ≤ Real.log X := by
    rw [hlogx]
    calc 1600 * (12 / ε * Real.log (x ^ (ε / 12))) = 19200 / ε * Real.log (x ^ (ε / 12)) := by ring
      _ ≤ x ^ (ε / 12) * Real.log (x ^ (ε / 12)) := mul_le_mul_of_nonneg_right hy hlogy0.le
      _ ≤ x ^ (ε / 12) * x ^ (ε / 12) := mul_le_mul_of_nonneg_left hlogy hy0.le
      _ = x ^ (ε / 6) := by rw [hy2]; ring
      _ ≤ Real.log X := hlog
  rw [← Real.log_le_log_iff (by positivity) (Real.rpow_pos_of_pos hX _), Real.log_pow,
    Real.log_rpow hX]
  push_cast
  linarith

/-- Final algebraic assembly inequality (`MSqMainB`): combines diagonal `Sd`, prime-power `R`,
exceptional `nstar` term, and off-diagonal `x^(-3) * S1^2` into `C * x * log x`. -/
theorem final_size (ε : ℝ) (hε1 : ε ≤ 1) (x : ℝ) (hx3 : 3 ≤ x) (C1 C2 C3 C4 S1 Sd R : ℝ)
    (hS0 : 0 ≤ S1) (hS1 : S1 ≤ C1 * x * Real.log x) (hSd : Sd ≤ C4 * x * Real.log x)
    (hR0 : 0 ≤ R) (hR : R ≤ C3 * (Real.sqrt x + x ^ (ε / 5) * Real.log x)) :
    Sd + R ^ 2 + (2 * (|C2| * Real.log x) ^ 2 + 2 * (|C2| * Real.log x) * R) + x ^ (-3 : ℝ) * S1 ^ 2 ≤
      (|C4| + 25 * C3 ^ 2 + 2 * C2 ^ 2 + 10 * |C2| * |C3| + C1 ^ 2) * x * Real.log x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hL1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]
    linarith [Real.exp_one_lt_d9]
  have hL0 : 0 ≤ Real.log x := by linarith
  have hLx : Real.log x ≤ x := (Real.log_le_sub_one_of_pos hx0).trans (by linarith)
  have hsx : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
  have hsqrt_le : Real.sqrt x ≤ x := by
    have h1 : Real.sqrt x * Real.sqrt x ≤ x * x := by rw [← sq, hsx]; nlinarith
    nlinarith [Real.sqrt_nonneg x]
  have hlog_rpow : ∀ α : ℝ, 0 < α → Real.log x ≤ x ^ α / α := by
    intro α hα
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 α)
    rw [Real.log_rpow hx0] at h
    rw [le_div_iff₀ hα]
    linarith
  have hL45 : Real.log x ≤ x ^ (4 / 5 : ℝ) / (4 / 5) := hlog_rpow (4 / 5) (by norm_num)
  have hL35 : Real.log x ≤ x ^ (3 / 5 : ℝ) / (3 / 5) := hlog_rpow (3 / 5) (by norm_num)
  have ha0 : 0 ≤ x ^ (ε / 5) := Real.rpow_nonneg hx0.le _
  have hab : x ^ (ε / 5) ≤ x ^ (1 / 5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hp45 : x ^ (1 / 5 : ℝ) * x ^ (4 / 5 : ℝ) = x := by
    rw [← Real.rpow_add hx0]; norm_num
  have hp35 : (x ^ (1 / 5 : ℝ)) ^ 2 * x ^ (3 / 5 : ℝ) = x := by
    rw [sq, ← Real.rpow_add hx0, ← Real.rpow_add hx0]; norm_num
  have hb0 : 0 ≤ x ^ (1 / 5 : ℝ) := Real.rpow_nonneg hx0.le _
  have haL : x ^ (ε / 5) * Real.log x ≤ 5 / 4 * x := by
    calc x ^ (ε / 5) * Real.log x ≤ x ^ (1 / 5 : ℝ) * (x ^ (4 / 5 : ℝ) / (4 / 5)) :=
          mul_le_mul hab hL45 hL0 hb0
      _ = 5 / 4 * (x ^ (1 / 5 : ℝ) * x ^ (4 / 5 : ℝ)) := by ring
      _ = 5 / 4 * x := by rw [hp45]
  have haL2 : (x ^ (ε / 5) * Real.log x) ^ 2 ≤ 5 / 3 * x * Real.log x := by
    have h1 : (x ^ (ε / 5)) ^ 2 ≤ (x ^ (1 / 5 : ℝ)) ^ 2 := pow_le_pow_left₀ ha0 hab 2
    calc (x ^ (ε / 5) * Real.log x) ^ 2 = (x ^ (ε / 5)) ^ 2 * Real.log x * Real.log x := by ring
      _ ≤ (x ^ (1 / 5 : ℝ)) ^ 2 * (x ^ (3 / 5 : ℝ) / (3 / 5)) * Real.log x := by
          apply mul_le_mul_of_nonneg_right _ hL0
          exact mul_le_mul h1 hL35 hL0 (sq_nonneg _)
      _ = 5 / 3 * ((x ^ (1 / 5 : ℝ)) ^ 2 * x ^ (3 / 5 : ℝ)) * Real.log x := by ring
      _ = 5 / 3 * x * Real.log x := by rw [hp35]
  set T := Real.sqrt x + x ^ (ε / 5) * Real.log x with hTdef
  have hT0 : 0 ≤ T := by positivity
  have hT : T ≤ 9 / 4 * x := by linarith
  have hT2 : T ^ 2 ≤ 16 / 3 * x * Real.log x := by
    have e : T ^ 2 = 2 * Real.sqrt x ^ 2 + 2 * (x ^ (ε / 5) * Real.log x) ^ 2 -
        (Real.sqrt x - x ^ (ε / 5) * Real.log x) ^ 2 := by rw [hTdef]; ring
    have hxL1 : x ≤ x * Real.log x := le_mul_of_one_le_right hx0.le hL1
    have hs := sq_nonneg (Real.sqrt x - x ^ (ε / 5) * Real.log x)
    rw [e, hsx]
    linarith
  have hR2 : R ^ 2 ≤ C3 ^ 2 * (16 / 3 * x * Real.log x) := by
    calc R ^ 2 ≤ (C3 * T) ^ 2 := pow_le_pow_left₀ hR0 hR 2
      _ = C3 ^ 2 * T ^ 2 := by ring
      _ ≤ C3 ^ 2 * (16 / 3 * x * Real.log x) := mul_le_mul_of_nonneg_left hT2 (sq_nonneg _)
  have hRT : R ≤ |C3| * T := hR.trans (mul_le_mul_of_nonneg_right (le_abs_self C3) hT0)
  have hxL : 0 ≤ x * Real.log x := mul_nonneg hx0.le hL0
  have e1 : Sd ≤ |C4| * x * Real.log x := by
    calc Sd ≤ C4 * x * Real.log x := hSd
      _ = C4 * (x * Real.log x) := by ring
      _ ≤ |C4| * (x * Real.log x) := mul_le_mul_of_nonneg_right (le_abs_self C4) hxL
      _ = |C4| * x * Real.log x := by ring
  have hC2 : 0 ≤ |C2| := abs_nonneg C2
  have hC3 : 0 ≤ |C3| := abs_nonneg C3
  have e3 : 2 * (|C2| * Real.log x) * R ≤ 9 / 2 * (|C2| * |C3|) * (x * Real.log x) := by
    have h1 : 0 ≤ 2 * (|C2| * Real.log x) := by positivity
    calc 2 * (|C2| * Real.log x) * R ≤ 2 * (|C2| * Real.log x) * (|C3| * T) :=
          mul_le_mul_of_nonneg_left hRT h1
      _ ≤ 2 * (|C2| * Real.log x) * (|C3| * (9 / 4 * x)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hT hC3) h1
      _ = 9 / 2 * (|C2| * |C3|) * (x * Real.log x) := by ring
  have e4 : 2 * (|C2| * Real.log x) ^ 2 ≤ 2 * C2 ^ 2 * (x * Real.log x) := by
    have : (|C2| * Real.log x) ^ 2 = C2 ^ 2 * (Real.log x * Real.log x) := by rw [mul_pow, sq_abs]; ring
    rw [this]
    have h2 : Real.log x * Real.log x ≤ x * Real.log x := mul_le_mul_of_nonneg_right hLx hL0
    have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg C2)
    linarith
  have e5 : x ^ (-3 : ℝ) * S1 ^ 2 ≤ C1 ^ 2 * (x * Real.log x) := by
    have hS2 : S1 ^ 2 ≤ (C1 * x * Real.log x) ^ 2 := pow_le_pow_left₀ hS0 hS1 2
    have hx3' : x ^ (-3 : ℝ) = (x ^ 3)⁻¹ := by
      rw [Real.rpow_neg hx0.le]; norm_cast
    rw [hx3']
    have hx30 : 0 < x ^ 3 := by positivity
    calc (x ^ 3)⁻¹ * S1 ^ 2 ≤ (x ^ 3)⁻¹ * (C1 * x * Real.log x) ^ 2 :=
          mul_le_mul_of_nonneg_left hS2 (inv_nonneg.mpr hx30.le)
      _ = C1 ^ 2 * (Real.log x * Real.log x) / x := by field_simp
      _ ≤ C1 ^ 2 * (x * Real.log x) := by
          rw [div_le_iff₀ hx0]
          have h3 : Real.log x * Real.log x ≤ x * Real.log x * x :=
            (mul_le_mul_of_nonneg_right hLx hL0).trans (le_mul_of_one_le_right hxL hx1)
          have h4 := mul_le_mul_of_nonneg_left h3 (sq_nonneg C1)
          linarith
  have hpos1 : 0 ≤ C3 ^ 2 * (x * Real.log x) := mul_nonneg (sq_nonneg _) hxL
  have hpos2 : 0 ≤ |C2| * |C3| * (x * Real.log x) := mul_nonneg (mul_nonneg hC2 hC3) hxL
  linarith

/-! ## Section 4: Diagonal & Prime-Power Pair Bounds (`MSqPairs`, `MSqDiagA`, `MSqDiagB`) -/

private lemma factorization_prime_pow_self (p k : ℕ) (hp : p.Prime) : (p ^ k).factorization p = k := by
  simp [Nat.factorization_pow, hp.factorization_self]

theorem soutPart_prime_pow (m₀ p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) :
    soutPart m₀ (p ^ k) = if Odd k ∧ ¬ p ∣ m₀ then p else 1 := by
  unfold soutPart
  rw [Nat.primeFactors_prime_pow hk hp, Finset.filter_singleton, factorization_prime_pow_self p k hp]
  split_ifs <;> simp

theorem soutPart_mul_of_coprime (m₀ a b : ℕ) (h : a.Coprime b) :
    soutPart m₀ (a * b) = soutPart m₀ a * soutPart m₀ b := by
  have hfac := Nat.factorization_mul_of_coprime h
  have hdisj := Nat.Coprime.disjoint_primeFactors h
  unfold soutPart
  rw [Nat.Coprime.primeFactors_mul h, Finset.filter_union,
    Finset.prod_union (Finset.disjoint_filter_filter hdisj)]
  congr 1
  · congr 1
    refine Finset.filter_congr fun q hq => ?_
    have hqb : q ∉ b.primeFactors := Finset.disjoint_left.1 hdisj hq
    have h0 : b.factorization q = 0 := by
      by_contra hne
      exact hqb (Nat.support_factorization b ▸ Finsupp.mem_support_iff.2 hne)
    rw [hfac, Finsupp.add_apply, h0, add_zero]
  · congr 1
    refine Finset.filter_congr fun q hq => ?_
    have hqa : q ∉ a.primeFactors := Finset.disjoint_right.1 hdisj hq
    have h0 : a.factorization q = 0 := by
      by_contra hne
      exact hqa (Nat.support_factorization a ▸ Finsupp.mem_support_iff.2 hne)
    rw [hfac, Finsupp.add_apply, h0, zero_add]

private lemma primePow_data {n : ℕ} (h : IsPrimePow n) :
    ∃ p k : ℕ, p.Prime ∧ k ≠ 0 ∧ n = p ^ k ∧ n.minFac = p ∧ n.factorization n.minFac = k := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 h
  have hm : (p ^ k).minFac = p := hp.pow_minFac hk.ne'
  refine ⟨p, k, hp, hk.ne', rfl, hm, ?_⟩
  rw [hm, factorization_prime_pow_self p k hp]

private def tPart (m₀ n : ℕ) : ℕ :=
  if _root_.Even (n.factorization n.minFac) ∨ n.minFac ∣ m₀ then 1 else n.minFac

private lemma soutPart_same {m₀ n n' : ℕ} (h : IsPrimePow n) (h' : IsPrimePow n')
    (he : n.minFac = n'.minFac) :
    soutPart m₀ (n * n') = 1 ∨ soutPart m₀ (n * n') = n.minFac := by
  obtain ⟨p, k, hp, hk, rfl, hm, -⟩ := primePow_data h
  obtain ⟨q, k', hq, hk', rfl, hm', -⟩ := primePow_data h'
  have hpq : p = q := hm.symm.trans (he.trans hm')
  subst hpq
  rw [← pow_add, soutPart_prime_pow m₀ p (k + k') hp (by omega), hm]
  split_ifs <;> simp

private lemma tPart_prime_pow_eq_soutPart (m₀ p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) :
    tPart m₀ (p ^ k) = soutPart m₀ (p ^ k) := by
  rw [soutPart_prime_pow m₀ p k hp hk]
  unfold tPart
  rw [hp.pow_minFac hk, factorization_prime_pow_self p k hp]
  rcases Nat.even_or_odd k with h1 | h1
  · have h1' : ¬ Odd k := Nat.not_odd_iff_even.2 h1
    simp [h1, h1']
  · have h1' : ¬ _root_.Even k := Nat.not_even_iff_odd.2 h1
    by_cases h2 : p ∣ m₀ <;> simp [h1, h1', h2]

private lemma soutPart_diff {m₀ n n' : ℕ} (h : IsPrimePow n) (h' : IsPrimePow n')
    (he : n.minFac ≠ n'.minFac) :
    soutPart m₀ (n * n') = tPart m₀ n * tPart m₀ n' := by
  obtain ⟨p, k, hp, hk, rfl, hm, -⟩ := primePow_data h
  obtain ⟨q, k', hq, hk', rfl, hm', -⟩ := primePow_data h'
  have hpq : p ≠ q := fun hpq => he (hm.trans (hpq.trans hm'.symm))
  have hcop : (p ^ k).Coprime (q ^ k') := Nat.Coprime.pow k k' ((Nat.coprime_primes hp hq).2 hpq)
  rw [soutPart_mul_of_coprime m₀ _ _ hcop, tPart_prime_pow_eq_soutPart m₀ p k hp hk,
    tPart_prime_pow_eq_soutPart m₀ q k' hq hk']

private def aW (c : ℕ → ℝ) (p n : ℕ) : ℝ :=
  if IsPrimePow n ∧ n.minFac = p then c n else 0

private def gW (c : ℕ → ℝ) (m₀ n : ℕ) : ℝ :=
  if IsPrimePow n ∧ (_root_.Even (n.factorization n.minFac) ∨ n.minFac ∣ m₀) then c n else 0

private lemma aW_nonneg {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) (p n : ℕ) : 0 ≤ aW c p n := by
  unfold aW; split_ifs <;> [exact hc n; exact le_refl 0]

private lemma gW_nonneg {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) (m₀ n : ℕ) : 0 ≤ gW c m₀ n := by
  unfold gW; split_ifs <;> [exact hc n; exact le_refl 0]

private lemma sum_aW_eq_sP (c : ℕ → ℝ) (N p : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, aW c p n = sP c N p := by
  unfold aW sP; rw [Finset.sum_filter]

private lemma sum_gW_eq_RR (c : ℕ → ℝ) (m₀ N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, gW c m₀ n = RR c m₀ N := by
  unfold gW RR; rw [Finset.sum_filter]

private lemma gW_eq_of_tPart_eq_one {c : ℕ → ℝ} {m₀ n : ℕ} (h : IsPrimePow n)
    (ht : tPart m₀ n = 1) : gW c m₀ n = c n := by
  have hcond : _root_.Even (n.factorization n.minFac) ∨ n.minFac ∣ m₀ := by
    unfold tPart at ht
    split_ifs at ht with h1
    · exact h1
    · exact absurd ht (Nat.minFac_prime h.ne_one).one_lt.ne'
  unfold gW; rw [if_pos ⟨h, hcond⟩]

private lemma tPart_cases (m₀ n : ℕ) : tPart m₀ n = 1 ∨ tPart m₀ n = n.minFac := by
  unfold tPart; split_ifs <;> simp

/-- Diagonal pair-sum bound (`soutPart m₀ (n * n') = 1`): bounded by `∑_p sP(p)² + RR²`. -/
theorem pairs_one (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hpp : ∀ n, c n ≠ 0 → IsPrimePow n) (m₀ N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, ∑ n' ∈ Finset.Icc 1 N,
        if soutPart m₀ (n * n') = 1 then c n * c n' else 0) ≤
      (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, sP c N p ^ 2) + RR c m₀ N ^ 2 := by
  have hpt : ∀ n ∈ Finset.Icc 1 N, ∀ n' ∈ Finset.Icc 1 N,
      (if soutPart m₀ (n * n') = 1 then c n * c n' else 0) ≤
        (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, aW c p n * aW c p n') + gW c m₀ n * gW c m₀ n' := by
    intro n hn n' hn'
    have hsum_nn : 0 ≤ ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, aW c p n * aW c p n' :=
      Finset.sum_nonneg fun p _ => mul_nonneg (aW_nonneg hc p n) (aW_nonneg hc p n')
    have hg_nn : 0 ≤ gW c m₀ n * gW c m₀ n' := mul_nonneg (gW_nonneg hc m₀ n) (gW_nonneg hc m₀ n')
    split_ifs with hs
    · by_cases hcn : c n = 0
      · rw [hcn, zero_mul]; linarith
      by_cases hcn' : c n' = 0
      · rw [hcn', mul_zero]; linarith
      have hp1 := hpp n hcn
      have hp2 := hpp n' hcn'
      by_cases he : n.minFac = n'.minFac
      · have hpmem : n.minFac ∈ (Finset.Icc 1 N).filter Nat.Prime := by
          rw [Finset.mem_filter, Finset.mem_Icc]
          have hmf_prime := Nat.minFac_prime hp1.ne_one
          have hmf_le : n.minFac ≤ n := Nat.minFac_le (Finset.mem_Icc.mp hn).1
          exact ⟨⟨hmf_prime.pos, hmf_le.trans (Finset.mem_Icc.mp hn).2⟩, hmf_prime⟩
        have hsingle : aW c n.minFac n * aW c n.minFac n' ≤
            ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, aW c p n * aW c p n' :=
          Finset.single_le_sum (fun p _ => mul_nonneg (aW_nonneg hc p n) (aW_nonneg hc p n')) hpmem
        have e1 : aW c n.minFac n = c n := by unfold aW; rw [if_pos ⟨hp1, rfl⟩]
        have e2 : aW c n.minFac n' = c n' := by unfold aW; rw [if_pos ⟨hp2, he.symm⟩]
        rw [e1, e2] at hsingle
        linarith
      · have hd := soutPart_diff (m₀ := m₀) hp1 hp2 he
        rw [hs] at hd
        have h1 : tPart m₀ n = 1 := Nat.eq_one_of_mul_eq_one_right hd.symm
        have h2 : tPart m₀ n' = 1 := Nat.eq_one_of_mul_eq_one_left hd.symm
        rw [gW_eq_of_tPart_eq_one hp1 h1, gW_eq_of_tPart_eq_one hp2 h2]
        linarith
    · linarith
  calc (∑ n ∈ Finset.Icc 1 N, ∑ n' ∈ Finset.Icc 1 N,
          if soutPart m₀ (n * n') = 1 then c n * c n' else 0)
      ≤ ∑ n ∈ Finset.Icc 1 N, ∑ n' ∈ Finset.Icc 1 N,
          ((∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, aW c p n * aW c p n') +
            gW c m₀ n * gW c m₀ n') :=
        Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun n' hn' => hpt n hn n' hn'
    _ = (∑ n ∈ Finset.Icc 1 N, ∑ n' ∈ Finset.Icc 1 N,
          ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, aW c p n * aW c p n') +
        (∑ n ∈ Finset.Icc 1 N, ∑ n' ∈ Finset.Icc 1 N, gW c m₀ n * gW c m₀ n') := by
        simp only [Finset.sum_add_distrib]
    _ = (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, sP c N p ^ 2) + RR c m₀ N ^ 2 := by
        congr 1
        · rw [Finset.sum_comm]
          have hswap : ∀ n ∈ Finset.Icc 1 N,
              ∑ n' ∈ Finset.Icc 1 N, ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, aW c p n * aW c p n' =
                ∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, ∑ n' ∈ Finset.Icc 1 N, aW c p n * aW c p n' :=
            fun _ _ => Finset.sum_comm
          rw [Finset.sum_comm]
          rw [Finset.sum_congr rfl hswap, Finset.sum_comm]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [← Finset.sum_mul_sum, sum_aW_eq_sP, sq]
        · rw [← Finset.sum_mul_sum, sum_gW_eq_RR, sq]

/-- Exceptional-conductor pair-sum bound (`soutPart m₀ (n * n') = r`, `1 < r`):
bounded by `2 * B² + 2 * B * RR` whenever `sP c N p ≤ B` for all `p`. -/
theorem pairs_r (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hpp : ∀ n, c n ≠ 0 → IsPrimePow n)
    (m₀ N r : ℕ) (hr : 1 < r) (B : ℝ) (hB : ∀ p, sP c N p ≤ B) :
    (∑ n ∈ Finset.Icc 1 N, ∑ n' ∈ Finset.Icc 1 N,
        if soutPart m₀ (n * n') = r then c n * c n' else 0) ≤
      2 * B ^ 2 + 2 * B * RR c m₀ N := by
  have hB0 : 0 ≤ B := (sP_nonneg c hc N 2).trans (hB 2)
  have hR0 : 0 ≤ RR c m₀ N := RR_nonneg c hc m₀ N
  by_cases hrp : r.Prime
  · have hpt : ∀ n n', (if soutPart m₀ (n * n') = r then c n * c n' else 0) ≤
        aW c r n * aW c r n' + aW c r n * gW c m₀ n' + gW c m₀ n * aW c r n' := by
      intro n n'
      have q1 := mul_nonneg (aW_nonneg hc r n) (aW_nonneg hc r n')
      have q2 := mul_nonneg (aW_nonneg hc r n) (gW_nonneg hc m₀ n')
      have q3 := mul_nonneg (gW_nonneg hc m₀ n) (aW_nonneg hc r n')
      split_ifs with hs
      · by_cases hcn : c n = 0
        · rw [hcn, zero_mul]; linarith
        by_cases hcn' : c n' = 0
        · rw [hcn', mul_zero]; linarith
        have hn := hpp n hcn
        have hn' := hpp n' hcn'
        by_cases he : n.minFac = n'.minFac
        · rcases soutPart_same (m₀ := m₀) hn hn' he with h1 | h1
          · exact absurd (hs.symm.trans h1) hrp.one_lt.ne'
          · have hnr : n.minFac = r := h1.symm.trans hs
            have hnr' : n'.minFac = r := he.symm.trans hnr
            have e1 : aW c r n = c n := by unfold aW; rw [if_pos ⟨hn, hnr⟩]
            have e2 : aW c r n' = c n' := by unfold aW; rw [if_pos ⟨hn', hnr'⟩]
            rw [e1, e2]
            have := mul_nonneg (hc n) (gW_nonneg hc m₀ n')
            have := mul_nonneg (gW_nonneg hc m₀ n) (hc n')
            linarith
        · have hd := soutPart_diff (m₀ := m₀) hn hn' he
          rw [hs] at hd
          have p1 := Nat.minFac_prime hn.ne_one
          have p2 := Nat.minFac_prime hn'.ne_one
          rcases tPart_cases m₀ n with t1 | t1 <;> rcases tPart_cases m₀ n' with t2 | t2 <;>
            rw [t1, t2] at hd
          · exact absurd (hd.trans (one_mul 1)) hrp.one_lt.ne'
          · have e1 : gW c m₀ n = c n := gW_eq_of_tPart_eq_one hn t1
            have e2 : aW c r n' = c n' := by unfold aW; rw [if_pos ⟨hn', by rw [hd, one_mul]⟩]
            rw [e1, e2]; have := mul_nonneg (aW_nonneg hc r n) (hc n'); linarith
          · have e1 : aW c r n = c n := by unfold aW; rw [if_pos ⟨hn, by rw [hd, mul_one]⟩]
            have e2 : gW c m₀ n' = c n' := gW_eq_of_tPart_eq_one hn' t2
            rw [e1, e2]; have := mul_nonneg (hc n) (aW_nonneg hc r n'); linarith
          · exfalso; rw [hd] at hrp
            rcases Nat.prime_mul_iff.1 hrp with ⟨-, h⟩ | ⟨-, h⟩
            · exact p2.one_lt.ne' h
            · exact p1.one_lt.ne' h
      · linarith
    have hsum :
        (∑ n ∈ Finset.Icc 1 N, ∑ n' ∈ Finset.Icc 1 N,
            if soutPart m₀ (n * n') = r then c n * c n' else 0) ≤
          sP c N r * sP c N r + sP c N r * RR c m₀ N + RR c m₀ N * sP c N r := by
      calc (∑ n ∈ Finset.Icc 1 N, ∑ n' ∈ Finset.Icc 1 N,
              if soutPart m₀ (n * n') = r then c n * c n' else 0)
          ≤ ∑ n ∈ Finset.Icc 1 N, ∑ n' ∈ Finset.Icc 1 N,
              (aW c r n * aW c r n' + aW c r n * gW c m₀ n' + gW c m₀ n * aW c r n') :=
            Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun n' _ => hpt n n'
        _ = sP c N r * sP c N r + sP c N r * RR c m₀ N + RR c m₀ N * sP c N r := by
            simp only [Finset.sum_add_distrib, ← Finset.sum_mul_sum, sum_aW_eq_sP, sum_gW_eq_RR]
    have h1 := hB r
    have h10 := sP_nonneg c hc N r
    nlinarith
  · have hpt : ∀ n n', (if soutPart m₀ (n * n') = r then c n * c n' else 0) ≤
        aW c r.minFac n * aW c (r / r.minFac) n' + aW c (r / r.minFac) n * aW c r.minFac n' := by
      intro n n'
      have q1 := mul_nonneg (aW_nonneg hc r.minFac n) (aW_nonneg hc (r / r.minFac) n')
      have q2 := mul_nonneg (aW_nonneg hc (r / r.minFac) n) (aW_nonneg hc r.minFac n')
      split_ifs with hs
      · by_cases hcn : c n = 0
        · rw [hcn, zero_mul]; linarith
        by_cases hcn' : c n' = 0
        · rw [hcn', mul_zero]; linarith
        have hn := hpp n hcn
        have hn' := hpp n' hcn'
        by_cases he : n.minFac = n'.minFac
        · exfalso
          rcases soutPart_same (m₀ := m₀) hn hn' he with h1 | h1
          · exact absurd (hs.symm.trans h1) hr.ne'
          · exact hrp ((h1.symm.trans hs) ▸ Nat.minFac_prime hn.ne_one)
        · have hd := soutPart_diff (m₀ := m₀) hn hn' he
          rw [hs] at hd
          have p1 := Nat.minFac_prime hn.ne_one
          have p2 := Nat.minFac_prime hn'.ne_one
          rcases tPart_cases m₀ n with t1 | t1 <;> rcases tPart_cases m₀ n' with t2 | t2 <;>
            rw [t1, t2] at hd
          · exact absurd (hd.trans (one_mul 1)) hr.ne'
          · exact absurd (by rw [hd, one_mul]; exact p2) hrp
          · exact absurd (by rw [hd, mul_one]; exact p1) hrp
          · have hm_dvd : r.minFac ∣ n.minFac * n'.minFac := hd ▸ Nat.minFac_dvd r
            have hm_p := Nat.minFac_prime hr.ne'
            rcases hm_p.dvd_mul.1 hm_dvd with h1 | h1
            · have heq1 : n.minFac = r.minFac := ((Nat.prime_dvd_prime_iff_eq hm_p p1).1 h1).symm
              have hmul_eq : r = n'.minFac * r.minFac := by
                calc r = n.minFac * n'.minFac := hd
                  _ = r.minFac * n'.minFac := by rw [heq1]
                  _ = n'.minFac * r.minFac := mul_comm _ _
              have heq2 : n'.minFac = r / r.minFac :=
                (Nat.div_eq_of_eq_mul_left hm_p.pos hmul_eq).symm
              have e1 : aW c r.minFac n = c n := by unfold aW; rw [if_pos ⟨hn, heq1⟩]
              have e2 : aW c (r / r.minFac) n' = c n' := by unfold aW; rw [if_pos ⟨hn', heq2⟩]
              rw [e1, e2]; linarith
            · have heq2 : n'.minFac = r.minFac := ((Nat.prime_dvd_prime_iff_eq hm_p p2).1 h1).symm
              have hmul_eq : r = n.minFac * r.minFac := by
                calc r = n.minFac * n'.minFac := hd
                  _ = n.minFac * r.minFac := by rw [heq2]
              have heq1 : n.minFac = r / r.minFac :=
                (Nat.div_eq_of_eq_mul_left hm_p.pos hmul_eq).symm
              have e1 : aW c (r / r.minFac) n = c n := by unfold aW; rw [if_pos ⟨hn, heq1⟩]
              have e2 : aW c r.minFac n' = c n' := by unfold aW; rw [if_pos ⟨hn', heq2⟩]
              rw [e1, e2]; linarith
      · linarith
    have hsum :
        (∑ n ∈ Finset.Icc 1 N, ∑ n' ∈ Finset.Icc 1 N,
            if soutPart m₀ (n * n') = r then c n * c n' else 0) ≤
          sP c N r.minFac * sP c N (r / r.minFac) + sP c N (r / r.minFac) * sP c N r.minFac := by
      calc (∑ n ∈ Finset.Icc 1 N, ∑ n' ∈ Finset.Icc 1 N,
              if soutPart m₀ (n * n') = r then c n * c n' else 0)
          ≤ ∑ n ∈ Finset.Icc 1 N, ∑ n' ∈ Finset.Icc 1 N,
              (aW c r.minFac n * aW c (r / r.minFac) n' + aW c (r / r.minFac) n * aW c r.minFac n') :=
            Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun n' _ => hpt n n'
        _ = sP c N r.minFac * sP c N (r / r.minFac) + sP c N (r / r.minFac) * sP c N r.minFac := by
            simp only [Finset.sum_add_distrib, ← Finset.sum_mul_sum, sum_aW_eq_sP]
    have h1 := hB r.minFac
    have h2 := hB (r / r.minFac)
    have h10 := sP_nonneg c hc N r.minFac
    have h20 := sP_nonneg c hc N (r / r.minFac)
    have hmul : sP c N r.minFac * sP c N (r / r.minFac) ≤ B ^ 2 := by
      rw [sq]; exact mul_le_mul h1 h2 h20 hB0
    have hmul' : sP c N (r / r.minFac) * sP c N r.minFac ≤ B ^ 2 := by
      rw [mul_comm]; exact hmul
    nlinarith

/-! ### Elementary Chebyshev & Prime-Power Weight Bounds (`MSqDiagA`, `MSqDiagB`) -/

private lemma sum_vM_Icc_le (N : ℕ) : ∑ n ∈ Finset.Icc 1 N, Λ n ≤ 6 * (N : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have hpsi := Stage4ExplicitFormula.chebyshevPsi_le_six_mul (x := (N : ℝ)) (by exact_mod_cast hN)
    refine le_trans ?_ hpsi
    unfold RHDirect.chebyshevPsi
    rw [Nat.floor_natCast]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    rw [Finset.mem_Icc] at hn; exact Finset.mem_range.mpr (by omega)

private lemma vM_major_abel (g : ℕ → ℝ) (hg0 : ∀ n, 0 ≤ g n) (hg : ∀ n, 1 ≤ n → g (n + 1) ≤ g n) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, Λ n * g n ≤ 6 * ∑ n ∈ Finset.Icc 1 N, g n := by
  have key : ∀ M : ℕ, (∑ n ∈ Finset.Icc 1 M, Λ n * g n) - (∑ n ∈ Finset.Icc 1 M, Λ n) * g M ≤
      6 * ((∑ n ∈ Finset.Icc 1 M, g n) - (M : ℝ) * g M) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_Icc_succ_top (show 1 ≤ M + 1 by omega),
        Finset.sum_Icc_succ_top (show 1 ≤ M + 1 by omega),
        Finset.sum_Icc_succ_top (show 1 ≤ M + 1 by omega)]
      have h1 : (∑ n ∈ Finset.Icc 1 M, Λ n) * (g M - g (M + 1)) ≤
          6 * (M : ℝ) * (g M - g (M + 1)) := by
        rcases Nat.eq_zero_or_pos M with rfl | hpos
        · simp
        · exact mul_le_mul_of_nonneg_right (sum_vM_Icc_le M) (by linarith [hg M hpos])
      push_cast; linarith
  have h2 : (∑ n ∈ Finset.Icc 1 N, Λ n) * g N ≤ 6 * (N : ℝ) * g N :=
    mul_le_mul_of_nonneg_right (sum_vM_Icc_le N) (hg0 N)
  linarith [key N]

private lemma sum_inv_Icc_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / (n : ℝ) ≤ 1 + Real.log (N : ℝ) := by
  induction N with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [Finset.sum_Icc_succ_top (by omega)]
      have ihk := ih hk
      have hk0 : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
      have hk1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
      have hstep : (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ≤ Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) := by
        rw [← Real.log_div hk1.ne' hk0.ne']
        have hpos : (0 : ℝ) < (k : ℝ) / ((k + 1 : ℕ) : ℝ) := div_pos hk0 hk1
        have hle := Real.log_le_sub_one_of_pos hpos
        rw [Real.log_div hk0.ne' hk1.ne'] at hle
        have heq : 1 - (k : ℝ) / ((k + 1 : ℕ) : ℝ) = 1 / ((k + 1 : ℕ) : ℝ) := by
          push_cast; field_simp; ring
        have hlog_neg : Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ)) = -(Real.log (k : ℝ) - Real.log ((k + 1 : ℕ) : ℝ)) := by
          rw [Real.log_div hk1.ne' hk0.ne']; ring
        rw [hlog_neg]
        linarith
      linarith

/-- Total weight bound `∑_{n=1}^{⌊x^400⌋} cN x n ≤ C1 * x * log x` (`MSqDiagA`). -/
theorem sum_cN_le :
    ∃ C1 x1 : ℝ, 0 < C1 ∧ 2 ≤ x1 ∧ ∀ x : ℝ, x1 ≤ x →
      ∑ n ∈ Finset.Icc 1 ⌊x ^ 400⌋₊, cN x n ≤ C1 * x * Real.log x := by
  refine ⟨2500, 3, by norm_num, by norm_num, fun x hx3 => ?_⟩
  have hx0 : 0 < x := by linarith
  have hL1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; linarith [Real.exp_one_lt_d9]
  set N := ⌊x ^ 400⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by
    rw [Nat.cast_one]; exact one_le_pow₀ (by linarith : (1 : ℝ) ≤ x))
  have hNR : (N : ℝ) ≤ x ^ 400 := Nat.floor_le (by positivity)
  have hM : ∑ n ∈ Finset.Icc 1 N, Λ n / (n : ℝ) ≤ 2500 * Real.log x := by
    have h1 : ∑ n ∈ Finset.Icc 1 N, Λ n / (n : ℝ) = ∑ n ∈ Finset.Icc 1 N, Λ n * (1 / (n : ℝ)) :=
      Finset.sum_congr rfl fun n _ => by ring
    rw [h1]
    have h2 := vM_major_abel (fun n => 1 / (n : ℝ)) (fun n => by positivity)
      (fun n hn => one_div_le_one_div_of_le (Nat.cast_pos.mpr hn) (by exact_mod_cast (by omega : n ≤ n + 1))) N
    have h3 := sum_inv_Icc_le N hN1
    have hlogN : Real.log (N : ℝ) ≤ 400 * Real.log x := by
      calc Real.log (N : ℝ) ≤ Real.log (x ^ 400) := Real.log_le_log (Nat.cast_pos.mpr hN1) hNR
        _ = 400 * Real.log x := by rw [Real.log_pow]; norm_num
    linarith
  have hstep : ∑ n ∈ Finset.Icc 1 N, cN x n ≤ x * ∑ n ∈ Finset.Icc 1 N, Λ n / (n : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    unfold cN ZeroDensityWindow.cN
    calc Λ n * min 1 (x / (n : ℝ)) ≤ Λ n * (x / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) ArithmeticFunction.vonMangoldt_nonneg
      _ = x * (Λ n / (n : ℝ)) := by ring
  calc ∑ n ∈ Finset.Icc 1 N, cN x n ≤ x * (2500 * Real.log x) :=
        hstep.trans (mul_le_mul_of_nonneg_left hM hx0.le)
    _ = 2500 * x * Real.log x := by ring

private lemma geom_sum_inv_pow_le {p : ℕ} (hp : 2 ≤ p) (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / ((p : ℝ) ^ k) ≤ 2 / (p : ℝ) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  set r : ℝ := 1 / (p : ℝ)
  have hr0 : 0 ≤ r := by positivity
  have hr_half : r ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hpR
  have hrew : ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / ((p : ℝ) ^ k) = r * ∑ j ∈ Finset.range K, r ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_bij (fun k _ => k - 1) (fun k hk => Finset.mem_range.mpr (by
      have := Finset.mem_Icc.mp hk; omega)) (fun k₁ hk₁ k₂ hk₂ heq => by
      have h1 := Finset.mem_Icc.mp hk₁; have h2 := Finset.mem_Icc.mp hk₂; omega)
      (fun j hj => ⟨j + 1, Finset.mem_Icc.mpr ⟨by omega, by have := Finset.mem_range.mp hj; omega⟩, by omega⟩)
      (fun k hk => ?_)
    have hk1 := (Finset.mem_Icc.mp hk).1
    have hpow : k = (k - 1) + 1 := by omega
    dsimp only [r]
    rw [one_div_pow]
    conv_lhs => rw [hpow, pow_succ]
    ring
  rw [hrew, geom_sum_eq (by linarith : r ≠ 1)]
  have h1 : (r ^ K - 1) / (r - 1) = (1 - r ^ K) / (1 - r) := by
    rw [← neg_div_neg_eq]; ring_nf
  rw [h1]
  have h1r : (1 / 2 : ℝ) ≤ 1 - r := by linarith
  have hnum : 1 - r ^ K ≤ 1 := by linarith [pow_nonneg hr0 K]
  have hdiv : (1 - r ^ K) / (1 - r) ≤ 2 := by
    rw [div_le_iff₀ (by linarith : 0 < 1 - r)]; linarith
  calc r * ((1 - r ^ K) / (1 - r)) ≤ r * 2 := mul_le_mul_of_nonneg_left hdiv hr0
    _ = 2 / (p : ℝ) := by dsimp only [r]; ring

/-- Prime-power sum bound `sP (cN x) N p ≤ 2 * x * log p / p` for every prime `p`. -/
theorem sP_cN_le_log_div (x : ℝ) (hx : 0 ≤ x) (N p : ℕ) (hp : p.Prime) :
    sP (cN x) N p ≤ 2 * x * Real.log p / (p : ℝ) := by
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hsub : (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p) ⊆
      (Finset.Icc 1 N).image (fun k => p ^ k) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨p', k, hp', hk, rfl, hm, -⟩ := primePow_data hn.2.1
    have hpq : p' = p := hm.symm.trans hn.2.2
    cases hpq
    rw [Finset.mem_image]
    refine ⟨k, Finset.mem_Icc.mpr ⟨by omega, ?_⟩, rfl⟩
    have hlt : k ≤ p ^ k := le_of_lt (Nat.lt_pow_self hp.one_lt)
    exact hlt.trans hn.1.2
  have hinj : Set.InjOn (fun k : ℕ => p ^ k) (Finset.Icc 1 N) := fun a _ b _ hab =>
    Nat.pow_right_injective hp.two_le hab
  calc sP (cN x) N p
      ≤ ∑ n ∈ (Finset.Icc 1 N).image (fun k => p ^ k), cN x n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => cN_nonneg x hx n)
    _ = ∑ k ∈ Finset.Icc 1 N, cN x (p ^ k) := Finset.sum_image hinj
    _ ≤ ∑ k ∈ Finset.Icc 1 N, (x * Real.log p) * (1 / ((p : ℝ) ^ k)) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk1 : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
        unfold cN ZeroDensityWindow.cN
        rw [ArithmeticFunction.vonMangoldt_apply_pow hk1, ArithmeticFunction.vonMangoldt_apply_prime hp]
        have hmin : min 1 (x / ((p ^ k : ℕ) : ℝ)) ≤ x / ((p : ℝ) ^ k) := by
          push_cast; exact min_le_right _ _
        calc Real.log p * min 1 (x / ((p ^ k : ℕ) : ℝ))
            ≤ Real.log p * (x / ((p : ℝ) ^ k)) := mul_le_mul_of_nonneg_left hmin hlog
          _ = (x * Real.log p) * (1 / ((p : ℝ) ^ k)) := by ring
    _ = (x * Real.log p) * ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / ((p : ℝ) ^ k) := by
        rw [← Finset.mul_sum]
    _ ≤ (x * Real.log p) * (2 / (p : ℝ)) :=
        mul_le_mul_of_nonneg_left (geom_sum_inv_pow_le hp.two_le N) (mul_nonneg hx hlog)
    _ = 2 * x * Real.log p / (p : ℝ) := by ring

private lemma log_div_le_of_three_le {a b : ℝ} (ha : 3 ≤ a) (hab : a ≤ b) :
    Real.log b / b ≤ Real.log a / a := by
  have hanti : AntitoneOn (fun t : ℝ => Real.log t / t) (Set.Ici 3) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 3)
    · refine ContinuousOn.div (Real.continuousOn_log.mono fun t ht => ne_of_gt (by linarith [Set.mem_Ici.mp ht]))
        continuousOn_id (fun t ht => ne_of_gt (by linarith [Set.mem_Ici.mp ht]))
    · intro t ht
      have ht3 : 3 ≤ t := Set.mem_Ici.mp (interior_subset ht)
      have ht0 : 0 < t := by linarith
      exact ((Real.differentiableAt_log ht0.ne').div differentiableAt_id ht0.ne').differentiableWithinAt
    · intro t ht
      have ht3 : 3 ≤ t := Set.mem_Ici.mp (interior_subset ht)
      have ht0 : 0 < t := by linarith
      have hd : HasDerivAt (fun u : ℝ => Real.log u / u) ((1 - Real.log t) / t ^ 2) t := by
        have h1 : HasDerivAt (fun u : ℝ => Real.log u / u) ((t⁻¹ * t - Real.log t * 1) / t ^ 2) t :=
          (Real.hasDerivAt_log ht0.ne').div (hasDerivAt_id t) ht0.ne'
        have hinv : (t⁻¹ * t - Real.log t * 1) / t ^ 2 = (1 - Real.log t) / t ^ 2 := by
          rw [inv_mul_cancel₀ ht0.ne', mul_one]
        rwa [hinv] at h1
      rw [hd.deriv]
      have hL1 : 1 ≤ Real.log t := by
        rw [Real.le_log_iff_exp_le ht0]; linarith [Real.exp_one_lt_d9]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg t)
  exact hanti ha (ha.trans hab) hab

/-- Uniform prime-power weight bound `sP (cN x) N p ≤ 4 * Real.log x` for all `x ≥ 3` and all `p` (`MSqDiagA`). -/
theorem sP_cN_le_four_log {x : ℝ} (hx : 3 ≤ x) (N p : ℕ) :
    sP (cN x) N p ≤ 4 * Real.log x := by
  have hx0 : 0 < x := by linarith
  have hLx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  by_cases hp : p.Prime
  · by_cases hpx : (p : ℝ) ≤ x
    · have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
      have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
      have hlp : 0 < Real.log (p : ℝ) := Real.log_pos (by linarith)
      have hlp_le : Real.log (p : ℝ) ≤ Real.log x := Real.log_le_log hp0 hpx
      have hsub : (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p) ⊆
          (Finset.Icc 1 N).image (fun k => p ^ k) := by
        intro n hn
        rw [Finset.mem_filter, Finset.mem_Icc] at hn
        obtain ⟨p', k, _, hk, rfl, hm, -⟩ := primePow_data hn.2.1
        have hpq : p' = p := hm.symm.trans hn.2.2; subst hpq
        exact Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨by omega, (le_of_lt (Nat.lt_pow_self hp.one_lt)).trans hn.1.2⟩, rfl⟩
      have hinj : Set.InjOn (fun k : ℕ => p ^ k) (Finset.Icc 1 N) := fun a _ b _ hab =>
        Nat.pow_right_injective hp.two_le hab
      set K := ⌊Real.log x / Real.log (p : ℝ)⌋₊
      have hK_le : (K : ℝ) ≤ Real.log x / Real.log (p : ℝ) := Nat.floor_le (div_nonneg hLx hlp.le)
      have hsplit : ∑ k ∈ Finset.Icc 1 N, cN x (p ^ k) ≤
          (∑ k ∈ (Finset.Icc 1 N).filter (· ≤ K), cN x (p ^ k)) +
          (∑ k ∈ (Finset.Icc 1 N).filter (fun k => ¬ k ≤ K), cN x (p ^ k)) := by
        rw [Finset.sum_filter_add_sum_filter_not]
      have hpart1 : ∑ k ∈ (Finset.Icc 1 N).filter (· ≤ K), cN x (p ^ k) ≤ Real.log x := by
        have hsubK : (Finset.Icc 1 N).filter (· ≤ K) ⊆ Finset.Icc 1 K := fun k hk => by
          rw [Finset.mem_filter, Finset.mem_Icc] at hk; exact Finset.mem_Icc.mpr ⟨hk.1.1, hk.2⟩
        calc ∑ k ∈ (Finset.Icc 1 N).filter (· ≤ K), cN x (p ^ k)
            ≤ ∑ k ∈ (Finset.Icc 1 N).filter (· ≤ K), Real.log (p : ℝ) := by
              refine Finset.sum_le_sum fun k hk => ?_
              have hk1 : k ≠ 0 := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1; omega
              unfold cN ZeroDensityWindow.cN
              rw [ArithmeticFunction.vonMangoldt_apply_pow hk1, ArithmeticFunction.vonMangoldt_apply_prime hp]
              exact mul_le_of_le_one_right hlp.le (min_le_left _ _)
          _ = (((Finset.Icc 1 N).filter (· ≤ K)).card : ℝ) * Real.log (p : ℝ) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (K : ℝ) * Real.log (p : ℝ) := by
              have hc : ((Finset.Icc 1 N).filter (· ≤ K)).card ≤ K :=
                (Finset.card_le_card hsubK).trans (by simp)
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hlp.le
          _ ≤ (Real.log x / Real.log (p : ℝ)) * Real.log (p : ℝ) :=
              mul_le_mul_of_nonneg_right hK_le hlp.le
          _ = Real.log x := div_mul_cancel₀ _ hlp.ne'
      have hpart2 : ∑ k ∈ (Finset.Icc 1 N).filter (fun k => ¬ k ≤ K), cN x (p ^ k) ≤ 2 * Real.log x := by
        have hx_le_pK1 : x ≤ (p : ℝ) ^ (K + 1) := by
          have hlt : Real.log x / Real.log (p : ℝ) < (K : ℝ) + 1 := Nat.lt_floor_add_one _
          have hlt' : Real.log x / Real.log (p : ℝ) < ((K + 1 : ℕ) : ℝ) := by push_cast; exact hlt
          have hmul : Real.log x < ((K + 1 : ℕ) : ℝ) * Real.log (p : ℝ) := (div_lt_iff₀ hlp).mp hlt'
          rw [← Real.log_pow] at hmul
          exact ((Real.log_lt_log_iff hx0 (pow_pos hp0 _)).mp hmul).le
        have hterm : ∀ k ∈ (Finset.Icc 1 N).filter (fun k => ¬ k ≤ K),
            cN x (p ^ k) ≤ Real.log (p : ℝ) * (1 / (p : ℝ) ^ (k - (K + 1))) := by
          intro k hk
          rw [Finset.mem_filter, Finset.mem_Icc] at hk
          have hk1 : k ≠ 0 := by omega
          have hkge : K + 1 ≤ k := by omega
          unfold cN ZeroDensityWindow.cN
          rw [ArithmeticFunction.vonMangoldt_apply_pow hk1, ArithmeticFunction.vonMangoldt_apply_prime hp]
          have hpow_eq : ((p ^ k : ℕ) : ℝ) = (p : ℝ) ^ (K + 1) * (p : ℝ) ^ (k - (K + 1)) := by
            push_cast; rw [← pow_add]; congr 1; omega
          have hdiv : x / ((p ^ k : ℕ) : ℝ) ≤ 1 / (p : ℝ) ^ (k - (K + 1)) := by
            rw [hpow_eq, div_le_div_iff₀ (mul_pos (pow_pos hp0 _) (pow_pos hp0 _)) (pow_pos hp0 _)]
            nlinarith [pow_pos hp0 (k - (K + 1))]
          exact mul_le_mul_of_nonneg_left ((min_le_right _ _).trans hdiv) hlp.le
        have hsum_le : ∑ k ∈ (Finset.Icc 1 N).filter (fun k => ¬ k ≤ K), cN x (p ^ k) ≤
            Real.log (p : ℝ) * ∑ j ∈ Finset.range (N + 1), (1 / (p : ℝ)) ^ j := by
          calc ∑ k ∈ (Finset.Icc 1 N).filter (fun k => ¬ k ≤ K), cN x (p ^ k)
              ≤ ∑ k ∈ (Finset.Icc 1 N).filter (fun k => ¬ k ≤ K),
                  Real.log (p : ℝ) * (1 / (p : ℝ) ^ (k - (K + 1))) := Finset.sum_le_sum hterm
            _ = Real.log (p : ℝ) * ∑ k ∈ (Finset.Icc 1 N).filter (fun k => ¬ k ≤ K),
                  (1 / (p : ℝ)) ^ (k - (K + 1)) := by
                rw [Finset.mul_sum]; congr 1; ext k; rw [one_div_pow]
            _ ≤ Real.log (p : ℝ) * ∑ j ∈ Finset.range (N + 1), (1 / (p : ℝ)) ^ j := by
                refine mul_le_mul_of_nonneg_left ?_ hlp.le
                have hinj2 : Set.InjOn (fun k => k - (K + 1)) ((Finset.Icc 1 N).filter (fun k => ¬ k ≤ K)) := by
                  intro a ha b hb hab
                  have ha' := (Finset.mem_filter.mp ha).2
                  have hb' := (Finset.mem_filter.mp hb).2
                  dsimp only at hab; omega
                rw [← Finset.sum_image (f := fun j => (1 / (p : ℝ)) ^ j) hinj2]
                refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) (fun _ _ _ => by positivity)
                obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
                have hkN := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).2
                exact Finset.mem_range.mpr (by omega)
        have hgeom : ∑ j ∈ Finset.range (N + 1), (1 / (p : ℝ)) ^ j ≤ 2 := by
          set r : ℝ := 1 / (p : ℝ)
          have hr_half : r ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hpR
          rw [geom_sum_eq (by linarith : r ≠ 1)]
          have h1 : (r ^ (N + 1) - 1) / (r - 1) = (1 - r ^ (N + 1)) / (1 - r) := by
            rw [← neg_div_neg_eq]; ring_nf
          rw [h1, div_le_iff₀ (by linarith : 0 < 1 - r)]
          linarith [pow_nonneg (by positivity : 0 ≤ r) (N + 1)]
        calc ∑ k ∈ (Finset.Icc 1 N).filter (fun k => ¬ k ≤ K), cN x (p ^ k)
            ≤ Real.log (p : ℝ) * 2 := hsum_le.trans (mul_le_mul_of_nonneg_left hgeom hlp.le)
          _ ≤ 2 * Real.log x := by linarith
      calc sP (cN x) N p
          ≤ ∑ n ∈ (Finset.Icc 1 N).image (fun k => p ^ k), cN x n :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => cN_nonneg x hx0.le n)
        _ = ∑ k ∈ Finset.Icc 1 N, cN x (p ^ k) := Finset.sum_image hinj
        _ ≤ Real.log x + 2 * Real.log x := by linarith
        _ ≤ 4 * Real.log x := by linarith
    · push Not at hpx
      have hle := sP_cN_le_log_div x hx0.le N p hp
      have hdiv := log_div_le_of_three_le hx hpx.le
      calc sP (cN x) N p ≤ 2 * x * Real.log (p : ℝ) / (p : ℝ) := hle
        _ = 2 * x * (Real.log (p : ℝ) / (p : ℝ)) := by ring
        _ ≤ 2 * x * (Real.log x / x) := mul_le_mul_of_nonneg_left hdiv (by positivity)
        _ = 2 * Real.log x := by field_simp [hx0.ne']
        _ ≤ 4 * Real.log x := by linarith
  · have hemp : (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p) = ∅ := by
      ext n; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
      rintro ⟨-, hpp, rfl⟩
      exact hp (Nat.minFac_prime hpp.ne_one)
    unfold sP; rw [hemp, Finset.sum_empty]; positivity

theorem exists_primePowerSum_le :
    ∃ C2 x2 : ℝ, 0 < C2 ∧ 3 ≤ x2 ∧ ∀ x : ℝ, x2 ≤ x → ∀ p : ℕ,
      sP (cN x) ⌊x ^ 400⌋₊ p ≤ C2 * Real.log x :=
  ⟨4, 3, by norm_num, le_rfl, fun x hx p => sP_cN_le_four_log hx _ p⟩

private lemma sum_inv_sq_tail_le (K M : ℕ) (hK : 1 ≤ K) :
    ∑ m ∈ Finset.Ioc K M, (1 : ℝ) / ((m : ℝ) ^ 2) ≤ 2 / (K : ℝ) := by
  have h1 : ∀ m ∈ Finset.Ioc K M, (1 : ℝ) / ((m : ℝ) ^ 2) ≤
      (1 : ℝ) / ((m - 1 : ℕ) : ℝ) - (1 : ℝ) / (m : ℝ) := by
    intro m hm
    have hmK := (Finset.mem_Ioc.mp hm).1
    have hm2 : 2 ≤ m := by omega
    have hm0 : (0 : ℝ) < (m : ℝ) := by positivity
    have hm1 : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    rw [hcast, div_sub_div _ _ (by linarith) hm0.ne', one_mul, mul_one,
      show (m : ℝ) - ((m : ℝ) - 1) = 1 by ring]
    exact one_div_le_one_div_of_le (mul_pos (by linarith) hm0) (by nlinarith)
  by_cases hKM : M ≤ K
  · rw [Finset.Ioc_eq_empty_of_le hKM, Finset.sum_empty]; positivity
  · push Not at hKM
    have htele : ∀ n : ℕ, K ≤ n →
        ∑ m ∈ Finset.Ioc K n, ((1 : ℝ) / ((m - 1 : ℕ) : ℝ) - (1 : ℝ) / (m : ℝ)) =
          1 / (K : ℝ) - 1 / (n : ℝ) := by
      intro n hn
      induction n with
      | zero => omega
      | succ d ih =>
        by_cases hKd : K ≤ d
        · have hsplit : Finset.Ioc K (d + 1) = insert (d + 1) (Finset.Ioc K d) := by
            ext x; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
          have hnot : d + 1 ∉ Finset.Ioc K d := by simp
          rw [hsplit, Finset.sum_insert hnot, ih hKd]
          simp only [Nat.add_sub_cancel]; ring
        · have heq : d + 1 = K := by omega
          rw [heq, Finset.Ioc_self, Finset.sum_empty, sub_self]
    have hle := (Finset.sum_le_sum h1).trans (le_of_eq (htele M hKM.le))
    have hK0 : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK
    have hM0 : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
    have h12 : (1 : ℝ) / (K : ℝ) ≤ 2 / (K : ℝ) := by
      exact div_le_div_of_nonneg_right (by norm_num) hK0.le
    linarith

/-- Even-exponent & `m₀`-dividing prime-power sum bound (`MSqDiagA`):
`RR (cN x) m₀ ⌊x^400⌋ ≤ C3 * (√x + y * log x)`. -/
theorem RR_cN_le :
    ∃ C3 x3 : ℝ, 0 < C3 ∧ 3 ≤ x3 ∧ ∀ x : ℝ, x3 ≤ x → ∀ (m₀ : ℕ) (y : ℝ), 1 ≤ y →
      (∀ p : ℕ, p.Prime → p ∣ m₀ → p ≤ ⌊x ^ 400⌋₊ → (p : ℝ) ≤ y) →
      RR (cN x) m₀ ⌊x ^ 400⌋₊ ≤ C3 * (Real.sqrt x + y * Real.log x) := by
  refine ⟨42, 3, by norm_num, le_rfl, fun x hx3 m₀ y hy1 hpm => ?_⟩
  have hx0 : 0 < x := by linarith
  have hLx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  set N := ⌊x ^ 400⌋₊
  -- Split `RR` into (A) even-exponent prime powers (which are squares `m²`) and (B) `n.minFac ∣ m₀`
  have hsplit : RR (cN x) m₀ N ≤
      (∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ _root_.Even (n.factorization n.minFac)), cN x n) +
      (∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac ∣ m₀), cN x n) := by
    unfold RR
    have hsub : (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ (_root_.Even (n.factorization n.minFac) ∨ n.minFac ∣ m₀)) ⊆
        (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ _root_.Even (n.factorization n.minFac)) ∪
        (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac ∣ m₀) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_union] at hn ⊢
      rcases hn.2.2 with h | h
      · exact Or.inl ⟨hn.1, hn.2.1, h⟩
      · exact Or.inr ⟨hn.1, hn.2.1, h⟩
    have hle_u : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ _root_.Even (n.factorization n.minFac)) ∪
        (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac ∣ m₀), cN x n ≤
        (∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ _root_.Even (n.factorization n.minFac)), cN x n) +
        (∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac ∣ m₀), cN x n) := by
      have hu := Finset.sum_union_inter
        (s₁ := (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ _root_.Even (n.factorization n.minFac)))
        (s₂ := (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac ∣ m₀))
        (f := fun n => cN x n)
      have hi : 0 ≤ ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ _root_.Even (n.factorization n.minFac)) ∩
          (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac ∣ m₀), cN x n :=
        Finset.sum_nonneg fun n _ => cN_nonneg x hx0.le n
      linarith
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => cN_nonneg x hx0.le n)).trans hle_u
  -- Part A: even prime powers `n = m²` with `m ≤ N`, `Λ(m²) = Λ(m)`
  have hpartA : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ _root_.Even (n.factorization n.minFac)), cN x n ≤
      42 * Real.sqrt x := by
    have hsubA : (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ _root_.Even (n.factorization n.minFac)) ⊆
        (Finset.Icc 1 N).image (fun m => m ^ 2) := by
      intro n hn
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨p, k, hp, hk, rfl, _, hfac⟩ := primePow_data hn.2.1
      rw [hfac] at hn
      obtain ⟨r, hr⟩ := hn.2.2
      have hpow : p ^ k = (p ^ r) ^ 2 := by rw [← pow_mul, hr, mul_two]
      rw [Finset.mem_image]
      refine ⟨p ^ r, Finset.mem_Icc.mpr ⟨Nat.one_le_pow _ _ hp.pos, ?_⟩, hpow.symm⟩
      have hle : p ^ r ≤ (p ^ r) ^ 2 := Nat.le_self_pow two_ne_zero _
      exact hle.trans (hpow ▸ hn.1.2)
    have hinjA : Set.InjOn (fun m : ℕ => m ^ 2) (Finset.Icc 1 N) := fun a _ b _ hab =>
      (Nat.pow_left_injective two_ne_zero) hab
    have hsumA : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ _root_.Even (n.factorization n.minFac)), cN x n ≤
        ∑ m ∈ Finset.Icc 1 N, cN x (m ^ 2) := by
      calc _ ≤ ∑ n ∈ (Finset.Icc 1 N).image (fun m => m ^ 2), cN x n :=
            Finset.sum_le_sum_of_subset_of_nonneg hsubA (fun n _ _ => cN_nonneg x hx0.le n)
        _ = ∑ m ∈ Finset.Icc 1 N, cN x (m ^ 2) := Finset.sum_image hinjA
    set K := ⌊Real.sqrt x⌋₊
    have hK1 : 1 ≤ K := Nat.le_floor (by
      rw [Nat.cast_one, Real.le_sqrt (by norm_num) hx0.le]; linarith)
    have hKR : (K : ℝ) ≤ Real.sqrt x := Nat.floor_le (Real.sqrt_nonneg x)
    have hK_half : Real.sqrt x / 2 ≤ (K : ℝ) := by
      have hlt : Real.sqrt x < (K : ℝ) + 1 := Nat.lt_floor_add_one (Real.sqrt x)
      have h1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
      linarith
    have hdec : ∀ m : ℕ, cN x (m ^ 2) = Λ m * min 1 (x / ((m : ℝ) ^ 2)) := by
      intro m
      unfold cN ZeroDensityWindow.cN
      rw [ArithmeticFunction.vonMangoldt_apply_pow two_ne_zero]
      push_cast; rfl
    have hA1 : ∑ m ∈ (Finset.Icc 1 N).filter (· ≤ K), cN x (m ^ 2) ≤ 6 * Real.sqrt x := by
      have hsubK : (Finset.Icc 1 N).filter (· ≤ K) ⊆ Finset.Icc 1 K := fun m hm => by
        rw [Finset.mem_filter, Finset.mem_Icc] at hm; exact Finset.mem_Icc.mpr ⟨hm.1.1, hm.2⟩
      calc ∑ m ∈ (Finset.Icc 1 N).filter (· ≤ K), cN x (m ^ 2)
          ≤ ∑ m ∈ (Finset.Icc 1 N).filter (· ≤ K), Λ m := by
            refine Finset.sum_le_sum fun m _ => ?_
            rw [hdec]; exact mul_le_of_le_one_right ArithmeticFunction.vonMangoldt_nonneg (min_le_left _ _)
        _ ≤ ∑ m ∈ Finset.Icc 1 K, Λ m :=
            Finset.sum_le_sum_of_subset_of_nonneg hsubK (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
        _ ≤ 6 * (K : ℝ) := sum_vM_Icc_le K
        _ ≤ 6 * Real.sqrt x := by linarith
    have hA2 : ∑ m ∈ (Finset.Icc 1 N).filter (fun m => ¬ m ≤ K), cN x (m ^ 2) ≤ 36 * Real.sqrt x := by
      have hsub_tail : (Finset.Icc 1 N).filter (fun m => ¬ m ≤ K) ⊆ Finset.Ioc K N := fun m hm => by
        rw [Finset.mem_filter, Finset.mem_Icc] at hm; exact Finset.mem_Ioc.mpr ⟨by omega, hm.1.2⟩
      -- Use Abel summation `vM_major_abel` on `g(m) = if m ≤ K then 1/K² else 1/m²`? Even simpler:
      -- `∑_{m ∈ Ioc K N} Λ(m) / m² ≤ 6 * (1/K + ∑_{m ∈ Ioc K N} 1/m²)` via `vM_major_abel`!
      set g : ℕ → ℝ := fun m => if m ≤ K then 1 / ((K : ℝ) ^ 2) else 1 / ((m : ℝ) ^ 2)
      have hg0 : ∀ m, 0 ≤ g m := fun m => by dsimp only [g]; split_ifs <;> positivity
      have hg_dec : ∀ m, 1 ≤ m → g (m + 1) ≤ g m := by
        intro m hm
        dsimp only [g]
        split_ifs with h1 h2 h2
        · exact le_rfl
        · omega
        · have hKm : (K : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_le.mpr (by omega)
          exact one_div_le_one_div_of_le (sq_pos_of_pos (Nat.cast_pos.mpr hK1)) (by nlinarith)
        · have hmm : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_le.mpr (by omega)
          exact one_div_le_one_div_of_le (sq_pos_of_pos (Nat.cast_pos.mpr hm)) (by nlinarith)
      have htail_vM : ∑ m ∈ Finset.Ioc K N, Λ m / ((m : ℝ) ^ 2) ≤ 18 / (K : ℝ) := by
        have hle_all : ∑ m ∈ Finset.Ioc K N, Λ m / ((m : ℝ) ^ 2) ≤ ∑ m ∈ Finset.Icc 1 N, Λ m * g m := by
          have hsub_in : Finset.Ioc K N ⊆ Finset.Icc 1 N := fun m hm => by
            rw [Finset.mem_Ioc] at hm; exact Finset.mem_Icc.mpr ⟨by omega, hm.2⟩
          calc ∑ m ∈ Finset.Ioc K N, Λ m / ((m : ℝ) ^ 2)
              = ∑ m ∈ Finset.Ioc K N, Λ m * g m := by
                refine Finset.sum_congr rfl fun m hm => ?_
                have hgt : ¬ m ≤ K := by have := (Finset.mem_Ioc.mp hm).1; omega
                dsimp only [g]; rw [if_neg hgt]; ring
            _ ≤ ∑ m ∈ Finset.Icc 1 N, Λ m * g m :=
                Finset.sum_le_sum_of_subset_of_nonneg hsub_in
                  (fun m _ _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (hg0 m))
        have hab := vM_major_abel g hg0 hg_dec N
        have hsumg : ∑ m ∈ Finset.Icc 1 N, g m ≤ 3 / (K : ℝ) := by
          rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) (· ≤ K)]
          have hg1 : ∑ m ∈ (Finset.Icc 1 N).filter (· ≤ K), g m ≤ 1 / (K : ℝ) := by
            have hsubK : (Finset.Icc 1 N).filter (· ≤ K) ⊆ Finset.Icc 1 K := fun m hm => by
              rw [Finset.mem_filter, Finset.mem_Icc] at hm; exact Finset.mem_Icc.mpr ⟨hm.1.1, hm.2⟩
            have hcard : (((Finset.Icc 1 N).filter (· ≤ K)).card : ℝ) ≤ (K : ℝ) := by
              exact_mod_cast (Finset.card_le_card hsubK).trans (by simp)
            have heq : ∑ m ∈ (Finset.Icc 1 N).filter (· ≤ K), g m =
                (((Finset.Icc 1 N).filter (· ≤ K)).card : ℝ) * (1 / (K : ℝ) ^ 2) := by
              rw [← nsmul_eq_mul, ← Finset.sum_const]
              exact Finset.sum_congr rfl fun m hm => by dsimp only [g]; rw [if_pos (Finset.mem_filter.mp hm).2]
            rw [heq]
            have hKpos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK1
            calc (((Finset.Icc 1 N).filter (· ≤ K)).card : ℝ) * (1 / (K : ℝ) ^ 2)
                ≤ (K : ℝ) * (1 / (K : ℝ) ^ 2) := mul_le_mul_of_nonneg_right hcard (by positivity)
              _ = 1 / (K : ℝ) := by field_simp [hKpos.ne']
          have hg2 : ∑ m ∈ (Finset.Icc 1 N).filter (fun m => ¬ m ≤ K), g m ≤ 2 / (K : ℝ) := by
            calc ∑ m ∈ (Finset.Icc 1 N).filter (fun m => ¬ m ≤ K), g m
                = ∑ m ∈ (Finset.Icc 1 N).filter (fun m => ¬ m ≤ K), (1 : ℝ) / ((m : ℝ) ^ 2) :=
                  Finset.sum_congr rfl fun m hm => by dsimp only [g]; rw [if_neg (Finset.mem_filter.mp hm).2]
              _ ≤ ∑ m ∈ Finset.Ioc K N, (1 : ℝ) / ((m : ℝ) ^ 2) :=
                  Finset.sum_le_sum_of_subset_of_nonneg hsub_tail (fun _ _ _ => by positivity)
              _ ≤ 2 / (K : ℝ) := sum_inv_sq_tail_le K N hK1
          have h12 : (1 : ℝ) / (K : ℝ) + 2 / (K : ℝ) = 3 / (K : ℝ) := by ring
          linarith
        have h63 : 6 * (3 / (K : ℝ)) = 18 / (K : ℝ) := by ring
        linarith
      calc ∑ m ∈ (Finset.Icc 1 N).filter (fun m => ¬ m ≤ K), cN x (m ^ 2)
          ≤ ∑ m ∈ Finset.Ioc K N, cN x (m ^ 2) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub_tail (fun m _ _ => cN_nonneg x hx0.le _)
        _ ≤ ∑ m ∈ Finset.Ioc K N, x * (Λ m / ((m : ℝ) ^ 2)) := by
            refine Finset.sum_le_sum fun m _ => ?_
            rw [hdec]
            calc Λ m * min 1 (x / ((m : ℝ) ^ 2)) ≤ Λ m * (x / ((m : ℝ) ^ 2)) :=
                  mul_le_mul_of_nonneg_left (min_le_right _ _) ArithmeticFunction.vonMangoldt_nonneg
              _ = x * (Λ m / ((m : ℝ) ^ 2)) := by ring
        _ = x * ∑ m ∈ Finset.Ioc K N, Λ m / ((m : ℝ) ^ 2) := by rw [← Finset.mul_sum]
        _ ≤ x * (18 / (K : ℝ)) := mul_le_mul_of_nonneg_left htail_vM hx0.le
        _ ≤ 36 * Real.sqrt x := by
            have hKpos : (0 : ℝ) < (K : ℝ) := Nat.cast_pos.mpr hK1
            have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
            rw [mul_div_assoc', div_le_iff₀ hKpos]
            nlinarith [Real.sqrt_nonneg x]
    have hsplit_sum : ∑ m ∈ Finset.Icc 1 N, cN x (m ^ 2) =
        (∑ m ∈ (Finset.Icc 1 N).filter (· ≤ K), cN x (m ^ 2)) +
        (∑ m ∈ (Finset.Icc 1 N).filter (fun m => ¬ m ≤ K), cN x (m ^ 2)) :=
      (Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) (· ≤ K) (fun m => cN x (m ^ 2))).symm
    linarith
  -- Part B: `n.minFac ∣ m₀` — group by `p = n.minFac ∈ Icc 1 ⌊y⌋₊`
  have hpartB : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac ∣ m₀), cN x n ≤
      4 * y * Real.log x := by
    have hfib : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac ∣ m₀), cN x n ≤
        ∑ p ∈ Finset.Icc 1 ⌊y⌋₊, sP (cN x) N p := by
      have hgroup :
          ∑ p ∈ Finset.Icc 1 ⌊y⌋₊,
              ∑ n ∈ ((Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac ∣ m₀)).filter (fun n => n.minFac = p),
                cN x n =
            ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac ∣ m₀), cN x n := by
        refine Finset.sum_fiberwise_of_maps_to (fun n hn => ?_) _
        rw [Finset.mem_filter, Finset.mem_Icc] at hn
        have hp := Nat.minFac_prime hn.2.1.ne_one
        have hpleN : n.minFac ≤ N := (Nat.minFac_le hn.1.1).trans hn.1.2
        have hpley : (n.minFac : ℝ) ≤ y := hpm n.minFac hp hn.2.2 hpleN
        exact Finset.mem_Icc.mpr ⟨hp.pos, Nat.le_floor hpley⟩
      rw [← hgroup]
      refine Finset.sum_le_sum fun p _ => ?_
      unfold sP
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) (fun n _ _ => cN_nonneg x hx0.le n)
      simp only [Finset.mem_filter] at hn ⊢
      exact ⟨hn.1.1, hn.1.2.1, hn.2⟩
    calc ∑ n ∈ (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac ∣ m₀), cN x n
        ≤ ∑ p ∈ Finset.Icc 1 ⌊y⌋₊, sP (cN x) N p := hfib
      _ ≤ ∑ _p ∈ Finset.Icc 1 ⌊y⌋₊, (4 * Real.log x) :=
          Finset.sum_le_sum fun p _ => sP_cN_le_four_log hx3 N p
      _ = (⌊y⌋₊ : ℝ) * (4 * Real.log x) := by rw [Finset.sum_const, nsmul_eq_mul]; simp
      _ ≤ y * (4 * Real.log x) := mul_le_mul_of_nonneg_right (Nat.floor_le (by linarith)) (by positivity)
      _ = 4 * y * Real.log x := by ring
  linarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 38) (mul_nonneg (by linarith : 0 ≤ y) hLx)]

private lemma sum_log_sq_div_sq_primes_dyadic_le (y : ℕ) (hy : 1 ≤ y) :
    ∑ p ∈ (Finset.Ioc y (2 * y)).filter Nat.Prime, Real.log (p : ℝ) ^ 2 / (p : ℝ) ^ 2 ≤
      12 * Real.log (2 * (y : ℝ)) / (y : ℝ) := by
  have hyR : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hy0 : (0 : ℝ) < (y : ℝ) := by linarith
  have hL0 : 0 ≤ Real.log (2 * (y : ℝ)) := Real.log_nonneg (by linarith)
  have hterm : ∀ p ∈ (Finset.Ioc y (2 * y)).filter Nat.Prime,
      Real.log (p : ℝ) ^ 2 / (p : ℝ) ^ 2 ≤ Real.log (2 * (y : ℝ)) / (y : ℝ) ^ 2 * Λ p := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨h1, h2⟩, hpr⟩ := hp
    have hp1 : (y : ℝ) < (p : ℝ) := by exact_mod_cast h1
    have hp2 : (p : ℝ) ≤ 2 * (y : ℝ) := by exact_mod_cast h2
    have hlp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpr.one_lt.le)
    have hlle : Real.log (p : ℝ) ≤ Real.log (2 * (y : ℝ)) := Real.log_le_log (by linarith) hp2
    rw [ArithmeticFunction.vonMangoldt_apply_prime hpr]
    calc Real.log (p : ℝ) ^ 2 / (p : ℝ) ^ 2 = Real.log (p : ℝ) * Real.log (p : ℝ) / (p : ℝ) ^ 2 := by ring
      _ ≤ Real.log (2 * (y : ℝ)) * Real.log (p : ℝ) / (p : ℝ) ^ 2 := by gcongr
      _ ≤ Real.log (2 * (y : ℝ)) * Real.log (p : ℝ) / (y : ℝ) ^ 2 := by gcongr
      _ = Real.log (2 * (y : ℝ)) / (y : ℝ) ^ 2 * Real.log (p : ℝ) := by ring
  have hsum : ∑ p ∈ (Finset.Ioc y (2 * y)).filter Nat.Prime, Λ p ≤ 12 * (y : ℝ) := by
    have hsub : (Finset.Ioc y (2 * y)).filter Nat.Prime ⊆ Finset.Icc 1 (2 * y) := fun p hp => by
      rw [Finset.mem_filter, Finset.mem_Ioc] at hp; exact Finset.mem_Icc.mpr ⟨by omega, hp.1.2⟩
    have hle := (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)).trans (sum_vM_Icc_le (2 * y))
    push_cast at hle; linarith
  calc ∑ p ∈ (Finset.Ioc y (2 * y)).filter Nat.Prime, Real.log (p : ℝ) ^ 2 / (p : ℝ) ^ 2
      ≤ ∑ p ∈ (Finset.Ioc y (2 * y)).filter Nat.Prime, Real.log (2 * (y : ℝ)) / (y : ℝ) ^ 2 * Λ p :=
        Finset.sum_le_sum hterm
    _ = Real.log (2 * (y : ℝ)) / (y : ℝ) ^ 2 * ∑ p ∈ (Finset.Ioc y (2 * y)).filter Nat.Prime, Λ p := by
        rw [Finset.mul_sum]
    _ ≤ Real.log (2 * (y : ℝ)) / (y : ℝ) ^ 2 * (12 * (y : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum (div_nonneg hL0 (sq_nonneg _))
    _ = 12 * Real.log (2 * (y : ℝ)) / (y : ℝ) := by field_simp [hy0.ne']

private lemma sum_log_sq_div_sq_primes_tail_le (N : ℕ) : ∀ d y : ℕ, 1 ≤ y → N - y ≤ d →
    ∑ p ∈ (Finset.Ioc y N).filter Nat.Prime, Real.log (p : ℝ) ^ 2 / (p : ℝ) ^ 2 ≤
      24 * (Real.log (y : ℝ) + 2 * Real.log 2) / (y : ℝ) := by
  intro d
  induction d with
  | zero =>
    intro y hy hd
    rw [Finset.Ioc_eq_empty_of_le (by omega), Finset.filter_empty, Finset.sum_empty]
    have hly : 0 ≤ Real.log (y : ℝ) := Real.log_nonneg (by exact_mod_cast hy)
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    exact div_nonneg (by linarith) (Nat.cast_nonneg y)
  | succ d ih =>
    intro y hy hd
    have hy0 : (0 : ℝ) < (y : ℝ) := Nat.cast_pos.mpr hy
    have hly : 0 ≤ Real.log (y : ℝ) := Real.log_nonneg (by exact_mod_cast hy)
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlog2y : Real.log (2 * (y : ℝ)) = Real.log 2 + Real.log (y : ℝ) :=
      Real.log_mul (by norm_num) hy0.ne'
    have hblock := sum_log_sq_div_sq_primes_dyadic_le y hy
    by_cases hN : N ≤ 2 * y
    · have hsub : (Finset.Ioc y N).filter Nat.Prime ⊆ (Finset.Ioc y (2 * y)).filter Nat.Prime :=
        Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_right hN)
      calc ∑ p ∈ (Finset.Ioc y N).filter Nat.Prime, Real.log (p : ℝ) ^ 2 / (p : ℝ) ^ 2
          ≤ ∑ p ∈ (Finset.Ioc y (2 * y)).filter Nat.Prime, Real.log (p : ℝ) ^ 2 / (p : ℝ) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
        _ ≤ 12 * Real.log (2 * (y : ℝ)) / (y : ℝ) := hblock
        _ ≤ 24 * (Real.log (y : ℝ) + 2 * Real.log 2) / (y : ℝ) := by
            apply div_le_div_of_nonneg_right _ hy0.le
            rw [hlog2y]; linarith
    · push Not at hN
      have hsplit : (Finset.Ioc y N).filter Nat.Prime =
          (Finset.Ioc y (2 * y)).filter Nat.Prime ∪ (Finset.Ioc (2 * y) N).filter Nat.Prime := by
        rw [← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc (by omega) hN.le]
      have hdisj : Disjoint ((Finset.Ioc y (2 * y)).filter Nat.Prime) ((Finset.Ioc (2 * y) N).filter Nat.Prime) := by
        apply Finset.disjoint_filter_filter
        rw [Finset.disjoint_left]
        intro a ha hb; rw [Finset.mem_Ioc] at ha hb; omega
      have ht := ih (2 * y) (by omega) (by omega)
      rw [hsplit, Finset.sum_union hdisj]
      calc ∑ p ∈ (Finset.Ioc y (2 * y)).filter Nat.Prime, Real.log (p : ℝ) ^ 2 / (p : ℝ) ^ 2 +
            ∑ p ∈ (Finset.Ioc (2 * y) N).filter Nat.Prime, Real.log (p : ℝ) ^ 2 / (p : ℝ) ^ 2
          ≤ 12 * Real.log (2 * (y : ℝ)) / (y : ℝ) +
            24 * (Real.log ((2 * y : ℕ) : ℝ) + 2 * Real.log 2) / ((2 * y : ℕ) : ℝ) :=
            add_le_add hblock ht
        _ = 24 * (Real.log (y : ℝ) + 2 * Real.log 2) / (y : ℝ) := by
            push_cast; rw [hlog2y]; field_simp [hy0.ne']; ring

/-- Diagonal prime-power square sum bound (`MSqDiagB`):
`∑_{p ≤ ⌊x^400⌋, p prime} sP (cN x) ⌊x^400⌋ p ^ 2 ≤ C4 * x * Real.log x`. -/
theorem sum_sP_sq_le :
    ∃ C4 x4 : ℝ, 0 < C4 ∧ 3 ≤ x4 ∧ ∀ x : ℝ, x4 ≤ x →
      ∑ p ∈ (Finset.Icc 1 ⌊x ^ 400⌋₊).filter Nat.Prime, sP (cN x) ⌊x ^ 400⌋₊ p ^ 2 ≤
        C4 * x * Real.log x := by
  refine ⟨1000, 3, by norm_num, le_rfl, fun x hx3 => ?_⟩
  have hx0 : 0 < x := by linarith
  have hL1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hx0]; linarith [Real.exp_one_lt_d9]
  set N := ⌊x ^ 400⌋₊
  set M := ⌊x⌋₊
  have hM1 : 1 ≤ M := Nat.le_floor (by rw [Nat.cast_one]; linarith)
  have hMR : (M : ℝ) ≤ x := Nat.floor_le hx0.le
  have hM_half : x / 2 ≤ (M : ℝ) := by
    have h1 : x < (M : ℝ) + 1 := Nat.lt_floor_add_one x
    have h2 : (3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (Nat.le_floor hx3 : 3 ≤ M)
    linarith
  rw [← Finset.sum_filter_add_sum_filter_not ((Finset.Icc 1 N).filter Nat.Prime) (· ≤ M)]
  -- Small primes `p ≤ M`: `sP ≤ 4 * log x` and `sP ≤ 2 * x * log p / p`; even simpler:
  -- For `p ≤ M`, `sP(p)² ≤ (4 * log x) * sP(p)`! Wait: `∑_{p ≤ M} sP(p) ≤ ∑_{n ≤ N} cN x n`? No,
  -- that would give `x (log x)^2`. Instead bound `sP(p) ≤ 2 * log p + (if p ≤ √x then 4 * log x else 0)`!
  -- Actually for `p > √x` and `p ≤ x`, the ONLY power `p^k ≤ x` is `k = 1` (contributing `log p`),
  -- and higher powers `k ≥ 2` have `p^k ≥ p² > x`, so `∑_{k ≥ 2} x * log p / p^k ≤ 2 * x * log p / p² ≤ 2 * log p`!
  -- Thus for `√x < p ≤ x`, `sP(p) ≤ 3 * log p`, hence `sP(p)² ≤ 9 * (log x) * log p`!
  -- And for `p ≤ √x`, `sP(p)² ≤ 16 * (log x)²`, and there are `≤ √x` such primes, contributing `≤ 16 * √x * (log x)² ≤ 16 * x * log x`!
  have hsmall : ∑ p ∈ ((Finset.Icc 1 N).filter Nat.Prime).filter (· ≤ M), sP (cN x) N p ^ 2 ≤
      100 * x * Real.log x := by
    set S := ⌊Real.sqrt x⌋₊
    rw [← Finset.sum_filter_add_sum_filter_not (((Finset.Icc 1 N).filter Nat.Prime).filter (· ≤ M)) (· ≤ S)]
    have htiny : ∑ p ∈ (((Finset.Icc 1 N).filter Nat.Prime).filter (· ≤ M)).filter (· ≤ S),
        sP (cN x) N p ^ 2 ≤ 32 * x * Real.log x := by
      have hsub : (((Finset.Icc 1 N).filter Nat.Prime).filter (· ≤ M)).filter (· ≤ S) ⊆ Finset.Icc 1 S :=
        fun p hp => by
          simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
          exact ⟨hp.1.1.1.1, hp.2⟩
      have hcard : ((((Finset.Icc 1 N).filter Nat.Prime).filter (· ≤ M)).filter (· ≤ S)).card ≤ S :=
        (Finset.card_le_card hsub).trans (by simp)
      have hcardR : (((((Finset.Icc 1 N).filter Nat.Prime).filter (· ≤ M)).filter (· ≤ S)).card : ℝ) ≤ Real.sqrt x :=
        (by exact_mod_cast hcard : _ ≤ (S : ℝ)).trans (Nat.floor_le (Real.sqrt_nonneg x))
      have hlog_le_sqrt : Real.log x ≤ 2 * Real.sqrt x := by
        have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx0)
        rw [Real.log_sqrt hx0.le] at h; linarith
      calc ∑ p ∈ (((Finset.Icc 1 N).filter Nat.Prime).filter (· ≤ M)).filter (· ≤ S), sP (cN x) N p ^ 2
          ≤ ∑ _p ∈ (((Finset.Icc 1 N).filter Nat.Prime).filter (· ≤ M)).filter (· ≤ S), (4 * Real.log x) ^ 2 :=
            Finset.sum_le_sum fun p _ => pow_le_pow_left₀ (sP_nonneg _ (cN_nonneg x hx0.le) _ _)
              (sP_cN_le_four_log hx3 N p) 2
        _ = (((((Finset.Icc 1 N).filter Nat.Prime).filter (· ≤ M)).filter (· ≤ S)).card : ℝ) * (16 * Real.log x ^ 2) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ Real.sqrt x * (16 * Real.log x ^ 2) := mul_le_mul_of_nonneg_right hcardR (by positivity)
        _ = 16 * (Real.sqrt x * Real.log x) * Real.log x := by ring
        _ ≤ 16 * (Real.sqrt x * (2 * Real.sqrt x)) * Real.log x := by
            have h1 : Real.sqrt x * Real.log x ≤ Real.sqrt x * (2 * Real.sqrt x) :=
              mul_le_mul_of_nonneg_left hlog_le_sqrt (Real.sqrt_nonneg x)
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by norm_num)) (by linarith)
        _ = 32 * x * Real.log x := by
            have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
            calc 16 * (Real.sqrt x * (2 * Real.sqrt x)) * Real.log x
                = 32 * (Real.sqrt x * Real.sqrt x) * Real.log x := by ring
              _ = 32 * x * Real.log x := by rw [hsq]
    have hmid : ∑ p ∈ (((Finset.Icc 1 N).filter Nat.Prime).filter (· ≤ M)).filter (fun p => ¬ p ≤ S),
        sP (cN x) N p ^ 2 ≤ 68 * x * Real.log x := by
      have hpt : ∀ p ∈ (((Finset.Icc 1 N).filter Nat.Prime).filter (· ≤ M)).filter (fun p => ¬ p ≤ S),
          sP (cN x) N p ^ 2 ≤ 9 * Real.log x * Λ p := by
        intro p hp_mem
        simp only [Finset.mem_filter, Finset.mem_Icc] at hp_mem
        obtain ⟨⟨⟨⟨_, _⟩, hpr⟩, hpM⟩, hpS⟩ := hp_mem
        have hp_gt_sqrt : Real.sqrt x < (p : ℝ) := by
          have h1 : S < p := by omega
          exact (Nat.lt_floor_add_one (Real.sqrt x)).trans_le (by exact_mod_cast h1)
        have hpsq_gt : x < (p : ℝ) ^ 2 := by
          have := mul_lt_mul'' hp_gt_sqrt hp_gt_sqrt (Real.sqrt_nonneg x) (Real.sqrt_nonneg x)
          rw [Real.mul_self_sqrt hx0.le, ← sq] at this; exact this
        have hlp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hpr.one_lt.le)
        have hlp_le : Real.log (p : ℝ) ≤ Real.log x :=
          Real.log_le_log (Nat.cast_pos.mpr hpr.pos) ((by exact_mod_cast hpM : (p : ℝ) ≤ (M : ℝ)).trans hMR)
        -- Bound `sP (cN x) N p ≤ 3 * Real.log p`
        have hsP_le : sP (cN x) N p ≤ 3 * Real.log (p : ℝ) := by
          have hsub : (Finset.Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p) ⊆
              (Finset.Icc 1 N).image (fun k => p ^ k) := by
            intro n hn
            rw [Finset.mem_filter, Finset.mem_Icc] at hn
            obtain ⟨p', k, _, hk, rfl, hm, -⟩ := primePow_data hn.2.1
            have hpq : p' = p := hm.symm.trans hn.2.2; subst hpq
            exact Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨by omega, (le_of_lt (Nat.lt_pow_self hpr.one_lt)).trans hn.1.2⟩, rfl⟩
          have hinj : Set.InjOn (fun k : ℕ => p ^ k) (Finset.Icc 1 N) := fun a _ b _ hab =>
            Nat.pow_right_injective hpr.two_le hab
          have hstep1 : sP (cN x) N p ≤ ∑ k ∈ Finset.Icc 1 N, cN x (p ^ k) := by
            calc _ ≤ ∑ n ∈ (Finset.Icc 1 N).image (fun k => p ^ k), cN x n :=
                  Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => cN_nonneg x hx0.le n)
              _ = ∑ k ∈ Finset.Icc 1 N, cN x (p ^ k) := Finset.sum_image hinj
          have hN1 : 1 ≤ N := Nat.le_floor (by rw [Nat.cast_one]; exact one_le_pow₀ (by linarith : (1 : ℝ) ≤ x))
          have hsplit1 : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
            ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
          rw [hsplit1, Finset.sum_insert (by simp)] at hstep1
          have hk1 : cN x (p ^ 1) ≤ Real.log (p : ℝ) := by
            unfold cN ZeroDensityWindow.cN
            rw [pow_one, ArithmeticFunction.vonMangoldt_apply_prime hpr]
            exact mul_le_of_le_one_right hlp (min_le_left _ _)
          have hk2 : ∑ k ∈ Finset.Icc 2 N, cN x (p ^ k) ≤ 2 * Real.log (p : ℝ) := by
            have hterm : ∀ k ∈ Finset.Icc 2 N, cN x (p ^ k) ≤ Real.log (p : ℝ) * (1 / (p : ℝ) ^ (k - 2)) := by
              intro k hk
              have hk2' := (Finset.mem_Icc.mp hk).1
              unfold cN ZeroDensityWindow.cN
              rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega), ArithmeticFunction.vonMangoldt_apply_prime hpr]
              have hpeq : ((p ^ k : ℕ) : ℝ) = (p : ℝ) ^ 2 * (p : ℝ) ^ (k - 2) := by
                push_cast; rw [← pow_add]; congr 1; omega
              have hp0 : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hpr.pos
              have hdiv : x / ((p ^ k : ℕ) : ℝ) ≤ 1 / (p : ℝ) ^ (k - 2) := by
                rw [hpeq, div_le_div_iff₀ (mul_pos (pow_pos hp0 2) (pow_pos hp0 _)) (pow_pos hp0 _)]
                nlinarith [pow_pos hp0 (k - 2)]
              exact mul_le_mul_of_nonneg_left ((min_le_right _ _).trans hdiv) hlp
            calc ∑ k ∈ Finset.Icc 2 N, cN x (p ^ k)
                ≤ ∑ k ∈ Finset.Icc 2 N, Real.log (p : ℝ) * (1 / (p : ℝ) ^ (k - 2)) := Finset.sum_le_sum hterm
              _ = Real.log (p : ℝ) * ∑ k ∈ Finset.Icc 2 N, (1 / (p : ℝ)) ^ (k - 2) := by
                  rw [Finset.mul_sum]; congr 1; ext k; rw [one_div_pow]
              _ ≤ Real.log (p : ℝ) * ∑ j ∈ Finset.range (N + 1), (1 / (p : ℝ)) ^ j := by
                  refine mul_le_mul_of_nonneg_left ?_ hlp
                  have hinj2 : Set.InjOn (fun k => k - 2) (Finset.Icc 2 N) := by
                    intro a ha b hb hab; dsimp only at hab
                    have ha' := (Finset.mem_Icc.mp ha).1; have hb' := (Finset.mem_Icc.mp hb).1; omega
                  rw [← Finset.sum_image (f := fun j => (1 / (p : ℝ)) ^ j) hinj2]
                  refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) (fun _ _ _ => by positivity)
                  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
                  exact Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hk).2; omega)
              _ ≤ Real.log (p : ℝ) * 2 := by
                  refine mul_le_mul_of_nonneg_left ?_ hlp
                  set r : ℝ := 1 / (p : ℝ)
                  have hr_half : r ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hpr.two_le)
                  rw [geom_sum_eq (by linarith : r ≠ 1)]
                  have h1 : (r ^ (N + 1) - 1) / (r - 1) = (1 - r ^ (N + 1)) / (1 - r) := by
                    rw [← neg_div_neg_eq]; ring_nf
                  rw [h1, div_le_iff₀ (by linarith : 0 < 1 - r)]
                  linarith [pow_nonneg (by positivity : 0 ≤ r) (N + 1)]
              _ = 2 * Real.log (p : ℝ) := by ring
          linarith
        rw [ArithmeticFunction.vonMangoldt_apply_prime hpr]
        calc sP (cN x) N p ^ 2 ≤ (3 * Real.log (p : ℝ)) ^ 2 :=
              pow_le_pow_left₀ (sP_nonneg _ (cN_nonneg x hx0.le) _ _) hsP_le 2
          _ = 9 * Real.log (p : ℝ) * Real.log (p : ℝ) := by ring
          _ ≤ 9 * Real.log x * Real.log (p : ℝ) := by gcongr
      have hsubM : (((Finset.Icc 1 N).filter Nat.Prime).filter (· ≤ M)).filter (fun p => ¬ p ≤ S) ⊆
          Finset.Icc 1 M := fun p hp => by
        simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
        exact ⟨hp.1.1.1.1, hp.1.2⟩
      calc ∑ p ∈ (((Finset.Icc 1 N).filter Nat.Prime).filter (· ≤ M)).filter (fun p => ¬ p ≤ S), sP (cN x) N p ^ 2
          ≤ ∑ p ∈ (((Finset.Icc 1 N).filter Nat.Prime).filter (· ≤ M)).filter (fun p => ¬ p ≤ S),
              9 * Real.log x * Λ p := Finset.sum_le_sum hpt
        _ = 9 * Real.log x * ∑ p ∈ (((Finset.Icc 1 N).filter Nat.Prime).filter (· ≤ M)).filter (fun p => ¬ p ≤ S), Λ p := by
            rw [← Finset.mul_sum]
        _ ≤ 9 * Real.log x * ∑ n ∈ Finset.Icc 1 M, Λ n :=
            mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum_of_subset_of_nonneg hsubM (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg))
              (by positivity)
        _ ≤ 9 * Real.log x * (6 * (M : ℝ)) := mul_le_mul_of_nonneg_left (sum_vM_Icc_le M) (by positivity)
        _ ≤ 9 * Real.log x * (6 * x) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = 54 * x * Real.log x := by ring
        _ ≤ 68 * x * Real.log x := by nlinarith
    linarith
  -- Large primes `p > M`: `sP(p)² ≤ 4 * x² * (log p)² / p²`, sum via dyadic tail bound
  have hlarge : ∑ p ∈ ((Finset.Icc 1 N).filter Nat.Prime).filter (fun p => ¬ p ≤ M), sP (cN x) N p ^ 2 ≤
      900 * x * Real.log x := by
    have hsub : ((Finset.Icc 1 N).filter Nat.Prime).filter (fun p => ¬ p ≤ M) ⊆
        (Finset.Ioc M N).filter Nat.Prime := fun p hp => by
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hp ⊢
      exact ⟨⟨by omega, hp.1.1.2⟩, hp.1.2⟩
    have htail := sum_log_sq_div_sq_primes_tail_le N (N - M) M hM1 le_rfl
    have hlogM : Real.log (M : ℝ) ≤ Real.log x := Real.log_le_log (Nat.cast_pos.mpr hM1) hMR
    have hl2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
    have htail2 : 24 * (Real.log (M : ℝ) + 2 * Real.log 2) / (M : ℝ) ≤ 144 * Real.log x / x := by
      have hMpos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM1
      rw [div_le_div_iff₀ hMpos hx0]
      nlinarith
    calc ∑ p ∈ ((Finset.Icc 1 N).filter Nat.Prime).filter (fun p => ¬ p ≤ M), sP (cN x) N p ^ 2
        ≤ ∑ p ∈ (Finset.Ioc M N).filter Nat.Prime, sP (cN x) N p ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
      _ ≤ ∑ p ∈ (Finset.Ioc M N).filter Nat.Prime, (2 * x * Real.log (p : ℝ) / (p : ℝ)) ^ 2 := by
          refine Finset.sum_le_sum fun p hp => ?_
          exact pow_le_pow_left₀ (sP_nonneg _ (cN_nonneg x hx0.le) _ _)
            (sP_cN_le_log_div x hx0.le N p (Finset.mem_filter.mp hp).2) 2
      _ = 4 * x ^ 2 * ∑ p ∈ (Finset.Ioc M N).filter Nat.Prime, Real.log (p : ℝ) ^ 2 / (p : ℝ) ^ 2 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => ?_; ring
      _ ≤ 4 * x ^ 2 * (144 * Real.log x / x) := mul_le_mul_of_nonneg_left (htail.trans htail2) (by positivity)
      _ = 576 * x * Real.log x := by field_simp [hx0.ne']; ring
      _ ≤ 900 * x * Real.log x := by nlinarith
  linarith

/-! ## Section 5: Unconditional Jacobi Cancellation on `PPset` & `meanSquareHypW_of_bv_and_logfree` -/

theorem intervalIntegrable_inv_log {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t => 1 / Real.log t) MeasureTheory.volume a b := by
  have hmem : ∀ t ∈ Set.uIcc a b, 2 ≤ t := by
    intro t ht
    rcases Set.mem_uIcc.mp ht with h | h <;> linarith [h.1]
  apply ContinuousOn.intervalIntegrable
  refine ContinuousOn.div continuousOn_const (Real.continuousOn_log.mono ?_) ?_
  · intro t ht; exact ne_of_gt (by linarith [hmem t ht])
  · intro t ht; exact (Real.log_pos (by linarith [hmem t ht])).ne'

theorem liX_lower {X : ℝ} (hX : 4 ≤ X) : X / (2 * Real.log X) ≤ liX X := by
  have hconst : ∫ _t in (2 : ℝ)..X, (1 / Real.log X) = (X - 2) / Real.log X := by
    rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have hmono : (X - 2) / Real.log X ≤ liX X := by
    rw [← hconst]; unfold liX
    refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
      (intervalIntegrable_inv_log le_rfl (by linarith)) fun t ht => ?_
    exact one_div_le_one_div_of_le (Real.log_pos (by linarith [ht.1]))
      (Real.log_le_log (by linarith [ht.1]) ht.2)
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hhalf : X / (2 * Real.log X) ≤ (X - 2) / Real.log X := by
    rw [div_le_div_iff₀ (by positivity) hlogX]; nlinarith
  exact hhalf.trans hmono

private lemma primeCountAP_eq_Icc_card (M b : ℕ) (X : ℝ) :
    Stage2DirichletAP.primeCountAP M b X =
      ((Finset.Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ p % M = b % M)).card := by
  unfold Stage2DirichletAP.primeCountAP
  have hset :
      (Finset.range (⌊X⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ b [MOD M]) =
        (Finset.Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ p % M = b % M) := by
    ext p
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    simp only [Nat.ModEq]
    constructor
    · rintro ⟨hp_lt, hp_pr, hp_mod⟩
      exact ⟨⟨hp_pr.pos, by omega⟩, hp_pr, hp_mod⟩
    · rintro ⟨⟨_, hp_le⟩, hp_pr, hp_mod⟩
      exact ⟨by omega, hp_pr, hp_mod⟩
  exact congrArg Finset.card hset

theorem abs_card_PPset_sub_primeCountAP_le (M b : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    |((PPset M b X).card : ℝ) - (Stage2DirichletAP.primeCountAP M b X : ℝ)| ≤ X ^ (1 / 2 : ℝ) := by
  rw [primeCountAP_eq_Icc_card]
  have hsub : PPset M b X ⊆ (Finset.Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ p % M = b % M) := by
    intro q hq; simp only [PPset, Finset.mem_filter] at hq ⊢; exact ⟨hq.1, hq.2.1, hq.2.2.1⟩
  have hle : (PPset M b X).card ≤ ((Finset.Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ p % M = b % M)).card :=
    Finset.card_le_card hsub
  have hdiff_sub : ((Finset.Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ p % M = b % M)) \ PPset M b X ⊆
      Finset.Icc 1 ⌊X ^ (1 / 2 : ℝ)⌋₊ := by
    intro q hq
    rw [Finset.mem_sdiff] at hq
    simp only [PPset, Finset.mem_filter, Finset.mem_Icc] at hq ⊢
    refine ⟨hq.1.1.1, Nat.le_floor ?_⟩
    by_contra hgt; push Not at hgt
    exact hq.2 ⟨hq.1.1, hq.1.2.1, hq.1.2.2, hgt⟩
  have hcard_diff : (((Finset.Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ p % M = b % M)) \ PPset M b X).card ≤
      ⌊X ^ (1 / 2 : ℝ)⌋₊ :=
    (Finset.card_le_card hdiff_sub).trans (by simp)
  have hadd : (((Finset.Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ p % M = b % M)) \ PPset M b X).card +
      (PPset M b X).card =
      ((Finset.Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ p % M = b % M)).card :=
    Finset.card_sdiff_add_card_eq_card hsub
  have hfl : (⌊X ^ (1 / 2 : ℝ)⌋₊ : ℝ) ≤ X ^ (1 / 2 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg (by linarith) _)
  have hleR : ((PPset M b X).card : ℝ) ≤ (((Finset.Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ p % M = b % M)).card : ℝ) := by
    exact_mod_cast hle
  have hdiffR : (((Finset.Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ p % M = b % M)).card : ℝ) -
      ((PPset M b X).card : ℝ) ≤ X ^ (1 / 2 : ℝ) := by
    have h1 : (((Finset.Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ p % M = b % M)).card : ℝ) -
        ((PPset M b X).card : ℝ) ≤ (⌊X ^ (1 / 2 : ℝ)⌋₊ : ℝ) := by
      have : ((((Finset.Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ p % M = b % M)) \ PPset M b X).card : ℝ) +
          ((PPset M b X).card : ℝ) =
          (((Finset.Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ p % M = b % M)).card : ℝ) := by
        exact_mod_cast hadd
      have h2 : ((((Finset.Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ p % M = b % M)) \ PPset M b X).card : ℝ) ≤
          (⌊X ^ (1 / 2 : ℝ)⌋₊ : ℝ) := by exact_mod_cast hcard_diff
      linarith
    linarith
  rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  exact hdiffR

/-- Partition of `∑_{q ∈ PPset m₀ a₀ X} (q / s)` into residue classes `b ∈ clsB m₀ s a₀` when `s ≤ √X`. -/
theorem jacobi_sum_PPset_eq_clsB (m₀ s a₀ : ℕ) {X : ℝ} (hm : 0 < m₀) (hs : 0 < s)
    (hsX : (s : ℝ) ≤ X ^ (1 / 2 : ℝ)) :
    ∑ q ∈ PPset m₀ a₀ X, (jacobiSym (q : ℤ) s : ℝ) =
      ∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * ((PPset (m₀ * s) b X).card : ℝ) := by
  have hmaps : ∀ q ∈ PPset m₀ a₀ X, q % (m₀ * s) ∈ clsB m₀ s a₀ := by
    intro q hq
    rw [PPset, Finset.mem_filter] at hq
    rw [clsB, Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.mod_lt q (Nat.mul_pos hm hs), ?_, ?_⟩
    · have h1 : q % (m₀ * s) ≡ q [MOD m₀] := Nat.ModEq.of_mul_right s (Nat.mod_modEq q (m₀ * s))
      exact h1.trans hq.2.2.1
    · have h1 : q % (m₀ * s) ≡ q [MOD s] := Nat.ModEq.of_mul_left m₀ (Nat.mod_modEq q (m₀ * s))
      unfold Nat.Coprime; rw [Nat.ModEq.gcd_eq h1]
      have hsq : s < q := by
        have : (s : ℝ) < (q : ℝ) := hsX.trans_lt hq.2.2.2
        exact_mod_cast this
      exact (Nat.Prime.coprime_iff_not_dvd hq.2.1).mpr fun hd =>
        absurd (Nat.le_of_dvd hs hd) (by omega)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hfib : (PPset m₀ a₀ X).filter (fun q => q % (m₀ * s) = b) = PPset (m₀ * s) b X := by
    ext q
    rw [clsB, Finset.mem_filter, Finset.mem_range] at hb
    simp only [PPset, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hq1, hqp, _, hqX⟩, hqmod⟩
      exact ⟨hq1, hqp, by rw [hqmod, Nat.mod_eq_of_lt hb.1], hqX⟩
    · rintro ⟨hq1, hqp, hqmod, hqX⟩
      have hqeq : q % (m₀ * s) = b := by rwa [Nat.mod_eq_of_lt hb.1] at hqmod
      have hqm : q % m₀ = a₀ % m₀ := by
        have h1 : q ≡ q % (m₀ * s) [MOD m₀] := (Nat.ModEq.of_mul_right s (Nat.mod_modEq q (m₀ * s))).symm
        rw [hqeq] at h1
        exact h1.trans hb.2.1
      exact ⟨⟨hq1, hqp, hqm, hqX⟩, hqeq⟩
  rw [hfib]
  have hconst : ∀ q ∈ PPset (m₀ * s) b X, (jacobiSym (q : ℤ) s : ℝ) = (jacobiSym (b : ℤ) s : ℝ) := by
    intro q hq
    rw [PPset, Finset.mem_filter] at hq
    have hmod : q ≡ b [MOD s] := Nat.ModEq.of_mul_left m₀ hq.2.2.1
    rw [jacobi_congr hmod]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, mul_comm]

private lemma tendsto_rpow_mul_exp_neg_rpow {K B α : ℝ} (hK : 0 < K) (hα : 0 < α) :
    Tendsto (fun x : ℝ => x ^ B * Real.exp (-K * x ^ α)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun u : ℝ => u ^ (B / α) * Real.exp (-K * u)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun v : ℝ => v ^ (B / α) * Real.exp (-v)) atTop (𝓝 0) := by
      simpa [Real.exp_neg, div_eq_mul_inv] using
        (isLittleO_rpow_exp_atTop (B / α)).tendsto_div_nhds_zero
    have hcomp := h2.comp (tendsto_id.const_mul_atTop hK)
    have hscale : Tendsto (fun u : ℝ => K ^ (-(B / α)) * ((K * u) ^ (B / α) * Real.exp (-(K * u)))) atTop (𝓝 0) := by
      simpa using hcomp.const_mul (K ^ (-(B / α)))
    refine hscale.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    rw [Real.mul_rpow hK.le hu.le, ← mul_assoc, ← mul_assoc, ← Real.rpow_add hK, neg_add_cancel,
      Real.rpow_zero, one_mul, neg_mul]
  have hcomp2 := h1.comp (tendsto_rpow_atTop hα)
  refine hcomp2.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  dsimp only [Function.comp_apply]
  rw [← Real.rpow_mul hx.le, mul_div_cancel₀ _ hα.ne']

/-- **Unconditional Prime-Count Lower Bound & Jacobi Cancellation on `PPset m₀ a₀ X`**
(directly from `Stage10SiegelWalfiszFull.siegel_walfisz_pi`, with ZERO exceptional modulus!):
for every `ε ∈ (0, 1]`, there exists `x₀ ≥ 3` such that for all `x ≥ x₀`, `8 ∣ m₀`, `a₀.Coprime m₀`,
`m₀ ≤ (log X)^(1/ε)`, `x^(ε/6) ≤ log X ≤ x^(ε/5) * (log x)^2`:
1. `X ^ (9 / 10 : ℝ) ≤ ((PPset m₀ a₀ X).card : ℝ)` and `X / (4 * (log X)^(1 + 1/ε)) ≤ |PPset|`;
2. for EVERY odd squarefree `1 < s ≤ ⌊x^400⌋₊ ^ 2` coprime to `m₀`,
   `|∑ q ∈ PPset m₀ a₀ X, (jacobiSym (q : ℤ) s : ℝ)| ≤ x ^ (-3 : ℝ) * ((PPset m₀ a₀ X).card : ℝ)`. -/
theorem jacobi_cancellation_on_PPset_unconditional {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ x₀ : ℝ, 3 ≤ x₀ ∧
      ∀ (x X : ℝ) (m₀ a₀ : ℕ), x₀ ≤ x → 0 < m₀ → 8 ∣ m₀ → a₀.Coprime m₀ →
        (m₀ : ℝ) ≤ (Real.log X) ^ (1 / ε) →
        x ^ (ε / 6) ≤ Real.log X → Real.log X ≤ x ^ (ε / 5) * Real.log x ^ 2 →
        X ^ (9 / 10 : ℝ) ≤ ((PPset m₀ a₀ X).card : ℝ) ∧
        ∀ s : ℕ, 1 < s → Odd s → Squarefree s → s.Coprime m₀ → s ≤ ⌊x ^ 400⌋₊ ^ 2 →
          |∑ q ∈ PPset m₀ a₀ X, (jacobiSym (q : ℤ) s : ℝ)| ≤
            x ^ (-3 : ℝ) * ((PPset m₀ a₀ X).card : ℝ) := by
  obtain ⟨c_sw, hc_sw, hsw_all⟩ := Stage10SiegelWalfiszFull.siegel_walfisz_pi
  set A_tot : ℝ := 1 / ε + 4800 / ε
  have hA_pos : 0 < A_tot := by positivity
  obtain ⟨C_sw, hC_sw, hsw⟩ := hsw_all A_tot hA_pos
  -- Three asymptotic thresholds from `tendsto_rpow_mul_exp_neg_rpow`
  have hT1 := (tendsto_rpow_mul_exp_neg_rpow (K := c_sw) (B := 3 * (A_tot + 1) + 3) (α := ε / 12)
    hc_sw (by positivity)).eventually (Iio_mem_nhds (show (0 : ℝ) < 1 / (8 * C_sw) by positivity))
  have hT2 := (tendsto_rpow_mul_exp_neg_rpow (K := 1 / 2) (B := 3 * (A_tot + 1) + 3) (α := ε / 6)
    (by norm_num) (by positivity)).eventually (Iio_mem_nhds (show (0 : ℝ) < 1 / 8 by norm_num))
  have hT3 := (tendsto_rpow_mul_exp_neg_rpow (K := 1 / 10) (B := 3 * (1 / ε + 1)) (α := ε / 6)
    (by norm_num) (by positivity)).eventually (Iio_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))
  rw [Filter.eventually_atTop] at hT1 hT2 hT3
  obtain ⟨x1, hx1⟩ := hT1
  obtain ⟨x2, hx2⟩ := hT2
  obtain ⟨x3, hx3⟩ := hT3
  -- Also ensure `x^(ε/6) ≥ 2` so `X ≥ exp 2 ≥ 4` and `x ≥ (19200 / ε)^(12 / ε)` so `x^800 ≤ X^(1/2)`
  set x4 : ℝ := max (2 ^ (6 / ε)) ((19200 / ε) ^ (12 / ε))
  set x₀ : ℝ := max (max 3 x4) (max x1 (max x2 x3))
  refine ⟨x₀, le_trans (le_max_left _ _) (le_max_left _ _), fun x X m₀ a₀ hx hm0 h8 hcop hm_le hXlo hXhi => ?_⟩
  have hx3' : 3 ≤ x := (le_trans (le_max_left _ _) (le_max_left _ _)).trans hx
  have hx4' : x4 ≤ x := (le_trans (le_max_right _ _) (le_max_left _ _)).trans hx
  have hxx1 : x1 ≤ x := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hx
  have hxx2 : x2 ≤ x := (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)).trans hx
  have hxx3 : x3 ≤ x := (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)).trans hx
  have hx0 : 0 < x := by linarith
  have hx1_lt : 1 < x := by linarith
  have hL_ge2 : 2 ≤ Real.log X := by
    have h2 : (2 : ℝ) ^ (6 / ε) ≤ x := (le_max_left _ _).trans hx4'
    have hpow := Real.rpow_le_rpow (by positivity) h2 (by positivity : 0 ≤ ε / 6)
    rw [← Real.rpow_mul (by norm_num), show (6 / ε) * (ε / 6) = 1 by field_simp, Real.rpow_one] at hpow
    exact hpow.trans hXlo
  have hL_pos : 0 < Real.log X := by linarith
  by_cases hX_pos : 0 < X
  swap
  · have hXle : X ≤ 0 := not_lt.mp hX_pos
    have hPP_emp : PPset m₀ a₀ X = ∅ := by
      ext q; simp only [PPset, Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false]
      have hfl : ⌊X⌋₊ = 0 := Nat.floor_of_nonpos hXle
      rw [hfl]; omega
    constructor
    · rw [hPP_emp, Finset.card_empty, Nat.cast_zero]
      rcases hXle.lt_or_eq with hneg | rfl
      · rw [Real.rpow_def_of_neg hneg]
        have hcos : Real.cos (Real.pi * (9 / 10 : ℝ)) ≤ 0 :=
          Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
        have hcos' : Real.cos (9 / 10 * Real.pi) ≤ 0 := by rwa [mul_comm] at hcos
        have : Real.exp (Real.log X * (9 / 10)) * Real.cos (9 / 10 * Real.pi) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hcos'
        linarith
      · rw [Real.zero_rpow (by norm_num)]
    · intro s _ _ _ _ _
      rw [hPP_emp, Finset.sum_empty, abs_zero, Finset.card_empty, Nat.cast_zero, mul_zero]
  have hX_ge4 : 4 ≤ X := by
    have hexp : Real.exp 2 ≤ X := by rwa [← Real.le_log_iff_exp_le hX_pos]
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have he2 : (4 : ℝ) ≤ Real.exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]; nlinarith
    linarith
  have hL_le_x3 : Real.log X ≤ x ^ 3 := by
    have hLx : Real.log x ≤ x := (Real.log_le_sub_one_of_pos hx0).trans (by linarith)
    have hxe : x ^ (ε / 5) ≤ x := by
      calc x ^ (ε / 5) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1_lt.le (by linarith)
        _ = x := Real.rpow_one x
    have hsq : Real.log x ^ 2 ≤ x ^ 2 := by nlinarith [Real.log_nonneg hx1_lt.le]
    calc Real.log X ≤ x ^ (ε / 5) * Real.log x ^ 2 := hXhi
      _ ≤ x * x ^ 2 := mul_le_mul hxe hsq (sq_nonneg _) hx0.le
      _ = x ^ 3 := by ring
  have hsqrtL_ge : x ^ (ε / 12) ≤ Real.sqrt (Real.log X) := by
    rw [Real.le_sqrt (Real.rpow_nonneg hx0.le _) hL_pos.le, sq, ← Real.rpow_add hx0,
      show ε / 12 + ε / 12 = ε / 6 by ring]
    exact hXlo
  -- Step 1: Apply Siegel–Walfisz to `m₀` itself to get `X / (4 * (log X)^(1 + 1/ε)) ≤ |PPset|`
  have : NeZero m₀ := ⟨hm0.ne'⟩
  have hm_Atot : (m₀ : ℝ) ≤ (Real.log X) ^ A_tot :=
    hm_le.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by dsimp only [A_tot]; linarith [show 0 ≤ 4800 / ε by positivity]))
  have hsw_m₀ := hsw X hX_ge4 m₀ hm_Atot a₀ hcop
  have hsw_m₀' : |(Stage2DirichletAP.primeCountAP m₀ a₀ X : ℝ) - liX X / (m₀.totient : ℝ)| ≤
      C_sw * X * Real.exp (-c_sw * Real.sqrt (Real.log X)) := by
    have hcast : Stage2DirichletAP.primeCountAP m₀ a₀ (⌊X⌋₊ : ℝ) = Stage2DirichletAP.primeCountAP m₀ a₀ X := by
      simp [Stage2DirichletAP.primeCountAP]
    rw [← hcast]; exact hsw_m₀
  have hdiff_m₀ := abs_card_PPset_sub_primeCountAP_le m₀ a₀ (by linarith : 1 ≤ X)
  have hli_lo : X / (2 * (Real.log X) ^ (1 / ε + 1)) ≤ liX X / (m₀.totient : ℝ) := by
    have hphi_pos : (0 : ℝ) < (m₀.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hm0)
    have hphi_le : (m₀.totient : ℝ) ≤ (Real.log X) ^ (1 / ε) :=
      (by exact_mod_cast Nat.totient_le m₀ : (m₀.totient : ℝ) ≤ (m₀ : ℝ)).trans hm_le
    have hli := liX_lower hX_ge4
    calc X / (2 * (Real.log X) ^ (1 / ε + 1))
        = (X / (2 * Real.log X)) / (Real.log X) ^ (1 / ε) := by
          rw [Real.rpow_add hL_pos, Real.rpow_one, div_div]; ring
      _ ≤ liX X / (Real.log X) ^ (1 / ε) := div_le_div_of_nonneg_right hli (by positivity)
      _ ≤ liX X / (m₀.totient : ℝ) :=
          div_le_div_of_nonneg_left (le_trans (by positivity) hli) hphi_pos hphi_le
  -- Bound the error terms for `m₀` by `(1/8) * X / (Real.log X)^(1/ε + 1)`
  have herr_sw : C_sw * (Real.log X) ^ (A_tot + 1) * Real.exp (-c_sw * Real.sqrt (Real.log X)) ≤
      x ^ (-3 : ℝ) / 8 := by
    have hL_pow : (Real.log X) ^ (A_tot + 1) ≤ x ^ (3 * (A_tot + 1)) := by
      calc (Real.log X) ^ (A_tot + 1) ≤ (x ^ 3) ^ (A_tot + 1) :=
            Real.rpow_le_rpow hL_pos.le hL_le_x3 (by positivity)
        _ = x ^ (3 * (A_tot + 1)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; push_cast; ring
    have hexp_le : Real.exp (-c_sw * Real.sqrt (Real.log X)) ≤ Real.exp (-c_sw * x ^ (ε / 12)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hbd1 : x ^ (3 * (A_tot + 1) + 3) * Real.exp (-c_sw * x ^ (ε / 12)) < 1 / (8 * C_sw) := hx1 x hxx1
    have hmul_x3 : x ^ (3 * (A_tot + 1)) * Real.exp (-c_sw * x ^ (ε / 12)) ≤
        x ^ (-3 : ℝ) * (1 / (8 * C_sw)) := by
      have h1 : x ^ (3 * (A_tot + 1)) = x ^ (-3 : ℝ) * x ^ (3 * (A_tot + 1) + 3) := by
        rw [← Real.rpow_add hx0]; congr 1; ring
      rw [h1, mul_assoc]
      exact mul_le_mul_of_nonneg_left hbd1.le (Real.rpow_nonneg hx0.le _)
    calc C_sw * (Real.log X) ^ (A_tot + 1) * Real.exp (-c_sw * Real.sqrt (Real.log X))
        ≤ C_sw * (x ^ (3 * (A_tot + 1)) * Real.exp (-c_sw * x ^ (ε / 12))) := by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left
            (mul_le_mul hL_pow hexp_le (Real.exp_pos _).le (by positivity)) hC_sw.le
      _ ≤ C_sw * (x ^ (-3 : ℝ) * (1 / (8 * C_sw))) := mul_le_mul_of_nonneg_left hmul_x3 hC_sw.le
      _ = x ^ (-3 : ℝ) / 8 := by field_simp [hC_sw.ne']
  have herr_sqrt : (Real.log X) ^ (A_tot + 1) * X ^ (-(1 / 2 : ℝ)) ≤ x ^ (-3 : ℝ) / 8 := by
    have hL_pow : (Real.log X) ^ (A_tot + 1) ≤ x ^ (3 * (A_tot + 1)) := by
      calc (Real.log X) ^ (A_tot + 1) ≤ (x ^ 3) ^ (A_tot + 1) :=
            Real.rpow_le_rpow hL_pos.le hL_le_x3 (by positivity)
        _ = x ^ (3 * (A_tot + 1)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; push_cast; ring
    have hexp_le : X ^ (-(1 / 2 : ℝ)) ≤ Real.exp (-(1 / 2) * x ^ (ε / 6)) := by
      rw [Real.rpow_def_of_pos hX_pos]; apply Real.exp_le_exp.mpr; nlinarith
    have hbd2 : x ^ (3 * (A_tot + 1) + 3) * Real.exp (-(1 / 2) * x ^ (ε / 6)) < 1 / 8 := hx2 x hxx2
    have h1 : x ^ (3 * (A_tot + 1)) = x ^ (-3 : ℝ) * x ^ (3 * (A_tot + 1) + 3) := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    calc (Real.log X) ^ (A_tot + 1) * X ^ (-(1 / 2 : ℝ))
        ≤ x ^ (3 * (A_tot + 1)) * Real.exp (-(1 / 2) * x ^ (ε / 6)) :=
          mul_le_mul hL_pow hexp_le (Real.rpow_nonneg hX_pos.le _) (by positivity)
      _ = x ^ (-3 : ℝ) * (x ^ (3 * (A_tot + 1) + 3) * Real.exp (-(1 / 2) * x ^ (ε / 6))) := by
          rw [h1, mul_assoc]
      _ ≤ x ^ (-3 : ℝ) * (1 / 8) := mul_le_mul_of_nonneg_left hbd2.le (Real.rpow_nonneg hx0.le _)
      _ = x ^ (-3 : ℝ) / 8 := by ring
  have hxm3_le1 : x ^ (-3 : ℝ) ≤ 1 := by
    rw [Real.rpow_neg hx0.le]
    exact inv_le_one_of_one_le₀ (by norm_cast; nlinarith)
  have hL_pow_mono : (Real.log X) ^ (1 / ε + 1) ≤ (Real.log X) ^ (A_tot + 1) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by dsimp only [A_tot]; linarith [show 0 ≤ 4800 / ε by positivity])
  have hPP_lo_main : X / (4 * (Real.log X) ^ (1 / ε + 1)) ≤ ((PPset m₀ a₀ X).card : ℝ) := by
    have h1 : C_sw * X * Real.exp (-c_sw * Real.sqrt (Real.log X)) ≤
        X / (8 * (Real.log X) ^ (1 / ε + 1)) := by
      rw [le_div_iff₀ (by positivity)]
      have hmul : C_sw * (Real.log X) ^ (1 / ε + 1) * Real.exp (-c_sw * Real.sqrt (Real.log X)) ≤ 1 / 8 := by
        calc C_sw * (Real.log X) ^ (1 / ε + 1) * Real.exp (-c_sw * Real.sqrt (Real.log X))
            ≤ C_sw * (Real.log X) ^ (A_tot + 1) * Real.exp (-c_sw * Real.sqrt (Real.log X)) := by gcongr
          _ ≤ x ^ (-3 : ℝ) / 8 := herr_sw
          _ ≤ 1 / 8 := by linarith
      nlinarith
    have h2 : X ^ (1 / 2 : ℝ) ≤ X / (8 * (Real.log X) ^ (1 / ε + 1)) := by
      rw [le_div_iff₀ (by positivity)]
      have hX_split : X ^ (1 / 2 : ℝ) = X * X ^ (-(1 / 2 : ℝ)) := by
        conv_lhs => rw [show (1 / 2 : ℝ) = 1 + -(1 / 2 : ℝ) by norm_num]
        rw [Real.rpow_add hX_pos, Real.rpow_one]
      have hmul : (Real.log X) ^ (1 / ε + 1) * X ^ (-(1 / 2 : ℝ)) ≤ 1 / 8 := by
        calc (Real.log X) ^ (1 / ε + 1) * X ^ (-(1 / 2 : ℝ))
            ≤ (Real.log X) ^ (A_tot + 1) * X ^ (-(1 / 2 : ℝ)) := by gcongr
          _ ≤ x ^ (-3 : ℝ) / 8 := herr_sqrt
          _ ≤ 1 / 8 := by linarith
      rw [hX_split]; nlinarith
    have h3 := (abs_le.mp hsw_m₀').1
    have h4 := (abs_le.mp hdiff_m₀).1
    have hcomb : X / (2 * (Real.log X) ^ (1 / ε + 1)) -
        X / (8 * (Real.log X) ^ (1 / ε + 1)) - X / (8 * (Real.log X) ^ (1 / ε + 1)) =
        X / (4 * (Real.log X) ^ (1 / ε + 1)) := by ring
    linarith
  have hPP_rpow : X ^ (9 / 10 : ℝ) ≤ ((PPset m₀ a₀ X).card : ℝ) := by
    refine le_trans ?_ hPP_lo_main
    rw [le_div_iff₀ (by positivity)]
    have hX_split : X ^ (9 / 10 : ℝ) = X * X ^ (-(1 / 10 : ℝ)) := by
      conv_lhs => rw [show (9 / 10 : ℝ) = 1 + -(1 / 10 : ℝ) by norm_num]
      rw [Real.rpow_add hX_pos, Real.rpow_one]
    have hL_pow : (Real.log X) ^ (1 / ε + 1) ≤ x ^ (3 * (1 / ε + 1)) := by
      calc (Real.log X) ^ (1 / ε + 1) ≤ (x ^ 3) ^ (1 / ε + 1) :=
            Real.rpow_le_rpow hL_pos.le hL_le_x3 (by positivity)
        _ = x ^ (3 * (1 / ε + 1)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; push_cast; ring
    have hexp_le : X ^ (-(1 / 10 : ℝ)) ≤ Real.exp (-(1 / 10) * x ^ (ε / 6)) := by
      rw [Real.rpow_def_of_pos hX_pos]; apply Real.exp_le_exp.mpr; nlinarith
    have hbd3 : x ^ (3 * (1 / ε + 1)) * Real.exp (-(1 / 10) * x ^ (ε / 6)) < 1 / 4 := hx3 x hxx3
    have hprod : 4 * (Real.log X) ^ (1 / ε + 1) * X ^ (-(1 / 10 : ℝ)) ≤ 1 := by
      have : (Real.log X) ^ (1 / ε + 1) * X ^ (-(1 / 10 : ℝ)) ≤ 1 / 4 :=
        (mul_le_mul hL_pow hexp_le (Real.rpow_nonneg hX_pos.le _) (by positivity)).trans hbd3.le
      linarith
    rw [hX_split]; nlinarith
  refine ⟨hPP_rpow, fun s hs1 hodd hsq hcop_s hsN => ?_⟩
  -- Step 2: Jacobi cancellation on `PPset m₀ a₀ X` for odd squarefree `1 < s ≤ ⌊x^400⌋²`
  have hs_le_x800 : (s : ℝ) ≤ x ^ 800 := by
    have hfl : (⌊x ^ 400⌋₊ : ℝ) ≤ x ^ 400 := Nat.floor_le (by positivity)
    calc (s : ℝ) ≤ (⌊x ^ 400⌋₊ : ℝ) ^ 2 := by exact_mod_cast hsN
      _ ≤ (x ^ 400) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hfl 2
      _ = x ^ 800 := by ring
  have hs_le_sqrtX : (s : ℝ) ≤ X ^ (1 / 2 : ℝ) :=
    hs_le_x800.trans (pow_le_sqrt_of_rpow_le_log ε hε x X hx3' ((le_max_right _ _).trans hx4') hX_pos hXlo)
  have hs_le_L : (s : ℝ) ≤ (Real.log X) ^ (4800 / ε) := by
    have hx_le_L : x ≤ (Real.log X) ^ (6 / ε) := by
      have h := Real.rpow_le_rpow (Real.rpow_nonneg hx0.le _) hXlo (by positivity : 0 ≤ 6 / ε)
      rwa [← Real.rpow_mul hx0.le, show (ε / 6) * (6 / ε) = 1 by field_simp, Real.rpow_one] at h
    calc (s : ℝ) ≤ x ^ 800 := hs_le_x800
      _ ≤ ((Real.log X) ^ (6 / ε)) ^ (800 : ℕ) := pow_le_pow_left₀ hx0.le hx_le_L 800
      _ = (Real.log X) ^ (4800 / ε) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hL_pos.le]; congr 1; push_cast; ring
  have hms_le : ((m₀ * s : ℕ) : ℝ) ≤ (Real.log X) ^ A_tot := by
    push_cast
    rw [show A_tot = 1 / ε + 4800 / ε from rfl, Real.rpow_add hL_pos]
    exact mul_le_mul hm_le hs_le_L (Nat.cast_nonneg _) (by positivity)
  have hpart := jacobi_sum_PPset_eq_clsB m₀ s a₀ hm0 (by omega) hs_le_sqrtX
  have horth := sum_jacobi_clsB_eq_zero m₀ s a₀ hm0 hs1 hodd hsq hcop_s
  set mainTerm : ℝ := liX X / ((m₀ * s).totient : ℝ)
  have hsub_main :
      ∑ q ∈ PPset m₀ a₀ X, (jacobiSym (q : ℤ) s : ℝ) =
        ∑ b ∈ clsB m₀ s a₀,
          (jacobiSym (b : ℤ) s : ℝ) * (((PPset (m₀ * s) b X).card : ℝ) - mainTerm) := by
    rw [hpart]
    have h0 : ∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * mainTerm = 0 := by
      rw [← Finset.sum_mul, horth, zero_mul]
    have hsplit_sub :
        ∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * (((PPset (m₀ * s) b X).card : ℝ) - mainTerm) =
          (∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * ((PPset (m₀ * s) b X).card : ℝ)) -
          (∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * mainTerm) := by
      rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun _ _ => by ring
    linarith
  have : NeZero (m₀ * s) := ⟨Nat.mul_ne_zero hm0.ne' (by omega)⟩
  have hper_b : ∀ b ∈ clsB m₀ s a₀,
      |((PPset (m₀ * s) b X).card : ℝ) - mainTerm| ≤
        C_sw * X * Real.exp (-c_sw * Real.sqrt (Real.log X)) + X ^ (1 / 2 : ℝ) := by
    intro b hb
    have hbcop := coprime_of_mem_clsB hcop hb
    have h1 := hsw X hX_ge4 (m₀ * s) hms_le b hbcop
    have hcast : Stage2DirichletAP.primeCountAP (m₀ * s) b (⌊X⌋₊ : ℝ) =
        Stage2DirichletAP.primeCountAP (m₀ * s) b X := by simp [Stage2DirichletAP.primeCountAP]
    rw [hcast] at h1
    have h1' : |(Stage2DirichletAP.primeCountAP (m₀ * s) b X : ℝ) - mainTerm| ≤
        C_sw * X * Real.exp (-c_sw * Real.sqrt (Real.log X)) := h1
    have h2 := abs_card_PPset_sub_primeCountAP_le (m₀ * s) b (by linarith : 1 ≤ X)
    have htri := abs_sub_le ((PPset (m₀ * s) b X).card : ℝ)
      (Stage2DirichletAP.primeCountAP (m₀ * s) b X : ℝ) mainTerm
    linarith
  have hsum_abs :
      |∑ q ∈ PPset m₀ a₀ X, (jacobiSym (q : ℤ) s : ℝ)| ≤
        (s : ℝ) * (C_sw * X * Real.exp (-c_sw * Real.sqrt (Real.log X)) + X ^ (1 / 2 : ℝ)) := by
    rw [hsub_main]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ b ∈ clsB m₀ s a₀,
        |(jacobiSym (b : ℤ) s : ℝ) * (((PPset (m₀ * s) b X).card : ℝ) - mainTerm)| ≤
          C_sw * X * Real.exp (-c_sw * Real.sqrt (Real.log X)) + X ^ (1 / 2 : ℝ) := by
      intro b hb
      rw [abs_mul]
      have hj : |(jacobiSym (b : ℤ) s : ℝ)| ≤ 1 := by
        rcases jacobiSym.trichotomy (b : ℤ) s with h | h | h <;> simp [h]
      calc |(jacobiSym (b : ℤ) s : ℝ)| * |((PPset (m₀ * s) b X).card : ℝ) - mainTerm|
          ≤ 1 * (C_sw * X * Real.exp (-c_sw * Real.sqrt (Real.log X)) + X ^ (1 / 2 : ℝ)) :=
            mul_le_mul hj (hper_b b hb) (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    calc ∑ b ∈ clsB m₀ s a₀, |(jacobiSym (b : ℤ) s : ℝ) * (((PPset (m₀ * s) b X).card : ℝ) - mainTerm)|
        ≤ ∑ _b ∈ clsB m₀ s a₀, (C_sw * X * Real.exp (-c_sw * Real.sqrt (Real.log X)) + X ^ (1 / 2 : ℝ)) :=
          Finset.sum_le_sum hterm
      _ = ((clsB m₀ s a₀).card : ℝ) * (C_sw * X * Real.exp (-c_sw * Real.sqrt (Real.log X)) + X ^ (1 / 2 : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (s : ℝ) * (C_sw * X * Real.exp (-c_sw * Real.sqrt (Real.log X)) + X ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast card_clsB_le m₀ s a₀) (by positivity)
  -- Compare `(s : ℝ) * (err)` against `x ^ (-3) * (X / (4 * (log X)^(1/ε + 1)))`
  have hprod_le : (s : ℝ) * (Real.log X) ^ (1 / ε + 1) ≤ (Real.log X) ^ (A_tot + 1) := by
    have hpow : (Real.log X) ^ (4800 / ε) * (Real.log X) ^ (1 / ε + 1) = (Real.log X) ^ (A_tot + 1) := by
      rw [← Real.rpow_add hL_pos]; congr 1; dsimp only [A_tot]; ring
    rw [← hpow]
    exact mul_le_mul_of_nonneg_right hs_le_L (by positivity)
  have hfinal_num :
      (s : ℝ) * (C_sw * X * Real.exp (-c_sw * Real.sqrt (Real.log X)) + X ^ (1 / 2 : ℝ)) ≤
        x ^ (-3 : ℝ) * (X / (4 * (Real.log X) ^ (1 / ε + 1))) := by
    rw [mul_div_assoc', le_div_iff₀ (by positivity)]
    have hX_split : X ^ (1 / 2 : ℝ) = X * X ^ (-(1 / 2 : ℝ)) := by
      conv_lhs => rw [show (1 / 2 : ℝ) = 1 + -(1 / 2 : ℝ) by norm_num]
      rw [Real.rpow_add hX_pos, Real.rpow_one]
    have hpart1 :
        (s : ℝ) * (C_sw * X * Real.exp (-c_sw * Real.sqrt (Real.log X))) * (4 * (Real.log X) ^ (1 / ε + 1)) ≤
          x ^ (-3 : ℝ) * X / 2 := by
      have h1 : (s : ℝ) * (Real.log X) ^ (1 / ε + 1) * (C_sw * Real.exp (-c_sw * Real.sqrt (Real.log X))) ≤
          x ^ (-3 : ℝ) / 8 := by
        calc (s : ℝ) * (Real.log X) ^ (1 / ε + 1) * (C_sw * Real.exp (-c_sw * Real.sqrt (Real.log X)))
            ≤ (Real.log X) ^ (A_tot + 1) * (C_sw * Real.exp (-c_sw * Real.sqrt (Real.log X))) :=
              mul_le_mul_of_nonneg_right hprod_le (by positivity)
          _ = C_sw * (Real.log X) ^ (A_tot + 1) * Real.exp (-c_sw * Real.sqrt (Real.log X)) := by ring
          _ ≤ x ^ (-3 : ℝ) / 8 := herr_sw
      nlinarith
    have hpart2 :
        (s : ℝ) * X ^ (1 / 2 : ℝ) * (4 * (Real.log X) ^ (1 / ε + 1)) ≤ x ^ (-3 : ℝ) * X / 2 := by
      rw [hX_split]
      have h2 : (s : ℝ) * (Real.log X) ^ (1 / ε + 1) * X ^ (-(1 / 2 : ℝ)) ≤ x ^ (-3 : ℝ) / 8 := by
        calc (s : ℝ) * (Real.log X) ^ (1 / ε + 1) * X ^ (-(1 / 2 : ℝ))
            ≤ (Real.log X) ^ (A_tot + 1) * X ^ (-(1 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_right hprod_le (by positivity)
          _ ≤ x ^ (-3 : ℝ) / 8 := herr_sqrt
      nlinarith
    have hdist :
        (s : ℝ) * (C_sw * X * Real.exp (-c_sw * Real.sqrt (Real.log X)) + X ^ (1 / 2 : ℝ)) *
            (4 * (Real.log X) ^ (1 / ε + 1)) =
          (s : ℝ) * (C_sw * X * Real.exp (-c_sw * Real.sqrt (Real.log X))) * (4 * (Real.log X) ^ (1 / ε + 1)) +
          (s : ℝ) * X ^ (1 / 2 : ℝ) * (4 * (Real.log X) ^ (1 / ε + 1)) := by ring
    linarith
  exact hsum_abs.trans (hfinal_num.trans (mul_le_mul_of_nonneg_left hPP_lo_main (Real.rpow_nonneg hx0.le _)))

/-- **General `MSqMain` Reduction Engine**:
given any prime window `PPset m₀ a₀ X` satisfying off-diagonal Jacobi cancellation (up to at most
one exceptional odd squarefree conductor `nstar`), proves the full quadratic-twist mean-square bound
`≤ C * x * log x * |PPset m₀ a₀ X|`. -/
theorem meansq_bound_of_jacobi_cancellation {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C x₀ : ℝ, 0 < C ∧ 3 ≤ x₀ ∧
      ∀ (x X : ℝ) (m₀ a₀ : ℕ) (κ : ℕ → ℂ),
        x₀ ≤ x → 0 < m₀ → 8 ∣ m₀ →
        (∀ p : ℕ, p.Prime → p ∣ m₀ → (p : ℝ) ≤ x ^ (ε / 5) ∨ x ^ 400 < (p : ℝ)) →
        a₀.Coprime m₀ → x ^ (ε / 6) ≤ Real.log X → (∀ n, ‖κ n‖ ≤ 1) →
        (∃ nstar : ℕ, ∀ s : ℕ, 1 < s → Odd s → Squarefree s → s.Coprime m₀ →
          s ≤ ⌊x ^ 400⌋₊ ^ 2 → s ≠ nstar →
          |∑ q ∈ PPset m₀ a₀ X, (jacobiSym (q : ℤ) s : ℝ)| ≤
            x ^ (-3 : ℝ) * ((PPset m₀ a₀ X).card : ℝ)) →
        (∑ q ∈ PPset m₀ a₀ X,
            ‖∑ n ∈ Finset.Icc 1 ⌊x ^ 400⌋₊, ((cN x n : ℝ) : ℂ) * κ n * ((jacobiSym (n : ℤ) q : ℤ) : ℂ)‖ ^ 2) ≤
          C * x * Real.log x * ((PPset m₀ a₀ X).card : ℝ) := by
  obtain ⟨C1, x1, hC1, _, h1⟩ := sum_cN_le
  obtain ⟨C2, x2, hC2, _, h2⟩ := exists_primePowerSum_le
  obtain ⟨C3, x3, hC3, _, h3⟩ := RR_cN_le
  obtain ⟨C4, x4, hC4, _, h4⟩ := sum_sP_sq_le
  set C : ℝ := |C4| + 25 * C3 ^ 2 + 2 * C2 ^ 2 + 10 * |C2| * |C3| + C1 ^ 2
  set x₀ : ℝ := max (max (max x1 x2) (max x3 x4)) (max 3 ((19200 / ε) ^ (12 / ε)))
  have hC_pos : 0 < C := by
    have h1' : 0 ≤ |C4| := abs_nonneg C4
    have h2' : 0 ≤ 25 * C3 ^ 2 := by positivity
    have h3' : 0 ≤ 2 * C2 ^ 2 := by positivity
    have h4' : 0 ≤ 10 * |C2| * |C3| := by positivity
    have h5' : 0 < C1 ^ 2 := sq_pos_of_pos hC1
    dsimp only [C]; linarith
  refine ⟨C, x₀, hC_pos, le_trans (le_max_left _ _) (le_max_right _ _), ?_⟩
  intro x X m₀ a₀ κ hx hm0 h8 hsm hcop hX2 hκ ⟨ns0, hns0⟩
  simp only [x₀, max_le_iff] at hx
  obtain ⟨⟨⟨hx1, hx2⟩, ⟨hx3, hx4⟩⟩, ⟨hx5, hx6⟩⟩ := hx
  have hx0 : 0 < x := by linarith
  set N := ⌊x ^ 400⌋₊
  set PP := PPset m₀ a₀ X
  obtain ⟨nstar, hns1, hns⟩ : ∃ nstar : ℕ, 1 < nstar ∧
      ∀ s : ℕ, 1 < s → Odd s → Squarefree s → s.Coprime m₀ → s ≤ N ^ 2 → s ≠ nstar →
        |∑ q ∈ PP, (jacobiSym (q : ℤ) s : ℝ)| ≤ x ^ (-3 : ℝ) * (PP.card : ℝ) := by
    by_cases hc : 1 < ns0
    · exact ⟨ns0, hc, hns0⟩
    · exact ⟨2, by norm_num, fun s hs1 hs2 hs3 hs4 hs5 _ => hns0 s hs1 hs2 hs3 hs4 hs5 (by omega)⟩
  have hc0 : ∀ n, 0 ≤ cN x n := cN_nonneg x hx0.le
  have hcpp : ∀ n, cN x n ≠ 0 → IsPrimePow n := cN_primePow x
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hbig : ∀ n ∈ Finset.Icc 1 N, ∀ n' ∈ Finset.Icc 1 N, ∀ q ∈ PP,
      q.Prime ∧ q % m₀ = a₀ % m₀ ∧ n * n' < q := by
    intro n hn n' hn' q hq
    rw [show PP = PPset m₀ a₀ X from rfl, PPset, Finset.mem_filter, Finset.mem_Icc] at hq
    obtain ⟨⟨hq1, hq2⟩, hqp, hqm, hqX⟩ := hq
    refine ⟨hqp, hqm, ?_⟩
    have hXpos : 0 < X := by
      by_contra hneg
      have : ⌊X⌋₊ = 0 := Nat.floor_of_nonpos (not_lt.mp hneg)
      omega
    have hpow := pow_le_sqrt_of_rpow_le_log ε hε x X hx5 hx6 hXpos hX2
    have hfl : (N : ℝ) ≤ x ^ 400 := Nat.floor_le (by positivity)
    have hnr : (n : ℝ) ≤ x ^ 400 := le_trans (by exact_mod_cast (Finset.mem_Icc.mp hn).2) hfl
    have hnr' : (n' : ℝ) ≤ x ^ 400 := le_trans (by exact_mod_cast (Finset.mem_Icc.mp hn').2) hfl
    have hmul : (n : ℝ) * (n' : ℝ) ≤ x ^ 800 := by
      calc (n : ℝ) * (n' : ℝ) ≤ x ^ 400 * x ^ 400 := mul_le_mul hnr hnr' (Nat.cast_nonneg _) (by positivity)
        _ = x ^ 800 := by rw [← pow_add]
    have : ((n * n' : ℕ) : ℝ) < (q : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hPc : (0 : ℝ) ≤ (PP.card : ℝ) := Nat.cast_nonneg _
  have hη : (0 : ℝ) ≤ x ^ (-3 : ℝ) := Real.rpow_nonneg hx0.le _
  have step1 := meansq_expand PP (Finset.Icc 1 N) (cN x) hc0 κ hκ (fun n q => jacobiSym (n : ℤ) q)
  have step2 := meansq_split (Finset.Icc 1 N) (cN x) hc0 (fun n n' => soutPart m₀ (n * n'))
    (fun n n' => |∑ q ∈ PP, ((jacobiSym (n : ℤ) q * jacobiSym (n' : ℤ) q : ℤ) : ℝ)|) (PP.card : ℝ)
    (x ^ (-3 : ℝ)) hPc hη nstar
    (fun n hn n' hn' => by
      rw [abs_pair_sum_eq PP m₀ a₀ n n' h8 hcop (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn').1
        (hbig n hn n' hn')]
      exact abs_sum_jacobi_le PP _)
    (fun n hn n' hn' e1 e2 => by
      have hn1 := Finset.mem_Icc.mp hn
      have hn1' := Finset.mem_Icc.mp hn'
      rw [abs_pair_sum_eq PP m₀ a₀ n n' h8 hcop hn1.1 hn1'.1 (hbig n hn n' hn')]
      have hpos := soutPart_pos m₀ (n * n')
      refine hns _ (by change soutPart m₀ (n * n') ≠ 1 at e1; omega)
        (soutPart_odd m₀ _ (dvd_trans (by norm_num) h8)) (soutPart_squarefree m₀ _)
        (soutPart_coprime m₀ _) ?_ e2
      refine (soutPart_le m₀ _ (Nat.mul_pos hn1.1 hn1'.1)).trans ?_
      rw [sq]; exact Nat.mul_le_mul hn1.2 hn1'.2)
  have hp1 := pairs_one (cN x) hc0 hcpp m₀ N
  have hB : ∀ p, sP (cN x) N p ≤ |C2| * Real.log x := fun p =>
    (h2 x hx2 p).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hl0)
  have hpr := pairs_r (cN x) hc0 hcpp m₀ N nstar hns1 (|C2| * Real.log x) hB
  have hy1 : (1 : ℝ) ≤ x ^ (ε / 5) := Real.one_le_rpow (by linarith) (by positivity)
  have hRR := h3 x hx3 m₀ (x ^ (ε / 5)) hy1 (fun p hp hpm hpN => by
    rcases hsm p hp hpm with h | h
    · exact h
    · exfalso
      have hfl : (N : ℝ) ≤ x ^ 400 := Nat.floor_le (by positivity)
      have : (p : ℝ) ≤ (N : ℝ) := by exact_mod_cast hpN
      linarith)
  have hfin := final_size ε hε1 x hx5 C1 C2 C3 C4 (∑ n ∈ Finset.Icc 1 N, cN x n)
    (∑ p ∈ (Finset.Icc 1 N).filter Nat.Prime, sP (cN x) N p ^ 2) (RR (cN x) m₀ N)
    (Finset.sum_nonneg fun n _ => hc0 n) (h1 x hx1) (h4 x hx4) (RR_nonneg _ hc0 _ _) hRR
  refine step1.trans (step2.trans ?_)
  refine mul_le_mul_of_nonneg_right ?_ hPc
  linarith

/-- **HEADLINE UNCONDITIONAL THEOREM (`meanSquareHypW_of_bv_and_logfree`)**:
for EVERY `ε ∈ (0, 1]`, there exist `C > 0` and `x₀ ≥ 3` such that `MeanSquareHypW ε C x₀` holds
unconditionally (`0` assumptions, `0` `sorry`, `0` custom `axiom`s)! -/
theorem meanSquareHypW_of_bv_and_logfree {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C x₀ : ℝ, 0 < C ∧ 3 ≤ x₀ ∧ MeanSquareHypW ε C x₀ := by
  obtain ⟨x_sw, hx_sw, hsw⟩ := jacobi_cancellation_on_PPset_unconditional hε hε1
  obtain ⟨C, x_ms, hC, hx_ms, hms⟩ := meansq_bound_of_jacobi_cancellation hε hε1
  refine ⟨C, max x_sw x_ms, hC, le_trans hx_sw (le_max_left _ _), ?_⟩
  intro x X m₀ a₀ κ hx h8 hsm hcop ha4 hm_le hXlo hXhi hκ _
  have hm0 : 0 < m₀ := by
    rcases Nat.eq_zero_or_pos m₀ with rfl | h
    · rw [Nat.coprime_zero_right] at hcop; subst hcop; norm_num at ha4
    · exact h
  have ⟨hcard, hcancel⟩ := hsw x X m₀ a₀ ((le_max_left _ _).trans hx) hm0 h8 hcop hm_le hXlo hXhi
  refine ⟨hcard, hms x X m₀ a₀ κ ((le_max_right _ _).trans hx) hm0 h8 hsm hcop hXlo hκ ⟨0, ?_⟩⟩
  intro s hs1 hodd hsq hcops hsN _
  exact hcancel s hs1 hodd hsq hcops hsN

/-! ## Section 6: Unconditional `twisted_psi_mean_square_on_primes`, Log-Free Zero-Density Boxes & M6 Wave 2 Bridges -/

/-- Totalized quadratic Dirichlet character `quadCharNat q : DirichletCharacter ℂ q`:
equals `quadCharPrime q` when `q.Prime`, and `1` otherwise (ergonomic inside `Finset.sum`). -/
def quadCharNat (q : ℕ) : DirichletCharacter ℂ q :=
  if h : q.Prime then @quadCharPrime q ⟨h⟩ else 1

theorem quadCharNat_eq_quadCharPrime {q : ℕ} (hq : q.Prime) :
    quadCharNat q = @quadCharPrime q ⟨hq⟩ :=
  dif_pos hq

theorem quadCharNat_apply_nat {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (n : ℕ) :
    quadCharNat q (n : ZMod q) = ((jacobiSym (n : ℤ) q : ℤ) : ℂ) := by
  rw [quadCharNat_eq_quadCharPrime hq]
  have : Fact q.Prime := ⟨hq⟩
  exact quadCharPrime_apply_nat hq2 n

theorem quadCharNat_ne_one {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    quadCharNat q ≠ 1 := by
  rw [quadCharNat_eq_quadCharPrime hq]
  have : Fact q.Prime := ⟨hq⟩
  exact quadCharPrime_ne_one hq2

theorem quadCharNat_isPrimitive {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    (quadCharNat q).IsPrimitive := by
  rw [quadCharNat_eq_quadCharPrime hq]
  have : Fact q.Prime := ⟨hq⟩
  exact quadCharPrime_isPrimitive hq2

theorem quadCharNat_sq_eq_one {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    (quadCharNat q) ^ 2 = 1 := by
  rw [quadCharNat_eq_quadCharPrime hq]
  have : Fact q.Prime := ⟨hq⟩
  exact quadCharPrime_sq_eq_one hq2

/-- **HEADLINE UNCONDITIONAL THEOREM (`twisted_psi_mean_square_on_primes`)**:
combining `Stage11SecondMomentFrame.bdh_twisted_primes_mean_square_le` (BDH + Parseval),
`Stage11BombieriVinogradov.multiplicative_large_sieve_Ioc`, and
`Stage11BombieriVinogradov.bombieri_vinogradov_rpow`:
for EVERY `A > 0`, there exist `B > 0` and `C > 0` such that:
1. **(BDH/Parseval Quadratic-Twist `ψ` & Cesàro-1 Mean Square over Odd Primes `q ≤ Q`)**:
   for every fixed primitive character `ψ : PChar`, `x ≥ 16`, and `Q : ℕ` with `ψ.N * Q ≤ x / 2`,
   letting `P := (Finset.Icc 3 Q).filter (fun q => q.Prime ∧ ¬ q ∣ ψ.N)`:
   `∑_{q ∈ P} φ(ψ.N * q)⁻¹ ‖ψ(x, ψ · (·/q))‖² ≤ C * (x * (ψ.N * Q) * (log x)³ + x² / (log x)^A)`
   AND the same bound for `cesaroWindowPsiChar (twistedChar ψ.χ (quadCharNat q)) x`;
2. **(Multiplicative Large-Sieve Unweighted `L²` Bound for `ψ(x, (·/q))`)**:
   for every `Q : ℕ` and `x ≥ 1`:
   `∑_{q ∈ [3, Q], q prime} ‖ψ(x, (·/q))‖² ≤ 6 * (⌊x⌋ + 3 * Q²) * x * log x`;
3. **(Bombieri–Vinogradov `L¹` Average for `ψ(x, (·/q))` up to `x^(1/2) / (log x)^B`)**:
   for every `x ≥ 3`:
   `∑_{q ∈ [3, ⌊x^(1/2)/(log x)^B⌋], q prime} φ(q)⁻¹ ‖ψ(x, (·/q))‖ ≤ C * x / (log x)^A`. -/
theorem twisted_psi_mean_square_on_primes {A : ℝ} (hA : 0 < A) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧
      (∀ (ψ : PChar) (x : ℝ), 16 ≤ x → ∀ Q : ℕ, ((ψ.N * Q : ℕ) : ℝ) ≤ x / 2 →
        let P := (Finset.Icc 3 Q).filter (fun q => q.Prime ∧ ¬ q ∣ ψ.N)
        (∑ q ∈ P, ((ψ.N * q).totient : ℝ)⁻¹ *
            ‖Stage2DirichletAP.chebyshevPsiChar (Stage11SecondMomentFrame.twistedChar ψ.χ (quadCharNat q)) x‖ ^ 2 ≤
          C * (x * ((ψ.N * Q : ℕ) : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ A)) ∧
        (∑ q ∈ P, ((ψ.N * q).totient : ℝ)⁻¹ *
            ‖Stage11SecondMomentFrame.cesaroWindowPsiChar (Stage11SecondMomentFrame.twistedChar ψ.χ (quadCharNat q)) x‖ ^ 2 ≤
          C * (x * ((ψ.N * Q : ℕ) : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ A))) ∧
      (∀ (Q : ℕ) (x : ℝ), 1 ≤ x →
        ∑ q ∈ (Finset.Icc 3 Q).filter Nat.Prime,
            ‖Stage2DirichletAP.chebyshevPsiChar (quadCharNat q) x‖ ^ 2 ≤
          6 * ((⌊x⌋₊ : ℝ) + 3 * (Q : ℝ) ^ 2) * x * Real.log x) ∧
      (∀ x : ℝ, 3 ≤ x →
        ∑ q ∈ (Finset.Icc 3 ⌊x ^ (1 / 2 : ℝ) / (Real.log x) ^ B⌋₊).filter Nat.Prime,
            (q.totient : ℝ)⁻¹ * ‖Stage2DirichletAP.chebyshevPsiChar (quadCharNat q) x‖ ≤
          C * x / (Real.log x) ^ A) := by
  classical
  obtain ⟨C₁, hC₁, hbdh⟩ := Stage11SecondMomentFrame.bdh_twisted_primes_mean_square_le hA
  obtain ⟨B, C₂, hB, hC₂, hbv⟩ := Stage11BombieriVinogradov.bombieri_vinogradov_rpow A
  refine ⟨B, max C₁ C₂, hB, lt_of_lt_of_le hC₁ (le_max_left _ _), ?_, ?_, ?_⟩
  · -- Part 1: BDH + Parseval quadratic-twist mean square
    intro ψ x hx Q hQx
    dsimp only
    set P := (Finset.Icc 3 Q).filter (fun q => q.Prime ∧ ¬ q ∣ ψ.N)
    set P₀ := (Finset.Icc 1 Q).filter (fun q => q.Prime ∧ ¬ q ∣ ψ.N)
    have hP_sub : P ⊆ P₀ := fun q hq => by
      simp only [P, P₀, Finset.mem_filter, Finset.mem_Icc] at hq ⊢
      exact ⟨⟨by omega, hq.1.2⟩, hq.2⟩
    have ⟨hbd1, hbd2⟩ := hbdh ψ x hx Q hQx
    have hLx_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hRHS_nn : 0 ≤ x * ((ψ.N * Q : ℕ) : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ A :=
      add_nonneg (by positivity) (div_nonneg (sq_nonneg x) (Real.rpow_nonneg hLx_pos.le A))
    constructor
    · calc ∑ q ∈ P, ((ψ.N * q).totient : ℝ)⁻¹ *
              ‖Stage2DirichletAP.chebyshevPsiChar (Stage11SecondMomentFrame.twistedChar ψ.χ (quadCharNat q)) x‖ ^ 2
          ≤ ∑ q ∈ P, ((ψ.N * q).totient : ℝ)⁻¹ *
              ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
                ‖Stage2DirichletAP.chebyshevPsiChar (Stage11SecondMomentFrame.twistedChar ψ.χ χ) x‖ ^ 2 := by
            refine Finset.sum_le_sum fun q hq => mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Nat.cast_nonneg _))
            have hq3 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
            have hqp := (Finset.mem_filter.mp hq).2.1
            have hmem : quadCharNat q ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q) :=
              Finset.mem_erase.mpr ⟨quadCharNat_ne_one hqp (by omega), Finset.mem_univ _⟩
            exact Finset.single_le_sum
              (f := fun χ => ‖Stage2DirichletAP.chebyshevPsiChar (Stage11SecondMomentFrame.twistedChar ψ.χ χ) x‖ ^ 2)
              (fun _ _ => sq_nonneg _) hmem
        _ ≤ ∑ q ∈ P₀, ((ψ.N * q).totient : ℝ)⁻¹ *
              ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
                ‖Stage2DirichletAP.chebyshevPsiChar (Stage11SecondMomentFrame.twistedChar ψ.χ χ) x‖ ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hP_sub
              (fun _ _ _ => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
        _ ≤ C₁ * (x * ((ψ.N * Q : ℕ) : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ A) := hbd1
        _ ≤ max C₁ C₂ * (x * ((ψ.N * Q : ℕ) : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ A) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hRHS_nn
    · calc ∑ q ∈ P, ((ψ.N * q).totient : ℝ)⁻¹ *
              ‖Stage11SecondMomentFrame.cesaroWindowPsiChar (Stage11SecondMomentFrame.twistedChar ψ.χ (quadCharNat q)) x‖ ^ 2
          ≤ ∑ q ∈ P, ((ψ.N * q).totient : ℝ)⁻¹ *
              ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
                ‖Stage11SecondMomentFrame.cesaroWindowPsiChar (Stage11SecondMomentFrame.twistedChar ψ.χ χ) x‖ ^ 2 := by
            refine Finset.sum_le_sum fun q hq => mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Nat.cast_nonneg _))
            have hq3 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
            have hqp := (Finset.mem_filter.mp hq).2.1
            have hmem : quadCharNat q ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q) :=
              Finset.mem_erase.mpr ⟨quadCharNat_ne_one hqp (by omega), Finset.mem_univ _⟩
            exact Finset.single_le_sum
              (f := fun χ => ‖Stage11SecondMomentFrame.cesaroWindowPsiChar (Stage11SecondMomentFrame.twistedChar ψ.χ χ) x‖ ^ 2)
              (fun _ _ => sq_nonneg _) hmem
        _ ≤ ∑ q ∈ P₀, ((ψ.N * q).totient : ℝ)⁻¹ *
              ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
                ‖Stage11SecondMomentFrame.cesaroWindowPsiChar (Stage11SecondMomentFrame.twistedChar ψ.χ χ) x‖ ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hP_sub
              (fun _ _ _ => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
        _ ≤ C₁ * (x * ((ψ.N * Q : ℕ) : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ A) := hbd2
        _ ≤ max C₁ C₂ * (x * ((ψ.N * Q : ℕ) : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ A) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hRHS_nn
  · -- Part 2: Large sieve L² bound for `ψ(x, quadCharNat q)`
    intro Q x hx1
    have hx0 : 0 < x := by linarith
    have hLx : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hls := jacobi_large_sieve_l2_bound Q 0 ⌊x⌋₊ (fun n => (Λ n : ℂ))
    simp only [zero_add] at hls
    have hcongr :
        ∑ q ∈ (Finset.Icc 3 Q).filter Nat.Prime,
            ‖Stage2DirichletAP.chebyshevPsiChar (quadCharNat q) x‖ ^ 2 =
          ∑ q ∈ (Finset.Icc 3 Q).filter Nat.Prime,
            ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (Λ n : ℂ) * ((jacobiSym (n : ℤ) q : ℤ) : ℂ)‖ ^ 2 := by
      refine Finset.sum_congr rfl fun q hq => ?_
      have hqp := (Finset.mem_filter.mp hq).2
      have hq3 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
      congr 2
      unfold Stage2DirichletAP.chebyshevPsiChar
      have hsplit : Finset.range (⌊x⌋₊ + 1) = insert 0 (Finset.Ioc 0 ⌊x⌋₊) := by
        ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]; omega
      rw [hsplit, Finset.sum_insert (by simp), ArithmeticFunction.map_zero,
        Complex.ofReal_zero, mul_zero, zero_add]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [quadCharNat_apply_nat hqp (by omega) n, mul_comm]
    rw [hcongr]
    refine hls.trans ?_
    have hvM_sq : ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ‖(Λ n : ℂ)‖ ^ 2 ≤ 6 * x * Real.log x := by
      have hterm : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊, ‖(Λ n : ℂ)‖ ^ 2 ≤ Real.log x * Λ n := by
        intro n hn
        rw [Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, sq]
        have hn1 := (Finset.mem_Ioc.mp hn).1
        have hn_le : (n : ℝ) ≤ x :=
          (by exact_mod_cast (Finset.mem_Ioc.mp hn).2 : (n : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans (Nat.floor_le hx0.le)
        have hΛ_le : Λ n ≤ Real.log x :=
          ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log (Nat.cast_pos.mpr hn1) hn_le)
        exact mul_le_mul_of_nonneg_right hΛ_le ArithmeticFunction.vonMangoldt_nonneg
      have hIoc_eq : Finset.Ioc 0 ⌊x⌋₊ = Finset.Icc 1 ⌊x⌋₊ := by
        ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
      calc ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ‖(Λ n : ℂ)‖ ^ 2
          ≤ ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Real.log x * Λ n := Finset.sum_le_sum hterm
        _ = Real.log x * ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n := by rw [← Finset.mul_sum]
        _ = Real.log x * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n := by rw [hIoc_eq]
        _ ≤ Real.log x * (6 * (⌊x⌋₊ : ℝ)) := mul_le_mul_of_nonneg_left (sum_vM_Icc_le ⌊x⌋₊) hLx
        _ ≤ Real.log x * (6 * x) := mul_le_mul_of_nonneg_left (by linarith [Nat.floor_le hx0.le]) hLx
        _ = 6 * x * Real.log x := by ring
    calc ((⌊x⌋₊ : ℝ) + 3 * (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ‖(Λ n : ℂ)‖ ^ 2
        ≤ ((⌊x⌋₊ : ℝ) + 3 * (Q : ℝ) ^ 2) * (6 * x * Real.log x) :=
          mul_le_mul_of_nonneg_left hvM_sq (by positivity)
      _ = 6 * ((⌊x⌋₊ : ℝ) + 3 * (Q : ℝ) ^ 2) * x * Real.log x := by ring
  · -- Part 3: Bombieri–Vinogradov L¹ average for `ψ(x, quadCharNat q)`
    intro x hx3
    have hbv_x := hbv x hx3
    set Q := ⌊x ^ (1 / 2 : ℝ) / (Real.log x) ^ B⌋₊
    have hper_q : ∀ q ∈ (Finset.Icc 3 Q).filter Nat.Prime,
        (q.totient : ℝ)⁻¹ * ‖Stage2DirichletAP.chebyshevPsiChar (quadCharNat q) x‖ ≤
          Stage11BombieriVinogradov.psiAPMaxError q x := by
      intro q hq
      have hqp := (Finset.mem_filter.mp hq).2
      have hq3 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
      have : NeZero q := ⟨hqp.ne_zero⟩
      have hne1 : quadCharNat q ≠ 1 := quadCharNat_ne_one hqp (by omega)
      -- Express `ψ(x, χ) = ∑_{a : (ZMod q)ˣ} χ(a) * (ψ(x; q, a.val) - x / φ(q))`
      have horth : ∑ a : (ZMod q)ˣ, quadCharNat q (a : ZMod q) = 0 := by
        have hsum_all := MulChar.sum_eq_zero_of_ne_one hne1
        have hsplit : ∑ z : ZMod q, quadCharNat q z = ∑ a : (ZMod q)ˣ, quadCharNat q (a : ZMod q) := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun z : ZMod q => IsUnit z)]
          have hnon : ∑ z ∈ Finset.univ.filter (fun z : ZMod q => ¬ IsUnit z), quadCharNat q z = 0 :=
            Finset.sum_eq_zero fun z hz => MulChar.map_nonunit _ (Finset.mem_filter.mp hz).2
          rw [hnon, add_zero]
          refine (Finset.sum_bij (fun (a : (ZMod q)ˣ) _ => (a : ZMod q))
            (fun a _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, a.isUnit⟩)
            (fun a₁ _ a₂ _ h => Units.ext h)
            (fun z hz => by obtain ⟨u, rfl⟩ := (Finset.mem_filter.mp hz).2; exact ⟨u, Finset.mem_univ _, rfl⟩)
            (fun _ _ => rfl)).symm
        rw [← hsplit]; exact hsum_all
      have hdecomp :
          Stage2DirichletAP.chebyshevPsiChar (quadCharNat q) x =
            ∑ a : (ZMod q)ˣ, quadCharNat q (a : ZMod q) *
              ((Stage2DirichletAP.chebyshevPsiAP q (a : ZMod q).val x - x / (q.totient : ℝ) : ℝ) : ℂ) := by
        have hzero_sub :
            ∑ a : (ZMod q)ˣ, quadCharNat q (a : ZMod q) * ((x / (q.totient : ℝ) : ℝ) : ℂ) = 0 := by
          rw [← Finset.sum_mul, horth, zero_mul]
        have hsplit_sub :
            ∑ a : (ZMod q)ˣ, quadCharNat q (a : ZMod q) *
                ((Stage2DirichletAP.chebyshevPsiAP q (a : ZMod q).val x - x / (q.totient : ℝ) : ℝ) : ℂ) =
              (∑ a : (ZMod q)ˣ, quadCharNat q (a : ZMod q) * (Stage2DirichletAP.chebyshevPsiAP q (a : ZMod q).val x : ℂ)) -
              (∑ a : (ZMod q)ˣ, quadCharNat q (a : ZMod q) * ((x / (q.totient : ℝ) : ℝ) : ℂ)) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun a _ => by push_cast; ring
        rw [hsplit_sub, hzero_sub, sub_zero]
        unfold Stage2DirichletAP.chebyshevPsiChar Stage2DirichletAP.chebyshevPsiAP
        simp_rw [Complex.ofReal_sum, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun n _ => ?_
        by_cases hu : IsUnit (n : ZMod q)
        · obtain ⟨u, hu_eq⟩ := hu
          have hsingle : ∀ a : (ZMod q)ˣ,
              quadCharNat q (a : ZMod q) * (if n ≡ (a : ZMod q).val [MOD q] then (Λ n : ℝ) else 0 : ℂ) =
                if a = u then quadCharNat q (n : ZMod q) * (Λ n : ℂ) else 0 := by
            intro a
            have hiff : n ≡ (a : ZMod q).val [MOD q] ↔ a = u := by
              rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, ← hu_eq]
              exact ⟨fun h => Units.ext h.symm, fun h => by rw [h]⟩
            by_cases ha : a = u
            · rw [if_pos ha, if_pos (hiff.mpr ha), ha, hu_eq]
            · rw [if_neg ha, if_neg (fun h => ha (hiff.mp h)), mul_zero]
          have hcast_if : ∀ a : (ZMod q)ˣ,
              quadCharNat q (a : ZMod q) *
                  (((if n ≡ (a : ZMod q).val [MOD q] then Λ n else 0 : ℝ) : ℂ)) =
                if a = u then quadCharNat q (n : ZMod q) * (Λ n : ℂ) else 0 := by
            intro a; simpa [apply_ite] using hsingle a
          rw [Finset.sum_congr rfl (fun a _ => hcast_if a), Finset.sum_ite_eq' Finset.univ u,
            if_pos (Finset.mem_univ u)]
        · rw [MulChar.map_nonunit _ hu, zero_mul]
          symm
          refine Finset.sum_eq_zero fun a _ => ?_
          have hnot : ¬ n ≡ (a : ZMod q).val [MOD q] := by
            intro hmod
            have heq : (n : ZMod q) = (a : ZMod q) := by
              rw [← ZMod.natCast_zmod_val (a : ZMod q)]
              exact (ZMod.natCast_eq_natCast_iff n (a : ZMod q).val q).mpr hmod
            exact hu (heq ▸ a.isUnit)
          rw [if_neg hnot, Complex.ofReal_zero, mul_zero]
      have hnorm :
          ‖Stage2DirichletAP.chebyshevPsiChar (quadCharNat q) x‖ ≤
            (q.totient : ℝ) * Stage11BombieriVinogradov.psiAPMaxError q x := by
        rw [hdecomp]
        refine (norm_sum_le _ _).trans ?_
        have hterm : ∀ a : (ZMod q)ˣ,
            ‖quadCharNat q (a : ZMod q) *
              ((Stage2DirichletAP.chebyshevPsiAP q (a : ZMod q).val x - x / (q.totient : ℝ) : ℝ) : ℂ)‖ ≤
              Stage11BombieriVinogradov.psiAPMaxError q x := by
          intro a
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          have hχ1 : ‖quadCharNat q (a : ZMod q)‖ ≤ 1 := by
            have hval : (a : ZMod q) = (((a : ZMod q).val : ℕ) : ZMod q) := (ZMod.natCast_zmod_val _).symm
            rw [hval, quadCharNat_apply_nat hqp (by omega)]
            rcases jacobiSym.trichotomy ((a : ZMod q).val : ℤ) q with h | h | h
            · rw [h]; norm_num
            · rw [h]; norm_num
            · rw [h]; norm_num
          have hcop_a : Nat.Coprime (a : ZMod q).val q := by
            have hval : (((a : ZMod q).val : ℕ) : ZMod q) = (a : ZMod q) := ZMod.natCast_zmod_val _
            exact (ZMod.isUnit_iff_coprime _ q).mp (hval.symm ▸ a.isUnit)
          have herr := Stage11BombieriVinogradov.abs_chebyshevPsiAP_sub_le_psiAPMaxError hqp.pos hcop_a x
          calc ‖quadCharNat q (a : ZMod q)‖ * |Stage2DirichletAP.chebyshevPsiAP q (a : ZMod q).val x - x / (q.totient : ℝ)|
              ≤ 1 * Stage11BombieriVinogradov.psiAPMaxError q x :=
                mul_le_mul hχ1 herr (abs_nonneg _) zero_le_one
            _ = _ := one_mul _
        calc ∑ a : (ZMod q)ˣ, ‖quadCharNat q (a : ZMod q) *
                ((Stage2DirichletAP.chebyshevPsiAP q (a : ZMod q).val x - x / (q.totient : ℝ) : ℝ) : ℂ)‖
            ≤ ∑ _a : (ZMod q)ˣ, Stage11BombieriVinogradov.psiAPMaxError q x :=
              Finset.sum_le_sum fun a _ => hterm a
          _ = (Fintype.card (ZMod q)ˣ : ℝ) * Stage11BombieriVinogradov.psiAPMaxError q x := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          _ = (q.totient : ℝ) * Stage11BombieriVinogradov.psiAPMaxError q x := by
              rw [ZMod.card_units_eq_totient]
      have hphi_pos : (0 : ℝ) < (q.totient : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hqp.pos)
      calc (q.totient : ℝ)⁻¹ * ‖Stage2DirichletAP.chebyshevPsiChar (quadCharNat q) x‖
          ≤ (q.totient : ℝ)⁻¹ * ((q.totient : ℝ) * Stage11BombieriVinogradov.psiAPMaxError q x) :=
            mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hphi_pos.le)
        _ = Stage11BombieriVinogradov.psiAPMaxError q x := inv_mul_cancel_left₀ hphi_pos.ne' _
    have hsubQ : (Finset.Icc 3 Q).filter Nat.Prime ⊆ Finset.Icc 1 Q := fun q hq => by
      rw [Finset.mem_filter, Finset.mem_Icc] at hq; exact Finset.mem_Icc.mpr ⟨by omega, hq.1.2⟩
    have hLx_pos : 0 < Real.log x := Real.log_pos (by linarith)
    calc ∑ q ∈ (Finset.Icc 3 Q).filter Nat.Prime,
            (q.totient : ℝ)⁻¹ * ‖Stage2DirichletAP.chebyshevPsiChar (quadCharNat q) x‖
        ≤ ∑ q ∈ (Finset.Icc 3 Q).filter Nat.Prime, Stage11BombieriVinogradov.psiAPMaxError q x :=
          Finset.sum_le_sum hper_q
      _ ≤ ∑ q ∈ Finset.Icc 1 Q, Stage11BombieriVinogradov.psiAPMaxError q x :=
          Finset.sum_le_sum_of_subset_of_nonneg hsubQ (fun q _ _ => Stage11BombieriVinogradov.psiAPMaxError_nonneg q x)
      _ ≤ C₂ * x / (Real.log x) ^ A := hbv_x
      _ ≤ max C₁ C₂ * x / (Real.log x) ^ A := by
          gcongr; exact le_max_right _ _

/-! ### Unconditional Log-Free Zero-Density Box Bound (Directly from `Stage11LogFreeDensity`) -/

/-- Zero-free box `Re(s) > 1 - δ`, `|Im(s)| ≤ Q` for a Dirichlet character `ψ`. -/
def ZeroFreeBoxAt (δ Q : ℝ) {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) : Prop :=
  ∀ s : ℂ, 1 - δ < s.re → |s.im| ≤ Q → DirichletCharacter.LFunction ψ s ≠ 0

theorem zeroFreeBoxAt_eq_zeroFreeBox (Q : ℝ) {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) :
    ZeroFreeBoxAt (1 / 400) Q ψ ↔ ZeroDensityWindow.ZeroFreeBox Q ψ := Iff.rfl

/-- Zero-density box count hypothesis at gap `δ`: any finite family of primitive characters of
conductor `≤ Q` failing `ZeroFreeBoxAt δ Q` has cardinality `≤ C * Q ^ (1 / 4)`. -/
def ZeroDensityBoxBoundAt (δ C : ℝ) : Prop :=
  ∀ (Q : ℝ) (F : Finset (Σ k : ℕ, DirichletCharacter ℂ (k + 1))), 3 ≤ Q →
    (∀ p ∈ F, p.2.IsPrimitive ∧ ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧
      ∃ s : ℂ, 1 - δ < s.re ∧ |s.im| ≤ Q ∧ DirichletCharacter.LFunction p.2 s = 0) →
    (F.card : ℝ) ≤ C * Q ^ (1 / 4 : ℝ)

private lemma analyticOrderNatAt_LFunction_pos {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m)
    {ρ : ℂ} (_h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hzero : DirichletCharacter.LFunction χ ρ = 0) :
    1 ≤ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ := by
  have hρ_ne1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl 1 h1
  have hopen : IsOpen ({z : ℂ | z ≠ 1}) := isOpen_ne
  have hdiff : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) {z : ℂ | z ≠ 1} := fun z hz => by
    have hz1 : z ≠ 1 := hz
    exact (DirichletCharacter.differentiableAt_LFunction χ z (Or.inl hz1)).differentiableWithinAt
  have hanOn : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) {z : ℂ | z ≠ 1} :=
    hdiff.analyticOnNhd hopen
  have hanAt : AnalyticAt ℂ (DirichletCharacter.LFunction χ) ρ := hanOn ρ hρ_ne1
  have hconn : IsPreconnected ({z : ℂ | z ≠ 1}) := by
    have hrank : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
    exact (isConnected_compl_singleton_of_one_lt_rank hrank (1 : ℂ)).isPreconnected
  have hne_top : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ ⊤ := by
    intro htop
    have hev0 : DirichletCharacter.LFunction χ =ᶠ[𝓝 ρ] 0 := analyticOrderAt_eq_top.mp htop
    have heq0 := hanOn.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hρ_ne1 hev0
    have h2mem : (2 : ℂ) ∈ ({z : ℂ | z ≠ 1}) := by norm_num
    have hL2_zero : DirichletCharacter.LFunction χ 2 = 0 := heq0 h2mem
    have hL2_ne : DirichletCharacter.LFunction χ 2 ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num)) (by norm_num)
    exact hL2_ne hL2_zero
  have hne_zero : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ 0 := by
    intro h0_ord
    have hne : DirichletCharacter.LFunction χ ρ ≠ 0 := (hanAt.analyticOrderAt_eq_zero).mp h0_ord
    exact hne hzero
  have hpos_nat : analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ ≠ 0 := by
    intro hnat0
    unfold analyticOrderNatAt at hnat0
    rcases ENat.ne_top_iff_exists.mp hne_top with ⟨n, hn⟩
    rw [← hn] at hnat0 hne_zero
    rw [ENat.toNat_natCast] at hnat0
    subst hnat0
    exact hne_zero rfl
  omega

/-- **UNCONDITIONAL LOG-FREE ZERO-DENSITY BOX BOUND (DIRECTLY FROM `Stage11LogFreeDensity`)**:
there exist explicit `δ ∈ (0, 1/400]` and `C > 0` such that `ZeroDensityBoxBoundAt δ C` holds
unconditionally (`0` assumptions)! -/
theorem exists_zeroDensityBoxBoundAt_unconditional :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 / 400 ∧ 0 < C ∧ ZeroDensityBoxBoundAt δ C := by
  classical
  obtain ⟨C₀, hC₀, A₀, hA₀, hzd⟩ := Stage11LogFreeDensity.gallagher_logfree_zero_density_sum
  set δ : ℝ := min (1 / 400) (1 / (12 * A₀))
  have hδ_pos : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ_le400 : δ ≤ 1 / 400 := min_le_left _ _
  have hAδ : A₀ * δ ≤ 1 / 12 := by
    have h1 : δ ≤ 1 / (12 * A₀) := min_le_right _ _
    calc A₀ * δ ≤ A₀ * (1 / (12 * A₀)) := mul_le_mul_of_nonneg_left h1 hA₀.le
      _ = 1 / 12 := by field_simp [hA₀.ne']
  refine ⟨δ, 2 * C₀, hδ_pos, hδ_le400, by positivity, fun Q F hQ3 hF => ?_⟩
  set Qn : ℕ := ⌊Q⌋₊
  have hQn3 : 3 ≤ Qn := Nat.le_floor hQ3
  have hQn1 : 1 ≤ Qn := by omega
  have hQn_le : (Qn : ℝ) ≤ Q := Nat.floor_le (by linarith)
  have hzd_Q := hzd Qn hQn1 Q (by linarith) (1 - δ) (by linarith) (by linarith)
  have hF_le : (F.card : ℝ) ≤ (Stage11LogFreeDensity.primitiveZeroBoxCount Qn (1 - δ) Q : ℝ) := by
    suffices hnat : F.card ≤ Stage11LogFreeDensity.primitiveZeroBoxCount Qn (1 - δ) Q by exact_mod_cast hnat
    unfold Stage11LogFreeDensity.primitiveZeroBoxCount
    have hF_sub : F ⊆ (Finset.range Qn).sigma
        (fun k => Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive)) := by
      intro p hp
      obtain ⟨hprim, hcond, _⟩ := hF p hp
      rw [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter]
      have hp_le : p.1 + 1 ≤ Qn := Nat.le_floor hcond
      exact ⟨by omega, Finset.mem_univ _, hprim⟩
    have hcard_le : F.card ≤ ∑ p ∈ F, (Stage11LogFreeDensity.zerosOfLInBox p.2 (1 - δ) Q).card := by
      calc F.card = ∑ _p ∈ F, 1 := by simp
        _ ≤ ∑ p ∈ F, (Stage11LogFreeDensity.zerosOfLInBox p.2 (1 - δ) Q).card := by
            refine Finset.sum_le_sum fun p hp => ?_
            obtain ⟨_, _, s, hs_re, hs_im, hs_zero⟩ := hF p hp
            have hs_lt1 : s.re < 1 := by
              by_contra hge; push Not at hge
              have hne1 : p.2 ≠ 1 ∨ s ≠ 1 := by
                by_cases h1 : s = 1
                · subst h1
                  by_cases hχ1 : p.2 = 1
                  · exfalso
                    have hcond1 : p.1 + 1 = 1 := by
                      have hp_prim := (hF p hp).1
                      unfold DirichletCharacter.IsPrimitive at hp_prim
                      rw [hχ1, DirichletCharacter.conductor_one] at hp_prim
                      exact hp_prim.symm
                    have hL1 : DirichletCharacter.LFunction p.2 1 = riemannZeta 1 := by
                      have htriv : ∀ k (hk : k + 1 = 1) (χ : DirichletCharacter ℂ (k + 1)),
                          χ = 1 → DirichletCharacter.LFunction χ 1 = riemannZeta 1 := by
                        rintro k hk χ rfl
                        have hk0 : k = 0 := by omega
                        subst hk0; simp [DirichletCharacter.LFunction_modOne_eq]
                      exact htriv p.1 hcond1 p.2 hχ1
                    rw [hL1] at hs_zero
                    exact riemannZeta_one_ne_zero hs_zero
                  · exact Or.inl hχ1
                · exact Or.inr h1
              exact DirichletCharacter.LFunction_ne_zero_of_one_le_re p.2 hne1 hge hs_zero
            have hs_pos : 0 < s.re := by linarith
            rw [Stage11LogFreeDensity.zerosOfLInBox_card_eq_sum]
            have hmem : s ∈ (Stage11LogFreeDensity.finite_LFunction_zeros_in_box p.2 (1 - δ) Q).toFinset := by
              rw [Set.Finite.mem_toFinset]
              exact ⟨hs_pos, hs_re.le, hs_lt1, hs_im, hs_zero⟩
            exact (analyticOrderNatAt_LFunction_pos p.2 hs_pos hs_lt1 hs_zero).trans
              (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem)
    refine hcard_le.trans ?_
    calc ∑ p ∈ F, (Stage11LogFreeDensity.zerosOfLInBox p.2 (1 - δ) Q).card
        ≤ ∑ p ∈ (Finset.range Qn).sigma
            (fun k => Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive)),
            (Stage11LogFreeDensity.zerosOfLInBox p.2 (1 - δ) Q).card :=
          Finset.sum_le_sum_of_subset hF_sub
      _ = ∑ k ∈ Finset.range Qn,
            ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ (k + 1) => χ.IsPrimitive),
              (Stage11LogFreeDensity.zerosOfLInBox χ (1 - δ) Q).card :=
          Finset.sum_sigma _ _ _
  have hbase_le : (Qn : ℝ) ^ 2 * (Q + 2) ≤ 2 * Q ^ 3 := by
    have h1 : (Qn : ℝ) ^ 2 ≤ Q ^ 2 := by nlinarith
    have h2 : Q + 2 ≤ 2 * Q := by linarith
    nlinarith [sq_nonneg Q]
  have hbase_ge1 : (1 : ℝ) ≤ 2 * Q ^ 3 := by
    have hQ3_ge1 : (1 : ℝ) ≤ Q ^ 3 := one_le_pow₀ (by linarith)
    linarith
  have hrpow_le : ((Qn : ℝ) ^ 2 * (Q + 2)) ^ (A₀ * (1 - (1 - δ))) ≤ 2 * Q ^ (1 / 4 : ℝ) := by
    rw [show 1 - (1 - δ) = δ by ring]
    calc ((Qn : ℝ) ^ 2 * (Q + 2)) ^ (A₀ * δ)
        ≤ (2 * Q ^ 3) ^ (A₀ * δ) :=
          Real.rpow_le_rpow (by positivity) hbase_le (by positivity)
      _ ≤ (2 * Q ^ 3) ^ (1 / 12 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hbase_ge1 hAδ
      _ = (2 : ℝ) ^ (1 / 12 : ℝ) * (Q ^ 3) ^ (1 / 12 : ℝ) :=
          Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ 2 * Q ^ (1 / 4 : ℝ) := by
          have h2le : (2 : ℝ) ^ (1 / 12 : ℝ) ≤ 2 := by
            calc (2 : ℝ) ^ (1 / 12 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 2 := Real.rpow_one 2
          have hQpow : (Q ^ 3) ^ (1 / 12 : ℝ) = Q ^ (1 / 4 : ℝ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; congr 1; norm_num
          rw [hQpow]
          exact mul_le_mul_of_nonneg_right h2le (Real.rpow_nonneg (by linarith) _)
  calc (F.card : ℝ) ≤ C₀ * (((Qn : ℝ) ^ 2) * (Q + 2)) ^ (A₀ * (1 - (1 - δ))) := hF_le.trans hzd_Q
    _ ≤ C₀ * (2 * Q ^ (1 / 4 : ℝ)) := mul_le_mul_of_nonneg_left hrpow_le hC₀.le
    _ = (2 * C₀) * Q ^ (1 / 4 : ℝ) := by ring

private lemma sigma_of_not_zeroFreeBoxAt (δ Q : ℝ) (M : ℕ) [NeZero M]
    (ψ : DirichletCharacter ℂ M) (hp : ψ.IsPrimitive) (hM : (M : ℝ) ≤ Q)
    (hz : ¬ ZeroFreeBoxAt δ Q ψ) :
    ∃ p : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)),
      p.1 + 1 = M ∧ p.2.IsPrimitive ∧ ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧
      ∃ s : ℂ, 1 - δ < s.re ∧ |s.im| ≤ Q ∧ DirichletCharacter.LFunction p.2 s = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne M)
  refine ⟨⟨k, ψ⟩, rfl, hp, hM, ?_⟩
  unfold ZeroFreeBoxAt at hz; push Not at hz; exact hz

/-- Bad-prime counting at gap `δ` (analogue of `ZeroDensityWindow.count_bad_of_zeroDensityBox`). -/
theorem count_bad_primes_of_zeroDensityBoxAt {δ C : ℝ} (hZD : ZeroDensityBoxBoundAt δ C)
    (Q F : ℝ) (S : Finset ℕ) (hQ : 3 ≤ Q)
    (hS : ∀ q ∈ S, q.Prime ∧ F < (q : ℝ) ∧
      ∃ (f : ℕ) (_ : NeZero (f * q)) (ψ : DirichletCharacter ℂ (f * q)),
        (f : ℝ) ≤ F ∧ ((f * q : ℕ) : ℝ) ≤ Q ∧ ψ.IsPrimitive ∧ ¬ ZeroFreeBoxAt δ Q ψ) :
    (S.card : ℝ) ≤ max C 0 * Q ^ (1 / 4 : ℝ) := by
  classical
  have key : ∀ q : ℕ, ∃ p : (Σ k : ℕ, DirichletCharacter ℂ (k + 1)), q ∈ S →
      (∃ f : ℕ, p.1 + 1 = f * q ∧ (f : ℝ) ≤ F) ∧ p.2.IsPrimitive ∧ ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧
      ∃ s : ℂ, 1 - δ < s.re ∧ |s.im| ≤ Q ∧ DirichletCharacter.LFunction p.2 s = 0 := by
    intro q
    by_cases hq : q ∈ S
    · obtain ⟨-, -, f, hne, ψ, hf, hNQ, hp, hz⟩ := hS q hq
      obtain ⟨p, h1, h2⟩ := sigma_of_not_zeroFreeBoxAt δ Q (f * q) ψ hp hNQ hz
      exact ⟨p, fun _ => ⟨⟨f, h1, hf⟩, h2⟩⟩
    · exact ⟨⟨0, 1⟩, fun h => absurd h hq⟩
  choose g hg using key
  have hinj : Set.InjOn g S := by
    intro q hq q' hq' h
    obtain ⟨⟨f, hf, -⟩, -⟩ := hg q hq
    obtain ⟨⟨f', hf', hF'⟩, -⟩ := hg q' hq'
    have hpq := (hS q hq).1
    have hpq' := (hS q' hq').1
    have hlt := (hS q hq).2.1
    have he : f * q = f' * q' := by rw [← hf, ← hf', h]
    have hd : q ∣ f' * q' := ⟨f, by rw [← he, mul_comm]⟩
    rcases (Nat.Prime.dvd_mul hpq).1 hd with h1 | h1
    · have hpos : 0 < f' := by
        rcases Nat.eq_zero_or_pos f' with h0 | h0
        · rw [h0] at hf'; simp at hf'
        · exact h0
      have : (q : ℝ) ≤ f' := by exact_mod_cast Nat.le_of_dvd hpos h1
      linarith
    · exact (Nat.prime_dvd_prime_iff_eq hpq hpq').1 h1
  have h1 := hZD Q (S.image g) hQ (fun p hp => by
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
    exact (hg q hq).2)
  rw [Finset.card_image_of_injOn hinj] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _))

/-! ### Clean Bridges for M6 Wave 2 (`Stage14M6_PairGoodWired`) -/

/-- **Bridge 1 (Dense Good-Prime Extraction from `MeanSquareHypW`)**:
for any `ε ∈ (0, 1]` and `η ∈ (0, 1)`, combining `MeanSquareHypW ε C x₀` with Markov/Chebyshev
bad-set extraction (`ZeroDensityWindow.chebyshev_bad_card` + `share_of_bad`) yields a subset
`G ⊆ PPset m₀ a₀ X` of density `≥ 1 - η` on which EVERY prime `q ∈ G` satisfies the pointwise
quadratic-twist character-sum bound `‖∑_{n ≤ x^400} cN(x, n) κ(n) (n / q)‖ ≤ √(C / η * x * log x)`. -/
theorem quadTwist_good_prime_share_of_meanSquareHypW {ε C x₀ : ℝ}
    (hC : 0 < C) (hMS : MeanSquareHypW ε C x₀)
    {x X : ℝ} {m₀ a₀ : ℕ} {κ : ℕ → ℂ} (hx : max 3 x₀ ≤ x) (h8 : 8 ∣ m₀)
    (hsm : ∀ p : ℕ, p.Prime → p ∣ m₀ → (p : ℝ) ≤ x ^ (ε / 5) ∨ x ^ 400 < (p : ℝ))
    (hcop : a₀.Coprime m₀) (ha4 : a₀ % 4 = 3)
    (hm_le : (m₀ : ℝ) ≤ (Real.log X) ^ (1 / ε))
    (hXlo : x ^ (ε / 6) ≤ Real.log X) (hXhi : Real.log X ≤ x ^ (ε / 5) * Real.log x ^ 2)
    (hκ : ∀ n, ‖κ n‖ ≤ 1) (hκm : ∀ a b, κ (a * b) = κ a * κ b)
    {η : ℝ} (hη : 0 < η) :
    ∃ G ⊆ PPset m₀ a₀ X,
      X ^ (9 / 10 : ℝ) ≤ ((PPset m₀ a₀ X).card : ℝ) ∧
      (1 - η) * ((PPset m₀ a₀ X).card : ℝ) ≤ (G.card : ℝ) ∧
      ∀ q ∈ G,
        ‖∑ n ∈ Finset.Icc 1 ⌊x ^ 400⌋₊, ((cN x n : ℝ) : ℂ) * κ n * ((jacobiSym (n : ℤ) q : ℤ) : ℂ)‖ ≤
          Real.sqrt (C / η * x * Real.log x) := by
  have hx3 : 3 ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 < x := by linarith
  have hLx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have ⟨hcard, hms⟩ := hMS x X m₀ a₀ κ ((le_max_right _ _).trans hx) h8 hsm hcop ha4 hm_le hXlo hXhi hκ hκm
  set T : ℝ := Real.sqrt (C / η * x * Real.log x)
  have hT_pos : 0 < T := Real.sqrt_pos.mpr (by positivity)
  have hT_sq : T ^ 2 = C / η * x * Real.log x := Real.sq_sqrt (by positivity)
  set f : ℕ → ℝ := fun q =>
    ‖∑ n ∈ Finset.Icc 1 ⌊x ^ 400⌋₊, ((cN x n : ℝ) : ℂ) * κ n * ((jacobiSym (n : ℤ) q : ℤ) : ℂ)‖
  obtain ⟨G, hGsub, hGcard, hG⟩ := ZeroDensityWindow.share_of_bad (PPset m₀ a₀ X) (η := η)
    (fun q => f q ≤ T) (fun B hBP hBad => by
      have hch := ZeroDensityWindow.chebyshev_bad_card hBP f hT_pos hms (fun q hq => by
        have hgt : T < f q := lt_of_not_ge (hBad q hq)
        exact hgt.le.trans (le_abs_self _))
      have hdiv_eq : C * x * Real.log x / T ^ 2 = η := by
        rw [hT_sq]; field_simp [hC.ne', hη.ne', hx0.ne', hLx_pos.ne']
      rwa [hdiv_eq] at hch)
  exact ⟨G, hGsub, hcard, hGcard, hG⟩

/-- **Bridge 2 (Unconditional Coupled Zero-Free Box + Twisted `ψ` Mean-Square Prime Extraction)**:
combining `twisted_psi_mean_square_on_primes` + `exists_zeroDensityBoxBoundAt_unconditional` +
`count_bad_primes_of_zeroDensityBoxAt`, with ZERO hypotheses!
For every `A > 0`, there exist `δ ∈ (0, 1/400]` and `C, C_zd > 0` such that for every fixed
primitive character `ψ : PChar`, `x ≥ 16`, `Q : ℕ` with `3 ≤ ψ.N * Q ≤ x / 2`, and `δ_m ∈ (0, 1)`,
letting `P := (Finset.Icc 3 Q).filter (fun q => q.Prime ∧ ¬ q ∣ ψ.N ∧ ψ.N < q)` and
`E := C * (x * (ψ.N * Q) * (log x)³ + x² / (log x)^A)`, there exists `G ⊆ P` with
`(1 - δ_m) * |P| - C_zd * (ψ.N * Q)^(1/4) ≤ |G|` such that EVERY `q ∈ G` simultaneously satisfies:
1. quadratic-twist `ψ(x, ψ · (·/q))` bound `φ(ψ.N * q)⁻¹ ‖...‖² ≤ (2 * E) / (δ_m * |P|)`,
2. quadratic-twist Cesàro-1 bound `φ(ψ.N * q)⁻¹ ‖cesaroWindowPsiChar (ψ · (·/q)) x‖² ≤ (2 * E) / (δ_m * |P|)`,
3. unconditional zero-free box `ZeroFreeBoxAt δ (ψ.N * Q)` for EVERY primitive character of conductor `ψ.N * q`. -/
theorem quadTwist_coupled_good_primes_unconditional {A : ℝ} (hA : 0 < A) :
    ∃ δ C C_zd : ℝ, 0 < δ ∧ δ ≤ 1 / 400 ∧ 0 < C ∧ 0 < C_zd ∧
      ∀ (ψ : PChar) (x : ℝ), 16 ≤ x → ∀ Q : ℕ, 3 ≤ ((ψ.N * Q : ℕ) : ℝ) →
        ((ψ.N * Q : ℕ) : ℝ) ≤ x / 2 →
        ∀ δ_m : ℝ, 0 < δ_m → δ_m < 1 →
          let P := (Finset.Icc 3 Q).filter (fun q => q.Prime ∧ ¬ q ∣ ψ.N ∧ ψ.N < q)
          let E := C * (x * ((ψ.N * Q : ℕ) : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ A)
          ∃ G ⊆ P,
            (1 - δ_m) * (P.card : ℝ) - C_zd * ((ψ.N * Q : ℕ) : ℝ) ^ (1 / 4 : ℝ) ≤ (G.card : ℝ) ∧
            ∀ q ∈ G,
              (((ψ.N * q).totient : ℝ)⁻¹ *
                  ‖Stage2DirichletAP.chebyshevPsiChar (Stage11SecondMomentFrame.twistedChar ψ.χ (quadCharNat q)) x‖ ^ 2 ≤
                (2 * E) / (δ_m * (P.card : ℝ))) ∧
              (((ψ.N * q).totient : ℝ)⁻¹ *
                  ‖Stage11SecondMomentFrame.cesaroWindowPsiChar (Stage11SecondMomentFrame.twistedChar ψ.χ (quadCharNat q)) x‖ ^ 2 ≤
                (2 * E) / (δ_m * (P.card : ℝ))) ∧
              (∀ [NeZero (ψ.N * q)] (η : DirichletCharacter ℂ (ψ.N * q)),
                η.IsPrimitive → ZeroFreeBoxAt δ ((ψ.N * Q : ℕ) : ℝ) η) := by
  classical
  obtain ⟨δ, C_zd, hδ0, hδ400, hCzd, hZD⟩ := exists_zeroDensityBoxBoundAt_unconditional
  obtain ⟨_, C, _, hC, hms_all, _, _⟩ := twisted_psi_mean_square_on_primes hA
  refine ⟨δ, C, C_zd, hδ0, hδ400, hC, hCzd, fun ψ x hx Q hQ3 hQx δ_m hδm0 _hδm1 => ?_⟩
  dsimp only
  set P₀ := (Finset.Icc 3 Q).filter (fun q => q.Prime ∧ ¬ q ∣ ψ.N)
  set P := (Finset.Icc 3 Q).filter (fun q => q.Prime ∧ ¬ q ∣ ψ.N ∧ ψ.N < q)
  set E := C * (x * ((ψ.N * Q : ℕ) : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ A)
  have hP_sub : P ⊆ P₀ := fun q hq => by
    simp only [P, P₀, Finset.mem_filter] at hq ⊢; exact ⟨hq.1, hq.2.1, hq.2.2.1⟩
  by_cases hP : P = ∅
  · refine ⟨∅, Finset.empty_subset P, ?_, fun _ h => absurd h (Finset.notMem_empty _)⟩
    rw [hP, Finset.card_empty, Nat.cast_zero, mul_zero, zero_sub]
    linarith [mul_nonneg hCzd.le (Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) (ψ.N * Q)) (1 / 4 : ℝ))]
  · have hP_pos : (0 : ℝ) < (P.card : ℝ) :=
      Nat.cast_pos.mpr (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hP))
    have hLx_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hE_pos : 0 < E := by
      dsimp only [E]
      have h1 : 0 ≤ x * ((ψ.N * Q : ℕ) : ℝ) * (Real.log x) ^ 3 := by positivity
      have h2 : 0 < x ^ 2 / (Real.log x) ^ A := div_pos (by positivity) (Real.rpow_pos_of_pos hLx_pos A)
      exact mul_pos hC (by linarith)
    set M_psi : ℕ → ℝ := fun q =>
      ((ψ.N * q).totient : ℝ)⁻¹ *
        ‖Stage2DirichletAP.chebyshevPsiChar (Stage11SecondMomentFrame.twistedChar ψ.χ (quadCharNat q)) x‖ ^ 2
    set M_ces : ℕ → ℝ := fun q =>
      ((ψ.N * q).totient : ℝ)⁻¹ *
        ‖Stage11SecondMomentFrame.cesaroWindowPsiChar (Stage11SecondMomentFrame.twistedChar ψ.χ (quadCharNat q)) x‖ ^ 2
    have hM_psi_nn : ∀ q, 0 ≤ M_psi q := fun _ => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (sq_nonneg _)
    have hM_ces_nn : ∀ q, 0 ≤ M_ces q := fun _ => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (sq_nonneg _)
    have ⟨h1, h2⟩ := hms_all ψ x hx Q hQx
    have h1' : ∑ q ∈ P₀, M_psi q ≤ E := h1
    have h2' : ∑ q ∈ P₀, M_ces q ≤ E := h2
    have hsum_P : ∑ q ∈ P, (M_psi q + M_ces q) ≤ 2 * E := by
      have hsub_le : ∑ q ∈ P, (M_psi q + M_ces q) ≤ ∑ q ∈ P₀, (M_psi q + M_ces q) :=
        Finset.sum_le_sum_of_subset_of_nonneg hP_sub (fun q _ _ => add_nonneg (hM_psi_nn q) (hM_ces_nn q))
      rw [Finset.sum_add_distrib] at hsub_le
      have hP₀_eq : ∑ q ∈ P₀, (M_psi q + M_ces q) = ∑ q ∈ P₀, M_psi q + ∑ q ∈ P₀, M_ces q :=
        Finset.sum_add_distrib
      rw [hP₀_eq] at hsub_le
      linarith [Finset.sum_add_distrib (s := P) (f := M_psi) (g := M_ces)]
    set T : ℝ := (2 * E) / (δ_m * (P.card : ℝ))
    have hT_pos : 0 < T := div_pos (by linarith) (mul_pos hδm0 hP_pos)
    set BadMS := P.filter (fun q => T < M_psi q + M_ces q)
    set BadZF := P.filter (fun q =>
      ∃ (_ : NeZero (ψ.N * q)) (η : DirichletCharacter ℂ (ψ.N * q)),
        η.IsPrimitive ∧ ¬ ZeroFreeBoxAt δ ((ψ.N * Q : ℕ) : ℝ) η)
    have hBadMS_le : (BadMS.card : ℝ) ≤ δ_m * (P.card : ℝ) := by
      have hm : (BadMS.card : ℝ) * T ≤ 2 * E := by
        calc (BadMS.card : ℝ) * T = ∑ _q ∈ BadMS, T := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ∑ q ∈ BadMS, (M_psi q + M_ces q) := Finset.sum_le_sum fun q hq => (Finset.mem_filter.mp hq).2.le
          _ ≤ ∑ q ∈ P, (M_psi q + M_ces q) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun q _ _ => add_nonneg (hM_psi_nn q) (hM_ces_nn q))
          _ ≤ 2 * E := hsum_P
      have hmul : (BadMS.card : ℝ) * T ≤ (δ_m * (P.card : ℝ)) * T := by
        calc (BadMS.card : ℝ) * T ≤ 2 * E := hm
          _ = (δ_m * (P.card : ℝ)) * T := by dsimp only [T]; field_simp [hδm0.ne', hP_pos.ne']
      exact le_of_mul_le_mul_right hmul hT_pos
    have hBadZF_le : (BadZF.card : ℝ) ≤ C_zd * ((ψ.N * Q : ℕ) : ℝ) ^ (1 / 4 : ℝ) := by
      have h := count_bad_primes_of_zeroDensityBoxAt hZD ((ψ.N * Q : ℕ) : ℝ) (ψ.N : ℝ) BadZF hQ3 (fun q hq => by
        have hmem := Finset.mem_filter.mp hq
        have hqP := Finset.mem_filter.mp hmem.1
        obtain ⟨hne, η, hprim, hnz⟩ := hmem.2
        refine ⟨hqP.2.1, by exact_mod_cast hqP.2.2.2, ψ.N, hne, η, le_rfl, ?_, hprim, hnz⟩
        exact_mod_cast Nat.mul_le_mul_left ψ.N (Finset.mem_Icc.mp hqP.1).2)
      rwa [max_eq_left hCzd.le] at h
    set G := P \ (BadMS ∪ BadZF)
    have hG_card : (1 - δ_m) * (P.card : ℝ) - C_zd * ((ψ.N * Q : ℕ) : ℝ) ^ (1 / 4 : ℝ) ≤ (G.card : ℝ) := by
      have hsub_u : BadMS ∪ BadZF ⊆ P :=
        Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      have haddR : (G.card : ℝ) + ((BadMS ∪ BadZF).card : ℝ) = (P.card : ℝ) := by
        exact_mod_cast Finset.card_sdiff_add_card_eq_card hsub_u
      have hunionR : ((BadMS ∪ BadZF).card : ℝ) ≤ (BadMS.card : ℝ) + (BadZF.card : ℝ) := by
        exact_mod_cast Finset.card_union_le BadMS BadZF
      linarith
    refine ⟨G, Finset.sdiff_subset, hG_card, fun q hq => ?_⟩
    have hmem := Finset.mem_sdiff.mp hq
    have hms_le : M_psi q + M_ces q ≤ T := by
      by_contra hgt
      exact hmem.2 (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hmem.1, lt_of_not_ge hgt⟩))
    refine ⟨by linarith [hM_ces_nn q], by linarith [hM_psi_nn q], fun [hne : NeZero (ψ.N * q)] η hprim => ?_⟩
    by_contra hnz
    exact hmem.2 (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hmem.1, hne, η, hprim, hnz⟩))

/-- **Bridge 3 (Two-Stage Quadratic-Twist Prime-Pair Extraction for `Stage14M6_PairGoodWired`)**:
wraps `ZeroDensityWindow.pair_share_of_stages` for two-stage prime windows `(PP₁, q ↦ PP₂ q)`
where stage 1 selects `q ∈ PP₁` and stage 2 selects `d ∈ PP₂ q`. -/
theorem quadTwist_pair_good_stage_bridge (PP₁ : Finset ℕ) (PP₂ : ℕ → Finset ℕ)
    {η : ℝ} (Good₁ : ℕ → Prop) (Good₂ : ℕ → ℕ → Prop)
    (h1 : PP₁.Nonempty ∧ ∀ B ⊆ PP₁, (∀ q ∈ B, ¬ Good₁ q) → (B.card : ℝ) ≤ η * (PP₁.card : ℝ))
    (h2 : ∀ q ∈ PP₁, (PP₂ q).Nonempty ∧
      ∀ B ⊆ PP₂ q, (∀ d ∈ B, ¬ Good₂ q d) → (B.card : ℝ) ≤ η * ((PP₂ q).card : ℝ)) :
    ∃ G₁ ⊆ PP₁, 0 < PP₁.card ∧ (1 - η) * (PP₁.card : ℝ) ≤ (G₁.card : ℝ) ∧
      ∀ q ∈ G₁, Good₁ q ∧
        ∃ G₂ ⊆ PP₂ q, 0 < (PP₂ q).card ∧ (1 - η) * ((PP₂ q).card : ℝ) ≤ (G₂.card : ℝ) ∧
          ∀ d ∈ G₂, Good₂ q d :=
  ZeroDensityWindow.pair_share_of_stages PP₁ PP₂ Good₁ Good₂ h1 h2

/-- **MASTER UNCONDITIONAL STAGE 14 M6 WAVE-1 PACKAGE (`stage14M6_quadTwistMSq_master`)**:
simultaneously exports all four M6 Wave-1 deliverables (`0` assumptions, `0` `sorry`, `0` custom `axiom`s):
1. Unconditional `MeanSquareHypW` for every `ε ∈ (0, 1]` (`meanSquareHypW_of_bv_and_logfree`);
2. Unconditional Jacobi Pólya–Vinogradov + Multiplicative Large Sieve `L²` bounds (`abs_sum_jacobi_polya_vinogradov`, `jacobi_large_sieve_l2_bound`);
3. Unconditional twisted Chebyshev `ψ(x, χ)` mean-square & Bombieri–Vinogradov `L¹` bounds on odd primes (`twisted_psi_mean_square_on_primes`);
4. Unconditional log-free zero-density box bound `ZeroDensityBoxBoundAt δ C` (`exists_zeroDensityBoxBoundAt_unconditional`) feeding `Stage14M6_PairGoodWired`. -/
theorem stage14M6_quadTwistMSq_master :
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ C x₀ : ℝ, 0 < C ∧ 3 ≤ x₀ ∧ MeanSquareHypW ε C x₀) ∧
    (∀ {q : ℕ}, q.Prime → q ≠ 2 → ∀ N : ℕ,
      |∑ n ∈ Finset.Icc 1 N, (jacobiSym (n : ℤ) q : ℝ)| ≤ Real.sqrt (q : ℝ) * (1 + Real.log (q : ℝ))) ∧
    (∀ (Q M N : ℕ) (a : ℕ → ℂ),
      ∑ q ∈ (Finset.Icc 3 Q).filter Nat.Prime,
          ‖∑ n ∈ Finset.Ioc M (M + N), a n * ((jacobiSym (n : ℤ) q : ℤ) : ℂ)‖ ^ 2 ≤
        ((N : ℝ) + 3 * (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2) ∧
    (∀ A : ℝ, 0 < A → ∃ B C : ℝ, 0 < B ∧ 0 < C ∧
      (∀ (ψ : PChar) (x : ℝ), 16 ≤ x → ∀ Q : ℕ, ((ψ.N * Q : ℕ) : ℝ) ≤ x / 2 →
        let P := (Finset.Icc 3 Q).filter (fun q => q.Prime ∧ ¬ q ∣ ψ.N)
        (∑ q ∈ P, ((ψ.N * q).totient : ℝ)⁻¹ *
            ‖Stage2DirichletAP.chebyshevPsiChar (Stage11SecondMomentFrame.twistedChar ψ.χ (quadCharNat q)) x‖ ^ 2 ≤
          C * (x * ((ψ.N * Q : ℕ) : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ A)) ∧
        (∑ q ∈ P, ((ψ.N * q).totient : ℝ)⁻¹ *
            ‖Stage11SecondMomentFrame.cesaroWindowPsiChar (Stage11SecondMomentFrame.twistedChar ψ.χ (quadCharNat q)) x‖ ^ 2 ≤
          C * (x * ((ψ.N * Q : ℕ) : ℝ) * (Real.log x) ^ 3 + x ^ 2 / (Real.log x) ^ A))) ∧
      (∀ (Q : ℕ) (x : ℝ), 1 ≤ x →
        ∑ q ∈ (Finset.Icc 3 Q).filter Nat.Prime,
            ‖Stage2DirichletAP.chebyshevPsiChar (quadCharNat q) x‖ ^ 2 ≤
          6 * ((⌊x⌋₊ : ℝ) + 3 * (Q : ℝ) ^ 2) * x * Real.log x) ∧
      (∀ x : ℝ, 3 ≤ x →
        ∑ q ∈ (Finset.Icc 3 ⌊x ^ (1 / 2 : ℝ) / (Real.log x) ^ B⌋₊).filter Nat.Prime,
            (q.totient : ℝ)⁻¹ * ‖Stage2DirichletAP.chebyshevPsiChar (quadCharNat q) x‖ ≤
          C * x / (Real.log x) ^ A)) ∧
    (∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 / 400 ∧ 0 < C ∧ ZeroDensityBoxBoundAt δ C) :=
  ⟨fun _ hε hε1 => meanSquareHypW_of_bv_and_logfree hε hε1,
   fun hq hq2 N => abs_sum_jacobi_polya_vinogradov hq hq2 N,
   jacobi_large_sieve_l2_bound,
   fun _ hA => twisted_psi_mean_square_on_primes hA,
   exists_zeroDensityBoxBoundAt_unconditional⟩

end Stage14M6_QuadTwistMSq
end RHDirect

end
