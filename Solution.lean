import RHDirect.VinogradovThreePrimes
import RHDirect.ChenTheorem
import RHDirect.Stage11LinnikUnconditional
import RHDirect.DworkWeil1Unconditional
import RHDirect.GaussClassNumberUnconditional
import RHDirect.HasseMinkowskiGeneral
import RHDirect.CFT_HilbertClassField
import RHDirect.Stage9LandauSiegel
import RHDirect.Stage11HermitianCurvature
import RHDirect.MaynardTaoUnconditional
import MaynardDock.Capstone246
import Prize.PPL024_Main
import Prize.PPL086
import Prize.PPL176_Lower
import RHDirect.PPL031_HagerGaussSharp
import RHDirect.PPL173_Main
import RHDirect.PPL121_Main
import RHDirect.PPL042_Main
import RHDirect.PPL123_Main
import RHDirect.PPL124_Main
import RHDirect.PPL088_Main
import RHDirect.PPL133_Main
import RHDirect.Arith4Ext_AlgebraicMethod
import RHDirect.Arith4Ext_SieveCharacters
import RHDirect.Arith4Ext_SzemerediRegularity
import RHDirect.Arith4Ext_ConvexOptDuality
import RHDirect.Arith4Ext_SetSystemsCorrelation
import RHDirect.Arith4Ext_MeasureConvex
import RHDirect.Arith4Ext_RamseyCombinatorics
import RHDirect.Arith4Ext_TopologicalComb
import RHDirect.Arith4Ext_GeneratingFunctions
import RHDirect.Arith4Ext_ZetaLFunctions

open scoped TensorProduct

/-!
# Arithmetica4 — Unconditional Landmark Proofs (`Solution.lean`)

Discharges all 46 pure-Mathlib challenge theorems declared in `Challenge.lean`
unconditionally with `0` `sorry`, `0` custom axioms, and `0` `native_decide`.
-/

/-! ## 1. Vinogradov's Three-Primes Theorem (1937) -/

theorem vinogradov_three_primes :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Odd n →
      ∃ p₁ p₂ p₃ : ℕ, Nat.Prime p₁ ∧ Nat.Prime p₂ ∧ Nat.Prime p₃ ∧ p₁ + p₂ + p₃ = n :=
  RHDirect.Vinogradov.vinogradov_three_primes_unconditional

/-! ## 2. Chen's Theorem (1973) -/

theorem chen_theorem :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Even n →
      ∃ p q : ℕ, Nat.Prime p ∧
        (Nat.Prime q ∨ ∃ r s : ℕ, Nat.Prime r ∧ Nat.Prime s ∧ q = r * s) ∧
        p + q = n :=
  RHDirect.Chen.chen_theorem

/-! ## 3. Linnik's Least Prime in an Arithmetic Progression (1944) -/

theorem linnik_theorem :
    ∃ L : ℝ, 0 < L ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (m a : ℕ), 2 ≤ m → Nat.Coprime a m →
        ∃ p : ℕ, Nat.Prime p ∧ p ≡ a [MOD m] ∧ (p : ℝ) ≤ C * (m : ℝ) ^ L :=
  RHDirect.Stage11LinnikUnconditional.linnik_least_prime_in_ap_unconditional

/-! ## 4–6. Unconditional Bounded Prime Gaps (Polymath8b, H = 246) -/

theorem unconditional_prime_gap_le_246 :
    ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ p < q ∧ Nat.Prime p ∧ Nat.Prime q ∧ q - p ≤ 246 :=
  MaynardDock.unconditional_prime_gap_le_246

theorem bounded_prime_gaps_246_unconditional :
    ∃ H : ℕ, 0 < H ∧ H ≤ 246 ∧
      ∀ N : ℕ, ∃ p q : ℕ, N < p ∧ p < q ∧ Nat.Prime p ∧ Nat.Prime q ∧ q - p ≤ H :=
  MaynardDock.bounded_prime_gaps_246_unconditional

theorem frequently_consecutive_prime_gap_le_246 :
    Filter.Frequently (fun m : ℕ => Nat.nth Nat.Prime (m + 1) - Nat.nth Nat.Prime m ≤ 246)
      Filter.atTop :=
  MaynardDock.frequently_consecutive_prime_gap_le_246

/-! ## 6b. Maynard–Tao Arbitrary `m`-Tuples of Bounded Primes (2015) -/

theorem maynard_tao_m_tuples :
    ∀ m : ℕ, 1 ≤ m → ∃ H : ℕ, ∀ N : ℕ, ∃ S : Finset ℕ, S.card = m ∧
      (∀ p ∈ S, N ≤ p ∧ Nat.Prime p) ∧ ∀ p ∈ S, ∀ q ∈ S, p ≤ q + H :=
  RHDirect.MaynardTao.maynard_tao_m_tuples_unconditional

/-! ## 7. Dwork's Rationality Theorem (Weil Conjecture I, 1960) -/

theorem dwork_rationality
    (p r n : ℕ) [Fact p.Prime] (hr : 0 < r)
    (fs : Finset (MvPolynomial (Fin n) (GaloisField p r)))
    (φ : ∀ m : ℕ, 1 ≤ m → (GaloisField p r →+* GaloisField p (r * m))) :
    ∃ P Q : Polynomial ℚ, Q.coeff 0 = 1 ∧
      PowerSeries.subst
        (PowerSeries.mk fun m =>
          if hm : 1 ≤ m then
            (Nat.card {x : Fin n → GaloisField p (r * m) //
              ∀ f ∈ fs, MvPolynomial.eval₂ (φ m hm) x f = 0} : ℚ) / (m : ℚ)
          else 0)
        (PowerSeries.exp ℚ) * (Q : PowerSeries ℚ) = (P : PowerSeries ℚ) := by
  have hlog :
      (PowerSeries.mk fun m =>
        if hm : 1 ≤ m then
          (Nat.card {x : Fin n → GaloisField p (r * m) //
            ∀ f ∈ fs, MvPolynomial.eval₂ (φ m hm) x f = 0} : ℚ) / (m : ℚ)
        else 0) =
      PowerSeries.mk fun m =>
        if m = 0 then 0 else (RHDirect.DworkWeil1.affinePointCount p r fs m : ℚ) / (m : ℚ) := by
    congr 1
    funext m
    rcases m with _ | m
    · simp
    · have hm : 1 ≤ m + 1 := Nat.succ_pos m
      simp only [hm, ↓reduceDIte, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
      rw [RHDirect.DworkWeil1.affinePointCount_eq_galoisField hr fs hm (φ (m + 1) hm)]
  change ∃ P Q : Polynomial ℚ, Q.coeff 0 = 1 ∧
    RHDirect.DworkRat.expSeries (PowerSeries.mk fun m =>
      if hm : 1 ≤ m then
        (Nat.card {x : Fin n → GaloisField p (r * m) //
          ∀ f ∈ fs, MvPolynomial.eval₂ (φ m hm) x f = 0} : ℚ) / (m : ℚ)
      else 0) * (Q : PowerSeries ℚ) = (P : PowerSeries ℚ)
  rw [hlog]
  exact RHDirect.DworkWeil1.dwork_rationality_unconditional p r n hr fs

/-! ## 8. Gauss Class Number Problem (Heilbronn–Siegel, `h(ℚ(√(-d))) → ∞`) -/

theorem gauss_class_number_problem :
    ∀ M : ℕ, ∃ D₀ : ℕ, ∀ (d : ℕ)
      [Fact (Irreducible (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)))],
      D₀ ≤ d → Squarefree d →
      M ≤ NumberField.classNumber (AdjoinRoot (Polynomial.X ^ 2 + Polynomial.C (d : ℚ))) := by
  intro M
  obtain ⟨D₀, hD₀⟩ := RHDirect.GaussClassNumber.gauss_classNumber_problem_native_unconditional M
  refine ⟨max D₀ 1, fun d _ hd hsf => ?_⟩
  have hd_pos : 0 < d := lt_of_lt_of_le (by omega) ((le_max_right D₀ 1).trans hd)
  have h1 : M ≤ NumberField.classNumber (RHDirect.GaussClassNumber.ImagQuadField d) :=
    hD₀ d ((le_max_left D₀ 1).trans hd) hsf
  have he : RHDirect.GaussClassNumber.ImagQuadField d ≃ₐ[ℚ]
      AdjoinRoot (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)) :=
    RHDirect.GaussClassNumber.imagQuadField_equiv_adjoinRoot d hd_pos
  have hcg : ClassGroup (NumberField.RingOfIntegers (RHDirect.GaussClassNumber.ImagQuadField d)) ≃*
      ClassGroup (NumberField.RingOfIntegers (AdjoinRoot (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)))) :=
    ClassGroup.mulEquiv (NumberField.RingOfIntegers.mapRingEquiv he.toRingEquiv)
  have hcard : NumberField.classNumber (RHDirect.GaussClassNumber.ImagQuadField d) =
      NumberField.classNumber (AdjoinRoot (Polynomial.X ^ 2 + Polynomial.C (d : ℚ))) := by
    unfold NumberField.classNumber
    exact Fintype.card_congr hcg.toEquiv
  omega

/-! ## 9. General `n`-Variable Hasse–Minkowski Theorem over `ℚ` -/

theorem hasse_minkowski_general {n : ℕ} (Q : QuadraticForm ℚ (Fin n → ℚ))
    (hnd : Q.Nondegenerate) :
    (∃ v : Fin n → ℚ, v ≠ 0 ∧ Q v = 0) ↔
      (∃ v : ℝ ⊗[ℚ] (Fin n → ℚ), v ≠ 0 ∧ Q.baseChange ℝ v = 0) ∧
      (∀ p : ℕ, [Fact p.Prime] →
        ∃ v : ℚ_[p] ⊗[ℚ] (Fin n → ℚ), v ≠ 0 ∧ Q.baseChange ℚ_[p] v = 0) :=
  RHDirect.HasseMinkowskiGeneral.hasse_minkowski_general_Q Q hnd

/-! ## 10. Hilbert Class Field & Artin Reciprocity Isomorphism -/

section HilbertClassField
universe u

theorem hilbert_class_field_artin
    (K : Type u) [Field K] [NumberField K]
    (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] :
    ∃ H : IntermediateField K Ω,
      FiniteDimensional K H ∧ IsGalois K H ∧
      (∀ σ τ : H ≃ₐ[K] H, σ * τ = τ * σ) ∧
      Nonempty (ClassGroup (NumberField.RingOfIntegers K) ≃* (H ≃ₐ[K] H)) := by
  refine ⟨RHDirect.CFT.Global.hilbertClassField K Ω, inferInstance, inferInstance,
    fun σ τ => ?_, ⟨RHDirect.CFT.Global.hilbertClassFieldArtinEquiv K Ω⟩⟩
  exact (IsMulCommutative.is_comm (M := RHDirect.CFT.Global.hilbertClassField K Ω ≃ₐ[K]
    RHDirect.CFT.Global.hilbertClassField K Ω)).comm σ τ

end HilbertClassField

/-! ## 11. Siegel's `L(1, χ)` Lower Bound (`0` Exceptions) -/

theorem siegel_l1_lower_bound :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧
        ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
          χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
          C / (q : ℝ) ^ ε ≤ (DirichletCharacter.LFunction χ 1).re :=
  RHDirect.Stage9LandauSiegel.siegel_theorem_L1_lower_bound

/-! ## 12. Bochner–Kodaira–Nakano Negative-Weight Vanishing -/

theorem bochner_negative_weight_vanishing :
    (∀ {k : ℤ}, k < 0 →
      ∀ f : ModularForm (Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ).range k, f = 0) ∧
    (∀ {k : ℤ}, k < 0 →
      ∀ f : CuspForm (Matrix.SpecialLinearGroup.mapGL (R := ℤ) ℝ).range k, f = 0) :=
  ⟨fun hk f => RHDirect.Stage11HermitianCurvature.modularForm_eq_zero_of_weight_neg hk f,
   fun hk f => RHDirect.Stage11HermitianCurvature.cuspForm_eq_zero_of_weight_neg hk f⟩

/-! ## 13. Zhi-Wei Sun's Prime-Shifted Unit Fractions Conjecture (PPL 024, Bloom) -/

theorem sun_prime_shifted_unit_fractions (r : ℚ) (hr : 0 < r) (d : ℤ)
    (hd : d ∈ ({-1, 1} : Set ℤ)) :
    ∃ S : Finset ℕ, (∀ p ∈ S, Nat.Prime p) ∧
      r = ∑ p ∈ S, (1 : ℚ) / ((p : ℚ) + (d : ℚ)) :=
  PPL024.ppl024_sun_both r hr d hd

/-! ## 14. Benkoski–Erdős (1974) Positive Lower Density of Weird Numbers (PPL 086) -/

open Classical in
theorem weird_positive_lower_density :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * (N : ℝ) ≤ (((Finset.Icc 1 N).filter (fun n =>
        (0 < n ∧ 2 * n ≤ ∑ d ∈ n.divisors, d) ∧
        ¬ (0 < n ∧ ∃ S : Finset ℕ, S ⊆ n.properDivisors ∧ ∑ d ∈ S, d = n))).card : ℝ) := by
  obtain ⟨c, hc, N₀, hN⟩ := PPL086.weird_positive_lower_density
  refine ⟨c, hc, N₀, fun N h => ?_⟩
  have hcard : ((Finset.Icc 1 N).filter PPL086.IsWeird).card =
      ((Finset.Icc 1 N).filter (fun n =>
        (0 < n ∧ 2 * n ≤ ∑ d ∈ n.divisors, d) ∧
        ¬ (0 < n ∧ ∃ S : Finset ℕ, S ⊆ n.properDivisors ∧ ∑ d ∈ S, d = n))).card := by
    congr 1
    ext n
    simp only [Finset.mem_filter, PPL086.IsWeird, PPL086.IsAbundant, PPL086.IsPseudoperfect, PPL086.sigma]
  rw [← hcard]
  exact hN N h

/-! ## 15. Erdős #708 Split-Clique Lower Bound (PPL 176) -/

theorem erdos_708_split_clique_lower (n : ℕ) (hn : 1 ≤ n) :
    ∀ k : ℕ, (k : ℝ) < 2 * (n : ℝ) - Real.sqrt (6 * (n : ℝ)) - 2 →
      ¬ (∀ (A : Finset ℕ) (hA : A.Nonempty), (A.card = n ∧ ∀ a ∈ A, 2 ≤ a) →
        ∀ x : ℕ, ∃ B ⊆ Finset.Icc (x + 1) (x + A.max' hA),
          B.card ≤ k ∧ (∏ a ∈ A, a) ∣ (∏ b ∈ B, b)) := by
  simpa only [PPL176.SatisfiesBound, PPL176.IsValidSet, PPL176.consecInterval, PPL176.IsCover] using
    PPL176.erdos708_explicit_sqrt6_lower n hn

/-! ## 16–17. Hager's Sharper Gauss–Legendre & Radau Reverse-Markov Inequalities (PPL 031) -/

theorem hager_gauss_legendre_sharp
    (n : ℕ) (hn : 1 ≤ n)
    (P : Polynomial ℝ) (hPdeg : P.natDegree = n)
    (hPorth : ∀ q : Polynomial ℝ, q.natDegree < n →
      ∫ t in (-1 : ℝ)..1, P.eval t * q.eval t = 0)
    (τ : Fin n → ℝ) (hτmono : StrictMono τ) (hτroots : ∀ i : Fin n, P.eval (τ i) = 0)
    (p : Polynomial ℝ) (hpdeg : p.natDegree ≤ n) (hp_m1 : p.eval (-1) = 0)
    (hderiv : ∀ i : Fin n, |p.derivative.eval (τ i)| ≤ 1) :
    ∀ i : Fin n, |p.eval (τ i)| ≤ 1 + τ ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩ :=
  PPL031_HagerGaussSharp.hager_gauss_legendre_sharp_challenge
    n hn P hPdeg hPorth τ hτmono hτroots p hpdeg hp_m1 hderiv

theorem hager_radau_bound
    (n : ℕ) (hn : 1 ≤ n)
    (R : Polynomial ℝ) (hRdeg : R.natDegree = n) (hR1 : R.eval 1 = 0)
    (hRorth : ∀ q : Polynomial ℝ, q.natDegree < n - 1 →
      ∫ t in (-1 : ℝ)..1, R.eval t * q.eval t = 0)
    (τ : Fin n → ℝ) (hτmono : StrictMono τ) (hτroots : ∀ i : Fin n, R.eval (τ i) = 0)
    (p : Polynomial ℝ) (hpdeg : p.natDegree ≤ n) (hp_m1 : p.eval (-1) = 0)
    (hderiv : ∀ i : Fin n, |p.derivative.eval (τ i)| ≤ 1) :
    ∀ i : Fin n, |p.eval (τ i)| ≤ 2 :=
  PPL031_HagerGaussSharp.hager_radau_bound_challenge
    n hn R hRdeg hR1 hRorth τ hτmono hτroots p hpdeg hp_m1 hderiv

/-! ## 18–25. World-Record & Classical Quantitative Bounds (`PPL*` Milestones) -/

theorem erdos_711_upper_bound (n m : ℕ) (hn : 1 ≤ n) :
    ((sInf ({ L : ℕ | ∃ a : ℕ → ℕ,
      (∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → a i = a j → i = j) ∧
      (∀ k, 1 ≤ k → k ≤ n → m < a k ∧ a k < m + L ∧ k ∣ a k) } : Set ℕ) : ℕ) : ℝ)
      ≤ 13 * (n : ℝ) ^ ((10 : ℝ) / 7) + 2 :=
  PPL173.ppl173_world_record_rpow n m hn

theorem nfa_separating_words_bound {α : Type*} (w x : List α)
    (hlen : w.length = x.length) (hne : w ≠ x) (hn : 2 ≤ w.length) :
    ∃ (m : ℕ) (M : NFA α (Fin m)),
      ((w ∈ M.accepts ∧ x ∉ M.accepts) ∨ (x ∈ M.accepts ∧ w ∉ M.accepts)) ∧
      (m : ℝ) ≤ 128 * (w.length : ℝ) ^ ((1 : ℝ) / 3) * (Real.log (w.length : ℝ)) ^ ((2 : ℝ) / 3) :=
  PPL121.ppl090_nfa_separating_words_bound w x hlen hne hn

theorem ramsey_diagonal_exponential_improvement :
    ∃ L₀ : ℕ, ∀ k ≥ L₀,
      ((sInf {n : ℕ | ∀ G : SimpleGraph (Fin n), ¬(G.CliqueFree k ∧ Gᶜ.CliqueFree k)} : ℕ) : ℝ) ≤
        (399 / 100 : ℝ) ^ k :=
  PPL042.ppl042_diagonal_exponential_improvement

theorem roth_three_ap_quantitative :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ((sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
        (∀ a d : ℕ, 0 < d → ¬ ∀ i < 3, a + i * d ∈ A) ∧ A.card = m} : ℕ) : ℝ) ≤
        100 * (N : ℝ) / Real.log (Real.log (N : ℝ)) :=
  PPL123.roth_quantitative_upper_bound

theorem rankin_general_k_ap_free_lower (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (N : ℝ) * Real.exp (-C * (Real.log (N : ℝ)) ^ ((1 : ℝ) / (Nat.clog 2 k : ℝ))) ≤
        (sSup {m : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧
          (∀ a d : ℕ, 0 < d → ¬ ∀ i < k, a + i * d ∈ A) ∧ A.card = m} : ℕ) :=
  PPL123.rankin_general_k_lower_bound k hk

theorem ruzsa_1998_infinite_sidon :
    ∃ A : Set ℕ, A.Infinite ∧
      (∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ b₁ ∈ A, ∀ b₂ ∈ A,
        a₁ ≤ a₂ → b₁ ≤ b₂ → a₁ + a₂ = b₁ + b₂ → a₁ = b₁ ∧ a₂ = b₂) ∧
      ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (N : ℝ) ^ (Real.sqrt 2 - 1 - ε) ≤ ((A ∩ Set.Icc 1 N).ncard : ℝ) :=
  PPL124.ppl124_ruzsa_1998_world_record_sidon

theorem sidon_b3_upper_bound_beats_green :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in Filter.atTop,
      ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 N →
        (∀ m₁ m₂ : Multiset ℕ,
          m₁.card = 3 → m₂.card = 3 →
          (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
          m₁.sum = m₂.sum → m₁ = m₂) →
        (A.card : ℝ) ≤ (((699 / 200 : ℝ) ^ ((1 : ℝ) / 3)) + ε) * (N : ℝ) ^ ((1 : ℝ) / 3) :=
  PPL088.ppl088_b3_upper_bound_beats_green

theorem unitary_perfect_sharper_upper_bound (n : ℕ)
    (hn : ∑ d ∈ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ Nat.Coprime d (n / d)), d = n ∧ 0 < n)
    (hne90 : n ≠ 90) :
    n < 3 ^ (2 ^ (n.primeFactors.card - 1)) :=
  PPL133.sharper_upper_bound_ne_90 n hn hne90

/-! ## 26–45. `Arith4Ext_*` Tier A Combinatorial, Analytic & Topological Landmarks -/

theorem combinatorial_nullstellensatz {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] [IsDomain R] [DecidableEq R]
    (f : MvPolynomial ι R) (t : ι → ℕ) (S : ι → Finset R)
    (hdeg : f.totalDegree ≤ ∑ i : ι, t i)
    (hcoeff : f.coeff (∑ i : ι, t i • Finsupp.single i 1) ≠ 0)
    (hcard : ∀ i : ι, t i < (S i).card) :
    ∃ x : ι → R, (∀ i : ι, x i ∈ S i) ∧ MvPolynomial.eval x f ≠ 0 :=
  Arith4Ext.AlgebraicMethod.combinatorial_nullstellensatz f t S hdeg hcoeff hcard

theorem cauchy_davenport {p : ℕ} [Fact p.Prime] (A B : Finset (ZMod p))
    (hA : A.Nonempty) (hB : B.Nonempty) :
    min p (A.card + B.card - 1) ≤ ((A ×ˢ B).image (fun x => x.1 + x.2)).card :=
  Arith4Ext.AlgebraicMethod.cauchy_davenport A B hA hB

theorem chevalley_warning {p : ℕ} [Fact p.Prime] {n : ℕ}
    (fs : List (MvPolynomial (Fin n) (ZMod p)))
    (hdeg : (fs.map MvPolynomial.totalDegree).sum < n) :
    p ∣ (Finset.univ.filter (fun x : Fin n → ZMod p => ∀ f ∈ fs, MvPolynomial.eval x f = 0)).card :=
  Arith4Ext.AlgebraicMethod.chevalley_warning fs hdeg

theorem polya_vinogradov {q : ℕ} (hq : 2 ≤ q) [NeZero q]
    (χ : MulChar (ZMod q) ℂ) (hχ : DirichletCharacter.IsPrimitive χ) (M N : ℕ) :
    ‖∑ n ∈ Finset.Icc M (M + N - 1), χ (n : ZMod q)‖ ≤
      Real.sqrt (q : ℝ) * (Real.log (q : ℝ) + 1) :=
  Arith4Ext.SieveCharacters.polya_vinogradov hq χ hχ M N

theorem brun_titchmarsh_interval (M N : ℕ) (hN : 2 ≤ N) :
    (((Finset.Icc (M + 1) (M + N)).filter Nat.Prime).card : ℝ) ≤
      9 * (N : ℝ) / Real.log (N : ℝ) :=
  Arith4Ext.SieveCharacters.brun_titchmarsh_interval M N hN

theorem corners_theorem (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ A : Finset (ℕ × ℕ),
      A ⊆ Finset.range N ×ˢ Finset.range N →
      δ * (N : ℝ) ^ 2 ≤ (A.card : ℝ) →
      ∃ (x y x' y' : ℕ), (x, y) ∈ A ∧ (x', y) ∈ A ∧ (x, y') ∈ A ∧
        x' ≠ x ∧ (x' : ℤ) - (x : ℤ) = (y' : ℤ) - (y : ℤ) :=
  Arith4Ext.SzemerediRegularity.corners_theorem_via_removal δ hδ

section ConvexOpt
open scoped Matrix

theorem farkas_lemma {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (∃ x : Fin n → ℝ, (∀ j, 0 ≤ x j) ∧ A.mulVec x = b) ↔
      ¬ (∃ y : Fin m → ℝ, (∀ j, 0 ≤ (Aᵀ.mulVec y) j) ∧ y ⬝ᵥ b < 0) :=
  Arith4Ext.ConvexOptDuality.farkas_lemma A b

theorem von_neumann_minimax {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ vStar : ℝ,
      (∃ pStar : Fin m → ℝ, (∀ i, 0 ≤ pStar i) ∧ ∑ i, pStar i = 1 ∧
        ∀ q : Fin n → ℝ, (∀ j, 0 ≤ q j) → ∑ j, q j = 1 → vStar ≤ pStar ⬝ᵥ A.mulVec q) ∧
      (∃ qStar : Fin n → ℝ, (∀ j, 0 ≤ qStar j) ∧ ∑ j, qStar j = 1 ∧
        ∀ p : Fin m → ℝ, (∀ i, 0 ≤ p i) → ∑ i, p i = 1 → p ⬝ᵥ A.mulVec qStar ≤ vStar) :=
  Arith4Ext.ConvexOptDuality.von_neumann_minimax_value hm hn A

theorem birkhoff_von_neumann {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hnonneg : ∀ i j, 0 ≤ M i j)
    (hrow : ∀ i, ∑ j : Fin n, M i j = 1)
    (hcol : ∀ j, ∑ i : Fin n, M i j = 1) :
    ∃ w : Equiv.Perm (Fin n) → ℝ,
      (∀ σ, 0 ≤ w σ) ∧ (∑ σ : Equiv.Perm (Fin n), w σ = 1) ∧
        M = ∑ σ : Equiv.Perm (Fin n), w σ • Matrix.of (fun i j => if σ i = j then (1 : ℝ) else 0) :=
  Arith4Ext.ConvexOptDuality.birkhoff_von_neumann M hnonneg hrow hcol

end ConvexOpt

theorem dilworth_theorem {P : Type*} [PartialOrder P] [DecidableEq P] (S : Finset P) :
    ∃ k : ℕ,
      (∃ U ⊆ S, IsAntichain (· ≤ ·) (U : Set P) ∧ U.card = k) ∧
      (∀ U ⊆ S, IsAntichain (· ≤ ·) (U : Set P) → U.card ≤ k) ∧
      (∃ 𝒞 : Finset (Finset P), 𝒞.card ≤ k ∧
        (∀ C ∈ 𝒞, IsChain (· ≤ ·) (C : Set P)) ∧ S ⊆ 𝒞.biUnion id) :=
  Arith4Ext.ConvexOptDuality.dilworth_theorem S

theorem sperner_theorem {n : ℕ} (ℱ : Finset (Finset (Fin n)))
    (hAnti : ∀ A ∈ ℱ, ∀ B ∈ ℱ, A ⊆ B → A = B) :
    ℱ.card ≤ Nat.choose n (n / 2) :=
  Arith4Ext.SetSystemsCorrelation.sperner_theorem ℱ hAnti

theorem erdos_ko_rado {n k : ℕ} (hk : 1 ≤ k) (hkn : 2 * k ≤ n)
    (ℱ : Finset (Finset (Fin n)))
    (hunif : ∀ A ∈ ℱ, A.card = k)
    (hinter : ∀ A ∈ ℱ, ∀ B ∈ ℱ, ¬ Disjoint A B) :
    ℱ.card ≤ Nat.choose (n - 1) (k - 1) :=
  Arith4Ext.SetSystemsCorrelation.erdos_ko_rado hk hkn ℱ hunif hinter

theorem sauer_shelah {n d : ℕ} (ℱ : Finset (Finset (Fin n)))
    (hno : ∀ S : Finset (Fin n), d < S.card →
      ¬ (∀ T ⊆ S, ∃ A ∈ ℱ, A ∩ S = T)) :
    ℱ.card ≤ ∑ k ∈ Finset.range (d + 1), Nat.choose n k :=
  Arith4Ext.SetSystemsCorrelation.sauer_shelah ℱ hno

open scoped Pointwise in
theorem brunn_minkowski_1d {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hneA : A.Nonempty) (hneB : B.Nonempty) :
    MeasureTheory.volume A + MeasureTheory.volume B ≤ MeasureTheory.volume (A + B) :=
  Arith4Ext.MeasureConvex.brunn_minkowski_1d hA hB hneA hneB

theorem van_der_waerden_theorem (k r : ℕ) (hk : 1 ≤ k) (hr : 1 ≤ r) :
    ∃ N : ℕ, ∀ (c : ℕ → Fin r),
      ∃ (a d : ℕ), 0 < d ∧ a + (k - 1) * d < N ∧
        ∃ col : Fin r, ∀ j : Fin k, c (a + j.1 * d) = col :=
  Arith4Ext.RamseyCombinatorics.van_der_waerden_theorem k r hk hr

theorem schur_theorem {r N : ℕ} (hr : 1 ≤ r) (hN : 3 * Nat.factorial r - 1 ≤ N)
    (c : ℕ → Fin r) :
    ∃ x y z : ℕ, 1 ≤ x ∧ 1 ≤ y ∧ z ≤ N ∧ x + y = z ∧ c x = c y ∧ c y = c z :=
  Arith4Ext.RamseyCombinatorics.schur_theorem hr hN c

theorem brouwer_fixed_point_simplex (d : ℕ)
    (f : (Fin (d + 1) → ℝ) → (Fin (d + 1) → ℝ))
    (hf_cont : ContinuousOn f {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1})
    (hf_maps : Set.MapsTo f {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}
      {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}) :
    ∃ x : Fin (d + 1) → ℝ, (∀ i, 0 ≤ x i) ∧ (∑ i, x i = 1) ∧ f x = x :=
  Arith4Ext.TopologicalComb.brouwer_fixed_point_simplex d f hf_cont hf_maps

theorem kneser_no_coloring_lt (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (col : Finset (Fin n) → Fin (n - 2 * k + 1)) :
    ¬ ∀ A B : Finset (Fin n), A.card = k → B.card = k → Disjoint A B → col A ≠ col B :=
  Arith4Ext.TopologicalComb.kneser_no_coloring_lt n k hk hn col

theorem stirling_factorial_bounds (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (2 * Real.pi * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n *
        Real.exp (1 / (12 * (n : ℝ) + 1)) ≤ (n.factorial : ℝ) ∧
      (n.factorial : ℝ) ≤
        Real.sqrt (2 * Real.pi * (n : ℝ)) * ((n : ℝ) / Real.exp 1) ^ n *
          Real.exp (1 / (12 * (n : ℝ))) :=
  Arith4Ext.GeneratingFunctions.stirling_factorial_bounds n hn

theorem riemannZeta_ne_zero_on_re_one (t : ℝ) :
    riemannZeta (1 + (t : ℂ) * Complex.I) ≠ 0 :=
  Arith4Ext.ZetaLFunctions.riemannZeta_ne_zero_on_re_one t
