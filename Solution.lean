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

open scoped TensorProduct

/-!
# Arithmetica4 — Unconditional Landmark Proofs (`Solution.lean`)

Discharges all 12 pure-Mathlib challenge theorems declared in `Challenge.lean`
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
