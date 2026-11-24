import RHDirect.Stage4ClassFieldTheory
import RHDirect.Stage5DirichletDensity
import RHDirect.Stage5ZetaZeroFree
import RHDirect.Stage6ClassNumberFormula
import RHDirect.Stage7DedekindZeta
import RHDirect.Stage7PNTInAP
import RHDirect.Stage8ExplicitPrimeBounds
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# RHDirect.Stage9CyclotomicChebotarev

**UNCONDITIONAL EFFECTIVE CYCLOTOMIC CHEBOTAREV DENSITY THEOREM WITH `exp(-c √(log x))` ERROR,
EFFECTIVE CYCLOTOMIC DEDEKIND ZETA ZERO-FREE REGION, & EFFECTIVE PRIME IDEAL THEOREM IN `ℚ(ζ_q)`**
(`0` assumptions, `0` `sorry`, `0` custom `axiom`s) in pure Mathlib `v4.33.1`.

## Main Contents
1. **Unconditional Cyclotomic Dedekind Zeta Analytic Continuation, Simple Pole Positive Real
   Residue, & De La Vallée Poussin Zero-Free Region**:
   - `cyclotomicDedekindZeta q s := ∏ χ : DirichletCharacter ℂ q, DirichletCharacter.LFunction χ s`,
     identified with the exact unramified Euler product of `Stage7DedekindZeta` on `Re(s) > 1`
     (and matching the full `dedekindZeta (CycField q) s` up to the finite ramified product `v ∣ q`).
   - `cyclotomicDedekindZeta_meromorphic` & `cyclotomicDedekindZeta_residue_one`: holomorphic on
     `ℂ \ {1}`, entire regularization `cyclotomicDedekindZetaReg q` extending `(s - 1) ζ_{ℚ(ζ_q)}(s)`
     across `s = 1`, and exact strictly positive real residue
     `lim_{s → 1} (s - 1) * cyclotomicDedekindZeta q s = (∏_{p ∣ q} (1 - p⁻¹)) * ∏_{χ ≠ 1} L(1, χ) > 0`.
   - `cyclotomicDedekindZeta_zeroFree`, `cyclotomicDedekindZetaReg_zeroFree`, and
     `cyclotomicDedekindZeta_primitive_zeroFree`: unconditional de la Vallée Poussin zero-free
     region `1 - c / Real.log (|s.im| + 2) ≤ s.re` combining
     `Stage5ZetaZeroFree.riemannZeta_deLaValleePoussin_zeroFree` and
     `Stage8ExplicitPrimeBounds.LFunction_deLaValleePoussin_zeroFree_fixed_char`.
2. **Unconditional Effective Cyclotomic Chebotarev Density Theorem (`0` Assumptions!)**:
   - Frobenius prime-counting functions `chebotarevPsi q σ x`, `chebotarevTheta q σ x`, and
     `chebotarevPi q σ x` for any `σ ∈ Gal(ℚ(ζ_q)/ℚ)`.
   - `effective_cyclotomic_chebotarev_psi` & `effective_cyclotomic_chebotarev_theta`:
     `|chebotarevPsi q σ x - x / |Gal(ℚ(ζ_q)/ℚ)|| ≤ C * x * exp(-c √(log x))` and
     `|chebotarevTheta q σ x - x / |Gal(ℚ(ζ_q)/ℚ)|| ≤ C * x * exp(-c √(log x))`.
   - `effective_cyclotomic_chebotarev_pi_asymp`: exact natural density
     `chebotarevPi q σ n / Nat.primeCounting n → 1 / |Gal(ℚ(ζ_q)/ℚ)|`, upgrading
     `Stage5DirichletDensity` from Dirichlet density to effective natural density.
   - `effective_abelian_subfield_splitting`: for every subgroup `H ≤ (ZMod q)ˣ` (corresponding to
     the abelian subfield `K = ℚ(ζ_q)^H` of degree `[K : ℚ] = [(ZMod q)ˣ : H]`), exact natural
     splitting density `1 / [K : ℚ]` and `exp(-c √(log x))` error bounds for `ψ_split` and `θ_split`.
   - `effective_kronecker_bauer_abelian`: two subgroups `H₁, H₂ ≤ (ZMod q)ˣ` have the same
     splitting prime set up to a set of natural density `0` iff `H₁ = H₂` (and the same for
     arbitrary intermediate fields `K₁, K₂ : IntermediateField ℚ (CycField q)`).
3. **Unconditional Effective Prime Ideal Theorem for `ℚ(ζ_q)`**:
   - Concrete prime-ideal Chebyshev function `primeIdealTheta (CycField q) x = ∑_{N(𝔭) ≤ x} log N(𝔭)`
     and prime-ideal counting function `primeIdealPi (CycField q) x = #{𝔭 | N(𝔭) ≤ x}` on Mathlib's
     actual `HeightOneSpectrum (𝓞 (CyclotomicField q ℚ))` and `Ideal.absNorm`.
   - `effective_prime_ideal_theorem_cyclotomic`:
     `|primeIdealTheta (CycField q) x - x| ≤ C * x * exp(-c √(log x))` AND
     `primeIdealPi (CycField q) x / (x / Real.log x) → 1`.

Zero `sorry`, zero custom `axiom`s.
-/

noncomputable section

open Complex DirichletCharacter Filter Finset MeasureTheory NumberField IsDedekindDomain Set Topology
open RHDirect.Stage2DirichletAP RHDirect.Stage4ClassFieldTheory RHDirect.Stage5DirichletDensity
open RHDirect.Stage6ClassNumberFormula RHDirect.Stage7DedekindZeta RHDirect.Stage7PNTInAP
open RHDirect.Stage8ExplicitPrimeBounds
open scoped ArithmeticFunction.vonMangoldt BigOperators NumberField

namespace RHDirect.Stage9CyclotomicChebotarev

/-! ## Section 1: Analytic Continuation, Positive Real Residue & De La Vallée Poussin Zero-Free Region of `ζ_{ℚ(ζ_q)}(s)` -/

section CyclotomicDedekindZeta

/-- The analytic continuation of the (unramified-at-`q`) cyclotomic Dedekind zeta function
`ζ_{ℚ(ζ_q)}(s) = ∏_{χ mod q} L(s, χ)` defined on all of `ℂ`. -/
def cyclotomicDedekindZeta (q : ℕ) [NeZero q] (s : ℂ) : ℂ :=
  ∏ χ : DirichletCharacter ℂ q, DirichletCharacter.LFunction χ s

open Classical in
/-- Exact residue of `cyclotomicDedekindZeta q` at its simple pole `s = 1`:
`(∏_{p ∣ q} (1 - p⁻¹)) * ∏_{χ ≠ 1} L(1, χ)`. -/
def cyclotomicDedekindZetaResidue (q : ℕ) [NeZero q] : ℂ :=
  (∏ p ∈ q.primeFactors, (1 - ((p : ℂ))⁻¹)) *
    ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), DirichletCharacter.LFunction χ 1

/-- Holomorphic regularization `(s - 1) * cyclotomicDedekindZeta q s` extended across `s = 1`
by its exact residue `cyclotomicDedekindZetaResidue q`. -/
def cyclotomicDedekindZetaReg (q : ℕ) [NeZero q] : ℂ → ℂ :=
  Function.update (fun s => (s - 1) * cyclotomicDedekindZeta q s) 1
    (cyclotomicDedekindZetaResidue q)

/-- On `Re(s) > 1`, `cyclotomicDedekindZeta q s` equals the exact unramified Dedekind Euler
product over all height-one prime ideals of `𝓞 (CyclotomicField q ℚ)` not lying over `q`. -/
theorem cyclotomicDedekindZeta_eq_unramified_eulerProduct (q : ℕ) [NeZero q] {s : ℂ}
    (hs : 1 < s.re) :
    cyclotomicDedekindZeta q s =
      ∏' v : {v : HeightOneSpectrum (𝓞 (CycField q)) // ¬ ((Ideal.absNorm v.asIdeal).minFac ∣ q)},
        (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹ :=
  (Stage7DedekindZeta.cyc_unramified_tprod_eq_prod_dirichletLFunction q hs).symm

/-- On `Re(s) > 1`, the full concrete Dedekind zeta function `Stage7DedekindZeta.dedekindZeta (CycField q) s`
equals the finite product of ramified Euler factors at `v ∣ q` times `cyclotomicDedekindZeta q s`. -/
theorem dedekindZeta_cyclotomic_eq_ramified_mul (q : ℕ) [NeZero q] {s : ℂ} (hs : 1 < s.re) :
    Stage7DedekindZeta.dedekindZeta (CycField q) s =
      (∏' v : {v : HeightOneSpectrum (𝓞 (CycField q)) // (Ideal.absNorm v.asIdeal).minFac ∣ q},
        (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-s))⁻¹) *
      cyclotomicDedekindZeta q s :=
  Stage7DedekindZeta.cyc_dedekindZeta_eq_ramified_mul_prod_dirichletLFunction q hs

/-- `cyclotomicDedekindZeta q` is complex-differentiable at every `s ≠ 1`. -/
theorem cyclotomicDedekindZeta_differentiableAt (q : ℕ) [NeZero q] {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (cyclotomicDedekindZeta q) s := by
  unfold cyclotomicDedekindZeta
  have h := DifferentiableAt.finsetProd (u := Finset.univ)
    (f := fun (χ : DirichletCharacter ℂ q) z => DirichletCharacter.LFunction χ z)
    fun χ _ => DirichletCharacter.differentiableAt_LFunction χ s (Or.inl hs)
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => by simp [Finset.prod_apply])

/-- `cyclotomicDedekindZeta q` is holomorphic on `ℂ \ {1}`. -/
theorem cyclotomicDedekindZeta_differentiableOn (q : ℕ) [NeZero q] :
    DifferentiableOn ℂ (cyclotomicDedekindZeta q) ({1}ᶜ) := fun _ hs =>
  (cyclotomicDedekindZeta_differentiableAt q (Set.mem_compl_singleton_iff.mp hs)).differentiableWithinAt

/-- For every real `σ > 1`, `cyclotomicDedekindZeta q (σ : ℂ)` is strictly positive real
(`0 < re` and `im = 0`). -/
theorem cyclotomicDedekindZeta_real_pos (q : ℕ) [NeZero q] {σ : ℝ} (hσ : 1 < σ) :
    0 < (cyclotomicDedekindZeta q (σ : ℂ)).re ∧ (cyclotomicDedekindZeta q (σ : ℂ)).im = 0 := by
  have hs : (1 : ℝ) < ((σ : ℂ)).re := by simpa using hσ
  have hhp1 := Stage7DedekindZeta.cyc_unramified_hasProd_eq_prod_dirichletLFunction q hs
  have hhp2 := Stage7DedekindZeta.hasProd_eulerProduct_subtype_exp_neg_log (CycField q)
    (fun v => ¬ ((Ideal.absNorm v.asIdeal).minFac ∣ q)) hs
  have heq : cyclotomicDedekindZeta q (σ : ℂ) =
      Complex.exp (∑' v : {v : HeightOneSpectrum (𝓞 (CycField q)) //
        ¬ ((Ideal.absNorm v.asIdeal).minFac ∣ q)},
        -Complex.log (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-(σ : ℂ)))) :=
    hhp1.unique hhp2
  have hterm : ∀ v : {v : HeightOneSpectrum (𝓞 (CycField q)) //
      ¬ ((Ideal.absNorm v.asIdeal).minFac ∣ q)},
      -Complex.log (1 - (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-(σ : ℂ))) =
        ((-Real.log (1 - (Ideal.absNorm v.1.asIdeal : ℝ) ^ (-σ)) : ℝ) : ℂ) := by
    intro v
    have hgt : 1 < Ideal.absNorm v.1.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v.1
    have hgtR : (1 : ℝ) < (Ideal.absNorm v.1.asIdeal : ℝ) := by exact_mod_cast hgt
    have hposR : (0 : ℝ) < (Ideal.absNorm v.1.asIdeal : ℝ) := zero_lt_one.trans hgtR
    have hrpow_lt : (Ideal.absNorm v.1.asIdeal : ℝ) ^ (-σ) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hgtR (by linarith)
    have hsub_pos : 0 < 1 - (Ideal.absNorm v.1.asIdeal : ℝ) ^ (-σ) := by linarith
    have hcpow : (Ideal.absNorm v.1.asIdeal : ℂ) ^ (-(σ : ℂ)) =
        (((Ideal.absNorm v.1.asIdeal : ℝ) ^ (-σ) : ℝ) : ℂ) := by
      rw [show (-(σ : ℂ)) = ((-σ : ℝ) : ℂ) by simp, Complex.ofReal_cpow hposR.le]
      simp
    rw [hcpow, show (1 : ℂ) - (((Ideal.absNorm v.1.asIdeal : ℝ) ^ (-σ) : ℝ) : ℂ) =
      ((1 - (Ideal.absNorm v.1.asIdeal : ℝ) ^ (-σ) : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_log hsub_pos.le, Complex.ofReal_neg]
  rw [heq]
  simp_rw [hterm]
  rw [← Complex.ofReal_tsum, ← Complex.ofReal_exp, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨Real.exp_pos _, rfl⟩

/-- **Exact Simple-Pole Positive Real Residue Theorem for `ζ_{ℚ(ζ_q)}(s)` at `s = 1`**:
`lim_{s → 1, s ≠ 1} (s - 1) * cyclotomicDedekindZeta q s = cyclotomicDedekindZetaResidue q`,
and the residue is strictly positive real (`0 < re`, `im = 0`, hence `≠ 0`). -/
theorem cyclotomicDedekindZeta_residue_one (q : ℕ) [NeZero q] :
    Tendsto (fun s : ℂ => (s - 1) * cyclotomicDedekindZeta q s) (𝓝[≠] (1 : ℂ))
      (𝓝 (cyclotomicDedekindZetaResidue q)) ∧
    0 < (cyclotomicDedekindZetaResidue q).re ∧
    (cyclotomicDedekindZetaResidue q).im = 0 ∧
    cyclotomicDedekindZetaResidue q ≠ 0 := by
  obtain ⟨htend, hne⟩ := Stage6ClassNumberFormula.prod_dirichletLFunction_residue_one q
  change Tendsto (fun s : ℂ => (s - 1) * cyclotomicDedekindZeta q s) (𝓝[≠] (1 : ℂ))
      (𝓝 (cyclotomicDedekindZetaResidue q)) at htend
  change cyclotomicDedekindZetaResidue q ≠ 0 at hne
  have hmaps : Tendsto (fun σ : ℝ => (σ : ℂ)) (nhdsWithin 1 (Set.Ioi 1)) (𝓝[≠] (1 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h1 : Tendsto (fun σ : ℝ => (σ : ℂ)) (nhds (1 : ℝ)) (nhds (1 : ℂ)) := by
        simpa using (Complex.continuous_ofReal.continuousAt (x := (1 : ℝ))).tendsto
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hEq
      exact (Set.mem_Ioi.mp hσ).ne' (by exact_mod_cast hEq)
  have hreal_tend :
      Tendsto (fun σ : ℝ => ((σ : ℂ) - 1) * cyclotomicDedekindZeta q (σ : ℂ))
        (nhdsWithin 1 (Set.Ioi 1)) (𝓝 (cyclotomicDedekindZetaResidue q)) :=
    htend.comp hmaps
  have hneBot : (nhdsWithin (1 : ℝ) (Set.Ioi 1)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  have him_zero : (cyclotomicDedekindZetaResidue q).im = 0 := by
    have hlim_im : Tendsto
        (fun σ : ℝ => (((σ : ℂ) - 1) * cyclotomicDedekindZeta q (σ : ℂ)).im)
        (nhdsWithin 1 (Set.Ioi 1)) (𝓝 (cyclotomicDedekindZetaResidue q).im) :=
      Complex.continuous_im.continuousAt.tendsto.comp hreal_tend
    have hlim_0 : Tendsto
        (fun σ : ℝ => (((σ : ℂ) - 1) * cyclotomicDedekindZeta q (σ : ℂ)).im)
        (nhdsWithin 1 (Set.Ioi 1)) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with σ hσ
      have hpos := cyclotomicDedekindZeta_real_pos q (Set.mem_Ioi.mp hσ)
      simp [Complex.mul_im, hpos.2]
    exact tendsto_nhds_unique hlim_im hlim_0
  have hre_nonneg : 0 ≤ (cyclotomicDedekindZetaResidue q).re := by
    have hlim_re : Tendsto
        (fun σ : ℝ => (((σ : ℂ) - 1) * cyclotomicDedekindZeta q (σ : ℂ)).re)
        (nhdsWithin 1 (Set.Ioi 1)) (𝓝 (cyclotomicDedekindZetaResidue q).re) :=
      Complex.continuous_re.continuousAt.tendsto.comp hreal_tend
    refine ge_of_tendsto hlim_re ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ1 : 1 < σ := Set.mem_Ioi.mp hσ
    have hpos := cyclotomicDedekindZeta_real_pos q hσ1
    have hre_eq : (((σ : ℂ) - 1) * cyclotomicDedekindZeta q (σ : ℂ)).re =
        (σ - 1) * (cyclotomicDedekindZeta q (σ : ℂ)).re := by
      simp [Complex.mul_re, hpos.2]
    rw [hre_eq]
    exact mul_nonneg (by linarith) hpos.1.le
  have hre_pos : 0 < (cyclotomicDedekindZetaResidue q).re := by
    refine lt_of_le_of_ne hre_nonneg ?_
    intro h0
    apply hne
    exact Complex.ext (by simpa using h0.symm) (by simpa using him_zero)
  exact ⟨htend, hre_pos, him_zero, hne⟩

/-- The regularized cyclotomic Dedekind zeta function `cyclotomicDedekindZetaReg q` is **entire**
(holomorphic on all of `ℂ`), with value `cyclotomicDedekindZetaResidue q` at `s = 1` and
`(s - 1) * cyclotomicDedekindZeta q s` for all `s ≠ 1`. -/
theorem cyclotomicDedekindZetaReg_differentiable (q : ℕ) [NeZero q] :
    Differentiable ℂ (cyclotomicDedekindZetaReg q) := by
  rw [← differentiableOn_univ]
  rw [← Complex.differentiableOn_compl_singleton_and_continuousAt_iff (c := (1 : ℂ))
    Filter.univ_mem]
  refine ⟨?_, ?_⟩
  · have hdiff_mul :
        DifferentiableOn ℂ (fun s : ℂ => (s - 1) * cyclotomicDedekindZeta q s) (Set.univ \ {1}) := by
      rw [← Set.compl_eq_univ_sdiff]
      exact (differentiableOn_id.sub (differentiableOn_const 1)).mul
        (cyclotomicDedekindZeta_differentiableOn q)
    refine hdiff_mul.congr fun s hs => ?_
    exact Function.update_of_ne hs.2 _ _
  · rw [ContinuousAt, cyclotomicDedekindZetaReg, Function.update_self]
    have hlim := (cyclotomicDedekindZeta_residue_one q).1
    rw [Metric.tendsto_nhds] at hlim ⊢
    intro ε hε
    have hev := hlim ε hε
    rw [eventually_nhdsWithin_iff] at hev
    filter_upwards [hev] with s hs
    by_cases hs1 : s = 1
    · subst hs1; simp [hε]
    · rw [Function.update_of_ne hs1]
      exact hs hs1

/-- **Meromorphic Continuation of `ζ_{ℚ(ζ_q)}(s)` on `ℂ`**:
holomorphic on `ℂ \ {1}`, with an entire regularization `(s - 1) * ζ_{ℚ(ζ_q)}(s)` taking the
strictly positive real residue `cyclotomicDedekindZetaResidue q` at `s = 1`. -/
theorem cyclotomicDedekindZeta_meromorphic (q : ℕ) [NeZero q] :
    DifferentiableOn ℂ (cyclotomicDedekindZeta q) ({1}ᶜ) ∧
    Differentiable ℂ (cyclotomicDedekindZetaReg q) ∧
    (∀ s : ℂ, s ≠ 1 → cyclotomicDedekindZetaReg q s = (s - 1) * cyclotomicDedekindZeta q s) ∧
    cyclotomicDedekindZetaReg q 1 = cyclotomicDedekindZetaResidue q ∧
    0 < (cyclotomicDedekindZetaResidue q).re ∧
    (cyclotomicDedekindZetaResidue q).im = 0 := by
  have hres := cyclotomicDedekindZeta_residue_one q
  exact ⟨cyclotomicDedekindZeta_differentiableOn q,
    cyclotomicDedekindZetaReg_differentiable q,
    fun s hs => Function.update_of_ne hs _ _,
    Function.update_self _ _ _,
    hres.2.1, hres.2.2.1⟩

/-- Helper: de la Vallée Poussin zero-free region for the principal character `1 mod q`. -/
private lemma LFunction_principal_deLaValleePoussin_zeroFree (q : ℕ) [NeZero q] :
    ∃ c : ℝ, 0 < c ∧
      ∀ s : ℂ, 1 - c / Real.log (|s.im| + 2) ≤ s.re → s ≠ 1 →
        DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s ≠ 0 := by
  obtain ⟨c_ζ, hc_ζ, hzf_ζ⟩ := Stage5ZetaZeroFree.riemannZeta_deLaValleePoussin_zeroFree
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set c : ℝ := min c_ζ (Real.log 2 / 2)
  have hc_pos : 0 < c := lt_min hc_ζ (by positivity)
  refine ⟨c, hc_pos, fun s hre hs1 => ?_⟩
  have hlog_ge : Real.log 2 ≤ Real.log (|s.im| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  have hlog_pos : 0 < Real.log (|s.im| + 2) := hlog2_pos.trans_le hlog_ge
  have hs_re_pos : 0 < s.re := by
    have hdiv : c / Real.log (|s.im| + 2) ≤ 1 / 2 := by
      calc c / Real.log (|s.im| + 2)
          ≤ (Real.log 2 / 2) / Real.log (|s.im| + 2) :=
            div_le_div_of_nonneg_right (min_le_right _ _) hlog_pos.le
        _ ≤ (Real.log 2 / 2) / Real.log 2 :=
            div_le_div_of_nonneg_left (by positivity) hlog2_pos hlog_ge
        _ = 1 / 2 := by field_simp [hlog2_pos.ne']
    linarith
  have hzeta_ne : riemannZeta s ≠ 0 := by
    have hdiv : c / Real.log (|s.im| + 2) ≤ c_ζ / Real.log (|s.im| + 2) :=
      div_le_div_of_nonneg_right (min_le_left _ _) hlog_pos.le
    exact hzf_ζ s (by linarith) hs1
  have htriv : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s =
      (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) * riemannZeta s :=
    DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := q) hs1
  rw [htriv]
  refine mul_ne_zero ?_ hzeta_ne
  refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hnorm_lt : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp_prime.pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp_prime.one_lt) (neg_lt_zero.mpr hs_re_pos)
  intro h0
  have h1 : (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h0).symm
  rw [h1, norm_one] at hnorm_lt
  exact lt_irrefl 1 hnorm_lt

/-- Helper: uniform de la Vallée Poussin zero-free constant across any finite set of characters mod `q`. -/
private lemma finset_dirichletChar_deLaValleePoussin_zeroFree {q : ℕ} [NeZero q]
    (S : Finset (DirichletCharacter ℂ q)) :
    ∃ c : ℝ, 0 < c ∧
      ∀ χ ∈ S, ∀ s : ℂ, 1 - c / Real.log (|s.im| + 2) ≤ s.re → s ≠ 1 →
        DirichletCharacter.LFunction χ s ≠ 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun _ h => (Finset.notMem_empty _ h).elim⟩
  | insert χ S' _ ih =>
    obtain ⟨c₁, hc₁, hS'⟩ := ih
    have hχ_zf : ∃ c₂ : ℝ, 0 < c₂ ∧
        ∀ s : ℂ, 1 - c₂ / Real.log (|s.im| + 2) ≤ s.re → s ≠ 1 →
          DirichletCharacter.LFunction χ s ≠ 0 := by
      by_cases h1 : χ = 1
      · subst h1; exact LFunction_principal_deLaValleePoussin_zeroFree q
      · obtain ⟨c₂, hc₂, hzf⟩ := Stage8ExplicitPrimeBounds.LFunction_deLaValleePoussin_zeroFree_fixed_char h1
        exact ⟨c₂, hc₂, fun s hs _ => hzf s hs⟩
    obtain ⟨c₂, hc₂, hχ⟩ := hχ_zf
    refine ⟨min c₁ c₂, lt_min hc₁ hc₂, fun ψ hψ s hs hs1 => ?_⟩
    have hlog_pos : 0 < Real.log (|s.im| + 2) :=
      Real.log_pos (by linarith [abs_nonneg s.im])
    rcases Finset.mem_insert.mp hψ with rfl | hmem
    · have hle : min c₁ c₂ / Real.log (|s.im| + 2) ≤ c₂ / Real.log (|s.im| + 2) :=
        div_le_div_of_nonneg_right (min_le_right _ _) hlog_pos.le
      exact hχ s (by linarith) hs1
    · have hle : min c₁ c₂ / Real.log (|s.im| + 2) ≤ c₁ / Real.log (|s.im| + 2) :=
        div_le_div_of_nonneg_right (min_le_left _ _) hlog_pos.le
      exact hS' ψ hmem s (by linarith) hs1

/-- **UNCONDITIONAL DE LA VALLÉE POUSSIN ZERO-FREE REGION FOR `ζ_{ℚ(ζ_q)}(s)` (`0` ASSUMPTIONS!)**:
for EVERY `q ≥ 1` (`[NeZero q]`), there exists `c > 0` such that
`cyclotomicDedekindZeta q s ≠ 0` whenever `1 - c / Real.log (|s.im| + 2) ≤ s.re` and `s ≠ 1`. -/
theorem cyclotomicDedekindZeta_zeroFree (q : ℕ) [NeZero q] :
    ∃ c : ℝ, 0 < c ∧
      ∀ s : ℂ, 1 - c / Real.log (|s.im| + 2) ≤ s.re → s ≠ 1 →
        cyclotomicDedekindZeta q s ≠ 0 := by
  obtain ⟨c, hc, hzf⟩ := finset_dirichletChar_deLaValleePoussin_zeroFree (Finset.univ : Finset (DirichletCharacter ℂ q))
  refine ⟨c, hc, fun s hs hs1 => ?_⟩
  unfold cyclotomicDedekindZeta
  exact Finset.prod_ne_zero_iff.mpr fun χ _ => hzf χ (Finset.mem_univ χ) s hs hs1

/-- **UNCONDITIONAL DE LA VALLÉE POUSSIN ZERO-FREE REGION FOR THE ENTIRE REGULARIZATION
`cyclotomicDedekindZetaReg q`** (zero-free EVERYWHERE in `1 - c / log(|s.im| + 2) ≤ s.re`,
including at `s = 1`!). -/
theorem cyclotomicDedekindZetaReg_zeroFree (q : ℕ) [NeZero q] :
    ∃ c : ℝ, 0 < c ∧
      ∀ s : ℂ, 1 - c / Real.log (|s.im| + 2) ≤ s.re →
        cyclotomicDedekindZetaReg q s ≠ 0 := by
  obtain ⟨c, hc, hzf⟩ := cyclotomicDedekindZeta_zeroFree q
  refine ⟨c, hc, fun s hs => ?_⟩
  by_cases hs1 : s = 1
  · subst hs1
    rw [cyclotomicDedekindZetaReg, Function.update_self]
    exact (cyclotomicDedekindZeta_residue_one q).2.2.2
  · rw [cyclotomicDedekindZetaReg, Function.update_of_ne hs1]
    exact mul_ne_zero (sub_ne_zero.mpr hs1) (hzf s hs hs1)

/-- **UNCONDITIONAL DE LA VALLÉE POUSSIN ZERO-FREE REGION FOR THE FULL PRIMITIVE CYCLOTOMIC
DEDEKIND ZETA PRODUCT `∏_{χ mod q} L(s, χ*)`**: for every `q ≥ 1`, there exists `c > 0` such that
`∏ χ : DirichletCharacter ℂ q, primitiveLFunction χ s ≠ 0` whenever
`1 - c / Real.log (|s.im| + 2) ≤ s.re` and `s ≠ 1`. -/
theorem cyclotomicDedekindZeta_primitive_zeroFree (q : ℕ) [NeZero q] :
    ∃ c : ℝ, 0 < c ∧
      ∀ s : ℂ, 1 - c / Real.log (|s.im| + 2) ≤ s.re → s ≠ 1 →
        ∏ χ : DirichletCharacter ℂ q, Stage6ClassNumberFormula.primitiveLFunction χ s ≠ 0 := by
  classical
  have hfin : ∀ (S : Finset (DirichletCharacter ℂ q)), ∃ c : ℝ, 0 < c ∧
      ∀ χ ∈ S, ∀ s : ℂ, 1 - c / Real.log (|s.im| + 2) ≤ s.re → s ≠ 1 →
        Stage6ClassNumberFormula.primitiveLFunction χ s ≠ 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, one_pos, fun _ h => (Finset.notMem_empty _ h).elim⟩
    | insert χ S' _ ih =>
      obtain ⟨c₁, hc₁, hS'⟩ := ih
      have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
      have hχ_zf : ∃ c₂ : ℝ, 0 < c₂ ∧
          ∀ s : ℂ, 1 - c₂ / Real.log (|s.im| + 2) ≤ s.re → s ≠ 1 →
            Stage6ClassNumberFormula.primitiveLFunction χ s ≠ 0 := by
        unfold Stage6ClassNumberFormula.primitiveLFunction
        by_cases h1 : χ.primitiveCharacter = 1
        · rw [h1]; exact LFunction_principal_deLaValleePoussin_zeroFree χ.conductor
        · obtain ⟨c₂, hc₂, hzf⟩ :=
            Stage8ExplicitPrimeBounds.LFunction_deLaValleePoussin_zeroFree_fixed_char h1
          exact ⟨c₂, hc₂, fun s hs _ => hzf s hs⟩
      obtain ⟨c₂, hc₂, hχ⟩ := hχ_zf
      refine ⟨min c₁ c₂, lt_min hc₁ hc₂, fun ψ hψ s hs hs1 => ?_⟩
      have hlog_pos : 0 < Real.log (|s.im| + 2) :=
        Real.log_pos (by linarith [abs_nonneg s.im])
      rcases Finset.mem_insert.mp hψ with rfl | hmem
      · have hle : min c₁ c₂ / Real.log (|s.im| + 2) ≤ c₂ / Real.log (|s.im| + 2) :=
          div_le_div_of_nonneg_right (min_le_right _ _) hlog_pos.le
        exact hχ s (by linarith) hs1
      · have hle : min c₁ c₂ / Real.log (|s.im| + 2) ≤ c₁ / Real.log (|s.im| + 2) :=
          div_le_div_of_nonneg_right (min_le_left _ _) hlog_pos.le
        exact hS' ψ hmem s (by linarith) hs1
  obtain ⟨c, hc, hzf⟩ := hfin Finset.univ
  refine ⟨c, hc, fun s hs hs1 => ?_⟩
  exact Finset.prod_ne_zero_iff.mpr fun χ _ => hzf χ (Finset.mem_univ χ) s hs hs1

end CyclotomicDedekindZeta

/-! ## Section 2: Unconditional Effective Cyclotomic Chebotarev Density Theorem, Subfield Splitting & Effective Kronecker–Bauer -/

section EffectiveChebotarev

/-- Canonical natural representative `a_σ ∈ {0, ..., q-1}` of `(artinMap q)⁻¹ σ ∈ (ZMod q)ˣ`. -/
def artinRep (q : ℕ) [NeZero q] (σ : CycGal q) : ℕ :=
  (((artinMap q).symm σ : (ZMod q)ˣ) : ZMod q).val

/-- `artinRep q σ` is coprime to `q`. -/
theorem artinRep_coprime (q : ℕ) [NeZero q] (σ : CycGal q) :
    Nat.Coprime (artinRep q σ) q := by
  unfold artinRep
  set u : (ZMod q)ˣ := (artinMap q).symm σ
  exact (ZMod.isUnit_iff_coprime _ q).mp ((ZMod.natCast_zmod_val (u : ZMod q)).symm ▸ u.isUnit)

/-- Exact `Fintype.card` of `Gal(ℚ(ζ_q)/ℚ)` equals `φ(q)`. -/
theorem fintype_card_cycGal_eq_totient (q : ℕ) [NeZero q] :
    Fintype.card (CycGal q) = q.totient := by
  rw [← Nat.card_eq_fintype_card]
  exact Stage4ClassFieldTheory.card_cycGal_eq_totient q

open Classical in
/-- Frobenius prime-power Chebyshev function `ψ_Cheb(x; q, σ) = ∑_{n ≤ x, (n,q)=1, Frob_n = σ} Λ(n)`. -/
def chebotarevPsi (q : ℕ) [NeZero q] (σ : CycGal q) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1),
    if h : Nat.Coprime n q then
      if frob q n h = σ then Λ n else 0
    else 0

open Classical in
/-- Frobenius prime Chebyshev function `θ_Cheb(x; q, σ) = ∑_{p ≤ x, p ∤ q, Frob_p = σ} log p`. -/
def chebotarevTheta (q : ℕ) [NeZero q] (σ : CycGal q) (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.range (⌊x⌋₊ + 1),
    if p ∈ FrobPrimes q σ then Real.log (p : ℝ) else 0

open Classical in
/-- Frobenius prime-counting function `π_Cheb(x; q, σ) = #{p ≤ x : p prime, p ∤ q, Frob_p = σ}`. -/
def chebotarevPi (q : ℕ) [NeZero q] (σ : CycGal q) (x : ℝ) : ℕ :=
  ((Finset.range (⌊x⌋₊ + 1)).filter fun p => p ∈ FrobPrimes q σ).card

/-- Exact arithmetic equivalence: `(∃ h : n.Coprime q, frob q n h = σ) ↔ n ≡ artinRep q σ [MOD q]`. -/
lemma coprime_and_frob_eq_iff_modEq (q : ℕ) [NeZero q] (σ : CycGal q) (n : ℕ) :
    (∃ h : Nat.Coprime n q, frob q n h = σ) ↔ n ≡ artinRep q σ [MOD q] := by
  set u : (ZMod q)ˣ := (artinMap q).symm σ
  have ha_cast : (artinRep q σ : ZMod q) = (u : ZMod q) := ZMod.natCast_zmod_val (u : ZMod q)
  constructor
  · rintro ⟨hcop, hEq⟩
    have hu_eq : ZMod.unitOfCoprime n hcop = u := by
      apply (artinMap q).injective
      calc artinMap q (ZMod.unitOfCoprime n hcop)
          = frob q n hcop := rfl
        _ = σ := hEq
        _ = artinMap q u := ((artinMap q).apply_symm_apply σ).symm
    have hval : (n : ZMod q) = (artinRep q σ : ZMod q) := by
      rw [ha_cast, ← hu_eq, ZMod.coe_unitOfCoprime]
    exact (ZMod.natCast_eq_natCast_iff n (artinRep q σ) q).mp hval
  · intro hmod
    have hcast : (n : ZMod q) = (u : ZMod q) := by
      rw [← ha_cast]
      exact (ZMod.natCast_eq_natCast_iff n (artinRep q σ) q).mpr hmod
    have hcop : Nat.Coprime n q := (ZMod.isUnit_iff_coprime n q).mp (hcast.symm ▸ u.isUnit)
    refine ⟨hcop, ?_⟩
    have hu_eq : ZMod.unitOfCoprime n hcop = u := by
      apply Units.ext
      rw [ZMod.coe_unitOfCoprime, hcast]
    calc frob q n hcop = artinMap q (ZMod.unitOfCoprime n hcop) := rfl
      _ = artinMap q u := by rw [hu_eq]
      _ = σ := (artinMap q).apply_symm_apply σ

/-- Exact identification `chebotarevPsi q σ x = chebyshevPsiAP q (artinRep q σ) x`. -/
theorem chebotarevPsi_eq_chebyshevPsiAP (q : ℕ) [NeZero q] (σ : CycGal q) (x : ℝ) :
    chebotarevPsi q σ x = Stage2DirichletAP.chebyshevPsiAP q (artinRep q σ) x := by
  classical
  unfold chebotarevPsi Stage2DirichletAP.chebyshevPsiAP
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hmod : n ≡ artinRep q σ [MOD q]
  · obtain ⟨hcop, hEq⟩ := (coprime_and_frob_eq_iff_modEq q σ n).mpr hmod
    simp [hmod, hcop, hEq]
  · rw [if_neg hmod]
    split_ifs with hcop hEq
    · exact (hmod ((coprime_and_frob_eq_iff_modEq q σ n).mp ⟨hcop, hEq⟩)).elim
    · rfl
    · rfl

/-- Exact identification `chebotarevTheta q σ x = chebyshevThetaAP q (artinRep q σ) x`. -/
theorem chebotarevTheta_eq_chebyshevThetaAP (q : ℕ) [NeZero q] (σ : CycGal q) (x : ℝ) :
    chebotarevTheta q σ x = Stage2DirichletAP.chebyshevThetaAP q (artinRep q σ) x := by
  classical
  unfold chebotarevTheta Stage2DirichletAP.chebyshevThetaAP
  refine Finset.sum_congr rfl fun p _ => ?_
  have hiff : p ∈ FrobPrimes q σ ↔ p.Prime ∧ p ≡ artinRep q σ [MOD q] := by
    rw [Stage5DirichletDensity.frobPrimes_eq_primes_modEq q σ]
    rfl
  simp [hiff]

/-- Exact identification `chebotarevPi q σ x = primeCountAP q (artinRep q σ) x`. -/
theorem chebotarevPi_eq_primeCountAP (q : ℕ) [NeZero q] (σ : CycGal q) (x : ℝ) :
    chebotarevPi q σ x = Stage2DirichletAP.primeCountAP q (artinRep q σ) x := by
  classical
  unfold chebotarevPi Stage2DirichletAP.primeCountAP
  congr 1
  refine Finset.filter_congr fun p _ => ?_
  rw [Stage5DirichletDensity.frobPrimes_eq_primes_modEq q σ]
  rfl

/-- **UNCONDITIONAL EFFECTIVE CYCLOTOMIC CHEBOTAREV DENSITY THEOREM FOR `ψ` (`0` ASSUMPTIONS!)**:
for every `q ≥ 1` (`[NeZero q]`) and every `σ ∈ Gal(ℚ(ζ_q)/ℚ)`:
`∃ c > 0, ∃ C > 0, ∀ x ≥ 2, |chebotarevPsi q σ x - x / |Gal(ℚ(ζ_q)/ℚ)|| ≤ C * x * exp(-c √(log x))`. -/
theorem effective_cyclotomic_chebotarev_psi (q : ℕ) [NeZero q] (σ : CycGal q) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 2 ≤ x →
        |chebotarevPsi q σ x - x / (Fintype.card (CycGal q) : ℝ)| ≤
          C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  simp_rw [chebotarevPsi_eq_chebyshevPsiAP, fintype_card_cycGal_eq_totient]
  exact Stage8ExplicitPrimeBounds.effective_pnt_psiAP_sqrt (artinRep_coprime q σ)

/-- **UNCONDITIONAL EFFECTIVE CYCLOTOMIC CHEBOTAREV DENSITY THEOREM FOR `θ` (`0` ASSUMPTIONS!)**:
for every `q ≥ 1` (`[NeZero q]`) and every `σ ∈ Gal(ℚ(ζ_q)/ℚ)`:
`∃ c > 0, ∃ C > 0, ∀ x ≥ 2, |chebotarevTheta q σ x - x / |Gal(ℚ(ζ_q)/ℚ)|| ≤ C * x * exp(-c √(log x))`. -/
theorem effective_cyclotomic_chebotarev_theta (q : ℕ) [NeZero q] (σ : CycGal q) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 2 ≤ x →
        |chebotarevTheta q σ x - x / (Fintype.card (CycGal q) : ℝ)| ≤
          C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  simp_rw [chebotarevTheta_eq_chebyshevThetaAP, fintype_card_cycGal_eq_totient]
  exact Stage8ExplicitPrimeBounds.effective_pnt_thetaAP_sqrt (artinRep_coprime q σ)

/-- **UNCONDITIONAL EFFECTIVE CYCLOTOMIC CHEBOTAREV NATURAL DENSITY THEOREM (`0` ASSUMPTIONS!)**:
for every `q ≥ 1` (`[NeZero q]`) and every `σ ∈ Gal(ℚ(ζ_q)/ℚ)`:
`chebotarevPi q σ n / Nat.primeCounting n → 1 / |Gal(ℚ(ζ_q)/ℚ)|` (upgrading
`Stage5DirichletDensity` from Dirichlet density to natural density!). -/
theorem effective_cyclotomic_chebotarev_pi_asymp (q : ℕ) [NeZero q] (σ : CycGal q) :
    Tendsto (fun n : ℕ => (chebotarevPi q σ n : ℝ) / (Nat.primeCounting n : ℝ))
      atTop (𝓝 (1 / (Fintype.card (CycGal q) : ℝ))) := by
  simp_rw [chebotarevPi_eq_primeCountAP, fintype_card_cycGal_eq_totient, one_div]
  exact Stage8ExplicitPrimeBounds.prime_density_in_AP_ratio (artinRep_coprime q σ)

/-- Real-variable asymptotic for `chebotarevPi`:
`chebotarevPi q σ x / (x / (|Gal(ℚ(ζ_q)/ℚ)| * Real.log x)) → 1`. -/
theorem effective_cyclotomic_chebotarev_pi_real_asymp (q : ℕ) [NeZero q] (σ : CycGal q) :
    Tendsto
      (fun x : ℝ =>
        (chebotarevPi q σ x : ℝ) / (x / ((Fintype.card (CycGal q) : ℝ) * Real.log x)))
      atTop (𝓝 1) := by
  simp_rw [chebotarevPi_eq_primeCountAP, fintype_card_cycGal_eq_totient]
  exact Stage7PNTInAP.pnt_primeCountAP_real_asymp (artinRep_coprime q σ)

/-- **Unconditional Super-Polynomial Short-Interval Cyclotomic Chebotarev Prime Existence**:
for every `q ≥ 1` and `σ ∈ Gal(ℚ(ζ_q)/ℚ)`, eventually every interval
`(x, x + x * exp(-c √(log x))]` contains a prime `p ∈ FrobPrimes q σ`. -/
theorem exists_prime_frob_short_interval (q : ℕ) [NeZero q] (σ : CycGal q) :
    ∃ c_q : ℝ, 0 < c_q ∧ ∃ X_q : ℝ, ∀ x : ℝ, X_q ≤ x →
      ∃ p : ℕ, p ∈ FrobPrimes q σ ∧ x < (p : ℝ) ∧
        (p : ℝ) ≤ x + x * Real.exp (-c_q * Real.sqrt (Real.log x)) := by
  obtain ⟨c_q, hc_q, X_q, hshort⟩ :=
    Stage8ExplicitPrimeBounds.exists_prime_in_AP_short_interval (artinRep_coprime q σ)
  refine ⟨c_q, hc_q, X_q, fun x hx => ?_⟩
  obtain ⟨p, hp, hmod, hxp, hpy⟩ := hshort x hx
  refine ⟨p, ?_, hxp, hpy⟩
  rw [Stage5DirichletDensity.frobPrimes_eq_primes_modEq q σ]
  exact ⟨hp, hmod⟩

/-! ### Natural Prime Density API & Effective Abelian Subfield Prime Splitting -/

open Classical in
/-- Prime-counting function of an arbitrary set of natural numbers `S : Set ℕ`:
`primeCountSet S x = #{p ≤ x : p.Prime ∧ p ∈ S}`. -/
def primeCountSet (S : Set ℕ) (x : ℝ) : ℕ :=
  ((Finset.range (⌊x⌋₊ + 1)).filter fun p => p.Prime ∧ p ∈ S).card

/-- **Natural Prime Density**: a set `S : Set ℕ` has natural density `δ : ℝ` if
`primeCountSet S n / Nat.primeCounting n → δ` as `n → ∞`. -/
def HasNaturalDensity (S : Set ℕ) (δ : ℝ) : Prop :=
  Tendsto (fun n : ℕ => (primeCountSet S n : ℝ) / (Nat.primeCounting n : ℝ)) atTop (𝓝 δ)

theorem primeCountSet_empty (x : ℝ) : primeCountSet ∅ x = 0 := by
  classical
  simp [primeCountSet]

theorem hasNaturalDensity_empty : HasNaturalDensity ∅ 0 := by
  unfold HasNaturalDensity
  simp only [primeCountSet_empty, Nat.cast_zero, zero_div]
  exact tendsto_const_nhds

theorem primeCountSet_mono {S₁ S₂ : Set ℕ} (hsub : S₁ ⊆ S₂) (x : ℝ) :
    primeCountSet S₁ x ≤ primeCountSet S₂ x := by
  classical
  unfold primeCountSet
  refine Finset.card_le_card fun p hp => ?_
  simp only [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.1, hsub hp.2.2⟩

theorem hasNaturalDensity_mono {S₁ S₂ : Set ℕ} {δ₁ δ₂ : ℝ} (hsub : S₁ ⊆ S₂)
    (h₁ : HasNaturalDensity S₁ δ₁) (h₂ : HasNaturalDensity S₂ δ₂) : δ₁ ≤ δ₂ := by
  refine le_of_tendsto_of_tendsto h₁ h₂ ?_
  filter_upwards [eventually_ge_atTop 2] with n _
  exact div_le_div_of_nonneg_right (by exact_mod_cast primeCountSet_mono hsub n) (Nat.cast_nonneg _)

theorem hasNaturalDensity_zero_of_subset {S₁ S₂ : Set ℕ} (hsub : S₁ ⊆ S₂)
    (h₂ : HasNaturalDensity S₂ 0) : HasNaturalDensity S₁ 0 := by
  unfold HasNaturalDensity at h₂ ⊢
  refine squeeze_zero' ?_ ?_ h₂
  · filter_upwards with n
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards with n
    exact div_le_div_of_nonneg_right (by exact_mod_cast primeCountSet_mono hsub n) (Nat.cast_nonneg _)

theorem primeCountSet_frobPrimes (q : ℕ) [NeZero q] (σ : CycGal q) (x : ℝ) :
    primeCountSet (FrobPrimes q σ) x = chebotarevPi q σ x := by
  classical
  unfold primeCountSet chebotarevPi
  congr 1
  refine Finset.filter_congr fun p _ => ?_
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

theorem hasNaturalDensity_frobPrimes (q : ℕ) [NeZero q] (σ : CycGal q) :
    HasNaturalDensity (FrobPrimes q σ) (1 / (Fintype.card (CycGal q) : ℝ)) := by
  unfold HasNaturalDensity
  simp_rw [primeCountSet_frobPrimes]
  exact effective_cyclotomic_chebotarev_pi_asymp q σ

open Classical in
/-- Subfield splitting Chebyshev `ψ` sum for an Artin subgroup `H ≤ (ZMod q)ˣ`
(corresponding to the abelian subfield `K = cycFixedField q H ⊆ ℚ(ζ_q)`):
`ψ_split(H, x) = ∑_{n ≤ x, (n,q)=1, (n mod q) ∈ H} Λ(n)`. -/
def splitPsi (q : ℕ) [NeZero q] (H : Subgroup (ZMod q)ˣ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1),
    if h : Nat.Coprime n q then
      if ZMod.unitOfCoprime n h ∈ H then Λ n else 0
    else 0

open Classical in
/-- Subfield splitting Chebyshev `θ` sum for `H ≤ (ZMod q)ˣ`:
`θ_split(H, x) = ∑_{p ≤ x, p ∈ SplitPrimes (cycFixedField q H)} log p`. -/
def splitTheta (q : ℕ) [NeZero q] (H : Subgroup (ZMod q)ˣ) (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.range (⌊x⌋₊ + 1),
    if p ∈ SplitPrimes (cycFixedField q H) then Real.log (p : ℝ) else 0

open Classical in
/-- Subfield splitting prime-counting function for `H ≤ (ZMod q)ˣ`:
`π_split(H, x) = #{p ≤ x : p ∈ SplitPrimes (cycFixedField q H)}`. -/
def splitPi (q : ℕ) [NeZero q] (H : Subgroup (ZMod q)ˣ) (x : ℝ) : ℕ :=
  ((Finset.range (⌊x⌋₊ + 1)).filter fun p => p ∈ SplitPrimes (cycFixedField q H)).card

/-- Exact equality `primeCountSet (SplitPrimes (cycFixedField q H)) x = splitPi q H x`. -/
theorem primeCountSet_splitPrimes_eq_splitPi (q : ℕ) [NeZero q] (H : Subgroup (ZMod q)ˣ) (x : ℝ) :
    primeCountSet (SplitPrimes (cycFixedField q H)) x = splitPi q H x := by
  classical
  unfold primeCountSet splitPi
  congr 1
  refine Finset.filter_congr fun p _ => ?_
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

/-- Exact Frobenius decomposition of `splitPsi q H x` over `u : H`. -/
theorem splitPsi_eq_sum (q : ℕ) [NeZero q] (H : Subgroup (ZMod q)ˣ) [Fintype H] (x : ℝ) :
    splitPsi q H x = ∑ u : H, chebotarevPsi q (artinMap q u.1) x := by
  classical
  unfold splitPsi chebotarevPsi
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hcop : Nat.Coprime n q
  · simp only [dif_pos hcop]
    set v : (ZMod q)ˣ := ZMod.unitOfCoprime n hcop
    have hiff : ∀ u : H, (frob q n hcop = artinMap q u.1) ↔ v = u.1 := fun u =>
      (artinMap q).injective.eq_iff
    by_cases hv : v ∈ H
    · rw [if_pos hv]
      have huniq : ∑ u : H, (if frob q n hcop = artinMap q u.1 then Λ n else 0) =
          ∑ u : H, (if u = ⟨v, hv⟩ then Λ n else 0) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [hiff u]
        have heq : (v = u.1) ↔ (u = ⟨v, hv⟩) := by
          constructor
          · intro h; exact Subtype.ext h.symm
          · intro h; exact (congrArg Subtype.val h).symm
        simp [heq]
      rw [huniq]
      simp
    · rw [if_neg hv]
      symm
      refine Finset.sum_eq_zero fun u _ => ?_
      rw [if_neg]
      intro hEq
      exact hv (((hiff u).mp hEq).symm ▸ u.2)
  · simp [dif_neg hcop]

/-- Exact Frobenius decomposition of `splitTheta q H x` over `u : H`. -/
theorem splitTheta_eq_sum (q : ℕ) [NeZero q] (H : Subgroup (ZMod q)ˣ) [Fintype H] (x : ℝ) :
    splitTheta q H x = ∑ u : H, chebotarevTheta q (artinMap q u.1) x := by
  classical
  unfold splitTheta chebotarevTheta
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hmem : p ∈ SplitPrimes (cycFixedField q H)
  · rw [if_pos hmem]
    obtain ⟨hp, hndvd, hv⟩ := (Stage5DirichletDensity.mem_splitPrimes_cycFixedField_iff H p).mp hmem
    set v : (ZMod q)ˣ := ZMod.unitOfCoprime p ((Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd)
    have huniq : ∑ u : H, (if p ∈ FrobPrimes q (artinMap q u.1) then Real.log (p : ℝ) else 0) =
        ∑ u : H, (if u = ⟨v, hv⟩ then Real.log (p : ℝ) else 0) := by
      refine Finset.sum_congr rfl fun u _ => ?_
      have hiff : p ∈ FrobPrimes q (artinMap q u.1) ↔ u = ⟨v, hv⟩ := by
        constructor
        · rintro ⟨hp', hndvd', hEq⟩
          have hv_eq : v = u.1 := (artinMap q).injective hEq
          exact Subtype.ext hv_eq.symm
        · intro hu
          refine ⟨hp, hndvd, ?_⟩
          have hv_eq : v = u.1 := (congrArg Subtype.val hu).symm
          exact congrArg (artinMap q) hv_eq
      simp [hiff]
    rw [huniq]
    simp
  · rw [if_neg hmem]
    symm
    refine Finset.sum_eq_zero fun u _ => ?_
    rw [if_neg]
    intro hfp
    obtain ⟨hp, hndvd, hEq⟩ := hfp
    apply hmem
    rw [Stage5DirichletDensity.mem_splitPrimes_cycFixedField_iff]
    refine ⟨hp, hndvd, ?_⟩
    have hv_eq : ZMod.unitOfCoprime p ((Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd) = u.1 :=
      (artinMap q).injective hEq
    exact hv_eq.symm ▸ u.2

/-- Exact Frobenius decomposition of `splitPi q H x` over `u : H`. -/
theorem splitPi_eq_sum (q : ℕ) [NeZero q] (H : Subgroup (ZMod q)ˣ) [Fintype H] (x : ℝ) :
    splitPi q H x = ∑ u : H, chebotarevPi q (artinMap q u.1) x := by
  classical
  unfold splitPi chebotarevPi
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hmem : p ∈ SplitPrimes (cycFixedField q H)
  · rw [if_pos hmem]
    obtain ⟨hp, hndvd, hv⟩ := (Stage5DirichletDensity.mem_splitPrimes_cycFixedField_iff H p).mp hmem
    set v : (ZMod q)ˣ := ZMod.unitOfCoprime p ((Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd)
    have huniq : ∑ u : H, (if p ∈ FrobPrimes q (artinMap q u.1) then 1 else 0) =
        ∑ u : H, (if u = ⟨v, hv⟩ then 1 else 0) := by
      refine Finset.sum_congr rfl fun u _ => ?_
      have hiff : p ∈ FrobPrimes q (artinMap q u.1) ↔ u = ⟨v, hv⟩ := by
        constructor
        · rintro ⟨hp', hndvd', hEq⟩
          exact Subtype.ext ((artinMap q).injective hEq).symm
        · intro hu
          exact ⟨hp, hndvd, congrArg (artinMap q) (congrArg Subtype.val hu).symm⟩
      simp [hiff]
    rw [huniq]
    simp
  · rw [if_neg hmem]
    symm
    refine Finset.sum_eq_zero fun u _ => ?_
    rw [if_neg]
    rintro ⟨hp, hndvd, hEq⟩
    apply hmem
    rw [Stage5DirichletDensity.mem_splitPrimes_cycFixedField_iff]
    refine ⟨hp, hndvd, ?_⟩
    exact ((artinMap q).injective hEq).symm ▸ u.2

/-- Helper: uniform `exp(-c √(log x))` bound for a finite sum of `chebotarevPsi q σ x`
over any subset `s : Finset (CycGal q)`. -/
theorem effective_cyclotomic_chebotarev_psi_finset (q : ℕ) [NeZero q] (s : Finset (CycGal q)) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 2 ≤ x →
        |(∑ σ ∈ s, chebotarevPsi q σ x) -
            (s.card : ℝ) * (x / (Fintype.card (CycGal q) : ℝ))| ≤
          C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨1, one_pos, 1, one_pos, fun x hx => ?_⟩
    simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero, zero_mul, sub_self, abs_zero]
    positivity
  | insert σ s' hσ ih =>
    obtain ⟨c₁, hc₁, C₁, hC₁, hbd₁⟩ := ih
    obtain ⟨c₂, hc₂, C₂, hC₂, hbd₂⟩ := effective_cyclotomic_chebotarev_psi q σ
    set c : ℝ := min c₁ c₂
    refine ⟨c, lt_min hc₁ hc₂, C₁ + C₂, by positivity, fun x hx => ?_⟩
    have hx0 : 0 < x := by linarith
    have hsq_nn : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
    rw [Finset.sum_insert hσ, Finset.card_insert_of_notMem hσ, Nat.cast_add, Nat.cast_one, add_mul,
      one_mul]
    have hsplit : (chebotarevPsi q σ x + ∑ τ ∈ s', chebotarevPsi q τ x) -
        ((s'.card : ℝ) * (x / (Fintype.card (CycGal q) : ℝ)) +
          x / (Fintype.card (CycGal q) : ℝ)) =
        (chebotarevPsi q σ x - x / (Fintype.card (CycGal q) : ℝ)) +
        ((∑ τ ∈ s', chebotarevPsi q τ x) -
          (s'.card : ℝ) * (x / (Fintype.card (CycGal q) : ℝ))) := by ring
    rw [hsplit]
    have hb1 : |(∑ τ ∈ s', chebotarevPsi q τ x) -
        (s'.card : ℝ) * (x / (Fintype.card (CycGal q) : ℝ))| ≤
        C₁ * x * Real.exp (-c * Real.sqrt (Real.log x)) :=
      (hbd₁ x hx).trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith [min_le_left c₁ c₂])) (by positivity))
    have hb2 : |chebotarevPsi q σ x - x / (Fintype.card (CycGal q) : ℝ)| ≤
        C₂ * x * Real.exp (-c * Real.sqrt (Real.log x)) :=
      (hbd₂ x hx).trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith [min_le_right c₁ c₂])) (by positivity))
    calc |(chebotarevPsi q σ x - x / (Fintype.card (CycGal q) : ℝ)) +
            ((∑ τ ∈ s', chebotarevPsi q τ x) -
              (s'.card : ℝ) * (x / (Fintype.card (CycGal q) : ℝ)))|
        ≤ |chebotarevPsi q σ x - x / (Fintype.card (CycGal q) : ℝ)| +
          |(∑ τ ∈ s', chebotarevPsi q τ x) -
            (s'.card : ℝ) * (x / (Fintype.card (CycGal q) : ℝ))| := abs_add_le _ _
      _ ≤ C₂ * x * Real.exp (-c * Real.sqrt (Real.log x)) +
          C₁ * x * Real.exp (-c * Real.sqrt (Real.log x)) := add_le_add hb2 hb1
      _ = (C₁ + C₂) * x * Real.exp (-c * Real.sqrt (Real.log x)) := by ring

/-- Helper: uniform `exp(-c √(log x))` bound for a finite sum of `chebotarevTheta q σ x`
over any subset `s : Finset (CycGal q)`. -/
theorem effective_cyclotomic_chebotarev_theta_finset (q : ℕ) [NeZero q] (s : Finset (CycGal q)) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 2 ≤ x →
        |(∑ σ ∈ s, chebotarevTheta q σ x) -
            (s.card : ℝ) * (x / (Fintype.card (CycGal q) : ℝ))| ≤
          C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨1, one_pos, 1, one_pos, fun x hx => ?_⟩
    simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero, zero_mul, sub_self, abs_zero]
    positivity
  | insert σ s' hσ ih =>
    obtain ⟨c₁, hc₁, C₁, hC₁, hbd₁⟩ := ih
    obtain ⟨c₂, hc₂, C₂, hC₂, hbd₂⟩ := effective_cyclotomic_chebotarev_theta q σ
    set c : ℝ := min c₁ c₂
    refine ⟨c, lt_min hc₁ hc₂, C₁ + C₂, by positivity, fun x hx => ?_⟩
    have hx0 : 0 < x := by linarith
    have hsq_nn : 0 ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
    rw [Finset.sum_insert hσ, Finset.card_insert_of_notMem hσ, Nat.cast_add, Nat.cast_one, add_mul,
      one_mul]
    have hsplit : (chebotarevTheta q σ x + ∑ τ ∈ s', chebotarevTheta q τ x) -
        ((s'.card : ℝ) * (x / (Fintype.card (CycGal q) : ℝ)) +
          x / (Fintype.card (CycGal q) : ℝ)) =
        (chebotarevTheta q σ x - x / (Fintype.card (CycGal q) : ℝ)) +
        ((∑ τ ∈ s', chebotarevTheta q τ x) -
          (s'.card : ℝ) * (x / (Fintype.card (CycGal q) : ℝ))) := by ring
    rw [hsplit]
    have hb1 : |(∑ τ ∈ s', chebotarevTheta q τ x) -
        (s'.card : ℝ) * (x / (Fintype.card (CycGal q) : ℝ))| ≤
        C₁ * x * Real.exp (-c * Real.sqrt (Real.log x)) :=
      (hbd₁ x hx).trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith [min_le_left c₁ c₂])) (by positivity))
    have hb2 : |chebotarevTheta q σ x - x / (Fintype.card (CycGal q) : ℝ)| ≤
        C₂ * x * Real.exp (-c * Real.sqrt (Real.log x)) :=
      (hbd₂ x hx).trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by nlinarith [min_le_right c₁ c₂])) (by positivity))
    calc |(chebotarevTheta q σ x - x / (Fintype.card (CycGal q) : ℝ)) +
            ((∑ τ ∈ s', chebotarevTheta q τ x) -
              (s'.card : ℝ) * (x / (Fintype.card (CycGal q) : ℝ)))|
        ≤ |chebotarevTheta q σ x - x / (Fintype.card (CycGal q) : ℝ)| +
          |(∑ τ ∈ s', chebotarevTheta q τ x) -
            (s'.card : ℝ) * (x / (Fintype.card (CycGal q) : ℝ))| := abs_add_le _ _
      _ ≤ C₂ * x * Real.exp (-c * Real.sqrt (Real.log x)) +
          C₁ * x * Real.exp (-c * Real.sqrt (Real.log x)) := add_le_add hb2 hb1
      _ = (C₁ + C₂) * x * Real.exp (-c * Real.sqrt (Real.log x)) := by ring

/-- Helper: Lagrange ratio `(Fintype.card H : ℝ) / (Fintype.card (CycGal q) : ℝ) = 1 / [cycFixedField q H : ℚ]`. -/
private lemma card_subgroup_div_card_cycGal (q : ℕ) [NeZero q] (H : Subgroup (ZMod q)ˣ)
    [Fintype H] :
    (Fintype.card H : ℝ) / (Fintype.card (CycGal q) : ℝ) =
      1 / (Module.finrank ℚ (cycFixedField q H) : ℝ) := by
  rw [fintype_card_cycGal_eq_totient, Stage4ClassFieldTheory.finrank_cycFixedField_eq_index]
  have hlag : (Fintype.card H : ℝ) * (H.index : ℝ) = (q.totient : ℝ) := by
    have h1 := Subgroup.card_mul_index H
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] at h1
    exact_mod_cast h1
  have hHpos : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  have htot_pos : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hidx_pos : (H.index : ℝ) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hlag; linarith
  rw [← hlag]
  field_simp [hHpos, hidx_pos]

/-- **UNCONDITIONAL EFFECTIVE ABELIAN SUBFIELD PRIME SPLITTING (`0` ASSUMPTIONS!)**:
for EVERY `q ≥ 1` (`[NeZero q]`) and EVERY subgroup `H ≤ (ZMod q)ˣ` (corresponding to the abelian
subfield `K = cycFixedField q H ⊆ ℚ(ζ_q)` of degree `[K : ℚ] = [(ZMod q)ˣ : H]`):
1. `π_split(H, n) / π(n) → 1 / [K : ℚ]` (exact natural splitting density!),
2. `∃ c > 0, ∃ C > 0, ∀ x ≥ 2, |ψ_split(H, x) - x / [K : ℚ]| ≤ C * x * exp(-c √(log x))`,
3. `∃ c > 0, ∃ C > 0, ∀ x ≥ 2, |θ_split(H, x) - x / [K : ℚ]| ≤ C * x * exp(-c √(log x))`. -/
theorem effective_abelian_subfield_splitting (q : ℕ) [NeZero q] (H : Subgroup (ZMod q)ˣ) :
    Tendsto (fun n : ℕ => (splitPi q H n : ℝ) / (Nat.primeCounting n : ℝ))
      atTop (𝓝 (1 / (Module.finrank ℚ (cycFixedField q H) : ℝ))) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 2 ≤ x →
        |splitPsi q H x - x / (Module.finrank ℚ (cycFixedField q H) : ℝ)| ≤
          C * x * Real.exp (-c * Real.sqrt (Real.log x))) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 2 ≤ x →
        |splitTheta q H x - x / (Module.finrank ℚ (cycFixedField q H) : ℝ)| ≤
          C * x * Real.exp (-c * Real.sqrt (Real.log x))) := by
  classical
  let s : Finset (CycGal q) := Finset.univ.image (fun u : H => artinMap q u.1)
  have hinj : Function.Injective (fun u : H => artinMap q u.1) := fun u v h =>
    Subtype.ext ((artinMap q).injective h)
  have hscard : s.card = Fintype.card H := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  have hratio := card_subgroup_div_card_cycGal q H
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1: Natural splitting density `π_split(H, n) / π(n) → 1 / [K : ℚ]`
    have hsum : Tendsto
        (fun n : ℕ => ∑ u : H, (chebotarevPi q (artinMap q u.1) n : ℝ) / (Nat.primeCounting n : ℝ))
        atTop (𝓝 (∑ _u : H, (1 / (Fintype.card (CycGal q) : ℝ)))) :=
      tendsto_finsetSum Finset.univ fun u _ =>
        effective_cyclotomic_chebotarev_pi_asymp q (artinMap q u.1)
    have hlim_eq : ∑ _u : H, (1 / (Fintype.card (CycGal q) : ℝ)) =
        1 / (Module.finrank ℚ (cycFixedField q H) : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div, hratio]
    rw [hlim_eq] at hsum
    refine hsum.congr fun n => ?_
    rw [splitPi_eq_sum q H (n : ℝ), Nat.cast_sum, Finset.sum_div]
  · -- Part 2: Effective `ψ_split` bound
    obtain ⟨c, hc, C, hC, hbd⟩ := effective_cyclotomic_chebotarev_psi_finset q s
    refine ⟨c, hc, C, hC, fun x hx => ?_⟩
    have hsum_eq : ∑ σ ∈ s, chebotarevPsi q σ x = splitPsi q H x := by
      rw [splitPsi_eq_sum q H x, Finset.sum_image (fun u _ v _ h => hinj h)]
    have hmain_eq : (s.card : ℝ) * (x / (Fintype.card (CycGal q) : ℝ)) =
        x / (Module.finrank ℚ (cycFixedField q H) : ℝ) := by
      rw [hscard, show (Fintype.card H : ℝ) * (x / (Fintype.card (CycGal q) : ℝ)) =
        x * ((Fintype.card H : ℝ) / (Fintype.card (CycGal q) : ℝ)) by ring, hratio]
      ring
    simpa only [hsum_eq, hmain_eq] using hbd x hx
  · -- Part 3: Effective `θ_split` bound
    obtain ⟨c, hc, C, hC, hbd⟩ := effective_cyclotomic_chebotarev_theta_finset q s
    refine ⟨c, hc, C, hC, fun x hx => ?_⟩
    have hsum_eq : ∑ σ ∈ s, chebotarevTheta q σ x = splitTheta q H x := by
      rw [splitTheta_eq_sum q H x, Finset.sum_image (fun u _ v _ h => hinj h)]
    have hmain_eq : (s.card : ℝ) * (x / (Fintype.card (CycGal q) : ℝ)) =
        x / (Module.finrank ℚ (cycFixedField q H) : ℝ) := by
      rw [hscard, show (Fintype.card H : ℝ) * (x / (Fintype.card (CycGal q) : ℝ)) =
        x * ((Fintype.card H : ℝ) / (Fintype.card (CycGal q) : ℝ)) by ring, hratio]
      ring
    simpa only [hsum_eq, hmain_eq] using hbd x hx

/-- Natural density of `SplitPrimes K` equals `1 / [K : ℚ]` for EVERY intermediate field
`K : IntermediateField ℚ (CycField q)`. -/
theorem hasNaturalDensity_splitPrimes_eq_inv_finrank (q : ℕ) [NeZero q]
    (K : IntermediateField ℚ (CycField q)) :
    HasNaturalDensity (SplitPrimes K) (1 / (Module.finrank ℚ K : ℝ)) := by
  have hK : cycFixedField q (cycFixingSubgroup q K) = K :=
    Stage4ClassFieldTheory.cycFixedField_fixingSubgroup q K
  have h := (effective_abelian_subfield_splitting q (cycFixingSubgroup q K)).1
  unfold HasNaturalDensity
  rw [← hK]
  simpa only [primeCountSet_splitPrimes_eq_splitPi] using h

/-- **Effective Kronecker–Bauer Inclusion Theorem for Abelian Subfields (Natural Density Form)**:
for any subgroups `H₁, H₂ ≤ (ZMod q)ˣ`, the set of primes splitting in `ℚ(ζ_q)^{H₁}` but not
in `ℚ(ζ_q)^{H₂}` has natural density `0` IFF `H₁ ≤ H₂`. -/
theorem effective_kronecker_bauer_le_abelian (q : ℕ) [NeZero q]
    (H₁ H₂ : Subgroup (ZMod q)ˣ) :
    HasNaturalDensity (SplitPrimes (cycFixedField q H₁) \ SplitPrimes (cycFixedField q H₂)) 0 ↔
      H₁ ≤ H₂ := by
  constructor
  · intro h0 u hu1
    by_contra hu2
    have hsub : FrobPrimes q (artinMap q u) ⊆
        SplitPrimes (cycFixedField q H₁) \ SplitPrimes (cycFixedField q H₂) := by
      rintro p ⟨hp, hndvd, hEq⟩
      have hv_eq : ZMod.unitOfCoprime p ((Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd) = u :=
        (artinMap q).injective hEq
      refine ⟨?_, ?_⟩
      · rw [Stage5DirichletDensity.mem_splitPrimes_cycFixedField_iff]
        exact ⟨hp, hndvd, hv_eq.symm ▸ hu1⟩
      · rw [Stage5DirichletDensity.mem_splitPrimes_cycFixedField_iff]
        rintro ⟨_, _, hv2⟩
        exact hu2 (hv_eq ▸ hv2)
    have hle := hasNaturalDensity_mono hsub (hasNaturalDensity_frobPrimes q (artinMap q u)) h0
    have hpos : (0 : ℝ) < 1 / (Fintype.card (CycGal q) : ℝ) := by
      rw [fintype_card_cycGal_eq_totient]
      have htot : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
      positivity
    linarith
  · intro hle
    have hsub : SplitPrimes (cycFixedField q H₁) ⊆ SplitPrimes (cycFixedField q H₂) := by
      intro p hp
      rw [Stage5DirichletDensity.mem_splitPrimes_cycFixedField_iff] at hp ⊢
      obtain ⟨hpr, hndvd, hu⟩ := hp
      exact ⟨hpr, hndvd, hle hu⟩
    rw [Set.sdiff_eq_empty.mpr hsub]
    exact hasNaturalDensity_empty

/-- **UNCONDITIONAL EFFECTIVE KRONECKER–BAUER UNIQUENESS THEOREM FOR ABELIAN SUBFIELDS (`0` ASSUMPTIONS!)**:
two subgroups `H₁, H₂ ≤ (ZMod q)ˣ` have the same splitting prime set up to a set of natural
density `0` IFF `H₁ = H₂`! -/
theorem effective_kronecker_bauer_abelian (q : ℕ) [NeZero q]
    (H₁ H₂ : Subgroup (ZMod q)ˣ) :
    HasNaturalDensity
        (symmDiff (SplitPrimes (cycFixedField q H₁)) (SplitPrimes (cycFixedField q H₂))) 0 ↔
      H₁ = H₂ := by
  constructor
  · intro h0
    have h12 : H₁ ≤ H₂ :=
      (effective_kronecker_bauer_le_abelian q H₁ H₂).mp
        (hasNaturalDensity_zero_of_subset Set.subset_union_left h0)
    have h21 : H₂ ≤ H₁ :=
      (effective_kronecker_bauer_le_abelian q H₂ H₁).mp
        (hasNaturalDensity_zero_of_subset Set.subset_union_right h0)
    exact le_antisymm h12 h21
  · rintro rfl
    simp [hasNaturalDensity_empty]

/-- **Effective Kronecker–Bauer Uniqueness Theorem for Cyclotomic Intermediate Fields (Natural Density Form)**:
`HasNaturalDensity (symmDiff (SplitPrimes K₁) (SplitPrimes K₂)) 0 ↔ K₁ = K₂`. -/
theorem effective_kronecker_bauer_intermediateField (q : ℕ) [NeZero q]
    (K₁ K₂ : IntermediateField ℚ (CycField q)) :
    HasNaturalDensity (symmDiff (SplitPrimes K₁) (SplitPrimes K₂)) 0 ↔ K₁ = K₂ := by
  have h1 : cycFixedField q (cycFixingSubgroup q K₁) = K₁ :=
    Stage4ClassFieldTheory.cycFixedField_fixingSubgroup q K₁
  have h2 : cycFixedField q (cycFixingSubgroup q K₂) = K₂ :=
    Stage4ClassFieldTheory.cycFixedField_fixingSubgroup q K₂
  conv_lhs => rw [← h1, ← h2]
  rw [effective_kronecker_bauer_abelian q (cycFixingSubgroup q K₁) (cycFixingSubgroup q K₂)]
  constructor
  · intro heq; rw [← h1, ← h2, heq]
  · intro heq; rw [heq]

end EffectiveChebotarev

/-! ## Section 3: Unconditional Effective Prime Ideal Theorem for `ℚ(ζ_q)` -/

section EffectivePrimeIdealTheorem

/-- There are only finitely many height-one prime ideals of `𝓞 K` with absolute norm `≤ N`. -/
theorem finite_heightOne_absNorm_le (K : Type*) [Field K] [NumberField K] (N : ℕ) :
    {v : HeightOneSpectrum (𝓞 K) | Ideal.absNorm v.asIdeal ≤ N}.Finite := by
  have hI : {I : Ideal (𝓞 K) | Ideal.absNorm I ≤ N}.Finite := by
    have hsub : {I : Ideal (𝓞 K) | Ideal.absNorm I ≤ N} ⊆
        ⋃ n ∈ (Finset.range (N + 1) : Set ℕ), {I : Ideal (𝓞 K) | Ideal.absNorm I = n} := by
      intro I hI
      exact Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.lt_succ_of_le hI))) rfl
    exact ((Finset.finite_toSet (Finset.range (N + 1))).biUnion fun n _ =>
      Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 K) n).subset hsub
  refine Set.Finite.of_finite_image (f := fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal) ?_ ?_
  · refine hI.subset ?_
    rintro I ⟨v, hv, rfl⟩
    exact hv
  · exact fun v _ w _ h => HeightOneSpectrum.ext h

/-- The finite set of all height-one prime ideals `𝔭` of `𝓞 K` with `Ideal.absNorm 𝔭 ≤ ⌊x⌋₊`. -/
def primeIdealsUpTo (K : Type*) [Field K] [NumberField K] (x : ℝ) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  (finite_heightOne_absNorm_le K ⌊x⌋₊).toFinset

theorem mem_primeIdealsUpTo {K : Type*} [Field K] [NumberField K] {x : ℝ}
    {v : HeightOneSpectrum (𝓞 K)} :
    v ∈ primeIdealsUpTo K x ↔ Ideal.absNorm v.asIdeal ≤ ⌊x⌋₊ :=
  Set.Finite.mem_toFinset _

/-- Concrete prime-ideal Chebyshev function `θ_K(x) = ∑_{N(𝔭) ≤ x} log N(𝔭)` over all height-one
prime ideals of `𝓞 K`. -/
def primeIdealTheta (K : Type*) [Field K] [NumberField K] (x : ℝ) : ℝ :=
  ∑ v ∈ primeIdealsUpTo K x, Real.log (Ideal.absNorm v.asIdeal : ℝ)

/-- Concrete prime-ideal counting function `π_K(x) = #{𝔭 : HeightOneSpectrum (𝓞 K) | N(𝔭) ≤ x}`. -/
def primeIdealPi (K : Type*) [Field K] [NumberField K] (x : ℝ) : ℕ :=
  (primeIdealsUpTo K x).card

/-- Helper: if `p` is prime and `p ≡ 1 [MOD q]`, then `¬ p ∣ q`. -/
private lemma not_dvd_of_prime_modEq_one {q p : ℕ} [NeZero q] (hp : p.Prime) (hmod : p ≡ 1 [MOD q]) :
    ¬ p ∣ q := by
  have hcast : (p : ZMod q) = (1 : ZMod q) := by
    simpa using (ZMod.natCast_eq_natCast_iff p 1 q).mpr hmod
  have hcop : Nat.Coprime p q := (ZMod.isUnit_iff_coprime p q).mp (hcast.symm ▸ isUnit_one)
  exact (Nat.Prime.coprime_iff_not_dvd hp).mp hcop

/-- Helper: exact degree-1 split prime-ideal contribution to `primeIdealTheta (CycField q) x`
and `primeIdealPi (CycField q) x`. -/
private lemma split_primeIdeals_exact_eval (q : ℕ) [NeZero q] (x : ℝ) :
    let S_split := (primeIdealsUpTo (CycField q) x).filter fun v =>
      ¬ ((Ideal.absNorm v.asIdeal).minFac ∣ q) ∧ (Ideal.absNorm v.asIdeal).minFac ≡ 1 [MOD q]
    (∑ v ∈ S_split, Real.log (Ideal.absNorm v.asIdeal : ℝ)) =
      (q.totient : ℝ) * Stage2DirichletAP.chebyshevThetaAP q 1 x ∧
    S_split.card = q.totient * Stage2DirichletAP.primeCountAP q 1 x := by
  classical
  intro S_split
  set P_split : Finset ℕ := (Finset.range (⌊x⌋₊ + 1)).filter fun p => p.Prime ∧ p ≡ 1 [MOD q]
  have hmaps : ∀ v ∈ S_split, (Ideal.absNorm v.asIdeal).minFac ∈ P_split := by
    intro v hv
    rw [Finset.mem_filter] at hv
    have hv_norm : Ideal.absNorm v.asIdeal ≤ ⌊x⌋₊ := mem_primeIdealsUpTo.mp hv.1
    have hp_prime : (Ideal.absNorm v.asIdeal).minFac.Prime := minFac_absNorm_prime v
    have hp_le : (Ideal.absNorm v.asIdeal).minFac ≤ Ideal.absNorm v.asIdeal :=
      Nat.le_of_dvd (Nat.zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v))
        (Nat.minFac_dvd _)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hp_le.trans hv_norm)), hp_prime, hv.2.2⟩
  -- For every `p ∈ P_split`, the fiber `{v ∈ S_split | minFac = p}` has size `φ(q)` and norm `p`
  have hfiber : ∀ p ∈ P_split,
      (∀ v ∈ S_split.filter (fun v => (Ideal.absNorm v.asIdeal).minFac = p),
        Ideal.absNorm v.asIdeal = p) ∧
      (S_split.filter (fun v => (Ideal.absNorm v.asIdeal).minFac = p)).card = q.totient := by
    intro p hp_mem
    obtain ⟨hp_rng, hp_prime, hp_mod⟩ := Finset.mem_filter.mp hp_mem
    have hp_le : p ≤ ⌊x⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp_rng)
    have hndvd : ¬ p ∣ q := not_dvd_of_prime_modEq_one hp_prime hp_mod
    have hcop : Nat.Coprime p q := hp_prime.coprime_iff_not_dvd.mpr hndvd
    have hres1 : resDeg q p hcop = 1 := (Stage4ClassFieldTheory.resDeg_eq_one_iff hcop).mpr hp_mod
    have hnum : numPrimesAbove q p hcop = q.totient :=
      (Stage4ClassFieldTheory.numPrimesAbove_eq_totient_iff hcop).mpr hp_mod
    have hnorm_of_above : ∀ v : PrimesAbove (CycField q) p, Ideal.absNorm v.1.asIdeal = p := by
      intro v
      rw [Stage7DedekindZeta.cyc_absNorm_eq_pow_resDeg hp_prime hndvd v, hres1, pow_one]
    have hnorm_fib : ∀ v ∈ S_split.filter (fun v => (Ideal.absNorm v.asIdeal).minFac = p),
        Ideal.absNorm v.asIdeal = p := by
      intro v hv
      have hmf : (Ideal.absNorm v.asIdeal).minFac = p := (Finset.mem_filter.mp hv).2
      have hdvd : p ∣ Ideal.absNorm v.asIdeal := hmf ▸ Nat.minFac_dvd _
      exact hnorm_of_above ⟨v, hdvd⟩
    refine ⟨hnorm_fib, ?_⟩
    have : Finite (PrimesAbove (CycField q) p) := finite_primesAbove (CycField q) hp_prime
    let : Fintype (PrimesAbove (CycField q) p) := Fintype.ofFinite _
    have hcard_above : Fintype.card (PrimesAbove (CycField q) p) = q.totient := by
      rw [Stage7DedekindZeta.cyc_card_primesAbove_eq_numPrimesAbove hp_prime hndvd, hnum]
    rw [← hcard_above]
    refine Finset.card_bij
      (fun v hv =>
        (⟨v, (Finset.mem_filter.mp hv).2 ▸ Nat.minFac_dvd _⟩ : PrimesAbove (CycField q) p))
      (fun _ _ => Finset.mem_univ _)
      (fun _ _ _ _ h => congrArg Subtype.val h)
      (fun w _ => ?_)
    refine ⟨w.1, ?_, Subtype.ext rfl⟩
    have hwnorm : Ideal.absNorm w.1.asIdeal = p := hnorm_of_above w
    have hwmf : (Ideal.absNorm w.1.asIdeal).minFac = p := by
      rw [hwnorm]; exact hp_prime.minFac_eq
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨mem_primeIdealsUpTo.mpr (by rw [hwnorm]; exact hp_le),
      by rw [hwmf]; exact hndvd, by rw [hwmf]; exact hp_mod⟩, hwmf⟩
  constructor
  · rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    unfold Stage2DirichletAP.chebyshevThetaAP
    rw [← Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨hnorm, hcard⟩ := hfiber p hp
    calc ∑ v ∈ S_split.filter (fun v => (Ideal.absNorm v.asIdeal).minFac = p),
            Real.log (Ideal.absNorm v.asIdeal : ℝ)
        = ∑ _v ∈ S_split.filter (fun v => (Ideal.absNorm v.asIdeal).minFac = p), Real.log (p : ℝ) :=
            Finset.sum_congr rfl fun v hv => by rw [hnorm v hv]
      _ = ((S_split.filter (fun v => (Ideal.absNorm v.asIdeal).minFac = p)).card : ℝ) *
            Real.log (p : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = (q.totient : ℝ) * Real.log (p : ℝ) := by rw [hcard]
  · rw [Finset.card_eq_sum_card_fiberwise hmaps]
    unfold Stage2DirichletAP.primeCountAP
    calc ∑ p ∈ P_split, (S_split.filter (fun v => (Ideal.absNorm v.asIdeal).minFac = p)).card
        = ∑ _p ∈ P_split, q.totient := Finset.sum_congr rfl fun p hp => (hfiber p hp).2
      _ = P_split.card * q.totient := by rw [Finset.sum_const, smul_eq_mul]
      _ = q.totient * P_split.card := mul_comm _ _

/-- Helper: upper bound on the cardinality of all non-totally-split (ramified or `f ≥ 2`)
prime ideals of `𝓞 (CycField q)` of norm `≤ ⌊x⌋₊`. -/
private lemma rest_primeIdeals_card_le (q : ℕ) [NeZero q] (x : ℝ) :
    let S_rest := (primeIdealsUpTo (CycField q) x).filter fun v =>
      ¬ (¬ ((Ideal.absNorm v.asIdeal).minFac ∣ q) ∧ (Ideal.absNorm v.asIdeal).minFac ≡ 1 [MOD q])
    S_rest.card ≤ q.totient * (Nat.sqrt ⌊x⌋₊ + q.primeFactors.card) := by
  classical
  intro S_rest
  set P_bad : Finset ℕ := ((Finset.Icc 1 (Nat.sqrt ⌊x⌋₊)).filter Nat.Prime) ∪ q.primeFactors
  have hmaps : ∀ v ∈ S_rest, (Ideal.absNorm v.asIdeal).minFac ∈ P_bad := by
    intro v hv
    obtain ⟨hv_up, hv_not⟩ := Finset.mem_filter.mp hv
    have hv_norm : Ideal.absNorm v.asIdeal ≤ ⌊x⌋₊ := mem_primeIdealsUpTo.mp hv_up
    set p : ℕ := (Ideal.absNorm v.asIdeal).minFac
    have hp_prime : p.Prime := minFac_absNorm_prime v
    by_cases hdvd : p ∣ q
    · exact Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp_prime, hdvd, NeZero.ne q⟩)
    · have hnotmod : ¬ (p ≡ 1 [MOD q]) := fun hmod => hv_not ⟨hdvd, hmod⟩
      have hcop : Nat.Coprime p q := hp_prime.coprime_iff_not_dvd.mpr hdvd
      have hf_ne1 : resDeg q p hcop ≠ 1 := fun hf1 =>
        hnotmod ((Stage4ClassFieldTheory.resDeg_eq_one_iff hcop).mp hf1)
      have hf_ge2 : 2 ≤ resDeg q p hcop := by
        have := Stage4ClassFieldTheory.resDeg_pos hcop; omega
      have hnorm_eq : Ideal.absNorm v.asIdeal = p ^ resDeg q p hcop :=
        Stage7DedekindZeta.cyc_absNorm_eq_pow_resDeg hp_prime hdvd ⟨v, Nat.minFac_dvd _⟩
      have hp_sq_le : p * p ≤ ⌊x⌋₊ := by
        calc p * p = p ^ 2 := (sq p).symm
          _ ≤ p ^ resDeg q p hcop := Nat.pow_le_pow_right hp_prime.pos hf_ge2
          _ = Ideal.absNorm v.asIdeal := hnorm_eq.symm
          _ ≤ ⌊x⌋₊ := hv_norm
      have hp_le_sqrt : p ≤ Nat.sqrt ⌊x⌋₊ := Nat.le_sqrt.mpr hp_sq_le
      exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp_prime.one_le, hp_le_sqrt⟩, hp_prime⟩)
  have hfib_le : ∀ p ∈ P_bad,
      (S_rest.filter (fun v => (Ideal.absNorm v.asIdeal).minFac = p)).card ≤ q.totient := by
    intro p hp_mem
    have hp_prime : p.Prime := by
      rcases Finset.mem_union.mp hp_mem with h1 | h2
      · exact (Finset.mem_filter.mp h1).2
      · exact Nat.prime_of_mem_primeFactors h2
    have : Finite (PrimesAbove (CycField q) p) := finite_primesAbove (CycField q) hp_prime
    let : Fintype (PrimesAbove (CycField q) p) := Fintype.ofFinite _
    have hcard_le : Fintype.card (PrimesAbove (CycField q) p) ≤ q.totient := by
      rw [← Nat.card_eq_fintype_card, ← Stage4ClassFieldTheory.cyc_finrank q]
      exact Stage7DedekindZeta.card_primesAbove_le_finrank (CycField q) hp_prime
    refine le_trans ?_ hcard_le
    by_cases hne : (S_rest.filter (fun v => (Ideal.absNorm v.asIdeal).minFac = p)).Nonempty
    · obtain ⟨v₀, hv₀⟩ := hne
      have hd₀ : p ∣ Ideal.absNorm v₀.asIdeal := (Finset.mem_filter.mp hv₀).2 ▸ Nat.minFac_dvd _
      refine Finset.card_le_card_of_injOn
        (fun v => if hd : p ∣ Ideal.absNorm v.asIdeal then (⟨v, hd⟩ : PrimesAbove (CycField q) p)
          else ⟨v₀, hd₀⟩)
        (fun _ _ => Finset.mem_univ _) ?_
      intro v₁ hv₁ v₂ hv₂ hEq
      have hd₁ : p ∣ Ideal.absNorm v₁.asIdeal := (Finset.mem_filter.mp hv₁).2 ▸ Nat.minFac_dvd _
      have hd₂ : p ∣ Ideal.absNorm v₂.asIdeal := (Finset.mem_filter.mp hv₂).2 ▸ Nat.minFac_dvd _
      simp only [dif_pos hd₁, dif_pos hd₂] at hEq
      exact congrArg Subtype.val hEq
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
      exact Nat.zero_le _
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hPbad_card : P_bad.card ≤ Nat.sqrt ⌊x⌋₊ + q.primeFactors.card := by
    calc P_bad.card
        ≤ ((Finset.Icc 1 (Nat.sqrt ⌊x⌋₊)).filter Nat.Prime).card + q.primeFactors.card :=
          Finset.card_union_le _ _
      _ ≤ (Finset.Icc 1 (Nat.sqrt ⌊x⌋₊)).card + q.primeFactors.card :=
          Nat.add_le_add_right (Finset.card_filter_le _ _) _
      _ = Nat.sqrt ⌊x⌋₊ + q.primeFactors.card := by simp [Nat.card_Icc]
  calc ∑ p ∈ P_bad, (S_rest.filter (fun v => (Ideal.absNorm v.asIdeal).minFac = p)).card
      ≤ ∑ _p ∈ P_bad, q.totient := Finset.sum_le_sum hfib_le
    _ = P_bad.card * q.totient := by rw [Finset.sum_const, smul_eq_mul]
    _ = q.totient * P_bad.card := mul_comm _ _
    _ ≤ q.totient * (Nat.sqrt ⌊x⌋₊ + q.primeFactors.card) := Nat.mul_le_mul_left _ hPbad_card

/-- Exact comparison band for `primeIdealTheta (CycField q) x`:
`0 ≤ primeIdealTheta (CycField q) x - φ(q) * θ(x; q, 1) ≤ φ(q) * (√x + ω(q)) * log x`
for every `x ≥ 1`. -/
theorem primeIdealTheta_cyclotomic_band (q : ℕ) [NeZero q] {x : ℝ} (hx : 1 ≤ x) :
    (q.totient : ℝ) * Stage2DirichletAP.chebyshevThetaAP q 1 x ≤
      primeIdealTheta (CycField q) x ∧
    primeIdealTheta (CycField q) x ≤
      (q.totient : ℝ) * Stage2DirichletAP.chebyshevThetaAP q 1 x +
        (q.totient : ℝ) * (Real.sqrt x + (q.primeFactors.card : ℝ)) * Real.log x := by
  classical
  let P : HeightOneSpectrum (𝓞 (CycField q)) → Prop := fun v =>
    ¬ ((Ideal.absNorm v.asIdeal).minFac ∣ q) ∧ (Ideal.absNorm v.asIdeal).minFac ≡ 1 [MOD q]
  have hsplit : primeIdealTheta (CycField q) x =
      (∑ v ∈ (primeIdealsUpTo (CycField q) x).filter P, Real.log (Ideal.absNorm v.asIdeal : ℝ)) +
      (∑ v ∈ (primeIdealsUpTo (CycField q) x).filter (fun v => ¬ P v),
        Real.log (Ideal.absNorm v.asIdeal : ℝ)) := by
    unfold primeIdealTheta
    exact (Finset.sum_filter_add_sum_filter_not _ P _).symm
  have hmain := (split_primeIdeals_exact_eval q x).1
  have hrest_nn : 0 ≤ ∑ v ∈ (primeIdealsUpTo (CycField q) x).filter (fun v => ¬ P v),
      Real.log (Ideal.absNorm v.asIdeal : ℝ) :=
    Finset.sum_nonneg fun v _ => Real.log_natCast_nonneg _
  have hrest_le :
      (∑ v ∈ (primeIdealsUpTo (CycField q) x).filter (fun v => ¬ P v),
        Real.log (Ideal.absNorm v.asIdeal : ℝ)) ≤
      (q.totient : ℝ) * (Real.sqrt x + (q.primeFactors.card : ℝ)) * Real.log x := by
    have hlog_le : ∀ v ∈ (primeIdealsUpTo (CycField q) x).filter (fun v => ¬ P v),
        Real.log (Ideal.absNorm v.asIdeal : ℝ) ≤ Real.log x := by
      intro v hv
      have hpos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
        exact_mod_cast (Nat.zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm v))
      have hle : (Ideal.absNorm v.asIdeal : ℝ) ≤ x :=
        le_trans (by exact_mod_cast mem_primeIdealsUpTo.mp (Finset.mem_filter.mp hv).1)
          (Nat.floor_le (by linarith))
      exact Real.log_le_log hpos hle
    have hcard_R : (((primeIdealsUpTo (CycField q) x).filter (fun v => ¬ P v)).card : ℝ) ≤
        (q.totient : ℝ) * (Real.sqrt x + (q.primeFactors.card : ℝ)) := by
      have hcard_nat := rest_primeIdeals_card_le q x
      have hcard_cast : (((primeIdealsUpTo (CycField q) x).filter (fun v => ¬ P v)).card : ℝ) ≤
          (q.totient : ℝ) * ((Nat.sqrt ⌊x⌋₊ : ℝ) + (q.primeFactors.card : ℝ)) := by
        exact_mod_cast hcard_nat
      have hsqrt_le : (Nat.sqrt ⌊x⌋₊ : ℝ) ≤ Real.sqrt x := by
        refine Real.le_sqrt_of_sq_le ?_
        have h1 : (Nat.sqrt ⌊x⌋₊ : ℝ) ^ 2 ≤ (⌊x⌋₊ : ℝ) := by
          exact_mod_cast (show (Nat.sqrt ⌊x⌋₊) ^ 2 ≤ ⌊x⌋₊ by rw [sq]; exact Nat.sqrt_le ⌊x⌋₊)
        exact h1.trans (Nat.floor_le (by linarith))
      have htot_nn : (0 : ℝ) ≤ (q.totient : ℝ) := Nat.cast_nonneg _
      nlinarith
    calc ∑ v ∈ (primeIdealsUpTo (CycField q) x).filter (fun v => ¬ P v),
            Real.log (Ideal.absNorm v.asIdeal : ℝ)
        ≤ ∑ _v ∈ (primeIdealsUpTo (CycField q) x).filter (fun v => ¬ P v), Real.log x :=
          Finset.sum_le_sum hlog_le
      _ = (((primeIdealsUpTo (CycField q) x).filter (fun v => ¬ P v)).card : ℝ) * Real.log x := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (q.totient : ℝ) * (Real.sqrt x + (q.primeFactors.card : ℝ)) * Real.log x :=
          mul_le_mul_of_nonneg_right hcard_R (Real.log_nonneg hx)
  rw [hsplit, hmain]
  exact ⟨by linarith, by linarith⟩

/-- Exact comparison band for `primeIdealPi (CycField q) x`:
`φ(q) * π(x; q, 1) ≤ π_{ℚ(ζ_q)}(x) ≤ φ(q) * π(x; q, 1) + φ(q) * (√x + ω(q))` for `x ≥ 0`. -/
theorem primeIdealPi_cyclotomic_band (q : ℕ) [NeZero q] {x : ℝ} (hx : 0 ≤ x) :
    (q.totient : ℝ) * (Stage2DirichletAP.primeCountAP q 1 x : ℝ) ≤
      (primeIdealPi (CycField q) x : ℝ) ∧
    (primeIdealPi (CycField q) x : ℝ) ≤
      (q.totient : ℝ) * (Stage2DirichletAP.primeCountAP q 1 x : ℝ) +
        (q.totient : ℝ) * (Real.sqrt x + (q.primeFactors.card : ℝ)) := by
  classical
  let P : HeightOneSpectrum (𝓞 (CycField q)) → Prop := fun v =>
    ¬ ((Ideal.absNorm v.asIdeal).minFac ∣ q) ∧ (Ideal.absNorm v.asIdeal).minFac ≡ 1 [MOD q]
  have hsplit_nat : primeIdealPi (CycField q) x =
      ((primeIdealsUpTo (CycField q) x).filter P).card +
      ((primeIdealsUpTo (CycField q) x).filter (fun v => ¬ P v)).card := by
    unfold primeIdealPi
    have h := Finset.sum_filter_add_sum_filter_not (primeIdealsUpTo (CycField q) x) P
      (fun _ => (1 : ℕ))
    simpa only [Finset.sum_const, smul_eq_mul, mul_one] using h.symm
  have hmain_nat := (split_primeIdeals_exact_eval q x).2
  have hrest_nat := rest_primeIdeals_card_le q x
  have hsplit_R : (primeIdealPi (CycField q) x : ℝ) =
      (q.totient : ℝ) * (Stage2DirichletAP.primeCountAP q 1 x : ℝ) +
      (((primeIdealsUpTo (CycField q) x).filter (fun v => ¬ P v)).card : ℝ) := by
    rw [hsplit_nat, hmain_nat]
    push_cast; rfl
  have hsqrt_le : (Nat.sqrt ⌊x⌋₊ : ℝ) ≤ Real.sqrt x := by
    refine Real.le_sqrt_of_sq_le ?_
    have h1 : (Nat.sqrt ⌊x⌋₊ : ℝ) ^ 2 ≤ (⌊x⌋₊ : ℝ) := by
      exact_mod_cast (show (Nat.sqrt ⌊x⌋₊) ^ 2 ≤ ⌊x⌋₊ by rw [sq]; exact Nat.sqrt_le ⌊x⌋₊)
    exact h1.trans (Nat.floor_le hx)
  have hrest_R : (((primeIdealsUpTo (CycField q) x).filter (fun v => ¬ P v)).card : ℝ) ≤
      (q.totient : ℝ) * (Real.sqrt x + (q.primeFactors.card : ℝ)) := by
    have h1 : (((primeIdealsUpTo (CycField q) x).filter (fun v => ¬ P v)).card : ℝ) ≤
        (q.totient : ℝ) * ((Nat.sqrt ⌊x⌋₊ : ℝ) + (q.primeFactors.card : ℝ)) := by
      exact_mod_cast hrest_nat
    have htot_nn : (0 : ℝ) ≤ (q.totient : ℝ) := Nat.cast_nonneg _
    nlinarith
  rw [hsplit_R]
  exact ⟨by linarith [Nat.cast_nonneg (α := ℝ) (((primeIdealsUpTo (CycField q) x).filter (fun v => ¬ P v)).card)],
    by linarith⟩

/-- Helper: elementary decay bound `Real.sqrt x * Real.log x ≤ 4 * x * Real.exp (-c * Real.sqrt (Real.log x))`
for `0 < c ≤ 1 / 4` and `2 ≤ x`. -/
private lemma sqrt_mul_log_le_four_mul_exp_neg_sqrt_local {c x : ℝ} (hc : 0 < c) (hc4 : c ≤ 1 / 4)
    (hx : 2 ≤ x) :
    Real.sqrt x * Real.log x ≤ 4 * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  have hx0 : 0 < x := by linarith
  set Lx : ℝ := Real.log x
  have hLx_pos : 0 < Lx := Real.log_pos (by linarith)
  have hsqrt_eq : Real.sqrt x * Lx = x * (Lx * Real.exp (-(1 / 2) * Lx)) := by
    have h1 : Real.exp (-(1 / 2) * Lx) = (Real.sqrt x)⁻¹ := by
      rw [show -(1 / 2) * Lx = -(Real.log x / 2) by ring, Real.exp_neg,
        ← Real.log_sqrt hx0.le, Real.exp_log (Real.sqrt_pos.mpr hx0)]
    rw [h1]
    have hsq_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have hmul : x * (Real.sqrt x)⁻¹ = Real.sqrt x := by
      rw [← div_eq_mul_inv, div_eq_iff hsq_pos.ne', Real.mul_self_sqrt hx0.le]
    calc Real.sqrt x * Lx = (x * (Real.sqrt x)⁻¹) * Lx := by rw [hmul]
      _ = x * (Lx * (Real.sqrt x)⁻¹) := by ring
  have hkey : Lx * Real.exp (-(1 / 2) * Lx) ≤ 4 * Real.exp (-c * Real.sqrt Lx) := by
    by_cases hL1 : 1 ≤ Lx
    · have hsq_le : Real.sqrt Lx ≤ Lx := by
        have h1 : Real.sqrt Lx * Real.sqrt Lx = Lx := Real.mul_self_sqrt hLx_pos.le
        have h2 : 1 ≤ Real.sqrt Lx := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hL1
        nlinarith
      have hexp_le : Real.exp (-(1 / 4) * Lx) ≤ Real.exp (-c * Real.sqrt Lx) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_nonneg Lx])
      have hlin : Lx * Real.exp (-(1 / 4) * Lx) ≤ 4 := by
        have h1 := Real.add_one_le_exp ((1 / 4 : ℝ) * Lx)
        have h2 : Lx / 4 ≤ Real.exp ((1 / 4 : ℝ) * Lx) := by linarith
        rw [show -(1 / 4 : ℝ) * Lx = -((1 / 4 : ℝ) * Lx) by ring, Real.exp_neg, ← div_eq_mul_inv,
          div_le_iff₀ (Real.exp_pos _)]
        linarith
      have hsplit : Real.exp (-(1 / 2) * Lx) = Real.exp (-(1 / 4) * Lx) * Real.exp (-(1 / 4) * Lx) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hsplit, ← mul_assoc]
      calc (Lx * Real.exp (-(1 / 4) * Lx)) * Real.exp (-(1 / 4) * Lx)
          ≤ 4 * Real.exp (-(1 / 4) * Lx) := mul_le_mul_of_nonneg_right hlin (Real.exp_pos _).le
        _ ≤ 4 * Real.exp (-c * Real.sqrt Lx) := mul_le_mul_of_nonneg_left hexp_le (by norm_num)
    · push Not at hL1
      have hsq_le1 : Real.sqrt Lx ≤ 1 := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hL1.le
      have h1 : Real.exp (-(1 / 2) * Lx) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have h2 : Real.exp (-(1 / 4 : ℝ)) ≤ Real.exp (-c * Real.sqrt Lx) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.sqrt_nonneg Lx])
      have h3 : (1 / 4 : ℝ) ≤ Real.exp (-(1 / 4 : ℝ)) := by linarith [Real.add_one_le_exp (-(1 / 4 : ℝ))]
      calc Lx * Real.exp (-(1 / 2) * Lx) ≤ 1 * 1 := mul_le_mul hL1.le h1 (Real.exp_pos _).le zero_le_one
        _ = 4 * (1 / 4) := by norm_num
        _ ≤ 4 * Real.exp (-c * Real.sqrt Lx) := by linarith
  rw [hsqrt_eq]
  have := mul_le_mul_of_nonneg_left hkey hx0.le
  linarith

/-- **UNCONDITIONAL EFFECTIVE PRIME IDEAL CHEBYSHEV THEOREM FOR `ℚ(ζ_q)` (`0` ASSUMPTIONS!)**:
`∃ c > 0, ∃ C > 0, ∀ x ≥ 2, |∑_{N(𝔭) ≤ x} log N(𝔭) - x| ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x))`. -/
theorem effective_prime_ideal_theta_cyclotomic (q : ℕ) [NeZero q] :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 2 ≤ x →
        |primeIdealTheta (CycField q) x - x| ≤
          C * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c₁, hc₁, C₁, hC₁, hth⟩ :=
    Stage8ExplicitPrimeBounds.effective_pnt_thetaAP_sqrt (Nat.coprime_one_left q)
  set c : ℝ := min c₁ (1 / 4)
  have hc_pos : 0 < c := lt_min hc₁ (by norm_num)
  have hphi_pos : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  set C : ℝ := (q.totient : ℝ) * (C₁ + 4 * (1 + (q.primeFactors.card : ℝ)))
  refine ⟨c, hc_pos, C, by positivity, fun x hx2 => ?_⟩
  have hx0 : 0 < x := by linarith
  have hsq1 : (1 : ℝ) ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by linarith)
  have hband := primeIdealTheta_cyclotomic_band q (by linarith : 1 ≤ x)
  have hmain : |(q.totient : ℝ) * Stage2DirichletAP.chebyshevThetaAP q 1 x - x| ≤
      (q.totient : ℝ) * C₁ * x * Real.exp (-c * Real.sqrt (Real.log x)) := by
    have h1 := hth x hx2
    have h2 : |(q.totient : ℝ) * Stage2DirichletAP.chebyshevThetaAP q 1 x - x| =
        (q.totient : ℝ) * |Stage2DirichletAP.chebyshevThetaAP q 1 x - x / (q.totient : ℝ)| := by
      calc |(q.totient : ℝ) * Stage2DirichletAP.chebyshevThetaAP q 1 x - x|
          = |(q.totient : ℝ) * (Stage2DirichletAP.chebyshevThetaAP q 1 x - x / (q.totient : ℝ))| := by
            congr 1
            field_simp [hphi_pos.ne']
        _ = (q.totient : ℝ) * |Stage2DirichletAP.chebyshevThetaAP q 1 x - x / (q.totient : ℝ)| := by
            rw [abs_mul, abs_of_pos hphi_pos]
    rw [h2]
    have hmon : Real.exp (-c₁ * Real.sqrt (Real.log x)) ≤ Real.exp (-c * Real.sqrt (Real.log x)) :=
      Real.exp_le_exp.mpr (by nlinarith [min_le_left c₁ (1 / 4 : ℝ), Real.sqrt_nonneg (Real.log x)])
    calc (q.totient : ℝ) * |Stage2DirichletAP.chebyshevThetaAP q 1 x - x / (q.totient : ℝ)|
        ≤ (q.totient : ℝ) * (C₁ * x * Real.exp (-c₁ * Real.sqrt (Real.log x))) :=
          mul_le_mul_of_nonneg_left h1 hphi_pos.le
      _ ≤ (q.totient : ℝ) * (C₁ * x * Real.exp (-c * Real.sqrt (Real.log x))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmon (by positivity)) hphi_pos.le
      _ = (q.totient : ℝ) * C₁ * x * Real.exp (-c * Real.sqrt (Real.log x)) := by ring
  have herr : |primeIdealTheta (CycField q) x -
      (q.totient : ℝ) * Stage2DirichletAP.chebyshevThetaAP q 1 x| ≤
      (q.totient : ℝ) * (4 * (1 + (q.primeFactors.card : ℝ))) * x *
        Real.exp (-c * Real.sqrt (Real.log x)) := by
    rw [abs_of_nonneg (sub_nonneg.mpr hband.1)]
    have hrem : primeIdealTheta (CycField q) x -
        (q.totient : ℝ) * Stage2DirichletAP.chebyshevThetaAP q 1 x ≤
        (q.totient : ℝ) * (Real.sqrt x + (q.primeFactors.card : ℝ)) * Real.log x := by
      linarith [hband.2]
    have hsum_le : Real.sqrt x + (q.primeFactors.card : ℝ) ≤
        (1 + (q.primeFactors.card : ℝ)) * Real.sqrt x := by
      nlinarith [Nat.cast_nonneg (α := ℝ) q.primeFactors.card]
    have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have hdecay := sqrt_mul_log_le_four_mul_exp_neg_sqrt_local hc_pos (min_le_right _ _) hx2
    calc primeIdealTheta (CycField q) x -
          (q.totient : ℝ) * Stage2DirichletAP.chebyshevThetaAP q 1 x
        ≤ (q.totient : ℝ) * (Real.sqrt x + (q.primeFactors.card : ℝ)) * Real.log x := hrem
      _ ≤ (q.totient : ℝ) * ((1 + (q.primeFactors.card : ℝ)) * Real.sqrt x) * Real.log x :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum_le hphi_pos.le) hlog_nn
      _ = (q.totient : ℝ) * (1 + (q.primeFactors.card : ℝ)) * (Real.sqrt x * Real.log x) := by ring
      _ ≤ (q.totient : ℝ) * (1 + (q.primeFactors.card : ℝ)) *
            (4 * x * Real.exp (-c * Real.sqrt (Real.log x))) :=
          mul_le_mul_of_nonneg_left hdecay (by positivity)
      _ = (q.totient : ℝ) * (4 * (1 + (q.primeFactors.card : ℝ))) * x *
            Real.exp (-c * Real.sqrt (Real.log x)) := by ring
  have htri : |primeIdealTheta (CycField q) x - x| ≤
      |primeIdealTheta (CycField q) x - (q.totient : ℝ) * Stage2DirichletAP.chebyshevThetaAP q 1 x| +
      |(q.totient : ℝ) * Stage2DirichletAP.chebyshevThetaAP q 1 x - x| := by
    simpa [sub_add_sub_cancel] using abs_add_le
      (primeIdealTheta (CycField q) x - (q.totient : ℝ) * Stage2DirichletAP.chebyshevThetaAP q 1 x)
      ((q.totient : ℝ) * Stage2DirichletAP.chebyshevThetaAP q 1 x - x)
  dsimp only [C]
  linarith

/-- **UNCONDITIONAL PRIME IDEAL COUNTING ASYMPTOTIC FOR `ℚ(ζ_q)` (`0` ASSUMPTIONS!)**:
`#{𝔭 : HeightOneSpectrum (𝓞 (CyclotomicField q ℚ)) | N(𝔭) ≤ x} / (x / Real.log x) → 1`. -/
theorem prime_ideal_pi_asymp_cyclotomic (q : ℕ) [NeZero q] :
    Tendsto (fun x : ℝ => (primeIdealPi (CycField q) x : ℝ) / (x / Real.log x)) atTop (𝓝 1) := by
  have hphi_pos : (0 : ℝ) < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hmain : Tendsto
      (fun x : ℝ => ((q.totient : ℝ) * (Stage2DirichletAP.primeCountAP q 1 x : ℝ)) / (x / Real.log x))
      atTop (𝓝 1) := by
    refine (Stage7PNTInAP.pnt_primeCountAP_real_asymp (Nat.coprime_one_left q)).congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hlog0 : 0 < Real.log x := Real.log_pos hx
    field_simp [hx0.ne', hlog0.ne', hphi_pos.ne']
  have hlog_div_sqrt : Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    exact h.congr fun x => by rw [Real.sqrt_eq_rpow]
  have hlog_div_x : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
    exact h.congr' (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with x _; rw [Real.rpow_one])
  have herr_zero : Tendsto
      (fun x : ℝ =>
        ((q.totient : ℝ) * (Real.sqrt x + (q.primeFactors.card : ℝ))) / (x / Real.log x))
      atTop (𝓝 0) := by
    have hcomb : Tendsto
        (fun x : ℝ =>
          (q.totient : ℝ) * (Real.log x / Real.sqrt x + (q.primeFactors.card : ℝ) * (Real.log x / x)))
        atTop (𝓝 0) := by
      have h1 := hlog_div_sqrt.add (hlog_div_x.const_mul (q.primeFactors.card : ℝ))
      rw [mul_zero, add_zero] at h1
      simpa [mul_zero] using h1.const_mul (q.totient : ℝ)
    refine hcomb.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hsq0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have hlog0 : 0 < Real.log x := Real.log_pos hx
    have hsq_mul : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
    field_simp [hx0.ne', hsq0.ne', hlog0.ne']
    nlinarith [hsq_mul]
  have hupper : Tendsto
      (fun x : ℝ =>
        ((q.totient : ℝ) * (Stage2DirichletAP.primeCountAP q 1 x : ℝ)) / (x / Real.log x) +
        ((q.totient : ℝ) * (Real.sqrt x + (q.primeFactors.card : ℝ))) / (x / Real.log x))
      atTop (𝓝 1) := by
    simpa only [add_zero] using hmain.add herr_zero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hmain hupper ?_ ?_
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hden : 0 < x / Real.log x := div_pos (by linarith) (Real.log_pos hx)
    exact div_le_div_of_nonneg_right (primeIdealPi_cyclotomic_band q (by linarith)).1 hden.le
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hden : 0 < x / Real.log x := div_pos (by linarith) (Real.log_pos hx)
    rw [← add_div]
    exact div_le_div_of_nonneg_right (primeIdealPi_cyclotomic_band q (by linarith)).2 hden.le

/-- Natural-number variable version of the Prime Ideal Theorem for `ℚ(ζ_q)`:
`#{𝔭 | N(𝔭) ≤ n} / (n / Real.log n) → 1`. -/
theorem prime_ideal_pi_nat_asymp_cyclotomic (q : ℕ) [NeZero q] :
    Tendsto (fun n : ℕ => (primeIdealPi (CycField q) n : ℝ) / ((n : ℝ) / Real.log (n : ℝ)))
      atTop (𝓝 1) :=
  (prime_ideal_pi_asymp_cyclotomic q).comp tendsto_natCast_atTop_atTop

/-- **UNCONDITIONAL EFFECTIVE PRIME IDEAL THEOREM FOR `ℚ(ζ_q)` (`0` ASSUMPTIONS!)**:
simultaneously proving BOTH the effective de la Vallée Poussin Chebyshev error bound
`|∑_{N(𝔭) ≤ x} log N(𝔭) - x| ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x))`
AND the prime-ideal counting asymptotic `#{𝔭 | N(𝔭) ≤ x} / (x / Real.log x) → 1`! -/
theorem effective_prime_ideal_theorem_cyclotomic (q : ℕ) [NeZero q] :
    (∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 2 ≤ x →
        |primeIdealTheta (CycField q) x - x| ≤
          C * x * Real.exp (-c * Real.sqrt (Real.log x))) ∧
    Tendsto (fun x : ℝ => (primeIdealPi (CycField q) x : ℝ) / (x / Real.log x)) atTop (𝓝 1) :=
  ⟨effective_prime_ideal_theta_cyclotomic q, prime_ideal_pi_asymp_cyclotomic q⟩

end EffectivePrimeIdealTheorem

/-! ## Section 4: Master Unconditional Stage 9 Theorem -/

/-- **Master Unconditional Stage 9 Theorem (`0` ASSUMPTIONS!)**:
simultaneously packaging all three pillars for EVERY cyclotomic field `ℚ(ζ_q)` (`q ≥ 1`):
1. Analytic continuation, positive real residue at `s = 1`, and de la Vallée Poussin zero-free
   region for `ζ_{ℚ(ζ_q)}(s)` (and its entire regularization `cyclotomicDedekindZetaReg q`).
2. Effective Cyclotomic Chebotarev Density Theorem (`ψ`, `θ` with `exp(-c √(log x))` error and
   natural density `1 / |Gal(ℚ(ζ_q)/ℚ)|`), Effective Abelian Subfield Prime Splitting, and
   Effective Kronecker–Bauer Uniqueness.
3. Effective Prime Ideal Theorem for `ℚ(ζ_q)` (`θ_{ℚ(ζ_q)}(x) = x + O(x exp(-c √(log x)))` and
   `π_{ℚ(ζ_q)}(x) ~ x / log x`). -/
theorem stage9_cyclotomic_chebotarev_unconditional (q : ℕ) [NeZero q] :
    (DifferentiableOn ℂ (cyclotomicDedekindZeta q) ({1}ᶜ) ∧
      0 < (cyclotomicDedekindZetaResidue q).re ∧
      (cyclotomicDedekindZetaResidue q).im = 0 ∧
      ∃ c : ℝ, 0 < c ∧
        ∀ s : ℂ, 1 - c / Real.log (|s.im| + 2) ≤ s.re → s ≠ 1 →
          cyclotomicDedekindZeta q s ≠ 0) ∧
    (∀ σ : CycGal q,
      (∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
        ∀ x : ℝ, 2 ≤ x →
          |chebotarevPsi q σ x - x / (Fintype.card (CycGal q) : ℝ)| ≤
            C * x * Real.exp (-c * Real.sqrt (Real.log x))) ∧
      Tendsto (fun n : ℕ => (chebotarevPi q σ n : ℝ) / (Nat.primeCounting n : ℝ))
        atTop (𝓝 (1 / (Fintype.card (CycGal q) : ℝ)))) ∧
    (∀ H₁ H₂ : Subgroup (ZMod q)ˣ,
      HasNaturalDensity
          (symmDiff (SplitPrimes (cycFixedField q H₁)) (SplitPrimes (cycFixedField q H₂))) 0 ↔
        H₁ = H₂) ∧
    ((∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧
        ∀ x : ℝ, 2 ≤ x →
          |primeIdealTheta (CycField q) x - x| ≤
            C * x * Real.exp (-c * Real.sqrt (Real.log x))) ∧
      Tendsto (fun x : ℝ => (primeIdealPi (CycField q) x : ℝ) / (x / Real.log x)) atTop (𝓝 1)) :=
  ⟨⟨cyclotomicDedekindZeta_differentiableOn q,
    (cyclotomicDedekindZeta_residue_one q).2.1,
    (cyclotomicDedekindZeta_residue_one q).2.2.1,
    cyclotomicDedekindZeta_zeroFree q⟩,
   fun σ => ⟨effective_cyclotomic_chebotarev_psi q σ,
     effective_cyclotomic_chebotarev_pi_asymp q σ⟩,
   fun H₁ H₂ => effective_kronecker_bauer_abelian q H₁ H₂,
   effective_prime_ideal_theorem_cyclotomic q⟩

end RHDirect.Stage9CyclotomicChebotarev
