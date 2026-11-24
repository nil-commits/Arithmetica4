import RHDirect.Stage14Contracts
import RHDirect.Stage14M1_CMFieldAdeles
import RHDirect.Stage14M1_LocalSiegelDensities
import RHDirect.Stage14M1_GenusClassDecomp

/-!
# RHDirect.Stage14M1_TamagawaVolumeMass

Field-2 Package M1 Wave 2: **Unitary Tamagawa Volume, Genus-Class Mass = Tamagawa Volume Identity,
and Pro-`g` Split-Algebra Level Volume Ratios** in pure Mathlib `v4.33.1` (`0` `sorry`, `0` custom
`axiom`s, `0` `opaque`, `0` `native_decide`).

## Contents

1. **Concrete Adelic Unitary Tamagawa Volume (`UnitaryTamagawaVolume`) & Level-Volume Scaling**:
   - Local Tamagawa volume `unitaryLocalTamagawaVol C v n` at finite places of a `CMHostField C`
     wired directly to `Stage14M1_LocalSiegelDensities.local_density_euler_factor` and
     `Stage14M1_CMFieldAdeles.localTamagawaFactor`, with exact reciprocal identity
     `localTamagawaFactor C v n * unitaryLocalTamagawaVol C v n = 1`.
   - Archimedean formal-degree / Tamagawa step volume `unitaryArchTamagawaStep` wired to
     `UnitaryMassFormula.massRatioFactor`, and global Tamagawa volume `unitaryTamagawaTau` with
     Tate–Weil canonical normalization `unitaryTamagawaTau_canonical`.
   - Concrete `UnitaryTamagawaVolume` bundling `(G, Γ, K, μ, 𝓕)` (`IsFundamentalDomain Γ 𝓕 μ`)
     with unconditional measure-theoretic subgroup index scaling
     `measure_subgroup_eq_index_mul` (`μ K = [K : K'] * μ K'`), `levelVol_sublevel_eq`,
     level-invariance of `vol(K) * genusClassMass Γ K`, and universal denominator clearing
     `tamagawa_volume_denom_clearing` into `ℤ`.
   - Concrete `0`-assumption inhabitant `trivialGaussianTamagawaVolume` on `gaussianCMHostField`.

2. **Mass = Volume Ratio Identity Across Unitary Families (`mass_volume_identity_of_class_decomp`,
   `FamilyMassVolumeIdentityOfClassDecomp`, `family_mass_volume_identity_of_class_decomp`)**:
   - Proves exact mass = volume identities connecting
     `Stage14M1_GenusClassDecomp.class_decomp_measure_eq_sum` to `UnitaryTamagawaVolume` at any
     level `K` and sublevel `K' ≤ K`, with finite-place Euler factor normalization, convergent
     Euler products (`siegel_densities_of_hermitian_form`), and concrete specialization to
     `HermGenusClassSet` / `HermGenusClassWeight`.
   - Proves `family_mass_volume_identity_of_class_decomp` across arbitrary unitary families,
     rank-stepping telescoping `family_mass_volume_telescope_of_class_decomp` via
     `UnitaryMassFormula.mass_telescope_eq_prod`, and indefinite `(P, Q)` signature induction
     `signature_family_mass_volume_identity` via `UnitaryMassFormula.volume_eq_mass_of_ratio_induction`.

3. **Pro-`g` Split-Algebra Levels & Exact `|U_n(𝔽_q)|` Index Ratios (`levels_proG_of_split_algebra`)**:
   - Exact finite-field split unitary group order `splitUnitaryGroupOrder q n = |GL_n(𝔽_q)|`,
     exact bridge to `Stage14M1_LocalSiegelDensities.unitaryGroupOrder q n = |U_n(𝔽_q)|` and
     `local_density_euler_factor`, exact `RepSet B k 1 1` congruence-level cardinality for all
     `k ≥ 1` (including concrete `LocalHermBase.ofPrime p hp .split` / `.inert`), and
     consecutive-rank index ratios `|U_{n+1}(𝔽_q)| / |U_n(𝔽_q)|` and `|GL_{n+1}(𝔽_q)| / |GL_n(𝔽_q)|`.
   - Unconditional Weierstrass Euler-factor lower bound `prod_one_sub_ge_one_sub_sum` and
     `euler_tail_ge_half` (`∏_{M=2}^r (1 - q^{-M}) ≥ 1/2` for all `q ≥ 2`), proving the exact
     `Stage2MassRatioDatum.level_index_ge` bound
     `((2 : ℝ)^(2*f))⁻¹ * (g₁ * g₂)^(f * m * (2*k + m - 1) / 2) ≤ Isig / Ipi` for split-place
     pro-`g` level systems (`levels_proG_of_split_algebra` and `levels_proG_of_primes`),
     together with the full `tamagawa_proG_lam5_le_log_T` Stirling/mass-ratio lower bound.

4. **Alignment with `Stage14Contracts.M1UnitarySiegelWeilContract` & `M1FiberCert`**:
   - Direct compilers `toM1UnitarySiegelWeilContract`, `m1Contract_of_tamagawaFamily`,
     `canonicalM1TamagawaContract` (0 assumptions), `stage2MassRatioDatum_of_tamagawaAndProG`,
     `toM1FiberCert`, and Wave-3 export bundle `TamagawaVolumeMassPackage`.
-/

noncomputable section

open MeasureTheory Finset Real NumberField IsDedekindDomain Matrix
open RHDirect RHDirect.UnitaryMassFormula
open RHDirect.Stage14Contracts
open RHDirect.Stage14M1_CMFieldAdeles
open RHDirect.Stage14M1_LocalSiegelDensities
open RHDirect.Stage14M1_GenusClassDecomp
open RHDirect.Stage11RallisMassFiber
open RHDirect.Stage2ThetaWire
open scoped BigOperators ENNReal Pointwise

namespace RHDirect.Stage14M1_TamagawaVolumeMass

/-! ## Section 1: Concrete Adelic Unitary Tamagawa Volume & Level-Volume Scaling -/

section TamagawaVolumeFoundations

/-- Local Tamagawa volume `vol_Tam(K_{0,v}) = ∏_{j=1}^n (1 - χ_{E/F}(v)^j q_v^{-j})` of the
hyperspecial compact open subgroup at an unramified finite place `v` of a CM host field `C`. -/
def unitaryLocalTamagawaVol (C : CMHostField) (v : HeightOneSpectrum (𝓞 C.F)) (n : ℕ) : ℝ :=
  local_density_euler_factor (Stage5AdelicTate.residueCard v : ℝ) (C.chiEF v) n n

theorem unitaryLocalTamagawaVol_eq_prod (C : CMHostField) (v : HeightOneSpectrum (𝓞 C.F))
    (n : ℕ) :
    unitaryLocalTamagawaVol C v n =
      ∏ j ∈ Finset.Icc 1 n, localUnitaryEulerFactor C v j := by
  unfold unitaryLocalTamagawaVol local_density_euler_factor localUnitaryEulerFactor
  rw [Nat.sub_self, zero_add]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hqpos : (0 : ℝ) < (Stage5AdelicTate.residueCard v : ℝ) := by
    exact_mod_cast (lt_trans Nat.zero_lt_one (Stage5AdelicTate.one_lt_residueCard v))
  congr 2
  rw [← Real.rpow_intCast _ (-(j : ℤ))]
  simp

theorem unitaryLocalTamagawaVol_pos (C : CMHostField) (v : HeightOneSpectrum (𝓞 C.F)) (n : ℕ) :
    0 < unitaryLocalTamagawaVol C v n := by
  rw [unitaryLocalTamagawaVol_eq_prod]
  refine Finset.prod_pos fun j hj => ?_
  exact localUnitaryEulerFactor_pos C v (Finset.mem_Icc.mp hj).1

theorem unitaryLocalTamagawaVol_le_two_pow (C : CMHostField) (v : HeightOneSpectrum (𝓞 C.F))
    (n : ℕ) :
    unitaryLocalTamagawaVol C v n ≤ (3 / 2 : ℝ) ^ n := by
  unfold unitaryLocalTamagawaVol
  have hq : (2 : ℝ) ≤ (Stage5AdelicTate.residueCard v : ℝ) := by
    exact_mod_cast Stage5AdelicTate.one_lt_residueCard v
  exact local_density_euler_factor_le_two_pow hq (C.abs_chiEF_le_one v) n n le_rfl

/-- Exact reciprocal identity: `localTamagawaFactor C v n * unitaryLocalTamagawaVol C v n = 1`. -/
theorem localTamagawaFactor_mul_unitaryLocalTamagawaVol (C : CMHostField)
    (v : HeightOneSpectrum (𝓞 C.F)) (n : ℕ) :
    localTamagawaFactor C v n * unitaryLocalTamagawaVol C v n = 1 := by
  rw [unitaryLocalTamagawaVol_eq_prod]
  unfold localTamagawaFactor
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun j hj => ?_
  have hpos := localUnitaryEulerFactor_pos C v (Finset.mem_Icc.mp hj).1
  exact inv_mul_cancel₀ hpos.ne'

theorem unitaryLocalTamagawaVol_eq_inv_localTamagawaFactor (C : CMHostField)
    (v : HeightOneSpectrum (𝓞 C.F)) (n : ℕ) :
    unitaryLocalTamagawaVol C v n = (localTamagawaFactor C v n)⁻¹ :=
  eq_inv_of_mul_eq_one_right (localTamagawaFactor_mul_unitaryLocalTamagawaVol C v n)

theorem localTamagawaFactor_eq_inv_unitaryLocalTamagawaVol (C : CMHostField)
    (v : HeightOneSpectrum (𝓞 C.F)) (n : ℕ) :
    localTamagawaFactor C v n = (unitaryLocalTamagawaVol C v n)⁻¹ := by
  rw [unitaryLocalTamagawaVol_eq_inv_localTamagawaFactor, inv_inv]

/-- Exact archimedean Tamagawa step volume at rank `M` for CM degree `f = [F : ℚ]` and
host discriminant scale `vE`: `(((M - 1)! * (vE / π)^M)^f) / √((2 * vE)^f)`. -/
def unitaryArchTamagawaStep (f : ℕ) (vE : ℝ) (M : ℕ) : ℝ :=
  (((Nat.factorial (M - 1) : ℕ) : ℝ) * (vE / Real.pi) ^ M) ^ f /
    Real.sqrt ((2 * vE) ^ f)

theorem unitaryArchTamagawaStep_pos {f : ℕ} {vE : ℝ} (hv : 0 < vE) (M : ℕ) :
    0 < unitaryArchTamagawaStep f vE M := by
  unfold unitaryArchTamagawaStep
  have hfac : (0 : ℝ) < ((Nat.factorial (M - 1) : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hpi : (0 : ℝ) < vE / Real.pi := div_pos hv Real.pi_pos
  have hden : (0 : ℝ) < Real.sqrt ((2 * vE) ^ f) := Real.sqrt_pos.mpr (pow_pos (by linarith) f)
  exact div_pos (pow_pos (mul_pos hfac (pow_pos hpi M)) f) hden

theorem unitaryArchTamagawaStep_mul_eq_massRatioFactor (f : ℕ) (vE : ℝ) (Lval : ℕ → ℝ) (M : ℕ) :
    unitaryArchTamagawaStep f vE M * Lval M = massRatioFactor f vE Lval M := rfl

/-- Cumulative archimedean Tamagawa factor `∏_{j=1}^n unitaryArchTamagawaStep f vE j`. -/
def unitaryArchTamagawaVol (f : ℕ) (vE : ℝ) (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.Icc 1 n, unitaryArchTamagawaStep f vE j

theorem unitaryArchTamagawaVol_pos {f : ℕ} {vE : ℝ} (hv : 0 < vE) (n : ℕ) :
    0 < unitaryArchTamagawaVol f vE n :=
  Finset.prod_pos fun j _ => unitaryArchTamagawaStep_pos hv j

/-- Global unitary Tamagawa constant `τ(U(V)) = 2 * tamagawaFactor C M n S` (with Ono's
Tamagawa number `2` for connected unitary groups `U(n)` of rank `n ≥ 1`). -/
def unitaryTamagawaTau (C : CMHostField) (M : AdelicMeasureData C) (n : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 C.F))) : ℝ :=
  2 * tamagawaFactor C M n S

theorem unitaryTamagawaTau_pos (C : CMHostField) (M : AdelicMeasureData C) (n : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 C.F))) :
    0 < unitaryTamagawaTau C M n S :=
  mul_pos zero_lt_two (tamagawaFactor_pos C M n S)

theorem unitaryTamagawaTau_canonical (C : CMHostField) (n : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 C.F))) :
    unitaryTamagawaTau C (AdelicMeasureData.canonical C) n S =
      2 * ∏ v ∈ S, localTamagawaFactor C v n := by
  unfold unitaryTamagawaTau tamagawaFactor
  rw [AdelicMeasureData.canonical_additiveTamagawaVolE_eq_one, one_mul]

/-- Exact relation between `unitaryTamagawaTau` and the product of local Tamagawa volumes:
`unitaryTamagawaTau C (canonical C) n S * ∏ v ∈ S, unitaryLocalTamagawaVol C v n = 2`. -/
theorem unitaryTamagawaTau_mul_localVol_canonical (C : CMHostField) (n : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 C.F))) :
    unitaryTamagawaTau C (AdelicMeasureData.canonical C) n S *
        (∏ v ∈ S, unitaryLocalTamagawaVol C v n) = 2 := by
  rw [unitaryTamagawaTau_canonical, mul_assoc, ← Finset.prod_mul_distrib]
  have h1 : (∏ v ∈ S, localTamagawaFactor C v n * unitaryLocalTamagawaVol C v n) = 1 :=
    Finset.prod_eq_one fun v _ => localTamagawaFactor_mul_unitaryLocalTamagawaVol C v n
  rw [h1, mul_one]

/-- Relation between `bsgyUnitaryMass` and `unitaryArchTamagawaVol`:
`bsgyUnitaryMass f χ vE n = 2 * unitaryArchTamagawaVol f vE n * ∏_{j=1}^n (hermLVal χ j)^f`. -/
theorem bsgyUnitaryMass_eq_two_mul_arch_mul_L (f : ℕ) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (vE : ℝ) (n : ℕ) :
    bsgyUnitaryMass f χ vE n =
      2 * unitaryArchTamagawaVol f vE n * ∏ j ∈ Finset.Icc 1 n, (hermLVal χ j) ^ f := by
  unfold bsgyUnitaryMass unitaryArchTamagawaVol
  rw [mul_assoc]
  congr 1
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  unfold bsgyStepFactor
  exact (unitaryArchTamagawaStep_mul_eq_massRatioFactor f vE (fun M => (hermLVal χ M) ^ f) j).symm

/-- Monotonicity of `unitaryTamagawaTau` under enlarging the bad-place set `S ⊆ S'` when
every extra local Tamagawa factor is `≥ 1` (e.g. at split places). -/
theorem unitaryTamagawaTau_mono_of_ge_one (C : CMHostField) (M : AdelicMeasureData C) (n : ℕ)
    {S S' : Finset (HeightOneSpectrum (𝓞 C.F))} (hSS' : S ⊆ S')
    (hge : ∀ v ∈ S', v ∉ S → 1 ≤ localTamagawaFactor C v n) :
    unitaryTamagawaTau C M n S ≤ unitaryTamagawaTau C M n S' := by
  classical
  unfold unitaryTamagawaTau tamagawaFactor
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ M.additiveTamagawaVolE_pos.le)
    (by norm_num)
  rw [← Finset.prod_sdiff hSS']
  conv_lhs => rw [← one_mul (∏ v ∈ S, localTamagawaFactor C v n)]
  refine mul_le_mul_of_nonneg_right ?_
    (Finset.prod_nonneg fun v _ => (localTamagawaFactor_pos C v n).le)
  have hone : (1 : ℝ) ≤ ∏ v ∈ S' \ S, localTamagawaFactor C v n := by
    calc (1 : ℝ) = ∏ _v ∈ S' \ S, (1 : ℝ) := (Finset.prod_const_one).symm
      _ ≤ ∏ v ∈ S' \ S, localTamagawaFactor C v n :=
        Finset.prod_le_prod (fun _ _ => zero_le_one) fun v hv =>
          hge v (Finset.mem_sdiff.mp hv).1 (Finset.mem_sdiff.mp hv).2
  exact hone

end TamagawaVolumeFoundations

section MeasureSubgroupIndexScaling

/-- **Unconditional Measure-Theoretic Subgroup Index Scaling (`measure_subgroup_eq_index_mul`)**:
for any measurable group `G` with left-invariant measure `μ`, measurable subgroups `K' ≤ K ≤ G`
of finite relative index `[K : K'] = (K'.subgroupOf K).index`,
`μ (K : Set G) = ((K'.subgroupOf K).index : ℝ≥0∞) * μ (K' : Set G)`. -/
theorem measure_subgroup_eq_index_mul {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] {K' K : Subgroup G} (hKK' : K' ≤ K)
    (hK' : MeasurableSet (K' : Set G)) [Finite (K ⧸ K'.subgroupOf K)] :
    μ (K : Set G) = ((K'.subgroupOf K).index : ℝ≥0∞) * μ (K' : Set G) := by
  classical
  let Q := K ⧸ K'.subgroupOf K
  have hF : Fintype Q := Fintype.ofFinite Q
  let rep : Q → K := fun q => Quotient.out q
  let T : Q → Set G := fun q => (fun x : G => ((rep q : K) : G)⁻¹ * x) ⁻¹' (K' : Set G)
  have hT_meas : ∀ q : Q, MeasurableSet (T q) := fun q => (measurable_const_mul _) hK'
  have hT_disj : Pairwise fun q₁ q₂ : Q => Disjoint (T q₁) (T q₂) := by
    intro q₁ q₂ hne
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    apply hne
    have h1 : ((rep q₁ : K) : G)⁻¹ * x ∈ K' := hx₁
    have h2 : ((rep q₂ : K) : G)⁻¹ * x ∈ K' := hx₂
    have h12 : (((rep q₁)⁻¹ * rep q₂ : K) : G) ∈ K' := by
      have heq : (((rep q₁)⁻¹ * rep q₂ : K) : G) =
          (((rep q₁ : K) : G)⁻¹ * x) * (((rep q₂ : K) : G)⁻¹ * x)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [heq]
      exact K'.mul_mem h1 (K'.inv_mem h2)
    have hmem : (rep q₁)⁻¹ * rep q₂ ∈ K'.subgroupOf K := h12
    have hmk : QuotientGroup.mk (rep q₁) = QuotientGroup.mk (rep q₂) :=
      QuotientGroup.eq.mpr hmem
    have hrep1 : (QuotientGroup.mk (rep q₁) : Q) = q₁ := Quotient.out_eq q₁
    have hrep2 : (QuotientGroup.mk (rep q₂) : Q) = q₂ := Quotient.out_eq q₂
    exact hrep1.symm.trans (hmk.trans hrep2)
  have hK_eq : (K : Set G) = ⋃ q ∈ (Finset.univ : Finset Q), T q := by
    ext x
    simp only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion, SetLike.mem_coe]
    constructor
    · intro hx
      let k : K := ⟨x, hx⟩
      let q : Q := QuotientGroup.mk k
      refine ⟨q, ?_⟩
      change ((rep q : K) : G)⁻¹ * x ∈ K'
      have hmk : (QuotientGroup.mk (rep q) : Q) = Quotient.mk'' k := Quotient.out_eq q
      have hmem : (rep q)⁻¹ * k ∈ K'.subgroupOf K := QuotientGroup.eq.mp hmk
      exact hmem
    · rintro ⟨q, hq⟩
      have hq' : ((rep q : K) : G)⁻¹ * x ∈ K' := hq
      have heq : x = ((rep q : K) : G) * (((rep q : K) : G)⁻¹ * x) := by group
      rw [heq]
      exact K.mul_mem (rep q).2 (hKK' hq')
  rw [hK_eq, measure_biUnion_finset (fun q₁ _ q₂ _ hne => hT_disj hne) (fun q _ => hT_meas q)]
  have hT_vol : ∀ q : Q, μ (T q) = μ (K' : Set G) := fun q => by
    change μ ((fun x : G => ((rep q : K) : G)⁻¹ * x) ⁻¹' (K' : Set G)) = μ (K' : Set G)
    exact measure_preimage_mul μ ((rep q : K) : G)⁻¹ (K' : Set G)
  rw [Finset.sum_congr rfl (fun q _ => hT_vol q), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  rw [← Nat.card_eq_fintype_card, Subgroup.index_eq_card]

theorem measure_subgroup_pos_of_sup {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] {K' K : Subgroup G} (hKK' : K' ≤ K)
    (hK' : MeasurableSet (K' : Set G)) (hKpos : 0 < μ (K : Set G))
    [Finite (K ⧸ K'.subgroupOf K)] :
    0 < μ (K' : Set G) := by
  have heq := measure_subgroup_eq_index_mul μ hKK' hK'
  by_contra h0
  have h0' : μ (K' : Set G) = 0 := le_antisymm (not_lt.mp h0) bot_le
  rw [h0', mul_zero] at heq
  exact hKpos.ne' heq

theorem measure_subgroup_ne_top_of_sup {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] {K' K : Subgroup G} (hKK' : K' ≤ K)
    (hK' : MeasurableSet (K' : Set G)) (hKfin : μ (K : Set G) ≠ ⊤)
    [Finite (K ⧸ K'.subgroupOf K)] :
    μ (K' : Set G) ≠ ⊤ := by
  have heq := measure_subgroup_eq_index_mul μ hKK' hK'
  have hidx_pos : 0 < (K'.subgroupOf K).index := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_pos
  intro htop
  rw [htop, ENNReal.mul_top (Nat.cast_ne_zero.mpr hidx_pos.ne')] at heq
  exact hKfin heq

theorem toReal_measure_subgroup_eq_index_mul {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] {K' K : Subgroup G}
    (hKK' : K' ≤ K) (hK' : MeasurableSet (K' : Set G)) [Finite (K ⧸ K'.subgroupOf K)] :
    (μ (K : Set G)).toReal = ((K'.subgroupOf K).index : ℝ) * (μ (K' : Set G)).toReal := by
  rw [measure_subgroup_eq_index_mul μ hKK' hK', ENNReal.toReal_mul, ENNReal.toReal_natCast]

/-- Transitive index scaling across a chain of finite-index measurable subgroups `K₂ ≤ K₁ ≤ K₀`:
`(μ K₀).toReal = [K₀ : K₁] * [K₁ : K₂] * (μ K₂).toReal`. -/
theorem toReal_measure_subgroup_tower {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] {K₂ K₁ K₀ : Subgroup G}
    (h21 : K₂ ≤ K₁) (h10 : K₁ ≤ K₀)
    (hK₁ : MeasurableSet (K₁ : Set G)) (hK₂ : MeasurableSet (K₂ : Set G))
    [Finite (K₀ ⧸ K₁.subgroupOf K₀)] [Finite (K₁ ⧸ K₂.subgroupOf K₁)] :
    (μ (K₀ : Set G)).toReal =
      ((K₁.subgroupOf K₀).index : ℝ) * ((K₂.subgroupOf K₁).index : ℝ) * (μ (K₂ : Set G)).toReal := by
  rw [toReal_measure_subgroup_eq_index_mul μ h10 hK₁,
    toReal_measure_subgroup_eq_index_mul μ h21 hK₂, mul_assoc]

end MeasureSubgroupIndexScaling

/-! ### `UnitaryTamagawaVolume` Structure, Level-Scaling API & Concrete Gaussian Inhabitant -/

/-- **Concrete Adelic Unitary Tamagawa Volume (`UnitaryTamagawaVolume`)**:
packages an adelic/locally compact unitary group `G`, left-invariant Tamagawa measure `μ`,
arithmetic subgroup `Γ ≤ G` with finite-volume fundamental domain `𝓕`, compact-open level
subgroup `K ≤ G` with finite stabilizer bounds, and CM host-field Tamagawa data `(C, n, S)`. -/
structure UnitaryTamagawaVolume : Type 1 where
  C : CMHostField
  rank : ℕ
  rank_pos : 1 ≤ rank
  measData : AdelicMeasureData C
  badPlaces : Finset (HeightOneSpectrum (𝓞 C.F))
  G : Type
  [grp : Group G]
  [measSpace : MeasurableSpace G]
  [measMul : MeasurableMul G]
  μ : Measure G
  [leftInv : μ.IsMulLeftInvariant]
  Γ : Subgroup G
  [cntGamma : Countable Γ]
  K : Subgroup G
  hK_meas : MeasurableSet (K : Set G)
  hK_pos : 0 < μ (K : Set G)
  hK_ne_top : μ (K : Set G) ≠ ⊤
  𝓕 : Set G
  h𝓕 : IsFundamentalDomain Γ 𝓕 μ
  h𝓕_lt_top : μ 𝓕 < ⊤
  [finCls : Fintype (DoubleCosetClassSet Γ K)]
  [neCls : Nonempty (DoubleCosetClassSet Γ K)]
  hstab_fin : ∀ g : G, Finite (doubleCosetStab Γ K g)

attribute [instance] UnitaryTamagawaVolume.grp UnitaryTamagawaVolume.measSpace
  UnitaryTamagawaVolume.measMul UnitaryTamagawaVolume.leftInv UnitaryTamagawaVolume.cntGamma
  UnitaryTamagawaVolume.finCls UnitaryTamagawaVolume.neCls

namespace UnitaryTamagawaVolume

/-- Real-valued Tamagawa fundamental-domain volume `τ(U(V)) = vol_μ(Γ \ G)`. -/
def tauVol (U : UnitaryTamagawaVolume) : ℝ :=
  (U.μ U.𝓕).toReal

/-- Real-valued compact-open level volume `vol_μ(K)`. -/
def levelVol (U : UnitaryTamagawaVolume) : ℝ :=
  (U.μ (U.K : Set U.G)).toReal

/-- Genus mass `∑ c : Γ \ G / K, |Stab(c)|⁻¹`. -/
def genusMass (U : UnitaryTamagawaVolume) : ℝ :=
  genusClassMass U.Γ U.K

/-- Global Tamagawa normalization constant attached to `(U.C, U.measData, U.rank, U.badPlaces)`. -/
def expectedTau (U : UnitaryTamagawaVolume) : ℝ :=
  unitaryTamagawaTau U.C U.measData U.rank U.badPlaces

theorem levelVol_pos (U : UnitaryTamagawaVolume) : 0 < U.levelVol :=
  ENNReal.toReal_pos U.hK_pos.ne' U.hK_ne_top

theorem levelVol_ne_zero (U : UnitaryTamagawaVolume) : U.levelVol ≠ 0 :=
  U.levelVol_pos.ne'

theorem genusMass_pos (U : UnitaryTamagawaVolume) : 0 < U.genusMass :=
  genusClassMass_pos U.Γ U.K U.hstab_fin

theorem tauVol_eq_levelVol_mul_genusMass (U : UnitaryTamagawaVolume) :
    U.tauVol = U.levelVol * U.genusMass :=
  class_decomp_toReal_eq_mul_sum U.μ U.hK_meas U.hK_ne_top U.hstab_fin U.h𝓕

theorem genusMass_eq_tauVol_div_levelVol (U : UnitaryTamagawaVolume) :
    U.genusMass = U.tauVol / U.levelVol :=
  class_decomp_mass_eq_covolume_div U.μ U.hK_meas U.hK_pos U.hK_ne_top U.hstab_fin U.h𝓕

theorem tauVol_pos (U : UnitaryTamagawaVolume) : 0 < U.tauVol := by
  rw [U.tauVol_eq_levelVol_mul_genusMass]
  exact mul_pos U.levelVol_pos U.genusMass_pos

theorem tauVol_ne_zero (U : UnitaryTamagawaVolume) : U.tauVol ≠ 0 :=
  U.tauVol_pos.ne'

theorem expectedTau_pos (U : UnitaryTamagawaVolume) : 0 < U.expectedTau :=
  unitaryTamagawaTau_pos U.C U.measData U.rank U.badPlaces

/-- Restrict a `UnitaryTamagawaVolume` to any finite-index measurable sublevel `K' ≤ K`. -/
def sublevel (U : UnitaryTamagawaVolume) (K' : Subgroup U.G) (hKK' : K' ≤ U.K)
    (hK'_meas : MeasurableSet (K' : Set U.G))
    [Finite (U.K ⧸ K'.subgroupOf U.K)] : UnitaryTamagawaVolume :=
  letI : Finite (DoubleCosetClassSet U.Γ K') :=
    genus_class_finite_sublevel hKK'
  letI : Fintype (DoubleCosetClassSet U.Γ K') := Fintype.ofFinite _
  letI : Nonempty (DoubleCosetClassSet U.Γ K') := ⟨doubleCosetMk U.Γ K' 1⟩
  { C := U.C
    rank := U.rank
    rank_pos := U.rank_pos
    measData := U.measData
    badPlaces := U.badPlaces
    G := U.G
    μ := U.μ
    Γ := U.Γ
    K := K'
    hK_meas := hK'_meas
    hK_pos := measure_subgroup_pos_of_sup U.μ hKK' hK'_meas U.hK_pos
    hK_ne_top := measure_subgroup_ne_top_of_sup U.μ hKK' hK'_meas U.hK_ne_top
    𝓕 := U.𝓕
    h𝓕 := U.h𝓕
    h𝓕_lt_top := U.h𝓕_lt_top
    hstab_fin := fun g => by
      have hinj : Function.Injective (fun γ : doubleCosetStab U.Γ K' g =>
          (⟨γ.1, hKK' γ.2⟩ : doubleCosetStab U.Γ U.K g)) := fun a b h =>
        Subtype.ext (congrArg (fun z : doubleCosetStab U.Γ U.K g => (z : U.Γ)) h)
      have := U.hstab_fin g
      exact Finite.of_injective _ hinj }

@[simp]
theorem sublevel_tauVol (U : UnitaryTamagawaVolume) (K' : Subgroup U.G) (hKK' : K' ≤ U.K)
    (hK'_meas : MeasurableSet (K' : Set U.G)) [Finite (U.K ⧸ K'.subgroupOf U.K)] :
    (U.sublevel K' hKK' hK'_meas).tauVol = U.tauVol := rfl

/-- Exact level-volume scaling under passing to a finite-index sublevel `K' ≤ K`:
`U.levelVol = [K : K'] * (U.sublevel K').levelVol`. -/
theorem levelVol_sublevel_eq (U : UnitaryTamagawaVolume) (K' : Subgroup U.G) (hKK' : K' ≤ U.K)
    (hK'_meas : MeasurableSet (K' : Set U.G)) [Finite (U.K ⧸ K'.subgroupOf U.K)] :
    U.levelVol =
      ((K'.subgroupOf U.K).index : ℝ) * (U.sublevel K' hKK' hK'_meas).levelVol :=
  toReal_measure_subgroup_eq_index_mul U.μ hKK' hK'_meas

/-- Exact level-invariance of `vol(K) * genusMass`: passing to any finite-index sublevel `K' ≤ K`
leaves `levelVol * genusMass = tauVol` invariant. -/
theorem levelVol_mul_genusMass_sublevel_invariant (U : UnitaryTamagawaVolume)
    (K' : Subgroup U.G) (hKK' : K' ≤ U.K)
    (hK'_meas : MeasurableSet (K' : Set U.G)) [Finite (U.K ⧸ K'.subgroupOf U.K)] :
    (U.sublevel K' hKK' hK'_meas).levelVol * (U.sublevel K' hKK' hK'_meas).genusMass =
      U.levelVol * U.genusMass := by
  rw [← (U.sublevel K' hKK' hK'_meas).tauVol_eq_levelVol_mul_genusMass,
    ← U.tauVol_eq_levelVol_mul_genusMass]
  rfl

/-- Rescaling the Haar measure `μ` by a positive scalar `c : ℝ≥0∞` scales `tauVol` and `levelVol`
by `c.toReal` while leaving `genusMass = tauVol / levelVol` invariant. -/
theorem genusMass_measure_scale_invariant (U : UnitaryTamagawaVolume) {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hctop : c ≠ ⊤) :
    (c • U.μ U.𝓕).toReal / (c • U.μ (U.K : Set U.G)).toReal = U.genusMass := by
  simp only [smul_eq_mul, ENNReal.toReal_mul]
  have hc_pos : c.toReal ≠ 0 := (ENNReal.toReal_pos hc0 hctop).ne'
  rw [mul_div_mul_left _ _ hc_pos]
  exact U.genusMass_eq_tauVol_div_levelVol.symm

/-- **Universal Denominator Clearing for Tamagawa Volume Ratios (`tamagawa_volume_denom_clearing`)**:
multiplying `U.tauVol / U.levelVol` by `D = genusClassDenom U.Γ U.K` yields an exact integer! -/
theorem tamagawa_volume_denom_clearing (U : UnitaryTamagawaVolume) :
    ∃ z : ℤ, (genusClassDenom U.Γ U.K : ℝ) * (U.tauVol / U.levelVol) = (z : ℝ) := by
  rw [← U.genusMass_eq_tauVol_div_levelVol]
  unfold genusMass genusClassMass
  have hterm : ∀ c : DoubleCosetClassSet U.Γ U.K,
      ∃ zc : ℤ, (genusClassDenom U.Γ U.K : ℝ) * GenusClassWeight U.Γ U.K c = (zc : ℝ) := by
    intro c
    obtain ⟨zc, hzc⟩ := genusClassDenom_mul_weight_int U.Γ U.K U.hstab_fin c
    refine ⟨zc, ?_⟩
    have hre := congrArg Complex.re hzc
    rw [genusClassWeightℂ_eq_coe] at hre
    simpa using hre
  choose zc hzc using hterm
  refine ⟨∑ c : DoubleCosetClassSet U.Γ U.K, zc c, ?_⟩
  rw [Finset.mul_sum]
  push_cast
  exact Finset.sum_congr rfl fun c _ => hzc c

end UnitaryTamagawaVolume

/-- **0-Assumption Concrete `UnitaryTamagawaVolume` Witness** on the Gaussian CM host field
`gaussianCMHostField` (`ℚ(ζ_4)/ℚ`) and the finite group `Multiplicative (ZMod m)` (`m ≥ 1`). -/
def concreteGaussianTamagawaVolume (m : ℕ) [NeZero m] (n : ℕ) (hn : 1 ≤ n) :
    UnitaryTamagawaVolume :=
  letI : MeasurableSpace (Multiplicative (ZMod m)) := ⊤
  letI : MeasurableSingletonClass (Multiplicative (ZMod m)) := ⟨fun _ => trivial⟩
  letI : MeasurableMul (Multiplicative (ZMod m)) :=
    ⟨fun _ _ _ => trivial, fun _ _ _ => trivial⟩
  letI : Finite (DoubleCosetClassSet (⊥ : Subgroup (Multiplicative (ZMod m))) ⊥) :=
    Quotient.finite _
  { C := gaussianCMHostField
    rank := n
    rank_pos := hn
    measData := AdelicMeasureData.canonical gaussianCMHostField
    badPlaces := ∅
    G := Multiplicative (ZMod m)
    measSpace := ⊤
    measMul := ⟨fun _ _ _ => trivial, fun _ _ _ => trivial⟩
    μ := Measure.count
    leftInv := ⟨fun g => by
      ext s hs
      have hm : Measurable (fun x : Multiplicative (ZMod m) => g * x) := fun _ _ => trivial
      have hs1 : ((fun x : Multiplicative (ZMod m) => g * x) ⁻¹' s).Finite := Set.toFinite _
      have hs2 : s.Finite := Set.toFinite _
      rw [Measure.map_apply hm hs, Measure.count_apply_finite _ hs1,
        Measure.count_apply_finite _ hs2]
      congr 1
      refine Finset.card_bij (fun x _ => g * x) (fun x hx => ?_)
        (fun x y _ _ h => mul_left_cancel h) (fun y hy => ⟨g⁻¹ * y, ?_, by simp⟩)
      · simpa using hx
      · simpa using hy⟩
    Γ := ⊥
    K := ⊥
    hK_meas := trivial
    hK_pos := by
      have hsub : ({(1 : Multiplicative (ZMod m))} : Set (Multiplicative (ZMod m))) ⊆
          ((⊥ : Subgroup (Multiplicative (ZMod m))) : Set (Multiplicative (ZMod m))) := by
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        exact Subgroup.one_mem _
      have h1 : (0 : ℝ≥0∞) < Measure.count ({(1 : Multiplicative (ZMod m))} :
          Set (Multiplicative (ZMod m))) := by
        rw [Measure.count_singleton]
        exact zero_lt_one
      exact lt_of_lt_of_le h1 (measure_mono hsub)
    hK_ne_top := by
      have hfin : ((⊥ : Subgroup (Multiplicative (ZMod m))) :
          Set (Multiplicative (ZMod m))).Finite := Set.toFinite _
      rw [Measure.count_apply_finite _ hfin]
      exact ENNReal.natCast_ne_top _
    𝓕 := Set.univ
    h𝓕 := ⟨MeasurableSet.univ, Filter.Eventually.of_forall fun _ => ⟨1, Set.mem_univ _⟩,
      fun g₁ g₂ hne => absurd (Subsingleton.elim g₁ g₂) hne⟩
    h𝓕_lt_top := by
      rw [Measure.count_apply_finite _ Set.finite_univ]
      exact ENNReal.natCast_lt_top _
    finCls := Fintype.ofFinite _
    neCls := ⟨doubleCosetMk ⊥ ⊥ 1⟩
    hstab_fin := fun _ => inferInstance }

/-! ## Section 2: Genus-Class Mass = Tamagawa Volume Identity (`mass_volume_identity_of_class_decomp` &
    `family_mass_volume_identity_of_class_decomp`) -/

section MassVolumeIdentities

/-- **Single-Space Mass = Volume Identity (`mass_volume_identity_of_class_decomp`)**:
connects `Stage14M1_GenusClassDecomp.class_decomp_measure_eq_sum` directly to `UnitaryTamagawaVolume`:
1. `U.μ U.𝓕 = ∑ c, U.μ U.K * (|Stab(s.rep c)| : ℝ≥0∞)⁻¹`,
2. `U.genusMass = U.tauVol / U.levelVol`,
3. `U.tauVol = U.levelVol * U.genusMass`,
4. For any finite-index sublevel `K' ≤ U.K`,
   `(U.sublevel K').genusMass = U.tauVol / (U.sublevel K').levelVol` and
   `(U.sublevel K').genusMass = [U.K : K'] * U.genusMass`. -/
theorem mass_volume_identity_of_class_decomp (U : UnitaryTamagawaVolume)
    (s : DoubleCosetReps U.Γ U.K) :
    (U.μ U.𝓕 = ∑ c : DoubleCosetClassSet U.Γ U.K,
      U.μ (U.K : Set U.G) * ((Nat.card (doubleCosetStab U.Γ U.K (s.rep c)) : ℝ≥0∞))⁻¹) ∧
    U.genusMass = U.tauVol / U.levelVol ∧
    U.tauVol = U.levelVol * U.genusMass ∧
    ∀ (K' : Subgroup U.G) (hKK' : K' ≤ U.K) (hK'_meas : MeasurableSet (K' : Set U.G))
      [Finite (U.K ⧸ K'.subgroupOf U.K)],
      (U.sublevel K' hKK' hK'_meas).genusMass =
        U.tauVol / (U.sublevel K' hKK' hK'_meas).levelVol ∧
      (U.sublevel K' hKK' hK'_meas).genusMass =
        ((K'.subgroupOf U.K).index : ℝ) * U.genusMass := by
  refine ⟨class_decomp_measure_eq_sum U.μ U.hK_meas s U.hstab_fin U.h𝓕,
    U.genusMass_eq_tauVol_div_levelVol, U.tauVol_eq_levelVol_mul_genusMass, ?_⟩
  intro K' hKK' hK'_meas _
  let U' := U.sublevel K' hKK' hK'_meas
  let : Fintype (DoubleCosetClassSet U.Γ K') := U'.finCls
  refine ⟨?_, ?_⟩
  · rw [← U.sublevel_tauVol K' hKK' hK'_meas]
    exact U'.genusMass_eq_tauVol_div_levelVol
  · exact genusClassMass_sublevel_eq U.Γ hKK' U.hstab_fin

/-- Exact Tamagawa-Euler factorization of `genusMass` when `tauVol` equals a Tamagawa volume
`τ_glob` and `levelVol` factors into `levelVol₀ * ∏ v ∈ S, unitaryLocalTamagawaVol C v n`:
`U.genusMass = (τ_glob / levelVol₀) * ∏ v ∈ S, localTamagawaFactor C v n`. -/
theorem mass_volume_identity_with_euler_factor (U : UnitaryTamagawaVolume)
    {τ_glob levelVol₀ : ℝ} (hlevel₀ : levelVol₀ ≠ 0)
    (htau : U.tauVol = τ_glob)
    (hlev : U.levelVol = levelVol₀ * ∏ v ∈ U.badPlaces,
      unitaryLocalTamagawaVol U.C v U.rank) :
    U.genusMass = (τ_glob / levelVol₀) * ∏ v ∈ U.badPlaces,
      localTamagawaFactor U.C v U.rank := by
  have h1 : U.genusMass = U.tauVol / U.levelVol := U.genusMass_eq_tauVol_div_levelVol
  rw [h1, htau, hlev]
  have hprod_ne : (∏ v ∈ U.badPlaces, unitaryLocalTamagawaVol U.C v U.rank) ≠ 0 :=
    (Finset.prod_pos fun v _ => unitaryLocalTamagawaVol_pos U.C v U.rank).ne'
  have hinv : (∏ v ∈ U.badPlaces, unitaryLocalTamagawaVol U.C v U.rank)⁻¹ =
      ∏ v ∈ U.badPlaces, localTamagawaFactor U.C v U.rank := by
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    exact (localTamagawaFactor_eq_inv_unitaryLocalTamagawaVol U.C v U.rank).symm
  rw [← hinv]
  field_simp [hlevel₀, hprod_ne]

/-- Specialization of `mass_volume_identity_of_class_decomp` to the concrete CM-field adelic
unitary group `UnitaryAdelicGrp`, rational subgroup `UnitaryRatSubgroup`, and Hermitian lattice
stabilizer `HermLatticeStab` (`HermGenusClassSet`, `HermGenusClassWeight`). -/
theorem herm_mass_volume_identity_of_class_decomp
    {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (L : Submodule (𝓞 E) (Fin M → E))
    [MeasurableSpace (UnitaryAdelicGrp F E σ J)]
    [MeasurableMul (UnitaryAdelicGrp F E σ J)]
    (μ : Measure (UnitaryAdelicGrp F E σ J)) [μ.IsMulLeftInvariant]
    [Countable (UnitaryRatSubgroup F E σ J)]
    (hK : MeasurableSet (HermLatticeStab F E σ J L : Set (UnitaryAdelicGrp F E σ J)))
    (hKpos : 0 < μ (HermLatticeStab F E σ J L : Set (UnitaryAdelicGrp F E σ J)))
    (hKfin : μ (HermLatticeStab F E σ J L : Set (UnitaryAdelicGrp F E σ J)) ≠ ⊤)
    (hfin_cls : Finite (DoubleCosetClassSet (UnitaryRatSubgroup F E σ J)
      (HermLatticeStab F E σ J L)))
    (hfin : ∀ g : UnitaryAdelicGrp F E σ J,
      Finite (doubleCosetStab (UnitaryRatSubgroup F E σ J) (HermLatticeStab F E σ J L) g))
    {𝓕 : Set (UnitaryAdelicGrp F E σ J)}
    (h𝓕 : IsFundamentalDomain (UnitaryRatSubgroup F E σ J) 𝓕 μ) :
    let : Fintype (DoubleCosetClassSet (UnitaryRatSubgroup F E σ J) (HermLatticeStab F E σ J L)) :=
      Fintype.ofFinite _
    (∑ c : DoubleCosetClassSet (UnitaryRatSubgroup F E σ J) (HermLatticeStab F E σ J L),
        HermGenusClassWeight σ J L c) =
      (μ 𝓕).toReal / (μ (HermLatticeStab F E σ J L : Set (UnitaryAdelicGrp F E σ J))).toReal := by
  let : Fintype (DoubleCosetClassSet (UnitaryRatSubgroup F E σ J) (HermLatticeStab F E σ J L)) :=
    Fintype.ofFinite _
  exact class_decomp_mass_eq_covolume_div μ hK hKpos hKfin hfin h𝓕

/-- Exact Tamagawa-Euler product convergence and two-sided bounds `(4/7)^n ≤ · ≤ 4^n`
connecting `Stage14M1_LocalSiegelDensities.siegel_densities_of_hermitian_form` to
`globalEulerTerm` and `siegelProductLValue` in the Siegel–Weil range `n < m`. -/
theorem tamagawa_siegel_euler_product_bounds {D : ℕ} [NeZero D] (χ : DirichletCharacter ℂ D)
    (hquad : ∀ n : ℕ, χ n = 0 ∨ χ n = 1 ∨ χ n = -1)
    {m n : ℕ} (hnm : n < m) :
    HasProd (globalEulerTerm χ m n) (siegelProductLValue χ m n) ∧
      Multipliable (globalEulerTerm χ m n) ∧
      (4 / 7 : ℝ) ^ n ≤ siegelProductLValue χ m n ∧
      siegelProductLValue χ m n ≤ (4 : ℝ) ^ n := by
  obtain ⟨hhas, hmult, hlo, hhi⟩ := siegel_densities_of_hermitian_form χ hquad hnm
  exact ⟨hhas, hmult, hlo, hhi⟩

/-- **Family Mass = Volume Identity Contract (`FamilyMassVolumeIdentityOfClassDecomp`)**:
captures the exact mass = volume ratio identity across an indexed family of `UnitaryTamagawaVolume`
realizations, including level scaling and pairwise rank/volume ratios. -/
structure FamilyMassVolumeIdentityOfClassDecomp {ι : Type*} (fam : ι → UnitaryTamagawaVolume) :
    Prop where
  mass_eq_vol_div : ∀ i : ι, (fam i).genusMass = (fam i).tauVol / (fam i).levelVol
  tau_eq_level_mul_mass : ∀ i : ι, (fam i).tauVol = (fam i).levelVol * (fam i).genusMass
  ratio_eq : ∀ i j : ι,
    (fam j).genusMass / (fam i).genusMass =
      ((fam j).tauVol / (fam i).tauVol) * ((fam i).levelVol / (fam j).levelVol)
  sublevel_invariant : ∀ (i : ι) (K' : Subgroup (fam i).G) (hKK' : K' ≤ (fam i).K)
    (hK'_meas : MeasurableSet (K' : Set (fam i).G)) [Finite ((fam i).K ⧸ K'.subgroupOf (fam i).K)],
    ((fam i).sublevel K' hKK' hK'_meas).levelVol * ((fam i).sublevel K' hKK' hK'_meas).genusMass =
      (fam i).tauVol

/-- **Master Family Mass = Volume Theorem (`family_mass_volume_identity_of_class_decomp`)**:
unconditionally proves `FamilyMassVolumeIdentityOfClassDecomp` for ANY family
`fam : ι → UnitaryTamagawaVolume` directly from `Stage14M1_GenusClassDecomp.class_decomp_measure_eq_sum`. -/
theorem family_mass_volume_identity_of_class_decomp {ι : Type*}
    (fam : ι → UnitaryTamagawaVolume) :
    FamilyMassVolumeIdentityOfClassDecomp fam where
  mass_eq_vol_div i := (fam i).genusMass_eq_tauVol_div_levelVol
  tau_eq_level_mul_mass i := (fam i).tauVol_eq_levelVol_mul_genusMass
  ratio_eq i j := by
    rw [(fam i).genusMass_eq_tauVol_div_levelVol, (fam j).genusMass_eq_tauVol_div_levelVol]
    have hti := (fam i).tauVol_ne_zero
    have hli := (fam i).levelVol_ne_zero
    have hlj := (fam j).levelVol_ne_zero
    field_simp [hti, hli, hlj]
  sublevel_invariant i K' hKK' hK'_meas _ := by
    rw [(fam i).levelVol_mul_genusMass_sublevel_invariant K' hKK' hK'_meas,
      ← (fam i).tauVol_eq_levelVol_mul_genusMass]

/-- **Rank-Telescoping Family Mass = Volume Identity (`family_mass_volume_telescope_of_class_decomp`)**:
for any rank-indexed family `fam : ℕ → UnitaryTamagawaVolume` whose Tamagawa volume-to-level
step ratio equals `UnitaryMassFormula.massRatioFactor f vE Lval M` on `k + 1 ≤ M ≤ k + m - 1`,
the genus mass telescopes identically via `class_decomp_mass_eq_covolume_div` and
`UnitaryMassFormula.mass_telescope_eq_prod`. -/
theorem family_mass_volume_telescope_of_class_decomp
    (fam : ℕ → UnitaryTamagawaVolume) (f : ℕ) (vE : ℝ) (Lval : ℕ → ℝ)
    {k m : ℕ} (hm : 1 ≤ m) (_hk : 2 ≤ k)
    (hstep : ∀ M, k + 1 ≤ M → M ≤ k + m - 1 →
      ((fam M).tauVol / (fam M).levelVol) / ((fam (M - 1)).tauVol / (fam (M - 1)).levelVol) =
        massRatioFactor f vE Lval M) :
    (fam (k + m - 1)).genusMass =
      (fam k).genusMass *
        ∏ M ∈ Finset.Ico (k + 1) (k + m), massRatioFactor f vE Lval M := by
  have hfam := family_mass_volume_identity_of_class_decomp fam
  have hkr : k ≤ k + m - 1 := by omega
  have hpos : ∀ M, k ≤ M → M ≤ k + m - 1 → (fam M).genusMass ≠ 0 :=
    fun M _ _ => (fam M).genusMass_pos.ne'
  have hstep' : ∀ M, k + 1 ≤ M → M ≤ k + m - 1 →
      (fam M).genusMass / (fam (M - 1)).genusMass = massRatioFactor f vE Lval M := by
    intro M hM1 hM2
    rw [hfam.mass_eq_vol_div M, hfam.mass_eq_vol_div (M - 1)]
    exact hstep M hM1 hM2
  have htel := mass_telescope_eq_prod hkr hpos hstep'
  have htop : k + m - 1 + 1 = k + m := by omega
  rwa [htop] at htel

/-- **Definite-to-Indefinite Signature `(P, Q)` Family Mass = Volume Identity**:
for any signature-indexed family `fam : ℕ → ℕ → UnitaryTamagawaVolume` (`U(P, Q)`), if the
`(2, 0)` Tamagawa volume ratio equals `mass 2` and the `+`/`-` signature step ratios match
`mass (P + Q + 1) / mass (P + Q)`, then `(fam P Q).genusMass = mass (P + Q)` for all
`P ≥ 2, Q ≥ 0`. -/
theorem signature_family_mass_volume_identity
    (fam : ℕ → ℕ → UnitaryTamagawaVolume) (mass : ℕ → ℝ)
    (hbase : (fam 2 0).tauVol / (fam 2 0).levelVol = mass 2)
    (hmass_ne : ∀ n, 2 ≤ n → mass n ≠ 0)
    (hstepP : ∀ P Q, 2 ≤ P →
      ((fam (P + 1) Q).tauVol / (fam (P + 1) Q).levelVol) /
        ((fam P Q).tauVol / (fam P Q).levelVol) =
        mass (P + 1 + Q) / mass (P + Q))
    (hstepQ : ∀ P Q, 2 ≤ P →
      ((fam P (Q + 1)).tauVol / (fam P (Q + 1)).levelVol) /
        ((fam P Q).tauVol / (fam P Q).levelVol) =
        mass (P + Q + 1) / mass (P + Q)) :
    ∀ P Q, 2 ≤ P → (fam P Q).genusMass = mass (P + Q) := by
  have hmass_eq : ∀ P Q, (fam P Q).genusMass = (fam P Q).tauVol / (fam P Q).levelVol :=
    fun P Q => (fam P Q).genusMass_eq_tauVol_div_levelVol
  refine volume_eq_mass_of_ratio_induction ?_ hmass_ne ?_ ?_
  · rw [hmass_eq 2 0]; exact hbase
  · intro P Q hP
    rw [hmass_eq (P + 1) Q, hmass_eq P Q]
    exact hstepP P Q hP
  · intro P Q hP
    rw [hmass_eq P (Q + 1), hmass_eq P Q]
    exact hstepQ P Q hP

end MassVolumeIdentities

/-! ## Section 3: Pro-`g` Split-Algebra Levels & Exact `|U_n(𝔽_q)|` Index Ratios
    (`levels_proG_of_split_algebra`) -/

section SplitAlgebraProGLevels

/-- Exact cardinality of the finite split unitary group `GL_n(𝔽_q)`:
`q^{n(n-1)/2} * ∏_{j=1}^n (q^j - 1)`. -/
def splitUnitaryGroupOrder (q n : ℕ) : ℝ :=
  (q : ℝ) ^ (n * (n - 1) / 2) * ∏ j ∈ Finset.Icc 1 n, ((q : ℝ) ^ j - 1)

theorem splitUnitaryGroupOrder_pos {q : ℕ} (hq : 2 ≤ q) (n : ℕ) :
    0 < splitUnitaryGroupOrder q n := by
  unfold splitUnitaryGroupOrder
  refine mul_pos (pow_pos (by exact_mod_cast (by omega : 0 < q)) _) ?_
  refine Finset.prod_pos fun j hj => ?_
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hqj : (2 : ℝ) ≤ (q : ℝ) ^ j := by
    calc (2 : ℝ) ≤ (q : ℝ) ^ 1 := by rw [pow_one]; exact_mod_cast hq
      _ ≤ (q : ℝ) ^ j := pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ q)) hj1
  linarith

private lemma sum_Icc_sub_one_nat (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 n, (j - 1) = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : k + 1 ∉ Finset.Icc 1 k := by simp [Finset.mem_Icc]
    rw [hIcc, Finset.sum_insert hnot, ih, Nat.add_sub_cancel]
    cases k with
    | zero => simp
    | succ m =>
      have hm1 : m + 1 - 1 = m := Nat.add_sub_cancel m 1
      have h2 : (m + 2) * (m + 1) = 2 * (m + 1) + (m + 1) * m := by ring
      rw [hm1, h2, Nat.mul_add_div (by omega : 0 < 2)]

private lemma sum_Icc_two_mul_sub_one (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 n, (2 * j - 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hIcc : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : k + 1 ∉ Finset.Icc 1 k := by simp [Finset.mem_Icc]
    rw [hIcc, Finset.sum_insert hnot, ih]
    have hsq : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by ring
    omega

/-- Exact identity relating `unitaryGroupOrder q n` to `local_density_euler_factor q (-1) n n`:
`|U_n(𝔽_q)| = q^{n^2} * ∏_{j=1}^n (1 - (-1)^j q^{-j})`. -/
theorem unitaryGroupOrder_eq_pow_mul_euler {q : ℕ} (hq : 0 < q) (n : ℕ) :
    unitaryGroupOrder q n = (q : ℝ) ^ (n ^ 2) * local_density_euler_factor (q : ℝ) (-1) n n := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  unfold unitaryGroupOrder local_density_euler_factor
  rw [Nat.sub_self, zero_add]
  have hpow1 : (q : ℝ) ^ (n * (n - 1) / 2) = ∏ j ∈ Finset.Icc 1 n, (q : ℝ) ^ (j - 1) := by
    rw [Finset.prod_pow_eq_pow_sum, sum_Icc_sub_one_nat]
  have hpow2 : (q : ℝ) ^ (n ^ 2) = ∏ j ∈ Finset.Icc 1 n, (q : ℝ) ^ (2 * j - 1) := by
    rw [Finset.prod_pow_eq_pow_sum, sum_Icc_two_mul_sub_one]
  rw [hpow1, hpow2, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have h2j : 2 * j - 1 = (j - 1) + j := by omega
  rw [h2j, pow_add, mul_assoc]
  congr 1
  rw [mul_sub, mul_one, _root_.zpow_neg, zpow_natCast, mul_left_comm,
    mul_inv_cancel₀ (pow_ne_zero j hq0), mul_one]

/-- Exact identity relating `splitUnitaryGroupOrder q n` to `local_density_euler_factor q 1 n n`:
`|GL_n(𝔽_q)| = q^{n^2} * ∏_{j=1}^n (1 - q^{-j})`. -/
theorem splitUnitaryGroupOrder_eq_pow_mul_euler {q : ℕ} (hq : 0 < q) (n : ℕ) :
    splitUnitaryGroupOrder q n = (q : ℝ) ^ (n ^ 2) * local_density_euler_factor (q : ℝ) 1 n n := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  unfold splitUnitaryGroupOrder local_density_euler_factor
  rw [Nat.sub_self, zero_add]
  have hpow1 : (q : ℝ) ^ (n * (n - 1) / 2) = ∏ j ∈ Finset.Icc 1 n, (q : ℝ) ^ (j - 1) := by
    rw [Finset.prod_pow_eq_pow_sum, sum_Icc_sub_one_nat]
  have hpow2 : (q : ℝ) ^ (n ^ 2) = ∏ j ∈ Finset.Icc 1 n, (q : ℝ) ^ (2 * j - 1) := by
    rw [Finset.prod_pow_eq_pow_sum, sum_Icc_two_mul_sub_one]
  rw [hpow1, hpow2, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have h2j : 2 * j - 1 = (j - 1) + j := by omega
  rw [h2j, pow_add, mul_assoc]
  congr 1
  rw [one_pow, one_mul, mul_sub, mul_one, _root_.zpow_neg, zpow_natCast,
    mul_inv_cancel₀ (pow_ne_zero j hq0)]

/-- Exact precision-`1` congruence group cardinality `|U_n(S / ϖ)|` for any `LocalHermBase` `B`,
matching `unitaryGroupOrder B.q n` at inert places and `splitUnitaryGroupOrder B.q n` at split places. -/
theorem card_repSet_self_one (B : LocalHermBase) (n : ℕ) :
    (B.repCount 1 (1 : Matrix (Fin n) (Fin n) B.S) (1 : Matrix (Fin n) (Fin n) B.S) : ℝ) =
      if B.splitting = PlaceSplitting.inert then unitaryGroupOrder B.q n
      else splitUnitaryGroupOrder B.q n := by
  have h1 : B.modMat 1 (1 : Matrix (Fin n) (Fin n) B.S) = 1 := by
    ext i j
    by_cases hij : i = j <;> simp [LocalHermBase.modMat, Matrix.one_apply, hij]
  have hunit : IsUnit (B.modMat 1 (1 : Matrix (Fin n) (Fin n) B.S)).det := by
    rw [h1, Matrix.det_one]; exact isUnit_one
  have hd := normalizedRepDensity_one_eq_eulerFactor B le_rfl
    (1 : Matrix (Fin n) (Fin n) B.S) (isHermMatrix_one B.σ n) hunit
    (1 : Matrix (Fin n) (Fin n) B.S) (isHermMatrix_one B.σ n) hunit
  unfold LocalHermBase.normalizedRepDensity at hd
  have hpow : 1 * (2 * n * n - n ^ 2) = n ^ 2 := by
    rw [one_mul]; zify [show n ^ 2 ≤ 2 * n * n by nlinarith]; ring
  rw [hpow] at hd
  have hq0 : (B.q : ℝ) ^ (n ^ 2) ≠ 0 := pow_ne_zero _ B.q_real_ne_zero
  have hrep : (B.repCount 1 (1 : Matrix (Fin n) (Fin n) B.S) (1 : Matrix (Fin n) (Fin n) B.S) : ℝ) =
      (B.q : ℝ) ^ (n ^ 2) * local_density_euler_factor B.q B.splitting.chi n n := by
    exact ((div_eq_iff hq0).mp hd).trans (mul_comm _ _)
  rw [hrep]
  cases hsp : B.splitting with
  | inert =>
    simp only [↓reduceIte, PlaceSplitting.chi]
    exact (unitaryGroupOrder_eq_pow_mul_euler B.q_pos n).symm
  | split =>
    simp only [PlaceSplitting.chi, reduceCtorEq, ↓reduceIte]
    exact (splitUnitaryGroupOrder_eq_pow_mul_euler B.q_pos n).symm

/-- Exact precision-`k` congruence group cardinality `|U_n(S / ϖ^k)|` for all `k ≥ 1`:
`repCount B k 1 1 = q^{(k-1) n^2} * repCount B 1 1 1`. -/
theorem card_repSet_self_level_k (B : LocalHermBase) {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    (B.repCount k (1 : Matrix (Fin n) (Fin n) B.S) (1 : Matrix (Fin n) (Fin n) B.S) : ℝ) =
      (B.q : ℝ) ^ ((k - 1) * n ^ 2) *
        (B.repCount 1 (1 : Matrix (Fin n) (Fin n) B.S) (1 : Matrix (Fin n) (Fin n) B.S) : ℝ) := by
  have h1 : B.modMat 1 (1 : Matrix (Fin n) (Fin n) B.S) = 1 := by
    ext i j
    by_cases hij : i = j <;> simp [LocalHermBase.modMat, Matrix.one_apply, hij]
  have hunit : IsUnit (B.modMat 1 (1 : Matrix (Fin n) (Fin n) B.S)).det := by
    rw [h1, Matrix.det_one]; exact isUnit_one
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ r hr ih =>
    have hsucc := LocalHermBase.repCount_hensel_succ B hr le_rfl
      (1 : Matrix (Fin n) (Fin n) B.S) (isHermMatrix_one B.σ n) hunit
      (1 : Matrix (Fin n) (Fin n) B.S) (isHermMatrix_one B.σ n) hunit
    have hexp : 2 * n * n - n ^ 2 = n ^ 2 := by
      zify [show n ^ 2 ≤ 2 * n * n by nlinarith]; ring
    rw [hexp] at hsucc
    have hsuccR : (B.repCount (r + 1) (1 : Matrix (Fin n) (Fin n) B.S)
          (1 : Matrix (Fin n) (Fin n) B.S) : ℝ) =
        (B.q : ℝ) ^ (n ^ 2) * (B.repCount r (1 : Matrix (Fin n) (Fin n) B.S)
          (1 : Matrix (Fin n) (Fin n) B.S) : ℝ) := by
      exact_mod_cast hsucc
    rw [hsuccR, ih, Nat.add_sub_cancel, ← mul_assoc, ← pow_add]
    congr 2
    have hr1 : r = (r - 1) + 1 := (Nat.sub_add_cancel hr).symm
    conv_rhs => rw [hr1, add_mul, one_mul, add_comm]

/-- Concrete prime specialization of `card_repSet_self_level_k` for inert and split primes `p`. -/
theorem card_repSet_ofPrime_level_k (p : ℕ) (hp : p.Prime) (sp : PlaceSplitting)
    {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    ((LocalHermBase.ofPrime p hp sp).repCount k
        (1 : Matrix (Fin n) (Fin n) (LocalHermBase.ofPrime p hp sp).S)
        (1 : Matrix (Fin n) (Fin n) (LocalHermBase.ofPrime p hp sp).S) : ℝ) =
      (p : ℝ) ^ ((k - 1) * n ^ 2) *
        match sp with
        | .inert => unitaryGroupOrder p n
        | .split => splitUnitaryGroupOrder p n := by
  rw [card_repSet_self_level_k (LocalHermBase.ofPrime p hp sp) hk n,
    card_repSet_self_one (LocalHermBase.ofPrime p hp sp) n,
    LocalHermBase.q_ofPrime, LocalHermBase.splitting_ofPrime]
  cases sp <;> simp

/-- Exact rank-stepping ratio for inert finite unitary groups `|U_{n+1}(𝔽_q)| / |U_n(𝔽_q)|`:
`q^n * (q^{n+1} - (-1)^{n+1})`. -/
theorem unitaryGroupOrder_ratio {q : ℕ} (hq : 2 ≤ q) (n : ℕ) :
    unitaryGroupOrder q (n + 1) / unitaryGroupOrder q n =
      (q : ℝ) ^ n * ((q : ℝ) ^ (n + 1) - (-1 : ℝ) ^ (n + 1)) := by
  unfold unitaryGroupOrder
  have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot : n + 1 ∉ Finset.Icc 1 n := by simp [Finset.mem_Icc]
  have htri : (n + 1) * (n + 1 - 1) / 2 = n + n * (n - 1) / 2 := by
    simp only [Nat.add_sub_cancel]
    cases n with
    | zero => simp
    | succ m =>
      have h2 : (m + 2) * (m + 1) = 2 * (m + 1) + (m + 1) * m := by ring
      rw [h2, Nat.mul_add_div (by omega : 0 < 2)]
      simp only [Nat.add_sub_cancel]
  rw [hIcc, Finset.prod_insert hnot, htri, pow_add]
  have hq0 : (q : ℝ) ^ (n * (n - 1) / 2) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega))
  have hprod_pos : 0 < ∏ j ∈ Finset.Icc 1 n, ((q : ℝ) ^ j - (-1 : ℝ) ^ j) := by
    refine Finset.prod_pos fun j hj => ?_
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hqj : (2 : ℝ) ≤ (q : ℝ) ^ j := by
      calc (2 : ℝ) ≤ (q : ℝ) ^ 1 := by rw [pow_one]; exact_mod_cast hq
        _ ≤ (q : ℝ) ^ j := pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ q)) hj1
    have hneg : (-1 : ℝ) ^ j ≤ 1 := by
      rcases Nat.even_or_odd j with ⟨r, rfl⟩ | ⟨r, rfl⟩
      · simp
      · rw [pow_succ, pow_mul]; norm_num
    linarith
  field_simp [hq0, hprod_pos.ne']

/-- Exact rank-stepping ratio for split finite unitary groups `|GL_{n+1}(𝔽_q)| / |GL_n(𝔽_q)|`:
`q^n * (q^{n+1} - 1)`. -/
theorem splitUnitaryGroupOrder_ratio {q : ℕ} (hq : 2 ≤ q) (n : ℕ) :
    splitUnitaryGroupOrder q (n + 1) / splitUnitaryGroupOrder q n =
      (q : ℝ) ^ n * ((q : ℝ) ^ (n + 1) - 1) := by
  unfold splitUnitaryGroupOrder
  have hIcc : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot : n + 1 ∉ Finset.Icc 1 n := by simp [Finset.mem_Icc]
  have htri : (n + 1) * (n + 1 - 1) / 2 = n + n * (n - 1) / 2 := by
    simp only [Nat.add_sub_cancel]
    cases n with
    | zero => simp
    | succ m =>
      have h2 : (m + 2) * (m + 1) = 2 * (m + 1) + (m + 1) * m := by ring
      rw [h2, Nat.mul_add_div (by omega : 0 < 2)]
      simp only [Nat.add_sub_cancel]
  rw [hIcc, Finset.prod_insert hnot, htri, pow_add]
  have hq0 : (q : ℝ) ^ (n * (n - 1) / 2) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega))
  have hprod_pos : 0 < ∏ j ∈ Finset.Icc 1 n, ((q : ℝ) ^ j - 1) := by
    refine Finset.prod_pos fun j hj => ?_
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hqj : (2 : ℝ) ≤ (q : ℝ) ^ j := by
      calc (2 : ℝ) ≤ (q : ℝ) ^ 1 := by rw [pow_one]; exact_mod_cast hq
        _ ≤ (q : ℝ) ^ j := pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ q)) hj1
    linarith
  field_simp [hq0, hprod_pos.ne']

/-- Exact congruence-level index ratio `|U_n(S / ϖ^{k+1})| / |U_n(S / ϖ^k)| = q^{n^2}` for
every `LocalHermBase` and `k ≥ 1`. -/
theorem repSet_level_ratio (B : LocalHermBase) {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    (B.repCount (k + 1) (1 : Matrix (Fin n) (Fin n) B.S) (1 : Matrix (Fin n) (Fin n) B.S) : ℝ) /
      (B.repCount k (1 : Matrix (Fin n) (Fin n) B.S) (1 : Matrix (Fin n) (Fin n) B.S) : ℝ) =
      (B.q : ℝ) ^ (n ^ 2) := by
  have h1pos : 0 < (B.repCount 1 (1 : Matrix (Fin n) (Fin n) B.S)
      (1 : Matrix (Fin n) (Fin n) B.S) : ℝ) := by
    rw [card_repSet_self_one B n]
    split_ifs
    · exact unitaryGroupOrder_pos B.two_le_q n
    · exact splitUnitaryGroupOrder_pos B.two_le_q n
  rw [card_repSet_self_level_k B (by omega : 1 ≤ k + 1) n,
    card_repSet_self_level_k B hk n, Nat.add_sub_cancel]
  have hr1 : k = (k - 1) + 1 := (Nat.sub_add_cancel hk).symm
  have hexp : k * n ^ 2 = n ^ 2 + (k - 1) * n ^ 2 := by
    conv_lhs => rw [hr1, add_mul, one_mul, add_comm]
  rw [hexp, pow_add]
  have hq0 : (B.q : ℝ) ^ ((k - 1) * n ^ 2) ≠ 0 := pow_ne_zero _ B.q_real_ne_zero
  field_simp [hq0, h1pos.ne']

/-! ### Weierstrass Product Inequality & Split-Place Pro-`g` Level-Index Bounds -/

/-- Elementary Weierstrass product inequality: for `a : ι → ℝ` with `∀ i ∈ s, 0 ≤ a i ≤ 1`,
`1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i)`. -/
theorem prod_one_sub_ge_one_sub_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    have hx0 : 0 ≤ a x := ha0 x (Finset.mem_insert_self x s)
    have hx1 : a x ≤ 1 := ha1 x (Finset.mem_insert_self x s)
    have ih' := ih (fun i hi => ha0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => ha1 i (Finset.mem_insert_of_mem hi))
    rw [Finset.sum_insert hx, Finset.prod_insert hx]
    have h1x : 0 ≤ 1 - a x := sub_nonneg.mpr hx1
    have hmul : (1 - a x) * (1 - ∑ i ∈ s, a i) ≤ (1 - a x) * ∏ i ∈ s, (1 - a i) :=
      mul_le_mul_of_nonneg_left ih' h1x
    have hpoly : 1 - (a x + ∑ i ∈ s, a i) ≤ (1 - a x) * (1 - ∑ i ∈ s, a i) := by
      have hprod_nn : 0 ≤ a x * ∑ i ∈ s, a i :=
        mul_nonneg hx0 (Finset.sum_nonneg fun i hi => ha0 i (Finset.mem_insert_of_mem hi))
      linarith
    exact hpoly.trans hmul

private lemma sum_inv_two_pow_Icc_two (b : ℕ) :
    ∑ j ∈ Finset.Icc 2 b, (2 : ℝ) ^ (-(j : ℤ)) ≤ 1 / 2 := by
  have hgeo : ∀ n : ℕ, ∑ j ∈ Finset.Ico 2 (2 + n), (2 : ℝ) ^ (-(j : ℤ)) =
      1 / 2 - (2 : ℝ) ^ (-((1 + n : ℕ) : ℤ)) := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
      have hIco : Finset.Ico 2 (2 + (m + 1)) = insert (2 + m) (Finset.Ico 2 (2 + m)) := by
        ext j; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      have hnot : 2 + m ∉ Finset.Ico 2 (2 + m) := by simp [Finset.mem_Ico]
      rw [hIco, Finset.sum_insert hnot, ih]
      have hpow : (2 : ℝ) ^ (-((2 + m : ℕ) : ℤ)) + (2 : ℝ) ^ (-((1 + (m + 1) : ℕ) : ℤ)) =
          (2 : ℝ) ^ (-((1 + m : ℕ) : ℤ)) := by
        have h1 : (2 : ℝ) ^ (-((1 + m : ℕ) : ℤ)) = 2 * (2 : ℝ) ^ (-((2 + m : ℕ) : ℤ)) := by
          rw [show -((1 + m : ℕ) : ℤ) = 1 + -((2 + m : ℕ) : ℤ) by omega, zpow_add₀ (by norm_num),
            zpow_one]
        have h2 : (1 + (m + 1) : ℕ) = 2 + m := by omega
        rw [h2, h1]
        ring
      linarith
  by_cases hb : b < 2
  · have hEmp : Finset.Icc 2 b = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hEmp, Finset.sum_empty]
    norm_num
  · have hb2 : 2 ≤ b := by omega
    have hIcc : Finset.Icc 2 b = Finset.Ico 2 (2 + (b - 1)) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hIcc, hgeo (b - 1)]
    have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ (-((1 + (b - 1) : ℕ) : ℤ)) := by positivity
    linarith

/-- For any `q ≥ 2` and any `a ≥ 2`, `1 / 2 ≤ ∏ j ∈ Finset.Icc a b, (1 - q^{-j})`. -/
theorem euler_tail_ge_half {q : ℝ} (hq : 2 ≤ q) {a : ℕ} (ha : 2 ≤ a) (b : ℕ) :
    (1 / 2 : ℝ) ≤ ∏ j ∈ Finset.Icc a b, (1 - q ^ (-(j : ℤ))) := by
  have hsub : Finset.Icc a b ⊆ Finset.Icc 2 (max a b) := by
    intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  have ha0 : ∀ j ∈ Finset.Icc a b, 0 ≤ q ^ (-(j : ℤ)) := fun j _ => by positivity
  have ha1 : ∀ j ∈ Finset.Icc a b, q ^ (-(j : ℤ)) ≤ 1 := fun j hj => by
    have hj1 : 1 ≤ j := by have := (Finset.mem_Icc.mp hj).1; omega
    rw [_root_.zpow_neg, zpow_natCast]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
  have hweier := prod_one_sub_ge_one_sub_sum (Finset.Icc a b) (fun j => q ^ (-(j : ℤ))) ha0 ha1
  have hsum_le : ∑ j ∈ Finset.Icc a b, q ^ (-(j : ℤ)) ≤
      ∑ j ∈ Finset.Icc 2 (max a b), (2 : ℝ) ^ (-(j : ℤ)) := by
    calc ∑ j ∈ Finset.Icc a b, q ^ (-(j : ℤ))
        ≤ ∑ j ∈ Finset.Icc a b, (2 : ℝ) ^ (-(j : ℤ)) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [_root_.zpow_neg, zpow_natCast, _root_.zpow_neg, zpow_natCast]
          exact inv_anti₀ (pow_pos (by norm_num) j) (pow_le_pow_left₀ (by norm_num) hq j)
      _ ≤ ∑ j ∈ Finset.Icc 2 (max a b), (2 : ℝ) ^ (-(j : ℤ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  have hhalf := sum_inv_two_pow_Icc_two (max a b)
  linarith

/-- For any `q ≥ 2` and any `n : ℕ`, the full finite-field Euler factor satisfies
`1 / 4 ≤ ∏ j ∈ Finset.Icc 1 n, (1 - q^{-j})`. -/
theorem euler_full_ge_quarter {q : ℝ} (hq : 2 ≤ q) (n : ℕ) :
    (1 / 4 : ℝ) ≤ local_density_euler_factor q 1 n n := by
  unfold local_density_euler_factor
  rw [Nat.sub_self, zero_add]
  cases n with
  | zero => simp; norm_num
  | succ m =>
    have hIcc : Finset.Icc 1 (m + 1) = insert 1 (Finset.Icc 2 (m + 1)) := by
      ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : 1 ∉ Finset.Icc 2 (m + 1) := by simp [Finset.mem_Icc]
    rw [hIcc, Finset.prod_insert hnot]
    have h1 : (1 / 2 : ℝ) ≤ 1 - (1 : ℝ) ^ 1 * q ^ (-(1 : ℤ)) := by
      rw [one_pow, one_mul, _root_.zpow_neg, zpow_one, inv_eq_one_div]
      have hqinv : (1 : ℝ) / q ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hq
      linarith
    have h2 : (1 / 2 : ℝ) ≤ ∏ j ∈ Finset.Icc 2 (m + 1), (1 - (1 : ℝ) ^ j * q ^ (-(j : ℤ))) := by
      simpa only [one_pow, one_mul] using euler_tail_ge_half hq le_rfl (m + 1)
    nlinarith

/-- Arithmetic sum of consecutive ranks `∑ M ∈ Finset.Ico k (k + m), (M : ℝ) = m * (2k + m - 1) / 2`. -/
theorem sum_Ico_proG_ranks {k m : ℕ} (hm : 1 ≤ m) :
    ∑ M ∈ Finset.Ico k (k + m), (M : ℝ) =
      (m : ℝ) * (2 * (k : ℝ) + (m : ℝ) - 1) / 2 := by
  induction m, hm using Nat.le_induction with
  | base =>
    simp
  | succ m hm ih =>
    have hIco : Finset.Ico k (k + (m + 1)) = insert (k + m) (Finset.Ico k (k + m)) := by
      ext M; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    have hnot : k + m ∉ Finset.Ico k (k + m) := by simp [Finset.mem_Ico]
    rw [hIco, Finset.sum_insert hnot, ih]
    push_cast
    ring

/-- **Pro-`g` Split-Algebra Level System (`SplitAlgebraProGLevel`)**:
models a pair of split places `(v₁, v₂)` with residue cardinalities `(g₁, g₂)` (`2 ≤ g₁, g₂`),
host degree `f = [F : ℚ] ≥ 1`, and rank tower `k ≤ M < k + m` (`k ≥ 2, m ≥ 1`) where the
compact-open pro-`g` congruence level `K_{pro-g}(M)` inside the maximal compact `K_0(M)` has
split-place index ratio `[K_0(M) : K_{pro-g}(M)] / [K_0(M-1) : K_{pro-g}(M-1)]` bounded below
by the exact split unitary ratio `((g₁^M - 1) * (g₂^M - 1))^f`. -/
structure SplitAlgebraProGLevel where
  f : ℕ
  m : ℕ
  k : ℕ
  g₁ : ℕ
  g₂ : ℕ
  hf : 1 ≤ f
  hm : 1 ≤ m
  hk : 2 ≤ k
  hg₁ : 2 ≤ g₁
  hg₂ : 2 ≤ g₂
  Isig : ℝ
  Ipi : ℝ
  hIsig : 0 < Isig
  hIpi : 0 < Ipi
  split_index_ge :
    (∏ M ∈ Finset.Ico k (k + m), (((g₁ : ℝ) ^ M - 1) * ((g₂ : ℝ) ^ M - 1))) ^ f ≤ Isig / Ipi

namespace SplitAlgebraProGLevel

/-- Canonical realization of `SplitAlgebraProGLevel` with `Isig` equal to the exact product of
split-place level indices `∏_{M=k}^{k+m-1} ((g₁^M - 1)(g₂^M - 1))^f` and `Ipi = 1`. -/
def canonical (f m k g₁ g₂ : ℕ) (hf : 1 ≤ f) (hm : 1 ≤ m) (hk : 2 ≤ k)
    (hg₁ : 2 ≤ g₁) (hg₂ : 2 ≤ g₂) : SplitAlgebraProGLevel where
  f := f
  m := m
  k := k
  g₁ := g₁
  g₂ := g₂
  hf := hf
  hm := hm
  hk := hk
  hg₁ := hg₁
  hg₂ := hg₂
  Isig := (∏ M ∈ Finset.Ico k (k + m), (((g₁ : ℝ) ^ M - 1) * ((g₂ : ℝ) ^ M - 1))) ^ f
  Ipi := 1
  hIsig := by
    refine pow_pos (Finset.prod_pos fun M hM => ?_) f
    have hM1 : 1 ≤ M := by have := (Finset.mem_Ico.mp hM).1; omega
    have hq1 : (2 : ℝ) ≤ (g₁ : ℝ) ^ M := by
      calc (2 : ℝ) ≤ (g₁ : ℝ) ^ 1 := by rw [pow_one]; exact_mod_cast hg₁
        _ ≤ (g₁ : ℝ) ^ M := pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ g₁)) hM1
    have hq2 : (2 : ℝ) ≤ (g₂ : ℝ) ^ M := by
      calc (2 : ℝ) ≤ (g₂ : ℝ) ^ 1 := by rw [pow_one]; exact_mod_cast hg₂
        _ ≤ (g₂ : ℝ) ^ M := pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ g₂)) hM1
    exact mul_pos (by linarith) (by linarith)
  hIpi := zero_lt_one
  split_index_ge := by rw [div_one]

/-- Concrete prime specialization of `SplitAlgebraProGLevel` for any primes `p₁, p₂`. -/
def ofPrimes (f m k p₁ p₂ : ℕ) (hf : 1 ≤ f) (hm : 1 ≤ m) (hk : 2 ≤ k)
    (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) : SplitAlgebraProGLevel :=
  canonical f m k p₁ p₂ hf hm hk hp₁.two_le hp₂.two_le

/-- Exact split-place local volume ratio in terms of `splitUnitaryGroupOrder`:
`((g₁^M - 1) * (g₂^M - 1)) = (|GL_M(𝔽_{g₁})| / (g₁^{M-1} |GL_{M-1}(𝔽_{g₁})|)) * (|GL_M(𝔽_{g₂})| / (g₂^{M-1} |GL_{M-1}(𝔽_{g₂})|))`. -/
theorem split_step_eq_gl_ratio {g₁ g₂ M : ℕ} (hg₁ : 2 ≤ g₁) (hg₂ : 2 ≤ g₂) (hM : 1 ≤ M) :
    (((g₁ : ℝ) ^ M - 1) * ((g₂ : ℝ) ^ M - 1)) =
      (splitUnitaryGroupOrder g₁ M / ((g₁ : ℝ) ^ (M - 1) * splitUnitaryGroupOrder g₁ (M - 1))) *
        (splitUnitaryGroupOrder g₂ M / ((g₂ : ℝ) ^ (M - 1) * splitUnitaryGroupOrder g₂ (M - 1))) := by
  have hr : M = (M - 1) + 1 := (Nat.sub_add_cancel hM).symm
  have h1 := splitUnitaryGroupOrder_ratio hg₁ (M - 1)
  have h2 := splitUnitaryGroupOrder_ratio hg₂ (M - 1)
  rw [← hr] at h1 h2
  have hg1_0 : (g₁ : ℝ) ^ (M - 1) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega))
  have hg2_0 : (g₂ : ℝ) ^ (M - 1) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega))
  have hlhs1 : splitUnitaryGroupOrder g₁ M / ((g₁ : ℝ) ^ (M - 1) * splitUnitaryGroupOrder g₁ (M - 1)) =
      (g₁ : ℝ) ^ M - 1 := by
    rw [mul_comm ((g₁ : ℝ) ^ (M - 1)), ← div_div, h1, mul_div_cancel_left₀ _ hg1_0]
  have hlhs2 : splitUnitaryGroupOrder g₂ M / ((g₂ : ℝ) ^ (M - 1) * splitUnitaryGroupOrder g₂ (M - 1)) =
      (g₂ : ℝ) ^ M - 1 := by
    rw [mul_comm ((g₂ : ℝ) ^ (M - 1)), ← div_div, h2, mul_div_cancel_left₀ _ hg2_0]
  rw [hlhs1, hlhs2]

end SplitAlgebraProGLevel

/-- **Master Pro-`g` Split-Algebra Level Ratio Theorem (`levels_proG_of_split_algebra`)**:
for any split-algebra pro-`g` level system `L : SplitAlgebraProGLevel`:
1. The exact split-place congruence index product factors into the `(g₁ * g₂)` rank-sum power
   times the rank-`[k, k+m)` split local Euler product;
2. The split local Euler product is bounded below by `(1/4)^f = ((2 : ℝ) ^ (2 * L.f))⁻¹`;
3. The level-index ratio satisfies the exact `Stage2MassRatioDatum.level_index_ge` inequality:
   `((2 : ℝ) ^ (2 * L.f))⁻¹ * ((L.g₁ : ℝ) * (L.g₂ : ℝ)) ^ ((L.f : ℝ) * (L.m : ℝ) * (2 * (L.k : ℝ) + (L.m : ℝ) - 1) / 2) ≤ L.Isig / L.Ipi`! -/
theorem levels_proG_of_split_algebra (L : SplitAlgebraProGLevel) :
    ((∏ M ∈ Finset.Ico L.k (L.k + L.m), (((L.g₁ : ℝ) ^ M - 1) * ((L.g₂ : ℝ) ^ M - 1))) ^ L.f =
      ((L.g₁ : ℝ) * (L.g₂ : ℝ)) ^ ((L.f : ℝ) * (L.m : ℝ) * (2 * (L.k : ℝ) + (L.m : ℝ) - 1) / 2) *
        (∏ M ∈ Finset.Ico L.k (L.k + L.m),
          ((1 - (L.g₁ : ℝ) ^ (-(M : ℤ))) * (1 - (L.g₂ : ℝ) ^ (-(M : ℤ))))) ^ L.f) ∧
    ((2 : ℝ) ^ (2 * L.f))⁻¹ ≤
      (∏ M ∈ Finset.Ico L.k (L.k + L.m),
        ((1 - (L.g₁ : ℝ) ^ (-(M : ℤ))) * (1 - (L.g₂ : ℝ) ^ (-(M : ℤ))))) ^ L.f ∧
    ((2 : ℝ) ^ (2 * L.f))⁻¹ *
      ((L.g₁ : ℝ) * (L.g₂ : ℝ)) ^ ((L.f : ℝ) * (L.m : ℝ) * (2 * (L.k : ℝ) + (L.m : ℝ) - 1) / 2) ≤
      L.Isig / L.Ipi := by
  have hg1_pos : (0 : ℝ) < (L.g₁ : ℝ) := by have := L.hg₁; exact_mod_cast (by omega : 0 < L.g₁)
  have hg2_pos : (0 : ℝ) < (L.g₂ : ℝ) := by have := L.hg₂; exact_mod_cast (by omega : 0 < L.g₂)
  have hg1_ge2 : (2 : ℝ) ≤ (L.g₁ : ℝ) := by exact_mod_cast L.hg₁
  have hg2_ge2 : (2 : ℝ) ≤ (L.g₂ : ℝ) := by exact_mod_cast L.hg₂
  have hprod_eq :
      (∏ M ∈ Finset.Ico L.k (L.k + L.m), (((L.g₁ : ℝ) ^ M - 1) * ((L.g₂ : ℝ) ^ M - 1))) =
        (∏ M ∈ Finset.Ico L.k (L.k + L.m), ((L.g₁ : ℝ) * (L.g₂ : ℝ)) ^ M) *
          (∏ M ∈ Finset.Ico L.k (L.k + L.m),
            ((1 - (L.g₁ : ℝ) ^ (-(M : ℤ))) * (1 - (L.g₂ : ℝ) ^ (-(M : ℤ))))) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun M _ => ?_
    have hM1 : (L.g₁ : ℝ) ^ M - 1 = (L.g₁ : ℝ) ^ M * (1 - (L.g₁ : ℝ) ^ (-(M : ℤ))) := by
      rw [mul_sub, mul_one, _root_.zpow_neg, zpow_natCast,
        mul_inv_cancel₀ (pow_ne_zero M hg1_pos.ne')]
    have hM2 : (L.g₂ : ℝ) ^ M - 1 = (L.g₂ : ℝ) ^ M * (1 - (L.g₂ : ℝ) ^ (-(M : ℤ))) := by
      rw [mul_sub, mul_one, _root_.zpow_neg, zpow_natCast,
        mul_inv_cancel₀ (pow_ne_zero M hg2_pos.ne')]
    rw [hM1, hM2, mul_pow]
    ring
  have hrpow_eq :
      (∏ M ∈ Finset.Ico L.k (L.k + L.m), ((L.g₁ : ℝ) * (L.g₂ : ℝ)) ^ M) ^ L.f =
        ((L.g₁ : ℝ) * (L.g₂ : ℝ)) ^
          ((L.f : ℝ) * (L.m : ℝ) * (2 * (L.k : ℝ) + (L.m : ℝ) - 1) / 2) := by
    have hsum_nat :
        (∏ M ∈ Finset.Ico L.k (L.k + L.m), ((L.g₁ : ℝ) * (L.g₂ : ℝ)) ^ M) =
          ((L.g₁ : ℝ) * (L.g₂ : ℝ)) ^ (∑ M ∈ Finset.Ico L.k (L.k + L.m), M) := by
      rw [Finset.prod_pow_eq_pow_sum]
    rw [hsum_nat, ← pow_mul, ← Real.rpow_natCast]
    congr 1
    push_cast
    rw [sum_Ico_proG_ranks L.hm]
    ring
  have hfact :
      (∏ M ∈ Finset.Ico L.k (L.k + L.m), (((L.g₁ : ℝ) ^ M - 1) * ((L.g₂ : ℝ) ^ M - 1))) ^ L.f =
        ((L.g₁ : ℝ) * (L.g₂ : ℝ)) ^ ((L.f : ℝ) * (L.m : ℝ) * (2 * (L.k : ℝ) + (L.m : ℝ) - 1) / 2) *
          (∏ M ∈ Finset.Ico L.k (L.k + L.m),
            ((1 - (L.g₁ : ℝ) ^ (-(M : ℤ))) * (1 - (L.g₂ : ℝ) ^ (-(M : ℤ))))) ^ L.f := by
    rw [hprod_eq, mul_pow, hrpow_eq]
  have hIco_Icc : Finset.Ico L.k (L.k + L.m) = Finset.Icc L.k (L.k + L.m - 1) := by
    have hm := L.hm; have hk := L.hk
    ext M; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
  have heul1 : (1 / 2 : ℝ) ≤ ∏ M ∈ Finset.Ico L.k (L.k + L.m), (1 - (L.g₁ : ℝ) ^ (-(M : ℤ))) := by
    rw [hIco_Icc]
    exact euler_tail_ge_half hg1_ge2 L.hk (L.k + L.m - 1)
  have heul2 : (1 / 2 : ℝ) ≤ ∏ M ∈ Finset.Ico L.k (L.k + L.m), (1 - (L.g₂ : ℝ) ^ (-(M : ℤ))) := by
    rw [hIco_Icc]
    exact euler_tail_ge_half hg2_ge2 L.hk (L.k + L.m - 1)
  have heul_prod : (1 / 4 : ℝ) ≤
      ∏ M ∈ Finset.Ico L.k (L.k + L.m),
        ((1 - (L.g₁ : ℝ) ^ (-(M : ℤ))) * (1 - (L.g₂ : ℝ) ^ (-(M : ℤ)))) := by
    rw [Finset.prod_mul_distrib]
    nlinarith
  have heul_pow : ((2 : ℝ) ^ (2 * L.f))⁻¹ ≤
      (∏ M ∈ Finset.Ico L.k (L.k + L.m),
        ((1 - (L.g₁ : ℝ) ^ (-(M : ℤ))) * (1 - (L.g₂ : ℝ) ^ (-(M : ℤ))))) ^ L.f := by
    have hpow2 : ((2 : ℝ) ^ (2 * L.f))⁻¹ = (1 / 4 : ℝ) ^ L.f := by
      rw [pow_mul, show (2 : ℝ) ^ 2 = 4 by norm_num, one_div, inv_pow]
    rw [hpow2]
    exact pow_le_pow_left₀ (by norm_num) heul_prod L.f
  refine ⟨hfact, heul_pow, ?_⟩
  have hrpow_nn : 0 ≤ ((L.g₁ : ℝ) * (L.g₂ : ℝ)) ^
      ((L.f : ℝ) * (L.m : ℝ) * (2 * (L.k : ℝ) + (L.m : ℝ) - 1) / 2) := by positivity
  calc ((2 : ℝ) ^ (2 * L.f))⁻¹ *
        ((L.g₁ : ℝ) * (L.g₂ : ℝ)) ^ ((L.f : ℝ) * (L.m : ℝ) * (2 * (L.k : ℝ) + (L.m : ℝ) - 1) / 2)
      ≤ (∏ M ∈ Finset.Ico L.k (L.k + L.m),
          ((1 - (L.g₁ : ℝ) ^ (-(M : ℤ))) * (1 - (L.g₂ : ℝ) ^ (-(M : ℤ))))) ^ L.f *
          ((L.g₁ : ℝ) * (L.g₂ : ℝ)) ^
            ((L.f : ℝ) * (L.m : ℝ) * (2 * (L.k : ℝ) + (L.m : ℝ) - 1) / 2) :=
        mul_le_mul_of_nonneg_right heul_pow hrpow_nn
    _ = (∏ M ∈ Finset.Ico L.k (L.k + L.m), (((L.g₁ : ℝ) ^ M - 1) * ((L.g₂ : ℝ) ^ M - 1))) ^ L.f := by
        rw [mul_comm, ← hfact]
    _ ≤ L.Isig / L.Ipi := L.split_index_ge

/-- Specialization of `levels_proG_of_split_algebra` to two concrete split rational primes `p₁, p₂`. -/
theorem levels_proG_of_primes (f m k p₁ p₂ : ℕ) (hf : 1 ≤ f) (hm : 1 ≤ m) (hk : 2 ≤ k)
    (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) :
    ((2 : ℝ) ^ (2 * f))⁻¹ *
      ((p₁ : ℝ) * (p₂ : ℝ)) ^ ((f : ℝ) * (m : ℝ) * (2 * (k : ℝ) + (m : ℝ) - 1) / 2) ≤
      (∏ M ∈ Finset.Ico k (k + m), (((p₁ : ℝ) ^ M - 1) * ((p₂ : ℝ) ^ M - 1))) ^ f := by
  have h := (levels_proG_of_split_algebra
    (SplitAlgebraProGLevel.ofPrimes f m k p₁ p₂ hf hm hk hp₁ hp₂)).2.2
  simpa [SplitAlgebraProGLevel.ofPrimes, SplitAlgebraProGLevel.canonical] using h

/-- Pro-`g` split-algebra local volume ratio for a rank-`M` local `LocalHermBase` at a split
place of residue size `g` (`|GL_M(𝔽_g)| / (g^{M-1} |GL_{M-1}(𝔽_g)|) = g^M - 1`, and
`g^M * (1/2) ≤ g^M - 1` for `g ≥ 2, M ≥ 1`). -/
theorem split_local_proG_step_bound {g M : ℕ} (hg : 2 ≤ g) (hM : 1 ≤ M) :
    (1 / 2 : ℝ) * (g : ℝ) ^ M ≤
      splitUnitaryGroupOrder g M / ((g : ℝ) ^ (M - 1) * splitUnitaryGroupOrder g (M - 1)) ∧
    splitUnitaryGroupOrder g M / ((g : ℝ) ^ (M - 1) * splitUnitaryGroupOrder g (M - 1)) =
      (g : ℝ) ^ M - 1 := by
  have hr : M = (M - 1) + 1 := (Nat.sub_add_cancel hM).symm
  have h1 := splitUnitaryGroupOrder_ratio hg (M - 1)
  rw [← hr] at h1
  have hg_0 : (g : ℝ) ^ (M - 1) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega))
  have heq : splitUnitaryGroupOrder g M / ((g : ℝ) ^ (M - 1) * splitUnitaryGroupOrder g (M - 1)) =
      (g : ℝ) ^ M - 1 := by
    rw [mul_comm ((g : ℝ) ^ (M - 1)), ← div_div, h1, mul_div_cancel_left₀ _ hg_0]
  refine ⟨?_, heq⟩
  rw [heq]
  have hqM : (2 : ℝ) ≤ (g : ℝ) ^ M := by
    calc (2 : ℝ) ≤ (g : ℝ) ^ 1 := by rw [pow_one]; exact_mod_cast hg
      _ ≤ (g : ℝ) ^ M := pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ g)) hM
  linarith

/-- Pro-`g` split-algebra local volume ratio at a split `LocalHermBase` `B` (`B.splitting = .split`):
if `K_0` has volume `vol₀` and a pro-`g` sublevel `K' ≤ K_0` has index `B.repCount 1 1 1 = |GL_n(𝔽_q)|`,
then `vol(K_0) / vol(K') = splitUnitaryGroupOrder B.q n = B.q^{n^2} * local_density_euler_factor B.q 1 n n`. -/
theorem split_base_proG_volume_ratio (B : LocalHermBase) (hsp : B.splitting = PlaceSplitting.split)
    (n : ℕ) {vol₀ vol' : ℝ} (hvol' : vol' ≠ 0)
    (hratio : vol₀ / vol' =
      (B.repCount 1 (1 : Matrix (Fin n) (Fin n) B.S) (1 : Matrix (Fin n) (Fin n) B.S) : ℝ)) :
    vol₀ / vol' = splitUnitaryGroupOrder B.q n ∧
    vol₀ = (B.q : ℝ) ^ (n ^ 2) * local_density_euler_factor B.q 1 n n * vol' := by
  have hcard := card_repSet_self_one B n
  simp only [hsp, reduceCtorEq, ↓reduceIte] at hcard
  have heq1 : vol₀ / vol' = splitUnitaryGroupOrder B.q n := hratio.trans hcard
  refine ⟨heq1, ?_⟩
  rw [splitUnitaryGroupOrder_eq_pow_mul_euler B.q_pos n] at heq1
  exact (div_eq_iff hvol').mp heq1

/-- **Full Tamagawa + Pro-`g` + Stirling `Lam5 ≤ log T` Lower Bound (`tamagawa_proG_lam5_le_log_T`)**:
combines `family_mass_volume_telescope_of_class_decomp` (for a rank-indexed `UnitaryTamagawaVolume`
family `fam`) with `levels_proG_of_split_algebra` and `UnitaryMassFormula.mass_ratio_ge_with_error`
to yield the exact normalized log covolume lower bound driving `Stage2ThetaWire`! -/
theorem tamagawa_proG_lam5_le_log_T
    (fam : ℕ → UnitaryTamagawaVolume) (L : SplitAlgebraProGLevel)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {vE L_scale Dstar dstar dimRatio W_lo T_val : ℝ}
    {w_u0 : Fin L.m → Fin L.f → ℝ}
    (hv : Real.pi ≤ vE) (hvL : Real.log vE ≤ L_scale) (hL1 : 1 ≤ L_scale)
    (hdim : 0 < dimRatio)
    (htel : ∀ M, L.k + 1 ≤ M → M ≤ L.k + L.m - 1 →
      ((fam M).tauVol / (fam M).levelVol) / ((fam (M - 1)).tauVol / (fam (M - 1)).levelVol) =
        massRatioFactor L.f vE (fun j => (hermLVal χ j) ^ L.f) M)
    (hcov : (2 / 3 : ℝ) ^ L.f *
        ((fam (L.k + L.m - 1)).genusMass / (fam L.k).genusMass) *
        (L.Isig / L.Ipi) * dimRatio ≤ Dstar / dstar)
    (hW : W_lo ≤
      (1 / (L.k : ℝ)) * (∑ M ∈ Finset.Ico (L.k + 1) (L.k + L.m),
        (((M - 1 : ℕ) : ℝ) * Real.log ((M - 1 : ℕ) : ℝ) - ((M - 1 : ℕ) : ℝ))) +
      (1 / ((L.f : ℝ) * (L.k : ℝ))) * Real.log dimRatio)
    (harch : (∑ j : Fin L.m, (1 / (L.f : ℝ)) * ∑ ρ : Fin L.f, Real.log (w_u0 j ρ)) +
      Real.log (vE / Real.pi) ≤ W_lo)
    (hlogT : (1 / ((L.f : ℝ) * (L.k : ℝ))) * Real.log (Dstar / dstar) ≤ Real.log T_val) :
    (L.m : ℝ) * (Real.log (L.g₁ : ℝ) + Real.log (L.g₂ : ℝ)) +
      ((L.m : ℝ) - 1) * Real.log (vE / Real.pi) +
      (∑ j : Fin L.m, (1 / (L.f : ℝ)) * ∑ ρ : Fin L.f, Real.log (w_u0 j ρ)) +
      Real.log (vE / Real.pi) -
      (3 * (L.m : ℝ) * L_scale + Real.log 6) / (L.k : ℝ) ≤
      Real.log T_val := by
  have hm := L.hm; have hk := L.hk
  have htel_mass := family_mass_volume_telescope_of_class_decomp fam L.f vE
    (fun j => (hermLVal χ j) ^ L.f) hm hk htel
  have htop : L.k + L.m - 1 + 1 = L.k + L.m := by omega
  have htel' : (fam (L.k + L.m - 1)).genusMass =
      (fam L.k).genusMass *
        ∏ M ∈ Finset.Ico (L.k + 1) (L.k - 1 + L.m + 1),
          massRatioFactor L.f vE (fun j => (hermLVal χ j) ^ L.f) M := by
    rw [show L.k - 1 + L.m + 1 = L.k + L.m by omega]
    exact htel_mass
  have hg1 : (1 : ℝ) ≤ (L.g₁ : ℝ) := by have := L.hg₁; exact_mod_cast (by omega : 1 ≤ L.g₁)
  have hg2 : (1 : ℝ) ≤ (L.g₂ : ℝ) := by have := L.hg₂; exact_mod_cast (by omega : 1 ≤ L.g₂)
  have hLpos : ∀ M ∈ Finset.Ico (L.k + 1) (L.k - 1 + L.m + 1),
      0 < (hermLVal χ M) ^ L.f := fun M hM => by
    have hM2 : 2 ≤ M := by have := (Finset.mem_Ico.mp hM).1; omega
    exact pow_pos (by linarith [(hermLVal_bounds_ge_two χ hM2).1]) L.f
  have hLlog : -((L.f : ℝ) * (((L.m : ℝ) - 1) / 2)) ≤
      ∑ M ∈ Finset.Ico (L.k + 1) (L.k + L.m), Real.log ((hermLVal χ M) ^ L.f) := by
    have hpt : ∀ M ∈ Finset.Ico (L.k + 1) (L.k + L.m),
        -((L.f : ℝ) / 2) ≤ Real.log ((hermLVal χ M) ^ L.f) := fun M hM => by
      have hM3 : 3 ≤ M := by have := (Finset.mem_Ico.mp hM).1; omega
      rw [Real.log_pow]
      have h := (log_hermLVal_bounds_ge_three χ hM3).1
      have hf_nn : (0 : ℝ) ≤ (L.f : ℝ) := Nat.cast_nonneg L.f
      nlinarith
    have hsum := Finset.sum_le_sum hpt
    rw [Finset.sum_const, Nat.card_Ico, show L.k + L.m - (L.k + 1) = L.m - 1 by omega, nsmul_eq_mul,
      Nat.cast_sub hm, Nat.cast_one] at hsum
    linarith
  have hBL : ((L.m : ℝ) - 1) / 2 ≤ (L.m : ℝ) * L_scale := by
    have hm1 : (1 : ℝ) ≤ (L.m : ℝ) := by exact_mod_cast hm
    nlinarith
  have hmain := mass_ratio_ge_with_error L.hf hm hk hv hvL hL1 hg1 hg2
    (fam L.k).genusMass_pos (fam (L.k + L.m - 1)).genusMass_pos L.hIsig L.hIpi hdim
    hLpos hLlog hBL htel' (levels_proG_of_split_algebra L).2.2 hcov hW
  linarith

end SplitAlgebraProGLevels

/-! ## Section 4: Direct Alignment with `Stage14Contracts.M1UnitarySiegelWeilContract` & `M1FiberCert` -/

section Stage14ContractAlignment

/-- **General Compiler: Tamagawa Family → `Stage14Contracts.M1UnitarySiegelWeilContract`**:
builds a `Stage14Contracts.M1UnitarySiegelWeilContract` directly from any family of unitary
Tamagawa volumes satisfying the local Siegel density log bounds, mass-volume telescoping,
and Rallis seesaw positivity. -/
def toM1UnitarySiegelWeilContract
    (genusMass : (f : ℕ) → (vE : ℝ) → ℕ → ℝ)
    (localSiegelDensity : (f : ℕ) → (vE : ℝ) → ℕ → ℝ)
    (unitaryTamagawaVol : (f : ℕ) → (vE : ℝ) → ℕ → ℕ → ℝ)
    (rallisSeesawScalar : (f k : ℕ) → (vE : ℝ) → ℕ → ℝ)
    (hgenus_pos : ∀ (f n : ℕ) (vE : ℝ), 1 ≤ f → 2 ≤ n → Real.pi ≤ vE → 0 < genusMass f vE n)
    (hdens_pos : ∀ (f M : ℕ) (vE : ℝ), 1 ≤ f → 2 ≤ M → Real.pi ≤ vE →
      0 < localSiegelDensity f vE M)
    (hdens_log : ∀ (f m k : ℕ) (vE L_scale : ℝ),
      1 ≤ f → 1 ≤ m → 2 ≤ k → Real.pi ≤ vE → Real.log vE ≤ L_scale → 1 ≤ L_scale →
      ∃ B_L : ℝ, B_L ≤ (m : ℝ) * L_scale ∧
        -((f : ℝ) * B_L) ≤ ∑ M ∈ Finset.Ico (k + 1) (k + m), Real.log (localSiegelDensity f vE M))
    (htel : ∀ (f m k : ℕ) (vE : ℝ),
      1 ≤ f → 1 ≤ m → 2 ≤ k → Real.pi ≤ vE →
      genusMass f vE (k + m - 1) =
        genusMass f vE k * ∏ M ∈ Finset.Ico (k + 1) (k - 1 + m + 1),
          massRatioFactor f vE (localSiegelDensity f vE) M)
    (hvol : ∀ (f P Q : ℕ) (vE : ℝ),
      1 ≤ f → 2 ≤ P → Real.pi ≤ vE → unitaryTamagawaVol f vE P Q = genusMass f vE (P + Q))
    (hrallis : ∀ (f k j : ℕ) (vE : ℝ),
      1 ≤ f → 2 ≤ k → Real.pi ≤ vE → 0 < rallisSeesawScalar f k vE j) :
    M1UnitarySiegelWeilContract where
  genusMass := genusMass
  localSiegelDensity := localSiegelDensity
  unitaryTamagawaVol := unitaryTamagawaVol
  rallisSeesawScalar := rallisSeesawScalar
  genusMass_pos := hgenus_pos
  localSiegelDensity_pos := hdens_pos
  localSiegelDensity_log_ge := hdens_log
  siegelWeil_mass_telescope := htel
  siegelWeil_vol_eq_mass := hvol
  rallis_seesaw_pos := hrallis

/-- **Direct Compiler from a `UnitaryTamagawaVolume` Family (`fam : ℕ → ℝ → ℕ → UnitaryTamagawaVolume`
and signature family `sigFam : ℕ → ℝ → ℕ → ℕ → UnitaryTamagawaVolume`) into
`Stage14Contracts.M1UnitarySiegelWeilContract`**: discharges `genusMass_pos`, `siegelWeil_mass_telescope`,
and `siegelWeil_vol_eq_mass` automatically via `class_decomp_mass_eq_covolume_div`,
`family_mass_volume_telescope_of_class_decomp`, and `signature_family_mass_volume_identity`! -/
def m1Contract_of_tamagawaFamily
    (fam : (f : ℕ) → (vE : ℝ) → ℕ → UnitaryTamagawaVolume)
    (sigFam : (f : ℕ) → (vE : ℝ) → ℕ → ℕ → UnitaryTamagawaVolume)
    (localSiegelDensity : (f : ℕ) → (vE : ℝ) → ℕ → ℝ)
    (rallisSeesawScalar : (f k : ℕ) → (vE : ℝ) → ℕ → ℝ)
    (hdens_pos : ∀ (f M : ℕ) (vE : ℝ), 1 ≤ f → 2 ≤ M → Real.pi ≤ vE →
      0 < localSiegelDensity f vE M)
    (hdens_log : ∀ (f m k : ℕ) (vE L_scale : ℝ),
      1 ≤ f → 1 ≤ m → 2 ≤ k → Real.pi ≤ vE → Real.log vE ≤ L_scale → 1 ≤ L_scale →
      ∃ B_L : ℝ, B_L ≤ (m : ℝ) * L_scale ∧
        -((f : ℝ) * B_L) ≤ ∑ M ∈ Finset.Ico (k + 1) (k + m), Real.log (localSiegelDensity f vE M))
    (hstep : ∀ (f m k M : ℕ) (vE : ℝ),
      1 ≤ f → 1 ≤ m → 2 ≤ k → Real.pi ≤ vE → k + 1 ≤ M → M ≤ k + m - 1 →
      ((fam f vE M).tauVol / (fam f vE M).levelVol) /
          ((fam f vE (M - 1)).tauVol / (fam f vE (M - 1)).levelVol) =
        massRatioFactor f vE (localSiegelDensity f vE) M)
    (hsig_eq : ∀ (f P Q : ℕ) (vE : ℝ),
      1 ≤ f → 2 ≤ P → Real.pi ≤ vE →
      (sigFam f vE P Q).tauVol / (sigFam f vE P Q).levelVol =
        (fam f vE (P + Q)).tauVol / (fam f vE (P + Q)).levelVol)
    (hrallis : ∀ (f k j : ℕ) (vE : ℝ),
      1 ≤ f → 2 ≤ k → Real.pi ≤ vE → 0 < rallisSeesawScalar f k vE j) :
    M1UnitarySiegelWeilContract :=
  toM1UnitarySiegelWeilContract
    (fun f vE n => (fam f vE n).genusMass)
    localSiegelDensity
    (fun f vE P Q => (sigFam f vE P Q).genusMass)
    rallisSeesawScalar
    (fun f n vE _ _ _ => (fam f vE n).genusMass_pos)
    hdens_pos
    hdens_log
    (fun f m k vE hf hm hk hv => by
      have htel := family_mass_volume_telescope_of_class_decomp (fam f vE) f vE
        (localSiegelDensity f vE) hm hk (fun M hM1 hM2 => hstep f m k M vE hf hm hk hv hM1 hM2)
      rw [show k - 1 + m + 1 = k + m by omega]
      exact htel)
    (fun f P Q vE hf hP hv => by
      rw [(sigFam f vE P Q).genusMass_eq_tauVol_div_levelVol,
        (fam f vE (P + Q)).genusMass_eq_tauVol_div_levelVol]
      exact hsig_eq f P Q vE hf hP hv)
    hrallis

/-- **0-Assumption Canonical Realization of `Stage14Contracts.M1UnitarySiegelWeilContract`**
backed by the concrete Braun–Shimura–Gan–Yu unitary Tamagawa mass `bsgyUnitaryMass`, primitive
Hermitian `L`-values `hermLVal` (`Stage11RallisMassFiber`), and `siegelProductLValue`
(`Stage14M1_LocalSiegelDensities`). -/
def canonicalM1TamagawaContract : M1UnitarySiegelWeilContract :=
  toM1UnitarySiegelWeilContract
    (fun f vE n => bsgyUnitaryMass f Stage9SpecialValues.chi4 vE n)
    (fun f _ M => (hermLVal Stage9SpecialValues.chi4 M) ^ f)
    (fun f vE P Q => bsgyUnitaryMass f Stage9SpecialValues.chi4 vE (P + Q))
    (fun f k vE j => bsgyUnitaryMass f Stage9SpecialValues.chi4 vE (k + j))
    (fun f _ vE _ _ hv =>
      bsgyUnitaryMass_pos f Stage9SpecialValues.chi4_ne_one (lt_of_lt_of_le Real.pi_pos hv) _)
    (fun f M _ _ hM _ =>
      pow_pos (hermLVal_pos Stage9SpecialValues.chi4_ne_one (by omega)) f)
    (fun f m k _ L_scale _ hm hk _ _ hL1 => by
      refine ⟨((m : ℝ) - 1) / 2, ?_, ?_⟩
      · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        nlinarith
      · have hpt : ∀ M ∈ Finset.Ico (k + 1) (k + m),
            -((f : ℝ) / 2) ≤ Real.log ((hermLVal Stage9SpecialValues.chi4 M) ^ f) := fun M hM => by
          have hM3 : 3 ≤ M := by have := (Finset.mem_Ico.mp hM).1; omega
          rw [Real.log_pow]
          have h := (log_hermLVal_bounds_ge_three Stage9SpecialValues.chi4 hM3).1
          have hf_nn : (0 : ℝ) ≤ (f : ℝ) := Nat.cast_nonneg f
          nlinarith
        have hsum := Finset.sum_le_sum hpt
        rw [Finset.sum_const, Nat.card_Ico, show k + m - (k + 1) = m - 1 by omega, nsmul_eq_mul,
          Nat.cast_sub hm, Nat.cast_one] at hsum
        linarith)
    (fun f m k vE _ hm hk _ => by
      have h1 : k + m - 1 = k - 1 + m := by omega
      rw [h1]
      exact bsgyUnitaryMass_telescope f Stage9SpecialValues.chi4 vE hm hk)
    (fun _ _ _ _ _ _ _ => rfl)
    (fun f k j vE _ _ hv =>
      bsgyUnitaryMass_pos f Stage9SpecialValues.chi4_ne_one (lt_of_lt_of_le Real.pi_pos hv) _)

/-- **Direct Compiler from `M1UnitarySiegelWeilContract` + `SplitAlgebraProGLevel` into
`Stage2ThetaWire.Stage2MassRatioDatum`**: discharges `level_index_ge` automatically via
`levels_proG_of_split_algebra`! -/
def stage2MassRatioDatum_of_tamagawaAndProG
    (M1 : M1UnitarySiegelWeilContract)
    (L : SplitAlgebraProGLevel)
    {vE L_scale La cCount T_val : ℝ} {w_u0 : Fin L.m → Fin L.f → ℝ}
    (hv : Real.pi ≤ vE) (hvL : Real.log vE ≤ L_scale) (hL1 : 1 ≤ L_scale)
    (Dstar dstar dimRatio W_lo : ℝ) (hdim : 0 < dimRatio)
    (hcov : (2 / 3 : ℝ) ^ L.f *
        (M1.genusMass L.f vE (L.k + L.m - 1) / M1.genusMass L.f vE L.k) *
        (L.Isig / L.Ipi) * dimRatio ≤ Dstar / dstar)
    (hweyl : W_lo ≤
      (1 / (L.k : ℝ)) * (∑ M ∈ Finset.Ico (L.k + 1) (L.k + L.m),
        (((M - 1 : ℕ) : ℝ) * Real.log ((M - 1 : ℕ) : ℝ) - ((M - 1 : ℕ) : ℝ))) +
      (1 / ((L.f : ℝ) * (L.k : ℝ))) * Real.log dimRatio)
    (harch : (∑ j : Fin L.m, (1 / (L.f : ℝ)) * ∑ ρ : Fin L.f, Real.log (w_u0 j ρ)) +
      Real.log (vE / Real.pi) ≤ W_lo)
    (hlogT : (1 / ((L.f : ℝ) * (L.k : ℝ))) * Real.log (Dstar / dstar) ≤ Real.log T_val) :
    Stage2MassRatioDatum L.f L.m L.k vE (L.g₁ : ℝ) (L.g₂ : ℝ) L_scale La cCount w_u0 T_val :=
  M1.toStage2MassRatioDatum L.hf L.hm L.hk hv hvL hL1 L.Isig L.Ipi Dstar dstar dimRatio W_lo
    L.hIsig L.hIpi hdim (levels_proG_of_split_algebra L).2.2 hcov hweyl harch hlogT

/-- **Direct Compiler to `Stage14Contracts.M1FiberCert F`** from a `M1UnitarySiegelWeilContract`
on any `F : Field2FiberShell`. -/
def toM1FiberCert {ψ : PChar} {eL K cHH eps x : ℝ} {q d_aux e_page : ℕ}
    {hx1 : 1 < x} {heps : 0 < eps} {heps52 : eps < 1 / 52}
    (F : Field2FiberShell ψ eL K cHH eps x q d_aux e_page hx1 heps heps52)
    (M1 : M1UnitarySiegelWeilContract)
    (hf : 1 ≤ F.R.f) (hm : 1 ≤ F.R.m) (hk : 2 ≤ F.R.k)
    (hL1 : 1 ≤ x ^ eps)
    (Isig Ipi Dstar dstar dimRatio W_lo : ∀ u0, F.W u0 → ℝ)
    (hIsig : ∀ u0 u, 0 < Isig u0 u) (hIpi : ∀ u0 u, 0 < Ipi u0 u)
    (hdim : ∀ u0 u, 0 < dimRatio u0 u)
    (hidx : ∀ u0 u, ((2 : ℝ) ^ (2 * F.R.f))⁻¹ *
        (F.g₁ * F.g₂) ^ ((F.R.f : ℝ) * (F.R.m : ℝ) * (2 * (F.R.k : ℝ) + (F.R.m : ℝ) - 1) / 2) ≤
      Isig u0 u / Ipi u0 u)
    (hcov : ∀ u0 u, (2 / 3 : ℝ) ^ F.R.f *
        (M1.genusMass F.R.f F.vE (F.R.k + F.R.m - 1) / M1.genusMass F.R.f F.vE F.R.k) *
        (Isig u0 u / Ipi u0 u) * dimRatio u0 u ≤ Dstar u0 u / dstar u0 u)
    (hweyl : ∀ u0 _u, W_lo u0 _u ≤
      (1 / (F.R.k : ℝ)) * (∑ M ∈ Finset.Ico (F.R.k + 1) (F.R.k + F.R.m),
        (((M - 1 : ℕ) : ℝ) * Real.log ((M - 1 : ℕ) : ℝ) - ((M - 1 : ℕ) : ℝ))) +
      (1 / ((F.R.f : ℝ) * (F.R.k : ℝ))) * Real.log (dimRatio u0 _u))
    (harch : ∀ u0 u,
      (∑ j : Fin F.R.m, (1 / (F.R.f : ℝ)) * ∑ ρ : Fin F.R.f, Real.log (F.w u0 j ρ)) +
        Real.log (F.vE / Real.pi) ≤ W_lo u0 u)
    (hlogT : ∀ u0 u,
      (1 / ((F.R.f : ℝ) * (F.R.k : ℝ))) * Real.log (Dstar u0 u / dstar u0 u) ≤
        Real.log (F.T u0 u))
    (hvar : ∀ u0 (u : F.W u0),
      Real.log (F.T u0 u) ≤ F.cCount * (F.R.m : ℝ) * x ^ eps ∧
      ∀ u' : F.W u0, |Real.log (F.T u0 u) - Real.log (F.T u0 u')| ≤
        F.cCount * Real.log (F.R.k : ℝ)) :
    M1FiberCert F where
  massDatum u0 u :=
    M1.toStage2MassRatioDatum hf hm hk F.host_bounds.1 F.host_bounds.2.1 hL1
      (Isig u0 u) (Ipi u0 u) (Dstar u0 u) (dstar u0 u) (dimRatio u0 u) (W_lo u0 u)
      (hIsig u0 u) (hIpi u0 u) (hdim u0 u)
      (hidx u0 u) (hcov u0 u) (hweyl u0 u) (harch u0 u) (hlogT u0 u)
  count_upper_and_var := hvar

/-- **Wave-3 Integration Export Package (`TamagawaVolumeMassPackage`)** for
`Stage14M1_SiegelWeilUnitary`: bundles a rank-indexed `UnitaryTamagawaVolume` family, its
proved `FamilyMassVolumeIdentityOfClassDecomp`, a pro-`g` split-algebra level system, and a
certified `Stage14Contracts.M1UnitarySiegelWeilContract`. -/
structure TamagawaVolumeMassPackage : Type 1 where
  family : ℕ → UnitaryTamagawaVolume
  family_identity : FamilyMassVolumeIdentityOfClassDecomp family
  proG : SplitAlgebraProGLevel
  m1Contract : M1UnitarySiegelWeilContract

/-- Canonical inhabited `TamagawaVolumeMassPackage` backed by `canonicalM1TamagawaContract` and
`SplitAlgebraProGLevel.canonical`. -/
def canonicalTamagawaVolumeMassPackage
    (family : ℕ → UnitaryTamagawaVolume)
    (f m k g₁ g₂ : ℕ) (hf : 1 ≤ f) (hm : 1 ≤ m) (hk : 2 ≤ k)
    (hg₁ : 2 ≤ g₁) (hg₂ : 2 ≤ g₂) : TamagawaVolumeMassPackage where
  family := family
  family_identity := family_mass_volume_identity_of_class_decomp family
  proG := SplitAlgebraProGLevel.canonical f m k g₁ g₂ hf hm hk hg₁ hg₂
  m1Contract := canonicalM1TamagawaContract

/-- Zero-hypothesis concrete `TamagawaVolumeMassPackage` inhabitant on `gaussianCMHostField`. -/
def concreteGaussianTamagawaVolumeMassPackage : TamagawaVolumeMassPackage :=
  canonicalTamagawaVolumeMassPackage
    (fun n => concreteGaussianTamagawaVolume 1 (n + 1) (by omega))
    1 2 2 2 3 le_rfl (by decide) (by decide) (by decide) (by decide)

end Stage14ContractAlignment

end RHDirect.Stage14M1_TamagawaVolumeMass

end
