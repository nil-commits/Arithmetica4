import RHDirect.Stage11GroundingAudit
import RHDirect.Stage11LinnikUnconditional
import RHDirect.Stage11BombieriVinogradov
import RHDirect.Stage11LLLSiegelReduction
import RHDirect.Stage11ModularSymbols
import RHDirect.Stage11HermitianCurvature
import RHDirect.Stage11GL2SmoothRep
import RHDirect.CFT_HilbertClassField
import RHDirect.CFT_HilbertArtinBridge
import RHDirect.ChenTheorem
import RHDirect.DworkRatMain
import RHDirect.DworkRatFredholmComplete
import RHDirect.DworkZetaPolyElliptic
import RHDirect.LatticeSmoothingFull

/-!
# RHDirect.UnifiedSoundnessAudit

Forensic, kernel-checked soundness audit superseding `RHDirect.Stage11GroundingAudit`.

`Stage11GroundingAudit` covered only 18 of the 33 Stage 11 modules and over-classified several
proxy / formula-model modules (`Stage11MoriwakiCovolume`, `Stage11Sym2AdjointL`,
`Stage11DoublingRallis`, `Stage11BesselWaveSchur`, `Stage11RallisMassFiber`,
`Stage11StickelbergerRamified`, `Stage11LocalLanglandsGL2`, `Stage11ConcretePatching`,
`Stage11BaseChangeTrace`, `Stage11GaloisModularityBridge`, `Stage11IharaLevelRaising`) without
disclosing their proxy definitions or omitting the remaining 15 Stage 11 files (`Stage11ArakelovFaltings`,
`Stage11IwasawaMainConj`, `Stage11ThetaSiegelBridge`, etc.).

This module provides:
1. A strict three-tier classification `SoundnessTier`:
   - `unconditionalNativeMathlib` (`0` extra assumptions, native Mathlib types, non-proxy)
   - `conditionalExplicitHyp` (mathematically sound reduction taking explicit un-discharged hypotheses)
   - `proxyOrSyntheticModel` (formula proxy, synthetic algebraic quotient, or toy witness — NOT
     equivalent to the classical native-Mathlib theorem)
2. A complete `unifiedAuditManifest : List AuditEntry` covering ALL **33** Stage 11 modules plus
   the newly verified Tier-A campaigns (`GlobalCFT`, `ChenTheorem`, `DworkRatMain`,
   `DworkRatFredholmComplete`, `DworkZetaPolyElliptic`, `LatticeSmoothingFull`).
3. Explicit zero-assumption **type-pinning zero-drift witnesses** (`witness_*`) whose Lean type
   signatures pin the exact zero-hypothesis native-Mathlib statements of our Tier-A crown theorems.
4. Decidable consistency theorems over `unifiedAuditManifest` proved via `decide` (zero
   `native_decide`).

Zero `sorry`, zero custom `axiom`s, zero `opaque`, zero `native_decide`, zero `import Mathlib`.
-/

namespace RHDirect.UnifiedSoundnessAudit

open scoped ArithmeticFunction.vonMangoldt BigOperators UpperHalfPlane

/-! ## 1. Honest Three-Tier Soundness Classification -/

/-- Strict three-tier forensic soundness classification determined by inspecting actual Lean
type signatures and definitions (never docstrings or README claims). -/
inductive SoundnessTier where
  /-- Zero un-discharged hypotheses (`0` extra assumptions), operating directly on native
  Mathlib mathematical objects (non-proxy). -/
  | unconditionalNativeMathlib
  /-- Mathematically sound reduction or partial theorem whose Lean signature explicitly takes
  un-discharged hypotheses (or open contract fields). -/
  | conditionalExplicitHyp
  /-- Formula proxy, synthetic algebraic quotient, hardcoded toy model, or mismatched claim
  that is NOT equivalent to the classical native-Mathlib theorem. -/
  | proxyOrSyntheticModel
  deriving Repr, DecidableEq

/-- Structured forensic audit entry for one module or campaign root. -/
structure AuditEntry where
  moduleName : String
  campaign : String
  tier : SoundnessTier
  mainTheoremOrTarget : String
  priorStage11AuditClass : String
  rationale : String
  deriving Repr, DecidableEq

/-! ## 2. Complete Stage 11 Manifest (All 33 Modules) & Newly Verified Tier-A Campaigns -/

/-- Complete honest audit ledger covering all **33** `RHDirect.Stage11*` modules, fixing all 15
omissions and correcting all over-classifications from `Stage11GroundingAudit`. -/
def stage11Manifest : List AuditEntry := [
  { moduleName := "RHDirect.Stage11ArakelovFaltings"
    campaign := "Stage11"
    tier := .proxyOrSyntheticModel
    mainTheoremOrTarget := "faltingsHeight; arithmetic_hodge_index"
    priorStage11AuditClass := "OMITTED"
    rationale := "Tier C #5: faltingsHeight is defined directly as -(1/12) log((2π)^12 ‖Δ(τ)‖ y^6) without elliptic curves, Néron models, or Hodge bundles; ArithSurfaceModel hardcodes a Lorentzian quadratic form." },
  { moduleName := "RHDirect.Stage11BaseChangeTrace"
    campaign := "Stage11"
    tier := .proxyOrSyntheticModel
    mainTheoremOrTarget := "concreteSolvablePrimeStepBaseChange; SolvableDescentEquiv"
    priorStage11AuditClass := "concreteAlgebraicClassification"
    rationale := "Tier C #9: rank-1 ℂˣ character model (π ↦ π^p), not genuine GL_n automorphic base change." },
  { moduleName := "RHDirect.Stage11BesselWaveSchur"
    campaign := "Stage11"
    tier := .proxyOrSyntheticModel
    mainTheoremOrTarget := "wavePacket; bessel_grid_cotlar_stein_opNorm_le"
    priorStage11AuditClass := "mathlibNativeUnconditional"
    rationale := "Tier C #8: Cotlar–Stein / Schur norm bounds on EuclideanSpace are genuine, but wavePacket is a Euclidean Gaussian Gabor packet with zero Bessel functions." },
  { moduleName := "RHDirect.Stage11BombieriVinogradov"
    campaign := "Stage11"
    tier := .unconditionalNativeMathlib
    mainTheoremOrTarget := "bombieri_vinogradov; brun_titchmarsh_all"
    priorStage11AuditClass := "OMITTED"
    rationale := "Tier A: 0-assumption Bombieri–Vinogradov (ϑ = 1/2) and Brun–Titchmarsh directly on native ArithmeticFunction.vonMangoldt, Nat.totient, and Nat.Prime." },
  { moduleName := "RHDirect.Stage11BostDworkSqueeze"
    campaign := "Stage11"
    tier := .conditionalExplicitHyp
    mainTheoremOrTarget := "stage11_thetaSlopeContract : Stage11ThetaCoreInputs S → ThetaSlopeContract S"
    priorStage11AuditClass := "parameterizedStage3Discharge"
    rationale := "Tier B: sound reduction of ThetaSlopeContract S to explicit un-discharged Stage11ThetaCoreInputs S." },
  { moduleName := "RHDirect.Stage11ConcretePatching"
    campaign := "Stage11"
    tier := .proxyOrSyntheticModel
    mainTheoremOrTarget := "S12_concrete_selmer_realization; S24_odd_congruence_log_bound"
    priorStage11AuditClass := "concreteAlgebraicClassification"
    rationale := "Tier C #3: S24 Hecke discriminant divisibility 3^2 * 144169 ∣ disc T_2 is genuine, but CongruencePatchingRealization witnesses use toy constant Selmer systems (shaLen := 0 or constant v_l)." },
  { moduleName := "RHDirect.Stage11CrystallineFontaine"
    campaign := "Stage11"
    tier := .proxyOrSyntheticModel
    mainTheoremOrTarget := "delta12_weaklyAdmissible"
    priorStage11AuditClass := "OMITTED"
    rationale := "Tier C #9: Fontaine–Laffaille proxy where delta12_weaklyAdmissible holds for arbitrary a : ℤ." },
  { moduleName := "RHDirect.Stage11DefiniteUnitaryChain"
    campaign := "Stage11"
    tier := .unconditionalNativeMathlib
    mainTheoremOrTarget := "chain_hermitian_minkowski_bost_bridge; chainRank_realizes_rankVal"
    priorStage11AuditClass := "concreteAlgebraicClassification"
    rationale := "Tier A (finite-dim Hermitian lattice scope): genuine EuclideanSpace ℂ (Fin N), Matrix.PosDef, ZLattice.covolume, and Minkowski–Bost slope bridge." },
  { moduleName := "RHDirect.Stage11DeuringHeilbronn"
    campaign := "Stage11"
    tier := .unconditionalNativeMathlib
    mainTheoremOrTarget := "deuring_heilbronn_unconditional"
    priorStage11AuditClass := "OMITTED"
    rationale := "Tier A: unconditional Deuring–Heilbronn zero repulsion directly on native DirichletCharacter.LFunction." },
  { moduleName := "RHDirect.Stage11DiamondFujiwara"
    campaign := "Stage11"
    tier := .conditionalExplicitHyp
    mainTheoremOrTarget := "Diamond–Fujiwara patching reduction"
    priorStage11AuditClass := "OMITTED"
    rationale := "Tier B: sound patching reduction explicitly assuming the patched limit exists." },
  { moduleName := "RHDirect.Stage11DoublingRallis"
    campaign := "Stage11"
    tier := .proxyOrSyntheticModel
    mainTheoremOrTarget := "localDoublingFactorUn_eq; E8_global_doubling_euler_product"
    priorStage11AuditClass := "mathlibNativeUnconditional"
    rationale := "Tier C #8: localDoublingFactorUn_eq is Finset.prod_mul_distrib on a hardcoded scalar formula with zero Haar integral or doubling zeta integral." },
  { moduleName := "RHDirect.Stage11EulerSystemSelmer"
    campaign := "Stage11"
    tier := .conditionalExplicitHyp
    mainTheoremOrTarget := "galoisModularityContract_of_eulerSystemSupply"
    priorStage11AuditClass := "parameterizedStage3Discharge"
    rationale := "Tier B: sound reduction discharging GaloisModularityContract S while axiomatizing Kolyvagin / Poitou–Tate hypotheses inside EulerSystemWindowSupply." },
  { moduleName := "RHDirect.Stage11FerreroWashington"
    campaign := "Stage11"
    tier := .conditionalExplicitHyp
    mainTheoremOrTarget := "iwasawaTwoTowerBound_of_cyclic_mu_zero; irregular_prime_37_layerQuot_exact_growth"
    priorStage11AuditClass := "mathlibNativeUnconditional"
    rationale := "Tier B: genuine PadicInt / PowerSeries μ = 0 algebra on Kubota–Leopoldt series, but iwasawaTwoTowerBound_of_cyclic_mu_zero takes un-discharged Sel ↪ LayerQuot and sha_le_selmer without a ClassGroup link." },
  { moduleName := "RHDirect.Stage11GaloisModularityBridge"
    campaign := "Stage11"
    tier := .proxyOrSyntheticModel
    mainTheoremOrTarget := "exists_concrete_minimalAutomorphyInputs"
    priorStage11AuditClass := "concreteAlgebraicClassification"
    rationale := "Tier C #9: exists_concrete_minimalAutomorphyInputs fills 36 interface fields with True / trivial." },
  { moduleName := "RHDirect.Stage11GL2SmoothRep"
    campaign := "Stage11"
    tier := .unconditionalNativeMathlib
    mainTheoremOrTarget := "satakeGL2OfEigenform_smooth_hecke_grounding; classical_eigenforms_gl2_smooth_hecke_match"
    priorStage11AuditClass := "OMITTED"
    rationale := "Tier A: genuine Iwasawa/Bruhat decomposition, spherical T_p Satake eigenvalue, and Steinberg Iwahori-fixed finrank = 1 on native Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]." },
  { moduleName := "RHDirect.Stage11GroundingAudit"
    campaign := "Stage11"
    tier := .proxyOrSyntheticModel
    mainTheoremOrTarget := "stage11GroundingManifest"
    priorStage11AuditClass := "OMITTED"
    rationale := "Tier C #13: superseded manifest covering only 18/33 Stage 11 files and over-classifying multiple proxy modules as mathlibNativeUnconditional." },
  { moduleName := "RHDirect.Stage11HermitianCurvature"
    campaign := "Stage11"
    tier := .unconditionalNativeMathlib
    mainTheoremOrTarget := "modularForm_eq_zero_of_weight_neg; cuspForm_eq_zero_of_weight_neg; gauss_bonnet_sl2Z_orbifold"
    priorStage11AuditClass := "mathlibNativeUnconditional"
    rationale := "Tier A: 0-assumption Bochner Laplacian identity and negative-weight vanishing directly on native UpperHalfPlane, ModularForm, and CuspForm." },
  { moduleName := "RHDirect.Stage11IharaLevelRaising"
    campaign := "Stage11"
    tier := .proxyOrSyntheticModel
    mainTheoremOrTarget := "ribet_level_raising_criterion; concreteWitnessLattice"
    priorStage11AuditClass := "concreteAlgebraicClassification"
    rationale := "Tier B/C #9: abstract Ribet criterion assumes hα_sat, and the level 11 → 22 witness concreteWitnessLattice is a hardcoded ℤ^4 lattice." },
  { moduleName := "RHDirect.Stage11IwasawaMainConj"
    campaign := "Stage11"
    tier := .proxyOrSyntheticModel
    mainTheoremOrTarget := "main_conjecture_irregular_prime_37"
    priorStage11AuditClass := "OMITTED"
    rationale := "Tier C #2: zero occurrences of ClassGroup or NumberField.classNumber; defines X32 := IwasawaAlg 37 ⧸ Ideal.span {F32} and proves charIdeal(Λ/(F32)) = (F32)." },
  { moduleName := "RHDirect.Stage11LinnikBridge"
    campaign := "Stage11"
    tier := .conditionalExplicitHyp
    mainTheoremOrTarget := "linnikAPInterval_of_dh_and_logfree; linnik_exp_three_eventually_of_GRH"
    priorStage11AuditClass := "parameterizedStage3Discharge"
    rationale := "Tier B: sound reduction of LinnikAPDyadic / LinnikAPInterval to explicit DeuringHeilbronnHypothesis and LogFreeZeroDensityHypothesis (discharged in Stage11LinnikUnconditional)." },
  { moduleName := "RHDirect.Stage11LinnikUnconditional"
    campaign := "Stage11"
    tier := .unconditionalNativeMathlib
    mainTheoremOrTarget := "linnik_least_prime_in_ap_unconditional; linnikAPInterval_unconditional"
    priorStage11AuditClass := "OMITTED"
    rationale := "Tier A: 0-assumption Linnik's Theorem (1944) and Stage2PrimePairs.LinnikAPInterval on native Nat.Prime and Nat.ModEq (module also defines conditional 2-field RH bundle Stage11UnifiedInputs)." },
  { moduleName := "RHDirect.Stage11LLLSiegelReduction"
    campaign := "Stage11"
    tier := .unconditionalNativeMathlib
    mainTheoremOrTarget := "exists_lll_reduced_basis; exists_lll_reduced_basis_euclidean; exists_siegelReduced_lll_basis_for_stage3"
    priorStage11AuditClass := "OMITTED"
    rationale := "Tier A: 0-assumption Lovász LLL basis existence and Siegel-reduction bounds directly on native Submodule ℤ E and IsZLattice ℝ Λ." },
  { moduleName := "RHDirect.Stage11LocalLanglandsGL2"
    campaign := "Stage11"
    tier := .proxyOrSyntheticModel
    mainTheoremOrTarget := "llcGL2 : GL2LocalRep p ≃ WD2Param p"
    priorStage11AuditClass := "concreteAlgebraicClassification"
    rationale := "Tier C #4: syntactic enum bijection GL2LocalRep ≃ WD2Param (localLFactor_llcGL2_eq is cases π <;> rfl, omitting wild p=2 supercuspidals; genuine smooth GL₂(ℚ_p) is in Stage11GL2SmoothRep)." },
  { moduleName := "RHDirect.Stage11LogFreeDensity"
    campaign := "Stage11"
    tier := .unconditionalNativeMathlib
    mainTheoremOrTarget := "logFreeZeroDensity_unconditional"
    priorStage11AuditClass := "OMITTED"
    rationale := "Tier A: unconditional Gallagher log-free zero-density estimate directly on native DirichletCharacter.LFunction." },
  { moduleName := "RHDirect.Stage11MazurDeformation"
    campaign := "Stage11"
    tier := .proxyOrSyntheticModel
    mainTheoremOrTarget := "universal deformation ring proxy"
    priorStage11AuditClass := "OMITTED"
    rationale := "Tier C #9: no Schlessinger universal deformation ring R_{rhoBar} for residually irreducible Galois representations." },
  { moduleName := "RHDirect.Stage11ModularSymbols"
    campaign := "Stage11"
    tier := .unconditionalNativeMathlib
    mainTheoremOrTarget := "manin_delta_period_ratios; periodPoly_S_relation; modularSymbol_hecke_distribution; mttDist_compat"
    priorStage11AuditClass := "OMITTED"
    rationale := "Tier A: 0-assumption Eichler–Shimura period polynomials, Manin period ratios (691 Λ(Δ,1) = 1620 Λ(Δ,3) = 2520 Λ(Δ,5)), and MTT p-adic distributions directly on Mathlib CuspForm." },
  { moduleName := "RHDirect.Stage11MoriwakiCovolume"
    campaign := "Stage11"
    tier := .proxyOrSyntheticModel
    mainTheoremOrTarget := "cmHermHSChainSystem; arithSurfaceHSChainSystem; stage3_fiber_covolume_and_small_sections"
    priorStage11AuditClass := "mathlibNativeUnconditional"
    rationale := "Tier C #6: diagonal monomial lattice toy model where cmHermHSChainSystem and arithSurfaceHSChainSystem are definitional aliases of projSpaceHSChainSystem." },
  { moduleName := "RHDirect.Stage11RallisMassFiber"
    campaign := "Stage11"
    tier := .proxyOrSyntheticModel
    mainTheoremOrTarget := "perturbedOrthonormalFrame; Stage2ThetaWire fiber discharge"
    priorStage11AuditClass := "parameterizedStage3Discharge"
    rationale := "Tier C #7: contains genuine Schur norm checks on EuclideanSpace, but discharges Stage 2/3 fiber fields via synthetic x-dependent bypasses." },
  { moduleName := "RHDirect.Stage11SecondMomentFrame"
    campaign := "Stage11"
    tier := .unconditionalNativeMathlib
    mainTheoremOrTarget := "bdh_twisted_primes_mean_square_le; twisted_box_mean_square_transfer"
    priorStage11AuditClass := "mathlibNativeUnconditional"
    rationale := "Tier A: 0-assumption Barban–Davenport–Halberstam twisted-prime mean-square transfer on native DirichletCharacter and vonMangoldt (twisted_box_zero_free_and_mean_square_transfer additionally takes hZD)." },
  { moduleName := "RHDirect.Stage11StickelbergerRamified"
    campaign := "Stage11"
    tier := .proxyOrSyntheticModel
    mainTheoremOrTarget := "analyticHMinus; discharges_unified_ramified_branch_of_stickelberger"
    priorStage11AuditClass := "mathlibNativeUnconditional"
    rationale := "Tier C #3: analyticHMinus is an analytic Bernoulli product never linked to ClassGroup, and the ramified discharge uses a toy constant Selmer system." },
  { moduleName := "RHDirect.Stage11Sym2AdjointL"
    campaign := "Stage11"
    tier := .proxyOrSyntheticModel
    mainTheoremOrTarget := "delta12_sym2L_master; adjointLAtOneFromPetersson"
    priorStage11AuditClass := "mathlibNativeUnconditional"
    rationale := "Tier C #8: Secs 1–3 Sym² LSeries Euler product for Re(s) > k+1 and S24 Petersson ratio are unconditional, but Sec 4 defines adjointLAtOneFromPetersson directly as Petersson norm without meromorphic continuation to s = k." },
  { moduleName := "RHDirect.Stage11ThetaSiegelBridge"
    campaign := "Stage11"
    tier := .proxyOrSyntheticModel
    mainTheoremOrTarget := "Stage11ThetaSiegelCoreInputs; certified fixed-x witness"
    priorStage11AuditClass := "OMITTED"
    rationale := "Tier C #7: discharges fields via synthetic bypasses (latM := ℤ[i] ⊂ ℂ¹, circular T_val, exfalso hcompat) and a fixed-x (x = 2^2000) toy witness with shaLen ≡ 0, aT ≡ 0, U0 = W = PUnit." },
  { moduleName := "RHDirect.Stage11WilesPatchingBridge"
    campaign := "Stage11"
    tier := .proxyOrSyntheticModel
    mainTheoremOrTarget := "Wiles patching bridge"
    priorStage11AuditClass := "OMITTED"
    rationale := "Tier C #3: unconditional VWin chains use toy constant Selmer systems and tautological R_∞ = T_∞, phi_inf = AlgHom.id; general l = 2 and ramified branches remain open." }
]

/-- Newly verified Tier-A unconditional native-Mathlib campaigns integrated into `Arithmetica4`. -/
def newCampaignManifest : List AuditEntry := [
  { moduleName := "RHDirect.CFT_HilbertClassField"
    campaign := "GlobalCFT"
    tier := .unconditionalNativeMathlib
    mainTheoremOrTarget := "hilbertClassFieldArtinEquiv; isUnramifiedEverywhere_hilbertClassField; le_hilbertClassField_iff"
    priorStage11AuditClass := "NEW_TIER_A"
    rationale := "Tier A (15-module Local & Global CFT campaign): 0-assumption Hilbert Class Field Artin isomorphism ClassGroup (𝓞 K) ≃* (hilbertClassField K Ω ≃ₐ[K] hilbertClassField K Ω) on native NumberField and ClassGroup." },
  { moduleName := "RHDirect.CFT_HilbertArtinBridge"
    campaign := "GlobalCFT"
    tier := .unconditionalNativeMathlib
    mainTheoremOrTarget := "hilbertArtinData_unconditional"
    priorStage11AuditClass := "NEW_TIER_A"
    rationale := "Tier A: 0-assumption construction of Stage13GL_KummerDuality.HilbertArtinData K Ω from Global CFT (note downstream shaLen_le_of_cl_unconditional still takes explicit cyclotomic bound hB)." },
  { moduleName := "RHDirect.ChenTheorem"
    campaign := "ChenTheorem"
    tier := .unconditionalNativeMathlib
    mainTheoremOrTarget := "chen_theorem"
    priorStage11AuditClass := "NEW_TIER_A"
    rationale := "Tier A (7-module Chen campaign): 0-assumption Chen's Theorem (N = p + P₂) on native Nat.Prime via Rosser–Iwaniec linear sieve and prime/bilinear Bombieri–Vinogradov." },
  { moduleName := "RHDirect.DworkRatMain"
    campaign := "DworkRat"
    tier := .unconditionalNativeMathlib
    mainTheoremOrTarget := "borel_dwork_rationality"
    priorStage11AuditClass := "NEW_TIER_A"
    rationale := "Tier A: 0-assumption Borel–Dwork rationality criterion on native PowerSeries ℚ_[p] and ℤ[[T]] via Hankel determinants and Kronecker's criterion (full Weil I for general varieties remains open)." },
  { moduleName := "RHDirect.DworkRatFredholmComplete"
    campaign := "DworkRat"
    tier := .unconditionalNativeMathlib
    mainTheoremOrTarget := "expSeries_trace_mul_charpoly_rev_eq_one; zetaOfCounts_trace_mul_detOneSubMul"
    priorStage11AuditClass := "NEW_TIER_A"
    rationale := "Tier A: fixes Tier C #11 (DworkRatFredholm docstring gap) by unconditionally proving Jacobi's Fredholm determinant identity exp(∑ Tr(A^m) T^m / m) * det(1 - T·A) = 1 over any char-0 field K." },
  { moduleName := "RHDirect.DworkZetaPolyElliptic"
    campaign := "DworkZeta"
    tier := .unconditionalNativeMathlib
    mainTheoremOrTarget := "zeta_elliptic_complex; zeta_elliptic_den_poly; isRationalPS_zeta_genus_g_descent"
    priorStage11AuditClass := "NEW_TIER_A"
    rationale := "Tier A: unconditional rationality of complex-eigenvalue elliptic and genus-g Hasse–Weil trace generating series in PowerSeries ℚ via ℂ-descent (linking to algebraic variety point counts via Dwork's trace formula remains open)." },
  { moduleName := "RHDirect.LatticeSmoothingFull"
    campaign := "LatticeSmoothing"
    tier := .unconditionalNativeMathlib
    mainTheoremOrTarget := "eta_le_sqrt_n_add_log_div_lambda1; eta_le_sqrt_n_add_log_mul_lambdan; tv_distance_foldedGaussianDensity_fundamentalDomain"
    priorStage11AuditClass := "NEW_TIER_A"
    rationale := "Tier A (4-module LatticeSmoothing campaign): full 0 < ε ≤ 1 MR07 Lemma 3.2, Lemma 3.3 (λ_n & Gram–Schmidt), and Lemma 4.1 (TV distance ≤ ε/2) on native EuclideanSpace ℝ (Fin n) and IsZLattice ℝ Λ." }
]

/-- Unified forensic audit manifest combining all 33 Stage 11 modules and the 7 new Tier-A
campaign roots (40 entries total). -/
def unifiedAuditManifest : List AuditEntry :=
  stage11Manifest ++ newCampaignManifest

/-! ## 3. Type-Pinning Zero-Drift Witnesses (Kernel-Checked!)

Each theorem below pins the **literal zero-hypothesis native-Mathlib Lean type** of a Tier-A
crown theorem so Lean's kernel itself guarantees no hidden `Prop` hypothesis or proxy wrapper
has crept into the statement. -/

/-- Witness 1: **Linnik's Theorem (1944)** on native `Nat.Prime` and `Nat.ModEq` (`0` assumptions). -/
theorem witness_linnik_unconditional :
    ∃ L : ℝ, 0 < L ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (m a : ℕ), 2 ≤ m → Nat.Coprime a m →
        ∃ p : ℕ, Nat.Prime p ∧ p ≡ a [MOD m] ∧ (p : ℝ) ≤ C * (m : ℝ) ^ L :=
  RHDirect.Stage11LinnikUnconditional.linnik_least_prime_in_ap_unconditional

/-- Witness 2: **Bombieri–Vinogradov Theorem (`ϑ = 1/2`)** on native `vonMangoldt` and `Nat.totient`
(`0` assumptions). -/
theorem witness_bombieri_vinogradov_unconditional (A : ℝ) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧
      ∀ x : ℝ, 3 ≤ x →
        ∑ q ∈ Finset.Icc 1 ⌊Real.sqrt x / (Real.log x) ^ B⌋₊,
          RHDirect.Stage11BombieriVinogradov.psiAPMaxError q x ≤ C * x / (Real.log x) ^ A :=
  RHDirect.Stage11BombieriVinogradov.bombieri_vinogradov A

/-- Witness 3: **Chen's Theorem (`N = p + P₂`, 1973)** on native `Nat.Prime` (`0` assumptions). -/
theorem witness_chen_theorem_unconditional :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Even n →
      ∃ p q : ℕ, Nat.Prime p ∧
        (Nat.Prime q ∨ ∃ r s : ℕ, Nat.Prime r ∧ Nat.Prime s ∧ q = r * s) ∧
        p + q = n :=
  RHDirect.Chen.chen_theorem

section HilbertWitness
universe u

/-- Witness 4: **Hilbert Class Field Artin Reciprocity Isomorphism**
`ClassGroup (𝓞 K) ≃* (hilbertClassField K Ω ≃ₐ[K] hilbertClassField K Ω)` plus everywhere
unramified and maximality property on native `NumberField` and `ClassGroup` (`0` extra
assumptions). -/
theorem witness_hilbert_class_field_artin_equiv
    (K : Type u) [Field K] [NumberField K]
    (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] :
    Nonempty (ClassGroup (NumberField.RingOfIntegers K) ≃*
      (RHDirect.CFT.Global.hilbertClassField K Ω ≃ₐ[K]
        RHDirect.CFT.Global.hilbertClassField K Ω)) ∧
    RHDirect.CFT.Global.IsUnramifiedEverywhere K (RHDirect.CFT.Global.hilbertClassField K Ω) ∧
    (∀ (L : IntermediateField K Ω) [FiniteDimensional K L] [IsAbelianGalois K L],
      L ≤ RHDirect.CFT.Global.hilbertClassField K Ω ↔
        RHDirect.CFT.Global.IsUnramifiedEverywhere K L) :=
  ⟨⟨RHDirect.CFT.Global.hilbertClassFieldArtinEquiv K Ω⟩,
   RHDirect.CFT.Global.isUnramifiedEverywhere_hilbertClassField K Ω,
   fun L _ _ => RHDirect.CFT.Global.le_hilbertClassField_iff K Ω L⟩

end HilbertWitness

/-- Witness 5: **Unconditional `HilbertArtinData K Ω`** constructed with zero parameters from
Global Class Field Theory (`0` extra assumptions). -/
theorem witness_hilbert_artin_data_unconditional
    (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] :
    Nonempty (RHDirect.Stage13GL_KummerDuality.HilbertArtinData K Ω) :=
  ⟨RHDirect.CFT.Global.hilbertArtinData_unconditional K Ω⟩

/-- Witness 6: **Borel–Dwork Rationality Criterion** on `ℤ[[T]]` and `PowerSeries ℚ_[p]`
(`0` extra assumptions). -/
theorem witness_borel_dwork_rationality {p : ℕ} [Fact p.Prime] (a : ℕ → ℤ)
    (h_arch : ∃ C₀ A : ℕ, ∀ n, (a n).natAbs ≤ C₀ * A ^ n)
    (h_mero : ∃ (g h : PowerSeries ℚ_[p]),
      (PowerSeries.mk (fun n => (a n : ℚ_[p]))) * h = g ∧ PowerSeries.coeff 0 h = 1 ∧
      (∀ r : ℝ, 0 < r → ∃ C : ℝ, ∀ n,
        ‖PowerSeries.coeff n g‖ ≤ C * r ^ (-(n : ℤ)) ∧
        ‖PowerSeries.coeff n h‖ ≤ C * r ^ (-(n : ℤ)))) :
    RHDirect.DworkRat.IsRationalPS (PowerSeries.mk (fun n => (a n : ℚ))) :=
  RHDirect.DworkRat.borel_dwork_rationality a h_arch h_mero

/-- Witness 7: **Finite-Matrix Jacobi / Fredholm Determinant Identity**
`exp(∑_{m≥1} Tr(A^m) T^m / m) * det(1 - T · A) = 1` over any char-0 field `K`
(`0` extra assumptions). -/
theorem witness_fredholm_jacobi_identity
    {K : Type*} [Field K] [Algebra ℚ K] [CharZero K]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    RHDirect.DworkRat.expSeries
        (PowerSeries.mk fun m => if m = 0 then 0 else (Matrix.trace (A ^ m)) / (m : K)) *
      RHDirect.DworkRat.detOneSubMul A = 1 :=
  RHDirect.DworkRat.expSeries_trace_mul_charpoly_rev_eq_one A

/-- Witness 8: **Complex-Eigenvalue Elliptic Curve Zeta Rationality** descended to
`PowerSeries ℚ` (`0` extra assumptions). -/
theorem witness_elliptic_zeta_complex_rationality
    {a : ℤ} {q : ℕ} (α β : ℂ)
    (ha : α + β = (a : ℂ)) (hq : α * β = (q : ℂ))
    (N : ℕ → ℚ) (hN : ∀ m, (N m : ℂ) = (q : ℂ) ^ m + 1 - (α ^ m + β ^ m)) :
    RHDirect.HasseWeil.zetaSeq N *
        ((1 - PowerSeries.X) * (1 - (q : PowerSeries ℚ) * PowerSeries.X)) =
      1 - (a : PowerSeries ℚ) * PowerSeries.X + (q : PowerSeries ℚ) * PowerSeries.X ^ 2 :=
  RHDirect.HasseWeil.zeta_elliptic_complex α β ha hq N hN

/-- Witness 9: **Full Micciancio–Regev (2007) Lattice Smoothing Suite** on native
`EuclideanSpace ℝ (Fin n)` and `IsZLattice ℝ Λ` (`0` extra assumptions):
- **MR07 Lemma 3.2**: full `0 < ε ≤ 1` dual smoothing bound `η_ε(Λ) ≤ √(n + ln(1/ε)/π) / λ₁(Λ*)`,
- **MR07 Lemma 3.3**: primal `λ_n(Λ)` and max Gram–Schmidt norm smoothing bounds for `0 < ε ≤ 1`,
- **MR07 Lemma 4.1**: total-variation distance `≤ ε / 2` over any fundamental parallelepiped `P(B)`
  for `0 < ε < 1` and `s ≥ η_ε(Λ)`. -/
theorem witness_lattice_smoothing_mr07_full
    {n : ℕ} (hn : 0 < n)
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Module.Basis (Fin n) ℤ L)
    {ε : ℝ} (hε : 0 < ε) :
    (ε ≤ 1 →
      RHDirect.LatticeSmoothing.eta L ε ≤
        Real.sqrt ((n : ℝ) + Real.log (1 / ε) / Real.pi) /
          RHDirect.Stage10GeometryOfNumbers.shortestNorm
            (RHDirect.Stage12BanaszczykTransference.dualLattice L)) ∧
    (ε ≤ 1 →
      RHDirect.LatticeSmoothing.eta L ε ≤
        Real.sqrt ((n : ℝ) + Real.log (1 / ε) / Real.pi) *
          RHDirect.Stage10GeometryOfNumbers.successiveMinimum
            (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
            L ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩) ∧
    (ε ≤ 1 →
      RHDirect.LatticeSmoothing.eta L ε ≤
        Real.sqrt ((n : ℝ) + Real.log (1 / ε) / Real.pi) *
          Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩
            (fun i : Fin n =>
              ‖RHDirect.Stage11LLLSiegelReduction.gramSchmidtVec
                (fun k => (b k : EuclideanSpace ℝ (Fin n))) i‖)) ∧
    (∀ {s : ℝ}, ε < 1 → RHDirect.LatticeSmoothing.eta L ε ≤ s →
      (1 / 2 : ℝ) *
          ∫ x in ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ),
            |RHDirect.LatticeSmoothingFull.foldedGaussianDensity L s x -
              (ZLattice.covolume L MeasureTheory.volume)⁻¹| ∂MeasureTheory.volume ≤
        ε / 2) :=
  ⟨fun hε1 => RHDirect.LatticeSmoothingFull.eta_le_sqrt_n_add_log_div_lambda1 hn hε hε1,
   fun hε1 => RHDirect.LatticeSmoothingFull.eta_le_sqrt_n_add_log_mul_lambdan hn hε hε1,
   fun hε1 => RHDirect.LatticeSmoothingFull.eta_le_sqrt_n_add_log_mul_max_gsNorm hn b hε hε1,
   fun hε1 hs => RHDirect.LatticeSmoothingFull.tv_distance_foldedGaussianDensity_fundamentalDomain
     hn b hε hε1 hs⟩

/-- Witness 10: **Manin's Period-Ratio Theorem for Ramanujan's `Δ`** (including the `691`
critical `L`-value ratio and closed-form period polynomial) on native `CuspForm` (`0` assumptions). -/
theorem witness_manin_delta_period_ratios :
    (48 * RHDirect.Stage9CuspFormLFunc.completedDeltaL 4 =
        25 * RHDirect.Stage9CuspFormLFunc.completedDeltaL 2 ∧
     12 * RHDirect.Stage9CuspFormLFunc.completedDeltaL 6 =
        5 * RHDirect.Stage9CuspFormLFunc.completedDeltaL 2 ∧
     5 * RHDirect.Stage9CuspFormLFunc.completedDeltaL 6 =
        4 * RHDirect.Stage9CuspFormLFunc.completedDeltaL 4) ∧
    (14 * RHDirect.Stage9CuspFormLFunc.completedDeltaL 5 =
        9 * RHDirect.Stage9CuspFormLFunc.completedDeltaL 3 ∧
     691 * RHDirect.Stage9CuspFormLFunc.completedDeltaL 1 =
        1620 * RHDirect.Stage9CuspFormLFunc.completedDeltaL 3 ∧
     691 * RHDirect.Stage9CuspFormLFunc.completedDeltaL 1 =
        2520 * RHDirect.Stage9CuspFormLFunc.completedDeltaL 5) ∧
    (∀ X : ℂ,
      (RHDirect.Stage11ModularSymbols.periodPoly
        RHDirect.Stage8RamanujanDelta.ramanujanDelta).eval X =
        (5 / 2 : ℂ) * RHDirect.Stage9CuspFormLFunc.completedDeltaL 2 *
          (4 * X ^ 9 - 25 * X ^ 7 + 42 * X ^ 5 - 25 * X ^ 3 + 4 * X) +
        Complex.I * (-45 * RHDirect.Stage9CuspFormLFunc.completedDeltaL 3) *
          (-(36 / 691 : ℂ) * (X ^ 10 - 1) + (X ^ 8 - X ^ 2) - 3 * (X ^ 6 - X ^ 4))) :=
  RHDirect.Stage11ModularSymbols.manin_delta_period_ratios

/-- Witness 11: **Lovász LLL-Reduced Basis Existence** on any discrete lattice `L ⊂ E` in a
finite-dimensional real inner product space (`0` extra assumptions). -/
theorem witness_lll_basis_exists
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L]
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ b : Module.Basis (Fin (RHDirect.ArakelovCovolume.rk L)) ℤ L,
      RHDirect.Stage11LLLSiegelReduction.IsLLLReduced b δ :=
  RHDirect.Stage11LLLSiegelReduction.exists_lll_reduced_basis L hδ0 hδ1

/-- Witness 12: **Bochner–Kodaira–Nakano Negative-Weight Vanishing** directly on Mathlib
`ModularForm` and `CuspForm` (`0` extra assumptions). -/
theorem witness_bochner_negative_weight_vanishing :
    (∀ {k : ℤ}, k < 0 →
      ∀ f : ModularForm RHDirect.Stage7EisensteinSeries.SL2ZRange k, f = 0) ∧
    (∀ {k : ℤ}, k < 0 →
      ∀ f : CuspForm RHDirect.Stage7EisensteinSeries.SL2ZRange k, f = 0) :=
  ⟨fun hk f => RHDirect.Stage11HermitianCurvature.modularForm_eq_zero_of_weight_neg hk f,
   fun hk f => RHDirect.Stage11HermitianCurvature.cuspForm_eq_zero_of_weight_neg hk f⟩

/-- Witness 13 (Bonus pinning `Stage11GL2SmoothRep`): **Smooth `GL₂(ℚ_p)` Spherical Hecke
Grounding** directly on native `Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]` (`0` extra assumptions). -/
theorem witness_gl2_smooth_hecke_grounding (p : ℕ) [Fact p.Prime] (a_p : ℂ) (k : ℕ) :
    Module.finrank ℂ (RHDirect.Stage11GL2SmoothRep.fixedSubmodule p
      (RHDirect.Stage11LocalLanglandsGL2.LocalChar.unramChar p
        (RHDirect.Stage11LocalLanglandsGL2.satakeRoots a_p p k).1)
      (RHDirect.Stage11LocalLanglandsGL2.LocalChar.unramChar p
        (RHDirect.Stage11LocalLanglandsGL2.satakeRoots a_p p k).2)
      (RHDirect.Stage11GL2SmoothRep.K0 p)) = 1 ∧
    (∀ g : RHDirect.Stage11GL2SmoothRep.GL2Qp p,
      RHDirect.Stage11GL2SmoothRep.heckeTp p
        (RHDirect.Stage11GL2SmoothRep.eigenformSphericalVecClassical a_p p k).1 g =
        Matrix.trace (RHDirect.Stage11LocalLanglandsGL2.llcGL2 p
          (RHDirect.Stage11LocalLanglandsGL2.satakeGL2OfEigenform a_p p k)).frobMatrix *
          (RHDirect.Stage11GL2SmoothRep.eigenformSphericalVecClassical a_p p k).1 g) :=
  let h := RHDirect.Stage11GL2SmoothRep.satakeGL2OfEigenform_smooth_hecke_grounding (p := p) a_p k
  ⟨h.1, h.2.2.2.1⟩

/-! ## 4. Decidable Consistency Theorems over `unifiedAuditManifest` (Zero `native_decide`) -/

/-- All **33** Stage 11 modules are accounted for with distinct module names. -/
theorem stage11Manifest_count_and_nodup :
    stage11Manifest.length = 33 ∧
    (stage11Manifest.map (·.moduleName)).Nodup := by
  decide

/-- Every entry in `unifiedAuditManifest` has non-empty identifier and target fields. -/
theorem unifiedAuditManifest_nonempty_fields :
    unifiedAuditManifest.all (fun r =>
      !r.moduleName.isEmpty && !r.campaign.isEmpty &&
      !r.mainTheoremOrTarget.isEmpty && !r.rationale.isEmpty) = true := by
  simp [unifiedAuditManifest, stage11Manifest, newCampaignManifest]

/-- Exact Stage 11 tier breakdown: `10` unconditional native Mathlib, `5` conditional explicit
hypothesis reductions, `18` proxy / synthetic models (`10 + 5 + 18 = 33`). -/
theorem stage11Manifest_tier_counts :
    (stage11Manifest.filter (fun r => r.tier == .unconditionalNativeMathlib)).length = 10 ∧
    (stage11Manifest.filter (fun r => r.tier == .conditionalExplicitHyp)).length = 5 ∧
    (stage11Manifest.filter (fun r => r.tier == .proxyOrSyntheticModel)).length = 18 := by
  decide

/-- All newly integrated campaign roots (`GlobalCFT`, `ChenTheorem`, `DworkRat`, `DworkZeta`,
`LatticeSmoothing`) are classified as `unconditionalNativeMathlib`. -/
theorem newCampaignManifest_all_unconditional :
    newCampaignManifest.length = 7 ∧
    newCampaignManifest.all (fun r => r.tier == .unconditionalNativeMathlib) = true := by
  decide

/-- The unified manifest has `40` unique entries (`33` Stage 11 + `7` new Tier-A campaigns),
with `17` unconditional native-Mathlib entries total, and supersedes `Stage11GroundingAudit`'s
incomplete `18`-entry manifest by reclassifying all 10+ over-claimed modules out of
`unconditionalNativeMathlib`. -/
theorem unifiedAuditManifest_consistent :
    unifiedAuditManifest.length = 40 ∧
    (unifiedAuditManifest.map (·.moduleName)).Nodup ∧
    RHDirect.Stage11GroundingAudit.stage11GroundingManifest.length = 18 ∧
    (unifiedAuditManifest.filter (fun r => r.tier == .unconditionalNativeMathlib)).length = 17 ∧
    (["RHDirect.Stage11MoriwakiCovolume",
      "RHDirect.Stage11Sym2AdjointL",
      "RHDirect.Stage11DoublingRallis",
      "RHDirect.Stage11BesselWaveSchur",
      "RHDirect.Stage11RallisMassFiber",
      "RHDirect.Stage11IwasawaMainConj",
      "RHDirect.Stage11StickelbergerRamified",
      "RHDirect.Stage11LocalLanglandsGL2",
      "RHDirect.Stage11ArakelovFaltings",
      "RHDirect.Stage11ThetaSiegelBridge"].all fun m =>
        stage11Manifest.any (fun r =>
          r.moduleName == m && r.tier != .unconditionalNativeMathlib)) = true := by
  decide

/-! ## 5. Kernel Axiom Receipts (`#print axioms`) -/

#print axioms witness_linnik_unconditional
#print axioms witness_bombieri_vinogradov_unconditional
#print axioms witness_chen_theorem_unconditional
#print axioms witness_hilbert_class_field_artin_equiv
#print axioms witness_hilbert_artin_data_unconditional
#print axioms witness_borel_dwork_rationality
#print axioms witness_fredholm_jacobi_identity
#print axioms witness_elliptic_zeta_complex_rationality
#print axioms witness_lattice_smoothing_mr07_full
#print axioms witness_manin_delta_period_ratios
#print axioms witness_lll_basis_exists
#print axioms witness_bochner_negative_weight_vanishing
#print axioms witness_gl2_smooth_hecke_grounding
#print axioms unifiedAuditManifest_consistent

end RHDirect.UnifiedSoundnessAudit

