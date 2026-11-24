# Arithmetica4

A Lean 4 (`v4.33.1`) formalization library of landmark theorems in algebraic, analytic, and p-adic number theory built on targeted Mathlib imports (`0` `sorry`, `0` custom axioms, verified with official Lean `leanchecker`).

> **Mathematical Honesty First:** *Kernel-checked (`0` `sorry`, `leanchecker: PASS`) guarantees logical soundness of each Lean statement, NOT that every statement in a large codebase is unconditional or proxy-free.* See [`docs/SOUNDNESS_AUDIT.md`](docs/SOUNDNESS_AUDIT.md) for a complete, line-cited audit classifying every module into **Tier A (Unconditional Native Mathlib)**, **Tier B (Conditional / Scoped)**, and **Tier C (Legacy Baseline Proxies/Toys)**.

---

## Trustless Entry Point (`Challenge.lean` ↔ `Solution.lean`)

To audit the unconditional headline theorems without reading any proof internals or trusting intermediate definitions:

1. **[`Challenge.lean`](Challenge.lean)** imports **only upstream Mathlib** (`0` `RHDirect`, `0` `PrimeGaps`, `0` `MaynardDock` imports, `0` custom definitions) and states 13 pure-Mathlib landmark theorems:
   - `vinogradov_three_primes` (Vinogradov 1937)
   - `chen_theorem` (Chen 1973, `N = p + P₂`)
   - `linnik_theorem` (Linnik 1944)
   - `unconditional_prime_gap_le_246`, `bounded_prime_gaps_246_unconditional`, `frequently_consecutive_prime_gap_le_246` (Polymath8b, `H = 246`)
   - `maynard_tao_m_tuples` (Maynard–Tao arbitrary `m`-tuples of primes in bounded intervals)
   - `dwork_rationality` (Dwork 1960 / Weil Conjecture I)
   - `gauss_class_number_problem` (Heilbronn–Siegel, `h(ℚ(√(-d))) → ∞`)
   - `hasse_minkowski_general` (General `n`-variable Hasse–Minkowski over `ℚ`)
   - `hilbert_class_field_artin` (Hilbert Class Field & Artin Reciprocity isomorphism)
   - `siegel_l1_lower_bound` (Siegel 1935 `L(1, χ)` lower bound, `0` exceptions)
   - `bochner_negative_weight_vanishing` (Negative-weight vanishing on Mathlib `ModularForm` / `CuspForm`)
2. **[`Solution.lean`](Solution.lean)** discharges all 13 theorems unconditionally (`0` `sorry`, `0` custom axioms).
3. **[`scripts/verify_challenge.lean`](scripts/verify_challenge.lean)** loads `Challenge` and `Solution` in separate environments (`trustLevel := 0`), confirms `Challenge` has zero project imports, checks syntactic `Expr` identity of every theorem type and universe list, and verifies every theorem in `Solution` depends strictly on `{propext, Classical.choice, Quot.sound}`.

---

## Tier A — Unconditional Landmarks on Native Mathlib (`0` Extra Hypotheses, `0` Proxies)

| Landmark Theorem | Root Module(s) | Exact Native-Mathlib Statement |
|---|---|---|
| **Bounded Prime Gaps (`H = 246`, Polymath8b) & Maynard–Tao `m`-Tuples** | `MaynardDock.Capstone246`, `PrimeGaps.Bounded246`, `MaynardDock.BombieriVinogradovAdapter`, `RHDirect.MaynardTaoUnconditional` | `unconditional_prime_gap_le_246`, `bounded_prime_gaps_246_unconditional`, `frequently_consecutive_prime_gap_le_246` (`0` parameters via Axiom Math's [`PrimeGapsLib`](https://github.com/AxiomMath/PrimeGapsLib) + `RHDirect` B–V discharge), plus `maynard_tao_600_unconditional` and `maynard_tao_m_tuples_unconditional` (`∀ m ≥ 1`, arbitrary `m`-tuples in bounded intervals). |
| **Dwork's Rationality Theorem (1960) — Weil Conjecture I** | `RHDirect.DworkTraceFormula`, `RHDirect.DworkWeil1Unconditional` (`6,162` L) | `dwork_rationality_unconditional`: rationality of `Z(V(fs), T) ∈ ℚ[[T]]` for **arbitrary** affine algebraic sets `V(fs) ⊆ 𝔸^n` over **arbitrary** finite fields `GaloisField p r` via Dwork splitting function, trace formula, nuclear Fredholm determinant, and Borel–Dwork. |
| **Vinogradov's Three-Primes Theorem (1937)** | `RHDirect.VinogradovMinorArcBound`, `RHDirect.VinogradovMajorArcEval`, `RHDirect.VinogradovThreePrimes` (`5,080` L) | `vinogradov_three_primes_unconditional : ∃ N₀, ∀ n ≥ N₀, Odd n → ∃ p₁ p₂ p₃, Nat.Prime p₁ ∧ Nat.Prime p₂ ∧ Nat.Prime p₃ ∧ p₁ + p₂ + p₃ = n` (Dirichlet + Vaughan Type I/II minor arcs + uniform Siegel–Walfisz major arcs + singular series). |
| **Dirichlet Class Number Formula & Gauss–Heilbronn–Siegel `h(ℚ(√(-d))) → ∞`** | `RHDirect.GaussClassNumberUnconditional` (`3,929` L) | `dirichlet_classNumber_formula_imagQuad` & `gauss_classNumber_problem_native_unconditional` directly on Mathlib's native **`NumberField.classNumber`** (`Fintype.card (ClassGroup (𝓞 K))`). |
| **Full Arithmetic + Spectral Weil Explicit Formula & Positivity Criterion** | `RHDirect.WeilExplicitPositivity` (`2,924` L) | `weil_explicit_formula` & `weil_positivity_arith_iff_RH : RiemannHypothesis ↔ ∀ f : AdmissibleWeilTest, 0 ≤ (weilArithDist (weilSelfConv f)).re` directly on native `ArithmeticFunction.vonMangoldt` and `riemannZeta` (zero reference to zeros on the arithmetic side). |
| **General `n`-Variable Hasse–Minkowski Theorem over `ℚ`** | `RHDirect.HasseMinkowskiGeneral` (`1,828` L) | `hasse_minkowski_general_V` & `hasse_minkowski_general_Q`: local–global isotropy over `ℝ` and all `ℚ_[p]` for **every** dimension `n : ℕ` and **every** nondegenerate `QuadraticForm ℚ V`. |
| **Local & Global Class Field Theory, Ray Class Fields, & Hilbert Class Field** | `RHDirect.CFT_HilbertClassField`, `RHDirect.CFT_HilbertArtinBridge` (`16` modules, `57,874` L) | `localReciprocity`, `reciprocityMapEquiv`, `normGroupOrderIso`, `hilbertClassFieldArtinEquiv : ClassGroup (𝓞 K) ≃* Gal(H_K/K)`, and 0-parameter `hilbertArtinData_unconditional`. *(Extracted and consolidated from Levent Alpöge's public `GroundTheory` formalization; see [`NOTICE`](NOTICE).)* |
| **Chen's Theorem (`N = p + P₂`)** | `RHDirect.ChenTheorem` (`7` modules, `14,630` L) | `chen_theorem : ∃ N₀, ∀ n ≥ N₀, Even n → ∃ p q, Nat.Prime p ∧ IsP2 q ∧ p + q = n` via Rosser–Iwaniec linear sieve + bilinear Bombieri–Vinogradov. |
| **Linnik's Theorem (1944) & Bombieri–Vinogradov (`ϑ = 1/2`)** | `RHDirect.Stage11LinnikUnconditional`, `RHDirect.Stage11BombieriVinogradov` | `linnik_least_prime_in_ap_unconditional` & `bombieri_vinogradov` on native `DirichletCharacter.LFunction`, `vonMangoldt`, `Nat.Prime`, `Nat.ModEq`. |
| **Full Micciancio–Regev (2007) Lattice Smoothing** | `RHDirect.LatticeSmoothingFull` (`650` L) | MR07 Lemmas 3.2 (full `0 < ε ≤ 1` dual bound), 3.3 (primal `λ_n` & Gram–Schmidt bounds), and 4.1 (TV distance `≤ ε / 2` to uniform on `ℝ^n / Λ`) on native `IsZLattice`. |
| **Borel–Dwork Rationality & Jacobi–Fredholm Determinant Identity** | `RHDirect.DworkRatMain`, `RHDirect.DworkRatFredholmComplete` | `borel_dwork_rationality`, Jacobi's `derivative_det`, and `exp(∑ Tr(A^m) T^m / m) * det(1 - T A) = 1` over any char-0 field `K` + descent to `ℚ`. |
| **Additional Native Baseline Results** | `RHDirect.Stage5–Stage11` | Effective PNT, uniform Siegel–Walfisz, Siegel's `L(1, χ) ≥ C(ε) q^{-ε}`, Li's 1997 criterion, Manin's `Δ` period ratios (`691 Λ(Δ,1) = 1620 Λ(Δ,3) = 2520 Λ(Δ,5)`), Bochner negative-weight vanishing on native `ModularForm`/`CuspForm`, textbook LLL & Minkowski's 2nd Theorem, and smooth principal-series/Steinberg reps on `GL (Fin 2) ℚ_[p]`. |

---

## Scoped & Conditional Results (Explicitly Bounded Scope)

- **`RHDirect.ArtinDedekindGenuine`** (`1,791` L): Genuine `Ideal.arithFrobAt` Artin `L`-functions linked directly to `Stage7DedekindZeta.dedekindZeta` (incl. `ℚ(∛2)` `S₃` factorization for all `p ≠ 2, 3`); scoped to unramified Euler factors on `Re(s) > 1`.
- **`RHDirect.GL2SmoothLLCUnconditional`** (`1,937` L): Genuine non-supercuspidal `GL₂(ℚ_p)` admissibility (`SmoothInd`, `SmoothSteinberg`) + Local CFT pullback to `W_{ℚ_p}^{ab} ≤ Gal(ℚ_p^{ab}/ℚ_p)` + `heckeTp`/`steinbergHeckeUp` & `LinearMap.det` on `V^{I, N=0}`. **Does not cover supercuspidal representations, non-abelian `W_{ℚ_p}`, or local `ε`-factors.**
- **`RHDirect.DworkZetaPolyElliptic`** (`279` L): Exact `PowerSeries ℚ` rationality for arbitrary complex Frobenius eigenvalues `α, β ∈ ℂ` (`N_m = q^m + 1 - (α^m + β^m)`) and genus-`g` matrix Frobenius (`q^m + 1 - Tr(F^m)`).
- **`RHDirect.MaynardTaoReduction` & `RHDirect.MaynardTaoUnconditional`**: `MaynardTaoReduction` defines the admissible 50-tuple / W-trick framework; `RHDirect.MaynardTaoSieve` + `RHDirect.MaynardTaoUnconditional` unconditionally discharge `AnalyticCore` (`H ≤ 600`) and `MAnalyticCore` (`maynard_tao_m_tuples_unconditional`), while `MaynardDock.Capstone246` achieves the sharper `H = 246` Polymath8b bound.
- **`RHDirect.Main`**: Top-level RH/GRH architecture is **100% conditional** on open arithmetic-geometry / patching hypotheses (Pillars 2–4).
- **`RHDirect.UnifiedSoundnessAudit`** (`601` L): 13 kernel-pinned 0-assumption native witnesses + honest 40-entry classification manifest.

---

## Build & Verify Locally

- **Toolchain:** `leanprover/lean4:v4.33.1`
- **Mathlib pin:** `0df444a360eaa60ab8c11dca51a86af692955474`
- **Zero-Cheat Gate:** `0` `sorry` (outside `Challenge.lean` specifications), `0` `admit`, `0` custom `axiom`, `0` `opaque`, `0` `native_decide`, `0` `import Mathlib`. Every headline theorem depends strictly on `[propext, Classical.choice, Quot.sound]` and passes official Lean `leanchecker`.

```bash
git clone https://github.com/nil-commits/Arithmetica4.git
cd Arithmetica4
lake exe cache get

# Build and verify the trustless Challenge <-> Solution entry point + H = 246:
lake build Challenge Solution MaynardDock.Capstone246 MaynardDock.Audit
lake env lean --run scripts/verify_challenge.lean
lake env leanchecker --fresh Solution
lake env leanchecker --fresh MaynardDock.Capstone246

# Build individual RHDirect landmarks:
lake build RHDirect.DworkWeil1Unconditional
lake build RHDirect.VinogradovThreePrimes
lake build RHDirect.GaussClassNumberUnconditional
lake build RHDirect.WeilExplicitPositivity
lake build RHDirect.HasseMinkowskiGeneral
lake build RHDirect.CFT_HilbertClassField
lake build RHDirect.ChenTheorem

# Or run the local 3-gate verification harness (cheat scan + leanchecker + exhaustive axiom audit):
python3 scripts/verify_harness.py RHDirect/DworkWeil1Unconditional.lean RHDirect/VinogradovThreePrimes.lean
```

## License & Attribution

Released under the Apache License 2.0 (see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE)).
- `PrimeGaps/`, `PrimeGapsTheory/`, and `PrimeGapsCert/` are vendored unmodified from [`AxiomMath/PrimeGapsLib`](https://github.com/AxiomMath/PrimeGapsLib) (Copyright 2026 Axiom Math, Apache-2.0).
- `PrimeNumberTheoremAnd` uses [`nil-commits/PrimeNumberTheoremAnd`](https://github.com/nil-commits/PrimeNumberTheoremAnd) (`6c89d569`), a public fork of `AxiomMath/PrimeNumberTheoremAnd` with a 1-line Lean `v4.33.1` fix in `MediumPNT.lean`.
