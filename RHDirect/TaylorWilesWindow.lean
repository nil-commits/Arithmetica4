import RHDirect.Interfaces
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Support
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.Exponential

/-!
# RHDirect.TaylorWilesWindow

Compact, direct, zero-`sorry`, zero-`axiom` rebuild of the **Abstract Taylor–Wiles Patching
Algebra & Selmer/Vandiver Window (`VWinAt ψ 401`) Rank-Bound Core** against `RHDirect.Interfaces`
and Mathlib `v4.33.1`, completely stripped of `OpenImageCondition`, `LiteratureCMHypothesis`,
and Gen 1–5 vestigial wrappers.

## Contents

1. **Abstract Taylor–Wiles Patching Algebra & Fitting/Length Inequalities**
   - Base-change freeness & finiteness of patched modules (`patched_tensor_free_finite`,
     distilling `PatchedModuleFreeFiniteOverIwasawaAlgebra.lean`).
   - Faithfulness of nontrivial free patched modules (`annihilator_eq_bot_of_free_nontrivial`)
     and the abstract `R_∞ = T_∞` patching isomorphism (`patched_R_eq_T_of_free`).
   - Fitting-determinant annihilation via Cramer's adjugate identity
     (`det_mem_annihilator_coker`) and presentation length bounds
     (`length_le_rank_mul_quotient_of_surjective`, `length_coker_le_rank_mul_det`).
   - Multiplicative principal-ideal length subadditivity (`length_quotient_span_mul_le`,
     `length_quotient_span_pow_le`) and DVR/uniformizer obstruction length bounds
     (`length_le_of_pow_mem_annihilator`, `patched_finite_level_length_bound`,
     `patched_selmer_obstruction_bound`).

2. **Three-Part `VVle` Patching Decomposition & Prime-Sum Aggregation**
   - `VVle.of_uniform_prime_bound`: lifts finite-support patched length bounds directly to `VVle`.
   - `VVle.of_three_parts`: combines `l = 2` (Iwasawa 2-tower), odd ramified primes (`l ∣ M`),
     and odd unramified/patching primes (`l ∤ 2 * M`) into `VVle S E t (B₂ + B_ram + B_patch)`.

3. **Quantitative `WinPair` / `PageN` Estimates & Direct `VWinAt` / `VWin` Window Assembly**
   - `admissible_of_pageN`, `log_mul_le_rpow_of_winPair`, `eventually_winPair_gt_power`,
     `log_conductor_mul_height_le_of_pageN`, `minusBound_le_exp_of_log_le`,
     `error_terms_le_sqrt_exp_rpow`.
   - `vwinAt_of_joint_patching`, `vwin_of_joint_patching`, and
     `galoisModularityContract_of_patching` (assembling `VWinAt S ψ 401`, `VWin S`, and
     `GaloisModularityContract S` directly with zero dead fields!).

4. **The `401 = 400 + 1` Window Scaling & Rank-Bound Bridge**
   - `eventually_rank_le_rpow_400_of_lt_one_div_52`: proves `(R.t : ℝ) ≤ s.x ^ (400 : ℝ)`
     for `ScaleParams` + `ChainRanks` + `RankVal` (matching `EventuallyRankLeRpowOfLtOneDivFiftytwo.lean`).
   - `winPairs_of_vwinAt_401`: shifts `VWinAt S ψ 401` by `k = c ^ (1 / (2 + 8 ε))` via
     `401 = 400 + 1` and `VVle.mono` into a full `[Z, Z ^ (3 / 2)]` window of `WinDatum`
     with cutoff `⌊x ^ 400⌋₊` (matching `WinPairs.lean`).
-/

noncomputable section

open scoped BigOperators TensorProduct
open Real Finset Filter RHDirect

namespace RHDirect.TaylorWilesWindow

/-! ## Section 1: Abstract Taylor–Wiles Patching Algebra & Fitting/Length Inequalities -/

/-- Base-change freeness and finiteness for a patched module `X ≃+ S ⊗[B] M` over an Iwasawa
algebra `Λ`, distilling `PatchedModuleFreeFiniteOverIwasawaAlgebra.lean` (`tens_free`). -/
theorem patched_tensor_free_finite
    {Λ B S M X : Type*} [CommRing Λ] [CommRing B] [CommRing S] [Algebra B S]
    [AddCommGroup M] [Module B M] [Module Λ M]
    [Module.Free B S] [Module.Finite B S]
    [Module.Free Λ M] [Module.Finite Λ M]
    [AddCommGroup X] [Module Λ X]
    (lam : Λ → B) (hl : ∀ (a : Λ) (m : M), a • m = lam a • m)
    (e : X ≃+ S ⊗[B] M)
    (he : ∀ (a : Λ) (x : X), e (a • x) = algebraMap B S (lam a) • e x) :
    Module.Free Λ X ∧ Module.Finite Λ X := by
  classical
  let φ : S ⊗[B] M ≃ₗ[B] (Module.Free.ChooseBasisIndex B S →₀ M) :=
    (TensorProduct.congr (Module.Free.chooseBasis B S).repr (LinearEquiv.refl B M)).trans
      (TensorProduct.finsuppScalarLeft B M _)
  have key : ∀ (a : Λ) (x : X), φ (e (a • x)) = a • φ (e x) := by
    intro a x
    rw [he, algebraMap_smul, map_smul]
    ext i
    simp only [Finsupp.smul_apply, hl]
  let ψ : X ≃ₗ[Λ] (Module.Free.ChooseBasisIndex B S →₀ M) :=
    { toFun := fun x => φ (e x)
      invFun := fun f => e.symm (φ.symm f)
      map_add' := fun x y => by simp
      map_smul' := key
      left_inv := fun x => by simp
      right_inv := fun f => by simp }
  exact ⟨Module.Free.of_equiv ψ.symm, Module.Finite.equiv ψ.symm⟩

/-- Surjective `R`-linear maps can only enlarge the annihilator ideal. -/
theorem annihilator_le_of_surjective {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {f : M →ₗ[R] N} (hf : Function.Surjective f) :
    Module.annihilator R M ≤ Module.annihilator R N := by
  intro r hr
  rw [Module.mem_annihilator] at hr ⊢
  intro n
  obtain ⟨m, rfl⟩ := hf n
  rw [← map_smul, hr m, map_zero]

/-- Pullback of annihilators along a scalar restriction `φ : R →+* S`: an element of `R` kills `M`
iff its image in `S` kills `M`. -/
theorem annihilator_comap_eq {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] :
    Module.annihilator R M = (Module.annihilator S M).comap (algebraMap R S) := by
  ext r
  simp only [Ideal.mem_comap, Module.mem_annihilator, algebraMap_smul]

/-- A nontrivial free `R`-module is faithful: its annihilator ideal is `⊥`. -/
theorem annihilator_eq_bot_of_free_nontrivial {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Nontrivial M] :
    Module.annihilator R M = ⊥ := by
  rw [eq_bot_iff]
  intro r hr
  rw [Ideal.mem_bot]
  let b := Module.Free.chooseBasis R M
  have hne : Nonempty (Module.Free.ChooseBasisIndex R M) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have hsub : Subsingleton M := by
      refine ⟨fun x y => b.repr.injective ?_⟩
      ext i
      exact h.elim i
    exact not_subsingleton M hsub
  obtain ⟨i⟩ := hne
  have h0 : r • b i = 0 := Module.mem_annihilator.mp hr (b i)
  have h1 : b.repr (r • b i) i = 0 := by rw [h0, map_zero, Finsupp.zero_apply]
  simpa [map_smul, Module.Basis.repr_self] using h1

/-- **Abstract `R_∞ = T_∞` Taylor–Wiles Patching Theorem**: if a ring homomorphism
`φ : R_∞ →+* T` is surjective (the deformation-to-Hecke surjection) and there exists a nontrivial
`T`-module `M_∞` that is free over `R_∞` via `φ`, then `φ` is bijective (giving `R_∞ ≃+* T`). -/
theorem patched_R_eq_T_of_free {R T M : Type*} [CommRing R] [CommRing T] [Algebra R T]
    [AddCommGroup M] [Module R M] [Module T M] [IsScalarTower R T M]
    [Module.Free R M] [Nontrivial M] (hsurj : Function.Surjective (algebraMap R T)) :
    Function.Bijective (algebraMap R T) := by
  refine ⟨?_, hsurj⟩
  rw [injective_iff_map_eq_zero]
  intro r hr
  have hann : r ∈ Module.annihilator R M := by
    rw [Module.mem_annihilator]
    intro m
    rw [← algebraMap_smul T r m, hr, zero_smul]
  rw [annihilator_eq_bot_of_free_nontrivial] at hann
  exact Ideal.mem_bot.mp hann

/-- **Fitting-Determinant Annihilation (Cramer/Cayley–Hamilton)**: for any square presentation
`A : Matrix (Fin r) (Fin r) R`, `A.det` lies in the annihilator of `coker(A) = R^r / im(A)`. -/
theorem det_mem_annihilator_coker {R : Type*} [CommRing R] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) R) :
    A.det ∈ Module.annihilator R ((Fin r → R) ⧸ LinearMap.range A.mulVecLin) := by
  rw [Module.mem_annihilator]
  intro q
  induction q using Quotient.inductionOn' with
  | h v =>
    change Submodule.Quotient.mk (A.det • v) = 0
    rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
    refine ⟨A.adjugate.mulVec v, ?_⟩
    change A.mulVec (A.adjugate.mulVec v) = A.det • v
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- Surjective factorization through the quotient by any ideal inside `ann(M)`:
if `R^r ↠ M` and `I ≤ Module.annihilator R M`, then `(R ⧸ I)^r ↠ M`. -/
theorem exists_surjective_from_pi_quotient {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {r : ℕ} {I : Ideal R}
    (f : (Fin r → R) →ₗ[R] M) (hf : Function.Surjective f) (hI : I ≤ Module.annihilator R M) :
    ∃ g : (Fin r → R ⧸ I) →ₗ[R] M, Function.Surjective g := by
  let e : Fin r → M := fun i => f (Pi.single i 1)
  let mkElem : Fin r → (R ⧸ I) →ₗ[R] M := fun i =>
    I.liftQ (LinearMap.toSpanSingleton R M (e i)) (by
      intro a ha
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      exact Module.mem_annihilator.mp (hI ha) (e i))
  let g : (Fin r → R ⧸ I) →ₗ[R] M :=
    ∑ i : Fin r, (mkElem i).comp (LinearMap.proj i)
  refine ⟨g, fun m => ?_⟩
  obtain ⟨v, rfl⟩ := hf m
  refine ⟨fun i => Ideal.Quotient.mk I (v i), ?_⟩
  have hv : v = ∑ i : Fin r, v i • Pi.single i (1 : R) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  calc g (fun i => Ideal.Quotient.mk I (v i))
      = ∑ i : Fin r, v i • e i := by
          simp only [g, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
            mkElem]
          refine Finset.sum_congr rfl fun i _ => ?_
          change Submodule.liftQ I (LinearMap.toSpanSingleton R M (e i)) _
            (Submodule.Quotient.mk (v i)) = v i • e i
          rw [Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply]
    _ = f (∑ i : Fin r, v i • Pi.single i (1 : R)) := by
          simp only [map_sum, map_smul, e]
    _ = f v := by rw [← hv]

/-- **Presentation Length Inequality**: if `M` is generated by `r` elements over `R` and killed
by an ideal `I ≤ Module.annihilator R M`, then `length_R(M) ≤ r * length_R(R ⧸ I)`. -/
theorem length_le_rank_mul_quotient_of_surjective {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {r : ℕ} {I : Ideal R}
    (f : (Fin r → R) →ₗ[R] M) (hf : Function.Surjective f) (hI : I ≤ Module.annihilator R M) :
    Module.length R M ≤ (r : ℕ∞) * Module.length R (R ⧸ I) := by
  obtain ⟨g, hg⟩ := exists_surjective_from_pi_quotient f hf hI
  calc Module.length R M
      ≤ Module.length R (Fin r → R ⧸ I) := Module.length_le_of_surjective g hg
    _ = ENat.card (Fin r) * Module.length R (R ⧸ I) := Module.length_pi
    _ = (r : ℕ∞) * Module.length R (R ⧸ I) := by simp

/-- **Fitting-Ideal / Determinant Patching Length Inequality**: for any square presentation
`A : Matrix (Fin r) (Fin r) R`, the length of `coker(A)` is bounded by `r` times the length of
`R ⧸ (det A)`. -/
theorem length_coker_le_rank_mul_det {R : Type*} [CommRing R] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) R) :
    Module.length R ((Fin r → R) ⧸ LinearMap.range A.mulVecLin) ≤
      (r : ℕ∞) * Module.length R (R ⧸ Ideal.span ({A.det} : Set R)) := by
  refine length_le_rank_mul_quotient_of_surjective
    (LinearMap.range A.mulVecLin).mkQ (Submodule.mkQ_surjective _) ?_
  rw [Ideal.span_singleton_le_iff_mem]
  exact det_mem_annihilator_coker A

/-- **Principal-Ideal Multiplicative Length Subadditivity**:
`length_R(R ⧸ (a * b)) ≤ length_R(R ⧸ (a)) + length_R(R ⧸ (b))`. -/
theorem length_quotient_span_mul_le {R : Type*} [CommRing R] (a b : R) :
    Module.length R (R ⧸ Ideal.span ({a * b} : Set R)) ≤
      Module.length R (R ⧸ Ideal.span ({a} : Set R)) +
        Module.length R (R ⧸ Ideal.span ({b} : Set R)) := by
  let Iab : Ideal R := Ideal.span ({a * b} : Set R)
  let Ia : Ideal R := Ideal.span ({a} : Set R)
  let Ib : Ideal R := Ideal.span ({b} : Set R)
  have hle : Iab ≤ Ia := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mul_mem_right b Ia (Ideal.subset_span rfl)
  let qMap : (R ⧸ Iab) →ₗ[R] (R ⧸ Ia) :=
    Submodule.factor hle
  have hqSurj : Function.Surjective qMap := Submodule.factor_surjective hle
  have hadd : Module.length R (R ⧸ Iab) =
      Module.length R (LinearMap.ker qMap) + Module.length R (R ⧸ Ia) :=
    Module.length_eq_add_of_exact (LinearMap.ker qMap).subtype qMap
      (Submodule.subtype_injective _) hqSurj (LinearMap.exact_subtype_ker_map qMap)
  let mulA : R →ₗ[R] (LinearMap.ker qMap) :=
    { toFun := fun x =>
        ⟨Ideal.Quotient.mk Iab (a * x), by
          change Ideal.Quotient.mk Ia (a * x) = 0
          rw [Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.mul_mem_right x Ia (Ideal.subset_span rfl)⟩
      map_add' := fun x y => by
        apply Subtype.ext
        change Ideal.Quotient.mk Iab (a * (x + y)) =
          Ideal.Quotient.mk Iab (a * x) + Ideal.Quotient.mk Iab (a * y)
        rw [mul_add, map_add]
      map_smul' := fun r x => by
        apply Subtype.ext
        change Ideal.Quotient.mk Iab (a * (r * x)) = r • Ideal.Quotient.mk Iab (a * x)
        rw [← mul_assoc, mul_comm a r, mul_assoc]
        exact map_smul (Ideal.Quotient.mkₐ R Iab).toLinearMap r (a * x) }
  let liftMulA : (R ⧸ Ib) →ₗ[R] (LinearMap.ker qMap) :=
    Ib.liftQ mulA (by
      intro x hx
      rw [LinearMap.mem_ker]
      rw [Ideal.mem_span_singleton] at hx
      obtain ⟨c, rfl⟩ := hx
      apply Subtype.ext
      change Ideal.Quotient.mk Iab (a * (b * c)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, ← mul_assoc]
      exact Ideal.mul_mem_right c Iab (Ideal.subset_span rfl))
  have hSurjK : Function.Surjective liftMulA := by
    rintro ⟨y, hy⟩
    induction y using Quotient.inductionOn' with
    | h r =>
      have hr : r ∈ Ia := by
        have h0 : Ideal.Quotient.mk Ia r = 0 := hy
        exact Ideal.Quotient.eq_zero_iff_mem.mp h0
      rw [Ideal.mem_span_singleton] at hr
      obtain ⟨x, rfl⟩ := hr
      exact ⟨Ideal.Quotient.mk Ib x, rfl⟩
  have hKle : Module.length R (LinearMap.ker qMap) ≤ Module.length R (R ⧸ Ib) :=
    Module.length_le_of_surjective liftMulA hSurjK
  rw [hadd, add_comm]
  exact add_le_add_right hKle _

/-- Power length bound for principal ideals:
`length_R(R ⧸ (a ^ k)) ≤ k * length_R(R ⧸ (a))`. -/
theorem length_quotient_span_pow_le {R : Type*} [CommRing R] (a : R) :
    ∀ k : ℕ, Module.length R (R ⧸ Ideal.span ({a ^ k} : Set R)) ≤
      (k : ℕ∞) * Module.length R (R ⧸ Ideal.span ({a} : Set R))
  | 0 => by
      have htop : Ideal.span ({a ^ 0} : Set R) = ⊤ := by
        rw [pow_zero, Ideal.span_singleton_one]
      have hsub : Subsingleton (R ⧸ Ideal.span ({a ^ 0} : Set R)) := by
        rw [htop]
        infer_instance
      simp [Module.length_eq_zero]
  | k + 1 => by
      rw [pow_succ]
      calc Module.length R (R ⧸ Ideal.span ({a ^ k * a} : Set R))
          ≤ Module.length R (R ⧸ Ideal.span ({a ^ k} : Set R)) +
              Module.length R (R ⧸ Ideal.span ({a} : Set R)) :=
            length_quotient_span_mul_le (a ^ k) a
        _ ≤ (k : ℕ∞) * Module.length R (R ⧸ Ideal.span ({a} : Set R)) +
              Module.length R (R ⧸ Ideal.span ({a} : Set R)) :=
            add_le_add_left (length_quotient_span_pow_le a k) _
        _ = ((k + 1 : ℕ) : ℕ∞) * Module.length R (R ⧸ Ideal.span ({a} : Set R)) := by
            push_cast
            rw [add_mul, one_mul]

/-- **DVR / Uniformizer Presentation Length Bound**: if `ϖ ∈ R` has simple residue module
`R ⧸ (ϖ)` (length `1`), `M` is generated by `r` elements, and `ϖ ^ k ∈ ann_R(M)`, then
`length_R(M) ≤ r * k`. -/
theorem length_le_of_pow_mem_annihilator {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {r k : ℕ} {ϖ : R}
    [IsSimpleModule R (R ⧸ Ideal.span ({ϖ} : Set R))]
    (f : (Fin r → R) →ₗ[R] M) (hf : Function.Surjective f)
    (hk : ϖ ^ k ∈ Module.annihilator R M) :
    Module.length R M ≤ ((r * k : ℕ) : ℕ∞) := by
  have h1 : Module.length R M ≤ (r : ℕ∞) * Module.length R (R ⧸ Ideal.span ({ϖ ^ k} : Set R)) := by
    refine length_le_rank_mul_quotient_of_surjective f hf ?_
    rwa [Ideal.span_singleton_le_iff_mem]
  have h2 : Module.length R (R ⧸ Ideal.span ({ϖ ^ k} : Set R)) ≤ (k : ℕ∞) := by
    have hp := length_quotient_span_pow_le ϖ k
    rw [Module.length_eq_one (R := R) (M := R ⧸ Ideal.span ({ϖ} : Set R)), mul_one] at hp
    exact hp
  calc Module.length R M
      ≤ (r : ℕ∞) * Module.length R (R ⧸ Ideal.span ({ϖ ^ k} : Set R)) := h1
    _ ≤ (r : ℕ∞) * (k : ℕ∞) := mul_le_mul_right h2 (r : ℕ∞)
    _ = ((r * k : ℕ) : ℕ∞) := by push_cast; rfl

/-- **Abstract Taylor–Wiles Patched Module Data**: packages a patched module `M_∞` over `R_∞`,
its specialization surjection `π : M_∞ ↠ M_0` to a finite-level module `M_0`, generator bound `d`
over `R_∞`, and congruence/obstruction ideal `I` annihilating `M_0`. -/
structure PatchedModuleBoundData.{u, v} (R_inf : Type u) [CommRing R_inf] where
  M_inf : Type v
  [addInf : AddCommGroup M_inf]
  [modInf : Module R_inf M_inf]
  M_0 : Type v
  [add0 : AddCommGroup M_0]
  [mod0 : Module R_inf M_0]
  genRank : ℕ
  genMap : (Fin genRank → R_inf) →ₗ[R_inf] M_inf
  gen_surj : Function.Surjective genMap
  spec : M_inf →ₗ[R_inf] M_0
  spec_surj : Function.Surjective spec
  obsIdeal : Ideal R_inf
  obs_kills : obsIdeal ≤ Module.annihilator R_inf M_0

attribute [instance] PatchedModuleBoundData.addInf PatchedModuleBoundData.modInf
  PatchedModuleBoundData.add0 PatchedModuleBoundData.mod0

/-- **Finite-Level Patching Length Inequality**: a patched module `M_∞` of generator rank `d`
specializing onto `M_0` with obstruction ideal `I ≤ ann(M_0)` forces
`length(M_0) ≤ d * length(R_∞ ⧸ I)`. -/
theorem patched_finite_level_length_bound {R_inf : Type*} [CommRing R_inf]
    (D : PatchedModuleBoundData R_inf) :
    Module.length R_inf D.M_0 ≤
      (D.genRank : ℕ∞) * Module.length R_inf (R_inf ⧸ D.obsIdeal) :=
  length_le_rank_mul_quotient_of_surjective (D.spec.comp D.genMap)
    (D.spec_surj.comp D.gen_surj) D.obs_kills

/-- **Patched Selmer/Cohomology Obstruction Bound**: if a Selmer module `Sel` injects into (or
embeds as a submodule of) a finite-level patched specialization `M_0`, then `length(Sel)` is
uniformly bounded by `D.genRank * length(R_∞ ⧸ D.obsIdeal)`; in particular if `R_∞ ⧸ I` has finite
length `L`, then `length(Sel) ≠ ⊤` and `(length(Sel)).toNat ≤ D.genRank * L`. -/
theorem patched_selmer_obstruction_bound {R_inf Sel : Type*} [CommRing R_inf]
    [AddCommGroup Sel] [Module R_inf Sel]
    (D : PatchedModuleBoundData R_inf)
    (ι : Sel →ₗ[R_inf] D.M_0) (hι : Function.Injective ι)
    {L : ℕ} (hL : Module.length R_inf (R_inf ⧸ D.obsIdeal) ≤ (L : ℕ∞)) :
    Module.length R_inf Sel ≠ ⊤ ∧ (Module.length R_inf Sel).toNat ≤ D.genRank * L := by
  have hle : Module.length R_inf Sel ≤ ((D.genRank * L : ℕ) : ℕ∞) := by
    calc Module.length R_inf Sel
        ≤ Module.length R_inf D.M_0 := Module.length_le_of_injective ι hι
      _ ≤ (D.genRank : ℕ∞) * Module.length R_inf (R_inf ⧸ D.obsIdeal) :=
          patched_finite_level_length_bound D
      _ ≤ (D.genRank : ℕ∞) * (L : ℕ∞) := mul_le_mul_right hL (D.genRank : ℕ∞)
      _ = ((D.genRank * L : ℕ) : ℕ∞) := by push_cast; rfl
  refine ⟨ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle, ?_⟩
  exact ENat.toNat_le_of_le_natCast hle

/-! ## Section 2: Three-Part `VVle` Decomposition & Patching Prime-Sum Aggregation -/

/-- Prime-by-prime finite length bounds supported on a finite prime set `P₀` directly yield
`VVle S E t` with the weighted log-sum bound. -/
theorem vvle_of_uniform_prime_bound {S : SelmerSystem} {E : Type} [Field E] [NumberField E]
    {t : ℕ} (P₀ : Finset Nat.Primes) (L : Nat.Primes → ℕ → ℕ)
    (hfin : ∀ (l : Nat.Primes) (e : ℕ), 0 < e → e < t → S.shaLen E l e ≠ ⊤)
    (hsupp : ∀ (l : Nat.Primes) (e : ℕ), 0 < e → e < t → l ∉ P₀ → S.shaLen E l e = 0)
    (hbd : ∀ l ∈ P₀, ∀ e : ℕ, 0 < e → e < t → (S.shaLen E l e).toNat ≤ L l e) :
    VVle S E t (∑ l ∈ P₀, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, (L l e : ℝ)) := by
  refine ⟨hfin, fun P => ?_⟩
  have hterm_nonneg : ∀ l : Nat.Primes,
      0 ≤ Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, (L l e : ℝ) := by
    intro l
    exact mul_nonneg (Real.log_natCast_nonneg _) (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
  have hzero : ∀ l ∈ P, l ∉ P₀ →
      Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((S.shaLen E l e).toNat : ℝ) = 0 := by
    intro l _ hl
    have hsum0 : ∑ e ∈ Finset.Ico 1 t, ((S.shaLen E l e).toNat : ℝ) = 0 := by
      refine Finset.sum_eq_zero fun e he => ?_
      simp only [Finset.mem_Ico] at he
      rw [hsupp l e (by omega) he.2 hl]
      simp
    rw [hsum0, mul_zero]
  calc ∑ l ∈ P, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((S.shaLen E l e).toNat : ℝ)
      = ∑ l ∈ P ∩ P₀, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((S.shaLen E l e).toNat : ℝ) := by
        symm
        refine Finset.sum_subset Finset.inter_subset_left fun l hl hnot => ?_
        exact hzero l hl (fun h0 => hnot (Finset.mem_inter.mpr ⟨hl, h0⟩))
    _ ≤ ∑ l ∈ P ∩ P₀, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, (L l e : ℝ) := by
        refine Finset.sum_le_sum fun l hl => ?_
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun e he => ?_)
          (Real.log_natCast_nonneg _)
        simp only [Finset.mem_Ico] at he
        exact_mod_cast hbd l (Finset.mem_inter.mp hl).2 e (by omega) he.2
    _ ≤ ∑ l ∈ P₀, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, (L l e : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right fun l _ _ => hterm_nonneg l

/-- **Three-Part `VVle` Patching Split** (clean, dead-field-free analogue of `vvle_of_parts` in
`AdmissibleOfPageN.lean`): splits the Selmer prime sum into:
1. the `l = 2` Iwasawa 2-tower contribution (`B₂`),
2. odd primes dividing the character conductor `M` (`B_ram`),
3. odd unramified/patching primes `l ∤ 2 * M` (`B_patch`). -/
theorem vvle_of_three_parts {S : SelmerSystem} {E : Type} [Field E] [NumberField E]
    {t M : ℕ} {B₂ B_ram B_patch : ℝ}
    (h2_fin : ∀ (l : Nat.Primes) (e : ℕ), (l : ℕ) = 2 → 0 < e → e < t → S.shaLen E l e ≠ ⊤)
    (h2_sum : ∀ P : Finset Nat.Primes, (∀ l ∈ P, (l : ℕ) = 2) →
      ∑ l ∈ P, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((S.shaLen E l e).toNat : ℝ) ≤ B₂)
    (hram_fin : ∀ (l : Nat.Primes) (e : ℕ), (l : ℕ) ≠ 2 → (l : ℕ) ∣ M → 0 < e → e < t →
      S.shaLen E l e ≠ ⊤)
    (hram_sum : ∀ P : Finset Nat.Primes, (∀ l ∈ P, (l : ℕ) ≠ 2 ∧ (l : ℕ) ∣ M) →
      ∑ l ∈ P, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((S.shaLen E l e).toNat : ℝ) ≤ B_ram)
    (hpat_fin : ∀ (l : Nat.Primes) (e : ℕ), (l : ℕ) ≠ 2 → ¬((l : ℕ) ∣ M) → 0 < e → e < t →
      S.shaLen E l e ≠ ⊤)
    (hpat_sum : ∀ P : Finset Nat.Primes, (∀ l ∈ P, (l : ℕ) ≠ 2 ∧ ¬((l : ℕ) ∣ M)) →
      ∑ l ∈ P, Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((S.shaLen E l e).toNat : ℝ) ≤ B_patch) :
    VVle S E t (B₂ + B_ram + B_patch) := by
  classical
  refine ⟨fun l e he1 he2 => ?_, fun P => ?_⟩
  · by_cases h2 : (l : ℕ) = 2
    · exact h2_fin l e h2 he1 he2
    · by_cases hd : (l : ℕ) ∣ M
      · exact hram_fin l e h2 hd he1 he2
      · exact hpat_fin l e h2 hd he1 he2
  · let f : Nat.Primes → ℝ := fun l =>
      Real.log (l : ℕ) * ∑ e ∈ Finset.Ico 1 t, ((S.shaLen E l e).toNat : ℝ)
    let P₂ := P.filter (fun l : Nat.Primes => (l : ℕ) = 2)
    let P_odd := P.filter (fun l : Nat.Primes => (l : ℕ) ≠ 2)
    let P_ram := P_odd.filter (fun l : Nat.Primes => (l : ℕ) ∣ M)
    let P_pat := P_odd.filter (fun l : Nat.Primes => ¬((l : ℕ) ∣ M))
    have hsplit1 : ∑ l ∈ P, f l = (∑ l ∈ P₂, f l) + ∑ l ∈ P_odd, f l := by
      simpa [P₂, P_odd] using (Finset.sum_filter_add_sum_filter_not P (fun l : Nat.Primes => (l : ℕ) = 2) f).symm
    have hsplit2 : ∑ l ∈ P_odd, f l = (∑ l ∈ P_ram, f l) + ∑ l ∈ P_pat, f l := by
      simpa [P_ram, P_pat] using (Finset.sum_filter_add_sum_filter_not P_odd (fun l : Nat.Primes => (l : ℕ) ∣ M) f).symm
    have hb1 : ∑ l ∈ P₂, f l ≤ B₂ :=
      h2_sum P₂ fun l hl => (Finset.mem_filter.mp hl).2
    have hb2 : ∑ l ∈ P_ram, f l ≤ B_ram :=
      hram_sum P_ram fun l hl =>
        ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).2, (Finset.mem_filter.mp hl).2⟩
    have hb3 : ∑ l ∈ P_pat, f l ≤ B_patch :=
      hpat_sum P_pat fun l hl =>
        ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hl).1).2, (Finset.mem_filter.mp hl).2⟩
    change ∑ l ∈ P, f l ≤ B₂ + B_ram + B_patch
    linarith

/-! ## Section 3: Quantitative `WinPair` / `PageN` Estimates & Direct `VWinAt` / `VWin` Assembly -/

/-- Admissibility envelope for page heights `e x` and cutoff `t x` at scale `x ≥ 2`. -/
def AdmissiblePage (A1 Ct : ℝ) (e t : ℝ → ℕ) : Prop :=
  ∀ x : ℝ, 2 ≤ x →
    2 ≤ e x ∧ (2 : ℝ) ^ e x ≤ x ^ A1 ∧ 2 ≤ t x ∧ (t x : ℝ) ≤ x ^ Ct

/-- Any `PageN eps x (e x)` function with `0 < eps < 1 / 52` and `1 ≤ Ct` satisfies
`AdmissiblePage 4 Ct e (fun x => ⌊x ^ Ct⌋₊)` (matching `AdmissibleOfPageN.lean`). -/
theorem admissible_of_pageN {eps Ct : ℝ} (h0 : 0 < eps) (h1 : eps < 1 / 52) (hC : 1 ≤ Ct)
    {e : ℝ → ℕ} (he : ∀ x ≥ (1 : ℝ), PageN eps x (e x)) :
    AdmissiblePage 4 Ct e (fun x => ⌊x ^ Ct⌋₊) := by
  intro x hx
  have hx1 : (1 : ℝ) ≤ x := by linarith
  obtain ⟨a, b⟩ := he x hx1
  have h2 : x ^ (2 : ℝ) ≤ x ^ (2 + 8 * eps) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have h3 : x ^ (2 + 8 * eps) ≤ x ^ (3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have h4 : x ^ (4 : ℝ) = x * x ^ (3 : ℝ) := by
    rw [show (4 : ℝ) = 1 + 3 by norm_num, Real.rpow_add (by linarith), Real.rpow_one]
  have h5 : (0 : ℝ) ≤ x ^ (3 : ℝ) := by positivity
  have h6 : x ≤ x ^ Ct := Real.self_le_rpow_of_one_le hx1 hC
  have h8 : 2 * x ^ (3 : ℝ) ≤ x * x ^ (3 : ℝ) := mul_le_mul_of_nonneg_right hx h5
  refine ⟨?_, b.trans ((mul_le_mul_of_nonneg_left h3 zero_le_two).trans (h8.trans h4.ge)),
    Nat.le_floor (by push_cast; linarith), Nat.floor_le (by linarith)⟩
  rw [Real.rpow_two] at h2
  have h7 : (2 : ℝ) ^ 2 ≤ 2 ^ e x := by nlinarith
  exact (pow_le_pow_iff_right₀ (by norm_num)).1 h7

/-- Upper bound `log(q * d) ≤ Y ^ (eps / 4)` for any `WinPair eps Y q d` at sufficiently large `Y`
(matching `CMFieldExponentialBounds/logpair.lean`). -/
theorem log_mul_le_rpow_of_winPair (eps : ℝ) (heps : 0 < eps) :
    ∃ Y0 : ℝ, ∀ Y ≥ Y0, ∀ q d : ℕ, WinPair eps Y q d →
      Real.log ((q : ℝ) * d) ≤ Y ^ (eps / 4) := by
  have hs : 0 < eps / 20 := by positivity
  have h1 := (isLittleO_log_rpow_rpow_atTop 2 hs).bound (by norm_num : (0 : ℝ) < 1 / 2)
  have h2 := (tendsto_rpow_atTop hs).eventually_ge_atTop 2
  obtain ⟨Y0, hY0⟩ := Filter.eventually_atTop.1 ((h1.and h2).and (Filter.eventually_gt_atTop 0))
  refine ⟨Y0, fun Y hY q d hw => ?_⟩
  obtain ⟨⟨hl, hg⟩, hpos⟩ := hY0 Y hY
  have hq : (0 : ℝ) < q := by exact_mod_cast hw.q_prime.pos
  have hd : (0 : ℝ) < d := by exact_mod_cast hw.d_prime.pos
  rw [Real.log_mul hq.ne' hd.ne']
  have hA : 0 < Y ^ (eps / 5) := Real.rpow_pos_of_pos hpos _
  have hB : 0 < Y ^ (eps / 20) := Real.rpow_pos_of_pos hpos _
  rw [Real.rpow_two, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    abs_of_pos hB] at hl
  have hsplit : Y ^ (eps / 4) = Y ^ (eps / 5) * Y ^ (eps / 20) := by
    rw [← Real.rpow_add hpos]
    ring_nf
  rw [hsplit]
  have hq' := hw.q_up
  have hd' := hw.d_up
  nlinarith [mul_le_mul_of_nonneg_left hl hA.le, mul_le_mul_of_nonneg_left hg hA.le]

/-- Lower bound forcing both primes `q, d` in `WinPair eps (X ^ (1 / J)) q d` to exceed
`2 * X ^ Ct + 1` and any fixed threshold `P` (matching `CMFieldExponentialBounds/bigpair.lean`). -/
theorem eventually_winPair_gt_power (eps J Ct P : ℝ) (heps : 0 < eps) (hJ : 0 < J) :
    ∃ X0 : ℝ, ∀ X ≥ X0, ∀ q d : ℕ, WinPair eps (X ^ (1 / J)) q d →
      2 * X ^ Ct + 1 < (q : ℝ) ∧ 2 * X ^ Ct + 1 < (d : ℝ) ∧ P < (q : ℝ) ∧ P < (d : ℝ) := by
  set δ : ℝ := 1 / J * (eps / 5) with hδ
  have hδpos : 0 < δ := by positivity
  set mC : ℝ := max Ct 0 with hmC
  set n : ℕ := ⌈(mC + 1) / δ⌉₊ with hn_def
  have hn : mC + 1 ≤ δ * n := by
    have h := Nat.le_ceil ((mC + 1) / δ)
    rw [div_le_iff₀ hδpos] at h
    linarith
  set M : ℝ := 2 ^ n * (n.factorial : ℝ) with hM_def
  have hM : 0 < M := by positivity
  refine ⟨max (Real.exp J) (M * (|P| + 3) + 1), fun X hX q d hw => ?_⟩
  have hXe : Real.exp J ≤ X := le_trans (le_max_left _ _) hX
  have hXM : M * (|P| + 3) + 1 ≤ X := le_trans (le_max_right _ _) hX
  have hX1 : 1 ≤ X := by
    have := Real.add_one_le_exp J
    linarith
  have hX0 : 0 < X := by linarith
  have hY : (X ^ (1 / J)) ^ (eps / 5) = X ^ δ := by
    rw [← Real.rpow_mul hX0.le]
  have hlogY : 1 ≤ Real.log (X ^ (1 / J)) := by
    rw [Real.log_rpow hX0]
    have hJl : J ≤ Real.log X := (Real.le_log_iff_exp_le hX0).2 hXe
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hJ]
    linarith
  set y : ℝ := X ^ δ / 2 with hy_def
  have hy0 : 0 ≤ y := by positivity
  have hfac := Real.pow_div_factorial_le_exp y hy0 n
  have hyn : y ^ n = X ^ (δ * n) / 2 ^ n := by
    rw [hy_def, div_pow, ← Real.rpow_natCast (X ^ δ), ← Real.rpow_mul hX0.le]
  have hlow : X ^ (δ * n) / M ≤ Real.exp y := by
    rw [hyn, div_div] at hfac
    exact hfac
  have hpow : X ^ mC * X ≤ X ^ (δ * n) := by
    rw [← Real.rpow_add_one hX0.ne']
    exact Real.rpow_le_rpow_of_exponent_le hX1 hn
  have hCt : X ^ Ct ≤ X ^ mC := Real.rpow_le_rpow_of_exponent_le hX1 (le_max_left _ _)
  have hmC1 : 1 ≤ X ^ mC := Real.one_le_rpow hX1 (le_max_right _ _)
  have hXdiv : |P| + 3 < X / M := by
    rw [lt_div_iff₀ hM]
    linarith
  have hmain : X ^ mC * (|P| + 3) < Real.exp y := by
    have h1 : X ^ mC * (|P| + 3) < X ^ mC * (X / M) :=
      mul_lt_mul_of_pos_left hXdiv (by linarith)
    have h2 : X ^ mC * (X / M) = X ^ mC * X / M := by ring
    have h3 : X ^ mC * X / M ≤ X ^ (δ * n) / M := div_le_div_of_nonneg_right hpow hM.le
    linarith
  have hP0 : 0 ≤ |P| := abs_nonneg P
  have hB1 : 2 * X ^ Ct + 1 < Real.exp y := by nlinarith
  have hB2 : P < Real.exp y := by
    have := le_abs_self P
    nlinarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hw.q_prime.pos
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hw.d_prime.pos
  have hqlo := hw.q_lo
  have hdlo := hw.d_lo
  rw [hY] at hqlo hdlo
  have hq : Real.exp y < q := by
    rw [← Real.exp_log hq0]
    exact Real.exp_lt_exp.2 (by rw [hy_def]; exact hqlo)
  have hd : Real.exp y < d := by
    rw [← Real.exp_log hd0]
    apply Real.exp_lt_exp.2
    have hXd : 0 ≤ X ^ δ := by positivity
    have hl2 : 1 ≤ Real.log (X ^ (1 / J)) ^ 2 := by nlinarith
    have : X ^ δ / 2 ≤ X ^ δ * Real.log (X ^ (1 / J)) ^ 2 / 2 := by nlinarith
    rw [hy_def]
    linarith
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Conductor-times-height log estimate `log(N * t) ≤ 2 * x ^ (eps / 4)` from `PageN` and
`log(q * d) ≤ x ^ (eps / 4)` (matching `LogConductorMulHeightLeOfPageN.lean`). -/
theorem log_conductor_mul_height_le_of_pageN (eps Ct : ℝ) (m : ℕ)
    (heps : 0 < eps) (heps1 : eps < 1 / 52) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ N t e q d : ℕ, 1 ≤ N → N ≤ 2 ^ (e + 2) * m * q * d →
      PageN eps x e → 1 ≤ t → (t : ℝ) ≤ x ^ Ct → Real.log ((q : ℝ) * d) ≤ x ^ (eps / 4) →
      Real.log ((N : ℝ) * t) ≤ 2 * x ^ (eps / 4) := by
  have hr : 0 < eps / 4 := by positivity
  have hK0 : 0 < 3 + |Ct| := by positivity
  have h1 := (isLittleO_log_rpow_atTop hr).bound (by positivity : (0 : ℝ) < 1 / (2 * (3 + |Ct|)))
  have h2 := (tendsto_rpow_atTop hr).eventually_ge_atTop (2 * (3 * Real.log 2 + Real.log m))
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1 ((h1.and h2).and (Filter.eventually_ge_atTop 1))
  refine ⟨x0, fun x hx N t e q d hN hNle hP ht htx hqd => ?_⟩
  obtain ⟨⟨hl, hg⟩, hx1⟩ := hx0 x hx
  have hxpos : 0 < x := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hX : 0 < x ^ (eps / 4) := Real.rpow_pos_of_pos hxpos _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlogx, abs_of_pos hX] at hl
  have hKl : (3 + |Ct|) * Real.log x ≤ x ^ (eps / 4) / 2 := by
    calc (3 + |Ct|) * Real.log x
        ≤ (3 + |Ct|) * (1 / (2 * (3 + |Ct|)) * x ^ (eps / 4)) :=
          mul_le_mul_of_nonneg_left hl hK0.le
      _ = x ^ (eps / 4) / 2 := by field_simp
  have hprod : 1 ≤ 2 ^ (e + 2) * m * q * d := le_trans hN hNle
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hprod)
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hprod)
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hprod)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have htr : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hqr : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hdr : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hNle' : (N : ℝ) ≤ 2 ^ (e + 2) * m * (q * d) := by
    rw [← mul_assoc]
    exact_mod_cast hNle
  rw [Real.log_mul (by linarith) (by linarith)]
  have hlogN : Real.log N ≤ ((e : ℝ) + 2) * Real.log 2 + Real.log m + Real.log ((q : ℝ) * d) := by
    calc Real.log N
        ≤ Real.log (2 ^ (e + 2) * m * ((q : ℝ) * d)) :=
          Real.log_le_log (by linarith) hNle'
      _ = ((e : ℝ) + 2) * Real.log 2 + Real.log m + Real.log ((q : ℝ) * d) := by
          rw [Real.log_mul (by positivity) (by positivity),
            Real.log_mul (by positivity) (by linarith), Real.log_pow]
          push_cast
          ring
  have hlogt : Real.log t ≤ Ct * Real.log x := by
    calc Real.log t ≤ Real.log (x ^ Ct) := Real.log_le_log (by linarith) htx
      _ = Ct * Real.log x := Real.log_rpow hxpos _
  have hE : (e : ℝ) * Real.log 2 ≤ Real.log 2 + (2 + 8 * eps) * Real.log x := by
    have h := Real.log_le_log (by positivity) hP.2
    rw [Real.log_pow, Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hxpos _).ne',
      Real.log_rpow hxpos] at h
    exact h
  have hC : Ct * Real.log x ≤ |Ct| * Real.log x :=
    mul_le_mul_of_nonneg_right (le_abs_self Ct) hlogx
  nlinarith [mul_nonneg hlogx (by linarith : (0 : ℝ) ≤ 1 - 8 * eps)]

/-- Explicit ramified/minus-part Selmer bound function (matching `minusBound` in `minusle.lean`). -/
def minusBound (C : ℝ) (o n N t : ℕ) : ℝ :=
  3 * (n : ℝ) * (t : ℝ) ^ 2 * Real.log ((t : ℝ) * N) +
    C * ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) * (n : ℝ) ^ 2 * (t : ℝ) ^ 2 *
      Real.log ((t : ℝ) * l * N) ^ 2

/-- Exponential domination of `minusBound` by `K * exp(8 * W)` whenever `log(N * t) ≤ 2 * W`
(matching `CMFieldExponentialBounds/minusle.lean`). -/
theorem minusBound_le_exp_of_log_le (C : ℝ) (o : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (n N t : ℕ) (W : ℝ), 1 ≤ N → 1 ≤ t → n ≤ N →
      Real.log ((N : ℝ) * t) ≤ 2 * W → minusBound C o n N t ≤ K * Real.exp (8 * W) := by
  refine ⟨3 + |C| * ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) ^ 3, by positivity, ?_⟩
  intro n N t W hN ht hn hW
  unfold minusBound
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hn' : (n : ℝ) ≤ N := by exact_mod_cast hn
  have hX1 : (1 : ℝ) ≤ (N : ℝ) * t := one_le_mul_of_one_le_of_one_le hN1 ht1
  have hXpos : 0 < (N : ℝ) * t := by linarith
  have hXe : (N : ℝ) * t ≤ Real.exp (2 * W) := by
    rw [← Real.exp_log hXpos]
    exact Real.exp_le_exp.mpr hW
  have hX4 : ((N : ℝ) * t) ^ 4 ≤ Real.exp (8 * W) := by
    have e : Real.exp (8 * W) = Real.exp (2 * W) ^ 4 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [e]
    exact pow_le_pow_left₀ hXpos.le hXe 4
  have hnt : (n : ℝ) * t ≤ (N : ℝ) * t := mul_le_mul_of_nonneg_right hn' (by positivity)
  have htX : (t : ℝ) ≤ (N : ℝ) * t := by nlinarith
  have hlog : Real.log ((t : ℝ) * N) ≤ (N : ℝ) * t := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < t * N by linarith)
    linarith
  have hlog0 : 0 ≤ Real.log ((t : ℝ) * N) := Real.log_nonneg (by linarith)
  have h1 : 3 * (n : ℝ) * t ^ 2 * Real.log (t * N) ≤ 3 * ((N : ℝ) * t) ^ 4 := by
    have h3 : (n : ℝ) * t * t * Real.log (t * N) ≤ ((N : ℝ) * t) ^ 3 := by
      calc (n : ℝ) * t * t * Real.log (t * N)
          ≤ ((N : ℝ) * t) * ((N : ℝ) * t) * ((N : ℝ) * t) :=
            mul_le_mul (mul_le_mul hnt htX (by positivity) (by positivity)) hlog hlog0 (by positivity)
        _ = ((N : ℝ) * t) ^ 3 := by ring
    have h34 : ((N : ℝ) * t) ^ 3 ≤ ((N : ℝ) * t) ^ 4 := pow_le_pow_right₀ hX1 (by norm_num)
    have e : 3 * (n : ℝ) * t ^ 2 * Real.log (t * N) =
        3 * ((n : ℝ) * t * t * Real.log (t * N)) := by ring
    rw [e]
    linarith
  have h2 : ∑ l ∈ o.primeFactors.erase 2,
        (l : ℝ) * n ^ 2 * t ^ 2 * Real.log (t * l * N) ^ 2
      ≤ (∑ l ∈ o.primeFactors.erase 2, (l : ℝ) ^ 3) * ((N : ℝ) * t) ^ 4 := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro l hl
    have hl1 : (1 : ℝ) ≤ l := by
      have := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hl)
      exact_mod_cast this.one_lt.le
    have hge : (1 : ℝ) ≤ t * l * N :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le ht1 hl1) hN1
    have hlg : Real.log ((t : ℝ) * l * N) ≤ l * ((N : ℝ) * t) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < t * l * N by linarith)
      linarith
    have hlg0 : 0 ≤ Real.log ((t : ℝ) * l * N) := Real.log_nonneg hge
    have hsq : Real.log ((t : ℝ) * l * N) ^ 2 ≤ (l * ((N : ℝ) * t)) ^ 2 :=
      pow_le_pow_left₀ hlg0 hlg 2
    have hnt2 : ((n : ℝ) * t) ^ 2 ≤ ((N : ℝ) * t) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hnt 2
    calc (l : ℝ) * n ^ 2 * t ^ 2 * Real.log (t * l * N) ^ 2
        = (l : ℝ) * ((n : ℝ) * t) ^ 2 * Real.log (t * l * N) ^ 2 := by ring
      _ ≤ (l : ℝ) * ((N : ℝ) * t) ^ 2 * (l * ((N : ℝ) * t)) ^ 2 := by gcongr
      _ = (l : ℝ) ^ 3 * ((N : ℝ) * t) ^ 4 := by ring
  have hS0 : 0 ≤ ∑ l ∈ o.primeFactors.erase 2,
      (l : ℝ) * n ^ 2 * t ^ 2 * Real.log (t * l * N) ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hK0 : 0 ≤ 3 + |C| * ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) ^ 3 := by positivity
  calc 3 * (n : ℝ) * t ^ 2 * Real.log (t * N)
        + C * ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) * n ^ 2 * t ^ 2 * Real.log (t * l * N) ^ 2
      ≤ 3 * ((N : ℝ) * t) ^ 4 +
          |C| * ((∑ l ∈ o.primeFactors.erase 2, (l : ℝ) ^ 3) * ((N : ℝ) * t) ^ 4) :=
        add_le_add h1 ((mul_le_mul_of_nonneg_right (le_abs_self C) hS0).trans
          (mul_le_mul_of_nonneg_left h2 (abs_nonneg C)))
    _ = (3 + |C| * ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) ^ 3) * ((N : ℝ) * t) ^ 4 := by ring
    _ ≤ (3 + |C| * ∑ l ∈ o.primeFactors.erase 2, (l : ℝ) ^ 3) * Real.exp (8 * W) :=
        mul_le_mul_of_nonneg_left hX4 hK0

/-- Combined absorption of the three Selmer-window error parts (2-tower, minus/ramified, and
patching/height-and-vanishing) into `Real.sqrt (Real.exp (x ^ eps))`
(matching `CMFieldExponentialBounds/ErrorTermsLeSqrtExpRpow.lean`). -/
theorem error_terms_le_sqrt_exp_rpow (eps K C : ℝ) (heps : 0 < eps) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ u : ℝ, 1 ≤ u → Real.log u ≤ 2 * x ^ (eps / 4) →
      Real.exp (x ^ (4 * eps / 5)) * Real.log 2 + K * Real.exp (8 * x ^ (eps / 4)) +
          (u ^ C + C * Real.exp (x ^ (4 * eps / 5))) ≤
        Real.sqrt (Real.exp (x ^ eps)) := by
  set N : ℝ := Real.log 2 + |C| + |K| + 1 with hN
  set D : ℝ := 9 + 2 * |C| with hD
  set T : ℝ := 2 * (D + Real.log N + 1) with hTdef
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hN1 : 1 ≤ N := by
    have := abs_nonneg C
    have := abs_nonneg K
    linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hD0 : 9 ≤ D := by
    have := abs_nonneg C
    linarith
  have hT : 0 ≤ T := by linarith
  refine ⟨max 1 (T ^ (5 / eps)), fun x hx u hu hlog => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
  have hxpos : 0 < x := by linarith
  set a := x ^ (eps / 4) with ha
  set b := x ^ (4 * eps / 5) with hb
  set s := x ^ (eps / 5) with hs
  have hab : a ≤ b := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hb1 : 1 ≤ b := Real.one_le_rpow hx1 (by positivity)
  have ha0 : 0 ≤ a := by positivity
  have hc : x ^ eps = b * s := by
    rw [hb, hs, ← Real.rpow_add hxpos]
    congr 1
    ring
  have hsT : T ≤ s := by
    have h1 : T = (T ^ (5 / eps)) ^ (eps / 5) := by
      rw [← Real.rpow_mul hT]
      have : 5 / eps * (eps / 5) = 1 := by field_simp
      rw [this, Real.rpow_one]
    rw [h1, hs]
    exact Real.rpow_le_rpow (by positivity) (le_trans (le_max_right _ _) hx) (by positivity)
  have hlogu : 0 ≤ Real.log u := Real.log_nonneg hu
  have hupos : 0 < u := by linarith
  have huC : u ^ C ≤ Real.exp (D * b) := by
    rw [Real.rpow_def_of_pos hupos]
    apply Real.exp_le_exp.mpr
    have e1 : Real.log u * C ≤ Real.log u * |C| :=
      mul_le_mul_of_nonneg_left (le_abs_self C) hlogu
    have e2 : Real.log u * |C| ≤ (2 * a) * |C| :=
      mul_le_mul_of_nonneg_right hlog (abs_nonneg C)
    have e3 : (2 * a) * |C| ≤ (2 * b) * |C| :=
      mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg C)
    have e4 : (2 * b) * |C| ≤ D * b := by
      rw [hD]
      nlinarith [abs_nonneg C]
    linarith
  have hK : K * Real.exp (8 * a) ≤ |K| * Real.exp (D * b) := by
    have : K * Real.exp (8 * a) ≤ |K| * Real.exp (8 * a) :=
      mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le
    have h2 : Real.exp (8 * a) ≤ Real.exp (D * b) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h3 := mul_le_mul_of_nonneg_left h2 (abs_nonneg K)
    linarith
  have hE : Real.exp b ≤ Real.exp (D * b) := Real.exp_le_exp.mpr (by nlinarith)
  have hCE : C * Real.exp b ≤ |C| * Real.exp (D * b) := by
    have : C * Real.exp b ≤ |C| * Real.exp b :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
    have h3 := mul_le_mul_of_nonneg_left hE (abs_nonneg C)
    linarith
  have hL2 : Real.exp b * Real.log 2 ≤ Real.exp (D * b) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hE hl2.le
  have hsum : Real.exp b * Real.log 2 + K * Real.exp (8 * a) + (u ^ C + C * Real.exp b)
      ≤ N * Real.exp (D * b) := by
    rw [hN]
    nlinarith
  have hfin : N * Real.exp (D * b) ≤ Real.exp (x ^ eps / 2) := by
    rw [← Real.exp_log (by linarith : (0 : ℝ) < N), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [hc]
    have : b * (D + Real.log N + 1) ≤ b * s / 2 := by
      have := mul_le_mul_of_nonneg_left hsT (by linarith : (0 : ℝ) ≤ b)
      rw [hTdef] at this
      linarith
    nlinarith
  rw [Real.exp_half] at hfin
  linarith

/-- Minimal coprime prime-pair condition `(q, d)` relative to character conductor `N`. -/
structure PrimePair (N q d : ℕ) : Prop where
  q_prime : q.Prime
  q_mod : q % 8 = 3
  d_prime : d.Prime
  d_mod : d % 16 = 7
  cop : Nat.Coprime (q * d) N

/-- Conductor and degree invariant carrier for abelian CM host fields `E`. -/
structure HostFieldInvariants where
  condOf : (E : Type) → [Field E] → [NumberField E] → ℕ
  degOf : (E : Type) → [Field E] → [NumberField E] → ℕ

/-- Clean, dead-field-free **Joint Patching + Height-and-Vanishing Window Contract**
(distilling `JointWin` + `ThmBc` + `ConductorBoundsOfIsChiField` in `AdmissibleOfPageN.lean`,
completely stripped of `OpenImageCondition`, `LiteratureCMHypothesis`, and Gen 1–5 wrappers).

For each primitive character `ψ` and admissible page `(e, t)`, supplies a window `[Y, Y^2] ⊆ [X^(1/J), X]`
on which every `IsChiField ψ (e x) q d E` satisfies the three-part patching bound:
- `l = 2` Iwasawa bound `exp(x^(4ε/5)) * log 2`,
- ramified/minus-part bound `minusBound Cb ψ.N (deg E) (cond E) (t x)`,
- odd unramified Taylor–Wiles patching bound `(cond E * t x)^C + C * exp(x^(4ε/5))`. -/
structure JointPatchingWindow (S : SelmerSystem) (inv : HostFieldInvariants) (Ct : ℝ) : Prop where
  cond_bounds : ∀ (ψ : PChar) (e q d : ℕ), 0 < q → 0 < d →
    ∀ (E : Type) [Field E] [NumberField E], IsChiField ψ e q d E →
      1 ≤ inv.condOf E ∧ inv.condOf E ≤ 2 ^ (e + 2) * ψ.N * q * d ∧ inv.degOf E ≤ inv.condOf E
  ram_const : ∃ Cb : ℝ, ∀ (ψ : PChar) (eps : ℝ), 0 < eps → eps < 1 / 52 →
    ∀ (e t : ℝ → ℕ), AdmissiblePage 4 Ct e t →
    ∃ (J C P XJ : ℝ), 0 < J ∧
      ∀ X ≥ XJ, ∀ q d : ℕ, PrimePair ψ.N q d →
        2 * X ^ Ct + 1 < (q : ℝ) → 2 * X ^ Ct + 1 < (d : ℝ) →
        P < (q : ℝ) → P < (d : ℝ) → Real.log ((q : ℝ) * d) ≤ X ^ (eps / (4 * J)) →
        ∃ Y : ℝ, X ^ (1 / J) ≤ Y ∧ Y ^ (2 : ℝ) ≤ X ∧
          ∀ x : ℝ, Y ≤ x → x ≤ Y ^ (2 : ℝ) →
            ∀ (E : Type) [Field E] [NumberField E], IsChiField ψ (e x) q d E →
              VVle S E (t x)
                (Real.exp (x ^ (4 * eps / 5)) * Real.log 2 +
                  minusBound Cb ψ.N (inv.degOf E) (inv.condOf E) (t x) +
                  (((inv.condOf E : ℝ) * (t x : ℝ)) ^ C + C * Real.exp (x ^ (4 * eps / 5))))

/-- **Direct Window Assembly (`VWinAt S ψ Ct`)**: combines `admissible_of_pageN`,
`log_mul_le_rpow_of_winPair`, `eventually_winPair_gt_power`, `log_conductor_mul_height_le_of_pageN`,
`minusBound_le_exp_of_log_le`, `error_terms_le_sqrt_exp_rpow`, and `VVle.mono` to assemble
`VWinAt S ψ Ct` directly from `JointPatchingWindow S inv Ct` for any `1 ≤ Ct`. -/
theorem vwinAt_of_joint_patching {S : SelmerSystem} {inv : HostFieldInvariants} {Ct : ℝ}
    (hC : 1 ≤ Ct) (hJ : JointPatchingWindow S inv Ct) (ψ : PChar) : VWinAt S ψ Ct := by
  intro eps h0 h1 e he
  set t : ℝ → ℕ := fun x => ⌊x ^ Ct⌋₊ with ht
  have hadm : AdmissiblePage 4 Ct e t := admissible_of_pageN h0 h1 hC he
  obtain ⟨Cb, hCb⟩ := hJ.ram_const
  obtain ⟨J, C, P, XJ, hJ0, hmain⟩ := hCb ψ eps h0 h1 e t hadm
  obtain ⟨K, hK0, hK⟩ := minusBound_le_exp_of_log_le Cb ψ.N
  obtain ⟨xT, hxT⟩ := error_terms_le_sqrt_exp_rpow eps K C h0
  obtain ⟨xN, hxN⟩ := log_conductor_mul_height_le_of_pageN eps Ct ψ.N h0 h1
  obtain ⟨Y0, hY0⟩ := log_mul_le_rpow_of_winPair eps h0
  obtain ⟨J', hJ'1, hJJ'⟩ : ∃ J' : ℝ, 1 ≤ J' ∧ J ≤ J' :=
    ⟨max J 1, le_max_right _ _, le_max_left _ _⟩
  have hJ'0 : 0 < J' := by linarith
  obtain ⟨P', hPP', hNP'⟩ : ∃ P' : ℝ, P ≤ P' ∧ (ψ.N : ℝ) ≤ P' :=
    ⟨max P (ψ.N : ℝ), le_max_left _ _, le_max_right _ _⟩
  obtain ⟨XB, hXB⟩ := eventually_winPair_gt_power eps J' Ct P' h0 hJ'0
  obtain ⟨L, hxTL, hxNL, hY0L, h2L⟩ :
      ∃ L : ℝ, xT ≤ L ∧ xN ≤ L ∧ Y0 ≤ L ∧ 2 ≤ L :=
    ⟨max (max xT xN) (max Y0 2),
      le_max_of_le_left (le_max_left _ _), le_max_of_le_left (le_max_right _ _),
      le_max_of_le_right (le_max_left _ _), le_max_of_le_right (le_max_right _ _)⟩
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hL0 : (0 : ℝ) ≤ L := by linarith
  refine ⟨J', hJ'1, max (max XJ XB) (L ^ J'), ?_⟩
  intro X hX q d hw
  have hXJ : XJ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXB' : XB ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hXL : L ^ J' ≤ X := le_trans (le_max_right _ _) hX
  have hLX : L ≤ X ^ (1 / J') := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg hL0 _) hXL (le_of_lt (one_div_pos.mpr hJ'0))
    rwa [← Real.rpow_mul hL0, mul_one_div_cancel hJ'0.ne', Real.rpow_one] at this
  have hX1 : 1 ≤ X := by
    have : 1 ≤ L ^ J' := Real.one_le_rpow hL1 hJ'0.le
    linarith
  have hX0 : (0 : ℝ) ≤ X := by linarith
  obtain ⟨hq3, hd3, hPq, hPd⟩ := hXB X hXB' q d hw
  have hlog := hY0 _ (hY0L.trans hLX) q d hw
  have hpow : (X ^ (1 / J')) ^ (eps / 4) = X ^ (eps / (4 * J')) := by
    rw [← Real.rpow_mul hX0]
    congr 1
    field_simp
  have hmono : X ^ (eps / (4 * J')) ≤ X ^ (eps / (4 * J)) :=
    Real.rpow_le_rpow_of_exponent_le hX1
      (div_le_div_of_nonneg_left h0.le (by positivity) (by linarith))
  have hlogJ : Real.log ((q : ℝ) * d) ≤ X ^ (eps / (4 * J)) := by
    rw [hpow] at hlog
    exact hlog.trans hmono
  have hN0 : 0 < ψ.N := Nat.pos_of_ne_zero (NeZero.ne _)
  have hcop : ∀ r : ℕ, Nat.Prime r → (ψ.N : ℝ) < r → Nat.Coprime r ψ.N := by
    intro r hr hlt
    have hlt' : ψ.N < r := by exact_mod_cast hlt
    exact (Nat.Prime.coprime_iff_not_dvd hr).2
      (fun hdvd => absurd (Nat.le_of_dvd hN0 hdvd) (not_le.2 hlt'))
  have hpp : PrimePair ψ.N q d :=
    ⟨hw.q_prime, hw.q_mod, hw.d_prime, hw.d_mod,
      Nat.Coprime.mul_left (hcop q hw.q_prime (lt_of_le_of_lt hNP' hPq))
        (hcop d hw.d_prime (lt_of_le_of_lt hNP' hPd))⟩
  obtain ⟨Y, hYlo, hYhi, hY⟩ :=
    hmain X hXJ q d hpp hq3 hd3 (lt_of_le_of_lt hPP' hPq) (lt_of_le_of_lt hPP' hPd) hlogJ
  have hWY : X ^ (1 / J') ≤ Y :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hX1
      (one_div_le_one_div_of_le (by linarith) hJJ')) hYlo
  refine ⟨Y, hWY, hYhi, ?_⟩
  intro x hxY hxY2 E _ _ hE
  have hWx : X ^ (1 / J') ≤ x := hWY.trans hxY
  have hLx : L ≤ x := hLX.trans hWx
  have hx2 : 2 ≤ x := h2L.trans hLx
  have hx1 : 1 ≤ x := by linarith
  have hv := hY x hxY hxY2 E hE
  obtain ⟨hc1, hc2, hc3⟩ := hJ.cond_bounds ψ (e x) q d hw.q_prime.pos hw.d_prime.pos E hE
  obtain ⟨-, -, ht2, htle⟩ := hadm x hx2
  have ht1 : 1 ≤ t x := by omega
  have hWpos : (0 : ℝ) ≤ X ^ (1 / J') := Real.rpow_nonneg hX0 _
  have hqd : Real.log ((q : ℝ) * d) ≤ x ^ (eps / 4) := by
    have hlog0 := hY0 _ (hY0L.trans hLX) q d hw
    exact hlog0.trans (Real.rpow_le_rpow hWpos hWx (by linarith))
  have hNt := hxN x (hxNL.trans hLx) (inv.condOf E) (t x) (e x) q d hc1 hc2 (he x hx1) ht1 htle hqd
  have hmb := hK (inv.degOf E) (inv.condOf E) (t x) (x ^ (eps / 4)) hc1 ht1 hc3 hNt
  have hu1 : (1 : ℝ) ≤ (inv.condOf E : ℝ) * (t x : ℝ) := by
    have a : (1 : ℝ) ≤ inv.condOf E := by exact_mod_cast hc1
    have b : (1 : ℝ) ≤ t x := by exact_mod_cast ht1
    nlinarith
  have htot := hxT x (hxTL.trans hLx) ((inv.condOf E : ℝ) * (t x : ℝ)) hu1 hNt
  refine VVle.mono hv le_rfl ?_
  linarith

/-- **Full Selmer/Vandiver Window `VWin S` (`Ct = 401`)** from `JointPatchingWindow S inv 401`. -/
theorem vwin_of_joint_patching {S : SelmerSystem} {inv : HostFieldInvariants}
    (hJ : JointPatchingWindow S inv 401) : VWin S :=
  fun ψ => vwinAt_of_joint_patching (by norm_num) hJ ψ

/-- **Direct Pillar 3 Contract (`GaloisModularityContract S`)** from `JointPatchingWindow S inv 401`,
completely free of `OpenImageCondition`, `LiteratureCMHypothesis`, and Gen 1–5 wrappers! -/
theorem galoisModularityContract_of_patching {S : SelmerSystem} {inv : HostFieldInvariants}
    (hJ : JointPatchingWindow S inv 401) : GaloisModularityContract S :=
  ⟨vwin_of_joint_patching hJ⟩

/-! ## Section 4: The `401 = 400 + 1` Window Scaling & Rank-Bound Bridge -/

/-- Exact asymptotic rank-cutoff bound `(R.t : ℝ) ≤ s.x ^ 400` for `0 < eps < 1 / 52` and
`s.x ≥ 2 ^ 100` (matching `CharacterBoxes/EventuallyRankLeRpowOfLtOneDivFiftytwo.lean`). -/
theorem eventually_rank_le_rpow_400_of_lt_one_div_52 (eps : ℝ)
    (he0 : 0 < eps) (he1 : eps < 1 / 52) :
    ∃ x0 : ℝ, ∀ (s : ScaleParams) (R : ChainRanks),
      s.eps = eps → x0 ≤ s.x →
      s.delta1 = s.x ^ (-(s.eps / 8)) → s.L = s.x ^ s.eps →
      R.f = 2 * R.n → R.r ≤ 2 * R.k → 5 ≤ R.k →
      RankVal s R → (R.t : ℝ) ≤ s.x ^ (400 : ℝ) := by
  refine ⟨(2 : ℝ) ^ 100, ?_⟩
  intro s R hs hx hdelta hLdef hfdef hrle hk5nat hR
  have hX1 : 1 < s.x := s.x_gt_one
  have hX0 : 0 < s.x := by linarith
  have he := s.eps_pos
  have he' := s.eps_lt
  obtain ⟨⟨-, hn2⟩, ⟨hm1, -⟩, ⟨-, hk2⟩, heq⟩ := hR
  have hmono : ∀ a b : ℝ, a ≤ b → s.x ^ a ≤ s.x ^ b :=
    fun a b h => Real.rpow_le_rpow_of_exponent_le hX1.le h
  have hY : ∀ n : ℕ, s.x ^ ((n : ℝ) / 100) = (s.x ^ ((1 : ℝ) / 100)) ^ n := by
    intro n
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
    ring_nf
  have hY2 : (2 : ℝ) ≤ s.x ^ ((1 : ℝ) / 100) := by
    have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 2 ^ 100) hx
      (by norm_num : (0 : ℝ) ≤ 1 / 100)
    have h2 : ((2 : ℝ) ^ 100) ^ ((1 : ℝ) / 100) = 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    linarith
  generalize hYd : s.x ^ ((1 : ℝ) / 100) = Y at hY hY2
  have hY1 : (1 : ℝ) ≤ Y := by linarith
  have hY0 : (0 : ℝ) < Y := by linarith
  have hn : (R.n : ℝ) ≤ 2 * Y ^ 216 := by
    have h := hmono _ _ (show 2 + 8 * s.eps ≤ ((216 : ℕ) : ℝ) / 100 by push_cast; linarith)
    rw [hY] at h
    linarith
  have hfe : (R.f : ℝ) = 2 * (R.n : ℝ) := by exact_mod_cast hfdef
  have hf : (R.f : ℝ) ≤ 4 * Y ^ 216 := by linarith
  have hk : (R.k : ℝ) ≤ 2 * Y ^ 470 := by
    have h := hmono _ _ (show 9 / 2 + 10 * s.eps ≤ ((470 : ℕ) : ℝ) / 100 by push_cast; linarith)
    rw [hY] at h
    linarith
  have hm : Y ^ 49 ≤ (R.m : ℝ) := by
    refine le_trans ?_ hm1
    rw [Real.le_sqrt (by positivity) (mul_nonneg hX0.le s.delta1_pos.le)]
    have h1 : (Y ^ 49) ^ 2 = s.x ^ (((98 : ℕ) : ℝ) / 100) := by rw [hY]; ring
    have h2 : s.x * s.delta1 = s.x ^ ((1 : ℝ) + -(s.eps / 8)) := by
      rw [hdelta, Real.rpow_add hX0, Real.rpow_one]
    rw [h1, h2]
    exact hmono _ _ (by push_cast; linarith)
  have hm0 : (0 : ℝ) < R.m := lt_of_lt_of_le (by positivity) hm
  have hL : s.L ^ 2 ≤ Y ^ 4 := by
    have h1 : s.L ^ 2 = s.x ^ (s.eps * 2) := by
      rw [hLdef, ← Real.rpow_two, ← Real.rpow_mul hX0.le]
    rw [h1]
    have h := hmono _ _ (show s.eps * 2 ≤ ((4 : ℕ) : ℝ) / 100 by push_cast; linarith)
    rw [hY] at h
    exact h
  have hr : (R.r : ℝ) ≤ 4 * Y ^ 470 := by
    have h' : (R.r : ℝ) ≤ 2 * (R.k : ℝ) := by exact_mod_cast hrle
    linarith
  have hk5 : (5 : ℝ) ≤ R.k := by exact_mod_cast hk5nat
  have hk0 : (0 : ℝ) ≤ (R.k : ℝ) - 1 := by linarith
  have hk' : (R.k : ℝ) - 1 ≤ 2 * Y ^ 470 := by linarith
  have hB : (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m ≤ 128 * Y ^ 1797 := by
    rw [div_le_iff₀ hm0]
    calc (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2
        ≤ (4 * Y ^ 216) ^ 2 * (2 * Y ^ 470) ^ 3 * Y ^ 4 := by gcongr
      _ = 128 * Y ^ 1797 * Y ^ 49 := by ring
      _ ≤ 128 * Y ^ 1797 * R.m := by gcongr
  have hp1 : Y ^ 216 ≤ Y ^ 1797 := pow_le_pow_right₀ hY1 (by norm_num)
  have hQ : (R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m ≤ 132 * Y ^ 1797 := by
    linarith
  have hQ0 : 0 ≤ (R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m := by
    have : 0 ≤ (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m :=
      div_nonneg (mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hk0 3)) (by positivity))
        hm0.le
    linarith [Nat.cast_nonneg (α := ℝ) R.f]
  have hr0 : (0 : ℝ) ≤ R.r := by positivity
  have hW : (nWv R s : ℝ) ≤ 5288 * Y ^ 2267 := by
    have hy0 : (0 : ℝ) ≤
        10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) / 8 :=
      div_nonneg (mul_nonneg (by positivity) hQ0) (by norm_num)
    have hc := Nat.ceil_lt_add_one hy0
    have hyb :
        10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) ≤
          10 * (4 * Y ^ 470) * (132 * Y ^ 1797) :=
      mul_le_mul (by linarith) hQ hQ0 (by positivity)
    have hY2267 : (1 : ℝ) ≤ Y ^ 2267 := one_le_pow₀ hY1
    have e1 : 10 * (4 * Y ^ 470) * (132 * Y ^ 1797) = 5280 * Y ^ 2267 := by ring
    unfold nWv
    push_cast
    linarith
  have hT : (TOv s : ℝ) ≤ 2 * Y ^ 37700 := by
    have hc := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ s.x ^ (377 : ℝ) by positivity)
    have h1 : s.x ^ (377 : ℝ) = Y ^ 37700 := by
      rw [show (377 : ℝ) = ((37700 : ℕ) : ℝ) / 100 by norm_num, hY]
    have h2 : (1 : ℝ) ≤ Y ^ 37700 := one_le_pow₀ hY1
    unfold TOv
    linarith
  have heqR : (R.r : ℝ) + R.t = 8 * R.f * R.r + 4 + (TOv s : ℝ) * (nWv R s : ℝ) := by
    exact_mod_cast heq
  have hfr : (R.f : ℝ) * R.r ≤ (4 * Y ^ 216) * (4 * Y ^ 470) :=
    mul_le_mul hf hr hr0 (by positivity)
  have hTW : (TOv s : ℝ) * nWv R s ≤ (2 * Y ^ 37700) * (5288 * Y ^ 2267) :=
    mul_le_mul hT hW (by positivity) (by positivity)
  rw [show (400 : ℝ) = ((40000 : ℕ) : ℝ) / 100 by norm_num, hY]
  have e1 : (4 * Y ^ 216) * (4 * Y ^ 470) = 16 * Y ^ 686 := by ring
  have e2 : (2 * Y ^ 37700) * (5288 * Y ^ 2267) = 10576 * Y ^ 39967 := by ring
  have p1 : Y ^ 686 ≤ Y ^ 39967 := pow_le_pow_right₀ hY1 (by norm_num)
  have p2 : (1 : ℝ) ≤ Y ^ 39967 := one_le_pow₀ hY1
  have p3 : (10708 : ℝ) ≤ Y ^ 33 := by
    have := pow_le_pow_left₀ (by norm_num) hY2 33
    norm_num at this
    linarith
  have e3 : Y ^ 40000 = Y ^ 33 * Y ^ 39967 := by ring
  have p4 : (10708 : ℝ) * Y ^ 39967 ≤ Y ^ 33 * Y ^ 39967 :=
    mul_le_mul_of_nonneg_right p3 (by positivity)
  rw [e3]
  linarith

/-- Clean shifted-window datum produced by `winPairs_of_vwinAt_401` (matching `WinPairs.lean`):
gives an auxiliary pair `(q, d)` at scale `Y ∈ [x^(1/J), x]`, a `c`-shifted page height `e`,
and the Selmer bound `VAt S ψ eps 400 q d e x` (cutoff `⌊x ^ 400⌋₊`). -/
structure WinDatum (S : SelmerSystem) (ψ : PChar) (eps J c x Y : ℝ) (q d e : ℕ) : Prop where
  Y_ge : x ^ (1 / J) ≤ Y
  Y_le : Y ≤ x
  pair : WinPair eps Y q d
  page_lo : x ^ (2 + 8 * eps) ≤ c * (2 : ℝ) ^ e
  page_hi : c * (2 : ℝ) ^ e ≤ 2 * x ^ (2 + 8 * eps)
  vbound : VAt S ψ eps 400 q d e x

/-- Abstract supply of admissible auxiliary prime pairs `WinPair eps Y q d` at all sufficiently
large scales `Y` (matching `PairEx` in `WinPairs.lean`). -/
def PairSupply : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ (eps J : ℝ), 0 < eps → eps < 1 / 52 → 1 ≤ J →
    ∃ Y1 : ℝ, ∀ Y ≥ Y1, ∃ q d : ℕ, WinPair eps Y q d

/-- **The `401 = 400 + 1` Window-Shifting Theorem** (matching `CharacterBoxes/WinPairs.lean`):
from `VWinAt S ψ 401` and `PairSupply`, for every `0 < eps < 1 / 52` and scale factor `1 ≤ c`,
there exists `J ≥ 1` such that for arbitrarily large `Z`, EVERY `x ∈ [Z, Z ^ (3 / 2)]` admits
a `WinDatum S ψ eps J c x Y q d e` with cutoff `⌊x ^ 400⌋₊`!

Key mechanism: setting `k = c ^ (1 / (2 + 8 * eps))` and `Z = k * W` inside `[W, W^2]`, the
`+1` margin in `401 = 400 + 1` absorbs `k ^ 400 ≤ W ≤ x'`, so `(k * x') ^ 400 ≤ (x') ^ 401`,
and `VVle.mono` transfers the Selmer bound from `x'` to `x = k * x'`. -/
theorem winPairs_of_vwinAt_401 {S : SelmerSystem} (ψ : PChar) (eps c : ℝ)
    (heps : 0 < eps) (heps52 : eps < 1 / 52) (hc : 1 ≤ c)
    (hV : VWinAt S ψ 401) (hP : PairSupply) :
    ∃ J : ℝ, 1 ≤ J ∧ ∀ y : ℝ, ∃ Z : ℝ, y ≤ Z ∧
      ∀ x : ℝ, Z ≤ x → x ≤ Z ^ ((3 : ℝ) / 2) →
        ∃ (Y : ℝ) (q d e : ℕ), WinDatum S ψ eps J c x Y q d e := by
  obtain ⟨e, he⟩ := exists_pageN eps heps
  obtain ⟨J, hJ, X0, hX0⟩ := hV eps heps heps52 e he
  have hN : 0 < ψ.N := Nat.pos_of_ne_zero (NeZero.ne _)
  obtain ⟨Y1, hY1⟩ := hP ψ.N hN eps J heps heps52 hJ
  have ha : 0 < 2 + 8 * eps := by linarith
  have hc0 : 0 ≤ c := by linarith
  obtain ⟨k, hk1, hka⟩ : ∃ k : ℝ, 1 ≤ k ∧ k ^ (2 + 8 * eps) = c := by
    refine ⟨c ^ (1 / (2 + 8 * eps)), Real.one_le_rpow hc (one_div_nonneg.2 ha.le), ?_⟩
    rw [one_div, Real.rpow_inv_rpow hc0 ha.ne']
  have hk0 : 0 ≤ k := by linarith
  refine ⟨J, hJ, fun y => ?_⟩
  have hJ0 : J ≠ 0 := ne_of_gt (by linarith)
  have hJi : 0 ≤ 1 / J := one_div_nonneg.2 (by linarith)
  obtain ⟨M, hM1, hMy, hMY1, hMk3, hMk400⟩ :
      ∃ M : ℝ, 1 ≤ M ∧ y ≤ M ∧ Y1 ≤ M ∧ k ^ (3 : ℝ) ≤ M ∧ k ^ (400 : ℝ) ≤ M :=
    ⟨max 1 (max y (max Y1 (max (k ^ (3 : ℝ)) (k ^ (400 : ℝ))))),
      by simp, by simp, by simp, by simp, by simp⟩
  obtain ⟨X, hXX0, hXM⟩ : ∃ X : ℝ, X0 ≤ X ∧ M ^ J ≤ X :=
    ⟨max X0 (M ^ J), le_max_left _ _, le_max_right _ _⟩
  have hM0 : 0 ≤ M := by linarith
  have hY0M : M ≤ X ^ (1 / J) := by
    calc M = (M ^ J) ^ (1 / J) := by rw [one_div, Real.rpow_rpow_inv hM0 hJ0]
      _ ≤ X ^ (1 / J) := Real.rpow_le_rpow (Real.rpow_nonneg hM0 _) hXM hJi
  obtain ⟨q, d, hpg⟩ := hY1 (X ^ (1 / J)) (hMY1.trans hY0M)
  obtain ⟨W, hW0, hW2, hWV⟩ := hX0 X hXX0 q d hpg
  have hWM : M ≤ W := hY0M.trans hW0
  have hW1 : 1 ≤ W := hM1.trans hWM
  have hWnn : 0 ≤ W := by linarith
  have hk3 : k ^ (3 : ℝ) ≤ W := hMk3.trans hWM
  have hlem : (k * W) ^ ((3 : ℝ) / 2) ≤ W ^ (2 : ℝ) := by
    have h1 : (k * W) ^ ((3 : ℝ) / 2) = ((k * W) ^ (3 : ℝ)) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_mul (mul_nonneg hk0 hWnn)]
      norm_num
    have h2 : W ^ (2 : ℝ) = (W ^ (4 : ℝ)) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_mul hWnn]
      norm_num
    rw [h1, h2]
    apply Real.rpow_le_rpow (Real.rpow_nonneg (mul_nonneg hk0 hWnn) _) _ (by norm_num)
    rw [Real.mul_rpow hk0 hWnn, show (4 : ℝ) = 1 + 3 by norm_num,
      Real.rpow_add (by linarith : 0 < W), Real.rpow_one]
    exact mul_le_mul_of_nonneg_right hk3 (Real.rpow_nonneg hWnn _)
  refine ⟨k * W, hMy.trans (hWM.trans (le_mul_of_one_le_left hWnn hk1)), fun x hZx hxZ => ?_⟩
  have hkpos : 0 < k := by linarith
  have hxW2 : x ≤ W ^ (2 : ℝ) := hxZ.trans hlem
  have hxX : x ≤ X := hxW2.trans hW2
  have hx1 : W ≤ x := (le_mul_of_one_le_left hWnn hk1).trans hZx
  have hx0 : 0 ≤ x := by linarith
  obtain ⟨x', rfl⟩ : ∃ x', x = k * x' := ⟨x / k, by field_simp⟩
  have hWx' : W ≤ x' := le_of_mul_le_mul_left hZx hkpos
  have hx'0 : 0 ≤ x' := hWnn.trans hWx'
  have hx'1 : 1 ≤ x' := hW1.trans hWx'
  have hx'x : x' ≤ k * x' := le_mul_of_one_le_left hx'0 hk1
  have hpage : x' ^ (2 + 8 * eps) ≤ 2 ^ (e x') ∧ 2 ^ (e x') ≤ 2 * x' ^ (2 + 8 * eps) :=
    he x' hx'1
  have hpow : (k * x') ^ (2 + 8 * eps) = c * x' ^ (2 + 8 * eps) := by
    rw [Real.mul_rpow hk0 hx'0, hka]
  refine ⟨X ^ (1 / J), q, d, e x', ?_, ?_, hpg, ?_, ?_, ?_⟩
  · exact Real.rpow_le_rpow hx0 hxX hJi
  · exact hW0.trans hx1
  · rw [hpow]
    exact mul_le_mul_of_nonneg_left hpage.1 hc0
  · rw [hpow]
    calc c * 2 ^ (e x') ≤ c * (2 * x' ^ (2 + 8 * eps)) := mul_le_mul_of_nonneg_left hpage.2 hc0
      _ = 2 * (c * x' ^ (2 + 8 * eps)) := by ring
  · intro E _ _ hE
    have hv := hWV x' hWx' (hx'x.trans hxW2) E hE
    refine VVle.mono hv ?_ ?_
    · apply Nat.floor_mono
      rw [Real.mul_rpow hk0 hx'0, show (401 : ℝ) = 1 + 400 by norm_num,
        Real.rpow_add (by linarith : 0 < x'), Real.rpow_one]
      exact mul_le_mul_of_nonneg_right (hMk400.trans (hWM.trans hWx')) (Real.rpow_nonneg hx'0 _)
    · exact Real.sqrt_le_sqrt (Real.exp_le_exp.2 (Real.rpow_le_rpow hx'0 hx'x heps.le))

end RHDirect.TaylorWilesWindow

end
