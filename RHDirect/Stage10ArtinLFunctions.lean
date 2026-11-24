import Mathlib.Algebra.DirectSum.Module
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Equiv
import Mathlib.RepresentationTheory.FinGroupCharZero
import Mathlib.RepresentationTheory.Induced
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Semisimple

/-!
# RHDirect.Stage10ArtinLFunctions

**UNCONDITIONAL ARTIN `L`-FUNCTION FORMALISM (ADDITIVITY, INDUCTIVITY `L(Ind_H^G ρ, s) = L(ρ, s)`,
DEDEKIND ZETA FACTORIZATION `ζ_L(s) = ∏_ρ L(ρ, s)^{dim ρ}`), BRAUER / MONOMIAL INDUCTION FOR
`S_3` & `D_n`, & CONCRETE NON-ABELIAN `S_3` ARTIN `L`-FUNCTION FACTORIZATION AND SPLITTING LAW
FOR `ℚ(∛2)`** (`0` assumptions, `0` `sorry`, `0` custom `axiom`s) in pure Mathlib `v4.33.1`.

## Main Contents
1. **Local Artin Euler Factors & Newton Log-Determinant Identity**:
   - Finite-order diagonalization over `ℂ` (`exists_eigenbasis_of_pow_eq_one`, `exists_eigenbasis_rep`).
   - `artinLocalPoly ρ g T := LinearMap.det (1 - T • ρ g)` and `artinLocalFactor ρ g T := (artinLocalPoly ρ g T)⁻¹`.
   - Isomorphism invariance (`artinLocalFactor_iso`), conjugacy invariance (`artinLocalFactor_conj`),
     relation to `charpoly` (`artinLocalPoly_eq_charpoly_eval`), Newton log-det identity
     (`exp_tsum_character_eq_artinLocalFactor`), and character determination
     (`artinLocalFactor_eq_of_character_eq`).
2. **Three Fundamental Artin Formalism Laws (`0` Assumptions)**:
   - **Additivity**: `artinLocalFactor_prod`, `artinLocalFactor_directSum`.
   - **Trivial & 1D Character**: `artinLocalFactor_trivial`, `artinLocalFactor_repOfChar`.
   - **Inductivity (`artinLocalFactor_ind`)**: for ANY subgroup `H ≤ G` and finite-dimensional `ψ`,
     `artinLocalFactor (Ind_H^G ψ) g T = ∏_{O ∈ orbits(⟨g⟩ on G⧸H)} artinLocalFactor ψ (orbitMonodromy H g O) (T ^ |O|)`.
   - **Permutation & Regular Specializations**: `artinLocalFactor_perm_eq_prod_cycles`,
     `artinLocalFactor_leftRegular_eq_prod_cycles`.
3. **Global Artin `L`-Function `artinL` & General Regular-Representation Factorization**:
   - Absolute convergence & nonvanishing (`artinL_multipliable_and_ne_zero`, `artinL_multipliable`, `artinL_ne_zero`) on `1 < s.re`.
   - Global additivity (`artinL_prod`, `artinL_directSum`), trivial specialization to `riemannZeta s` (`artinL_trivial`),
     and character determination (`artinL_eq_of_character_eq`).
   - Complete irreducible decomposition of `ℂ[G]` with exact multiplicity `dim W_i` and
     **`dedekind_eq_prod_irrep_artinL`**.
4. **General Dihedral `D_n` & Concrete Non-Abelian `S_3 ≃ D_3` Artin Theory**:
   - Explicit 2D dihedral representations `dihedralRep2 n hn k`, irreducibility (`dihedralRep2_isIrreducible`),
     monomial induction **`dihedral_irrep_ind_cyclic`** (`dihedralRep2 n hn k ≃ Ind_{C_n}^{D_n} χ_k`),
     and local Euler factor reduction (`artinLocalFactor_dihedralRep2_eq_ind`).
   - Explicit `S_3 ≃* D_3` (`s3EquivD3`), all 3 irreducible representations (`s3Triv`, `s3Sign`, `s3Rho2`),
     exact character table, regular & cubic permutation decompositions (`s3_reg_character_decomp`,
     `s3_perm3_character_decomp`, `s3_cosetC2_character_decomp`, `s3_cosetC3_character_decomp`),
     monomial induction **`rho2_eq_ind_C3`**, exact Euler factors at all 3 conjugacy classes,
     global Dedekind factorizations (**`zeta_K_eq_zeta_Q_mul_artinL_rho2`**,
     **`zeta_L_eq_zeta_F_mul_artinL_rho2_sq`**, **`artinL_rho2_eq_zeta_K_div_zeta_Q`**,
     **`artin_brauer_kuroda_S3`**), and Hecke identification (**`artinL_rho2_eq_hecke_L_C3`**).
5. **Concrete `ℚ(∛2)` Splitting Law Verification (`X³ - 2` over `𝔽_p`)**:
   - Exact root count & Frobenius law for all primes `p ≠ 2, 3`
     (`numRootsCbrt2_mod_three_eq_two`, `numRootsCbrt2_mod_three_eq_one_of_isCube`,
     `numRootsCbrt2_mod_three_eq_one_of_not_isCube`, `cbrt2_numRoots_eq_one_add_char`),
     concrete prime verifications at `p = 5, 7, 11, 13, 31`, and minimality **`first_split_prime_cbrt2`**.

Zero `sorry`, zero custom `axiom`s.
-/

noncomputable section

open Complex Finset LinearMap Module Representation Subgroup
open scoped BigOperators DirectSum

namespace RHDirect.Stage10ArtinLFunctions

/-! ## Section 1: Finite-Order Diagonalization & Concrete Local Artin Euler Factors -/

section LocalArtinFactor

/-- Primitive `N`-th root of unity `exp(2πi / N)` in `ℂ`. -/
def primRoot (N : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (N : ℂ))

lemma primRoot_ne_zero (N : ℕ) : primRoot N ≠ 0 :=
  Complex.exp_ne_zero _

lemma primRoot_pow_eq_one {N : ℕ} (hN : 0 < N) : (primRoot N) ^ N = 1 := by
  unfold primRoot
  rw [← Complex.exp_nat_mul]
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have harg : (N : ℂ) * (2 * ↑Real.pi * I / (N : ℂ)) = 2 * ↑Real.pi * I := by
    field_simp [hNc]
  rw [harg]
  exact Complex.exp_two_pi_mul_I

lemma norm_primRoot_pow (N k : ℕ) : ‖(primRoot N) ^ k‖ = 1 := by
  rw [norm_pow]
  unfold primRoot
  have hre : (2 * ↑Real.pi * I / (N : ℂ)).re = 0 := by
    rw [div_eq_mul_inv]
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [Complex.norm_exp, hre, Real.exp_zero, one_pow]

lemma primRoot_pow_injective {N : ℕ} (hN : 0 < N) :
    Function.Injective (fun k : Fin N => (primRoot N) ^ k.1) := by
  intro k₁ k₂ h
  dsimp only at h
  unfold primRoot at h
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int] at h
  obtain ⟨m, hm⟩ := h
  have hpi : (2 * ↑Real.pi * I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have h1 : ((k₁.1 : ℂ) / (N : ℂ) - (k₂.1 : ℂ) / (N : ℂ) - (m : ℂ)) * (2 * ↑Real.pi * I) = 0 := by
    have hm' : (k₁.1 : ℂ) * (2 * ↑Real.pi * I / (N : ℂ)) -
        (k₂.1 : ℂ) * (2 * ↑Real.pi * I / (N : ℂ)) - (m : ℂ) * (2 * ↑Real.pi * I) = 0 := by
      linear_combination hm
    convert hm' using 1
    ring
  have h2 : (k₁.1 : ℂ) / (N : ℂ) - (k₂.1 : ℂ) / (N : ℂ) - (m : ℂ) = 0 :=
    (mul_eq_zero.mp h1).resolve_right hpi
  have h3 : ((((k₁.1 : ℤ) - (k₂.1 : ℤ)) : ℤ) : ℂ) = ((m * (N : ℤ) : ℤ) : ℂ) := by
    push_cast
    have h2' := congr_arg (· * (N : ℂ)) h2
    simp only [zero_mul] at h2'
    field_simp [hNc] at h2'
    linear_combination h2'
  have h4 : (k₁.1 : ℤ) - (k₂.1 : ℤ) = m * (N : ℤ) := Int.cast_injective h3
  have hlt1 : (k₁.1 : ℤ) < (N : ℤ) := Int.ofNat_lt.mpr k₁.2
  have hlt2 : (k₂.1 : ℤ) < (N : ℤ) := Int.ofNat_lt.mpr k₂.2
  have hm0 : m = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have : m * (N : ℤ) ≤ -(N : ℤ) := by nlinarith
      omega
    · have : (N : ℤ) ≤ m * (N : ℤ) := by nlinarith
      omega
  have hk : k₁.1 = k₂.1 := by
    have h4' : (k₁.1 : ℤ) - (k₂.1 : ℤ) = 0 := by rw [h4, hm0, zero_mul]
    omega
  exact Fin.ext hk

/-- **Finite-Order Diagonalization over `ℂ`**: every linear endomorphism `f` of a
finite-dimensional complex vector space satisfying `f ^ N = 1` (`0 < N`) admits a basis of
eigenvectors whose eigenvalues are `N`-th roots of unity (hence of modulus `1`). -/
theorem exists_eigenbasis_of_pow_eq_one {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (f : Module.End ℂ V) {N : ℕ} (hN : 0 < N) (hf : f ^ N = 1) :
    ∃ (b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V)
      (ev : Fin (Module.finrank ℂ V) → ℂ),
      (∀ i, f (b i) = ev i • b i) ∧ (∀ i, (ev i) ^ N = 1) ∧ (∀ i, ‖ev i‖ = 1) := by
  let ζ : ℂ := primRoot N
  have hζ_ne : ζ ≠ 0 := primRoot_ne_zero N
  have hζN : ζ ^ N = 1 := primRoot_pow_eq_one hN
  have hζ_inj : Function.Injective (fun k : Fin N => ζ ^ k.1) := primRoot_pow_injective hN
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  let P : Fin N → Module.End ℂ V := fun k =>
    (N : ℂ)⁻¹ • ∑ j : Fin N, (ζ ^ (-(k.1 * j.1 : ℤ))) • f ^ j.1
  have hsumP : ∑ k : Fin N, P k = 1 := by
    dsimp only [P]
    rw [← Finset.smul_sum, Finset.sum_comm]
    have hinner : ∀ j : Fin N,
        ∑ k : Fin N, (ζ ^ (-(k.1 * j.1 : ℤ))) • f ^ j.1 =
          if j.1 = 0 then (N : ℂ) • (1 : Module.End ℂ V) else 0 := by
      intro j
      rw [← Finset.sum_smul]
      split_ifs with hj0
      · simp [hj0]
      · let w : ℂ := ζ ^ (-(j.1 : ℤ))
        have hw_pow : ∀ k : Fin N, ζ ^ (-(k.1 * j.1 : ℤ)) = w ^ k.1 := by
          intro k
          dsimp only [w]
          rw [← zpow_natCast, ← zpow_mul]
          congr 1
          ring
        have hw_ne : w ≠ 1 := by
          intro hw1
          have h1 : ζ ^ j.1 = 1 := by
            have hinv : w⁻¹ = 1 := by rw [hw1, inv_one]
            dsimp only [w] at hinv
            rw [← zpow_neg, neg_neg, zpow_natCast] at hinv
            exact hinv
          have h0 : (⟨0, hN⟩ : Fin N) = j := hζ_inj (by simpa using h1.symm)
          exact hj0 (congr_arg Fin.val h0).symm
        have hwN : w ^ N = 1 := by
          dsimp only [w]
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζN, one_zpow]
        have hgeom : ∑ k : Fin N, ζ ^ (-(k.1 * j.1 : ℤ)) = 0 := by
          simp_rw [hw_pow]
          rw [Fin.sum_univ_eq_sum_range (fun k => w ^ k), geom_sum_eq hw_ne, hwN, sub_self,
            zero_div]
        rw [hgeom, zero_smul]
    simp_rw [hinner]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    have hfilt : (Finset.univ.filter fun j : Fin N => j.1 = 0) = {⟨0, hN⟩} := by
      ext j
      simp [Fin.ext_iff]
    rw [hfilt, Finset.sum_singleton, smul_smul, inv_mul_cancel₀ hNc, one_smul]
  have hshift_eq : ∀ j : Fin N, f ^ ((j.1 + 1) % N) = f ^ (j.1 + 1) := by
    intro j
    by_cases hlt : j.1 + 1 < N
    · rw [Nat.mod_eq_of_lt hlt]
    · have heq : j.1 + 1 = N := by omega
      rw [heq, Nat.mod_self, pow_zero, hf]
  have hζ_mod : ∀ (k : Fin N) (j : Fin N),
      ζ ^ (-((k.1 : ℤ) * (((j.1 + 1) % N : ℕ) : ℤ))) = ζ ^ (-((k.1 : ℤ) * ((j.1 + 1 : ℕ) : ℤ))) := by
    intro k j
    by_cases hlt : j.1 + 1 < N
    · rw [Nat.mod_eq_of_lt hlt]
    · have heq : j.1 + 1 = N := by omega
      rw [heq, Nat.mod_self]
      have h1 : -((k.1 : ℤ) * (N : ℤ)) = (N : ℤ) * (-(k.1 : ℤ)) := by ring
      rw [Nat.cast_zero, mul_zero, neg_zero, zpow_zero, h1, zpow_mul, zpow_natCast, hζN, one_zpow]
  have hfP : ∀ k : Fin N, f * P k = (ζ ^ k.1) • P k := by
    intro k
    dsimp only [P]
    rw [mul_smul_comm, smul_comm]
    congr 1
    rw [Finset.mul_sum, Finset.smul_sum]
    let e : Fin N ≃ Fin N :=
      { toFun := fun j => ⟨(j.1 + 1) % N, Nat.mod_lt _ hN⟩
        invFun := fun j => ⟨(j.1 + (N - 1)) % N, Nat.mod_lt _ hN⟩
        left_inv := fun j => by
          apply Fin.ext
          have hj := j.2
          have : (j.1 + 1) % N + (N - 1) ≡ j.1 + 1 + (N - 1) [MOD N] :=
            Nat.ModEq.add_right _ (Nat.mod_modEq _ _)
          have h2 : j.1 + 1 + (N - 1) = j.1 + N := by omega
          rw [h2] at this
          simpa [Nat.ModEq, Nat.mod_eq_of_lt hj] using this
        right_inv := fun j => by
          apply Fin.ext
          have hj := j.2
          have : (j.1 + (N - 1)) % N + 1 ≡ j.1 + (N - 1) + 1 [MOD N] :=
            Nat.ModEq.add_right _ (Nat.mod_modEq _ _)
          have h2 : j.1 + (N - 1) + 1 = j.1 + N := by omega
          rw [h2] at this
          simpa [Nat.ModEq, Nat.mod_eq_of_lt hj] using this }
    symm
    rw [← Equiv.sum_comp e]
    apply Finset.sum_congr rfl
    intro j _
    have he_val : (e j).1 = (j.1 + 1) % N := rfl
    simp only [he_val]
    rw [hshift_eq j, smul_smul, mul_smul_comm]
    have hpow : f * f ^ j.1 = f ^ (j.1 + 1) := by rw [pow_succ']
    rw [hpow]
    congr 1
    have hm := hζ_mod k j
    push_cast at hm ⊢
    rw [hm, ← zpow_natCast, ← zpow_add₀ hζ_ne]
    congr 1
    ring
  have hmem_eig : ∀ (k : Fin N) (v : V), P k v ∈ f.eigenspace (ζ ^ k.1) := by
    intro k v
    rw [Module.End.mem_eigenspace_iff]
    have h1 := congr_arg (fun T : Module.End ℂ V => T v) (hfP k)
    simpa [Module.End.mul_apply] using h1
  have hiSup_top : (⨆ k : Fin N, f.eigenspace (ζ ^ k.1)) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have hv : v = ∑ k : Fin N, P k v := by
      have h1 := congr_arg (fun T : Module.End ℂ V => T v) hsumP
      simpa [LinearMap.sum_apply] using h1.symm
    rw [hv]
    exact Submodule.sum_mem _ fun k _ => Submodule.mem_iSup_of_mem k (hmem_eig k v)
  have hind : iSupIndep (fun k : Fin N => f.eigenspace (ζ ^ k.1)) :=
    f.eigenspaces_iSupIndep.comp hζ_inj
  have hisInt : DirectSum.IsInternal (fun k : Fin N => f.eigenspace (ζ ^ k.1)) :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr ⟨hind, hiSup_top⟩
  let b0 := hisInt.collectedBasis (fun k : Fin N => Module.finBasis ℂ (f.eigenspace (ζ ^ k.1)))
  have hcard : Fintype.card (Σ k : Fin N, Fin (Module.finrank ℂ (f.eigenspace (ζ ^ k.1)))) =
      Module.finrank ℂ V := (Module.finrank_eq_card_basis b0).symm
  let eIdx := Fintype.equivFinOfCardEq hcard
  let b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V := b0.reindex eIdx
  let ev : Fin (Module.finrank ℂ V) → ℂ := fun i => ζ ^ (eIdx.symm i).1.1
  refine ⟨b, ev, ?_, ?_, ?_⟩
  · intro i
    have hbi : b i = b0 (eIdx.symm i) := by simp [b]
    rw [hbi]
    have hmem : b0 (eIdx.symm i) ∈ f.eigenspace (ζ ^ (eIdx.symm i).1.1) := by
      rw [DirectSum.IsInternal.collectedBasis_coe]
      exact (Module.finBasis ℂ (f.eigenspace (ζ ^ (eIdx.symm i).1.1)) (eIdx.symm i).2).2
    exact Module.End.mem_eigenspace_iff.mp hmem
  · intro i
    dsimp only [ev]
    rw [← pow_mul, mul_comm, pow_mul, hζN, one_pow]
  · intro i
    exact norm_primRoot_pow N (eIdx.symm i).1.1

/-- Local Artin characteristic polynomial factor `det(1 - T · ρ(g))` for a finite-dimensional
complex representation `ρ` of a group `G`. -/
def artinLocalPoly {G V : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (g : G) (T : ℂ) : ℂ :=
  LinearMap.det ((1 : Module.End ℂ V) - T • (ρ g))

/-- Local Artin Euler factor `det(1 - T · ρ(g))⁻¹` for a finite-dimensional complex
representation `ρ` of a group `G`. -/
def artinLocalFactor {G V : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (g : G) (T : ℂ) : ℂ :=
  (artinLocalPoly ρ g T)⁻¹

@[simp]
theorem artinLocalPoly_zero {G V : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    artinLocalPoly ρ g 0 = 1 := by
  simp [artinLocalPoly]

@[simp]
theorem artinLocalFactor_zero {G V : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    artinLocalFactor ρ g 0 = 1 := by
  simp [artinLocalFactor]

/-- Isomorphic representations have identical local Artin polynomials. -/
theorem artinLocalPoly_iso {G V W : Type*} [Monoid G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (φ : Representation.Equiv ρ σ) (g : G) (T : ℂ) :
    artinLocalPoly ρ g T = artinLocalPoly σ g T := by
  unfold artinLocalPoly
  have hconj : (1 : Module.End ℂ W) - T • σ g =
      φ.toLinearEquiv.toLinearMap ∘ₗ ((1 : Module.End ℂ V) - T • ρ g) ∘ₗ
        φ.toLinearEquiv.symm.toLinearMap := by
    ext w
    have hcomm : σ g w = φ.toLinearEquiv (ρ g (φ.toLinearEquiv.symm w)) := by
      have h1 := φ.isIntertwining' g
      have h2 := congr_arg (fun f : V →ₗ[ℂ] W => f (φ.toLinearEquiv.symm w)) h1
      change φ.toLinearEquiv (ρ g (φ.toLinearEquiv.symm w)) = σ g (φ.toLinearEquiv (φ.toLinearEquiv.symm w)) at h2
      rw [φ.toLinearEquiv.apply_symm_apply] at h2
      exact h2.symm
    change w - T • σ g w = φ.toLinearEquiv (φ.toLinearEquiv.symm w - T • ρ g (φ.toLinearEquiv.symm w))
    rw [map_sub, map_smul, φ.toLinearEquiv.apply_symm_apply, hcomm]
  rw [hconj, LinearMap.det_conj]

/-- Isomorphic representations have identical local Artin Euler factors. -/
theorem artinLocalFactor_iso {G V W : Type*} [Monoid G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (φ : Representation.Equiv ρ σ) (g : G) (T : ℂ) :
    artinLocalFactor ρ g T = artinLocalFactor σ g T := by
  simp [artinLocalFactor, artinLocalPoly_iso φ g T]

/-- Conjugacy invariance of `artinLocalPoly`: `det(1 - T · ρ(h g h⁻¹)) = det(1 - T · ρ(g))`. -/
theorem artinLocalPoly_conj {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (g h : G) (T : ℂ) :
    artinLocalPoly ρ (h * g * h⁻¹) T = artinLocalPoly ρ g T := by
  unfold artinLocalPoly
  let eh : V ≃ₗ[ℂ] V := LinearEquiv.ofLinearMap (ρ h) (ρ h⁻¹)
    (by ext v; simp [← Module.End.mul_apply, ← map_mul])
    (by ext v; simp [← Module.End.mul_apply, ← map_mul])
  have hconj : (1 : Module.End ℂ V) - T • ρ (h * g * h⁻¹) =
      eh.toLinearMap ∘ₗ ((1 : Module.End ℂ V) - T • ρ g) ∘ₗ eh.symm.toLinearMap := by
    ext v
    have hmul : ρ (h * g * h⁻¹) v = ρ h (ρ g (ρ h⁻¹ v)) := by
      simp [map_mul, Module.End.mul_apply]
    simp [eh, map_sub, map_smul, hmul, ← Module.End.mul_apply, ← map_mul]
  rw [hconj, LinearMap.det_conj]

/-- Conjugacy invariance of `artinLocalFactor`: depends only on the conjugacy class of `g`. -/
theorem artinLocalFactor_conj {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (g h : G) (T : ℂ) :
    artinLocalFactor ρ (h * g * h⁻¹) T = artinLocalFactor ρ g T := by
  simp [artinLocalFactor, artinLocalPoly_conj]

/-- Relation between `artinLocalPoly` and Mathlib's characteristic polynomial `LinearMap.charpoly`. -/
theorem artinLocalPoly_eq_charpoly_eval {G V : Type*} [Monoid G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) {T : ℂ} (hT : T ≠ 0) :
    artinLocalPoly ρ g T = T ^ Module.finrank ℂ V * (ρ g).charpoly.eval T⁻¹ := by
  unfold artinLocalPoly
  have hsplit : (1 : Module.End ℂ V) - T • ρ g = T • (T⁻¹ • (1 : Module.End ℂ V) - ρ g) := by
    ext v
    simp [smul_sub, smul_smul, mul_inv_cancel₀ hT]
  rw [hsplit, LinearMap.det_smul]
  congr 1
  have hb := Module.finBasis ℂ V
  rw [← LinearMap.det_toMatrix hb]
  have hchar : (ρ g).charpoly = (LinearMap.toMatrix hb hb (ρ g)).charpoly :=
    (LinearMap.charpoly_toMatrix (ρ g) hb).symm
  rw [hchar, Matrix.eval_charpoly]
  congr 1
  ext i j
  simp [map_sub, map_smul, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.diagonal_apply]

/-- Eigenbasis product formula for `artinLocalPoly` and character power-sums. -/
theorem artinLocalPoly_eq_prod_of_eigenbasis {G V ι : Type*} [Monoid G]
    [AddCommGroup V] [Module ℂ V] [Fintype ι] [DecidableEq ι]
    (ρ : Representation ℂ G V) (g : G) (b : Module.Basis ι ℂ V) (ev : ι → ℂ)
    (hev : ∀ i, ρ g (b i) = ev i • b i) (T : ℂ) :
    artinLocalPoly ρ g T = ∏ i : ι, (1 - ev i * T) := by
  unfold artinLocalPoly
  rw [← LinearMap.det_toMatrix b]
  have hdiag : LinearMap.toMatrix b b ((1 : Module.End ℂ V) - T • ρ g) =
      Matrix.diagonal (fun i => 1 - ev i * T) := by
    ext i j
    rw [LinearMap.toMatrix_apply, LinearMap.sub_apply, Module.End.one_apply, LinearMap.smul_apply,
      hev j, map_sub, map_smul, map_smul, b.repr_self]
    by_cases hij : i = j
    · subst hij
      simp [Matrix.diagonal_apply_eq, mul_comm]
    · simp [Matrix.diagonal_apply_ne _ hij, Ne.symm hij]
  rw [hdiag, Matrix.det_diagonal]

theorem character_pow_eq_sum_of_eigenbasis {G V ι : Type*} [Monoid G]
    [AddCommGroup V] [Module ℂ V] [Fintype ι] [DecidableEq ι]
    (ρ : Representation ℂ G V) (g : G) (b : Module.Basis ι ℂ V) (ev : ι → ℂ)
    (hev : ∀ i, ρ g (b i) = ev i • b i) (m : ℕ) :
    ρ.character (g ^ m) = ∑ i : ι, (ev i) ^ m := by
  unfold Representation.character
  rw [map_pow]
  have hpow : ∀ i, ((ρ g) ^ m) (b i) = (ev i) ^ m • b i := by
    intro i
    induction m with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, hev i, smul_smul, pow_succ', mul_comm]
  rw [LinearMap.trace_eq_matrix_trace ℂ b]
  simp only [Matrix.trace, Matrix.diag]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.toMatrix_apply, hpow i, map_smul, b.repr_self]
  simp

/-- Existence of a unitary eigenbasis for `ρ g` when `G` is a finite group. -/
theorem exists_eigenbasis_rep {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    ∃ (b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V)
      (ev : Fin (Module.finrank ℂ V) → ℂ),
      (∀ i, ρ g (b i) = ev i • b i) ∧
      (∀ i, (ev i) ^ orderOf g = 1) ∧
      (∀ i, ‖ev i‖ = 1) := by
  have hord : 0 < orderOf g := orderOf_pos g
  have hpow : (ρ g) ^ orderOf g = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  exact exists_eigenbasis_of_pow_eq_one (ρ g) hord hpow

/-- Nonvanishing of `artinLocalPoly` and `artinLocalFactor` on the open unit disk `‖T‖ < 1`. -/
theorem artinLocalPoly_ne_zero_of_norm_lt_one {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) {T : ℂ} (hT : ‖T‖ < 1) :
    artinLocalPoly ρ g T ≠ 0 := by
  obtain ⟨b, ev, hev, _, hnorm⟩ := exists_eigenbasis_rep ρ g
  rw [artinLocalPoly_eq_prod_of_eigenbasis ρ g b ev hev T]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _ h0
  have heq : ev i * T = 1 := (sub_eq_zero.mp h0).symm
  have hn : ‖ev i * T‖ = 1 := by rw [heq, norm_one]
  rw [norm_mul, hnorm i, one_mul] at hn
  linarith

theorem artinLocalFactor_ne_zero_of_norm_lt_one {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) {T : ℂ} (hT : ‖T‖ < 1) :
    artinLocalFactor ρ g T ≠ 0 :=
  inv_ne_zero (artinLocalPoly_ne_zero_of_norm_lt_one ρ g hT)

/-- **Newton / Log-Determinant Identity**: on the open unit disk `‖T‖ < 1`,
`exp (∑_{m ≥ 1} (χ_ρ(g^m) / m) * T^m) = artinLocalFactor ρ g T`. -/
theorem exp_tsum_character_eq_artinLocalFactor {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) {T : ℂ} (hT : ‖T‖ < 1) :
    Complex.exp (∑' m : ℕ, (ρ.character (g ^ (m + 1)) / ((m + 1 : ℕ) : ℂ)) * T ^ (m + 1)) =
      artinLocalFactor ρ g T := by
  obtain ⟨b, ev, hev, _, hnorm⟩ := exists_eigenbasis_rep ρ g
  have hhas : ∀ i : Fin (Module.finrank ℂ V),
      HasSum (fun m : ℕ => ((ev i) ^ (m + 1) / ((m + 1 : ℕ) : ℂ)) * T ^ (m + 1))
        (-Complex.log (1 - ev i * T)) := by
    intro i
    have hz : ‖ev i * T‖ < 1 := by rw [norm_mul, hnorm i, one_mul]; exact hT
    have hlog := Complex.hasSum_taylorSeries_neg_log hz
    have hshift : HasSum (fun m : ℕ => (ev i * T) ^ (m + 1) / ((m + 1 : ℕ) : ℂ))
        (-Complex.log (1 - ev i * T)) := by
      have h0 : (ev i * T) ^ 0 / (0 : ℂ) = 0 := by simp
      have := (hasSum_nat_add_iff' (f := fun n : ℕ => (ev i * T) ^ n / (n : ℂ)) 1).mpr hlog
      simpa [Finset.sum_range_one, h0] using this
    refine hshift.congr_fun fun m => ?_
    rw [mul_pow, mul_div_right_comm]
  have hsum : HasSum
      (fun m : ℕ => (ρ.character (g ^ (m + 1)) / ((m + 1 : ℕ) : ℂ)) * T ^ (m + 1))
      (∑ i : Fin (Module.finrank ℂ V), -Complex.log (1 - ev i * T)) := by
    have hfin := hasSum_sum (s := Finset.univ) fun i _ => hhas i
    refine hfin.congr_fun fun m => ?_
    rw [character_pow_eq_sum_of_eigenbasis ρ g b ev hev (m + 1), Finset.sum_div, Finset.sum_mul]
  rw [hsum.tsum_eq, Complex.exp_sum]
  unfold artinLocalFactor
  rw [artinLocalPoly_eq_prod_of_eigenbasis ρ g b ev hev T, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hne : 1 - ev i * T ≠ 0 := by
    intro h0
    have heq : ev i * T = 1 := (sub_eq_zero.mp h0).symm
    have hn : ‖ev i * T‖ = 1 := by rw [heq, norm_one]
    rw [norm_mul, hnorm i, one_mul] at hn
    linarith
  rw [Complex.exp_neg, Complex.exp_log hne]

/-- **Character Determination of Local Artin Euler Factors**: two finite-dimensional complex
representations with the same character have identical `artinLocalFactor` at every `g : G` and
every `T : ℂ`. -/
theorem artinLocalFactor_eq_of_character_eq {G V W : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (hchar : ρ.character = σ.character) (g : G) (T : ℂ) :
    artinLocalFactor ρ g T = artinLocalFactor σ g T := by
  suffices hpoly : artinLocalPoly ρ g T = artinLocalPoly σ g T by
    simp [artinLocalFactor, hpoly]
  obtain ⟨b₁, ev₁, hev₁, _, _⟩ := exists_eigenbasis_rep ρ g
  obtain ⟨b₂, ev₂, hev₂, _, _⟩ := exists_eigenbasis_rep σ g
  let p₁ : Polynomial ℂ := ∏ i : Fin (Module.finrank ℂ V), (1 - Polynomial.C (ev₁ i) * Polynomial.X)
  let p₂ : Polynomial ℂ := ∏ i : Fin (Module.finrank ℂ W), (1 - Polynomial.C (ev₂ i) * Polynomial.X)
  have hp₁ : ∀ z : ℂ, p₁.eval z = artinLocalPoly ρ g z := by
    intro z
    rw [artinLocalPoly_eq_prod_of_eigenbasis ρ g b₁ ev₁ hev₁ z]
    simp [p₁, Polynomial.eval_prod]
  have hp₂ : ∀ z : ℂ, p₂.eval z = artinLocalPoly σ g z := by
    intro z
    rw [artinLocalPoly_eq_prod_of_eigenbasis σ g b₂ ev₂ hev₂ z]
    simp [p₂, Polynomial.eval_prod]
  have hpeq : p₁ = p₂ := by
    by_contra hne
    have hdiff_ne : p₁ - p₂ ≠ 0 := sub_ne_zero.mpr hne
    have hinf : Set.Infinite {z : ℂ | (p₁ - p₂).eval z = 0} := by
      have hsub : Set.range (fun n : ℕ => (((n + 2 : ℕ) : ℂ)⁻¹)) ⊆
          {z : ℂ | (p₁ - p₂).eval z = 0} := by
        rintro _ ⟨n, rfl⟩
        have hlt : ‖(((n + 2 : ℕ) : ℂ)⁻¹)‖ < 1 := by
          rw [norm_inv, Complex.norm_natCast]
          have h2 : (1 : ℝ) < ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < n + 2)
          exact inv_lt_one_of_one_lt₀ h2
        have hfac : artinLocalFactor ρ g (((n + 2 : ℕ) : ℂ)⁻¹) =
            artinLocalFactor σ g (((n + 2 : ℕ) : ℂ)⁻¹) := by
          rw [← exp_tsum_character_eq_artinLocalFactor ρ g hlt,
            ← exp_tsum_character_eq_artinLocalFactor σ g hlt, hchar]
        have hpol : artinLocalPoly ρ g (((n + 2 : ℕ) : ℂ)⁻¹) =
            artinLocalPoly σ g (((n + 2 : ℕ) : ℂ)⁻¹) :=
          inv_injective hfac
        change (p₁ - p₂).eval (((n + 2 : ℕ) : ℂ)⁻¹) = 0
        rw [Polynomial.eval_sub, hp₁, hp₂, hpol, sub_self]
      refine Set.Infinite.mono hsub (Set.infinite_range_of_injective ?_)
      intro m n hmn
      have hcast : ((m + 2 : ℕ) : ℂ) = ((n + 2 : ℕ) : ℂ) := inv_injective hmn
      exact Nat.add_right_cancel (Nat.cast_injective hcast)
    have hfin : {z : ℂ | (p₁ - p₂).eval z = 0}.Finite := by
      have : {z : ℂ | (p₁ - p₂).eval z = 0} = ((p₁ - p₂).roots.toFinset : Set ℂ) := by
        ext z
        simp [Polynomial.mem_roots hdiff_ne, Polynomial.IsRoot.def]
      rw [this]
      exact Finset.finite_toSet _
    exact hinf hfin
  rw [← hp₁, ← hp₂, hpeq]

end LocalArtinFactor

/-! ## Section 2: The Three Fundamental Artin Formalism Laws (Additivity, Trivial/1D, Inductivity) -/

section ArtinFormalism

/-- **Law 1 (Binary Additivity)**: `artinLocalFactor (ρ₁ ⊕ ρ₂) g T = artinLocalFactor ρ₁ g T * artinLocalFactor ρ₂ g T`. -/
theorem artinLocalPoly_prod {G V₁ V₂ : Type*} [Group G] [Finite G]
    [AddCommGroup V₁] [Module ℂ V₁] [FiniteDimensional ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] [FiniteDimensional ℂ V₂]
    (ρ₁ : Representation ℂ G V₁) (ρ₂ : Representation ℂ G V₂) (g : G) (T : ℂ) :
    artinLocalPoly (Representation.prod ρ₁ ρ₂) g T =
      artinLocalPoly ρ₁ g T * artinLocalPoly ρ₂ g T := by
  obtain ⟨b₁, ev₁, hev₁, _, _⟩ := exists_eigenbasis_rep ρ₁ g
  obtain ⟨b₂, ev₂, hev₂, _, _⟩ := exists_eigenbasis_rep ρ₂ g
  let b := b₁.prod b₂
  let ev := Sum.elim ev₁ ev₂
  have hev : ∀ i, (Representation.prod ρ₁ ρ₂) g (b i) = ev i • b i := by
    rintro (i | j)
    · ext <;> simp [b, ev, Representation.prod, hev₁]
    · ext <;> simp [b, ev, Representation.prod, hev₂]
  rw [artinLocalPoly_eq_prod_of_eigenbasis _ g b ev hev T,
    artinLocalPoly_eq_prod_of_eigenbasis ρ₁ g b₁ ev₁ hev₁ T,
    artinLocalPoly_eq_prod_of_eigenbasis ρ₂ g b₂ ev₂ hev₂ T,
    Fintype.prod_sum_type]
  rfl

theorem artinLocalFactor_prod {G V₁ V₂ : Type*} [Group G] [Finite G]
    [AddCommGroup V₁] [Module ℂ V₁] [FiniteDimensional ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] [FiniteDimensional ℂ V₂]
    (ρ₁ : Representation ℂ G V₁) (ρ₂ : Representation ℂ G V₂) (g : G) (T : ℂ) :
    artinLocalFactor (Representation.prod ρ₁ ρ₂) g T =
      artinLocalFactor ρ₁ g T * artinLocalFactor ρ₂ g T := by
  simp [artinLocalFactor, artinLocalPoly_prod, mul_comm]

/-- **Law 1 (Finite Direct Sum Additivity)**:
`artinLocalFactor (⨁ i, ρ i) g T = ∏ i, artinLocalFactor (ρ i) g T`. -/
theorem artinLocalPoly_directSum {G ι : Type*} [Group G] [Finite G] [Fintype ι] [DecidableEq ι]
    {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i)) (g : G) (T : ℂ) :
    artinLocalPoly (Representation.directSum ρ) g T =
      ∏ i : ι, artinLocalPoly (ρ i) g T := by
  have heig : ∀ i : ι, ∃ (b : Module.Basis (Fin (Module.finrank ℂ (V i))) ℂ (V i))
      (ev : Fin (Module.finrank ℂ (V i)) → ℂ), ∀ j, ρ i g (b j) = ev j • b j := by
    intro i
    obtain ⟨b, ev, hev, _, _⟩ := exists_eigenbasis_rep (ρ i) g
    exact ⟨b, ev, hev⟩
  choose b ev hev using heig
  let eDS : (⨁ i : ι, V i) ≃ₗ[ℂ] (∀ i : ι, V i) := DirectSum.linearEquivFunOnFintype ℂ ι V
  let B : Module.Basis (Σ i : ι, Fin (Module.finrank ℂ (V i))) ℂ (⨁ i, V i) :=
    (Pi.basis b).map eDS.symm
  let EV : (Σ i : ι, Fin (Module.finrank ℂ (V i))) → ℂ := fun p => ev p.1 p.2
  have hEV : ∀ p, (Representation.directSum ρ) g (B p) = EV p • B p := by
    rintro ⟨i, j⟩
    have hB : B ⟨i, j⟩ = DirectSum.lof ℂ ι V i (b i j) := by
      apply eDS.injective
      ext k
      simp only [B, Basis.map_apply, Pi.basis_apply, eDS, DirectSum.linearEquivFunOnFintype_apply]
      change Pi.single i (b i j) k = DirectSum.of V i (b i j) k
      by_cases hki : k = i
      · subst hki; simp
      · rw [Pi.single_eq_of_ne hki, DirectSum.of_eq_of_ne i k (b i j) hki]
    rw [hB]
    change DirectSum.lmap (fun k => ρ k g) (DirectSum.lof ℂ ι V i (b i j)) =
      ev i j • DirectSum.lof ℂ ι V i (b i j)
    rw [DirectSum.lmap_lof, hev i j, map_smul]
  rw [artinLocalPoly_eq_prod_of_eigenbasis _ g B EV hEV T, Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro i _
  exact (artinLocalPoly_eq_prod_of_eigenbasis (ρ i) g (b i) (ev i) (hev i) T).symm

theorem artinLocalFactor_directSum {G ι : Type*} [Group G] [Finite G] [Fintype ι] [DecidableEq ι]
    {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i)) (g : G) (T : ℂ) :
    artinLocalFactor (Representation.directSum ρ) g T =
      ∏ i : ι, artinLocalFactor (ρ i) g T := by
  simp [artinLocalFactor, artinLocalPoly_directSum, Finset.prod_inv_distrib]

/-- 1-dimensional complex representation associated to a character `χ : G →* ℂˣ`. -/
def repOfChar {G : Type*} [Monoid G] (χ : G →* ℂˣ) : Representation ℂ G ℂ where
  toFun g := ((χ g : ℂ) • (1 : Module.End ℂ ℂ))
  map_one' := by ext; simp
  map_mul' g₁ g₂ := by ext; simp [mul_comm]

@[simp]
theorem repOfChar_apply {G : Type*} [Monoid G] (χ : G →* ℂˣ) (g : G) (z : ℂ) :
    repOfChar χ g z = (χ g : ℂ) * z := by
  simp [repOfChar]

@[simp]
theorem repOfChar_character {G : Type*} [Monoid G] (χ : G →* ℂˣ) (g : G) :
    (repOfChar χ).character g = (χ g : ℂ) := by
  unfold Representation.character
  rw [LinearMap.trace_eq_matrix_trace ℂ (Module.Basis.singleton Unit ℂ)]
  simp [Matrix.trace, repOfChar]

/-- **Law 2 (1-Dimensional Character Euler Factor)**:
`artinLocalFactor (repOfChar χ) g T = (1 - χ(g) T)⁻¹`. -/
theorem artinLocalPoly_repOfChar {G : Type*} [Monoid G] (χ : G →* ℂˣ) (g : G) (T : ℂ) :
    artinLocalPoly (repOfChar χ) g T = 1 - (χ g : ℂ) * T := by
  have hev : ∀ _ : Unit, repOfChar χ g (Module.Basis.singleton Unit ℂ ()) =
      (χ g : ℂ) • Module.Basis.singleton Unit ℂ () := by
    intro _; simp
  rw [artinLocalPoly_eq_prod_of_eigenbasis (repOfChar χ) g (Module.Basis.singleton Unit ℂ)
    (fun _ => (χ g : ℂ)) hev T]
  simp

theorem artinLocalFactor_repOfChar {G : Type*} [Monoid G] (χ : G →* ℂˣ) (g : G) (T : ℂ) :
    artinLocalFactor (repOfChar χ) g T = (1 - (χ g : ℂ) * T)⁻¹ := by
  simp [artinLocalFactor, artinLocalPoly_repOfChar]

/-- **Law 2 (Trivial Representation Euler Factor)**:
`artinLocalFactor (Representation.trivial ℂ G ℂ) g T = (1 - T)⁻¹`. -/
theorem artinLocalFactor_trivial {G : Type*} [Monoid G] (g : G) (T : ℂ) :
    artinLocalFactor (Representation.trivial ℂ G ℂ) g T = (1 - T)⁻¹ := by
  have heq : Representation.trivial ℂ G ℂ = repOfChar (1 : G →* ℂˣ) := by
    ext g
    simp [Representation.trivial]
  rw [heq, artinLocalFactor_repOfChar]
  simp

/-- Cyclic shift matrix of size `d ≥ 1` with monodromy twist `μ`:
sends `e_j ↦ e_{j+1}` for `j + 1 < d` and `e_{d-1} ↦ μ • e_0`. -/
def cyclicShiftMatrix (d : ℕ) (μ : ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j =>
    if j.1 + 1 = i.1 then 1
    else if i.1 = 0 ∧ j.1 + 1 = d then μ
    else 0

/-- Exact determinant of `1 - T · C(d, μ)` for the twisted cyclic shift matrix:
`det(1 - T · C(d, μ)) = 1 - μ · T^d`. -/
theorem det_one_sub_smul_cyclicShiftMatrix (d : ℕ) (hd : 0 < d) (μ T : ℂ) :
    Matrix.det ((1 : Matrix (Fin d) (Fin d) ℂ) - T • cyclicShiftMatrix d μ) = 1 - μ * T ^ d := by
  cases d with
  | zero => exact absurd hd (lt_irrefl 0)
  | succ m =>
    cases m with
    | zero =>
      rw [Matrix.det_fin_one]
      simp [cyclicShiftMatrix, mul_comm]
    | succ k =>
      let M : Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ :=
        (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ) - T • cyclicShiftMatrix (k + 2) μ
      change M.det = 1 - μ * T ^ (k + 2)
      rw [Matrix.det_succ_row_zero]
      have hrow0 : ∀ j : Fin (k + 2),
          M 0 j = if j = 0 then 1 else if j = Fin.last (k + 1) then -(T * μ) else 0 := by
        intro j
        by_cases hj0 : j = 0
        · subst hj0
          simp [M, cyclicShiftMatrix]
        · by_cases hjl : j = Fin.last (k + 1)
          · subst hjl
            simp [M, cyclicShiftMatrix, Fin.last]
          · have hjv : j.1 ≠ k + 1 := fun h => hjl (Fin.ext h)
            have h0j : (0 : Fin (k + 2)) ≠ j := fun h => hj0 h.symm
            simp [M, cyclicShiftMatrix, hj0, hjl, hjv, Matrix.one_apply_ne h0j]
      have hne : (0 : Fin (k + 2)) ≠ Fin.last (k + 1) := by
        intro h
        have := congr_arg Fin.val h
        simp [Fin.last] at this
      have hsum_two :
          ∑ j : Fin (k + 2), (-1 : ℂ) ^ (j : ℕ) * M 0 j * (M.submatrix Fin.succ j.succAbove).det =
            (M.submatrix Fin.succ (0 : Fin (k + 2)).succAbove).det +
            (-1 : ℂ) ^ (k + 1) * (-(T * μ)) *
              (M.submatrix Fin.succ (Fin.last (k + 1)).succAbove).det := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (k + 2)))]
        have hmemL : Fin.last (k + 1) ∈ Finset.univ.erase (0 : Fin (k + 2)) :=
          Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩
        rw [← Finset.add_sum_erase _ _ hmemL]
        have hrest : ∑ j ∈ (Finset.univ.erase (0 : Fin (k + 2))).erase (Fin.last (k + 1)),
            (-1 : ℂ) ^ (j : ℕ) * M 0 j * (M.submatrix Fin.succ j.succAbove).det = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          have hjl : j ≠ Fin.last (k + 1) := (Finset.mem_erase.mp hj).1
          have hj0 : j ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
          simp [hrow0 j, hj0, hjl]
        rw [hrest, add_zero]
        simp [hrow0, Fin.last]
      rw [hsum_two]
      -- First minor: lower triangular (zero for i < j, i.e., toDual j < toDual i) with 1 on diagonal
      have hdet0 : (M.submatrix Fin.succ (0 : Fin (k + 2)).succAbove).det = 1 := by
        have htri : (M.submatrix Fin.succ (0 : Fin (k + 2)).succAbove).BlockTriangular OrderDual.toDual := by
          intro i j hij
          have hlt : i < j := OrderDual.ofDual_lt_ofDual.mp hij
          simp only [Matrix.submatrix_apply, Fin.succAbove_zero]
          have hne' : i.succ ≠ j.succ := ne_of_lt (Fin.succ_lt_succ_iff.mpr hlt)
          have hstep : j.1 + 1 ≠ i.1 := by omega
          simp [M, cyclicShiftMatrix, Matrix.one_apply_ne hne', hstep]
        rw [Matrix.BlockTriangular.det htri]
        apply Finset.prod_eq_one
        intro i _
        let : Unique {a : Fin (k + 1) // OrderDual.toDual a = i} :=
          { default := ⟨OrderDual.ofDual i, rfl⟩
            uniq := fun ⟨a, ha⟩ => Subtype.ext (OrderDual.toDual.injective (ha.trans rfl)) }
        rw [Matrix.det_unique]
        simp only [Matrix.toSquareBlock_def, Matrix.submatrix_apply, Fin.succAbove_zero]
        change M (OrderDual.ofDual i).succ (OrderDual.ofDual i).succ = 1
        simp [M, cyclicShiftMatrix]
      -- Second minor: upper triangular (zero for j < i, i.e., id j < id i) with -T on diagonal
      have hdetL : (M.submatrix Fin.succ (Fin.last (k + 1)).succAbove).det = (-T) ^ (k + 1) := by
        have htri : (M.submatrix Fin.succ (Fin.last (k + 1)).succAbove).BlockTriangular _root_.id := by
          intro i j hij
          have hlt : j < i := hij
          simp only [Matrix.submatrix_apply, Fin.succAbove_last]
          have hne' : i.succ ≠ j.castSucc := by
            intro h; have := congr_arg Fin.val h; simp at this; omega
          have hstep : j.1 ≠ i.1 := ne_of_lt hlt
          simp [M, cyclicShiftMatrix, Matrix.one_apply_ne hne', hstep]
        rw [Matrix.BlockTriangular.det htri]
        have hsq : ∀ i : Fin (k + 1),
            ((M.submatrix Fin.succ (Fin.last (k + 1)).succAbove).toSquareBlock _root_.id i).det = -T := by
          intro i
          let : Unique {a : Fin (k + 1) // _root_.id a = i} :=
            { default := ⟨i, rfl⟩
              uniq := fun ⟨a, ha⟩ => Subtype.ext ha }
          rw [Matrix.det_unique]
          simp only [Matrix.toSquareBlock_def, Matrix.submatrix_apply, Fin.succAbove_last]
          change M i.succ i.castSucc = -T
          have hne' : i.succ ≠ i.castSucc := by
            intro h; have := congr_arg Fin.val h; simp at this
          simp [M, cyclicShiftMatrix, Matrix.one_apply_ne hne']
        simp_rw [hsq]
        simp
      rw [hdet0, hdetL]
      have hsign : (-1 : ℂ) ^ (k + 1) * (-T) ^ (k + 1) = T ^ (k + 1) := by
        rw [← mul_pow]
        simp
      calc
        1 + (-1 : ℂ) ^ (k + 1) * -(T * μ) * (-T) ^ (k + 1)
            = 1 - μ * T * ((-1 : ℂ) ^ (k + 1) * (-T) ^ (k + 1)) := by ring
        _ = 1 - μ * T * T ^ (k + 1) := by rw [hsign]
        _ = 1 - μ * T ^ (k + 2) := by rw [pow_succ']; ring

/-- Determinant of a heterogeneous block-diagonal matrix equals the product of the determinants
of its diagonal blocks. -/
theorem det_blockDiagonal' {o : Type*} [Fintype o] [DecidableEq o]
    {m : o → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    {R : Type*} [CommRing R] (M : ∀ i, Matrix (m i) (m i) R) :
    (Matrix.blockDiagonal' M).det = ∏ i : o, (M i).det := by
  let eO : o ≃ Fin (Fintype.card o) := Fintype.equivFin o
  let b : (Σ i : o, m i) → Fin (Fintype.card o) := fun x => eO x.1
  have htri : (Matrix.blockDiagonal' M).BlockTriangular b := by
    intro x y hxy
    have hne : x.1 ≠ y.1 := fun h => ne_of_lt hxy (congr_arg eO h.symm)
    exact Matrix.blockDiagonal'_apply_ne M x.2 y.2 hne
  rw [Matrix.BlockTriangular.det htri]
  have hblock : ∀ k : Fin (Fintype.card o),
      ((Matrix.blockDiagonal' M).toSquareBlock b k).det = (M (eO.symm k)).det := by
    intro k
    let eK : {x : Σ i : o, m i // b x = k} ≃ m (eO.symm k) :=
      { toFun := fun ⟨⟨i, j⟩, hij⟩ =>
          have hi : i = eO.symm k := by
            apply eO.injective
            simpa [b] using hij
          hi ▸ j
        invFun := fun j => ⟨⟨eO.symm k, j⟩, by simp [b]⟩
        left_inv := fun ⟨⟨i, j⟩, hij⟩ => by
          have hi : i = eO.symm k := by
            apply eO.injective
            simpa [b] using hij
          subst hi
          rfl
        right_inv := fun j => rfl }
    rw [← Matrix.det_reindex_self eK ((Matrix.blockDiagonal' M).toSquareBlock b k)]
    congr 1
    ext j₁ j₂
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.toSquareBlock_def, eK,
      Matrix.blockDiagonal'_apply_eq]
  rw [Finset.prod_congr rfl fun k _ => hblock k]
  rw [Finset.prod_subset (Finset.subset_univ (Finset.univ.image b))]
  · rw [← Equiv.prod_comp eO.symm]
  · intro k _ hk
    have hemp : IsEmpty (m (eO.symm k)) :=
      ⟨fun j => hk (Finset.mem_image.mpr ⟨⟨eO.symm k, j⟩, Finset.mem_univ _, by simp [b]⟩)⟩
    exact Matrix.det_isEmpty

/-! ### Orbit Decomposition for Finite `G`-Sets and Artin Inductivity -/

section OrbitAndInductivity

open Classical

variable {G : Type*} [Group G] [Fintype G]

/-- Type of `⟨g⟩`-orbits on a `G`-set `X`. -/
abbrev CycleOrbits (g : G) (X : Type*) [MulAction G X] : Type _ :=
  Quotient (MulAction.orbitRel (Subgroup.zpowers g) X)

/-- Cardinality of a `⟨g⟩`-orbit `O` on a finite `G`-set `X`. -/
def orbitSize {X : Type*} [Finite X] [MulAction G X] (g : G) (O : CycleOrbits g X) : ℕ :=
  Nat.card {x : X // Quotient.mk (MulAction.orbitRel (Subgroup.zpowers g) X) x = O}

omit [Fintype G] in
lemma orbitSize_pos {X : Type*} [Finite X] [MulAction G X] (g : G) (O : CycleOrbits g X) :
    0 < orbitSize g O := by
  unfold orbitSize
  obtain ⟨x, rfl⟩ := Quotient.exists_rep O
  exact Nat.card_pos_iff.mpr ⟨⟨⟨x, rfl⟩⟩, inferInstance⟩

/-- For any `x` in an orbit `O` of `⟨g⟩` on a finite `G`-set `X`, the orbit size equals the minimal
positive period `d` such that `g^d • x = x`, and `j : Fin d ↦ g^j • x` bijects onto the orbit. -/
lemma orbit_cycle_equiv {X : Type*} [Finite X] [MulAction G X] (g : G)
    (O : CycleOrbits g X) (x : X)
    (hx : Quotient.mk (MulAction.orbitRel (Subgroup.zpowers g) X) x = O) :
    (g ^ orbitSize g O) • x = x ∧
      Function.Bijective (fun j : Fin (orbitSize g O) =>
        (⟨(g ^ j.1) • x,
          (Quotient.sound (show MulAction.orbitRel (Subgroup.zpowers g) X ((g ^ j.1) • x) x from
            ⟨⟨g ^ j.1, Subgroup.npow_mem_zpowers g j.1⟩, rfl⟩)).trans hx⟩ :
          {y : X // Quotient.mk (MulAction.orbitRel (Subgroup.zpowers g) X) y = O})) := by
  have hex : ∃ k : ℕ, 0 < k ∧ (g ^ k) • x = x :=
    ⟨orderOf g, orderOf_pos g, by rw [pow_orderOf_eq_one, one_smul]⟩
  let d := Nat.find hex
  have hd_pos : 0 < d := (Nat.find_spec hex).1
  have hd_fix : (g ^ d) • x = x := (Nat.find_spec hex).2
  have hd_min : ∀ k : ℕ, 0 < k → k < d → (g ^ k) • x ≠ x := fun k hk1 hk2 =>
    fun h => Nat.find_min hex hk2 ⟨hk1, h⟩
  have hzpow : ∀ z : ℤ, (g ^ z) • x = (g ^ (z % (d : ℤ)).toNat) • x := by
    intro z
    have hdn : (d : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hd_pos.ne'
    have hdiv : z = (d : ℤ) * (z / (d : ℤ)) + z % (d : ℤ) := (Int.mul_ediv_add_emod z d).symm
    have hrem_nn : 0 ≤ z % (d : ℤ) := Int.emod_nonneg z hdn
    have hq : ∀ q : ℤ, ((g ^ d) ^ q) • x = x := by
      intro q
      induction q using Int.induction_on with
      | zero => simp
      | succ n ih =>
        rw [zpow_add, zpow_one, mul_smul, hd_fix, ih]
      | pred n ih =>
        have hinv : (g ^ d)⁻¹ • x = x := by
          calc (g ^ d)⁻¹ • x = (g ^ d)⁻¹ • ((g ^ d) • x) := by rw [hd_fix]
          _ = x := inv_smul_smul _ _
        rw [sub_eq_add_neg, zpow_add, zpow_neg_one, mul_smul, hinv, ih]
    have hsplit : g ^ z = g ^ (z % (d : ℤ)).toNat * (g ^ d) ^ (z / (d : ℤ)) := by
      calc g ^ z
          = g ^ ((d : ℤ) * (z / (d : ℤ)) + z % (d : ℤ)) := by rw [← hdiv]
      _ = g ^ ((d : ℤ) * (z / (d : ℤ))) * g ^ (z % (d : ℤ)) := zpow_add g _ _
      _ = g ^ (z % (d : ℤ)) * g ^ ((d : ℤ) * (z / (d : ℤ))) := by
          rw [← zpow_add, ← zpow_add, add_comm]
      _ = g ^ (z % (d : ℤ)).toNat * (g ^ d) ^ (z / (d : ℤ)) := by
          rw [← zpow_natCast, Int.toNat_of_nonneg hrem_nn, zpow_mul, zpow_natCast]
    rw [hsplit, mul_smul, hq]
  let f : Fin d → {y : X // Quotient.mk (MulAction.orbitRel (Subgroup.zpowers g) X) y = O} :=
    fun j => ⟨(g ^ j.1) • x,
      (Quotient.sound (show MulAction.orbitRel (Subgroup.zpowers g) X ((g ^ j.1) • x) x from
        ⟨⟨g ^ j.1, Subgroup.npow_mem_zpowers g j.1⟩, rfl⟩)).trans hx⟩
  have hf_inj : Function.Injective f := by
    intro i j hij
    have heq : (g ^ i.1) • x = (g ^ j.1) • x := congr_arg Subtype.val hij
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
    · have hsub : (g ^ (j.1 - i.1)) • x = x := by
        have hji : g ^ j.1 = g ^ i.1 * g ^ (j.1 - i.1) := by
          rw [← pow_add, Nat.add_sub_cancel' hlt.le]
        have h1 := congr_arg ((g ^ i.1)⁻¹ • ·) heq
        rw [inv_smul_smul, hji, mul_smul, inv_smul_smul] at h1
        exact h1.symm
      exact hd_min (j.1 - i.1) (by omega) (by omega) hsub
    · have hsub : (g ^ (i.1 - j.1)) • x = x := by
        have hij' : g ^ i.1 = g ^ j.1 * g ^ (i.1 - j.1) := by
          rw [← pow_add, Nat.add_sub_cancel' hgt.le]
        have h1 := congr_arg ((g ^ j.1)⁻¹ • ·) heq
        rw [hij', mul_smul, inv_smul_smul, inv_smul_smul] at h1
        exact h1
      exact hd_min (i.1 - j.1) (by omega) (by omega) hsub
  have hf_surj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    have hrel : MulAction.orbitRel (Subgroup.zpowers g) X y x :=
      Quotient.exact (hy.trans hx.symm)
    obtain ⟨⟨a, ha⟩, hay⟩ := hrel
    rw [Subgroup.mem_zpowers_iff] at ha
    obtain ⟨z, rfl⟩ := ha
    have hy_eq : y = (g ^ z) • x := hay.symm
    rw [hzpow z] at hy_eq
    have hlt : (z % (d : ℤ)).toNat < d := by
      have hdn : (0 : ℤ) < (d : ℤ) := Int.natCast_pos.mpr hd_pos
      have hltz : z % (d : ℤ) < (d : ℤ) := Int.emod_lt_of_pos z hdn
      omega
    exact ⟨⟨(z % (d : ℤ)).toNat, hlt⟩, Subtype.ext hy_eq.symm⟩
  have hcard : orbitSize g O = d := by
    unfold orbitSize
    have heq := Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at heq
    exact heq.symm
  refine ⟨by rw [hcard]; exact hd_fix, ?_⟩
  have hfn : (fun j : Fin (orbitSize g O) =>
      (⟨(g ^ j.1) • x,
        (Quotient.sound (show MulAction.orbitRel (Subgroup.zpowers g) X ((g ^ j.1) • x) x from
          ⟨⟨g ^ j.1, Subgroup.npow_mem_zpowers g j.1⟩, rfl⟩)).trans hx⟩ :
        {y : X // Quotient.mk (MulAction.orbitRel (Subgroup.zpowers g) X) y = O})) =
      f ∘ Fin.cast hcard := by
    ext j; rfl
  rw [hfn]
  have hbij_f : Function.Bijective f := ⟨hf_inj, hf_surj⟩
  exact hbij_f.comp (Fin.castOrderIso hcard).bijective

/-- Helper coset representative `q.out : G` for `q : G ⧸ H`. -/
def cosetOut (H : Subgroup G) (q : G ⧸ H) : G :=
  Quotient.out (s := QuotientGroup.leftRel H) q

omit [Fintype G] in
lemma cosetOut_eq (H : Subgroup G) (q : G ⧸ H) : ((cosetOut H q : G) : G ⧸ H) = q :=
  Quotient.out_eq (s := QuotientGroup.leftRel H) q

/-- Concrete finite-dimensional model of the induced representation `Ind_H^G ψ` on `(G ⧸ H) → W`,
using `cosetOut H` as a system of left coset representatives. -/
def indModel (H : Subgroup G) {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ψ : Representation ℂ H W) : Representation ℂ G ((G ⧸ H) → W) where
  toFun g :=
    { toFun := fun f q =>
        ψ ⟨(cosetOut H q)⁻¹ * g * cosetOut H (g⁻¹ • q), by
          have h1 : ((cosetOut H q : G) : G ⧸ H) = q := cosetOut_eq H q
          have h2 : ((cosetOut H (g⁻¹ • q) : G) : G ⧸ H) = g⁻¹ • q := cosetOut_eq H (g⁻¹ • q)
          have h3 : ((g * cosetOut H (g⁻¹ • q) : G) : G ⧸ H) = ((cosetOut H q : G) : G ⧸ H) := by
            change g • ((cosetOut H (g⁻¹ • q) : G) : G ⧸ H) = ((cosetOut H q : G) : G ⧸ H)
            rw [h2, h1, smul_inv_smul]
          rw [mul_assoc]
          exact QuotientGroup.leftRel_apply.mp (Quotient.exact h3.symm)⟩ (f (g⁻¹ • q))
      map_add' := fun f₁ f₂ => by ext q; simp
      map_smul' := fun c f => by ext q; simp }
  map_one' := by
    refine LinearMap.ext fun f => funext fun q => ?_
    change ψ ⟨(cosetOut H q)⁻¹ * 1 * cosetOut H ((1 : G)⁻¹ • q), _⟩ (f ((1 : G)⁻¹ • q)) = f q
    have hq : (1 : G)⁻¹ • q = q := by simp
    have h1 : (⟨(cosetOut H q)⁻¹ * 1 * cosetOut H ((1 : G)⁻¹ • q), by
        simp⟩ : H) = 1 := by
      apply Subtype.ext; simp
    rw [h1, hq, map_one, Module.End.one_apply]
  map_mul' g₁ g₂ := by
    refine LinearMap.ext fun f => funext fun q => ?_
    change ψ _ (f ((g₁ * g₂)⁻¹ • q)) = ψ _ (ψ _ (f (g₂⁻¹ • (g₁⁻¹ • q))))
    have hq : (g₁ * g₂)⁻¹ • q = g₂⁻¹ • (g₁⁻¹ • q) := by rw [mul_inv_rev, mul_smul]
    rw [← Module.End.mul_apply, ← map_mul]
    congr 1
    · congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, mul_assoc, mul_inv_cancel_left]
      rw [hq]
    · rw [hq]

omit [Fintype G] in
@[simp]
lemma indModel_apply (H : Subgroup G) {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ψ : Representation ℂ H W) (g : G) (f : (G ⧸ H) → W) (q : G ⧸ H) :
    indModel H ψ g f q =
      ψ ⟨(cosetOut H q)⁻¹ * g * cosetOut H (g⁻¹ • q), by
        have h1 : ((cosetOut H q : G) : G ⧸ H) = q := cosetOut_eq H q
        have h2 : ((cosetOut H (g⁻¹ • q) : G) : G ⧸ H) = g⁻¹ • q := cosetOut_eq H (g⁻¹ • q)
        have h3 : ((g * cosetOut H (g⁻¹ • q) : G) : G ⧸ H) = ((cosetOut H q : G) : G ⧸ H) := by
          change g • ((cosetOut H (g⁻¹ • q) : G) : G ⧸ H) = ((cosetOut H q : G) : G ⧸ H)
          rw [h2, h1, smul_inv_smul]
        rw [mul_assoc]
        exact QuotientGroup.leftRel_apply.mp (Quotient.exact h3.symm)⟩ (f (g⁻¹ • q)) := rfl

/-- Canonical isomorphism between Mathlib's `Representation.ind H.subtype ψ` and the concrete
finite-dimensional model `indModel H ψ` on `(G ⧸ H) → W`. -/
def indEquivIndModel (H : Subgroup G) {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ψ : Representation ℂ H W) :
    Representation.Equiv (Representation.ind H.subtype ψ) (indModel H ψ) := by
  have hα : ∀ x : G, (cosetOut H ((x⁻¹ : G) : G ⧸ H))⁻¹ * x⁻¹ ∈ H := fun x =>
    QuotientGroup.leftRel_apply.mp (Quotient.exact (cosetOut_eq H ((x⁻¹ : G) : G ⧸ H)))
  let fwdElem : G → W →ₗ[ℂ] ((G ⧸ H) → W) := fun x =>
    { toFun := fun w q =>
        if q = ((x⁻¹ : G) : G ⧸ H) then ψ ⟨(cosetOut H ((x⁻¹ : G) : G ⧸ H))⁻¹ * x⁻¹, hα x⟩ w else 0
      map_add' := fun w₁ w₂ => by
        ext q
        dsimp only [Pi.add_apply]
        by_cases hq : q = ((x⁻¹ : G) : G ⧸ H) <;> simp [hq]
      map_smul' := fun c w => by
        ext q
        dsimp only [Pi.smul_apply, RingHom.id_apply]
        by_cases hq : q = ((x⁻¹ : G) : G ⧸ H) <;> simp [hq] }
  let fwdAlg : MonoidAlgebra ℂ G →ₗ[ℂ] (W →ₗ[ℂ] ((G ⧸ H) → W)) :=
    (Finsupp.linearCombination ℂ fwdElem).comp (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap
  let fwdTensor : TensorProduct ℂ (MonoidAlgebra ℂ G) W →ₗ[ℂ] ((G ⧸ H) → W) :=
    TensorProduct.lift fwdAlg
  have hfwd_single : ∀ (x : G) (c : ℂ) (w : W),
      fwdTensor (MonoidAlgebra.single x c ⊗ₜ[ℂ] w) = c • fwdElem x w := by
    intro x c w
    change (Finsupp.linearCombination ℂ fwdElem
      (MonoidAlgebra.coeffLinearEquiv ℂ (MonoidAlgebra.single x c))) w = c • fwdElem x w
    have hcoeff : MonoidAlgebra.coeffLinearEquiv ℂ (MonoidAlgebra.single x c) = Finsupp.single x c := by
      ext y
      simp [Finsupp.single_apply]
    rw [hcoeff, Finsupp.linearCombination_single]
    rfl
  have hfwd_rel : ∀ h : H,
      fwdTensor ∘ₗ (Representation.tprod ((leftRegular ℂ G).comp H.subtype) ψ) h = fwdTensor := by
    intro h
    apply TensorProduct.ext
    apply MonoidAlgebra.lhom_ext'
    intro x
    apply LinearMap.ext_ring
    ext w q
    have hlhs : (fwdTensor ∘ₗ (Representation.tprod ((leftRegular ℂ G).comp H.subtype) ψ) h)
        (MonoidAlgebra.single x (1 : ℂ) ⊗ₜ[ℂ] w) q =
        fwdTensor (MonoidAlgebra.single ((h : G) * x) 1 ⊗ₜ[ℂ] ψ h w) q := by
      have hlr : (leftRegular ℂ G) (h : G) (MonoidAlgebra.single x (1 : ℂ)) =
          MonoidAlgebra.single ((h : G) * x) (1 : ℂ) :=
        Representation.ofMulAction_single (h : G) x (1 : ℂ)
      simp [Representation.tprod_apply, hlr]
    change (fwdTensor ∘ₗ (Representation.tprod ((leftRegular ℂ G).comp H.subtype) ψ) h)
        (MonoidAlgebra.single x (1 : ℂ) ⊗ₜ[ℂ] w) q =
      fwdTensor (MonoidAlgebra.single x (1 : ℂ) ⊗ₜ[ℂ] w) q
    rw [hlhs, hfwd_single, hfwd_single, one_smul, one_smul]
    have hcoset : ((((h : G) * x)⁻¹ : G) : G ⧸ H) = ((x⁻¹ : G) : G ⧸ H) := by
      rw [mul_inv_rev]
      exact Quotient.sound (show (QuotientGroup.leftRel H) (x⁻¹ * (h : G)⁻¹) x⁻¹ by
        rw [QuotientGroup.leftRel_apply]
        simp [mul_assoc])
    dsimp only [fwdElem, LinearMap.coe_mk, AddHom.coe_mk]
    by_cases hq : q = ((x⁻¹ : G) : G ⧸ H)
    · rw [if_pos (hq.trans hcoset.symm), if_pos hq, ← Module.End.mul_apply, ← map_mul]
      congr 2
      apply Subtype.ext
      simp [mul_inv_rev, mul_assoc]
    · rw [if_neg (fun h' => hq (h'.trans hcoset)), if_neg hq]
  let fwd : Representation.IndV H.subtype ψ →ₗ[ℂ] ((G ⧸ H) → W) :=
    Representation.Coinvariants.lift _ fwdTensor hfwd_rel
  have hfwd_mk : ∀ (x : G) (w : W),
      fwd (Representation.IndV.mk H.subtype ψ x w) = fwdElem x w := by
    intro x w
    change fwdTensor (MonoidAlgebra.single x 1 ⊗ₜ[ℂ] w) = fwdElem x w
    rw [hfwd_single, one_smul]
  let inv : ((G ⧸ H) → W) →ₗ[ℂ] Representation.IndV H.subtype ψ :=
    ∑ q : G ⧸ H, (Representation.IndV.mk H.subtype ψ (cosetOut H q)⁻¹).comp
      (LinearMap.proj q)
  have hleft : inv.comp fwd = LinearMap.id := by
    apply Representation.IndV.hom_ext
    intro x
    ext w
    change inv (fwd (Representation.IndV.mk H.subtype ψ x w)) =
      Representation.IndV.mk H.subtype ψ x w
    rw [hfwd_mk]
    have hinv_eval : inv (fwdElem x w) =
        ∑ q : G ⧸ H, Representation.IndV.mk H.subtype ψ (cosetOut H q)⁻¹ (fwdElem x w q) := by
      dsimp only [inv]
      rw [LinearMap.sum_apply]
      rfl
    rw [hinv_eval]
    have hsingle : ∑ q : G ⧸ H,
        Representation.IndV.mk H.subtype ψ (cosetOut H q)⁻¹ (fwdElem x w q) =
        Representation.IndV.mk H.subtype ψ (cosetOut H ((x⁻¹ : G) : G ⧸ H))⁻¹
          (ψ ⟨(cosetOut H ((x⁻¹ : G) : G ⧸ H))⁻¹ * x⁻¹, hα x⟩ w) := by
      rw [Finset.sum_eq_single ((x⁻¹ : G) : G ⧸ H)]
      · simp [fwdElem]
      · intro q _ hq
        simp [fwdElem, hq]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsingle]
    let h : H := ⟨(cosetOut H ((x⁻¹ : G) : G ⧸ H))⁻¹ * x⁻¹, hα x⟩
    have hx_eq : (cosetOut H ((x⁻¹ : G) : G ⧸ H))⁻¹ = (h : G) * x := by
      simp [h, mul_assoc]
    have hlr : (leftRegular ℂ G) (h : G) (MonoidAlgebra.single x (1 : ℂ)) =
        MonoidAlgebra.single ((h : G) * x) (1 : ℂ) :=
      Representation.ofMulAction_single (h : G) x (1 : ℂ)
    have hcoinv := Representation.Coinvariants.mk_self_apply
      (ρ := Representation.tprod ((leftRegular ℂ G).comp H.subtype) ψ) h
      (MonoidAlgebra.single x (1 : ℂ) ⊗ₜ[ℂ] w)
    simpa [Representation.IndV.mk, Representation.tprod_apply, hlr, hx_eq] using hcoinv
  have hright : fwd.comp inv = LinearMap.id := by
    refine LinearMap.ext fun f => funext fun q => ?_
    change fwd (inv f) q = f q
    have hinv_eval : inv f =
        ∑ q' : G ⧸ H, Representation.IndV.mk H.subtype ψ (cosetOut H q')⁻¹ (f q') := by
      dsimp only [inv]
      rw [LinearMap.sum_apply]
      rfl
    rw [hinv_eval, map_sum, Finset.sum_apply]
    simp_rw [hfwd_mk]
    rw [Finset.sum_eq_single q]
    · simp only [fwdElem, LinearMap.coe_mk, AddHom.coe_mk, inv_inv, cosetOut_eq, ite_true]
      have h2 : (⟨(cosetOut H q)⁻¹ * cosetOut H q, by simp⟩ : H) = 1 := by
        apply Subtype.ext; simp
      rw [h2, map_one, Module.End.one_apply]
    · intro q' _ hq'
      simp [fwdElem, cosetOut_eq, hq'.symm]
    · intro h; exact absurd (Finset.mem_univ _) h
  let le : Representation.IndV H.subtype ψ ≃ₗ[ℂ] ((G ⧸ H) → W) :=
    LinearEquiv.ofLinearMap fwd inv hright hleft
  refine Representation.Equiv.mk le ?_
  intro g
  apply Representation.IndV.hom_ext
  intro x
  ext w q
  change fwd (((Representation.ind H.subtype ψ) g) (Representation.IndV.mk H.subtype ψ x w)) q =
    indModel H ψ g (fwd (Representation.IndV.mk H.subtype ψ x w)) q
  have hact : ((Representation.ind H.subtype ψ) g) (Representation.IndV.mk H.subtype ψ x w) =
      Representation.IndV.mk H.subtype ψ (x * g⁻¹) w := by
    simp [Representation.ind, Representation.IndV.mk]
  rw [hact, hfwd_mk, hfwd_mk, indModel_apply]
  dsimp only [fwdElem, LinearMap.coe_mk, AddHom.coe_mk]
  have hiff : q = (((x * g⁻¹)⁻¹ : G) : G ⧸ H) ↔ g⁻¹ • q = ((x⁻¹ : G) : G ⧸ H) := by
    have hcos : (((x * g⁻¹)⁻¹ : G) : G ⧸ H) = g • ((x⁻¹ : G) : G ⧸ H) := by
      rw [mul_inv_rev, inv_inv]; rfl
    rw [hcos]
    exact ⟨fun h => by rw [h, inv_smul_smul], fun h => by rw [← h, smul_inv_smul]⟩
  by_cases hq1 : q = (((x * g⁻¹)⁻¹ : G) : G ⧸ H)
  · have hq2 : g⁻¹ • q = ((x⁻¹ : G) : G ⧸ H) := hiff.mp hq1
    rw [if_pos hq1, if_pos hq2, ← Module.End.mul_apply, ← map_mul]
    congr 2
    apply Subtype.ext
    simp only [Subgroup.coe_mul, mul_inv_rev, inv_inv, mul_assoc]
    rw [hq2, hq1]
    have hq1' : ((g * x⁻¹ : G) : G ⧸ H) = (((x * g⁻¹)⁻¹ : G) : G ⧸ H) := by
      simp [mul_inv_rev]
    rw [← hq1']
    group
  · have hq2 : g⁻¹ • q ≠ ((x⁻¹ : G) : G ⧸ H) := fun h => hq1 (hiff.mpr h)
    rw [if_neg hq1, if_neg hq2, map_zero]

/-- Finite-dimensionality of `Representation.IndV H.subtype ψ` for finite `G` and
finite-dimensional `W`. -/
instance finiteDimensional_indV (H : Subgroup G) {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (ψ : Representation ℂ H W) :
    FiniteDimensional ℂ (Representation.IndV H.subtype ψ) :=
  (indEquivIndModel H ψ).toLinearEquiv.symm.finiteDimensional

/-- Monodromy element `x⁻¹ * g ^ |O| * x ∈ H` associated to a `⟨g⟩`-orbit `O` on `G ⧸ H`
and a representative `x : G` with `(x : G ⧸ H) ∈ O`. -/
def orbitMonodromyOfRep (H : Subgroup G) (g : G) (O : CycleOrbits g (G ⧸ H))
    (x : G) (hx : Quotient.mk (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H)) (x : G ⧸ H) = O) :
    H :=
  ⟨x⁻¹ * g ^ orbitSize g O * x, by
    have hfix := (orbit_cycle_equiv g O (x : G ⧸ H) hx).1
    have hcos : ((g ^ orbitSize g O * x : G) : G ⧸ H) = (x : G ⧸ H) := hfix
    rw [mul_assoc]
    exact QuotientGroup.leftRel_apply.mp (Quotient.exact hcos.symm)⟩

/-- Canonical monodromy element for a `⟨g⟩`-orbit `O` on `G ⧸ H`. -/
def orbitMonodromy (H : Subgroup G) (g : G) (O : CycleOrbits g (G ⧸ H)) : H :=
  orbitMonodromyOfRep H g O (cosetOut H (Quotient.out O))
    (by rw [cosetOut_eq H]; exact Quotient.out_eq O)

/-- Independence of `artinLocalFactor ψ (orbitMonodromyOfRep ...) (T ^ |O|)` on the choice of
orbit representative `x : G`. -/
theorem artinLocalFactor_orbitMonodromyOfRep_eq (H : Subgroup G) {W : Type*}
    [AddCommGroup W] [Module ℂ W] (ψ : Representation ℂ H W) (g : G)
    (O : CycleOrbits g (G ⧸ H)) (x₁ x₂ : G)
    (hx₁ : Quotient.mk (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H)) (x₁ : G ⧸ H) = O)
    (hx₂ : Quotient.mk (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H)) (x₂ : G ⧸ H) = O)
    (T : ℂ) :
    artinLocalFactor ψ (orbitMonodromyOfRep H g O x₁ hx₁) T =
      artinLocalFactor ψ (orbitMonodromyOfRep H g O x₂ hx₂) T := by
  have hrel : MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H) (x₂ : G ⧸ H) (x₁ : G ⧸ H) :=
    Quotient.exact (hx₂.trans hx₁.symm)
  obtain ⟨⟨a, ha⟩, hax⟩ := hrel
  rw [Subgroup.mem_zpowers_iff] at ha
  obtain ⟨k, rfl⟩ := ha
  have hcos : ((g ^ k * x₁ : G) : G ⧸ H) = (x₂ : G ⧸ H) := hax
  let h : H := ⟨x₂⁻¹ * (g ^ k * x₁),
    QuotientGroup.leftRel_apply.mp (Quotient.exact hcos.symm)⟩
  have hconj : orbitMonodromyOfRep H g O x₂ hx₂ =
      h * orbitMonodromyOfRep H g O x₁ hx₁ * h⁻¹ := by
    apply Subtype.ext
    simp only [orbitMonodromyOfRep, h, Subgroup.coe_mul, Subgroup.coe_inv]
    have hcomm : g ^ k * g ^ orbitSize g O * (g ^ k)⁻¹ = g ^ orbitSize g O := by
      rw [← zpow_natCast, ← zpow_add, ← zpow_neg, ← zpow_add]
      congr 1; ring
    calc
      x₂⁻¹ * g ^ orbitSize g O * x₂
          = x₂⁻¹ * (g ^ k * g ^ orbitSize g O * (g ^ k)⁻¹) * x₂ := by rw [hcomm]
      _ = x₂⁻¹ * (g ^ k * x₁) * (x₁⁻¹ * g ^ orbitSize g O * x₁) * (x₂⁻¹ * (g ^ k * x₁))⁻¹ := by
          group
  rw [hconj, artinLocalFactor_conj]

/-- **Law 3 — ARTIN INDUCTIVITY (`artinLocalPoly_ind`)**:
For ANY finite group `G`, ANY subgroup `H ≤ G`, and ANY finite-dimensional complex representation
`ψ` of `H`, the local Artin polynomial of `Ind_H^G ψ` at `g ∈ G` equals the product over
`⟨g⟩`-orbits `O` on `G ⧸ H` of `artinLocalPoly ψ (orbitMonodromy H g O) (T ^ orbitSize g O)`. -/
theorem artinLocalPoly_ind (H : Subgroup G) {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (ψ : Representation ℂ H W) (g : G) (T : ℂ) :
    artinLocalPoly (Representation.ind H.subtype ψ) g T =
      ∏ O : CycleOrbits g (G ⧸ H),
        artinLocalPoly ψ (orbitMonodromy H g O) (T ^ orbitSize g O) := by
  rw [artinLocalPoly_iso (indEquivIndModel H ψ) g T]
  let xO : CycleOrbits g (G ⧸ H) → G := fun O => cosetOut H (Quotient.out O)
  have hxO : ∀ O, Quotient.mk (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H)) (xO O : G ⧸ H) = O :=
    fun O => by dsimp only [xO]; rw [cosetOut_eq H]; exact Quotient.out_eq O
  let idxEquiv : (Σ O : CycleOrbits g (G ⧸ H), Fin (orbitSize g O)) ≃ (G ⧸ H) :=
    Equiv.ofBijective
      (fun p => (g ^ p.2.1) • (xO p.1 : G ⧸ H))
      ⟨by
        rintro ⟨O₁, j₁⟩ ⟨O₂, j₂⟩ heq
        dsimp only at heq
        have hO : O₁ = O₂ := by
          have h1 : Quotient.mk (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H))
              ((g ^ j₁.1) • (xO O₁ : G ⧸ H)) = O₁ :=
            (Quotient.sound (show MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H)
              ((g ^ j₁.1) • (xO O₁ : G ⧸ H)) (xO O₁ : G ⧸ H) from
              ⟨⟨g ^ j₁.1, Subgroup.npow_mem_zpowers g j₁.1⟩, rfl⟩)).trans (hxO O₁)
          have h2 : Quotient.mk (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H))
              ((g ^ j₂.1) • (xO O₂ : G ⧸ H)) = O₂ :=
            (Quotient.sound (show MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H)
              ((g ^ j₂.1) • (xO O₂ : G ⧸ H)) (xO O₂ : G ⧸ H) from
              ⟨⟨g ^ j₂.1, Subgroup.npow_mem_zpowers g j₂.1⟩, rfl⟩)).trans (hxO O₂)
          rw [← h1, heq, h2]
        subst hO
        have hinj := (orbit_cycle_equiv g O₁ (xO O₁ : G ⧸ H) (hxO O₁)).2.1
        have hj : j₁ = j₂ := hinj (Subtype.ext heq)
        subst hj
        rfl,
       by
        intro q
        let O : CycleOrbits g (G ⧸ H) :=
          Quotient.mk (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H)) q
        have hsurj := (orbit_cycle_equiv g O (xO O : G ⧸ H) (hxO O)).2.2
        obtain ⟨j, hj⟩ := hsurj ⟨q, rfl⟩
        exact ⟨⟨O, j⟩, congr_arg Subtype.val hj⟩⟩
  have hc_mem : ∀ (O : CycleOrbits g (G ⧸ H)) (j : Fin (orbitSize g O)),
      (cosetOut H ((g ^ j.1) • (xO O : G ⧸ H)))⁻¹ * (g ^ j.1 * xO O) ∈ H := by
    intro O j
    have hcos : ((g ^ j.1 * xO O : G) : G ⧸ H) =
        ((cosetOut H ((g ^ j.1) • (xO O : G ⧸ H)) : G) : G ⧸ H) := by
      rw [cosetOut_eq H]; rfl
    exact QuotientGroup.leftRel_apply.mp (Quotient.exact hcos.symm)
  let cH : (O : CycleOrbits g (G ⧸ H)) → Fin (orbitSize g O) → H :=
    fun O j => ⟨(cosetOut H ((g ^ j.1) • (xO O : G ⧸ H)))⁻¹ * (g ^ j.1 * xO O), hc_mem O j⟩
  let twistTo : (∀ O : CycleOrbits g (G ⧸ H), Fin (orbitSize g O) → W) →ₗ[ℂ] ((G ⧸ H) → W) :=
    { toFun := fun u q =>
        let p := idxEquiv.symm q
        ψ (cH p.1 p.2) (u p.1 p.2)
      map_add' := fun u₁ u₂ => by ext q; simp
      map_smul' := fun r u => by ext q; simp }
  let twistFrom : ((G ⧸ H) → W) →ₗ[ℂ] (∀ O : CycleOrbits g (G ⧸ H), Fin (orbitSize g O) → W) :=
    { toFun := fun f O j =>
        ψ (cH O j)⁻¹ (f (idxEquiv ⟨O, j⟩))
      map_add' := fun f₁ f₂ => by ext O j; simp
      map_smul' := fun r f => by ext O j; simp }
  let twist : (∀ O : CycleOrbits g (G ⧸ H), Fin (orbitSize g O) → W) ≃ₗ[ℂ] ((G ⧸ H) → W) :=
    LinearEquiv.ofLinearMap twistTo twistFrom
      (LinearMap.ext fun f => funext fun q => by
        change twistTo (twistFrom f) q = f q
        dsimp only [twistTo, twistFrom, LinearMap.coe_mk, AddHom.coe_mk]
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
        have hq : idxEquiv ⟨(idxEquiv.symm q).1, (idxEquiv.symm q).2⟩ = q :=
          idxEquiv.apply_symm_apply q
        rw [hq])
      (LinearMap.ext fun u => funext fun O => funext fun j => by
        change twistFrom (twistTo u) O j = u O j
        dsimp only [twistTo, twistFrom, LinearMap.coe_mk, AddHom.coe_mk]
        have hsymm : idxEquiv.symm (idxEquiv ⟨O, j⟩) = ⟨O, j⟩ := idxEquiv.symm_apply_apply ⟨O, j⟩
        rw [hsymm]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply])
  unfold artinLocalPoly
  have hdet_eq : LinearMap.det ((1 : Module.End ℂ ((G ⧸ H) → W)) - T • indModel H ψ g) =
      LinearMap.det (twist.symm.toLinearMap ∘ₗ
        ((1 : Module.End ℂ ((G ⧸ H) → W)) - T • indModel H ψ g) ∘ₗ twist.toLinearMap) :=
    (LinearMap.det_conj _ twist.symm).symm
  rw [hdet_eq]
  have heig : ∀ O : CycleOrbits g (G ⧸ H),
      ∃ (b : Module.Basis (Fin (Module.finrank ℂ W)) ℂ W)
        (ev : Fin (Module.finrank ℂ W) → ℂ),
        ∀ k, ψ (orbitMonodromy H g O) (b k) = ev k • b k := by
    intro O
    obtain ⟨b, ev, hev, _, _⟩ := exists_eigenbasis_rep ψ (orbitMonodromy H g O)
    exact ⟨b, ev, hev⟩
  choose bW evW hevW using heig
  let BOrb : ∀ O : CycleOrbits g (G ⧸ H),
      Module.Basis (Fin (Module.finrank ℂ W) × Fin (orbitSize g O)) ℂ (Fin (orbitSize g O) → W) :=
    fun O => (Pi.basis (fun _ : Fin (orbitSize g O) => bW O)).reindex
      ((Equiv.sigmaEquivProd _ _).trans (Equiv.prodComm _ _))
  let BAll : Module.Basis (Σ O : CycleOrbits g (G ⧸ H), Fin (Module.finrank ℂ W) × Fin (orbitSize g O))
      ℂ (∀ O : CycleOrbits g (G ⧸ H), Fin (orbitSize g O) → W) :=
    Pi.basis BOrb
  have hconj_act : ∀ (u : ∀ O : CycleOrbits g (G ⧸ H), Fin (orbitSize g O) → W)
      (O : CycleOrbits g (G ⧸ H)) (j : Fin (orbitSize g O)),
      twist.symm (indModel H ψ g (twist u)) O j =
        if hj0 : j.1 = 0 then
          ψ (orbitMonodromy H g O) (u O ⟨orbitSize g O - 1, Nat.sub_lt (orbitSize_pos g O) Nat.one_pos⟩)
        else
          u O ⟨j.1 - 1, by omega⟩ := by
    intro u O j
    change twistFrom (indModel H ψ g (twistTo u)) O j = _
    dsimp only [twistFrom, twistTo, LinearMap.coe_mk, AddHom.coe_mk]
    rw [indModel_apply]
    have hidx : idxEquiv ⟨O, j⟩ = (g ^ j.1) • (xO O : G ⧸ H) := rfl
    rw [hidx]
    split_ifs with hj0
    · let jlast : Fin (orbitSize g O) :=
        ⟨orbitSize g O - 1, Nat.sub_lt (orbitSize_pos g O) Nat.one_pos⟩
      have hg_prev : g⁻¹ • ((g ^ j.1) • (xO O : G ⧸ H)) = idxEquiv ⟨O, jlast⟩ := by
        have hfix := (orbit_cycle_equiv g O (xO O : G ⧸ H) (hxO O)).1
        have hd : 1 ≤ orbitSize g O := orbitSize_pos g O
        rw [hj0, pow_zero, one_smul]
        change g⁻¹ • (xO O : G ⧸ H) = (g ^ (orbitSize g O - 1)) • (xO O : G ⧸ H)
        calc g⁻¹ • (xO O : G ⧸ H)
            = g⁻¹ • ((g ^ orbitSize g O) • (xO O : G ⧸ H)) := by rw [hfix]
        _ = (g⁻¹ * g ^ orbitSize g O) • (xO O : G ⧸ H) := by rw [mul_smul]
        _ = (g ^ (orbitSize g O - 1)) • (xO O : G ⧸ H) := by
            congr 1
            have : g ^ orbitSize g O = g * g ^ (orbitSize g O - 1) := by
              rw [← pow_succ', Nat.sub_add_cancel hd]
            rw [this, inv_mul_cancel_left]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      have hsymm : idxEquiv.symm (g⁻¹ • ((g ^ j.1) • (xO O : G ⧸ H))) = ⟨O, jlast⟩ := by
        rw [hg_prev, Equiv.symm_apply_apply]
      have hu_eq : u (idxEquiv.symm (g⁻¹ • ((g ^ j.1) • (xO O : G ⧸ H)))).1
          (idxEquiv.symm (g⁻¹ • ((g ^ j.1) • (xO O : G ⧸ H)))).2 = u O jlast := by
        rw [hsymm]
      rw [hu_eq]
      congr 2
      apply Subtype.ext
      have hd : 1 ≤ orbitSize g O := orbitSize_pos g O
      have hval_c : ((cH (idxEquiv.symm (g⁻¹ • ((g ^ j.1) • (xO O : G ⧸ H)))).1
          (idxEquiv.symm (g⁻¹ • ((g ^ j.1) • (xO O : G ⧸ H)))).2 : H) : G) =
          ((cH O jlast : H) : G) := by
        rw [hsymm]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hval_c, hg_prev]
      simp only [cH, orbitMonodromy, orbitMonodromyOfRep, xO, jlast, hj0, pow_zero, one_mul,
        one_smul]
      have hpow : g * g ^ (orbitSize g O - 1) = g ^ orbitSize g O := by
        rw [← pow_succ', Nat.sub_add_cancel hd]
      have hqeq : cosetOut H (idxEquiv ⟨O, jlast⟩) =
          cosetOut H ((g ^ (orbitSize g O - 1)) • ((cosetOut H (Quotient.out O) : G) : G ⧸ H)) := rfl
      rw [hqeq]
      calc
        ((cosetOut H ((cosetOut H (Quotient.out O) : G) : G ⧸ H))⁻¹ * cosetOut H (Quotient.out O))⁻¹ *
          ((cosetOut H ((cosetOut H (Quotient.out O) : G) : G ⧸ H))⁻¹ * g *
            cosetOut H ((g ^ (orbitSize g O - 1)) • ((cosetOut H (Quotient.out O) : G) : G ⧸ H))) *
          ((cosetOut H ((g ^ (orbitSize g O - 1)) • ((cosetOut H (Quotient.out O) : G) : G ⧸ H)))⁻¹ *
            (g ^ (orbitSize g O - 1) * cosetOut H (Quotient.out O)))
            = (cosetOut H (Quotient.out O))⁻¹ * (g * g ^ (orbitSize g O - 1)) *
                cosetOut H (Quotient.out O) := by group
        _ = (cosetOut H (Quotient.out O))⁻¹ * g ^ orbitSize g O *
              cosetOut H (Quotient.out O) := by rw [hpow]
    · let jprev : Fin (orbitSize g O) := ⟨j.1 - 1, by omega⟩
      have hg_prev : g⁻¹ • ((g ^ j.1) • (xO O : G ⧸ H)) = idxEquiv ⟨O, jprev⟩ := by
        change g⁻¹ • ((g ^ j.1) • (xO O : G ⧸ H)) = (g ^ (j.1 - 1)) • (xO O : G ⧸ H)
        rw [← mul_smul]
        congr 1
        have hj1 : 1 ≤ j.1 := Nat.pos_of_ne_zero hj0
        have : g ^ j.1 = g * g ^ (j.1 - 1) := by rw [← pow_succ', Nat.sub_add_cancel hj1]
        rw [this, inv_mul_cancel_left]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      have hsymm : idxEquiv.symm (g⁻¹ • ((g ^ j.1) • (xO O : G ⧸ H))) = ⟨O, jprev⟩ := by
        rw [hg_prev, Equiv.symm_apply_apply]
      have hu_eq : u (idxEquiv.symm (g⁻¹ • ((g ^ j.1) • (xO O : G ⧸ H)))).1
          (idxEquiv.symm (g⁻¹ • ((g ^ j.1) • (xO O : G ⧸ H)))).2 = u O jprev := by
        rw [hsymm]
      rw [hu_eq]
      have hid : ((cH O j)⁻¹ *
          ⟨(cosetOut H ((g ^ j.1) • (xO O : G ⧸ H)))⁻¹ * g *
            cosetOut H (g⁻¹ • ((g ^ j.1) • (xO O : G ⧸ H))),
            by
              have h1 : ((cosetOut H ((g ^ j.1) • (xO O : G ⧸ H)) : G) : G ⧸ H) =
                  (g ^ j.1) • (xO O : G ⧸ H) := cosetOut_eq H _
              have h2 : ((cosetOut H (g⁻¹ • ((g ^ j.1) • (xO O : G ⧸ H))) : G) : G ⧸ H) =
                  g⁻¹ • ((g ^ j.1) • (xO O : G ⧸ H)) := cosetOut_eq H _
              have h3 : ((g * cosetOut H (g⁻¹ • ((g ^ j.1) • (xO O : G ⧸ H))) : G) : G ⧸ H) =
                  ((cosetOut H ((g ^ j.1) • (xO O : G ⧸ H)) : G) : G ⧸ H) := by
                change g • ((cosetOut H (g⁻¹ • ((g ^ j.1) • (xO O : G ⧸ H))) : G) : G ⧸ H) = _
                rw [h2, h1, smul_inv_smul]
              rw [mul_assoc]
              exact QuotientGroup.leftRel_apply.mp (Quotient.exact h3.symm)⟩ *
          cH (idxEquiv.symm (g⁻¹ • ((g ^ j.1) • (xO O : G ⧸ H)))).1
            (idxEquiv.symm (g⁻¹ • ((g ^ j.1) • (xO O : G ⧸ H)))).2) = 1 := by
        apply Subtype.ext
        have hj1 : 1 ≤ j.1 := Nat.pos_of_ne_zero hj0
        have hpow : g * g ^ (j.1 - 1) = g ^ j.1 := by rw [← pow_succ', Nat.sub_add_cancel hj1]
        have hval_c : ((cH (idxEquiv.symm (g⁻¹ • ((g ^ j.1) • (xO O : G ⧸ H)))).1
            (idxEquiv.symm (g⁻¹ • ((g ^ j.1) • (xO O : G ⧸ H)))).2 : H) : G) =
            ((cH O jprev : H) : G) := by
          rw [hsymm]
        have hqeq : cosetOut H (idxEquiv ⟨O, jprev⟩) =
            cosetOut H ((g ^ (j.1 - 1)) • (xO O : G ⧸ H)) := rfl
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one, hval_c, hg_prev, hqeq]
        simp only [cH, jprev]
        calc
          ((cosetOut H ((g ^ j.1) • (xO O : G ⧸ H)))⁻¹ * (g ^ j.1 * xO O))⁻¹ *
            ((cosetOut H ((g ^ j.1) • (xO O : G ⧸ H)))⁻¹ * g *
              cosetOut H ((g ^ (j.1 - 1)) • (xO O : G ⧸ H))) *
            ((cosetOut H ((g ^ (j.1 - 1)) • (xO O : G ⧸ H)))⁻¹ * (g ^ (j.1 - 1) * xO O))
              = (xO O)⁻¹ * (g ^ j.1)⁻¹ * (g * g ^ (j.1 - 1)) * xO O := by group
          _ = (xO O)⁻¹ * (g ^ j.1)⁻¹ * g ^ j.1 * xO O := by rw [hpow]
          _ = 1 := by group
      rw [hid, map_one, Module.End.one_apply]
  let eBlock : (Σ p : (Σ O : CycleOrbits g (G ⧸ H), Fin (Module.finrank ℂ W)), Fin (orbitSize g p.1)) ≃
      (Σ O : CycleOrbits g (G ⧸ H), Fin (Module.finrank ℂ W) × Fin (orbitSize g O)) :=
    { toFun := fun ⟨⟨O, k⟩, j⟩ => ⟨O, k, j⟩
      invFun := fun ⟨O, k, j⟩ => ⟨⟨O, k⟩, j⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, _, _⟩ => rfl }
  let B := BAll.reindex eBlock.symm
  rw [← LinearMap.det_toMatrix B]
  let blocks : ∀ p : (Σ O : CycleOrbits g (G ⧸ H), Fin (Module.finrank ℂ W)),
      Matrix (Fin (orbitSize g p.1)) (Fin (orbitSize g p.1)) ℂ :=
    fun p => (1 : Matrix (Fin (orbitSize g p.1)) (Fin (orbitSize g p.1)) ℂ) -
      T • cyclicShiftMatrix (orbitSize g p.1) (evW p.1 p.2)
  have hmat : LinearMap.toMatrix B B
      (twist.symm.toLinearMap ∘ₗ
        ((1 : Module.End ℂ ((G ⧸ H) → W)) - T • indModel H ψ g) ∘ₗ twist.toLinearMap) =
      Matrix.blockDiagonal' blocks := by
    ext ⟨⟨O₁, k₁⟩, j₁⟩ ⟨⟨O₂, k₂⟩, j₂⟩
    dsimp only at j₁ j₂
    rw [LinearMap.toMatrix_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearMap.sub_apply, Module.End.one_apply, LinearMap.smul_apply]
    simp only [LinearEquiv.coe_coe, map_sub, map_smul, LinearEquiv.symm_apply_apply,
      Finsupp.coe_sub, Finsupp.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have hB_eq : ∀ (O : CycleOrbits g (G ⧸ H)) (k : Fin (Module.finrank ℂ W)) (j : Fin (orbitSize g O)),
        B ⟨⟨O, k⟩, j⟩ = Pi.single O (Pi.single j (bW O k)) := by
      intro O k j
      simp [B, BAll, BOrb, eBlock, Pi.basis_apply]
    have hrepr_single : ∀ (O : CycleOrbits g (G ⧸ H)) (j : Fin (orbitSize g O)) (w : W),
        B.repr (Pi.single O (Pi.single j w)) ⟨⟨O₁, k₁⟩, j₁⟩ =
          if hO : O₁ = O then
            if j₁ = hO ▸ j then (bW O).repr w k₁ else 0
          else 0 := by
      intro O j w
      change (BAll.repr (Pi.single O (Pi.single j w))) ⟨O₁, k₁, j₁⟩ = _
      rw [Pi.basis_repr]
      by_cases hO : O₁ = O
      · subst hO
        simp only [dite_true, Pi.single_eq_same]
        change ((Pi.basis (fun _ : Fin (orbitSize g O₁) => bW O₁)).repr (Pi.single j w)) ⟨j₁, k₁⟩ = _
        rw [Pi.basis_repr]
        by_cases hJ : j₁ = j
        · subst hJ
          simp
        · simp [hJ]
      · simp [hO]
    have hterm1 : B.repr (B ⟨⟨O₂, k₂⟩, j₂⟩) ⟨⟨O₁, k₁⟩, j₁⟩ =
        if (⟨⟨O₁, k₁⟩, j₁⟩ : Σ p : (Σ O : CycleOrbits g (G ⧸ H), Fin (Module.finrank ℂ W)),
            Fin (orbitSize g p.1)) = ⟨⟨O₂, k₂⟩, j₂⟩ then 1 else 0 := by
      rw [B.repr_self, Finsupp.single_apply]
      by_cases h : (⟨⟨O₂, k₂⟩, j₂⟩ : Σ p : (Σ O : CycleOrbits g (G ⧸ H), Fin (Module.finrank ℂ W)),
          Fin (orbitSize g p.1)) = ⟨⟨O₁, k₁⟩, j₁⟩
      · simp [h]
      · simp [h, Ne.symm h]
    have hind_basis : twist.symm (indModel H ψ g (twist (B ⟨⟨O₂, k₂⟩, j₂⟩))) =
        if hj : j₂.1 + 1 < orbitSize g O₂ then
          Pi.single O₂ (Pi.single ⟨j₂.1 + 1, hj⟩ (bW O₂ k₂))
        else
          Pi.single O₂ (Pi.single ⟨0, orbitSize_pos g O₂⟩ (evW O₂ k₂ • bW O₂ k₂)) := by
      ext O j
      rw [hconj_act, hB_eq O₂ k₂ j₂]
      by_cases hj : j₂.1 + 1 < orbitSize g O₂
      · rw [dif_pos hj]
        by_cases hO : O = O₂
        · subst hO
          simp only [Pi.single_eq_same]
          by_cases hj0 : j.1 = 0
          · rw [dif_pos hj0]
            have hneq : (⟨orbitSize g O - 1, Nat.sub_lt (orbitSize_pos g O) Nat.one_pos⟩ :
                Fin (orbitSize g O)) ≠ j₂ := by
              intro h; have := congr_arg Fin.val h; dsimp at this; omega
            have hneq2 : j ≠ ⟨j₂.1 + 1, hj⟩ := by
              intro h; have := congr_arg Fin.val h; dsimp at this; omega
            rw [Pi.single_eq_of_ne hneq, map_zero, Pi.single_eq_of_ne hneq2]
          · rw [dif_neg hj0]
            by_cases hjeq : j = ⟨j₂.1 + 1, hj⟩
            · subst hjeq
              have hprev : (⟨j₂.1 + 1 - 1, by omega⟩ : Fin (orbitSize g O)) = j₂ := by ext; simp
              rw [hprev, Pi.single_eq_same, Pi.single_eq_same]
            · have hne2 : (⟨j.1 - 1, by omega⟩ : Fin (orbitSize g O)) ≠ j₂ := by
                intro h; apply hjeq; ext; have := congr_arg Fin.val h; dsimp at this ⊢; omega
              rw [Pi.single_eq_of_ne hne2, Pi.single_eq_of_ne hjeq]
        · rw [Pi.single_eq_of_ne hO, Pi.single_eq_of_ne hO]
          split_ifs <;> simp
      · rw [dif_neg hj]
        have hj2_lt : j₂.1 < orbitSize g O₂ := j₂.2
        have hjlast : j₂.1 = orbitSize g O₂ - 1 := by omega
        by_cases hO : O = O₂
        · subst hO
          simp only [Pi.single_eq_same]
          by_cases hj0 : j.1 = 0
          · rw [dif_pos hj0]
            have heq1 : (⟨orbitSize g O - 1, Nat.sub_lt (orbitSize_pos g O) Nat.one_pos⟩ :
                Fin (orbitSize g O)) = j₂ := by ext; exact hjlast.symm
            have heq2 : j = ⟨0, orbitSize_pos g O⟩ := by ext; exact hj0
            rw [heq1, heq2, Pi.single_eq_same, Pi.single_eq_same, hevW]
          · rw [dif_neg hj0]
            have hne1 : (⟨j.1 - 1, by omega⟩ : Fin (orbitSize g O)) ≠ j₂ := by
              intro h; have := congr_arg Fin.val h; dsimp at this; omega
            have hne2 : j ≠ ⟨0, orbitSize_pos g O⟩ := fun h => hj0 (congr_arg Fin.val h)
            rw [Pi.single_eq_of_ne hne1, Pi.single_eq_of_ne hne2]
        · rw [Pi.single_eq_of_ne hO, Pi.single_eq_of_ne hO]
          split_ifs <;> simp
    rw [hterm1, hind_basis]
    by_cases hO : O₁ = O₂
    · subst hO
      by_cases hk : k₁ = k₂
      · subst hk
        have hblock : Matrix.blockDiagonal' blocks ⟨⟨O₁, k₁⟩, j₁⟩ ⟨⟨O₁, k₁⟩, j₂⟩ =
            blocks ⟨O₁, k₁⟩ j₁ j₂ := by
          simp [Matrix.blockDiagonal'_apply]
        rw [hblock]
        simp only [blocks, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
          cyclicShiftMatrix]
        have h1 : (if (⟨⟨O₁, k₁⟩, j₁⟩ : Σ p : (Σ O : CycleOrbits g (G ⧸ H),
              Fin (Module.finrank ℂ W)), Fin (orbitSize g p.1)) = ⟨⟨O₁, k₁⟩, j₂⟩ then (1 : ℂ) else 0) =
            if j₁ = j₂ then 1 else 0 := by
          by_cases h : j₁ = j₂ <;> simp [h]
        rw [h1]
        congr 1
        congr 1
        by_cases hj_lt : j₂.1 + 1 < orbitSize g O₁
        · rw [dif_pos hj_lt, hrepr_single]
          simp only [dite_true]
          by_cases hstep : j₂.1 + 1 = j₁.1
          · have hjeq : j₁ = ⟨j₂.1 + 1, hj_lt⟩ := by ext; exact hstep.symm
            rw [if_pos hjeq, if_pos hstep, (bW O₁).repr_self, Finsupp.single_eq_same]
          · have hjne : j₁ ≠ ⟨j₂.1 + 1, hj_lt⟩ := fun h => hstep (congr_arg Fin.val h).symm
            have hne_end : j₂.1 + 1 ≠ orbitSize g O₁ := by omega
            rw [if_neg hjne, if_neg hstep, if_neg (by intro h; exact hne_end h.2)]
        · rw [dif_neg hj_lt, hrepr_single]
          simp only [dite_true]
          have hj1_lt : j₁.1 < orbitSize g O₁ := j₁.2
          have hj2_lt : j₂.1 < orbitSize g O₁ := j₂.2
          have hstep_ne : j₂.1 + 1 ≠ j₁.1 := by omega
          have hend : j₂.1 + 1 = orbitSize g O₁ := by omega
          by_cases hj10 : j₁.1 = 0
          · have hjeq : j₁ = ⟨0, orbitSize_pos g O₁⟩ := by ext; exact hj10
            rw [if_pos hjeq, if_neg hstep_ne, if_pos ⟨hj10, hend⟩, map_smul, (bW O₁).repr_self]
            simp
          · have hjne : j₁ ≠ ⟨0, orbitSize_pos g O₁⟩ := fun h => hj10 (congr_arg Fin.val h)
            rw [if_neg hjne, if_neg hstep_ne, if_neg (by intro h; exact hj10 h.1)]
      · have hpne : (⟨O₁, k₁⟩ : Σ O : CycleOrbits g (G ⧸ H), Fin (Module.finrank ℂ W)) ≠
            ⟨O₁, k₂⟩ := by
          intro h; apply hk; simpa using h
        rw [Matrix.blockDiagonal'_apply_ne _ _ _ hpne]
        have hne_all : (⟨⟨O₁, k₁⟩, j₁⟩ : Σ p : (Σ O : CycleOrbits g (G ⧸ H),
              Fin (Module.finrank ℂ W)), Fin (orbitSize g p.1)) ≠ ⟨⟨O₁, k₂⟩, j₂⟩ := by
          intro h; exact hk (by simpa using h : k₁ = k₂ ∧ j₁ = j₂).1
        rw [if_neg hne_all, zero_sub, neg_eq_zero]
        by_cases hj_lt : j₂.1 + 1 < orbitSize g O₁
        · rw [dif_pos hj_lt, hrepr_single]
          simp only [dite_true]
          split_ifs
          · rw [(bW O₁).repr_self, Finsupp.single_eq_of_ne hk, mul_zero]
          · rw [mul_zero]
        · rw [dif_neg hj_lt, hrepr_single]
          simp only [dite_true]
          split_ifs
          · rw [map_smul, (bW O₁).repr_self, Finsupp.coe_smul, Pi.smul_apply,
              Finsupp.single_eq_of_ne hk, smul_zero, mul_zero]
          · rw [mul_zero]
    · have hpne : (⟨O₁, k₁⟩ : Σ O : CycleOrbits g (G ⧸ H), Fin (Module.finrank ℂ W)) ≠
          ⟨O₂, k₂⟩ := by
        intro h; exact hO (congr_arg Sigma.fst h)
      rw [Matrix.blockDiagonal'_apply_ne _ _ _ hpne]
      have hne_all : (⟨⟨O₁, k₁⟩, j₁⟩ : Σ p : (Σ O : CycleOrbits g (G ⧸ H),
            Fin (Module.finrank ℂ W)), Fin (orbitSize g p.1)) ≠ ⟨⟨O₂, k₂⟩, j₂⟩ := by
        intro h; exact hO (congr_arg (fun x => x.1.1) h)
      rw [if_neg hne_all, zero_sub, neg_eq_zero]
      by_cases hj_lt : j₂.1 + 1 < orbitSize g O₂
      · rw [dif_pos hj_lt, hrepr_single, dif_neg hO, mul_zero]
      · rw [dif_neg hj_lt, hrepr_single, dif_neg hO, mul_zero]
  rw [hmat, det_blockDiagonal', Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro O _
  change ∏ k : Fin (Module.finrank ℂ W), (blocks ⟨O, k⟩).det =
    artinLocalPoly ψ (orbitMonodromy H g O) (T ^ orbitSize g O)
  rw [artinLocalPoly_eq_prod_of_eigenbasis ψ (orbitMonodromy H g O) (bW O) (evW O) (hevW O)]
  apply Finset.prod_congr rfl
  intro k _
  exact det_one_sub_smul_cyclicShiftMatrix (orbitSize g O) (orbitSize_pos g O) (evW O k) T

/-- **Law 3 — ARTIN INDUCTIVITY (`artinLocalFactor_ind`)**:
`artinLocalFactor (Ind_H^G ψ) g T = ∏ O ∈ orbits(⟨g⟩ on G ⧸ H), artinLocalFactor ψ (orbitMonodromy H g O) (T ^ |O|)`. -/
theorem artinLocalFactor_ind (H : Subgroup G) {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (ψ : Representation ℂ H W) (g : G) (T : ℂ) :
    artinLocalFactor (Representation.ind H.subtype ψ) g T =
      ∏ O : CycleOrbits g (G ⧸ H),
        artinLocalFactor ψ (orbitMonodromy H g O) (T ^ orbitSize g O) := by
  simp [artinLocalFactor, artinLocalPoly_ind, Finset.prod_inv_distrib]

/-- Equivalence between `Ind_H^G (1_H)` and the permutation representation `ℂ[G ⧸ H]`
(`Representation.ofMulAction ℂ G (G ⧸ H)`). -/
def indTrivialEquivOfMulAction (H : Subgroup G) :
    Representation.Equiv
      (Representation.ind H.subtype (Representation.trivial ℂ H ℂ))
      (Representation.ofMulAction ℂ G (G ⧸ H)) := by
  let e1 := indEquivIndModel H (Representation.trivial ℂ H ℂ)
  let le : ((G ⧸ H) → ℂ) ≃ₗ[ℂ] MonoidAlgebra ℂ (G ⧸ H) :=
    (Finsupp.linearEquivFunOnFinite ℂ ℂ (G ⧸ H)).symm.trans (MonoidAlgebra.coeffLinearEquiv ℂ).symm
  have hle_apply : ∀ f : (G ⧸ H) → ℂ, le f = ∑ q : G ⧸ H, MonoidAlgebra.single q (f q) := by
    intro f
    apply (MonoidAlgebra.coeffLinearEquiv ℂ).injective
    ext q
    rw [map_sum, Finsupp.finsetSum_apply]
    have hl : (MonoidAlgebra.coeffLinearEquiv ℂ (le f)) q = f q := by
      simp [le]
    rw [hl, Finset.sum_eq_single q]
    · simp
    · intro q' _ hq'
      simp [hq']
    · intro h; exact absurd (Finset.mem_univ _) h
  let e2 : Representation.Equiv (indModel H (Representation.trivial ℂ H ℂ))
      (Representation.ofMulAction ℂ G (G ⧸ H)) :=
    Representation.Equiv.mk le fun g =>
      LinearMap.ext fun f => by
        change le (indModel H (Representation.trivial ℂ H ℂ) g f) =
          Representation.ofMulAction ℂ G (G ⧸ H) g (le f)
        rw [hle_apply, hle_apply, map_sum]
        have hact : ∀ q : G ⧸ H,
            Representation.ofMulAction ℂ G (G ⧸ H) g (MonoidAlgebra.single q (f q)) =
              MonoidAlgebra.single (g • q) (f q) := fun q =>
          Representation.ofMulAction_single g q (f q)
        simp_rw [hact]
        have htriv : ∀ q : G ⧸ H, indModel H (Representation.trivial ℂ H ℂ) g f q = f (g⁻¹ • q) :=
          fun q => by simp [indModel, Representation.trivial]
        simp_rw [htriv]
        rw [← Equiv.sum_comp (MulAction.toPerm g)]
        apply Finset.sum_congr rfl
        intro q _
        simp
  exact e1.trans e2

/-- **Specialization of Inductivity to `ψ = 1_H` (Permutation Representation Euler Factor)**:
`artinLocalFactor (ofMulAction ℂ G (G ⧸ H)) g T = ∏ O ∈ orbits(⟨g⟩ on G ⧸ H), (1 - T ^ |O|)⁻¹`. -/
theorem artinLocalFactor_perm_eq_prod_cycles (H : Subgroup G) (g : G) (T : ℂ) :
    artinLocalFactor (Representation.ofMulAction ℂ G (G ⧸ H)) g T =
      ∏ O : CycleOrbits g (G ⧸ H), (1 - T ^ orbitSize g O)⁻¹ := by
  rw [← artinLocalFactor_iso (indTrivialEquivOfMulAction H) g T,
    artinLocalFactor_ind H (Representation.trivial ℂ H ℂ) g T]
  apply Finset.prod_congr rfl
  intro O _
  exact artinLocalFactor_trivial (orbitMonodromy H g O) (T ^ orbitSize g O)

/-- Regular-representation specialization:
`artinLocalFactor (leftRegular ℂ G) g T = ∏ O ∈ orbits(⟨g⟩ on G), (1 - T ^ |O|)⁻¹`. -/
theorem artinLocalFactor_leftRegular_eq_prod_cycles (g : G) (T : ℂ) :
    artinLocalFactor (leftRegular ℂ G) g T =
      ∏ O : CycleOrbits g G, (1 - T ^ orbitSize g O)⁻¹ := by
  let qBot : G ≃ (G ⧸ (⊥ : Subgroup G)) := (QuotientGroup.quotientBot).symm.toEquiv
  have hqBot_smul : ∀ (a x : G), qBot (a • x) = a • qBot x := fun _ _ => rfl
  let eRep : Representation.Equiv (leftRegular ℂ G)
      (Representation.ofMulAction ℂ G (G ⧸ (⊥ : Subgroup G))) :=
    Representation.Equiv.mk (MonoidAlgebra.mapDomainLinearEquiv ℂ ℂ qBot) fun a => by
      apply MonoidAlgebra.lhom_ext'
      intro x
      apply LinearMap.ext_ring
      change MonoidAlgebra.mapDomainLinearEquiv ℂ ℂ qBot
          ((leftRegular ℂ G) a (MonoidAlgebra.single x (1 : ℂ))) =
        Representation.ofMulAction ℂ G (G ⧸ (⊥ : Subgroup G)) a
          (MonoidAlgebra.mapDomainLinearEquiv ℂ ℂ qBot (MonoidAlgebra.single x (1 : ℂ)))
      have h1 : (leftRegular ℂ G) a (MonoidAlgebra.single x (1 : ℂ)) =
          MonoidAlgebra.single (a * x) (1 : ℂ) :=
        Representation.ofMulAction_single a x (1 : ℂ)
      rw [h1]
      simp only [MonoidAlgebra.mapDomainLinearEquiv_single]
      rw [Representation.ofMulAction_single]
      rfl
  rw [artinLocalFactor_iso eRep g T, artinLocalFactor_perm_eq_prod_cycles (⊥ : Subgroup G) g T]
  let eOrb : CycleOrbits g G ≃ CycleOrbits g (G ⧸ (⊥ : Subgroup G)) :=
    { toFun := Quotient.map qBot (fun x y ⟨⟨a, ha⟩, hax⟩ => ⟨⟨a, ha⟩, by
        change a • qBot y = qBot x
        rw [← hqBot_smul]
        exact congr_arg qBot hax⟩)
      invFun := Quotient.map qBot.symm (fun x y ⟨⟨a, ha⟩, hax⟩ => ⟨⟨a, ha⟩, by
        apply qBot.injective
        change qBot (a • qBot.symm y) = qBot (qBot.symm x)
        rw [hqBot_smul, qBot.apply_symm_apply, qBot.apply_symm_apply]
        exact hax⟩)
      left_inv := fun O => by
        obtain ⟨x, rfl⟩ := Quotient.exists_rep O
        change Quotient.mk _ (qBot.symm (qBot x)) = Quotient.mk _ x
        rw [qBot.symm_apply_apply]
      right_inv := fun O => by
        obtain ⟨x, rfl⟩ := Quotient.exists_rep O
        change Quotient.mk _ (qBot (qBot.symm x)) = Quotient.mk _ x
        rw [qBot.apply_symm_apply] }
  rw [← Equiv.prod_comp eOrb]
  apply Finset.prod_congr rfl
  intro O _
  congr 2
  congr 1
  unfold orbitSize
  symm
  refine Nat.card_congr
    { toFun := fun ⟨x, hx⟩ => ⟨qBot x, by
        subst hx
        rfl⟩
      invFun := fun ⟨y, hy⟩ => ⟨qBot.symm y, by
        have h1 : eOrb (Quotient.mk (MulAction.orbitRel (Subgroup.zpowers g) G) (qBot.symm y)) =
            eOrb O := by
          change Quotient.mk _ (qBot (qBot.symm y)) = eOrb O
          rw [qBot.apply_symm_apply]
          exact hy
        exact eOrb.injective h1⟩
      left_inv := fun ⟨x, _⟩ => Subtype.ext (qBot.symm_apply_apply x)
      right_inv := fun ⟨y, _⟩ => Subtype.ext (qBot.apply_symm_apply y) }

end OrbitAndInductivity

end ArtinFormalism

/-! ## Section 3: Global Artin `L`-Function `artinL` & General Regular-Representation Factorization -/

section GlobalArtinL

open Classical

/-- Global unramified Artin `L`-function `L_S(ρ, s) = ∏'_{p ∉ S} det(1 - p^{-s} ρ(Frob_p))⁻¹`
attached to a finite set of ramified primes `S`, a Frobenius assignment `frob`, and a
complex representation `ρ` of `G`. -/
def artinL {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (S : Finset ℕ) (frob : {p : ℕ // p.Prime ∧ p ∉ S} → G)
    (ρ : Representation ℂ G V) (s : ℂ) : ℂ :=
  ∏' p : {p : ℕ // p.Prime ∧ p ∉ S}, artinLocalFactor ρ (frob p) ((p.1 : ℂ) ^ (-s))

/-- Elementary bound `‖-Complex.log (1 - z)‖ ≤ 2 * ‖z‖` for `‖z‖ ≤ 1 / 2`. -/
lemma norm_neg_log_one_sub_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖-Complex.log (1 - z)‖ ≤ 2 * ‖z‖ := by
  have hz1 : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
  have hlog := Complex.hasSum_taylorSeries_neg_log hz1
  have hshift : HasSum (fun m : ℕ => z ^ (m + 1) / ((m + 1 : ℕ) : ℂ)) (-Complex.log (1 - z)) := by
    have h0 : z ^ 0 / (0 : ℂ) = 0 := by simp
    have := (hasSum_nat_add_iff' (f := fun n : ℕ => z ^ n / (n : ℂ)) 1).mpr hlog
    simpa [Finset.sum_range_one, h0] using this
  have hgeom : HasSum (fun m : ℕ => ‖z‖ * ‖z‖ ^ m) (‖z‖ * (1 - ‖z‖)⁻¹) :=
    (hasSum_geometric_of_lt_one (norm_nonneg z) hz1).mul_left ‖z‖
  have hbound : ∀ m : ℕ, ‖z ^ (m + 1) / ((m + 1 : ℕ) : ℂ)‖ ≤ ‖z‖ * ‖z‖ ^ m := by
    intro m
    rw [norm_div, norm_pow, Complex.norm_natCast, pow_succ']
    have hm1 : (1 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.succ_pos m
    exact div_le_self (by positivity) hm1
  have hnorm_le : ‖-Complex.log (1 - z)‖ ≤ ‖z‖ * (1 - ‖z‖)⁻¹ := by
    have hsum_norm : Summable (fun m : ℕ => ‖z ^ (m + 1) / ((m + 1 : ℕ) : ℂ)‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hgeom.summable
    calc
      ‖-Complex.log (1 - z)‖ = ‖∑' m : ℕ, z ^ (m + 1) / ((m + 1 : ℕ) : ℂ)‖ := by
        rw [hshift.tsum_eq]
      _ ≤ ∑' m : ℕ, ‖z ^ (m + 1) / ((m + 1 : ℕ) : ℂ)‖ := norm_tsum_le_tsum_norm hsum_norm
      _ ≤ ∑' m : ℕ, ‖z‖ * ‖z‖ ^ m :=
        hsum_norm.tsum_le_tsum hbound hgeom.summable
      _ = ‖z‖ * (1 - ‖z‖)⁻¹ := hgeom.tsum_eq
  have hinv : (1 - ‖z‖)⁻¹ ≤ 2 := by
    have hpos : (1 / 2 : ℝ) ≤ 1 - ‖z‖ := by linarith
    have h1 : (1 - ‖z‖)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hpos
    linarith [show (1 / 2 : ℝ)⁻¹ = 2 by norm_num]
  calc
    ‖-Complex.log (1 - z)‖ ≤ ‖z‖ * (1 - ‖z‖)⁻¹ := hnorm_le
    _ ≤ ‖z‖ * 2 := mul_le_mul_of_nonneg_left hinv (norm_nonneg z)
    _ = 2 * ‖z‖ := mul_comm _ _

/-- **Unconditional Absolute Convergence & Exponential-Logarithm Representation of `artinL`**:
for every finite group `G`, finite-dimensional `ρ`, and `s : ℂ` with `1 < s.re`, the Euler
product defining `artinL S frob ρ s` is `Multipliable` and nonzero. -/
theorem artinL_multipliable_and_ne_zero {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (S : Finset ℕ) (frob : {p : ℕ // p.Prime ∧ p ∉ S} → G)
    (ρ : Representation ℂ G V) {s : ℂ} (hs : 1 < s.re) :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ p ∉ S} =>
      artinLocalFactor ρ (frob p) ((p.1 : ℂ) ^ (-s))) ∧
      artinL S frob ρ s ≠ 0 := by
  have heig : ∀ p : {p : ℕ // p.Prime ∧ p ∉ S},
      ∃ (b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V)
        (ev : Fin (Module.finrank ℂ V) → ℂ),
        (∀ i, ρ (frob p) (b i) = ev i • b i) ∧ (∀ i, ‖ev i‖ = 1) := by
    intro p
    obtain ⟨b, ev, hev, _, hnorm⟩ := exists_eigenbasis_rep ρ (frob p)
    exact ⟨b, ev, hev, hnorm⟩
  choose b ev hev hnorm using heig
  let g : {p : ℕ // p.Prime ∧ p ∉ S} → ℂ := fun p =>
    ∑ i : Fin (Module.finrank ℂ V), -Complex.log (1 - ev p i * (p.1 : ℂ) ^ (-s))
  have hp_norm : ∀ p : {p : ℕ // p.Prime ∧ p ∉ S},
      ‖(p.1 : ℂ) ^ (-s)‖ = (p.1 : ℝ) ^ (-s.re) := by
    intro p
    rw [Complex.norm_natCast_cpow_of_pos p.2.1.pos, Complex.neg_re]
  have hp_half : ∀ p : {p : ℕ // p.Prime ∧ p ∉ S}, ‖(p.1 : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
    intro p
    rw [hp_norm p]
    have h2le : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.1.two_le
    have h1 : (p.1 : ℝ) ^ (-s.re) ≤ (p.1 : ℝ) ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have h2 : (p.1 : ℝ) ^ (-1 : ℝ) ≤ (2 : ℝ) ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one, Real.rpow_neg_one]
      exact inv_anti₀ (by norm_num) h2le
    have h3 : (2 : ℝ) ^ (-1 : ℝ) = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
    exact (h1.trans h2).trans_eq h3
  have hexp_eq : ∀ p : {p : ℕ // p.Prime ∧ p ∉ S},
      Complex.exp (g p) = artinLocalFactor ρ (frob p) ((p.1 : ℂ) ^ (-s)) := by
    intro p
    dsimp only [g]
    rw [Complex.exp_sum]
    unfold artinLocalFactor
    rw [artinLocalPoly_eq_prod_of_eigenbasis ρ (frob p) (b p) (ev p) (hev p),
      ← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro i _
    have hz : ‖ev p i * (p.1 : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
      rw [norm_mul, hnorm p i, one_mul]
      exact hp_half p
    have hne : 1 - ev p i * (p.1 : ℂ) ^ (-s) ≠ 0 := by
      intro h0
      have heq : ev p i * (p.1 : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h0).symm
      have hn : ‖ev p i * (p.1 : ℂ) ^ (-s)‖ = 1 := by rw [heq, norm_one]
      linarith
    rw [Complex.exp_neg, Complex.exp_log hne]
  have hg_bound : ∀ p : {p : ℕ // p.Prime ∧ p ∉ S},
      ‖g p‖ ≤ (2 * (Module.finrank ℂ V : ℝ)) * (p.1 : ℝ) ^ (-s.re) := by
    intro p
    calc
      ‖g p‖ ≤ ∑ i : Fin (Module.finrank ℂ V), ‖-Complex.log (1 - ev p i * (p.1 : ℂ) ^ (-s))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _i : Fin (Module.finrank ℂ V), 2 * (p.1 : ℝ) ^ (-s.re) := by
        apply Finset.sum_le_sum
        intro i _
        have hz : ‖ev p i * (p.1 : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
          rw [norm_mul, hnorm p i, one_mul]; exact hp_half p
        calc
          ‖-Complex.log (1 - ev p i * (p.1 : ℂ) ^ (-s))‖
              ≤ 2 * ‖ev p i * (p.1 : ℂ) ^ (-s)‖ := norm_neg_log_one_sub_le hz
          _ = 2 * (p.1 : ℝ) ^ (-s.re) := by rw [norm_mul, hnorm p i, one_mul, hp_norm p]
      _ = (2 * (Module.finrank ℂ V : ℝ)) * (p.1 : ℝ) ^ (-s.re) := by
        simp [Finset.sum_const, nsmul_eq_mul]; ring
  have hnat_sum : Summable (fun n : ℕ => (n : ℝ) ^ (-s.re)) := by
    have h := Real.summable_nat_rpow_inv.mpr hs
    refine h.congr fun n => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg n)]
  have hp_sum : Summable (fun p : {p : ℕ // p.Prime ∧ p ∉ S} =>
      (2 * (Module.finrank ℂ V : ℝ)) * (p.1 : ℝ) ^ (-s.re)) :=
    (hnat_sum.comp_injective Subtype.val_injective).mul_left _
  have hg_sum : Summable g :=
    Summable.of_norm_bounded hp_sum hg_bound
  have hhasProd : HasProd (fun p : {p : ℕ // p.Prime ∧ p ∉ S} =>
      artinLocalFactor ρ (frob p) ((p.1 : ℂ) ^ (-s))) (Complex.exp (∑' p, g p)) := by
    rw [HasProd]
    have htend : Filter.Tendsto (fun F : Finset {p : ℕ // p.Prime ∧ p ∉ S} =>
        Complex.exp (∑ p ∈ F, g p)) Filter.atTop (nhds (Complex.exp (∑' p, g p))) :=
      (Complex.continuous_exp.continuousAt.tendsto).comp hg_sum.hasSum
    refine htend.congr fun F => ?_
    rw [Complex.exp_sum]
    exact Finset.prod_congr rfl fun p _ => hexp_eq p
  refine ⟨hhasProd.multipliable, ?_⟩
  unfold artinL
  rw [hhasProd.tprod_eq]
  exact Complex.exp_ne_zero _

theorem artinL_multipliable {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (S : Finset ℕ) (frob : {p : ℕ // p.Prime ∧ p ∉ S} → G)
    (ρ : Representation ℂ G V) {s : ℂ} (hs : 1 < s.re) :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ p ∉ S} =>
      artinLocalFactor ρ (frob p) ((p.1 : ℂ) ^ (-s))) :=
  (artinL_multipliable_and_ne_zero S frob ρ hs).1

theorem artinL_ne_zero {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (S : Finset ℕ) (frob : {p : ℕ // p.Prime ∧ p ∉ S} → G)
    (ρ : Representation ℂ G V) {s : ℂ} (hs : 1 < s.re) :
    artinL S frob ρ s ≠ 0 :=
  (artinL_multipliable_and_ne_zero S frob ρ hs).2

/-- Global isomorphism invariance of `artinL`. -/
theorem artinL_iso {G V W : Type*} [Group G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (S : Finset ℕ) (frob : {p : ℕ // p.Prime ∧ p ∉ S} → G)
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (φ : Representation.Equiv ρ σ) (s : ℂ) :
    artinL S frob ρ s = artinL S frob σ s := by
  unfold artinL
  congr 1; ext p
  exact artinLocalFactor_iso φ (frob p) ((p.1 : ℂ) ^ (-s))

/-- Global character determination of `artinL`. -/
theorem artinL_eq_of_character_eq {G V W : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (S : Finset ℕ) (frob : {p : ℕ // p.Prime ∧ p ∉ S} → G)
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (hchar : ρ.character = σ.character) (s : ℂ) :
    artinL S frob ρ s = artinL S frob σ s := by
  unfold artinL
  congr 1; ext p
  exact artinLocalFactor_eq_of_character_eq hchar (frob p) ((p.1 : ℂ) ^ (-s))

/-- **Global Additivity (Binary)**: `L_S(ρ₁ ⊕ ρ₂, s) = L_S(ρ₁, s) · L_S(ρ₂, s)` on `1 < s.re`. -/
theorem artinL_prod {G V₁ V₂ : Type*} [Group G] [Finite G]
    [AddCommGroup V₁] [Module ℂ V₁] [FiniteDimensional ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] [FiniteDimensional ℂ V₂]
    (S : Finset ℕ) (frob : {p : ℕ // p.Prime ∧ p ∉ S} → G)
    (ρ₁ : Representation ℂ G V₁) (ρ₂ : Representation ℂ G V₂)
    {s : ℂ} (hs : 1 < s.re) :
    artinL S frob (Representation.prod ρ₁ ρ₂) s =
      artinL S frob ρ₁ s * artinL S frob ρ₂ s := by
  unfold artinL
  simp_rw [artinLocalFactor_prod]
  exact (artinL_multipliable S frob ρ₁ hs).tprod_mul (artinL_multipliable S frob ρ₂ hs)

/-- Helper: finite product commutes with `tprod` for multipliable families. -/
lemma tprod_finset_prod_of_multipliable {α ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → α → ℂ) (hf : ∀ i ∈ s, Multipliable (f i)) :
    (∏' a : α, ∏ i ∈ s, f i a) = ∏ i ∈ s, ∏' a : α, f i a := by
  have hmult_prod : ∀ t : Finset ι, (∀ j ∈ t, Multipliable (f j)) →
      Multipliable (fun a => ∏ j ∈ t, f j a) := by
    intro t ht
    induction t using Finset.induction_on with
    | empty => simp [multipliable_one]
    | insert j t hjt iht =>
      simp_rw [Finset.prod_insert hjt]
      exact (ht j (Finset.mem_insert_self j t)).mul
        (iht (fun k hk => ht k (Finset.mem_insert_of_mem hk)))
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hf_i : Multipliable (f i) := hf i (Finset.mem_insert_self i s)
    have hf_s : ∀ j ∈ s, Multipliable (f j) := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    simp_rw [Finset.prod_insert hi]
    rw [hf_i.tprod_mul (hmult_prod s hf_s), ih hf_s]

/-- **Global Additivity (Finite Direct Sum)**: `L_S(⨁ i, ρ i, s) = ∏ i, L_S(ρ i, s)` on `1 < s.re`. -/
theorem artinL_directSum {G ι : Type*} [Group G] [Finite G] [Fintype ι] [DecidableEq ι]
    {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)]
    (S : Finset ℕ) (frob : {p : ℕ // p.Prime ∧ p ∉ S} → G)
    (ρ : ∀ i, Representation ℂ G (V i)) {s : ℂ} (hs : 1 < s.re) :
    artinL S frob (Representation.directSum ρ) s =
      ∏ i : ι, artinL S frob (ρ i) s := by
  unfold artinL
  simp_rw [artinLocalFactor_directSum]
  exact tprod_finset_prod_of_multipliable Finset.univ
    (fun i p => artinLocalFactor (ρ i) (frob p) ((p.1 : ℂ) ^ (-s)))
    (fun i _ => artinL_multipliable S frob (ρ i) hs)

/-- **Global Trivial Specialization**: on `1 < s.re`, the Artin `L`-function of the trivial
representation equals the unramified Riemann zeta function
`(∏_{p ∈ S, p prime} (1 - p^{-s})) · ζ(s)`. -/
theorem artinL_trivial {G : Type*} [Group G] [Finite G]
    (S : Finset ℕ) (frob : {p : ℕ // p.Prime ∧ p ∉ S} → G)
    {s : ℂ} (hs : 1 < s.re) :
    artinL S frob (Representation.trivial ℂ G ℂ) s =
      (∏ p ∈ S.filter Nat.Prime, (1 - (p : ℂ) ^ (-s))) * riemannZeta s := by
  have hzeta : HasProd (fun p : Nat.Primes => (1 - (p.1 : ℂ) ^ (-s))⁻¹) (riemannZeta s) :=
    riemannZeta_eulerProduct_hasProd hs
  let ramSet : Set Nat.Primes := {p | p.1 ∈ S}
  have hram_fin : ramSet.Finite := by
    refine Set.Finite.subset ((S.finite_toSet).preimage (Subtype.val_injective.injOn)) ?_
    intro p hp; exact hp
  let f : Nat.Primes → ℂ := fun p => (1 - (p.1 : ℂ) ^ (-s))⁻¹
  have hmult_ram : Multipliable (f ∘ (Subtype.val : ramSet → Nat.Primes)) := by
    let : Fintype ramSet := hram_fin.fintype
    exact (hasProd_fintype (f ∘ (Subtype.val : ramSet → Nat.Primes))).multipliable
  let eUnram : {p : ℕ // p.Prime ∧ p ∉ S} ≃ (ramSetᶜ : Set Nat.Primes) :=
    { toFun := fun ⟨p, hp, hnot⟩ => ⟨⟨p, hp⟩, hnot⟩
      invFun := fun ⟨⟨p, hp⟩, hnot⟩ => ⟨p, hp, hnot⟩
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
  have hmult_unram0 : Multipliable ((f ∘ (Subtype.val : (ramSetᶜ : Set Nat.Primes) → Nat.Primes)) ∘ eUnram) := by
    have h := artinL_multipliable S frob (Representation.trivial ℂ G ℂ) hs
    refine h.congr fun ⟨p, hp, hnot⟩ => ?_
    dsimp only [Function.comp_apply, f, eUnram]
    exact artinLocalFactor_trivial (frob ⟨p, hp, hnot⟩) ((p : ℂ) ^ (-s))
  have hmult_unram : Multipliable (f ∘ (Subtype.val : (ramSetᶜ : Set Nat.Primes) → Nat.Primes)) :=
    (Equiv.multipliable_iff eUnram).mp hmult_unram0
  have hsplit : riemannZeta s =
      (∏' p : ramSet, f p.1) * (∏' p : (ramSetᶜ : Set Nat.Primes), f p.1) := by
    rw [← hzeta.tprod_eq]
    have hmul := (multipliable_subtype_iff_mulIndicator.mp hmult_ram).tprod_mul
      (multipliable_subtype_iff_mulIndicator.mp hmult_unram)
    rw [← tprod_subtype ramSet f, ← tprod_subtype (ramSetᶜ : Set Nat.Primes) f] at hmul
    rw [← hmul]
    congr 1; ext p
    by_cases hp : p ∈ ramSet
    · simp [Set.mulIndicator_of_mem hp, Set.mulIndicator_of_notMem (Set.notMem_compl_iff.mpr hp), f]
    · simp [Set.mulIndicator_of_notMem hp, Set.mulIndicator_of_mem (Set.mem_compl hp), f]
  have hram_val : (∏' p : ramSet, f p.1) =
      (∏ p ∈ S.filter Nat.Prime, (1 - (p : ℂ) ^ (-s)))⁻¹ := by
    let : Fintype ramSet := hram_fin.fintype
    rw [tprod_eq_prod (s := Finset.univ) (fun p hp => absurd (Finset.mem_univ p) hp),
      ← Finset.prod_inv_distrib]
    refine Finset.prod_bij (fun p _ => p.1.1) ?_ ?_ ?_ ?_
    · intro p _
      exact Finset.mem_filter.mpr ⟨p.2, p.1.2⟩
    · intro p₁ _ p₂ _ heq
      exact Subtype.ext (Subtype.ext heq)
    · intro n hn
      obtain ⟨hnS, hnp⟩ := Finset.mem_filter.mp hn
      exact ⟨⟨⟨n, hnp⟩, hnS⟩, Finset.mem_univ _, rfl⟩
    · intro p _; rfl
  have hunram_val : (∏' p : (ramSetᶜ : Set Nat.Primes), f p.1) =
      artinL S frob (Representation.trivial ℂ G ℂ) s := by
    rw [← Equiv.tprod_eq eUnram]
    unfold artinL
    congr 1; ext ⟨p, hp, hnot⟩
    dsimp only [f, eUnram]
    exact (artinLocalFactor_trivial (frob ⟨p, hp, hnot⟩) ((p : ℂ) ^ (-s))).symm
  have hfin_ne : (∏ p ∈ S.filter Nat.Prime, (1 - (p : ℂ) ^ (-s))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp h0
    have hpr : p.Prime := (Finset.mem_filter.mp hp).2
    have hnorm : ‖(p : ℂ) ^ (-s)‖ < 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hpr.pos, Complex.neg_re]
      have h1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hpr.one_lt
      exact Real.rpow_lt_one_of_one_lt_of_neg h1 (by linarith)
    have heq : (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h0).symm
    rw [heq, norm_one] at hnorm
    exact lt_irrefl 1 hnorm
  rw [hsplit, hram_val, hunram_val, ← mul_assoc, mul_inv_cancel₀ hfin_ne, one_mul]

/-! ### Complete Irreducible Decomposition of `ℂ[G]` & General Dedekind Zeta Factorization -/

section RegularDecomposition

variable {G : Type*} [Group G] [Fintype G]

/-- Character of a subrepresentation pushed along an isomorphism `ρ ≃ ρ₁ ⊕ ρ₂`. -/
lemma character_prod {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [FiniteDimensional ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] [FiniteDimensional ℂ V₂]
    (ρ₁ : Representation ℂ G V₁) (ρ₂ : Representation ℂ G V₂) (g : G) :
    (Representation.prod ρ₁ ρ₂).character g = ρ₁.character g + ρ₂.character g := by
  obtain ⟨b₁, ev₁, hev₁, _, _⟩ := exists_eigenbasis_rep ρ₁ g
  obtain ⟨b₂, ev₂, hev₂, _, _⟩ := exists_eigenbasis_rep ρ₂ g
  let b := b₁.prod b₂
  let ev := Sum.elim ev₁ ev₂
  have hev : ∀ i, (Representation.prod ρ₁ ρ₂) g (b i) = ev i • b i := by
    rintro (i | j)
    · ext <;> simp [b, ev, Representation.prod, hev₁]
    · ext <;> simp [b, ev, Representation.prod, hev₂]
  have h1 := character_pow_eq_sum_of_eigenbasis (Representation.prod ρ₁ ρ₂) g b ev hev 1
  have h2 := character_pow_eq_sum_of_eigenbasis ρ₁ g b₁ ev₁ hev₁ 1
  have h3 := character_pow_eq_sum_of_eigenbasis ρ₂ g b₂ ev₂ hev₂ 1
  simp only [pow_one] at h1 h2 h3
  rw [h1, h2, h3, Fintype.sum_sum_type]
  rfl

omit [Fintype G] in
/-- Irreducibility is preserved under representation isomorphism. -/
lemma isIrreducible_of_equiv {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (φ : Representation.Equiv ρ σ) (hρ : Representation.IsIrreducible ρ) :
    Representation.IsIrreducible σ := by
  have hmap : ∀ (S : Subrepresentation ρ) (g : G) (w : W),
      w ∈ S.toSubmodule.map φ.toLinearEquiv.toLinearMap →
      σ g w ∈ S.toSubmodule.map φ.toLinearEquiv.toLinearMap := by
    intro S g w hw
    rcases hw with ⟨v, hv, rfl⟩
    refine ⟨ρ g v, S.apply_mem_toSubmodule g hv, ?_⟩
    have h1 := φ.isIntertwining' g
    exact congr_arg (fun f : V →ₗ[ℂ] W => f v) h1
  have hcomap : ∀ (T : Subrepresentation σ) (g : G) (v : V),
      v ∈ T.toSubmodule.comap φ.toLinearEquiv.toLinearMap →
      ρ g v ∈ T.toSubmodule.comap φ.toLinearEquiv.toLinearMap := by
    intro T g v hv
    have h1 := φ.isIntertwining' g
    have h2 : φ.toLinearEquiv (ρ g v) = σ g (φ.toLinearEquiv v) :=
      congr_arg (fun f : V →ₗ[ℂ] W => f v) h1
    change φ.toLinearEquiv (ρ g v) ∈ T.toSubmodule
    rw [h2]
    exact T.apply_mem_toSubmodule g hv
  let eSub : Subrepresentation ρ ≃o Subrepresentation σ :=
    { toFun := fun S => ⟨S.toSubmodule.map φ.toLinearEquiv.toLinearMap, hmap S⟩
      invFun := fun T => ⟨T.toSubmodule.comap φ.toLinearEquiv.toLinearMap, hcomap T⟩
      left_inv := fun S => Subrepresentation.ext (Submodule.comap_map_eq_of_injective φ.toLinearEquiv.injective S.toSubmodule)
      right_inv := fun T => Subrepresentation.ext (Submodule.map_comap_eq_of_surjective φ.toLinearEquiv.surjective T.toSubmodule)
      map_rel_iff' := fun {S₁ S₂} => by
        change S₁.toSubmodule.map φ.toLinearEquiv.toLinearMap ≤
            S₂.toSubmodule.map φ.toLinearEquiv.toLinearMap ↔ S₁.toSubmodule ≤ S₂.toSubmodule
        constructor
        · intro h v hv
          obtain ⟨v', hv', heq⟩ := h ⟨v, hv, rfl⟩
          exact (φ.toLinearEquiv.injective heq) ▸ hv'
        · exact Submodule.map_mono }
  exact eSub.isSimpleOrder_iff.mp hρ

/-- Helper: every finite-dimensional complex representation of a finite group `G` decomposes
into a finite list of irreducible subrepresentations whose characters sum to `ρ.character`
and whose local Artin Euler factors multiply to `artinLocalFactor ρ`. -/
theorem exists_irrep_decomp_list.{u} {V : Type u} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    ∃ (k : ℕ) (W : Fin k → Subrepresentation ρ),
      (∀ i, Representation.IsIrreducible (W i).toRepresentation) ∧
      (∀ g, ρ.character g = ∑ i : Fin k, (W i).toRepresentation.character g) ∧
      (∀ g T, artinLocalFactor ρ g T = ∏ i : Fin k, artinLocalFactor (W i).toRepresentation g T) := by
  suffices h : ∀ n : ℕ, ∀ {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ G V), Module.finrank ℂ V = n →
      ∃ (k : ℕ) (W : Fin k → Subrepresentation ρ),
        (∀ i, Representation.IsIrreducible (W i).toRepresentation) ∧
        (∀ g, ρ.character g = ∑ i : Fin k, (W i).toRepresentation.character g) ∧
        (∀ g T, artinLocalFactor ρ g T = ∏ i : Fin k, artinLocalFactor (W i).toRepresentation g T) from
    h (Module.finrank ℂ V) ρ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ _ ρ hdim
    by_cases hn0 : n = 0
    · subst hn0
      have : Subsingleton V := Module.finrank_zero_iff.mp hdim
      refine ⟨0, Fin.elim0, fun i => i.elim0, fun g => ?_, fun g T => ?_⟩
      · have h0 : ρ g = 0 := Subsingleton.elim _ _
        simp [Representation.character, h0]
      · simp [artinLocalFactor, artinLocalPoly, LinearMap.det_eq_one_of_subsingleton]
    · have hpos : 0 < Module.finrank ℂ V := by omega
      by_cases hirr : Representation.IsIrreducible ρ
      · let topSub : Subrepresentation ρ := ⊤
        let eTop : Representation.Equiv topSub.toRepresentation ρ :=
          Representation.Equiv.mk Submodule.topEquiv (fun _ => rfl)
        have hirr_top : Representation.IsIrreducible topSub.toRepresentation :=
          isIrreducible_of_equiv eTop.symm hirr
        refine ⟨1, fun _ => topSub, fun _ => hirr_top, fun g => ?_, fun g T => ?_⟩
        · simp [Representation.char_iso eTop]
        · simp [artinLocalFactor_iso eTop]
      · have : Nontrivial V := Module.finrank_pos_iff.mp hpos
        have hbot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
          intro heq
          have hsub : (⊥ : Submodule ℂ V) = ⊤ := congr_arg Subrepresentation.toSubmodule heq
          exact bot_ne_top hsub
        have hexU : ∃ U : Subrepresentation ρ, U ≠ ⊥ ∧ U ≠ ⊤ := by
          by_contra hall
          push Not at hall
          have : Nontrivial (Subrepresentation ρ) := ⟨⟨⊥, ⊤, hbot_ne_top⟩⟩
          apply hirr
          refine ⟨fun U => ?_⟩
          by_cases hU : U = ⊥
          · exact Or.inl hU
          · exact Or.inr (hall U hU)
        obtain ⟨U, hU_bot, hU_top⟩ := hexU
        have : Invertible (Fintype.card G : ℂ) :=
          invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
        have hss : Representation.IsSemisimpleRepresentation ρ := by
          rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
          infer_instance
        obtain ⟨U', hcompl⟩ := hss.exists_isCompl U
        -- Show ρ ≃ U ⊕ U'
        have hcompl_sub : IsCompl U.toSubmodule U'.toSubmodule := by
          constructor
          · rw [disjoint_iff]
            have h1 := congr_arg Subrepresentation.toSubmodule hcompl.disjoint.eq_bot
            exact h1
          · rw [codisjoint_iff]
            have h2 := congr_arg Subrepresentation.toSubmodule hcompl.codisjoint.eq_top
            exact h2
        let eProd : Representation.Equiv
            (Representation.prod U.toRepresentation U'.toRepresentation) ρ :=
          Representation.Equiv.mk (Submodule.prodEquivOfIsCompl U.toSubmodule U'.toSubmodule hcompl_sub)
            fun g => LinearMap.ext fun ⟨⟨u, hu⟩, ⟨u', hu'⟩⟩ => by
              change ρ g u + ρ g u' = ρ g (u + u')
              rw [map_add]
        -- Dimension bounds: both finrank U < n and finrank U' < n
        have hsum_dim : Module.finrank ℂ U.toSubmodule + Module.finrank ℂ U'.toSubmodule = n := by
          have := LinearEquiv.finrank_eq eProd.toLinearEquiv
          rw [Module.finrank_prod, hdim] at this
          exact this
        have hU_pos : 0 < Module.finrank ℂ U.toSubmodule := by
          apply Module.finrank_pos_iff.mpr
          by_contra hnot
          have : Subsingleton U.toSubmodule := not_nontrivial_iff_subsingleton.mp hnot
          apply hU_bot
          apply Subrepresentation.ext
          change U.toSubmodule = ⊥
          rw [eq_bot_iff]
          intro x hx
          have : (⟨x, hx⟩ : U.toSubmodule) = 0 := Subsingleton.elim _ _
          exact congr_arg Subtype.val this
        have hU'_pos : 0 < Module.finrank ℂ U'.toSubmodule := by
          apply Module.finrank_pos_iff.mpr
          by_contra hnot
          have : Subsingleton U'.toSubmodule := not_nontrivial_iff_subsingleton.mp hnot
          have hU'_bot : U'.toSubmodule = ⊥ := by
            rw [eq_bot_iff]
            intro x hx
            have : (⟨x, hx⟩ : U'.toSubmodule) = 0 := Subsingleton.elim _ _
            exact congr_arg Subtype.val this
          apply hU_top
          apply Subrepresentation.ext
          have := hcompl_sub.codisjoint.eq_top
          rw [hU'_bot, sup_bot_eq] at this
          exact this
        obtain ⟨k₁, W₁, hirr₁, hchar₁, hfac₁⟩ :=
          ih (Module.finrank ℂ U.toSubmodule) (by omega) U.toRepresentation rfl
        obtain ⟨k₂, W₂, hirr₂, hchar₂, hfac₂⟩ :=
          ih (Module.finrank ℂ U'.toSubmodule) (by omega) U'.toRepresentation rfl
        -- Push subrepresentations of U and U' back into Subrepresentation ρ
        let pushU : Subrepresentation U.toRepresentation → Subrepresentation ρ := fun S =>
          { toSubmodule := S.toSubmodule.map U.toSubmodule.subtype
            apply_mem_toSubmodule := fun g x hx => by
              rcases hx with ⟨u, hu, rfl⟩
              exact ⟨U.toRepresentation g u, S.apply_mem_toSubmodule g hu, rfl⟩ }
        let pushU' : Subrepresentation U'.toRepresentation → Subrepresentation ρ := fun S =>
          { toSubmodule := S.toSubmodule.map U'.toSubmodule.subtype
            apply_mem_toSubmodule := fun g x hx => by
              rcases hx with ⟨u, hu, rfl⟩
              exact ⟨U'.toRepresentation g u, S.apply_mem_toSubmodule g hu, rfl⟩ }
        have hpushU_equiv : ∀ S : Subrepresentation U.toRepresentation,
            Representation.Equiv S.toRepresentation (pushU S).toRepresentation := fun S => by
          let f : S.toSubmodule →ₗ[ℂ] (pushU S).toSubmodule :=
            { toFun := fun ⟨u, hu⟩ => ⟨u.1, ⟨u, hu, rfl⟩⟩
              map_add' := fun _ _ => rfl
              map_smul' := fun _ _ => rfl }
          have hf_bij : Function.Bijective f :=
            ⟨fun ⟨⟨u₁, hu₁⟩, h₁⟩ ⟨⟨u₂, hu₂⟩, h₂⟩ h => by
              have hval : u₁ = u₂ := congr_arg Subtype.val h
              subst hval; rfl,
             fun ⟨_, ⟨u, hu, rfl⟩⟩ => ⟨⟨u, hu⟩, rfl⟩⟩
          exact Representation.Equiv.mk (LinearEquiv.ofBijective f hf_bij) (fun _ => rfl)
        have hpushU'_equiv : ∀ S : Subrepresentation U'.toRepresentation,
            Representation.Equiv S.toRepresentation (pushU' S).toRepresentation := fun S => by
          let f : S.toSubmodule →ₗ[ℂ] (pushU' S).toSubmodule :=
            { toFun := fun ⟨u, hu⟩ => ⟨u.1, ⟨u, hu, rfl⟩⟩
              map_add' := fun _ _ => rfl
              map_smul' := fun _ _ => rfl }
          have hf_bij : Function.Bijective f :=
            ⟨fun ⟨⟨u₁, hu₁⟩, h₁⟩ ⟨⟨u₂, hu₂⟩, h₂⟩ h => by
              have hval : u₁ = u₂ := congr_arg Subtype.val h
              subst hval; rfl,
             fun ⟨_, ⟨u, hu, rfl⟩⟩ => ⟨⟨u, hu⟩, rfl⟩⟩
          exact Representation.Equiv.mk (LinearEquiv.ofBijective f hf_bij) (fun _ => rfl)
        let W : Fin (k₁ + k₂) → Subrepresentation ρ := fun idx =>
          if hlt : idx.1 < k₁ then pushU (W₁ ⟨idx.1, hlt⟩)
          else pushU' (W₂ ⟨idx.1 - k₁, by omega⟩)
        have hW_left : ∀ i : Fin k₁, W (Fin.castAdd k₂ i) = pushU (W₁ i) := fun i => by
          simp [W, i.2]
        have hW_right : ∀ j : Fin k₂, W (Fin.natAdd k₁ j) = pushU' (W₂ j) := fun j => by
          have hnot : ¬ k₁ + j.1 < k₁ := by omega
          simp [W, hnot]
        refine ⟨k₁ + k₂, W, ?_, ?_, ?_⟩
        · intro idx
          by_cases hlt : idx.1 < k₁
          · have hidx : idx = Fin.castAdd k₂ ⟨idx.1, hlt⟩ := by ext; rfl
            rw [hidx, hW_left]
            exact isIrreducible_of_equiv (hpushU_equiv (W₁ ⟨idx.1, hlt⟩)) (hirr₁ ⟨idx.1, hlt⟩)
          · have hidx : idx = Fin.natAdd k₁ ⟨idx.1 - k₁, by omega⟩ := by ext; dsimp; omega
            rw [hidx, hW_right]
            exact isIrreducible_of_equiv (hpushU'_equiv (W₂ ⟨idx.1 - k₁, by omega⟩))
              (hirr₂ ⟨idx.1 - k₁, by omega⟩)
        · intro g
          rw [← Representation.char_iso eProd, character_prod, hchar₁ g, hchar₂ g, Fin.sum_univ_add]
          congr 1
          · apply Finset.sum_congr rfl
            intro i _
            rw [hW_left]
            exact congr_fun (Representation.char_iso (hpushU_equiv (W₁ i))) g
          · apply Finset.sum_congr rfl
            intro j _
            rw [hW_right]
            exact congr_fun (Representation.char_iso (hpushU'_equiv (W₂ j))) g
        · intro g T
          rw [← artinLocalFactor_iso eProd, artinLocalFactor_prod, hfac₁ g T, hfac₂ g T,
            Fin.prod_univ_add]
          congr 1
          · apply Finset.prod_congr rfl
            intro i _
            rw [hW_left]
            exact artinLocalFactor_iso (hpushU_equiv (W₁ i)) g T
          · apply Finset.prod_congr rfl
            intro j _
            rw [hW_right]
            exact artinLocalFactor_iso (hpushU'_equiv (W₂ j)) g T

/-- Exact character of the left regular representation `ℂ[G]`: `|G|` at `1` and `0` elsewhere. -/
theorem leftRegular_character (g : G) :
    (leftRegular ℂ G).character g = if g = 1 then (Fintype.card G : ℂ) else 0 := by
  unfold Representation.character
  let b : Module.Basis G ℂ (MonoidAlgebra ℂ G) := MonoidAlgebra.basis G ℂ
  rw [LinearMap.trace_eq_matrix_trace ℂ b]
  simp only [Matrix.trace, Matrix.diag]
  have hentry : ∀ x : G, LinearMap.toMatrix b b ((leftRegular ℂ G) g) x x =
      if g = 1 then 1 else 0 := by
    intro x
    rw [LinearMap.toMatrix_apply]
    have hbx : b x = MonoidAlgebra.single x (1 : ℂ) := by
      simp [b, MonoidAlgebra.basis]
    have hact : (leftRegular ℂ G) g (b x) = b (g * x) := by
      rw [hbx]
      have h1 : (leftRegular ℂ G) g (MonoidAlgebra.single x (1 : ℂ)) =
          MonoidAlgebra.single (g * x) (1 : ℂ) :=
        Representation.ofMulAction_single g x (1 : ℂ)
      rw [h1]
      simp [b, MonoidAlgebra.basis]
    rw [hact, b.repr_self, Finsupp.single_apply]
    have hiff : g * x = x ↔ g = 1 := mul_eq_right
    by_cases hg : g = 1
    · rw [if_pos (hiff.mpr hg), if_pos hg]
    · rw [if_neg (mt hiff.mp hg), if_neg hg]
  simp_rw [hentry]
  split_ifs <;> simp

/-- **Complete Irreducible Decomposition of `ℂ[G]` & Local/Global Regular-Representation
Artin Factorization (`dedekind_eq_prod_irrep_artinL`)**:
For ANY finite group `G`, there exists a finite family of pairwise non-isomorphic irreducible
subrepresentations `(W_i)_{i : ι}` of `leftRegular ℂ G` such that:
1. `(leftRegular ℂ G).character = ∑ i, (dim W_i) • χ_{W_i}`,
2. `∑ i, (dim W_i)^2 = |G|`,
3. At EVERY `g : G` and `T : ℂ`:
   `∏_{O ∈ orbits(⟨g⟩ on G)} (1 - T ^ |O|)⁻¹ = ∏ i, (artinLocalFactor (W_i) g T) ^ (dim W_i)`,
4. Globally, for ANY Frobenius assignment `frob` and `1 < s.re`:
   `∏' p, (∏_{O ∈ orbits(⟨frob p⟩ on G)} (1 - p^{-|O| s})⁻¹) = ∏ i, (artinL S frob (W_i) s) ^ (dim W_i)`. -/
theorem dedekind_eq_prod_irrep_artinL (S : Finset ℕ) (frob : {p : ℕ // p.Prime ∧ p ∉ S} → G) :
    ∃ (ι : Type) (_ : Fintype ι) (W : ι → Subrepresentation (leftRegular ℂ G)),
      (∀ i, Representation.IsIrreducible (W i).toRepresentation) ∧
      (∀ i j, Nonempty (Representation.Equiv (W i).toRepresentation (W j).toRepresentation) → i = j) ∧
      (∀ g, (leftRegular ℂ G).character g =
        ∑ i : ι, (Module.finrank ℂ (W i).toSubmodule : ℂ) * (W i).toRepresentation.character g) ∧
      (∑ i : ι, (Module.finrank ℂ (W i).toSubmodule) ^ 2 = Fintype.card G) ∧
      (∀ g T, ∏ O : CycleOrbits g G, (1 - T ^ orbitSize g O)⁻¹ =
        ∏ i : ι, (artinLocalFactor (W i).toRepresentation g T) ^ Module.finrank ℂ (W i).toSubmodule) ∧
      (∀ s : ℂ, 1 < s.re →
        (∏' p : {p : ℕ // p.Prime ∧ p ∉ S},
          ∏ O : CycleOrbits (frob p) G, (1 - ((p.1 : ℂ) ^ (-s)) ^ orbitSize (frob p) O)⁻¹) =
        ∏ i : ι, (artinL S frob (W i).toRepresentation s) ^ Module.finrank ℂ (W i).toSubmodule) := by
  obtain ⟨k, U, hirr, hchar_sum, hfac_prod⟩ := exists_irrep_decomp_list (leftRegular ℂ G)
  let r : Fin k → Fin k → Prop :=
    fun a b => Nonempty (Representation.Equiv (U a).toRepresentation (U b).toRepresentation)
  let setoidR : Setoid (Fin k) :=
    { r := r
      iseqv :=
        { refl := fun a => ⟨Representation.Equiv.refl _⟩
          symm := fun ⟨φ⟩ => ⟨φ.symm⟩
          trans := fun ⟨φ⟩ ⟨ψ⟩ => ⟨φ.trans ψ⟩ } }
  let ι : Type := Quotient setoidR
  let repIdx : ι → Fin k := fun c => Quotient.out c
  let W : ι → Subrepresentation (leftRegular ℂ G) := fun c => U (repIdx c)
  let mult : ι → ℕ := fun c =>
    (Finset.univ.filter fun a : Fin k => Quotient.mk setoidR a = c).card
  have hW_irr : ∀ c : ι, Representation.IsIrreducible (W c).toRepresentation :=
    fun c => hirr (repIdx c)
  have hW_pair : ∀ c₁ c₂ : ι,
      Nonempty (Representation.Equiv (W c₁).toRepresentation (W c₂).toRepresentation) →
        c₁ = c₂ := by
    intro c₁ c₂ hne
    have hq : Quotient.mk setoidR (repIdx c₁) = Quotient.mk setoidR (repIdx c₂) :=
      Quotient.sound hne
    simpa [repIdx] using hq
  have hchar_grp : ∀ g : G,
      (leftRegular ℂ G).character g =
        ∑ c : ι, (mult c : ℂ) * (W c).toRepresentation.character g := by
    intro g
    rw [hchar_sum g]
    rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset ι))
      (g := Quotient.mk setoidR) (fun _ _ => Finset.mem_univ _)]
    apply Finset.sum_congr rfl
    intro c _
    have hconst : ∀ a ∈ Finset.univ.filter (fun a : Fin k => Quotient.mk setoidR a = c),
        (U a).toRepresentation.character g = (W c).toRepresentation.character g := by
      intro a ha
      have hrel : r a (repIdx c) :=
        Quotient.exact ((Finset.mem_filter.mp ha).2.trans (Quotient.out_eq c).symm)
      obtain ⟨φ⟩ := hrel
      exact congr_fun (Representation.char_iso φ) g
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  have hfac_grp : ∀ g T,
      artinLocalFactor (leftRegular ℂ G) g T =
        ∏ c : ι, (artinLocalFactor (W c).toRepresentation g T) ^ mult c := by
    intro g T
    rw [hfac_prod g T]
    rw [← Finset.prod_fiberwise_of_maps_to (t := (Finset.univ : Finset ι))
      (g := Quotient.mk setoidR) (fun _ _ => Finset.mem_univ _)]
    apply Finset.prod_congr rfl
    intro c _
    have hconst : ∀ a ∈ Finset.univ.filter (fun a : Fin k => Quotient.mk setoidR a = c),
        artinLocalFactor (U a).toRepresentation g T = artinLocalFactor (W c).toRepresentation g T := by
      intro a ha
      have hrel : r a (repIdx c) :=
        Quotient.exact ((Finset.mem_filter.mp ha).2.trans (Quotient.out_eq c).symm)
      obtain ⟨φ⟩ := hrel
      exact artinLocalFactor_iso φ g T
    rw [Finset.prod_congr rfl hconst, Finset.prod_const]
  -- Prove mult c = Module.finrank ℂ (W c).toSubmodule using character orthogonality
  have hmult_eq : ∀ c : ι, mult c = Module.finrank ℂ (W c).toSubmodule := by
    intro c
    have : Invertible (Nat.card G : ℂ) :=
      invertibleOfNonzero (Nat.cast_ne_zero.mpr (by rw [Nat.card_eq_fintype_card]; exact Fintype.card_ne_zero))
    have hlhs : (Nat.card G : ℂ)⁻¹ * ∑ g : G,
        (leftRegular ℂ G).character g * (W c).toRepresentation.character g⁻¹ =
        (Module.finrank ℂ (W c).toSubmodule : ℂ) := by
      simp_rw [leftRegular_character]
      rw [Finset.sum_eq_single (1 : G)]
      · simp only [ite_true, inv_one, Representation.char_one]
        rw [Nat.card_eq_fintype_card, ← mul_assoc,
          inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]
      · intro g _ hg
        simp [hg]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hrhs : (Nat.card G : ℂ)⁻¹ * ∑ g : G,
        (leftRegular ℂ G).character g * (W c).toRepresentation.character g⁻¹ =
        (mult c : ℂ) := by
      simp_rw [hchar_grp, Finset.sum_mul]
      rw [Finset.sum_comm, Finset.mul_sum]
      have hterm : ∀ c' : ι,
          (Nat.card G : ℂ)⁻¹ * ∑ g : G,
              (mult c' : ℂ) * (W c').toRepresentation.character g *
                (W c).toRepresentation.character g⁻¹ =
            if c' = c then (mult c' : ℂ) else 0 := by
        intro c'
        have hpull : (Nat.card G : ℂ)⁻¹ * ∑ g : G,
              (mult c' : ℂ) * (W c').toRepresentation.character g *
                (W c).toRepresentation.character g⁻¹ =
            (mult c' : ℂ) * ((Nat.card G : ℂ)⁻¹ * ∑ g : G,
              (W c').toRepresentation.character g * (W c).toRepresentation.character g⁻¹) := by
          simp_rw [mul_assoc]
          rw [← Finset.mul_sum]
          ring
        rw [hpull]
        have := hW_irr c'
        have := hW_irr c
        rw [Representation.char_orthonormal (W c').toRepresentation (W c).toRepresentation]
        by_cases hcc : c' = c
        · subst hcc
          rw [if_pos ⟨Representation.Equiv.refl _⟩, if_pos rfl]
          simp
        · have hne : ¬ Nonempty (Representation.Equiv (W c).toRepresentation (W c').toRepresentation) :=
            fun h => hcc (hW_pair c c' h).symm
          rw [if_neg hne, if_neg hcc]
          simp
      simp_rw [hterm]
      rw [Finset.sum_ite_eq']
      simp
    have hcast : (mult c : ℂ) = (Module.finrank ℂ (W c).toSubmodule : ℂ) := hrhs.symm.trans hlhs
    exact Nat.cast_injective hcast
  refine ⟨ι, inferInstance, W, hW_irr, hW_pair, ?_, ?_, ?_, ?_⟩
  · intro g
    rw [hchar_grp g]
    apply Finset.sum_congr rfl
    intro c _
    rw [hmult_eq c]
  · have h1 := hchar_grp 1
    rw [leftRegular_character 1, if_pos rfl] at h1
    have hcast : (Fintype.card G : ℂ) = ((∑ c : ι, (Module.finrank ℂ (W c).toSubmodule) ^ 2 : ℕ) : ℂ) := by
      rw [h1, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [hmult_eq c, Representation.char_one, Nat.cast_pow, sq]
    exact (Nat.cast_injective hcast).symm
  · intro g T
    rw [← artinLocalFactor_leftRegular_eq_prod_cycles g T, hfac_grp g T]
    apply Finset.prod_congr rfl
    intro c _
    rw [hmult_eq c]
  · intro s hs
    have hloc : ∀ p : {p : ℕ // p.Prime ∧ p ∉ S},
        (∏ O : CycleOrbits (frob p) G, (1 - ((p.1 : ℂ) ^ (-s)) ^ orbitSize (frob p) O)⁻¹) =
          ∏ c : ι, (artinLocalFactor (W c).toRepresentation (frob p) ((p.1 : ℂ) ^ (-s))) ^
            Module.finrank ℂ (W c).toSubmodule := by
      intro p
      rw [← artinLocalFactor_leftRegular_eq_prod_cycles (frob p) ((p.1 : ℂ) ^ (-s)),
        hfac_grp (frob p) ((p.1 : ℂ) ^ (-s))]
      apply Finset.prod_congr rfl
      intro c _
      rw [hmult_eq c]
    simp_rw [hloc]
    have hmult_pow : ∀ c : ι,
        Multipliable (fun p : {p : ℕ // p.Prime ∧ p ∉ S} =>
          (artinLocalFactor (W c).toRepresentation (frob p) ((p.1 : ℂ) ^ (-s))) ^
            Module.finrank ℂ (W c).toSubmodule) := fun c =>
      (artinL_multipliable S frob (W c).toRepresentation hs).pow (Module.finrank ℂ (W c).toSubmodule)
    rw [tprod_finset_prod_of_multipliable Finset.univ _ (fun c _ => hmult_pow c)]
    apply Finset.prod_congr rfl
    intro c _
    exact (artinL_multipliable S frob (W c).toRepresentation hs).tprod_pow
      (Module.finrank ℂ (W c).toSubmodule)

end RegularDecomposition

end GlobalArtinL

/-! ## Section 4: Concrete Non-Abelian `S_3` & General Dihedral `D_n` Artin Representations -/

section DihedralAndS3

open Classical

/-! ### 4.1 General Dihedral Groups `D_n` & Monomial Induction from `C_n` -/

section DihedralGeneral

/-- The index-2 cyclic rotation subgroup `C_n = {r i | i : ZMod n} ≤ DihedralGroup n`. -/
def rotationSubgroup (n : ℕ) : Subgroup (DihedralGroup n) where
  carrier := {g | ∃ i : ZMod n, g = DihedralGroup.r i}
  one_mem' := ⟨0, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨i + j, rfl⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨-i, rfl⟩

instance rotationSubgroup_normal (n : ℕ) : (rotationSubgroup n).Normal where
  conj_mem := by
    rintro _ ⟨i, rfl⟩ (j | j)
    · exact ⟨i, by simp [DihedralGroup.r_mul_r, DihedralGroup.inv_r]⟩
    · exact ⟨-i, by simp [DihedralGroup.sr_mul_r, DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr]⟩

/-- Extract the rotation angle `i : ZMod n` of an element of `rotationSubgroup n`. -/
def rotAngle {n : ℕ} (x : rotationSubgroup n) : ZMod n :=
  match x.1, x.2 with
  | DihedralGroup.r i, _ => i
  | DihedralGroup.sr _, h => absurd h (by rintro ⟨i, hi⟩; cases hi)

@[simp]
lemma rotAngle_r {n : ℕ} (i : ZMod n) :
    rotAngle ⟨DihedralGroup.r i, ⟨i, rfl⟩⟩ = i := rfl

lemma rotAngle_mul {n : ℕ} (x y : rotationSubgroup n) :
    rotAngle (x * y) = rotAngle x + rotAngle y := by
  rcases x with ⟨g₁, ⟨i, rfl⟩⟩
  rcases y with ⟨g₂, ⟨j, rfl⟩⟩
  rfl

/-- Helper exponential `ω_{n, k}(i) = exp(2πi · k · i.val / n)` on `ZMod n`. -/
def dihedralPhase (n : ℕ) (k : ℤ) (i : ZMod n) : ℂ :=
  (primRoot n) ^ (k * (i.val : ℤ))

lemma dihedralPhase_ne_zero (n : ℕ) (k : ℤ) (i : ZMod n) : dihedralPhase n k i ≠ 0 :=
  zpow_ne_zero _ (primRoot_ne_zero n)

lemma dihedralPhase_zero (n : ℕ) (k : ℤ) : dihedralPhase n k 0 = 1 := by
  simp [dihedralPhase]

lemma dihedralPhase_add {n : ℕ} (hn : 0 < n) [NeZero n] (k : ℤ) (i j : ZMod n) :
    dihedralPhase n k (i + j) = dihedralPhase n k i * dihedralPhase n k j := by
  unfold dihedralPhase
  rw [← zpow_add₀ (primRoot_ne_zero n)]
  have hval : (i + j).val = (i.val + j.val) % n := ZMod.val_add i j
  have hdiv : ((i.val + j.val : ℕ) : ℤ) =
      (n : ℤ) * (((i.val + j.val) / n : ℕ) : ℤ) + (((i.val + j.val) % n : ℕ) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod (i.val + j.val) n).symm
  have hdiv' : (i.val : ℤ) + (j.val : ℤ) =
      (n : ℤ) * (((i.val + j.val) / n : ℕ) : ℤ) + ((i + j).val : ℤ) := by
    rw [hval]
    exact_mod_cast hdiv
  have hsum : k * (i.val : ℤ) + k * (j.val : ℤ) =
      k * ((i + j).val : ℤ) + (n : ℤ) * (k * (((i.val + j.val) / n : ℕ) : ℤ)) := by
    linear_combination k * hdiv'
  have htriv : (primRoot n) ^ ((n : ℤ) * (k * (((i.val + j.val) / n : ℕ) : ℤ))) = 1 := by
    rw [zpow_mul, zpow_natCast, primRoot_pow_eq_one hn, one_zpow]
  rw [hsum, zpow_add₀ (primRoot_ne_zero n), htriv, mul_one]

lemma dihedralPhase_neg {n : ℕ} (hn : 0 < n) [NeZero n] (k : ℤ) (i : ZMod n) :
    dihedralPhase n k (-i) = (dihedralPhase n k i)⁻¹ := by
  have h := dihedralPhase_add hn k (-i) i
  rw [neg_add_cancel, dihedralPhase_zero] at h
  exact eq_inv_of_mul_eq_one_left h.symm

lemma dihedralPhase_sub {n : ℕ} (hn : 0 < n) [NeZero n] (k : ℤ) (i j : ZMod n) :
    dihedralPhase n k (i - j) = dihedralPhase n k i * (dihedralPhase n k j)⁻¹ := by
  rw [sub_eq_add_neg, dihedralPhase_add hn k i (-j), dihedralPhase_neg hn k j]

/-- 1-dimensional character `χ_k : C_n →* ℂˣ` sending `r i ↦ exp(2πi · k · i / n)`. -/
def dihedralRotChar (n : ℕ) (hn : 0 < n) [NeZero n] (k : ℤ) : rotationSubgroup n →* ℂˣ where
  toFun x := Units.mk0 (dihedralPhase n k (rotAngle x)) (dihedralPhase_ne_zero n k _)
  map_one' := by
    apply Units.ext
    have h1 : (1 : rotationSubgroup n) = ⟨DihedralGroup.r 0, ⟨0, rfl⟩⟩ := rfl
    change dihedralPhase n k (rotAngle (1 : rotationSubgroup n)) = 1
    rw [h1, rotAngle_r, dihedralPhase_zero]
  map_mul' x y := by
    apply Units.ext
    change dihedralPhase n k (rotAngle (x * y)) =
      dihedralPhase n k (rotAngle x) * dihedralPhase n k (rotAngle y)
    rw [rotAngle_mul, dihedralPhase_add hn]

/-- Explicit 2-dimensional complex representation `dihedralRep2 n hn k` of `DihedralGroup n`:
- `r i` acts by `diag(ω^i, ω^{-i})`,
- `sr i` acts by anti-diagonal `[[0, ω^{-i}], [ω^i, 0]]`. -/
def dihedralRep2 (n : ℕ) (hn : 0 < n) [NeZero n] (k : ℤ) :
    Representation ℂ (DihedralGroup n) (Fin 2 → ℂ) where
  toFun g := match g with
    | DihedralGroup.r i =>
      { toFun := fun v => ![dihedralPhase n k i * v 0, (dihedralPhase n k i)⁻¹ * v 1]
        map_add' := fun v w => by ext a; fin_cases a <;> simp [mul_add]
        map_smul' := fun c v => by ext a; fin_cases a <;> simp [mul_left_comm] }
    | DihedralGroup.sr i =>
      { toFun := fun v => ![(dihedralPhase n k i)⁻¹ * v 1, dihedralPhase n k i * v 0]
        map_add' := fun v w => by ext a; fin_cases a <;> simp [mul_add]
        map_smul' := fun c v => by ext a; fin_cases a <;> simp [mul_left_comm] }
  map_one' := by
    refine LinearMap.ext fun v => funext fun a => ?_
    change (![dihedralPhase n k 0 * v 0, (dihedralPhase n k 0)⁻¹ * v 1]) a = v a
    fin_cases a <;> simp [dihedralPhase_zero]
  map_mul' g₁ g₂ := by
    refine LinearMap.ext fun v => funext fun a => ?_
    cases g₁ with
    | r i =>
      cases g₂ with
      | r j =>
        change (![dihedralPhase n k (i + j) * v 0, (dihedralPhase n k (i + j))⁻¹ * v 1]) a =
          (![dihedralPhase n k i * (dihedralPhase n k j * v 0),
            (dihedralPhase n k i)⁻¹ * ((dihedralPhase n k j)⁻¹ * v 1)]) a
        fin_cases a
        · simp [dihedralPhase_add hn, mul_assoc]
        · simp [dihedralPhase_add hn, mul_comm, mul_left_comm]
      | sr j =>
        change (![(dihedralPhase n k (j - i))⁻¹ * v 1, dihedralPhase n k (j - i) * v 0]) a =
          (![dihedralPhase n k i * ((dihedralPhase n k j)⁻¹ * v 1),
            (dihedralPhase n k i)⁻¹ * (dihedralPhase n k j * v 0)]) a
        fin_cases a
        · simp [dihedralPhase_sub hn, mul_assoc]
        · simp [dihedralPhase_sub hn, mul_comm, mul_left_comm]
    | sr i =>
      cases g₂ with
      | r j =>
        change (![(dihedralPhase n k (i + j))⁻¹ * v 1, dihedralPhase n k (i + j) * v 0]) a =
          (![(dihedralPhase n k i)⁻¹ * ((dihedralPhase n k j)⁻¹ * v 1),
            dihedralPhase n k i * (dihedralPhase n k j * v 0)]) a
        fin_cases a
        · simp [dihedralPhase_add hn, mul_comm, mul_left_comm]
        · simp [dihedralPhase_add hn, mul_assoc]
      | sr j =>
        change (![dihedralPhase n k (j - i) * v 0, (dihedralPhase n k (j - i))⁻¹ * v 1]) a =
          (![(dihedralPhase n k i)⁻¹ * (dihedralPhase n k j * v 0),
            dihedralPhase n k i * ((dihedralPhase n k j)⁻¹ * v 1)]) a
        fin_cases a
        · simp [dihedralPhase_sub hn, mul_comm, mul_left_comm]
        · simp [dihedralPhase_sub hn, mul_assoc]

@[simp]
lemma dihedralRep2_r_apply {n : ℕ} (hn : 0 < n) [NeZero n] (k : ℤ) (i : ZMod n) (v : Fin 2 → ℂ) :
    dihedralRep2 n hn k (DihedralGroup.r i) v =
      ![dihedralPhase n k i * v 0, (dihedralPhase n k i)⁻¹ * v 1] := rfl

@[simp]
lemma dihedralRep2_sr_apply {n : ℕ} (hn : 0 < n) [NeZero n] (k : ℤ) (i : ZMod n) (v : Fin 2 → ℂ) :
    dihedralRep2 n hn k (DihedralGroup.sr i) v =
      ![(dihedralPhase n k i)⁻¹ * v 1, dihedralPhase n k i * v 0] := rfl

/-- Exact character of `dihedralRep2 n hn k` on rotations and reflections. -/
theorem dihedralRep2_character_r {n : ℕ} (hn : 0 < n) [NeZero n] (k : ℤ) (i : ZMod n) :
    (dihedralRep2 n hn k).character (DihedralGroup.r i) =
      dihedralPhase n k i + (dihedralPhase n k i)⁻¹ := by
  unfold Representation.character
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin 2))]
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]

theorem dihedralRep2_character_sr {n : ℕ} (hn : 0 < n) [NeZero n] (k : ℤ) (i : ZMod n) :
    (dihedralRep2 n hn k).character (DihedralGroup.sr i) = 0 := by
  unfold Representation.character
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin 2))]
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]

/-- **Irreducibility of 2D Dihedral Representations**: whenever `ω_{n,k}(1)^2 ≠ 1`
(i.e. `2k ≢ 0 [MOD n]`), `dihedralRep2 n hn k` is irreducible! -/
theorem dihedralRep2_isIrreducible {n : ℕ} (hn : 0 < n) [NeZero n] (k : ℤ)
    (hk : (dihedralPhase n k 1) ^ 2 ≠ 1) :
    Representation.IsIrreducible (dihedralRep2 n hn k) := by
  have hbot_ne_top : (⊥ : Subrepresentation (dihedralRep2 n hn k)) ≠ ⊤ := by
    intro heq
    have h1 : (⊥ : Submodule ℂ (Fin 2 → ℂ)) = ⊤ := congr_arg Subrepresentation.toSubmodule heq
    exact bot_ne_top h1
  have : Nontrivial (Subrepresentation (dihedralRep2 n hn k)) := ⟨⟨⊥, ⊤, hbot_ne_top⟩⟩
  refine ⟨fun S => ?_⟩
  by_cases hS : S = ⊥
  · exact Or.inl hS
  · right
    have hex : ∃ v : Fin 2 → ℂ, v ∈ S.toSubmodule ∧ v ≠ 0 := by
      by_contra hnone
      push Not at hnone
      apply hS
      apply Subrepresentation.ext
      change S.toSubmodule = ⊥
      rw [eq_bot_iff]
      intro v hv
      exact hnone v hv
    obtain ⟨v, hvS, hv0⟩ := hex
    let μ : ℂ := dihedralPhase n k 1
    have hμ_ne0 : μ ≠ 0 := dihedralPhase_ne_zero n k 1
    have hdiff_ne : μ - μ⁻¹ ≠ 0 := by
      intro h0
      have heq : μ = μ⁻¹ := sub_eq_zero.mp h0
      have hsq : μ ^ 2 = 1 := by
        rw [sq]
        conv_rhs => rw [← mul_inv_cancel₀ hμ_ne0]
        rw [← heq]
      exact hk hsq
    let e0 : Fin 2 → ℂ := ![1, 0]
    let e1 : Fin 2 → ℂ := ![0, 1]
    have hrv : dihedralRep2 n hn k (DihedralGroup.r 1) v ∈ S.toSubmodule :=
      S.apply_mem_toSubmodule (DihedralGroup.r 1) hvS
    have hproj0 : ((μ - μ⁻¹) * v 0) • e0 ∈ S.toSubmodule := by
      have hmem : dihedralRep2 n hn k (DihedralGroup.r 1) v - μ⁻¹ • v ∈ S.toSubmodule :=
        S.toSubmodule.sub_mem hrv (S.toSubmodule.smul_mem μ⁻¹ hvS)
      convert hmem using 1
      ext a; fin_cases a
      · simp [e0, μ]; ring
      · simp [e0, μ]
    have hproj1 : ((μ - μ⁻¹) * v 1) • e1 ∈ S.toSubmodule := by
      have hmem : μ • v - dihedralRep2 n hn k (DihedralGroup.r 1) v ∈ S.toSubmodule :=
        S.toSubmodule.sub_mem (S.toSubmodule.smul_mem μ hvS) hrv
      convert hmem using 1
      ext a; fin_cases a
      · simp [e1, μ]
      · simp [e1, μ]; ring
    have he0_swap : dihedralRep2 n hn k (DihedralGroup.sr 0) e0 = e1 := by
      ext a; fin_cases a <;> simp [e0, e1, dihedralPhase_zero]
    have he1_swap : dihedralRep2 n hn k (DihedralGroup.sr 0) e1 = e0 := by
      ext a; fin_cases a <;> simp [e0, e1, dihedralPhase_zero]
    have hboth : e0 ∈ S.toSubmodule ∧ e1 ∈ S.toSubmodule := by
      by_cases hv00 : v 0 ≠ 0
      · have hc : (μ - μ⁻¹) * v 0 ≠ 0 := mul_ne_zero hdiff_ne hv00
        have he0 : e0 ∈ S.toSubmodule := by
          have := S.toSubmodule.smul_mem ((μ - μ⁻¹) * v 0)⁻¹ hproj0
          rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
        have he1 : e1 ∈ S.toSubmodule := by
          rw [← he0_swap]
          exact S.apply_mem_toSubmodule (DihedralGroup.sr 0) he0
        exact ⟨he0, he1⟩
      · push Not at hv00
        have hv01 : v 1 ≠ 0 := by
          intro h1
          apply hv0
          ext a; fin_cases a <;> assumption
        have hc : (μ - μ⁻¹) * v 1 ≠ 0 := mul_ne_zero hdiff_ne hv01
        have he1 : e1 ∈ S.toSubmodule := by
          have := S.toSubmodule.smul_mem ((μ - μ⁻¹) * v 1)⁻¹ hproj1
          rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
        have he0 : e0 ∈ S.toSubmodule := by
          rw [← he1_swap]
          exact S.apply_mem_toSubmodule (DihedralGroup.sr 0) he1
        exact ⟨he0, he1⟩
    apply Subrepresentation.ext
    change S.toSubmodule = ⊤
    rw [eq_top_iff]
    intro w _
    have hw : w = w 0 • e0 + w 1 • e1 := by
      ext a; fin_cases a <;> simp [e0, e1]
    rw [hw]
    exact S.toSubmodule.add_mem (S.toSubmodule.smul_mem _ hboth.1)
      (S.toSubmodule.smul_mem _ hboth.2)

/-- **GENERAL DIHEDRAL MONOMIAL INDUCTION (`dihedral_irrep_ind_cyclic`)**:
For EVERY `n > 0` and EVERY `k : ℤ`, the 2-dimensional representation `dihedralRep2 n hn k`
of `DihedralGroup n` is canonically isomorphic to the induced representation
`Ind_{C_n}^{D_n} χ_k` from the index-2 cyclic rotation subgroup `C_n = rotationSubgroup n`! -/
def dihedral_irrep_ind_cyclic (n : ℕ) (hn : 0 < n) [NeZero n] (k : ℤ) :
    Representation.Equiv (dihedralRep2 n hn k)
      (Representation.ind (rotationSubgroup n).subtype (repOfChar (dihedralRotChar n hn k))) := by
  let H := rotationSubgroup n
  let χ := dihedralRotChar n hn k
  let ψ := repOfChar χ
  let e0 : Representation.IndV H.subtype ψ :=
    Representation.IndV.mk H.subtype ψ (DihedralGroup.r 0) 1
  let e1 : Representation.IndV H.subtype ψ :=
    Representation.IndV.mk H.subtype ψ (DihedralGroup.sr 0) 1
  -- Key coinvariant relation: IndV.mk (h * x) 1 = (χ h)⁻¹ • IndV.mk x 1
  have hmk_mul : ∀ (h : H) (x : DihedralGroup n),
      Representation.IndV.mk H.subtype ψ ((h : DihedralGroup n) * x) (1 : ℂ) =
        ((χ h : ℂ)⁻¹) • Representation.IndV.mk H.subtype ψ x (1 : ℂ) := by
    intro h x
    have hcoinv := Representation.Coinvariants.mk_self_apply
      (ρ := Representation.tprod ((leftRegular ℂ (DihedralGroup n)).comp H.subtype) ψ) h
      (MonoidAlgebra.single x (1 : ℂ) ⊗ₜ[ℂ] ((χ h : ℂ)⁻¹ : ℂ))
    have hlr : (leftRegular ℂ (DihedralGroup n)) (h : DihedralGroup n)
        (MonoidAlgebra.single x (1 : ℂ)) =
        MonoidAlgebra.single ((h : DihedralGroup n) * x) (1 : ℂ) :=
      Representation.ofMulAction_single (h : DihedralGroup n) x (1 : ℂ)
    have hψ : ψ h ((χ h : ℂ)⁻¹ : ℂ) = 1 := by
      simp [ψ]
    have h1 : Representation.IndV.mk H.subtype ψ ((h : DihedralGroup n) * x) (1 : ℂ) =
        Representation.IndV.mk H.subtype ψ x ((χ h : ℂ)⁻¹ : ℂ) := by
      simpa [Representation.IndV.mk, Representation.tprod_apply, hlr, hψ] using hcoinv
    rw [h1]
    have hsmul : ((χ h : ℂ)⁻¹ : ℂ) = ((χ h : ℂ)⁻¹) • (1 : ℂ) := by simp
    conv_lhs => rw [hsmul]
    rw [map_smul]
  -- Forward linear map (Fin 2 → ℂ) →ₗ[ℂ] IndV
  let fwd : (Fin 2 → ℂ) →ₗ[ℂ] Representation.IndV H.subtype ψ :=
    { toFun := fun v => v 0 • e0 + v 1 • e1
      map_add' := fun v w => by simp [add_smul]; abel
      map_smul' := fun c v => by simp [smul_add, smul_smul] }
  -- Check intertwining on all g : DihedralGroup n
  have hinter : ∀ g : DihedralGroup n,
      fwd ∘ₗ dihedralRep2 n hn k g = (Representation.ind H.subtype ψ) g ∘ₗ fwd := by
    intro g
    refine LinearMap.ext fun v => ?_
    change fwd (dihedralRep2 n hn k g v) =
      (Representation.ind H.subtype ψ) g (v 0 • e0 + v 1 • e1)
    rw [map_add, map_smul, map_smul]
    have hind_mk : ∀ x : DihedralGroup n,
        (Representation.ind H.subtype ψ) g (Representation.IndV.mk H.subtype ψ x 1) =
          Representation.IndV.mk H.subtype ψ (x * g⁻¹) 1 := fun x => by
      simp [Representation.ind, Representation.IndV.mk]
    cases g with
    | r i =>
      have he0_act : (Representation.ind H.subtype ψ) (DihedralGroup.r i) e0 =
          dihedralPhase n k i • e0 := by
        dsimp only [e0]
        rw [hind_mk]
        have hmul : DihedralGroup.r 0 * (DihedralGroup.r i)⁻¹ =
            ((⟨DihedralGroup.r (-i), ⟨-i, rfl⟩⟩ : H) : DihedralGroup n) * DihedralGroup.r 0 := by
          simp [DihedralGroup.inv_r]
        rw [hmul, hmk_mul]
        congr 1
        change (dihedralPhase n k (-i))⁻¹ = dihedralPhase n k i
        rw [dihedralPhase_neg hn, inv_inv]
      have he1_act : (Representation.ind H.subtype ψ) (DihedralGroup.r i) e1 =
          (dihedralPhase n k i)⁻¹ • e1 := by
        dsimp only [e1]
        rw [hind_mk]
        have hmul : DihedralGroup.sr 0 * (DihedralGroup.r i)⁻¹ =
            ((⟨DihedralGroup.r i, ⟨i, rfl⟩⟩ : H) : DihedralGroup n) * DihedralGroup.sr 0 := by
          simp [DihedralGroup.inv_r, DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr]
        rw [hmul, hmk_mul]
        rfl
      rw [he0_act, he1_act, smul_smul, smul_smul, dihedralRep2_r_apply]
      simp [fwd, mul_comm]
    | sr i =>
      have he0_act : (Representation.ind H.subtype ψ) (DihedralGroup.sr i) e0 =
          dihedralPhase n k i • e1 := by
        dsimp only [e0]
        rw [hind_mk]
        have hmul : DihedralGroup.r 0 * (DihedralGroup.sr i)⁻¹ =
            ((⟨DihedralGroup.r (-i), ⟨-i, rfl⟩⟩ : H) : DihedralGroup n) * DihedralGroup.sr 0 := by
          simp [DihedralGroup.inv_sr, DihedralGroup.r_mul_sr]
        rw [hmul, hmk_mul]
        congr 1
        change (dihedralPhase n k (-i))⁻¹ = dihedralPhase n k i
        rw [dihedralPhase_neg hn, inv_inv]
      have he1_act : (Representation.ind H.subtype ψ) (DihedralGroup.sr i) e1 =
          (dihedralPhase n k i)⁻¹ • e0 := by
        dsimp only [e1]
        rw [hind_mk]
        have hmul : DihedralGroup.sr 0 * (DihedralGroup.sr i)⁻¹ =
            ((⟨DihedralGroup.r i, ⟨i, rfl⟩⟩ : H) : DihedralGroup n) * DihedralGroup.r 0 := by
          simp [DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr]
        rw [hmul, hmk_mul]
        rfl
      rw [he0_act, he1_act, smul_smul, smul_smul, dihedralRep2_sr_apply]
      simp only [fwd, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      rw [add_comm]
      congr 1 <;> rw [mul_comm]
  -- Prove fwd is bijective via indEquivIndModel
  let eMod := indEquivIndModel H ψ
  have hcoset_ne : ((DihedralGroup.r 0 : DihedralGroup n) : DihedralGroup n ⧸ H) ≠
      ((DihedralGroup.sr 0 : DihedralGroup n) : DihedralGroup n ⧸ H) := by
    intro heq
    have hrel := QuotientGroup.leftRel_apply.mp (Quotient.exact heq)
    rcases hrel with ⟨i, hi⟩
    simp at hi
  have hcoset_cases : ∀ q : DihedralGroup n ⧸ H,
      q = ((DihedralGroup.r 0 : DihedralGroup n) : DihedralGroup n ⧸ H) ∨
      q = ((DihedralGroup.sr 0 : DihedralGroup n) : DihedralGroup n ⧸ H) := by
    intro q
    obtain ⟨g, rfl⟩ := Quotient.exists_rep q
    cases g with
    | r i =>
      left
      exact Quotient.sound (show (QuotientGroup.leftRel H) (DihedralGroup.r i) (DihedralGroup.r 0) by
        rw [QuotientGroup.leftRel_apply]
        exact ⟨-i, by simp [DihedralGroup.inv_r]⟩)
    | sr i =>
      right
      exact Quotient.sound (show (QuotientGroup.leftRel H) (DihedralGroup.sr i) (DihedralGroup.sr 0) by
        rw [QuotientGroup.leftRel_apply]
        exact ⟨-i, by simp [DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr]⟩)
  have hcard_quot : Fintype.card (DihedralGroup n ⧸ H) = 2 := by
    let e2 : Fin 2 ≃ (DihedralGroup n ⧸ H) :=
      Equiv.ofBijective
        (fun a => if a = 0 then ((DihedralGroup.r 0 : DihedralGroup n) : DihedralGroup n ⧸ H)
          else ((DihedralGroup.sr 0 : DihedralGroup n) : DihedralGroup n ⧸ H))
        ⟨by
          intro a b hab
          fin_cases a <;> fin_cases b
          · rfl
          · exact absurd hab hcoset_ne
          · exact absurd hab.symm hcoset_ne
          · rfl,
         by
          intro q
          rcases hcoset_cases q with hq | hq
          · exact ⟨0, by simp [hq]⟩
          · exact ⟨1, by simp [hq]⟩⟩
    exact (Fintype.card_congr e2).symm.trans (Fintype.card_fin 2)
  have hsurj : Function.Surjective fwd := by
    intro y
    have hspan : ∀ x : DihedralGroup n, ∀ c : ℂ,
        Representation.IndV.mk H.subtype ψ x c ∈ LinearMap.range fwd := by
      intro x c
      have hsc : Representation.IndV.mk H.subtype ψ x c =
          c • Representation.IndV.mk H.subtype ψ x 1 := by
        have hc : c = c • (1 : ℂ) := by simp
        conv_lhs => rw [hc]
        rw [map_smul]
      rw [hsc]
      apply Submodule.smul_mem
      cases x with
      | r i =>
        have hmul : DihedralGroup.r i =
            ((⟨DihedralGroup.r i, ⟨i, rfl⟩⟩ : H) : DihedralGroup n) * DihedralGroup.r 0 := by
          simp
        rw [hmul, hmk_mul]
        refine ⟨![((χ ⟨DihedralGroup.r i, ⟨i, rfl⟩⟩ : ℂ)⁻¹), 0], ?_⟩
        simp [fwd, e0]
      | sr i =>
        have hmul : DihedralGroup.sr i =
            ((⟨DihedralGroup.r (-i), ⟨-i, rfl⟩⟩ : H) : DihedralGroup n) * DihedralGroup.sr 0 := by
          simp [DihedralGroup.r_mul_sr]
        rw [hmul, hmk_mul]
        refine ⟨![0, ((χ ⟨DihedralGroup.r (-i), ⟨-i, rfl⟩⟩ : ℂ)⁻¹)], ?_⟩
        simp [fwd, e1]
    have hrange_top : LinearMap.range fwd = ⊤ := by
      rw [eq_top_iff]
      intro z _
      let π : Representation.IndV H.subtype ψ →ₗ[ℂ]
          (Representation.IndV H.subtype ψ ⧸ LinearMap.range fwd) :=
        Submodule.mkQ (LinearMap.range fwd)
      have hπ0 : π = 0 := by
        apply Representation.IndV.hom_ext
        intro x
        refine LinearMap.ext fun c => ?_
        change Submodule.Quotient.mk (Representation.IndV.mk H.subtype ψ x c) = 0
        rw [Submodule.Quotient.mk_eq_zero]
        exact hspan x c
      have hz0 : π z = 0 := congr_arg (fun f : _ →ₗ[ℂ] _ => f z) hπ0
      exact (Submodule.Quotient.mk_eq_zero _).mp hz0
    have hy : y ∈ LinearMap.range fwd := hrange_top ▸ Submodule.mem_top
    exact hy
  have hdim_eq : Module.finrank ℂ (Fin 2 → ℂ) = Module.finrank ℂ (Representation.IndV H.subtype ψ) := by
    rw [Module.finrank_fin_fun, LinearEquiv.finrank_eq eMod.toLinearEquiv,
      Module.finrank_pi_fintype, Finset.sum_const, Module.finrank_self, smul_eq_mul, mul_one,
      Finset.card_univ, hcard_quot]
  have hbij : Function.Bijective fwd :=
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim_eq).mpr hsurj, hsurj⟩
  exact Representation.Equiv.mk (LinearEquiv.ofBijective fwd hbij) hinter

/-- Exact local Artin Euler factors of `dihedralRep2 n hn k` on rotations and reflections,
and reduction by Artin inductivity to 1D abelian Euler factors over `C_n`. -/
theorem artinLocalFactor_dihedralRep2_r {n : ℕ} (hn : 0 < n) [NeZero n] (k : ℤ)
    (i : ZMod n) (T : ℂ) :
    artinLocalFactor (dihedralRep2 n hn k) (DihedralGroup.r i) T =
      (1 - dihedralPhase n k i * T)⁻¹ * (1 - (dihedralPhase n k i)⁻¹ * T)⁻¹ := by
  unfold artinLocalFactor artinLocalPoly
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (Fin 2)), Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, LinearMap.sub_apply, Module.End.one_apply,
    LinearMap.smul_apply, dihedralRep2_r_apply, Pi.basisFun_apply, Pi.basisFun_repr,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp [mul_comm]

theorem artinLocalFactor_dihedralRep2_sr {n : ℕ} (hn : 0 < n) [NeZero n] (k : ℤ)
    (i : ZMod n) (T : ℂ) :
    artinLocalFactor (dihedralRep2 n hn k) (DihedralGroup.sr i) T = (1 - T ^ 2)⁻¹ := by
  unfold artinLocalFactor artinLocalPoly
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ (Fin 2)), Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, LinearMap.sub_apply, Module.End.one_apply,
    LinearMap.smul_apply, dihedralRep2_sr_apply, Pi.basisFun_apply, Pi.basisFun_repr,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hne : dihedralPhase n k i ≠ 0 := dihedralPhase_ne_zero n k i
  congr 1
  simp only [Pi.single_apply, Fin.isValue, zero_ne_one, one_ne_zero,
    ite_true, ite_false, mul_zero, mul_one, zero_sub, mul_neg, neg_mul, sub_neg_eq_add,
    Matrix.cons_val_zero, Matrix.cons_val_one, sub_zero]
  field_simp [hne]
  ring

/-- **Dihedral Artin Inductivity**: every 2D dihedral Artin local Euler factor equals the
1D abelian induced Euler factor over the index-2 cyclic subgroup `C_n = rotationSubgroup n`. -/
theorem artinLocalFactor_dihedralRep2_eq_ind {n : ℕ} (hn : 0 < n) [NeZero n] (k : ℤ)
    (g : DihedralGroup n) (T : ℂ) :
    artinLocalFactor (dihedralRep2 n hn k) g T =
      ∏ O : CycleOrbits g (DihedralGroup n ⧸ rotationSubgroup n),
        (1 - (dihedralRotChar n hn k (orbitMonodromy (rotationSubgroup n) g O) : ℂ) *
          T ^ orbitSize g O)⁻¹ := by
  rw [artinLocalFactor_iso (dihedral_irrep_ind_cyclic n hn k) g T,
    artinLocalFactor_ind (rotationSubgroup n) (repOfChar (dihedralRotChar n hn k)) g T]
  apply Finset.prod_congr rfl
  intro O _
  exact artinLocalFactor_repOfChar (dihedralRotChar n hn k) _ _

end DihedralGeneral

/-! ### 4.2 Concrete Non-Abelian `S_3 ≃ D_3`, Character Table, & Artin–Brauer–Kuroda Factorization -/

section ConcreteS3

/-- Explicit homomorphism `D_3 →* S_3 = Equiv.Perm (Fin 3)` sending `r i ↦ (x ↦ x + i mod 3)`
and `sr i ↦ (x ↦ -x - i mod 3)`. -/
def d3ToS3Fun : DihedralGroup 3 → Equiv.Perm (Fin 3)
  | DihedralGroup.r i =>
    { toFun := fun x => ⟨(x.1 + i.val) % 3, Nat.mod_lt _ (by decide)⟩
      invFun := fun x => ⟨(x.1 + (3 - i.val)) % 3, Nat.mod_lt _ (by decide)⟩
      left_inv := fun x => by
        have hx := x.2; have hi : i.val < 3 := i.val_lt
        ext; dsimp; omega
      right_inv := fun x => by
        have hx := x.2; have hi : i.val < 3 := i.val_lt
        ext; dsimp; omega }
  | DihedralGroup.sr i =>
    { toFun := fun x => ⟨(6 - x.1 - i.val) % 3, Nat.mod_lt _ (by decide)⟩
      invFun := fun x => ⟨(6 - x.1 - i.val) % 3, Nat.mod_lt _ (by decide)⟩
      left_inv := fun x => by
        have hx := x.2; have hi : i.val < 3 := i.val_lt
        ext; dsimp; omega
      right_inv := fun x => by
        have hx := x.2; have hi : i.val < 3 := i.val_lt
        ext; dsimp; omega }

def d3ToS3 : DihedralGroup 3 →* Equiv.Perm (Fin 3) where
  toFun := d3ToS3Fun
  map_one' := by decide
  map_mul' := by decide

lemma d3ToS3_bijective : Function.Bijective d3ToS3 := by
  constructor
  · decide
  · decide

/-- Concrete group isomorphism `S_3 = Equiv.Perm (Fin 3) ≃* DihedralGroup 3`. -/
def s3EquivD3 : Equiv.Perm (Fin 3) ≃* DihedralGroup 3 :=
  (MulEquiv.ofBijective d3ToS3 d3ToS3_bijective).symm

/-- The trivial 1-dimensional representation of `S_3`. -/
def s3Triv : Representation ℂ (Equiv.Perm (Fin 3)) ℂ :=
  Representation.trivial ℂ (Equiv.Perm (Fin 3)) ℂ

/-- The sign character `sgn : S_3 →* ℂˣ`. -/
def s3SignChar : Equiv.Perm (Fin 3) →* ℂˣ :=
  (Units.map (Int.castRingHom ℂ).toMonoidHom).comp Equiv.Perm.sign

/-- The 1-dimensional sign representation of `S_3`. -/
def s3Sign : Representation ℂ (Equiv.Perm (Fin 3)) ℂ :=
  repOfChar s3SignChar

/-- The 2-dimensional irreducible representation `ρ₂` of `S_3 ≃ D_3`. -/
def s3Rho2 : Representation ℂ (Equiv.Perm (Fin 3)) (Fin 2 → ℂ) :=
  (dihedralRep2 3 (by norm_num) 1).comp s3EquivD3.toMonoidHom

/-- The cube-root identity `ω + ω⁻¹ = -1` for `ω = primRoot 3 = exp(2πi/3)`. -/
lemma primRoot3_add_inv : primRoot 3 + (primRoot 3)⁻¹ = -1 := by
  have h3 : (primRoot 3) ^ 3 = 1 := primRoot_pow_eq_one (by norm_num)
  have hne : primRoot 3 ≠ 1 := by
    intro h1
    have h0 : (⟨1, by decide⟩ : Fin 3) = ⟨0, by decide⟩ :=
      primRoot_pow_injective (N := 3) (by norm_num) (by simpa using h1)
    exact absurd (congr_arg Fin.val h0) (by decide)
  have hfac : (primRoot 3 - 1) * ((primRoot 3) ^ 2 + primRoot 3 + 1) = 0 := by
    calc (primRoot 3 - 1) * ((primRoot 3) ^ 2 + primRoot 3 + 1)
        = (primRoot 3) ^ 3 - 1 := by ring
    _ = 0 := by rw [h3, sub_self]
  have hquad : (primRoot 3) ^ 2 + primRoot 3 + 1 = 0 :=
    (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hne)
  have hinv : (primRoot 3)⁻¹ = (primRoot 3) ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    calc primRoot 3 * (primRoot 3) ^ 2 = (primRoot 3) ^ 3 := by ring
    _ = 1 := h3
  rw [hinv]
  linear_combination hquad

lemma dihedralPhase_3_one : dihedralPhase 3 1 1 = primRoot 3 := by
  unfold dihedralPhase
  have h1 : (1 : ZMod 3).val = 1 := rfl
  rw [h1]
  simp

lemma dihedralPhase_3_two : dihedralPhase 3 1 2 = (primRoot 3)⁻¹ := by
  have h21 : (2 : ZMod 3) = -(1 : ZMod 3) := by decide
  rw [h21, dihedralPhase_neg (by norm_num), dihedralPhase_3_one]

lemma primRoot3_sq_ne_one : (dihedralPhase 3 1 1) ^ 2 ≠ 1 := by
  rw [dihedralPhase_3_one]
  intro h2
  have h0 : (⟨2, by decide⟩ : Fin 3) = ⟨0, by decide⟩ :=
    primRoot_pow_injective (N := 3) (by norm_num) (by simpa using h2)
  exact absurd (congr_arg Fin.val h0) (by decide)

/-- Irreducibility of all 3 irreducible representations of `S_3`: `s3Triv`, `s3Sign`, `s3Rho2`. -/
theorem s3Triv_isIrreducible : Representation.IsIrreducible s3Triv := by
  have hbot : (⊥ : Subrepresentation s3Triv) ≠ ⊤ := fun h =>
    bot_ne_top (congr_arg Subrepresentation.toSubmodule h)
  have : Nontrivial (Subrepresentation s3Triv) := ⟨⟨⊥, ⊤, hbot⟩⟩
  refine ⟨fun S => ?_⟩
  by_cases hS : S = ⊥
  · exact Or.inl hS
  · right
    have hex : ∃ z : ℂ, z ∈ S.toSubmodule ∧ z ≠ 0 := by
      by_contra hnone; push Not at hnone
      apply hS; apply Subrepresentation.ext; change S.toSubmodule = ⊥
      rw [eq_bot_iff]; intro z hz; exact hnone z hz
    obtain ⟨z, hzS, hz0⟩ := hex
    apply Subrepresentation.ext; change S.toSubmodule = ⊤; rw [eq_top_iff]
    intro w _
    have hw : w = (w * z⁻¹) • z := by simp [smul_eq_mul, mul_assoc, inv_mul_cancel₀ hz0]
    rw [hw]; exact S.toSubmodule.smul_mem _ hzS

theorem s3Sign_isIrreducible : Representation.IsIrreducible s3Sign := by
  have hbot : (⊥ : Subrepresentation s3Sign) ≠ ⊤ := fun h =>
    bot_ne_top (congr_arg Subrepresentation.toSubmodule h)
  have : Nontrivial (Subrepresentation s3Sign) := ⟨⟨⊥, ⊤, hbot⟩⟩
  refine ⟨fun S => ?_⟩
  by_cases hS : S = ⊥
  · exact Or.inl hS
  · right
    have hex : ∃ z : ℂ, z ∈ S.toSubmodule ∧ z ≠ 0 := by
      by_contra hnone; push Not at hnone
      apply hS; apply Subrepresentation.ext; change S.toSubmodule = ⊥
      rw [eq_bot_iff]; intro z hz; exact hnone z hz
    obtain ⟨z, hzS, hz0⟩ := hex
    apply Subrepresentation.ext; change S.toSubmodule = ⊤; rw [eq_top_iff]
    intro w _
    have hw : w = (w * z⁻¹) • z := by simp [smul_eq_mul, mul_assoc, inv_mul_cancel₀ hz0]
    rw [hw]; exact S.toSubmodule.smul_mem _ hzS

theorem s3Rho2_isIrreducible : Representation.IsIrreducible s3Rho2 := by
  have hirr := dihedralRep2_isIrreducible (n := 3) (by norm_num) 1 primRoot3_sq_ne_one
  have hbot : (⊥ : Subrepresentation s3Rho2) ≠ ⊤ := fun h =>
    bot_ne_top (congr_arg Subrepresentation.toSubmodule h)
  have : Nontrivial (Subrepresentation s3Rho2) := ⟨⟨⊥, ⊤, hbot⟩⟩
  refine ⟨fun S => ?_⟩
  let S' : Subrepresentation (dihedralRep2 3 (by norm_num) 1) :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := fun d v hv => by
        have := S.apply_mem_toSubmodule (s3EquivD3.symm d) hv
        simpa [s3Rho2] using this }
  rcases hirr.eq_bot_or_eq_top S' with h0 | h1
  · left
    exact Subrepresentation.ext (show S.toSubmodule = ⊥ from congr_arg Subrepresentation.toSubmodule h0)
  · right
    exact Subrepresentation.ext (show S.toSubmodule = ⊤ from congr_arg Subrepresentation.toSubmodule h1)

/-- Exact element orders in `DihedralGroup 3`. -/
lemma orderOf_d3_r0 : orderOf (DihedralGroup.r (0 : ZMod 3)) = 1 := by
  change orderOf (1 : DihedralGroup 3) = 1
  exact orderOf_one

lemma orderOf_d3_r1 : orderOf (DihedralGroup.r (1 : ZMod 3)) = 3 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hlt => ?_⟩
  interval_cases m <;> decide

lemma orderOf_d3_r2 : orderOf (DihedralGroup.r (2 : ZMod 3)) = 3 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hlt => ?_⟩
  interval_cases m <;> decide

lemma orderOf_d3_sr (i : ZMod 3) : orderOf (DihedralGroup.sr i) = 2 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by fin_cases i <;> decide, fun m hm hlt => ?_⟩
  interval_cases m
  fin_cases i <;> decide

lemma zmod3_cases (i : ZMod 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  revert i; decide

lemma d3_orderOf_eq_three {d : DihedralGroup 3} (hd : orderOf d = 3) :
    d = DihedralGroup.r 1 ∨ d = DihedralGroup.r 2 := by
  cases d with
  | r i =>
    rcases zmod3_cases i with rfl | rfl | rfl
    · rw [orderOf_d3_r0] at hd; omega
    · exact Or.inl rfl
    · exact Or.inr rfl
  | sr i =>
    rw [orderOf_d3_sr] at hd; omega

lemma d3_orderOf_eq_two {d : DihedralGroup 3} (hd : orderOf d = 2) :
    ∃ i : ZMod 3, d = DihedralGroup.sr i := by
  cases d with
  | r i =>
    rcases zmod3_cases i with rfl | rfl | rfl
    · rw [orderOf_d3_r0] at hd; omega
    · rw [orderOf_d3_r1] at hd; omega
    · rw [orderOf_d3_r2] at hd; omega
  | sr i => exact ⟨i, rfl⟩

/-- Exact character table of `s3Rho2` at all 3 conjugacy classes (`1`, 3-cycles, transpositions). -/
lemma s3Rho2_character_eq_d3 (g : Equiv.Perm (Fin 3)) :
    s3Rho2.character g = (dihedralRep2 3 (by norm_num) 1).character (s3EquivD3 g) := rfl

theorem s3Rho2_character_one : s3Rho2.character 1 = 2 := by
  rw [s3Rho2_character_eq_d3, map_one]
  change (dihedralRep2 3 (by norm_num) 1).character (DihedralGroup.r 0) = 2
  rw [dihedralRep2_character_r, dihedralPhase_zero]
  norm_num

theorem s3Rho2_character_threeCycle {g : Equiv.Perm (Fin 3)} (hg : orderOf g = 3) :
    s3Rho2.character g = -1 := by
  rw [s3Rho2_character_eq_d3]
  have hord : orderOf (s3EquivD3 g) = 3 := by rw [MulEquiv.orderOf_eq]; exact hg
  rcases d3_orderOf_eq_three hord with h1 | h2
  · rw [h1, dihedralRep2_character_r, dihedralPhase_3_one]
    exact primRoot3_add_inv
  · rw [h2, dihedralRep2_character_r, dihedralPhase_3_two, inv_inv, add_comm]
    exact primRoot3_add_inv

theorem s3Rho2_character_transposition {g : Equiv.Perm (Fin 3)} (hg : orderOf g = 2) :
    s3Rho2.character g = 0 := by
  rw [s3Rho2_character_eq_d3]
  have hord : orderOf (s3EquivD3 g) = 2 := by rw [MulEquiv.orderOf_eq]; exact hg
  obtain ⟨i, hi⟩ := d3_orderOf_eq_two hord
  rw [hi, dihedralRep2_character_sr]

/-- Exact local Artin Euler factors of `s3Rho2` at all 3 conjugacy classes of `S_3`. -/
theorem artinLocalFactor_s3Rho2_one (T : ℂ) :
    artinLocalFactor s3Rho2 1 T = (1 - T)⁻¹ ^ 2 := by
  change artinLocalFactor (dihedralRep2 3 (by norm_num) 1) (s3EquivD3 1) T = _
  rw [map_one]
  change artinLocalFactor (dihedralRep2 3 (by norm_num) 1) (DihedralGroup.r 0) T = _
  rw [artinLocalFactor_dihedralRep2_r, dihedralPhase_zero, inv_one, one_mul, sq]

theorem artinLocalFactor_s3Rho2_threeCycle {g : Equiv.Perm (Fin 3)} (hg : orderOf g = 3) (T : ℂ) :
    artinLocalFactor s3Rho2 g T = (1 + T + T ^ 2)⁻¹ := by
  change artinLocalFactor (dihedralRep2 3 (by norm_num) 1) (s3EquivD3 g) T = _
  have hord : orderOf (s3EquivD3 g) = 3 := by rw [MulEquiv.orderOf_eq]; exact hg
  have hne : primRoot 3 ≠ 0 := primRoot_ne_zero 3
  have hpoly : (1 - (primRoot 3)⁻¹ * T) * (1 - primRoot 3 * T) = 1 + T + T ^ 2 := by
    calc (1 - (primRoot 3)⁻¹ * T) * (1 - primRoot 3 * T)
        = 1 - (primRoot 3 + (primRoot 3)⁻¹) * T + (primRoot 3 * (primRoot 3)⁻¹) * T ^ 2 := by ring
    _ = 1 - (-1) * T + 1 * T ^ 2 := by rw [primRoot3_add_inv, mul_inv_cancel₀ hne]
    _ = 1 + T + T ^ 2 := by ring
  rcases d3_orderOf_eq_three hord with h1 | h2
  · rw [h1, artinLocalFactor_dihedralRep2_r, dihedralPhase_3_one, ← mul_inv,
      mul_comm (1 - primRoot 3 * T), hpoly]
  · rw [h2, artinLocalFactor_dihedralRep2_r, dihedralPhase_3_two, inv_inv, ← mul_inv, hpoly]

theorem artinLocalFactor_s3Rho2_threeCycle_eq_quot {g : Equiv.Perm (Fin 3)} (hg : orderOf g = 3)
    {T : ℂ} (hT : 1 - T ≠ 0) :
    artinLocalFactor s3Rho2 g T = (1 - T ^ 3)⁻¹ * (1 - T) := by
  rw [artinLocalFactor_s3Rho2_threeCycle hg]
  have hfac : 1 - T ^ 3 = (1 - T) * (1 + T + T ^ 2) := by ring
  rw [hfac, mul_inv, mul_comm (1 - T)⁻¹, mul_assoc, inv_mul_cancel₀ hT, mul_one]

theorem artinLocalFactor_s3Rho2_transposition {g : Equiv.Perm (Fin 3)} (hg : orderOf g = 2) (T : ℂ) :
    artinLocalFactor s3Rho2 g T = (1 - T ^ 2)⁻¹ := by
  change artinLocalFactor (dihedralRep2 3 (by norm_num) 1) (s3EquivD3 g) T = _
  have hord : orderOf (s3EquivD3 g) = 2 := by rw [MulEquiv.orderOf_eq]; exact hg
  obtain ⟨i, hi⟩ := d3_orderOf_eq_two hord
  rw [hi, artinLocalFactor_dihedralRep2_sr]

/-- The normal cyclic subgroup `C_3 = A_3 = alternatingGroup (Fin 3) ⊴ S_3`. -/
abbrev s3C3 : Subgroup (Equiv.Perm (Fin 3)) := alternatingGroup (Fin 3)

/-- The order-2 subgroup `C_2 = {1, swap 1 2} ≤ S_3` (the stabilizer of `0 : Fin 3`,
corresponding to the non-Galois cubic subfield `K = L^{C_2}`). -/
def s3C2 : Subgroup (Equiv.Perm (Fin 3)) :=
  MulAction.stabilizer (Equiv.Perm (Fin 3)) (0 : Fin 3)

/-- Every element of `S_3` has order `1`, `2`, or `3`. -/
lemma s3_order_cases (g : Equiv.Perm (Fin 3)) :
    g = 1 ∨ orderOf g = 3 ∨ orderOf g = 2 := by
  have hinv : s3EquivD3.symm (s3EquivD3 g) = g := s3EquivD3.symm_apply_apply g
  have hord : orderOf g = orderOf (s3EquivD3 g) := (MulEquiv.orderOf_eq s3EquivD3 g).symm
  cases hd : s3EquivD3 g with
  | r i =>
    rcases zmod3_cases i with rfl | rfl | rfl
    · left
      rw [← hinv, hd]
      exact map_one s3EquivD3.symm
    · right; left; rw [hord, hd, orderOf_d3_r1]
    · right; left; rw [hord, hd, orderOf_d3_r2]
  | sr i =>
    right; right; rw [hord, hd, orderOf_d3_sr]

lemma s3_sign_of_orderOf_eq_three {g : Equiv.Perm (Fin 3)} (h3 : orderOf g = 3) :
    Equiv.Perm.sign g = 1 := by
  have hord : orderOf (s3EquivD3 g) = 3 := by rw [MulEquiv.orderOf_eq]; exact h3
  have hinv : d3ToS3 (s3EquivD3 g) = g :=
    (MulEquiv.ofBijective d3ToS3 d3ToS3_bijective).apply_symm_apply g
  rw [← hinv]
  rcases d3_orderOf_eq_three hord with h1 | h2
  · rw [h1]; decide
  · rw [h2]; decide

lemma s3_sign_of_orderOf_eq_two {g : Equiv.Perm (Fin 3)} (h2 : orderOf g = 2) :
    Equiv.Perm.sign g = -1 := by
  have hord : orderOf (s3EquivD3 g) = 2 := by rw [MulEquiv.orderOf_eq]; exact h2
  have hinv : d3ToS3 (s3EquivD3 g) = g :=
    (MulEquiv.ofBijective d3ToS3 d3ToS3_bijective).apply_symm_apply g
  rw [← hinv]
  obtain ⟨i, hi⟩ := d3_orderOf_eq_two hord
  rw [hi]
  fin_cases i <;> decide

/-- Exact character of a permutation representation `ofMulAction ℂ G X` = number of fixed points. -/
theorem ofMulAction_character {G X : Type*} [Group G] [Fintype X] [MulAction G X] (g : G) :
    (Representation.ofMulAction ℂ G X).character g =
      (Nat.card {x : X // g • x = x} : ℂ) := by
  unfold Representation.character
  let b : Module.Basis X ℂ (MonoidAlgebra ℂ X) := MonoidAlgebra.basis X ℂ
  rw [LinearMap.trace_eq_matrix_trace ℂ b]
  simp only [Matrix.trace, Matrix.diag]
  have hentry : ∀ x : X, LinearMap.toMatrix b b ((Representation.ofMulAction ℂ G X) g) x x =
      if g • x = x then 1 else 0 := by
    intro x
    rw [LinearMap.toMatrix_apply]
    have hbx : b x = MonoidAlgebra.single x (1 : ℂ) := by simp [b, MonoidAlgebra.basis]
    have hact : (Representation.ofMulAction ℂ G X) g (b x) = b (g • x) := by
      rw [hbx, Representation.ofMulAction_single]
      simp [b, MonoidAlgebra.basis]
    rw [hact, b.repr_self, Finsupp.single_apply]
  simp_rw [hentry]
  rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- **Regular Representation Character Decomposition of `S_3`**:
`χ_{ℂ[S_3]} = χ_1 + χ_{sgn} + 2 χ_{ρ₂}`. -/
theorem s3_reg_character_decomp (g : Equiv.Perm (Fin 3)) :
    (leftRegular ℂ (Equiv.Perm (Fin 3))).character g =
      s3Triv.character g + s3Sign.character g + 2 * s3Rho2.character g := by
  have htriv : s3Triv.character g = 1 := by
    have : s3Triv = repOfChar (1 : Equiv.Perm (Fin 3) →* ℂˣ) := by
      ext σ; simp [s3Triv, Representation.trivial]
    rw [this, repOfChar_character]; simp
  rw [htriv, leftRegular_character]
  rcases s3_order_cases g with rfl | h3 | h2
  · rw [if_pos rfl, s3Rho2_character_one]
    have hsgn : s3Sign.character 1 = 1 := by simp [s3Sign]
    have hcard : Fintype.card (Equiv.Perm (Fin 3)) = 6 := by decide
    rw [hsgn, hcard]; norm_num
  · have hne : g ≠ 1 := fun h => by subst h; simp at h3
    rw [if_neg hne, s3Rho2_character_threeCycle h3]
    have hsgn : s3Sign.character g = 1 := by
      simp [s3Sign, s3SignChar, s3_sign_of_orderOf_eq_three h3]
    rw [hsgn]; norm_num
  · have hne : g ≠ 1 := fun h => by subst h; simp at h2
    rw [if_neg hne, s3Rho2_character_transposition h2]
    have hsgn : s3Sign.character g = -1 := by
      simp [s3Sign, s3SignChar, s3_sign_of_orderOf_eq_two h2]
    rw [hsgn]; norm_num

/-- **Degree-3 Permutation Character Decomposition of `S_3`** (matching the cubic subfield `K = L^{C_2}`):
`χ_{ℂ[Fin 3]} = χ_1 + χ_{ρ₂}` and `χ_{ℂ[S_3 / C_2]} = χ_1 + χ_{ρ₂}`! -/
theorem s3_perm3_character_decomp (g : Equiv.Perm (Fin 3)) :
    (Representation.ofMulAction ℂ (Equiv.Perm (Fin 3)) (Fin 3)).character g =
      s3Triv.character g + s3Rho2.character g := by
  have htriv : s3Triv.character g = 1 := by
    have : s3Triv = repOfChar (1 : Equiv.Perm (Fin 3) →* ℂˣ) := by
      ext σ; simp [s3Triv, Representation.trivial]
    rw [this, repOfChar_character]; simp
  rw [htriv, ofMulAction_character]
  have hinv : d3ToS3 (s3EquivD3 g) = g :=
    (MulEquiv.ofBijective d3ToS3 d3ToS3_bijective).apply_symm_apply g
  rcases s3_order_cases g with rfl | h3 | h2
  · rw [s3Rho2_character_one]
    have hcard : Nat.card {x : Fin 3 // (1 : Equiv.Perm (Fin 3)) • x = x} = 3 := by
      have he : {x : Fin 3 // (1 : Equiv.Perm (Fin 3)) • x = x} ≃ Fin 3 :=
        { toFun := Subtype.val
          invFun := fun x => ⟨x, one_smul _ x⟩
          left_inv := fun ⟨_, _⟩ => rfl
          right_inv := fun _ => rfl }
      rw [Nat.card_congr he, Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [hcard]; norm_num
  · rw [s3Rho2_character_threeCycle h3]
    have hord : orderOf (s3EquivD3 g) = 3 := by rw [MulEquiv.orderOf_eq]; exact h3
    have hemp : IsEmpty {x : Fin 3 // g • x = x} := by
      refine ⟨fun ⟨x, hx⟩ => ?_⟩
      rw [← hinv] at hx
      rcases d3_orderOf_eq_three hord with h1 | h2
      · rw [h1] at hx; fin_cases x <;> exact absurd hx (by decide)
      · rw [h2] at hx; fin_cases x <;> exact absurd hx (by decide)
    rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero]; norm_num
  · rw [s3Rho2_character_transposition h2]
    have hord : orderOf (s3EquivD3 g) = 2 := by rw [MulEquiv.orderOf_eq]; exact h2
    obtain ⟨i, hi⟩ := d3_orderOf_eq_two hord
    have hcard1 : Nat.card {x : Fin 3 // g • x = x} = 1 := by
      rw [← hinv, hi]
      rcases zmod3_cases i with rfl | rfl | rfl
      · let : Unique {x : Fin 3 // d3ToS3 (DihedralGroup.sr (0 : ZMod 3)) • x = x} :=
          { default := ⟨0, by decide⟩
            uniq := fun ⟨x, hx⟩ => Subtype.ext (by fin_cases x <;> first | rfl | exact absurd hx (by decide)) }
        exact Nat.card_unique
      · let : Unique {x : Fin 3 // d3ToS3 (DihedralGroup.sr (1 : ZMod 3)) • x = x} :=
          { default := ⟨1, by decide⟩
            uniq := fun ⟨x, hx⟩ => Subtype.ext (by fin_cases x <;> first | rfl | exact absurd hx (by decide)) }
        exact Nat.card_unique
      · let : Unique {x : Fin 3 // d3ToS3 (DihedralGroup.sr (2 : ZMod 3)) • x = x} :=
          { default := ⟨2, by decide⟩
            uniq := fun ⟨x, hx⟩ => Subtype.ext (by fin_cases x <;> first | rfl | exact absurd hx (by decide)) }
        exact Nat.card_unique
    rw [hcard1]; norm_num

/-- `S_3`-equivariant bijection `S_3 ⧸ s3C2 ≃ Fin 3`, giving `ℂ[S_3 ⧸ C_2] ≃ ℂ[Fin 3]`. -/
def s3CosetC2EquivFin3 :
    Representation.Equiv
      (Representation.ofMulAction ℂ (Equiv.Perm (Fin 3)) (Equiv.Perm (Fin 3) ⧸ s3C2))
      (Representation.ofMulAction ℂ (Equiv.Perm (Fin 3)) (Fin 3)) := by
  have horb : MulAction.orbit (Equiv.Perm (Fin 3)) (0 : Fin 3) = Set.univ := by
    ext x
    simp only [Set.mem_univ, iff_true, MulAction.mem_orbit_iff]
    exact ⟨Equiv.swap 0 x, by simp⟩
  let eSet : (Equiv.Perm (Fin 3) ⧸ s3C2) ≃ Fin 3 :=
    (MulAction.orbitEquivQuotientStabilizer (Equiv.Perm (Fin 3)) (0 : Fin 3)).symm.trans
      (Equiv.ofBijective (fun x : MulAction.orbit (Equiv.Perm (Fin 3)) (0 : Fin 3) => x.1)
        ⟨Subtype.val_injective, fun x => ⟨⟨x, horb ▸ Set.mem_univ x⟩, rfl⟩⟩)
  have heSet_smul : ∀ (g : Equiv.Perm (Fin 3)) (q : Equiv.Perm (Fin 3) ⧸ s3C2),
      eSet (g • q) = g • eSet q := by
    intro g q
    obtain ⟨σ, rfl⟩ := Quotient.exists_rep q
    change eSet ((g * σ : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 3) ⧸ s3C2) =
      g • eSet ((σ : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 3) ⧸ s3C2)
    change (g * σ) • (0 : Fin 3) = g • (σ • (0 : Fin 3))
    exact mul_smul g σ (0 : Fin 3)
  refine Representation.Equiv.mk (MonoidAlgebra.mapDomainLinearEquiv ℂ ℂ eSet) fun g => ?_
  apply MonoidAlgebra.lhom_ext'
  intro q
  apply LinearMap.ext_ring
  change MonoidAlgebra.mapDomainLinearEquiv ℂ ℂ eSet
      ((Representation.ofMulAction ℂ (Equiv.Perm (Fin 3)) (Equiv.Perm (Fin 3) ⧸ s3C2)) g
        (MonoidAlgebra.single q (1 : ℂ))) =
    (Representation.ofMulAction ℂ (Equiv.Perm (Fin 3)) (Fin 3)) g
      (MonoidAlgebra.mapDomainLinearEquiv ℂ ℂ eSet (MonoidAlgebra.single q (1 : ℂ)))
  rw [Representation.ofMulAction_single, MonoidAlgebra.mapDomainLinearEquiv_single,
    MonoidAlgebra.mapDomainLinearEquiv_single, Representation.ofMulAction_single, heSet_smul]

theorem s3_cosetC2_character_decomp (g : Equiv.Perm (Fin 3)) :
    (Representation.ofMulAction ℂ (Equiv.Perm (Fin 3)) (Equiv.Perm (Fin 3) ⧸ s3C2)).character g =
      s3Triv.character g + s3Rho2.character g := by
  rw [congr_fun (Representation.char_iso s3CosetC2EquivFin3) g, s3_perm3_character_decomp]

/-- **Degree-2 Permutation Character Decomposition of `S_3`** (matching the quadratic subfield `F = L^{C_3}`):
`χ_{ℂ[S_3 / C_3]} = χ_1 + χ_{sgn}`. -/
theorem s3_cosetC3_character_decomp (g : Equiv.Perm (Fin 3)) :
    (Representation.ofMulAction ℂ (Equiv.Perm (Fin 3)) (Equiv.Perm (Fin 3) ⧸ s3C3)).character g =
      s3Triv.character g + s3Sign.character g := by
  have htriv : s3Triv.character g = 1 := by
    have : s3Triv = repOfChar (1 : Equiv.Perm (Fin 3) →* ℂˣ) := by
      ext σ; simp [s3Triv, Representation.trivial]
    rw [this, repOfChar_character]; simp
  rw [htriv, ofMulAction_character]
  -- Explicit 2-element set {1, swap 0 1} of cosets of s3C3 = alternatingGroup (Fin 3)
  let q0 : Equiv.Perm (Fin 3) ⧸ s3C3 := ((1 : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 3) ⧸ s3C3)
  let q1 : Equiv.Perm (Fin 3) ⧸ s3C3 := ((Equiv.swap (0 : Fin 3) 1) : Equiv.Perm (Fin 3) ⧸ s3C3)
  have hqne : q0 ≠ q1 := by
    intro h
    have hmem : (1 : Equiv.Perm (Fin 3))⁻¹ * Equiv.swap (0 : Fin 3) 1 ∈ s3C3 :=
      QuotientGroup.leftRel_apply.mp (Quotient.exact h)
    have hsign : Equiv.Perm.sign (Equiv.swap (0 : Fin 3) 1) = 1 := by
      simp [s3C3, Equiv.Perm.mem_alternatingGroup] at hmem
    have hneg : Equiv.Perm.sign (Equiv.swap (0 : Fin 3) 1) = -1 := by decide
    rw [hneg] at hsign
    exact absurd hsign (by decide)
  have hqcases : ∀ q : Equiv.Perm (Fin 3) ⧸ s3C3, q = q0 ∨ q = q1 := by
    intro q
    obtain ⟨σ, rfl⟩ := Quotient.exists_rep q
    have hsign := Int.units_eq_one_or (Equiv.Perm.sign σ)
    rcases hsign with h1 | hneg
    · left
      exact Quotient.sound (show (QuotientGroup.leftRel s3C3) σ 1 by
        rw [QuotientGroup.leftRel_apply]
        simp [s3C3, Equiv.Perm.mem_alternatingGroup, h1])
    · right
      exact Quotient.sound (show (QuotientGroup.leftRel s3C3) σ (Equiv.swap 0 1) by
        rw [QuotientGroup.leftRel_apply]
        have hsw : Equiv.Perm.sign (Equiv.swap (0 : Fin 3) 1) = -1 := by decide
        simp [s3C3, Equiv.Perm.mem_alternatingGroup, map_mul, hneg, hsw])
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin 3) ⧸ s3C3)) = {q0, q1} := by
    ext q
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact hqcases q
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h1 | hneg
  · have hfix0 : g • q0 = q0 := by
      exact Quotient.sound (show (QuotientGroup.leftRel s3C3) (g * 1) 1 by
        rw [QuotientGroup.leftRel_apply]
        simp [s3C3, Equiv.Perm.mem_alternatingGroup, h1])
    have hfix1 : g • q1 = q1 := by
      exact Quotient.sound (show (QuotientGroup.leftRel s3C3) (g * Equiv.swap 0 1) (Equiv.swap 0 1) by
        rw [QuotientGroup.leftRel_apply]
        have hsw : Equiv.Perm.sign (Equiv.swap (0 : Fin 3) 1) = -1 := by decide
        simp [s3C3, Equiv.Perm.mem_alternatingGroup, map_mul, h1, hsw])
    have hcard2 : Nat.card {q : Equiv.Perm (Fin 3) ⧸ s3C3 // g • q = q} = 2 := by
      let e2 : Fin 2 ≃ {q : Equiv.Perm (Fin 3) ⧸ s3C3 // g • q = q} :=
        Equiv.ofBijective
          (fun a => if a = 0 then ⟨q0, hfix0⟩ else ⟨q1, hfix1⟩)
          ⟨by
            intro a b hab
            fin_cases a <;> fin_cases b
            · rfl
            · exact absurd (congr_arg Subtype.val hab) hqne
            · exact absurd (congr_arg Subtype.val hab).symm hqne
            · rfl,
           by
            rintro ⟨q, hq⟩
            rcases hqcases q with rfl | rfl
            · exact ⟨0, rfl⟩
            · exact ⟨1, rfl⟩⟩
      rw [← Nat.card_congr e2, Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [hcard2]
    simp [s3Sign, s3SignChar, h1]
    norm_num
  · have hnfix0 : g • q0 ≠ q0 := by
      intro h
      have hmem := QuotientGroup.leftRel_apply.mp (Quotient.exact h)
      have hs : Equiv.Perm.sign g = 1 := by
        simpa [s3C3, Equiv.Perm.mem_alternatingGroup] using hmem
      rw [hneg] at hs; exact absurd hs (by decide)
    have hnfix1 : g • q1 ≠ q1 := by
      intro h
      have hmem := QuotientGroup.leftRel_apply.mp (Quotient.exact h)
      have hsw : Equiv.Perm.sign (Equiv.swap (0 : Fin 3) 1) = -1 := by decide
      have hs : Equiv.Perm.sign g = 1 := by
        have h2 : Equiv.Perm.sign ((g * Equiv.swap (0 : Fin 3) 1)⁻¹ * Equiv.swap (0 : Fin 3) 1) = 1 :=
          (Equiv.Perm.mem_alternatingGroup).mp hmem
        simp [map_mul, hsw] at h2
        exact h2
      rw [hneg] at hs; exact absurd hs (by decide)
    have hemp : IsEmpty {q : Equiv.Perm (Fin 3) ⧸ s3C3 // g • q = q} := by
      refine ⟨fun ⟨q, hq⟩ => ?_⟩
      rcases hqcases q with rfl | rfl
      · exact hnfix0 hq
      · exact hnfix1 hq
    rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero]
    simp [s3Sign, s3SignChar, hneg]

/-- Nontrivial cubic 1-dimensional character `ω : s3C3 →* ℂˣ` on `C_3 = A_3 ⊴ S_3`,
pulled back from `dihedralRotChar 3 _ 1` along `s3EquivD3`. -/
lemma s3EquivD3_mem_rot_iff (g : Equiv.Perm (Fin 3)) :
    s3EquivD3 g ∈ rotationSubgroup 3 ↔ g ∈ s3C3 := by
  have hall : ∀ d : DihedralGroup 3,
      d ∈ rotationSubgroup 3 ↔ d3ToS3 d ∈ s3C3 := by
    intro d
    cases d with
    | r i =>
      constructor
      · intro _
        rw [Equiv.Perm.mem_alternatingGroup]
        fin_cases i <;> decide
      · intro _; exact ⟨i, rfl⟩
    | sr i =>
      constructor
      · rintro ⟨j, hj⟩; cases hj
      · intro h
        rw [Equiv.Perm.mem_alternatingGroup] at h
        have hneg : Equiv.Perm.sign (d3ToS3 (DihedralGroup.sr i)) = -1 := by
          fin_cases i <;> decide
        rw [hneg] at h
        exact absurd h (by decide)
  have h1 := hall (s3EquivD3 g)
  have hinv : d3ToS3 (s3EquivD3 g) = g := (MulEquiv.ofBijective d3ToS3 d3ToS3_bijective).apply_symm_apply g
  rwa [hinv] at h1

def s3C3EquivRot3 : s3C3 ≃* rotationSubgroup 3 where
  toFun x := ⟨s3EquivD3 x.1, (s3EquivD3_mem_rot_iff x.1).mpr x.2⟩
  invFun y := ⟨s3EquivD3.symm y.1, (s3EquivD3_mem_rot_iff (s3EquivD3.symm y.1)).mp (by simp [y.2])⟩
  left_inv x := Subtype.ext (s3EquivD3.symm_apply_apply x.1)
  right_inv y := Subtype.ext (s3EquivD3.apply_symm_apply y.1)
  map_mul' x y := Subtype.ext (map_mul s3EquivD3 x.1 y.1)

def s3Omega : s3C3 →* ℂˣ :=
  (dihedralRotChar 3 (by norm_num) 1).comp s3C3EquivRot3.toMonoidHom

/-- **Monomial Induction for `S_3` (`rho2_eq_ind_C3`)**:
`s3Rho2 ≃ Ind_{C_3}^{S_3} ω`! -/
def rho2_eq_ind_C3 :
    Representation.Equiv s3Rho2
      (Representation.ind s3C3.subtype (repOfChar s3Omega)) := by
  -- Transport dihedral_irrep_ind_cyclic 3 _ 1 along s3EquivD3
  let eD := dihedral_irrep_ind_cyclic 3 (by norm_num) 1
  -- Build equivalence Ind_{C_3}^{S_3} s3Omega ≃ (Ind_{rot3}^{D_3} dihedralRotChar).comp s3EquivD3
  let eS3Ind : Representation.Equiv
      ((Representation.ind (rotationSubgroup 3).subtype
        (repOfChar (dihedralRotChar 3 (by norm_num) 1))).comp s3EquivD3.toMonoidHom)
      (Representation.ind s3C3.subtype (repOfChar s3Omega)) := by
    let fwdAlg : MonoidAlgebra ℂ (DihedralGroup 3) →ₗ[ℂ] MonoidAlgebra ℂ (Equiv.Perm (Fin 3)) :=
      (MonoidAlgebra.mapDomainLinearEquiv ℂ ℂ s3EquivD3.symm.toEquiv).toLinearMap
    let invAlg : MonoidAlgebra ℂ (Equiv.Perm (Fin 3)) →ₗ[ℂ] MonoidAlgebra ℂ (DihedralGroup 3) :=
      (MonoidAlgebra.mapDomainLinearEquiv ℂ ℂ s3EquivD3.toEquiv).toLinearMap
    let fwdT : TensorProduct ℂ (MonoidAlgebra ℂ (DihedralGroup 3)) ℂ →ₗ[ℂ]
        Representation.IndV s3C3.subtype (repOfChar s3Omega) :=
      (Representation.Coinvariants.mk _).comp (TensorProduct.map fwdAlg LinearMap.id)
    let invT : TensorProduct ℂ (MonoidAlgebra ℂ (Equiv.Perm (Fin 3))) ℂ →ₗ[ℂ]
        Representation.IndV (rotationSubgroup 3).subtype
          (repOfChar (dihedralRotChar 3 (by norm_num) 1)) :=
      (Representation.Coinvariants.mk _).comp (TensorProduct.map invAlg LinearMap.id)
    have hfwd_rel : ∀ h : rotationSubgroup 3,
        fwdT ∘ₗ (Representation.tprod ((leftRegular ℂ (DihedralGroup 3)).comp
          (rotationSubgroup 3).subtype) (repOfChar (dihedralRotChar 3 (by norm_num) 1))) h = fwdT := by
      intro h
      apply TensorProduct.ext
      apply MonoidAlgebra.lhom_ext'
      intro d
      apply LinearMap.ext_ring
      refine LinearMap.ext fun c => ?_
      have hlr : (leftRegular ℂ (DihedralGroup 3)) (h : DihedralGroup 3)
          (MonoidAlgebra.single d (1 : ℂ)) =
          MonoidAlgebra.single ((h : DihedralGroup 3) * d) (1 : ℂ) :=
        Representation.ofMulAction_single (h : DihedralGroup 3) d (1 : ℂ)
      have hlr' : (leftRegular ℂ (Equiv.Perm (Fin 3))) ((s3C3EquivRot3.symm h : s3C3) : Equiv.Perm (Fin 3))
          (MonoidAlgebra.single (s3EquivD3.symm d) (1 : ℂ)) =
          MonoidAlgebra.single (s3EquivD3.symm ((h : DihedralGroup 3) * d)) (1 : ℂ) := by
        rw [Representation.ofMulAction_single]
        congr 1
        simp [s3C3EquivRot3, map_mul]
      have hch : s3Omega (s3C3EquivRot3.symm h) = dihedralRotChar 3 (by norm_num) 1 h := by
        simp [s3Omega]
      have hcoinv := Representation.Coinvariants.mk_self_apply
        (ρ := Representation.tprod ((leftRegular ℂ (Equiv.Perm (Fin 3))).comp s3C3.subtype)
          (repOfChar s3Omega))
        (s3C3EquivRot3.symm h) (MonoidAlgebra.single (s3EquivD3.symm d) (1 : ℂ) ⊗ₜ[ℂ] c)
      change Representation.Coinvariants.mk _
          (fwdAlg ((leftRegular ℂ (DihedralGroup 3)) (h : DihedralGroup 3)
            (MonoidAlgebra.single d (1 : ℂ))) ⊗ₜ[ℂ]
            ((dihedralRotChar 3 (by norm_num) 1 h : ℂ) * c)) =
        Representation.Coinvariants.mk _
          (fwdAlg (MonoidAlgebra.single d (1 : ℂ)) ⊗ₜ[ℂ] c)
      rw [hlr]
      simp only [fwdAlg, LinearEquiv.coe_coe, MonoidAlgebra.mapDomainLinearEquiv_single]
      simpa [Representation.tprod_apply, hlr', hch, repOfChar_apply] using hcoinv
    have hinv_rel : ∀ h : s3C3,
        invT ∘ₗ (Representation.tprod ((leftRegular ℂ (Equiv.Perm (Fin 3))).comp s3C3.subtype)
          (repOfChar s3Omega)) h = invT := by
      intro h
      apply TensorProduct.ext
      apply MonoidAlgebra.lhom_ext'
      intro x
      apply LinearMap.ext_ring
      refine LinearMap.ext fun c => ?_
      have hlr : (leftRegular ℂ (Equiv.Perm (Fin 3))) (h : Equiv.Perm (Fin 3))
          (MonoidAlgebra.single x (1 : ℂ)) =
          MonoidAlgebra.single ((h : Equiv.Perm (Fin 3)) * x) (1 : ℂ) :=
        Representation.ofMulAction_single (h : Equiv.Perm (Fin 3)) x (1 : ℂ)
      have hlr' : (leftRegular ℂ (DihedralGroup 3)) ((s3C3EquivRot3 h : rotationSubgroup 3) : DihedralGroup 3)
          (MonoidAlgebra.single (s3EquivD3 x) (1 : ℂ)) =
          MonoidAlgebra.single (s3EquivD3 ((h : Equiv.Perm (Fin 3)) * x)) (1 : ℂ) := by
        rw [Representation.ofMulAction_single]
        congr 1
        simp [s3C3EquivRot3, map_mul]
      have hcoinv := Representation.Coinvariants.mk_self_apply
        (ρ := Representation.tprod ((leftRegular ℂ (DihedralGroup 3)).comp
          (rotationSubgroup 3).subtype) (repOfChar (dihedralRotChar 3 (by norm_num) 1)))
        (s3C3EquivRot3 h) (MonoidAlgebra.single (s3EquivD3 x) (1 : ℂ) ⊗ₜ[ℂ] c)
      change Representation.Coinvariants.mk _
          (invAlg ((leftRegular ℂ (Equiv.Perm (Fin 3))) (h : Equiv.Perm (Fin 3))
            (MonoidAlgebra.single x (1 : ℂ))) ⊗ₜ[ℂ]
            ((s3Omega h : ℂ) * c)) =
        Representation.Coinvariants.mk _
          (invAlg (MonoidAlgebra.single x (1 : ℂ)) ⊗ₜ[ℂ] c)
      rw [hlr]
      simp only [invAlg, LinearEquiv.coe_coe, MonoidAlgebra.mapDomainLinearEquiv_single]
      simpa [Representation.tprod_apply, hlr', s3Omega, repOfChar_apply] using hcoinv
    let fwd : Representation.IndV (rotationSubgroup 3).subtype
          (repOfChar (dihedralRotChar 3 (by norm_num) 1)) →ₗ[ℂ]
        Representation.IndV s3C3.subtype (repOfChar s3Omega) :=
      Representation.Coinvariants.lift _ fwdT hfwd_rel
    let inv : Representation.IndV s3C3.subtype (repOfChar s3Omega) →ₗ[ℂ]
        Representation.IndV (rotationSubgroup 3).subtype
          (repOfChar (dihedralRotChar 3 (by norm_num) 1)) :=
      Representation.Coinvariants.lift _ invT hinv_rel
    have hfwd_mk : ∀ (d : DihedralGroup 3) (c : ℂ),
        fwd (Representation.IndV.mk (rotationSubgroup 3).subtype
          (repOfChar (dihedralRotChar 3 (by norm_num) 1)) d c) =
        Representation.IndV.mk s3C3.subtype (repOfChar s3Omega) (s3EquivD3.symm d) c := by
      intro d c
      change Representation.Coinvariants.mk _ (fwdAlg (MonoidAlgebra.single d 1) ⊗ₜ[ℂ] c) = _
      simp [fwdAlg, Representation.IndV.mk]
    have hinv_mk : ∀ (x : Equiv.Perm (Fin 3)) (c : ℂ),
        inv (Representation.IndV.mk s3C3.subtype (repOfChar s3Omega) x c) =
        Representation.IndV.mk (rotationSubgroup 3).subtype
          (repOfChar (dihedralRotChar 3 (by norm_num) 1)) (s3EquivD3 x) c := by
      intro x c
      change Representation.Coinvariants.mk _ (invAlg (MonoidAlgebra.single x 1) ⊗ₜ[ℂ] c) = _
      simp [invAlg, Representation.IndV.mk]
    have hleft : inv.comp fwd = LinearMap.id := by
      apply Representation.IndV.hom_ext
      intro d; refine LinearMap.ext fun c => ?_
      change inv (fwd (Representation.IndV.mk _ _ d c)) = Representation.IndV.mk _ _ d c
      rw [hfwd_mk, hinv_mk, s3EquivD3.apply_symm_apply]
    have hright : fwd.comp inv = LinearMap.id := by
      apply Representation.IndV.hom_ext
      intro x; refine LinearMap.ext fun c => ?_
      change fwd (inv (Representation.IndV.mk _ _ x c)) = Representation.IndV.mk _ _ x c
      rw [hinv_mk, hfwd_mk, s3EquivD3.symm_apply_apply]
    refine Representation.Equiv.mk (LinearEquiv.ofLinearMap fwd inv hright hleft) fun g => ?_
    apply Representation.IndV.hom_ext
    intro d; refine LinearMap.ext fun c => ?_
    change fwd ((Representation.ind (rotationSubgroup 3).subtype
        (repOfChar (dihedralRotChar 3 (by norm_num) 1))) (s3EquivD3 g)
        (Representation.IndV.mk _ _ d c)) =
      (Representation.ind s3C3.subtype (repOfChar s3Omega)) g
        (fwd (Representation.IndV.mk _ _ d c))
    have h1 : (Representation.ind (rotationSubgroup 3).subtype
        (repOfChar (dihedralRotChar 3 (by norm_num) 1))) (s3EquivD3 g)
        (Representation.IndV.mk _ _ d c) =
      Representation.IndV.mk _ _ (d * (s3EquivD3 g)⁻¹) c := by
      simp [Representation.ind, Representation.IndV.mk]
    have h2 : (Representation.ind s3C3.subtype (repOfChar s3Omega)) g
        (Representation.IndV.mk _ _ (s3EquivD3.symm d) c) =
      Representation.IndV.mk _ _ (s3EquivD3.symm d * g⁻¹) c := by
      simp [Representation.ind, Representation.IndV.mk]
    rw [h1, hfwd_mk, hfwd_mk, h2]
    simp [map_mul, map_inv]
  let eComp : Representation.Equiv s3Rho2
      ((Representation.ind (rotationSubgroup 3).subtype
        (repOfChar (dihedralRotChar 3 (by norm_num) 1))).comp s3EquivD3.toMonoidHom) :=
    Representation.Equiv.mk eD.toLinearEquiv fun g => eD.isIntertwining' (s3EquivD3 g)
  exact eComp.trans eS3Ind

/-- **Local `S_3` Dedekind–Artin Euler Factor Identities** (at EVERY `g ∈ S_3` and EVERY `T : ℂ`):
1. `artinLocalFactor ℂ[S_3/C_3] g T = artinLocalFactor 1 g T * artinLocalFactor sgn g T`
2. `artinLocalFactor ℂ[S_3/C_2] g T = artinLocalFactor 1 g T * artinLocalFactor ρ₂ g T`
3. `artinLocalFactor ℂ[S_3] g T = artinLocalFactor ℂ[S_3/C_3] g T * (artinLocalFactor ρ₂ g T)^2`
4. **Artin–Brauer–Kuroda local identity**:
   `artinLocalFactor ℂ[S_3] g T * (artinLocalFactor 1 g T)^2 = artinLocalFactor ℂ[S_3/C_3] g T * (artinLocalFactor ℂ[S_3/C_2] g T)^2`. -/
theorem artinLocalFactor_s3_cosetC3 (g : Equiv.Perm (Fin 3)) (T : ℂ) :
    artinLocalFactor (Representation.ofMulAction ℂ (Equiv.Perm (Fin 3))
      (Equiv.Perm (Fin 3) ⧸ s3C3)) g T =
      artinLocalFactor s3Triv g T * artinLocalFactor s3Sign g T := by
  have hchar : (Representation.ofMulAction ℂ (Equiv.Perm (Fin 3))
      (Equiv.Perm (Fin 3) ⧸ s3C3)).character = (Representation.prod s3Triv s3Sign).character := by
    ext x
    rw [character_prod, s3_cosetC3_character_decomp]
  rw [artinLocalFactor_eq_of_character_eq hchar g T, artinLocalFactor_prod]

theorem artinLocalFactor_s3_cosetC2 (g : Equiv.Perm (Fin 3)) (T : ℂ) :
    artinLocalFactor (Representation.ofMulAction ℂ (Equiv.Perm (Fin 3))
      (Equiv.Perm (Fin 3) ⧸ s3C2)) g T =
      artinLocalFactor s3Triv g T * artinLocalFactor s3Rho2 g T := by
  have hchar : (Representation.ofMulAction ℂ (Equiv.Perm (Fin 3))
      (Equiv.Perm (Fin 3) ⧸ s3C2)).character = (Representation.prod s3Triv s3Rho2).character := by
    ext x
    rw [character_prod, s3_cosetC2_character_decomp]
  rw [artinLocalFactor_eq_of_character_eq hchar g T, artinLocalFactor_prod]

theorem artinLocalFactor_s3_regular (g : Equiv.Perm (Fin 3)) (T : ℂ) :
    artinLocalFactor (leftRegular ℂ (Equiv.Perm (Fin 3))) g T =
      artinLocalFactor (Representation.ofMulAction ℂ (Equiv.Perm (Fin 3))
        (Equiv.Perm (Fin 3) ⧸ s3C3)) g T *
      (artinLocalFactor s3Rho2 g T) ^ 2 := by
  let R := Representation.prod
    (Representation.prod s3Triv s3Sign) (Representation.prod s3Rho2 s3Rho2)
  have hchar : (leftRegular ℂ (Equiv.Perm (Fin 3))).character = R.character := by
    ext x
    rw [s3_reg_character_decomp, character_prod, character_prod, character_prod]
    ring
  rw [artinLocalFactor_eq_of_character_eq hchar g T, artinLocalFactor_prod,
    artinLocalFactor_prod, artinLocalFactor_prod, ← artinLocalFactor_s3_cosetC3, sq]

/-- **Global `S_3` Dedekind Zeta Factorizations & Artin–Brauer–Kuroda Relation (`0` Assumptions)**:
For ANY `S_3`-Frobenius assignment `frob : {p // p.Prime ∧ p ∉ S} → S_3` and `1 < s.re`:
- `Z_Q(s) = artinL S frob s3Triv s` (unramified Riemann zeta),
- `Z_F(s) = artinL S frob ℂ[S_3/C_3] s` (quadratic subfield `F = L^{C_3}`),
- `Z_K(s) = artinL S frob ℂ[S_3/C_2] s` (cubic non-Galois subfield `K = L^{C_2}`),
- `Z_L(s) = artinL S frob ℂ[S_3] s` (full `S_3` Galois closure `L`):
1. `Z_F(s) = Z_Q(s) · L(sgn, s)`,
2. `Z_K(s) = Z_Q(s) · L(ρ₂, s)` (`zeta_K_eq_zeta_Q_mul_artinL_rho2`),
3. `Z_L(s) = Z_F(s) · L(ρ₂, s)²` (`zeta_L_eq_zeta_F_mul_artinL_rho2_sq`),
4. `L(ρ₂, s) = Z_K(s) / Z_Q(s)` (`artinL_rho2_eq_zeta_K_div_zeta_Q`),
5. `Z_L(s) · Z_Q(s)² = Z_F(s) · Z_K(s)²` (`artin_brauer_kuroda_S3`),
6. `L(ρ₂, s) = L_Hecke(ω, s)` (`artinL_rho2_eq_hecke_L_C3`: exact equality with the 1D abelian
   Hecke `L`-function over the quadratic subfield `F = L^{C_3}`!). -/
theorem zeta_F_eq_zeta_Q_mul_artinL_sign (S : Finset ℕ)
    (frob : {p : ℕ // p.Prime ∧ p ∉ S} → Equiv.Perm (Fin 3)) {s : ℂ} (hs : 1 < s.re) :
    artinL S frob (Representation.ofMulAction ℂ (Equiv.Perm (Fin 3))
      (Equiv.Perm (Fin 3) ⧸ s3C3)) s =
      artinL S frob s3Triv s * artinL S frob s3Sign s := by
  unfold artinL
  simp_rw [artinLocalFactor_s3_cosetC3]
  exact (artinL_multipliable S frob s3Triv hs).tprod_mul (artinL_multipliable S frob s3Sign hs)

theorem zeta_K_eq_zeta_Q_mul_artinL_rho2 (S : Finset ℕ)
    (frob : {p : ℕ // p.Prime ∧ p ∉ S} → Equiv.Perm (Fin 3)) {s : ℂ} (hs : 1 < s.re) :
    artinL S frob (Representation.ofMulAction ℂ (Equiv.Perm (Fin 3))
      (Equiv.Perm (Fin 3) ⧸ s3C2)) s =
      artinL S frob s3Triv s * artinL S frob s3Rho2 s := by
  unfold artinL
  simp_rw [artinLocalFactor_s3_cosetC2]
  exact (artinL_multipliable S frob s3Triv hs).tprod_mul (artinL_multipliable S frob s3Rho2 hs)

theorem zeta_L_eq_zeta_F_mul_artinL_rho2_sq (S : Finset ℕ)
    (frob : {p : ℕ // p.Prime ∧ p ∉ S} → Equiv.Perm (Fin 3)) {s : ℂ} (hs : 1 < s.re) :
    artinL S frob (leftRegular ℂ (Equiv.Perm (Fin 3))) s =
      artinL S frob (Representation.ofMulAction ℂ (Equiv.Perm (Fin 3))
        (Equiv.Perm (Fin 3) ⧸ s3C3)) s *
      (artinL S frob s3Rho2 s) ^ 2 := by
  unfold artinL
  simp_rw [artinLocalFactor_s3_regular]
  have h1 := artinL_multipliable S frob
    (Representation.ofMulAction ℂ (Equiv.Perm (Fin 3)) (Equiv.Perm (Fin 3) ⧸ s3C3)) hs
  have h2 := artinL_multipliable S frob s3Rho2 hs
  rw [h1.tprod_mul (h2.pow 2), h2.tprod_pow 2]

theorem artinL_rho2_eq_zeta_K_div_zeta_Q (S : Finset ℕ)
    (frob : {p : ℕ // p.Prime ∧ p ∉ S} → Equiv.Perm (Fin 3)) {s : ℂ} (hs : 1 < s.re) :
    artinL S frob s3Rho2 s =
      artinL S frob (Representation.ofMulAction ℂ (Equiv.Perm (Fin 3))
        (Equiv.Perm (Fin 3) ⧸ s3C2)) s /
      artinL S frob s3Triv s := by
  have hne : artinL S frob s3Triv s ≠ 0 := artinL_ne_zero S frob s3Triv hs
  rw [zeta_K_eq_zeta_Q_mul_artinL_rho2 S frob hs, mul_div_cancel_left₀ _ hne]

theorem artin_brauer_kuroda_S3 (S : Finset ℕ)
    (frob : {p : ℕ // p.Prime ∧ p ∉ S} → Equiv.Perm (Fin 3)) {s : ℂ} (hs : 1 < s.re) :
    artinL S frob (leftRegular ℂ (Equiv.Perm (Fin 3))) s * (artinL S frob s3Triv s) ^ 2 =
      artinL S frob (Representation.ofMulAction ℂ (Equiv.Perm (Fin 3))
        (Equiv.Perm (Fin 3) ⧸ s3C3)) s *
      (artinL S frob (Representation.ofMulAction ℂ (Equiv.Perm (Fin 3))
        (Equiv.Perm (Fin 3) ⧸ s3C2)) s) ^ 2 := by
  rw [zeta_L_eq_zeta_F_mul_artinL_rho2_sq S frob hs, zeta_K_eq_zeta_Q_mul_artinL_rho2 S frob hs]
  ring

/-- **Hecke / Class-Field `L`-Function Identification (`artinL_rho2_eq_hecke_L_C3`)**:
By Artin inductivity and `rho2_eq_ind_C3`, the 2-dimensional non-abelian Artin `L`-function
`L(ρ₂, s)` is IDENTICALLY EQUAL (for ALL `s : ℂ`) to the 1-dimensional abelian Hecke `L`-function
`L_F(ω, s)` over the quadratic subfield `F = L^{C_3}`! -/
theorem artinL_rho2_eq_hecke_L_C3 (S : Finset ℕ)
    (frob : {p : ℕ // p.Prime ∧ p ∉ S} → Equiv.Perm (Fin 3)) (s : ℂ) :
    artinL S frob s3Rho2 s =
      ∏' p : {p : ℕ // p.Prime ∧ p ∉ S},
        ∏ O : CycleOrbits (frob p) (Equiv.Perm (Fin 3) ⧸ s3C3),
          (1 - (s3Omega (orbitMonodromy s3C3 (frob p) O) : ℂ) *
            ((p.1 : ℂ) ^ (-s)) ^ orbitSize (frob p) O)⁻¹ := by
  unfold artinL
  congr 1; ext p
  rw [artinLocalFactor_iso rho2_eq_ind_C3 (frob p) ((p.1 : ℂ) ^ (-s)),
    artinLocalFactor_ind s3C3 (repOfChar s3Omega) (frob p) ((p.1 : ℂ) ^ (-s))]
  apply Finset.prod_congr rfl
  intro O _
  exact artinLocalFactor_repOfChar s3Omega _ _

end ConcreteS3

end DihedralAndS3

/-! ## Section 5: Concrete `ℚ(∛2)` Splitting Law Verification (`X³ - 2` over `𝔽_p`) -/

section ConcreteCbrt2

open Classical

/-- Number of roots of `X³ - 2` in `𝔽_p = ZMod p`. -/
def numRootsCbrt2 (p : ℕ) [NeZero p] : ℕ :=
  (Finset.univ.filter fun x : ZMod p => x ^ 3 = 2).card

/-- Concrete `S_3`-Frobenius conjugacy class representative attached to `X³ - 2` at a prime `p`:
- `p ≡ 2 [MOD 3]` → transposition `swap 1 2` (order 2),
- `p ≡ 1 [MOD 3]` and `2` is a cube mod `p` → identity `1` (order 1),
- `p ≡ 1 [MOD 3]` and `2` is NOT a cube mod `p` → 3-cycle `d3ToS3 (r 1)` (order 3). -/
def frobCbrt2 (p : ℕ) : Equiv.Perm (Fin 3) :=
  if p % 3 = 2 then Equiv.swap (1 : Fin 3) 2
  else if ∃ a : ZMod p, a ^ 3 = 2 then 1
  else d3ToS3 (DihedralGroup.r 1)

lemma orderOf_swap12 : orderOf (Equiv.swap (1 : Fin 3) 2) = 2 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hlt => ?_⟩
  interval_cases m
  decide

lemma orderOf_d3ToS3_r1 : orderOf (d3ToS3 (DihedralGroup.r 1)) = 3 := by
  have h1 : d3ToS3 (DihedralGroup.r 1) = s3EquivD3.symm (DihedralGroup.r 1) := rfl
  rw [h1, MulEquiv.orderOf_eq, orderOf_d3_r1]

/-- **Case 1 (`p ≡ 2 [MOD 3]`)**: for every prime `p ≡ 2 [MOD 3]`, `X³ - 2` has **EXACTLY 1**
root in `𝔽_p`! -/
theorem numRootsCbrt2_mod_three_eq_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hmod : p % 3 = 2) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    numRootsCbrt2 p = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hne2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h0
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 2 ≤ p := hp.two_le
    exact hp2 (le_antisymm hle hge)
  -- x ↦ x^3 is injective on ZMod p because gcd(3, p - 1) = 1
  have hcop : Nat.Coprime 3 (p - 1) := by
    have h1 : (p - 1) % 3 = 1 := by omega
    rw [Nat.Coprime, Nat.gcd_rec, h1]
    decide
  have hcube_inj : Function.Injective (fun x : ZMod p => x ^ 3) := by
    intro x y hxy
    dsimp only at hxy
    by_cases hy0 : y = 0
    · subst hy0
      have hx3 : x ^ 3 = 0 := by simpa using hxy
      exact eq_zero_of_pow_eq_zero hx3
    · have hx0 : x ≠ 0 := by
        intro hx; subst hx
        have : y ^ 3 = 0 := by simpa using hxy.symm
        exact hy0 (eq_zero_of_pow_eq_zero this)
      let u : (ZMod p)ˣ := Units.mk0 (x * y⁻¹) (mul_ne_zero hx0 (inv_ne_zero hy0))
      have hu3 : u ^ 3 = 1 := by
        apply Units.ext
        change (x * y⁻¹) ^ 3 = 1
        rw [mul_pow, inv_pow, hxy, mul_inv_cancel₀ (pow_ne_zero 3 hy0)]
      have hcard_u : Fintype.card (ZMod p)ˣ = p - 1 := by
        rw [ZMod.card_units_eq_totient, Nat.totient_prime hp]
      have hup : u ^ (p - 1) = 1 := by
        rw [← hcard_u]; exact pow_card_eq_one
      have hord_dvd1 : orderOf u ∣ 3 := orderOf_dvd_of_pow_eq_one hu3
      have hord_dvd2 : orderOf u ∣ (p - 1) := orderOf_dvd_of_pow_eq_one hup
      have hord1 : orderOf u = 1 :=
        Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd hord_dvd1 hord_dvd2)
      have hu1 : u = 1 := orderOf_eq_one_iff.mp hord1
      have hxy1 : x * y⁻¹ = 1 := congr_arg Units.val hu1
      calc x = (x * y⁻¹) * y := by rw [mul_assoc, inv_mul_cancel₀ hy0, mul_one]
      _ = y := by rw [hxy1, one_mul]
  have hcube_bij : Function.Bijective (fun x : ZMod p => x ^ 3) :=
    Finite.injective_iff_bijective.mp hcube_inj
  obtain ⟨a, ha⟩ := hcube_bij.2 (2 : ZMod p)
  have hfilt : (Finset.univ.filter fun x : ZMod p => x ^ 3 = 2) = {a} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun hx => hcube_inj (hx.trans ha.symm), fun hx => hx ▸ ha⟩
  unfold numRootsCbrt2
  rw [hfilt, Finset.card_singleton]

/-- **Case 2 (`p ≡ 1 [MOD 3]` and `2` is a cube mod `p`)**: `X³ - 2` splits completely into
**EXACTLY 3** distinct roots in `𝔽_p`! -/
theorem numRootsCbrt2_mod_three_eq_one_of_isCube {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hmod : p % 3 = 1) (hcube : ∃ a : ZMod p, a ^ 3 = 2) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    numRootsCbrt2 p = 3 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := hcube
  have ha0 : a ≠ 0 := by
    intro h0; subst h0
    have h20 : (2 : ZMod p) = 0 := by simpa using ha.symm
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h20
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    exact hp2 (le_antisymm hle hp.two_le)
  -- Find a primitive cube root of unity ζ ∈ (ZMod p)ˣ via cyclicity of (ZMod p)ˣ
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hcard_u : Fintype.card (ZMod p)ˣ = p - 1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hp]
  have hord_g : orderOf g = p - 1 := by
    rw [← hcard_u, ← Nat.card_eq_fintype_card]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  let q : ℕ := (p - 1) / 3
  have h3q : 3 * q = p - 1 := by omega
  let ζu : (ZMod p)ˣ := g ^ q
  let ζ : ZMod p := ζu.1
  have hζ3 : ζ ^ 3 = 1 := by
    have hu : ζu ^ 3 = 1 := by
      dsimp only [ζu]
      rw [← pow_mul, mul_comm, h3q, ← hord_g, pow_orderOf_eq_one]
    exact congr_arg Units.val hu
  have hζ_ne1 : ζ ≠ 1 := by
    intro h1
    have hu : ζu = 1 := Units.ext h1
    have hdvd : orderOf g ∣ q := orderOf_dvd_of_pow_eq_one hu
    rw [hord_g] at hdvd
    have hq_pos : 0 < q := by
      have hp2le := hp.two_le
      dsimp only [q]
      omega
    have hle : p - 1 ≤ q := Nat.le_of_dvd hq_pos hdvd
    omega
  have hζ2_ne1 : ζ ^ 2 ≠ 1 := by
    intro h2
    have hζ1 : ζ = 1 := by
      calc ζ = ζ * 1 := (mul_one ζ).symm
      _ = ζ * ζ ^ 2 := by rw [h2]
      _ = ζ ^ 3 := by ring
      _ = 1 := hζ3
    exact hζ_ne1 hζ1
  have hζ_ne_ζ2 : ζ ≠ ζ ^ 2 := by
    intro heq
    have hζ0 : ζ ≠ 0 := Units.ne_zero ζu
    have h1 : ζ = 1 := mul_left_cancel₀ hζ0 (by rw [mul_one, ← sq]; exact heq.symm)
    exact hζ_ne1 h1
  have hquad : 1 + ζ + ζ ^ 2 = 0 := by
    have hfac : (ζ - 1) * (1 + ζ + ζ ^ 2) = 0 := by
      calc (ζ - 1) * (1 + ζ + ζ ^ 2) = ζ ^ 3 - 1 := by ring
      _ = 0 := by rw [hζ3, sub_self]
    exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hζ_ne1)
  have hfilt : (Finset.univ.filter fun x : ZMod p => x ^ 3 = 2) = {a, ζ * a, ζ ^ 2 * a} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hx
      have hfac : (x - a) * (x - ζ * a) * (x - ζ ^ 2 * a) = 0 := by
        calc (x - a) * (x - ζ * a) * (x - ζ ^ 2 * a)
            = x ^ 3 - (1 + ζ + ζ ^ 2) * a * x ^ 2 + (1 + ζ + ζ ^ 2) * ζ * a ^ 2 * x -
                ζ ^ 3 * a ^ 3 := by ring
        _ = x ^ 3 - 0 * a * x ^ 2 + 0 * ζ * a ^ 2 * x - 1 * a ^ 3 := by rw [hquad, hζ3]
        _ = x ^ 3 - a ^ 3 := by ring
        _ = 0 := by rw [hx, ha, sub_self]
      rcases mul_eq_zero.mp hfac with h12 | h3
      · rcases mul_eq_zero.mp h12 with h1 | h2
        · exact Or.inl (sub_eq_zero.mp h1)
        · exact Or.inr (Or.inl (sub_eq_zero.mp h2))
      · exact Or.inr (Or.inr (sub_eq_zero.mp h3))
    · rintro (rfl | rfl | rfl)
      · exact ha
      · rw [mul_pow, hζ3, one_mul, ha]
      · rw [mul_pow, ← pow_mul, mul_comm 2 3, pow_mul, hζ3, one_pow, one_mul, ha]
  have hne_12 : a ≠ ζ * a := fun h => hζ_ne1 (mul_right_cancel₀ ha0 (by rw [one_mul]; exact h.symm))
  have hne_13 : a ≠ ζ ^ 2 * a := fun h => hζ2_ne1 (mul_right_cancel₀ ha0 (by rw [one_mul]; exact h.symm))
  have hne_23 : ζ * a ≠ ζ ^ 2 * a := fun h => hζ_ne_ζ2 (mul_right_cancel₀ ha0 h)
  unfold numRootsCbrt2
  rw [hfilt, Finset.card_insert_of_notMem (by simp [hne_12, hne_13]),
    Finset.card_pair hne_23]

/-- **Case 3 (`p ≡ 1 [MOD 3]` and `2` is NOT a cube mod `p`)**: `X³ - 2` has **0** roots in `𝔽_p`! -/
theorem numRootsCbrt2_mod_three_eq_one_of_not_isCube {p : ℕ} [NeZero p]
    (hnot : ¬ ∃ a : ZMod p, a ^ 3 = 2) :
    numRootsCbrt2 p = 0 := by
  unfold numRootsCbrt2
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _ hx
  exact hnot ⟨x, hx⟩

/-- **Exact `ℚ(∛2)` Frobenius Classification, Character Trace & Local Euler Factor Law**:
for EVERY prime `p ≠ 2, 3`:
1. `p % 3 = 2` → transposition (`numRootsCbrt2 p = 1`, `tr = 0`, Euler factor `(1 - p^{-2s})⁻¹`),
2. `p % 3 = 1 ∧ ∃ a : ZMod p, a^3 = 2` → identity (`numRootsCbrt2 p = 3`, `tr = 2`, Euler factor `(1 - p^{-s})⁻²`),
3. `p % 3 = 1 ∧ ¬ ∃ a : ZMod p, a^3 = 2` → 3-cycle (`numRootsCbrt2 p = 0`, `tr = -1`, Euler factor `(1 + p^{-s} + p^{-2s})⁻¹`),
and in ALL cases `((numRootsCbrt2 p : ℂ) = 1 + s3Rho2.character (frobCbrt2 p))`! -/
theorem cbrt2_splitting_law_mod_three_eq_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hmod : p % 3 = 2) (s : ℂ) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    numRootsCbrt2 p = 1 ∧
      s3Rho2.character (frobCbrt2 p) = 0 ∧
      artinLocalFactor s3Rho2 (frobCbrt2 p) ((p : ℂ) ^ (-s)) = (1 - (p : ℂ) ^ (-2 * s))⁻¹ := by
  have hfrob : frobCbrt2 p = Equiv.swap (1 : Fin 3) 2 := by simp [frobCbrt2, hmod]
  refine ⟨numRootsCbrt2_mod_three_eq_two hp hp2 hmod, ?_, ?_⟩
  · rw [hfrob, s3Rho2_character_transposition orderOf_swap12]
  · rw [hfrob, artinLocalFactor_s3Rho2_transposition orderOf_swap12]
    congr 2
    rw [← Complex.cpow_nat_mul]
    congr 1; push_cast; ring

theorem cbrt2_splitting_law_mod_three_eq_one_split {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hmod : p % 3 = 1) (hcube : ∃ a : ZMod p, a ^ 3 = 2) (s : ℂ) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    numRootsCbrt2 p = 3 ∧
      s3Rho2.character (frobCbrt2 p) = 2 ∧
      artinLocalFactor s3Rho2 (frobCbrt2 p) ((p : ℂ) ^ (-s)) = (1 - (p : ℂ) ^ (-s))⁻¹ ^ 2 := by
  have hne2 : p % 3 ≠ 2 := by omega
  have hfrob : frobCbrt2 p = 1 := by simp [frobCbrt2, hne2, hcube]
  refine ⟨numRootsCbrt2_mod_three_eq_one_of_isCube hp hp2 hmod hcube, ?_, ?_⟩
  · rw [hfrob, s3Rho2_character_one]
  · rw [hfrob, artinLocalFactor_s3Rho2_one]

theorem cbrt2_splitting_law_mod_three_eq_one_inert {p : ℕ} (hp : p.Prime)
    (hmod : p % 3 = 1) (hnot : ¬ ∃ a : ZMod p, a ^ 3 = 2) (s : ℂ) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    numRootsCbrt2 p = 0 ∧
      s3Rho2.character (frobCbrt2 p) = -1 ∧
      artinLocalFactor s3Rho2 (frobCbrt2 p) ((p : ℂ) ^ (-s)) =
        (1 + (p : ℂ) ^ (-s) + (p : ℂ) ^ (-2 * s))⁻¹ := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hne2 : p % 3 ≠ 2 := by omega
  have hfrob : frobCbrt2 p = d3ToS3 (DihedralGroup.r 1) := by simp [frobCbrt2, hne2, hnot]
  refine ⟨numRootsCbrt2_mod_three_eq_one_of_not_isCube hnot, ?_, ?_⟩
  · rw [hfrob, s3Rho2_character_threeCycle orderOf_d3ToS3_r1]
  · rw [hfrob, artinLocalFactor_s3Rho2_threeCycle orderOf_d3ToS3_r1]
    congr 2
    rw [← Complex.cpow_nat_mul]
    congr 1; push_cast; ring

theorem cbrt2_numRoots_eq_one_add_char {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    (numRootsCbrt2 p : ℂ) = 1 + s3Rho2.character (frobCbrt2 p) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hmod_cases : p % 3 = 1 ∨ p % 3 = 2 := by
    have h0 : p % 3 ≠ 0 := by
      intro h0
      have hdvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
      rcases hp.eq_one_or_self_of_dvd 3 hdvd with h1 | h3
      · omega
      · exact hp3 h3.symm
    omega
  rcases hmod_cases with h1 | h2
  · by_cases hcube : ∃ a : ZMod p, a ^ 3 = 2
    · obtain ⟨hnum, htr, _⟩ := cbrt2_splitting_law_mod_three_eq_one_split hp hp2 h1 hcube 2
      rw [hnum, htr]; norm_num
    · obtain ⟨hnum, htr, _⟩ := cbrt2_splitting_law_mod_three_eq_one_inert hp h1 hcube 2
      rw [hnum, htr]; norm_num
  · obtain ⟨hnum, htr, _⟩ := cbrt2_splitting_law_mod_three_eq_two hp hp2 h2 2
    rw [hnum, htr]; norm_num

/-! ### Concrete Prime Verifications (`p = 5, 7, 11, 13, 31`) & Minimality of `p = 31` -/

theorem cbrt2_prime_5 (s : ℂ) :
    numRootsCbrt2 5 = 1 ∧
      s3Rho2.character (frobCbrt2 5) = 0 ∧
      artinLocalFactor s3Rho2 (frobCbrt2 5) ((5 : ℂ) ^ (-s)) = (1 - (5 : ℂ) ^ (-2 * s))⁻¹ :=
  cbrt2_splitting_law_mod_three_eq_two (by decide) (by decide) (by decide) s

theorem cbrt2_prime_7 (s : ℂ) :
    numRootsCbrt2 7 = 0 ∧
      s3Rho2.character (frobCbrt2 7) = -1 ∧
      artinLocalFactor s3Rho2 (frobCbrt2 7) ((7 : ℂ) ^ (-s)) =
        (1 + (7 : ℂ) ^ (-s) + (7 : ℂ) ^ (-2 * s))⁻¹ :=
  cbrt2_splitting_law_mod_three_eq_one_inert (by decide) (by decide) (by decide) s

theorem cbrt2_prime_11 (s : ℂ) :
    numRootsCbrt2 11 = 1 ∧
      s3Rho2.character (frobCbrt2 11) = 0 ∧
      artinLocalFactor s3Rho2 (frobCbrt2 11) ((11 : ℂ) ^ (-s)) = (1 - (11 : ℂ) ^ (-2 * s))⁻¹ :=
  cbrt2_splitting_law_mod_three_eq_two (by decide) (by decide) (by decide) s

theorem cbrt2_prime_13 (s : ℂ) :
    numRootsCbrt2 13 = 0 ∧
      s3Rho2.character (frobCbrt2 13) = -1 ∧
      artinLocalFactor s3Rho2 (frobCbrt2 13) ((13 : ℂ) ^ (-s)) =
        (1 + (13 : ℂ) ^ (-s) + (13 : ℂ) ^ (-2 * s))⁻¹ :=
  cbrt2_splitting_law_mod_three_eq_one_inert (by decide) (by decide) (by decide) s

theorem cbrt2_prime_31 (s : ℂ) :
    numRootsCbrt2 31 = 3 ∧
      (4 : ZMod 31) ^ 3 = 2 ∧
      s3Rho2.character (frobCbrt2 31) = 2 ∧
      artinLocalFactor s3Rho2 (frobCbrt2 31) ((31 : ℂ) ^ (-s)) = (1 - (31 : ℂ) ^ (-s))⁻¹ ^ 2 := by
  have h4 : (4 : ZMod 31) ^ 3 = 2 := by decide
  obtain ⟨hnum, htr, hfac⟩ :=
    cbrt2_splitting_law_mod_three_eq_one_split (p := 31) (by decide) (by decide) (by decide)
      ⟨4, h4⟩ s
  exact ⟨hnum, h4, htr, hfac⟩

/-- **Minimality of `p = 31`**: `31` is the FIRST prime where `X³ - 2` splits completely! -/
theorem first_split_prime_cbrt2 :
    ∀ p : ℕ, (hp : p.Prime) → p ≠ 2 → p ≠ 3 → p < 31 →
      haveI : NeZero p := ⟨hp.ne_zero⟩
      numRootsCbrt2 p ≠ 3 := by
  intro p hp hp2 hp3 hlt
  have hcases : p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29 := by
    have hle : p ≤ 30 := by omega
    interval_cases p <;> simp_all (config := { decide := true })
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [(cbrt2_prime_5 2).1]; decide
  · rw [(cbrt2_prime_7 2).1]; decide
  · rw [(cbrt2_prime_11 2).1]; decide
  · rw [(cbrt2_prime_13 2).1]; decide
  · rw [numRootsCbrt2_mod_three_eq_two (by decide) (by decide) (by decide)]; decide
  · rw [numRootsCbrt2_mod_three_eq_one_of_not_isCube (by decide)]; decide
  · rw [numRootsCbrt2_mod_three_eq_two (by decide) (by decide) (by decide)]; decide
  · rw [numRootsCbrt2_mod_three_eq_two (by decide) (by decide) (by decide)]; decide

end ConcreteCbrt2

end RHDirect.Stage10ArtinLFunctions
