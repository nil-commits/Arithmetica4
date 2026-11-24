import RHDirect.Stage5ModularHecke
import RHDirect.Stage4SelbergTrace
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# RHDirect.Stage6HeckeSpectral

Spectral Theory of Commuting Normal Hecke Algebras, Petersson-Adjoint Hecke Modules,
Simultaneous Hecke Diagonalization, Atkin–Lehner Multiplicity One, and Eichler–Selberg /
Weil–Deligne Spectral Trace Decomposition in pure Mathlib `v4.33.1` (0 `sorry`, 0 custom `axiom`s).

## Main Results

1. **Simultaneous Spectral Theorem for Commuting Families of Normal Operators**:
   - Unconditional characterization of normal operators `IsNormalOp T := T* ∘ T = T ∘ T*`,
     norm preservation `‖T* x‖ = ‖T x‖`, adjoint eigenvector law `T x = μ • x → T* x = star μ • x`,
     and eigenspace orthogonality.
   - Single-operator normal spectral theorem (`exists_orthonormalBasis_eigenvectors_of_isNormal`)
     and **Finite-Dimensional Fuglede Theorem** (`comm_adjoint_of_comm_isNormal`): if `T` is normal
     and `S ∘ T = T ∘ S`, then `S ∘ T* = T* ∘ S` and `S* ∘ T = T ∘ S*`.
   - **Master Simultaneous Spectral Theorem** (`exists_orthonormalBasis_simultaneous_eigenvectors_of_comm_normal`):
     on any finite-dimensional complex inner product space `H`, every commuting family `ℱ` of normal
     operators admits an orthonormal basis of simultaneous eigenvectors for every `T ∈ ℱ`.
   - **Joint Eigenspace Orthogonality** (`jointEigenspace_orthogonal_of_ne`): joint eigenspaces
     associated to distinct character homomorphisms `λ₁ ≠ λ₂ : 𝕋 → ℂ` are pairwise orthogonal.

2. **Petersson-Adjoint Hecke Spaces `T_n* = conj(χ(n)) • T_n` & Orthonormal Hecke Eigenbasis**:
   - `PeterssonHeckeSpace N k χ H`: finite-dimensional complex inner product space carrying
     commuting Hecke operators `T_n` (`Nat.Coprime n N`) with multiplicative/prime-power algebra
     relations and the Petersson adjoint law `T_n* = star (χ n) • T_n` (`= (χ n)⁻¹ • T_n`).
   - Unconditional proof that every `T_n` (`Nat.Coprime n N`) is normal (`hecke_isNormal`),
     self-adjoint whenever `χ(n) = 1` (`hecke_isSymmetric_of_char_one`), and therefore `H` admits an
     orthonormal basis `{f_1, ..., f_d}` of simultaneous Hecke eigenforms for ALL `T_n`
     (`Nat.Coprime n N`) (`exists_orthonormalBasis_heckeEigenforms`) with exact eigenvalue
     conjugation `star (λ_n(f_j)) = star (χ(n)) * λ_n(f_j)` (real when `χ = 1`) and full Hecke
     multiplicativity & prime-power recurrences.
   - Non-vacuous concrete realization (`diagonalPeterssonHeckeSpace`) from any family of
     self-adjoint normalized eigenforms (e.g. `Stage5ModularHecke.eisensteinCoeff k 1`).

3. **Strong Multiplicity One (Atkin–Lehner) & 1-Dimensional Eigenspaces**:
   - Every non-zero cuspidal (`f 0 = 0`) Hecke eigenform satisfies `f 1 ≠ 0` and normalizes to
     `f = f 1 • f_norm` (`cusp_eigenform_normalize`).
   - Prime Hecke operators generate the full Hecke eigenform action
     (`isHeckeEigenform_of_prime_eigenvalues`).
   - **Normalized Eigenform Multiplicity One** (`normalized_eigenform_eq_of_prime_eigenvalues`):
     two cuspidal normalized Hecke eigenforms with identical prime eigenvalues are **IDENTICAL**
     (plus coprime-to-`N` coefficient determination `normalized_eigenform_eq_on_coprime_of_prime_eigenvalues`).
   - **General Multiplicity One & 1-Dimensional Eigenspaces** (`eigenform_eq_smul_of_prime_eigenvalues`,
     `finrank_cuspHeckeEigenspace_le_one`): any joint prime-Hecke eigenspace on a space with
     injective cuspidal `q`-expansion has `Module.finrank ℂ E ≤ 1`.

4. **Exact Hecke Trace Identities, Spectral Resolution & Eichler–Selberg / `LSeries` / `satakeWDRep` Bridge**:
   - Exact Hecke traces `Tr(T_n) = ∑_j λ_n(f_j)`, `Tr(T_m ∘ T_n) = ∑_j λ_m(f_j) λ_n(f_j)`,
     `Tr(T_n^r) = ∑_j λ_n(f_j)^r`, and Hilbert–Schmidt trace `Tr(T_n* ∘ T_n) = ∑_j ‖λ_n(f_j)‖²`.
   - Spectral resolution of `T_n` along `{f_j}` (`hecke_spectral_expansion`,
     `hecke_inner_spectral_expansion`).
   - Direct Eichler–Selberg / Weil–Deligne trace bridge to `Stage5ModularHecke.satakeWDRep`
     (`hecke_prime_pow_trace_eq_sum_satake`, `hecke_prime_trace_eq_sum_satakeWDRep_trace`,
     `hecke_prime_ramanujan_trace_bound`) and to `Stage5ModularHecke.eigenform_LSeries_eulerProduct`
     via `PeterssonQExpansionSpace` (`peterssonQExpansion_spectral_eulerProduct`).
-/

noncomputable section

open Complex Finset Module Submodule
open RHDirect RHDirect.Stage5ModularHecke RHDirect.Stage4SelbergTrace
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace RHDirect.Stage6HeckeSpectral

/-! ## Section 1: Normal Operators, Finite-Dimensional Fuglede Theorem & Simultaneous Spectral Theorem -/

section SimultaneousNormalSpectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/-- A linear operator `T : H →ₗ[ℂ] H` on a finite-dimensional complex inner product space is
**normal** if it commutes with its Hilbert adjoint: `T* ∘ T = T ∘ T*`. -/
def IsNormalOp (T : H →ₗ[ℂ] H) : Prop :=
  LinearMap.adjoint T ∘ₗ T = T ∘ₗ LinearMap.adjoint T

theorem IsNormalOp.id : IsNormalOp (LinearMap.id : H →ₗ[ℂ] H) := by
  simp [IsNormalOp]

theorem IsNormalOp.smul_id (c : ℂ) : IsNormalOp (c • (LinearMap.id : H →ₗ[ℂ] H)) := by
  simp [IsNormalOp, LinearMap.comp_smul, LinearMap.smul_comp]

theorem IsNormalOp.adjoint_mem {T : H →ₗ[ℂ] H} (hT : IsNormalOp T) :
    IsNormalOp (LinearMap.adjoint T) := by
  unfold IsNormalOp at hT ⊢
  rw [LinearMap.adjoint_adjoint]
  exact hT.symm

/-- For any normal operator `T`, `‖T* x‖ = ‖T x‖` for every `x : H`. -/
theorem IsNormalOp.norm_adjoint_eq {T : H →ₗ[ℂ] H} (hT : IsNormalOp T) (x : H) :
    ‖LinearMap.adjoint T x‖ = ‖T x‖ := by
  have hinner : inner ℂ (LinearMap.adjoint T x) (LinearMap.adjoint T x) = inner ℂ (T x) (T x) := by
    calc inner ℂ (LinearMap.adjoint T x) (LinearMap.adjoint T x)
        = inner ℂ x (T (LinearMap.adjoint T x)) := by
            rw [LinearMap.adjoint_inner_left]
      _ = inner ℂ x ((T ∘ₗ LinearMap.adjoint T) x) := rfl
      _ = inner ℂ x ((LinearMap.adjoint T ∘ₗ T) x) := by rw [← hT]
      _ = inner ℂ (T x) (T x) := by
            rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right]
  have hsq : ‖LinearMap.adjoint T x‖ ^ 2 = ‖T x‖ ^ 2 := by
    have hre := congrArg Complex.re hinner
    simpa [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow] using hre
  nlinarith [norm_nonneg (LinearMap.adjoint T x), norm_nonneg (T x)]

/-- Shifting a normal operator by any scalar multiple of the identity preserves normality. -/
theorem IsNormalOp.sub_smul_id {T : H →ₗ[ℂ] H} (hT : IsNormalOp T) (μ : ℂ) :
    IsNormalOp (T - μ • LinearMap.id) := by
  unfold IsNormalOp at hT ⊢
  have hadj : LinearMap.adjoint (T - μ • LinearMap.id) =
      LinearMap.adjoint T - star μ • LinearMap.id := by
    rw [map_sub, map_smulₛₗ, LinearMap.adjoint_id, starRingEnd_apply]
  rw [hadj]
  ext x
  have hTx : LinearMap.adjoint T (T x) = T (LinearMap.adjoint T x) :=
    LinearMap.congr_fun hT x
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    map_sub, map_smul, hTx, smul_sub, smul_smul, mul_comm (star μ) μ]
  abel

/-- **Adjoint Eigenvector Law for Normal Operators**:
if `T` is normal and `T x = μ • x`, then `T* x = star μ • x`. -/
theorem IsNormalOp.adjoint_apply_of_eigenvector {T : H →ₗ[ℂ] H} (hT : IsNormalOp T)
    {x : H} {μ : ℂ} (hx : T x = μ • x) :
    LinearMap.adjoint T x = star μ • x := by
  have hshift := hT.sub_smul_id μ
  have hzero : (T - μ • (LinearMap.id : H →ₗ[ℂ] H)) x = 0 := by
    simp [hx]
  have hnorm : ‖LinearMap.adjoint (T - μ • (LinearMap.id : H →ₗ[ℂ] H)) x‖ = 0 := by
    rw [hshift.norm_adjoint_eq x, hzero, norm_zero]
  have hadj0 : LinearMap.adjoint (T - μ • (LinearMap.id : H →ₗ[ℂ] H)) x = 0 :=
    norm_eq_zero.mp hnorm
  have hadj : LinearMap.adjoint (T - μ • (LinearMap.id : H →ₗ[ℂ] H)) =
      LinearMap.adjoint T - star μ • LinearMap.id := by
    rw [map_sub, map_smulₛₗ, LinearMap.adjoint_id, starRingEnd_apply]
  rw [hadj] at hadj0
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hadj0
  exact sub_eq_zero.mp hadj0

/-- **Eigenspace Orthogonality for a Normal Operator**:
eigenvectors of a normal operator for distinct eigenvalues are orthogonal. -/
theorem IsNormalOp.inner_eq_zero_of_ne_eigenvalues {T : H →ₗ[ℂ] H} (hT : IsNormalOp T)
    {x y : H} {μ₁ μ₂ : ℂ} (hx : T x = μ₁ • x) (hy : T y = μ₂ • y) (hne : μ₁ ≠ μ₂) :
    inner ℂ x y = 0 := by
  have h1 : μ₂ * inner ℂ x y = μ₁ * inner ℂ x y := by
    calc μ₂ * inner ℂ x y
        = inner ℂ x (μ₂ • y) := by rw [inner_smul_right]
      _ = inner ℂ x (T y) := by rw [hy]
      _ = inner ℂ (LinearMap.adjoint T x) y := by rw [← LinearMap.adjoint_inner_left]
      _ = inner ℂ (star μ₁ • x) y := by rw [hT.adjoint_apply_of_eigenvector hx]
      _ = μ₁ * inner ℂ x y := by rw [inner_smul_left, starRingEnd_apply, star_star]
  have hdiff : (μ₂ - μ₁) * inner ℂ x y = 0 := by
    rw [sub_mul, h1, sub_self]
  exact (mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hne.symm)

/-- If a submodule `W ≤ H` is invariant under both `S` and `S*`, then `Wᗮ` is invariant under
both `S` and `S*`. -/
theorem orthogonal_invariant_of_invariant {S : H →ₗ[ℂ] H} {W : Submodule ℂ H}
    (hS : ∀ w ∈ W, S w ∈ W) (hSadj : ∀ w ∈ W, LinearMap.adjoint S w ∈ W) :
    (∀ v ∈ Wᗮ, S v ∈ Wᗮ) ∧ (∀ v ∈ Wᗮ, LinearMap.adjoint S v ∈ Wᗮ) := by
  constructor
  · intro v hv
    rw [Submodule.mem_orthogonal] at hv ⊢
    intro w hw
    rw [← LinearMap.adjoint_inner_left]
    exact hv (LinearMap.adjoint S w) (hSadj w hw)
  · intro v hv
    rw [Submodule.mem_orthogonal] at hv ⊢
    intro w hw
    rw [LinearMap.adjoint_inner_right]
    exact hv (S w) (hS w hw)

/-- The Hilbert adjoint of the restriction `S|_W` equals the restriction `(S*)|_W` whenever `W`
is invariant under both `S` and `S*`. -/
theorem adjoint_restrict_eq {S : H →ₗ[ℂ] H} {W : Submodule ℂ H}
    (hS : ∀ w ∈ W, S w ∈ W) (hSadj : ∀ w ∈ W, LinearMap.adjoint S w ∈ W) :
    LinearMap.adjoint (S.restrict hS) = (LinearMap.adjoint S).restrict hSadj := by
  apply LinearMap.ext
  intro y
  refine ext_inner_left ℂ fun x => ?_
  rw [LinearMap.adjoint_inner_right]
  change inner ℂ (S x : H) (y : H) = inner ℂ (x : H) (LinearMap.adjoint S y : H)
  exact (LinearMap.adjoint_inner_right S x y).symm

/-- Restricting a normal operator to a jointly `S`- and `S*`-invariant submodule preserves normality. -/
theorem IsNormalOp.restrict {S : H →ₗ[ℂ] H} (hSn : IsNormalOp S) {W : Submodule ℂ H}
    (hS : ∀ w ∈ W, S w ∈ W) (hSadj : ∀ w ∈ W, LinearMap.adjoint S w ∈ W) :
    IsNormalOp (S.restrict hS) := by
  unfold IsNormalOp
  rw [adjoint_restrict_eq hS hSadj]
  ext x
  change (LinearMap.adjoint S (S x) : H) = S (LinearMap.adjoint S x)
  exact LinearMap.congr_fun hSn x

/-- Concatenating orthonormal bases of `W` and `Wᗮ` yields an orthonormal basis of `H`. -/
def orthonormalBasisOfOrthogonalSplit (W : Submodule ℂ H)
    (e₁ : OrthonormalBasis (Fin (Module.finrank ℂ W)) ℂ W)
    (e₂ : OrthonormalBasis (Fin (Module.finrank ℂ Wᗮ)) ℂ Wᗮ) :
    OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H := by
  by_cases h0 : Module.finrank ℂ H = 0
  · exact stdOrthonormalBasis ℂ H
  · have hdim : Module.finrank ℂ W + Module.finrank ℂ Wᗮ = Module.finrank ℂ H :=
      W.finrank_add_finrank_orthogonal
    haveI : Nonempty (Fin (Module.finrank ℂ W + Module.finrank ℂ Wᗮ)) := ⟨⟨0, by omega⟩⟩
    let v : Fin (Module.finrank ℂ W + Module.finrank ℂ Wᗮ) → H :=
      Fin.addCases (fun i => (e₁ i : H)) (fun j => (e₂ j : H))
    have hv : Orthonormal ℂ v := by
      rw [orthonormal_iff_ite]
      intro a b
      refine Fin.addCases (fun i₁ => ?_) (fun j₁ => ?_) a
      · refine Fin.addCases (fun i₂ => ?_) (fun j₂ => ?_) b
        · simp only [v, Fin.addCases_left]
          have heq : (Fin.castAdd (Module.finrank ℂ Wᗮ) i₁ =
              Fin.castAdd (Module.finrank ℂ Wᗮ) i₂) ↔ (i₁ = i₂) :=
            (Fin.castAdd_injective _ _).eq_iff
          simp only [heq]
          exact (orthonormal_iff_ite.mp e₁.orthonormal) i₁ i₂
        · simp only [v, Fin.addCases_left, Fin.addCases_right]
          have hne : Fin.castAdd (Module.finrank ℂ Wᗮ) i₁ ≠
              Fin.natAdd (Module.finrank ℂ W) j₂ := by
            intro h
            have hv := congrArg Fin.val h
            simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
            omega
          rw [if_neg hne]
          exact Submodule.inner_right_of_mem_orthogonal (e₁ i₁).2 (e₂ j₂).2
      · refine Fin.addCases (fun i₂ => ?_) (fun j₂ => ?_) b
        · simp only [v, Fin.addCases_left, Fin.addCases_right]
          have hne : Fin.natAdd (Module.finrank ℂ W) j₁ ≠
              Fin.castAdd (Module.finrank ℂ Wᗮ) i₂ := by
            intro h
            have hv := congrArg Fin.val h
            simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
            omega
          rw [if_neg hne]
          exact Submodule.inner_left_of_mem_orthogonal (e₁ i₂).2 (e₂ j₁).2
        · simp only [v, Fin.addCases_right]
          have heq : (Fin.natAdd (Module.finrank ℂ W) j₁ =
              Fin.natAdd (Module.finrank ℂ W) j₂) ↔ (j₁ = j₂) :=
            (Fin.natAdd_injective _ _).eq_iff
          simp only [heq]
          exact (orthonormal_iff_ite.mp e₂.orthonormal) j₁ j₂
    have hcard : Fintype.card (Fin (Module.finrank ℂ W + Module.finrank ℂ Wᗮ)) =
        Module.finrank ℂ H := by
      rw [Fintype.card_fin, hdim]
    let b := basisOfOrthonormalOfCardEqFinrank hv hcard
    have hb_orth : Orthonormal ℂ b := by
      simpa [b, coe_basisOfOrthonormalOfCardEqFinrank] using hv
    exact (b.toOrthonormalBasis hb_orth).reindex (finCongr hdim)

lemma orthonormalBasisOfOrthogonalSplit_apply_left (W : Submodule ℂ H)
    (e₁ : OrthonormalBasis (Fin (Module.finrank ℂ W)) ℂ W)
    (e₂ : OrthonormalBasis (Fin (Module.finrank ℂ Wᗮ)) ℂ Wᗮ)
    (i : Fin (Module.finrank ℂ W)) :
    orthonormalBasisOfOrthogonalSplit W e₁ e₂
      (finCongr W.finrank_add_finrank_orthogonal (Fin.castAdd _ i)) = (e₁ i : H) := by
  have hne : Module.finrank ℂ H ≠ 0 := by
    have := W.finrank_add_finrank_orthogonal
    have := i.isLt
    omega
  simp [orthonormalBasisOfOrthogonalSplit, hne, coe_basisOfOrthonormalOfCardEqFinrank]

lemma orthonormalBasisOfOrthogonalSplit_apply_right (W : Submodule ℂ H)
    (e₁ : OrthonormalBasis (Fin (Module.finrank ℂ W)) ℂ W)
    (e₂ : OrthonormalBasis (Fin (Module.finrank ℂ Wᗮ)) ℂ Wᗮ)
    (j : Fin (Module.finrank ℂ Wᗮ)) :
    orthonormalBasisOfOrthogonalSplit W e₁ e₂
      (finCongr W.finrank_add_finrank_orthogonal (Fin.natAdd _ j)) = (e₂ j : H) := by
  have hne : Module.finrank ℂ H ≠ 0 := by
    have := W.finrank_add_finrank_orthogonal
    have := j.isLt
    omega
  simp [orthonormalBasisOfOrthogonalSplit, hne, coe_basisOfOrthonormalOfCardEqFinrank]

/-- Helper: every index `k : Fin (finrank H)` comes from either the `W` block or the `Wᗮ` block
under `orthonormalBasisOfOrthogonalSplit`. -/
lemma orthonormalBasisOfOrthogonalSplit_cases (W : Submodule ℂ H)
    (e₁ : OrthonormalBasis (Fin (Module.finrank ℂ W)) ℂ W)
    (e₂ : OrthonormalBasis (Fin (Module.finrank ℂ Wᗮ)) ℂ Wᗮ)
    (k : Fin (Module.finrank ℂ H)) :
    (∃ i : Fin (Module.finrank ℂ W),
      orthonormalBasisOfOrthogonalSplit W e₁ e₂ k = (e₁ i : H)) ∨
    (∃ j : Fin (Module.finrank ℂ Wᗮ),
      orthonormalBasisOfOrthogonalSplit W e₁ e₂ k = (e₂ j : H)) := by
  let k' : Fin (Module.finrank ℂ W + Module.finrank ℂ Wᗮ) :=
    (finCongr W.finrank_add_finrank_orthogonal).symm k
  have hk : finCongr W.finrank_add_finrank_orthogonal k' = k :=
    (finCongr W.finrank_add_finrank_orthogonal).apply_symm_apply k
  rw [← hk]
  refine Fin.addCases (fun i => Or.inl ⟨i, ?_⟩) (fun j => Or.inr ⟨j, ?_⟩) k'
  · exact orthonormalBasisOfOrthogonalSplit_apply_left W e₁ e₂ i
  · exact orthonormalBasisOfOrthogonalSplit_apply_right W e₁ e₂ j

/-- **Single-Operator Normal Spectral Theorem**:
Every normal operator `T : H →ₗ[ℂ] H` on a finite-dimensional complex inner product space admits
an orthonormal basis of eigenvectors. -/
theorem exists_orthonormalBasis_eigenvectors_of_isNormal :
    ∀ {d : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
      (_hd : Module.finrank ℂ V = d) (T : V →ₗ[ℂ] V) (_hT : IsNormalOp T),
      ∃ (e : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V)
        (μ : Fin (Module.finrank ℂ V) → ℂ),
        ∀ i, T (e i) = μ i • e i := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro V _ _ _ hd T hT
    by_cases hd0 : d = 0
    · refine ⟨stdOrthonormalBasis ℂ V, fun _ => 0, fun i => ?_⟩
      exact absurd i.isLt (by omega)
    · have hpos : 0 < Module.finrank ℂ V := by omega
      have : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
      obtain ⟨μ₀, hμ₀⟩ := Module.End.exists_eigenvalue T
      let W : Submodule ℂ V := Module.End.eigenspace T μ₀
      have hW_ne : W ≠ ⊥ := hμ₀
      have hW_pos : 0 < Module.finrank ℂ W := by
        obtain ⟨w, hw, hwne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW_ne
        exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨w, hw⟩, fun h => hwne (congrArg Subtype.val h)⟩
      have hW_inv : ∀ w ∈ W, T w ∈ W := by
        intro w hw
        have hTw : T w = μ₀ • w := Module.End.mem_eigenspace_iff.mp hw
        rw [hTw]
        exact W.smul_mem μ₀ hw
      have hW_adj : ∀ w ∈ W, LinearMap.adjoint T w ∈ W := by
        intro w hw
        have hTw : T w = μ₀ • w := Module.End.mem_eigenspace_iff.mp hw
        rw [hT.adjoint_apply_of_eigenvector hTw]
        exact W.smul_mem (star μ₀) hw
      have hWort := orthogonal_invariant_of_invariant hW_inv hW_adj
      have hdim_sum : Module.finrank ℂ W + Module.finrank ℂ Wᗮ = d := by
        rw [W.finrank_add_finrank_orthogonal, hd]
      have hWort_lt : Module.finrank ℂ Wᗮ < d := by omega
      obtain ⟨e₂, μ₂, he₂⟩ := ih (Module.finrank ℂ Wᗮ) hWort_lt rfl
        (T.restrict hWort.1) (hT.restrict hWort.1 hWort.2)
      let e₁ : OrthonormalBasis (Fin (Module.finrank ℂ W)) ℂ W := stdOrthonormalBasis ℂ W
      let e : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V :=
        orthonormalBasisOfOrthogonalSplit W e₁ e₂
      let μ : Fin (Module.finrank ℂ V) → ℂ := fun k =>
        Fin.addCases (fun _ => μ₀) μ₂ ((finCongr W.finrank_add_finrank_orthogonal).symm k)
      refine ⟨e, μ, fun k => ?_⟩
      let k' : Fin (Module.finrank ℂ W + Module.finrank ℂ Wᗮ) :=
        (finCongr W.finrank_add_finrank_orthogonal).symm k
      have hk : finCongr W.finrank_add_finrank_orthogonal k' = k :=
        (finCongr W.finrank_add_finrank_orthogonal).apply_symm_apply k
      rw [← hk]
      refine Fin.addCases
        (motive := fun x =>
          T (e (finCongr W.finrank_add_finrank_orthogonal x)) =
            μ (finCongr W.finrank_add_finrank_orthogonal x) •
              e (finCongr W.finrank_add_finrank_orthogonal x))
        (fun i => ?_) (fun j => ?_) k'
      · simp only [e, μ, Equiv.symm_apply_apply, Fin.addCases_left,
          orthonormalBasisOfOrthogonalSplit_apply_left]
        exact Module.End.mem_eigenspace_iff.mp (e₁ i).2
      · simp only [e, μ, Equiv.symm_apply_apply, Fin.addCases_right,
          orthonormalBasisOfOrthogonalSplit_apply_right]
        exact congrArg Subtype.val (he₂ j)

/-- **Finite-Dimensional Fuglede Theorem**:
If `T : H →ₗ[ℂ] H` is normal and `S` commutes with `T` (`S ∘ T = T ∘ S`), then:
1. `S` commutes with `T*` (`S ∘ T* = T* ∘ S`), and
2. `S*` commutes with `T` (`S* ∘ T = T ∘ S*`). -/
theorem comm_adjoint_of_comm_isNormal {S T : H →ₗ[ℂ] H}
    (hT : IsNormalOp T) (hcomm : S ∘ₗ T = T ∘ₗ S) :
    (S ∘ₗ LinearMap.adjoint T = LinearMap.adjoint T ∘ₗ S) ∧
    (LinearMap.adjoint S ∘ₗ T = T ∘ₗ LinearMap.adjoint S) := by
  obtain ⟨e, μ, he⟩ := exists_orthonormalBasis_eigenvectors_of_isNormal rfl T hT
  have he_adj : ∀ i, LinearMap.adjoint T (e i) = star (μ i) • e i :=
    fun i => hT.adjoint_apply_of_eigenvector (he i)
  have hzero_off : ∀ i j, μ i ≠ μ j → inner ℂ (e i) (S (e j)) = 0 := by
    intro i j hne
    have h1 : μ j * inner ℂ (e i) (S (e j)) = μ i * inner ℂ (e i) (S (e j)) := by
      calc μ j * inner ℂ (e i) (S (e j))
          = inner ℂ (e i) (S (μ j • e j)) := by rw [map_smul, inner_smul_right]
        _ = inner ℂ (e i) ((S ∘ₗ T) (e j)) := by rw [LinearMap.comp_apply, he j]
        _ = inner ℂ (e i) ((T ∘ₗ S) (e j)) := by rw [hcomm]
        _ = inner ℂ (LinearMap.adjoint T (e i)) (S (e j)) := by
              rw [LinearMap.comp_apply, ← LinearMap.adjoint_inner_left]
        _ = inner ℂ (star (μ i) • e i) (S (e j)) := by rw [he_adj i]
        _ = μ i * inner ℂ (e i) (S (e j)) := by
              rw [inner_smul_left, starRingEnd_apply, star_star]
    have hdiff : (μ j - μ i) * inner ℂ (e i) (S (e j)) = 0 := by
      rw [sub_mul, h1, sub_self]
    exact (mul_eq_zero.mp hdiff).resolve_left (sub_ne_zero.mpr hne.symm)
  have h1 : S ∘ₗ LinearMap.adjoint T = LinearMap.adjoint T ∘ₗ S := by
    apply e.toBasis.ext
    intro j
    rw [OrthonormalBasis.coe_toBasis]
    apply e.repr.injective
    ext i
    rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply]
    have hL : inner ℂ (e i) ((S ∘ₗ LinearMap.adjoint T) (e j)) =
        star (μ j) * inner ℂ (e i) (S (e j)) := by
      rw [LinearMap.comp_apply, he_adj j, map_smul, inner_smul_right]
    have hR : inner ℂ (e i) ((LinearMap.adjoint T ∘ₗ S) (e j)) =
        star (μ i) * inner ℂ (e i) (S (e j)) := by
      rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, he i, inner_smul_left,
          starRingEnd_apply]
    rw [hL, hR]
    by_cases hij : μ i = μ j
    · rw [hij]
    · rw [hzero_off i j hij, mul_zero, mul_zero]
  have h2 : LinearMap.adjoint S ∘ₗ T = T ∘ₗ LinearMap.adjoint S := by
    have hadj := congrArg LinearMap.adjoint h1
    rw [LinearMap.adjoint_comp, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint] at hadj
    exact hadj.symm
  exact ⟨h1, h2⟩

private theorem simultaneous_spectral_aux :
    ∀ {d : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
      (_hd : Module.finrank ℂ V = d) (ℱ : Set (V →ₗ[ℂ] V))
      (_hnorm : ∀ T ∈ ℱ, IsNormalOp T)
      (_hcomm : ∀ S ∈ ℱ, ∀ T ∈ ℱ, S ∘ₗ T = T ∘ₗ S),
      ∃ (e : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V),
        ∀ T ∈ ℱ, ∀ i, ∃ μ : ℂ, T (e i) = μ • e i := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro V _ _ _ hd ℱ hnorm hcomm
    by_cases hd0 : d = 0
    · refine ⟨stdOrthonormalBasis ℂ V, fun _ _ i => ?_⟩
      exact absurd i.isLt (by omega)
    · by_cases hall : ∀ T ∈ ℱ, ∃ c : ℂ, T = c • LinearMap.id
      · refine ⟨stdOrthonormalBasis ℂ V, fun T hT i => ?_⟩
        obtain ⟨c, rfl⟩ := hall T hT
        exact ⟨c, by simp⟩
      · push Not at hall
        obtain ⟨T₀, hT₀_mem, hT₀_not_scalar⟩ := hall
        have hpos : 0 < Module.finrank ℂ V := by omega
        have : Nontrivial V := Module.nontrivial_of_finrank_pos hpos
        obtain ⟨μ₀, hμ₀⟩ := Module.End.exists_eigenvalue T₀
        let W : Submodule ℂ V := Module.End.eigenspace T₀ μ₀
        have hW_ne_bot : W ≠ ⊥ := hμ₀
        have hW_ne_top : W ≠ ⊤ := by
          intro htop
          apply hT₀_not_scalar μ₀
          ext x
          have hx : x ∈ W := by rw [htop]; trivial
          exact Module.End.mem_eigenspace_iff.mp hx
        have hW_pos : 0 < Module.finrank ℂ W := by
          obtain ⟨w, hw, hwne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW_ne_bot
          exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨w, hw⟩, fun h => hwne (congrArg Subtype.val h)⟩
        have hWort_ne_bot : Wᗮ ≠ ⊥ := by
          intro hbot
          apply hW_ne_top
          rw [← W.orthogonal_orthogonal, hbot]
          ext x
          simp
        have hWort_pos : 0 < Module.finrank ℂ Wᗮ := by
          obtain ⟨w, hw, hwne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWort_ne_bot
          exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨w, hw⟩, fun h => hwne (congrArg Subtype.val h)⟩
        have hdim_sum : Module.finrank ℂ W + Module.finrank ℂ Wᗮ = d := by
          rw [W.finrank_add_finrank_orthogonal, hd]
        have hW_lt : Module.finrank ℂ W < d := by omega
        have hWort_lt : Module.finrank ℂ Wᗮ < d := by omega
        have hS_W : ∀ S ∈ ℱ, (∀ w ∈ W, S w ∈ W) ∧ (∀ w ∈ W, LinearMap.adjoint S w ∈ W) := by
          intro S hS
          have hST : S ∘ₗ T₀ = T₀ ∘ₗ S := hcomm S hS T₀ hT₀_mem
          have hSadjT : LinearMap.adjoint S ∘ₗ T₀ = T₀ ∘ₗ LinearMap.adjoint S :=
            (comm_adjoint_of_comm_isNormal (hnorm T₀ hT₀_mem) hST).2
          constructor
          · intro w hw
            have hTw : T₀ w = μ₀ • w := Module.End.mem_eigenspace_iff.mp hw
            rw [Module.End.mem_eigenspace_iff]
            calc T₀ (S w) = (T₀ ∘ₗ S) w := rfl
              _ = (S ∘ₗ T₀) w := by rw [hST]
              _ = S (μ₀ • w) := by rw [LinearMap.comp_apply, hTw]
              _ = μ₀ • S w := map_smul S μ₀ w
          · intro w hw
            have hTw : T₀ w = μ₀ • w := Module.End.mem_eigenspace_iff.mp hw
            rw [Module.End.mem_eigenspace_iff]
            calc T₀ (LinearMap.adjoint S w) = (T₀ ∘ₗ LinearMap.adjoint S) w := rfl
              _ = (LinearMap.adjoint S ∘ₗ T₀) w := by rw [hSadjT]
              _ = LinearMap.adjoint S (μ₀ • w) := by rw [LinearMap.comp_apply, hTw]
              _ = μ₀ • LinearMap.adjoint S w := map_smul _ μ₀ w
        have hS_Wort : ∀ S ∈ ℱ,
            (∀ v ∈ Wᗮ, S v ∈ Wᗮ) ∧ (∀ v ∈ Wᗮ, LinearMap.adjoint S v ∈ Wᗮ) :=
          fun S hS => orthogonal_invariant_of_invariant (hS_W S hS).1 (hS_W S hS).2
        let ℱ₁ : Set (W →ₗ[ℂ] W) :=
          { R | ∃ (S : V →ₗ[ℂ] V) (hS : S ∈ ℱ), R = S.restrict (hS_W S hS).1 }
        let ℱ₂ : Set (Wᗮ →ₗ[ℂ] Wᗮ) :=
          { R | ∃ (S : V →ₗ[ℂ] V) (hS : S ∈ ℱ), R = S.restrict (hS_Wort S hS).1 }
        have hnorm₁ : ∀ R ∈ ℱ₁, IsNormalOp R := by
          rintro R ⟨S, hS, rfl⟩
          exact (hnorm S hS).restrict (hS_W S hS).1 (hS_W S hS).2
        have hcomm₁ : ∀ R₁ ∈ ℱ₁, ∀ R₂ ∈ ℱ₁, R₁ ∘ₗ R₂ = R₂ ∘ₗ R₁ := by
          rintro R₁ ⟨S₁, hS₁, rfl⟩ R₂ ⟨S₂, hS₂, rfl⟩
          ext w
          change S₁ (S₂ w) = S₂ (S₁ w)
          exact LinearMap.congr_fun (hcomm S₁ hS₁ S₂ hS₂) w
        have hnorm₂ : ∀ R ∈ ℱ₂, IsNormalOp R := by
          rintro R ⟨S, hS, rfl⟩
          exact (hnorm S hS).restrict (hS_Wort S hS).1 (hS_Wort S hS).2
        have hcomm₂ : ∀ R₁ ∈ ℱ₂, ∀ R₂ ∈ ℱ₂, R₁ ∘ₗ R₂ = R₂ ∘ₗ R₁ := by
          rintro R₁ ⟨S₁, hS₁, rfl⟩ R₂ ⟨S₂, hS₂, rfl⟩
          ext v
          change S₁ (S₂ v) = S₂ (S₁ v)
          exact LinearMap.congr_fun (hcomm S₁ hS₁ S₂ hS₂) v
        obtain ⟨e₁, he₁⟩ := ih (Module.finrank ℂ W) hW_lt rfl ℱ₁ hnorm₁ hcomm₁
        obtain ⟨e₂, he₂⟩ := ih (Module.finrank ℂ Wᗮ) hWort_lt rfl ℱ₂ hnorm₂ hcomm₂
        refine ⟨orthonormalBasisOfOrthogonalSplit W e₁ e₂, fun S hS k => ?_⟩
        rcases orthonormalBasisOfOrthogonalSplit_cases W e₁ e₂ k with ⟨i, hki⟩ | ⟨j, hkj⟩
        · rw [hki]
          obtain ⟨μ, hμ⟩ := he₁ (S.restrict (hS_W S hS).1) ⟨S, hS, rfl⟩ i
          exact ⟨μ, congrArg Subtype.val hμ⟩
        · rw [hkj]
          obtain ⟨μ, hμ⟩ := he₂ (S.restrict (hS_Wort S hS).1) ⟨S, hS, rfl⟩ j
          exact ⟨μ, congrArg Subtype.val hμ⟩

/-- **Simultaneous Spectral Theorem for Commuting Families of Normal Operators (Unconditional)**:
On any finite-dimensional complex inner product space `H`, if `ℱ : Set (H →ₗ[ℂ] H)` is a commuting
family of normal operators (`∀ T ∈ ℱ, T* ∘ T = T ∘ T*` and `∀ S T ∈ ℱ, S ∘ T = T ∘ S`), then
`H` admits an orthonormal basis `e` of simultaneous eigenvectors for EVERY `T ∈ ℱ`, with explicit
eigenvalue function `ev T i = ⟨e i, T (e i)⟩`. -/
theorem exists_orthonormalBasis_simultaneous_eigenvectors_of_comm_normal
    (ℱ : Set (H →ₗ[ℂ] H))
    (hnorm : ∀ T ∈ ℱ, LinearMap.adjoint T ∘ₗ T = T ∘ₗ LinearMap.adjoint T)
    (hcomm : ∀ S ∈ ℱ, ∀ T ∈ ℱ, S ∘ₗ T = T ∘ₗ S) :
    ∃ (e : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H)
      (ev : (H →ₗ[ℂ] H) → Fin (Module.finrank ℂ H) → ℂ),
      ∀ T ∈ ℱ, ∀ i, T (e i) = ev T i • e i := by
  obtain ⟨e, he⟩ := simultaneous_spectral_aux rfl ℱ hnorm hcomm
  refine ⟨e, fun T i => inner ℂ (e i) (T (e i)), fun T hT i => ?_⟩
  obtain ⟨μ, hμ⟩ := he T hT i
  have hμ_eq : inner ℂ (e i) (T (e i)) = μ := by
    rw [hμ, inner_smul_right, inner_self_eq_norm_sq_to_K, e.orthonormal.1 i]
    simp
  dsimp only
  rw [hμ_eq]
  exact hμ

/-- Joint eigenspace attached to an operator family `ρ : 𝕋 → (H →ₗ[ℂ] H)` and a character
`lam : 𝕋 → ℂ`: `E(lam) = { x ∈ H | ∀ t : 𝕋, ρ t x = lam t • x }`. -/
def jointEigenspace {𝕋 : Type*} (ρ : 𝕋 → (H →ₗ[ℂ] H)) (lam : 𝕋 → ℂ) : Submodule ℂ H where
  carrier := { x | ∀ t : 𝕋, ρ t x = lam t • x }
  add_mem' hx hy t := by simp [map_add, hx t, hy t, smul_add]
  zero_mem' t := by simp
  smul_mem' c x hx t := by simp [map_smul, hx t, smul_comm c (lam t)]

omit [FiniteDimensional ℂ H] in
@[simp]
theorem mem_jointEigenspace_iff {𝕋 : Type*} (ρ : 𝕋 → (H →ₗ[ℂ] H)) (lam : 𝕋 → ℂ) (x : H) :
    x ∈ jointEigenspace ρ lam ↔ ∀ t : 𝕋, ρ t x = lam t • x :=
  Iff.rfl

/-- **Joint Eigenspace Orthogonality**:
For any family of normal operators `ρ : 𝕋 → (H →ₗ[ℂ] H)` and any two distinct character
homomorphisms `λ₁ ≠ λ₂ : 𝕋 → ℂ`, their joint eigenspaces are orthogonal:
`∀ x ∈ E(λ₁), ∀ y ∈ E(λ₂), ⟨x, y⟩ = 0`. -/
theorem jointEigenspace_orthogonal_of_ne {𝕋 : Type*} (ρ : 𝕋 → (H →ₗ[ℂ] H))
    (hnorm : ∀ t : 𝕋, IsNormalOp (ρ t)) {lam₁ lam₂ : 𝕋 → ℂ} (hne : lam₁ ≠ lam₂) :
    ∀ x ∈ jointEigenspace ρ lam₁, ∀ y ∈ jointEigenspace ρ lam₂, inner ℂ x y = 0 := by
  have hex : ∃ t : 𝕋, lam₁ t ≠ lam₂ t := by
    by_contra h
    push Not at h
    exact hne (funext h)
  obtain ⟨t, ht⟩ := hex
  intro x hx y hy
  exact (hnorm t).inner_eq_zero_of_ne_eigenvalues (hx t) (hy t) ht

/-- Submodule orthogonality form: `jointEigenspace ρ lam₁ ≤ (jointEigenspace ρ lam₂)ᗮ`
whenever `lam₁ ≠ lam₂`. -/
theorem jointEigenspace_le_orthogonal_of_ne {𝕋 : Type*} (ρ : 𝕋 → (H →ₗ[ℂ] H))
    (hnorm : ∀ t : 𝕋, IsNormalOp (ρ t)) {lam₁ lam₂ : 𝕋 → ℂ} (hne : lam₁ ≠ lam₂) :
    jointEigenspace ρ lam₁ ≤ (jointEigenspace ρ lam₂)ᗮ := by
  intro x hx
  rw [Submodule.mem_orthogonal]
  intro y hy
  exact (jointEigenspace_orthogonal_of_ne ρ hnorm hne.symm) y hy x hx

/-- Indexed pairwise orthogonality of joint eigenspaces for any injective family of characters
`Λ : ι → (𝕋 → ℂ)`. -/
theorem jointEigenspace_pairwise_orthogonal {𝕋 ι : Type*} (ρ : 𝕋 → (H →ₗ[ℂ] H))
    (hnorm : ∀ t : 𝕋, IsNormalOp (ρ t)) (Λ : ι → (𝕋 → ℂ)) (hinj : Function.Injective Λ) :
    Pairwise (fun i j : ι => ∀ x ∈ jointEigenspace ρ (Λ i), ∀ y ∈ jointEigenspace ρ (Λ j),
      inner ℂ x y = 0) :=
  fun _ _ hij => jointEigenspace_orthogonal_of_ne ρ hnorm (fun h => hij (hinj h))

end SimultaneousNormalSpectral

/-! ## Section 2: Petersson-Adjoint Hecke Spaces & Existence of an Orthonormal Hecke Eigenbasis -/

section PeterssonHeckeSpaces

/-- For a Dirichlet character `χ` mod `N` (`NeZero N`) and `Nat.Coprime n N`,
`star (χ n) = (χ n)⁻¹`. -/
theorem star_dirichletChar_eq_inv_of_coprime {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {n : ℕ} (hcop : Nat.Coprime n N) :
    star (χ (n : ZMod N)) = (χ (n : ZMod N))⁻¹ := by
  have hnorm : ‖χ (n : ZMod N)‖ = 1 := norm_dirichletChar_eq_one_of_coprime χ hcop
  have hmul : χ (n : ZMod N) * star (χ (n : ZMod N)) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm, one_pow,
        Complex.ofReal_one]
  exact eq_inv_of_mul_eq_one_right hmul

/-- **Finite-Dimensional Petersson–Hecke Space of Weight `k`, Level `N`, Nebentypus `χ`**:
a finite-dimensional complex inner product space `H` (modelling `S_k(Γ₀(N), χ)` with the
Petersson inner product) carrying the Hecke algebra `{T_n}` with commuting, multiplicative,
prime-power relations and the **Petersson Adjoint Law** `T_n* = conj(χ(n)) • T_n` for all
`Nat.Coprime n N`. -/
structure PeterssonHeckeSpace (N k : ℕ) (χ : DirichletCharacter ℂ N) (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] where
  /-- The `n`-th Hecke operator `T_n : H →ₗ[ℂ] H`. -/
  hecke : ℕ → (H →ₗ[ℂ] H)
  /-- `T_1 = id`. -/
  hecke_one : hecke 1 = LinearMap.id
  /-- Commutativity of Hecke operators for indices coprime to the level `N`. -/
  hecke_comm : ∀ m n : ℕ, Nat.Coprime m N → Nat.Coprime n N →
    hecke m ∘ₗ hecke n = hecke n ∘ₗ hecke m
  /-- Coprime multiplicativity `T_m ∘ T_n = T_{m * n}` for indices coprime to `N`. -/
  hecke_mul_of_coprime : ∀ m n : ℕ, Nat.Coprime m N → Nat.Coprime n N → Nat.Coprime m n →
    hecke m ∘ₗ hecke n = hecke (m * n)
  /-- Prime-power Hecke recurrence for unramified primes `p ∤ N`:
  `T_{p^{r+1}} = T_p ∘ T_{p^r} - χ(p) · p^{k-1} · T_{p^{r-1}}`. -/
  hecke_prime_pow : ∀ p : ℕ, p.Prime → Nat.Coprime p N → ∀ r : ℕ, 1 ≤ r →
    hecke (p ^ (r + 1)) =
      hecke p ∘ₗ hecke (p ^ r) - (χ (p : ZMod N) * (p : ℂ) ^ (k - 1)) • hecke (p ^ (r - 1))
  /-- **Petersson Adjoint Law**: `T_n* = conj(χ(n)) • T_n` for all `Nat.Coprime n N`. -/
  hecke_adjoint : ∀ n : ℕ, Nat.Coprime n N →
    LinearMap.adjoint (hecke n) = star (χ (n : ZMod N)) • hecke n

variable {N k : ℕ} {χ : DirichletCharacter ℂ N}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/-- Equivalent inverse form of the Petersson adjoint law: `T_n* = χ(n)⁻¹ • T_n` when `NeZero N`. -/
theorem PeterssonHeckeSpace.hecke_adjoint_inv [NeZero N]
    (S : PeterssonHeckeSpace N k χ H) {n : ℕ} (hcop : Nat.Coprime n N) :
    LinearMap.adjoint (S.hecke n) = (χ (n : ZMod N))⁻¹ • S.hecke n := by
  rw [S.hecke_adjoint n hcop, star_dirichletChar_eq_inv_of_coprime χ hcop]

/-- **Every Hecke operator `T_n` (`Nat.Coprime n N`) on a `PeterssonHeckeSpace` is NORMAL**:
`T_n* ∘ T_n = T_n ∘ T_n*`. -/
theorem PeterssonHeckeSpace.hecke_isNormal
    (S : PeterssonHeckeSpace N k χ H) {n : ℕ} (hcop : Nat.Coprime n N) :
    IsNormalOp (S.hecke n) := by
  unfold IsNormalOp
  rw [S.hecke_adjoint n hcop, LinearMap.smul_comp, LinearMap.comp_smul]

/-- Whenever `χ(n) = 1`, `T_n` is Hermitian (`IsSymmetric`) for the Petersson inner product. -/
theorem PeterssonHeckeSpace.hecke_isSymmetric_of_char_one
    (S : PeterssonHeckeSpace N k χ H) {n : ℕ} (hcop : Nat.Coprime n N)
    (hχ : χ (n : ZMod N) = 1) :
    (S.hecke n).IsSymmetric := by
  intro u v
  rw [← LinearMap.adjoint_inner_right, S.hecke_adjoint n hcop, hχ, star_one, one_smul]

/-- For trivial Nebentypus (`χ = 1`), every `T_n` (`Nat.Coprime n N`) is Petersson self-adjoint. -/
theorem PeterssonHeckeSpace.hecke_isSymmetric_of_trivialChar [NeZero N]
    (S : PeterssonHeckeSpace N k (1 : DirichletCharacter ℂ N) H)
    {n : ℕ} (hcop : Nat.Coprime n N) :
    (S.hecke n).IsSymmetric := by
  apply S.hecke_isSymmetric_of_char_one hcop
  have hu : IsUnit (n : ZMod N) := (ZMod.isUnit_iff_coprime n N).mpr hcop
  exact MulChar.one_apply hu

/-- **Exact Petersson Eigenvalue Conjugation Law**:
for any nonzero eigenvector `T_n v = μ • v` (`Nat.Coprime n N`),
`conj(μ) = conj(χ(n)) * μ`. -/
theorem PeterssonHeckeSpace.eigenvalue_star_eq
    (S : PeterssonHeckeSpace N k χ H) {n : ℕ} (hcop : Nat.Coprime n N)
    {v : H} (hv : v ≠ 0) {μ : ℂ} (heig : S.hecke n v = μ • v) :
    star μ = star (χ (n : ZMod N)) * μ := by
  have h1 : LinearMap.adjoint (S.hecke n) v = star μ • v :=
    (S.hecke_isNormal hcop).adjoint_apply_of_eigenvector heig
  have h2 : LinearMap.adjoint (S.hecke n) v = (star (χ (n : ZMod N)) * μ) • v := by
    rw [S.hecke_adjoint n hcop, LinearMap.smul_apply, heig, smul_smul]
  exact smul_left_injective ℂ hv (h1.symm.trans h2)

/-- Whenever `χ(n) = 1`, every Hecke eigenvalue `μ` of `T_n` (`Nat.Coprime n N`) is purely REAL
(`μ.im = 0`). -/
theorem PeterssonHeckeSpace.eigenvalue_im_eq_zero_of_char_one
    (S : PeterssonHeckeSpace N k χ H) {n : ℕ} (hcop : Nat.Coprime n N)
    (hχ : χ (n : ZMod N) = 1) {v : H} (hv : v ≠ 0) {μ : ℂ}
    (heig : S.hecke n v = μ • v) :
    μ.im = 0 := by
  have hst := S.eigenvalue_star_eq hcop hv heig
  rw [hχ, star_one, one_mul] at hst
  exact Complex.conj_eq_iff_im.mp hst

/-- Distinct simultaneous Hecke eigenforms are Petersson-orthogonal. -/
theorem PeterssonHeckeSpace.inner_eq_zero_of_distinct_eigenvalues
    (S : PeterssonHeckeSpace N k χ H) {u v : H} {lam₁ lam₂ : ℕ → ℂ}
    (hu : ∀ n, Nat.Coprime n N → S.hecke n u = lam₁ n • u)
    (hv : ∀ n, Nat.Coprime n N → S.hecke n v = lam₂ n • v)
    {n : ℕ} (hcop : Nat.Coprime n N) (hne : lam₁ n ≠ lam₂ n) :
    inner ℂ u v = 0 :=
  (S.hecke_isNormal hcop).inner_eq_zero_of_ne_eigenvalues (hu n hcop) (hv n hcop) hne

/-- **UNCONDITIONAL EXISTENCE OF AN ORTHONORMAL HECKE EIGENBASIS**:
Every finite-dimensional `PeterssonHeckeSpace N k χ H` admits an orthonormal basis
`{f_1, ..., f_d}` of simultaneous Hecke eigenforms for ALL `T_n` (`Nat.Coprime n N`), satisfying:
1. `T_n f_j = λ_n(f_j) • f_j`,
2. Exact Petersson conjugation `conj(λ_n(f_j)) = conj(χ(n)) * λ_n(f_j)`,
3. `λ_1(f_j) = 1`,
4. Coprime multiplicativity `λ_{mn}(f_j) = λ_m(f_j) * λ_n(f_j)`,
5. Prime-power recurrence `λ_{p^{r+1}}(f_j) = λ_p(f_j) λ_{p^r}(f_j) - χ(p) p^{k-1} λ_{p^{r-1}}(f_j)`. -/
theorem exists_orthonormalBasis_heckeEigenforms (S : PeterssonHeckeSpace N k χ H) :
    ∃ (f : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H)
      (lam : Fin (Module.finrank ℂ H) → ℕ → ℂ),
      (∀ j n, Nat.Coprime n N → S.hecke n (f j) = lam j n • f j) ∧
      (∀ j n, Nat.Coprime n N → star (lam j n) = star (χ (n : ZMod N)) * lam j n) ∧
      (∀ j, lam j 1 = 1) ∧
      (∀ j m n, Nat.Coprime m N → Nat.Coprime n N → Nat.Coprime m n →
        lam j (m * n) = lam j m * lam j n) ∧
      (∀ j p, p.Prime → Nat.Coprime p N → ∀ r, 1 ≤ r →
        lam j (p ^ (r + 1)) =
          lam j p * lam j (p ^ r) -
            χ (p : ZMod N) * (p : ℂ) ^ (k - 1) * lam j (p ^ (r - 1))) := by
  let ℱ : Set (H →ₗ[ℂ] H) := { T | ∃ n : ℕ, Nat.Coprime n N ∧ T = S.hecke n }
  have hnorm : ∀ T ∈ ℱ, LinearMap.adjoint T ∘ₗ T = T ∘ₗ LinearMap.adjoint T := by
    rintro T ⟨n, hcop, rfl⟩
    exact S.hecke_isNormal hcop
  have hcomm : ∀ A ∈ ℱ, ∀ B ∈ ℱ, A ∘ₗ B = B ∘ₗ A := by
    rintro A ⟨m, hm, rfl⟩ B ⟨n, hn, rfl⟩
    exact S.hecke_comm m n hm hn
  obtain ⟨f, ev, hev⟩ :=
    exists_orthonormalBasis_simultaneous_eigenvectors_of_comm_normal ℱ hnorm hcomm
  let lam : Fin (Module.finrank ℂ H) → ℕ → ℂ := fun j n => ev (S.hecke n) j
  have hf_ne : ∀ j, f j ≠ 0 := fun j => f.orthonormal.ne_zero j
  have heig : ∀ j n, Nat.Coprime n N → S.hecke n (f j) = lam j n • f j :=
    fun j n hcop => hev (S.hecke n) ⟨n, hcop, rfl⟩ j
  refine ⟨f, lam, heig, ?_, ?_, ?_, ?_⟩
  · intro j n hcop
    exact S.eigenvalue_star_eq hcop (hf_ne j) (heig j n hcop)
  · intro j
    have h1 := heig j 1 (Nat.coprime_one_left N)
    rw [S.hecke_one, LinearMap.id_apply] at h1
    exact (smul_left_injective ℂ (hf_ne j) (h1.symm.trans (one_smul ℂ (f j)).symm))
  · intro j m n hm hn hmn
    have hcop_mul : Nat.Coprime (m * n) N := hm.mul_left hn
    have hL := heig j (m * n) hcop_mul
    have hR : S.hecke (m * n) (f j) = (lam j m * lam j n) • f j := by
      rw [← S.hecke_mul_of_coprime m n hm hn hmn, LinearMap.comp_apply,
          heig j n hn, map_smul, heig j m hm, smul_smul, mul_comm]
    exact smul_left_injective ℂ (hf_ne j) (hL.symm.trans hR)
  · intro j p hp hcop r hr
    have hcop_pow : ∀ s : ℕ, Nat.Coprime (p ^ s) N := fun s => hcop.pow_left s
    have hL := heig j (p ^ (r + 1)) (hcop_pow (r + 1))
    have hR : S.hecke (p ^ (r + 1)) (f j) =
        (lam j p * lam j (p ^ r) -
          χ (p : ZMod N) * (p : ℂ) ^ (k - 1) * lam j (p ^ (r - 1))) • f j := by
      rw [S.hecke_prime_pow p hp hcop r hr, LinearMap.sub_apply, LinearMap.comp_apply,
          LinearMap.smul_apply, heig j (p ^ r) (hcop_pow r), map_smul, heig j p hcop,
          heig j (p ^ (r - 1)) (hcop_pow (r - 1)), smul_smul, smul_smul, ← sub_smul,
          mul_comm (lam j (p ^ r)) (lam j p)]
    exact smul_left_injective ℂ (hf_ne j) (hL.symm.trans hR)

/-- **Trivial Nebentypus Corollary**:
When `χ = 1`, `H` has an orthonormal Hecke eigenbasis whose eigenvalues `λ_n(f_j)` are ALL
**purely real** (`(lam j n).im = 0`) for every `Nat.Coprime n N`! -/
theorem exists_orthonormalBasis_heckeEigenforms_real_of_trivialChar [NeZero N]
    (S : PeterssonHeckeSpace N k (1 : DirichletCharacter ℂ N) H) :
    ∃ (f : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H)
      (lam : Fin (Module.finrank ℂ H) → ℕ → ℂ),
      (∀ j n, Nat.Coprime n N → S.hecke n (f j) = lam j n • f j) ∧
      (∀ j n, Nat.Coprime n N → (lam j n).im = 0) := by
  obtain ⟨f, lam, heig, hstar, _, _, _⟩ := exists_orthonormalBasis_heckeEigenforms S
  refine ⟨f, lam, heig, fun j n hcop => ?_⟩
  have hu : IsUnit (n : ZMod N) := (ZMod.isUnit_iff_coprime n N).mpr hcop
  have h1 : (1 : DirichletCharacter ℂ N) (n : ZMod N) = 1 := MulChar.one_apply hu
  have hst := hstar j n hcop
  rw [h1, star_one, one_mul] at hst
  exact Complex.conj_eq_iff_im.mp hst

/-- **Non-Vacuous Concrete Realization of `PeterssonHeckeSpace`**:
Given any `d` normalized Hecke eigenforms `a : Fin d → ℕ → ℂ` of weight `k`, level `N`, Nebentypus
`χ` satisfying the Petersson eigenvalue conjugation `star (a j n) = star (χ n) * a j n` for
`Nat.Coprime n N`, the diagonal Hecke action on `EuclideanSpace ℂ (Fin d)` forms a genuine
`PeterssonHeckeSpace N k χ (EuclideanSpace ℂ (Fin d))`. -/
def diagonalPeterssonHeckeSpace {d : ℕ} (a : Fin d → ℕ → ℂ)
    (heig : ∀ j : Fin d, IsNormalizedHeckeEigenform k χ (a j) (a j))
    (hsa : ∀ j : Fin d, ∀ n : ℕ, Nat.Coprime n N → star (a j n) = star (χ (n : ZMod N)) * a j n) :
    PeterssonHeckeSpace N k χ (EuclideanSpace ℂ (Fin d)) where
  hecke n :=
    { toFun := fun v => WithLp.toLp 2 (fun j => a j n * v j)
      map_add' := fun u v => by ext j; simp [mul_add]
      map_smul' := fun c v => by ext j; simp; ring }
  hecke_one := by
    apply LinearMap.ext; intro v; ext j
    simp [(heig j).1]
  hecke_comm m n _ _ := by
    apply LinearMap.ext; intro v; ext j
    simp [mul_left_comm]
  hecke_mul_of_coprime m n _ _ hmn := by
    apply LinearMap.ext; intro v; ext j
    change a j m * (a j n * v j) = a j (m * n) * v j
    by_cases hm : m = 0
    · subst hm
      have hn1 : n = 1 := (Nat.coprime_zero_left n).mp hmn
      subst hn1; simp [(heig j).1]
    by_cases hn : n = 0
    · subst hn
      have hm1 : m = 1 := (Nat.coprime_zero_right m).mp hmn
      subst hm1; simp [(heig j).1]
    rw [eigenform_isMultiplicative (heig j) (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn) hmn,
        mul_assoc]
  hecke_prime_pow p hp _ r hr := by
    apply LinearMap.ext; intro v; ext j
    change a j (p ^ (r + 1)) * v j =
      a j p * (a j (p ^ r) * v j) -
        χ (p : ZMod N) * (p : ℂ) ^ (k - 1) * (a j (p ^ (r - 1)) * v j)
    have hrec := eigenform_prime_pow_recurrence (heig j) hp (r - 1)
    have hr1 : r - 1 + 1 = r := by omega
    have hr2 : r - 1 + 2 = r + 1 := by omega
    rw [hr1, hr2] at hrec
    rw [hrec]
    ring
  hecke_adjoint n hcop := by
    apply LinearMap.ext; intro v
    refine ext_inner_left ℂ fun u => ?_
    rw [LinearMap.adjoint_inner_right, PiLp.inner_apply, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [RCLike.inner_apply, Complex.star_def, LinearMap.smul_apply,
      LinearMap.coe_mk, AddHom.coe_mk, PiLp.smul_apply, smul_eq_mul, map_mul]
    have hsj : starRingEnd ℂ (a j n) = starRingEnd ℂ (χ (n : ZMod N)) * a j n := hsa j n hcop
    rw [hsj]
    ring

/-- Concrete non-vacuous `d`-dimensional `PeterssonHeckeSpace 1 k 1` realized from
`Stage5ModularHecke.eisensteinCoeff k 1`. -/
def eisensteinPeterssonSpace (k d : ℕ) :
    PeterssonHeckeSpace 1 k (1 : DirichletCharacter ℂ 1) (EuclideanSpace ℂ (Fin d)) :=
  diagonalPeterssonHeckeSpace (fun _ => eisensteinCoeff k (1 : DirichletCharacter ℂ 1))
    (fun _ => isNormalizedHeckeEigenform_eisensteinCoeff k (1 : DirichletCharacter ℂ 1))
    (fun _ n _ => by
      have hχ1 : (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 :=
        MulChar.one_apply ((ZMod.isUnit_iff_coprime n 1).mpr (Nat.coprime_one_right n))
      rw [hχ1, star_one, one_mul]
      simp only [eisensteinCoeff, heckeWeight, star_sum, star_mul, star_pow]
      refine Finset.sum_congr rfl fun m _ => ?_
      have hm1 : (1 : DirichletCharacter ℂ 1) (m : ZMod 1) = 1 :=
        MulChar.one_apply ((ZMod.isUnit_iff_coprime m 1).mpr (Nat.coprime_one_right m))
      simp [hm1, mul_comm])

/-- **Bochner Spectral Gap for Self-Adjoint Hecke Operators**:
Bridging `Stage4SelbergTrace.automorphic_bochner_spectral_gap` /
`Stage3ExplicitSpectral.bochner_spectral_gap_symmetric`, for any `PeterssonHeckeSpace N k χ H`,
any `n` with `Nat.Coprime n N` and `χ(n) = 1`, and any linear operator `D : H →ₗ[ℂ] K` with
curvature bound `κ * ‖v‖² ≤ Re ⟨T_n v, v⟩`, every eigenvalue `μ` of `D* ∘ D + T_n` is purely real
and satisfies `κ ≤ μ.re`. -/
theorem hecke_bochner_spectral_gap
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]
    (S : PeterssonHeckeSpace N k χ H) {n : ℕ} (hcop : Nat.Coprime n N)
    (hχ : χ (n : ZMod N) = 1) (D : H →ₗ[ℂ] K) {κ : ℝ}
    (hcurv : ∀ v : H, κ * ‖v‖ ^ 2 ≤ (inner ℂ (S.hecke n v) v).re)
    {v : H} (hv : v ≠ 0) {μ : ℂ}
    (heig : (LinearMap.adjoint D ∘ₗ D + S.hecke n) v = μ • v) :
    μ.im = 0 ∧ κ ≤ μ.re :=
  Stage3ExplicitSpectral.bochner_spectral_gap_symmetric D (LinearMap.adjoint D) (S.hecke n)
    (fun x y => LinearMap.adjoint_inner_left D y x)
    (S.hecke_isSymmetric_of_char_one hcop hχ) hcurv hv heig

end PeterssonHeckeSpaces

/-! ## Section 3: Strong Multiplicity One (Atkin–Lehner) & 1-Dimensional Eigenspaces -/

section MultiplicityOne

variable {N k : ℕ} {χ : DirichletCharacter ℂ N}

/-- Every cuspidal (`f 0 = 0`) Hecke eigenform with `f 1 = 0` vanishes identically. -/
theorem cusp_eigenform_eq_zero_of_coeff_one_eq_zero {f lam : ℕ → ℂ}
    (hf0 : f 0 = 0) (heig : IsHeckeEigenform k χ f lam) (hf1 : f 1 = 0) :
    f = 0 := by
  funext n
  match n with
  | 0 => exact hf0
  | n + 1 =>
    have h := congrFun (heig (n + 1) (Nat.succ_pos n)) 1
    rw [heckeOp_apply_one k χ (Nat.succ_pos n), Pi.smul_apply, smul_eq_mul, hf1, mul_zero] at h
    exact h

/-- Every non-zero cuspidal (`f 0 = 0`) Hecke eigenform has `f 1 ≠ 0`. -/
theorem cusp_eigenform_coeff_one_ne_zero {f lam : ℕ → ℂ}
    (hf0 : f 0 = 0) (heig : IsHeckeEigenform k χ f lam) (hf : f ≠ 0) :
    f 1 ≠ 0 :=
  fun h1 => hf (cusp_eigenform_eq_zero_of_coeff_one_eq_zero hf0 heig h1)

/-- Scaling any cuspidal Hecke eigenform `f` with `f 1 ≠ 0` by `(f 1)⁻¹` produces a normalized
cuspidal Hecke eigenform `f_norm` with `f = f 1 • f_norm`. -/
theorem cusp_eigenform_normalize {f lam : ℕ → ℂ}
    (hf0 : f 0 = 0) (heig : IsHeckeEigenform k χ f lam) (hf1 : f 1 ≠ 0) :
    let f_norm : ℕ → ℂ := (f 1)⁻¹ • f
    f_norm 0 = 0 ∧ IsNormalizedHeckeEigenform k χ f_norm lam ∧ f = f 1 • f_norm := by
  intro f_norm
  refine ⟨by simp [f_norm, hf0], ⟨by simp [f_norm, inv_mul_cancel₀ hf1], fun n hn => ?_⟩, ?_⟩
  · simp only [f_norm, heckeOp_smul, heig n hn, smul_comm (f 1)⁻¹ (lam n)]
  · ext n
    simp only [f_norm, Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hf1, one_mul]

/-- **Prime Hecke Eigenvalues Determine Full Hecke Eigenform Action**:
if `T_p f = α p • f` for every prime `p`, then `f` is a simultaneous Hecke eigenform for ALL
`T_n` (`n ≥ 1`) with an explicit eigenvalue sequence `lam` agreeing with `α` on primes. -/
theorem isHeckeEigenform_of_prime_eigenvalues {f α : ℕ → ℂ}
    (hprime : ∀ p : ℕ, p.Prime → heckeOp k χ p f = α p • f) :
    ∃ lam : ℕ → ℂ, IsHeckeEigenform k χ f lam ∧ (∀ p : ℕ, p.Prime → lam p = α p) := by
  have hpp : ∀ p : ℕ, p.Prime → ∀ r : ℕ, ∃ c : ℂ, heckeOp k χ (p ^ r) f = c • f := by
    intro p hp r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      match r with
      | 0 => exact ⟨1, by simp [heckeOp_one]⟩
      | 1 => exact ⟨α p, by simpa using hprime p hp⟩
      | r + 2 =>
        obtain ⟨c₁, hc₁⟩ := ih (r + 1) (by omega)
        obtain ⟨c₀, hc₀⟩ := ih r (by omega)
        refine ⟨α p * c₁ - χ (p : ZMod N) * (p : ℂ) ^ (k - 1) * c₀, ?_⟩
        rw [heckeOp_prime_pow_recurrence k χ hp (r := r + 1) (by omega), Nat.add_sub_cancel,
            hc₁, heckeOp_smul, hprime p hp, hc₀, smul_smul, smul_smul, ← sub_smul,
            mul_comm c₁ (α p)]
  have hall : ∀ n : ℕ, 1 ≤ n → ∃ c : ℂ, heckeOp k χ n f = c • f := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hn1 : n = 1
      · subst hn1; exact ⟨1, by simp [heckeOp_one]⟩
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
      obtain ⟨c₁, hc₁⟩ := hpp p hp a
      obtain ⟨c₂, hc₂⟩ := ih n' hn'_lt hn'_pos
      refine ⟨c₁ * c₂, ?_⟩
      rw [hn_eq, ← heckeOp_mul_of_coprime k χ hcop, hc₂, heckeOp_smul, hc₁, smul_smul, mul_comm]
  by_cases hf0 : f = 0
  · subst hf0
    refine ⟨fun n => if n.Prime then α n else 0, fun n _ => ?_, fun p hp => if_pos hp⟩
    simp [heckeOp_zero_fun]
  · classical
    let lam : ℕ → ℂ := fun n => if h : 1 ≤ n then Classical.choose (hall n h) else 0
    have hlam : IsHeckeEigenform k χ f lam := fun n hn => by
      simp only [lam, dif_pos hn]
      exact Classical.choose_spec (hall n hn)
    refine ⟨lam, hlam, fun p hp => ?_⟩
    have h1 := hlam p hp.one_le
    have h2 := hprime p hp
    exact smul_left_injective ℂ hf0 (h1.symm.trans h2)

/-- **Coprime-to-`N` Eigenform Determination**:
two normalized Hecke eigenforms of weight `k` and Nebentypus `χ` whose eigenvalues agree at all
primes `p ∤ N` have identical Fourier coefficients `f n = g n` for ALL `n ≥ 1` with `Nat.Coprime n N`. -/
theorem normalized_eigenform_eq_on_coprime_of_prime_eigenvalues
    {f g lam₁ lam₂ : ℕ → ℂ}
    (hf : IsNormalizedHeckeEigenform k χ f lam₁)
    (hg : IsNormalizedHeckeEigenform k χ g lam₂)
    (hprime : ∀ p : ℕ, p.Prime → Nat.Coprime p N → lam₁ p = lam₂ p) :
    ∀ n : ℕ, 1 ≤ n → Nat.Coprime n N → f n = g n := by
  have hpp : ∀ p : ℕ, p.Prime → Nat.Coprime p N → ∀ r : ℕ, f (p ^ r) = g (p ^ r) := by
    intro p hp hcop r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      match r with
      | 0 => simp [hf.1, hg.1]
      | 1 =>
        rw [pow_one, ← eigenvalue_eq_coeff hf hp.one_le, ← eigenvalue_eq_coeff hg hp.one_le]
        exact hprime p hp hcop
      | r + 2 =>
        rw [eigenform_prime_pow_recurrence hf hp r, eigenform_prime_pow_recurrence hg hp r,
            ← eigenvalue_eq_coeff hf hp.one_le, ← eigenvalue_eq_coeff hg hp.one_le,
            hprime p hp hcop, ih (r + 1) (by omega), ih r (by omega)]
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn hcop
    by_cases hn1 : n = 1
    · subst hn1; rw [hf.1, hg.1]
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn1
    have hn0 : n ≠ 0 := by omega
    have hp_cop : Nat.Coprime p N := hcop.coprime_dvd_left hpn
    set a := n.factorization p
    have ha_pos : 1 ≤ a := (hp.dvd_iff_one_le_factorization hn0).mp hpn
    have hpa_dvd : p ^ a ∣ n := Nat.ordProj_dvd n p
    set n' := n / p ^ a
    have hn_eq : n = p ^ a * n' := (Nat.mul_div_cancel' hpa_dvd).symm
    have hn'_pos : 1 ≤ n' := Nat.div_pos (Nat.le_of_dvd (by omega) hpa_dvd) (pow_pos hp.pos a)
    have hn'_cop : Nat.Coprime n' N := hcop.coprime_dvd_left (Nat.div_dvd_of_dvd hpa_dvd)
    have hcop_split : Nat.Coprime (p ^ a) n' :=
      (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_ordCompl hp hn0)).pow_left a
    have hn'_lt : n' < n := by
      have hpa_gt : 1 < p ^ a := one_lt_pow₀ hp.one_lt (by omega)
      calc n' = 1 * n' := (one_mul n').symm
        _ < p ^ a * n' := Nat.mul_lt_mul_of_pos_right hpa_gt (by omega)
        _ = n := hn_eq.symm
    rw [hn_eq,
        eigenform_isMultiplicative hf (one_le_pow₀ hp.one_le) hn'_pos hcop_split,
        eigenform_isMultiplicative hg (one_le_pow₀ hp.one_le) hn'_pos hcop_split,
        hpp p hp hp_cop a, ih n' hn'_lt hn'_pos hn'_cop]

/-- **NORMALIZED EIGENFORM MULTIPLICITY ONE (ATKIN–LEHNER)**:
On the space of cuspidal `q`-expansions (`f 0 = 0`), two normalized Hecke eigenforms (`a_1 = 1`)
with identical eigenvalues at all primes `p` are **IDENTICAL** (`f = g`). -/
theorem normalized_eigenform_eq_of_prime_eigenvalues
    {f g lam₁ lam₂ : ℕ → ℂ}
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hf : IsNormalizedHeckeEigenform k χ f lam₁)
    (hg : IsNormalizedHeckeEigenform k χ g lam₂)
    (hprime : ∀ p : ℕ, p.Prime → lam₁ p = lam₂ p) :
    f = g := by
  have hpp : ∀ p : ℕ, p.Prime → ∀ r : ℕ, f (p ^ r) = g (p ^ r) := by
    intro p hp r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      match r with
      | 0 => simp [hf.1, hg.1]
      | 1 =>
        rw [pow_one, ← eigenvalue_eq_coeff hf hp.one_le, ← eigenvalue_eq_coeff hg hp.one_le]
        exact hprime p hp
      | r + 2 =>
        rw [eigenform_prime_pow_recurrence hf hp r, eigenform_prime_pow_recurrence hg hp r,
            ← eigenvalue_eq_coeff hf hp.one_le, ← eigenvalue_eq_coeff hg hp.one_le,
            hprime p hp, ih (r + 1) (by omega), ih r (by omega)]
  have hpos : ∀ n : ℕ, 1 ≤ n → f n = g n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hn1 : n = 1
      · subst hn1; rw [hf.1, hg.1]
      obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn1
      have hn0 : n ≠ 0 := by omega
      set a := n.factorization p
      have ha_pos : 1 ≤ a := (hp.dvd_iff_one_le_factorization hn0).mp hpn
      have hpa_dvd : p ^ a ∣ n := Nat.ordProj_dvd n p
      set n' := n / p ^ a
      have hn_eq : n = p ^ a * n' := (Nat.mul_div_cancel' hpa_dvd).symm
      have hn'_pos : 1 ≤ n' := Nat.div_pos (Nat.le_of_dvd (by omega) hpa_dvd) (pow_pos hp.pos a)
      have hcop_split : Nat.Coprime (p ^ a) n' :=
        (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_ordCompl hp hn0)).pow_left a
      have hn'_lt : n' < n := by
        have hpa_gt : 1 < p ^ a := one_lt_pow₀ hp.one_lt (by omega)
        calc n' = 1 * n' := (one_mul n').symm
          _ < p ^ a * n' := Nat.mul_lt_mul_of_pos_right hpa_gt (by omega)
          _ = n := hn_eq.symm
      rw [hn_eq,
          eigenform_isMultiplicative hf (one_le_pow₀ hp.one_le) hn'_pos hcop_split,
          eigenform_isMultiplicative hg (one_le_pow₀ hp.one_le) hn'_pos hcop_split,
          hpp p hp a, ih n' hn'_lt hn'_pos]
  funext n
  match n with
  | 0 => rw [hf0, hg0]
  | n + 1 => exact hpos (n + 1) (Nat.succ_pos n)

/-- **MULTIPLICITY ONE (1-DIMENSIONAL EIGENSPACE FORM)**:
Any cuspidal Hecke eigenform `f` sharing all prime eigenvalues with a non-zero cuspidal eigenform
`g` (`g 1 ≠ 0`) is a scalar multiple of `g`: `f = (f 1 / g 1) • g`.
In particular, for any normalized eigenform `f_norm` with the same prime eigenvalues,
`f = f 1 • f_norm`. -/
theorem eigenform_eq_smul_of_prime_eigenvalues
    {f g lam₁ lam₂ : ℕ → ℂ}
    (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hf : IsHeckeEigenform k χ f lam₁) (hg : IsHeckeEigenform k χ g lam₂)
    (hg1 : g 1 ≠ 0) (hprime : ∀ p : ℕ, p.Prime → lam₁ p = lam₂ p) :
    f = (f 1 / g 1) • g := by
  by_cases hf1 : f 1 = 0
  · rw [hf1, zero_div, zero_smul]
    exact cusp_eigenform_eq_zero_of_coeff_one_eq_zero hf0 hf hf1
  · obtain ⟨hf_n0, hf_norm, hf_eq⟩ := cusp_eigenform_normalize hf0 hf hf1
    obtain ⟨hg_n0, hg_norm, _⟩ := cusp_eigenform_normalize hg0 hg hg1
    have hnorm_eq : (f 1)⁻¹ • f = (g 1)⁻¹ • g :=
      normalized_eigenform_eq_of_prime_eigenvalues hf_n0 hg_n0 hf_norm hg_norm hprime
    calc f = f 1 • ((f 1)⁻¹ • f) := hf_eq
      _ = f 1 • ((g 1)⁻¹ • g) := by rw [hnorm_eq]
      _ = (f 1 / g 1) • g := by rw [smul_smul, div_eq_mul_inv]

/-- Joint prime-Hecke eigenspace `{ v ∈ V | ∀ p prime, T p v = α p • v }` on any vector space `V`
equipped with linear operators `T : ℕ → (V →ₗ[ℂ] V)`. -/
def primeHeckeEigenspace {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : ℕ → (V →ₗ[ℂ] V)) (α : ℕ → ℂ) : Submodule ℂ V where
  carrier := { v | ∀ p : ℕ, p.Prime → T p v = α p • v }
  add_mem' hu hv p hp := by simp [map_add, hu p hp, hv p hp, smul_add]
  zero_mem' p _ := by simp
  smul_mem' c v hv p hp := by simp [map_smul, hv p hp, smul_comm c (α p)]

/-- **ATKIN–LEHNER MULTIPLICITY ONE (`Module.finrank ℂ E ≤ 1`)**:
On any finite-dimensional `ℂ`-vector space `V` with an injective cuspidal `q`-expansion map
`qExp : V →ₗ[ℂ] (ℕ → ℂ)` (`∀ v, qExp v 0 = 0`) intertwining the prime Hecke operators `T p` with
`heckeOp k χ p`, every joint prime-Hecke eigenspace has dimension **at most `1`**! -/
theorem finrank_cuspHeckeEigenspace_le_one
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : ℕ → (V →ₗ[ℂ] V)) (qExp : V →ₗ[ℂ] (ℕ → ℂ))
    (hq_inj : Function.Injective qExp)
    (hq_cusp : ∀ v : V, qExp v 0 = 0)
    (hq_hecke : ∀ p : ℕ, p.Prime → ∀ v : V, qExp (T p v) = heckeOp k χ p (qExp v))
    (α : ℕ → ℂ) :
    Module.finrank ℂ (primeHeckeEigenspace T α) ≤ 1 := by
  let E := primeHeckeEigenspace T α
  by_cases hbot : E = ⊥
  · rw [show Module.finrank ℂ E = 0 by rw [hbot]; exact finrank_bot ℂ V]
    exact Nat.zero_le 1
  · obtain ⟨v₀, hv₀_mem, hv₀_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hv₀_prime : ∀ p : ℕ, p.Prime → heckeOp k χ p (qExp v₀) = α p • qExp v₀ := fun p hp => by
      rw [← hq_hecke p hp v₀, hv₀_mem p hp, map_smul]
    obtain ⟨lam₀, hlam₀, hlam₀_p⟩ := isHeckeEigenform_of_prime_eigenvalues (k := k) (χ := χ) hv₀_prime
    have hqv₀_ne : qExp v₀ ≠ 0 := fun h0 => hv₀_ne (hq_inj (h0.trans (map_zero qExp).symm))
    have hqv₀_1 : qExp v₀ 1 ≠ 0 :=
      cusp_eigenform_coeff_one_ne_zero (hq_cusp v₀) hlam₀ hqv₀_ne
    have hspan : (⊤ : Submodule ℂ E) ≤ Submodule.span ℂ ({(⟨v₀, hv₀_mem⟩ : E)} : Set E) := by
      intro u _
      have hu_prime : ∀ p : ℕ, p.Prime → heckeOp k χ p (qExp u.1) = α p • qExp u.1 := fun p hp => by
        rw [← hq_hecke p hp u.1, u.2 p hp, map_smul]
      obtain ⟨lam_u, hlam_u, hlam_u_p⟩ :=
        isHeckeEigenform_of_prime_eigenvalues (k := k) (χ := χ) hu_prime
      have hq_eq : qExp u.1 = (qExp u.1 1 / qExp v₀ 1) • qExp v₀ :=
        eigenform_eq_smul_of_prime_eigenvalues (hq_cusp u.1) (hq_cusp v₀) hlam_u hlam₀ hqv₀_1
          (fun p hp => (hlam_u_p p hp).trans (hlam₀_p p hp).symm)
      have hu_eq : u = (qExp u.1 1 / qExp v₀ 1) • (⟨v₀, hv₀_mem⟩ : E) := by
        apply Subtype.ext
        apply hq_inj
        rw [Submodule.coe_smul_of_tower, map_smul]
        exact hq_eq
      rw [hu_eq]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
    have hfin := Submodule.finrank_mono hspan
    rw [finrank_top] at hfin
    have hv0E_ne : (⟨v₀, hv₀_mem⟩ : E) ≠ 0 := fun h => hv₀_ne (congrArg Subtype.val h)
    exact hfin.trans (le_of_eq (finrank_span_singleton hv0E_ne))

end MultiplicityOne

/-! ## Section 4: Exact Hecke Trace Identities, Spectral Resolution & Eichler–Selberg / `LSeries` / `satakeWDRep` Bridge -/

section HeckeTraceAndSpectralBridge

variable {N k : ℕ} {χ : DirichletCharacter ℂ N}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/-- **Exact Hecke Trace Identity**:
for any orthonormal basis `f` of simultaneous Hecke eigenvectors with eigenvalues `lam`,
`Tr(T_n) = ∑_{j=1}^d λ_n(f_j)`. -/
theorem hecke_trace_eq_sum_eigenvalues (S : PeterssonHeckeSpace N k χ H)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : OrthonormalBasis ι ℂ H) (lam : ι → ℕ → ℂ)
    {n : ℕ} (heig : ∀ j : ι, S.hecke n (f j) = lam j n • f j) :
    LinearMap.trace ℂ H (S.hecke n) = ∑ j : ι, lam j n := by
  rw [trace_eq_sum_inner_orthonormalBasis f (S.hecke n)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [heig j, inner_smul_right, inner_self_eq_norm_sq_to_K, f.orthonormal.1 j]
  simp

/-- **Exact Bilinear / Product Hecke Trace Identity**:
`Tr(T_m ∘ T_n) = ∑_{j=1}^d λ_m(f_j) · λ_n(f_j)`. -/
theorem hecke_trace_comp_eq_sum_mul_eigenvalues (S : PeterssonHeckeSpace N k χ H)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : OrthonormalBasis ι ℂ H) (lam : ι → ℕ → ℂ)
    {m n : ℕ}
    (hm : ∀ j : ι, S.hecke m (f j) = lam j m • f j)
    (hn : ∀ j : ι, S.hecke n (f j) = lam j n • f j) :
    LinearMap.trace ℂ H (S.hecke m ∘ₗ S.hecke n) = ∑ j : ι, lam j m * lam j n := by
  rw [trace_eq_sum_inner_orthonormalBasis f (S.hecke m ∘ₗ S.hecke n)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.comp_apply, hn j, map_smul, hm j, smul_smul, inner_smul_right,
      inner_self_eq_norm_sq_to_K, f.orthonormal.1 j]
  simp [mul_comm]

/-- **Exact Power Hecke Trace Identity**:
`Tr((T_n)^r) = ∑_{j=1}^d λ_n(f_j)^r`. -/
theorem hecke_trace_pow_eq_sum_pow_eigenvalues (S : PeterssonHeckeSpace N k χ H)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : OrthonormalBasis ι ℂ H) (lam : ι → ℕ → ℂ)
    {n : ℕ} (heig : ∀ j : ι, S.hecke n (f j) = lam j n • f j) (r : ℕ) :
    LinearMap.trace ℂ H ((S.hecke n) ^ r) = ∑ j : ι, (lam j n) ^ r := by
  have hpow : ∀ j : ι, ∀ s : ℕ, ((S.hecke n) ^ s) (f j) = (lam j n) ^ s • f j := by
    intro j s
    induction s with
    | zero => simp
    | succ s ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_smul, heig j, smul_smul, mul_comm, ← pow_succ']
  rw [trace_eq_sum_inner_orthonormalBasis f ((S.hecke n) ^ r)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hpow j r, inner_smul_right, inner_self_eq_norm_sq_to_K, f.orthonormal.1 j]
  simp

/-- **Exact Hilbert–Schmidt Norm-Square Trace Identity**:
`Tr(T_n* ∘ T_n) = ∑_{j=1}^d ‖λ_n(f_j)‖²`. -/
theorem hecke_trace_adjoint_comp_eq_sum_norm_sq (S : PeterssonHeckeSpace N k χ H)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : OrthonormalBasis ι ℂ H) (lam : ι → ℕ → ℂ)
    {n : ℕ} (hcop : Nat.Coprime n N)
    (heig : ∀ j : ι, S.hecke n (f j) = lam j n • f j) :
    LinearMap.trace ℂ H (LinearMap.adjoint (S.hecke n) ∘ₗ S.hecke n) =
      ∑ j : ι, ((‖lam j n‖ ^ 2 : ℝ) : ℂ) := by
  rw [trace_eq_sum_inner_orthonormalBasis f (LinearMap.adjoint (S.hecke n) ∘ₗ S.hecke n)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hadj : LinearMap.adjoint (S.hecke n) (f j) = star (lam j n) • f j :=
    (S.hecke_isNormal hcop).adjoint_apply_of_eigenvector (heig j)
  rw [LinearMap.comp_apply, heig j, map_smul, hadj, smul_smul, inner_smul_right,
      inner_self_eq_norm_sq_to_K, f.orthonormal.1 j]
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **Spectral Resolution of `T_n` along the Orthonormal Hecke Eigenbasis**:
`T_n v = ∑_j (λ_n(f_j) · ⟨f_j, v⟩) • f_j`. -/
theorem hecke_spectral_expansion (S : PeterssonHeckeSpace N k χ H)
    {ι : Type*} [Fintype ι]
    (f : OrthonormalBasis ι ℂ H) (lam : ι → ℕ → ℂ)
    {n : ℕ} (heig : ∀ j : ι, S.hecke n (f j) = lam j n • f j) (v : H) :
    S.hecke n v = ∑ j : ι, (lam j n * inner ℂ (f j) v) • f j := by
  conv_lhs => rw [← f.sum_repr' v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, heig j, smul_smul, mul_comm]

/-- **Sesquilinear Spectral Expansion of `T_n`**:
`⟨u, T_n v⟩ = ∑_j λ_n(f_j) · conj(⟨f_j, u⟩) · ⟨f_j, v⟩`. -/
theorem hecke_inner_spectral_expansion (S : PeterssonHeckeSpace N k χ H)
    {ι : Type*} [Fintype ι]
    (f : OrthonormalBasis ι ℂ H) (lam : ι → ℕ → ℂ)
    {n : ℕ} (heig : ∀ j : ι, S.hecke n (f j) = lam j n • f j) (u v : H) :
    inner ℂ u (S.hecke n v) =
      ∑ j : ι, lam j n * star (inner ℂ (f j) u) * inner ℂ (f j) v := by
  rw [hecke_spectral_expansion S f lam heig v, inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_right, ← inner_conj_symm (f j) u, starRingEnd_apply, star_star]
  ring

/-- **Eichler–Selberg Satake Power-Sum Trace Formula**:
for any prime `p ∤ N`, any `r : ℕ`, and Satake pairs `(α j, β j)` attached to
`(λ_p(f_j), χ(p) p^(k-1))`, the trace of `T_{p^r}` equals the sum of complete homogeneous
symmetric polynomials of degree `r` in the Satake parameters:
`Tr(T_{p^r}) = ∑_j ∑_{i=0}^r α_j^i β_j^{r - i}`. -/
theorem hecke_prime_pow_trace_eq_sum_satake (S : PeterssonHeckeSpace N k χ H)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : OrthonormalBasis ι ℂ H) (lam : ι → ℕ → ℂ)
    (heig : ∀ j : ι, ∀ n : ℕ, Nat.Coprime n N → S.hecke n (f j) = lam j n • f j)
    (h1 : ∀ j : ι, lam j 1 = 1)
    (hrec : ∀ j : ι, ∀ p : ℕ, p.Prime → Nat.Coprime p N → ∀ r : ℕ, 1 ≤ r →
      lam j (p ^ (r + 1)) =
        lam j p * lam j (p ^ r) -
          χ (p : ZMod N) * (p : ℂ) ^ (k - 1) * lam j (p ^ (r - 1)))
    {p : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p N)
    (α β : ι → ℂ)
    (hsat : ∀ j : ι,
      IsSatakePair (lam j p) (χ (p : ZMod N) * (p : ℂ) ^ (k - 1)) (α j) (β j))
    (r : ℕ) :
    LinearMap.trace ℂ H (S.hecke (p ^ r)) =
      ∑ j : ι, ∑ i ∈ Finset.range (r + 1), (α j) ^ i * (β j) ^ (r - i) := by
  rw [hecke_trace_eq_sum_eigenvalues S f lam (fun j => heig j (p ^ r) (hcop.pow_left r))]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact primePow_eq_satake_sum (hsat j) (g := fun s => lam j (p ^ s))
    (by rw [pow_zero, h1 j]) (by rw [pow_one])
    (fun s => by simpa using hrec j p hp hcop (s + 1) (Nat.succ_pos s)) r

/-- **Eichler–Selberg ↔ Local Langlands `satakeWDRep` Frobenius Trace Identity**:
For every prime `p ∤ N` (`NeZero N`) and every local Weil group `W : WDGroup` with Frobenius `φ`
(`W.deg φ = 1`), the trace of the Hecke operator `T_p` on `H` equals the sum over the Hecke
eigenbasis of the Frobenius traces of the unramified 2-dimensional Satake Weil–Deligne
representations `Stage5ModularHecke.satakeWDRep`! -/
theorem hecke_prime_trace_eq_sum_satakeWDRep_trace [NeZero N]
    (S : PeterssonHeckeSpace N k χ H)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : OrthonormalBasis ι ℂ H) (lam : ι → ℕ → ℂ)
    {p : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p N)
    (heig : ∀ j : ι, S.hecke p (f j) = lam j p • f j)
    (W : RHDirect.LocalLanglands.WDGroup) {φ : W.G} (hφ : W.deg φ = 1) :
    ∃ (α β : ι → ℂ) (hα : ∀ j, α j ≠ 0) (hβ : ∀ j, β j ≠ 0),
      (∀ j, IsSatakePair (lam j p) (χ (p : ZMod N) * (p : ℂ) ^ (k - 1)) (α j) (β j)) ∧
      LinearMap.trace ℂ H (S.hecke p) =
        ∑ j : ι, Matrix.trace
          ((satakeWDRep W (α j) (β j) (hα j) (hβ j)).ρ φ : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hc_ne : χ (p : ZMod N) * (p : ℂ) ^ (k - 1) ≠ 0 := by
    have hχ_ne : χ (p : ZMod N) ≠ 0 := by
      intro h0
      have h1 := norm_dirichletChar_eq_one_of_coprime χ hcop
      rw [h0, norm_zero] at h1
      exact zero_ne_one h1
    exact mul_ne_zero hχ_ne (pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero))
  have hex : ∀ j : ι, ∃ ab : ℂ × ℂ,
      IsSatakePair (lam j p) (χ (p : ZMod N) * (p : ℂ) ^ (k - 1)) ab.1 ab.2 := fun j => by
    obtain ⟨a, b, hab⟩ := exists_satake_pair (lam j p) (χ (p : ZMod N) * (p : ℂ) ^ (k - 1))
    exact ⟨(a, b), hab⟩
  let α : ι → ℂ := fun j => (Classical.choose (hex j)).1
  let β : ι → ℂ := fun j => (Classical.choose (hex j)).2
  have hsat : ∀ j : ι,
      IsSatakePair (lam j p) (χ (p : ZMod N) * (p : ℂ) ^ (k - 1)) (α j) (β j) :=
    fun j => Classical.choose_spec (hex j)
  have hα : ∀ j : ι, α j ≠ 0 := fun j => left_ne_zero_of_mul ((hsat j).2.symm ▸ hc_ne)
  have hβ : ∀ j : ι, β j ≠ 0 := fun j => right_ne_zero_of_mul ((hsat j).2.symm ▸ hc_ne)
  refine ⟨α, β, hα, hβ, hsat, ?_⟩
  rw [hecke_trace_eq_sum_eigenvalues S f lam heig]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact (satakeWDRep_trace_frob W (hα j) (hβ j) (hsat j) hφ).symm

/-- **Petersson Self-Adjointness + Ramanujan–Petersson Trace & Temperedness Bound**:
for any `PeterssonHeckeSpace N k χ H` (`NeZero N`) and unramified prime `p ∤ N`, if each
eigenform in the orthonormal Hecke eigenbasis satisfies `‖λ_p(f_j)‖ ≤ 2 p^{(k-1)/2}`, then:
1. Every Satake pair is pure of weight `k - 1`: `‖α_j‖ = ‖β_j‖ = p^{(k-1)/2}` (automatically
   discharging the self-adjointness hypothesis of `Stage5ModularHecke.ramanujan_petersson_iff_of_selfAdjoint`
   via the Petersson adjoint law!),
2. Every twisted Satake Weil–Deligne representation is tempered/unitary, and
3. The Hecke trace obeys `‖Tr(T_p)‖ ≤ 2 · dim(H) · p^{(k-1)/2}`. -/
theorem hecke_prime_ramanujan_trace_bound [NeZero N]
    (S : PeterssonHeckeSpace N k χ H)
    {p : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p N)
    (f : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H)
    (lam : Fin (Module.finrank ℂ H) → ℕ → ℂ)
    (heig : ∀ j, S.hecke p (f j) = lam j p • f j)
    (hrp : ∀ j, ‖lam j p‖ ≤ 2 * (p : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2))
    (α β : Fin (Module.finrank ℂ H) → ℂ)
    (hsat : ∀ j,
      IsSatakePair (lam j p) (χ (p : ZMod N) * (p : ℂ) ^ (k - 1)) (α j) (β j)) :
    (∀ j, ‖α j‖ = (p : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2) ∧
          ‖β j‖ = (p : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) ∧
    (∀ j, ‖α j * ((p : ℂ) ^ (-(((k - 1 : ℕ) : ℂ) / 2)))‖ = 1 ∧
          ‖β j * ((p : ℂ) ^ (-(((k - 1 : ℕ) : ℂ) / 2)))‖ = 1) ∧
    ‖LinearMap.trace ℂ H (S.hecke p)‖ ≤
      2 * (Module.finrank ℂ H : ℝ) * (p : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2) := by
  have hpure : ∀ j, ‖α j‖ = (p : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2) ∧
      ‖β j‖ = (p : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2) := fun j => by
    have hsa : star (lam j p) = star (χ (p : ZMod N)) * lam j p :=
      S.eigenvalue_star_eq hcop (f.orthonormal.ne_zero j) (heig j)
    exact (ramanujan_petersson_iff_of_selfAdjoint χ hp hcop (hsat j) hsa).mpr (hrp j)
  refine ⟨hpure, fun j => satakeWDRep_tempered_of_ramanujan_petersson hp (hpure j), ?_⟩
  rw [hecke_trace_eq_sum_eigenvalues S f lam heig]
  calc ‖∑ j : Fin (Module.finrank ℂ H), lam j p‖
      ≤ ∑ j : Fin (Module.finrank ℂ H), ‖lam j p‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin (Module.finrank ℂ H), (2 * (p : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) :=
        Finset.sum_le_sum fun j _ => hrp j
    _ = (Module.finrank ℂ H : ℝ) * (2 * (p : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) := by
        simp [nsmul_eq_mul]
    _ = 2 * (Module.finrank ℂ H : ℝ) * (p : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2) := by ring

/-- **Full `q`-Expansion Petersson Space (Level-1 / All-`n` Normal Hecke Algebra)**:
a `PeterssonHeckeSpace 1 k χ H` equipped with an injective cuspidal `q`-expansion map
`qExp : H →ₗ[ℂ] (ℕ → ℂ)` intertwining `S.hecke n` with `Stage5ModularHecke.heckeOp k χ n`
for every `n ≥ 1`. -/
structure PeterssonQExpansionSpace (k : ℕ) (χ : DirichletCharacter ℂ 1) (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    extends PeterssonHeckeSpace 1 k χ H where
  /-- Faithful `q`-expansion map `f ↦ (a_n(f))_{n ≥ 0}`. -/
  qExp : H →ₗ[ℂ] (ℕ → ℂ)
  qExp_injective : Function.Injective qExp
  qExp_cusp : ∀ v : H, qExp v 0 = 0
  qExp_hecke : ∀ n : ℕ, 1 ≤ n → ∀ v : H, qExp (hecke n v) = heckeOp k χ n (qExp v)

/-- Non-vacuous concrete 1-dimensional `PeterssonQExpansionSpace k 1` witness realized from
`Stage5ModularHecke.eisensteinCoeff k 1`. -/
def eisensteinPeterssonQExpansionSpace (k : ℕ) :
    PeterssonQExpansionSpace k (1 : DirichletCharacter ℂ 1) (EuclideanSpace ℂ (Fin 1)) where
  toPeterssonHeckeSpace := eisensteinPeterssonSpace k 1
  qExp :=
    { toFun := fun v n => v 0 * eisensteinCoeff k (1 : DirichletCharacter ℂ 1) n
      map_add' := fun u v => by funext n; simp [add_mul]
      map_smul' := fun c v => by funext n; simp [mul_assoc] }
  qExp_injective := by
    intro u v huv
    have h1 := congrFun huv 1
    have he1 : eisensteinCoeff k (1 : DirichletCharacter ℂ 1) 1 = 1 :=
      (isNormalizedHeckeEigenform_eisensteinCoeff k (1 : DirichletCharacter ℂ 1)).1
    simp only [LinearMap.coe_mk, AddHom.coe_mk, he1, mul_one] at h1
    ext j
    fin_cases j
    exact h1
  qExp_cusp := fun v => by simp [eisensteinCoeff]
  qExp_hecke := fun n hn v => by
    have heig := (isNormalizedHeckeEigenform_eisensteinCoeff k (1 : DirichletCharacter ℂ 1)).2 n hn
    funext m
    have hm := congrFun heig m
    have hlin : (fun r => v 0 * eisensteinCoeff k (1 : DirichletCharacter ℂ 1) r) =
        v 0 • eisensteinCoeff k (1 : DirichletCharacter ℂ 1) := rfl
    change (eisensteinCoeff k (1 : DirichletCharacter ℂ 1) n * v 0) *
        eisensteinCoeff k (1 : DirichletCharacter ℂ 1) m =
      heckeOp k (1 : DirichletCharacter ℂ 1) n
        (fun r => v 0 * eisensteinCoeff k (1 : DirichletCharacter ℂ 1) r) m
    rw [hlin, heckeOp_smul, Pi.smul_apply, smul_eq_mul, hm, Pi.smul_apply, smul_eq_mul]
    ring

/-- **Master Bridge from Petersson Diagonalization to `Stage5ModularHecke.eigenform_LSeries_eulerProduct`,
Multiplicity One, and Exact Hecke Trace**:
Every `S : PeterssonQExpansionSpace k χ H` unconditionally admits an orthonormal Hecke eigenbasis
`{f_1, ..., f_d}` whose normalized `q`-expansions `g_j = (a_1(f_j))⁻¹ • qExp(f_j)` satisfy:
1. Every `g_j` is a cuspidal `IsNormalizedHeckeEigenform k χ (g_j) (lam_j)` with `lam_j n = g_j n`,
2. Exact Hecke traces: `Tr(T_n) = ∑_j g_j n` and `Tr(T_m ∘ T_n) = ∑_j g_j m * g_j n` (`m, n ≥ 1`),
3. Atkin–Lehner Multiplicity One: every prime-Hecke eigenspace has `finrank ≤ 1`,
4. Exact degree-2 `GL_2` Euler product for every basis eigenform (`LSeriesSummable (g_j) s →
   ∏'_p degree2EulerFactor k χ (g_j p) p s = LSeries (g_j) s`), and
5. Exact eigenbasis product of `L`-functions equals the product of local degree-2 Euler products! -/
theorem peterssonQExpansion_spectral_eulerProduct
    {k : ℕ} {χ : DirichletCharacter ℂ 1}
    (S : PeterssonQExpansionSpace k χ H) :
    ∃ (f : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H)
      (g : Fin (Module.finrank ℂ H) → ℕ → ℂ),
      (∀ j, g j 0 = 0 ∧ IsNormalizedHeckeEigenform k χ (g j) (g j)) ∧
      (∀ j n, 1 ≤ n → S.hecke n (f j) = g j n • f j) ∧
      (∀ n, 1 ≤ n → LinearMap.trace ℂ H (S.hecke n) = ∑ j, g j n) ∧
      (∀ m n, 1 ≤ m → 1 ≤ n →
        LinearMap.trace ℂ H (S.hecke m ∘ₗ S.hecke n) = ∑ j, g j m * g j n) ∧
      (∀ α : ℕ → ℂ, Module.finrank ℂ (primeHeckeEigenspace S.hecke α) ≤ 1) ∧
      (∀ j (s : ℂ), LSeriesSummable (g j) s →
        (∏' (p : Nat.Primes), degree2EulerFactor k χ (g j (p : ℕ)) (p : ℕ) s) =
          LSeries (g j) s) ∧
      (∀ (s : ℂ), (∀ j, LSeriesSummable (g j) s) →
        (∏ j : Fin (Module.finrank ℂ H),
          ∏' (p : Nat.Primes), degree2EulerFactor k χ (g j (p : ℕ)) (p : ℕ) s) =
          ∏ j : Fin (Module.finrank ℂ H), LSeries (g j) s) := by
  obtain ⟨f, lam, heig, _, _, _, _⟩ := exists_orthonormalBasis_heckeEigenforms S.toPeterssonHeckeSpace
  have hq_eig : ∀ j, IsHeckeEigenform k χ (S.qExp (f j)) (lam j) := fun j n hn => by
    rw [← S.qExp_hecke n hn (f j), heig j n (Nat.coprime_one_right n), map_smul]
  have hq_ne : ∀ j, S.qExp (f j) ≠ 0 := fun j h0 =>
    (f.orthonormal.ne_zero j) (S.qExp_injective (h0.trans (map_zero S.qExp).symm))
  have hq1_ne : ∀ j, S.qExp (f j) 1 ≠ 0 := fun j =>
    cusp_eigenform_coeff_one_ne_zero (S.qExp_cusp (f j)) (hq_eig j) (hq_ne j)
  let g : Fin (Module.finrank ℂ H) → ℕ → ℂ := fun j => (S.qExp (f j) 1)⁻¹ • S.qExp (f j)
  have hg_norm : ∀ j, g j 0 = 0 ∧ IsNormalizedHeckeEigenform k χ (g j) (lam j) := fun j => by
    obtain ⟨h0, hn, _⟩ := cusp_eigenform_normalize (S.qExp_cusp (f j)) (hq_eig j) (hq1_ne j)
    exact ⟨h0, hn⟩
  have hlam_eq_g : ∀ j n, 1 ≤ n → lam j n = g j n := fun j n hn =>
    eigenvalue_eq_coeff (hg_norm j).2 hn
  have hg_self : ∀ j, g j 0 = 0 ∧ IsNormalizedHeckeEigenform k χ (g j) (g j) := fun j => by
    refine ⟨(hg_norm j).1, (hg_norm j).2.1, fun n hn => ?_⟩
    rw [← hlam_eq_g j n hn]
    exact (hg_norm j).2.2 n hn
  have hf_eig : ∀ j n, 1 ≤ n → S.hecke n (f j) = g j n • f j := fun j n hn => by
    rw [← hlam_eq_g j n hn]
    exact heig j n (Nat.coprime_one_right n)
  refine ⟨f, g, hg_self, hf_eig, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    exact hecke_trace_eq_sum_eigenvalues S.toPeterssonHeckeSpace f g (fun j => hf_eig j n hn)
  · intro m n hm hn
    exact hecke_trace_comp_eq_sum_mul_eigenvalues S.toPeterssonHeckeSpace f g
      (fun j => hf_eig j m hm) (fun j => hf_eig j n hn)
  · intro α
    exact finrank_cuspHeckeEigenspace_le_one (k := k) (χ := χ) S.hecke S.qExp
      S.qExp_injective S.qExp_cusp (fun p hp v => S.qExp_hecke p hp.one_le v) α
  · intro j s hs
    exact eigenform_LSeries_eulerProduct (hg_self j).2 hs
  · intro s hs
    refine Finset.prod_congr rfl fun j _ => ?_
    exact eigenform_LSeries_eulerProduct (hg_self j).2 (hs j)

end HeckeTraceAndSpectralBridge

/-! ## Section 5: Master Stage 6 Packaging Theorem -/

/-- **Stage 6 Master Unconditional Packaging Theorem**:
bundles:
1. Simultaneous Spectral Theorem for arbitrary commuting families of normal operators on any
   finite-dimensional complex inner product space,
2. Joint eigenspace orthogonality for distinct characters,
3. Unconditional existence of an orthonormal Hecke eigenbasis with exact Petersson conjugation,
   multiplicativity, prime-power recurrence, and exact `Tr(T_n)` / `Tr(T_m ∘ T_n)` trace identities
   on every `PeterssonHeckeSpace N k χ H`, and
4. Atkin–Lehner Normalized Eigenform Multiplicity One (`normalized_eigenform_eq_of_prime_eigenvalues`). -/
theorem stage6_hecke_spectral_master
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (ℱ : Set (H →ₗ[ℂ] H))
    (hnorm : ∀ T ∈ ℱ, LinearMap.adjoint T ∘ₗ T = T ∘ₗ LinearMap.adjoint T)
    (hcomm : ∀ S ∈ ℱ, ∀ T ∈ ℱ, S ∘ₗ T = T ∘ₗ S)
    {N k : ℕ} {χ : DirichletCharacter ℂ N}
    (S : PeterssonHeckeSpace N k χ H) :
    (∃ (e : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H)
       (ev : (H →ₗ[ℂ] H) → Fin (Module.finrank ℂ H) → ℂ),
       ∀ T ∈ ℱ, ∀ i, T (e i) = ev T i • e i) ∧
    (∃ (f : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H)
       (lam : Fin (Module.finrank ℂ H) → ℕ → ℂ),
       (∀ j n, Nat.Coprime n N → S.hecke n (f j) = lam j n • f j) ∧
       (∀ j n, Nat.Coprime n N → star (lam j n) = star (χ (n : ZMod N)) * lam j n) ∧
       (∀ n, Nat.Coprime n N → LinearMap.trace ℂ H (S.hecke n) = ∑ j, lam j n) ∧
       (∀ m n, Nat.Coprime m N → Nat.Coprime n N →
         LinearMap.trace ℂ H (S.hecke m ∘ₗ S.hecke n) = ∑ j, lam j m * lam j n)) ∧
    (∀ (f g lam₁ lam₂ : ℕ → ℂ), f 0 = 0 → g 0 = 0 →
      IsNormalizedHeckeEigenform k χ f lam₁ → IsNormalizedHeckeEigenform k χ g lam₂ →
      (∀ p : ℕ, p.Prime → lam₁ p = lam₂ p) → f = g) := by
  refine ⟨exists_orthonormalBasis_simultaneous_eigenvectors_of_comm_normal ℱ hnorm hcomm, ?_,
    fun f g lam₁ lam₂ hf0 hg0 hf hg hp =>
      normalized_eigenform_eq_of_prime_eigenvalues hf0 hg0 hf hg hp⟩
  obtain ⟨f, lam, heig, hstar, _, _, _⟩ := exists_orthonormalBasis_heckeEigenforms S
  refine ⟨f, lam, heig, hstar, ?_, ?_⟩
  · intro n hcop
    exact hecke_trace_eq_sum_eigenvalues S f lam (fun j => heig j n hcop)
  · intro m n hm hn
    exact hecke_trace_comp_eq_sum_mul_eigenvalues S f lam
      (fun j => heig j m hm) (fun j => heig j n hn)

end RHDirect.Stage6HeckeSpectral
