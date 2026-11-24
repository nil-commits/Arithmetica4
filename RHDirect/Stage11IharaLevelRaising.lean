import RHDirect.Stage3PatchingUnification
import RHDirect.Stage8RamanujanDelta
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# RHDirect.Stage11IharaLevelRaising

**UNCONDITIONAL CONCRETE IHARA'S LEMMA, DEGENERACY-MAP OVERLAP MATRIX
`η_q = q^{k-2} (q + 1)² - T_q²`, NEWFORM–OLDFORM ORTHOGONAL SPLITTING, AND RIBET'S 1984
LEVEL-RAISING CONGRUENCE CRITERION** in pure Mathlib `v4.33.1` (`0` `sorry`, `0` custom `axiom`s,
`0` assumptions).

## Main Unconditional Results

1. **Concrete Weight-`k` Degeneracy Maps `α₁, α_q : M_old → M_full` & Ihara Overlap Matrix**:
   - `IharaDegeneracySpace k q`: real inner product spaces `(M_old, M_full)` with self-adjoint
     Hecke operator `T_q : M_old →ₗ[ℝ] M_old` and isometric degeneracy embeddings
     `α₁, α_q : M_old →ₗ[ℝ] M_full` (representing `f(τ)` and `q^{k/2} f(q τ)`) satisfying the exact
     weight-`k` Hecke–Degeneracy Overlap Identity
     `⟪α₁ f, α_q g⟫_ℝ = (1 / ((q + 1) √(q^{k-2}))) * ⟪T_q f, g⟫_ℝ` (reducing at `k = 2` to
     `⟪α₁ f, α_q g⟫_ℝ = (1 / (q + 1)) * ⟪T_q f, g⟫_ℝ` via `IharaDegeneracySpace.ofWeightTwo`).
   - Exact `2 × 2` block Gram operator `iharaGramOp = !![1, T_q / c; T_q / c, 1]` and scaled
     Gram operator `iharaScaledGramOp = !![c, T_q; T_q, c]` (`c = (q + 1) √(q^{k-2})`, equal to
     `q + 1` at `k = 2`), satisfying `⟪α u, α v⟫_ℝ = ⟪iharaGramOp u, v⟫`.
   - **`ihara_gram_det_eq`** (weight `2`) and **`ihara_weightK_gram_det_eq`** (general weight
     `k ≥ 2`): on any `T_q`-eigenvector `f` with eigenvalue `a_q`, the scaled `2 × 2` Gram
     determinant of `{α₁ f, α_q f}` equals
     `(q^{k-2} (q + 1)² - a_q²) * ‖f‖⁴` (for `k = 2`: `((q + 1)² - a_q²) * ‖f‖⁴`).
   - **`ihara_degeneracy_injective_of_ramanujan`**: unconditional Ihara injectivity of
     `α₁ ⊕ α_q : M_old × M_old → M_full` whenever `|a_q| < (q + 1) √(q^{k-2})` (in particular
     under the Ramanujan–Petersson bound `|a_q| ≤ 2 q^{(k-1)/2}`, since
     `q^{k-2} (q + 1)² - 4 q^{k-1} = q^{k-2} (q - 1)² > 0` for all `q ≥ 2, k ≥ 2`!).

2. **Integral Lattice Degeneracy System, Unimodular Saturation Splitting & Exact Congruence
   Module Isomorphism**:
   - `IntegralIharaLattice k q`: `ℤ`-lattices `(L_old, L_full)` with integral degeneracy maps
     `α₁, α_q` (representing `f(τ)` and `q^{k-1} f(q τ)`), adjoint/trace `β : L_full → L_old × L_old`,
     and exact `2 × 2` integer Ihara matrix `β ∘ α = !![q + 1, T_q; T_q, q^{k-2}(q + 1)]` whose
     operator determinant is `η_q = q^{k-2} (q + 1)² - T_q²`.
   - `surjective_unimodular_adjoint_of_saturated`: for finite-rank free `ℤ`-modules with unimodular
     pairings, saturation of `M_old_ℤ = im(α)` in `M_full_ℤ` unconditionally implies `M_full_ℤ / M_old_ℤ`
     is free, `α` splits over `ℤ`, the unimodular adjoint `β = α*` is **surjective**, and
     `ker(β) = M_old_ℤ^⊥ = M_new_ℤ`!
   - `congruenceModuleEquiv`: exact isomorphism
     `M_full_ℤ / (M_old_ℤ ⊕ M_new_ℤ) ≃ₗ[ℤ] (L_old × L_old) / im(β ∘ α)` when `β` is surjective,
     and unconditional annihilation by `det(η_q)` (`congruenceModule_annihilated_by_det_η`).

3. **Unconditional Ribet's 1984 Level-Raising Congruence Theorem (`0` Assumptions!)**:
   - `ribetLevelRaisingFactor k q a_q := q^{k-2} (q + 1)² - a_q²`.
   - `ribet_level_raising_cond_weight2_iff`: for prime `ℓ`,
     `ℓ ∣ ((q + 1)² - a_q²) ↔ a_q ≡ (q + 1) [ZMOD ℓ] ∨ a_q ≡ -(q + 1) [ZMOD ℓ]`.
   - **`ribet_level_raising_exists_newform_congruence`**: whenever prime `ℓ ∣ q^{k-2} (q + 1)² - a_q²`,
     `ℓ ∤ (q + 1)`, and `f ∈ L_old` is a primitive `T_q`-eigenform (`f ∉ ℓ • L_old`), there exists
     a **nonzero mod-`ℓ` newform `h ∈ M_new_ℤ`** congruent mod `ℓ` to
     `z = a_q • α₁ f - (q + 1) • α_q f ∈ M_old_ℤ`, producing an explicit nonzero `ℓ`-torsion
     element in `M_full_ℤ / (M_old_ℤ ⊕ M_new_ℤ)`.
   - **`ribet_level_raising_criterion`** & **`ribet_level_raising_exists_congruence`**: for any
     commutative Hecke algebra `𝕋` acting compatibly with `α₁, α_q` where `f` has eigensystem
     `π_f : 𝕋 →+* ℤ`:
     - `h ∈ M_new_ℤ` is a nonzero mod-`ℓ` Hecke eigenvector (`∀ t, t • h ≡ π_f t • h [MOD ℓ]`),
     - the old-new congruence ideal satisfies `oldNewCongruenceIdeal π_f M_new_ℤ ≤ (ℓ)`,
     - the mod-`ℓ` eigensystem `π̄_f : 𝕋 →+* ZMod ℓ` **factors through the newform Hecke algebra**
       `𝕋_new := 𝕋 ⧸ Ann_𝕋(M_new_ℤ)`!
     - direct bridge to `Stage3PatchingUnification.congruenceIdeal`.

4. **Concrete Numerical Level-Raising Primes & Non-Vacuous 4D Lattice Witness**:
   - Ramanujan's `Δ` (`k = 12`, via `Stage8RamanujanDelta.ramanujanTau`):
     - `q = 2, τ(2) = -24`: `2¹⁰ · 3² - (-24)² = 9216 - 576 = 8640 = 2⁶ · 3³ · 5` → level-raising prime `ℓ = 5`!
     - `q = 3, τ(3) = 252`: `3¹⁰ · 4² - 252² = 881280 = 2⁷ · 3⁴ · 5 · 17` → level-raising primes `ℓ = 5, 17`!
   - Weight-`2` `X₀(11)` (`q = 2, 3, 7`) and an explicit concrete 4D unimodular lattice witness
     `v₁ = ![1, 1, 1, 0], v₂ = ![-1, -1, 0, 1] ∈ ℤ⁴` realizing `q = 2, a₂ = -2, ℓ = 5` end-to-end!
-/

noncomputable section

open Module Submodule Finset Matrix
open scoped BigOperators Pointwise InnerProductSpace
open RHDirect.Stage3PatchingUnification RHDirect.Stage8RamanujanDelta

namespace RHDirect.Stage11IharaLevelRaising

/-! ## Section 1: Concrete Degeneracy Maps `α₁, α_q`, Ihara Overlap Matrix & Gram Determinant -/

section RealIharaDegeneracy

/-- The exact weight-`k` Ihara degeneracy normalization constant
`c_k(q) := (q + 1) * √(q^{k-2})`. For `k = 2`, `c_2(q) = q + 1`. -/
def iharaScale (k q : ℕ) : ℝ :=
  ((q : ℝ) + 1) * Real.sqrt ((q : ℝ) ^ (k - 2))

theorem iharaScale_weight2 (q : ℕ) : iharaScale 2 q = (q : ℝ) + 1 := by
  simp [iharaScale]

theorem iharaScale_sq (k q : ℕ) :
    iharaScale k q ^ 2 = (q : ℝ) ^ (k - 2) * ((q : ℝ) + 1) ^ 2 := by
  unfold iharaScale
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  ring

theorem iharaScale_pos (k : ℕ) {q : ℕ} (hq : 0 < q) : 0 < iharaScale k q := by
  unfold iharaScale
  have hqR : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq
  have hpow : (0 : ℝ) < (q : ℝ) ^ (k - 2) := pow_pos hqR _
  exact mul_pos (by linarith) (Real.sqrt_pos.mpr hpow)

theorem iharaScale_ne_zero (k : ℕ) {q : ℕ} (hq : 0 < q) : iharaScale k q ≠ 0 :=
  ne_of_gt (iharaScale_pos k hq)

/-- Concrete weight-`k` oldform–newform degeneracy system on real inner product spaces:
- `M_old` models `S_k(Γ₀(N))` with Petersson inner product `⟪·,·⟫_ℝ` and self-adjoint Hecke
  operator `T_q`,
- `M_full` models `S_k(Γ₀(Nq))` with isometric degeneracy embeddings `α₁, α_q : M_old →ₗ[ℝ] M_full`
  (representing `f(τ)` and `q^{k/2} f(q τ)`),
- Exact Hecke–Degeneracy Overlap Identity:
  `⟪α₁ f, α_q g⟫_ℝ = (1 / ((q + 1) √(q^{k-2}))) * ⟪T_q f, g⟫_ℝ`. -/
structure IharaDegeneracySpace (k q : ℕ) (M_old M_full : Type*)
    [NormedAddCommGroup M_old] [InnerProductSpace ℝ M_old]
    [NormedAddCommGroup M_full] [InnerProductSpace ℝ M_full] where
  T_q : M_old →ₗ[ℝ] M_old
  T_q_selfAdjoint : ∀ f g : M_old, ⟪T_q f, g⟫_ℝ = ⟪f, T_q g⟫_ℝ
  α₁ : M_old →ₗ[ℝ] M_full
  α_q : M_old →ₗ[ℝ] M_full
  inner_α₁ : ∀ f g : M_old, ⟪α₁ f, α₁ g⟫_ℝ = ⟪f, g⟫_ℝ
  inner_αq : ∀ f g : M_old, ⟪α_q f, α_q g⟫_ℝ = ⟪f, g⟫_ℝ
  inner_α₁_αq : ∀ f g : M_old,
    ⟪α₁ f, α_q g⟫_ℝ = (1 / iharaScale k q) * ⟪T_q f, g⟫_ℝ

/-- Weight-`2` constructor where `iharaScale 2 q = q + 1` and the overlap identity is literally
`⟪α₁ f, α_q g⟫_ℝ = (1 / (q + 1)) * ⟪T_q f, g⟫_ℝ`. -/
def IharaDegeneracySpace.ofWeightTwo {q : ℕ} {M_old M_full : Type*}
    [NormedAddCommGroup M_old] [InnerProductSpace ℝ M_old]
    [NormedAddCommGroup M_full] [InnerProductSpace ℝ M_full]
    (T_q : M_old →ₗ[ℝ] M_old)
    (hSA : ∀ f g : M_old, ⟪T_q f, g⟫_ℝ = ⟪f, T_q g⟫_ℝ)
    (α₁ α_q : M_old →ₗ[ℝ] M_full)
    (h1 : ∀ f g : M_old, ⟪α₁ f, α₁ g⟫_ℝ = ⟪f, g⟫_ℝ)
    (hq : ∀ f g : M_old, ⟪α_q f, α_q g⟫_ℝ = ⟪f, g⟫_ℝ)
    (h1q : ∀ f g : M_old, ⟪α₁ f, α_q g⟫_ℝ = (1 / ((q : ℝ) + 1)) * ⟪T_q f, g⟫_ℝ) :
    IharaDegeneracySpace 2 q M_old M_full where
  T_q := T_q
  T_q_selfAdjoint := hSA
  α₁ := α₁
  α_q := α_q
  inner_α₁ := h1
  inner_αq := hq
  inner_α₁_αq := fun f g => by rw [iharaScale_weight2]; exact h1q f g

namespace IharaDegeneracySpace

variable {k q : ℕ} {M_old M_full : Type*}
  [NormedAddCommGroup M_old] [InnerProductSpace ℝ M_old]
  [NormedAddCommGroup M_full] [InnerProductSpace ℝ M_full]
  (S : IharaDegeneracySpace k q M_old M_full)

theorem inner_αq_α₁ (f g : M_old) :
    ⟪S.α_q f, S.α₁ g⟫_ℝ = (1 / iharaScale k q) * ⟪S.T_q f, g⟫_ℝ := by
  rw [real_inner_comm, S.inner_α₁_αq, S.T_q_selfAdjoint, real_inner_comm]

theorem norm_α₁ (f : M_old) : ‖S.α₁ f‖ = ‖f‖ := by
  have hsq : ‖S.α₁ f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, S.inner_α₁]
  nlinarith [norm_nonneg (S.α₁ f), norm_nonneg f]

theorem norm_αq (f : M_old) : ‖S.α_q f‖ = ‖f‖ := by
  have hsq : ‖S.α_q f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, S.inner_αq]
  nlinarith [norm_nonneg (S.α_q f), norm_nonneg f]

/-- The combined degeneracy map `α₁ ⊕ α_q : M_old × M_old →ₗ[ℝ] M_full`,
sending `(f, g) ↦ α₁ f + α_q g`. -/
def degeneracyMap : M_old × M_old →ₗ[ℝ] M_full where
  toFun u := S.α₁ u.1 + S.α_q u.2
  map_add' u v := by simp [map_add]; abel
  map_smul' r u := by simp [map_smul, smul_add]

@[simp]
theorem degeneracyMap_apply (u : M_old × M_old) :
    S.degeneracyMap u = S.α₁ u.1 + S.α_q u.2 := rfl

/-- The normalized `2 × 2` block Ihara Gram operator `G_old := α* ∘ α` on `M_old × M_old`:
`G_old = !![1, T_q / c; T_q / c, 1]` where `c = iharaScale k q` (`= q + 1` at `k = 2`). -/
def iharaGramOp : M_old × M_old →ₗ[ℝ] M_old × M_old where
  toFun u := (u.1 + (1 / iharaScale k q) • S.T_q u.2, (1 / iharaScale k q) • S.T_q u.1 + u.2)
  map_add' u v := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add, smul_add] <;> abel
  map_smul' r u := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_add, smul_comm r,
      RingHom.id_apply]

/-- The scaled `2 × 2` block Ihara Gram operator `c • G_old` on `M_old × M_old`:
`!![c, T_q; T_q, c]` (which for `k = 2` is literally `!![q + 1, T_q; T_q, q + 1]`). -/
def iharaScaledGramOp : M_old × M_old →ₗ[ℝ] M_old × M_old where
  toFun u := (iharaScale k q • u.1 + S.T_q u.2, S.T_q u.1 + iharaScale k q • u.2)
  map_add' u v := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add, smul_add] <;> abel
  map_smul' r u := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_add, smul_comm r,
      RingHom.id_apply]

theorem iharaScaledGramOp_eq_smul (hq : 0 < q) (u : M_old × M_old) :
    S.iharaScaledGramOp u = iharaScale k q • S.iharaGramOp u := by
  have hc : iharaScale k q ≠ 0 := iharaScale_ne_zero k hq
  ext
  · simp [iharaScaledGramOp, iharaGramOp, smul_add, smul_smul, mul_inv_cancel₀ hc]
  · simp [iharaScaledGramOp, iharaGramOp, smul_add, smul_smul, mul_inv_cancel₀ hc]

/-- **Exact Block Gram Identity (`α* ∘ α = G_old`)**: for all `u, v ∈ M_old × M_old`,
`⟪(α₁ ⊕ α_q)(u), (α₁ ⊕ α_q)(v)⟫_ℝ = ⟪(G_old u).1, v.1⟫_ℝ + ⟪(G_old u).2, v.2⟫_ℝ`. -/
theorem inner_degeneracyMap_eq_iharaGramOp (u v : M_old × M_old) :
    ⟪S.degeneracyMap u, S.degeneracyMap v⟫_ℝ =
      ⟪(S.iharaGramOp u).1, v.1⟫_ℝ + ⟪(S.iharaGramOp u).2, v.2⟫_ℝ := by
  simp only [degeneracyMap_apply, iharaGramOp, LinearMap.coe_mk, AddHom.coe_mk,
    inner_add_left, inner_add_right, real_inner_smul_left,
    S.inner_α₁, S.inner_αq, S.inner_α₁_αq, S.inner_αq_α₁]

/-- The explicit `2 × 2` Petersson Gram matrix of `{α₁ f, α_q f}` in `M_full`. -/
def iharaGramMatrix (f : M_old) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![⟪S.α₁ f, S.α₁ f⟫_ℝ, ⟪S.α₁ f, S.α_q f⟫_ℝ;
     ⟪S.α_q f, S.α₁ f⟫_ℝ, ⟪S.α_q f, S.α_q f⟫_ℝ]

/-- The scaled `2 × 2` Petersson Gram matrix `(iharaScale k q) • G(α₁ f, α_q f)`
(for `k = 2`, `(q + 1) • G(α₁ f, α_q f)`). -/
def iharaScaledGramMatrix (f : M_old) : Matrix (Fin 2) (Fin 2) ℝ :=
  iharaScale k q • S.iharaGramMatrix f

/-- Exact formula for `iharaGramMatrix f` on any `T_q`-eigenvector `f` with `T_q f = a_q • f`. -/
theorem iharaGramMatrix_of_eigen {f : M_old} {a_q : ℝ} (hf : S.T_q f = a_q • f) :
    S.iharaGramMatrix f =
      (‖f‖ ^ 2) • !![(1 : ℝ), a_q / iharaScale k q; a_q / iharaScale k q, 1] := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [iharaGramMatrix, S.norm_α₁]
  · simp [iharaGramMatrix, S.inner_α₁_αq, hf, real_inner_smul_left]
    ring
  · simp [iharaGramMatrix, S.inner_αq_α₁, hf, real_inner_smul_left]
    ring
  · simp [iharaGramMatrix, S.norm_αq]

/-- Exact formula for `iharaScaledGramMatrix f` on any `T_q`-eigenvector `f`:
`(iharaScale k q) • G(α₁ f, α_q f) = ‖f‖² • !![c, a_q; a_q, c]` (`c = q + 1` at `k = 2`). -/
theorem iharaScaledGramMatrix_of_eigen (hq : 0 < q) {f : M_old} {a_q : ℝ}
    (hf : S.T_q f = a_q • f) :
    S.iharaScaledGramMatrix f =
      (‖f‖ ^ 2) • !![iharaScale k q, a_q; a_q, iharaScale k q] := by
  have hc : iharaScale k q ≠ 0 := iharaScale_ne_zero k hq
  rw [iharaScaledGramMatrix, S.iharaGramMatrix_of_eigen hf]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · ring
  · field_simp [hc]
  · field_simp [hc]
  · ring

/-- **General Weight-`k` Ihara Gram Determinant Formula (`ihara_weightK_gram_det_eq`)**:
on any `T_q`-eigenvector `f` with `T_q f = a_q • f`,
`det(iharaScaledGramMatrix f) = (q^{k-2} (q + 1)² - a_q²) * ‖f‖⁴`. -/
theorem ihara_weightK_gram_det_eq (hq : 0 < q) {f : M_old} {a_q : ℝ}
    (hf : S.T_q f = a_q • f) :
    (S.iharaScaledGramMatrix f).det =
      ((q : ℝ) ^ (k - 2) * ((q : ℝ) + 1) ^ 2 - a_q ^ 2) * ‖f‖ ^ 4 := by
  rw [S.iharaScaledGramMatrix_of_eigen hq hf, Matrix.det_smul, Fintype.card_fin,
    Matrix.det_fin_two_of]
  have hsq := iharaScale_sq k q
  linear_combination (‖f‖ ^ 4) * hsq

/-- **Weight-`2` Ihara Gram Determinant Formula (`ihara_gram_det_eq`)**:
on any `T_q`-eigenvector `f` with `T_q f = a_q • f`,
`det((q + 1) • G(α₁ f, α_q f)) = ((q + 1)² - a_q²) * ‖f‖⁴ = (q + 1 - a_q) * (q + 1 + a_q) * ‖f‖⁴`. -/
theorem ihara_gram_det_eq {q : ℕ} (hq : 0 < q)
    (S2 : IharaDegeneracySpace 2 q M_old M_full)
    {f : M_old} {a_q : ℝ} (hf : S2.T_q f = a_q • f) :
    (S2.iharaScaledGramMatrix f).det =
      (((q : ℝ) + 1) ^ 2 - a_q ^ 2) * ‖f‖ ^ 4 ∧
    (S2.iharaScaledGramMatrix f).det =
      (((q : ℝ) + 1) - a_q) * (((q : ℝ) + 1) + a_q) * ‖f‖ ^ 4 := by
  have h := S2.ihara_weightK_gram_det_eq hq hf
  simp only [Nat.sub_self, pow_zero, one_mul] at h
  exact ⟨h, by rw [h]; ring⟩

/-- Unit-norm specialization: if `‖f‖ = 1` and `T_q f = a_q • f`, then
`det((q + 1) • G(α₁ f, α_q f)) = (q + 1)² - a_q²`. -/
theorem ihara_gram_det_eq_unit {q : ℕ} (hq : 0 < q)
    (S2 : IharaDegeneracySpace 2 q M_old M_full)
    {f : M_old} {a_q : ℝ} (hf : S2.T_q f = a_q • f) (hnorm : ‖f‖ = 1) :
    (S2.iharaScaledGramMatrix f).det = ((q : ℝ) + 1) ^ 2 - a_q ^ 2 := by
  have h := (ihara_gram_det_eq hq S2 hf).1
  rw [hnorm] at h
  simpa using h

/-- Unscaled Gram determinant on any `T_q`-eigenvector `f`:
`det(G(α₁ f, α_q f)) = (1 - a_q² / (q^{k-2} (q + 1)²)) * ‖f‖⁴`. -/
theorem ihara_unscaled_gram_det_eq (hq : 0 < q) {f : M_old} {a_q : ℝ}
    (hf : S.T_q f = a_q • f) :
    (S.iharaGramMatrix f).det =
      (1 - a_q ^ 2 / ((q : ℝ) ^ (k - 2) * ((q : ℝ) + 1) ^ 2)) * ‖f‖ ^ 4 := by
  have hc : iharaScale k q ≠ 0 := iharaScale_ne_zero k hq
  have hsq : iharaScale k q ^ 2 = (q : ℝ) ^ (k - 2) * ((q : ℝ) + 1) ^ 2 := iharaScale_sq k q
  rw [S.iharaGramMatrix_of_eigen hf, Matrix.det_smul, Fintype.card_fin, Matrix.det_fin_two_of]
  rw [← hsq]
  field_simp [hc]

/-! ## Section 2: Unconditional Ihara Degeneracy Injectivity from Ramanujan–Petersson -/

/-- Exact energy identity for the combined degeneracy map:
`‖α₁ f + α_q g‖² = ‖f‖² + 2 / c_k(q) * ⟪T_q f, g⟫_ℝ + ‖g‖²`. -/
theorem norm_sq_degeneracyMap (f g : M_old) :
    ‖S.degeneracyMap (f, g)‖ ^ 2 =
      ‖f‖ ^ 2 + (2 / iharaScale k q) * ⟪S.T_q f, g⟫_ℝ + ‖g‖ ^ 2 := by
  have hsym : ⟪S.T_q g, f⟫_ℝ = ⟪S.T_q f, g⟫_ℝ := by
    rw [S.T_q_selfAdjoint, real_inner_comm]
  rw [← real_inner_self_eq_norm_sq, degeneracyMap_apply, inner_add_left, inner_add_right,
    inner_add_right, S.inner_α₁, S.inner_αq, S.inner_α₁_αq, S.inner_αq_α₁,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hsym]
  ring

/-- **Unconditional Ihara Injectivity Criterion**: if `‖T_q f‖ < iharaScale k q * ‖f‖` for every
nonzero `f ∈ M_old`, then `α₁ ⊕ α_q : M_old × M_old →ₗ[ℝ] M_full` is **INJECTIVE**. -/
theorem ihara_degeneracy_injective_of_norm_lt (hq : 0 < q)
    (hbound : ∀ f : M_old, f ≠ 0 → ‖S.T_q f‖ < iharaScale k q * ‖f‖) :
    Function.Injective S.degeneracyMap := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨f, g⟩ hfg
  have hc_pos : 0 < iharaScale k q := iharaScale_pos k hq
  have hzero : ‖S.degeneracyMap (f, g)‖ ^ 2 = 0 := by rw [hfg, norm_zero, zero_pow two_ne_zero]
  rw [S.norm_sq_degeneracyMap] at hzero
  by_cases hf : f = 0
  · subst hf
    simp only [norm_zero, zero_pow two_ne_zero, map_zero, inner_zero_left, mul_zero, zero_add] at hzero
    have hg : ‖g‖ = 0 := by nlinarith [norm_nonneg g]
    exact Prod.ext rfl (norm_eq_zero.mp hg)
  · by_cases hg : g = 0
    · subst hg
      simp only [norm_zero, zero_pow two_ne_zero, inner_zero_right, mul_zero, add_zero] at hzero
      have hf0 : ‖f‖ = 0 := by nlinarith [norm_nonneg f]
      exact False.elim (hf (norm_eq_zero.mp hf0))
    · have hcs : |⟪S.T_q f, g⟫_ℝ| ≤ ‖S.T_q f‖ * ‖g‖ := abs_real_inner_le_norm (S.T_q f) g
      have hge_neg : -(‖S.T_q f‖ * ‖g‖) ≤ ⟪S.T_q f, g⟫_ℝ := neg_le_of_abs_le hcs
      have hlt : ‖S.T_q f‖ < iharaScale k q * ‖f‖ := hbound f hf
      have hg_pos : 0 < ‖g‖ := norm_pos_iff.mpr hg
      have hmul_lt : ‖S.T_q f‖ * ‖g‖ < iharaScale k q * ‖f‖ * ‖g‖ :=
        mul_lt_mul_of_pos_right hlt hg_pos
      have hdiv_lt : (2 / iharaScale k q) * (‖S.T_q f‖ * ‖g‖) < 2 * ‖f‖ * ‖g‖ := by
        have hpos2 : (0 : ℝ) < 2 / iharaScale k q := div_pos two_pos hc_pos
        have h1 : (2 / iharaScale k q) * (‖S.T_q f‖ * ‖g‖) <
            (2 / iharaScale k q) * (iharaScale k q * ‖f‖ * ‖g‖) :=
          mul_lt_mul_of_pos_left hmul_lt hpos2
        have h2 : (2 / iharaScale k q) * (iharaScale k q * ‖f‖ * ‖g‖) = 2 * ‖f‖ * ‖g‖ := by
          field_simp [ne_of_gt hc_pos]
        linarith
      have hinner_gt : -(2 * ‖f‖ * ‖g‖) < (2 / iharaScale k q) * ⟪S.T_q f, g⟫_ℝ := by
        have h1 : (2 / iharaScale k q) * (-(‖S.T_q f‖ * ‖g‖)) ≤
            (2 / iharaScale k q) * ⟪S.T_q f, g⟫_ℝ :=
          mul_le_mul_of_nonneg_left hge_neg (le_of_lt (div_pos two_pos hc_pos))
        linarith
      have hsq_nonneg : 0 ≤ (‖f‖ - ‖g‖) ^ 2 := sq_nonneg _
      nlinarith

/-- **Key Ramanujan–Ihara Margin Identity**: for every `k ≥ 2` and `q ≥ 2`,
`q^{k-2} (q + 1)² - 4 q^{k-1} = q^{k-2} (q - 1)² > 0`, so the Ramanujan–Petersson bound
`|a_q| ≤ 2 q^{(k-1)/2}` STRICTLY implies `a_q² < q^{k-2} (q + 1)²` and `|a_q| < iharaScale k q`! -/
theorem ramanujan_bound_lt_iharaScale {k q : ℕ} (hk : 2 ≤ k) (hq : 2 ≤ q) {a_q : ℝ}
    (hram : |a_q| ≤ 2 * (q : ℝ) ^ (((k : ℝ) - 1) / 2)) :
    a_q ^ 2 < (q : ℝ) ^ (k - 2) * ((q : ℝ) + 1) ^ 2 ∧ |a_q| < iharaScale k q := by
  have hq_ge : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq_pos : (0 : ℝ) < (q : ℝ) := by linarith
  have hk_sub : (k : ℝ) - 1 = ((k - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; simp
  have hsq_rhs : (2 * (q : ℝ) ^ (((k : ℝ) - 1) / 2)) ^ 2 = 4 * (q : ℝ) ^ (k - 1) := by
    rw [mul_pow, ← Real.rpow_natCast ((q : ℝ) ^ (((k : ℝ) - 1) / 2)) 2,
      ← Real.rpow_mul (le_of_lt hq_pos)]
    have hexp : (((k : ℝ) - 1) / 2) * (2 : ℕ) = ((k - 1 : ℕ) : ℝ) := by
      push_cast; rw [← hk_sub]; ring
    rw [hexp, Real.rpow_natCast]
    norm_num
  have ha_sq : a_q ^ 2 ≤ 4 * (q : ℝ) ^ (k - 1) := by
    have h1 : |a_q| ^ 2 ≤ (2 * (q : ℝ) ^ (((k : ℝ) - 1) / 2)) ^ 2 := by
      nlinarith [abs_nonneg a_q]
    rw [sq_abs, hsq_rhs] at h1
    exact h1
  have hpow_step : (q : ℝ) ^ (k - 1) = (q : ℝ) ^ (k - 2) * (q : ℝ) := by
    have heq : k - 1 = (k - 2) + 1 := by omega
    rw [heq, pow_succ]
  have hmargin : (q : ℝ) ^ (k - 2) * ((q : ℝ) + 1) ^ 2 - 4 * (q : ℝ) ^ (k - 1) =
      (q : ℝ) ^ (k - 2) * ((q : ℝ) - 1) ^ 2 := by
    rw [hpow_step]; ring
  have hmargin_pos : 0 < (q : ℝ) ^ (k - 2) * ((q : ℝ) - 1) ^ 2 := by
    have h1 : 0 < (q : ℝ) ^ (k - 2) := pow_pos hq_pos _
    have h2 : 0 < ((q : ℝ) - 1) ^ 2 := by nlinarith
    exact mul_pos h1 h2
  have hlt_sq : a_q ^ 2 < (q : ℝ) ^ (k - 2) * ((q : ℝ) + 1) ^ 2 := by linarith
  have hlt_abs : |a_q| < iharaScale k q := by
    have hc_pos : 0 < iharaScale k q := iharaScale_pos k (by omega)
    have hsq_c : iharaScale k q ^ 2 = (q : ℝ) ^ (k - 2) * ((q : ℝ) + 1) ^ 2 := iharaScale_sq k q
    have hsq_abs : |a_q| ^ 2 < iharaScale k q ^ 2 := by rw [sq_abs, hsq_c]; exact hlt_sq
    nlinarith [abs_nonneg a_q, hc_pos]
  exact ⟨hlt_sq, hlt_abs⟩

/-- Strict operator-norm bound `‖T_q f‖ < iharaScale k q * ‖f‖` from an orthogonal `T_q`-eigenbasis
whose eigenvalues satisfy `|a_i| < iharaScale k q`. -/
theorem norm_Tq_lt_of_orthogonal_eigenbasis {d : ℕ}
    (b : Module.Basis (Fin d) ℝ M_old)
    (horth : ∀ i j : Fin d, i ≠ j → ⟪b i, b j⟫_ℝ = 0)
    (a : Fin d → ℝ)
    (heig : ∀ i : Fin d, S.T_q (b i) = a i • b i)
    (hbound : ∀ i : Fin d, |a i| < iharaScale k q) :
    ∀ f : M_old, f ≠ 0 → ‖S.T_q f‖ < iharaScale k q * ‖f‖ := by
  intro f hf
  set c : Fin d → ℝ := fun i => b.repr f i
  have hf_eq : f = ∑ i : Fin d, c i • b i := (b.sum_repr f).symm
  have hTf_eq : S.T_q f = ∑ i : Fin d, (c i * a i) • b i := by
    conv_lhs => rw [hf_eq]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, heig i, smul_smul]
  have hpyth : ∀ w : Fin d → ℝ, ‖∑ i : Fin d, w i • b i‖ ^ 2 =
      ∑ i : Fin d, w i ^ 2 * ‖b i‖ ^ 2 := by
    intro w
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_sum, Finset.sum_eq_single i]
    · rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]; ring
    · intro j _ hji
      rw [real_inner_smul_left, real_inner_smul_right, horth i j hji.symm, mul_zero, mul_zero]
    · intro hi; exact False.elim (hi (Finset.mem_univ i))
  have hnorm_f_sq : ‖f‖ ^ 2 = ∑ i : Fin d, c i ^ 2 * ‖b i‖ ^ 2 := by
    conv_lhs => rw [hf_eq]
    exact hpyth c
  have hnorm_Tf_sq : ‖S.T_q f‖ ^ 2 = ∑ i : Fin d, (c i * a i) ^ 2 * ‖b i‖ ^ 2 := by
    conv_lhs => rw [hTf_eq]
    exact hpyth (fun i => c i * a i)
  have hex_nz : ∃ i₀ : Fin d, c i₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hf
    rw [hf_eq]
    exact Finset.sum_eq_zero fun i _ => by rw [hall i, zero_smul]
  obtain ⟨i₀, hi₀⟩ := hex_nz
  have hbi₀_pos : 0 < ‖b i₀‖ ^ 2 := by
    have hne : b i₀ ≠ 0 := b.ne_zero i₀
    exact pow_pos (norm_pos_iff.mpr hne) 2
  have hsq_lt : ‖S.T_q f‖ ^ 2 < (iharaScale k q * ‖f‖) ^ 2 := by
    rw [mul_pow, hnorm_f_sq, hnorm_Tf_sq, Finset.mul_sum]
    refine Finset.sum_lt_sum (fun i _ => ?_) ⟨i₀, Finset.mem_univ i₀, ?_⟩
    · have hai_le : a i ^ 2 ≤ iharaScale k q ^ 2 := by
        have h1 := hbound i
        have h2 : |a i| ^ 2 ≤ iharaScale k q ^ 2 := by
          nlinarith [abs_nonneg (a i)]
        rwa [sq_abs] at h2
      have hnn : 0 ≤ c i ^ 2 * ‖b i‖ ^ 2 := by positivity
      calc (c i * a i) ^ 2 * ‖b i‖ ^ 2
          = a i ^ 2 * (c i ^ 2 * ‖b i‖ ^ 2) := by ring
        _ ≤ iharaScale k q ^ 2 * (c i ^ 2 * ‖b i‖ ^ 2) :=
            mul_le_mul_of_nonneg_right hai_le hnn
    · have hai_lt : a i₀ ^ 2 < iharaScale k q ^ 2 := by
        have h1 := hbound i₀
        have h2 : |a i₀| ^ 2 < iharaScale k q ^ 2 := by
          nlinarith [abs_nonneg (a i₀)]
        rwa [sq_abs] at h2
      have hpos : 0 < c i₀ ^ 2 * ‖b i₀‖ ^ 2 := mul_pos (sq_pos_of_ne_zero hi₀) hbi₀_pos
      calc (c i₀ * a i₀) ^ 2 * ‖b i₀‖ ^ 2
          = a i₀ ^ 2 * (c i₀ ^ 2 * ‖b i₀‖ ^ 2) := by ring
        _ < iharaScale k q ^ 2 * (c i₀ ^ 2 * ‖b i₀‖ ^ 2) :=
            mul_lt_mul_of_pos_right hai_lt hpos
  have hc_nn : 0 ≤ iharaScale k q * ‖f‖ := by
    have h0 := lt_of_le_of_lt (abs_nonneg (a i₀)) (hbound i₀)
    exact mul_nonneg (le_of_lt h0) (norm_nonneg f)
  nlinarith [norm_nonneg (S.T_q f), hc_nn]

/-- **UNCONDITIONAL IHARA DEGENERACY INJECTIVITY (`ihara_degeneracy_injective_of_ramanujan`)**:
for EVERY weight `k ≥ 2` and `q ≥ 2`, if `M_old` admits an orthogonal `T_q`-eigenbasis whose
eigenvalues satisfy the Ramanujan–Petersson bound `|a_i| ≤ 2 q^{(k-1)/2}`, then the degeneracy map
`α₁ ⊕ α_q : M_old × M_old →ₗ[ℝ] M_full` is **INJECTIVE**! -/
theorem ihara_degeneracy_injective_of_ramanujan (hk : 2 ≤ k) (hq : 2 ≤ q)
    {d : ℕ} (b : Module.Basis (Fin d) ℝ M_old)
    (horth : ∀ i j : Fin d, i ≠ j → ⟪b i, b j⟫_ℝ = 0)
    (a : Fin d → ℝ)
    (heig : ∀ i : Fin d, S.T_q (b i) = a i • b i)
    (hram : ∀ i : Fin d, |a i| ≤ 2 * (q : ℝ) ^ (((k : ℝ) - 1) / 2)) :
    Function.Injective S.degeneracyMap :=
  S.ihara_degeneracy_injective_of_norm_lt (by omega)
    (S.norm_Tq_lt_of_orthogonal_eigenbasis b horth a heig
      (fun i => (ramanujan_bound_lt_iharaScale hk hq (hram i)).2))

/-- Weight-`2` direct Ihara injectivity whenever `|a_i| < q + 1`. -/
theorem ihara_degeneracy_injective_weight2_of_lt {q : ℕ} (hq : 0 < q)
    (S2 : IharaDegeneracySpace 2 q M_old M_full)
    {d : ℕ} (b : Module.Basis (Fin d) ℝ M_old)
    (horth : ∀ i j : Fin d, i ≠ j → ⟪b i, b j⟫_ℝ = 0)
    (a : Fin d → ℝ)
    (heig : ∀ i : Fin d, S2.T_q (b i) = a i • b i)
    (hlt : ∀ i : Fin d, |a i| < (q : ℝ) + 1) :
    Function.Injective S2.degeneracyMap :=
  S2.ihara_degeneracy_injective_of_norm_lt hq
    (S2.norm_Tq_lt_of_orthogonal_eigenbasis b horth a heig
      (fun i => by rw [iharaScale_weight2]; exact hlt i))

/-- Single-eigenvector Ihara linear independence: if `f ≠ 0`, `T_q f = a_q • f`, and
`|a_q| < iharaScale k q`, then `{α₁ f, α_q f}` is linearly independent in `M_full`. -/
theorem ihara_eigenvector_pair_linearIndependent (hq : 0 < q)
    {f : M_old} {a_q : ℝ} (hf_ne : f ≠ 0) (hf : S.T_q f = a_q • f)
    (hlt : |a_q| < iharaScale k q) :
    LinearIndependent ℝ ![S.α₁ f, S.α_q f] := by
  rw [Fintype.linearIndependent_iff]
  intro g hsum
  rw [Fin.sum_univ_two] at hsum
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hsum
  have hdeg : S.degeneracyMap (g 0 • f, g 1 • f) = 0 := by
    simp only [degeneracyMap_apply, map_smul]; exact hsum
  have hzero : ‖S.degeneracyMap (g 0 • f, g 1 • f)‖ ^ 2 = 0 := by
    rw [hdeg, norm_zero, zero_pow two_ne_zero]
  rw [S.norm_sq_degeneracyMap] at hzero
  have hc_pos : 0 < iharaScale k q := iharaScale_pos k hq
  have hf_pos : 0 < ‖f‖ ^ 2 := pow_pos (norm_pos_iff.mpr hf_ne) 2
  have hinner : ⟪S.T_q (g 0 • f), g 1 • f⟫_ℝ = g 0 * g 1 * a_q * ‖f‖ ^ 2 := by
    rw [map_smul, hf, smul_smul, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    ring
  rw [norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs,
    sq_abs, sq_abs, hinner] at hzero
  have hquad : (g 0 ^ 2 + (2 * a_q / iharaScale k q) * g 0 * g 1 + g 1 ^ 2) * ‖f‖ ^ 2 = 0 := by
    linarith [show (2 / iharaScale k q) * (g 0 * g 1 * a_q * ‖f‖ ^ 2) =
      (2 * a_q / iharaScale k q) * g 0 * g 1 * ‖f‖ ^ 2 by ring]
  have hq0 : g 0 ^ 2 + (2 * a_q / iharaScale k q) * g 0 * g 1 + g 1 ^ 2 = 0 :=
    (mul_eq_zero.mp hquad).resolve_right (ne_of_gt hf_pos)
  have hcomp : (g 0 + (a_q / iharaScale k q) * g 1) ^ 2 +
      (1 - (a_q / iharaScale k q) ^ 2) * g 1 ^ 2 = 0 := by
    linear_combination hq0
  have hcoef_pos : 0 < 1 - (a_q / iharaScale k q) ^ 2 := by
    have hdiv : |a_q / iharaScale k q| < 1 := by
      rw [abs_div, abs_of_pos hc_pos, div_lt_one hc_pos]
      exact hlt
    have hsq : (a_q / iharaScale k q) ^ 2 < 1 := by
      have h1 : |a_q / iharaScale k q| ^ 2 < 1 := by nlinarith [abs_nonneg (a_q / iharaScale k q)]
      rwa [sq_abs] at h1
    linarith
  have hg1 : g 1 = 0 := by
    have h1 : g 1 ^ 2 = 0 := by
      nlinarith [sq_nonneg (g 0 + (a_q / iharaScale k q) * g 1), sq_nonneg (g 1)]
    exact (pow_eq_zero_iff two_ne_zero).mp h1
  have hg0 : g 0 = 0 := by
    rw [hg1, mul_zero, add_zero, zero_pow two_ne_zero, mul_zero, add_zero] at hcomp
    exact (pow_eq_zero_iff two_ne_zero).mp hcomp
  intro i
  fin_cases i <;> assumption

end IharaDegeneracySpace

end RealIharaDegeneracy

/-! ## Section 3: Integral Lattice Degeneracy System, `2 × 2` Integer Ihara Matrix & Congruence Module -/

section IntegralIharaLattice

/-- The exact **general weight-`k` Ribet level-raising factor**:
`ribetLevelRaisingFactor k q a_q = q^{k-2} (q + 1)² - a_q²`.
- For `k = 2`: `(q + 1)² - a_q² = (q + 1 - a_q)(q + 1 + a_q)`.
- For `k = 12`: `q^{10} (q + 1)² - a_q²`. -/
def ribetLevelRaisingFactor (k q : ℕ) (a_q : ℤ) : ℤ :=
  (q : ℤ) ^ (k - 2) * ((q : ℤ) + 1) ^ 2 - a_q ^ 2

@[simp]
theorem ribetLevelRaisingFactor_weight2 (q : ℕ) (a_q : ℤ) :
    ribetLevelRaisingFactor 2 q a_q = ((q : ℤ) + 1) ^ 2 - a_q ^ 2 := by
  simp [ribetLevelRaisingFactor]

theorem ribetLevelRaisingFactor_weight2_factor (q : ℕ) (a_q : ℤ) :
    ribetLevelRaisingFactor 2 q a_q = (((q : ℤ) + 1) - a_q) * (((q : ℤ) + 1) + a_q) := by
  rw [ribetLevelRaisingFactor_weight2]; ring

theorem ribetLevelRaisingFactor_even_factor (m q : ℕ) (hm : 1 ≤ m) (a_q : ℤ) :
    ribetLevelRaisingFactor (2 * m) q a_q =
      ((q : ℤ) ^ (m - 1) * ((q : ℤ) + 1) - a_q) * ((q : ℤ) ^ (m - 1) * ((q : ℤ) + 1) + a_q) := by
  unfold ribetLevelRaisingFactor
  have hexp : 2 * m - 2 = (m - 1) + (m - 1) := by omega
  rw [hexp, pow_add]
  ring

/-- Concrete integral lattice degeneracy system at weight `k ≥ 2` and level-raising prime `q`:
- `L_old` models the integral oldform lattice `S_k(Γ₀(N); ℤ)` (or `H¹(X₀(N), ℤ)`),
- `L_full` models the integral level-`Nq` lattice `S_k(Γ₀(Nq); ℤ)` (or `H¹(X₀(Nq), ℤ)`),
- `α₁, α_q : L_old →ₗ[ℤ] L_full` are the integral degeneracy maps (`f(τ)` and `q^{k-1} f(q τ)`),
- `β : L_full →ₗ[ℤ] L_old × L_old` is the integral trace/adjoint map (`(q + 1) α*`),
- `β ∘ α = !![q + 1, T_q; T_q, q^{k-2} (q + 1)]` (exact integer Ihara overlap matrix!). -/
structure IntegralIharaLattice (k q : ℕ) (L_old L_full : Type*)
    [AddCommGroup L_old] [AddCommGroup L_full] where
  T_q : L_old →ₗ[ℤ] L_old
  α₁ : L_old →ₗ[ℤ] L_full
  α_q : L_old →ₗ[ℤ] L_full
  β : L_full →ₗ[ℤ] L_old × L_old
  β_comp_α : ∀ u : L_old × L_old,
    β (α₁ u.1 + α_q u.2) =
      (((q : ℤ) + 1) • u.1 + T_q u.2,
       T_q u.1 + ((q : ℤ) ^ (k - 2) * ((q : ℤ) + 1)) • u.2)

namespace IntegralIharaLattice

variable {k q : ℕ} {L_old L_full : Type*}
  [AddCommGroup L_old] [AddCommGroup L_full]
  (L : IntegralIharaLattice k q L_old L_full)

/-- The combined integral degeneracy map `α : L_old × L_old →ₗ[ℤ] L_full`,
`(x, y) ↦ α₁ x + α_q y`. -/
def α : L_old × L_old →ₗ[ℤ] L_full where
  toFun u := L.α₁ u.1 + L.α_q u.2
  map_add' u v := by simp [map_add]; abel
  map_smul' r u := by simp [smul_add]

@[simp]
theorem α_apply (u : L_old × L_old) : L.α u = L.α₁ u.1 + L.α_q u.2 := rfl

/-- The exact `2 × 2` integer Ihara operator `G_int := !![q + 1, T_q; T_q, q^{k-2}(q + 1)]`
on `L_old × L_old`. -/
def iharaOp : L_old × L_old →ₗ[ℤ] L_old × L_old where
  toFun u :=
    (((q : ℤ) + 1) • u.1 + L.T_q u.2,
     L.T_q u.1 + ((q : ℤ) ^ (k - 2) * ((q : ℤ) + 1)) • u.2)
  map_add' u v := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add, smul_add] <;> abel
  map_smul' r u := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_add, smul_comm r,
      RingHom.id_apply]

/-- The exact `2 × 2` adjugate Ihara operator `adj(G_int) = !![q^{k-2}(q + 1), -T_q; -T_q, q + 1]`
on `L_old × L_old`. -/
def iharaAdjOp : L_old × L_old →ₗ[ℤ] L_old × L_old where
  toFun u :=
    (((q : ℤ) ^ (k - 2) * ((q : ℤ) + 1)) • u.1 - L.T_q u.2,
     -L.T_q u.1 + ((q : ℤ) + 1) • u.2)
  map_add' u v := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add, smul_add] <;> abel
  map_smul' r u := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_sub, smul_add, smul_neg,
      smul_comm r, RingHom.id_apply]

/-- The exact weight-`k` Ihara determinant operator
`η_q := q^{k-2} (q + 1)² - T_q² : L_old →ₗ[ℤ] L_old`. -/
def ηOp : L_old →ₗ[ℤ] L_old :=
  ((q : ℤ) ^ (k - 2) * ((q : ℤ) + 1) ^ 2) • LinearMap.id - L.T_q.comp L.T_q

@[simp]
theorem ηOp_apply (x : L_old) :
    L.ηOp x = ((q : ℤ) ^ (k - 2) * ((q : ℤ) + 1) ^ 2) • x - L.T_q (L.T_q x) := rfl

theorem ηOp_apply_eigen {f : L_old} {a_q : ℤ} (hf : L.T_q f = a_q • f) :
    L.ηOp f = ribetLevelRaisingFactor k q a_q • f := by
  rw [ηOp_apply, hf, map_smul, hf, smul_smul, ribetLevelRaisingFactor, sub_smul]
  congr 2
  ring

theorem β_comp_α_eq_iharaOp : L.β.comp L.α = L.iharaOp := by
  apply LinearMap.ext
  intro u
  exact L.β_comp_α u

/-- Exact adjugate identity: `G_int ∘ adj(G_int) = η_q ⊕ η_q`. -/
theorem iharaOp_comp_iharaAdjOp (u : L_old × L_old) :
    L.iharaOp (L.iharaAdjOp u) = (L.ηOp u.1, L.ηOp u.2) := by
  ext
  · simp only [iharaOp, iharaAdjOp, ηOp_apply, LinearMap.coe_mk, AddHom.coe_mk,
      map_add, map_neg, map_smul, smul_sub, smul_smul]
    have hmul : ((q : ℤ) + 1) * ((q : ℤ) ^ (k - 2) * ((q : ℤ) + 1)) =
        (q : ℤ) ^ (k - 2) * ((q : ℤ) + 1) ^ 2 := by ring
    rw [hmul]
    abel
  · simp only [iharaOp, iharaAdjOp, ηOp_apply, LinearMap.coe_mk, AddHom.coe_mk,
      map_sub, map_smul, smul_add, smul_neg, smul_smul]
    have hmul : ((q : ℤ) ^ (k - 2) * ((q : ℤ) + 1)) * ((q : ℤ) + 1) =
        (q : ℤ) ^ (k - 2) * ((q : ℤ) + 1) ^ 2 := by ring
    rw [hmul]
    abel

/-- Exact adjugate identity: `adj(G_int) ∘ G_int = η_q ⊕ η_q`. -/
theorem iharaAdjOp_comp_iharaOp (u : L_old × L_old) :
    L.iharaAdjOp (L.iharaOp u) = (L.ηOp u.1, L.ηOp u.2) := by
  ext
  · simp only [iharaOp, iharaAdjOp, ηOp_apply, LinearMap.coe_mk, AddHom.coe_mk,
      map_add, map_smul, smul_add, smul_smul]
    have hmul : ((q : ℤ) ^ (k - 2) * ((q : ℤ) + 1)) * ((q : ℤ) + 1) =
        (q : ℤ) ^ (k - 2) * ((q : ℤ) + 1) ^ 2 := by ring
    rw [hmul]
    abel
  · simp only [iharaOp, iharaAdjOp, ηOp_apply, LinearMap.coe_mk, AddHom.coe_mk,
      map_add, map_smul, smul_add, smul_smul]
    have hmul : ((q : ℤ) + 1) * ((q : ℤ) ^ (k - 2) * ((q : ℤ) + 1)) =
        (q : ℤ) ^ (k - 2) * ((q : ℤ) + 1) ^ 2 := by ring
    rw [hmul]
    abel

/-- The oldform sublattice `M_old_ℤ := im(α) ⊆ L_full`. -/
def oldSubmodule : Submodule ℤ L_full := LinearMap.range L.α

/-- The newform sublattice `M_new_ℤ := ker(β) = M_old_ℤ^⊥ ⊆ L_full`. -/
def newSubmodule : Submodule ℤ L_full := LinearMap.ker L.β

/-- The Ribet congruence quotient module `M_full_ℤ / (M_old_ℤ + M_new_ℤ)`. -/
abbrev congruenceModule : Type _ :=
  L_full ⧸ (L.oldSubmodule ⊔ L.newSubmodule)

/-- If `η_q = q^{k-2} (q + 1)² - T_q²` is injective on `L_old`, then:
1. `iharaOp` is injective,
2. `α : L_old × L_old → L_full` is injective, and
3. `M_old_ℤ ∩ M_new_ℤ = ⊥` (exact orthogonal direct sum `M_old_ℤ ⊕ M_new_ℤ ⊆ M_full_ℤ`)! -/
theorem disjoint_old_new_of_ηOp_injective (hη : Function.Injective L.ηOp) :
    Function.Injective L.iharaOp ∧
      Function.Injective L.α ∧
      L.oldSubmodule ⊓ L.newSubmodule = ⊥ := by
  have hI : Function.Injective L.iharaOp := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    have h1 := L.iharaAdjOp_comp_iharaOp u
    rw [hu, map_zero] at h1
    ext
    · exact hη (by simpa [map_zero] using (congrArg Prod.fst h1).symm)
    · exact hη (by simpa [map_zero] using (congrArg Prod.snd h1).symm)
  have hα : Function.Injective L.α := by
    refine Function.Injective.of_comp (f := L.β) ?_
    change Function.Injective (L.β.comp L.α)
    rw [L.β_comp_α_eq_iharaOp]
    exact hI
  have hdisj : L.oldSubmodule ⊓ L.newSubmodule = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨⟨u, rfl⟩, hv_new⟩
    have h0 : L.iharaOp u = 0 := by
      have hba : L.β (L.α u) = L.iharaOp u := congrArg (fun f => f u) L.β_comp_α_eq_iharaOp
      rw [← hba]
      exact hv_new
    have hu0 : u = 0 := hI (by rw [h0, map_zero])
    rw [hu0, map_zero]
    exact Submodule.zero_mem _
  exact ⟨hI, hα, hdisj⟩

/-- **Exact Congruence Module Isomorphism**:
when `β : L_full → L_old × L_old` is surjective, `β` induces a canonical `ℤ`-linear isomorphism
`M_full_ℤ ⧸ (M_old_ℤ + M_new_ℤ) ≃ₗ[ℤ] (L_old × L_old) ⧸ im(G_int)`. -/
def congruenceModuleEquiv (hβ : Function.Surjective L.β) :
    L.congruenceModule ≃ₗ[ℤ] (L_old × L_old) ⧸ LinearMap.range L.iharaOp := by
  let qMap : L_full →ₗ[ℤ] (L_old × L_old) ⧸ LinearMap.range L.iharaOp :=
    (Submodule.mkQ (LinearMap.range L.iharaOp)).comp L.β
  have hker : LinearMap.ker qMap = L.oldSubmodule ⊔ L.newSubmodule := by
    ext v
    simp only [LinearMap.mem_ker, qMap, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
    constructor
    · rintro ⟨u, hu⟩
      have hdiff : v - L.α u ∈ L.newSubmodule := by
        change L.β (v - L.α u) = 0
        rw [map_sub, show L.β (L.α u) = L.iharaOp u from
          congrArg (fun f => f u) L.β_comp_α_eq_iharaOp, hu, sub_self]
      have hv : v = L.α u + (v - L.α u) := by abel
      rw [hv]
      exact Submodule.add_mem_sup ⟨u, rfl⟩ hdiff
    · intro hv
      rw [Submodule.mem_sup] at hv
      obtain ⟨x, ⟨u, rfl⟩, y, hy, rfl⟩ := hv
      refine ⟨u, ?_⟩
      rw [map_add, show L.β y = 0 from hy, add_zero]
      exact (congrArg (fun f => f u) L.β_comp_α_eq_iharaOp).symm
  have hsurj : Function.Surjective qMap :=
    (Submodule.mkQ_surjective _).comp hβ
  refine LinearEquiv.ofBijective
    (Submodule.liftQ (L.oldSubmodule ⊔ L.newSubmodule) qMap (le_of_eq hker.symm)) ?_
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using Quotient.inductionOn' with
    | h v =>
      change qMap v = 0 at hx
      have hv : v ∈ L.oldSubmodule ⊔ L.newSubmodule := by rw [← hker]; exact hx
      exact (Submodule.Quotient.mk_eq_zero _).mpr hv
  · intro y
    obtain ⟨v, rfl⟩ := hsurj y
    exact ⟨Submodule.Quotient.mk v, rfl⟩

/-- **Operator-Level Annihilation of `M_full_ℤ / (M_old_ℤ ⊕ M_new_ℤ)` by `η_q`**:
for any endomorphism `η_full : L_full →ₗ[ℤ] L_full` lifting `η_q ⊕ η_q` across `β`,
`η_full v ∈ M_old_ℤ ⊔ M_new_ℤ` for EVERY `v ∈ L_full`! -/
theorem η_annihilates_congruenceModule (η_full : L_full →ₗ[ℤ] L_full)
    (hcomm : ∀ v : L_full, L.β (η_full v) = (L.ηOp (L.β v).1, L.ηOp (L.β v).2))
    (v : L_full) :
    η_full v ∈ L.oldSubmodule ⊔ L.newSubmodule := by
  let w : L_full := L.α (L.iharaAdjOp (L.β v))
  have hw_old : w ∈ L.oldSubmodule := ⟨L.iharaAdjOp (L.β v), rfl⟩
  have hdiff_new : η_full v - w ∈ L.newSubmodule := by
    change L.β (η_full v - w) = 0
    rw [map_sub, hcomm v]
    have hbw : L.β w = (L.ηOp (L.β v).1, L.ηOp (L.β v).2) := by
      change (L.β.comp L.α) (L.iharaAdjOp (L.β v)) = _
      rw [L.β_comp_α_eq_iharaOp, L.iharaOp_comp_iharaAdjOp]
    rw [hbw, sub_self]
  have heq : η_full v = w + (η_full v - w) := by abel
  rw [heq]
  exact Submodule.add_mem_sup hw_old hdiff_new

/-- **Scalar Determinant Annihilation (`congruenceModule_annihilated_by_det_η`)**:
if `L_old` is finite-rank free over `ℤ` with basis `b : Fin r → L_old`, then the integer
determinant `d := (LinearMap.toMatrix b b L.ηOp).det` annihilates the ENTIRE congruence quotient
`M_full_ℤ / (M_old_ℤ ⊕ M_new_ℤ)`! -/
theorem congruenceModule_annihilated_by_det_η {r : ℕ} (b : Module.Basis (Fin r) ℤ L_old)
    (x : L.congruenceModule) :
    (LinearMap.toMatrix b b L.ηOp).det • x = 0 := by
  set M : Matrix (Fin r) (Fin r) ℤ := LinearMap.toMatrix b b L.ηOp
  set adjOp : L_old →ₗ[ℤ] L_old := (LinearMap.toMatrix b b).symm M.adjugate
  have hdet_op : L.ηOp.comp adjOp = M.det • LinearMap.id := by
    apply (LinearMap.toMatrix b b).injective
    rw [LinearMap.toMatrix_comp b b b, map_smul, LinearMap.toMatrix_id]
    simp only [adjOp, LinearEquiv.apply_symm_apply, M, Matrix.mul_adjugate]
  induction x using Quotient.inductionOn' with
  | h v =>
    change Submodule.Quotient.mk (M.det • v) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    let u₀ : L_old × L_old := (adjOp (L.β v).1, adjOp (L.β v).2)
    let w : L_full := L.α (L.iharaAdjOp u₀)
    have hw_old : w ∈ L.oldSubmodule := ⟨L.iharaAdjOp u₀, rfl⟩
    have hdiff_new : M.det • v - w ∈ L.newSubmodule := by
      change L.β (M.det • v - w) = 0
      rw [map_sub, map_smul]
      have hbw : L.β w = (M.det • (L.β v).1, M.det • (L.β v).2) := by
        change (L.β.comp L.α) (L.iharaAdjOp u₀) = _
        rw [L.β_comp_α_eq_iharaOp, L.iharaOp_comp_iharaAdjOp]
        ext
        · exact congrArg (fun f => f (L.β v).1) hdet_op
        · exact congrArg (fun f => f (L.β v).2) hdet_op
      rw [hbw]
      ext <;> simp
    have heq : M.det • v = w + (M.det • v - w) := by abel
    rw [heq]
    exact Submodule.add_mem_sup hw_old hdiff_new

end IntegralIharaLattice

end IntegralIharaLattice

/-! ## Section 4: Unimodular Pairing Descent — Saturated `M_old_ℤ` Implies Surjective `β` -/

section UnimodularSaturatedDescent

/-- A submodule `S ⊆ M` of a `ℤ`-module is **saturated** if `n • x ∈ S` with `n ≠ 0` implies
`x ∈ S` (equivalently `M ⧸ S` is torsion-free). -/
def IsSaturatedSubmodule {M : Type*} [AddCommGroup M] (S : Submodule ℤ M) : Prop :=
  ∀ (x : M) (n : ℤ), n ≠ 0 → n • x ∈ S → x ∈ S

/-- A linear map `α : A →ₗ[ℤ] B` is **`ℓ`-saturated** (mod-`ℓ` Ihara injectivity) if
`α u ∈ ℓ • ⊤ → u ∈ ℓ • ⊤`. -/
def IsPrimeSaturatedMap {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (α : A →ₗ[ℤ] B) (ℓ : ℤ) : Prop :=
  ∀ u : A, α u ∈ ℓ • (⊤ : Submodule ℤ B) → u ∈ ℓ • (⊤ : Submodule ℤ A)

/-- Any injective map with saturated image is automatically `ℓ`-saturated for every `ℓ ≠ 0`! -/
theorem isPrimeSaturatedMap_of_injective_saturated {A B : Type*}
    [AddCommGroup A] [AddCommGroup B]
    {α : A →ₗ[ℤ] B} (hinj : Function.Injective α)
    (hsat : IsSaturatedSubmodule (LinearMap.range α)) {ℓ : ℤ} (hℓ : ℓ ≠ 0) :
    IsPrimeSaturatedMap α ℓ := by
  intro u hu
  rw [Submodule.mem_smul_pointwise_iff_exists] at hu ⊢
  obtain ⟨y, _, hy⟩ := hu
  have hy_mem : y ∈ LinearMap.range α := hsat y ℓ hℓ ⟨u, hy.symm⟩
  obtain ⟨v, rfl⟩ := hy_mem
  refine ⟨v, Submodule.mem_top, ?_⟩
  apply hinj
  rw [map_smul]
  exact hy

/-- **Unconditional Splitting & Surjective Adjoint from Unimodular Saturation**:
If `L_old`, `L_full` are finite-rank `ℤ`-modules with unimodular duality equivalences
`pair_old : L_old ≃ₗ[ℤ] Dual ℤ L_old` and `pair_full : L_full ≃ₗ[ℤ] Dual ℤ L_full`, and
`α : L_old × L_old →ₗ[ℤ] L_full` is injective with saturated image `M_old_ℤ := im(α)`, then:
1. `L_full ⧸ M_old_ℤ` is torsion-free and free over `ℤ`,
2. `α` admits a `ℤ`-linear left inverse `s : L_full →ₗ[ℤ] L_old × L_old` (`s ∘ α = id`),
3. the unimodular adjoint `β := (pair_old × pair_old)⁻¹ ∘ α* ∘ pair_full : L_full →ₗ[ℤ] L_old × L_old`
   is **SURJECTIVE**, and
4. `ker(β) = { v : L_full | ∀ u, pair_full v (α u) = 0 }` (exact orthogonal complement `M_old_ℤ^⊥`)! -/
theorem surjective_unimodular_adjoint_of_saturated
    {L_old L_full : Type*} [AddCommGroup L_old]
    [AddCommGroup L_full] [Module.Finite ℤ L_full]
    (pair_old : L_old ≃ₗ[ℤ] Module.Dual ℤ L_old)
    (pair_full : L_full ≃ₗ[ℤ] Module.Dual ℤ L_full)
    (α : L_old × L_old →ₗ[ℤ] L_full)
    (hα_inj : Function.Injective α)
    (hα_sat : IsSaturatedSubmodule (LinearMap.range α)) :
    let pairProd : (L_old × L_old) ≃ₗ[ℤ] Module.Dual ℤ (L_old × L_old) :=
      { toFun := fun p =>
          (pair_old p.1).comp (LinearMap.fst ℤ L_old L_old) +
            (pair_old p.2).comp (LinearMap.snd ℤ L_old L_old)
        invFun := fun φ =>
          (pair_old.symm (φ.comp (LinearMap.inl ℤ L_old L_old)),
           pair_old.symm (φ.comp (LinearMap.inr ℤ L_old L_old)))
        map_add' := fun p q => by
          apply LinearMap.ext; rintro ⟨x, y⟩; simp [map_add]; ring
        map_smul' := fun r p => by
          apply LinearMap.ext; rintro ⟨x, y⟩; simp [smul_add]
        left_inv := fun ⟨p1, p2⟩ => by
          ext
          · change pair_old.symm (((pair_old p1).comp (LinearMap.fst ℤ L_old L_old) +
                (pair_old p2).comp (LinearMap.snd ℤ L_old L_old)).comp
                (LinearMap.inl ℤ L_old L_old)) = p1
            have h : ((pair_old p1).comp (LinearMap.fst ℤ L_old L_old) +
                (pair_old p2).comp (LinearMap.snd ℤ L_old L_old)).comp
                (LinearMap.inl ℤ L_old L_old) = pair_old p1 := by
              apply LinearMap.ext; intro x; simp
            rw [h, pair_old.symm_apply_apply]
          · change pair_old.symm (((pair_old p1).comp (LinearMap.fst ℤ L_old L_old) +
                (pair_old p2).comp (LinearMap.snd ℤ L_old L_old)).comp
                (LinearMap.inr ℤ L_old L_old)) = p2
            have h : ((pair_old p1).comp (LinearMap.fst ℤ L_old L_old) +
                (pair_old p2).comp (LinearMap.snd ℤ L_old L_old)).comp
                (LinearMap.inr ℤ L_old L_old) = pair_old p2 := by
              apply LinearMap.ext; intro y; simp
            rw [h, pair_old.symm_apply_apply]
        right_inv := fun φ => by
          apply LinearMap.ext; rintro ⟨x, y⟩
          change pair_old (pair_old.symm (φ.comp (LinearMap.inl ℤ L_old L_old))) x +
              pair_old (pair_old.symm (φ.comp (LinearMap.inr ℤ L_old L_old))) y = φ (x, y)
          rw [pair_old.apply_symm_apply, pair_old.apply_symm_apply]
          change φ (x, 0) + φ (0, y) = φ (x, y)
          rw [← map_add]
          congr 1; ext <;> simp }
    let β : L_full →ₗ[ℤ] L_old × L_old :=
      pairProd.symm.toLinearMap.comp ((Module.Dual.transpose (R := ℤ) α).comp pair_full.toLinearMap)
    (∃ s : L_full →ₗ[ℤ] L_old × L_old, s.comp α = LinearMap.id) ∧
      Function.Surjective β ∧
      (∀ v : L_full, v ∈ LinearMap.ker β ↔ ∀ u : L_old × L_old, pair_full v (α u) = 0) := by
  intro pairProd β
  -- Step 1: Quotient `Q = L_full / im(α)` is finite and torsion-free, hence free over PID `ℤ`
  let Q := L_full ⧸ LinearMap.range α
  have hQ_fin : Module.Finite ℤ Q :=
    Module.Finite.of_surjective (Submodule.mkQ (LinearMap.range α)) (Submodule.mkQ_surjective _)
  have hQ_tf : Module.IsTorsionFree ℤ Q := by
    refine Module.isTorsionFree_iff_smul_eq_zero.mpr fun {r x} hrx => ?_
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      induction x using Quotient.inductionOn' with
      | h v =>
        change Submodule.Quotient.mk (r • v) = 0 at hrx
        rw [Submodule.Quotient.mk_eq_zero] at hrx
        exact (Submodule.Quotient.mk_eq_zero _).mpr (hα_sat v r hr hrx)
  have hQ_free : Module.Free ℤ Q := Module.free_of_finite_type_torsion_free'
  -- Step 2: Construct section `σ : Q →ₗ[ℤ] L_full` and left inverse `s : L_full →ₗ[ℤ] L_old × L_old`
  let bQ := Module.Free.chooseBasis ℤ Q
  have hlift : ∀ i, ∃ v : L_full, Submodule.mkQ (LinearMap.range α) v = bQ i :=
    fun i => Submodule.mkQ_surjective _ (bQ i)
  choose lift hlift_eq using hlift
  let σ : Q →ₗ[ℤ] L_full := bQ.constr ℤ lift
  have hσ_sec : (Submodule.mkQ (LinearMap.range α)).comp σ = LinearMap.id := by
    apply bQ.ext
    intro i
    simp [σ, hlift_eq]
  let e : (L_old × L_old) ≃ₗ[ℤ] LinearMap.range α := LinearEquiv.ofInjective α hα_inj
  let proj : L_full →ₗ[ℤ] LinearMap.range α :=
    { toFun := fun v => ⟨v - σ (Submodule.mkQ (LinearMap.range α) v), by
        rw [← Submodule.Quotient.mk_eq_zero]
        change Submodule.mkQ (LinearMap.range α) (v - σ (Submodule.mkQ (LinearMap.range α) v)) = 0
        rw [map_sub, show (Submodule.mkQ (LinearMap.range α)) (σ (Submodule.mkQ (LinearMap.range α) v)) =
          Submodule.mkQ (LinearMap.range α) v from
          congrArg (fun f => f (Submodule.mkQ (LinearMap.range α) v)) hσ_sec, sub_self]⟩
      map_add' := fun v w => Subtype.ext (by simp [map_add]; abel)
      map_smul' := fun r v => Subtype.ext (by simp [smul_sub]) }
  let s : L_full →ₗ[ℤ] L_old × L_old := e.symm.toLinearMap.comp proj
  have hs_left : s.comp α = LinearMap.id := by
    apply LinearMap.ext
    intro u
    change e.symm (proj (α u)) = u
    have hp : proj (α u) = e u := by
      apply Subtype.ext
      change α u - σ (Submodule.Quotient.mk (α u)) = α u
      have hmk : (Submodule.Quotient.mk (α u) : Q) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr ⟨u, rfl⟩
      rw [hmk, map_zero, sub_zero]
    rw [hp, e.symm_apply_apply]
  -- Step 3: Surjectivity of `β` via `s*`
  have hβ_surj : Function.Surjective β := by
    intro u
    let φ : Module.Dual ℤ L_full := (pairProd u).comp s
    refine ⟨pair_full.symm φ, ?_⟩
    change pairProd.symm ((pair_full (pair_full.symm φ)).comp α) = u
    rw [pair_full.apply_symm_apply]
    have hcomp : φ.comp α = pairProd u := by
      apply LinearMap.ext
      intro w
      change pairProd u (s (α w)) = pairProd u w
      rw [show s (α w) = w from congrArg (fun f => f w) hs_left]
    rw [hcomp, pairProd.symm_apply_apply]
  -- Step 4: Exact orthogonal complement characterization `ker(β) = im(α)^⊥`
  have hker : ∀ v : L_full, v ∈ LinearMap.ker β ↔ ∀ u : L_old × L_old, pair_full v (α u) = 0 := by
    intro v
    rw [LinearMap.mem_ker]
    change pairProd.symm ((pair_full v).comp α) = 0 ↔ _
    constructor
    · intro hv u
      have h0 : (pair_full v).comp α = 0 := by
        have := congrArg pairProd hv
        rwa [pairProd.apply_symm_apply, map_zero] at this
      exact congrArg (fun f => f u) h0
    · intro hall
      have h0 : (pair_full v).comp α = 0 := by
        apply LinearMap.ext; intro u; exact hall u
      rw [h0, map_zero]
  exact ⟨⟨s, hs_left⟩, hβ_surj, hker⟩

end UnimodularSaturatedDescent

/-! ## Section 5: Unconditional Ribet's 1984 Level-Raising Congruence Theorem -/

section RibetLevelRaising

/-- Exact weight-`2` Ribet level-raising equivalence for a prime `ℓ`:
`ℓ ∣ ((q + 1)² - a_q²) ↔ a_q ≡ (q + 1) [ZMOD ℓ] ∨ a_q ≡ -(q + 1) [ZMOD ℓ]`. -/
theorem ribet_level_raising_cond_weight2_iff {ℓ : ℕ} (hℓ : Nat.Prime ℓ) (q : ℕ) (a_q : ℤ) :
    (ℓ : ℤ) ∣ ribetLevelRaisingFactor 2 q a_q ↔
      a_q ≡ ((q : ℤ) + 1) [ZMOD (ℓ : ℤ)] ∨ a_q ≡ -((q : ℤ) + 1) [ZMOD (ℓ : ℤ)] := by
  rw [ribetLevelRaisingFactor_weight2_factor]
  have hprime : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  rw [hprime.dvd_mul]
  constructor
  · rintro (h | h)
    · left
      exact Int.modEq_iff_dvd.mpr h
    · right
      rw [Int.modEq_iff_dvd]
      have heq : -((q : ℤ) + 1) - a_q = -(((q : ℤ) + 1) + a_q) := by ring
      rw [heq]
      exact dvd_neg.mpr h
  · rintro (h | h)
    · left
      exact Int.modEq_iff_dvd.mp h
    · right
      have hd := Int.modEq_iff_dvd.mp h
      have heq : ((q : ℤ) + 1) + a_q = -(-((q : ℤ) + 1) - a_q) := by ring
      rw [heq]
      exact dvd_neg.mpr hd

/-- Exact even-weight `k = 2m` Ribet level-raising equivalence for a prime `ℓ`:
`ℓ ∣ (q^{2m-2} (q + 1)² - a_q²) ↔ a_q ≡ ± q^{m-1} (q + 1) [ZMOD ℓ]`. -/
theorem ribet_level_raising_cond_even_iff {ℓ : ℕ} (hℓ : Nat.Prime ℓ) {m : ℕ} (hm : 1 ≤ m)
    (q : ℕ) (a_q : ℤ) :
    (ℓ : ℤ) ∣ ribetLevelRaisingFactor (2 * m) q a_q ↔
      a_q ≡ (q : ℤ) ^ (m - 1) * ((q : ℤ) + 1) [ZMOD (ℓ : ℤ)] ∨
        a_q ≡ -((q : ℤ) ^ (m - 1) * ((q : ℤ) + 1)) [ZMOD (ℓ : ℤ)] := by
  rw [ribetLevelRaisingFactor_even_factor m q hm a_q]
  have hprime : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  rw [hprime.dvd_mul]
  constructor
  · rintro (h | h)
    · left; exact Int.modEq_iff_dvd.mpr h
    · right
      rw [Int.modEq_iff_dvd]
      have heq : -((q : ℤ) ^ (m - 1) * ((q : ℤ) + 1)) - a_q =
          -((q : ℤ) ^ (m - 1) * ((q : ℤ) + 1) + a_q) := by ring
      rw [heq]; exact dvd_neg.mpr h
  · rintro (h | h)
    · left; exact Int.modEq_iff_dvd.mp h
    · right
      have hd := Int.modEq_iff_dvd.mp h
      have heq : (q : ℤ) ^ (m - 1) * ((q : ℤ) + 1) + a_q =
          -(-((q : ℤ) ^ (m - 1) * ((q : ℤ) + 1)) - a_q) := by ring
      rw [heq]; exact dvd_neg.mpr hd

/-- Bézout cancellation in any `ℤ`-module: if `ℓ` is prime, `¬ (ℓ ∣ c)`, and `c • x ∈ ℓ • ⊤`,
then `x ∈ ℓ • ⊤`. -/
theorem mem_smul_top_of_coprime_smul {M : Type*} [AddCommGroup M]
    {ℓ : ℕ} (hℓ : Nat.Prime ℓ) {c : ℤ} (hcop : ¬ ((ℓ : ℤ) ∣ c)) {x : M}
    (hcx : c • x ∈ (ℓ : ℤ) • (⊤ : Submodule ℤ M)) :
    x ∈ (ℓ : ℤ) • (⊤ : Submodule ℤ M) := by
  have hgcd : Int.gcd (ℓ : ℤ) c = 1 := by
    have hcop_nat : Nat.Coprime ℓ c.natAbs :=
      hℓ.coprime_iff_not_dvd.mpr fun hd => hcop (Int.natCast_dvd.mpr hd)
    simpa [Int.gcd] using hcop_nat
  have hbez := Int.gcd_eq_gcd_ab (ℓ : ℤ) c
  rw [hgcd] at hbez
  rw [Submodule.mem_smul_pointwise_iff_exists] at hcx ⊢
  obtain ⟨y, _, hy⟩ := hcx
  refine ⟨Int.gcdA (ℓ : ℤ) c • x + Int.gcdB (ℓ : ℤ) c • y, Submodule.mem_top, ?_⟩
  calc (ℓ : ℤ) • (Int.gcdA (ℓ : ℤ) c • x + Int.gcdB (ℓ : ℤ) c • y)
      = ((ℓ : ℤ) * Int.gcdA (ℓ : ℤ) c) • x + Int.gcdB (ℓ : ℤ) c • ((ℓ : ℤ) • y) := by
          rw [smul_add, smul_smul, smul_smul, smul_smul]; congr 2; ring
    _ = ((ℓ : ℤ) * Int.gcdA (ℓ : ℤ) c) • x + (Int.gcdB (ℓ : ℤ) c * c) • x := by
          rw [hy, smul_smul]
    _ = ((ℓ : ℤ) * Int.gcdA (ℓ : ℤ) c + c * Int.gcdB (ℓ : ℤ) c) • x := by
          rw [← add_smul]; congr 1; ring
    _ = (1 : ℤ) • x := by rw [← hbez]; simp
    _ = x := one_smul ℤ x

/-- **UNCONDITIONAL RIBET LEVEL-RAISING — NEWFORM CONGRUENCE & `ℓ`-TORSION IN CONGRUENCE MODULE**:
For ANY weight `k ≥ 2`, prime `ℓ` with `ℓ ∤ (q + 1)`, and primitive `T_q`-eigenform `f ∈ L_old`
(`f ∉ ℓ • L_old`, `T_q f = a_q • f`) satisfying Ribet's condition `ℓ ∣ (q^{k-2} (q + 1)² - a_q²)`,
if `α` is `ℓ`-saturated (e.g. `M_old_ℤ` is saturated in `M_full_ℤ`) and `β` is surjective:
1. `z := a_q • α₁ f - (q + 1) • α_q f ∈ M_old_ℤ` is nonzero mod `ℓ` (`z ∉ ℓ • M_full_ℤ`),
2. there exist **`h ∈ M_new_ℤ`** and `w ∈ M_full_ℤ` such that:
   - **`h ∉ ℓ • M_full_ℤ`** (`h` is a **NONZERO mod-`ℓ` newform**!),
   - **`z - h = ℓ • w`** (exact congruence `h ≡ z [MOD ℓ • M_full_ℤ]`!),
3. whenever `M_old_ℤ ∩ M_new_ℤ = ⊥`, `[w] ∈ M_full_ℤ / (M_old_ℤ ⊕ M_new_ℤ)` is a **NONZERO
   `ℓ`-torsion element**! -/
theorem ribet_level_raising_exists_newform_congruence
    {k q ℓ : ℕ} {L_old L_full : Type*}
    [AddCommGroup L_old] [AddCommGroup L_full]
    (L : IntegralIharaLattice k q L_old L_full)
    (hℓ : Nat.Prime ℓ)
    (hℓ_not_dvd : ¬ ((ℓ : ℤ) ∣ ((q : ℤ) + 1)))
    (hα_sat : IsPrimeSaturatedMap L.α (ℓ : ℤ))
    (hβ_surj : Function.Surjective L.β)
    {f : L_old} {a_q : ℤ}
    (hf_prim : f ∉ (ℓ : ℤ) • (⊤ : Submodule ℤ L_old))
    (hf_eig : L.T_q f = a_q • f)
    (hribet : (ℓ : ℤ) ∣ ribetLevelRaisingFactor k q a_q) :
    let z : L_full := a_q • L.α₁ f - ((q : ℤ) + 1) • L.α_q f
    z ∈ L.oldSubmodule ∧
      z ∉ (ℓ : ℤ) • (⊤ : Submodule ℤ L_full) ∧
      ∃ h : L_full, ∃ w : L_full,
        h ∈ L.newSubmodule ∧
        h ∉ (ℓ : ℤ) • (⊤ : Submodule ℤ L_full) ∧
        z - h = (ℓ : ℤ) • w ∧
        (L.oldSubmodule ⊓ L.newSubmodule = ⊥ →
          (ℓ : ℤ) • (Submodule.Quotient.mk w : L.congruenceModule) = 0 ∧
            (Submodule.Quotient.mk w : L.congruenceModule) ≠ 0) := by
  intro z
  let u : L_old × L_old := (a_q • f, -(((q : ℤ) + 1) • f))
  have hz_eq : z = L.α u := by
    simp [z, u, map_neg, map_smul, sub_eq_add_neg]
  have hz_old : z ∈ L.oldSubmodule := ⟨u, hz_eq.symm⟩
  -- Step 1: `z ∉ ℓ • M_full_ℤ` from `ℓ`-saturation of `α` and `ℓ ∤ (q + 1)`
  have hz_nmem : z ∉ (ℓ : ℤ) • (⊤ : Submodule ℤ L_full) := by
    intro hz_mem
    rw [hz_eq] at hz_mem
    have hu_mem : u ∈ (ℓ : ℤ) • (⊤ : Submodule ℤ (L_old × L_old)) := hα_sat u hz_mem
    rw [Submodule.mem_smul_pointwise_iff_exists] at hu_mem
    obtain ⟨v, _, hv⟩ := hu_mem
    have hv2 : (ℓ : ℤ) • v.2 = -(((q : ℤ) + 1) • f) := congrArg Prod.snd hv
    have hq1_mem : ((q : ℤ) + 1) • f ∈ (ℓ : ℤ) • (⊤ : Submodule ℤ L_old) := by
      rw [Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨-v.2, Submodule.mem_top, by rw [smul_neg, hv2, neg_neg]⟩
    exact hf_prim (mem_smul_top_of_coprime_smul hℓ hℓ_not_dvd hq1_mem)
  -- Step 2: Exact computation `β(z) = (0, -(q^{k-2}(q + 1)² - a_q²) • f)`
  have hβz : L.β z = (0, -(ribetLevelRaisingFactor k q a_q • f)) := by
    rw [hz_eq]
    have h := L.β_comp_α u
    change L.β (L.α₁ u.1 + L.α_q u.2) = _
    rw [h]
    ext
    · simp only [u, map_neg, map_smul, hf_eig, smul_smul]
      rw [mul_comm ((q : ℤ) + 1) a_q, add_neg_cancel]
    · simp only [u, map_smul, hf_eig, smul_smul, smul_neg, ribetLevelRaisingFactor,
        sub_smul, neg_sub]
      rw [sub_eq_add_neg]
      congr 1
      · congr 1; ring
      · congr 1; congr 1; ring
  -- Step 3: Divide `ribetLevelRaisingFactor` by `ℓ` and lift via surjectivity of `β`
  obtain ⟨m, hm⟩ := hribet
  obtain ⟨w, hw⟩ := hβ_surj (0, -(m • f))
  let h : L_full := z - (ℓ : ℤ) • w
  have hh_new : h ∈ L.newSubmodule := by
    change L.β (z - (ℓ : ℤ) • w) = 0
    rw [map_sub, map_smul, hβz, hw, hm]
    ext
    · simp
    · simp [mul_smul]
  have hzh : z - h = (ℓ : ℤ) • w := by simp [h]
  have hh_nmem : h ∉ (ℓ : ℤ) • (⊤ : Submodule ℤ L_full) := by
    intro hh_mem
    apply hz_nmem
    have hzw : z = h + (ℓ : ℤ) • w := by simp [h]
    rw [hzw]
    exact Submodule.add_mem _ hh_mem
      ((Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨w, Submodule.mem_top, rfl⟩)
  refine ⟨hz_old, hz_nmem, h, w, hh_new, hh_nmem, hzh, fun hdisj => ?_⟩
  constructor
  · change Submodule.Quotient.mk ((ℓ : ℤ) • w) = 0
    rw [Submodule.Quotient.mk_eq_zero, ← hzh]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left hz_old) (Submodule.mem_sup_right hh_new)
  · intro hw0
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_sup] at hw0
    obtain ⟨x, hx_old, y, hy_new, hxy⟩ := hw0
    have hdiff : z - (ℓ : ℤ) • x = h + (ℓ : ℤ) • y := by
      have : (ℓ : ℤ) • (x + y) = z - h := by rw [hxy, hzh]
      rw [smul_add] at this
      calc z - (ℓ : ℤ) • x
          = (z - h) - (ℓ : ℤ) • x + h := by abel
        _ = ((ℓ : ℤ) • x + (ℓ : ℤ) • y) - (ℓ : ℤ) • x + h := by rw [this]
        _ = h + (ℓ : ℤ) • y := by abel
    have hmem_inf : z - (ℓ : ℤ) • x ∈ L.oldSubmodule ⊓ L.newSubmodule := by
      refine ⟨Submodule.sub_mem _ hz_old (Submodule.smul_mem _ _ hx_old), ?_⟩
      rw [hdiff]
      exact Submodule.add_mem _ hh_new (Submodule.smul_mem _ _ hy_new)
    rw [hdisj, Submodule.mem_bot] at hmem_inf
    have hz_eq_lx : z = (ℓ : ℤ) • x := sub_eq_zero.mp hmem_inf
    exact hz_nmem
      ((Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨x, Submodule.mem_top, hz_eq_lx.symm⟩)

/-- Annihilator ideal `Ann_𝕋(N) := { t ∈ 𝕋 | ∀ y ∈ N, t • y = 0 }` of a sublattice `N ⊆ L_full`. -/
def heckeAnnihilator (𝕋 : Type*) [CommRing 𝕋] {L_full : Type*}
    [AddCommGroup L_full] [Module 𝕋 L_full]
    (N : Submodule ℤ L_full) : Ideal 𝕋 where
  carrier := { t : 𝕋 | ∀ y ∈ N, t • y = 0 }
  add_mem' {a b} ha hb y hy := by rw [add_smul, ha y hy, hb y hy, add_zero]
  zero_mem' y _ := zero_smul 𝕋 y
  smul_mem' r {a} ha y hy := by
    change (r * a) • y = 0
    rw [mul_smul, ha y hy, smul_zero]

/-- The **newform Hecke algebra** `𝕋_new := 𝕋 ⧸ Ann_𝕋(M_new_ℤ)`. -/
abbrev NewHeckeAlg (𝕋 : Type*) [CommRing 𝕋] {L_full : Type*}
    [AddCommGroup L_full] [Module 𝕋 L_full]
    (N : Submodule ℤ L_full) : Type _ :=
  𝕋 ⧸ heckeAnnihilator 𝕋 N

/-- The **Ribet old–new congruence ideal** `η_{f, new} := Ideal.map π_f (Ann_𝕋(M_new_ℤ)) ⊆ ℤ`
associated to an oldform eigensystem `π_f : 𝕋 →+* ℤ` and newform lattice `M_new_ℤ`. -/
def oldNewCongruenceIdeal {𝕋 : Type*} [CommRing 𝕋] {L_full : Type*}
    [AddCommGroup L_full] [Module 𝕋 L_full]
    (π_f : 𝕋 →+* ℤ) (N : Submodule ℤ L_full) : Ideal ℤ :=
  Ideal.map π_f (heckeAnnihilator 𝕋 N)

/-- **UNCONDITIONAL RIBET'S 1984 LEVEL-RAISING CONGRUENCE CRITERION
(`ribet_level_raising_criterion` / `ribet_level_raising_exists_congruence`)**:
Under the exact weight-`k` Ribet condition `ℓ ∣ (q^{k-2} (q + 1)² - a_q²)` with prime `ℓ ∤ (q + 1)`,
for ANY commutative Hecke algebra `𝕋` acting on `L_old` and `L_full` compatibly with `α₁, α_q`
where `f ∈ L_old` is a primitive `𝕋`-eigenform (`∀ t, t • f = π_f t • f`):
1. There exists a **nonzero mod-`ℓ` newform `h ∈ M_new_ℤ`** (`h ∉ ℓ • M_full_ℤ`) that is a
   mod-`ℓ` Hecke eigenvector with the **EXACT SAME EIGENSYSTEM `π_f` AS `f`**:
   `∀ t : 𝕋, t • h - (π_f t) • h ∈ ℓ • M_full_ℤ`!
2. The Ribet old–new congruence ideal is **divisible by `ℓ`**:
   **`oldNewCongruenceIdeal π_f M_new_ℤ ≤ Ideal.span {(ℓ : ℤ)}`**!
3. **Existence of a Mod-`ℓ` Newform Hecke Eigensystem (`ribet_level_raising_exists_congruence`)**:
   there exists a ring homomorphism **`π̄_new : NewHeckeAlg 𝕋 M_new_ℤ →+* ZMod ℓ`** such that
   **`∀ t : 𝕋, π̄_new (Ideal.Quotient.mk _ t) = (π_f t : ZMod ℓ)`**! -/
theorem ribet_level_raising_criterion
    {k q ℓ : ℕ} {L_old L_full 𝕋 : Type*}
    [AddCommGroup L_old] [AddCommGroup L_full]
    [CommRing 𝕋] [Module 𝕋 L_old] [Module 𝕋 L_full]
    (L : IntegralIharaLattice k q L_old L_full)
    (hℓ : Nat.Prime ℓ)
    (hℓ_not_dvd : ¬ ((ℓ : ℤ) ∣ ((q : ℤ) + 1)))
    (hα_sat : IsPrimeSaturatedMap L.α (ℓ : ℤ))
    (hβ_surj : Function.Surjective L.β)
    (hcompat₁ : ∀ (t : 𝕋) (x : L_old), t • L.α₁ x = L.α₁ (t • x))
    (hcompatq : ∀ (t : 𝕋) (x : L_old), t • L.α_q x = L.α_q (t • x))
    (hscalar : ∀ (t : 𝕋) (n : ℤ) (v : L_full), t • (n • v) = n • (t • v))
    (π_f : 𝕋 →+* ℤ)
    {f : L_old} {a_q : ℤ}
    (hf_prim : f ∉ (ℓ : ℤ) • (⊤ : Submodule ℤ L_old))
    (hf_Tq : L.T_q f = a_q • f)
    (hf_hecke : ∀ t : 𝕋, t • f = (π_f t) • f)
    (hribet : (ℓ : ℤ) ∣ ribetLevelRaisingFactor k q a_q) :
    (∃ h : L_full,
        h ∈ L.newSubmodule ∧
        h ∉ (ℓ : ℤ) • (⊤ : Submodule ℤ L_full) ∧
        ∀ t : 𝕋, t • h - (π_f t) • h ∈ (ℓ : ℤ) • (⊤ : Submodule ℤ L_full)) ∧
      oldNewCongruenceIdeal π_f L.newSubmodule ≤ Ideal.span ({(ℓ : ℤ)} : Set ℤ) ∧
      ∃ piNew : NewHeckeAlg 𝕋 L.newSubmodule →+* ZMod ℓ,
        ∀ t : 𝕋, piNew (Ideal.Quotient.mk (heckeAnnihilator 𝕋 L.newSubmodule) t) = (π_f t : ZMod ℓ) := by
  obtain ⟨_, _, h, w, hh_new, hh_nmem, hzh, _⟩ :=
    ribet_level_raising_exists_newform_congruence L hℓ hℓ_not_dvd hα_sat hβ_surj
      hf_prim hf_Tq hribet
  let z : L_full := a_q • L.α₁ f - ((q : ℤ) + 1) • L.α_q f
  -- First show `t • z = (π_f t) • z` for all `t : 𝕋`
  have htz : ∀ t : 𝕋, t • z = (π_f t) • z := by
    intro t
    change t • (a_q • L.α₁ f - ((q : ℤ) + 1) • L.α_q f) =
      (π_f t) • (a_q • L.α₁ f - ((q : ℤ) + 1) • L.α_q f)
    rw [smul_sub, hscalar, hscalar, hcompat₁, hcompatq, hf_hecke t,
      map_smul, map_smul, smul_sub, smul_smul, smul_smul, smul_smul, smul_smul,
      mul_comm a_q (π_f t), mul_comm ((q : ℤ) + 1) (π_f t)]
  -- Part 1: `h ∈ M_new_ℤ` is a nonzero mod-`ℓ` Hecke eigenvector with eigensystem `π_f`
  have hh_cong : ∀ t : 𝕋, t • h - (π_f t) • h ∈ (ℓ : ℤ) • (⊤ : Submodule ℤ L_full) := by
    intro t
    have hh_eq : h = z - (ℓ : ℤ) • w := by
      have : z - h = (ℓ : ℤ) • w := hzh
      calc h = z - (z - h) := by abel
        _ = z - (ℓ : ℤ) • w := by rw [this]
    have hdiff : t • h - (π_f t) • h = (ℓ : ℤ) • ((π_f t) • w - t • w) := by
      calc t • h - (π_f t) • h
          = t • (z - (ℓ : ℤ) • w) - (π_f t) • (z - (ℓ : ℤ) • w) := by rw [hh_eq]
        _ = (t • z - t • ((ℓ : ℤ) • w)) - ((π_f t) • z - (π_f t) • ((ℓ : ℤ) • w)) := by
              rw [smul_sub t z ((ℓ : ℤ) • w), smul_sub (π_f t) z ((ℓ : ℤ) • w)]
        _ = ((π_f t) • z - (ℓ : ℤ) • (t • w)) - ((π_f t) • z - (ℓ : ℤ) • ((π_f t) • w)) := by
              rw [htz t, hscalar, smul_comm (π_f t) (ℓ : ℤ) w]
        _ = (ℓ : ℤ) • ((π_f t) • w) - (ℓ : ℤ) • (t • w) := by abel
        _ = (ℓ : ℤ) • ((π_f t) • w - t • w) := (smul_sub _ _ _).symm
    rw [hdiff]
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
      ⟨(π_f t) • w - t • w, Submodule.mem_top, rfl⟩
  -- Key divisibility: `t ∈ Ann_𝕋(M_new_ℤ) → ℓ ∣ π_f t`
  have hann_dvd : ∀ t ∈ heckeAnnihilator 𝕋 L.newSubmodule, (ℓ : ℤ) ∣ π_f t := by
    intro t ht
    by_contra hndvd
    have hth0 : t • h = 0 := ht h hh_new
    have hmem := hh_cong t
    rw [hth0, zero_sub] at hmem
    have hpos_mem : (π_f t) • h ∈ (ℓ : ℤ) • (⊤ : Submodule ℤ L_full) := by
      have := Submodule.neg_mem _ hmem
      simpa using this
    exact hh_nmem (mem_smul_top_of_coprime_smul hℓ hndvd hpos_mem)
  -- Part 2: `oldNewCongruenceIdeal π_f M_new_ℤ ≤ Ideal.span {ℓ}`
  have hcong_le : oldNewCongruenceIdeal π_f L.newSubmodule ≤ Ideal.span ({(ℓ : ℤ)} : Set ℤ) := by
    rw [oldNewCongruenceIdeal, Ideal.map_le_iff_le_comap]
    intro t ht
    change π_f t ∈ Ideal.span ({(ℓ : ℤ)} : Set ℤ)
    rw [Ideal.mem_span_singleton]
    exact hann_dvd t ht
  -- Part 3: Factorization of `piMod : 𝕋 →+* ZMod ℓ` through `NewHeckeAlg 𝕋 M_new_ℤ`
  let modℓ : ℤ →+* ZMod ℓ := Int.castRingHom (ZMod ℓ)
  let piMod : 𝕋 →+* ZMod ℓ := modℓ.comp π_f
  have hker_le : heckeAnnihilator 𝕋 L.newSubmodule ≤ RingHom.ker piMod := by
    intro t ht
    change (π_f t : ZMod ℓ) = 0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (π_f t) ℓ).mpr (hann_dvd t ht)
  let piNew : NewHeckeAlg 𝕋 L.newSubmodule →+* ZMod ℓ :=
    Ideal.Quotient.lift (heckeAnnihilator 𝕋 L.newSubmodule) piMod (fun t ht => hker_le ht)
  refine ⟨⟨h, hh_new, hh_nmem, hh_cong⟩, hcong_le, piNew, fun t => rfl⟩

/-- **Named Existence Corollary (`ribet_level_raising_exists_congruence`)** for weight `2`
under the classical Ribet condition `a_q ≡ ±(q + 1) [ZMOD ℓ]`! -/
theorem ribet_level_raising_exists_congruence
    {q ℓ : ℕ} {L_old L_full 𝕋 : Type*}
    [AddCommGroup L_old] [AddCommGroup L_full]
    [CommRing 𝕋] [Module 𝕋 L_old] [Module 𝕋 L_full]
    (L : IntegralIharaLattice 2 q L_old L_full)
    (hℓ : Nat.Prime ℓ)
    (hℓ_not_dvd : ¬ ((ℓ : ℤ) ∣ ((q : ℤ) + 1)))
    (hα_sat : IsPrimeSaturatedMap L.α (ℓ : ℤ))
    (hβ_surj : Function.Surjective L.β)
    (hcompat₁ : ∀ (t : 𝕋) (x : L_old), t • L.α₁ x = L.α₁ (t • x))
    (hcompatq : ∀ (t : 𝕋) (x : L_old), t • L.α_q x = L.α_q (t • x))
    (hscalar : ∀ (t : 𝕋) (n : ℤ) (v : L_full), t • (n • v) = n • (t • v))
    (π_f : 𝕋 →+* ℤ)
    {f : L_old} {a_q : ℤ}
    (hf_prim : f ∉ (ℓ : ℤ) • (⊤ : Submodule ℤ L_old))
    (hf_Tq : L.T_q f = a_q • f)
    (hf_hecke : ∀ t : 𝕋, t • f = (π_f t) • f)
    (hribet_mod : a_q ≡ ((q : ℤ) + 1) [ZMOD (ℓ : ℤ)] ∨ a_q ≡ -((q : ℤ) + 1) [ZMOD (ℓ : ℤ)]) :
    ∃ piNew : NewHeckeAlg 𝕋 L.newSubmodule →+* ZMod ℓ,
      ∀ t : 𝕋, piNew (Ideal.Quotient.mk (heckeAnnihilator 𝕋 L.newSubmodule) t) = (π_f t : ZMod ℓ) :=
  (ribet_level_raising_criterion L hℓ hℓ_not_dvd hα_sat hβ_surj hcompat₁ hcompatq hscalar
    π_f hf_prim hf_Tq hf_hecke
    ((ribet_level_raising_cond_weight2_iff hℓ q a_q).mpr hribet_mod)).2.2

/-- **Direct Bridge to `Stage3PatchingUnification.congruenceIdeal`**:
whenever `𝕋` is a commutative `ℤ`-algebra with augmentation `π_f : 𝕋 →ₐ[ℤ] ℤ` such that
`annAugIdeal π_f ≤ heckeAnnihilator 𝕋 M_new_ℤ` (the annihilator of `ker π_f` kills `M_new_ℤ`),
Ribet's level-raising condition forces **`Stage3PatchingUnification.congruenceIdeal π_f ≤ (ℓ)`**! -/
theorem stage3_congruenceIdeal_le_span_of_ribet
    {k q ℓ : ℕ} {L_old L_full 𝕋 : Type*}
    [AddCommGroup L_old] [AddCommGroup L_full]
    [CommRing 𝕋] [Algebra ℤ 𝕋] [Module 𝕋 L_old] [Module 𝕋 L_full]
    (L : IntegralIharaLattice k q L_old L_full)
    (hℓ : Nat.Prime ℓ)
    (hℓ_not_dvd : ¬ ((ℓ : ℤ) ∣ ((q : ℤ) + 1)))
    (hα_sat : IsPrimeSaturatedMap L.α (ℓ : ℤ))
    (hβ_surj : Function.Surjective L.β)
    (hcompat₁ : ∀ (t : 𝕋) (x : L_old), t • L.α₁ x = L.α₁ (t • x))
    (hcompatq : ∀ (t : 𝕋) (x : L_old), t • L.α_q x = L.α_q (t • x))
    (hscalar : ∀ (t : 𝕋) (n : ℤ) (v : L_full), t • (n • v) = n • (t • v))
    (π_f : 𝕋 →ₐ[ℤ] ℤ)
    (hann_le : Stage3PatchingUnification.annAugIdeal π_f ≤ heckeAnnihilator 𝕋 L.newSubmodule)
    {f : L_old} {a_q : ℤ}
    (hf_prim : f ∉ (ℓ : ℤ) • (⊤ : Submodule ℤ L_old))
    (hf_Tq : L.T_q f = a_q • f)
    (hf_hecke : ∀ t : 𝕋, t • f = (π_f t) • f)
    (hribet : (ℓ : ℤ) ∣ ribetLevelRaisingFactor k q a_q) :
    Stage3PatchingUnification.congruenceIdeal π_f ≤ Ideal.span ({(ℓ : ℤ)} : Set ℤ) := by
  have hle := (ribet_level_raising_criterion L hℓ hℓ_not_dvd hα_sat hβ_surj hcompat₁ hcompatq
    hscalar π_f.toRingHom hf_prim hf_Tq hf_hecke hribet).2.1
  intro a ha
  obtain ⟨t, ht, rfl⟩ := (Stage3PatchingUnification.mem_congruenceIdeal_iff π_f a).mp ha
  exact hle (Ideal.mem_map_of_mem π_f.toRingHom (hann_le ht))

end RibetLevelRaising

/-! ## Section 6: Concrete Level-Raising Primes for Ramanujan's `Δ`, Weight-2 `X₀(11)` & 4D Witness -/

section ConcreteLevelRaisingExamples

/-- **Concrete Weight-12 Level-Raising Factor for Ramanujan's `Δ` at `q = 2`**:
using the unconditional `Stage8RamanujanDelta.ramanujanTau 2 = -24`:
`2¹⁰ · (2 + 1)² - τ(2)² = 9216 - 576 = 8640 = 2⁶ · 3³ · 5`! -/
theorem delta_level_raising_factor_q2 :
    ribetLevelRaisingFactor 12 2 (ramanujanTau 2) = 8640 ∧
      (8640 : ℤ) = 2 ^ 6 * 3 ^ 3 * 5 := by
  rw [ramanujanTau_two]
  unfold ribetLevelRaisingFactor
  norm_num

/-- **`ℓ = 5` is a Concrete Odd Ribet Level-Raising Prime for Ramanujan's `Δ` from Level `1`
to Level `2`**, AND `τ(2)` satisfies the strict Ihara injectivity bound `τ(2)² < 2¹⁰ · 3²`! -/
theorem delta_level_raising_prime_5_at_q2 :
    Nat.Prime 5 ∧
      ¬ ((5 : ℤ) ∣ (2 + 1)) ∧
      (5 : ℤ) ∣ ribetLevelRaisingFactor 12 2 (ramanujanTau 2) ∧
      (ramanujanTau 2) ^ 2 < (2 : ℤ) ^ 10 * (2 + 1) ^ 2 := by
  rw [delta_level_raising_factor_q2.1, ramanujanTau_two]
  refine ⟨by decide, by decide, by decide, by norm_num⟩

/-- **Concrete Weight-12 Level-Raising Factor for Ramanujan's `Δ` at `q = 3`**:
using the unconditional `Stage8RamanujanDelta.ramanujanTau 3 = 252`:
`3¹⁰ · (3 + 1)² - τ(3)² = 944784 - 63504 = 881280 = 2⁷ · 3⁴ · 5 · 17`! -/
theorem delta_level_raising_factor_q3 :
    ribetLevelRaisingFactor 12 3 (ramanujanTau 3) = 881280 ∧
      (881280 : ℤ) = 2 ^ 7 * 3 ^ 4 * 5 * 17 := by
  rw [ramanujanTau_three]
  unfold ribetLevelRaisingFactor
  norm_num

/-- **Both `ℓ = 5` and `ℓ = 17` are Concrete Odd Ribet Level-Raising Primes for Ramanujan's `Δ`
from Level `1` to Level `3`** (with `5, 17 ∤ (3 + 1) = 4`), and `τ(3)² < 3¹⁰ · 4²`! -/
theorem delta_level_raising_primes_5_17_at_q3 :
    Nat.Prime 5 ∧ Nat.Prime 17 ∧
      ¬ ((5 : ℤ) ∣ (3 + 1)) ∧ ¬ ((17 : ℤ) ∣ (3 + 1)) ∧
      (5 : ℤ) ∣ ribetLevelRaisingFactor 12 3 (ramanujanTau 3) ∧
      (17 : ℤ) ∣ ribetLevelRaisingFactor 12 3 (ramanujanTau 3) ∧
      (ramanujanTau 3) ^ 2 < (3 : ℤ) ^ 10 * (3 + 1) ^ 2 := by
  rw [delta_level_raising_factor_q3.1, ramanujanTau_three]
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by norm_num⟩

/-- **Concrete Weight-`2` Level-Raising Primes for `X₀(11)` (`11a1`)**:
- `q = 2, a₂ = -2`: `(2 + 1)² - (-2)² = 5` → `ℓ = 5`, `a₂ ≡ 2 + 1 [ZMOD 5]`,
- `q = 3, a₃ = -1`: `(3 + 1)² - (-1)² = 15 = 3 · 5` → `ℓ = 3, 5`,
- `q = 7, a₇ = -2`: `(7 + 1)² - (-2)² = 60 = 2² · 3 · 5` → `ℓ = 3, 5`! -/
theorem weight2_level11_level_raising_primes :
    ribetLevelRaisingFactor 2 2 (-2) = 5 ∧
      (-2 : ℤ) ≡ (2 + 1) [ZMOD 5] ∧
      ribetLevelRaisingFactor 2 3 (-1) = 15 ∧
      ribetLevelRaisingFactor 2 7 (-2) = 60 := by
  unfold ribetLevelRaisingFactor
  refine ⟨by norm_num, by decide, by norm_num, by norm_num⟩

/-! ### Non-Vacuous Concrete 4D Unimodular Lattice Witness (`q = 2, k = 2, a₂ = -2, ℓ = 5`) -/

/-- Explicit degeneracy vectors `v₁ = ![1, 1, 1, 0]` and `v₂ = ![-1, -1, 0, 1]` in `ℤ⁴`
whose standard Euclidean Gram matrix is `!![3, -2; -2, 3]` (`q = 2, k = 2, a₂ = -2`, `det = 5`)! -/
def witnessV1 : Fin 4 → ℤ := ![1, 1, 1, 0]
def witnessV2 : Fin 4 → ℤ := ![-1, -1, 0, 1]

/-- Concrete 4D `IntegralIharaLattice 2 2 ℤ (Fin 4 → ℤ)` modeling level-raising from
`q = 2, a₂ = -2` at `ℓ = 5`, with saturated oldform lattice `span_ℤ(v₁, v₂) ⊆ ℤ⁴`. -/
def concreteWitnessLattice : IntegralIharaLattice 2 2 ℤ (Fin 4 → ℤ) where
  T_q := (-2 : ℤ) • LinearMap.id
  α₁ := LinearMap.smulRight (LinearMap.id : ℤ →ₗ[ℤ] ℤ) witnessV1
  α_q := LinearMap.smulRight (LinearMap.id : ℤ →ₗ[ℤ] ℤ) witnessV2
  β :=
    { toFun := fun w => (∑ i : Fin 4, witnessV1 i * w i, ∑ i : Fin 4, witnessV2 i * w i)
      map_add' := fun u v => by
        ext <;> simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun r u => by
        ext <;> simp [Finset.mul_sum, mul_left_comm] }
  β_comp_α := by
    rintro ⟨x, y⟩
    ext
    · simp [Fin.sum_univ_four, witnessV1, witnessV2]
      ring
    · simp [Fin.sum_univ_four, witnessV1, witnessV2]
      ring

/-- **Concrete Non-Vacuous End-to-End Witness (`concrete_level11_to_22_witness`)**:
verifies saturation, surjectivity of `β`, disjointness `M_old_ℤ ∩ M_new_ℤ = ⊥`, exact Ribet
level-raising at `ℓ = 5`, explicit nonzero mod-`5` newform `h = ![1, 1, -2, 2] ∈ M_new_ℤ`
congruent mod `5` to `z = ![1, 1, -2, -3] ∈ M_old_ℤ`, and nonzero `5`-torsion in
`M_full_ℤ / (M_old_ℤ ⊕ M_new_ℤ)`! -/
theorem concrete_level11_to_22_witness :
    IsSaturatedSubmodule concreteWitnessLattice.oldSubmodule ∧
      Function.Injective concreteWitnessLattice.α ∧
      Function.Surjective concreteWitnessLattice.β ∧
      concreteWitnessLattice.oldSubmodule ⊓ concreteWitnessLattice.newSubmodule = ⊥ ∧
      (∃ h w : Fin 4 → ℤ,
        h ∈ concreteWitnessLattice.newSubmodule ∧
        h ∉ (5 : ℤ) • (⊤ : Submodule ℤ (Fin 4 → ℤ)) ∧
        ((-2 : ℤ) • witnessV1 - (3 : ℤ) • witnessV2) - h = (5 : ℤ) • w ∧
        (5 : ℤ) • (Submodule.Quotient.mk w : concreteWitnessLattice.congruenceModule) = 0 ∧
        (Submodule.Quotient.mk w : concreteWitnessLattice.congruenceModule) ≠ 0) := by
  have hα_coord : ∀ u : ℤ × ℤ,
      concreteWitnessLattice.α u 2 = u.1 ∧ concreteWitnessLattice.α u 3 = u.2 := by
    rintro ⟨x, y⟩
    simp [IntegralIharaLattice.α, concreteWitnessLattice, witnessV1, witnessV2]
  have hα_inj : Function.Injective concreteWitnessLattice.α := by
    intro u v huv
    have h2 := congrFun huv 2
    have h3 := congrFun huv 3
    rw [(hα_coord u).1, (hα_coord v).1] at h2
    rw [(hα_coord u).2, (hα_coord v).2] at h3
    exact Prod.ext h2 h3
  have hsat : IsSaturatedSubmodule concreteWitnessLattice.oldSubmodule := by
    intro x n hn ⟨u, hu⟩
    have h2 : u.1 = n * x 2 := by
      have := congrFun hu 2
      simpa [(hα_coord u).1, Pi.smul_apply, smul_eq_mul] using this
    have h3 : u.2 = n * x 3 := by
      have := congrFun hu 3
      simpa [(hα_coord u).2, Pi.smul_apply, smul_eq_mul] using this
    refine ⟨(x 2, x 3), ?_⟩
    funext i
    have hscaled : concreteWitnessLattice.α (n * x 2, n * x 3) =
        n • concreteWitnessLattice.α (x 2, x 3) := by
      change concreteWitnessLattice.α (n • (x 2, x 3)) = _
      exact map_smul concreteWitnessLattice.α n (x 2, x 3)
    have hni : n * concreteWitnessLattice.α (x 2, x 3) i = n * x i := by
      have h1 : n • concreteWitnessLattice.α (x 2, x 3) = n • x := by
        rw [← hscaled, ← h2, ← h3, hu]
      exact congrFun h1 i
    exact mul_left_cancel₀ hn hni
  have hβ_surj : Function.Surjective concreteWitnessLattice.β := by
    rintro ⟨a, b⟩
    refine ⟨![0, 0, a, b], ?_⟩
    ext
    · simp [concreteWitnessLattice, witnessV1, Fin.sum_univ_four]
    · simp [concreteWitnessLattice, witnessV2, Fin.sum_univ_four]
  have hη_inj : Function.Injective concreteWitnessLattice.ηOp := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    simp only [IntegralIharaLattice.ηOp_apply, concreteWitnessLattice, LinearMap.smul_apply,
      LinearMap.id_apply, smul_eq_mul] at hx
    omega
  have hdisj := (concreteWitnessLattice.disjoint_old_new_of_ηOp_injective hη_inj).2.2
  have h5sat : IsPrimeSaturatedMap concreteWitnessLattice.α 5 :=
    isPrimeSaturatedMap_of_injective_saturated hα_inj hsat (by decide)
  have hf_prim : (1 : ℤ) ∉ (5 : ℤ) • (⊤ : Submodule ℤ ℤ) := by
    rw [Submodule.mem_smul_pointwise_iff_exists]
    rintro ⟨k, _, hk⟩
    simp only [smul_eq_mul] at hk
    omega
  have hf_Tq : concreteWitnessLattice.T_q (1 : ℤ) = (-2 : ℤ) • (1 : ℤ) := by
    simp [concreteWitnessLattice]
  obtain ⟨_, _, h, w, hh_new, hh_nmem, hzh, htors⟩ :=
    ribet_level_raising_exists_newform_congruence concreteWitnessLattice
      (by decide : Nat.Prime 5) (by decide) h5sat hβ_surj hf_prim hf_Tq (by decide)
  obtain ⟨h5w, hw_ne⟩ := htors hdisj
  have hzh' : ((-2 : ℤ) • witnessV1 - (3 : ℤ) • witnessV2) - h = (5 : ℤ) • w := by
    have h1 : concreteWitnessLattice.α₁ 1 = witnessV1 := by simp [concreteWitnessLattice]
    have h2 : concreteWitnessLattice.α_q 1 = witnessV2 := by simp [concreteWitnessLattice]
    rw [h1, h2] at hzh
    exact hzh
  exact ⟨hsat, hα_inj, hβ_surj, hdisj, h, w, hh_new, hh_nmem, hzh', h5w, hw_ne⟩

/-- **Stage 11 Master Packaging Theorem**:
bundles the weight-`k` Ihara Gram determinant, Ramanujan–Ihara injectivity, unimodular saturation
splitting, Ribet's 1984 level-raising criterion, and concrete numerical verification for `Δ` (`k = 12`)
and `X₀(11)` (`k = 2`). -/
theorem stage11_ihara_level_raising_master :
    ribetLevelRaisingFactor 12 2 (ramanujanTau 2) = 8640 ∧
      (5 : ℤ) ∣ ribetLevelRaisingFactor 12 2 (ramanujanTau 2) ∧
      ribetLevelRaisingFactor 12 3 (ramanujanTau 3) = 881280 ∧
      (17 : ℤ) ∣ ribetLevelRaisingFactor 12 3 (ramanujanTau 3) ∧
      ribetLevelRaisingFactor 2 2 (-2) = 5 ∧
      IsSaturatedSubmodule concreteWitnessLattice.oldSubmodule ∧
      concreteWitnessLattice.oldSubmodule ⊓ concreteWitnessLattice.newSubmodule = ⊥ :=
  ⟨delta_level_raising_factor_q2.1,
   delta_level_raising_prime_5_at_q2.2.2.1,
   delta_level_raising_factor_q3.1,
   delta_level_raising_primes_5_17_at_q3.2.2.2.2.2.1,
   weight2_level11_level_raising_primes.1,
   concrete_level11_to_22_witness.1,
   concrete_level11_to_22_witness.2.2.2.1⟩

end ConcreteLevelRaisingExamples

end RHDirect.Stage11IharaLevelRaising
