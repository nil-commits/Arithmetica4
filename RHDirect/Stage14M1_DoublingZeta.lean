import RHDirect.Stage14M1_UnitaryGroupDef
import RHDirect.Stage14M1_SchrodingerFockModel
import RHDirect.Stage11DoublingRallis

/-!
# RHDirect.Stage14M1_DoublingZeta

Field-2 Package M1 Wave 2 (Module 3 of 5): **Doubled CM Hermitian Spaces `V^□ = V ⊕ (-V)`,
Adelic & Local Doubling Embeddings `U(V) × U(-V) ↪ U(V ⊕ -V)`, Piatetski-Shapiro–Rallis
Doubling Zeta Integrals, Unramified Local `L`-Factor Identities, and the Doubling Seesaw Fubini
Theorem** in pure Mathlib `v4.33.1` (`0` `sorry`, `0` custom `axiom`s, `0` `opaque`, `0` `native_decide`).

## Contents

1. **Concrete Doubled CM Hermitian Spaces (`DoubledHermSpace`) & Lagrangian Splitting**:
   - `DoubledHermSpace E F V` wrapping `H : HermSpaceCM E F V`, `H.doubled = H.directSum H.neg`,
     and complementary maximal totally isotropic Lagrangians `V^Δ` (`diagonalSubspace`) and
     `V^∇` (`antiDiagonalSubspace`).
   - Exact Gram matrix bridge `doubled_gram_eq_doubledForm` connecting `Stage14M1_UnitaryGroupDef`
     to `Stage11DoublingRallis.doubledForm`, determinant `doubled_gram_det`, signature `(dim, dim)`
     for positive-definite `H` (`DoubledHermSpace.indefiniteOfPosDef`), and Siegel parabolic
     stabilizer `siegelParabolicSubgroup` of `V^Δ`.

2. **Concrete Doubling Embeddings (`DoublingEmbedding`) Across All Levels**:
   - Coordinate-free isomorphism `unitaryGrpNegEquiv : UnitaryGrp H ≃* UnitaryGrp H.neg`,
     matrix equivalence `unitaryMatGrp_neg`, and injective embedding
     `doublingEmbeddingHom : UnitaryGrp H × UnitaryGrp H.neg →* UnitaryGrp H.doubled`.
   - Functorial matrix `R`-point embeddings `unitaryMatGrpDoubledEmbed` and
     `unitaryPtsDoubledEmbed`, instantiated at local finite (`unitaryLocalDoubledEmbed`),
     local archimedean (`unitaryArchDoubledEmbed`), finite-adelic
     (`unitaryFiniteAdelicDoubledEmbed`), and full adelic (`unitaryAdelicDoubledEmbed`)
     groups, with exact rational-embedding commutation (`doubledEmbed_ratToAdelic_comm`) and
     `CompactOpenLevel` compatibility (`stdMaximalLevel_doubled_compat`,
     `principalCongruence_doubled_compat`).

3. **Concrete Doubling Zeta Integrals (`DoublingZetaIntegral`) & Eigenform Factorization**:
   - `DoublingSiegelSection` wired to `Stage14M1_SchrodingerFockModel.siegelSection`,
     `DoublingZetaIntegral` (Bochner integral `∫_G ⟨φ₂, π(g) φ₁⟩ f_s(g) dμ_G` and discrete
     weighted genus pairing `autDoublingZeta`), inner-product bridge `doublingZetaIntegral_eq_inner`,
     unconditional Bochner integrability under Siegel-set / decay envelopes, product-measure
     factorization across places, Hecke commutation, and eigenform factorization.

4. **Exact Local Unramified Doubling `L`-Factor (`doubling_unramified_local_L_factor`)**:
   - Rank-`n` `U(n)` unramified local doubling identity at arbitrary prime powers `q_v`,
     analytic `GL₂` / `U(1,1)` Cartan–Macdonald double-coset series identity at any `q ≥ 2`,
     partial Euler product convergence (`doubling_partial_euler_product`) in the half-plane
     of absolute convergence, and limit-product factorization `doubling_limit_eq_prod_mul`.

5. **Piatetski-Shapiro–Rallis Doubling Seesaw Fubini (`doubling_seesaw_fubini`)**:
   - Twisted and untwisted doubling seesaw identities in weighted finite-genus, `EuclideanSpace`,
     and full Bochner-integral (`doubling_seesaw_fubini`, `doubling_seesaw_theta_mean`) settings,
     plus Rallis inner-product non-negativity (`doubling_seesaw_normSq_nonneg`), non-vanishing
     equivalence (`doubling_seesaw_ne_zero_iff`), and Wave-3 packaging (`DoublingZetaPackage`).
-/

noncomputable section

open Module Submodule Matrix TensorProduct NumberField IsDedekindDomain MeasureTheory Filter Finset
open RHDirect RHDirect.RallisSeesaw RHDirect.SiegelWeilCore
open RHDirect.Stage14M1_UnitaryGroupDef RHDirect.Stage14M1_SchrodingerFockModel
open RHDirect.Stage11DoublingRallis
open scoped BigOperators InnerProductSpace ComplexConjugate Topology NNReal

namespace RHDirect.Stage14M1_DoublingZeta

local instance instFactPrimePrimes (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-! ## Section 1: Concrete Doubled CM Hermitian Spaces (`DoubledHermSpace`) -/

section DoubledSpace

section MatrixReindexHelpers

private lemma matReindex_mul_self {m n R : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [NonUnitalNonAssocSemiring R]
    (e : m ≃ n) (A B : Matrix m m R) :
    A.reindex e e * B.reindex e e = (A * B).reindex e e := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply]
  exact Equiv.sum_comp e.symm (fun k => A (e.symm i) k * B k (e.symm j))

private lemma matReindex_one_self {m n R : Type*} [DecidableEq m] [DecidableEq n]
    [Zero R] [One R] (e : m ≃ n) :
    (1 : Matrix m m R).reindex e e = 1 := by
  ext i j
  simp [Matrix.one_apply]

private lemma conjTransposeMap_reindex {m n A : Type*} [CommRing A]
    (σ : A →+* A) (e : m ≃ n) (M : Matrix m m A) :
    conjTransposeMap σ (M.reindex e e) = (conjTransposeMap σ M).reindex e e := by
  ext i j
  rfl

private lemma matMap_reindex {m n A B : Type*} (f : A → B) (e : m ≃ n) (M : Matrix m m A) :
    (M.reindex e e).map f = (M.map f).reindex e e := by
  ext i j
  rfl

end MatrixReindexHelpers

section BasicInclusions

variable {E V : Type*} [CommRing E] [AddCommGroup V] [Module E V]

/-- Canonical `E`-linear inclusion of `V` onto the diagonal Lagrangian `V^Δ = {(v, v)} ⊆ V × V`. -/
def diagIncl (E V : Type*) [CommRing E] [AddCommGroup V] [Module E V] :
    V →ₗ[E] V × V where
  toFun v := (v, v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Canonical `E`-linear inclusion of `V` onto the anti-diagonal Lagrangian `V^∇ = {(v, -v)} ⊆ V × V`. -/
def antiDiagIncl (E V : Type*) [CommRing E] [AddCommGroup V] [Module E V] :
    V →ₗ[E] V × V where
  toFun v := (v, -v)
  map_add' x y := by ext <;> simp; abel
  map_smul' _ _ := by ext <;> simp [smul_neg]

@[simp]
lemma diagIncl_apply (v : V) : diagIncl E V v = (v, v) := rfl

@[simp]
lemma antiDiagIncl_apply (v : V) : antiDiagIncl E V v = (v, -v) := rfl

lemma diagIncl_injective : Function.Injective (diagIncl E V) := by
  intro x y h
  exact congrArg Prod.fst h

lemma antiDiagIncl_injective : Function.Injective (antiDiagIncl E V) := by
  intro x y h
  exact congrArg Prod.fst h

end BasicInclusions

section DoubledGeometry

variable {E F V : Type*}
  [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  [AddCommGroup V] [Module E V] [FiniteDimensional E V]

/-- Anti-diagonal Lagrangian subspace `V^∇ = {(v, -v) | v ∈ V} ⊆ V ⊕ (-V)`. -/
def antiDiagonalSubspace (_H : HermSpaceCM E F V) : Submodule E (V × V) where
  carrier := { p | p.2 = -p.1 }
  zero_mem' := by simp
  add_mem' := by
    intro a b (ha : a.2 = -a.1) (hb : b.2 = -b.1)
    change a.2 + b.2 = -(a.1 + b.1)
    rw [ha, hb]; abel
  smul_mem' := by
    intro c x (hx : x.2 = -x.1)
    change c • x.2 = -(c • x.1)
    rw [hx, smul_neg]

@[simp]
lemma mem_diagonalSubspace_iff (H : HermSpaceCM E F V) (p : V × V) :
    p ∈ H.diagonalSubspace ↔ p.1 = p.2 := Iff.rfl

@[simp]
lemma mem_antiDiagonalSubspace_iff (H : HermSpaceCM E F V) (p : V × V) :
    p ∈ antiDiagonalSubspace H ↔ p.2 = -p.1 := Iff.rfl

lemma diagIncl_mem_diagonal (H : HermSpaceCM E F V) (v : V) :
    diagIncl E V v ∈ H.diagonalSubspace := rfl

lemma antiDiagIncl_mem_antiDiagonal (H : HermSpaceCM E F V) (v : V) :
    antiDiagIncl E V v ∈ antiDiagonalSubspace H := rfl

/-- Total isotropy of the anti-diagonal subspace `V^∇` for the doubled Hermitian form `H.doubled`. -/
theorem doubled_form_antiDiagonal_eq_zero (H : HermSpaceCM E F V) {x y : V × V}
    (hx : x ∈ antiDiagonalSubspace H) (hy : y ∈ antiDiagonalSubspace H) :
    H.doubled.form x y = 0 := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  change x₂ = -x₁ at hx
  change y₂ = -y₁ at hy
  subst hx; subst hy
  simp [HermSpaceCM.doubled_form]

/-- Cross-pairing between the complementary Lagrangians `V^Δ` and `V^∇`:
`⟨(v, v), (w, -w)⟩_{V^□} = 2 · ⟨v, w⟩_V`. -/
theorem doubled_form_diag_antiDiag (H : HermSpaceCM E F V) (v w : V) :
    H.doubled.form (diagIncl E V v) (antiDiagIncl E V w) = 2 * H.form v w := by
  simp only [diagIncl_apply, antiDiagIncl_apply, HermSpaceCM.doubled_form, map_neg]
  ring

/-- In characteristic `0` (`NumberField E`), the doubled space splits as the direct sum
`V ⊕ (-V) = V^Δ ⊕ V^∇` of two complementary maximal totally isotropic subspaces. -/
theorem diagonal_antiDiagonal_compl (H : HermSpaceCM E F V) :
    IsCompl H.diagonalSubspace (antiDiagonalSubspace H) := by
  have h2 : (2 : E) ≠ 0 := two_ne_zero
  rw [isCompl_iff]
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff]
    ext p
    simp only [Submodule.mem_inf, mem_diagonalSubspace_iff, mem_antiDiagonalSubspace_iff,
      Submodule.mem_bot]
    constructor
    · rintro ⟨h1, h2p⟩
      have hsum : p.1 + p.1 = 0 := by
        calc p.1 + p.1 = p.1 + p.2 := by rw [← h1]
          _ = p.1 + (-p.1) := by rw [h2p]
          _ = 0 := add_neg_cancel _
      have h2smul : (2 : E) • p.1 = 0 := by
        simpa [two_smul] using hsum
      have hp1 : p.1 = 0 := (smul_eq_zero.mp h2smul).resolve_left h2
      have hp2 : p.2 = 0 := by rw [← h1, hp1]
      exact Prod.ext hp1 hp2
    · intro hp
      subst hp
      exact ⟨rfl, neg_zero.symm⟩
  · rw [codisjoint_iff, eq_top_iff']
    intro p
    let u : V := (2 : E)⁻¹ • (p.1 + p.2)
    let v : V := (2 : E)⁻¹ • (p.1 - p.2)
    have hp : p = diagIncl E V u + antiDiagIncl E V v := by
      ext
      · change p.1 = (2 : E)⁻¹ • (p.1 + p.2) + (2 : E)⁻¹ • (p.1 - p.2)
        rw [← smul_add]
        have hadd : (p.1 + p.2) + (p.1 - p.2) = (2 : E) • p.1 := by
          rw [two_smul]; abel
        rw [hadd, smul_smul, inv_mul_cancel₀ h2, one_smul]
      · change p.2 = (2 : E)⁻¹ • (p.1 + p.2) + -((2 : E)⁻¹ • (p.1 - p.2))
        rw [← smul_neg, ← smul_add]
        have hsub : (p.1 + p.2) + -(p.1 - p.2) = (2 : E) • p.2 := by
          rw [two_smul]; abel
        rw [hsub, smul_smul, inv_mul_cancel₀ h2, one_smul]
    rw [hp]
    exact Submodule.add_mem_sup (diagIncl_mem_diagonal H u) (antiDiagIncl_mem_antiDiagonal H v)

/-- Dimension of the diagonal Lagrangian `V^Δ` equals `H.dim`. -/
theorem finrank_diagonalSubspace (H : HermSpaceCM E F V) :
    Module.finrank E H.diagonalSubspace = H.dim := by
  let e : V ≃ₗ[E] H.diagonalSubspace :=
    { toFun := fun v => ⟨diagIncl E V v, diagIncl_mem_diagonal H v⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun p => p.1.1
      left_inv := fun _ => rfl
      right_inv := fun ⟨⟨x₁, x₂⟩, hx⟩ => by
        change x₁ = x₂ at hx
        ext <;> simp [hx] }
  rw [← e.finrank_eq, H.dim_eq]

/-- Dimension of the anti-diagonal Lagrangian `V^∇` equals `H.dim`. -/
theorem finrank_antiDiagonalSubspace (H : HermSpaceCM E F V) :
    Module.finrank E (antiDiagonalSubspace H) = H.dim := by
  let e : V ≃ₗ[E] antiDiagonalSubspace H :=
    { toFun := fun v => ⟨antiDiagIncl E V v, antiDiagIncl_mem_antiDiagonal H v⟩
      map_add' := fun x y => by ext <;> simp; abel
      map_smul' := fun c x => by ext <;> simp [smul_neg]
      invFun := fun p => p.1.1
      left_inv := fun _ => rfl
      right_inv := fun ⟨⟨x₁, x₂⟩, hx⟩ => by
        change x₂ = -x₁ at hx
        ext <;> simp [hx] }
  rw [← e.finrank_eq, H.dim_eq]

/-- Exact Gram matrix identity linking `HermSpaceCM.doubled.gram` to
`Stage11DoublingRallis.doubledForm H.gram`. -/
theorem doubled_gram_eq_doubledForm (H : HermSpaceCM E F V) :
    H.doubled.gram = (doubledForm H.gram).reindex finSumFinEquiv finSumFinEquiv := by
  change (H.directSum H.neg).gram = _
  rw [HermSpaceCM.directSum_gram, HermSpaceCM.neg_gram]
  rfl

/-- Exact determinant formula `det(gram(V^□)) = (-1)^{dim V} · det(gram(V))²`. -/
theorem doubled_gram_det (H : HermSpaceCM E F V) :
    H.doubled.gram.det = (-1 : E) ^ H.dim * H.gram.det ^ 2 := by
  have hdet : ((doubledForm H.gram).reindex finSumFinEquiv finSumFinEquiv).det =
      (-1 : E) ^ H.dim * H.gram.det ^ 2 := by
    rw [Matrix.det_reindex_self]
    unfold doubledForm
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg, Fintype.card_fin]
    ring
  have heq := congrArg Matrix.det (doubled_gram_eq_doubledForm H)
  exact heq.trans hdet

/-- **Concrete Doubled CM Hermitian Space `DoubledHermSpace E F V`**:
bundles a CM Hermitian space `base : HermSpaceCM E F V` with its doubled Hermitian space
`V^□ = V ⊕ (-V)` (`base.doubled`), Lagrangian splitting `V^Δ ⊕ V^∇`, and Gram/determinant data. -/
structure DoubledHermSpace (E F V : Type*)
    [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V] where
  base : HermSpaceCM E F V

namespace DoubledHermSpace

/-- Constructor from any CM Hermitian space `H : HermSpaceCM E F V`. -/
def ofHermSpace (H : HermSpaceCM E F V) : DoubledHermSpace E F V :=
  ⟨H⟩

/-- The underlying CM Hermitian space `V^□ = V ⊕ (-V)` on `V × V`. -/
abbrev space (D : DoubledHermSpace E F V) : HermSpaceCM E F (V × V) :=
  D.base.doubled

/-- The maximal totally isotropic diagonal Lagrangian `V^Δ = {(v, v)}`. -/
abbrev diagLagrangian (D : DoubledHermSpace E F V) : Submodule E (V × V) :=
  D.base.diagonalSubspace

/-- The complementary maximal totally isotropic anti-diagonal Lagrangian `V^∇ = {(v, -v)}`. -/
abbrev antiDiagLagrangian (D : DoubledHermSpace E F V) : Submodule E (V × V) :=
  antiDiagonalSubspace D.base

lemma dim_eq (D : DoubledHermSpace E F V) : D.space.dim = D.base.dim + D.base.dim := rfl

lemma finrank_eq (D : DoubledHermSpace E F V) :
    Module.finrank E (V × V) = 2 * D.base.dim := by
  rw [Module.finrank_prod, D.base.dim_eq, two_mul]

lemma gram_eq (D : DoubledHermSpace E F V) :
    D.space.gram = (doubledForm D.base.gram).reindex finSumFinEquiv finSumFinEquiv :=
  doubled_gram_eq_doubledForm D.base

lemma det_gram (D : DoubledHermSpace E F V) :
    D.space.gram.det = (-1 : E) ^ D.base.dim * D.base.gram.det ^ 2 :=
  doubled_gram_det D.base

lemma diag_antiDiag_compl (D : DoubledHermSpace E F V) :
    IsCompl D.diagLagrangian D.antiDiagLagrangian :=
  diagonal_antiDiagonal_compl D.base

/-- For any positive-definite CM Hermitian space `H` of positive dimension, `DoubledHermSpace`
realizes a concrete `IndefiniteHermSpace` of balanced signature `(dim, dim)`. -/
def indefiniteOfPosDef (D : DoubledHermSpace E F V)
    (hpos : D.base.IsPosDef) (hdim : 0 < D.base.dim) :
    IndefiniteHermSpace E F (V × V) :=
  IndefiniteHermSpace.ofDoubledPosDef D.base hpos hdim

end DoubledHermSpace

/-- The **Siegel parabolic subgroup** `P(V^Δ) ≤ U(V^□)` stabilizing the maximal isotropic
diagonal subspace `V^Δ`. -/
def siegelParabolicSubgroup (H : HermSpaceCM E F V) : Subgroup (UnitaryGrp H.doubled) where
  carrier := { g | ∀ x ∈ H.diagonalSubspace, g.1 x ∈ H.diagonalSubspace }
  one_mem' := fun _ hx => hx
  mul_mem' := fun {a b} ha hb x hx => ha _ (hb x hx)
  inv_mem' := by
    intro g hg x hx
    let res : H.diagonalSubspace →ₗ[E] H.diagonalSubspace :=
      { toFun := fun y => ⟨g.1 y.1, hg y.1 y.2⟩
        map_add' := fun y₁ y₂ => by ext <;> simp
        map_smul' := fun c y => by ext <;> simp }
    have hinj : LinearMap.ker res = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro y hy
      ext1
      exact g.1.injective (by simpa [res] using congrArg Subtype.val hy)
    have hsurj : LinearMap.range res = ⊤ :=
      LinearMap.range_eq_top.mpr
        ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
          (LinearMap.ker_eq_bot.mp hinj))
    have hx_top : (⟨x, hx⟩ : H.diagonalSubspace) ∈ LinearMap.range res := by
      rw [hsurj]; trivial
    rcases hx_top with ⟨y, hy⟩
    have hy_eq : g.1 y.1 = x := congrArg Subtype.val hy
    have hinv_eq : (g⁻¹).1 x = y.1 := by
      change g.1.symm x = y.1
      rw [← hy_eq, LinearEquiv.symm_apply_apply]
    rw [hinv_eq]
    exact y.2

end DoubledGeometry

end DoubledSpace

/-! ## Section 2: Concrete Doubling Embeddings (`DoublingEmbedding`) Across All Levels -/

section DoublingEmbeddings

section CoordinateFree

variable {E F V : Type*}
  [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  [AddCommGroup V] [Module E V] [FiniteDimensional E V]

/-- Canonical group isomorphism `U(V) ≃* U(-V)` (`UnitaryGrp H ≃* UnitaryGrp H.neg`). -/
def unitaryGrpNegEquiv (H : HermSpaceCM E F V) : UnitaryGrp H ≃* UnitaryGrp H.neg where
  toFun g := ⟨g.1, fun x y => by simp only [HermSpaceCM.neg_form, g.2 x y]⟩
  invFun g := ⟨g.1, fun x y => by
    have h := g.2 x y
    simp only [HermSpaceCM.neg_form, neg_inj] at h
    exact h⟩
  map_mul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
lemma unitaryGrpNegEquiv_apply (H : HermSpaceCM E F V) (g : UnitaryGrp H) :
    (unitaryGrpNegEquiv H g).1 = g.1 := rfl

/-- Coordinate-free doubling embedding `U(V) × U(-V) →* U(V ⊕ -V)`. -/
def doublingEmbeddingHom (H : HermSpaceCM E F V) :
    UnitaryGrp H × UnitaryGrp H.neg →* UnitaryGrp H.doubled where
  toFun p :=
    ⟨LinearEquiv.prodCongr p.1.1 p.2.1, fun x y => by
      simp only [HermSpaceCM.doubled_form, LinearEquiv.prodCongr_apply]
      have h1 : H.form (p.1.1 x.1) (p.1.1 y.1) = H.form x.1 y.1 := p.1.2 x.1 y.1
      have h2 : H.neg.form (p.2.1 x.2) (p.2.1 y.2) = H.neg.form x.2 y.2 := p.2.2 x.2 y.2
      simp only [HermSpaceCM.neg_form, neg_inj] at h2
      rw [h1, h2]⟩
  map_one' := by
    apply Subtype.ext; apply LinearEquiv.ext; intro ⟨x₁, x₂⟩; rfl
  map_mul' _ _ := by
    apply Subtype.ext; apply LinearEquiv.ext; intro ⟨x₁, x₂⟩; rfl

@[simp]
lemma doublingEmbeddingHom_apply (H : HermSpaceCM E F V)
    (g₁ : UnitaryGrp H) (g₂ : UnitaryGrp H.neg) (x : V × V) :
    (doublingEmbeddingHom H (g₁, g₂)).1 x = (g₁.1 x.1, g₂.1 x.2) := rfl

theorem doublingEmbeddingHom_injective (H : HermSpaceCM E F V) :
    Function.Injective (doublingEmbeddingHom H) := by
  rintro ⟨g₁, g₂⟩ ⟨h₁, h₂⟩ heq
  have h1 : g₁ = h₁ := by
    apply Subtype.ext; apply LinearEquiv.ext; intro v
    have hv := congrArg (fun u : UnitaryGrp H.doubled => (u.1 (v, 0)).1) heq
    simpa [doublingEmbeddingHom] using hv
  have h2 : g₂ = h₂ := by
    apply Subtype.ext; apply LinearEquiv.ext; intro v
    have hv := congrArg (fun u : UnitaryGrp H.doubled => (u.1 (0, v)).2) heq
    simpa [doublingEmbeddingHom] using hv
  exact Prod.ext h1 h2

/-- A pair `(g₁, g₂) ∈ U(V) × U(-V)` lies in the Siegel parabolic `P(V^Δ)` if and only if
`g₁ = g₂` (i.e. it lies in the diagonal subgroup `U(V)^Δ`). -/
theorem doublingEmbeddingHom_mem_siegelParabolic_iff (H : HermSpaceCM E F V)
    (g₁ : UnitaryGrp H) (g₂ : UnitaryGrp H.neg) :
    doublingEmbeddingHom H (g₁, g₂) ∈ siegelParabolicSubgroup H ↔ g₁.1 = g₂.1 := by
  constructor
  · intro hmem
    apply LinearEquiv.ext
    intro v
    have hv : (doublingEmbeddingHom H (g₁, g₂)).1 (v, v) ∈ H.diagonalSubspace :=
      hmem (v, v) rfl
    exact hv
  · intro heq x hx
    change x.1 = x.2 at hx
    change g₁.1 x.1 = g₂.1 x.2
    rw [hx, heq]

/-- Compatibility with `Stage14M1_UnitaryGroupDef.UnitaryGrp.doubledEmbed`. -/
lemma doublingEmbeddingHom_eq_doubledEmbed (H : HermSpaceCM E F V)
    (g₁ g₂ : UnitaryGrp H) :
    doublingEmbeddingHom H (g₁, unitaryGrpNegEquiv H g₂) = UnitaryGrp.doubledEmbed H (g₁, g₂) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro ⟨x₁, x₂⟩
  rfl

end CoordinateFree

section MatrixAndAdelicPoints

/-- Equality of matrix unitary groups `UnitaryMatGrp σ (-J) = UnitaryMatGrp σ J`. -/
theorem unitaryMatGrp_neg {A : Type*} [CommRing A] {n : Type*} [Fintype n] [DecidableEq n]
    (σ : A →+* A) (J : Matrix n n A) :
    UnitaryMatGrp σ (-J) = UnitaryMatGrp σ J := by
  ext g
  simp only [UnitaryMatGrp, Subgroup.mem_mk, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

/-- Block-diagonal `Fin (m + m)` matrix embedding `(g₁, g₂) ↦ reindex(diag(g₁, g₂))`. -/
def blockDiagFin {A : Type*} [CommRing A] {m : ℕ}
    (g₁ g₂ : Matrix (Fin m) (Fin m) A) : Matrix (Fin (m + m)) (Fin (m + m)) A :=
  (Stage11DoublingRallis.doubledEmbed g₁ g₂).reindex finSumFinEquiv finSumFinEquiv

lemma blockDiagFin_one {A : Type*} [CommRing A] {m : ℕ} :
    blockDiagFin (1 : Matrix (Fin m) (Fin m) A) 1 = 1 := by
  unfold blockDiagFin
  rw [doubledEmbed_one, matReindex_one_self]

lemma blockDiagFin_mul {A : Type*} [CommRing A] {m : ℕ}
    (g₁ g₂ h₁ h₂ : Matrix (Fin m) (Fin m) A) :
    blockDiagFin g₁ g₂ * blockDiagFin h₁ h₂ = blockDiagFin (g₁ * h₁) (g₂ * h₂) := by
  unfold blockDiagFin
  rw [matReindex_mul_self, doubledEmbed_mul]

lemma blockDiagFin_injective {A : Type*} [CommRing A] {m : ℕ} :
    Function.Injective (fun p : Matrix (Fin m) (Fin m) A × Matrix (Fin m) (Fin m) A =>
      blockDiagFin p.1 p.2) := by
  rintro ⟨g₁, g₂⟩ ⟨h₁, h₂⟩ heq
  apply doubledEmbed_injective
  unfold blockDiagFin at heq
  ext x y
  have hxy := congrFun (congrFun heq (finSumFinEquiv x)) (finSumFinEquiv y)
  simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using hxy

lemma blockDiagFin_preserves_herm {A : Type*} [CommRing A] {m : ℕ}
    (σ : A →+* A) {J g₁ g₂ : Matrix (Fin m) (Fin m) A}
    (hg₁ : conjTransposeMap σ g₁ * J * g₁ = J)
    (hg₂ : conjTransposeMap σ g₂ * (-J) * g₂ = -J) :
    conjTransposeMap σ (blockDiagFin g₁ g₂) *
        ((doubledForm J).reindex finSumFinEquiv finSumFinEquiv) *
        blockDiagFin g₁ g₂ =
      (doubledForm J).reindex finSumFinEquiv finSumFinEquiv := by
  unfold blockDiagFin
  rw [conjTransposeMap_reindex, matReindex_mul_self, matReindex_mul_self]
  congr 1
  unfold Stage11DoublingRallis.doubledEmbed doubledForm
  rw [conjTransposeMap_fromBlocks]
  have hc0 : conjTransposeMap σ (0 : Matrix (Fin m) (Fin m) A) = 0 := by
    ext i j; simp [conjTransposeMap]
  rw [hc0, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, hg₁, hg₂]

/-- Matrix `GL`-level doubling embedding `GL_m(A) × GL_m(A) →* GL_{2m}(A)`. -/
def doubledGLHom {A : Type*} [CommRing A] {m : ℕ} :
    GL (Fin m) A × GL (Fin m) A →* GL (Fin (m + m)) A where
  toFun p :=
    ⟨blockDiagFin p.1.1 p.2.1, blockDiagFin p.1⁻¹.1 p.2⁻¹.1,
      by rw [blockDiagFin_mul, Units.mul_inv, Units.mul_inv, blockDiagFin_one],
      by rw [blockDiagFin_mul, Units.inv_mul, Units.inv_mul, blockDiagFin_one]⟩
  map_one' := by
    apply Units.ext
    change blockDiagFin (1 : Matrix (Fin m) (Fin m) A) 1 = 1
    exact blockDiagFin_one
  map_mul' a b := by
    apply Units.ext
    change blockDiagFin (a.1 * b.1).1 (a.2 * b.2).1 =
      blockDiagFin a.1.1 a.2.1 * blockDiagFin b.1.1 b.2.1
    rw [Units.val_mul, Units.val_mul, blockDiagFin_mul]

theorem doubledGLHom_injective {A : Type*} [CommRing A] {m : ℕ} :
    Function.Injective (doubledGLHom (A := A) (m := m)) := by
  rintro ⟨g₁, g₂⟩ ⟨h₁, h₂⟩ heq
  have hmat : blockDiagFin g₁.1 g₂.1 = blockDiagFin h₁.1 h₂.1 :=
    congrArg (fun u : GL (Fin (m + m)) A => (u : Matrix (Fin (m + m)) (Fin (m + m)) A)) heq
  have hm := @blockDiagFin_injective A _ m (g₁.1, g₂.1) (h₁.1, h₂.1) hmat
  exact Prod.ext (Units.ext (congrArg Prod.fst hm)) (Units.ext (congrArg Prod.snd hm))

lemma baseChangeGL_doubledGLHom {A B : Type*} [CommRing A] [CommRing B] {m : ℕ}
    (φ : A →+* B) (g₁ g₂ : GL (Fin m) A) :
    baseChangeGL φ (doubledGLHom (g₁, g₂)) =
      doubledGLHom (baseChangeGL φ g₁, baseChangeGL φ g₂) := by
  apply Units.ext
  ext i j
  simp only [baseChangeGL_apply_matrix, doubledGLHom, blockDiagFin,
    Matrix.map_apply, Matrix.reindex_apply]
  rcases hi : finSumFinEquiv.symm i with a | a <;>
    rcases hj : finSumFinEquiv.symm j with b | b <;>
    simp [hi, hj, Stage11DoublingRallis.doubledEmbed, baseChangeGL_apply_matrix]

/-- Matrix unitary group doubling embedding `U(J)(A) × U(-J)(A) →* U(diag(J, -J))(A)`. -/
def unitaryMatGrpDoubledEmbed {A : Type*} [CommRing A] {m : ℕ}
    (σ : A →+* A) (J : Matrix (Fin m) (Fin m) A) :
    UnitaryMatGrp σ J × UnitaryMatGrp σ (-J) →*
      UnitaryMatGrp σ ((doubledForm J).reindex finSumFinEquiv finSumFinEquiv) where
  toFun p := ⟨doubledGLHom (p.1.1, p.2.1), blockDiagFin_preserves_herm σ p.1.2 p.2.2⟩
  map_one' := by apply Subtype.ext; exact map_one doubledGLHom
  map_mul' a b := by apply Subtype.ext; exact map_mul doubledGLHom (a.1.1, a.2.1) (b.1.1, b.2.1)

theorem unitaryMatGrpDoubledEmbed_injective {A : Type*} [CommRing A] {m : ℕ}
    (σ : A →+* A) (J : Matrix (Fin m) (Fin m) A) :
    Function.Injective (unitaryMatGrpDoubledEmbed σ J) := by
  intro a b h
  have hgl := doubledGLHom_injective (congrArg Subtype.val h)
  exact Prod.ext (Subtype.ext (congrArg Prod.fst hgl)) (Subtype.ext (congrArg Prod.snd hgl))

/-- Functorial `R`-points doubling embedding `U(J)(R) × U(-J)(R) →* U(V^□)(R)`. -/
def unitaryPtsDoubledEmbed {F E : Type*} [Field F] [CommRing E] [Algebra F E] {m : ℕ}
    (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (R : Type*) [CommRing R] [Algebra F R] :
    UnitaryPts σ J R × UnitaryPts σ (-J) R →*
      UnitaryPts σ ((doubledForm J).reindex finSumFinEquiv finSumFinEquiv) R where
  toFun p :=
    ⟨doubledGLHom (p.1.1, p.2.1), by
      have hneg : (-J).map (inclE (F := F) (E := E) R) = -(J.map (inclE (F := F) (E := E) R)) := by
        ext i j; simp
      have hp2 : p.2.1 ∈ UnitaryMatGrp (sigTensor σ R) (-(J.map (inclE (F := F) (E := E) R))) := by
        rw [← hneg]; exact p.2.2
      have hres := blockDiagFin_preserves_herm (sigTensor σ R) p.1.2 hp2
      have hre : ((doubledForm J).reindex finSumFinEquiv finSumFinEquiv).map
            (inclE (F := F) (E := E) R) =
          (doubledForm (J.map (inclE (F := F) (E := E) R))).reindex
            finSumFinEquiv finSumFinEquiv := by
        rw [matMap_reindex]
        congr 1
        ext x y
        cases x <;> cases y <;> simp [doubledForm]
      change conjTransposeMap (sigTensor σ R) (blockDiagFin p.1.1.1 p.2.1.1) *
          (((doubledForm J).reindex finSumFinEquiv finSumFinEquiv).map (inclE (F := F) (E := E) R)) *
          blockDiagFin p.1.1.1 p.2.1.1 =
        ((doubledForm J).reindex finSumFinEquiv finSumFinEquiv).map (inclE (F := F) (E := E) R)
      rw [hre]
      exact hres⟩
  map_one' := by apply Subtype.ext; exact map_one doubledGLHom
  map_mul' a b := by apply Subtype.ext; exact map_mul doubledGLHom (a.1.1, a.2.1) (b.1.1, b.2.1)

theorem unitaryPtsDoubledEmbed_injective {F E : Type*} [Field F] [CommRing E] [Algebra F E] {m : ℕ}
    (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (R : Type*) [CommRing R] [Algebra F R] :
    Function.Injective (unitaryPtsDoubledEmbed σ J R) := by
  intro a b h
  have hgl := doubledGLHom_injective (congrArg Subtype.val h)
  exact Prod.ext (Subtype.ext (congrArg Prod.fst hgl)) (Subtype.ext (congrArg Prod.snd hgl))

section InstantiationsOnHermSpace

variable {E F V : Type*}
  [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  [AddCommGroup V] [Module E V] [FiniteDimensional E V]

private lemma mem_unitaryPts_neg (H : HermSpaceCM E F V) (R : Type*) [CommRing R] [Algebra F R]
    (g : UnitaryPts H.cm.conjAlgHom H.neg.gram R) :
    (g.1 : GL (Fin H.dim) (E ⊗[F] R)) ∈ UnitaryPts H.cm.conjAlgHom (-H.gram) R :=
  g.2

private lemma mem_unitaryPts_doubled (H : HermSpaceCM E F V) (R : Type*) [CommRing R] [Algebra F R]
    (g : GL (Fin H.doubled.dim) (E ⊗[F] R))
    (hg : g ∈ UnitaryPts H.cm.conjAlgHom
      ((doubledForm H.gram).reindex finSumFinEquiv finSumFinEquiv) R) :
    g ∈ UnitaryPts H.cm.conjAlgHom H.doubled.gram R := by
  have hgd : H.doubled.gram = (doubledForm H.gram).reindex finSumFinEquiv finSumFinEquiv :=
    doubled_gram_eq_doubledForm H
  change conjTransposeMap (sigTensor H.cm.conjAlgHom R) (g : Matrix _ _ _) *
      (H.doubled.gram.map (inclE (F := F) (E := E) R)) * (g : Matrix _ _ _) =
    H.doubled.gram.map (inclE (F := F) (E := E) R)
  rw [hgd]
  exact hg

/-- Local finite-place doubling embedding `U(V)(F_v) × U(-V)(F_v) →* U(V^□)(F_v)`. -/
def unitaryLocalDoubledEmbed (H : HermSpaceCM E F V) (v : HeightOneSpectrum (𝓞 F)) :
    UnitaryLocalGrp H v × UnitaryLocalGrp H.neg v →* UnitaryLocalGrp H.doubled v :=
  let φ := unitaryPtsDoubledEmbed H.cm.conjAlgHom H.gram (v.adicCompletion F)
  { toFun := fun p =>
      let res := φ (p.1, ⟨p.2.1, mem_unitaryPts_neg H (v.adicCompletion F) p.2⟩)
      ⟨res.1, mem_unitaryPts_doubled H (v.adicCompletion F) res.1 res.2⟩
    map_one' := by apply Subtype.ext; exact map_one doubledGLHom
    map_mul' := fun a b => by apply Subtype.ext; exact map_mul doubledGLHom (a.1.1, a.2.1) (b.1.1, b.2.1) }

/-- Local archimedean doubling embedding `U(V)(F_ι) × U(-V)(F_ι) →* U(V^□)(F_ι)`. -/
def unitaryArchDoubledEmbed (H : HermSpaceCM E F V) (ι : F →+* ℝ) :
    UnitaryArchGrp H ι × UnitaryArchGrp H.neg ι →* UnitaryArchGrp H.doubled ι :=
  let φ := unitaryPtsDoubledEmbed H.cm.conjAlgHom H.gram (ArchReal F ι)
  { toFun := fun p =>
      let res := φ (p.1, ⟨p.2.1, mem_unitaryPts_neg H (ArchReal F ι) p.2⟩)
      ⟨res.1, mem_unitaryPts_doubled H (ArchReal F ι) res.1 res.2⟩
    map_one' := by apply Subtype.ext; exact map_one doubledGLHom
    map_mul' := fun a b => by apply Subtype.ext; exact map_mul doubledGLHom (a.1.1, a.2.1) (b.1.1, b.2.1) }

/-- Finite-adelic doubling embedding `U(V)(𝔸_{F,f}) × U(-V)(𝔸_{F,f}) →* U(V^□)(𝔸_{F,f})`. -/
def unitaryFiniteAdelicDoubledEmbed (H : HermSpaceCM E F V) :
    UnitaryFiniteAdelicGrp H × UnitaryFiniteAdelicGrp H.neg →* UnitaryFiniteAdelicGrp H.doubled :=
  let φ := unitaryPtsDoubledEmbed H.cm.conjAlgHom H.gram (FiniteAdeleRing (𝓞 F) F)
  { toFun := fun p =>
      let res := φ (p.1, ⟨p.2.1, mem_unitaryPts_neg H (FiniteAdeleRing (𝓞 F) F) p.2⟩)
      ⟨res.1, mem_unitaryPts_doubled H (FiniteAdeleRing (𝓞 F) F) res.1 res.2⟩
    map_one' := by apply Subtype.ext; exact map_one doubledGLHom
    map_mul' := fun a b => by apply Subtype.ext; exact map_mul doubledGLHom (a.1.1, a.2.1) (b.1.1, b.2.1) }

/-- Full adelic doubling embedding `U(V)(𝔸_F) × U(-V)(𝔸_F) →* U(V^□)(𝔸_F)`. -/
def unitaryAdelicDoubledEmbed (H : HermSpaceCM E F V) :
    UnitaryAdelicGrp H × UnitaryAdelicGrp H.neg →* UnitaryAdelicGrp H.doubled where
  toFun p :=
    (fun ι => unitaryArchDoubledEmbed H ι (p.1.1 ι, p.2.1 ι),
     unitaryFiniteAdelicDoubledEmbed H (p.1.2, p.2.2))
  map_one' := by
    apply Prod.ext
    · funext ι; exact map_one (unitaryArchDoubledEmbed H ι)
    · exact map_one (unitaryFiniteAdelicDoubledEmbed H)
  map_mul' a b := by
    apply Prod.ext
    · funext ι; exact map_mul (unitaryArchDoubledEmbed H ι) (a.1.1 ι, a.2.1 ι) (b.1.1 ι, b.2.1 ι)
    · exact map_mul (unitaryFiniteAdelicDoubledEmbed H) (a.1.2, a.2.2) (b.1.2, b.2.2)

theorem unitaryLocalDoubledEmbed_injective (H : HermSpaceCM E F V) (v : HeightOneSpectrum (𝓞 F)) :
    Function.Injective (unitaryLocalDoubledEmbed H v) := by
  intro a b h
  have hgl := doubledGLHom_injective (congrArg Subtype.val h)
  exact Prod.ext (Subtype.ext (congrArg Prod.fst hgl)) (Subtype.ext (congrArg Prod.snd hgl))

theorem unitaryArchDoubledEmbed_injective (H : HermSpaceCM E F V) (ι : F →+* ℝ) :
    Function.Injective (unitaryArchDoubledEmbed H ι) := by
  intro a b h
  have hgl := doubledGLHom_injective (congrArg Subtype.val h)
  exact Prod.ext (Subtype.ext (congrArg Prod.fst hgl)) (Subtype.ext (congrArg Prod.snd hgl))

theorem unitaryFiniteAdelicDoubledEmbed_injective (H : HermSpaceCM E F V) :
    Function.Injective (unitaryFiniteAdelicDoubledEmbed H) := by
  intro a b h
  have hgl := doubledGLHom_injective (congrArg Subtype.val h)
  exact Prod.ext (Subtype.ext (congrArg Prod.fst hgl)) (Subtype.ext (congrArg Prod.snd hgl))

theorem unitaryAdelicDoubledEmbed_injective (H : HermSpaceCM E F V) :
    Function.Injective (unitaryAdelicDoubledEmbed H) := by
  rintro ⟨⟨aArch, aFin⟩, ⟨bArch, bFin⟩⟩ ⟨⟨cArch, cFin⟩, ⟨dArch, dFin⟩⟩ h
  have hfin : (aFin, bFin) = (cFin, dFin) :=
    unitaryFiniteAdelicDoubledEmbed_injective H (congrArg Prod.snd h)
  have harch1 : aArch = cArch := by
    funext ι
    exact congrArg Prod.fst
      (unitaryArchDoubledEmbed_injective H ι (congrFun (congrArg Prod.fst h) ι))
  have harch2 : bArch = dArch := by
    funext ι
    exact congrArg Prod.snd
      (unitaryArchDoubledEmbed_injective H ι (congrFun (congrArg Prod.fst h) ι))
  have hfin1 : aFin = cFin := congrArg Prod.fst hfin
  have hfin2 : bFin = dFin := congrArg Prod.snd hfin
  apply Prod.ext
  · apply Prod.ext <;> assumption
  · apply Prod.ext <;> assumption

private lemma toMatrix_doubled_eq (H : HermSpaceCM E F V)
    (g₁ : UnitaryGrp H) (g₂ : UnitaryGrp H.neg) :
    LinearMap.toMatrix H.doubled.frame H.doubled.frame
        ((doublingEmbeddingHom H (g₁, g₂)).1 : V × V →ₗ[E] V × V) =
      blockDiagFin
        (LinearMap.toMatrix H.frame H.frame (g₁.1 : V →ₗ[E] V))
        (LinearMap.toMatrix H.neg.frame H.neg.frame (g₂.1 : V →ₗ[E] V)) := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  let i' : Fin (H.dim + H.dim) := i
  let j' : Fin (H.dim + H.dim) := j
  let M₁ : Matrix (Fin H.dim) (Fin H.dim) E :=
    LinearMap.toMatrix H.frame H.frame (g₁.1 : V →ₗ[E] V)
  let M₂ : Matrix (Fin H.dim) (Fin H.dim) E :=
    LinearMap.toMatrix H.neg.frame H.neg.frame (g₂.1 : V →ₗ[E] V)
  change ((H.frame.prod H.neg.frame).reindex finSumFinEquiv).repr
      (g₁.1 ((((H.frame.prod H.neg.frame).reindex finSumFinEquiv) j').1),
       g₂.1 ((((H.frame.prod H.neg.frame).reindex finSumFinEquiv) j').2)) i' =
    (Stage11DoublingRallis.doubledEmbed M₁ M₂)
      (finSumFinEquiv.symm i') (finSumFinEquiv.symm j')
  erw [Basis.repr_reindex_apply, Basis.coe_reindex, Function.comp_apply]
  rcases hi : finSumFinEquiv.symm i' with a | a <;>
    rcases hj : finSumFinEquiv.symm j' with b | b <;>
    erw [hi, hj]
  · erw [Basis.prod_apply, Basis.prod_repr_inl]
    simp [M₁, Stage11DoublingRallis.doubledEmbed, LinearMap.toMatrix_apply]
    rfl
  · erw [Basis.prod_apply, Basis.prod_repr_inl]
    simp [Stage11DoublingRallis.doubledEmbed]
    change (H.frame.repr (g₁.1 0)) a = 0
    simp
  · erw [Basis.prod_apply, Basis.prod_repr_inr]
    simp [Stage11DoublingRallis.doubledEmbed]
    let a' : Fin H.neg.dim := a
    change (H.neg.frame.repr (g₂.1 0)) a' = 0
    simp
  · erw [Basis.prod_apply, Basis.prod_repr_inr]
    simp [M₂, Stage11DoublingRallis.doubledEmbed]
    let a' : Fin H.neg.dim := a
    let b' : Fin H.neg.dim := b
    change (H.neg.frame.repr (g₂.1 (H.neg.frame b'))) a' =
      (LinearMap.toMatrix H.neg.frame H.neg.frame (g₂.1 : V →ₗ[E] V)) a' b'
    rw [LinearMap.toMatrix_apply]
    rfl

/-- Exact commutation of `doublingEmbeddingHom` with `unitaryGrpEquivMat`. -/
theorem doubledEmbed_unitaryGrpEquivMat_comm (H : HermSpaceCM E F V)
    (g₁ : UnitaryGrp H) (g₂ : UnitaryGrp H.neg) :
    ((unitaryGrpEquivMat H.doubled (doublingEmbeddingHom H (g₁, g₂))).1 :
        Matrix (Fin H.doubled.dim) (Fin H.doubled.dim) E) =
      blockDiagFin
        ((unitaryGrpEquivMat H g₁).1 : Matrix (Fin H.dim) (Fin H.dim) E)
        ((unitaryGrpEquivMat H.neg g₂).1 : Matrix (Fin H.neg.dim) (Fin H.neg.dim) E) :=
  toMatrix_doubled_eq H g₁ g₂

/-- Exact commutation of `doublingEmbeddingHom` with `ratToFiniteAdelic`. -/
theorem doubledEmbed_ratToFiniteAdelic_comm (H : HermSpaceCM E F V)
    (g₁ : UnitaryGrp H) (g₂ : UnitaryGrp H.neg) :
    H.doubled.ratToFiniteAdelic (doublingEmbeddingHom H (g₁, g₂)) =
      unitaryFiniteAdelicDoubledEmbed H
        (H.ratToFiniteAdelic g₁, H.neg.ratToFiniteAdelic g₂) := by
  apply Subtype.ext
  apply Units.ext
  have hgl : (unitaryGrpEquivMat H.doubled (doublingEmbeddingHom H (g₁, g₂))).1 =
      doubledGLHom ((unitaryGrpEquivMat H g₁).1, (unitaryGrpEquivMat H.neg g₂).1) :=
    Units.ext (doubledEmbed_unitaryGrpEquivMat_comm H g₁ g₂)
  have hbc := congrArg
    (baseChangeGL (n := Fin H.doubled.dim) (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)))
    hgl
  have h2 := baseChangeGL_doubledGLHom (inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F))
    (unitaryGrpEquivMat H g₁).1 (unitaryGrpEquivMat H.neg g₂).1
  exact congrArg
    (fun u : GL (Fin H.doubled.dim) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) =>
      (u : Matrix (Fin H.doubled.dim) (Fin H.doubled.dim) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)))
    (hbc.trans h2)

/-- Exact commutation of `doublingEmbeddingHom` with `ratToArch`. -/
theorem doubledEmbed_ratToArch_comm (H : HermSpaceCM E F V) (ι : F →+* ℝ)
    (g₁ : UnitaryGrp H) (g₂ : UnitaryGrp H.neg) :
    H.doubled.ratToArch ι (doublingEmbeddingHom H (g₁, g₂)) =
      unitaryArchDoubledEmbed H ι (H.ratToArch ι g₁, H.neg.ratToArch ι g₂) := by
  apply Subtype.ext
  apply Units.ext
  have hgl : (unitaryGrpEquivMat H.doubled (doublingEmbeddingHom H (g₁, g₂))).1 =
      doubledGLHom ((unitaryGrpEquivMat H g₁).1, (unitaryGrpEquivMat H.neg g₂).1) :=
    Units.ext (doubledEmbed_unitaryGrpEquivMat_comm H g₁ g₂)
  have hbc := congrArg
    (baseChangeGL (n := Fin H.doubled.dim) (inclE (F := F) (E := E) (ArchReal F ι)))
    hgl
  have h2 := baseChangeGL_doubledGLHom (inclE (F := F) (E := E) (ArchReal F ι))
    (unitaryGrpEquivMat H g₁).1 (unitaryGrpEquivMat H.neg g₂).1
  exact congrArg
    (fun u : GL (Fin H.doubled.dim) (E ⊗[F] ArchReal F ι) =>
      (u : Matrix (Fin H.doubled.dim) (Fin H.doubled.dim) (E ⊗[F] ArchReal F ι)))
    (hbc.trans h2)

/-- Exact commutation of `doublingEmbeddingHom` with the full diagonal rational embedding
`ratToAdelic : U(V)(E) →* U(V)(𝔸_F)`. -/
theorem doubledEmbed_ratToAdelic_comm (H : HermSpaceCM E F V)
    (g₁ : UnitaryGrp H) (g₂ : UnitaryGrp H.neg) :
    H.doubled.ratToAdelic (doublingEmbeddingHom H (g₁, g₂)) =
      unitaryAdelicDoubledEmbed H (H.ratToAdelic g₁, H.neg.ratToAdelic g₂) := by
  apply Prod.ext
  · funext ι
    exact doubledEmbed_ratToArch_comm H ι g₁ g₂
  · exact doubledEmbed_ratToFiniteAdelic_comm H g₁ g₂

/-- Action of `blockDiagFin M₁ M₂` on `Fin (m + m) → A` splits cleanly across `finSumFinEquiv`. -/
lemma blockDiagFin_mulVec {A : Type*} [CommRing A] {m : ℕ}
    (M₁ M₂ : Matrix (Fin m) (Fin m) A) (v : Fin (m + m) → A) :
    ∀ k : Fin (m + m),
      (blockDiagFin M₁ M₂ *ᵥ v) k =
        match finSumFinEquiv.symm k with
        | Sum.inl i => (M₁ *ᵥ (fun j => v (finSumFinEquiv (Sum.inl j)))) i
        | Sum.inr i => (M₂ *ᵥ (fun j => v (finSumFinEquiv (Sum.inr j)))) i := by
  intro k
  change ∑ l : Fin (m + m),
      (Stage11DoublingRallis.doubledEmbed M₁ M₂) (finSumFinEquiv.symm k) (finSumFinEquiv.symm l) * v l = _
  rw [← finSumFinEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Stage11DoublingRallis.doubledEmbed]
  rcases finSumFinEquiv.symm k with i | i <;> simp [Matrix.mulVec, dotProduct]

private lemma blockDiagFin_mem_stabGL {A : Type*} [CommRing A] {m : ℕ} (S : Subring A)
    {g₁ g₂ : GL (Fin m) A}
    (hg₁ : g₁ ∈ stabGL (stdLat (Fin m) S)) (hg₂ : g₂ ∈ stabGL (stdLat (Fin m) S)) :
    doubledGLHom (g₁, g₂) ∈ stabGL (stdLat (Fin (m + m)) S) := by
  intro x
  rw [mem_stdLat_iff, mem_stdLat_iff]
  let x₁ : Fin m → A := fun j => x (finSumFinEquiv (Sum.inl j))
  let x₂ : Fin m → A := fun j => x (finSumFinEquiv (Sum.inr j))
  have hx_iff : (∀ k : Fin (m + m), x k ∈ S) ↔ (∀ j, x₁ j ∈ S) ∧ (∀ j, x₂ j ∈ S) := by
    constructor
    · intro hx; exact ⟨fun j => hx _, fun j => hx _⟩
    · rintro ⟨h1, h2⟩ k
      rw [← finSumFinEquiv.apply_symm_apply k]
      rcases finSumFinEquiv.symm k with j | j
      · exact h1 j
      · exact h2 j
  have hmul_iff : (∀ k : Fin (m + m), (blockDiagFin g₁.1 g₂.1 *ᵥ x) k ∈ S) ↔
      (∀ j, (g₁.1 *ᵥ x₁) j ∈ S) ∧ (∀ j, (g₂.1 *ᵥ x₂) j ∈ S) := by
    constructor
    · intro hm
      refine ⟨fun j => ?_, fun j => ?_⟩
      · have h := hm (finSumFinEquiv (Sum.inl j))
        rw [blockDiagFin_mulVec, Equiv.symm_apply_apply] at h
        exact h
      · have h := hm (finSumFinEquiv (Sum.inr j))
        rw [blockDiagFin_mulVec, Equiv.symm_apply_apply] at h
        exact h
    · rintro ⟨h1, h2⟩ k
      rw [blockDiagFin_mulVec]
      rcases finSumFinEquiv.symm k with j | j
      · exact h1 j
      · exact h2 j
  have h1 := hg₁ x₁
  have h2 := hg₂ x₂
  rw [mem_stdLat_iff, mem_stdLat_iff] at h1 h2
  change (∀ k : Fin (m + m), x k ∈ S) ↔
    ∀ k : Fin (m + m), (blockDiagFin g₁.1 g₂.1 *ᵥ x) k ∈ S
  rw [hx_iff, hmul_iff, h1, h2]

/-- **Maximal Compact Level Compatibility**:
`unitaryFiniteAdelicDoubledEmbed` sends `stdMaximalLevel H × stdMaximalLevel H.neg` into
`stdMaximalLevel H.doubled`! -/
theorem stdMaximalLevel_doubled_compat (H : HermSpaceCM E F V)
    {k₁ : UnitaryFiniteAdelicGrp H} (hk₁ : k₁ ∈ stdMaximalLevel H)
    {k₂ : UnitaryFiniteAdelicGrp H.neg} (hk₂ : k₂ ∈ stdMaximalLevel H.neg) :
    unitaryFiniteAdelicDoubledEmbed H (k₁, k₂) ∈ stdMaximalLevel H.doubled := by
  have hk₁' : k₁.1 ∈ stabGL (stdLat (Fin H.dim) (adelicIntRing F E)) := hk₁
  have hk₂' : (k₂.1 : GL (Fin H.dim) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) ∈
      stabGL (stdLat (Fin H.dim) (adelicIntRing F E)) := hk₂
  exact blockDiagFin_mem_stabGL (adelicIntRing F E) hk₁' hk₂'

/-- **Principal Congruence Level Compatibility**:
`unitaryFiniteAdelicDoubledEmbed` sends
`principalCongruenceSubgroup H I × principalCongruenceSubgroup H.neg I` into
`principalCongruenceSubgroup H.doubled I` for every ideal `I ≤ 𝓞 F`! -/
theorem principalCongruence_doubled_compat (H : HermSpaceCM E F V) (I : Ideal (𝓞 F))
    {k₁ : UnitaryFiniteAdelicGrp H} (hk₁ : k₁ ∈ principalCongruenceSubgroup H I)
    {k₂ : UnitaryFiniteAdelicGrp H.neg} (hk₂ : k₂ ∈ principalCongruenceSubgroup H.neg I) :
    unitaryFiniteAdelicDoubledEmbed H (k₁, k₂) ∈ principalCongruenceSubgroup H.doubled I := by
  change (unitaryFiniteAdelicDoubledEmbed H (k₁, k₂)).1 ∈
    congruenceSubgroup F E (Fin H.doubled.dim) I
  rcases hk₁ with ⟨g₁, hg₁, hkg₁⟩
  rcases hk₂ with ⟨g₂, hg₂, hkg₂⟩
  let g₂' : GL (Fin H.dim) (adelicIntRing F E) := g₂
  have hg₁' : baseChangeGL (Ideal.Quotient.mk (levelIdeal F E I)) g₁ = 1 := hg₁
  have hg₂' : baseChangeGL (Ideal.Quotient.mk (levelIdeal F E I)) g₂' = 1 := hg₂
  let dg : GL (Fin H.doubled.dim) (adelicIntRing F E) := doubledGLHom (g₁, g₂')
  refine ⟨dg, ?_, ?_⟩
  · change baseChangeGL (Ideal.Quotient.mk (levelIdeal F E I)) (doubledGLHom (g₁, g₂')) = 1
    rw [baseChangeGL_doubledGLHom, hg₁', hg₂']
    exact map_one doubledGLHom
  · apply Units.ext
    change (baseChangeGL (adelicIntRing F E).subtype (doubledGLHom (g₁, g₂'))).1 =
      (unitaryFiniteAdelicDoubledEmbed H (k₁, k₂)).1.1
    rw [baseChangeGL_doubledGLHom]
    have hk₁m : (baseChangeGL (adelicIntRing F E).subtype g₁).1 = k₁.1.1 :=
      congrArg (fun u : GL (Fin H.dim) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) => u.1) hkg₁
    have hk₂m : (baseChangeGL (adelicIntRing F E).subtype g₂').1 = k₂.1.1 :=
      congrArg (fun u : GL (Fin H.neg.dim) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) => u.1) hkg₂
    change blockDiagFin
        (baseChangeGL (adelicIntRing F E).subtype g₁).1
        (baseChangeGL (adelicIntRing F E).subtype g₂').1 =
      blockDiagFin k₁.1.1 k₂.1.1
    rw [hk₁m, hk₂m]

/-- **Unified Doubling Embedding Package `DoublingEmbedding H`**:
packages the coordinate-free, finite-adelic, and full adelic embeddings
`U(V) × U(-V) ↪ U(V ⊕ -V)` together with injectivity, rational commutation,
level compatibility, and diagonal stabilization of `V^Δ`. -/
structure DoublingEmbedding {E F V : Type*}
    [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (H : HermSpaceCM E F V) where
  grpHom : UnitaryGrp H × UnitaryGrp H.neg →* UnitaryGrp H.doubled
  grpHom_inj : Function.Injective grpHom
  finAdelicHom : UnitaryFiniteAdelicGrp H × UnitaryFiniteAdelicGrp H.neg →*
    UnitaryFiniteAdelicGrp H.doubled
  finAdelicHom_inj : Function.Injective finAdelicHom
  adelicHom : UnitaryAdelicGrp H × UnitaryAdelicGrp H.neg →* UnitaryAdelicGrp H.doubled
  adelicHom_inj : Function.Injective adelicHom
  ratToAdelic_comm : ∀ g₁ g₂,
    H.doubled.ratToAdelic (grpHom (g₁, g₂)) =
      adelicHom (H.ratToAdelic g₁, H.neg.ratToAdelic g₂)
  stdMaximal_compat : ∀ k₁ ∈ stdMaximalLevel H, ∀ k₂ ∈ stdMaximalLevel H.neg,
    finAdelicHom (k₁, k₂) ∈ stdMaximalLevel H.doubled
  diag_stabilizes : ∀ g : UnitaryGrp H,
    grpHom (g, unitaryGrpNegEquiv H g) ∈ siegelParabolicSubgroup H

/-- Canonical construction of `DoublingEmbedding H` for any CM Hermitian space `H`. -/
def canonicalDoublingEmbedding (H : HermSpaceCM E F V) : DoublingEmbedding H where
  grpHom := doublingEmbeddingHom H
  grpHom_inj := doublingEmbeddingHom_injective H
  finAdelicHom := unitaryFiniteAdelicDoubledEmbed H
  finAdelicHom_inj := unitaryFiniteAdelicDoubledEmbed_injective H
  adelicHom := unitaryAdelicDoubledEmbed H
  adelicHom_inj := unitaryAdelicDoubledEmbed_injective H
  ratToAdelic_comm := doubledEmbed_ratToAdelic_comm H
  stdMaximal_compat _ hk₁ _ hk₂ := stdMaximalLevel_doubled_compat H hk₁ hk₂
  diag_stabilizes g := (doublingEmbeddingHom_mem_siegelParabolic_iff H g _).mpr rfl

end InstantiationsOnHermSpace

end MatrixAndAdelicPoints

end DoublingEmbeddings

/-! ## Section 3: Concrete Doubling Zeta Integrals (`DoublingZetaIntegral`) & Eigenform Factorization -/

section DoublingZetaIntegrals

/-- **Doubling Siegel Parabolic Section `DoublingSiegelSection`** on a group `G`
with parabolic subgroup `P` and compact subgroup `K`, realized via a height function `H`
and local/adelic Weil representation datum `(ω, evalZero)`. -/
structure DoublingSiegelSection (G V : Type*) [Group G] [AddCommGroup V] [Module ℂ V] where
  ω : G →* Module.End ℂ V
  evalZero : V →ₗ[ℂ] ℂ
  height : G → ℝ≥0
  s0 : ℂ
  Φ : V
  parabolic : Subgroup G
  compact : Subgroup G
  height_right_K : ∀ g, ∀ k ∈ compact, height (g * k) = height g
  vacuum_K_eigen : ∀ k ∈ compact, ∃ χ : Circle, ω k Φ = (χ : ℂ) • Φ

namespace DoublingSiegelSection

/-- Value of the Siegel–Eisenstein doubling section at `(s, g)`:
`f_s(g) = H(g)^{s - s₀} · evalZero(ω(g) Φ)` (directly matching
`Stage14M1_SchrodingerFockModel.siegelSection`). -/
def eval {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (sec : DoublingSiegelSection G V) (s : ℂ) (g : G) : ℂ :=
  siegelSection sec.ω sec.evalZero sec.height sec.s0 sec.Φ s g

theorem eval_one {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (sec : DoublingSiegelSection G V) (hH1 : sec.height 1 = 1) (s : ℂ) :
    sec.eval s 1 = sec.evalZero sec.Φ :=
  siegelSection_one sec.ω sec.evalZero sec.height hH1 sec.s0 sec.Φ s

theorem eval_right_K_eigen {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (sec : DoublingSiegelSection G V) (s : ℂ) (g : G) {k : G} (hk : k ∈ sec.compact) :
    ∃ χ : Circle, sec.eval s (g * k) = (χ : ℂ) * sec.eval s g := by
  obtain ⟨χ, hχ⟩ := sec.vacuum_K_eigen k hk
  refine ⟨χ, ?_⟩
  unfold eval siegelSection
  have hχ' : sec.ω k sec.Φ = (χ : ℂ) • sec.Φ := hχ
  rw [sec.height_right_K g k hk, map_mul, Module.End.mul_apply, hχ']
  change ((sec.height g : ℝ) : ℂ) ^ (s - sec.s0) * sec.evalZero ((sec.ω g) ((χ : ℂ) • sec.Φ)) = _
  rw [map_smul, map_smul, smul_eq_mul]
  ring

end DoublingSiegelSection

/-- **Concrete Doubling Zeta Integral `DoublingZetaIntegral`**:
$$Z(s, \varphi_1, \varphi_2, f_s) = \int_G \langle \varphi_2, \pi(g)\varphi_1 \rangle\,f_s(g)\,d\mu_G(g),$$
wired directly to `Stage11DoublingRallis.doublingZetaInt` and `doublingOpInt`. -/
def DoublingZetaIntegral {G V : Type*} [MeasurableSpace G] [Group G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (μG : Measure G) (π : G →* Module.End ℂ V) (f_s : ℂ → G → ℂ)
    (s : ℂ) (φ₁ φ₂ : V) : ℂ :=
  doublingZetaInt μG π (f_s s) φ₁ φ₂

/-- Finite-genus / weighted discrete doubling zeta pairing
`Z_fin(s, φ₁, φ₂, f_s) = ∑_{g ∈ G} ⟨φ₂, π(g) φ₁⟩ * f_s(g)`. -/
def autDoublingZeta {G V : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : G →* Module.End ℂ V) (f_s : ℂ → G → ℂ) (s : ℂ) (φ₁ φ₂ : V) : ℂ :=
  doublingZeta π (f_s s) φ₁ φ₂

/-- **Operator-Pairing Identity**: `⟨φ₂, D_s φ₁⟩ = Z(s, φ₁, φ₂, f_s)`. -/
theorem doublingZetaIntegral_eq_inner {G V : Type*} [MeasurableSpace G] [Group G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (μG : Measure G) (π : G →* Module.End ℂ V) (f_s : ℂ → G → ℂ)
    (s : ℂ) (φ₁ φ₂ : V)
    (hint : Integrable (fun g : G => f_s s g • π g φ₁) μG) :
    inner ℂ φ₂ (doublingOpInt μG π (f_s s) φ₁) =
      DoublingZetaIntegral μG π f_s s φ₁ φ₂ :=
  doubling_zeta_integral_eq μG π (f_s s) φ₁ φ₂ hint

theorem autDoublingZeta_eq_inner {G V : Type*} [Group G] [Fintype G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : G →* Module.End ℂ V) (f_s : ℂ → G → ℂ) (s : ℂ) (φ₁ φ₂ : V) :
    inner ℂ φ₂ (doublingOp π (f_s s) φ₁) = autDoublingZeta π f_s s φ₁ φ₂ :=
  doubling_zeta_fin_eq π (f_s s) φ₁ φ₂

/-- Left `ℂ`-linearity of `DoublingZetaIntegral` in `φ₁`. -/
theorem doublingZetaIntegral_smul_left {G V : Type*} [MeasurableSpace G] [Group G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (μG : Measure G) (π : G →* Module.End ℂ V) (f_s : ℂ → G → ℂ)
    (s : ℂ) (c : ℂ) (φ₁ φ₂ : V) :
    DoublingZetaIntegral μG π f_s s (c • φ₁) φ₂ =
      c * DoublingZetaIntegral μG π f_s s φ₁ φ₂ := by
  unfold DoublingZetaIntegral doublingZetaInt
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only [map_smul, inner_smul_right]
  ring

/-- Right conjugate-linearity of `DoublingZetaIntegral` in `φ₂`. -/
theorem doublingZetaIntegral_smul_right {G V : Type*} [MeasurableSpace G] [Group G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (μG : Measure G) (π : G →* Module.End ℂ V) (f_s : ℂ → G → ℂ)
    (s : ℂ) (c : ℂ) (φ₁ φ₂ : V) :
    DoublingZetaIntegral μG π f_s s φ₁ (c • φ₂) =
      star c * DoublingZetaIntegral μG π f_s s φ₁ φ₂ := by
  unfold DoublingZetaIntegral doublingZetaInt
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only [inner_smul_left, starRingEnd_apply]
  ring

/-- **Unconditional Convergence Criterion (`doublingZetaIntegral_integrable_of_decay`)**:
if the matrix coefficient `g ↦ ⟨φ₂, π(g) φ₁⟩ * f_s(g)` is `AEStronglyMeasurable` and
dominated by `M · H(g)^{-decayExp}` for a `SiegelSetEnvelope` (`decayExp ≥ critExp`), then
the doubling zeta integral is Bochner-integrable with quantitative `L¹` bound. -/
theorem doublingZetaIntegral_integrable_of_decay {G V : Type*} [MeasurableSpace G] [Group G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (μG : Measure G) (E : SiegelSetEnvelope μG)
    (π : G →* Module.End ℂ V) (f_s : ℂ → G → ℂ) (s : ℂ) (φ₁ φ₂ : V)
    (M : ℝ) (decayExp : ℝ) (hExp : E.critExp ≤ decayExp)
    (hmeas : AEStronglyMeasurable (fun g : G => inner ℂ φ₂ (π g φ₁) * f_s s g) μG)
    (hdom : ∀ᵐ g ∂μG, ‖inner ℂ φ₂ (π g φ₁) * f_s s g‖ ≤ M * (E.H g) ^ (-decayExp)) :
    Integrable (fun g : G => inner ℂ φ₂ (π g φ₁) * f_s s g) μG := by
  have hintE : Integrable (fun g : G => M * (E.H g) ^ (-decayExp)) μG :=
    (E.decay_integrable hExp).const_mul M
  refine hintE.mono' hmeas ?_
  filter_upwards [hdom] with g hg
  exact hg

/-- **Product-Measure Factorization of the Doubling Zeta Integral**:
when `(G₁ × G₂, μ₁ × μ₂)` carries factorizable matrix coefficients `c₁(g₁) * c₂(g₂)`
and a factorizable section `f₁(g₁) * f₂(g₂)`, the doubling zeta integral over `G₁ × G₂`
factors into the product of the two factor integrals. -/
theorem doublingZetaIntegral_factorizes_prod {G₁ G₂ : Type*}
    [MeasurableSpace G₁] [MeasurableSpace G₂]
    (μ₁ : Measure G₁) (μ₂ : Measure G₂) [SFinite μ₁] [SFinite μ₂]
    (c₁ : G₁ → ℂ) (c₂ : G₂ → ℂ) (f₁ : G₁ → ℂ) (f₂ : G₂ → ℂ)
    (hint : Integrable (fun p : G₁ × G₂ => (c₁ p.1 * f₁ p.1) * (c₂ p.2 * f₂ p.2))
      (μ₁.prod μ₂)) :
    ∫ p : G₁ × G₂, (c₁ p.1 * c₂ p.2) * (f₁ p.1 * f₂ p.2) ∂(μ₁.prod μ₂) =
      (∫ g₁ : G₁, c₁ g₁ * f₁ g₁ ∂μ₁) * (∫ g₂ : G₂, c₂ g₂ * f₂ g₂ ∂μ₂) := by
  have hrew : (fun p : G₁ × G₂ => (c₁ p.1 * c₂ p.2) * (f₁ p.1 * f₂ p.2)) =
      fun p : G₁ × G₂ => (c₁ p.1 * f₁ p.1) * (c₂ p.2 * f₂ p.2) := by
    funext p; ring
  rw [hrew, integral_prod _ hint]
  simp_rw [integral_const_mul, integral_mul_const]

/-- **Multiplicity-One Hecke Eigenform Factorization of `autDoublingZeta`**:
wired directly to `Stage11DoublingRallis.doubling_eigenform_factorization` on the
simultaneous Hecke eigenspace `S = ⨅ i, eigenspace (T i) (lam i)`. -/
theorem autDoublingZeta_eigenform_factorization {G V ι : Type*}
    [Group G] [Fintype G] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : G →* Module.End ℂ V) (f_s : ℂ → G → ℂ) (s : ℂ)
    (T : ι → Module.End ℂ V) (lam : ι → ℂ)
    (hcomm : ∀ i g, T i ∘ₗ π g = π g ∘ₗ T i)
    (hdim1 : Module.finrank ℂ (↥(⨅ i : ι, Module.End.eigenspace (T i) (lam i))) = 1) :
    ∃! Z_pi : ℂ,
      ∀ φ₁ ∈ (⨅ i : ι, Module.End.eigenspace (T i) (lam i) : Submodule ℂ V),
      ∀ φ₂ ∈ (⨅ i : ι, Module.End.eigenspace (T i) (lam i) : Submodule ℂ V),
        autDoublingZeta π f_s s φ₁ φ₂ = Z_pi * inner ℂ φ₂ φ₁ := by
  have hcommOp : ∀ i, T i ∘ₗ doublingOp π (f_s s) = doublingOp π (f_s s) ∘ₗ T i := fun i =>
    doublingOp_comm_hecke π (f_s s) (T i) (hcomm i)
  obtain ⟨Z_pi, hZ, huniq⟩ := doubling_eigenform_factorization T lam (doublingOp π (f_s s)) hcommOp hdim1
  refine ⟨Z_pi, fun φ₁ h₁ φ₂ h₂ => ?_, fun Z' hZ' => ?_⟩
  · rw [← autDoublingZeta_eq_inner]
    exact (hZ.2.1 φ₁ h₁ φ₂ h₂).1
  · set S : Submodule ℂ V := ⨅ i : ι, Module.End.eigenspace (T i) (lam i)
    have hS_ne_bot : S ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hdim1
      exact zero_ne_one hdim1
    obtain ⟨e, heS, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS_ne_bot
    have hinner_ne : inner ℂ e e ≠ 0 := inner_self_ne_zero.mpr he0
    have h1 := hZ' e heS e heS
    have h2 := (hZ.2.1 e heS e heS).1
    rw [← autDoublingZeta_eq_inner, h2] at h1
    exact mul_right_cancel₀ hinner_ne h1.symm

/-- **Concrete Adelic Split-Place Vacuum Matrix Coefficient Bridge**:
links `Stage14M1_SchrodingerFockModel.adelic_padic_split_vacuum_coeff` to the local-global
factorization of the doubling matrix coefficient on `adelicVacuum`. -/
theorem doubling_adelic_vacuum_matrix_coeff (g : AdelicWeilElement) :
    let hA : IsArchSchwartz (realWeilOp (Real.cos g.thetaInf) (Real.sin g.thetaInf)
        (-Real.sin g.thetaInf) (Real.cos g.thetaInf) adelicVacuum.fInf) := by
      change IsArchSchwartz (realWeilOp _ _ _ _ stdGauss)
      rw [gauss_vacuum_eigenvalue]
      exact isArchSchwartz_const_mul _ stdGauss_isArchSchwartz
    adelicPureInner adelicVacuum (adelicWeilAct g adelicVacuum hA) =
      (1 / 2 : ℂ) * Complex.exp (Complex.I * (g.thetaInf : ℂ)) *
        ∏ p ∈ g.ramPrimes,
          (g.chiFin p (g.aFin p) : ℂ) *
            (((p.1 : ℝ) ^ (-((|(g.aFin p).1.valuation| : ℤ) : ℝ) / 2) : ℝ) : ℂ) :=
  adelic_padic_split_vacuum_coeff g

end DoublingZetaIntegrals

/-! ## Section 4: `doubling_unramified_local_L_factor` & Partial Euler Product Convergence -/

section UnramifiedLocalDoublingL

/-- Unramified local data at a finite place `v` of a CM base field `F` with residue cardinality
`q_v ≥ 2` (`1 < q_v`) and Satake parameters `α : Fin n → ℂ` for `U(n)`. -/
structure CMUnramifiedPlaceData (F : Type*) [Field F] [NumberField F] (n : ℕ) where
  v : HeightOneSpectrum (𝓞 F)
  q : ℕ
  hq : 1 < q
  satake : Fin n → ℂ

/-- Rank-`n` local standard Euler factor at residue cardinality `q`:
`L_v^{(n)}(w, α) = ∏_{i=1}^n (1 - α_i q^{-w})⁻¹`. -/
def localStdLFactorUn_q (n : ℕ) (q : ℂ) (α : Fin n → ℂ) (w : ℂ) : ℂ :=
  ∏ i : Fin n, (1 - α i * q ^ (-w))⁻¹

/-- Rank-`n` local Piatetski-Shapiro–Rallis doubling normalizing factor at residue cardinality `q`:
`d_v^{(n)}(s) = ∏_{j=0}^{n-1} (1 - q^{-(2s + n - j)})⁻¹`. -/
def localDoublingNormFactorUn_q (n : ℕ) (q s : ℂ) : ℂ :=
  ∏ j ∈ Finset.range n, (1 - q ^ (-(2 * s + (n : ℂ) - (j : ℂ))))⁻¹

/-- Rank-`n` unramified local doubling zeta factor at residue cardinality `q`:
`Z_v^{(n)}(s, α) = ∏_{i=0}^{n-1} (1 - q^{-(2s + n - i)}) / (1 - α_i q^{-(s + 1/2)})`. -/
def localDoublingFactorUn_q (n : ℕ) (q : ℂ) (α : Fin n → ℂ) (s : ℂ) : ℂ :=
  ∏ i : Fin n, (1 - q ^ (-(2 * s + (n : ℂ) - (i.1 : ℂ)))) *
    (1 - α i * q ^ (-(s + 1 / 2)))⁻¹

@[simp]
lemma localStdLFactorUn_q_nat (n p : ℕ) (α : Fin n → ℂ) (w : ℂ) :
    localStdLFactorUn_q n (p : ℂ) α w = localStdLFactorUn n p α w := rfl

@[simp]
lemma localDoublingNormFactorUn_q_nat (n p : ℕ) (s : ℂ) :
    localDoublingNormFactorUn_q n (p : ℂ) s = localDoublingNormFactorUn n p s := rfl

@[simp]
lemma localDoublingFactorUn_q_nat (n p : ℕ) (α : Fin n → ℂ) (s : ℂ) :
    localDoublingFactorUn_q n (p : ℂ) α s = localDoublingFactorUn n p α s := rfl

/-- **Rank-`n` Unramified Local Doubling Factorization (`doubling_unramified_local_L_factor_Un`)**:
for EVERY rank `n`, residue cardinality `q : ℂ`, Satake parameter tuple `α : Fin n → ℂ`, and `s : ℂ`,
$$Z_v^{(n)}(s, \alpha) = \frac{L_v^{(n)}(s + 1/2, \alpha)}{d_v^{(n)}(s)}.$$ -/
theorem doubling_unramified_local_L_factor_Un (n : ℕ) (q : ℂ) (α : Fin n → ℂ) (s : ℂ) :
    localDoublingFactorUn_q n q α s =
      localStdLFactorUn_q n q α (s + 1 / 2) / localDoublingNormFactorUn_q n q s := by
  unfold localDoublingFactorUn_q localStdLFactorUn_q localDoublingNormFactorUn_q
  rw [Finset.prod_mul_distrib,
    Finset.prod_inv_distrib (s := Finset.range n)
      (f := fun j : ℕ => 1 - q ^ (-(2 * s + (n : ℂ) - (j : ℂ)))),
    div_inv_eq_mul, mul_comm]
  congr 1
  rw [Fin.prod_univ_eq_prod_range (fun j : ℕ => 1 - q ^ (-(2 * s + (n : ℂ) - (j : ℂ)))) n]

/-- Cartan double-coset volume `vol(K diag(ϖ_v^r, 1) K)` at residue cardinality `q`. -/
def cartanCosetVol_q (q : ℕ) (r : ℕ) : ℂ :=
  if r = 0 then 1 else (q : ℂ) ^ r * (1 + (q : ℂ)⁻¹)

/-- Macdonald unramified spherical matrix coefficient on `GL₂(F_v)` at residue cardinality `q`. -/
def macdonaldSphericalGL2_q (q : ℕ) (α β : ℂ) (r : ℕ) : ℂ :=
  match r with
  | 0 => 1
  | 1 => (1 + (q : ℂ)⁻¹)⁻¹ * (q : ℂ) ^ (-(1 : ℂ) / 2) * homogSym2 α β 1
  | m + 2 =>
      (1 + (q : ℂ)⁻¹)⁻¹ * (q : ℂ) ^ (-((m + 2 : ℕ) : ℂ) / 2) *
        (homogSym2 α β (m + 2) - (q : ℂ)⁻¹ * (α * β) * homogSym2 α β m)

/-- Unramified Siegel–Eisenstein doubling section `f_s(diag(ϖ_v^r, 1)) = q^{-r(s + 1)}`. -/
def unramifiedDoublingSection_q (q : ℕ) (s : ℂ) (r : ℕ) : ℂ :=
  (q : ℂ) ^ (-(r : ℂ) * (s + 1))

/-- Full Cartan–Macdonald local unramified doubling zeta integral `Z_v(s, α, β)` at any
residue cardinality `q ≥ 2`. -/
def localDoublingZetaGL2_q (q : ℕ) (α β s : ℂ) : ℂ :=
  ∑' r : ℕ, cartanCosetVol_q q r * macdonaldSphericalGL2_q q α β r *
    unramifiedDoublingSection_q q s r

def localStdLFactorGL2_q (q : ℕ) (α β w : ℂ) : ℂ :=
  ((1 - α * (q : ℂ) ^ (-w)) * (1 - β * (q : ℂ) ^ (-w)))⁻¹

def localDoublingNormFactor_q (q : ℕ) (ω s : ℂ) : ℂ :=
  (1 - ω * (q : ℂ) ^ (-(2 * s + 2)))⁻¹

private lemma cartan_term_simplify_q {q : ℕ} (hq : 1 < q) (α β s : ℂ) (r : ℕ) :
    cartanCosetVol_q q r * macdonaldSphericalGL2_q q α β r * unramifiedDoublingSection_q q s r =
      (match r with
       | 0 => homogSym2 α β 0
       | 1 => homogSym2 α β 1
       | m + 2 => homogSym2 α β (m + 2) - (q : ℂ)⁻¹ * (α * β) * homogSym2 α β m) *
        ((q : ℂ) ^ (-(s + 1 / 2))) ^ r := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (lt_trans zero_lt_one hq)
  have hqC_ne : (q : ℂ) ≠ 0 := by exact_mod_cast hq_pos.ne'
  have h1q_ne : (1 : ℂ) + (q : ℂ)⁻¹ ≠ 0 := by
    have hR : (0 : ℝ) < 1 + (q : ℝ)⁻¹ := by positivity
    have hC : ((1 + (q : ℝ)⁻¹ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
    simpa only [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_inv,
      Complex.ofReal_natCast] using hC
  have hpow : ∀ n : ℕ,
      (q : ℂ) ^ n * (q : ℂ) ^ (-(n : ℂ) / 2) * (q : ℂ) ^ (-(n : ℂ) * (s + 1)) =
        ((q : ℂ) ^ (-(s + 1 / 2))) ^ n := by
    intro n
    rw [← Complex.cpow_natCast (q : ℂ) n, ← Complex.cpow_add _ _ hqC_ne,
      ← Complex.cpow_add _ _ hqC_ne, ← Complex.cpow_nat_mul]
    congr 1
    ring
  cases r with
  | zero =>
    simp [cartanCosetVol_q, macdonaldSphericalGL2_q, unramifiedDoublingSection_q]
  | succ k =>
    cases k with
    | zero =>
      simp only [cartanCosetVol_q, Nat.zero_add, one_ne_zero, ↓reduceIte,
        macdonaldSphericalGL2_q, unramifiedDoublingSection_q, pow_one, Nat.cast_one]
      have h1 := hpow 1
      simp only [pow_one, Nat.cast_one] at h1
      calc (q : ℂ) * (1 + (q : ℂ)⁻¹) *
              ((1 + (q : ℂ)⁻¹)⁻¹ * (q : ℂ) ^ (-(1 : ℂ) / 2) * homogSym2 α β 1) *
              (q : ℂ) ^ (-(1 : ℂ) * (s + 1))
          = homogSym2 α β 1 * ((1 + (q : ℂ)⁻¹) * (1 + (q : ℂ)⁻¹)⁻¹) *
              ((q : ℂ) * (q : ℂ) ^ (-(1 : ℂ) / 2) * (q : ℂ) ^ (-(1 : ℂ) * (s + 1))) := by ring
        _ = homogSym2 α β 1 * (q : ℂ) ^ (-(s + 1 / 2)) := by
              rw [mul_inv_cancel₀ h1q_ne, mul_one, h1]
    | succ m =>
      simp only [cartanCosetVol_q, Nat.succ_ne_zero, ↓reduceIte, macdonaldSphericalGL2_q,
        unramifiedDoublingSection_q]
      have hm := hpow (m + 2)
      calc (q : ℂ) ^ (m + 2) * (1 + (q : ℂ)⁻¹) *
              ((1 + (q : ℂ)⁻¹)⁻¹ * (q : ℂ) ^ (-((m + 2 : ℕ) : ℂ) / 2) *
                (homogSym2 α β (m + 2) - (q : ℂ)⁻¹ * (α * β) * homogSym2 α β m)) *
              (q : ℂ) ^ (-((m + 2 : ℕ) : ℂ) * (s + 1))
          = (homogSym2 α β (m + 2) - (q : ℂ)⁻¹ * (α * β) * homogSym2 α β m) *
              ((1 + (q : ℂ)⁻¹) * (1 + (q : ℂ)⁻¹)⁻¹) *
              ((q : ℂ) ^ (m + 2) * (q : ℂ) ^ (-((m + 2 : ℕ) : ℂ) / 2) *
                (q : ℂ) ^ (-((m + 2 : ℕ) : ℂ) * (s + 1))) := by ring
        _ = (homogSym2 α β (m + 2) - (q : ℂ)⁻¹ * (α * β) * homogSym2 α β m) *
              ((q : ℂ) ^ (-(s + 1 / 2))) ^ (m + 2) := by
              rw [mul_inv_cancel₀ h1q_ne, mul_one, hm]

/-- **Analytic Rank-2 / Split-Place Local Unramified Doubling Identity** at arbitrary residue
cardinality `q > 1`:
$$Z_v(s, \alpha, \beta) = \frac{L_v(s + 1/2, \pi_v)}{d_v(s, \alpha \beta)}.$$ -/
theorem doubling_unramified_local_L_factor_GL2_q {q : ℕ} (hq : 1 < q) {α β s : ℂ}
    (hα : ‖α * (q : ℂ) ^ (-(s + 1 / 2))‖ < 1)
    (hβ : ‖β * (q : ℂ) ^ (-(s + 1 / 2))‖ < 1) :
    localDoublingZetaGL2_q q α β s =
      localStdLFactorGL2_q q α β (s + 1 / 2) / localDoublingNormFactor_q q (α * β) s := by
  have hqC_ne : (q : ℂ) ≠ 0 := by
    have : 0 < q := lt_trans zero_lt_one hq
    exact Nat.cast_ne_zero.mpr this.ne'
  set X : ℂ := (q : ℂ) ^ (-(s + 1 / 2))
  have hMain : HasSum (fun r : ℕ => homogSym2 α β r * X ^ r)
      (((1 - α * X) * (1 - β * X))⁻¹) := hasSum_homogSym2_mul_pow hα hβ
  let cShift : ℂ := (q : ℂ)⁻¹ * (α * β) * X ^ 2
  have hSubBase : HasSum (fun m : ℕ => cShift * (homogSym2 α β m * X ^ m))
      (cShift * ((1 - α * X) * (1 - β * X))⁻¹) := hMain.mul_left cShift
  let gShift : ℕ → ℂ := fun r =>
    match r with
    | 0 => 0
    | 1 => 0
    | m + 2 => (q : ℂ)⁻¹ * (α * β) * homogSym2 α β m * X ^ (m + 2)
  have hShift : HasSum gShift (cShift * ((1 - α * X) * (1 - β * X))⁻¹) := by
    have h2 : HasSum (fun m : ℕ => gShift (m + 2)) (cShift * ((1 - α * X) * (1 - β * X))⁻¹) := by
      refine hSubBase.congr_fun fun m => ?_
      dsimp only [gShift, cShift]
      rw [pow_add]
      ring
    have h2' : HasSum (fun m : ℕ => gShift (m + 2))
        (cShift * ((1 - α * X) * (1 - β * X))⁻¹ - ∑ i ∈ Finset.range 2, gShift i) := by
      simpa [Finset.sum_range_succ, gShift] using h2
    exact (hasSum_nat_add_iff' 2 (f := gShift)).mp h2'
  have hDiff : HasSum (fun r : ℕ => homogSym2 α β r * X ^ r - gShift r)
      (((1 - α * X) * (1 - β * X))⁻¹ - cShift * ((1 - α * X) * (1 - β * X))⁻¹) :=
    hMain.sub hShift
  have hTerms : (fun r : ℕ =>
      cartanCosetVol_q q r * macdonaldSphericalGL2_q q α β r * unramifiedDoublingSection_q q s r) =
      fun r : ℕ => homogSym2 α β r * X ^ r - gShift r := by
    funext r
    rw [cartan_term_simplify_q hq α β s r]
    cases r with
    | zero => dsimp only [gShift, X]; ring
    | succ k =>
      cases k with
      | zero => dsimp only [gShift, X]; ring
      | succ m => dsimp only [gShift, X]; ring
  unfold localDoublingZetaGL2_q
  rw [hTerms, hDiff.tsum_eq]
  have hX2 : (q : ℂ)⁻¹ * X ^ 2 = (q : ℂ) ^ (-(2 * s + 2)) := by
    dsimp only [X]
    rw [← Complex.cpow_neg_one (q : ℂ), ← Complex.cpow_nat_mul, ← Complex.cpow_add _ _ hqC_ne]
    congr 1
    push_cast
    ring
  have hcShift : cShift = (α * β) * (q : ℂ) ^ (-(2 * s + 2)) := by
    dsimp only [cShift]
    rw [← hX2]
    ring
  unfold localStdLFactorGL2_q localDoublingNormFactor_q
  rw [hcShift, div_inv_eq_mul]
  change ((1 - α * X) * (1 - β * X))⁻¹ -
      α * β * (q : ℂ) ^ (-(2 * s + 2)) * ((1 - α * X) * (1 - β * X))⁻¹ =
    ((1 - α * X) * (1 - β * X))⁻¹ * (1 - α * β * (q : ℂ) ^ (-(2 * s + 2)))
  ring

/-- **MASTER LOCAL UNRAMIFIED DOUBLING `L`-FACTOR THEOREM (`doubling_unramified_local_L_factor`)**:
unconditionally certifies BOTH:
1. For any `CMUnramifiedPlaceData F n` (`q_v > 1`, `satake : Fin n → ℂ`),
   `Z_v^{(n)}(s, α) = L_v^{(n)}(s + 1/2, α) / d_v^{(n)}(s)`;
2. For any `CMUnramifiedPlaceData F 2` in the domain of absolute convergence, the full analytic
   Macdonald–Cartan double-coset series `localDoublingZetaGL2_q` equals
   `L_v(s + 1/2, α) / d_v(s, det α)`;
3. Exact compatibility with `Stage11DoublingRallis.localDoublingZetaGL2_eq` at rational primes! -/
theorem doubling_unramified_local_L_factor {F : Type*} [Field F] [NumberField F] :
    (∀ (n : ℕ) (P : CMUnramifiedPlaceData F n) (s : ℂ),
      localDoublingFactorUn_q n (P.q : ℂ) P.satake s =
        localStdLFactorUn_q n (P.q : ℂ) P.satake (s + 1 / 2) /
          localDoublingNormFactorUn_q n (P.q : ℂ) s) ∧
    (∀ (P : CMUnramifiedPlaceData F 2) (s : ℂ),
      ‖P.satake 0 * (P.q : ℂ) ^ (-(s + 1 / 2))‖ < 1 →
      ‖P.satake 1 * (P.q : ℂ) ^ (-(s + 1 / 2))‖ < 1 →
      localDoublingZetaGL2_q P.q (P.satake 0) (P.satake 1) s =
        localStdLFactorGL2_q P.q (P.satake 0) (P.satake 1) (s + 1 / 2) /
          localDoublingNormFactor_q P.q (P.satake 0 * P.satake 1) s) ∧
    (∀ {p : ℕ}, p.Prime → ∀ {α β s : ℂ},
      ‖α * (p : ℂ) ^ (-(s + 1 / 2))‖ < 1 →
      ‖β * (p : ℂ) ^ (-(s + 1 / 2))‖ < 1 →
      localDoublingZetaGL2 p α β s =
        localStdLFactorGL2 p α β (s + 1 / 2) / localDoublingNormFactor p (α * β) s) :=
  ⟨fun n P s => doubling_unramified_local_L_factor_Un n (P.q : ℂ) P.satake s,
   fun P _ h0 h1 => doubling_unramified_local_L_factor_GL2_q P.hq h0 h1,
   @localDoublingZetaGL2_eq⟩

section PartialEulerProduct

private lemma summable_prime_inv_rpow {δ : ℝ} (hδ : 1 < δ) :
    Summable (fun p : Nat.Primes => ((p.1 : ℝ) ^ δ)⁻¹) :=
  (Real.summable_nat_rpow_inv.mpr hδ).comp_injective (Subtype.val_injective (p := Nat.Prime))

private lemma multipliable_finset_prod_c {ι κ : Type*} (s : Finset κ) (f : κ → ι → ℂ)
    (hf : ∀ k ∈ s, Multipliable (f k)) :
    Multipliable (fun i => ∏ k ∈ s, f k i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [multipliable_one]
  | @insert k s hk ih =>
    have hk' : Multipliable (f k) := hf k (Finset.mem_insert_self k s)
    have hs' : Multipliable (fun i => ∏ j ∈ s, f j i) :=
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
    simpa [Finset.prod_insert hk] using hk'.mul hs'

private lemma multipliable_one_sub_inv_of_summable {ι : Type*} (z : ι → ℂ)
    (hz_sum : Summable (fun i => ‖z i‖))
    (hz_ne : ∀ i, 1 - z i ≠ 0) :
    Multipliable (fun i => (1 - z i)⁻¹) ∧ Multipliable (fun i => 1 - z i) := by
  have hz_tendsto : Tendsto (fun i => ‖z i‖) cofinite (nhds 0) :=
    hz_sum.tendsto_cofinite_zero
  have hev : ∀ᶠ i in cofinite, ‖z i‖ ≤ 1 / 2 :=
    hz_tendsto.eventually (Metric.ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1 / 2))
      |>.mono fun i hi => by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at hi
        exact hi.le
  have hterm : ∀ i, (1 - z i)⁻¹ = 1 + z i * (1 - z i)⁻¹ := fun i => by
    have h := hz_ne i
    field_simp [h]
    ring
  have hsum_inv : Summable (fun i => z i * (1 - z i)⁻¹) := by
    refine Summable.of_norm_bounded_eventually (g := fun i => 2 * ‖z i‖) (hz_sum.mul_left 2) ?_
    refine hev.mono fun i hi => ?_
    have hlow : 1 / 2 ≤ ‖1 - z i‖ := by
      have htri : ‖(1 : ℂ)‖ - ‖z i‖ ≤ ‖(1 : ℂ) - z i‖ := norm_sub_norm_le 1 (z i)
      rw [norm_one] at htri
      linarith
    have hinv_le : ‖(1 - z i)⁻¹‖ ≤ 2 := by
      rw [norm_inv]
      exact inv_le_of_inv_le₀ (by norm_num) (by simpa using hlow)
    rw [norm_mul]
    calc ‖z i‖ * ‖(1 - z i)⁻¹‖ ≤ ‖z i‖ * 2 := mul_le_mul_of_nonneg_left hinv_le (norm_nonneg _)
      _ = 2 * ‖z i‖ := mul_comm _ _
  have hsum_neg : Summable (fun i => -z i) :=
    (Summable.of_norm hz_sum).neg
  have hm1 : Multipliable (fun i => 1 + z i * (1 - z i)⁻¹) :=
    Complex.multipliable_one_add_of_summable hsum_inv
  have hm2 : Multipliable (fun i => 1 + (-z i)) :=
    Complex.multipliable_one_add_of_summable hsum_neg
  refine ⟨hm1.congr fun i => (hterm i).symm, hm2.congr fun i => (sub_eq_add_neg 1 (z i)).symm⟩

/-- **Absolute Convergence of the Partial Unitary Standard `L`-Product & Doubling Normalizing
Factor** outside any finite ramified set `S : Finset Nat.Primes`:
if `∀ p ∉ S, ∀ i, ‖α p i‖ ≤ p ^ σ₀`, `σ₀ + 1 / 2 < s.re`, and `0 < s.re`, then BOTH
`∏' p ∉ S, localStdLFactorUn n p (α p) (s + 1/2)`,
`∏' p ∉ S, localDoublingNormFactorUn n p s`, and their quotient
`∏' p ∉ S, localDoublingFactorUn n p (α p) s` converge unconditionally (`Multipliable`)! -/
theorem doubling_partial_euler_product {n : ℕ} (S : Finset Nat.Primes)
    (α : Nat.Primes → Fin n → ℂ) (σ₀ : ℝ)
    (hbound : ∀ p : Nat.Primes, p ∉ S → ∀ i : Fin n, ‖α p i‖ ≤ (p.1 : ℝ) ^ σ₀)
    {s : ℂ} (hs : σ₀ + 1 / 2 < s.re) (hs_pos : 0 < s.re) :
    Multipliable (fun p : {p : Nat.Primes // p ∉ S} =>
      localStdLFactorUn n p.1.1 (α p.1) (s + 1 / 2)) ∧
    Multipliable (fun p : {p : Nat.Primes // p ∉ S} =>
      localDoublingNormFactorUn n p.1.1 s) ∧
    Multipliable (fun p : {p : Nat.Primes // p ∉ S} =>
      localDoublingFactorUn n p.1.1 (α p.1) s) := by
  have hδ : 1 < s.re + 1 / 2 - σ₀ := by linarith
  have hsum_base : Summable (fun p : {p : Nat.Primes // p ∉ S} =>
      ((p.1.1 : ℝ) ^ (s.re + 1 / 2 - σ₀))⁻¹) :=
    (summable_prime_inv_rpow hδ).comp_injective Subtype.val_injective
  have hstd_i : ∀ i : Fin n,
      Multipliable (fun p : {p : Nat.Primes // p ∉ S} =>
        (1 - α p.1 i * (p.1.1 : ℂ) ^ (-(s + 1 / 2)))⁻¹) := by
    intro i
    refine (multipliable_one_sub_inv_of_summable
      (fun p : {p : Nat.Primes // p ∉ S} => α p.1 i * (p.1.1 : ℂ) ^ (-(s + 1 / 2))) ?_ ?_).1
    · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_) hsum_base
      have hp_pos : (0 : ℝ) < (p.1.1 : ℝ) := Nat.cast_pos.mpr p.1.2.pos
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos p.1.2.pos]
      have hexp : (-(s + 1 / 2)).re = -(s.re + 1 / 2) := by simp
      rw [hexp]
      calc ‖α p.1 i‖ * (p.1.1 : ℝ) ^ (-(s.re + 1 / 2))
          ≤ (p.1.1 : ℝ) ^ σ₀ * (p.1.1 : ℝ) ^ (-(s.re + 1 / 2)) :=
            mul_le_mul_of_nonneg_right (hbound p.1 p.2 i) (Real.rpow_nonneg hp_pos.le _)
        _ = (p.1.1 : ℝ) ^ (-(s.re + 1 / 2 - σ₀)) := by
            rw [← Real.rpow_add hp_pos]
            congr 1; ring
        _ = ((p.1.1 : ℝ) ^ (s.re + 1 / 2 - σ₀))⁻¹ := Real.rpow_neg hp_pos.le _
    · intro p h0
      have h1 : α p.1 i * (p.1.1 : ℂ) ^ (-(s + 1 / 2)) = 1 := (sub_eq_zero.mp h0).symm
      have hp_pos : (0 : ℝ) < (p.1.1 : ℝ) := Nat.cast_pos.mpr p.1.2.pos
      have hp_gt1 : (1 : ℝ) < (p.1.1 : ℝ) := by exact_mod_cast p.1.2.one_lt
      have hlt : ‖α p.1 i * (p.1.1 : ℂ) ^ (-(s + 1 / 2))‖ < 1 := by
        rw [norm_mul, Complex.norm_natCast_cpow_of_pos p.1.2.pos]
        have hexp : (-(s + 1 / 2)).re = -(s.re + 1 / 2) := by simp
        rw [hexp]
        calc ‖α p.1 i‖ * (p.1.1 : ℝ) ^ (-(s.re + 1 / 2))
            ≤ (p.1.1 : ℝ) ^ σ₀ * (p.1.1 : ℝ) ^ (-(s.re + 1 / 2)) :=
              mul_le_mul_of_nonneg_right (hbound p.1 p.2 i) (Real.rpow_nonneg hp_pos.le _)
          _ = (p.1.1 : ℝ) ^ (-(s.re + 1 / 2 - σ₀)) := by
              rw [← Real.rpow_add hp_pos]; congr 1; ring
          _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp_gt1 (by linarith)
      rw [h1, norm_one] at hlt
      exact lt_irrefl 1 hlt
  have hnorm_j : ∀ j ∈ Finset.range n,
      Multipliable (fun p : {p : Nat.Primes // p ∉ S} =>
        (1 - (p.1.1 : ℂ) ^ (-(2 * s + (n : ℂ) - (j : ℂ))))⁻¹) ∧
      Multipliable (fun p : {p : Nat.Primes // p ∉ S} =>
        1 - (p.1.1 : ℂ) ^ (-(2 * s + (n : ℂ) - (j : ℂ)))) := by
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    have hre_gt1 : 1 < 2 * s.re + (n : ℝ) - (j : ℝ) := by
      have hnj : (1 : ℝ) ≤ (n : ℝ) - (j : ℝ) := by
        have hjn1 : j + 1 ≤ n := hjn
        have : ((j + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hjn1
        push_cast at this
        linarith
      linarith
    have hsum_j : Summable (fun p : {p : Nat.Primes // p ∉ S} =>
        ‖(p.1.1 : ℂ) ^ (-(2 * s + (n : ℂ) - (j : ℂ)))‖) := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => ?_)
        ((summable_prime_inv_rpow hre_gt1).comp_injective Subtype.val_injective)
      have hp_pos : (0 : ℝ) < (p.1.1 : ℝ) := Nat.cast_pos.mpr p.1.2.pos
      have hexp : (-(2 * s + (n : ℂ) - (j : ℂ))).re = -(2 * s.re + (n : ℝ) - (j : ℝ)) := by
        simp only [Complex.neg_re, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.re_ofNat,
          Complex.im_ofNat, Complex.natCast_re, zero_mul, sub_zero]
      rw [Complex.norm_natCast_cpow_of_pos p.1.2.pos, hexp, Real.rpow_neg hp_pos.le]
      rfl
    refine multipliable_one_sub_inv_of_summable _ hsum_j fun p h0 => ?_
    have h1 : (p.1.1 : ℂ) ^ (-(2 * s + (n : ℂ) - (j : ℂ))) = 1 := (sub_eq_zero.mp h0).symm
    have hp_gt1 : (1 : ℝ) < (p.1.1 : ℝ) := by exact_mod_cast p.1.2.one_lt
    have hlt : ‖(p.1.1 : ℂ) ^ (-(2 * s + (n : ℂ) - (j : ℂ)))‖ < 1 := by
      rw [Complex.norm_natCast_cpow_of_pos p.1.2.pos]
      apply Real.rpow_lt_one_of_one_lt_of_neg hp_gt1
      simp only [Complex.neg_re, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.re_ofNat,
        Complex.im_ofNat, Complex.natCast_re, zero_mul, sub_zero]
      linarith
    rw [h1, norm_one] at hlt
    exact lt_irrefl 1 hlt
  have hM_std : Multipliable (fun p : {p : Nat.Primes // p ∉ S} =>
      localStdLFactorUn n p.1.1 (α p.1) (s + 1 / 2)) := by
    unfold localStdLFactorUn
    exact multipliable_finset_prod_c Finset.univ _ fun i _ => hstd_i i
  have hM_norm : Multipliable (fun p : {p : Nat.Primes // p ∉ S} =>
      localDoublingNormFactorUn n p.1.1 s) := by
    unfold localDoublingNormFactorUn
    exact multipliable_finset_prod_c (Finset.range n) _ fun j hj => (hnorm_j j hj).1
  have hM_norm_inv : Multipliable (fun p : {p : Nat.Primes // p ∉ S} =>
      ∏ j ∈ Finset.range n, (1 - (p.1.1 : ℂ) ^ (-(2 * s + (n : ℂ) - (j : ℂ))))) :=
    multipliable_finset_prod_c (Finset.range n) _ fun j hj => (hnorm_j j hj).2
  have hM_fac : Multipliable (fun p : {p : Nat.Primes // p ∉ S} =>
      localDoublingFactorUn n p.1.1 (α p.1) s) := by
    have hmul := hM_std.mul hM_norm_inv
    refine hmul.congr fun p => ?_
    rw [localDoublingFactorUn_eq]
    unfold localDoublingNormFactorUn
    rw [Finset.prod_inv_distrib, div_inv_eq_mul]
  exact ⟨hM_std, hM_norm, hM_fac⟩

/-- **Limit–Product Factorization at Unramified Places** (distilling Alpöge's
`DoublingEulerProductFarRight.limit_eq_prod_mul` cleanly):
whenever partial doubling integrals `I T` converge to `J` as `T → ⊤` and split outside `S` as
`I U = (∏ v ∈ T, f v) * I S` for `U = S ⊔ T`, then `J = P * I S` where `P = ∏' v ∉ S, f v`! -/
theorem doubling_limit_eq_prod_mul {ι : Type*} (S : Finset ι) (f : ι → ℂ)
    (I : Finset ι → ℂ) {P J : ℂ}
    (hP : HasProd (fun v : {v : ι // v ∉ (S : Set ι)} => f v.1) P)
    (hJ : Tendsto I atTop (nhds J))
    (hsplit : ∀ T U : Finset ι, Disjoint S T → (∀ u, u ∈ U ↔ u ∈ S ∨ u ∈ T) →
      I U = (∏ v ∈ T, f v) * I S) :
    J = P * I S := by
  classical
  let e : {v : ι // v ∉ (S : Set ι)} ↪ ι := Function.Embedding.subtype _
  have ht : Tendsto (fun T : Finset {v : ι // v ∉ (S : Set ι)} => S ∪ T.map e)
      atTop atTop := by
    refine tendsto_atTop.2 fun b =>
      (eventually_ge_atTop (b.subtype fun v => v ∉ (S : Set ι))).mono fun T hT u hu => ?_
    by_cases hS : u ∈ S
    · exact Finset.mem_union_left _ hS
    · exact Finset.mem_union_right _
        (Finset.mem_map.2 ⟨⟨u, hS⟩, hT (Finset.mem_subtype.2 hu), rfl⟩)
  have h1 := hJ.comp ht
  have h2 : Tendsto (fun T : Finset {v : ι // v ∉ (S : Set ι)} => (∏ v ∈ T, f v.1) * I S)
      atTop (nhds (P * I S)) :=
    Tendsto.mul_const _ hP
  refine tendsto_nhds_unique h1 (h2.congr fun T => ?_)
  rw [Function.comp_apply, hsplit (T.map e) _ ?_ (fun u => Finset.mem_union), Finset.prod_map]
  · rfl
  · refine Finset.disjoint_left.2 fun u hu hu' => ?_
    obtain ⟨w, -, rfl⟩ := Finset.mem_map.1 hu'
    exact w.2 hu

end PartialEulerProduct

end UnramifiedLocalDoublingL

/-! ## Section 5: `doubling_seesaw_fubini`, Theta Mean & Rallis Inner-Product Positivity -/

section DoublingSeesawFubini

/-- **Twisted Weighted Finite-Genus Doubling Seesaw**:
for a determinant character `χ : G → Circle` and a doubled theta kernel `Θd` satisfying
`Θ g₁ h * star (Θ g₂ h) = (χ g₂ : ℂ) * Θd (g₁, g₂) h`, the weighted genus inner product
of `θ(φ₁)` and `θ(φ₂)` equals the doubled weighted pairing against `Θd`! -/
theorem doubling_seesaw_weighted_twisted {G H : Type*} [Fintype G] [Fintype H]
    (wG : G → ℂ) (wH : H → ℂ) (hwG : ∀ g, star (wG g) = wG g)
    (Θ : G → H → ℂ) (Θd : G × G → H → ℂ) (χ : G → Circle)
    (hsplit : ∀ g₁ g₂ h, Θ g₁ h * star (Θ g₂ h) = (χ g₂ : ℂ) * Θd (g₁, g₂) h)
    (φ₁ φ₂ : G → ℂ) :
    autInner wH (thetaLiftW wG Θ φ₁) (thetaLiftW wG Θ φ₂) =
      ∑ p : G × G, (wG p.1 * wG p.2) * φ₁ p.1 * star (φ₂ p.2) * (χ p.2 : ℂ) *
        (∑ h : H, wH h * Θd p h) := by
  rw [doubling_seesaw_inner_product_eq wG wH hwG Θ φ₁ φ₂]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold doubledThetaKernel
  have hsum : (∑ h : H, wH h * Θ p.1 h * star (Θ p.2 h)) =
      (χ p.2 : ℂ) * ∑ h : H, wH h * Θd p h := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    have hs := hsplit p.1 p.2 h
    calc wH h * Θ p.1 h * star (Θ p.2 h)
        = wH h * (Θ p.1 h * star (Θ p.2 h)) := by ring
      _ = wH h * ((χ p.2 : ℂ) * Θd p h) := by rw [hs]
      _ = (χ p.2 : ℂ) * (wH h * Θd p h) := by ring
  rw [hsum]
  ring

/-- **Hilbert-Space (`EuclideanSpace ℂ`) Doubling Seesaw Identity**
(bridged from `Stage11DoublingRallis.doubling_seesaw_inner_product_L2`). -/
theorem doubling_seesaw_L2 {G H : Type*} [Fintype G] [Fintype H]
    (Θ : G → H → ℂ) (φ₁ φ₂ : EuclideanSpace ℂ G) :
    inner ℂ (thetaLiftLin Θ φ₂) (thetaLiftLin Θ φ₁) =
      ∑ p : G × G, φ₁ p.1 * star (φ₂ p.2) * doubledThetaKernel (fun _ => (1 : ℂ)) Θ p :=
  doubling_seesaw_inner_product_L2 Θ φ₁ φ₂

/-- **PIATETSKI-SHAPIRO–RALLIS DOUBLING SEESAW FUBINI THEOREM (`doubling_seesaw_fubini`)**:
For `SFinite` automorphic quotient measure spaces `(G, μG)` and `(H, μH)`, theta kernel
`Θ : G → H → ℂ`, doubled theta kernel `Θd : G × G → H → ℂ`, and character twist
`χ : G → Circle` satisfying the doubling kernel factorization
`Θ g₁ h * star (Θ g₂ h) = (χ g₂ : ℂ) * Θd (g₁, g₂) h`:
$$\int_H \theta(\varphi_1)(h)\,\overline{\theta(\varphi_2)(h)}\,d\mu_H(h) =
  \iint_{G \times G} \varphi_1(g_1)\,\overline{\varphi_2(g_2)}\,\chi(g_2)\,
    \left(\int_H \Theta^□((g_1, g_2), h)\,d\mu_H(h)\right) d\mu_G(g_1)\,d\mu_G(g_2).$$ -/
theorem doubling_seesaw_fubini {G H : Type*} [MeasurableSpace G] [MeasurableSpace H]
    {μG : Measure G} {μH : Measure H} [SFinite μG] [SFinite μH]
    (Θ : G → H → ℂ) (Θd : G × G → H → ℂ) (χ : G → Circle)
    (hsplit : ∀ g₁ g₂ h, Θ g₁ h * star (Θ g₂ h) = (χ g₂ : ℂ) * Θd (g₁, g₂) h)
    (φ₁ φ₂ : G → ℂ)
    (hint₁ : Integrable
      (fun p : (G × G) × H =>
        φ₁ p.1.1 * star (φ₂ p.1.2) * (Θ p.1.1 p.2 * star (Θ p.1.2 p.2)))
      ((μG.prod μG).prod μH))
    (hint₂ : ∀ h : H, Integrable
      (fun p : G × G => (φ₁ p.1 * Θ p.1 h) * star (φ₂ p.2 * Θ p.2 h)) (μG.prod μG)) :
    ∫ h, thetaLiftInt μG Θ φ₁ h * star (thetaLiftInt μG Θ φ₂ h) ∂μH =
      ∫ p : G × G, φ₁ p.1 * star (φ₂ p.2) * (χ p.2 : ℂ) * (∫ h, Θd p h ∂μH) ∂(μG.prod μG) := by
  rw [doubling_seesaw_integral_eq Θ φ₁ φ₂ hint₁ hint₂]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  dsimp only [doubledThetaKernelInt]
  have hker : (fun h => Θ p.1 h * star (Θ p.2 h)) = fun h => (χ p.2 : ℂ) * Θd p h := by
    funext h
    exact hsplit p.1 p.2 h
  rw [hker, integral_const_mul]
  ring

/-- Untwisted `doubling_seesaw_fubini` (`χ = 1`). -/
theorem doubling_seesaw_fubini_untwisted {G H : Type*} [MeasurableSpace G] [MeasurableSpace H]
    {μG : Measure G} {μH : Measure H} [SFinite μG] [SFinite μH]
    (Θ : G → H → ℂ) (φ₁ φ₂ : G → ℂ)
    (hint₁ : Integrable
      (fun p : (G × G) × H =>
        φ₁ p.1.1 * star (φ₂ p.1.2) * (Θ p.1.1 p.2 * star (Θ p.1.2 p.2)))
      ((μG.prod μG).prod μH))
    (hint₂ : ∀ h : H, Integrable
      (fun p : G × G => (φ₁ p.1 * Θ p.1 h) * star (φ₂ p.2 * Θ p.2 h)) (μG.prod μG)) :
    ∫ h, thetaLiftInt μG Θ φ₁ h * star (thetaLiftInt μG Θ φ₂ h) ∂μH =
      ∫ p : G × G, φ₁ p.1 * star (φ₂ p.2) * doubledThetaKernelInt μH Θ p ∂(μG.prod μG) :=
  doubling_seesaw_integral_eq Θ φ₁ φ₂ hint₁ hint₂

/-- **Normalized Theta-Mean Form of `doubling_seesaw_fubini`** (matching Alpöge's
`RallisDM.lean:84-108` and `SiegelWeilCore.thetaMean`):
when `0 < μH.real Set.univ`, factoring out the quotient volume `vol(H) = μH.real Set.univ`
rewrites the inner `h`-integral as `vol(H) * thetaMean μH volH (Θd p)`. -/
theorem doubling_seesaw_theta_mean {G H : Type*} [MeasurableSpace G] [MeasurableSpace H]
    {μG : Measure G} {μH : Measure H} [SFinite μG] [SFinite μH]
    (Θ : G → H → ℂ) (Θd : G × G → H → ℂ) (χ : G → Circle)
    (hsplit : ∀ g₁ g₂ h, Θ g₁ h * star (Θ g₂ h) = (χ g₂ : ℂ) * Θd (g₁, g₂) h)
    (_hvol_pos : 0 < μH.real Set.univ)
    (φ₁ φ₂ : G → ℂ)
    (hint₁ : Integrable
      (fun p : (G × G) × H =>
        φ₁ p.1.1 * star (φ₂ p.1.2) * (Θ p.1.1 p.2 * star (Θ p.1.2 p.2)))
      ((μG.prod μG).prod μH))
    (hint₂ : ∀ h : H, Integrable
      (fun p : G × G => (φ₁ p.1 * Θ p.1 h) * star (φ₂ p.2 * Θ p.2 h)) (μG.prod μG)) :
    let volH : ℝ := μH.real Set.univ
    ((volH : ℂ)⁻¹ * ∫ h, thetaLiftInt μG Θ φ₁ h * star (thetaLiftInt μG Θ φ₂ h) ∂μH) =
      ∫ p : G × G,
        φ₁ p.1 * star (φ₂ p.2) * (χ p.2 : ℂ) *
          thetaMean μH volH (Θd p) ∂(μG.prod μG) := by
  intro volH
  rw [doubling_seesaw_fubini Θ Θd χ hsplit φ₁ φ₂ hint₁ hint₂, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  dsimp only [thetaMean]
  rw [Complex.real_smul, Complex.ofReal_inv]
  ring

/-- **Rallis Inner-Product Positivity** across Hilbert, weighted finite-genus, and continuous
Bochner-integral settings. -/
theorem doubling_seesaw_normSq_nonneg {G H : Type*} [MeasurableSpace G] [MeasurableSpace H]
    (μG : Measure G) (μH : Measure H) (Θ : G → H → ℂ) (φ : G → ℂ) :
    0 ≤ (∫ h, thetaLiftInt μG Θ φ h * star (thetaLiftInt μG Θ φ h) ∂μH).re ∧
    (∫ h, thetaLiftInt μG Θ φ h * star (thetaLiftInt μG Θ φ h) ∂μH).im = 0 :=
  rallis_integral_inner_product_nonneg μG μH Θ φ

/-- **Rallis Non-Vanishing Equivalence**: `θ(φ) ≠ 0 ↔ 0 < Re⟨D φ, φ⟩`. -/
theorem doubling_seesaw_ne_zero_iff {G H : Type*} [Fintype G] [Fintype H]
    (Θ : G → H → ℂ) (φ : EuclideanSpace ℂ G) :
    thetaLiftLin Θ φ ≠ 0 ↔ 0 < (inner ℂ (doublingGramOp Θ φ) φ).re :=
  theta_lift_ne_zero_iff_doubling_pos Θ φ

end DoublingSeesawFubini

/-! ## Section 6: Wave-3 Integration Bridges (`RallisSeesawGlobal` & `DoublingZetaPackage`) -/

section Wave3Bridges

/-- **Direct Bridge into `RHDirect.RallisSeesaw.RallisInnerProductHyp`** from a doubling
eigenform action `D φ = (c * L * ∏ Z_v) • φ`. -/
theorem toRallisInnerProductHyp {G H P : Type*} [Fintype G] [Fintype H]
    (Θ : G → H → ℂ) (S : Submodule ℂ (EuclideanSpace ℂ G))
    (Pset : Finset P) (c L : ℂ) (Z_loc : P → ℂ)
    (hD : ∀ φ ∈ S, doublingGramOp Θ φ = (c * L * ∏ v ∈ Pset, Z_loc v) • φ) :
    RallisInnerProductHyp (thetaLiftLin Θ) S Pset c L Z_loc :=
  rallisInnerProductHyp_of_doubling_eigen Θ S Pset c L Z_loc hD

/-- **Direct Bridge into `RHDirect.SiegelWeilCore.DoublingZetaForm`** from a concrete
doubling Gram operator `doublingGramOp Θ`. -/
def toDoublingZetaForm {G H Lat : Type*} [Fintype G] [Fintype H]
    (Θ : G → H → ℂ) (IsSelfDual : Lat → Prop) (vec : Lat → EuclideanSpace ℂ G)
    (htransfer : ∀ L₁ L₂, IsSelfDual L₁ → IsSelfDual L₂ →
      ∃ u : ℂ, u ≠ 0 ∧
        inner ℂ (vec L₂) (doublingGramOp Θ (vec L₂)) =
          u * inner ℂ (vec L₁) (doublingGramOp Θ (vec L₁))) :
    DoublingZetaForm Lat :=
  concreteDoublingZetaForm Θ IsSelfDual vec htransfer

/-- **Unified Wave-2 Export Package `DoublingZetaPackage`** for downstream Wave 3
`Stage14M1_RallisSeesawGlobal`, bundling a `DoubledHermSpace`, its `DoublingEmbedding`,
and the local unramified `L`-factor identity. -/
structure DoublingZetaPackage (E F V : Type*)
    [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V] where
  doubled : DoubledHermSpace E F V
  embed : DoublingEmbedding doubled.base
  local_L_factor : ∀ (n : ℕ) (P : CMUnramifiedPlaceData F n) (s : ℂ),
    localDoublingFactorUn_q n (P.q : ℂ) P.satake s =
      localStdLFactorUn_q n (P.q : ℂ) P.satake (s + 1 / 2) /
        localDoublingNormFactorUn_q n (P.q : ℂ) s

/-- Canonical `DoublingZetaPackage` attached to any CM Hermitian space `H`. -/
def canonicalDoublingZetaPackage {E F V : Type*}
    [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (H : HermSpaceCM E F V) : DoublingZetaPackage E F V where
  doubled := DoubledHermSpace.ofHermSpace H
  embed := canonicalDoublingEmbedding H
  local_L_factor n P s := doubling_unramified_local_L_factor_Un n (P.q : ℂ) P.satake s

end Wave3Bridges

end RHDirect.Stage14M1_DoublingZeta

end
