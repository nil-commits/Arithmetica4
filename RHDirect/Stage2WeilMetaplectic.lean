import RHDirect.RallisSeesaw
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# RHDirect.Stage2WeilMetaplectic

Compact, self-contained, 0-`sorry`, 0-`axiom` formalization of the **Finite-Field / Schrödinger
Model of the Weil Representation, Heisenberg Commutation, Plancherel–Fourier Unitarity,
Stone–von Neumann Uniqueness, Metaplectic Parabolic Generators, and Explicit Seesaw Dual-Pair
Intertwiners** underneath `RHDirect.RallisSeesaw` and `RHDirect.SiegelWeilCore`.

## Structure

1. **Finite-Field Additive Characters & Dot-Product Orthogonality on `𝔽^n`**:
   - Bilinear dot product `dotProd` on `Fin n → 𝔽` and unit-circle properties of additive
     characters `ψ : AddChar 𝔽 ℂ` (`addChar_norm_eq_one`, `addChar_star_eq_neg`).
   - Exact orthogonality `sum_psi_dotProd` on `𝔽^n` and nondegeneracy.
2. **Concrete Schrödinger Representation & Heisenberg Group `Heis 𝔽 n`**:
   - Hilbert space `SchrodingerSpace 𝔽 n := EuclideanSpace ℂ (Fin n → 𝔽)`, bridged directly to
     `RHDirect.RallisSeesaw.wip`.
   - Concrete translation `T a` and character-multiplication `M ψ b`, group laws, unitarity,
     adjoints, and the exact **Heisenberg commutation relation**
     `T a ∘ₗ M ψ b = ψ (dotProd a b) • (M ψ b ∘ₗ T a)`.
   - Concrete polarized Heisenberg group `Heis 𝔽 n` (`Group (Heis 𝔽 n)`), unitary representation
     `schrodingerRep : Heis 𝔽 n →* End ℂ (SchrodingerSpace 𝔽 n)`, and group commutator realizing
     the canonical symplectic form `sympForm`.
3. **Finite Fourier Transform `ℱ`, Plancherel/Parseval Unitarity, `ℱ² = reflection` & Weyl
   Intertwining**:
   - Normalized finite Fourier operator `fourierOp ψ`, exact Plancherel unitarity
     `fourierOp_unitary`, Parseval identity `fourierOp_parseval`, reflection inversion
     `fourierOp_sq_eq_reflect`, order-4 identity `fourierOp_pow_four`, adjoint formula, and
     exact Weyl intertwining (`fourierOp_comp_T`, `fourierOp_comp_M`).
4. **Stone–von Neumann Theorem (Commutant = Scalars, Irreducibility & Unitary Uniqueness)**:
   - Delta-basis projectors `coordProj ψ x₀`, Schur commutant theorem
     `heis_commutant_eq_scalars`, irreducibility `schrodinger_irreducible`.
   - Vacuum-projection decomposition `heis_vacuum_decomposition`, isometry of the canonical
     intertwiner `heisIntertwiner`, and full **Stone–von Neumann unitary equivalence**
     `stone_von_neumann_uniqueness` (`SchrodingerSpace 𝔽 n ≃ₗᵢ[ℂ] H`).
5. **Metaplectic Parabolic Generators & Explicit Finite Seesaw Dual-Pair Intertwiners**:
   - Siegel Levi `weilLevi` and quadratic-phase `weilQuad` operators, exact unitarity, group
     laws, Heisenberg covariance (`weilLevi_comp_T`, `weilLevi_comp_M`,
     `weilQuad_conj_T`), and Siegel parabolic semidirect relation (`weilLevi_comp_weilQuad`).
   - Concrete finite-field orthogonal–symplectic (`tensorForm`, `O(M₁) × Sp(M₂)`) and
     Hermitian–unitary (`hermTensorForm`, `U(H₁) × U(H₂)`) dual-pair symplectic forms.
   - Commuting dual-pair Weil action `dualPairWeilAction` on `L²(M_{m × n}(𝔽))`, explicit
     `RHDirect.RallisSeesaw.SeesawDualPair` packaging (`finiteThetaSeesawPair`), Rallis
     nonnegativity/nonvanishing, direct-sum splitting factorization (`finiteTheta_split_product`),
     and the exact **Kudla–Rallis Seesaw Intertwiner Identity** (`seesaw_intertwiner_identity`).
-/

open Finset Matrix RHDirect RHDirect.RallisSeesaw
open scoped BigOperators InnerProductSpace

namespace RHDirect.Stage2WeilMetaplectic

noncomputable section

/-! ## Section 1: Finite-Field Additive Characters & Dot-Product Orthogonality on `𝔽^n` -/

section FiniteFieldCharacters

/-- Standard nondegenerate dot product `⟨a, b⟩ = ∑ i, a i * b i` on `𝔽^n`. -/
def dotProd {𝔽 : Type*} [CommSemiring 𝔽] {n : ℕ} (a b : Fin n → 𝔽) : 𝔽 :=
  ∑ i : Fin n, a i * b i

theorem dotProd_comm {𝔽 : Type*} [CommSemiring 𝔽] {n : ℕ} (a b : Fin n → 𝔽) :
    dotProd a b = dotProd b a := by
  unfold dotProd
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

@[simp]
theorem dotProd_zero_left {𝔽 : Type*} [CommSemiring 𝔽] {n : ℕ} (b : Fin n → 𝔽) :
    dotProd (0 : Fin n → 𝔽) b = 0 := by
  simp [dotProd]

@[simp]
theorem dotProd_zero_right {𝔽 : Type*} [CommSemiring 𝔽] {n : ℕ} (a : Fin n → 𝔽) :
    dotProd a (0 : Fin n → 𝔽) = 0 := by
  simp [dotProd]

theorem dotProd_add_left {𝔽 : Type*} [CommSemiring 𝔽] {n : ℕ} (a₁ a₂ b : Fin n → 𝔽) :
    dotProd (a₁ + a₂) b = dotProd a₁ b + dotProd a₂ b := by
  unfold dotProd
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem dotProd_add_right {𝔽 : Type*} [CommSemiring 𝔽] {n : ℕ} (a b₁ b₂ : Fin n → 𝔽) :
    dotProd a (b₁ + b₂) = dotProd a b₁ + dotProd a b₂ := by
  unfold dotProd
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem dotProd_neg_left {𝔽 : Type*} [CommRing 𝔽] {n : ℕ} (a b : Fin n → 𝔽) :
    dotProd (-a) b = -dotProd a b := by
  unfold dotProd
  simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

theorem dotProd_neg_right {𝔽 : Type*} [CommRing 𝔽] {n : ℕ} (a b : Fin n → 𝔽) :
    dotProd a (-b) = -dotProd a b := by
  unfold dotProd
  simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem dotProd_sub_left {𝔽 : Type*} [CommRing 𝔽] {n : ℕ} (a₁ a₂ b : Fin n → 𝔽) :
    dotProd (a₁ - a₂) b = dotProd a₁ b - dotProd a₂ b := by
  rw [sub_eq_add_neg, dotProd_add_left, dotProd_neg_left, sub_eq_add_neg]

theorem dotProd_sub_right {𝔽 : Type*} [CommRing 𝔽] {n : ℕ} (a b₁ b₂ : Fin n → 𝔽) :
    dotProd a (b₁ - b₂) = dotProd a b₁ - dotProd a b₂ := by
  rw [sub_eq_add_neg, dotProd_add_right, dotProd_neg_right, sub_eq_add_neg]

theorem dotProd_smul_left {𝔽 : Type*} [CommSemiring 𝔽] {n : ℕ} (c : 𝔽) (a b : Fin n → 𝔽) :
    dotProd (c • a) b = c * dotProd a b := by
  unfold dotProd
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

theorem dotProd_smul_right {𝔽 : Type*} [CommSemiring 𝔽] {n : ℕ} (c : 𝔽) (a b : Fin n → 𝔽) :
    dotProd a (c • b) = c * dotProd a b := by
  rw [dotProd_comm, dotProd_smul_left, dotProd_comm]

theorem dotProd_mulVec_left {𝔽 : Type*} [CommSemiring 𝔽] {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) 𝔽) (x : Fin n → 𝔽) (y : Fin m → 𝔽) :
    dotProd (M.mulVec x) y = dotProd x (Mᵀ.mulVec y) := by
  unfold dotProd Matrix.mulVec dotProduct
  simp only [Finset.sum_mul, Finset.mul_sum, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem dotProd_mulVec_right {𝔽 : Type*} [CommSemiring 𝔽] {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) 𝔽) (y : Fin m → 𝔽) (x : Fin n → 𝔽) :
    dotProd y (M.mulVec x) = dotProd (Mᵀ.mulVec y) x := by
  rw [dotProd_comm, dotProd_mulVec_left, dotProd_comm]

/-- Every value of an additive character on a finite additive group lies on the unit circle. -/
theorem addChar_norm_eq_one {A : Type*} [AddCommGroup A] [Fintype A]
    (ψ : AddChar A ℂ) (a : A) :
    ‖ψ a‖ = 1 := by
  have hpow : (ψ a) ^ Fintype.card A = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]
  have h1 : ‖ψ a‖ ^ Fintype.card A = 1 := by
    rw [← norm_pow, hpow, norm_one]
  have hpos : 0 < Fintype.card A := Fintype.card_pos
  rcases lt_trichotomy ‖ψ a‖ 1 with hlt | heq | hgt
  · exfalso
    have := pow_lt_one₀ (norm_nonneg _) hlt hpos.ne'
    linarith
  · exact heq
  · exfalso
    have := one_lt_pow₀ hgt hpos.ne'
    linarith

/-- Every value of an additive character on a finite additive group is nonzero. -/
theorem addChar_ne_zero {A : Type*} [AddCommGroup A] [Fintype A]
    (ψ : AddChar A ℂ) (a : A) :
    ψ a ≠ 0 := by
  intro h
  have h1 := addChar_norm_eq_one ψ a
  rw [h, norm_zero] at h1
  norm_num at h1

/-- Complex conjugation of a finite-group additive character equals negation of its argument. -/
theorem addChar_star_eq_neg {A : Type*} [AddCommGroup A] [Fintype A]
    (ψ : AddChar A ℂ) (a : A) :
    star (ψ a) = ψ (-a) := by
  have hmul : star (ψ a) * ψ a = 1 := by
    rw [Complex.star_def, Complex.conj_mul', addChar_norm_eq_one ψ a]
    norm_num
  have hinv : ψ (-a) * ψ a = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  exact mul_right_cancel₀ (addChar_ne_zero ψ a) (hmul.trans hinv.symm)

theorem addChar_starRingEnd_eq_neg {A : Type*} [AddCommGroup A] [Fintype A]
    (ψ : AddChar A ℂ) (a : A) :
    (starRingEnd ℂ) (ψ a) = ψ (-a) :=
  addChar_star_eq_neg ψ a

/-- **Exact Additive Character Orthogonality on `𝔽^n`**:
for any nontrivial additive character `ψ : AddChar 𝔽 ℂ`,
`∑ y : Fin n → 𝔽, ψ (⟨x, y⟩) = if x = 0 then |𝔽^n| else 0`. -/
theorem sum_psi_dotProd {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] {n : ℕ}
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) (x : Fin n → 𝔽) :
    ∑ y : Fin n → 𝔽, ψ (dotProd x y) =
      if x = 0 then (Fintype.card (Fin n → 𝔽) : ℂ) else 0 := by
  by_cases hx : x = 0
  · subst hx
    simp [AddChar.map_zero_eq_one]
  · rw [if_neg hx]
    have hne : ∃ i₀ : Fin n, x i₀ ≠ 0 := by
      by_contra hAll
      push Not at hAll
      exact hx (funext hAll)
    obtain ⟨i₀, hi₀⟩ := hne
    have hψne : ∃ t : 𝔽, ψ t ≠ 1 := by
      by_contra hAll
      push Not at hAll
      apply hψ
      ext a
      exact hAll a
    obtain ⟨t, ht⟩ := hψne
    let y₀ : Fin n → 𝔽 := Pi.single i₀ (t * (x i₀)⁻¹)
    have hdot : dotProd x y₀ = t := by
      unfold dotProd y₀
      rw [Finset.sum_eq_single i₀]
      · simp [Pi.single_eq_same, mul_comm t, mul_inv_cancel_left₀ hi₀]
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj]
      · intro hmem
        exact absurd (Finset.mem_univ i₀) hmem
    have hshift : ψ t * ∑ y : Fin n → 𝔽, ψ (dotProd x y) =
        ∑ y : Fin n → 𝔽, ψ (dotProd x y) := by
      rw [Finset.mul_sum, ← hdot]
      calc ∑ y : Fin n → 𝔽, ψ (dotProd x y₀) * ψ (dotProd x y)
          = ∑ y : Fin n → 𝔽, ψ (dotProd x (y₀ + y)) := by
              refine Finset.sum_congr rfl fun y _ => ?_
              rw [dotProd_add_right, AddChar.map_add_eq_mul]
        _ = ∑ y : Fin n → 𝔽, ψ (dotProd x y) :=
              Fintype.sum_equiv (Equiv.addLeft y₀) _ _ (fun _ => rfl)
    have hmul : (ψ t - 1) * ∑ y : Fin n → 𝔽, ψ (dotProd x y) = 0 := by
      rw [sub_mul, one_mul, hshift, sub_self]
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr ht)

theorem sum_psi_dotProd_neg {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] {n : ℕ}
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) (x : Fin n → 𝔽) :
    ∑ y : Fin n → 𝔽, ψ (-dotProd x y) =
      if x = 0 then (Fintype.card (Fin n → 𝔽) : ℂ) else 0 := by
  have h : ∑ y : Fin n → 𝔽, ψ (-dotProd x y) = ∑ y : Fin n → 𝔽, ψ (dotProd (-x) y) := by
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [dotProd_neg_left]
  rw [h, sum_psi_dotProd ψ hψ (-x)]
  by_cases hx : x = 0
  · subst hx; simp
  · rw [if_neg (neg_ne_zero.mpr hx), if_neg hx]

/-- Nondegeneracy of `y ↦ ψ(⟨x, y⟩)` on `𝔽^n`. -/
theorem eq_zero_of_forall_psi_dotProd {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] {n : ℕ}
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) {x : Fin n → 𝔽}
    (h : ∀ y : Fin n → 𝔽, ψ (dotProd x y) = 1) : x = 0 := by
  have hsum : ∑ y : Fin n → 𝔽, ψ (dotProd x y) = (Fintype.card (Fin n → 𝔽) : ℂ) := by
    calc ∑ y : Fin n → 𝔽, ψ (dotProd x y)
        = ∑ _y : Fin n → 𝔽, (1 : ℂ) := Finset.sum_congr rfl fun y _ => h y
      _ = (Fintype.card (Fin n → 𝔽) : ℂ) := by simp
  rw [sum_psi_dotProd ψ hψ x] at hsum
  by_contra hx
  rw [if_neg hx] at hsum
  have hcard : (Fintype.card (Fin n → 𝔽) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact hcard hsum.symm

end FiniteFieldCharacters

/-! ## Section 2: Concrete Schrödinger Space `L²(𝔽^n)`, `T_a`, `M_b`, and the Heisenberg Group -/

section SchrodingerHeisenberg

/-- The concrete finite-field Schrödinger Hilbert space `L²(𝔽^n) = EuclideanSpace ℂ (Fin n → 𝔽)`. -/
abbrev SchrodingerSpace (𝔽 : Type*) (n : ℕ) := EuclideanSpace ℂ (Fin n → 𝔽)

/-- Coordinate evaluation of a finite sum in `EuclideanSpace ℂ α`. -/
theorem euclidean_sum_apply {α ι : Type*} (s : Finset ι) (f : ι → EuclideanSpace ℂ α) (x : α) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, PiLp.add_apply, ih]

/-- Explicit coordinate formula for the inner product on `EuclideanSpace ℂ α`
(conjugate-linear in the first argument, matching Mathlib's `InnerProductSpace`). -/
theorem euclidean_inner_eq {α : Type*} [Fintype α] (f g : EuclideanSpace ℂ α) :
    inner ℂ f g = ∑ x : α, star (f x) * g x := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [RCLike.inner_apply, mul_comm, Complex.star_def]

/-- Explicit coordinate formula for the inner product on `SchrodingerSpace 𝔽 n`. -/
theorem schrodinger_inner_eq {𝔽 : Type*} [Fintype 𝔽] {n : ℕ}
    (f g : SchrodingerSpace 𝔽 n) :
    inner ℂ f g = ∑ x : Fin n → 𝔽, star (f x) * g x :=
  euclidean_inner_eq f g

/-- Direct bridge between the Schrödinger inner product and `RHDirect.RallisSeesaw.wip` with
unit weights. -/
theorem schrodinger_inner_eq_wip {𝔽 : Type*} [Fintype 𝔽] {n : ℕ}
    (f g : SchrodingerSpace 𝔽 n) :
    inner ℂ f g = wip (fun _ : Fin n → 𝔽 => (1 : ℂ)) (fun x => f x) (fun x => g x) := by
  rw [schrodinger_inner_eq]
  unfold wip
  simp only [one_mul]

/-- Explicit coordinate formula for the squared norm on `SchrodingerSpace 𝔽 n`. -/
theorem schrodinger_norm_sq {𝔽 : Type*} [Fintype 𝔽] {n : ℕ} (f : SchrodingerSpace 𝔽 n) :
    ‖f‖ ^ 2 = ∑ x : Fin n → 𝔽, ‖f x‖ ^ 2 :=
  EuclideanSpace.norm_sq_eq f

/-- Standard point-mass (delta) basis vector `δ_{x₀}` in `SchrodingerSpace 𝔽 n`. -/
def deltaVec {𝔽 : Type*} [DecidableEq 𝔽] {n : ℕ} (x₀ : Fin n → 𝔽) : SchrodingerSpace 𝔽 n :=
  WithLp.toLp 2 (fun x => if x = x₀ then (1 : ℂ) else 0)

@[simp]
theorem deltaVec_apply {𝔽 : Type*} [DecidableEq 𝔽] {n : ℕ} (x₀ x : Fin n → 𝔽) :
    deltaVec x₀ x = if x = x₀ then (1 : ℂ) else 0 := rfl

theorem inner_deltaVec_left {𝔽 : Type*} [Fintype 𝔽] [DecidableEq 𝔽] {n : ℕ}
    (x₀ : Fin n → 𝔽) (f : SchrodingerSpace 𝔽 n) :
    inner ℂ (deltaVec x₀) f = f x₀ := by
  rw [schrodinger_inner_eq, Finset.sum_eq_single x₀]
  · simp
  · intro x _ hx
    simp [hx]
  · intro h
    exact absurd (Finset.mem_univ x₀) h

theorem inner_deltaVec_deltaVec {𝔽 : Type*} [Fintype 𝔽] [DecidableEq 𝔽] {n : ℕ}
    (x y : Fin n → 𝔽) :
    inner ℂ (deltaVec x) (deltaVec y) = if x = y then (1 : ℂ) else 0 := by
  rw [inner_deltaVec_left, deltaVec_apply]

theorem schrodinger_eq_sum_deltaVec {𝔽 : Type*} [Fintype 𝔽] [DecidableEq 𝔽] {n : ℕ}
    (f : SchrodingerSpace 𝔽 n) :
    f = ∑ x : Fin n → 𝔽, f x • deltaVec x := by
  ext y
  rw [euclidean_sum_apply]
  rw [Finset.sum_eq_single y]
  · simp [PiLp.smul_apply, deltaVec_apply]
  · intro x _ hx
    simp [PiLp.smul_apply, deltaVec_apply, Ne.symm hx]
  · intro h
    exact absurd (Finset.mem_univ y) h

/-- **Translation operator** `(T a f)(x) = f(x + a)` on `SchrodingerSpace 𝔽 n`. -/
def T {𝔽 : Type*} [Add 𝔽] {n : ℕ} (a : Fin n → 𝔽) :
    SchrodingerSpace 𝔽 n →ₗ[ℂ] SchrodingerSpace 𝔽 n where
  toFun f := WithLp.toLp 2 (fun x => f (x + a))
  map_add' _ _ := by ext x; rfl
  map_smul' _ _ := by ext x; rfl

@[simp]
theorem T_apply {𝔽 : Type*} [Add 𝔽] {n : ℕ} (a : Fin n → 𝔽)
    (f : SchrodingerSpace 𝔽 n) (x : Fin n → 𝔽) :
    T a f x = f (x + a) := rfl

/-- **Character-multiplication (modulation) operator** `(M ψ b f)(x) = ψ(⟨b, x⟩) * f(x)`. -/
def M {𝔽 : Type*} [CommSemiring 𝔽] {n : ℕ} (ψ : AddChar 𝔽 ℂ) (b : Fin n → 𝔽) :
    SchrodingerSpace 𝔽 n →ₗ[ℂ] SchrodingerSpace 𝔽 n where
  toFun f := WithLp.toLp 2 (fun x => ψ (dotProd b x) * f x)
  map_add' f g := by
    ext x
    change ψ (dotProd b x) * (f x + g x) = ψ (dotProd b x) * f x + ψ (dotProd b x) * g x
    ring
  map_smul' c f := by
    ext x
    change ψ (dotProd b x) * (c * f x) = c * (ψ (dotProd b x) * f x)
    ring

@[simp]
theorem M_apply {𝔽 : Type*} [CommSemiring 𝔽] {n : ℕ}
    (ψ : AddChar 𝔽 ℂ) (b : Fin n → 𝔽) (f : SchrodingerSpace 𝔽 n) (x : Fin n → 𝔽) :
    M ψ b f x = ψ (dotProd b x) * f x := rfl

@[simp]
theorem T_zero {𝔽 : Type*} [AddMonoid 𝔽] {n : ℕ} :
    T (0 : Fin n → 𝔽) = LinearMap.id := by
  ext f x
  simp

theorem T_comp {𝔽 : Type*} [AddSemigroup 𝔽] {n : ℕ} (a₁ a₂ : Fin n → 𝔽) :
    T a₁ ∘ₗ T a₂ = T (a₁ + a₂) := by
  ext f x
  simp [add_assoc]

@[simp]
theorem M_zero {𝔽 : Type*} [CommSemiring 𝔽] {n : ℕ} (ψ : AddChar 𝔽 ℂ) :
    M ψ (0 : Fin n → 𝔽) = LinearMap.id := by
  ext f x
  simp [AddChar.map_zero_eq_one]

theorem M_comp {𝔽 : Type*} [CommSemiring 𝔽] {n : ℕ}
    (ψ : AddChar 𝔽 ℂ) (b₁ b₂ : Fin n → 𝔽) :
    M ψ b₁ ∘ₗ M ψ b₂ = M ψ (b₁ + b₂) := by
  ext f x
  simp only [LinearMap.comp_apply, M_apply, dotProd_add_left, AddChar.map_add_eq_mul]
  ring

theorem T_deltaVec {𝔽 : Type*} [AddCommGroup 𝔽] [DecidableEq 𝔽] {n : ℕ}
    (a x₀ : Fin n → 𝔽) :
    T a (deltaVec x₀) = deltaVec (x₀ - a) := by
  ext y
  simp only [T_apply, deltaVec_apply]
  congr 1
  exact propext eq_sub_iff_add_eq.symm

theorem M_deltaVec {𝔽 : Type*} [CommSemiring 𝔽] [DecidableEq 𝔽] {n : ℕ}
    (ψ : AddChar 𝔽 ℂ) (b x₀ : Fin n → 𝔽) :
    M ψ b (deltaVec x₀) = ψ (dotProd b x₀) • deltaVec x₀ := by
  ext y
  simp only [M_apply, PiLp.smul_apply, smul_eq_mul, deltaVec_apply]
  by_cases h : y = x₀
  · subst h; simp
  · simp [h]

/-- **Exact Heisenberg Commutation Relation**:
`T a ∘ M ψ b = ψ (⟨a, b⟩) • (M ψ b ∘ T a)`. -/
theorem heisenberg_comm_relation {𝔽 : Type*} [CommSemiring 𝔽] {n : ℕ}
    (ψ : AddChar 𝔽 ℂ) (a b : Fin n → 𝔽) :
    T a ∘ₗ M ψ b = ψ (dotProd a b) • (M ψ b ∘ₗ T a) := by
  ext f x
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, PiLp.smul_apply, smul_eq_mul,
    T_apply, M_apply, dotProd_add_right, AddChar.map_add_eq_mul, dotProd_comm b a]
  ring

/-- **Unitarity of translation `T a`**. -/
theorem T_unitary {𝔽 : Type*} [AddGroup 𝔽] [Fintype 𝔽] {n : ℕ}
    (a : Fin n → 𝔽) (f g : SchrodingerSpace 𝔽 n) :
    inner ℂ (T a f) (T a g) = inner ℂ f g := by
  rw [schrodinger_inner_eq, schrodinger_inner_eq]
  exact Fintype.sum_equiv (Equiv.addRight a) _ _ (fun _ => rfl)

/-- **Adjoint of translation**: `(T a)* = T (-a)`. -/
theorem T_adjoint {𝔽 : Type*} [AddGroup 𝔽] [Fintype 𝔽] {n : ℕ} (a : Fin n → 𝔽) :
    LinearMap.adjoint (T a) = T (-a) := by
  apply LinearMap.ext
  intro g
  refine ext_inner_left ℂ fun f => ?_
  rw [LinearMap.adjoint_inner_right, ← T_unitary (-a) (T a f) g]
  have h : T (-a) (T a f) = f := by
    rw [← LinearMap.comp_apply, T_comp, neg_add_cancel, T_zero, LinearMap.id_apply]
  rw [h]

/-- **Unitarity of character multiplication `M ψ b`**. -/
theorem M_unitary {𝔽 : Type*} [CommRing 𝔽] [Fintype 𝔽] {n : ℕ}
    (ψ : AddChar 𝔽 ℂ) (b : Fin n → 𝔽) (f g : SchrodingerSpace 𝔽 n) :
    inner ℂ (M ψ b f) (M ψ b g) = inner ℂ f g := by
  rw [schrodinger_inner_eq, schrodinger_inner_eq]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [M_apply, star_mul, addChar_star_eq_neg]
  have h1 : ψ (-dotProd b x) * ψ (dotProd b x) = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  calc star (f x) * ψ (-dotProd b x) * (ψ (dotProd b x) * g x)
      = (ψ (-dotProd b x) * ψ (dotProd b x)) * (star (f x) * g x) := by ring
    _ = star (f x) * g x := by rw [h1, one_mul]

/-- **Adjoint of character multiplication**: `(M ψ b)* = M ψ (-b)`. -/
theorem M_adjoint {𝔽 : Type*} [CommRing 𝔽] [Fintype 𝔽] {n : ℕ}
    (ψ : AddChar 𝔽 ℂ) (b : Fin n → 𝔽) :
    LinearMap.adjoint (M ψ b) = M ψ (-b) := by
  apply LinearMap.ext
  intro g
  refine ext_inner_left ℂ fun f => ?_
  rw [LinearMap.adjoint_inner_right, ← M_unitary ψ (-b) (M ψ b f) g]
  have h : M ψ (-b) (M ψ b f) = f := by
    rw [← LinearMap.comp_apply, M_comp, neg_add_cancel, M_zero, LinearMap.id_apply]
  rw [h]

/-- Canonical nondegenerate symplectic form `ω((a₁, b₁), (a₂, b₂)) = ⟨a₁, b₂⟩ - ⟨a₂, b₁⟩`
on `𝔽^n × 𝔽^n`. -/
def sympForm {𝔽 : Type*} [CommRing 𝔽] {n : ℕ} (v w : (Fin n → 𝔽) × (Fin n → 𝔽)) : 𝔽 :=
  dotProd v.1 w.2 - dotProd w.1 v.2

theorem sympForm_antisymm {𝔽 : Type*} [CommRing 𝔽] {n : ℕ}
    (v w : (Fin n → 𝔽) × (Fin n → 𝔽)) :
    sympForm v w = -sympForm w v := by
  unfold sympForm
  ring

theorem sympForm_self {𝔽 : Type*} [CommRing 𝔽] {n : ℕ} (v : (Fin n → 𝔽) × (Fin n → 𝔽)) :
    sympForm v v = 0 := by
  unfold sympForm
  exact sub_self _

/-- Concrete polarized Heisenberg group `Heis 𝔽 n` on `𝔽^n × 𝔽^n × 𝔽` with multiplication
`(a₁, b₁, z₁) * (a₂, b₂, z₂) = (a₁ + a₂, b₁ + b₂, z₁ + z₂ + ⟨a₁, b₂⟩)`. -/
@[ext]
structure Heis (𝔽 : Type*) (n : ℕ) where
  a : Fin n → 𝔽
  b : Fin n → 𝔽
  z : 𝔽

instance {𝔽 : Type*} [Zero 𝔽] {n : ℕ} : One (Heis 𝔽 n) where
  one := ⟨0, 0, 0⟩

instance {𝔽 : Type*} [CommSemiring 𝔽] {n : ℕ} : Mul (Heis 𝔽 n) where
  mul g₁ g₂ := ⟨g₁.a + g₂.a, g₁.b + g₂.b, g₁.z + g₂.z + dotProd g₁.a g₂.b⟩

instance {𝔽 : Type*} [CommRing 𝔽] {n : ℕ} : Inv (Heis 𝔽 n) where
  inv g := ⟨-g.a, -g.b, -g.z + dotProd g.a g.b⟩

instance {𝔽 : Type*} [CommRing 𝔽] {n : ℕ} : Group (Heis 𝔽 n) where
  mul_assoc g₁ g₂ g₃ := by
    apply Heis.ext
    · funext i; exact add_assoc (g₁.a i) (g₂.a i) (g₃.a i)
    · funext i; exact add_assoc (g₁.b i) (g₂.b i) (g₃.b i)
    · change g₁.z + g₂.z + dotProd g₁.a g₂.b + g₃.z + dotProd (g₁.a + g₂.a) g₃.b =
        g₁.z + (g₂.z + g₃.z + dotProd g₂.a g₃.b) + dotProd g₁.a (g₂.b + g₃.b)
      rw [dotProd_add_left, dotProd_add_right]
      ring
  one_mul g := by
    apply Heis.ext
    · funext i; exact zero_add (g.a i)
    · funext i; exact zero_add (g.b i)
    · change 0 + g.z + dotProd 0 g.b = g.z
      simp
  mul_one g := by
    apply Heis.ext
    · funext i; exact add_zero (g.a i)
    · funext i; exact add_zero (g.b i)
    · change g.z + 0 + dotProd g.a 0 = g.z
      simp
  inv_mul_cancel g := by
    apply Heis.ext
    · funext i; exact neg_add_cancel (g.a i)
    · funext i; exact neg_add_cancel (g.b i)
    · change -g.z + dotProd g.a g.b + g.z + dotProd (-g.a) g.b = 0
      rw [dotProd_neg_left]
      ring

/-- Central embedding `z ↦ (0, 0, z)` into `Heis 𝔽 n`. -/
def Heis.center {𝔽 : Type*} [Zero 𝔽] {n : ℕ} (z : 𝔽) : Heis 𝔽 n := ⟨0, 0, z⟩

/-- Translation embedding `a ↦ (a, 0, 0)` into `Heis 𝔽 n`. -/
def Heis.trans {𝔽 : Type*} [Zero 𝔽] {n : ℕ} (a : Fin n → 𝔽) : Heis 𝔽 n := ⟨a, 0, 0⟩

/-- Modulation embedding `b ↦ (0, b, 0)` into `Heis 𝔽 n`. -/
def Heis.mod {𝔽 : Type*} [Zero 𝔽] {n : ℕ} (b : Fin n → 𝔽) : Heis 𝔽 n := ⟨0, b, 0⟩

/-- Exact group commutator in `Heis 𝔽 n` equals the central symplectic cocycle `ω((a₁, b₁), (a₂, b₂))`. -/
theorem Heis.commutator_eq_sympForm {𝔽 : Type*} [CommRing 𝔽] {n : ℕ} (g₁ g₂ : Heis 𝔽 n) :
    g₁ * g₂ * g₁⁻¹ * g₂⁻¹ = Heis.center (sympForm (g₁.a, g₁.b) (g₂.a, g₂.b)) := by
  apply Heis.ext
  · funext i; change g₁.a i + g₂.a i + -g₁.a i + -g₂.a i = 0; ring
  · funext i; change g₁.b i + g₂.b i + -g₁.b i + -g₂.b i = 0; ring
  · change g₁.z + g₂.z + dotProd g₁.a g₂.b + (-g₁.z + dotProd g₁.a g₁.b) +
        dotProd (g₁.a + g₂.a) (-g₁.b) + (-g₂.z + dotProd g₂.a g₂.b) +
        dotProd (g₁.a + g₂.a + -g₁.a) (-g₂.b) =
        dotProd g₁.a g₂.b - dotProd g₂.a g₁.b
    have hsimp : g₁.a + g₂.a + -g₁.a = g₂.a := by funext j; simp
    rw [hsimp, dotProd_add_left, dotProd_neg_right, dotProd_neg_right, dotProd_neg_right]
    ring

/-- **Concrete Schrödinger Representation of `Heis 𝔽 n`** on `SchrodingerSpace 𝔽 n`:
`ρ(a, b, z) = ψ(z) • (M ψ b ∘ₗ T a)`. -/
def schrodingerRep {𝔽 : Type*} [CommRing 𝔽] {n : ℕ} (ψ : AddChar 𝔽 ℂ) :
    Heis 𝔽 n →* Module.End ℂ (SchrodingerSpace 𝔽 n) where
  toFun g := ψ g.z • (M ψ g.b ∘ₗ T g.a)
  map_one' := by
    change ψ 0 • (M ψ 0 ∘ₗ T 0) = LinearMap.id
    simp [AddChar.map_zero_eq_one]
  map_mul' g₁ g₂ := by
    apply LinearMap.ext
    intro f
    ext x
    change ψ (g₁.z + g₂.z + dotProd g₁.a g₂.b) * (ψ (dotProd (g₁.b + g₂.b) x) * f (x + (g₁.a + g₂.a))) =
      ψ g₁.z * (ψ (dotProd g₁.b x) * (ψ g₂.z * (ψ (dotProd g₂.b (x + g₁.a)) * f (x + g₁.a + g₂.a))))
    rw [← add_assoc x g₁.a g₂.a, dotProd_add_left, dotProd_add_right, dotProd_comm g₂.b g₁.a,
      AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
      AddChar.map_add_eq_mul]
    ring

@[simp]
theorem schrodingerRep_center {𝔽 : Type*} [CommRing 𝔽] {n : ℕ} (ψ : AddChar 𝔽 ℂ) (z : 𝔽) :
    schrodingerRep ψ (Heis.center z : Heis 𝔽 n) = ψ z • LinearMap.id := by
  change ψ z • (M ψ 0 ∘ₗ T 0) = ψ z • LinearMap.id
  simp

@[simp]
theorem schrodingerRep_trans {𝔽 : Type*} [CommRing 𝔽] {n : ℕ} (ψ : AddChar 𝔽 ℂ) (a : Fin n → 𝔽) :
    schrodingerRep ψ (Heis.trans a) = T a := by
  change ψ 0 • (M ψ 0 ∘ₗ T a) = T a
  simp [AddChar.map_zero_eq_one]

@[simp]
theorem schrodingerRep_mod {𝔽 : Type*} [CommRing 𝔽] {n : ℕ} (ψ : AddChar 𝔽 ℂ) (b : Fin n → 𝔽) :
    schrodingerRep ψ (Heis.mod b) = M ψ b := by
  change ψ 0 • (M ψ b ∘ₗ T 0) = M ψ b
  simp [AddChar.map_zero_eq_one]

/-- Every element of `Heis 𝔽 n` acts unitarily in the Schrödinger representation. -/
theorem schrodingerRep_unitary {𝔽 : Type*} [CommRing 𝔽] [Fintype 𝔽] {n : ℕ}
    (ψ : AddChar 𝔽 ℂ) (g : Heis 𝔽 n) (f₁ f₂ : SchrodingerSpace 𝔽 n) :
    inner ℂ (schrodingerRep ψ g f₁) (schrodingerRep ψ g f₂) = inner ℂ f₁ f₂ := by
  change inner ℂ (ψ g.z • M ψ g.b (T g.a f₁)) (ψ g.z • M ψ g.b (T g.a f₂)) = inner ℂ f₁ f₂
  rw [inner_smul_left, inner_smul_right, M_unitary, T_unitary,
    addChar_starRingEnd_eq_neg, ← mul_assoc]
  have h1 : ψ (-g.z) * ψ g.z = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  rw [h1, one_mul]

/-- The Hilbert adjoint of `schrodingerRep ψ g` is `schrodingerRep ψ g⁻¹`. -/
theorem schrodingerRep_adjoint {𝔽 : Type*} [CommRing 𝔽] [Fintype 𝔽] {n : ℕ}
    (ψ : AddChar 𝔽 ℂ) (g : Heis 𝔽 n) :
    LinearMap.adjoint (schrodingerRep ψ g) = schrodingerRep ψ g⁻¹ := by
  apply LinearMap.ext
  intro f₂
  refine ext_inner_left ℂ fun f₁ => ?_
  rw [LinearMap.adjoint_inner_right, ← schrodingerRep_unitary ψ g⁻¹ (schrodingerRep ψ g f₁) f₂]
  have h : schrodingerRep ψ g⁻¹ (schrodingerRep ψ g f₁) = f₁ := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [h]

end SchrodingerHeisenberg

/-! ## Section 3: Finite Fourier Transform `ℱ`, Plancherel/Parseval Unitarity, `ℱ² = R` & Weyl Intertwining -/

section FiniteFourierTransform

/-- Real positive normalization factor `|𝔽^n|^{-1/2}` for the unitary finite Fourier transform. -/
def fourierNorm (𝔽 : Type*) [Fintype 𝔽] (n : ℕ) : ℝ :=
  (Real.sqrt (Fintype.card (Fin n → 𝔽) : ℝ))⁻¹

theorem fourierNorm_pos (𝔽 : Type*) [Fintype 𝔽] [Nonempty 𝔽] (n : ℕ) :
    0 < fourierNorm 𝔽 n := by
  unfold fourierNorm
  exact inv_pos.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))

theorem fourierNorm_sq (𝔽 : Type*) [Fintype 𝔽] (n : ℕ) :
    ((fourierNorm 𝔽 n : ℂ) * (fourierNorm 𝔽 n : ℂ)) = (Fintype.card (Fin n → 𝔽) : ℂ)⁻¹ := by
  have hpos : (0 : ℝ) ≤ (Fintype.card (Fin n → 𝔽) : ℝ) := Nat.cast_nonneg _
  have hr : fourierNorm 𝔽 n * fourierNorm 𝔽 n = (Fintype.card (Fin n → 𝔽) : ℝ)⁻¹ := by
    unfold fourierNorm
    rw [← mul_inv, Real.mul_self_sqrt hpos]
  rw [← Complex.ofReal_mul, hr, Complex.ofReal_inv, Complex.ofReal_natCast]

/-- **Normalized Finite Fourier Transform `ℱ`** on `SchrodingerSpace 𝔽 n`:
`(ℱ f)(y) = |𝔽^n|^{-1/2} ∑ x, ψ(⟨x, y⟩) * f(x)`. -/
def fourierOp {𝔽 : Type*} [CommSemiring 𝔽] [Fintype 𝔽] {n : ℕ} (ψ : AddChar 𝔽 ℂ) :
    SchrodingerSpace 𝔽 n →ₗ[ℂ] SchrodingerSpace 𝔽 n where
  toFun f := WithLp.toLp 2 (fun y =>
    (fourierNorm 𝔽 n : ℂ) * ∑ x : Fin n → 𝔽, ψ (dotProd x y) * f x)
  map_add' f g := by
    ext y
    change (fourierNorm 𝔽 n : ℂ) * ∑ x, ψ (dotProd x y) * (f x + g x) =
      (fourierNorm 𝔽 n : ℂ) * ∑ x, ψ (dotProd x y) * f x +
      (fourierNorm 𝔽 n : ℂ) * ∑ x, ψ (dotProd x y) * g x
    simp_rw [mul_add, Finset.sum_add_distrib, mul_add]
  map_smul' c f := by
    ext y
    change (fourierNorm 𝔽 n : ℂ) * ∑ x, ψ (dotProd x y) * (c * f x) =
      c * ((fourierNorm 𝔽 n : ℂ) * ∑ x, ψ (dotProd x y) * f x)
    have h : ∑ x, ψ (dotProd x y) * (c * f x) = c * ∑ x, ψ (dotProd x y) * f x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => by ring
    rw [h]
    ring

@[simp]
theorem fourierOp_apply {𝔽 : Type*} [CommSemiring 𝔽] [Fintype 𝔽] {n : ℕ}
    (ψ : AddChar 𝔽 ℂ) (f : SchrodingerSpace 𝔽 n) (y : Fin n → 𝔽) :
    fourierOp ψ f y = (fourierNorm 𝔽 n : ℂ) * ∑ x : Fin n → 𝔽, ψ (dotProd x y) * f x := rfl

/-- **Reflection operator** `(R f)(x) = f(-x)` on `SchrodingerSpace 𝔽 n`. -/
def reflectOp {𝔽 : Type*} [Neg 𝔽] {n : ℕ} :
    SchrodingerSpace 𝔽 n →ₗ[ℂ] SchrodingerSpace 𝔽 n where
  toFun f := WithLp.toLp 2 (fun x => f (-x))
  map_add' _ _ := by ext x; rfl
  map_smul' _ _ := by ext x; rfl

@[simp]
theorem reflectOp_apply {𝔽 : Type*} [Neg 𝔽] {n : ℕ}
    (f : SchrodingerSpace 𝔽 n) (x : Fin n → 𝔽) :
    reflectOp f x = f (-x) := rfl

theorem reflectOp_sq {𝔽 : Type*} [InvolutiveNeg 𝔽] {n : ℕ} :
    (reflectOp (𝔽 := 𝔽) (n := n)) ∘ₗ reflectOp = LinearMap.id := by
  ext f x
  simp

theorem reflectOp_unitary {𝔽 : Type*} [InvolutiveNeg 𝔽] [Fintype 𝔽] {n : ℕ}
    (f g : SchrodingerSpace 𝔽 n) :
    inner ℂ (reflectOp f) (reflectOp g) = inner ℂ f g := by
  rw [schrodinger_inner_eq, schrodinger_inner_eq]
  exact Fintype.sum_equiv (Equiv.neg (Fin n → 𝔽)) _ _ (fun _ => rfl)

theorem reflectOp_adjoint {𝔽 : Type*} [InvolutiveNeg 𝔽] [Fintype 𝔽] {n : ℕ} :
    LinearMap.adjoint (reflectOp (𝔽 := 𝔽) (n := n)) = reflectOp := by
  apply LinearMap.ext
  intro g
  refine ext_inner_left ℂ fun f => ?_
  rw [LinearMap.adjoint_inner_right, ← reflectOp_unitary (reflectOp f) g]
  have h : reflectOp (reflectOp f) = f := by
    rw [← LinearMap.comp_apply, reflectOp_sq, LinearMap.id_apply]
  rw [h]

/-- **Plancherel / Unitarity Theorem for the Finite Fourier Transform `ℱ`**:
`⟨ℱ f, ℱ g⟩ = ⟨f, g⟩` for every nontrivial `ψ : AddChar 𝔽 ℂ`. -/
theorem fourierOp_unitary {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] {n : ℕ}
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) (f g : SchrodingerSpace 𝔽 n) :
    inner ℂ (fourierOp ψ f) (fourierOp ψ g) = inner ℂ f g := by
  rw [schrodinger_inner_eq, schrodinger_inner_eq]
  have hstar : star (fourierNorm 𝔽 n : ℂ) = (fourierNorm 𝔽 n : ℂ) := Complex.conj_ofReal _
  have hcard : (Fintype.card (Fin n → 𝔽) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc ∑ y : Fin n → 𝔽, star (fourierOp ψ f y) * fourierOp ψ g y
      = ∑ y : Fin n → 𝔽,
          ((fourierNorm 𝔽 n : ℂ) * (fourierNorm 𝔽 n : ℂ)) *
            ∑ x₁ : Fin n → 𝔽, ∑ x₂ : Fin n → 𝔽,
              star (f x₁) * g x₂ * ψ (dotProd (x₂ - x₁) y) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          simp only [fourierOp_apply, star_mul, hstar, star_sum, addChar_star_eq_neg]
          rw [Finset.sum_mul, Finset.sum_mul]
          conv_rhs => rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x₁ _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          conv_rhs => rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x₂ _ => ?_
          rw [dotProd_sub_left, sub_eq_add_neg, AddChar.map_add_eq_mul]
          ring
    _ = (Fintype.card (Fin n → 𝔽) : ℂ)⁻¹ *
          ∑ x₁ : Fin n → 𝔽, ∑ x₂ : Fin n → 𝔽,
            star (f x₁) * g x₂ * ∑ y : Fin n → 𝔽, ψ (dotProd (x₂ - x₁) y) := by
          rw [fourierNorm_sq, ← Finset.mul_sum]
          congr 1
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x₁ _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x₂ _ => (Finset.mul_sum _ _ _).symm
    _ = (Fintype.card (Fin n → 𝔽) : ℂ)⁻¹ *
          ∑ x₁ : Fin n → 𝔽, star (f x₁) * g x₁ * (Fintype.card (Fin n → 𝔽) : ℂ) := by
          congr 1
          refine Finset.sum_congr rfl fun x₁ _ => ?_
          rw [Finset.sum_eq_single x₁]
          · rw [sub_self, sum_psi_dotProd ψ hψ, if_pos rfl]
          · intro x₂ _ hne
            rw [sum_psi_dotProd ψ hψ, if_neg (sub_ne_zero.mpr hne), mul_zero]
          · intro h
            exact absurd (Finset.mem_univ x₁) h
    _ = ∑ x₁ : Fin n → 𝔽, star (f x₁) * g x₁ := by
          rw [← Finset.sum_mul, mul_comm (Fintype.card (Fin n → 𝔽) : ℂ)⁻¹, mul_assoc,
            mul_inv_cancel₀ hcard, mul_one]

/-- **Parseval Identity**: `‖ℱ f‖ ^ 2 = ‖f‖ ^ 2`. -/
theorem fourierOp_parseval {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] {n : ℕ}
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) (f : SchrodingerSpace 𝔽 n) :
    ‖fourierOp ψ f‖ ^ 2 = ‖f‖ ^ 2 := by
  have h := congrArg Complex.re (fourierOp_unitary ψ hψ f f)
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  norm_cast at h

/-- Coordinate Parseval identity: `∑ y, ‖(ℱ f) y‖ ^ 2 = ∑ x, ‖f x‖ ^ 2`. -/
theorem fourierOp_parseval_sum {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] {n : ℕ}
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) (f : SchrodingerSpace 𝔽 n) :
    ∑ y : Fin n → 𝔽, ‖fourierOp ψ f y‖ ^ 2 = ∑ x : Fin n → 𝔽, ‖f x‖ ^ 2 := by
  rw [← schrodinger_norm_sq, ← schrodinger_norm_sq, fourierOp_parseval ψ hψ f]

/-- **Fourier Inversion (`ℱ² = reflection`)**: `fourierOp ψ ∘ₗ fourierOp ψ = reflectOp`. -/
theorem fourierOp_sq_eq_reflect {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] (n : ℕ)
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) :
    fourierOp (n := n) ψ ∘ₗ fourierOp (n := n) ψ = reflectOp (n := n) := by
  have hcard : (Fintype.card (Fin n → 𝔽) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  ext f z
  simp only [LinearMap.comp_apply, fourierOp_apply, reflectOp_apply]
  calc (fourierNorm 𝔽 n : ℂ) * ∑ y : Fin n → 𝔽,
          ψ (dotProd y z) * ((fourierNorm 𝔽 n : ℂ) * ∑ x : Fin n → 𝔽, ψ (dotProd x y) * f x)
      = ((fourierNorm 𝔽 n : ℂ) * (fourierNorm 𝔽 n : ℂ)) *
          ∑ x : Fin n → 𝔽, f x * ∑ y : Fin n → 𝔽, ψ (dotProd (x + z) y) := by
          rw [Finset.mul_sum]
          calc ∑ y : Fin n → 𝔽, (fourierNorm 𝔽 n : ℂ) *
                (ψ (dotProd y z) * ((fourierNorm 𝔽 n : ℂ) * ∑ x, ψ (dotProd x y) * f x))
              = ∑ y : Fin n → 𝔽, ∑ x : Fin n → 𝔽,
                  ((fourierNorm 𝔽 n : ℂ) * (fourierNorm 𝔽 n : ℂ)) *
                    (f x * ψ (dotProd (x + z) y)) := by
                  refine Finset.sum_congr rfl fun y _ => ?_
                  simp only [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun x _ => ?_
                  rw [dotProd_add_left, AddChar.map_add_eq_mul, dotProd_comm y z]
                  ring
            _ = ∑ x : Fin n → 𝔽, ∑ y : Fin n → 𝔽,
                  ((fourierNorm 𝔽 n : ℂ) * (fourierNorm 𝔽 n : ℂ)) *
                    (f x * ψ (dotProd (x + z) y)) := Finset.sum_comm
            _ = ((fourierNorm 𝔽 n : ℂ) * (fourierNorm 𝔽 n : ℂ)) *
                  ∑ x : Fin n → 𝔽, f x * ∑ y : Fin n → 𝔽, ψ (dotProd (x + z) y) := by
                  simp only [Finset.mul_sum]
    _ = (Fintype.card (Fin n → 𝔽) : ℂ)⁻¹ * (f (-z) * (Fintype.card (Fin n → 𝔽) : ℂ)) := by
          rw [fourierNorm_sq]
          congr 1
          rw [Finset.sum_eq_single (-z)]
          · rw [neg_add_cancel, sum_psi_dotProd ψ hψ, if_pos rfl]
          · intro x _ hx
            have hne : x + z ≠ 0 := fun h0 => hx (eq_neg_of_add_eq_zero_left h0)
            rw [sum_psi_dotProd ψ hψ, if_neg hne, mul_zero]
          · intro h
            exact absurd (Finset.mem_univ (-z)) h
    _ = f (-z) := by
          rw [mul_comm (f (-z)), ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

/-- The finite Fourier transform has order dividing `4`: `ℱ⁴ = 1`. -/
theorem fourierOp_pow_four {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] (n : ℕ)
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) :
    (fourierOp (n := n) ψ) ^ 4 = (1 : Module.End ℂ (SchrodingerSpace 𝔽 n)) := by
  have hsq : fourierOp (n := n) ψ * fourierOp (n := n) ψ = reflectOp (n := n) :=
    fourierOp_sq_eq_reflect n ψ hψ
  calc (fourierOp (n := n) ψ) ^ 4
      = (fourierOp (n := n) ψ * fourierOp (n := n) ψ) *
        (fourierOp (n := n) ψ * fourierOp (n := n) ψ) := by
          rw [show (4 : ℕ) = 2 + 2 by rfl, pow_add, sq]
    _ = reflectOp (n := n) * reflectOp (n := n) := by rw [hsq]
    _ = 1 := reflectOp_sq

/-- `ℱ` commutes with reflection `R`. -/
theorem fourierOp_comm_reflect {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] (n : ℕ)
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) :
    fourierOp (n := n) ψ ∘ₗ reflectOp (n := n) = reflectOp (n := n) ∘ₗ fourierOp (n := n) ψ := by
  rw [← fourierOp_sq_eq_reflect n ψ hψ, LinearMap.comp_assoc]

/-- **Adjoint of the Finite Fourier Transform**: `ℱ* = R ∘ ℱ`. -/
theorem fourierOp_adjoint {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] (n : ℕ)
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) :
    LinearMap.adjoint (fourierOp (n := n) ψ) = reflectOp (n := n) ∘ₗ fourierOp (n := n) ψ := by
  apply LinearMap.ext
  intro g
  refine ext_inner_left ℂ fun f => ?_
  rw [LinearMap.adjoint_inner_right, ← fourierOp_unitary ψ hψ (fourierOp (n := n) ψ f) g]
  have h : fourierOp (n := n) ψ (fourierOp (n := n) ψ f) = reflectOp (n := n) f := by
    rw [← LinearMap.comp_apply, fourierOp_sq_eq_reflect n ψ hψ]
  rw [h, ← LinearMap.adjoint_inner_right, reflectOp_adjoint, LinearMap.comp_apply]

theorem fourierOp_comp_adjoint {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] (n : ℕ)
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) :
    fourierOp (n := n) ψ ∘ₗ LinearMap.adjoint (fourierOp (n := n) ψ) = LinearMap.id := by
  rw [fourierOp_adjoint n ψ hψ, ← LinearMap.comp_assoc, fourierOp_comm_reflect n ψ hψ,
    LinearMap.comp_assoc, fourierOp_sq_eq_reflect n ψ hψ, reflectOp_sq]

theorem adjoint_comp_fourierOp {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] (n : ℕ)
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) :
    LinearMap.adjoint (fourierOp (n := n) ψ) ∘ₗ fourierOp (n := n) ψ = LinearMap.id := by
  rw [fourierOp_adjoint n ψ hψ, LinearMap.comp_assoc, fourierOp_sq_eq_reflect n ψ hψ, reflectOp_sq]

/-- **Weyl Element Intertwining (Translation → Modulation)**:
`ℱ ∘ T a = M ψ (-a) ∘ ℱ`. -/
theorem fourierOp_comp_T {𝔽 : Type*} [CommRing 𝔽] [Fintype 𝔽] {n : ℕ}
    (ψ : AddChar 𝔽 ℂ) (a : Fin n → 𝔽) :
    fourierOp ψ ∘ₗ T a = M ψ (-a) ∘ₗ fourierOp ψ := by
  ext f y
  simp only [LinearMap.comp_apply, fourierOp_apply, T_apply, M_apply]
  have hsum : ∑ x : Fin n → 𝔽, ψ (dotProd x y) * f (x + a) =
      ψ (dotProd (-a) y) * ∑ u : Fin n → 𝔽, ψ (dotProd u y) * f u := by
    rw [Finset.mul_sum]
    calc ∑ x : Fin n → 𝔽, ψ (dotProd x y) * f (x + a)
        = ∑ u : Fin n → 𝔽, ψ (dotProd (u - a) y) * f u := by
            refine Fintype.sum_equiv (Equiv.addRight a) _ _ fun x => ?_
            simp
      _ = ∑ u : Fin n → 𝔽, ψ (dotProd (-a) y) * (ψ (dotProd u y) * f u) := by
            refine Finset.sum_congr rfl fun u _ => ?_
            rw [sub_eq_add_neg, dotProd_add_left, AddChar.map_add_eq_mul]
            ring
  rw [hsum]
  ring

/-- **Weyl Element Intertwining (Modulation → Translation)**:
`ℱ ∘ M ψ b = T b ∘ ℱ`. -/
theorem fourierOp_comp_M {𝔽 : Type*} [CommSemiring 𝔽] [Fintype 𝔽] {n : ℕ}
    (ψ : AddChar 𝔽 ℂ) (b : Fin n → 𝔽) :
    fourierOp ψ ∘ₗ M ψ b = T b ∘ₗ fourierOp ψ := by
  ext f y
  simp only [LinearMap.comp_apply, fourierOp_apply, M_apply, T_apply]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [dotProd_add_right, AddChar.map_add_eq_mul, dotProd_comm b x]
  ring

end FiniteFourierTransform

/-! ## Section 4: Stone–von Neumann Theorem (Commutant = Scalars, Irreducibility & Uniqueness) -/

section StoneVonNeumann

/-- Explicit spectral coordinate projector `P_{x₀} = |𝔽^n|⁻¹ ∑ b, ψ(-⟨b, x₀⟩) • M ψ b`
projecting `f ∈ SchrodingerSpace 𝔽 n` onto the line spanned by `δ_{x₀}`. -/
def coordProj {𝔽 : Type*} [CommRing 𝔽] [Fintype 𝔽] {n : ℕ}
    (ψ : AddChar 𝔽 ℂ) (x₀ : Fin n → 𝔽) :
    SchrodingerSpace 𝔽 n →ₗ[ℂ] SchrodingerSpace 𝔽 n :=
  ((Fintype.card (Fin n → 𝔽) : ℂ)⁻¹) •
    ∑ b : Fin n → 𝔽, ψ (-dotProd b x₀) • M ψ b

theorem coordProj_apply {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] {n : ℕ}
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) (x₀ : Fin n → 𝔽) (f : SchrodingerSpace 𝔽 n) :
    coordProj ψ x₀ f = f x₀ • deltaVec x₀ := by
  have hcard : (Fintype.card (Fin n → 𝔽) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  ext x
  simp only [coordProj, LinearMap.smul_apply, LinearMap.sum_apply, PiLp.smul_apply, smul_eq_mul,
    deltaVec_apply]
  rw [euclidean_sum_apply]
  have hsum : ∑ b : Fin n → 𝔽, (ψ (-dotProd b x₀) • M ψ b f) x =
      (∑ b : Fin n → 𝔽, ψ (dotProd (x - x₀) b)) * f x := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [PiLp.smul_apply, smul_eq_mul, M_apply]
    rw [dotProd_sub_left, dotProd_comm x b, dotProd_comm x₀ b, sub_eq_add_neg,
      AddChar.map_add_eq_mul]
    ring
  rw [hsum, sum_psi_dotProd ψ hψ (x - x₀)]
  by_cases hx : x = x₀
  · subst hx
    rw [sub_self, if_pos rfl, if_pos rfl, mul_one, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]
  · rw [if_neg (sub_ne_zero.mpr hx), if_neg hx]
    simp

/-- **Stone–von Neumann Schur Commutant Theorem**:
every linear operator on `SchrodingerSpace 𝔽 n` commuting with all translations `T a` and
character multiplications `M ψ b` (`ψ ≠ 1`) is a scalar multiple of the identity. -/
theorem heis_commutant_eq_scalars {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] {n : ℕ}
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1)
    (A : SchrodingerSpace 𝔽 n →ₗ[ℂ] SchrodingerSpace 𝔽 n)
    (hT : ∀ a : Fin n → 𝔽, A ∘ₗ T a = T a ∘ₗ A)
    (hM : ∀ b : Fin n → 𝔽, A ∘ₗ M ψ b = M ψ b ∘ₗ A) :
    ∃ c : ℂ, A = c • LinearMap.id := by
  have hP : ∀ x₀ : Fin n → 𝔽, A ∘ₗ coordProj ψ x₀ = coordProj ψ x₀ ∘ₗ A := by
    intro x₀
    apply LinearMap.ext
    intro f
    simp only [LinearMap.comp_apply, coordProj, LinearMap.smul_apply, LinearMap.sum_apply,
      map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    have hMb : A (M ψ b f) = M ψ b (A f) := by
      simpa [LinearMap.comp_apply] using congrArg (fun L => L f) (hM b)
    rw [hMb]
  have hdiag : ∀ x₀ : Fin n → 𝔽, A (deltaVec x₀) = (A (deltaVec x₀) x₀) • deltaVec x₀ := by
    intro x₀
    have h1 : A (coordProj ψ x₀ (deltaVec x₀)) = coordProj ψ x₀ (A (deltaVec x₀)) := by
      simpa [LinearMap.comp_apply] using congrArg (fun L => L (deltaVec x₀)) (hP x₀)
    rw [coordProj_apply ψ hψ x₀ (deltaVec x₀), coordProj_apply ψ hψ x₀ (A (deltaVec x₀)),
      deltaVec_apply, if_pos rfl, one_smul] at h1
    exact h1
  set c : ℂ := A (deltaVec 0) 0
  refine ⟨c, ?_⟩
  apply LinearMap.ext
  intro f
  have hbasis : ∀ x₀ : Fin n → 𝔽, A (deltaVec x₀) = c • deltaVec x₀ := by
    intro x₀
    have hTa : A (T (-x₀) (deltaVec 0)) = T (-x₀) (A (deltaVec 0)) := by
      simpa [LinearMap.comp_apply] using congrArg (fun L => L (deltaVec 0)) (hT (-x₀))
    rw [T_deltaVec, zero_sub, neg_neg, hdiag 0, map_smul, T_deltaVec, zero_sub, neg_neg] at hTa
    exact hTa
  conv_lhs => rw [schrodinger_eq_sum_deltaVec f]
  rw [map_sum]
  calc ∑ x : Fin n → 𝔽, A (f x • deltaVec x)
      = ∑ x : Fin n → 𝔽, (c * f x) • deltaVec x := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [map_smul, hbasis x, smul_smul, mul_comm]
    _ = c • ∑ x : Fin n → 𝔽, f x • deltaVec x := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun x _ => by rw [smul_smul]
    _ = (c • LinearMap.id) f := by rw [← schrodinger_eq_sum_deltaVec f]; rfl

/-- **Stone–von Neumann Irreducibility**:
every submodule of `SchrodingerSpace 𝔽 n` invariant under all `T a` and `M ψ b` (`ψ ≠ 1`)
is either `⊥` or `⊤`. -/
theorem schrodinger_irreducible {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] {n : ℕ}
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1)
    (W : Submodule ℂ (SchrodingerSpace 𝔽 n))
    (hT : ∀ a : Fin n → 𝔽, ∀ f ∈ W, T a f ∈ W)
    (hM : ∀ b : Fin n → 𝔽, ∀ f ∈ W, M ψ b f ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  · right
    have hne : ∃ f ∈ W, f ≠ 0 := by
      by_contra hAll
      push Not at hAll
      apply hbot
      rw [Submodule.eq_bot_iff]
      exact hAll
    obtain ⟨f, hfW, hf0⟩ := hne
    have hcoord : ∃ x₀ : Fin n → 𝔽, f x₀ ≠ 0 := by
      by_contra hAll
      push Not at hAll
      apply hf0
      ext x
      exact hAll x
    obtain ⟨x₀, hx₀⟩ := hcoord
    have hPx : coordProj ψ x₀ f ∈ W := by
      simp only [coordProj, LinearMap.smul_apply, LinearMap.sum_apply]
      exact W.smul_mem _ (W.sum_mem fun b _ => W.smul_mem _ (hM b f hfW))
    rw [coordProj_apply ψ hψ x₀ f] at hPx
    have hdx₀ : deltaVec x₀ ∈ W := by
      have hinv := W.smul_mem (f x₀)⁻¹ hPx
      rwa [smul_smul, inv_mul_cancel₀ hx₀, one_smul] at hinv
    have hdx : ∀ x : Fin n → 𝔽, deltaVec x ∈ W := by
      intro x
      have h := hT (x₀ - x) (deltaVec x₀) hdx₀
      rw [T_deltaVec, sub_sub_cancel] at h
      exact h
    rw [Submodule.eq_top_iff']
    intro g
    rw [schrodinger_eq_sum_deltaVec g]
    exact W.sum_mem fun x _ => W.smul_mem _ (hdx x)

/-- Vacuum / modulation-invariant subspace `H₀ = {v ∈ H | ∀ b, π(0, b, 0) v = v}` of any
representation `π` of `Heis 𝔽 n`. -/
def heisVacuumSubspace {𝔽 H : Type*} [CommRing 𝔽] {n : ℕ}
    [AddCommGroup H] [Module ℂ H]
    (π : Heis 𝔽 n →* Module.End ℂ H) : Submodule ℂ H where
  carrier := {v : H | ∀ b : Fin n → 𝔽, π (Heis.mod b) v = v}
  add_mem' {u v} hu hv b := by rw [map_add, hu b, hv b]
  zero_mem' b := map_zero _
  smul_mem' c {v} hv b := by rw [map_smul, hv b]

/-- Vacuum projection operator `P₀ = |𝔽^n|⁻¹ ∑ b, π(0, b, 0)` onto `heisVacuumSubspace π`. -/
def heisVacuumProj {𝔽 H : Type*} [CommRing 𝔽] [Fintype 𝔽] {n : ℕ}
    [AddCommGroup H] [Module ℂ H]
    (π : Heis 𝔽 n →* Module.End ℂ H) : Module.End ℂ H :=
  ((Fintype.card (Fin n → 𝔽) : ℂ)⁻¹) • ∑ b : Fin n → 𝔽, π (Heis.mod b)

theorem heisVacuumProj_mem {𝔽 H : Type*} [CommRing 𝔽] [Fintype 𝔽] {n : ℕ}
    [AddCommGroup H] [Module ℂ H]
    (π : Heis 𝔽 n →* Module.End ℂ H) (w : H) :
    heisVacuumProj π w ∈ heisVacuumSubspace π := by
  intro b₀
  simp only [heisVacuumProj, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum]
  congr 1
  have hmul : ∀ b : Fin n → 𝔽, π (Heis.mod b₀) (π (Heis.mod b) w) = π (Heis.mod (b₀ + b)) w := by
    intro b
    have hgrp : (Heis.mod b₀ : Heis 𝔽 n) * Heis.mod b = Heis.mod (b₀ + b) := by
      apply Heis.ext
      · funext i; change (0 : 𝔽) + 0 = 0; simp
      · rfl
      · change (0 : 𝔽) + 0 + dotProd 0 b = 0; simp
    rw [← Module.End.mul_apply, ← map_mul, hgrp]
  simp_rw [hmul]
  exact Fintype.sum_equiv (Equiv.addLeft b₀) _ _ (fun _ => rfl)

/-- **Exact Heisenberg Vacuum Reconstruction Identity**:
for ANY representation `π` of `Heis 𝔽 n` with nontrivial central character `ψ ≠ 1`,
every vector `w ∈ H` decomposes canonically as `w = ∑ x, π(-x, 0, 0) (P₀ (π(x, 0, 0) w))`. -/
theorem heis_vacuum_decomposition {𝔽 H : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] {n : ℕ}
    [AddCommGroup H] [Module ℂ H]
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) (π : Heis 𝔽 n →* Module.End ℂ H)
    (hcent : ∀ z : 𝔽, π (Heis.center z) = ψ z • LinearMap.id) (w : H) :
    ∑ x : Fin n → 𝔽, π (Heis.trans (-x)) (heisVacuumProj π (π (Heis.trans x) w)) = w := by
  have hcard : (Fintype.card (Fin n → 𝔽) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hconj : ∀ x b : Fin n → 𝔽,
      (Heis.trans (-x) : Heis 𝔽 n) * Heis.mod b * Heis.trans x =
        Heis.center (-dotProd x b) * Heis.mod b := by
    intro x b
    apply Heis.ext
    · funext i; change -x i + 0 + x i = 0 + 0; ring
    · funext i; change 0 + b i + 0 = 0 + b i; ring
    · change 0 + 0 + dotProd (-x) b + 0 + dotProd (-x + 0) 0 =
        -dotProd x b + 0 + dotProd 0 b
      simp [dotProd_neg_left]
  calc ∑ x : Fin n → 𝔽, π (Heis.trans (-x)) (heisVacuumProj π (π (Heis.trans x) w))
      = ((Fintype.card (Fin n → 𝔽) : ℂ)⁻¹) •
          ∑ x : Fin n → 𝔽, ∑ b : Fin n → 𝔽,
            π (Heis.trans (-x) * Heis.mod b * Heis.trans x) w := by
          simp only [heisVacuumProj, LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum,
            ← Finset.smul_sum]
          congr 1
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun b _ => ?_
          rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    _ = ((Fintype.card (Fin n → 𝔽) : ℂ)⁻¹) •
          ∑ b : Fin n → 𝔽, (∑ x : Fin n → 𝔽, ψ (-dotProd x b)) • π (Heis.mod b) w := by
          congr 1
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_smul]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [hconj x b, map_mul, Module.End.mul_apply, hcent (-dotProd x b),
            LinearMap.smul_apply, LinearMap.id_apply]
    _ = ((Fintype.card (Fin n → 𝔽) : ℂ)⁻¹) •
          ((Fintype.card (Fin n → 𝔽) : ℂ) • π (Heis.mod 0) w) := by
          congr 1
          rw [Finset.sum_eq_single 0]
          · have h0 : ∑ x : Fin n → 𝔽, ψ (-dotProd x 0) = (Fintype.card (Fin n → 𝔽) : ℂ) := by
              simp [AddChar.map_zero_eq_one]
            rw [h0]
          · intro b _ hb
            have hsum : ∑ x : Fin n → 𝔽, ψ (-dotProd x b) = 0 := by
              have hcomm : ∑ x : Fin n → 𝔽, ψ (-dotProd x b) =
                  ∑ x : Fin n → 𝔽, ψ (-dotProd b x) :=
                Finset.sum_congr rfl fun x _ => by rw [dotProd_comm]
              rw [hcomm, sum_psi_dotProd_neg ψ hψ b, if_neg hb]
            rw [hsum, zero_smul]
          · intro h
            exact absurd (Finset.mem_univ 0) h
    _ = w := by
          rw [smul_smul, inv_mul_cancel₀ hcard, one_smul]
          have h1 : (Heis.mod (0 : Fin n → 𝔽) : Heis 𝔽 n) = 1 := rfl
          rw [h1, map_one, Module.End.one_apply]

/-- Canonical `Heis 𝔽 n`-intertwiner `Φ_v : SchrodingerSpace 𝔽 n →ₗ[ℂ] H` attached to a vacuum
vector `v ∈ heisVacuumSubspace π`: `Φ_v(f) = ∑ x, f(x) • π(-x, 0, 0) v`. -/
def heisIntertwiner {𝔽 H : Type*} [CommRing 𝔽] [Fintype 𝔽] {n : ℕ}
    [AddCommGroup H] [Module ℂ H]
    (π : Heis 𝔽 n →* Module.End ℂ H) (v : H) :
    SchrodingerSpace 𝔽 n →ₗ[ℂ] H where
  toFun f := ∑ x : Fin n → 𝔽, f x • π (Heis.trans (-x)) v
  map_add' f g := by
    simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => by rw [smul_smul]

/-- `heisIntertwiner π v` intertwines `schrodingerRep ψ` with `π` whenever `v ∈ heisVacuumSubspace π`. -/
theorem heisIntertwiner_equivariant {𝔽 H : Type*} [CommRing 𝔽] [Fintype 𝔽] {n : ℕ}
    [AddCommGroup H] [Module ℂ H]
    (ψ : AddChar 𝔽 ℂ) (π : Heis 𝔽 n →* Module.End ℂ H)
    (hcent : ∀ z : 𝔽, π (Heis.center z) = ψ z • LinearMap.id)
    {v : H} (hv : v ∈ heisVacuumSubspace π) (g : Heis 𝔽 n) (f : SchrodingerSpace 𝔽 n) :
    heisIntertwiner π v (schrodingerRep ψ g f) = π g (heisIntertwiner π v f) := by
  have hT : ∀ a : Fin n → 𝔽, ∀ f' : SchrodingerSpace 𝔽 n,
      heisIntertwiner π v (T a f') = π (Heis.trans a) (heisIntertwiner π v f') := by
    intro a f'
    simp only [heisIntertwiner, LinearMap.coe_mk, AddHom.coe_mk, T_apply, map_sum, map_smul]
    calc ∑ x : Fin n → 𝔽, f' (x + a) • π (Heis.trans (-x)) v
        = ∑ u : Fin n → 𝔽, f' u • π (Heis.trans (a - u)) v := by
            refine Fintype.sum_equiv (Equiv.addRight a) _ _ fun x => ?_
            have hneg : -(x : Fin n → 𝔽) = a - (x + a) := by funext i; simp
            rw [hneg]
            rfl
      _ = ∑ u : Fin n → 𝔽, f' u • π (Heis.trans a) (π (Heis.trans (-u)) v) := by
            refine Finset.sum_congr rfl fun u _ => ?_
            congr 1
            have hgrp : (Heis.trans (a - u) : Heis 𝔽 n) = Heis.trans a * Heis.trans (-u) := by
              apply Heis.ext
              · funext i; change a i - u i = a i + -u i; ring
              · funext i; change (0 : 𝔽) = 0 + 0; simp
              · change (0 : 𝔽) = 0 + 0 + dotProd a 0; simp
            rw [hgrp, map_mul, Module.End.mul_apply]
  have hM : ∀ b : Fin n → 𝔽, ∀ f' : SchrodingerSpace 𝔽 n,
      heisIntertwiner π v (M ψ b f') = π (Heis.mod b) (heisIntertwiner π v f') := by
    intro b f'
    simp only [heisIntertwiner, LinearMap.coe_mk, AddHom.coe_mk, M_apply, map_sum, map_smul]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hrel : (Heis.mod b : Heis 𝔽 n) * Heis.trans (-x) =
        Heis.center (dotProd b x) * (Heis.trans (-x) * Heis.mod b) := by
      apply Heis.ext
      · funext i; change 0 + -x i = 0 + (-x i + 0); ring
      · funext i; change b i + 0 = 0 + (0 + b i); ring
      · change 0 + 0 + dotProd 0 0 =
          dotProd b x + (0 + 0 + dotProd (-x) b) + dotProd 0 (0 + b)
        simp only [dotProd_zero_left, add_zero, zero_add, dotProd_neg_left, dotProd_comm x b]
        ring
    have hact : π (Heis.mod b) (π (Heis.trans (-x)) v) =
        ψ (dotProd b x) • π (Heis.trans (-x)) v := by
      rw [← Module.End.mul_apply, ← map_mul, hrel, map_mul, map_mul,
        Module.End.mul_apply, Module.End.mul_apply, hcent (dotProd b x),
        LinearMap.smul_apply, LinearMap.id_apply, hv b]
    rw [hact, smul_smul, mul_comm]
  have hg : g = Heis.center g.z * (Heis.mod g.b * Heis.trans g.a) := by
    apply Heis.ext
    · funext i; change g.a i = 0 + (0 + g.a i); ring
    · funext i; change g.b i = 0 + (g.b i + 0); ring
    · change g.z = g.z + (0 + 0 + dotProd 0 0) + dotProd 0 (g.b + 0); simp
  change heisIntertwiner π v (ψ g.z • M ψ g.b (T g.a f)) = π g (heisIntertwiner π v f)
  rw [map_smul, hM, hT]
  conv_rhs => rw [hg]
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
    hcent g.z, LinearMap.smul_apply, LinearMap.id_apply]

/-- **Exact Inner-Product Factorization for `heisIntertwiner`**:
for unitary `π` and vacuum vectors `v₁, v₂ ∈ heisVacuumSubspace π`,
`⟨Φ_{v₁}(f), Φ_{v₂}(g)⟩_H = ⟨v₁, v₂⟩_H * ⟨f, g⟩_{L²(𝔽^n)}`. -/
theorem heisIntertwiner_inner {𝔽 H : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] {n : ℕ}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) (π : Heis 𝔽 n →* Module.End ℂ H)
    (hcent : ∀ z : 𝔽, π (Heis.center z) = ψ z • LinearMap.id)
    (hunit : ∀ (g : Heis 𝔽 n) (u w : H), inner ℂ (π g u) (π g w) = inner ℂ u w)
    {v₁ v₂ : H} (hv₁ : v₁ ∈ heisVacuumSubspace π) (hv₂ : v₂ ∈ heisVacuumSubspace π)
    (f g : SchrodingerSpace 𝔽 n) :
    inner ℂ (heisIntertwiner π v₁ f) (heisIntertwiner π v₂ g) =
      inner ℂ v₁ v₂ * inner ℂ f g := by
  have horth : ∀ x y : Fin n → 𝔽,
      inner ℂ (π (Heis.trans (-x)) v₁) (π (Heis.trans (-y)) v₂) =
        if x = y then inner ℂ v₁ v₂ else 0 := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl, hunit]
    · rw [if_neg hxy]
      have hscale : ∀ b : Fin n → 𝔽,
          ψ (dotProd (y - x) b) *
            inner ℂ (π (Heis.trans (-x)) v₁) (π (Heis.trans (-y)) v₂) =
          inner ℂ (π (Heis.trans (-x)) v₁) (π (Heis.trans (-y)) v₂) := by
        intro b
        have hrel : ∀ u : Fin n → 𝔽, ∀ v ∈ heisVacuumSubspace π,
            π (Heis.mod b) (π (Heis.trans (-u)) v) =
              ψ (dotProd b u) • π (Heis.trans (-u)) v := by
          intro u v hv
          have heq : (Heis.mod b : Heis 𝔽 n) * Heis.trans (-u) =
              Heis.center (dotProd b u) * (Heis.trans (-u) * Heis.mod b) := by
            apply Heis.ext
            · funext i; change 0 + -u i = 0 + (-u i + 0); ring
            · funext i; change b i + 0 = 0 + (0 + b i); ring
            · change 0 + 0 + dotProd 0 0 =
                dotProd b u + (0 + 0 + dotProd (-u) b) + dotProd 0 (0 + b)
              simp only [dotProd_zero_left, add_zero, zero_add, dotProd_neg_left, dotProd_comm u b]
              ring
          rw [← Module.End.mul_apply, ← map_mul, heq, map_mul, map_mul,
            Module.End.mul_apply, Module.End.mul_apply, hcent (dotProd b u),
            LinearMap.smul_apply, LinearMap.id_apply, hv b]
        have hu := hunit (Heis.mod b) (π (Heis.trans (-x)) v₁) (π (Heis.trans (-y)) v₂)
        rw [hrel x v₁ hv₁, hrel y v₂ hv₂, inner_smul_left, inner_smul_right,
          addChar_starRingEnd_eq_neg, ← mul_assoc] at hu
        have hchar : ψ (-dotProd b x) * ψ (dotProd b y) = ψ (dotProd (y - x) b) := by
          rw [← AddChar.map_add_eq_mul, dotProd_sub_left, dotProd_comm y b, dotProd_comm x b]
          congr 1
          ring
        rwa [hchar] at hu
      have hsum : (∑ b : Fin n → 𝔽, ψ (dotProd (y - x) b)) *
          inner ℂ (π (Heis.trans (-x)) v₁) (π (Heis.trans (-y)) v₂) =
          (Fintype.card (Fin n → 𝔽) : ℂ) *
            inner ℂ (π (Heis.trans (-x)) v₁) (π (Heis.trans (-y)) v₂) := by
        rw [Finset.sum_mul]
        calc ∑ b : Fin n → 𝔽, ψ (dotProd (y - x) b) *
                inner ℂ (π (Heis.trans (-x)) v₁) (π (Heis.trans (-y)) v₂)
            = ∑ _b : Fin n → 𝔽, inner ℂ (π (Heis.trans (-x)) v₁) (π (Heis.trans (-y)) v₂) :=
                Finset.sum_congr rfl fun b _ => hscale b
          _ = (Fintype.card (Fin n → 𝔽) : ℂ) *
                inner ℂ (π (Heis.trans (-x)) v₁) (π (Heis.trans (-y)) v₂) := by simp
      rw [sum_psi_dotProd ψ hψ (y - x), if_neg (sub_ne_zero.mpr (Ne.symm hxy)), zero_mul] at hsum
      have hcard : (Fintype.card (Fin n → 𝔽) : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      exact (mul_eq_zero.mp hsum.symm).resolve_left hcard
  simp only [heisIntertwiner, LinearMap.coe_mk, AddHom.coe_mk, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right]
  rw [schrodinger_inner_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single x]
  · rw [horth x x, if_pos rfl, Complex.star_def]
    ring
  · intro y _ hy
    rw [horth y x, if_neg hy, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ x) h

/-- **Stone–von Neumann Unitary Uniqueness Theorem**:
every nonzero irreducible unitary representation `(H, π)` of `Heis 𝔽 n` with nontrivial central
character `ψ ≠ 1` is unitarily `Heis 𝔽 n`-equivariantly isomorphic (`SchrodingerSpace 𝔽 n ≃ₗᵢ[ℂ] H`)
to the concrete Schrödinger representation! -/
theorem stone_von_neumann_uniqueness {𝔽 H : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] {n : ℕ}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Nontrivial H]
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) (π : Heis 𝔽 n →* Module.End ℂ H)
    (hcent : ∀ z : 𝔽, π (Heis.center z) = ψ z • LinearMap.id)
    (hunit : ∀ (g : Heis 𝔽 n) (u w : H), inner ℂ (π g u) (π g w) = inner ℂ u w)
    (hirr : ∀ W : Submodule ℂ H, (∀ g : Heis 𝔽 n, ∀ w ∈ W, π g w ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ U : SchrodingerSpace 𝔽 n ≃ₗᵢ[ℂ] H,
      ∀ (g : Heis 𝔽 n) (f : SchrodingerSpace 𝔽 n),
        U (schrodingerRep ψ g f) = π g (U f) := by
  have hvac_ne : ∃ v₀ ∈ heisVacuumSubspace π, v₀ ≠ 0 := by
    by_contra hAll
    push Not at hAll
    obtain ⟨w, hw0⟩ := exists_ne (0 : H)
    have hzero : w = 0 := by
      rw [← heis_vacuum_decomposition ψ hψ π hcent w]
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [hAll _ (heisVacuumProj_mem π (π (Heis.trans x) w)), map_zero]
    exact hw0 hzero
  obtain ⟨v₀, hv₀mem, hv₀ne⟩ := hvac_ne
  let v : H := ((‖v₀‖ : ℝ)⁻¹ : ℂ) • v₀
  have hv_mem : v ∈ heisVacuumSubspace π := (heisVacuumSubspace π).smul_mem _ hv₀mem
  have hv_norm : ‖v‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv₀ne)]
  have hv_inner : inner ℂ v v = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hv_norm]
    simp
  let Φ : SchrodingerSpace 𝔽 n →ₗ[ℂ] H := heisIntertwiner π v
  have hΦ_inner : ∀ f g : SchrodingerSpace 𝔽 n, inner ℂ (Φ f) (Φ g) = inner ℂ f g := by
    intro f g
    rw [heisIntertwiner_inner ψ hψ π hcent hunit hv_mem hv_mem, hv_inner, one_mul]
  have hΦ_norm : ∀ f : SchrodingerSpace 𝔽 n, ‖Φ f‖ = ‖f‖ := by
    intro f
    have hsq : ‖Φ f‖ ^ 2 = ‖f‖ ^ 2 := by
      have h := congrArg Complex.re (hΦ_inner f f)
      rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
      norm_cast at h
    exact (sq_eq_sq₀ (norm_nonneg (Φ f)) (norm_nonneg f)).mp hsq
  have hΦ_inj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    have hn : ‖f‖ = 0 := by rw [← hΦ_norm f, hf, norm_zero]
    exact norm_eq_zero.mp hn
  have hrange_inv : ∀ g : Heis 𝔽 n, ∀ w ∈ LinearMap.range Φ, π g w ∈ LinearMap.range Φ := by
    rintro g _ ⟨f, rfl⟩
    exact ⟨schrodingerRep ψ g f, heisIntertwiner_equivariant ψ π hcent hv_mem g f⟩
  have hrange_ne_bot : LinearMap.range Φ ≠ ⊥ := by
    intro hbot
    have h1 : Φ (deltaVec 0) = 0 := by
      have hmem : Φ (deltaVec 0) ∈ (⊥ : Submodule ℂ H) := hbot ▸ LinearMap.mem_range_self Φ _
      exact (Submodule.mem_bot ℂ).mp hmem
    have hd0 : deltaVec (0 : Fin n → 𝔽) ≠ 0 := by
      intro hz
      have := congrArg (fun f : SchrodingerSpace 𝔽 n => f 0) hz
      simp at this
    exact hd0 (hΦ_inj (h1.trans (map_zero Φ).symm))
  have hrange_top : LinearMap.range Φ = ⊤ :=
    (hirr (LinearMap.range Φ) hrange_inv).resolve_left hrange_ne_bot
  have hΦ_surj : Function.Surjective Φ := LinearMap.range_eq_top.mp hrange_top
  let e : SchrodingerSpace 𝔽 n ≃ₗ[ℂ] H := LinearEquiv.ofBijective Φ ⟨hΦ_inj, hΦ_surj⟩
  let U : SchrodingerSpace 𝔽 n ≃ₗᵢ[ℂ] H :=
    { toLinearEquiv := e
      norm_map' := hΦ_norm }
  exact ⟨U, fun g f => heisIntertwiner_equivariant ψ π hcent hv_mem g f⟩

/-- **Stone–von Neumann Dimension Theorem**:
every nonzero irreducible unitary representation `(H, π)` of `Heis 𝔽 n` with nontrivial central
character `ψ ≠ 1` has exact complex dimension `|𝔽|^n`. -/
theorem stone_von_neumann_finrank {𝔽 H : Type*} [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] {n : ℕ}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Nontrivial H]
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1) (π : Heis 𝔽 n →* Module.End ℂ H)
    (hcent : ∀ z : 𝔽, π (Heis.center z) = ψ z • LinearMap.id)
    (hunit : ∀ (g : Heis 𝔽 n) (u w : H), inner ℂ (π g u) (π g w) = inner ℂ u w)
    (hirr : ∀ W : Submodule ℂ H, (∀ g : Heis 𝔽 n, ∀ w ∈ W, π g w ∈ W) → W = ⊥ ∨ W = ⊤) :
    Module.finrank ℂ H = Fintype.card 𝔽 ^ n := by
  obtain ⟨U, _⟩ := stone_von_neumann_uniqueness ψ hψ π hcent hunit hirr
  rw [← U.toLinearEquiv.finrank_eq, finrank_euclideanSpace, Fintype.card_fun, Fintype.card_fin]

/-- **Stone–von Neumann Mutual Unitary Equivalence**:
any two nonzero irreducible unitary representations `(H₁, π₁)` and `(H₂, π₂)` of `Heis 𝔽 n` with
the same nontrivial central character `ψ ≠ 1` are unitarily `Heis 𝔽 n`-equivariantly isomorphic. -/
theorem stone_von_neumann_equiv_of_irred {𝔽 H₁ H₂ : Type*}
    [Field 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] {n : ℕ}
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [Nontrivial H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [Nontrivial H₂]
    (ψ : AddChar 𝔽 ℂ) (hψ : ψ ≠ 1)
    (π₁ : Heis 𝔽 n →* Module.End ℂ H₁) (π₂ : Heis 𝔽 n →* Module.End ℂ H₂)
    (hcent₁ : ∀ z : 𝔽, π₁ (Heis.center z) = ψ z • LinearMap.id)
    (hcent₂ : ∀ z : 𝔽, π₂ (Heis.center z) = ψ z • LinearMap.id)
    (hunit₁ : ∀ (g : Heis 𝔽 n) (u w : H₁), inner ℂ (π₁ g u) (π₁ g w) = inner ℂ u w)
    (hunit₂ : ∀ (g : Heis 𝔽 n) (u w : H₂), inner ℂ (π₂ g u) (π₂ g w) = inner ℂ u w)
    (hirr₁ : ∀ W : Submodule ℂ H₁, (∀ g : Heis 𝔽 n, ∀ w ∈ W, π₁ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hirr₂ : ∀ W : Submodule ℂ H₂, (∀ g : Heis 𝔽 n, ∀ w ∈ W, π₂ g w ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ U : H₁ ≃ₗᵢ[ℂ] H₂,
      ∀ (g : Heis 𝔽 n) (v : H₁), U (π₁ g v) = π₂ g (U v) := by
  obtain ⟨U₁, hU₁⟩ := stone_von_neumann_uniqueness ψ hψ π₁ hcent₁ hunit₁ hirr₁
  obtain ⟨U₂, hU₂⟩ := stone_von_neumann_uniqueness ψ hψ π₂ hcent₂ hunit₂ hirr₂
  refine ⟨U₁.symm.trans U₂, fun g v => ?_⟩
  simp only [LinearIsometryEquiv.trans_apply]
  have h1 : U₁.symm (π₁ g v) = schrodingerRep ψ g (U₁.symm v) := by
    apply U₁.injective
    rw [U₁.apply_symm_apply, hU₁ g (U₁.symm v), U₁.apply_symm_apply]
  rw [h1, hU₂]

end StoneVonNeumann

/-! ## Section 5: Metaplectic Parabolic Generators & Explicit Seesaw Dual-Pair Intertwiners -/

section WeilParabolicAndSeesaw

/-- **Siegel Levi Weil Operator** `M(g)`: `(weilLevi g f)(x) = f (g⁻¹ x)` on `SchrodingerSpace 𝔽 n`. -/
def weilLevi {𝔽 : Type*} [CommRing 𝔽] {n : ℕ} (g : GL (Fin n) 𝔽) :
    SchrodingerSpace 𝔽 n →ₗ[ℂ] SchrodingerSpace 𝔽 n where
  toFun f := WithLp.toLp 2 (fun x => f (g⁻¹.1.mulVec x))
  map_add' _ _ := by ext x; rfl
  map_smul' _ _ := by ext x; rfl

@[simp]
theorem weilLevi_apply {𝔽 : Type*} [CommRing 𝔽] {n : ℕ} (g : GL (Fin n) 𝔽)
    (f : SchrodingerSpace 𝔽 n) (x : Fin n → 𝔽) :
    weilLevi g f x = f (g⁻¹.1.mulVec x) := rfl

/-- `weilLevi` is a group homomorphism `GL_n(𝔽) →* End ℂ (SchrodingerSpace 𝔽 n)`. -/
def weilLeviHom {𝔽 : Type*} [CommRing 𝔽] {n : ℕ} :
    GL (Fin n) 𝔽 →* Module.End ℂ (SchrodingerSpace 𝔽 n) where
  toFun := weilLevi
  map_one' := by
    ext f x
    simp
  map_mul' g₁ g₂ := by
    ext f x
    change f ((g₁ * g₂)⁻¹.1.mulVec x) = f (g₂⁻¹.1.mulVec (g₁⁻¹.1.mulVec x))
    rw [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec]

/-- Unitarity of the Siegel Levi Weil operator `weilLevi g`. -/
theorem weilLevi_unitary {𝔽 : Type*} [CommRing 𝔽] [Fintype 𝔽] {n : ℕ}
    (g : GL (Fin n) 𝔽) (f₁ f₂ : SchrodingerSpace 𝔽 n) :
    inner ℂ (weilLevi g f₁) (weilLevi g f₂) = inner ℂ f₁ f₂ := by
  rw [schrodinger_inner_eq, schrodinger_inner_eq]
  let e : (Fin n → 𝔽) ≃ (Fin n → 𝔽) :=
    { toFun := fun x => g⁻¹.1.mulVec x
      invFun := fun x => g.1.mulVec x
      left_inv := fun x => by
        dsimp
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      right_inv := fun x => by
        dsimp
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] }
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem weilLevi_adjoint {𝔽 : Type*} [CommRing 𝔽] [Fintype 𝔽] {n : ℕ} (g : GL (Fin n) 𝔽) :
    LinearMap.adjoint (weilLevi g) = weilLevi g⁻¹ := by
  apply LinearMap.ext
  intro f₂
  refine ext_inner_left ℂ fun f₁ => ?_
  rw [LinearMap.adjoint_inner_right, ← weilLevi_unitary g⁻¹ (weilLevi g f₁) f₂]
  have h : weilLevi g⁻¹ (weilLevi g f₁) = f₁ := by
    change (weilLeviHom g⁻¹ * weilLeviHom g) f₁ = f₁
    rw [← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [h]

/-- Exact Heisenberg translation covariance of `weilLevi g`:
`weilLevi g ∘ T a = T (g a) ∘ weilLevi g`. -/
theorem weilLevi_comp_T {𝔽 : Type*} [CommRing 𝔽] {n : ℕ}
    (g : GL (Fin n) 𝔽) (a : Fin n → 𝔽) :
    weilLevi g ∘ₗ T a = T (g.1.mulVec a) ∘ₗ weilLevi g := by
  ext f x
  simp only [LinearMap.comp_apply, weilLevi_apply, T_apply, Matrix.mulVec_add,
    Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

/-- Exact Heisenberg modulation covariance of `weilLevi g`:
`weilLevi g ∘ M ψ b = M ψ ((g⁻¹)ᵀ b) ∘ weilLevi g`. -/
theorem weilLevi_comp_M {𝔽 : Type*} [CommRing 𝔽] {n : ℕ}
    (ψ : AddChar 𝔽 ℂ) (g : GL (Fin n) 𝔽) (b : Fin n → 𝔽) :
    weilLevi g ∘ₗ M ψ b = M ψ ((g⁻¹.1)ᵀ.mulVec b) ∘ₗ weilLevi g := by
  ext f x
  simp only [LinearMap.comp_apply, weilLevi_apply, M_apply, dotProd_mulVec_right]

/-- **Siegel Unipotent / Quadratic-Phase Weil Operator** `U(S)`:
`(weilQuad ψ S f)(x) = ψ(⟨x, S x⟩) * f(x)`. -/
def weilQuad {𝔽 : Type*} [CommSemiring 𝔽] {n : ℕ}
    (ψ : AddChar 𝔽 ℂ) (S : Matrix (Fin n) (Fin n) 𝔽) :
    SchrodingerSpace 𝔽 n →ₗ[ℂ] SchrodingerSpace 𝔽 n where
  toFun f := WithLp.toLp 2 (fun x => ψ (dotProd x (S.mulVec x)) * f x)
  map_add' f g := by
    ext x
    change ψ (dotProd x (S.mulVec x)) * (f x + g x) =
      ψ (dotProd x (S.mulVec x)) * f x + ψ (dotProd x (S.mulVec x)) * g x
    ring
  map_smul' c f := by
    ext x
    change ψ (dotProd x (S.mulVec x)) * (c * f x) = c * (ψ (dotProd x (S.mulVec x)) * f x)
    ring

@[simp]
theorem weilQuad_apply {𝔽 : Type*} [CommSemiring 𝔽] {n : ℕ}
    (ψ : AddChar 𝔽 ℂ) (S : Matrix (Fin n) (Fin n) 𝔽)
    (f : SchrodingerSpace 𝔽 n) (x : Fin n → 𝔽) :
    weilQuad ψ S f x = ψ (dotProd x (S.mulVec x)) * f x := rfl

@[simp]
theorem weilQuad_zero {𝔽 : Type*} [CommSemiring 𝔽] {n : ℕ} (ψ : AddChar 𝔽 ℂ) :
    weilQuad ψ (0 : Matrix (Fin n) (Fin n) 𝔽) = LinearMap.id := by
  ext f x
  simp [AddChar.map_zero_eq_one]

theorem weilQuad_add {𝔽 : Type*} [CommSemiring 𝔽] {n : ℕ}
    (ψ : AddChar 𝔽 ℂ) (S₁ S₂ : Matrix (Fin n) (Fin n) 𝔽) :
    weilQuad ψ (S₁ + S₂) = weilQuad ψ S₁ ∘ₗ weilQuad ψ S₂ := by
  ext f x
  simp only [LinearMap.comp_apply, weilQuad_apply, Matrix.add_mulVec, dotProd_add_right,
    AddChar.map_add_eq_mul]
  ring

theorem weilQuad_unitary {𝔽 : Type*} [CommRing 𝔽] [Fintype 𝔽] {n : ℕ}
    (ψ : AddChar 𝔽 ℂ) (S : Matrix (Fin n) (Fin n) 𝔽)
    (f₁ f₂ : SchrodingerSpace 𝔽 n) :
    inner ℂ (weilQuad ψ S f₁) (weilQuad ψ S f₂) = inner ℂ f₁ f₂ := by
  rw [schrodinger_inner_eq, schrodinger_inner_eq]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [weilQuad_apply, star_mul, addChar_star_eq_neg]
  have h1 : ψ (-dotProd x (S.mulVec x)) * ψ (dotProd x (S.mulVec x)) = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  calc star (f₁ x) * ψ (-dotProd x (S.mulVec x)) * (ψ (dotProd x (S.mulVec x)) * f₂ x)
      = (ψ (-dotProd x (S.mulVec x)) * ψ (dotProd x (S.mulVec x))) * (star (f₁ x) * f₂ x) := by ring
    _ = star (f₁ x) * f₂ x := by rw [h1, one_mul]

theorem weilQuad_adjoint {𝔽 : Type*} [CommRing 𝔽] [Fintype 𝔽] {n : ℕ}
    (ψ : AddChar 𝔽 ℂ) (S : Matrix (Fin n) (Fin n) 𝔽) :
    LinearMap.adjoint (weilQuad ψ S) = weilQuad ψ (-S) := by
  apply LinearMap.ext
  intro f₂
  refine ext_inner_left ℂ fun f₁ => ?_
  rw [LinearMap.adjoint_inner_right, ← weilQuad_unitary ψ (-S) (weilQuad ψ S f₁) f₂]
  have h : weilQuad ψ (-S) (weilQuad ψ S f₁) = f₁ := by
    rw [← LinearMap.comp_apply, ← weilQuad_add, neg_add_cancel, weilQuad_zero, LinearMap.id_apply]
  rw [h]

/-- **Exact Heisenberg Covariance of the Quadratic-Phase Metaplectic Operator**:
for any symmetric matrix `Sᵀ = S`,
`weilQuad ψ (-S) ∘ T a ∘ weilQuad ψ S = ψ(⟨a, S a⟩) • (M ψ (2 • S a) ∘ T a)`. -/
theorem weilQuad_conj_T {𝔽 : Type*} [CommRing 𝔽] {n : ℕ}
    (ψ : AddChar 𝔽 ℂ) {S : Matrix (Fin n) (Fin n) 𝔽}
    (hS : Sᵀ = S) (a : Fin n → 𝔽) :
    weilQuad ψ (-S) ∘ₗ T a ∘ₗ weilQuad ψ S =
      ψ (dotProd a (S.mulVec a)) • (M ψ ((2 : 𝔽) • S.mulVec a) ∘ₗ T a) := by
  ext f x
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, PiLp.smul_apply, smul_eq_mul,
    weilQuad_apply, T_apply, M_apply, Matrix.neg_mulVec, dotProd_neg_right, Matrix.mulVec_add,
    dotProd_add_left, dotProd_add_right, dotProd_smul_left]
  have hsym : dotProd a (S.mulVec x) = dotProd (S.mulVec a) x := by
    rw [dotProd_mulVec_right, hS]
  have hsym2 : dotProd x (S.mulVec a) = dotProd (S.mulVec a) x := by
    rw [dotProd_comm]
  rw [hsym, hsym2, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  ring

/-- **Siegel Parabolic Semidirect Product Relation**:
`weilLevi g ∘ weilQuad ψ S = weilQuad ψ ((g⁻¹)ᵀ * S * g⁻¹) ∘ weilLevi g`. -/
theorem weilLevi_comp_weilQuad {𝔽 : Type*} [CommRing 𝔽] {n : ℕ}
    (ψ : AddChar 𝔽 ℂ) (g : GL (Fin n) 𝔽) (S : Matrix (Fin n) (Fin n) 𝔽) :
    weilLevi g ∘ₗ weilQuad ψ S =
      weilQuad ψ ((g⁻¹.1)ᵀ * S * g⁻¹.1) ∘ₗ weilLevi g := by
  ext f x
  simp only [LinearMap.comp_apply, weilLevi_apply, weilQuad_apply]
  congr 2
  rw [dotProd_mulVec_left, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-! ### Concrete Finite-Field Orthogonal–Symplectic & Hermitian–Unitary Dual-Pair Spaces -/

/-- Canonical trace tensor bilinear form `Ω(X, Y) = tr(Xᵀ * M₁ * Y * M₂)` on `M_{m × n}(𝔽)`. -/
def tensorForm {𝔽 : Type*} [CommRing 𝔽] {m n : ℕ}
    (M₁ : Matrix (Fin m) (Fin m) 𝔽) (M₂ : Matrix (Fin n) (Fin n) 𝔽)
    (X Y : Matrix (Fin m) (Fin n) 𝔽) : 𝔽 :=
  Matrix.trace (Xᵀ * M₁ * Y * M₂)

/-- When `M₁` is symmetric (orthogonal space) and `M₂` is skew-symmetric (symplectic space),
`tensorForm M₁ M₂` is skew-symmetric (a symplectic form on `M_{m × n}(𝔽)`). -/
theorem tensorForm_skew {𝔽 : Type*} [CommRing 𝔽] {m n : ℕ}
    {M₁ : Matrix (Fin m) (Fin m) 𝔽} {M₂ : Matrix (Fin n) (Fin n) 𝔽}
    (h₁ : M₁ᵀ = M₁) (h₂ : M₂ᵀ = -M₂) (X Y : Matrix (Fin m) (Fin n) 𝔽) :
    tensorForm M₁ M₂ Y X = -tensorForm M₁ M₂ X Y := by
  unfold tensorForm
  rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, h₁, h₂]
  simp only [Matrix.neg_mul, Matrix.trace_neg]
  congr 1
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- **Dual-Pair Invariance of the Orthogonal–Symplectic Tensor Form**:
if `g₁ᵀ M₁ g₁ = M₁` (`g₁ ∈ O(M₁)`) and `g₂ᵀ M₂ g₂ = M₂` (`g₂ ∈ Sp(M₂)`), then the commuting
bimodule action `X ↦ g₁ * X * g₂ᵀ` preserves `tensorForm M₁ M₂`. -/
theorem tensorForm_dualPair_invariant {𝔽 : Type*} [CommRing 𝔽] {m n : ℕ}
    {M₁ : Matrix (Fin m) (Fin m) 𝔽} {M₂ : Matrix (Fin n) (Fin n) 𝔽}
    {g₁ : Matrix (Fin m) (Fin m) 𝔽} {g₂ : Matrix (Fin n) (Fin n) 𝔽}
    (hg₁ : g₁ᵀ * M₁ * g₁ = M₁) (hg₂ : g₂ᵀ * M₂ * g₂ = M₂)
    (X Y : Matrix (Fin m) (Fin n) 𝔽) :
    tensorForm M₁ M₂ (g₁ * X * g₂ᵀ) (g₁ * Y * g₂ᵀ) = tensorForm M₁ M₂ X Y := by
  unfold tensorForm
  calc Matrix.trace ((g₁ * X * g₂ᵀ)ᵀ * M₁ * (g₁ * Y * g₂ᵀ) * M₂)
      = Matrix.trace (g₂ * (Xᵀ * (g₁ᵀ * M₁ * g₁) * Y * g₂ᵀ * M₂)) := by
          rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace (Xᵀ * M₁ * Y * (g₂ᵀ * M₂ * g₂)) := by
          rw [hg₁, Matrix.trace_mul_comm]
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace (Xᵀ * M₁ * Y * M₂) := by rw [hg₂]

/-- Involutive conjugate transpose `Xᴴ` of a matrix over `𝔽` with respect to a field involution `σ`. -/
def sigmaConjTranspose {𝔽 : Type*} [Semiring 𝔽] {m n : ℕ} (σ : 𝔽 ≃+* 𝔽)
    (X : Matrix (Fin m) (Fin n) 𝔽) :
    Matrix (Fin n) (Fin m) 𝔽 :=
  (X.map σ)ᵀ

/-- Canonical Hermitian trace tensor form `tr(Xᴴ * H₁ * Y * H₂)` for a unitary dual pair
`(U(H₁), U(H₂))` over `(𝔽, σ)`. -/
def hermTensorForm {𝔽 : Type*} [CommRing 𝔽] {m n : ℕ} (σ : 𝔽 ≃+* 𝔽)
    (H₁ : Matrix (Fin m) (Fin m) 𝔽) (H₂ : Matrix (Fin n) (Fin n) 𝔽)
    (X Y : Matrix (Fin m) (Fin n) 𝔽) : 𝔽 :=
  Matrix.trace (sigmaConjTranspose σ X * H₁ * Y * H₂)

/-- **Dual-Pair Invariance of the Unitary–Unitary Hermitian Tensor Form**:
if `g₁ᴴ H₁ g₁ = H₁` (`g₁ ∈ U(H₁)`) and `g₂ᴴ H₂ g₂ = H₂` (`g₂ ∈ U(H₂)`), then the commuting
bimodule action `X ↦ g₁ * X * g₂ᴴ` preserves `hermTensorForm σ H₁ H₂`. -/
theorem hermTensorForm_dualPair_invariant {𝔽 : Type*} [CommRing 𝔽] {m n : ℕ} (σ : 𝔽 ≃+* 𝔽)
    (hσ : ∀ x : 𝔽, σ (σ x) = x)
    {H₁ : Matrix (Fin m) (Fin m) 𝔽} {H₂ : Matrix (Fin n) (Fin n) 𝔽}
    {g₁ : Matrix (Fin m) (Fin m) 𝔽} {g₂ : Matrix (Fin n) (Fin n) 𝔽}
    (hg₁ : sigmaConjTranspose σ g₁ * H₁ * g₁ = H₁)
    (hg₂ : sigmaConjTranspose σ g₂ * H₂ * g₂ = H₂)
    (X Y : Matrix (Fin m) (Fin n) 𝔽) :
    hermTensorForm σ H₁ H₂ (g₁ * X * sigmaConjTranspose σ g₂)
      (g₁ * Y * sigmaConjTranspose σ g₂) = hermTensorForm σ H₁ H₂ X Y := by
  have hmul : ∀ {p q r : ℕ} (A : Matrix (Fin p) (Fin q) 𝔽) (B : Matrix (Fin q) (Fin r) 𝔽),
      sigmaConjTranspose σ (A * B) = sigmaConjTranspose σ B * sigmaConjTranspose σ A := by
    intro p q r A B
    ext i j
    simp only [sigmaConjTranspose, Matrix.transpose_apply, Matrix.map_apply, Matrix.mul_apply,
      map_sum, map_mul]
    refine Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hinv : ∀ {p q : ℕ} (A : Matrix (Fin p) (Fin q) 𝔽),
      sigmaConjTranspose σ (sigmaConjTranspose σ A) = A := by
    intro p q A
    ext i j
    simp [sigmaConjTranspose, hσ]
  unfold hermTensorForm
  calc Matrix.trace (sigmaConjTranspose σ (g₁ * X * sigmaConjTranspose σ g₂) * H₁ *
          (g₁ * Y * sigmaConjTranspose σ g₂) * H₂)
      = Matrix.trace (g₂ * (sigmaConjTranspose σ X * (sigmaConjTranspose σ g₁ * H₁ * g₁) *
          Y * sigmaConjTranspose σ g₂ * H₂)) := by
          rw [hmul, hmul, hinv]
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace (sigmaConjTranspose σ X * H₁ * Y * (sigmaConjTranspose σ g₂ * H₂ * g₂)) := by
          rw [hg₁, Matrix.trace_mul_comm]
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace (sigmaConjTranspose σ X * H₁ * Y * H₂) := by rw [hg₂]

/-! ### Explicit Dual-Pair Weil Action & Seesaw Dual-Pair Intertwiners -/

/-- Commuting dual-pair Weil action of `G₁ × G₂` on the finite matrix Schrödinger space
`EuclideanSpace ℂ (Matrix (Fin m) (Fin n) 𝔽)` via `ρ₁ : G₁ →* GL_m(𝔽)` and `ρ₂ : G₂ →* GL_n(𝔽)`:
`(ω(g₁, g₂) φ)(X) = φ ((ρ₁ g₁)⁻¹ * X * (ρ₂ g₂))`. -/
def dualPairWeilAction {𝔽 G₁ G₂ : Type*} [CommRing 𝔽] [Group G₁] [Group G₂] {m n : ℕ}
    (ρ₁ : G₁ →* GL (Fin m) 𝔽) (ρ₂ : G₂ →* GL (Fin n) 𝔽) :
    G₁ × G₂ →* Module.End ℂ (EuclideanSpace ℂ (Matrix (Fin m) (Fin n) 𝔽)) where
  toFun g :=
    { toFun := fun φ => WithLp.toLp 2 (fun X => φ ((ρ₁ g.1)⁻¹.1 * X * (ρ₂ g.2).1))
      map_add' := fun _ _ => by ext X; rfl
      map_smul' := fun _ _ => by ext X; rfl }
  map_one' := by
    ext φ X
    change φ ((ρ₁ 1)⁻¹.1 * X * (ρ₂ 1).1) = φ X
    simp
  map_mul' g h := by
    ext φ X
    change φ ((ρ₁ (g.1 * h.1))⁻¹.1 * X * (ρ₂ (g.2 * h.2)).1) =
      φ ((ρ₁ h.1)⁻¹.1 * ((ρ₁ g.1)⁻¹.1 * X * (ρ₂ g.2).1) * (ρ₂ h.2).1)
    simp only [map_mul, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

/-- The dual-pair Weil action `dualPairWeilAction ρ₁ ρ₂` is unitary on `L²(M_{m × n}(𝔽))`. -/
theorem dualPairWeilAction_unitary {𝔽 G₁ G₂ : Type*} [CommRing 𝔽] [Fintype 𝔽]
    [Group G₁] [Group G₂] {m n : ℕ}
    (ρ₁ : G₁ →* GL (Fin m) 𝔽) (ρ₂ : G₂ →* GL (Fin n) 𝔽)
    (g : G₁ × G₂) (φ₁ φ₂ : EuclideanSpace ℂ (Matrix (Fin m) (Fin n) 𝔽)) :
    inner ℂ (dualPairWeilAction ρ₁ ρ₂ g φ₁) (dualPairWeilAction ρ₁ ρ₂ g φ₂) =
      inner ℂ φ₁ φ₂ := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  let e : Matrix (Fin m) (Fin n) 𝔽 ≃ Matrix (Fin m) (Fin n) 𝔽 :=
    { toFun := fun X => (ρ₁ g.1)⁻¹.1 * X * (ρ₂ g.2).1
      invFun := fun X => (ρ₁ g.1).1 * X * (ρ₂ g.2)⁻¹.1
      left_inv := fun X => by
        dsimp
        simp only [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
        rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
      right_inv := fun X => by
        dsimp
        simp only [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
        rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul] }
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- Finite-group theta-kernel `K(g, h) = ⟨φ₁, ω(g, h) φ₂⟩_M` built from a Weil representation
`ω : G × H →* End ℂ M` and Schwartz test vectors `φ₁, φ₂ ∈ M`. -/
def finiteThetaKernel {G H M : Type*} [Group G] [Group H]
    [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    (ω : G × H →* Module.End ℂ M) (φ₁ φ₂ : M) (g : G) (h : H) : ℂ :=
  inner ℂ φ₁ (ω (g, h) φ₂)

/-- Concrete linear theta lift `finiteThetaLift : L²(G) →ₗ[ℂ] L²(H)` from `finiteThetaKernel`. -/
def finiteThetaLift {G H M : Type*} [Group G] [Fintype G] [Group H]
    [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    (ω : G × H →* Module.End ℂ M) (φ₁ φ₂ : M) :
    EuclideanSpace ℂ G →ₗ[ℂ] EuclideanSpace ℂ H where
  toFun f := WithLp.toLp 2 (fun h => ∑ g : G, f g * finiteThetaKernel ω φ₁ φ₂ g h)
  map_add' f₁ f₂ := by
    ext h
    change ∑ g : G, (f₁ g + f₂ g) * finiteThetaKernel ω φ₁ φ₂ g h =
      (∑ g : G, f₁ g * finiteThetaKernel ω φ₁ φ₂ g h) +
      (∑ g : G, f₂ g * finiteThetaKernel ω φ₁ φ₂ g h)
    simp_rw [add_mul, Finset.sum_add_distrib]
  map_smul' c f := by
    ext h
    change ∑ g : G, (c * f g) * finiteThetaKernel ω φ₁ φ₂ g h =
      c * ∑ g : G, f g * finiteThetaKernel ω φ₁ φ₂ g h
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => by ring

/-- Explicit adjoint theta lift `finiteThetaLiftAdj : L²(H) →ₗ[ℂ] L²(G)` using the conjugate
transpose kernel `kerAdj`. -/
def finiteThetaLiftAdj {G H M : Type*} [Group G] [Group H] [Fintype H]
    [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    (ω : G × H →* Module.End ℂ M) (φ₁ φ₂ : M) :
    EuclideanSpace ℂ H →ₗ[ℂ] EuclideanSpace ℂ G where
  toFun u := WithLp.toLp 2 (fun g => ∑ h : H, u h * star (finiteThetaKernel ω φ₁ φ₂ g h))
  map_add' u₁ u₂ := by
    ext g
    change ∑ h : H, (u₁ h + u₂ h) * star (finiteThetaKernel ω φ₁ φ₂ g h) =
      (∑ h : H, u₁ h * star (finiteThetaKernel ω φ₁ φ₂ g h)) +
      (∑ h : H, u₂ h * star (finiteThetaKernel ω φ₁ φ₂ g h))
    simp_rw [add_mul, Finset.sum_add_distrib]
  map_smul' c u := by
    ext g
    change ∑ h : H, (c * u h) * star (finiteThetaKernel ω φ₁ φ₂ g h) =
      c * ∑ h : H, u h * star (finiteThetaKernel ω φ₁ φ₂ g h)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => by ring

/-- **Explicit `RHDirect.RallisSeesaw.SeesawDualPair` Instantiation** for any finite dual-pair
Weil representation `(G, H, ω)` and test vectors `φ₁, φ₂ ∈ M`, directly bridging into
`RHDirect.RallisSeesaw` (`rallis_pairing_eq_normSq`, `lift_ne_zero_iff`, `eigen_swap_finrank`). -/
def finiteThetaSeesawPair {G H M : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
    [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    (ω : G × H →* Module.End ℂ M) (φ₁ φ₂ : M) :
    SeesawDualPair ℂ (EuclideanSpace ℂ G) (EuclideanSpace ℂ H) where
  θ := finiteThetaLift ω φ₁ φ₂
  θAdj := finiteThetaLiftAdj ω φ₁ φ₂
  adjoint_eq f u := by
    have hL : inner ℂ (finiteThetaLift ω φ₁ φ₂ f) u =
        wip (fun _ : H => (1 : ℂ))
          (kerOp (fun _ : G => (1 : ℂ)) (finiteThetaKernel ω φ₁ φ₂) (fun g => f g))
          (fun h => u h) := by
      rw [euclidean_inner_eq]
      unfold wip kerOp finiteThetaLift
      refine Finset.sum_congr rfl fun h _ => ?_
      simp only [one_mul]
      rfl
    have hR : inner ℂ f (finiteThetaLiftAdj ω φ₁ φ₂ u) =
        wip (fun _ : G => (1 : ℂ)) (fun g => f g)
          (kerOp (fun _ : H => (1 : ℂ)) (kerAdj (finiteThetaKernel ω φ₁ φ₂)) (fun h => u h)) := by
      rw [euclidean_inner_eq]
      unfold wip kerOp kerAdj finiteThetaLiftAdj
      refine Finset.sum_congr rfl fun g _ => ?_
      simp only [one_mul]
      rfl
    rw [hL, hR]
    exact kerOp_adjoint _ _ _ _ _ (fun _ => star_one _)

/-- **Rallis Spectral Eigenvalue-Swap for the Finite Weil Theta Lift**:
for any nonzero eigenvalue `μ ≠ 0`, `Θ* ∘ Θ` on `L²(G)` and `Θ ∘ Θ*` on `L²(H)` have identical
`μ`-eigenspace multiplicities (bridging `finiteThetaSeesawPair` directly into
`RHDirect.RallisSeesaw.eigen_swap_finrank`). -/
theorem finiteTheta_eigen_swap {G H M : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
    [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    (ω : G × H →* Module.End ℂ M) (φ₁ φ₂ : M) {μ : ℂ} (hμ : μ ≠ 0) :
    Module.finrank ℂ (Module.End.eigenspace
        (finiteThetaLiftAdj ω φ₁ φ₂ ∘ₗ finiteThetaLift ω φ₁ φ₂) μ) =
      Module.finrank ℂ (Module.End.eigenspace
        (finiteThetaLift ω φ₁ φ₂ ∘ₗ finiteThetaLiftAdj ω φ₁ φ₂) μ) :=
  eigen_swap_finrank (finiteThetaLift ω φ₁ φ₂) (finiteThetaLiftAdj ω φ₁ φ₂) hμ

/-- **Rallis Inner-Product Positivity & Nonvanishing for the Finite Weil Theta Lift**:
direct specialization of `SeesawDualPair.rallis_pairing_eq_normSq` and `lift_ne_zero_iff`. -/
theorem finiteTheta_rallis_criterion {G H M : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
    [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    (ω : G × H →* Module.End ℂ M) (φ₁ φ₂ : M) (f : EuclideanSpace ℂ G) :
    inner ℂ f (finiteThetaLiftAdj ω φ₁ φ₂ (finiteThetaLift ω φ₁ φ₂ f)) =
      ((‖finiteThetaLift ω φ₁ φ₂ f‖ ^ 2 : ℝ) : ℂ) ∧
    (finiteThetaLift ω φ₁ φ₂ f ≠ 0 ↔
      inner ℂ f (finiteThetaLiftAdj ω φ₁ φ₂ (finiteThetaLift ω φ₁ φ₂ f)) ≠ 0) :=
  ⟨(finiteThetaSeesawPair ω φ₁ φ₂).rallis_pairing_eq_normSq f,
   (finiteThetaSeesawPair ω φ₁ φ₂).lift_ne_zero_iff f⟩

/-- **Exact Kudla–Rallis Seesaw Intertwiner Identity**:
given a seesaw diagram of subgroups `ιG : G₂ →* G₁` and `ιH : H₁ →* H₂` with compatible Weil
representations `ω₁ : G₁ × H₁ →* End ℂ M` and `ω₂ : G₂ × H₂ →* End ℂ M` satisfying
`ω₁ (ιG g₂, h₁) = ω₂ (g₂, ιH h₁)`, the restriction of the `G₂ → H₂` theta lift to `H₁` is the
exact Hilbert adjoint of the restriction of the `H₁ → G₁` adjoint lift to `G₂`:
`⟨Res_{H₁}^{H₂} (Θ₂ f), u⟩_{H₁} = ⟨f, Res_{G₂}^{G₁} (Θ₁* u)⟩_{G₂}`. -/
theorem seesaw_intertwiner_identity {G₁ G₂ H₁ H₂ M : Type*}
    [Group G₁] [Group G₂] [Fintype G₂]
    [Group H₁] [Fintype H₁] [Group H₂]
    [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    (ιG : G₂ →* G₁) (ιH : H₁ →* H₂)
    (ω₁ : G₁ × H₁ →* Module.End ℂ M) (ω₂ : G₂ × H₂ →* Module.End ℂ M)
    (hseesaw : ∀ (g₂ : G₂) (h₁ : H₁), ω₁ (ιG g₂, h₁) = ω₂ (g₂, ιH h₁))
    (φ₁ φ₂ : M) (f : EuclideanSpace ℂ G₂) (u : EuclideanSpace ℂ H₁) :
    inner ℂ (WithLp.toLp 2 (fun h₁ : H₁ => finiteThetaLift ω₂ φ₁ φ₂ f (ιH h₁))) u =
      inner ℂ f (WithLp.toLp 2 (fun g₂ : G₂ => finiteThetaLiftAdj ω₁ φ₁ φ₂ u (ιG g₂))) := by
  rw [euclidean_inner_eq, euclidean_inner_eq]
  have hker : ∀ (g₂ : G₂) (h₁ : H₁),
      finiteThetaKernel ω₂ φ₁ φ₂ g₂ (ιH h₁) = finiteThetaKernel ω₁ φ₁ φ₂ (ιG g₂) h₁ := by
    intro g₂ h₁
    unfold finiteThetaKernel
    rw [hseesaw g₂ h₁]
  simp only [finiteThetaLift, finiteThetaLiftAdj, LinearMap.coe_mk, AddHom.coe_mk,
    PiLp.toLp_apply, star_sum, star_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g₂ _ => Finset.sum_congr rfl fun h₁ _ => ?_
  rw [hker g₂ h₁]
  ring

/-- **Direct-Sum Seesaw Splitting Factorization**:
for a direct-sum Weil pair `(G₁ × G₂, H)` acting diagonally on `M₁` and `M₂` via `ω₁`, `ω₂` with
product kernel `K₁(g₁, h) * K₂(g₂, h)`, the theta lift of a pure tensor `f₁ ⊗ f₂` equals the
pointwise product of the individual theta lifts `Θ₁(f₁) · Θ₂(f₂)`. -/
theorem finiteTheta_split_product {G₁ G₂ H M₁ M₂ : Type*}
    [Group G₁] [Fintype G₁] [Group G₂] [Fintype G₂] [Group H]
    [NormedAddCommGroup M₁] [InnerProductSpace ℂ M₁]
    [NormedAddCommGroup M₂] [InnerProductSpace ℂ M₂]
    (ω₁ : G₁ × H →* Module.End ℂ M₁) (ω₂ : G₂ × H →* Module.End ℂ M₂)
    (φ₁ ψ₁ : M₁) (φ₂ ψ₂ : M₂)
    (f₁ : EuclideanSpace ℂ G₁) (f₂ : EuclideanSpace ℂ G₂) (h : H) :
    (∑ p : G₁ × G₂, (f₁ p.1 * f₂ p.2) *
        (finiteThetaKernel ω₁ φ₁ ψ₁ p.1 h * finiteThetaKernel ω₂ φ₂ ψ₂ p.2 h)) =
      finiteThetaLift ω₁ φ₁ ψ₁ f₁ h * finiteThetaLift ω₂ φ₂ ψ₂ f₂ h := by
  rw [Fintype.sum_prod_type]
  simp only [finiteThetaLift, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun g₁ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun g₂ _ => ?_
  ring

/-- **Equivariance of the Finite Weil Theta Kernel**:
when `ω : G × H →* End ℂ M` is unitary,
`K_{ω(g₀, h₀) φ₁, φ₂}(g, h) = K_{φ₁, φ₂}(g₀⁻¹ * g, h₀⁻¹ * h)`. -/
theorem finiteThetaKernel_equivariant {G H M : Type*} [Group G] [Group H]
    [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    (ω : G × H →* Module.End ℂ M)
    (hunit : ∀ (p : G × H) (x y : M), inner ℂ (ω p x) (ω p y) = inner ℂ x y)
    (φ₁ φ₂ : M) (g₀ g : G) (h₀ h : H) :
    finiteThetaKernel ω (ω (g₀, h₀) φ₁) φ₂ g h =
      finiteThetaKernel ω φ₁ φ₂ (g₀⁻¹ * g) (h₀⁻¹ * h) := by
  unfold finiteThetaKernel
  rw [← hunit (g₀⁻¹, h₀⁻¹) (ω (g₀, h₀) φ₁) (ω (g, h) φ₂)]
  have h1 : ω (g₀⁻¹, h₀⁻¹) (ω (g₀, h₀) φ₁) = φ₁ := by
    rw [← Module.End.mul_apply, ← map_mul]
    have hp : ((g₀⁻¹, h₀⁻¹) : G × H) * (g₀, h₀) = 1 := by
      ext <;> simp
    rw [hp, map_one, Module.End.one_apply]
  have h2 : ω (g₀⁻¹, h₀⁻¹) (ω (g, h) φ₂) = ω (g₀⁻¹ * g, h₀⁻¹ * h) φ₂ := by
    rw [← Module.End.mul_apply, ← map_mul]
    rfl
  rw [h1, h2]

end WeilParabolicAndSeesaw

end

end RHDirect.Stage2WeilMetaplectic
