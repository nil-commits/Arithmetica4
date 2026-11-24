import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Length

/-!
# RHDirect.Stage12GMAReducibility

Unconditional (`0` assumptions, `0` `sorry`, `0` custom `axiom`s, `0` `native_decide`, pure Mathlib
`v4.33.1`) formalization of **Phase C / Stage 12 (4 of 9)**:

1. **Concrete Bellaïche–Chenevier Generalized Matrix Algebras (`GMA R d`) & Total Reducibility
   Ideal (`I_red`, `gma_reducibility_ideal_minimal`)**:
   - Concrete rank-`d` GMA over a commutative ring `R` using explicit `Fin d × Fin d` block modules
     `Block i j`, diagonal identifications `diagEquiv i : Block i i ≃ₗ[R] R`, associative block
     multiplication `mul i j k`, and trace commutativity `(COMM)` — completely free of
     `Algebra`/`SMul` typeclass diamonds.
   - Explicit ring structure on `GMA.Elem A`, orthogonal idempotents `idemp i`, central trace
     `tr : A.Elem →+ R` (`tr (x * y) = tr (y * x)`), standard matrix GMA `matrixGMA R d`, and
     non-trivial ideal-weighted GMAs `idealGMA R d I`.
   - Total reducibility ideal `reducibilityIdeal A = ⨆_{i ≠ j} pairIdeal i j` and
     **Bellaïche–Chenevier Theorem 1.5.1 (`gma_reducibility_ideal_minimal`)**: for a GMA generated
     by `ρ : G →* A.Elem` with lifted idempotents, a ring homomorphism `f : R →+* S` splits the
     trace pseudocharacter into a sum of `d` adapted characters iff `A.reducibilityIdeal ≤ ker f`
     (iff `f` factors uniquely through `R ⧸ A.reducibilityIdeal`).

2. **Bellaïche–Chenevier `Ext¹` Injection (`gma_ext_injection` / `LemmaP`) & Selmer Length Bounds**:
   - Concrete 1-cocycles `Ext1Cocycle`, 1-coboundaries `Ext1Coboundary`, and quotient
     `Ext1Char χ_i χ_j M ≃ Ext¹_G(χ_j, χ_i; M)`.
   - Reducible block submodule `B'_{i,j} = I_red · A_{i,j} + ∑_{k ≠ i, j} A_{i,k} A_{k,j}` and
     `S`-module `GMARedHom A f i j M` of `f`-semilinear homomorphisms `A_{i,j} / B'_{i,j} → M`.
   - **Bellaïche–Chenevier Theorem 1.5.5 (`gma_ext_injection`)**: exact `S`-linear injection
     `GMARedHom A f i j M ↪ Ext1Char χ_i χ_j M`, specialized to `d = 3` (`U(3)`, `CountI`) and
     `d = 4` (`Sp₄`, `CountII`/`CountIII`).
   - Exact module-length bounds `length_gmaRedHom_le_ext1`,
     `selmer_length_le_reducibility_length`, and Cayley–Hamilton / monic-polynomial DVR valuation
     bound `reducibility_comap_length_le_sum_val` connecting `len(𝒪 / (I_red ∩ 𝒪))` to
     `∑_ρ v_ϖ(t_ρ - t_eis)`.

3. **Concrete 3D `U(3)` (`CountI`) & 4D `Sp₄` (`CountII`/`CountIII`) Reducible Pseudocharacter
   Families & Complex-Conjugation Parity Forcing**:
   - General GMA anti-involutions `GMAInvolution A σ` with induced ring anti-involution `τElem`,
     trace preservation, and pair-ideal invariance.
   - Explicit 3D conjugate-self-dual unitary involution `u3MatrixInvolution` (`X ↦ J₃ Xᵀ J₃`),
     block duality `A_{0,1} ≃ A_{1,2}`, reducibility ideal collapse
     `I_red = pairIdeal 0 1 ⊔ pairIdeal 0 2`, and Eisenstein trace identity
     `tr(ρ(g)) ≡ Ψ(g) + 1 + Ψ(g)⁻¹ (mod I_red)`.
   - Explicit 4D symplectic involution `sp4MatrixInvolution` (`X ↦ -J₄ Xᵀ J₄`), block dualities
     `A_{0,1} ≃ A_{2,3}` and `A_{0,2} ≃ A_{1,3}`, anti-diagonal minus signs, reducibility ideal
     collapse to 4 pair ideals, and `Sp₄` Eisenstein trace identity.
   - Exact odd-prime (`IsUnit 2`) complex-conjugation parity forcing (`gma_conj_block_action`,
     `gma_ext_parity_forcing`, `involution_eigenspace_decomp`, `u3_plus_parity_forcing`,
     `sp4_plus_parity_forcing`).

4. **Unconditional Single Global Resultant Integer Bound (`CorGSumLog`,
   `frobenius_trace_norm_nonzero_log_bound`, & Pure Polynomial `(condF E * t)^C` Bound)**:
   - Exact prime-sum theorem `corG_sum_log` and two-auxiliary-prime elimination
     `corG_two_primes_sum_log`.
   - Archimedean Eisenstein separation `eisenstein_trace_archimedean_separation` (`q ≥ 7`, `e ≥ 1`,
     `‖t‖ ≤ √q + 2` ⇒ `t ≠ eis3 q e z` and `log ‖q^e (t - eis3 q e z)‖ ≤ 2 e log q + 1`) and its
     4D `Sp₄` counterpart `sp4_eisenstein_trace_archimedean_separation`.
   - Constructive integer resultant `resultantInt T Q := det(aeval T Q) ∈ ℤ` for finite-rank
     integral Frobenius operators `T : Matrix (Fin n) (Fin n) ℤ`, proved unconditionally to satisfy:
     - `resultantInt T Q ≠ 0`,
     - `Real.log |resultantInt T Q| ≤ n * Q.natDegree * (2 * e * Real.log q + 1)`,
     - `∑ v_l(α_j - β_o) ≤ padicValInt l (resultantInt T Q)` in `ℤ_[l]` for every prime `l`.
   - End-to-end global pure polynomial bound `global_plus_selmer_pure_poly_bound`:
     `∑_{l ∈ Ls} Real.log l * ∑_{k=1}^{t-1} len(l, k) ≤ (condF * t)^C` across ALL good odd primes
     simultaneously!
-/

noncomputable section

open scoped BigOperators Pointwise
open Finset Matrix Polynomial

namespace RHDirect
namespace Stage12GMAReducibility

/-! ## Section 1: Concrete Bellaïche–Chenevier Generalized Matrix Algebras (`GMA R d`) & Reducibility Ideal -/

section GMABasic

/-- A concrete rank-`d` Bellaïche–Chenevier **Generalized Matrix Algebra (GMA)** over a commutative
ring `R`. Diagonal blocks `Block i i` are explicitly identified with `R` via `diagEquiv i`, and
block multiplication `mul i j k` is associative and satisfies the trace-commutativity law `(COMM)`.
All ring/module operations are explicit to prevent `Algebra`/`SMul` typeclass diamonds. -/
structure GMA (R : Type*) [CommRing R] (d : ℕ) where
  Block : Fin d → Fin d → Type*
  blockAdd : ∀ i j : Fin d, AddCommGroup (Block i j)
  blockMod : ∀ i j : Fin d, @Module R (Block i j) _ (blockAdd i j).toAddCommMonoid
  diagEquiv : ∀ i : Fin d, @LinearEquiv R R _ _ (RingHom.id R) (RingHom.id R) _ _
    (Block i i) R (blockAdd i i).toAddCommMonoid _ (blockMod i i) _
  mul : ∀ i j k : Fin d,
    @LinearMap R R _ _ (RingHom.id R) (Block i j)
      (@LinearMap R R _ _ (RingHom.id R) (Block j k) (Block i k)
        (blockAdd j k).toAddCommMonoid (blockAdd i k).toAddCommMonoid
        (blockMod j k) (blockMod i k))
      (blockAdd i j).toAddCommMonoid _ (blockMod i j) _
  mul_diag_left : ∀ (i j : Fin d) (r : R) (x : Block i j),
    mul i i j ((diagEquiv i).symm r) x = @HSMul.hSMul R (Block i j) (Block i j)
      (@instHSMul R (Block i j) (blockMod i j).toSMul) r x
  mul_diag_right : ∀ (i j : Fin d) (x : Block i j) (r : R),
    mul i j j x ((diagEquiv j).symm r) = @HSMul.hSMul R (Block i j) (Block i j)
      (@instHSMul R (Block i j) (blockMod i j).toSMul) r x
  block_mul_assoc : ∀ (i j k l : Fin d) (x : Block i j) (y : Block j k) (z : Block k l),
    mul i j l x (mul j k l y z) = mul i k l (mul i j k x y) z
  mul_comm_trace : ∀ (i j : Fin d) (x : Block i j) (y : Block j i),
    diagEquiv i (mul i j i x y) = diagEquiv j (mul j i j y x)

namespace GMA

variable {R : Type*} [CommRing R] {d : ℕ} (A : GMA R d)

attribute [local instance] GMA.blockAdd GMA.blockMod

/-- Local helper exposing the `AddCommGroup` instance on each block `A.Block i j`. -/
scoped instance instBlockAdd (i j : Fin d) : AddCommGroup (A.Block i j) :=
  A.blockAdd i j

/-- Local helper exposing the `Module R` instance on each block `A.Block i j`. -/
scoped instance instBlockMod (i j : Fin d) : Module R (A.Block i j) :=
  A.blockMod i j

/-- An element of the GMA `A`, stored as a `Fin d × Fin d` array of block entries. -/
@[ext]
structure Elem where
  entry : ∀ i j : Fin d, A.Block i j

variable {A}

instance : Zero A.Elem := ⟨⟨fun _ _ => 0⟩⟩

instance : One A.Elem :=
  ⟨⟨fun i j => if h : i = j then h ▸ (A.diagEquiv i).symm 1 else 0⟩⟩

instance : Add A.Elem := ⟨fun x y => ⟨fun i j => x.entry i j + y.entry i j⟩⟩

instance : Neg A.Elem := ⟨fun x => ⟨fun i j => -x.entry i j⟩⟩

instance : Sub A.Elem := ⟨fun x y => ⟨fun i j => x.entry i j - y.entry i j⟩⟩

instance : Mul A.Elem :=
  ⟨fun x y => ⟨fun i k => ∑ j : Fin d, A.mul i j k (x.entry i j) (y.entry j k)⟩⟩

@[simp] theorem zero_entry (i j : Fin d) : (0 : A.Elem).entry i j = 0 := rfl

@[simp] theorem one_entry_diag (i : Fin d) :
    (1 : A.Elem).entry i i = (A.diagEquiv i).symm 1 := by
  show (if h : i = i then h ▸ (A.diagEquiv i).symm 1 else 0) = _
  simp

@[simp] theorem one_entry_off {i j : Fin d} (h : i ≠ j) :
    (1 : A.Elem).entry i j = 0 :=
  dif_neg h

@[simp] theorem add_entry (x y : A.Elem) (i j : Fin d) :
    (x + y).entry i j = x.entry i j + y.entry i j := rfl

@[simp] theorem neg_entry (x : A.Elem) (i j : Fin d) :
    (-x).entry i j = -x.entry i j := rfl

@[simp] theorem sub_entry (x y : A.Elem) (i j : Fin d) :
    (x - y).entry i j = x.entry i j - y.entry i j := rfl

@[simp] theorem mul_entry (x y : A.Elem) (i k : Fin d) :
    (x * y).entry i k = ∑ j : Fin d, A.mul i j k (x.entry i j) (y.entry j k) := rfl

/-- Explicit `R`-scalar multiplication on `A.Elem` (entrywise). -/
def smulElem (r : R) (x : A.Elem) : A.Elem :=
  ⟨fun i j => r • x.entry i j⟩

@[simp] theorem smulElem_entry (r : R) (x : A.Elem) (i j : Fin d) :
    (smulElem r x).entry i j = r • x.entry i j := rfl

instance instRingElem : Ring A.Elem where
  add_assoc x y z := by ext i j; exact add_assoc (x.entry i j) (y.entry i j) (z.entry i j)
  zero_add x := by ext i j; exact zero_add (x.entry i j)
  add_zero x := by ext i j; exact add_zero (x.entry i j)
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel x := by ext i j; exact neg_add_cancel (x.entry i j)
  add_comm x y := by ext i j; exact add_comm (x.entry i j) (y.entry i j)
  sub_eq_add_neg x y := by ext i j; exact sub_eq_add_neg (x.entry i j) (y.entry i j)
  left_distrib x y z := by
    ext i k
    simp only [mul_entry, add_entry, map_add, Finset.sum_add_distrib]
  right_distrib x y z := by
    ext i k
    simp only [mul_entry, add_entry, map_add, LinearMap.add_apply, Finset.sum_add_distrib]
  zero_mul x := by
    ext i k
    simp only [mul_entry, zero_entry, map_zero, LinearMap.zero_apply, Finset.sum_const_zero]
  mul_zero x := by
    ext i k
    simp only [mul_entry, zero_entry, map_zero, Finset.sum_const_zero]
  mul_assoc x y z := by
    ext i l
    simp only [mul_entry, map_sum, LinearMap.sum_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    exact (A.block_mul_assoc i j k l (x.entry i j) (y.entry j k) (z.entry k l)).symm
  one_mul x := by
    ext i k
    rw [mul_entry, Finset.sum_eq_single i]
    · rw [one_entry_diag, A.mul_diag_left, one_smul]
    · intro j _ hji
      rw [one_entry_off hji.symm, map_zero, LinearMap.zero_apply]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  mul_one x := by
    ext i k
    rw [mul_entry, Finset.sum_eq_single k]
    · rw [one_entry_diag, A.mul_diag_right, one_smul]
    · intro j _ hjk
      rw [one_entry_off hjk, map_zero]
    · intro hk; exact absurd (Finset.mem_univ k) hk

theorem sum_entry {ι : Type*} (s : Finset ι) (f : ι → A.Elem) (a b : Fin d) :
    (∑ i ∈ s, f i).entry a b = ∑ i ∈ s, (f i).entry a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert c s hc ih =>
    rw [Finset.sum_insert hc, Finset.sum_insert hc, add_entry, ih]

/-- Canonical diagonal ring homomorphism `R →+* A.Elem`, `r ↦ diag(r, …, r)`. -/
def scalarHom (A : GMA R d) : R →+* A.Elem where
  toFun r := ⟨fun i j => if h : i = j then h ▸ (A.diagEquiv i).symm r else 0⟩
  map_one' := rfl
  map_mul' r s := by
    ext i k
    by_cases hik : i = k
    · subst hik
      rw [mul_entry, Finset.sum_eq_single i]
      · simp only [↓reduceDIte]
        rw [A.mul_diag_left, ← map_smul, smul_eq_mul]
      · intro j _ hji
        simp [hji.symm]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    · simp only [hik, ↓reduceDIte, mul_entry]
      refine (Finset.sum_eq_zero fun j _ => ?_).symm
      by_cases hij : i = j
      · subst hij; simp [hik]
      · simp [hij]
  map_zero' := by
    ext i j
    rw [zero_entry]
    by_cases h : i = j
    · subst h; show (if h : i = i then h ▸ (A.diagEquiv i).symm 0 else 0) = 0; simp
    · exact dif_neg h
  map_add' r s := by
    ext i j
    by_cases h : i = j
    · subst h; simp [map_add]
    · simp [h]

@[simp] theorem scalarHom_entry_diag (A : GMA R d) (r : R) (i : Fin d) :
    (A.scalarHom r).entry i i = (A.diagEquiv i).symm r := by
  show (if h : i = i then h ▸ (A.diagEquiv i).symm r else 0) = _
  simp

@[simp] theorem scalarHom_entry_off (A : GMA R d) (r : R) {i j : Fin d} (h : i ≠ j) :
    (A.scalarHom r).entry i j = 0 :=
  dif_neg h

theorem scalarHom_mul (A : GMA R d) (r : R) (x : A.Elem) :
    A.scalarHom r * x = smulElem r x := by
  ext i k
  rw [mul_entry, Finset.sum_eq_single i]
  · rw [scalarHom_entry_diag, A.mul_diag_left]; rfl
  · intro j _ hji
    rw [scalarHom_entry_off A r hji.symm, map_zero, LinearMap.zero_apply]
  · intro hi; exact absurd (Finset.mem_univ i) hi

theorem mul_scalarHom (A : GMA R d) (x : A.Elem) (r : R) :
    x * A.scalarHom r = smulElem r x := by
  ext i k
  rw [mul_entry, Finset.sum_eq_single k]
  · rw [scalarHom_entry_diag, A.mul_diag_right]; rfl
  · intro j _ hjk
    rw [scalarHom_entry_off A r hjk, map_zero]
  · intro hk; exact absurd (Finset.mem_univ k) hk

theorem scalarHom_comm (A : GMA R d) (r : R) (x : A.Elem) :
    A.scalarHom r * x = x * A.scalarHom r := by
  rw [scalarHom_mul, mul_scalarHom]

/-- Single-block element `blockElem i j x ∈ A.Elem` having `x` in position `(i, j)` and `0`
elsewhere. -/
def blockElem (A : GMA R d) (i j : Fin d) (x : A.Block i j) : A.Elem :=
  ⟨fun a b => if h : a = i ∧ b = j then h.1 ▸ h.2 ▸ x else 0⟩

@[simp] theorem blockElem_entry_same (A : GMA R d) (i j : Fin d) (x : A.Block i j) :
    (A.blockElem i j x).entry i j = x := by
  show (if h : i = i ∧ j = j then h.1 ▸ h.2 ▸ x else 0) = x
  simp

theorem blockElem_entry_ne (A : GMA R d) {i j a b : Fin d} (h : a ≠ i ∨ b ≠ j)
    (x : A.Block i j) :
    (A.blockElem i j x).entry a b = 0 := by
  have hnot : ¬ (a = i ∧ b = j) := by
    rintro ⟨rfl, rfl⟩
    exact h.elim (fun h1 => h1 rfl) (fun h2 => h2 rfl)
  show (if h' : a = i ∧ b = j then h'.1 ▸ h'.2 ▸ x else 0) = 0
  simp [hnot]

theorem blockElem_mul_blockElem_same (A : GMA R d) (i j k : Fin d)
    (x : A.Block i j) (y : A.Block j k) :
    A.blockElem i j x * A.blockElem j k y = A.blockElem i k (A.mul i j k x y) := by
  ext a b
  by_cases hab : a = i ∧ b = k
  · rcases hab with ⟨rfl, rfl⟩
    rw [mul_entry, blockElem_entry_same, Finset.sum_eq_single j]
    · rw [blockElem_entry_same, blockElem_entry_same]
    · intro m _ hmj
      rw [blockElem_entry_ne A (Or.inr hmj), map_zero, LinearMap.zero_apply]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  · rw [mul_entry, blockElem_entry_ne A (by tauto)]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hai : a = i
    · by_cases hbk : b = k
      · exact absurd ⟨hai, hbk⟩ hab
      · rw [blockElem_entry_ne A (Or.inr hbk), map_zero]
    · rw [blockElem_entry_ne A (Or.inl hai), map_zero, LinearMap.zero_apply]

theorem blockElem_mul_blockElem_ne (A : GMA R d) {i j j' k : Fin d} (h : j ≠ j')
    (x : A.Block i j) (y : A.Block j' k) :
    A.blockElem i j x * A.blockElem j' k y = 0 := by
  ext a b
  rw [mul_entry, zero_entry]
  refine Finset.sum_eq_zero fun m _ => ?_
  by_cases hmj : m = j
  · subst hmj
    rw [blockElem_entry_ne A (Or.inl h), map_zero]
  · rw [blockElem_entry_ne A (Or.inr hmj), map_zero, LinearMap.zero_apply]

/-- Orthogonal diagonal idempotent `e_i ∈ A.Elem`. -/
def idemp (A : GMA R d) (i : Fin d) : A.Elem :=
  A.blockElem i i ((A.diagEquiv i).symm 1)

theorem idemp_mul_idemp_same (A : GMA R d) (i : Fin d) :
    A.idemp i * A.idemp i = A.idemp i := by
  unfold idemp
  rw [blockElem_mul_blockElem_same, A.mul_diag_left, one_smul]

theorem idemp_mul_idemp_ne (A : GMA R d) {i j : Fin d} (h : i ≠ j) :
    A.idemp i * A.idemp j = 0 :=
  A.blockElem_mul_blockElem_ne h _ _

theorem idemp_mul_elem_mul_idemp (A : GMA R d) (i j : Fin d) (x : A.Elem) :
    A.idemp i * x * A.idemp j = A.blockElem i j (x.entry i j) := by
  ext a b
  by_cases hab : a = i ∧ b = j
  · rcases hab with ⟨rfl, rfl⟩
    rw [blockElem_entry_same, mul_entry, Finset.sum_eq_single b]
    · rw [mul_entry, Finset.sum_eq_single a]
      · simp only [idemp, blockElem_entry_same]
        rw [A.mul_diag_left, one_smul, A.mul_diag_right, one_smul]
      · intro m _ hma
        rw [idemp, blockElem_entry_ne A (Or.inr hma), map_zero, LinearMap.zero_apply]
      · intro ha; exact absurd (Finset.mem_univ a) ha
    · intro m _ hmb
      have hmb' : (A.idemp b).entry m b = 0 := A.blockElem_entry_ne (Or.inl hmb) _
      rw [hmb', map_zero]
    · intro hb; exact absurd (Finset.mem_univ b) hb
  · rw [blockElem_entry_ne A (by tauto), mul_entry]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hbj : b = j
    · subst hbj
      have hai : a ≠ i := fun h => hab ⟨h, rfl⟩
      rw [mul_entry]
      have h0 : ∑ k : Fin d, A.mul a k m ((A.idemp i).entry a k) (x.entry k m) = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [idemp, blockElem_entry_ne A (Or.inl hai), map_zero, LinearMap.zero_apply]
      rw [h0, map_zero, LinearMap.zero_apply]
    · have hmb : (A.idemp j).entry m b = 0 := A.blockElem_entry_ne (Or.inr hbj) _
      rw [hmb, map_zero]

theorem idemp_mul_blockElem_mul_idemp (A : GMA R d) (i j : Fin d) (x : A.Block i j) :
    A.idemp i * A.blockElem i j x * A.idemp j = A.blockElem i j x := by
  rw [idemp_mul_elem_mul_idemp, blockElem_entry_same]

theorem sum_idemp_eq_one (A : GMA R d) : (∑ i : Fin d, A.idemp i) = 1 := by
  ext a b
  rw [sum_entry]
  by_cases hab : a = b
  · subst hab
    rw [one_entry_diag, Finset.sum_eq_single a]
    · exact A.blockElem_entry_same a a _
    · intro i _ hia
      exact A.blockElem_entry_ne (Or.inl hia.symm) _
    · intro ha; exact absurd (Finset.mem_univ a) ha
  · rw [one_entry_off hab]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hai : a = i
    · subst hai
      exact A.blockElem_entry_ne (Or.inr (Ne.symm hab)) _
    · exact A.blockElem_entry_ne (Or.inl hai) _

/-- The GMA **trace** `tr(x) := ∑ i, diagEquiv i (x_{i,i}) : A.Elem →+ R`. -/
def tr (A : GMA R d) : A.Elem →+ R where
  toFun x := ∑ i : Fin d, A.diagEquiv i (x.entry i i)
  map_zero' := by simp
  map_add' x y := by simp [map_add, Finset.sum_add_distrib]

@[simp] theorem tr_apply (A : GMA R d) (x : A.Elem) :
    A.tr x = ∑ i : Fin d, A.diagEquiv i (x.entry i i) := rfl

theorem tr_smulElem (A : GMA R d) (r : R) (x : A.Elem) :
    A.tr (smulElem r x) = r * A.tr x := by
  simp only [tr_apply, smulElem_entry, map_smul, smul_eq_mul, Finset.mul_sum]

theorem tr_one (A : GMA R d) : A.tr 1 = (d : R) := by
  simp [tr_apply]

theorem tr_scalarHom (A : GMA R d) (r : R) : A.tr (A.scalarHom r) = (d : R) * r := by
  simp [tr_apply]

theorem tr_blockElem_diag (A : GMA R d) (i : Fin d) (x : A.Block i i) :
    A.tr (A.blockElem i i x) = A.diagEquiv i x := by
  rw [tr_apply, Finset.sum_eq_single i]
  · rw [blockElem_entry_same]
  · intro j _ hji
    rw [blockElem_entry_ne A (Or.inl hji), map_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

theorem tr_blockElem_off (A : GMA R d) {i j : Fin d} (h : i ≠ j) (x : A.Block i j) :
    A.tr (A.blockElem i j x) = 0 := by
  rw [tr_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hki : k = i
  · subst hki
    rw [blockElem_entry_ne A (Or.inr h), map_zero]
  · rw [blockElem_entry_ne A (Or.inl hki), map_zero]

/-- **Centrality of the GMA trace (`tr(xy) = tr(yx)`)** from `(COMM)`. -/
theorem tr_mul_comm (A : GMA R d) (x y : A.Elem) : A.tr (x * y) = A.tr (y * x) := by
  simp only [tr_apply, mul_entry, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  exact A.mul_comm_trace i j (x.entry i j) (y.entry j i)

theorem tr_idemp_mul_elem_mul_idemp (A : GMA R d) (i : Fin d) (x : A.Elem) :
    A.tr (A.idemp i * x * A.idemp i) = A.diagEquiv i (x.entry i i) := by
  rw [idemp_mul_elem_mul_idemp, tr_blockElem_diag]

/-! ### 1.2 Concrete Standard Matrix GMA & Ideal-Weighted Sub-GMAs -/

/-- The standard `d × d` matrix algebra over `R` as a `GMA R d`. -/
def matrixGMA (R : Type*) [CommRing R] (d : ℕ) : GMA R d where
  Block _ _ := R
  blockAdd _ _ := inferInstance
  blockMod _ _ := inferInstance
  diagEquiv _ := LinearEquiv.refl R R
  mul _ _ _ := LinearMap.mul R R
  mul_diag_left _ _ _ _ := rfl
  mul_diag_right _ _ x r := mul_comm x r
  block_mul_assoc _ _ _ _ x y z := (mul_assoc x y z).symm
  mul_comm_trace _ _ x y := mul_comm x y

/-- Ring isomorphism `(matrixGMA R d).Elem ≃+* Matrix (Fin d) (Fin d) R`. -/
def matrixGMAElemEquiv (R : Type*) [CommRing R] (d : ℕ) :
    (matrixGMA R d).Elem ≃+* Matrix (Fin d) (Fin d) R where
  toFun x := Matrix.of fun i j => x.entry i j
  invFun M := ⟨fun i j => M i j⟩
  left_inv x := by ext i j; rfl
  right_inv M := by ext i j; rfl
  map_mul' x y := by
    ext i k
    rfl
  map_add' x y := by ext i j; rfl

theorem matrixGMAElemEquiv_tr (R : Type*) [CommRing R] (d : ℕ) (x : (matrixGMA R d).Elem) :
    (matrixGMAElemEquiv R d x).trace = (matrixGMA R d).tr x := rfl

/-- Concrete **ideal-weighted GMA (`idealGMA R d I`)** inside `M_d(R)` with block `(i, j)` given
by an ideal `I i j ≤ R` satisfying `I i i = ⊤` and `I i j * I j k ≤ I i k`. -/
def idealGMA (R : Type*) [CommRing R] (d : ℕ) (I : Fin d → Fin d → Ideal R)
    (hdiag : ∀ i, I i i = ⊤) (hmul : ∀ i j k, I i j * I j k ≤ I i k) : GMA R d where
  Block i j := I i j
  blockAdd _ _ := inferInstance
  blockMod _ _ := inferInstance
  diagEquiv i :=
    { toFun := fun x => x.1
      invFun := fun r => ⟨r, by rw [hdiag i]; trivial⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => rfl }
  mul i j k :=
    { toFun := fun x =>
        { toFun := fun y => ⟨x.1 * y.1, hmul i j k (Ideal.mul_mem_mul x.2 y.2)⟩
          map_add' := fun y₁ y₂ => Subtype.ext (mul_add x.1 y₁.1 y₂.1)
          map_smul' := fun r y => Subtype.ext (by simp [mul_left_comm]) }
      map_add' := fun x₁ x₂ => by ext y; exact add_mul x₁.1 x₂.1 y.1
      map_smul' := fun r x => by ext y; exact mul_assoc r x.1 y.1 }
  mul_diag_left _ _ _ _ := Subtype.ext rfl
  mul_diag_right _ _ x r := Subtype.ext (mul_comm x.1 r)
  block_mul_assoc _ _ _ _ x y z := Subtype.ext (mul_assoc x.1 y.1 z.1).symm
  mul_comm_trace _ _ x y := mul_comm x.1 y.1

/-! ### 1.3 Total Reducibility Ideal `I_red` & Bellaïche–Chenevier Theorem 1.5.1 -/

/-- Pairwise off-diagonal product ideal `im(A_{i,j} ⊗ A_{j,i} → R) ⊆ R`. -/
def pairIdeal (A : GMA R d) (i j : Fin d) : Ideal R :=
  Ideal.span { r : R | ∃ (x : A.Block i j) (y : A.Block j i),
    r = A.diagEquiv i (A.mul i j i x y) }

theorem mem_pairIdeal_mul (A : GMA R d) (i j : Fin d) (x : A.Block i j) (y : A.Block j i) :
    A.diagEquiv i (A.mul i j i x y) ∈ A.pairIdeal i j :=
  Ideal.subset_span ⟨x, y, rfl⟩

theorem pairIdeal_le_iff (A : GMA R d) (i j : Fin d) (J : Ideal R) :
    A.pairIdeal i j ≤ J ↔ ∀ (x : A.Block i j) (y : A.Block j i),
      A.diagEquiv i (A.mul i j i x y) ∈ J := by
  rw [pairIdeal, Ideal.span_le]
  constructor
  · intro h x y
    exact h ⟨x, y, rfl⟩
  · rintro h r ⟨x, y, rfl⟩
    exact h x y

/-- Symmetry `pairIdeal i j = pairIdeal j i` from trace commutativity `(COMM)`. -/
theorem pairIdeal_symm (A : GMA R d) (i j : Fin d) :
    A.pairIdeal i j = A.pairIdeal j i := by
  apply le_antisymm
  · rw [pairIdeal_le_iff]
    intro x y
    rw [A.mul_comm_trace i j x y]
    exact A.mem_pairIdeal_mul j i y x
  · rw [pairIdeal_le_iff]
    intro y x
    rw [A.mul_comm_trace j i y x]
    exact A.mem_pairIdeal_mul i j x y

/-- The **total reducibility ideal** `I_red(A) := ∑_{i ≠ j} im(A_{i,j} ⊗ A_{j,i} → R) ≤ R`
of a rank-`d` GMA `A`. -/
def reducibilityIdeal (A : GMA R d) : Ideal R :=
  ⨆ (i : Fin d) (j : Fin d) (_ : i ≠ j), A.pairIdeal i j

theorem pairIdeal_le_reducibilityIdeal (A : GMA R d) {i j : Fin d} (h : i ≠ j) :
    A.pairIdeal i j ≤ A.reducibilityIdeal :=
  le_iSup_of_le i (le_iSup_of_le j (le_iSup_of_le h le_rfl))

theorem mem_reducibilityIdeal_mul (A : GMA R d) {i j : Fin d} (h : i ≠ j)
    (x : A.Block i j) (y : A.Block j i) :
    A.diagEquiv i (A.mul i j i x y) ∈ A.reducibilityIdeal :=
  A.pairIdeal_le_reducibilityIdeal h (A.mem_pairIdeal_mul i j x y)

theorem reducibilityIdeal_le_iff (A : GMA R d) (J : Ideal R) :
    A.reducibilityIdeal ≤ J ↔
      ∀ (i j : Fin d), i ≠ j → ∀ (x : A.Block i j) (y : A.Block j i),
        A.diagEquiv i (A.mul i j i x y) ∈ J := by
  simp only [reducibilityIdeal, iSup_le_iff, pairIdeal_le_iff]

/-- Universal factoring characterization of `A.reducibilityIdeal`: a ring hom `f : R →+* S`
annihilates all off-diagonal products `A_{i,j} · A_{j,i}` iff `A.reducibilityIdeal ≤ ker f` iff
`f` factors uniquely through `R ⧸ A.reducibilityIdeal`. -/
theorem reducibilityIdeal_le_ker_iff (A : GMA R d) {S : Type*} [CommRing S] (f : R →+* S) :
    A.reducibilityIdeal ≤ RingHom.ker f ↔
      ∀ (i j : Fin d), i ≠ j → ∀ (x : A.Block i j) (y : A.Block j i),
        f (A.diagEquiv i (A.mul i j i x y)) = 0 :=
  A.reducibilityIdeal_le_iff (RingHom.ker f)

theorem factors_through_reducibilityIdeal_iff (A : GMA R d) {S : Type*} [CommRing S]
    (f : R →+* S) :
    A.reducibilityIdeal ≤ RingHom.ker f ↔
      ∃! fbar : R ⧸ A.reducibilityIdeal →+* S,
        fbar.comp (Ideal.Quotient.mk A.reducibilityIdeal) = f := by
  constructor
  · intro hf
    refine ⟨Ideal.Quotient.lift A.reducibilityIdeal f (fun r hr => hf hr), ?_, ?_⟩
    · ext r; rfl
    · intro g hg
      ext r
      exact RingHom.congr_fun hg r
  · rintro ⟨fbar, hfbar, _⟩ r hr
    rw [RingHom.mem_ker, ← hfbar, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]

/-! ### 1.4 GMA Representations `ρ : G →* A.Elem` & Bellaïche–Chenevier Theorem 1.5.1 -/

section GMARepresentations

variable {G : Type*} [Group G]

/-- The `i`-th diagonal coordinate `g ↦ diagEquiv i ((ρ g)_{i,i}) : G → R`. -/
def diagComp (A : GMA R d) (ρ : G →* A.Elem) (i : Fin d) (g : G) : R :=
  A.diagEquiv i ((ρ g).entry i i)

/-- The trace pseudocharacter `T_ρ(g) := tr(ρ(g)) = ∑ i, diagComp ρ i g`. -/
def traceChar (A : GMA R d) (ρ : G →* A.Elem) (g : G) : R :=
  A.tr (ρ g)

theorem traceChar_eq_sum_diagComp (A : GMA R d) (ρ : G →* A.Elem) (g : G) :
    A.traceChar ρ g = ∑ i : Fin d, A.diagComp ρ i g := rfl

theorem diagComp_one (A : GMA R d) (ρ : G →* A.Elem) (i : Fin d) :
    A.diagComp ρ i 1 = 1 := by
  simp [diagComp]

/-- **Fundamental diagonal defect identity**:
`diagComp ρ i (g * h) = diagComp ρ i g * diagComp ρ i h + ∑_{j ≠ i} (ρ g)_{i,j} (ρ h)_{j,i}`. -/
theorem diagComp_mul (A : GMA R d) (ρ : G →* A.Elem) (i : Fin d) (g h : G) :
    A.diagComp ρ i (g * h) =
      A.diagComp ρ i g * A.diagComp ρ i h +
        ∑ j ∈ Finset.univ.erase i,
          A.diagEquiv i (A.mul i j i ((ρ g).entry i j) ((ρ h).entry j i)) := by
  unfold diagComp
  rw [map_mul, mul_entry, map_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  congr 1
  have h1 : (ρ g).entry i i = (A.diagEquiv i).symm (A.diagEquiv i ((ρ g).entry i i)) := by simp
  conv_lhs => rw [h1, A.mul_diag_left, map_smul, smul_eq_mul]

/-- Modulo any ring hom `f : R →+* S` killing `I_red`, each diagonal component `f ∘ diagComp ρ i`
is a genuine multiplicative character `G →* S`. -/
def diagCharOfFactor (A : GMA R d) (ρ : G →* A.Elem) {S : Type*} [CommRing S]
    (f : R →+* S) (hf : A.reducibilityIdeal ≤ RingHom.ker f) (i : Fin d) : G →* S where
  toFun g := f (A.diagComp ρ i g)
  map_one' := by rw [A.diagComp_one ρ i, map_one]
  map_mul' g h := by
    rw [A.diagComp_mul ρ i g h, map_add, map_mul, map_sum]
    have hzero : ∑ j ∈ Finset.univ.erase i,
        f (A.diagEquiv i (A.mul i j i ((ρ g).entry i j) ((ρ h).entry j i))) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
      exact (A.reducibilityIdeal_le_ker_iff f).mp hf i j hij _ _
    rw [hzero, add_zero]

/-- Since `G` is a group, `diagCharOfFactor` automatically lands in the unit group `Sˣ`. -/
def diagUnitCharOfFactor (A : GMA R d) (ρ : G →* A.Elem) {S : Type*} [CommRing S]
    (f : R →+* S) (hf : A.reducibilityIdeal ≤ RingHom.ker f) (i : Fin d) : G →* Sˣ where
  toFun g :=
    { val := A.diagCharOfFactor ρ f hf i g
      inv := A.diagCharOfFactor ρ f hf i g⁻¹
      val_inv := by rw [← map_mul, mul_inv_cancel, map_one]
      inv_val := by rw [← map_mul, inv_mul_cancel, map_one] }
  map_one' := Units.ext (map_one _)
  map_mul' g h := Units.ext (map_mul _ g h)

@[simp] theorem diagUnitCharOfFactor_val (A : GMA R d) (ρ : G →* A.Elem) {S : Type*} [CommRing S]
    (f : R →+* S) (hf : A.reducibilityIdeal ≤ RingHom.ker f) (i : Fin d) (g : G) :
    ((A.diagUnitCharOfFactor ρ f hf i g : Sˣ) : S) = f (A.diagComp ρ i g) := rfl

theorem traceChar_splits_of_reducibilityIdeal (A : GMA R d) (ρ : G →* A.Elem) {S : Type*}
    [CommRing S] (f : R →+* S) (hf : A.reducibilityIdeal ≤ RingHom.ker f) (g : G) :
    f (A.traceChar ρ g) = ∑ i : Fin d, A.diagCharOfFactor ρ f hf i g := by
  rw [traceChar_eq_sum_diagComp, map_sum]
  rfl

/-- Explicit `R`-linear evaluation `MonoidAlgebra R G → A.Elem` extending `ρ : G →* A.Elem`. -/
def monoidAlgEval (A : GMA R d) (ρ : G →* A.Elem) (u : MonoidAlgebra R G) : A.Elem :=
  u.coeff.sum fun g r => A.scalarHom r * ρ g

theorem monoidAlgEval_zero (A : GMA R d) (ρ : G →* A.Elem) :
    A.monoidAlgEval ρ 0 = 0 := by
  unfold monoidAlgEval
  simp

theorem monoidAlgEval_add (A : GMA R d) (ρ : G →* A.Elem) (u v : MonoidAlgebra R G) :
    A.monoidAlgEval ρ (u + v) = A.monoidAlgEval ρ u + A.monoidAlgEval ρ v := by
  unfold monoidAlgEval
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_mul])

theorem monoidAlgEval_single (A : GMA R d) (ρ : G →* A.Elem) (g : G) (r : R) :
    A.monoidAlgEval ρ (MonoidAlgebra.single g r) = A.scalarHom r * ρ g := by
  unfold monoidAlgEval
  change (Finsupp.single g r).sum (fun g' r' => A.scalarHom r' * ρ g') = _
  rw [Finsupp.sum_single_index (by simp)]

theorem monoidAlgEval_smul (A : GMA R d) (ρ : G →* A.Elem) (r : R) (u : MonoidAlgebra R G) :
    A.monoidAlgEval ρ (r • u) = A.scalarHom r * A.monoidAlgEval ρ u := by
  unfold monoidAlgEval
  change (r • u.coeff).sum (fun g s => A.scalarHom s * ρ g) = _
  rw [Finsupp.sum_smul_index' (fun _ => by simp)]
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun g _ => ?_
  rw [smul_eq_mul, map_mul, mul_assoc]

/-- Explicit `R`-linear ring homomorphism `MonoidAlgebra R G →+* A.Elem` extending `ρ : G →* A.Elem`
(zero `Algebra` typeclass diamonds). -/
def monoidAlgHom (A : GMA R d) (ρ : G →* A.Elem) : MonoidAlgebra R G →+* A.Elem where
  toFun := A.monoidAlgEval ρ
  map_one' := by
    have h1 : (1 : MonoidAlgebra R G) = MonoidAlgebra.single (1 : G) (1 : R) := rfl
    rw [h1, A.monoidAlgEval_single, map_one, map_one, mul_one]
  map_zero' := A.monoidAlgEval_zero ρ
  map_add' := A.monoidAlgEval_add ρ
  map_mul' u v := by
    refine MonoidAlgebra.induction_on
      (motive := fun u => A.monoidAlgEval ρ (u * v) = A.monoidAlgEval ρ u * A.monoidAlgEval ρ v)
      u ?_ ?_ ?_
    · intro g
      refine MonoidAlgebra.induction_on
        (motive := fun v => A.monoidAlgEval ρ (MonoidAlgebra.of R G g * v) =
          A.monoidAlgEval ρ (MonoidAlgebra.of R G g) * A.monoidAlgEval ρ v) v ?_ ?_ ?_
      · intro h
        change A.monoidAlgEval ρ (MonoidAlgebra.single g 1 * MonoidAlgebra.single h 1) =
          A.monoidAlgEval ρ (MonoidAlgebra.single g 1) * A.monoidAlgEval ρ (MonoidAlgebra.single h 1)
        rw [MonoidAlgebra.single_mul_single, one_mul,
          A.monoidAlgEval_single, A.monoidAlgEval_single, A.monoidAlgEval_single,
          map_one, one_mul, one_mul, one_mul, map_mul]
      · intro v₁ v₂ ih₁ ih₂
        rw [mul_add, A.monoidAlgEval_add, A.monoidAlgEval_add, mul_add, ih₁, ih₂]
      · intro s v₁ ih
        rw [mul_smul_comm, A.monoidAlgEval_smul, A.monoidAlgEval_smul, ih, ← mul_assoc,
          A.scalarHom_comm, mul_assoc]
    · intro u₁ u₂ ih₁ ih₂
      rw [add_mul, A.monoidAlgEval_add, A.monoidAlgEval_add, add_mul, ih₁, ih₂]
    · intro r u₁ ih
      rw [smul_mul_assoc, A.monoidAlgEval_smul, A.monoidAlgEval_smul, ih, mul_assoc]

@[simp] theorem monoidAlgHom_single (A : GMA R d) (ρ : G →* A.Elem) (g : G) (r : R) :
    A.monoidAlgHom ρ (MonoidAlgebra.single g r) = A.scalarHom r * ρ g :=
  A.monoidAlgEval_single ρ g r

@[simp] theorem monoidAlgHom_of (A : GMA R d) (ρ : G →* A.Elem) (g : G) :
    A.monoidAlgHom ρ (MonoidAlgebra.of R G g) = ρ g := by
  change A.monoidAlgHom ρ (MonoidAlgebra.single g 1) = ρ g
  rw [monoidAlgHom_single, map_one, one_mul]

theorem monoidAlgHom_smul (A : GMA R d) (ρ : G →* A.Elem) (r : R) (u : MonoidAlgebra R G) :
    A.monoidAlgHom ρ (r • u) = A.scalarHom r * A.monoidAlgHom ρ u :=
  A.monoidAlgEval_smul ρ r u

/-- Explicit `f`-semilinear evaluation `MonoidAlgebra R G → S` of a character `χ : G →* S`. -/
def monoidAlgCharEval {S : Type*} [CommRing S] (f : R →+* S) (χ : G →* S)
    (u : MonoidAlgebra R G) : S :=
  u.coeff.sum fun g r => f r * χ g

theorem monoidAlgCharEval_single {S : Type*} [CommRing S] (f : R →+* S) (χ : G →* S)
    (g : G) (r : R) :
    monoidAlgCharEval f χ (MonoidAlgebra.single g r) = f r * χ g := by
  unfold monoidAlgCharEval
  change (Finsupp.single g r).sum (fun g' r' => f r' * χ g') = _
  rw [Finsupp.sum_single_index (by simp)]

theorem monoidAlgCharEval_add {S : Type*} [CommRing S] (f : R →+* S) (χ : G →* S)
    (u v : MonoidAlgebra R G) :
    monoidAlgCharEval f χ (u + v) = monoidAlgCharEval f χ u + monoidAlgCharEval f χ v := by
  unfold monoidAlgCharEval
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [add_mul])

theorem monoidAlgCharEval_smul {S : Type*} [CommRing S] (f : R →+* S) (χ : G →* S)
    (r : R) (u : MonoidAlgebra R G) :
    monoidAlgCharEval f χ (r • u) = f r * monoidAlgCharEval f χ u := by
  unfold monoidAlgCharEval
  change (r • u.coeff).sum (fun g s => f s * χ g) = _
  rw [Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun g _ => ?_
  rw [smul_eq_mul, map_mul, mul_assoc]

/-- Explicit `f`-semilinear ring extension `MonoidAlgebra R G →+* S` of a character `χ : G →* S`. -/
def monoidAlgChar {S : Type*} [CommRing S] (f : R →+* S) (χ : G →* S) :
    MonoidAlgebra R G →+* S where
  toFun := monoidAlgCharEval f χ
  map_one' := by
    have h1 : (1 : MonoidAlgebra R G) = MonoidAlgebra.single (1 : G) (1 : R) := rfl
    rw [h1, monoidAlgCharEval_single, map_one, map_one, mul_one]
  map_zero' := by unfold monoidAlgCharEval; simp
  map_add' := monoidAlgCharEval_add f χ
  map_mul' u v := by
    refine MonoidAlgebra.induction_on
      (motive := fun u => monoidAlgCharEval f χ (u * v) =
        monoidAlgCharEval f χ u * monoidAlgCharEval f χ v) u ?_ ?_ ?_
    · intro g
      refine MonoidAlgebra.induction_on
        (motive := fun v => monoidAlgCharEval f χ (MonoidAlgebra.of R G g * v) =
          monoidAlgCharEval f χ (MonoidAlgebra.of R G g) * monoidAlgCharEval f χ v) v ?_ ?_ ?_
      · intro h
        change monoidAlgCharEval f χ (MonoidAlgebra.single g 1 * MonoidAlgebra.single h 1) =
          monoidAlgCharEval f χ (MonoidAlgebra.single g 1) *
            monoidAlgCharEval f χ (MonoidAlgebra.single h 1)
        rw [MonoidAlgebra.single_mul_single, one_mul, monoidAlgCharEval_single,
          monoidAlgCharEval_single, monoidAlgCharEval_single, map_one, one_mul, one_mul,
          one_mul, map_mul]
      · intro v₁ v₂ ih₁ ih₂
        rw [mul_add, monoidAlgCharEval_add, monoidAlgCharEval_add, mul_add, ih₁, ih₂]
      · intro s v₁ ih
        rw [mul_smul_comm, monoidAlgCharEval_smul, monoidAlgCharEval_smul, ih]; ring
    · intro u₁ u₂ ih₁ ih₂
      rw [add_mul, monoidAlgCharEval_add, monoidAlgCharEval_add, add_mul, ih₁, ih₂]
    · intro r u₁ ih
      rw [smul_mul_assoc, monoidAlgCharEval_smul, monoidAlgCharEval_smul, ih, mul_assoc]

@[simp] theorem monoidAlgChar_of {S : Type*} [CommRing S] (f : R →+* S) (χ : G →* S) (g : G) :
    monoidAlgChar f χ (MonoidAlgebra.of R G g) = χ g := by
  change monoidAlgCharEval f χ (MonoidAlgebra.single g 1) = χ g
  rw [monoidAlgCharEval_single, map_one, one_mul]

theorem monoidAlgChar_smul {S : Type*} [CommRing S] (f : R →+* S) (χ : G →* S)
    (r : R) (u : MonoidAlgebra R G) :
    monoidAlgChar f χ (r • u) = f r * monoidAlgChar f χ u :=
  monoidAlgCharEval_smul f χ r u

theorem monoidAlgChar_diagComp (A : GMA R d) (ρ : G →* A.Elem) {S : Type*} [CommRing S]
    (f : R →+* S) (hf : A.reducibilityIdeal ≤ RingHom.ker f) (i : Fin d)
    (u : MonoidAlgebra R G) :
    monoidAlgChar f (A.diagCharOfFactor ρ f hf i) u =
      f (A.diagEquiv i ((A.monoidAlgHom ρ u).entry i i)) := by
  refine MonoidAlgebra.induction_on
    (motive := fun u => monoidAlgChar f (A.diagCharOfFactor ρ f hf i) u =
      f (A.diagEquiv i ((A.monoidAlgHom ρ u).entry i i))) u ?_ ?_ ?_
  · intro g
    rw [monoidAlgChar_of, monoidAlgHom_of]
    rfl
  · intro u₁ u₂ ih₁ ih₂
    simp only [map_add, add_entry, ih₁, ih₂]
  · intro r u₁ ih
    rw [monoidAlgChar_smul, monoidAlgHom_smul, scalarHom_mul, smulElem_entry, map_smul,
      smul_eq_mul, map_mul, ih]

theorem trace_monoidAlgHom_eq_sum_chars (A : GMA R d) (ρ : G →* A.Elem) {S : Type*} [CommRing S]
    (f : R →+* S) (χ : Fin d → (G →* S))
    (hsplit : ∀ g : G, f (A.traceChar ρ g) = ∑ k : Fin d, χ k g)
    (u : MonoidAlgebra R G) :
    f (A.tr (A.monoidAlgHom ρ u)) = ∑ k : Fin d, monoidAlgChar f (χ k) u := by
  refine MonoidAlgebra.induction_on
    (motive := fun u => f (A.tr (A.monoidAlgHom ρ u)) = ∑ k : Fin d, monoidAlgChar f (χ k) u)
    u ?_ ?_ ?_
  · intro g
    rw [monoidAlgHom_of]
    exact (hsplit g).trans (Finset.sum_congr rfl fun k _ => (monoidAlgChar_of f (χ k) g).symm)
  · intro u₁ u₂ ih₁ ih₂
    simp only [map_add, ih₁, ih₂, Finset.sum_add_distrib]
  · intro r u₁ ih
    rw [monoidAlgHom_smul, scalarHom_mul, tr_smulElem, map_mul, ih, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => (monoidAlgChar_smul f (χ k) r u₁).symm

/-- **Bellaïche–Chenevier Theorem 1.5.1 (`gma_reducibility_ideal_minimal`)**:
Suppose `ρ : G →* A.Elem` generates the GMA `A` (`monoidAlgHom ρ` is surjective) with lifted
idempotents `eLift : Fin d → MonoidAlgebra R G` (`monoidAlgHom ρ (eLift i) = A.idemp i`).
Then for any commutative ring `S` and ring homomorphism `f : R →+* S`, the following are equivalent:
1. `A.reducibilityIdeal ≤ RingHom.ker f` (i.e., `f` factors uniquely through
   `R ⧸ A.reducibilityIdeal`);
2. The pushed-forward trace pseudocharacter `f ∘ traceChar ρ` splits into a sum of `d` characters
   `χ : Fin d → (G →* S)` adapted to the lifted idempotents
   (`monoidAlgChar f (χ k) (eLift i) = if k = i then 1 else 0`). -/
theorem gma_reducibility_ideal_minimal (A : GMA R d) (ρ : G →* A.Elem)
    (hsurj : Function.Surjective (A.monoidAlgHom ρ))
    (eLift : Fin d → MonoidAlgebra R G)
    (heLift : ∀ i : Fin d, A.monoidAlgHom ρ (eLift i) = A.idemp i)
    {S : Type*} [CommRing S] (f : R →+* S) :
    A.reducibilityIdeal ≤ RingHom.ker f ↔
      ∃ χ : Fin d → (G →* S),
        (∀ g : G, f (A.traceChar ρ g) = ∑ k : Fin d, χ k g) ∧
        (∀ i k : Fin d, monoidAlgChar f (χ k) (eLift i) = if k = i then 1 else 0) := by
  constructor
  · intro hf
    refine ⟨A.diagCharOfFactor ρ f hf, A.traceChar_splits_of_reducibilityIdeal ρ f hf, ?_⟩
    intro i k
    rw [A.monoidAlgChar_diagComp ρ f hf k (eLift i), heLift i]
    by_cases hki : k = i
    · subst hki
      simp [idemp]
    · simp [idemp, A.blockElem_entry_ne (Or.inl hki), hki]
  · rintro ⟨χ, hsplit, hadapt⟩
    rw [A.reducibilityIdeal_le_ker_iff f]
    intro i j hij x y
    obtain ⟨u, hu⟩ := hsurj (A.blockElem i j x)
    obtain ⟨v, hv⟩ := hsurj (A.blockElem j i y)
    let w : MonoidAlgebra R G := eLift i * u * eLift j * v * eLift i
    have hmw : A.monoidAlgHom ρ w = A.blockElem i i (A.mul i j i x y) := by
      simp only [w, map_mul, heLift, hu, hv]
      have h1 : A.idemp i * A.blockElem i j x * A.idemp j = A.blockElem i j x :=
        A.idemp_mul_blockElem_mul_idemp i j x
      have h2 : A.blockElem i j x * A.blockElem j i y = A.blockElem i i (A.mul i j i x y) :=
        A.blockElem_mul_blockElem_same i j i x y
      calc A.idemp i * A.blockElem i j x * A.idemp j * A.blockElem j i y * A.idemp i
          = A.blockElem i j x * A.blockElem j i y * A.idemp i := by rw [h1]
        _ = A.blockElem i i (A.mul i j i x y) * A.idemp i := by rw [h2]
        _ = A.blockElem i i (A.mul i j i x y) := by
            unfold idemp
            rw [blockElem_mul_blockElem_same, A.mul_diag_right, one_smul]
    have htr_lhs : f (A.tr (A.monoidAlgHom ρ w)) = f (A.diagEquiv i (A.mul i j i x y)) := by
      rw [hmw, A.tr_blockElem_diag]
    rw [← htr_lhs, A.trace_monoidAlgHom_eq_sum_chars ρ f χ hsplit w]
    refine Finset.sum_eq_zero fun k _ => ?_
    simp only [w, map_mul, hadapt]
    by_cases hki : k = i
    · subst hki
      simp [hij]
    · simp [hki]

/-- Quotient-factoring form of Bellaïche–Chenevier Theorem 1.5.1. -/
theorem gma_reducibility_ideal_minimal_quotient (A : GMA R d) (ρ : G →* A.Elem)
    (hsurj : Function.Surjective (A.monoidAlgHom ρ))
    (eLift : Fin d → MonoidAlgebra R G)
    (heLift : ∀ i : Fin d, A.monoidAlgHom ρ (eLift i) = A.idemp i)
    {S : Type*} [CommRing S] (f : R →+* S) :
    (∃! fbar : R ⧸ A.reducibilityIdeal →+* S,
      fbar.comp (Ideal.Quotient.mk A.reducibilityIdeal) = f) ↔
      ∃ χ : Fin d → (G →* S),
        (∀ g : G, f (A.traceChar ρ g) = ∑ k : Fin d, χ k g) ∧
        (∀ i k : Fin d, monoidAlgChar f (χ k) (eLift i) = if k = i then 1 else 0) :=
  (A.factors_through_reducibilityIdeal_iff f).symm.trans
    (A.gma_reducibility_ideal_minimal ρ hsurj eLift heLift f)

end GMARepresentations
end GMA
end GMABasic

/-! ## Section 2: Bellaïche–Chenevier `Ext¹` Injection (`gma_ext_injection` / `LemmaP`) & Selmer Length Bounds -/

section GMAExtInjection

open GMA

variable {R S G M : Type*} [CommRing R] [CommRing S] [Group G] [AddCommGroup M] [Module S M]

/-- The `S`-module of 1-cocycles `Z¹(G, M(χ_i χ_j⁻¹))` representing extensions of `χ_j` by `χ_i`:
`c(g h) = c(g) + (χ_i(g) χ_j(g)⁻¹) • c(h)`. -/
def Ext1Cocycle (χi χj : G →* Sˣ) (M : Type*) [AddCommGroup M] [Module S M] :
    Submodule S (G → M) where
  carrier := { c : G → M | ∀ g h : G,
    c (g * h) = c g + ((χi g * (χj g)⁻¹ : Sˣ) : S) • c h }
  add_mem' {c₁ c₂} h₁ h₂ g h := by
    simp only [Pi.add_apply, h₁ g h, h₂ g h, smul_add]
    abel
  zero_mem' g h := by simp
  smul_mem' s {c} hc g h := by
    simp only [Pi.smul_apply, hc g h, smul_add, smul_comm s]

/-- The `S`-submodule of 1-coboundaries `B¹(G, M(χ_i χ_j⁻¹)) ≤ Z¹(G, M(χ_i χ_j⁻¹))`:
`c(g) = (χ_i(g) χ_j(g)⁻¹) • m - m`. -/
def Ext1Coboundary (χi χj : G →* Sˣ) (M : Type*) [AddCommGroup M] [Module S M] :
    Submodule S (Ext1Cocycle χi χj M) where
  carrier := { c | ∃ m : M, ∀ g : G,
    c.1 g = ((χi g * (χj g)⁻¹ : Sˣ) : S) • m - m }
  add_mem' := by
    rintro c₁ c₂ ⟨m₁, h₁⟩ ⟨m₂, h₂⟩
    refine ⟨m₁ + m₂, fun g => ?_⟩
    change c₁.1 g + c₂.1 g = _
    rw [h₁ g, h₂ g, smul_add]
    abel
  zero_mem' := ⟨0, fun _ => by simp⟩
  smul_mem' s := by
    rintro c ⟨m, hm⟩
    refine ⟨s • m, fun g => ?_⟩
    change s • c.1 g = _
    rw [hm g, smul_sub, smul_comm]

/-- Concrete extension group `Ext¹_G(χ_j, χ_i; M) := Z¹(G, M(χ_i χ_j⁻¹)) / B¹(G, M(χ_i χ_j⁻¹))`. -/
abbrev Ext1Char (χi χj : G →* Sˣ) (M : Type*) [AddCommGroup M] [Module S M] : Type _ :=
  Ext1Cocycle χi χj M ⧸ Ext1Coboundary χi χj M

/-- The **reducible submodule** `B'_{i,j} := I_red · A_{i,j} + ∑_{k ≠ i, j} A_{i,k} A_{k,j}`
inside `A.Block i j` (Bellaïche–Chenevier §1.5.2). -/
def reducibleBlockSubmodule {d : ℕ} (A : GMA R d) (i j : Fin d) :
    Submodule R (A.Block i j) :=
  (A.reducibilityIdeal • (⊤ : Submodule R (A.Block i j))) ⊔
    ⨆ (k : Fin d) (_ : k ≠ i) (_ : k ≠ j),
      Submodule.span R { z : A.Block i j | ∃ (x : A.Block i k) (y : A.Block k j),
        z = A.mul i k j x y }

/-- For `d = 2`, there is no intermediate index `k ∉ {i, j}`, so `B'_{i,j} = I_red · A_{i,j}`. -/
theorem reducibleBlockSubmodule_two (A : GMA R 2) {i j : Fin 2} (hij : i ≠ j) :
    reducibleBlockSubmodule A i j = A.reducibilityIdeal • (⊤ : Submodule R (A.Block i j)) := by
  unfold reducibleBlockSubmodule
  have hbot : (⨆ (k : Fin 2) (_ : k ≠ i) (_ : k ≠ j),
      Submodule.span R { z : A.Block i j | ∃ (x : A.Block i k) (y : A.Block k j),
        z = A.mul i k j x y }) = ⊥ := by
    rw [eq_bot_iff]
    refine iSup_le fun k => iSup_le fun hki => iSup_le fun hkj => ?_
    exfalso
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
  rw [hbot, sup_bot_eq]

/-- An `f`-semilinear homomorphism `λ : A.Block i j → M` vanishing on all intermediate products
`A_{i,k} A_{k,j}` (`k ≠ i, j`) — equivalently, a homomorphism out of `A_{i,j} / B'_{i,j}` into `M`
when `A.reducibilityIdeal ≤ ker f`. -/
@[ext]
structure GMARedHom {d : ℕ} (A : GMA R d) (f : R →+* S) (i j : Fin d)
    (M : Type*) [AddCommGroup M] [Module S M] where
  toAddHom : A.Block i j →+ M
  map_smul' : ∀ (r : R) (x : A.Block i j), toAddHom (r • x) = f r • toAddHom x
  map_inter_mul' : ∀ (k : Fin d), k ≠ i → k ≠ j →
    ∀ (x : A.Block i k) (y : A.Block k j), toAddHom (A.mul i k j x y) = 0

namespace GMARedHom

variable {d : ℕ} {A : GMA R d} {f : R →+* S} {i j : Fin d}

instance : Zero (GMARedHom A f i j M) :=
  ⟨⟨0, fun _ _ => by simp, fun _ _ _ _ _ => rfl⟩⟩

instance : Add (GMARedHom A f i j M) :=
  ⟨fun u v =>
    ⟨u.toAddHom + v.toAddHom,
      fun r x => by simp [u.map_smul', v.map_smul', smul_add],
      fun k hki hkj x y => by simp [u.map_inter_mul' k hki hkj x y, v.map_inter_mul' k hki hkj x y]⟩⟩

instance : Neg (GMARedHom A f i j M) :=
  ⟨fun u =>
    ⟨-u.toAddHom,
      fun r x => by simp [u.map_smul'],
      fun k hki hkj x y => by simp [u.map_inter_mul' k hki hkj x y]⟩⟩

instance : Sub (GMARedHom A f i j M) :=
  ⟨fun u v =>
    ⟨u.toAddHom - v.toAddHom,
      fun r x => by simp [u.map_smul', v.map_smul', smul_sub],
      fun k hki hkj x y => by simp [u.map_inter_mul' k hki hkj x y, v.map_inter_mul' k hki hkj x y]⟩⟩

instance : SMul S (GMARedHom A f i j M) :=
  ⟨fun s u =>
    ⟨{ toFun := fun x => s • u.toAddHom x
       map_zero' := by simp
       map_add' := fun x y => by simp [smul_add] },
      fun r x => by simp [u.map_smul', smul_comm s],
      fun k hki hkj x y => by simp [u.map_inter_mul' k hki hkj x y]⟩⟩

@[simp] theorem zero_apply (x : A.Block i j) : (0 : GMARedHom A f i j M).toAddHom x = 0 := rfl
@[simp] theorem add_apply (u v : GMARedHom A f i j M) (x : A.Block i j) :
    (u + v).toAddHom x = u.toAddHom x + v.toAddHom x := rfl
@[simp] theorem neg_apply (u : GMARedHom A f i j M) (x : A.Block i j) :
    (-u).toAddHom x = -u.toAddHom x := rfl
@[simp] theorem sub_apply (u v : GMARedHom A f i j M) (x : A.Block i j) :
    (u - v).toAddHom x = u.toAddHom x - v.toAddHom x := rfl
@[simp] theorem smul_apply (s : S) (u : GMARedHom A f i j M) (x : A.Block i j) :
    (s • u).toAddHom x = s • u.toAddHom x := rfl

instance instAddCommGroup : AddCommGroup (GMARedHom A f i j M) where
  add_assoc u v w := by ext x; exact add_assoc (u.toAddHom x) (v.toAddHom x) (w.toAddHom x)
  zero_add u := by ext x; exact zero_add (u.toAddHom x)
  add_zero u := by ext x; exact add_zero (u.toAddHom x)
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel u := by ext x; exact neg_add_cancel (u.toAddHom x)
  add_comm u v := by ext x; exact add_comm (u.toAddHom x) (v.toAddHom x)
  sub_eq_add_neg u v := by ext x; exact sub_eq_add_neg (u.toAddHom x) (v.toAddHom x)

instance instModule : Module S (GMARedHom A f i j M) where
  one_smul u := by ext x; exact one_smul S (u.toAddHom x)
  mul_smul s t u := by ext x; exact mul_smul s t (u.toAddHom x)
  smul_zero s := by ext x; exact smul_zero s
  smul_add s u v := by ext x; exact smul_add s (u.toAddHom x) (v.toAddHom x)
  add_smul s t u := by ext x; exact add_smul s t (u.toAddHom x)
  zero_smul u := by ext x; exact zero_smul S (u.toAddHom x)

/-- Any `λ ∈ GMARedHom A f i j M` with `I_red ≤ ker f` automatically vanishes on the entire
reducible block submodule `B'_{i,j} = I_red · A_{i,j} + ∑_{k ≠ i, j} A_{i,k} A_{k,j}`. -/
theorem vanishes_on_reducibleBlockSubmodule (hf : A.reducibilityIdeal ≤ RingHom.ker f)
    (lam : GMARedHom A f i j M) {z : A.Block i j} (hz : z ∈ reducibleBlockSubmodule A i j) :
    lam.toAddHom z = 0 := by
  unfold reducibleBlockSubmodule at hz
  obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Submodule.mem_sup.mp hz
  rw [map_add]
  have h1 : lam.toAddHom z₁ = 0 := by
    refine Submodule.smul_induction_on hz₁ (fun r hr x _ => ?_)
      (fun a b ha hb => by rw [map_add, ha, hb, add_zero])
    rw [lam.map_smul', RingHom.mem_ker.mp (hf hr), zero_smul]
  have h2 : lam.toAddHom z₂ = 0 := by
    let K : Submodule R (A.Block i j) :=
      { carrier := { x | lam.toAddHom x = 0 }
        add_mem' := fun {a b} ha hb => by
          change lam.toAddHom (a + b) = 0
          rw [map_add, ha, hb, add_zero]
        zero_mem' := map_zero _
        smul_mem' := fun r {x} hx => by
          change lam.toAddHom (r • x) = 0
          rw [lam.map_smul', hx, smul_zero] }
    have hle : (⨆ (k : Fin d) (_ : k ≠ i) (_ : k ≠ j),
        Submodule.span R { z : A.Block i j | ∃ (x : A.Block i k) (y : A.Block k j),
          z = A.mul i k j x y }) ≤ K := by
      refine iSup_le fun k => iSup_le fun hki => iSup_le fun hkj => Submodule.span_le.mpr ?_
      rintro z ⟨x, y, rfl⟩
      exact lam.map_inter_mul' k hki hkj x y
    exact hle hz₂
  rw [h1, h2, add_zero]

end GMARedHom

/-- The cocycle associated to `λ ∈ GMARedHom A f i j M`:
`c_λ(g) := χ_j(g)⁻¹ • λ((ρ g)_{i,j}) ∈ Z¹(G, M(χ_i χ_j⁻¹))`. -/
def gmaCocycle {d : ℕ} (A : GMA R d) (ρ : G →* A.Elem) (f : R →+* S)
    (hf : A.reducibilityIdeal ≤ RingHom.ker f) {i j : Fin d} (hij : i ≠ j)
    (lam : GMARedHom A f i j M) :
    Ext1Cocycle (A.diagUnitCharOfFactor ρ f hf i) (A.diagUnitCharOfFactor ρ f hf j) M :=
  ⟨fun g => (((A.diagUnitCharOfFactor ρ f hf j g)⁻¹ : Sˣ) : S) • lam.toAddHom ((ρ g).entry i j),
    by
      intro g h
      dsimp only
      have hmul : lam.toAddHom ((ρ (g * h)).entry i j) =
          ((A.diagUnitCharOfFactor ρ f hf i g : Sˣ) : S) • lam.toAddHom ((ρ h).entry i j) +
          ((A.diagUnitCharOfFactor ρ f hf j h : Sˣ) : S) • lam.toAddHom ((ρ g).entry i j) := by
        rw [map_mul, mul_entry, map_sum]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
        have hj_mem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
        rw [← Finset.add_sum_erase _ _ hj_mem]
        have hrest : ∑ k ∈ (Finset.univ.erase i).erase j,
            lam.toAddHom (A.mul i k j ((ρ g).entry i k) ((ρ h).entry k j)) = 0 := by
          refine Finset.sum_eq_zero fun k hk => ?_
          have hkj : k ≠ j := Finset.ne_of_mem_erase hk
          have hki : k ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
          exact lam.map_inter_mul' k hki hkj _ _
        rw [hrest, add_zero]
        congr 1
        · have h1 : (ρ g).entry i i = (A.diagEquiv i).symm (A.diagComp ρ i g) := by
            simp [diagComp]
          rw [h1, A.mul_diag_left, lam.map_smul']; rfl
        · have h2 : (ρ h).entry j j = (A.diagEquiv j).symm (A.diagComp ρ j h) := by
            simp [diagComp]
          rw [h2, A.mul_diag_right, lam.map_smul']; rfl
      rw [hmul, smul_add, map_mul, mul_inv, Units.val_mul]
      have hterm1 : (((A.diagUnitCharOfFactor ρ f hf j g)⁻¹ : Sˣ) : S) *
            (((A.diagUnitCharOfFactor ρ f hf j h)⁻¹ : Sˣ) : S) *
            ((A.diagUnitCharOfFactor ρ f hf i g : Sˣ) : S) =
          ((A.diagUnitCharOfFactor ρ f hf i g * (A.diagUnitCharOfFactor ρ f hf j g)⁻¹ : Sˣ) : S) *
            (((A.diagUnitCharOfFactor ρ f hf j h)⁻¹ : Sˣ) : S) := by
        rw [Units.val_mul]; ring
      have hterm2 : (((A.diagUnitCharOfFactor ρ f hf j g)⁻¹ : Sˣ) : S) *
            (((A.diagUnitCharOfFactor ρ f hf j h)⁻¹ : Sˣ) : S) *
            ((A.diagUnitCharOfFactor ρ f hf j h : Sˣ) : S) =
          (((A.diagUnitCharOfFactor ρ f hf j g)⁻¹ : Sˣ) : S) := by
        have hcancel : (((A.diagUnitCharOfFactor ρ f hf j h)⁻¹ : Sˣ) : S) *
            ((A.diagUnitCharOfFactor ρ f hf j h : Sˣ) : S) = 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        calc (((A.diagUnitCharOfFactor ρ f hf j g)⁻¹ : Sˣ) : S) *
              (((A.diagUnitCharOfFactor ρ f hf j h)⁻¹ : Sˣ) : S) *
              ((A.diagUnitCharOfFactor ρ f hf j h : Sˣ) : S)
            = (((A.diagUnitCharOfFactor ρ f hf j g)⁻¹ : Sˣ) : S) *
              ((((A.diagUnitCharOfFactor ρ f hf j h)⁻¹ : Sˣ) : S) *
                ((A.diagUnitCharOfFactor ρ f hf j h : Sˣ) : S)) := by ring
          _ = (((A.diagUnitCharOfFactor ρ f hf j g)⁻¹ : Sˣ) : S) * 1 := by rw [hcancel]
          _ = (((A.diagUnitCharOfFactor ρ f hf j g)⁻¹ : Sˣ) : S) := mul_one _
      rw [smul_smul, smul_smul, hterm1, hterm2, ← smul_smul, add_comm]⟩

/-- The `S`-linear map `GMARedHom A f i j M →ₗ[S] Ext1Char χ_i χ_j M`. -/
def gmaExtMap {d : ℕ} (A : GMA R d) (ρ : G →* A.Elem) (f : R →+* S)
    (hf : A.reducibilityIdeal ≤ RingHom.ker f) {i j : Fin d} (hij : i ≠ j) :
    GMARedHom A f i j M →ₗ[S]
      Ext1Char (A.diagUnitCharOfFactor ρ f hf i) (A.diagUnitCharOfFactor ρ f hf j) M where
  toFun lam := Submodule.Quotient.mk (gmaCocycle A ρ f hf hij lam)
  map_add' u v := by
    rw [← Submodule.Quotient.mk_add]
    congr 1
    ext g
    exact smul_add _ _ _
  map_smul' s u := by
    change Submodule.Quotient.mk _ = s • Submodule.Quotient.mk _
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    ext g
    exact smul_comm _ _ _

/-- **Bellaïche–Chenevier Theorem 1.5.5 (`gma_ext_injection` / `LemmaP` core)**:
For any rank-`d` GMA `A` generated by `ρ : G →* A.Elem` (`monoidAlgHom ρ` surjective with lifted
idempotents `eLift`), any `f : R →+* S` killing `I_red`, and any `i ≠ j`, the canonical map
`gmaExtMap : Hom(A_{i,j} / B'_{i,j}, M) → Ext¹_G(χ_j, χ_i; M)` is **INJECTIVE**. -/
theorem gma_ext_injection {d : ℕ} (A : GMA R d) (ρ : G →* A.Elem)
    (hsurj : Function.Surjective (A.monoidAlgHom ρ))
    (eLift : Fin d → MonoidAlgebra R G)
    (heLift : ∀ k : Fin d, A.monoidAlgHom ρ (eLift k) = A.idemp k)
    (f : R →+* S) (hf : A.reducibilityIdeal ≤ RingHom.ker f)
    {i j : Fin d} (hij : i ≠ j) :
    Function.Injective (gmaExtMap (M := M) A ρ f hf hij) := by
  rw [injective_iff_map_eq_zero]
  intro lam hlam
  rw [gmaExtMap, LinearMap.coe_mk, AddHom.coe_mk, Submodule.Quotient.mk_eq_zero] at hlam
  obtain ⟨m, hm⟩ := hlam
  have hgroup : ∀ g : G, lam.toAddHom ((ρ g).entry i j) =
      (A.diagCharOfFactor ρ f hf i g - A.diagCharOfFactor ρ f hf j g) • m := by
    intro g
    have hg := hm g
    change (((A.diagUnitCharOfFactor ρ f hf j g)⁻¹ : Sˣ) : S) • lam.toAddHom ((ρ g).entry i j) =
      ((A.diagUnitCharOfFactor ρ f hf i g * (A.diagUnitCharOfFactor ρ f hf j g)⁻¹ : Sˣ) : S) • m - m at hg
    have hmul := congrArg (fun v : M => ((A.diagUnitCharOfFactor ρ f hf j g : Sˣ) : S) • v) hg
    simp only [smul_smul, smul_sub] at hmul
    have hc1 : ((A.diagUnitCharOfFactor ρ f hf j g : Sˣ) : S) *
        (((A.diagUnitCharOfFactor ρ f hf j g)⁻¹ : Sˣ) : S) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hc2 : ((A.diagUnitCharOfFactor ρ f hf j g : Sˣ) : S) *
        ((A.diagUnitCharOfFactor ρ f hf i g * (A.diagUnitCharOfFactor ρ f hf j g)⁻¹ : Sˣ) : S) =
        ((A.diagUnitCharOfFactor ρ f hf i g : Sˣ) : S) := by
      rw [Units.val_mul]
      calc ((A.diagUnitCharOfFactor ρ f hf j g : Sˣ) : S) *
            (((A.diagUnitCharOfFactor ρ f hf i g : Sˣ) : S) *
              (((A.diagUnitCharOfFactor ρ f hf j g)⁻¹ : Sˣ) : S))
          = (((A.diagUnitCharOfFactor ρ f hf j g : Sˣ) : S) *
              (((A.diagUnitCharOfFactor ρ f hf j g)⁻¹ : Sˣ) : S)) *
              ((A.diagUnitCharOfFactor ρ f hf i g : Sˣ) : S) := by ring
        _ = 1 * ((A.diagUnitCharOfFactor ρ f hf i g : Sˣ) : S) := by rw [hc1]
        _ = ((A.diagUnitCharOfFactor ρ f hf i g : Sˣ) : S) := one_mul _
    rw [hc1, one_smul, hc2] at hmul
    rw [hmul, sub_smul]
    rfl
  have halg : ∀ u : MonoidAlgebra R G,
      lam.toAddHom ((A.monoidAlgHom ρ u).entry i j) =
        (monoidAlgChar f (A.diagCharOfFactor ρ f hf i) u -
          monoidAlgChar f (A.diagCharOfFactor ρ f hf j) u) • m := by
    intro u
    refine MonoidAlgebra.induction_on
      (motive := fun u => lam.toAddHom ((A.monoidAlgHom ρ u).entry i j) =
        (monoidAlgChar f (A.diagCharOfFactor ρ f hf i) u -
          monoidAlgChar f (A.diagCharOfFactor ρ f hf j) u) • m) u ?_ ?_ ?_
    · intro g
      rw [monoidAlgHom_of, monoidAlgChar_of, monoidAlgChar_of]
      exact hgroup g
    · intro u₁ u₂ ih₁ ih₂
      simp only [map_add, add_entry, ih₁, ih₂]
      rw [← add_smul]
      congr 1
      ring
    · intro r u₁ ih
      rw [monoidAlgHom_smul, scalarHom_mul, smulElem_entry, lam.map_smul', ih, smul_smul,
        monoidAlgChar_smul, monoidAlgChar_smul, mul_sub]
  ext x
  obtain ⟨u, hu⟩ := hsurj (A.blockElem i j x)
  let u' : MonoidAlgebra R G := eLift i * u * eLift j
  have hmu' : A.monoidAlgHom ρ u' = A.blockElem i j x := by
    simp only [u', map_mul, heLift, hu]
    exact A.idemp_mul_blockElem_mul_idemp i j x
  have hχi_ej : monoidAlgChar f (A.diagCharOfFactor ρ f hf i) (eLift j) = 0 := by
    rw [A.monoidAlgChar_diagComp ρ f hf i (eLift j), heLift j]
    simp [idemp, A.blockElem_entry_ne (Or.inl hij)]
  have hχj_ei : monoidAlgChar f (A.diagCharOfFactor ρ f hf j) (eLift i) = 0 := by
    rw [A.monoidAlgChar_diagComp ρ f hf j (eLift i), heLift i]
    simp [idemp, A.blockElem_entry_ne (Or.inl hij.symm)]
  have hx := halg u'
  rw [hmu', blockElem_entry_same] at hx
  simp only [u', map_mul, hχi_ej, hχj_ei, mul_zero, zero_mul, sub_self, zero_smul] at hx
  exact hx

/-- Specialization of `gma_ext_injection` to rank `d = 3` (`U(3)` `CountI`, blocks `(0, 1)` and
`(1, 2)`). -/
theorem gma_ext_injection_u3 (A : GMA R 3) (ρ : G →* A.Elem)
    (hsurj : Function.Surjective (A.monoidAlgHom ρ))
    (eLift : Fin 3 → MonoidAlgebra R G)
    (heLift : ∀ k : Fin 3, A.monoidAlgHom ρ (eLift k) = A.idemp k)
    (f : R →+* S) (hf : A.reducibilityIdeal ≤ RingHom.ker f) :
    Function.Injective (gmaExtMap (M := M) A ρ f hf (by decide : (0 : Fin 3) ≠ 1)) ∧
    Function.Injective (gmaExtMap (M := M) A ρ f hf (by decide : (1 : Fin 3) ≠ 2)) :=
  ⟨gma_ext_injection A ρ hsurj eLift heLift f hf (by decide),
   gma_ext_injection A ρ hsurj eLift heLift f hf (by decide)⟩

/-- Specialization of `gma_ext_injection` to rank `d = 4` (`Sp₄` `CountII`/`CountIII`, blocks
`(0, 1)`, `(0, 2)`, `(1, 2)`, and `(0, 3)`). -/
theorem gma_ext_injection_sp4 (A : GMA R 4) (ρ : G →* A.Elem)
    (hsurj : Function.Surjective (A.monoidAlgHom ρ))
    (eLift : Fin 4 → MonoidAlgebra R G)
    (heLift : ∀ k : Fin 4, A.monoidAlgHom ρ (eLift k) = A.idemp k)
    (f : R →+* S) (hf : A.reducibilityIdeal ≤ RingHom.ker f) :
    Function.Injective (gmaExtMap (M := M) A ρ f hf (by decide : (0 : Fin 4) ≠ 1)) ∧
    Function.Injective (gmaExtMap (M := M) A ρ f hf (by decide : (0 : Fin 4) ≠ 2)) ∧
    Function.Injective (gmaExtMap (M := M) A ρ f hf (by decide : (1 : Fin 4) ≠ 2)) ∧
    Function.Injective (gmaExtMap (M := M) A ρ f hf (by decide : (0 : Fin 4) ≠ 3)) :=
  ⟨gma_ext_injection A ρ hsurj eLift heLift f hf (by decide),
   gma_ext_injection A ρ hsurj eLift heLift f hf (by decide),
   gma_ext_injection A ρ hsurj eLift heLift f hf (by decide),
   gma_ext_injection A ρ hsurj eLift heLift f hf (by decide)⟩

/-- **Module-length inequality from `gma_ext_injection`**:
`len_S(Hom(A_{i,j} / B'_{i,j}, M)) ≤ len_S(Ext¹_G(χ_j, χ_i; M))`. -/
theorem length_gmaRedHom_le_ext1 {d : ℕ} (A : GMA R d) (ρ : G →* A.Elem)
    (hsurj : Function.Surjective (A.monoidAlgHom ρ))
    (eLift : Fin d → MonoidAlgebra R G)
    (heLift : ∀ k : Fin d, A.monoidAlgHom ρ (eLift k) = A.idemp k)
    (f : R →+* S) (hf : A.reducibilityIdeal ≤ RingHom.ker f)
    {i j : Fin d} (hij : i ≠ j) :
    Module.length S (GMARedHom A f i j M) ≤
      Module.length S (Ext1Char (A.diagUnitCharOfFactor ρ f hf i)
        (A.diagUnitCharOfFactor ρ f hf j) M) :=
  Module.length_le_of_injective (gmaExtMap (M := M) A ρ f hf hij)
    (gma_ext_injection A ρ hsurj eLift heLift f hf hij)

/-! ### 2.2 Selmer Extension Length Bound by `len(R / I_red)` & Monic Trace-Difference Valuation -/

/-- Exact `R`-module length of a finite product `(Fin r → N)` equals `r * len_R(N)`. -/
theorem length_pi_fin (R N : Type*) [Ring R] [AddCommGroup N] [Module R N] (r : ℕ) :
    Module.length R (Fin r → N) = (r : ℕ∞) * Module.length R N := by
  induction r with
  | zero =>
    have : Subsingleton (Fin 0 → N) := inferInstance
    simp
  | succ r ih =>
    let e : (Fin (r + 1) → N) ≃ₗ[R] N × (Fin r → N) :=
      { toFun := fun v => (v 0, fun i => v i.succ)
        invFun := fun p => Fin.cons p.1 p.2
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun v => by
          ext i
          refine Fin.cases rfl (fun _ => rfl) i
        right_inv := fun p => by
          ext
          · rfl
          · rfl }
    have hlen_e : Module.length R (Fin (r + 1) → N) = Module.length R (N × (Fin r → N)) :=
      le_antisymm (Module.length_le_of_injective e.toLinearMap e.injective)
        (Module.length_le_of_injective e.symm.toLinearMap e.symm.injective)
    have hprod : Module.length R (N × (Fin r → N)) =
        Module.length R N + Module.length R (Fin r → N) := by
      have hex : Function.Exact (LinearMap.inl R N (Fin r → N)) (LinearMap.snd R N (Fin r → N)) := by
        intro p
        constructor
        · intro hp
          exact ⟨p.1, Prod.ext rfl hp.symm⟩
        · rintro ⟨a, rfl⟩; rfl
      exact Module.length_eq_add_of_exact (LinearMap.inl R N (Fin r → N))
        (LinearMap.snd R N (Fin r → N)) LinearMap.inl_injective Prod.snd_surjective hex
    rw [hlen_e, hprod, ih]
    push_cast
    ring

/-- **Selmer / Reducible-Quotient Length Bound (`LemmaP` / `MainCotSpan`)**:
If an `R`-module `Sel` is annihilated by `I := A.reducibilityIdeal` and generated over `R` by `r`
elements, then `len_R(Sel) ≤ r * len_R(R / I_red)`. -/
theorem selmer_length_le_reducibility_length {d : ℕ} (A : GMA R d)
    {Sel : Type*} [AddCommGroup Sel] [Module R Sel]
    (hann : ∀ a ∈ A.reducibilityIdeal, ∀ x : Sel, a • x = 0)
    {r : ℕ} (gen : Fin r → Sel) (hgen : Submodule.span R (Set.range gen) = ⊤) :
    Module.length R Sel ≤ (r : ℕ∞) * Module.length R (R ⧸ A.reducibilityIdeal) := by
  let compMap : Fin r → ((R ⧸ A.reducibilityIdeal) →ₗ[R] Sel) := fun i =>
    Submodule.liftQ A.reducibilityIdeal (LinearMap.toSpanSingleton R Sel (gen i))
      (fun a ha => LinearMap.mem_ker.mpr (hann a ha (gen i)))
  let qMap : (Fin r → R ⧸ A.reducibilityIdeal) →ₗ[R] Sel :=
    { toFun := fun v => ∑ i : Fin r, compMap i (v i)
      map_add' := fun v w => by
        simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
      map_smul' := fun a v => by
        simp only [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        exact map_smul (compMap i) a (v i) }
  have hsurj : Function.Surjective qMap := by
    intro y
    have hy : y ∈ Submodule.span R (Set.range gen) := hgen ▸ Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hy
    obtain ⟨c, rfl⟩ := hy
    refine ⟨fun i => Submodule.Quotient.mk (c i), ?_⟩
    rfl
  calc Module.length R Sel
      ≤ Module.length R (Fin r → R ⧸ A.reducibilityIdeal) :=
        Module.length_le_of_surjective qMap hsurj
    _ = (r : ℕ∞) * Module.length R (R ⧸ A.reducibilityIdeal) :=
        length_pi_fin R (R ⧸ A.reducibilityIdeal) r

/-- **Cayley–Hamilton / Monic Polynomial Descent to `I_red ∩ 𝒪`**:
If `f : 𝒪 →+* R` is a ring homomorphism and `δ ∈ A.reducibilityIdeal` is a root of a polynomial
`P ∈ 𝒪[X]` (`Polynomial.eval₂ f δ P = 0`), then `P.coeff 0 ∈ A.reducibilityIdeal.comap f`! -/
theorem constantCoeff_mem_comap_reducibilityIdeal_of_eval₂_zero
    {𝒪 : Type*} [CommRing 𝒪] {d : ℕ} (A : GMA R d) (f : 𝒪 →+* R)
    {δ : R} (hδ : δ ∈ A.reducibilityIdeal) {P : 𝒪[X]} (hP : Polynomial.eval₂ f δ P = 0) :
    P.coeff 0 ∈ A.reducibilityIdeal.comap f := by
  change f (P.coeff 0) ∈ A.reducibilityIdeal
  have hsplit : P = Polynomial.C (P.coeff 0) + Polynomial.X * P.divX := by
    rw [add_comm]
    exact (Polynomial.X_mul_divX_add P).symm
  have hev : f (P.coeff 0) + δ * Polynomial.eval₂ f δ P.divX = 0 := by
    have h0 := congrArg (Polynomial.eval₂ f δ) hsplit
    rw [hP, Polynomial.eval₂_add, Polynomial.eval₂_C, Polynomial.eval₂_mul,
      Polynomial.eval₂_X] at h0
    exact h0.symm
  have heq : f (P.coeff 0) = -(δ * Polynomial.eval₂ f δ P.divX) := eq_neg_of_add_eq_zero_left hev
  rw [heq]
  exact A.reducibilityIdeal.neg_mem (A.reducibilityIdeal.mul_mem_right _ hδ)

/-- Over a DVR `(𝒪, ϖ)`, `length_𝒪(𝒪 ⧸ (ϖ^k)) = k`. -/
theorem length_dvr_quotient_pow {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪]
    [IsDiscreteValuationRing 𝒪] {ϖ : 𝒪} (hϖ : Irreducible ϖ) (k : ℕ) :
    Module.length 𝒪 (𝒪 ⧸ Ideal.span ({ϖ ^ k} : Set 𝒪)) = (k : ℕ∞) := by
  induction k with
  | zero =>
    rw [pow_zero, Ideal.span_singleton_one]
    have : Subsingleton (𝒪 ⧸ (⊤ : Ideal 𝒪)) := Submodule.Quotient.subsingleton_iff.mpr rfl
    simp
  | succ k ih =>
    let I1 : Ideal 𝒪 := Ideal.span ({ϖ ^ (k + 1)} : Set 𝒪)
    let I0 : Ideal 𝒪 := Ideal.span ({ϖ ^ k} : Set 𝒪)
    have hle : I1 ≤ I0 := by
      rw [Ideal.span_singleton_le_span_singleton, pow_succ]
      exact dvd_mul_right _ _
    let proj : (𝒪 ⧸ I1) →ₗ[𝒪] (𝒪 ⧸ I0) := Submodule.factor hle
    have hsurj : Function.Surjective proj := Submodule.factor_surjective hle
    let incl : (𝒪 ⧸ Ideal.span ({ϖ} : Set 𝒪)) →ₗ[𝒪] (𝒪 ⧸ I1) :=
      Submodule.liftQ (Ideal.span ({ϖ} : Set 𝒪))
        ((Submodule.mkQ I1).comp (LinearMap.mulLeft 𝒪 (ϖ ^ k)))
        (by
          rw [Ideal.span_le, Set.singleton_subset_iff]
          change (Submodule.mkQ I1) (ϖ ^ k * ϖ) = 0
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← pow_succ]
          exact Ideal.subset_span rfl)
    have hinj : Function.Injective incl := by
      rw [injective_iff_map_eq_zero]
      intro q hq
      induction q using Quotient.inductionOn' with
      | h a =>
        change (Submodule.mkQ I1) (ϖ ^ k * a) = 0 at hq
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
          Ideal.mem_span_singleton, pow_succ] at hq
        have hϖk : ϖ ^ k ≠ 0 := pow_ne_zero k hϖ.ne_zero
        have hdvd : ϖ ∣ a := (mul_dvd_mul_iff_left hϖk).mp hq
        exact (Submodule.Quotient.mk_eq_zero _).mpr (Ideal.mem_span_singleton.mpr hdvd)
    have hex : Function.Exact incl proj := by
      intro q
      induction q using Quotient.inductionOn' with
      | h x =>
        change (Submodule.Quotient.mk x : 𝒪 ⧸ I0) = 0 ↔ _
        rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]
        constructor
        · rintro ⟨a, rfl⟩
          exact ⟨Submodule.Quotient.mk a, rfl⟩
        · rintro ⟨q', hq'⟩
          induction q' using Quotient.inductionOn' with
          | h a =>
            have hsub : ϖ ^ k * a - x ∈ I1 := by
              have h1 : (Submodule.Quotient.mk (ϖ ^ k * a) : 𝒪 ⧸ I1) =
                  Submodule.Quotient.mk x := hq'
              exact (Submodule.Quotient.eq I1).mp h1
            have hsub0 : ϖ ^ k * a - x ∈ I0 := hle hsub
            rw [Ideal.mem_span_singleton] at hsub0
            obtain ⟨b, hb⟩ := hsub0
            exact ⟨a - b, by linear_combination -hb⟩
    have hmax : (Ideal.span ({ϖ} : Set 𝒪)).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible hϖ
    have hsimple : IsSimpleModule 𝒪 (𝒪 ⧸ Ideal.span ({ϖ} : Set 𝒪)) := by
      rw [isSimpleModule_iff_isCoatom]
      exact hmax.out
    have hlen1 : Module.length 𝒪 (𝒪 ⧸ Ideal.span ({ϖ} : Set 𝒪)) = 1 :=
      Module.length_eq_one_iff.mpr hsimple
    have hadd := Module.length_eq_add_of_exact incl proj hinj hsurj hex
    rw [hadd, hlen1, ih]
    push_cast
    ring

/-- **Monic Trace-Difference Valuation Bound on `I_red ∩ 𝒪`**:
Over a DVR `(𝒪, ϖ)`, if `δ ∈ A.reducibilityIdeal` satisfies a polynomial `P ∈ 𝒪[X]` whose
constant coefficient factors up to a unit as `u * ϖ ^ (∑_{ρ ∈ X} v ρ)` (e.g.
`∏_{ρ ∈ X} (t_ρ - t_eis)` with `v_ϖ(t_ρ - t_eis) = v ρ`), then:
`len_𝒪(𝒪 ⧸ (I_red ∩ 𝒪)) ≤ ∑_{ρ ∈ X} v ρ`! -/
theorem reducibility_comap_length_le_sum_val {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪]
    [IsDiscreteValuationRing 𝒪] {ϖ : 𝒪} (hϖ : Irreducible ϖ)
    {d : ℕ} (A : GMA R d) (f : 𝒪 →+* R)
    {δ : R} (hδ : δ ∈ A.reducibilityIdeal) {P : 𝒪[X]} (hP : Polynomial.eval₂ f δ P = 0)
    {ι : Type*} (X : Finset ι) (v : ι → ℕ)
    (hfac : ∃ u : 𝒪ˣ, P.coeff 0 = (u : 𝒪) * ϖ ^ (∑ ρ ∈ X, v ρ)) :
    Module.length 𝒪 (𝒪 ⧸ A.reducibilityIdeal.comap f) ≤ ((∑ ρ ∈ X, v ρ : ℕ) : ℕ∞) := by
  have hc0 : P.coeff 0 ∈ A.reducibilityIdeal.comap f :=
    constantCoeff_mem_comap_reducibilityIdeal_of_eval₂_zero A f hδ hP
  obtain ⟨u, hu⟩ := hfac
  have hpow_mem : ϖ ^ (∑ ρ ∈ X, v ρ) ∈ A.reducibilityIdeal.comap f := by
    have h1 : ((u⁻¹ : 𝒪ˣ) : 𝒪) * P.coeff 0 ∈ A.reducibilityIdeal.comap f :=
      (A.reducibilityIdeal.comap f).mul_mem_left _ hc0
    rw [hu, ← _root_.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul] at h1
    exact h1
  have hle : Ideal.span ({ϖ ^ (∑ ρ ∈ X, v ρ)} : Set 𝒪) ≤ A.reducibilityIdeal.comap f :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hpow_mem)
  calc Module.length 𝒪 (𝒪 ⧸ A.reducibilityIdeal.comap f)
      ≤ Module.length 𝒪 (𝒪 ⧸ Ideal.span ({ϖ ^ (∑ ρ ∈ X, v ρ)} : Set 𝒪)) :=
        Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)
    _ = ((∑ ρ ∈ X, v ρ : ℕ) : ℕ∞) := length_dvr_quotient_pow hϖ (∑ ρ ∈ X, v ρ)

end GMAExtInjection

/-! ## Section 3: Concrete 3D `U(3)` (`CountI`) & 4D `Sp₄` (`CountII`/`CountIII`) Involution GMAs & Parity Forcing -/

section U3Sp4InvolutionGMA

open GMA

variable {R : Type*} [CommRing R]

/-- A Bellaïche–Chenevier **anti-involution** `τ` on a rank-`d` GMA `A` along an involutive
index permutation `σ : Fin d ≃ Fin d` (`σ (σ i) = i`), represented directly as an `R`-linear ring
anti-involution `τElem : A.Elem →+ A.Elem` compatible with the orthogonal idempotents `A.idemp i`.
This representation is completely free of dependent-cast boilerplate. -/
structure GMAInvolution {d : ℕ} (A : GMA R d) (σ : Fin d ≃ Fin d) where
  σ_invol : ∀ i : Fin d, σ (σ i) = i
  τElem : A.Elem →+ A.Elem
  τElem_invol : ∀ x : A.Elem, τElem (τElem x) = x
  τElem_one : τElem 1 = 1
  τElem_mul : ∀ x y : A.Elem, τElem (x * y) = τElem y * τElem x
  τElem_smul : ∀ (r : R) (x : A.Elem), τElem (smulElem r x) = smulElem r (τElem x)
  τElem_idemp : ∀ i : Fin d, τElem (A.idemp i) = A.idemp (σ i)
  τElem_diag : ∀ (i : Fin d) (r : R),
    (τElem (A.blockElem i i ((A.diagEquiv i).symm r))).entry (σ i) (σ i) =
      (A.diagEquiv (σ i)).symm r

namespace GMAInvolution

variable {d : ℕ} {A : GMA R d} {σ : Fin d ≃ Fin d} (τ : GMAInvolution A σ)

/-- The induced `R`-linear block duality map `τBlock i j : A.Block i j →ₗ[R] A.Block (σ j) (σ i)`. -/
def τBlock (i j : Fin d) : A.Block i j →ₗ[R] A.Block (σ j) (σ i) where
  toFun x := (τ.τElem (A.blockElem i j x)).entry (σ j) (σ i)
  map_add' x y := by
    have hadd : A.blockElem i j (x + y) = A.blockElem i j x + A.blockElem i j y := by
      ext a b
      by_cases h : a = i ∧ b = j
      · rcases h with ⟨rfl, rfl⟩; simp
      · simp [A.blockElem_entry_ne (by tauto)]
    rw [hadd, map_add, add_entry]
  map_smul' r x := by
    have hsm : A.blockElem i j (r • x) = smulElem r (A.blockElem i j x) := by
      ext a b
      by_cases h : a = i ∧ b = j
      · rcases h with ⟨rfl, rfl⟩; simp
      · simp [A.blockElem_entry_ne (by tauto)]
    rw [hsm, τ.τElem_smul, smulElem_entry]; rfl

/-- `τElem` maps single-block elements `(i, j)` directly to single-block elements `(σ j, σ i)`. -/
theorem τElem_blockElem (i j : Fin d) (x : A.Block i j) :
    τ.τElem (A.blockElem i j x) = A.blockElem (σ j) (σ i) (τ.τBlock i j x) := by
  calc τ.τElem (A.blockElem i j x)
      = τ.τElem (A.idemp i * A.blockElem i j x * A.idemp j) := by
        rw [A.idemp_mul_blockElem_mul_idemp]
    _ = τ.τElem (A.idemp j) * τ.τElem (A.idemp i * A.blockElem i j x) := τ.τElem_mul _ _
    _ = τ.τElem (A.idemp j) * (τ.τElem (A.blockElem i j x) * τ.τElem (A.idemp i)) := by
        rw [τ.τElem_mul]
    _ = A.idemp (σ j) * τ.τElem (A.blockElem i j x) * A.idemp (σ i) := by
        rw [τ.τElem_idemp, τ.τElem_idemp, mul_assoc]
    _ = A.blockElem (σ j) (σ i) (τ.τBlock i j x) := A.idemp_mul_elem_mul_idemp (σ j) (σ i) _

/-- Entrywise characterization of `τElem`: `(τElem x)_{σ j, σ i} = τBlock i j (x_{i, j})`. -/
theorem τElem_entry_apply (x : A.Elem) (i j : Fin d) :
    (τ.τElem x).entry (σ j) (σ i) = τ.τBlock i j (x.entry i j) := by
  have h1 : A.idemp (σ j) * τ.τElem x * A.idemp (σ i) =
      A.blockElem (σ j) (σ i) ((τ.τElem x).entry (σ j) (σ i)) :=
    A.idemp_mul_elem_mul_idemp (σ j) (σ i) (τ.τElem x)
  have h2 : A.idemp (σ j) * τ.τElem x * A.idemp (σ i) =
      τ.τElem (A.blockElem i j (x.entry i j)) := by
    rw [← A.idemp_mul_elem_mul_idemp i j x, τ.τElem_mul, τ.τElem_mul,
      τ.τElem_idemp, τ.τElem_idemp, mul_assoc]
  rw [h2, τ.τElem_blockElem] at h1
  have h3 := congrArg (fun e : A.Elem => e.entry (σ j) (σ i)) h1
  simpa using h3.symm

/-- `τBlock` is anti-multiplicative on blocks. -/
theorem τBlock_anti_mul (i j k : Fin d) (x : A.Block i j) (y : A.Block j k) :
    τ.τBlock i k (A.mul i j k x y) =
      A.mul (σ k) (σ j) (σ i) (τ.τBlock j k y) (τ.τBlock i j x) := by
  have h := congrArg (fun e : A.Elem => e.entry (σ k) (σ i))
    (by
      calc τ.τElem (A.blockElem i k (A.mul i j k x y))
          = τ.τElem (A.blockElem i j x * A.blockElem j k y) := by
            rw [A.blockElem_mul_blockElem_same]
        _ = τ.τElem (A.blockElem j k y) * τ.τElem (A.blockElem i j x) := τ.τElem_mul _ _
        _ = A.blockElem (σ k) (σ j) (τ.τBlock j k y) *
              A.blockElem (σ j) (σ i) (τ.τBlock i j x) := by
            rw [τ.τElem_blockElem, τ.τElem_blockElem]
        _ = A.blockElem (σ k) (σ i)
              (A.mul (σ k) (σ j) (σ i) (τ.τBlock j k y) (τ.τBlock i j x)) :=
            A.blockElem_mul_blockElem_same _ _ _ _ _)
  simpa [τBlock] using h

/-- `τElem` preserves GMA trace: `tr(τElem x) = tr(x)`. -/
theorem tr_τElem (x : A.Elem) : A.tr (τ.τElem x) = A.tr x := by
  rw [tr_apply, tr_apply, ← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [τ.τElem_entry_apply x i i]
  have h1 : x.entry i i = (A.diagEquiv i).symm (A.diagEquiv i (x.entry i i)) := by simp
  conv_lhs => rw [h1]
  change A.diagEquiv (σ i) ((τ.τElem (A.blockElem i i ((A.diagEquiv i).symm _))).entry (σ i) (σ i)) = _
  rw [τ.τElem_diag i, LinearEquiv.apply_symm_apply]

/-- `τBlock i j` is an `R`-linear isomorphism `A.Block i j ≃ₗ[R] A.Block (σ j) (σ i)`. -/
def τBlockEquiv (i j : Fin d) : A.Block i j ≃ₗ[R] A.Block (σ j) (σ i) where
  toLinearMap := τ.τBlock i j
  invFun y := (τ.τElem (A.blockElem (σ j) (σ i) y)).entry i j
  left_inv x := by
    change (τ.τElem (A.blockElem (σ j) (σ i) (τ.τBlock i j x))).entry i j = x
    rw [← τ.τElem_blockElem, τ.τElem_invol, A.blockElem_entry_same]
  right_inv y := by
    dsimp only
    have hi : A.idemp i = τ.τElem (A.idemp (σ i)) := by rw [τ.τElem_idemp, τ.σ_invol]
    have hj : A.idemp j = τ.τElem (A.idemp (σ j)) := by rw [τ.τElem_idemp, τ.σ_invol]
    have hinv : τ.τElem (A.blockElem (σ j) (σ i) y) =
        A.blockElem i j ((τ.τElem (A.blockElem (σ j) (σ i) y)).entry i j) := by
      calc τ.τElem (A.blockElem (σ j) (σ i) y)
          = τ.τElem (A.idemp (σ j) * A.blockElem (σ j) (σ i) y * A.idemp (σ i)) := by
            rw [A.idemp_mul_blockElem_mul_idemp]
        _ = τ.τElem (A.idemp (σ i)) * τ.τElem (A.blockElem (σ j) (σ i) y) * τ.τElem (A.idemp (σ j)) := by
            rw [τ.τElem_mul, τ.τElem_mul, mul_assoc]
        _ = A.idemp i * τ.τElem (A.blockElem (σ j) (σ i) y) * A.idemp j := by
            rw [← hi, ← hj]
        _ = A.blockElem i j ((τ.τElem (A.blockElem (σ j) (σ i) y)).entry i j) :=
            A.idemp_mul_elem_mul_idemp i j _
    change (τ.τElem (A.blockElem i j ((τ.τElem (A.blockElem (σ j) (σ i) y)).entry i j))).entry
      (σ j) (σ i) = y
    rw [← hinv, τ.τElem_invol, A.blockElem_entry_same]

/-- `τ` identifies the pairwise ideals `pairIdeal (σ j) (σ i) = pairIdeal i j`. -/
theorem pairIdeal_τ_eq (τ : GMAInvolution A σ) (i j : Fin d) :
    A.pairIdeal (σ j) (σ i) = A.pairIdeal i j := by
  have hle : ∀ (a b : Fin d), A.pairIdeal a b ≤ A.pairIdeal (σ b) (σ a) := by
    intro a b
    rw [pairIdeal_le_iff]
    intro x y
    have hmul := τ.τBlock_anti_mul a b a x y
    have heq : A.diagEquiv a (A.mul a b a x y) =
        A.diagEquiv (σ a) (A.mul (σ a) (σ b) (σ a) (τ.τBlock b a y) (τ.τBlock a b x)) := by
      have h1 : A.mul a b a x y = (A.diagEquiv a).symm (A.diagEquiv a (A.mul a b a x y)) := by simp
      have h2 := congrArg (A.diagEquiv (σ a)) hmul
      conv_lhs at h2 => rw [h1]
      change A.diagEquiv (σ a)
        ((τ.τElem (A.blockElem a a ((A.diagEquiv a).symm _))).entry (σ a) (σ a)) = _ at h2
      rw [τ.τElem_diag a, LinearEquiv.apply_symm_apply] at h2
      exact h2
    rw [heq, A.mul_comm_trace (σ a) (σ b)]
    exact A.mem_pairIdeal_mul (σ b) (σ a) (τ.τBlock a b x) (τ.τBlock b a y)
  apply le_antisymm
  · have h := hle (σ j) (σ i)
    rwa [τ.σ_invol i, τ.σ_invol j] at h
  · exact hle i j

end GMAInvolution

/-! ### 3.1 Concrete 3D Unitary `U(3)` GMA (`CountI`) -/

/-- Index reversal involution `σ₃ : 0 ↔ 2, 1 ↔ 1` on `Fin 3`. -/
def rev3 : Fin 3 ≃ Fin 3 where
  toFun := ![2, 1, 0]
  invFun := ![2, 1, 0]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

theorem rev3_invol (i : Fin 3) : rev3 (rev3 i) = i := rev3.left_inv i

/-- Anti-diagonal symmetric involution matrix `J₃ = [[0,0,1],[0,1,0],[1,0,0]]` for `U(3)`. -/
def J3 (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  Matrix.of fun i j => if j = rev3 i then 1 else 0

theorem J3_transpose (R : Type*) [CommRing R] : (J3 R)ᵀ = J3 R := by
  ext i j
  simp only [Matrix.transpose_apply, J3, Matrix.of_apply]
  have hiff : i = rev3 j ↔ j = rev3 i := by
    constructor <;> intro h <;> rw [h, rev3_invol]
  simp [hiff]

theorem J3_mul_J3 (R : Type*) [CommRing R] : J3 R * J3 R = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (rev3 i)]
  · simp [J3, Matrix.one_apply, rev3_invol, eq_comm]
  · intro k _ hki
    simp [J3, hki]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Explicit `R`-valued entry projection for `matrixGMA R d`, keeping the return type syntactically
`R` (never `(matrixGMA R d).Block a b`) for clean ring arithmetic. -/
def matEntry {d : ℕ} (x : (matrixGMA R d).Elem) (i j : Fin d) : R :=
  x.entry i j

/-- Concrete 3D unitary conjugate-self-dual anti-involution `X ↦ J₃ Xᵀ J₃` on `matrixGMA R 3`. -/
def u3MatrixInvolution (R : Type*) [CommRing R] :
    GMAInvolution (matrixGMA R 3) rev3 where
  σ_invol := rev3_invol
  τElem :=
    { toFun := fun x => ⟨fun a b => x.entry (rev3 b) (rev3 a)⟩
      map_zero' := by ext a b; rfl
      map_add' := fun _ _ => by ext a b; rfl }
  τElem_invol x := by
    ext a b
    show matEntry x (rev3 (rev3 a)) (rev3 (rev3 b)) = matEntry x a b
    rw [rev3_invol, rev3_invol]
  τElem_one := by
    ext a b
    by_cases hab : a = b
    · subst hab
      change (1 : (matrixGMA R 3).Elem).entry (rev3 a) (rev3 a) =
        (1 : (matrixGMA R 3).Elem).entry a a
      rw [one_entry_diag, one_entry_diag]; rfl
    · have hne : rev3 b ≠ rev3 a := fun h => hab (rev3.injective h).symm
      change (1 : (matrixGMA R 3).Elem).entry (rev3 b) (rev3 a) =
        (1 : (matrixGMA R 3).Elem).entry a b
      rw [one_entry_off hne, one_entry_off hab]; rfl
  τElem_mul x y := by
    ext a b
    change (∑ k : Fin 3, matEntry x (rev3 b) k * matEntry y k (rev3 a)) =
      ∑ j : Fin 3, matEntry y (rev3 j) (rev3 a) * matEntry x (rev3 b) (rev3 j)
    rw [← Equiv.sum_comp rev3]
    refine Finset.sum_congr rfl fun j _ => mul_comm _ _
  τElem_smul r x := by ext a b; rfl
  τElem_idemp i := by
    ext a b
    change (GMA.idemp (matrixGMA R 3) i).entry (rev3 b) (rev3 a) =
      (GMA.idemp (matrixGMA R 3) (rev3 i)).entry a b
    by_cases h : a = rev3 i ∧ b = rev3 i
    · rcases h with ⟨rfl, rfl⟩
      have h1 : (GMA.idemp (matrixGMA R 3) i).entry (rev3 (rev3 i)) (rev3 (rev3 i)) = (1 : R) := by
        rw [rev3_invol, idemp, blockElem_entry_same]; rfl
      have h2 : (GMA.idemp (matrixGMA R 3) (rev3 i)).entry (rev3 i) (rev3 i) = (1 : R) := by
        rw [idemp, blockElem_entry_same]; rfl
      exact h1.trans h2.symm
    · have hne : rev3 b ≠ i ∨ rev3 a ≠ i := by
        by_contra hc
        push Not at hc
        apply h
        exact ⟨by rw [← hc.2, rev3_invol], by rw [← hc.1, rev3_invol]⟩
      have h1 : (GMA.idemp (matrixGMA R 3) i).entry (rev3 b) (rev3 a) = (0 : R) :=
        GMA.blockElem_entry_ne _ hne _
      have h2 : (GMA.idemp (matrixGMA R 3) (rev3 i)).entry a b = (0 : R) :=
        GMA.blockElem_entry_ne _ (by tauto) _
      exact h1.trans h2.symm
  τElem_diag i r := by
    change (GMA.blockElem (matrixGMA R 3) i i r).entry (rev3 (rev3 i)) (rev3 (rev3 i)) = r
    rw [rev3_invol]; exact GMA.blockElem_entry_same (matrixGMA R 3) i i r

theorem u3MatrixInvolution_eq_J3_conj (R : Type*) [CommRing R] (x : (matrixGMA R 3).Elem) :
    matrixGMAElemEquiv R 3 ((u3MatrixInvolution R).τElem x) =
      J3 R * (matrixGMAElemEquiv R 3 x)ᵀ * J3 R := by
  ext i j
  change matEntry x (rev3 j) (rev3 i) =
    ∑ k : Fin 3, (∑ m : Fin 3, (J3 R) i m * matEntry x k m) * (J3 R) k j
  rw [Finset.sum_eq_single (rev3 j)]
  · rw [Finset.sum_eq_single (rev3 i)]
    · simp [J3, rev3_invol]
    · intro m _ hm; simp [J3, hm]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro k _ hkj
    have hneq : j ≠ rev3 k := fun h => hkj (by rw [h, rev3_invol])
    simp [J3, hneq]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **3D `U(3)` Block Duality**: Any `rev3`-anti-involution on `GMA R 3` identifies
`A_{0,1} ≃ₗ[R] A_{1,2}` and `A_{1,0} ≃ₗ[R] A_{2,1}`. -/
def u3_block_duality (A : GMA R 3) (τ : GMAInvolution A rev3) :
    (A.Block 0 1 ≃ₗ[R] A.Block 1 2) × (A.Block 1 0 ≃ₗ[R] A.Block 2 1) :=
  (τ.τBlockEquiv 0 1, τ.τBlockEquiv 1 0)

/-- **3D `U(3)` Reducibility Ideal Collapse**: Under `U(3)` duality (`rev3`), the 6 off-diagonal
pair ideals of `GMA R 3` collapse to just **TWO** generators:
`I_red(A) = pairIdeal 0 1 ⊔ pairIdeal 0 2`! -/
theorem u3_reducibilityIdeal_eq_sup_two (A : GMA R 3) (τ : GMAInvolution A rev3) :
    A.reducibilityIdeal = A.pairIdeal 0 1 ⊔ A.pairIdeal 0 2 := by
  have h12 : A.pairIdeal 1 2 = A.pairIdeal 0 1 := τ.pairIdeal_τ_eq 0 1
  apply le_antisymm
  · rw [reducibilityIdeal]
    refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => ?_
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact le_sup_left
    · exact le_sup_right
    · rw [A.pairIdeal_symm]; exact le_sup_left
    · exact absurd rfl hij
    · exact le_trans (le_of_eq h12) le_sup_left
    · rw [A.pairIdeal_symm]; exact le_sup_right
    · rw [A.pairIdeal_symm]; exact le_trans (le_of_eq h12) le_sup_left
    · exact absurd rfl hij
  · exact sup_le (A.pairIdeal_le_reducibilityIdeal (by decide))
      (A.pairIdeal_le_reducibilityIdeal (by decide))

/-- **`U(3)` Reducible Eisenstein Trace Identity**: Modulo `I_red` (along `f : R →+* S`), if the
diagonal characters of `ρ : G →* A.Elem` are `(Ψ, 1, Ψ⁻¹)`, then
`f (tr(ρ g)) = Ψ g + 1 + (Ψ g)⁻¹`. -/
theorem u3_eisenstein_trace_mod_reducibility {S G : Type*} [CommRing S] [Group G]
    (A : GMA R 3) (ρ : G →* A.Elem) (f : R →+* S) (hf : A.reducibilityIdeal ≤ RingHom.ker f)
    (Ψ : G →* Sˣ)
    (h0 : ∀ g, A.diagCharOfFactor ρ f hf 0 g = (Ψ g : S))
    (h1 : ∀ g, A.diagCharOfFactor ρ f hf 1 g = 1)
    (h2 : ∀ g, A.diagCharOfFactor ρ f hf 2 g = ((Ψ g)⁻¹ : Sˣ))
    (g : G) :
    f (A.traceChar ρ g) = (Ψ g : S) + 1 + ((Ψ g)⁻¹ : Sˣ) := by
  rw [A.traceChar_splits_of_reducibilityIdeal ρ f hf g, Fin.sum_univ_three, h0 g, h1 g, h2 g]

/-! ### 3.2 Concrete 4D Symplectic `Sp₄` GMA (`CountII` / `CountIII`) -/

/-- Index reversal involution `σ₄ : 0 ↔ 3, 1 ↔ 2` on `Fin 4`. -/
def rev4 : Fin 4 ≃ Fin 4 where
  toFun := ![3, 2, 1, 0]
  invFun := ![3, 2, 1, 0]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

theorem rev4_invol (i : Fin 4) : rev4 (rev4 i) = i := rev4.left_inv i

/-- Symplectic sign vector `s₄ = ![1, 1, -1, -1]` for `J₄`. -/
def sympSign (R : Type*) [CommRing R] : Fin 4 → R := ![1, 1, -1, -1]

theorem sympSign_sq (R : Type*) [CommRing R] (i : Fin 4) :
    sympSign R i * sympSign R i = 1 := by
  fin_cases i <;> simp [sympSign]

theorem sympSign_rev4 (R : Type*) [CommRing R] (i : Fin 4) :
    sympSign R (rev4 i) = -sympSign R i := by
  fin_cases i <;> simp [sympSign, rev4]

/-- Standard 4×4 skew-symmetric symplectic form matrix `J₄` (`J₄ᵀ = -J₄`, `J₄² = -I`). -/
def J4 (R : Type*) [CommRing R] : Matrix (Fin 4) (Fin 4) R :=
  Matrix.of fun i j => if j = rev4 i then sympSign R i else 0

theorem J4_transpose (R : Type*) [CommRing R] : (J4 R)ᵀ = -J4 R := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.neg_apply, J4, Matrix.of_apply]
  by_cases h : j = rev4 i
  · subst h
    simp [rev4_invol, sympSign_rev4]
  · have h' : i ≠ rev4 j := fun heq => h (by rw [heq, rev4_invol])
    simp [h, h']

theorem J4_mul_J4 (R : Type*) [CommRing R] : J4 R * J4 R = -1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (rev4 i)]
  · simp only [J4, Matrix.of_apply, ↓reduceIte, Matrix.neg_apply, Matrix.one_apply, rev4_invol]
    by_cases hij : i = j
    · subst hij
      simp [sympSign_rev4, sympSign_sq]
    · have hji : j ≠ i := Ne.symm hij
      simp [hij, hji]
  · intro k _ hki
    simp [J4, hki]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Concrete 4D symplectic anti-involution `X ↦ -J₄ Xᵀ J₄` (`(i, j) ↦ s(i) s(j) X_{3-j, 3-i}`)
on `matrixGMA R 4`. -/
def sp4MatrixInvolution (R : Type*) [CommRing R] :
    GMAInvolution (matrixGMA R 4) rev4 where
  σ_invol := rev4_invol
  τElem :=
    { toFun := fun x =>
        ⟨fun a b => sympSign R a * sympSign R b * matEntry x (rev4 b) (rev4 a)⟩
      map_zero' := by ext a b; show sympSign R a * sympSign R b * (0 : R) = 0; simp
      map_add' := fun x y => by
        ext a b
        show sympSign R a * sympSign R b *
            (matEntry x (rev4 b) (rev4 a) + matEntry y (rev4 b) (rev4 a)) =
          sympSign R a * sympSign R b * matEntry x (rev4 b) (rev4 a) +
          sympSign R a * sympSign R b * matEntry y (rev4 b) (rev4 a)
        ring }
  τElem_invol x := by
    ext a b
    show sympSign R a * sympSign R b *
      (sympSign R (rev4 b) * sympSign R (rev4 a) * matEntry x (rev4 (rev4 a)) (rev4 (rev4 b))) =
      matEntry x a b
    rw [rev4_invol, rev4_invol, sympSign_rev4, sympSign_rev4]
    have h1 : sympSign R a * sympSign R a = 1 := sympSign_sq R a
    have h2 : sympSign R b * sympSign R b = 1 := sympSign_sq R b
    calc sympSign R a * sympSign R b * (-sympSign R b * -sympSign R a * matEntry x a b)
        = (sympSign R a * sympSign R a) * (sympSign R b * sympSign R b) * matEntry x a b := by ring
      _ = 1 * 1 * matEntry x a b := by rw [h1, h2]
      _ = matEntry x a b := by ring
  τElem_one := by
    ext a b
    by_cases hab : a = b
    · subst hab
      change sympSign R a * sympSign R a * matEntry (1 : (matrixGMA R 4).Elem) (rev4 a) (rev4 a) =
        matEntry (1 : (matrixGMA R 4).Elem) a a
      have h1 : matEntry (1 : (matrixGMA R 4).Elem) (rev4 a) (rev4 a) = 1 := by
        unfold matEntry; rw [one_entry_diag]; rfl
      have h2 : matEntry (1 : (matrixGMA R 4).Elem) a a = 1 := by
        unfold matEntry; rw [one_entry_diag]; rfl
      rw [sympSign_sq, h1, h2, mul_one]
    · have hne : rev4 b ≠ rev4 a := fun h => hab (rev4.injective h).symm
      change sympSign R a * sympSign R b * matEntry (1 : (matrixGMA R 4).Elem) (rev4 b) (rev4 a) =
        matEntry (1 : (matrixGMA R 4).Elem) a b
      have h1 : matEntry (1 : (matrixGMA R 4).Elem) (rev4 b) (rev4 a) = 0 := one_entry_off hne
      have h2 : matEntry (1 : (matrixGMA R 4).Elem) a b = 0 := one_entry_off hab
      rw [h1, h2, mul_zero]
  τElem_mul x y := by
    ext a b
    change sympSign R a * sympSign R b *
        (∑ k : Fin 4, matEntry x (rev4 b) k * matEntry y k (rev4 a)) =
      ∑ j : Fin 4, (sympSign R a * sympSign R j * matEntry y (rev4 j) (rev4 a)) *
        (sympSign R j * sympSign R b * matEntry x (rev4 b) (rev4 j))
    rw [← Equiv.sum_comp rev4, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hj := sympSign_sq R j
    calc sympSign R a * sympSign R b *
            (matEntry x (rev4 b) (rev4 j) * matEntry y (rev4 j) (rev4 a))
        = sympSign R a * sympSign R b * 1 *
            (matEntry x (rev4 b) (rev4 j) * matEntry y (rev4 j) (rev4 a)) := by ring
      _ = sympSign R a * sympSign R b * (sympSign R j * sympSign R j) *
            (matEntry x (rev4 b) (rev4 j) * matEntry y (rev4 j) (rev4 a)) := by rw [hj]
      _ = (sympSign R a * sympSign R j * matEntry y (rev4 j) (rev4 a)) *
            (sympSign R j * sympSign R b * matEntry x (rev4 b) (rev4 j)) := by ring
  τElem_smul r x := by
    ext a b
    show sympSign R a * sympSign R b * (r * matEntry x (rev4 b) (rev4 a)) =
      r * (sympSign R a * sympSign R b * matEntry x (rev4 b) (rev4 a))
    ring
  τElem_idemp i := by
    ext a b
    change sympSign R a * sympSign R b *
        matEntry (GMA.idemp (matrixGMA R 4) i) (rev4 b) (rev4 a) =
      matEntry (GMA.idemp (matrixGMA R 4) (rev4 i)) a b
    by_cases h : a = rev4 i ∧ b = rev4 i
    · rcases h with ⟨rfl, rfl⟩
      have h1 : matEntry (GMA.idemp (matrixGMA R 4) i) (rev4 (rev4 i)) (rev4 (rev4 i)) = 1 := by
        unfold matEntry; rw [rev4_invol, idemp, blockElem_entry_same]; rfl
      have h2 : matEntry (GMA.idemp (matrixGMA R 4) (rev4 i)) (rev4 i) (rev4 i) = 1 := by
        unfold matEntry; rw [idemp, blockElem_entry_same]; rfl
      rw [sympSign_sq, h1, h2, mul_one]
    · have hne : rev4 b ≠ i ∨ rev4 a ≠ i := by
        by_contra hc
        push Not at hc
        apply h
        exact ⟨by rw [← hc.2, rev4_invol], by rw [← hc.1, rev4_invol]⟩
      have h1 : matEntry (GMA.idemp (matrixGMA R 4) i) (rev4 b) (rev4 a) = 0 :=
        GMA.blockElem_entry_ne _ hne _
      have h2 : matEntry (GMA.idemp (matrixGMA R 4) (rev4 i)) a b = 0 :=
        GMA.blockElem_entry_ne _ (by tauto) _
      rw [h1, h2, mul_zero]
  τElem_diag i r := by
    change sympSign R (rev4 i) * sympSign R (rev4 i) *
      matEntry (GMA.blockElem (matrixGMA R 4) i i r) (rev4 (rev4 i)) (rev4 (rev4 i)) = r
    have h1 : matEntry (GMA.blockElem (matrixGMA R 4) i i r) (rev4 (rev4 i)) (rev4 (rev4 i)) = r := by
      unfold matEntry; rw [rev4_invol]; exact GMA.blockElem_entry_same (matrixGMA R 4) i i r
    rw [sympSign_sq, h1, one_mul]

theorem sp4MatrixInvolution_eq_J4_conj (R : Type*) [CommRing R] (x : (matrixGMA R 4).Elem) :
    matrixGMAElemEquiv R 4 ((sp4MatrixInvolution R).τElem x) =
      -(J4 R * (matrixGMAElemEquiv R 4 x)ᵀ * J4 R) := by
  ext i j
  change sympSign R i * sympSign R j * matEntry x (rev4 j) (rev4 i) =
    -(∑ k : Fin 4, (∑ m : Fin 4, (J4 R) i m * matEntry x k m) * (J4 R) k j)
  rw [Finset.sum_eq_single (rev4 j)]
  · rw [Finset.sum_eq_single (rev4 i)]
    · simp only [J4, Matrix.of_apply, ↓reduceIte, rev4_invol, sympSign_rev4]
      ring
    · intro m _ hm; simp [J4, hm]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro k _ hkj
    have hneq : j ≠ rev4 k := fun h => hkj (by rw [h, rev4_invol])
    simp [J4, hneq]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Explicit `Sp₄` Symplectic Anti-Diagonal Sign Constraints**:
`τ(X)_{0, 3} = -X_{0, 3}` and `τ(X)_{1, 2} = -X_{1, 2}` (anti-symmetric blocks), while
`τ(X)_{2, 3} = +X_{0, 1}` (symmetric pair)! -/
theorem sp4_antidiag_sign (R : Type*) [CommRing R] (x : (matrixGMA R 4).Elem) :
    matEntry ((sp4MatrixInvolution R).τElem x) 0 3 = -matEntry x 0 3 ∧
    matEntry ((sp4MatrixInvolution R).τElem x) 1 2 = -matEntry x 1 2 ∧
    matEntry ((sp4MatrixInvolution R).τElem x) 2 3 = matEntry x 0 1 ∧
    matEntry ((sp4MatrixInvolution R).τElem x) 1 3 = -matEntry x 0 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change sympSign R 0 * sympSign R 3 * matEntry x (rev4 3) (rev4 0) = -matEntry x 0 3
    simp [sympSign, rev4]
  · change sympSign R 1 * sympSign R 2 * matEntry x (rev4 2) (rev4 1) = -matEntry x 1 2
    simp [sympSign, rev4]
  · change sympSign R 2 * sympSign R 3 * matEntry x (rev4 3) (rev4 2) = matEntry x 0 1
    simp [sympSign, rev4]
  · change sympSign R 1 * sympSign R 3 * matEntry x (rev4 3) (rev4 1) = -matEntry x 0 2
    simp [sympSign, rev4]

/-- **4D `Sp₄` Block Dualities**: Any `rev4`-anti-involution on `GMA R 4` gives exact `R`-linear
isomorphisms `A_{0,1} ≃ A_{2,3}` and `A_{0,2} ≃ A_{1,3}`. -/
def sp4_block_duality (A : GMA R 4) (τ : GMAInvolution A rev4) :
    (A.Block 0 1 ≃ₗ[R] A.Block 2 3) × (A.Block 0 2 ≃ₗ[R] A.Block 1 3) :=
  (τ.τBlockEquiv 0 1, τ.τBlockEquiv 0 2)

/-- **4D `Sp₄` Reducibility Ideal Collapse**: Under `Sp₄` duality (`rev4`), the 12 off-diagonal
pair ideals of `GMA R 4` collapse to just **4** generators:
`I_red(A) = pairIdeal 0 1 ⊔ pairIdeal 0 2 ⊔ pairIdeal 0 3 ⊔ pairIdeal 1 2`! -/
theorem sp4_reducibilityIdeal_eq_sup_four (A : GMA R 4) (τ : GMAInvolution A rev4) :
    A.reducibilityIdeal =
      A.pairIdeal 0 1 ⊔ A.pairIdeal 0 2 ⊔ A.pairIdeal 0 3 ⊔ A.pairIdeal 1 2 := by
  have h23 : A.pairIdeal 2 3 = A.pairIdeal 0 1 := τ.pairIdeal_τ_eq 0 1
  have h13 : A.pairIdeal 1 3 = A.pairIdeal 0 2 := τ.pairIdeal_τ_eq 0 2
  apply le_antisymm
  · rw [reducibilityIdeal]
    refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => ?_
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact le_sup_of_le_left (le_sup_of_le_left le_sup_left)
    · exact le_sup_of_le_left (le_sup_of_le_left le_sup_right)
    · exact le_sup_of_le_left le_sup_right
    · rw [A.pairIdeal_symm]; exact le_sup_of_le_left (le_sup_of_le_left le_sup_left)
    · exact absurd rfl hij
    · exact le_sup_right
    · exact le_trans (le_of_eq h13) (le_sup_of_le_left (le_sup_of_le_left le_sup_right))
    · rw [A.pairIdeal_symm]; exact le_sup_of_le_left (le_sup_of_le_left le_sup_right)
    · rw [A.pairIdeal_symm]; exact le_sup_right
    · exact absurd rfl hij
    · exact le_trans (le_of_eq h23) (le_sup_of_le_left (le_sup_of_le_left le_sup_left))
    · rw [A.pairIdeal_symm]; exact le_sup_of_le_left le_sup_right
    · rw [A.pairIdeal_symm]
      exact le_trans (le_of_eq h13) (le_sup_of_le_left (le_sup_of_le_left le_sup_right))
    · rw [A.pairIdeal_symm]
      exact le_trans (le_of_eq h23) (le_sup_of_le_left (le_sup_of_le_left le_sup_left))
    · exact absurd rfl hij
  · exact sup_le (sup_le (sup_le (A.pairIdeal_le_reducibilityIdeal (by decide))
      (A.pairIdeal_le_reducibilityIdeal (by decide)))
      (A.pairIdeal_le_reducibilityIdeal (by decide)))
      (A.pairIdeal_le_reducibilityIdeal (by decide))

/-- **`Sp₄` Reducible Eisenstein Trace Identity**: Modulo `I_red` (along `f : R →+* S`), with
symplectic diagonal characters `(χ₀, χ₁, μ χ₁⁻¹, μ χ₀⁻¹)`,
`f (tr(ρ g)) = χ₀ g + χ₁ g + μ g * (χ₁ g)⁻¹ + μ g * (χ₀ g)⁻¹`. -/
theorem sp4_eisenstein_trace_mod_reducibility {S G : Type*} [CommRing S] [Group G]
    (A : GMA R 4) (ρ : G →* A.Elem) (f : R →+* S) (hf : A.reducibilityIdeal ≤ RingHom.ker f)
    (χ₀ χ₁ μ : G →* Sˣ)
    (h0 : ∀ g, A.diagCharOfFactor ρ f hf 0 g = (χ₀ g : S))
    (h1 : ∀ g, A.diagCharOfFactor ρ f hf 1 g = (χ₁ g : S))
    (h2 : ∀ g, A.diagCharOfFactor ρ f hf 2 g = ((μ g * (χ₁ g)⁻¹ : Sˣ) : S))
    (h3 : ∀ g, A.diagCharOfFactor ρ f hf 3 g = ((μ g * (χ₀ g)⁻¹ : Sˣ) : S))
    (g : G) :
    f (A.traceChar ρ g) =
      (χ₀ g : S) + (χ₁ g : S) + ((μ g * (χ₁ g)⁻¹ : Sˣ) : S) + ((μ g * (χ₀ g)⁻¹ : Sˣ) : S) := by
  rw [A.traceChar_splits_of_reducibilityIdeal ρ f hf g, Fin.sum_univ_four, h0 g, h1 g, h2 g, h3 g]

/-! ### 3.3 Exact Complex-Conjugation Parity Forcing (`IsUnit (2 : R)`) -/

/-- Exact odd-prime (`IsUnit (2 : R)`) eigenspace decomposition for any involution `φ : M →ₗ[R] M`
(`φ² = id`): every `x ∈ M` decomposes uniquely as `x = x⁺ + x⁻` with `φ x⁺ = x⁺` and `φ x⁻ = -x⁻`. -/
theorem involution_eigenspace_decomp {M : Type*} [AddCommGroup M] [Module R M]
    (h2 : IsUnit (2 : R)) (φ : M →ₗ[R] M) (hφ : ∀ x, φ (φ x) = x) (x : M) :
    ∃! p : { v : M // φ v = v } × { v : M // φ v = -v }, p.1.1 + p.2.1 = x := by
  obtain ⟨u, hu⟩ := h2
  have hu2 : (u⁻¹ : Rˣ).1 * 2 = 1 := by
    rw [← hu, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  let xp : M := (u⁻¹ : Rˣ).1 • (x + φ x)
  let xm : M := (u⁻¹ : Rˣ).1 • (x - φ x)
  have hxp : φ xp = xp := by
    simp only [xp, map_smul, map_add, hφ x, add_comm]
  have hxm : φ xm = -xm := by
    simp only [xm, map_smul, map_sub, hφ x, ← smul_neg, neg_sub]
  have hsum : xp + xm = x := by
    simp only [xp, xm, ← smul_add]
    have hadd : (x + φ x) + (x - φ x) = (2 : R) • x := by
      rw [two_smul]; abel
    rw [hadd, smul_smul, hu2, one_smul]
  refine ⟨(⟨xp, hxp⟩, ⟨xm, hxm⟩), hsum, ?_⟩
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ hab
  have hab' : a + b = x := hab
  have hφab : a - b = φ x := by
    rw [← hab', map_add, ha, hb, sub_eq_add_neg]
  have ha_eq : a = xp := by
    have h2a : (2 : R) • a = x + φ x := by
      calc (2 : R) • a = (a + b) + (a - b) := by rw [two_smul]; abel
        _ = x + φ x := by rw [hab', hφab]
    calc a = ((u⁻¹ : Rˣ).1 * 2) • a := by rw [hu2, one_smul]
      _ = (u⁻¹ : Rˣ).1 • ((2 : R) • a) := mul_smul _ _ _
      _ = xp := by rw [h2a]
  have hb_eq : b = xm := by
    have h2b : (2 : R) • b = x - φ x := by
      calc (2 : R) • b = (a + b) - (a - b) := by rw [two_smul]; abel
        _ = x - φ x := by rw [hab', hφab]
    calc b = ((u⁻¹ : Rˣ).1 * 2) • b := by rw [hu2, one_smul]
      _ = (u⁻¹ : Rˣ).1 • ((2 : R) • b) := mul_smul _ _ _
      _ = xm := by rw [h2b]
  exact Prod.ext (Subtype.ext ha_eq) (Subtype.ext hb_eq)

/-- **Diagonal Conjugation Parity Law**: If `c ∈ G` has diagonal GMA image
`ρ c = diag(ε_0, …, ε_{d-1})` with `ε_i ^ 2 = 1`, then conjugation by `c` scales the `(i, j)`
block by `ε_i * ε_j`: `(ρ (c * g * c)).entry i j = (ε i * ε j) • (ρ g).entry i j`! -/
theorem gma_conj_block_action {G : Type*} [Group G] {d : ℕ} (A : GMA R d) (ρ : G →* A.Elem)
    (c : G) (ε : Fin d → R)
    (hc_diag : ∀ i : Fin d, (ρ c).entry i i = (A.diagEquiv i).symm (ε i))
    (hc_off : ∀ i j : Fin d, i ≠ j → (ρ c).entry i j = 0)
    (g : G) (i j : Fin d) :
    (ρ (c * g * c)).entry i j = (ε i * ε j) • (ρ g).entry i j := by
  rw [map_mul, map_mul, mul_entry, Finset.sum_eq_single j]
  · rw [mul_entry, Finset.sum_eq_single i]
    · rw [hc_diag i, hc_diag j, A.mul_diag_left, A.mul_diag_right, smul_smul, mul_comm (ε j)]
    · intro k _ hki
      rw [hc_off i k hki.symm, map_zero, LinearMap.zero_apply]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  · intro k _ hkj
    rw [hc_off k j hkj, map_zero]
  · intro hj; exact absurd (Finset.mem_univ j) hj

/-- **Exact Parity Forcing on `gmaCocycle`**: Under diagonal complex conjugation `ρ c = diag(ε)`
(`ε_k ^ 2 = 1`), the `c`-conjugate of `c_λ = gmaCocycle lam` is scaled by `f (ε i * ε j)`! -/
theorem gma_ext_parity_forcing {S G M : Type*} [CommRing S] [Group G] [AddCommGroup M]
    [Module S M] {d : ℕ} (A : GMA R d) (ρ : G →* A.Elem) (f : R →+* S)
    (hf : A.reducibilityIdeal ≤ RingHom.ker f) {i j : Fin d} (hij : i ≠ j)
    (c : G) (ε : Fin d → R) (hε2 : ∀ k, ε k * ε k = 1)
    (hc_diag : ∀ k : Fin d, (ρ c).entry k k = (A.diagEquiv k).symm (ε k))
    (hc_off : ∀ a b : Fin d, a ≠ b → (ρ c).entry a b = 0)
    (lam : GMARedHom A f i j M) (g : G) :
    (gmaCocycle A ρ f hf hij lam).1 (c * g * c) =
      f (ε i * ε j) • (gmaCocycle A ρ f hf hij lam).1 g := by
  change (((A.diagUnitCharOfFactor ρ f hf j (c * g * c))⁻¹ : Sˣ) : S) •
      lam.toAddHom ((ρ (c * g * c)).entry i j) =
    f (ε i * ε j) •
      ((((A.diagUnitCharOfFactor ρ f hf j g)⁻¹ : Sˣ) : S) • lam.toAddHom ((ρ g).entry i j))
  have hχc : ∀ k, ((A.diagUnitCharOfFactor ρ f hf k c : Sˣ) : S) = f (ε k) := by
    intro k
    change f (A.diagEquiv k ((ρ c).entry k k)) = f (ε k)
    rw [hc_diag k, LinearEquiv.apply_symm_apply]
  have hχc_sq : ((A.diagUnitCharOfFactor ρ f hf j c : Sˣ) : S) *
      ((A.diagUnitCharOfFactor ρ f hf j c : Sˣ) : S) = 1 := by
    rw [hχc j, ← map_mul, hε2 j, map_one]
  have hχ_conj : A.diagUnitCharOfFactor ρ f hf j (c * g * c) =
      A.diagUnitCharOfFactor ρ f hf j g := by
    apply Units.ext
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul]
    calc ((A.diagUnitCharOfFactor ρ f hf j c : Sˣ) : S) *
          ((A.diagUnitCharOfFactor ρ f hf j g : Sˣ) : S) *
          ((A.diagUnitCharOfFactor ρ f hf j c : Sˣ) : S)
        = (((A.diagUnitCharOfFactor ρ f hf j c : Sˣ) : S) *
          ((A.diagUnitCharOfFactor ρ f hf j c : Sˣ) : S)) *
          ((A.diagUnitCharOfFactor ρ f hf j g : Sˣ) : S) := by ring
      _ = 1 * ((A.diagUnitCharOfFactor ρ f hf j g : Sˣ) : S) := by rw [hχc_sq]
      _ = ((A.diagUnitCharOfFactor ρ f hf j g : Sˣ) : S) := one_mul _
  rw [hχ_conj, gma_conj_block_action A ρ c ε hc_diag hc_off g i j, lam.map_smul', smul_comm]

/-- **`U(3)` Plus-Parity Block Forcing (`CountI`)**: For `ε = ![1, 1, 1]` (or any `ε` with
`ε 0 = ε 1 = ε 2` and `ε_k² = 1`), complex conjugation acts as `+1` on BOTH `A_{0,1}` and `A_{1,2}`
(forcing plus-parity Selmer classes into `A_{0,1} ≃ A_{1,2}`!). When `ε = ![-1, 1, -1]`,
`A_{0,1}` and `A_{1,2}` carry pure minus-parity (`-1`) while `A_{0,2}` carries pure plus-parity
(`+1`)! -/
theorem u3_plus_parity_forcing {S G M : Type*} [CommRing S] [Group G] [AddCommGroup M]
    [Module S M] (A : GMA R 3) (ρ : G →* A.Elem) (f : R →+* S)
    (hf : A.reducibilityIdeal ≤ RingHom.ker f)
    (c : G) (s : R) (hs : s * s = 1)
    (hc_diag : ∀ k : Fin 3, (ρ c).entry k k = (A.diagEquiv k).symm (![s, (1 : R), s] k))
    (hc_off : ∀ a b : Fin 3, a ≠ b → (ρ c).entry a b = 0) :
    (∀ (lam : GMARedHom A f 0 1 M) (g : G),
      (gmaCocycle A ρ f hf (by decide) lam).1 (c * g * c) =
        f s • (gmaCocycle A ρ f hf (by decide) lam).1 g) ∧
    (∀ (lam : GMARedHom A f 1 2 M) (g : G),
      (gmaCocycle A ρ f hf (by decide) lam).1 (c * g * c) =
        f s • (gmaCocycle A ρ f hf (by decide) lam).1 g) ∧
    (∀ (lam : GMARedHom A f 0 2 M) (g : G),
      (gmaCocycle A ρ f hf (by decide) lam).1 (c * g * c) =
        (gmaCocycle A ρ f hf (by decide) lam).1 g) := by
  have hε2 : ∀ k : Fin 3, (![s, (1 : R), s] k) * (![s, (1 : R), s] k) = 1 := by
    intro k; fin_cases k <;> simp [hs]
  refine ⟨fun lam g => ?_, fun lam g => ?_, fun lam g => ?_⟩
  · simpa using gma_ext_parity_forcing A ρ f hf (by decide : (0 : Fin 3) ≠ 1) c
      ![s, 1, s] hε2 hc_diag hc_off lam g
  · simpa using gma_ext_parity_forcing A ρ f hf (by decide : (1 : Fin 3) ≠ 2) c
      ![s, 1, s] hε2 hc_diag hc_off lam g
  · have h := gma_ext_parity_forcing A ρ f hf (by decide : (0 : Fin 3) ≠ 2) c
      ![s, 1, s] hε2 hc_diag hc_off lam g
    simpa [hs] using h

/-- **`Sp₄` Symplectic Plus-Parity Block Forcing (`CountII` / `CountIII`)**:
For an odd symplectic representation (`ρ c = diag(1, 1, -1, -1)`), complex conjugation acts as:
- **`+1` (plus-parity)** on `A_{0,1}` and `A_{2,3}` (forcing plus-parity Selmer classes here!),
- **`-1` (minus-parity)** on `A_{0,2}`, `A_{1,3}`, `A_{0,3}`, and `A_{1,2}` (so when `IsUnit (2 : S)`,
  every plus-parity class vanishes identically on these 4 blocks!). -/
theorem sp4_plus_parity_forcing {S G M : Type*} [CommRing S] [Group G] [AddCommGroup M]
    [Module S M] (A : GMA R 4) (ρ : G →* A.Elem) (f : R →+* S)
    (hf : A.reducibilityIdeal ≤ RingHom.ker f)
    (c : G)
    (hc_diag : ∀ k : Fin 4, (ρ c).entry k k = (A.diagEquiv k).symm (sympSign R k))
    (hc_off : ∀ a b : Fin 4, a ≠ b → (ρ c).entry a b = 0) :
    (∀ (lam : GMARedHom A f 0 1 M) (g : G),
      (gmaCocycle A ρ f hf (by decide) lam).1 (c * g * c) =
        (gmaCocycle A ρ f hf (by decide) lam).1 g) ∧
    (∀ (lam : GMARedHom A f 2 3 M) (g : G),
      (gmaCocycle A ρ f hf (by decide) lam).1 (c * g * c) =
        (gmaCocycle A ρ f hf (by decide) lam).1 g) ∧
    (∀ (lam : GMARedHom A f 0 2 M) (g : G),
      (gmaCocycle A ρ f hf (by decide) lam).1 (c * g * c) =
        -(gmaCocycle A ρ f hf (by decide) lam).1 g) ∧
    (∀ (lam : GMARedHom A f 1 2 M) (g : G),
      (gmaCocycle A ρ f hf (by decide) lam).1 (c * g * c) =
        -(gmaCocycle A ρ f hf (by decide) lam).1 g) ∧
    (∀ (lam : GMARedHom A f 0 3 M) (g : G),
      (gmaCocycle A ρ f hf (by decide) lam).1 (c * g * c) =
        -(gmaCocycle A ρ f hf (by decide) lam).1 g) := by
  have hε2 : ∀ k : Fin 4, sympSign R k * sympSign R k = 1 := by
    intro k; fin_cases k <;> simp [sympSign]
  refine ⟨fun lam g => ?_, fun lam g => ?_, fun lam g => ?_, fun lam g => ?_, fun lam g => ?_⟩
  · simpa [sympSign] using gma_ext_parity_forcing A ρ f hf (by decide : (0 : Fin 4) ≠ 1) c
      (sympSign R) hε2 hc_diag hc_off lam g
  · simpa [sympSign] using gma_ext_parity_forcing A ρ f hf (by decide : (2 : Fin 4) ≠ 3) c
      (sympSign R) hε2 hc_diag hc_off lam g
  · simpa [sympSign] using gma_ext_parity_forcing A ρ f hf (by decide : (0 : Fin 4) ≠ 2) c
      (sympSign R) hε2 hc_diag hc_off lam g
  · simpa [sympSign] using gma_ext_parity_forcing A ρ f hf (by decide : (1 : Fin 4) ≠ 2) c
      (sympSign R) hε2 hc_diag hc_off lam g
  · simpa [sympSign] using gma_ext_parity_forcing A ρ f hf (by decide : (0 : Fin 4) ≠ 3) c
      (sympSign R) hε2 hc_diag hc_off lam g

/-- Odd-prime vanishing on minus-parity blocks: if `IsUnit (2 : S)` and a cocycle `c_λ` on a
minus-parity block (`c_λ(cgc) = -c_λ(g)`) is plus-invariant (`c_λ(cgc) = c_λ(g)`), then `c_λ = 0`! -/
theorem odd_prime_plus_vanishes_on_minus_block {S M : Type*} [CommRing S] [AddCommGroup M]
    [Module S M] (h2 : IsUnit (2 : S)) {v : M} (hplus : v = -v) : v = 0 := by
  obtain ⟨u, hu⟩ := h2
  have h2v : (2 : S) • v = 0 := by
    rw [two_smul]
    calc v + v = v + (-v) := by conv_rhs => rw [← hplus]
      _ = 0 := add_neg_cancel v
  have h1 : (u⁻¹ : Sˣ).1 * (2 : S) = 1 := by
    rw [← hu, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc v = ((u⁻¹ : Sˣ).1 * 2) • v := by rw [h1, one_smul]
    _ = (u⁻¹ : Sˣ).1 • ((2 : S) • v) := mul_smul _ _ _
    _ = 0 := by rw [h2v, smul_zero]

end U3Sp4InvolutionGMA

/-! ## Section 4: Unconditional Single Global Resultant Integer Bound (`CorGSumLog` & `frobenius_trace_norm_nonzero_log_bound`) -/

section GlobalResultantBound

/-! ### 4.1 Exact Global Prime-Sum Theorem (`CorGSumLog`) & Two-Auxiliary-Prime Elimination -/

/-- **Global Prime-Valuation Sum Inequality (`corG_sum_log`)**:
For ANY nonzero integer `NN : ℤ` (`NN ≠ 0`) and ANY finite set of primes `Ls : Finset Nat.Primes`:
`∑_{l ∈ Ls} Real.log (l : ℕ) * (padicValInt l NN : ℝ) ≤ Real.log |(NN : ℝ)|`. -/
theorem corG_sum_log (NN : ℤ) (hNN : NN ≠ 0) (Ls : Finset Nat.Primes) :
    ∑ l ∈ Ls, Real.log (l : ℕ) * (padicValInt l NN : ℝ) ≤ Real.log |(NN : ℝ)| := by
  classical
  have hdvd : ∏ l ∈ Ls, ((l : ℕ) : ℤ) ^ (padicValInt l NN) ∣ NN := by
    apply Finset.prod_dvd_of_coprime
    · intro a _ b _ hab
      simp only [Function.onFun]
      apply IsCoprime.pow
      rw [Nat.isCoprime_iff_coprime]
      exact (Nat.coprime_primes a.2 b.2).mpr (fun h => hab (Subtype.ext h))
    · intro l _
      have : Fact (Nat.Prime (l : ℕ)) := ⟨l.2⟩
      exact padicValInt_dvd NN
  have hP : (∏ l ∈ Ls, ((l : ℕ) : ℝ) ^ (padicValInt l NN)) ≤ |(NN : ℝ)| := by
    have h1 : (∏ l ∈ Ls, ((l : ℕ) : ℤ) ^ (padicValInt l NN)) ≤ |NN| :=
      Int.le_of_dvd (abs_pos.mpr hNN) ((dvd_abs _ _).mpr hdvd)
    have h2 : ((∏ l ∈ Ls, ((l : ℕ) : ℤ) ^ (padicValInt l NN) : ℤ) : ℝ) ≤ ((|NN| : ℤ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h2
    exact h2
  have hpos : ∀ l ∈ Ls, (0 : ℝ) < ((l : ℕ) : ℝ) ^ (padicValInt l NN) :=
    fun l _ => pow_pos (by exact_mod_cast l.2.pos) _
  calc ∑ l ∈ Ls, Real.log (l : ℕ) * (padicValInt l NN : ℝ)
      = ∑ l ∈ Ls, Real.log (((l : ℕ) : ℝ) ^ (padicValInt l NN)) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Real.log_pow]
        ring
    _ = Real.log (∏ l ∈ Ls, ((l : ℕ) : ℝ) ^ (padicValInt l NN)) :=
        (Real.log_prod (fun l hl => (hpos l hl).ne')).symm
    _ ≤ Real.log |(NN : ℝ)| := Real.log_le_log (Finset.prod_pos hpos) hP

/-- **Single-Integer Global Selmer Sum Bound**:
If a single nonzero integer `NN : ℤ` (`NN ≠ 0`) valuation-bounds the plus-parity Selmer length sum
`∑_{k=1}^{t-1} len l k ≤ C_mult * padicValInt l NN` for every prime `l ∈ Ls`, then
`∑_{l ∈ Ls} Real.log l * ∑_{k=1}^{t-1} len l k ≤ C_mult * Real.log |NN|`! -/
theorem global_selmer_sum_log_le_log_abs_int (Ls : Finset Nat.Primes) (t : ℕ)
    (len : Nat.Primes → ℕ → ℕ) (NN : ℤ) (hNN : NN ≠ 0) (C_mult : ℝ) (hC : 0 ≤ C_mult)
    (hbound : ∀ l ∈ Ls, (∑ k ∈ Finset.Ico 1 t, (len l k : ℝ)) ≤
      C_mult * (padicValInt l NN : ℝ)) :
    ∑ l ∈ Ls, Real.log (l : ℕ) * (∑ k ∈ Finset.Ico 1 t, (len l k : ℝ)) ≤
      C_mult * Real.log |(NN : ℝ)| := by
  calc ∑ l ∈ Ls, Real.log (l : ℕ) * (∑ k ∈ Finset.Ico 1 t, (len l k : ℝ))
      ≤ ∑ l ∈ Ls, Real.log (l : ℕ) * (C_mult * (padicValInt l NN : ℝ)) :=
        Finset.sum_le_sum fun l hl =>
          mul_le_mul_of_nonneg_left (hbound l hl) (Real.log_natCast_nonneg (l : ℕ))
    _ = C_mult * ∑ l ∈ Ls, Real.log (l : ℕ) * (padicValInt l NN : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => by ring
    _ ≤ C_mult * Real.log |(NN : ℝ)| :=
        mul_le_mul_of_nonneg_left (corG_sum_log NN hNN Ls) hC

/-- **Two-Auxiliary-Prime Elimination (`corG_two_primes_sum_log`, exact Alpöge `CorGSumLog.corGK`)**:
Given two distinct auxiliary primes `r₁ ≠ r₂`, if `NN₁ ≠ 0` controls all `l ∈ Ls` with `l ≠ r₁`
and `NN₂ ≠ 0` controls all `l ∈ Ls` with `l ≠ r₂`, then for ALL primes `l ∈ Ls` simultaneously:
`∑_{l ∈ Ls} Real.log l * ∑_{k=1}^{t-1} len l k ≤ C_mult * (Real.log |NN₁| + Real.log |NN₂|)`! -/
theorem corG_two_primes_sum_log (Ls : Finset Nat.Primes) (t : ℕ)
    (len : Nat.Primes → ℕ → ℕ) (r₁ r₂ : ℕ) (hr : r₁ ≠ r₂)
    (NN₁ NN₂ : ℤ) (hNN₁ : NN₁ ≠ 0) (hNN₂ : NN₂ ≠ 0) (C_mult : ℝ) (hC : 0 ≤ C_mult)
    (hb₁ : ∀ l ∈ Ls, (l : ℕ) ≠ r₁ →
      (∑ k ∈ Finset.Ico 1 t, (len l k : ℝ)) ≤ C_mult * (padicValInt l NN₁ : ℝ))
    (hb₂ : ∀ l ∈ Ls, (l : ℕ) ≠ r₂ →
      (∑ k ∈ Finset.Ico 1 t, (len l k : ℝ)) ≤ C_mult * (padicValInt l NN₂ : ℝ)) :
    ∑ l ∈ Ls, Real.log (l : ℕ) * (∑ k ∈ Finset.Ico 1 t, (len l k : ℝ)) ≤
      C_mult * (Real.log |(NN₁ : ℝ)| + Real.log |(NN₂ : ℝ)|) := by
  have hcomb : ∀ l ∈ Ls, (∑ k ∈ Finset.Ico 1 t, (len l k : ℝ)) ≤
      C_mult * (padicValInt l NN₁ : ℝ) + C_mult * (padicValInt l NN₂ : ℝ) := by
    intro l hl
    have h1 : 0 ≤ C_mult * (padicValInt l NN₁ : ℝ) := mul_nonneg hC (Nat.cast_nonneg _)
    have h2 : 0 ≤ C_mult * (padicValInt l NN₂ : ℝ) := mul_nonneg hC (Nat.cast_nonneg _)
    by_cases hlr : (l : ℕ) = r₁
    · have hlr2 : (l : ℕ) ≠ r₂ := fun h => hr (hlr.symm.trans h)
      linarith [hb₂ l hl hlr2]
    · linarith [hb₁ l hl hlr]
  calc ∑ l ∈ Ls, Real.log (l : ℕ) * (∑ k ∈ Finset.Ico 1 t, (len l k : ℝ))
      ≤ ∑ l ∈ Ls, Real.log (l : ℕ) *
          (C_mult * (padicValInt l NN₁ : ℝ) + C_mult * (padicValInt l NN₂ : ℝ)) :=
        Finset.sum_le_sum fun l hl =>
          mul_le_mul_of_nonneg_left (hcomb l hl) (Real.log_natCast_nonneg (l : ℕ))
    _ = C_mult * (∑ l ∈ Ls, Real.log (l : ℕ) * (padicValInt l NN₁ : ℝ)) +
        C_mult * (∑ l ∈ Ls, Real.log (l : ℕ) * (padicValInt l NN₂ : ℝ)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun l _ => by ring
    _ ≤ C_mult * Real.log |(NN₁ : ℝ)| + C_mult * Real.log |(NN₂ : ℝ)| :=
        add_le_add (mul_le_mul_of_nonneg_left (corG_sum_log NN₁ hNN₁ Ls) hC)
          (mul_le_mul_of_nonneg_left (corG_sum_log NN₂ hNN₂ Ls) hC)
    _ = C_mult * (Real.log |(NN₁ : ℝ)| + Real.log |(NN₂ : ℝ)|) := by ring

/-! ### 4.2 Archimedean Eisenstein Separation (`U(3)` & `Sp₄`) -/

/-- The 3D `U(3)` Eisenstein Frobenius trace `eis3(q, e, z) := q^e z + 1 + (q^e z)⁻¹`. -/
def eis3 (q e : ℕ) (z : ℂ) : ℂ :=
  (q : ℂ) ^ e * z + 1 + ((q : ℂ) ^ e * z)⁻¹

/-- The 4D `Sp₄` Eisenstein Frobenius trace `eis4(q, e, z₁, z₂) := q^e z₁ + z₂ + z₂⁻¹ + (q^e z₁)⁻¹`. -/
def eis4 (q e : ℕ) (z₁ z₂ : ℂ) : ℂ :=
  (q : ℂ) ^ e * z₁ + z₂ + z₂⁻¹ + ((q : ℂ) ^ e * z₁)⁻¹

/-- **Archimedean Eisenstein Separation (`U(3)`, `CountI`)**:
For `q ≥ 7`, `e ≥ 1`, any root of unity `z : ℂ` (`‖z‖ = 1`), and any Ramanujan-bounded Frobenius
trace `t : ℂ` (`‖t‖ ≤ √q + 2`):
1. `t ≠ eis3 q e z` (strict archimedean nonvanishing), and
2. `Real.log ‖(q : ℂ) ^ e * (t - eis3 q e z)‖ ≤ 2 * e * Real.log q + 1`. -/
theorem eisenstein_trace_archimedean_separation (q e : ℕ) (hq : 7 ≤ q) (he : 1 ≤ e)
    (z t : ℂ) (hz : ‖z‖ = 1) (ht : ‖t‖ ≤ Real.sqrt (q : ℝ) + 2) :
    t ≠ eis3 q e z ∧
    Real.log ‖(q : ℂ) ^ e * (t - eis3 q e z)‖ ≤ 2 * (e : ℝ) * Real.log (q : ℝ) + 1 := by
  have hqR : (7 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hqe_ge : (q : ℝ) ≤ (q : ℝ) ^ e := by
    calc (q : ℝ) = (q : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (q : ℝ) ^ e := pow_le_pow_right₀ (by linarith) he
  have hqe_pos : (0 : ℝ) < (q : ℝ) ^ e := pow_pos hqpos e
  have hsqrt_le : Real.sqrt (q : ℝ) ≤ (q : ℝ) / 2 := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hnorm_qz : ‖(q : ℂ) ^ e * z‖ = (q : ℝ) ^ e := by
    rw [norm_mul, norm_pow, Complex.norm_natCast, hz, mul_one]
  have hnorm_inv : ‖((q : ℂ) ^ e * z)⁻¹‖ = ((q : ℝ) ^ e)⁻¹ := by
    rw [norm_inv, hnorm_qz]
  have hinv_le : ((q : ℝ) ^ e)⁻¹ ≤ 1 / 7 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hne : t ≠ eis3 q e z := by
    intro heq
    have htri : ‖(q : ℂ) ^ e * z‖ ≤ ‖eis3 q e z‖ + ‖(1 : ℂ) + ((q : ℂ) ^ e * z)⁻¹‖ := by
      have hdecomp : (q : ℂ) ^ e * z = eis3 q e z - ((1 : ℂ) + ((q : ℂ) ^ e * z)⁻¹) := by
        unfold eis3; ring
      conv_lhs => rw [hdecomp]
      exact norm_sub_le (eis3 q e z) ((1 : ℂ) + ((q : ℂ) ^ e * z)⁻¹)
    have h12 : ‖(1 : ℂ) + ((q : ℂ) ^ e * z)⁻¹‖ ≤ 1 + ((q : ℝ) ^ e)⁻¹ := by
      calc ‖(1 : ℂ) + ((q : ℂ) ^ e * z)⁻¹‖
          ≤ ‖(1 : ℂ)‖ + ‖((q : ℂ) ^ e * z)⁻¹‖ := norm_add_le _ _
        _ = 1 + ((q : ℝ) ^ e)⁻¹ := by rw [norm_one, hnorm_inv]
    rw [hnorm_qz, ← heq] at htri
    nlinarith
  refine ⟨hne, ?_⟩
  have hnorm_eis : ‖eis3 q e z‖ ≤ (q : ℝ) ^ e + 1 + ((q : ℝ) ^ e)⁻¹ := by
    unfold eis3
    have h1 : ‖(q : ℂ) ^ e * z + 1 + ((q : ℂ) ^ e * z)⁻¹‖ ≤
        ‖(q : ℂ) ^ e * z + 1‖ + ‖((q : ℂ) ^ e * z)⁻¹‖ := norm_add_le _ _
    have h2 : ‖(q : ℂ) ^ e * z + 1‖ ≤ ‖(q : ℂ) ^ e * z‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    rw [hnorm_inv] at h1
    rw [hnorm_qz, norm_one] at h2
    linarith
  have hnorm_prod : ‖(q : ℂ) ^ e * (t - eis3 q e z)‖ ≤ Real.exp 1 * ((q : ℝ) ^ e) ^ 2 := by
    have hdiff : ‖t - eis3 q e z‖ ≤ (q : ℝ) ^ e + Real.sqrt (q : ℝ) + 3 + ((q : ℝ) ^ e)⁻¹ := by
      calc ‖t - eis3 q e z‖ ≤ ‖t‖ + ‖eis3 q e z‖ := norm_sub_le _ _
        _ ≤ (Real.sqrt (q : ℝ) + 2) + ((q : ℝ) ^ e + 1 + ((q : ℝ) ^ e)⁻¹) :=
            add_le_add ht hnorm_eis
        _ = (q : ℝ) ^ e + Real.sqrt (q : ℝ) + 3 + ((q : ℝ) ^ e)⁻¹ := by ring
    have hexp1 : (2 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (1 : ℝ)
      linarith
    have hmul_le : (q : ℝ) ^ e * ((q : ℝ) ^ e + Real.sqrt (q : ℝ) + 3 + ((q : ℝ) ^ e)⁻¹) ≤
        2 * ((q : ℝ) ^ e) ^ 2 := by
      have hinv_mul : (q : ℝ) ^ e * ((q : ℝ) ^ e)⁻¹ = 1 := mul_inv_cancel₀ hqe_pos.ne'
      have hlin : (q : ℝ) ^ e * (Real.sqrt (q : ℝ) + 3) + 1 ≤ ((q : ℝ) ^ e) ^ 2 := by
        have hstep : Real.sqrt (q : ℝ) + 3 ≤ (13 / 14 : ℝ) * (q : ℝ) ^ e := by nlinarith
        have h1 : (q : ℝ) ^ e * (Real.sqrt (q : ℝ) + 3) ≤ (13 / 14 : ℝ) * ((q : ℝ) ^ e) ^ 2 := by
          nlinarith
        have h2 : (1 : ℝ) ≤ (1 / 14 : ℝ) * ((q : ℝ) ^ e) ^ 2 := by nlinarith
        linarith
      nlinarith
    calc ‖(q : ℂ) ^ e * (t - eis3 q e z)‖
        = (q : ℝ) ^ e * ‖t - eis3 q e z‖ := by rw [norm_mul, norm_pow, Complex.norm_natCast]
      _ ≤ (q : ℝ) ^ e * ((q : ℝ) ^ e + Real.sqrt (q : ℝ) + 3 + ((q : ℝ) ^ e)⁻¹) :=
          mul_le_mul_of_nonneg_left hdiff hqe_pos.le
      _ ≤ 2 * ((q : ℝ) ^ e) ^ 2 := hmul_le
      _ ≤ Real.exp 1 * ((q : ℝ) ^ e) ^ 2 :=
          mul_le_mul_of_nonneg_right hexp1 (sq_nonneg _)
  have hpos_prod : 0 < ‖(q : ℂ) ^ e * (t - eis3 q e z)‖ := by
    rw [norm_pos_iff]
    exact mul_ne_zero (pow_ne_zero e (by exact_mod_cast (show q ≠ 0 by omega))) (sub_ne_zero.mpr hne)
  calc Real.log ‖(q : ℂ) ^ e * (t - eis3 q e z)‖
      ≤ Real.log (Real.exp 1 * ((q : ℝ) ^ e) ^ 2) := Real.log_le_log hpos_prod hnorm_prod
    _ = Real.log (Real.exp 1) + Real.log (((q : ℝ) ^ e) ^ 2) :=
        Real.log_mul (Real.exp_pos 1).ne' (pow_pos hqe_pos 2).ne'
    _ = 1 + 2 * ((e : ℝ) * Real.log (q : ℝ)) := by
        rw [Real.log_exp, Real.log_pow, Real.log_pow]; ring
    _ = 2 * (e : ℝ) * Real.log (q : ℝ) + 1 := by ring

/-- **Archimedean Eisenstein Separation (`Sp₄`, `CountII` / `CountIII`)**:
For `q ≥ 11`, `e ≥ 1`, roots of unity `z₁, z₂ : ℂ` (`‖z₁‖ = ‖z₂‖ = 1`), and any Ramanujan-bounded
`Sp₄` Frobenius trace `t : ℂ` (`‖t‖ ≤ 2 * √q + 2`):
`t ≠ eis4 q e z₁ z₂` and `Real.log ‖(q : ℂ) ^ e * (t - eis4 q e z₁ z₂)‖ ≤ 2 * e * Real.log q + 1`. -/
theorem sp4_eisenstein_trace_archimedean_separation (q e : ℕ) (hq : 11 ≤ q) (he : 1 ≤ e)
    (z₁ z₂ t : ℂ) (hz₁ : ‖z₁‖ = 1) (hz₂ : ‖z₂‖ = 1) (ht : ‖t‖ ≤ 2 * Real.sqrt (q : ℝ) + 2) :
    t ≠ eis4 q e z₁ z₂ ∧
    Real.log ‖(q : ℂ) ^ e * (t - eis4 q e z₁ z₂)‖ ≤ 2 * (e : ℝ) * Real.log (q : ℝ) + 1 := by
  have hqR : (11 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hqe_ge : (q : ℝ) ≤ (q : ℝ) ^ e := by
    calc (q : ℝ) = (q : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (q : ℝ) ^ e := pow_le_pow_right₀ (by linarith) he
  have hqe_pos : (0 : ℝ) < (q : ℝ) ^ e := pow_pos hqpos e
  have hsqrt_le : 2 * Real.sqrt (q : ℝ) ≤ (61 / 100 : ℝ) * (q : ℝ) := by
    have hsq : Real.sqrt (q : ℝ) ≤ (61 / 200 : ℝ) * (q : ℝ) := by
      rw [Real.sqrt_le_left (by linarith)]
      nlinarith
    linarith
  have hnorm_qz : ‖(q : ℂ) ^ e * z₁‖ = (q : ℝ) ^ e := by
    rw [norm_mul, norm_pow, Complex.norm_natCast, hz₁, mul_one]
  have hnorm_inv : ‖((q : ℂ) ^ e * z₁)⁻¹‖ = ((q : ℝ) ^ e)⁻¹ := by
    rw [norm_inv, hnorm_qz]
  have hinv_le : ((q : ℝ) ^ e)⁻¹ ≤ 1 / 11 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hz₂_inv : ‖z₂⁻¹‖ = 1 := by rw [norm_inv, hz₂, inv_one]
  have hne : t ≠ eis4 q e z₁ z₂ := by
    intro heq
    have htri : ‖(q : ℂ) ^ e * z₁‖ ≤ ‖eis4 q e z₁ z₂‖ + ‖z₂ + z₂⁻¹ + ((q : ℂ) ^ e * z₁)⁻¹‖ := by
      have hdecomp : (q : ℂ) ^ e * z₁ = eis4 q e z₁ z₂ - (z₂ + z₂⁻¹ + ((q : ℂ) ^ e * z₁)⁻¹) := by
        unfold eis4; ring
      conv_lhs => rw [hdecomp]
      exact norm_sub_le (eis4 q e z₁ z₂) (z₂ + z₂⁻¹ + ((q : ℂ) ^ e * z₁)⁻¹)
    have hrem : ‖z₂ + z₂⁻¹ + ((q : ℂ) ^ e * z₁)⁻¹‖ ≤ 2 + ((q : ℝ) ^ e)⁻¹ := by
      have h1 : ‖z₂ + z₂⁻¹ + ((q : ℂ) ^ e * z₁)⁻¹‖ ≤ ‖z₂ + z₂⁻¹‖ + ‖((q : ℂ) ^ e * z₁)⁻¹‖ :=
        norm_add_le _ _
      have h2 : ‖z₂ + z₂⁻¹‖ ≤ ‖z₂‖ + ‖z₂⁻¹‖ := norm_add_le _ _
      rw [hnorm_inv] at h1
      rw [hz₂, hz₂_inv] at h2
      linarith
    rw [hnorm_qz, ← heq] at htri
    nlinarith
  refine ⟨hne, ?_⟩
  have hnorm_eis : ‖eis4 q e z₁ z₂‖ ≤ (q : ℝ) ^ e + 2 + ((q : ℝ) ^ e)⁻¹ := by
    unfold eis4
    have h1 : ‖(q : ℂ) ^ e * z₁ + z₂ + z₂⁻¹ + ((q : ℂ) ^ e * z₁)⁻¹‖ ≤
        ‖(q : ℂ) ^ e * z₁ + z₂ + z₂⁻¹‖ + ‖((q : ℂ) ^ e * z₁)⁻¹‖ := norm_add_le _ _
    have h2 : ‖(q : ℂ) ^ e * z₁ + z₂ + z₂⁻¹‖ ≤ ‖(q : ℂ) ^ e * z₁ + z₂‖ + ‖z₂⁻¹‖ :=
      norm_add_le _ _
    have h3 : ‖(q : ℂ) ^ e * z₁ + z₂‖ ≤ ‖(q : ℂ) ^ e * z₁‖ + ‖z₂‖ := norm_add_le _ _
    rw [hnorm_inv] at h1
    rw [hz₂_inv] at h2
    rw [hnorm_qz, hz₂] at h3
    linarith
  have hnorm_prod : ‖(q : ℂ) ^ e * (t - eis4 q e z₁ z₂)‖ ≤ Real.exp 1 * ((q : ℝ) ^ e) ^ 2 := by
    have hdiff : ‖t - eis4 q e z₁ z₂‖ ≤ (q : ℝ) ^ e + 2 * Real.sqrt (q : ℝ) + 4 + ((q : ℝ) ^ e)⁻¹ := by
      calc ‖t - eis4 q e z₁ z₂‖ ≤ ‖t‖ + ‖eis4 q e z₁ z₂‖ := norm_sub_le _ _
        _ ≤ (2 * Real.sqrt (q : ℝ) + 2) + ((q : ℝ) ^ e + 2 + ((q : ℝ) ^ e)⁻¹) :=
            add_le_add ht hnorm_eis
        _ = (q : ℝ) ^ e + 2 * Real.sqrt (q : ℝ) + 4 + ((q : ℝ) ^ e)⁻¹ := by ring
    have hexp1 : (2.1 : ℝ) ≤ Real.exp 1 := by
      have h := Real.sum_le_exp_of_nonneg (x := (1 : ℝ)) zero_le_one 3
      simp [Finset.sum_range_succ, Nat.factorial] at h
      linarith
    have hmul_le : (q : ℝ) ^ e * ((q : ℝ) ^ e + 2 * Real.sqrt (q : ℝ) + 4 + ((q : ℝ) ^ e)⁻¹) ≤
        2.1 * ((q : ℝ) ^ e) ^ 2 := by
      have hinv_mul : (q : ℝ) ^ e * ((q : ℝ) ^ e)⁻¹ = 1 := mul_inv_cancel₀ hqe_pos.ne'
      have hstep : 2 * Real.sqrt (q : ℝ) + 4 ≤ (11 / 11 : ℝ) * (q : ℝ) ^ e := by nlinarith
      have h1 : (q : ℝ) ^ e * (2 * Real.sqrt (q : ℝ) + 4) ≤ ((q : ℝ) ^ e) ^ 2 := by nlinarith
      have h2 : (1 : ℝ) ≤ (0.1 : ℝ) * ((q : ℝ) ^ e) ^ 2 := by nlinarith
      nlinarith
    calc ‖(q : ℂ) ^ e * (t - eis4 q e z₁ z₂)‖
        = (q : ℝ) ^ e * ‖t - eis4 q e z₁ z₂‖ := by rw [norm_mul, norm_pow, Complex.norm_natCast]
      _ ≤ (q : ℝ) ^ e * ((q : ℝ) ^ e + 2 * Real.sqrt (q : ℝ) + 4 + ((q : ℝ) ^ e)⁻¹) :=
          mul_le_mul_of_nonneg_left hdiff hqe_pos.le
      _ ≤ 2.1 * ((q : ℝ) ^ e) ^ 2 := hmul_le
      _ ≤ Real.exp 1 * ((q : ℝ) ^ e) ^ 2 :=
          mul_le_mul_of_nonneg_right hexp1 (sq_nonneg _)
  have hpos_prod : 0 < ‖(q : ℂ) ^ e * (t - eis4 q e z₁ z₂)‖ := by
    rw [norm_pos_iff]
    exact mul_ne_zero (pow_ne_zero e (by exact_mod_cast (show q ≠ 0 by omega))) (sub_ne_zero.mpr hne)
  calc Real.log ‖(q : ℂ) ^ e * (t - eis4 q e z₁ z₂)‖
      ≤ Real.log (Real.exp 1 * ((q : ℝ) ^ e) ^ 2) := Real.log_le_log hpos_prod hnorm_prod
    _ = Real.log (Real.exp 1) + Real.log (((q : ℝ) ^ e) ^ 2) :=
        Real.log_mul (Real.exp_pos 1).ne' (pow_pos hqe_pos 2).ne'
    _ = 1 + 2 * ((e : ℝ) * Real.log (q : ℝ)) := by
        rw [Real.log_exp, Real.log_pow, Real.log_pow]; ring
    _ = 2 * (e : ℝ) * Real.log (q : ℝ) + 1 := by ring

/-! ### 4.3 Constructive Integral Characteristic-Polynomial Resultant `NN : ℤ` (`det(aeval T Q)`) -/

/-- Exact evaluation of `Matrix.charpoly M` at `β`: `(charpoly M).eval β = det(β • 1 - M)`. -/
theorem eval_charpoly_eq_det_sub {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (β : R) :
    (Matrix.charpoly M).eval β = Matrix.det (β • (1 : Matrix (Fin n) (Fin n) R) - M) := by
  rw [Matrix.charpoly, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.charmatrix_apply,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply, smul_eq_mul,
    Polynomial.coe_evalRingHom]
  split_ifs <;> simp

/-- `det(M - β • 1) = (-1)^n * (charpoly M).eval β`. -/
theorem det_sub_smul_one_eq_neg_one_pow_mul_eval_charpoly {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (β : R) :
    Matrix.det (M - β • (1 : Matrix (Fin n) (Fin n) R)) =
      (-1 : R) ^ n * (Matrix.charpoly M).eval β := by
  rw [eval_charpoly_eq_det_sub]
  have hneg : M - β • (1 : Matrix (Fin n) (Fin n) R) = (-1 : R) • (β • 1 - M) := by
    ext i j; simp
  rw [hneg, Matrix.det_smul, Fintype.card_fin]

/-- Over ANY commutative ring `R`, `det(aeval M (∏_{β ∈ s} (X - C β))) = ∏_{β ∈ s} det(M - β • 1)`. -/
theorem det_aeval_prod_X_sub_C {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (s : Multiset R) :
    Matrix.det (Polynomial.aeval M (s.map (fun β => Polynomial.X - Polynomial.C β)).prod) =
      (s.map (fun β => Matrix.det (M - β • (1 : Matrix (Fin n) (Fin n) R)))).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons,
      map_mul, Matrix.det_mul, ih]
    congr 1
    simp [Algebra.algebraMap_eq_smul_one]

/-- Helper: `aeval` commutes with base-change `f.mapMatrix` for any ring hom `f : R →+* S`. -/
theorem map_aeval_matrix {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (f : R →+* S) (T : Matrix (Fin n) (Fin n) R) (Q : R[X]) :
    f.mapMatrix (Polynomial.aeval T Q) = Polynomial.aeval (T.map f) (Q.map f) := by
  induction Q using Polynomial.induction_on' with
  | add p q ihp ihq =>
    rw [map_add, Polynomial.map_add, map_add, map_add, ihp, ihq]
  | monomial k a =>
    rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial,
      map_mul, map_pow]
    congr 1
    ext i j
    simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply]
    split_ifs <;> simp

/-- **Constructive Global Resultant Integer `NN : ℤ`** from a finite-rank integral Frobenius
operator `T : Matrix (Fin n) (Fin n) ℤ` and an integral Eisenstein polynomial `Q : ℤ[X]`:
`resultantInt T Q := Matrix.det (Polynomial.aeval T Q) ∈ ℤ`. -/
def resultantInt {n : ℕ} (T : Matrix (Fin n) (Fin n) ℤ) (Q : ℤ[X]) : ℤ :=
  Matrix.det (Polynomial.aeval T Q)

/-- Exact complex root-product formula for `resultantInt T Q`:
`(resultantInt T Q : ℂ) = ∏_{β ∈ roots(Q_ℂ)} ∏_{α ∈ roots(charpoly T_ℂ)} (α - β)`. -/
theorem resultantInt_cast_eq_prod_roots {n : ℕ} (T : Matrix (Fin n) (Fin n) ℤ)
    (Q : ℤ[X]) (hQ : Q.Monic) :
    ((resultantInt T Q : ℤ) : ℂ) =
      ((Q.map (Int.castRingHom ℂ)).roots.map fun β =>
        (((T.map (Int.castRingHom ℂ)).charpoly).roots.map fun α => α - β).prod).prod := by
  let f : ℤ →+* ℂ := Int.castRingHom ℂ
  let Tℂ : Matrix (Fin n) (Fin n) ℂ := T.map f
  let Qℂ : ℂ[X] := Q.map f
  have hQℂ_monic : Qℂ.Monic := hQ.map f
  have hQℂ_splits : Qℂ.Splits := IsAlgClosed.splits Qℂ
  have hQℂ_eq : Qℂ = (Qℂ.roots.map fun β => Polynomial.X - Polynomial.C β).prod :=
    hQℂ_splits.eq_prod_roots_of_monic hQℂ_monic
  have hcast : ((resultantInt T Q : ℤ) : ℂ) = Matrix.det (Polynomial.aeval Tℂ Qℂ) := by
    unfold resultantInt
    change f (Matrix.det (Polynomial.aeval T Q)) = _
    rw [RingHom.map_det, map_aeval_matrix]
  rw [hcast, hQℂ_eq, det_aeval_prod_X_sub_C]
  congr 1
  refine Multiset.map_congr rfl fun β _ => ?_
  rw [det_sub_smul_one_eq_neg_one_pow_mul_eval_charpoly]
  have hP_monic : Tℂ.charpoly.Monic := Matrix.charpoly_monic Tℂ
  have hP_splits : Tℂ.charpoly.Splits := IsAlgClosed.splits Tℂ.charpoly
  have hP_eq : Tℂ.charpoly = (Tℂ.charpoly.roots.map fun α => Polynomial.X - Polynomial.C α).prod :=
    hP_splits.eq_prod_roots_of_monic hP_monic
  have hcard : Tℂ.charpoly.roots.card = n := by
    have h1 : Tℂ.charpoly.natDegree = Tℂ.charpoly.roots.card := hP_splits.natDegree_eq_card_roots
    have h2 : Tℂ.charpoly.natDegree = n := by
      simp [Matrix.charpoly_natDegree_eq_dim]
    omega
  have heval : Tℂ.charpoly.eval β = (Tℂ.charpoly.roots.map fun α => β - α).prod := by
    conv_lhs => rw [hP_eq]
    rw [Polynomial.eval_multiset_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun α _ => ?_)
    simp
  rw [heval]
  have hneg_prod : ∀ s : Multiset ℂ,
      (-1 : ℂ) ^ s.card * (s.map fun α => β - α).prod = (s.map fun α => α - β).prod := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      rw [Multiset.card_cons, pow_succ, Multiset.map_cons, Multiset.prod_cons,
        Multiset.map_cons, Multiset.prod_cons, ← ih]
      ring
  have hres := hneg_prod Tℂ.charpoly.roots
  rw [hcard] at hres
  exact hres

/-- **Unconditional Resultant Nonvanishing & Log-Norm Bound (`frobenius_trace_norm_nonzero_log_bound`)**:
Let `T : Matrix (Fin n) (Fin n) ℤ` be any rank-`n` integral Frobenius operator (`q^e · Frob_w`)
whose complex eigenvalues `α` satisfy `‖α‖ ≤ q^e (√q + 2)` (`q ≥ 7`, `e ≥ 1`), and let `Q : ℤ[X]`
be any monic integer polynomial whose complex roots `β` have the Eisenstein form
`β = q^e * eis3 q e z` (`‖z‖ = 1`).
Then `NN := resultantInt T Q ∈ ℤ` satisfies:
1. **`NN ≠ 0`**, and
2. **`Real.log |(NN : ℝ)| ≤ (n : ℝ) * (Q.natDegree : ℝ) * (2 * (e : ℝ) * Real.log (q : ℝ) + 1)`**! -/
theorem frobenius_trace_norm_nonzero_log_bound {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℤ) (Q : ℤ[X]) (hQ : Q.Monic)
    (q e : ℕ) (hq : 7 ≤ q) (he : 1 ≤ e)
    (hT_bd : ∀ α ∈ ((T.map (Int.castRingHom ℂ)).charpoly).roots,
      ‖α‖ ≤ (q : ℝ) ^ e * (Real.sqrt (q : ℝ) + 2))
    (hQ_eis : ∀ β ∈ (Q.map (Int.castRingHom ℂ)).roots,
      ∃ z : ℂ, ‖z‖ = 1 ∧ β = (q : ℂ) ^ e * eis3 q e z) :
    resultantInt T Q ≠ 0 ∧
    Real.log |((resultantInt T Q : ℤ) : ℝ)| ≤
      (n : ℝ) * (Q.natDegree : ℝ) * (2 * (e : ℝ) * Real.log (q : ℝ) + 1) := by
  let f : ℤ →+* ℂ := Int.castRingHom ℂ
  let Tℂ := T.map f
  let Qℂ := Q.map f
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hqe0 : (q : ℂ) ^ e ≠ 0 := pow_ne_zero e hq0
  have hqe_pos : (0 : ℝ) < (q : ℝ) ^ e := pow_pos (by exact_mod_cast (show 0 < q by omega)) e
  have hpair : ∀ β ∈ Qℂ.roots, ∀ α ∈ Tℂ.charpoly.roots,
      α - β ≠ 0 ∧ Real.log ‖α - β‖ ≤ 2 * (e : ℝ) * Real.log (q : ℝ) + 1 := by
    intro β hβ α hα
    obtain ⟨z, hz, rfl⟩ := hQ_eis β hβ
    let t : ℂ := α / (q : ℂ) ^ e
    have ht_eq : α = (q : ℂ) ^ e * t := by
      simp only [t, mul_div_cancel₀ _ hqe0]
    have ht_bd : ‖t‖ ≤ Real.sqrt (q : ℝ) + 2 := by
      have h1 := hT_bd α hα
      rw [ht_eq, norm_mul, norm_pow, Complex.norm_natCast] at h1
      exact le_of_mul_le_mul_left h1 hqe_pos
    obtain ⟨hne, hlog⟩ := eisenstein_trace_archimedean_separation q e hq he z t hz ht_bd
    have hdiff : α - (q : ℂ) ^ e * eis3 q e z = (q : ℂ) ^ e * (t - eis3 q e z) := by
      rw [ht_eq]; ring
    rw [hdiff]
    exact ⟨mul_ne_zero hqe0 (sub_ne_zero.mpr hne), hlog⟩
  have hprod := resultantInt_cast_eq_prod_roots T Q hQ
  have hne : resultantInt T Q ≠ 0 := by
    intro h0
    have h0C : ((resultantInt T Q : ℤ) : ℂ) = 0 := by rw [h0]; simp
    rw [hprod] at h0C
    rw [Multiset.prod_eq_zero_iff] at h0C
    simp only [Multiset.mem_map] at h0C
    obtain ⟨β, hβ, hinner⟩ := h0C
    rw [Multiset.prod_eq_zero_iff] at hinner
    simp only [Multiset.mem_map] at hinner
    obtain ⟨α, hα, hαβ⟩ := hinner
    exact (hpair β hβ α hα).1 hαβ
  refine ⟨hne, ?_⟩
  have hnorm_eq : |((resultantInt T Q : ℤ) : ℝ)| =
      (Qℂ.roots.map fun β => (Tℂ.charpoly.roots.map fun α => ‖α - β‖).prod).prod := by
    rw [← Complex.norm_intCast, hprod]
    have hnorm_prod : ∀ s : Multiset ℂ, ‖s.prod‖ = (s.map norm).prod := by
      intro s
      induction s using Multiset.induction_on with
      | empty => simp
      | cons a s ih => simp [ih]
    rw [hnorm_prod, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun β _ => ?_
    change ‖(Tℂ.charpoly.roots.map fun α => α - β).prod‖ = _
    rw [hnorm_prod, Multiset.map_map]
    rfl
  have hlog_prod : ∀ (s : Multiset ℝ), (∀ x ∈ s, 0 < x) →
      Real.log s.prod = (s.map Real.log).sum := by
    intro s hs
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      have ha : 0 < a := hs a (Multiset.mem_cons_self a s)
      have hs' : ∀ x ∈ s, 0 < x := fun x hx => hs x (Multiset.mem_cons_of_mem hx)
      have hsp : 0 < s.prod := Multiset.prod_pos hs'
      rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons,
        Real.log_mul ha.ne' hsp.ne', ih hs']
  have hinner_pos : ∀ β ∈ Qℂ.roots, 0 < (Tℂ.charpoly.roots.map fun α => ‖α - β‖).prod := by
    intro β hβ
    refine Multiset.prod_pos fun x hx => ?_
    simp only [Multiset.mem_map] at hx
    obtain ⟨α, hα, rfl⟩ := hx
    exact norm_pos_iff.mpr (hpair β hβ α hα).1
  have hlog_eq : Real.log |((resultantInt T Q : ℤ) : ℝ)| =
      (Qℂ.roots.map fun β => (Tℂ.charpoly.roots.map fun α => Real.log ‖α - β‖).sum).sum := by
    rw [hnorm_eq, hlog_prod]
    · rw [Multiset.map_map]
      congr 1
      refine Multiset.map_congr rfl fun β hβ => ?_
      change Real.log (Tℂ.charpoly.roots.map fun α => ‖α - β‖).prod = _
      rw [hlog_prod]
      · rw [Multiset.map_map]; rfl
      · intro x hx
        simp only [Multiset.mem_map] at hx
        obtain ⟨α, hα, rfl⟩ := hx
        exact norm_pos_iff.mpr (hpair β hβ α hα).1
    · intro x hx
      simp only [Multiset.mem_map] at hx
      obtain ⟨β, hβ, rfl⟩ := hx
      exact hinner_pos β hβ
  have hsum_le : ∀ (s : Multiset ℂ) (g : ℂ → ℝ) (B : ℝ),
      (∀ x ∈ s, g x ≤ B) → (s.map g).sum ≤ (s.card : ℝ) * B := by
    intro s g B hB
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, Nat.cast_add, Nat.cast_one]
      have ha := hB a (Multiset.mem_cons_self a s)
      have hs := ih (fun x hx => hB x (Multiset.mem_cons_of_mem hx))
      linarith
  have hcardT : Tℂ.charpoly.roots.card = n := by
    have hsp : Tℂ.charpoly.Splits := IsAlgClosed.splits Tℂ.charpoly
    have h1 := hsp.natDegree_eq_card_roots
    have h2 : Tℂ.charpoly.natDegree = n := by simp [Matrix.charpoly_natDegree_eq_dim]
    omega
  have hcardQ : Qℂ.roots.card = Q.natDegree := by
    have hsp : Qℂ.Splits := IsAlgClosed.splits Qℂ
    have h1 := hsp.natDegree_eq_card_roots
    have h2 : Qℂ.natDegree = Q.natDegree := hQ.natDegree_map f
    omega
  rw [hlog_eq]
  have houter : (Qℂ.roots.map fun β => (Tℂ.charpoly.roots.map fun α => Real.log ‖α - β‖).sum).sum ≤
      (Qℂ.roots.card : ℝ) * ((Tℂ.charpoly.roots.card : ℝ) * (2 * (e : ℝ) * Real.log (q : ℝ) + 1)) := by
    refine hsum_le Qℂ.roots _ _ fun β hβ => ?_
    exact hsum_le Tℂ.charpoly.roots _ _ fun α hα => (hpair β hβ α hα).2
  rw [hcardT, hcardQ] at houter
  linarith

/-! ### 4.4 `l`-adic Divisibility in `ℤ_[l]` for `resultantInt T Q` -/

/-- If `(l : ℤ_[l]) ^ k ∣ (NN : ℤ_[l])` in `ℤ_[l]` and `NN ≠ 0`, then `k ≤ padicValInt l NN`. -/
theorem le_padicValInt_of_pow_dvd_padicInt {l : ℕ} [Fact l.Prime] {NN : ℤ} (hNN : NN ≠ 0)
    {k : ℕ} (hdvd : ((l : ℤ_[l]) ^ k) ∣ (NN : ℤ_[l])) :
    k ≤ padicValInt l NN := by
  obtain ⟨q, hq⟩ := hdvd
  have hzmod : ((NN : ℤ) : ZMod (l ^ k)) = 0 := by
    have h1 := congrArg (PadicInt.toZModPow k) hq
    simp only [map_intCast, map_mul, map_pow, map_natCast] at h1
    have hlk : ((l : ZMod (l ^ k)) ^ k) = 0 := by
      rw [← Nat.cast_pow, ZMod.natCast_self]
    rw [hlk, zero_mul] at h1
    exact h1
  have hzdvd : ((l ^ k : ℕ) : ℤ) ∣ NN := (ZMod.intCast_zmod_eq_zero_iff_dvd NN (l ^ k)).mp hzmod
  have hnatdvd : l ^ k ∣ NN.natAbs := by
    rw [← Int.natCast_dvd]
    exact hzdvd
  have hne_abs : NN.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hNN
  rw [padicValInt]
  exact (padicValNat_dvd_iff_le hne_abs).mp hnatdvd

/-- **Universal `l`-adic Factor Divisibility of `resultantInt T Q` in `ℤ_[l]`**:
For ANY prime `l`, if `T.charpoly` over `ℤ_[l]` has linear factors `∏_{α ∈ sT} (X - C α)` and
`Q` over `ℤ_[l]` has linear factors `∏_{β ∈ sQ} (X - C β)`, then
`∏_{β ∈ sQ} ∏_{α ∈ sT} (α - β)` DIVIDES `(resultantInt T Q : ℤ_[l])` in `ℤ_[l]`!
Consequently, if `((l : ℤ_[l]) ^ v)` divides that root-difference product and `resultantInt T Q ≠ 0`,
then **`v ≤ padicValInt l (resultantInt T Q)`**! -/
theorem padicValInt_resultantInt_ge_of_factor {l : ℕ} [Fact l.Prime] {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℤ) (Q : ℤ[X]) (hNN : resultantInt T Q ≠ 0)
    (sT sQ : Multiset ℤ_[l]) (P_rem Q_rem : ℤ_[l][X])
    (hT_fac : (T.map (Int.castRingHom ℤ_[l])).charpoly =
      (sT.map fun α => Polynomial.X - Polynomial.C α).prod * P_rem)
    (hQ_fac : Q.map (Int.castRingHom ℤ_[l]) =
      (sQ.map fun β => Polynomial.X - Polynomial.C β).prod * Q_rem)
    (v : ℕ)
    (hv : ((l : ℤ_[l]) ^ v) ∣ (sQ.map fun β => (sT.map fun α => α - β).prod).prod) :
    v ≤ padicValInt l (resultantInt T Q) := by
  let f : ℤ →+* ℤ_[l] := Int.castRingHom ℤ_[l]
  let Tl := T.map f
  let Ql := Q.map f
  have hcast : ((resultantInt T Q : ℤ) : ℤ_[l]) = Matrix.det (Polynomial.aeval Tl Ql) := by
    unfold resultantInt
    change f (Matrix.det (Polynomial.aeval T Q)) = _
    rw [RingHom.map_det, map_aeval_matrix]
  have hdvd_outer : (sQ.map fun β => Matrix.det (Tl - β • (1 : Matrix (Fin n) (Fin n) ℤ_[l]))).prod ∣
      ((resultantInt T Q : ℤ) : ℤ_[l]) := by
    rw [hcast]
    have hQl : Ql = (sQ.map fun β => Polynomial.X - Polynomial.C β).prod * Q_rem := hQ_fac
    rw [hQl, map_mul, Matrix.det_mul, det_aeval_prod_X_sub_C]
    exact dvd_mul_right _ _
  have hdvd_each : ∀ β : ℤ_[l], (sT.map fun α => α - β).prod ∣
      Matrix.det (Tl - β • (1 : Matrix (Fin n) (Fin n) ℤ_[l])) := by
    intro β
    rw [det_sub_smul_one_eq_neg_one_pow_mul_eval_charpoly, hT_fac, Polynomial.eval_mul]
    have hsign : ∀ s : Multiset ℤ_[l],
        (s.map fun α => α - β).prod = (-1 : ℤ_[l]) ^ s.card * (s.map fun α => β - α).prod := by
      intro s
      induction s using Multiset.induction_on with
      | empty => simp
      | cons a s ih =>
        rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ,
          Multiset.map_cons, Multiset.prod_cons, ih]
        ring
    have hev : (sT.map fun α => Polynomial.X - Polynomial.C α).prod.eval β =
        (sT.map fun α => β - α).prod := by
      rw [Polynomial.eval_multiset_prod, Multiset.map_map]
      refine congrArg Multiset.prod (Multiset.map_congr rfl fun α _ => ?_)
      simp
    rw [hev, hsign sT]
    refine ⟨(-1 : ℤ_[l]) ^ (n + sT.card) * P_rem.eval β, ?_⟩
    have hneg2 : (-1 : ℤ_[l]) ^ sT.card * (-1 : ℤ_[l]) ^ sT.card = 1 := by
      rw [← mul_pow]; norm_num
    calc (-1 : ℤ_[l]) ^ n * ((sT.map fun α => β - α).prod * P_rem.eval β)
        = ((-1 : ℤ_[l]) ^ sT.card * (-1 : ℤ_[l]) ^ sT.card) *
            ((-1 : ℤ_[l]) ^ n * ((sT.map fun α => β - α).prod * P_rem.eval β)) := by
          rw [hneg2, one_mul]
      _ = (-1 : ℤ_[l]) ^ sT.card * (sT.map fun α => β - α).prod *
            ((-1 : ℤ_[l]) ^ (n + sT.card) * P_rem.eval β) := by
          rw [pow_add]; ring
  have hdvd_prod : (sQ.map fun β => (sT.map fun α => α - β).prod).prod ∣
      (sQ.map fun β => Matrix.det (Tl - β • (1 : Matrix (Fin n) (Fin n) ℤ_[l]))).prod := by
    clear hQ_fac hdvd_outer hv
    induction sQ using Multiset.induction_on with
    | empty => simp
    | cons b s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons]
      exact mul_dvd_mul (hdvd_each b) ih
  exact le_padicValInt_of_pow_dvd_padicInt hNN (hv.trans (hdvd_prod.trans hdvd_outer))

/-! ### 4.5 End-to-End Pure Polynomial Bound `(condF * t)^C` Across ALL Good Odd Primes -/

/-- **Explicit Polynomial Log-Bound from Two Auxiliary Primes `r₁ ≠ r₂`**:
If `T₁, T₂` have Borel–Clozel rank `n₁, n₂ ≤ c₀ * dK ^ a * N ^ b * e ^ c` and Eisenstein degree
`deg(Q₁), deg(Q₂) ≤ d_orb`, then
`log |NN₁| + log |NN₂| ≤ (c₀ * dK^a * N^b * e^c * d_orb) * (2 * e + 1) * (log r₁ + log r₂)`! -/
theorem resultant_two_primes_poly_log_bound {n₁ n₂ : ℕ}
    (T₁ : Matrix (Fin n₁) (Fin n₁) ℤ) (Q₁ : ℤ[X]) (hQ₁ : Q₁.Monic)
    (T₂ : Matrix (Fin n₂) (Fin n₂) ℤ) (Q₂ : ℤ[X]) (hQ₂ : Q₂.Monic)
    (r₁ r₂ e : ℕ) (hr₁ : 7 ≤ r₁) (hr₂ : 7 ≤ r₂) (he : 1 ≤ e)
    (hT₁ : ∀ α ∈ ((T₁.map (Int.castRingHom ℂ)).charpoly).roots,
      ‖α‖ ≤ (r₁ : ℝ) ^ e * (Real.sqrt (r₁ : ℝ) + 2))
    (hQ₁_eis : ∀ β ∈ (Q₁.map (Int.castRingHom ℂ)).roots,
      ∃ z : ℂ, ‖z‖ = 1 ∧ β = (r₁ : ℂ) ^ e * eis3 r₁ e z)
    (hT₂ : ∀ α ∈ ((T₂.map (Int.castRingHom ℂ)).charpoly).roots,
      ‖α‖ ≤ (r₂ : ℝ) ^ e * (Real.sqrt (r₂ : ℝ) + 2))
    (hQ₂_eis : ∀ β ∈ (Q₂.map (Int.castRingHom ℂ)).roots,
      ∃ z : ℂ, ‖z‖ = 1 ∧ β = (r₂ : ℂ) ^ e * eis3 r₂ e z)
    (B_rk B_orb : ℝ) (hBrk : 0 ≤ B_rk) (_hBorb : 0 ≤ B_orb)
    (hn₁ : (n₁ : ℝ) ≤ B_rk) (hn₂ : (n₂ : ℝ) ≤ B_rk)
    (hd₁ : (Q₁.natDegree : ℝ) ≤ B_orb) (hd₂ : (Q₂.natDegree : ℝ) ≤ B_orb) :
    resultantInt T₁ Q₁ ≠ 0 ∧ resultantInt T₂ Q₂ ≠ 0 ∧
    Real.log |((resultantInt T₁ Q₁ : ℤ) : ℝ)| + Real.log |((resultantInt T₂ Q₂ : ℤ) : ℝ)| ≤
      B_rk * B_orb * (2 * (e : ℝ) + 1) * (Real.log (r₁ : ℝ) + Real.log (r₂ : ℝ)) := by
  obtain ⟨hne₁, hlog₁⟩ := frobenius_trace_norm_nonzero_log_bound T₁ Q₁ hQ₁ r₁ e hr₁ he hT₁ hQ₁_eis
  obtain ⟨hne₂, hlog₂⟩ := frobenius_trace_norm_nonzero_log_bound T₂ Q₂ hQ₂ r₂ e hr₂ he hT₂ hQ₂_eis
  have hlr₁ : (1 : ℝ) ≤ Real.log (r₁ : ℝ) := by
    have hexp : Real.exp 1 ≤ (r₁ : ℝ) := by
      have h1 : Real.exp 1 < 3 := by
        have := Real.exp_one_lt_d9
        linarith
      have h2 : (7 : ℝ) ≤ (r₁ : ℝ) := by exact_mod_cast hr₁
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (r₁ : ℝ) := Real.log_le_log (Real.exp_pos 1) hexp
  have hlr₂ : (1 : ℝ) ≤ Real.log (r₂ : ℝ) := by
    have hexp : Real.exp 1 ≤ (r₂ : ℝ) := by
      have h1 : Real.exp 1 < 3 := by
        have := Real.exp_one_lt_d9
        linarith
      have h2 : (7 : ℝ) ≤ (r₂ : ℝ) := by exact_mod_cast hr₂
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (r₂ : ℝ) := Real.log_le_log (Real.exp_pos 1) hexp
  have hb1 : Real.log |((resultantInt T₁ Q₁ : ℤ) : ℝ)| ≤
      B_rk * B_orb * (2 * (e : ℝ) + 1) * Real.log (r₁ : ℝ) := by
    have hstep1 : 2 * (e : ℝ) * Real.log (r₁ : ℝ) + 1 ≤ (2 * (e : ℝ) + 1) * Real.log (r₁ : ℝ) := by
      nlinarith
    have hstep2 : (n₁ : ℝ) * (Q₁.natDegree : ℝ) ≤ B_rk * B_orb :=
      mul_le_mul hn₁ hd₁ (Nat.cast_nonneg _) hBrk
    have hpos_rhs : 0 ≤ (2 * (e : ℝ) + 1) * Real.log (r₁ : ℝ) := by positivity
    calc Real.log |((resultantInt T₁ Q₁ : ℤ) : ℝ)|
        ≤ (n₁ : ℝ) * (Q₁.natDegree : ℝ) * (2 * (e : ℝ) * Real.log (r₁ : ℝ) + 1) := hlog₁
      _ ≤ (n₁ : ℝ) * (Q₁.natDegree : ℝ) * ((2 * (e : ℝ) + 1) * Real.log (r₁ : ℝ)) :=
          mul_le_mul_of_nonneg_left hstep1 (by positivity)
      _ ≤ (B_rk * B_orb) * ((2 * (e : ℝ) + 1) * Real.log (r₁ : ℝ)) :=
          mul_le_mul_of_nonneg_right hstep2 hpos_rhs
      _ = B_rk * B_orb * (2 * (e : ℝ) + 1) * Real.log (r₁ : ℝ) := by ring
  have hb2 : Real.log |((resultantInt T₂ Q₂ : ℤ) : ℝ)| ≤
      B_rk * B_orb * (2 * (e : ℝ) + 1) * Real.log (r₂ : ℝ) := by
    have hstep1 : 2 * (e : ℝ) * Real.log (r₂ : ℝ) + 1 ≤ (2 * (e : ℝ) + 1) * Real.log (r₂ : ℝ) := by
      nlinarith
    have hstep2 : (n₂ : ℝ) * (Q₂.natDegree : ℝ) ≤ B_rk * B_orb :=
      mul_le_mul hn₂ hd₂ (Nat.cast_nonneg _) hBrk
    have hpos_rhs : 0 ≤ (2 * (e : ℝ) + 1) * Real.log (r₂ : ℝ) := by positivity
    calc Real.log |((resultantInt T₂ Q₂ : ℤ) : ℝ)|
        ≤ (n₂ : ℝ) * (Q₂.natDegree : ℝ) * (2 * (e : ℝ) * Real.log (r₂ : ℝ) + 1) := hlog₂
      _ ≤ (n₂ : ℝ) * (Q₂.natDegree : ℝ) * ((2 * (e : ℝ) + 1) * Real.log (r₂ : ℝ)) :=
          mul_le_mul_of_nonneg_left hstep1 (by positivity)
      _ ≤ (B_rk * B_orb) * ((2 * (e : ℝ) + 1) * Real.log (r₂ : ℝ)) :=
          mul_le_mul_of_nonneg_right hstep2 hpos_rhs
      _ = B_rk * B_orb * (2 * (e : ℝ) + 1) * Real.log (r₂ : ℝ) := by ring
  refine ⟨hne₁, hne₂, ?_⟩
  linarith

/-- **END-TO-END GLOBAL PURE POLYNOMIAL BOUND (`(condF * t)^C`) ACROSS ALL GOOD ODD PRIMES**:
Combines `corG_two_primes_sum_log` and `resultant_two_primes_poly_log_bound`:
whenever `condF * t ≥ 2`, `r₁, r₂ ≤ condF * t` (`r₁ ≠ r₂`, `r₁, r₂ ≥ 7`), the Borel–Clozel rank
and orbit degrees satisfy `B_rk ≤ (condF * t)^A₁`, `B_orb ≤ (condF * t)^A₂`, `e ≤ t`, and the
two global resultant integers `NN₁ := resultantInt T₁ Q₁`, `NN₂ := resultantInt T₂ Q₂` bound the
plus-parity Selmer sums across all `l ∈ Ls` (with multiplicity factor `C_mult ≤ (condF * t)^A₀`),
we obtain the **unconditional pure polynomial bound across ALL primes `l ∈ Ls` simultaneously**:
`∑_{l ∈ Ls} Real.log (l : ℕ) * ∑_{k=1}^{t-1} (len l k : ℝ) ≤ ((condF : ℝ) * (t : ℝ)) ^ (A₀ + A₁ + A₂ + 5)`! -/
theorem global_plus_selmer_pure_poly_bound
    (Ls : Finset Nat.Primes) (condF t e : ℕ) (hct : 2 ≤ condF * t) (he1 : 1 ≤ e) (het : e ≤ t)
    (len : Nat.Primes → ℕ → ℕ)
    {n₁ n₂ : ℕ}
    (T₁ : Matrix (Fin n₁) (Fin n₁) ℤ) (Q₁ : ℤ[X]) (hQ₁ : Q₁.Monic)
    (T₂ : Matrix (Fin n₂) (Fin n₂) ℤ) (Q₂ : ℤ[X]) (hQ₂ : Q₂.Monic)
    (r₁ r₂ : ℕ) (hr_ne : r₁ ≠ r₂) (hr₁ : 7 ≤ r₁) (hr₂ : 7 ≤ r₂)
    (hr₁_le : r₁ ≤ condF * t) (hr₂_le : r₂ ≤ condF * t)
    (hT₁ : ∀ α ∈ ((T₁.map (Int.castRingHom ℂ)).charpoly).roots,
      ‖α‖ ≤ (r₁ : ℝ) ^ e * (Real.sqrt (r₁ : ℝ) + 2))
    (hQ₁_eis : ∀ β ∈ (Q₁.map (Int.castRingHom ℂ)).roots,
      ∃ z : ℂ, ‖z‖ = 1 ∧ β = (r₁ : ℂ) ^ e * eis3 r₁ e z)
    (hT₂ : ∀ α ∈ ((T₂.map (Int.castRingHom ℂ)).charpoly).roots,
      ‖α‖ ≤ (r₂ : ℝ) ^ e * (Real.sqrt (r₂ : ℝ) + 2))
    (hQ₂_eis : ∀ β ∈ (Q₂.map (Int.castRingHom ℂ)).roots,
      ∃ z : ℂ, ‖z‖ = 1 ∧ β = (r₂ : ℂ) ^ e * eis3 r₂ e z)
    (A₀ A₁ A₂ : ℕ) (C_mult : ℝ) (hC_nonneg : 0 ≤ C_mult)
    (hC_le : C_mult ≤ ((condF : ℝ) * (t : ℝ)) ^ A₀)
    (hn₁ : (n₁ : ℝ) ≤ ((condF : ℝ) * (t : ℝ)) ^ A₁)
    (hn₂ : (n₂ : ℝ) ≤ ((condF : ℝ) * (t : ℝ)) ^ A₁)
    (hd₁ : (Q₁.natDegree : ℝ) ≤ ((condF : ℝ) * (t : ℝ)) ^ A₂)
    (hd₂ : (Q₂.natDegree : ℝ) ≤ ((condF : ℝ) * (t : ℝ)) ^ A₂)
    (hb₁ : ∀ l ∈ Ls, (l : ℕ) ≠ r₁ →
      (∑ k ∈ Finset.Ico 1 t, (len l k : ℝ)) ≤ C_mult * (padicValInt l (resultantInt T₁ Q₁) : ℝ))
    (hb₂ : ∀ l ∈ Ls, (l : ℕ) ≠ r₂ →
      (∑ k ∈ Finset.Ico 1 t, (len l k : ℝ)) ≤ C_mult * (padicValInt l (resultantInt T₂ Q₂) : ℝ)) :
    ∑ l ∈ Ls, Real.log (l : ℕ) * (∑ k ∈ Finset.Ico 1 t, (len l k : ℝ)) ≤
      ((condF : ℝ) * (t : ℝ)) ^ (A₀ + A₁ + A₂ + 5) := by
  set X : ℝ := (condF : ℝ) * (t : ℝ)
  have hX2 : (2 : ℝ) ≤ X := by
    have : (2 : ℝ) ≤ ((condF * t : ℕ) : ℝ) := by exact_mod_cast hct
    simpa [X, Nat.cast_mul] using this
  have hXpos : 0 < X := by linarith
  have hcond_pos : 1 ≤ condF := by
    by_contra h0
    have hc0 : condF = 0 := by omega
    rw [hc0, zero_mul] at hct
    omega
  have he_le_X : (e : ℝ) ≤ X := by
    have h1 : e ≤ condF * t := le_trans het (Nat.le_mul_of_pos_left t (by omega))
    have h2 : (e : ℝ) ≤ ((condF * t : ℕ) : ℝ) := by exact_mod_cast h1
    simpa [X, Nat.cast_mul] using h2
  obtain ⟨hne₁, hne₂, hlog_sum⟩ :=
    resultant_two_primes_poly_log_bound T₁ Q₁ hQ₁ T₂ Q₂ hQ₂ r₁ r₂ e hr₁ hr₂ he1
      hT₁ hQ₁_eis hT₂ hQ₂_eis (X ^ A₁) (X ^ A₂) (by positivity) (by positivity)
      hn₁ hn₂ hd₁ hd₂
  have hsum := corG_two_primes_sum_log Ls t len r₁ r₂ hr_ne
    (resultantInt T₁ Q₁) (resultantInt T₂ Q₂) hne₁ hne₂ C_mult hC_nonneg hb₁ hb₂
  have hlogr₁ : Real.log (r₁ : ℝ) ≤ X := by
    have hle : (r₁ : ℝ) ≤ X := by
      have : (r₁ : ℝ) ≤ ((condF * t : ℕ) : ℝ) := by exact_mod_cast hr₁_le
      simpa [X, Nat.cast_mul] using this
    have hr1pos : (0 : ℝ) < (r₁ : ℝ) := by positivity
    linarith [Real.log_le_sub_one_of_pos hr1pos]
  have hlogr₂ : Real.log (r₂ : ℝ) ≤ X := by
    have hle : (r₂ : ℝ) ≤ X := by
      have : (r₂ : ℝ) ≤ ((condF * t : ℕ) : ℝ) := by exact_mod_cast hr₂_le
      simpa [X, Nat.cast_mul] using this
    have hr2pos : (0 : ℝ) < (r₂ : ℝ) := by positivity
    linarith [Real.log_le_sub_one_of_pos hr2pos]
  have hXsq : 4 ≤ X ^ 2 := by nlinarith
  have hfac1 : 2 * (e : ℝ) + 1 ≤ X ^ 3 := by
    have hX3 : 4 * X ≤ X ^ 3 := by
      have : X ^ 3 = X * X ^ 2 := by ring
      nlinarith
    linarith
  have hfac2 : Real.log (r₁ : ℝ) + Real.log (r₂ : ℝ) ≤ X ^ 2 := by nlinarith
  have hprod_bound :
      X ^ A₁ * X ^ A₂ * (2 * (e : ℝ) + 1) * (Real.log (r₁ : ℝ) + Real.log (r₂ : ℝ)) ≤
        X ^ (A₁ + A₂ + 5) := by
    have hlog_nonneg : 0 ≤ Real.log (r₁ : ℝ) + Real.log (r₂ : ℝ) :=
      add_nonneg (Real.log_natCast_nonneg r₁) (Real.log_natCast_nonneg r₂)
    calc X ^ A₁ * X ^ A₂ * (2 * (e : ℝ) + 1) * (Real.log (r₁ : ℝ) + Real.log (r₂ : ℝ))
        ≤ X ^ A₁ * X ^ A₂ * X ^ 3 * X ^ 2 := by
          gcongr
      _ = X ^ (A₁ + A₂ + 5) := by
          rw [pow_add, pow_add]
          ring
  have hlog_final :
      Real.log |((resultantInt T₁ Q₁ : ℤ) : ℝ)| + Real.log |((resultantInt T₂ Q₂ : ℤ) : ℝ)| ≤
        X ^ (A₁ + A₂ + 5) := hlog_sum.trans hprod_bound
  have hlog_nonneg :
      0 ≤ Real.log |((resultantInt T₁ Q₁ : ℤ) : ℝ)| + Real.log |((resultantInt T₂ Q₂ : ℤ) : ℝ)| := by
    have h1 : (1 : ℝ) ≤ |((resultantInt T₁ Q₁ : ℤ) : ℝ)| := by
      have : (1 : ℤ) ≤ |resultantInt T₁ Q₁| := Int.one_le_abs hne₁
      exact_mod_cast this
    have h2 : (1 : ℝ) ≤ |((resultantInt T₂ Q₂ : ℤ) : ℝ)| := by
      have : (1 : ℤ) ≤ |resultantInt T₂ Q₂| := Int.one_le_abs hne₂
      exact_mod_cast this
    exact add_nonneg (Real.log_nonneg h1) (Real.log_nonneg h2)
  calc ∑ l ∈ Ls, Real.log (l : ℕ) * (∑ k ∈ Finset.Ico 1 t, (len l k : ℝ))
      ≤ C_mult * (Real.log |((resultantInt T₁ Q₁ : ℤ) : ℝ)| +
          Real.log |((resultantInt T₂ Q₂ : ℤ) : ℝ)|) := hsum
    _ ≤ X ^ A₀ * X ^ (A₁ + A₂ + 5) :=
        mul_le_mul hC_le hlog_final hlog_nonneg (by positivity)
    _ = X ^ (A₀ + A₁ + A₂ + 5) := by
        rw [← pow_add]
        congr 1
        omega

end GlobalResultantBound

end Stage12GMAReducibility
end RHDirect
