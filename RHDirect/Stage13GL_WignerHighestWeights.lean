import RHDirect.Stage13GL_BernoulliAndWeylAlg
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.FieldTheory.IsAlgClosed.Spectrum

/-!
# RHDirect.Stage13GL_WignerHighestWeights

Option-C GaloisLibrary Wave 2 (Module 2 of 3): **Weyl Character Regularity,
Dual Infinitesimal Character Regularity, Cohomology Transport, and Wigner Highest-Weight
Vanishing**, surgically ported and compressed from the `42` `WeylCharacterRegularity` (`4` files)
and `WignerHighestWeights` (`38` files) modules plus their inlined helper layers
(`DualInfinitesimalCharacterRegular`, `HasCohomologyTransport`, `HasCohomology`, `ExpSq`,
`ProjectionCompact`, `AntisymmetrizedProductEqFactorialSmulQdet`, `MultisetSeparation`)
directly onto concrete Mathlib types and `RHDirect.Stage13GL_BernoulliAndWeylAlg`
(zero invented proxy structures, zero open parameters, zero `sorry`, zero custom axioms).

## Contents
1. **Quantum Determinant Centrality, Antisymmetrized Product & Multiset Separation**:
   - Row skew-symmetry (`qminor_row_comp_perm`, `qminor_row_eq_zero`), general `GlRel` centrality
     (`qdet_central`), doubly antisymmetrized products (`orderedTermProduct`,
     `doublyAntisymmetrizedProduct`, `antisymmetrizedProduct_perm_invariant`,
     `antisymmetrizedProduct_eq_factorial_smul_qdet`, `quantumDet_neg_transpose`), `msetSep`, `expSq`.
2. **Kronecker Product & Weyl Character Regularity (`WeylCharacterRegularity`)**:
   - `piK`, `kronAt`, concrete `regFun`, `AlgRep`, `extGL`, `coordL`, `AlgRep.dmat`, `AlgRep.triv`,
     `AlgRep.std`, `IsReg`, `dOf`, `eOf`, `AlgInfChar`, `algInfChar_iff`.
   - Regularity & derivative invariance (`isReg_conj`, `dOf_conj`, `eOf_conj`, `isReg_piK`, `dOf_piK`,
     `eOf_piK`, `coord_hol`), twisted polynomial representations (`fac`, `isReg_fac`, `dOf_fac`,
     `eOf_fac`), and highest-weight realization (`exists_irr`, `exists_tens`,
     `exists_algRep_of_antitone`).
3. **Dual Infinitesimal Character Regularity (`DualInfinitesimalCharacterRegular`)**:
   - `dualS`, `dualE`, `HasDualInfChar`, `exists_joint_eigenvector`, `exists_nat_of_primitive`,
     `exists_highest`, `dmat_bracket`, `isPreconnected_invSet`, `commute_mat`, Laurent torus
     integrality (`eigenvalue_int`), `glRel_dualE`, `dualE_comm`, `qdet_commute_dualE`,
     `commute_dmat`, `exists_scalar`, `qdet_scalar`, and `exists_dualInfChar`.
4. **`(𝔤, K)`-Cohomology, Transport & Conjugation (`HasCohomology`, `HasCohomologyTransport`)**:
   - Smooth Lie commutation (`chart_rt_inf`, `hasDerivAt_curve_sm`, `lie_comm`, `rt_lie`, `glRel_Eop`).
   - Concrete Hermitian cochains (`Herm`, `adHerm`, `IsCochain`, `dCo`, `HasCohomology`, `IsCohFor`,
     `tensorK`, `tensorLie`), transport (`tr`, `hasCohomology_transport`), conjugation (`barG`, `barH`,
     `barRep`, `barL`), and algebraic isomorphism transport (`IsAlgIso`, `isAlgIso_refl`, `cohTransport`).
5. **Multi-`𝔤𝔩_n` Highest-Weight Irreducibility & Algebraic Isomorphism**:
   - `IsMultiGl`, `Stab`, `low`, `Dom`, `eL`, `hol`, `IsLieHom`, `eLRel`, exponential generation
     (`expGenC`, `expGen`, `expMat`, `expSub`), `lieDecomp`, `pairAlg`, `algIrr`, `multiHW`,
     `lowStab`, `lowLine`, `wtEq`, `hwIso`, `algIsoLie`, `algIso`.
6. **Telescoping Retraction, Antipode & Wigner Vanishing (`WignerVanishingGL`)**:
   - `rp`, `tel`, `eps`, `telML`, `telSum`, `telGrp`, `telDer`, `epsGrp`, `epsDer`, `glNegOp`,
     `dualIff`, `alphaAbs`, `holEq`, `holMul`, `alphaReal`, `tensA`, `tensB`, `homId`, `homot`,
     `kCurve`, `infAbs`, `tensDer`, `WignerVanishingGL`, and `wigner`.
-/

noncomputable section

open NumberField Matrix Topology
open RHDirect.CapelliCore RHDirect.Stage13GL_BernoulliAndWeylAlg
open scoped TensorProduct

namespace RHDirect.Stage13GL_WignerHighestWeights

/-! ## Section 1: Quantum Determinant Centrality, Antisymmetrized Product & Multiset Separation -/

section QuantumDetHelpers

open Finset

private lemma prod_ofFn_update_eq_mul {A : Type*} [Ring A] : ∀ {t : ℕ} (F : Fin t → A) (k : Fin t),
    ∃ L R : A, ∀ x : A, (List.ofFn (Function.update F k x)).prod = L * x * R
  | 0, _, k => k.elim0
  | t + 1, F, k => by
    refine Fin.cases ?_ (fun k' => ?_) k
    · refine ⟨1, (List.ofFn fun i : Fin t => F i.succ).prod, fun x => ?_⟩
      simp [List.ofFn_succ, Fin.succ_ne_zero]
    · obtain ⟨L, R, h⟩ := prod_ofFn_update_eq_mul (fun i : Fin t => F i.succ) k'
      refine ⟨F 0 * L, R, fun x => ?_⟩
      have hf : (fun i : Fin t => Function.update F k'.succ x i.succ) =
          Function.update (fun i : Fin t => F i.succ) k' x := by
        funext i; simp [Function.update_apply, Fin.succ_inj]
      rw [List.ofFn_succ, List.prod_cons, hf, h]
      simp [(Fin.succ_ne_zero k').symm, mul_assoc]

private lemma prod_ofFn_update_sub {A : Type*} [Ring A] {t : ℕ} (F : Fin t → A) (k : Fin t) (x y : A) :
    (List.ofFn (Function.update F k (x - y))).prod =
      (List.ofFn (Function.update F k x)).prod - (List.ofFn (Function.update F k y)).prod := by
  obtain ⟨L, R, h⟩ := prod_ofFn_update_eq_mul F k
  rw [h, h, h, mul_sub, sub_mul]

private lemma prod_ofFn_update_ite {A : Type*} [Ring A] {t : ℕ} (F : Fin t → A) (k : Fin t) (p : Prop)
    [Decidable p] (x : A) :
    (List.ofFn (Function.update F k (if p then x else 0))).prod =
      if p then (List.ofFn (Function.update F k x)).prod else 0 := by
  by_cases hp : p
  · simp only [if_pos hp]
  · simp only [if_neg hp]
    obtain ⟨L, R, h⟩ := prod_ofFn_update_eq_mul F k
    rw [h, mul_zero, zero_mul]

private lemma commutator_prod_ofFn_eq_sum_update {A : Type*} [Ring A] (X : A) : ∀ {t : ℕ} (F : Fin t → A),
    X * (List.ofFn F).prod - (List.ofFn F).prod * X =
      ∑ k, (List.ofFn (Function.update F k (X * F k - F k * X))).prod
  | 0, _ => by simp
  | t + 1, F => by
    have ih := commutator_prod_ofFn_eq_sum_update X (fun i : Fin t => F i.succ)
    rw [Fin.sum_univ_succ]
    have h0 : (List.ofFn (Function.update F 0 (X * F 0 - F 0 * X))).prod =
        (X * F 0 - F 0 * X) * (List.ofFn fun i : Fin t => F i.succ).prod := by
      simp [List.ofFn_succ, Fin.succ_ne_zero]
    have hs : ∀ k : Fin t, (List.ofFn (Function.update F k.succ (X * F k.succ - F k.succ * X))).prod =
        F 0 * (List.ofFn (Function.update (fun i : Fin t => F i.succ) k
          (X * F k.succ - F k.succ * X))).prod := by
      intro k
      have hf : (fun i : Fin t => Function.update F k.succ (X * F k.succ - F k.succ * X) i.succ) =
          Function.update (fun i : Fin t => F i.succ) k (X * F k.succ - F k.succ * X) := by
        funext i; simp [Function.update_apply, Fin.succ_inj]
      rw [List.ofFn_succ, List.prod_cons, hf]
      simp [(Fin.succ_ne_zero k).symm]
    rw [h0, Finset.sum_congr rfl (fun k _ => hs k), ← Finset.mul_sum, ← ih, List.ofFn_succ,
      List.prod_cons]
    noncomm_ring

private lemma capelliTm_commutator {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (hE : GlRel E) (v : ℂ) (a b c d : Fin n) :
    E c d * capelliTm E v a b - capelliTm E v a b * E c d =
      (if d = a then capelliTm E v c b else 0) - (if b = c then capelliTm E v a d else 0) := by
  have hc := hE c d a b
  have hcomm : E c d * (if a = b then algebraMap ℂ A v else 0) =
      (if a = b then algebraMap ℂ A v else 0) * E c d := by
    by_cases hab : a = b
    · simp only [if_pos hab]; exact (Algebra.commutes v (E c d)).symm
    · simp only [if_neg hab, mul_zero, zero_mul]
  have key : E c d * capelliTm E v a b - capelliTm E v a b * E c d = E c d * E a b - E a b * E c d := by
    unfold capelliTm; rw [mul_add, add_mul, hcomm]; abel
  rw [key, hc]
  unfold capelliTm
  by_cases h1 : d = a
  · by_cases h2 : b = c
    · subst h1; subst h2; simp
    · subst h1; simp [h2, Ne.symm h2]
  · by_cases h2 : b = c
    · subst h2; simp [h1, Ne.symm h1]
    · simp [h1, h2]

theorem qminor_row_comp_perm {A : Type*} [Ring A] [Algebra ℂ A] {n t : ℕ}
    (E : Fin n → Fin n → A) (a b : Fin t → Fin n) (ρ : Equiv.Perm (Fin t)) (u : ℂ) :
    qminor E (a ∘ ρ) b u = (((Equiv.Perm.sign ρ : ℤˣ) : ℤ) : ℂ) • qminor E a b u := by
  unfold qminor
  rw [Finset.smul_sum, ← Equiv.sum_comp (Equiv.mulLeft ρ⁻¹)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Equiv.coe_mulLeft, Function.comp_apply, Equiv.Perm.mul_apply]
  have hρ : ∀ k, ρ (ρ⁻¹ (σ k)) = σ k := fun k => ρ.apply_symm_apply (σ k)
  simp only [hρ]
  rw [Algebra.smul_def, map_intCast, ← mul_assoc, ← Int.cast_mul, Equiv.Perm.sign_mul,
    Equiv.Perm.sign_inv, Units.val_mul]

theorem qminor_row_eq_zero {A : Type*} [Ring A] [Algebra ℂ A] {n t : ℕ}
    (E : Fin n → Fin n → A) (a b : Fin t → Fin n) (u : ℂ) (ha : ¬ Function.Injective a) :
    qminor E a b u = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.1 ha
  have h := qminor_row_comp_perm E a b (Equiv.swap i j) u
  have ha' : a ∘ Equiv.swap i j = a := funext fun k => Equiv.apply_swap_eq_self hij k
  rw [ha', Equiv.Perm.sign_swap hne] at h
  have h2 : (2 : ℂ) • qminor E a b u = 0 := by
    rw [two_smul]
    calc qminor E a b u + qminor E a b u = qminor E a b u + (-qminor E a b u) := by
          conv_rhs => rw [← show (-1 : ℂ) • qminor E a b u = -qminor E a b u from neg_one_smul ℂ _]
          exact congrArg (qminor E a b u + ·) (by simpa using h)
      _ = 0 := add_neg_cancel _
  simpa [smul_smul] using congrArg ((2 : ℂ)⁻¹ • ·) h2

theorem qdet_central {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (hE : GlRel E) (u : ℂ) (c d : Fin n) :
    qdet E u * E c d = E c d * qdet E u := by
  have hs : ∀ (z : ℤ) (X P : A), X * ((z : A) * P) - (z : A) * P * X = (z : A) * (X * P - P * X) := by
    intro z X P; simp only [mul_sub, ← mul_assoc, (Int.cast_commute z X).eq]
  have hcomm : E c d * qdet E u - qdet E u * E c d =
      qminor E (Function.update id d c) id u - qminor E id (Function.update id c d) u := by
    unfold qdet qminor
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hs, ← mul_sub]
    congr 1
    rw [commutator_prod_ofFn_eq_sum_update]
    simp only [capelliTm_commutator E hE, prod_ofFn_update_sub, prod_ofFn_update_ite,
      Finset.sum_sub_distrib, id_eq]
    congr 1
    · rw [Finset.sum_eq_single (σ.symm d)]
      · rw [if_pos (σ.apply_symm_apply d).symm]
        congr 2; funext k
        by_cases hk : k = σ.symm d
        · subst hk; simp
        · simp [hk, show σ k ≠ d from fun h => hk (by rw [← h, Equiv.symm_apply_apply])]
      · intro b _ hb
        rw [if_neg (show d ≠ σ b from fun h => hb (by rw [h, Equiv.symm_apply_apply]))]
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      congr 2; funext k
      by_cases hk : k = c <;> simp [hk]
  have key : qminor E (Function.update id d c) id u - qminor E id (Function.update id c d) u = 0 := by
    by_cases hcd : c = d
    · rw [hcd, show Function.update (id : Fin n → Fin n) d d = id from funext fun x => by by_cases hx : x = d <;> simp [hx], sub_self]
    · rw [qminor_row_eq_zero E _ id u (fun h => hcd (h (by simp [hcd]))),
        qminor_eq_zero E hE id u _ (fun h => hcd (h (by simp [Ne.symm hcd]))), sub_zero]
  rw [key, sub_eq_zero] at hcomm
  exact hcomm.symm

def orderedTermProduct {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (arg : Fin n → ℂ) (σ τ : Equiv.Perm (Fin n)) : A :=
  (List.ofFn fun k : Fin n => capelliTm E (arg k) (σ k) (τ k)).prod

def doublyAntisymmetrizedProduct {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (arg : Fin n → ℂ) : A :=
  ∑ τ : Equiv.Perm (Fin n), ∑ σ : Equiv.Perm (Fin n),
    ((Equiv.Perm.sign τ : ℤ) : A) * (((Equiv.Perm.sign σ : ℤ) : A) * orderedTermProduct E arg σ τ)

private lemma term_two_by_two_exchange {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
    (E : Fin n → Fin n → A) (x y : ℂ) (p q c d : Fin n) :
    capelliTm E x p c * capelliTm E y q d - capelliTm E x q c * capelliTm E y p d -
        capelliTm E x p d * capelliTm E y q c + capelliTm E x q d * capelliTm E y p c =
      capelliTm E y p c * capelliTm E x q d - capelliTm E y q c * capelliTm E x p d -
        capelliTm E y p d * capelliTm E x q c + capelliTm E y q d * capelliTm E x p c := by
  simp only [capelliTm, Algebra.algebraMap_eq_smul_one]
  split_ifs <;>
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, zero_add] <;>
    module

private lemma list_prod_ofFn_update_adjacent {A : Type*} [Ring A] {t : ℕ} (f g : Fin t → A) (i : ℕ)
    (hi : i + 1 < t) (h : ∀ k : Fin t, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → g k = f k) :
    (List.ofFn g).prod = ((List.ofFn f).take i).prod * (g ⟨i, by omega⟩ * g ⟨i + 1, hi⟩) *
      ((List.ofFn f).drop (i + 2)).prod := by
  have htake : (List.ofFn g).take i = (List.ofFn f).take i := by
    apply List.ext_getElem
    · simp
    · intro j h1 _; simp only [List.getElem_take, List.getElem_ofFn]; simp only [List.length_take, List.length_ofFn] at h1
      exact h _ (by simp; omega) (by simp; omega)
  have hdrop : (List.ofFn g).drop (i + 2) = (List.ofFn f).drop (i + 2) := by
    apply List.ext_getElem
    · simp
    · intro j _ _; simp only [List.getElem_drop, List.getElem_ofFn]; exact h _ (by simp; omega) (by simp; omega)
  rw [← List.take_append_drop i (List.ofFn g), List.drop_eq_getElem_cons (by simp; omega),
    List.drop_eq_getElem_cons (by simp; omega), htake, List.getElem_ofFn, List.getElem_ofFn,
    show i + 1 + 1 = i + 2 from rfl, hdrop]
  simp only [List.prod_append, List.prod_cons, mul_assoc]

private lemma orderedProduct_adjacent_swap_identity {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ}
    (E : Fin (m + 1) → Fin (m + 1) → A) (i : Fin m) (arg : Fin (m + 1) → ℂ)
    (σ τ : Equiv.Perm (Fin (m + 1))) :
    orderedTermProduct E arg σ τ - orderedTermProduct E arg (σ * Equiv.swap i.castSucc i.succ) τ -
        orderedTermProduct E arg σ (τ * Equiv.swap i.castSucc i.succ) +
        orderedTermProduct E arg (σ * Equiv.swap i.castSucc i.succ) (τ * Equiv.swap i.castSucc i.succ) =
      orderedTermProduct E (arg ∘ Equiv.swap i.castSucc i.succ) σ τ -
        orderedTermProduct E (arg ∘ Equiv.swap i.castSucc i.succ) (σ * Equiv.swap i.castSucc i.succ) τ -
        orderedTermProduct E (arg ∘ Equiv.swap i.castSucc i.succ) σ (τ * Equiv.swap i.castSucc i.succ) +
        orderedTermProduct E (arg ∘ Equiv.swap i.castSucc i.succ) (σ * Equiv.swap i.castSucc i.succ)
          (τ * Equiv.swap i.castSucc i.succ) := by
  have hi : (i : ℕ) + 1 < m + 1 := by omega
  have hfix : ∀ k : Fin (m + 1), (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → Equiv.swap i.castSucc i.succ k = k := by
    intro k h1 h2
    exact Equiv.swap_apply_of_ne_of_ne (fun h => h1 (by subst h; simp)) (fun h => h2 (by subst h; simp))
  have hM : ∀ (a : Fin (m + 1) → ℂ) (σ' τ' : Equiv.Perm (Fin (m + 1))),
      (∀ k : Fin (m + 1), (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → a k = arg k ∧ σ' k = σ k ∧ τ' k = τ k) →
      orderedTermProduct E a σ' τ' = ((List.ofFn fun k => capelliTm E (arg k) (σ k) (τ k)).take i).prod *
        (capelliTm E (a ⟨i, by omega⟩) (σ' ⟨i, by omega⟩) (τ' ⟨i, by omega⟩) *
          capelliTm E (a ⟨i + 1, hi⟩) (σ' ⟨i + 1, hi⟩) (τ' ⟨i + 1, hi⟩)) *
        ((List.ofFn fun k => capelliTm E (arg k) (σ k) (τ k)).drop (i + 2)).prod := by
    intro a σ' τ' hk
    exact list_prod_ofFn_update_adjacent _ _ i hi fun k h1 h2 => by
      obtain ⟨e1, e2, e3⟩ := hk k h1 h2; rw [e1, e2, e3]
  have hc : ∀ k : Fin (m + 1), (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 →
      (arg ∘ Equiv.swap i.castSucc i.succ) k = arg k ∧
        (σ * Equiv.swap i.castSucc i.succ) k = σ k ∧ (τ * Equiv.swap i.castSucc i.succ) k = τ k :=
    fun k h1 h2 => by simp [Equiv.Perm.mul_apply, hfix k h1 h2]
  rw [hM arg σ τ (fun _ _ _ => ⟨rfl, rfl, rfl⟩),
    hM arg (σ * Equiv.swap i.castSucc i.succ) τ (fun k h1 h2 => ⟨rfl, (hc k h1 h2).2.1, rfl⟩),
    hM arg σ (τ * Equiv.swap i.castSucc i.succ) (fun k h1 h2 => ⟨rfl, rfl, (hc k h1 h2).2.2⟩),
    hM arg (σ * Equiv.swap i.castSucc i.succ) (τ * Equiv.swap i.castSucc i.succ)
      (fun k h1 h2 => ⟨rfl, (hc k h1 h2).2.1, (hc k h1 h2).2.2⟩),
    hM (arg ∘ Equiv.swap i.castSucc i.succ) σ τ (fun k h1 h2 => ⟨(hc k h1 h2).1, rfl, rfl⟩),
    hM (arg ∘ Equiv.swap i.castSucc i.succ) (σ * Equiv.swap i.castSucc i.succ) τ
      (fun k h1 h2 => ⟨(hc k h1 h2).1, (hc k h1 h2).2.1, rfl⟩),
    hM (arg ∘ Equiv.swap i.castSucc i.succ) σ (τ * Equiv.swap i.castSucc i.succ)
      (fun k h1 h2 => ⟨(hc k h1 h2).1, rfl, (hc k h1 h2).2.2⟩),
    hM (arg ∘ Equiv.swap i.castSucc i.succ) (σ * Equiv.swap i.castSucc i.succ)
      (τ * Equiv.swap i.castSucc i.succ) hc]
  have e0 : (⟨i, by omega⟩ : Fin (m + 1)) = i.castSucc := Fin.ext rfl
  have e1 : (⟨i + 1, hi⟩ : Fin (m + 1)) = i.succ := Fin.ext rfl
  simp only [e0, e1, Equiv.Perm.mul_apply, Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have hfac : ∀ L R a1 a2 a3 a4 : A, L * a1 * R - L * a2 * R - L * a3 * R + L * a4 * R = L * (a1 - a2 - a3 + a4) * R :=
    fun _ _ _ _ _ _ => by noncomm_ring
  rw [hfac, hfac, term_two_by_two_exchange]

private lemma antisymmetrizedProduct_adjacent_swap {A : Type*} [Ring A] [Algebra ℂ A] {m : ℕ}
    (E : Fin (m + 1) → Fin (m + 1) → A) (i : Fin m) (arg : Fin (m + 1) → ℂ) :
    doublyAntisymmetrizedProduct E (arg ∘ Equiv.swap i.castSucc i.succ) = doublyAntisymmetrizedProduct E arg := by
  have hne : i.castSucc ≠ i.succ := (Fin.castSucc_lt_succ (i := i)).ne
  have key := orderedProduct_adjacent_swap_identity E i arg
  generalize hs : Equiv.swap i.castSucc i.succ = s at key ⊢
  have hsg : Equiv.Perm.sign s = -1 := by rw [← hs]; exact Equiv.Perm.sign_swap hne
  have hre : ∀ F : Equiv.Perm (Fin (m + 1)) → A,
      ∑ σ, ((Equiv.Perm.sign σ : ℤ) : A) * F (σ * s) = -∑ σ, ((Equiv.Perm.sign σ : ℤ) : A) * F σ := by
    intro F
    rw [← Equiv.sum_comp (Equiv.mulRight s) (fun σ => ((Equiv.Perm.sign σ : ℤ) : A) * F σ)]
    simp [Equiv.Perm.sign_mul, hsg]
  have q1 : ∀ a : Fin (m + 1) → ℂ, ∑ τ, ∑ σ, ((Equiv.Perm.sign τ : ℤ) : A) *
      (((Equiv.Perm.sign σ : ℤ) : A) * orderedTermProduct E a (σ * s) τ) = -doublyAntisymmetrizedProduct E a := by
    intro a; simp only [doublyAntisymmetrizedProduct, ← Finset.mul_sum]; rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun τ _ => by rw [hre (fun σ => orderedTermProduct E a σ τ), mul_neg]
  have q2 : ∀ a : Fin (m + 1) → ℂ, ∑ τ, ∑ σ, ((Equiv.Perm.sign τ : ℤ) : A) *
      (((Equiv.Perm.sign σ : ℤ) : A) * orderedTermProduct E a σ (τ * s)) = -doublyAntisymmetrizedProduct E a := by
    intro a; simp only [doublyAntisymmetrizedProduct, ← Finset.mul_sum]
    exact hre (fun τ => ∑ σ, ((Equiv.Perm.sign σ : ℤ) : A) * orderedTermProduct E a σ τ)
  have q3 : ∀ a : Fin (m + 1) → ℂ, ∑ τ, ∑ σ, ((Equiv.Perm.sign τ : ℤ) : A) *
      (((Equiv.Perm.sign σ : ℤ) : A) * orderedTermProduct E a (σ * s) (τ * s)) = doublyAntisymmetrizedProduct E a := by
    intro a; simp only [← Finset.mul_sum]
    have h1 : ∀ τ, ∑ σ, ((Equiv.Perm.sign σ : ℤ) : A) * orderedTermProduct E a (σ * s) (τ * s) =
        -∑ σ, ((Equiv.Perm.sign σ : ℤ) : A) * orderedTermProduct E a σ (τ * s) :=
      fun τ => hre (fun σ => orderedTermProduct E a σ (τ * s))
    simp only [h1, mul_neg, Finset.sum_neg_distrib]
    rw [hre (fun τ => ∑ σ, ((Equiv.Perm.sign σ : ℤ) : A) * orderedTermProduct E a σ τ), neg_neg]
    simp only [doublyAntisymmetrizedProduct, Finset.mul_sum]
  have T_eq : ∀ a : Fin (m + 1) → ℂ, ∑ τ, ∑ σ, ((Equiv.Perm.sign τ : ℤ) : A) *
      (((Equiv.Perm.sign σ : ℤ) : A) * (orderedTermProduct E a σ τ - orderedTermProduct E a (σ * s) τ -
        orderedTermProduct E a σ (τ * s) + orderedTermProduct E a (σ * s) (τ * s))) =
      4 • doublyAntisymmetrizedProduct E a := by
    intro a; simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [q1 a, q2 a, q3 a]; simp only [doublyAntisymmetrizedProduct]; abel
  have h4 : (4 : ℂ) • doublyAntisymmetrizedProduct E arg = (4 : ℂ) • doublyAntisymmetrizedProduct E (arg ∘ s) := by
    rw [show (4 : ℂ) = ((4 : ℕ) : ℂ) by norm_num, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul,
      ← T_eq arg, ← T_eq (arg ∘ s)]
    exact Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun σ _ => by rw [key σ τ]
  exact (smul_right_injective A (by norm_num : (4 : ℂ) ≠ 0) h4).symm

theorem antisymmetrizedProduct_perm_invariant {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
    (E : Fin n → Fin n → A) (π : Equiv.Perm (Fin n)) (arg : Fin n → ℂ) :
    doublyAntisymmetrizedProduct E (arg ∘ π) = doublyAntisymmetrizedProduct E arg := by
  cases n with
  | zero => rw [show arg ∘ π = arg from funext fun k => k.elim0]
  | succ m =>
    have hπ : π ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial
    revert arg
    induction hπ using Submonoid.closure_induction with
    | mem _ hx => obtain ⟨i, rfl⟩ := hx; exact antisymmetrizedProduct_adjacent_swap E i
    | one => intro _; rfl
    | mul x y _ _ hx hy => intro arg; show doublyAntisymmetrizedProduct E ((arg ∘ x) ∘ y) = _; rw [hy (arg ∘ x), hx arg]

theorem antisymmetrizedProduct_eq_factorial_smul_qdet {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
    (E : Fin n → Fin n → A) (hE : GlRel E) (u : ℂ) :
    doublyAntisymmetrizedProduct E (fun k => u - (k : ℂ)) = (n.factorial : ℂ) • qdet E u := by
  simp only [doublyAntisymmetrizedProduct, ← Finset.mul_sum]
  have hin : ∀ τ : Equiv.Perm (Fin n), ∑ σ, ((Equiv.Perm.sign σ : ℤ) : A) *
      orderedTermProduct E (fun k => u - (k : ℂ)) σ τ = qminor E id (id ∘ τ) u := fun _ => rfl
  have hcol : ∀ τ : Equiv.Perm (Fin n), qminor E id (id ∘ τ) u = ((Equiv.Perm.sign τ : ℤ) : A) * qdet E u := fun τ => by
    rw [qminor_comp_perm E hE id u τ id, Algebra.smul_def, map_intCast]; rfl
  have hsq : ∀ τ : Equiv.Perm (Fin n), ((Equiv.Perm.sign τ : ℤ) : A) *
      (((Equiv.Perm.sign τ : ℤ) : A) * qdet E u) = qdet E u := fun τ => by
    rw [← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one, one_mul]
  simp only [hin, hcol, hsq, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℂ]

private lemma orderedTermProduct_neg_transpose {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
    (E : Fin n → Fin n → A) (arg : Fin n → ℂ) (σ τ : Equiv.Perm (Fin n)) :
    orderedTermProduct (fun a b => -E b a) arg σ τ =
      (-1) ^ n * orderedTermProduct E (fun k => -arg k) τ σ := by
  have htm : ∀ y a b, capelliTm (fun a b => -E b a) y a b = -capelliTm E (-y) b a := fun y a b => by
    simp only [capelliTm]; by_cases h : a = b
    · subst h; rw [if_pos rfl, if_pos rfl, map_neg]; abel
    · rw [if_neg h, if_neg (Ne.symm h)]; simp
  simp only [orderedTermProduct]
  have h : (fun k : Fin n => capelliTm (fun a b => -E b a) (arg k) (σ k) (τ k)) =
      fun k => -(capelliTm E (-arg k) (τ k) (σ k)) := funext fun k => htm _ _ _
  rw [h, show (List.ofFn fun k => -(capelliTm E (-arg k) (τ k) (σ k))) =
      (List.ofFn fun k => capelliTm E (-arg k) (τ k) (σ k)).map Neg.neg by rw [List.map_ofFn]; rfl,
    List.prod_map_neg, List.length_ofFn]

theorem quantumDet_neg_transpose {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
    (E : Fin n → Fin n → A) (hE : GlRel E) (x : ℂ) :
    qdet (fun a b => -E b a) x = ((-1 : ℂ) ^ n) • qdet E ((n : ℂ) - 1 - x) := by
  have hE' : GlRel (fun a b => -E b a) := fun a b c d => by
    have h := hE b a d c
    simp only [neg_mul_neg]; rw [h]
    by_cases h1 : a = d <;> by_cases h2 : c = b
    · subst h1 h2; simp; abel
    · subst h1; simp [h2, Ne.symm h2]
    · subst h2; simp [h1, Ne.symm h1]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  have h1 := antisymmetrizedProduct_eq_factorial_smul_qdet (fun a b => -E b a) hE' x
  have h2 : doublyAntisymmetrizedProduct (fun a b => -E b a) (fun k => x - (k : ℂ)) =
      (-1) ^ n * doublyAntisymmetrizedProduct E (fun k => -(x - (k : ℂ))) := by
    simp only [doublyAntisymmetrizedProduct, orderedTermProduct_neg_transpose]
    rw [Finset.sum_comm, Finset.mul_sum]; refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun κ _ => ?_
    rw [show ((-1 : A)) ^ n = (((-1 : ℤ) ^ n : ℤ) : A) by push_cast; rfl]
    simp only [← zsmul_eq_mul, smul_smul]; congr 1; ring
  have h3 : (fun k : Fin n => -(x - (k : ℂ))) = (fun k : Fin n => ((n : ℂ) - 1 - x) - (k : ℂ)) ∘ Fin.revPerm := by
    funext k; simp only [Function.comp_apply, Fin.revPerm_apply, Fin.val_rev]
    rw [Nat.cast_sub (Nat.succ_le_of_lt k.isLt)]; push_cast; ring
  have h4 := antisymmetrizedProduct_perm_invariant E Fin.revPerm (fun k : Fin n => ((n : ℂ) - 1 - x) - (k : ℂ))
  have h5 := antisymmetrizedProduct_eq_factorial_smul_qdet E hE ((n : ℂ) - 1 - x)
  refine smul_right_injective A (by exact_mod_cast n.factorial_ne_zero : ((n.factorial : ℕ) : ℂ) ≠ 0) ?_
  change ((n.factorial : ℕ) : ℂ) • qdet (fun a b => -E b a) x =
    ((n.factorial : ℕ) : ℂ) • (((-1 : ℂ) ^ n) • qdet E ((n : ℂ) - 1 - x))
  rw [← h1, h2, h3, h4, h5, smul_comm, Algebra.smul_def ((-1 : ℂ) ^ n)]
  simp

private lemma eval_prod_add (m : Multiset ℂ) (u : ℂ) :
    (((m.map (fun x : ℂ ↦ -x)).map (fun x : ℂ ↦ Polynomial.X - Polynomial.C x)).prod).eval u =
      (m.map (fun x : ℂ ↦ u + x)).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp only [Multiset.map_cons, Multiset.prod_cons, Polynomial.eval_mul, ih,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]; ring

theorem msetSep (m m' : Multiset ℂ)
    (h : ∀ u : ℂ, (m.map (u + ·)).prod = (m'.map (u + ·)).prod) : m = m' := by
  have hp : ((m.map (fun x : ℂ ↦ -x)).map (fun x : ℂ ↦ Polynomial.X - Polynomial.C x)).prod =
      ((m'.map (fun x : ℂ ↦ -x)).map (fun x : ℂ ↦ Polynomial.X - Polynomial.C x)).prod := by
    apply Polynomial.funext; intro u; rw [eval_prod_add, eval_prod_add, h u]
  have hr := congrArg Polynomial.roots hp
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at hr
  exact Multiset.map_injective neg_injective hr

theorem expSq {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ) (h : N * N = 0) :
    NormedSpace.exp N = (1 : Matrix (Fin n) (Fin n) ℂ) + N := by
  have hz : ∀ k : ℕ, k ∉ Finset.range 2 → ((k.factorial : ℂ)⁻¹) • N ^ k = 0 := by
    intro k hk
    have hk2 : 2 ≤ k := by rw [Finset.mem_range] at hk; omega
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk2
    rw [pow_add, pow_two, h, zero_mul, smul_zero]
  rw [NormedSpace.exp_eq_tsum ℂ]
  beta_reduce
  rw [tsum_eq_sum hz]
  simp [Finset.sum_range_succ]

end QuantumDetHelpers

/-! ## Section 2: Kronecker Product & Weyl Character Regularity (`WeylCharacterRegularity`) -/

section WeylCharacterRegularity

section Kron

variable {T κ : Type*} [Fintype T] [DecidableEq T] [Fintype κ] [DecidableEq κ]

def piK : (T → Matrix κ κ ℂ) →* Matrix (T → κ) (T → κ) ℂ where
  toFun M := Matrix.of fun f g => ∏ t, M t (f t) (g t)
  map_one' := by
    ext f g; simp only [Matrix.of_apply, Pi.one_apply, Matrix.one_apply]
    by_cases h : f = g
    · subst h; simp
    · obtain ⟨t, ht⟩ := Function.ne_iff.mp h
      rw [if_neg h]; exact Finset.prod_eq_zero (Finset.mem_univ t) (if_neg ht)
  map_mul' M N := by
    ext f g; simp only [Matrix.of_apply, Pi.mul_apply, Matrix.mul_apply]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    exact Finset.sum_congr rfl fun _ _ => Finset.prod_mul_distrib

theorem piK_apply (A : T → Matrix κ κ ℂ) (f g : T → κ) : piK A f g = ∏ t, A t (f t) (g t) := rfl

theorem piK_mulSingle (t : T) (A : Matrix κ κ ℂ) (f g : T → κ) :
    piK (Pi.mulSingle t A) f g =
      A (f t) (g t) * ∏ s ∈ Finset.univ.erase t, (1 : Matrix κ κ ℂ) (f s) (g s) := by
  rw [piK_apply, ← Finset.mul_prod_erase _ _ (Finset.mem_univ t), Pi.mulSingle_eq_same]
  congr 1
  exact Finset.prod_congr rfl fun s hs => by rw [Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hs)]

def kronAt (t : T) : Matrix κ κ ℂ →ₐ[ℂ] Matrix (T → κ) (T → κ) ℂ :=
  AlgHom.ofLinearMap
    { toFun := fun A => piK (Pi.mulSingle t A)
      map_add' := fun A B => by ext f g; simp [piK_mulSingle, add_mul]
      map_smul' := fun c A => by ext f g; simp [piK_mulSingle, mul_assoc] }
    (by simp) (fun A B => by simp [Pi.mulSingle_mul])

theorem kronAt_apply (t : T) (A : Matrix κ κ ℂ) (f g : T → κ) :
    kronAt t A f g =
      A (f t) (g t) * ∏ s ∈ Finset.univ.erase t, (1 : Matrix κ κ ℂ) (f s) (g s) :=
  piK_mulSingle t A f g

end Kron

section AlgRepDef

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

variable (E a) in
def regFun : Subalgebra ℂ (GL (Fin a) (Cinf E) → ℂ) :=
  Algebra.adjoin ℂ
    ({f | ∃ τ i j, f = fun y => coord τ (y.val i j)} ∪ {f | ∃ τ, f = fun y => (coord τ y.val.det)⁻¹})

variable (E a) in
structure AlgRep where
  d : ℕ
  mat : GL (Fin a) (Cinf E) →* Matrix (Fin d) (Fin d) ℂ
  reg : ∀ i j, (fun y => mat y i j) ∈ regFun E a
  pos : 0 < d
  irred : ∀ W : Submodule ℂ (Fin d → ℂ), (∀ y, ∀ v ∈ W, mat y *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤

open Classical in
def extGL (f : GL (Fin a) (Cinf E) → ℂ) (x : Lie E a) : ℂ :=
  if h : IsUnit (Matrix.of x) then f h.unit else 0

omit [NumberField E] in
theorem extGL_val (f : GL (Fin a) (Cinf E) → ℂ) (y : GL (Fin a) (Cinf E)) :
    extGL f (toL y.val) = f y := by
  have h : IsUnit (Matrix.of (toL y.val)) := y.isUnit
  have e : h.unit = y := Units.ext h.unit_spec
  rw [extGL, dif_pos h, e]

theorem extGL_eventuallyEq {f : GL (Fin a) (Cinf E) → ℂ} {F : Lie E a → ℂ}
    (h : ∀ y, f y = F (toL y.val)) {x : Lie E a} (hx : x ∈ invSet E a) :
    extGL f =ᶠ[𝓝 x] F :=
  Filter.eventually_of_mem (isOpen_invSet.mem_nhds hx) fun z hz => by
    obtain ⟨u, hu⟩ := hz
    have e : z = toL u.val := hu.symm
    rw [e, extGL_val, h]

def coordL (τ : E →+* ℂ) : Cinf E →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := coord τ
      map_add' := map_add _
      map_smul' := fun c z => coord_smul τ c z }

@[simp] theorem coordL_apply (τ : E →+* ℂ) (z : Cinf E) : coordL τ z = coord τ z := rfl

theorem differentiableAt_extGL {f : GL (Fin a) (Cinf E) → ℂ} (hf : f ∈ regFun E a)
    {x : Lie E a} (hx : x ∈ invSet E a) : DifferentiableAt ℝ (extGL f) x := by
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    rcases hf with ⟨τ, i, j, rfl⟩ | ⟨τ, rfl⟩
    · refine DifferentiableAt.congr_of_eventuallyEq (f := fun x => coordL τ (x i j)) (by fun_prop)
        (extGL_eventuallyEq (F := fun x => coordL τ (x i j)) (fun _ => rfl) hx)
    · refine DifferentiableAt.congr_of_eventuallyEq (f := fun x => (coordL τ (Matrix.of x).det)⁻¹) ?_
        (extGL_eventuallyEq (F := fun x => (coordL τ (Matrix.of x).det)⁻¹) (fun _ => rfl) hx)
      exact ((coordL τ).differentiableAt.comp x (contDiff_det.differentiable (by simp) x)).inv
        (((Matrix.isUnit_iff_isUnit_det _).1 hx).map (coord τ)).ne_zero
  | algebraMap c =>
    exact (differentiableAt_const c).congr_of_eventuallyEq (extGL_eventuallyEq (F := fun _ => c) (fun _ => rfl) hx)
  | add f g _ _ h1 h2 =>
    exact (h1.add h2).congr_of_eventuallyEq (extGL_eventuallyEq (fun y => by simp [extGL_val]) hx)
  | mul f g _ _ h1 h2 =>
    exact (h1.mul h2).congr_of_eventuallyEq (extGL_eventuallyEq (fun y => by simp [extGL_val]) hx)

namespace AlgRep

def dmat (Ξ : AlgRep E a) : Lie E a →ₗ[ℝ] Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ where
  toFun X := Matrix.of fun i j => fderiv ℝ (extGL fun y => Ξ.mat y i j) (oneL E a) X
  map_add' X Y := by ext i j; simp
  map_smul' c X := by ext i j; simp

theorem hasDerivAt_curve (Ξ : AlgRep E a) (c : ℝ → GL (Fin a) (Cinf E)) (X : Lie E a) (h0 : c 0 = 1)
    (hc : HasDerivAt (fun t => toL (c t).val) X 0) (i j : Fin Ξ.d) :
    HasDerivAt (fun t => Ξ.mat (c t) i j) (Ξ.dmat X i j) 0 := by
  have h : HasFDerivAt (extGL fun y => Ξ.mat y i j) (fderiv ℝ (extGL fun y => Ξ.mat y i j) (oneL E a))
      (toL (c 0).val) := by
    rw [h0]; exact (differentiableAt_extGL (Ξ.reg i j) isUnit_one).hasFDerivAt
  have h2 := h.comp_hasDerivAt (0 : ℝ) hc
  simp only [Function.comp_def, extGL_val] at h2
  exact h2

theorem mat_mul_dmat (Ξ : AlgRep E a) (y : GL (Fin a) (Cinf E)) (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    Ξ.mat y * Ξ.dmat (toL X) = Ξ.dmat (toL (y.val * X * (y⁻¹).val)) * Ξ.mat y := by
  classical
  let T : Lie E a →L[ℝ] Lie E a := (rmul (toL (y⁻¹).val)).comp (lmul (toL y.val))
  have hT : T (oneL E a) = oneL E a := (congrArg (· * (y⁻¹).val) (mul_one y.val)).trans y.mul_inv
  have hd := fun i j => (differentiableAt_extGL (Ξ.reg i j) (x := oneL E a) isUnit_one).hasFDerivAt
  ext i j
  have h1 := HasFDerivAt.fun_sum (u := Finset.univ) fun l _ => (hd l j).const_mul (Ξ.mat y i l)
  have h2 := HasFDerivAt.fun_sum (u := Finset.univ) fun l _ =>
    (HasFDerivAt.comp (oneL E a) (hT.symm ▸ hd i l) T.hasFDerivAt).mul_const (Ξ.mat y l j)
  have h3 := h1.unique (h2.congr_of_eventuallyEq (Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one)
    fun z hz => by
      obtain ⟨u, hu⟩ := hz
      have e : z = toL u.val := hu.symm
      have e2 : T (toL u.val) = toL (y * u * y⁻¹).val := rfl
      simp only [e, Function.comp_apply, e2, extGL_val]
      rw [← Matrix.mul_apply, ← Matrix.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel_right]))
  have h4 := congrArg (fun D : Lie E a →L[ℝ] ℂ => D (toL X)) h3
  simp only [_root_.sum_apply, _root_.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul, hT] at h4
  rw [Matrix.mul_apply, Matrix.mul_apply]
  exact h4.trans (Finset.sum_congr rfl fun _ _ => mul_comm _ _)

variable (E a) in
def triv : AlgRep E a where
  d := 1
  mat := 1
  reg i j := Subalgebra.algebraMap_mem _ ((1 : Matrix (Fin 1) (Fin 1) ℂ) i j)
  pos := one_pos
  irred W _ := by
    refine or_iff_not_imp_left.2 fun h => eq_top_iff.2 fun w _ => ?_
    obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 h
    have hv0 : v 0 ≠ 0 := fun h' => h0 (funext fun i => Fin.fin_one_eq_zero i ▸ h')
    convert W.smul_mem (w 0 / v 0) hv
    ext i; fin_cases i; simp [div_mul_cancel₀ _ hv0]

theorem dmat_triv (X : Lie E a) : (triv E a).dmat X = 0 := by
  ext i j
  have h := extGL_eventuallyEq (f := fun y => (triv E a).mat y i j)
    (F := fun _ => (1 : Matrix (Fin 1) (Fin 1) ℂ) i j) (fun _ => rfl) (x := oneL E a) isUnit_one
  change fderiv ℝ _ _ X = 0; rw [h.fderiv_eq]; simp

omit [NumberField E] in
theorem exists_section (τ : E →+* ℂ) : ∃ s : ℂ →+* Cinf E, ∀ z, coord τ (s z) = z := by
  unfold coord; split_ifs
  · exact ⟨Pi.constRingHom _ _, fun _ => rfl⟩
  · exact ⟨(Pi.constRingHom _ _).comp (starRingEnd ℂ), fun z => by simp⟩

def std (τ : E →+* ℂ) (ha : 0 < a) : AlgRep E a where
  d := a
  mat := ((coord τ).mapMatrix.toMonoidHom).comp (Units.coeHom _)
  reg i j := Algebra.subset_adjoin (Or.inl ⟨τ, i, j, rfl⟩)
  pos := ha
  irred W hW := by
    obtain ⟨s, hs⟩ := exists_section τ
    have h1 : ∀ M : Matrix (Fin a) (Fin a) ℂ, IsUnit M → ∀ v ∈ W, M *ᵥ v ∈ W := by
      rintro _ ⟨g, rfl⟩ v hv
      convert hW (GeneralLinearGroup.map s g) v hv using 2
      ext i j; exact (hs _).symm
    have h2 : ∀ M : Matrix (Fin a) (Fin a) ℂ, ∀ v ∈ W, M *ᵥ v ∈ W := by
      intro M v hv
      obtain ⟨c, hc⟩ := (Matrix.finite_spectrum M).infinite_compl.nonempty
      have h3 := h1 _ (spectrum.notMem_iff.1 hc) v hv
      rw [Matrix.sub_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec] at h3
      simpa using W.sub_mem (W.smul_mem c hv) h3
    refine or_iff_not_imp_left.2 fun h => eq_top_iff.2 fun w _ => ?_
    obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 h
    obtain ⟨j, hj⟩ := Function.ne_iff.1 h0
    have hj' : v j ≠ 0 := hj
    convert h2 (Matrix.of fun i k => if k = j then w i / v j else 0) v hv
    ext i; simp [Matrix.mulVec, dotProduct, hj']

theorem dmat_std (τ : E →+* ℂ) (ha : 0 < a) (X : Lie E a) :
    (std τ ha).dmat X = (Matrix.of X).map (coord τ) := by
  ext i j
  have h := extGL_eventuallyEq (f := fun y => (std τ ha).mat y i j) (F := fun x => coordL τ (x i j))
    (fun _ => rfl) (x := oneL E a) isUnit_one
  change fderiv ℝ _ _ X = _
  rw [h.fderiv_eq]
  exact congrArg (fun L : Lie E a →L[ℝ] ℂ => L X) (((coordL τ).comp ((ContinuousLinearMap.proj j).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin a => Fin a → Cinf E) i))).fderiv)

end AlgRep

omit [NumberField E] in
theorem atEmb_mul (τ : E →+* ℂ) (z z' : ℂ) : atEmb τ z * atEmb τ z' = atEmb τ (z * z') := by
  classical
  unfold atEmb; rw [← Pi.single_mul]; split_ifs <;> simp

omit [NumberField E] in
theorem atEmb_conj [IsTotallyComplex E] (τ : E →+* ℂ) (z : ℂ) :
    atEmb (ComplexEmbedding.conjugate τ) z = atEmb τ (starRingEnd ℂ z) := by
  have hne : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
    InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 h))
  unfold atEmb; simp only [InfinitePlace.mk_conjugate_eq]
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · rw [if_pos h, if_neg (by rw [InfinitePlace.mk_conjugate_eq, h]; exact hne.symm)]
  · rw [if_pos (by rw [InfinitePlace.mk_conjugate_eq, h]), if_neg (by rw [h]; exact hne)]; simp

omit [NumberField E] in
theorem atEmb_mul_of_ne {τ τ' : E →+* ℂ} (h : InfinitePlace.mk τ ≠ InfinitePlace.mk τ') (z z' : ℂ) :
    atEmb τ z * atEmb τ' z' = 0 := by
  classical
  funext w; unfold atEmb
  by_cases hw : w = InfinitePlace.mk τ
  · subst hw; simp [Pi.single_eq_of_ne h]
  · simp [Pi.single_eq_of_ne hw]

omit [NumberField E] in
theorem mul_atEmb (τ : E →+* ℂ) (x : Cinf E) (z : ℂ) : x * atEmb τ z = atEmb τ (coord τ x * z) := by
  classical
  funext w; unfold atEmb coord
  by_cases hw : w = InfinitePlace.mk τ
  · subst hw; split_ifs <;> simp
  · simp [Pi.single_eq_of_ne hw]

def AlgInfChar (Ξ : AlgRep E a) (τ : E →+* ℂ) (m : Multiset ℂ) : Prop :=
  Multiset.card m = a ∧
    ∀ u : ℂ, qdet (fun i j => (1 / 2 : ℂ) • (Ξ.dmat (toL (Matrix.single i j (atEmb τ 1))) -
      Complex.I • Ξ.dmat (toL (Matrix.single i j (atEmb τ Complex.I))))) (u + ((a : ℂ) - 1) / 2) =
      (m.map (u + ·)).prod • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)

def IsReg {ι κ : Type*} (M : GL (Fin a) (Cinf E) → Matrix ι κ ℂ) : Prop :=
  ∀ i j, (fun y => M y i j) ∈ regFun E a

def dOf {ι κ : Type*} (M : GL (Fin a) (Cinf E) → Matrix ι κ ℂ) (X : Lie E a) : Matrix ι κ ℂ :=
  Matrix.of fun i j => fderiv ℝ (extGL fun y => M y i j) (oneL E a) X

def eOf {ι κ : Type*} (M : GL (Fin a) (Cinf E) → Matrix ι κ ℂ) (τ : E →+* ℂ) (i j : Fin a) :
    Matrix ι κ ℂ :=
  (1 / 2 : ℂ) • (dOf M (toL (Matrix.single i j (atEmb τ 1))) -
    Complex.I • dOf M (toL (Matrix.single i j (atEmb τ Complex.I))))

omit [NumberField E] in
theorem dmat_eq (Ξ : AlgRep E a) (X : Lie E a) : Ξ.dmat X = dOf Ξ.mat X := rfl

omit [NumberField E] in
theorem algInfChar_iff (Ξ : AlgRep E a) (τ : E →+* ℂ) (m : Multiset ℂ) :
    AlgInfChar Ξ τ m ↔ Multiset.card m = a ∧
      ∀ u : ℂ, qdet (eOf Ξ.mat τ) (u + ((a : ℂ) - 1) / 2) =
        (m.map (u + ·)).prod • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) :=
  Iff.rfl

omit [NumberField E] in
theorem extGL_one (f : GL (Fin a) (Cinf E) → ℂ) : extGL f (oneL E a) = f 1 := extGL_val f 1

theorem IsReg.diff {ι κ : Type*} {M : GL (Fin a) (Cinf E) → Matrix ι κ ℂ} (h : IsReg M)
    (i : ι) (j : κ) :
    HasFDerivAt (extGL fun y => M y i j) (fderiv ℝ (extGL fun y => M y i j) (oneL E a)) (oneL E a) :=
  (differentiableAt_extGL (h i j) (x := oneL E a) isUnit_one).hasFDerivAt

omit [NumberField E] in
theorem isReg_conj {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ]
    {M : GL (Fin a) (Cinf E) → Matrix ι κ ℂ} (h : IsReg M)
    (B : Matrix ι' ι ℂ) (A : Matrix κ κ' ℂ) : IsReg fun y => B * M y * A := fun i j => by
  have e : (fun y => (B * M y * A) i j) = ∑ l, ∑ k, (B i k * A l j) • fun y => M y k l := by
    funext y; simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
  rw [e]
  exact Subalgebra.sum_mem _ fun l _ => Subalgebra.sum_mem _ fun k _ => Subalgebra.smul_mem _ (h k l) _

theorem dOf_conj {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ]
    {M : GL (Fin a) (Cinf E) → Matrix ι κ ℂ} (h : IsReg M)
    (B : Matrix ι' ι ℂ) (A : Matrix κ κ' ℂ) (X : Lie E a) :
    dOf (fun y => B * M y * A) X = B * dOf M X * A := by
  ext i j
  have h1 := HasFDerivAt.fun_sum (u := Finset.univ) fun l _ =>
    (HasFDerivAt.fun_sum (u := Finset.univ) fun k _ => (h.diff k l).const_mul (B i k)).mul_const (A l j)
  have h2 := h1.congr_of_eventuallyEq (extGL_eventuallyEq (f := fun y => (B * M y * A) i j)
    (fun y => by simp only [extGL_val, Matrix.mul_apply]) (x := oneL E a) isUnit_one)
  rw [dOf, Matrix.of_apply, h2.fderiv]
  simp [Matrix.mul_apply, dOf, mul_comm]

theorem eOf_conj {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ]
    {M : GL (Fin a) (Cinf E) → Matrix ι κ ℂ} (h : IsReg M)
    (B : Matrix ι' ι ℂ) (A : Matrix κ κ' ℂ) (τ : E →+* ℂ) (i j : Fin a) :
    eOf (fun y => B * M y * A) τ i j = B * eOf M τ i j * A := by
  simp only [eOf, dOf_conj h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]

section PiKD

variable {T κ : Type*} [Fintype T] [DecidableEq T] [Fintype κ] [DecidableEq κ]

omit [NumberField E] in
theorem isReg_piK {M : T → GL (Fin a) (Cinf E) → Matrix κ κ ℂ} (h : ∀ t, IsReg (M t)) :
    IsReg fun y => piK fun t => M t y := fun f g => by
  have e : (fun y => piK (fun t => M t y) f g) = ∏ t, fun y => M t y (f t) (g t) := by
    funext y; simp [piK_apply]
  rw [e]
  exact Subalgebra.prod_mem _ fun t _ => h t _ _

theorem dOf_piK {M : T → GL (Fin a) (Cinf E) → Matrix κ κ ℂ} (h : ∀ t, IsReg (M t))
    (h1 : ∀ t, M t 1 = 1) (X : Lie E a) :
    dOf (fun y => piK fun t => M t y) X = ∑ t, kronAt t (dOf (M t) X) := by
  ext f g
  have h2 := HasFDerivAt.finsetProd (u := Finset.univ) fun t _ => (h t).diff (f t) (g t)
  have h3 := h2.congr_of_eventuallyEq (extGL_eventuallyEq (f := fun y => piK (fun t => M t y) f g)
    (fun y => by simp only [extGL_val, piK_apply]) (x := oneL E a) isUnit_one)
  rw [dOf, Matrix.of_apply, h3.fderiv]
  simp [Matrix.sum_apply, kronAt_apply, dOf, extGL_one, h1, mul_comm]

theorem eOf_piK {M : T → GL (Fin a) (Cinf E) → Matrix κ κ ℂ} (h : ∀ t, IsReg (M t))
    (h1 : ∀ t, M t 1 = 1) (τ : E →+* ℂ) (i j : Fin a) :
    eOf (fun y => piK fun t => M t y) τ i j = ∑ t, kronAt t (eOf (M t) τ i j) := by
  simp only [eOf, dOf_piK h h1, map_smul, map_sub, Finset.smul_sum, ← Finset.sum_sub_distrib]

end PiKD

omit [NumberField E] in
open Classical in
theorem coord_hol [IsTotallyComplex E] (τ τ' : E →+* ℂ) :
    (1 / 2 : ℂ) * (coord τ' (atEmb τ 1) - Complex.I * coord τ' (atEmb τ Complex.I)) =
      if τ' = τ then 1 else 0 := by
  split_ifs with h
  · subst h; rw [coord_atEmb, coord_atEmb, Complex.I_mul_I]; norm_num
  · by_cases hw : InfinitePlace.mk τ' = InfinitePlace.mk τ
    · obtain rfl : ComplexEmbedding.conjugate τ' = τ := (InfinitePlace.mk_eq_iff.1 hw).resolve_left h
      simp [atEmb_conj, coord_atEmb]
    · have h0 : ∀ z, coord τ' (atEmb τ z) = 0 := fun z => by
        have := congrArg (coord τ') (atEmb_mul_of_ne hw 1 z)
        rwa [map_mul, coord_atEmb, one_mul, map_zero] at this
      simp [h0]

theorem fderiv_det_one (X : Lie E a) :
    fderiv ℝ (fun x : Lie E a => (Matrix.of x).det) (oneL E a) X = (Matrix.of X).trace := by
  have hd : HasFDerivAt (fun x : Lie E a => (Matrix.of x).det)
      (fderiv ℝ (fun x : Lie E a => (Matrix.of x).det) (oneL E a)) (oneL E a + (0 : ℝ) • X) := by
    rw [zero_smul, add_zero]
    exact (contDiff_det.differentiable (by simp) _).hasFDerivAt
  have h1 := hd.comp_hasDerivAt (0 : ℝ) (((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (oneL E a))
  rw [one_smul] at h1
  refine h1.unique ?_
  set P := (1 + (Polynomial.X : Polynomial (Cinf E)) • (Matrix.of X).map Polynomial.C).det.divX.divX
  have hr : HasDerivAt (fun t : ℝ => t • (1 : Cinf E)) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (1 : Cinf E)
  have hP : DifferentiableAt ℝ (fun t : ℝ => P.eval (t • (1 : Cinf E))) 0 := by
    simp only [Polynomial.eval_eq_sum_range]; fun_prop
  have h2 := ((hr.const_mul (Matrix.of X).trace).const_add 1).add (hP.hasDerivAt.mul (hr.mul hr))
  simp only [mul_one, zero_smul, Pi.mul_apply, mul_zero, add_zero] at h2
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  have e : Matrix.of (oneL E a + t • X) = 1 + (t • (1 : Cinf E)) • Matrix.of X := by
    rw [smul_assoc, one_smul]; rfl
  change (Matrix.of (oneL E a + t • X)).det = _
  rw [e, Matrix.det_one_add_smul, sq]; rfl

def fac (P : Pre a) (N : ℕ) (τ : E →+* ℂ) : GL (Fin a) (Cinf E) →* Matrix (Fin P.d) (Fin P.d) ℂ where
  toFun y := (coord τ y.val.det)⁻¹ ^ N • P.mat (y.val.map (coord τ))
  map_one' := by simp
  map_mul' y z := by
    simp only [Units.val_mul, Matrix.det_mul, map_mul, Matrix.map_mul, mul_inv, mul_pow, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, mul_comm]

omit [NumberField E] in
theorem fac_apply (P : Pre a) (N : ℕ) (τ : E →+* ℂ) (y : GL (Fin a) (Cinf E)) (i j : Fin P.d) :
    fac P N τ y i j = (coord τ y.val.det)⁻¹ ^ N * P.mat (y.val.map (coord τ)) i j := rfl

omit [NumberField E] in
theorem isReg_fac (P : Pre a) (N : ℕ) (τ : E →+* ℂ) : IsReg (fac P N τ) := fun i j => by
  obtain ⟨p, hp⟩ := P.poly i j
  have h1 : ∀ q : MvPolynomial (Fin a × Fin a) ℂ, (fun y : GL (Fin a) (Cinf E) =>
      MvPolynomial.eval (fun ab => coord τ (y.val ab.1 ab.2)) q) ∈ regFun E a := fun q => by
    induction q using MvPolynomial.induction_on with
    | C c => simp only [MvPolynomial.eval_C]; exact (regFun E a).algebraMap_mem c
    | add p q hp hq => simp only [map_add]; exact (regFun E a).add_mem hp hq
    | mul_X p n hp =>
      simp only [map_mul, MvPolynomial.eval_X]
      exact (regFun E a).mul_mem hp (Algebra.subset_adjoin (Or.inl ⟨τ, n.1, n.2, rfl⟩))
  have h2 : (fun y : GL (Fin a) (Cinf E) => (coord τ y.val.det)⁻¹) ∈ regFun E a :=
    Algebra.subset_adjoin (Or.inr ⟨τ, rfl⟩)
  have h3 := (regFun E a).mul_mem ((regFun E a).pow_mem h2 N) (h1 p)
  convert h3 using 1; funext y; simp [fac_apply, hp]

theorem diff_coef (P : Pre a) (i j : Fin P.d) : Differentiable ℂ (P.coef i j) := coefDiff a P i j

theorem dOf_fac (P : Pre a) (N : ℕ) (τ : E →+* ℂ) (X : Lie E a) :
    dOf (fac P N τ) X = P.D ((Matrix.of X).map (coord τ)) - ((N : ℂ) * coord τ (Matrix.of X).trace) • 1 := by
  ext i j
  let L : Lie E a →L[ℝ] (Fin a → Fin a → ℂ) :=
    ContinuousLinearMap.pi fun k => ContinuousLinearMap.pi fun l => (coordL τ).comp ((ContinuousLinearMap.proj l).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin a => Fin a → Cinf E) k))
  have hL : L (oneL E a) = oneM a := by
    funext k l; exact congrFun (congrFun (Matrix.map_one (coord τ) (map_zero _) (map_one _)) k) l
  have h1 : HasFDerivAt (fun x => P.coef i j (L x))
      (((fderiv ℂ (P.coef i j) (oneM a)).restrictScalars ℝ).comp L) (oneL E a) :=
    HasFDerivAt.comp (g := P.coef i j) (oneL E a)
      (by rw [hL]; exact (diff_coef P i j _).hasFDerivAt.restrictScalars ℝ) L.hasFDerivAt
  have h2 := (coordL τ).hasFDerivAt.comp (oneL E a) (contDiff_det.differentiable (by simp) (oneL E a)).hasFDerivAt
  have h3 := ((hasDerivAt_inv (x := coordL τ (Matrix.of (oneL E a)).det) (by simp)).pow N).hasFDerivAt.restrictScalars ℝ
  have h4 := (h3.comp (oneL E a) h2).mul h1
  have h5 := h4.congr_of_eventuallyEq (extGL_eventuallyEq (f := fun y => fac P N τ y i j)
    (fun _ => rfl) (x := oneL E a) isUnit_one)
  rw [dOf, Matrix.of_apply, h5.fderiv]
  have h6 : P.coef i j (oneM a) = (1 : Matrix _ _ ℂ) i j := congrFun (congrFun (map_one P.mat) i) j
  have h7 : P.D ((Matrix.of X).map (coord τ)) i j = fderiv ℂ (P.coef i j) (oneM a) (L X) := rfl
  simp [hL, h6, h7, fderiv_det_one]; ring

open Classical in
theorem eOf_fac [IsTotallyComplex E] (P : Pre a) (N : ℕ) (τ' τ : E →+* ℂ) (i j : Fin a) :
    eOf (fac P N τ') τ i j =
      if τ' = τ then P.E i j + (if i = j then algebraMap ℂ _ (-(N : ℂ)) else 0) else 0 := by
  have h1 : ∀ x : Cinf E, dOf (fac P N τ') (toL (Matrix.single i j x)) =
      coord τ' x • (P.E i j + (if i = j then algebraMap ℂ _ (-(N : ℂ)) else 0)) := fun x => by
    have e0 : Matrix.of (toL (Matrix.single i j x)) = Matrix.single i j x := rfl
    have e : (Matrix.single i j x).map (coord τ') = coord τ' x • Matrix.single i j 1 := by
      ext k l; simp [Matrix.single_apply, apply_ite (coord τ')]
    rw [dOf_fac, e0, e, map_smul, Pre.E, smul_add, sub_eq_add_neg]
    congr 1
    split_ifs with h
    · subst h; simp [Algebra.algebraMap_eq_smul_one, smul_smul, mul_comm]
    · simp [h]
  rw [eOf, h1, h1, smul_smul, ← sub_smul, smul_smul, coord_hol]
  split_ifs <;> simp

theorem exists_irr {D : ℕ} (hD : 0 < D) (ρ : GL (Fin a) (Cinf E) →* Matrix (Fin D) (Fin D) ℂ)
    (hρ : IsReg ρ) (s : ℂ → ℂ) (hs : ∀ τ u, qdet (eOf ρ τ) u = s u • 1) :
    ∃ Ξ : AlgRep E a, Ξ.d ≤ D ∧ ∀ τ u, qdet (eOf Ξ.mat τ) u = s u • 1 := by
  obtain ⟨d, A, B, ρ', h0, h1, hBA, h2, h3, h4⟩ := irrSub _ D ρ hD
  have hρ' : IsReg ρ' := by
    have := isReg_conj hρ B A
    simpa only [← h2] using this
  refine ⟨⟨d, ρ', hρ', h0, h4⟩, h1, fun τ u => ?_⟩
  have h5 : ∀ i j, eOf ρ τ i j * A = A * eOf ρ' τ i j := fun i j => by
    have e1 := eOf_conj hρ (1 : Matrix (Fin D) (Fin D) ℂ) A τ i j
    have e2 := eOf_conj hρ' A (1 : Matrix (Fin d) (Fin d) ℂ) τ i j
    simp only [Matrix.one_mul, Matrix.mul_one, h3] at e1 e2
    rw [← e1, e2]
  have h6 := congrArg (B * ·) (qdetRect a D d _ _ A h5 u)
  simp only [hs, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, ← Matrix.mul_assoc, hBA] at h6
  exact h6.symm

theorem exists_tens [IsTotallyComplex E] (P : Pre a) (hP : 0 < P.d) (ν : Fin a → ℂ) (hν : P.HasWt ν)
    (N : ℕ) :
    ∃ Ξ : AlgRep E a, Ξ.d ≤ P.d ^ Fintype.card (E →+* ℂ) ∧
      ∀ τ u, qdet (eOf Ξ.mat τ) u = (∏ k : Fin a, (u - N - (k : ℂ) + ν k)) • 1 := by
  classical
  let e : ((E →+* ℂ) → Fin P.d) ≃ Fin (P.d ^ Fintype.card (E →+* ℂ)) :=
    Fintype.equivFinOfCardEq (by simp)
  let r := Matrix.reindexAlgEquiv ℂ ℂ e
  let ρ : GL (Fin a) (Cinf E) →* Matrix _ _ ℂ :=
    (r.toAlgHom.toMonoidHom.comp piK).comp (MonoidHom.pi fun τ : E →+* ℂ => fac P N τ)
  have hr := isReg_piK (fun τ : E →+* ℂ => isReg_fac P N τ)
  refine exists_irr (pow_pos hP _) ρ (fun i j => hr _ _) _ fun τ u => ?_
  have h1 : eOf ρ τ = fun i j => (r.toAlgHom.comp (kronAt τ))
      (P.E i j + (if i = j then algebraMap ℂ _ (-(N : ℂ)) else 0)) := by
    funext i j
    have h2 : eOf ρ τ i j = r (eOf (fun y => piK fun t : E →+* ℂ => fac P N t y) τ i j) := rfl
    rw [h2, eOf_piK (fun τ => isReg_fac P N τ) (fun τ => map_one _), Finset.sum_eq_single τ]
    · rw [eOf_fac, if_pos rfl]; rfl
    · intro t _ ht; rw [eOf_fac, if_neg ht, map_zero]
    · simp
  rw [h1, ← map_qdet, qdet_shift, hν, map_smul, map_one]
  simp only [sub_eq_add_neg]

/-- Concrete realization of any antitone integral highest weight `(ν, N)` as an irreducible
`AlgRep E a` with explicit quantum-determinant infinitesimal character (`existsScalar` + `exists_tens`). -/
theorem exists_algRep_of_antitone [IsTotallyComplex E] (ν : Fin a → ℕ) (hν : Antitone ν)
    (H : ℕ) (hH : ∀ k, ν k ≤ H) (N : ℕ) :
    ∃ Ξ : AlgRep E a, ∀ τ u, qdet (eOf Ξ.mat τ) u = (∏ k : Fin a, (u - N - (k : ℂ) + ν k)) • 1 := by
  obtain ⟨P, hPd, -, hwt⟩ := existsScalar a ν hν H hH
  obtain ⟨Ξ, -, hq⟩ := exists_tens (E := E) P hPd (fun k => (ν k : ℂ)) hwt N
  exact ⟨Ξ, hq⟩

end AlgRepDef

end WeylCharacterRegularity

/-! ## Section 3: Dual Infinitesimal Character Regularity (`DualInfinitesimalCharacterRegular`) -/

section DualInfCharRegular

section Lin

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

private theorem exists_eigenvalue [Nontrivial V] (f : Module.End ℂ V) :
    ∃ c : ℂ, f.HasEigenvalue c := by
  have hint : IsIntegral ℂ f := Algebra.IsIntegral.isIntegral f
  have hdeg : (minpoly ℂ f).degree ≠ 0 := by
    intro h0
    have h1 : minpoly ℂ f = Polynomial.C ((minpoly ℂ f).coeff 0) := Polynomial.eq_C_of_degree_eq_zero h0
    have h2 : (minpoly ℂ f).coeff 0 ≠ 0 := fun hz => minpoly.ne_zero hint (by rw [h1, hz, map_zero])
    have h3 : Polynomial.aeval f (minpoly ℂ f) = 0 := minpoly.aeval ℂ f
    rw [h1, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one] at h3
    exact h2 ((smul_eq_zero.1 h3).resolve_right one_ne_zero)
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_root (minpoly ℂ f) hdeg
  obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.2 hc
  have hq0 : q ≠ 0 := fun hz => minpoly.ne_zero hint (by rw [hq, hz, mul_zero])
  have hqlt : q.degree < (minpoly ℂ f).degree := by
    rw [hq, Polynomial.degree_mul, Polynomial.degree_X_sub_C, Polynomial.degree_eq_natDegree hq0]
    exact_mod_cast (by omega : q.natDegree < 1 + q.natDegree)
  have hfq : Polynomial.aeval f q ≠ 0 := fun hz =>
    not_le.2 hqlt (Polynomial.degree_le_of_dvd (minpoly.dvd ℂ f hz) hq0)
  have ⟨w, hw⟩ : ∃ w : V, Polynomial.aeval f q w ≠ 0 := by
    by_contra h; push Not at h; exact hfq (LinearMap.ext h)
  refine ⟨c, Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 ?_, hw⟩⟩
  have h0 : Polynomial.aeval f (Polynomial.X - Polynomial.C c) (Polynomial.aeval f q w) = 0 := by
    rw [← Module.End.mul_apply, ← map_mul, ← hq, minpoly.aeval, LinearMap.zero_apply]
  simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one,
    LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h0
  exact h0

theorem exists_joint_eigenvector {ι : Type*} (T : ι → Module.End ℂ V) (hT : ∀ i j, T i * T j = T j * T i)
    (W : Submodule ℂ V) (h0 : W ≠ ⊥) (hW : ∀ i, ∀ v ∈ W, T i v ∈ W) :
    ∃ v ∈ W, v ≠ 0 ∧ ∃ c : ι → ℂ, ∀ i, T i v = c i • v := by
  obtain ⟨U, ⟨hU0, hUW, hU⟩, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Submodule ℂ V))
    {U | U ≠ ⊥ ∧ U ≤ W ∧ ∀ i, ∀ v ∈ U, T i v ∈ U} ⟨W, h0, le_rfl, hW⟩
  have : Nontrivial U := Submodule.nontrivial_iff_ne_bot.2 hU0
  have key : ∀ i, ∃ c : ℂ, ∀ v ∈ U, T i v = c • v := by
    intro i
    obtain ⟨c, hc⟩ := exists_eigenvalue ((T i).restrict (hU i))
    obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
    have hx1 : T i x = c • (x : V) := congrArg Subtype.val hx.apply_eq_smul
    refine ⟨c, ?_⟩
    have h1 : U ⊓ Module.End.eigenspace (T i) c = U := by
      refine (inf_le_left.eq_or_lt).resolve_right (hmin _ ⟨?_, inf_le_left.trans hUW, fun j v hv => ⟨hU j v hv.1, ?_⟩⟩)
      · exact (Submodule.ne_bot_iff _).2 ⟨x, ⟨x.2, Module.End.mem_eigenspace_iff.2 hx1⟩,
          fun h => hx.2 (Subtype.ext h)⟩
      · have h2 := Module.End.mem_eigenspace_iff.1 hv.2
        refine Module.End.mem_eigenspace_iff.2 ?_
        rw [← Module.End.mul_apply, hT, Module.End.mul_apply, h2, map_smul]
    intro v hv; rw [← h1] at hv; exact Module.End.mem_eigenspace_iff.1 hv.2
  choose c hc using key
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hU0
  exact ⟨v, hUW hv, hv0, c, fun i => hc i v hv⟩

theorem exists_nat_of_primitive (e f h : Module.End ℂ V) (hef : e * f - f * e = h)
    (hf : h * f - f * h = (-2 : ℂ) • f) (v : V) (μ : ℂ) (hv : v ≠ 0) (he : e v = 0)
    (hh : h v = μ • v) : ∃ m : ℕ, μ = (m : ℂ) := by
  have h1 : ∀ n : ℕ, h ((f ^ n) v) = (μ - 2 * n) • (f ^ n) v := by
    intro n; induction n with
    | zero => simpa using hh
    | succ n ih =>
      have h2 := LinearMap.congr_fun hf ((f ^ n) v)
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, ih, map_smul] at h2
      rw [pow_succ', Module.End.mul_apply, sub_eq_iff_eq_add.1 h2, ← add_smul]; congr 1; push_cast; ring
  have h2 : ∀ n : ℕ, e ((f ^ (n + 1)) v) = ((n + 1) * (μ - n)) • (f ^ n) v := by
    intro n; induction n with
    | zero => simpa [he, hh] using LinearMap.congr_fun hef v
    | succ n ih =>
      have h3 := LinearMap.congr_fun hef ((f ^ (n + 1)) v)
      simp only [LinearMap.sub_apply, Module.End.mul_apply, ih, map_smul, h1] at h3
      rw [pow_succ' f (n + 1), Module.End.mul_apply, sub_eq_iff_eq_add.1 h3,
        ← Module.End.mul_apply f (f ^ n), ← pow_succ', ← add_smul]
      congr 1; push_cast; ring
  by_contra hno; push Not at hno
  have h3 : ∀ n : ℕ, (f ^ n) v ≠ 0 := by
    intro n; induction n with
    | zero => simpa using hv
    | succ n ih =>
      intro h0; have h4 := h2 n; rw [h0, map_zero, eq_comm, smul_eq_zero] at h4
      rcases h4 with h4 | h4
      · rcases mul_eq_zero.1 h4 with h5 | h5
        · exact Nat.cast_add_one_ne_zero n h5
        · exact hno n (sub_eq_zero.1 h5)
      · exact ih h4
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => μ - 2 * (n : ℂ))
    (s := {c | h.HasEigenvalue c}) (fun n m hnm => ?_) (fun n => ?_) (Module.End.finite_hasEigenvalue h)
  · have : (n : ℂ) = m := by linear_combination (-1 / 2 : ℂ) * hnm
    exact Nat.cast_injective this
  · exact Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 (h1 n), h3 n⟩

theorem exists_highest [Nontrivial V] (n : ℕ) (F : Fin n → Fin n → Module.End ℂ V) (hF : GlRel F) :
    ∃ (ν : Fin n → ℂ) (v : V), v ≠ 0 ∧ IsHW F ν v ∧ ∀ i j, i < j → ∃ m : ℕ, ν i - ν j = (m : ℂ) := by
  have hc : ∀ k i j, F k k * F i j - F i j * F k k =
      ((if k = i then (1 : ℂ) else 0) - (if j = k then 1 else 0)) • F i j := by
    intro k i j; rw [hF]; by_cases h1 : k = i <;> by_cases h2 : j = k <;> simp_all
  let H : Module.End ℂ V := ∑ k : Fin n, ((k : ℕ) : ℂ) • F k k
  have hH : ∀ i j, H * F i j = F i j * H + (((i : ℕ) : ℂ) - (j : ℕ)) • F i j := by
    intro i j; rw [← sub_eq_iff_eq_add', Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    simp only [smul_mul_assoc, mul_smul_comm, ← smul_sub, hc, smul_smul, ← Finset.sum_smul]; simp [mul_sub]
  obtain ⟨l, hl, hmin⟩ := Set.exists_min_image {c | H.HasEigenvalue c} Complex.re
    (Module.End.finite_hasEigenvalue H) (exists_eigenvalue H)
  obtain ⟨v, hv, hv0, ν, hν⟩ := exists_joint_eigenvector (fun k => F k k)
    (fun i j => by rw [← sub_eq_zero, hc]; by_cases h : i = j <;> simp [h, eq_comm]) (H.eigenspace l) hl
    (fun k v hv => by rw [Module.End.mem_eigenspace_iff] at hv ⊢; rw [← Module.End.mul_apply, hH]; simp [hv])
  rw [Module.End.mem_eigenspace_iff] at hv
  have hup : ∀ i j, i < j → F i j v = 0 := by
    intro i j hij; by_contra h0
    have h1 : H (F i j v) = (l + (((i : ℕ) : ℂ) - (j : ℕ))) • F i j v := by
      rw [← Module.End.mul_apply, hH]; simp [hv, add_smul]
    have h2 := hmin _ (Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 h1, h0⟩)
    simp at h2; exact absurd hij (not_lt.2 h2)
  refine ⟨ν, v, hv0, ⟨hν, hup⟩, fun i j hij => exists_nat_of_primitive (F i j) (F j i) (F i i - F j j) ?_ ?_ v _ hv0
    (hup i j hij) ?_⟩
  · rw [hF]; simp
  · have h1 := hc i j i; have h2 := hc j j i; simp only [hij.ne, if_false, if_true] at h1 h2
    rw [sub_mul, mul_sub]; linear_combination (norm := module) h1 - h2
  · simp [hν, sub_smul]

end Lin

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def dualS (Ξ : AlgRep E a) (i j : Fin a) (x : Cinf E) : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ :=
  -(Ξ.dmat (toL (Matrix.single i j x)))ᵀ

def dualE (Ξ : AlgRep E a) (τ : E →+* ℂ) (i j : Fin a) : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ :=
  (1 / 2 : ℂ) • (dualS Ξ i j (atEmb τ 1) - Complex.I • dualS Ξ i j (atEmb τ Complex.I))

def HasDualInfChar (Ξ : AlgRep E a) (τ : E →+* ℂ) (m : Multiset ℂ) : Prop :=
  Multiset.card m = a ∧
    ∀ u : ℂ, qdet (dualE Ξ τ) (u + ((a : ℂ) - 1) / 2) =
      (m.map (u + ·)).prod • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)

section Diff

open scoped Matrix.Norms.Operator

def dCL (Ξ : AlgRep E a) : Lie E a →L[ℝ] Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ :=
  LinearMap.toContinuousLinearMap Ξ.dmat

theorem hasDerivAt_mat (Ξ : AlgRep E a) (c : ℝ → GL (Fin a) (Cinf E)) (X : Lie E a) (h0 : c 0 = 1)
    (hc : HasDerivAt (fun t => toL (c t).val) X 0) : HasDerivAt (fun t => Ξ.mat (c t)) (Ξ.dmat X) 0 :=
  (hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => Ξ.hasDerivAt_curve c X h0 hc i j :
    HasDerivAt (fun t => Matrix.of.symm (Ξ.mat (c t))) (Matrix.of.symm (Ξ.dmat X)) 0)

theorem dmat_bracket (Ξ : AlgRep E a) (X Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    Ξ.dmat (toL X) * Ξ.dmat (toL Y) - Ξ.dmat (toL Y) * Ξ.dmat (toL X) = Ξ.dmat (toL (X * Y - Y * X)) := by
  let c : ℝ → GL (Fin a) (Cinf E) := fun t => (Matrix.isUnit_exp (t • X)).unit
  have h0 : c 0 = 1 := Units.ext (by simp [c])
  have hi : ∀ t, ((c t)⁻¹).val = NormedSpace.exp (t • -X) := fun t => by
    rw [smul_neg, Matrix.exp_neg, Matrix.coe_units_inv]; rfl
  have h1 : HasDerivAt (fun t => (c t).val) X 0 := by
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0; rw [zero_smul, NormedSpace.exp_zero, one_mul] at h; exact h
  have h2 : HasDerivAt (fun t => ((c t)⁻¹).val) (-X) 0 := by
    simp only [hi]; have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) 0
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at h; exact h
  have h3 : HasDerivAt (fun t => (c t).val * Y * ((c t)⁻¹).val) (X * Y - Y * X) 0 := by
    have h := (h1.mul_const Y).mul h2
    simp only [h0, inv_one, Units.val_one, mul_one, one_mul, mul_neg, ← sub_eq_add_neg] at h; exact h
  have h4 := hasDerivAt_mat Ξ c (toL X) h0 h1
  have h3' : HasDerivAt (fun t => toL ((c t).val * Y * ((c t)⁻¹).val)) (toL (X * Y - Y * X)) 0 := h3
  have h5 := ((dCL Ξ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h3').mul h4
  have h6 := (h4.mul_const (Ξ.dmat (toL Y))).unique
    (h5.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => Ξ.mat_mul_dmat (c t) Y))
  simp only [Function.comp_apply, h0, inv_one, Units.val_one, mul_one, one_mul, map_one] at h6
  rw [h6]; exact add_sub_cancel_right _ _

theorem isPreconnected_invSet : IsPreconnected (invSet E a) := by
  refine isPreconnected_of_forall (oneL E a) fun y hy => ?_
  let B : Matrix (Fin a) (Fin a) (Cinf E) := Matrix.of y - 1
  let x : ℂ → Lie E a := fun s => toL (1 + s • B)
  let p : InfinitePlace E → Polynomial ℂ := fun w =>
    (1 + (Polynomial.X : Polynomial ℂ) • B.map fun z => Polynomial.C (z w)).det
  have hp : ∀ w s, (p w).eval s = (1 + s • B).det w := by
    intro w s
    refine ((Polynomial.evalRingHom s).map_det _).trans (Eq.trans ?_ ((Pi.evalRingHom (fun _ => ℂ) w).map_det _).symm)
    congr 1; ext i j; by_cases h : i = j <;> simp [h] <;> ring
  have hc : {s | x s ∉ invSet E a}.Countable := by
    refine (Set.countable_iUnion fun w => (Polynomial.finite_setOfPred_isRoot (p := p w) fun h => ?_).countable).mono
      fun s hs => ?_
    · simpa [h] using hp w 0
    · have h : ¬ IsUnit (1 + s • B).det := fun h => hs ((Matrix.isUnit_iff_isUnit_det _).2 h)
      rw [Pi.isUnit_iff, not_forall] at h; obtain ⟨w, hw⟩ := h
      exact Set.mem_iUnion.2 ⟨w, (hp w s).trans (by simpa using hw)⟩
  have hx : Continuous x := (continuous_const.add (continuous_id.smul continuous_const) :
    Continuous fun s : ℂ => toL 1 + s • toL B)
  have e0 : x 0 = oneL E a := by simp [x]
  have e1 : x 1 = y := by simp [x, B]
  refine ⟨x '' {s | x s ∉ invSet E a}ᶜ, ?_, ⟨0, ?_, e0⟩, ⟨1, ?_, e1⟩,
    (hc.isPathConnected_compl_of_one_lt_rank (by simp)).isConnected.isPreconnected.image _ hx.continuousOn⟩
  · rintro _ ⟨s, hs, rfl⟩; exact not_not.1 hs
  · exact not_not.2 (e0 ▸ isUnit_one)
  · exact not_not.2 (e1 ▸ hy)

theorem commute_mat (Ξ : AlgRep E a) (Z : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) (hZ : ∀ X, Z * Ξ.dmat X = Ξ.dmat X * Z)
    (y : GL (Fin a) (Cinf E)) : Z * Ξ.mat y = Ξ.mat y * Z := by
  let M : Lie E a → Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ := fun x => Matrix.of fun i j => extGL (fun y => Ξ.mat y i j) x
  have hM : ∀ u : GL (Fin a) (Cinf E), M (toL u.val) = Ξ.mat u := fun u => by
    ext i j; exact extGL_val (fun y => Ξ.mat y i j) u
  have hU : ∀ x ∈ invSet E a, IsUnit (M x) := by
    rintro x ⟨u, hu⟩; have hx : x = toL u.val := hu.symm; rw [hx, hM]; exact (Group.isUnit u).map Ξ.mat
  have hd : ∀ x ∈ invSet E a, DifferentiableAt ℝ M x := fun x hx =>
    (differentiableAt_pi.2 fun i => differentiableAt_pi.2 fun j => differentiableAt_extGL (Ξ.reg i j) hx :
      DifferentiableAt ℝ (fun x => Matrix.of.symm (M x)) x)
  have h1 : HasFDerivAt M (dCL Ξ) (oneL E a) := by
    have h : HasFDerivAt (fun x => Matrix.of.symm (M x)) _ (oneL E a) :=
      hasFDerivAt_pi.2 fun i => hasFDerivAt_pi.2 fun j =>
        (differentiableAt_extGL (Ξ.reg i j) (x := oneL E a) isUnit_one).hasFDerivAt
    exact h
  let G : Lie E a → Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ := fun x => M x * Z * Ring.inverse (M x)
  have hG : ∀ x ∈ invSet E a, DifferentiableAt ℝ G x := fun x hx =>
    ((hd x hx).mul_const Z).mul ((hd x hx).inverse (hU x hx))
  have hGM : ∀ x ∈ invSet E a, G x * M x = M x * Z := fun x hx => by
    simp only [G]; rw [mul_assoc, Ring.inverse_mul_cancel _ (hU x hx), mul_one]
  have h2 : Set.EqOn (fderiv ℝ G) 0 (invSet E a) := by
    intro x hx; obtain ⟨u, hu⟩ := id hx; obtain rfl : x = toL u.val := hu.symm
    have e1 : lmul (toL (u⁻¹).val) (toL u.val) = oneL E a := u.inv_mul
    have h3 := ((HasFDerivAt.comp (toL u.val) (e1.symm ▸ h1) (lmul (toL (u⁻¹).val)).hasFDerivAt).const_mul
      (Ξ.mat u)).congr_of_eventuallyEq (f₁ := M) (Filter.eventually_of_mem (isOpen_invSet.mem_nhds hx) fun z hz => by
        obtain ⟨v, hv⟩ := hz; obtain rfl : z = toL v.val := hv.symm
        have e2 : lmul (toL (u⁻¹).val) (toL v.val) = toL (u⁻¹ * v).val := rfl
        simp only [Function.comp_apply, e2, hM, ← map_mul, mul_inv_cancel_left])
    have h4 := (h3.mul_const' Z).unique (((hG _ hx).hasFDerivAt.mul' h3).congr_of_eventuallyEq
      (Filter.eventually_of_mem (isOpen_invSet.mem_nhds hx) fun z hz => (hGM z hz).symm))
    ext1 v
    have h5 := congrArg (fun L : Lie E a →L[ℝ] Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ => L v) h4
    have h6 := hGM _ hx; rw [hM] at h6
    have h7 : Ξ.mat u * Ξ.dmat (lmul (toL (u⁻¹).val) v) * Z =
      G (toL u.val) * (Ξ.mat u * Ξ.dmat (lmul (toL (u⁻¹).val) v)) + fderiv ℝ G (toL u.val) v * M (toL u.val) := h5
    rw [← mul_assoc, h6, mul_assoc _ Z, hZ, mul_assoc, left_eq_add] at h7
    exact (hU _ hx).mul_left_eq_zero.1 h7
  have h3 := isOpen_invSet.is_const_of_fderiv_eq_zero isPreconnected_invSet
    (fun x hx => (hG x hx).differentiableWithinAt) h2 (val_mem_invSet y) (val_mem_invSet 1)
  have h4 := hGM _ (val_mem_invSet y); rw [h3, hM] at h4
  simpa only [G, hM, map_one, one_mul, Ring.inverse_one, mul_one] using h4

end Diff

omit [NumberField E] in
def expDiag (δ : Fin a → Cinf E) : GL (Fin a) (Cinf E) :=
  ⟨diagonal fun l w => Complex.exp (δ l w), diagonal fun l w => Complex.exp (-δ l w),
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr; funext l w; simp [← Complex.exp_add],
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr; funext l w; simp [← Complex.exp_add]⟩

omit [NumberField E] in
theorem expDiag_add (δ δ' : Fin a → Cinf E) : expDiag (δ + δ') = expDiag δ * expDiag δ' := Units.ext (by
  change diagonal _ = diagonal _ * diagonal _; rw [diagonal_mul_diagonal]; congr; funext l w; simp [Complex.exp_add])

omit [NumberField E] in
theorem expDiag_zero : expDiag (0 : Fin a → Cinf E) = 1 := Units.ext (by
  change diagonal _ = 1; rw [← diagonal_one]; congr; funext l w; simp)

theorem hasDerivAt_expDiag (δ : Fin a → Cinf E) :
    HasDerivAt (fun t : ℝ => toL (expDiag (t • δ)).val) (toL (diagonal δ)) 0 := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun w => ?_
  by_cases h : i = j
  · subst h; simpa [expDiag] using ((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const (δ i w)).cexp
  · simpa [expDiag, h] using hasDerivAt_const (0 : ℝ) (0 : ℂ)

def expChar (p : ℤ × ℤ) : Multiplicative ℂ →* ℂ where
  toFun z := Complex.exp (p.1 * z.toAdd + p.2 * starRingEnd ℂ z.toAdd)
  map_one' := by simp
  map_mul' x y := by rw [← Complex.exp_add]; congr 1; simp only [toAdd_mul, map_add]; ring

def laurent : Submodule ℂ (Multiplicative ℂ → ℂ) :=
  Submodule.span ℂ ((fun f : Multiplicative ℂ →* ℂ => (f : Multiplicative ℂ → ℂ)) '' Set.range expChar)

theorem expChar_mem (p : ℤ × ℤ) : (expChar p : Multiplicative ℂ → ℂ) ∈ laurent :=
  Submodule.subset_span ⟨_, ⟨p, rfl⟩, rfl⟩

theorem laurent_mul {f g : Multiplicative ℂ → ℂ} (hf : f ∈ laurent) (hg : g ∈ laurent) : f * g ∈ laurent := by
  have h := Submodule.mul_mem_mul hf hg
  rw [laurent, Submodule.span_mul_span] at h
  refine Submodule.span_le.2 ?_ h
  rintro _ ⟨_, ⟨_, ⟨p, rfl⟩, rfl⟩, _, ⟨_, ⟨q, rfl⟩, rfl⟩, rfl⟩
  suffices e : (expChar p : Multiplicative ℂ → ℂ) * expChar q = expChar (p + q) from
    (show (expChar p : Multiplicative ℂ → ℂ) * expChar q ∈ laurent from e ▸ expChar_mem (p + q))
  funext z; simp only [expChar, Pi.mul_apply, MonoidHom.coe_mk, OneHom.coe_mk, ← Complex.exp_add, Prod.fst_add, Prod.snd_add]
  congr 1; push_cast; ring

omit [NumberField E] in
theorem exists_coord_exp (τ τ' : E →+* ℂ) : ∃ p : ℤ × ℤ, ∀ z : Multiplicative ℂ,
    coord τ' (fun w => Complex.exp (atEmb τ z.toAdd w)) = expChar p z := by
  classical
  by_cases hw : InfinitePlace.mk τ' = InfinitePlace.mk τ
  · unfold coord atEmb; rw [hw]; split_ifs
    · exact ⟨(1, 0), fun z => by simp [expChar]⟩
    · exact ⟨(0, 1), fun z => by simp [expChar]⟩
    · exact ⟨(0, 1), fun z => by simp [expChar, ← Complex.exp_conj]⟩
    · exact ⟨(1, 0), fun z => by simp [expChar, ← Complex.exp_conj]⟩
  · refine ⟨0, fun z => ?_⟩; unfold coord atEmb; split_ifs <;> simp [expChar, Pi.single_eq_of_ne hw]

omit [NumberField E] in
def torus (τ : E →+* ℂ) (k : Fin a) (z : ℂ) : GL (Fin a) (Cinf E) := expDiag (Pi.single k (atEmb τ z))

omit [NumberField E] in
theorem reg_torus (τ : E →+* ℂ) (k : Fin a) {f : GL (Fin a) (Cinf E) → ℂ} (hf : f ∈ regFun E a) :
    (fun z : Multiplicative ℂ => f (torus τ k z.toAdd)) ∈ laurent := by
  have h1 : (1 : Multiplicative ℂ → ℂ) ∈ laurent := by convert expChar_mem 0 using 1; funext z; simp [expChar]
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    rcases hf with ⟨τ', i, j, rfl⟩ | ⟨τ', rfl⟩
    · obtain ⟨p, hp⟩ := exists_coord_exp τ τ'
      by_cases h : i = j
      · subst h
        by_cases h : i = k
        · subst h; convert expChar_mem p using 1; funext z; simpa [torus, expDiag] using hp z
        · convert h1 using 1; funext z
          simp only [torus, expDiag, diagonal_apply_eq, Pi.single_eq_of_ne h, Pi.zero_apply, Complex.exp_zero]
          exact map_one (coord τ')
      · convert laurent.zero_mem using 1; funext z; simp [torus, expDiag, h]
    · obtain ⟨p, hp⟩ := exists_coord_exp τ τ'
      convert expChar_mem (-p) using 1; funext z
      have e : (torus τ k z.toAdd).val.det = fun w => Complex.exp (atEmb τ z.toAdd w) := by
        change (diagonal _).det = _
        rw [det_diagonal, Finset.prod_eq_single k]
        · simp
        · intro l _ hl; funext w; simp [hl]
        · simp
      beta_reduce; rw [e, hp]
      simp only [expChar, MonoidHom.coe_mk, OneHom.coe_mk, ← Complex.exp_neg, Prod.fst_neg, Prod.snd_neg]
      congr 1; push_cast; ring
  | algebraMap c => convert laurent.smul_mem c h1 using 1; funext z; simp
  | add f g _ _ h1 h2 => exact laurent.add_mem h1 h2
  | mul f g _ _ h1 h2 => exact laurent_mul h1 h2

theorem eigenvalue_int (Ξ : AlgRep E a) (τ : E →+* ℂ) (k : Fin a) (v : Fin Ξ.d → ℂ) (c : ℂ) (hv : v ≠ 0)
    (h : dualE Ξ τ k k *ᵥ v = c • v) : ∃ n : ℤ, c = (n : ℂ) := by
  have hadd : ∀ z z', torus τ k (z + z') = torus τ k z * torus τ k z' := fun z z' => by
    rw [torus, torus, torus, ← expDiag_add, ← Pi.single_add, atEmb_eq τ (z + z'), atEmb_eq τ z, atEmb_eq τ z']
    congr 2; simp only [Complex.add_re, Complex.add_im, add_smul]; abel
  have hsm : ∀ (t : ℝ) z, torus τ k (t * z) = expDiag (t • Pi.single k (atEmb τ z)) := fun t z => by
    rw [torus, ← Pi.single_smul, atEmb_eq, atEmb_eq τ z]; simp [smul_smul]
  have h0 : torus τ k 0 = 1 := by simpa [expDiag_zero] using hsm 0 0
  have hS : ∀ z x, Commute (Ξ.mat (torus τ k z))ᵀ (dualS Ξ k k x) := fun z x => by
    have h1 := Ξ.mat_mul_dmat (torus τ k z) (Matrix.single k k x)
    have h2 : (torus τ k z).val * Matrix.single k k x = Matrix.single k k x * (torus τ k z).val := by
      rw [← Matrix.diagonal_single]; exact Matrix.commute_diagonal _ _
    rw [h2, Units.mul_inv_cancel_right] at h1
    refine Commute.neg_right ?_
    exact (Matrix.transpose_mul _ _).symm.trans ((congrArg Matrix.transpose h1).symm.trans (Matrix.transpose_mul _ _))
  obtain ⟨u, hu, hu0, χ, hχ⟩ := exists_joint_eigenvector (fun z : ℂ => Matrix.toLin' (Ξ.mat (torus τ k z))ᵀ)
    (fun z z' => by
      rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul,
        ← Matrix.transpose_mul, ← Matrix.transpose_mul, ← map_mul, ← map_mul, ← hadd, ← hadd, add_comm])
    (Module.End.eigenspace (Matrix.toLin' (dualE Ξ τ k k)) c)
    ((Submodule.ne_bot_iff _).2 ⟨v, Module.End.mem_eigenspace_iff.2 h, hv⟩)
    (fun z u hu => by
      have h1 : Commute (Ξ.mat (torus τ k z))ᵀ (dualE Ξ τ k k) :=
        ((hS z _).sub_right ((hS z _).smul_right _)).smul_right _
      rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hu ⊢
      rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← h1.eq, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_smul])
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hu
  simp only [Matrix.toLin'_apply] at hχ
  let ψ : Multiplicative ℂ →* ℂ :=
    { toFun := fun z => χ z.toAdd
      map_one' := smul_left_injective ℂ hu0 (by simpa [h0] using (hχ 0).symm)
      map_mul' := fun z z' => smul_left_injective ℂ hu0 (by
        simp only [toAdd_mul]
        rw [← hχ, hadd, map_mul, Matrix.transpose_mul, ← Matrix.mulVec_mulVec, hχ, Matrix.mulVec_smul, hχ, smul_smul]) }
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hu0
  have hi' : u i ≠ 0 := hi
  have hc : ∀ z, χ z * u i = ∑ j, Ξ.mat (torus τ k z) j i * u j := fun z => (congrFun (hχ z) i).symm
  have hψ : (ψ : Multiplicative ℂ → ℂ) ∈ laurent := by
    convert laurent.sum_mem (t := Finset.univ) fun j _ => laurent.smul_mem (u j / u i) (reg_torus τ k (Ξ.reg j i)) using 1
    funext z; change χ z.toAdd = _; rw [← mul_left_inj' hi', hc, Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_; simp only [Pi.smul_apply, smul_eq_mul]; field_simp
  obtain ⟨p, hp⟩ : ψ ∈ Set.range expChar := by
    by_contra hn; exact (linearIndependent_monoidHom (Multiplicative ℂ) ℂ).notMem_span_image hn hψ
  have key : ∀ z, (dualS Ξ k k (atEmb τ z) *ᵥ u) i = -(p.1 * z + p.2 * starRingEnd ℂ z) * u i := by
    intro z
    have h1 := HasDerivAt.fun_sum (u := Finset.univ) fun j _ => (Ξ.hasDerivAt_curve _ _ (by simp [expDiag_zero])
      (hasDerivAt_expDiag (Pi.single k (atEmb τ z))) j i).mul_const (u j)
    have h2 : HasDerivAt (fun t : ℝ => Complex.exp (t * (p.1 * z + p.2 * starRingEnd ℂ z)) * u i)
        ((p.1 * z + p.2 * starRingEnd ℂ z) * u i) 0 := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const
        (p.1 * z + p.2 * starRingEnd ℂ z)).cexp.mul_const (u i)
    have h3 := h1.unique (h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
      have e : χ (t * z) = _ := (DFunLike.congr_fun hp (Multiplicative.ofAdd (t * z))).symm
      simp only [← hsm, ← hc, e, expChar, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, map_mul, Complex.conj_ofReal]
      congr 2; ring))
    rw [neg_mul, ← h3, dualS, Matrix.neg_mulVec, Matrix.diagonal_single]; rfl
  refine ⟨-p.1, mul_right_cancel₀ hi' ?_⟩
  have h1 := congrFun hu i
  simp only [dualE, Matrix.smul_mulVec, Matrix.sub_mulVec, Pi.smul_apply, Pi.sub_apply, key, smul_eq_mul, map_one,
    Complex.conj_I] at h1
  push_cast; linear_combination -h1 + ((p.1 - p.2) / 2 * u i) * Complex.I_mul_I

def dualL (Ξ : AlgRep E a) (i j : Fin a) : Cinf E →ₗ[ℝ] Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ where
  toFun := dualS Ξ i j
  map_add' x y := by
    have h : toL (Matrix.single i j (x + y)) = toL (Matrix.single i j x) + toL (Matrix.single i j y) :=
      congrArg toL (Matrix.single_add i j x y)
    simp only [dualS, h, map_add, Matrix.transpose_add, neg_add]
  map_smul' c x := by
    have h : toL (Matrix.single i j (c • x)) = c • toL (Matrix.single i j x) :=
      congrArg toL (Matrix.smul_single c i j x).symm
    simp only [dualS, h, map_smul, Matrix.transpose_smul, smul_neg, RingHom.id_apply]

omit [NumberField E] in
theorem dualL_apply (Ξ : AlgRep E a) (i j : Fin a) (x : Cinf E) : dualL Ξ i j x = dualS Ξ i j x := rfl

theorem dualL_comm (Ξ : AlgRep E a) (i j k l : Fin a) (x y : Cinf E) :
    dualL Ξ i j x * dualL Ξ k l y - dualL Ξ k l y * dualL Ξ i j x =
      (if j = k then dualL Ξ i l (x * y) else 0) - (if l = i then dualL Ξ k j (x * y) else 0) := by
  have h := congrArg (fun M => -Mᵀ) (dmat_bracket Ξ (Matrix.single i j x) (Matrix.single k l y))
  have e : ∀ X Y : Matrix (Fin a) (Fin a) (Cinf E), toL (X - Y) = toL X - toL Y := fun _ _ => rfl
  simp only [e, map_sub, Matrix.transpose_sub, Matrix.transpose_mul, neg_sub] at h
  simp only [dualL_apply, dualS, neg_mul_neg]
  rw [h, sub_eq_neg_add, sub_eq_add_neg]
  have z : Ξ.dmat (toL 0) = 0 := map_zero _
  congr 1
  · split_ifs with h
    · subst h; rw [Matrix.single_mul_single_same]
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ h, z]; simp
  · split_ifs with h
    · subst h; rw [Matrix.single_mul_single_same, mul_comm y, neg_neg]
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ h, z]; simp

theorem dualE_commutator_formula (Ξ : AlgRep E a) (τ τ' : E →+* ℂ) (i j k l : Fin a) :
    dualE Ξ τ i j * dualE Ξ τ' k l - dualE Ξ τ' k l * dualE Ξ τ i j =
      (if j = k then (1 / 4 : ℂ) • (dualL Ξ i l (atEmb τ 1 * atEmb τ' 1) - dualL Ξ i l (atEmb τ .I * atEmb τ' .I) -
        Complex.I • (dualL Ξ i l (atEmb τ 1 * atEmb τ' .I) + dualL Ξ i l (atEmb τ .I * atEmb τ' 1))) else 0) -
      (if l = i then (1 / 4 : ℂ) • (dualL Ξ k j (atEmb τ 1 * atEmb τ' 1) - dualL Ξ k j (atEmb τ .I * atEmb τ' .I) -
        Complex.I • (dualL Ξ k j (atEmb τ 1 * atEmb τ' .I) + dualL Ξ k j (atEmb τ .I * atEmb τ' 1))) else 0) := by
  have h1 := dualL_comm Ξ i j k l (atEmb τ 1) (atEmb τ' 1)
  have h2 := dualL_comm Ξ i j k l (atEmb τ 1) (atEmb τ' .I)
  have h3 := dualL_comm Ξ i j k l (atEmb τ .I) (atEmb τ' 1)
  have h4 := dualL_comm Ξ i j k l (atEmb τ .I) (atEmb τ' .I)
  simp only [dualE, ← dualL_apply, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, smul_sub, smul_smul]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  split_ifs at h1 h2 h3 h4 ⊢ <;>
    linear_combination (norm := skip) (exp := 1) (1 / 4 : ℂ) • h1 - (Complex.I / 4 : ℂ) • h2 -
      (Complex.I / 4 : ℂ) • h3 - (1 / 4 : ℂ) • h4 <;>
    match_scalars <;> ring_nf <;> simp

theorem glRel_dualE (Ξ : AlgRep E a) (τ : E →+* ℂ) : GlRel (dualE Ξ τ) := by
  intro i j k l
  have e : atEmb τ (Complex.I * Complex.I) = -atEmb τ 1 := by rw [atEmb_eq]; simp
  rw [dualE_commutator_formula]
  simp only [atEmb_mul, one_mul, mul_one, e, map_neg, dualE, ← dualL_apply]
  congr 1 <;> split_ifs <;> first | rfl | (match_scalars <;> ring)

variable [IsTotallyComplex E]

theorem dualE_comm (Ξ : AlgRep E a) {τ τ' : E →+* ℂ} (h : τ ≠ τ') (i j k l : Fin a) :
    dualE Ξ τ i j * dualE Ξ τ' k l = dualE Ξ τ' k l * dualE Ξ τ i j := by
  rw [← sub_eq_zero, dualE_commutator_formula]
  by_cases hw : InfinitePlace.mk τ = InfinitePlace.mk τ'
  · obtain rfl : ComplexEmbedding.conjugate τ = τ' := (InfinitePlace.mk_eq_iff.1 hw).resolve_left h
    have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by rw [atEmb_eq]; simp
    have e' : atEmb τ (-1) = -atEmb τ 1 := by rw [atEmb_eq]; simp
    simp [atEmb_conj, atEmb_mul, e, e']
  · simp [atEmb_mul_of_ne hw]

theorem qdet_commute_dualE (Ξ : AlgRep E a) (τ τ' : E →+* ℂ) (u : ℂ) (i j : Fin a) :
    Commute (qdet (dualE Ξ τ) u) (dualE Ξ τ' i j) := by
  by_cases h : τ = τ'
  · subst h; exact qdet_central _ (glRel_dualE Ξ τ) u i j
  · refine Commute.sum_left _ _ _ fun σ _ => Commute.mul_left (Int.cast_commute _ _)
      (Commute.list_prod_left _ _ fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine Commute.add_left ?_ (dualE_comm Ξ h _ _ _ _)
    split_ifs
    · exact Algebra.commutes _ _
    · exact Commute.zero_left _

theorem commute_dmat (Ξ : AlgRep E a) (Z : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)
    (h : ∀ τ i j, Commute Z (dualE Ξ τ i j)) (X : Lie E a) : Commute Z (Ξ.dmat X)ᵀ := by
  classical
  have h1 : ∀ τ i j z, Commute Z (dualL Ξ i j (atEmb τ z)) := by
    intro τ i j z
    have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by rw [atEmb_eq]; simp
    have e1 : dualL Ξ i j (atEmb τ 1) = dualE Ξ τ i j + dualE Ξ (ComplexEmbedding.conjugate τ) i j := by
      simp only [dualE, ← dualL_apply, atEmb_conj, map_one, Complex.conj_I, e, map_neg]
      match_scalars <;> ring
    have e2 : dualL Ξ i j (atEmb τ Complex.I) =
        Complex.I • (dualE Ξ τ i j - dualE Ξ (ComplexEmbedding.conjugate τ) i j) := by
      simp only [dualE, ← dualL_apply, atEmb_conj, map_one, Complex.conj_I, e, map_neg]
      match_scalars
      · linear_combination Complex.I_mul_I
      · ring
    rw [atEmb_eq, map_add, map_smul, map_smul, e1, e2]
    exact (((h _ _ _).add_right (h _ _ _)).smul_right _).add_right
      ((((h _ _ _).sub_right (h _ _ _)).smul_right _).smul_right _)
  have h2 : ∀ i j x, Commute Z (dualL Ξ i j x) := by
    intro i j x
    have e : x = ∑ w : InfinitePlace E, atEmb w.embedding (x w) := by
      conv_lhs => rw [← Finset.univ_sum_single x]
      refine Finset.sum_congr rfl fun w _ => ?_
      unfold atEmb; rw [if_pos (by rw [InfinitePlace.mk_embedding])]; congr 1; simp
    rw [e, map_sum]; exact Commute.sum_right _ _ _ fun w _ => h1 _ _ _ _
  have e : X = ∑ i, ∑ j, toL (Matrix.single i j (X i j)) := Matrix.matrix_eq_sum_single (Matrix.of X)
  rw [e, map_sum, Matrix.transpose_sum]
  refine Commute.sum_right _ _ _ fun i _ => ?_
  rw [map_sum, Matrix.transpose_sum]
  refine Commute.sum_right _ _ _ fun j _ => ?_
  simpa [dualL_apply, dualS] using (h2 i j (X i j)).neg_right

omit [NumberField E] [IsTotallyComplex E] in
theorem exists_scalar (Ξ : AlgRep E a) (Z : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) (h : ∀ y, Z * Ξ.mat y = Ξ.mat y * Z) :
    ∃ c : ℂ, Z = c • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) := by
  have : Nonempty (Fin Ξ.d) := ⟨⟨0, Ξ.pos⟩⟩
  obtain ⟨c, hc⟩ := exists_eigenvalue (Matrix.toLin' Z)
  refine ⟨c, ?_⟩
  have h1 := (Ξ.irred (Module.End.eigenspace (Matrix.toLin' Z) c) fun y v hv => by
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]).resolve_left hc
  apply Matrix.toLin'.injective; refine LinearMap.ext fun v => ?_
  have hv : v ∈ Module.End.eigenspace (Matrix.toLin' Z) c := h1 ▸ Submodule.mem_top
  rw [Module.End.mem_eigenspace_iff.1 hv]; simp

theorem qdet_scalar (Ξ : AlgRep E a) (τ : E →+* ℂ) (u : ℂ) :
    ∃ c : ℂ, qdet (dualE Ξ τ) u = c • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) := by
  obtain ⟨c, hc⟩ := exists_scalar Ξ (qdet (dualE Ξ τ) u)ᵀ (commute_mat Ξ _ fun X => by
    have h := congrArg Matrix.transpose (commute_dmat Ξ _ (fun τ' => qdet_commute_dualE Ξ τ τ' u) X).eq
    simpa [Matrix.transpose_mul] using h.symm)
  exact ⟨c, by simpa using congrArg Matrix.transpose hc⟩

theorem exists_dualInfChar (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (Ξ : AlgRep E a) (τ : E →+* ℂ) :
    ∃ m : Multiset ℂ, HasDualInfChar Ξ τ m ∧ m.Nodup ∧
      ∀ z ∈ m, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2 := by
  have : Nonempty (Fin Ξ.d) := ⟨⟨0, Ξ.pos⟩⟩
  let f := (Matrix.toLinAlgEquiv' : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin Ξ.d → ℂ)).toAlgHom
  have hf : ∀ M v, f M v = M *ᵥ v := fun _ _ => rfl
  have hgl : GlRel fun i j => f (dualE Ξ τ i j) := fun i j k l => by
    simpa only [map_sub, map_mul, apply_ite f, map_zero] using congrArg f (glRel_dualE Ξ τ i j k l)
  obtain ⟨ν, v, hv, hw, hν⟩ := exists_highest a _ hgl
  refine ⟨Finset.univ.val.map fun k : Fin a => ν k + (((a : ℂ) - 1) / 2 - (k : ℕ)), ⟨by simp, fun u => ?_⟩, ?_, ?_⟩
  · obtain ⟨c, hc⟩ := qdet_scalar Ξ τ (u + ((a : ℂ) - 1) / 2)
    have h := qdet_hw _ ν v hgl hw (u + ((a : ℂ) - 1) / 2)
    rw [← map_qdet, hc, hf, Matrix.smul_mulVec, Matrix.one_mulVec] at h
    rw [hc, smul_left_injective ℂ hv h, Multiset.map_map, ← Finset.prod_eq_multiset_prod]
    congr 1; exact Finset.prod_congr rfl fun k _ => by simp only [Function.comp_apply]; ring
  · have key : ∀ i j : Fin a, i < j →
        ν i + (((a : ℂ) - 1) / 2 - (i : ℕ)) ≠ ν j + (((a : ℂ) - 1) / 2 - (j : ℕ)) := by
      intro i j hij h
      obtain ⟨m, hm⟩ := hν i j hij
      have h2 : ((m + j : ℕ) : ℂ) = ((i : ℕ) : ℂ) := by push_cast; linear_combination h - hm
      have h3 : m + (j : ℕ) = i := Nat.cast_injective h2
      have : (i : ℕ) < j := hij; omega
    refine Multiset.Nodup.map (fun i j h => ?_) Finset.univ.nodup
    rcases lt_trichotomy i j with h' | h' | h'
    · exact absurd h (key i j h')
    · exact h'
    · exact absurd h.symm (key j i h')
  · intro z hz; obtain ⟨k, -, rfl⟩ := Multiset.mem_map.1 hz
    obtain ⟨n, hn⟩ := eigenvalue_int Ξ τ k v (ν k) hv (hw.1 k)
    exact ⟨n - (k : ℕ), by rw [hn]; push_cast; ring⟩

end DualInfCharRegular

/-! ## Section 4: `(𝔤, K)`-Cohomology, Transport & Conjugation (`HasCohomology`, `HasCohomologyTransport`) -/

section CohomologyAndTransport

section SmoothLieComm

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem chart_rt_inf (φ : GA E a → ℂ) (g : GA E a) (y : GL (Fin a) (Cinf E)) :
    chart (fun x => φ (x * infGL E a y)) g = chart φ g ∘ rmul (toL y.val) := by
  funext x
  by_cases h : IsUnit (Matrix.of x)
  · obtain ⟨u, hu⟩ := h
    have hx : x = toL u.val := hu.symm
    rw [hx, chart_val, mul_assoc, ← map_mul, ← chart_val φ g]; rfl
  · have h' : ¬ IsUnit (Matrix.of (rmul (toL y.val) x)) := fun h' => by
      have : Matrix.of (rmul (toL y.val) x) = Matrix.of x * y.val := rfl
      rw [this] at h'
      exact h (by simpa [mul_assoc] using h'.mul (y⁻¹).isUnit)
    rw [Function.comp_apply, chart, chart, dif_neg h, dif_neg h']

theorem hasDerivAt_curve_sm (φ : Sm E a) (g : GA E a) (c : ℝ → GL (Fin a) (Cinf E)) (X : Lie E a)
    (h0 : c 0 = 1) (hc : HasDerivAt (fun t => toL (c t).val) X 0) :
    HasDerivAt (fun t => φ.1 (g * infGL E a (c t))) (lieD X φ.1 g) 0 := by
  have h : HasFDerivAt (chart φ.1 g) (fderiv ℝ (chart φ.1 g) (oneL E a)) (toL (c 0).val) := by
    rw [h0]; exact (differentiableAt_chart φ.2 g).hasFDerivAt
  have h2 := h.comp_hasDerivAt (0 : ℝ) hc
  simp only [Function.comp_def, chart_val] at h2
  exact h2

open scoped ContDiff in
theorem lie_comm (X Y : Lie E a) :
    lie E a X * lie E a Y - lie E a Y * lie E a X =
      lie E a (toL (Matrix.of X * Matrix.of Y)) - lie E a (toL (Matrix.of Y * Matrix.of X)) := by
  refine LinearMap.ext fun φ => Subtype.ext <| funext fun g => ?_
  have hs : ContDiffAt ℝ ∞ (chart φ.1 g) (oneL E a) := contDiffAt_chart φ.2 g isUnit_one
  have hd : DifferentiableAt ℝ (fderiv ℝ (chart φ.1 g)) (oneL E a) :=
    (hs.fderiv_right (m := 1) (by norm_cast)).differentiableAt (by simp)
  have key : ∀ X Y : Lie E a, lieD X (lieD Y φ.1) g =
      fderiv ℝ (fderiv ℝ (chart φ.1 g)) (oneL E a) X Y + lieD (toL (Matrix.of X * Matrix.of Y)) φ.1 g := by
    intro X Y
    have e : chart (lieD Y φ.1) g =ᶠ[𝓝 (oneL E a)] fun x => fderiv ℝ (chart φ.1 g) x (rmul Y x) :=
      Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun x hx => chart_lieD φ.2 Y g hx
    rw [lieD, e.fderiv_eq, fderiv_clm_apply hd (rmul Y).differentiableAt, ContinuousLinearMap.fderiv]
    have e1 : rmul Y (oneL E a) = Y := one_mul (Matrix.of Y)
    rw [e1, add_comm]; rfl
  change lieD X (lieD Y φ.1) g - lieD Y (lieD X φ.1) g = lieD _ φ.1 g - lieD _ φ.1 g
  rw [key, key, (hs.isSymmSndFDerivAt (by simp; norm_cast)).eq X Y]
  ring

theorem rt_lie (y : GL (Fin a) (Cinf E)) (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    rt E a (infGL E a y) * lie E a (toL X) = lie E a (toL (y.val * X * (y⁻¹).val)) * rt E a (infGL E a y) := by
  refine LinearMap.ext fun φ => Subtype.ext <| funext fun g => ?_
  change fderiv ℝ (chart φ.1 (g * infGL E a y)) (oneL E a) (toL X) =
    fderiv ℝ (chart (fun x => φ.1 (x * infGL E a y)) g) (oneL E a) (toL (y.val * X * (y⁻¹).val))
  have hd : DifferentiableAt ℝ (chart φ.1 g) (toL y.val) :=
    (contDiffAt_chart φ.2 g (val_mem_invSet y)).differentiableAt (by simp)
  have e1 : lmul (toL y.val) (oneL E a) = toL y.val := mul_one y.val
  have e2 : rmul (toL y.val) (oneL E a) = toL y.val := one_mul y.val
  rw [chart_mul, chart_rt_inf, fderiv_comp _ (by rw [e1]; exact hd) (lmul (toL y.val)).differentiableAt,
    fderiv_comp _ (by rw [e2]; exact hd) (rmul (toL y.val)).differentiableAt, e1, e2,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]
  exact congrArg (fun Z => fderiv ℝ (chart φ.1 g) (toL y.val) (toL Z)) (Units.inv_mul_cancel_right (y.val * X) y).symm

theorem lieS_comm (i j k l : Fin a) (x y : Cinf E) :
    lieS E a i j x * lieS E a k l y - lieS E a k l y * lieS E a i j x =
      (if j = k then lieS E a i l (x * y) else 0) - (if l = i then lieS E a k j (x * y) else 0) := by
  simp only [lieS_apply, lie_comm]
  have z : lie E a (toL 0) = 0 := map_zero _
  congr 1
  · split_ifs with h
    · subst h; rw [show Matrix.of (toL (Matrix.single i j x)) = Matrix.single i j x from rfl,
        show Matrix.of (toL (Matrix.single j l y)) = Matrix.single j l y from rfl, Matrix.single_mul_single_same]
    · rw [show Matrix.of (toL (Matrix.single i j x)) = Matrix.single i j x from rfl,
        show Matrix.of (toL (Matrix.single k l y)) = Matrix.single k l y from rfl,
        Matrix.single_mul_single_of_ne _ _ _ _ h, z]
  · split_ifs with h
    · rw [h, show Matrix.of (toL (Matrix.single k i y)) = Matrix.single k i y from rfl,
        show Matrix.of (toL (Matrix.single i j x)) = Matrix.single i j x from rfl,
        Matrix.single_mul_single_same, mul_comm y]
    · rw [show Matrix.of (toL (Matrix.single k l y)) = Matrix.single k l y from rfl,
        show Matrix.of (toL (Matrix.single i j x)) = Matrix.single i j x from rfl,
        Matrix.single_mul_single_of_ne _ _ _ _ h, z]

theorem Eop_comm_aux (τ τ' : E →+* ℂ) (i j k l : Fin a) :
    Eop τ i j * Eop τ' k l - Eop τ' k l * Eop τ i j =
      (if j = k then (1 / 4 : ℂ) • (lieS E a i l (atEmb τ 1 * atEmb τ' 1) - lieS E a i l (atEmb τ .I * atEmb τ' .I) -
        Complex.I • (lieS E a i l (atEmb τ 1 * atEmb τ' .I) + lieS E a i l (atEmb τ .I * atEmb τ' 1))) else 0) -
      (if l = i then (1 / 4 : ℂ) • (lieS E a k j (atEmb τ 1 * atEmb τ' 1) - lieS E a k j (atEmb τ .I * atEmb τ' .I) -
        Complex.I • (lieS E a k j (atEmb τ 1 * atEmb τ' .I) + lieS E a k j (atEmb τ .I * atEmb τ' 1))) else 0) := by
  have h1 := lieS_comm i j k l (atEmb τ 1) (atEmb τ' 1)
  have h2 := lieS_comm i j k l (atEmb τ 1) (atEmb τ' .I)
  have h3 := lieS_comm i j k l (atEmb τ .I) (atEmb τ' 1)
  have h4 := lieS_comm i j k l (atEmb τ .I) (atEmb τ' .I)
  simp only [Eop, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, smul_sub, smul_smul]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  split_ifs at h1 h2 h3 h4 ⊢ <;>
    linear_combination (norm := skip) (exp := 1) (1 / 4 : ℂ) • h1 - (Complex.I / 4 : ℂ) • h2 -
      (Complex.I / 4 : ℂ) • h3 - (1 / 4 : ℂ) • h4 <;>
    match_scalars <;> ring_nf <;> simp

theorem glRel_Eop (τ : E →+* ℂ) : GlRel (Eop (E := E) (a := a) τ) := by
  intro i j k l
  have e : atEmb τ (Complex.I * Complex.I) = -atEmb τ 1 := by rw [atEmb_eq]; simp
  rw [Eop_comm_aux]
  simp only [atEmb_mul, one_mul, mul_one, e, map_neg, Eop]
  congr 1 <;> split_ifs <;> first | rfl | (match_scalars <;> ring)

end SmoothLieComm

section CohomologyDef

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

variable (E a) in
abbrev Herm : Submodule ℝ (Matrix (Fin a) (Fin a) (Cinf E)) :=
  selfAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) (Cinf E))

omit [NumberField E] in
def adHerm (k : Kinf E a) (X : Herm E a) : Herm E a :=
  ⟨k.1 * X.1 * star k.1, IsSelfAdjoint.conjugate X.2 k.1⟩

section Complex

omit [NumberField E]

variable {M : Type*} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
  (κ : Kinf E a → Module.End ℂ M) (L : Lie E a →ₗ[ℝ] Module.End ℂ M)

def IsCochain {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M) : Prop :=
  ∀ (k : Kinf E a) (X : Fin q → Herm E a), ω (fun i => adHerm k (X i)) = κ k (ω X)

def dCo {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M) : Herm E a [⋀^Fin (q + 1)]→ₗ[ℝ] M :=
  AlternatingMap.alternatizeUncurryFin
    { toFun := fun X => ((L (toL X.1)).restrictScalars ℝ).compAlternatingMap ω
      map_add' := fun X Y => AlternatingMap.ext fun v => LinearMap.congr_fun (map_add L (toL X.1) (toL Y.1)) (ω v)
      map_smul' := fun c X => AlternatingMap.ext fun v => LinearMap.congr_fun (map_smul L c (toL X.1)) (ω v) }

theorem dCo_apply {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M) (X : Fin (q + 1) → Herm E a) :
    dCo L ω X = ∑ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) • L (toL (X i).1) (ω (i.removeNth X)) :=
  AlternatingMap.alternatizeUncurryFin_apply _ _

def HasCohomology : Prop :=
  (∃ ω : Herm E a [⋀^Fin 0]→ₗ[ℝ] M, IsCochain κ ω ∧ dCo L ω = 0 ∧ ω ≠ 0) ∨
    ∃ (q : ℕ) (ω : Herm E a [⋀^Fin (q + 1)]→ₗ[ℝ] M), IsCochain κ ω ∧ dCo L ω = 0 ∧
      ∀ η : Herm E a [⋀^Fin q]→ₗ[ℝ] M, IsCochain κ η → dCo L η ≠ ω

variable {κ L}

theorem IsCochain.dCo (h : ∀ (k : Kinf E a) (X : Herm E a), κ k * L (toL X.1) = L (toL (adHerm k X).1) * κ k)
    {q : ℕ} {ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M} (hω : IsCochain κ ω) : IsCochain κ (dCo L ω) := fun k X => by
  rw [dCo_apply, dCo_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, ← Module.End.mul_apply, h, Module.End.mul_apply, ← hω]; rfl

theorem hasCohomology_of_invariant {m : M} (h0 : m ≠ 0) (hκ : ∀ k, κ k m = m) (hL : ∀ X, L X m = 0) :
    HasCohomology κ L :=
  Or.inl ⟨AlternatingMap.constOfIsEmpty ℝ _ _ m, fun k _ => (hκ k).symm,
    AlternatingMap.ext fun X => by simp [dCo_apply, hL], fun h => h0 (DFunLike.congr_fun h 0)⟩

theorem dCo_cons {q : ℕ} (ω : Herm E a [⋀^Fin (q + 1)]→ₗ[ℝ] M) (Z : Herm E a) (X : Fin (q + 1) → Herm E a) :
    dCo L ω (Matrix.vecCons Z X) = L (toL Z.1) (ω X) - dCo L (ω.curryLeft Z) X := by
  rw [dCo_apply, dCo_apply, Fin.sum_univ_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · simp [Matrix.vecCons]
  · refine Finset.sum_congr rfl fun i _ => ?_
    have e : i.succ.removeNth (Matrix.vecCons Z X) = Matrix.vecCons Z (i.removeNth X) := by
      funext j; refine Fin.cases ?_ (fun j => ?_) j <;> simp [Fin.removeNth]
    simp [e, pow_succ]

theorem not_hasCohomology_of_central {c : ℂ} (hc : c ≠ 0) (h : ∀ m, L (oneL E a) m = c • m) :
    ¬ HasCohomology κ L := by
  let Z : Herm E a := ⟨1, IsSelfAdjoint.one _⟩
  have hZ : ∀ k, adHerm k Z = Z := fun k => Subtype.ext (by
    change k.1 * 1 * star k.1 = 1; rw [mul_one]; exact k.2.2)
  rintro (⟨ω, -, h1, h2⟩ | ⟨q, ω, h0, h1, h2⟩)
  · refine h2 (AlternatingMap.ext fun X => ?_)
    have h3 := DFunLike.congr_fun h1 fun _ => Z
    rw [dCo_apply, Fin.sum_univ_one, h, Subsingleton.elim (Fin.removeNth _ _) X] at h3
    simpa [hc] using h3
  · let s : M →ₗ[ℝ] M := (c⁻¹ • LinearMap.id : M →ₗ[ℂ] M).restrictScalars ℝ
    refine h2 (s.compAlternatingMap (ω.curryLeft Z)) (fun k X => ?_) (AlternatingMap.ext fun X => ?_)
    · change c⁻¹ • ω (Matrix.vecCons Z _) = κ k (c⁻¹ • ω (Matrix.vecCons Z X))
      rw [map_smul, ← h0]; congr 2; funext j; refine Fin.cases ?_ (fun j => ?_) j <;> simp [hZ]
    · have h3 := dCo_cons (L := L) ω Z X
      rw [h1, h, AlternatingMap.zero_apply, eq_comm, sub_eq_zero, dCo_apply] at h3
      rw [dCo_apply, ← inv_smul_smul₀ hc (ω X), h3, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_comm c⁻¹, ← map_smul (L _) c⁻¹]; rfl

end Complex

variable [IsTotallyComplex E]

def lieOp (π : CuspSub E a) : Lie E a →ₗ[ℝ] Module.End ℂ π.V where
  toFun X := π.op (.lie X)
  map_add' X Y := LinearMap.ext fun φ => Subtype.ext (LinearMap.congr_fun (map_add (lie E a) X Y) φ.1)
  map_smul' c X := LinearMap.ext fun φ => Subtype.ext (LinearMap.congr_fun (map_smul (lie E a) c X) φ.1)

def tensorK (π : CuspSub E a) (Ξ : AlgRep E a) (k : Kinf E a) :
    Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) :=
  TensorProduct.map (π.op (.cpt k)) (Matrix.toLin' (Ξ.mat (Unitary.toUnits k)))

def tensorLie (π : CuspSub E a) (Ξ : AlgRep E a) :
    Lie E a →ₗ[ℝ] Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) where
  toFun X := (lieOp π X).rTensor _ + (Matrix.toLin' (Ξ.dmat X)).lTensor _
  map_add' X Y := by simp only [map_add, LinearMap.rTensor_add, LinearMap.lTensor_add]; abel
  map_smul' c X := by
    rw [map_smul, map_smul, RingHom.id_apply, ← algebraMap_smul ℂ c (lieOp π X),
      ← algebraMap_smul ℂ c (Ξ.dmat X),
      ← algebraMap_smul ℂ c (_ + _ : Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))), map_smul,
      LinearMap.rTensor_smul, LinearMap.lTensor_smul, smul_add]

theorem tensorLie_tmul (π : CuspSub E a) (Ξ : AlgRep E a) (X : Lie E a) (φ : π.V) (v : Fin Ξ.d → ℂ) :
    tensorLie π Ξ X (φ ⊗ₜ v) = π.op (.lie X) φ ⊗ₜ v + φ ⊗ₜ (Ξ.dmat X *ᵥ v) := rfl

theorem tensorK_mul_tensorLie (π : CuspSub E a) (Ξ : AlgRep E a) (k : Kinf E a) (X : Herm E a) :
    tensorK π Ξ k * tensorLie π Ξ (toL X.1) = tensorLie π Ξ (toL (adHerm k X).1) * tensorK π Ξ k := by
  refine TensorProduct.ext' fun φ v => ?_
  have h1 : π.op (.cpt k) (π.op (.lie (toL X.1)) φ) = π.op (.lie (toL (adHerm k X).1)) (π.op (.cpt k) φ) :=
    Subtype.ext (LinearMap.congr_fun (rt_lie (Unitary.toUnits k) X.1) φ.1)
  have h2 : Ξ.mat (Unitary.toUnits k) * Ξ.dmat (toL X.1) = Ξ.dmat (toL (adHerm k X).1) * Ξ.mat (Unitary.toUnits k) :=
    Ξ.mat_mul_dmat (Unitary.toUnits k) X.1
  simp only [Module.End.mul_apply, tensorK, tensorLie_tmul, map_add, TensorProduct.map_tmul,
    Matrix.toLin'_apply, Matrix.mulVec_mulVec, h1, h2]

def IsCohFor (π : CuspSub E a) (Ξ : AlgRep E a) : Prop := HasCohomology (tensorK π Ξ) (tensorLie π Ξ)

def IsCohomological (π : CuspSub E a) : Prop := ∃ Ξ : AlgRep E a, IsCohFor π Ξ

end CohomologyDef

section CohomologyTransport

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

section Transport

omit [NumberField E]

variable {M M' : Type*} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
  [AddCommGroup M'] [Module ℂ M'] [Module ℝ M'] [IsScalarTower ℝ ℂ M']
  {κ : Kinf E a → Module.End ℂ M} {L : Lie E a →ₗ[ℝ] Module.End ℂ M}
  {κ' : Kinf E a → Module.End ℂ M'} {L' : Lie E a →ₗ[ℝ] Module.End ℂ M'}

def tr (σ : Herm E a →ₗ[ℝ] Herm E a) (T : M →ₗ[ℂ] M') {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M) :
    Herm E a [⋀^Fin q]→ₗ[ℝ] M' :=
  (T.restrictScalars ℝ).compAlternatingMap (ω.compLinearMap σ)

theorem tr_apply (σ : Herm E a →ₗ[ℝ] Herm E a) (T : M →ₗ[ℂ] M') {q : ℕ}
    (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M) (X : Fin q → Herm E a) :
    tr σ T ω X = T (ω fun i => σ (X i)) := rfl

theorem isCochain_tr {σ : Herm E a →ₗ[ℝ] Herm E a} {s : Kinf E a → Kinf E a} {T : M →ₗ[ℂ] M'}
    (had : ∀ k X, σ (adHerm k X) = adHerm (s k) (σ X)) (hκ : ∀ k m, T (κ (s k) m) = κ' k (T m))
    {q : ℕ} {ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M} (hω : IsCochain κ ω) : IsCochain κ' (tr σ T ω) :=
  fun k X => by rw [tr_apply, tr_apply, ← hκ, ← hω]; simp only [had]

theorem dCo_tr {σ : Herm E a →ₗ[ℝ] Herm E a} {T : M →ₗ[ℂ] M'}
    (hL : ∀ X m, T (L (toL (σ X).1) m) = L' (toL X.1) (T m))
    {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M) : dCo L' (tr σ T ω) = tr σ T (dCo L ω) := by
  refine AlternatingMap.ext fun X => ?_
  rw [tr_apply, dCo_apply, dCo_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, hL, tr_apply]; rfl

theorem tr_tr {σ : Herm E a →ₗ[ℝ] Herm E a} (hσ : ∀ X, σ (σ X) = X) (T : M ≃ₗ[ℂ] M')
    {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M) :
    tr σ T.symm.toLinearMap (tr σ T.toLinearMap ω) = ω :=
  AlternatingMap.ext fun X => by simp [tr_apply, hσ]

theorem tr_zero (σ : Herm E a →ₗ[ℝ] Herm E a) (T : M →ₗ[ℂ] M') {q : ℕ} :
    tr σ T (0 : Herm E a [⋀^Fin q]→ₗ[ℝ] M) = 0 :=
  AlternatingMap.ext fun _ => by simp [tr_apply]

theorem hasCohomology_transport {σ : Herm E a →ₗ[ℝ] Herm E a} {s : Kinf E a → Kinf E a} (T : M ≃ₗ[ℂ] M')
    (hσ : ∀ X, σ (σ X) = X) (hs : ∀ k, s (s k) = k)
    (had : ∀ k X, σ (adHerm k X) = adHerm (s k) (σ X)) (hκ : ∀ k m, T (κ (s k) m) = κ' k (T m))
    (hL : ∀ X m, T (L (toL (σ X).1) m) = L' (toL X.1) (T m)) (H : HasCohomology κ L) :
    HasCohomology κ' L' := by
  have hκ' : ∀ k m, T.symm (κ' (s k) m) = κ k (T.symm m) := fun k m => by
    rw [T.symm_apply_eq]; have := hκ (s k) (T.symm m); rw [hs, T.apply_symm_apply] at this; exact this.symm
  have hL' : ∀ X m, T.symm (L' (toL (σ X).1) m) = L (toL X.1) (T.symm m) := fun X m => by
    rw [T.symm_apply_eq]; have := hL (σ X) (T.symm m); rw [hσ, T.apply_symm_apply] at this; exact this.symm
  rcases H with ⟨ω, h0, h1, h2⟩ | ⟨q, ω, h0, h1, h2⟩
  · refine Or.inl ⟨tr σ T.toLinearMap ω, isCochain_tr (T := T.toLinearMap) had hκ h0, ?_, fun h => h2 ?_⟩
    · rw [dCo_tr (L := L) (T := T.toLinearMap) hL, h1, tr_zero]
    · rw [← tr_tr hσ T ω, h, tr_zero]
  · refine Or.inr ⟨q, tr σ T.toLinearMap ω, isCochain_tr (T := T.toLinearMap) had hκ h0, ?_, fun η hη h => ?_⟩
    · rw [dCo_tr (L := L) (T := T.toLinearMap) hL, h1, tr_zero]
    · refine h2 (tr σ T.symm.toLinearMap η) (isCochain_tr (T := T.symm.toLinearMap) had hκ' hη) ?_
      rw [dCo_tr (L := L') (T := T.symm.toLinearMap) hL', h, tr_tr hσ]

end Transport

omit [NumberField E] in
def barG : GL (Fin a) (Cinf E) →* GL (Fin a) (Cinf E) :=
  GeneralLinearGroup.map (starRingEnd (Cinf E))

omit [NumberField E] in
theorem barG_val (y : GL (Fin a) (Cinf E)) (i j : Fin a) : (barG y).val i j = star (y.val i j) := rfl

omit [NumberField E] in
theorem barG_barG (y : GL (Fin a) (Cinf E)) : barG (barG y) = y := by
  ext i j : 2; simp [barG_val]

omit [NumberField E] in
theorem barG_det (y : GL (Fin a) (Cinf E)) : (barG y).val.det = star y.val.det :=
  ((starRingEnd (Cinf E)).map_det y.val).symm

omit [NumberField E] in
def barH : Herm E a →ₗ[ℝ] Herm E a where
  toFun X := ⟨X.1.map star, by
    have h : star X.1 = X.1 := X.2
    change star (X.1.map star) = X.1.map star
    ext i j : 1
    have := congrFun (congrFun h j) i
    change star (star (X.1 j i)) = star (X.1 i j)
    rw [star_star]; exact this.symm⟩
  map_add' _ _ := Subtype.ext (by ext i j; simp)
  map_smul' _ _ := Subtype.ext (by ext i j; simp)

variable [IsTotallyComplex E]

omit [NumberField E] in
theorem coord_star_eq_conj (τ : E →+* ℂ) (x : Cinf E) :
    coord τ (star x) = coord (ComplexEmbedding.conjugate τ) x := by
  have hne : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
    IsTotallyComplex.complexEmbedding_not_isReal τ (ComplexEmbedding.isReal_iff.2 h)
  unfold coord; rw [InfinitePlace.mk_conjugate_eq]
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · rw [if_pos h, if_neg (by rw [h]; exact hne.symm)]; simp
  · rw [if_neg (by rw [h]; exact hne), if_pos h]; simp

omit [NumberField E] in
theorem regFun_comp {f : GL (Fin a) (Cinf E) → ℂ} (hf : f ∈ regFun E a) :
    (fun y => f (barG y)) ∈ regFun E a := by
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    rcases hf with ⟨τ, i, j, rfl⟩ | ⟨τ, rfl⟩
    · exact Algebra.subset_adjoin (Or.inl ⟨_, i, j, funext fun y => coord_star_eq_conj τ _⟩)
    · exact Algebra.subset_adjoin (Or.inr ⟨ComplexEmbedding.conjugate τ, funext fun y => by
        simp only [barG_det, coord_star_eq_conj]⟩)
  | algebraMap c => exact Subalgebra.algebraMap_mem _ c
  | add _ _ _ _ h1 h2 => exact add_mem h1 h2
  | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2

abbrev barRep (Ξ : AlgRep E a) : AlgRep E a where
  d := Ξ.d
  mat := Ξ.mat.comp barG
  reg i j := regFun_comp (Ξ.reg i j)
  pos := Ξ.pos
  irred W hW := Ξ.irred W fun y v hv => by
    have := hW (barG y) v hv; rwa [MonoidHom.comp_apply, barG_barG] at this

omit [NumberField E] [IsTotallyComplex E] in
def barL : Lie E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X i j => star (X i j)
      map_add' := fun _ _ => by ext i j; simp
      map_smul' := fun _ _ => by ext i j; simp }

def IsAlgIso (Ξ Ξ' : AlgRep E a) (T : (Fin Ξ.d → ℂ) ≃ₗ[ℂ] (Fin Ξ'.d → ℂ)) : Prop :=
  (∀ y v, T (Ξ.mat y *ᵥ v) = Ξ'.mat y *ᵥ T v) ∧ ∀ X v, T (Ξ.dmat X *ᵥ v) = Ξ'.dmat X *ᵥ T v

omit [NumberField E] [IsTotallyComplex E] in
theorem isAlgIso_refl (Ξ : AlgRep E a) : IsAlgIso Ξ Ξ (LinearEquiv.refl _ _) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem cohTransport (π : CuspSub E a) (Ξ Ξ' : AlgRep E a)
    (T : (Fin Ξ.d → ℂ) ≃ₗ[ℂ] (Fin Ξ'.d → ℂ)) (hT : IsAlgIso Ξ Ξ' T) :
    IsCohFor π Ξ → IsCohFor π Ξ' := by
  intro H
  refine hasCohomology_transport (σ := LinearMap.id) (s := id) (LinearEquiv.lTensor π.V T)
    (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun k m => ?_) (fun X m => ?_) H
  · induction m using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul φ v =>
      change π.op (.cpt k) φ ⊗ₜ[ℂ] T (Ξ.mat (Unitary.toUnits k) *ᵥ v) =
        π.op (.cpt k) φ ⊗ₜ[ℂ] (Ξ'.mat (Unitary.toUnits k) *ᵥ T v)
      rw [hT.1]
  · induction m using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul φ v =>
      rw [tensorLie_tmul, map_add]
      change π.op (.lie (toL X.1)) φ ⊗ₜ[ℂ] T v + φ ⊗ₜ[ℂ] T (Ξ.dmat (toL X.1) *ᵥ v) =
        π.op (.lie (toL X.1)) φ ⊗ₜ[ℂ] T v + φ ⊗ₜ[ℂ] (Ξ'.dmat (toL X.1) *ᵥ T v)
      rw [hT.2]

end CohomologyTransport

end CohomologyAndTransport

/-! ## Section 5: Multi-`𝔤𝔩_n` Highest-Weight Irreducibility & Algebraic Isomorphism -/

section MultiGLHighestWeights

section HWDefs

variable {ι V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}

def IsMultiGl {A : Type*} [Ring A] (F : ι → Fin n → Fin n → A) : Prop :=
  (∀ t, GlRel (F t)) ∧ ∀ s t, s ≠ t → ∀ i j k l, F s i j * F t k l = F t k l * F s i j

def Stab (F : ι → Fin n → Fin n → Module.End ℂ V) (W : Submodule ℂ V) : Prop :=
  ∀ t i j, ∀ w ∈ W, F t i j w ∈ W

def low (F : ι → Fin n → Fin n → Module.End ℂ V) (v : V) : Submodule ℂ V :=
  sInf {W | v ∈ W ∧ ∀ t i j, j < i → ∀ w ∈ W, F t i j w ∈ W}

def Dom (ν : Fin n → ℂ) : Prop := ∀ i j, i < j → ∃ m : ℕ, ν i - ν j = (m : ℂ)

end HWDefs

section HolAndLieHom

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

section Hol

variable {N : Type*} [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N]

omit [NumberField E] in
def eL (L : Lie E a →ₗ[ℝ] N) (τ : E →+* ℂ) (i j : Fin a) : N :=
  (1 / 2 : ℂ) • (L (toL (Matrix.single i j (atEmb τ 1))) - Complex.I • L (toL (Matrix.single i j (atEmb τ Complex.I))))

omit [NumberField E] in
def hol (τ : E →+* ℂ) (L : Lie E a →ₗ[ℝ] N) : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] N where
  toFun x := ∑ i, ∑ j, x i j • eL L τ i j
  map_add' _ _ := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' _ _ := by simp [Finset.smul_sum, mul_smul]

omit [NumberField E] [IsScalarTower ℝ ℂ N] in
theorem hol_apply (τ : E →+* ℂ) (L : Lie E a →ₗ[ℝ] N) (x : Matrix (Fin a) (Fin a) ℂ) :
    hol τ L x = ∑ i, ∑ j, x i j • eL L τ i j := rfl

omit [NumberField E] [IsScalarTower ℝ ℂ N] in
theorem hol_single (τ : E →+* ℂ) (L : Lie E a →ₗ[ℝ] N) (i j : Fin a) :
    hol τ L (Matrix.single i j 1) = eL L τ i j := by
  simp [hol_apply, Matrix.single_apply, ite_and]

end Hol

omit [NumberField E] in
theorem eL_dmat (Ξ : AlgRep E a) (τ : E →+* ℂ) : eL Ξ.dmat τ = eOf Ξ.mat τ := rfl

omit [NumberField E] in
theorem dualE_eq (Ξ : AlgRep E a) (τ : E →+* ℂ) (i j : Fin a) :
    dualE Ξ τ i j = -(eL Ξ.dmat τ i j)ᵀ := by
  simp only [dualE, dualS, eL, Matrix.transpose_smul, Matrix.transpose_sub]; module

omit [NumberField E] in
def IsLieHom {A : Type*} [Ring A] [Module ℝ A] (L : Lie E a →ₗ[ℝ] A) : Prop :=
  ∀ X Y : Matrix (Fin a) (Fin a) (Cinf E), L (toL X) * L (toL Y) - L (toL Y) * L (toL X) = L (toL (X * Y - Y * X))

def eEnd (Ξ : AlgRep E a) (τ : E →+* ℂ) (i j : Fin a) : Module.End ℂ (Fin Ξ.d → ℂ) :=
  Matrix.toLin' (eL Ξ.dmat τ i j)

section SLApply

variable {A : Type*} [Ring A] [Algebra ℂ A] [Module ℝ A]

omit [NumberField E] [Algebra ℂ A] in
private def sL (L : Lie E a →ₗ[ℝ] A) (i j : Fin a) : Cinf E →ₗ[ℝ] A where
  toFun x := L (toL (Matrix.single i j x))
  map_add' x y := (congrArg L (congrArg toL (Matrix.single_add i j x y))).trans (L.map_add _ _)
  map_smul' c x := (congrArg L (congrArg toL (Matrix.smul_single c i j x).symm)).trans (L.map_smul _ _)

omit [NumberField E] [Algebra ℂ A] in
private theorem sL_apply (L : Lie E a →ₗ[ℝ] A) (i j : Fin a) (x : Cinf E) :
    sL L i j x = L (toL (Matrix.single i j x)) := rfl

omit [NumberField E] [Algebra ℂ A] in
private theorem sL_comm (L : Lie E a →ₗ[ℝ] A) (hL : IsLieHom L) (i j k l : Fin a) (x y : Cinf E) :
    sL L i j x * sL L k l y - sL L k l y * sL L i j x =
      (if j = k then sL L i l (x * y) else 0) - (if l = i then sL L k j (x * y) else 0) := by
  have h := hL (Matrix.single i j x) (Matrix.single k l y)
  have e : ∀ X Y : Matrix (Fin a) (Fin a) (Cinf E), toL (X - Y) = toL X - toL Y := fun _ _ => rfl
  rw [e, map_sub] at h; simp only [sL_apply]; rw [h]
  have z : L (toL 0) = 0 := map_zero _
  congr 1
  · split_ifs with h
    · subst h; rw [Matrix.single_mul_single_same]
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ h, z]
  · split_ifs with h
    · subst h; rw [Matrix.single_mul_single_same, mul_comm y]
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ h, z]

omit [NumberField E] in
private theorem eL_comm_aux [IsScalarTower ℝ ℂ A] (L : Lie E a →ₗ[ℝ] A) (hL : IsLieHom L)
    (τ τ' : E →+* ℂ) (i j k l : Fin a) :
    eL L τ i j * eL L τ' k l - eL L τ' k l * eL L τ i j =
      (if j = k then (1 / 4 : ℂ) • (sL L i l (atEmb τ 1 * atEmb τ' 1) - sL L i l (atEmb τ .I * atEmb τ' .I) -
        Complex.I • (sL L i l (atEmb τ 1 * atEmb τ' .I) + sL L i l (atEmb τ .I * atEmb τ' 1))) else 0) -
      (if l = i then (1 / 4 : ℂ) • (sL L k j (atEmb τ 1 * atEmb τ' 1) - sL L k j (atEmb τ .I * atEmb τ' .I) -
        Complex.I • (sL L k j (atEmb τ 1 * atEmb τ' .I) + sL L k j (atEmb τ .I * atEmb τ' 1))) else 0) := by
  have h1 := sL_comm L hL i j k l (atEmb τ 1) (atEmb τ' 1)
  have h2 := sL_comm L hL i j k l (atEmb τ 1) (atEmb τ' .I)
  have h3 := sL_comm L hL i j k l (atEmb τ .I) (atEmb τ' 1)
  have h4 := sL_comm L hL i j k l (atEmb τ .I) (atEmb τ' .I)
  simp only [eL, ← sL_apply, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, smul_sub, smul_smul]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  split_ifs at h1 h2 h3 h4 ⊢ <;>
    linear_combination (norm := skip) (exp := 1) (1 / 4 : ℂ) • h1 - (Complex.I / 4 : ℂ) • h2 -
      (Complex.I / 4 : ℂ) • h3 - (1 / 4 : ℂ) • h4 <;>
    match_scalars <;> ring_nf <;> simp

end SLApply

omit [NumberField E] in
theorem eLRel [IsTotallyComplex E] (A : Type*) [Ring A] [Algebra ℂ A] [Module ℝ A] [IsScalarTower ℝ ℂ A]
    (L : Lie E a →ₗ[ℝ] A) (hL : IsLieHom L) : IsMultiGl (eL L) := by
  refine ⟨fun τ i j k l => ?_, fun τ τ' h i j k l => ?_⟩
  · have e : atEmb τ (Complex.I * Complex.I) = -atEmb τ 1 := by rw [atEmb_eq]; simp
    rw [eL_comm_aux L hL]
    simp only [atEmb_mul, one_mul, mul_one, e, map_neg, eL, ← sL_apply]
    congr 1 <;> split_ifs <;> first | rfl | (match_scalars <;> ring)
  · rw [← sub_eq_zero, eL_comm_aux L hL]
    by_cases hw : InfinitePlace.mk τ = InfinitePlace.mk τ'
    · obtain rfl : ComplexEmbedding.conjugate τ = τ' := (InfinitePlace.mk_eq_iff.1 hw).resolve_left h
      have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by rw [atEmb_eq]; simp
      have e' : atEmb τ (-1) = -atEmb τ 1 := by rw [atEmb_eq]; simp
      simp [atEmb_conj, atEmb_mul, e, e']
    · simp [atEmb_mul_of_ne hw]

end HolAndLieHom

section ExpGeneration

open scoped Matrix.Norms.Operator

theorem expGenC (n : ℕ) (H : Submonoid (Matrix (Fin n) (Fin n) ℂ))
    (hH : ∀ X : Matrix (Fin n) (Fin n) ℂ, NormedSpace.exp X ∈ H)
    (g : Matrix (Fin n) (Fin n) ℂ) (hg : g.det ≠ 0) : g ∈ H := by
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero (fun M => M ∈ H) g hg ?_ ?_ ?_
  · intro D hD
    have hD' : ∀ i, D i ≠ 0 := by
      rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff] at hD; exact fun i => hD i (Finset.mem_univ i)
    have := hH (Matrix.diagonal fun i => Complex.log (D i))
    rw [Matrix.exp_diagonal] at this
    convert this using 2; funext i; rw [Pi.exp_def]; simp only [← Complex.exp_eq_exp_ℂ]; exact (Complex.exp_log (hD' i)).symm
  · intro t
    have := hH (Matrix.single t.i t.j t.c)
    rw [expSq _ (Matrix.single_mul_single_of_ne _ _ _ _ t.hij.symm _)] at this; exact this
  · intro A B _ _ hA hB; exact H.mul_mem hA hB

private theorem exp_map_eval {ι : Type*} [Fintype ι] {a : ℕ} (X : Matrix (Fin a) (Fin a) (ι → ℂ)) (w : ι) :
    (NormedSpace.exp X).map (fun x => x w) = NormedSpace.exp (X.map fun x => x w) :=
  NormedSpace.map_exp ((Pi.evalRingHom (fun _ : ι => ℂ) w).mapMatrix (m := Fin a))
    (Continuous.matrix_map continuous_id (continuous_apply w)) X

private theorem gen_pi {ι : Type*} [Fintype ι] {a : ℕ} (H : Submonoid (Matrix (Fin a) (Fin a) (ι → ℂ)))
    (hH : ∀ X, NormedSpace.exp X ∈ H) (y : Matrix (Fin a) (Fin a) (ι → ℂ)) (hy : IsUnit y) : y ∈ H := by
  classical
  let e : Matrix (Fin a) (Fin a) (ι → ℂ) ≃+* (ι → Matrix (Fin a) (Fin a) ℂ) :=
    Matrix.piRingEquiv (β := fun _ : ι => ℂ)
  have he : ∀ X w, e X w = X.map (fun x => x w) := fun _ _ => rfl
  let H' : Submonoid (ι → Matrix (Fin a) (Fin a) ℂ) := H.comap (e.symm : _ →* _)
  have h1 : ∀ (w : ι) (g : Matrix (Fin a) (Fin a) ℂ), g.det ≠ 0 → Pi.mulSingle w g ∈ H' := by
    intro w g hg
    refine expGenC a (H'.comap (MonoidHom.mulSingle (fun _ : ι => Matrix (Fin a) (Fin a) ℂ) w)) ?_ g hg
    intro X; change e.symm (Pi.mulSingle w (NormedSpace.exp X)) ∈ H
    have : e.symm (Pi.mulSingle w (NormedSpace.exp X)) = NormedSpace.exp (e.symm (Pi.single w X)) := by
      rw [RingEquiv.symm_apply_eq]; funext v
      rw [he, exp_map_eval, ← he, RingEquiv.apply_symm_apply]
      by_cases hv : v = w
      · subst hv; simp
      · simp [hv]
    rw [this]; exact hH _
  have h2 : ∀ w, (e y w).det ≠ 0 := fun w =>
    ((Matrix.isUnit_iff_isUnit_det _).1 ((hy.map e).map (Pi.evalRingHom (fun _ : ι => Matrix (Fin a) (Fin a) ℂ) w))).ne_zero
  have h3 : ∀ s : Finset ι, s.piecewise (e y) 1 ∈ H' := by
    intro s; induction s using Finset.induction_on with
    | empty => simp [H'.one_mem]
    | insert w s hw ih =>
      have : (insert w s).piecewise (e y) 1 = Pi.mulSingle w (e y w) * s.piecewise (e y) 1 := by
        funext v; by_cases hv : v = w
        · subst hv; simp [Finset.piecewise, hw]
        · simp [Finset.piecewise, hv]
      rw [this]; exact H'.mul_mem (h1 w _ (h2 w)) ih
  have h4 := h3 Finset.univ; rw [Finset.piecewise_univ] at h4
  have h5 : e.symm (e y) ∈ H := h4
  rwa [RingEquiv.symm_apply_apply] at h5

theorem expGen {E : Type} [Field E] [NumberField E] (a : ℕ) (H : Submonoid (GL (Fin a) (Cinf E)))
    (hH : ∀ (X : Matrix (Fin a) (Fin a) (Cinf E)) (y : GL (Fin a) (Cinf E)), y.val = NormedSpace.exp X → y ∈ H)
    (y : GL (Fin a) (Cinf E)) : y ∈ H := by
  have h : y.val ∈ H.map (Units.coeHom _) := by
    refine gen_pi (ι := InfinitePlace E) (H.map (Units.coeHom _)) ?_ y.val y.isUnit
    intro X; obtain ⟨u, hu⟩ := Matrix.isUnit_exp X; exact ⟨u, hH X u hu, hu⟩
  obtain ⟨u, hu, h'⟩ := h; exact (Units.ext h').symm ▸ hu

private theorem oneParam_eq_exp {n : ℕ} (F : ℝ → Matrix (Fin n) (Fin n) ℂ) (D : Matrix (Fin n) (Fin n) ℂ)
    (h0 : F 0 = 1) (hadd : ∀ s t, F (s + t) = F s * F t) (hD : HasDerivAt F D 0) :
    F 1 = NormedSpace.exp D := by
  have h1 : ∀ t, HasDerivAt F (F t * D) t := fun t => by
    have h2 : HasDerivAt (fun s => F (s - t)) D t :=
      HasDerivAt.comp_sub_const (f := F) (f' := D) t t (by rw [sub_self]; exact hD)
    refine (h2.const_mul (F t)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    change F s = F t * F (s - t); rw [← hadd, add_sub_cancel]
  have h4 : ∀ t, HasDerivAt (fun t : ℝ => F t * NormedSpace.exp (t • -D)) 0 t := fun t => by
    have h := (h1 t).mul (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-D) t)
    have e : F t * D * NormedSpace.exp (t • -D) + F t * (-D * NormedSpace.exp (t • -D)) = 0 := by
      rw [neg_mul, mul_neg, mul_assoc, add_neg_cancel]
    exact h.congr_deriv e
  have h5 := is_const_of_deriv_eq_zero (fun t => (h4 t).differentiableAt) (fun t => (h4 t).deriv) 1 0
  simp only [one_smul, zero_smul, NormedSpace.exp_zero, h0, mul_one] at h5
  have h6 : NormedSpace.exp (-D) * NormedSpace.exp D = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl D).neg_left, neg_add_cancel, NormedSpace.exp_zero]
  rw [← mul_one (F 1), ← h6, ← mul_assoc, h5, one_mul]

theorem expMat {E : Type} [Field E] [NumberField E] {a : ℕ} (Ξ : AlgRep E a)
    (X : Matrix (Fin a) (Fin a) (Cinf E)) (y : GL (Fin a) (Cinf E)) (hy : y.val = NormedSpace.exp X) :
    Ξ.mat y = NormedSpace.exp (Ξ.dmat (toL X)) := by
  have e : y = (Matrix.isUnit_exp X).unit := Units.ext hy
  rw [e]
  let c : ℝ → GL (Fin a) (Cinf E) := fun t => (Matrix.isUnit_exp (t • X)).unit
  have hc : ∀ t, (c t).val = NormedSpace.exp (t • X) := fun _ => rfl
  have h0 : c 0 = 1 := Units.ext (by simp [c])
  have hadd : ∀ s t, c (s + t) = c s * c t := fun s t => Units.ext (by
    rw [Units.val_mul, hc, hc, hc, add_smul,
      Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left s).smul_right t)])
  have h1 : HasDerivAt (fun t => (c t).val) X 0 := by
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0; rw [zero_smul, NormedSpace.exp_zero, one_mul] at h; exact h
  have h2 := hasDerivAt_mat Ξ c (toL X) h0 h1
  have h3 := oneParam_eq_exp (fun t => Ξ.mat (c t)) _ (by simp only [h0, map_one])
    (fun s t => by simp only [hadd, map_mul]) h2
  have e' : (Matrix.isUnit_exp X).unit = c 1 := Units.ext (by rw [hc, one_smul]; rfl)
  rw [e']; exact h3

theorem expSub (d d' : ℕ) (S : Subalgebra ℂ (Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d') (Fin d') ℂ))
    (A : Matrix (Fin d) (Fin d) ℂ) (B : Matrix (Fin d') (Fin d') ℂ) (h : (A, B) ∈ S) :
    (NormedSpace.exp A, NormedSpace.exp B) ∈ S := by
  have hc : IsClosed (S : Set (Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d') (Fin d') ℂ)) :=
    Submodule.closed_of_finiteDimensional (Subalgebra.toSubmodule S)
  have hA : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • A ^ n) (NormedSpace.exp A) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A
  have hB : HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • B ^ n) (NormedSpace.exp B) :=
    NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) B
  refine hc.mem_of_tendsto (hA.prodMk hB) (Filter.Eventually.of_forall fun s => ?_)
  exact S.sum_mem fun n _ => S.smul_mem (S.pow_mem h n) ((n.factorial : ℂ)⁻¹)

end ExpGeneration

section LieDecompAndPairAlg

private theorem scalarDecomp {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : Type*}
    [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N] (l : Cinf E →ₗ[ℝ] N) (x : Cinf E) :
    l x = ∑ τ : E →+* ℂ, coord τ x • ((1 / 2 : ℂ) • (l (atEmb τ 1) - Complex.I • l (atEmb τ Complex.I))) := by
  classical
  have e : x = ∑ w : InfinitePlace E, atEmb w.embedding (x w) := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    refine Finset.sum_congr rfl fun w _ => ?_
    unfold atEmb; rw [if_pos (by rw [InfinitePlace.mk_embedding])]; congr 1; simp
  rw [← Finset.sum_fiberwise Finset.univ InfinitePlace.mk]
  conv_lhs => rw [e, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := fun h =>
    InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)
      (InfinitePlace.isReal_iff.2 (ComplexEmbedding.isReal_iff.2 h.symm))
  have hf : (Finset.univ.filter fun τ : E →+* ℂ => InfinitePlace.mk τ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
    ext τ; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h; have h' : InfinitePlace.mk w.embedding = InfinitePlace.mk τ := by rw [InfinitePlace.mk_embedding, h]
      exact (InfinitePlace.mk_eq_iff.1 h').imp Eq.symm Eq.symm
    · rintro (rfl | rfl)
      · exact InfinitePlace.mk_embedding w
      · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  have e' : atEmb w.embedding (-Complex.I) = -atEmb w.embedding Complex.I := by rw [atEmb_eq]; simp
  rw [hf, Finset.sum_pair hne, coord_conj, coord_embedding, atEmb_eq _ (x w),
    map_add, map_smul, map_smul, ← algebraMap_smul ℂ (x w).re, ← algebraMap_smul ℂ (x w).im]
  simp only [atEmb_conj, map_one, Complex.conj_I, e', map_neg]
  have h1 : algebraMap ℝ ℂ (x w).re = (x w + starRingEnd ℂ (x w)) / 2 := by rw [Complex.add_conj]; simp
  have h2 : algebraMap ℝ ℂ (x w).im = -(x w - starRingEnd ℂ (x w)) * Complex.I / 2 := by
    rw [Complex.sub_conj]; push_cast; change ((x w).im : ℂ) = _; linear_combination ((x w).im : ℂ) * Complex.I_mul_I
  rw [h1, h2]; match_scalars <;> ring

theorem lieDecomp {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (N : Type*)
    [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N] (L : Lie E a →ₗ[ℝ] N)
    (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    L (toL X) = ∑ τ : E →+* ℂ, hol τ L (X.map (coord τ)) := by
  let L' : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] N := L
  change L' X = _
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum, hol_apply, Matrix.map_apply]
  rw [Finset.sum_comm]; conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact scalarDecomp (L' ∘ₗ Matrix.singleLinearMap ℝ i j) (X i j)

theorem pairAlg {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ Ξ' : AlgRep E a)
    (S : Subalgebra ℂ (Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ × Matrix (Fin Ξ'.d) (Fin Ξ'.d) ℂ))
    (h : ∀ τ i j, (eL Ξ.dmat τ i j, eL Ξ'.dmat τ i j) ∈ S) :
    (∀ X, (Ξ.dmat X, Ξ'.dmat X) ∈ S) ∧ ∀ y, (Ξ.mat y, Ξ'.mat y) ∈ S := by
  have h1 : ∀ X : Matrix (Fin a) (Fin a) (Cinf E), (Ξ.dmat (toL X), Ξ'.dmat (toL X)) ∈ S := fun X => by
    have e : (Ξ.dmat (toL X), Ξ'.dmat (toL X)) = ∑ τ : E →+* ℂ, ∑ i, ∑ j,
        (X.map (coord τ)) i j • (eL Ξ.dmat τ i j, eL Ξ'.dmat τ i j) := by
      rw [lieDecomp a _ Ξ.dmat X, lieDecomp a _ Ξ'.dmat X]
      exact Prod.ext (by simp only [hol_apply, Prod.fst_sum, Prod.smul_fst])
        (by simp only [hol_apply, Prod.snd_sum, Prod.smul_snd])
    rw [e]; exact S.sum_mem fun τ _ => S.sum_mem fun i _ => S.sum_mem fun j _ => S.smul_mem (h τ i j) _
  refine ⟨fun X => h1 (Matrix.of X), fun y => ?_⟩
  let H : Submonoid (GL (Fin a) (Cinf E)) :=
    { carrier := {y | (Ξ.mat y, Ξ'.mat y) ∈ S}
      one_mem' := by change (Ξ.mat 1, Ξ'.mat 1) ∈ S; rw [map_one, map_one]; exact S.one_mem
      mul_mem' := fun hx hy => by
        change (Ξ.mat (_ * _), Ξ'.mat (_ * _)) ∈ S; rw [map_mul, map_mul]; exact S.mul_mem hx hy }
  refine expGen a H (fun X y hy => ?_) y
  change (Ξ.mat y, Ξ'.mat y) ∈ S
  rw [expMat Ξ X y hy, expMat Ξ' X y hy]
  exact expSub _ _ S _ _ (h1 X)

end LieDecompAndPairAlg

section AlgIsoAndHW

theorem algIrr {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) :
    IsMultiGl (eEnd Ξ) ∧ ∀ W, Stab (eEnd Ξ) W → W = ⊥ ∨ W = ⊤ := by
  refine ⟨?_, fun W hW => ?_⟩
  · obtain ⟨h1, h2⟩ := eLRel _ Ξ.dmat (dmat_bracket Ξ)
    let f := (Matrix.toLinAlgEquiv' : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin Ξ.d → ℂ)).toAlgHom
    have hf : ∀ τ i j, eEnd Ξ τ i j = f (eL Ξ.dmat τ i j) := fun _ _ _ => rfl
    refine ⟨fun τ i j k l => ?_, fun s t hst i j k l => ?_⟩
    · simpa only [hf, map_sub, map_mul, apply_ite f, map_zero] using congrArg f (h1 τ i j k l)
    · rw [hf, hf, ← map_mul, ← map_mul, h2 s t hst]
  · let S : Subalgebra ℂ (Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ × Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) :=
      { carrier := {p | ∀ w ∈ W, p.1 *ᵥ w ∈ W}
        mul_mem' := fun hp hq w hw => by rw [Prod.fst_mul, ← Matrix.mulVec_mulVec]; exact hp _ (hq w hw)
        add_mem' := fun hp hq w hw => by rw [Prod.fst_add, Matrix.add_mulVec]; exact W.add_mem (hp w hw) (hq w hw)
        algebraMap_mem' := fun c w hw => by
          rw [Algebra.algebraMap_eq_smul_one, Prod.smul_fst, Prod.fst_one, Matrix.smul_mulVec, Matrix.one_mulVec]
          exact W.smul_mem c hw }
    exact Ξ.irred W fun y v hv => (pairAlg a Ξ Ξ S fun τ i j w hw => hW τ i j w hw).2 y v hv

theorem multiHW (ι V : Type*) [Fintype ι] [AddCommGroup V] [Module ℂ V] (n : ℕ)
    (F : ι → Fin n → Fin n → Module.End ℂ V) [FiniteDimensional ℂ V] [Nontrivial V] (hM : IsMultiGl F) :
    ∃ (ν : ι → Fin n → ℂ) (v : V), v ≠ 0 ∧ ∀ t, IsHW (F t) (ν t) v ∧ Dom (ν t) := by
  obtain ⟨hF, hcomm⟩ := hM
  classical
  have hc : ∀ t k i j, F t k k * F t i j - F t i j * F t k k =
      ((if k = i then (1 : ℂ) else 0) - (if j = k then 1 else 0)) • F t i j := fun t k i j => by
    rw [hF t]; by_cases h1 : k = i <;> by_cases h2 : j = k <;> simp_all
  let G : ι → Module.End ℂ V := fun s => ∑ k : Fin n, ((k : ℕ) : ℂ) • F s k k
  have hG : ∀ t i j, G t * F t i j - F t i j * G t = (((i : ℕ) : ℂ) - (j : ℕ)) • F t i j := fun t i j => by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    simp only [smul_mul_assoc, mul_smul_comm, ← smul_sub, hc, smul_smul, ← Finset.sum_smul]; simp [mul_sub]
  have hG' : ∀ s t, s ≠ t → ∀ i j, G s * F t i j - F t i j * G s = 0 := fun s t hst i j => by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_eq_zero fun k _ => by rw [smul_mul_assoc, mul_smul_comm, hcomm s t hst, sub_self]
  let H : Module.End ℂ V := ∑ s, G s
  have hH : ∀ t i j, H * F t i j = F t i j * H + (((i : ℕ) : ℂ) - (j : ℕ)) • F t i j := fun t i j => by
    rw [← sub_eq_iff_eq_add', Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
      Finset.sum_eq_single t (fun s _ hs => hG' s t hs i j) (by simp), hG]
  obtain ⟨l, hl, hmin⟩ := Set.exists_min_image {c | H.HasEigenvalue c} Complex.re
    (Module.End.finite_hasEigenvalue H) (exists_eigenvalue H)
  obtain ⟨v, hv, hv0, ν, hν⟩ := exists_joint_eigenvector (fun p : ι × Fin n => F p.1 p.2 p.2)
    (fun ⟨s, i⟩ ⟨t, j⟩ => by
      by_cases hst : s = t
      · subst hst; rw [← sub_eq_zero, hc]; by_cases h : i = j <;> simp [h, eq_comm]
      · exact hcomm s t hst _ _ _ _)
    (H.eigenspace l) hl
    (fun k v hv => by rw [Module.End.mem_eigenspace_iff] at hv ⊢; rw [← Module.End.mul_apply, hH]; simp [hv])
  rw [Module.End.mem_eigenspace_iff] at hv
  have hup : ∀ t i j, i < j → F t i j v = 0 := fun t i j hij => by
    by_contra h0
    have h1 : H (F t i j v) = (l + (((i : ℕ) : ℂ) - (j : ℕ))) • F t i j v := by
      rw [← Module.End.mul_apply, hH]; simp [hv, add_smul]
    have h2 := hmin _ (Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 h1, h0⟩)
    simp at h2; exact absurd hij (not_lt.2 h2)
  have hν' : ∀ t k, F t k k v = ν (t, k) • v := fun t k => hν (t, k)
  refine ⟨fun t k => ν (t, k), v, hv0, fun t => ⟨⟨hν' t, hup t⟩, fun i j hij =>
    exists_nat_of_primitive (F t i j) (F t j i) (F t i i - F t j j) ?_ ?_ v _ hv0 (hup t i j hij) ?_⟩⟩
  · rw [hF t]; simp
  · have h1 := hc t i j i; have h2 := hc t j j i; simp only [hij.ne, if_false, if_true] at h1 h2
    rw [sub_mul, mul_sub]; linear_combination (norm := module) h1 - h2
  · simp [hν', sub_smul]

theorem lowStab (ι V : Type*) [Fintype ι] [AddCommGroup V] [Module ℂ V] (n : ℕ)
    (F : ι → Fin n → Fin n → Module.End ℂ V) (hF : IsMultiGl F)
    (ν : ι → Fin n → ℂ) (v : V) (hv : ∀ t, IsHW (F t) (ν t) v) :
    v ∈ low F v ∧ Stab F (low F v) := by
  classical
  obtain ⟨hgl, hcomm⟩ := hF
  have hvlow : v ∈ low F v := by unfold low; rw [Submodule.mem_sInf]; exact fun _ hp => hp.1
  have hlow : ∀ t (i j : Fin n), j < i → ∀ w ∈ low F v, F t i j w ∈ low F v := fun t i j hji w hw => by
    unfold low at hw ⊢; rw [Submodule.mem_sInf] at hw ⊢; exact fun p hp => hp.2 t i j hji w (hw p hp)
  let W' : Submodule ℂ V := low F v ⊓ ⨅ t, ⨅ i, ⨅ j, (low F v).comap (F t i j)
  have hmem : ∀ w, w ∈ W' ↔ w ∈ low F v ∧ ∀ t i j, F t i j w ∈ low F v := fun w => by
    simp [W', Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]
  have hvW : v ∈ W' := by
    rw [hmem]; refine ⟨hvlow, fun t i j => ?_⟩
    rcases lt_trichotomy i j with h | h | h
    · rw [(hv t).2 i j h]; exact zero_mem _
    · subst h; rw [(hv t).1 i]; exact Submodule.smul_mem _ _ hvlow
    · exact hlow t i j h v hvlow
  have hWst : ∀ t (k l : Fin n), l < k → ∀ w ∈ W', F t k l w ∈ W' := fun t k l hlk w hw => by
    rw [hmem] at hw ⊢
    refine ⟨hlow t k l hlk w hw.1, fun s i j => ?_⟩
    by_cases hst : s = t
    · subst hst
      have h1 := congrArg (fun f : Module.End ℂ V => f w) (hgl s i j k l)
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at h1
      rw [sub_eq_iff_eq_add] at h1; rw [h1]
      refine add_mem (sub_mem ?_ ?_) (hlow s k l hlk _ (hw.2 s i j))
      · split_ifs
        · exact hw.2 s i l
        · rw [LinearMap.zero_apply]; exact zero_mem _
      · split_ifs
        · exact hw.2 s k j
        · rw [LinearMap.zero_apply]; exact zero_mem _
    · have h1 := congrArg (fun f : Module.End ℂ V => f w) (hcomm s t hst i j k l)
      simp only [Module.End.mul_apply] at h1; rw [h1]; exact hlow t k l hlk _ (hw.2 s i j)
  have hle : low F v ≤ W' := by unfold low; exact sInf_le ⟨hvW, hWst⟩
  exact ⟨hvlow, fun t i j w hw => ((hmem w).mp (hle hw)).2 t i j⟩

private theorem weight_operator_commutator_multiGl {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℂ V]
    {n : ℕ} (F : ι → Fin n → Fin n → Module.End ℂ V) (hF : IsMultiGl F) (t : ι) (i j : Fin n) (x : V) :
    (∑ s, ∑ a : Fin n, ((a : ℕ) : ℂ) • F s a a) (F t i j x) =
      F t i j ((∑ s, ∑ a : Fin n, ((a : ℕ) : ℂ) • F s a a) x) +
        (((i : ℕ) : ℂ) - ((j : ℕ) : ℂ)) • F t i j x := by
  classical
  obtain ⟨hgl, hcomm⟩ := hF
  have key : ∀ s (a : Fin n), F s a a (F t i j x) = F t i j (F s a a x) +
      (if s = t then ((if a = i then F t a j x else 0) - (if j = a then F t i a x else 0)) else 0) := by
    intro s a; by_cases hst : s = t
    · subst hst; rw [if_pos rfl]
      have h1 := congrArg (fun f : Module.End ℂ V => f x) (hgl s a a i j)
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at h1
      have h2 : (if a = i then F s a j x else 0) - (if j = a then F s i a x else 0) =
          (if a = i then F s a j else 0) x - (if j = a then F s i a else 0) x := by split_ifs <;> simp
      rw [h2, ← h1]; abel
    · rw [if_neg hst]
      have h1 := congrArg (fun f : Module.End ℂ V => f x) (hcomm s t hst a a i j)
      simp only [Module.End.mul_apply] at h1; rw [h1, add_zero]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, key, smul_add, Finset.sum_add_distrib, map_sum, map_smul]
  congr 1
  simp [smul_ite, smul_sub, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.sum_ite_irrel, sub_smul]

theorem lowLine (ι V : Type*) [Fintype ι] [AddCommGroup V] [Module ℂ V] (n : ℕ)
    (F : ι → Fin n → Fin n → Module.End ℂ V) (hF : IsMultiGl F) (ν : ι → Fin n → ℂ) (v : V)
    (hv : ∀ t, IsHW (F t) (ν t) v) (w : V) (hw : w ∈ low F v) (hwν : ∀ t k, F t k k w = ν t k • w) :
    ∃ c : ℂ, w = c • v := by
  classical
  set H : Module.End ℂ V := ∑ s, ∑ a : Fin n, ((a : ℕ) : ℂ) • F s a a with hH
  set l0 : ℂ := ∑ s, ∑ a : Fin n, ((a : ℕ) : ℂ) * ν s a with hl0
  have hHx : ∀ x : V, (∀ s k, F s k k x = ν s k • x) → H x = l0 • x := fun x hx => by
    simp only [hH, hl0, LinearMap.sum_apply, LinearMap.smul_apply, hx, smul_smul, Finset.sum_smul]
  have hsh : ∀ t (i j : Fin n) (μ : ℂ) (x : V), H x = μ • x →
      H (F t i j x) = (μ + (((i : ℕ) : ℂ) - ((j : ℕ) : ℂ))) • F t i j x := fun t i j μ x hx => by
    rw [hH, weight_operator_commutator_multiGl F hF t i j x, ← hH, hx, map_smul, add_smul]
  have hdist : ∀ i j : Fin n, j < i → ∃ d : ℕ, ((i : ℕ) : ℂ) - ((j : ℕ) : ℂ) = (d : ℂ) + 1 := fun i j hji => by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt (show (j : ℕ) < (i : ℕ) from hji)
    refine ⟨d, ?_⟩; rw [hd]; push_cast; ring
  let M : Submodule ℂ V := ⨆ k : ℕ, H.eigenspace (l0 + ((k : ℂ) + 1))
  have hFM : ∀ t (i j : Fin n), j < i → ∀ z ∈ M, F t i j z ∈ M := fun t i j hji z hz => by
    obtain ⟨d, hd⟩ := hdist i j hji
    refine Submodule.iSup_induction _ (motive := fun z => F t i j z ∈ M) hz ?_ (by simp) fun x y hx hy => by
      rw [map_add]; exact add_mem hx hy
    intro k z hz; rw [Module.End.mem_eigenspace_iff] at hz
    refine (le_iSup (fun k : ℕ => H.eigenspace (l0 + ((k : ℂ) + 1))) (k + d + 1)) ?_
    rw [Module.End.mem_eigenspace_iff, hsh t i j _ z hz, hd]; congr 1; push_cast; ring
  let P : Submodule ℂ V := (ℂ ∙ v) ⊔ M
  have hvP : v ∈ P := Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)
  have hPst : ∀ t (i j : Fin n), j < i → ∀ x ∈ P, F t i j x ∈ P := fun t i j hji x hx => by
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [map_add, map_smul]
    refine Submodule.mem_sup_right (add_mem (Submodule.smul_mem _ _ ?_) (hFM t i j hji z hz))
    obtain ⟨d, hd⟩ := hdist i j hji
    refine (le_iSup (fun k : ℕ => H.eigenspace (l0 + ((k : ℂ) + 1))) d) ?_
    rw [Module.End.mem_eigenspace_iff, hsh t i j l0 v (hHx v (fun s k => (hv s).1 k)), hd]
  have hle : low F v ≤ P := by unfold low; exact sInf_le ⟨hvP, hPst⟩
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hle hw)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hHz : H z = l0 • z := by
    have e3 : z = w - c • v := by rw [← hyz]; abel
    rw [e3, map_sub, map_smul, hHx w hwν, hHx v (fun s k => (hv s).1 k), smul_sub, smul_comm]
  have hMle : M ≤ ⨆ μ, ⨆ (_ : μ ≠ l0), H.eigenspace μ := by
    refine iSup_le fun k => le_iSup₂_of_le (l0 + ((k : ℂ) + 1)) ?_ le_rfl
    intro h; have h2 : ((k : ℂ) + 1) = 0 := by linear_combination h
    exact Nat.cast_add_one_ne_zero k h2
  have hz0 : z = 0 := (Submodule.disjoint_def.mp ((Module.End.eigenspaces_iSupIndep H) l0)) z
    (Module.End.mem_eigenspace_iff.mpr hHz) (hMle hz)
  exact ⟨c, by rw [← hyz, hz0, add_zero]⟩

theorem wtEq (n : ℕ) (ν ν' : Fin n → ℂ) (hν : Dom ν) (hν' : Dom ν')
    (hp : ∀ u : ℂ, ∏ k : Fin n, (u - (k : ℂ) + ν k) = ∏ k : Fin n, (u - (k : ℂ) + ν' k)) : ν = ν' := by
  classical
  have key : ∀ μ : Fin n → ℂ, Dom μ → ∀ i : Fin n,
      (Multiset.filter (fun y => ∃ k : ℕ, y - (μ i - (i : ℂ)) = (k : ℂ) + 1)
        (Multiset.map (fun j : Fin n => μ j - (j : ℂ)) Finset.univ.val)).card = (i : ℕ) := by
    intro μ hμ i
    have hP : ∀ j : Fin n, (∃ k : ℕ, μ j - (j : ℂ) - (μ i - (i : ℂ)) = (k : ℂ) + 1) ↔ j < i := by
      intro j; constructor
      · rintro ⟨k, hk⟩; by_contra hji
        rcases (not_lt.1 hji).lt_or_eq with hij | hij
        · obtain ⟨m, hm⟩ := hμ i j hij
          have h1 : (((i : ℕ) : ℕ) : ℂ) = ((k + 1 + m + (j : ℕ) : ℕ) : ℂ) := by
            push_cast; linear_combination hk + hm
          have h2 : (i : ℕ) = k + 1 + m + (j : ℕ) := Nat.cast_injective h1
          have h3 : (i : ℕ) < (j : ℕ) := hij; omega
        · subst hij
          have h1 : ((k + 1 : ℕ) : ℂ) = ((0 : ℕ) : ℂ) := by push_cast; linear_combination -hk
          have h2 : k + 1 = 0 := Nat.cast_injective h1; omega
      · intro hji; obtain ⟨m, hm⟩ := hμ j i hji
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt (show (j : ℕ) < (i : ℕ) from hji)
        have hi : ((i : ℕ) : ℂ) = ((j : ℕ) : ℂ) + (d : ℂ) + 1 := by exact_mod_cast hd
        refine ⟨m + d, ?_⟩; push_cast; linear_combination hm + hi
    rw [Multiset.filter_map, Multiset.card_map]
    have hf : Multiset.filter ((fun y => ∃ k : ℕ, y - (μ i - (i : ℂ)) = (k : ℂ) + 1) ∘
        fun j : Fin n => μ j - (j : ℂ)) Finset.univ.val = Multiset.filter (fun j : Fin n => j < i) Finset.univ.val :=
      Multiset.filter_congr fun j _ => hP j
    rw [hf]
    calc (Multiset.filter (fun j : Fin n => j < i) Finset.univ.val).card
        = (Finset.univ.filter (fun j : Fin n => j < i)).card := rfl
      _ = (Finset.Iio i).card := by congr 1; ext j; simp
      _ = (i : ℕ) := Fin.card_Iio i
  have hm : Multiset.map (fun j : Fin n => ν j - (j : ℂ)) Finset.univ.val =
      Multiset.map (fun j : Fin n => ν' j - (j : ℂ)) Finset.univ.val := by
    apply msetSep; intro u; rw [Multiset.map_map, Multiset.map_map]
    have e : ∀ μ : Fin n → ℂ, (Multiset.map ((fun x => u + x) ∘ fun j : Fin n => μ j - (j : ℂ))
        Finset.univ.val).prod = ∏ k : Fin n, (u - (k : ℂ) + μ k) := fun μ => by
      rw [Finset.prod_eq_multiset_prod]; congr 2; funext k; simp only [Function.comp]; ring
    rw [e, e]; exact hp u
  funext i
  have hmem : ν' i - (i : ℂ) ∈ Multiset.map (fun j : Fin n => ν j - (j : ℂ)) Finset.univ.val := by
    rw [hm]; exact Multiset.mem_map.2 ⟨i, by simp, rfl⟩
  obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 hmem
  have h1 := key ν hν j; have h2 := key ν' hν' i
  rw [← hm, ← hj, h1] at h2
  have hji : j = i := Fin.ext h2; subst hji; linear_combination hj

theorem hwIso (ι V : Type*) [Fintype ι] [AddCommGroup V] [Module ℂ V] (n : ℕ)
    (F : ι → Fin n → Fin n → Module.End ℂ V) (V' : Type*) [AddCommGroup V'] [Module ℂ V']
    (F' : ι → Fin n → Fin n → Module.End ℂ V')
    (hF : IsMultiGl F) (hF' : IsMultiGl F')
    (hS : ∀ W, Stab F W → W = ⊥ ∨ W = ⊤) (hS' : ∀ W, Stab F' W → W = ⊥ ∨ W = ⊤)
    (ν : ι → Fin n → ℂ) (v : V) (v' : V') (hv0 : v ≠ 0) (hv0' : v' ≠ 0)
    (hv : ∀ t, IsHW (F t) (ν t) v) (hv' : ∀ t, IsHW (F' t) (ν t) v') :
    ∃ T : V ≃ₗ[ℂ] V', ∀ t i j x, T (F t i j x) = F' t i j (T x) := by
  let P : ι → Fin n → Fin n → Module.End ℂ (V × V') := fun t i j => (F t i j).prodMap (F' t i j)
  have hPa : ∀ t i j (x : V) (y : V'), P t i j (x, y) = (F t i j x, F' t i j y) := fun _ _ _ _ _ => rfl
  have hP : IsMultiGl P := by
    refine ⟨fun t i j k l => LinearMap.ext fun z => ?_, fun s t hst i j k l => LinearMap.ext fun z => ?_⟩
    · have e := LinearMap.congr_fun (hF.1 t i j k l) z.1
      have e' := LinearMap.congr_fun (hF'.1 t i j k l) z.2
      refine Prod.ext (e.trans (by split_ifs <;> rfl)) (e'.trans (by split_ifs <;> rfl))
    · exact Prod.ext (LinearMap.congr_fun (hF.2 s t hst i j k l) z.1)
        (LinearMap.congr_fun (hF'.2 s t hst i j k l) z.2)
  have hvv : ∀ t, IsHW (P t) (ν t) (v, v') := fun t =>
    ⟨fun i => Prod.ext ((hv t).1 i) ((hv' t).1 i), fun i j h => Prod.ext ((hv t).2 i j h) ((hv' t).2 i j h)⟩
  obtain ⟨hm, hst⟩ := lowStab ι (V × V') n P hP ν (v, v') hvv
  have hl := lowLine ι (V × V') n P hP ν (v, v') hvv
  generalize low P (v, v') = W at hm hst hl
  have hA : ∀ y : V', ((0 : V), y) ∈ W → y = 0 := by
    rcases hS' (W.comap (LinearMap.inr ℂ V V')) (fun t i j w hw => by
      have := hst t i j _ hw; rwa [LinearMap.inr_apply, hPa, map_zero] at this) with h | h
    · exact fun y hy => (Submodule.eq_bot_iff _).1 h y hy
    · have h1 : ((0 : V), v') ∈ W := Submodule.eq_top_iff'.1 h v'
      obtain ⟨c, hc⟩ := hl _ h1 fun t k => by rw [hPa, map_zero, (hv' t).1 k, Prod.smul_mk, smul_zero]
      have h2 : c = 0 := (smul_eq_zero.1 (congrArg Prod.fst hc).symm).resolve_right hv0
      rw [h2, zero_smul] at hc; exact absurd (congrArg Prod.snd hc) hv0'
  have hB : ∀ x : V, (x, (0 : V')) ∈ W → x = 0 := by
    rcases hS (W.comap (LinearMap.inl ℂ V V')) (fun t i j w hw => by
      have := hst t i j _ hw; rwa [LinearMap.inl_apply, hPa, map_zero] at this) with h | h
    · exact fun y hy => (Submodule.eq_bot_iff _).1 h y hy
    · have h1 : (v, (0 : V')) ∈ W := Submodule.eq_top_iff'.1 h v
      obtain ⟨c, hc⟩ := hl _ h1 fun t k => by rw [hPa, map_zero, (hv t).1 k, Prod.smul_mk, smul_zero]
      have h2 : c = 0 := (smul_eq_zero.1 (congrArg Prod.snd hc).symm).resolve_right hv0'
      rw [h2, zero_smul] at hc; exact absurd (congrArg Prod.fst hc) hv0
  have hC : W.map (LinearMap.fst ℂ V V') = ⊤ :=
    (hS (W.map (LinearMap.fst ℂ V V')) (fun t i j _ ⟨z, hz, hzx⟩ =>
      ⟨P t i j z, hst t i j z hz, hzx ▸ rfl⟩)).resolve_left
      fun h => hv0 ((Submodule.eq_bot_iff _).1 h v ⟨_, hm, rfl⟩)
  have hD : W.map (LinearMap.snd ℂ V V') = ⊤ :=
    (hS' (W.map (LinearMap.snd ℂ V V')) (fun t i j _ ⟨z, hz, hzx⟩ =>
      ⟨P t i j z, hst t i j z hz, hzx ▸ rfl⟩)).resolve_left
      fun h => hv0' ((Submodule.eq_bot_iff _).1 h v' ⟨_, hm, rfl⟩)
  have b1 : Function.Bijective ((LinearMap.fst ℂ V V').comp W.subtype) := by
    refine ⟨(injective_iff_map_eq_zero _).2 ?_, fun x => ?_⟩
    · rintro ⟨⟨x, y⟩, hz⟩ (rfl : x = 0); exact Subtype.ext (Prod.ext rfl (hA y hz))
    · obtain ⟨z, hz, rfl⟩ := Submodule.eq_top_iff'.1 hC x; exact ⟨⟨z, hz⟩, rfl⟩
  have b2 : Function.Bijective ((LinearMap.snd ℂ V V').comp W.subtype) := by
    refine ⟨(injective_iff_map_eq_zero _).2 ?_, fun x => ?_⟩
    · rintro ⟨⟨x, y⟩, hz⟩ (rfl : y = 0); exact Subtype.ext (Prod.ext (hB x hz) rfl)
    · obtain ⟨z, hz, rfl⟩ := Submodule.eq_top_iff'.1 hD x; exact ⟨⟨z, hz⟩, rfl⟩
  have key : ∀ z : W, ((LinearEquiv.ofBijective _ b1).symm.trans (LinearEquiv.ofBijective _ b2)) z.1.1 = z.1.2 := by
    intro z; have : (LinearEquiv.ofBijective _ b1).symm z.1.1 = z := (LinearEquiv.ofBijective _ b1).symm_apply_apply z
    rw [LinearEquiv.trans_apply, this]; rfl
  refine ⟨(LinearEquiv.ofBijective _ b1).symm.trans (LinearEquiv.ofBijective _ b2), fun t i j x => ?_⟩
  obtain ⟨z, rfl⟩ := b1.2 x
  exact (key ⟨_, hst t i j z.1 z.2⟩).trans (congrArg (F' t i j) (key z).symm)

private theorem hw_prod {E : Type} [Field E] [NumberField E] {a : ℕ} (Ξ : AlgRep E a) (τ : E →+* ℂ)
    (m : Multiset ℂ) (h : AlgInfChar Ξ τ m) (hgl : GlRel (eEnd Ξ τ)) (ν : Fin a → ℂ)
    (v : Fin Ξ.d → ℂ) (hv : v ≠ 0) (hw : IsHW (eEnd Ξ τ) ν v) (u : ℂ) :
    ∏ k : Fin a, (u - (k : ℂ) + ν k) = (m.map (u - ((a : ℂ) - 1) / 2 + ·)).prod := by
  let f := (Matrix.toLinAlgEquiv' : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin Ξ.d → ℂ)).toAlgHom
  have hf : ∀ M v, f M v = M *ᵥ v := fun _ _ => rfl
  have h1 := qdet_hw (fun i j => f (eL Ξ.dmat τ i j)) ν v hgl hw u
  have h2 : qdet (eL Ξ.dmat τ) u =
      (m.map (u - ((a : ℂ) - 1) / 2 + ·)).prod • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) := by
    have h3 := h.2 (u - ((a : ℂ) - 1) / 2); rwa [sub_add_cancel] at h3
  rw [← map_qdet, h2, hf, Matrix.smul_mulVec, Matrix.one_mulVec] at h1
  exact (smul_left_injective ℂ hv h1).symm

theorem algIsoLie {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ Ξ' : AlgRep E a)
    (m : (E →+* ℂ) → Multiset ℂ) (h : ∀ τ, AlgInfChar Ξ τ (m τ)) (h' : ∀ τ, AlgInfChar Ξ' τ (m τ)) :
    ∃ T : (Fin Ξ.d → ℂ) ≃ₗ[ℂ] (Fin Ξ'.d → ℂ), ∀ τ i j v, T (eEnd Ξ τ i j v) = eEnd Ξ' τ i j (T v) := by
  have : Nonempty (Fin Ξ.d) := ⟨⟨0, Ξ.pos⟩⟩
  have : Nonempty (Fin Ξ'.d) := ⟨⟨0, Ξ'.pos⟩⟩
  obtain ⟨hM, hS⟩ := algIrr a Ξ
  obtain ⟨hM', hS'⟩ := algIrr a Ξ'
  obtain ⟨ν, v, hv, hν⟩ := multiHW _ _ a (eEnd Ξ) hM
  obtain ⟨ν', v', hv', hν'⟩ := multiHW _ _ a (eEnd Ξ') hM'
  obtain rfl : ν = ν' := funext fun τ => wtEq a _ _ (hν τ).2 (hν' τ).2 fun u =>
    (hw_prod Ξ τ _ (h τ) (hM.1 τ) _ v hv (hν τ).1 u).trans
      (hw_prod Ξ' τ _ (h' τ) (hM'.1 τ) _ v' hv' (hν' τ).1 u).symm
  exact hwIso _ _ a (eEnd Ξ) _ (eEnd Ξ') hM hM' hS hS' ν v v' hv hv' (fun τ => (hν τ).1) (fun τ => (hν' τ).1)

private def pairSub {d d' : ℕ} (T : (Fin d → ℂ) ≃ₗ[ℂ] (Fin d' → ℂ)) :
    Subalgebra ℂ (Matrix (Fin d) (Fin d) ℂ × Matrix (Fin d') (Fin d') ℂ) where
  carrier := {p | ∀ v, T (p.1 *ᵥ v) = p.2 *ᵥ T v}
  mul_mem' hp hq v := by
    have hp' : ∀ v, T (_ *ᵥ v) = _ *ᵥ T v := hp
    have hq' : ∀ v, T (_ *ᵥ v) = _ *ᵥ T v := hq
    rw [Prod.fst_mul, Prod.snd_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hp', hq']
  add_mem' hp hq v := by
    have hp' : ∀ v, T (_ *ᵥ v) = _ *ᵥ T v := hp
    have hq' : ∀ v, T (_ *ᵥ v) = _ *ᵥ T v := hq
    rw [Prod.fst_add, Prod.snd_add, Matrix.add_mulVec, Matrix.add_mulVec, map_add, hp', hq']
  algebraMap_mem' c v := by
    simp only [Algebra.algebraMap_eq_smul_one, Prod.smul_fst, Prod.smul_snd, Prod.fst_one, Prod.snd_one,
      Matrix.smul_mulVec, Matrix.one_mulVec, map_smul]

theorem algIso {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ Ξ' : AlgRep E a)
    (m : (E →+* ℂ) → Multiset ℂ) (h : ∀ τ, AlgInfChar Ξ τ (m τ)) (h' : ∀ τ, AlgInfChar Ξ' τ (m τ)) :
    ∃ T, IsAlgIso Ξ Ξ' T := by
  obtain ⟨T, hT⟩ := algIsoLie a Ξ Ξ' m h h'
  obtain ⟨h1, h2⟩ := pairAlg a Ξ Ξ' (pairSub T) fun τ i j v => hT τ i j v
  exact ⟨T, fun y v => h2 y v, fun X v => h1 X v⟩

end AlgIsoAndHW

end MultiGLHighestWeights

/-! ## Section 6: Telescoping Retraction, Antipode & Wigner Vanishing (`WignerVanishingGL`) -/

section WignerVanishing

section Tel

variable {X M : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M]

def rp : (n : ℕ) → (Fin n → X →ₗ[ℂ] Module.End ℂ M) → (Fin n → X) → Module.End ℂ M
  | 0, _, _ => 1
  | n + 1, b, x => rp n (Fin.tail b) (Fin.tail x) * b 0 (x 0)

def tel : (n : ℕ) → (Fin n → X →ₗ[ℂ] Module.End ℂ M) → (Fin n → X →ₗ[ℂ] Module.End ℂ M) →
    (X →ₗ[ℂ] M) → (Fin n → X) → M
  | 0, _, _, _, _ => 0
  | n + 1, a, b, f, x =>
    a 0 (x 0) (tel n (Fin.tail a) (Fin.tail b) f (Fin.tail x)) + rp n (Fin.tail b) (Fin.tail x) (f (x 0))

theorem rp_zero (b : Fin 0 → X →ₗ[ℂ] Module.End ℂ M) (x : Fin 0 → X) : rp 0 b x = 1 := rfl
theorem rp_succ {n : ℕ} (b : Fin (n + 1) → X →ₗ[ℂ] Module.End ℂ M) (x : Fin (n + 1) → X) :
    rp (n + 1) b x = rp n (Fin.tail b) (Fin.tail x) * b 0 (x 0) := rfl
theorem tel_zero (a b : Fin 0 → X →ₗ[ℂ] Module.End ℂ M) (f : X →ₗ[ℂ] M) (x : Fin 0 → X) :
    tel 0 a b f x = 0 := rfl
theorem tel_succ {n : ℕ} (a b : Fin (n + 1) → X →ₗ[ℂ] Module.End ℂ M) (f : X →ₗ[ℂ] M) (x : Fin (n + 1) → X) :
    tel (n + 1) a b f x =
      a 0 (x 0) (tel n (Fin.tail a) (Fin.tail b) f (Fin.tail x)) + rp n (Fin.tail b) (Fin.tail x) (f (x 0)) := rfl

def units {n : ℕ} (σ τ : Equiv.Perm (Fin n)) (k : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.single (σ k) (τ k) 1

def eps {n : ℕ} (μ : (Fin n → Matrix (Fin n) (Fin n) ℂ) → M) : M :=
  ∑ τ : Equiv.Perm (Fin n), ∑ σ : Equiv.Perm (Fin n),
    ((Equiv.Perm.sign τ : ℤ) * (Equiv.Perm.sign σ : ℤ)) • μ (units σ τ)

private theorem rpML (n : ℕ) (b : Fin n → X →ₗ[ℂ] Module.End ℂ M) :
    ∃ R : MultilinearMap ℂ (fun _ : Fin n => X) (Module.End ℂ M), ∀ x, R x = rp n b x := by
  induction n with
  | zero => exact ⟨MultilinearMap.constOfIsEmpty ℂ _ 1, fun _ => rfl⟩
  | succ n ih =>
    obtain ⟨R, hR⟩ := ih (Fin.tail b)
    let g : X →ₗ[ℂ] MultilinearMap ℂ (fun _ : Fin n => X) (Module.End ℂ M) :=
      { toFun := fun x0 => (LinearMap.mulRight ℂ (b 0 x0)).compMultilinearMap R
        map_add' := fun _ _ => MultilinearMap.ext fun _ => by simp [mul_add]
        map_smul' := fun _ _ => MultilinearMap.ext fun _ => by simp }
    exact ⟨LinearMap.uncurryLeft (R := ℂ) (M := fun _ : Fin (n + 1) => X) g, fun x => by rw [rp_succ, ← hR]; rfl⟩

theorem telML (n : ℕ) (a b : Fin n → X →ₗ[ℂ] Module.End ℂ M) :
    ∃ T : (X →ₗ[ℂ] M) →ₗ[ℂ] MultilinearMap ℂ (fun _ : Fin n => X) M, ∀ f x, T f x = tel n a b f x := by
  induction n with
  | zero => exact ⟨0, fun _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨T, hT⟩ := ih (Fin.tail a) (Fin.tail b)
    obtain ⟨R, hR⟩ := rpML n (Fin.tail b)
    let g : (X →ₗ[ℂ] M) → X →ₗ[ℂ] MultilinearMap ℂ (fun _ : Fin n => X) M := fun f =>
      { toFun := fun x0 => (a 0 x0).compMultilinearMap (T f) +
          (LinearMap.applyₗ (f x0) : Module.End ℂ M →ₗ[ℂ] M).compMultilinearMap R
        map_add' := fun _ _ => MultilinearMap.ext fun _ => by simp; abel
        map_smul' := fun _ _ => MultilinearMap.ext fun _ => by simp }
    have hg : ∀ (f : X →ₗ[ℂ] M) (x : Fin (n + 1) → X),
        LinearMap.uncurryLeft (R := ℂ) (M := fun _ : Fin (n + 1) => X) (g f) x =
          a 0 (x 0) (T f (Fin.tail x)) + R (Fin.tail x) (f (x 0)) := fun _ _ => rfl
    refine ⟨{ toFun := fun f => LinearMap.uncurryLeft (R := ℂ) (M := fun _ : Fin (n + 1) => X) (g f)
              map_add' := fun u v => MultilinearMap.ext fun y => by
                simp only [_root_.add_apply, hg, map_add, LinearMap.add_apply]; abel
              map_smul' := fun c u => MultilinearMap.ext fun y => by
                simp only [_root_.smul_apply, hg, map_smul, LinearMap.smul_apply, RingHom.id_apply, smul_add] },
      fun f x => by rw [tel_succ, ← hT, ← hR]; exact hg f x⟩

private theorem telSum_commute_rp (T : Module.End ℂ M) :
    ∀ (n : ℕ) (b : Fin n → X →ₗ[ℂ] Module.End ℂ M), (∀ j y, Commute T (b j y)) →
      ∀ x : Fin n → X, Commute T (rp n b x)
  | 0, _, _, _ => by rw [rp_zero]; exact Commute.one_right T
  | n + 1, b, h, x => by
    rw [rp_succ]; exact (telSum_commute_rp T n (Fin.tail b) (fun j y => h j.succ y) (Fin.tail x)).mul_right (h 0 (x 0))

theorem telSum (n : ℕ) (a b : Fin n → X →ₗ[ℂ] Module.End ℂ M)
    (hc : ∀ i j x y, Commute (a i x) (b j y)) (m : M) (f : X →ₗ[ℂ] M) (hf : ∀ i y, f y = a i y m - b i y m) :
    ∀ x : Fin n → X, tel n a b f x = (List.ofFn fun i => a i (x i)).prod m - rp n b x m := by
  induction n with
  | zero => intro x; rw [tel_zero, rp_zero]; simp
  | succ n ih =>
    intro x
    have h1 := ih (Fin.tail a) (Fin.tail b) (fun i j u v => hc i.succ j.succ u v) (fun i y => hf i.succ y) (Fin.tail x)
    have h2 : Commute (a 0 (x 0)) (rp n (Fin.tail b) (Fin.tail x)) :=
      telSum_commute_rp _ n _ (fun j y => hc 0 j.succ (x 0) y) _
    have h3 : a 0 (x 0) (rp n (Fin.tail b) (Fin.tail x) m) = rp n (Fin.tail b) (Fin.tail x) (a 0 (x 0) m) :=
      LinearMap.congr_fun h2.eq m
    rw [tel_succ, rp_succ, h1, hf 0 (x 0), List.ofFn_succ, List.prod_cons, map_sub, map_sub, h3,
      Module.End.mul_apply, Module.End.mul_apply]
    simp only [Fin.tail]; abel

private theorem rp_comm (κ : Module.End ℂ M) (g : X → X) :
    ∀ (n : ℕ) (b : Fin n → X →ₗ[ℂ] Module.End ℂ M), (∀ i y, κ * b i y = b i (g y) * κ) →
      ∀ x : Fin n → X, κ * rp n b x = rp n b (fun i => g (x i)) * κ
  | 0, _, _, _ => by rw [rp_zero, rp_zero, mul_one, one_mul]
  | n + 1, b, hb, x => by
    have h := rp_comm κ g n (Fin.tail b) (fun i y => hb i.succ y) (Fin.tail x)
    rw [rp_succ, rp_succ, ← mul_assoc, h, mul_assoc, hb, ← mul_assoc]; rfl

theorem telGrp (n : ℕ) (a b : Fin n → X →ₗ[ℂ] Module.End ℂ M) (κ : Module.End ℂ M) (g : X → X)
    (ha : ∀ i y, κ * a i y = a i (g y) * κ) (hb : ∀ i y, κ * b i y = b i (g y) * κ)
    (f f' : X →ₗ[ℂ] M) (hf : ∀ y, κ (f y) = f' (g y)) :
    ∀ x : Fin n → X, κ (tel n a b f x) = tel n a b f' fun i => g (x i) := by
  induction n with
  | zero => intro x; rw [tel_zero, tel_zero, map_zero]
  | succ n ih =>
    intro x
    have h1 := ih (Fin.tail a) (Fin.tail b) (fun i y => ha i.succ y) (fun i y => hb i.succ y) (Fin.tail x)
    have h2 := LinearMap.congr_fun (rp_comm κ g n (Fin.tail b) (fun i y => hb i.succ y) (Fin.tail x)) (f (x 0))
    have h3 := LinearMap.congr_fun (ha 0 (x 0)) (tel n (Fin.tail a) (Fin.tail b) f (Fin.tail x))
    simp only [Module.End.mul_apply] at h2 h3
    rw [tel_succ, tel_succ, map_add, h2, h3, h1, hf]; rfl

private theorem rpDer (D : Module.End ℂ M) (g : X → X) :
    ∀ (n : ℕ) (b : Fin n → X →ₗ[ℂ] Module.End ℂ M), (∀ i y, D * b i y - b i y * D = b i (g y)) →
      ∀ x : Fin n → X, D * rp n b x = rp n b x * D + ∑ k, rp n b (Function.update x k (g (x k)))
  | 0, _, _, _ => by simp [rp_zero]
  | n + 1, b, hb, x => by
    have h1 := rpDer D g n (Fin.tail b) (fun i y => hb i.succ y) (Fin.tail x)
    have h0 : D * b 0 (x 0) = b 0 (x 0) * D + b 0 (g (x 0)) := by rw [← hb]; abel
    rw [Fin.sum_univ_succ]
    simp only [rp_succ, Fin.tail_update_zero, Fin.tail_update_succ, Function.update_self,
      Function.update_of_ne (Fin.succ_ne_zero _).symm]
    rw [← mul_assoc, h1, add_mul, mul_assoc, h0, Finset.sum_mul, mul_add, mul_assoc, add_assoc]; rfl

theorem telDer (n : ℕ) (a b : Fin n → X →ₗ[ℂ] Module.End ℂ M) (D : Module.End ℂ M) (g : X → X)
    (ha : ∀ i y, D * a i y - a i y * D = a i (g y)) (hb : ∀ i y, D * b i y - b i y * D = b i (g y))
    (f f' : X →ₗ[ℂ] M) (hf : ∀ y, D (f y) = f' y + f (g y)) :
    ∀ x : Fin n → X, D (tel n a b f x) = tel n a b f' x + ∑ k, tel n a b f (Function.update x k (g (x k))) := by
  induction n with
  | zero => intro x; simp [tel_zero]
  | succ n ih =>
    intro x
    have h1 := ih (Fin.tail a) (Fin.tail b) (fun i y => ha i.succ y) (fun i y => hb i.succ y) (Fin.tail x)
    have h2 := rpDer D g n (Fin.tail b) (fun i y => hb i.succ y) (Fin.tail x)
    have h0 : ∀ m, D (a 0 (x 0) m) = a 0 (x 0) (D m) + a 0 (g (x 0)) m := fun m => by rw [← ha]; simp
    have h3 : ∀ m, D (rp n (Fin.tail b) (Fin.tail x) m) = rp n (Fin.tail b) (Fin.tail x) (D m) +
        ∑ k : Fin n, rp n (Fin.tail b) (Function.update (Fin.tail x) k (g (x k.succ))) m := fun m => by
      have := LinearMap.congr_fun h2 m
      simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sum_apply] at this; exact this
    rw [Fin.sum_univ_succ]
    simp only [tel_succ, Fin.tail_update_zero, Fin.tail_update_succ, Function.update_self,
      Function.update_of_ne (Fin.succ_ne_zero _).symm]
    rw [map_add, h0, h3, h1, hf, map_add, map_add, map_sum, Finset.sum_add_distrib]
    simp only [Fin.tail]; abel

end Tel

section EpsInvariance

private theorem eps_left_mul_eq_det_smul {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (μ : MultilinearMap ℂ (fun _ : Fin n => Matrix (Fin n) (Fin n) ℂ) M) (g : Matrix (Fin n) (Fin n) ℂ) :
    eps (fun x => μ fun i => g * x i) = g.det • eps μ := by
  have hs : ∀ a b : Fin n, g * single a b (1 : ℂ) = ∑ c, g c a • single c b (1 : ℂ) := fun a b => by
    ext i j; by_cases hbj : b = j <;> simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, hbj]
  have hdet : ∀ c : Fin n → Fin n, ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ k, g (c k) (σ k) = (g.submatrix c id).det := fun c => by
    rw [← Matrix.det_transpose, Matrix.det_apply']; rfl
  have hsum : ∀ w : (Fin n → Fin n) → M, ∑ c, (g.submatrix c id).det • w c =
      ∑ α : Equiv.Perm (Fin n), (((Equiv.Perm.sign α : ℤ) : ℂ) * g.det) • w α := fun w => by
    rw [← Finset.sum_subset (Finset.subset_univ
      (Finset.univ.image (fun α : Equiv.Perm (Fin n) => (⇑α : Fin n → Fin n))))]
    · rw [Finset.sum_image (fun α _ β _ h => Equiv.coe_fn_injective h)]
      exact Finset.sum_congr rfl fun α _ => by rw [Matrix.det_permute]
    · intro c _ hc
      have hni : ¬ Function.Injective c := fun hinj => hc (Finset.mem_image.mpr
        ⟨Equiv.ofBijective c (Finite.injective_iff_bijective.mp hinj), Finset.mem_univ _, rfl⟩)
      obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.1 hni
      rw [Matrix.det_zero_of_row_eq hne (by ext k; simp [hij]), zero_smul]
  simp only [eps, Finset.smul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hμ : ∀ σ : Equiv.Perm (Fin n), μ (fun i => g * units σ τ i) =
      ∑ c : Fin n → Fin n, (∏ k, g (c k) (σ k)) • μ (fun k => single (c k) (τ k) (1 : ℂ)) := fun σ => by
    simp only [units, hs]; rw [MultilinearMap.map_sum]
    exact Finset.sum_congr rfl fun c _ => MultilinearMap.map_smul_univ _ _ _
  have hc : ∀ c : Fin n → Fin n, ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign τ : ℤ) * (Equiv.Perm.sign σ : ℤ)) • (∏ k, g (c k) (σ k)) •
        μ (fun k => single (c k) (τ k) (1 : ℂ)) =
      ((Equiv.Perm.sign τ : ℤ) : ℂ) • ((g.submatrix c id).det • μ (fun k => single (c k) (τ k) (1 : ℂ))) := fun c => by
    simp only [← Int.cast_smul_eq_zsmul ℂ, smul_smul, ← Finset.sum_smul]
    congr 1; rw [← hdet c, Finset.mul_sum]; refine Finset.sum_congr rfl fun σ _ => ?_; push_cast; ring
  simp only [hμ, Finset.smul_sum]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun c _ => hc c, ← Finset.smul_sum, hsum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_; simp only [← Int.cast_smul_eq_zsmul ℂ, smul_smul]; congr 1; push_cast; ring

theorem epsGrp (M : Type*) [AddCommGroup M] [Module ℂ M] (n : ℕ)
    (μ : MultilinearMap ℂ (fun _ : Fin n => Matrix (Fin n) (Fin n) ℂ) M)
    (g g' : Matrix (Fin n) (Fin n) ℂ) (h : g' * g = 1) :
    eps (fun x => μ fun i => g * x i * g') = eps μ := by
  have hT : ∀ ν : (Fin n → Matrix (Fin n) (Fin n) ℂ) → M, eps (fun x => ν fun i => (x i)ᵀ) = eps ν := fun ν => by
    simp only [eps, units, Matrix.transpose_single]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun σ _ => ?_; rw [mul_comm]; rfl
  have e1 : eps (fun x => μ fun i => g * x i * g') = g.det • eps (fun x => μ fun i => x i * g') :=
    eps_left_mul_eq_det_smul (μ.compLinearMap (fun _ => LinearMap.mulRight ℂ g')) g
  have e2 : eps (fun x => μ fun i => (g'ᵀ * x i)ᵀ) = g'ᵀ.det • eps (fun x => μ fun i => (x i)ᵀ) :=
    eps_left_mul_eq_det_smul
      (μ.compLinearMap (fun _ => (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℂ ℂ).toLinearMap)) g'ᵀ
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.det_transpose, hT] at e2
  have e3 : eps (fun x => μ fun i => x i * g') = g'.det • eps μ := by
    rw [← hT (fun x => μ fun i => x i * g')]; exact e2
  rw [e1, e3, smul_smul, mul_comm, ← Matrix.det_mul, h, Matrix.det_one, one_smul]

private theorem update_swap_mul_eq_update {n : ℕ} (σ : Equiv.Perm (Fin n)) {a b : Fin n} (hab : a ≠ b) :
    Function.update (⇑(Equiv.swap a b * σ)) ((Equiv.swap a b * σ).symm b) a =
      Function.update (⇑σ) (σ.symm b) a := by
  have e : (Equiv.swap a b * σ).symm b = σ.symm a := by simp [Equiv.Perm.mul_def, Equiv.swap_apply_right]
  rw [e]; funext j
  simp only [Function.update_apply, Equiv.Perm.coe_mul, Function.comp_apply, Equiv.eq_symm_apply]
  by_cases h1 : σ j = a
  · simp [h1, hab]
  · by_cases h2 : σ j = b
    · simp [h2, Equiv.swap_apply_right]
    · simp [h1, h2, Equiv.swap_apply_of_ne_of_ne h1 h2]

private theorem sum_sign_smul_update_eq_ite {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (h : (Fin n → Fin n) → M) (a b : Fin n) :
    ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) • h (Function.update (⇑σ) (σ.symm b) a) =
      if a = b then ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) • h ⇑σ else 0 := by
  split_ifs with hab
  · subst hab; refine Finset.sum_congr rfl fun σ _ => ?_
    have := Function.update_eq_self (σ.symm a) (⇑σ); simp only [Equiv.apply_symm_apply] at this; rw [this]
  · have key : ∀ σ : Equiv.Perm (Fin n),
        (Equiv.Perm.sign σ : ℤ) • h (Function.update (⇑σ) (σ.symm b) a) =
          -((Equiv.Perm.sign (Equiv.mulLeft (Equiv.swap a b) σ) : ℤ) •
            h (Function.update (⇑(Equiv.mulLeft (Equiv.swap a b) σ))
              ((Equiv.mulLeft (Equiv.swap a b) σ).symm b) a)) := fun σ => by
      simp only [Equiv.coe_mulLeft]
      rw [update_swap_mul_eq_update σ hab, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab]; simp
    set S := ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) • h (Function.update (⇑σ) (σ.symm b) a) with hSdef
    have hS : S = -S := by
      conv_lhs => rw [hSdef, Finset.sum_congr rfl fun σ _ => key σ, Finset.sum_neg_distrib,
        Equiv.sum_comp (Equiv.mulLeft (Equiv.swap a b))
          (fun τ => (Equiv.Perm.sign τ : ℤ) • h (Function.update (⇑τ) (τ.symm b) a))]
    have h2 : (2 : ℂ) • S = 0 := by rw [two_smul]; nth_rewrite 2 [hS]; exact add_neg_cancel S
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

private theorem update_single_first_index_eq {n : ℕ} (r c : Fin n → Fin n) (k a : Fin n) :
    Function.update (fun j => Matrix.single (r j) (c j) (1 : ℂ)) k (Matrix.single a (c k) 1) =
      fun j => Matrix.single (Function.update r k a j) (c j) (1 : ℂ) := by
  funext j; by_cases hj : j = k <;> simp [hj]

private theorem update_single_col_eq {n : ℕ} (r c : Fin n → Fin n) (k a : Fin n) :
    Function.update (fun j => Matrix.single (r j) (c j) (1 : ℂ)) k (Matrix.single (r k) a 1) =
      fun j => Matrix.single (r j) (Function.update c k a j) (1 : ℂ) := by
  funext j; by_cases hj : j = k <;> simp [hj]

private theorem mul_single_eq_sum_smul_single {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) :
    y * Matrix.single p q (1 : ℂ) = ∑ a, y a p • Matrix.single a q (1 : ℂ) := by
  ext i j; simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, ite_and]

private theorem single_mul_eq_sum_smul_single {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) (p q : Fin n) :
    Matrix.single p q (1 : ℂ) * y = ∑ c, y q c • Matrix.single p c (1 : ℂ) := by
  ext i j; simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, ite_and]

private theorem sum_sign_left_mul_update_eq_trace_smul {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (μ : MultilinearMap ℂ (fun _ : Fin n => Matrix (Fin n) (Fin n) ℂ) M)
    (y : Matrix (Fin n) (Fin n) ℂ) (τ : Equiv.Perm (Fin n)) :
    ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) •
        ∑ k, μ (Function.update (units σ τ) k (y * units σ τ k)) =
      Matrix.trace y • ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) • μ (units σ τ) := by
  set h : (Fin n → Fin n) → M := fun r => μ (fun j => Matrix.single (r j) (τ j) (1 : ℂ)) with hh
  have inner : ∀ σ : Equiv.Perm (Fin n),
      ∑ k, μ (Function.update (units σ τ) k (y * units σ τ k)) =
        ∑ b, ∑ a, y a b • h (Function.update (⇑σ) (σ.symm b) a) := fun σ => by
    have hu : units σ τ = fun j => Matrix.single (σ j) (τ j) (1 : ℂ) := rfl
    rw [hu]; simp_rw [mul_single_eq_sum_smul_single, MultilinearMap.map_update_sum, MultilinearMap.map_update_smul,
      update_single_first_index_eq]
    rw [← Equiv.sum_comp σ.symm]; simp [hh]
  simp_rw [inner, Finset.smul_sum]; rw [Finset.sum_comm]
  have step : ∀ b : Fin n, ∑ σ : Equiv.Perm (Fin n), ∑ a, (Equiv.Perm.sign σ : ℤ) •
      y a b • h (Function.update (⇑σ) (σ.symm b) a) =
      y b b • ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) • h ⇑σ := fun b => by
    rw [Finset.sum_comm]
    simp_rw [smul_comm ((Equiv.Perm.sign _ : ℤ)) (y _ b), ← Finset.smul_sum, sum_sign_smul_update_eq_ite]; simp
  rw [Finset.sum_congr rfl fun b _ => step b, ← Finset.sum_smul, ← Finset.smul_sum]; rfl

private theorem sum_sign_right_mul_update_eq_trace_smul {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (μ : MultilinearMap ℂ (fun _ : Fin n => Matrix (Fin n) (Fin n) ℂ) M)
    (y : Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin n)) :
    ∑ τ : Equiv.Perm (Fin n), (Equiv.Perm.sign τ : ℤ) •
        ∑ k, μ (Function.update (units σ τ) k (units σ τ k * y)) =
      Matrix.trace y • ∑ τ : Equiv.Perm (Fin n), (Equiv.Perm.sign τ : ℤ) • μ (units σ τ) := by
  set h : (Fin n → Fin n) → M := fun c => μ (fun j => Matrix.single (σ j) (c j) (1 : ℂ)) with hh
  have inner : ∀ τ : Equiv.Perm (Fin n),
      ∑ k, μ (Function.update (units σ τ) k (units σ τ k * y)) =
        ∑ b, ∑ c, y b c • h (Function.update (⇑τ) (τ.symm b) c) := fun τ => by
    have hu : units σ τ = fun j => Matrix.single (σ j) (τ j) (1 : ℂ) := rfl
    rw [hu]; simp_rw [single_mul_eq_sum_smul_single, MultilinearMap.map_update_sum, MultilinearMap.map_update_smul,
      update_single_col_eq]
    rw [← Equiv.sum_comp τ.symm]; simp [hh]
  simp_rw [inner, Finset.smul_sum]; rw [Finset.sum_comm]
  have step : ∀ b : Fin n, ∑ τ : Equiv.Perm (Fin n), ∑ c, (Equiv.Perm.sign τ : ℤ) •
      y b c • h (Function.update (⇑τ) (τ.symm b) c) =
      y b b • ∑ τ : Equiv.Perm (Fin n), (Equiv.Perm.sign τ : ℤ) • h ⇑τ := fun b => by
    rw [Finset.sum_comm]
    simp_rw [smul_comm ((Equiv.Perm.sign _ : ℤ)) (y b _), ← Finset.smul_sum, sum_sign_smul_update_eq_ite]; simp
  rw [Finset.sum_congr rfl fun b _ => step b, ← Finset.sum_smul, ← Finset.smul_sum]; rfl

theorem epsDer (M : Type*) [AddCommGroup M] [Module ℂ M] (n : ℕ)
    (μ : MultilinearMap ℂ (fun _ : Fin n => Matrix (Fin n) (Fin n) ℂ) M) (y : Matrix (Fin n) (Fin n) ℂ) :
    eps (fun x => ∑ k, μ (Function.update x k (y * x k - x k * y))) = 0 := by
  change ∑ τ : Equiv.Perm (Fin n), ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign τ : ℤ) * (Equiv.Perm.sign σ : ℤ)) •
        ∑ k, μ (Function.update (units σ τ) k (y * units σ τ k - units σ τ k * y)) = 0
  simp_rw [MultilinearMap.map_update_sub, Finset.sum_sub_distrib, smul_sub, Finset.sum_sub_distrib]
  rw [sub_eq_zero]
  have L : ∀ τ : Equiv.Perm (Fin n), ∑ σ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign τ : ℤ) * (Equiv.Perm.sign σ : ℤ)) •
        ∑ k, μ (Function.update (units σ τ) k (y * units σ τ k)) =
      (Equiv.Perm.sign τ : ℤ) • (Matrix.trace y •
        ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) • μ (units σ τ)) := fun τ => by
    rw [← sum_sign_left_mul_update_eq_trace_smul, Finset.smul_sum]; simp_rw [mul_smul]
  have R : ∀ σ : Equiv.Perm (Fin n), ∑ τ : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign τ : ℤ) * (Equiv.Perm.sign σ : ℤ)) •
        ∑ k, μ (Function.update (units σ τ) k (units σ τ k * y)) =
      (Equiv.Perm.sign σ : ℤ) • (Matrix.trace y •
        ∑ τ : Equiv.Perm (Fin n), (Equiv.Perm.sign τ : ℤ) • μ (units σ τ)) := fun σ => by
    rw [← sum_sign_right_mul_update_eq_trace_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_; rw [mul_comm, mul_smul]
  rw [Finset.sum_congr rfl fun τ _ => L τ, Finset.sum_comm, Finset.sum_congr rfl fun σ _ => R σ]
  simp_rw [smul_comm _ (Matrix.trace y), ← Finset.smul_sum]
  congr 1; simp_rw [Finset.smul_sum, ← mul_smul]; rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [mul_comm]

end EpsInvariance

section GlNegOpAndDualIff

open MulOpposite

private theorem glRel_op {A : Type*} [Ring A] {n : ℕ} {X : Fin n → Fin n → A} (h : GlRel X) :
    GlRel fun i j => op (X j i) := fun a b c d => by
  have h1 := congrArg op (h d c b a)
  simp only [op_sub, op_mul, apply_ite op, op_zero] at h1
  rw [h1]; simp only [eq_comm (a := c) (b := b), eq_comm (a := a) (b := d)]

private theorem qdet_op {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} {X : Fin n → Fin n → A} (h : GlRel X) (y : ℂ) :
    qdet (fun i j => op (X j i)) y = op (qdet X y) := by
  have hP : ∀ (arg : Fin n → ℂ) (σ τ : Equiv.Perm (Fin n)), orderedTermProduct (fun i j => op (X j i)) arg σ τ =
      op (orderedTermProduct X (arg ∘ Fin.revPerm) (τ * Fin.revPerm) (σ * Fin.revPerm)) := fun arg σ τ => by
    unfold orderedTermProduct
    rw [op_list_prod, List.map_ofFn]
    congr 1
    refine List.ext_getElem (by simp) fun k h1 _ => ?_
    have hk : k < n := by simpa using h1
    have e : (⟨n - 1 - k, by omega⟩ : Fin n).rev = ⟨k, hk⟩ := Fin.ext (by rw [Fin.val_rev]; simp only; omega)
    simp only [List.getElem_reverse, List.getElem_ofFn, List.length_ofFn, Function.comp_apply, Equiv.Perm.mul_apply,
      Fin.revPerm_apply, e, capelliTm, op_add, apply_ite op, op_zero, eq_comm (a := τ _)]
    rfl
  have hS : ∀ arg : Fin n → ℂ, doublyAntisymmetrizedProduct (fun i j => op (X j i)) arg =
      op (doublyAntisymmetrizedProduct X (arg ∘ Fin.revPerm)) := fun arg => by
    unfold doublyAntisymmetrizedProduct
    rw [Finset.sum_comm, Finset.op_sum]
    refine Fintype.sum_equiv (Equiv.mulRight Fin.revPerm) _ _ fun σ => ?_
    rw [Finset.op_sum]
    refine Fintype.sum_equiv (Equiv.mulRight Fin.revPerm) _ _ fun τ => ?_
    simp only [hP, ← zsmul_eq_mul, op_smul, smul_smul, Equiv.coe_mulRight, Equiv.Perm.sign_mul, Units.val_mul]
    congr 1
    linear_combination (-((Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign τ : ℤ))) *
      Int.units_coe_mul_self (Equiv.Perm.sign (Fin.revPerm (n := n)))
  have e := hS fun k => y - (k : ℂ)
  rw [antisymmetrizedProduct_perm_invariant, antisymmetrizedProduct_eq_factorial_smul_qdet _ h,
    antisymmetrizedProduct_eq_factorial_smul_qdet _ (glRel_op h), op_smul] at e
  exact (IsUnit.mk0 _ (by exact_mod_cast n.factorial_ne_zero)).smul_left_cancel.mp e

theorem glNegOp (A : Type*) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A) (h : GlRel X) :
    GlRel (fun i j => -op (X i j)) ∧
      ∀ x : ℂ, qdet (fun i j => -op (X i j)) x = op ((-1 : ℂ) ^ n • qdet X ((n : ℂ) - 1 - x)) := by
  refine ⟨fun a b c d => ?_, fun x => ?_⟩
  · have h1 := congrArg op (h c d a b)
    simp only [op_sub, op_mul, apply_ite op, op_zero] at h1
    simp only [neg_mul_neg]; rw [h1]
    simp only [eq_comm (a := d) (b := a), eq_comm (a := b) (b := c)]
    split_ifs <;> abel
  · rw [quantumDet_neg_transpose _ (glRel_op h), qdet_op h, op_smul]

private theorem qdet_negT {d n : ℕ} (X : Fin n → Fin n → Matrix (Fin d) (Fin d) ℂ) (h : GlRel X) (u : ℂ) :
    qdet (fun i j => -(X i j)ᵀ) (u + ((n : ℂ) - 1) / 2) =
      (-1 : ℂ) ^ n • (qdet X (-u + ((n : ℂ) - 1) / 2))ᵀ := by
  have h1 := map_qdet (Matrix.transposeAlgEquiv (Fin d) ℂ ℂ).toAlgHom (fun i j => -(X i j)ᵀ) (u + ((n : ℂ) - 1) / 2)
  have h2 := (glNegOp _ n X h).2 (u + ((n : ℂ) - 1) / 2)
  have e : (fun i j => (Matrix.transposeAlgEquiv (Fin d) ℂ ℂ).toAlgHom (-(X i j)ᵀ)) =
      fun i j => -op (X i j) := by funext i j; simp
  have e' : (n : ℂ) - 1 - (u + ((n : ℂ) - 1) / 2) = -u + ((n : ℂ) - 1) / 2 := by ring
  rw [e, h2, e'] at h1
  have h3 : (qdet (fun i j => -(X i j)ᵀ) (u + ((n : ℂ) - 1) / 2))ᵀ =
      (-1 : ℂ) ^ n • qdet X (-u + ((n : ℂ) - 1) / 2) := op_injective h1
  rw [← Matrix.transpose_smul, ← h3, Matrix.transpose_transpose]

private theorem prod_neg (m : Multiset ℂ) (u : ℂ) :
    ((m.map Neg.neg).map (-u + ·)).prod = (-1) ^ Multiset.card m * (m.map (u + ·)).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons _ _ ih => simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, ih]; ring

theorem dualIff {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a)
    (τ : E →+* ℂ) (m : Multiset ℂ) :
    AlgInfChar Ξ τ (m.map Neg.neg) ↔ HasDualInfChar Ξ τ m := by
  have hR : GlRel (eL Ξ.dmat τ) := (eLRel _ Ξ.dmat (dmat_bracket Ξ)).1 τ
  have hd : dualE Ξ τ = fun i j => -(eL Ξ.dmat τ i j)ᵀ := funext fun i => funext fun j => dualE_eq Ξ τ i j
  have hs : (-1 : ℂ) ^ a * (-1 : ℂ) ^ a = 1 := by rw [← mul_pow]; simp
  change (Multiset.card (m.map Neg.neg) = a ∧ ∀ u : ℂ, qdet (eL Ξ.dmat τ) (u + ((a : ℂ) - 1) / 2) =
    ((m.map Neg.neg).map (u + ·)).prod • (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ)) ↔ _
  unfold HasDualInfChar
  rw [Multiset.card_map, hd]
  refine and_congr_right fun hm => ⟨fun h u => ?_, fun h u => ?_⟩
  · rw [qdet_negT _ hR, h, prod_neg, hm, Matrix.transpose_smul, Matrix.transpose_one, smul_smul, ← mul_assoc, hs, one_mul]
  · have h1 := congrArg (fun M => (-1 : ℂ) ^ a • Mᵀ) (h (-u))
    have h2 := prod_neg m (-u)
    simp only [qdet_negT _ hR, Matrix.transpose_smul, Matrix.transpose_transpose, Matrix.transpose_one,
      smul_smul, hs, one_smul, neg_neg] at h1
    rw [neg_neg, hm] at h2
    rw [h1, h2]

end GlNegOpAndDualIff

section AlphaAndRetraction

private theorem rp_eq {X M : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup M] [Module ℂ M] :
    ∀ (n : ℕ) (b : Fin n → X →ₗ[ℂ] Module.End ℂ M) (x : Fin n → X),
      rp n b x = (List.ofFn fun i => MulOpposite.op (b i (x i))).prod.unop
  | 0, _, _ => by rw [rp_zero]; simp
  | n + 1, b, x => by rw [rp_succ, rp_eq n, List.ofFn_succ, List.prod_cons, MulOpposite.unop_mul]; rfl

private def sh {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M) (c : ℂ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M :=
  A + (c • Matrix.traceLinearMap (Fin n) ℂ ℂ).smulRight 1

private theorem sh_apply {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M) (c : ℂ) (x : Matrix (Fin n) (Fin n) ℂ) :
    sh A c x = A x + (c * x.trace) • (1 : Module.End ℂ M) := rfl

private theorem trace_single' {n : ℕ} (i j : Fin n) :
    (Matrix.single i j (1 : ℂ)).trace = if i = j then 1 else 0 := by
  split_ifs with h
  · subst h; simp
  · simp [Matrix.trace_single_eq_of_ne _ _ _ h]

private theorem sh_single {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M) (c : ℂ) (i j : Fin n) :
    sh A c (Matrix.single i j 1) = capelliTm (fun i j => A (Matrix.single i j 1)) c i j := by
  rw [sh_apply, trace_single', capelliTm]; split_ifs <;> simp [Algebra.algebraMap_eq_smul_one, add_comm]

private theorem sh_single_op {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M) (c : ℂ) (i j : Fin n) :
    MulOpposite.op (sh (-B) c (Matrix.single i j 1)) =
      capelliTm (fun i j => -MulOpposite.op (B (Matrix.single i j 1))) c i j := by
  rw [sh_apply, trace_single', capelliTm]; split_ifs <;> simp [Algebra.algebraMap_eq_smul_one, add_comm]

private def epsL {M : Type*} [AddCommGroup M] [Module ℂ M] (n : ℕ) :
    ((Fin n → Matrix (Fin n) (Fin n) ℂ) → M) →ₗ[ℂ] M where
  toFun := eps
  map_add' _ _ := by simp [eps, Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [eps, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun σ _ => (smul_comm c _ _).symm

private theorem map_eps {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ} (κ : Module.End ℂ M)
    (μ : (Fin n → Matrix (Fin n) (Fin n) ℂ) → M) : κ (eps μ) = eps fun x => κ (μ x) := by
  simp only [eps, map_sum, map_zsmul]

theorem alphaAbs (M : Type*) [AddCommGroup M] [Module ℂ M] (n : ℕ)
    (A B : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M) (arg : Fin n → ℂ)
    (hc : ∀ x y, Commute (A x) (B y)) :
    ∃ α : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M) →ₗ[ℂ] M,
      (∀ (m : M) (f : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M), (∀ x, f x = A x m + B x m) →
        α f = doublyAntisymmetrizedProduct (fun i j => A (Matrix.single i j 1)) arg m -
          (doublyAntisymmetrizedProduct (fun i j => -MulOpposite.op (B (Matrix.single i j 1))) arg).unop m) ∧
      (∀ (κ : Module.End ℂ M) (g g' : Matrix (Fin n) (Fin n) ℂ), g' * g = 1 → (∀ x, κ * A x = A (g * x * g') * κ) →
        (∀ x, κ * B x = B (g * x * g') * κ) → ∀ f f' : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M,
          (∀ x, κ (f x) = f' (g * x * g')) → κ (α f) = α f') ∧
      ∀ (D : Module.End ℂ M) (y : Matrix (Fin n) (Fin n) ℂ), (∀ x, D * A x - A x * D = A (y * x - x * y)) →
        (∀ x, D * B x - B x * D = B (y * x - x * y)) → ∀ f f' : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M,
          (∀ x, D (f x) = f' x + f (y * x - x * y)) → D (α f) = α f' := by
  obtain ⟨T, hT⟩ := telML n (fun i => sh A (arg i)) (fun i => sh (-B) (arg i))
  let α : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] M) →ₗ[ℂ] M :=
    { toFun := fun f => eps (T f)
      map_add' := fun _ _ => by rw [map_add]; exact (epsL n).map_add _ _
      map_smul' := fun _ _ => by rw [map_smul]; exact (epsL n).map_smul _ _ }
  have hα : ∀ f, α f = eps (T f) := fun _ => rfl
  refine ⟨α, fun m f hf => ?_, fun κ g g' hg hA hB f f' hf => ?_, fun D y hA hB f f' hf => ?_⟩
  · have h := telSum n (fun i => sh A (arg i)) (fun i => sh (-B) (arg i))
      (fun i j x y => by
        rw [sh_apply, sh_apply]
        exact ((hc x y).neg_right.add_right ((Commute.one_right _).smul_right _)).add_left
          ((Commute.one_left _).smul_left _))
      m f (fun i x => by rw [hf, sh_apply, sh_apply]; simp)
    rw [hα]
    unfold eps doublyAntisymmetrizedProduct orderedTermProduct
    simp only [hT, h, rp_eq, units, sh_single_op]
    simp only [sh_single, ← zsmul_eq_mul, smul_smul, Finset.unop_sum,
      MulOpposite.unop_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_sub, Finset.sum_sub_distrib]
  · have htr : ∀ x : Matrix (Fin n) (Fin n) ℂ, (g * x * g').trace = x.trace := fun x => by
      rw [Matrix.trace_mul_cycle, hg, one_mul]
    have h := telGrp n (fun i => sh A (arg i)) (fun i => sh (-B) (arg i)) κ (fun x => g * x * g')
      (fun i x => by rw [sh_apply, sh_apply, htr, mul_add, add_mul, hA]; simp)
      (fun i x => by rw [sh_apply, sh_apply, htr, mul_add, add_mul, LinearMap.neg_apply, LinearMap.neg_apply, mul_neg, hB]; simp)
      f f' hf
    rw [hα, hα, map_eps, ← epsGrp M n (T f') g g' hg]; simp only [hT, h]
  · have htr : ∀ x : Matrix (Fin n) (Fin n) ℂ, (y * x - x * y).trace = 0 := fun x => by
      rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
    have h := telDer n (fun i => sh A (arg i)) (fun i => sh (-B) (arg i)) D (fun x => y * x - x * y)
      (fun i x => by rw [sh_apply, sh_apply, htr, mul_add, add_mul, ← hA]; simp)
      (fun i x => by rw [sh_apply, sh_apply, htr, mul_add, add_mul, LinearMap.neg_apply, LinearMap.neg_apply, ← hB]; simp; abel)
      f f' hf
    have e : (fun x => D (T f x)) = ⇑(T f') + fun x => ∑ k, T f (Function.update x k (y * x k - x k * y)) := by
      funext x; simp only [hT, h, Pi.add_apply]
    rw [hα, hα, map_eps, e]
    exact ((epsL n).map_add _ _).trans ((congrArg (eps (T f') + ·) (epsDer M n (T f) y)).trans (add_zero _))

section HolAndRetr

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

omit [NumberField E] in
def hp : Lie E a →ₗ[ℝ] Herm E a where
  toFun X := ⟨(1 / 2 : ℝ) • (Matrix.of X + star (Matrix.of X)), by
    change star _ = _; rw [star_smul, star_add, star_star, add_comm, star_trivial]⟩
  map_add' X Y := Subtype.ext (by
    change (1 / 2 : ℝ) • ((Matrix.of X + Matrix.of Y) + star (Matrix.of X + Matrix.of Y)) = _ + _
    rw [star_add, ← smul_add]; congr 1; abel)
  map_smul' c X := Subtype.ext (by
    change (1 / 2 : ℝ) • (c • Matrix.of X + star (c • Matrix.of X)) = c • ((1 / 2 : ℝ) • _)
    rw [star_smul, star_trivial, ← smul_add, smul_comm])

omit [NumberField E] in
theorem hp_val (X : Matrix (Fin a) (Fin a) (Cinf E)) : (hp (toL X)).1 = (1 / 2 : ℝ) • (X + star X) := rfl

omit [NumberField E] in
def brH (Z : Matrix (Fin a) (Fin a) (Cinf E)) (hZ : star Z = -Z) (Y : Herm E a) : Herm E a :=
  ⟨Z * Y.1 - Y.1 * Z, by
    have h : star Y.1 = Y.1 := Y.2; change star _ = _; rw [star_sub, star_mul, star_mul, h, hZ]; noncomm_ring⟩

section ComplexRetr

variable {M : Type*} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
  (κ : Kinf E a → Module.End ℂ M) (L : Lie E a →ₗ[ℝ] Module.End ℂ M)

omit [NumberField E] in
def InfEq {q : ℕ} (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M) : Prop :=
  ∀ (Z : Matrix (Fin a) (Fin a) (Cinf E)) (hZ : star Z = -Z) (Y : Fin q → Herm E a),
    L (toL Z) (ω Y) = ∑ i, ω (Function.update Y i (brH Z hZ (Y i)))

def SepDer : Prop :=
  ∀ (k : ℝ → Kinf E a) (Z : Matrix (Fin a) (Fin a) (Cinf E)), k 0 = 1 → HasDerivAt (fun t => toL (k t).1) (toL Z) 0 →
    ∀ m' : M, m' ≠ 0 → ∃ l : M →ₗ[ℂ] ℂ, l m' ≠ 0 ∧ ∀ m, HasDerivAt (fun t => l (κ (k t) m)) (l (L (toL Z) m)) 0

omit [NumberField E] in
structure IsRetr (α : (Lie E a →ₗ[ℝ] M) →ₗ[ℝ] M) : Prop where
  lie : ∀ (Y : Matrix (Fin a) (Fin a) (Cinf E)) (f f' : Lie E a →ₗ[ℝ] M),
    (∀ X, L (toL Y) (f (toL X)) = f' (toL X) + f (toL (Y * X - X * Y))) → L (toL Y) (α f) = α f'
  cpt : ∀ (k : Kinf E a) (f f' : Lie E a →ₗ[ℝ] M),
    (∀ X, κ k (f (toL X)) = f' (toL (k.1 * X * star k.1))) → κ k (α f) = α f'
  retr : ∀ (m : M) (f : Lie E a →ₗ[ℝ] M), (∀ X, f X = L X m) → α f = m

end ComplexRetr

omit [NumberField E] in
theorem holEq [IsTotallyComplex E] (N : Type*) [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N]
    (τ : E →+* ℂ) (L : Lie E a →ₗ[ℝ] N) (x : Matrix (Fin a) (Fin a) ℂ) :
    hol τ L x = (1 / 2 : ℂ) • (L (toL (x.map (atEmb τ))) - Complex.I • L (toL ((Complex.I • x).map (atEmb τ)))) := by
  let L' : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] N := L
  have hsum : ∀ y : Matrix (Fin a) (Fin a) ℂ, L' (y.map (atEmb τ)) = ∑ i, ∑ j, L' (Matrix.single i j (atEmb τ (y i j))) :=
    fun y => by conv_lhs => rw [Matrix.matrix_eq_sum_single (y.map (atEmb τ))]; simp only [map_sum, Matrix.map_apply]
  have hL : ∀ (i j : Fin a) (w : ℂ), L' (Matrix.single i j (atEmb τ w)) =
      (w.re : ℂ) • L' (Matrix.single i j (atEmb τ 1)) + (w.im : ℂ) • L' (Matrix.single i j (atEmb τ Complex.I)) :=
    fun i j w => by
      rw [atEmb_eq τ w, Matrix.single_add, ← Matrix.smul_single, ← Matrix.smul_single, map_add, map_smul, map_smul,
        ← algebraMap_smul ℂ w.re, ← algebraMap_smul ℂ w.im]; rfl
  change ∑ i, ∑ j, x i j • ((1 / 2 : ℂ) • (L' (Matrix.single i j (atEmb τ 1)) -
      Complex.I • L' (Matrix.single i j (atEmb τ Complex.I)))) =
    (1 / 2 : ℂ) • (L' (x.map (atEmb τ)) - Complex.I • L' ((Complex.I • x).map (atEmb τ)))
  rw [hsum, hsum]; simp only [Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, hL i j (x i j), hL i j (Complex.I * x i j)]
  generalize x i j = c; conv_lhs => rw [← Complex.re_add_im c]
  simp only [Complex.I_mul_re, Complex.I_mul_im, Complex.ofReal_neg]
  match_scalars
  · ring
  · linear_combination (-(c.im : ℂ) / 2) * Complex.I_mul_I

private def atEmbHom (τ : E →+* ℂ) : ℂ →+ Cinf E :=
  AddMonoidHom.mk' (atEmb τ) fun z w => by
    rw [atEmb_eq τ (z + w), atEmb_eq τ z, atEmb_eq τ w, Complex.add_re, Complex.add_im, add_smul, add_smul]; abel

omit [NumberField E] in
private theorem mul_atEmb_map (τ : E →+* ℂ) (p : Matrix (Fin a) (Fin a) (Cinf E)) (x : Matrix (Fin a) (Fin a) ℂ) :
    p * x.map (atEmb τ) = (p.map (coord τ) * x).map (atEmb τ) := by
  ext1 i j; simp only [Matrix.mul_apply, Matrix.map_apply]
  rw [show atEmb τ (∑ k, coord τ (p i k) * x k j) = ∑ k, atEmb τ (coord τ (p i k) * x k j) from
    map_sum (atEmbHom τ) _ _]
  exact Finset.sum_congr rfl fun k _ => mul_atEmb _ _ _

omit [NumberField E] in
private theorem atEmb_map_mul (τ : E →+* ℂ) (p : Matrix (Fin a) (Fin a) (Cinf E)) (x : Matrix (Fin a) (Fin a) ℂ) :
    x.map (atEmb τ) * p = (x * p.map (coord τ)).map (atEmb τ) := by
  ext1 i j; simp only [Matrix.mul_apply, Matrix.map_apply]
  rw [show atEmb τ (∑ k, x i k * coord τ (p k j)) = ∑ k, atEmb τ (x i k * coord τ (p k j)) from
    map_sum (atEmbHom τ) _ _]
  refine Finset.sum_congr rfl fun k _ => ?_; rw [mul_comm, mul_comm (x i k)]; exact mul_atEmb _ _ _

omit [NumberField E] in
private theorem atEmb_map_sub (τ : E →+* ℂ) (x y : Matrix (Fin a) (Fin a) ℂ) :
    (x - y).map (atEmb τ) = x.map (atEmb τ) - y.map (atEmb τ) := by
  ext1 i j; simp only [Matrix.sub_apply, Matrix.map_apply]; exact map_sub (atEmbHom τ) _ _

omit [NumberField E] in
theorem holMul [IsTotallyComplex E] (N : Type*) [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N]
    (τ : E →+* ℂ) (L L' : Lie E a →ₗ[ℝ] N) :
    (∀ p q : Matrix (Fin a) (Fin a) (Cinf E), (∀ X, L' (toL X) = L (toL (p * X * q))) →
      ∀ x, hol τ L' x = hol τ L (p.map (coord τ) * x * q.map (coord τ))) ∧
    ∀ Y : Matrix (Fin a) (Fin a) (Cinf E), (∀ X, L' (toL X) = L (toL (Y * X - X * Y))) →
      ∀ x, hol τ L' x = hol τ L (Y.map (coord τ) * x - x * Y.map (coord τ)) :=
  ⟨fun p q h x => by rw [holEq, holEq, h, h, mul_atEmb_map, atEmb_map_mul, mul_atEmb_map, atEmb_map_mul, Matrix.mul_smul, Matrix.smul_mul],
   fun Y h x => by rw [holEq, holEq, h, h, mul_atEmb_map, atEmb_map_mul, mul_atEmb_map, atEmb_map_mul, Matrix.mul_smul, Matrix.smul_mul, ← atEmb_map_sub, ← atEmb_map_sub, ← smul_sub]⟩

section AlphaRealAux

variable {N N' : Type*} [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N]
  [AddCommGroup N'] [Module ℂ N'] [Module ℝ N'] [IsScalarTower ℝ ℂ N']

omit [NumberField E] [IsScalarTower ℝ ℂ N] [IsScalarTower ℝ ℂ N'] in
private theorem hol_nat (τ : E →+* ℂ) (φ : N →ₗ[ℂ] N') (L : Lie E a →ₗ[ℝ] N) (L' : Lie E a →ₗ[ℝ] N')
    (h : ∀ X, φ (L (toL X)) = L' (toL X)) (x : Matrix (Fin a) (Fin a) ℂ) : φ (hol τ L x) = hol τ L' x := by
  simp only [hol_apply, eL, map_sum, map_smul, map_sub, h]

omit [NumberField E] [IsScalarTower ℝ ℂ N] in
private theorem hol_add (τ : E →+* ℂ) (L L' : Lie E a →ₗ[ℝ] N) : hol τ (L + L') = hol τ L + hol τ L' := by
  ext1 x; simp only [hol_apply, eL, LinearMap.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by module

omit [NumberField E] in
private theorem hol_smul (τ : E →+* ℂ) (r : ℝ) (L : Lie E a →ₗ[ℝ] N) : hol τ (r • L) = (r : ℂ) • hol τ L := by
  ext1 x
  have e : ∀ v : N, r • v = (r : ℂ) • v := fun v => (algebraMap_smul ℂ r v).symm
  simp only [hol_apply, eL, LinearMap.smul_apply, Finset.smul_sum, e]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by module

variable [IsTotallyComplex E]

omit [NumberField E] in
private theorem hol_grp (τ : E →+* ℂ) (φ : N →ₗ[ℂ] N') (L : Lie E a →ₗ[ℝ] N) (L' : Lie E a →ₗ[ℝ] N')
    (p q : Matrix (Fin a) (Fin a) (Cinf E)) (h : ∀ X, φ (L (toL X)) = L' (toL (p * X * q)))
    (x : Matrix (Fin a) (Fin a) ℂ) : φ (hol τ L x) = hol τ L' (p.map (coord τ) * x * q.map (coord τ)) := by
  rw [hol_nat τ φ L (φ.restrictScalars ℝ ∘ₗ L) (fun _ => rfl)]
  exact (holMul N' τ L' _).1 p q h x

omit [NumberField E] in
private theorem hol_der (τ : E →+* ℂ) (φ : N →ₗ[ℂ] N') (L : Lie E a →ₗ[ℝ] N) (L' L'' : Lie E a →ₗ[ℝ] N')
    (Y : Matrix (Fin a) (Fin a) (Cinf E)) (h : ∀ X, φ (L (toL X)) = L' (toL X) + L'' (toL (Y * X - X * Y)))
    (x : Matrix (Fin a) (Fin a) ℂ) :
    φ (hol τ L x) = hol τ L' x + hol τ L'' (Y.map (coord τ) * x - x * Y.map (coord τ)) := by
  rw [hol_nat τ φ L (φ.restrictScalars ℝ ∘ₗ L) (fun _ => rfl),
    ← (holMul N' τ L'' (φ.restrictScalars ℝ ∘ₗ L - L')).2 Y (fun X => sub_eq_of_eq_add' (h X)) x,
    ← LinearMap.add_apply, ← hol_add, add_sub_cancel]

omit [NumberField E] in
private theorem hol_grp_end {M : Type*} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
    (τ : E →+* ℂ) (u : Module.End ℂ M) (L : Lie E a →ₗ[ℝ] Module.End ℂ M)
    (p q : Matrix (Fin a) (Fin a) (Cinf E)) (h : ∀ X, u * L (toL X) = L (toL (p * X * q)) * u)
    (x : Matrix (Fin a) (Fin a) ℂ) : u * hol τ L x = hol τ L (p.map (coord τ) * x * q.map (coord τ)) * u := by
  have h1 := hol_grp τ (LinearMap.mulLeft ℂ u) L ((LinearMap.mulRight ℂ u).restrictScalars ℝ ∘ₗ L) p q h x
  rw [← hol_nat τ (LinearMap.mulRight ℂ u) L ((LinearMap.mulRight ℂ u).restrictScalars ℝ ∘ₗ L) (fun _ => rfl)] at h1
  exact h1

omit [NumberField E] in
private theorem hol_der_end {M : Type*} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
    (τ : E →+* ℂ) (u : Module.End ℂ M) (L : Lie E a →ₗ[ℝ] Module.End ℂ M)
    (Y : Matrix (Fin a) (Fin a) (Cinf E)) (h : ∀ X, u * L (toL X) - L (toL X) * u = L (toL (Y * X - X * Y)))
    (x : Matrix (Fin a) (Fin a) ℂ) :
    u * hol τ L x - hol τ L x * u = hol τ L (Y.map (coord τ) * x - x * Y.map (coord τ)) := by
  have h1 := hol_der τ (LinearMap.mulLeft ℂ u - LinearMap.mulRight ℂ u) L 0 L Y
    (fun X => (h X).trans (zero_add _).symm) x
  have h0 : hol τ (0 : Lie E a →ₗ[ℝ] Module.End ℂ M) x = 0 := by simp [hol_apply, eL]
  rw [h0, zero_add] at h1; exact h1

end AlphaRealAux

omit [NumberField E] in
theorem alphaReal [IsTotallyComplex E] (M : Type*) [AddCommGroup M] [Module ℂ M] [Module ℝ M]
    [IsScalarTower ℝ ℂ M] (κ : Kinf E a → Module.End ℂ M) (LA LB : Lie E a →ₗ[ℝ] Module.End ℂ M)
    (hA : IsLieHom LA) (hB : IsLieHom LB) (hc : ∀ X Y, Commute (LA X) (LB Y))
    (hκA : ∀ (k : Kinf E a) (X : Matrix (Fin a) (Fin a) (Cinf E)), κ k * LA (toL X) = LA (toL (k.1 * X * star k.1)) * κ k)
    (hκB : ∀ (k : Kinf E a) (X : Matrix (Fin a) (Fin a) (Cinf E)), κ k * LB (toL X) = LB (toL (k.1 * X * star k.1)) * κ k)
    (τ : E →+* ℂ) (x c c' : ℂ) (hqA : qdet (eL LA τ) x = c • (1 : Module.End ℂ M))
    (hqB : qdet (fun i j => -MulOpposite.op (eL LB τ i j)) x = MulOpposite.op (c' • (1 : Module.End ℂ M)))
    (hne : c ≠ c') :
    ∃ α : (Lie E a →ₗ[ℝ] M) →ₗ[ℝ] M, IsRetr κ (LA + LB) α := by
  have hcomm : ∀ y z, Commute (hol τ LA y) (hol τ LB z) := fun y z => by
    simp only [hol_apply, eL]
    refine Commute.sum_left _ _ _ fun i _ => Commute.sum_left _ _ _ fun j _ =>
      Commute.sum_right _ _ _ fun k _ => Commute.sum_right _ _ _ fun l _ => ?_
    exact (((((hc _ _).sub_right ((hc _ _).smul_right _)).sub_left
      (((hc _ _).sub_right ((hc _ _).smul_right _)).smul_left _)).smul_right _).smul_left _
      |>.smul_right _).smul_left _
  obtain ⟨α₀, h1, h2, h3⟩ := alphaAbs M a (hol τ LA) (hol τ LB) (fun k => x - (k : ℂ)) hcomm
  set s : ℂ := ((a.factorial : ℂ) * (c - c'))⁻¹ with hs
  have e : ∀ (r : ℝ) (v : M), r • v = (r : ℂ) • v := fun r v => (algebraMap_smul ℂ r v).symm
  let α : (Lie E a →ₗ[ℝ] M) →ₗ[ℝ] M :=
    { toFun := fun f => s • α₀ (hol τ f)
      map_add' := fun f g => by rw [hol_add, map_add, smul_add]
      map_smul' := fun r f => by rw [hol_smul, map_smul, RingHom.id_apply, e, smul_comm] }
  have hα : ∀ f, α f = s • α₀ (hol τ f) := fun _ => rfl
  refine ⟨α, fun Y f f' hf => ?_, fun k f f' hf => ?_, fun m f hf => ?_⟩
  · rw [hα, hα, map_smul]; congr 1
    refine h3 _ (Y.map (coord τ)) (hol_der_end τ _ LA Y fun X => ?_) (hol_der_end τ _ LB Y fun X => ?_) _ _
      (hol_der τ _ f f' f Y hf)
    · rw [LinearMap.add_apply, add_mul, mul_add, ← hA Y X, (hc (toL X) (toL Y)).eq]; abel
    · rw [LinearMap.add_apply, add_mul, mul_add, ← hB Y X, (hc (toL Y) (toL X)).eq]; abel
  · rw [hα, hα, map_smul]; congr 1
    refine h2 _ (k.1.map (coord τ)) ((star k.1).map (coord τ)) ?_ (hol_grp_end τ _ LA _ _ (hκA k))
      (hol_grp_end τ _ LB _ _ (hκB k)) _ _ (hol_grp τ _ f f' _ _ hf)
    have hk : star k.1 * k.1 = 1 := k.2.1
    rw [← Matrix.map_mul, hk, Matrix.map_one _ (map_zero _) (map_one _)]
  · have hx : ∀ y, hol τ f y = hol τ LA y m + hol τ LB y m := fun y => by
      rw [← hol_nat τ (LinearMap.applyₗ m) (LA + LB) f (fun X => (hf _).symm), hol_add]; rfl
    rw [hα, h1 m _ hx]; simp only [hol_single]
    have gA := (eLRel _ LA hA).1 τ
    have gB := (glNegOp _ a _ ((eLRel _ LB hB).1 τ)).1
    rw [antisymmetrizedProduct_eq_factorial_smul_qdet _ gB, hqB,
      show (fun i j => eL LA τ i j) = eL LA τ from rfl,
      antisymmetrizedProduct_eq_factorial_smul_qdet _ gA, hqA]
    have hz : (a.factorial : ℂ) * (c - c') ≠ 0 :=
      mul_ne_zero (by exact_mod_cast a.factorial_ne_zero) (sub_ne_zero.2 hne)
    simp only [MulOpposite.unop_smul, MulOpposite.unop_op, LinearMap.smul_apply, Module.End.one_apply, smul_smul,
      ← sub_smul]
    rw [← mul_sub, hs, inv_mul_cancel₀ hz, one_smul]

end HolAndRetr

end AlphaAndRetraction

section TensorAndHomotopy

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def lieA (π : CuspSub E a) (Ξ : AlgRep E a) : Lie E a →ₗ[ℝ] Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) where
  toFun X := (lieOp π X).rTensor _
  map_add' _ _ := by simp only [map_add, LinearMap.rTensor_add]
  map_smul' c X := by
    rw [map_smul, RingHom.id_apply, ← algebraMap_smul ℂ c (lieOp π X),
      ← algebraMap_smul ℂ c (LinearMap.rTensor _ _ : Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))), LinearMap.rTensor_smul]

def lieB (π : CuspSub E a) (Ξ : AlgRep E a) : Lie E a →ₗ[ℝ] Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) where
  toFun X := (Matrix.toLin' (Ξ.dmat X)).lTensor _
  map_add' _ _ := by simp only [map_add, LinearMap.lTensor_add]
  map_smul' c X := by
    rw [map_smul, RingHom.id_apply, ← algebraMap_smul ℂ c (Ξ.dmat X),
      ← algebraMap_smul ℂ c (LinearMap.lTensor _ _ : Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))), map_smul,
      LinearMap.lTensor_smul]

theorem lieA_apply (π : CuspSub E a) (Ξ : AlgRep E a) (X : Lie E a) : lieA π Ξ X = (lieOp π X).rTensor _ := rfl
theorem lieB_apply (π : CuspSub E a) (Ξ : AlgRep E a) (X : Lie E a) :
    lieB π Ξ X = (Matrix.toLin' (Ξ.dmat X)).lTensor _ := rfl
theorem tensorLie_eq (π : CuspSub E a) (Ξ : AlgRep E a) : tensorLie π Ξ = lieA π Ξ + lieB π Ξ := rfl
theorem lieA_commute (π : CuspSub E a) (Ξ : AlgRep E a) (X Y : Lie E a) : Commute (lieA π Ξ X) (lieB π Ξ Y) :=
  TensorProduct.ext' fun _ _ => rfl

private theorem qdet_intertw {M M' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M'] {k : ℕ}
    (R : M →ₗ[ℂ] M') (X : Fin k → Fin k → Module.End ℂ M) (Y : Fin k → Fin k → Module.End ℂ M')
    (h : ∀ p q, R ∘ₗ X p q = Y p q ∘ₗ R) (v : ℂ) :
    R ∘ₗ qdet X v = qdet Y v ∘ₗ R := by
  let S : Subalgebra ℂ (Module.End ℂ M × Module.End ℂ M') :=
    { carrier := {z | R ∘ₗ z.1 = z.2 ∘ₗ R}
      mul_mem' := fun hx hy => by
        change R ∘ₗ (_ ∘ₗ _) = (_ ∘ₗ _) ∘ₗ R
        rw [← LinearMap.comp_assoc, hx, LinearMap.comp_assoc, hy, LinearMap.comp_assoc]
      add_mem' := fun hx hy => by change R ∘ₗ (_ + _) = (_ + _) ∘ₗ R; rw [LinearMap.comp_add, LinearMap.add_comp, hx, hy]
      algebraMap_mem' := fun _ => by ext; simp }
  let Z : Fin k → Fin k → S := fun p q => ⟨(X p q, Y p q), h p q⟩
  have e1 : ((qdet Z v : S) : Module.End ℂ M × Module.End ℂ M').1 = qdet X v :=
    map_qdet ((AlgHom.fst ℂ _ _).comp S.val) Z v
  have e2 : ((qdet Z v : S) : Module.End ℂ M × Module.End ℂ M').2 = qdet Y v :=
    map_qdet ((AlgHom.snd ℂ _ _).comp S.val) Z v
  rw [← e1, ← e2]; exact (qdet Z v).2

theorem tensA (π : CuspSub E a) (Ξ : AlgRep E a) :
    IsLieHom (A := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (lieA π Ξ) ∧
      (∀ (k : Kinf E a) (X : Matrix (Fin a) (Fin a) (Cinf E)),
        tensorK π Ξ k * lieA π Ξ (toL X) = lieA π Ξ (toL (k.1 * X * star k.1)) * tensorK π Ξ k) ∧
      ∀ (τ : E →+* ℂ) (m : Multiset ℂ), π.HasInfChar τ m → ∀ u : ℂ,
        qdet (eL (N := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (lieA π Ξ) τ) (u + ((a : ℂ) - 1) / 2) =
          (m.map (u + ·)).prod • (1 : Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) := by
  let f : Module.End ℂ π.V →ₐ[ℂ] Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) := Module.End.rTensorAlgHom ℂ π.V (Fin Ξ.d → ℂ)
  have hf : ∀ X, lieA π Ξ X = f (lieOp π X) := fun _ => rfl
  refine ⟨fun X Y => ?_, fun k X => ?_, fun τ m hm u => ?_⟩
  · rw [hf, hf, hf, ← map_mul f, ← map_mul f, ← map_sub f]
    congr 1; exact LinearMap.ext fun φ => Subtype.ext (LinearMap.congr_fun ((lie_comm (toL X) (toL Y)).trans
      (map_sub (lie E a) (toL (X * Y)) (toL (Y * X))).symm) φ.1)
  · refine TensorProduct.ext' fun φ v => ?_
    have h1 : π.op (.cpt k) (lieOp π (toL X) φ) = lieOp π (toL (k.1 * X * star k.1)) (π.op (.cpt k) φ) :=
      Subtype.ext (LinearMap.congr_fun (rt_lie (Unitary.toUnits k) X) φ.1)
    simp only [Module.End.mul_apply, tensorK, lieA_apply, LinearMap.rTensor_tmul, TensorProduct.map_tmul, h1]
  · have e : eL (N := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (lieA π Ξ) τ =
        fun i j => f (eL (N := Module.End ℂ π.V) (lieOp π) τ i j) := by
      funext i j; simp only [eL, hf, map_smul, map_sub]
    have h := qdet_intertw π.V.subtype (eL (N := Module.End ℂ π.V) (lieOp π) τ) (Eop τ) (fun _ _ => rfl)
      (u + ((a : ℂ) - 1) / 2)
    have h2 : qdet (eL (N := Module.End ℂ π.V) (lieOp π) τ) (u + ((a : ℂ) - 1) / 2) =
        (m.map (u + ·)).prod • (1 : Module.End ℂ π.V) :=
      LinearMap.ext fun φ => Subtype.ext ((LinearMap.congr_fun h φ).trans (hm.2 u φ.1 φ.2))
    rw [e, ← map_qdet, h2, map_smul, map_one]

private def actAlg (V : Type*) [AddCommGroup V] [Module ℂ V] (d : ℕ) :
    Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] Module.End ℂ (V ⊗[ℂ] (Fin d → ℂ)) :=
  (Module.End.lTensorAlgHom ℂ (Fin d → ℂ) V).comp
    (Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin d → ℂ)).toAlgHom

private def actOp (V : Type*) [AddCommGroup V] [Module ℂ V] (d : ℕ) :
    Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] (Module.End ℂ (V ⊗[ℂ] (Fin d → ℂ)))ᵐᵒᵖ where
  toFun N := MulOpposite.op (actAlg V d Nᵀ)
  map_one' := by simp
  map_mul' _ _ := by simp [Matrix.transpose_mul]
  map_zero' := by simp
  map_add' _ _ := by simp [Matrix.transpose_add]
  commutes' _ := by simp [Algebra.algebraMap_eq_smul_one]

theorem tensB (π : CuspSub E a) (Ξ : AlgRep E a) :
    IsLieHom (A := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (lieB π Ξ) ∧
      (∀ (k : Kinf E a) (X : Matrix (Fin a) (Fin a) (Cinf E)),
        tensorK π Ξ k * lieB π Ξ (toL X) = lieB π Ξ (toL (k.1 * X * star k.1)) * tensorK π Ξ k) ∧
      ∀ (τ : E →+* ℂ) (m : Multiset ℂ), HasDualInfChar Ξ τ m → ∀ u : ℂ,
        qdet (fun i j => -MulOpposite.op (eL (N := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (lieB π Ξ) τ i j))
          (u + ((a : ℂ) - 1) / 2) =
            MulOpposite.op ((m.map (u + ·)).prod • (1 : Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)))) := by
  have hB : ∀ X, lieB π Ξ X = actAlg π.V Ξ.d (Ξ.dmat X) := fun _ => rfl
  refine ⟨fun X Y => ?_, fun k X => ?_, fun τ m hm u => ?_⟩
  · rw [hB, hB, hB, ← dmat_bracket, map_sub, map_mul, map_mul]
  · refine TensorProduct.ext' fun φ v => ?_
    have h2 : Ξ.mat (Unitary.toUnits k) * Ξ.dmat (toL X) = Ξ.dmat (toL (k.1 * X * star k.1)) * Ξ.mat (Unitary.toUnits k) :=
      Ξ.mat_mul_dmat (Unitary.toUnits k) X
    simp only [Module.End.mul_apply, tensorK, lieB_apply, LinearMap.lTensor_tmul, TensorProduct.map_tmul,
      Matrix.toLin'_apply, Matrix.mulVec_mulVec, h2]
  · have h0 := map_qdet (B := (Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)))ᵐᵒᵖ)
      (actOp π.V Ξ.d) (dualE Ξ τ) (u + ((a : ℂ) - 1) / 2)
    have h := h0.symm.trans (congrArg (actOp π.V Ξ.d) (hm.2 u))
    rw [map_smul, map_one] at h
    have e : ∀ i j, actOp π.V Ξ.d (dualE Ξ τ i j) =
        -MulOpposite.op (eL (N := Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) (lieB π Ξ) τ i j) := fun i j => by
      rw [dualE_eq, map_neg]; congr 1
      change MulOpposite.op (actAlg π.V Ξ.d (eL Ξ.dmat τ i j)ᵀᵀ) = _
      rw [Matrix.transpose_transpose]; simp only [eL, hB, map_smul, map_sub]
    simp only [e] at h; rw [h, MulOpposite.op_smul, MulOpposite.op_one]

omit [NumberField E] [IsTotallyComplex E] in
theorem homId (M : Type*) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
    (L : Lie E a →ₗ[ℝ] Module.End ℂ M) (q : ℕ) (ω : Herm E a [⋀^Fin (q + 1)]→ₗ[ℝ] M)
    (hd : dCo L ω = 0) (hinf : InfEq L ω) (X : Matrix (Fin a) (Fin a) (Cinf E)) (Y : Fin (q + 1) → Herm E a) :
    ∑ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) • (L (toL (Y i).1) (ω (Matrix.vecCons (hp (toL X)) (i.removeNth Y))) -
      ω (Matrix.vecCons (hp (toL ((Y i).1 * X - X * (Y i).1))) (i.removeNth Y))) = L (toL X) (ω Y) := by
  let Z : Matrix (Fin a) (Fin a) (Cinf E) := (1 / 2 : ℝ) • (X - star X)
  have hZ : star Z = -Z := by simp only [Z]; rw [star_smul, star_sub, star_star, star_trivial, ← smul_neg, neg_sub]
  have hX : toL X = toL (hp (toL X)).1 + toL Z :=
    congrArg toL (by rw [hp_val]; simp only [Z]; module : X = (hp (toL X)).1 + Z)
  have hb : ∀ U : Herm E a, hp (toL (U.1 * X - X * U.1)) = -brH Z hZ U := fun U => by
    apply Subtype.ext; have h : star U.1 = U.1 := U.2
    rw [hp_val]; change _ = -(Z * U.1 - U.1 * Z)
    simp only [Z, star_sub, star_mul, h, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub]; module
  have h1 := dCo_cons (L := L) ω (hp (toL X)) Y
  rw [hd, AlternatingMap.zero_apply, eq_comm, sub_eq_zero, dCo_apply] at h1
  rw [congrArg L hX, map_add, LinearMap.add_apply, h1, hinf Z hZ Y, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : ω (Matrix.vecCons (-brH Z hZ (Y i)) (i.removeNth Y)) = -ω (Matrix.vecCons (brH Z hZ (Y i)) (i.removeNth Y)) := by
    rw [← AlternatingMap.curryLeft_apply_apply, ← AlternatingMap.curryLeft_apply_apply, map_neg, AlternatingMap.neg_apply]
  rw [hb, h2, sub_neg_eq_add, smul_add, ← Fin.insertNth_removeNth, AlternatingMap.map_insertNth,
    AlternatingMap.curryLeft_apply_apply]

private def altFlip {A V M : Type*} [AddCommGroup A] [Module ℝ A] [AddCommGroup V] [Module ℝ V]
    [AddCommGroup M] [Module ℝ M] {q : ℕ} (φ : A →ₗ[ℝ] (V [⋀^Fin q]→ₗ[ℝ] M)) : V [⋀^Fin q]→ₗ[ℝ] (A →ₗ[ℝ] M) where
  toFun Y :=
    { toFun := fun X => φ X Y
      map_add' := fun X X' => by rw [map_add, AlternatingMap.add_apply]
      map_smul' := fun c X => by rw [map_smul, AlternatingMap.smul_apply, RingHom.id_apply] }
  map_update_add' Y i x y := LinearMap.ext fun X => (φ X).map_update_add Y i x y
  map_update_smul' Y i c x := LinearMap.ext fun X => (φ X).map_update_smul Y i c x
  map_eq_zero_of_eq' Y _ _ h hij := LinearMap.ext fun X => (φ X).map_eq_zero_of_eq Y h hij

omit [NumberField E] [IsTotallyComplex E] in
theorem homot (M : Type*) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
    (κ : Kinf E a → Module.End ℂ M) (L : Lie E a →ₗ[ℝ] Module.End ℂ M) (α : (Lie E a →ₗ[ℝ] M) →ₗ[ℝ] M)
    (hα : IsRetr κ L α) (hinf : ∀ (q : ℕ) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M), IsCochain κ ω → InfEq L ω) :
    ¬ HasCohomology κ L := by
  rintro (⟨ω, h0, h1, h2⟩ | ⟨q, ω, h0, h1, h2⟩)
  · refine h2 (AlternatingMap.ext fun Y => ?_)
    have key : ∀ X : Matrix (Fin a) (Fin a) (Cinf E), L (toL X) (ω Y) = 0 := fun X => by
      let Z : Matrix (Fin a) (Fin a) (Cinf E) := (1 / 2 : ℝ) • (X - star X)
      have hZ : star Z = -Z := by simp only [Z]; rw [star_smul, star_sub, star_star, star_trivial, ← smul_neg, neg_sub]
      have hX : toL X = toL (hp (toL X)).1 + toL Z :=
        congrArg toL (by rw [hp_val]; simp only [Z]; module : X = (hp (toL X)).1 + Z)
      have h3 := DFunLike.congr_fun h1 fun _ => hp (toL X)
      rw [dCo_apply, Fin.sum_univ_one, Subsingleton.elim (Fin.removeNth _ _) Y] at h3
      have h4 : L (toL (hp (toL X)).1) (ω Y) = 0 := by simpa using h3
      rw [congrArg L hX, map_add, LinearMap.add_apply, h4, hinf 0 ω h0 Z hZ Y]; simp
    rw [← hα.retr (ω Y) 0 fun X => (key (Matrix.of X)).symm, map_zero, AlternatingMap.zero_apply]
  · let F : Herm E a [⋀^Fin q]→ₗ[ℝ] (Lie E a →ₗ[ℝ] M) := altFlip (ω.curryLeft ∘ₗ hp)
    have hF : ∀ Y X, F Y X = ω (Matrix.vecCons (hp X) Y) := fun _ _ => rfl
    let ad : Matrix (Fin a) (Fin a) (Cinf E) → Lie E a →ₗ[ℝ] Lie E a := fun Y =>
      { toFun := fun X => toL (Y * Matrix.of X - Matrix.of X * Y)
        map_add' := fun X X' => congrArg toL (by noncomm_ring : Y * (Matrix.of X + Matrix.of X') -
          (Matrix.of X + Matrix.of X') * Y = (Y * Matrix.of X - Matrix.of X * Y) + (Y * Matrix.of X' - Matrix.of X' * Y))
        map_smul' := fun c X => congrArg toL (by rw [smul_sub, mul_smul_comm, smul_mul_assoc] :
          Y * (c • Matrix.of X) - (c • Matrix.of X) * Y = c • (Y * Matrix.of X - Matrix.of X * Y)) }
    refine h2 (α.compAlternatingMap F) (fun k Y => ?_) (AlternatingMap.ext fun Y => ?_)
    · refine (hα.cpt k (F Y) (F fun i => adHerm k (Y i)) fun X => ?_).symm
      have e : hp (toL (k.1 * X * star k.1)) = adHerm k (hp (toL X)) := by
        apply Subtype.ext; change _ = k.1 * (hp (toL X)).1 * star k.1
        rw [hp_val, hp_val, star_mul, star_mul, star_star, mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_assoc k.1 (star X)]
      rw [hF, hF, ← h0, e]; congr 1; funext j; refine Fin.cases ?_ (fun j => ?_) j <;> simp
    · let G : Fin (q + 1) → Lie E a →ₗ[ℝ] M := fun i =>
        (L (toL (Y i).1)).restrictScalars ℝ ∘ₗ F (i.removeNth Y) - F (i.removeNth Y) ∘ₗ ad (Y i).1
      have h3 : ∀ i, L (toL (Y i).1) (α (F (i.removeNth Y))) = α (G i) := fun i =>
        hα.lie _ _ _ fun X => (sub_add_cancel _ _).symm
      rw [dCo_apply, ← hα.retr (ω Y) (∑ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) • G i) fun X => ?_, map_sum]
      · refine Finset.sum_congr rfl fun i _ => ?_; rw [map_zsmul, ← h3]; rfl
      · rw [LinearMap.sum_apply]; exact homId M L q ω h1 (hinf _ ω h0) (Matrix.of X) Y

omit [IsTotallyComplex E] in
theorem kCurve (Z : Matrix (Fin a) (Fin a) (Cinf E)) (hZ : star Z = -Z) :
    ∃ k : ℝ → Kinf E a, k 0 = 1 ∧ HasDerivAt (fun t => toL (k t).1) (toL Z) 0 := by
  open scoped Matrix.Norms.Operator in
  have hs : ∀ t : ℝ, star (NormedSpace.exp (t • Z)) = NormedSpace.exp (-(t • Z)) := fun t => by
    rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, ← Matrix.star_eq_conjTranspose, star_smul,
      star_trivial, hZ, smul_neg]
  have hm : ∀ t : ℝ, NormedSpace.exp (t • Z) ∈ unitary (Matrix (Fin a) (Fin a) (Cinf E)) := fun t => by
    rw [Unitary.mem_iff, hs, ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Z)).neg_left,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Z)).neg_right]; simp
  refine ⟨fun t => ⟨NormedSpace.exp (t • Z), hm t⟩, Subtype.ext (by simp), ?_⟩
  open scoped Matrix.Norms.Operator in
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Z 0
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h; exact h

private theorem multi_cont {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {q : ℕ}
    (μ : MultilinearMap ℝ (fun _ : Fin q => V) ℂ) : Continuous μ := by
  let b := Module.finBasis ℝ V
  have e : (μ : (Fin q → V) → ℂ) = fun x => ∑ r : Fin q → Fin (Module.finrank ℝ V),
      (∏ i, b.coord (r i) (x i)) • μ fun i => b (r i) := by
    funext x
    have h : x = fun i => ∑ j, b.coord j (x i) • b j := funext fun i => (b.sum_repr (x i)).symm
    conv_lhs => rw [h, μ.map_sum]; simp only [μ.map_smul_univ]
  rw [e]
  refine continuous_finsetSum _ fun r _ => Continuous.fun_smul ?_ continuous_const
  exact continuous_finsetProd _ fun i _ => (b.coord (r i)).continuous_of_finiteDimensional.comp (continuous_apply i)

private theorem multi_deriv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {q : ℕ}
    (μ : MultilinearMap ℝ (fun _ : Fin q => V) ℂ) (c : ℝ → Fin q → V) (c' : Fin q → V)
    (hc : ∀ i, HasDerivAt (fun t => c t i) (c' i) 0) :
    HasDerivAt (fun t => μ (c t)) (∑ i, μ (Function.update (c 0) i (c' i))) 0 := by
  let ν : ContinuousMultilinearMap ℝ (fun _ : Fin q => V) ℂ := ⟨μ, multi_cont μ⟩
  have h := (ν.hasFDerivAt (c 0)).comp_hasDerivAt (0 : ℝ) (hasDerivAt_pi.2 hc)
  rw [ContinuousMultilinearMap.linearDeriv_apply] at h; exact h

omit [NumberField E] [IsTotallyComplex E] in
private theorem hp_herm (Y : Herm E a) : hp (toL Y.1) = Y := by
  apply Subtype.ext; have h : star Y.1 = Y.1 := Y.2; rw [hp_val, h, ← two_smul ℝ, smul_smul]; norm_num

omit [IsTotallyComplex E] in
private theorem conj_deriv (k : ℝ → Kinf E a) (Z : Matrix (Fin a) (Fin a) (Cinf E)) (hZ : star Z = -Z)
    (h0 : k 0 = 1) (hk : HasDerivAt (fun t => toL (k t).1) (toL Z) 0) (Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    HasDerivAt (fun t => toL ((k t).1 * Y * star (k t).1)) (toL (Z * Y - Y * Z)) 0 := by
  open scoped Matrix.Norms.Operator in
  have h1 : HasDerivAt (fun t => (k t).1) Z 0 := hk
  open scoped Matrix.Norms.Operator in
  have h2 : HasDerivAt (fun t => star (k t).1) (star Z) 0 :=
    (hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => (hasDerivAt_pi.1 (hasDerivAt_pi.1 hk j) i).star :
      HasDerivAt (fun t => toL (star (k t).1)) (toL (star Z)) 0)
  open scoped Matrix.Norms.Operator in
  have h := (h1.mul_const Y).mul h2
  simp only [h0, hZ, OneMemClass.coe_one, star_one, mul_one, one_mul, mul_neg, ← sub_eq_add_neg] at h; exact h

omit [IsTotallyComplex E] in
theorem infAbs (M : Type*) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]
    (κ : Kinf E a → Module.End ℂ M) (L : Lie E a →ₗ[ℝ] Module.End ℂ M) (hS : SepDer κ L)
    (q : ℕ) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M) (hω : IsCochain κ ω) : InfEq L ω := by
  intro Z hZ Y
  obtain ⟨k, h0, hk⟩ := kCurve Z hZ
  rw [← sub_eq_zero]; by_contra hne
  obtain ⟨l, hl, hd⟩ := hS k Z h0 hk _ hne
  apply hl
  let μ : MultilinearMap ℝ (fun _ : Fin q => Lie E a) ℂ :=
    (l.restrictScalars ℝ).compMultilinearMap (ω.toMultilinearMap.compLinearMap fun _ => hp)
  have hμ : ∀ X : Fin q → Herm E a, μ (fun i => toL (X i).1) = l (ω X) := fun X => by
    change l (ω fun i => hp (toL (X i).1)) = _; simp only [hp_herm]
  have h1 := multi_deriv μ (fun t i => toL (adHerm (k t) (Y i)).1) (fun i => toL (brH Z hZ (Y i)).1)
    (fun i => conj_deriv k Z hZ h0 hk (Y i).1)
  have h2 : ∀ t, μ (fun i => toL (adHerm (k t) (Y i)).1) = l (κ (k t) (ω Y)) := fun t => by rw [hμ, hω]
  simp only [h2] at h1
  rw [map_sub, (hd (ω Y)).unique h1, map_sum, sub_eq_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hμ]; congr 1; funext j
  by_cases h : j = i
  · subst h; simp only [Function.update_self]
  · simp only [Function.update_of_ne h, h0, adHerm, OneMemClass.coe_one, star_one, mul_one, one_mul]

theorem tensDer (π : CuspSub E a) (Ξ : AlgRep E a) : SepDer (tensorK π Ξ) (tensorLie π Ξ) := by
  intro k Z h0 hk m' hm
  let e := TensorProduct.piScalarRight ℂ ℂ π.V (Fin Ξ.d)
  have h1 : e m' ≠ 0 := fun h => hm (e.map_eq_zero_iff.1 h)
  obtain ⟨j, hj⟩ := Function.ne_iff.1 h1
  have h2 : (e m' j).1.1 ≠ 0 := fun h => hj (Subtype.ext (Subtype.ext h))
  obtain ⟨g, hg⟩ := Function.ne_iff.1 h2
  let l : π.V ⊗[ℂ] (Fin Ξ.d → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun m => (e m j).1.1 g
      map_add' := fun _ _ => by rw [map_add]; rfl
      map_smul' := fun _ _ => by rw [map_smul]; rfl }
  have hl : ∀ (φ : π.V) (v : Fin Ξ.d → ℂ), l (φ ⊗ₜ v) = φ.1.1 g * v j := fun φ v => by
    have h : e (φ ⊗ₜ v) j = v j • φ := by simp only [e, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
    change (e (φ ⊗ₜ v) j).1.1 g = _; rw [h, mul_comm]; rfl
  have hc0 : (fun t => Unitary.toUnits (k t)) 0 = 1 := by simp only [h0, map_one]
  refine ⟨l, hg, fun m => ?_⟩
  induction m using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add _ _ hx hy => simpa only [map_add] using hx.fun_add hy
  | tmul φ v =>
    have h3 := hasDerivAt_curve_sm φ.1 g (fun t => Unitary.toUnits (k t)) (toL Z) hc0 hk
    have h4 := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      (Ξ.hasDerivAt_curve (fun t => Unitary.toUnits (k t)) (toL Z) hc0 hk j i).mul_const (v i)
    have h5 := h3.fun_mul h4
    simp only [h0, map_one, mul_one] at h5
    simp only [tensorK, tensorLie_tmul, TensorProduct.map_tmul, map_add, hl, Matrix.toLin'_apply]
    have h6 : ∑ i, (1 : Matrix (Fin Ξ.d) (Fin Ξ.d) ℂ) j i * v i = v j := congrFun (Matrix.one_mulVec v) j
    rw [h6] at h5; exact h5

end TensorAndHomotopy

def WignerVanishingGL : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (Ξ : AlgRep E a)
    (m m' : (E →+* ℂ) → Multiset ℂ), (∀ τ, π.HasInfChar τ (m τ)) → (∀ τ, HasDualInfChar Ξ τ (m' τ)) →
    m ≠ m' → ¬ IsCohFor π Ξ

theorem wigner : WignerVanishingGL := by
  intro E _ _ _ a π Ξ m m' hm hm' hne
  obtain ⟨τ, hτ⟩ := Function.ne_iff.1 hne
  obtain ⟨u, hu⟩ : ∃ u : ℂ, ((m τ).map (u + ·)).prod ≠ ((m' τ).map (u + ·)).prod := by
    by_contra h; exact hτ (msetSep _ _ fun u => not_not.1 fun h' => h ⟨u, h'⟩)
  obtain ⟨a1, a2, a3⟩ := tensA π Ξ
  obtain ⟨b1, b2, b3⟩ := tensB π Ξ
  obtain ⟨α, hα⟩ := alphaReal (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) (tensorK π Ξ) (lieA π Ξ) (lieB π Ξ) a1 b1
    (lieA_commute π Ξ) a2 b2 τ _ _ _ (a3 τ _ (hm τ) u) (b3 τ _ (hm' τ) u) hu
  exact homot (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) (tensorK π Ξ) (tensorLie π Ξ) α hα
    (infAbs (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) (tensorK π Ξ) (tensorLie π Ξ) (tensDer π Ξ))

/-- **Cohomological Regularity & Infinitesimal Character Match**: if `π` is cohomological for `Ξ`
and has infinitesimal character `m`, then `m` must equal the dual infinitesimal character `m'` of `Ξ`,
hence `(CG.mk π).IsRegAlg` follows automatically from `exists_dualInfChar` and `wigner`. -/
theorem infChar_eq_dual_of_isCohFor {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    {π : CuspSub E a} {Ξ : AlgRep E a} {m m' : (E →+* ℂ) → Multiset ℂ}
    (hm : ∀ τ, π.HasInfChar τ (m τ)) (hm' : ∀ τ, HasDualInfChar Ξ τ (m' τ))
    (hcoh : IsCohFor π Ξ) : m = m' := by
  by_contra hne
  exact wigner E a π Ξ m m' hm hm' hne hcoh

theorem isRegAlg_of_isCohFor {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    {π : CuspSub E a} {Ξ : AlgRep E a} (hm : ∀ τ, ∃ m, π.HasInfChar τ m) (hcoh : IsCohFor π Ξ) :
    (CG.mk π).IsRegAlg := by
  choose m hm using hm
  choose m' hm' hnodup hint using fun τ => exists_dualInfChar E a Ξ τ
  obtain rfl : m = m' := infChar_eq_dual_of_isCohFor hm hm' hcoh
  rw [CG.isRegAlg_iff]
  intro τ
  rw [CG.HasInfChar.infChar_eq (π := CG.mk π) (hm τ)]
  exact ⟨hnodup τ, hint τ⟩

end WignerVanishing

end RHDirect.Stage13GL_WignerHighestWeights

end
