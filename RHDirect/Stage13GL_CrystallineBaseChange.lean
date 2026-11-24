import RHDirect.Stage12GaloisShaLen
import RHDirect.Stage12FontainePeriods
import RHDirect.Stage13GL_LocalDvrNakayama
import RHDirect.Stage13GL_BernoulliAndWeylAlg
import RHDirect.Stage13GL_SelmerTransport
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.Bounds

/-!
# RHDirect.Stage13GL_CrystallineBaseChange

Option-C surgical consolidation of Alpöge's `GaloisLibrary/CrystallineBaseChange` (69 files, 6,144 L)
and `GaloisLibrary/SimultaneousEigenvectors` (1 file, 9 L) — 70 source files / 6,153 raw lines —
directly onto concrete Mathlib + `Stage12*` + `Stage13GL_*` types with zero fake wrappers.

## Sections
1. **Simultaneous Eigenvectors, Schur's Lemma, Quadratic Restriction & Twist Cardinality**:
   `simEig`, `IsIrr`, `RepIso`, `tw`, `DualTw`, `IsFlagOn`, `IsSSRep`,
   `schur_scalar_of_commutes_irreducible`, `resTwo`, `twCard`, `ss_restrict_normal`,
   `flag_stable`, `dual_det`, `det_flag`, `charpoly_smul`, `signNe`, `quadFam_one`, `quadFam`.
2. **Frobenius Eigenvalues, Root-Counting `EigData`, Place Transport, Galois Levels & Quadratic Counting**:
   `Qbar`, `cycBar`, `FrobEig`, `KillsMu`, `LevelAway`, `FlagAt`, `SlopesIn`, `EigData`,
   `frobEx`, `charpoly_pow_eq_map_pow`, `frobenius_power_compatibility`,
   `exists_quadratic_sign_character`, `rootSum`, `normV_under`, `tendsto_under'`,
   `exists_normV_eq_prime_pow_le_finrank`, `placeOf`, `move_place_over`, `LevelS`,
   `levelS_res`, `count_quadratic_of_hypotheses`.
3. **Capelli Casimir, `SL₂` Lowest-Weight Theory, Iwasawa Descent & Hecke Eigenforms**:
   `qdet2`, `cap2`, `sl2Low`, `holVec_low_of`, `aff`, `real_orth_decomp`, `iwasawa_gl2_pos`,
   `fin_of_ker`, `formalHecke`, `formalHecke_comm`, `eq_zero_of_formalHecke_eig`,
   `exists_simultaneous_hecke_eigenvector`, `hecke_eq_dc`.
4. **Admissible Local Components, Satake Pairing, CM Conjugation & Quadratic Base Change**:
   `kOrbit`, `annPart`, `exists_kType`, `pair_heckeVec`, `algSat`, `algSat_pow`, `dual_conj`,
   `infOf`, `regAlg_of_infOf`, `wt_eq`, `cPl`, `normV_cPl`, `conj_algebraMap`, `TRCuspRep`,
   `IsBC0`, `AttR`, `AttC`, `bcAtt0`, `bcConj0`, `not_totallyReal_and_totallyComplex`,
   `QuadBC0`, `IsBCw`, `QuadBCw`, `quadBCw_of_quadBC0`, `splitOf_assembly`.
-/

noncomputable section

open scoped BigOperators Matrix NumberField Pointwise ContDiff
open NumberField IsDedekindDomain Polynomial Filter Topology MeasureTheory
open RHDirect.Stage12GaloisShaLen
open RHDirect.Stage13GL_LocalDvrNakayama
open RHDirect.Stage13GL_BernoulliAndWeylAlg
open RHDirect.Stage13GL_SelmerTransport

namespace RHDirect.Stage13GL_CrystallineBaseChange

/-! ## Section 1: Simultaneous Eigenvectors, Schur's Lemma, Quadratic Restriction & Twist Cardinality -/

section SimEigAndLinearRep

/-- Any family of pairwise commuting endomorphisms on a finite-dimensional vector space over an
algebraically closed field has a nonzero simultaneous eigenvector inside every nonzero invariant
subspace (`SimultaneousEigenvectors/SimEig.lean`). -/
theorem simEig {K M : Type*} [Field K] [IsAlgClosed K] [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] {J : Type*} (T : J → Module.End K M)
    (hT : ∀ i j : J, T i * T j = T j * T i) (d : ℕ) (U : Submodule K M)
    (hd : Module.finrank K U = d) (hU : U ≠ ⊥) (hinv : ∀ j : J, ∀ x ∈ U, T j x ∈ U) :
    ∃ v ∈ U, v ≠ 0 ∧ ∀ j : J, ∃ c : K, T j v = c • v := by
  induction d using Nat.strong_induction_on generalizing U with
  | _ d ih =>
    by_cases h : ∀ j, ∃ c : K, ∀ x ∈ U, T j x = c • x
    · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
      refine ⟨v, hv, hv0, fun j => ?_⟩
      obtain ⟨c, hc⟩ := h j
      exact ⟨c, hc v hv⟩
    · rw [not_forall] at h
      obtain ⟨i, hi⟩ := h
      have : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hU
      obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((T i).restrict (hinv i) : Module.End K U)
      obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
      have hw1 : T i (w : M) = c • (w : M) := by
        simpa [LinearMap.restrict_apply] using congrArg Subtype.val hw.apply_eq_smul
      have hw0 : (w : M) ≠ 0 := fun h0 => hw.2 (Subtype.ext h0)
      have hlt : U ⊓ (T i).eigenspace c < U := by
        refine lt_of_le_of_ne inf_le_left fun heq => hi ⟨c, fun x hx => ?_⟩
        rw [← heq] at hx
        exact Module.End.mem_eigenspace_iff.mp hx.2
      have hne : U ⊓ (T i).eigenspace c ≠ ⊥ := by
        intro h0
        have hm : (w : M) ∈ U ⊓ (T i).eigenspace c :=
          ⟨w.2, Module.End.mem_eigenspace_iff.mpr hw1⟩
        rw [h0] at hm
        exact hw0 ((Submodule.mem_bot K).mp hm)
      have hst : ∀ j, ∀ x ∈ U ⊓ (T i).eigenspace c, T j x ∈ U ⊓ (T i).eigenspace c := by
        intro j x hx
        refine ⟨hinv j x hx.1, Module.End.mem_eigenspace_iff.mpr ?_⟩
        have h2 : T i x = c • x := Module.End.mem_eigenspace_iff.mp hx.2
        have h3 := LinearMap.congr_fun (hT i j) x
        simp only [Module.End.mul_apply] at h3
        rw [h3, h2, map_smul]
      obtain ⟨v, hv, hv0, hvj⟩ :=
        ih _ (hd ▸ Submodule.finrank_lt_finrank_of_lt hlt) _ rfl hne hst
      exact ⟨v, hv.1, hv0, hvj⟩

/-- Concrete irreducibility of a matrix representation `r : Γ →* GL (Fin n) k`. -/
def IsIrr {Γ k : Type*} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) : Prop :=
  (⊤ : Submodule k (Fin n → k)) ≠ ⊥ ∧
    (∀ (_ : Γ) (_ : Fin n → k), True) ∧
    ∀ W : Submodule k (Fin n → k), W ≤ ⊤ →
      (∀ s, ∀ v ∈ W, (r s : Matrix (Fin n) (Fin n) k) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤

/-- Concrete semisimplicity of a matrix representation `r : Γ →* GL (Fin n) k`. -/
def IsSSRep {Γ k : Type*} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) : Prop :=
  ∀ W : Submodule k (Fin n → k),
    (∀ s, ∀ v ∈ W, (r s : Matrix (Fin n) (Fin n) k) *ᵥ v ∈ W) →
    ∃ W' : Submodule k (Fin n → k),
      (∀ s, ∀ v ∈ W', (r s : Matrix (Fin n) (Fin n) k) *ᵥ v ∈ W') ∧ IsCompl W W'

/-- Concrete isomorphism (conjugacy) of matrix representations `r, r' : Γ →* GL (Fin n) k`. -/
def RepIso {Γ k : Type*} [Group Γ] [Field k] {n : ℕ} (r r' : Γ →* GL (Fin n) k) : Prop :=
  ∃ g : GL (Fin n) k, ∀ s, r' s = g * r s * g⁻¹

theorem RepIso.refl {Γ k : Type*} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) :
    RepIso r r := ⟨1, fun s => by simp⟩

theorem RepIso.symm {Γ k : Type*} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k}
    (h : RepIso r r') : RepIso r' r := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g⁻¹, fun s => by rw [hg s]; group⟩

theorem RepIso.trans {Γ k : Type*} [Group Γ] [Field k] {n : ℕ} {r r' r'' : Γ →* GL (Fin n) k}
    (h : RepIso r r') (h' : RepIso r' r'') : RepIso r r'' := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨g', hg'⟩ := h'
  exact ⟨g' * g, fun s => by rw [hg' s, hg s]; group⟩

/-- Scalar character twist `tw r δ : Γ →* GL (Fin n) k`, multiplying `r s` by `δ s • 1`. -/
def tw {Γ k : Type*} [Group Γ] [CommRing k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (δ : Γ →* kˣ) : Γ →* GL (Fin n) k where
  toFun s :=
    ⟨((δ s : kˣ) : k) • (r s).val, (((δ s)⁻¹ : kˣ) : k) • ((r s)⁻¹).val,
      by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, one_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one],
      by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, one_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one]⟩
  map_one' := by apply Units.ext; simp
  map_mul' s t := by
    apply Units.ext
    simp only [Units.val_mul, map_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm]

@[simp]
theorem tw_val {Γ k : Type*} [Group Γ] [CommRing k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (δ : Γ →* kˣ) (s : Γ) :
    ((tw r δ s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      ((δ s : kˣ) : k) • ((r s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := rfl

/-- Dual-twist relation `DualTw r θ`: `r ≃ r^∨ ⊗ θ`, i.e. `g * (r s)⁻¹ᵀ * g⁻¹ = (θ s)⁻¹ • r s`. -/
def DualTw {Γ k : Type*} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (θ : Γ →* kˣ) : Prop :=
  ∃ g : GL (Fin n) k, ∀ s,
    ((θ s : kˣ) : k) •
      ((g : Matrix (Fin n) (Fin n) k) * ((r s)⁻¹ : GL (Fin n) k).val.transpose *
        ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) =
      ((r s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)

/-- Upper-triangular flag of a representation `r` on a subgroup `H` with diagonal characters `κ`. -/
def IsFlagOn {Γ k : Type*} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (H : Subgroup Γ) (κ : Fin n → H →* kˣ) : Prop :=
  ∃ g : GL (Fin n) k, ∀ s : H,
    (∀ i j : Fin n, j < i → ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j = 0) ∧
    ∀ i : Fin n, ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i = κ i s

/-- Schur's lemma: any matrix commuting with an irreducible representation over an algebraically
closed field is scalar (`ResTwo.lean`). -/
theorem schur_scalar_of_commutes_irreducible {Γ k : Type*} [Group Γ] [Field k] [IsAlgClosed k]
    {n : ℕ} (r : Γ →* GL (Fin n) k) (hirr : IsIrr r) (g : Matrix (Fin n) (Fin n) k)
    (hg : ∀ s, g * (r s : Matrix (Fin n) (Fin n) k) = (r s : Matrix (Fin n) (Fin n) k) * g) :
    ∃ c : k, g = c • (1 : Matrix (Fin n) (Fin n) k) := by
  obtain ⟨hne, -, hmin⟩ := hirr
  have hnt : Nontrivial (Fin n → k) := by
    by_contra hc
    rw [not_nontrivial_iff_subsingleton] at hc
    exact hne (Subsingleton.elim _ _)
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (Matrix.toLin' g : Module.End k (Fin n → k))
  refine ⟨c, ?_⟩
  rcases hmin (Module.End.eigenspace (Matrix.toLin' g : Module.End k (Fin n → k)) c) le_top (by
      intro t v hv
      rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
      rw [Matrix.mulVec_mulVec, hg, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]) with h | h
  · exact absurd h hc
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ Module.End.eigenspace (Matrix.toLin' g : Module.End k (Fin n → k)) c := by
      rw [h]; trivial
    rw [Module.End.mem_eigenspace_iff] at hv
    rw [hv]; simp

private theorem resTwo_part_two {Γ Γ' k : Type*} [Group Γ] [Group Γ'] [Field k] [IsAlgClosed k]
    {n : ℕ} (φ : Γ' →* Γ) (δ : Γ →* kˣ) (h1 : ∀ s, δ s = 1 ↔ s ∈ φ.range)
    (h2 : ∀ s, δ s = 1 ∨ δ s = -1) (r r' : Γ →* GL (Fin n) k)
    (hirr : IsIrr (r.comp φ)) (hiso : RepIso (r.comp φ) (r'.comp φ)) :
    RepIso r r' ∨ RepIso (tw r δ) r' := by
  obtain ⟨g, hg⟩ := hiso
  have hH : ∀ s, δ s = 1 → r' s = g * r s * g⁻¹ := by
    intro s hs
    obtain ⟨x, rfl⟩ := (h1 s).1 hs
    exact hg x
  by_cases hall : ∀ s, δ s = 1
  · exact Or.inl ⟨g, fun s => hH s (hall s)⟩
  push Not at hall
  obtain ⟨t, ht⟩ := hall
  have ht' : δ t = -1 := (h2 t).resolve_left ht
  obtain ⟨u, hu⟩ : ∃ u : GL (Fin n) k, u = (r t)⁻¹ * g⁻¹ * r' t * g := ⟨_, rfl⟩
  have hrt : r' t = g * (r t * u) * g⁻¹ := by rw [hu]; group
  have hcomm : ∀ s, δ s = 1 → u * r s = r s * u := by
    intro s hs
    have e1 := hH s hs
    have e2 := hH (t * s * t⁻¹) (by simp [hs])
    simp only [map_mul, map_inv] at e2
    rw [e1, hrt] at e2
    have e3 : u * r s = (r t)⁻¹ * g⁻¹ *
        (g * (r t * u) * g⁻¹ * (g * r s * g⁻¹) * (g * (r t * u) * g⁻¹)⁻¹) * g * r t * u := by
      group
    rw [e3, e2]; group
  obtain ⟨c, hc⟩ := schur_scalar_of_commutes_irreducible (r.comp φ) hirr
    (u : Matrix (Fin n) (Fin n) k) (by
      intro x
      have := hcomm (φ x) ((h1 _).2 ⟨x, rfl⟩)
      simpa using congrArg Units.val this)
  have hcen : ∀ a : GL (Fin n) k, u * a = a * u := by
    intro a; apply Units.ext; simp [hc]
  have huu : u * u = 1 := by
    have e2 := hH (t * t) (by simp [ht'])
    simp only [map_mul] at e2
    rw [hrt] at e2
    have e3 : u * r t * u = (r t)⁻¹ * g⁻¹ *
        (g * (r t * u) * g⁻¹ * (g * (r t * u) * g⁻¹)) * g := by group
    rw [e2, hcen (r t)] at e3
    calc u * u = (r t)⁻¹ * (r t * u * u) := by group
      _ = 1 := by rw [e3]; group
  have hneg : ∀ s, δ s = -1 → r' s = g * (u * r s) * g⁻¹ := by
    intro s hs
    have e1 := hH (t⁻¹ * s) (by simp [hs, ht'])
    have e2 : r' s = r' t * r' (t⁻¹ * s) := by rw [← map_mul]; simp
    rw [e2, e1, hrt, ← hcen (r t), map_mul, map_inv]; group
  have hu2 : u = 1 ∨ u = -1 := by
    have e := congrArg Units.val huu
    rw [Units.val_mul, hc, Matrix.smul_mul, Matrix.one_mul, smul_smul, Units.val_one] at e
    have hn : Nonempty (Fin n) := by
      by_contra hne
      rw [not_nonempty_iff] at hne
      exact hirr.1 (Subsingleton.elim _ _)
    obtain ⟨i⟩ := hn
    have e' := congrFun (congrFun e i) i
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at e'
    rcases mul_self_eq_one_iff.1 e' with h | h
    · left; apply Units.ext; simp [hc, h]
    · right; apply Units.ext; simp [hc, h]
  rcases hu2 with h | h
  · refine Or.inl ⟨g, fun s => ?_⟩
    rcases h2 s with hs | hs
    · exact hH s hs
    · rw [hneg s hs, h, one_mul]
  · refine Or.inr ⟨g, fun s => ?_⟩
    rcases h2 s with hs | hs
    · rw [hH s hs]; congr 2; apply Units.ext; simp [tw_val, hs]
    · rw [hneg s hs, h]; congr 2; apply Units.ext; simp [tw_val, hs]

private theorem resTwo_part_one {Γ Γ' k : Type*} [Group Γ] [Group Γ'] [Field k] {n : ℕ}
    (φ : Γ' →* Γ) (δ : Γ →* kˣ) (h1 : ∀ s, δ s = 1 ↔ s ∈ φ.range)
    (h2 : ∀ s, δ s = 1 ∨ δ s = -1) (r : Γ →* GL (Fin n) k)
    (hirr : IsIrr r) (hn : ¬ RepIso r (tw r δ)) : IsIrr (r.comp φ) := by
  refine ⟨hirr.1, fun _ _ => trivial, ?_⟩
  intro W _ hW
  by_contra hcon
  push Not at hcon
  obtain ⟨hW0, hW1⟩ := hcon
  apply hn
  by_cases hall : ∀ s, δ s = 1
  · refine ⟨1, fun s => ?_⟩
    apply Units.ext; simp [tw_val, hall s]
  push Not at hall
  obtain ⟨t, ht⟩ := hall
  have ht' : δ t = -1 := (h2 t).resolve_left ht
  let ρ : Γ → (Fin n → k) →ₗ[k] (Fin n → k) :=
    fun s => Matrix.toLin' (r s : Matrix (Fin n) (Fin n) k)
  have hmul : ∀ a b v, ρ a (ρ b v) = ρ (a * b) v := by
    intro a b v; simp [ρ, Matrix.toLin'_apply, Matrix.mulVec_mulVec]
  have a1 : ∀ s, δ s = 1 → ∀ v ∈ W, ρ s v ∈ W := by
    intro s hs v hv
    obtain ⟨x, rfl⟩ := (h1 s).1 hs
    exact hW x v hv
  have a2 : ∀ s, δ s = -1 → ∀ v ∈ W, ρ s v ∈ W.map (ρ t) := by
    intro s hs v hv
    refine ⟨ρ (t⁻¹ * s) v, a1 _ (by simp [hs, ht']) v hv, ?_⟩
    rw [hmul]; simp
  have a3 : ∀ s, δ s = 1 → ∀ v ∈ W.map (ρ t), ρ s v ∈ W.map (ρ t) := by
    rintro s hs _ ⟨v, hv, rfl⟩
    rw [hmul]; exact a2 _ (by simp [hs, ht']) v hv
  have a4 : ∀ s, δ s = -1 → ∀ v ∈ W.map (ρ t), ρ s v ∈ W := by
    rintro s hs _ ⟨v, hv, rfl⟩
    rw [hmul]; exact a1 _ (by simp [hs, ht']) v hv
  have hinf : W ⊓ W.map (ρ t) = ⊥ := by
    refine (hirr.2.2 _ le_top ?_).resolve_right (fun h => hW1 (top_le_iff.1 (h ▸ inf_le_left)))
    intro s v hv
    rcases h2 s with hs | hs
    · exact ⟨a1 s hs v hv.1, a3 s hs v hv.2⟩
    · exact ⟨a4 s hs v hv.2, a2 s hs v hv.1⟩
  have hsup : W ⊔ W.map (ρ t) = ⊤ := by
    refine (hirr.2.2 _ le_top ?_).resolve_left (fun h => hW0 (le_bot_iff.1 (h ▸ le_sup_left)))
    intro s v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    show ρ s (a + b) ∈ _
    rw [map_add]
    rcases h2 s with hs | hs
    · exact Submodule.add_mem_sup (a1 s hs a ha) (a3 s hs b hb)
    · rw [add_comm]; exact Submodule.add_mem_sup (a4 s hs b hb) (a2 s hs a ha)
  have hc : IsCompl W (W.map (ρ t)) := IsCompl.of_eq hinf hsup
  let P : (Fin n → k) →ₗ[k] (Fin n → k) := LinearMap.ofIsCompl hc W.subtype (-(W.map (ρ t)).subtype)
  have p1 : ∀ v ∈ W, P v = v := fun v hv => LinearMap.ofIsCompl_apply_left hc (u := ⟨v, hv⟩)
  have p2 : ∀ v ∈ W.map (ρ t), P v = -v := fun v hv => LinearMap.ofIsCompl_apply_right hc (v := ⟨v, hv⟩)
  have hdec : ∀ v : Fin n → k, ∃ a ∈ W, ∃ b ∈ W.map (ρ t), a + b = v := fun v =>
    Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top)
  have hPP : P ∘ₗ P = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec v
    simp [p1 a ha, p2 b hb]
  have hPr : ∀ s, (δ s : k) • (ρ s ∘ₗ P) = P ∘ₗ ρ s := by
    intro s
    refine LinearMap.ext fun v => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec v
    rcases h2 s with hs | hs
    · simp [p1 a ha, p2 b hb, hs, p1 _ (a1 s hs a ha), p2 _ (a3 s hs b hb)]
    · simp [p1 a ha, p2 b hb, hs, p2 _ (a2 s hs a ha), p1 _ (a4 s hs b hb), add_comm]
  have hM : LinearMap.toMatrix' P * LinearMap.toMatrix' P = 1 := by
    rw [← LinearMap.toMatrix'_comp, hPP, LinearMap.toMatrix'_id]
  refine ⟨⟨LinearMap.toMatrix' P, LinearMap.toMatrix' P, hM, hM⟩, fun s => ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  apply Units.ext
  have := congrArg LinearMap.toMatrix' (hPr s)
  simp only [map_smul, LinearMap.toMatrix'_comp, ρ, LinearMap.toMatrix'_toLin'] at this
  simp only [Units.val_mul, tw_val, Matrix.smul_mul]
  exact this

/-- Index-2 restriction theorem: irreducibility and fiber-of-size-2 descent (`ResTwo.lean`). -/
theorem resTwo {Γ Γ' k : Type*} [Group Γ] [Group Γ'] [Field k] [IsAlgClosed k] {n : ℕ}
    (φ : Γ' →* Γ) (δ : Γ →* kˣ) (h1 : ∀ s, δ s = 1 ↔ s ∈ φ.range)
    (h2 : ∀ s, δ s = 1 ∨ δ s = -1) (r : Γ →* GL (Fin n) k) :
    (IsIrr r → ¬ RepIso r (tw r δ) → IsIrr (r.comp φ)) ∧
    ∀ r' : Γ →* GL (Fin n) k, IsIrr (r.comp φ) → RepIso (r.comp φ) (r'.comp φ) →
      RepIso r r' ∨ RepIso (tw r δ) r' :=
  ⟨resTwo_part_one φ δ h1 h2 r, fun r' => resTwo_part_two φ δ h1 h2 r r'⟩

/-- An irreducible `n`-dimensional representation admits at most `n²` self-twist characters
(`TwCard.lean`). -/
theorem twCard {Γ k : Type*} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (hirr : IsIrr r) (S : Finset (Γ →* kˣ)) (hS : ∀ δ ∈ S, RepIso r (tw r δ)) :
    S.card ≤ n ^ 2 := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd Submodule.eq_bot_of_subsingleton hirr.1
    · exact h
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  classical
  choose g hg using hS
  have key : ∀ δ (hδ : δ ∈ S), ∀ s,
      ((g δ hδ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * (r s : Matrix (Fin n) (Fin n) k) =
        ((δ s : kˣ) : k) • ((r s : Matrix (Fin n) (Fin n) k) *
          (g δ hδ : Matrix (Fin n) (Fin n) k)) := by
    intro δ hδ s
    have h1 := congrArg
      (fun A : GL (Fin n) k => (A : Matrix (Fin n) (Fin n) k) * (g δ hδ : Matrix (Fin n) (Fin n) k))
      (hg δ hδ s)
    simp only [tw_val, Units.val_mul, mul_assoc, Units.inv_mul, mul_one] at h1
    rw [← h1, smul_mul_assoc]
  have hli : LinearIndependent k
      (fun δ : S => ((g δ.1 δ.2 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc δ0
    have hsum : ∀ s, ∑ δ : S, (c δ * ((δ.1 s : kˣ) : k)) •
        ((g δ.1 δ.2 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 0 := by
      intro s
      have h2 : (r s : Matrix (Fin n) (Fin n) k) *
          ∑ δ : S, (c δ * ((δ.1 s : kˣ) : k)) •
            ((g δ.1 δ.2 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 0 := by
        rw [Finset.mul_sum]
        have e : ∑ δ : S, (r s : Matrix (Fin n) (Fin n) k) *
            ((c δ * ((δ.1 s : kˣ) : k)) •
              ((g δ.1 δ.2 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) =
            (∑ δ : S, c δ • ((g δ.1 δ.2 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) *
              (r s : Matrix (Fin n) (Fin n) k) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun δ _ => ?_
          rw [smul_mul_assoc, key δ.1 δ.2 s, mul_smul_comm, mul_smul]
        rw [e, hc, zero_mul]
      have h3 := congrArg (fun A => (((r s)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * A) h2
      simpa [← mul_assoc] using h3
    have hD := (linearIndependent_monoidHom Γ k).comp
      (fun δ : S => (Units.coeHom k).comp δ.1)
      (fun a b hab => Subtype.ext (MonoidHom.ext fun s => Units.ext (DFunLike.congr_fun hab s)))
    rw [Fintype.linearIndependent_iff] at hD
    have hz : ∀ i j, ∀ δ : S,
        c δ * ((g δ.1 δ.2 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j = 0 := by
      intro i j
      apply hD
      funext s
      have e := congrFun (congrFun (hsum s) i) j
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at e
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply, MonoidHom.coe_comp,
        Units.coeHom_apply, Pi.zero_apply]
      rw [← e]
      exact Finset.sum_congr rfl fun δ _ => by ring
    by_contra hc0
    have h0 : ((g δ0.1 δ0.2 : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 0 := by
      ext i j
      exact (mul_eq_zero.mp (hz i j δ0)).resolve_left hc0
    exact (g δ0.1 δ0.2).ne_zero h0
  have hcard := hli.fintype_card_le_finrank
  rw [Module.finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one, Fintype.card_coe] at hcard
  rw [sq]
  exact hcard

/-- Clifford's theorem: restriction of a semisimple matrix representation to a normal subgroup
is semisimple (`SemisimpleRestrictionToNormalSubgroup.lean`). -/
theorem ss_restrict_normal {Γ k : Type*} [Group Γ] [Field k] {n : ℕ}
    (r : Γ →* GL (Fin n) k) (N : Subgroup Γ) [hN : N.Normal] (hss : IsSSRep r) :
    IsSSRep (r.comp N.subtype) := by
  let ρ : Γ →* Module.End k (Fin n → k) :=
    { toFun := fun g => Matrix.toLin' (r g : Matrix (Fin n) (Fin n) k)
      map_one' := by ext v; simp
      map_mul' := fun a b => by ext v; simp }
  have hmul : ∀ (a b : Γ) (v : Fin n → k), ρ a (ρ b v) = ρ (a * b) v := fun a b v => by
    rw [map_mul]; rfl
  intro W hW
  have hWN : ∀ g ∈ N, ∀ v ∈ W, ρ g v ∈ W := fun g hg v hv => hW ⟨g, hg⟩ v hv
  obtain ⟨W', ⟨hW's, hW'd⟩, hmax⟩ := exists_maximal_of_wellFoundedGT
    (fun U : Submodule k (Fin n → k) => (∀ g ∈ N, ∀ v ∈ U, ρ g v ∈ U) ∧ Disjoint W U)
    ⟨⊥, fun g _ v hv => by rw [Submodule.mem_bot] at hv ⊢; rw [hv, map_zero], disjoint_bot_right⟩
  refine ⟨W', fun g v hv => hW's g.1 g.2 v hv, hW'd, ?_⟩
  rw [codisjoint_iff]
  obtain ⟨C, hCs, hC⟩ := hss (⨅ g : Γ, (W ⊔ W').comap (ρ g)) (by
    intro g v hv
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hv ⊢
    intro h
    change ρ h (ρ g v) ∈ W ⊔ W'
    rw [hmul]; exact hv (h * g))
  by_cases hC0 : C = ⊥
  · have hU := hC.sup_eq_top
    rw [hC0, sup_bot_eq] at hU
    rw [eq_top_iff]
    intro v _
    have hv : v ∈ (⨅ g : Γ, (W ⊔ W').comap (ρ g)) := hU ▸ Submodule.mem_top
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hv
    simpa using hv 1
  exfalso
  obtain ⟨S, ⟨hSs, hS0, hSC⟩, hmin⟩ := exists_minimal_of_wellFoundedLT
    (fun U : Submodule k (Fin n → k) => (∀ g ∈ N, ∀ v ∈ U, ρ g v ∈ U) ∧ U ≠ ⊥ ∧ U ≤ C)
    ⟨C, fun g _ v hv => hCs g v hv, hC0, le_rfl⟩
  have hsup : ∀ m ∈ N, ∀ v ∈ W ⊔ W', ρ m v ∈ W ⊔ W' := by
    intro m hm v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add]
    exact Submodule.add_mem_sup (hWN m hm a ha) (hW's m hm b hb)
  have hmapN : ∀ g : Γ, ∀ m ∈ N, ∀ v ∈ S.map (ρ g), ρ m v ∈ S.map (ρ g) := by
    rintro g m hm _ ⟨s, hs, rfl⟩
    refine ⟨ρ (g⁻¹ * m * g) s, hSs _ (hN.conj_mem' m hm g) s hs, ?_⟩
    rw [hmul, hmul]; simp [mul_assoc]
  have key : ∀ g : Γ, ∀ s ∈ S, ρ g s ∈ W ⊔ W' := by
    intro g
    have hinf_eq : S.map (ρ g) ⊓ (W ⊔ W') = ⊥ ∨ S.map (ρ g) ⊓ (W ⊔ W') = S.map (ρ g) := by
      let U := S ⊓ (W ⊔ W').comap (ρ g)
      have hU_N : ∀ m ∈ N, ∀ v ∈ U, ρ m v ∈ U := by
        intro m hm v hv
        refine ⟨hSs m hm v hv.1, ?_⟩
        change ρ g (ρ m v) ∈ W ⊔ W'
        rw [hmul, show g * m = (g * m * g⁻¹) * g by group, ← hmul]
        exact hsup _ (hN.conj_mem m hm g) _ hv.2
      by_cases hU0 : U = ⊥
      · left
        rw [eq_bot_iff]
        rintro _ ⟨⟨s, hs, rfl⟩, hsw⟩
        have hsU : s ∈ U := ⟨hs, hsw⟩
        rw [hU0, Submodule.mem_bot] at hsU
        rw [hsU, map_zero]; exact Submodule.zero_mem _
      · right
        have hUS : U = S := le_antisymm inf_le_left (hmin ⟨hU_N, hU0, inf_le_left.trans hSC⟩ inf_le_left)
        rw [inf_eq_left]
        rintro _ ⟨s, hs, rfl⟩
        have hsU : s ∈ U := hUS.symm ▸ hs
        exact hsU.2
    rcases hinf_eq with hdis | hle
    · exfalso
      have hdis' : Disjoint (W ⊔ W') (S.map (ρ g)) := by
        rw [disjoint_iff, inf_comm]; exact hdis
      have hWdis : Disjoint W (W' ⊔ S.map (ρ g)) := by
        rw [disjoint_iff, eq_bot_iff]
        intro x hx
        obtain ⟨hxW, hx2⟩ := hx
        obtain ⟨w', hw', y, hy, rfl⟩ := Submodule.mem_sup.mp hx2
        have hy_mem : y ∈ (W ⊔ W') ⊓ S.map (ρ g) := by
          refine ⟨?_, hy⟩
          have : w' + y - w' ∈ W ⊔ W' :=
            (W ⊔ W').sub_mem (Submodule.mem_sup_left hxW) (Submodule.mem_sup_right hw')
          simpa using this
        rw [disjoint_iff.mp hdis', Submodule.mem_bot] at hy_mem
        subst hy_mem
        rw [add_zero] at hxW ⊢
        exact (disjoint_iff.mp hW'd).le ⟨hxW, hw'⟩
      have hstab : ∀ m ∈ N, ∀ v ∈ W' ⊔ S.map (ρ g), ρ m v ∈ W' ⊔ S.map (ρ g) := by
        intro m hm v hv
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
        rw [map_add]
        exact Submodule.add_mem_sup (hW's m hm a ha) (hmapN g m hm b hb)
      have hle' := hmax ⟨hstab, hWdis⟩ le_sup_left
      have hSg : S.map (ρ g) ≤ W' := le_sup_right.trans hle'
      obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
      have hgs : ρ g s ∈ (W ⊔ W') ⊓ S.map (ρ g) :=
        ⟨Submodule.mem_sup_right (hSg ⟨s, hs, rfl⟩), ⟨s, hs, rfl⟩⟩
      rw [disjoint_iff.mp hdis', Submodule.mem_bot] at hgs
      have := congrArg (ρ g⁻¹) hgs
      rw [hmul, inv_mul_cancel, map_one, map_zero] at this
      exact hs0 this
    · intro s hs
      have : ρ g s ∈ S.map (ρ g) ⊓ (W ⊔ W') := hle.symm ▸ ⟨s, hs, rfl⟩
      exact this.2
  obtain ⟨s, hs, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  have hs_inf : s ∈ (⨅ g : Γ, (W ⊔ W').comap (ρ g)) ⊓ C :=
    ⟨(Submodule.mem_iInf _).mpr fun g => key g s hs, hSC hs⟩
  rw [hC.inf_eq_bot, Submodule.mem_bot] at hs_inf
  exact hs0 hs_inf

/-- Any 2-dimensional representation is self-dual twisted by its determinant (`CharpolySmul.lean`). -/
theorem dual_det {Γ k : Type*} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) :
    DualTw r (Matrix.GeneralLinearGroup.det.comp r) := by
  refine ⟨⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by simp [Matrix.one_fin_two],
    by simp [Matrix.one_fin_two]⟩, fun s => ?_⟩
  have hdet0 : (r s).val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp (r s).isUnit).ne_zero
  have hinv : ((r s)⁻¹ : GL (Fin 2) k).val =
      (r s).val.det⁻¹ • !![(r s).val 1 1, -(r s).val 0 1; -(r s).val 1 0, (r s).val 0 0] := by
    have hmul : (r s).val * ((r s).val.det⁻¹ •
        !![(r s).val 1 1, -(r s).val 0 1; -(r s).val 1 0, (r s).val 0 0]) = 1 := by
      rw [Matrix.mul_smul]
      ext a b
      have hdet_eq : (r s).val 0 0 * (r s).val 1 1 - (r s).val 0 1 * (r s).val 1 0 = (r s).val.det :=
        (Matrix.det_fin_two (r s).val).symm
      fin_cases a <;> fin_cases b <;>
        simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.one_apply, Fin.isValue,
          Matrix.smul_apply, smul_eq_mul, ↓reduceIte, Fin.zero_eta, Fin.mk_one,
          zero_ne_one, one_ne_zero]
      · rw [← mul_inv_cancel₀ hdet0, ← hdet_eq]; ring
      · ring
      · ring
      · rw [← mul_inv_cancel₀ hdet0, ← hdet_eq]; ring
    have heq := congrArg (fun M => ((r s)⁻¹ : GL (Fin 2) k).val * M) hmul
    simpa [← Matrix.mul_assoc] using heq.symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hinv, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      Matrix.GeneralLinearGroup.val_det_apply] <;>
    field_simp [hdet0]

/-- Determinant of a 2-dimensional representation with a flag is the product of the diagonal
characters (`CharpolySmul.lean`). -/
theorem det_flag {Γ k : Type*} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) (H : Subgroup Γ)
    (κ : Fin 2 → H →* kˣ) (h : IsFlagOn r H κ) (s : H) :
    Matrix.GeneralLinearGroup.det (r s) = κ 0 s * κ 1 s := by
  obtain ⟨g, hg⟩ := h
  have : Matrix.GeneralLinearGroup.det (r s) = Matrix.GeneralLinearGroup.det (g * r s * g⁻¹) := by
    rw [map_mul, map_mul, map_inv, mul_right_comm]; simp
  rw [this]
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two,
    (hg s).1 1 0 (by decide), (hg s).2 0, (hg s).2 1]
  simp

/-- A diagonalized normal-subgroup action with distinct characters extends to a flag on any
normalizer (`CharpolySmul.lean`). -/
theorem flag_stable {Γ k : Type*} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k)
    (D N N' : Subgroup Γ) (hN : N ≤ N') (hND : N' ≤ D)
    (hc : ∀ d ∈ D, ∀ s ∈ N', d⁻¹ * s * d ∈ N')
    (χ : Fin 2 → Γ →* kˣ) (g : GL (Fin 2) k)
    (hg : ∀ s ∈ N', ((g * r s * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      Matrix.diagonal fun i => (χ i s : k))
    (hs : ∃ s ∈ N, χ 0 s ≠ χ 1 s)
    (h1 : ∀ d ∈ D, ∀ s ∈ N', χ 0 (d⁻¹ * s * d) = χ 0 s) :
    ∃ κ : Fin 2 → D →* kˣ, IsFlagOn r D κ ∧ ∀ i, ∀ s (hsN : s ∈ N), κ i ⟨s, hND (hN hsN)⟩ = χ i s := by
  let M : Γ → Matrix (Fin 2) (Fin 2) k := fun s => ((g * r s * g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)
  have hmul : ∀ a b, M (a * b) = M a * M b := fun a b => by
    simp only [M, map_mul, ← Units.val_mul]; congr 1; group
  have h1' : ∀ s ∈ N', M s 1 0 = 0 := fun s hs' => by rw [show M s = _ from hg s hs']; simp
  have h01 : ∀ s ∈ N', M s 0 1 = 0 := fun s hs' => by rw [show M s = _ from hg s hs']; simp
  have hd0 : ∀ s ∈ N', M s 0 0 = χ 0 s := fun s hs' => by rw [show M s = _ from hg s hs']; simp
  have hd1 : ∀ s ∈ N', M s 1 1 = χ 1 s := fun s hs' => by rw [show M s = _ from hg s hs']; simp
  obtain ⟨s0, hs0, hne⟩ := hs
  have hs0' : s0 ∈ N' := hN hs0
  have h3 : ∀ d ∈ D, M d 1 0 = 0 := by
    intro d hd
    have e : d * (d⁻¹ * s0 * d) = s0 * d := by group
    have e2 : (M d * M (d⁻¹ * s0 * d)) 1 0 = (M s0 * M d) 1 0 := by
      rw [← hmul, ← hmul, e]
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two] at e2
    rw [h1' _ (hc d hd s0 hs0'), h1' _ hs0', hd0 _ (hc d hd s0 hs0'), hd1 _ hs0',
      h1 d hd s0 hs0'] at e2
    have hdiff : (χ 0 s0 : k) - χ 1 s0 ≠ 0 := sub_ne_zero.2 fun h => hne (Units.ext h)
    apply mul_left_cancel₀ hdiff
    linear_combination e2
  have h00_mul : ∀ d₁ d₂ : D, M (d₁ * d₂) 0 0 = M d₁ 0 0 * M d₂ 0 0 := fun d₁ d₂ => by
    rw [hmul, Matrix.mul_apply, Fin.sum_univ_two, h3 d₂.1 d₂.2]; ring
  have h11_mul : ∀ d₁ d₂ : D, M (d₁ * d₂) 1 1 = M d₁ 1 1 * M d₂ 1 1 := fun d₁ d₂ => by
    rw [hmul, Matrix.mul_apply, Fin.sum_univ_two, h3 d₁.1 d₁.2]; ring
  refine ⟨fun i => MonoidHom.toHomUnits
    { toFun := fun s => M s.1 i i
      map_one' := by simp [M]
      map_mul' := fun s t => by
        fin_cases i
        · exact h00_mul s t
        · exact h11_mul s t },
    ⟨g, fun s => ⟨fun i j hij => ?_, fun i => rfl⟩⟩,
    fun i s hsN => Units.ext (by fin_cases i; exact hd0 s (hN hsN); exact hd1 s (hN hsN))⟩
  fin_cases i <;> fin_cases j
  · exact absurd hij (by decide)
  · exact absurd hij (by decide)
  · exact h3 s.1 s.2
  · exact absurd hij (by decide)

/-- Scaling a 2×2 matrix scales the roots of its characteristic polynomial (`CharpolySmul.lean`). -/
theorem charpoly_smul {k : Type*} [Field k] (φ : k →+* ℂ) (M : Matrix (Fin 2) (Fin 2) k)
    (c : k) (α β : ℂ)
    (h : M.charpoly.map φ = (X - C α) * (X - C β)) :
    (c • M).charpoly.map φ = (X - C (φ c * α)) * (X - C (φ c * β)) := by
  have h2 : ∀ A : Matrix (Fin 2) (Fin 2) k,
      A.charpoly.map φ = X ^ 2 - C (φ (A.trace)) * X + C (φ A.det) := fun A => by
    rw [Matrix.charpoly_fin_two]
    simp [map_sub, map_add, map_mul, Matrix.trace_fin_two, Matrix.det_fin_two]
  rw [h2 M] at h
  rw [h2 (c • M)]
  have htr : (c • M).trace = c * M.trace := by simp [Matrix.trace_smul]
  have hdet : (c • M).det = c ^ 2 * M.det := by simp
  have hcoeff1 := congrArg (fun p : Polynomial ℂ => p.coeff 1) h
  have hcoeff0 := congrArg (fun p : Polynomial ℂ => p.coeff 0) h
  simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C, mul_sub, sub_mul,
    coeff_mul_X, coeff_X_mul] at hcoeff1 hcoeff0
  norm_num at hcoeff1 hcoeff0
  have e1 : φ M.trace = α + β := by linear_combination -hcoeff1
  have e0 : φ M.det = α * β := by linear_combination hcoeff0
  rw [htr, hdet]
  simp only [map_mul, map_pow, e1, e0, map_add]
  ring

end SimEigAndLinearRep

/-! ### 1.2 Distinct Quadratic Restriction Subgroups (`SignNe`) & Coprime CM Family (`QuadFam`) -/

section SignNeAndQuadFam

/-- Galois restriction homomorphism `G K Ω →* G F Ω`. -/
abbrev res (F Ω K : Type*) [Field F] [Field K] [Field Ω] [Algebra F K] [Algebra F Ω]
    [Algebra K Ω] [IsScalarTower F K Ω] : G K Ω →* G F Ω :=
  AlgEquiv.restrictScalarsHom F

theorem range_res_eq {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    (K : Type*) [Field K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] :
    (res F Ω K).range = (IsScalarTower.toAlgHom F K Ω).fieldRange.fixingSubgroup := by
  ext σ
  rw [IntermediateField.mem_fixingSubgroup_iff, MonoidHom.mem_range]
  constructor
  · rintro ⟨τ, rfl⟩ y hy
    obtain ⟨k, rfl⟩ := AlgHom.mem_fieldRange.mp hy
    exact τ.commutes k
  · intro h
    refine ⟨AlgEquiv.ofRingEquiv (f := (σ : Ω ≃+* Ω))
      fun k => h _ (AlgHom.mem_fieldRange.mpr ⟨k, rfl⟩), ?_⟩
    ext y
    rfl

theorem equiv_of_range {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
    (K K' : Type*) [Field K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω]
    [Field K'] [Algebra F K'] [Algebra K' Ω] [IsScalarTower F K' Ω]
    (h : (res F Ω K).range = (res F Ω K').range) : Nonempty (K ≃ₐ[F] K') := by
  have hK := InfiniteGalois.fixedField_fixingSubgroup (IsScalarTower.toAlgHom F K Ω).fieldRange
  have hK' := InfiniteGalois.fixedField_fixingSubgroup (IsScalarTower.toAlgHom F K' Ω).fieldRange
  rw [range_res_eq, range_res_eq] at h
  have he : (IsScalarTower.toAlgHom F K Ω).fieldRange =
      (IsScalarTower.toAlgHom F K' Ω).fieldRange := by
    rw [← hK, ← hK', h]
  have he' : (IsScalarTower.toAlgHom F K Ω).range = (IsScalarTower.toAlgHom F K' Ω).range := by
    rw [← AlgHom.fieldRange_toSubalgebra, ← AlgHom.fieldRange_toSubalgebra, he]
  exact ⟨(AlgEquiv.ofInjectiveField _).trans
    ((Subalgebra.equivOfEq _ _ he').trans (AlgEquiv.ofInjectiveField _).symm)⟩

/-- Two quadratic number fields with coprime discriminants have distinct absolute Galois subgroups
inside `G ℚ Ω` (`SignNe.lean`). -/
theorem signNe (K K' Ω : Type*) [Field K] [NumberField K] [Field K'] [NumberField K']
    [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [Algebra K' Ω] [IsScalarTower ℚ K Ω]
    [IsScalarTower ℚ K' Ω] [IsAlgClosure ℚ Ω] (hK : Module.finrank ℚ K = 2)
    (hcop : IsCoprime (discr K) (discr K')) :
    (res ℚ Ω K).range ≠ (res ℚ Ω K').range := by
  intro heq
  obtain ⟨e⟩ := equiv_of_range (F := ℚ) (Ω := Ω) K K' heq
  rw [← NumberField.discr_eq_discr_of_algEquiv (K := K) e, isCoprime_self, Int.isUnit_iff] at hcop
  have hgt := NumberField.abs_discr_gt_two (K := K) (by omega)
  rcases hcop with h | h <;> rw [h] at hgt <;> norm_num at hgt

/-- Concrete imaginary quadratic CM field `ℚ(√(-p))` for a prime `p ≡ 3 (mod 4)`, constructed
directly via `QuadraticAlgebra ℚ (-((p + 1) / 4 : ℚ)) 1` with `discr = -p`. -/
private abbrev ImagQuadField (p : ℕ) : Type :=
  QuadraticAlgebra ℚ (-(((p + 1) / 4 : ℕ) : ℚ)) 1

private theorem imagQuadField_irred {p : ℕ} (hp : p.Prime) (h4 : p % 4 = 3) (r : ℚ) :
    r ^ 2 ≠ -(((p + 1) / 4 : ℕ) : ℚ) + 1 * r := by
  have hm : (4 : ℚ) * (((p + 1) / 4 : ℕ) : ℚ) = (p : ℚ) + 1 := by
    have h4nat : 4 * ((p + 1) / 4) = p + 1 := by omega
    exact_mod_cast h4nat
  have hp_pos : (0 : ℚ) < p := by exact_mod_cast hp.pos
  intro h
  have hsq : (2 * r - 1) ^ 2 + (p : ℚ) = 0 := by linear_combination 4 * h - hm
  nlinarith [sq_nonneg (2 * r - 1)]

/-- Existence of an imaginary quadratic CM field of discriminant `-p` for every prime `p ≡ 3 (mod 4)`
(`QuadFam.lean` — proved directly with 0 external dependencies!). -/
theorem quadFam_one (p : ℕ) (hp : p.Prime) (h4 : p % 4 = 3) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K),
      Module.finrank ℚ K = 2 ∧ discr K = -(p : ℤ) := by
  have : Fact (∀ r : ℚ, r ^ 2 ≠ -(((p + 1) / 4 : ℕ) : ℚ) + 1 * r) := ⟨imagQuadField_irred hp h4⟩
  let _ : Field (ImagQuadField p) := QuadraticAlgebra.instField
  have hfin : Module.finrank ℚ (ImagQuadField p) = 2 := by
    simpa using Module.finrank_eq_card_basis (QuadraticAlgebra.basis (-(((p + 1) / 4 : ℕ) : ℚ)) (1 : ℚ))
  have : NumberField (ImagQuadField p) :=
    { to_charZero := QuadraticAlgebra.instCharZero
      to_finiteDimensional := Module.Finite.of_basis
        (QuadraticAlgebra.basis (-(((p + 1) / 4 : ℕ) : ℚ)) (1 : ℚ)) }
  let m : ℕ := (p + 1) / 4
  have hm4 : 4 * m = p + 1 := by omega
  let gen : ImagQuadField p := ⟨0, 1⟩
  have hgen_sq : gen ^ 2 - gen + (m : ImagQuadField p) = 0 := by
    rw [sq]
    apply QuadraticAlgebra.ext
    · simp [gen, m]
    · simp [gen]
  have htc : IsTotallyComplex (ImagQuadField p) := by
    refine ⟨fun v => ?_⟩
    by_contra hnot
    have hreal : v.IsReal := InfinitePlace.not_isComplex_iff_isReal.mp hnot
    have him : (v.embedding gen).im = 0 :=
      Complex.conj_eq_iff_im.mp (RingHom.congr_fun (InfinitePlace.isReal_iff.mp hreal) gen)
    have hrootC : (v.embedding gen) ^ 2 - v.embedding gen + (m : ℂ) = 0 := by
      have := congrArg v.embedding hgen_sq
      simpa [map_sub, map_add, map_pow, map_natCast] using this
    have hroot : (v.embedding gen).re ^ 2 - (v.embedding gen).re + (m : ℝ) = 0 := by
      have hre := congrArg Complex.re hrootC
      simp [sq, him] at hre
      linarith
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hmR : (4 : ℝ) * (m : ℝ) = (p : ℝ) + 1 := by exact_mod_cast hm4
    nlinarith [sq_nonneg (2 * (v.embedding gen).re - 1)]
  have : Algebra.IsQuadraticExtension ℚ (ImagQuadField p) := ⟨hfin⟩
  have : IsCMField (ImagQuadField p) := IsCMField.ofCMExtension ℚ (ImagQuadField p)
  have hgen_int : IsIntegral ℤ gen := by
    refine ⟨X ^ 2 - X + C (m : ℤ), ?_, ?_⟩
    · have h1 : (X ^ 2 - X : Polynomial ℤ).Monic :=
        (monic_X_pow 2).sub_of_left (by simp)
      have hdeg : (C (m : ℤ) : Polynomial ℤ).degree < (X ^ 2 - X : Polynomial ℤ).degree := by
        rw [degree_sub_eq_left_of_degree_lt (by simp)]
        exact lt_of_le_of_lt degree_C_le (by simp)
      exact h1.add_of_left hdeg
    · simpa [aeval_def, eval₂_sub, eval₂_add, eval₂_pow, eval₂_X, eval₂_C] using hgen_sq
  let b : Module.Basis (Fin 2) ℚ (ImagQuadField p) :=
    QuadraticAlgebra.basis (-(((p + 1) / 4 : ℕ) : ℚ)) (1 : ℚ)
  have hb0 : b 0 = 1 := by
    apply QuadraticAlgebra.ext
    · simp [b, QuadraticAlgebra.basis]; rfl
    · simp [b, QuadraticAlgebra.basis]; rfl
  have hb1 : b 1 = gen := QuadraticAlgebra.ext (by simp [b, QuadraticAlgebra.basis, gen]) (by simp [b, QuadraticAlgebra.basis, gen])
  have hbrepr : ∀ z : ImagQuadField p, b.repr z 0 = z.re ∧ b.repr z 1 = z.im := fun z => by
    have hz : z = z.re • b 0 + z.im • b 1 := by
      rw [hb0, hb1]
      apply QuadraticAlgebra.ext <;> simp [gen]
    constructor
    · conv_lhs => rw [hz]
      simp [map_add, map_smul]
    · conv_lhs => rw [hz]
      simp [map_add, map_smul]
  have hlmm : ∀ (z : ImagQuadField p),
      Algebra.leftMulMatrix b z 0 0 = z.re ∧
      Algebra.leftMulMatrix b z 1 0 = z.im ∧
      Algebra.leftMulMatrix b z 0 1 = -(m : ℚ) * z.im ∧
      Algebra.leftMulMatrix b z 1 1 = z.re + z.im := fun z => by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Algebra.leftMulMatrix_eq_repr_mul, hb0, mul_one, (hbrepr z).1]
    · rw [Algebra.leftMulMatrix_eq_repr_mul, hb0, mul_one, (hbrepr z).2]
    · rw [Algebra.leftMulMatrix_eq_repr_mul, hb1, (hbrepr (z * gen)).1]
      simp [gen, m]
    · rw [Algebra.leftMulMatrix_eq_repr_mul, hb1, (hbrepr (z * gen)).2]
      simp [gen]
  have htr_formula : ∀ z : ImagQuadField p,
      Algebra.trace ℚ (ImagQuadField p) z = 2 * z.re + z.im := fun z => by
    rw [Algebra.trace_eq_matrix_trace b, Matrix.trace, Fin.sum_univ_two]
    simp only [Matrix.diag_apply, (hlmm z).1, (hlmm z).2.2.2]
    ring
  have hnorm_formula : ∀ z : ImagQuadField p,
      Algebra.norm ℚ z = z.re ^ 2 + z.re * z.im + (m : ℚ) * z.im ^ 2 := fun z => by
    rw [Algebra.norm_eq_matrix_det b, Matrix.det_fin_two,
      (hlmm z).1, (hlmm z).2.1, (hlmm z).2.2.1, (hlmm z).2.2.2]
    ring
  have hdiscr_b : Algebra.discr ℚ b = -(p : ℚ) := by
    rw [Algebra.discr_def, Matrix.det_fin_two]
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, hb0, hb1, mul_one, one_mul,
      htr_formula]
    have h1r : (1 : ImagQuadField p).re = 1 := rfl
    have h1i : (1 : ImagQuadField p).im = 0 := rfl
    have hgr : gen.re = 0 := rfl
    have hgi : gen.im = 1 := rfl
    have hgg_r : (gen * gen).re = -(m : ℚ) := by simp [gen, m]
    have hgg_i : (gen * gen).im = 1 := by simp [gen]
    rw [h1r, h1i, hgr, hgi, hgg_r, hgg_i]
    have hmQ : (4 : ℚ) * (m : ℚ) = (p : ℚ) + 1 := by exact_mod_cast hm4
    linarith
  have hmem_int : ∀ z : ImagQuadField p, IsIntegral ℤ z ↔
      ∃ a c : ℤ, z.re = a ∧ z.im = c := by
    intro z
    constructor
    · intro hz
      have htr_int : IsIntegral ℤ (Algebra.trace ℚ (ImagQuadField p) z) :=
        Algebra.isIntegral_trace hz
      obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.mp htr_int
      obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_norm ℚ hz)
      rw [htr_formula, eq_intCast] at ht
      rw [hnorm_formula, eq_intCast] at hn
      have hmQ : (4 : ℚ) * (m : ℚ) = (p : ℚ) + 1 := by exact_mod_cast hm4
      have hpb : (p : ℚ) * z.im ^ 2 = ((4 * n - t ^ 2 : ℤ) : ℚ) := by
        push_cast; rw [ht, hn]; linear_combination -z.im ^ 2 * hmQ
      have hden_b : z.im.den = 1 := by
        by_contra hd
        obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hd
        have hrel : (p : ℤ) * z.im.num ^ 2 = (4 * n - t ^ 2) * (z.im.den : ℤ) ^ 2 := by
          have h1 := congrArg (· * ((z.im.den : ℚ) ^ 2)) hpb
          have h2 : z.im * (z.im.den : ℚ) = (z.im.num : ℚ) := Rat.mul_den_eq_num z.im
          have h3 : (p : ℚ) * (z.im.num : ℚ) ^ 2 = ((4 * n - t ^ 2 : ℤ) : ℚ) * (z.im.den : ℚ) ^ 2 := by
            calc (p : ℚ) * (z.im.num : ℚ) ^ 2 = (p : ℚ) * (z.im * (z.im.den : ℚ)) ^ 2 := by rw [h2]
              _ = (p : ℚ) * z.im ^ 2 * (z.im.den : ℚ) ^ 2 := by ring
              _ = ((4 * n - t ^ 2 : ℤ) : ℚ) * (z.im.den : ℚ) ^ 2 := h1
          exact_mod_cast h3
        have hq_int : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
        have hqd_int : (q : ℤ) ∣ (z.im.den : ℤ) := Int.ofNat_dvd.mpr hqd
        have hq2 : (q : ℤ) ^ 2 ∣ (p : ℤ) * z.im.num ^ 2 := by
          rw [hrel]; exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hqd_int 2) _
        have hcop : IsCoprime (z.im.num : ℤ) (z.im.den : ℤ) :=
          Int.isCoprime_iff_nat_coprime.mpr z.im.reduced
        have hq_not_num : ¬ (q : ℤ) ∣ z.im.num := fun hqn =>
          hq_int.not_isUnit (hcop.isUnit_of_dvd' hqn hqd_int)
        have hq2_dvd_p : (q : ℤ) ^ 2 ∣ (p : ℤ) :=
          ((hq_int.coprime_iff_not_dvd.mpr hq_not_num).pow_right.pow_left).dvd_of_dvd_mul_right hq2
        have hq2_nat : q ^ 2 ∣ p := Int.ofNat_dvd.mp hq2_dvd_p
        have hle : q ^ 2 ≤ p := Nat.le_of_dvd hp.pos hq2_nat
        have hq_eq : q = p :=
          (Nat.prime_dvd_prime_iff_eq hq hp).mp (dvd_trans (dvd_pow_self q (by norm_num)) hq2_nat)
        subst hq_eq
        nlinarith [hp.two_le]
      set c : ℤ := z.im.num
      have hc : z.im = (c : ℚ) := (Rat.coe_int_num_of_den_eq_one hden_b).symm
      have h2a : 2 * z.re = (t : ℚ) - (c : ℚ) := by linarith
      have hpar : (2 : ℤ) ∣ (t - c) := by
        have h4eq : ((t - c) ^ 2 + 2 * (t - c) * c + 4 * (m : ℤ) * c ^ 2 : ℤ) = 4 * n := by
          have hq : (((t - c) ^ 2 + 2 * (t - c) * c + 4 * (m : ℤ) * c ^ 2 : ℤ) : ℚ) = (4 * n : ℚ) := by
            push_cast; rw [← h2a, ← hc, hn]; ring
          exact_mod_cast hq
        have heven : Even ((t - c) ^ 2) :=
          ⟨2 * n - (t - c) * c - 2 * (m : ℤ) * c ^ 2, by linarith⟩
        exact (Int.even_pow.mp heven).1.two_dvd
      obtain ⟨a, ha⟩ := hpar
      refine ⟨a, c, ?_, hc⟩
      have haQ : (t : ℚ) - (c : ℚ) = 2 * (a : ℚ) := by exact_mod_cast ha
      linarith
    · rintro ⟨a, c, ha, hc⟩
      have hz : z = (a : ImagQuadField p) + (c : ImagQuadField p) * gen := by
        apply QuadraticAlgebra.ext
        · simp [gen, ha]
        · simp [gen, hc]
      rw [hz]
      exact (isIntegral_intCast (n := a)).add ((isIntegral_intCast (n := c)).mul hgen_int)
  let c0 : 𝓞 (ImagQuadField p) → ℤ := fun z => ((hmem_int z.1).mp z.2).choose
  let c1 : 𝓞 (ImagQuadField p) → ℤ := fun z => ((hmem_int z.1).mp z.2).choose_spec.choose
  have hc0 : ∀ z, (c0 z : ℚ) = z.1.re := fun z =>
    ((hmem_int z.1).mp z.2).choose_spec.choose_spec.1.symm
  have hc1 : ∀ z, (c1 z : ℚ) = z.1.im := fun z =>
    ((hmem_int z.1).mp z.2).choose_spec.choose_spec.2.symm
  let bO : Module.Basis (Fin 2) ℤ (𝓞 (ImagQuadField p)) :=
    Module.Basis.ofEquivFun
      { toFun := fun z => ![c0 z, c1 z]
        invFun := fun v => ⟨⟨(v 0 : ℚ), (v 1 : ℚ)⟩, (hmem_int _).mpr ⟨v 0, v 1, rfl, rfl⟩⟩
        left_inv := fun z => Subtype.ext <| QuadraticAlgebra.ext (hc0 z) (hc1 z)
        right_inv := fun v => by
          ext i
          fin_cases i
          · have h : (c0 ⟨⟨(v 0 : ℚ), (v 1 : ℚ)⟩, (hmem_int _).mpr ⟨v 0, v 1, rfl, rfl⟩⟩ : ℚ) = (v 0 : ℚ) :=
              hc0 ⟨⟨(v 0 : ℚ), (v 1 : ℚ)⟩, (hmem_int _).mpr ⟨v 0, v 1, rfl, rfl⟩⟩
            exact_mod_cast h
          · have h : (c1 ⟨⟨(v 0 : ℚ), (v 1 : ℚ)⟩, (hmem_int _).mpr ⟨v 0, v 1, rfl, rfl⟩⟩ : ℚ) = (v 1 : ℚ) :=
              hc1 ⟨⟨(v 0 : ℚ), (v 1 : ℚ)⟩, (hmem_int _).mpr ⟨v 0, v 1, rfl, rfl⟩⟩
            exact_mod_cast h
        map_add' := fun x y => by
          ext i
          fin_cases i
          · have h : (c0 (x + y) : ℚ) = (c0 x : ℚ) + (c0 y : ℚ) := by rw [hc0, hc0, hc0]; rfl
            exact_mod_cast h
          · have h : (c1 (x + y) : ℚ) = (c1 x : ℚ) + (c1 y : ℚ) := by rw [hc1, hc1, hc1]; rfl
            exact_mod_cast h
        map_smul' := fun r x => by
          ext i
          fin_cases i
          · have h : (c0 (r • x) : ℚ) = (r : ℚ) * (c0 x : ℚ) := by
              rw [hc0, hc0]; change (r • x.1).re = (r : ℚ) * x.1.re; rw [zsmul_eq_mul]; simp
            exact_mod_cast h
          · have h : (c1 (r • x) : ℚ) = (r : ℚ) * (c1 x : ℚ) := by
              rw [hc1, hc1]; change (r • x.1).im = (r : ℚ) * x.1.im; rw [zsmul_eq_mul]; simp
            exact_mod_cast h }
  have hbO_val : ∀ i : Fin 2, (bO i : ImagQuadField p) = b i := fun i => by
    have hre : ∀ j : Fin 2, (bO j : ImagQuadField p).re = (bO.repr (bO j) 0 : ℚ) := fun j =>
      (hc0 (bO j)).symm
    have him : ∀ j : Fin 2, (bO j : ImagQuadField p).im = (bO.repr (bO j) 1 : ℚ) := fun j =>
      (hc1 (bO j)).symm
    fin_cases i
    · change (bO 0 : ImagQuadField p) = b 0
      rw [hb0]
      apply QuadraticAlgebra.ext
      · rw [hre 0, bO.repr_self]; simp; rfl
      · rw [him 0, bO.repr_self]; simp; rfl
    · change (bO 1 : ImagQuadField p) = b 1
      rw [hb1]
      apply QuadraticAlgebra.ext
      · rw [hre 1, bO.repr_self]; simp [gen]
      · rw [him 1, bO.repr_self]; simp [gen]
  refine ⟨ImagQuadField p, inferInstance, inferInstance, inferInstance, hfin, ?_⟩
  have hdisc_eq : (discr (ImagQuadField p) : ℚ) = Algebra.discr ℚ b := by
    rw [← NumberField.discr_eq_discr (ImagQuadField p) bO, Algebra.discr_def, Algebra.discr_def,
      Int.cast_det]
    congr 1
    ext i j
    simp only [Matrix.map_apply, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
    have htr_cast : ((Algebra.trace ℤ (𝓞 (ImagQuadField p)) (bO i * bO j) : ℤ) : ℚ) =
        Algebra.trace ℚ (ImagQuadField p) ((bO i : ImagQuadField p) * (bO j : ImagQuadField p)) := by
      have := Algebra.trace_localization ℤ (nonZeroDivisors ℤ) (bO i * bO j)
        (Sₘ := ImagQuadField p) (Rₘ := ℚ)
      simpa [RingOfIntegers.coe_eq_algebraMap] using this.symm
    rw [← hbO_val i, ← hbO_val j]
    exact htr_cast
  exact_mod_cast hdisc_eq.trans hdiscr_b

/-- For every `N`, there exist `N` imaginary quadratic CM fields with pairwise coprime
discriminants (`QuadFam.lean`). -/
theorem quadFam (N : ℕ) :
    ∃ (K : Fin N → Type) (_ : ∀ i, Field (K i)) (_ : ∀ i, NumberField (K i))
      (_ : ∀ i, IsCMField (K i)),
      (∀ i, Module.finrank ℚ (K i) = 2) ∧ ∀ i j, i ≠ j → IsCoprime (discr (K i)) (discr (K j)) := by
  have hS : {p : ℕ | p.Prime ∧ p % 4 = 3}.Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro n
    obtain ⟨p, hpn, hpp, hmod⟩ :=
      Nat.forall_exists_prime_gt_and_modEq n (q := 4) (a := 3) (by norm_num) (by norm_num)
    exact ⟨p, ⟨hpp, hmod⟩, hpn⟩
  let e := hS.natEmbedding
  let q : Fin N → ℕ := fun i => (e i.val).1
  have hq : ∀ i, (q i).Prime ∧ q i % 4 = 3 := fun i => (e i.val).2
  have hinj : ∀ i j, q i = q j → i = j := fun i j h => Fin.ext (e.injective (Subtype.ext h))
  choose K hF hN hC hr hd using fun i => quadFam_one (q i) (hq i).1 (hq i).2
  refine ⟨K, hF, hN, hC, hr, ?_⟩
  intro i j hij
  rw [hd i, hd j]
  have hne : q i ≠ q j := fun h => hij (hinj i j h)
  have hcop : Nat.Coprime (q i) (q j) := (Nat.coprime_primes (hq i).1 (hq j).1).2 hne
  exact (Nat.isCoprime_iff_coprime.2 hcop).neg_neg

end SignNeAndQuadFam

/-! ## Section 2: Frobenius Eigenvalues, Root-Counting `EigData`, Place Transport & Quadratic Counting -/

section FrobeniusAndEigData

/-- Shorthand for `PadicAlgCl l` (`Qbar l` in Alpöge's `GaloisLibrary`). -/
abbrev Qbar (l : ℕ) [Fact l.Prime] : Type := PadicAlgCl l

/-- Cyclotomic character valued in `(Qbar l)ˣ`. -/
def cycBar (F Ω : Type*) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] : G F Ω →* (Qbar l)ˣ :=
  (Units.map (algebraMap ℤ_[l] (Qbar l)).toMonoidHom).comp (cycZ F Ω l)

/-- Frobenius eigenvalue multiset of a continuous `l`-adic Galois representation `r` at place `w`. -/
def FrobEig {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ}
    (r : G F Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 F)) (B : Multiset ℂ) : Prop :=
  ∀ A : ValuationSubring Ω, IsPlaceOver A w →
    (∀ s ∈ Ine (F := F) A, r s = 1) ∧
    ∀ σ : G F Ω, IsFrob A (normV w) σ →
      Polynomial.map ι.toRingHom ((r σ⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly =
        (B.map fun b => X - C b).prod

/-- A character `χ : G F Ω →* (Qbar l)ˣ` kills `μ_M` if it vanishes on every element fixing all
`M`-th roots of unity in `Ω`. -/
def KillsMu {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
    (M : ℕ) (χ : G F Ω →* (Qbar l)ˣ) : Prop :=
  ∀ s : G F Ω, (∀ ζ : Ω, ζ ^ M = 1 → s ζ = ζ) → χ s = 1

/-- Away-from-`l` tame level condition `LevelAway l M r` (`CqStmt.lean`). -/
def LevelAway {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (l : ℕ) [Fact l.Prime] (M : ℕ) {n : ℕ} (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal →
    ∃ (A : ValuationSubring Ω) (_ : IsPlaceOver A w) (χ : Fin n → G F Ω →* (Qbar l)ˣ),
      (∀ i, KillsMu M (χ i)) ∧
      ∃ P : GL (Fin n) (Qbar l), ∀ s ∈ Ine (F := F) A,
        ((P * r s * P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) =
          Matrix.diagonal fun i => (χ i s : Qbar l)

/-- Above-`l` flag condition `FlagAt M m r A κ` (`CqStmt.lean`). -/
def FlagAt {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] (M : ℕ) {n : ℕ} (m : Fin n → ℤ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) (A : ValuationSubring Ω)
    (κ : Fin n → Dec (F := F) A →* (Qbar l)ˣ) : Prop :=
  ∃ χ : Fin n → G F Ω →* (Qbar l)ˣ,
    (∀ i, KillsMu M (χ i)) ∧
    IsFlagOn r (Dec (F := F) A) κ ∧
    ∀ i, ∀ s : Dec (F := F) A, (s : G F Ω) ∈ Ine (F := F) A →
      κ i s = χ i s * cycBar F Ω l s ^ (-m i)

/-- Integrality/slope condition `SlopesIn q m B` for Frobenius eigenvalues (`CqStmt.lean`). -/
def SlopesIn (q : ℕ) {n : ℕ} (m : Fin n → ℤ) (B : Multiset ℂ) : Prop :=
  (∀ a : ℤ, (∀ i, m i ≤ a) → ∀ b ∈ B, IsIntegral ℤ ((q : ℂ) ^ a * b)) ∧
  (∀ a : ℤ, (∀ i, -m i ≤ a) → ∀ b ∈ B, IsIntegral ℤ ((q : ℂ) ^ a * b⁻¹))

/-- Finite Frobenius-eigenvalue classification package `EigData n q m wt` (`CqStmt.lean`). -/
structure EigData (n q : ℕ) (m : Fin n → ℤ) (wt : ℤ) where
  S : Type
  fin : Finite S
  β : S → Multiset ℂ
  card : ∀ s, (β s).card = n
  conj : ∀ σ : ℂ ≃+* ℂ, ∃ e : S ≃ S, ∀ s, β (e s) = (β s).map σ
  pure : ∀ s, ∀ b ∈ β s, ‖b‖ = (q : ℝ) ^ (-(wt : ℝ) / 2)
  int : ∀ a : ℤ, (∀ i, m i ≤ a) → ∀ s, ∀ b ∈ β s, IsIntegral ℤ ((q : ℂ) ^ a * b)
  intInv : ∀ a : ℤ, (∀ i, -m i ≤ a) → ∀ s, ∀ b ∈ β s, IsIntegral ℤ ((q : ℂ) ^ a * b⁻¹)

/-- Classification of a predicate `P` on `l`-adic Galois representations by `D : EigData`. -/
def EigData.Classifies {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {l : ℕ} [Fact l.Prime] {n : ℕ} {m : Fin n → ℤ} {wt : ℤ}
    {w : HeightOneSpectrum (𝓞 F)} (D : EigData n (normV w) m wt)
    (ι : Qbar l ≃+* ℂ) (P : (G F Ω →* GL (Fin n) (Qbar l)) → Prop) : Prop :=
  ∃ cl : {r : G F Ω →* GL (Fin n) (Qbar l) // P r} → D.S,
    (∀ r r', cl r = cl r' → RepIso r.1 r'.1) ∧
    ∀ r, FrobEig ι r.1 w ((D.β (cl r)).map (·⁻¹))

/-! ### 2.1 Shared Dedekind-Domain, Place-Norm & Fiber Lemmas -/

theorem normV_eq_absNorm {K : Type*} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) :
    normV w = Ideal.absNorm w.asIdeal := by
  unfold normV
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem one_lt_normV {K : Type*} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) :
    1 < normV w := by
  rw [normV_eq_absNorm]
  have hne0 : Ideal.absNorm w.asIdeal ≠ 0 :=
    (Ideal.absNorm_eq_zero_iff.not.mpr w.ne_bot)
  have hne1 : Ideal.absNorm w.asIdeal ≠ 1 :=
    (Ideal.absNorm_eq_one_iff.not.mpr w.isPrime.ne_top)
  omega

/-- Norm-inertia-degree relation `normV w = normV (w.under (𝓞 K)) ^ f`
(deduplicated across 6 files in `CrystallineBaseChange`). -/
theorem normV_under {K K' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K']
    [Algebra K K'] (w : HeightOneSpectrum (𝓞 K')) :
    normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  rw [normV_eq_absNorm, normV_eq_absNorm, ← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

/-- The map `w ↦ w.under (𝓞 K)` tends to `cofinite` along `cofinite` (`NormQuad.lean`). -/
theorem tendsto_under' {K K' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K']
    [Algebra K K'] :
    Filter.Tendsto (fun w : HeightOneSpectrum (𝓞 K') => w.under (𝓞 K)) Filter.cofinite Filter.cofinite := by
  refine Filter.Tendsto.cofinite_of_finite_preimage_singleton fun v => ?_
  have h0 : Ideal.map (algebraMap (𝓞 K) (𝓞 K')) v.asIdeal ≠ 0 :=
    fun h => v.ne_bot ((Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)).1 h)
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  have e : w.under (𝓞 K) = v := hw
  show w.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap, ← e]
  exact le_rfl

/-- For any prime `p ∈ w`, `normV w = p^h` with `1 ≤ h ≤ [K : ℚ]`
(`ExistsNormVEqPrimePowLeFinrank.lean`). -/
theorem exists_normV_eq_prime_pow_le_finrank (K : Type*) [Field K] [NumberField K]
    (p : ℕ) (w : HeightOneSpectrum (𝓞 K)) (hp : p.Prime) (hpw : (p : 𝓞 K) ∈ w.asIdeal) :
    ∃ h : ℕ, 1 ≤ h ∧ h ≤ Module.finrank ℚ K ∧ normV w = p ^ h := by
  have hspan : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ Module.finrank ℚ K := by
    rw [Ideal.absNorm_span_singleton]
    have e : (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) := by simp
    rw [e, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
    simp [Int.natAbs_pow]
  have hdvd : Ideal.absNorm w.asIdeal ∣ p ^ Module.finrank ℚ K := by
    rw [← hspan]
    exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hpw)
  obtain ⟨h, hle, heq⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  refine ⟨h, ?_, hle, (normV_eq_absNorm w).trans heq⟩
  rcases Nat.eq_zero_or_pos h with h0 | h0
  · exfalso
    rw [h0, pow_zero, Ideal.absNorm_eq_one_iff] at heq
    exact w.isPrime.ne_top heq
  · exact h0

theorem normV_rat {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 ℚ))
    (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) : normV w = p := by
  obtain ⟨h, h1, h2, h3⟩ := exists_normV_eq_prime_pow_le_finrank ℚ p w hp hw
  rw [Module.finrank_self] at h2
  rw [h3, le_antisymm h2 h1, pow_one]

theorem exists_over (K : Type*) [Field K] [NumberField K] (h2 : Module.finrank ℚ K = 2)
    {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    ∃ (v : HeightOneSpectrum (𝓞 K)) (f : ℕ),
      v.under (𝓞 ℚ) = w ∧ (p : 𝓞 K) ∈ v.asIdeal ∧ 1 ≤ f ∧ f ≤ 2 ∧ normV v = p ^ f := by
  have := w.isMaximal
  obtain ⟨Q, hQ, hL⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 K) w.asIdeal
  have hpQ : (p : 𝓞 K) ∈ Q := by
    have : (p : 𝓞 ℚ) ∈ Q.under (𝓞 ℚ) := hL.over ▸ hw
    simpa [Ideal.under, Ideal.mem_comap] using this
  have h0 : Q ≠ ⊥ := by
    rintro rfl
    exact hp.ne_zero (by simpa using hpQ)
  obtain ⟨f, f1, f2, f3⟩ := exists_normV_eq_prime_pow_le_finrank K p ⟨Q, hQ.isPrime, h0⟩ hp hpQ
  exact ⟨⟨Q, hQ.isPrime, h0⟩, f, HeightOneSpectrum.ext hL.over.symm, hpQ, f1, h2 ▸ f2, f3⟩

theorem not_mem_of_coprime {F : Type*} [Field F] [NumberField F] {p a : ℕ} (h : p.Coprime a)
    (w : HeightOneSpectrum (𝓞 F)) (hw : (p : 𝓞 F) ∈ w.asIdeal) : (a : 𝓞 F) ∉ w.asIdeal := fun ha => by
  obtain ⟨x, y, e⟩ : IsCoprime (p : 𝓞 F) (a : 𝓞 F) := Nat.Coprime.cast h
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (e ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hw) (w.asIdeal.mul_mem_left _ ha)))

theorem exists_prime_notMem {F : Type*} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ l : ℕ, l.Prime ∧ ((l : ℕ) : 𝓞 F) ∉ v.asIdeal := by
  by_cases h2 : ((2 : ℕ) : 𝓞 F) ∈ v.asIdeal
  · refine ⟨3, Nat.prime_three, fun h3 => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)⟩
    have := v.asIdeal.sub_mem h3 h2
    convert this using 1
    push_cast
    ring
  · exact ⟨2, Nat.prime_two, h2⟩

theorem nat_mem_under {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L]
    [Algebra F L] (l : ℕ) (w : HeightOneSpectrum (𝓞 L)) :
    ((l : ℕ) : 𝓞 F) ∈ (w.under (𝓞 F)).asIdeal ↔ ((l : ℕ) : 𝓞 L) ∈ w.asIdeal := by
  change algebraMap (𝓞 F) (𝓞 L) _ ∈ w.asIdeal ↔ _
  rw [map_natCast]

theorem exists_avoid {N : ℕ} (d : Fin (N + 1) → ℤ)
    (hd : ∀ i j, i ≠ j → IsCoprime (d i) (d j)) {p : ℕ} (hp : p.Prime) :
    ∃ u : Fin N → Fin (N + 1), Function.Injective u ∧ ∀ i, ¬ (p : ℤ) ∣ d (u i) := by
  by_cases h : ∃ j, (p : ℤ) ∣ d j
  · obtain ⟨j, hj⟩ := h
    refine ⟨j.succAbove, Fin.succAbove_right_injective, fun i hi => ?_⟩
    have := (hd _ _ (Fin.succAbove_ne j i)).isUnit_of_dvd' hi hj
    exact (Nat.prime_iff_prime_int.1 hp).not_isUnit this
  · exact ⟨Fin.succ, Fin.succ_injective _, fun i hi => h ⟨_, hi⟩⟩

/-- Fiber-splitting bit lemma for 2-to-1 equivalence-relation fibers (`CountQuadraticOfHyp.lean`). -/
theorem bit_of_fibre {X U : Type*} (R : X → X → Prop) (hs : ∀ x y, R x y → R y x)
    (ht : ∀ x y z, R x y → R y z → R x z) (Q : X → U → Prop) (hQ : ∀ x, ∃ u, Q x u)
    (h2 : ∀ u x₀ x x', Q x₀ u → Q x u → Q x' u → ¬ R x₀ x → ¬ R x₀ x' → R x x') :
    ∃ g : X → U × Bool, (∀ x x', g x = g x' → R x x') ∧ ∀ x, Q x (g x).1 := by
  classical
  choose u hu using hQ
  have hex : ∀ x : X, ∃ y, Q y (u x) := fun x => ⟨x, hu x⟩
  refine ⟨fun x => (u x, decide (R (Classical.epsilon (α := X) (h := ⟨x⟩) fun y => Q y (u x)) x)),
    fun x x' h => ?_, hu⟩
  obtain ⟨h1, h3⟩ := Prod.ext_iff.1 h
  simp only at h1 h3
  have h0 := Classical.epsilon_spec (hex x)
  rw [← h1, decide_eq_decide] at h3
  have hx' : Q x' (u x) := h1 ▸ hu x'
  by_cases hc : R (Classical.epsilon (α := X) (h := ⟨x⟩) fun y => Q y (u x)) x
  · exact ht _ _ _ (hs _ _ hc) (h3.1 hc)
  · exact h2 _ _ _ _ h0 (hu x) hx' hc fun h4 => hc (h3.2 h4)

/-! ### 2.2 Frobenius Conjugation, Existence & Power Compatibility (`FrobEx`, `FrobeniusPowerCompatibility`) -/

private theorem val_smul_lt {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    (g : G F Ω) (A : ValuationSubring Ω) (y : Ω) :
    (g • A).valuation (g y) < 1 ↔ A.valuation y < 1 := by
  have e : ∀ z : Ω, g z ∈ g • A ↔ z ∈ A := fun z => by
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, show g z = g • z from rfl, inv_smul_smul]
  have hlt : ∀ (B : ValuationSubring Ω) (z : Ω), B.valuation z < 1 ↔ z ∈ B ∧ (z = 0 ∨ z⁻¹ ∉ B) :=
    fun B z => by
      constructor
      · intro h
        refine ⟨(B.valuation_le_one_iff z).mp h.le, ?_⟩
        by_cases hz : z = 0
        · exact Or.inl hz
        · right; intro hinv
          have h1 : B.valuation z⁻¹ ≤ 1 := (B.valuation_le_one_iff _).mpr hinv
          have hmul : B.valuation z * B.valuation z⁻¹ < 1 := by
            calc B.valuation z * B.valuation z⁻¹ ≤ B.valuation z * 1 := by gcongr
              _ = B.valuation z := mul_one _
              _ < 1 := h
          rw [← map_mul, mul_inv_cancel₀ hz, map_one] at hmul
          exact lt_irrefl 1 hmul
      · rintro ⟨hzB, h0 | hinv⟩
        · subst h0; simp
        · refine lt_of_le_of_ne ((B.valuation_le_one_iff z).mpr hzB) ?_
          intro heq
          apply hinv
          rw [← B.valuation_le_one_iff, map_inv₀, heq, inv_one]
  rw [hlt, hlt, e, ← map_inv₀, e, map_eq_zero]

private theorem val_smul_le {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    (g : G F Ω) (A : ValuationSubring Ω) (y : Ω) :
    (g • A).valuation (g y) ≤ 1 ↔ A.valuation y ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, show g y = g • y from rfl, inv_smul_smul]

private theorem conj_dec {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    {g τ : G F Ω} {A : ValuationSubring Ω} (h : τ ∈ (g • A).decompositionSubgroup F) :
    g⁻¹ * τ * g ∈ A.decompositionSubgroup F := by
  have h1 : τ • g • A = g • A := h
  show (g⁻¹ * τ * g) • A = A
  rw [mul_smul, mul_smul, h1, inv_smul_smul]

private theorem conj_apply {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    (g τ : G F Ω) (x : Ω) : g ((g⁻¹ * τ * g) x) = τ (g x) := by
  change g • ((g⁻¹ * τ * g) • x) = τ • (g • x)
  rw [mul_smul, mul_smul, smul_inv_smul]

private theorem conj_frob {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    {g τ : G F Ω} {A : ValuationSubring Ω} {q : ℕ} (h : IsFrob (g • A) q τ) :
    IsFrob A q (g⁻¹ * τ * g) := by
  refine ⟨conj_dec h.1, fun x hx => ?_⟩
  have h1 := h.2 (g x) ((val_smul_le g A x).2 hx)
  rwa [← conj_apply, ← map_pow, ← map_sub, val_smul_lt] at h1

private theorem conj_ine {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {g τ : G F Ω} {A : ValuationSubring Ω} (h : τ ∈ Ine (F := F) (g • A)) :
    g⁻¹ * τ * g ∈ Ine (F := F) A := by
  refine ⟨conj_dec h.1, fun x hx => ?_⟩
  have h1 := h.2 (g x) ((val_smul_le g A x).2 hx)
  rwa [← conj_apply, ← map_sub, val_smul_lt] at h1

/-- Inertia at a prime not dividing `M` fixes all `M`-th roots of unity in `Ω` (`FrobEx.lean`). -/
theorem ine_fix {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A w) {M : ℕ}
    (hM : ((M : ℕ) : 𝓞 F) ∉ w.asIdeal) {s : G F Ω} (hs : s ∈ Ine (F := F) A)
    (ζ : Ω) (hζ : ζ ^ M = 1) : s ζ = ζ := by
  set v := A.valuation with hvdef
  have hM0 : M ≠ 0 := by rintro rfl; exact hM (by simp)
  have hvM : ¬ v (M : Ω) < 1 := by
    intro hlt
    apply hM
    rw [← hA]
    simpa using hlt
  have hζ1 : v ζ = 1 := by
    rcases lt_trichotomy (v ζ) 1 with h | h | h
    · have h2 := pow_lt_one₀ bot_le h hM0
      rw [← map_pow, hζ, map_one] at h2
      exact absurd h2 (lt_irrefl 1)
    · exact h
    · have h2 := one_lt_pow₀ h hM0
      rw [← map_pow, hζ, map_one] at h2
      exact absurd h2 (lt_irrefl 1)
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ1
  have hsd : v (s ζ - ζ) < 1 := hs.2 ζ hζ1.le
  have hηM : (s ζ) ^ M = 1 := by rw [← map_pow, hζ, map_one]
  set η := s ζ with hη
  set u := η * ζ⁻¹ with hu
  have huM : u ^ M = 1 := by rw [hu, mul_pow, inv_pow, hηM, hζ, inv_one, mul_one]
  have hu1 : v (u - 1) < 1 := by
    have e : u - 1 = (η - ζ) * ζ⁻¹ := by rw [hu, sub_mul, mul_inv_cancel₀ hζ0]
    rw [e, map_mul, map_inv₀, hζ1, inv_one, mul_one]
    exact hsd
  have hule : v u ≤ 1 := by
    have e : u = (u - 1) + 1 := by ring
    rw [e]
    exact (v.map_add _ _).trans (max_le hu1.le (by rw [map_one]))
  by_contra hne
  have hu_ne : u ≠ 1 := by
    intro h1
    apply hne
    have e : η = u * ζ := by rw [hu, mul_assoc, inv_mul_cancel₀ hζ0, mul_one]
    rw [e, h1, one_mul]
  have hsum : ∑ i ∈ Finset.range M, u ^ i = 0 := by
    have h := geom_sum_mul u M
    rw [huM, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hu_ne)
  have hlt : v (∑ i ∈ Finset.range M, (u ^ i - 1)) < 1 := by
    apply Valuation.map_sum_lt v one_ne_zero
    intro i _
    rw [← geom_sum_mul u i, map_mul]
    have hs1 : v (∑ j ∈ Finset.range i, u ^ j) ≤ 1 :=
      Valuation.map_sum_le v (fun j _ => by rw [map_pow]; exact pow_le_one' hule j)
    calc v (∑ j ∈ Finset.range i, u ^ j) * v (u - 1) ≤ 1 * v (u - 1) := by gcongr
      _ = v (u - 1) := one_mul _
      _ < 1 := hu1
  rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_range, zero_sub, Valuation.map_neg] at hlt
  apply hvM
  simpa using hlt

/-- Uniqueness of Frobenius eigenvalues and existence from `LevelAway l M r` away from `lM`
(`FrobEx.lean`). -/
theorem frobEx (F Ω : Type*) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 F)) :
    (∀ B B', FrobEig ι r w B → FrobEig ι r w B' → B = B') ∧
    ∀ M : ℕ, LevelAway l M r → ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ((M : ℕ) : 𝓞 F) ∉ w.asIdeal →
      ∃ B, FrobEig ι r w B := by
  refine ⟨?_, ?_⟩
  · intro B B' hB hB'
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨σ, hσ⟩ := exists_isFrob hA
    have h1 := (hB A hA).2 σ hσ
    have h2 := (hB' A hA).2 σ hσ
    have h3 := congrArg Polynomial.roots (h1.symm.trans h2)
    simpa [Polynomial.roots_multiset_prod_X_sub_C] using h3
  · intro M hlev hl hM
    obtain ⟨A0, hA0, χ, hχ, P, hP⟩ := hlev w hl
    have hI0 : ∀ t ∈ Ine (F := F) A0, r t = 1 := by
      intro t ht
      have hd := hP t ht
      have hc : ∀ i, χ i t = 1 := fun i => hχ i t (fun ζ hζ => ine_fix hA0 hM ht ζ hζ)
      simp only [hc, Units.val_one, Matrix.diagonal_one] at hd
      have hq : P * r t * P⁻¹ = 1 := Units.ext hd
      calc r t = P⁻¹ * (P * r t * P⁻¹) * P := by group
        _ = 1 := by rw [hq]; group
    obtain ⟨σ0, hσ0⟩ := exists_isFrob hA0
    refine ⟨(Polynomial.map ι.toRingHom
      ((r σ0⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly).roots, ?_⟩
    intro A hA
    obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver hA0 hA
    subst hg
    refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
    · have ht := hI0 _ (conj_ine hs)
      calc r s = r g * r (g⁻¹ * s * g) * r g⁻¹ := by
            simp only [map_mul, map_inv]; group
        _ = 1 := by rw [ht]; simp
    · have hc := inv_mul_mem_Ine_of_isFrob hσ0 (conj_frob hσ)
      have he : r (g⁻¹ * σ * g) = r σ0 := by
        have h4 := hI0 _ hc
        rw [map_mul, map_inv] at h4
        exact (inv_mul_eq_one.1 h4).symm
      have hu : r σ⁻¹ = r g * r σ0⁻¹ * (r g)⁻¹ := by
        rw [map_inv r σ0, ← he]
        simp only [map_mul, map_inv]; group
      rw [hu, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
      exact Polynomial.Splits.eq_prod_roots_of_monic (IsAlgClosed.splits _)
        ((Matrix.charpoly_monic _).map _)

private theorem pow_cong {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) {a b : Ω}
    (ha : A.valuation a ≤ 1) (hb : A.valuation b ≤ 1) (h : A.valuation (a - b) < 1) (m : ℕ) :
    A.valuation (a ^ m - b ^ m) < 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : a ^ (m + 1) - b ^ (m + 1) = a * (a ^ m - b ^ m) + (a - b) * b ^ m := by ring
    rw [e]
    refine Valuation.map_add_lt A.valuation ?_ ?_
    · rw [map_mul]
      calc A.valuation a * A.valuation (a ^ m - b ^ m) ≤ 1 * A.valuation (a ^ m - b ^ m) := by gcongr
        _ = A.valuation (a ^ m - b ^ m) := one_mul _
        _ < 1 := ih
    · rw [map_mul, map_pow]
      calc A.valuation (a - b) * A.valuation b ^ m ≤ A.valuation (a - b) * 1 := by
            gcongr; exact pow_le_one' hb m
        _ = A.valuation (a - b) := mul_one _
        _ < 1 := h

private theorem dec_le {K Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    {A : ValuationSubring Ω} {g : G K Ω} (hg : g ∈ Dec (F := K) A) {x : Ω}
    (hx : A.valuation x ≤ 1) : A.valuation (g x) ≤ 1 :=
  (A.valuation_le_one_iff _).2 ((apply_mem_iff_of_mem_Dec hg x).2 ((A.valuation_le_one_iff _).1 hx))

private theorem isFrob_pow {K Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    {A : ValuationSubring Ω} {q : ℕ} {g : G K Ω} (hg : IsFrob (F := K) A q g) (n : ℕ) :
    IsFrob (F := K) A (q ^ n) (g ^ n) := by
  induction n with
  | zero => exact ⟨by rw [pow_zero]; exact one_mem _, fun x _ => by simp⟩
  | succ n ih =>
    refine ⟨Subgroup.pow_mem _ hg.1 _, fun x hx => ?_⟩
    have h1 := hg.2 _ (dec_le ih.1 hx)
    have h2 := pow_cong A (dec_le ih.1 hx) (b := x ^ q ^ n)
      (by rw [map_pow]; exact pow_le_one' hx _) (ih.2 x hx) q
    have h3 := Valuation.map_add_lt A.valuation h1 h2
    rw [sub_add_sub_cancel, ← pow_mul, ← pow_succ] at h3
    rw [pow_succ' g, AlgEquiv.mul_apply]
    exact h3

/-- Over `ℂ`, the roots of `(M ^ f).charpoly` are the `f`-th powers of the roots of `M.charpoly`. -/
theorem charpoly_pow_eq_map_pow {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (f : ℕ) :
    (M ^ f).charpoly = (M.charpoly.roots.map fun b => X - C (b ^ f)).prod := by
  induction n with
  | zero =>
    simp [Matrix.charpoly, Matrix.det_isEmpty]
  | succ n ih =>
    let T : Module.End ℂ (Fin (n + 1) → ℂ) := Matrix.toLin' M
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue T
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    let e0 : Fin (n + 1) ≃ Unit ⊕ Fin n :=
      { toFun := fun i => Fin.cases (Sum.inl ()) Sum.inr i
        invFun := fun x => Sum.elim (fun _ => 0) Fin.succ x
        left_inv := fun i => by refine Fin.cases rfl (fun _ => rfl) i
        right_inv := fun x => by cases x <;> rfl }
    obtain ⟨b0, hb0⟩ : ∃ b : Module.Basis (Fin (n + 1)) ℂ (Fin (n + 1) → ℂ), b 0 = v := by
      have hli : LinearIndepOn ℂ id ({v} : Set (Fin (n + 1) → ℂ)) := by
        rw [linearIndepOn_iff]
        intro l hl hsum
        ext x
        by_cases hx : x = v
        · subst hx
          rw [Finsupp.linearCombination_apply] at hsum
          have h1 : l x • x = 0 := by
            rw [Finsupp.sum_eq_single x] at hsum
            · exact hsum
            · intro y hy hyx
              have hy_mem : y ∈ ({x} : Set _) := hl (Finsupp.mem_support_iff.mpr hy)
              exact absurd hy_mem (by simpa using hyx)
            · intro _; exact zero_smul ℂ x
          exact (smul_eq_zero.mp h1).resolve_right hv.2
        · have hx' : x ∉ ({v} : Set _) := by simpa using hx
          exact Finsupp.notMem_support_iff.mp fun h => hx' (hl h)
      let s := hli.extend (Set.subset_univ ({v} : Set (Fin (n + 1) → ℂ)))
      let b' : Module.Basis s ℂ (Fin (n + 1) → ℂ) := Module.Basis.extend hli
      have hv_mem : v ∈ s := hli.subset_extend (Set.subset_univ _) (Set.mem_singleton v)
      have hfin : Finite s := Module.Finite.finite_basis b'
      let _ : Fintype s := Fintype.ofFinite s
      have hcard : Fintype.card s = n + 1 := by
        have := Module.finrank_eq_card_basis b'
        rw [Module.finrank_fin_fun] at this
        exact this.symm
      let idx0 : s := ⟨v, hv_mem⟩
      let eq1 : Fin (n + 1) ≃ s := (Fintype.equivFinOfCardEq hcard).symm
      let p : Equiv.Perm s := Equiv.swap (eq1 0) idx0
      let b : Module.Basis (Fin (n + 1)) ℂ (Fin (n + 1) → ℂ) := b'.reindex (eq1.trans p).symm
      refine ⟨b, ?_⟩
      simp only [b, Module.Basis.reindex_apply, Equiv.symm_symm, Equiv.trans_apply, p,
        Equiv.swap_apply_left]
      exact Module.Basis.extend_apply_self hli ⟨v, hv_mem⟩
    let A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := LinearMap.toMatrix b0 b0 T
    have hA_col : ∀ i : Fin n, A i.succ 0 = 0 := fun i => by
      have hTv : T (b0 0) = μ • b0 0 := by rw [hb0]; exact hv.apply_eq_smul
      rw [show A i.succ 0 = b0.repr (T (b0 0)) i.succ from LinearMap.toMatrix_apply b0 b0 T i.succ 0,
        hTv, map_smul, Finsupp.smul_apply, Module.Basis.repr_self,
        Finsupp.single_eq_of_ne (Fin.succ_ne_zero i), smul_zero]
    have hA_00 : A 0 0 = μ := by
      have hTv : T (b0 0) = μ • b0 0 := by rw [hb0]; exact hv.apply_eq_smul
      rw [show A 0 0 = b0.repr (T (b0 0)) 0 from LinearMap.toMatrix_apply b0 b0 T 0 0,
        hTv, map_smul, Finsupp.smul_apply, Module.Basis.repr_self,
        Finsupp.single_eq_same, smul_eq_mul, mul_one]
    let B : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => A i.succ j.succ
    let R : Matrix Unit (Fin n) ℂ := Matrix.of fun _ j => A 0 j.succ
    have hblock : ∀ k : ℕ, ∃ Rk : Matrix Unit (Fin n) ℂ,
        Matrix.reindexAlgEquiv ℂ ℂ e0 (A ^ k) =
          Matrix.fromBlocks (Matrix.of fun _ _ => μ ^ k) Rk 0 (B ^ k) := by
      intro k
      induction k with
      | zero =>
        refine ⟨0, ?_⟩
        ext x y
        cases x <;> cases y <;> simp [e0, Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]
      | succ k ihk =>
        obtain ⟨Rk, hRk⟩ := ihk
        have hA_blk : Matrix.reindexAlgEquiv ℂ ℂ e0 A =
            Matrix.fromBlocks (Matrix.of fun _ _ => μ) R 0 B := by
          ext x y
          cases x with
          | inl u => cases y with
            | inl v' => simp [e0, hA_00]
            | inr j => simp [e0, R]
          | inr i => cases y with
            | inl v' => simp [e0, hA_col i]
            | inr j => simp [e0, B]
        refine ⟨(Matrix.of fun _ _ => μ ^ k) * R + Rk * B, ?_⟩
        rw [pow_succ, map_mul, hRk, hA_blk, Matrix.fromBlocks_multiply]
        simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
        congr 1
        · ext _ _
          simp [Matrix.mul_apply, pow_succ]
    have hA_cp : A.charpoly = (X - C μ) * B.charpoly := by
      obtain ⟨R1, hR1⟩ := hblock 1
      rw [pow_one] at hR1
      rw [← Matrix.charpoly_reindex e0 A]
      change (Matrix.reindexAlgEquiv ℂ ℂ e0 A).charpoly = _
      rw [hR1, Matrix.charpoly_fromBlocks_zero₂₁, pow_one, pow_one]
      congr 1
      simp [Matrix.charpoly, Matrix.charmatrix, Matrix.det_unique]
    have hAf_cp : (A ^ f).charpoly = (X - C (μ ^ f)) * (B ^ f).charpoly := by
      obtain ⟨Rf, hRf⟩ := hblock f
      rw [← Matrix.charpoly_reindex e0 (A ^ f)]
      change (Matrix.reindexAlgEquiv ℂ ℂ e0 (A ^ f)).charpoly = _
      rw [hRf, Matrix.charpoly_fromBlocks_zero₂₁]
      congr 1
      simp [Matrix.charpoly, Matrix.charmatrix, Matrix.det_unique]
    have hAM : A.charpoly = M.charpoly := by
      rw [show A = LinearMap.toMatrix b0 b0 T from rfl,
        LinearMap.charpoly_toMatrix T b0, Matrix.charpoly_toLin']
    have hAfM : (A ^ f).charpoly = (M ^ f).charpoly := by
      have hpow : A ^ f = LinearMap.toMatrix b0 b0 (T ^ f) := by
        change (LinearMap.toMatrixAlgEquiv b0 T) ^ f = LinearMap.toMatrixAlgEquiv b0 (T ^ f)
        rw [map_pow]
      rw [hpow, LinearMap.charpoly_toMatrix (T ^ f) b0]
      have hTf : T ^ f = Matrix.toLin' (M ^ f) := by
        change (Matrix.toLinAlgEquiv' M) ^ f = Matrix.toLinAlgEquiv' (M ^ f)
        rw [map_pow]
      rw [hTf, Matrix.charpoly_toLin']
    rw [← hAfM, ← hAM, hAf_cp, hA_cp, ih B]
    have hne : (X - C μ) * B.charpoly ≠ 0 :=
      mul_ne_zero (Polynomial.X_sub_C_ne_zero μ) (Matrix.charpoly_monic B).ne_zero
    rw [Polynomial.roots_mul hne, Polynomial.roots_X_sub_C, Multiset.map_add, Multiset.prod_add,
      Multiset.map_singleton, Multiset.prod_singleton]

/-- Frobenius power compatibility along a field extension `F ↪ E`
(`FrobeniusPowerCompatibility.lean`). -/
theorem frobenius_power_compatibility (F E Ω : Type*) [Field F] [NumberField F]
    [Field E] [NumberField E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω]
    [IsScalarTower F E Ω] [IsAlgClosure F Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (w : HeightOneSpectrum (𝓞 E)) (f : ℕ) (hf : normV w = normV (w.under (𝓞 F)) ^ f) :
    ∀ (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (B : Multiset ℂ),
      FrobEig ι r (w.under (𝓞 F)) B →
      FrobEig ι (r.comp (res F Ω E)) w (B.map (· ^ f)) := by
  intro n r B hB A hA
  have hA' : IsPlaceOver A (w.under (𝓞 F)) := fun x => by
    rw [IsScalarTower.algebraMap_apply F E Ω]
    exact hA (algebraMap (𝓞 F) (𝓞 E) x)
  have hI : ∀ s ∈ Ine (F := E) A, res F Ω E s ∈ Ine (F := F) A := fun s hs => hs
  obtain ⟨hru, hrf⟩ := hB A hA'
  refine ⟨fun s hs => hru _ (hI s hs), fun φ hφ => ?_⟩
  obtain ⟨σ, hσ⟩ := exists_isFrob hA'
  have hσf : IsFrob (F := F) A (normV w) (σ ^ f) := hf ▸ isFrob_pow hσ f
  have hφF : IsFrob (F := F) A (normV w) (res F Ω E φ) := hφ
  have hdiff : (σ ^ f)⁻¹ * res F Ω E φ ∈ Ine (F := F) A := inv_mul_mem_Ine_of_isFrob hσf hφF
  have heq : r (res F Ω E φ) = r (σ ^ f) := by
    have h1 := hru _ hdiff
    rw [map_mul, map_inv] at h1
    exact (inv_mul_eq_one.1 h1).symm
  have hinv : r (res F Ω E φ⁻¹) = (r σ⁻¹) ^ f := by
    rw [map_inv, map_inv, heq, map_pow, ← inv_pow, ← map_inv]
  rw [MonoidHom.comp_apply, hinv, Units.val_pow_eq_pow_val, ← Matrix.charpoly_map, Matrix.map_pow]
  have hbase := hrf σ hσ
  rw [← Matrix.charpoly_map] at hbase
  rw [charpoly_pow_eq_map_pow, hbase, Polynomial.roots_multiset_prod_X_sub_C, Multiset.map_map]
  rfl

/-- Quadratic sign character `δ : G F Ω →* kˣ` cutting out a quadratic extension `E / F`
(`ExistsQuadraticSignCharacter.lean`, proved purely from Galois theory with 0 external inputs!). -/
theorem exists_quadratic_sign_character (F E Ω : Type*) [Field F] [CharZero F] [Field E] [Field Ω]
    [Algebra F E] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsGalois F Ω]
    (k : Type*) [Field k] [CharZero k] (h2 : Module.finrank F E = 2) :
    ∃ δ : G F Ω →* kˣ, (∀ s, δ s = 1 ↔ s ∈ (res F Ω E).range) ∧ ∀ s, δ s = 1 ∨ δ s = -1 := by
  classical
  have : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  have hgal : IsGalois F E := inferInstance
  have hnorm : Normal F E := hgal.to_normal
  let p : G F Ω →* (E ≃ₐ[F] E) := AlgEquiv.restrictNormalHom E
  let H : Subgroup (G F Ω) := (res F Ω E).range
  have hker : ∀ g : G F Ω, p g = 1 ↔ g ∈ H := fun g => by
    change p g = 1 ↔ g ∈ (res F Ω E).range
    rw [range_res_eq, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h y hy
      obtain ⟨x, rfl⟩ := AlgHom.mem_fieldRange.mp hy
      have hcomm := AlgEquiv.restrictNormal_commutes g E x
      rw [show g.restrictNormal E = p g from rfl, h, AlgEquiv.one_apply] at hcomm
      exact hcomm.symm
    · intro h
      ext x
      apply (algebraMap E Ω).injective
      have hcomm := AlgEquiv.restrictNormal_commutes g E x
      rw [show g.restrictNormal E = p g from rfl] at hcomm
      rw [hcomm, AlgEquiv.one_apply]
      exact h _ (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩)
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, h2]
  have hindex : ∀ s t : G F Ω, s ∉ H → t ∉ H → s * t ∈ H := by
    intro s t hs ht
    have hps : p s ≠ 1 := fun h => hs ((hker s).mp h)
    have hpt : p t ≠ 1 := fun h => ht ((hker t).mp h)
    have hst : p (s * t) = 1 := by
      rw [map_mul]
      have hfin : Finite (E ≃ₐ[F] E) := inferInstance
      let _ : Fintype (E ≃ₐ[F] E) := Fintype.ofFinite _
      have hfc : Fintype.card (E ≃ₐ[F] E) = 2 := by rw [← Nat.card_eq_fintype_card, hcard]
      have huniq : p s = p t := by
        by_contra hab
        have h3 : ({1, p s, p t} : Finset (E ≃ₐ[F] E)).card ≤ 2 := by
          rw [← hfc]; exact Finset.card_le_univ _
        rw [Finset.card_insert_of_notMem (by simp [hps.symm, hpt.symm]),
          Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton] at h3
        omega
      rw [huniq]
      have hord := pow_card_eq_one (x := p t)
      rwa [hfc, sq] at hord
    exact (hker (s * t)).mp hst
  refine ⟨{ toFun := fun s => if s ∈ H then 1 else -1
            map_one' := by rw [if_pos (one_mem H)]
            map_mul' := fun s t => by
              by_cases hs : s ∈ H <;> by_cases ht : t ∈ H
              · simp [hs, ht, H.mul_mem hs ht]
              · have hst : s * t ∉ H := fun h => ht (by simpa using H.mul_mem (H.inv_mem hs) h)
                simp [hs, ht, hst]
              · have hst : s * t ∉ H := fun h => hs (by simpa using H.mul_mem h (H.inv_mem ht))
                simp [hs, ht, hst]
              · simp [hs, ht, hindex s t hs ht] }, fun s => ?_, fun s => ?_⟩
  · change (if s ∈ H then (1 : kˣ) else -1) = 1 ↔ s ∈ H
    split_ifs with hs
    · exact ⟨fun _ => hs, fun _ => rfl⟩
    · refine ⟨fun h => ?_, fun h => absurd h hs⟩
      exfalso
      have h1 : (-1 : k) = 1 := congrArg Units.val h
      have : (2 : k) = 0 := by linear_combination -h1
      exact two_ne_zero this
  · change (if s ∈ H then (1 : kˣ) else -1) = 1 ∨ (if s ∈ H then (1 : kˣ) else -1) = -1
    split_ifs <;> simp

/-! ### 2.3 Root-Taking on `EigData` (`RootSum.lean`) -/

private theorem roots_finset (f : ℕ) (h1 : 1 ≤ f) (h2 : f ≤ 2) (B : Multiset ℂ) :
    ∃ T : Finset (Multiset ℂ), T.card ≤ 2 ^ B.card ∧ ∀ C : Multiset ℂ, C.map (· ^ f) = B → C ∈ T := by
  classical
  induction B using Multiset.induction_on with
  | empty =>
    refine ⟨{0}, by simp, fun C hC => ?_⟩
    simpa using hC
  | cons b B ih =>
    obtain ⟨T, hT, hm⟩ := ih
    refine ⟨((Polynomial.nthRoots f b).toFinset ×ˢ T).image fun x => x.1 ::ₘ x.2, ?_, fun C hC => ?_⟩
    · refine Finset.card_image_le.trans ?_
      rw [Finset.card_product, Multiset.card_cons, pow_succ']
      exact Nat.mul_le_mul (((Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots f b)).trans h2) hT
    · obtain ⟨a, ha, hab, hr⟩ := (Multiset.map_eq_cons _ _ _ _).2 hC
      refine Finset.mem_image.2 ⟨(a, C.erase a), Finset.mem_product.2 ⟨?_, hm _ hr⟩, Multiset.cons_erase ha⟩
      exact Multiset.mem_toFinset.2 ((Polynomial.mem_nthRoots h1).2 hab)

private theorem roots_card (f : ℕ) (h1 : 1 ≤ f) (h2 : f ≤ 2) (B : Multiset ℂ) :
    Finite {C : Multiset ℂ // C.map (· ^ f) = B} ∧
      Nat.card {C : Multiset ℂ // C.map (· ^ f) = B} ≤ 2 ^ B.card := by
  obtain ⟨T, hT, hm⟩ := roots_finset f h1 h2 B
  let g : {C : Multiset ℂ // C.map (· ^ f) = B} → T := fun C => ⟨C.1, hm _ C.2⟩
  have hg : Function.Injective g := fun x y h => Subtype.ext (congrArg Subtype.val h :)
  refine ⟨Finite.of_injective g hg, (Nat.card_le_card_of_injective g hg).trans ?_⟩
  simpa using hT

private theorem pairs_card {n q : ℕ} {m : Fin n → ℤ} {wt : ℤ} (D : EigData n q m wt)
    (f : ℕ) (h1 : 1 ≤ f) (h2 : f ≤ 2) :
    Finite {x : D.S × Multiset ℂ // x.2.map (· ^ f) = D.β x.1} ∧
      Nat.card {x : D.S × Multiset ℂ // x.2.map (· ^ f) = D.β x.1} ≤ 2 ^ n * Nat.card D.S := by
  have := D.fin
  have := Fintype.ofFinite D.S
  have : ∀ s, Finite {C : Multiset ℂ // C.map (· ^ f) = D.β s} := fun s => (roots_card f h1 h2 _).1
  let e := Equiv.subtypeProdEquivSigmaSubtype fun (s : D.S) (C : Multiset ℂ) => C.map (· ^ f) = D.β s
  refine ⟨Finite.of_equiv _ e.symm, ?_⟩
  rw [Nat.card_congr e, Nat.card_sigma]
  refine (Finset.sum_le_card_nsmul _ _ (2 ^ n) fun s _ => ?_).trans ?_
  · have := (roots_card f h1 h2 (D.β s)).2
    rwa [D.card] at this
  · simp [mul_comm]

private theorem pairs_conj {n q : ℕ} {m : Fin n → ℤ} {wt : ℤ} (D : EigData n q m wt)
    (f : ℕ) (h1 : 1 ≤ f) (h2 : f ≤ 2) (σ : ℂ ≃+* ℂ) :
    ∃ e : {x : D.S × Multiset ℂ // x.2.map (· ^ f) = D.β x.1} ≃
          {x : D.S × Multiset ℂ // x.2.map (· ^ f) = D.β x.1},
      ∀ x, (e x).1.2 = x.1.2.map σ := by
  have := (pairs_card D f h1 h2).1
  obtain ⟨e, he⟩ := D.conj σ
  let g : {x : D.S × Multiset ℂ // x.2.map (· ^ f) = D.β x.1} →
      {x : D.S × Multiset ℂ // x.2.map (· ^ f) = D.β x.1} :=
    fun x => ⟨(e x.1.1, x.1.2.map σ), by
      show (x.1.2.map σ).map (· ^ f) = D.β (e x.1.1)
      rw [he, ← x.2, Multiset.map_map, Multiset.map_map]
      exact Multiset.map_congr rfl fun b _ => by simp⟩
  have hg : Function.Injective g := fun x y h => by
    have h' := congrArg Subtype.val h
    simp only [g, Prod.mk.injEq] at h'
    exact Subtype.ext (Prod.ext (e.injective h'.1) (Multiset.map_injective σ.injective h'.2))
  exact ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.1 hg), fun _ => rfl⟩

private theorem int_root (p f : ℕ) (h1 : 1 ≤ f) (a : ℤ) (b : ℂ)
    (h : IsIntegral ℤ (((p ^ f : ℕ) : ℂ) ^ a * b ^ f)) : IsIntegral ℤ ((p : ℂ) ^ a * b) := by
  refine IsIntegral.of_pow (n := f) h1 ?_
  convert h using 1
  rw [mul_pow, Nat.cast_pow, ← zpow_natCast, ← zpow_natCast (p : ℂ), ← zpow_mul, ← zpow_mul, mul_comm a]

/-- Extracting `f`-th roots (`1 ≤ f ≤ 2`) across a finite family of `EigData n (p ^ f_i) m wt`
produces an `EigData n p m wt` with `|D'.S| ≤ 2^(n+1) * ∑ |D_i.S|` (`RootSum.lean`). -/
theorem rootSum (n p : ℕ) (_hp : 0 < p) (m : Fin n → ℤ) (wt : ℤ) (I : Type) [Fintype I]
    (q f : I → ℕ) (hf : ∀ i, 1 ≤ f i ∧ f i ≤ 2 ∧ q i = p ^ f i)
    (D : ∀ i, EigData n (q i) m wt) :
    ∃ D' : EigData n p m wt, Nat.card D'.S ≤ 2 ^ (n + 1) * ∑ i, Nat.card (D i).S ∧
      ∃ e : (Σ i, {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1} × Bool) → D'.S,
        Function.Injective e ∧ ∀ x, D'.β (e x) = x.2.1.1.2 := by
  have : ∀ i, Finite {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1} :=
    fun i => (pairs_card (D i) (f i) (hf i).1 (hf i).2.1).1
  have hmem : ∀ i (x : {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1}),
      ∀ b ∈ x.1.2, b ^ f i ∈ (D i).β x.1.1 := fun i x b hb => by
    rw [← x.2]; exact Multiset.mem_map_of_mem _ hb
  refine ⟨⟨Σ i, {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1} × Bool, inferInstance,
    fun x => x.2.1.1.2, ?_, ?_, ?_, ?_, ?_⟩, ?_, id, Function.injective_id, fun _ => rfl⟩
  · rintro ⟨i, x, t⟩
    have := (D i).card x.1.1
    rw [← x.2, Multiset.card_map] at this
    exact this
  · intro σ
    choose e he using fun i => pairs_conj (D i) (f i) (hf i).1 (hf i).2.1 σ
    exact ⟨Equiv.sigmaCongrRight fun i => (e i).prodCongr (Equiv.refl _), fun x => he x.1 x.2.1⟩
  · rintro ⟨i, x, t⟩ b hb
    have h := (D i).pure _ _ (hmem i x b hb)
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have hq : ((q i : ℕ) : ℝ) = (p : ℝ) ^ f i := by rw [(hf i).2.2, Nat.cast_pow]
    rw [norm_pow, hq, ← Real.rpow_natCast (p : ℝ), ← Real.rpow_mul hp0, mul_comm,
      Real.rpow_mul hp0, Real.rpow_natCast] at h
    exact (pow_left_inj₀ (norm_nonneg _) (Real.rpow_nonneg hp0 _) (by have := (hf i).1; omega)).1 h
  · rintro a ha ⟨i, x, t⟩ b hb
    have h := (D i).int a ha _ _ (hmem i x b hb)
    refine int_root p (f i) (hf i).1 a b ?_
    rw [← (hf i).2.2]; exact h
  · rintro a ha ⟨i, x, t⟩ b hb
    have h := (D i).intInv a ha _ _ (hmem i x b hb)
    refine int_root p (f i) (hf i).1 a b⁻¹ ?_
    rw [← (hf i).2.2, inv_pow]; exact h
  · show Nat.card (Σ i, {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1} × Bool) ≤ _
    rw [Nat.card_sigma, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
    have := (pairs_card (D i) (f i) (hf i).1 (hf i).2.1).2
    calc _ ≤ 2 ^ n * Nat.card (D i).S * 2 := Nat.mul_le_mul_right _ this
      _ = _ := by ring

/-! ### 2.4 Continuous Completion Isomorphism & Place Transport (`PlaceOf.lean`, `LevelRes.lean`) -/

/-- Compatibility of valuation subrings, ring isomorphisms, and completion isomorphisms
(`PlaceOf.lean`, `WdAway.lean`, `RecInv.lean`). -/
structure PlaceIso {F K Ω Ω' : Type*} [Field F] [NumberField F] [Field K] [NumberField K]
    [Field Ω] [Field Ω'] [Algebra F Ω] [Algebra K Ω']
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F))
    (B : ValuationSubring Ω') (w : HeightOneSpectrum (𝓞 K))
    (τ : Ω ≃+* Ω') (j : F →+* K) (i : v.adicCompletion F ≃+* w.adicCompletion K) : Prop where
  val : ∀ x : Ω, x ∈ A ↔ τ x ∈ B
  alg : ∀ x : F, τ (algebraMap F Ω x) = algebraMap K Ω' (j x)
  cont : Continuous i
  comp : ∀ x : F, i (algebraMap F _ x) = algebraMap K _ (j x)

private theorem lt_one_of_tendsto {R Γ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ]
    [Valued R Γ] {x : R} (h : Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0)) :
    (Valued.v x : Γ) < 1 := by
  by_contra hx
  have hx' : 1 ≤ (Valued.v x : Γ) := not_lt.1 hx
  have ho : {y : R | (Valued.v y : Γ) < 1} ∈ 𝓝 (0 : R) := by
    rw [Valued.mem_nhds_zero]
    refine ⟨1, fun y hy => ?_⟩
    simpa [Valuation.restrict_lt_iff_lt_embedding] using hy
  obtain ⟨n, hn⟩ := (h.eventually ho).exists
  rw [map_pow] at hn
  exact absurd hn (not_lt.2 (one_le_pow₀ hx'))

private theorem tendsto_zero_pow_of_v_lt_one {R : Type*} [Ring R]
    [Valued R (WithZero (Multiplicative ℤ))] {x : R}
    (hx : (Valued.v x : WithZero (Multiplicative ℤ)) < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(Valued.hasBasis_nhds_zero R (WithZero (Multiplicative ℤ))).tendsto_right_iff]
  intro γ _
  rw [Filter.eventually_atTop]
  have h1 : ∀ y : R, Valued.v.restrict y < γ.val ↔
      Valued.v y < MonoidWithZeroHom.ValueGroup₀.embedding γ.val :=
    fun _ => Valuation.restrict_lt_iff_lt_embedding Valued.v
  set c : WithZero (Multiplicative ℤ) := MonoidWithZeroHom.ValueGroup₀.embedding γ.val
  have hc_ne : c ≠ 0 := ((Units.isUnit γ).map MonoidWithZeroHom.ValueGroup₀.embedding).ne_zero
  obtain ⟨γ₀, hγ₀⟩ := WithZero.ne_zero_iff_exists.mp hc_ne
  by_cases hx0 : (Valued.v x : WithZero (Multiplicative ℤ)) = 0
  · refine ⟨1, fun n hn => ?_⟩
    change Valued.v.restrict (x ^ n) < γ.val
    rw [h1, map_pow, hx0, zero_pow (by omega)]
    change (0 : WithZero (Multiplicative ℤ)) < c
    rw [← hγ₀]
    exact WithZero.zero_lt_coe _
  · obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.mp hx0
    have ha_neg : Multiplicative.toAdd a < 0 := by
      have h2 : (a : WithZero (Multiplicative ℤ)) < (1 : WithZero (Multiplicative ℤ)) := ha.symm ▸ hx
      exact Multiplicative.toAdd_lt.mpr (WithZero.coe_lt_coe.mp h2)
    set g : ℤ := Multiplicative.toAdd γ₀
    refine ⟨((-g).toNat + 1), fun n hn => ?_⟩
    change Valued.v.restrict (x ^ n) < γ.val
    rw [h1, map_pow, ← ha, ← WithZero.coe_pow, ← hγ₀]
    apply WithZero.coe_lt_coe.mpr
    show Multiplicative.toAdd (a ^ n) < g
    rw [toAdd_pow, nsmul_eq_mul]
    nlinarith [Int.self_le_toNat (-g)]

/-- Any continuous completion isomorphism `i : v.adicCompletion F ≃+* w.adicCompletion K` extending
`algebraMap F K` forces `w.under (𝓞 F) = v` and yields a common valuation subring `A` over both
`v` and `w` with `PlaceIso` (`PlaceOf.lean`). -/
theorem placeOf (F K Ω : Type*) [Field F] [NumberField F] [Field K] [NumberField K]
    [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω]
    [IsAlgClosure F Ω] [IsAlgClosure K Ω]
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K))
    (i : v.adicCompletion F ≃+* w.adicCompletion K) (hi : Continuous i)
    (hx : ∀ x : F, i (algebraMap F _ x) = algebraMap K _ (algebraMap F K x)) :
    w.under (𝓞 F) = v ∧ ∃ A : ValuationSubring Ω, IsPlaceOver A v ∧ IsPlaceOver A w ∧
      PlaceIso A v A w (RingEquiv.refl Ω) (algebraMap F K) i := by
  have hle : v.asIdeal ≤ (w.under (𝓞 F)).asIdeal := by
    intro y hy
    have h1 : (Valued.v (algebraMap F (v.adicCompletion F) (y : F)) : WithZero (Multiplicative ℤ)) < 1 := by
      have h3 : (Valued.v (algebraMap F (v.adicCompletion F) (y : F)) : WithZero (Multiplicative ℤ)) =
          v.valuation F (y : F) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
      rw [h3]
      exact (v.valuation_lt_one_iff_mem y).2 hy
    have h2 : Tendsto (fun n : ℕ => (algebraMap F (v.adicCompletion F) (y : F)) ^ n) atTop (𝓝 0) :=
      tendsto_zero_pow_of_v_lt_one h1
    have h4 : Tendsto (fun n : ℕ => (i (algebraMap F (v.adicCompletion F) (y : F))) ^ n) atTop (𝓝 0) := by
      have := (hi.tendsto 0).comp h2
      rw [map_zero] at this
      exact this.congr fun n => by simp
    have h5 := lt_one_of_tendsto (Γ := WithZero (Multiplicative ℤ)) h4
    rw [hx] at h5
    have h6 : (Valued.v (algebraMap K (w.adicCompletion K) (algebraMap F K y)) : WithZero (Multiplicative ℤ)) =
        w.valuation K (algebraMap F K y) := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    rw [h6] at h5
    exact (w.valuation_lt_one_iff_mem (K := K) (algebraMap (𝓞 F) (𝓞 K) y)).1 h5
  have hv : w.under (𝓞 F) = v :=
    HeightOneSpectrum.ext (v.isMaximal.eq_of_le (w.under (𝓞 F)).isPrime.ne_top hle).symm
  obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
  refine ⟨hv, A, fun y => ?_, hA, fun _ => Iff.rfl, fun x => IsScalarTower.algebraMap_apply F K Ω x, hi, hx⟩
  rw [← hv, IsScalarTower.algebraMap_apply F K Ω]
  exact hA (algebraMap (𝓞 F) (𝓞 K) y)

/-- Place-moving conjugacy along a field extension `F ↪ K`: transports decomposition and inertia
subgroups from `B` over `w` to `A` over `w.under (𝓞 F)` (`LevelRes.lean`). -/
theorem move_place_over {F K Ω : Type*} [Field F] [NumberField F] [Field K] [NumberField K]
    [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω]
    [IsAlgClosure F Ω] [IsAlgClosure K Ω]
    (w : HeightOneSpectrum (𝓞 K)) {A : ValuationSubring Ω} (hA : IsPlaceOver A (w.under (𝓞 F))) :
    ∃ (B : ValuationSubring Ω) (g : G F Ω), IsPlaceOver B w ∧ (∀ x, x ∈ B ↔ g x ∈ A) ∧
      (∀ s ∈ Dec (F := K) B, g * res F Ω K s * g⁻¹ ∈ Dec (F := F) A) ∧
      ∀ s ∈ Ine (F := K) B, g * res F Ω K s * g⁻¹ ∈ Ine (F := F) A := by
  obtain ⟨B, hB⟩ := exists_isPlaceOver Ω w
  have hB' : IsPlaceOver B (w.under (𝓞 F)) := fun x => by
    rw [IsScalarTower.algebraMap_apply F K Ω]
    exact hB (algebraMap (𝓞 F) (𝓞 K) x)
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hB' hA
  have hm : ∀ x, x ∈ B ↔ g x ∈ g • B := fun x => ValuationSubring.smul_mem_pointwise_smul_iff.symm
  have hD : ∀ s ∈ Dec (F := K) B, g * res F Ω K s * g⁻¹ ∈ Dec (F := F) (g • B) := fun s hs => by
    have h1 : res F Ω K s • B = B := hs
    show (g * res F Ω K s * g⁻¹) • g • B = g • B
    rw [mul_smul, mul_smul, inv_smul_smul, h1]
  refine ⟨B, g, hB, hm, hD, fun s hs => ⟨hD s hs.1, fun x hx => ?_⟩⟩
  obtain ⟨y, rfl⟩ := g.surjective x
  have e : (g * res F Ω K s * g⁻¹) (g y) = g (s y) := by
    show g (s (g.symm (g y))) = _
    rw [AlgEquiv.symm_apply_apply]
  rw [e, ← map_sub, val_smul_lt]
  exact hs.2 y ((B.valuation_le_one_iff _).2 ((hm y).2 (((g • B).valuation_le_one_iff _).1 hx)))

/-- Semisimple level structure `LevelS` (`CqStmt.lean`). -/
structure LevelS {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] {n : ℕ} (M : ℕ) (m : Fin n → ℤ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop where
  cont : Continuous r
  away : LevelAway l M r
  above : ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal →
    ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ ∃ κ, FlagAt M m r A κ
  safe : l ∣ M ∨ ∀ i j, m i ≠ m j + 1

/-- Restriction of `LevelS` along a number-field extension `F ↪ K` (`LevelRes.lean`). -/
theorem levelS_res (F K Ω : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Field Ω] [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω]
    [IsAlgClosure F Ω] [IsAlgClosure K Ω]
    (l : ℕ) [Fact l.Prime] (n M : ℕ) (m : Fin n → ℤ) (r : G F Ω →* GL (Fin n) (Qbar l))
    (H : LevelS l M m r) : LevelS l M m (r.comp (res F Ω K)) := by
  have : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  have hres : Continuous (res F Ω K : G K Ω →* G F Ω) := (galEmbTop F K Ω).1.continuous
  have hK : ∀ χ : G F Ω →* (Qbar l)ˣ, KillsMu M χ → KillsMu M (χ.comp (res F Ω K)) :=
    fun χ h s hs => h _ hs
  have char_conj : ∀ (χ : G F Ω →* (Qbar l)ˣ) (g s : G F Ω),
      χ (g * s * g⁻¹) = χ s := fun χ g s => by
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  have rep_conj : ∀ (P : GL (Fin n) (Qbar l)) (g s : G F Ω),
      P * r g * r s * (P * r g)⁻¹ = P * r (g * s * g⁻¹) * P⁻¹ := fun P g s => by
    rw [map_mul, map_mul, map_inv]; group
  refine ⟨H.cont.comp hres, fun w hw => ?_, fun w hw => ?_, H.safe⟩
  · obtain ⟨A, hA, χ, hχ, P, hP⟩ := H.away (w.under (𝓞 F)) (fun h => hw ((nat_mem_under l w).1 h))
    obtain ⟨B, g, hB, -, -, hI⟩ := move_place_over w hA
    refine ⟨B, hB, fun i => (χ i).comp (res F Ω K), fun i => hK _ (hχ i), P * r g, fun s hs => ?_⟩
    have h := hP _ (hI s hs)
    have hch : (fun i => ((χ i (g * res F Ω K s * g⁻¹) : (Qbar l)ˣ) : Qbar l)) =
        (fun i => (((χ i).comp (res F Ω K) s : (Qbar l)ˣ) : Qbar l)) := by
      ext i; exact congrArg Units.val (char_conj (χ i) g (res F Ω K s))
    rw [hch] at h
    rw [MonoidHom.comp_apply, rep_conj P g (res F Ω K s)]
    exact h
  · obtain ⟨A, hA, κ, χ, hχ, ⟨P, hP⟩, hκ⟩ := H.above (w.under (𝓞 F)) ((nat_mem_under l w).2 hw)
    obtain ⟨B, g, hB, -, hD, hI⟩ := move_place_over w hA
    let d : Dec (F := K) B →* Dec (F := F) A :=
      (((MulAut.conj g).toMonoidHom.comp (res F Ω K)).comp (Dec (F := K) B).subtype).codRestrict _
        fun s => hD s s.2
    have hd : ∀ s, (d s : G F Ω) = g * res F Ω K s * g⁻¹ := fun _ => rfl
    refine ⟨B, hB, fun i => (κ i).comp d, fun i => (χ i).comp (res F Ω K),
      fun i => hK _ (hχ i), ⟨P * r g, fun s => ?_⟩, fun i s hs => ?_⟩
    · have hconj : P * r g * r ((res F Ω K) s) * (P * r g)⁻¹ = P * r (d s) * P⁻¹ := rep_conj P g _
      simpa only [MonoidHom.comp_apply, hconj] using hP (d s)
    · have h := hκ i (d s) (hI s hs)
      rw [hd, char_conj (χ i) g, char_conj (cycBar F Ω l) g] at h
      have hcyc : cycBar K Ω l s = cycBar F Ω l (res F Ω K s) := by
        ext
        simp [cycBar, cycZ]
      rw [hcyc]
      exact h

/-! ### 2.5 Quadratic Counting Assembly (`CountQuadraticOfHyp.lean`) -/

/-- Full quadratic counting reduction (`CountQuadraticOfHyp.lean`): given any CM-quadratic family
counting bound `hCountP` and admissible quadratic restriction `hAdmRes` on a family of predicates
`AdmR` over `ℚ` and `AdmP` over imaginary quadratic fields `K`, deduces a polynomial counting bound
`CountQ` over `ℚ` using `quadFam`, `exists_avoid`, `exists_over`, `rootSum`, `signNe`, `twCard`,
`resTwo`, `frobEx`, `frobenius_power_compatibility`, and `bit_of_fibre`. -/
theorem count_quadratic_of_hypotheses
    (AdmP : ∀ (K Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω]
      [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime] {n : ℕ},
      (Qbar l ≃+* ℂ) → ℕ → (Fin n → ℤ) → (G K Ω →* GL (Fin n) (Qbar l)) → Prop)
    (AdmR : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {n : ℕ},
      (Qbar l ≃+* ℂ) → ℕ → (Fin n → ℤ) → ℤ → (G ℚ Ω →* GL (Fin n) (Qbar l)) → Prop)
    (hIrrR : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
      (ι : Qbar l ≃+* ℂ) (M : ℕ) (m : Fin n → ℤ) (wt : ℤ) (r : G ℚ Ω →* GL (Fin n) (Qbar l)),
      AdmR Ω ι M m wt r → IsIrr r ∧ LevelAway l M r)
    (hIrrP : ∀ (K Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω]
      [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
      (ι : Qbar l ≃+* ℂ) (M : ℕ) (m : Fin n → ℤ) (r : G K Ω →* GL (Fin n) (Qbar l)),
      AdmP K Ω ι M m r → IsIrr r)
    (hCountP : ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 →
      ∀ (n : ℕ), 2 ≤ n → ∃ c A : ℕ,
        ∀ (m : Fin n → ℤ) (wt : ℤ), StrictAnti m → (∀ i, m i + m i.rev = wt) →
        ∀ H : ℕ, (∀ i, |m i| ≤ H) → ∀ M : ℕ, 1 ≤ M →
        ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 K)), p.Prime → (p : 𝓞 K) ∈ w.asIdeal →
          ¬ p ∣ M → ¬ (p : ℤ) ∣ discr K →
          ∃ D : EigData n (normV w) m wt, Nat.card D.S ≤ c * (M * (H + 1)) ^ A ∧
            ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p →
              ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ),
                D.Classifies (Ω := Ω) ι (AdmP K Ω ι M m))
    (hAdmRes : ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 →
      ∀ (n : ℕ), 2 ≤ n → ∀ (m : Fin n → ℤ) (wt : ℤ), StrictAnti m → ∀ M : ℕ, 1 ≤ M →
      ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 →
      ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω]
        [IsAlgClosure ℚ Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ) (r : G ℚ Ω →* GL (Fin n) (Qbar l)),
        AdmR Ω ι M m wt r → IsIrr (r.comp (res ℚ Ω K)) → AdmP K Ω ι M m (r.comp (res ℚ Ω K))) :
    ∀ (n : ℕ), 2 ≤ n → ∃ c A : ℕ,
      ∀ (m : Fin n → ℤ) (wt : ℤ), StrictAnti m → (∀ i, m i + m i.rev = wt) →
      ∀ H : ℕ, (∀ i, |m i| ≤ H) → ∀ M : ℕ, 1 ≤ M →
      ∀ (p : ℕ) (w : HeightOneSpectrum (𝓞 ℚ)), p.Prime → (p : 𝓞 ℚ) ∈ w.asIdeal → ¬ p ∣ M →
        ∃ D : EigData n (normV w) m wt, Nat.card D.S ≤ c * (M * (H + 1)) ^ A ∧
          ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → l ≠ p →
            ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ),
              D.Classifies (Ω := Ω) ι (AdmR Ω ι M m wt) := by
  intro n hn
  classical
  obtain ⟨K₀, _, _, _, hK2, hKc⟩ := quadFam (n ^ 2 + 1 + 1)
  choose c A hcA using fun i => hCountP (K₀ i) (hK2 i) n hn
  refine ⟨2 ^ (n + 1) * ((n ^ 2 + 1) * ∑ i, c i), ∑ i, A i, ?_⟩
  intro m wt hm hwt H hH M hM p w hp hpw hpM
  obtain ⟨u, hu, hup⟩ := exists_avoid (fun i => discr (K₀ i)) hKc hp
  choose v f hvw hpv hf1 hf2 hvf using fun i => exists_over (K₀ (u i)) (hK2 _) hp w hpw
  choose D hDc hD using fun i => hcA (u i) m wt hm hwt H hH M hM p (v i) hp (hpv i) hpM (hup i)
  obtain ⟨D', hD', e, he, heβ⟩ := rootSum n (normV w) (zero_lt_one.trans (one_lt_normV w)) m wt
    (Fin (n ^ 2 + 1)) (fun i => normV (v i)) f
    (fun i => ⟨hf1 i, hf2 i, by rw [normV_rat hp w hpw]; exact hvf i⟩) D
  refine ⟨D', hD'.trans ?_, ?_⟩
  · rw [mul_assoc, mul_assoc]
    refine Nat.mul_le_mul_left _ ?_
    have hb : ∀ i, Nat.card (D i).S ≤ (∑ i, c i) * (M * (H + 1)) ^ (∑ i, A i) := fun i =>
      (hDc i).trans (Nat.mul_le_mul (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))
        (Nat.pow_le_pow_right (Nat.mul_pos hM (Nat.succ_pos _))
          (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))))
    refine (Finset.sum_le_sum fun i _ => hb i).trans ?_
    simp
  intro l _ hl2 hlp Ω _ _ _ ι
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  let emb : ∀ i, K₀ (u i) →ₐ[ℚ] Ω := fun i => IsAlgClosed.lift
  let alg : ∀ i, Algebra (K₀ (u i)) Ω := fun i => (emb i).toRingHom.toAlgebra
  have tow : ∀ i, IsScalarTower ℚ (K₀ (u i)) Ω := fun i =>
    IsScalarTower.of_algebraMap_eq fun x => ((emb i).commutes x).symm
  have clo : ∀ i, IsAlgClosure (K₀ (u i)) Ω := fun i =>
    ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) _⟩
  choose δ hδ1 hδ2 using fun i =>
    exists_quadratic_sign_character ℚ (K₀ (u i)) Ω (Qbar l) (hK2 _)
  have hδi : Function.Injective δ := fun i j hij => by
    by_contra hne
    refine signNe (K₀ (u i)) (K₀ (u j)) Ω (hK2 _) (hKc _ _ fun h => hne (hu h)) (Subgroup.ext fun s => ?_)
    rw [← hδ1 i s, ← hδ1 j s, hij]
  choose cl hcl hclβ using fun i => hD i l hl2 hlp Ω ι
  have hlw : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal :=
    not_mem_of_coprime ((Nat.coprime_primes hp Fact.out).2 hlp.symm) w hpw
  have hMw : ((M : ℕ) : 𝓞 ℚ) ∉ w.asIdeal :=
    not_mem_of_coprime ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM) w hpw
  have hinv_inv : ∀ B : Multiset ℂ, (B.map (·⁻¹)).map (·⁻¹) = B := fun B => by
    rw [Multiset.map_map]; simp
  refine Exists.elim (bit_of_fibre (X := {r : G ℚ Ω →* GL (Fin n) (Qbar l) // AdmR Ω ι M m wt r})
    (U := Σ i, {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1})
    (fun r r' => RepIso r.1 r'.1) (fun _ _ => RepIso.symm) (fun _ _ _ => RepIso.trans)
    (fun r t => (∃ h : AdmP (K₀ (u t.1)) Ω ι M m (r.1.comp (res ℚ Ω (K₀ (u t.1)))),
        cl t.1 ⟨_, h⟩ = t.2.1.1) ∧
      FrobEig ι r.1 w (t.2.1.2.map (·⁻¹))) ?ex ?two) ?main
  case main =>
    rintro g ⟨hg, hgQ⟩
    refine ⟨fun r => e ⟨(g r).1.1, (g r).1.2, (g r).2⟩, fun r r' h => hg r r' ?_, fun r => ?_⟩
    · have h1 := congrArg (fun x : (Σ i, {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1} × Bool) =>
        ((⟨x.1, x.2.1⟩ : Σ i, {x : (D i).S × Multiset ℂ // x.2.map (· ^ f i) = (D i).β x.1}), x.2.2)) (he h)
      exact h1
    · rw [heβ]
      exact (hgQ r).2
  case ex =>
    rintro ⟨r, hr⟩
    obtain ⟨hirrR, hawayR⟩ := hIrrR Ω ι M m wt r hr
    obtain ⟨i, hi⟩ : ∃ i, ¬ RepIso r (tw r (δ i)) := by
      by_contra hall
      have h1 := twCard r hirrR (Finset.univ.image δ) fun d hd => by
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hd
        by_contra h
        exact hall ⟨i, h⟩
      rw [Finset.card_image_of_injective _ hδi, Finset.card_univ, Fintype.card_fin] at h1
      omega
    have hirr := (resTwo (res ℚ Ω (K₀ (u i))) (δ i) (hδ1 i) (hδ2 i) r).1 hirrR hi
    have hadm := hAdmRes (K₀ (u i)) (hK2 _) n hn m wt hm M hM l hl2 Ω ι r hr hirr
    obtain ⟨B, hB⟩ := (frobEx ℚ Ω l ι n r w).2 M hawayR hlw hMw
    have h1 := frobenius_power_compatibility ℚ (K₀ (u i)) Ω l ι (v i) (f i)
      (by rw [hvw, hvf, normV_rat hp w hpw]) n r B (by rw [hvw]; exact hB)
    have h2 := (frobEx (K₀ (u i)) Ω l ι n _ (v i)).1 _ _ h1 (hclβ i ⟨_, hadm⟩)
    refine ⟨⟨i, ⟨(cl i ⟨_, hadm⟩, B.map (·⁻¹)), ?_⟩⟩, ⟨hadm, rfl⟩, ?_⟩
    · show (B.map (·⁻¹)).map (· ^ f i) = (D i).β (cl i ⟨_, hadm⟩)
      rw [← hinv_inv ((D i).β _), ← h2, Multiset.map_map, Multiset.map_map]
      exact Multiset.map_congr rfl fun b _ => inv_pow b (f i)
    · show FrobEig ι r w ((B.map (·⁻¹)).map (·⁻¹))
      rw [hinv_inv]
      exact hB
  case two =>
    rintro ⟨i, t⟩ r₀ r r' ⟨⟨a₀, e₀⟩, -⟩ ⟨⟨a, e₁⟩, -⟩ ⟨⟨a', e₂⟩, -⟩ n1 n2
    have hR := (resTwo (res ℚ Ω (K₀ (u i))) (δ i) (hδ1 i) (hδ2 i) r₀.1).2
    have hirr0 := hIrrP (K₀ (u i)) Ω ι M m _ a₀
    have k1 := (hR r.1 hirr0 (hcl i _ _ (e₀.trans e₁.symm))).resolve_left n1
    have k2 := (hR r'.1 hirr0 (hcl i _ _ (e₀.trans e₂.symm))).resolve_left n2
    exact RepIso.trans (RepIso.symm k1) k2

end FrobeniusAndEigData

/-! ## Section 3: Capelli Casimir, `SL₂` Lowest-Weight Theory, Iwasawa Descent & Hecke Eigenforms -/

section CapelliSl2AndHecke

/-- Explicit `2×2` quantum determinant expansion (`CapTwo.lean`). -/
theorem qdet2 {A : Type*} [Ring A] [Algebra ℂ A] (E : Fin 2 → Fin 2 → A) (u : ℂ) :
    RHDirect.CapelliCore.qdet E u =
      (algebraMap ℂ A u + E 0 0) * (algebraMap ℂ A (u - 1) + E 1 1) - E 1 0 * E 0 1 := by
  have h : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  rw [RHDirect.CapelliCore.qdet, RHDirect.CapelliCore.qminor, h, Finset.sum_pair (by decide)]
  simp [RHDirect.CapelliCore.capelliTm, List.ofFn_succ, sub_eq_add_neg]

/-- Extracting trace and quadratic Casimir eigenvalues from a `2×2` Capelli infinitesimal
character (`CapTwo.lean`). -/
theorem cap2 {V : Type*} [AddCommGroup V] [Module ℂ V] (E : Fin 2 → Fin 2 → Module.End ℂ V)
    (hE : RHDirect.CapelliCore.GlRel E) (a b : ℂ) (φ : V)
    (h : ∀ u : ℂ, RHDirect.CapelliCore.qdet E (u + 1 / 2) φ = ((u + a) * (u + b)) • φ) :
    E 0 0 φ + E 1 1 φ = (a + b) • φ ∧
      E 0 0 (E 0 0 φ) + E 0 1 (E 1 0 φ) + E 1 0 (E 0 1 φ) + E 1 1 (E 1 1 φ) =
        (a ^ 2 + b ^ 2 - 1 / 2) • φ := by
  have h0 := h 0
  have h1 := h 1
  rw [qdet2] at h0 h1
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    Module.algebraMap_end_apply, map_add, map_smul] at h0 h1
  have hs : E 0 0 φ + E 1 1 φ = (a + b) • φ := by
    linear_combination (norm := module) h1 - h0
  have r1 : E 0 0 (E 1 1 φ) - E 1 1 (E 0 0 φ) = 0 := by
    simpa using LinearMap.congr_fun (hE 0 0 1 1) φ
  have r2 : E 0 1 (E 1 0 φ) - E 1 0 (E 0 1 φ) = E 0 0 φ - E 1 1 φ := by
    simpa using LinearMap.congr_fun (hE 0 1 1 0) φ
  have s0 := congrArg (E 0 0) hs
  have s1 := congrArg (E 1 1) hs
  simp only [map_add, map_smul] at s0 s1
  refine ⟨hs, ?_⟩
  linear_combination (norm := module) s0 + s1 + (a + b) • hs + r1 + r2 - (2 : ℂ) • h0

private theorem sl2_wt_low {V : Type*} [AddCommGroup V] [Module ℂ V] {W L : Module.End ℂ V}
    (hL : W * L - L * W = (-2 : ℂ) • L) {x : V} {n : ℤ} (hx : W x = (n : ℂ) • x) :
    W (L x) = ((n - 2 : ℤ) : ℂ) • L x := by
  have h := congrArg (fun f : Module.End ℂ V => f x) hL
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, hx, map_smul] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  push_cast
  module

private theorem sl2_cas {V : Type*} [AddCommGroup V] [Module ℂ V] {W R L : Module.End ℂ V} {k : ℕ}
    (hC : (4 : ℂ) • (R * L) = ((k : ℂ) * (k - 2)) • 1 - (W * W - (2 : ℂ) • W)) {x : V} {n : ℤ}
    (hx : W x = (n : ℂ) • x) :
    R (L x) = ((((k : ℤ) * (k - 2) - n * (n - 2) : ℤ) : ℂ) / 4) • x := by
  have h := congrArg (fun f : Module.End ℂ V => f x) hC
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, hx, map_smul,
    Module.End.one_apply] at h
  have e : R (L x) = (1 / 4 : ℂ) • (4 : ℂ) • R (L x) := by rw [smul_smul]; norm_num
  rw [e, h]
  push_cast
  module

private theorem sl2_bound {V : Type*} [AddCommGroup V] [Module ℂ V] {W R L : Module.End ℂ V}
    {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} {k : ℕ} (hL : W * L - L * W = (-2 : ℂ) • L)
    (hC : (4 : ℂ) • (R * L) = ((k : ℂ) * (k - 2)) • 1 - (W * W - (2 : ℂ) • W))
    (h0 : ∀ x, H x x = 0 → x = 0) (hW : ∀ x y, H (W x) y = H x (W y))
    (hH : ∀ x y, H (L x) y = -H x (R y)) {x : V} (hx0 : x ≠ 0) {n : ℤ}
    (hx : W x = (n : ℂ) • x) : (k : ℤ) * (k - 2) ≤ n * (n - 2) := by
  by_contra hlt
  push Not at hlt
  have hltR : (n : ℝ) * (n - 2) < (k : ℝ) * (k - 2) := by exact_mod_cast hlt
  set c : ℝ := ((k : ℝ) * (k - 2) - n * (n - 2)) / 4 with hc
  have hcpos : 0 < c := div_pos (by linarith) (by norm_num)
  have hcC : ((((k : ℤ) * (k - 2) - n * (n - 2) : ℤ) : ℂ) / 4) = (c : ℂ) := by
    rw [hc]; push_cast; ring
  have hwl := sl2_wt_low hL hx
  have h1 : H x (L x) = 0 := by
    have e := hW x (L x)
    rw [hx, hwl] at e
    simp [map_smulₛₗ] at e
    rcases e with e | e
    · have h2 : (2 : ℂ) = 0 := by linear_combination e
      norm_num at h2
    · exact e
  have h2 : H (L x) x = 0 := by
    have e := hW (L x) x
    rw [hwl, hx] at e
    simp [map_smulₛₗ] at e
    exact e
  have h3 : H (L x) (L x) = -(c : ℂ) * H x x := by
    have e := hH x (L x)
    rw [sl2_cas hC hx, hcC] at e
    simp only [map_smul, smul_eq_mul] at e
    rw [e]; ring
  set s : ℂ := ((Real.sqrt c : ℝ) : ℂ) with hsdef
  have hs : (starRingEnd ℂ) s = s := Complex.conj_ofReal _
  have hss : s * s = (c : ℂ) := by
    rw [hsdef, ← Complex.ofReal_mul, Real.mul_self_sqrt hcpos.le]
  have hy : H (s • x + L x) (s • x + L x) = 0 := by
    simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      hs, h1, h2, h3, RingHom.id_apply]
    ring_nf
    linear_combination (H x x) * hss
  have hy0 := h0 _ hy
  have hLx : L x = -(s • x) := eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hy0)
  have e1 : W (L x) = -(s • ((n : ℂ) • x)) := by rw [hLx, map_neg, map_smul, hx]
  rw [hwl, hLx] at e1
  have key : ((2 : ℂ) * s) • x = 0 := by
    have e2 : ((2 : ℂ) * s) • x = (((n - 2 : ℤ) : ℂ) • -(s • x)) - (-(s • ((n : ℂ) • x))) := by
      push_cast; module
    rw [e2, e1, sub_self]
  rcases smul_eq_zero.mp key with h | h
  · have hs0 : s = 0 := by
      rcases mul_eq_zero.mp h with h' | h'
      · norm_num at h'
      · exact h'
    have hc0 : (c : ℂ) = 0 := by rw [← hss, hs0, mul_zero]
    have : c = 0 := by exact_mod_cast hc0
    linarith
  · exact hx0 h

private theorem sl2_descend {V : Type*} [AddCommGroup V] [Module ℂ V] {W R L : Module.End ℂ V}
    {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} {k : ℕ} (hk : 3 ≤ k) (hL : W * L - L * W = (-2 : ℂ) • L)
    (hC : (4 : ℂ) • (R * L) = ((k : ℂ) * (k - 2)) • 1 - (W * W - (2 : ℂ) • W))
    (h0 : ∀ x, H x x = 0 → x = 0) (hW : ∀ x y, H (W x) y = H x (W y))
    (hH : ∀ x y, H (L x) y = -H x (R y)) (j : ℕ) :
    ∀ x : V, x ≠ 0 → W x = ((j : ℤ) : ℂ) • x → ∃ x, x ≠ 0 ∧ W x = (k : ℂ) • x ∧ L x = 0 := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro x hx0 hx
    have hb := sl2_bound hL hC h0 hW hH hx0 hx
    have hk' : (3 : ℤ) ≤ k := by exact_mod_cast hk
    have hj2 : 2 ≤ j := by
      by_contra h
      push Not at h
      interval_cases j <;> (push_cast at hb; nlinarith)
    by_cases hL0 : L x = 0
    · refine ⟨x, hx0, ?_, hL0⟩
      have hc := sl2_cas hC hx
      rw [hL0, map_zero] at hc
      have hq : ((((k : ℤ) * (k - 2) - ((j : ℤ) : ℤ) * ((j : ℤ) - 2) : ℤ)) : ℂ) / 4 = 0 := by
        rcases smul_eq_zero.mp hc.symm with h | h
        · exact h
        · exact absurd h hx0
      have hq' : (k : ℤ) * (k - 2) - (j : ℤ) * ((j : ℤ) - 2) = 0 := by
        have h4 : (((k : ℤ) * (k - 2) - (j : ℤ) * ((j : ℤ) - 2) : ℤ) : ℂ) = 0 := by
          linear_combination 4 * hq
        exact_mod_cast h4
      have hf : ((k : ℤ) - j) * ((k : ℤ) + j - 2) = 0 := by linear_combination hq'
      have hjk : j = k := by
        rcases mul_eq_zero.mp hf with h | h <;> omega
      rw [hx, hjk]
      simp
    · have hwl := sl2_wt_low hL hx
      refine ih (j - 2) (by omega) (L x) hL0 ?_
      rw [hwl, show ((j - 2 : ℕ) : ℤ) = (j : ℤ) - 2 by omega]

/-- `𝔰𝔩₂(ℂ)` discrete-series unitarity / lowest-weight theorem (`Sl2Low.lean`). -/
theorem sl2Low (V : Type*) [AddCommGroup V] [Module ℂ V] (W R L : Module.End ℂ V)
    (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (k : ℕ) (hk : 3 ≤ k)
    (hR : W * R - R * W = (2 : ℂ) • R) (hL : W * L - L * W = (-2 : ℂ) • L)
    (hC : (4 : ℂ) • (R * L) = ((k : ℂ) * (k - 2)) • 1 - (W * W - (2 : ℂ) • W))
    (hC' : (4 : ℂ) • (L * R) = ((k : ℂ) * (k - 2)) • 1 - (W * W + (2 : ℂ) • W))
    (h0 : ∀ x, H x x = 0 → x = 0) (hW : ∀ x y, H (W x) y = H x (W y))
    (hRH : ∀ x y, H (R x) y = -H x (L y)) (hLH : ∀ x y, H (L x) y = -H x (R y))
    (hex : ∃ x, x ≠ 0 ∧ ∃ n : ℤ, W x = (n : ℂ) • x) :
    ∃ x, x ≠ 0 ∧ ((W x = (k : ℂ) • x ∧ L x = 0) ∨ (W x = (-(k : ℂ)) • x ∧ R x = 0)) := by
  obtain ⟨x, hx0, n, hx⟩ := hex
  have hb := sl2_bound hL hC h0 hW hLH hx0 hx
  have hk' : (3 : ℤ) ≤ k := by exact_mod_cast hk
  have hf : (n - k) * (n + k - 2) = n * (n - 2) - k * (k - 2) := by ring
  rcases le_or_gt (k : ℤ) n with hn | hn
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = j := ⟨n.toNat, by omega⟩
    obtain ⟨y, hy0, hy1, hy2⟩ := sl2_descend hk hL hC h0 hW hLH j x hx0 hx
    exact ⟨y, hy0, Or.inl ⟨hy1, hy2⟩⟩
  · have hn2 : n + k - 2 ≤ 0 := by nlinarith
    obtain ⟨j, hj⟩ : ∃ j : ℕ, -n = j := ⟨(-n).toNat, by omega⟩
    have hL' : (-W) * R - R * (-W) = (-2 : ℂ) • R := by
      rw [show (-W) * R - R * (-W) = -(W * R - R * W) by noncomm_ring, hR]
      module
    have hC2 : (4 : ℂ) • (L * R) = ((k : ℂ) * (k - 2)) • 1 - ((-W) * (-W) - (2 : ℂ) • (-W)) := by
      rw [hC']
      congr 1
      rw [neg_mul_neg, smul_neg, sub_neg_eq_add]
    have hW' : ∀ a b, H ((-W) a) b = H a ((-W) b) := by
      intro a b
      simp only [LinearMap.neg_apply, map_neg, hW]
    have hx' : (-W) x = ((j : ℤ) : ℂ) • x := by
      rw [LinearMap.neg_apply, hx, ← neg_smul, ← hj]
      push_cast
      rfl
    obtain ⟨y, hy0, hy1, hy2⟩ :=
      sl2_descend (W := -W) (R := L) (L := R) (H := H) hk hL' hC2 h0 hW' hRH j x hx0 hx'
    refine ⟨y, hy0, Or.inr ⟨?_, hy2⟩⟩
    rw [neg_smul, ← hy1, LinearMap.neg_apply, neg_neg]

/-- Holomorphic lowest-weight vector extraction from `𝔰𝔩₂(ℂ)` generators, Hermitian form `H`,
and reflection involution `J` (`HolVec.lean`). -/
theorem holVec_low_of {V : Type*} [AddCommGroup V] [Module ℂ V] (A B C J : Module.End ℂ V)
    (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (k : ℕ) (hk : 3 ≤ k)
    (hAB : ∀ x, A (B x) = B (A x) + B x) (hAC : ∀ x, A (C x) = C (A x) - C x)
    (hBC : ∀ x, B (C x) = C (B x) + (2 : ℂ) • A x)
    (hCas : ∀ x, C (B x) = ((k : ℂ) * (k - 2) / 4) • x - A (A x) - A x)
    (hH : ∀ x, H x x = 0 → x = 0) (hA : ∀ x y, H (A x) y = -H x (A y))
    (hB : ∀ x y, H (B x) y = -H x (B y)) (hC : ∀ x y, H (C x) y = -H x (C y))
    (hJ : ∀ x, J x = 0 → x = 0) (hJA : ∀ x, A (J x) = J (A x))
    (hJB : ∀ x, B (J x) = -J (B x)) (hJC : ∀ x, C (J x) = -J (C x))
    (hw : ∃ x, x ≠ 0 ∧ ∃ n : ℤ, B x - C x = (Complex.I * n) • x) :
    ∃ x, x ≠ 0 ∧ B x - C x = (Complex.I * k) • x ∧ (2 : ℂ) • A x = Complex.I • (B x + C x) := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have key := sl2Low V ((-Complex.I) • (B - C)) (A + (Complex.I / 2) • (B + C))
    (A - (Complex.I / 2) • (B + C)) H k hk ?_ ?_ ?_ ?_ hH ?_ ?_ ?_ ?_
  · obtain ⟨x, hx, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := key
    · simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply] at h1 h2
      refine ⟨x, hx, ?_, ?_⟩
      · have : B x - C x = Complex.I • ((-Complex.I) • (B x - C x)) := by
          rw [smul_smul, mul_neg, hI, neg_neg, one_smul]
        rw [this, h1, smul_smul]
      · linear_combination (norm := module) (2 : ℂ) • h2
    · simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply] at h1 h2
      refine ⟨J x, fun h => hx (hJ x h), ?_, ?_⟩
      · have : B x - C x = Complex.I • ((-Complex.I) • (B x - C x)) := by
          rw [smul_smul, mul_neg, hI, neg_neg, one_smul]
        rw [h1] at this
        have h3 := congrArg J this
        simp only [map_sub, map_smul] at h3
        rw [hJB, hJC]
        linear_combination (norm := module) -h3
      · have h3 := congrArg J h2
        simp only [map_add, map_smul, map_zero] at h3
        rw [hJA, hJB, hJC]
        linear_combination (norm := module) (2 : ℂ) • h3
  · ext x
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
      map_add, map_sub, map_smul, hAB, hAC, hBC]
    match_scalars <;> grind
  · ext x
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
      map_add, map_sub, map_smul, hAB, hAC, hBC]
    match_scalars <;> grind
  · ext x
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
      map_add, map_sub, map_smul, Module.End.one_apply, hAB, hAC, hBC, hCas]
    match_scalars <;> grind
  · ext x
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
      map_add, map_sub, map_smul, Module.End.one_apply, hAB, hAC, hBC, hCas]
    match_scalars <;> grind
  · intro x y; simp [hB, hC]; ring
  · intro x y; simp [hA, hB, hC, map_ofNat]; ring
  · intro x y; simp [hA, hB, hC, map_ofNat]; ring
  · obtain ⟨x, hx, n, h⟩ := hw
    refine ⟨x, hx, n, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, h, smul_smul]
    congr 1
    grind

/-! ### 3.2 Affine/Iwasawa Decomposition for `GL₂` & Finite-Codimension Kernel (`IwasawaA`, `CuspSet`, `FinOfKer`) -/

/-- Upper-triangular affine matrix `aff y x = !![y, x; 0, 1] ∈ GL (Fin 2) R`. -/
def aff {R : Type*} [CommRing R] (y : Rˣ) (x : R) : GL (Fin 2) R :=
  ⟨!![(y : R), x; 0, 1], !![((y⁻¹ : Rˣ) : R), -((y⁻¹ : Rˣ) : R) * x; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem aff_mul {R : Type*} [CommRing R] (y y' : Rˣ) (x x' : R) :
    aff y x * aff y' x' = aff (y * y') ((y : R) * x' + x) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [aff, Matrix.mul_apply, Fin.sum_univ_two]

theorem aff_one {R : Type*} [CommRing R] : aff (1 : Rˣ) (0 : R) = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff]

/-- Real `2×2` orthogonal matrix factorization `O(2) = {diag(±1, 1)} · SO(2)` (`CuspSet.lean`). -/
theorem real_orth_decomp {a b c d : ℝ} (h1 : a * a + b * b = 1) (h2 : a * c + b * d = 0)
    (h3 : c * c + d * d = 1) :
    ∃ (s : Bool) (θ : ℝ),
      !![a, b; c, d] = !![(if s then (-1 : ℝ) else 1), 0; 0, 1] *
        !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] := by
  have hdet_sq : (a * d - b * c) ^ 2 = 1 := by
    have : (a * d - b * c) ^ 2 + (a * c + b * d) ^ 2 = (a * a + b * b) * (c * c + d * d) := by ring
    rw [h1, h2, h3] at this
    linarith
  have hnorm : ‖(⟨d, -c⟩ : ℂ)‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp only [mul_neg, neg_mul, neg_neg]
    have : d * d + c * c = 1 := by linarith
    rw [this, Real.sqrt_one]
  set θ : ℝ := Complex.arg (⟨d, -c⟩ : ℂ)
  have hcos : Real.cos θ = d := by
    have := Complex.cos_arg (show (⟨d, -c⟩ : ℂ) ≠ 0 from norm_ne_zero_iff.mp (by rw [hnorm]; norm_num))
    simpa [θ, hnorm] using this
  have hsin : Real.sin θ = -c := by
    have := Complex.sin_arg (⟨d, -c⟩ : ℂ)
    simpa [θ, hnorm] using this
  rcases sq_eq_one_iff.mp hdet_sq with hd1 | hd1
  · refine ⟨false, θ, ?_⟩
    have ha : a = d := by linear_combination -a * h3 + c * h2 + d * hd1
    have hb : b = -c := by linear_combination -b * h3 + d * h2 - c * hd1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hcos, hsin, ha, hb]
  · refine ⟨true, θ, ?_⟩
    have ha : a = -d := by linear_combination -a * h3 + c * h2 + d * hd1
    have hb : b = c := by linear_combination -b * h3 + d * h2 - c * hd1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hcos, hsin, ha, hb]

/-- Real Iwasawa decomposition for `GL₂⁺(ℝ)` (`DownLift.lean`): every `h ∈ GL (Fin 2) ℝ` with
`0 < det h` decomposes as `scalar(λ) · aff(y, x) · rot(θ)` with `λ > 0`, `y > 0`. -/
theorem iwasawa_gl2_pos (h : GL (Fin 2) ℝ) (hh : 0 < h.val.det) :
    ∃ (lam y : ℝ) (x θ : ℝ), 0 < lam ∧ 0 < y ∧
      h.val = !![lam, 0; 0, lam] * !![y, x; 0, 1] *
        !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] := by
  set a := h.val 0 0
  set b := h.val 0 1
  set c := h.val 1 0
  set d := h.val 1 1
  have hdet : a * d - b * c = h.val.det := (Matrix.det_fin_two h.val).symm
  have hcd_pos : 0 < c ^ 2 + d ^ 2 := by
    by_contra hle
    push Not at hle
    have hc0 : c = 0 := by nlinarith [sq_nonneg c, sq_nonneg d]
    have hd0 : d = 0 := by nlinarith [sq_nonneg c, sq_nonneg d]
    rw [hc0, hd0] at hdet
    linarith
  set r := Real.sqrt (c ^ 2 + d ^ 2)
  have hr : 0 < r := Real.sqrt_pos.mpr hcd_pos
  have hr2 : r ^ 2 = c ^ 2 + d ^ 2 := Real.sq_sqrt hcd_pos.le
  set z : ℂ := ⟨d / r, -c / r⟩
  have hz_norm : ‖z‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_apply]
    have hsq : (d / r) * (d / r) + (-c / r) * (-c / r) = 1 := by
      have hr0 : r ≠ 0 := hr.ne'
      field_simp [hr0]
      linarith
    rw [hsq, Real.sqrt_one]
  set θ := Complex.arg z
  have hcos : Real.cos θ = d / r := by
    have := Complex.cos_arg (norm_ne_zero_iff.mp (by rw [hz_norm]; norm_num))
    simpa [θ, hz_norm, z] using this
  have hsin : Real.sin θ = -c / r := by
    have := Complex.sin_arg z
    simpa [θ, hz_norm, z] using this
  refine ⟨r, h.val.det / r ^ 2, (a * c + b * d) / r ^ 2, θ, hr, div_pos hh (sq_pos_of_pos hr), ?_⟩
  ext i j
  have hr0 : r ≠ 0 := hr.ne'
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hcos, hsin]
  · change a = _; field_simp [hr0]; linear_combination a * hr2 + d * hdet
  · change b = _; field_simp [hr0]; linear_combination b * hr2 - c * hdet
  · change c = _; field_simp [hr0]
  · change d = _; field_simp [hr0]

/-- Finite-dimensionality from finite-codimension kernel (`FinOfKer.lean`): if `P ⊆ V` is mapped
by finitely many linear functionals `L : ι → V →ₗ[ℂ] ℂ` with `P ∩ ⋂ ker(L i) ⊆ Q` and `span Q`
finite-dimensional, then `span P` is finite-dimensional! -/
theorem fin_of_ker {V ι : Type*} [AddCommGroup V] [Module ℂ V] [Finite ι]
    (P Q : Set V) (h0 : (0 : V) ∈ P) (hadd : ∀ x ∈ P, ∀ y ∈ P, x + y ∈ P)
    (hsmul : ∀ (c : ℂ), ∀ x ∈ P, c • x ∈ P) (L : ι → V →ₗ[ℂ] ℂ)
    (hker : ∀ x ∈ P, (∀ i, L i x = 0) → x ∈ Q)
    (hQ : FiniteDimensional ℂ (Submodule.span ℂ Q)) :
    FiniteDimensional ℂ (Submodule.span ℂ P) := by
  let SP : Submodule ℂ V :=
    { carrier := P
      zero_mem' := h0
      add_mem' := fun hx hy => hadd _ hx _ hy
      smul_mem' := fun c _ hx => hsmul c _ hx }
  have hSP : Submodule.span ℂ P = SP := Submodule.span_eq SP
  rw [hSP]
  let Φ : SP →ₗ[ℂ] (ι → ℂ) := LinearMap.pi fun i => (L i).comp SP.subtype
  have hker_fd : FiniteDimensional ℂ (LinearMap.ker Φ) := by
    refine FiniteDimensional.of_injective
      ((SP.subtype.comp (LinearMap.ker Φ).subtype).codRestrict (Submodule.span ℂ Q) fun x => ?_)
      fun x y h => Subtype.ext (Subtype.ext (congrArg (fun u : Submodule.span ℂ Q => u.1) h))
    refine Submodule.subset_span (hker x.1.1 x.1.2 fun i => ?_)
    exact congrFun (LinearMap.mem_ker.mp x.2) i
  have hquot_fd : FiniteDimensional ℂ (SP ⧸ LinearMap.ker Φ) :=
    Φ.quotKerEquivRange.symm.finiteDimensional
  exact Module.Finite.of_submodule_quotient (LinearMap.ker Φ)

/-! ### 3.3 Formal Hecke Operators, Eigenform Existence & Minimal-Level Newforms (`ExistsEigenform`, `MinNew`) -/

/-- Formal `p`-th Hecke operator on `q`-expansion sequences `ℕ → K` with nebentypus value `e`
(`ExistsEigenform.lean`). -/
def formalHecke {K : Type*} [Field K] (p : ℕ) (e : K) : Module.End K (ℕ → K) where
  toFun c n := c (p * n) + if p ∣ n then e * c (n / p) else 0
  map_add' c₁ c₂ := by ext n; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' a c := by ext n; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

theorem formalHecke_apply {K : Type*} [Field K] (p : ℕ) (e : K) (c : ℕ → K) (n : ℕ) :
    formalHecke p e c n = c (p * n) + if p ∣ n then e * c (n / p) else 0 := rfl

/-- Distinct prime formal Hecke operators commute (`ExistsEigenform.lean`). -/
theorem formalHecke_comm {K : Type*} [Field K] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (e e' : K) :
    formalHecke p e * formalHecke q e' = formalHecke q e' * formalHecke p e := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  ext c n
  simp only [Module.End.mul_apply, formalHecke_apply]
  have h1 : q ∣ p * n ↔ q ∣ n := hcop.symm.dvd_mul_left
  have h2 : p ∣ q * n ↔ p ∣ n := hcop.dvd_mul_left
  have hmul : q * (p * n) = p * (q * n) := by ring
  by_cases hpn : p ∣ n <;> by_cases hqn : q ∣ n
  · obtain ⟨k, rfl⟩ := hpn
    have hqk : q ∣ k := hcop.symm.dvd_of_dvd_mul_left hqn
    obtain ⟨m, rfl⟩ := hqk
    have hpn' : p ∣ p * (q * m) := dvd_mul_right p (q * m)
    have hq_div : q ∣ p * (q * m) / p := by
      rw [Nat.mul_div_cancel_left _ hp.pos]; exact dvd_mul_right q m
    have hp_div : p ∣ p * (q * m) / q := by
      rw [show p * (q * m) = q * (p * m) by ring, Nat.mul_div_cancel_left _ hq.pos]
      exact dvd_mul_right p m
    simp only [h1, h2, hpn', hqn, hq_div, hp_div, ↓reduceIte, hmul]
    have e1 : p * (q * m) / p = q * m := Nat.mul_div_cancel_left _ hp.pos
    have e2 : p * (q * m) / q = p * m := by
      rw [show p * (q * m) = q * (p * m) by ring, Nat.mul_div_cancel_left _ hq.pos]
    have e5 : q * m / q = m := Nat.mul_div_cancel_left _ hq.pos
    have e6 : p * m / p = m := Nat.mul_div_cancel_left _ hp.pos
    have e7 : p * (p * (q * m)) / q = p * (p * m) := by
      rw [show p * (p * (q * m)) = q * (p * (p * m)) by ring, Nat.mul_div_cancel_left _ hq.pos]
    have e8 : q * (p * (q * m)) / p = q * (q * m) := by
      rw [show q * (p * (q * m)) = p * (q * (q * m)) by ring, Nat.mul_div_cancel_left _ hp.pos]
    rw [e1, e2, e5, e6, e7, e8]
    ring
  · have hq_div : ¬ q ∣ n / p := fun h => hqn (dvd_trans h (Nat.div_dvd_of_dvd hpn))
    simp only [h1, h2, hpn, hqn, hq_div, ↓reduceIte, hmul, add_zero]
    rw [show q * n / p = q * (n / p) from Nat.mul_div_assoc q hpn]
  · have hp_div : ¬ p ∣ n / q := fun h => hpn (dvd_trans h (Nat.div_dvd_of_dvd hqn))
    simp only [h1, h2, hpn, hqn, hp_div, ↓reduceIte, hmul, add_zero]
    rw [show p * n / q = p * (n / q) from Nat.mul_div_assoc p hqn]
  · simp only [h1, h2, hpn, hqn, ↓reduceIte, hmul, add_zero]

/-- If a `q`-expansion sequence `c` satisfies `c 0 = 0`, `c 1 = 0`, and is a simultaneous
eigenvector of `formalHecke p (e p)` for all primes `p`, then `c = 0` (`ExistsEigenform.lean`). -/
theorem eq_zero_of_formalHecke_eig {K : Type*} [Field K] (e b : Nat.Primes → K) (c : ℕ → K)
    (h0 : c 0 = 0) (h1 : c 1 = 0)
    (heig : ∀ p : Nat.Primes, formalHecke p.1 (e p) c = b p • c) : c = 0 := by
  funext n
  show c n = 0
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | k
    · exact h0
    · exact h1
    · obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : k + 2 ≠ 1)
      obtain ⟨m, hm⟩ := hpd
      have hm_lt : m < k + 2 := by
        have hp2 : 2 ≤ p := hp.two_le
        have hmpos : 0 < m := by
          rcases Nat.eq_zero_or_pos m with rfl | h; · simp at hm
          · exact h
        nlinarith
      have hact := congrFun (heig ⟨p, hp⟩) m
      simp only [formalHecke_apply, Pi.smul_apply, smul_eq_mul] at hact
      rw [← hm, ih m hm_lt, mul_zero] at hact
      by_cases hpm : p ∣ m
      · rw [if_pos hpm, ih (m / p) (lt_of_le_of_lt (Nat.div_le_self m p) hm_lt), mul_zero,
          add_zero] at hact
        exact hact
      · rw [if_neg hpm, add_zero] at hact
        exact hact

/-- Simultaneous Hecke eigenform existence on any finite-dimensional Hecke-stable space of
`q`-expansions (`ExistsEigenform.lean` via `simEig`!). -/
theorem exists_simultaneous_hecke_eigenvector {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (Φ : V →ₗ[ℂ] (ℕ → ℂ)) (hΦ_inj : Function.Injective Φ)
    (hΦ0 : ∀ f, Φ f 0 = 0) (e : Nat.Primes → ℂ)
    (T : Nat.Primes → Module.End ℂ V)
    (hT : ∀ p f, Φ (T p f) = formalHecke p.1 (e p) (Φ f))
    (f₀ : V) (hf₀ : f₀ ≠ 0) (a : ℕ → ℂ) :
    ∃ g : V, Φ g 1 = 1 ∧ (∀ p : Nat.Primes, T p g = Φ g p.1 • g) ∧
      ∀ p : Nat.Primes, T p f₀ = a p.1 • f₀ → Φ g p.1 = a p.1 := by
  have hcomm : ∀ p q : Nat.Primes, T p * T q = T q * T p := fun p q => by
    by_cases hpq : p = q
    · subst hpq; rfl
    · ext f
      apply hΦ_inj
      simp only [Module.End.mul_apply, hT]
      exact congrFun (congrArg DFunLike.coe
        (formalHecke_comm p.2 q.2 (fun h => hpq (Subtype.ext h)) (e p) (e q))) (Φ f)
  let U : Submodule ℂ V := ⨅ (p : Nat.Primes) (_ : T p f₀ = a p.1 • f₀), (T p).eigenspace (a p.1)
  have hf₀U : f₀ ∈ U := by
    simp only [U, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
    intro p hp; exact hp
  have hU_ne : U ≠ ⊥ := fun h => hf₀ (by rw [h] at hf₀U; exact hf₀U)
  have hU_inv : ∀ p : Nat.Primes, ∀ x ∈ U, T p x ∈ U := by
    intro p x hx
    simp only [U, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hx ⊢
    intro q hq
    have h1 := LinearMap.congr_fun (hcomm q p) x
    simp only [Module.End.mul_apply] at h1
    rw [h1, hx q hq, map_smul]
  obtain ⟨v, hvU, hv0, hveig⟩ := simEig T hcomm (Module.finrank ℂ U) U rfl hU_ne hU_inv
  choose b hb using hveig
  have hv1 : Φ v 1 ≠ 0 := by
    intro h1
    have hzero : Φ v = 0 := eq_zero_of_formalHecke_eig e b (Φ v) (hΦ0 v) h1 fun p => by
      rw [← hT p v, hb p, map_smul]
    exact hv0 (hΦ_inj (hzero.trans (map_zero Φ).symm))
  refine ⟨(Φ v 1)⁻¹ • v, ?_, ?_, ?_⟩
  · simp [hv1]
  · intro p
    have hp1 := congrFun (hT p v) 1
    rw [hb p, map_smul, Pi.smul_apply, smul_eq_mul, formalHecke_apply, mul_one,
      if_neg (Nat.not_dvd_of_pos_of_lt Nat.one_pos p.2.one_lt), add_zero] at hp1
    have hbp : b p = (Φ v 1)⁻¹ * Φ v p.1 := by
      have : b p * Φ v 1 = Φ v p.1 := hp1
      rw [← this, mul_comm (b p), inv_mul_cancel_left₀ hv1]
    simp only [map_smul, hb p, Pi.smul_apply, smul_eq_mul, hbp]
    rw [smul_smul, smul_smul, mul_comm ((Φ v 1)⁻¹)]
  · intro p hp
    have hv_p : T p v = a p.1 • v := by
      simp only [U, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at hvU
      exact hvU p hp
    have hp1 := congrFun (hT p v) 1
    rw [hv_p, map_smul, Pi.smul_apply, smul_eq_mul, formalHecke_apply, mul_one,
      if_neg (Nat.not_dvd_of_pos_of_lt Nat.one_pos p.2.one_lt), add_zero] at hp1
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, ← hp1]
    field_simp [hv1]

open Classical in
/-- General double-coset Hecke operator formula (`UOfSat.lean`): if `K` is commensurated and `h`
is the indicator of `K g K`, then `heckeVec ρ K h x = ∑_{c ∈ K g K / K} ρ c x`. -/
theorem hecke_eq_dc {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (K : Subgroup G) (g : G) (x : V)
    (hx : ∀ k ∈ K, ρ k x = x) {S : Finset G}
    (hcov : ∀ u : G, (∃ a ∈ K, ∃ b ∈ K, u = a * g * b) ↔ ∃ s ∈ S, s⁻¹ * u ∈ K)
    (hdisj : ∀ s₁ ∈ S, ∀ s₂ ∈ S, s₁⁻¹ * s₂ ∈ K → s₁ = s₂) :
    heckeVec ρ K (fun u => if ∃ a ∈ K, ∃ b ∈ K, u = a * g * b then (1 : ℂ) else 0) x =
      ∑ s ∈ S, ρ s x := by
  classical
  unfold heckeVec
  let f : G ⧸ K → V := fun c =>
    (if ∃ a ∈ K, ∃ b ∈ K, c.out = a * g * b then (1 : ℂ) else 0) • ρ c.out x
  have hwell : ∀ s : G, ∀ q : G ⧸ K, q = (s : G ⧸ K) → ρ q.out x = ρ s x := by
    intro s q hq
    have hmem : s⁻¹ * q.out ∈ K := by
      have : (q.out : G ⧸ K) = (s : G ⧸ K) := by rw [QuotientGroup.out_eq', hq]
      exact QuotientGroup.eq.mp this.symm
    have hmul : q.out = s * (s⁻¹ * q.out) := by group
    rw [hmul, map_mul, Module.End.mul_apply, hx _ hmem]
  have hsupp : Function.support f ⊆ (S.image (fun s : G => (s : G ⧸ K)) : Set (G ⧸ K)) := by
    intro q hq
    simp only [Function.mem_support, f] at hq
    have hcond : ∃ a ∈ K, ∃ b ∈ K, q.out = a * g * b := by
      by_contra h
      exact hq (by simp [h])
    obtain ⟨s, hs, hsq⟩ := (hcov q.out).mp hcond
    refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨s, hs, ?_⟩)
    rw [← QuotientGroup.out_eq' q]
    exact QuotientGroup.eq.mpr hsq
  rw [finsum_eq_sum_of_support_subset f hsupp, Finset.sum_image]
  · refine Finset.sum_congr rfl fun s hs => ?_
    simp only [f]
    have hcond : ∃ a ∈ K, ∃ b ∈ K, (s : G ⧸ K).out = a * g * b := by
      rw [hcov]
      refine ⟨s, hs, ?_⟩
      exact QuotientGroup.eq.mp (QuotientGroup.out_eq' (s : G ⧸ K)).symm
    rw [if_pos hcond, one_smul, hwell s (s : G ⧸ K) rfl]
  · intro s₁ hs₁ s₂ hs₂ heq
    exact hdisj s₁ hs₁ s₂ hs₂ (QuotientGroup.eq.mp heq)

end CapelliSl2AndHecke

/-! ## Section 4: Admissible Local Components, Satake Pairing, CM Conjugation & Quadratic Base Change -/

section AdmissibleSatakeAndBaseChange

/-! ### 4.1 Finite `K`-Type Orbits & Annihilator Decomposition (`FinCompR.lean`) -/

/-- Group-ring orbit map `ℂ[K] →ₗ[ℂ] V` sending `c ↦ ∑ c(k) κ(k) x` (`FinCompR.lean`). -/
def kOrbit {K V : Type*} [Group K] [AddCommGroup V] [Module ℂ V]
    (κ : Representation ℂ K V) (x : V) : (K →₀ ℂ) →ₗ[ℂ] V :=
  Finsupp.linearCombination ℂ fun k => κ k x

theorem kOrbit_comm {K V : Type*} [Group K] [AddCommGroup V] [Module ℂ V]
    (κ : Representation ℂ K V) (T : Module.End ℂ V)
    (hT : ∀ k x, T (κ k x) = κ k (T x)) (x : V) (c : K →₀ ℂ) :
    kOrbit κ (T x) c = T (kOrbit κ x c) := by
  simp only [kOrbit, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, hT]

theorem kOrbit_act {K V : Type*} [Group K] [AddCommGroup V] [Module ℂ V]
    (κ : Representation ℂ K V) (x : V) (k : K) (c : K →₀ ℂ) :
    kOrbit κ x (c.mapDomain (k * ·)) = κ k (kOrbit κ x c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c c' h h' => rw [Finsupp.mapDomain_add, map_add, map_add, map_add, h, h']
  | single a b => simp [kOrbit]

/-- Annihilator subspace of vectors whose `ℂ[K]`-annihilator contains that of `φ` (`FinCompR.lean`). -/
def annPart {K V : Type*} [Group K] [AddCommGroup V] [Module ℂ V]
    (κ : Representation ℂ K V) (φ : V) : Submodule ℂ V where
  carrier := {x | ∀ c, kOrbit κ φ c = 0 → kOrbit κ x c = 0}
  add_mem' := fun {x y} hx hy c hc => by
    have : kOrbit κ (x + y) c = kOrbit κ x c + kOrbit κ y c := by
      simp only [kOrbit, Finsupp.linearCombination_apply, Finsupp.sum, map_add, smul_add,
        Finset.sum_add_distrib]
    rw [this, hx c hc, hy c hc, add_zero]
  zero_mem' := fun c _ => by simp [kOrbit, Finsupp.linearCombination_apply, Finsupp.sum]
  smul_mem' := fun a x hx c hc => by
    have := kOrbit_comm κ (a • (1 : Module.End ℂ V)) (fun k x => by simp) x c
    simpa [hx c hc] using this

/-- Every `K`-finite vector `φ` determines a finite-dimensional matrix `K`-type `ξ : K →* Mat_d(ℂ)`
intertwining every vector in `annPart κ φ` (`FinCompR.lean`). -/
theorem exists_kType {K V : Type*} [Group K] [AddCommGroup V] [Module ℂ V]
    (κ : Representation ℂ K V) (φ : V)
    (hφ : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => κ k φ))) :
    ∃ (d : ℕ) (ξ : K →* Matrix (Fin d) (Fin d) ℂ), ∀ x ∈ annPart κ φ,
      ∃ f : (Fin d → ℂ) →ₗ[ℂ] V,
        (∀ k v, f (ξ k *ᵥ v) = κ k (f v)) ∧ x ∈ LinearMap.range f ∧ ∀ v, ∃ c, f v = kOrbit κ x c := by
  have hO : ∀ k, ∀ y ∈ LinearMap.range (kOrbit κ φ), κ k y ∈ LinearMap.range (kOrbit κ φ) := by
    rintro k _ ⟨c, rfl⟩
    exact ⟨_, kOrbit_act κ φ k c⟩
  have : FiniteDimensional ℂ (LinearMap.range (kOrbit κ φ)) := by
    rw [kOrbit, Finsupp.range_linearCombination]; exact hφ
  let b := Module.finBasis ℂ (LinearMap.range (kOrbit κ φ))
  obtain ⟨s, hs⟩ := (kOrbit κ φ).rangeRestrict.exists_rightInverse_of_surjective
    (LinearMap.range_rangeRestrict _)
  let subκ : K →* Module.End ℂ (LinearMap.range (kOrbit κ φ)) :=
    { toFun := fun k => (κ k).restrict (hO k)
      map_one' := by ext ⟨y, hy⟩; simp
      map_mul' := fun k₁ k₂ => by ext ⟨y, hy⟩; simp }
  refine ⟨_, (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp subκ, fun x hx => ?_⟩
  have key : ∀ c, kOrbit κ x (s ((kOrbit κ φ).rangeRestrict c)) = kOrbit κ x c := fun c => by
    rw [← sub_eq_zero, ← map_sub]
    refine hx _ ?_
    rw [map_sub, sub_eq_zero]
    exact congrArg Subtype.val (LinearMap.congr_fun hs ((kOrbit κ φ).rangeRestrict c))
  refine ⟨kOrbit κ x ∘ₗ s ∘ₗ b.equivFun.symm.toLinearMap, fun k v => ?_,
    ⟨b.equivFun ((kOrbit κ φ).rangeRestrict (Finsupp.single 1 1)), ?_⟩, fun v => ⟨_, rfl⟩⟩
  · obtain ⟨y, rfl⟩ := b.equivFun.surjective v
    obtain ⟨c, rfl⟩ := (kOrbit κ φ).surjective_rangeRestrict y
    have h1 : (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp subκ k *ᵥ
          b.equivFun ((kOrbit κ φ).rangeRestrict c) =
        b.equivFun ((kOrbit κ φ).rangeRestrict (c.mapDomain (k * ·))) := by
      have h2 : (kOrbit κ φ).rangeRestrict (c.mapDomain (k * ·)) =
          subκ k ((kOrbit κ φ).rangeRestrict c) := Subtype.ext (kOrbit_act κ φ k c)
      rw [h2]
      exact LinearMap.toMatrix_mulVec_repr b b _ _
    rw [h1]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, key, kOrbit_act]
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, key]
    simp [kOrbit]

/-! ### 4.2 Self-Adjoint Hecke Pairing & Algebraic Satake Conjugation (`SatOfPol`, `EventuallyNotMem`, `ExistsPrimeNotMem`) -/

/-- Self-adjointness of `heckeVec` under an equivariant bilinear pairing `β` with involution `θ`
(`SatOfPol.lean`). -/
theorem pair_heckeVec {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ G V} {ρ : Representation ℂ G W}
    {K : Subgroup G} {h : G → ℂ} {x : V} {y : W}
    (hfinV : (Function.support fun c : G ⧸ K => h c.out • σ c.out x).Finite)
    (hfinW : (Function.support fun c : G ⧸ K => h c.out • ρ c.out y).Finite)
    (hx : x ∈ fixed σ K) (hy : y ∈ fixed ρ K)
    (β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (θ : G ≃* G) (hθ : ∀ k, k ∈ K ↔ θ k ∈ K)
    (hi : ∀ g v w, β (σ (θ g) v) (ρ g w) = β v w)
    (ht : ∀ g, h g ≠ 0 → ∃ a ∈ K, ∃ b ∈ K, ∃ t, θ t⁻¹ = t ∧ g = a * t * b) :
    β (heckeVec σ K h x) y = β x (heckeVec ρ K h y) := by
  have hf := mem_fixed.1 hx
  have hg := mem_fixed.1 hy
  have bi : ∀ a ∈ K, ∀ b ∈ K, ∀ t, β (σ (a * t * b) x) y = β (σ t x) y := fun a ha b hb t => by
    obtain ⟨a, rfl⟩ := θ.surjective a
    rw [map_mul σ, map_mul σ, Module.End.mul_apply, Module.End.mul_apply, hf b hb]
    exact (congrArg (β _) (hg a ((hθ a).2 ha)).symm).trans (hi a _ _)
  have bi' : ∀ a ∈ K, ∀ b ∈ K, ∀ t, β x (ρ (a * t * b) y) = β x (ρ t y) := fun a ha b hb t => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hg b hb]
    exact (congrArg (fun u => β u _) (hf _ ((hθ a).1 ha)).symm).trans (hi a _ _)
  have inv : ∀ t, β (σ (θ t⁻¹) x) y = β x (ρ t y) := fun t => by
    rw [← hi t⁻¹ x (ρ t y)]; simp
  have e1 := (β.flip y).toAddMonoidHom.map_finsum hfinV
  have e2 := (β x).toAddMonoidHom.map_finsum hfinW
  refine e1.trans (Eq.trans (finsum_congr fun c => ?_) e2.symm)
  change β (h c.out • σ c.out x) y = β x (h c.out • ρ c.out y)
  rw [map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  by_cases h0 : h c.out = 0
  · simp [h0]
  obtain ⟨a, ha, b, hb, t, htt, e⟩ := ht _ h0
  congr 1
  rw [e, bi _ ha _ hb, bi' _ ha _ hb, ← inv, htt]

/-- Algebraically normalized Satake parameters `algSat n q B = B.map (q^((n-1)/2) * ·)`
(`CqStmt.lean`, `BcAtt0.lean`, `EventuallyNotMem.lean`). -/
def algSat (n q : ℕ) (B : Multiset ℂˣ) : Multiset ℂ :=
  B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ)

/-- Power functoriality of algebraically normalized Satake parameters (`BcAtt0.lean`). -/
theorem algSat_pow (n q f : ℕ) (B : Multiset ℂˣ) :
    algSat n (q ^ f) (B.map (· ^ f)) = (algSat n q B).map (· ^ f) := by
  simp only [algSat, Multiset.map_map, Function.comp_def]
  refine Multiset.map_congr rfl fun α _ => ?_
  have h : (((q ^ f : ℕ) : ℝ)) ^ (((n : ℝ) - 1) / 2) = ((q : ℝ) ^ (((n : ℝ) - 1) / 2)) ^ f := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q),
      ← Real.rpow_mul (Nat.cast_nonneg q), mul_comm]
  rw [h, mul_pow, Units.val_pow_eq_pow_val, Complex.ofReal_pow]

/-- Conjugate-self-duality of Satake parameters is preserved under any field automorphism
`σ : ℂ ≃+* ℂ` (`EventuallyNotMem.lean`). -/
theorem dual_conj {n q : ℕ} (hn : 1 ≤ n) (hq : q ≠ 0) (σ : ℂ ≃+* ℂ)
    {B B₁ B' B₁' : Multiset ℂˣ} {z z' : ℂˣ} (hz : (z' : ℂ) = σ z)
    (h : B₁.map (·⁻¹) = B.map (· * z⁻¹))
    (e : algSat n q B' = (algSat n q B).map σ)
    (e₁ : algSat n q B₁' = (algSat n q B₁).map σ) :
    B₁'.map (·⁻¹) = B'.map (· * z'⁻¹) := by
  have hc : (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) *
      (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) = (q : ℂ) ^ (n - 1) := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add (by positivity), add_halves,
      ← Nat.cast_one (R := ℝ), ← Nat.cast_sub hn, Real.rpow_natCast]
    push_cast
    rfl
  have h0 : (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos (by positivity) _).ne'
  simp only [algSat] at e e₁
  generalize (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) = c at *
  have hs : σ c * σ c = c * c := by rw [← map_mul, hc, map_pow, map_natCast]
  have h1 : σ c ≠ 0 := (map_ne_zero σ).2 h0
  apply Multiset.map_injective (f := fun x : ℂˣ => c⁻¹ * (x : ℂ))
    (fun x y hxy => Units.ext (mul_left_cancel₀ (inv_ne_zero h0) hxy))
  have k1 := congrArg (Multiset.map fun x : ℂ => x⁻¹) e₁
  have k2 := congrArg (Multiset.map fun x : ℂ => (c * c)⁻¹ * x * (σ z)⁻¹) e
  have k3 := congrArg (Multiset.map fun x : ℂˣ => σ (c⁻¹ * (x : ℂ))) h
  simp only [Multiset.map_map, Function.comp_def] at k1 k2 k3 ⊢
  refine (Multiset.map_congr rfl fun x _ => ?_).trans (k1.trans ((Multiset.map_congr rfl fun x _ => ?_).trans
    (k3.trans ((Multiset.map_congr rfl fun x _ => ?_).trans (k2.symm.trans
      (Multiset.map_congr rfl fun x _ => ?_))))))
  · simp [mul_comm]
  · simp [mul_comm]
  · rw [← hs]
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
    field_simp
  · simp only [Units.val_mul, Units.val_inv_eq_inv_val, hz]
    field_simp

/-- Infinitesimal character multiset `infOf m = {m i + (n - 1) / 2}` associated to integer
weights `m : Fin n → ℤ` (`CqStmt.lean`). -/
def infOf {n : ℕ} (m : Fin n → ℤ) : Multiset ℂ :=
  Finset.univ.val.map fun i : Fin n => (m i : ℂ) + ((n : ℂ) - 1) / 2

/-- Regular algebraicity of a `CuspSub K n` follows immediately from `HasInfChar τ (infOf m)`
with strictly antitone `m` (`EventuallyNotMem.lean`, `ExistsPrimeNotMem.lean`). -/
theorem regAlg_of_infOf {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {n : ℕ}
    {m : Fin n → ℤ} (hm : StrictAnti m) {π : CuspSub K n}
    (hinf : ∀ τ : K →+* ℂ, π.HasInfChar τ (infOf m)) : (CG.mk π).IsRegAlg := by
  rw [CG.isRegAlg_iff]
  intro τ
  rw [CG.HasInfChar.infChar_eq (π := CG.mk π) (hinf τ)]
  refine ⟨Finset.univ.nodup.map fun i j e => hm.injective ?_, fun z hz => ?_⟩
  · exact_mod_cast add_right_cancel e
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
    exact ⟨m i, rfl⟩

/-- Weight-sum duality `wt' = -wt` for Hodge-Tate weights attached to a symmetric weight tuple
`m i + m i.rev = wt` (`ExistsPrimeNotMem.lean`). -/
theorem wt_eq {n : ℕ} (hn : 1 ≤ n) {m : Fin n → ℤ} {wt wt' : ℤ}
    (hm : ∀ i, m i + m i.rev = wt) {H : Multiset ℤ}
    (h1 : H.map (fun k : ℤ => (k : ℂ)) = (infOf m).map fun z => ((n : ℂ) - 1) / 2 - z)
    (h2 : H = H.map (wt' - ·)) : wt' = -wt := by
  have e : H = Finset.univ.val.map fun i => -m i := by
    refine Multiset.map_injective (Int.cast_injective (α := ℂ)) ?_
    rw [h1, infOf, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun i _ => ?_
    simp
  have s1 := congrArg Multiset.sum h2
  rw [e, Multiset.map_map] at s1
  change ∑ i, -m i = ∑ i, (wt' - -m i) at s1
  have s2 : ∑ i : Fin n, (m i + m i.rev) = ∑ _i : Fin n, wt := Finset.sum_congr rfl fun i _ => hm i
  have s3 : ∑ i : Fin n, m i.rev = ∑ i, m i := Equiv.sum_comp Fin.revPerm m
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, s3] at s1 s2
  have hn' : (n : ℤ) ≠ 0 := by omega
  refine mul_left_cancel₀ hn' ?_
  linarith

/-! ### 4.3 CM Complex Conjugation on Finite Places & Quadratic Base-Change Compatibility (`QuadBCwOfQuadBC0`, `BcStmt`, `BcAtt0`, `ConjAlgebraMap`, `WeakEx`, `QuadBC`) -/

/-- Complex conjugation on finite places of a CM field `E`: pullback along `IsCMField.complexConj E`
(`ConjAlgebraMap.lean`). -/
def cPl {E : Type*} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    HeightOneSpectrum (𝓞 E) where
  asIdeal := w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv).toRingHom
  isPrime := w.isPrime.comap _
  ne_bot := fun h => w.ne_bot <| by
    let e := RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv
    have h1 : Ideal.map e.toRingHom (w.asIdeal.comap e.toRingHom) = ⊥ := by
      rw [h, Ideal.map_bot]
    rwa [Ideal.map_comap_of_surjective e.toRingHom e.surjective] at h1

theorem cPl_asIdeal {E : Type*} [Field E] [NumberField E] [IsCMField E]
    (w : HeightOneSpectrum (𝓞 E)) :
    (cPl w).asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv).toRingHom :=
  rfl

theorem cPl_injective {E : Type*} [Field E] [NumberField E] [IsCMField E] :
    Function.Injective (cPl (E := E)) := fun w₁ w₂ h => by
  let e := RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv
  have heq : (cPl w₁).asIdeal = (cPl w₂).asIdeal := congrArg HeightOneSpectrum.asIdeal h
  apply HeightOneSpectrum.ext
  have hmap := congrArg (Ideal.map e.toRingHom) heq
  rw [cPl_asIdeal, cPl_asIdeal] at hmap
  rwa [Ideal.map_comap_of_surjective e.toRingHom e.surjective,
    Ideal.map_comap_of_surjective e.toRingHom e.surjective] at hmap

/-- Complex conjugation preserves residue-field norm `normV (cPl w) = normV w`
(`ConjAlgebraMap.lean`, `EventuallyNotMem.lean`). -/
theorem normV_cPl {E : Type*} [Field E] [NumberField E] [IsCMField E]
    (w : HeightOneSpectrum (𝓞 E)) : normV (cPl w) = normV w := by
  rw [normV_eq_absNorm, normV_eq_absNorm, Ideal.absNorm_apply, Ideal.absNorm_apply,
    Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  refine (Nat.card_congr (Ideal.quotientEquiv _ _
    (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv).symm ?_).toEquiv).symm
  rw [cPl_asIdeal]
  exact (Ideal.map_symm _).symm

/-- Complex conjugation on a CM field `E` fixes any totally real subfield `F ↪ E`
(`ConjAlgebraMap.lean`). -/
theorem conj_algebraMap {F E : Type*} [Field F] [NumberField F] [IsTotallyReal F]
    [Field E] [NumberField E] [IsCMField E] [Algebra F E] (x : F) :
    IsCMField.complexConj E (algebraMap F E x) = algebraMap F E x := by
  rw [IsCMField.complexConj_eq_self_iff, mem_maximalRealSubfield_iff]
  intro φ
  have h := IsTotallyReal.complexEmbedding_isReal (φ.comp (algebraMap F E))
  exact RingHom.congr_fun h x

/-- Concrete totally real automorphic datum interface: a cuspidal representation over a totally
real field `F` together with its archimedean infinitesimal characters and unramified Satake
parameters (directly mirroring `Stage13GL_BernoulliAndWeylAlg.CuspSub` for `[IsTotallyReal F]`). -/
structure TRCuspRep (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) where
  HasInfChar : InfinitePlace F → Multiset ℂ → Prop
  HasSat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop
  hasSat_unique : ∀ {v B B'}, HasSat v B → HasSat v B' → B = B'
  IsRegAlg : Prop
  regAlg_spec : IsRegAlg → ∀ v : InfinitePlace F,
    ∃ m : Multiset ℂ, HasInfChar v m ∧ m.Nodup ∧
      ∀ z ∈ m, ∃ k : ℤ, z = (k : ℂ) + ((a : ℂ) - 1) / 2

/-- Weak base-change compatibility `IsBC0 π P` from a totally real `GL_a(𝔸_F)` cuspidal
representation `π` to a concrete totally complex `P : CuspSub E a` from
`Stage13GL_BernoulliAndWeylAlg` (`QuadBCwOfQuadBaseChange.lean`). -/
structure IsBC0 {F E : Type} [Field F] [NumberField F] [IsTotallyReal F]
    [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E] {a : ℕ}
    (π : TRCuspRep F a) (P : CuspSub E a) : Prop where
  inf : ∀ (τ : E →+* ℂ) (m : Multiset ℂ),
    π.HasInfChar (InfinitePlace.mk (τ.comp (algebraMap F E))) m → P.HasInfChar τ m
  unr : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
    ∀ v : HeightOneSpectrum (𝓞 F), v.asIdeal = w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) →
      ∀ f : ℕ, normV w = normV v ^ f → ∃ B, π.HasSat v B ∧ (CG.mk P).HasSat w (B.map (· ^ f))

/-- Galois attachment `AttR` over totally real `F` (`BcStmt.lean`). -/
def AttR {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω]
    {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ}
    (r : G F Ω →* GL (Fin n) (Qbar l)) (π : TRCuspRep F n) : Prop :=
  IsSSRep r ∧ ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
    ∃ B, π.HasSat v B ∧ FrobEig ι r v (algSat n (normV v) B)

/-- Galois attachment `AttC` over totally complex `E` onto concrete `CuspSub E n` (`BcStmt.lean`). -/
def AttC {E Ω : Type} [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra E Ω]
    {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ}
    (r : G E Ω →* GL (Fin n) (Qbar l)) (P : CuspSub E n) : Prop :=
  IsSSRep r ∧ ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
    ∃ B, (CG.mk P).HasSat w B ∧ FrobEig ι r w (algSat n (normV w) B)

/-- Weak base change `IsBC0 π P` preserves regular algebraicity and Galois attachment upon
restriction `r|_{G_E}` (`BcAtt0.lean` — 0 external parameters!). -/
theorem bcAtt0 (F E Ω : Type) [Field F] [NumberField F] [IsTotallyReal F]
    [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra F E] [Algebra F Ω]
    [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure F Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) (π : TRCuspRep F n) (P : CuspSub E n)
    (hbc : IsBC0 π P) :
    (π.IsRegAlg → (CG.mk P).IsRegAlg) ∧
    (AttR ι r π → IsSSRep (r.comp (res F Ω E)) → AttC ι (r.comp (res F Ω E)) P) := by
  refine ⟨fun hreg => (CG.isRegAlg_iff _).2 fun τ => ?_, fun hatt hss => ⟨hss, ?_⟩⟩
  · obtain ⟨m, hm, hnd, hz⟩ := π.regAlg_spec hreg (InfinitePlace.mk (τ.comp (algebraMap F E)))
    rw [CG.HasInfChar.infChar_eq (π := CG.mk P) (hbc.inf τ m hm)]
    exact ⟨hnd, hz⟩
  · filter_upwards [hbc.unr, (tendsto_under' (K := F) (K' := E)).eventually hatt.2] with w h1 h2
    obtain ⟨B, hB, hP⟩ := h1 (w.under (𝓞 F)) rfl _ (normV_under (K := F) w)
    obtain ⟨B', hB', hF⟩ := h2
    obtain rfl := π.hasSat_unique hB hB'
    refine ⟨_, hP, ?_⟩
    have h3 := frobenius_power_compatibility F E Ω l ι w _ (normV_under (K := F) w) n r _ hF
    rw [← algSat_pow, ← normV_under] at h3
    exact h3

/-- Weak base change `IsBC0 π P` to a CM field `E` forces `P` to be conjugate-invariant at almost
all finite places `w` (`ConjAlgebraMap.lean` — 0 external parameters!). -/
theorem bcConj0 (F E : Type) [Field F] [NumberField F] [IsTotallyReal F]
    [Field E] [NumberField E] [IsCMField E] [Algebra F E] (n : ℕ)
    (π : TRCuspRep F n) (P : CuspSub E n) (h : IsBC0 π P) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
      ∃ B, (CG.mk P).HasSat w B ∧ (CG.mk P).HasSat (cPl w) B := by
  have h1 := h.unr
  have h2 := (cPl_injective (E := E)).tendsto_cofinite.eventually h1
  filter_upwards [h1, h2] with w a b
  obtain ⟨B, hB, hP⟩ := a (w.under (𝓞 F)) rfl _ (normV_under w)
  obtain ⟨B', hB', hP'⟩ := b (w.under (𝓞 F)) (by
    rw [cPl_asIdeal]
    ext x
    have e2 : RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv
        (algebraMap (𝓞 F) (𝓞 E) x) = algebraMap (𝓞 F) (𝓞 E) x :=
      RingOfIntegers.ext (conj_algebraMap (x : F))
    rw [Ideal.mem_comap, Ideal.mem_comap]
    change _ ↔ RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv
      (algebraMap (𝓞 F) (𝓞 E) x) ∈ w.asIdeal
    rw [e2]
    rfl) _ ((normV_cPl w).trans (normV_under w))
  obtain rfl := π.hasSat_unique hB hB'
  exact ⟨_, hP, hP'⟩

/-- No number field can be both totally real and totally complex (`WeakEx.lean`). -/
theorem not_totallyReal_and_totallyComplex (F : Type*) [Field F] [NumberField F]
    (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)

/-- Canonical weak quadratic base-change predicate `QuadBC0` parameterized by a quadratic-twist
relation `IsQuadTwist` (`QuadBC0OfQuadBaseChange.lean`). -/
def QuadBC0
    (IsQuadTwist : ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyReal F]
      [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E] {a : ℕ},
      TRCuspRep F a → Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
    [IsTotallyComplex E] [Algebra F E], Module.finrank F E = 2 →
    ∀ (a : ℕ) [Fact (a = 2)], 1 ≤ a → ∀ π : TRCuspRep F a, π.IsRegAlg →
      IsQuadTwist F E π ∨ ∃ P : CuspSub E a, IsBC0 π P

/-- Upgraded quadratic base-change predicate `IsBCw` adding split-place local compatibility
(`QuadBCwOfQuadBaseChange.lean`). -/
structure IsBCw {F E : Type} [Field F] [NumberField F] [IsTotallyReal F]
    [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E] {a : ℕ}
    (Polarized : TRCuspRep F a → Prop)
    (SplitIso : TRCuspRep F a → CuspSub E a → Prop)
    (π : TRCuspRep F a) (P : CuspSub E a) : Prop extends IsBC0 π P where
  split : π.IsRegAlg → Polarized π → SplitIso π P

/-- Upgraded quadratic base-change statement `QuadBCw` (`QuadBCwOfQuadBaseChange.lean`). -/
def QuadBCw
    (IsQuadTwist : ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyReal F]
      [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E] {a : ℕ},
      TRCuspRep F a → Prop)
    (Polarized : ∀ {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ},
      TRCuspRep F a → Prop)
    (SplitIso : ∀ {F E : Type} [Field F] [NumberField F] [IsTotallyReal F]
      [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E] {a : ℕ},
      TRCuspRep F a → CuspSub E a → Prop) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E]
    [IsTotallyComplex E] [Algebra F E], Module.finrank F E = 2 →
    ∀ (a : ℕ) [Fact (a = 2)], 1 ≤ a → ∀ π : TRCuspRep F a, π.IsRegAlg →
      IsQuadTwist F E π ∨ ∃ P : CuspSub E a, IsBCw Polarized SplitIso π P

/-- Upgrading weak quadratic base change `QuadBC0` to split-compatible `QuadBCw` using
CM extension classification `IsCMField.ofCMExtension` and split-place compatibility `hSplit`
(`QuadBCwOfQuadBC0.lean`). -/
theorem quadBCw_of_quadBC0
    (IsQuadTwist : ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyReal F]
      [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E] {a : ℕ},
      TRCuspRep F a → Prop)
    (Polarized : ∀ {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ},
      TRCuspRep F a → Prop)
    (SplitIso : ∀ {F E : Type} [Field F] [NumberField F] [IsTotallyReal F]
      [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E] {a : ℕ},
      TRCuspRep F a → CuspSub E a → Prop)
    (hSplit : ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyReal F]
      [Field E] [NumberField E] [IsCMField E] [Algebra F E], Module.finrank F E = 2 →
      ∀ (a : ℕ) [Fact (a = 2)], 1 ≤ a → ∀ (π : TRCuspRep F a) (P : CuspSub E a),
        π.IsRegAlg → Polarized π → IsBC0 π P → SplitIso π P)
    (h : QuadBC0 IsQuadTwist) : QuadBCw IsQuadTwist Polarized SplitIso := by
  intro F E _ _ _ _ _ _ _ h2 a _ ha π hr
  refine (h F E h2 a ha π hr).imp_right fun ⟨P, hP⟩ => ⟨P, hP, fun hreg hpol => ?_⟩
  have : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h2 }
  have : IsCMField E := IsCMField.ofCMExtension F E
  exact hSplit F E h2 a ha π P hreg hpol hP

/-- Split-place local compatibility assembly (`SplitOf.lean`): given Galois existence over totally
real `F` (`exR`), Galois existence over CM `K` (`exC`), and local Langlands / Weil–Deligne
compatibility away from `l` (`hRec`), proves split-place local isomorphism from `IsBC0 π P`
using `exists_prime_notMem`, `exists_quadratic_sign_character`, `ss_restrict_normal`,
`bcAtt0`, and `placeOf`! -/
theorem splitOf_assembly
    (F K : Type) [Field F] [NumberField F] [IsTotallyReal F]
    [Field K] [NumberField K] [IsCMField K] [Algebra F K] (hK : Module.finrank F K = 2)
    (n : ℕ) (π : TRCuspRep F n) (P : CuspSub K n)
    (hreg : π.IsRegAlg) (hbc : IsBC0 π P)
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 K))
    (i : v.adicCompletion F ≃+* w.adicCompletion K) (hi : Continuous i)
    (hloc : ∀ x : F, i (algebraMap F _ x) = algebraMap K _ (algebraMap F K x))
    (LocalIso : Prop)
    (hExR : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra F Ω] [Algebra K Ω]
      [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ),
      ∃ r : G F Ω →* GL (Fin n) (Qbar l), Continuous r ∧ AttR ι r π)
    (hCompat : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra F Ω] [Algebra K Ω]
      [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsAlgClosure K Ω] (ι : Qbar l ≃+* ℂ)
      (r : G F Ω →* GL (Fin n) (Qbar l)) (A : ValuationSubring Ω),
      ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ((l : ℕ) : 𝓞 K) ∉ w.asIdeal →
      IsPlaceOver A v → IsPlaceOver A w →
      PlaceIso A v A w (RingEquiv.refl Ω) (algebraMap F K) i →
      (CG.mk P).IsRegAlg → Continuous r → AttR ι r π → AttC ι (r.comp (res F Ω K)) P →
      LocalIso) : LocalIso := by
  obtain ⟨l, hl, hlv⟩ := exists_prime_notMem v
  have : Fact l.Prime := ⟨hl⟩
  obtain ⟨ι⟩ : Nonempty (Qbar l ≃+* ℂ) :=
    IsAlgClosed.ringEquiv_of_equiv_of_charZero
      (by
        have hcard : Cardinal.mk (Qbar l) = Cardinal.continuum := by
          have h1 : Cardinal.mk ℚ_[l] = Cardinal.continuum := by
            apply le_antisymm
            · have hd := Padic.denseRange_ratCast l
              have hex : ∀ x : ℚ_[l], ∃ u : ℕ → ℚ, Filter.Tendsto (fun k => (u k : ℚ_[l])) Filter.atTop (nhds x) :=
                fun x => by
                  obtain ⟨s, hs, hx⟩ := mem_closure_iff_seq_limit.1 (hd x)
                  choose u hu using hs
                  exact ⟨u, by simpa only [hu] using hx⟩
              choose u hu using hex
              have hinj : Function.Injective u := fun x y hxy => tendsto_nhds_unique (hu x) (hxy ▸ hu y)
              exact (Cardinal.mk_le_of_injective hinj).trans (by simp)
            · obtain ⟨g, -, -, hg⟩ :=
                (PerfectSpace.univ_perfect (α := ℚ_[l])).exists_nat_bool_injection Set.univ_nonempty
              calc Cardinal.continuum = Cardinal.mk (ℕ → Bool) := by
                    rw [← Cardinal.power_def, Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.two_power_aleph0]
                _ ≤ Cardinal.mk ℚ_[l] := Cardinal.mk_le_of_injective hg
          exact le_antisymm
            ((Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[l] (Qbar l)).trans
              (max_le h1.le Cardinal.aleph0_le_continuum))
            (h1 ▸ Cardinal.mk_le_of_injective (algebraMap ℚ_[l] (Qbar l)).injective)
        rw [hcard]; exact Cardinal.aleph0_lt_continuum)
      (Cardinal.eq.mp (by
        have h1 : Cardinal.mk ℚ_[l] = Cardinal.continuum := by
          apply le_antisymm
          · have hd := Padic.denseRange_ratCast l
            have hex : ∀ x : ℚ_[l], ∃ u : ℕ → ℚ, Filter.Tendsto (fun k => (u k : ℚ_[l])) Filter.atTop (nhds x) :=
              fun x => by
                obtain ⟨s, hs, hx⟩ := mem_closure_iff_seq_limit.1 (hd x)
                choose u hu using hs
                exact ⟨u, by simpa only [hu] using hx⟩
            choose u hu using hex
            have hinj : Function.Injective u := fun x y hxy => tendsto_nhds_unique (hu x) (hxy ▸ hu y)
            exact (Cardinal.mk_le_of_injective hinj).trans (by simp)
          · obtain ⟨g, -, -, hg⟩ :=
              (PerfectSpace.univ_perfect (α := ℚ_[l])).exists_nat_bool_injection Set.univ_nonempty
            calc Cardinal.continuum = Cardinal.mk (ℕ → Bool) := by
                  rw [← Cardinal.power_def, Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.two_power_aleph0]
              _ ≤ Cardinal.mk ℚ_[l] := Cardinal.mk_le_of_injective hg
        have hcard : Cardinal.mk (Qbar l) = Cardinal.continuum := le_antisymm
          ((Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[l] (Qbar l)).trans
            (max_le h1.le Cardinal.aleph0_le_continuum))
          (h1 ▸ Cardinal.mk_le_of_injective (algebraMap ℚ_[l] (Qbar l)).injective)
        rw [hcard, Cardinal.mk_complex]))
  let Ω := AlgebraicClosure K
  have : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  have : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.trans F K Ω⟩
  obtain ⟨r, hr_cont, hatt⟩ := hExR l Ω ι
  have hnorm : (res F Ω K).range.Normal := by
    obtain ⟨δ, hδ, -⟩ := exists_quadratic_sign_character F K Ω (Qbar l) hK
    rw [show (res F Ω K).range = δ.ker from Subgroup.ext fun s => (hδ s).symm]
    infer_instance
  have hss_res : IsSSRep (r.comp (res F Ω K)) := by
    have hss_sub := ss_restrict_normal r (res F Ω K).range hatt.1
    intro W hW
    obtain ⟨W', hW', hcompl⟩ := hss_sub W fun ⟨g, hg⟩ v hv => by
      obtain ⟨s, rfl⟩ := hg
      exact hW s v hv
    exact ⟨W', fun s v hv => hW' ⟨res F Ω K s, ⟨s, rfl⟩⟩ v hv, hcompl⟩
  obtain ⟨hPr, hPa⟩ := bcAtt0 F K Ω l ι n r π P hbc
  obtain ⟨hw, A, hAv, hAw, hiso⟩ := placeOf F K Ω v w i hi hloc
  have hlw : ((l : ℕ) : 𝓞 K) ∉ w.asIdeal := fun hm => hlv <| by
    rw [← hw]
    change algebraMap (𝓞 F) (𝓞 K) _ ∈ w.asIdeal
    rwa [map_natCast]
  exact hCompat l Ω ι r A hlv hlw hAv hAw hiso (hPr hreg) hr_cont hatt (hPa hatt hss_res)

end AdmissibleSatakeAndBaseChange

end RHDirect.Stage13GL_CrystallineBaseChange
