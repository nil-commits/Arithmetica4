import RHDirect.RallisSeesaw
import RHDirect.Stage11DefiniteUnitaryChain
import RHDirect.UnitaryMassFormula
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.MeasureTheory.Group.FundamentalDomain

/-!
# RHDirect.Stage14M1_GenusClassDecomp

Field-2 Package M1 Wave 1 (Module 6 of 6): **Concrete Hermitian Genus Class Decomposition,
Canonical Petersson Weights, Unconditional Finiteness, Orbit-Stabilizer Sublevel Sums,
Exact Double-Coset Measure Decomposition, and Iterated Chain-Operator Independence**.

Zero `sorry`, zero custom `axiom`s, zero `native_decide`.

## Structure

1. **Double-Coset Genus Class Sets (`DoubleCosetClassSet`) & Adelic Unitary `HermGenusClassSet`**:
   - Group-theoretic double-coset space `DoubleCosetClassSet Γ K = DoubleCoset.Quotient Γ K`,
     stabilizer subgroup `doubleCosetStab Γ K g = { γ ∈ Γ | g⁻¹ γ g ∈ K }`, conjugation
     invariance `card_doubleCosetStab_mul`, covering & disjointness of any section `s`.
   - Concrete CM-field unitary group `UnitaryGroupOver R σ J` over any `F`-algebra `R`,
     functorial embedding `unitaryMap`, finite-adelic unitary group `UnitaryAdelicGrp F E σ J`,
     rational points `UnitaryRatSubgroup F E σ J`, adelic lattice completion `adelicLatHat`,
     compact-open lattice stabilizer `HermLatticeStab F E σ J L`, and the concrete adelic
     double-coset space **`HermGenusClassSet F E σ J L`** (`U(F) \ U(𝔸_f) / K_f`), plus
     concrete definite lattice genus classes `ConcreteLatticeGenusClassSet`.

2. **Canonical Genus Class Weights (`GenusClassWeight`) & Universal Denominator Clearing**:
   - Representative-independent weight **`GenusClassWeight Γ K c = 1 / |Aut(L_c)|`**
     (`HermGenusClassWeight` for `HermGenusClassSet`), positivity `genusClassWeight_pos`, total
     mass `genusClassMass`, universal denominator `genusClassDenom` clearing every weight
     simultaneously (`genusClassDenom_mul_weight_int`), and bridge to
     `Stage11DefiniteUnitaryChain.peterssonWeight`.

3. **Unconditional Finiteness (`genus_class_finite`) & Minkowski Mod-3 Rigidity**:
   - **Minkowski Mod-3 Torsion-Free Rigidity (`minkowski_mod_three_stabilizer_bound`)**:
     every finite subgroup of `GL_d(ℤ)` embeds injectively into `M_d(ℤ/3ℤ)`, giving the
     uniform stabilizer bound `|Aut(L)| ≤ 3 ^ (d^2)` independent of `L`!
   - **Adelic & Lattice Stabilizer Finiteness**:
     unconditional uniform bound `card_definiteUnitaryGroup_le_pow` for ALL definite
     Hermitian lattices `L : HermitianLattice N` (`|Aut(L)| ≤ 3 ^ ((2*N)*(2*N))`).
   - **Unconditional Genus Finiteness (`genus_class_finite`)**:
     (a) `genus_class_finite_of_finite_volume` from finite fundamental domain volume `μ 𝓕 < ⊤`,
         `0 < μ K`, and uniform stabilizer bound;
     (b) `genus_class_finite_sublevel` for any finite-index sublevel `K' ≤ K`;
     (c) `genus_class_finite` for bounded-denominator definite Hermitian lattice subgenera.

4. **Orbit-Stabilizer Sum (`double_coset_stabilizer_orbit_sum`)**:
   - Finite-group orbit-stabilizer sum `finite_group_orbit_stabilizer_sum` (`OrbitSum`).
   - Exact double-coset fiber decomposition over a finite-index sublevel `K' ≤ K`:
     the fiber of `DoubleCosetClassSet Γ K' → DoubleCosetClassSet Γ K` over `Γ g K` is in
     canonical bijection with `Stab_{Γ, K}(g) \ (K / K')`, yielding
     **`double_coset_stabilizer_orbit_sum`** and `genusClassMass_sublevel_eq`:
     `∑_{c' ↦ c} |Stab(c')|⁻¹ = [K : K'] * |Stab(c)|⁻¹` and
     `genusClassMass Γ K' = [K : K'] * genusClassMass Γ K`.

5. **Exact Measure Decomposition Over Double Cosets (`class_decomp_measure_eq_sum`)**:
   - **`class_decomp_measure_eq_sum`**:
     `μ 𝓕 = ∑ c : DoubleCosetClassSet Γ K, μ K * (|Stab(s c)| : ℝ≥0∞)⁻¹`,
   - real-valued **`class_decomp_toReal_eq_mul_sum`**:
     `(μ 𝓕).toReal = (μ K).toReal * ∑ c, GenusClassWeight Γ K c`,
   - **`class_decomp_lintegral_eq_sum`**: exact integral unfolding over `𝓕` for any
     `(Γ, K)`-bi-invariant measurable function `φ : G → ℝ≥0∞`.

6. **Double-Coset Independence of Adelic Theta Lifts & Iterated `chainOpM` (`chain_op_double_coset_indep`)**:
   - Adelic automorphic spaces `AdelicAMF` / `AdelicAMFK`, `class_sum_double_coset_indep`,
     `adelic_theta_lift_double_coset_indep`, `adelic_ip_double_coset_indep`.
   - **`chain_op_double_coset_indep`**: exact independence of `RallisSeesaw.chainOpM` from the
     choice of double-coset representatives `s j` at every stage `j = 0, ..., m`, together with
     denominator clearing `chain_op_double_coset_int_clearing` and `DefiniteUnitaryTower` bridge!
-/

noncomputable section

open MeasureTheory Finset Real NumberField IsDedekindDomain
open scoped BigOperators ENNReal TensorProduct Matrix Pointwise

namespace RHDirect.Stage14M1_GenusClassDecomp

/-! ## Section 1: Abstract Double-Coset Genus Class Sets & Stabilizer Theory -/

section DoubleCosetTheory

variable {G : Type*} [Group G]

/-- The double-coset genus class set `Γ \ G / K` for subgroups `Γ, K ≤ G`. -/
abbrev DoubleCosetClassSet (Γ K : Subgroup G) : Type _ :=
  DoubleCoset.Quotient (Γ : Set G) (K : Set G)

/-- Canonical projection `G → Γ \ G / K`. -/
def doubleCosetMk (Γ K : Subgroup G) (g : G) : DoubleCosetClassSet Γ K :=
  DoubleCoset.mk Γ K g

theorem doubleCosetMk_eq_quotient_mk (Γ K : Subgroup G) (g : G) :
    doubleCosetMk Γ K g = Quotient.mk (DoubleCoset.setoid (Γ : Set G) (K : Set G)) g :=
  rfl

/-- Stabilizer subgroup `Stab_{Γ, K}(g) = { γ ∈ Γ | g⁻¹ γ g ∈ K } = Γ ∩ g K g⁻¹` inside `Γ`. -/
def doubleCosetStab (Γ K : Subgroup G) (g : G) : Subgroup Γ where
  carrier := { γ : Γ | g⁻¹ * (γ : G) * g ∈ K }
  one_mem' := by simp [K.one_mem]
  mul_mem' := by
    intro γ₁ γ₂ h₁ h₂
    change g⁻¹ * ((γ₁ * γ₂ : Γ) : G) * g ∈ K
    have heq : g⁻¹ * ((γ₁ * γ₂ : Γ) : G) * g =
        (g⁻¹ * (γ₁ : G) * g) * (g⁻¹ * (γ₂ : G) * g) := by
      push_cast
      group
    rw [heq]
    exact K.mul_mem h₁ h₂
  inv_mem' := by
    intro γ hγ
    change g⁻¹ * ((γ⁻¹ : Γ) : G) * g ∈ K
    have heq : g⁻¹ * ((γ⁻¹ : Γ) : G) * g = (g⁻¹ * (γ : G) * g)⁻¹ := by
      push_cast
      group
    rw [heq]
    exact K.inv_mem hγ

theorem mem_doubleCosetStab_iff (Γ K : Subgroup G) (g : G) (γ : Γ) :
    γ ∈ doubleCosetStab Γ K g ↔ g⁻¹ * (γ : G) * g ∈ K :=
  Iff.rfl

theorem mem_doubleCosetStab_iff_genusAut (Γ K : Subgroup G) (g : G) (γ : Γ) :
    γ ∈ doubleCosetStab Γ K g ↔ γ ∈ UnitaryMassFormula.genusAut Γ K g := by
  simp only [mem_doubleCosetStab_iff, UnitaryMassFormula.genusAut, Set.mem_ofPred_eq, mul_assoc]

theorem doubleCosetStab_eq_inter (Γ K : Subgroup G) (g : G) :
    (doubleCosetStab Γ K g).map Γ.subtype =
      Γ ⊓ K.map (MulAut.conj g).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.coe_subtype, Subgroup.mem_inf]
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    refine ⟨γ.2, g⁻¹ * (γ : G) * g, hγ, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro ⟨hxΓ, k, hkK, hxk⟩
    refine ⟨⟨x, hxΓ⟩, ?_, rfl⟩
    rw [mem_doubleCosetStab_iff]
    change g⁻¹ * x * g ∈ K
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxk
    rw [← hxk]
    simpa [mul_assoc] using hkK

/-- Conjugation law for double-coset stabilizers under `(γ, κ) ∈ Γ × K`:
`δ ∈ Stab(γ g κ) ↔ γ⁻¹ δ γ ∈ Stab(g)`. -/
theorem mem_doubleCosetStab_mul_iff (Γ K : Subgroup G) (g : G) (γ : Γ) (κ : K) (δ : Γ) :
    δ ∈ doubleCosetStab Γ K ((γ : G) * g * κ) ↔ γ⁻¹ * δ * γ ∈ doubleCosetStab Γ K g := by
  simp only [mem_doubleCosetStab_iff]
  have heq : ((γ : G) * g * κ)⁻¹ * (δ : G) * ((γ : G) * g * κ) =
      (κ : G)⁻¹ * (g⁻¹ * ((γ⁻¹ * δ * γ : Γ) : G) * g) * κ := by
    push_cast
    group
  rw [heq, K.mul_mem_cancel_right κ.2, K.mul_mem_cancel_left (K.inv_mem κ.2)]

/-- Explicit group isomorphism `Stab_{Γ, K}(γ g κ) ≃* Stab_{Γ, K}(g)`. -/
def doubleCosetStabConjEquiv (Γ K : Subgroup G) (g : G) (γ : Γ) (κ : K) :
    doubleCosetStab Γ K ((γ : G) * g * κ) ≃* doubleCosetStab Γ K g where
  toFun δ := ⟨γ⁻¹ * δ.1 * γ, (mem_doubleCosetStab_mul_iff Γ K g γ κ δ.1).mp δ.2⟩
  invFun δ := ⟨γ * δ.1 * γ⁻¹, (mem_doubleCosetStab_mul_iff Γ K g γ κ _).mpr (by
    convert δ.2 using 2; group)⟩
  left_inv δ := Subtype.ext (by group)
  right_inv δ := Subtype.ext (by group)
  map_mul' δ₁ δ₂ := Subtype.ext (by
    simp only [Subgroup.coe_mul]
    group)

theorem card_doubleCosetStab_mul (Γ K : Subgroup G) (g : G) (γ : Γ) (κ : K) :
    Nat.card (doubleCosetStab Γ K ((γ : G) * g * κ)) = Nat.card (doubleCosetStab Γ K g) :=
  Nat.card_congr (doubleCosetStabConjEquiv Γ K g γ κ).toEquiv

theorem card_doubleCosetStab_eq_of_mk_eq {Γ K : Subgroup G} {g₁ g₂ : G}
    (h : doubleCosetMk Γ K g₁ = doubleCosetMk Γ K g₂) :
    Nat.card (doubleCosetStab Γ K g₁) = Nat.card (doubleCosetStab Γ K g₂) := by
  obtain ⟨γ, hγ, κ, hκ, h₂⟩ := (DoubleCoset.eq Γ K g₁ g₂).mp h
  have h2eq : g₂ = ((⟨γ, hγ⟩ : Γ) : G) * g₁ * ((⟨κ, hκ⟩ : K) : G) := h₂
  rw [h2eq, card_doubleCosetStab_mul]

/-- A section `s : Γ \ G / K → G` choosing a representative in each double coset. -/
structure DoubleCosetReps (Γ K : Subgroup G) where
  rep : DoubleCosetClassSet Γ K → G
  mk_rep : ∀ c, doubleCosetMk Γ K (rep c) = c

/-- Canonical double-coset section given by `Quotient.out`. -/
def canonicalDoubleCosetReps (Γ K : Subgroup G) : DoubleCosetReps Γ K where
  rep c := Quotient.out c
  mk_rep c := by
    rw [doubleCosetMk_eq_quotient_mk]
    exact Quotient.out_eq c

theorem doubleCosetReps_covering (Γ K : Subgroup G) (s : DoubleCosetReps Γ K) (x : G) :
    ∃ c : DoubleCosetClassSet Γ K, ∃ γ : Γ, ∃ κ : K,
      x = (γ : G) * s.rep c * κ := by
  set c := doubleCosetMk Γ K x
  have hmk : doubleCosetMk Γ K (s.rep c) = doubleCosetMk Γ K x := s.mk_rep c
  obtain ⟨γ, hγ, κ, hκ, hx⟩ := (DoubleCoset.eq Γ K (s.rep c) x).mp hmk
  exact ⟨c, ⟨γ, hγ⟩, ⟨κ, hκ⟩, hx⟩

theorem doubleCosetReps_disjoint (Γ K : Subgroup G) (s : DoubleCosetReps Γ K)
    {c₁ c₂ : DoubleCosetClassSet Γ K} {γ₁ γ₂ : Γ} {κ₁ κ₂ : K}
    (heq : (γ₁ : G) * s.rep c₁ * κ₁ = (γ₂ : G) * s.rep c₂ * κ₂) :
    c₁ = c₂ := by
  rw [← s.mk_rep c₁, ← s.mk_rep c₂]
  refine (DoubleCoset.eq Γ K (s.rep c₁) (s.rep c₂)).mpr ?_
  refine ⟨γ₂⁻¹ * γ₁, (Γ.mul_mem (Γ.inv_mem γ₂.2) γ₁.2),
    κ₁ * κ₂⁻¹, (K.mul_mem κ₁.2 (K.inv_mem κ₂.2)), ?_⟩
  simp only [Subgroup.coe_inv]
  calc (s.rep c₂ : G)
      = (γ₂ : G)⁻¹ * ((γ₂ : G) * s.rep c₂ * (κ₂ : G)) * (κ₂ : G)⁻¹ := by group
    _ = (γ₂ : G)⁻¹ * ((γ₁ : G) * s.rep c₁ * (κ₁ : G)) * (κ₂ : G)⁻¹ := by rw [← heq]
    _ = (γ₂ : G)⁻¹ * (γ₁ : G) * s.rep c₁ * ((κ₁ : G) * (κ₂ : G)⁻¹) := by group

private theorem doubleCosetSublevelProj_wd (Γ : Subgroup G) {K' K : Subgroup G} (hKK' : K' ≤ K)
    {g₁ g₂ : G} (h : (DoubleCoset.setoid (Γ : Set G) (K' : Set G)).r g₁ g₂) :
    doubleCosetMk Γ K g₁ = doubleCosetMk Γ K g₂ := by
  have heq : doubleCosetMk Γ K' g₁ = doubleCosetMk Γ K' g₂ := Quotient.sound h
  obtain ⟨γ, hγ, κ, hκ, h₁⟩ := (DoubleCoset.eq Γ K' g₂ g₁).mp heq.symm
  exact ((DoubleCoset.eq Γ K g₂ g₁).mpr ⟨γ, hγ, κ, hKK' hκ, h₁⟩).symm

/-- For a sublevel `K' ≤ K`, the canonical surjection `Γ \ G / K' → Γ \ G / K`. -/
def doubleCosetSublevelProj (Γ : Subgroup G) {K' K : Subgroup G} (hKK' : K' ≤ K) :
    DoubleCosetClassSet Γ K' → DoubleCosetClassSet Γ K :=
  Quotient.lift (fun g => doubleCosetMk Γ K g) fun _ _ h =>
    doubleCosetSublevelProj_wd Γ hKK' h

@[simp]
theorem doubleCosetSublevelProj_mk (Γ : Subgroup G) {K' K : Subgroup G} (hKK' : K' ≤ K) (g : G) :
    doubleCosetSublevelProj Γ hKK' (doubleCosetMk Γ K' g) = doubleCosetMk Γ K g :=
  rfl

theorem doubleCosetSublevelProj_surjective (Γ : Subgroup G) {K' K : Subgroup G} (hKK' : K' ≤ K) :
    Function.Surjective (doubleCosetSublevelProj Γ hKK') := by
  intro c
  obtain ⟨g, rfl⟩ := Quotient.exists_rep c
  exact ⟨doubleCosetMk Γ K' g, doubleCosetSublevelProj_mk Γ hKK' g⟩

end DoubleCosetTheory

/-! ## Section 2: Concrete CM-Field Adelic Unitary Groups & `HermGenusClassSet` -/

section AdelicUnitaryGroups

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- `σ`-conjugate transpose of a matrix over `R ⊗[F] E` where `σ : E →ₐ[F] E` is an
`F`-algebra involution. -/
def hermConjT (R : Type*) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (A : Matrix (Fin M) (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E) :=
  (A.map (Algebra.TensorProduct.map (AlgHom.id F R) σ).toRingHom)ᵀ

lemma hermConjT_one (R : Type*) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ} :
    hermConjT R σ (1 : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = 1 := by
  ext i j
  simp only [hermConjT, Matrix.transpose_apply, Matrix.map_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

lemma hermConjT_mul (R : Type*) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (A B : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :
    hermConjT R σ (A * B) = hermConjT R σ B * hermConjT R σ A := by
  unfold hermConjT
  rw [← Matrix.transpose_mul]
  congr 1
  exact map_mul (Algebra.TensorProduct.map (AlgHom.id F R) σ).toRingHom.mapMatrix A B

lemma hermConjT_involutive (R : Type*) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    (hσ : ∀ a, σ (σ a) = a) {M : ℕ} (A : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :
    hermConjT R σ (hermConjT R σ A) = A := by
  ext i j
  simp only [hermConjT, Matrix.transpose_apply, Matrix.map_apply]
  change (Algebra.TensorProduct.map (AlgHom.id F R) σ)
    ((Algebra.TensorProduct.map (AlgHom.id F R) σ) (A i j)) = A i j
  induction A i j using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [Algebra.TensorProduct.map_tmul, hσ]
  | add x y hx hy => simp [map_add, hx, hy]

/-- Base-change matrix `J_R` in `M_M(R ⊗[F] E)` attached to `J : M_M(E)`. -/
def baseChangeMat (R : Type*) [CommRing R] [Algebra F R] {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : Matrix (Fin M) (Fin M) (R ⊗[F] E) :=
  J.map (Algebra.TensorProduct.includeRight (R := F) (A := R) (B := E)).toRingHom

/-- **Concrete Unitary Group `U(R)`** over any commutative `F`-algebra `R`:
`{ g ∈ GL_M(R ⊗[F] E) | (g^†_σ) * J_R * g = J_R }`. -/
def UnitaryGroupOver (R : Type*) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : Subgroup (GL (Fin M) (R ⊗[F] E)) where
  carrier := { g | hermConjT R σ g.1 * baseChangeMat R J * g.1 = baseChangeMat R J }
  one_mem' := by
    simp only [Set.mem_ofPred_eq, Units.val_one, hermConjT_one, Matrix.one_mul, Matrix.mul_one]
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_ofPred_eq, Units.val_mul, hermConjT_mul] at hg hh ⊢
    calc hermConjT R σ h.1 * hermConjT R σ g.1 * baseChangeMat R J * (g.1 * h.1)
        = hermConjT R σ h.1 * (hermConjT R σ g.1 * baseChangeMat R J * g.1) * h.1 := by
          simp only [Matrix.mul_assoc]
      _ = hermConjT R σ h.1 * baseChangeMat R J * h.1 := by rw [hg]
      _ = baseChangeMat R J := hh
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at hg ⊢
    have hginv : (g.1 : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * (g⁻¹).1 = 1 := g.mul_inv
    have hg' : hermConjT R σ (g⁻¹).1 * hermConjT R σ g.1 = 1 := by
      rw [← hermConjT_mul]
      have hmul1 : (g.1 : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * (g⁻¹).1 = 1 := g.mul_inv
      rw [hmul1, hermConjT_one]
    calc hermConjT R σ (g⁻¹).1 * baseChangeMat R J * (g⁻¹).1
        = hermConjT R σ (g⁻¹).1 * (hermConjT R σ g.1 * baseChangeMat R J * g.1) * (g⁻¹).1 := by
          rw [hg]
      _ = (hermConjT R σ (g⁻¹).1 * hermConjT R σ g.1) * baseChangeMat R J * (g.1 * (g⁻¹).1) := by
          simp only [Matrix.mul_assoc]
      _ = baseChangeMat R J := by rw [hg', hginv, Matrix.one_mul, Matrix.mul_one]

/-- Functorial group homomorphism `U(R) →* U(S)` induced by an `F`-algebra homomorphism
`φ : R →ₐ[F] S`. -/
def unitaryMap {R S : Type*} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (φ : R →ₐ[F] S) (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    UnitaryGroupOver R σ J →* UnitaryGroupOver S σ J where
  toFun g :=
    ⟨Units.map (RingHom.mapMatrix (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom).toMonoidHom g.1,
      by
        let ψ := (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom
        have hcomm : hermConjT S σ (ψ.mapMatrix (g.1 : Matrix (Fin M) (Fin M) (R ⊗[F] E))) =
            ψ.mapMatrix (hermConjT R σ g.1) := by
          ext i j
          simp only [hermConjT, Matrix.transpose_apply, Matrix.map_apply, RingHom.mapMatrix_apply]
          induction g.1.val j i using TensorProduct.induction_on with
          | zero => simp
          | tmul r e => simp [ψ, Algebra.TensorProduct.map_tmul]
          | add x y hx hy =>
            change (Algebra.TensorProduct.map (AlgHom.id F S) σ).toRingHom (ψ (x + y)) =
              ψ ((Algebra.TensorProduct.map (AlgHom.id F R) σ).toRingHom (x + y))
            rw [map_add, map_add, hx, hy, map_add, map_add]
        have hJ : baseChangeMat S J = ψ.mapMatrix (baseChangeMat R J) := by
          ext i j
          simp [baseChangeMat, ψ, Algebra.TensorProduct.map_tmul]
        show hermConjT S σ (ψ.mapMatrix g.1.val) * baseChangeMat S J * (ψ.mapMatrix g.1.val) =
          baseChangeMat S J
        rw [hcomm, hJ, ← map_mul ψ.mapMatrix, ← map_mul ψ.mapMatrix]
        exact congrArg ψ.mapMatrix g.2⟩
  map_one' := by ext i j; simp
  map_mul' g h := by
    ext i j
    simp only [Subgroup.coe_mul, Units.val_mul, RingHom.toMonoidHom_eq_coe, Units.coe_map,
      MonoidHom.coe_coe, map_mul]

/-- When `φ : R →ₐ[F] S` is injective over a field `F`, the induced unitary map `U(R) →* U(S)`
is injective. -/
theorem unitaryMap_injective {R S : Type*} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (φ : R →ₐ[F] S) (hφ : Function.Injective φ) (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) [FiniteDimensional F E] :
    Function.Injective (unitaryMap φ σ J) := by
  intro g₁ g₂ heq
  let b := Module.finBasis F E
  have hinjT : Function.Injective (Algebra.TensorProduct.map φ (AlgHom.id F E)) := by
    intro x y hxy
    have hdiff : Algebra.TensorProduct.map φ (AlgHom.id F E) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    suffices z : ∀ z : R ⊗[F] E,
        Algebra.TensorProduct.map φ (AlgHom.id F E) z = 0 → z = 0 from
      sub_eq_zero.mp (z (x - y) hdiff)
    intro z hz
    let toFunR : R ⊗[F] E →ₗ[F] (Fin (Module.finrank F E) → R) :=
      TensorProduct.lift
        { toFun := fun r =>
            { toFun := fun e i => b.repr e i • r
              map_add' := fun e₁ e₂ => by ext i; dsimp; rw [map_add, Finsupp.coe_add, Pi.add_apply, add_smul]
              map_smul' := fun c e => by
                ext i; dsimp
                rw [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, smul_smul, mul_comm] }
          map_add' := fun r₁ r₂ => by ext e i; dsimp; rw [smul_add]
          map_smul' := fun c r => by ext e i; dsimp; rw [smul_comm] }
    let toFunS : S ⊗[F] E →ₗ[F] (Fin (Module.finrank F E) → S) :=
      TensorProduct.lift
        { toFun := fun s =>
            { toFun := fun e i => b.repr e i • s
              map_add' := fun e₁ e₂ => by ext i; dsimp; rw [map_add, Finsupp.coe_add, Pi.add_apply, add_smul]
              map_smul' := fun c e => by
                ext i; dsimp
                rw [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, smul_smul, mul_comm] }
          map_add' := fun s₁ s₂ => by ext e i; dsimp; rw [smul_add]
          map_smul' := fun c s => by ext e i; dsimp; rw [smul_comm] }
    have hrec : ∀ w : R ⊗[F] E, ∑ i, toFunR w i ⊗ₜ[F] b i = w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul r e =>
        simp only [toFunR, TensorProduct.lift.tmul, LinearMap.coe_mk, AddHom.coe_mk]
        have he : e = ∑ i, b.repr e i • b i := (b.sum_repr e).symm
        conv_rhs => rw [he, TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        calc (b.repr e i • r) ⊗ₜ[F] b i
            = b.repr e i • (r ⊗ₜ[F] b i) := (TensorProduct.smul_tmul' _ _ _).symm
          _ = r ⊗ₜ[F] (b.repr e i • b i) := TensorProduct.smul_tmul _ _ _
      | add a c ha hc =>
        simp only [map_add, Pi.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib, ha, hc]
    have hcoord : ∀ w i, φ (toFunR w i) = toFunS (Algebra.TensorProduct.map φ (AlgHom.id F E) w) i := by
      intro w i
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul r e =>
        simp only [toFunR, toFunS, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
          TensorProduct.lift.tmul, LinearMap.coe_mk, AddHom.coe_mk]
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, φ.commutes]
      | add a c ha hc =>
        simp only [map_add, Pi.add_apply, ha, hc]
    have hto0 : toFunR z = 0 := by
      ext i
      apply hφ
      rw [hcoord z i, hz, LinearMap.map_zero, Pi.zero_apply, Pi.zero_apply, map_zero]
    rw [← hrec z, hto0]
    simp
  apply Subtype.ext
  apply Units.ext
  ext i j
  apply hinjT
  have := congrArg (fun u => ((u.1 : GL (Fin M) (S ⊗[F] E)) : Matrix (Fin M) (Fin M) (S ⊗[F] E)) i j) heq
  simpa [unitaryMap] using this

end AdelicUnitaryGroups

section FiniteAdelicClassSet

open Classical

variable (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/-- Shorthand for the finite adele ring `𝔸_{F,f}` of a number field `F`. -/
abbrev FinAdeleF : Type _ := FiniteAdeleRing (𝓞 F) F

/-- Canonical `F`-algebra structure on `FinAdeleF F` via `FiniteAdeleRing.algebraMap`. -/
@[instance_reducible]
def finAdeleAlgebra : Algebra F (FinAdeleF F) :=
  (FiniteAdeleRing.algebraMap (𝓞 F) F).toAlgebra

attribute [local instance] finAdeleAlgebra

/-- Every number field `F` has at least one finite place `v : HeightOneSpectrum (𝓞 F)`. -/
theorem nonempty_heightOneSpectrum : Nonempty (HeightOneSpectrum (𝓞 F)) := by
  have hnot : (2 : 𝓞 F) ∉ (⊤ : Ideal (𝓞 F)) → False := fun h => h trivial
  have hne_top : Ideal.span {(2 : 𝓞 F)} ≠ ⊤ := by
    intro htop
    rw [Ideal.eq_top_iff_one, Ideal.mem_span_singleton] at htop
    obtain ⟨q, hq⟩ := htop
    have hint : IsIntegral ℤ ((1 : F) / 2) := by
      have hqF : (2 : F) * (q : F) = 1 := by
        simpa [map_ofNat] using congrArg (algebraMap (𝓞 F) F) hq.symm
      have hhalf : (1 : F) / 2 = (q : F) := by
        calc (1 : F) / 2 = ((2 : F) * (q : F)) / 2 := by rw [hqF]
          _ = (q : F) := by ring
      rw [hhalf]
      exact q.2
    have hnorm : ((1 : F) / 2) = algebraMap ℚ F ((1 : ℚ) / 2) := by
      simp
    have hq_rat : IsIntegral ℤ ((1 : ℚ) / 2) := by
      have := IsIntegral.tower_bot (R := ℤ) (A := ℚ) (B := F)
      exact (isIntegral_algebraMap_iff (algebraMap ℚ F).injective).mp (by
        simpa [hnorm] using hint)
    have h2 : (2 : ℤ) ∣ 1 := by
      rw [IsIntegrallyClosed.isIntegral_iff] at hq_rat
      obtain ⟨z, hz⟩ := hq_rat
      have hz_q : (z : ℚ) = 1 / 2 := by simpa using hz
      have : (2 : ℚ) * (z : ℚ) = 1 := by
        rw [hz_q]
        norm_num
      have hz2 : (2 : ℤ) * z = 1 := by exact_mod_cast this
      exact ⟨z, hz2.symm⟩
    omega
  obtain ⟨m, hm, h2m⟩ := Ideal.exists_le_maximal (Ideal.span {(2 : 𝓞 F)}) hne_top
  have hm_ne : m ≠ ⊥ := by
    intro hbot
    rw [hbot] at h2m
    have h20 : (2 : 𝓞 F) = 0 := Ideal.mem_bot.mp (h2m (Ideal.subset_span (Set.mem_singleton _)))
    have : (2 : F) = 0 := by exact_mod_cast h20
    norm_num at this
  exact ⟨⟨m, hm.isPrime, hm_ne⟩⟩

theorem nontrivial_finAdeleF : Nontrivial (FinAdeleF F) := by
  obtain ⟨v⟩ := nonempty_heightOneSpectrum F
  refine ⟨⟨1, 0, fun h => ?_⟩⟩
  have hv := congrArg (fun x : FinAdeleF F => x v) h
  exact one_ne_zero hv

/-- Canonical `F`-algebra embedding `F →ₐ[F] FinAdeleF F`. -/
def diagFinAdeleAlg : F →ₐ[F] FinAdeleF F :=
  Algebra.ofId F (FinAdeleF F)

theorem diagFinAdeleAlg_injective : Function.Injective (diagFinAdeleAlg F) := by
  have : Nontrivial (FinAdeleF F) := nontrivial_finAdeleF F
  exact RingHom.injective (diagFinAdeleAlg F).toRingHom

/-- The **Finite-Adelic Unitary Group `U(𝔸_{F,f})`** attached to `(E/F, σ, J)`. -/
abbrev UnitaryAdelicGrp (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : Type _ :=
  UnitaryGroupOver (FinAdeleF F) σ J

/-- The **Rational Subgroup `U(F) ≤ U(𝔸_{F,f})`** embedded diagonally. -/
def UnitaryRatSubgroup (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Subgroup (UnitaryAdelicGrp F E σ J) :=
  (unitaryMap (diagFinAdeleAlg F) σ J).range

/-- Integral finite-adele subring `∏_v 𝒪_{F,v} ⊂ 𝔸_{F,f}`. -/
def IntFinAdeleSubring : Subring (FinAdeleF F) where
  carrier := { a : FinAdeleF F | ∀ v : HeightOneSpectrum (𝓞 F), a v ∈ v.adicCompletionIntegers F }
  zero_mem' _ := zero_mem _
  one_mem' _ := one_mem _
  add_mem' ha hb v := add_mem (ha v) (hb v)
  neg_mem' ha v := neg_mem (ha v)
  mul_mem' ha hb v := mul_mem (ha v) (hb v)

/-- The **Adelic Lattice Completion `L̂ ⊂ (𝔸_{F,f} ⊗_F E)^M`** generated by `(∏_v 𝒪_{F,v}) · L`
for an `𝓞_E`-lattice `L ⊂ E^M`. -/
def adelicLatHat {M : ℕ} (L : Submodule (𝓞 E) (Fin M → E)) :
    AddSubgroup (Fin M → FinAdeleF F ⊗[F] E) :=
  AddSubgroup.closure
    { y : Fin M → FinAdeleF F ⊗[F] E |
      ∃ a ∈ IntFinAdeleSubring F, ∃ x ∈ L,
        y = fun i => a ⊗ₜ[F] (x i) }

/-- Canonical diagonal embedding `E^M → (𝔸_{F,f} ⊗_F E)^M` sending `x ↦ (1 ⊗ x_i)`. -/
def diagLatVec {M : ℕ} (x : Fin M → E) : Fin M → FinAdeleF F ⊗[F] E :=
  fun i => (1 : FinAdeleF F) ⊗ₜ[F] (x i)

/-- Matrix action of an element `g ∈ U(𝔸_{F,f})` on `(𝔸_{F,f} ⊗_F E)^M`. -/
def adelicMulVec (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (g : UnitaryAdelicGrp F E σ J) (y : Fin M → FinAdeleF F ⊗[F] E) :
    Fin M → FinAdeleF F ⊗[F] E :=
  ((g.1 : GL (Fin M) (FinAdeleF F ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (FinAdeleF F ⊗[F] E)).mulVec y

/-- **Compact-Open Adelic Lattice Stabilizer `K_f = Stab_{U(𝔸_f)}(L̂)`**:
elements of `U(𝔸_{F,f})` preserving the completed lattice `L̂`. -/
def HermLatticeStab (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (L : Submodule (𝓞 E) (Fin M → E)) :
    Subgroup (UnitaryAdelicGrp F E σ J) where
  carrier := { g | ∀ y, y ∈ adelicLatHat F E L ↔ adelicMulVec F E σ J g y ∈ adelicLatHat F E L }
  one_mem' y := by
    change y ∈ adelicLatHat F E L ↔ (1 : Matrix _ _ _).mulVec y ∈ adelicLatHat F E L
    rw [Matrix.one_mulVec]
  mul_mem' {g h} hg hh y := by
    have hmul : adelicMulVec F E σ J (g * h) y =
        adelicMulVec F E σ J g (adelicMulVec F E σ J h y) := by
      change ((g.1 * h.1 : GL (Fin M) (FinAdeleF F ⊗[F] E)) :
        Matrix (Fin M) (Fin M) (FinAdeleF F ⊗[F] E)).mulVec y = _
      rw [Units.val_mul, ← Matrix.mulVec_mulVec]
      rfl
    change y ∈ adelicLatHat F E L ↔ adelicMulVec F E σ J (g * h) y ∈ adelicLatHat F E L
    rw [hmul, ← hg (adelicMulVec F E σ J h y), ← hh y]
  inv_mem' {g} hg y := by
    have hinv : adelicMulVec F E σ J g (adelicMulVec F E σ J g⁻¹ y) = y := by
      change g.1.val.mulVec ((g⁻¹ : UnitaryAdelicGrp F E σ J).1.val.mulVec y) = y
      rw [Matrix.mulVec_mulVec]
      have hmul : g.1.val * (g⁻¹ : UnitaryAdelicGrp F E σ J).1.val = 1 := by
        simp
      rw [hmul, Matrix.one_mulVec]
    have hg' := hg (adelicMulVec F E σ J g⁻¹ y)
    rw [hinv] at hg'
    exact hg'.symm

/-- **Concrete Adelic Hermitian Genus Class Set `HermGenusClassSet F E σ J L = U(F) \ U(𝔸_f) / K_f`**:
the exact double-coset space indexing the Hermitian genus of `(E/F, σ, J, L)`. -/
def HermGenusClassSet (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (L : Submodule (𝓞 E) (Fin M → E)) : Type _ :=
  DoubleCosetClassSet (UnitaryRatSubgroup F E σ J) (HermLatticeStab F E σ J L)

/-- Canonical lattice associated to a coset representative `g ∈ U(𝔸_{F,f})`:
`L_g = { x ∈ E^M | g⁻¹ · (1 ⊗ x) ∈ L̂ }`. -/
def twistedRationalLattice (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (L : Submodule (𝓞 E) (Fin M → E)) (g : UnitaryAdelicGrp F E σ J) :
    Submodule (𝓞 E) (Fin M → E) where
  carrier := { x : Fin M → E | adelicMulVec F E σ J g⁻¹ (diagLatVec F E x) ∈ adelicLatHat F E L }
  zero_mem' := by
    change adelicMulVec F E σ J g⁻¹ (diagLatVec F E (0 : Fin M → E)) ∈ adelicLatHat F E L
    have h0 : diagLatVec F E (0 : Fin M → E) = 0 := by funext i; simp [diagLatVec]
    rw [h0]
    simp [adelicMulVec, (adelicLatHat F E L).zero_mem]
  add_mem' {x y} hx hy := by
    change adelicMulVec F E σ J g⁻¹ (diagLatVec F E (x + y)) ∈ adelicLatHat F E L
    have hadd : diagLatVec F E (x + y) = diagLatVec F E x + diagLatVec F E y := by
      funext i; simp [diagLatVec, TensorProduct.tmul_add]
    rw [hadd]
    simpa [adelicMulVec, Matrix.mulVec_add] using (adelicLatHat F E L).add_mem hx hy
  smul_mem' r x hx := by
    change adelicMulVec F E σ J g⁻¹ (diagLatVec F E (r • x)) ∈ adelicLatHat F E L
    let α : FinAdeleF F ⊗[F] E := (1 : FinAdeleF F) ⊗ₜ[F] (r : E)
    have hsmul : diagLatVec F E (r • x) = fun i => α * diagLatVec F E x i := by
      funext i
      change (1 : FinAdeleF F) ⊗ₜ[F] ((r : E) * x i) =
        ((1 : FinAdeleF F) ⊗ₜ[F] (r : E)) * ((1 : FinAdeleF F) ⊗ₜ[F] x i)
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have hmulVec : adelicMulVec F E σ J g⁻¹ (fun i => α * diagLatVec F E x i) =
        fun i => α * adelicMulVec F E σ J g⁻¹ (diagLatVec F E x) i := by
      funext i
      simp only [adelicMulVec, Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [hsmul, hmulVec]
    have hhat : ∀ z ∈ adelicLatHat F E L,
        (fun i => α * z i) ∈ adelicLatHat F E L := by
      intro z hz
      induction hz using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, ha, w, hw, rfl⟩ := hy
        refine AddSubgroup.subset_closure ⟨a, ha, r • w, L.smul_mem r hw, ?_⟩
        funext i
        change ((1 : FinAdeleF F) ⊗ₜ[F] (r : E)) * (a ⊗ₜ[F] w i) = a ⊗ₜ[F] ((r : E) * w i)
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      | zero =>
        have h0 : (fun i : Fin M => α * (0 : Fin M → FinAdeleF F ⊗[F] E) i) = 0 := by
          funext i; simp
        rw [h0]
        exact (adelicLatHat F E L).zero_mem
      | add z₁ z₂ _ _ h₁ h₂ =>
        have hadd : (fun i => α * (z₁ + z₂) i) =
            (fun i => α * z₁ i) + (fun i => α * z₂ i) := by
          funext i; simp [mul_add]
        rw [hadd]
        exact (adelicLatHat F E L).add_mem h₁ h₂
      | neg z₁ _ h₁ =>
        have hneg : (fun i => α * (-z₁) i) = -(fun i => α * z₁ i) := by
          funext i; simp [mul_neg]
        rw [hneg]
        exact (adelicLatHat F E L).neg_mem h₁
    exact hhat _ hx

end FiniteAdelicClassSet

/-! ### Section 2b: Concrete Definite Hermitian Lattice Genus Class Sets (`Stage11DefiniteUnitaryChain`) -/

section ConcreteLatticeGenus

open RHDirect.Stage11DefiniteUnitaryChain

/-- Definite unitary equivalence relation on `HermitianLattice N`: `L₁` and `L₂` are isometric
if there exists `g ∈ U(N)` carrying `L₁.lat` onto `L₂.lat`. -/
def definiteIsoSetoid (N : ℕ) : Setoid (HermitianLattice N) where
  r L₁ L₂ := ∃ g : Matrix.unitaryGroup (Fin N) ℂ,
    ∀ v, v ∈ L₁.lat ↔ unitaryAction g v ∈ L₂.lat
  iseqv := by
    refine ⟨fun L => ⟨1, fun v => by simp [unitaryAction_one]⟩, ?_, ?_⟩
    · rintro L₁ L₂ ⟨g, hg⟩
      refine ⟨g⁻¹, fun v => ?_⟩
      have h := hg (unitaryAction g⁻¹ v)
      rw [← unitaryAction_mul, mul_inv_cancel, unitaryAction_one] at h
      exact h.symm
    · rintro L₁ L₂ L₃ ⟨g₁, h₁⟩ ⟨g₂, h₂⟩
      refine ⟨g₂ * g₁, fun v => ?_⟩
      rw [unitaryAction_mul, h₁ v, h₂ (unitaryAction g₁ v)]

/-- Concrete genus class set for any predicate `P : HermitianLattice N → Prop`. -/
def ConcreteLatticeGenusClassSet {N : ℕ} (P : HermitianLattice N → Prop) : Type _ :=
  Quotient (Setoid.comap (Subtype.val : { L : HermitianLattice N // P L } → HermitianLattice N)
    (definiteIsoSetoid N))

/-- Bridge turning any finite `DoubleCosetClassSet Γ K` with a family of definite lattices
into a `Stage11DefiniteUnitaryChain.HermitianGenus N`. -/
def toHermitianGenus {N : ℕ} {G : Type} [Group G] (Γ K : Subgroup G)
    [Fintype (DoubleCosetClassSet Γ K)] [DecidableEq (DoubleCosetClassSet Γ K)]
    (latOf : DoubleCosetClassSet Γ K → HermitianLattice N) : HermitianGenus N where
  idx := DoubleCosetClassSet Γ K
  lat := latOf

end ConcreteLatticeGenus

/-! ## Section 3: Canonical `GenusClassWeight` (`1 / |Aut(L_i)|`), Positivity & Denominator Clearing -/

section GenusClassWeights

variable {G : Type*} [Group G]

/-- Unquotiented stabilizer weight `1 / |Stab_{Γ, K}(g)|` at a group element `g : G`. -/
def doubleCosetWeight (Γ K : Subgroup G) (g : G) : ℝ :=
  ((Nat.card (doubleCosetStab Γ K g) : ℕ) : ℝ)⁻¹

/-- Complex-valued stabilizer weight `1 / |Stab_{Γ, K}(g)|`. -/
def doubleCosetWeightℂ (Γ K : Subgroup G) (g : G) : ℂ :=
  ((Nat.card (doubleCosetStab Γ K g) : ℕ) : ℂ)⁻¹

theorem doubleCosetWeight_eq_of_mk_eq {Γ K : Subgroup G} {g₁ g₂ : G}
    (h : doubleCosetMk Γ K g₁ = doubleCosetMk Γ K g₂) :
    doubleCosetWeight Γ K g₁ = doubleCosetWeight Γ K g₂ := by
  unfold doubleCosetWeight
  rw [card_doubleCosetStab_eq_of_mk_eq h]

theorem doubleCosetWeightℂ_eq_of_mk_eq {Γ K : Subgroup G} {g₁ g₂ : G}
    (h : doubleCosetMk Γ K g₁ = doubleCosetMk Γ K g₂) :
    doubleCosetWeightℂ Γ K g₁ = doubleCosetWeightℂ Γ K g₂ := by
  unfold doubleCosetWeightℂ
  rw [card_doubleCosetStab_eq_of_mk_eq h]

/-- **Canonical `GenusClassWeight` (`1 / |Aut(L_i)|`)** well-defined on the double-coset
quotient `DoubleCosetClassSet Γ K = Γ \ G / K`. -/
def GenusClassWeight (Γ K : Subgroup G) (c : DoubleCosetClassSet Γ K) : ℝ :=
  Quotient.lift (doubleCosetWeight Γ K) (fun _ _ h =>
    doubleCosetWeight_eq_of_mk_eq (Quotient.sound h)) c

/-- Complex-valued canonical `GenusClassWeightℂ` on `DoubleCosetClassSet Γ K`. -/
def GenusClassWeightℂ (Γ K : Subgroup G) (c : DoubleCosetClassSet Γ K) : ℂ :=
  Quotient.lift (doubleCosetWeightℂ Γ K) (fun _ _ h =>
    doubleCosetWeightℂ_eq_of_mk_eq (Quotient.sound h)) c

/-- Concrete **Hermitian Adelic Genus Class Weight `1 / |Aut(L_i)|`** on `HermGenusClassSet`. -/
def HermGenusClassWeight {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (L : Submodule (𝓞 E) (Fin M → E)) :
    HermGenusClassSet F E σ J L → ℝ :=
  GenusClassWeight (UnitaryRatSubgroup F E σ J) (HermLatticeStab F E σ J L)

@[simp]
theorem genusClassWeight_mk (Γ K : Subgroup G) (g : G) :
    GenusClassWeight Γ K (doubleCosetMk Γ K g) =
      ((Nat.card (doubleCosetStab Γ K g) : ℕ) : ℝ)⁻¹ :=
  rfl

@[simp]
theorem genusClassWeightℂ_mk (Γ K : Subgroup G) (g : G) :
    GenusClassWeightℂ Γ K (doubleCosetMk Γ K g) =
      ((Nat.card (doubleCosetStab Γ K g) : ℕ) : ℂ)⁻¹ :=
  rfl

theorem genusClassWeight_eq_at_rep (Γ K : Subgroup G) (s : DoubleCosetReps Γ K)
    (c : DoubleCosetClassSet Γ K) :
    GenusClassWeight Γ K c = ((Nat.card (doubleCosetStab Γ K (s.rep c)) : ℕ) : ℝ)⁻¹ := by
  conv_lhs => rw [← s.mk_rep c]
  exact genusClassWeight_mk Γ K (s.rep c)

theorem genusClassWeightℂ_eq_coe (Γ K : Subgroup G) (c : DoubleCosetClassSet Γ K) :
    GenusClassWeightℂ Γ K c = (GenusClassWeight Γ K c : ℂ) := by
  obtain ⟨g, rfl⟩ := Quotient.exists_rep c
  rw [← doubleCosetMk_eq_quotient_mk, genusClassWeightℂ_mk, genusClassWeight_mk]
  push_cast
  rfl

theorem genusClassWeight_nonneg (Γ K : Subgroup G) (c : DoubleCosetClassSet Γ K) :
    0 ≤ GenusClassWeight Γ K c := by
  obtain ⟨g, rfl⟩ := Quotient.exists_rep c
  rw [← doubleCosetMk_eq_quotient_mk, genusClassWeight_mk]
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

theorem genusClassWeight_pos (Γ K : Subgroup G) (c : DoubleCosetClassSet Γ K)
    (hfin : ∀ g : G, Finite (doubleCosetStab Γ K g)) :
    0 < GenusClassWeight Γ K c := by
  obtain ⟨g, rfl⟩ := Quotient.exists_rep c
  rw [← doubleCosetMk_eq_quotient_mk, genusClassWeight_mk]
  have := hfin g
  have hne : Nonempty (doubleCosetStab Γ K g) := ⟨1⟩
  exact inv_pos.mpr (Nat.cast_pos.mpr Nat.card_pos)

theorem genusClassWeight_le_one (Γ K : Subgroup G) (c : DoubleCosetClassSet Γ K)
    (hfin : ∀ g : G, Finite (doubleCosetStab Γ K g)) :
    GenusClassWeight Γ K c ≤ 1 := by
  obtain ⟨g, rfl⟩ := Quotient.exists_rep c
  rw [← doubleCosetMk_eq_quotient_mk, genusClassWeight_mk]
  have := hfin g
  have hne : Nonempty (doubleCosetStab Γ K g) := ⟨1⟩
  have h1 : (1 : ℝ) ≤ Nat.card (doubleCosetStab Γ K g) := by
    exact_mod_cast Nat.succ_le_of_lt Nat.card_pos
  exact inv_le_one_of_one_le₀ h1

/-- Stabilizer cardinality attached to a double coset `c : DoubleCosetClassSet Γ K`. -/
def genusClassStabCard (Γ K : Subgroup G) (c : DoubleCosetClassSet Γ K) : ℕ :=
  Quotient.lift (fun g => Nat.card (doubleCosetStab Γ K g)) (fun _ _ h =>
    card_doubleCosetStab_eq_of_mk_eq (Quotient.sound h)) c

@[simp]
theorem genusClassStabCard_mk (Γ K : Subgroup G) (g : G) :
    genusClassStabCard Γ K (doubleCosetMk Γ K g) = Nat.card (doubleCosetStab Γ K g) :=
  rfl

theorem genusClassStabCard_pos (Γ K : Subgroup G) (c : DoubleCosetClassSet Γ K)
    (hfin : ∀ g : G, Finite (doubleCosetStab Γ K g)) :
    0 < genusClassStabCard Γ K c := by
  obtain ⟨g, rfl⟩ := Quotient.exists_rep c
  rw [← doubleCosetMk_eq_quotient_mk, genusClassStabCard_mk]
  have := hfin g
  have hne : Nonempty (doubleCosetStab Γ K g) := ⟨1⟩
  exact Nat.card_pos

theorem genusClassWeight_eq_inv_stabCard (Γ K : Subgroup G) (c : DoubleCosetClassSet Γ K) :
    GenusClassWeight Γ K c = (genusClassStabCard Γ K c : ℝ)⁻¹ := by
  obtain ⟨g, rfl⟩ := Quotient.exists_rep c
  rw [← doubleCosetMk_eq_quotient_mk, genusClassWeight_mk, genusClassStabCard_mk]

/-- Total Siegel–Tamagawa genus mass `∑ c, 1 / |Aut(L_c)|` over `DoubleCosetClassSet Γ K`. -/
def genusClassMass (Γ K : Subgroup G) [Fintype (DoubleCosetClassSet Γ K)] : ℝ :=
  ∑ c : DoubleCosetClassSet Γ K, GenusClassWeight Γ K c

theorem genusClassMass_nonneg (Γ K : Subgroup G) [Fintype (DoubleCosetClassSet Γ K)] :
    0 ≤ genusClassMass Γ K :=
  Finset.sum_nonneg fun c _ => genusClassWeight_nonneg Γ K c

theorem genusClassMass_pos (Γ K : Subgroup G) [Fintype (DoubleCosetClassSet Γ K)]
    [Nonempty (DoubleCosetClassSet Γ K)] (hfin : ∀ g : G, Finite (doubleCosetStab Γ K g)) :
    0 < genusClassMass Γ K :=
  Finset.sum_pos (fun c _ => genusClassWeight_pos Γ K c hfin) Finset.univ_nonempty

/-- Universal genus denominator `D_Γ = ∏ c, |Aut(L_c)|` clearing all Petersson weights. -/
def genusClassDenom (Γ K : Subgroup G) [Fintype (DoubleCosetClassSet Γ K)] : ℕ :=
  ∏ c : DoubleCosetClassSet Γ K, genusClassStabCard Γ K c

theorem genusClassDenom_pos (Γ K : Subgroup G) [Fintype (DoubleCosetClassSet Γ K)]
    (hfin : ∀ g : G, Finite (doubleCosetStab Γ K g)) :
    0 < genusClassDenom Γ K :=
  Finset.prod_pos fun c _ => genusClassStabCard_pos Γ K c hfin

theorem genusClassStabCard_dvd_denom (Γ K : Subgroup G) [Fintype (DoubleCosetClassSet Γ K)]
    (c : DoubleCosetClassSet Γ K) :
    genusClassStabCard Γ K c ∣ genusClassDenom Γ K :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ c)

/-- Every genus class weight becomes an exact integer upon multiplying by `genusClassDenom Γ K`. -/
theorem genusClassDenom_mul_weight_int (Γ K : Subgroup G) [Fintype (DoubleCosetClassSet Γ K)]
    (hfin : ∀ g : G, Finite (doubleCosetStab Γ K g)) (c : DoubleCosetClassSet Γ K) :
    ∃ z : ℤ, (genusClassDenom Γ K : ℂ) * GenusClassWeightℂ Γ K c = z := by
  obtain ⟨q, hq⟩ := genusClassStabCard_dvd_denom Γ K c
  refine ⟨(q : ℤ), ?_⟩
  rw [genusClassWeightℂ_eq_coe, genusClassWeight_eq_inv_stabCard, hq]
  have hpos : (genusClassStabCard Γ K c : ℂ) ≠ 0 := by
    exact_mod_cast (genusClassStabCard_pos Γ K c hfin).ne'
  push_cast
  field_simp [hpos]

/-- Agreement of `GenusClassWeight` with `Stage11DefiniteUnitaryChain.peterssonWeight`
when each coset's lattice automorphism group has the same cardinality as `doubleCosetStab`. -/
theorem peterssonWeight_eq_genusClassWeight {N : ℕ} {G : Type} [Group G] (Γ K : Subgroup G)
    [Fintype (DoubleCosetClassSet Γ K)] [DecidableEq (DoubleCosetClassSet Γ K)]
    (latOf : DoubleCosetClassSet Γ K → Stage11DefiniteUnitaryChain.HermitianLattice N)
    (hcard : ∀ c, Nat.card (Stage11DefiniteUnitaryChain.DefiniteUnitaryGroup (latOf c)) =
      genusClassStabCard Γ K c)
    (c : DoubleCosetClassSet Γ K) :
    Stage11DefiniteUnitaryChain.peterssonWeight (toHermitianGenus Γ K latOf) c =
      GenusClassWeight Γ K c := by
  simp only [Stage11DefiniteUnitaryChain.peterssonWeight, toHermitianGenus, hcard,
    genusClassWeight_eq_inv_stabCard]

end GenusClassWeights

/-! ## Section 4: Unconditional Finiteness (`genus_class_finite`) & Minkowski Mod-3 Rigidity -/

section GenusFiniteness

/-! ### 4A. Minkowski Mod-3 Torsion-Free Rigidity (`|H| ≤ 3^(d^2)` uniformly for finite `H ≤ GL_d(ℤ)`) -/

private lemma padic_mod3_order_prime_step {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ)
    (hA_ne : A ≠ 1) (p : ℕ) (hp : p.Prime) (hp_pow : A ^ p = 1)
    (hmod3 : ∀ i j, (A i j : ZMod 3) = (1 : Matrix (Fin d) (Fin d) (ZMod 3)) i j) :
    False := by
  classical
  let B : Matrix (Fin d) (Fin d) ℤ := A - 1
  have hB_ne : B ≠ 0 := sub_ne_zero.mpr hA_ne
  have hB_div3 : ∀ i j, (3 : ℤ) ∣ B i j := by
    intro i j
    have h0 : ((B i j : ℤ) : ZMod 3) = 0 := by
      simp only [B, Matrix.sub_apply, Int.cast_sub, hmod3 i j, Matrix.one_apply]
      split_ifs <;> simp
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (B i j) 3).mp h0
  have hbound : ∃ n : ℕ, ∀ m : ℕ, (∀ i j, ((3 : ℤ) ^ m) ∣ B i j) → m ≤ n := by
    have hex : ∃ i₀ j₀, B i₀ j₀ ≠ 0 := by
      by_contra h
      push Not at h
      exact hB_ne (Matrix.ext h)
    obtain ⟨i₀, j₀, hnz⟩ := hex
    refine ⟨(B i₀ j₀).natAbs, fun m hm => ?_⟩
    have hdvd : (3 ^ m : ℕ) ∣ (B i₀ j₀).natAbs := by
      have := hm i₀ j₀
      rw [← Int.natCast_dvd]
      simpa using this
    have hle : 3 ^ m ≤ (B i₀ j₀).natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hnz) hdvd
    have hm_lt : m < 3 ^ m := Nat.lt_pow_self (by norm_num)
    omega
  obtain ⟨Nmax, hNmax⟩ := hbound
  let P : ℕ → Prop := fun m => ∀ i j, ((3 : ℤ) ^ m) ∣ B i j
  have hP1 : P 1 := fun i j => by simpa using hB_div3 i j
  let S : Finset ℕ := (Finset.range (Nmax + 1)).filter P
  have h1_le_N : 1 ≤ Nmax := hNmax 1 hP1
  have h1S : 1 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hP1⟩
  let k := S.max' ⟨1, h1S⟩
  have hk_mem : k ∈ S := Finset.max'_mem S ⟨1, h1S⟩
  have hk_ge1 : 1 ≤ k := Finset.le_max' S 1 h1S
  have hk_P : P k := (Finset.mem_filter.mp hk_mem).2
  have hk1_not : ¬ P (k + 1) := by
    intro hP'
    have hle := hNmax (k + 1) hP'
    have hmem' : k + 1 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hP'⟩
    have hle' := Finset.le_max' S (k + 1) hmem'
    omega
  let C : Matrix (Fin d) (Fin d) ℤ := Matrix.of fun i j => B i j / ((3 : ℤ) ^ k)
  have hB_eq : B = ((3 : ℤ) ^ k) • C := by
    ext i j
    simp only [C, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    exact (Int.mul_ediv_cancel' (hk_P i j)).symm
  have hC_not : ∃ i₀ j₀, ¬ (3 : ℤ) ∣ C i₀ j₀ := by
    by_contra h
    push Not at h
    apply hk1_not
    intro i j
    have h1 := h i j
    rw [hB_eq]
    simp only [Matrix.smul_apply, smul_eq_mul]
    obtain ⟨q, hq⟩ := h1
    rw [hq, pow_succ]
    exact ⟨q, by ring⟩
  obtain ⟨i₀, j₀, hi₀j₀⟩ := hC_not
  have hA_eq : A = ((3 : ℤ) ^ k) • C + 1 := by
    rw [← hB_eq, add_comm]
    simp [B]
  have hcomm : Commute (((3 : ℤ) ^ k) • C) (1 : Matrix (Fin d) (Fin d) ℤ) :=
    Commute.one_right _
  have hbin : A ^ p = ∑ m ∈ Finset.range (p + 1),
      (Nat.choose p m : ℤ) • ((1 : Matrix (Fin d) (Fin d) ℤ) ^ (p - m) *
        (((3 : ℤ) ^ k) • C) ^ m) := by
    rw [hA_eq, hcomm.add_pow]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [one_pow, mul_one, one_mul, zsmul_eq_mul, Int.cast_natCast]
    exact (Nat.cast_commute (p.choose m) _).symm
  rw [hp_pow] at hbin
  have hp2 : 2 ≤ p + 1 := by have := hp.two_le; omega
  have hsum_split : ∑ m ∈ Finset.range (p + 1),
      (Nat.choose p m : ℤ) • ((1 : Matrix (Fin d) (Fin d) ℤ) ^ (p - m) *
        (((3 : ℤ) ^ k) • C) ^ m) =
      1 + (p : ℤ) • (((3 : ℤ) ^ k) • C) +
        ∑ m ∈ Finset.Ico 2 (p + 1),
          (Nat.choose p m : ℤ) • ((1 : Matrix (Fin d) (Fin d) ℤ) ^ (p - m) *
            (((3 : ℤ) ^ k) • C) ^ m) := by
    rw [← Finset.sum_range_add_sum_Ico _ hp2]
    have h01 : ∑ m ∈ Finset.range 2, (Nat.choose p m : ℤ) •
        ((1 : Matrix (Fin d) (Fin d) ℤ) ^ (p - m) * (((3 : ℤ) ^ k) • C) ^ m) =
        1 + (p : ℤ) • (((3 : ℤ) ^ k) • C) := by
      simp [Finset.sum_range_succ]
    rw [h01]
  rw [hsum_split] at hbin
  have hzero : (p : ℤ) • (((3 : ℤ) ^ k) • C) +
      ∑ m ∈ Finset.Ico 2 (p + 1),
        (Nat.choose p m : ℤ) • ((1 : Matrix (Fin d) (Fin d) ℤ) ^ (p - m) *
          (((3 : ℤ) ^ k) • C) ^ m) = 0 := by
    have := congrArg (fun X => X - 1) hbin
    simpa [add_assoc] using this.symm
  by_cases hp3 : p = 3
  · subst hp3
    have hpow2 : (((3 : ℤ) ^ k) • C) ^ 2 = ((3 : ℤ) ^ (2 * k)) • (C ^ 2) := by
      rw [smul_pow, ← pow_mul, mul_comm k 2]
    have hpow3 : (((3 : ℤ) ^ k) • C) ^ 3 = ((3 : ℤ) ^ (3 * k)) • (C ^ 3) := by
      rw [smul_pow, ← pow_mul, mul_comm k 3]
    have hIco3 : Finset.Ico 2 4 = {2, 3} := by decide
    rw [hIco3, Finset.sum_pair (by decide)] at hzero
    simp only [Nat.reduceSub, one_pow, one_mul, hpow2, hpow3] at hzero
    have hdvd_k2 : (3 : ℤ) ^ (k + 2) ∣ ((3 : ℤ) * (3 : ℤ) ^ k * C i₀ j₀) := by
      have hent := congrArg (fun M : Matrix (Fin d) (Fin d) ℤ => M i₀ j₀) hzero
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] at hent
      push_cast at hent
      have h2k : (3 : ℤ) ^ (k + 2) ∣
          ((Nat.choose 3 2 : ℕ) : ℤ) * ((3 : ℤ) ^ (2 * k) * (C ^ 2) i₀ j₀) := by
        have hpow_le : k + 2 ≤ 2 * k + 1 := by omega
        obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hpow_le
        refine ⟨(C ^ 2) i₀ j₀ * (3 : ℤ) ^ r, ?_⟩
        have hch : ((Nat.choose 3 2 : ℕ) : ℤ) = 3 := by decide
        rw [hch, ← mul_assoc, show (3 : ℤ) * (3 : ℤ) ^ (2 * k) = (3 : ℤ) ^ (2 * k + 1) by
          rw [pow_succ']]
        rw [hr, pow_add]
        ring
      have h3k : (3 : ℤ) ^ (k + 2) ∣
          ((Nat.choose 3 3 : ℕ) : ℤ) * ((3 : ℤ) ^ (3 * k) * (C ^ 3) i₀ j₀) := by
        have hpow_le : k + 2 ≤ 3 * k := by omega
        obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hpow_le
        refine ⟨(C ^ 3) i₀ j₀ * (3 : ℤ) ^ r, ?_⟩
        have hch : ((Nat.choose 3 3 : ℕ) : ℤ) = 1 := by decide
        rw [hch, one_mul, hr, pow_add]
        ring
      have hsum_dvd : (3 : ℤ) ^ (k + 2) ∣
          ((Nat.choose 3 2 : ℕ) : ℤ) * ((3 : ℤ) ^ (2 * k) * (C ^ 2) i₀ j₀) +
          ((Nat.choose 3 3 : ℕ) : ℤ) * ((3 : ℤ) ^ (3 * k) * (C ^ 3) i₀ j₀) :=
        dvd_add h2k h3k
      have heq : (3 : ℤ) * (3 : ℤ) ^ k * C i₀ j₀ =
          -(((Nat.choose 3 2 : ℕ) : ℤ) * ((3 : ℤ) ^ (2 * k) * (C ^ 2) i₀ j₀) +
            ((Nat.choose 3 3 : ℕ) : ℤ) * ((3 : ℤ) ^ (3 * k) * (C ^ 3) i₀ j₀)) := by
        linarith
      rw [heq]
      exact hsum_dvd.neg_right
    have hpow_eq : (3 : ℤ) ^ (k + 2) = (3 : ℤ) ^ (k + 1) * 3 := by rw [pow_succ]
    have hpow_eq2 : (3 : ℤ) * (3 : ℤ) ^ k * C i₀ j₀ = (3 : ℤ) ^ (k + 1) * C i₀ j₀ := by
      rw [pow_succ']
    rw [hpow_eq, hpow_eq2] at hdvd_k2
    have hne0 : (3 : ℤ) ^ (k + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    exact hi₀j₀ (Int.dvd_of_mul_dvd_mul_left hne0 hdvd_k2)
  · have hdvd_k1 : (3 : ℤ) ^ (k + 1) ∣ ((p : ℤ) * (3 : ℤ) ^ k * C i₀ j₀) := by
      have hent := congrArg (fun M : Matrix (Fin d) (Fin d) ℤ => M i₀ j₀) hzero
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, Matrix.zero_apply,
        smul_eq_mul] at hent
      have htail : (3 : ℤ) ^ (k + 1) ∣
          ∑ m ∈ Finset.Ico 2 (p + 1),
            (Nat.choose p m : ℤ) * (((1 : Matrix (Fin d) (Fin d) ℤ) ^ (p - m) *
              (((3 : ℤ) ^ k) • C) ^ m) i₀ j₀) := by
        refine Finset.dvd_sum fun m hm => ?_
        have hm2 : 2 ≤ m := (Finset.mem_Ico.mp hm).1
        rw [one_pow, one_mul, smul_pow, Matrix.smul_apply, smul_eq_mul, ← pow_mul]
        have hle : k + 1 ≤ k * m := by nlinarith
        obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hle
        refine dvd_mul_of_dvd_right (dvd_mul_of_dvd_left ⟨(3 : ℤ) ^ r, ?_⟩ _) _
        rw [hr, pow_add]
      have heq : (p : ℤ) * (3 : ℤ) ^ k * C i₀ j₀ =
          -(∑ m ∈ Finset.Ico 2 (p + 1),
            (Nat.choose p m : ℤ) * (((1 : Matrix (Fin d) (Fin d) ℤ) ^ (p - m) *
              (((3 : ℤ) ^ k) • C) ^ m) i₀ j₀)) := by
        linarith
      rw [heq]
      exact htail.neg_right
    have hpow_eq : (3 : ℤ) ^ (k + 1) = (3 : ℤ) ^ k * 3 := by rw [pow_succ]
    have hmul_eq : (p : ℤ) * (3 : ℤ) ^ k * C i₀ j₀ = (3 : ℤ) ^ k * ((p : ℤ) * C i₀ j₀) := by
      ring
    rw [hpow_eq, hmul_eq] at hdvd_k1
    have hne0 : (3 : ℤ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    have h3dvd : (3 : ℤ) ∣ (p : ℤ) * C i₀ j₀ := Int.dvd_of_mul_dvd_mul_left hne0 hdvd_k1
    have h3prime : Prime (3 : ℤ) := Int.prime_three
    rcases h3prime.dvd_or_dvd h3dvd with h3p | h3C
    · have h3p_nat : 3 ∣ p := Int.natCast_dvd_natCast.mp h3p
      exact hp3 ((Nat.prime_dvd_prime_iff_eq (by decide) hp).mp h3p_nat).symm
    · exact hi₀j₀ h3C

/-- **Minkowski Mod-3 Rigidity Theorem**: any finite subgroup `H` of `GL_d(ℤ)` embeds
injectively into `M_d(ℤ/3ℤ)` under reduction modulo `3`. -/
theorem minkowski_mod_three_inj {d : ℕ} {H : Type*} [Group H] [Finite H]
    (ρ : H →* Matrix (Fin d) (Fin d) ℤ) (hρ : Function.Injective ρ) :
    Function.Injective (fun h : H => (ρ h).map (Int.castRingHom (ZMod 3))) := by
  let : Fintype H := Fintype.ofFinite H
  let red : Matrix (Fin d) (Fin d) ℤ →+* Matrix (Fin d) (Fin d) (ZMod 3) :=
    (Int.castRingHom (ZMod 3)).mapMatrix
  have hker : ∀ g : H, red (ρ g) = 1 → g = 1 := by
    intro g hg
    by_contra hg1
    have hord_ne1 : orderOf g ≠ 1 := fun h1 => hg1 (orderOf_eq_one_iff.mp h1)
    have hord_gt : 1 < orderOf g := Nat.lt_of_le_of_ne (orderOf_pos g) hord_ne1.symm
    let p := (orderOf g).minFac
    have hp : p.Prime := Nat.minFac_prime hord_gt.ne'
    have hpdvd : p ∣ orderOf g := Nat.minFac_dvd (orderOf g)
    have hq_pos : 0 < orderOf g / p := Nat.div_pos (Nat.le_of_dvd (orderOf_pos g) hpdvd) hp.pos
    have hq_lt : orderOf g / p < orderOf g := Nat.div_lt_self (orderOf_pos g) hp.one_lt
    let h : H := g ^ (orderOf g / p)
    have hh_ne : h ≠ 1 := pow_ne_one_of_lt_orderOf hq_pos.ne' hq_lt
    have hh_pow : h ^ p = 1 := by
      dsimp only [h]
      rw [← pow_mul, Nat.div_mul_cancel hpdvd, pow_orderOf_eq_one]
    have hA_ne : ρ h ≠ 1 := fun h1 => hh_ne (hρ (h1.trans (map_one ρ).symm))
    have hA_pow : (ρ h) ^ p = 1 := by rw [← map_pow, hh_pow, map_one]
    have hmod : red (ρ h) = 1 := by
      dsimp only [h]
      rw [map_pow, map_pow, hg, one_pow]
    exact padic_mod3_order_prime_step (ρ h) hA_ne p hp hA_pow
      (fun i j => congrFun (congrFun hmod i) j)
  intro h₁ h₂ heq
  have heq' : red (ρ h₁) = red (ρ h₂) := heq
  have h12 : red (ρ (h₁ * h₂⁻¹)) = 1 := by
    have hprod : red (ρ (h₁ * h₂⁻¹)) * red (ρ h₂) = red (ρ h₁) := by
      rw [← map_mul, ← map_mul, inv_mul_cancel_right]
    have hinv : red (ρ h₂) * red (ρ h₂⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]
    calc red (ρ (h₁ * h₂⁻¹))
        = red (ρ (h₁ * h₂⁻¹)) * (red (ρ h₂) * red (ρ h₂⁻¹)) := by rw [hinv, Matrix.mul_one]
      _ = (red (ρ (h₁ * h₂⁻¹)) * red (ρ h₂)) * red (ρ h₂⁻¹) := by rw [Matrix.mul_assoc]
      _ = red (ρ h₂) * red (ρ h₂⁻¹) := by rw [hprod, heq']
      _ = 1 := hinv
  exact mul_inv_eq_one.mp (hker (h₁ * h₂⁻¹) h12)

/-- Uniform Minkowski stabilizer cardinality bound `|H| ≤ 3 ^ (d * d)` for every finite
subgroup `H` embedding into `M_d(ℤ)`. -/
theorem minkowski_mod_three_stabilizer_bound {d : ℕ} {H : Type*} [Group H] [Finite H]
    (ρ : H →* Matrix (Fin d) (Fin d) ℤ) (hρ : Function.Injective ρ) :
    Nat.card H ≤ 3 ^ (d * d) := by
  have : Fintype H := Fintype.ofFinite H
  have hinj := minkowski_mod_three_inj ρ hρ
  have hle := Fintype.card_le_of_injective _ hinj
  have hcard : Fintype.card (Matrix (Fin d) (Fin d) (ZMod 3)) = 3 ^ (d * d) := by
    change Fintype.card (Fin d → Fin d → ZMod 3) = 3 ^ (d * d)
    simp [ZMod.card, pow_mul]
  rw [Nat.card_eq_fintype_card]
  exact hle.trans_eq hcard

/-- **Uniform Definite Unitary Stabilizer Bound**: for EVERY rank-`N` positive-definite
Hermitian lattice `L : HermitianLattice N`, `|Aut(L)| ≤ 3 ^ (4 * N^2)`. -/
theorem card_definiteUnitaryGroup_le_pow {N : ℕ}
    (L : Stage11DefiniteUnitaryChain.HermitianLattice N) :
    Nat.card (Stage11DefiniteUnitaryChain.DefiniteUnitaryGroup L) ≤ 3 ^ ((2 * N) * (2 * N)) := by
  let b := L.zBasis
  let restrictAut : Stage11DefiniteUnitaryChain.DefiniteUnitaryGroup L →* (L.lat →ₗ[ℤ] L.lat) :=
    { toFun := fun g =>
        { toFun := fun x =>
            ⟨Stage11DefiniteUnitaryChain.unitaryAction g.1 x.1,
              (g.2 x.1).mp x.2⟩
          map_add' := fun x y => Subtype.ext (map_add _ x.1 y.1)
          map_smul' := fun c x => Subtype.ext (map_zsmul _ c x.1) }
      map_one' := by ext x; simp [Stage11DefiniteUnitaryChain.unitaryAction_one]
      map_mul' := fun g h => by ext x; simp [Stage11DefiniteUnitaryChain.unitaryAction_mul] }
  let ρ : Stage11DefiniteUnitaryChain.DefiniteUnitaryGroup L →*
      Matrix (Fin (2 * N)) (Fin (2 * N)) ℤ :=
    (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp restrictAut
  have hρ_inj : Function.Injective ρ := by
    intro g₁ g₂ heq
    have hres : restrictAut g₁ = restrictAut g₂ :=
      (LinearMap.toMatrixAlgEquiv b).injective heq
    apply Subtype.ext
    apply Stage11DefiniteUnitaryChain.unitaryAction_injective
    apply LinearIsometryEquiv.ext
    intro v
    have hspan : Submodule.span ℝ (L.lat : Set (Stage11DefiniteUnitaryChain.DefiniteHermitianSpace N)) = ⊤ :=
      IsZLattice.span_top (K := ℝ) (L := L.lat)
    have hv : v ∈ Submodule.span ℝ (L.lat : Set (Stage11DefiniteUnitaryChain.DefiniteHermitianSpace N)) := by
      rw [hspan]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx =>
      exact congrArg (fun f : L.lat →ₗ[ℤ] L.lat =>
        (f ⟨x, hx⟩ : Stage11DefiniteUnitaryChain.DefiniteHermitianSpace N)) hres
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => rw [← Complex.coe_smul, map_smul, map_smul, hx]
  exact minkowski_mod_three_stabilizer_bound ρ hρ_inj

/-! ### 4B. Unconditional Finiteness of Double-Coset Genus Class Sets (`genus_class_finite`) -/

/-- **Unconditional Measure-Theoretic Genus Finiteness (`genus_class_finite_of_finite_volume`)**:
If `μ` is a left-invariant measure on `G`, `𝓕` is a fundamental domain for `Γ` of finite measure
`μ 𝓕 < ⊤`, `K ≤ G` is measurable with `0 < μ K`, and stabilizers are uniformly bounded by `B`,
then `DoubleCosetClassSet Γ K` is **FINITE**! -/
theorem genus_class_finite_of_finite_volume {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] {Γ K : Subgroup G} [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant]
    (hK : MeasurableSet (K : Set G)) (hKpos : 0 < μ K)
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (h𝓕_lt : μ 𝓕 < ⊤)
    {B : ℕ} (_hBpos : 0 < B) (hstab_le : ∀ g : G, Finite (doubleCosetStab Γ K g) ∧
      Nat.card (doubleCosetStab Γ K g) ≤ B) :
    Finite (DoubleCosetClassSet Γ K) := by
  classical
  have : MeasurableConstSMul Γ G := ⟨fun γ => measurable_const_mul (γ : G)⟩
  have : SMulInvariantMeasure Γ G μ := ⟨fun γ s _ => measure_preimage_mul μ (γ : G) s⟩
  have hfin_bound : ∀ S : Finset (DoubleCosetClassSet Γ K),
      (S.card : ℝ≥0∞) * (μ K * (B : ℝ≥0∞)⁻¹) ≤ μ 𝓕 := by
    intro S
    let g : DoubleCosetClassSet Γ K → G := fun c => Quotient.out c
    let T : DoubleCosetClassSet Γ K → Set G := fun c => (fun y => (g c)⁻¹ * y) ⁻¹' (K : Set G)
    have hT : ∀ c, MeasurableSet (T c) := fun c => (measurable_const_mul _) hK
    let f : G → ℝ≥0∞ := fun y =>
      ∑ c ∈ S, ((Nat.card (doubleCosetStab Γ K (g c)) : ℝ≥0∞))⁻¹ * (T c).indicator 1 y
    have hf : Measurable f := Finset.measurable_sum _ fun c _ =>
      (measurable_one.indicator (hT c)).const_mul _
    have hG : ∫⁻ y, f y ∂μ =
        ∑ c ∈ S, μ K * ((Nat.card (doubleCosetStab Γ K (g c)) : ℝ≥0∞))⁻¹ := by
      rw [lintegral_finsetSum _ fun c _ => (measurable_one.indicator (hT c)).const_mul _]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [lintegral_const_mul _ (measurable_one.indicator (hT c)), lintegral_indicator_one (hT c),
        measure_preimage_mul, mul_comm]
    have hpt : ∀ x : G, ∑' γ : Γ, f (γ • x) ≤ 1 := by
      intro x
      set c₀ := doubleCosetMk Γ K x
      have hmk0 : doubleCosetMk Γ K (g c₀) = c₀ := by
        rw [doubleCosetMk_eq_quotient_mk]; exact Quotient.out_eq c₀
      obtain ⟨γ₀, hγ₀, κ₀, hκ₀, hx⟩ := (DoubleCoset.eq Γ K (g c₀) x).mp hmk0
      have hx' : x = (⟨γ₀, hγ₀⟩ : Γ) * g c₀ * (⟨κ₀, hκ₀⟩ : K) := hx
      let δ₀ : Γ := ⟨γ₀, hγ₀⟩
      let k₀ : K := ⟨κ₀, hκ₀⟩
      have hsum_c : ∀ c : DoubleCosetClassSet Γ K,
          ∑' γ : Γ, (T c).indicator (1 : G → ℝ≥0∞) (γ • x) =
            if c = c₀ then (Nat.card (doubleCosetStab Γ K (g c₀)) : ℝ≥0∞) else 0 := by
        intro c
        rw [hx']
        split_ifs with hc
        · subst hc
          have hstabFin : Finite (doubleCosetStab Γ K (g c₀)) := (hstab_le (g c₀)).1
          have hgenusAutFin : Finite (UnitaryMassFormula.genusAut Γ K (g c₀)) :=
            Finite.of_equiv (doubleCosetStab Γ K (g c₀))
              (Equiv.setCongr (Set.ext fun γ => mem_doubleCosetStab_iff_genusAut Γ K (g c₀) γ))
          have hfin' : (UnitaryMassFormula.doubleCosetHit Γ K (g c₀)
              ((δ₀ : G) * g c₀ * k₀)).Finite := by
            have hEq := UnitaryMassFormula.doubleCosetHitEquiv (g c₀) δ₀ k₀
            have : Finite (UnitaryMassFormula.doubleCosetHit Γ K (g c₀)
                ((δ₀ : G) * g c₀ * k₀)) := Finite.of_equiv _ hEq.symm
            exact Set.toFinite _
          have he : (fun γ : Γ => (T c₀).indicator (1 : G → ℝ≥0∞) (γ • ((δ₀ : G) * g c₀ * k₀))) =
              (UnitaryMassFormula.doubleCosetHit Γ K (g c₀) ((δ₀ : G) * g c₀ * k₀)).indicator 1 := by
            funext γ
            simp only [Set.indicator, T, UnitaryMassFormula.doubleCosetHit, Set.mem_preimage,
              Set.mem_ofPred_eq, Subgroup.smul_def, smul_eq_mul, SetLike.mem_coe, Pi.one_apply]
            rfl
          rw [he, ← _root_.tsum_subtype]
          have := hfin'.fintype
          rw [tsum_fintype]
          simp only [Pi.one_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
            Fintype.card_eq_nat_card]
          rw [Nat.card_congr (UnitaryMassFormula.doubleCosetHitEquiv (g c₀) δ₀ k₀)]
          congr 1
          exact Nat.card_congr (Equiv.setCongr (by
            ext γ; exact (mem_doubleCosetStab_iff_genusAut Γ K (g c₀) γ).symm))
        · have hempty : ∀ γ : Γ, γ • ((δ₀ : G) * g c₀ * k₀) ∉ T c := by
            intro γ hmem
            apply hc
            have hmem' : (g c)⁻¹ * ((γ : G) * ((δ₀ : G) * g c₀ * (k₀ : G))) ∈ K := hmem
            have hmk1 : doubleCosetMk Γ K (g c) = doubleCosetMk Γ K (g c₀) := by
              refine (DoubleCoset.eq Γ K (g c) (g c₀)).mpr ?_
              refine ⟨((γ * δ₀)⁻¹ : Γ), ((γ * δ₀)⁻¹ : Γ).2,
                ((⟨(g c)⁻¹ * ((γ : G) * ((δ₀ : G) * g c₀ * (k₀ : G))), hmem'⟩ : K) * k₀⁻¹ : K),
                K.mul_mem hmem' (K.inv_mem k₀.2), ?_⟩
              simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, mul_assoc]
              group
            have hc1 : doubleCosetMk Γ K (g c) = c := by
              rw [doubleCosetMk_eq_quotient_mk]; exact Quotient.out_eq c
            have hc2 : doubleCosetMk Γ K (g c₀) = c₀ := by
              rw [doubleCosetMk_eq_quotient_mk]; exact Quotient.out_eq c₀
            rw [← hc1, ← hc2]
            exact hmk1
          have hzero : (fun γ : Γ => (T c).indicator (1 : G → ℝ≥0∞)
              (γ • ((δ₀ : G) * g c₀ * k₀))) = 0 := by
            funext γ
            simp [Set.indicator_of_notMem (hempty γ)]
          rw [hzero]
          simp
      have hswap : ∑' γ : Γ, f (γ • x) =
          ∑ c ∈ S, ((Nat.card (doubleCosetStab Γ K (g c)) : ℝ≥0∞))⁻¹ *
            ∑' γ : Γ, (T c).indicator (1 : G → ℝ≥0∞) (γ • x) := by
        simp only [f]
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [ENNReal.tsum_mul_left]
      rw [hswap]
      simp_rw [hsum_c]
      by_cases hc₀ : c₀ ∈ S
      · rw [Finset.sum_eq_single c₀]
        · rw [if_pos rfl]
          have hpos_stab : (Nat.card (doubleCosetStab Γ K (g c₀)) : ℝ≥0∞) ≠ 0 := by
            have := (hstab_le (g c₀)).1
            have hne : Nonempty (doubleCosetStab Γ K (g c₀)) := ⟨1⟩
            exact_mod_cast (Nat.card_pos (α := doubleCosetStab Γ K (g c₀))).ne'
          exact (ENNReal.inv_mul_cancel hpos_stab (ENNReal.natCast_ne_top _)).le
        · intro c _ hne
          rw [if_neg hne, mul_zero]
        · intro h; exact absurd hc₀ h
      · have hzero : ∀ c ∈ S, ((Nat.card (doubleCosetStab Γ K (g c)) : ℝ≥0∞))⁻¹ *
            (if c = c₀ then (Nat.card (doubleCosetStab Γ K (g c₀)) : ℝ≥0∞) else 0) = 0 := by
          intro c hc
          rw [if_neg (by rintro rfl; exact hc₀ hc), mul_zero]
        rw [Finset.sum_eq_zero hzero]
        exact zero_le_one
    have hmeas : ∀ γ : Γ, Measurable fun x => f (γ • x) := fun γ => hf.comp (measurable_const_smul γ)
    have hsum_le_F : ∑ c ∈ S, μ K * ((Nat.card (doubleCosetStab Γ K (g c)) : ℝ≥0∞))⁻¹ ≤ μ 𝓕 := by
      calc ∑ c ∈ S, μ K * ((Nat.card (doubleCosetStab Γ K (g c)) : ℝ≥0∞))⁻¹
          = ∫⁻ y, f y ∂μ := hG.symm
        _ = ∑' γ : Γ, ∫⁻ x in 𝓕, f (γ • x) ∂μ := h𝓕.lintegral_eq_tsum'' f
        _ = ∫⁻ x in 𝓕, ∑' γ : Γ, f (γ • x) ∂μ := (lintegral_tsum fun γ => (hmeas γ).aemeasurable).symm
        _ ≤ ∫⁻ _ in 𝓕, 1 ∂μ := setLIntegral_mono_ae measurable_one.aemeasurable
            (ae_of_all _ fun x _ => hpt x)
        _ = μ 𝓕 := setLIntegral_one 𝓕
    have hterm_le : ∀ c ∈ S, μ K * (B : ℝ≥0∞)⁻¹ ≤
        μ K * ((Nat.card (doubleCosetStab Γ K (g c)) : ℝ≥0∞))⁻¹ := by
      intro c _
      refine mul_le_mul' le_rfl ?_
      rw [ENNReal.inv_le_inv]
      exact_mod_cast (hstab_le (g c)).2
    calc (S.card : ℝ≥0∞) * (μ K * (B : ℝ≥0∞)⁻¹)
        = ∑ _c ∈ S, μ K * (B : ℝ≥0∞)⁻¹ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ c ∈ S, μ K * ((Nat.card (doubleCosetStab Γ K (g c)) : ℝ≥0∞))⁻¹ :=
          Finset.sum_le_sum hterm_le
      _ ≤ μ 𝓕 := hsum_le_F
  by_contra hinf
  have : Infinite (DoubleCosetClassSet Γ K) := not_finite_iff_infinite.mp hinf
  have hunit_pos : 0 < μ K * (B : ℝ≥0∞)⁻¹ := by
    refine ENNReal.mul_pos hKpos.ne' ?_
    simp [ENNReal.inv_eq_zero, ENNReal.natCast_ne_top]
  by_cases hKtop : μ K * (B : ℝ≥0∞)⁻¹ = ⊤
  · obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq (DoubleCosetClassSet Γ K) 1
    have hle := hfin_bound S
    rw [hS, hKtop, Nat.cast_one, one_mul] at hle
    exact (lt_of_le_of_lt hle h𝓕_lt).false
  · obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt hunit_pos.ne' h𝓕_lt.ne
    obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq (DoubleCosetClassSet Γ K) N
    have hle := hfin_bound S
    rw [hS] at hle
    exact not_lt_of_ge hle hN

/-- **Sublevel Genus Finiteness (`genus_class_finite_sublevel`)**:
if `DoubleCosetClassSet Γ K` is finite and `K' ≤ K` has finite index (`Finite (K ⧸ K'.subgroupOf K)`),
then `DoubleCosetClassSet Γ K'` is also finite! -/
theorem genus_class_finite_sublevel {G : Type*} [Group G] {Γ K K' : Subgroup G}
    (_hKK' : K' ≤ K) [Finite (DoubleCosetClassSet Γ K)]
    [Finite (K ⧸ K'.subgroupOf K)] :
    Finite (DoubleCosetClassSet Γ K') := by
  let s := canonicalDoubleCosetReps Γ K
  let φ : DoubleCosetClassSet Γ K × (K ⧸ K'.subgroupOf K) → DoubleCosetClassSet Γ K' :=
    fun p => Quotient.liftOn' p.2 (fun k : K => doubleCosetMk Γ K' (s.rep p.1 * k)) fun k₁ k₂ h => by
      have hk : k₁⁻¹ * k₂ ∈ K'.subgroupOf K := QuotientGroup.leftRel_apply.mp h
      exact (DoubleCoset.eq Γ K' (s.rep p.1 * k₁) (s.rep p.1 * k₂)).mpr
        ⟨1, Γ.one_mem, (k₁⁻¹ * k₂ : K), hk, by simp [mul_assoc]⟩
  have hsurj : Function.Surjective φ := by
    intro c'
    obtain ⟨x, rfl⟩ := Quotient.exists_rep c'
    obtain ⟨c, γ, κ, hx⟩ := doubleCosetReps_covering Γ K s x
    refine ⟨(c, QuotientGroup.mk κ), ?_⟩
    rw [← doubleCosetMk_eq_quotient_mk]
    change doubleCosetMk Γ K' (s.rep c * κ) = doubleCosetMk Γ K' x
    refine (DoubleCoset.eq Γ K' (s.rep c * κ) x).mpr ?_
    refine ⟨γ, γ.2, 1, K'.one_mem, ?_⟩
    rw [hx]
    simp [mul_assoc]
  exact Finite.of_surjective φ hsurj

/-- **Concrete Definite Hermitian Lattice Subgenus Finiteness (`genus_class_finite`)**:
given any base definite Hermitian lattice `L₀ : HermitianLattice N` and positive integer
denominator bound `D ≥ 1`, the set of all intermediate `ℤ`-lattices `M` sandwiched between
`D • L₀.lat` and `L₀.lat` is **FINITE**! -/
theorem genus_class_finite {N : ℕ} (L₀ : Stage11DefiniteUnitaryChain.HermitianLattice N)
    (D : ℕ) (hD : 0 < D) :
    { M : Submodule ℤ (Stage11DefiniteUnitaryChain.DefiniteHermitianSpace N) |
        (D : ℤ) • L₀.lat ≤ M ∧ M ≤ L₀.lat }.Finite := by
  let Q := L₀.lat ⧸ ((D : ℤ) • (⊤ : Submodule ℤ L₀.lat))
  have hQ_fin : Finite Q := by
    let b := L₀.zBasis
    let e : L₀.lat ≃ₗ[ℤ] (Fin (2 * N) → ℤ) := b.equivFun
    let φ : L₀.lat →+ (Fin (2 * N) → ZMod D) :=
      { toFun := fun x i => (e x i : ZMod D)
        map_zero' := by ext i; simp
        map_add' := fun x y => by ext i; simp }
    have hker : ∀ x : L₀.lat, φ x = 0 ↔ x ∈ (D : ℤ) • (⊤ : Submodule ℤ L₀.lat) := by
      intro x
      constructor
      · intro hx
        have hdvd : ∀ i, (D : ℤ) ∣ e x i := fun i =>
          (ZMod.intCast_zmod_eq_zero_iff_dvd (e x i) D).mp (congrFun hx i)
        let y : L₀.lat := e.symm (fun i => e x i / (D : ℤ))
        have hxy : x = (D : ℤ) • y := by
          apply e.injective
          ext i
          simp only [y, LinearEquiv.apply_symm_apply, map_zsmul, Pi.smul_apply, smul_eq_mul]
          exact (Int.mul_ediv_cancel' (hdvd i)).symm
        rw [hxy]
        exact Submodule.smul_mem_pointwise_smul y (D : ℤ) (⊤ : Submodule ℤ L₀.lat) trivial
      · intro hx
        rw [Submodule.mem_smul_pointwise_iff_exists] at hx
        obtain ⟨y, _, rfl⟩ := hx
        ext i
        change ((e ((D : ℤ) • y) i : ℤ) : ZMod D) = 0
        rw [map_zsmul, Pi.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast,
          ZMod.natCast_self, zero_mul]
    have hinj : Function.Injective
        (QuotientAddGroup.lift ((D : ℤ) • (⊤ : Submodule ℤ L₀.lat)).toAddSubgroup φ
          (fun x hx => (hker x).mpr hx)) := by
      intro a b hab
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective a
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective b
      rw [QuotientAddGroup.eq]
      change -x + y ∈ (D : ℤ) • (⊤ : Submodule ℤ L₀.lat)
      rw [← hker]
      have hsub : φ (-x + y) = -φ x + φ y := by rw [map_add, map_neg]
      rw [hsub, neg_add_eq_zero]
      exact hab
    have : NeZero D := ⟨hD.ne'⟩
    exact Finite.of_injective _ hinj
  let S := { M : Submodule ℤ (Stage11DefiniteUnitaryChain.DefiniteHermitianSpace N) |
    (D : ℤ) • L₀.lat ≤ M ∧ M ≤ L₀.lat }
  let qMap : L₀.lat →ₗ[ℤ] Q := Submodule.mkQ ((D : ℤ) • (⊤ : Submodule ℤ L₀.lat))
  let ψ : S → Set Q := fun M =>
    (qMap '' { x : L₀.lat | (x : Stage11DefiniteUnitaryChain.DefiniteHermitianSpace N) ∈ M.1 })
  have hψ_inj : Function.Injective ψ := by
    intro M₁ M₂ heq
    apply Subtype.ext
    ext v
    have hv_iff : ∀ M : S, v ∈ M.1 ↔ ∃ hvL : v ∈ L₀.lat, qMap ⟨v, hvL⟩ ∈ ψ M := by
      intro M
      constructor
      · intro hvM
        have hvL : v ∈ L₀.lat := M.2.2 hvM
        exact ⟨hvL, ⟨⟨v, hvL⟩, hvM, rfl⟩⟩
      · rintro ⟨hvL, ⟨y, hyM, hyπ⟩⟩
        have hdiff : y - ⟨v, hvL⟩ ∈ (D : ℤ) • (⊤ : Submodule ℤ L₀.lat) := by
          rw [← Submodule.Quotient.eq ((D : ℤ) • (⊤ : Submodule ℤ L₀.lat))]
          exact hyπ
        rw [Submodule.mem_smul_pointwise_iff_exists] at hdiff
        obtain ⟨z, _, hz⟩ := hdiff
        have hv_eq : v = (y : Stage11DefiniteUnitaryChain.DefiniteHermitianSpace N) -
            (D : ℤ) • (z : Stage11DefiniteUnitaryChain.DefiniteHermitianSpace N) := by
          have hval := congrArg Subtype.val hz
          simp only [Submodule.coe_sub, SetLike.val_smul] at hval
          calc v = (y : Stage11DefiniteUnitaryChain.DefiniteHermitianSpace N) -
              ((y : Stage11DefiniteUnitaryChain.DefiniteHermitianSpace N) - v) := by abel
            _ = (y : Stage11DefiniteUnitaryChain.DefiniteHermitianSpace N) -
              (D : ℤ) • (z : Stage11DefiniteUnitaryChain.DefiniteHermitianSpace N) := by
              rw [hval]
        rw [hv_eq]
        refine M.1.sub_mem hyM (M.2.1 ?_)
        exact Submodule.smul_mem_pointwise_smul z.1 (D : ℤ) L₀.lat z.2
    rw [hv_iff M₁, hv_iff M₂, heq]
  have : Finite (Set Q) := inferInstance
  exact Set.finite_coe_iff.mp (Finite.of_injective ψ hψ_inj)

end GenusFiniteness

/-! ## Section 5: Orbit-Stabilizer Sum (`double_coset_stabilizer_orbit_sum`) -/

section OrbitStabilizerSum

/-- **Finite-Group Orbit-Stabilizer Sum (`OrbitSum`)**:
for any finite group `H` acting on a finite set `X` and any `H`-invariant function `F : X → k`,
`(|H|)⁻¹ * ∑ x, F x = ∑ ω, (|Stab_H(rep ω)|)⁻¹ * F (rep ω)`. -/
theorem finite_group_orbit_stabilizer_sum {H X : Type*} [Group H] [Fintype H]
    [MulAction H X] [Fintype X] [DecidableEq X]
    {k : Type*} [Field k] [CharZero k]
    [Fintype (MulAction.orbitRel.Quotient H X)]
    (F : X → k) (hF : ∀ (a : H) (x : X), F (a • x) = F x)
    (rep : MulAction.orbitRel.Quotient H X → X)
    (hrep : ∀ ω, Quotient.mk'' (rep ω) = ω) :
    (Fintype.card H : k)⁻¹ * ∑ x : X, F x =
      ∑ ω : MulAction.orbitRel.Quotient H X,
        ((Nat.card (MulAction.stabilizer H (rep ω)) : ℕ) : k)⁻¹ * F (rep ω) := by
  classical
  have hsum_orbit : ∑ x : X, F x =
      ∑ ω : MulAction.orbitRel.Quotient H X,
        (Fintype.card (MulAction.orbit H (rep ω)) : k) * F (rep ω) := by
    have hfib : ∑ x : X, F x =
        ∑ ω : MulAction.orbitRel.Quotient H X,
          ∑ x ∈ Finset.univ.filter (fun x : X =>
            (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) = ω), F x := by
      rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
        (fun x _ => Finset.mem_univ ((Quotient.mk'' x : MulAction.orbitRel.Quotient H X))) F]
    rw [hfib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    have hconst : ∀ x ∈ Finset.univ.filter (fun x : X =>
        (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) = ω), F x = F (rep ω) := by
      intro x hx
      have hq : (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) = Quotient.mk'' (rep ω) :=
        (Finset.mem_filter.mp hx).2.trans (hrep ω).symm
      obtain ⟨a, ha⟩ := Quotient.exact' hq
      rw [← ha, hF a (rep ω)]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have heqv : (Finset.univ.filter (fun x : X =>
        (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) = ω)).card =
        Fintype.card (MulAction.orbit H (rep ω)) := by
      rw [← Fintype.card_coe]
      refine Fintype.card_congr ?_
      exact
        { toFun := fun x => ⟨x.1, by
            have hx : (Quotient.mk'' x.1 : MulAction.orbitRel.Quotient H X) =
                Quotient.mk'' (rep ω) := (Finset.mem_filter.mp x.2).2.trans (hrep ω).symm
            exact Quotient.exact' hx⟩
          invFun := fun y => ⟨y.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            (Quotient.sound' y.2).trans (hrep ω)⟩⟩
          left_inv := fun x => by ext; rfl
          right_inv := fun y => by ext; rfl }
    exact_mod_cast heqv
  rw [hsum_orbit, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have horb := MulAction.card_orbit_mul_card_stabilizer_eq_card_group H (rep ω)
  have hHpos : (Fintype.card H : k) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  have hSpos : (Fintype.card (MulAction.stabilizer H (rep ω)) : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  rw [← Fintype.card_eq_nat_card]
  have horb_k : (Fintype.card (MulAction.orbit H (rep ω)) : k) *
      (Fintype.card (MulAction.stabilizer H (rep ω)) : k) = (Fintype.card H : k) := by
    exact_mod_cast horb
  calc (Fintype.card H : k)⁻¹ * ((Fintype.card (MulAction.orbit H (rep ω)) : k) * F (rep ω))
      = ((Fintype.card (MulAction.orbit H (rep ω)) : k) / (Fintype.card H : k)) * F (rep ω) := by
        ring
    _ = ((Fintype.card (MulAction.stabilizer H (rep ω)) : k)⁻¹) * F (rep ω) := by
        congr 1
        field_simp [hHpos, hSpos]
        exact horb_k

section DoubleCosetSublevelOrbit

variable {G : Type*} [Group G]

/-- Conjugation homomorphism `Stab_{Γ, K}(g) →* K` sending `γ ↦ g⁻¹ γ g`. -/
def stabToK (Γ K : Subgroup G) (g : G) : doubleCosetStab Γ K g →* K where
  toFun γ := ⟨g⁻¹ * (γ : G) * g, γ.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' γ₁ γ₂ := Subtype.ext (by
    simp only [Subgroup.coe_mul, mul_assoc]
    group)

@[simp]
lemma stabToK_coe (Γ K : Subgroup G) (g : G) (γ : doubleCosetStab Γ K g) :
    ((stabToK Γ K g γ : K) : G) = g⁻¹ * (γ.1 : G) * g := rfl

/-- Induced left-coset action of `Stab_{Γ, K}(g)` on `K ⧸ K'.subgroupOf K`. -/
@[instance_reducible]
def stabSublevelAction (Γ : Subgroup G) {K' K : Subgroup G} (g : G) :
    MulAction (doubleCosetStab Γ K g) (K ⧸ K'.subgroupOf K) :=
  MulAction.compHom (K ⧸ K'.subgroupOf K) (stabToK Γ K g)

/-- Exact group isomorphism between the orbit stabilizer in `Stab_{Γ, K}(g)` at `k • K'` and
`Stab_{Γ, K'}(g * k)`. -/
def doubleCosetSublevelStabEquiv (Γ : Subgroup G) {K' K : Subgroup G} (hKK' : K' ≤ K)
    (g : G) (k : K) :
    @MulAction.stabilizer (doubleCosetStab Γ K g) (K ⧸ K'.subgroupOf K) _
      (stabSublevelAction Γ g) (QuotientGroup.mk k) ≃*
      doubleCosetStab Γ K' (g * k) where
  toFun γ := ⟨γ.1.1, by
    have hmem : stabToK Γ K g γ.1 • (QuotientGroup.mk k : K ⧸ K'.subgroupOf K) =
        QuotientGroup.mk k := γ.2
    change (QuotientGroup.mk (stabToK Γ K g γ.1 * k) : K ⧸ K'.subgroupOf K) =
      QuotientGroup.mk k at hmem
    rw [QuotientGroup.eq] at hmem
    have hmem' : (stabToK Γ K g γ.1 * k)⁻¹ * k ∈ K'.subgroupOf K := hmem
    rw [← inv_mem_iff, mul_inv_rev, inv_inv] at hmem'
    have hmem'' : ((k⁻¹ * (stabToK Γ K g γ.1 * k) : K) : G) ∈ K' := by
      simpa [Subgroup.mem_subgroupOf, mul_assoc] using hmem'
    simpa [mem_doubleCosetStab_iff, mul_assoc] using hmem''⟩
  invFun γ :=
    let hγ_mem : γ.1 ∈ doubleCosetStab Γ K g := by
      rw [mem_doubleCosetStab_iff]
      have hmem : (g * k)⁻¹ * (γ.1 : G) * (g * k) ∈ K' := γ.2
      have hk' : (k : G) * ((g * k)⁻¹ * (γ.1 : G) * (g * k)) * (k : G)⁻¹ ∈ K :=
        K.mul_mem (K.mul_mem k.2 (hKK' hmem)) (K.inv_mem k.2)
      convert hk' using 1
      group
    ⟨⟨γ.1, hγ_mem⟩, by
      change (QuotientGroup.mk (stabToK Γ K g ⟨γ.1, hγ_mem⟩ * k) : K ⧸ K'.subgroupOf K) =
        QuotientGroup.mk k
      rw [QuotientGroup.eq, ← inv_mem_iff, mul_inv_rev, inv_inv, Subgroup.mem_subgroupOf]
      have hconj : ((k⁻¹ * (stabToK Γ K g ⟨γ.1, hγ_mem⟩ * k) : K) : G) =
          (g * k)⁻¹ * (γ.1 : G) * (g * k) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, stabToK_coe]
        group
      rw [hconj]
      exact γ.2⟩
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_mul' _ _ := by ext; rfl

private lemma doubleCosetSublevelFiber_surj (Γ : Subgroup G) {K' K : Subgroup G}
    (hKK' : K' ≤ K) (g : G)
    (c' : { c' : DoubleCosetClassSet Γ K' //
      doubleCosetSublevelProj Γ hKK' c' = doubleCosetMk Γ K g }) :
    ∃ k : K, doubleCosetMk Γ K' (g * k) = c'.1 := by
  let x : G := Quotient.out c'.1
  have hmk : doubleCosetMk Γ K' x = c'.1 := by
    rw [doubleCosetMk_eq_quotient_mk]; exact Quotient.out_eq c'.1
  have hproj : doubleCosetMk Γ K x = doubleCosetMk Γ K g := by
    rw [← doubleCosetSublevelProj_mk Γ hKK' x, hmk, c'.2]
  obtain ⟨γ, hγ, κ, hκ, hx⟩ := (DoubleCoset.eq Γ K g x).mp hproj.symm
  refine ⟨⟨κ, hκ⟩, ?_⟩
  rw [← hmk]
  refine (DoubleCoset.eq Γ K' (g * κ) x).mpr ?_
  exact ⟨γ, hγ, 1, K'.one_mem, by rw [hx]; group⟩

/-- Exact bijection between the orbits of `Stab_{Γ, K}(g)` on `K ⧸ K'.subgroupOf K` and the
fiber of `Γ \ G / K' → Γ \ G / K` over `doubleCosetMk Γ K g`. -/
def doubleCosetSublevelFiberEquiv (Γ : Subgroup G) {K' K : Subgroup G} (hKK' : K' ≤ K)
    (g : G) :
    @MulAction.orbitRel.Quotient (doubleCosetStab Γ K g) (K ⧸ K'.subgroupOf K) _
      (stabSublevelAction Γ g) ≃
      { c' : DoubleCosetClassSet Γ K' // doubleCosetSublevelProj Γ hKK' c' = doubleCosetMk Γ K g } where
  toFun := @Quotient.lift (K ⧸ K'.subgroupOf K) _
    (@MulAction.orbitRel (doubleCosetStab Γ K g) (K ⧸ K'.subgroupOf K) _ (stabSublevelAction Γ g))
    (fun q => Quotient.lift (fun k : K => ⟨doubleCosetMk Γ K' (g * k), by
      rw [doubleCosetSublevelProj_mk]
      exact (DoubleCoset.eq Γ K (g * k) g).mpr ⟨1, Γ.one_mem, (k⁻¹).1, (k⁻¹).2, by simp [mul_assoc]⟩⟩)
      (fun k₁ k₂ hk => by
        have hk' : k₁⁻¹ * k₂ ∈ K'.subgroupOf K := QuotientGroup.leftRel_apply.mp hk
        apply Subtype.ext
        exact (DoubleCoset.eq Γ K' (g * k₁) (g * k₂)).mpr
          ⟨1, Γ.one_mem, (k₁⁻¹ * k₂ : K), hk', by simp [mul_assoc]⟩) q)
    (by
      intro q₁ q₂ hrel
      obtain ⟨γ, hγ⟩ := hrel
      obtain ⟨k₁, rfl⟩ := QuotientGroup.mk_surjective q₁
      obtain ⟨k₂, rfl⟩ := QuotientGroup.mk_surjective q₂
      change (QuotientGroup.mk (stabToK Γ K g γ * k₂) : K ⧸ K'.subgroupOf K) =
        QuotientGroup.mk k₁ at hγ
      rw [QuotientGroup.eq] at hγ
      have hκ : ((stabToK Γ K g γ * k₂)⁻¹ * k₁ : K) ∈ K'.subgroupOf K := hγ
      apply Subtype.ext
      change doubleCosetMk Γ K' (g * k₁) = doubleCosetMk Γ K' (g * k₂)
      symm
      refine (DoubleCoset.eq Γ K' (g * k₂) (g * k₁)).mpr ?_
      refine ⟨γ.1.1, γ.1.2, ((stabToK Γ K g γ * k₂)⁻¹ * k₁ : K), hκ, ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, stabToK_coe]
      group)
  invFun c' :=
    @Quotient.mk'' (K ⧸ K'.subgroupOf K)
      (@MulAction.orbitRel (doubleCosetStab Γ K g) (K ⧸ K'.subgroupOf K) _ (stabSublevelAction Γ g))
      (QuotientGroup.mk (Classical.choose (doubleCosetSublevelFiber_surj Γ hKK' g c')))
  left_inv q := by
    classical
    induction q using Quotient.ind with
    | _ q0 =>
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q0
      set c' : { c' : DoubleCosetClassSet Γ K' //
          doubleCosetSublevelProj Γ hKK' c' = doubleCosetMk Γ K g } :=
        ⟨doubleCosetMk Γ K' (g * k), by
          rw [doubleCosetSublevelProj_mk]
          exact (DoubleCoset.eq Γ K (g * k) g).mpr ⟨1, Γ.one_mem, (k⁻¹).1, (k⁻¹).2, by simp [mul_assoc]⟩⟩
      let k₀ : K := Classical.choose (doubleCosetSublevelFiber_surj Γ hKK' g c')
      have hk₀ : doubleCosetMk Γ K' (g * k₀) = doubleCosetMk Γ K' (g * k) :=
        Classical.choose_spec (doubleCosetSublevelFiber_surj Γ hKK' g c')
      obtain ⟨δ, hδ, κ', hκ', hdx⟩ := (DoubleCoset.eq Γ K' (g * k) (g * k₀)).mp hk₀.symm
      have hγ_stab : (⟨δ, hδ⟩ : Γ) ∈ doubleCosetStab Γ K g := by
        rw [mem_doubleCosetStab_iff]
        have hsol : g⁻¹ * δ * g = (k₀ : G) * (κ' : G)⁻¹ * (k : G)⁻¹ := by
          calc g⁻¹ * δ * g
              = g⁻¹ * (δ * (g * k) * κ') * (κ')⁻¹ * k⁻¹ := by
                simp only [Subgroup.coe_inv, mul_assoc]; group
            _ = g⁻¹ * (g * k₀) * (κ')⁻¹ * k⁻¹ := by rw [← hdx]
            _ = (k₀ : G) * (κ')⁻¹ * k⁻¹ := by group
        rw [hsol]
        exact K.mul_mem (K.mul_mem k₀.2 (K.inv_mem (hKK' hκ'))) (K.inv_mem k.2)
      apply @Quotient.sound _
        (@MulAction.orbitRel (doubleCosetStab Γ K g) (K ⧸ K'.subgroupOf K) _
          (stabSublevelAction Γ g))
      refine ⟨⟨⟨δ, hδ⟩, hγ_stab⟩, ?_⟩
      change (QuotientGroup.mk (stabToK Γ K g _ * k) : K ⧸ K'.subgroupOf K) =
        QuotientGroup.mk k₀
      rw [QuotientGroup.eq, ← inv_mem_iff, mul_inv_rev, inv_inv, Subgroup.mem_subgroupOf]
      have hsol : ((k₀⁻¹ * (stabToK Γ K g ⟨⟨δ, hδ⟩, hγ_stab⟩ * k) : K) : G) = (κ' : G)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, stabToK_coe]
        calc (k₀ : G)⁻¹ * (g⁻¹ * δ * g * k)
            = (k₀ : G)⁻¹ * g⁻¹ * (δ * (g * k) * κ') * (κ')⁻¹ := by
              simp only [mul_assoc]; group
          _ = (k₀ : G)⁻¹ * g⁻¹ * (g * k₀) * (κ')⁻¹ := by rw [← hdx]
          _ = (κ')⁻¹ := by group
      rw [hsol]
      exact K'.inv_mem hκ'
  right_inv c' := Subtype.ext (Classical.choose_spec (doubleCosetSublevelFiber_surj Γ hKK' g c'))

/-- **Double-Coset Sublevel Orbit-Stabilizer Sum (`double_coset_stabilizer_orbit_sum`)**:
for any sublevel `K' ≤ K` of finite index and any double coset `c = doubleCosetMk Γ K g` with
finite stabilizer, the sum of weights over the fiber `{ c' // proj c' = c }` equals
`[K : K'] * GenusClassWeight Γ K c`. -/
theorem double_coset_stabilizer_orbit_sum {G : Type*} [Group G] (Γ : Subgroup G)
    {K' K : Subgroup G} (hKK' : K' ≤ K) [Finite (K ⧸ K'.subgroupOf K)]
    (g : G) (hfin : Finite (doubleCosetStab Γ K g))
    [Fintype { c' : DoubleCosetClassSet Γ K' //
        doubleCosetSublevelProj Γ hKK' c' = doubleCosetMk Γ K g }] :
    ∑ c' : { c' : DoubleCosetClassSet Γ K' //
        doubleCosetSublevelProj Γ hKK' c' = doubleCosetMk Γ K g },
      GenusClassWeight Γ K' c'.1 =
      ((K'.subgroupOf K).index : ℝ) * GenusClassWeight Γ K (doubleCosetMk Γ K g) := by
  classical
  have hstabFin : Finite (doubleCosetStab Γ K g) := hfin
  let : Fintype (doubleCosetStab Γ K g) := Fintype.ofFinite _
  let : Fintype (K ⧸ K'.subgroupOf K) := Fintype.ofFinite _
  let : MulAction (doubleCosetStab Γ K g) (K ⧸ K'.subgroupOf K) := stabSublevelAction Γ g
  let e := doubleCosetSublevelFiberEquiv Γ hKK' g
  have hOrbFin : Fintype (@MulAction.orbitRel.Quotient (doubleCosetStab Γ K g)
      (K ⧸ K'.subgroupOf K) _ (stabSublevelAction Γ g)) := inferInstance
  let rep : @MulAction.orbitRel.Quotient (doubleCosetStab Γ K g) (K ⧸ K'.subgroupOf K) _
      (stabSublevelAction Γ g) → (K ⧸ K'.subgroupOf K) := fun ω => Quotient.out ω
  have hrep : ∀ ω, @Quotient.mk'' (K ⧸ K'.subgroupOf K)
      (@MulAction.orbitRel (doubleCosetStab Γ K g) (K ⧸ K'.subgroupOf K) _
        (stabSublevelAction Γ g)) (rep ω) = ω := fun ω => Quotient.out_eq ω
  have horb := finite_group_orbit_stabilizer_sum (H := doubleCosetStab Γ K g)
    (X := K ⧸ K'.subgroupOf K) (k := ℝ) (fun _ => (1 : ℝ)) (fun _ _ => rfl) rep hrep
  simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at horb
  rw [← Fintype.sum_equiv e _ (fun c' => GenusClassWeight Γ K' c'.1) (fun _ => rfl)]
  have hterm : ∀ ω : @MulAction.orbitRel.Quotient (doubleCosetStab Γ K g)
        (K ⧸ K'.subgroupOf K) _ (stabSublevelAction Γ g),
        GenusClassWeight Γ K' (e ω).1 =
          ((Nat.card (@MulAction.stabilizer (doubleCosetStab Γ K g) (K ⧸ K'.subgroupOf K) _
            (stabSublevelAction Γ g) (rep ω)) : ℕ) : ℝ)⁻¹ := by
    intro ω
    obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (rep ω)
    have hω : ω = @Quotient.mk'' (K ⧸ K'.subgroupOf K)
        (@MulAction.orbitRel (doubleCosetStab Γ K g) (K ⧸ K'.subgroupOf K) _
          (stabSublevelAction Γ g)) (QuotientGroup.mk k) := by
      rw [hk, hrep ω]
    have heω : (e ω).1 = doubleCosetMk Γ K' (g * k) := by
      conv_lhs => rw [hω]
      rfl
    rw [heω, genusClassWeight_mk, ← hk]
    congr 2
    exact (Nat.card_congr (doubleCosetSublevelStabEquiv Γ hKK' g k).toEquiv).symm
  simp_rw [hterm]
  rw [← horb]
  have hidx : (Fintype.card (K ⧸ K'.subgroupOf K) : ℝ) = ((K'.subgroupOf K).index : ℝ) := by
    congr 1
    rw [← Nat.card_eq_fintype_card, Subgroup.index_eq_card]
  have hH : (Fintype.card (doubleCosetStab Γ K g) : ℝ)⁻¹ =
      GenusClassWeight Γ K (doubleCosetMk Γ K g) := by
    rw [genusClassWeight_mk, ← Fintype.card_eq_nat_card]
  rw [hidx, hH]
  ring

/-- **Global Sublevel Mass Scaling (`genusClassMass_sublevel_eq`)**:
for any finite-index sublevel `K' ≤ K`, `genusClassMass Γ K' = [K : K'] * genusClassMass Γ K`. -/
theorem genusClassMass_sublevel_eq {G : Type*} [Group G] (Γ : Subgroup G)
    {K' K : Subgroup G} (hKK' : K' ≤ K) [Fintype (DoubleCosetClassSet Γ K)]
    [Fintype (DoubleCosetClassSet Γ K')] [Finite (K ⧸ K'.subgroupOf K)]
    (hfin : ∀ g : G, Finite (doubleCosetStab Γ K g)) :
    genusClassMass Γ K' = ((K'.subgroupOf K).index : ℝ) * genusClassMass Γ K := by
  classical
  unfold genusClassMass
  have hpart := Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
    (fun c' _ => Finset.mem_univ (doubleCosetSublevelProj Γ hKK' c')) (GenusClassWeight Γ K')
  rw [← hpart, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨g, rfl⟩ := Quotient.exists_rep c
  rw [← doubleCosetMk_eq_quotient_mk]
  have horb := double_coset_stabilizer_orbit_sum Γ hKK' g (hfin g)
  rw [← horb]
  symm
  rw [← Fintype.sum_equiv (Equiv.subtypeEquivRight (by simp))
    (fun c' : { c' // c' ∈ Finset.univ.filter (fun c' : DoubleCosetClassSet Γ K' =>
      doubleCosetSublevelProj Γ hKK' c' = doubleCosetMk Γ K g) } => GenusClassWeight Γ K' c'.1)
    (fun c' : { c' : DoubleCosetClassSet Γ K' //
      doubleCosetSublevelProj Γ hKK' c' = doubleCosetMk Γ K g } => GenusClassWeight Γ K' c'.1)
    (fun _ => rfl)]
  convert Finset.sum_coe_sort (Finset.univ.filter (fun c' : DoubleCosetClassSet Γ K' =>
    doubleCosetSublevelProj Γ hKK' c' = doubleCosetMk Γ K g)) (GenusClassWeight Γ K')

end DoubleCosetSublevelOrbit

end OrbitStabilizerSum

/-! ## Section 6: Exact Measure Decomposition Over Double Cosets & Iterated Chain-Op Independence -/

section MeasureDecompositionAndChainIndep

section MeasureDecomp

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

/-- **Exact Measure Formula Decomposition Over Double Cosets (`class_decomp_measure_eq_sum`)**:
for any countable discrete subgroup `Γ ≤ G`, measurable compact-open `K ≤ G`, fundamental domain
`𝓕` for `Γ`, and any section `s : DoubleCosetReps Γ K` on `DoubleCosetClassSet Γ K`:
`μ 𝓕 = ∑ c : DoubleCosetClassSet Γ K, μ K * (|Stab_{Γ, K}(s.rep c)| : ℝ≥0∞)⁻¹`. -/
theorem class_decomp_measure_eq_sum {Γ K : Subgroup G} [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant]
    (hK : MeasurableSet (K : Set G))
    [Fintype (DoubleCosetClassSet Γ K)]
    (s : DoubleCosetReps Γ K)
    (hfin : ∀ g : G, Finite (doubleCosetStab Γ K g))
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) :
    μ 𝓕 = ∑ c : DoubleCosetClassSet Γ K,
      μ K * ((Nat.card (doubleCosetStab Γ K (s.rep c)) : ℝ≥0∞))⁻¹ := by
  have h1 := UnitaryMassFormula.measure_fundamentalDomain_eq_genus_mass_sum
    (Γ := Γ) (K := K) μ hK s.rep
    (fun x => doubleCosetReps_covering Γ K s x)
    (fun _ _ _ _ _ _ heq => doubleCosetReps_disjoint Γ K s heq)
    (fun c => by
      have heq : UnitaryMassFormula.genusAut Γ K (s.rep c) =
          (doubleCosetStab Γ K (s.rep c) : Set Γ) := by
        ext γ; exact (mem_doubleCosetStab_iff_genusAut Γ K (s.rep c) γ).symm
      rw [heq]
      have := hfin (s.rep c)
      exact Set.toFinite _)
    h𝓕
  rw [h1]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hcard : Nat.card (UnitaryMassFormula.genusAut Γ K (s.rep c)) =
      Nat.card (doubleCosetStab Γ K (s.rep c)) :=
    Nat.card_congr (Equiv.setCongr (by
      ext γ; exact (mem_doubleCosetStab_iff_genusAut Γ K (s.rep c) γ).symm))
  rw [hcard]

/-- Real-valued double-coset mass decomposition:
`(μ 𝓕).toReal = (μ K).toReal * ∑ c : DoubleCosetClassSet Γ K, GenusClassWeight Γ K c`. -/
theorem class_decomp_toReal_eq_mul_sum {Γ K : Subgroup G} [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant]
    (hK : MeasurableSet (K : Set G)) (hKfin : μ K ≠ ⊤)
    [Fintype (DoubleCosetClassSet Γ K)]
    (hfin : ∀ g : G, Finite (doubleCosetStab Γ K g))
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) :
    (μ 𝓕).toReal = (μ K).toReal * genusClassMass Γ K := by
  let s := canonicalDoubleCosetReps Γ K
  rw [class_decomp_measure_eq_sum μ hK s hfin h𝓕, ENNReal.toReal_sum]
  · unfold genusClassMass
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      genusClassWeight_eq_at_rep Γ K s c]
  · intro c _
    have := hfin (s.rep c)
    have hne : Nonempty (doubleCosetStab Γ K (s.rep c)) := ⟨1⟩
    have hpos : (Nat.card (doubleCosetStab Γ K (s.rep c)) : ℝ≥0∞) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    exact ENNReal.mul_ne_top hKfin (ENNReal.inv_ne_top.mpr hpos)

/-- Exact covolume-to-level ratio `(μ 𝓕).toReal / (μ K).toReal = genusClassMass Γ K`. -/
theorem class_decomp_mass_eq_covolume_div {Γ K : Subgroup G} [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant]
    (hK : MeasurableSet (K : Set G)) (hKpos : 0 < μ K) (hKfin : μ K ≠ ⊤)
    [Fintype (DoubleCosetClassSet Γ K)]
    (hfin : ∀ g : G, Finite (doubleCosetStab Γ K g))
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) :
    genusClassMass Γ K = (μ 𝓕).toReal / (μ K).toReal := by
  rw [class_decomp_toReal_eq_mul_sum μ hK hKfin hfin h𝓕]
  have hK0 : (μ K).toReal ≠ 0 := (ENNReal.toReal_pos hKpos.ne' hKfin).ne'
  exact (mul_div_cancel_left₀ _ hK0).symm

/-- **Double-Coset Unfolding for `(Γ, K)`-Bi-Invariant Non-Negative Measurable Functions**:
`∫⁻ x in 𝓕, φ x ∂μ = ∑ c, μ K * (|Stab(s c)|)⁻¹ * φ (s c)`. -/
theorem class_decomp_lintegral_eq_sum {Γ K : Subgroup G} [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant]
    (hK : MeasurableSet (K : Set G))
    [Fintype (DoubleCosetClassSet Γ K)]
    (s : DoubleCosetReps Γ K)
    (hfin : ∀ g : G, Finite (doubleCosetStab Γ K g))
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (φ : G → ℝ≥0∞) (hφ_meas : Measurable φ)
    (hφ_inv : ∀ (γ : Γ) (g : G) (κ : K), φ ((γ : G) * g * κ) = φ g) :
    ∫⁻ x in 𝓕, φ x ∂μ =
      ∑ c : DoubleCosetClassSet Γ K,
        μ K * ((Nat.card (doubleCosetStab Γ K (s.rep c)) : ℝ≥0∞))⁻¹ * φ (s.rep c) := by
  classical
  have : MeasurableConstSMul Γ G := ⟨fun γ => measurable_const_mul (γ : G)⟩
  have : SMulInvariantMeasure Γ G μ := ⟨fun γ s _ => measure_preimage_mul μ (γ : G) s⟩
  let T : DoubleCosetClassSet Γ K → Set G := fun c => (fun y => (s.rep c)⁻¹ * y) ⁻¹' (K : Set G)
  have hT : ∀ c, MeasurableSet (T c) := fun c => (measurable_const_mul _) hK
  let f : G → ℝ≥0∞ := fun y =>
    ∑ c : DoubleCosetClassSet Γ K,
      ((Nat.card (doubleCosetStab Γ K (s.rep c)) : ℝ≥0∞))⁻¹ * (T c).indicator φ y
  have hf : Measurable f := Finset.measurable_sum _ fun c _ =>
    (hφ_meas.indicator (hT c)).const_mul _
  have hG : ∫⁻ y, f y ∂μ =
      ∑ c : DoubleCosetClassSet Γ K,
        μ K * ((Nat.card (doubleCosetStab Γ K (s.rep c)) : ℝ≥0∞))⁻¹ * φ (s.rep c) := by
    rw [lintegral_finsetSum _ fun c _ => (hφ_meas.indicator (hT c)).const_mul _]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [lintegral_const_mul _ (hφ_meas.indicator (hT c))]
    have hind : (T c).indicator φ = (T c).indicator (fun _ => φ (s.rep c)) := by
      funext y
      by_cases hy : y ∈ T c
      · simp only [Set.indicator_of_mem hy]
        have hk : (s.rep c)⁻¹ * y ∈ K := hy
        have hy_eq : y = ((1 : Γ) : G) * s.rep c * (⟨(s.rep c)⁻¹ * y, hk⟩ : K) := by
          simp
        rw [hy_eq, hφ_inv]
      · simp only [Set.indicator_of_notMem hy]
    rw [hind, lintegral_indicator (hT c), setLIntegral_const,
      show μ (T c) = μ K by
        change μ ((fun y => (s.rep c)⁻¹ * y) ⁻¹' (K : Set G)) = μ K
        exact measure_preimage_mul μ (s.rep c)⁻¹ (K : Set G)]
    ring
  have hpt : ∀ x : G, ∑' γ : Γ, f (γ • x) = φ x := by
    intro x
    obtain ⟨j, δ, k, rfl⟩ := doubleCosetReps_covering Γ K s x
    have hsum : ∀ i : DoubleCosetClassSet Γ K,
        ∑' γ : Γ, (T i).indicator φ (γ • ((δ : G) * s.rep j * k)) =
          (Nat.card (UnitaryMassFormula.doubleCosetHit Γ K (s.rep i)
            ((δ : G) * s.rep j * k)) : ℝ≥0∞) * φ (s.rep j) := by
      intro i
      have hfin' : (UnitaryMassFormula.doubleCosetHit Γ K (s.rep i)
          ((δ : G) * s.rep j * k)).Finite := by
        by_cases hij : i = j
        · rw [hij]
          have hstabFin : Finite (doubleCosetStab Γ K (s.rep j)) := hfin (s.rep j)
          have hgenusAutFin : Finite (UnitaryMassFormula.genusAut Γ K (s.rep j)) :=
            Finite.of_equiv (doubleCosetStab Γ K (s.rep j))
              (Equiv.setCongr (Set.ext fun γ => mem_doubleCosetStab_iff_genusAut Γ K (s.rep j) γ))
          have : Finite (UnitaryMassFormula.doubleCosetHit Γ K (s.rep j)
              ((δ : G) * s.rep j * k)) :=
            Finite.of_equiv _ (UnitaryMassFormula.doubleCosetHitEquiv (s.rep j) δ k).symm
          exact Set.toFinite _
        · rw [UnitaryMassFormula.doubleCosetHit_empty s.rep
            (fun _ _ _ _ _ _ heq => doubleCosetReps_disjoint Γ K s heq) δ k i hij]
          exact Set.finite_empty
      have e : (fun γ : Γ => (T i).indicator φ (γ • ((δ : G) * s.rep j * k))) =
          (UnitaryMassFormula.doubleCosetHit Γ K (s.rep i)
            ((δ : G) * s.rep j * k)).indicator (fun _ => φ (s.rep j)) := by
        funext γ
        by_cases hmem : γ ∈ UnitaryMassFormula.doubleCosetHit Γ K (s.rep i)
            ((δ : G) * s.rep j * k)
        · have hmemT : γ • ((δ : G) * s.rep j * k) ∈ T i := hmem
          rw [Set.indicator_of_mem hmemT, Set.indicator_of_mem hmem]
          have heq : γ • ((δ : G) * s.rep j * k) =
              ((γ * δ : Γ) : G) * s.rep j * k := by
            simp [Subgroup.smul_def, mul_assoc]
          rw [heq, hφ_inv]
        · have hmemT : γ • ((δ : G) * s.rep j * k) ∉ T i := hmem
          rw [Set.indicator_of_notMem hmemT, Set.indicator_of_notMem hmem]
      rw [e, ← _root_.tsum_subtype]
      have := hfin'.fintype
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_eq_nat_card]
    have hswap : ∑' γ : Γ, f (γ • ((δ : G) * s.rep j * k)) =
        ∑ i : DoubleCosetClassSet Γ K,
          ((Nat.card (doubleCosetStab Γ K (s.rep i)) : ℝ≥0∞))⁻¹ *
            ∑' γ : Γ, (T i).indicator φ (γ • ((δ : G) * s.rep j * k)) := by
      simp only [f]
      rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ENNReal.tsum_mul_left]
    rw [hswap, Finset.sum_eq_single j]
    · rw [hsum j, Nat.card_congr (UnitaryMassFormula.doubleCosetHitEquiv (s.rep j) δ k)]
      have heq_set : Nat.card (UnitaryMassFormula.genusAut Γ K (s.rep j)) =
          Nat.card (doubleCosetStab Γ K (s.rep j)) :=
        Nat.card_congr (Equiv.setCongr (by
          ext γ; exact (mem_doubleCosetStab_iff_genusAut Γ K (s.rep j) γ).symm))
      rw [heq_set, ← mul_assoc]
      have hne : (Nat.card (doubleCosetStab Γ K (s.rep j)) : ℝ≥0∞) ≠ 0 := by
        have := hfin (s.rep j)
        have : Nonempty (doubleCosetStab Γ K (s.rep j)) := ⟨1⟩
        exact_mod_cast (Nat.card_pos (α := doubleCosetStab Γ K (s.rep j))).ne'
      rw [ENNReal.inv_mul_cancel hne (ENNReal.natCast_ne_top _), one_mul, hφ_inv]
    · intro i _ hij
      rw [hsum i, UnitaryMassFormula.doubleCosetHit_empty s.rep
        (fun _ _ _ _ _ _ heq => doubleCosetReps_disjoint Γ K s heq) δ k i hij]
      simp
    · intro h; exact absurd (Finset.mem_univ j) h
  have hmeas : ∀ γ : Γ, Measurable fun x => f (γ • x) := fun γ => hf.comp (measurable_const_smul γ)
  have hpt_eq : φ = fun x => ∑' γ : Γ, f (γ • x) := funext fun x => (hpt x).symm
  calc ∫⁻ x in 𝓕, φ x ∂μ
      = ∫⁻ x in 𝓕, ∑' γ : Γ, f (γ • x) ∂μ := by rw [hpt_eq]
    _ = ∑' γ : Γ, ∫⁻ x in 𝓕, f (γ • x) ∂μ := lintegral_tsum fun γ => (hmeas γ).aemeasurable
    _ = ∫⁻ y, f y ∂μ := (h𝓕.lintegral_eq_tsum'' f).symm
    _ = _ := hG

end MeasureDecomp

/-! ## Section 6b: Double-Coset Independence of Adelic Theta Lifts & Iterated `chainOpM` -/

section ChainOpDoubleCosetIndep

variable {G : Type*} [Group G]

/-- Left-`Γ`-equivariant, right-`K`-invariant adelic automorphic forms `AMF Γ K ρ`. -/
def AdelicAMF (Γ K : Subgroup G) {k W : Type*} [Field k] [AddCommGroup W] [Module k W]
    (ρ : Γ →* (W →ₗ[k] W)) : Submodule k (G → W) where
  carrier := { f | ∀ (γ : Γ) (g : G) (κ : K), f ((γ : G) * g * κ) = ρ γ (f g) }
  zero_mem' := fun γ g κ => by simp
  add_mem' := fun {f₁ f₂} h₁ h₂ γ g κ => by simp [h₁ γ g κ, h₂ γ g κ]
  smul_mem' := fun c f hf γ g κ => by simp [hf γ g κ]

/-- Left-`Γ`-invariant, right-`K`-equivariant adelic automorphic forms `AMFK Γ K ρK`. -/
def AdelicAMFK (Γ K : Subgroup G) {k W : Type*} [Field k] [AddCommGroup W] [Module k W]
    (ρK : K →* (W →ₗ[k] W)) : Submodule k (G → W) where
  carrier := { f | ∀ (γ : Γ) (g : G) (κ : K), f ((γ : G) * g * κ) = ρK κ⁻¹ (f g) }
  zero_mem' := fun γ g κ => by simp
  add_mem' := fun {f₁ f₂} h₁ h₂ γ g κ => by simp [h₁ γ g κ, h₂ γ g κ]
  smul_mem' := fun c f hf γ g κ => by simp [hf γ g κ]

/-- **Class-Sum Double-Coset Independence (`class_sum_double_coset_indep`)**:
for any `(Γ, K)`-bi-invariant function `F : G → M`, the stabilizer-weighted sum over
`DoubleCosetClassSet Γ K` is independent of the choice of representatives `s, s'`. -/
theorem class_sum_double_coset_indep {Γ K : Subgroup G} {k M : Type*} [Field k]
    [AddCommGroup M] [Module k M] [Fintype (DoubleCosetClassSet Γ K)]
    (F : G → M) (hF : ∀ (γ : Γ) (g : G) (κ : K), F ((γ : G) * g * κ) = F g)
    (s s' : DoubleCosetReps Γ K) :
    ∑ c : DoubleCosetClassSet Γ K,
      ((Nat.card (doubleCosetStab Γ K (s.rep c)) : ℕ) : k)⁻¹ • F (s.rep c) =
    ∑ c : DoubleCosetClassSet Γ K,
      ((Nat.card (doubleCosetStab Γ K (s'.rep c)) : ℕ) : k)⁻¹ • F (s'.rep c) := by
  refine Finset.sum_congr rfl fun c _ => ?_
  have hmk : doubleCosetMk Γ K (s.rep c) = doubleCosetMk Γ K (s'.rep c) :=
    (s.mk_rep c).trans (s'.mk_rep c).symm
  obtain ⟨γ, hγ, κ, hκ, heq⟩ := (DoubleCoset.eq Γ K (s.rep c) (s'.rep c)).mp hmk
  have heq' : s'.rep c = ((⟨γ, hγ⟩ : Γ) : G) * s.rep c * ((⟨κ, hκ⟩ : K) : G) := heq
  rw [heq', card_doubleCosetStab_mul, hF]

/-- Adelic theta lift evaluated over a chosen double-coset section `s : DoubleCosetReps Γ K`. -/
def adelicThetaLift {Γ K : Subgroup G} {k W M : Type*} [Field k] [AddCommGroup W] [Module k W]
    [AddCommGroup M] [Module k M] [Fintype (DoubleCosetClassSet Γ K)]
    (s : DoubleCosetReps Γ K) (θ : G → W →ₗ[k] M) (f : G → W) : M :=
  ∑ c : DoubleCosetClassSet Γ K,
    ((Nat.card (doubleCosetStab Γ K (s.rep c)) : ℕ) : k)⁻¹ • θ (s.rep c) (f (s.rep c))

/-- Independence of `adelicThetaLift` for `f ∈ AdelicAMF Γ K ρ`. -/
theorem adelic_theta_lift_double_coset_indep {Γ K : Subgroup G} {k W M : Type*} [Field k]
    [AddCommGroup W] [Module k W] [AddCommGroup M] [Module k M]
    [Fintype (DoubleCosetClassSet Γ K)]
    (ρ : Γ →* (W →ₗ[k] W)) (θ : G → W →ₗ[k] M)
    (hθ : ∀ (γ : Γ) (g : G) (κ : K) (w : W), θ ((γ : G) * g * κ) (ρ γ w) = θ g w)
    {f : G → W} (hf : f ∈ AdelicAMF Γ K ρ) (s s' : DoubleCosetReps Γ K) :
    adelicThetaLift s θ f = adelicThetaLift s' θ f := by
  refine class_sum_double_coset_indep (fun g => θ g (f g)) ?_ s s'
  intro γ g κ
  rw [hf γ g κ, hθ γ g κ (f g)]

/-- Independence of `adelicThetaLift` for `f ∈ AdelicAMFK Γ K ρK`. -/
theorem adelic_theta_liftK_double_coset_indep {Γ K : Subgroup G} {k W M : Type*} [Field k]
    [AddCommGroup W] [Module k W] [AddCommGroup M] [Module k M]
    [Fintype (DoubleCosetClassSet Γ K)]
    (ρK : K →* (W →ₗ[k] W)) (θ : G → W →ₗ[k] M)
    (hθ : ∀ (γ : Γ) (g : G) (κ : K) (w : W), θ ((γ : G) * g * κ) (ρK κ⁻¹ w) = θ g w)
    {f : G → W} (hf : f ∈ AdelicAMFK Γ K ρK) (s s' : DoubleCosetReps Γ K) :
    adelicThetaLift s θ f = adelicThetaLift s' θ f := by
  refine class_sum_double_coset_indep (fun g => θ g (f g)) ?_ s s'
  intro γ g κ
  rw [hf γ g κ, hθ γ g κ (f g)]

/-- Adelic Petersson inner product on `G → W` with respect to a `Γ`-invariant bilinear
pairing `B : W → W → k`. -/
def adelicIp {Γ K : Subgroup G} {k W : Type*} [Field k] [AddCommGroup W] [Module k W]
    [Fintype (DoubleCosetClassSet Γ K)]
    (s : DoubleCosetReps Γ K) (B : W → W → k) (f₁ f₂ : G → W) : k :=
  ∑ c : DoubleCosetClassSet Γ K,
    ((Nat.card (doubleCosetStab Γ K (s.rep c)) : ℕ) : k)⁻¹ * B (f₁ (s.rep c)) (f₂ (s.rep c))

/-- Independence of the adelic Petersson inner product from double-coset representatives. -/
theorem adelic_ip_double_coset_indep {Γ K : Subgroup G} {k W : Type*} [Field k]
    [AddCommGroup W] [Module k W] [Fintype (DoubleCosetClassSet Γ K)]
    (ρ : Γ →* (W →ₗ[k] W)) (B : W → W → k)
    (hB : ∀ (γ : Γ) (u v : W), B (ρ γ u) (ρ γ v) = B u v)
    {f₁ f₂ : G → W} (hf₁ : f₁ ∈ AdelicAMF Γ K ρ) (hf₂ : f₂ ∈ AdelicAMF Γ K ρ)
    (s s' : DoubleCosetReps Γ K) :
    adelicIp s B f₁ f₂ = adelicIp s' B f₁ f₂ := by
  unfold adelicIp
  refine Finset.sum_congr rfl fun c _ => ?_
  have hmk : doubleCosetMk Γ K (s.rep c) = doubleCosetMk Γ K (s'.rep c) :=
    (s.mk_rep c).trans (s'.mk_rep c).symm
  obtain ⟨γ, hγ, κ, hκ, heq⟩ := (DoubleCoset.eq Γ K (s.rep c) (s'.rep c)).mp hmk
  have heq' : s'.rep c = ((⟨γ, hγ⟩ : Γ) : G) * s.rep c * ((⟨κ, hκ⟩ : K) : G) := heq
  rw [heq', card_doubleCosetStab_mul, hf₁, hf₂, hB]

/-- Tower of adelic groups and subgroups `(G_j, Γ_j, K_j)` with finite double-coset spaces
`DoubleCosetClassSet (Γ j) (K j)`, supporting `RallisSeesaw.chainOpM`. -/
structure AdelicChainTower (k : Type*) [Field k] where
  G : ℕ → Type
  [grp : ∀ j, Group (G j)]
  Γ : ∀ j, Subgroup (G j)
  K : ∀ j, Subgroup (G j)
  [finCls : ∀ j, Fintype (DoubleCosetClassSet (Γ j) (K j))]
  M : ℕ → Type
  [addM : ∀ j, AddCommGroup (M j)]
  [modM : ∀ j, Module k (M j)]
  Kmap : ∀ j, G j → G (j + 1) → (M j →ₗ[k] M (j + 1))
  Kmap_inv : ∀ j (γ₁ : Γ j) (g₁ : G j) (κ₁ : K j) (γ₂ : Γ (j + 1)) (g₂ : G (j + 1)) (κ₂ : K (j + 1)),
    Kmap j ((γ₁ : G j) * g₁ * κ₁) ((γ₂ : G (j + 1)) * g₂ * κ₂) = Kmap j g₁ g₂

attribute [instance] AdelicChainTower.grp AdelicChainTower.finCls
  AdelicChainTower.addM AdelicChainTower.modM

namespace AdelicChainTower

variable {k : Type*} [Field k] (T : AdelicChainTower k)

/-- Family of double-coset representatives `s j` along every stage `j : ℕ`. -/
abbrev TowerReps := ∀ j : ℕ, DoubleCosetReps (T.Γ j) (T.K j)

/-- Genus-class weight function `c ↦ (|Stab_{Γ_j, K_j}(c)|)⁻¹` in field `k`. -/
def weightFun (j : ℕ) (c : DoubleCosetClassSet (T.Γ j) (T.K j)) : k :=
  ((genusClassStabCard (T.Γ j) (T.K j) c : ℕ) : k)⁻¹

/-- Transition kernel on `DoubleCosetClassSet` induced by a choice of representatives `s`. -/
def kernelOnCls (s : T.TowerReps) (j : ℕ)
    (c₁ : DoubleCosetClassSet (T.Γ j) (T.K j))
    (c₂ : DoubleCosetClassSet (T.Γ (j + 1)) (T.K (j + 1))) :
    T.M j →ₗ[k] T.M (j + 1) :=
  T.Kmap j ((s j).rep c₁) ((s (j + 1)).rep c₂)

/-- **`RallisSeesaw.chainOpM`** evaluated along the double-coset tower `T` using
representatives `s : T.TowerReps`. -/
def chainOp (s : T.TowerReps) (m : ℕ)
    (f₀ : DoubleCosetClassSet (T.Γ 0) (T.K 0) → T.M 0) :
    DoubleCosetClassSet (T.Γ m) (T.K m) → T.M m :=
  RallisSeesaw.chainOpM (T.weightFun) (T.kernelOnCls s) m f₀

/-- **Iterated Chain-Operator Double-Coset Independence (`chain_op_double_coset_indep`)**:
for ANY two choices of double-coset representatives `s, s' : T.TowerReps` across all stages
`j = 0, ..., m`, and any initial automorphic section `f₀`, the `m`-step iterated column-chain
operator `RallisSeesaw.chainOpM` gives the **EXACT SAME** result at every double coset `c`:
`T.chainOp s m f₀ = T.chainOp s' m f₀`! -/
theorem chain_op_double_coset_indep (s s' : T.TowerReps) (m : ℕ)
    (f₀ : DoubleCosetClassSet (T.Γ 0) (T.K 0) → T.M 0) :
    T.chainOp s m f₀ = T.chainOp s' m f₀ := by
  have hker_eq : ∀ j c₁ c₂, T.kernelOnCls s j c₁ c₂ = T.kernelOnCls s' j c₁ c₂ := by
    intro j c₁ c₂
    unfold kernelOnCls
    have hmk₁ : doubleCosetMk (T.Γ j) (T.K j) ((s j).rep c₁) =
        doubleCosetMk (T.Γ j) (T.K j) ((s' j).rep c₁) :=
      ((s j).mk_rep c₁).trans ((s' j).mk_rep c₁).symm
    have hmk₂ : doubleCosetMk (T.Γ (j + 1)) (T.K (j + 1)) ((s (j + 1)).rep c₂) =
        doubleCosetMk (T.Γ (j + 1)) (T.K (j + 1)) ((s' (j + 1)).rep c₂) :=
      ((s (j + 1)).mk_rep c₂).trans ((s' (j + 1)).mk_rep c₂).symm
    obtain ⟨γ₁, hγ₁, κ₁, hκ₁, heq₁⟩ :=
      (DoubleCoset.eq (T.Γ j) (T.K j) ((s j).rep c₁) ((s' j).rep c₁)).mp hmk₁
    obtain ⟨γ₂, hγ₂, κ₂, hκ₂, heq₂⟩ :=
      (DoubleCoset.eq (T.Γ (j + 1)) (T.K (j + 1))
        ((s (j + 1)).rep c₂) ((s' (j + 1)).rep c₂)).mp hmk₂
    have heq₁' : (s' j).rep c₁ =
        ((⟨γ₁, hγ₁⟩ : T.Γ j) : T.G j) * (s j).rep c₁ * ((⟨κ₁, hκ₁⟩ : T.K j) : T.G j) := heq₁
    have heq₂' : (s' (j + 1)).rep c₂ =
        ((⟨γ₂, hγ₂⟩ : T.Γ (j + 1)) : T.G (j + 1)) * (s (j + 1)).rep c₂ *
          ((⟨κ₂, hκ₂⟩ : T.K (j + 1)) : T.G (j + 1)) := heq₂
    rw [heq₁', heq₂', T.Kmap_inv]
  induction m with
  | zero => rfl
  | succ m ih =>
    funext c
    simp only [chainOp, RallisSeesaw.chainOpM_succ, RallisSeesaw.kerOpM]
    have ih' : RallisSeesaw.chainOpM T.weightFun (T.kernelOnCls s) m f₀ =
        RallisSeesaw.chainOpM T.weightFun (T.kernelOnCls s') m f₀ := ih
    rw [ih']
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hker_eq m a c]

/-- **Equivariant Version**: `chain_op_double_coset_indep` for left-`Γ`-equivariant /
right-`K`-invariant kernels `θ_j(γ₁ g₁ κ₁, γ₂ g₂ κ₂)` paired with `AdelicAMF` sections
(generalizing `chain_op_double_coset_indep` via `RallisSeesaw.chainOpM`). -/
theorem chain_op_equivariant_double_coset_indep
    {G : ℕ → Type*} [∀ j, Group (G j)]
    (Γ K : ∀ j, Subgroup (G j))
    [∀ j, Fintype (DoubleCosetClassSet (Γ j) (K j))]
    {M : ℕ → Type*} [∀ j, AddCommGroup (M j)] [∀ j, Module k (M j)]
    (ρ : ∀ j, Γ j →* (M j →ₗ[k] M j))
    (Kmap : ∀ j, G j → G (j + 1) → (M j →ₗ[k] M (j + 1)))
    (hKmap : ∀ j (γ₁ : Γ j) (g₁ : G j) (κ₁ : K j) (γ₂ : Γ (j + 1)) (g₂ : G (j + 1)) (κ₂ : K (j + 1))
      (v : M j), Kmap j ((γ₁ : G j) * g₁ * κ₁) ((γ₂ : G (j + 1)) * g₂ * κ₂) (ρ j γ₁ v) =
        ρ (j + 1) γ₂ (Kmap j g₁ g₂ v))
    (f₀ : G 0 → M 0) (hf₀ : f₀ ∈ AdelicAMF (Γ 0) (K 0) (ρ 0))
    (s s' : ∀ j, DoubleCosetReps (Γ j) (K j)) (m : ℕ)
    (c : DoubleCosetClassSet (Γ m) (K m)) :
    ∃ γ : Γ m, ∃ κ : K m,
      (s' m).rep c = (γ : G m) * (s m).rep c * κ ∧
      RallisSeesaw.chainOpM
        (fun j d => ((genusClassStabCard (Γ j) (K j) d : ℕ) : k)⁻¹)
        (fun j c₁ c₂ => Kmap j ((s' j).rep c₁) ((s' (j + 1)).rep c₂))
        m (fun c₀ => f₀ ((s' 0).rep c₀)) c =
      ρ m γ (RallisSeesaw.chainOpM
        (fun j d => ((genusClassStabCard (Γ j) (K j) d : ℕ) : k)⁻¹)
        (fun j c₁ c₂ => Kmap j ((s j).rep c₁) ((s (j + 1)).rep c₂))
        m (fun c₀ => f₀ ((s 0).rep c₀)) c) := by
  have hrep : ∀ j d, ∃ (γ : Γ j) (κ : K j),
      (s' j).rep d = (γ : G j) * (s j).rep d * κ := by
    intro j d
    have hmk : doubleCosetMk (Γ j) (K j) ((s j).rep d) =
        doubleCosetMk (Γ j) (K j) ((s' j).rep d) :=
      ((s j).mk_rep d).trans ((s' j).mk_rep d).symm
    obtain ⟨γ, hγ, κ, hκ, heq⟩ :=
      (DoubleCoset.eq (Γ j) (K j) ((s j).rep d) ((s' j).rep d)).mp hmk
    exact ⟨⟨γ, hγ⟩, ⟨κ, hκ⟩, heq⟩
  induction m with
  | zero =>
    obtain ⟨γ, κ, hγk⟩ := hrep 0 c
    refine ⟨γ, κ, hγk, ?_⟩
    simp only [RallisSeesaw.chainOpM_zero]
    rw [hγk, hf₀ γ ((s 0).rep c) κ]
  | succ m ih =>
    obtain ⟨γ', κ', hγk'⟩ := hrep (m + 1) c
    refine ⟨γ', κ', hγk', ?_⟩
    simp only [RallisSeesaw.chainOpM_succ, RallisSeesaw.kerOpM]
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    obtain ⟨γ_a, κ_a, hγk_a, ih_a⟩ := ih a
    rw [ih_a, hγk_a, hγk', hKmap m γ_a ((s m).rep a) κ_a γ' ((s (m + 1)).rep c) κ', map_smul]

end AdelicChainTower

/-- **Denominator-Clearing Integrality for Double-Coset `chainOpM` (`chain_op_double_coset_int_clearing`)**:
multiplying the `m`-step double-coset chain operator by `∏_{j < m} genusClassDenom (Γ j) (K j)`
clears every stabilizer denominator `1 / |Stab(L_{j, c})|` into `Λ m` via `RallisSeesaw.chainOpM_int_clearing`. -/
theorem chain_op_double_coset_int_clearing
    {G : ℕ → Type*} [∀ j, Group (G j)]
    (Γ K : ∀ j, Subgroup (G j))
    [∀ j, Fintype (DoubleCosetClassSet (Γ j) (K j))]
    (_hfin : ∀ j (g : G j), Finite (doubleCosetStab (Γ j) (K j) g))
    {R : Type*} [Field R] (S : Subring R)
    {M : ℕ → Type*} [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)]
    (Λ : ∀ j, AddSubgroup (M j))
    (Kcls : ∀ j, DoubleCosetClassSet (Γ j) (K j) →
      DoubleCosetClassSet (Γ (j + 1)) (K (j + 1)) → (M j →ₗ[R] M (j + 1)))
    (hS : ∀ j, ∀ s ∈ S, ∀ x ∈ Λ j, s • x ∈ Λ j)
    (hK : ∀ j a b, ∀ x ∈ Λ j, Kcls j a b x ∈ Λ (j + 1))
    (f₀ : DoubleCosetClassSet (Γ 0) (K 0) → M 0) (hf₀ : ∀ c, f₀ c ∈ Λ 0)
    (m : ℕ) (c : DoubleCosetClassSet (Γ m) (K m)) :
    (∏ j ∈ Finset.range m, (genusClassDenom (Γ j) (K j) : R)) •
      RallisSeesaw.chainOpM
        (fun j d => ((genusClassStabCard (Γ j) (K j) d : ℕ) : R)⁻¹)
        Kcls m f₀ c ∈ Λ m := by
  refine RallisSeesaw.chainOpM_int_clearing S Λ
    (fun j d => ((genusClassStabCard (Γ j) (K j) d : ℕ) : R)⁻¹)
    Kcls (fun j => (genusClassDenom (Γ j) (K j) : R)) hS ?_ hK f₀ hf₀ m c
  intro j d
  by_cases h0 : ((genusClassStabCard (Γ j) (K j) d : ℕ) : R) = 0
  · rw [h0, inv_zero, mul_zero]
    exact S.zero_mem
  · obtain ⟨q, hq⟩ := genusClassStabCard_dvd_denom (Γ j) (K j) d
    rw [hq, Nat.cast_mul, mul_right_comm, mul_inv_cancel₀ h0, one_mul]
    exact natCast_mem S q

/-- **Stage 11 `DefiniteUnitaryTower` Bridge**: any `m`-step double-coset genus family with
matching definite Hermitian lattices `latOf j` and kernels `kernel j` builds a concrete
`Stage11DefiniteUnitaryChain.DefiniteUnitaryTower m k t` whose Petersson weights equal
`GenusClassWeight` and whose `chainOpM` is independent of double-coset representatives! -/
def definiteUnitaryTowerOfDoubleCosets {m k t : ℕ}
    (G : Fin (m + 1) → Type) [∀ j, Group (G j)]
    (Γ K : ∀ j, Subgroup (G j))
    [∀ j, Fintype (DoubleCosetClassSet (Γ j) (K j))]
    [∀ j, DecidableEq (DoubleCosetClassSet (Γ j) (K j))]
    (latOf : ∀ j : Fin (m + 1), DoubleCosetClassSet (Γ j) (K j) →
      Stage11DefiniteUnitaryChain.HermitianLattice
        (Stage11DefiniteUnitaryChain.chainRank k t j.1))
    (kernel : ∀ j : Fin m,
      DoubleCosetClassSet (Γ j.castSucc) (K j.castSucc) →
      DoubleCosetClassSet (Γ j.succ) (K j.succ) → ℂ) :
    Stage11DefiniteUnitaryChain.DefiniteUnitaryTower m k t where
  genus j := toHermitianGenus (Γ j) (K j) (latOf j)
  kernel j := kernel j

end ChainOpDoubleCosetIndep

end MeasureDecompositionAndChainIndep

end RHDirect.Stage14M1_GenusClassDecomp
