import RHDirect.Stage12GaloisShaLen
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Multiplicity
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# RHDirect.Stage13GL_GaloisCohomLength

**GaloisLibrary Wave 1 (3 of 3 — Keystone):** Complete, self-contained Galois cohomology length
library wired directly onto `RHDirect.Stage12GaloisShaLen` (`Sha`, `shaLen`, `Sha1Galois`,
`galoisShaLen`, `realGaloisSelmerSystem`), with zero proxy structures and zero open parameters.

## Contents

1. **`p`-adic Unit Subgroups, `nuStar` / `nu` Invariants, `nuLeBound`, `QZ` Torsion Embeddings,
   and Torsion-Level `Module.length` Invariants**
   - `nuStar`, `nu`, `redPow`, `red`, `princ`, `resOrder`, `depth`, `twistInv`, `levelGroup`,
     `levelInertia`, `levelDec`, `nuBound`, `emultiplicity_pow_sub_one_odd`,
     `emultiplicity_pow_sub_one_sq`, `nu_ne_top`, `nuLeBound`.
   - `qz_torsion_zmod_embedding` (`QzTorsionZmodEmbedding`),
     `exists_length_eq_and_card_eq_pow_of_isFiniteLength`,
     `padicInt_length_eq_of_card_quotient_eq_card_submodule`,
     `length_eq_length_invariants_of_torsion_levels` (`LengthEqLengthInvariantsOfTorsionLevels`),
     `length_torsionBy_QZ`, `lenTwist`.

2. **Roots of Unity under Inertia & Decomposition, Cyclotomic Splitting, and `cardAbove`**
   - `fieldSubgroup`, `cardAbove`, `ineFixRoots`, `decActRoots`, `decFrob`, `classIff`, `classFix`.

3. **Cyclotomic Inertia Surjectivity, Infinite-Order Decomposition Elements, `ineOpen`, and `levelLeIne`**
   - `cyclotomicPrimePow_automorphism_inertial_at_prime`,
     `finiteGaloisInertia_lifts_absoluteInertia_rat`, `cycZ_Ine_surjective`.
   - `exists_unit_infinite_order`, `exists_mem_Dec_cycZ_zpow_ne_one`.
   - `decImage`, `ineImage`, `ineOpen`, `isOpen_decImage`, `levelLeIne`, `princ_le_ineImage`.

4. **Global & Local `H⁰` Twist Lengths, Cyclotomic Image Conjugation, and `contTw`**
   - `qzG`, `contAction_qzG`, `contAction_zlTw`, `contTw`, `eps`, `galImage`, `nuGal`,
     `cyclotomicCharacter_conj`, `H0_scalRep_inv_pow_eq_twistInv`, `ranges`,
     `length_H0_global_eq_nu`, `length_H0_local_eq_nu`, `local_H0_length_eq_sum`, `imageConj`.

5. **Absolute `ShaAbs`, Inflation Identification (`shaInfl`), Galois & Place Transport, `vFormula`,
   and `ShaLenEqShaInv` Wired onto `Sha1Galois` & `realGaloisSelmerSystem`**
   - `ShaAbs`, `shaInv`, `shaInfl`, `galTransport`, `placeTransport`, `shaAbsRes`,
     `shaLen_eq_abs`, `shaLen_congr`, `shaLen_eq_shaInv`, `shaInv_congr`,
     `vLenIndep`, `vFormula`, `indep`.
   - Direct wiring: `shaInv_eq_galoisShaLen`, `shaInv_eq_realGaloisSelmerSystem`,
     `galoisShaLen_congr`, `realGaloisSelmerSystem_shaLen_congr`, `vvle_realGalois_iff_shaInv`,
     `vvle_realGalois_congr`.

6. **`gsTransport`, Galois Action on `H¹`, Equivariant Transport (`H1_transport_field_iso`),
   and CM Plus/Minus Eigenspace Decomposition (`partLenCongr`)**
   - `gsTransport`, `IsLift`, `conjGal`, `conjGS`, `galoisActionOnCohomology`,
     `H1_transport_field_iso`, `length_eq_add_eigen`, `ShaPlus`, `ShaMinus`, `plusLen`, `minusLen`,
     `shaLen_eq_add`, `partLenCongr`, `Sha1GaloisPlus`, `Sha1GaloisMinus`,
     `galoisShaLen_eq_plus_add_minus`.

7. **Unramified Selmer Inflation (`selAllLeInf`) and Cyclotomic Block Cocycle Length Bound
   (`length_cyclotomic_block_cocycles_le_sha`)**
   - `Places`, `unrAt`, `SelAll`, `bkCond`, `selLen`, `selAllLeInf`.
   - `length_quot_padic_dvr`, `length_le_of_coord_map`, `LocTriv`, `exists_toSha`,
     `length_cyclotomic_block_cocycles_le_sha`, `length_cyclotomic_block_cocycles_le_galoisShaLen`.

Zero `sorry`, zero custom `axiom`s, zero `opaque`, zero `native_decide`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open NumberField IsDedekindDomain Representation Pointwise Polynomial
open RHDirect.Stage12GaloisShaLen

namespace RHDirect.Stage13GL_GaloisCohomLength

/-! ## Section 1: `p`-adic Unit Subgroups, `nu` Invariants, `QZ` Torsion & Torsion-Level Length -/

section PadicUnitsAndNu

section NuStar

variable {R : Type*} [CommRing R]

/-- Infimum of `p`-adic multiplicities of `u ^ tr - 1` for `u ∈ U`. -/
def nuStar (p : R) (U : Set R) (tr : ℕ) : ℕ∞ :=
  sInf ((fun u => emultiplicity p (u ^ tr - 1)) '' U)

theorem le_nuStar_iff (p : R) (U : Set R) (tr n : ℕ) :
    (n : ℕ∞) ≤ nuStar p U tr ↔ ∀ u ∈ U, p ^ n ∣ u ^ tr - 1 := by
  unfold nuStar
  rw [le_sInf_iff, Set.forall_mem_image]
  exact forall₂_congr fun u _ => pow_dvd_iff_le_emultiplicity.symm

theorem exists_eq_nuStar {p : R} {U : Set R} (hU : U.Nonempty) (tr : ℕ) :
    ∃ u ∈ U, emultiplicity p (u ^ tr - 1) = nuStar p U tr := by
  have h := csInf_mem (hU.image (fun u => emultiplicity p (u ^ tr - 1)))
  obtain ⟨u, hu, e⟩ := h
  exact ⟨u, hu, e⟩

theorem exists_exact_of_nuStar_eq {p : R} {U : Set R} {tr ν : ℕ} (h : nuStar p U tr = ν) :
    ∃ u ∈ U, p ^ ν ∣ u ^ tr - 1 ∧ ¬ p ^ (ν + 1) ∣ u ^ tr - 1 := by
  rcases U.eq_empty_or_nonempty with hU | hU
  · subst hU
    simp [nuStar] at h
  obtain ⟨u, hu, e⟩ := exists_eq_nuStar hU tr
  rw [h] at e
  refine ⟨u, hu, pow_dvd_iff_le_emultiplicity.mpr e.ge, fun hd => ?_⟩
  have := pow_dvd_iff_le_emultiplicity.mp hd
  rw [e] at this
  norm_cast at this
  omega

end NuStar

section PadicUnitSubgroups

variable (l : ℕ) [Fact l.Prime]

/-- The `l`-adic twist invariant `ν_l(U, tr) = inf_{u ∈ U} v_l(u^tr - 1) ∈ ℕ∞`. -/
def nu (U : Subgroup ℤ_[l]ˣ) (tr : ℕ) : ℕ∞ :=
  nuStar (l : ℤ_[l]) ((fun u : ℤ_[l]ˣ => (u : ℤ_[l])) '' (U : Set ℤ_[l]ˣ)) tr

/-- Reduction map `ℤ_[l]ˣ →* (ZMod (l ^ a))ˣ`. -/
def redPow (a : ℕ) : ℤ_[l]ˣ →* (ZMod (l ^ a))ˣ :=
  Units.map (PadicInt.toZModPow a : ℤ_[l] →+* ZMod (l ^ a)).toMonoidHom

/-- Reduction map `ℤ_[l]ˣ →* (ZMod l)ˣ`. -/
def red : ℤ_[l]ˣ →* (ZMod l)ˣ :=
  Units.map (PadicInt.toZMod : ℤ_[l] →+* ZMod l).toMonoidHom

/-- Principal congruence subgroup `U^(a) = ker(ℤ_[l]ˣ → (ZMod (l^a))ˣ)`. -/
def princ (a : ℕ) : Subgroup ℤ_[l]ˣ := (redPow l a).ker

/-- Residual order `#(U mod l) ≤ l - 1`. -/
def resOrder (U : Subgroup ℤ_[l]ˣ) : ℕ := Nat.card (U.map (red l))

/-- Depth of `U ∩ U^(1)`. -/
def depth (U : Subgroup ℤ_[l]ˣ) : ℕ∞ := nu l (U ⊓ princ l 1) 1

/-- Submodule of `A` fixed by `u ^ tr` for all `u ∈ U`. -/
def twistInv (A : Type*) [AddCommGroup A] [Module ℤ_[l] A] (U : Subgroup ℤ_[l]ˣ) (tr : ℕ) :
    Submodule ℤ_[l] A where
  carrier := {x | ∀ u ∈ U, ((u : ℤ_[l]) ^ tr) • x = x}
  zero_mem' := fun _ _ => smul_zero _
  add_mem' := fun {x y} hx hy u hu => by rw [smul_add, hx u hu, hy u hu]
  smul_mem' := fun c x hx u hu => by rw [smul_comm, hx u hu]

/-- Level-`N` subgroup of `ℤ_[l]ˣ` attached to `H ≤ (ZMod N)ˣ`. -/
def levelGroup (N : ℕ) (H : Subgroup (ZMod N)ˣ) : Subgroup ℤ_[l]ˣ :=
  (H.map (ZMod.unitsMap (Nat.ordProj_dvd N l))).comap (redPow l (N.factorization l))

/-- Level-`N` inertia subgroup `ker((ZMod N)ˣ → (ZMod (ordCompl[l] N))ˣ)`. -/
def levelInertia (N : ℕ) : Subgroup (ZMod N)ˣ :=
  (ZMod.unitsMap (Nat.ordCompl_dvd N l)).ker

/-- Level-`N` decomposition subgroup of `(ZMod N)ˣ` generated by Frobenius `l` on `ordCompl[l] N`. -/
def levelDec (N : ℕ) : Subgroup (ZMod N)ˣ :=
  (Subgroup.closure {u : (ZMod (ordCompl[l] N))ˣ |
      (u : ZMod (ordCompl[l] N)) = (l : ZMod (ordCompl[l] N))}).comap
    (ZMod.unitsMap (Nat.ordCompl_dvd N l))

/-- Explicit upper bound `nuBound l N e` on `ν_l(U, e)` for `princ l (v_l(N)) ≤ U`. -/
def nuBound (N e : ℕ) : ℕ :=
  if l ∣ N ∨ l - 1 ∣ e then max (N.factorization l) (if l = 2 then 2 else 1) + e.factorization l else 0

variable {l}

theorem mem_princ {a : ℕ} {u : ℤ_[l]ˣ} : u ∈ princ l a ↔ (l : ℤ_[l]) ^ a ∣ (u : ℤ_[l]) - 1 := by
  rw [princ, MonoidHom.mem_ker, ← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker,
    map_sub, map_one, sub_eq_zero, Units.ext_iff]
  simp [redPow]

theorem le_nu_iff {U : Subgroup ℤ_[l]ˣ} {tr n : ℕ} :
    (n : ℕ∞) ≤ nu l U tr ↔ ∀ u ∈ U, (l : ℤ_[l]) ^ n ∣ (u : ℤ_[l]) ^ tr - 1 := by
  rw [nu, le_nuStar_iff, Set.forall_mem_image]
  rfl

theorem le_nu_iff_pow_mem_princ {U : Subgroup ℤ_[l]ˣ} {tr n : ℕ} :
    (n : ℕ∞) ≤ nu l U tr ↔ ∀ u ∈ U, u ^ tr ∈ princ l n := by
  rw [le_nu_iff]
  simp only [mem_princ, Units.val_pow_eq_pow_val]

theorem mem_twistInv {A : Type*} [AddCommGroup A] [Module ℤ_[l] A] {U : Subgroup ℤ_[l]ˣ} {tr : ℕ}
    {x : A} : x ∈ twistInv l A U tr ↔ ∀ u ∈ U, ((u : ℤ_[l]) ^ tr) • x = x := Iff.rfl

theorem mem_levelGroup {N : ℕ} {H : Subgroup (ZMod N)ˣ} {u : ℤ_[l]ˣ} :
    u ∈ levelGroup l N H ↔
      ∃ h ∈ H, ZMod.unitsMap (Nat.ordProj_dvd N l) h = redPow l (N.factorization l) u := Iff.rfl

private theorem mem_princ_iff_norm {a : ℕ} {u : ℤ_[l]ˣ} :
    u ∈ princ l a ↔ ‖(u : ℤ_[l]) - 1‖ ≤ (l : ℝ) ^ (-a : ℤ) := by
  rw [mem_princ, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]

private theorem exists_princ_subset {s : Set ℤ_[l]ˣ} (hs : s ∈ nhds (1 : ℤ_[l]ˣ)) :
    ∃ a, (princ l a : Set ℤ_[l]ˣ) ⊆ s := by
  have h1 : Units.val '' s ∈ nhds ((1 : ℤ_[l]ˣ) : ℤ_[l]) :=
    Units.isOpenEmbedding_val.isOpenMap.image_mem_nhds hs
  simp only [Units.val_one] at h1
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp h1
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨a, ha⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hl)
  refine ⟨a, fun u hu => ?_⟩
  have hu' : (u : ℤ_[l]) ∈ Metric.ball (1 : ℤ_[l]) ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    refine lt_of_le_of_lt (mem_princ_iff_norm.mp hu) ?_
    rwa [zpow_neg, zpow_natCast, ← inv_pow]
  obtain ⟨v, hv, hvu⟩ := hball hu'
  rwa [← Units.val_injective hvu]

theorem isOpen_princ (a : ℕ) : IsOpen (princ l a : Set ℤ_[l]ˣ) := by
  have hr : ((l : ℝ) ^ (-a : ℤ)) ≠ 0 :=
    (zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _).ne'
  have hset : (princ l a : Set ℤ_[l]ˣ) =
      Units.val ⁻¹' Metric.closedBall (1 : ℤ_[l]) ((l : ℝ) ^ (-a : ℤ)) := by
    ext u
    simp only [SetLike.mem_coe, Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
    exact mem_princ_iff_norm
  rw [hset]
  exact Units.continuous_val.isOpen_preimage _ (IsUltrametricDist.isOpen_closedBall _ hr)

theorem isOpen_iff_princ_le (U : Subgroup ℤ_[l]ˣ) :
    IsOpen (U : Set ℤ_[l]ˣ) ↔ ∃ a, princ l a ≤ U :=
  ⟨fun h => exists_princ_subset (h.mem_nhds U.one_mem),
   fun ⟨a, ha⟩ => Subgroup.isOpen_mono ha (isOpen_princ a)⟩

private theorem red_eq_one_iff {u : ℤ_[l]ˣ} : red l u = 1 ↔ (l : ℤ_[l]) ∣ (u : ℤ_[l]) - 1 := by
  rw [← Units.val_eq_one, show ((red l u : (ZMod l)ˣ) : ZMod l) = PadicInt.toZMod (u : ℤ_[l]) from rfl,
    ← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod,
    RingHom.mem_ker, map_sub, map_one, sub_eq_zero]

private theorem red_surjective : Function.Surjective (red l) := by
  intro v
  obtain ⟨k, hk⟩ := ZMod.natCast_zmod_surjective (v : ZMod l)
  have hx : PadicInt.toZMod (k : ℤ_[l]) = (v : ZMod l) := by rw [map_natCast, hk]
  have hu : IsUnit (k : ℤ_[l]) := by
    by_contra hne
    have hm : (k : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := hne
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, hx] at hm
    exact v.ne_zero hm
  exact ⟨hu.unit, Units.ext (by simp [red, hx])⟩

theorem nu_pos_iff (U : Subgroup ℤ_[l]ˣ) (tr : ℕ) : 0 < nu l U tr ↔ resOrder l U ∣ tr := by
  rw [← Order.one_le_iff_pos, ← Nat.cast_one (R := ℕ∞), le_nu_iff, resOrder,
    ← IsCyclic.exponent_eq_card, Monoid.exponent_dvd_iff_forall_pow_eq_one]
  simp only [pow_one, ← Units.val_pow_eq_pow_val, ← red_eq_one_iff, map_pow]
  constructor
  · rintro h ⟨_, u, hu, rfl⟩
    exact Subtype.ext (h u hu)
  · intro h u hu
    exact congrArg Subtype.val (h ⟨red l u, u, hu, rfl⟩)

theorem princ_le_levelGroup (N : ℕ) (H : Subgroup (ZMod N)ˣ) :
    princ l (N.factorization l) ≤ levelGroup l N H ∧ IsOpen (levelGroup l N H : Set ℤ_[l]ˣ) := by
  have hle : princ l (N.factorization l) ≤ levelGroup l N H := fun u hu => by
    refine mem_levelGroup.mpr ⟨1, H.one_mem, ?_⟩
    rw [map_one]
    exact (MonoidHom.mem_ker.mp hu).symm
  exact ⟨hle, Subgroup.isOpen_mono hle (isOpen_princ _)⟩

theorem levelGroup_eq_top {N : ℕ} (hN : ¬ l ∣ N) (H : Subgroup (ZMod N)ˣ) :
    levelGroup l N H = ⊤ ∧ resOrder l (levelGroup l N H) = l - 1 := by
  have h : levelGroup l N H = ⊤ := by
    rw [eq_top_iff]
    intro u _
    apply (princ_le_levelGroup N H).1
    rw [mem_princ, Nat.factorization_eq_zero_of_not_dvd hN, pow_zero]
    exact one_dvd _
  refine ⟨h, ?_⟩
  rw [h, resOrder, Subgroup.map_top_of_surjective _ red_surjective, Subgroup.card_top,
    Nat.card_eq_fintype_card, ZMod.card_units]

/-! ### Lifting-the-Exponent in `ℤ_[l]` and `nuLeBound` -/

private theorem lte_not_dvd_natCast {m : ℕ} (hm : ¬ l ∣ m) : ¬ (l : ℤ_[l]) ∣ (m : ℤ_[l]) := by
  rintro ⟨c, hc⟩
  apply hm
  have h := congrArg PadicInt.toZMod hc
  rw [map_mul, map_natCast, map_natCast, ZMod.natCast_self, zero_mul] at h
  exact (ZMod.natCast_eq_zero_iff m l).mp h

private theorem lte_not_dvd_of_dvd_sub_one {u : ℤ_[l]} (hu : (l : ℤ_[l]) ∣ u - 1) :
    ¬ (l : ℤ_[l]) ∣ u := by
  intro h
  have h1 : (l : ℤ_[l]) ∣ 1 := by
    have := dvd_sub h hu
    rwa [sub_sub_cancel] at this
  exact PadicInt.prime_p.not_isUnit (isUnit_of_dvd_one h1)

private theorem lte_reduce {u : ℤ_[l]} (hu : (l : ℤ_[l]) ∣ u - 1)
    (h : ∀ k : ℕ, emultiplicity (l : ℤ_[l]) (u ^ l ^ k - 1) =
      emultiplicity (l : ℤ_[l]) (u - 1) + k) (n : ℕ) :
    emultiplicity (l : ℤ_[l]) (u ^ n - 1) =
      emultiplicity (l : ℤ_[l]) (u - 1) + emultiplicity l n := by
  rcases n with - | n
  · simp
  have hfin : FiniteMultiplicity l (n + 1) :=
    Nat.finiteMultiplicity_iff.mpr ⟨(Fact.out : l.Prime).ne_one, n.succ_pos⟩
  rcases emultiplicity_eq_coe.mp hfin.emultiplicity_eq_multiplicity with ⟨⟨c, hc⟩, hnot⟩
  set k := multiplicity l (n + 1) with hk
  have hcl : ¬ l ∣ c := by
    rintro ⟨d, rfl⟩
    exact hnot ⟨d, by rw [hc, pow_succ, mul_assoc]⟩
  have hx : (l : ℤ_[l]) ∣ u ^ l ^ k - 1 := by
    have := sub_dvd_pow_sub_pow u 1 (l ^ k)
    rw [one_pow] at this
    exact hu.trans this
  have e : u ^ (l ^ k * c) - 1 = (u ^ l ^ k) ^ c - 1 ^ c := by rw [one_pow, pow_mul]
  rw [hfin.emultiplicity_eq_multiplicity, ← hk]
  conv_lhs => rw [hc, e]
  rw [emultiplicity_pow_sub_pow_of_prime PadicInt.prime_p hx (lte_not_dvd_of_dvd_sub_one hx)
    (lte_not_dvd_natCast hcl), h k]

theorem emultiplicity_pow_sub_one_odd (hl : l ≠ 2) {u : ℤ_[l]} (hu : (l : ℤ_[l]) ∣ u - 1) (n : ℕ) :
    emultiplicity (l : ℤ_[l]) (u ^ n - 1) =
      emultiplicity (l : ℤ_[l]) (u - 1) + emultiplicity l n := by
  refine lte_reduce hu (fun k => ?_) n
  have h := emultiplicity_pow_prime_pow_sub_pow_prime_pow (p := l) (x := u) (y := 1)
    PadicInt.prime_p ((Fact.out : l.Prime).odd_of_ne_two hl) hu (lte_not_dvd_of_dvd_sub_one hu) k
  rwa [one_pow] at h

private theorem lte_two_step (hl : l = 2) {w : ℤ_[l]} (hw : (l : ℤ_[l]) ^ 2 ∣ w - 1) :
    emultiplicity (l : ℤ_[l]) (w ^ l - 1) = emultiplicity (l : ℤ_[l]) (w - 1) + 1 := by
  subst hl
  have hp : Prime ((2 : ℕ) : ℤ_[2]) := PadicInt.prime_p
  have h2 : ((2 : ℕ) : ℤ_[2]) ∣ w - 1 := (dvd_pow_self _ two_ne_zero).trans hw
  rw [show w ^ 2 - 1 = (w - 1) * (w + 1) by ring, emultiplicity_mul hp]
  congr 1
  rw [← Nat.cast_one (R := ℕ∞)]
  refine emultiplicity_eq_coe.2 ⟨?_, ?_⟩
  · rw [pow_one, show w + 1 = (w - 1) + ((2 : ℕ) : ℤ_[2]) by push_cast; ring]
    exact dvd_add h2 (dvd_refl _)
  · rw [one_add_one_eq_two]
    intro h
    have h3 := dvd_sub h hw
    rw [show (w + 1) - (w - 1) = ((2 : ℕ) : ℤ_[2]) * 1 by push_cast; ring, pow_two,
      mul_dvd_mul_iff_left hp.ne_zero] at h3
    exact hp.not_isUnit (isUnit_of_dvd_one h3)

theorem emultiplicity_pow_sub_one_sq {u : ℤ_[l]} (hu : (l : ℤ_[l]) ^ 2 ∣ u - 1) (n : ℕ) :
    emultiplicity (l : ℤ_[l]) (u ^ n - 1) =
      emultiplicity (l : ℤ_[l]) (u - 1) + emultiplicity l n := by
  have hu1 : (l : ℤ_[l]) ∣ u - 1 := (dvd_pow_self _ two_ne_zero).trans hu
  by_cases hl : l = 2
  · refine lte_reduce hu1 (fun k => ?_) n
    induction k with
    | zero => simp
    | succ k ih =>
      have hw : (l : ℤ_[l]) ^ 2 ∣ u ^ l ^ k - 1 := by
        have := sub_dvd_pow_sub_pow u 1 (l ^ k)
        rw [one_pow] at this
        exact hu.trans this
      rw [pow_succ, pow_mul, lte_two_step hl hw, ih]
      push_cast
      ring
  · exact emultiplicity_pow_sub_one_odd hl hu1 n

private theorem nu_le_emult {U : Subgroup ℤ_[l]ˣ} {u : ℤ_[l]ˣ} (hu : u ∈ U) (tr : ℕ) :
    nu l U tr ≤ emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) ^ tr - 1) := by
  refine ENat.forall_natCast_le_iff_le.mp fun n hn => ?_
  rw [le_nu_iff] at hn
  exact le_emultiplicity_of_pow_dvd (hn u hu)

private theorem exists_unit_sub_one_eq_pow {a : ℕ} (ha : 1 ≤ a) :
    ∃ u : ℤ_[l]ˣ, (u : ℤ_[l]) - 1 = (l : ℤ_[l]) ^ a := by
  have h : IsUnit (1 + (l : ℤ_[l]) ^ a) := by
    by_contra hn
    have h1 : ‖1 + (l : ℤ_[l]) ^ a‖ < 1 := PadicInt.not_isUnit_iff.mp hn
    rw [PadicInt.norm_lt_one_iff_dvd] at h1
    have h2 : (l : ℤ_[l]) ∣ (l : ℤ_[l]) ^ a := dvd_pow_self _ (by omega)
    exact PadicInt.prime_p.not_dvd_one ((dvd_add_left h2).mp h1)
  exact ⟨h.unit, by simp⟩

theorem nu_ne_top {U : Subgroup ℤ_[l]ˣ} (hU : IsOpen (U : Set ℤ_[l]ˣ)) {tr : ℕ} (htr : tr ≠ 0) :
    nu l U tr ≠ ⊤ := by
  obtain ⟨s, h⟩ := (isOpen_iff_princ_le U).mp hU
  obtain ⟨u, hu⟩ := exists_unit_sub_one_eq_pow (l := l) (a := s + 2) (by omega)
  have hm : u ∈ U := h (by rw [mem_princ, hu]; exact pow_dvd_pow _ (by omega))
  have h1 : (l : ℤ_[l]) ^ 2 ∣ (u : ℤ_[l]) - 1 := by rw [hu]; exact pow_dvd_pow _ (by omega)
  have hle := nu_le_emult hm tr
  rw [emultiplicity_pow_sub_one_sq h1, hu, emultiplicity_pow_self_of_prime PadicInt.prime_p,
    ← padicValNat_eq_emultiplicity htr, ← Nat.cast_add] at hle
  exact ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle

/-- Explicit upper bound `nu l U e ≤ nuBound l N e` whenever `princ l (v_l(N)) ≤ U` and `e ≠ 0`. -/
theorem nuLeBound (l : ℕ) [Fact l.Prime] (N e : ℕ) (U : Subgroup ℤ_[l]ˣ)
    (h : princ l (N.factorization l) ≤ U) (he : e ≠ 0) :
    nu l U e ≤ (nuBound l N e : ℕ∞) := by
  have hp : l.Prime := Fact.out
  unfold nuBound
  by_cases hc : l ∣ N ∨ l - 1 ∣ e
  · rw [if_pos hc]
    set a := max (N.factorization l) (if l = 2 then 2 else 1) with ha
    have ha1 : 1 ≤ a := le_trans (by split_ifs <;> omega) (le_max_right _ _)
    obtain ⟨u, hu⟩ := exists_unit_sub_one_eq_pow (l := l) ha1
    have hm : u ∈ U := h (by rw [mem_princ, hu]; exact pow_dvd_pow _ (le_max_left _ _))
    have hem : emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) - 1) = a := by
      rw [hu, emultiplicity_pow_self_of_prime PadicInt.prime_p]
    have key : emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) ^ e - 1) =
        emultiplicity (l : ℤ_[l]) ((u : ℤ_[l]) - 1) + emultiplicity l e := by
      by_cases hl : l = 2
      · refine emultiplicity_pow_sub_one_sq ?_ e
        rw [hu]
        refine pow_dvd_pow _ ?_
        rw [ha, if_pos hl]
        exact le_max_right _ _
      · refine emultiplicity_pow_sub_one_odd hl ?_ e
        rw [hu]
        exact dvd_pow_self _ (by omega)
    have hle := nu_le_emult hm e
    rw [key, hem, ← padicValNat_eq_emultiplicity he] at hle
    rw [Nat.cast_add, Nat.factorization_def _ hp]
    exact hle
  · rw [if_neg hc]
    rw [not_or] at hc
    obtain ⟨h1, h2⟩ := levelGroup_eq_top (l := l) hc.1 ⊤
    rw [h1] at h2
    have hU : U = ⊤ := by
      rw [eq_top_iff]
      intro u _
      apply h
      rw [mem_princ, Nat.factorization_eq_zero_of_not_dvd hc.1, pow_zero]
      exact one_dvd _
    subst hU
    have h3 := hc.2
    rw [← h2, ← nu_pos_iff] at h3
    simpa using not_lt.mp h3

end PadicUnitSubgroups

/-! ### `QZ` Torsion Embeddings & Torsion-Level `Module.length` Invariants -/

section TorsionLevelLength

private theorem qzTor_smul_mk (l : ℕ) [Fact l.Prime] (x : ℤ_[l]) (q : ℚ_[l]) :
    x • QZ.mk l q = QZ.mk l ((x : ℚ_[l]) * q) := rfl

private theorem qzTor_mk_eq_zero (l : ℕ) [Fact l.Prime] (q : ℚ_[l]) :
    QZ.mk l q = 0 ↔ ∃ z : ℤ_[l], (z : ℚ_[l]) = q :=
  Submodule.Quotient.mk_eq_zero (ZlSub l)

private theorem qzTor_key (l : ℕ) [Fact l.Prime] (r : ℕ) (x : ℤ_[l]) :
    x • QZ.mk l (((l : ℚ_[l]) ^ r)⁻¹) = 0 ↔ PadicInt.toZModPow r x = 0 := by
  have hl : ((l : ℚ_[l]) ^ r) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  rw [qzTor_smul_mk, qzTor_mk_eq_zero, ← RingHom.mem_ker, PadicInt.ker_toZModPow,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, Subtype.ext ?_⟩
    have : ((z * (l : ℤ_[l]) ^ r : ℤ_[l]) : ℚ_[l]) = (z : ℚ_[l]) * (l : ℚ_[l]) ^ r := by
      push_cast; rfl
    rw [this, hz]
    field_simp
  · rintro ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    push_cast
    field_simp

/-- Every element of `QZ l = ℚ_[l] / ℤ_[l]` is `l^r`-torsion, and the `l^r`-torsion submodule
embeds isomorphically from `ZMod (l ^ r)` compatibly with `PadicInt.toZModPow r`. -/
theorem qz_torsion_zmod_embedding (l : ℕ) [Fact l.Prime] :
    (∀ a : QZ l, ∃ r : ℕ, (l : ℤ_[l]) ^ r • a = 0) ∧
    ∀ r : ℕ, ∃ ι : ZMod (l ^ r) →+ QZ l, Function.Injective ι ∧
      (∀ a : QZ l, (l : ℤ_[l]) ^ r • a = 0 ↔ a ∈ Set.range ι) ∧
      ∀ (x : ℤ_[l]) (y : ZMod (l ^ r)), ι (PadicInt.toZModPow r x * y) = x • ι y := by
  have hp : l.Prime := Fact.out
  refine ⟨fun a => ?_, fun r => ?_⟩
  · obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) a
    have hlt : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
    have hpos : (0 : ℝ) < (‖q‖ + 1)⁻¹ := by positivity
    obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hpos hlt
    refine ⟨r, ?_⟩
    change (l : ℤ_[l]) ^ r • QZ.mk l q = 0
    rw [qzTor_smul_mk, qzTor_mk_eq_zero]
    have hle : ‖(l : ℚ_[l]) ^ r * q‖ ≤ 1 := by
      rw [norm_mul, norm_pow]
      calc ‖(l : ℚ_[l])‖ ^ r * ‖q‖ ≤ (‖q‖ + 1)⁻¹ * (‖q‖ + 1) :=
            mul_le_mul hr.le (by linarith) (norm_nonneg _) hpos.le
        _ = 1 := inv_mul_cancel₀ (by positivity)
    exact ⟨⟨_, hle⟩, by push_cast; rfl⟩
  · have hl : ((l : ℚ_[l]) ^ r) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)
    set e : QZ l := QZ.mk l (((l : ℚ_[l]) ^ r)⁻¹) with he
    have hs : Function.Surjective (PadicInt.toZModPow (p := l) r) := by
      haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ hp.ne_zero⟩
      exact ZMod.ringHom_surjective _
    have hwd : ∀ x x' : ℤ_[l], PadicInt.toZModPow r x = PadicInt.toZModPow r x' →
        x • e = x' • e := by
      intro x x' h
      rw [← sub_eq_zero, ← sub_smul, he, qzTor_key, map_sub, h, sub_self]
    have hinv := Function.surjInv_eq hs
    let ι : ZMod (l ^ r) →+ QZ l := AddMonoidHom.mk' (fun y => Function.surjInv hs y • e) (by
      intro y y'
      rw [← add_smul]
      apply hwd
      rw [map_add, hinv, hinv, hinv])
    have hι : ∀ x : ℤ_[l], ι (PadicInt.toZModPow r x) = x • e := fun x => hwd _ _ (hinv _)
    refine ⟨ι, ?_, fun a => ⟨fun ha => ?_, ?_⟩, fun x y => ?_⟩
    · rw [injective_iff_map_eq_zero]
      intro y hy
      obtain ⟨x, rfl⟩ := hs y
      rw [hι, he, qzTor_key] at hy
      exact hy
    · obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) a
      change (l : ℤ_[l]) ^ r • QZ.mk l q = 0 at ha
      rw [qzTor_smul_mk, qzTor_mk_eq_zero] at ha
      obtain ⟨z, hz⟩ := ha
      refine ⟨PadicInt.toZModPow r z, ?_⟩
      change ι (PadicInt.toZModPow r z) = QZ.mk l q
      rw [hι, he, qzTor_smul_mk, hz]
      congr 1
      push_cast
      field_simp
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := hs y
      rw [hι, smul_smul, he, qzTor_key, ← RingHom.mem_ker, PadicInt.ker_toZModPow]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · obtain ⟨x', rfl⟩ := hs y
      rw [← map_mul, hι, hι, mul_smul]

private lemma card_eq_card_residueField_of_isSimpleModule (O : Type*) [CommRing O] [IsLocalRing O]
    (S : Type*) [AddCommGroup S] [Module O S] [IsSimpleModule O S] :
    Nat.card S = Nat.card (IsLocalRing.ResidueField O) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := (isSimpleModule_iff_quot_maximal (R := O) (M := S)).mp ‹_›
  have hI' : I = IsLocalRing.maximalIdeal O := IsLocalRing.eq_maximalIdeal hI
  subst hI'
  exact Nat.card_congr e.toEquiv

theorem exists_length_eq_and_card_eq_pow_of_isFiniteLength (O : Type*) [CommRing O] [IsLocalRing O]
    (M : Type*) [AddCommGroup M] [Module O M] (h : IsFiniteLength O M) :
    ∃ n : ℕ, Module.length O M = n ∧ Nat.card M = Nat.card (IsLocalRing.ResidueField O) ^ n := by
  induction h with
  | @of_subsingleton M _ _ _ =>
    refine ⟨0, ?_, ?_⟩
    · simp
    · simp
  | @of_simple_quotient M _ _ N _ _ ih =>
    obtain ⟨n, hl, hc⟩ := ih
    refine ⟨n + 1, ?_, ?_⟩
    · rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N), hl, Module.length_eq_one_iff.mpr ‹_›]
      push_cast
      rfl
    · rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N.toAddSubgroup]
      change Nat.card (M ⧸ N) * Nat.card N = _
      rw [card_eq_card_residueField_of_isSimpleModule O (M ⧸ N), hc, pow_succ, mul_comm]

theorem exists_length_eq_and_card_eq_pow (O : Type*) [CommRing O] [IsLocalRing O]
    (M : Type*) [AddCommGroup M] [Module O M] [Finite M] :
    ∃ n : ℕ, Module.length O M = n ∧ Nat.card M = Nat.card (IsLocalRing.ResidueField O) ^ n :=
  exists_length_eq_and_card_eq_pow_of_isFiniteLength O M
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)

theorem card_residueField_padicInt (l : ℕ) [Fact l.Prime] :
    Nat.card (IsLocalRing.ResidueField ℤ_[l]) = l := by
  rw [Nat.card_congr (PadicInt.residueField (p := l)).toEquiv, Nat.card_zmod]

theorem padicInt_length_eq_top_of_infinite (l : ℕ) [Fact l.Prime] (X : Type*) [AddCommGroup X]
    [Module ℤ_[l] X] (h : ¬ Finite X) : Module.length ℤ_[l] X = ⊤ := by
  by_contra hne
  obtain ⟨n, -, hc⟩ := exists_length_eq_and_card_eq_pow_of_isFiniteLength ℤ_[l] X
    (Module.length_ne_top_iff.mp hne)
  rw [card_residueField_padicInt] at hc
  exact h (Nat.finite_of_card_ne_zero (by
    rw [hc]; exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero))

theorem padicInt_length_eq_of_card_eq (l : ℕ) [Fact l.Prime] (X Y : Type*) [AddCommGroup X]
    [Module ℤ_[l] X] [AddCommGroup Y] [Module ℤ_[l] Y] [Finite X] [Finite Y]
    (h : Nat.card X = Nat.card Y) : Module.length ℤ_[l] X = Module.length ℤ_[l] Y := by
  obtain ⟨n, hn, hc⟩ := exists_length_eq_and_card_eq_pow ℤ_[l] X
  obtain ⟨m, hm, hd⟩ := exists_length_eq_and_card_eq_pow ℤ_[l] Y
  rw [card_residueField_padicInt] at hc hd
  have : n = m := Nat.pow_right_injective (Fact.out : l.Prime).two_le (by
    simp only; rw [← hc, ← hd, h])
  rw [hn, hm, this]

/-- Fundamental `ℤ_[l]`-length comparison via separated quotient filtration and exhaustive
submodule filtration with matching finite cardinalities. -/
theorem padicInt_length_eq_of_card_quotient_eq_card_submodule (l : ℕ) [Fact l.Prime]
    (X Y : Type*) [AddCommGroup X] [Module ℤ_[l] X] [AddCommGroup Y] [Module ℤ_[l] Y]
    (N : ℕ → Submodule ℤ_[l] X) (P : ℕ → Submodule ℤ_[l] Y) (c : ℕ) (hN : Antitone N)
    (hsep : ∀ x, (∀ r, x ∈ N r) → x = 0) (hP : Monotone P) (hex : ∀ y, ∃ r, y ∈ P r)
    (hc : ∀ r, c ≤ r → Finite (P r) ∧ Nat.card (X ⧸ N r) = Nat.card (P r)) :
    Module.length ℤ_[l] X = Module.length ℤ_[l] Y := by
  have key : ∀ r0, c ≤ r0 → (∀ r, r0 ≤ r → Nat.card (P r) ≤ Nat.card (P r0)) →
      Module.length ℤ_[l] X = Module.length ℤ_[l] Y := by
    intro r0 h0 hb
    have hfin : ∀ r, c ≤ r → Finite (X ⧸ N r) := fun r hr => by
      have := (hc r hr).1
      exact Nat.finite_of_card_ne_zero (by rw [(hc r hr).2]; exact Nat.card_pos.ne')
    have hPtop : P r0 = ⊤ := by
      rw [eq_top_iff]
      intro y _
      obtain ⟨r, hr⟩ := hex y
      have hle : r0 ≤ max r r0 := le_max_right _ _
      have := (hc _ (h0.trans hle)).1
      have hbij : Function.Bijective (Submodule.inclusion (hP hle)) :=
        (Submodule.inclusion_injective _).bijective_of_nat_card_le (hb _ hle)
      obtain ⟨z, hz⟩ := hbij.2 ⟨y, hP (le_max_left r r0) hr⟩
      have : (z : Y) = y := congrArg Subtype.val hz
      exact this ▸ z.2
    have hNbot : N r0 = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      refine (Submodule.mem_bot _).mpr (hsep x fun r => ?_)
      have hle : r0 ≤ max r r0 := le_max_right _ _
      have := hfin _ (h0.trans hle)
      have hbij : Function.Bijective (Submodule.factor (hN hle)) :=
        (Submodule.factor_surjective _).bijective_of_nat_card_le (by
          rw [(hc _ (h0.trans hle)).2, (hc _ h0).2]; exact hb _ hle)
      have h1 : (N (max r r0)).mkQ x = 0 := hbij.1 (by
        rw [map_zero, Submodule.factor_mk]
        exact (Submodule.Quotient.mk_eq_zero _).mpr hx)
      exact hN (le_max_left r r0) ((Submodule.Quotient.mk_eq_zero _).mp h1)
    have eX : (X ⧸ N r0) ≃ₗ[ℤ_[l]] X := Submodule.quotEquivOfEqBot _ hNbot
    have eY : (P r0) ≃ₗ[ℤ_[l]] Y := LinearEquiv.ofTop _ hPtop
    have := hfin _ h0
    have := (hc _ h0).1
    rw [← eX.length_eq, ← eY.length_eq]
    exact padicInt_length_eq_of_card_eq l _ _ (hc _ h0).2
  have bdd : ∀ B : ℕ, (∀ r, c ≤ r → Nat.card (P r) ≤ B) →
      Module.length ℤ_[l] X = Module.length ℤ_[l] Y := by
    intro B hB
    have hS : ((fun r => Nat.card (P r)) '' {r | c ≤ r}).Finite :=
      (Set.finite_le_nat B).subset (by rintro _ ⟨r, hr, rfl⟩; exact hB r hr)
    obtain ⟨_, ⟨r0, hr0, rfl⟩, hmax⟩ := Set.exists_max_image _ id hS ⟨_, c, le_refl c, rfl⟩
    exact key r0 hr0 fun r hr => hmax _ ⟨r, le_trans hr0 hr, rfl⟩
  by_cases hX : Finite X
  · refine bdd (Nat.card X) fun r hr => ?_
    rw [← (hc r hr).2]
    exact Nat.card_le_card_of_surjective _ (N r).mkQ_surjective
  by_cases hY : Finite Y
  · exact bdd (Nat.card Y) fun r _ =>
      Nat.card_le_card_of_injective _ (P r).subtype_injective
  rw [padicInt_length_eq_top_of_infinite l X hX, padicInt_length_eq_top_of_infinite l Y hY]

/-- The `l^r`-multiple submodule `l^r • X ≤ X`. -/
abbrev lpow (l : ℕ) [Fact l.Prime] (X : Type*) [AddCommGroup X] [Module ℤ_[l] X] (r : ℕ) :
    Submodule ℤ_[l] X :=
  LinearMap.range (LinearMap.lsmul ℤ_[l] X ((l : ℤ_[l]) ^ r))

theorem lpow_anti (l : ℕ) [Fact l.Prime] (X : Type*) [AddCommGroup X] [Module ℤ_[l] X] :
    Antitone (lpow l X) := by
  intro r s h x ⟨y, hy⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact ⟨(l : ℤ_[l]) ^ k • y, by
    rw [← hy, pow_add, LinearMap.lsmul_apply, LinearMap.lsmul_apply, mul_smul]⟩

theorem lpow_sep (l : ℕ) [Fact l.Prime] (X : Type*) [AddCommGroup X] [Module ℤ_[l] X]
    [Module.Finite ℤ_[l] X] (x : X) (h : ∀ r, x ∈ lpow l X r) : x = 0 := by
  have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := X) (IsLocalRing.maximalIdeal ℤ_[l])
    (IsLocalRing.maximalIdeal.isMaximal ℤ_[l]).ne_top
  rw [← Submodule.mem_bot ℤ_[l], ← hK, Submodule.mem_iInf]
  intro r
  obtain ⟨y, rfl⟩ := h r
  refine Submodule.smul_mem_smul ?_ Submodule.mem_top
  rw [PadicInt.maximalIdeal_eq_span_p]
  exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) r

theorem card_quot_lpow {l : ℕ} [Fact l.Prime] {X Y : Type*} [AddCommGroup X] [Module ℤ_[l] X]
    [AddCommGroup Y] (r : ℕ) (π : X →+ Y) (hs : Function.Surjective π)
    (hk : ∀ x, π x = 0 ↔ ∃ y, (l : ℤ_[l]) ^ r • y = x) :
    Nat.card (X ⧸ lpow l X r) = Nat.card Y := by
  have : (lpow l X r).toAddSubgroup = π.ker := by
    ext x; exact (hk x).symm
  rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective π hs).toEquiv, ← this]
  rfl

/-- **Torsion-Level Length Invariance (`LengthEqLengthInvariantsOfTorsionLevels`)**:
if a finitely generated `ℤ_[l]`-module `X` has `#(X / l^r X) = #H⁰(Γ, N_r)` for all `r > 0`, where
`N_r ≃ A[l^r]` equivariantly for an `l`-primary torsion `Γ`-module `A`, then
`Module.length ℤ_[l] X = Module.length ℤ_[l] (H0 σ)`. -/
theorem length_eq_length_invariants_of_torsion_levels {l : ℕ} [Fact l.Prime]
    {Γ : Type*} [Group Γ] {X : Type*} [AddCommGroup X] [Module ℤ_[l] X] [Module.Finite ℤ_[l] X]
    {A : Type*} [AddCommGroup A] [Module ℤ_[l] A] (σ : Representation ℤ_[l] Γ A)
    (hA : ∀ a : A, ∃ r : ℕ, (l : ℤ_[l]) ^ r • a = 0)
    (N : ℕ → Type*) [∀ r, AddCommGroup (N r)] [∀ r, Module (ZMod (l ^ r)) (N r)] [∀ r, Finite (N r)]
    (τ : ∀ r, Representation (ZMod (l ^ r)) Γ (N r)) (ι : ∀ r, N r →+ A)
    (hι : ∀ r, Function.Injective (ι r))
    (hr : ∀ r (a : A), (l : ℤ_[l]) ^ r • a = 0 ↔ a ∈ Set.range (ι r))
    (he : ∀ r g n, ι r (τ r g n) = σ g (ι r n))
    (hc : ∀ r, 0 < r → Nat.card (X ⧸ lpow l X r) = Nat.card (H0 (τ r))) :
    Module.length ℤ_[l] X = Module.length ℤ_[l] (H0 σ) := by
  refine padicInt_length_eq_of_card_quotient_eq_card_submodule l X (H0 σ) (lpow l X)
    (fun r => Submodule.torsionBy ℤ_[l] (H0 σ) ((l : ℤ_[l]) ^ r)) 1 (lpow_anti l X) (lpow_sep l X)
    (fun r s h => Submodule.torsionBy_le_torsionBy_of_dvd _ _ (pow_dvd_pow _ h))
    (fun y => (hA y.1).imp fun r h => Subtype.ext h) fun r h => ?_
  let f : H0 (τ r) → Submodule.torsionBy ℤ_[l] (H0 σ) ((l : ℤ_[l]) ^ r) := fun n =>
    ⟨⟨ι r n.1, fun g => by rw [← he, n.2 g]⟩, Subtype.ext ((hr r _).2 ⟨n.1, rfl⟩)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => Subtype.ext (hι r (congrArg (fun x => x.1.1) h)), fun a => ?_⟩
    obtain ⟨n, hn⟩ := (hr r a.1.1).1 (congrArg Subtype.val a.2)
    exact ⟨⟨n, fun g => hι r (by rw [he, hn, a.1.2 g])⟩, Subtype.ext (Subtype.ext hn)⟩
  exact ⟨Finite.of_surjective f hf.2, (hc r h).trans (Nat.card_eq_of_bijective f hf)⟩

/-- Exact length of the `l^n`-torsion submodule of `QZ l = ℚ_[l] / ℤ_[l]`: equals `n`. -/
theorem length_torsionBy_QZ (l : ℕ) [Fact l.Prime] (n : ℕ) :
    Module.length ℤ_[l] (Submodule.torsionBy ℤ_[l] (QZ l) ((l : ℤ_[l]) ^ n)) = n := by
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ι, hι, hr, -⟩ := (qz_torsion_zmod_embedding l).2 n
  let e : ZMod (l ^ n) ≃ Submodule.torsionBy ℤ_[l] (QZ l) ((l : ℤ_[l]) ^ n) :=
    Equiv.ofBijective (fun y => ⟨ι y, (hr (ι y)).2 ⟨y, rfl⟩⟩)
      ⟨fun a b h => hι (congrArg Subtype.val h), fun ⟨a, ha⟩ => by
        obtain ⟨y, hy⟩ := (hr a).1 ha
        exact ⟨y, Subtype.ext hy⟩⟩
  haveI : Finite (Submodule.torsionBy ℤ_[l] (QZ l) ((l : ℤ_[l]) ^ n)) := Finite.of_equiv _ e
  obtain ⟨m, hm, hc⟩ := exists_length_eq_and_card_eq_pow ℤ_[l]
    (Submodule.torsionBy ℤ_[l] (QZ l) ((l : ℤ_[l]) ^ n))
  rw [card_residueField_padicInt, ← Nat.card_congr e, Nat.card_zmod] at hc
  have hmn : n = m := Nat.pow_right_injective (Fact.out : l.Prime).two_le hc
  rw [hm, hmn]

private theorem torsionBy_pow_le_twistInv {l : ℕ} [Fact l.Prime] {U : Subgroup ℤ_[l]ˣ}
    {tr n : ℕ} (h : (n : ℕ∞) ≤ nu l U tr) :
    Submodule.torsionBy ℤ_[l] (QZ l) ((l : ℤ_[l]) ^ n) ≤ twistInv l (QZ l) U tr := by
  intro x hx
  rw [Submodule.mem_torsionBy_iff] at hx
  rw [mem_twistInv]
  intro u hu
  obtain ⟨c, hc⟩ := le_nu_iff.mp h u hu
  have e2 : ((u : ℤ_[l]) ^ tr) • x = x + ((u : ℤ_[l]) ^ tr - 1) • x := by
    rw [sub_smul, one_smul]; abel
  rw [e2, hc, mul_comm, mul_smul, hx, smul_zero, add_zero]

theorem twistInv_eq_torsionBy {l : ℕ} [Fact l.Prime] {U : Subgroup ℤ_[l]ˣ} {tr n : ℕ}
    (h : nu l U tr = n) :
    twistInv l (QZ l) U tr = Submodule.torsionBy ℤ_[l] (QZ l) ((l : ℤ_[l]) ^ n) := by
  apply le_antisymm
  · intro x hx
    rw [mem_twistInv] at hx
    rw [Submodule.mem_torsionBy_iff]
    obtain ⟨w, ⟨v, hv, rfl⟩, hdvd, hndvd⟩ := exists_exact_of_nuStar_eq h
    obtain ⟨c, hc⟩ := hdvd
    have hcu : IsUnit c := by
      by_contra hnu
      rw [PadicInt.not_isUnit_iff, PadicInt.norm_lt_one_iff_dvd] at hnu
      obtain ⟨d, hd⟩ := hnu
      apply hndvd
      refine ⟨d, ?_⟩
      rw [hc, hd, pow_succ]
      ring
    have h1 : ((v : ℤ_[l]) ^ tr - 1) • x = 0 := by
      rw [sub_smul, one_smul, hx v hv, sub_self]
    rw [hc, mul_comm, mul_smul] at h1
    exact (hcu.smul_eq_zero).mp h1
  · exact torsionBy_pow_le_twistInv (by rw [h])

/-- Exact length formula (`LenTwist`): `Module.length ℤ_[l] (twistInv l (QZ l) U tr) = nu l U tr`. -/
theorem lenTwist (l : ℕ) [Fact l.Prime] (U : Subgroup ℤ_[l]ˣ) (tr : ℕ) :
    Module.length ℤ_[l] (twistInv l (QZ l) U tr) = nu l U tr := by
  by_cases htop : nu l U tr = ⊤
  · rw [htop, ENat.eq_top_iff_forall_ge]
    intro m
    have hle : Submodule.torsionBy ℤ_[l] (QZ l) ((l : ℤ_[l]) ^ m) ≤ twistInv l (QZ l) U tr :=
      torsionBy_pow_le_twistInv (by rw [htop]; exact le_top)
    calc (m : ℕ∞) = Module.length ℤ_[l] (Submodule.torsionBy ℤ_[l] (QZ l) ((l : ℤ_[l]) ^ m)) :=
          (length_torsionBy_QZ l m).symm
      _ ≤ Module.length ℤ_[l] (twistInv l (QZ l) U tr) := length_mono_of_le hle
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    rw [twistInv_eq_torsionBy hn.symm, length_torsionBy_QZ, hn]

end TorsionLevelLength

end PadicUnitsAndNu

/-! ## Section 2: Roots of Unity under Inertia & Decomposition, Cyclotomic Splitting, and `cardAbove` -/

section RootsAndCyclotomicSplitting

/-- The subgroup of `(ZMod N)ˣ` fixing an intermediate field `E ⊆ K = ℚ(ζ_N)`. -/
def fieldSubgroup (N : ℕ) [NeZero N] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {N} ℚ K] (E : IntermediateField ℚ K) : Subgroup (ZMod N)ˣ :=
  E.fixingSubgroup.map (IsCyclotomicExtension.Rat.galEquivZMod N K).toMonoidHom

/-- The number of primes of `𝓞 F` lying over `l` is at most `[F : ℚ]` (`CardAbove`). -/
theorem cardAbove (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) :
    D.S.card ≤ Module.finrank ℚ F := by
  classical
  have hl : l.Prime := Fact.out
  have hprod_dvd : (∏ v ∈ D.S, v.asIdeal) ∣ Ideal.span {((l : ℕ) : 𝓞 F)} := by
    refine Finset.prod_dvd_of_coprime (fun v _ w _ hvw => ?_) (fun v hv => ?_)
    · rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
      by_contra hne
      have hle : v.asIdeal ⊔ w.asIdeal = v.asIdeal :=
        (v.isMaximal.eq_of_le hne le_sup_left).symm
      have hwv : w.asIdeal ≤ v.asIdeal := le_sup_right.trans hle.le
      exact hvw (HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top hwv).symm)
    · rw [Ideal.dvd_span_singleton]
      rw [← Finset.mem_coe, D.hS] at hv
      exact hv
  have hnorm_dvd : (∏ v ∈ D.S, Ideal.absNorm v.asIdeal) ∣ l ^ Module.finrank ℚ F := by
    have h1 := map_dvd Ideal.absNorm hprod_dvd
    rw [map_prod, Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank] at h1
    exact h1
  have hpow_le : l ^ D.S.card ≤ ∏ v ∈ D.S, Ideal.absNorm v.asIdeal := by
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod (fun _ _ => Nat.zero_le l) fun v hv => ?_
    have hv_dvd : Ideal.absNorm v.asIdeal ∣ l ^ Module.finrank ℚ F :=
      (Finset.dvd_prod_of_mem _ hv).trans hnorm_dvd
    have hv_ne1 : Ideal.absNorm v.asIdeal ≠ 1 := by
      intro h1
      exact v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h1)
    have hv_pos : 0 < Ideal.absNorm v.asIdeal :=
      Nat.pos_of_ne_zero (fun h0 => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0))
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hl).mp hv_dvd
    have hk0 : k ≠ 0 := by rintro rfl; exact hv_ne1 (by simpa using hk)
    rw [hk]
    exact le_self_pow₀ hl.one_lt.le hk0
  have hle : l ^ D.S.card ≤ l ^ Module.finrank ℚ F :=
    hpow_le.trans (Nat.le_of_dvd (pow_pos hl.pos _) hnorm_dvd)
  exact (Nat.pow_le_pow_iff_right hl.one_lt).mp hle

/-- **`IneFixRoots`**: For `v_A(l) < 1` and `gcd(m, l) = 1`, `m`-th roots of unity are distinct
modulo the maximal ideal of `A` and fixed pointwise by `Ine (F := F) A`. -/
theorem ineFixRoots (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω)
    (hl : A.valuation (l : Ω) < 1) (m : ℕ) (hm : m.Coprime l) (ζ : Ω) (hζ : ζ ^ m = 1) :
    (∀ ξ : Ω, ξ ^ m = 1 → A.valuation (ξ - ζ) < 1 → ξ = ζ) ∧
      ∀ g ∈ Ine (F := F) A, g ζ = ζ := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (Fact.out : l.Prime).one_lt.ne' ((Nat.coprime_zero_left _).mp hm)
  have hv1 : ∀ x : Ω, x ^ m = 1 → A.valuation x = 1 :=
    fun x hx => valuation_eq_one_of_pow_eq_one A hm0 hx
  have hint : ∀ a : ℤ, A.valuation (a : Ω) ≤ 1 := fun a => by
    exact_mod_cast A.valuation_le_one (a : A)
  have hmv : ¬ A.valuation (m : Ω) < 1 := by
    intro hlt
    have hg : ((Nat.gcd m l : ℕ) : ℤ) = m * Nat.gcdA m l + l * Nat.gcdB m l := Nat.gcd_eq_gcd_ab m l
    rw [Nat.Coprime.gcd_eq_one hm] at hg
    have hΩ := congrArg (Int.cast : ℤ → Ω) hg
    push_cast at hΩ
    have h1 : A.valuation (1 : Ω) < 1 := by
      rw [hΩ]
      apply Valuation.map_add_lt
      · rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hlt
      · rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hl
    simp at h1
  have part1 : ∀ ξ : Ω, ξ ^ m = 1 → A.valuation (ξ - ζ) < 1 → ξ = ζ :=
    fun ξ hξ hlt => eq_of_pow_eq_one A hmv hξ hζ hlt
  refine ⟨part1, fun g hg => ?_⟩
  apply part1
  · rw [← map_pow, hζ, map_one]
  · exact (mem_Ine.mp hg).2 ζ (hv1 ζ hζ).le

/-- **`DecActRoots`**: For `v_A(l) < 1` and `gcd(m, l) = 1`, every element `g ∈ Dec A` acts on
all `m`-th roots of unity as a power of Frobenius `ζ ↦ ζ ^ (l ^ k)`. -/
theorem decActRoots (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω)
    (hA : A.valuation (l : Ω) < 1) (m : ℕ) (hm : m.Coprime l) (g : G F Ω)
    (hg : g ∈ Dec (F := F) A) :
    ∃ k : ℕ, ∀ ζ : Ω, ζ ^ m = 1 → g ζ = ζ ^ l ^ k := by
  have hl : l.Prime := Fact.out
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hm
    exact hl.one_lt.ne' hm
  haveI : NeZero m := ⟨hm0⟩
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : NeZero (m : Ω) := ⟨Nat.cast_ne_zero.mpr hm0⟩
  obtain ⟨ζ0, hζ0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  have hmemA : ∀ ξ : Ω, ξ ^ m = 1 → ξ ∈ A := fun ξ hξ =>
    (A.valuation_le_one_iff ξ).mp (valuation_eq_one_of_pow_eq_one A hm0 hξ).le
  have hgm : (g ζ0) ^ m = 1 := by rw [← map_pow, hζ0.pow_eq_one, map_one]
  obtain ⟨a, -, ha⟩ := hζ0.eq_pow_of_pow_eq_one hgm
  let g' : A.decompositionSubgroup F := ⟨g, hg⟩
  have hlm : ((l : A)) ∈ IsLocalRing.maximalIdeal A := by
    rw [ValuationSubring.valuation_lt_one_iff]
    simpa using hA
  haveI : CharP (IsLocalRing.ResidueField A) l := by
    rw [CharP.charP_iff_prime_eq_zero hl, ← map_natCast (IsLocalRing.residue A),
      IsLocalRing.residue_eq_zero_iff]
    exact hlm
  letI : Algebra (ZMod l) (IsLocalRing.ResidueField A) := ZMod.algebra _ l
  let z0 : A := ⟨ζ0, hmemA ζ0 hζ0.pow_eq_one⟩
  let ω : IsLocalRing.ResidueField A := IsLocalRing.residue A z0
  have hσω : g' • ω = ω ^ a := by
    have hz : g' • z0 = z0 ^ a := Subtype.ext (by change g ζ0 = ζ0 ^ a; exact ha.symm)
    simp only [ω]
    rw [← IsLocalRing.ResidueField.residue_smul, hz, map_pow]
  let σ : IsLocalRing.ResidueField A →ₐ[ZMod l] IsLocalRing.ResidueField A :=
    { MulSemiringAction.toRingHom _ (IsLocalRing.ResidueField A) g' with
      commutes' := fun r => RingHom.congr_fun (RingHom.ext_zmod
        ((MulSemiringAction.toRingHom _ (IsLocalRing.ResidueField A) g').comp
          (algebraMap (ZMod l) (IsLocalRing.ResidueField A)))
        (algebraMap (ZMod l) (IsLocalRing.ResidueField A))) r }
  have hσ : ∀ x, σ x = g' • x := fun _ => rfl
  let E := IntermediateField.adjoin (ZMod l) ({ω} : Set (IsLocalRing.ResidueField A))
  have hωE : ω ∈ E := IntermediateField.mem_adjoin_simple_self _ _
  have hint : IsIntegral (ZMod l) ω := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hm0) ?_
    have h1 : ω ^ m = 1 := by
      simp only [ω]
      rw [← map_pow]
      have : z0 ^ m = 1 := Subtype.ext (by change ζ0 ^ m = 1; exact hζ0.pow_eq_one)
      rw [this, map_one]
    rw [h1]
    exact isIntegral_one
  haveI : FiniteDimensional (ZMod l) E := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite E := Module.finite_of_finite (ZMod l)
  have hEle : E ≤ IntermediateField.comap σ E := by
    rw [IntermediateField.adjoin_simple_le_iff]
    show σ ω ∈ E
    rw [hσ, hσω]
    exact pow_mem hωE a
  let τ : E →ₐ[ZMod l] E :=
    { toFun := fun x => ⟨σ x, hEle x.2⟩
      map_one' := Subtype.ext (map_one σ)
      map_mul' := fun x y => Subtype.ext (map_mul σ x.1 y.1)
      map_zero' := Subtype.ext (map_zero σ)
      map_add' := fun x y => Subtype.ext (map_add σ x.1 y.1)
      commutes' := fun r => Subtype.ext (σ.commutes r) }
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod l) E).2 τ
  have hτω : τ ⟨ω, hωE⟩ = ⟨ω, hωE⟩ ^ (l ^ (n : ℕ)) := by
    rw [← hn]
    simp only [AlgHom.coe_pow, FiniteField.coe_frobeniusAlgHom, pow_iterate, ZMod.card]
  have hres : ω ^ a = ω ^ (l ^ (n : ℕ)) := by
    have h2 : ((τ ⟨ω, hωE⟩ : E) : IsLocalRing.ResidueField A) = σ ω := rfl
    have := congrArg Subtype.val hτω
    rw [h2] at this
    rw [← hσω, ← hσ]
    simpa using this
  have hfin : g ζ0 = ζ0 ^ (l ^ (n : ℕ)) := by
    rw [← ha]
    have hroot : (ζ0 ^ (l ^ (n : ℕ))) ^ m = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ0.pow_eq_one, one_pow]
    have hroota : (ζ0 ^ a) ^ m = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ0.pow_eq_one, one_pow]
    refine (ineFixRoots F Ω l A hA m hm _ hroot).1 _ hroota ?_
    have hsub : (z0 ^ a - z0 ^ (l ^ (n : ℕ))) ∈ IsLocalRing.maximalIdeal A := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, map_pow, sub_eq_zero]
      exact hres
    rw [ValuationSubring.valuation_lt_one_iff] at hsub
    simpa using hsub
  refine ⟨n, fun ζ hζ => ?_⟩
  obtain ⟨j, -, rfl⟩ := hζ0.eq_pow_of_pow_eq_one hζ
  rw [map_pow, hfin, ← pow_mul, ← pow_mul, mul_comm]

section DecFrobAux

private theorem prime_l_rat (l : ℕ) [hl : Fact l.Prime] : Prime ((l : ℕ) : 𝓞 ℚ) := by
  rw [← MulEquiv.prime_iff Rat.ringOfIntegersEquiv, map_natCast]
  exact Nat.prime_iff_prime_int.mp hl.out

private def vQ (l : ℕ) [Fact l.Prime] : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {((l : ℕ) : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (prime_l_rat l).ne_zero).mpr (prime_l_rat l)
  ne_bot := by rw [Ne, Ideal.span_singleton_eq_bot]; exact (prime_l_rat l).ne_zero

private theorem normV_vQ (l : ℕ) [Fact l.Prime] : normV (vQ l) = l := by
  show Nat.card (𝓞 ℚ ⧸ Ideal.span {((l : ℕ) : 𝓞 ℚ)}) = l
  have hJ : Ideal.span {((l : ℕ) : ℤ)} =
      Ideal.map (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) (Ideal.span {((l : ℕ) : 𝓞 ℚ)}) := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [Nat.card_congr
    ((Ideal.quotientEquiv _ _ Rat.ringOfIntegersEquiv hJ).trans (Int.quotientSpanNatEquivZMod l)).toEquiv,
    Nat.card_zmod]

private theorem isPlaceOver_vQ {l : ℕ} [hl : Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    (A : ValuationSubring Ω) (hA : A.valuation ((l : ℕ) : Ω) < 1) :
    IsPlaceOver (F := ℚ) A (vQ l) := by
  have hint : ∀ n : ℤ, A.valuation (n : Ω) ≤ 1 := fun n =>
    (A.valuation_le_one_iff _).mpr (intCast_mem A n)
  have hlt : ∀ n : ℤ, A.valuation (n : Ω) < 1 ↔ ((l : ℕ) : ℤ) ∣ n := fun n => by
    constructor
    · intro h
      by_contra hn
      have hirr : Irreducible ((l : ℕ) : ℤ) := (Nat.prime_iff_prime_int.mp hl.out).irreducible
      obtain ⟨a, b, hab⟩ := hirr.coprime_iff_not_dvd.mpr hn
      have h1 : A.valuation (((a * ((l : ℕ) : ℤ) + b * n : ℤ)) : Ω) < 1 := by
        push_cast
        apply Valuation.map_add_lt
        · rw [Valuation.map_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint a)) (by exact_mod_cast hA)
        · rw [Valuation.map_mul]
          exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint b)) h
      rw [hab] at h1
      simp at h1
    · rintro ⟨k, rfl⟩
      push_cast
      rw [Valuation.map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint k)) (by exact_mod_cast hA)
  intro x
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, x = (n : 𝓞 ℚ) :=
    ⟨Rat.ringOfIntegersEquiv x, Rat.ringOfIntegersEquiv.injective (by simp)⟩
  have hmem : ((n : ℤ) : 𝓞 ℚ) ∈ (vQ l).asIdeal ↔ ((l : ℕ) : ℤ) ∣ n := by
    show _ ∈ Ideal.span _ ↔ _
    rw [Ideal.mem_span_singleton, ← map_dvd_iff Rat.ringOfIntegersEquiv]
    simp
  rw [hmem, ← hlt n]
  simp

end DecFrobAux

/-- **`DecFrob`**: Existence of a Frobenius lift `g ∈ Dec (F := ℚ) A` acting as `ζ ↦ ζ ^ l`
simultaneously on all prime-to-`l` roots of unity. -/
theorem decFrob (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) :
    ∃ g ∈ Dec (F := ℚ) A, ∀ m : ℕ, m.Coprime l → ∀ ζ : Ω, ζ ^ m = 1 → g ζ = ζ ^ l := by
  have hP : IsPlaceOver (F := ℚ) A (vQ l) := isPlaceOver_vQ A (by exact_mod_cast hA)
  obtain ⟨σ, hσD, hσ⟩ := exists_isFrob hP
  rw [normV_vQ] at hσ
  refine ⟨σ, hσD, fun m hm ζ hζ => ?_⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (Fact.out : l.Prime).one_lt.ne' (by simpa using hm)
  have hζv : A.valuation ζ ≤ 1 := (valuation_eq_one_of_pow_eq_one A hm0 hζ).le
  have key := (ineFixRoots ℚ Ω l A hA m hm (ζ ^ l)
    (by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow])).1
  exact key (σ ζ) (by rw [← map_pow, hζ, map_one]) (hσ ζ hζv)

section ClassIffFix

private theorem ci_pow {Ω : Type*} [Monoid Ω] {m M : ℕ} [NeZero m] [NeZero M] (hm : m ∣ M)
    (a : (ZMod M)ˣ) (ζ : Ω) (hζ : ζ ^ m = 1) :
    ζ ^ (a : ZMod M).val = ζ ^ ((ZMod.unitsMap hm a : (ZMod m)ˣ) : ZMod m).val := by
  rw [ZMod.unitsMap_val, ← ZMod.natCast_val, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ]

private theorem ci_hen (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (l : ℕ) [Fact l.Prime]
    (i : ℕ) : HasEnoughRootsOfUnity Ω (l ^ i) := by
  have : NeZero (l ^ i) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have : NeZero ((l ^ i : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne _)⟩
  infer_instance

private theorem ci_spec {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (l : ℕ) [Fact l.Prime]
    (n : ℕ) (g : Ω ≃+* Ω) (ζ : Ω) (hζ : ζ ^ l ^ n = 1) :
    g ζ = ζ ^ ((redPow l n (cyclotomicCharacter Ω l g) : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)).val := by
  have hen := ci_hen Ω l
  exact cyclotomicCharacter.spec l g ζ hζ

private theorem ci_red {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (l : ℕ) [Fact l.Prime]
    (n : ℕ) (g : Ω ≃+* Ω) (w : (ZMod (l ^ n))ˣ)
    (h : ∀ ζ : Ω, ζ ^ l ^ n = 1 → g ζ = ζ ^ (w : ZMod (l ^ n)).val) :
    w = redPow l n (cyclotomicCharacter Ω l g) := by
  have hen := ci_hen Ω l n
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have h1 := ci_spec l n g ζ hζ.pow_eq_one
  rw [h ζ hζ.pow_eq_one] at h1
  have hfin : IsOfFinOrder ζ :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨l ^ n, Nat.pos_of_neZero _, hζ.pow_eq_one⟩
  rw [hfin.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf, ← ZMod.natCast_eq_natCast_iff,
    ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h1
  exact Units.ext h1

private theorem ci_eq {Ω : Type} [Field Ω] {x y : Ω} (hy : y ≠ 0) {a b : ℕ} (hab : a.Coprime b)
    (ha : x ^ a = y ^ a) (hb : x ^ b = y ^ b) : x = y := by
  have h1 : (x / y) ^ a = 1 := by rw [div_pow, ha, div_self (pow_ne_zero _ hy)]
  have h2 : (x / y) ^ b = 1 := by rw [div_pow, hb, div_self (pow_ne_zero _ hy)]
  have h3 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
  rw [hab.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h3
  exact (div_eq_one_iff_eq hy).1 h3

/-- **`ClassIff`**: Action of `g : Ω ≃+* Ω` on `N`-th roots of unity decomposes into its action
on `ordCompl[l] N`-th roots and the mod-`l^{v_l(N)}` cyclotomic character. -/
theorem classIff (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosed Ω] (l : ℕ) [Fact l.Prime]
    (N : ℕ) [NeZero N] (g : Ω ≃+* Ω) (h : (ZMod N)ˣ) :
    (∀ ζ : Ω, ζ ^ N = 1 → g ζ = ζ ^ (h : ZMod N).val) ↔
      ((∀ ζ : Ω, ζ ^ ordCompl[l] N = 1 →
          g ζ = ζ ^ ((ZMod.unitsMap (Nat.ordCompl_dvd N l) h : (ZMod (ordCompl[l] N))ˣ) :
            ZMod (ordCompl[l] N)).val) ∧
        ZMod.unitsMap (Nat.ordProj_dvd N l) h =
          redPow l (N.factorization l) (cyclotomicCharacter Ω l g)) := by
  have hl : l.Prime := Fact.out
  have hN : N ≠ 0 := NeZero.ne N
  have : NeZero (l ^ N.factorization l) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have : NeZero (ordCompl[l] N) := ⟨(Nat.ordCompl_pos l hN).ne'⟩
  have hmul : ordProj[l] N * ordCompl[l] N = N := Nat.ordProj_mul_ordCompl_eq_self N l
  constructor
  · intro H
    refine ⟨fun ζ hζ => ?_, ci_red l _ g _ fun ζ hζ => ?_⟩
    · rw [← ci_pow _ h ζ hζ]
      exact H ζ (by rw [← hmul, mul_comm, pow_mul, hζ, one_pow])
    · rw [← ci_pow _ h ζ hζ]
      exact H ζ (by rw [← hmul, pow_mul, hζ, one_pow])
  · rintro ⟨H1, H2⟩ ζ hζ
    have hζ0 : ζ ≠ 0 := by
      rintro rfl
      rw [zero_pow hN] at hζ
      exact zero_ne_one hζ
    have hcop : (ordProj[l] N).Coprime (ordCompl[l] N) :=
      (Nat.coprime_ordCompl hl hN).pow_left _
    have e1 : (ζ ^ ordProj[l] N) ^ ordCompl[l] N = 1 := by rw [← pow_mul, hmul, hζ]
    have e2 : (ζ ^ ordCompl[l] N) ^ ordProj[l] N = 1 := by rw [← pow_mul, mul_comm, hmul, hζ]
    refine ci_eq (pow_ne_zero _ hζ0) hcop ?_ ?_
    · rw [← map_pow, H1 _ e1, ← ci_pow _ h _ e1, ← pow_mul, ← pow_mul, mul_comm]
    · rw [← map_pow, ci_spec l _ g _ e2, ← H2, ← ci_pow _ h _ e2, ← pow_mul, ← pow_mul, mul_comm]

/-- **`ClassFix`**: If `g : Ω ≃+* Ω` acts on `N`-th roots of unity via `h ∈ (ZMod N)ˣ`, then `g`
fixes `F` (embedded via `φ : F →ₐ[ℚ] K = ℚ(ζ_N)`) iff `h ∈ fieldSubgroup N K φ.fieldRange`. -/
theorem classFix (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (N : ℕ) [NeZero N] (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {N} ℚ K]
    (φ : F →ₐ[ℚ] K) (g : Ω ≃+* Ω) (h : (ZMod N)ˣ)
    (hg : ∀ ζ : Ω, ζ ^ N = 1 → g ζ = ζ ^ (h : ZMod N).val) :
    (∀ x : F, g (algebraMap F Ω x) = algebraMap F Ω x) ↔
      h ∈ fieldSubgroup N K φ.fieldRange := by
  haveI : CharZero Ω := (RingHom.charZero_iff (algebraMap F Ω).injective).mp inferInstance
  letI : Algebra F K := φ.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ F K := inferInstance
  haveI : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  let ι : K →ₐ[F] Ω := IsAlgClosed.lift
  have hι : ∀ x : F, ι (φ x) = algebraMap F Ω x := fun x => ι.commutes x
  set σ : K ≃ₐ[ℚ] K := (IsCyclotomicExtension.Rat.galEquivZMod N K).symm h with hσ
  have hσζ : ∀ y : K, y ^ N = 1 → σ y = y ^ (h : ZMod N).val := by
    intro y hy
    have := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N K σ hy
    rw [this, hσ, MulEquiv.apply_symm_apply]
  have hcomm : ∀ y : K, g (ι y) = ι (σ y) := by
    have key : (g.toRingHom.toRatAlgHom).comp (ι.toRingHom.toRatAlgHom) =
        (ι.toRingHom.toRatAlgHom).comp σ.toAlgHom := by
      refine AlgHom.ext_of_adjoin_eq_top (s := {b : K | ∃ n ∈ ({N} : Set ℕ), n ≠ 0 ∧ b ^ n = 1})
        (Algebra.eq_top_iff.mpr IsCyclotomicExtension.adjoin_roots) ?_
      rintro b ⟨n, hn, -, hb⟩
      rw [Set.mem_singleton_iff] at hn
      subst hn
      simp only [AlgHom.coe_comp, Function.comp_apply, RingHom.toRatAlgHom_apply,
        AlgEquiv.coe_toAlgHom]
      rw [hσζ b hb, map_pow]
      apply hg
      rw [← map_pow, hb, map_one]
    intro y
    exact congrArg (fun f => f y) key
  unfold fieldSubgroup
  rw [Subgroup.mem_map_equiv, ← hσ, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro H y hy
    obtain ⟨x, rfl⟩ := AlgHom.mem_fieldRange.mp hy
    apply ι.toRingHom.injective
    change ι (σ (φ x)) = ι (φ x)
    rw [← hcomm, hι, H]
  · intro H x
    rw [← hι, hcomm, H _ (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩)]

end ClassIffFix

end RootsAndCyclotomicSplitting

/-! ## Section 3: Cyclotomic Inertia Surjectivity, `IneOpen`, `exists_mem_Dec_cycZ_zpow_ne_one` & `LevelLeIne` -/

section CyclotomicInertiaAndLevels

section CycInertialHelpers

variable {K : Type} [Field K] {Γ : Type} [LinearOrderedCommGroupWithZero Γ]

private theorem cyc_val_le_one (w : Valuation K Γ) {z : K} {n : ℕ} (hn : n ≠ 0) (hz : z ^ n = 1)
    (r : Algebra.adjoin ℤ ({z} : Set K)) : w (r : K) ≤ 1 := by
  have hz1 : w z ≤ 1 := by
    by_contra h
    push Not at h
    have h2 : w z ^ n = 1 := by rw [← map_pow, hz, map_one]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [pow_succ] at h2
    have h3 := mul_le_mul' (one_le_pow₀ h.le : 1 ≤ w z ^ m) (le_refl (w z))
    rw [one_mul, h2] at h3
    exact absurd h (not_lt.mpr h3)
  obtain ⟨r, hr⟩ := r
  show w r ≤ 1
  induction hr using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.mp hx]; exact hz1
  | algebraMap m =>
    rw [algebraMap_int_eq, eq_intCast]
    exact (Valuation.mem_integer_iff w _).mp (intCast_mem _ m)
  | add x y _ _ ihx ihy => exact (w.map_add x y).trans (max_le ihx ihy)
  | mul x y _ _ ihx ihy => rw [map_mul]; exact mul_le_one' ihx ihy

private def cycGen (z : K) : Algebra.adjoin ℤ ({z} : Set K) := ⟨z, Algebra.subset_adjoin rfl⟩

private theorem cyc_exists_int (z : K) (r : Algebra.adjoin ℤ ({z} : Set K)) :
    ∃ (m : ℤ) (s : Algebra.adjoin ℤ ({z} : Set K)), r = m + (cycGen z - 1) * s := by
  obtain ⟨r, hr⟩ := r
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact ⟨1, 1, Subtype.ext (by simp [cycGen])⟩
  | algebraMap m => exact ⟨m, 0, Subtype.ext (by simp)⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨m₁, s₁, h₁⟩ := ihx
    obtain ⟨m₂, s₂, h₂⟩ := ihy
    refine ⟨m₁ + m₂, s₁ + s₂, Subtype.ext ?_⟩
    have e₁ := congrArg Subtype.val h₁
    have e₂ := congrArg Subtype.val h₂
    push_cast [cycGen, Subtype.coe_mk] at e₁ e₂ ⊢
    rw [e₁, e₂]; ring
  | mul x y _ _ ihx ihy =>
    obtain ⟨m₁, s₁, h₁⟩ := ihx
    obtain ⟨m₂, s₂, h₂⟩ := ihy
    refine ⟨m₁ * m₂, (m₁ : Algebra.adjoin ℤ ({z} : Set K)) * s₂ + s₁ * m₂ + (cycGen z - 1) * s₁ * s₂,
      Subtype.ext ?_⟩
    have e₁ := congrArg Subtype.val h₁
    have e₂ := congrArg Subtype.val h₂
    push_cast [cycGen, Subtype.coe_mk] at e₁ e₂ ⊢
    rw [e₁, e₂]; ring

private theorem cyc_val_sub_one_lt (w : Valuation K Γ) {l k : ℕ} (hl : l.Prime) (hw : w (l : K) < 1)
    {z : K} (hz : z ^ (l ^ k) = 1) : w (z - 1) < 1 := by
  have hn : l ^ k ≠ 0 := pow_ne_zero _ hl.ne_zero
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hl (cycGen z - 1) 1 k
  have e := congrArg Subtype.val hr
  push_cast [cycGen] at e
  have key : (z - 1) ^ (l ^ k) = -((l : K) * (z - 1) * (r : K)) := by linear_combination -e + hz
  have h₁ : w (z - 1) ≤ 1 := by simpa [cycGen] using cyc_val_le_one w hn hz (cycGen z - 1)
  have h₂ : w (r : K) ≤ 1 := cyc_val_le_one w hn hz r
  have h₃ : w (z - 1) ^ (l ^ k) < 1 := by
    rw [← map_pow, key, Valuation.map_neg, map_mul, map_mul]
    calc w (l : K) * w (z - 1) * w (r : K) ≤ w (l : K) * 1 * 1 :=
          mul_le_mul' (mul_le_mul' le_rfl h₁) h₂
      _ < 1 := by simpa using hw
  by_contra h
  push Not at h
  exact absurd h₃ (not_lt.mpr (one_le_pow₀ h))

private theorem cyc_sub_one_dvd [CharZero K] {l k : ℕ} [Fact l.Prime] {z : K}
    (hz : IsPrimitiveRoot z (l ^ (k + 1))) :
    cycGen z - 1 ∣ (l : Algebra.adjoin ℤ ({z} : Set K)) := by
  have hl : l.Prime := Fact.out
  have hζ : IsPrimitiveRoot (z ^ l ^ k) l := by
    have := hz.pow_of_dvd (pow_ne_zero k hl.ne_zero) (pow_dvd_pow l k.le_succ)
    rwa [pow_succ, Nat.mul_div_cancel_left _ (pow_pos hl.pos k)] at this
  have hsum := hζ.geom_sum_eq_zero hl.one_lt
  have key : (l : Algebra.adjoin ℤ ({z} : Set K)) =
      ∑ i ∈ Finset.range l, (1 - (cycGen z ^ l ^ k) ^ i) := by
    apply Subtype.ext
    push_cast [cycGen]
    rw [Finset.sum_sub_distrib, hsum]
    simp
  rw [key]
  refine Finset.dvd_sum fun i _ => ?_
  rw [← neg_sub ((cycGen z ^ l ^ k) ^ i) 1, dvd_neg, ← pow_mul]
  exact sub_one_dvd_pow_sub_one _ _

private theorem cyc_val_eq_one [CharZero K] (w : Valuation K Γ) {l k : ℕ} [Fact l.Prime]
    (hw : w (l : K) < 1) {z : K} (hz : IsPrimitiveRoot z (l ^ (k + 1)))
    (u : Algebra.adjoin ℤ ({z} : Set K)) (hu : ¬ cycGen z - 1 ∣ u) : w (u : K) = 1 := by
  have hl : l.Prime := Fact.out
  have hn : l ^ (k + 1) ≠ 0 := pow_ne_zero _ hl.ne_zero
  obtain ⟨m, s, rfl⟩ := cyc_exists_int z u
  have hm : ¬ (l : ℤ) ∣ m := by
    rintro ⟨c, rfl⟩
    apply hu
    obtain ⟨t, ht⟩ := cyc_sub_one_dvd hz
    exact ⟨t * c + s, by push_cast; rw [ht]; ring⟩
  have hint : ∀ a : ℤ, w (a : K) ≤ 1 := fun a => by
    simpa using cyc_val_le_one w hn hz.pow_eq_one (a : Algebra.adjoin ℤ ({z} : Set K))
  have hwm : w (m : K) = 1 := by
    refine le_antisymm (hint m) ?_
    by_contra h
    push Not at h
    obtain ⟨a, b, hab⟩ :=
      (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hl).irreducible).mpr hm
    have e : ((a * l + b * m : ℤ) : K) = 1 := by rw [hab]; simp
    push_cast at e
    have h₀ := w.map_add ((a : K) * l) ((b : K) * m)
    rw [e, map_one, map_mul, map_mul] at h₀
    have h₁ : w (a : K) * w (l : K) < 1 :=
      lt_of_le_of_lt (by simpa using mul_le_mul' (hint a) (le_refl (w (l : K)))) hw
    have h₂ : w (b : K) * w (m : K) < 1 :=
      lt_of_le_of_lt (by simpa using mul_le_mul' (hint b) (le_refl (w (m : K)))) h
    exact absurd h₀ (not_le.mpr (max_lt h₁ h₂))
  have hzs : w ((z - 1) * s) < 1 := by
    rw [map_mul]
    calc w (z - 1) * w (s : K) ≤ w (z - 1) * 1 :=
          mul_le_mul' le_rfl (cyc_val_le_one w hn hz.pow_eq_one s)
      _ < 1 := by rw [mul_one]; exact cyc_val_sub_one_lt w hl hw hz.pow_eq_one
  push_cast [cycGen]
  rw [Valuation.map_add_eq_of_lt_left _ (by rw [hwm]; exact hzs), hwm]

private theorem cyc_exists_shape [CharZero K] (w : Valuation K Γ) {l k : ℕ} [Fact l.Prime]
    (hw : w (l : K) < 1) {z : K} (hz : IsPrimitiveRoot z (l ^ (k + 1)))
    (r s : Algebra.adjoin ℤ ({z} : Set K)) (hs : s ≠ 0) :
    (∃ r' u : Algebra.adjoin ℤ ({z} : Set K), ¬ cycGen z - 1 ∣ u ∧ (r : K) / s = r' / u) ∨
    (∃ u s' : Algebra.adjoin ℤ ({z} : Set K), ¬ cycGen z - 1 ∣ u ∧ s' ≠ 0 ∧
      (r : K) / s = u / ((z - 1) * s')) := by
  have hl : l.Prime := Fact.out
  have hn : l ^ (k + 1) ≠ 0 := pow_ne_zero _ hl.ne_zero
  have : IsNoetherianRing (Algebra.adjoin ℤ ({z} : Set K)) :=
    isNoetherianRing_of_fg ⟨{z}, by simp⟩
  have hz0 : z - 1 ≠ 0 := fun h =>
    hz.ne_one (Nat.one_lt_pow (Nat.succ_ne_zero k) hl.one_lt) (sub_eq_zero.mp h)
  have hnz : cycGen z - 1 ≠ 0 := fun h => hz0 (by simpa [cycGen] using congrArg Subtype.val h)
  have hnu : ¬ IsUnit (cycGen z - 1) := by
    intro h
    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp h
    have e := congrArg (fun t : Algebra.adjoin ℤ ({z} : Set K) => w (t : K)) hy
    push_cast [cycGen] at e
    rw [map_mul, map_one] at e
    have h₁ : w (z - 1) * w (y : K) < 1 :=
      (mul_le_mul' (le_refl (w (z - 1))) (cyc_val_le_one w hn hz.pow_eq_one y)).trans_lt
        (by rw [mul_one]; exact cyc_val_sub_one_lt w hl hw hz.pow_eq_one)
    exact absurd e h₁.ne
  obtain ⟨b, s₀, hs₀, hseq⟩ := WfDvdMonoid.max_power_factor' hs hnu
  have hs₀' : s₀ ≠ 0 := by rintro rfl; exact hs₀ (dvd_zero _)
  have hs₀K : (s₀ : K) ≠ 0 := by exact_mod_cast hs₀'
  by_cases hr : r = 0
  · left
    exact ⟨0, 1, fun h => hnu (isUnit_iff_dvd_one.mpr h), by subst hr; simp⟩
  obtain ⟨a, r₀, hr₀, hreq⟩ := WfDvdMonoid.max_power_factor' hr hnu
  rcases le_or_gt b a with hab | hab
  · left
    obtain ⟨c, rfl⟩ : ∃ c, a = b + c := ⟨a - b, by omega⟩
    refine ⟨(cycGen z - 1) ^ c * r₀, s₀, hs₀, ?_⟩
    rw [hreq, hseq]
    push_cast [cycGen]
    rw [div_eq_div_iff (mul_ne_zero (pow_ne_zero _ hz0) hs₀K) hs₀K]
    ring
  · right
    obtain ⟨c, rfl⟩ : ∃ c, b = a + c + 1 := ⟨b - a - 1, by omega⟩
    refine ⟨r₀, (cycGen z - 1) ^ c * s₀, hr₀, mul_ne_zero (pow_ne_zero _ hnz) hs₀', ?_⟩
    rw [hreq, hseq]
    push_cast [cycGen]
    rw [div_eq_div_iff (mul_ne_zero (pow_ne_zero _ hz0) hs₀K)
      (mul_ne_zero hz0 (mul_ne_zero (pow_ne_zero _ hz0) hs₀K))]
    ring

private theorem cyc_not_le_one [CharZero K] (w : Valuation K Γ) {l k : ℕ} [Fact l.Prime]
    (hw : w (l : K) < 1) {z : K} (hz : IsPrimitiveRoot z (l ^ (k + 1)))
    (u s : Algebra.adjoin ℤ ({z} : Set K)) (hu : ¬ cycGen z - 1 ∣ u) (hs : s ≠ 0) :
    ¬ w ((u : K) / ((z - 1) * s)) ≤ 1 := by
  intro h
  have hl : l.Prime := Fact.out
  have hn : l ^ (k + 1) ≠ 0 := pow_ne_zero _ hl.ne_zero
  have hz0 : z - 1 ≠ 0 := fun h =>
    hz.ne_one (Nat.one_lt_pow (Nat.succ_ne_zero k) hl.one_lt) (sub_eq_zero.mp h)
  have hsK : (s : K) ≠ 0 := by exact_mod_cast hs
  have hd0 : (z - 1) * (s : K) ≠ 0 := mul_ne_zero hz0 hsK
  have hd : w ((z - 1) * s) < 1 := by
    rw [map_mul]
    calc w (z - 1) * w (s : K) ≤ w (z - 1) * 1 :=
          mul_le_mul' le_rfl (cyc_val_le_one w hn hz.pow_eq_one s)
      _ < 1 := by rw [mul_one]; exact cyc_val_sub_one_lt w hl hw hz.pow_eq_one
  have e := congrArg w (div_mul_cancel₀ (u : K) hd0).symm
  rw [map_mul, cyc_val_eq_one w hw hz u hu] at e
  have h₁ : w ((u : K) / ((z - 1) * s)) * w ((z - 1) * s) < 1 :=
    lt_of_le_of_lt (by simpa using mul_le_mul' h (le_refl (w ((z - 1) * s)))) hd
  exact absurd e (ne_of_gt h₁)

private theorem cyc_ringHom_adjoin_eq_add {z : K} {n : ℕ} [NeZero n] (hz : IsPrimitiveRoot z n)
    (τ : K →+* K) (r : Algebra.adjoin ℤ ({z} : Set K)) :
    ∃ t : Algebra.adjoin ℤ ({z} : Set K), τ r = r + (z - 1) * t := by
  obtain ⟨i, -, hi⟩ := hz.eq_pow_of_pow_eq_one (ξ := τ z) (by rw [← map_pow, hz.pow_eq_one, map_one])
  obtain ⟨c, hc⟩ := sub_one_dvd_pow_sub_one (cycGen z) i
  have ec := congrArg Subtype.val hc
  push_cast [cycGen] at ec
  obtain ⟨r, hr⟩ := r
  show ∃ t : Algebra.adjoin ℤ ({z} : Set K), τ r = r + (z - 1) * t
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.mp hx]
    refine ⟨c - 1, ?_⟩
    push_cast
    rw [← hi]
    linear_combination ec
  | algebraMap m => exact ⟨0, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨t₁, h₁⟩ := ihx
    obtain ⟨t₂, h₂⟩ := ihy
    exact ⟨t₁ + t₂, by push_cast; rw [map_add, h₁, h₂]; ring⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨t₁, h₁⟩ := ihx
    obtain ⟨t₂, h₂⟩ := ihy
    refine ⟨t₁ * ⟨y, hy⟩ + ⟨x, hx⟩ * t₂ + (cycGen z - 1) * t₁ * t₂, ?_⟩
    push_cast [cycGen, Subtype.coe_mk]
    rw [map_mul, h₁, h₂]
    ring

private theorem cyc_core [CharZero K] (w : Valuation K Γ) {l k : ℕ} [Fact l.Prime]
    (hw : w (l : K) < 1) {z : K} (hz : IsPrimitiveRoot z (l ^ (k + 1)))
    (hfrac : ∀ x : K, ∃ r s : Algebra.adjoin ℤ ({z} : Set K), s ≠ 0 ∧ x = r / s) (τ : K →+* K) :
    (∀ x, w x ≤ 1 → w (τ x - x) < 1) ∧ (∀ x, w (τ x) ≤ 1 ↔ w x ≤ 1) := by
  have hl : l.Prime := Fact.out
  have hn : l ^ (k + 1) ≠ 0 := pow_ne_zero _ hl.ne_zero
  have : NeZero (l ^ (k + 1)) := ⟨hn⟩
  have small : ∀ t : Algebra.adjoin ℤ ({z} : Set K), w ((z - 1) * t) < 1 := fun t => by
    rw [map_mul]
    exact (mul_le_mul' le_rfl (cyc_val_le_one w hn hz.pow_eq_one t)).trans_lt
      (by rw [mul_one]; exact cyc_val_sub_one_lt w hl hw hz.pow_eq_one)
  have part1 : ∀ x, w x ≤ 1 → w (τ x - x) < 1 := by
    intro x hx
    obtain ⟨r, s, hs, rfl⟩ := hfrac x
    rcases cyc_exists_shape w hw hz r s hs with ⟨r', u, hu, he⟩ | ⟨u, s', hu, hs', he⟩
    · rw [he] at hx ⊢
      have hu1 := cyc_val_eq_one w hw hz u hu
      have hu0 : (u : K) ≠ 0 := fun h => by simp [h] at hu1
      obtain ⟨t₁, h₁⟩ := cyc_ringHom_adjoin_eq_add hz τ r'
      obtain ⟨t₂, h₂⟩ := cyc_ringHom_adjoin_eq_add hz τ u
      have hτu : w (τ u) = 1 := by
        rw [h₂, Valuation.map_add_eq_of_lt_left _ (by rw [hu1]; exact small t₂), hu1]
      have hτu0 : τ (u : K) ≠ 0 := fun h => by simp [h] at hτu
      have e : τ ((r' : K) / u) - r' / u =
          (z - 1) * ((t₁ * u - r' * t₂ : Algebra.adjoin ℤ ({z} : Set K)) : K) / (τ u * u) := by
        rw [map_div₀, div_sub_div _ _ hτu0 hu0]
        push_cast
        rw [h₁, h₂]
        ring
      rw [e, map_div₀, Valuation.map_mul w (τ _) _, hτu, hu1, mul_one, div_one]
      exact small _
    · exfalso
      rw [he] at hx
      exact cyc_not_le_one w hw hz u s' hu hs' hx
  refine ⟨part1, fun x => ⟨fun h => ?_, fun h => ?_⟩⟩
  · by_contra hx
    push Not at hx
    have hx0 : x ≠ 0 := by rintro rfl; simp at hx
    have hinv : (w x)⁻¹ < 1 := by
      have hx' : w x ≠ 0 := by rw [Valuation.ne_zero_iff]; exact hx0
      by_contra h'
      push Not at h'
      have h₁ := mul_le_mul' (le_refl (w x)) h'
      rw [mul_one, mul_inv_cancel₀ hx'] at h₁
      exact absurd hx (not_lt.mpr h₁)
    have hy : w x⁻¹ < 1 := by rwa [map_inv₀]
    have hτy : w (τ x⁻¹) < 1 := by
      rw [show τ x⁻¹ = (τ x⁻¹ - x⁻¹) + x⁻¹ by ring]
      exact (w.map_add _ _).trans_lt (max_lt (part1 _ hy.le) hy)
    rw [map_inv₀, map_inv₀] at hτy
    have hτx0 : w (τ x) ≠ 0 := by rw [Valuation.ne_zero_iff, _root_.map_ne_zero]; exact hx0
    have h₁ := mul_le_mul' h (le_refl (w (τ x))⁻¹)
    rw [mul_inv_cancel₀ hτx0, one_mul] at h₁
    exact absurd hτy (not_lt.mpr h₁)
  · rw [show τ x = (τ x - x) + x by ring]
    exact (w.map_add _ _).trans (max_le (part1 x h).le h)

private theorem cyc_frac (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ζ : Ω)
    (x : IntermediateField.adjoin ℚ {ζ}) :
    ∃ r s : Algebra.adjoin ℤ ({IntermediateField.AdjoinSimple.gen ℚ ζ} :
      Set (IntermediateField.adjoin ℚ {ζ})), s ≠ 0 ∧ x = r / s := by
  have : CharZero Ω := algebraRat.charZero (R := Ω)
  have hcoe : ∀ P : Polynomial ℤ,
      ((Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ ζ) P :
        IntermediateField.adjoin ℚ {ζ}) : Ω) = Polynomial.aeval ζ P := fun P => by
    have h := Polynomial.aeval_algHom_apply
      (algebraMap (IntermediateField.adjoin ℚ {ζ}) Ω).toIntAlgHom
      (IntermediateField.AdjoinSimple.gen ℚ ζ) P
    simpa using h.symm
  obtain ⟨p, q, hpq⟩ := (IntermediateField.mem_adjoin_simple_iff (F := ℚ) (x : Ω)).mp x.2
  obtain ⟨bp, hbp, hP⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) p
  obtain ⟨bq, hbq, hQ⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) q
  have hbp0 : (bp : Ω) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hbp
  have hbq0 : (bq : Ω) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hbq
  have eP : Polynomial.aeval ζ (IsLocalization.integerNormalization (nonZeroDivisors ℤ) p) =
      bp * Polynomial.aeval ζ p := by
    rw [← Polynomial.aeval_map_algebraMap (A := ℚ), hP]; simp [zsmul_eq_mul]
  have eQ : Polynomial.aeval ζ (IsLocalization.integerNormalization (nonZeroDivisors ℤ) q) =
      bq * Polynomial.aeval ζ q := by
    rw [← Polynomial.aeval_map_algebraMap (A := ℚ), hQ]; simp [zsmul_eq_mul]
  by_cases hB : Polynomial.aeval ζ q = 0
  · exact ⟨0, 1, one_ne_zero, Subtype.ext (by simp [hpq, hB])⟩
  refine ⟨(bq : Algebra.adjoin ℤ ({IntermediateField.AdjoinSimple.gen ℚ ζ} :
      Set (IntermediateField.adjoin ℚ {ζ}))) *
      ⟨Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ ζ)
        (IsLocalization.integerNormalization (nonZeroDivisors ℤ) p),
        Polynomial.aeval_mem_adjoin_singleton ℤ _⟩,
    (bp : Algebra.adjoin ℤ ({IntermediateField.AdjoinSimple.gen ℚ ζ} :
      Set (IntermediateField.adjoin ℚ {ζ}))) *
      ⟨Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ ζ)
        (IsLocalization.integerNormalization (nonZeroDivisors ℤ) q),
        Polynomial.aeval_mem_adjoin_singleton ℤ _⟩, ?_, ?_⟩
  · intro h
    have h' := congrArg (fun t : Algebra.adjoin ℤ ({IntermediateField.AdjoinSimple.gen ℚ ζ} :
      Set (IntermediateField.adjoin ℚ {ζ})) => ((t : IntermediateField.adjoin ℚ {ζ}) : Ω)) h
    push_cast [Subtype.coe_mk, hcoe] at h'
    rw [eQ] at h'
    exact mul_ne_zero hbp0 (mul_ne_zero hbq0 hB) h'
  · apply Subtype.ext
    push_cast [Subtype.coe_mk, hcoe]
    rw [eP, eQ, hpq]
    field_simp

/-- Every `ℚ`-automorphism of `ℚ(ζ_{l^k})` is inertial at any place `A` above `l`. -/
theorem cyclotomicPrimePow_automorphism_inertial_at_prime (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    (l k : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) (ζ : Ω)
    (hζ : IsPrimitiveRoot ζ (l ^ k))
    (τ : (IntermediateField.adjoin ℚ {ζ}) ≃ₐ[ℚ] (IntermediateField.adjoin ℚ {ζ})) :
    (∀ x : IntermediateField.adjoin ℚ {ζ}, A.valuation (x : Ω) ≤ 1 →
      A.valuation ((τ x : Ω) - (x : Ω)) < 1) ∧
    (∀ x : IntermediateField.adjoin ℚ {ζ},
      A.valuation ((τ x : IntermediateField.adjoin ℚ {ζ}) : Ω) ≤ 1 ↔ A.valuation (x : Ω) ≤ 1) := by
  rcases k with _ | k
  · rw [pow_zero, IsPrimitiveRoot.one_right_iff] at hζ
    subst hζ
    have hτ : ∀ x : IntermediateField.adjoin ℚ {(1 : Ω)}, τ x = x := fun x => by
      have hx : (x : Ω) ∈ (⊥ : IntermediateField ℚ Ω) := by
        rw [← IntermediateField.adjoin_simple_eq_bot_iff.mpr (one_mem _)]
        exact x.2
      obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hx
      have e : x = algebraMap ℚ _ q := Subtype.ext (by simpa using hq.symm)
      rw [e, AlgEquiv.commutes]
    exact ⟨fun x _ => by simp [hτ x], fun x => by simp [hτ x]⟩
  · have : CharZero (IntermediateField.adjoin ℚ {ζ}) :=
      algebraRat.charZero (R := IntermediateField.adjoin ℚ {ζ})
    have hg : IsPrimitiveRoot (IntermediateField.AdjoinSimple.gen ℚ ζ) (l ^ (k + 1)) :=
      IsPrimitiveRoot.of_map_of_injective (f := algebraMap (IntermediateField.adjoin ℚ {ζ}) Ω)
        (by simpa using hζ) (algebraMap (IntermediateField.adjoin ℚ {ζ}) Ω).injective
    have hw : (A.valuation.comap (algebraMap (IntermediateField.adjoin ℚ {ζ}) Ω))
        (l : IntermediateField.adjoin ℚ {ζ}) < 1 := by
      simpa [Valuation.comap_apply] using hA
    obtain ⟨h₁, h₂⟩ := cyc_core (A.valuation.comap (algebraMap (IntermediateField.adjoin ℚ {ζ}) Ω))
      hw hg (cyc_frac Ω ζ) τ.toRingHom
    refine ⟨fun x hx => ?_, fun x => ?_⟩
    · simpa [Valuation.comap_apply] using h₁ x (by simpa [Valuation.comap_apply] using hx)
    · simpa [Valuation.comap_apply] using h₂ x

end CycInertialHelpers

section InertiaLiftHelpers

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

private theorem mem_Ine_of_integral {A : ValuationSubring Ω} {σ : G F Ω} (hσ : σ ∈ Dec (F := F) A)
    (h : ∀ b : Ω, IsIntegral ℤ b → A.valuation (σ b - b) < 1) : σ ∈ Ine (F := F) A := by
  refine ⟨hσ, fun x hx => ?_⟩
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den F A hx
  have hσs : A.valuation (σ s) = 1 := by
    refine le_antisymm ((A.valuation_le_one_iff _).mpr ((apply_mem_iff_of_mem_Dec hσ s).mpr
      (mem_of_isIntegral_int A hs))) ?_
    rw [← not_lt, valuation_apply_lt_one_iff hσ, hs1]
    exact lt_irrefl 1
  have he' : σ s * σ x = σ t := by rw [← map_mul, e]
  have key : σ s * (σ x - x) = (σ t - t) + x * (s - σ s) := by rw [← he', ← e]; ring
  have hv : A.valuation (σ s * (σ x - x)) < 1 := by
    rw [key]
    refine Valuation.map_add_lt _ (h t ht) ?_
    rw [Valuation.map_mul, Valuation.map_sub_swap]
    calc A.valuation x * A.valuation (σ s - s) ≤ 1 * A.valuation (σ s - s) := mul_le_mul_left hx _
      _ < 1 := by rw [one_mul]; exact h s hs
  rwa [Valuation.map_mul, hσs, one_mul] at hv

private theorem exists_smul_eq_val {A A' : ValuationSubring Ω}
    (h : ∀ x : 𝓞 F, A.valuation (algebraMap F Ω x) < 1 ↔ A'.valuation (algebraMap F Ω x) < 1) :
    ∃ g : Ω ≃ₐ[F] Ω, ∀ y, A'.valuation (g y) < 1 ↔ A.valuation y < 1 := by
  letI : TopologicalSpace (IntCl F Ω) := ⊥
  haveI : DiscreteTopology (IntCl F Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl F Ω
  haveI := isInvariant_intCl F Ω
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := 𝓞 F)
    (G := Ω ≃ₐ[F] Ω) (primeBelow (F := F) A) (primeBelow (F := F) A')
    (by
      ext x
      rw [Ideal.under, Ideal.under, Ideal.mem_comap, Ideal.mem_comap, mem_primeBelow, mem_primeBelow]
      exact h x)
  have e : g • A = A' := by
    refine eq_of_valuation_lt_one_iff F fun b hb => ?_
    let b' : IntCl F Ω := ⟨b, hb.tower_top⟩
    change b' ∈ primeBelow (F := F) (g • A) ↔ b' ∈ primeBelow (F := F) A'
    rw [primeBelow_smul, hg]
  refine ⟨g, fun y => ?_⟩
  rw [← e, smul_valuation_lt_one_iff]
  have : (g⁻¹ : Ω ≃ₐ[F] Ω) (g y) = y := g.symm_apply_apply y
  rw [this]

private def intEquiv (s : Ω ≃+* Ω) : IntCl F Ω ≃+* IntCl F Ω where
  toFun b := ⟨s b, IsIntegral.tower_top (R := ℤ)
    ((isIntegral_trans (b : Ω) b.2).map s.toRingHom.toIntAlgHom)⟩
  invFun b := ⟨s.symm b, IsIntegral.tower_top (R := ℤ)
    ((isIntegral_trans (b : Ω) b.2).map s.symm.toRingHom.toIntAlgHom)⟩
  left_inv b := Subtype.ext (s.symm_apply_apply b)
  right_inv b := Subtype.ext (s.apply_symm_apply b)
  map_mul' a b := Subtype.ext (map_mul s (a : Ω) b)
  map_add' a b := Subtype.ext (map_add s (a : Ω) b)

private theorem exists_congr_inertia {A : ValuationSubring Ω} (s : Ω ≃+* Ω)
    (hs : ∀ y, A.valuation (s y) < 1 ↔ A.valuation y < 1)
    (h : ∀ x : 𝓞 F, A.valuation (s (algebraMap F Ω x) - algebraMap F Ω x) < 1) :
    ∃ g : Ω ≃ₐ[F] Ω, g ∈ Dec (F := F) A ∧
      ∀ b : Ω, IsIntegral ℤ b → A.valuation (g b - s b) < 1 := by
  letI : TopologicalSpace (IntCl F Ω) := ⊥
  haveI : DiscreteTopology (IntCl F Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl F Ω
  haveI := isInvariant_intCl F Ω
  set Q := primeBelow (F := F) A with hQ
  have hmap : Q = Q.map (intEquiv (F := F) s : IntCl F Ω →+* IntCl F Ω) := by
    rw [Ideal.map_comap_of_equiv]
    ext b
    rw [Ideal.mem_comap, mem_primeBelow, mem_primeBelow, ← hs ((intEquiv (F := F) s).symm b)]
    have : s (((intEquiv (F := F) s).symm b : IntCl F Ω) : Ω) = b := s.apply_symm_apply b
    rw [this]
  let φ : (IntCl F Ω ⧸ Q) ≃ₐ[𝓞 F ⧸ Q.under (𝓞 F)] (IntCl F Ω ⧸ Q) :=
    AlgEquiv.ofRingEquiv (f := Ideal.quotientEquiv Q Q (intEquiv (F := F) s) hmap) (by
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      change Ideal.Quotient.mk Q (intEquiv (F := F) s (algebraMap _ _ x)) =
        Ideal.Quotient.mk Q (algebraMap _ _ x)
      rw [Ideal.Quotient.eq]
      exact h x)
  obtain ⟨⟨σ, hσQ⟩, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := Ω ≃ₐ[F] Ω) (Q.under (𝓞 F)) Q φ
  have hσQ' : σ • Q = Q := hσQ
  refine ⟨σ, ?_, fun b hb => ?_⟩
  · refine eq_of_valuation_lt_one_iff F fun b hb => ?_
    let b' : IntCl F Ω := ⟨b, hb.tower_top⟩
    change b' ∈ primeBelow (F := F) (σ • A) ↔ b' ∈ Q
    rw [primeBelow_smul, hσQ']
  · let b' : IntCl F Ω := ⟨b, hb.tower_top⟩
    have h1 : Ideal.Quotient.mk Q (σ • b') = Ideal.Quotient.mk Q (intEquiv (F := F) s b') :=
      DFunLike.congr_fun hσ (Ideal.Quotient.mk Q b')
    rw [Ideal.Quotient.eq] at h1
    exact h1

omit [IsAlgClosure F Ω] in
private theorem mem_Dec_of_lt {A : ValuationSubring Ω} {σ : G F Ω}
    (h : ∀ y, A.valuation (σ y) < 1 ↔ A.valuation y < 1) : σ ∈ Dec (F := F) A := by
  have key : ∀ y, y ∈ A ↔ (y = 0 ∨ ¬ A.valuation y⁻¹ < 1) := fun y => by
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    · have h0 : 0 < A.valuation y := zero_lt_iff.mpr (by simpa using hy)
      rw [← A.valuation_le_one_iff, map_inv₀, inv_lt_one₀ h0, not_lt]
      simp [hy]
  show σ • A = A
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, key, key y,
    ← h, map_inv₀ σ, mul_inv_apply, map_eq_zero_iff _ (σ⁻¹ : G F Ω).injective]

theorem exists_mem_Ine_lift (A : ValuationSubring Ω) (M : Type*) [Field M] [Algebra F M]
    [Algebra M Ω] [IsScalarTower F M Ω] [FiniteDimensional F M] [IsGalois F M] (τ : M ≃ₐ[F] M)
    (h : ∀ x : M, A.valuation (algebraMap M Ω x) ≤ 1 →
      A.valuation ((algebraMap M Ω (τ x)) - (algebraMap M Ω x)) < 1) :
    ∃ σ ∈ Ine (F := F) A, ∀ x : M, σ (algebraMap M Ω x) = algebraMap M Ω (τ x) := by
  haveI : NumberField M := NumberField.of_module_finite F M
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : IsAlgClosure M Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := F) M⟩
  have hint : ∀ x : 𝓞 M, A.valuation (algebraMap M Ω (x : M)) ≤ 1 := fun x =>
    (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A
      (x.isIntegral_coe.map (algebraMap M Ω).toIntAlgHom))
  let σ₁ : Ω ≃ₐ[F] Ω := τ.liftNormal Ω
  have h₁ : ∀ x : M, σ₁ (algebraMap M Ω x) = algebraMap M Ω (τ x) := fun x =>
    τ.liftNormal_commutes Ω x
  obtain ⟨g, hg⟩ := exists_smul_eq_val (F := M) (A := A) (A' := σ₁⁻¹ • A) (by
    intro x
    rw [smul_valuation_lt_one_iff, inv_inv]
    change A.valuation (algebraMap M Ω (x : M)) < 1 ↔ A.valuation (σ₁ (algebraMap M Ω (x : M))) < 1
    rw [h₁]
    have hx := h x (hint x)
    exact ⟨fun hl => by simpa using Valuation.map_add_lt _ hx hl,
           fun hl => by simpa using Valuation.map_sub_lt _ hl hx⟩)
  let σ₂ : Ω ≃ₐ[F] Ω := σ₁ * g.restrictScalars F
  have h₂ : ∀ x : M, σ₂ (algebraMap M Ω x) = algebraMap M Ω (τ x) := fun x => by
    rw [← h₁]
    exact congrArg σ₁ (g.commutes x)
  have h₂' : ∀ y, A.valuation (σ₂ y) < 1 ↔ A.valuation y < 1 := fun y => by
    rw [← hg y, smul_valuation_lt_one_iff, inv_inv]
    rfl
  obtain ⟨k, hk, hk'⟩ := exists_congr_inertia (F := M) (A := A) σ₂.toRingEquiv h₂' (by
    intro x
    change A.valuation (σ₂ (algebraMap M Ω (x : M)) - algebraMap M Ω (x : M)) < 1
    rw [h₂]
    exact h x (hint x))
  have hkinv : ∀ y, A.valuation (k.symm y) < 1 ↔ A.valuation y < 1 := fun y => by
    rw [← valuation_apply_lt_one_iff hk, k.apply_symm_apply]
  refine ⟨k.symm.restrictScalars F * σ₂, mem_Ine_of_integral (mem_Dec_of_lt fun y => ?_)
    fun b hb => ?_, fun x => ?_⟩
  · change A.valuation (k.symm (σ₂ y)) < 1 ↔ _
    rw [hkinv, h₂']
  · change A.valuation (k.symm (σ₂ b) - b) < 1
    rw [← valuation_apply_lt_one_iff hk, map_sub, k.apply_symm_apply, Valuation.map_sub_swap]
    exact hk' b hb
  · change k.symm (σ₂ (algebraMap M Ω x)) = _
    rw [h₂]
    exact k.symm.commutes (τ x)

theorem finiteGaloisInertia_lifts_absoluteInertia_rat (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (M : IntermediateField ℚ Ω)
    [FiniteDimensional ℚ M] [IsGalois ℚ M] (τ : M ≃ₐ[ℚ] M)
    (h : ∀ x : M, A.valuation (x : Ω) ≤ 1 → A.valuation ((τ x : Ω) - (x : Ω)) < 1) :
    ∃ σ ∈ Ine (F := ℚ) A, ∀ x : M, σ (x : Ω) = (τ x : Ω) := by
  have hst : @IsScalarTower ℚ M Ω (DivisionRing.toRatAlgebra (R := M)).toSMul
      (inferInstance : Algebra M Ω).toSMul (‹Algebra ℚ Ω›).toSMul :=
    @IsScalarTower.of_algebraMap_eq' ℚ M Ω _ _ _ DivisionRing.toRatAlgebra _ _
      (Subsingleton.elim _ _)
  have e : (DivisionRing.toRatAlgebra : Algebra ℚ M) = M.algebra' := Subsingleton.elim _ _
  have hfd : @FiniteDimensional ℚ M _ _ (DivisionRing.toRatAlgebra (R := M)).toModule := by
    rw [e]; assumption
  exact @exists_mem_Ine_lift ℚ Ω _ _ _ _ _ A M _ DivisionRing.toRatAlgebra _ hst hfd _ τ h

end InertiaLiftHelpers

/-- **Surjectivity of `cycZ ℚ Ω l` on inertia at `l`**: for any `A` over `l`,
`cycZ ℚ Ω l : Ine (F := ℚ) A → ℤ_[l]ˣ` is surjective. -/
theorem cycZ_Ine_surjective (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) (v : ℤ_[l]ˣ) :
    ∃ σ ∈ Ine (F := ℚ) A, cycZ ℚ Ω l σ = v := by
  have hstep : ∀ k : ℕ, ∃ σ ∈ Ine (F := ℚ) A,
      PadicInt.toZModPow k ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) = PadicInt.toZModPow k (v : ℤ_[l]) := by
    intro k
    have hl : l.Prime := Fact.out
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
    haveI : NeZero (l ^ k) := ⟨pow_ne_zero k hl.ne_zero⟩
    haveI : NeZero ((l : ℕ) : Ω) := ⟨by
      have h := (algebraMap ℚ Ω).injective.ne (Nat.cast_ne_zero.mpr hl.ne_zero : (l : ℚ) ≠ 0)
      simpa using h⟩
    haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun _ => inferInstance
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ k)
    have e : (IntermediateField.adjoin ℚ {ζ}).algebra' =
        (DivisionRing.toRatAlgebra : Algebra ℚ (IntermediateField.adjoin ℚ {ζ})) :=
      Subsingleton.elim _ _
    haveI : IsCyclotomicExtension {l ^ k} ℚ (IntermediateField.adjoin ℚ {ζ}) := by
      rw [← e]
      exact hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
    haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {ζ}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
    haveI : IsGalois ℚ (IntermediateField.adjoin ℚ {ζ}) :=
      IsCyclotomicExtension.isGalois {l ^ k} ℚ (IntermediateField.adjoin ℚ {ζ})
    let u : (ZMod (l ^ k))ˣ :=
      Units.map (PadicInt.toZModPow k : ℤ_[l] →+* ZMod (l ^ k)).toMonoidHom v
    have hz := IsCyclotomicExtension.zeta_spec (l ^ k) ℚ (IntermediateField.adjoin ℚ {ζ})
    have hirr := cyclotomic.irreducible_rat (Nat.pos_of_neZero (l ^ k))
    have hpow := hz.pow_of_coprime (u : ZMod (l ^ k)).val (ZMod.val_coe_unit_coprime u)
    let τ := IsCyclotomicExtension.fromZetaAut hpow hirr
    have hτz := IsCyclotomicExtension.fromZetaAut_spec hpow hirr
    obtain ⟨hτ₁, -⟩ := cyclotomicPrimePow_automorphism_inertial_at_prime Ω l k A hA ζ hζ τ
    obtain ⟨σ, hσ, hστ⟩ := finiteGaloisInertia_lifts_absoluteInertia_rat Ω A _ τ hτ₁
    refine ⟨σ, hσ, ?_⟩
    set z := IsCyclotomicExtension.zeta (l ^ k) ℚ (IntermediateField.adjoin ℚ {ζ})
    have hzΩ : IsPrimitiveRoot (z : Ω) (l ^ k) := IsPrimitiveRoot.coe_submonoidClass_iff.mpr hz
    have h₁ : σ (z : Ω) = (z : Ω) ^ (PadicInt.toZModPow k
        ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])).val :=
      cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G ℚ Ω) Ω σ) (z : Ω) hzΩ.pow_eq_one
    have h₂ : σ (z : Ω) = (z : Ω) ^ (u : ZMod (l ^ k)).val := by rw [hστ z, hτz]; simp [z]
    show PadicInt.toZModPow k ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) = (u : ZMod (l ^ k))
    apply ZMod.val_injective
    exact hzΩ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (h₁.symm.trans h₂)
  let f : G ℚ Ω → ℤ_[l] := fun σ => ((cycZ ℚ Ω l σ : ℤ_[l]ˣ) : ℤ_[l])
  have hf : Continuous f := Units.continuous_val.comp (continuous_cycZ ℚ Ω l)
  let t : ℕ → Set (G ℚ Ω) := fun k => (Ine (F := ℚ) A : Set (G ℚ Ω)) ∩
    {σ | PadicInt.toZModPow k (f σ) = PadicInt.toZModPow k (v : ℤ_[l])}
  have hcl : ∀ k, IsClosed (t k) := fun k => by
    refine (isClosed_Ine (F := ℚ) A).inter ?_
    have hset : {σ | PadicInt.toZModPow k (f σ) = PadicInt.toZModPow k (v : ℤ_[l])} =
        {σ | ‖f σ - (v : ℤ_[l])‖ ≤ (l : ℝ) ^ (-(k : ℤ))} := by
      ext σ
      simp only [Set.mem_ofPred_eq]
      rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker,
        map_sub, sub_eq_zero]
    rw [hset]
    exact isClosed_le (continuous_norm.comp (hf.sub continuous_const)) continuous_const
  have hdec : ∀ k, t (k + 1) ⊆ t k := by
    rintro k σ ⟨h₁, h₂⟩
    refine ⟨h₁, ?_⟩
    simp only [Set.mem_ofPred_eq] at h₂ ⊢
    rw [← PadicInt.cast_toZModPow k (k + 1) (Nat.le_succ k) (f σ),
      ← PadicInt.cast_toZModPow k (k + 1) (Nat.le_succ k), h₂]
  have hne : ∀ k, (t k).Nonempty := fun k => by
    obtain ⟨σ, hσ, h⟩ := hstep k; exact ⟨σ, hσ, h⟩
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t hdec hne
    (hcl 0).isCompact hcl
  rw [Set.mem_iInter] at hσ
  exact ⟨σ, (hσ 0).1, Units.ext (PadicInt.ext_of_toZModPow.mp fun k => (hσ k).2)⟩

/-- `1 + l ∈ ℤ_[l]ˣ` has infinite multiplicative order. -/
theorem exists_unit_infinite_order (l : ℕ) [Fact l.Prime] :
    ∃ u : ℤ_[l]ˣ, ∀ n : ℤ, n ≠ 0 → u ^ n ≠ 1 := by
  have hl : l.Prime := Fact.out
  have hu : IsUnit (1 + (l : ℤ_[l])) := by
    rw [← sub_neg_eq_add]
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ fun h =>
      PadicInt.irreducible_p.not_isUnit ((IsUnit.neg_iff _).1 h)
  obtain ⟨u, hu⟩ := hu
  refine ⟨u, fun n hn h => ?_⟩
  have h1 : u ^ n.natAbs = 1 := by
    rcases Int.natAbs_eq n with e | e
    · rw [← zpow_natCast, ← e, h]
    · rw [e, zpow_neg, inv_eq_one, zpow_natCast] at h; exact h
  have h2 : (((1 + l) ^ n.natAbs : ℕ) : ℤ_[l]) = ((1 : ℕ) : ℤ_[l]) := by
    push_cast
    rw [← hu, ← Units.val_pow_eq_pow_val, h1, Units.val_one]
  have h3 := Nat.cast_injective h2
  rw [pow_eq_one_iff] at h3
  rcases h3 with h3 | h3
  · exact hl.ne_zero (by omega)
  · exact hn (Int.natAbs_eq_zero.1 h3)

/-- **`ExistsDecompositionGroupCyclotomicCharacterZpowN`**: At any prime `v ∣ l`, there exists
`g ∈ Dec A` with `cycZ F Ω l g ^ n ≠ 1` for any nonzero `n : ℤ`. -/
theorem exists_mem_Dec_cycZ_zpow_ne_one (F Ω : Type) [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F))
    (A : ValuationSubring Ω) (hl : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal) (hA : IsPlaceOver A v)
    (n : ℤ) (hn : n ≠ 0) :
    ∃ g : G F Ω, g ∈ Dec (F := F) A ∧ cycZ F Ω l g ^ n ≠ 1 := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hv : A.valuation (l : Ω) < 1 := by simpa using (hA _).2 hl
  obtain ⟨u, hu⟩ := exists_unit_infinite_order l
  obtain ⟨σ, hσ, hσu⟩ := cycZ_Ine_surjective Ω l A hv u
  let K : IntermediateField ℚ Ω := (IsScalarTower.toAlgHom ℚ F Ω).fieldRange
  have : FiniteDimensional ℚ K :=
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom ℚ F Ω)).toLinearEquiv.finiteDimensional
  have : Finite ((Ω ≃ₐ[ℚ] Ω) ⧸ K.fixingSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ K.fixingSubgroup_isOpen
  have : K.fixingSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨N, hN, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero (H := K.fixingSubgroup)) σ
  let g : G F Ω := { (σ ^ N).toRingEquiv with
    commutes' := fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hmem _ ⟨x, rfl⟩ }
  have hD : σ ^ N ∈ Dec (F := ℚ) A := (Dec (F := ℚ) A).pow_mem (Ine_le_Dec A hσ) N
  refine ⟨g, hD, ?_⟩
  change cycZ ℚ Ω l (σ ^ N) ^ n ≠ 1
  rw [map_pow, hσu, ← zpow_natCast, ← zpow_mul]
  exact hu _ (mul_ne_zero (by exact_mod_cast hN.ne') hn)

section ImagesAndLevels

variable (F : Type) {Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  (l : ℕ) [Fact l.Prime]

/-- Image of the decomposition group `Dec A` under the `l`-adic cyclotomic character. -/
def decImage (A : ValuationSubring Ω) : Subgroup ℤ_[l]ˣ := (Dec (F := F) A).map (cycZ F Ω l)

/-- Image of the inertia group `Ine A` under the `l`-adic cyclotomic character. -/
def ineImage (A : ValuationSubring Ω) : Subgroup ℤ_[l]ˣ := (Ine (F := F) A).map (cycZ F Ω l)

theorem ineImage_le_decImage (A : ValuationSubring Ω) : ineImage F l A ≤ decImage F l A :=
  Subgroup.map_mono (Ine_le_Dec A)

end ImagesAndLevels

/-- **`IneOpen`**: For `v ∣ l` and `A` over `v`, `ineImage F l A` is open of finite index `≤ [F : ℚ]`. -/
theorem ineOpen (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω)
    (hl : v ∈ Above F l) (hA : IsPlaceOver A v) :
    IsOpen (ineImage F l A : Set ℤ_[l]ˣ) ∧ (ineImage F l A).index ≠ 0 ∧
      (ineImage F l A).index ≤ Module.finrank ℚ F := by
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  have hl' : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal := hl
  have hv : A.valuation (l : Ω) < 1 := by simpa using (hA _).2 hl'
  let K : IntermediateField ℚ Ω := (IsScalarTower.toAlgHom ℚ F Ω).fieldRange
  have hK : Module.finrank ℚ F = K.fixingSubgroup.index := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom ℚ F Ω)).toLinearEquiv.finrank_eq
  have hK0 : K.fixingSubgroup.index ≠ 0 := by rw [← hK]; exact Module.finrank_pos.ne'
  let I : Subgroup (G ℚ Ω) := Ine (F := ℚ) A
  let f : I →* ℤ_[l]ˣ := (cycZ ℚ Ω l).comp I.subtype
  have hf : Function.Surjective f := fun u => by
    obtain ⟨σ, hσ, h⟩ := cycZ_Ine_surjective Ω l A hv u
    exact ⟨⟨σ, hσ⟩, h⟩
  have hle : (K.fixingSubgroup.subgroupOf I).map f ≤ ineImage F l A := by
    rintro _ ⟨σ, hσ, rfl⟩
    let g : G F Ω := { σ.1.toRingEquiv with
      commutes' := fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ ⟨x, rfl⟩ }
    exact ⟨g, σ.2, rfl⟩
  have hrel0 : K.fixingSubgroup.relIndex ⊤ ≠ 0 := by rwa [Subgroup.relIndex_top_right]
  have hrel : K.fixingSubgroup.relIndex I ≤ K.fixingSubgroup.index := by
    rw [← Subgroup.relIndex_top_right]
    exact Subgroup.relIndex_le_of_le_right le_top hrel0
  have hrelI : K.fixingSubgroup.relIndex I ≠ 0 := fun h =>
    hrel0 (Subgroup.relIndex_eq_zero_of_le_right le_top h)
  have hdvd : (ineImage F l A).index ∣ K.fixingSubgroup.relIndex I :=
    (Subgroup.index_dvd_of_le hle).trans (Subgroup.index_map_dvd _ hf)
  have h0 : (ineImage F l A).index ≠ 0 := ne_zero_of_dvd_ne_zero hrelI hdvd
  refine ⟨?_, h0, ?_⟩
  · have : (ineImage F l A).FiniteIndex := ⟨h0⟩
    refine Subgroup.isOpen_of_isClosed_of_finiteIndex _ ?_
    exact ((isClosed_Ine (F := F) A).isCompact.image (continuous_cycZ F Ω l)).isClosed
  · rw [hK]
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hrelI) hdvd).trans hrel

theorem isOpen_decImage {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {v : HeightOneSpectrum (𝓞 F)}
    {A : ValuationSubring Ω} (hv : v ∈ Above F l) (hA : IsPlaceOver A v) :
    IsOpen (decImage F l A : Set ℤ_[l]ˣ) :=
  Subgroup.isOpen_mono (ineImage_le_decImage F l A) (ineOpen F Ω l v A hv hA).1

/-- **`LevelLeIne`**: If `φ : F →ₐ[ℚ] K = ℚ(ζ_N)`, then for any place `A` above `v ∣ l`,
`levelGroup l N (fieldSubgroup N K φ.fieldRange ⊓ levelInertia l N) ≤ ineImage F l A`. -/
theorem levelLeIne (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (N : ℕ) [NeZero N] (K : Type) [Field K] [NumberField K]
    [IsCyclotomicExtension {N} ℚ K] (φ : F →ₐ[ℚ] K) (l : ℕ) [Fact l.Prime]
    (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (hv : v ∈ Above F l)
    (hA : IsPlaceOver A v) :
    levelGroup l N (fieldSubgroup N K φ.fieldRange ⊓ levelInertia l N) ≤ ineImage F l A := by
  intro u hu
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
  haveI : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨h, ⟨hF, hI⟩, hh⟩ := mem_levelGroup.mp hu
  have hl : A.valuation (l : Ω) < 1 := by simpa using (hA (l : 𝓞 F)).mpr hv
  obtain ⟨σ, hσI, hσu⟩ := cycZ_Ine_surjective Ω l A hl u
  have hcop : (N / l ^ N.factorization l).Coprime l :=
    (Nat.coprime_ordCompl (Fact.out : l.Prime) (NeZero.ne N)).symm
  have hfixm : ∀ ζ : Ω, ζ ^ (N / l ^ N.factorization l) = 1 → σ ζ = ζ := fun ζ hζ =>
    (ineFixRoots ℚ Ω l A hl _ hcop ζ hζ).2 σ hσI
  have hroots : ∀ ζ : Ω, ζ ^ N = 1 → σ.toRingEquiv ζ = ζ ^ (h : ZMod N).val := by
    rw [classIff Ω l N σ.toRingEquiv h]
    refine ⟨fun ζ hζ => ?_, ?_⟩
    · have h1 : (ZMod.unitsMap (Nat.ordCompl_dvd N l)) h = 1 := hI
      have e : σ.toRingEquiv ζ = ζ := hfixm ζ hζ
      rw [e, h1, Units.val_one]
      rcases Nat.lt_or_ge 1 (N / l ^ N.factorization l) with hm | hm
      · haveI : Fact (1 < N / l ^ N.factorization l) := ⟨hm⟩
        rw [ZMod.val_one, pow_one]
      · have hpos : 0 < N / l ^ N.factorization l := Nat.ordCompl_pos l (NeZero.ne N)
        have hm1 : N / l ^ N.factorization l = 1 := by omega
        rw [hm1, pow_one] at hζ
        rw [hζ, one_pow]
    · rw [hh]
      congr 1
      exact hσu.symm
  have hfixF : ∀ x : F, σ.toRingEquiv (algebraMap F Ω x) = algebraMap F Ω x :=
    (classFix F Ω N K φ σ.toRingEquiv h hroots).mpr hF
  let τ : Ω ≃ₐ[F] Ω := { σ.toRingEquiv with commutes' := hfixF }
  exact ⟨τ, ⟨hσI.1, fun x hx => hσI.2 x hx⟩, by rw [← hσu]; rfl⟩

theorem princ_le_ineImage {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {N : ℕ} [NeZero N] {K : Type} [Field K] [NumberField K]
    [IsCyclotomicExtension {N} ℚ K] (φ : F →ₐ[ℚ] K) {l : ℕ} [Fact l.Prime]
    {v : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω}
    (hv : v ∈ Above F l) (hA : IsPlaceOver A v) :
    princ l (N.factorization l) ≤ ineImage F l A :=
  (princ_le_levelGroup N _).1.trans (levelLeIne F Ω N K φ l v A hv hA)

end CyclotomicInertiaAndLevels

/-! ## Section 4: Global & Local `H⁰` Twist Lengths, Conjugation of Images, and `contTw` -/

section H0TwistLengthsAndImages

section GlobalRepDefs

variable (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime]

/-- The `(-e)`-twisted representation `(ℚ_l / ℤ_l)(-e)` on the absolute Galois group `G F Ω`. -/
def qzG (e : ℤ) : Representation ℤ_[l] (G F Ω) (QZ l) := scalRep (QZ l) (cycZ F Ω l ^ (-e))

theorem qzG_apply (e : ℤ) (g : G F Ω) (x : QZ l) :
    qzG F Ω l e g x = ((cycZ F Ω l g ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • x := rfl

theorem qzTw_comp_toGS [IsAlgClosure F Ω] (D : LData F Ω l) (e : ℤ) :
    (qzTw D e).comp (toGS Ω _) = qzG F Ω l e := by
  ext g x
  simp [qzG, qzTw, scalRep, ← D.hchi]

theorem contAction_qzG [IsAlgClosure F Ω] (e : ℤ) : ContAction (qzG F Ω l e) :=
  contScal l _ _ (Units.continuous_val.comp ((continuous_cycZ F Ω l).zpow (-e)))

theorem contAction_zlTw [IsAlgClosure F Ω] (D : LData F Ω l) (n : ℤ) : ContAction (zlTw D n) :=
  ((Units.continuous_val.comp ((continuous_LData_chi D).zpow n)).comp continuous_fst).mul
    continuous_snd

theorem contTw [IsAlgClosure F Ω] (D : LData F Ω l) (e : ℤ) :
    ContAction (qzTw D e) ∧ ContAction (zlTw D e) :=
  ⟨contAction_qzTw D e, contAction_zlTw F Ω l D e⟩

end GlobalRepDefs

/-- Canonical `l`-adic cyclotomic character on `Gal(AlgebraicClosure E / E)`. -/
def eps (l : ℕ) [Fact l.Prime] (E : Type*) [Field E] :
    (AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) →* ℤ_[l]ˣ :=
  (cyclotomicCharacter (AlgebraicClosure E) l).comp
    (MulSemiringAction.toRingAut (AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) (AlgebraicClosure E))

/-- Image of the absolute Galois group `Gal(AlgebraicClosure E / E)` under `χ_l`. -/
def galImage (l : ℕ) [Fact l.Prime] (E : Type*) [Field E] : Subgroup ℤ_[l]ˣ := (eps l E).range

/-- Global Galois twist invariant `ν_l(Gal(Ē/E), tr)`. -/
def nuGal (l : ℕ) [Fact l.Prime] (E : Type*) [Field E] (tr : ℕ) : ℕ∞ :=
  ⨅ g : AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E,
    emultiplicity (l : ℤ_[l]) (((eps l E g : ℤ_[l]ˣ) : ℤ_[l]) ^ tr - 1)

theorem nuGal_eq_nu (l : ℕ) [Fact l.Prime] (E : Type*) [Field E] (tr : ℕ) :
    nuGal l E tr = nu l (galImage l E) tr := by
  unfold nuGal nu nuStar galImage
  rw [iInf, Set.image_image]
  congr 1
  ext x
  simp [MonoidHom.coe_range]

/-- Conjugation invariance of Mathlib's `cyclotomicCharacter` along any ring isomorphism `φ : L ≃+* M`. -/
theorem cyclotomicCharacter_conj {L M : Type*} [Field L] [Field M] (p : ℕ) [Fact p.Prime]
    (φ : L ≃+* M) (g : L ≃+* L) (g' : M ≃+* M) (h : ∀ x, g' (φ x) = φ (g x)) :
    cyclotomicCharacter M p g' = cyclotomicCharacter L p g := by
  have hg' : g' = φ.symm.trans (g.trans φ) := by
    ext x
    rw [RingEquiv.trans_apply, RingEquiv.trans_apply, ← h, RingEquiv.apply_symm_apply]
  subst hg'
  symm
  by_cases H : ∀ i : ℕ, ∃ ζ : L, IsPrimitiveRoot ζ (p ^ i)
  · have hL (i : ℕ) : HasEnoughRootsOfUnity L (p ^ i) := ⟨H i, rootsOfUnity.isCyclic _ _⟩
    have hM (i : ℕ) : HasEnoughRootsOfUnity M (p ^ i) := by
      obtain ⟨ζ, hζ⟩ := H i
      exact ⟨⟨φ ζ, hζ.map_of_injective φ.injective⟩, rootsOfUnity.isCyclic _ _⟩
    ext1
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    rw [cyclotomicCharacter.toZModPow, cyclotomicCharacter.toZModPow]
    refine modularCyclotomicCharacter.unique M
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity M (p ^ n)) _ fun t ht => ?_
    have hs : Units.map φ.symm.toMonoidHom t ∈ rootsOfUnity (p ^ n) L := by
      rw [mem_rootsOfUnity] at ht ⊢
      rw [← map_pow, ht, map_one]
    have key := modularCyclotomicCharacter.spec L
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity L (p ^ n)) g hs
    simp only [Units.coe_map] at key
    change g (φ.symm (t : M)) = (φ.symm (t : M)) ^ _ at key
    rw [RingEquiv.trans_apply, RingEquiv.trans_apply, key, map_pow, RingEquiv.apply_symm_apply]
  · have H' : ¬ ∀ i : ℕ, ∃ ζ : M, IsPrimitiveRoot ζ (p ^ i) := by
      intro hM
      apply H
      intro i
      obtain ⟨ζ, hζ⟩ := hM i
      exact ⟨φ.symm ζ, hζ.map_of_injective φ.symm.injective⟩
    ext1
    simp [cyclotomicCharacter, cyclotomicCharacter.toFun, H, H']

private theorem units_zpow_neg_smul_eq_self_iff (l : ℕ) [Fact l.Prime] (A : Type*)
    [AddCommGroup A] [Module ℤ_[l] A] (v : ℤ_[l]ˣ) (e : ℤ) (x : A) :
    ((v ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • x = x ↔ ((v : ℤ_[l]) ^ e.natAbs) • x = x := by
  have key : ∀ n : ℕ, ((v ^ (-(n : ℤ)) : ℤ_[l]ˣ) : ℤ_[l]) • x = x ↔
      ((v : ℤ_[l]) ^ n) • x = x := fun n => by
    rw [← Units.val_pow_eq_pow_val, ← Units.smul_def, ← Units.smul_def, zpow_neg, zpow_natCast]
    exact ⟨fun h => by conv_lhs => rw [← h]; simp, fun h => by conv_lhs => rw [← h]; simp⟩
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg e
  · simpa using key n
  · simp [← Units.val_pow_eq_pow_val]

/-- **`H0ScalRepInvPowEqTwistInv`**: `H⁰(Γ, (ℚ_l/ℤ_l)(-e)) = twistInv l (QZ l) ψ.range |e|`. -/
theorem H0_scalRep_inv_pow_eq_twistInv (l : ℕ) [Fact l.Prime] (Γ : Type*) [Group Γ]
    (ψ : Γ →* ℤ_[l]ˣ) (e : ℤ) :
    H0 (scalRep (QZ l) (ψ ^ (-e))) = twistInv l (QZ l) ψ.range e.natAbs := by
  ext x
  rw [mem_twistInv]
  change (∀ g : Γ, (scalRep (QZ l) (ψ ^ (-e))) g x = x) ↔ _
  simp only [scalRep_apply, MonoidHom.zpow_apply]
  constructor
  · intro h u hu
    obtain ⟨g, rfl⟩ := hu
    exact (units_zpow_neg_smul_eq_self_iff l (QZ l) (ψ g) e x).mp (h g)
  · intro h g
    exact (units_zpow_neg_smul_eq_self_iff l (QZ l) (ψ g) e x).mpr (h (ψ g) ⟨g, rfl⟩)

/-- **`Ranges`**: Ranges of `cycZ`, `D.chi`, and local restrictions `D.chi ∘ locFam`. -/
theorem ranges (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (D : LData F Ω l) :
    (cycZ F Ω l).range = galImage l F ∧
      D.chi.range = galImage l F ∧
      ∀ v : D.S, (D.chi.comp (locFam D.S D.A v)).range = decImage F l (D.A v) := by
  have hcyc : (cycZ F Ω l).range = galImage l F := by
    let e : Ω ≃ₐ[F] AlgebraicClosure F := IsAlgClosure.equiv F Ω (AlgebraicClosure F)
    have hpt : ∀ σ : G F Ω, cycZ F Ω l σ = eps l F (AlgEquiv.autCongr e σ) := fun σ => by
      simp only [cycZ, eps, MonoidHom.comp_apply]
      exact (cyclotomicCharacter_conj l e.toRingEquiv _ _ fun x => by
        show e (σ (e.symm (e x))) = e (σ x)
        rw [e.symm_apply_apply]).symm
    ext x
    simp only [MonoidHom.mem_range, galImage]
    exact ⟨fun ⟨σ, hσ⟩ => ⟨_, (hpt σ).symm.trans hσ⟩,
           fun ⟨τ, hτ⟩ => ⟨(AlgEquiv.autCongr e).symm τ, by rw [hpt, MulEquiv.apply_symm_apply, hτ]⟩⟩
  have hchi : D.chi.range = (cycZ F Ω l).range := by
    have htop : (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))).range = ⊤ :=
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
    rw [← D.hchi, MonoidHom.range_comp, htop, ← MonoidHom.range_eq_map]
  refine ⟨hcyc, hchi.trans hcyc, fun v => ?_⟩
  have hcomp : D.chi.comp (locFam D.S D.A v) = (cycZ F Ω l).comp (Dec (F := F) (D.A v)).subtype := by
    rw [← D.hchi]; rfl
  rw [hcomp, MonoidHom.range_comp, Subgroup.range_subtype]
  rfl

section H0Lengths

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime]

theorem global_fixed_points_eq_twist_fixed_points (D : LData F Ω l) (e : ℤ) :
    H0 (qzTw D e) = twistInv l (QZ l) (galImage l F) e.natAbs := by
  rw [← (ranges F Ω l D).2.1]
  exact H0_scalRep_inv_pow_eq_twistInv l _ D.chi e

theorem local_fixed_points_eq_twist_fixed_points (D : LData F Ω l) (e : ℤ) (v : D.S) :
    H0 ((qzTw D e).comp (locFam D.S D.A v)) = twistInv l (QZ l) (decImage F l (D.A v)) e.natAbs := by
  show H0 (scalRep (QZ l) ((D.chi.comp (locFam D.S D.A v)) ^ (-e))) = _
  rw [H0_scalRep_inv_pow_eq_twistInv, (ranges F Ω l D).2.2 v]

theorem length_H0_global_eq_nu (D : LData F Ω l) (e : ℤ) :
    Module.length ℤ_[l] (H0 (qzTw D e)) = nuGal l F e.natAbs := by
  rw [global_fixed_points_eq_twist_fixed_points, nuGal_eq_nu]
  exact lenTwist l _ _

theorem length_H0_local_eq_nu (D : LData F Ω l) (e : ℤ) (v : D.S) :
    Module.length ℤ_[l] (H0 ((qzTw D e).comp (locFam D.S D.A v))) =
      nu l (decImage F l (D.A v)) e.natAbs := by
  rw [local_fixed_points_eq_twist_fixed_points]
  exact lenTwist l _ _

theorem local_H0_length_eq_sum (D : LData F Ω l) (e : ℤ) :
    sumLocalH0TwistLength D e = ∑ v : D.S, nu l (decImage F l (D.A v)) e.natAbs :=
  Finset.sum_congr rfl fun v _ => length_H0_local_eq_nu D e v

theorem conj_mem_Dec {A : ValuationSubring Ω} {g σ : G F Ω} (hσ : σ ∈ Dec (F := F) (g • A)) :
    g⁻¹ * σ * g ∈ Dec (F := F) A := by
  have h : σ • g • A = g • A := hσ
  show (g⁻¹ * σ * g) • A = A
  rw [mul_smul, mul_smul, h, inv_smul_smul]

theorem conj_mem_Ine' {A : ValuationSubring Ω} {g σ : G F Ω} (hσ : σ ∈ Ine (F := F) (g • A)) :
    g⁻¹ * σ * g ∈ Ine (F := F) A := by
  refine ⟨conj_mem_Dec hσ.1, fun x hx => ?_⟩
  have hx' : (g • A).valuation (g x) ≤ 1 := by
    rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      AlgEquiv.smul_def]
    have : (g⁻¹ : G F Ω) (g x) = x := by show (g⁻¹ * g) x = x; simp
    rw [this]
    exact (A.valuation_le_one_iff x).1 hx
  have h := (smul_valuation_lt_one_iff g A _).1 (hσ.2 _ hx')
  have e : (g⁻¹ : G F Ω) (σ (g x) - g x) = (g⁻¹ * σ * g) x - x := by
    rw [map_sub]
    congr 1
    show (g⁻¹ * g) x = x; simp
  rwa [e] at h

/-- **`ImageConj`**: `decImage F l A` and `ineImage F l A` depend only on the prime `v` below `A`. -/
theorem imageConj (v : HeightOneSpectrum (𝓞 F)) (A A' : ValuationSubring Ω)
    (hA : IsPlaceOver A v) (hA' : IsPlaceOver A' v) :
    decImage F l A = decImage F l A' ∧ ineImage F l A = ineImage F l A' := by
  have hc : ∀ g σ : G F Ω, cycZ F Ω l (g⁻¹ * σ * g) = cycZ F Ω l σ := fun g σ => by
    rw [map_mul, map_mul, map_inv, mul_comm _ (cycZ F Ω l σ), inv_mul_cancel_right]
  have key : ∀ A A' : ValuationSubring Ω, IsPlaceOver A v → IsPlaceOver A' v →
      decImage F l A' ≤ decImage F l A ∧ ineImage F l A' ≤ ineImage F l A := fun A A' hA hA' => by
    obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hA hA'
    exact ⟨fun _ ⟨σ, hσ, h⟩ => ⟨_, conj_mem_Dec hσ, (hc g σ).trans h⟩,
           fun _ ⟨σ, hσ, h⟩ => ⟨_, conj_mem_Ine' hσ, (hc g σ).trans h⟩⟩
  exact ⟨le_antisymm (key A' A hA' hA).1 (key A A' hA hA').1,
         le_antisymm (key A' A hA' hA).2 (key A A' hA hA').2⟩

end H0Lengths

end H0TwistLengthsAndImages

/-! ## Section 5: `ShaAbs`, `ShaInfl`, Transport, `VFormula`, and `ShaLenEqShaInv` Wired onto `realGaloisSelmerSystem` -/

section ShaAbsAndInvariance

section ShaAbsDef

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

/-- Absolute Tate–Shafarevich submodule `ShaAbs ρ S ≤ H¹(G F Ω, M)`: locally trivial at every
decomposition group over `v ∈ S` and unramified at every inertia group over `v ∉ S`. -/
def ShaAbs (ρ : Representation R (G F Ω) M) (S : Set (HeightOneSpectrum (𝓞 F))) :
    Submodule R (H1 ρ) :=
  (⨅ (v : HeightOneSpectrum (𝓞 F)) (_ : v ∈ S) (A : ValuationSubring Ω) (_ : IsPlaceOver A v),
      LinearMap.ker (resH1 ρ (Dec (F := F) A).subtype continuous_subtype_val)) ⊓
    ⨅ (v : HeightOneSpectrum (𝓞 F)) (_ : v ∉ S) (A : ValuationSubring Ω) (_ : IsPlaceOver A v),
      LinearMap.ker (resH1 ρ (Ine (F := F) A).subtype continuous_subtype_val)

theorem mem_ShaAbs (ρ : Representation R (G F Ω) M) (S : Set (HeightOneSpectrum (𝓞 F)))
    (x : H1 ρ) :
    x ∈ ShaAbs ρ S ↔
      (∀ v ∈ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v →
        resH1 ρ (Dec (F := F) A).subtype continuous_subtype_val x = 0) ∧
      ∀ v ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v →
        resH1 ρ (Ine (F := F) A).subtype continuous_subtype_val x = 0 := by
  simp only [ShaAbs, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]

private theorem resH1_mk_eq_zero_iff_coboundary (ρ : Representation R (G F Ω) M) (z : Z1 ρ)
    (H : Subgroup (G F Ω)) :
    resH1 ρ H.subtype continuous_subtype_val (Submodule.Quotient.mk z) = 0 ↔
      ∃ m, ∀ g ∈ H, z.1 g = ρ g m - m := by
  simp [resH1, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, mem_B1, restrictCocycles1]

theorem mk_mem_ShaAbs (ρ : Representation R (G F Ω) M) (S : Set (HeightOneSpectrum (𝓞 F)))
    (z : Z1 ρ) :
    (Submodule.Quotient.mk z : H1 ρ) ∈ ShaAbs ρ S ↔
      (∀ v ∈ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v →
        ∃ m, ∀ g ∈ Dec (F := F) A, z.1 g = ρ g m - m) ∧
      ∀ v ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v →
        ∃ m, ∀ g ∈ Ine (F := F) A, z.1 g = ρ g m - m := by
  simp only [mem_ShaAbs, resH1_mk_eq_zero_iff_coboundary]

end ShaAbsDef

/-- Canonical invariant `shaInv F l e := Module.length ℤ_[l] (ShaAbs (qzG F (AlgebraicClosure F) l e) (Above F l))`. -/
def shaInv (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (e : ℤ) : ℕ∞ :=
  Module.length ℤ_[l] (ShaAbs (qzG F (AlgebraicClosure F) l e) (Above F l))

/-- **`ShaInfl`**: Inflation `resH1 ρ (toGS Ω S)` identifies `Sha1` with `ShaAbs`. -/
theorem shaInfl (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (A : S → ValuationSubring Ω)
    (hA : ∀ v, IsPlaceOver (A v) v.1) (R : Type) [CommRing R] (M : Type) [AddCommGroup M]
    [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    [T2Space M] (ρ : Representation R (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) :
    (Sha1 ρ (locFam S A) (continuous_locFam S A)).map
      (resH1 ρ (toGS Ω _) (continuous_toGS Ω _)) =
      ShaAbs (ρ.comp (toGS Ω _)) (S : Set (HeightOneSpectrum (𝓞 F))) := by
  have hI := (infUnram (F := F) (Ω := Ω) (S := (S : Set (HeightOneSpectrum (𝓞 F)))) ρ).2
  have key : ∀ z : Z1 ρ,
      (Submodule.Quotient.mk z : H1 ρ) ∈ Sha1 ρ (locFam S A) (continuous_locFam S A) ↔
        ∀ v : S, ∃ m, ∀ g ∈ Dec (F := F) (A v), z.1 (toGS Ω _ g) = ρ (toGS Ω _ g) m - m := fun z => by
    refine (Submodule.mem_iInf _).trans (forall_congr' fun v => ?_)
    exact ((Submodule.Quotient.mk_eq_zero _).trans (mem_B1 _ _)).trans
      (exists_congr fun _ => ⟨fun h g hg => h ⟨g, hg⟩, fun h (g : Dec (F := F) (A v)) => h g.1 g.2⟩)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine (mem_ShaAbs _ _ _).2 ⟨?_, (hI _).1 ⟨y, rfl⟩⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    intro v hv A' hA'
    obtain ⟨m, hm⟩ := (key z).1 hy ⟨v, hv⟩
    obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := F) (hA ⟨v, hv⟩) hA'
    refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_B1 _ _).2 ?_)
    let w := restrictCocycles1 ρ (toGS Ω _) (continuous_toGS Ω _) z
    refine ⟨ρ (toGS Ω _ g) m - w.1 g, fun σ => ?_⟩
    have h1 : (σ : G F Ω) ∈ Dec (F := F) (g • A ⟨v, hv⟩) := by rw [hg]; exact σ.2
    have h2 := cocycle1_conj_coboundary _ w.2.2 g _ m (hm _ (conj_mem_Dec h1))
    have h3 : g * (g⁻¹ * σ * g) * g⁻¹ = σ := by group
    rw [h3] at h2
    exact h2
  · intro hx
    obtain ⟨-, h2⟩ := (mem_ShaAbs _ _ _).1 hx
    obtain ⟨y, rfl⟩ := (hI x).2 h2
    refine ⟨y, ?_, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact (key z).2 fun v =>
      ((mk_mem_ShaAbs _ _ (restrictCocycles1 ρ (toGS Ω _) (continuous_toGS Ω _) z)).1 hx).1
        v.1 v.2 _ (hA v)

/-- **`GalTransport`**: Field homomorphism `f : F →+* F'` lifted to `σ : Ω ≃+* Ω'` induces a
continuous injective homomorphism `φ : G F' Ω' →* G F Ω` preserving `cycZ`. -/
theorem galTransport (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (F' Ω' : Type) [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω']
    [IsAlgClosure F' Ω'] (f : F →+* F') (σ : Ω ≃+* Ω')
    (hσ : ∀ x, σ (algebraMap F Ω x) = algebraMap F' Ω' (f x)) :
    ∃ φ : G F' Ω' →* G F Ω, Continuous φ ∧ (∀ g x, σ (φ g x) = g (σ x)) ∧
      (∀ (l : ℕ) [Fact l.Prime] (g : G F' Ω'), cycZ F Ω l (φ g) = cycZ F' Ω' l g) ∧
      Function.Injective φ ∧ (Function.Surjective f → Function.Surjective φ) := by
  have hc : ∀ g : G F' Ω', ∀ x : F,
      ((σ.trans g.toRingEquiv).trans σ.symm) (algebraMap F Ω x) = algebraMap F Ω x := fun g x => by
    simp only [RingEquiv.trans_apply, hσ, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
    rw [← hσ, RingEquiv.symm_apply_apply]
  let φ : G F' Ω' →* G F Ω :=
    { toFun := fun g => AlgEquiv.ofRingEquiv (hc g)
      map_one' := by ext x; simp
      map_mul' := fun a b => by ext x; simp }
  have hφ : ∀ g x, φ g x = σ.symm (g (σ x)) := fun _ _ => rfl
  haveI : Algebra.IsAlgebraic F' Ω' := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsIntegral F' Ω' := Algebra.IsAlgebraic.isIntegral
  refine ⟨φ, ?_, fun g x => by rw [hφ, σ.apply_symm_apply], ?_, ?_, ?_⟩
  · apply continuous_of_continuousAt_one
    rw [ContinuousAt, map_one, Filter.tendsto_def]
    intro U hU
    obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff F Ω U).1 hU
    let b := Module.finBasis F E
    have hV : (⋂ i, {g : G F' Ω' | g (σ (b i)) = σ (b i)}) ∈ nhds (1 : G F' Ω') :=
      Filter.iInter_mem.2 fun i =>
        IsOpen.mem_nhds (isOpen_setOf_apply (σ (b i)) (fun y => y = σ (b i))) rfl
    refine Filter.mem_of_superset hV fun g hg => hEU ?_
    have hb : ∀ i, φ g (b i) = b i := fun i => by
      rw [hφ, Set.mem_iInter.1 hg i, RingEquiv.symm_apply_apply]
    show φ g ∈ E.fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have hs := congrArg (fun z : E => (z : Ω)) (b.sum_repr ⟨y, hy⟩)
    simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at hs
    rw [← hs, map_sum]
    simp [map_smul, hb]
  · intro l _ g
    simp only [cycZ, MonoidHom.comp_apply]
    refine (cyclotomicCharacter_conj l σ _ _ fun x => ?_).symm
    show g (σ x) = σ (φ g x)
    rw [hφ, σ.apply_symm_apply]
  · intro a b h
    ext y
    have := congrArg (fun k : G F Ω => k (σ.symm y)) h
    simpa [hφ] using this
  · intro hf h
    have hc' : ∀ y : F', ((σ.symm.trans h.toRingEquiv).trans σ) (algebraMap F' Ω' y) =
        algebraMap F' Ω' y := fun y => by
      obtain ⟨x, rfl⟩ := hf y
      rw [← hσ]
      simp
    exact ⟨AlgEquiv.ofRingEquiv hc', by ext x; simp [hφ]⟩

private theorem pt_val_lt_one {Ω Ω' : Type} [Field Ω] [Field Ω'] {σ : Ω ≃+* Ω'}
    {A : ValuationSubring Ω} {A' : ValuationSubring Ω'} (hA : ∀ x, x ∈ A ↔ σ x ∈ A') (x : Ω) :
    A.valuation x < 1 ↔ A'.valuation (σ x) < 1 := by
  rw [valuation_lt_one_iff' (Ω := Ω), valuation_lt_one_iff' (Ω := Ω'), ← hA, ← map_inv₀, ← hA,
    map_eq_zero_iff _ σ.injective]

/-- **`PlaceTransport`**: Pullback of places, valuation subrings, decomposition and inertia groups
along a compatible field homomorphism `(f, σ, φ)`. -/
theorem placeTransport (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (F' Ω' : Type) [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω']
    [IsAlgClosure F' Ω'] (f : F →+* F') (σ : Ω ≃+* Ω')
    (h : ∀ x, σ (algebraMap F Ω x) = algebraMap F' Ω' (f x)) (φ : G F' Ω' →* G F Ω)
    (hφ : ∀ g x, σ (φ g x) = g (σ x)) (v' : HeightOneSpectrum (𝓞 F')) (A' : ValuationSubring Ω')
    (hv' : IsPlaceOver A' v') :
    ∃ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v ∧
      (∀ l : ℕ, v ∈ Above F l ↔ v' ∈ Above F' l) ∧ (∀ x, x ∈ A ↔ σ x ∈ A') ∧
      (∀ g, φ g ∈ Dec (F := F) A ↔ g ∈ Dec (F := F') A') ∧
      ∀ g, φ g ∈ Ine (F := F) A ↔ g ∈ Ine (F := F') A' := by
  have hne : v'.asIdeal.comap (RingOfIntegers.mapRingHom f) ≠ ⊥ := by
    intro hb
    have h1 : ((Ideal.absNorm v'.asIdeal : ℕ) : 𝓞 F) ∈
        v'.asIdeal.comap (RingOfIntegers.mapRingHom f) := by
      rw [Ideal.mem_comap, map_natCast]
      exact Ideal.absNorm_mem _
    rw [hb, Ideal.mem_bot, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff] at h1
    exact v'.ne_bot h1
  let v : HeightOneSpectrum (𝓞 F) :=
    ⟨v'.asIdeal.comap (RingOfIntegers.mapRingHom f), Ideal.comap_isPrime _ _, hne⟩
  have hA : ∀ x, x ∈ A'.comap σ.toRingHom ↔ σ x ∈ A' := fun _ => Iff.rfl
  generalize A'.comap σ.toRingHom = A at hA
  have hD : ∀ g, φ g ∈ Dec (F := F) A ↔ g ∈ Dec (F := F') A' := fun g => by
    constructor
    · intro hg
      rw [mem_Dec]
      ext y
      obtain ⟨x, rfl⟩ := σ.surjective y
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, ← hφ, ← hA,
        ← hA, map_inv]
      exact apply_mem_iff_of_mem_Dec ((Dec (F := F) A).inv_mem hg) _
    · intro hg
      rw [mem_Dec]
      ext x
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, AlgEquiv.smul_def, hA,
        hA, hφ]
      exact apply_mem_iff_of_mem_Dec ((Dec (F := F') A').inv_mem hg) _
  refine ⟨v, A, ?_, ?_, hA, hD, ?_⟩
  · intro x
    have e : x ∈ v.asIdeal ↔ RingOfIntegers.mapRingHom f x ∈ v'.asIdeal := Iff.rfl
    rw [e, ← hv', pt_val_lt_one hA, h]
    rfl
  · intro l
    show RingOfIntegers.mapRingHom f ((l : ℕ) : 𝓞 F) ∈ v'.asIdeal ↔ ((l : ℕ) : 𝓞 F') ∈ v'.asIdeal
    rw [map_natCast]
  · intro g
    constructor
    · intro hg
      refine ⟨(hD g).1 hg.1, fun y hy => ?_⟩
      obtain ⟨x, rfl⟩ := σ.surjective y
      rw [← hφ, ← map_sub, ← pt_val_lt_one hA]
      exact hg.2 _ ((A.valuation_le_one_iff _).2 ((hA x).2 ((A'.valuation_le_one_iff _).1 hy)))
    · intro hg
      refine ⟨(hD g).2 hg.1, fun x hx => ?_⟩
      rw [pt_val_lt_one hA, map_sub, hφ]
      exact hg.2 _ ((A'.valuation_le_one_iff _).2 ((hA x).1 ((A.valuation_le_one_iff _).1 hx)))

/-- **`ShaAbsRes`**: Restriction along `φ : G F' Ω' →* G F Ω` preserves `ShaAbs` and gives
length monotonicity when `φ` is surjective. -/
theorem shaAbsRes (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (F' Ω' : Type) [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω']
    (S : Set (HeightOneSpectrum (𝓞 F))) (S' : Set (HeightOneSpectrum (𝓞 F')))
    (φ : G F' Ω' →* G F Ω) (hφ : Continuous φ)
    (h : ∀ (v' : HeightOneSpectrum (𝓞 F')) (A' : ValuationSubring Ω'), IsPlaceOver A' v' →
      ∃ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v ∧ (v ∈ S ↔ v' ∈ S') ∧
        (∀ g ∈ Dec (F := F') A', φ g ∈ Dec (F := F) A) ∧
        ∀ g ∈ Ine (F := F') A', φ g ∈ Ine (F := F) A)
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (ρ : Representation R (G F Ω) M) :
    (∀ x ∈ ShaAbs ρ S, resH1 ρ φ hφ x ∈ ShaAbs (ρ.comp φ) S') ∧
      (Function.Surjective φ → Module.length R (ShaAbs ρ S) ≤ Module.length R (ShaAbs (ρ.comp φ) S')) := by
  have h1 : ∀ x ∈ ShaAbs ρ S, resH1 ρ φ hφ x ∈ ShaAbs (ρ.comp φ) S' := by
    intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨ha, hb⟩ := (mk_mem_ShaAbs ρ S z).1 hx
    refine (mk_mem_ShaAbs (ρ.comp φ) S' (restrictCocycles1 ρ φ hφ z)).2 ⟨?_, ?_⟩
    · intro v' hv' A' hA'
      obtain ⟨v, A, hA, hS, hD, -⟩ := h v' A' hA'
      obtain ⟨m, hm⟩ := ha v (hS.2 hv') A hA
      exact ⟨m, fun g hg => hm (φ g) (hD g hg)⟩
    · intro v' hv' A' hA'
      obtain ⟨v, A, hA, hS, -, hI⟩ := h v' A' hA'
      obtain ⟨m, hm⟩ := hb v (fun hv => hv' (hS.1 hv)) A hA
      exact ⟨m, fun g hg => hm (φ g) (hI g hg)⟩
  refine ⟨h1, fun hs => ?_⟩
  have hinj : Function.Injective (resH1 ρ φ hφ) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx' : (Submodule.Quotient.mk (restrictCocycles1 ρ φ hφ z) : H1 (ρ.comp φ)) = 0 := hx
    obtain ⟨m, hm⟩ := (mem_B1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hx')
    refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_B1 _ _).2 ⟨m, fun g => ?_⟩)
    obtain ⟨g', rfl⟩ := hs g
    exact hm g'
  refine length_mono_of_injective ((resH1 ρ φ hφ).restrict h1) fun x y hxy =>
    Subtype.ext (hinj (congrArg Subtype.val hxy))

/-! ### `ShaLenEqShaInv`, `VLenIndep`, `VFormula`, and Direct Wiring onto `realGaloisSelmerSystem` -/

section ShaLenEqShaInvSection

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime]

theorem map_Sha (D : LData F Ω l) (e : ℤ) :
    (Sha D e).map (resH1 (qzTw D e) (toGS Ω _) (continuous_toGS Ω _)) =
      ShaAbs ((qzTw D e).comp (toGS Ω _)) (Above F l) := by
  rw [← D.hS]
  exact shaInfl F Ω D.S D.A D.hA _ _ _

theorem injective_infl (D : LData F Ω l) (e : ℤ) :
    Function.Injective (resH1 (qzTw D e) (toGS Ω _) (continuous_toGS Ω _)) :=
  (infUnram (F := F) (Ω := Ω) (qzTw D e)).1

theorem shaLen_eq_abs (D : LData F Ω l) (e : ℤ) :
    shaLen D e = Module.length ℤ_[l] (ShaAbs (qzG F Ω l e) (Above F l)) := by
  rw [← qzTw_comp_toGS F Ω l D e, ← map_Sha]
  exact (Submodule.equivMapOfInjective _ (injective_infl D e) _).length_eq

variable {F' Ω' : Type} [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω']

theorem length_ShaAbs_le (f : F ≃+* F') (e : ℤ) :
    Module.length ℤ_[l] (ShaAbs (qzG F Ω l e) (Above F l)) ≤
      Module.length ℤ_[l] (ShaAbs (qzG F' Ω' l e) (Above F' l)) := by
  let σ : Ω ≃+* Ω' := IsAlgClosure.equivOfEquiv Ω Ω' f
  have hσ : ∀ x, σ (algebraMap F Ω x) = algebraMap F' Ω' (f.toRingHom x) :=
    fun x => IsAlgClosure.equivOfEquiv_algebraMap Ω Ω' f x
  obtain ⟨φ, h1, h2, h3, -, h5⟩ := galTransport F Ω F' Ω' f.toRingHom σ hσ
  have e1 : (qzG F Ω l e).comp φ = qzG F' Ω' l e := by
    refine MonoidHom.ext fun g => LinearMap.ext fun x => ?_
    rw [MonoidHom.comp_apply, qzG_apply, qzG_apply, h3]
  rw [← e1]
  refine (shaAbsRes F Ω F' Ω' _ _ φ h1 (fun v' A' hA' => ?_) _ _ _).2 (h5 f.surjective)
  obtain ⟨v, A, a, b, -, c, d⟩ := placeTransport F Ω F' Ω' f.toRingHom σ hσ φ h2 v' A' hA'
  exact ⟨v, A, a, b l, fun g hg => (c g).2 hg, fun g hg => (d g).2 hg⟩

theorem shaLen_congr (f : F ≃+* F') (D : LData F Ω l) (D' : LData F' Ω' l) (e : ℤ) :
    shaLen D e = shaLen D' e := by
  rw [shaLen_eq_abs, shaLen_eq_abs]
  exact le_antisymm (length_ShaAbs_le f e) (length_ShaAbs_le f.symm e)

/-- **`ShaLenEqShaInv`**: For every algebraic closure `Ω` and `D : LData F Ω l`,
`shaLen D e = shaInv F l e`. -/
theorem shaLen_eq_shaInv (D : LData F Ω l) (e : ℤ) : shaLen D e = shaInv F l e := by
  rw [shaLen_eq_abs]
  exact le_antisymm (length_ShaAbs_le (RingEquiv.refl F) e) (length_ShaAbs_le (RingEquiv.refl F) e)

theorem shaInv_congr (f : F ≃+* F') (e : ℤ) : shaInv F l e = shaInv F' l e :=
  le_antisymm (length_ShaAbs_le f e) (length_ShaAbs_le f.symm e)

/-- **`VLenIndep`**: `D.S = D'.S` and `VLen D e = VLen D' e` for any two `LData F Ω l`. -/
theorem vLenIndep (D D' : LData F Ω l) (e : ℤ) : D.S = D'.S ∧ VLen D e = VLen D' e := by
  have hS : D.S = D'.S := LData.S_eq D D'
  refine ⟨hS, ?_⟩
  obtain ⟨S, hS₁, A, hA, chi, hchi⟩ := D
  obtain ⟨S', hS₂, A', hA', chi', hchi'⟩ := D'
  dsimp only at hS
  subst hS
  have hc : chi = chi' := by
    refine MonoidHom.ext fun x => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    exact DFunLike.congr_fun (hchi.trans hchi'.symm) g
  subst hc
  rfl

/-- Full independence of `shaLen`, `VLen`, and `sumLocalH0TwistLength` on `LData`. -/
theorem indep (D D' : LData F Ω l) (e : ℤ) :
    shaLen D e = shaLen D' e ∧ VLen D e = VLen D' e ∧
      sumLocalH0TwistLength D e = sumLocalH0TwistLength D' e := by
  refine ⟨shaLen_congr (RingEquiv.refl F) D D' e, (vLenIndep D D' e).2, ?_⟩
  have hS := (vLenIndep D D' e).1
  rw [local_H0_length_eq_sum, local_H0_length_eq_sum]
  refine Fintype.sum_equiv (Equiv.subtypeEquivRight fun v => by rw [hS]) _ _ fun v => ?_
  rw [(imageConj v.1 _ _ (D.hA v) (D'.hA ⟨v.1, hS ▸ v.2⟩)).1]
  rfl

/-- Local `H²` product localization map `H²(G_{F, S_l}, ℤ_l(e+1)) → ∏_{v ∈ S_l} H²(D_v, ℤ_l(e+1))`. -/
def localH2 (D : LData F Ω l) (e : ℤ) :
    H2 (zlTw D (e + 1)) →ₗ[ℤ_[l]] ∀ v : D.S, H2 ((zlTw D (e + 1)).comp (locFam D.S D.A v)) :=
  LinearMap.pi fun v => resH2 (zlTw D (e + 1)) (locFam D.S D.A v) (continuous_locFam D.S D.A v)

/-- Poitou–Tate odd-prime / totally-complex condition. -/
def PTCase (F : Type) [Field F] [NumberField F] (l : ℕ) : Prop :=
  l ≠ 2 ∨ InfinitePlace.nrRealPlaces F = 0

theorem ptCase_of_isTotallyComplex (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
    (l : ℕ) : PTCase F l :=
  Or.inr (NumberField.nrRealPlaces_eq_zero_iff.2 inferInstance)

def PTCokerAt (D : LData F Ω l) (e : ℤ) : Prop :=
  PTCase F l →
    Module.length ℤ_[l] ((∀ v : D.S, H2 ((zlTw D (e + 1)).comp (locFam D.S D.A v))) ⧸
        LinearMap.range (localH2 D e)) =
      Module.length ℤ_[l] (H0 (qzTw D e))

def PTShaAt (D : LData F Ω l) (e : ℤ) : Prop :=
  PTCase F l → Module.length ℤ_[l] (Sha2Zl D e) = shaLen D e

def TateLocalDualityH2AtPlaces (D : LData F Ω l) (e : ℤ) : Prop :=
  ∀ v : D.S, Module.length ℤ_[l] (H2 ((zlTw D (e + 1)).comp (locFam D.S D.A v))) =
    Module.length ℤ_[l] (H0 ((qzTw D e).comp (locFam D.S D.A v)))

theorem length_add_coker {R X Y : Type*} [CommRing R] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (f : X →ₗ[R] Y) :
    Module.length R X + Module.length R (Y ⧸ LinearMap.range f) =
      Module.length R (LinearMap.ker f) + Module.length R Y := by
  have hX := Module.length_eq_add_of_exact (LinearMap.ker f).subtype (LinearMap.ker f).mkQ
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  have hY := Module.length_eq_add_of_exact (LinearMap.range f).subtype (LinearMap.range f).mkQ
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  rw [hX, hY, (f.quotKerEquivRange).length_eq, add_assoc]

/-- **`VFormula`**: Exact Poitou–Tate length balance
`VLen D e + len H⁰(G_{F,S_l}, (ℚ_l/ℤ_l)(-e)) = shaLen D e + ∑_{v ∈ S_l} len H⁰(D_v, (ℚ_l/ℤ_l)(-e))`. -/
theorem vFormula (D : LData F Ω l) (e : ℤ) (hcase : PTCase F l)
    (hcoker : PTCokerAt D e) (hsha : PTShaAt D e) (hloc : TateLocalDualityH2AtPlaces D e) :
    VLen D e + Module.length ℤ_[l] (H0 (qzTw D e)) = shaLen D e + sumLocalH0TwistLength D e := by
  have hker : LinearMap.ker (localH2 D e) = Sha2Zl D e := by
    unfold localH2
    rw [LinearMap.ker_pi]
    rfl
  have key := length_add_coker (localH2 D e)
  rw [hcoker hcase, hker, hsha hcase, Module.length_pi_of_fintype] at key
  unfold VLen sumLocalH0TwistLength
  rw [key]
  congr 1
  exact Finset.sum_congr rfl fun v _ => hloc v

theorem vFormula_nuGal (D : LData F Ω l) (e : ℤ) (hcase : PTCase F l)
    (hcoker : PTCokerAt D e) (hsha : PTShaAt D e) (hloc : TateLocalDualityH2AtPlaces D e) :
    VLen D e + nuGal l F e.natAbs = shaLen D e + sumLocalH0TwistLength D e := by
  rw [← length_H0_global_eq_nu D e]
  exact vFormula D e hcase hcoker hsha hloc

theorem VLen_le_shaLen_add (D : LData F Ω l) (e : ℤ) (hcase : PTCase F l)
    (hcoker : PTCokerAt D e) (hsha : PTShaAt D e) (hloc : TateLocalDualityH2AtPlaces D e) :
    VLen D e ≤ shaLen D e + sumLocalH0TwistLength D e := by
  rw [← vFormula_nuGal D e hcase hcoker hsha hloc]
  exact le_self_add

end ShaLenEqShaInvSection

/-! ### Direct Option-C Wiring onto `Stage12GaloisShaLen.Sha1Galois` & `realGaloisSelmerSystem` -/

section RealGaloisWiring

/-- `shaInv E p.1 e` agrees identically with `Stage12GaloisShaLen.galoisShaLen E p e`. -/
theorem shaInv_eq_galoisShaLen (E : Type) [Field E] [NumberField E] (p : Nat.Primes) (e : ℤ) :
    shaInv E p.1 e = galoisShaLen E p e :=
  (shaLen_eq_shaInv (canonicalLData E p) e).symm

/-- `shaInv E p.1 e` agrees identically with `realGaloisSelmerSystem.shaLen E p e`. -/
theorem shaInv_eq_realGaloisSelmerSystem (E : Type) [Field E] [NumberField E]
    (p : Nat.Primes) (e : ℕ) :
    shaInv E p.1 (e : ℤ) = realGaloisSelmerSystem.shaLen E p e :=
  shaInv_eq_galoisShaLen E p (e : ℤ)

/-- `galoisShaLen` is invariant under arbitrary ring isomorphisms `f : E ≃+* E'`. -/
theorem galoisShaLen_congr {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E']
    (f : E ≃+* E') (p : Nat.Primes) (e : ℤ) :
    galoisShaLen E p e = galoisShaLen E' p e := by
  rw [← shaInv_eq_galoisShaLen, ← shaInv_eq_galoisShaLen]
  exact shaInv_congr f e

/-- `realGaloisSelmerSystem.shaLen` is invariant under arbitrary field isomorphisms `f : E ≃+* E'`. -/
theorem realGaloisSelmerSystem_shaLen_congr {E E' : Type} [Field E] [NumberField E]
    [Field E'] [NumberField E'] (f : E ≃+* E') (p : Nat.Primes) (e : ℕ) :
    realGaloisSelmerSystem.shaLen E p e = realGaloisSelmerSystem.shaLen E' p e :=
  galoisShaLen_congr f p (e : ℤ)

/-- Exact characterization of `RHDirect.VVle realGaloisSelmerSystem` in terms of `shaInv`. -/
theorem vvle_realGalois_iff_shaInv (E : Type) [Field E] [NumberField E] (t : ℕ) (B : ℝ) :
    RHDirect.VVle realGaloisSelmerSystem E t B ↔
      (∀ (p : Nat.Primes) (e : ℕ), 0 < e → e < t → shaInv E p.1 (e : ℤ) ≠ ⊤) ∧
      ∀ S : Finset Nat.Primes, ∑ l ∈ S, Real.log (l : ℕ) *
        ∑ e ∈ Finset.Ico 1 t, ((shaInv E l.1 (e : ℤ)).toNat : ℝ) ≤ B := by
  simp only [RHDirect.VVle, shaInv_eq_realGaloisSelmerSystem]

/-- `RHDirect.VVle realGaloisSelmerSystem` is invariant under field isomorphisms `f : E ≃+* E'`. -/
theorem vvle_realGalois_congr {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E']
    (f : E ≃+* E') (t : ℕ) (B : ℝ) :
    RHDirect.VVle realGaloisSelmerSystem E t B ↔ RHDirect.VVle realGaloisSelmerSystem E' t B := by
  simp only [vvle_realGalois_iff_shaInv, shaInv_congr f]

end RealGaloisWiring

end ShaAbsAndInvariance

/-! ## Section 6: `GsTransport`, Galois Action on `H¹`, Equivariant Field-Iso Transport & CM Plus/Minus Splitting -/

section FieldIsoTransportAndCMParts

section GsTransportSection

private theorem transport_mem_NS {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {F' Ω' : Type} [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω']
    [IsAlgClosure F' Ω'] {l : ℕ} [Fact l.Prime] (f : F →+* F') (σ : Ω ≃+* Ω')
    (hσ : ∀ x, σ (algebraMap F Ω x) = algebraMap F' Ω' (f x)) (φ : G F' Ω' →* G F Ω)
    (h1 : Continuous φ) (h2 : ∀ g x, σ (φ g x) = g (σ x))
    {S : Set (HeightOneSpectrum (𝓞 F))} (hS : S = Above F l)
    {S' : Set (HeightOneSpectrum (𝓞 F'))} (hS' : S' = Above F' l) :
    NS Ω' S' ≤ (NS Ω S).comap φ := by
  have hN : (NS Ω S).Normal := normal_NS S
  have hclosed : IsClosed ((NS Ω S).comap φ : Set (G F' Ω')) := (isClosed_NS Ω S).preimage h1
  haveI : ((NS Ω S).comap φ).Normal := hN.comap φ
  apply Subgroup.topologicalClosure_minimal _ _ hclosed
  apply Subgroup.normalClosure_le_normal
  intro g hg
  simp only [Set.mem_iUnion, Set.mem_compl_iff, Set.mem_ofPred_eq] at hg
  obtain ⟨v', hv', A', hA', hgA⟩ := hg
  obtain ⟨v, A, hA, habove, -, -, hine⟩ := placeTransport F Ω F' Ω' f σ hσ φ h2 v' A' hA'
  have hgi : φ g ∈ Ine (F := F) A := (hine g).2 hgA
  show φ g ∈ NS Ω S
  apply Subgroup.le_topologicalClosure
  apply Subgroup.subset_normalClosure
  simp only [Set.mem_iUnion, Set.mem_compl_iff, Set.mem_ofPred_eq]
  refine ⟨v, ?_, A, hA, hgi⟩
  rw [hS]
  rw [hS'] at hv'
  exact fun h => hv' ((habove l).1 h)

/-- **`GsTransport`**: Field isomorphism `f : F ≃+* F'` lifted to `σ : Ω ≃+* Ω'` induces
topological group isomorphisms `G F' Ω' ≃* G F Ω` and `GS Ω' S' ≃* GS Ω S` commuting with
`toGS` and the cyclotomic character `chi`. -/
theorem gsTransport (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (F' Ω' : Type) [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω']
    [IsAlgClosure F' Ω'] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (D' : LData F' Ω' l)
    (f : F ≃+* F') (σ : Ω ≃+* Ω') (hσ : ∀ x, σ (algebraMap F Ω x) = algebraMap F' Ω' (f x)) :
    ∃ (φ : G F' Ω' ≃* G F Ω)
      (ψ : GS Ω' (D'.S : Set (HeightOneSpectrum (𝓞 F'))) ≃*
        GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))),
      Continuous φ ∧ Continuous φ.symm ∧ Continuous ψ ∧ Continuous ψ.symm ∧
      (∀ g x, σ (φ g x) = g (σ x)) ∧
      (∀ g, ψ (toGS Ω' _ g) = toGS Ω _ (φ g)) ∧
      ∀ g, D.chi (ψ g) = D'.chi g := by
  obtain ⟨φ, hφc, hφact, hφcyc, -, -⟩ := galTransport F Ω F' Ω' (f : F →+* F') σ hσ
  have hσ' : ∀ x : F', σ.symm (algebraMap F' Ω' x) = algebraMap F Ω ((f.symm : F' →+* F) x) := by
    intro x
    apply σ.injective
    rw [RingEquiv.apply_symm_apply, hσ]
    simp
  obtain ⟨φ', hφ'c, hφ'act, -, -, -⟩ := galTransport F' Ω' F Ω (f.symm : F' →+* F) σ.symm hσ'
  have hleft : ∀ g, φ' (φ g) = g := fun g => AlgEquiv.ext fun y => by
    apply σ.symm.injective
    rw [hφ'act]
    apply σ.injective
    rw [hφact, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  have hright : ∀ g, φ (φ' g) = g := fun g => AlgEquiv.ext fun x => by
    apply σ.injective
    rw [hφact]
    apply σ.symm.injective
    rw [hφ'act, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
  let Φ : G F' Ω' ≃* G F Ω :=
    { toFun := φ, invFun := φ', left_inv := hleft, right_inv := hright, map_mul' := φ.map_mul }
  have hmap : (NS Ω' (D'.S : Set (HeightOneSpectrum (𝓞 F')))).map (Φ : G F' Ω' →* G F Ω) =
      NS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      exact transport_mem_NS (f : F →+* F') σ hσ φ hφc hφact D.hS D'.hS
    · intro h hh
      exact ⟨φ' h, transport_mem_NS (f.symm : F' →+* F) σ.symm hσ' φ' hφ'c hφ'act D'.hS D.hS hh,
        hright h⟩
  let Ψ : GS Ω' (D'.S : Set (HeightOneSpectrum (𝓞 F'))) ≃*
      GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) :=
    QuotientGroup.congr _ _ Φ hmap
  have hΨmk : ∀ g : G F' Ω', Ψ (QuotientGroup.mk g) = QuotientGroup.mk (φ g) :=
    fun g => QuotientGroup.congr_mk _ _ Φ hmap g
  have hΨsmk : ∀ g : G F Ω, Ψ.symm (QuotientGroup.mk g) = QuotientGroup.mk (φ' g) := fun g => by
    apply Ψ.injective
    rw [MulEquiv.apply_symm_apply, hΨmk, hright]
  have hΨc : Continuous Ψ := by
    rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
    have : (Ψ ∘ QuotientGroup.mk) = (QuotientGroup.mk ∘ φ) := funext hΨmk
    rw [this]
    exact QuotientGroup.continuous_mk.comp hφc
  have hΨsc : Continuous Ψ.symm := by
    rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
    have : (Ψ.symm ∘ QuotientGroup.mk) = (QuotientGroup.mk ∘ φ') := funext hΨsmk
    rw [this]
    exact QuotientGroup.continuous_mk.comp hφ'c
  refine ⟨Φ, Ψ, hφc, hφ'c, hΨc, hΨsc, hφact, fun g => hΨmk g, ?_⟩
  intro g
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective g
  rw [hΨmk]
  show D.chi (toGS Ω _ (φ h)) = D'.chi (toGS Ω' _ h)
  have e1 : D.chi (toGS Ω _ (φ h)) = cycZ F Ω l (φ h) := DFunLike.congr_fun D.hchi (φ h)
  have e2 : D'.chi (toGS Ω' _ h) = cycZ F' Ω' l h := DFunLike.congr_fun D'.hchi h
  exact e1.trans ((hφcyc l h).trans e2.symm)

end GsTransportSection

section GaloisActionOnH1

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

/-- `σ : Ω ≃+* Ω` lifts `τ : F ≃+* F`. -/
def IsLift (τ : F ≃+* F) (σ : Ω ≃+* Ω) : Prop :=
  ∀ x, σ (algebraMap F Ω x) = algebraMap F Ω (τ x)

variable {τ : F ≃+* F} {σ : Ω ≃+* Ω}

omit [NumberField F] in
theorem IsLift.symm (h : IsLift τ σ) : IsLift τ.symm σ.symm := fun x => by
  rw [RingEquiv.symm_apply_eq, h, RingEquiv.apply_symm_apply]

omit [NumberField F] in
theorem IsLift.trans {τ' : F ≃+* F} {σ' : Ω ≃+* Ω} (h : IsLift τ σ) (h' : IsLift τ' σ') :
    IsLift (τ.trans τ') (σ.trans σ') := fun x => by
  rw [RingEquiv.trans_apply, h, h', RingEquiv.trans_apply]

omit [NumberField F] in
theorem exists_isLift [IsAlgClosure F Ω] (τ : F ≃+* F) : ∃ σ : Ω ≃+* Ω, IsLift τ σ :=
  ⟨IsAlgClosure.equivOfEquiv Ω Ω τ, fun x => IsAlgClosure.equivOfEquiv_algebraMap Ω Ω τ x⟩

/-- Conjugation action `g ↦ σ⁻¹ ∘ g ∘ σ` on `G F Ω` induced by a lift `σ` of `τ`. -/
def conjGal (h : IsLift τ σ) : G F Ω →* G F Ω where
  toFun g := AlgEquiv.ofRingEquiv (f := (σ.trans g.toRingEquiv).trans σ.symm) fun x => by
    show σ.symm (g (σ (algebraMap F Ω x))) = _
    rw [h, AlgEquiv.commutes, ← h, RingEquiv.symm_apply_apply]
  map_one' := AlgEquiv.ext fun x => σ.symm_apply_apply x
  map_mul' g k := AlgEquiv.ext fun x => by
    show σ.symm (g (k (σ x))) = σ.symm (g (σ (σ.symm (k (σ x)))))
    rw [RingEquiv.apply_symm_apply]

omit [NumberField F] in
theorem conjGal_apply (h : IsLift τ σ) (g : G F Ω) (x : Ω) : conjGal h g x = σ.symm (g (σ x)) := rfl

omit [NumberField F] in
theorem apply_conjGal (h : IsLift τ σ) (g : G F Ω) (x : Ω) : σ (conjGal h g x) = g (σ x) :=
  σ.apply_symm_apply _

theorem continuous_conjGal [IsAlgClosure F Ω] (h : IsLift τ σ) : Continuous (conjGal h) := by
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsIntegral F Ω := Algebra.IsAlgebraic.isIntegral
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨E, hE, hs⟩ := (krullTopology_mem_nhds_one_iff F Ω s).1 hs
  let b := Module.finBasis F E
  have ho : IsOpen (⋂ i, {g : G F Ω | g (σ (b i)) = σ (b i)}) :=
    isOpen_iInter_of_finite fun i => isOpen_setOf_apply (F := F) (σ (b i)) (fun t => t = σ (b i))
  rw [Filter.mem_map]
  refine Filter.mem_of_superset (ho.mem_nhds (Set.mem_iInter.2 fun _ => rfl)) fun g hg => hs ?_
  have h1 : ∀ i, conjGal h g (b i) = b i := fun i =>
    σ.injective (by rw [apply_conjGal]; exact Set.mem_iInter.1 hg i)
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have e : (conjGal h g).toLinearMap ∘ₗ E.val.toLinearMap = E.val.toLinearMap := b.ext h1
  exact LinearMap.congr_fun e ⟨x, hx⟩

private theorem lift_val_lt_one {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A) (x : Ω) :
    A'.valuation (σ x) < 1 ↔ A.valuation x < 1 := by
  rw [valuation_lt_one_iff' (Ω := Ω), valuation_lt_one_iff' (Ω := Ω), hA, ← map_inv₀, hA,
    map_eq_zero_iff _ σ.injective]

theorem conjGal_mem_Dec (h : IsLift τ σ) {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A)
    {g : G F Ω} (hg : g ∈ Dec (F := F) A') : conjGal h g ∈ Dec (F := F) A := by
  rw [mem_Dec]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, AlgEquiv.smul_def, ← hA,
    ← hA, apply_conjGal]
  exact apply_mem_iff_of_mem_Dec ((Dec (F := F) A').inv_mem hg) _

theorem conjGal_mem_Ine (h : IsLift τ σ) {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A)
    {g : G F Ω} (hg : g ∈ Ine (F := F) A') : conjGal h g ∈ Ine (F := F) A := by
  refine ⟨conjGal_mem_Dec h hA hg.1, fun x hx => ?_⟩
  rw [← lift_val_lt_one hA, map_sub, apply_conjGal]
  exact hg.2 _ ((A'.valuation_le_one_iff _).2 ((hA x).2 ((A.valuation_le_one_iff _).1 hx)))

/-- Pullback of a prime of `𝓞 F` along `τ : F ≃+* F`. -/
def preplace (τ : F ≃+* F) (v : HeightOneSpectrum (𝓞 F)) : HeightOneSpectrum (𝓞 F) :=
  (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv τ)).symm v

omit [NumberField F] in
theorem mem_preplace (τ : F ≃+* F) (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) :
    x ∈ (preplace τ v).asIdeal ↔ RingOfIntegers.mapRingEquiv τ x ∈ v.asIdeal := Iff.rfl

theorem isPlaceOver_preplace (h : IsLift τ σ) {A A' : ValuationSubring Ω}
    (hA : ∀ x, σ x ∈ A' ↔ x ∈ A) {v : HeightOneSpectrum (𝓞 F)} (hv : IsPlaceOver A' v) :
    IsPlaceOver A (preplace τ v) := fun x => by
  rw [mem_preplace, ← hv, ← lift_val_lt_one hA, h]; rfl

omit [NumberField F] in
theorem preplace_mem_Above (τ : F ≃+* F) (l : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    preplace τ v ∈ Above F l ↔ v ∈ Above F l := by
  show ((l : ℕ) : 𝓞 F) ∈ (preplace τ v).asIdeal ↔ ((l : ℕ) : 𝓞 F) ∈ v.asIdeal
  rw [mem_preplace, map_natCast]

variable [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]

theorem conjGal_mem_NS (h : IsLift τ σ) {S : Set (HeightOneSpectrum (𝓞 F))} (hS : S = Above F l)
    {g : G F Ω} (hg : g ∈ NS Ω S) : conjGal h g ∈ NS Ω S := by
  have hc : IsClosed (((NS Ω S).comap (conjGal h) : Subgroup (G F Ω)) : Set (G F Ω)) :=
    (isClosed_NS Ω S).preimage (continuous_conjGal h)
  refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) hc hg
  intro k hk
  simp only [Set.mem_iUnion, Set.mem_compl_iff, Set.mem_ofPred_eq] at hk
  obtain ⟨v, hv, A', hA', hk⟩ := hk
  have hA : ∀ x, σ x ∈ A' ↔ x ∈ A'.comap σ.toRingHom := fun _ => Iff.rfl
  show conjGal h k ∈ NS Ω S
  apply Subgroup.le_topologicalClosure
  apply Subgroup.subset_normalClosure
  simp only [Set.mem_iUnion, Set.mem_compl_iff, Set.mem_ofPred_eq]
  refine ⟨preplace τ v, ?_, A'.comap σ.toRingHom, isPlaceOver_preplace h hA hA',
    conjGal_mem_Ine h hA hk⟩
  subst hS
  exact fun hh => hv ((preplace_mem_Above τ l v).1 hh)

def conjGS (D : LData F Ω l) (h : IsLift τ σ) :
    GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) →* GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) :=
  QuotientGroup.map _ _ (conjGal h) fun _ hg => conjGal_mem_NS h D.hS hg

theorem conjGS_toGS (D : LData F Ω l) (h : IsLift τ σ) (g : G F Ω) :
    conjGS D h (toGS Ω _ g) = toGS Ω _ (conjGal h g) := rfl

theorem continuous_conjGS (D : LData F Ω l) (h : IsLift τ σ) : Continuous (conjGS D h) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ((continuous_toGS Ω _).comp (continuous_conjGal h))

theorem chi_toGS (D : LData F Ω l) (g : G F Ω) :
    D.chi (toGS Ω _ g) = cyclotomicCharacter Ω l g.toRingEquiv :=
  DFunLike.congr_fun D.hchi g

theorem chi_conjGS (D : LData F Ω l) (h : IsLift τ σ)
    (g : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F)))) : D.chi (conjGS D h g) = D.chi g := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ g
  refine (chi_toGS D (conjGal h g)).trans (Eq.trans ?_ (chi_toGS D g).symm)
  have e : (conjGal h g).toRingEquiv = σ⁻¹ * g.toRingEquiv * σ := rfl
  rw [e, map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]

variable (l) in
def twScal (σ : Ω ≃+* Ω) (e : ℤ) : ℤ_[l] := ((cyclotomicCharacter Ω l σ ^ (-e) : ℤ_[l]ˣ) : ℤ_[l])

theorem qzTw_apply (D : LData F Ω l) (e : ℤ) (g : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))))
    (m : QZ l) : qzTw D e g m = ((D.chi g ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • m := rfl

def h1TwistConjByLift (D : LData F Ω l) (e : ℤ) (h : IsLift τ σ) :
    H1 (qzTw D e) →ₗ[ℤ_[l]] H1 (qzTw D e) :=
  (mapH1 ((qzTw D e).comp (conjGS D h)) (qzTw D e) (twScal l σ e • LinearMap.id)
    continuous_of_discreteTopology (fun g m => by
      show twScal l σ e • qzTw D e (conjGS D h g) m = qzTw D e g (twScal l σ e • m)
      rw [qzTw_apply, qzTw_apply, chi_conjGS, smul_comm])).comp
    (resH1 (qzTw D e) (conjGS D h) (continuous_conjGS D h))

theorem exists_cocycle_h1TwistConjByLift_mk_eq_mk (D : LData F Ω l) (e : ℤ) (h : IsLift τ σ)
    (z : Z1 (qzTw D e)) :
    ∃ z' : Z1 (qzTw D e), h1TwistConjByLift D e h (Submodule.Quotient.mk z) = Submodule.Quotient.mk z' ∧
      ∀ g, z'.1 g = twScal l σ e • z.1 (conjGS D h g) :=
  ⟨_, rfl, fun _ => rfl⟩

theorem h1TwistConjByLift_mul_apply (D : LData F Ω l) (e : ℤ) {τ₁ τ₂ τ₃ : F ≃+* F}
    {σ₁ σ₂ σ₃ : Ω ≃+* Ω} (h₁ : IsLift τ₁ σ₁) (h₂ : IsLift τ₂ σ₂) (h₃ : IsLift τ₃ σ₃)
    (hσ : σ₃ = σ₂ * σ₁) (x : H1 (qzTw D e)) :
    h1TwistConjByLift D e h₃ x = h1TwistConjByLift D e h₂ (h1TwistConjByLift D e h₁ x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z₁, e₁, f₁⟩ := exists_cocycle_h1TwistConjByLift_mk_eq_mk D e h₁ z
  obtain ⟨z₂, e₂, f₂⟩ := exists_cocycle_h1TwistConjByLift_mk_eq_mk D e h₂ z₁
  obtain ⟨z₃, e₃, f₃⟩ := exists_cocycle_h1TwistConjByLift_mk_eq_mk D e h₃ z
  rw [e₁, e₂, e₃]
  congr 1
  refine Subtype.ext (funext fun g => ?_)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ g
  have e4 : conjGS D h₃ (toGS Ω _ g) = conjGS D h₁ (conjGS D h₂ (toGS Ω _ g)) := by
    rw [conjGS_toGS, conjGS_toGS, conjGS_toGS]
    congr 1; subst hσ; rfl
  refine (f₃ _).trans (Eq.trans ?_ (f₂ _).symm)
  rw [f₁, smul_smul]
  refine congrArg₂ (· • ·) ?_ (congrArg z.1 e4)
  rw [twScal, twScal, twScal, hσ, map_mul, mul_zpow, Units.val_mul]

theorem h1TwistConjByLift_eq_self_of_forall_apply_eq (D : LData F Ω l) (e : ℤ) (h : IsLift τ σ)
    (hτ : ∀ x, τ x = x) (x : H1 (qzTw D e)) : h1TwistConjByLift D e h x = x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z₁, e₁, f₁⟩ := exists_cocycle_h1TwistConjByLift_mk_eq_mk D e h z
  let g₀ : G F Ω := AlgEquiv.ofRingEquiv (f := σ) fun x => by rw [h, hτ]
  rw [e₁, Submodule.Quotient.eq]
  refine (mem_B1 _ _).2 ⟨z.1 (toGS Ω _ g₀), fun g => ?_⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ g
  have hc := z.2.2
  have e1 : toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) g₀ * conjGS D h (toGS Ω _ g) =
      toGS Ω _ g * toGS Ω _ g₀ := by
    rw [conjGS_toGS, ← map_mul, ← map_mul]
    congr 1
    exact AlgEquiv.ext fun x => apply_conjGal h g x
  have e2 := congrArg z.1 e1
  rw [hc, hc, qzTw_apply, chi_toGS] at e2
  have e3 : z₁.1 (toGS Ω _ g) =
      z.1 (toGS Ω _ g) + qzTw D e (toGS Ω _ g) (z.1 (toGS Ω _ g₀)) - z.1 (toGS Ω _ g₀) := by
    rw [f₁, ← e2, add_sub_cancel_left]; rfl
  show z₁.1 (toGS Ω _ g) - z.1 (toGS Ω _ g) =
    qzTw D e (toGS Ω _ g) (z.1 (toGS Ω _ g₀)) - z.1 (toGS Ω _ g₀)
  rw [e3]; abel

theorem h1TwistConjByLift_eq_of_isLift_of_isLift (D : LData F Ω l) (e : ℤ) {σ' : Ω ≃+* Ω}
    (h : IsLift τ σ) (h' : IsLift τ σ') : h1TwistConjByLift D e h = h1TwistConjByLift D e h' :=
  LinearMap.ext fun x => by
    rw [h1TwistConjByLift_mul_apply D e (h.trans h'.symm) h' h
        (RingEquiv.ext fun _ => (σ'.apply_symm_apply _).symm),
      h1TwistConjByLift_eq_self_of_forall_apply_eq D e (h.trans h'.symm)
        fun y => τ.symm_apply_apply y]

theorem h1TwistConjByLift_mem_sha_of_mem_sha (D : LData F Ω l) (e : ℤ) (h : IsLift τ σ)
    {x : H1 (qzTw D e)} (hx : x ∈ Sha D e) : h1TwistConjByLift D e h x ∈ Sha D e := by
  rw [Sha, mem_Sha1] at hx ⊢
  intro v
  have hw : preplace τ v.1 ∈ D.S := by
    rw [← Finset.mem_coe, D.hS, preplace_mem_Above, ← D.hS]; exact v.2
  let w : D.S := ⟨_, hw⟩
  have hA : ∀ x, σ x ∈ D.A v ↔ x ∈ (D.A v).comap σ.toRingHom := fun _ => Iff.rfl
  obtain ⟨g₀, hg₀⟩ := exists_smul_eq_of_isPlaceOver (F := F) (D.hA w) (isPlaceOver_preplace h hA (D.hA v))
  have h' : IsLift τ (g₀.toRingEquiv.trans σ) := fun y => by
    rw [RingEquiv.trans_apply, ← h]; exact congrArg σ (g₀.commutes y)
  have hA' : ∀ x, (g₀.toRingEquiv.trans σ) x ∈ D.A v ↔ x ∈ D.A w := fun x =>
    (hA (g₀ x)).trans (by rw [← hg₀, ← AlgEquiv.smul_def]; exact ValuationSubring.smul_mem_pointwise_smul_iff)
  rw [h1TwistConjByLift_eq_of_isLift_of_isLift D e h h']
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z₁, e₁, f₁⟩ := exists_cocycle_h1TwistConjByLift_mk_eq_mk D e h' z
  obtain ⟨m, hm⟩ := (mem_B1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 (hx w))
  rw [e₁]
  refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_B1 _ _).2 ⟨twScal l (g₀.toRingEquiv.trans σ) e • m, fun g => ?_⟩)
  change z₁.1 (toGS Ω _ g.1) = _
  rw [f₁, conjGS_toGS]
  have hmw := hm ⟨_, conjGal_mem_Dec h' hA' g.2⟩
  change z.1 (toGS Ω _ (conjGal h' g.1)) = qzTw D e (toGS Ω _ (conjGal h' g.1)) m - m at hmw
  rw [hmw, ← conjGS_toGS D h', qzTw_apply, chi_conjGS, smul_sub, smul_comm]
  rfl

/-- Canonical action of `Aut(F)` on `H¹(G_{F,S_l}, (ℚ_l/ℤ_l)(-e))`, independent of the chosen lift to `Ω`. -/
def galoisActionOnCohomology (D : LData F Ω l) (e : ℤ) (τ : F ≃+* F) :
    Module.End ℤ_[l] (H1 (qzTw D e)) :=
  h1TwistConjByLift D e (exists_isLift (Ω := Ω) τ).choose_spec

theorem galois_action_cohomology_eq_conj (D : LData F Ω l) (e : ℤ) (h : IsLift τ σ) :
    galoisActionOnCohomology D e τ = h1TwistConjByLift D e h :=
  h1TwistConjByLift_eq_of_isLift_of_isLift D e _ h

theorem galois_action_cohomology_one (D : LData F Ω l) (e : ℤ) :
    galoisActionOnCohomology D e (1 : F ≃+* F) = 1 :=
  LinearMap.ext fun x => h1TwistConjByLift_eq_self_of_forall_apply_eq D e _ (fun _ => rfl) x

theorem galois_action_cohomology_mul (D : LData F Ω l) (e : ℤ) (τ₁ τ₂ : F ≃+* F) :
    galoisActionOnCohomology D e (τ₁ * τ₂) =
      galoisActionOnCohomology D e τ₁ * galoisActionOnCohomology D e τ₂ := by
  obtain ⟨σ₁, h₁⟩ := exists_isLift (Ω := Ω) τ₁
  obtain ⟨σ₂, h₂⟩ := exists_isLift (Ω := Ω) τ₂
  rw [galois_action_cohomology_eq_conj D e h₁, galois_action_cohomology_eq_conj D e h₂,
    galois_action_cohomology_eq_conj D e (τ := τ₁ * τ₂) (h₂.trans h₁)]
  exact LinearMap.ext fun x => h1TwistConjByLift_mul_apply D e h₂ h₁ _ rfl x

theorem galois_action_preserves_sha (D : LData F Ω l) (e : ℤ) (τ : F ≃+* F) {x : H1 (qzTw D e)}
    (hx : x ∈ Sha D e) : galoisActionOnCohomology D e τ x ∈ Sha D e :=
  h1TwistConjByLift_mem_sha_of_mem_sha D e _ hx

end GaloisActionOnH1

section H1TransportFieldIso

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {F' Ω' : Type} [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω']
  {l : ℕ} [Fact l.Prime]

theorem mem_sha_iff_res_mem_absolute_sha (D : LData F Ω l) (e : ℤ) (x : H1 (qzTw D e)) :
    x ∈ Sha D e ↔ resH1 (qzTw D e) (toGS Ω _) (continuous_toGS Ω _) x ∈
      ShaAbs ((qzTw D e).comp (toGS Ω _)) (Above F l) := by
  constructor
  · intro hx
    rw [← map_Sha D e]
    exact Submodule.mem_map_of_mem hx
  · intro hx
    rw [← map_Sha D e] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rwa [← injective_infl D e hyx]

private theorem pairH1_qzTw_mem_sha (D : LData F Ω l) (D' : LData F' Ω' l) (e : ℤ) (f : F →+* F')
    (σ : Ω ≃+* Ω') (hσ : ∀ x, σ (algebraMap F Ω x) = algebraMap F' Ω' (f x))
    (φ : G F' Ω' →* G F Ω) (hφ : ∀ g x, σ (φ g x) = g (σ x))
    (ψ : GS Ω' (D'.S : Set (HeightOneSpectrum (𝓞 F'))) →*
      GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))))
    (hψ : Continuous ψ) (hc : ∀ g, ψ (toGS Ω' _ g) = toGS Ω _ (φ g))
    (hq : ∀ g m, (LinearMap.id : QZ l →ₗ[ℤ_[l]] QZ l) (qzTw D e (ψ g) m) =
      qzTw D' e g (LinearMap.id (R := ℤ_[l]) m))
    (x : H1 (qzTw D e)) (hx : x ∈ Sha D e) :
    pairH1 (qzTw D e) (qzTw D' e) ψ hψ LinearMap.id continuous_id hq x ∈ Sha D' e := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [mem_sha_iff_res_mem_absolute_sha] at hx ⊢
  simp only [resH1, pairH1, Submodule.mapQ_apply] at hx ⊢
  rw [mk_mem_ShaAbs] at hx ⊢
  obtain ⟨hxa, hxb⟩ := hx
  constructor
  · intro v' hv' A' hA'
    obtain ⟨v, A, hA, hab, -, hdec, -⟩ := placeTransport F Ω F' Ω' f σ hσ φ hφ v' A' hA'
    obtain ⟨m, hm⟩ := hxa v ((hab l).2 hv') A hA
    refine ⟨m, fun g hg => ?_⟩
    have h1 := hm (φ g) ((hdec g).2 hg)
    have h2 := hq (toGS Ω' (D'.S : Set (HeightOneSpectrum (𝓞 F'))) g) m
    simp only [LinearMap.id_apply] at h2
    change (z : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) → QZ l) (toGS Ω _ (φ g)) =
      qzTw D e (toGS Ω _ (φ g)) m - m at h1
    change LinearMap.id ((z : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) → QZ l)
        (ψ (toGS Ω' _ g))) = qzTw D' e (toGS Ω' _ g) m - m
    rw [LinearMap.id_apply, hc, h1, ← hc, h2]
  · intro v' hv' A' hA'
    obtain ⟨v, A, hA, hab, -, -, hine⟩ := placeTransport F Ω F' Ω' f σ hσ φ hφ v' A' hA'
    obtain ⟨m, hm⟩ := hxb v (fun h => hv' ((hab l).1 h)) A hA
    refine ⟨m, fun g hg => ?_⟩
    have h1 := hm (φ g) ((hine g).2 hg)
    have h2 := hq (toGS Ω' (D'.S : Set (HeightOneSpectrum (𝓞 F'))) g) m
    simp only [LinearMap.id_apply] at h2
    change (z : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) → QZ l) (toGS Ω _ (φ g)) =
      qzTw D e (toGS Ω _ (φ g)) m - m at h1
    change LinearMap.id ((z : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) → QZ l)
        (ψ (toGS Ω' _ g))) = qzTw D' e (toGS Ω' _ g) m - m
    rw [LinearMap.id_apply, hc, h1, ← hc, h2]

/-- **`H1_transport_field_iso`**: Any field isomorphism `f : F ≃+* F'` induces a `ℤ_[l]`-linear
isomorphism `Φ : H¹(G_{F,S_l}, (ℚ_l/ℤ_l)(-e)) ≃ₗ H¹(G_{F',S_l}, (ℚ_l/ℤ_l)(-e))` mapping `Sha D e`
onto `Sha D' e` and equivariant for `galoisActionOnCohomology`. -/
theorem H1_transport_field_iso (D : LData F Ω l) (D' : LData F' Ω' l) (f : F ≃+* F') (e : ℤ) :
    ∃ Φ : H1 (qzTw D e) ≃ₗ[ℤ_[l]] H1 (qzTw D' e),
      (Sha D e).map Φ.toLinearMap = Sha D' e ∧
      ∀ (τ : F ≃+* F) (τ' : F' ≃+* F'), (∀ x, f (τ x) = τ' (f x)) →
        ∀ x, Φ (galoisActionOnCohomology D e τ x) = galoisActionOnCohomology D' e τ' (Φ x) := by
  let σ : Ω ≃+* Ω' := IsAlgClosure.equivOfEquiv Ω Ω' f
  have hσ : ∀ x, σ (algebraMap F Ω x) = algebraMap F' Ω' (f x) :=
    fun x => IsAlgClosure.equivOfEquiv_algebraMap Ω Ω' f x
  obtain ⟨φ, ψ, -, -, hψ, hψs, hφ, hc, hchi⟩ := gsTransport F Ω F' Ω' l D D' f σ hσ
  have hq : ∀ g m, (LinearMap.id : QZ l →ₗ[ℤ_[l]] QZ l) (qzTw D e (ψ g) m) =
      qzTw D' e g (LinearMap.id (R := ℤ_[l]) m) := fun g m => by
    simp only [LinearMap.id_apply, qzTw_apply, hchi]
  have hq' : ∀ g m, (LinearMap.id : QZ l →ₗ[ℤ_[l]] QZ l) (qzTw D' e (ψ.symm g) m) =
      qzTw D e g (LinearMap.id (R := ℤ_[l]) m) := fun g m => by
    simp only [LinearMap.id_apply, qzTw_apply, ← hchi, MulEquiv.apply_symm_apply]
  let Φ := pairH1 (qzTw D e) (qzTw D' e) ψ.toMonoidHom hψ LinearMap.id continuous_id hq
  let Ψ := pairH1 (qzTw D' e) (qzTw D e) ψ.symm.toMonoidHom hψs LinearMap.id continuous_id hq'
  have hΦΨ : Φ.comp Ψ = LinearMap.id := by
    apply Submodule.linearMap_qext
    ext z
    simp [Φ, Ψ, pairH1, compatiblePairCocycles1]
  have hΨΦ : Ψ.comp Φ = LinearMap.id := by
    apply Submodule.linearMap_qext
    ext z
    simp [Φ, Ψ, pairH1, compatiblePairCocycles1]
  have hσ' : ∀ x, σ.symm (algebraMap F' Ω' x) = algebraMap F Ω (f.symm x) := fun x => by
    rw [RingEquiv.symm_apply_eq, hσ, RingEquiv.apply_symm_apply]
  have hφ' : ∀ g x, σ.symm (φ.symm g x) = g (σ.symm x) := fun g x => by
    have h := hφ (φ.symm g) (σ.symm x)
    rw [MulEquiv.apply_symm_apply, RingEquiv.apply_symm_apply] at h
    rw [← h, RingEquiv.symm_apply_apply]
  have hc' : ∀ g, ψ.symm (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) g) =
      toGS Ω' (D'.S : Set (HeightOneSpectrum (𝓞 F'))) (φ.symm g) := fun g => by
    rw [MulEquiv.symm_apply_eq, hc, MulEquiv.apply_symm_apply]
  refine ⟨LinearEquiv.ofLinearMap Φ Ψ hΦΨ hΨΦ, ?_, ?_⟩
  · apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact pairH1_qzTw_mem_sha D D' e f.toRingHom σ hσ φ.toMonoidHom hφ _ hψ (fun g => hc g) hq x hx
    · intro y hy
      exact ⟨Ψ y, pairH1_qzTw_mem_sha D' D e f.symm.toRingHom σ.symm hσ' φ.symm.toMonoidHom hφ' _
        hψs (fun g => hc' g) hq' y hy, LinearMap.congr_fun hΦΨ y⟩
  · intro τ τ' hτ x
    obtain ⟨σ1, h1⟩ := exists_isLift (Ω := Ω) τ
    let σ1' : Ω' ≃+* Ω' := σ.symm.trans (σ1.trans σ)
    have h1' : IsLift τ' σ1' := fun y => by
      obtain ⟨y0, rfl⟩ := f.surjective y
      show σ (σ1 (σ.symm (algebraMap F' Ω' (f y0)))) = algebraMap F' Ω' (τ' (f y0))
      rw [← hσ, RingEquiv.symm_apply_apply, h1, hσ, hτ]
    rw [galois_action_cohomology_eq_conj D e h1, galois_action_cohomology_eq_conj D' e h1']
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨z1, hz1, hz1v⟩ := exists_cocycle_h1TwistConjByLift_mk_eq_mk D e h1 z
    simp only [LinearEquiv.coe_ofLinearMap]
    rw [hz1]
    have hΦmk : ∀ w, Φ (Submodule.Quotient.mk w) =
        Submodule.Quotient.mk (compatiblePairCocycles1 (qzTw D e) (qzTw D' e) ψ.toMonoidHom hψ
          LinearMap.id continuous_id hq w) :=
      fun _ => rfl
    rw [hΦmk, hΦmk]
    obtain ⟨z2, hz2, hz2v⟩ := exists_cocycle_h1TwistConjByLift_mk_eq_mk D' e h1'
      (compatiblePairCocycles1 (qzTw D e) (qzTw D' e) ψ.toMonoidHom hψ LinearMap.id continuous_id hq z)
    rw [hz2]
    congr 1
    apply Subtype.ext
    funext g'
    rw [hz2v]
    show LinearMap.id ((z1 : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) → QZ l) (ψ g')) =
      twScal l σ1' e • LinearMap.id ((z : GS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) → QZ l)
        (ψ (conjGS D' h1' g')))
    rw [LinearMap.id_apply, LinearMap.id_apply, hz1v]
    have htw : twScal l σ1' e = twScal l σ1 e := by
      unfold twScal
      rw [cyclotomicCharacter_conj l σ σ1 σ1' fun x => by simp [σ1']]
    have hconj : conjGS D h1 (ψ g') = ψ (conjGS D' h1' g') := by
      obtain ⟨g0, rfl⟩ := QuotientGroup.mk'_surjective _ g'
      change conjGS D h1 (ψ (toGS Ω' _ g0)) = ψ (conjGS D' h1' (toGS Ω' _ g0))
      rw [hc, conjGS_toGS, conjGS_toGS, hc]
      congr 1
      have key : ∀ y, φ g0 y = σ.symm (g0 (σ y)) := fun y => by rw [RingEquiv.eq_symm_apply, hφ]
      ext x
      apply σ.injective
      rw [hφ, conjGal_apply, conjGal_apply, key]
      simp [σ1']
    rw [htw, hconj]

end H1TransportFieldIso

/-! ### Involutive Eigenspace Length Splitting & CM Plus/Minus Parts (`PartLenCongr`) -/

section PlusMinusCM

/-- Involution eigenspace length splitting when `2` is a unit in `R`. -/
theorem length_eq_add_eigen {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (h2 : IsUnit (2 : R)) (N : Submodule R M) (f : Module.End R M) (hN : ∀ x ∈ N, f x ∈ N)
    (hf : ∀ x, f (f x) = x) (s : R) (hs : s * s = 1) :
    Module.length R N = Module.length R ↥(N ⊓ f.eigenspace s) + Module.length R ↥(N ⊓ f.eigenspace (-s)) := by
  set c : R := ↑h2.unit⁻¹
  have hc : (2 : R) * c = 1 := h2.mul_val_inv
  have eP : ∀ x : M, f (x + s • f x) = s • (x + s • f x) := fun x => by
    rw [map_add, map_smul, hf, smul_add, smul_smul, hs, one_smul, add_comm]
  have eQ : ∀ x : M, f (x - s • f x) = (-s) • (x - s • f x) := fun x => by
    rw [map_sub, map_smul, hf, smul_sub, smul_smul, neg_mul, hs, neg_smul, neg_smul, one_smul]
    abel
  have memP : ∀ x ∈ N, c • (x + s • f x) ∈ N ⊓ f.eigenspace s := fun x hx =>
    ⟨N.smul_mem c (N.add_mem hx (N.smul_mem s (hN x hx))),
      (f.eigenspace s).smul_mem c (Module.End.mem_eigenspace_iff.mpr (eP x))⟩
  have memQ : ∀ x ∈ N, c • (x - s • f x) ∈ N ⊓ f.eigenspace (-s) := fun x hx =>
    ⟨N.smul_mem c (N.sub_mem hx (N.smul_mem s (hN x hx))),
      (f.eigenspace (-s)).smul_mem c (Module.End.mem_eigenspace_iff.mpr (eQ x))⟩
  let toP : N →ₗ[R] ↥(N ⊓ f.eigenspace s) :=
    (c • (N.subtype + s • (f ∘ₗ N.subtype))).codRestrict _ (fun x => by
      simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply, Submodule.coe_subtype]
      exact memP _ x.2)
  let toQ : N →ₗ[R] ↥(N ⊓ f.eigenspace (-s)) :=
    (c • (N.subtype - s • (f ∘ₗ N.subtype))).codRestrict _ (fun x => by
      simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply, Submodule.coe_subtype]
      exact memQ _ x.2)
  let back : (↥(N ⊓ f.eigenspace s) × ↥(N ⊓ f.eigenspace (-s))) →ₗ[R] N :=
    (Submodule.inclusion inf_le_left).coprod (Submodule.inclusion inf_le_left)
  have h₁ : (toP.prod toQ) ∘ₗ back = LinearMap.id := by
    ext ⟨a, ha⟩
    all_goals simp [toP, toQ, back]
    · rw [Module.End.mem_eigenspace_iff.mp ha.2]
      linear_combination (norm := module) hs • (c • a) + hc • a
    · rw [Module.End.mem_eigenspace_iff.mp ha.2]
      linear_combination (norm := module) hs • (-(c • a))
    · rw [Module.End.mem_eigenspace_iff.mp ha.2]
      linear_combination (norm := module) hs • (-(c • a))
    · rw [Module.End.mem_eigenspace_iff.mp ha.2]
      linear_combination (norm := module) hs • (c • a) + hc • a
  have h₂ : back ∘ₗ (toP.prod toQ) = LinearMap.id := by
    ext ⟨x, hx⟩
    simp [toP, toQ, back]
    linear_combination (norm := module) hc • x
  rw [(LinearEquiv.ofLinearMap (toP.prod toQ) back h₁ h₂).length_eq, Module.length_prod]

section CMPartsDefs

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
  [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]

variable (E) in
def cE : E ≃+* E := (IsCMField.complexConj E).toRingEquiv

def cAct (D : LData E Ω l) (e : ℤ) : Module.End ℤ_[l] (H1 (qzTw D e)) :=
  galoisActionOnCohomology D e (cE E)

def ShaPlus (D : LData E Ω l) (e : ℕ) : Submodule ℤ_[l] (H1 (qzTw D (e : ℤ))) :=
  Sha D e ⊓ (cAct D e).eigenspace ((-1) ^ e)

def ShaMinus (D : LData E Ω l) (e : ℕ) : Submodule ℤ_[l] (H1 (qzTw D (e : ℤ))) :=
  Sha D e ⊓ (cAct D e).eigenspace ((-1) ^ (e + 1))

def plusLen (D : LData E Ω l) (e : ℕ) : ℕ∞ := Module.length ℤ_[l] (ShaPlus D e)

def minusLen (D : LData E Ω l) (e : ℕ) : ℕ∞ := Module.length ℤ_[l] (ShaMinus D e)

theorem cAct_cAct (D : LData E Ω l) (e : ℤ) (x : H1 (qzTw D e)) : cAct D e (cAct D e x) = x := by
  have hc : cE E * cE E = 1 := by ext y; simp [cE, IsCMField.complexConj_apply_apply]
  show galoisActionOnCohomology D e (cE E) (galoisActionOnCohomology D e (cE E) x) = x
  rw [← Module.End.mul_apply, ← galois_action_cohomology_mul, hc, galois_action_cohomology_one,
    Module.End.one_apply]

theorem cAct_mem_Sha (D : LData E Ω l) (e : ℤ) {x : H1 (qzTw D e)} (hx : x ∈ Sha D e) :
    cAct D e x ∈ Sha D e :=
  galois_action_preserves_sha D e _ hx

/-- Exact odd-prime splitting `shaLen D e = plusLen D e + minusLen D e` for any CM field `E`. -/
theorem shaLen_eq_add (hl : l ≠ 2) (D : LData E Ω l) (e : ℕ) :
    shaLen D e = plusLen D e + minusLen D e := by
  have h2 : IsUnit (2 : ℤ_[l]) := by
    by_contra hn
    have hmem : (2 : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := (IsLocalRing.mem_maximalIdeal _).mpr hn
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_ofNat] at hmem
    have h3 : ((2 : ℕ) : ZMod l) = 0 := by simpa using hmem
    rw [ZMod.natCast_eq_zero_iff] at h3
    exact hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h3)
  have hs : ((-1 : ℤ_[l]) ^ e) * ((-1) ^ e) = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  have key := length_eq_add_eigen h2 (Sha D e) (cAct D e) (fun _ hx => cAct_mem_Sha D e hx)
    (cAct_cAct D e) _ hs
  have hneg : -((-1 : ℤ_[l]) ^ e) = (-1) ^ (e + 1) := by rw [pow_succ, mul_neg_one]
  rwa [hneg] at key

end CMPartsDefs

private theorem cE_comm {F F' : Type} [Field F] [NumberField F] [IsCMField F]
    [Field F'] [NumberField F'] [IsCMField F'] (f : F ≃+* F') (x : F) :
    f (cE F x) = cE F' (f x) := by
  let φ' : F' →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  apply φ'.injective
  have h1 := IsCMField.complexEmbedding_complexConj F (φ'.comp f.toRingHom) x
  have h2 := IsCMField.complexEmbedding_complexConj F' φ' (f x)
  show φ' (f ((IsCMField.complexConj F) x)) = φ' ((IsCMField.complexConj F') (f x))
  rw [h2]
  exact h1

private theorem length_inf_eigen {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (Φ : M ≃ₗ[R] M') (N : Submodule R M) (N' : Submodule R M')
    (hN : N.map Φ.toLinearMap = N') (c : Module.End R M) (c' : Module.End R M')
    (hc : ∀ x, Φ (c x) = c' (Φ x)) (s : R) :
    Module.length R ↥(N ⊓ c.eigenspace s) = Module.length R ↥(N' ⊓ c'.eigenspace s) := by
  have hE : (c.eigenspace s).map Φ.toLinearMap = c'.eigenspace s := by
    ext y
    rw [Submodule.map_equiv_eq_comap_symm, Submodule.mem_comap, Module.End.mem_eigenspace_iff,
      Module.End.mem_eigenspace_iff]
    constructor
    · intro h
      have h' := congrArg Φ h
      rwa [hc, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, map_smul,
        LinearEquiv.apply_symm_apply] at h'
    · intro h
      apply Φ.injective
      rw [LinearEquiv.coe_coe, hc, LinearEquiv.apply_symm_apply, map_smul,
        LinearEquiv.apply_symm_apply, h]
  have hm : (N ⊓ c.eigenspace s).map Φ.toLinearMap = N' ⊓ c'.eigenspace s := by
    rw [Submodule.map_inf _ Φ.injective, hN, hE]
  rw [← hm]
  exact (Φ.submoduleMap (N ⊓ c.eigenspace s)).length_eq

/-- **`PartLenCongr`**: `plusLen` and `minusLen` are invariant under CM field isomorphisms `f : F ≃+* F'`. -/
theorem partLenCongr {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] [IsCMField F] {F' Ω' : Type} [Field F'] [NumberField F'] [Field Ω']
    [Algebra F' Ω'] [IsAlgClosure F' Ω'] [IsCMField F'] {l : ℕ} [Fact l.Prime]
    (D : LData F Ω l) (D' : LData F' Ω' l) (f : F ≃+* F') (e : ℕ) :
    plusLen D e = plusLen D' e ∧ minusLen D e = minusLen D' e := by
  obtain ⟨Φ, hΦ, hact⟩ := H1_transport_field_iso D D' f (e : ℤ)
  have hc := hact (cE F) (cE F') (cE_comm f)
  unfold plusLen minusLen ShaPlus ShaMinus cAct
  exact ⟨length_inf_eigen Φ _ _ hΦ _ _ hc _, length_inf_eigen Φ _ _ hΦ _ _ hc _⟩

/-- Canonical plus-part of `Stage12GaloisShaLen.Sha1Galois E p e` for a CM field `E`. -/
def Sha1GaloisPlus (E : Type) [Field E] [NumberField E] [IsCMField E] (p : Nat.Primes) (e : ℕ) :
    Submodule ℤ_[p.1] (H1 (qzTw (canonicalLData E p) (e : ℤ))) :=
  ShaPlus (canonicalLData E p) e

/-- Canonical minus-part of `Stage12GaloisShaLen.Sha1Galois E p e` for a CM field `E`. -/
def Sha1GaloisMinus (E : Type) [Field E] [NumberField E] [IsCMField E] (p : Nat.Primes) (e : ℕ) :
    Submodule ℤ_[p.1] (H1 (qzTw (canonicalLData E p) (e : ℤ))) :=
  ShaMinus (canonicalLData E p) e

def galoisPlusLen (E : Type) [Field E] [NumberField E] [IsCMField E] (p : Nat.Primes) (e : ℕ) : ℕ∞ :=
  plusLen (canonicalLData E p) e

def galoisMinusLen (E : Type) [Field E] [NumberField E] [IsCMField E] (p : Nat.Primes) (e : ℕ) : ℕ∞ :=
  minusLen (canonicalLData E p) e

/-- Direct CM plus/minus splitting on `realGaloisSelmerSystem.shaLen` for every odd prime `p ≠ 2`. -/
theorem galoisShaLen_eq_plus_add_minus (E : Type) [Field E] [NumberField E] [IsCMField E]
    (p : Nat.Primes) (hp : (p : ℕ) ≠ 2) (e : ℕ) :
    realGaloisSelmerSystem.shaLen E p e = galoisPlusLen E p e + galoisMinusLen E p e :=
  shaLen_eq_add hp (canonicalLData E p) e

end PlusMinusCM

end FieldIsoTransportAndCMParts

/-! ## Section 7: Unramified Selmer Inflation (`selAllLeInf`) & Cyclotomic Block Cocycle Length Bound (`≤ Sha`) -/

section SelmerInflationAndCyclotomicBlockBound

section SelAllSection

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

variable (F Ω) in
/-- Choice of a valuation subring of `Ω` lying over every finite prime `v` of `𝓞 F`. -/
abbrev Places : Type :=
  {A : HeightOneSpectrum (𝓞 F) → ValuationSubring Ω // ∀ v, IsPlaceOver (A v) v}

/-- Local unramified cohomology at `A`. -/
def unrAt (rho : Representation R (G F Ω) M) (A : ValuationSubring Ω) :
    Submodule R (H1 (rho.comp (Dec (F := F) A).subtype)) :=
  H1ur (rho.comp (Dec (F := F) A).subtype) ((Ine (F := F) A).subgroupOf (Dec (F := F) A))

/-- Global Selmer group defined by local conditions at all finite places. -/
def SelAll (rho : Representation R (G F Ω) M) (A : Places F Ω)
    (L : ∀ v, Submodule R (H1 (rho.comp (Dec (F := F) (A.1 v)).subtype))) :
    Submodule R (H1 rho) :=
  Sel rho (fun v => (Dec (F := F) (A.1 v)).subtype) (fun _ => continuous_subtype_val) L

/-- Bloch–Kato style local conditions: `Ll v` above `l`, `⊤` on `Sig`, unramified elsewhere. -/
def bkCond (rho : Representation R (G F Ω) M) (A : Places F Ω) (l : ℕ)
    (Sig : Set (HeightOneSpectrum (𝓞 F)))
    (Ll : ∀ v, Submodule R (H1 (rho.comp (Dec (F := F) (A.1 v)).subtype))) :
    ∀ v, Submodule R (H1 (rho.comp (Dec (F := F) (A.1 v)).subtype)) :=
  open Classical in
  fun v => if ((l : ℕ) : 𝓞 F) ∈ v.asIdeal then Ll v else if v ∈ Sig then ⊤ else unrAt rho (A.1 v)

def selLen (rho : Representation R (G F Ω) M) (A : Places F Ω) (l : ℕ)
    (Sig : Set (HeightOneSpectrum (𝓞 F)))
    (Ll : ∀ v, Submodule R (H1 (rho.comp (Dec (F := F) (A.1 v)).subtype))) : ℕ∞ :=
  Module.length R (SelAll rho A (bkCond rho A l Sig Ll))

/-- **`SelAllLeInf`**: Any Selmer class unramified outside `S` lies in the image of inflation from `G_{F, S}`. -/
theorem selAllLeInf [IsAlgClosure F Ω] [T2Space M] (S : Set (HeightOneSpectrum (𝓞 F)))
    (rhoS : Representation R (GS Ω S) M) (A : Places F Ω)
    (L : ∀ v, Submodule R (H1 ((rhoS.comp (toGS Ω S)).comp (Dec (F := F) (A.1 v)).subtype)))
    (hL : ∀ v ∉ S, L v ≤ unrAt (rhoS.comp (toGS Ω S)) (A.1 v)) :
    SelAll (rhoS.comp (toGS Ω S)) A L ≤
      LinearMap.range (resH1 rhoS (toGS Ω S) (continuous_toGS Ω S)) := by
  intro x hx
  rw [(infUnram (F := F) (Ω := Ω) (S := S) rhoS).2 x]
  intro v hv A' hA'
  have hloc := (mem_Sel _ _ _ _ x).1 hx v
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hunr : (Submodule.Quotient.mk
      (restrictCocycles1 _ ((Ine (F := F) (A.1 v)).subgroupOf (Dec (F := F) (A.1 v))).subtype
        continuous_subtype_val
        (restrictCocycles1 (rhoS.comp (toGS Ω S)) (Dec (F := F) (A.1 v)).subtype
          continuous_subtype_val z)) : H1 _) = 0 :=
    hL v hv hloc
  obtain ⟨m, hm⟩ := (mem_B1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hunr)
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := F) (A.2 v) hA'
  refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_B1 _ _).2 ⟨(rhoS.comp (toGS Ω S)) g m - z.1 g, fun σ => ?_⟩)
  have h1 : (σ : G F Ω) ∈ Ine (F := F) (g • A.1 v) := by rw [hg]; exact σ.2
  have hτ := conj_mem_Ine' (F := F) h1
  have hτD : g⁻¹ * σ.1 * g ∈ Dec (F := F) (A.1 v) := Ine_le_Dec _ hτ
  have h2 := cocycle1_conj_coboundary (rhoS.comp (toGS Ω S)) z.2.2 g (g⁻¹ * σ.1 * g) m
    (hm ⟨⟨g⁻¹ * σ.1 * g, hτD⟩, hτ⟩)
  have h3 : g * (g⁻¹ * σ.1 * g) * g⁻¹ = σ.1 := by group
  rw [h3] at h2
  exact h2

end SelAllSection

section CyclotomicBlockCocyclesLeSha

section AlgDvrLength

variable {l : ℕ} [Fact l.Prime] (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]

theorem algebraMap_padic_dvr_inj : Function.Injective (algebraMap ℤ_[l] O) := by
  by_contra h
  have hk : RingHom.ker (algebraMap ℤ_[l] O) ≠ ⊥ := fun h0 =>
    h ((RingHom.injective_iff_ker_eq_bot _).2 h0)
  have hp : (RingHom.ker (algebraMap ℤ_[l] O)).IsPrime := RingHom.ker_isPrime _
  have hm : ((⊥ : Ideal O).comap (algebraMap ℤ_[l] O)).IsMaximal := hp.isMaximal hk
  have : (⊥ : Ideal O).IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ hm
  exact IsDiscreteValuationRing.not_a_field O (IsLocalRing.eq_maximalIdeal this).symm

/-- For a finite DVR extension `O / ℤ_[l]`, `length_{ℤ_[l]}(O / lO) = finrank_{ℤ_[l]}(O)`. -/
theorem length_quot_padic_dvr :
    Module.length ℤ_[l] (O ⧸ Ideal.span {(l : O)}) = Module.finrank ℤ_[l] O := by
  haveI : FaithfulSMul ℤ_[l] O := (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap_padic_dvr_inj O)
  let b := Module.finBasis ℤ_[l] O
  let R := IsLocalRing.ResidueField ℤ_[l]
  let φ : O →ₗ[ℤ_[l]] (Fin (Module.finrank ℤ_[l] O) → R) :=
    ((Algebra.linearMap ℤ_[l] R).compLeft _).comp b.equivFun.toLinearMap
  have hs : Function.Surjective φ := fun y => by
    choose x hx using fun j => IsLocalRing.residue_surjective (R := ℤ_[l]) (y j)
    refine ⟨b.equivFun.symm x, funext fun j => ?_⟩
    simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact hx j
  have hk : LinearMap.ker φ = (Ideal.span {(l : O)}).restrictScalars ℤ_[l] := by
    ext x
    rw [LinearMap.mem_ker, Submodule.restrictScalars_mem, Ideal.mem_span_singleton']
    have key : ∀ z : ℤ_[l], algebraMap ℤ_[l] R z = 0 ↔ ∃ y, y * (l : ℤ_[l]) = z := fun z => by
      rw [← Ideal.mem_span_singleton', ← PadicInt.maximalIdeal_eq_span_p]
      exact IsLocalRing.residue_eq_zero_iff z
    constructor
    · intro h
      choose y hy using fun j => (key _).1 (congrFun h j)
      refine ⟨b.equivFun.symm y, b.equivFun.injective ?_⟩
      have : b.equivFun.symm y * (l : O) = (l : ℤ_[l]) • b.equivFun.symm y := by
        rw [Algebra.smul_def, map_natCast, mul_comm]
      rw [this, map_smul, LinearEquiv.apply_symm_apply]
      funext j
      rw [Pi.smul_apply, smul_eq_mul, mul_comm]
      exact hy j
    · rintro ⟨y, rfl⟩
      have : y * (l : O) = (l : ℤ_[l]) • y := by rw [Algebra.smul_def, map_natCast, mul_comm]
      rw [this, map_smul]
      funext j
      rw [Pi.smul_apply, Algebra.smul_def, (key _).2 ⟨1, one_mul _⟩, zero_mul]
      rfl
  have e1 := φ.quotKerEquivOfSurjective hs
  rw [hk] at e1
  have e2 := Submodule.Quotient.restrictScalarsEquiv ℤ_[l] (Ideal.span {(l : O)})
  have h1 : Module.length ℤ_[l] R = 1 := by
    rw [Module.length_eq_one_iff]
    exact isSimpleModule_iff_quot_maximal.2 ⟨_, IsLocalRing.maximalIdeal.isMaximal _, ⟨LinearEquiv.refl _ _⟩⟩
  rw [← e2.length_eq, e1.length_eq, Module.length_pi_of_fintype]
  simp [h1]

/-- Key DVR scalar-restriction length bound: if `Ψ : C →ₗ[ℤ_[l]] (Fin d → S)` has `ker Ψ ≤ B`, then
`len_O(C) ≤ len_O(B) + len_O(O / lO) * len_{ℤ_[l]}(S)`. -/
theorem length_le_of_coord_map {C S : Type*} [AddCommGroup C] [Module O C] [Module ℤ_[l] C]
    [IsScalarTower ℤ_[l] O C] [AddCommGroup S] [Module ℤ_[l] S] (B : Submodule O C)
    (Ψ : C →ₗ[ℤ_[l]] (Fin (Module.finrank ℤ_[l] O) → S)) (h : ∀ x, Ψ x = 0 → x ∈ B) :
    Module.length O C ≤ Module.length O B +
      Module.length O (O ⧸ Ideal.span {(l : O)}) * Module.length ℤ_[l] S := by
  haveI : IsLocalHom (algebraMap ℤ_[l] O) := ⟨fun x hx => by
    by_contra hnx
    have hlx : (l : ℤ_[l]) ∣ x := by
      rw [← PadicInt.norm_lt_one_iff_dvd]
      exact PadicInt.not_isUnit_iff.mp hnx
    have hlu : IsUnit (l : O) :=
      isUnit_of_dvd_unit (by simpa using map_dvd (algebraMap ℤ_[l] O) hlx) hx
    have htop : Ideal.span {(l : O)} = ⊤ := Ideal.span_singleton_eq_top.mpr hlu
    haveI : Subsingleton (O ⧸ Ideal.span {(l : O)}) := by rw [htop]; infer_instance
    have h0 : Module.length ℤ_[l] (O ⧸ Ideal.span {(l : O)}) = 0 :=
      (Module.length_eq_zero_iff).mpr inferInstance
    haveI : FaithfulSMul ℤ_[l] O :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap_padic_dvr_inj O)
    have hpos : 0 < Module.finrank ℤ_[l] O := Module.finrank_pos
    rw [length_quot_padic_dvr O] at h0
    exact hpos.ne' (Nat.cast_eq_zero.mp h0)⟩
  rw [Module.length_eq_add_of_exact B.subtype B.mkQ B.subtype_injective B.mkQ_surjective
    (LinearMap.exact_subtype_mkQ B)]
  refine add_le_add le_rfl ?_
  have h1 : Module.length ℤ_[l] (C ⧸ B) ≤ Module.length ℤ_[l] (C ⧸ LinearMap.ker Ψ) := by
    refine Module.length_le_of_surjective
      ((LinearMap.ker Ψ).liftQ (B.mkQ.restrictScalars ℤ_[l]) fun x hx =>
        (Submodule.Quotient.mk_eq_zero _).2 (h x hx)) fun y => ?_
    obtain ⟨x, rfl⟩ := B.mkQ_surjective y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  have h2 : Module.length ℤ_[l] (C ⧸ LinearMap.ker Ψ) ≤
      (Module.finrank ℤ_[l] O : ℕ∞) * Module.length ℤ_[l] S := by
    refine (Module.length_le_of_injective ((LinearMap.ker Ψ).liftQ Ψ le_rfl) ?_).trans (le_of_eq ?_)
    · rw [← LinearMap.ker_eq_bot]
      exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
    · rw [Module.length_pi_of_fintype]; simp
  have h3 := h1.trans h2
  rw [← length_quot_padic_dvr O, IsLocalRing.length_restrictScalars ℤ_[l] O (C ⧸ B),
    IsLocalRing.length_restrictScalars ℤ_[l] O (O ⧸ Ideal.span {(l : O)}), mul_right_comm] at h3
  haveI : Module.Finite (IsLocalRing.ResidueField ℤ_[l]) (IsLocalRing.ResidueField O) := inferInstance
  exact (ENat.mul_le_mul_right_iff Module.length_pos.ne' Module.length_ne_top).1 h3

end AlgDvrLength

section LocTrivToSha

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] (Dd : LData F Ω l) (e : ℤ) (A : Places F Ω)

abbrev twG : Representation ℤ_[l] (G F Ω) (QZ l) := (qzTw Dd e).comp (toGS Ω _)

theorem twG_apply (g : G F Ω) (x : QZ l) :
    twG Dd e g x = ((cycZ F Ω l g ^ (-e) : ℤ_[l]ˣ) : ℤ_[l]) • x := by
  rw [← Dd.hchi]; rfl

/-- Predicate on 1-cocycles `f : G F Ω → QZ l` that vanish on inertia outside `S_l` and are
locally coboundaries at every prime `v ∣ l`. -/
def LocTriv (f : G F Ω → QZ l) : Prop :=
  f ∈ Z1 (twG Dd e) ∧
    (∀ v, v ∉ Above F l → ∀ g ∈ Ine (F := F) (A.1 v), f g = 0) ∧
    ∀ v ∈ Above F l, ∃ m, ∀ g ∈ Dec (F := F) (A.1 v), f g = twG Dd e g m - m

variable {Dd e A}

theorem LocTriv.vanish {f : G F Ω → QZ l} (hf : LocTriv Dd e A f) (n : G F Ω)
    (hn : n ∈ NS Ω (Dd.S : Set (HeightOneSpectrum (𝓞 F)))) : f n = 0 := by
  have htriv : ∀ n ∈ NS Ω (Dd.S : Set (HeightOneSpectrum (𝓞 F))), ∀ x, twG Dd e n x = x := by
    intro n hn x
    have : toGS Ω (Dd.S : Set (HeightOneSpectrum (𝓞 F))) n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    show qzTw Dd e (toGS Ω _ n) x = x
    rw [this, map_one]; rfl
  have h1 : f 1 = 0 := cocycle1_one (twG Dd e) hf.1.2
  let N : Subgroup (G F Ω) :=
    { carrier := {n | n ∈ NS Ω (Dd.S : Set (HeightOneSpectrum (𝓞 F))) ∧ f n = 0}
      one_mem' := ⟨one_mem _, h1⟩
      mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by rw [hf.1.2, ha.2, hb.2, map_zero, add_zero]⟩
      inv_mem' := fun {a} ha => ⟨inv_mem ha.1, by
        have := hf.1.2 a⁻¹ a
        rw [inv_mul_cancel, h1, ha.2, map_zero, add_zero] at this
        exact this.symm⟩ }
  haveI hN : N.Normal := ⟨fun a ha g => by
    have hc := (normal_NS (Ω := Ω) (Dd.S : Set (HeightOneSpectrum (𝓞 F)))).conj_mem a ha.1 g
    refine ⟨hc, ?_⟩
    rw [cocycle1_conj_coboundary _ hf.1.2 g a 0 (by rw [ha.2, map_zero, sub_zero]), htriv _ hc, sub_self]⟩
  have hcl : IsClosed (N : Set (G F Ω)) := (isClosed_NS Ω _).inter (isClosed_singleton.preimage hf.1.1)
  refine (Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_) hcl hn).2
  intro τ hτ
  simp only [Set.mem_iUnion, Set.mem_compl_iff, Set.mem_ofPred_eq] at hτ
  obtain ⟨v, hv, A', hA', hτ⟩ := hτ
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) (A.2 v) hA'
  have h2 := conj_mem_Ine' (F := F) hτ
  have h3 : g⁻¹ * τ * g ∈ N := by
    refine ⟨?_, hf.2.1 v (by rw [← Dd.hS]; exact hv) _ h2⟩
    apply Subgroup.le_topologicalClosure
    apply Subgroup.subset_normalClosure
    simp only [Set.mem_iUnion, Set.mem_compl_iff, Set.mem_ofPred_eq]
    exact ⟨v, hv, A.1 v, A.2 v, h2⟩
  have := hN.conj_mem _ h3 g
  simpa [mul_assoc] using this

variable (Dd e) in
def infl : ↥(Z1 (qzTw Dd e)) →ₗ[ℤ_[l]] (G F Ω → QZ l) :=
  (Z1 (twG Dd e)).subtype.comp (restrictCocycles1 (qzTw Dd e) (toGS Ω _) (continuous_toGS Ω _))

theorem infl_inj : Function.Injective (infl Dd e) := fun _ _ h =>
  Subtype.ext (funext fun x => by obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x; exact congrFun h g)

theorem LocTriv.mem_range {f : G F Ω → QZ l} (hf : LocTriv Dd e A f) :
    f ∈ LinearMap.range (infl Dd e) := by
  let f' : GS Ω (Dd.S : Set (HeightOneSpectrum (𝓞 F))) → QZ l := Quotient.lift f fun a b hab => by
    have h1 := hf.vanish _ (QuotientGroup.leftRel_apply.1 hab)
    have h2 := hf.1.2 a (a⁻¹ * b)
    rw [mul_inv_cancel_left, h1, map_zero, add_zero] at h2
    exact h2.symm
  refine ⟨⟨f', hf.1.1.quotient_lift _, fun a b => ?_⟩, rfl⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact hf.1.2 a b

theorem mk_mem_Sha (z : ↥(Z1 (qzTw Dd e))) (hz : LocTriv Dd e A (infl Dd e z)) :
    Submodule.Quotient.mk z ∈ Sha Dd e := by
  refine (Submodule.mem_iInf _).2 fun v => ?_
  refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_B1 _ _).2 ?_)
  obtain ⟨m, hm⟩ := hz.2.2 v.1 (by rw [← Dd.hS]; exact v.2)
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := F) (A.2 v.1) (Dd.hA v)
  refine ⟨twG Dd e g m - infl Dd e z g, fun σ => ?_⟩
  have h1 : (σ : G F Ω) ∈ Dec (F := F) (g • A.1 v.1) := by rw [hg]; exact σ.2
  have h2 := cocycle1_conj_coboundary _ hz.1.2 g _ m (hm _ (conj_mem_Dec h1))
  have h3 : g * (g⁻¹ * σ * g) * g⁻¹ = σ := by group
  rw [h3] at h2
  exact h2

/-- Any `ℤ_[l]`-linear map `a : C →ₗ[ℤ_[l]] (G F Ω → QZ l)` landing in `LocTriv` descends to
`Ψ : C →ₗ[ℤ_[l]] Sha Dd e` whose kernel consists of global coboundaries. -/
theorem exists_toSha {C : Type*} [AddCommGroup C] [Module ℤ_[l] C]
    (a : C →ₗ[ℤ_[l]] (G F Ω → QZ l)) (ha : ∀ x, LocTriv Dd e A (a x)) :
    ∃ Ψ : C →ₗ[ℤ_[l]] ↥(Sha Dd e), ∀ x, Ψ x = 0 → ∃ m, ∀ g, a x g = twG Dd e g m - m := by
  let a' := LinearMap.codRestrictOfInjective a (infl Dd e) infl_inj fun x => (ha x).mem_range
  have h : ∀ x, infl Dd e (a' x) = a x := fun x => LinearMap.codRestrictOfInjective_comp_apply _ _ _ _ x
  refine ⟨LinearMap.codRestrict _ ((Submodule.mkQ _).comp a') fun x =>
      mk_mem_Sha (A := A) _ (by rw [h]; exact ha x),
    fun x hx => ?_⟩
  obtain ⟨m, hm⟩ := (mem_B1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 (congrArg Subtype.val hx))
  refine ⟨m, fun g => ?_⟩
  rw [← h]
  exact hm _

/-- **Cyclotomic Block Cocycle Length Bound (`LengthCyclotomicBlockCocyclesLeSha`)**:
Given a finite DVR extension `O / ℤ_[l]`, a discrete `O`-module `M` with a `ℤ_[l]`-linear coordinate
bijection `p : M ≃ (Fin (finrank ℤ_[l] O) → QZ l)` intertwining `ρ` with `twG Dd e`, and any
`O`-submodule `C ≤ Z1 ρ` whose coordinates are `LocTriv`,
`Module.length O C ≤ Module.length O (B1 ρ ⊓ C) + Module.length O (O ⧸ lO) * shaLen Dd e`. -/
theorem length_cyclotomic_block_cocycles_le_sha {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    {M : Type*} [AddCommGroup M] [Module O M] [Module ℤ_[l] M] [IsScalarTower ℤ_[l] O M]
    [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M]
    (ρ : Representation O (G F Ω) M) (p : M →+ (Fin (Module.finrank ℤ_[l] O) → QZ l))
    (hp : Function.Bijective p)
    (hps : ∀ (z : ℤ_[l]) (x : M), p (algebraMap ℤ_[l] O z • x) = z • p x)
    (hact : ∀ g x j, p (ρ g x) j = twG Dd e g (p x j))
    (C : Submodule O (G F Ω → M))
    (hloc : ∀ (j : Fin (Module.finrank ℤ_[l] O)) (f : C), LocTriv Dd e A (fun g => p (f.1 g) j)) :
    Module.length O C ≤ Module.length O ↥(B1 ρ ⊓ C) +
      Module.length O (O ⧸ Ideal.span {(l : O)}) * shaLen Dd e := by
  let a : Fin (Module.finrank ℤ_[l] O) → (↥C →ₗ[ℤ_[l]] (G F Ω → QZ l)) := fun j =>
    { toFun := fun f g => p (f.1 g) j
      map_add' := fun f f' => funext fun g => congrFun (p.map_add (f.1 g) (f'.1 g)) j
      map_smul' := fun z f => funext fun g => by
        rw [← algebraMap_smul O z f]
        exact congrFun (hps z (f.1 g)) j }
  choose Ψ hΨ using fun j => exists_toSha (Dd := Dd) (e := e) (A := A) (a j) (hloc j)
  have key := length_le_of_coord_map (l := l) O ((B1 ρ).comap C.subtype) (LinearMap.pi Ψ) fun f hf => by
    choose m hm using fun j => hΨ j f (congrFun hf j)
    obtain ⟨y, rfl⟩ := hp.2 m
    refine (mem_B1 _ _).2 ⟨y, fun g => hp.1 (funext fun j => ?_)⟩
    rw [map_sub, Pi.sub_apply, hact]
    exact hm j g
  refine key.trans (add_le_add (le_of_eq ?_) le_rfl)
  have e' := Submodule.equivMapOfInjective C.subtype C.subtype_injective ((B1 ρ).comap C.subtype)
  rw [Submodule.map_comap_subtype, inf_comm] at e'
  exact e'.length_eq

/-- Same cyclotomic block cocycle length bound stated directly in terms of `galoisShaLen F p e`
(and `realGaloisSelmerSystem.shaLen F p e` when `e : ℕ`). -/
theorem length_cyclotomic_block_cocycles_le_galoisShaLen (p : Nat.Primes)
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[p.1] O]
    [Module.Finite ℤ_[p.1] O] {M : Type*} [AddCommGroup M] [Module O M] [Module ℤ_[p.1] M]
    [IsScalarTower ℤ_[p.1] O M] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M]
    (Dd : LData F Ω p.1) (e : ℤ) (A : Places F Ω) (ρ : Representation O (G F Ω) M)
    (coord : M →+ (Fin (Module.finrank ℤ_[p.1] O) → QZ p.1)) (hp : Function.Bijective coord)
    (hps : ∀ (z : ℤ_[p.1]) (x : M), coord (algebraMap ℤ_[p.1] O z • x) = z • coord x)
    (hact : ∀ g x j, coord (ρ g x) j = twG Dd e g (coord x j))
    (C : Submodule O (G F Ω → M))
    (hloc : ∀ (j : Fin (Module.finrank ℤ_[p.1] O)) (f : C), LocTriv Dd e A (fun g => coord (f.1 g) j)) :
    Module.length O C ≤ Module.length O ↥(B1 ρ ⊓ C) +
      Module.length O (O ⧸ Ideal.span {(p.1 : O)}) * galoisShaLen F p e := by
  rw [← shaLen_eq_galoisShaLen F p Dd e]
  exact length_cyclotomic_block_cocycles_le_sha (Dd := Dd) (e := e) (A := A) ρ coord hp hps hact C hloc

end LocTrivToSha

end CyclotomicBlockCocyclesLeSha

end SelmerInflationAndCyclotomicBlockBound

end RHDirect.Stage13GL_GaloisCohomLength

end
