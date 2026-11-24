import RHDirect.Interfaces
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Atoms.Finite

/-!
# RHDirect.BaseChangeCyclic

Compact, direct, zero-`sorry`, zero-`axiom` rebuild of the **Cyclic Base Change,
Frobenius-Twist Descent, Solvable Prime-Tower Lifting & Strong Multiplicity One Algebra**
core for `rh-direct`, distilled directly from:
- `ModularityArgument/BaseChangeUnits/` (`CycFree.lean`, `ExistsPrimeIndex.lean`,
  `UpCycOf.lean`, `WideOfCyclic.lean`, `CyclicLiftRankTwoOfCyclicBaseChange.lean`,
  `SolvableEquivalenceOfBaseChange.lean`, `QuadraticInductionGL2Alt.lean`, `WsIIOfPrintsH.lean`),
- `Foundations/Convolution/RealGroupAnalysis/QuadBC2.lean`, and
- `PositivityTheory.Rg.BcN` (`BaseChangeIsobaricN`).

## Contents

1. **Finite Solvable Prime-Index Composition Chains** (`exists_normal_prime_index`,
   `SolvableStepChain`, `exists_solvableStepChain`, `SolvableStepChain.card_eq_prod`).
2. **Multiset Scaling Rigidity, Eigenvalue Polynomials & Algebraic Satake Normalization**
   (`multiset_map_mul_eq_self_pow_card`, `multiset_map_mul_eq_self_eq_one_of_coprime`,
   `algSat`, `algSat_pow`, `eigPoly`, `multiset_eq_of_eigPoly_eq`, `eigPoly_quad_inert`).
3. **Strong Multiplicity One & Cyclic-Group Twist Invariance** (`SatakeSystem`,
   `SatakeSystem.conj_iso_of_sat_invariant`, `SatakeSystem.cyclic_action_invariant_iff_gen`,
   `SatakeSystem.self_twist_trivial_of_coprime`, `SatakeSystem.twist_injective_of_no_self_twist`).
4. **Prime-Degree Cyclic Base Change & Frobenius-Eigenvalue Descent** (`BaseChangeStep`,
   `BaseChangeStep.lift_unique`, `BaseChangeStep.lift_fiber_invariant`,
   `BaseChangeStep.lift_of_no_self_twist`, `BaseChangeStep.lift_of_coprime_prime_rank`,
   `BaseChangeStep.rankTwo_dichotomy`, `BaseChangeStep.rankTwo_odd_prime_lift`,
   `BaseChangeGalStep.frob_lift`, `BaseChangeGalStep.frob_descent`, `BaseChangeGalStep.aut_equiv`).
5. **Cyclic-Prime Tower Lifting & Solvable Induction** (`BaseChangeTower`,
   `BaseChangeTower.norm_under`, `BaseChangeTower.aut_equiv`, `BaseChangeTower.lift_aut`,
   `BaseChangeTower.descent_aut`, `BaseChangeTower.append`, `BaseChangeTower.of_solvable_decomp`).
6. **Isobaric Base Change Algebra (`BaseChangeIsobaricN` core)** (`IsobaricBaseChangeDatum`,
   `IsobaricBaseChangeDatum.totalSat_card`, `IsobaricBaseChangeDatum.eigPoly_total`,
   `IsobaricBaseChangeDatum.satake_unique_of_split`).
7. **Cyclic Character Level Bridge to `RHDirect.Interfaces`** (`Level.cyc_subgroup_isCyclic`,
   `Level.cyc_order_eq_orderOf`, `Level.cyc_card_le_order`, `PChar.pow_orderOf_val`).

Zero `sorry`, zero custom `axiom`s.
-/

noncomputable section

open Complex Polynomial Filter

namespace RHDirect

/-! ## 1. Finite Solvable Groups & Cyclic Prime-Index Composition Chains -/

/-- Every nontrivial finite solvable group admits a normal subgroup of prime index
(mirroring `BaseChangeUnits/ExistsPrimeIndex.lean`). -/
theorem exists_normal_prime_index (Γ : Type) [Group Γ] [Finite Γ] [Nontrivial Γ]
    [Group.IsSolvable Γ] :
    ∃ M : Subgroup Γ, M.Normal ∧ M.index.Prime := by
  obtain ⟨M, hM, hle⟩ := (eq_top_or_exists_le_coatom (commutator Γ)).resolve_left
    (Group.IsSolvable.commutator_lt_top_of_nontrivial Γ).ne
  have hnorm : M.Normal := ⟨fun n hn g => by
    have h1 : g * n * g⁻¹ * n⁻¹ ∈ M :=
      hle (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
    simpa [mul_assoc] using M.mul_mem h1 hn⟩
  refine ⟨M, hnorm, ?_⟩
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (n := Nat.card (Γ ⧸ M))
    (mt Subgroup.index_eq_one.1 hM.1)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hd
  have h1 : (Subgroup.zpowers g).comap (QuotientGroup.mk' M) = ⊤ := by
    refine hM.2 _ (lt_of_le_of_ne (fun x hx => ?_) fun e => ?_)
    · rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
      exact one_mem _
    · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M g
      have hx : x ∈ M := e ▸ Subgroup.mem_zpowers _
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx, orderOf_one] at hg
      exact hp.one_lt.ne hg
  have h2 : Subgroup.zpowers g = ⊤ :=
    Subgroup.comap_injective (QuotientGroup.mk'_surjective M)
      (h1.trans (Subgroup.comap_top _).symm)
  rw [Subgroup.index, ← Subgroup.card_top, ← h2, Nat.card_zpowers, hg]
  exact hp

/-- A normal subgroup of prime index yields a cyclic quotient of that prime order. -/
theorem isCyclic_quotient_of_prime_index {Γ : Type} [Group Γ] (M : Subgroup Γ) [M.Normal]
    (hp : M.index.Prime) : IsCyclic (Γ ⧸ M) := by
  have : Fact M.index.Prime := ⟨hp⟩
  exact isCyclic_of_prime_card (p := M.index) rfl

/-- An explicit composition chain of normal prime-index cyclic steps decomposing a finite
solvable group `Γ` down to the trivial group. -/
inductive SolvableStepChain : (Γ : Type) → [Group Γ] → Type 1
  | nil (Γ : Type) [Group Γ] (hsub : Subsingleton Γ) : SolvableStepChain Γ
  | cons {Γ : Type} [Group Γ] (M : Subgroup Γ) (hnorm : M.Normal)
      (hp : M.index.Prime) (rest : SolvableStepChain M) : SolvableStepChain Γ

namespace SolvableStepChain

/-- Number of cyclic prime-degree steps in a `SolvableStepChain`. -/
def length {Γ : Type} [Group Γ] : SolvableStepChain Γ → ℕ
  | .nil _ _ => 0
  | .cons _ _ _ rest => rest.length + 1

/-- The ordered list of prime indices along a `SolvableStepChain`. -/
def primes {Γ : Type} [Group Γ] : SolvableStepChain Γ → List ℕ
  | .nil _ _ => []
  | .cons M _ _ rest => M.index :: rest.primes

theorem primes_length {Γ : Type} [Group Γ] (c : SolvableStepChain Γ) :
    c.primes.length = c.length := by
  induction c with
  | nil _ _ => rfl
  | cons _ _ _ _ ih => simp [primes, length, ih]

theorem primes_all_prime {Γ : Type} [Group Γ] (c : SolvableStepChain Γ) :
    ∀ p ∈ c.primes, p.Prime := by
  induction c with
  | nil _ _ => intro p hp; nomatch hp
  | cons _ _ hM _ ih =>
    intro p hp
    simp only [primes, List.mem_cons] at hp
    rcases hp with rfl | hp'
    · exact hM
    · exact ih p hp'

/-- The cardinality of `Γ` equals the product of the prime step degrees in the chain. -/
theorem card_eq_prod {Γ : Type} [Group Γ] [Finite Γ] (c : SolvableStepChain Γ) :
    Nat.card Γ = c.primes.prod := by
  induction c with
  | nil G hsub =>
    have : Subsingleton G := hsub
    simp [primes, Nat.card_unique]
  | cons M _ _ rest ih =>
    simp only [primes, List.prod_cons]
    have hlag : Nat.card M * M.index = Nat.card _ := M.card_mul_index
    rw [← hlag, mul_comm, ih]

end SolvableStepChain

/-- Every finite solvable group admits a prime-index cyclic composition chain, proved by
strong induction on `Nat.card Γ`. -/
theorem exists_solvableStepChain (Γ : Type) [Group Γ] [Finite Γ] [Group.IsSolvable Γ] :
    Nonempty (SolvableStepChain Γ) := by
  suffices h : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G] [Group.IsSolvable G],
      Nat.card G = n → Nonempty (SolvableStepChain G) from h (Nat.card Γ) Γ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G _ _ _ hcard
    by_cases hsub : Subsingleton G
    · exact ⟨.nil G hsub⟩
    · have : Nontrivial G := not_subsingleton_iff_nontrivial.mp hsub
      obtain ⟨M, hnorm, hp⟩ := exists_normal_prime_index G
      have : Group.IsSolvable M :=
        Group.isSolvable_of_isSolvable_injective M.subtype_injective
      have hMlt : Nat.card M < n := by
        rw [← hcard, ← M.card_mul_index]
        exact lt_mul_of_one_lt_right Nat.card_pos hp.one_lt
      obtain ⟨rest⟩ := ih (Nat.card M) hMlt M rfl
      exact ⟨.cons M hnorm hp rest⟩

/-! ## 2. Multiset Scaling Rigidity, Eigenvalue Polynomials & Algebraic Satake Normalization -/

private theorem multiset_prod_map_mul {G : Type} [CommGroup G] (B : Multiset G) (c : G) :
    (B.map (· * c)).prod = B.prod * c ^ B.card := by
  induction B using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, ih, pow_succ]
    ac_rfl

/-- **Multiset Scaling Rigidity**: If multiplying every element of a multiset `B` in a
commutative group by `c` leaves `B` unchanged, then `c ^ B.card = 1`. -/
theorem multiset_map_mul_eq_self_pow_card {G : Type} [CommGroup G] (B : Multiset G) (c : G)
    (h : B.map (· * c) = B) : c ^ B.card = 1 := by
  have hprod : (B.map (· * c)).prod = B.prod := congrArg Multiset.prod h
  rw [multiset_prod_map_mul] at hprod
  exact mul_left_cancel (hprod.trans (mul_one B.prod).symm)

/-- Under a self-twist `B.map (· * c) = B`, the exact order of `c` divides `B.card`. -/
theorem multiset_map_mul_eq_self_orderOf_dvd {G : Type} [CommGroup G] (B : Multiset G) (c : G)
    (h : B.map (· * c) = B) : orderOf c ∣ B.card :=
  orderOf_dvd_of_pow_eq_one (multiset_map_mul_eq_self_pow_card B c h)

/-- **Coprime Prime-Order Rigidity**: If `B.map (· * c) = B`, `c ^ p = 1`, and
`Nat.Coprime p B.card`, then `c = 1`. -/
theorem multiset_map_mul_eq_self_eq_one_of_coprime {G : Type} [CommGroup G] (B : Multiset G)
    (c : G) {p : ℕ} (h : B.map (· * c) = B) (hp : c ^ p = 1) (hcop : Nat.Coprime p B.card) :
    c = 1 := by
  have hd1 : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one hp
  have hd2 : orderOf c ∣ B.card := multiset_map_mul_eq_self_orderOf_dvd B c h
  have h1 : orderOf c ∣ Nat.gcd p B.card := Nat.dvd_gcd hd1 hd2
  rw [hcop.gcd_eq_one, Nat.dvd_one] at h1
  exact orderOf_eq_one_iff.mp h1

/-- Rank-1 multiset scaling rigidity: a singleton multiset fixed by `· * c` forces `c = 1`. -/
theorem multiset_map_mul_eq_self_rank_one {G : Type} [CommGroup G] (B : Multiset G) (c : G)
    (hcard : B.card = 1) (h : B.map (· * c) = B) : c = 1 := by
  have hpow := multiset_map_mul_eq_self_pow_card B c h
  rwa [hcard, pow_one] at hpow

/-- Cyclic-subgroup twist invariance: if `B` is invariant under scaling by `c`, then `B` is
invariant under scaling by every integer power `c ^ k` (`k : ℤ`). -/
theorem multiset_map_mul_zpow_of_eq_self {G : Type} [CommGroup G] (B : Multiset G) (c : G)
    (h : B.map (· * c) = B) : ∀ k : ℤ, B.map (· * c ^ k) = B := by
  have hnat : ∀ m : ℕ, B.map (· * c ^ m) = B := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have : B.map (· * c ^ (m + 1)) = (B.map (· * c ^ m)).map (· * c) := by
        rw [Multiset.map_map]
        refine Multiset.map_congr rfl fun x _ => ?_
        simp only [Function.comp_apply, pow_succ, mul_assoc]
      rw [this, ih, h]
  have hinv : B.map (· * c⁻¹) = B := by
    have : (B.map (· * c)).map (· * c⁻¹) = B := by
      rw [Multiset.map_map]
      simp
    rwa [h] at this
  have hnatInv : ∀ m : ℕ, B.map (· * (c⁻¹) ^ m) = B := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have : B.map (· * (c⁻¹) ^ (m + 1)) = (B.map (· * (c⁻¹) ^ m)).map (· * c⁻¹) := by
        rw [Multiset.map_map]
        refine Multiset.map_congr rfl fun x _ => ?_
        simp only [Function.comp_apply, pow_succ, mul_assoc]
      rw [this, ih, hinv]
  intro k
  cases k with
  | ofNat m => simpa using hnat m
  | negSucc m =>
    have hpow : c ^ Int.negSucc m = (c⁻¹) ^ (m + 1) := by
      rw [zpow_negSucc, inv_pow]
    rw [hpow]
    exact hnatInv (m + 1)

/-- Algebraic Satake normalization `α ↦ q^((n-1)/2) · α` (mirroring `UpCycOf.algSat`). -/
def algSat (n q : ℕ) (B : Multiset ℂˣ) : Multiset ℂ :=
  B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ)

theorem algSat_card (n q : ℕ) (B : Multiset ℂˣ) : (algSat n q B).card = B.card := by
  simp [algSat]

/-- Exact Frobenius-power compatibility for algebraic Satake parameters
(mirroring `UpCycOf.algSat_pow`). -/
theorem algSat_pow (n q f : ℕ) (B : Multiset ℂˣ) :
    algSat n (q ^ f) (B.map (· ^ f)) = (algSat n q B).map (· ^ f) := by
  simp only [algSat, Multiset.map_map, Function.comp_def]
  refine Multiset.map_congr rfl fun α _ => ?_
  have hr : ((q ^ f : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) = ((q : ℝ) ^ (((n : ℝ) - 1) / 2)) ^ f := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_natCast,
      ← Real.rpow_mul (Nat.cast_nonneg q), ← Real.rpow_mul (Nat.cast_nonneg q), mul_comm]
  rw [hr, mul_pow, Units.val_pow_eq_pow_val, Complex.ofReal_pow]

theorem algSat_pow_one (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n (q ^ 1) (B.map (· ^ 1)) = algSat n q B := by
  simp [algSat]

theorem algSat_twist (n q : ℕ) (B : Multiset ℂˣ) (c : ℂˣ) :
    algSat n q (B.map (· * c)) = (algSat n q B).map (· * (c : ℂ)) := by
  simp only [algSat, Multiset.map_map, Function.comp_def]
  refine Multiset.map_congr rfl fun α _ => ?_
  simp only [Units.val_mul, mul_assoc]

/-- Monic characteristic polynomial attached to a multiset of complex eigenvalues:
`∏_{α ∈ A} (X - α)`. -/
def eigPoly (A : Multiset ℂ) : Polynomial ℂ :=
  (A.map fun α => Polynomial.X - Polynomial.C α).prod

theorem eigPoly_zero : eigPoly 0 = 1 := by
  simp [eigPoly]

theorem eigPoly_cons (a : ℂ) (A : Multiset ℂ) :
    eigPoly (a ::ₘ A) = (Polynomial.X - Polynomial.C a) * eigPoly A := by
  simp [eigPoly]

theorem eigPoly_add (A B : Multiset ℂ) : eigPoly (A + B) = eigPoly A * eigPoly B := by
  simp [eigPoly, Multiset.map_add, Multiset.prod_add]

theorem eigPoly_monic (A : Multiset ℂ) : (eigPoly A).Monic := by
  induction A using Multiset.induction_on with
  | empty => simp [eigPoly]
  | cons a s ih =>
    rw [eigPoly_cons]
    exact (Polynomial.monic_X_sub_C a).mul ih

theorem eigPoly_ne_zero (A : Multiset ℂ) : eigPoly A ≠ 0 :=
  (eigPoly_monic A).ne_zero

theorem eigPoly_natDegree (A : Multiset ℂ) : (eigPoly A).natDegree = A.card := by
  induction A using Multiset.induction_on with
  | empty => simp [eigPoly]
  | cons a s ih =>
    rw [eigPoly_cons, (Polynomial.monic_X_sub_C a).natDegree_mul (eigPoly_monic s),
      Polynomial.natDegree_X_sub_C, ih, Multiset.card_cons, add_comm]

theorem eigPoly_roots (A : Multiset ℂ) : (eigPoly A).roots = A := by
  induction A using Multiset.induction_on with
  | empty => simp [eigPoly]
  | cons a s ih =>
    rw [eigPoly_cons,
      Polynomial.roots_mul (mul_ne_zero (Polynomial.monic_X_sub_C a).ne_zero (eigPoly_ne_zero s)),
      Polynomial.roots_X_sub_C, ih, Multiset.singleton_add]

/-- **Eigenvalue Multiset Uniqueness**: Two multisets of Frobenius eigenvalues with the same
characteristic polynomial are equal. -/
theorem multiset_eq_of_eigPoly_eq {A B : Multiset ℂ} (h : eigPoly A = eigPoly B) : A = B := by
  rw [← eigPoly_roots A, ← eigPoly_roots B, h]

/-- **Quadratic Inert-Place Induction Identity** (mirroring `QuadraticInductionGL2Alt.IndSys`
and `IndCh`): adding negated eigenvalues pairs `(X - b)(X + b) = X^2 - b^2`. -/
theorem eigPoly_quad_inert (B : Multiset ℂ) :
    eigPoly (B + B.map fun b => -b) = (eigPoly (B.map (· ^ 2))).comp (Polynomial.X ^ 2) := by
  induction B using Multiset.induction_on with
  | empty => simp [eigPoly]
  | cons b s ih =>
    have hsplit : (b ::ₘ s) + (b ::ₘ s).map (fun x => -x) =
        b ::ₘ (-b) ::ₘ (s + s.map fun x => -x) := by
      simp only [Multiset.map_cons, Multiset.cons_add, Multiset.add_cons]
      exact Multiset.cons_swap (-b) b _
    rw [hsplit, eigPoly_cons, eigPoly_cons, ih, Multiset.map_cons, eigPoly_cons,
      Polynomial.mul_comp, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
    have hpair : (Polynomial.X - Polynomial.C b) * (Polynomial.X - Polynomial.C (-b)) =
        Polynomial.X ^ 2 - Polynomial.C (b ^ 2) := by
      rw [map_neg, sub_neg_eq_add, map_pow]
      ring
    rw [← mul_assoc, hpair]

/-! ## 3. Strong Multiplicity One, Cofinite Satake Systems & Cyclic-Group Twist Invariance -/

/-- Abstract cuspidal Satake-parameter system of rank `n` with character twists and Strong
Multiplicity One (distilling `CycFree.lean` and `SolvableEquivalenceOfBaseChange.lean`). -/
structure SatakeSystem where
  /-- Finite places of the number field. -/
  Place : Type
  /-- Automorphic / cuspidal representations of rank `rank`. -/
  Rep : Type
  /-- Hecke / idele-class characters acting by twisting. -/
  Char : Type
  [charGroup : CommGroup Char]
  /-- Rank `n ≥ 1` of the `GL_n` representations. -/
  rank : ℕ
  rank_pos : 1 ≤ rank
  /-- Local Satake parameter relation `sat π v B`. -/
  sat : Rep → Place → Multiset ℂˣ → Prop
  /-- Every Satake parameter multiset has cardinality `rank`. -/
  sat_card : ∀ π v B, sat π v B → B.card = rank
  /-- Uniqueness of the Satake parameter at each unramified place (`cusp_unique`). -/
  sat_unique : ∀ π v B₁ B₂, sat π v B₁ → sat π v B₂ → B₁ = B₂
  /-- Cofinite existence of unramified Satake parameters (`SatakeParameterExistence`). -/
  sat_exists_cofinite : ∀ π, ∀ᶠ v in cofinite, ∃ B, sat π v B
  /-- Isomorphism equivalence relation on representations. -/
  iso : Rep → Rep → Prop
  iso_refl : ∀ π, iso π π
  iso_symm : ∀ {π₁ π₂}, iso π₁ π₂ → iso π₂ π₁
  iso_trans : ∀ {π₁ π₂ π₃}, iso π₁ π₂ → iso π₂ π₃ → iso π₁ π₃
  /-- Isomorphic representations share the same Satake parameters. -/
  iso_sat : ∀ {π₁ π₂}, iso π₁ π₂ → ∀ v B, sat π₁ v B → sat π₂ v B
  /-- Character twist `π ↦ π ⊗ η`. -/
  twist : Rep → Char → Rep
  /-- Local character value `η(ϖ_v) ∈ ℂˣ` at unramified places. -/
  charVal : Char → Place → ℂˣ
  /-- Multiplicativity of local character values (cofinitely). -/
  charVal_one : ∀ᶠ v in cofinite, charVal 1 v = 1
  charVal_mul : ∀ η₁ η₂, ∀ᶠ v in cofinite, charVal (η₁ * η₂) v = charVal η₁ v * charVal η₂ v
  /-- Twist preserves `iso` and forms a group action up to `iso`. -/
  twist_iso : ∀ {π₁ π₂} (η : Char), iso π₁ π₂ → iso (twist π₁ η) (twist π₂ η)
  twist_one : ∀ π, iso (twist π 1) π
  twist_mul : ∀ π η₁ η₂, iso (twist (twist π η₁) η₂) (twist π (η₁ * η₂))
  /-- Cofinite Satake parameter law for twists (`STwSat`). -/
  twist_sat : ∀ π η, ∀ᶠ v in cofinite, ∀ B, sat π v B → sat (twist π η) v (B.map (· * charVal η v))
  /-- **Strong Multiplicity One**: Cofinite Satake agreement implies isomorphism (`smo0`). -/
  strongMultOne : ∀ {π₁ π₂},
    (∀ᶠ v in cofinite, ∃ B, sat π₁ v B ∧ sat π₂ v B) → iso π₁ π₂

attribute [instance] SatakeSystem.charGroup

namespace SatakeSystem

variable {S : SatakeSystem}

/-- Strong Multiplicity One from pointwise Satake parameter equality on a cofinite set. -/
theorem iso_of_sat_cofinite_eq {π₁ π₂ : S.Rep}
    (h : ∀ᶠ v in cofinite, ∀ B, S.sat π₁ v B → S.sat π₂ v B) : S.iso π₁ π₂ := by
  refine S.strongMultOne ?_
  filter_upwards [S.sat_exists_cofinite π₁, h] with v ⟨B, hB⟩ h12
  exact ⟨B, hB, h12 B hB⟩

/-- **Conjugate-Invariance from Satake Pullback** (faithful abstract counterpart of
`CycFree.conjIso0`): if `conjAct π` pulls back Satake parameters along `g : Place → Place`
and `π` has `g`-invariant Satake parameters cofinally, then `StrongMultOne` gives
`iso (conjAct π) π`. -/
theorem conj_iso_of_sat_invariant (π π' : S.Rep) (g : S.Place → S.Place)
    (hpull : ∀ᶠ w in cofinite, ∀ B, S.sat π (g w) B → S.sat π' w B)
    (hinv : ∀ᶠ w in cofinite, ∃ B, S.sat π w B ∧ S.sat π (g w) B) :
    S.iso π' π := by
  refine S.strongMultOne ?_
  filter_upwards [hpull, hinv] with w hp ⟨B, hB1, hB2⟩
  exact ⟨B, hp B hB2, hB1⟩

/-- **Abstract Cyclic-Group Action Invariance**: A group action of a cyclic group `Γ = ⟨g₀⟩`
preserving `S.iso` fixes `π` on all of `Γ` iff the generator `g₀` fixes `π`. -/
theorem cyclic_action_invariant_iff_gen {Γ : Type} [Group Γ] (act : Γ → S.Rep → S.Rep)
    (hact_one : ∀ x, S.iso (act 1 x) x)
    (hact_mul : ∀ g h x, S.iso (act (g * h) x) (act g (act h x)))
    (hact_iso : ∀ g {x y}, S.iso x y → S.iso (act g x) (act g y))
    (g₀ : Γ) (hgen : Subgroup.zpowers g₀ = ⊤) (π : S.Rep) :
    (∀ g : Γ, S.iso (act g π) π) ↔ S.iso (act g₀ π) π := by
  constructor
  · intro hall
    exact hall g₀
  · intro h0
    have hinv : S.iso (act g₀⁻¹ π) π := by
      have h1 : S.iso (act g₀⁻¹ (act g₀ π)) (act g₀⁻¹ π) := hact_iso g₀⁻¹ h0
      have h2 : S.iso (act (g₀⁻¹ * g₀) π) (act g₀⁻¹ (act g₀ π)) := hact_mul g₀⁻¹ g₀ π
      rw [inv_mul_cancel] at h2
      exact S.iso_trans (S.iso_symm h1) (S.iso_trans (S.iso_symm h2) (hact_one π))
    have hnat : ∀ m : ℕ, S.iso (act (g₀ ^ m) π) π := by
      intro m
      induction m with
      | zero => simpa using hact_one π
      | succ m ih =>
        rw [pow_succ']
        exact S.iso_trans (hact_mul g₀ (g₀ ^ m) π) (S.iso_trans (hact_iso g₀ ih) h0)
    have hnatInv : ∀ m : ℕ, S.iso (act ((g₀⁻¹) ^ m) π) π := by
      intro m
      induction m with
      | zero => simpa using hact_one π
      | succ m ih =>
        rw [pow_succ']
        exact S.iso_trans (hact_mul g₀⁻¹ ((g₀⁻¹) ^ m) π) (S.iso_trans (hact_iso g₀⁻¹ ih) hinv)
    intro g
    have hg : g ∈ Subgroup.zpowers g₀ := hgen.symm ▸ Subgroup.mem_top g
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    cases k with
    | ofNat m => simpa using hnat m
    | negSucc m =>
      rw [zpow_negSucc, ← inv_pow]
      exact hnatInv (m + 1)

/-- Twisting by `η⁻¹` cancels twisting by `η` up to `S.iso`. -/
theorem twist_inv_cancel (π : S.Rep) (η : S.Char) :
    S.iso (S.twist (S.twist π η) η⁻¹) π :=
  S.iso_trans (S.twist_mul π η η⁻¹) (by simpa [mul_inv_cancel] using S.twist_one π)

/-- **Self-Twist Rank-Power Law**: If `π ⊗ η ≅ π`, then `η(ϖ_v)^rank = 1` for all but
finitely many places `v`. -/
theorem self_twist_char_pow_rank {π : S.Rep} {η : S.Char} (h : S.iso (S.twist π η) π) :
    ∀ᶠ v in cofinite, (S.charVal η v) ^ S.rank = 1 := by
  filter_upwards [S.sat_exists_cofinite π, S.twist_sat π η] with v ⟨B, hB⟩ htw
  have hB' : S.sat π v (B.map (· * S.charVal η v)) := S.iso_sat h v _ (htw B hB)
  have heq : B.map (· * S.charVal η v) = B := S.sat_unique π v _ _ hB' hB
  have hcard : B.card = S.rank := S.sat_card π v B hB
  rw [← hcard]
  exact multiset_map_mul_eq_self_pow_card B (S.charVal η v) heq

/-- **Coprime Prime-Order Self-Twist Rigidity**: If `π ⊗ η ≅ π`, `η(ϖ_v)^p = 1` cofinally,
and `Nat.Coprime p S.rank`, then `η(ϖ_v) = 1` cofinally. -/
theorem self_twist_trivial_of_coprime {π : S.Rep} {η : S.Char} {p : ℕ}
    (h : S.iso (S.twist π η) π) (hp : ∀ᶠ v in cofinite, (S.charVal η v) ^ p = 1)
    (hcop : Nat.Coprime p S.rank) :
    ∀ᶠ v in cofinite, S.charVal η v = 1 := by
  filter_upwards [S.sat_exists_cofinite π, S.twist_sat π η, hp] with v ⟨B, hB⟩ htw hvp
  have hB' : S.sat π v (B.map (· * S.charVal η v)) := S.iso_sat h v _ (htw B hB)
  have heq : B.map (· * S.charVal η v) = B := S.sat_unique π v _ _ hB' hB
  have hcard : B.card = S.rank := S.sat_card π v B hB
  exact multiset_map_mul_eq_self_eq_one_of_coprime B (S.charVal η v) heq hvp (hcard ▸ hcop)

/-- **Rank-1 Self-Twist Rigidity**: For `rank = 1`, `π ⊗ η ≅ π` forces `η(ϖ_v) = 1` cofinally. -/
theorem self_twist_rank_one_trivial (hr1 : S.rank = 1) {π : S.Rep} {η : S.Char}
    (h : S.iso (S.twist π η) π) : ∀ᶠ v in cofinite, S.charVal η v = 1 := by
  filter_upwards [S.self_twist_char_pow_rank h] with v hv
  rwa [hr1, pow_one] at hv

/-- **Character-Twist Rigidity (Injectivity on Twists)**: If no nontrivial character in a
subgroup `H ≤ S.Char` self-twists `π`, then the map `η ↦ π ⊗ η` is injective up to `S.iso`
on `H`. -/
theorem twist_injective_of_no_self_twist (H : Subgroup S.Char) (π : S.Rep)
    (hno : ∀ η ∈ H, S.iso (S.twist π η) π → η = 1)
    {η₁ η₂ : S.Char} (h1 : η₁ ∈ H) (h2 : η₂ ∈ H)
    (hiso : S.iso (S.twist π η₁) (S.twist π η₂)) : η₁ = η₂ := by
  have hinv : S.iso (S.twist (S.twist π η₁) η₂⁻¹) π :=
    S.iso_trans (S.twist_iso η₂⁻¹ hiso) (S.twist_inv_cancel π η₂)
  have hprod : S.iso (S.twist π (η₁ * η₂⁻¹)) π :=
    S.iso_trans (S.iso_symm (S.twist_mul π η₁ η₂⁻¹)) hinv
  have hmem : η₁ * η₂⁻¹ ∈ H := H.mul_mem h1 (H.inv_mem h2)
  exact mul_inv_eq_one.mp (hno (η₁ * η₂⁻¹) hmem hprod)

/-- Stabilizer of `π` under character twisting is a subgroup of `S.Char`. -/
def twistStabilizer (π : S.Rep) : Subgroup S.Char where
  carrier := {η | S.iso (S.twist π η) π}
  mul_mem' := by
    intro η₁ η₂ h1 h2
    exact S.iso_trans (S.iso_symm (S.twist_mul π η₁ η₂))
      (S.iso_trans (S.twist_iso η₂ h1) h2)
  one_mem' := S.twist_one π
  inv_mem' := by
    intro η hη
    exact S.iso_trans (S.iso_symm (S.twist_iso η⁻¹ hη)) (S.twist_inv_cancel π η)

/-- If a prime-order cyclic character group `H` acts on `π`, then either `π` has trivial
stabilizer in `H` (faithful orbit of size `p`), or `H` fixes `π` completely. -/
theorem twistStabilizer_prime_dichotomy (H : Subgroup S.Char) {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card H = p) (π : S.Rep) :
    (∀ η ∈ H, S.iso (S.twist π η) π → η = 1) ∨ (∀ η ∈ H, S.iso (S.twist π η) π) := by
  let K : Subgroup H := (S.twistStabilizer π).subgroupOf H
  have hdvd : Nat.card K ∣ Nat.card H := Subgroup.card_subgroup_dvd_card K
  rw [hcard] at hdvd
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp'
  · left
    intro η hη hiso
    have hmem : (⟨η, hη⟩ : H) ∈ K := hiso
    have hKbot : K = ⊥ := (Subgroup.card_eq_one (H := K)).mp h1
    rw [hKbot, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · right
    intro η hη
    have : Finite H := Nat.finite_of_card_ne_zero (hcard ▸ hp.ne_zero)
    have hKtop : K = ⊤ := Subgroup.eq_top_of_card_eq K (hp'.trans hcard.symm)
    have hmem : (⟨η, hη⟩ : H) ∈ K := hKtop.symm ▸ Subgroup.mem_top _
    exact hmem

end SatakeSystem

/-! ## 4. Prime-Degree Cyclic Base Change (`BaseChangeStep`) & Frobenius-Eigenvalue Descent -/

/-- Abstract place-extension datum between a base number field `K` and a finite extension `M`
(capturing `w.under (𝓞 K)`, `w.asIdeal.inertiaDeg (𝓞 K)`, `normV_under`, and finite fibers). -/
structure PlaceExtension (PlaceK PlaceM : Type) where
  under : PlaceM → PlaceK
  inertia : PlaceM → ℕ
  inertia_pos : ∀ w, 0 < inertia w
  normK : PlaceK → ℕ
  normM : PlaceM → ℕ
  norm_under : ∀ w, normM w = normK (under w) ^ inertia w
  under_tendsto_cofinite : Tendsto under cofinite cofinite

/-- Local unramified base-change relation between `π` over `K` and `P` over `M`:
cofinitely, `B_w = B_{w|K}^{f(w/v)}`. -/
def IsLocalBaseChange {S_K S_M : SatakeSystem} (ext : PlaceExtension S_K.Place S_M.Place)
    (π : S_K.Rep) (P : S_M.Rep) : Prop :=
  ∀ᶠ w in cofinite, ∃ B, S_K.sat π (ext.under w) B ∧ S_M.sat P w (B.map (· ^ ext.inertia w))

/-- Cofinite fiber-invariance of Satake parameters of `P` across Galois-conjugate places over
the same place of `K` with the same inertia degree. -/
def IsFiberInvariant {S_K S_M : SatakeSystem} (ext : PlaceExtension S_K.Place S_M.Place)
    (P : S_M.Rep) : Prop :=
  ∀ᶠ w in cofinite, ∀ w' : S_M.Place,
    ext.under w' = ext.under w → ext.inertia w' = ext.inertia w →
    ∃ B, S_M.sat P w B ∧ S_M.sat P w' B

/-- Prime-degree cyclic base-change package between `S_K` and `S_M` (distilling the exact 3
laws of `CycC` in `CycFree.lean` together with the cyclic extension character subgroup `H`). -/
structure BaseChangeStep (S_K S_M : SatakeSystem) where
  /-- Degree `p` of the cyclic extension `M / K` (`p.Prime`). -/
  p : ℕ
  p_prime : p.Prime
  /-- Rank compatibility `n_M = n_K`. -/
  rank_eq : S_M.rank = S_K.rank
  /-- Underlying place extension `Place_M → Place_K`. -/
  ext : PlaceExtension S_K.Place S_M.Place
  /-- Regularity predicate on representations (e.g. regular algebraic cuspidal). -/
  IsRegK : S_K.Rep → Prop
  IsRegM : S_M.Rep → Prop
  isRegK_iso : ∀ {π₁ π₂}, S_K.iso π₁ π₂ → IsRegK π₁ → IsRegK π₂
  isRegK_twist : ∀ {π} {η}, IsRegK π → IsRegK (S_K.twist π η)
  /-- The cyclic subgroup `H ≤ S_K.Char` of characters trivial on `N_{M/K}(𝔸_Mˣ)` (order `p`). -/
  cyclicChars : Subgroup S_K.Char
  cyclicChars_card : Nat.card cyclicChars = p
  cyclicChars_pow : ∀ η ∈ cyclicChars, ∀ᶠ v in cofinite, (S_K.charVal η v) ^ p = 1
  /-- Faithfulness of local character evaluation on `cyclicChars` (Chebotarev / Artin):
  a nontrivial character in `cyclicChars` cannot equal `1` cofinally. -/
  cyclicChars_faithful : ∀ η ∈ cyclicChars,
    (∀ᶠ v in cofinite, S_K.charVal η v = 1) → η = 1
  /-- Law 1 (Base-Change Lifting, `CycC.1`): every regular `π` over `K` either admits a
  nontrivial self-twist `η ∈ cyclicChars` or lifts to a regular `P` over `M`. -/
  lift : ∀ π, IsRegK π →
    (∃ η ∈ cyclicChars, η ≠ 1 ∧ S_K.iso (S_K.twist π η) π) ∨
      (∃ P, IsRegM P ∧ IsLocalBaseChange ext π P)
  /-- Law 2 (Cyclic Descent, `CycC.2`): every regular fiber-invariant `P` over `M` descends
  to a regular `π` over `K`. -/
  descent : ∀ P, IsRegM P → IsFiberInvariant ext P →
    ∃ π, IsRegK π ∧ IsLocalBaseChange ext π P
  /-- Law 3 (Fiber Rigidity, `CycC.3`): any two descents of the same `P` differ by a twist
  from `cyclicChars`. -/
  fiber : ∀ π₁ π₂ P, IsLocalBaseChange ext π₁ P → IsLocalBaseChange ext π₂ P →
    ∃ η ∈ cyclicChars, S_K.iso π₂ (S_K.twist π₁ η)

namespace BaseChangeStep

variable {S_K S_M : SatakeSystem} (step : BaseChangeStep S_K S_M)

/-- Algebraic Satake Frobenius-power compatibility along `IsLocalBaseChange`. -/
theorem algSat_compat {π : S_K.Rep} {P : S_M.Rep} (hbc : IsLocalBaseChange step.ext π P) :
    ∀ᶠ w in cofinite, ∃ B_v B_w,
      S_K.sat π (step.ext.under w) B_v ∧ S_M.sat P w B_w ∧
      algSat S_K.rank (step.ext.normM w) B_w =
        (algSat S_K.rank (step.ext.normK (step.ext.under w)) B_v).map (· ^ step.ext.inertia w) := by
  filter_upwards [hbc] with w ⟨B, hBv, hBw⟩
  refine ⟨B, B.map (· ^ step.ext.inertia w), hBv, hBw, ?_⟩
  rw [step.ext.norm_under w, algSat_pow]

/-- **Strong Multiplicity One for Cyclic Base-Change Lifts**: Any two base-change lifts of the
same `π` over `K` are isomorphic over `M`. -/
theorem lift_unique {π : S_K.Rep} {P₁ P₂ : S_M.Rep}
    (h1 : IsLocalBaseChange step.ext π P₁) (h2 : IsLocalBaseChange step.ext π P₂) :
    S_M.iso P₁ P₂ := by
  refine S_M.strongMultOne ?_
  filter_upwards [h1, h2] with w ⟨B₁, hB₁K, hB₁M⟩ ⟨B₂, hB₂K, hB₂M⟩
  have heq : B₁ = B₂ := S_K.sat_unique π (step.ext.under w) B₁ B₂ hB₁K hB₂K
  subst heq
  exact ⟨B₁.map (· ^ step.ext.inertia w), hB₁M, hB₂M⟩

/-- Every base-change lift `P` of `π` is automatically fiber-invariant across places over the
same place of `K` with equal inertia degree. -/
theorem lift_fiber_invariant {π : S_K.Rep} {P : S_M.Rep}
    (hbc : IsLocalBaseChange step.ext π P) :
    IsFiberInvariant step.ext P := by
  have hbad : {w : S_M.Place | ¬∃ B, S_K.sat π (step.ext.under w) B ∧
      S_M.sat P w (B.map (· ^ step.ext.inertia w))}.Finite :=
    Filter.eventually_cofinite.mp hbc
  let badK : Set S_K.Place := step.ext.under '' {w : S_M.Place |
    ¬∃ B, S_K.sat π (step.ext.under w) B ∧ S_M.sat P w (B.map (· ^ step.ext.inertia w))}
  have hbadK_fin : badK.Finite := hbad.image step.ext.under
  have hbadK_ev : ∀ᶠ v in cofinite, v ∉ badK :=
    Filter.eventually_cofinite.mpr (by simpa using hbadK_fin)
  have hpre : ∀ᶠ w in cofinite, step.ext.under w ∉ badK :=
    step.ext.under_tendsto_cofinite.eventually hbadK_ev
  filter_upwards [hbc, hpre] with w ⟨B, hBv, hBw⟩ hgood w' hund hiner
  have hw' : ∃ B', S_K.sat π (step.ext.under w') B' ∧
      S_M.sat P w' (B'.map (· ^ step.ext.inertia w')) := by
    by_contra hnot
    exact hgood ⟨w', hnot, hund⟩
  obtain ⟨B', hB'v, hB'w⟩ := hw'
  rw [hund] at hB'v
  have heq : B' = B := S_K.sat_unique π (step.ext.under w) B' B hB'v hBv
  rw [heq, hiner] at hB'w
  exact ⟨B.map (· ^ step.ext.inertia w), hBw, hB'w⟩

/-- **Unconditional Lifting without Self-Twists** (mirroring `WideOfCyclic.lean`):
If `π` admits no nontrivial self-twist in `cyclicChars`, it lifts uniquely to `M`. -/
theorem lift_of_no_self_twist {π : S_K.Rep} (hreg : step.IsRegK π)
    (hno : ∀ η ∈ step.cyclicChars, η ≠ 1 → ¬S_K.iso (S_K.twist π η) π) :
    ∃ P, step.IsRegM P ∧ IsLocalBaseChange step.ext π P :=
  (step.lift π hreg).resolve_left fun ⟨η, hη, hne, hiso⟩ => hno η hη hne hiso

/-- **Coprime Prime-Rank Unconditional Lifting**: Whenever `Nat.Coprime step.p S_K.rank`,
no representation can have a nontrivial self-twist of prime order `p`, so EVERY regular `π`
lifts unconditionally across the cyclic prime extension! -/
theorem lift_of_coprime_prime_rank (hcop : Nat.Coprime step.p S_K.rank)
    {π : S_K.Rep} (hreg : step.IsRegK π) :
    ∃ P, step.IsRegM P ∧ IsLocalBaseChange step.ext π P := by
  refine step.lift_of_no_self_twist hreg fun η hη hne hiso => hne ?_
  exact step.cyclicChars_faithful η hη
    (S_K.self_twist_trivial_of_coprime hiso (step.cyclicChars_pow η hη) hcop)

/-- **Rank-2 Cyclic Base-Change Dichotomy** (mirroring `QuadBC2.lean` &
`CyclicLiftRankTwoOfCyclicBaseChange.lean`): a regular rank-2 representation over `K` is
either dihedral (self-twisted by a nontrivial character of `M/K`) or admits a unique
regular cuspidal base-change lift to `M`. -/
theorem rankTwo_dichotomy (hr2 : S_K.rank = 2) {π : S_K.Rep} (hreg : step.IsRegK π) :
    (∃ η ∈ step.cyclicChars, η ≠ 1 ∧ S_K.iso (S_K.twist π η) π) ∨
      (∃ P, step.IsRegM P ∧ IsLocalBaseChange step.ext π P ∧
        ∀ P', IsLocalBaseChange step.ext π P' → S_M.iso P P') := by
  have _ := hr2
  rcases step.lift π hreg with hdih | ⟨P, hregM, hbc⟩
  · exact Or.inl hdih
  · exact Or.inr ⟨P, hregM, hbc, fun P' hbc' => step.lift_unique hbc hbc'⟩

/-- **Rank-2 Odd-Prime Unconditional Lifting**: For any odd prime `p ≠ 2`, `gcd(p, 2) = 1`,
so EVERY regular rank-2 representation lifts unconditionally across a degree-`p` cyclic
extension with no dihedral obstruction! -/
theorem rankTwo_odd_prime_lift (hr2 : S_K.rank = 2) (hodd : step.p ≠ 2)
    {π : S_K.Rep} (hreg : step.IsRegK π) :
    ∃ P, step.IsRegM P ∧ IsLocalBaseChange step.ext π P := by
  have hcop : Nat.Coprime step.p S_K.rank := by
    rw [hr2]
    exact (step.p_prime.coprime_iff_not_dvd).mpr fun hd =>
      hodd ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left step.p_prime.ne_one)
  exact step.lift_of_coprime_prime_rank hcop hreg

/-- **Rank-1 Unconditional Lifting**: Every rank-1 representation lifts unconditionally across
every cyclic prime extension. -/
theorem rankOne_lift (hr1 : S_K.rank = 1) {π : S_K.Rep} (hreg : step.IsRegK π) :
    ∃ P, step.IsRegM P ∧ IsLocalBaseChange step.ext π P :=
  step.lift_of_coprime_prime_rank (by rw [hr1]; exact Nat.coprime_one_right step.p) hreg

end BaseChangeStep

/-! ### Frobenius-Eigenvalue Attachment & Descent across a Cyclic Prime Step -/

/-- Abstract global Galois representation level coupled to a `SatakeSystem` via Frobenius
eigenvalues (distilling `IsAut`, `AttachedSys`, `FrobEig` in `SolvableEquivalenceOfBaseChange.lean`). -/
structure BaseChangeLevel where
  S : SatakeSystem
  norm : S.Place → ℕ
  IsReg : S.Rep → Prop
  isReg_iso : ∀ {π₁ π₂}, S.iso π₁ π₂ → IsReg π₁ → IsReg π₂
  isReg_twist : ∀ {π} {η}, IsReg π → IsReg (S.twist π η)
  /-- Global `l`-adic Galois representations `G_K → GL_n(Qbar_l)`. -/
  GalRep : Type
  IsIrr : GalRep → Prop
  /-- Frobenius eigenvalue multiset at unramified places `v`. -/
  frobEig : GalRep → S.Place → Multiset ℂ → Prop
  frobEig_unique : ∀ r v A₁ A₂, frobEig r v A₁ → frobEig r v A₂ → A₁ = A₂

namespace BaseChangeLevel

/-- A Galois representation `r` is attached to an automorphic representation `π` if their
Frobenius and algebraic Satake eigenvalue multisets match cofinally. -/
def IsAttached (L : BaseChangeLevel) (r : L.GalRep) (π : L.S.Rep) : Prop :=
  ∀ᶠ v in cofinite, ∃ B, L.S.sat π v B ∧ L.frobEig r v (algSat L.S.rank (L.norm v) B)

/-- Automorphy of a Galois representation `r`: `r` is attached to some regular `π`. -/
def IsAut (L : BaseChangeLevel) (r : L.GalRep) : Prop :=
  ∃ π, L.IsReg π ∧ L.IsAttached r π

/-- Attachment is invariant under `S.iso`. -/
theorem isAttached_of_iso {L : BaseChangeLevel} {r : L.GalRep} {π₁ π₂ : L.S.Rep}
    (hiso : L.S.iso π₁ π₂) (hatt : L.IsAttached r π₁) : L.IsAttached r π₂ := by
  filter_upwards [hatt] with v ⟨B, hB, hF⟩
  exact ⟨B, L.S.iso_sat hiso v B hB, hF⟩

/-- **Strong Multiplicity One for Attached Automorphic Representations**: Any two automorphic
representations attached to the same Galois representation `r` are isomorphic! -/
theorem attached_unique {L : BaseChangeLevel} {r : L.GalRep} {π₁ π₂ : L.S.Rep}
    (hnorm_pos : ∀ᶠ v in cofinite, 0 < L.norm v)
    (h1 : L.IsAttached r π₁) (h2 : L.IsAttached r π₂) :
    L.S.iso π₁ π₂ := by
  refine L.S.strongMultOne ?_
  filter_upwards [hnorm_pos, h1, h2] with v hpos ⟨B₁, hB₁, hF₁⟩ ⟨B₂, hB₂, hF₂⟩
  have halg : algSat L.S.rank (L.norm v) B₁ = algSat L.S.rank (L.norm v) B₂ :=
    L.frobEig_unique r v _ _ hF₁ hF₂
  have hscale_ne : (((L.norm v : ℝ) ^ (((L.S.rank : ℝ) - 1) / 2) : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hpos) _).ne'
  have hinj : Function.Injective (fun α : ℂˣ =>
      (((L.norm v : ℝ) ^ (((L.S.rank : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ)) := by
    intro α₁ α₂ h
    exact Units.ext (mul_left_cancel₀ hscale_ne h)
  have heq : B₁ = B₂ := Multiset.map_injective hinj halg
  subst heq
  exact ⟨B₁, hB₁, hB₂⟩

end BaseChangeLevel

/-- A prime-degree cyclic Galois base-change step `L₁ → L₂` coupling `BaseChangeStep` with
Galois restriction `res : L₁.GalRep → L₂.GalRep`, Frobenius-power compatibility, and
Chebotarev / Brauer–Nesbitt twist descent. -/
structure BaseChangeGalStep (L₁ L₂ : BaseChangeLevel) where
  step : BaseChangeStep L₁.S L₂.S
  normK_eq : step.ext.normK = L₁.norm
  normM_eq : step.ext.normM = L₂.norm
  isRegK_eq : step.IsRegK = L₁.IsReg
  isRegM_eq : step.IsRegM = L₂.IsReg
  /-- Galois restriction `r ↦ r|_{G_M}`. -/
  res : L₁.GalRep → L₂.GalRep
  /-- Irreducibility of `r|_{G_M}` implies irreducibility of `r`. -/
  isIrr_of_res : ∀ r, L₂.IsIrr (res r) → L₁.IsIrr r
  /-- Frobenius-power compatibility on restricted representations:
  `Frob_w(r|_M) = Frob_{w|K}(r)^{f(w/v)}`. -/
  frob_res : ∀ r w A, L₁.frobEig r (step.ext.under w) A →
    L₂.frobEig (res r) w (A.map (· ^ step.ext.inertia w))
  /-- Conjugate places over the same place of `K` with equal inertia have identical
  Frobenius eigenvalues on `r|_M` (conjugate matrices have identical characteristic polynomials). -/
  frob_fiber_eq : ∀ r, ∀ᶠ w in cofinite, ∀ w' : L₂.S.Place,
    step.ext.under w' = step.ext.under w → step.ext.inertia w' = step.ext.inertia w →
    ∀ A, L₂.frobEig (res r) w A → L₂.frobEig (res r) w' A
  /-- Irreducibility of `r|_M` rules out nontrivial self-twist of an attached `π`
  (mirroring `noTwist` / `SelfTwGal`). -/
  irred_no_self_twist : ∀ r π, L₂.IsIrr (res r) → L₁.IsAttached r π →
    ∀ η ∈ step.cyclicChars, η ≠ 1 → ¬L₁.S.iso (L₁.S.twist π η) π
  /-- **Frobenius-Twist Descent Identification** (mirroring `IsoOfFrobOne` + Schur's lemma
  for cyclic prime quotient `G_K / G_M`): if `r|_M` is irreducible and attached to `P`, and
  `π` over `K` base-changes to `P`, then `r` is attached to some cyclic character twist
  `π ⊗ η` (`η ∈ step.cyclicChars`). -/
  descent_twist_match : ∀ r π P, L₂.IsIrr (res r) → L₁.IsReg π →
    L₂.IsAttached (res r) P → IsLocalBaseChange step.ext π P →
    ∃ η ∈ step.cyclicChars, L₁.IsAttached r (L₁.S.twist π η)
  /-- Positive residue norms cofinally on `L₂`. -/
  normM_pos : ∀ᶠ w in cofinite, 0 < L₂.norm w

namespace BaseChangeGalStep

variable {L₁ L₂ : BaseChangeLevel} (G : BaseChangeGalStep L₁ L₂)

/-- **Frobenius-Eigenvalue Base-Change Lifting**: If `r|_{G_M}` is irreducible and `r` is
automorphic over `K`, then `r|_{G_M}` is automorphic over `M`. -/
theorem frob_lift {r : L₁.GalRep} (hirr : L₂.IsIrr (G.res r)) (haut : L₁.IsAut r) :
    L₂.IsAut (G.res r) := by
  obtain ⟨π, hreg, hatt⟩ := haut
  have hreg' : G.step.IsRegK π := G.isRegK_eq ▸ hreg
  obtain ⟨P, hregM, hbc⟩ :=
    G.step.lift_of_no_self_twist hreg' (G.irred_no_self_twist r π hirr hatt)
  refine ⟨P, G.isRegM_eq ▸ hregM, ?_⟩
  have hatt_up := G.step.ext.under_tendsto_cofinite.eventually hatt
  filter_upwards [hbc, hatt_up] with w ⟨B, hBv, hBw⟩ ⟨B', hB'v, hF⟩
  have heq : B' = B := L₁.S.sat_unique π (G.step.ext.under w) B' B hB'v hBv
  rw [heq] at hF
  refine ⟨B.map (· ^ G.step.ext.inertia w), hBw, ?_⟩
  have hF' := G.frob_res r w _ hF
  have hrank : L₂.S.rank = L₁.S.rank := G.step.rank_eq
  have hnorm : L₂.norm w = L₁.norm (G.step.ext.under w) ^ G.step.ext.inertia w := by
    rw [← G.normM_eq, ← G.normK_eq, G.step.ext.norm_under w]
  rw [hrank, hnorm, algSat_pow]
  exact hF'

/-- If `r|_{G_M}` is attached to `P`, then `P` is automatically fiber-invariant across
Galois-conjugate places over `K`. -/
theorem fiber_invariant_of_attached_res {r : L₁.GalRep} {P : L₂.S.Rep}
    (hatt : L₂.IsAttached (G.res r) P) :
    IsFiberInvariant G.step.ext P := by
  have hgood_all : ∀ᶠ w in cofinite,
      0 < L₂.norm w ∧ ∃ B, L₂.S.sat P w B ∧
        L₂.frobEig (G.res r) w (algSat L₂.S.rank (L₂.norm w) B) := by
    filter_upwards [G.normM_pos, hatt] with w hpos h
    exact ⟨hpos, h⟩
  have hbad : {w : L₂.S.Place | ¬(0 < L₂.norm w ∧ ∃ B, L₂.S.sat P w B ∧
      L₂.frobEig (G.res r) w (algSat L₂.S.rank (L₂.norm w) B))}.Finite :=
    Filter.eventually_cofinite.mp hgood_all
  let badK : Set L₁.S.Place := G.step.ext.under '' {w : L₂.S.Place |
    ¬(0 < L₂.norm w ∧ ∃ B, L₂.S.sat P w B ∧
      L₂.frobEig (G.res r) w (algSat L₂.S.rank (L₂.norm w) B))}
  have hbadK_fin : badK.Finite := hbad.image G.step.ext.under
  have hbadK_ev : ∀ᶠ v in cofinite, v ∉ badK :=
    Filter.eventually_cofinite.mpr (by simpa using hbadK_fin)
  have hpre : ∀ᶠ w in cofinite, G.step.ext.under w ∉ badK :=
    G.step.ext.under_tendsto_cofinite.eventually hbadK_ev
  filter_upwards [hgood_all, G.frob_fiber_eq r, hpre] with
      w ⟨hpos, B, hBw, hFw⟩ hfib hnotbad w' hund hiner
  have hw' : 0 < L₂.norm w' ∧ ∃ B', L₂.S.sat P w' B' ∧
      L₂.frobEig (G.res r) w' (algSat L₂.S.rank (L₂.norm w') B') := by
    by_contra hnot
    exact hnotbad ⟨w', hnot, hund⟩
  obtain ⟨_, B', hB'w, hF'w⟩ := hw'
  have hF_same : L₂.frobEig (G.res r) w' (algSat L₂.S.rank (L₂.norm w) B) :=
    hfib w' hund hiner _ hFw
  have hnorm_eq : L₂.norm w' = L₂.norm w := by
    rw [← G.normM_eq, G.step.ext.norm_under w', G.step.ext.norm_under w, hund, hiner]
  rw [hnorm_eq] at hF'w
  have halg : algSat L₂.S.rank (L₂.norm w) B = algSat L₂.S.rank (L₂.norm w) B' :=
    L₂.frobEig_unique (G.res r) w' _ _ hF_same hF'w
  have hscale_ne : (((L₂.norm w : ℝ) ^ (((L₂.S.rank : ℝ) - 1) / 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hpos) _).ne'
  have hinj : Function.Injective (fun α : ℂˣ =>
      (((L₂.norm w : ℝ) ^ (((L₂.S.rank : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ)) := by
    intro α₁ α₂ h
    exact Units.ext (mul_left_cancel₀ hscale_ne h)
  have heq : B = B' := Multiset.map_injective hinj halg
  subst heq
  exact ⟨B, hBw, hB'w⟩

/-- **Frobenius-Eigenvalue Base-Change Descent**: If `r|_{G_M}` is irreducible and automorphic
over `M`, then `r` descends to an automorphic representation over `K`! -/
theorem frob_descent {r : L₁.GalRep} (hirr : L₂.IsIrr (G.res r)) (haut : L₂.IsAut (G.res r)) :
    L₁.IsAut r := by
  obtain ⟨P, hregM, hattM⟩ := haut
  have hinv : IsFiberInvariant G.step.ext P := G.fiber_invariant_of_attached_res hattM
  obtain ⟨π, hregK, hbc⟩ := G.step.descent P (G.isRegM_eq ▸ hregM) hinv
  have hregK' : L₁.IsReg π := G.isRegK_eq ▸ hregK
  obtain ⟨η, _, hattK⟩ := G.descent_twist_match r π P hirr hregK' hattM hbc
  exact ⟨L₁.S.twist π η, L₁.isReg_twist hregK', hattK⟩

/-- **Prime-Degree Cyclic Base-Change Equivalence** (mirroring `stepC` in
`SolvableEquivalenceOfBaseChange.lean`): whenever `r|_{G_M}` is irreducible, automorphy of
`r` over `K` is equivalent to automorphy of `r|_{G_M}` over `M`. -/
theorem aut_equiv {r : L₁.GalRep} (hirr : L₂.IsIrr (G.res r)) :
    L₁.IsAut r ↔ L₂.IsAut (G.res r) :=
  ⟨G.frob_lift hirr, G.frob_descent hirr⟩

end BaseChangeGalStep

/-! ## 5. Cyclic-Prime Tower Lifting & Descent (`BaseChangeTower`) -/

/-- A finite tower of prime-degree cyclic base-change steps from a base level `L₁` to a top
level `L₂`, supporting clean induction on cyclic/solvable chain length. -/
inductive BaseChangeTower : BaseChangeLevel → BaseChangeLevel → Type 1
  | nil (L : BaseChangeLevel) : BaseChangeTower L L
  | cons {L₁ L₂ L₃ : BaseChangeLevel}
      (step : BaseChangeGalStep L₁ L₂) (rest : BaseChangeTower L₂ L₃) :
      BaseChangeTower L₁ L₃

namespace BaseChangeTower

/-- Number of cyclic prime steps in the tower. -/
def length : {L₁ L₂ : BaseChangeLevel} → BaseChangeTower L₁ L₂ → ℕ
  | _, _, .nil _ => 0
  | _, _, .cons _ rest => rest.length + 1

/-- Total extension degree `∏ p_i` along the tower. -/
def degree : {L₁ L₂ : BaseChangeLevel} → BaseChangeTower L₁ L₂ → ℕ
  | _, _, .nil _ => 1
  | _, _, .cons step rest => step.step.p * rest.degree

theorem degree_pos : ∀ {L₁ L₂ : BaseChangeLevel} (T : BaseChangeTower L₁ L₂), 0 < T.degree
  | _, _, .nil _ => Nat.one_pos
  | _, _, .cons step rest => Nat.mul_pos step.step.p_prime.pos (degree_pos rest)

/-- Iterated Galois restriction `G_{L₂} → G_{L₁}` pulling back `L₁.GalRep` to `L₂.GalRep`. -/
def res : {L₁ L₂ : BaseChangeLevel} → BaseChangeTower L₁ L₂ → L₁.GalRep → L₂.GalRep
  | _, _, .nil _, r => r
  | _, _, .cons step rest, r => rest.res (step.res r)

/-- Composed place projection `L₂.S.Place → L₁.S.Place`. -/
def under : {L₁ L₂ : BaseChangeLevel} → BaseChangeTower L₁ L₂ → L₂.S.Place → L₁.S.Place
  | _, _, .nil _, w => w
  | _, _, .cons step rest, w => step.step.ext.under (rest.under w)

/-- Composed inertia degree `f(w / v) = ∏ f_i` along the tower. -/
def inertia : {L₁ L₂ : BaseChangeLevel} → BaseChangeTower L₁ L₂ → L₂.S.Place → ℕ
  | _, _, .nil _, _ => 1
  | _, _, .cons step rest, w => step.step.ext.inertia (rest.under w) * rest.inertia w

theorem inertia_pos : ∀ {L₁ L₂ : BaseChangeLevel} (T : BaseChangeTower L₁ L₂) (w : L₂.S.Place),
    0 < T.inertia w
  | _, _, .nil _, _ => Nat.one_pos
  | _, _, .cons step rest, w =>
      Nat.mul_pos (step.step.ext.inertia_pos (rest.under w)) (inertia_pos rest w)

/-- Residue norm multiplicativity along the entire tower: `N(w) = N(w|_K)^{f(w/v)}`. -/
theorem norm_under : ∀ {L₁ L₂ : BaseChangeLevel} (T : BaseChangeTower L₁ L₂) (w : L₂.S.Place),
    L₂.norm w = L₁.norm (T.under w) ^ T.inertia w
  | _, _, .nil _, w => by simp [under, inertia]
  | _, _, .cons step rest, w => by
      simp only [under, inertia]
      rw [norm_under rest w, ← step.normM_eq, step.step.ext.norm_under (rest.under w),
        step.normK_eq, ← pow_mul]

/-- The composed place projection has finite fibers (`Tendsto under cofinite cofinite`). -/
theorem under_tendsto_cofinite : ∀ {L₁ L₂ : BaseChangeLevel} (T : BaseChangeTower L₁ L₂),
    Tendsto T.under cofinite cofinite
  | _, _, .nil _ => tendsto_id
  | _, _, .cons step rest =>
      step.step.ext.under_tendsto_cofinite.comp (under_tendsto_cofinite rest)

/-- Iterated Frobenius-power compatibility along an entire tower of arbitrary length. -/
theorem frob_res : ∀ {L₁ L₂ : BaseChangeLevel} (T : BaseChangeTower L₁ L₂)
    (r : L₁.GalRep) (w : L₂.S.Place) (A : Multiset ℂ),
    L₁.frobEig r (T.under w) A → L₂.frobEig (T.res r) w (A.map (· ^ T.inertia w))
  | _, _, .nil _, _, _, A, hA => by simpa [res, under, inertia] using hA
  | _, _, .cons step rest, r, w, A, hA => by
      simp only [res, under, inertia] at hA ⊢
      have h1 := step.frob_res r (rest.under w) A hA
      have h2 := frob_res rest (step.res r) w _ h1
      simpa [Multiset.map_map, Function.comp_def, pow_mul] using h2

/-- Irreducibility propagates downward from the top of the tower to the base. -/
theorem isIrr_of_res : ∀ {L₁ L₂ : BaseChangeLevel} (T : BaseChangeTower L₁ L₂) {r : L₁.GalRep},
    L₂.IsIrr (T.res r) → L₁.IsIrr r
  | _, _, .nil _, _, h => h
  | _, _, .cons step rest, r, h => step.isIrr_of_res r (isIrr_of_res rest h)

/-- **Tower Automorphy Equivalence** (proved by induction on `BaseChangeTower` length):
if `r` remains irreducible after restriction to the top of any cyclic-prime tower `T`,
then `r` is automorphic at the base iff `T.res r` is automorphic at the top! -/
theorem aut_equiv : ∀ {L₁ L₂ : BaseChangeLevel} (T : BaseChangeTower L₁ L₂) {r : L₁.GalRep},
    L₂.IsIrr (T.res r) → (L₁.IsAut r ↔ L₂.IsAut (T.res r))
  | _, _, .nil _, _, _ => Iff.rfl
  | _, _, .cons step rest, r, hirr => by
      have hirr_mid := isIrr_of_res rest hirr
      exact (step.aut_equiv hirr_mid).trans (aut_equiv rest hirr)

/-- Direct upward lifting along a cyclic-prime tower. -/
theorem lift_aut {L₁ L₂ : BaseChangeLevel} (T : BaseChangeTower L₁ L₂) {r : L₁.GalRep}
    (hirr : L₂.IsIrr (T.res r)) (haut : L₁.IsAut r) : L₂.IsAut (T.res r) :=
  (T.aut_equiv hirr).mp haut

/-- Direct downward Frobenius-eigenvalue descent along a cyclic-prime tower. -/
theorem descent_aut {L₁ L₂ : BaseChangeLevel} (T : BaseChangeTower L₁ L₂) {r : L₁.GalRep}
    (hirr : L₂.IsIrr (T.res r)) (haut : L₂.IsAut (T.res r)) : L₁.IsAut r :=
  (T.aut_equiv hirr).mpr haut

/-- Concatenation (transitivity) of two cyclic-prime towers. -/
def append : {L₁ L₂ L₃ : BaseChangeLevel} →
    BaseChangeTower L₁ L₂ → BaseChangeTower L₂ L₃ → BaseChangeTower L₁ L₃
  | _, _, _, .nil _, T₂ => T₂
  | _, _, _, .cons step rest, T₂ => .cons step (rest.append T₂)

theorem length_append : ∀ {L₁ L₂ L₃ : BaseChangeLevel}
    (T₁ : BaseChangeTower L₁ L₂) (T₂ : BaseChangeTower L₂ L₃),
    (T₁.append T₂).length = T₁.length + T₂.length
  | _, _, _, .nil _, _ => by simp [append, length]
  | _, _, _, .cons _ rest, T₂ => by
      simp [append, length, length_append rest T₂]; omega

theorem degree_append : ∀ {L₁ L₂ L₃ : BaseChangeLevel}
    (T₁ : BaseChangeTower L₁ L₂) (T₂ : BaseChangeTower L₂ L₃),
    (T₁.append T₂).degree = T₁.degree * T₂.degree
  | _, _, _, .nil _, _ => by simp [append, degree]
  | _, _, _, .cons step rest, T₂ => by
      simp [append, degree, degree_append rest T₂, mul_assoc]

theorem res_append : ∀ {L₁ L₂ L₃ : BaseChangeLevel}
    (T₁ : BaseChangeTower L₁ L₂) (T₂ : BaseChangeTower L₂ L₃) (r : L₁.GalRep),
    (T₁.append T₂).res r = T₂.res (T₁.res r)
  | _, _, _, .nil _, _, _ => rfl
  | _, _, _, .cons step rest, T₂, r => res_append rest T₂ (step.res r)

/-- **Solvable Tower Construction by Strong Induction on Extension Degree**
(mirroring `solvable_equivalence_of_base_change` & `solC_of_stepC` in
`SolvableEquivalenceOfBaseChange.lean`):
Given an indexed family of solvable extensions `Rel L₁ L₂ d` of degree `d ≥ 1` where
degree `1` is trivial (`L₁ = L₂`), every prime-degree extension admits a `BaseChangeGalStep`,
and every composite solvable extension splits through an intermediate level `L_mid` with
strictly smaller factors `d₁ * d₂ = d`, EVERY solvable extension admits a `BaseChangeTower`
of exact degree `d`! -/
theorem of_solvable_decomp (Rel : BaseChangeLevel → BaseChangeLevel → ℕ → Prop)
    (hdeg_one : ∀ L₁ L₂, Rel L₁ L₂ 1 → L₁ = L₂)
    (hprime : ∀ L₁ L₂ p, p.Prime → Rel L₁ L₂ p →
      ∃ step : BaseChangeGalStep L₁ L₂, step.step.p = p)
    (hsplit : ∀ L₁ L₂ d, 1 < d → ¬d.Prime → Rel L₁ L₂ d →
      ∃ L_mid d₁ d₂, 1 < d₁ ∧ 1 < d₂ ∧ d₁ * d₂ = d ∧ Rel L₁ L_mid d₁ ∧ Rel L_mid L₂ d₂) :
    ∀ d, 0 < d → ∀ L₁ L₂, Rel L₁ L₂ d →
      ∃ T : BaseChangeTower L₁ L₂, T.degree = d := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hdpos L₁ L₂ hrel
    by_cases hd1 : d = 1
    · subst hd1
      obtain rfl := hdeg_one L₁ L₂ hrel
      exact ⟨.nil L₁, rfl⟩
    · have hdgt : 1 < d := by omega
      by_cases hdp : d.Prime
      · obtain ⟨step, hsp⟩ := hprime L₁ L₂ d hdp hrel
        exact ⟨.cons step (.nil L₂), by simp [degree, hsp]⟩
      · obtain ⟨L_mid, d₁, d₂, h1, h2, hmul, hrel1, hrel2⟩ := hsplit L₁ L₂ d hdgt hdp hrel
        have hd1_lt : d₁ < d := by
          rw [← hmul]; exact lt_mul_of_one_lt_right (by omega) h2
        have hd2_lt : d₂ < d := by
          rw [← hmul]; exact lt_mul_of_one_lt_left (by omega) h1
        obtain ⟨T₁, hT₁⟩ := ih d₁ hd1_lt (by omega) L₁ L_mid hrel1
        obtain ⟨T₂, hT₂⟩ := ih d₂ hd2_lt (by omega) L_mid L₂ hrel2
        exact ⟨T₁.append T₂, by rw [degree_append, hT₁, hT₂, hmul]⟩

/-- Direct solvable automorphy equivalence corollary (`SolE`): any solvable extension
satisfying the prime-step decomposition preserves and reflects automorphy of every
Galois representation remaining irreducible at the top! -/
theorem solvable_aut_equiv (Rel : BaseChangeLevel → BaseChangeLevel → ℕ → Prop)
    (hdeg_one : ∀ L₁ L₂, Rel L₁ L₂ 1 → L₁ = L₂)
    (hprime : ∀ L₁ L₂ p, p.Prime → Rel L₁ L₂ p →
      ∃ step : BaseChangeGalStep L₁ L₂, step.step.p = p)
    (hsplit : ∀ L₁ L₂ d, 1 < d → ¬d.Prime → Rel L₁ L₂ d →
      ∃ L_mid d₁ d₂, 1 < d₁ ∧ 1 < d₂ ∧ d₁ * d₂ = d ∧ Rel L₁ L_mid d₁ ∧ Rel L_mid L₂ d₂)
    {d : ℕ} (hd : 0 < d) {L₁ L₂ : BaseChangeLevel} (hrel : Rel L₁ L₂ d) :
    ∃ T : BaseChangeTower L₁ L₂, T.degree = d ∧
      ∀ r : L₁.GalRep, L₂.IsIrr (T.res r) → (L₁.IsAut r ↔ L₂.IsAut (T.res r)) := by
  obtain ⟨T, hdeg⟩ := of_solvable_decomp Rel hdeg_one hprime hsplit d hd L₁ L₂ hrel
  exact ⟨T, hdeg, fun _ hirr => T.aut_equiv hirr⟩

end BaseChangeTower

/-! ## 6. Isobaric Base Change Algebra (`BaseChangeIsobaricN` Core) -/

private theorem multiset_card_finset_sum {α ι : Type} (s : Finset ι) (f : ι → Multiset α) :
    (∑ i ∈ s, f i).card = ∑ i ∈ s, (f i).card := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Multiset.card_add, Finset.sum_cons, ih]

/-- Algebraic isobaric base-change decomposition datum on `U(n) → GL_n / E`
(distilling `PositivityTheory.Rg.BcN.IsBaseChangeN` / `BaseChangeIsobaricN`). -/
structure IsobaricBaseChangeDatum (Place Emb : Type) (n : ℕ) where
  /-- Number of discrete/cuspidal isobaric summands. -/
  c : ℕ
  /-- Ranks `N_i > 0` summing to `n`. -/
  N : Fin c → ℕ
  N_pos : ∀ i, 0 < N i
  sum_N : ∑ i, N i = n
  /-- Local Satake parameter multiset of the `i`-th summand at place `w`. -/
  satComp : Fin c → Place → Multiset ℂˣ
  satComp_card : ∀ i w, (satComp i w).card = N i
  /-- Infinitesimal character multiset of the `i`-th summand at embedding `τ`. -/
  infComp : Fin c → Emb → Multiset ℂ
  infComp_card : ∀ i τ, (infComp i τ).card = N i

namespace IsobaricBaseChangeDatum

variable {Place Emb : Type} {n : ℕ} (D : IsobaricBaseChangeDatum Place Emb n)

/-- Total isobaric Satake parameter multiset `⊞_i B_i` at place `w`. -/
def totalSat (w : Place) : Multiset ℂˣ := ∑ i : Fin D.c, D.satComp i w

/-- Total isobaric infinitesimal character `∑_i m_i(τ)` at embedding `τ`. -/
def totalInf (τ : Emb) : Multiset ℂ := ∑ i : Fin D.c, D.infComp i τ

theorem totalSat_card (w : Place) : (D.totalSat w).card = n := by
  rw [totalSat, multiset_card_finset_sum]
  simp only [D.satComp_card, D.sum_N]

theorem totalInf_card (τ : Emb) : (D.totalInf τ).card = n := by
  rw [totalInf, multiset_card_finset_sum]
  simp only [D.infComp_card, D.sum_N]

/-- The characteristic polynomial of an isobaric base change factors cleanly as the product
of the characteristic polynomials of its discrete summands. -/
theorem eigPoly_total (w : Place) :
    eigPoly ((D.totalSat w).map Units.val) =
      ∏ i : Fin D.c, eigPoly ((D.satComp i w).map Units.val) := by
  simp only [totalSat]
  induction (Finset.univ : Finset (Fin D.c)) using Finset.cons_induction with
  | empty => simp [eigPoly_zero]
  | cons a s ha ih =>
    rw [Finset.sum_cons, Multiset.map_add, eigPoly_add, Finset.prod_cons, ih]

/-- **Split-Place Isobaric Uniqueness**: If two isobaric base-change data `D₁, D₂` match the
same unitary local Satake multisets cofinally on split places, then their total Satake
multisets and characteristic polynomials coincide cofinally on split places. -/
theorem satake_unique_of_split {D₁ D₂ : IsobaricBaseChangeDatum Place Emb n}
    (IsSplit : Place → Prop) (uSat : Place → Multiset ℂˣ → Prop)
    (uSat_unique : ∀ w B₁ B₂, uSat w B₁ → uSat w B₂ → B₁ = B₂)
    (h1 : ∀ᶠ w in cofinite, IsSplit w → uSat w (D₁.totalSat w))
    (h2 : ∀ᶠ w in cofinite, IsSplit w → uSat w (D₂.totalSat w)) :
    ∀ᶠ w in cofinite, IsSplit w →
      D₁.totalSat w = D₂.totalSat w ∧
      eigPoly ((D₁.totalSat w).map Units.val) = eigPoly ((D₂.totalSat w).map Units.val) := by
  filter_upwards [h1, h2] with w hw1 hw2 hsp
  have heq : D₁.totalSat w = D₂.totalSat w := uSat_unique w _ _ (hw1 hsp) (hw2 hsp)
  exact ⟨heq, by rw [heq]⟩

end IsobaricBaseChangeDatum

/-! ## 7. Bridge to `RHDirect.Interfaces` Cyclic Character Levels (`Level.cyc`) -/

/-- The character subgroup generating `Level.cyc ψ` is cyclic. -/
theorem Level.cyc_subgroup_isCyclic (ψ : PChar) :
    IsCyclic (Subgroup.zpowers ψ.χ) :=
  inferInstance

/-- The order parameter `(Level.cyc ψ).o` equals the exact multiplicative order `orderOf ψ.χ`. -/
theorem Level.cyc_order_eq_orderOf (ψ : PChar) :
    (Level.cyc ψ).o = orderOf ψ.χ := by
  change Nat.card (Subgroup.zpowers ψ.χ) = orderOf ψ.χ
  exact Nat.card_zpowers ψ.χ

/-- The primitive-character support `(Level.cyc ψ).KEPT` has cardinality at most `(Level.cyc ψ).o`. -/
theorem Level.cyc_card_le_order (ψ : PChar) :
    (Level.cyc ψ).KEPT.card ≤ (Level.cyc ψ).o := by
  classical
  change ((Finset.univ.filter fun χ : DirichletCharacter ℂ ψ.N =>
      χ ∈ Subgroup.zpowers ψ.χ).image PChar.of).card ≤ Nat.card (Subgroup.zpowers ψ.χ)
  refine le_trans Finset.card_image_le ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

private theorem mulChar_pow_apply_of_isUnit {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {x : ZMod N} (hx : IsUnit x) : ∀ k : ℕ, (χ ^ k) x = (χ x) ^ k := by
  intro k
  induction k with
  | zero => simp [MulChar.one_apply hx]
  | succ k ih => rw [pow_succ, MulChar.mul_apply, ih, pow_succ]

/-- Every value `ψ.val a` at an integer coprime to `ψ.N` is a `(Level.cyc ψ).o`-th root of unity. -/
theorem PChar.pow_orderOf_val (ψ : PChar) (a : ℕ) (hcop : Nat.Coprime a ψ.N) :
    (ψ.val a) ^ (Level.cyc ψ).o = 1 := by
  rw [Level.cyc_order_eq_orderOf, PChar.val]
  have hu : IsUnit (a : ZMod ψ.N) := (ZMod.isUnit_iff_coprime a ψ.N).mpr hcop
  rw [← mulChar_pow_apply_of_isUnit ψ.χ hu, pow_orderOf_eq_one, MulChar.one_apply hu]

end RHDirect

end
