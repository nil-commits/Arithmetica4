import RHDirect.Stage13MinusParityRubin
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.Finiteness
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-!
# RHDirect.Stage13StickelbergerRealize

Realization of **Field #4a (`StickelbergerRamifiedControl` & Alpöge `StickBound` on genuine
`Stage13MinusParityRubin.minusParitySelmerSystem.minusLen`)** for ramified odd primes
`l ∣ orderOf ψ.χ` (`Stage13Field1Unification.lean:839–848`), with **0 `sorry`, 0 custom `axiom`s,
0 `opaque`, 0 `native_decide`**.

## Brutally Honest Audit of What Closes with `0` Parameters vs. What Remains Isolated

### 1. Proved UNCONDITIONALLY with `0` Open Parameters (Directly from Mathlib `v4.33.1`):
- **Genuine `l`-torsion rank bound (`h1_l_torsion_rank_bound`, Alpöge's `UpperTheory.V.Odd.gen`)**
  on the real Galois cohomology module `Stage12GaloisShaLen.H1 (qzTw D e)` (and hence on
  `Sha1Galois E l e` and `minusParitySelmerSystem.minusLen`!):
  For EVERY number field `E` embedding in `CyclotomicField N ℚ` (`0 < N`), EVERY prime `l`,
  EVERY `D : LData E Ω l`, and EVERY twist `e : ℤ`:
  `∃ g : ℕ, Module.length ℤ_[l] (Submodule.torsionBy ℤ_[l] (H1 (qzTw D e)) (l : ℤ_[l])) ≤ g ∧`
  `  (g : ℝ) ≤ 8 * l * [E : ℚ] * Real.log (l * N)`.
  Proved completely from scratch in pure Mathlib via:
  - `len_and_card_of_finite_padicInt`: `Module.length ℤ_[l] M = k ∧ Nat.card M = l ^ k`,
  - `log_classNumber_le`: Minkowski's bound (`exists_ideal_in_class_of_norm_le`) + ideal tuple
    counting (`harmonic_le_one_add_log`),
  - `natAbs_discr_le_pow_of_cyclotomic`: `|discr E| ≤ N ^ [E : ℚ]` via
    `NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow` + cyclotomic
    derivative norm divisibility `Φ_N'(ζ) ∣ N * ζ^(N-1)`,
  - `card_above_le_finrank`, Dirichlet `S`-unit rank (`card_sUnit_quot_pow_le`), and Kummer
    Selmer exact sequence (`card_selK_quot_pow_le`),
  - Continuous Hilbert 90 (`hilbert90_continuous` via Dedekind independence of characters),
    inertia-ramification divisibility (`dvdOfIne`), and Kummer injection (`unrSel`, `unrInj`,
    `fnOne`).
- **Higher Stickelberger Archimedean Bound (`bdxLog`, `C = 30`)** & **Signed-Det Exponent Bridge**:
  - `bdxLog`: `Real.log (bdX (N * l) (2 * (N * l) + 1) (e + 1)) + Real.log (N * l) ≤ 30 * (e + 1) * Real.log (e * l * N)`.
  - `stickelberger_minusLen_bound_of_annihilation_exponent`: combines `0`-parameter
    `h1_l_torsion_rank_bound` + `length_le_mul_lTorsion` to deduce Alpöge's `StickBound`
    `minusLen E l k ≠ ⊤ ∧ minusLen * log l ≤ (8 * C) * l * [E:ℚ]^2 * (k + 1) * log(k * l * condF E)^2`
    from ANY annihilation exponent `r` (`r * log l ≤ C * [E:ℚ] * (k+1) * log(k * l * condF E)`).
- **Direct Discharge of `Stage2RamifiedPrimes.RamifiedPrimeRealization` (`C_ram = 480`) & `VVminusLe`**
  from `StickelbergerAnnihilatorExponentOnShaMinus` (with `h1_l_torsion_rank_bound` 0-parameter!).
- **Unconditional (`0`-parameter) `StickelbergerRamifiedControl` for totally-real fields**
  (`stickelbergerRamifiedControl_realGalois_of_totallyReal`).

### 2. Two Genuine Gaps Honestly Isolated (NOT Faked!):
1. **Global Class Field Theory / Hilbert Class Field Artin Reciprocity + Stickelberger Class-Group
   Annihilation on `ShaMinus` (`StickelbergerAnnihilatorExponentOnShaMinus`, Alpöge's `killPow`):**
   In Alpöge's formalization, `killPow` depends on global idelic Class Field Theory (`HilbertClassField`
   Artin map `artCl : G K Ω →* ClassGroup (𝓞 K)` with `artKer`, `artFrob`, `artSurj`) and
   Stickelberger's theorem on `ClassGroup (𝓞 (ℚ(ζ_M)))` (requiring degree-1 prime ideal
   representatives in every ideal class). Neither is in Mathlib `v4.33.1`.
2. **Structural Tightness Gap in `Stage11StickelbergerRamified.StickelbergerRamifiedControl`
   (`Stage13Field1Unification.lean:844–847`):**
   Every inhabitant of `StickelbergerRamifiedControl S E t M n N` enforces `genRank ≤ n` and
   `log ann ≤ 5 * n * k * log(2 * k * N)`, forcing `minusLen E l k * log l ≤ 5 * n^2 * k * log(2 * k * N)`.
   By contrast, Alpöge's elementary `StickBound` (`killPow * gen`) yields
   `240 * l * n^2 * (k + 1) * log(k * l * N)^2` (looser by `~ 100 * l * log(k * l * N)` — already
   strong enough for `RamifiedPrimeRealization` & `VVminusLe` via `minusBound 480`, whereas
   `StickelbergerRamifiedControl` requires the strictly sharper Mazur–Wiles Iwasawa Main Conjecture
   bound, isolated cleanly in `SharpStickelbergerMinusLenHypothesis`).
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped BigOperators Pointwise nonZeroDivisors NumberField
open NumberField IsDedekindDomain Finset Real RHDirect
open RHDirect.Stage2GaloisWire
open RHDirect.Stage11StickelbergerRamified
open RHDirect.Stage12GaloisShaLen
open RHDirect.Stage12Window1RootAvoid
open RHDirect.Stage13MinusParityRubin
open RHDirect.TaylorWilesWindow

namespace RHDirect.Stage13StickelbergerRealize

/-! ## Section 1: Finite `ℤ_[l]`-Module Length–Cardinality Identity & Minkowski / Cyclotomic Discriminant Bounds -/

section FiniteLengthAndClassNumberBounds

/-- Every simple `ℤ_[l]`-module has cardinality `l`. -/
private theorem natCard_of_isSimpleModule_padicInt (l : ℕ) [Fact l.Prime]
    (M : Type*) [AddCommGroup M] [Module ℤ_[l] M] [h : IsSimpleModule ℤ_[l] M] :
    Nat.card M = l := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp h
  have hIm : I = IsLocalRing.maximalIdeal ℤ_[l] := IsLocalRing.eq_maximalIdeal hI
  subst hIm
  rw [Nat.card_congr e.toEquiv]
  have f := RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective (PadicInt.toZMod (p := l)))
  have g := Ideal.quotEquivOfEq (PadicInt.ker_toZMod (p := l))
  rw [← Nat.card_congr g.toEquiv, Nat.card_congr f.toEquiv, Nat.card_zmod]

/-- For every finite `ℤ_[l]`-module `M`, its length `k` is finite and `Nat.card M = l ^ k`. -/
theorem len_and_card_of_finite_padicInt (l : ℕ) [Fact l.Prime]
    (M : Type*) [AddCommGroup M] [Module ℤ_[l] M] [Finite M] :
    ∃ k : ℕ, Module.length ℤ_[l] M = k ∧ Nat.card M = l ^ k := by
  have hfl : IsFiniteLength ℤ_[l] M :=
    isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨inferInstance, inferInstance⟩
  induction hfl with
  | of_subsingleton =>
    exact ⟨0, by rw [Module.length_eq_zero]; rfl, by rw [Nat.card_of_subsingleton (0 : _)]; simp⟩
  | @of_simple_quotient M _ _ N _ _ ih =>
    obtain ⟨k, hk, hc⟩ := ih
    refine ⟨k + 1, ?_, ?_⟩
    · rw [Module.length_eq_add_of_exact N.subtype N.mkQ (Submodule.injective_subtype N)
        (Submodule.mkQ_surjective N) (LinearMap.exact_subtype_mkQ N), hk, Module.length_eq_one]
      rfl
    · rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N.toAddSubgroup]
      have h1 : Nat.card (M ⧸ N.toAddSubgroup) = l := natCard_of_isSimpleModule_padicInt l (M ⧸ N)
      have h2 : Nat.card N.toAddSubgroup = l ^ k := hc
      rw [h1, h2, pow_succ, mul_comm]

/-! ### Minkowski Ideal Counting (`log_classNumber_le`) -/

private theorem card_fiber_le (n M k : ℕ) (hk : 1 ≤ k) :
    (((Fintype.piFinset fun _ : Fin (n + 2) => Icc 1 M).filter
      (fun a => ∏ i, a i ≤ M)).filter (fun a => a 0 = k)).card ≤
    ((Fintype.piFinset fun _ : Fin (n + 1) => Icc 1 (M / k)).filter
      (fun a => ∏ i, a i ≤ M / k)).card := by
  refine Finset.card_le_card_of_injOn (fun a => Fin.tail a) ?_ ?_
  · intro a ha
    simp only [coe_filter, mem_filter, Fintype.mem_piFinset, mem_Icc, Set.mem_ofPred_eq] at ha ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := ha
    rw [Fin.prod_univ_succ, h3] at h2
    have h4 : ∏ i, Fin.tail a i ≤ M / k := by
      rw [Nat.le_div_iff_mul_le (by omega), mul_comm]
      exact h2
    refine ⟨fun i => ⟨(h1 _).1, le_trans ?_ h4⟩, h4⟩
    exact Finset.single_le_prod' (f := fun i => Fin.tail a i) (fun j _ => (h1 _).1) (mem_univ i)
  · intro a ha b hb hab
    simp only [coe_filter, Set.mem_ofPred_eq] at ha hb
    have : Fin.tail a = Fin.tail b := hab
    rw [← Fin.cons_self_tail a, ← Fin.cons_self_tail b, ha.2, hb.2, this]

/-- Number of `(n + 1)`-tuples of positive integers with product `≤ M` is `≤ M * (1 + log M)^n`. -/
theorem card_tuples_le (n M : ℕ) (hM : 1 ≤ M) :
    (((Fintype.piFinset fun _ : Fin (n + 1) => Icc 1 M).filter
      (fun a => ∏ i, a i ≤ M)).card : ℝ) ≤ M * (1 + Real.log M) ^ n := by
  induction n generalizing M with
  | zero =>
    have := Finset.card_filter_le (Fintype.piFinset fun _ : Fin (0 + 1) => Icc 1 M)
      (fun a => ∏ i, a i ≤ M)
    rw [Fintype.card_piFinset] at this
    simp only [Nat.card_Icc, Nat.add_sub_cancel, prod_const, card_univ, Fintype.card_fin,
      zero_add, pow_one] at this
    rw [pow_zero, mul_one]
    exact_mod_cast this
  | succ n ih =>
    have hlog : 0 ≤ Real.log M := Real.log_natCast_nonneg M
    rw [Finset.card_eq_sum_card_fiberwise (f := fun a : Fin (n + 1 + 1) → ℕ => a 0)
      (t := Icc 1 M) (by
        intro a ha
        simp only [coe_filter, Fintype.mem_piFinset, Set.mem_ofPred_eq] at ha
        exact_mod_cast ha.1 0)]
    push_cast
    have key : ∀ k ∈ Icc 1 M,
        ((((Fintype.piFinset fun _ : Fin (n + 1 + 1) => Icc 1 M).filter
          (fun a => ∏ i, a i ≤ M)).filter (fun a => a 0 = k)).card : ℝ) ≤
          (M * (1 + Real.log M) ^ n) * ((k : ℝ))⁻¹ := by
      intro k hk
      rw [mem_Icc] at hk
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk.1
      have h1 : 1 ≤ M / k := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
      have h2 := ih (M / k) h1
      have h3 := card_fiber_le n M k hk.1
      have h4 : ((M / k : ℕ) : ℝ) ≤ M * (k : ℝ)⁻¹ := by
        rw [← div_eq_mul_inv]; exact Nat.cast_div_le
      have h5 : Real.log ((M / k : ℕ) : ℝ) ≤ Real.log M := by
        apply Real.log_le_log (by exact_mod_cast h1)
        exact_mod_cast Nat.div_le_self M k
      have h6 : 0 ≤ Real.log ((M / k : ℕ) : ℝ) := Real.log_natCast_nonneg _
      calc _ ≤ _ := Nat.cast_le.2 h3
        _ ≤ _ := h2
        _ ≤ (M * (k : ℝ)⁻¹) * (1 + Real.log M) ^ n := by gcongr
        _ = _ := by ring
    have hh : ∑ k ∈ Icc 1 M, ((k : ℝ))⁻¹ ≤ 1 + Real.log M := by
      have := harmonic_le_one_add_log M
      rw [harmonic_eq_sum_Icc] at this
      push_cast at this
      exact this
    calc _ ≤ _ := Finset.sum_le_sum key
      _ = (M * (1 + Real.log M) ^ n) * ∑ k ∈ Icc 1 M, ((k : ℝ))⁻¹ := by rw [Finset.mul_sum]
      _ ≤ (M * (1 + Real.log M) ^ n) * (1 + Real.log M) := by gcongr
      _ = _ := by ring

private theorem classB_prod {ι : Type*} {n : ℕ} (q : ι → ℕ) (idx : ι → Fin n) (s : Multiset ι) :
    ∏ i, ((s.filter (fun x => idx x = i)).map q).prod = (s.map q).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have h : ∀ i, (((a ::ₘ s).filter (fun x => idx x = i)).map q).prod =
        (if idx a = i then q a else 1) * ((s.filter (fun x => idx x = i)).map q).prod := by
      intro i
      by_cases h : idx a = i
      · simp [Multiset.filter_cons_of_pos, h]
      · simp [Multiset.filter_cons_of_neg, h]
    simp only [h, Finset.prod_mul_distrib, ih, Finset.prod_ite_eq, Finset.mem_univ, if_true,
      Multiset.map_cons, Multiset.prod_cons]

private theorem classB_inj {ι : Type*} {n : ℕ} (q : ι → ℕ) (idx : ι → Fin n)
    (hq : ∀ x, (q x).Prime) (hinj : ∀ x y, q x = q y → idx x = idx y → x = y)
    (s t : Multiset ι)
    (h : ∀ i, ((s.filter (fun x => idx x = i)).map q).prod =
      ((t.filter (fun x => idx x = i)).map q).prod) : s = t := by
  classical
  have h1 : ∀ (u : Multiset ι), UniqueFactorizationMonoid.normalizedFactors (u.map q).prod
      = u.map q := by
    intro u
    apply UniqueFactorizationMonoid.normalizedFactors_prod_of_prime
    intro p hp
    obtain ⟨x, -, rfl⟩ := Multiset.mem_map.mp hp
    exact (hq x).prime
  have h2 : ∀ i, (s.filter (fun x => idx x = i)).map q = (t.filter (fun x => idx x = i)).map q := by
    intro i
    rw [← h1, h i, h1]
  have hg : Function.Injective (fun x => (idx x, q x)) := by
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact hinj x y hxy.2 hxy.1
  have h3 : ∀ (u : Multiset ι) i, (u.filter (fun x => idx x = i)).map (fun x => (idx x, q x)) =
      ((u.filter (fun x => idx x = i)).map q).map (fun r => (i, r)) := by
    intro u i
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro x hx
    simp [(Multiset.mem_filter.mp hx).2]
  have h4 : ∀ i, s.filter (fun x => idx x = i) = t.filter (fun x => idx x = i) := by
    intro i
    apply Multiset.map_injective hg
    rw [h3, h3, h2]
  ext x
  have := congrArg (Multiset.count x) (h4 (idx x))
  rwa [Multiset.count_filter_of_pos (by rfl), Multiset.count_filter_of_pos (by rfl)] at this

private theorem classB_idx {ι : Type*} {n : ℕ} (q : ι → ℕ)
    (h : ∀ p, ∃ S : Finset ι, S.card ≤ n ∧ ∀ x, q x = p → x ∈ S) :
    ∃ idx : ι → Fin n, ∀ x y, q x = q y → idx x = idx y → x = y := by
  choose S hS hS' using h
  have : ∀ p, ∃ f : S p → Fin n, Function.Injective f := by
    intro p
    obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (α := S p) (β := Fin n)
      (by simpa using hS p)
    exact ⟨f, f.injective⟩
  choose f hf using this
  refine ⟨fun x => f (q x) ⟨x, hS' _ x rfl⟩, ?_⟩
  intro x y hxy hi
  have key : ∀ p (hp : q y = p), f (q y) ⟨y, hS' _ y rfl⟩ = f p ⟨y, hS' _ y hp⟩ := by
    rintro p rfl; rfl
  simp only at hi
  rw [key (q x) hxy.symm] at hi
  exact congrArg Subtype.val (hf _ hi)

private theorem classB_fact (K : Type*) [Field K] [NumberField K] (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ∃ s : Multiset (HeightOneSpectrum (𝓞 K)), (s.map (fun v => v.asIdeal)).prod = I := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hI
  | h₂ x hx => exact ⟨0, by simpa using (isUnit_iff_eq_one.mp hx).symm⟩
  | h₃ x p hx hp ih =>
    have hx0 : x ≠ ⊥ := hx
    obtain ⟨s, hs⟩ := ih hx0
    have hp0 : p ≠ ⊥ := hp.ne_zero
    have hpp : p.IsPrime := Ideal.isPrime_of_prime hp
    refine ⟨(⟨p, hpp, hp0⟩ : HeightOneSpectrum (𝓞 K)) ::ₘ s, ?_⟩
    rw [Multiset.map_cons, Multiset.prod_cons, hs, mul_comm]

private theorem card_primesOverFinset_le_finrank_rat (K : Type*) [Field K] [NumberField K]
    (p : ℕ) [hp : Fact p.Prime] (h0 : Ideal.span {(p : ℤ)} ≠ ⊥) :
    (IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K)).card ≤ Module.finrank ℚ K := by
  classical
  set P : Ideal ℤ := Ideal.span {(p : ℤ)}
  haveI hPmax : P.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  haveI : Fintype (P.primesOver (𝓞 K)) := by
    rw [← IsDedekindDomain.coe_primesOverFinset h0 (𝓞 K)]
    infer_instance
  have hsum : ∑ q : P.primesOver (𝓞 K), (q : Ideal (𝓞 K)).ramificationIdx ℤ *
      (q : Ideal (𝓞 K)).inertiaDeg ℤ = Module.finrank ℚ K := by
    rw [Ideal.sum_ramification_inertia_eq_finrank P (𝓞 K), NumberField.RingOfIntegers.rank]
  have hcard : (IsDedekindDomain.primesOverFinset P (𝓞 K)).card = Fintype.card (P.primesOver (𝓞 K)) := by
    rw [← Nat.card_eq_fintype_card, ← IsDedekindDomain.coe_primesOverFinset h0 (𝓞 K),
      Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [hcard, ← hsum, Fintype.card_eq_sum_ones]
  refine Finset.sum_le_sum fun q _ => ?_
  haveI := Ideal.primesOver.isPrime P q
  exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
    (Ideal.ramificationIdx_pos _ ℤ).ne' (Ideal.inertiaDeg_pos _ ℤ).ne')

private theorem card_ideals_le_tuples (K : Type*) [Field K] [NumberField K] (M : ℕ) :
    Nat.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ M} ≤
      ((Fintype.piFinset fun _ : Fin (Module.finrank ℚ K) => Icc 1 M).filter
        (fun a => ∏ i, a i ≤ M)).card := by
  classical
  let q : HeightOneSpectrum (𝓞 K) → ℕ := fun v => Ideal.absNorm (v.asIdeal.under ℤ)
  have hq : ∀ v, (q v).Prime := fun v => by
    have := v.isPrime
    have : NeZero v.asIdeal := ⟨v.ne_bot⟩
    exact Nat.absNorm_under_prime v.asIdeal
  have hle : ∀ v, q v ≤ Ideal.absNorm v.asIdeal := fun v => by
    refine Nat.le_of_dvd (Nat.pos_of_ne_zero ?_) (Int.absNorm_under_dvd_absNorm v.asIdeal)
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  obtain ⟨idx, hidx⟩ := classB_idx (n := Module.finrank ℚ K) q fun p => by
    by_cases hp : p.Prime
    · have : Fact p.Prime := ⟨hp⟩
      have h0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
      refine ⟨(IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K)).preimage
        (fun v => v.asIdeal) (fun a _ b _ h => HeightOneSpectrum.ext h), ?_, ?_⟩
      · refine le_trans ?_ (card_primesOverFinset_le_finrank_rat K p h0)
        apply Finset.card_le_card_of_injOn (fun v => v.asIdeal)
        · intro v hv
          exact Finset.mem_coe.mpr (Finset.mem_preimage.mp (Finset.mem_coe.mp hv))
        · exact fun a _ b _ h => HeightOneSpectrum.ext h
      · rintro v rfl
        refine Finset.mem_preimage.mpr ((IsDedekindDomain.mem_primesOverFinset_iff h0 _).mpr ?_)
        exact ⟨v.isPrime, Int.liesOver_span_absNorm v.asIdeal⟩
    · exact ⟨∅, by simp, fun x hx => absurd (hx ▸ hq x) hp⟩
  choose s hs using classB_fact K
  rw [← Nat.card_eq_finsetCard]
  have hprod : ∀ (I : Ideal (𝓞 K)) (hI : I ≠ ⊥), ((s I hI).map q).prod ≤ Ideal.absNorm I := by
    intro I hI
    conv_rhs => rw [← hs I hI, map_multiset_prod, Multiset.map_map]
    exact Multiset.prod_map_le_prod_map _ _ (fun v _ => hle v)
  have hpos : ∀ u : Multiset (HeightOneSpectrum (𝓞 K)), 0 < (u.map q).prod := fun u =>
    Multiset.prod_pos fun a ha => by
      obtain ⟨x, -, rfl⟩ := Multiset.mem_map.mp ha
      exact (hq x).pos
  refine Nat.card_le_card_of_injective
    (fun I => ⟨fun i => (((s I.1 I.2.1).filter (fun x => idx x = i)).map q).prod, ?_⟩) ?_
  · have h1 := (classB_prod q idx (s I.1 I.2.1)).trans_le ((hprod I.1 I.2.1).trans I.2.2)
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun i => Finset.mem_Icc.mpr ⟨hpos _, le_trans ?_ h1⟩, h1⟩
    exact Finset.single_le_prod' (f := fun i => (((s I.1 I.2.1).filter
      (fun x => idx x = i)).map q).prod) (fun j _ => hpos _) (Finset.mem_univ i)
  · intro I J hIJ
    have h := classB_inj q idx hq hidx _ _ (congrFun (congrArg Subtype.val hIJ))
    apply Subtype.ext
    rw [← hs I.1 I.2.1, ← hs J.1 J.2.1, h]

private theorem classC_fact (n : ℕ) :
    (2 : ℝ) ^ n * ((n + 1).factorial : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have h1 : (2 : ℝ) ≤ (1 + (((n + 1 : ℕ) : ℝ))⁻¹) ^ (n + 1) := by
      have := one_add_mul_le_pow (a := (((n + 1 : ℕ) : ℝ))⁻¹)
        (le_trans (by norm_num) (inv_nonneg.mpr hp.le)) (n + 1)
      rw [mul_inv_cancel₀ hp.ne'] at this
      linarith
    have h2 : 2 * ((n + 1 : ℕ) : ℝ) ^ (n + 1) ≤ ((n + 1 + 1 : ℕ) : ℝ) ^ (n + 1) := by
      have e : ((n + 1 + 1 : ℕ) : ℝ) = (1 + (((n + 1 : ℕ) : ℝ))⁻¹) * ((n + 1 : ℕ) : ℝ) := by
        rw [add_mul, inv_mul_cancel₀ hp.ne']; push_cast; ring
      rw [e, mul_pow]
      gcongr
    calc (2 : ℝ) ^ (n + 1) * ((n + 1 + 1).factorial : ℝ)
        = ((n + 1 + 1 : ℕ) : ℝ) * (2 * (2 ^ n * ((n + 1).factorial : ℝ))) := by
          rw [Nat.factorial_succ (n + 1), Nat.cast_mul]; ring
      _ ≤ ((n + 1 + 1 : ℕ) : ℝ) * (2 * ((n + 1 : ℕ) : ℝ) ^ (n + 1)) := by gcongr
      _ ≤ ((n + 1 + 1 : ℕ) : ℝ) * ((n + 1 + 1 : ℕ) : ℝ) ^ (n + 1) := by gcongr
      _ = _ := by ring

private theorem classC_const (n r : ℕ) (hn : 0 < n) (hr : 2 * r ≤ n) :
    (4 / Real.pi) ^ r * ((n.factorial : ℝ) / (n : ℝ) ^ n) ≤ 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 : (4 / Real.pi) ≤ 2 := by
    rw [div_le_iff₀ Real.pi_pos]; linarith [Real.pi_gt_three]
  have h2 : (4 / Real.pi) ^ r ≤ (2 : ℝ) ^ m :=
    (pow_le_pow_left₀ (by positivity) h1 r).trans (pow_le_pow_right₀ (by norm_num) (by omega))
  rw [← mul_div_assoc, div_le_one (by positivity)]
  refine le_trans ?_ (classC_fact m)
  gcongr

/-- **Minkowski Class-Number Ideal-Counting Bound**: `h(K)` is at most the number of nonzero ideals
of `𝓞 K` with `absNorm I ≤ ⌊√|discr K|⌋`. -/
theorem classNumber_le_card_ideals (K : Type*) [Field K] [NumberField K] :
    classNumber K ≤
      Nat.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ ⌊√|(discr K : ℝ)|⌋₊} := by
  classical
  have hfin : Finite {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ ⌊√|(discr K : ℝ)|⌋₊} :=
    (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌊√|(discr K : ℝ)|⌋₊).subset fun _ h => h.2
  rw [classNumber, ← Nat.card_eq_fintype_card]
  refine Nat.card_le_card_of_surjective
    (fun I => ClassGroup.mk0 (⟨I.1, mem_nonZeroDivisors_of_ne_zero I.2.1⟩ :
      nonZeroDivisors (Ideal (𝓞 K)))) ?_
  intro C
  obtain ⟨I, hI, hn⟩ := exists_ideal_in_class_of_norm_le C
  refine ⟨⟨I.1, nonZeroDivisors.coe_ne_zero I, ?_⟩, hI⟩
  apply Nat.le_floor
  refine hn.trans ?_
  have hc := classC_const (Module.finrank ℚ K) (InfinitePlace.nrComplexPlaces K)
    Module.finrank_pos (by have := InfinitePlace.card_add_two_mul_card_eq_rank K; omega)
  rw [← mul_assoc]
  simpa using mul_le_of_le_one_left (Real.sqrt_nonneg |(discr K : ℝ)|) hc

/-- **Unconditional Minkowski Logarithmic Class-Number Bound (`0` parameters!)**:
`log (classNumber K) ≤ log |discr K| / 2 + [K : ℚ] * log (1 + log |discr K| / 2)`. -/
theorem log_classNumber_le (K : Type*) [Field K] [NumberField K] :
    Real.log (classNumber K) ≤ Real.log |(discr K : ℝ)| / 2 +
      Module.finrank ℚ K * Real.log (1 + Real.log |(discr K : ℝ)| / 2) := by
  have hd : (1 : ℝ) ≤ |(discr K : ℝ)| := by
    exact_mod_cast Int.one_le_abs (discr_ne_zero K)
  have hsqrt1 : (1 : ℝ) ≤ √|(discr K : ℝ)| := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    linarith
  set M := ⌊√|(discr K : ℝ)|⌋₊
  have hM1 : 1 ≤ M := Nat.le_floor (by simpa using hsqrt1)
  have hM_le : (M : ℝ) ≤ √|(discr K : ℝ)| := Nat.floor_le (Real.sqrt_nonneg _)
  have h1 := (classNumber_le_card_ideals K).trans (card_ideals_le_tuples K M)
  have hpos : (0 : ℝ) < (classNumber K : ℝ) := Nat.cast_pos.mpr (classNumber_pos K)
  have hdeg_pos : 0 < Module.finrank ℚ K := Module.finrank_pos
  obtain ⟨n, hn⟩ : ∃ n, Module.finrank ℚ K = n + 1 := ⟨Module.finrank ℚ K - 1, by omega⟩
  have h2 : (classNumber K : ℝ) ≤ (M : ℝ) * (1 + Real.log (M : ℝ)) ^ n := by
    have h1R : (classNumber K : ℝ) ≤
        (((Fintype.piFinset fun _ : Fin (Module.finrank ℚ K) => Icc 1 M).filter
          (fun a => ∏ i, a i ≤ M)).card : ℝ) := by exact_mod_cast h1
    refine h1R.trans ?_
    rw [hn]
    exact card_tuples_le n M hM1
  have hlogM : Real.log (M : ℝ) ≤ Real.log |(discr K : ℝ)| / 2 := by
    calc Real.log (M : ℝ) ≤ Real.log (√|(discr K : ℝ)|) :=
          Real.log_le_log (by exact_mod_cast hM1) hM_le
      _ = Real.log |(discr K : ℝ)| / 2 := Real.log_sqrt (by linarith)
  have hlogD_nn : 0 ≤ Real.log |(discr K : ℝ)| := Real.log_nonneg hd
  have hlog_step : Real.log (classNumber K) ≤
      Real.log (M : ℝ) + n * Real.log (1 + Real.log (M : ℝ)) := by
    have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
    have h1logM : 1 ≤ 1 + Real.log (M : ℝ) := by
      have := Real.log_natCast_nonneg M; linarith
    have hpow_pos : 0 < (1 + Real.log (M : ℝ)) ^ n := pow_pos (by linarith) n
    calc Real.log (classNumber K)
        ≤ Real.log ((M : ℝ) * (1 + Real.log (M : ℝ)) ^ n) := Real.log_le_log hpos h2
      _ = Real.log (M : ℝ) + Real.log ((1 + Real.log (M : ℝ)) ^ n) :=
          Real.log_mul hMpos.ne' hpow_pos.ne'
      _ = Real.log (M : ℝ) + n * Real.log (1 + Real.log (M : ℝ)) := by rw [Real.log_pow]
  have hn_le : (n : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by
    rw [hn]; push_cast; linarith
  have hlog_mono : Real.log (1 + Real.log (M : ℝ)) ≤ Real.log (1 + Real.log |(discr K : ℝ)| / 2) :=
    Real.log_le_log (by have := Real.log_natCast_nonneg M; linarith) (by linarith)
  have hlog_nn : 0 ≤ Real.log (1 + Real.log |(discr K : ℝ)| / 2) :=
    Real.log_nonneg (by linarith)
  calc Real.log (classNumber K)
      ≤ Real.log (M : ℝ) + n * Real.log (1 + Real.log (M : ℝ)) := hlog_step
    _ ≤ Real.log |(discr K : ℝ)| / 2 + n * Real.log (1 + Real.log |(discr K : ℝ)| / 2) := by
        gcongr
    _ ≤ Real.log |(discr K : ℝ)| / 2 +
          Module.finrank ℚ K * Real.log (1 + Real.log |(discr K : ℝ)| / 2) := by
        gcongr

/-! ### Cyclotomic Discriminant Tower Bound (`|discr E| ≤ N ^ [E : ℚ]`) -/

/-- For `K = CyclotomicField N ℚ` (`0 < N`), `(discr K).natAbs ≤ N ^ [K : ℚ]`. -/
theorem natAbs_discr_cyclotomic_le (N : ℕ) (hN : 0 < N) :
    (discr (CyclotomicField N ℚ)).natAbs ≤ N ^ Module.finrank ℚ (CyclotomicField N ℚ) := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero (N : ℚ) := ⟨Nat.cast_ne_zero.mpr hN.ne'⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  let K := CyclotomicField N ℚ
  let ζ : K := IsCyclotomicExtension.zeta N ℚ K
  have hζ : IsPrimitiveRoot ζ N := IsCyclotomicExtension.zeta_spec N ℚ K
  have hζ_int : IsIntegral ℤ ζ := hζ.isIntegral hN
  let ζO : 𝓞 K := ⟨ζ, hζ_int⟩
  let pb : PowerBasis ℚ K := hζ.powerBasis ℚ
  have hgen : pb.gen = ζ := IsPrimitiveRoot.powerBasis_gen ℚ hζ
  have hmin : minpoly ℚ ζ = Polynomial.cyclotomic N ℚ :=
    (hζ.minpoly_eq_cyclotomic_of_irreducible (Polynomial.cyclotomic.irreducible_rat hN)).symm
  -- Step 1: `discr K ∣ Algebra.discr ℤ (fun i => ζO ^ i.1)` via integral basis change matrix
  have hdiscr_dvd : discr K ∣ Algebra.discr ℤ (fun i : Fin pb.dim => ζO ^ i.1) := by
    let bInt := RingOfIntegers.basis K
    have hcard : pb.dim = Module.finrank ℚ K := by
      rw [← pb.finrank]
    let eIdx : Fin pb.dim ≃ Module.Free.ChooseBasisIndex ℤ (𝓞 K) :=
      Fintype.equivOfCardEq (by
        rw [Fintype.card_fin, ← Module.finrank_eq_card_chooseBasisIndex,
          RingOfIntegers.rank, hcard])
    let bZ : Module.Basis (Fin pb.dim) ℤ (𝓞 K) := bInt.reindex eIdx.symm
    let M : Matrix (Fin pb.dim) (Fin pb.dim) ℤ := fun i j => bZ.repr (ζO ^ i.1) j
    have htr_mat : Algebra.traceMatrix ℤ (fun i : Fin pb.dim => ζO ^ i.1) =
        M * Algebra.traceMatrix ℤ bZ * M.transpose := by
      ext i j
      simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.mul_apply,
        Matrix.transpose_apply]
      conv_lhs => rw [← bZ.sum_repr (ζO ^ i.1), ← bZ.sum_repr (ζO ^ j.1)]
      rw [Finset.sum_mul, map_sum]
      calc ∑ a, Algebra.trace ℤ (𝓞 K) (((bZ.repr (ζO ^ i.1)) a • bZ a) * ∑ b, (bZ.repr (ζO ^ j.1)) b • bZ b)
          = ∑ a, ∑ b, M i a * Algebra.trace ℤ (𝓞 K) (bZ a * bZ b) * M j b := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.mul_sum, map_sum]
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [smul_mul_assoc, mul_smul_comm, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
            simp only [M]; ring
        _ = ∑ b, (∑ a, M i a * Algebra.trace ℤ (𝓞 K) (bZ a * bZ b)) * M j b := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun b _ => (Finset.sum_mul _ _ _).symm
    have hdet : Algebra.discr ℤ (fun i : Fin pb.dim => ζO ^ i.1) = M.det ^ 2 * Algebra.discr ℤ bZ := by
      rw [Algebra.discr_def, Algebra.discr_def, htr_mat, Matrix.det_mul, Matrix.det_mul,
        Matrix.det_transpose]
      ring
    have hbZ_discr : Algebra.discr ℤ bZ = discr K := by
      unfold NumberField.discr
      have hbZ_eq : (bZ : Fin pb.dim → 𝓞 K) = bInt ∘ eIdx.symm.symm := funext fun i => by simp [bZ]
      rw [hbZ_eq, Algebra.discr_reindex ℤ bInt eIdx.symm]
    rw [hbZ_discr] at hdet
    exact ⟨M.det ^ 2, by rw [hdet, mul_comm]⟩
  -- Step 2: `((Algebra.discr ℤ (fun i => ζO ^ i.1) : ℤ) : ℚ) = Algebra.discr ℚ pb.basis`
  have hdiscr_cast : ((Algebra.discr ℤ (fun i : Fin pb.dim => ζO ^ i.1) : ℤ) : ℚ) =
      Algebra.discr ℚ pb.basis := by
    rw [Algebra.discr_def, Algebra.discr_def]
    change (Int.castRingHom ℚ) (Algebra.traceMatrix ℤ (fun i : Fin pb.dim => ζO ^ i.1)).det = _
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.traceMatrix_apply,
      Algebra.traceForm_apply, Int.coe_castRingHom]
    have htr : ((Algebra.trace ℤ (𝓞 K) (ζO ^ i.1 * ζO ^ j.1) : ℤ) : ℚ) =
        Algebra.trace ℚ K (algebraMap (𝓞 K) K (ζO ^ i.1 * ζO ^ j.1)) :=
      Algebra.coe_trace_int (K := K) _
    rw [htr, map_mul, map_pow, map_pow, pb.basis_eq_pow, pb.basis_eq_pow, hgen]
    rfl
  -- Step 3: `Algebra.discr ℚ pb.basis = (-1)^(d*(d-1)/2) * Algebra.norm ℚ (Φ_N'(ζ))`
  have hdiscr_norm := Algebra.discr_powerBasis_eq_norm ℚ pb
  rw [hgen, hmin] at hdiscr_norm
  -- Step 4: `Φ_N(X) ∣ X^N - 1` in `ℤ[X]` ⇒ `Φ_N'(ζ) * Q(ζ) = N * ζ^(N-1)` in `𝓞 K`
  have hdvd_poly : Polynomial.cyclotomic N ℤ ∣ Polynomial.X ^ N - 1 :=
    Polynomial.cyclotomic.dvd_X_pow_sub_one N ℤ
  obtain ⟨Q, hQ⟩ := hdvd_poly
  have hderiv := congrArg Polynomial.derivative hQ
  rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_one, sub_zero,
    Polynomial.derivative_mul] at hderiv
  have heval := congrArg (Polynomial.aeval ζO) hderiv
  have hroot : Polynomial.aeval ζO (Polynomial.cyclotomic N ℤ) = 0 := by
    apply Subtype.ext
    change (IsScalarTower.toAlgHom ℤ (𝓞 K) K) (Polynomial.aeval ζO (Polynomial.cyclotomic N ℤ)) = 0
    rw [← Polynomial.aeval_algHom_apply]
    change Polynomial.aeval ζ (Polynomial.cyclotomic N ℤ) = 0
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hζ.isRoot_cyclotomic hN
  rw [map_mul, map_add, map_mul, map_mul, hroot, zero_mul, add_zero, map_natCast,
    map_pow, Polynomial.aeval_X] at heval
  -- Take `Algebra.norm ℤ` of `N * ζO^(N-1) = Φ_N'(ζO) * Q(ζO)`
  have hnorm_eq := congrArg (Algebra.norm ℤ) heval
  rw [map_mul, map_mul, map_pow, map_natCast] at hnorm_eq
  have hnorm_ζ : (Algebra.norm ℤ ζO).natAbs = 1 := by
    have hpow : Algebra.norm ℤ ζO ^ N = 1 := by
      rw [← map_pow]
      have h1 : ζO ^ N = 1 := Subtype.ext (by
        change ζ ^ N = 1; exact hζ.pow_eq_one)
      rw [h1, map_one]
    have hpow_abs : (Algebra.norm ℤ ζO).natAbs ^ N = 1 := by
      rw [← Int.natAbs_pow, hpow]; rfl
    have hpos : 0 < (Algebra.norm ℤ ζO).natAbs := by
      by_contra h0
      have h0' : (Algebra.norm ℤ ζO).natAbs = 0 := by omega
      rw [h0', zero_pow hN.ne'] at hpow_abs; omega
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hpos) with h1 | hgt
    · exact h1.symm
    · exfalso; have := Nat.one_lt_pow hN.ne' hgt; omega
  have hnorm_N : Algebra.norm ℤ ((N : ℕ) : 𝓞 K) = (N : ℤ) ^ Module.finrank ℚ K := by
    have hcast : ((N : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) (N : ℤ) := by simp
    rw [hcast, Algebra.norm_algebraMap, RingOfIntegers.rank]
  have hnorm_lhs : (Algebra.norm ℤ ((N : ℕ) : 𝓞 K) * (Algebra.norm ℤ ζO) ^ (N - 1)).natAbs =
      N ^ Module.finrank ℚ K := by
    rw [hnorm_N, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_pow,
      Int.natAbs_natCast, hnorm_ζ, one_pow, mul_one]
  -- Relate `Algebra.norm ℤ (Φ_N'(ζO))` to `Algebra.norm ℚ (Φ_N'(ζ))`
  have hnorm_cast : ((Algebra.norm ℤ (Polynomial.aeval ζO (Polynomial.derivative (Polynomial.cyclotomic N ℤ))) : ℤ) : ℚ) =
      Algebra.norm ℚ (Polynomial.aeval ζ (Polynomial.derivative (Polynomial.cyclotomic N ℚ))) := by
    rw [Algebra.coe_norm_int]
    congr 1
    change (IsScalarTower.toAlgHom ℤ (𝓞 K) K)
      (Polynomial.aeval ζO (Polynomial.derivative (Polynomial.cyclotomic N ℤ))) = _
    rw [← Polynomial.aeval_algHom_apply]
    change Polynomial.aeval ζ (Polynomial.derivative (Polynomial.cyclotomic N ℤ)) = _
    rw [← Polynomial.aeval_map_algebraMap ℚ, ← Polynomial.derivative_map, Polynomial.map_cyclotomic]
  have habs_discr : (Algebra.discr ℤ (fun i : Fin pb.dim => ζO ^ i.1)).natAbs =
      (Algebra.norm ℤ (Polynomial.aeval ζO (Polynomial.derivative (Polynomial.cyclotomic N ℤ)))).natAbs := by
    have hQeq : ((Algebra.discr ℤ (fun i : Fin pb.dim => ζO ^ i.1) : ℤ) : ℚ) =
        ((-1 : ℚ) ^ (pb.dim * (pb.dim - 1) / 2)) *
          ((Algebra.norm ℤ (Polynomial.aeval ζO (Polynomial.derivative (Polynomial.cyclotomic N ℤ))) : ℤ) : ℚ) := by
      rw [hdiscr_cast, hdiscr_norm, hnorm_cast, pb.finrank]
    have hZeq : Algebra.discr ℤ (fun i : Fin pb.dim => ζO ^ i.1) =
        ((-1 : ℤ) ^ (pb.dim * (pb.dim - 1) / 2)) *
          Algebra.norm ℤ (Polynomial.aeval ζO (Polynomial.derivative (Polynomial.cyclotomic N ℤ))) := by
      exact_mod_cast hQeq
    rw [hZeq, Int.natAbs_mul, Int.natAbs_pow]
    simp
  have hdvd_nat : (discr K).natAbs ∣ N ^ Module.finrank ℚ K := by
    have h1 : (discr K).natAbs ∣ (Algebra.discr ℤ (fun i : Fin pb.dim => ζO ^ i.1)).natAbs :=
      Int.natAbs_dvd_natAbs.mpr hdiscr_dvd
    rw [habs_discr] at h1
    have h2 : (Algebra.norm ℤ (Polynomial.aeval ζO (Polynomial.derivative (Polynomial.cyclotomic N ℤ)))).natAbs ∣
        N ^ Module.finrank ℚ K := by
      rw [← hnorm_lhs, hnorm_eq, Int.natAbs_mul]
      exact dvd_mul_right _ _
    exact h1.trans h2
  exact Nat.le_of_dvd (pow_pos hN _) hdvd_nat

/-- **Unconditional Cyclotomic Subfield Discriminant Bound (`0` parameters!)**:
For EVERY number field `E` embedding in `CyclotomicField N ℚ` (`0 < N`),
`(discr E).natAbs ≤ N ^ [E : ℚ]` and `[E : ℚ] ≤ N`! -/
theorem natAbs_discr_le_pow_of_cyclotomic (E : Type) [Field E] [NumberField E]
    (N : ℕ) (hN : 0 < N) (hE : Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ)) :
    (discr E).natAbs ≤ N ^ Module.finrank ℚ E ∧ Module.finrank ℚ E ≤ N := by
  obtain ⟨φ⟩ := hE
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero (N : ℚ) := ⟨Nat.cast_ne_zero.mpr hN.ne'⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  let K := CyclotomicField N ℚ
  let F : IntermediateField ℚ K := φ.fieldRange
  let eEF : E ≃ₐ[ℚ] F := AlgEquiv.ofInjectiveField φ
  have hrank : Module.finrank ℚ E = Module.finrank ℚ F := eEF.toLinearEquiv.finrank_eq
  have hdisc : discr E = discr F := NumberField.discr_eq_discr_of_algEquiv E eEF
  have htow := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    F (𝓞 F) K (𝓞 K)
  have hdiff_pos : 0 < Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 K)) := by
    by_contra h0
    have h0' : Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 K)) = 0 := by omega
    rw [h0', zero_mul] at htow
    exact Int.natAbs_ne_zero.mpr (discr_ne_zero K) htow
  have hpow_le : (discr F).natAbs ^ Module.finrank F K ≤ (discr K).natAbs := by
    rw [htow]
    exact Nat.le_mul_of_pos_left _ hdiff_pos
  have hK_le : (discr K).natAbs ≤ N ^ Module.finrank ℚ K := natAbs_discr_cyclotomic_le N hN
  have hfin_mul : Module.finrank ℚ F * Module.finrank F K = Module.finrank ℚ K :=
    Module.finrank_mul_finrank ℚ F K
  have hpow_le2 : (discr F).natAbs ^ Module.finrank F K ≤ (N ^ Module.finrank ℚ F) ^ Module.finrank F K := by
    rw [← pow_mul, hfin_mul]
    exact hpow_le.trans hK_le
  have hFK_pos : 0 < Module.finrank F K := Module.finrank_pos
  have hdiscr_le : (discr F).natAbs ≤ N ^ Module.finrank ℚ F := by
    by_contra hgt
    push Not at hgt
    exact absurd hpow_le2 (not_le.mpr (Nat.pow_lt_pow_left hgt hFK_pos.ne'))
  refine ⟨?_, ?_⟩
  · rwa [hdisc, hrank]
  · have hinj : Function.Injective φ.toLinearMap := (φ : E →+* K).injective
    have h := LinearMap.finrank_le_finrank_of_injective hinj
    rw [IsCyclotomicExtension.finrank K (Polynomial.cyclotomic.irreducible_rat hN)] at h
    exact h.trans (Nat.totient_le N)

/-- **Unconditional Cyclotomic Class-Number Log Bound (`0` parameters!)**:
For EVERY `E ↪ CyclotomicField N ℚ` (`2 ≤ N`), `Real.log (classNumber E) ≤ 3 * [E : ℚ] * Real.log N`. -/
theorem log_classNumber_le_of_cyclotomic (E : Type) [Field E] [NumberField E]
    (N : ℕ) (hN : 2 ≤ N) (hE : Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ)) :
    Real.log (classNumber E) ≤ 3 * Module.finrank ℚ E * Real.log N := by
  obtain ⟨hd, hn⟩ := natAbs_discr_le_pow_of_cyclotomic E N (by omega) hE
  have hc := log_classNumber_le E
  have hd1 : (1 : ℝ) ≤ |(discr E : ℝ)| := by
    exact_mod_cast Int.one_le_abs (discr_ne_zero E)
  have hd2 : |(discr E : ℝ)| ≤ (N : ℝ) ^ Module.finrank ℚ E := by
    have h : (((discr E).natAbs : ℕ) : ℝ) ≤ (N : ℝ) ^ Module.finrank ℚ E := by exact_mod_cast hd
    rwa [Nat.cast_natAbs, Int.cast_abs] at h
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn' : (Module.finrank ℚ E : ℝ) ≤ N := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ (Module.finrank ℚ E : ℝ) := Nat.cast_nonneg _
  generalize Module.finrank ℚ E = n at *
  have hL0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hL1 : Real.log N ≤ N - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hD0 : 0 ≤ Real.log |(discr E : ℝ)| := Real.log_nonneg hd1
  have hD : Real.log |(discr E : ℝ)| ≤ n * Real.log N := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by linarith) hd2
  have hnL : (n : ℝ) * Real.log N ≤ N * (N - 1) := mul_le_mul hn' hL1 hL0 (by linarith)
  have h2 : Real.log (1 + Real.log |(discr E : ℝ)| / 2) ≤ 2 * Real.log N := by
    have e : 2 * Real.log N = Real.log ((N : ℝ) ^ 2) := by rw [Real.log_pow]; norm_num
    rw [e]
    apply Real.log_le_log (by linarith)
    nlinarith
  have h3 := mul_le_mul_of_nonneg_left h2 hn0
  have h4 := mul_nonneg hn0 hL0
  nlinarith

end FiniteLengthAndClassNumberBounds

/-! ## Section 2: Kummer `S`-Unit Rank & `SelK(S_l, l) / l` Cardinality Bound (`0` Parameters!) -/

section KummerSUnitAndSelmerCardBounds

/-- Additive valuation `ord_v(a) : ℤ` of a nonzero field element `a : Kˣ` at `v`. -/
def ordv {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) : ℤ :=
  -Multiplicative.toAdd (v.valuationOfNeZero a)

@[simp] theorem ordv_one {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    ordv v 1 = 0 := by simp [ordv]

@[simp] theorem ordv_mul {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (a b : Kˣ) : ordv v (a * b) = ordv v a + ordv v b := by
  simp [ordv, add_comm]

@[simp] theorem ordv_inv {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (a : Kˣ) : ordv v a⁻¹ = -ordv v a := by
  simp [ordv]

@[simp] theorem ordv_pow {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (a : Kˣ) (n : ℕ) : ordv v (a ^ n) = n * ordv v a := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, ordv_mul, ih]; push_cast; ring

/-- The `n`-th power subgroup `(Kˣ)^n ≤ Kˣ`. -/
def powK (K : Type) [Field K] (n : ℕ) : Subgroup Kˣ :=
  (powMonoidHom n : Kˣ →* Kˣ).range

/-- The Kummer `S`-Selmer subgroup `SelK S n = {a ∈ Kˣ | ∀ v ∉ S, n ∣ ord_v(a)}`. -/
def SelK {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    Subgroup Kˣ where
  carrier := {a | ∀ v ∉ S, (n : ℤ) ∣ ordv v a}
  one_mem' _ _ := by simp
  mul_mem' ha hb v hv := by rw [ordv_mul]; exact dvd_add (ha v hv) (hb v hv)
  inv_mem' ha v hv := by rw [ordv_inv]; exact dvd_neg.mpr (ha v hv)

/-- Prime class `[v] ∈ ClassGroup (𝓞 K)`. -/
def primeCl {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    ClassGroup (𝓞 K) :=
  ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩

/-- Subgroup of `ClassGroup (𝓞 K)` generated by primes in `S`. -/
def clSub {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) :
    Subgroup (ClassGroup (𝓞 K)) :=
  Subgroup.closure (primeCl '' S)

/-- The `S`-class group `Cl_S(K) = ClassGroup (𝓞 K) ⧸ clSub S`. -/
abbrev ClS {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) : Type :=
  ClassGroup (𝓞 K) ⧸ clSub S

/-- The `n`-th root ideal class `∏_v [v]^{ord_v(a) / n} ∈ ClassGroup (𝓞 K)`. -/
def radCl {K : Type} [Field K] [NumberField K] (n : ℕ) (a : Kˣ) : ClassGroup (𝓞 K) :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K), primeCl v ^ (ordv v a / (n : ℤ))

/-- Number of primes of `𝓞 K` lying over `l` is at most `[K : ℚ]`. -/
theorem card_above_le_finrank (K : Type) [Field K] [NumberField K] (l : ℕ) [hl : Fact l.Prime] :
    Nat.card (Above K l) ≤ Module.finrank ℚ K := by
  classical
  have hn : l.Prime := hl.out
  have hp0 : (Ideal.span {(l : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hn.ne_zero
  have hmax : (Ideal.span {(l : ℤ)} : Ideal ℤ).IsMaximal := inferInstance
  let Sfin : Finset (HeightOneSpectrum (𝓞 K)) := (above_finite (F := K) l).toFinset
  have hcard_eq : Nat.card (Above K l) = Sfin.card := by
    rw [show Above K l = (Sfin : Set (HeightOneSpectrum (𝓞 K))) from (Set.Finite.coe_toFinset _).symm,
      Nat.card_coe_set_eq, Set.ncard_coe_finset]
  rw [hcard_eq]
  refine le_trans (Finset.card_le_card_of_injOn
    (t := IsDedekindDomain.primesOverFinset (Ideal.span {(l : ℤ)}) (𝓞 K))
    (fun p => p.asIdeal) ?_ ?_) (card_primesOverFinset_le_finrank_rat K l hp0)
  · intro p hp
    have hp' : ((l : ℕ) : 𝓞 K) ∈ p.asIdeal := by
      simpa [Sfin, Above] using hp
    rw [Finset.mem_coe, IsDedekindDomain.mem_primesOverFinset_iff hp0]
    have := p.isPrime
    refine ⟨p.isPrime, ⟨hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_⟩⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact hp'
  · intro p _ p' _ h
    exact HeightOneSpectrum.ext h

/-- `S`-unit subgroup `S.unit K = {a ∈ Kˣ | ∀ v ∉ S, v(a) = 1}` as a `Subgroup Kˣ`. -/
def sUnitSubgroup {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) :
    Subgroup Kˣ where
  carrier := {a | ∀ v ∉ S, v.valuation K (a : K) = 1}
  one_mem' _ _ := by simp
  mul_mem' ha hb v hv := by simp [ha v hv, hb v hv]
  inv_mem' ha v hv := by simp [ha v hv]

private theorem mem_sUnit_iff_ordv {K : Type} [Field K] [NumberField K]
    {S : Set (HeightOneSpectrum (𝓞 K))} {a : Kˣ} :
    a ∈ sUnitSubgroup S ↔ ∀ v ∉ S, ordv v a = 0 := by
  change (∀ v ∉ S, v.valuation K (a : K) = 1) ↔ _
  refine forall₂_congr fun v _ => ?_
  rw [← HeightOneSpectrum.valuationOfNeZero_eq, ← WithZero.coe_one, WithZero.coe_inj, ordv,
    neg_eq_zero, toAdd_eq_zero]

private theorem sUnit_valuation_hom_ker {K : Type} [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) :
    let valHom : Additive (sUnitSubgroup S) →ₗ[ℤ] (S → ℤ) :=
      AddMonoidHom.toIntLinearMap
        { toFun := fun x v => ordv v.1 (x.toMul : Kˣ)
          map_zero' := by funext v; simp
          map_add' := fun x y => by funext v; simp }
    let ofUnits : (𝓞 K)ˣ →* sUnitSubgroup S :=
      { toFun := fun u => ⟨Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) u, fun v _ => by
          rw [← HeightOneSpectrum.valuationOfNeZero_eq, HeightOneSpectrum.valuation_of_unit_eq,
            WithZero.coe_one]⟩
        map_one' := Subtype.ext (by ext; simp)
        map_mul' := fun a b => Subtype.ext (by ext; simp) }
    Function.Injective ofUnits ∧ LinearMap.ker valHom = LinearMap.range ofUnits.toAdditive.toIntLinearMap := by
  intro valHom ofUnits
  refine ⟨fun u₁ u₂ h => ?_, ?_⟩
  · have hval : algebraMap (𝓞 K) K (u₁ : 𝓞 K) = algebraMap (𝓞 K) K (u₂ : 𝓞 K) :=
      congrArg (fun x : sUnitSubgroup S => ((x.1 : Kˣ) : K)) h
    exact Units.ext (IsFractionRing.injective (𝓞 K) K hval)
  · ext x
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    constructor
    · intro hx
      have hall : ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K ((x.toMul : Kˣ) : K) = 1 := by
        intro v
        by_cases hv : v ∈ S
        · have h1 : ordv v (x.toMul : Kˣ) = 0 := congrFun hx ⟨v, hv⟩
          rw [ordv, neg_eq_zero, toAdd_eq_zero] at h1
          rw [← HeightOneSpectrum.valuationOfNeZero_eq, h1, WithZero.coe_one]
        · exact x.toMul.2 v hv
      obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K
        ((x.toMul : Kˣ) : K) fun v => (hall v).le
      obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K
        (((x.toMul : Kˣ)⁻¹ : Kˣ) : K) fun v => by
          rw [Units.val_inv_eq_inv_val, map_inv₀, hall v, inv_one]
      have hab : a * b = 1 := by
        apply IsFractionRing.injective (𝓞 K) K
        rw [map_mul, ha, hb, map_one, Units.mul_inv]
      let u : (𝓞 K)ˣ := ⟨a, b, hab, mul_comm a b ▸ hab⟩
      refine ⟨Additive.ofMul u, ?_⟩
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Units.ext
      simpa [ofUnits, u] using ha
    · rintro ⟨u, rfl⟩
      funext v
      change ordv v.1 (Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) u.toMul) = 0
      rw [ordv, neg_eq_zero, toAdd_eq_zero]
      exact HeightOneSpectrum.valuation_of_unit_eq v.1 u.toMul

/-- Index of `l • M` in a finitely generated torsion-free `ℤ`-module `M` equals `l ^ finrank ℤ M`. -/
private theorem index_nsmul_range_free_int {M : Type*} [AddCommGroup M] [Module.Finite ℤ M]
    [Module.IsTorsionFree ℤ M] (l : ℕ) (hl : 0 < l) :
    (AddMonoidHom.range (nsmulAddMonoidHom l : M →+ M)).index = l ^ Module.finrank ℤ M := by
  classical
  haveI : NeZero l := ⟨hl.ne'⟩
  haveI : Module.Free ℤ M := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis ℤ M
  let ι := Module.Free.ChooseBasisIndex ℤ M
  have hcard : Fintype.card ι = Module.finrank ℤ M := (Module.finrank_eq_card_chooseBasisIndex ℤ M).symm
  let φ : M →+ (ι → ZMod l) :=
    { toFun := fun m i => ((b.repr m i : ℤ) : ZMod l)
      map_zero' := by ext i; simp
      map_add' := fun x y => by ext i; simp }
  have hsurj : Function.Surjective φ := fun f => by
    refine ⟨b.repr.symm (Finsupp.equivFunOnFinite.symm fun i => ((f i).val : ℤ)), ?_⟩
    ext i
    simp [φ]
  have hker : φ.ker = AddMonoidHom.range (nsmulAddMonoidHom l : M →+ M) := by
    ext m
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    constructor
    · intro hm
      have hdvd : ∀ i : ι, (l : ℤ) ∣ b.repr m i := fun i =>
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ l).mp (congrFun hm i)
      choose c hc using hdvd
      refine ⟨b.repr.symm (Finsupp.equivFunOnFinite.symm c), ?_⟩
      apply b.repr.injective
      ext i
      simp only [nsmulAddMonoidHom_apply, map_nsmul, Finsupp.coe_smul, Pi.smul_apply,
        nsmul_eq_mul, LinearEquiv.apply_symm_apply]
      exact (hc i).symm
    · rintro ⟨x, rfl⟩
      ext i
      simp only [φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, nsmulAddMonoidHom_apply, map_nsmul,
        Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]
  rw [← hker, AddSubgroup.index_eq_card,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective φ hsurj).toEquiv,
    Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, hcard]

/-- **Dirichlet `S`-Unit Power-Quotient Cardinality Bound (`0` parameters!)**:
For any finite set `S` of primes of `𝓞 K` and prime `l`,
`Finite (sUnitSubgroup S ⧸ (powK K l).subgroupOf (sUnitSubgroup S))` and
`Nat.card (sUnitSubgroup S ⧸ (powK K l).subgroupOf (sUnitSubgroup S)) ≤ l ^ (Units.rank K + Nat.card S + 1)`. -/
theorem card_sUnit_quot_pow_le (K : Type) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] (l : ℕ) [hl : Fact l.Prime] :
    Finite (sUnitSubgroup S ⧸ (powK K l).subgroupOf (sUnitSubgroup S)) ∧
    Nat.card (sUnitSubgroup S ⧸ (powK K l).subgroupOf (sUnitSubgroup S)) ≤
      l ^ (NumberField.Units.rank K + Nat.card S + 1) := by
  classical
  have hl0 : l ≠ 0 := hl.out.ne_zero
  -- Exact sequence `0 → Additive (𝓞 K)ˣ → Additive (sUnitSubgroup S) → (S → ℤ)`
  let valHom : Additive (sUnitSubgroup S) →ₗ[ℤ] (S → ℤ) :=
    AddMonoidHom.toIntLinearMap
      { toFun := fun x v => ordv v.1 (x.toMul : Kˣ)
        map_zero' := by funext v; simp
        map_add' := fun x y => by funext v; simp }
  obtain ⟨hinj, hker⟩ := sUnit_valuation_hom_ker S
  letI : Fintype S := Fintype.ofFinite S
  -- Finiteness and `ℤ`-rank of `Additive (𝓞 K)ˣ` directly from `NumberField.Units.basisModTorsion`
  let qU : Additive (𝓞 K)ˣ →ₗ[ℤ] Additive ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K) :=
    (QuotientGroup.mk' (NumberField.Units.torsion K)).toAdditive.toIntLinearMap
  have hqU_surj : Function.Surjective qU := fun y =>
    let ⟨x, hx⟩ := QuotientGroup.mk'_surjective (NumberField.Units.torsion K) y.toMul
    ⟨Additive.ofMul x, hx⟩
  haveI : Module.Finite ℤ (Additive ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K)) :=
    Module.Finite.of_basis (NumberField.Units.basisModTorsion K)
  have hkerU_fin : Finite (LinearMap.ker qU) := by
    let fU : LinearMap.ker qU → NumberField.Units.torsion K := fun ⟨x, hx⟩ =>
      ⟨x.toMul, (QuotientGroup.eq_one_iff _).mp hx⟩
    exact Finite.of_injective fU fun a b hab =>
      Subtype.ext (Additive.toMul.injective (congrArg (fun z : NumberField.Units.torsion K => z.1) hab))
  haveI : Module.Finite ℤ (LinearMap.ker qU) := Module.Finite.of_finite
  haveI : Module.Finite ℤ (Additive (𝓞 K)ˣ ⧸ LinearMap.ker qU) :=
    Module.Finite.equiv (qU.quotKerEquivOfSurjective hqU_surj).symm
  haveI : Module.Finite ℤ (Additive (𝓞 K)ˣ) :=
    Module.Finite.of_submodule_quotient (LinearMap.ker qU)
  have hrank_units : Module.finrank ℤ (Additive (𝓞 K)ˣ) = NumberField.Units.rank K := by
    have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.ker qU)
    have h2 : Module.finrank ℤ (Additive (𝓞 K)ˣ ⧸ LinearMap.ker qU) = NumberField.Units.rank K := by
      rw [(qU.quotKerEquivOfSurjective hqU_surj).finrank_eq,
        Module.finrank_eq_card_basis (NumberField.Units.basisModTorsion K), Fintype.card_fin]
    have h3 : Module.finrank ℤ (LinearMap.ker qU) = 0 := by
      have hrank0 : Module.rank ℤ (LinearMap.ker qU) = 0 := by
        rw [rank_eq_zero_iff]
        intro x
        haveI : Finite (LinearMap.ker qU) := hkerU_fin
        obtain ⟨n, hn, hnx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp (isOfFinAddOrder_of_finite x)
        exact ⟨(n : ℤ), by exact_mod_cast hn.ne', by rw [natCast_zsmul]; exact hnx⟩
      rw [Module.finrank, hrank0, map_zero]
    omega
  let eKer : Additive (𝓞 K)ˣ ≃ₗ[ℤ] LinearMap.ker valHom :=
    (LinearEquiv.ofInjective _ (fun a b h => Additive.toMul.injective (hinj (congrArg Additive.toMul h)))).trans
      (LinearEquiv.ofEq _ _ hker.symm)
  haveI : Module.Finite ℤ (LinearMap.ker valHom) := Module.Finite.equiv eKer
  haveI : Module.Finite ℤ (LinearMap.range valHom) := inferInstance
  haveI : Module.Finite ℤ (Additive (sUnitSubgroup S) ⧸ LinearMap.ker valHom) :=
    Module.Finite.equiv valHom.quotKerEquivRange.symm
  haveI : Module.Finite ℤ (Additive (sUnitSubgroup S)) :=
    Module.Finite.of_submodule_quotient (LinearMap.ker valHom)
  -- Rank of `Additive (sUnitSubgroup S)`: `≤ Units.rank K + Nat.card S`
  have hrank_ker : Module.finrank ℤ (LinearMap.ker valHom) = NumberField.Units.rank K := by
    rw [← eKer.finrank_eq, hrank_units]
  have hrank_range : Module.finrank ℤ (LinearMap.range valHom) ≤ Nat.card S := by
    calc Module.finrank ℤ (LinearMap.range valHom)
        ≤ Module.finrank ℤ (S → ℤ) := Submodule.finrank_le _
      _ = Fintype.card S := Module.finrank_fintype_fun_eq_card ℤ
      _ = Nat.card S := (Nat.card_eq_fintype_card).symm
  have hrank_sUnit : Module.finrank ℤ (Additive (sUnitSubgroup S)) ≤
      NumberField.Units.rank K + Nat.card S := by
    have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.ker valHom)
    rw [valHom.quotKerEquivRange.finrank_eq] at h1
    omega
  -- Identify `(powK K l).subgroupOf (sUnitSubgroup S) = (powMonoidHom l : sUnitSubgroup S →* _).range`
  have hpow_eq : (powK K l).subgroupOf (sUnitSubgroup S) =
      (powMonoidHom l : sUnitSubgroup S →* sUnitSubgroup S).range := by
    ext x
    rw [Subgroup.mem_subgroupOf, powK, MonoidHom.mem_range, MonoidHom.mem_range]
    constructor
    · rintro ⟨b, hb⟩
      rw [powMonoidHom_apply] at hb
      have hbS : b ∈ sUnitSubgroup S := by
        intro v hv
        have h1 : v.valuation K ((b ^ l : Kˣ) : K) = 1 := hb ▸ x.2 v hv
        rw [Units.val_pow_eq_pow_val, map_pow] at h1
        have hne0 : v.valuation K (b : K) ≠ 0 := by
          intro h0; rw [h0, zero_pow hl0] at h1; exact zero_ne_one h1
        obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.mp hne0
        rw [← hu, ← WithZero.coe_pow, ← WithZero.coe_one, WithZero.coe_inj] at h1
        have hu1 : u = 1 := by
          have := congrArg Multiplicative.toAdd h1
          simp only [toAdd_pow, toAdd_one, nsmul_eq_mul] at this
          have h0 : Multiplicative.toAdd u = 0 := (mul_eq_zero.mp this).resolve_left (by exact_mod_cast hl0)
          exact Multiplicative.toAdd.injective (h0.trans toAdd_one.symm)
        rw [← hu, hu1, WithZero.coe_one]
      exact ⟨⟨b, hbS⟩, Subtype.ext hb⟩
    · rintro ⟨c, hc⟩
      exact ⟨c.1, congrArg Subtype.val hc⟩
  -- Split `sUnitSubgroup S` by its torsion subgroup `T`
  set G := sUnitSubgroup S
  set T := CommGroup.torsion G
  set N := (powMonoidHom l : G →* G).range
  let qGT : Additive G →ₗ[ℤ] Additive (G ⧸ T) := (QuotientGroup.mk' T).toAdditive.toIntLinearMap
  have hqGT_surj : Function.Surjective qGT := QuotientGroup.mk'_surjective T
  haveI : Module.Finite ℤ (Additive (G ⧸ T)) :=
    Module.Finite.of_surjective qGT hqGT_surj
  haveI : Module.IsTorsionFree ℤ (Additive (G ⧸ T)) := by
    refine Module.isTorsionFree_iff_smul_eq_zero.mpr fun r x hrx => ?_
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective T x.toMul
      have hpow1 : (QuotientGroup.mk' T g) ^ r.natAbs = 1 := by
        have h1 : (r • Additive.ofMul (QuotientGroup.mk' T g)) = 0 := hrx
        have h2 : (QuotientGroup.mk' T g) ^ r = 1 := h1
        rcases Int.natAbs_eq r with heq | heq
        · rwa [← zpow_natCast, ← heq]
        · have : (QuotientGroup.mk' T g) ^ (-(r.natAbs : ℤ)) = 1 := by rwa [← heq]
          rw [zpow_neg, inv_eq_one, zpow_natCast] at this
          exact this
      rw [← map_pow] at hpow1
      have hpow1' : g ^ r.natAbs ∈ T := (QuotientGroup.eq_one_iff _).mp hpow1
      have hgT : g ∈ T := (isOfFinOrder_pow.mp hpow1').resolve_right (Int.natAbs_ne_zero.mpr hr)
      show Additive.ofMul (QuotientGroup.mk' T g) = 0
      exact (QuotientGroup.eq_one_iff g).mpr hgT
  have hrank_quot : Module.finrank ℤ (Additive (G ⧸ T)) ≤ Module.finrank ℤ (Additive G) := by
    have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.ker qGT)
    rw [(qGT.quotKerEquivOfSurjective hqGT_surj).finrank_eq] at h1
    omega
  have hsup_eq : N ⊔ T = (powMonoidHom l : G ⧸ T →* G ⧸ T).range.comap (QuotientGroup.mk' T) := by
    ext x
    simp only [Subgroup.mem_comap, MonoidHom.mem_range, powMonoidHom_apply]
    constructor
    · intro hx
      obtain ⟨_, ⟨b, rfl⟩, t, ht, rfl⟩ := Subgroup.mem_sup.1 hx
      refine ⟨QuotientGroup.mk' T b, ?_⟩
      have h1 : QuotientGroup.mk' T t = 1 := (QuotientGroup.eq_one_iff t).2 ht
      rw [map_mul, h1, mul_one, powMonoidHom_apply, map_pow]
    · rintro ⟨q, hq⟩
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective T q
      have ht : (b ^ l)⁻¹ * x ∈ T := by
        rw [← QuotientGroup.eq]; rw [← map_pow] at hq; exact hq
      have h := Subgroup.mul_mem_sup (S := N) (T := T) ⟨b, rfl⟩ ht
      rwa [powMonoidHom_apply, mul_inv_cancel_left] at h
  have hQ_idx : (powMonoidHom l : G ⧸ T →* G ⧸ T).range.index =
      l ^ Module.finrank ℤ (Additive (G ⧸ T)) :=
    index_nsmul_range_free_int (M := Additive (G ⧸ T)) l hl.out.pos
  have hsup_idx : (N ⊔ T).index = l ^ Module.finrank ℤ (Additive (G ⧸ T)) := by
    rw [hsup_eq, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective T), hQ_idx]
  -- Torsion subgroup `T` injects into `NumberField.Units.torsion K`, hence `Finite T` and `|T[l]| ≤ l`!
  have hT_fin : Finite T := by
    have hinjT : Function.Injective (fun t : T => ((t.1.1 : Kˣ) : K)) :=
      fun a b h => Subtype.ext (Subtype.ext (Units.ext h))
    have hmem_unit : ∀ t : T, ∃ u : NumberField.Units.torsion K, ((u.1 : 𝓞 K) : K) = ((t.1.1 : Kˣ) : K) := fun t => by
      have hfin_G : IsOfFinOrder t.1 := t.2
      obtain ⟨m, hm, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin_G
      have hpowK : (t.1.1 : Kˣ) ^ m = 1 := congrArg Subtype.val hpow
      have hval1 : ∀ v : HeightOneSpectrum (𝓞 K), v.valuation K ((t.1.1 : Kˣ) : K) = 1 := fun v => by
        have h1 : v.valuation K (((t.1.1 : Kˣ) : K) ^ m) = 1 := by
          rw [← Units.val_pow_eq_pow_val, hpowK, Units.val_one, map_one]
        rw [map_pow] at h1
        have hne0 : v.valuation K ((t.1.1 : Kˣ) : K) ≠ 0 := by
          intro h0; rw [h0, zero_pow hm.ne'] at h1; exact zero_ne_one h1
        obtain ⟨w, hw⟩ := WithZero.ne_zero_iff_exists.mp hne0
        rw [← hw, ← WithZero.coe_pow, ← WithZero.coe_one, WithZero.coe_inj] at h1
        have hw1 : w = 1 := by
          have := congrArg Multiplicative.toAdd h1
          simp only [toAdd_pow, toAdd_one, nsmul_eq_mul] at this
          exact Multiplicative.toAdd.injective
            (((mul_eq_zero.mp this).resolve_left (by exact_mod_cast hm.ne')).trans toAdd_one.symm)
        rw [← hw, hw1, WithZero.coe_one]
      obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K
        ((t.1.1 : Kˣ) : K) fun v => (hval1 v).le
      obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K
        (((t.1.1)⁻¹ : Kˣ) : K) fun v => by
          rw [Units.val_inv_eq_inv_val, map_inv₀, hval1 v, inv_one]
      have hab : a * b = 1 := by
        apply IsFractionRing.injective (𝓞 K) K
        rw [map_mul, ha, hb, map_one, Units.mul_inv]
      let u : (𝓞 K)ˣ := ⟨a, b, hab, mul_comm a b ▸ hab⟩
      have hu_fin : IsOfFinOrder u := isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, Units.ext (by
        apply IsFractionRing.injective (𝓞 K) K
        rw [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one]
        change (algebraMap (𝓞 K) K a) ^ m = 1
        rw [ha, ← Units.val_pow_eq_pow_val, hpowK, Units.val_one])⟩
      exact ⟨⟨u, hu_fin⟩, ha⟩
    choose f hf using hmem_unit
    exact Finite.of_injective f fun a b hab => hinjT (by dsimp only; rw [← hf a, ← hf b, hab])
  have hrel_eq : N.relIndex T = (powMonoidHom l : T →* T).range.index := by
    rw [Subgroup.relIndex]
    congr 1
    ext ⟨t, ht⟩
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range, MonoidHom.mem_range]
    constructor
    · rintro ⟨x, hx⟩
      rw [powMonoidHom_apply] at hx
      have hxT : x ∈ T := (isOfFinOrder_pow.1 (hx ▸ ht)).resolve_right hl0
      exact ⟨⟨x, hxT⟩, Subtype.ext hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨x.1, congrArg Subtype.val hx⟩
  have hrel_le : (powMonoidHom l : T →* T).range.index ≤ l := by
    have h1 := Subgroup.card_mul_index (powMonoidHom l : T →* T).range
    have h2 := Subgroup.card_mul_index (powMonoidHom l : T →* T).ker
    have hk : (powMonoidHom l : T →* T).ker.index = Nat.card (powMonoidHom l : T →* T).range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange (powMonoidHom l : T →* T)).toEquiv
    rw [hk] at h2
    have hidx_eq : (powMonoidHom l : T →* T).range.index = Nat.card (powMonoidHom l : T →* T).ker := by
      have hpos : 0 < Nat.card (powMonoidHom l : T →* T).range := Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h1, ← h2, mul_comm])
    rw [hidx_eq]
    let poly : Polynomial K := Polynomial.X ^ l - 1
    have hpoly_ne : poly ≠ 0 := Polynomial.X_pow_sub_C_ne_zero hl.out.pos (1 : K)
    let fKer : (powMonoidHom l : T →* T).ker → {x : K // x ∈ poly.roots.toFinset} := fun t =>
      ⟨((t.1.1.1 : Kˣ) : K), by
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hpoly_ne, Polynomial.IsRoot.def]
        simp only [poly, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
        have ht : t.1 ^ l = 1 := t.2
        have hval : ((t.1.1.1 : Kˣ) : K) ^ l = 1 := by
          have := congrArg (fun z : T => ((z.1.1 : Kˣ) : K)) ht
          simpa using this
        rw [hval, sub_self]⟩
    have hfKer_inj : Function.Injective fKer := fun a b h =>
      Subtype.ext (Subtype.ext (Subtype.ext (Units.ext (congrArg Subtype.val h))))
    calc Nat.card (powMonoidHom l : T →* T).ker
        ≤ Nat.card {x : K // x ∈ poly.roots.toFinset} := Nat.card_le_card_of_injective fKer hfKer_inj
      _ = poly.roots.toFinset.card := Nat.card_eq_finsetCard _
      _ ≤ poly.roots.card := Multiset.toFinset_card_le _
      _ ≤ poly.natDegree := Polynomial.card_roots' poly
      _ = l := by
          rw [show poly = Polynomial.X ^ l - Polynomial.C 1 by simp [poly],
            Polynomial.natDegree_X_pow_sub_C]
  have hN_idx : N.index = l ^ Module.finrank ℤ (Additive (G ⧸ T)) * (powMonoidHom l : T →* T).range.index := by
    rw [← Subgroup.relIndex_mul_index (le_sup_left : N ≤ N ⊔ T), Subgroup.relIndex_sup_left,
      hrel_eq, hsup_idx, mul_comm]
  have hN_pos : 0 < N.index := by
    rw [hN_idx]
    have hrel_pos : 0 < (powMonoidHom l : T →* T).range.index :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    exact Nat.mul_pos (pow_pos hl.out.pos _) hrel_pos
  have hN_le : N.index ≤ l ^ (NumberField.Units.rank K + Nat.card S + 1) := by
    rw [hN_idx, pow_succ]
    refine Nat.mul_le_mul ?_ hrel_le
    exact Nat.pow_le_pow_right hl.out.pos (hrank_quot.trans hrank_sUnit)
  rw [hpow_eq]
  refine ⟨Nat.finite_of_card_ne_zero (by change N.index ≠ 0; omega), ?_⟩
  exact hN_le

private theorem clProd_facts (K : Type) [Field K] [NumberField K] :
    (∀ I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ,
      ClassGroup.mk K I = ∏ᶠ v, primeCl v ^ FractionalIdeal.count K v I.1) ∧
    (∀ (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ),
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (a : K)) = ordv v a) ∧
    (∀ a : Kˣ, {v : HeightOneSpectrum (𝓞 K) | ordv v a ≠ 0}.Finite) := by
  have h1 : ∀ I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ,
      ClassGroup.mk K I = ∏ᶠ v, primeCl v ^ FractionalIdeal.count K v I.1 := by
    intro I
    let P : HeightOneSpectrum (𝓞 K) → (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ := fun v =>
      FractionalIdeal.mk0 K ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩
    have hfin : (Function.mulSupport fun v => P v ^ FractionalIdeal.count K v I.1).Finite :=
      (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors I.1)).subset
        fun v hv h => hv (by simp only [h, zpow_zero])
    have hI : ∏ᶠ v, P v ^ FractionalIdeal.count K v I.1 = I := by
      apply Units.ext
      rw [← Units.coeHom_apply, map_finprod _ hfin]
      conv_rhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K I.ne_zero]
      exact finprod_congr fun v => by simp [Units.val_zpow_eq_zpow_val, P]
    conv_lhs => rw [← hI]
    rw [map_finprod _ hfin]
    exact finprod_congr fun v => by rw [map_zpow, ClassGroup.mk_mk0]; rfl
  have h2 : ∀ (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ),
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (a : K)) = ordv v a := by
    intro v a
    have hI : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (a : K) =
        FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K))
          (algebraMap (𝓞 K) K (IsLocalization.sec (nonZeroDivisors (𝓞 K)) (a : K)).2)⁻¹ *
          ↑(Ideal.span {(IsLocalization.sec (nonZeroDivisors (𝓞 K)) (a : K)).1} : Ideal (𝓞 K)) := by
      rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton,
        IsLocalization.sec_spec' (nonZeroDivisors (𝓞 K)) (a : K), inv_mul_cancel_left₀]
      simp [nonZeroDivisors.coe_ne_zero]
    rw [FractionalIdeal.count_well_defined K v (FractionalIdeal.spanSingleton_ne_zero_iff.2 a.ne_zero) hI]
    change _ = -Multiplicative.toAdd (v.valuationOfNeZeroToFun a)
    simp only [HeightOneSpectrum.valuationOfNeZeroToFun, toAdd_ofAdd]
    ring
  refine ⟨h1, h2, fun a => ?_⟩
  have hf := FractionalIdeal.finite_factors
    (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (a : K))
  rw [Filter.eventually_cofinite] at hf
  exact hf.subset fun v hv h0 => hv (by rw [← h2 v a]; exact h0)

/-- **Kummer Exact Sequence Cardinality Identity**:
`Nat.card (SelK S n ⧸ powK) = Nat.card (sUnitSubgroup S ⧸ powK) * Nat.card {c : ClS S // c ^ n = 1}`. -/
theorem card_selK_quot_pow_eq (K : Type) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ) (hn : n ≠ 0) :
    Nat.card (SelK S n ⧸ (powK K n).subgroupOf (SelK S n)) =
      Nat.card (sUnitSubgroup S ⧸ (powK K n).subgroupOf (sUnitSubgroup S)) *
        Nat.card {c : ClS S // c ^ n = 1} := by
  classical
  obtain ⟨hcl1, hcl2, hcl_fin⟩ := clProd_facts K
  have hfinSupp : ∀ a : Kˣ, Function.HasFiniteMulSupport (fun v => primeCl v ^ (ordv v a / (n : ℤ))) :=
    fun a => (hcl_fin a).subset fun v hv h => hv (by simp [h])
  have hmk_prime : ∀ {v : HeightOneSpectrum (𝓞 K)}, v ∈ S →
      (QuotientGroup.mk (primeCl v) : ClS S) = 1 :=
    fun hv => (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_closure ⟨_, hv, rfl⟩)
  have hmk_radCl : ∀ a : Kˣ, (QuotientGroup.mk (radCl n a) : ClS S) =
      ∏ᶠ v, (QuotientGroup.mk (primeCl v) : ClS S) ^ (ordv v a / (n : ℤ)) := fun a => by
    simpa [radCl] using (QuotientGroup.mk' (clSub S)).map_finprod (hfinSupp a)
  have hmk_finprod_congr : ∀ (f g : HeightOneSpectrum (𝓞 K) → ℤ),
      {v | f v ≠ 0}.Finite → {v | g v ≠ 0}.Finite → (∀ v ∉ S, f v = g v) →
      (QuotientGroup.mk (∏ᶠ v, primeCl v ^ f v) : ClS S) =
        QuotientGroup.mk (∏ᶠ v, primeCl v ^ g v) := by
    intro f g hf hg hfg
    have hfm : ∀ h : HeightOneSpectrum (𝓞 K) → ℤ, {v | h v ≠ 0}.Finite →
        Function.HasFiniteMulSupport (fun v => primeCl v ^ h v) :=
      fun h hh => hh.subset fun v hv h0 => hv (by simp [h0])
    have e1 := (QuotientGroup.mk' (clSub S)).map_finprod (hfm f hf)
    have e2 := (QuotientGroup.mk' (clSub S)).map_finprod (hfm g hg)
    simp only [QuotientGroup.mk'_apply] at e1 e2
    rw [e1, e2]
    refine finprod_congr fun v => ?_
    by_cases hv : v ∈ S
    · change (QuotientGroup.mk' (clSub S)) (primeCl v ^ f v) = (QuotientGroup.mk' (clSub S)) (primeCl v ^ g v)
      rw [map_zpow, map_zpow]
      change (QuotientGroup.mk (primeCl v) : ClS S) ^ f v = (QuotientGroup.mk (primeCl v) : ClS S) ^ g v
      rw [hmk_prime hv, one_zpow, one_zpow]
    · rw [hfg v hv]
  have hmul : ∀ a ∈ SelK S n, ∀ b ∈ SelK S n,
      (QuotientGroup.mk (radCl n (a * b)) : ClS S) =
        QuotientGroup.mk (radCl n a) * QuotientGroup.mk (radCl n b) := by
    intro a ha b hb
    rw [hmk_radCl, hmk_radCl, hmk_radCl, ← finprod_mul_distrib]
    · refine finprod_congr fun v => ?_
      by_cases hv : v ∈ S
      · simp [hmk_prime hv]
      · rw [ordv_mul, Int.add_ediv_of_dvd_left (ha v hv), zpow_add]
    · exact (hfinSupp a).subset fun v hv h => hv (by
        dsimp only at h ⊢; rw [← QuotientGroup.mk_zpow, h, QuotientGroup.mk_one])
    · exact (hfinSupp b).subset fun v hv h => hv (by
        dsimp only at h ⊢; rw [← QuotientGroup.mk_zpow, h, QuotientGroup.mk_one])
  have hpow : ∀ a ∈ SelK S n, (QuotientGroup.mk (radCl n a) : ClS S) ^ n = 1 := by
    intro a ha
    have h1 : (QuotientGroup.mk (radCl n a) : ClS S) ^ n =
        QuotientGroup.mk (∏ᶠ v, primeCl v ^ (n * (ordv v a / (n : ℤ)))) := by
      rw [← QuotientGroup.mk_pow]
      congr 1
      unfold radCl
      rw [finprod_pow (hfinSupp a)]
      exact finprod_congr fun v => by rw [← zpow_natCast, ← zpow_mul, mul_comm]
    have h2 : (QuotientGroup.mk (∏ᶠ v, primeCl v ^ (n * (ordv v a / (n : ℤ)))) : ClS S) =
        QuotientGroup.mk (∏ᶠ v, primeCl v ^ ordv v a) := by
      refine hmk_finprod_congr _ _ ((hcl_fin a).subset fun v hv h0 => hv (by simp [h0]))
        (hcl_fin a) fun v hv => Int.mul_ediv_cancel' (ha v hv)
    have h3 : (∏ᶠ v, primeCl v ^ ordv v a) = 1 := by
      have hprinc : ClassGroup.mk K (Units.mk0
          (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (a : K))
          (FractionalIdeal.spanSingleton_ne_zero_iff.2 a.ne_zero)) = 1 :=
        ClassGroup.mk_eq_one_iff.2 ((FractionalIdeal.isPrincipal_iff _).2 ⟨(a : K), rfl⟩)
      rw [hcl1] at hprinc
      simpa [hcl2] using hprinc
    rw [h1, h2, h3, QuotientGroup.mk_one]
  let f : SelK S n →* ClS S :=
    MonoidHom.mk' (fun a => (QuotientGroup.mk (radCl n a.1) : ClS S)) fun a b => hmul a.1 a.2 b.1 b.2
  have hU : sUnitSubgroup S ≤ SelK S n := fun a ha v hv => by
    rw [mem_sUnit_iff_ordv.mp ha v hv]; exact dvd_zero _
  have hP : powK K n ≤ SelK S n := by
    rintro _ ⟨b, rfl⟩ v _; simp
  -- Exactness: `ker f = (sUnitSubgroup S ⊔ powK K n).subgroupOf (SelK S n)`
  have hmem_clSub : ∀ {c : ClassGroup (𝓞 K)}, c ∈ clSub S →
      ∃ g : HeightOneSpectrum (𝓞 K) → ℤ, {v | g v ≠ 0}.Finite ∧ (∀ v ∉ S, g v = 0) ∧
        c = ∏ᶠ v, primeCl v ^ g v := by
    intro c hc
    induction hc using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      refine ⟨fun v => if v = w then 1 else 0, (Set.finite_singleton w).subset fun v hv => ?_,
        fun v hv => if_neg fun (h : v = w) => hv (h ▸ hw), ?_⟩
      · by_contra h; exact hv (if_neg h)
      · rw [finprod_eq_single _ w fun v hv => by simp [hv]]; simp
    | one => exact ⟨fun _ => 0, by simp, by simp, by simp⟩
    | mul x y _ _ hx hy =>
      obtain ⟨f₁, hf₁, hf₁', rfl⟩ := hx
      obtain ⟨f₂, hf₂, hf₂', rfl⟩ := hy
      refine ⟨fun v => f₁ v + f₂ v, (hf₁.union hf₂).subset fun v hv => ?_,
        fun v hv => by simp [hf₁' v hv, hf₂' v hv], ?_⟩
      · by_contra h; simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
        exact hv (by dsimp only; rw [h.1, h.2, add_zero])
      · rw [← finprod_mul_distrib (hf₁.subset fun v hv h => hv (by simp [h]))
            (hf₂.subset fun v hv h => hv (by simp [h]))]
        exact finprod_congr fun v => (zpow_add _ _ _).symm
    | inv x _ hx =>
      obtain ⟨f₁, hf₁, hf₁', rfl⟩ := hx
      refine ⟨fun v => -f₁ v, by simpa using hf₁, fun v hv => by simp [hf₁' v hv], ?_⟩
      rw [← finprod_inv_distrib]
      exact finprod_congr fun v => (zpow_neg _ _).symm
  have hf_ker : f.ker = (sUnitSubgroup S ⊔ powK K n).subgroupOf (SelK S n) := by
    ext ⟨a, ha⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change (QuotientGroup.mk (radCl n a) : ClS S) = 1 ↔ a ∈ sUnitSubgroup S ⊔ powK K n
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro hmem
      obtain ⟨g, hg, hg', hc⟩ := hmem_clSub (inv_mem hmem)
      have hfa : {v | ordv v a / (n : ℤ) ≠ 0}.Finite :=
        (hcl_fin a).subset fun v hv h => hv (by simp [h])
      let hfn : HeightOneSpectrum (𝓞 K) → ℤ := fun v => ordv v a / (n : ℤ) + g v
      have hhfin : {v | hfn v ≠ 0}.Finite :=
        (hfa.union hg).subset fun v hv => by
          by_contra h; simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
          exact hv (by simp [hfn, h.1, h.2])
      have hprod1 : ∏ᶠ v, primeCl v ^ hfn v = 1 := by
        have hsplit : ∏ᶠ v, primeCl v ^ hfn v =
            (∏ᶠ v, primeCl v ^ (ordv v a / (n : ℤ))) * (∏ᶠ v, primeCl v ^ g v) := by
          rw [← finprod_mul_distrib (hfa.subset fun v hv h => hv (by simp [h]))
            (hg.subset fun v hv h => hv (by simp [h]))]
          exact finprod_congr fun v => zpow_add _ _ _
        rw [hsplit, ← hc]
        exact mul_inv_cancel _
      -- Build fractional ideal `I = ∏_v v^{hfn v}` which is principal!
      let I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
        ∏ᶠ v : HeightOneSpectrum (𝓞 K), (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ hfn v
      have hI0 : I ≠ 0 := by
        refine finprod_ne_zero (fun v => zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 v.ne_bot))
      have hcountI : ∀ v, FractionalIdeal.count K v I = hfn v := fun v =>
        FractionalIdeal.count_finprod K v hfn (by simpa [Filter.eventually_cofinite] using hhfin)
      have hI_cl : ClassGroup.mk K (Units.mk0 I hI0) = 1 := by
        rw [hcl1, ← hprod1]
        exact finprod_congr fun v => by rw [Units.val_mk0, hcountI]
      obtain ⟨b, hb⟩ := (FractionalIdeal.isPrincipal_iff _).1 (ClassGroup.mk_eq_one_iff.1 hI_cl)
      rw [Units.val_mk0] at hb
      have hb0 : b ≠ 0 := fun h0 => hI0 (by rw [hb, h0, FractionalIdeal.spanSingleton_zero])
      let bu : Kˣ := Units.mk0 b hb0
      have hord_b : ∀ v, ordv v bu = hfn v := fun v => by
        rw [← hcl2 v bu]; show FractionalIdeal.count K v (FractionalIdeal.spanSingleton _ b) = _
        rw [← hb, hcountI]
      refine Subgroup.mem_sup.2 ⟨a * (bu ^ n)⁻¹, mem_sUnit_iff_ordv.2 fun v hv => ?_,
        bu ^ n, ⟨bu, rfl⟩, by simp⟩
      rw [ordv_mul, ordv_inv, ordv_pow, hord_b, show hfn v = ordv v a / (n : ℤ) + 0 by simp [hfn, hg' v hv],
        add_zero, Int.mul_ediv_cancel' (ha v hv), add_neg_cancel]
    · intro hsup
      obtain ⟨u, hu, _, ⟨b, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 hsup
      rw [powMonoidHom_apply]
      have hrad : radCl n (u * b ^ n) =
          (∏ᶠ v, primeCl v ^ (ordv v u / (n : ℤ))) * (∏ᶠ v, primeCl v ^ ordv v b) := by
        unfold radCl
        rw [← finprod_mul_distrib ((hcl_fin u).subset fun v hv h => hv (by simp [h]))
          ((hcl_fin b).subset fun v hv h => hv (by simp [h]))]
        refine finprod_congr fun v => ?_
        rw [ordv_mul, ordv_pow, Int.add_mul_ediv_left _ _ (by exact_mod_cast hn), zpow_add]
      have hprinc : (∏ᶠ v, primeCl v ^ ordv v b) = 1 := by
        have h0 : ClassGroup.mk K (Units.mk0
            (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (b : K))
            (FractionalIdeal.spanSingleton_ne_zero_iff.2 b.ne_zero)) = 1 :=
          ClassGroup.mk_eq_one_iff.2 ((FractionalIdeal.isPrincipal_iff _).2 ⟨(b : K), rfl⟩)
        rw [hcl1] at h0; simpa [hcl2] using h0
      rw [hrad, hprinc, mul_one]
      refine finprod_induction (fun c => c ∈ clSub S) (one_mem _) (fun _ _ => mul_mem) fun v => ?_
      by_cases hv : v ∈ S
      · have hmem : primeCl v ∈ clSub S := Subgroup.subset_closure ⟨v, hv, rfl⟩
        exact zpow_mem hmem _
      · rw [mem_sUnit_iff_ordv.mp hu v hv]; simp
  -- Range of `f` is `{c : ClS S // c ^ n = 1}`
  have hrange : ∀ c : ClS S, c ^ n = 1 → ∃ a : SelK S n, f a = c := by
    intro c hc
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    obtain ⟨I, rfl⟩ : ∃ I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ, ClassGroup.mk K I = x :=
      ClassGroup.induction K (fun I => ⟨I, rfl⟩) x
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hc
    obtain ⟨g, hg, hg', hJ_eq⟩ := hmem_clSub hc
    -- Build fractional ideal `J` supported in `S` with `ClassGroup.mk K J = (ClassGroup.mk K I)^n`
    let J0 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ g v
    have hJ0_ne : J0 ≠ 0 :=
      finprod_ne_zero fun v => zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 v.ne_bot)
    let J : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ := Units.mk0 J0 hJ0_ne
    have hJcount : ∀ v, FractionalIdeal.count K v J.1 = g v := fun v =>
      FractionalIdeal.count_finprod K v g (by simpa [Filter.eventually_cofinite] using hg)
    have hJcl : ClassGroup.mk K J = (ClassGroup.mk K I) ^ n := by
      rw [hcl1, hJ_eq]
      exact finprod_congr fun v => by rw [hJcount]
    have hP_cl : ClassGroup.mk K (I ^ n * J⁻¹) = 1 := by
      rw [map_mul, map_pow, map_inv, hJcl, mul_inv_cancel]
    obtain ⟨y, hy⟩ := (FractionalIdeal.isPrincipal_iff _).1 (ClassGroup.mk_eq_one_iff.1 hP_cl)
    have hy0 : y ≠ 0 := fun h0 => (I ^ n * J⁻¹).ne_zero (by rw [hy, h0, FractionalIdeal.spanSingleton_zero])
    let a : Kˣ := Units.mk0 y hy0
    have hcount_a : ∀ v ∉ S, ordv v a = n * FractionalIdeal.count K v I.1 := fun v hv => by
      rw [← hcl2 v a]
      show FractionalIdeal.count K v (FractionalIdeal.spanSingleton _ y) = _
      rw [← hy, Units.val_mul, FractionalIdeal.count_mul K v (Units.ne_zero _) (Units.ne_zero _),
        Units.val_pow_eq_pow_val, FractionalIdeal.count_pow, Units.val_inv_eq_inv_val,
        FractionalIdeal.count_inv, hJcount v, hg' v hv, neg_zero, add_zero]
    have ha_mem : a ∈ SelK S n := fun v hv => ⟨FractionalIdeal.count K v I.1, hcount_a v hv⟩
    refine ⟨⟨a, ha_mem⟩, ?_⟩
    change (QuotientGroup.mk (radCl n a) : ClS S) = QuotientGroup.mk (ClassGroup.mk K I)
    rw [hcl1]
    refine hmk_finprod_congr _ _ ((hcl_fin a).subset fun v hv h0 => hv (by simp [h0])) ?_ fun v hv => ?_
    · have hf := FractionalIdeal.finite_factors I.1
      rwa [Filter.eventually_cofinite] at hf
    · rw [hcount_a v hv, Int.mul_ediv_cancel_left _ (by exact_mod_cast hn)]
  -- Group-index identity `|A / P| = |U / P| * |range f|`
  have hQ : sUnitSubgroup S ⊔ powK K n ≤ SelK S n := sup_le hU hP
  have hPQ : (powK K n).subgroupOf (SelK S n) ≤ (sUnitSubgroup S ⊔ powK K n).subgroupOf (SelK S n) :=
    fun x hx => (le_sup_right : powK K n ≤ sUnitSubgroup S ⊔ powK K n) hx
  have hcard_eq : Nat.card (SelK S n ⧸ (powK K n).subgroupOf (SelK S n)) =
      Nat.card (sUnitSubgroup S ⧸ (powK K n).subgroupOf (sUnitSubgroup S)) * Nat.card f.range := by
    change ((powK K n).subgroupOf (SelK S n)).index = ((powK K n).subgroupOf (sUnitSubgroup S)).index * _
    rw [← Subgroup.relIndex_mul_index hPQ, Subgroup.relIndex_subgroupOf hQ,
      Subgroup.relIndex_sup_right, ← hf_ker]
    congr 1
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  rw [hcard_eq]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ⟨?_, fun hc => ?_⟩)
  · rintro ⟨a, rfl⟩; exact hpow a.1 a.2
  · exact hrange c hc

/-- **Kummer `S_l`-Selmer Quotient Cardinality Bound (`0` parameters!)**:
`Finite (SelK (Above K l) l ⧸ powK)` and `Nat.card (SelK (Above K l) l ⧸ powK) ≤ l ^ (2 * [K : ℚ]) * classNumber K`. -/
theorem card_selK_above_quot_pow_le (K : Type) [Field K] [NumberField K] (l : ℕ) [hl : Fact l.Prime] :
    Finite (SelK (Above K l) l ⧸ (powK K l).subgroupOf (SelK (Above K l) l)) ∧
    Nat.card (SelK (Above K l) l ⧸ (powK K l).subgroupOf (SelK (Above K l) l)) ≤
      l ^ (2 * Module.finrank ℚ K) * classNumber K := by
  haveI : Finite (Above K l) := (above_finite (F := K) l).to_subtype
  obtain ⟨hfinU, hcardU⟩ := card_sUnit_quot_pow_le K (Above K l) l
  have hcard_eq := card_selK_quot_pow_eq K (Above K l) l hl.out.ne_zero
  have hcl_le : Nat.card {c : ClS (Above K l) // c ^ l = 1} ≤ classNumber K := by
    haveI : Finite (ClS (Above K l)) := Quotient.finite _
    calc Nat.card {c : ClS (Above K l) // c ^ l = 1}
        ≤ Nat.card (ClS (Above K l)) := Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      _ ≤ Nat.card (ClassGroup (𝓞 K)) := Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective
      _ = classNumber K := by rw [classNumber, Nat.card_eq_fintype_card]
  have hrank_le : NumberField.Units.rank K + Nat.card (Above K l) + 1 ≤ 2 * Module.finrank ℚ K := by
    have hU : NumberField.Units.rank K + 1 ≤ Module.finrank ℚ K := by
      rw [NumberField.Units.rank]
      have hsig := InfinitePlace.card_add_two_mul_card_eq_rank K
      have hcard_inf : Fintype.card (InfinitePlace K) =
          InfinitePlace.nrRealPlaces K + InfinitePlace.nrComplexPlaces K :=
        InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
      have hpos : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos
      omega
    have hA := card_above_le_finrank K l
    omega
  have hposU : 0 < Nat.card (sUnitSubgroup (Above K l) ⧸ (powK K l).subgroupOf (sUnitSubgroup (Above K l))) :=
    Nat.card_pos
  have hposC : 0 < Nat.card {c : ClS (Above K l) // c ^ l = 1} := by
    haveI : Finite (ClS (Above K l)) := Quotient.finite _
    haveI : Nonempty {c : ClS (Above K l) // c ^ l = 1} := ⟨⟨1, one_pow l⟩⟩
    exact Nat.card_pos
  refine ⟨Nat.finite_of_card_ne_zero (by rw [hcard_eq]; exact (Nat.mul_pos hposU hposC).ne'), ?_⟩
  rw [hcard_eq]
  exact Nat.mul_le_mul (hcardU.trans (Nat.pow_le_pow_right hl.out.pos hrank_le)) hcl_le

end KummerSUnitAndSelmerCardBounds

/-! ## Section 3: Hilbert 90, Kummer Unramified Injection & Unconditional `h1_l_torsion_rank_bound` (`0` Parameters!) -/

section Hilbert90AndH1LTorsionRankBound

/-- Continuous `ZMod l`-homomorphisms from `G K Ω` unramified outside `Above K l`. -/
def UnrHom (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (l : ℕ) :
    Set (G K Ω → ZMod l) :=
  {φ | IsLocallyConstant φ ∧ (∀ a b, φ (a * b) = φ a + φ b) ∧
    ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := K) A, φ g = 0}

/-- **Continuous Hilbert Theorem 90 (`0` parameters!)** via Dedekind's linear independence of characters. -/
theorem hilbert90_continuous (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (f : G K Ω → Ω) (hlc : IsLocallyConstant f) (h0 : ∀ g, f g ≠ 0)
    (hc : ∀ g h, f (g * h) = f g * g (f h)) :
    ∃ β : Ω, β ≠ 0 ∧ ∀ g : G K Ω, g β = f g * β := by
  classical
  have h1 : f 1 = 1 := by
    have h := hc 1 1
    rw [mul_one, AlgEquiv.one_apply] at h
    exact (mul_eq_left₀ (h0 1)).1 h.symm
  have hU : f ⁻¹' {1} ∈ nhds (1 : G K Ω) := (hlc {1}).mem_nhds h1
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff K Ω _).1 hU
  have hH : ∀ (g h : G K Ω), h ∈ L.fixingSubgroup → f (g * h) = f g := fun g h hh => by
    have : f h = 1 := hLU hh
    rw [hc, this, map_one, mul_one]
  have hopen : IsOpen (L.fixingSubgroup : Set (G K Ω)) := L.fixingSubgroup_isOpen
  haveI : Finite (G K Ω ⧸ L.fixingSubgroup) := Subgroup.quotient_finite_of_isOpen _ hopen
  letI : Fintype (G K Ω ⧸ L.fixingSubgroup) := Fintype.ofFinite _
  let χ : (G K Ω ⧸ L.fixingSubgroup) → (L →* Ω) := fun q =>
    ((q.out : G K Ω) : Ω →* Ω).comp (L.val : L →* Ω)
  have hχ : ∀ q (x : L), χ q x = (q.out : G K Ω) (x : Ω) := fun _ _ => rfl
  have hinj : Function.Injective χ := by
    intro p q hpq
    rw [← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' q, QuotientGroup.eq,
      IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have h := DFunLike.congr_fun hpq ⟨x, hx⟩
    rw [hχ, hχ] at h
    rw [AlgEquiv.mul_apply]
    change p.out.symm (q.out x) = x
    rw [AlgEquiv.symm_apply_eq]
    exact h.symm
  have hli := (linearIndependent_monoidHom L Ω).comp χ hinj
  have hex : ∃ x : L, ∑ q, f q.out * χ q x ≠ 0 := by
    by_contra hne
    push Not at hne
    have := Fintype.linearIndependent_iff.1 hli (fun q => f q.out) (by
      ext x; simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hne x)
    exact h0 (QuotientGroup.mk (1 : G K Ω)).out (this (QuotientGroup.mk 1))
  obtain ⟨x, hx⟩ := hex
  let α : Ω := ∑ q : G K Ω ⧸ L.fixingSubgroup, f q.out * (q.out : G K Ω) (x : Ω)
  have hα0 : α ≠ 0 := hx
  have hterm : ∀ (g : G K Ω) (q : G K Ω ⧸ L.fixingSubgroup),
      f (g * q.out) * (g * q.out) (x : Ω) =
        f ((g • q).out) * ((g • q).out : G K Ω) (x : Ω) := fun g q => by
    have hmem : ((g • q).out)⁻¹ * (g * q.out) ∈ L.fixingSubgroup := by
      rw [← QuotientGroup.eq]
      change QuotientGroup.mk (g • q).out = QuotientGroup.mk (g * q.out)
      rw [QuotientGroup.out_eq']
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have heq : g * q.out = (g • q).out * (((g • q).out)⁻¹ * (g * q.out)) := by group
    rw [heq, hH _ _ hmem, AlgEquiv.mul_apply,
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hmem x.1 x.2]
  have hact_α : ∀ g : G K Ω, f g * g α = α := fun g => by
    calc f g * g α = f g * ∑ q : G K Ω ⧸ L.fixingSubgroup, g (f q.out * (q.out : G K Ω) (x : Ω)) := by
            rw [map_sum g]
      _ = ∑ q : G K Ω ⧸ L.fixingSubgroup, f g * (g (f q.out) * (g * q.out) (x : Ω)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun q _ => by rw [map_mul]; rfl
      _ = ∑ q : G K Ω ⧸ L.fixingSubgroup, f (g * q.out) * (g * q.out) (x : Ω) := by
            refine Finset.sum_congr rfl fun q _ => by rw [← mul_assoc, ← hc g q.out]
      _ = ∑ q : G K Ω ⧸ L.fixingSubgroup, f ((g • q).out) * ((g • q).out : G K Ω) (x : Ω) :=
            Finset.sum_congr rfl fun q _ => hterm g q
      _ = α := Equiv.sum_comp (MulAction.toPerm g)
            (fun q : G K Ω ⧸ L.fixingSubgroup => f q.out * (q.out : G K Ω) (x : Ω))
  refine ⟨α⁻¹, inv_ne_zero hα0, fun g => ?_⟩
  have hga : g α = (f g)⁻¹ * α := by
    apply mul_left_cancel₀ (h0 g)
    rw [hact_α g, ← mul_assoc, mul_inv_cancel₀ (h0 g), one_mul]
  rw [map_inv₀, hga, mul_inv, inv_inv]

/-- **Kummer Radical Existence (`0` parameters!)**: from any locally constant 1-cocycle
`z : G K Ω → ZMod n` twisted by the cyclotomic character `η`, produces `β ∈ Ω` and `a ∈ Kˣ`
with `β^n = a` and `g β = ζ^(z g) * β`. -/
theorem radExists (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (n : ℕ) [NeZero n] (ζ : Ω) (η z : G K Ω → ZMod n) (hζ : IsPrimitiveRoot ζ n)
    (hη : ∀ g : G K Ω, g ζ = ζ ^ (η g).val) (hz : IsLocallyConstant z)
    (hc : ∀ g h, z (g * h) = z g + η g * z h) :
    ∃ (β : Ω) (a : Kˣ), β ^ n = algebraMap K Ω a ∧ ∀ g : G K Ω, g β = ζ ^ (z g).val * β := by
  have hmod : ∀ m : ℕ, ζ ^ (m % n) = ζ ^ m := fun m => (pow_eq_pow_mod m hζ.pow_eq_one).symm
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne n)
  obtain ⟨β, hβ0, hβ⟩ := hilbert90_continuous K Ω (fun g => ζ ^ (z g).val)
    (hz.comp fun x : ZMod n => ζ ^ x.val) (fun g => pow_ne_zero _ hζ0) (fun g h => by
      show ζ ^ (z (g * h)).val = ζ ^ (z g).val * g (ζ ^ (z h).val)
      rw [hc, ZMod.val_add, hmod, pow_add, ZMod.val_mul, hmod, map_pow, hη, ← pow_mul])
  haveI : IsGalois K Ω := {}
  have hfix : ∀ g : Ω ≃ₐ[K] Ω, g (β ^ n) = β ^ n := fun g => by
    rw [map_pow, hβ g, mul_pow, ← pow_mul, mul_comm _ n, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (β ^ n)).2 hfix
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact pow_ne_zero n hβ0 ha.symm
  exact ⟨β, Units.mk0 a ha0, ha.symm, hβ⟩

/-- Lifting an inertia automorphism of a finite Galois subextension `L / K` to `Ine (F := K) A`. -/
private theorem lift_inertia_to_abs {K Ω : Type} [Field K] [NumberField K] [Field Ω]
    [Algebra K Ω] [IsAlgClosure K Ω] (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsGalois K L] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (hA : IsPlaceOver A v)
    (P : Ideal (𝓞 L))
    (hP_def : ∀ x : 𝓞 L, x ∈ P ↔ A.valuation (algebraMap L Ω (x : L)) < 1)
    (τ : L ≃ₐ[K] L) (hτ : τ ∈ P.inertia (L ≃ₐ[K] L)) :
    ∃ φ : G K Ω, AlgEquiv.restrictNormalHom L φ = τ ∧ φ ∈ Ine (F := K) A := by
  haveI : NumberField L := NumberField.of_module_finite K L
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsIntegral K Ω := Algebra.IsAlgebraic.isIntegral
  letI : TopologicalSpace (IntCl K Ω) := ⊥
  haveI : DiscreteTopology (IntCl K Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl K Ω
  haveI := isInvariant_intCl K Ω
  let Q : Ideal (IntCl K Ω) := primeBelow (F := K) A
  have hv : Q.under (𝓞 K) = v.asIdeal := under_primeBelow hA
  have hQmax : Q.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := 𝓞 K) Q (by
      show (Q.under (𝓞 K)).IsMaximal; rw [hv]; exact v.isMaximal)
  -- Define `Algebra (𝓞 L) (IntCl K Ω)` via `L ↪ Ω`
  let mapOL : 𝓞 L →+* IntCl K Ω :=
    { toFun := fun x => ⟨(x : L), (x.2.map (IsScalarTower.toAlgHom ℤ L Ω)).tower_top⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  letI : Algebra (𝓞 L) (IntCl K Ω) := mapOL.toAlgebra
  have hPQ : Q.under (𝓞 L) = P := by
    ext x
    rw [Ideal.mem_comap, mem_primeBelow, hP_def x]
    rfl
  haveI : Q.IsPrime := hQmax.isPrime
  haveI : P.IsPrime := hPQ ▸ Ideal.IsPrime.under (𝓞 L) Q
  have hPunder : P.under (𝓞 K) = v.asIdeal := by
    ext x
    rw [Ideal.mem_comap, hP_def]
    exact hA x
  have hPmax : P.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := 𝓞 K) P (by
      show (P.under (𝓞 K)).IsMaximal; rw [hPunder]; exact v.isMaximal)
  -- Setup `G_L = L.fixingSubgroup` acting on `IntCl K Ω` over `𝓞 L`
  let G_L := L.fixingSubgroup
  haveI : CompactSpace G_L := isCompact_iff_compactSpace.mp (InfiniteGalois.fixingSubgroup_isClosed L).isCompact
  haveI : ContinuousSMul G_L (IntCl K Ω) := continuousSMul_iff_stabilizer_isOpen.2 fun b => by
    have hopen : IsOpen (MulAction.stabilizer (G K Ω) b : Set (G K Ω)) := by
      let Kb : IntermediateField K Ω := IntermediateField.adjoin K {(b : Ω)}
      haveI : FiniteDimensional K Kb :=
        IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)
      exact Subgroup.isOpen_mono (H₁ := Kb.fixingSubgroup)
        (fun σ hσ => Subtype.ext ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _
          (IntermediateField.mem_adjoin_simple_self K _)))
        Kb.fixingSubgroup_isOpen
    exact hopen.preimage continuous_subtype_val
  haveI : Algebra.IsIntegral (𝓞 L) (IntCl K Ω) := ⟨fun b => by
    have h1 : IsIntegral ℤ b :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ (IntCl K Ω) Ω)
        Subtype.coe_injective).mp (isIntegral_trans (b : Ω) b.2)
    exact h1.tower_top⟩
  have hfix : ∀ (g : G_L) (a : 𝓞 L), g • algebraMap (𝓞 L) (IntCl K Ω) a = algebraMap (𝓞 L) (IntCl K Ω) a :=
    fun g a => Subtype.ext ((IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ (a : L).2)
  haveI : SMulCommClass G_L (𝓞 L) (IntCl K Ω) := ⟨fun g a b => by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hfix]⟩
  haveI : Algebra.IsInvariant (𝓞 L) (IntCl K Ω) G_L := ⟨fun b hb => by
    have hmem : (b : Ω) ∈ IntermediateField.fixedField G_L := by
      rw [IntermediateField.mem_fixedField_iff]
      intro f hf
      exact congrArg Subtype.val (hb ⟨f, hf⟩)
    rw [InfiniteGalois.fixedField_fixingSubgroup] at hmem
    have hint : IsIntegral ℤ (⟨b, hmem⟩ : L) :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ L Ω) (algebraMap L Ω).injective).1
        (isIntegral_trans (b : Ω) b.2)
    exact ⟨⟨⟨b, hmem⟩, hint⟩, Subtype.ext rfl⟩⟩
  -- Lift `τ` to `g : G K Ω`
  obtain ⟨g, hg⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) (E := Ω) τ
  have hgL : ∀ x : 𝓞 L, g • algebraMap (𝓞 L) (IntCl K Ω) x =
      algebraMap (𝓞 L) (IntCl K Ω) (τ • x) := fun x => Subtype.ext (by
    rw [← hg]; exact (AlgEquiv.restrictNormal_commutes g L x).symm)
  have hunder : Q.under (𝓞 L) = (g⁻¹ • Q).under (𝓞 L) := by
    ext x
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_inv_pointwise_smul_iff, hgL]
    have hτx : τ • x - x ∈ P := hτ x
    change x ∈ Q.under (𝓞 L) ↔ τ • x ∈ Q.under (𝓞 L)
    rw [hPQ]
    constructor
    · intro hx
      have h1 : τ • x = (τ • x - x) + x := by ring
      rw [h1]; exact P.add_mem hτx hx
    · intro hx
      have h1 : x = τ • x - (τ • x - x) := by ring
      rw [h1]; exact P.sub_mem hx hτx
  obtain ⟨h, hh⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := 𝓞 L) (G := G_L)
    Q (g⁻¹ • Q) hunder
  set g' : G K Ω := g * h with hg'
  have hst : g' • Q = Q := by
    rw [hg', mul_smul]
    exact (congrArg (g • ·) (show (h : G K Ω) • Q = g⁻¹ • Q from hh.symm)).trans (smul_inv_smul g Q)
  have hmemQ : ∀ b : IntCl K Ω, g'⁻¹ • b ∈ Q ↔ b ∈ Q := fun b => by
    rw [← Ideal.mem_pointwise_smul_iff_inv_smul_mem, hst]
  have hmemQ' : ∀ b : IntCl K Ω, g' • b ∈ Q ↔ b ∈ Q := fun b => by
    have h1 := hmemQ (g' • b); rw [inv_smul_smul] at h1; exact h1.symm
  let u : IntCl K Ω ⧸ Q →+* IntCl K Ω ⧸ Q :=
    Ideal.quotientMap Q (MulSemiringAction.toRingHom _ _ g'⁻¹) fun b hb => (hmemQ b).2 hb
  let uInv : IntCl K Ω ⧸ Q →+* IntCl K Ω ⧸ Q :=
    Ideal.quotientMap Q (MulSemiringAction.toRingHom _ _ g') fun b hb => (hmemQ' b).2 hb
  have hu : ∀ b : IntCl K Ω, u (Ideal.Quotient.mk Q b) = Ideal.Quotient.mk Q (g'⁻¹ • b) := fun _ => rfl
  have huInv : ∀ b : IntCl K Ω, uInv (Ideal.Quotient.mk Q b) = Ideal.Quotient.mk Q (g' • b) := fun _ => rfl
  have hg'L : ∀ x : 𝓞 L, g'⁻¹ • algebraMap (𝓞 L) (IntCl K Ω) (τ • x) =
      algebraMap (𝓞 L) (IntCl K Ω) x := fun x => by
    rw [inv_smul_eq_iff, hg', mul_smul, ← hgL]
    exact congrArg (g • ·) (hfix h x).symm
  haveI : Q.LiesOver P := ⟨hPQ.symm⟩
  let ψ : (IntCl K Ω ⧸ Q) ≃ₐ[𝓞 L ⧸ P] (IntCl K Ω ⧸ Q) :=
    { toFun := u
      invFun := uInv
      left_inv := fun c => by
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
        rw [hu, huInv, smul_inv_smul]
      right_inv := fun c => by
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
        rw [huInv, hu, inv_smul_smul]
      map_mul' := u.map_mul
      map_add' := u.map_add
      commutes' := fun c => by
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
        obtain ⟨y, rfl⟩ : ∃ y, τ • y = x := ⟨τ⁻¹ • x, smul_inv_smul τ x⟩
        have hτy : Ideal.Quotient.mk Q (algebraMap (𝓞 L) (IntCl K Ω) (τ • y)) =
            Ideal.Quotient.mk Q (algebraMap (𝓞 L) (IntCl K Ω) y) := by
          rw [Ideal.Quotient.eq, ← map_sub]
          have : τ • y - y ∈ Q.under (𝓞 L) := hPQ.symm ▸ hτ y
          exact this
        show u (Ideal.Quotient.mk Q (algebraMap (𝓞 L) (IntCl K Ω) (τ • y))) =
          Ideal.Quotient.mk Q (algebraMap (𝓞 L) (IntCl K Ω) (τ • y))
        rw [hu, hg'L, hτy] }
  obtain ⟨k, hk⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := G_L) P Q ψ
  set φ : G K Ω := (k : G K Ω) * g'
  have hφ_res : AlgEquiv.restrictNormalHom L φ = τ := by
    have hker : ∀ s : G_L, AlgEquiv.restrictNormalHom L (s : G K Ω) = 1 := fun s => by
      rw [← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker]; exact s.2
    rw [show φ = (k : G K Ω) * (g * (h : G K Ω)) from rfl, map_mul, map_mul, hker, hker, hg,
      one_mul, mul_one]
  have hφQ : ∀ b : IntCl K Ω, φ • b - b ∈ Q := fun b => by
    have e := DFunLike.congr_fun hk (Ideal.Quotient.mk Q (g' • b))
    have e' : Ideal.Quotient.mk Q (φ • b) = Ideal.Quotient.mk Q b := by
      rw [show φ • b = (k : G K Ω) • (g' • b) from mul_smul _ _ _]
      refine (show Ideal.Quotient.mk Q ((k : G K Ω) • (g' • b)) = ψ (Ideal.Quotient.mk Q (g' • b)) from e).trans ?_
      show u (Ideal.Quotient.mk Q (g' • b)) = Ideal.Quotient.mk Q b
      rw [hu, inv_smul_smul]
    exact Ideal.Quotient.eq.mp e'
  have hφ_dec : φ ∈ Dec (F := K) A := by
    rw [mem_Dec]
    refine eq_of_valuation_lt_one_iff K fun b hb => ?_
    let b' : IntCl K Ω := ⟨b, hb.tower_top⟩
    have hlt_iff : (φ • A).valuation b < 1 ↔ φ⁻¹ • b' ∈ Q := by
      rw [smul_valuation_lt_one_iff]; rfl
    rw [hlt_iff]
    change φ⁻¹ • b' ∈ Q ↔ b' ∈ Q
    have hdiff := hφQ (φ⁻¹ • b')
    rw [smul_inv_smul] at hdiff
    constructor
    · intro h1; have : b' = (b' - φ⁻¹ • b') + φ⁻¹ • b' := by ring
      rw [this]; exact Q.add_mem hdiff h1
    · intro h1; have : φ⁻¹ • b' = b' - (b' - φ⁻¹ • b') := by ring
      rw [this]; exact Q.sub_mem h1 hdiff
  refine ⟨φ, hφ_res, hφ_dec, fun x hx => ?_⟩
  obtain ⟨s, t, hs, ht, hs1, hst_eq⟩ := exists_den K A hx
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs1
  have hs_phi : A.valuation (φ s) = 1 := by
    have h1 := valuation_apply_lt_one_iff hφ_dec s
    have hle := (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A (hs.map (φ.restrictScalars ℤ)))
    refine le_antisymm hle ?_
    rw [← not_lt, h1, hs1]; exact lt_irrefl 1
  have hdiff_eq : φ s * (φ x - x) = (φ t - t) - (φ s - s) * x := by
    rw [mul_sub, ← map_mul, hst_eq]
    linear_combination -hst_eq
  have hval_lt : A.valuation ((φ t - t) - (φ s - s) * x) < 1 := by
    have ht_lt : A.valuation (φ t - t) < 1 := hφQ ⟨t, ht.tower_top⟩
    have hs_lt : A.valuation (φ s - s) < 1 := hφQ ⟨s, hs.tower_top⟩
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ht_lt ?_)
    rw [Valuation.map_mul]
    calc A.valuation (φ s - s) * A.valuation x ≤ A.valuation (φ s - s) * 1 :=
          mul_le_mul_of_nonneg_left hx zero_le
      _ < 1 := by rwa [mul_one]
  rw [← hdiff_eq, Valuation.map_mul, hs_phi, one_mul] at hval_lt
  exact hval_lt

/-- At an unramified prime `w ∣ v` (`e(w / v) = 1`), the `w`-adic valuation restricts to `v` on `K`. -/
private theorem valuation_liesOver_of_ramificationIdx_one {K M : Type} [Field K] [NumberField K]
    [Field M] [NumberField M] [Algebra K M] (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 M)) [w.asIdeal.LiesOver v.asIdeal]
    (hram : w.asIdeal.ramificationIdx (𝓞 K) = 1) (x : K) :
    w.valuation M (algebraMap K M x) = v.valuation K x := by
  let f : 𝓞 K →+* 𝓞 M := algebraMap (𝓞 K) (𝓞 M)
  have hf_inj : Function.Injective f := FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 M)
  have hmap_ne : ∀ {I : Ideal (𝓞 K)}, I ≠ ⊥ → Ideal.map f I ≠ ⊥ := fun {I} hI hbot => by
    obtain ⟨r, hrI, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    have hmem : f r ∈ Ideal.map f I := Ideal.mem_map_of_mem f hrI
    rw [hbot, Ideal.mem_bot] at hmem
    exact hr0 (hf_inj (hmem.trans (map_zero f).symm))
  have hw_prime : Prime w.asIdeal := Ideal.prime_of_isPrime w.ne_bot w.isPrime
  have hv_prime : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
  have hmult_v : emultiplicity w.asIdeal (Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal) = 1 := by
    have hne : Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal ≠ ⊥ := hmap_ne v.ne_bot
    have hfin : FiniteMultiplicity w.asIdeal (Ideal.map (algebraMap (𝓞 K) (𝓞 M)) v.asIdeal) :=
      FiniteMultiplicity.of_prime_left hw_prime hne
    rw [hfin.emultiplicity_eq_multiplicity,
      ← Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity v.asIdeal w.asIdeal hne, hram]
    rfl
  have hmult_ne : ∀ {p : Ideal (𝓞 K)}, Prime p → p ≠ v.asIdeal →
      emultiplicity w.asIdeal (Ideal.map f p) = 0 := fun {p} hp hne => by
    refine emultiplicity_eq_zero.mpr fun hdvd => hne ?_
    have hle : Ideal.map f p ≤ w.asIdeal := Ideal.le_of_dvd hdvd
    have hle' : p ≤ v.asIdeal := by
      have h1 : p ≤ w.asIdeal.comap f := Ideal.map_le_iff_le_comap.mp hle
      rwa [show w.asIdeal.comap f = v.asIdeal from (Ideal.LiesOver.over (p := v.asIdeal) (P := w.asIdeal)).symm] at h1
    have hp_max : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    exact hp_max.eq_of_le v.isPrime.ne_top hle'
  have hmult_eq : ∀ I : Ideal (𝓞 K), I ≠ ⊥ →
      emultiplicity w.asIdeal (Ideal.map f I) = emultiplicity v.asIdeal I := fun I hI => by
    induction I using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => exact absurd rfl hI
    | h₂ u hu =>
      rw [Ideal.isUnit_iff.mp hu, Ideal.map_top,
        emultiplicity_eq_zero.mpr (fun hd => w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (Ideal.le_of_dvd hd (by simp)) isUnit_one)),
        emultiplicity_eq_zero.mpr (fun hd => v.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (Ideal.le_of_dvd hd (by simp)) isUnit_one))]
    | h₃ a p ha hp ih =>
      rw [Ideal.map_mul, emultiplicity_mul hw_prime, emultiplicity_mul hv_prime, ih ha]
      by_cases hpv : p = v.asIdeal
      · subst hpv
        have hself : emultiplicity v.asIdeal v.asIdeal = 1 := by
          apply le_antisymm
          · by_contra hgt
            have h2 : ((2 : ℕ) : ℕ∞) ≤ emultiplicity v.asIdeal v.asIdeal := by
              cases h : emultiplicity v.asIdeal v.asIdeal with
              | top => exact le_top
              | coe n =>
                rw [h] at hgt
                have hn : 2 ≤ n := by
                  have hlt : (1 : ℕ∞) < (n : ℕ∞) := not_le.mp hgt
                  have hlt' : 1 < n := by exact_mod_cast hlt
                  omega
                exact_mod_cast hn
            obtain ⟨c, hc⟩ := pow_dvd_iff_le_emultiplicity.mpr h2
            have h1 : v.asIdeal * 1 = v.asIdeal * (v.asIdeal * c) := by
              rw [mul_one, ← mul_assoc, ← pow_two]; exact hc
            exact v.isPrime.ne_top (Ideal.isUnit_iff.mp
              (isUnit_iff_exists_inv.mpr ⟨c, (mul_left_cancel₀ v.ne_bot h1).symm⟩))
          · exact pow_dvd_iff_le_emultiplicity.mp (by rw [pow_one])
        rw [hmult_v, hself]
      · have hzero : emultiplicity v.asIdeal p = 0 :=
          emultiplicity_eq_zero.mpr fun hd =>
            hpv (((Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero).eq_of_le v.isPrime.ne_top (Ideal.le_of_dvd hd))
        rw [hmult_ne hp hpv, hzero]
  have hint_eq : ∀ r : 𝓞 K, w.intValuation (f r) = v.intValuation r := fun r => by
    by_cases hr : r = 0
    · subst hr; simp
    · have hfr : f r ≠ 0 := fun h => hr (hf_inj (h.trans (map_zero f).symm))
      have ha0 : w.intValuation (f r) ≠ 0 := HeightOneSpectrum.intValuation_ne_zero w (f r) hfr
      have hb0 : v.intValuation r ≠ 0 := HeightOneSpectrum.intValuation_ne_zero v r hr
      have ha1 : w.intValuation (f r) ≤ 1 := HeightOneSpectrum.intValuation_le_one w (f r)
      have hb1 : v.intValuation r ≤ 1 := HeightOneSpectrum.intValuation_le_one v r
      have hcut : ∀ m : ℕ, w.intValuation (f r) ≤ WithZero.exp (-(m : ℤ)) ↔
          v.intValuation r ≤ WithZero.exp (-(m : ℤ)) := fun m => by
        rw [HeightOneSpectrum.intValuation_le_pow_iff_dvd, HeightOneSpectrum.intValuation_le_pow_iff_dvd,
          show Ideal.span {f r} = Ideal.map f (Ideal.span {r}) by rw [Ideal.map_span, Set.image_singleton],
          pow_dvd_iff_le_emultiplicity, pow_dvd_iff_le_emultiplicity,
          hmult_eq _ (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hr)]
      have hkey : ∀ {a b : WithZero (Multiplicative ℤ)}, a ≠ 0 → a ≤ 1 →
          (∀ m : ℕ, a ≤ WithZero.exp (-(m : ℤ)) → b ≤ WithZero.exp (-(m : ℤ))) → b ≤ a := fun {a b} h0 h1 hc => by
        have hlog : WithZero.log a ≤ 0 := by
          rw [← WithZero.exp_le_exp, WithZero.exp_log h0, WithZero.exp_zero]; exact h1
        have hm : ((-WithZero.log a).toNat : ℤ) = -WithZero.log a := Int.toNat_of_nonneg (by omega)
        have h2 := hc (-WithZero.log a).toNat (by rw [hm, neg_neg, WithZero.exp_log h0])
        rwa [hm, neg_neg, WithZero.exp_log h0] at h2
      exact le_antisymm (hkey hb0 hb1 fun m => (hcut m).2) (hkey ha0 ha1 fun m => (hcut m).1)
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have h1 : algebraMap K M (algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s) =
      algebraMap (𝓞 M) M (f r) / algebraMap (𝓞 M) M (f s) := by
    rw [map_div₀]
    rfl
  rw [h1, map_div₀, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, hint_eq r, hint_eq s]

/-- **Inertia Divisibility for Kummer Radicals (`dvdOfIne`, `0` parameters!)**:
If `β^n = a` (`a ∈ Kˣ`) and `Ine A` fixes `β` at a place `A` over `v`, then `n ∣ ord_v(a)`. -/
theorem dvdOfIne (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (n : ℕ) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (β : Ω) (a : Kˣ)
    (hA : IsPlaceOver A v) (hβ : β ^ n = algebraMap K Ω a)
    (hI : ∀ g ∈ Ine (F := K) A, g β = β) : (n : ℤ) ∣ ordv v a := by
  haveI : IsGalois K Ω := IsAlgClosure.isGalois K Ω
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  let L : IntermediateField K Ω := (FiniteGaloisIntermediateField.adjoin K ({β} : Set Ω)).toIntermediateField
  have hβL : β ∈ L := FiniteGaloisIntermediateField.subset_adjoin K _ rfl
  haveI : FiniteDimensional K L := inferInstance
  haveI : IsGalois K L := inferInstance
  haveI : NumberField L := NumberField.of_module_finite K L
  let mapOL : 𝓞 L →+* IntCl K Ω :=
    { toFun := fun x => ⟨(x : L), (x.2.map (IsScalarTower.toAlgHom ℤ L Ω)).tower_top⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_zero' := Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  let P : Ideal (𝓞 L) := (primeBelow (F := K) A).comap mapOL
  have hP_def : ∀ x : 𝓞 L, x ∈ P ↔ A.valuation (algebraMap L Ω (x : L)) < 1 := fun _ => Iff.rfl
  have hPunder : P.under (𝓞 K) = v.asIdeal := by
    ext x; rw [Ideal.mem_comap, hP_def]; exact hA x
  haveI : P.IsPrime := Ideal.IsPrime.comap mapOL
  haveI : P.LiesOver v.asIdeal := ⟨hPunder.symm⟩
  -- Every inertia automorphism `τ ∈ P.inertia (L ≃ₐ[K] L)` fixes `⟨β, hβL⟩`
  have hfix : ∀ τ ∈ P.inertia (L ≃ₐ[K] L), τ ⟨β, hβL⟩ = ⟨β, hβL⟩ := fun τ hτ => by
    obtain ⟨φ, hφ_res, hφ_ine⟩ := lift_inertia_to_abs L A v hA P hP_def τ hτ
    rw [← hφ_res]
    exact Subtype.ext ((AlgEquiv.restrictNormal_commutes φ L ⟨β, hβL⟩).trans (hI φ hφ_ine))
  -- Pass to inertia fixed field `M = fixedField (P.inertia)` where `e(P_M / v) = 1`
  let M : IntermediateField K L := IntermediateField.fixedField (P.inertia (L ≃ₐ[K] L))
  haveI : NumberField M := NumberField.of_module_finite K M
  have hle : P.inertia (L ≃ₐ[K] L) ≤ M.fixingSubgroup := (IntermediateField.le_iff_le _ _).1 le_rfl
  have hβM : (⟨β, hβL⟩ : L) ∈ M := (IntermediateField.mem_fixedField_iff _ _).2 hfix
  let Q : Ideal (𝓞 M) := P.under (𝓞 M)
  haveI : Q.IsPrime := Ideal.IsPrime.under (𝓞 M) P
  haveI : Q.LiesOver v.asIdeal := ⟨by rw [Ideal.under_under]; exact Ideal.LiesOver.over⟩
  have hram1 : Q.ramificationIdx (𝓞 K) = 1 := by
    have hb := v.ne_bot
    have hPb : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hb P
    have hqb : Q ≠ ⊥ := Ideal.under_ne_bot _ hPb
    haveI : IsGaloisGroup M.fixingSubgroup M L :=
      .of_mulEquiv_algEquiv (IntermediateField.fixingSubgroupEquiv M) fun _ _ => rfl
    haveI : IsGaloisGroup M.fixingSubgroup (𝓞 M) (𝓞 L) :=
      IsGaloisGroup.of_isFractionRing _ _ _ M L
    haveI := v.isMaximal
    haveI : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hqb
    haveI : Finite (𝓞 K ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ hb
    haveI : Finite (𝓞 M ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot _ hqb
    haveI : P.LiesOver Q := ⟨rfl⟩
    have h1 := Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) v.asIdeal P
    have h2 := Ideal.card_inertia_eq_ramificationIdxIn (G := M.fixingSubgroup) Q P
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P (L ≃ₐ[K] L)] at h1
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ P M.fixingSubgroup] at h2
    have h3 := Ideal.ramificationIdx_tower (R := 𝓞 K) Q P
    have h4 : Nat.card (P.inertia M.fixingSubgroup) =
        Nat.card ↥(P.inertia (L ≃ₐ[K] L) ⊓ M.fixingSubgroup) := by
      rw [← AddSubgroup.inertia_map_subtype, Subgroup.card_subtype]
    rw [← h1, ← h2, h4] at h3
    have hpos : 0 < Nat.card ↥(P.inertia (L ≃ₐ[K] L) ⊓ M.fixingSubgroup) := Nat.card_pos
    rw [inf_eq_left.mpr hle] at h3 hpos
    exact Nat.eq_of_mul_eq_mul_right hpos (h3.symm.trans (one_mul _).symm)
  let w : HeightOneSpectrum (𝓞 M) := ⟨Q, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
  haveI : w.asIdeal.LiesOver v.asIdeal := (inferInstance : Q.LiesOver v.asIdeal)
  have hval : w.valuation M (algebraMap K M (a : K)) = v.valuation K (a : K) :=
    valuation_liesOver_of_ramificationIdx_one v w hram1 (a : K)
  have hβM_pow : (⟨⟨β, hβL⟩, hβM⟩ : M) ^ n = algebraMap K M (a : K) :=
    Subtype.ext (Subtype.ext hβ)
  rw [← hβM_pow, map_pow, ← HeightOneSpectrum.valuationOfNeZero_eq] at hval
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, ← WithZero.coe_one, WithZero.coe_inj] at hval
    simp [ordv, hval]
  · have h0 : w.valuation M ⟨⟨β, hβL⟩, hβM⟩ ≠ 0 := fun e => by
      rw [e, zero_pow hn.ne'] at hval
      exact WithZero.coe_ne_zero hval.symm
    obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.1 h0
    rw [← hm, ← WithZero.coe_pow, WithZero.coe_inj] at hval
    rw [ordv, ← hval, toAdd_pow, dvd_neg, nsmul_eq_mul]
    exact dvd_mul_right _ _

/-- **Kummer Unramified Injection (`unrSel`, `0` parameters!)**:
When `K` contains a primitive `l`-th root of unity, `UnrHom K Ω l` injects into `SelK (Above K l) l ⧸ powK K l`. -/
theorem unrSel (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (l : ℕ) [hl : Fact l.Prime] (hζK : ∃ ζ : K, IsPrimitiveRoot ζ l) :
    ∃ f : UnrHom K Ω l → SelK (Above K l) l ⧸ (powK K l).subgroupOf (SelK (Above K l) l),
      Function.Injective f := by
  obtain ⟨ζ₀, hζ₀⟩ := hζK
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  have hζ : IsPrimitiveRoot (algebraMap K Ω ζ₀) l := hζ₀.map_of_injective (algebraMap K Ω).injective
  have hgζ : ∀ g : G K Ω, g (algebraMap K Ω ζ₀) = algebraMap K Ω ζ₀ := fun g => g.commutes ζ₀
  have hdata : ∀ φ : UnrHom K Ω l, ∃ (β : Ω) (a : Kˣ), β ^ l = algebraMap K Ω a ∧
      ∀ g : G K Ω, g β = algebraMap K Ω ζ₀ ^ (φ.1 g).val * β := fun φ => by
    obtain ⟨hlc, hadd, -⟩ := φ.2
    exact radExists K Ω l (algebraMap K Ω ζ₀) (fun _ => 1) φ.1 hζ
      (fun g => by rw [hgζ, ZMod.val_one, pow_one]) hlc (fun g h => by rw [hadd, one_mul])
  choose β a hβa hgβ using hdata
  have hsel : ∀ φ, a φ ∈ SelK (Above K l) l := fun φ v hv => by
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
    refine dvdOfIne K Ω l A v (β φ) (a φ) hA (hβa φ) fun g hg => ?_
    have hnot : ¬ A.valuation (l : Ω) < 1 := fun hlt => hv (by
      have h1 : A.valuation (algebraMap K Ω ((((l : ℕ) : 𝓞 K) : K))) < 1 := by
        simpa using hlt
      exact (hA ((l : ℕ) : 𝓞 K)).mp h1)
    have h0 : φ.1 g = 0 := φ.2.2.2 A hnot g hg
    rw [hgβ, h0, ZMod.val_zero, pow_zero, one_mul]
  refine ⟨fun φ => QuotientGroup.mk ⟨a φ, hsel φ⟩, fun φ ψ hfe => ?_⟩
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hfe
  obtain ⟨c, hc⟩ := hfe
  have hc' : a ψ = a φ * c ^ l := by
    have h : c ^ l = (a φ)⁻¹ * a ψ := by simpa [powK] using hc
    rw [h, mul_inv_cancel_left]
  have hβne : ∀ φ, β φ ≠ 0 := fun φ h => by
    have h' := hβa φ
    rw [h, zero_pow (NeZero.ne l)] at h'
    exact (a φ).ne_zero ((map_eq_zero_iff _ (algebraMap K Ω).injective).mp h'.symm)
  have hcΩ : algebraMap K Ω (c : K) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K Ω).injective).mpr c.ne_zero
  apply Subtype.ext
  funext g
  have hγl : (β ψ / (β φ * algebraMap K Ω c)) ^ l = 1 := by
    rw [div_pow, mul_pow, hβa ψ, hβa φ, ← map_pow, ← map_mul, hc', Units.val_mul,
      Units.val_pow_eq_pow_val]
    exact div_self ((map_ne_zero_iff _ (algebraMap K Ω).injective).mpr
      (mul_ne_zero (a φ).ne_zero (pow_ne_zero _ c.ne_zero)))
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hγl
  have hgγ : g (β ψ / (β φ * algebraMap K Ω c)) = β ψ / (β φ * algebraMap K Ω c) := by
    rw [← hi, map_pow, hgζ]
  have hγ0 : β ψ / (β φ * algebraMap K Ω c) ≠ 0 := div_ne_zero (hβne ψ) (mul_ne_zero (hβne φ) hcΩ)
  have hgγ' : g (β ψ / (β φ * algebraMap K Ω c)) =
      algebraMap K Ω ζ₀ ^ (ψ.1 g).val / algebraMap K Ω ζ₀ ^ (φ.1 g).val *
        (β ψ / (β φ * algebraMap K Ω c)) := by
    rw [map_div₀, map_mul, hgβ, hgβ, AlgEquiv.commutes]
    ring
  rw [hgγ] at hgγ'
  have hratio : algebraMap K Ω ζ₀ ^ (ψ.1 g).val / algebraMap K Ω ζ₀ ^ (φ.1 g).val = 1 :=
    mul_right_cancel₀ hγ0 (by rw [one_mul]; exact hgγ'.symm)
  have hpow_eq : algebraMap K Ω ζ₀ ^ (ψ.1 g).val = algebraMap K Ω ζ₀ ^ (φ.1 g).val :=
    eq_of_div_eq_one hratio
  exact (ZMod.val_injective l (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hpow_eq)).symm

/-- Adjoining `l`-th roots of unity `E(ζ_l)` inside `Ω`. -/
def FnOne (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (l : ℕ) : IntermediateField E Ω :=
  IntermediateField.adjoin E ((Polynomial.X ^ l - 1 : Polynomial E).rootSet Ω)

/-- Basic cyclotomic properties of `FnOne E Ω l`: `[E(ζ_l) : E] ∣ l - 1`, primitive `l`-th root,
and cyclotomic embedding `E(ζ_l) ↪ CyclotomicField (l * N) ℚ`. -/
theorem fnOne_props (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [hl : Fact l.Prime] :
    IsCyclotomicExtension {l} E (FnOne E Ω l) ∧
    Module.finrank E (FnOne E Ω l) ∣ l - 1 ∧
    (∃ ζ : FnOne E Ω l, IsPrimitiveRoot ζ l) ∧
    (∀ N : ℕ, 0 < N → Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) →
      Nonempty (FnOne E Ω l →ₐ[ℚ] CyclotomicField (l * N) ℚ)) := by
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hroot : (Polynomial.X ^ l - 1 : Polynomial E).rootSet Ω =
      {b : Ω | ∃ m ∈ ({l} : Set ℕ), m ≠ 0 ∧ b ^ m = 1} := by
    have hp : (Polynomial.X ^ l - 1 : Polynomial E) ≠ 0 := by
      simpa using Polynomial.X_pow_sub_C_ne_zero hl.out.pos (1 : E)
    ext b; rw [Polynomial.mem_rootSet_of_ne hp]; simp [sub_eq_zero, hl.out.ne_zero]
  have hc : IsCyclotomicExtension {l} E (FnOne E Ω l) := by
    unfold FnOne; rw [hroot]
    refine IntermediateField.isCyclotomicExtension_adjoin_of_exists_isPrimitiveRoot
      (S := {l}) (K := E) (L := Ω) ?_
    intro m hm _; rw [Set.mem_singleton_iff] at hm; rw [hm]
    exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  haveI : IsCyclotomicExtension {l} E (FnOne E Ω l) := hc
  refine ⟨hc, ?_, ⟨_, IsCyclotomicExtension.zeta_spec l E (FnOne E Ω l)⟩, ?_⟩
  · haveI : FiniteDimensional E (FnOne E Ω l) := IsCyclotomicExtension.finiteDimensional {l} E _
    haveI : IsGalois E (FnOne E Ω l) := IsCyclotomicExtension.isGalois {l} E _
    rw [← IsGalois.card_aut_eq_finrank, ← Nat.totient_prime hl.out, ← ZMod.card_units_eq_totient,
      ← Nat.card_eq_fintype_card]
    exact Subgroup.card_dvd_of_injective _
      (IsPrimitiveRoot.autToPow_injective E (IsCyclotomicExtension.zeta_spec l E (FnOne E Ω l)))
  · intro N hN ⟨φ⟩
    haveI : NeZero N := ⟨hN.ne'⟩
    haveI : NeZero (l * N) := ⟨Nat.mul_ne_zero hl.out.ne_zero hN.ne'⟩
    haveI : NeZero ((l * N : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne (l * N))⟩
    haveI : NeZero ((N : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hN.ne'⟩
    letI : IsCyclotomicExtension {l * N} ℚ (CyclotomicField (l * N) ℚ) :=
      CyclotomicField.isCyclotomicExtension (l * N) ℚ
    letI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
      CyclotomicField.isCyclotomicExtension N ℚ
    obtain ⟨ζ, hζ⟩ : ∃ ζ : CyclotomicField (l * N) ℚ, IsPrimitiveRoot ζ (l * N) :=
      ⟨_, IsCyclotomicExtension.zeta_spec (l * N) ℚ (CyclotomicField (l * N) ℚ)⟩
    have hζN : IsPrimitiveRoot (ζ ^ l) N := hζ.pow (Nat.pos_of_ne_zero (NeZero.ne _)) rfl
    have hζl : IsPrimitiveRoot (ζ ^ N) l := hζ.pow (Nat.pos_of_ne_zero (NeZero.ne _)) (mul_comm l N)
    have hsN : Polynomial.IsSplittingField ℚ (CyclotomicField N ℚ) (Polynomial.X ^ N - 1) :=
      IsCyclotomicExtension.isSplittingField_X_pow_sub_one N ℚ _
    have hsl : Polynomial.IsSplittingField E (FnOne E Ω l) (Polynomial.X ^ l - 1) :=
      IsCyclotomicExtension.isSplittingField_X_pow_sub_one l E _
    have hsplitN : (Polynomial.map (algebraMap ℚ (CyclotomicField (l * N) ℚ))
        (Polynomial.X ^ N - 1)).Splits := by
      rw [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X]
      simpa [Polynomial.C_1] using Polynomial.X_pow_sub_one_splits hζN
    let ψ := Polynomial.IsSplittingField.lift (CyclotomicField N ℚ)
      (Polynomial.X ^ N - 1 : Polynomial ℚ) hsplitN
    letI : Algebra E (CyclotomicField (l * N) ℚ) := ((ψ.comp φ) : E →+* _).toAlgebra
    have hsplitl : (Polynomial.map (algebraMap E (CyclotomicField (l * N) ℚ))
        (Polynomial.X ^ l - 1)).Splits := by
      rw [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X]
      simpa [Polynomial.C_1] using Polynomial.X_pow_sub_one_splits hζl
    exact ⟨((Polynomial.IsSplittingField.lift (FnOne E Ω l) (Polynomial.X ^ l - 1 : Polynomial E)
      hsplitl : FnOne E Ω l →ₐ[E] _) : FnOne E Ω l →+* _).toRatAlgHom⟩

/-- `FnOne E Ω l = E(ζ_l)` is a number field whenever `E` is. -/
instance instNumberField_FnOne (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] : NumberField (FnOne E Ω l) := by
  haveI : IsCyclotomicExtension {l} E (FnOne E Ω l) := (fnOne_props E Ω l).1
  haveI : FiniteDimensional E (FnOne E Ω l) := IsCyclotomicExtension.finiteDimensional {l} E _
  exact NumberField.of_module_finite E (FnOne E Ω l)

/-- Embedding `ZMod l ↪ QZ l` identifying `ZMod l` with the `l`-torsion of `ℚ_l / ℤ_l`. -/
private theorem zmodToQZ_one (l : ℕ) [hl : Fact l.Prime] :
    ∃ ι : ZMod l →+ QZ l, Function.Injective ι ∧
      (∀ x : QZ l, x ∈ Set.range ι ↔ (l : ℤ_[l]) • x = 0) ∧
      ∀ (z : ℤ_[l]) (a : ZMod l), ι (PadicInt.toZMod z * a) = z • ι a := by
  have hl0 : ((l : ℚ_[l])) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  have zsm : ∀ (k : ℤ) (q : ℚ_[l]), k • (Submodule.Quotient.mk q : QZ l) =
      Submodule.Quotient.mk ((k : ℚ_[l]) * q) := fun k q => by
    rw [← Int.cast_smul_eq_zsmul ℤ_[l]]
    change (Submodule.Quotient.mk (((k : ℤ_[l]) : ℚ_[l]) * q) : QZ l) = _
    rw [PadicInt.coe_intCast]
  have hker : (l : ℤ) • (Submodule.Quotient.mk ((l : ℚ_[l])⁻¹) : QZ l) = 0 := by
    rw [zsm]
    refine (Submodule.Quotient.mk_eq_zero (ZlSub l)).2 ⟨1, ?_⟩
    push_cast; exact (mul_inv_cancel₀ hl0).symm
  let ι : ZMod l →+ QZ l :=
    ZMod.lift l ⟨zmultiplesHom (QZ l) (Submodule.Quotient.mk ((l : ℚ_[l])⁻¹) : QZ l), hker⟩
  have hι : ∀ k : ℤ, ι (k : ZMod l) = Submodule.Quotient.mk ((k : ℚ_[l]) * (l : ℚ_[l])⁻¹) := fun k => by
    simp only [ι, ZMod.lift_coe]; exact zsm k _
  have hkill : ∀ a : ZMod l, l • ι a = 0 := fun a => by
    rw [← map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, map_zero]
  have h3 : ∀ (z : ℤ_[l]) (a : ZMod l), ι (PadicInt.toZMod z * a) = z • ι a := fun z a => by
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec 1 z)
    have hzw : z = ((z.appr 1 : ℕ) : ℤ_[l]) + w * (l : ℤ_[l]) := by
      have hw1 : z - ((z.appr 1 : ℕ) : ℤ_[l]) = w * (l : ℤ_[l]) := by
        simpa [pow_one] using hw.symm
      linear_combination hw1
    have hz : PadicInt.toZMod z = ((z.appr 1 : ℕ) : ZMod l) := by
      conv_lhs => rw [hzw]
      rw [map_add, map_mul, map_natCast, map_natCast, ZMod.natCast_self, mul_zero, add_zero]
    rw [hz, ← nsmul_eq_mul, map_nsmul]
    conv_rhs => rw [hzw]
    rw [add_smul, Nat.cast_smul_eq_nsmul, mul_smul, Nat.cast_smul_eq_nsmul, hkill, smul_zero, add_zero]
  refine ⟨ι, ?_, ?_, h3⟩
  · rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective a
    rw [hι] at ha
    obtain ⟨y, hy⟩ := (Submodule.Quotient.mk_eq_zero (ZlSub l)).1 ha
    have hy' : (y : ℚ_[l]) = (k : ℚ_[l]) * (l : ℚ_[l])⁻¹ := hy
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hky : (k : ℤ_[l]) = y * (l : ℤ_[l]) := by
      apply Subtype.ext
      push_cast; rw [hy', mul_assoc, inv_mul_cancel₀ hl0, mul_one]
    have hmem : (k : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
      rw [hky, ← PadicInt.ker_toZMod, RingHom.mem_ker, map_mul, map_natCast, ZMod.natCast_self, mul_zero]
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_intCast] at hmem
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd k l).mp hmem
  · intro x
    constructor
    · rintro ⟨a, rfl⟩
      rw [Nat.cast_smul_eq_nsmul]; exact hkill a
    · intro hx
      obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) x
      change (l : ℤ_[l]) • (Submodule.Quotient.mk q : ℚ_[l] ⧸ ZlSub l) = 0 at hx
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨y, hy⟩ := hx
      have hy' : (y : ℚ_[l]) = (l : ℚ_[l]) * q := hy
      refine ⟨PadicInt.toZMod y, ?_⟩
      obtain ⟨k, hk⟩ := ZMod.intCast_surjective (PadicInt.toZMod y)
      rw [← hk, hι]
      change (Submodule.Quotient.mk ((k : ℚ_[l]) * (l : ℚ_[l])⁻¹) : ℚ_[l] ⧸ ZlSub l) =
        Submodule.Quotient.mk q
      rw [Submodule.Quotient.eq]
      have hdiff : ∃ w : ℤ_[l], (k : ℤ_[l]) - y = (l : ℤ_[l]) * w := by
        set d : ℤ_[l] := (k : ℤ_[l]) - y
        have hd0 : PadicInt.toZMod d = 0 := by
          simp only [d, map_sub, map_intCast, hk, sub_self]
        obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec 1 d)
        have hdu : d = ((d.appr 1 : ℕ) : ℤ_[l]) + u * (l : ℤ_[l]) := by
          have hu1 : d - ((d.appr 1 : ℕ) : ℤ_[l]) = u * (l : ℤ_[l]) := by simpa [pow_one] using hu.symm
          linear_combination hu1
        have happr0 : ((d.appr 1 : ℕ) : ZMod l) = 0 := by
          rw [← hd0]
          conv_rhs => rw [hdu]
          rw [map_add, map_mul, map_natCast, map_natCast, ZMod.natCast_self, mul_zero, add_zero]
        obtain ⟨c, hc⟩ := (ZMod.natCast_eq_zero_iff (d.appr 1) l).mp happr0
        refine ⟨(c : ℤ_[l]) + u, ?_⟩
        rw [hdu, hc, Nat.cast_mul]; ring
      obtain ⟨w, hw⟩ := hdiff
      refine ⟨w, ?_⟩
      show (w : ℚ_[l]) = (k : ℚ_[l]) * (l : ℚ_[l])⁻¹ - q
      have hq : q = (y : ℚ_[l]) * (l : ℚ_[l])⁻¹ := by
        rw [hy', mul_comm (l : ℚ_[l]) q, mul_assoc, mul_inv_cancel₀ hl0, mul_one]
      have hwQ : ((k : ℚ_[l]) - (y : ℚ_[l])) = (l : ℚ_[l]) * (w : ℚ_[l]) := by
        have := congrArg (fun z : ℤ_[l] => (z : ℚ_[l])) hw
        simpa using this
      rw [hq, ← sub_mul, hwQ, mul_comm (l : ℚ_[l]) (w : ℚ_[l]), mul_assoc, mul_inv_cancel₀ hl0, mul_one]

/-- Divisibility of `QZ l = ℚ_l / ℤ_l` by `(l : ℤ_[l])`. -/
private theorem qz_divisible_by_l (l : ℕ) [hl : Fact l.Prime] (m : QZ l) :
    ∃ m' : QZ l, (l : ℤ_[l]) • m' = m := by
  obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) m
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  refine ⟨Submodule.Quotient.mk ((l : ℚ_[l])⁻¹ * q), ?_⟩
  change (Submodule.Quotient.mk (((l : ℤ_[l]) : ℚ_[l]) * ((l : ℚ_[l])⁻¹ * q)) : QZ l) = _
  rw [PadicInt.coe_natCast, ← mul_assoc, mul_inv_cancel₀ hl0, one_mul]

/-- Every `l`-torsion class in `H¹(G_{E, S_l}, (ℚ_l / ℤ_l)(-e))` has an `l`-torsion cocycle representative. -/
private theorem torsRep (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (D : LData E Ω l) (e : ℤ)
    (x : H1 (qzTw D e)) (hx : (l : ℤ_[l]) • x = 0) :
    ∃ z : Z1 (qzTw D e), x = Submodule.Quotient.mk z ∧ ∀ g, (l : ℤ_[l]) • z.1 g = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨m, hm⟩ := (mem_B1 _ _).mp (Submodule.mem_comap.1 hx)
  obtain ⟨m', hm'⟩ := qz_divisible_by_l l m
  let cb : Z1 (qzTw D e) := ⟨fun g => qzTw D e g m' - m', by
    refine ⟨?_, fun g h => ?_⟩
    · have hcont := contAction_qzTw D e
      have h1 : Continuous (fun g => qzTw D e g m') :=
        hcont.comp (continuous_id.prodMk continuous_const)
      exact h1.sub continuous_const
    · simp only [map_mul, Module.End.mul_apply, map_sub]; abel⟩
  have hcb_mem : cb ∈ (B1 (qzTw D e)).comap (Z1 (qzTw D e)).subtype :=
    (mem_B1 _ _).mpr ⟨m', fun _ => rfl⟩
  refine ⟨z - cb, ?_, fun g => ?_⟩
  · rw [Submodule.Quotient.eq, sub_sub_cancel]; exact hcb_mem
  · have h1 : (l : ℤ_[l]) • cb.1 g = (l : ℤ_[l]) • z.1 g := by
      change (l : ℤ_[l]) • (qzTw D e g m' - m') = (l : ℤ_[l]) • z.1 g
      rw [smul_sub, ← map_smul, hm', ← hm g]
      rfl
    show (l : ℤ_[l]) • (z.1 g - cb.1 g) = 0
    rw [smul_sub, sub_eq_zero]; exact h1.symm

/-- Standard averaging lemma: a 1-cocycle vanishing on a finite-index subgroup whose index is a unit in `R` is a coboundary. -/
private theorem coboundary_of_vanishing_on_finite_index {R Q M : Type*} [CommRing R] [Group Q]
    [AddCommGroup M] [Module R M] (rho : Representation R Q M) (H : Subgroup Q) (f : Q → M)
    (hf : ∀ g h, f (g * h) = f g + rho g (f h)) (hH : ∀ u ∈ H, f u = 0)
    (hu : IsUnit (H.index : R)) (hn : H.index ≠ 0) :
    ∃ m : M, ∀ g : Q, f g = rho g m - m := by
  classical
  haveI : Fintype (Q ⧸ H) := Subgroup.fintypeOfIndexNeZero hn
  have hconst : ∀ a b : Q, (a : Q ⧸ H) = (b : Q ⧸ H) → f a = f b := fun a b hab => by
    have hmem : a⁻¹ * b ∈ H := QuotientGroup.eq.mp hab
    have h1 := hf a (a⁻¹ * b)
    rw [mul_inv_cancel_left, hH _ hmem, map_zero, add_zero] at h1
    exact h1.symm
  let F : Q ⧸ H → M := fun x => f x.out
  have hF : ∀ a : Q, F (a : Q ⧸ H) = f a := fun a => hconst _ _ (QuotientGroup.out_eq' _)
  have hstep : ∀ (g : Q) (x : Q ⧸ H), F (g • x) = f g + rho g (F x) := fun g x => by
    induction x using QuotientGroup.induction_on with
    | H a =>
      have h2 : g • (a : Q ⧸ H) = ((g * a : Q) : Q ⧸ H) := rfl
      rw [h2, hF, hF, hf]
  have hcard : Fintype.card (Q ⧸ H) = H.index := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  have hsum : ∀ g : Q, ∑ x, F x = (H.index : R) • f g + rho g (∑ x, F x) := fun g => by
    calc ∑ x, F x = ∑ x, F (g • x) := (Equiv.sum_comp (MulAction.toPerm g) F).symm
      _ = ∑ x : Q ⧸ H, (f g + rho g (F x)) := Finset.sum_congr rfl fun x _ => hstep g x
      _ = (H.index : R) • f g + rho g (∑ x, F x) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcard,
            Nat.cast_smul_eq_nsmul, map_sum]
  rcases hu with ⟨u, hu⟩
  refine ⟨-(((u⁻¹ : Rˣ) : R) • ∑ x, F x), fun g => ?_⟩
  have h1 := hsum g
  have h2 : (H.index : R) • f g = -(rho g (∑ x, F x) - ∑ x, F x) := by
    rw [neg_sub]; exact eq_sub_of_add_eq h1.symm
  have h3 := congrArg (fun y => ((u⁻¹ : Rˣ) : R) • y) h2
  rw [← hu, ← mul_smul, Units.inv_mul, one_smul] at h3
  rw [h3, map_neg, map_smul, smul_neg, smul_sub, neg_sub, sub_neg_eq_add, add_comm]
  abel

/-- **Injection of `H¹(G_{E, S_l}, (ℚ_l / ℤ_l)(-e))[l]` into `UnrHom (FnOne E Ω l) Ω l` (`0` parameters!)**. -/
theorem unrInj (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [hl : Fact l.Prime] (D : LData E Ω l) (e : ℤ) :
    ∃ f : Submodule.torsionBy ℤ_[l] (H1 (qzTw D e)) (l : ℤ_[l]) → UnrHom (FnOne E Ω l) Ω l,
      Function.Injective f := by
  classical
  obtain ⟨ι, hinj, hrange, hsmul⟩ := zmodToQZ_one l
  obtain ⟨hc, hdeg, ⟨ζ₁, hζ₁⟩, _⟩ := fnOne_props E Ω l
  haveI : IsCyclotomicExtension {l} E (FnOne E Ω l) := hc
  haveI : FiniteDimensional E (FnOne E Ω l) := IsCyclotomicExtension.finiteDimensional {l} E _
  haveI : NumberField (FnOne E Ω l) := NumberField.of_module_finite E _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : IsAlgClosure (FnOne E Ω l) Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := E) _⟩
  let K := FnOne E Ω l
  -- Canonical embedding `galEmb : G K Ω →* G E Ω`
  let galEmb : G K Ω →* G E Ω :=
    { toFun := fun σ =>
        { toRingEquiv := σ.toRingEquiv
          commutes' := fun x => σ.commutes (algebraMap E K x) }
      map_one' := AlgEquiv.ext fun _ => rfl
      map_mul' := fun _ _ => AlgEquiv.ext fun _ => rfl }
  have hgalEmb_cont : Continuous galEmb := by
    apply continuous_of_continuousAt_one galEmb
    intro s hs
    rw [map_one, krullTopology_mem_nhds_one_iff] at hs
    obtain ⟨L, hL, hLs⟩ := hs
    rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
    let LK : IntermediateField K Ω := IntermediateField.adjoin K (L : Set Ω)
    have hLK_fin : FiniteDimensional K LK := by
      haveI : FiniteDimensional E L := hL
      have hfin : (Set.range (Module.finBasis E L)).Finite := Set.finite_range _
      have hgen : LK = IntermediateField.adjoin K (Set.range (fun i => (Module.finBasis E L i : Ω))) := by
        apply le_antisymm
        · rw [IntermediateField.adjoin_le_iff]
          intro x hx
          have hx' : x = ∑ i, (Module.finBasis E L).repr ⟨x, hx⟩ i • (Module.finBasis E L i : Ω) := by
            have h1 := congrArg (fun y : L => (y : Ω)) ((Module.finBasis E L).sum_repr ⟨x, hx⟩).symm
            simpa only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] using h1
          rw [hx']
          refine IntermediateField.sum_mem _ fun i _ => ?_
          rw [Algebra.smul_def]
          exact IntermediateField.mul_mem _
            (IntermediateField.algebraMap_mem _ (algebraMap E K _))
            (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
        · rw [IntermediateField.adjoin_le_iff]
          rintro _ ⟨i, rfl⟩
          exact IntermediateField.subset_adjoin _ _ (Module.finBasis E L i).2
      rw [hgen]
      exact IntermediateField.finiteDimensional_adjoin fun x _ =>
        (Algebra.IsIntegral.isIntegral (R := E) x).tower_top
    refine ⟨LK, hLK_fin, fun σ hσ => hLs ?_⟩
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
    intro x hx
    exact hσ x (IntermediateField.subset_adjoin K (L : Set Ω) hx)
  -- Every `σ : G K Ω` fixes all `l`-th roots of unity, so `toZMod (cycZ E Ω l (galEmb σ)) = 1`!
  have hcyc_mod : ∀ σ : G K Ω, PadicInt.toZMod ((cycZ E Ω l (galEmb σ) : ℤ_[l]ˣ) : ℤ_[l]) = 1 := fun σ => by
    haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
    haveI : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hl.out.ne_zero⟩
    haveI : NeZero l := ⟨hl.out.ne_zero⟩
    have hζΩ : IsPrimitiveRoot (algebraMap K Ω ζ₁) l := hζ₁.map_of_injective (algebraMap K Ω).injective
    have hspec := cyclotomicCharacter.spec (L := Ω) l
      (MulSemiringAction.toRingAut (G E Ω) Ω (galEmb σ)) (algebraMap K Ω ζ₁) (by rw [pow_one]; exact hζΩ.pow_eq_one)
    have hfix : (galEmb σ) (algebraMap K Ω ζ₁) = algebraMap K Ω ζ₁ := σ.commutes ζ₁
    set z : ℤ_[l] := ((cycZ E Ω l (galEmb σ) : ℤ_[l]ˣ) : ℤ_[l])
    have h1 : (algebraMap K Ω ζ₁) ^ 1 = (algebraMap K Ω ζ₁) ^ (PadicInt.toZModPow 1 z).val := by
      conv_lhs => rw [pow_one, ← hfix]
      exact hspec
    have hlt : (PadicInt.toZModPow 1 z).val < l := by
      haveI : NeZero (l ^ 1) := ⟨pow_ne_zero 1 hl.out.ne_zero⟩
      simpa [pow_one] using ZMod.val_lt (PadicInt.toZModPow 1 z)
    have hval1 : (PadicInt.toZModPow 1 z).val = 1 :=
      (hζΩ.pow_inj hl.out.one_lt hlt h1).symm
    have heq1 : PadicInt.toZModPow 1 z = 1 := by
      haveI : NeZero (l ^ 1) := ⟨pow_ne_zero 1 hl.out.ne_zero⟩
      haveI : Fact (1 < l ^ 1) := ⟨by rw [pow_one]; exact hl.out.one_lt⟩
      apply ZMod.val_injective (l ^ 1)
      rw [hval1, ZMod.val_one]
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec 1 z)
    have hzw : z = ((z.appr 1 : ℕ) : ℤ_[l]) + w * (l : ℤ_[l]) := by
      have hw1 : z - ((z.appr 1 : ℕ) : ℤ_[l]) = w * (l : ℤ_[l]) := by simpa [pow_one] using hw.symm
      linear_combination hw1
    have happr : ((z.appr 1 : ℕ) : ZMod l) = 1 := by
      have h2 : ((z.appr 1 : ℕ) : ZMod (l ^ 1)) = 1 := heq1
      have h3 := congrArg (ZMod.ringEquivCongr (pow_one l)) h2
      simpa using h3
    conv_lhs => rw [hzw]
    rw [map_add, map_mul, map_natCast, map_natCast, ZMod.natCast_self, mul_zero, add_zero, happr]
  -- Key: every `l`-torsion cocycle `z` induces an element of `UnrHom K Ω l`
  have key : ∀ z : Z1 (qzTw D e), (∀ g, (l : ℤ_[l]) • z.1 g = 0) →
      ∃ φ : UnrHom K Ω l, ∀ σ : G K Ω,
        ι (φ.1 σ) = z.1 (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) (galEmb σ)) := by
    intro z hz
    let w : G K Ω → QZ l := fun σ => z.1 (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) (galEmb σ))
    have hwt : ∀ σ, w σ ∈ Set.range ι := fun σ => (hrange _).2 (hz _)
    let φ : G K Ω → ZMod l := fun σ => Function.invFun ι (w σ)
    have hφ : ∀ σ, ι (φ σ) = w σ := fun σ => Function.invFun_eq (hwt σ)
    have hsmul_triv : ∀ (σ : G K Ω) (x : QZ l), (l : ℤ_[l]) • x = 0 →
        qzTw D e (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) (galEmb σ)) x = x := fun σ x hx => by
      obtain ⟨a, rfl⟩ := (hrange x).2 hx
      have hchi : D.chi (toGS Ω _ (galEmb σ)) = cycZ E Ω l (galEmb σ) :=
        congrArg (fun f => f (galEmb σ)) D.hchi
      have hmod1 : PadicInt.toZMod ((((D.chi ^ (-e)) (toGS Ω _ (galEmb σ)) : ℤ_[l]ˣ) : ℤ_[l])) = 1 := by
        have h1 : ((D.chi ^ (-e)) (toGS Ω _ (galEmb σ))) = (cycZ E Ω l (galEmb σ)) ^ (-e) := by
          cases -e with
          | ofNat n => simp [hchi]
          | negSucc n => simp [hchi]
        rw [h1]
        have hu1 : Units.map (PadicInt.toZMod (p := l)).toMonoidHom (cycZ E Ω l (galEmb σ)) = 1 :=
          Units.ext (hcyc_mod σ)
        have hpow : Units.map (PadicInt.toZMod (p := l)).toMonoidHom ((cycZ E Ω l (galEmb σ)) ^ (-e)) = 1 := by
          rw [map_zpow, hu1, one_zpow]
        exact congrArg Units.val hpow
      change ((((D.chi ^ (-e)) (toGS Ω _ (galEmb σ)) : ℤ_[l]ˣ) : ℤ_[l])) • ι a = ι a
      rw [← hsmul, hmod1, one_mul]
    have hadd : ∀ a b : G K Ω, φ (a * b) = φ a + φ b := fun a b => by
      apply hinj
      rw [map_add, hφ, hφ, hφ]
      change z.1 (toGS Ω _ (galEmb (a * b))) = w a + w b
      rw [map_mul, map_mul, z.2.2, hsmul_triv a (w b) (hz _)]
    have hlc : IsLocallyConstant φ := by
      have hw_cont : Continuous w := z.2.1.comp ((continuous_toGS Ω _).comp hgalEmb_cont)
      rw [IsLocallyConstant.iff_isOpen_fiber]
      intro c
      have heq : φ ⁻¹' {c} = w ⁻¹' {ι c} := by
        ext σ; simp only [Set.mem_preimage, Set.mem_singleton_iff]
        exact ⟨fun h => by rw [← hφ σ, h], fun h => hinj ((hφ σ).trans h)⟩
      rw [heq]
      exact (isOpen_discrete {ι c}).preimage hw_cont
    have hunr : ∀ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := K) A, φ g = 0 := by
      intro A hAl g hg
      apply hinj
      rw [map_zero, hφ]
      let pE : Ideal (𝓞 E) := (primeBelow (F := E) A).under (𝓞 E)
      haveI := isPrime_primeBelow (F := E) A
      have hpE_prime : pE.IsPrime := Ideal.IsPrime.under (𝓞 E) (primeBelow (F := E) A)
      have hz1_zero : z.1 1 = 0 := by
        have hz1 := z.2.2 1 1
        simp only [mul_one, map_one, Module.End.one_apply] at hz1
        exact add_eq_left.mp hz1.symm
      by_cases hbot : pE = ⊥
      · -- If `pE = ⊥`, then `A = ⊤` on `Ω`, so `g ∈ Ine K A` forces `g = 1`.
        have hall : ∀ y : Ω, y ∈ A := fun y => by
          by_contra hny
          have hinv : y⁻¹ ∈ A := (A.mem_or_inv_mem y).resolve_left hny
          have hlt : A.valuation y⁻¹ < 1 := by
            rw [valuation_lt_one_iff']; exact ⟨hinv, Or.inr (by rwa [inv_inv])⟩
          have hy0 : y⁻¹ ≠ 0 := inv_ne_zero fun h0 => hny (h0 ▸ A.zero_mem)
          obtain ⟨s, t, hs, ht, hs1, hst⟩ := exists_den E A hlt.le
          have hs0 : s ≠ 0 := by rintro rfl; simp at hs1
          have ht0 : t ≠ 0 := fun h0 => mul_ne_zero hs0 hy0 (hst.trans h0)
          have ht_lt : A.valuation t < 1 := by rw [← hst, Valuation.map_mul, hs1, one_mul]; exact hlt
          have hcoeff0 : (minpoly ℤ t).coeff 0 ≠ 0 := by
            intro h0
            obtain ⟨q, hq⟩ := Polynomial.X_dvd_iff.mpr h0
            have hev := minpoly.aeval ℤ t
            rw [hq, map_mul, Polynomial.aeval_X, mul_eq_zero] at hev
            rcases hev with rfl | hq0
            · exact ht0 rfl
            · have hqne : q ≠ 0 := fun hqz => minpoly.ne_zero ht (by rw [hq, hqz, mul_zero])
              have hmon_q : q.Monic :=
                Polynomial.Monic.of_mul_monic_left Polynomial.monic_X (hq ▸ minpoly.monic ht)
              exact not_lt.mpr (minpoly.min ℤ t hmon_q hq0) (by
                rw [hq]
                exact Polynomial.degree_lt_degree (by rw [Polynomial.natDegree_X_mul hqne]; omega))
          have hc_mem : ((minpoly ℤ t).coeff 0 : 𝓞 E) ∈ pE := by
            change A.valuation (algebraMap E Ω (((minpoly ℤ t).coeff 0 : 𝓞 E) : E)) < 1
            have hev := minpoly.aeval ℤ t
            rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ'] at hev
            have hneg : algebraMap ℤ Ω ((minpoly ℤ t).coeff 0) =
                -(∑ i ∈ Finset.range (minpoly ℤ t).natDegree,
                  algebraMap ℤ Ω ((minpoly ℤ t).coeff (i + 1)) * t ^ (i + 1)) :=
              eq_neg_of_add_eq_zero_left (by simpa [Algebra.smul_def, pow_zero, mul_one, add_comm] using hev)
            rw [show algebraMap E Ω (((minpoly ℤ t).coeff 0 : 𝓞 E) : E) =
                  algebraMap ℤ Ω ((minpoly ℤ t).coeff 0) by simp, hneg, Valuation.map_neg]
            refine Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_
            rw [Valuation.map_mul, pow_succ', Valuation.map_mul]
            have h1 : A.valuation (algebraMap ℤ Ω ((minpoly ℤ t).coeff (i + 1))) ≤ 1 :=
              (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A isIntegral_algebraMap)
            have h2 : A.valuation (t ^ i) ≤ 1 := by
              rw [Valuation.map_pow]; exact pow_le_one' ht_lt.le i
            calc A.valuation (algebraMap ℤ Ω ((minpoly ℤ t).coeff (i + 1))) *
                  (A.valuation t * A.valuation (t ^ i))
                ≤ 1 * (A.valuation t * 1) := by gcongr
              _ < 1 := by simpa using ht_lt
          rw [hbot, Ideal.mem_bot] at hc_mem
          exact hcoeff0 (by have := congrArg (algebraMap (𝓞 E) E) hc_mem; simpa using this)
        have hg1 : g = 1 := by
          ext x
          have hdiff := hg.2 x ((A.valuation_le_one_iff x).mpr (hall x))
          have h1 := (valuation_lt_one_iff' A (g x - x)).mp hdiff
          rcases h1.2 with h0 | hni
          · exact sub_eq_zero.mp h0
          · exact absurd (hall _) hni
        show z.1 (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) (galEmb g)) = 0
        rw [hg1, map_one, map_one, hz1_zero]
      · let v : HeightOneSpectrum (𝓞 E) := ⟨pE, hpE_prime, hbot⟩
        have hAv : IsPlaceOver A v := fun x => Iff.rfl
        have hv_notS : v ∉ (D.S : Set (HeightOneSpectrum (𝓞 E))) := fun hvS => by
          have hvA : v ∈ Above E l := D.hS ▸ hvS
          exact hAl (by simpa using (hAv ((l : ℕ) : 𝓞 E)).mpr hvA)
        have hg_ineE : galEmb g ∈ Ine (F := E) A := ⟨hg.1, hg.2⟩
        have hNS : galEmb g ∈ NS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) :=
          ine_le_NS (D.S : Set (HeightOneSpectrum (𝓞 E))) hv_notS hAv hg_ineE
        have hgs1 : toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) (galEmb g) = 1 :=
          (QuotientGroup.eq_one_iff _).mpr hNS
        show z.1 (toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 E))) (galEmb g)) = 0
        rw [hgs1, hz1_zero]
    exact ⟨⟨φ, hlc, hadd, hunr⟩, hφ⟩
  -- Pick `l`-torsion cocycle representative for every `x ∈ H1[l]`
  have hzf : ∀ x : Submodule.torsionBy ℤ_[l] (H1 (qzTw D e)) (l : ℤ_[l]),
      ∃ z : Z1 (qzTw D e), x.1 = Submodule.Quotient.mk z ∧ ∀ g, (l : ℤ_[l]) • z.1 g = 0 :=
    fun x => torsRep E Ω l D e x.1 ((Submodule.mem_torsionBy_iff _ _).1 x.2)
  choose zf hzf using hzf
  choose φf hφf using fun x => key (zf x) (hzf x).2
  refine ⟨φf, fun x y hxy => ?_⟩
  have hv : ∀ σ : G K Ω, (zf x).1 (toGS Ω _ (galEmb σ)) = (zf y).1 (toGS Ω _ (galEmb σ)) := fun σ => by
    rw [← hφf x σ, ← hφf y σ, hxy]
  apply Subtype.ext
  rw [(hzf x).1, (hzf y).1, ← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
  -- Index `[G E Ω : K.fixingSubgroup] = [K : E] ∣ l - 1`, which is a unit in `ℤ_[l]`!
  have hidx_eq : K.fixingSubgroup.index = Module.finrank E K := by
    haveI : IsGalois E K := IsCyclotomicExtension.isGalois {l} E K
    let res : G E Ω →* (K ≃ₐ[E] K) := AlgEquiv.restrictNormalHom K
    have hsurj : Function.Surjective res := AlgEquiv.restrictNormalHom_surjective (F := E) (K₁ := K) (E := Ω)
    have hker : res.ker = K.fixingSubgroup := IntermediateField.restrictNormalHom_ker K
    rw [← hker, Subgroup.index_eq_card,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective res hsurj).toEquiv,
      IsGalois.card_aut_eq_finrank]
  have hidx_dvd : K.fixingSubgroup.index ∣ l - 1 := hidx_eq ▸ hdeg
  have hidx_ne : K.fixingSubgroup.index ≠ 0 := fun h0 => by
    rw [h0, zero_dvd_iff] at hidx_dvd; have := hl.out.two_le; omega
  have hidx_unit : IsUnit (K.fixingSubgroup.index : ℤ_[l]) := by
    apply isUnit_natCast_padicInt_of_not_dvd
    have hle := Nat.le_of_dvd (by have := hl.out.two_le; omega) hidx_dvd
    exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hidx_ne) (by have := hl.out.two_le; omega)
  have hvan : ∀ g ∈ K.fixingSubgroup, (zf x - zf y).1 (toGS Ω _ g) = 0 := fun g hg => by
    let σ : G K Ω :=
      { toRingEquiv := g.toRingEquiv
        commutes' := fun a => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg a.1 a.2 }
    have hσ : galEmb σ = g := AlgEquiv.ext fun _ => rfl
    rw [← hσ]
    show (zf x).1 (toGS Ω _ (galEmb σ)) - (zf y).1 (toGS Ω _ (galEmb σ)) = 0
    rw [hv σ, sub_self]
  obtain ⟨m, hm⟩ := coboundary_of_vanishing_on_finite_index ((qzTw D e).comp (toGS Ω _))
    K.fixingSubgroup (fun g => (zf x - zf y).1 (toGS Ω _ g))
    (fun g h => by rw [map_mul]; exact (zf x - zf y).2.2 _ _) hvan hidx_unit hidx_ne
  exact (mem_B1 _ _).mpr ⟨m, fun g => by
    obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective g
    exact hm σ⟩

/-- **HEADLINE `0`-PARAMETER `l`-TORSION RANK BOUND (`h1_l_torsion_rank_bound`, Alpöge's `UpperTheory.V.Odd.gen`)**:
For EVERY number field `E` embedding in `CyclotomicField N ℚ` (`0 < N`), EVERY algebraic closure `Ω`,
EVERY prime `l`, EVERY `D : LData E Ω l`, and EVERY twist `e : ℤ`:
`∃ g : ℕ, Module.length ℤ_[l] (Submodule.torsionBy ℤ_[l] (H1 (qzTw D e)) (l : ℤ_[l])) ≤ g ∧`
`  (g : ℝ) ≤ 8 * l * [E : ℚ] * Real.log (l * N)`! -/
theorem h1_l_torsion_rank_bound
    (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (N : ℕ) (hN : 0 < N) (hE : Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ))
    (l : ℕ) [hl : Fact l.Prime] (D : LData E Ω l) (e : ℤ) :
    ∃ g : ℕ,
      Module.length ℤ_[l] (Submodule.torsionBy ℤ_[l] (H1 (qzTw D e)) (l : ℤ_[l])) ≤ g ∧
      (g : ℝ) ≤ 8 * (l : ℝ) * (Module.finrank ℚ E : ℝ) * Real.log ((l : ℝ) * (N : ℝ)) := by
  have hl2 : 2 ≤ l := hl.out.two_le
  obtain ⟨hc, hdeg, hζ, hemb⟩ := fnOne_props E Ω l
  haveI : IsCyclotomicExtension {l} E (FnOne E Ω l) := hc
  haveI : FiniteDimensional E (FnOne E Ω l) := IsCyclotomicExtension.finiteDimensional {l} E _
  haveI : NumberField (FnOne E Ω l) := NumberField.of_module_finite E _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : IsAlgClosure (FnOne E Ω l) Ω := ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := E) _⟩
  obtain ⟨f, hf⟩ := unrInj E Ω l D e
  obtain ⟨f', hf'⟩ := unrSel (FnOne E Ω l) Ω l hζ
  obtain ⟨hfin, hcard⟩ := card_selK_above_quot_pow_le (FnOne E Ω l) l
  have hH := log_classNumber_le_of_cyclotomic (FnOne E Ω l) (l * N) (by nlinarith) (hemb N hN hE)
  haveI : Finite (Submodule.torsionBy ℤ_[l] (H1 (qzTw D e)) (l : ℤ_[l])) :=
    Finite.of_injective _ (hf'.comp hf)
  obtain ⟨k, hk, hc_card⟩ := len_and_card_of_finite_padicInt l
    (Submodule.torsionBy ℤ_[l] (H1 (qzTw D e)) (l : ℤ_[l]))
  have h1 := (Nat.card_le_card_of_injective _ (hf'.comp hf)).trans hcard
  rw [hc_card] at h1
  have hn : Module.finrank ℚ (FnOne E Ω l) ≤ l * Module.finrank ℚ E := by
    rw [← Module.finrank_mul_finrank ℚ E (FnOne E Ω l), mul_comm]
    exact Nat.mul_le_mul_right _ ((Nat.le_of_dvd (by omega) hdeg).trans (by omega))
  refine ⟨k, hk.le, ?_⟩
  have hh : (0 : ℝ) < classNumber (FnOne E Ω l) := by exact_mod_cast classNumber_pos _
  generalize Module.finrank ℚ (FnOne E Ω l) = m at *
  generalize classNumber (FnOne E Ω l) = h at *
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl2
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h2 : (l : ℝ) ^ k ≤ (l : ℝ) ^ (2 * m) * h := by exact_mod_cast h1
  have h3 := Real.log_le_log (by positivity) h2
  rw [Real.log_mul (by positivity) hh.ne', Real.log_pow, Real.log_pow] at h3
  push_cast at h3 hH
  have ha : Real.log 2 ≤ Real.log l := Real.log_le_log (by norm_num) hl'
  have hb : Real.log l ≤ Real.log ((l : ℝ) * N) := Real.log_le_log (by positivity) (by nlinarith)
  have h2' := Real.log_two_gt_d9
  have hn' : (m : ℝ) ≤ l * Module.finrank ℚ E := by exact_mod_cast hn
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have h4 := mul_le_mul_of_nonneg_left hb hm
  have h5 : (k : ℝ) * (5 / 8) ≤ k * Real.log l := mul_le_mul_of_nonneg_left (by linarith) hk0
  have h6 := mul_le_mul_of_nonneg_right hn' (show 0 ≤ Real.log ((l : ℝ) * N) by linarith)
  nlinarith

/-- **Unconditional (`0`-parameter) `l`-torsion rank bound on `Sha1Galois E l e`** for any
`E ↪ CyclotomicField N ℚ` (`0 < N`). -/
theorem sha1Galois_l_torsion_rank_bound
    (E : Type) [Field E] [NumberField E]
    (N : ℕ) (hN : 0 < N) (hE : Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ))
    (l : Nat.Primes) (e : ℤ) :
    ∃ g : ℕ,
      Module.length ℤ_[l.1] (Submodule.torsionBy ℤ_[l.1] (Sha1Galois E l e) (l.1 : ℤ_[l.1])) ≤ g ∧
      (g : ℝ) ≤ 8 * (l.1 : ℝ) * (Module.finrank ℚ E : ℝ) * Real.log ((l.1 : ℝ) * (N : ℝ)) := by
  haveI : Fact l.1.Prime := ⟨l.2⟩
  obtain ⟨g, hg, hgb⟩ := h1_l_torsion_rank_bound E (AlgebraicClosure E) N hN hE l.1
    (canonicalLData E l) e
  refine ⟨g, ?_, hgb⟩
  let incl : Submodule.torsionBy ℤ_[l.1] (Sha1Galois E l e) (l.1 : ℤ_[l.1]) →ₗ[ℤ_[l.1]]
      Submodule.torsionBy ℤ_[l.1] (H1 (qzTw (canonicalLData E l) e)) (l.1 : ℤ_[l.1]) :=
    { toFun := fun ⟨⟨x, _⟩, hx⟩ => ⟨x, by
        rw [Submodule.mem_torsionBy_iff] at hx ⊢
        exact congrArg Subtype.val hx⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective incl := fun ⟨⟨x, _⟩, _⟩ ⟨⟨y, _⟩, _⟩ h =>
    Subtype.ext (Subtype.ext (congrArg Subtype.val h : x = y))
  exact (length_mono_of_injective incl hinj).trans hg

/-- Every `IsChiField ψ e q d E` embeds unconditionally into `CyclotomicField (condF E) ℚ` (`0 < condF E`). -/
theorem cyclotomic_emb_condF_of_isChiField
    (ψ : PChar) (e q d : ℕ) (hq : 0 < q) (hd : 0 < d)
    (E : Type) [Field E] [NumberField E] (hE : IsChiField ψ e q d E) :
    0 < condF E ∧ Nonempty (E →ₐ[ℚ] CyclotomicField (condF E) ℚ) := by
  obtain ⟨M, hM_pos, _, _, hM_emb⟩ := exists_cyclotomic_emb_of_isChiField ψ e q d hq hd E hE
  exact Nat.sInf_mem (s := {N : ℕ | 0 < N ∧ Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ)}) ⟨M, hM_pos, hM_emb⟩

/-- **Unconditional (`0`-parameter) `l`-torsion rank bound for any `IsChiField ψ e q d E` with `N = condF E`**! -/
theorem h1_l_torsion_rank_bound_of_isChiField
    (ψ : PChar) (e_page q d : ℕ) (hq : 0 < q) (hd : 0 < d)
    (E : Type) [Field E] [NumberField E] (hE : IsChiField ψ e_page q d E)
    (l : Nat.Primes) (k : ℤ) :
    ∃ g : ℕ,
      Module.length ℤ_[l.1]
        (Submodule.torsionBy ℤ_[l.1] (H1 (qzTw (canonicalLData E l) k)) (l.1 : ℤ_[l.1])) ≤ g ∧
      (g : ℝ) ≤ 8 * (l.1 : ℝ) * (Module.finrank ℚ E : ℝ) * Real.log ((l.1 : ℝ) * (condF E : ℝ)) := by
  haveI : Fact l.1.Prime := ⟨l.2⟩
  obtain ⟨hN, hEmb⟩ := cyclotomic_emb_condF_of_isChiField ψ e_page q d hq hd E hE
  exact h1_l_torsion_rank_bound E (AlgebraicClosure E) (condF E) hN hEmb l.1 (canonicalLData E l) k

end Hilbert90AndH1LTorsionRankBound

/-! ## Section 4: Higher Stickelberger `bdX`/`bdxLog` (`C = 30`) & `StickBound` Bridge (`0` Parameters!) -/

section StickelbergerAnnihilationAlgebraAndBdxLog

/-- Higher Stickelberger denominator factor `denY M k = M * k * (k + 1)!`. -/
def denY (M k : ℕ) : ℕ := M * k * (k + 1).factorial

/-- Higher Stickelberger numerator size bound `sizeY M a k = 2 * a^k * M^k * k!`. -/
def sizeY (M a k : ℕ) : ℕ := 2 * a ^ k * M ^ k * k.factorial

/-- Combined higher Stickelberger Archimedean bound `bdX M a k = denY M k * sizeY M a k`. -/
def bdX (M a k : ℕ) : ℕ := denY M k * sizeY M a k

private theorem bdX_mul_le (M a k T : ℕ) (hT : 2 ≤ T) (hM : M ≤ T) (ha : a ≤ T ^ 3)
    (hk : k ≤ T) (hk2 : 2 ≤ k) :
    bdX M a k * M ≤ T ^ (10 * k) := by
  have hk1 : k + 1 ≤ T ^ 2 := by nlinarith
  have f1 : (k + 1).factorial ≤ (T ^ 2) ^ (k + 1) :=
    (Nat.factorial_le_pow _).trans (Nat.pow_le_pow_left hk1 _)
  have f2 : k.factorial ≤ T ^ k := (Nat.factorial_le_pow _).trans (Nat.pow_le_pow_left hk _)
  calc bdX M a k * M = M * k * (k + 1).factorial * (2 * a ^ k * M ^ k * k.factorial) * M := rfl
    _ ≤ T * T * (T ^ 2) ^ (k + 1) * (T * (T ^ 3) ^ k * T ^ k * T ^ k) * T := by gcongr
    _ = T ^ (7 * k + 6) := by ring
    _ ≤ T ^ (10 * k) := Nat.pow_le_pow_right (by omega) (by omega)

/-- **Unconditional Higher Stickelberger Archimedean Log Bound (`bdxLog`, `C = 30`, `0` parameters!)**:
For all `1 ≤ N`, `2 ≤ l`, `1 ≤ e`:
`Real.log (bdX (N * l) (2 * (N * l) + 1) (e + 1)) + Real.log (N * l) ≤ 30 * (e + 1) * Real.log (e * l * N)`. -/
theorem bdxLog (N l e : ℕ) (hN : 1 ≤ N) (hl : 2 ≤ l) (he : 1 ≤ e) :
    Real.log (bdX (N * l) (2 * (N * l) + 1) (e + 1)) + Real.log ((N : ℝ) * l) ≤
      30 * ((e : ℝ) + 1) * Real.log ((e : ℝ) * l * N) := by
  have h2 : e * 2 ≤ e * l := Nat.mul_le_mul_left e hl
  have h3 : e * l ≤ e * l * N := Nat.le_mul_of_pos_right _ hN
  have h4 : 1 * l * N ≤ e * l * N := by gcongr
  have h5 : N * l ≤ e * l * N := by nlinarith
  have hX2 : 2 ≤ e * l * N := by nlinarith
  have hT : 2 ≤ 3 * (e * l * N) := by omega
  have hM : N * l ≤ 3 * (e * l * N) := by omega
  have ha : 2 * (N * l) + 1 ≤ (3 * (e * l * N)) ^ 3 :=
    le_trans (by omega) (Nat.le_self_pow (by norm_num) _)
  have hk : e + 1 ≤ 3 * (e * l * N) := by nlinarith
  have key := bdX_mul_le (N * l) (2 * (N * l) + 1) (e + 1) (3 * (e * l * N)) hT hM ha hk (by omega)
  have hNl : 0 < N * l := by positivity
  have hb : 0 < bdX (N * l) (2 * (N * l) + 1) (e + 1) := by
    unfold bdX denY sizeY; positivity
  have hbpos : (0 : ℝ) < (bdX (N * l) (2 * (N * l) + 1) (e + 1) : ℝ) := by exact_mod_cast hb
  have hMpos : (0 : ℝ) < (N : ℝ) * l := by exact_mod_cast hNl
  rw [← Real.log_mul hbpos.ne' hMpos.ne']
  have hcast : (bdX (N * l) (2 * (N * l) + 1) (e + 1) : ℝ) * ((N : ℝ) * l)
      = ((bdX (N * l) (2 * (N * l) + 1) (e + 1) * (N * l) : ℕ) : ℝ) := by push_cast; ring
  rw [hcast]
  have hXr : (2 : ℝ) ≤ (e : ℝ) * l * N := by exact_mod_cast hX2
  have hlog2 : Real.log 2 ≤ Real.log ((e : ℝ) * l * N) := Real.log_le_log (by norm_num) hXr
  have hlog3 : Real.log 3 ≤ 2 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]; exact Real.log_le_log (by norm_num) (by norm_num)
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogT : Real.log (((3 * (e * l * N) : ℕ) : ℝ)) ≤ 3 * Real.log ((e : ℝ) * l * N) := by
    push_cast; rw [Real.log_mul (by norm_num) (by positivity)]; linarith
  have hpos : (0 : ℝ) < ((bdX (N * l) (2 * (N * l) + 1) (e + 1) * (N * l) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hb hNl
  calc Real.log ((bdX (N * l) (2 * (N * l) + 1) (e + 1) * (N * l) : ℕ) : ℝ)
      ≤ Real.log (((3 * (e * l * N)) ^ (10 * (e + 1)) : ℕ) : ℝ) :=
        Real.log_le_log hpos (by exact_mod_cast key)
    _ = (10 * (e + 1) : ℕ) * Real.log (((3 * (e * l * N) : ℕ) : ℝ)) := by
        rw [Nat.cast_pow, Real.log_pow]
    _ ≤ (10 * (e + 1) : ℕ) * (3 * Real.log ((e : ℝ) * l * N)) :=
        mul_le_mul_of_nonneg_left hlogT (by positivity)
    _ = 30 * ((e : ℝ) + 1) * Real.log ((e : ℝ) * l * N) := by push_cast; ring

/-- The concrete minus-parity `Sha` submodule whose `ℤ_[l]`-length IS `minusParitySelmerSystem.minusLen E l k`. -/
def ShaMinusReal (E : Type) [Field E] [NumberField E] (l : Nat.Primes) (k : ℕ) :
    Submodule ℤ_[l.1] (H1 (qzTw (canonicalLData E l) (k : ℤ))) := by
  classical
  let chooseInv : CMGaloisInvolution E (AlgebraicClosure E) :=
    if h : ∃ I : CMGaloisInvolution E (AlgebraicClosure E), I.c ≠ 1
    then Classical.choose h
    else CMGaloisInvolution.trivial E (AlgebraicClosure E)
  exact Sha1Galois E l (k : ℤ) ⊓
    (conjH1 chooseInv (canonicalLData E l) (k : ℤ)).eigenspace ((-1 : ℤ_[l.1]) ^ (k + 1))

theorem length_shaMinusReal_eq_minusLen (E : Type) [Field E] [NumberField E]
    (l : Nat.Primes) (k : ℕ) :
    Module.length ℤ_[l.1] ↥(ShaMinusReal E l k) = minusParitySelmerSystem.minusLen E l k := rfl

/-- **Unconditional (`0`-parameter) `StickBound` Bridge**:
Combining our `0`-parameter `h1_l_torsion_rank_bound` (`g ≤ 8 * l * [E:ℚ] * log(l * N)`) and
`Stage13MinusParityRubin.length_le_mul_lTorsion`, ANY annihilation exponent `r` killing
`ShaMinusReal E l k` with `r * log l ≤ C * [E:ℚ] * (k + 1) * log(k * l * N)` yields:
`minusParitySelmerSystem.minusLen E l k ≠ ⊤` AND
`((minusParitySelmerSystem.minusLen E l k).toNat : ℝ) * Real.log l ≤ (8 * C) * l * [E:ℚ]^2 * (k + 1) * Real.log (k * l * N)^2`! -/
theorem stickelberger_minusLen_bound_of_annihilation_exponent
    (E : Type) [Field E] [NumberField E]
    (N : ℕ) (hN : 0 < N) (hE : Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ))
    (l : Nat.Primes) (k : ℕ) (hk : 1 ≤ k)
    {C : ℝ} (hC : 0 ≤ C) {r : ℕ}
    (hr_bd : (r : ℝ) * Real.log (l.1 : ℝ) ≤
      C * (Module.finrank ℚ E : ℝ) * ((k : ℝ) + 1) * Real.log ((k : ℝ) * (l.1 : ℝ) * (N : ℝ)))
    (hann : ∀ x ∈ ShaMinusReal E l k, (l.1 : ℤ_[l.1]) ^ r • x = 0) :
    minusParitySelmerSystem.minusLen E l k ≠ ⊤ ∧
    ((minusParitySelmerSystem.minusLen E l k).toNat : ℝ) * Real.log (l.1 : ℝ) ≤
      (8 * C) * (l.1 : ℝ) * (Module.finrank ℚ E : ℝ) ^ 2 * ((k : ℝ) + 1) *
        Real.log ((k : ℝ) * (l.1 : ℝ) * (N : ℝ)) ^ 2 := by
  haveI : Fact l.1.Prime := ⟨l.2⟩
  obtain ⟨g, hg, hgb⟩ := h1_l_torsion_rank_bound E (AlgebraicClosure E) N hN hE l.1
    (canonicalLData E l) (k : ℤ)
  have hker_eq : LinearMap.ker ((l.1 : ℤ_[l.1]) •
      (LinearMap.id : H1 (qzTw (canonicalLData E l) (k : ℤ)) →ₗ[ℤ_[l.1]] _)) =
      Submodule.torsionBy ℤ_[l.1] (H1 (qzTw (canonicalLData E l) (k : ℤ))) (l.1 : ℤ_[l.1]) := by
    ext x; simp [LinearMap.mem_ker, Submodule.mem_torsionBy_iff]
  have hlen_le : minusParitySelmerSystem.minusLen E l k ≤ ((r * g : ℕ) : ℕ∞) := by
    rw [← length_shaMinusReal_eq_minusLen]
    have h1 := length_le_mul_lTorsion (l := l.1) r (ShaMinusReal E l k) hann
    rw [hker_eq] at h1
    calc Module.length ℤ_[l.1] ↥(ShaMinusReal E l k)
        ≤ (r : ℕ∞) * Module.length ℤ_[l.1]
            (Submodule.torsionBy ℤ_[l.1] (H1 (qzTw (canonicalLData E l) (k : ℤ))) (l.1 : ℤ_[l.1])) := h1
      _ ≤ (r : ℕ∞) * (g : ℕ∞) := mul_le_mul_of_nonneg_left hg zero_le
      _ = ((r * g : ℕ) : ℕ∞) := by rw [Nat.cast_mul]
  have hfin : minusParitySelmerSystem.minusLen E l k ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top _) hlen_le
  refine ⟨hfin, ?_⟩
  have htoNat : ((minusParitySelmerSystem.minusLen E l k).toNat : ℝ) ≤ (r : ℝ) * (g : ℝ) := by
    exact_mod_cast ENat.toNat_le_of_le_natCast hlen_le
  have hl1 : (1 : ℝ) ≤ (l.1 : ℝ) := by exact_mod_cast l.2.one_le
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlN : (1 : ℝ) ≤ (l.1 : ℝ) * (N : ℝ) := one_le_mul_of_one_le_of_one_le hl1 hN1
  have hlog_mono : Real.log ((l.1 : ℝ) * (N : ℝ)) ≤ Real.log ((k : ℝ) * (l.1 : ℝ) * (N : ℝ)) :=
    Real.log_le_log (by positivity) (by rw [mul_assoc]; exact le_mul_of_one_le_left (by positivity) hk1)
  have hlog_nn : 0 ≤ Real.log ((k : ℝ) * (l.1 : ℝ) * (N : ℝ)) := (Real.log_nonneg hlN).trans hlog_mono
  have hlogl_nn : 0 ≤ Real.log (l.1 : ℝ) := Real.log_nonneg hl1
  have hgb' : (g : ℝ) ≤ 8 * (l.1 : ℝ) * (Module.finrank ℚ E : ℝ) *
      Real.log ((k : ℝ) * (l.1 : ℝ) * (N : ℝ)) := hgb.trans (by gcongr)
  calc ((minusParitySelmerSystem.minusLen E l k).toNat : ℝ) * Real.log (l.1 : ℝ)
      ≤ ((r : ℝ) * (g : ℝ)) * Real.log (l.1 : ℝ) := by gcongr
    _ = ((r : ℝ) * Real.log (l.1 : ℝ)) * (g : ℝ) := by ring
    _ ≤ (C * (Module.finrank ℚ E : ℝ) * ((k : ℝ) + 1) * Real.log ((k : ℝ) * (l.1 : ℝ) * (N : ℝ))) *
          (8 * (l.1 : ℝ) * (Module.finrank ℚ E : ℝ) * Real.log ((k : ℝ) * (l.1 : ℝ) * (N : ℝ))) :=
        mul_le_mul hr_bd hgb' (Nat.cast_nonneg g) (by positivity)
    _ = (8 * C) * (l.1 : ℝ) * (Module.finrank ℚ E : ℝ) ^ 2 * ((k : ℝ) + 1) *
          Real.log ((k : ℝ) * (l.1 : ℝ) * (N : ℝ)) ^ 2 := by ring

end StickelbergerAnnihilationAlgebraAndBdxLog

/-! ## Section 5: Direct Discharge of `RamifiedPrimeRealization` (`C_ram = 480`) & `VVminusLe` -/

section RamifiedPrimeRealizationAndVVminusLeDischarge

/-- **Minimal Isolated Global-CFT / Stickelberger Annihilation Sub-Hypothesis (`killPow`)**:
Isolates the EXACT single global-CFT + Stickelberger class-group annihilation step from Alpöge's
`UpperTheory.V.Odd.killPow` (`C = 30`, from Hilbert Class Field Artin reciprocity + Stickelberger's
theorem on `ClassGroup (𝓞 (ℚ(ζ_M)))`, neither yet in Mathlib `v4.33.1`).
Everything else (`h1_l_torsion_rank_bound`, `lenPow`, `bdxLog`, `adjKill`, `detR`) is proved
UNCONDITIONALLY with `0` open parameters! -/
def StickelbergerAnnihilatorExponentOnShaMinus
    (E : Type) [Field E] [NumberField E] (t M : ℕ) : Prop :=
  ∀ (l : Nat.Primes) (k : ℕ), (l : ℕ) ≠ 2 → (l : ℕ) ∣ M → 0 < k → k < t →
    ∃ r : ℕ,
      (r : ℝ) * Real.log (l.1 : ℝ) ≤
        30 * (Module.finrank ℚ E : ℝ) * ((k : ℝ) + 1) *
          Real.log ((k : ℝ) * (l.1 : ℝ) * (condF E : ℝ)) ∧
      ∀ x ∈ ShaMinusReal E l k, (l.1 : ℤ_[l.1]) ^ r • x = 0

/-- **Direct Discharge of Odd-Ramified `minusBound` (`C_ram = 240`) on `minusParitySelmerSystem.minusLen`**
from `0`-parameter `h1_l_torsion_rank_bound` + `StickelbergerAnnihilatorExponentOnShaMinus` (`killPow`)! -/
theorem vvminusLe_ramified_realGalois_of_annihilator
    (ψ : PChar) (e_page q d t : ℕ) (hq : 0 < q) (hd : 0 < d) (ht : 2 ≤ t)
    (E : Type) [Field E] [NumberField E] (hE : IsChiField ψ e_page q d E)
    (hKill : StickelbergerAnnihilatorExponentOnShaMinus E t (orderOf ψ.χ)) :
    (∀ (l : Nat.Primes) (k : ℕ), (l : ℕ) ≠ 2 → (l : ℕ) ∣ orderOf ψ.χ →
      0 < k → k < t → minusParitySelmerSystem.minusLen E l k ≠ ⊤) ∧
    (∀ Pram : Finset Nat.Primes, (∀ l ∈ Pram, (l : ℕ) ≠ 2 ∧ (l : ℕ) ∣ orderOf ψ.χ) →
      ∑ l ∈ Pram, Real.log (l : ℕ) *
          ∑ k ∈ Finset.Ico 1 t, ((minusParitySelmerSystem.minusLen E l k).toNat : ℝ) ≤
        TaylorWilesWindow.minusBound 240 (orderOf ψ.χ) (Module.finrank ℚ E) (condF E) t) := by
  classical
  have hcond := cyclotomic_emb_condF_of_isChiField ψ e_page q d hq hd E hE
  have hM0 : orderOf ψ.χ ≠ 0 := (orderOf_pos ψ.χ).ne'
  have hN1 : (1 : ℝ) ≤ (condF E : ℝ) := by exact_mod_cast hcond.1
  have ht1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast (by omega : 1 ≤ t)
  have hfin : ∀ (l : Nat.Primes) (k : ℕ), (l : ℕ) ≠ 2 → (l : ℕ) ∣ orderOf ψ.χ →
      0 < k → k < t → minusParitySelmerSystem.minusLen E l k ≠ ⊤ := fun l k hne2 hdvd hk1 hkt => by
    obtain ⟨r, hr_bd, hann⟩ := hKill l k hne2 hdvd hk1 hkt
    exact (stickelberger_minusLen_bound_of_annihilation_exponent E (condF E) hcond.1 hcond.2
      l k hk1 (by norm_num : (0 : ℝ) ≤ 30) hr_bd hann).1
  refine ⟨hfin, fun Pram hPram => ?_⟩
  have hterm : ∀ l ∈ Pram,
      Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, ((minusParitySelmerSystem.minusLen E l k).toNat : ℝ) ≤
        240 * ((l.1 : ℝ) * (Module.finrank ℚ E : ℝ) ^ 2 * (t : ℝ) ^ 2 *
          Real.log ((t : ℝ) * (l.1 : ℝ) * (condF E : ℝ)) ^ 2) := fun l hl => by
    obtain ⟨hne2, hdvd⟩ := hPram l hl
    have hl1 : (1 : ℝ) ≤ (l.1 : ℝ) := by exact_mod_cast l.2.one_le
    rw [Finset.mul_sum]
    have hinner : ∀ k ∈ Finset.Ico 1 t,
        Real.log (l : ℕ) * ((minusParitySelmerSystem.minusLen E l k).toNat : ℝ) ≤
          240 * ((l.1 : ℝ) * (Module.finrank ℚ E : ℝ) ^ 2 * (t : ℝ) *
            Real.log ((t : ℝ) * (l.1 : ℝ) * (condF E : ℝ)) ^ 2) := fun k hk => by
      rw [Finset.mem_Ico] at hk
      obtain ⟨r, hr_bd, hann⟩ := hKill l k hne2 hdvd hk.1 hk.2
      have hbd := (stickelberger_minusLen_bound_of_annihilation_exponent E (condF E) hcond.1 hcond.2
        l k hk.1 (by norm_num : (0 : ℝ) ≤ 30) hr_bd hann).2
      have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
      have hktR : (k : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast hk.2
      have hk_le_t : (k : ℝ) ≤ (t : ℝ) := by linarith
      have hlog_le : Real.log ((k : ℝ) * (l.1 : ℝ) * (condF E : ℝ)) ≤
          Real.log ((t : ℝ) * (l.1 : ℝ) * (condF E : ℝ)) :=
        Real.log_le_log (by positivity) (by gcongr)
      have hlog_nn : 0 ≤ Real.log ((k : ℝ) * (l.1 : ℝ) * (condF E : ℝ)) :=
        Real.log_nonneg (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hk1R hl1) hN1)
      have hsq : Real.log ((k : ℝ) * (l.1 : ℝ) * (condF E : ℝ)) ^ 2 ≤
          Real.log ((t : ℝ) * (l.1 : ℝ) * (condF E : ℝ)) ^ 2 :=
        pow_le_pow_left₀ hlog_nn hlog_le 2
      calc Real.log (l : ℕ) * ((minusParitySelmerSystem.minusLen E l k).toNat : ℝ)
          = ((minusParitySelmerSystem.minusLen E l k).toNat : ℝ) * Real.log (l.1 : ℝ) := mul_comm _ _
        _ ≤ (8 * 30) * (l.1 : ℝ) * (Module.finrank ℚ E : ℝ) ^ 2 * ((k : ℝ) + 1) *
              Real.log ((k : ℝ) * (l.1 : ℝ) * (condF E : ℝ)) ^ 2 := hbd
        _ ≤ (8 * 30) * (l.1 : ℝ) * (Module.finrank ℚ E : ℝ) ^ 2 * (t : ℝ) *
              Real.log ((t : ℝ) * (l.1 : ℝ) * (condF E : ℝ)) ^ 2 := by gcongr
        _ = 240 * ((l.1 : ℝ) * (Module.finrank ℚ E : ℝ) ^ 2 * (t : ℝ) *
              Real.log ((t : ℝ) * (l.1 : ℝ) * (condF E : ℝ)) ^ 2) := by ring
    calc ∑ k ∈ Finset.Ico 1 t, Real.log (l : ℕ) * ((minusParitySelmerSystem.minusLen E l k).toNat : ℝ)
        ≤ ∑ _k ∈ Finset.Ico 1 t, 240 * ((l.1 : ℝ) * (Module.finrank ℚ E : ℝ) ^ 2 * (t : ℝ) *
            Real.log ((t : ℝ) * (l.1 : ℝ) * (condF E : ℝ)) ^ 2) := Finset.sum_le_sum hinner
      _ = ((t - 1 : ℕ) : ℝ) * (240 * ((l.1 : ℝ) * (Module.finrank ℚ E : ℝ) ^ 2 * (t : ℝ) *
            Real.log ((t : ℝ) * (l.1 : ℝ) * (condF E : ℝ)) ^ 2)) := by
          rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      _ ≤ (t : ℝ) * (240 * ((l.1 : ℝ) * (Module.finrank ℚ E : ℝ) ^ 2 * (t : ℝ) *
            Real.log ((t : ℝ) * (l.1 : ℝ) * (condF E : ℝ)) ^ 2)) := by
          gcongr; exact_mod_cast Nat.sub_le t 1
      _ = 240 * ((l.1 : ℝ) * (Module.finrank ℚ E : ℝ) ^ 2 * (t : ℝ) ^ 2 *
            Real.log ((t : ℝ) * (l.1 : ℝ) * (condF E : ℝ)) ^ 2) := by ring
  unfold TaylorWilesWindow.minusBound
  have hfirst_nn : 0 ≤ 3 * (Module.finrank ℚ E : ℝ) * (t : ℝ) ^ 2 * Real.log ((t : ℝ) * (condF E : ℝ)) := by
    have hlog : 0 ≤ Real.log ((t : ℝ) * (condF E : ℝ)) := Real.log_nonneg (by nlinarith)
    positivity
  have hsum_le :
      ∑ l ∈ Pram, Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, ((minusParitySelmerSystem.minusLen E l k).toNat : ℝ) ≤
        240 * ∑ m ∈ (orderOf ψ.χ).primeFactors.erase 2,
          (m : ℝ) * (Module.finrank ℚ E : ℝ) ^ 2 * (t : ℝ) ^ 2 *
            Real.log ((t : ℝ) * (m : ℝ) * (condF E : ℝ)) ^ 2 := by
    calc ∑ l ∈ Pram, Real.log (l : ℕ) * ∑ k ∈ Finset.Ico 1 t, ((minusParitySelmerSystem.minusLen E l k).toNat : ℝ)
        ≤ ∑ l ∈ Pram, 240 * ((l.1 : ℝ) * (Module.finrank ℚ E : ℝ) ^ 2 * (t : ℝ) ^ 2 *
            Real.log ((t : ℝ) * (l.1 : ℝ) * (condF E : ℝ)) ^ 2) := Finset.sum_le_sum hterm
      _ = 240 * ∑ m ∈ Pram.image (fun p : Nat.Primes => (p : ℕ)),
            (m : ℝ) * (Module.finrank ℚ E : ℝ) ^ 2 * (t : ℝ) ^ 2 *
              Real.log ((t : ℝ) * (m : ℝ) * (condF E : ℝ)) ^ 2 := by
          rw [← Finset.mul_sum]
          congr 1
          exact (Finset.sum_image
            (f := fun m : ℕ => (m : ℝ) * (Module.finrank ℚ E : ℝ) ^ 2 * (t : ℝ) ^ 2 *
              Real.log ((t : ℝ) * (m : ℝ) * (condF E : ℝ)) ^ 2)
            (g := fun p : Nat.Primes => (p : ℕ))
            (fun a _ b _ h => Nat.Primes.coe_nat_injective h)).symm
      _ ≤ 240 * ∑ m ∈ (orderOf ψ.χ).primeFactors.erase 2,
            (m : ℝ) * (Module.finrank ℚ E : ℝ) ^ 2 * (t : ℝ) ^ 2 *
              Real.log ((t : ℝ) * (m : ℝ) * (condF E : ℝ)) ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => by positivity)
          intro m hm
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
          exact Finset.mem_erase.mpr ⟨(hPram p hp).1, Nat.mem_primeFactors.mpr ⟨p.2, (hPram p hp).2, hM0⟩⟩
  linarith

end RamifiedPrimeRealizationAndVVminusLeDischarge

/-! ## Section 6: Verbatim Field #4a (`StickelbergerRamifiedControl`) Realization & Gap Isolation -/

section Field4aStickelbergerRamifiedControlRealization

/-- **Unconditional (`0`-parameter) `StickelbergerRamifiedControl` for Totally-Real Fields**:
When `E` admits no nontrivial `CMGaloisInvolution`, `minusParitySelmerSystem.minusLen E l k = 0`
identically, so `StickelbergerRamifiedControl` holds with ZERO open parameters! -/
theorem stickelbergerRamifiedControl_realGalois_of_totallyReal
    (E : Type) [Field E] [NumberField E] (t M : ℕ) (hM : M ≠ 0) (hN : 1 ≤ condF E) (ht : 1 ≤ t)
    (hreal : ¬ ∃ I : CMGaloisInvolution E (AlgebraicClosure E), I.c ≠ 1) :
    Nonempty (StickelbergerRamifiedControl
      ⟨fun E' _ _ l k => minusParitySelmerSystem.minusLen E' l k⟩
      E t M (Module.finrank ℚ E) (condF E)) := by
  refine ⟨{
    M_ne_zero := hM
    N_pos := hN
    t_pos := ht
    genRank := fun _ _ _ _ _ _ => 0
    genRank_le := fun _ _ _ _ _ _ => Nat.zero_le _
    ann := fun _ _ _ _ _ _ => 1
    ann_pos := fun _ _ _ _ _ _ => Nat.one_pos
    shaLen_le := fun l k hne2 _ _ _ => by
      haveI : Fact l.1.Prime := ⟨l.2⟩
      change minusParitySelmerSystem.minusLen E l k ≤ ((0 * padicValNat l.1 1 : ℕ) : ℕ∞)
      rw [zero_mul, Nat.cast_zero, ← length_shaMinusReal_eq_minusLen]
      have hzero : ∀ x ∈ ShaMinusReal E l k, x = 0 := fun x hx => by
        unfold ShaMinusReal at hx
        rw [dif_neg hreal] at hx
        have heig : x ∈ Module.End.eigenspace
            (conjH1 (CMGaloisInvolution.trivial E (AlgebraicClosure E)) (canonicalLData E l) (k : ℤ))
            ((-1 : ℤ_[l.1]) ^ (k + 1)) := hx.2
        rw [Module.End.mem_eigenspace_iff] at heig
        have hact : conjH1 (CMGaloisInvolution.trivial E (AlgebraicClosure E))
            (canonicalLData E l) (k : ℤ) x = ((-1 : ℤ_[l.1]) ^ k) • x := by
          obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
          dsimp only [conjH1]
          simp only [pairH1, Submodule.mapQ_apply]
          rw [← Submodule.Quotient.mk_smul]
          congr 1
          ext g
          change ((-1 : ℤ_[l.1]) ^ (k : ℤ).natAbs) •
            f.1 (gsConj (CMGaloisInvolution.trivial E (AlgebraicClosure E)) l.1 (canonicalLData E l) g) =
            ((-1 : ℤ_[l.1]) ^ k) • f.1 g
          have hgs : gsConj (CMGaloisInvolution.trivial E (AlgebraicClosure E)) l.1
              (canonicalLData E l) g = g := by
            obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective g
            change gsConj (CMGaloisInvolution.trivial E (AlgebraicClosure E)) l.1
              (canonicalLData E l) (toGS (AlgebraicClosure E) _ σ) = toGS (AlgebraicClosure E) _ σ
            rw [gsConj_mk]
            congr 1
          rw [hgs, Int.natAbs_natCast]
        rw [hact] at heig
        have h2 : (2 : ℤ_[l.1]) • x = 0 := by
          have hadd : ((-1 : ℤ_[l.1]) ^ k + (-1 : ℤ_[l.1]) ^ k) • x = 0 := by
            rw [add_smul]
            conv_lhs => arg 1; rw [heig]
            rw [pow_succ, mul_neg, mul_one, neg_smul, neg_add_cancel]
          have hunit : IsUnit ((-1 : ℤ_[l.1]) ^ k) := (isUnit_one.neg).pow k
          rcases hunit with ⟨u, hu⟩
          have h2u : (2 : ℤ_[l.1]) • ((u : ℤ_[l.1]) • x) = 0 := by
            rw [two_smul, ← add_smul, hu]; exact hadd
          rw [← mul_smul, mul_comm, mul_smul] at h2u
          have h3 := congrArg (fun y => ((u⁻¹ : ℤ_[l.1]ˣ) : ℤ_[l.1]) • y) h2u
          rw [← mul_smul, Units.inv_mul, one_smul, smul_zero] at h3
          exact h3
        rcases isUnit_two_padicInt_of_ne_two hne2 with ⟨u2, hu2⟩
        have h3 := congrArg (fun y => ((u2⁻¹ : ℤ_[l.1]ˣ) : ℤ_[l.1]) • y) h2
        rw [← hu2, ← mul_smul, Units.inv_mul, one_smul, smul_zero] at h3
        exact h3
      haveI : Subsingleton ↥(ShaMinusReal E l k) := ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ =>
        Subtype.ext ((hzero x hx).trans (hzero y hy).symm)⟩
      rw [Module.length_eq_zero]
    bernoulli_control := fun l k _ _ hk1 _ => by
      refine ⟨0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, 1, Nat.zero_le _,
        fun i => i.elim0, fun i => i.elim0, le_rfl, ?_, ?_⟩
      · rw [Nat.cast_one, Real.log_one]
        have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
        have hN1 : (1 : ℝ) ≤ (condF E : ℝ) := by exact_mod_cast hN
        have hlog_nn : 0 ≤ Real.log (2 * (k : ℝ) * (condF E : ℝ)) :=
          Real.log_nonneg (by nlinarith)
        positivity
      · simp }⟩

/-- **Minimal Sharp Mazur–Wiles / Stickelberger Sub-Hypothesis for Field #4a VERBATIM**:
Because `Stage11StickelbergerRamified.StickelbergerRamifiedControl S E t M n N` enforces
`genRank ≤ n` and `log ann ≤ 5 * n * k * log(2 * k * N)` (forcing `minusLen * log l ≤ 5 * n^2 * k * log(2 * k * N)`,
strictly sharper than Alpöge's elementary `killPow * gen` bound `240 * l * n^2 * (k + 1) * log(k * l * N)^2`),
inhabiting `StickelbergerRamifiedControl` verbatim requires the Mazur–Wiles / sharp Stickelberger
annihilation bound isolated cleanly here. -/
def SharpStickelbergerMinusLenHypothesis
    (E : Type) [Field E] [NumberField E] (t M N : ℕ) : Prop :=
  ∀ (l : Nat.Primes) (k : ℕ), (l : ℕ) ≠ 2 → (l : ℕ) ∣ M → 0 < k → k < t →
    ∃ (m : ℕ),
      minusParitySelmerSystem.minusLen E l k ≤ ((Module.finrank ℚ E * m : ℕ) : ℕ∞) ∧
      (m : ℝ) * Real.log (l.1 : ℝ) ≤
        (Module.finrank ℚ E : ℝ) * (k : ℝ) * Real.log (2 * (k : ℝ) * (N : ℝ))

/-- **VERBATIM FIELD #4a DISCHARGE (`Stage13Field1Unification.lean:844–847`)** from
`SharpStickelbergerMinusLenHypothesis`! -/
theorem stickelbergerRamifiedControl_realGalois_of_sharp
    (ψ : PChar) (e t : ℝ → ℕ) (hAdm : AdmissiblePage 4 401 e t)
    (x : ℝ) (hx : 2 ≤ x) (q d : ℕ) (hPP : TaylorWilesWindow.PrimePair ψ.N q d)
    (E : Type) [Field E] [NumberField E] (hE : IsChiField ψ (e x) q d E)
    (_hne : (ψ.N.primeFactors.erase 2).Nonempty)
    (hSharp : SharpStickelbergerMinusLenHypothesis E (t x) (orderOf ψ.χ) (condF E)) :
    Nonempty (StickelbergerRamifiedControl
      ⟨fun E' _ _ l k => minusParitySelmerSystem.minusLen E' l k⟩ E (t x)
      (orderOf ψ.χ) (Module.finrank ℚ E) (condF E)) := by
  have hcond := condF_bounds_of_isChiField ψ (e x) q d hPP.q_prime.pos hPP.d_prime.pos E hE
  have ht2 : 2 ≤ t x := (hAdm x hx).2.2.1
  have hM0 : orderOf ψ.χ ≠ 0 := (orderOf_pos ψ.χ).ne'
  choose m hm_len hm_log using hSharp
  refine ⟨{
    M_ne_zero := hM0
    N_pos := hcond.1
    t_pos := by omega
    genRank := fun _ _ _ _ _ _ => Module.finrank ℚ E
    genRank_le := fun _ _ _ _ _ _ => le_rfl
    ann := fun l k hne2 hdvd hk1 hkt => l.1 ^ m l k hne2 hdvd hk1 hkt
    ann_pos := fun l k hne2 hdvd hk1 hkt => pow_pos l.2.pos _
    shaLen_le := fun l k hne2 hdvd hk1 hkt => by
      haveI : Fact l.1.Prime := ⟨l.2⟩
      change minusParitySelmerSystem.minusLen E l k ≤ _
      rw [padicValNat.prime_pow]
      exact hm_len l k hne2 hdvd hk1 hkt
    bernoulli_control := fun l k hne2 hdvd hk1 hkt => by
      refine ⟨0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
        l.1 ^ m l k hne2 hdvd hk1 hkt, Nat.zero_le _, fun i => i.elim0, fun i => i.elim0,
        Nat.one_le_pow _ _ l.2.pos, ?_, ?_⟩
      · rw [Nat.cast_pow, Real.log_pow]
        exact hm_log l k hne2 hdvd hk1 hkt
      · simp }⟩

end Field4aStickelbergerRamifiedControlRealization

end RHDirect.Stage13StickelbergerRealize

end
