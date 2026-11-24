import RHDirect.ChenDefs
import RHDirect.Stage8MertensTheorems
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# RHDirect.ChenLinearSieve

Formalization of:
1. **Rosser–Iwaniec Linear Sieve (`β = 2`)** (`linear_sieve_upper`, `linear_sieve_lower`)
   for any `LinearSieveDensity ω K` and any `LinearSievePair F f`, with `z₀` depending
   only on `(K, F, f, ε)`.
2. **Uniform Chen Prime Density Theorems** (`chenPrimeDensity_linearSieve`,
   `siftProd_chenPrimeDensity_pos`, `siftProd_chenPrimeDensity_ratio_of_ge_rpow`)
   using `RHDirect.Stage8MertensTheorems.mertens_third_theorem_quant`.

Zero `sorry`, zero custom `axiom`s, zero `opaque`, zero `native_decide`.
-/

noncomputable section

open Finset Classical MeasureTheory Set Filter

namespace RHDirect.Chen

/-! ## Section 1: Rosser (`β = 2`) Combinatorial Sieve Weights & Exact Buchstab Identities -/

/-- Helper: two strictly decreasing lists of natural numbers that are permutations of each other
are equal. -/
private lemma list_eq_of_perm_of_pairwise_gt :
    ∀ {L₁ L₂ : List ℕ}, L₁.Perm L₂ → L₁.Pairwise (· > ·) → L₂.Pairwise (· > ·) → L₁ = L₂ := by
  intro L₁
  induction L₁ with
  | nil =>
    intro L₂ hp _ _
    exact hp.nil_eq
  | cons a t₁ ih =>
    intro L₂ hp hw₁ hw₂
    cases L₂ with
    | nil => exact (hp.symm.nil_eq).symm
    | cons b t₂ =>
      have ha_mem : a ∈ b :: t₂ := hp.subset (by simp)
      have hb_mem : b ∈ a :: t₁ := hp.symm.subset (by simp)
      have hab : a = b := by
        rcases List.mem_cons.mp ha_mem with rfl | ha'
        · rfl
        · rcases List.mem_cons.mp hb_mem with rfl | hb'
          · rfl
          · have h1 : b > a := (List.pairwise_cons.mp hw₂).1 a ha'
            have h2 : a > b := (List.pairwise_cons.mp hw₁).1 b hb'
            omega
      subst hab
      congr 1
      exact ih (hp.cons_inv) (List.pairwise_cons.mp hw₁).2 (List.pairwise_cons.mp hw₂).2

/-- Helper: `s.sort (· ≥ ·)` on `s : Finset ℕ` is strictly decreasing (`Pairwise (· > ·)`). -/
private lemma finset_sort_pairwise_gt (s : Finset ℕ) : (s.sort (· ≥ ·)).Pairwise (· > ·) := by
  have hs : (s.sort (· ≥ ·)).Pairwise (· ≥ ·) := Finset.pairwise_sort s (· ≥ ·)
  have hnd : (s.sort (· ≥ ·)).Nodup := Finset.sort_nodup s (· ≥ ·)
  rw [List.pairwise_iff_getElem] at hs ⊢
  rw [List.Nodup, List.pairwise_iff_getElem] at hnd
  intro i j hi hj hij
  have hge := hs i j hi hj hij
  have hne := hnd i j hi hj hij
  omega

/-- Helper: `(s.sort (· ≥ ·)).prod = ∏ p ∈ s, p` for `s : Finset ℕ`. -/
private lemma finset_sort_prod (s : Finset ℕ) : (s.sort (· ≥ ·)).prod = ∏ p ∈ s, p := by
  have hnd : (s.sort (· ≥ ·)).Nodup := Finset.sort_nodup s (· ≥ ·)
  have hto : (s.sort (· ≥ ·)).toFinset = s := by
    ext x; simp
  rw [← hto, List.prod_toFinset _ hnd]
  simp

/-- Recursive Rosser (`β = 2`) admissibility predicate on a strictly descending list of primes:
- `sign = true` (`D⁺`, upper sieve): checks `p^3 < D` at even 0-based indices (`p₁, p₃, ...`).
- `sign = false` (`D⁻`, lower sieve): checks `p^3 < D` at odd 0-based indices (`p₂, p₄, ...`). -/
def rosserOk (sign : Bool) (D : ℝ) : List ℕ → Prop
  | [] => True
  | p :: rest =>
    if sign then (p : ℝ) ^ 3 < D ∧ rosserOk false (D / (p : ℝ)) rest
    else rosserOk true (D / (p : ℝ)) rest

/-- Descending list of all primes strictly less than `z : ℝ`. -/
def primesLtList (z : ℝ) : List ℕ :=
  (((Finset.range (⌊z⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) < z)).sort (· ≥ ·))

lemma mem_primesLtList {z : ℝ} {p : ℕ} :
    p ∈ primesLtList z ↔ p.Prime ∧ (p : ℝ) < z := by
  unfold primesLtList
  rw [Finset.mem_sort, Finset.mem_filter, Finset.mem_range]
  constructor
  · intro h; exact h.2
  · intro ⟨hp, hlt⟩
    refine ⟨?_, hp, hlt⟩
    by_cases hz : 0 ≤ z
    · exact Nat.lt_succ_of_le (Nat.le_floor (le_of_lt hlt))
    · have : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
      linarith

lemma primesLtList_nodup (z : ℝ) : (primesLtList z).Nodup :=
  Finset.sort_nodup _ _

lemma primesLtList_pairwise_gt (z : ℝ) : (primesLtList z).Pairwise (· > ·) :=
  finset_sort_pairwise_gt _

lemma primesLtList_prime {z : ℝ} {p : ℕ} (hp : p ∈ primesLtList z) : p.Prime :=
  (mem_primesLtList.mp hp).1

lemma primesLtList_eq_nil_of_le_two {z : ℝ} (hz : z ≤ 2) : primesLtList z = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro p hp
  obtain ⟨hpr, hlt⟩ := mem_primesLtList.mp hp
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpr.two_le
  linarith

/-- Product of `1 - ω p` over a list `L`. -/
def listSiftProd (ω : ℕ → ℝ) : List ℕ → ℝ
  | [] => 1
  | p :: rest => (1 - ω p) * listSiftProd ω rest

lemma listSiftProd_eq_prod_toFinset (ω : ℕ → ℝ) {L : List ℕ} (hnd : L.Nodup) :
    listSiftProd ω L = ∏ p ∈ L.toFinset, (1 - ω p) := by
  induction L with
  | nil => simp [listSiftProd]
  | cons p rest ih =>
    rw [List.nodup_cons] at hnd
    simp only [listSiftProd, List.toFinset_cons]
    rw [Finset.prod_insert (by simp [hnd.1]), ih hnd.2]

lemma listSiftProd_primesLtList (ω : ℕ → ℝ) (z : ℝ) :
    listSiftProd ω (primesLtList z) = siftProd ω z := by
  rw [listSiftProd_eq_prod_toFinset ω (primesLtList_nodup z)]
  unfold siftProd
  refine Finset.prod_congr ?_ fun _ _ => rfl
  ext p
  simp only [List.mem_toFinset, mem_primesLtList, Finset.mem_filter, Finset.mem_range]
  constructor
  · intro ⟨hp, hlt⟩
    refine ⟨?_, hp, hlt⟩
    by_cases hz : 0 ≤ z
    · exact Nat.lt_succ_of_le (Nat.le_floor (le_of_lt hlt))
    · have : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
      linarith
  · intro h; exact h.2

/-- Exact recursive definition of the Rosser main-term sum `V^±_ω(D, L)`:
`∑_{M sublist of L, rosserOk sign D M} (-1)^{M.length} * ∏_{p ∈ M} ω p`. -/
def rosserV (ω : ℕ → ℝ) (sign : Bool) (D : ℝ) : List ℕ → ℝ
  | [] => 1
  | p :: rest =>
    if sign then
      rosserV ω true D rest - if (p : ℝ) ^ 3 < D then ω p * rosserV ω false (D / (p : ℝ)) rest else 0
    else
      rosserV ω false D rest - ω p * rosserV ω true (D / (p : ℝ)) rest

/-- Exact combinatorial sieve indicator sum `S(sign, D, L)`:
`∑_{M sublist of L, rosserOk sign D M} (-1)^{M.length}`.
Equals `rosserV (fun _ => 1) sign D L`. -/
def rosserInd (sign : Bool) (D : ℝ) (L : List ℕ) : ℝ :=
  rosserV (fun _ => 1) sign D L

/-- Fundamental combinatorial sieve inequalities (`β = 2`) by structural induction on `L`:
- Upper sieve: `rosserInd true D L ≥ (if L = [] then 1 else 0)`
- Lower sieve: `rosserInd false D L ≤ (if L = [] then 1 else 0)` -/
lemma rosserInd_bounds (L : List ℕ) :
    ∀ D : ℝ,
      (if L = [] then (1 : ℝ) else 0) ≤ rosserInd true D L ∧
      rosserInd false D L ≤ (if L = [] then (1 : ℝ) else 0) := by
  induction L with
  | nil =>
    intro D
    simp [rosserInd, rosserV]
  | cons p rest ih =>
    intro D
    have h1 := ih D
    have h2 := ih (D / (p : ℝ))
    simp only [rosserInd] at h1 h2 ⊢
    constructor
    · simp only [List.cons_ne_nil, ↓reduceIte, rosserV, one_mul]
      split_ifs with hlt
      · linarith [h1.1, h2.2]
      · have hnn : (0 : ℝ) ≤ if rest = [] then 1 else 0 := by split_ifs <;> norm_num
        linarith [h1.1]
    · simp only [List.cons_ne_nil, ↓reduceIte, rosserV, Bool.false_eq_true, one_mul]
      linarith [h1.2, h2.1]

/-- Support bound for `rosserOk`: if `L` is strictly decreasing positive integers `≥ 2`:
- `rosserOk true D L` implies `∏ L < D` (whenever `1 < D`).
- `rosserOk false D L` implies `∏ L < D` (whenever `1 < D` and `∀ p ∈ L, (p : ℝ) < D`). -/
lemma rosserOk_prod_lt :
    ∀ (L : List ℕ) (sign : Bool) (D : ℝ),
      (∀ p ∈ L, 2 ≤ p) →
      L.Pairwise (· > ·) →
      1 < D →
      (∀ p ∈ L, (p : ℝ) < D) →
      rosserOk sign D L →
      (L.prod : ℝ) < D := by
  intro L
  induction L with
  | nil =>
    intro _ D _ _ hD _ _
    simpa using hD
  | cons p rest ih =>
    intro sign D hge hpw hD hlt hok
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hge p (by simp)
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hpw_rest : rest.Pairwise (· > ·) := (List.pairwise_cons.mp hpw).2
    have hge_rest : ∀ q ∈ rest, 2 ≤ q := fun q hq => hge q (by simp [hq])
    cases sign with
    | true =>
      simp only [rosserOk, ↓reduceIte] at hok
      obtain ⟨hp3, hok_rest⟩ := hok
      have hp_cube : (p : ℝ) ^ 3 = (p : ℝ) * (p : ℝ) * (p : ℝ) := by ring
      have hp_sq : (4 : ℝ) ≤ (p : ℝ) * (p : ℝ) := by nlinarith
      cases rest with
      | nil =>
        simp only [List.prod_cons, List.prod_nil, mul_one]
        nlinarith
      | cons q tail =>
        have hqp : q < p := (List.pairwise_cons.mp hpw).1 q (by simp)
        have hqpR : (q : ℝ) < (p : ℝ) := by exact_mod_cast hqp
        have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hge q (by simp)
        have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
        have hp_lt_D : (p : ℝ) < D := by nlinarith
        have hih_f := ih false (D / (p : ℝ)) hge_rest hpw_rest
          (by rw [one_lt_div hp0]; exact hp_lt_D)
          (fun x hx => by
            have hxp : x < p := (List.pairwise_cons.mp hpw).1 x hx
            have hxpR : (x : ℝ) < (p : ℝ) := by exact_mod_cast hxp
            rw [lt_div_iff₀ hp0]
            have : (x : ℝ) * (p : ℝ) < (p : ℝ) * (p : ℝ) := mul_lt_mul_of_pos_right hxpR hp0
            nlinarith)
          hok_rest
        rw [lt_div_iff₀ hp0] at hih_f
        calc (((p :: q :: tail).prod : ℕ) : ℝ)
            = ((q :: tail).prod : ℝ) * (p : ℝ) := by simp [List.prod_cons, mul_comm]
          _ < D := hih_f
    | false =>
      simp only [rosserOk, Bool.false_eq_true, ↓reduceIte] at hok
      cases rest with
      | nil =>
        simp only [List.prod_cons, List.prod_nil, mul_one]
        exact hlt p (by simp)
      | cons q tail =>
        have hq3 : (q : ℝ) ^ 3 < D / (p : ℝ) := by
          simp only [rosserOk, ↓reduceIte] at hok; exact hok.1
        have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hge q (by simp)
        have hq_cube : (q : ℝ) ^ 3 = (q : ℝ) * (q : ℝ) * (q : ℝ) := by ring
        have hq_sq : (4 : ℝ) ≤ (q : ℝ) * (q : ℝ) := by nlinarith
        have hDp1 : 1 < D / (p : ℝ) := by nlinarith
        have hlt_rest : ∀ x ∈ q :: tail, (x : ℝ) < D / (p : ℝ) := by
          intro x hx
          have hxq : x ≤ q := by
            rcases List.mem_cons.mp hx with rfl | hmem
            · exact le_rfl
            · exact le_of_lt ((List.pairwise_cons.mp hpw_rest).1 x hmem)
          have hxqR : (x : ℝ) ≤ (q : ℝ) := by exact_mod_cast hxq
          nlinarith
        have hih_t := ih true (D / (p : ℝ)) hge_rest hpw_rest hDp1 hlt_rest hok
        rw [lt_div_iff₀ hp0] at hih_t
        calc (((p :: q :: tail).prod : ℕ) : ℝ)
            = ((q :: tail).prod : ℝ) * (p : ℝ) := by simp [List.prod_cons, mul_comm]
          _ < D := hih_t

/-- Express `rosserV` explicitly as a sum over all sublists `M` of `L` satisfying `rosserOk`. -/
def rosserSublistSum (f : List ℕ → ℝ) (sign : Bool) (D : ℝ) (L : List ℕ) : ℝ :=
  ((L.sublists.filter (fun M => decide (rosserOk sign D M))).map
    (fun M => (-1 : ℝ) ^ M.length * f M)).sum

lemma rosserV_eq_sublistSum (ω : ℕ → ℝ) (L : List ℕ) :
    ∀ (sign : Bool) (D : ℝ),
      rosserV ω sign D L =
        rosserSublistSum (fun M => (M.map ω).prod) sign D L := by
  induction L with
  | nil =>
    intro sign D
    have hok : rosserOk sign D [] := trivial
    unfold rosserV rosserSublistSum
    rw [List.sublists_nil]
    simp [hok]
  | cons p rest ih =>
    intro sign D
    unfold rosserSublistSum
    have hflat : ∀ (S : List (List ℕ)),
        (((S.flatMap (fun x => [x, p :: x])).filter (fun M => decide (rosserOk sign D M))).map
          (fun M => (-1 : ℝ) ^ M.length * (M.map ω).prod)).sum =
        ((S.filter (fun M => decide (rosserOk sign D M))).map
          (fun M => (-1 : ℝ) ^ M.length * (M.map ω).prod)).sum +
        (((S.map (p :: ·)).filter (fun M => decide (rosserOk sign D M))).map
          (fun M => (-1 : ℝ) ^ M.length * (M.map ω).prod)).sum := by
      intro S
      induction S with
      | nil => simp
      | cons M tl iht =>
        simp only [List.flatMap_cons, List.filter_append, List.map_append, List.sum_append,
          List.filter_cons, List.map_cons, iht]
        split_ifs <;> simp <;> ring
    dsimp only
    rw [List.sublists_cons]
    have hbind : (do let x ← rest.sublists; [x, p :: x]) = rest.sublists.flatMap (fun x => [x, p :: x]) := rfl
    rw [hbind, hflat]
    have hpart1 : ((rest.sublists.filter (fun M => decide (rosserOk sign D M))).map
        (fun M => (-1 : ℝ) ^ M.length * (M.map ω).prod)).sum = rosserV ω sign D rest :=
      (ih sign D).symm
    rw [hpart1]
    cases sign with
    | true =>
      simp only [rosserV, ↓reduceIte]
      by_cases hp3 : (p : ℝ) ^ 3 < D
      · rw [if_pos hp3]
        have hpart2 : (((rest.sublists.map (p :: ·)).filter (fun M => decide (rosserOk true D M))).map
            (fun M => (-1 : ℝ) ^ M.length * (M.map ω).prod)).sum =
            -(ω p * rosserV ω false (D / (p : ℝ)) rest) := by
          rw [ih false (D / (p : ℝ))]
          unfold rosserSublistSum
          rw [List.filter_map, List.map_map]
          have hfilt : rest.sublists.filter ((fun M => decide (rosserOk true D M)) ∘ (p :: ·)) =
              rest.sublists.filter (fun M => decide (rosserOk false (D / (p : ℝ)) M)) := by
            refine List.filter_congr fun M _ => ?_
            simp [rosserOk, hp3]
          rw [hfilt]
          have hmap : ((rest.sublists.filter (fun M => decide (rosserOk false (D / (p : ℝ)) M))).map
              ((fun M => (-1 : ℝ) ^ M.length * (M.map ω).prod) ∘ (p :: ·))).sum =
              (-(ω p)) * ((rest.sublists.filter (fun M => decide (rosserOk false (D / (p : ℝ)) M))).map
                (fun M => (-1 : ℝ) ^ M.length * (M.map ω).prod)).sum := by
            rw [← List.sum_map_mul_left]
            congr 1
            refine List.map_congr_left fun M _ => ?_
            simp only [Function.comp_apply, List.length_cons, pow_succ, List.map_cons, List.prod_cons]
            ring
          rw [hmap]; ring
        rw [hpart2]; ring
      · rw [if_neg hp3, sub_zero]
        have hfilt : (rest.sublists.map (p :: ·)).filter (fun M => decide (rosserOk true D M)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro M hM
          obtain ⟨M', _, rfl⟩ := List.mem_map.mp hM
          simp [rosserOk, hp3]
        rw [hfilt]; simp
    | false =>
      simp only [rosserV, Bool.false_eq_true, ↓reduceIte]
      have hpart2 : (((rest.sublists.map (p :: ·)).filter (fun M => decide (rosserOk false D M))).map
          (fun M => (-1 : ℝ) ^ M.length * (M.map ω).prod)).sum =
          -(ω p * rosserV ω true (D / (p : ℝ)) rest) := by
        rw [ih true (D / (p : ℝ))]
        unfold rosserSublistSum
        rw [List.filter_map, List.map_map]
        have hfilt : rest.sublists.filter ((fun M => decide (rosserOk false D M)) ∘ (p :: ·)) =
            rest.sublists.filter (fun M => decide (rosserOk true (D / (p : ℝ)) M)) := by
          refine List.filter_congr fun M _ => ?_
          simp [rosserOk]
        rw [hfilt]
        have hmap : ((rest.sublists.filter (fun M => decide (rosserOk true (D / (p : ℝ)) M))).map
            ((fun M => (-1 : ℝ) ^ M.length * (M.map ω).prod) ∘ (p :: ·))).sum =
            (-(ω p)) * ((rest.sublists.filter (fun M => decide (rosserOk true (D / (p : ℝ)) M))).map
              (fun M => (-1 : ℝ) ^ M.length * (M.map ω).prod)).sum := by
          rw [← List.sum_map_mul_left]
          congr 1
          refine List.map_congr_left fun M _ => ?_
          simp only [Function.comp_apply, List.length_cons, pow_succ, List.map_cons, List.prod_cons]
          ring
        rw [hmap]; ring
      rw [hpart2]; ring

/-- Prime-factor uniqueness for strictly descending lists of primes: `M ↦ M.prod` produces
squarefree integers whose prime factors are exactly `M.toFinset`. -/
lemma squarefree_prod_of_primes {M : List ℕ} (hpr : ∀ p ∈ M, p.Prime) (hnd : M.Nodup) :
    Squarefree M.prod ∧ M.prod.primeFactors = M.toFinset := by
  induction M with
  | nil => simp
  | cons p rest ih =>
    rw [List.nodup_cons] at hnd
    have hp : p.Prime := hpr p (by simp)
    have hrest := ih (fun q hq => hpr q (by simp [hq])) hnd.2
    have hcop : Nat.Coprime p rest.prod := by
      rw [hp.coprime_iff_not_dvd]
      intro hdvd
      have hmem : p ∈ rest.prod.primeFactors := by
        rw [Nat.mem_primeFactors]
        refine ⟨hp, hdvd, ?_⟩
        intro h0
        have := hrest.1
        rw [h0] at this
        exact not_squarefree_zero this
      rw [hrest.2, List.mem_toFinset] at hmem
      exact hnd.1 hmem
    refine ⟨?_, ?_⟩
    · rw [List.prod_cons]
      exact (Nat.squarefree_mul hcop).mpr ⟨hp.squarefree, hrest.1⟩
    · rw [List.prod_cons, Nat.primeFactors_mul hp.ne_zero (fun h0 => by
        have := hrest.1; rw [h0] at this; exact not_squarefree_zero this),
        hp.primeFactors, hrest.2, List.toFinset_cons]
      ext x; simp

/-- The exact sieve weight `rosserWeight`. -/
def rosserWeight (sign : Bool) (D z : ℝ) (d : ℕ) : ℝ :=
  if Squarefree d ∧ (∀ p ∈ d.primeFactors, (p : ℝ) < z) ∧
     rosserOk sign D (d.primeFactors.sort (· ≥ ·))
  then (-1 : ℝ) ^ d.primeFactors.card else 0

lemma abs_rosserWeight_le_one (sign : Bool) (D z : ℝ) (d : ℕ) :
    |rosserWeight sign D z d| ≤ 1 := by
  unfold rosserWeight
  split_ifs <;> simp

/-- Support of `rosserWeight` lies inside the `d < D` squarefree `< z` divisor set. -/
def sieveDivisors (D z : ℝ) : Finset ℕ :=
  (Finset.range (⌊D⌋₊ + 1)).filter (fun d => Squarefree d ∧ (d : ℝ) < D ∧
    ∀ p ∈ d.primeFactors, (p : ℝ) < z)

lemma rosserWeight_eq_zero_of_not_mem {sign : Bool} {D z : ℝ} (hD1 : 1 < D) (hzD : z ≤ D)
    {d : ℕ} (hd : d ∉ sieveDivisors D z) :
    rosserWeight sign D z d = 0 := by
  unfold rosserWeight
  split_ifs with h
  · exfalso
    obtain ⟨hsq, hltz, hok⟩ := h
    set M := d.primeFactors.sort (· ≥ ·)
    have hpw : M.Pairwise (· > ·) := finset_sort_pairwise_gt d.primeFactors
    have hpr : ∀ p ∈ M, p.Prime := fun p hp =>
      Nat.prime_of_mem_primeFactors (Finset.mem_sort _ |>.mp hp)
    have hge : ∀ p ∈ M, 2 ≤ p := fun p hp => (hpr p hp).two_le
    have hltD : ∀ p ∈ M, (p : ℝ) < D := fun p hp =>
      lt_of_lt_of_le (hltz p (Finset.mem_sort _ |>.mp hp)) hzD
    have hprod_lt : (M.prod : ℝ) < D := rosserOk_prod_lt M sign D hge hpw hD1 hltD hok
    have hprod_eq : M.prod = d := by
      rw [finset_sort_prod]
      exact Nat.prod_primeFactors_of_squarefree hsq
    rw [hprod_eq] at hprod_lt
    apply hd
    unfold sieveDivisors
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (Nat.le_floor (le_of_lt hprod_lt)), hsq, hprod_lt, hltz⟩
  · rfl

/-- Fundamental bijection between `rosserOk` sublists of `primesLtList z` and the support of
`rosserWeight` inside `sieveDivisors D z`. -/
lemma sum_rosserWeight_mul {sign : Bool} {D z : ℝ} (hD1 : 1 < D) (hzD : z ≤ D)
    (g : ℕ → ℝ) :
    ∑ d ∈ sieveDivisors D z, rosserWeight sign D z d * g d =
      rosserSublistSum (fun M => g M.prod) sign D (primesLtList z) := by
  set L := primesLtList z
  set subOk := L.sublists.filter (fun M => decide (rosserOk sign D M))
  have hLpw : L.Pairwise (· > ·) := primesLtList_pairwise_gt z
  have hLnd : L.Nodup := primesLtList_nodup z
  have hsub_nd : subOk.Nodup := (hLnd.sublists).filter _
  have hM_props : ∀ M ∈ subOk,
      M.Pairwise (· > ·) ∧ (∀ p ∈ M, p.Prime) ∧ (∀ p ∈ M, (p : ℝ) < z) ∧
      rosserOk sign D M ∧ M.prod ∈ sieveDivisors D z ∧
      M.prod.primeFactors.sort (· ≥ ·) = M := by
    intro M hM
    rw [List.mem_filter, List.mem_sublists, decide_eq_true_eq] at hM
    obtain ⟨hsub, hok⟩ := hM
    have hpw : M.Pairwise (· > ·) := hLpw.sublist hsub
    have hnd : M.Nodup := hpw.imp (fun h => ne_of_gt h)
    have hpr : ∀ p ∈ M, p.Prime := fun p hp => primesLtList_prime (hsub.subset hp)
    have hltz : ∀ p ∈ M, (p : ℝ) < z := fun p hp => (mem_primesLtList.mp (hsub.subset hp)).2
    have hsq_pf := squarefree_prod_of_primes hpr hnd
    have hprod_lt : (M.prod : ℝ) < D :=
      rosserOk_prod_lt M sign D (fun p hp => (hpr p hp).two_le) hpw hD1
        (fun p hp => lt_of_lt_of_le (hltz p hp) hzD) hok
    have hmem_div : M.prod ∈ sieveDivisors D z := by
      unfold sieveDivisors
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.lt_succ_of_le (Nat.le_floor (le_of_lt hprod_lt)), hsq_pf.1, hprod_lt, ?_⟩
      intro p hp
      rw [hsq_pf.2, List.mem_toFinset] at hp
      exact hltz p hp
    have hsort : M.prod.primeFactors.sort (· ≥ ·) = M := by
      set S := M.prod.primeFactors.sort (· ≥ ·)
      have hSnd : S.Nodup := Finset.sort_nodup _ _
      have hSpw : S.Pairwise (· > ·) := finset_sort_pairwise_gt _
      have hSperm : S.Perm M := by
        refine (List.perm_ext_iff_of_nodup hSnd hnd).mpr fun x => ?_
        rw [Finset.mem_sort, hsq_pf.2, List.mem_toFinset]
      exact list_eq_of_perm_of_pairwise_gt hSperm hSpw hpw
    exact ⟨hpw, hpr, hltz, hok, hmem_div, hsort⟩
  have hRHS : rosserSublistSum (fun M => g M.prod) sign D L =
      ∑ M ∈ subOk.toFinset, (-1 : ℝ) ^ M.length * g M.prod := by
    unfold rosserSublistSum
    rw [← List.sum_toFinset _ hsub_nd]
  set D_ok := (sieveDivisors D z).filter (fun d => rosserOk sign D (d.primeFactors.sort (· ≥ ·)))
  have hLHS : ∑ d ∈ sieveDivisors D z, rosserWeight sign D z d * g d =
      ∑ d ∈ D_ok, (-1 : ℝ) ^ d.primeFactors.card * g d := by
    rw [← Finset.sum_filter_add_sum_filter_not (sieveDivisors D z)
      (fun d => rosserOk sign D (d.primeFactors.sort (· ≥ ·)))]
    have hzero : ∑ d ∈ (sieveDivisors D z).filter (fun d => ¬ rosserOk sign D (d.primeFactors.sort (· ≥ ·))),
        rosserWeight sign D z d * g d = 0 := by
      refine Finset.sum_eq_zero fun d hd => ?_
      rw [Finset.mem_filter] at hd
      unfold rosserWeight
      rw [if_neg (fun h => hd.2 h.2.2), zero_mul]
    rw [hzero, add_zero]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Finset.mem_filter] at hd
    have hmem := hd.1
    unfold sieveDivisors at hmem
    rw [Finset.mem_filter] at hmem
    unfold rosserWeight
    rw [if_pos ⟨hmem.2.1, hmem.2.2.2, hd.2⟩]
  rw [hLHS, hRHS]
  symm
  refine Finset.sum_nbij' (fun M => M.prod) (fun d => d.primeFactors.sort (· ≥ ·))
    ?_ ?_ ?_ ?_ ?_
  · intro M hM
    have hp := hM_props M (List.mem_toFinset.mp hM)
    rw [Finset.mem_filter]
    exact ⟨hp.2.2.2.2.1, by rw [hp.2.2.2.2.2]; exact hp.2.2.2.1⟩
  · intro d hd
    rw [Finset.mem_filter] at hd
    have hmem := hd.1
    unfold sieveDivisors at hmem
    rw [Finset.mem_filter] at hmem
    rw [List.mem_toFinset, List.mem_filter, List.mem_sublists, decide_eq_true_eq]
    refine ⟨?_, hd.2⟩
    set S := d.primeFactors.sort (· ≥ ·)
    have hSnd : S.Nodup := Finset.sort_nodup _ _
    have hSpw : S.Pairwise (· > ·) := finset_sort_pairwise_gt _
    have hsub_mem : ∀ p ∈ S, p ∈ L := fun p hp => by
      have hpf : p ∈ d.primeFactors := (Finset.mem_sort _).mp hp
      exact mem_primesLtList.mpr ⟨Nat.prime_of_mem_primeFactors hpf, hmem.2.2.2 p hpf⟩
    have hSeq : S = L.filter (fun p => decide (p ∈ S)) := by
      have hFnd : (L.filter (fun p => decide (p ∈ S))).Nodup := hLnd.filter _
      have hFpw : (L.filter (fun p => decide (p ∈ S))).Pairwise (· > ·) := hLpw.filter _
      have hperm : S.Perm (L.filter (fun p => decide (p ∈ S))) := by
        refine (List.perm_ext_iff_of_nodup hSnd hFnd).mpr fun x => ?_
        rw [List.mem_filter, decide_eq_true_eq]
        exact ⟨fun hx => ⟨hsub_mem x hx, hx⟩, fun hx => hx.2⟩
      exact list_eq_of_perm_of_pairwise_gt hperm hSpw hFpw
    rw [hSeq]
    exact List.filter_sublist
  · intro M hM
    exact (hM_props M (List.mem_toFinset.mp hM)).2.2.2.2.2
  · intro d hd
    rw [Finset.mem_filter] at hd
    have hmem := hd.1
    unfold sieveDivisors at hmem
    rw [Finset.mem_filter] at hmem
    rw [finset_sort_prod]
    exact Nat.prod_primeFactors_of_squarefree hmem.2.1
  · intro M hM
    have hp := hM_props M (List.mem_toFinset.mp hM)
    have hnd : M.Nodup := hp.1.imp (fun h => ne_of_gt h)
    have hpf := (squarefree_prod_of_primes hp.2.1 hnd).2
    have hcard : M.prod.primeFactors.card = M.length := by
      rw [hpf, List.toFinset_card_of_nodup hnd]
    rw [hcard]

/-- Specialize `sum_rosserWeight_mul` to `g d = multDensity ω d`: yields `rosserV ω sign D (primesLtList z)`. -/
lemma sum_rosserWeight_multDensity {ω : ℕ → ℝ} {sign : Bool} {D z : ℝ} (hD1 : 1 < D) (hzD : z ≤ D) :
    ∑ d ∈ sieveDivisors D z, rosserWeight sign D z d * multDensity ω d =
      rosserV ω sign D (primesLtList z) := by
  rw [sum_rosserWeight_mul hD1 hzD, rosserV_eq_sublistSum]
  unfold rosserSublistSum
  congr 1
  refine List.map_congr_left fun M hM => ?_
  rw [List.mem_filter, List.mem_sublists, decide_eq_true_eq] at hM
  have hLpw := primesLtList_pairwise_gt z
  have hpw := hLpw.sublist hM.1
  have hnd : M.Nodup := hpw.imp (fun h => ne_of_gt h)
  have hpr : ∀ p ∈ M, p.Prime := fun p hp => primesLtList_prime (hM.1.subset hp)
  have hsq_pf := squarefree_prod_of_primes hpr hnd
  congr 1
  dsimp only [multDensity]
  rw [if_pos hsq_pf.1, hsq_pf.2, List.prod_toFinset _ hnd]

/-- Specialize `sum_rosserWeight_mul` to divisibility indicator `g d = if d ∣ a then 1 else 0`:
equals `rosserInd sign D ((primesLtList z).filter (fun p => decide (p ∣ a)))`. -/
lemma sum_rosserWeight_dvd {sign : Bool} {D z : ℝ} (hD1 : 1 < D) (hzD : z ≤ D) (a : ℕ) :
    ∑ d ∈ sieveDivisors D z, rosserWeight sign D z d * (if d ∣ a then (1 : ℝ) else 0) =
      rosserInd sign D ((primesLtList z).filter (fun p => decide (p ∣ a))) := by
  rw [sum_rosserWeight_mul hD1 hzD]
  unfold rosserInd
  rw [rosserV_eq_sublistSum]
  set L := primesLtList z
  set La := L.filter (fun p => decide (p ∣ a))
  have hLnd : L.Nodup := primesLtList_nodup z
  have hLpw : L.Pairwise (· > ·) := primesLtList_pairwise_gt z
  have hLand : La.Nodup := hLnd.filter _
  unfold rosserSublistSum
  have hmap_one : ∀ M : List ℕ, (M.map (fun _ => (1 : ℝ))).prod = 1 := fun M => by
    induction M <;> simp [*]
  have hRHS_eq : ((La.sublists.filter (fun M => decide (rosserOk sign D M))).map
      (fun M => (-1 : ℝ) ^ M.length * (M.map (fun _ => (1 : ℝ))).prod)).sum =
      ∑ M ∈ (La.sublists.filter (fun M => decide (rosserOk sign D M))).toFinset, (-1 : ℝ) ^ M.length := by
    rw [← List.sum_toFinset _ ((hLand.sublists).filter _)]
    refine Finset.sum_congr rfl fun M _ => by rw [hmap_one, mul_one]
  rw [hRHS_eq]
  rw [← List.sum_toFinset _ ((hLnd.sublists).filter _)]
  have hLHS_filt :
      ∑ M ∈ (L.sublists.filter (fun M => decide (rosserOk sign D M))).toFinset,
        (-1 : ℝ) ^ M.length * (if M.prod ∣ a then (1 : ℝ) else 0) =
      ∑ M ∈ ((L.sublists.filter (fun M => decide (rosserOk sign D M))).toFinset).filter (fun M => M.prod ∣ a),
        (-1 : ℝ) ^ M.length := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun M _ => by split_ifs <;> ring
  rw [hLHS_filt]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext M
  simp only [Finset.mem_filter, List.mem_toFinset, List.mem_filter, List.mem_sublists, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hsub, hok⟩, hdvd⟩
    refine ⟨?_, hok⟩
    have hMpw : M.Pairwise (· > ·) := hLpw.sublist hsub
    have hMnd : M.Nodup := hMpw.imp (fun h => ne_of_gt h)
    have hsub_La : ∀ p ∈ M, p ∈ La := fun p hp => by
      rw [List.mem_filter, decide_eq_true_eq]
      exact ⟨hsub.subset hp, dvd_trans (List.dvd_prod hp) hdvd⟩
    have hLapw : La.Pairwise (· > ·) := hLpw.filter _
    have hMeq : M = La.filter (fun p => decide (p ∈ M)) := by
      have hFnd : (La.filter (fun p => decide (p ∈ M))).Nodup := hLand.filter _
      have hFpw : (La.filter (fun p => decide (p ∈ M))).Pairwise (· > ·) := hLapw.filter _
      have hperm : M.Perm (La.filter (fun p => decide (p ∈ M))) :=
        (List.perm_ext_iff_of_nodup hMnd hFnd).mpr fun x => by
          rw [List.mem_filter, decide_eq_true_eq]
          exact ⟨fun hx => ⟨hsub_La x hx, hx⟩, fun hx => hx.2⟩
      exact list_eq_of_perm_of_pairwise_gt hperm hMpw hFpw
    rw [hMeq]; exact List.filter_sublist
  · rintro ⟨hsub, hok⟩
    have hsubL : List.Sublist M L := hsub.trans List.filter_sublist
    refine ⟨⟨hsubL, hok⟩, ?_⟩
    have hMpw : M.Pairwise (· > ·) := hLpw.sublist hsubL
    have hMnd : M.Nodup := hMpw.imp (fun h => ne_of_gt h)
    have hMpr : ∀ p ∈ M, p.Prime := fun p hp => primesLtList_prime (hsubL.subset hp)
    have hMdvd : ∀ p ∈ M, p ∣ a := fun p hp => by
      have := hsub.subset hp
      rw [List.mem_filter, decide_eq_true_eq] at this
      exact this.2
    clear hsub hsubL hok hMpw
    induction M with
    | nil => simp
    | cons p rest ih =>
      rw [List.nodup_cons] at hMnd
      have hp : p.Prime := hMpr p (by simp)
      have hpa : p ∣ a := hMdvd p (by simp)
      have hrest_a : rest.prod ∣ a :=
        ih hMnd.2 (fun q hq => hMpr q (by simp [hq])) (fun q hq => hMdvd q (by simp [hq]))
      have hcop : Nat.Coprime p rest.prod := by
        rw [hp.coprime_iff_not_dvd]
        intro hdvd
        have hsq := squarefree_prod_of_primes (fun q hq => hMpr q (by simp [hq])) hMnd.2
        have hmem : p ∈ rest.prod.primeFactors := by
          rw [Nat.mem_primeFactors]
          refine ⟨hp, hdvd, fun h0 => by have := hsq.1; rw [h0] at this; exact not_squarefree_zero this⟩
        rw [hsq.2, List.mem_toFinset] at hmem
        exact hMnd.1 hmem
      rw [List.prod_cons]
      exact hcop.mul_dvd_of_dvd_of_dvd hpa hrest_a

/-- **Abstract Rosser Sieve Fundamental Inequality** (connects `siftedCard A z` directly to
`X * rosserV ω sign D (primesLtList z)` plus the remainder sum over `sieveDivisors D z`). -/
theorem siftedCard_rosser_bounds (ω : ℕ → ℝ) (A : Finset ℕ) {X D z : ℝ} (hD1 : 1 < D) (hzD : z ≤ D) :
    (siftedCard A z : ℝ) ≤
      X * rosserV ω true D (primesLtList z) +
        ∑ d ∈ sieveDivisors D z, |((A.filter (fun a => d ∣ a)).card : ℝ) - X * multDensity ω d| ∧
    X * rosserV ω false D (primesLtList z) -
        ∑ d ∈ sieveDivisors D z, |((A.filter (fun a => d ∣ a)).card : ℝ) - X * multDensity ω d| ≤
      (siftedCard A z : ℝ) := by
  have hswap : ∀ sign : Bool,
      ∑ a ∈ A, rosserInd sign D ((primesLtList z).filter (fun p => decide (p ∣ a))) =
        X * rosserV ω sign D (primesLtList z) +
          ∑ d ∈ sieveDivisors D z,
            rosserWeight sign D z d * (((A.filter (fun a => d ∣ a)).card : ℝ) - X * multDensity ω d) := by
    intro sign
    have h1 : ∑ a ∈ A, rosserInd sign D ((primesLtList z).filter (fun p => decide (p ∣ a))) =
        ∑ d ∈ sieveDivisors D z, rosserWeight sign D z d * ((A.filter (fun a => d ∣ a)).card : ℝ) := by
      calc ∑ a ∈ A, rosserInd sign D ((primesLtList z).filter (fun p => decide (p ∣ a)))
          = ∑ a ∈ A, ∑ d ∈ sieveDivisors D z, rosserWeight sign D z d * (if d ∣ a then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl fun a _ => (sum_rosserWeight_dvd hD1 hzD a).symm
        _ = ∑ d ∈ sieveDivisors D z, ∑ a ∈ A, rosserWeight sign D z d * (if d ∣ a then (1 : ℝ) else 0) :=
            Finset.sum_comm
        _ = ∑ d ∈ sieveDivisors D z, rosserWeight sign D z d * ((A.filter (fun a => d ∣ a)).card : ℝ) := by
            refine Finset.sum_congr rfl fun d _ => ?_
            rw [← Finset.mul_sum, Finset.sum_boole]
    rw [h1, ← sum_rosserWeight_multDensity (ω := ω) hD1 hzD, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => by ring
  have hrem_bd : ∀ sign : Bool,
      |∑ d ∈ sieveDivisors D z,
          rosserWeight sign D z d * (((A.filter (fun a => d ∣ a)).card : ℝ) - X * multDensity ω d)| ≤
        ∑ d ∈ sieveDivisors D z, |((A.filter (fun a => d ∣ a)).card : ℝ) - X * multDensity ω d| := by
    intro sign
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d _ => ?_)
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (abs_rosserWeight_le_one sign D z d)
  have hsift_eq : (siftedCard A z : ℝ) =
      ∑ a ∈ A, if (primesLtList z).filter (fun p => decide (p ∣ a)) = [] then (1 : ℝ) else 0 := by
    unfold siftedCard
    have hbool : (∑ a ∈ A, if (primesLtList z).filter (fun p => decide (p ∣ a)) = [] then (1 : ℝ) else 0) =
        ((A.filter (fun a => (primesLtList z).filter (fun p => decide (p ∣ a)) = [])).card : ℝ) := by
      rw [Finset.sum_boole]
    rw [hbool]
    congr 2
    refine Finset.filter_congr fun a _ => ?_
    rw [List.filter_eq_nil_iff]
    constructor
    · intro h p hp
      obtain ⟨hpr, hlt⟩ := mem_primesLtList.mp hp
      simp [h p hpr hlt]
    · intro h p hpr hlt hdvd
      have := h p (mem_primesLtList.mpr ⟨hpr, hlt⟩)
      simp [hdvd] at this
  constructor
  · have hup : (siftedCard A z : ℝ) ≤
        ∑ a ∈ A, rosserInd true D ((primesLtList z).filter (fun p => decide (p ∣ a))) := by
      rw [hsift_eq]
      exact Finset.sum_le_sum fun a _ => (rosserInd_bounds _ D).1
    rw [hswap true] at hup
    have hbd := (abs_le.mp (hrem_bd true)).2
    linarith
  · have hlo : ∑ a ∈ A, rosserInd false D ((primesLtList z).filter (fun p => decide (p ∣ a))) ≤
        (siftedCard A z : ℝ) := by
      rw [hsift_eq]
      exact Finset.sum_le_sum fun a _ => (rosserInd_bounds _ D).2
    rw [hswap false] at hlo
    have hbd := (abs_le.mp (hrem_bd false)).1
    linarith

/-! ### Exact Buchstab Identities & Positive Error Recursions -/

/-- Exact splitting of `primesLtList z` into `[w, z)` and `< w` for `w ≤ z`. -/
def primesIcoList (w z : ℝ) : List ℕ :=
  (primesLtList z).filter (fun p => decide (w ≤ (p : ℝ)))

lemma primesLtList_split {w z : ℝ} (hwz : w ≤ z) :
    primesLtList z = primesIcoList w z ++ primesLtList w := by
  have hLpw := primesLtList_pairwise_gt z
  have hLnd := primesLtList_nodup z
  have h1pw : (primesIcoList w z).Pairwise (· > ·) := hLpw.filter _
  have h2pw : (primesLtList w).Pairwise (· > ·) := primesLtList_pairwise_gt w
  have hcross : ∀ a ∈ primesIcoList w z, ∀ b ∈ primesLtList w, a > b := by
    intro a ha b hb
    unfold primesIcoList at ha
    rw [List.mem_filter, decide_eq_true_eq] at ha
    have hb_lt : (b : ℝ) < w := (mem_primesLtList.mp hb).2
    exact_mod_cast lt_of_lt_of_le hb_lt ha.2
  have hpw_app : (primesIcoList w z ++ primesLtList w).Pairwise (· > ·) :=
    List.pairwise_append.mpr ⟨h1pw, h2pw, hcross⟩
  have hnd_app : (primesIcoList w z ++ primesLtList w).Nodup :=
    hpw_app.imp (fun h => ne_of_gt h)
  have hperm : (primesLtList z).Perm (primesIcoList w z ++ primesLtList w) := by
    refine (List.perm_ext_iff_of_nodup hLnd hnd_app).mpr fun p => ?_
    rw [List.mem_append]
    unfold primesIcoList
    rw [List.mem_filter, decide_eq_true_eq, mem_primesLtList, mem_primesLtList]
    constructor
    · intro ⟨hpr, hltz⟩
      by_cases hwp : w ≤ (p : ℝ)
      · exact Or.inl ⟨⟨hpr, hltz⟩, hwp⟩
      · exact Or.inr ⟨hpr, lt_of_not_ge hwp⟩
    · rintro (⟨⟨hpr, hltz⟩, _⟩ | ⟨hpr, hltw⟩)
      · exact ⟨hpr, hltz⟩
      · exact ⟨hpr, lt_of_lt_of_le hltw hwz⟩
  exact list_eq_of_perm_of_pairwise_gt hperm hLpw hpw_app

/-- Exact Buchstab identity on any append `L₁ ++ L₂` where every element of `L₁` is strictly greater
than every element of `L₂`. -/
lemma rosserV_true_buchstab_append (ω : ℕ → ℝ) (D : ℝ) (L₁ L₂ : List ℕ)
    (hgt : ∀ p ∈ L₁, ∀ q ∈ L₂, p > q) (hL₁pw : L₁.Pairwise (· > ·))
    (hL₁pr : ∀ p ∈ L₁, p.Prime)
    (hL₂eq : ∀ p ∈ L₁, (L₁ ++ L₂).filter (fun q => decide (q < p)) = primesLtList (p : ℝ)) :
    rosserV ω true D (L₁ ++ L₂) =
      rosserV ω true D L₂ -
        (L₁.map (fun p : ℕ => if (p : ℝ) ^ 3 < D then ω p * rosserV ω false (D / (p : ℝ)) (primesLtList (p : ℝ)) else 0)).sum := by
  induction L₁ with
  | nil => simp
  | cons p rest ih =>
    have hrest_pw : rest.Pairwise (· > ·) := (List.pairwise_cons.mp hL₁pw).2
    have hp_gt_rest : ∀ q ∈ rest, p > q := (List.pairwise_cons.mp hL₁pw).1
    have hp_gt_L₂ : ∀ q ∈ L₂, p > q := fun q hq => hgt p (by simp) q hq
    have htail_eq : rest ++ L₂ = primesLtList (p : ℝ) := by
      have hfilt := hL₂eq p (by simp)
      rw [← hfilt]
      simp only [List.cons_append, List.filter_cons, lt_self_iff_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      symm
      rw [List.filter_eq_self]
      intro q hq
      rw [decide_eq_true_eq]
      rcases List.mem_append.mp hq with hqr | hq2
      · exact hp_gt_rest q hqr
      · exact hp_gt_L₂ q hq2
    have hrest_eq : ∀ r ∈ rest, (rest ++ L₂).filter (fun q => decide (q < r)) = primesLtList (r : ℝ) := by
      intro r hr
      have hfilt := hL₂eq r (by simp [hr])
      have hpr_lt : ¬ p < r := not_lt.mpr (le_of_lt (hp_gt_rest r hr))
      simpa [List.cons_append, List.filter_cons, hpr_lt] using hfilt
    have hih := ih (fun r hr q hq => hgt r (by simp [hr]) q hq) hrest_pw
      (fun r hr => hL₁pr r (by simp [hr])) hrest_eq
    simp only [List.cons_append, rosserV, ↓reduceIte, List.map_cons, List.sum_cons]
    rw [hih, htail_eq]
    ring

lemma rosserV_false_buchstab_append (ω : ℕ → ℝ) (D : ℝ) (L₁ L₂ : List ℕ)
    (hgt : ∀ p ∈ L₁, ∀ q ∈ L₂, p > q) (hL₁pw : L₁.Pairwise (· > ·))
    (hL₁pr : ∀ p ∈ L₁, p.Prime)
    (hL₂eq : ∀ p ∈ L₁, (L₁ ++ L₂).filter (fun q => decide (q < p)) = primesLtList (p : ℝ)) :
    rosserV ω false D (L₁ ++ L₂) =
      rosserV ω false D L₂ -
        (L₁.map (fun p : ℕ => ω p * rosserV ω true (D / (p : ℝ)) (primesLtList (p : ℝ)))).sum := by
  induction L₁ with
  | nil => simp
  | cons p rest ih =>
    have hrest_pw : rest.Pairwise (· > ·) := (List.pairwise_cons.mp hL₁pw).2
    have hp_gt_rest : ∀ q ∈ rest, p > q := (List.pairwise_cons.mp hL₁pw).1
    have hp_gt_L₂ : ∀ q ∈ L₂, p > q := fun q hq => hgt p (by simp) q hq
    have htail_eq : rest ++ L₂ = primesLtList (p : ℝ) := by
      have hfilt := hL₂eq p (by simp)
      rw [← hfilt]
      simp only [List.cons_append, List.filter_cons, lt_self_iff_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      symm
      rw [List.filter_eq_self]
      intro q hq
      rw [decide_eq_true_eq]
      rcases List.mem_append.mp hq with hqr | hq2
      · exact hp_gt_rest q hqr
      · exact hp_gt_L₂ q hq2
    have hrest_eq : ∀ r ∈ rest, (rest ++ L₂).filter (fun q => decide (q < r)) = primesLtList (r : ℝ) := by
      intro r hr
      have hfilt := hL₂eq r (by simp [hr])
      have hpr_lt : ¬ p < r := not_lt.mpr (le_of_lt (hp_gt_rest r hr))
      simpa [List.cons_append, List.filter_cons, hpr_lt] using hfilt
    have hih := ih (fun r hr q hq => hgt r (by simp [hr]) q hq) hrest_pw
      (fun r hr => hL₁pr r (by simp [hr])) hrest_eq
    simp only [List.cons_append, rosserV, Bool.false_eq_true, ↓reduceIte, List.map_cons, List.sum_cons]
    rw [hih, htail_eq]
    ring

/-- The filter of `primesLtList z` to `< p` (for `p < z`) is `primesLtList p`. -/
lemma primesLtList_filter_lt {z : ℝ} {p : ℕ} (hpz : (p : ℝ) < z) :
    (primesLtList z).filter (fun q => decide (q < p)) = primesLtList (p : ℝ) := by
  have h1pw : ((primesLtList z).filter (fun q => decide (q < p))).Pairwise (· > ·) :=
    (primesLtList_pairwise_gt z).filter _
  have h2pw : (primesLtList (p : ℝ)).Pairwise (· > ·) := primesLtList_pairwise_gt (p : ℝ)
  have h1nd := (primesLtList_nodup z).filter (fun q => decide (q < p))
  have h2nd := primesLtList_nodup (p : ℝ)
  have hperm : ((primesLtList z).filter (fun q => decide (q < p))).Perm (primesLtList (p : ℝ)) := by
    refine (List.perm_ext_iff_of_nodup h1nd h2nd).mpr fun q => ?_
    rw [List.mem_filter, decide_eq_true_eq, mem_primesLtList, mem_primesLtList]
    constructor
    · rintro ⟨⟨hqr, _⟩, hqp⟩; exact ⟨hqr, by exact_mod_cast hqp⟩
    · rintro ⟨hqr, hqp⟩
      exact ⟨⟨hqr, lt_trans hqp hpz⟩, by exact_mod_cast hqp⟩
  exact list_eq_of_perm_of_pairwise_gt hperm h1pw h2pw

/-- Exact Buchstab identity for `V⁺(D, z) = rosserV ω true D (primesLtList z)` on `[w, z)`. -/
lemma rosserV_true_buchstab (ω : ℕ → ℝ) (D : ℝ) {w z : ℝ} (hwz : w ≤ z) :
    rosserV ω true D (primesLtList z) =
      rosserV ω true D (primesLtList w) -
        ∑ p ∈ (primesIcoList w z).toFinset,
          if (p : ℝ) ^ 3 < D then ω p * rosserV ω false (D / (p : ℝ)) (primesLtList (p : ℝ)) else 0 := by
  have hsplit := primesLtList_split hwz
  have hnd : (primesIcoList w z).Nodup := (primesLtList_nodup z).filter _
  rw [List.sum_toFinset _ hnd]
  rw [hsplit]
  exact rosserV_true_buchstab_append ω D (primesIcoList w z) (primesLtList w)
    (fun p hp q hq => by
      unfold primesIcoList at hp; rw [List.mem_filter, decide_eq_true_eq] at hp
      exact_mod_cast lt_of_lt_of_le (mem_primesLtList.mp hq).2 hp.2)
    ((primesLtList_pairwise_gt z).filter _)
    (fun p hp => by
      unfold primesIcoList at hp; rw [List.mem_filter] at hp
      exact primesLtList_prime hp.1)
    (fun p hp => by
      rw [← hsplit]
      unfold primesIcoList at hp; rw [List.mem_filter] at hp
      exact primesLtList_filter_lt (mem_primesLtList.mp hp.1).2)

/-- Exact Buchstab identity for `V⁻(D, z) = rosserV ω false D (primesLtList z)` on `[w, z)`. -/
lemma rosserV_false_buchstab (ω : ℕ → ℝ) (D : ℝ) {w z : ℝ} (hwz : w ≤ z) :
    rosserV ω false D (primesLtList z) =
      rosserV ω false D (primesLtList w) -
        ∑ p ∈ (primesIcoList w z).toFinset,
          ω p * rosserV ω true (D / (p : ℝ)) (primesLtList (p : ℝ)) := by
  have hsplit := primesLtList_split hwz
  have hnd : (primesIcoList w z).Nodup := (primesLtList_nodup z).filter _
  rw [List.sum_toFinset _ hnd]
  rw [hsplit]
  exact rosserV_false_buchstab_append ω D (primesIcoList w z) (primesLtList w)
    (fun p hp q hq => by
      unfold primesIcoList at hp; rw [List.mem_filter, decide_eq_true_eq] at hp
      exact_mod_cast lt_of_lt_of_le (mem_primesLtList.mp hq).2 hp.2)
    ((primesLtList_pairwise_gt z).filter _)
    (fun p hp => by
      unfold primesIcoList at hp; rw [List.mem_filter] at hp
      exact primesLtList_prime hp.1)
    (fun p hp => by
      rw [← hsplit]
      unfold primesIcoList at hp; rw [List.mem_filter] at hp
      exact primesLtList_filter_lt (mem_primesLtList.mp hp.1).2)

/-- When `w ≤ z` and `D ≤ w ^ 3`, `V⁺(D, z) = V⁺(D, w)` (primes `p ≥ w` contribute `0`). -/
lemma rosserV_true_eq_of_le_cube (ω : ℕ → ℝ) {D w z : ℝ} (hw0 : 0 ≤ w) (hwz : w ≤ z) (hDw : D ≤ w ^ 3) :
    rosserV ω true D (primesLtList z) = rosserV ω true D (primesLtList w) := by
  rw [rosserV_true_buchstab ω D hwz]
  have hzero : ∑ p ∈ (primesIcoList w z).toFinset,
      (if (p : ℝ) ^ 3 < D then ω p * rosserV ω false (D / (p : ℝ)) (primesLtList (p : ℝ)) else 0) = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [List.mem_toFinset] at hp
    unfold primesIcoList at hp
    rw [List.mem_filter, decide_eq_true_eq] at hp
    have hp3 : w ^ 3 ≤ (p : ℝ) ^ 3 := pow_le_pow_left₀ hw0 hp.2 3
    rw [if_neg (not_lt.mpr (hDw.trans hp3))]
  rw [hzero, sub_zero]

/-- Exact positivity of `Δ⁺(D, L) = V⁺(D, L) - P(L)` and `Δ⁻(D, L) = P(L) - V⁻(D, L)`. -/
lemma rosserV_sandwiches_listSiftProd {ω : ℕ → ℝ} (hnn : ∀ p, 0 ≤ ω p) (hlt : ∀ p, ω p < 1)
    (L : List ℕ) :
    ∀ D : ℝ,
      listSiftProd ω L ≤ rosserV ω true D L ∧
      rosserV ω false D L ≤ listSiftProd ω L := by
  induction L with
  | nil =>
    intro D; simp [listSiftProd, rosserV]
  | cons p rest ih =>
    intro D
    have h1 := ih D
    have h2 := ih (D / (p : ℝ))
    have hωp : 0 ≤ ω p := hnn p
    have hP_nn : 0 ≤ listSiftProd ω rest := by
      clear ih h1 h2
      induction rest with
      | nil => simp [listSiftProd]
      | cons q t iht =>
        simp only [listSiftProd]
        exact mul_nonneg (by linarith [hlt q]) iht
    constructor
    · simp only [listSiftProd, rosserV, ↓reduceIte]
      split_ifs
      · nlinarith [h1.1, h2.2]
      · nlinarith [h1.1, hP_nn]
    · simp only [listSiftProd, rosserV, Bool.false_eq_true, ↓reduceIte]
      nlinarith [h1.2, h2.1]

/-- Exact positive Buchstab identity for `siftProd`:
`siftProd ω z = siftProd ω w - ∑_{p ∈ [w, z)} ω p * siftProd ω p`. -/
lemma siftProd_buchstab (ω : ℕ → ℝ) {w z : ℝ} (hwz : w ≤ z) :
    siftProd ω z = siftProd ω w -
      ∑ p ∈ (primesIcoList w z).toFinset, ω p * siftProd ω (p : ℝ) := by
  rw [← listSiftProd_primesLtList ω z, ← listSiftProd_primesLtList ω w]
  have hsplit := primesLtList_split hwz
  have hnd : (primesIcoList w z).Nodup := (primesLtList_nodup z).filter _
  rw [List.sum_toFinset _ hnd]
  have hgen : ∀ (L₁ L₂ : List ℕ),
      (∀ p ∈ L₁, ∀ q ∈ L₂, p > q) → L₁.Pairwise (· > ·) →
      (∀ p ∈ L₁, (L₁ ++ L₂).filter (fun q => decide (q < p)) = primesLtList (p : ℝ)) →
      listSiftProd ω (L₁ ++ L₂) =
        listSiftProd ω L₂ - (L₁.map (fun p : ℕ => ω p * siftProd ω (p : ℝ))).sum := by
    intro L₁ L₂
    induction L₁ with
    | nil => intro _ _ _; simp
    | cons p rest ih =>
      intro hgt hpw hfilt
      have hrest_pw := (List.pairwise_cons.mp hpw).2
      have hp_rest := (List.pairwise_cons.mp hpw).1
      have hp_L₂ : ∀ q ∈ L₂, p > q := fun q hq => hgt p (by simp) q hq
      have htail : rest ++ L₂ = primesLtList (p : ℝ) := by
        have hf := hfilt p (by simp)
        rw [← hf]
        simp only [List.cons_append, List.filter_cons, lt_self_iff_false, decide_false, Bool.false_eq_true, ↓reduceIte]
        symm; rw [List.filter_eq_self]
        intro q hq; rw [decide_eq_true_eq]
        rcases List.mem_append.mp hq with h1 | h2
        · exact hp_rest q h1
        · exact hp_L₂ q h2
      have hrest_filt : ∀ r ∈ rest, (rest ++ L₂).filter (fun q => decide (q < r)) = primesLtList (r : ℝ) := by
        intro r hr
        have hf := hfilt r (by simp [hr])
        have hpr_lt : ¬ p < r := not_lt.mpr (le_of_lt (hp_rest r hr))
        simpa [List.cons_append, List.filter_cons, hpr_lt] using hf
      have hih := ih (fun r hr q hq => hgt r (by simp [hr]) q hq) hrest_pw hrest_filt
      simp only [List.cons_append, listSiftProd, List.map_cons, List.sum_cons]
      rw [← listSiftProd_primesLtList ω (p : ℝ), ← htail]
      linarith
  rw [hsplit]
  exact hgen (primesIcoList w z) (primesLtList w)
    (fun p hp q hq => by
      unfold primesIcoList at hp; rw [List.mem_filter, decide_eq_true_eq] at hp
      exact_mod_cast lt_of_lt_of_le (mem_primesLtList.mp hq).2 hp.2)
    ((primesLtList_pairwise_gt z).filter _)
    (fun p hp => by
      rw [← hsplit]
      unfold primesIcoList at hp; rw [List.mem_filter] at hp
      exact primesLtList_filter_lt (mem_primesLtList.mp hp.1).2)

/-- Exact Buchstab identity for `Δ⁺ = V⁺ - P` when `z ^ 3 ≤ D` (`s ≥ 3`):
`V⁺(D, z) - P(z) = (V⁺(D, w) - P(w)) + ∑_{w ≤ p < z} ω(p) * (P(p) - V⁻(D/p, p))`. -/
lemma rosserDelta_true_buchstab (ω : ℕ → ℝ) {D w z : ℝ} (hwz : w ≤ z) (hz3 : z ^ 3 ≤ D) :
    rosserV ω true D (primesLtList z) - siftProd ω z =
      (rosserV ω true D (primesLtList w) - siftProd ω w) +
        ∑ p ∈ (primesIcoList w z).toFinset,
          ω p * (siftProd ω (p : ℝ) - rosserV ω false (D / (p : ℝ)) (primesLtList (p : ℝ))) := by
  rw [rosserV_true_buchstab ω D hwz, siftProd_buchstab ω hwz]
  have hsum_eq : ∑ p ∈ (primesIcoList w z).toFinset,
      (if (p : ℝ) ^ 3 < D then ω p * rosserV ω false (D / (p : ℝ)) (primesLtList (p : ℝ)) else 0) =
      ∑ p ∈ (primesIcoList w z).toFinset, ω p * rosserV ω false (D / (p : ℝ)) (primesLtList (p : ℝ)) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [List.mem_toFinset] at hp
    unfold primesIcoList at hp
    rw [List.mem_filter] at hp
    have hpz : (p : ℝ) < z := (mem_primesLtList.mp hp.1).2
    have hp3 : (p : ℝ) ^ 3 < D := lt_of_lt_of_le (pow_lt_pow_left₀ hpz (Nat.cast_nonneg p) (by norm_num)) hz3
    rw [if_pos hp3]
  rw [hsum_eq]
  have hdiff : ∑ p ∈ (primesIcoList w z).toFinset,
      ω p * (siftProd ω (p : ℝ) - rosserV ω false (D / (p : ℝ)) (primesLtList (p : ℝ))) =
      (∑ p ∈ (primesIcoList w z).toFinset, ω p * siftProd ω (p : ℝ)) -
      (∑ p ∈ (primesIcoList w z).toFinset, ω p * rosserV ω false (D / (p : ℝ)) (primesLtList (p : ℝ))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => by ring
  linarith

/-- Exact Buchstab identity for `Δ⁻ = P - V⁻` for any `w ≤ z`:
`P(z) - V⁻(D, z) = (P(w) - V⁻(D, w)) + ∑_{w ≤ p < z} ω(p) * (V⁺(D/p, p) - P(p))`. -/
lemma rosserDelta_false_buchstab (ω : ℕ → ℝ) (D : ℝ) {w z : ℝ} (hwz : w ≤ z) :
    siftProd ω z - rosserV ω false D (primesLtList z) =
      (siftProd ω w - rosserV ω false D (primesLtList w)) +
        ∑ p ∈ (primesIcoList w z).toFinset,
          ω p * (rosserV ω true (D / (p : ℝ)) (primesLtList (p : ℝ)) - siftProd ω (p : ℝ)) := by
  rw [rosserV_false_buchstab ω D hwz, siftProd_buchstab ω hwz]
  have hdiff : ∑ p ∈ (primesIcoList w z).toFinset,
      ω p * (rosserV ω true (D / (p : ℝ)) (primesLtList (p : ℝ)) - siftProd ω (p : ℝ)) =
      (∑ p ∈ (primesIcoList w z).toFinset, ω p * rosserV ω true (D / (p : ℝ)) (primesLtList (p : ℝ))) -
      (∑ p ∈ (primesIcoList w z).toFinset, ω p * siftProd ω (p : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => by ring
  linarith

/-- When `D > z ^ (⌊z⌋₊ + 3)` and `2 ≤ z`, EVERY sublist of `primesLtList z` satisfies
`rosserOk sign D`, hence `rosserV ω sign D (primesLtList z) = siftProd ω z`! -/
lemma rosserV_eq_siftProd_of_large_D (ω : ℕ → ℝ) {D z : ℝ} (hz2 : 2 ≤ z)
    (hD : z ^ (⌊z⌋₊ + 3) < D) (sign : Bool) :
    rosserV ω sign D (primesLtList z) = siftProd ω z := by
  rw [← listSiftProd_primesLtList ω z]
  have hgen : ∀ (L : List ℕ) (sign : Bool) (D' : ℝ),
      (∀ p ∈ L, 2 ≤ p ∧ (p : ℝ) < z) →
      z ^ (L.length + 3) < D' →
      rosserV ω sign D' L = listSiftProd ω L := by
    intro L
    induction L with
    | nil => intro _ _ _ _; simp [rosserV, listSiftProd]
    | cons p rest ih =>
      intro sign D' hmem hD'
      have hp_lt : (p : ℝ) < z := (hmem p (by simp)).2
      have hp0 : (0 : ℝ) < (p : ℝ) := by
        have := (hmem p (by simp)).1; positivity
      have hz1 : 1 ≤ z := by linarith
      have hrest_mem : ∀ q ∈ rest, 2 ≤ q ∧ (q : ℝ) < z := fun q hq => hmem q (by simp [hq])
      have hD'_div : z ^ (rest.length + 3) < D' / (p : ℝ) := by
        rw [lt_div_iff₀ hp0]
        have h1 : z ^ (rest.length + 3) * (p : ℝ) < z ^ (rest.length + 3) * z :=
          mul_lt_mul_of_pos_left hp_lt (pow_pos (by linarith) _)
        have h2 : z ^ (rest.length + 3) * z = z ^ ((p :: rest).length + 3) := by
          rw [List.length_cons, show rest.length + 1 + 3 = (rest.length + 3) + 1 by omega]
          exact (pow_succ z (rest.length + 3)).symm
        linarith
      have hD'_rest : z ^ (rest.length + 3) < D' := by
        have hpow : z ^ (rest.length + 3) ≤ z ^ ((p :: rest).length + 3) :=
          pow_le_pow_right₀ hz1 (by simp)
        linarith
      have hp3 : (p : ℝ) ^ 3 < D' := by
        have h1 : (p : ℝ) ^ 3 < z ^ 3 := pow_lt_pow_left₀ hp_lt hp0.le (by norm_num)
        have h2 : z ^ 3 ≤ z ^ ((p :: rest).length + 3) := pow_le_pow_right₀ hz1 (by omega)
        linarith
      cases sign with
      | true =>
        simp only [rosserV, ↓reduceIte, hp3, listSiftProd]
        rw [ih true D' hrest_mem hD'_rest, ih false (D' / (p : ℝ)) hrest_mem hD'_div]
        ring
      | false =>
        simp only [rosserV, Bool.false_eq_true, ↓reduceIte, listSiftProd]
        rw [ih false D' hrest_mem hD'_rest, ih true (D' / (p : ℝ)) hrest_mem hD'_div]
        ring
  refine hgen (primesLtList z) sign D
    (fun p hp => ⟨(primesLtList_prime hp).two_le, (mem_primesLtList.mp hp).2⟩) ?_
  have hlen : (primesLtList z).length ≤ ⌊z⌋₊ := by
    have hcard : (primesLtList z).length = ((primesLtList z).toFinset).card :=
      (List.toFinset_card_of_nodup (primesLtList_nodup z)).symm
    rw [hcard]
    have hsub : (primesLtList z).toFinset ⊆ Finset.Icc 1 ⌊z⌋₊ := by
      intro p hp
      rw [List.mem_toFinset, mem_primesLtList] at hp
      rw [Finset.mem_Icc]
      exact ⟨hp.1.one_le, Nat.le_floor (le_of_lt hp.2)⟩
    calc ((primesLtList z).toFinset).card
        ≤ (Finset.Icc 1 ⌊z⌋₊).card := Finset.card_le_card hsub
      _ = ⌊z⌋₊ := by simp
  exact lt_of_le_of_lt (pow_le_pow_right₀ (by linarith) (by omega)) hD

/-- Trivial upper bound `|rosserV ω sign D L| ≤ ∏_{p ∈ L} (1 + ω p) ≤ (listSiftProd ω L)⁻¹`. -/
lemma abs_rosserV_le_inv_listSiftProd {ω : ℕ → ℝ} (hnn : ∀ p, 0 ≤ ω p) (hlt : ∀ p, ω p < 1)
    (L : List ℕ) :
    ∀ (sign : Bool) (D : ℝ),
      |rosserV ω sign D L| ≤ (listSiftProd ω L)⁻¹ := by
  induction L with
  | nil =>
    intro sign D; simp [rosserV, listSiftProd]
  | cons p rest ih =>
    intro sign D
    have h1 := ih sign D
    have h2 := ih (!sign) (D / (p : ℝ))
    have hωp : 0 ≤ ω p := hnn p
    have h1m : 0 < 1 - ω p := by linarith [hlt p]
    have hP_pos : 0 < listSiftProd ω rest := by
      clear ih h1 h2
      induction rest with
      | nil => simp [listSiftProd]
      | cons q t iht =>
        simp only [listSiftProd]
        exact mul_pos (by linarith [hlt q]) iht
    have hfactor : 1 + ω p ≤ (1 - ω p)⁻¹ := by
      rw [← one_div, le_div_iff₀ h1m]
      nlinarith
    have hstep : |rosserV ω sign D (p :: rest)| ≤ (1 + ω p) * (listSiftProd ω rest)⁻¹ := by
      cases sign with
      | true =>
        simp only [rosserV, ↓reduceIte]
        split_ifs
        · calc |rosserV ω true D rest - ω p * rosserV ω false (D / (p : ℝ)) rest|
              ≤ |rosserV ω true D rest| + |ω p * rosserV ω false (D / (p : ℝ)) rest| := abs_sub _ _
            _ = |rosserV ω true D rest| + ω p * |rosserV ω false (D / (p : ℝ)) rest| := by
                rw [abs_mul, abs_of_nonneg hωp]
            _ ≤ (listSiftProd ω rest)⁻¹ + ω p * (listSiftProd ω rest)⁻¹ := by
                nlinarith [ih true D, ih false (D / (p : ℝ))]
            _ = (1 + ω p) * (listSiftProd ω rest)⁻¹ := by ring
        · rw [sub_zero]
          calc |rosserV ω true D rest|
              ≤ (listSiftProd ω rest)⁻¹ := ih true D
            _ ≤ (1 + ω p) * (listSiftProd ω rest)⁻¹ := by nlinarith [inv_pos.mpr hP_pos]
      | false =>
        simp only [rosserV, Bool.false_eq_true, ↓reduceIte]
        calc |rosserV ω false D rest - ω p * rosserV ω true (D / (p : ℝ)) rest|
            ≤ |rosserV ω false D rest| + |ω p * rosserV ω true (D / (p : ℝ)) rest| := abs_sub _ _
          _ = |rosserV ω false D rest| + ω p * |rosserV ω true (D / (p : ℝ)) rest| := by
              rw [abs_mul, abs_of_nonneg hωp]
          _ ≤ (listSiftProd ω rest)⁻¹ + ω p * (listSiftProd ω rest)⁻¹ := by
              nlinarith [ih false D, ih true (D / (p : ℝ))]
          _ = (1 + ω p) * (listSiftProd ω rest)⁻¹ := by ring
    calc |rosserV ω sign D (p :: rest)|
        ≤ (1 + ω p) * (listSiftProd ω rest)⁻¹ := hstep
      _ ≤ (1 - ω p)⁻¹ * (listSiftProd ω rest)⁻¹ :=
          mul_le_mul_of_nonneg_right hfactor (inv_nonneg.mpr hP_pos.le)
      _ = (listSiftProd ω (p :: rest))⁻¹ := by
          simp only [listSiftProd, mul_inv]

/-! ## Section 2: Master Buchstab–Mertens Summation-by-Parts Lemmas -/

lemma siftProd_pos_of_linearSieve {ω : ℕ → ℝ} {K : ℝ} (hω : LinearSieveDensity ω K) (z : ℝ) :
    0 < siftProd ω z := by
  unfold siftProd
  exact Finset.prod_pos fun p _ => sub_pos.mpr (hω.lt_one p)

lemma siftProd_two_eq_one (ω : ℕ → ℝ) : siftProd ω 2 = 1 := by
  rw [← listSiftProd_primesLtList, primesLtList_eq_nil_of_le_two le_rfl]
  rfl

/-- Exact splitting of `siftProd` on `[w, z)`:
`siftProd ω w / siftProd ω z = ∏_{w ≤ p < z, p prime} (1 - ω p)⁻¹`. -/
lemma siftProd_div_eq_prod_inv {ω : ℕ → ℝ} {K : ℝ} (hω : LinearSieveDensity ω K)
    {w z : ℝ} (hwz : w ≤ z) :
    siftProd ω w / siftProd ω z =
      ∏ p ∈ (Finset.range (⌊z⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - ω p)⁻¹ := by
  have hPw : 0 < siftProd ω w := siftProd_pos_of_linearSieve hω w
  set S_z := (Finset.range (⌊z⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) < z)
  set S_w := (Finset.range (⌊w⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) < w)
  set S_wz := (Finset.range (⌊z⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z)
  have hdisj : Disjoint S_w S_wz := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rw [Finset.mem_filter] at hp1 hp2
    linarith [hp1.2.2, hp2.2.2.1]
  have hunion : S_w ∪ S_wz = S_z := by
    ext p
    simp only [S_w, S_wz, S_z, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro (⟨_, hpr, hltw⟩ | ⟨hr, hpr, _, hltz⟩)
      · have hltz : (p : ℝ) < z := lt_of_lt_of_le hltw hwz
        refine ⟨?_, hpr, hltz⟩
        by_cases hz : 0 ≤ z
        · exact Nat.lt_succ_of_le (Nat.le_floor (le_of_lt hltz))
        · have : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
          linarith
      · exact ⟨hr, hpr, hltz⟩
    · intro ⟨hr, hpr, hltz⟩
      by_cases hwp : w ≤ (p : ℝ)
      · exact Or.inr ⟨hr, hpr, hwp, hltz⟩
      · have hltw : (p : ℝ) < w := lt_of_not_ge hwp
        refine Or.inl ⟨?_, hpr, hltw⟩
        by_cases hw : 0 ≤ w
        · exact Nat.lt_succ_of_le (Nat.le_floor (le_of_lt hltw))
        · have : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
          linarith
  have hprod_split : siftProd ω z = siftProd ω w * ∏ p ∈ S_wz, (1 - ω p) := by
    change ∏ p ∈ S_z, (1 - ω p) = (∏ p ∈ S_w, (1 - ω p)) * ∏ p ∈ S_wz, (1 - ω p)
    rw [← hunion, Finset.prod_union hdisj]
  rw [hprod_split, div_mul_eq_div_div, div_self hPw.ne', one_div, ← Finset.prod_inv_distrib]

lemma siftProd_ratio_le {ω : ℕ → ℝ} {K : ℝ} (hω : LinearSieveDensity ω K)
    {w z : ℝ} (hw2 : 2 ≤ w) (hwz : w ≤ z) :
    siftProd ω w / siftProd ω z ≤ (Real.log z / Real.log w) * (1 + K / Real.log w) := by
  rw [siftProd_div_eq_prod_inv hω hwz]
  exact hω.mertens_ratio w z hw2 hwz

lemma siftProd_le_mul_ratio {ω : ℕ → ℝ} {K : ℝ} (hω : LinearSieveDensity ω K)
    {w z : ℝ} (hw2 : 2 ≤ w) (hwz : w ≤ z) :
    siftProd ω w ≤ siftProd ω z * ((Real.log z / Real.log w) * (1 + K / Real.log w)) := by
  have hPz := siftProd_pos_of_linearSieve hω z
  exact (div_le_iff₀ hPz).mp (siftProd_ratio_le hω hw2 hwz) |>.trans_eq (mul_comm _ _)

lemma inv_siftProd_le {ω : ℕ → ℝ} {K : ℝ} (hω : LinearSieveDensity ω K)
    {z : ℝ} (hz2 : 2 ≤ z) :
    (siftProd ω z)⁻¹ ≤ (Real.log z / Real.log 2) * (1 + K / Real.log 2) := by
  have h := siftProd_ratio_le hω le_rfl hz2
  rw [siftProd_two_eq_one, one_div] at h
  exact h

/-- Elementary algebraic summation-by-parts identity for any sequences `A : Fin (n + 2) → ℝ`
and `g : Fin (n + 1) → ℝ`. -/
private lemma fin_sum_by_parts :
    ∀ (n : ℕ) (A : Fin (n + 2) → ℝ) (g : Fin (n + 1) → ℝ),
      ∑ k : Fin (n + 1), (A k.castSucc - A k.succ) * g k =
        A 0 * g 0 - A (Fin.last (n + 1)) * g (Fin.last n) +
          ∑ k : Fin n, A k.succ.castSucc * (g k.succ - g k.castSucc) := by
  intro n
  induction n with
  | zero =>
    intro A g
    simp
    ring
  | succ m ih =>
    intro A g
    conv_lhs => rw [Fin.sum_univ_castSucc]
    conv_rhs => rw [Fin.sum_univ_castSucc]
    have hih := ih (fun i => A i.castSucc) (fun i => g i.castSucc)
    simp only [Fin.castSucc_zero, Fin.castSucc_succ] at hih
    have hsum_eq : ∑ k : Fin m, A k.castSucc.succ.castSucc * (g k.castSucc.succ - g k.castSucc.castSucc) =
        ∑ k : Fin m, A k.castSucc.castSucc.succ * (g k.castSucc.succ - g k.castSucc.castSucc) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Fin.castSucc_succ]
    have hlast1 : (Fin.last m).succ = Fin.last (m + 1) := Fin.succ_last m
    have hlast2 : (Fin.last (m + 1)).succ = Fin.last (m + 2) := Fin.succ_last (m + 1)
    rw [hih, ← hsum_eq, hlast1, hlast2]
    ring

/-- Adjacent interval integral telescoping for a sequence `u : Fin (m + 1) → ℝ`. -/
private lemma sum_intervalIntegral_antitone_seq :
    ∀ (m : ℕ) (u : Fin (m + 1) → ℝ) (f : ℝ → ℝ),
      (∀ k : Fin m, IntervalIntegrable f volume (u k.succ) (u k.castSucc)) →
      ∑ k : Fin m, (∫ t in u k.succ..u k.castSucc, f t) =
        ∫ t in u (Fin.last m)..u 0, f t := by
  intro m
  induction m with
  | zero =>
    intro u f _
    simp
  | succ n ih =>
    intro u f hint
    rw [Fin.sum_univ_castSucc]
    have hih := ih (fun i => u i.castSucc) f (fun k => by
      simpa only [Fin.castSucc_succ] using hint k.castSucc)
    simp only [Fin.castSucc_succ, Fin.castSucc_zero] at hih
    rw [hih]
    have hint_left : IntervalIntegrable f volume (u (Fin.last n).castSucc) (u 0) := by
      clear ih hih
      induction n with
      | zero => simp
      | succ r ihr =>
        have hstep : IntervalIntegrable f volume (u (Fin.last (r + 1)).castSucc) (u (Fin.last r).castSucc.castSucc) := by
          have h0 := hint (Fin.last r).castSucc
          have h1 : (Fin.last r).castSucc.succ = (Fin.last (r + 1)).castSucc := by
            rw [← Fin.castSucc_succ, Fin.succ_last]
          rwa [h1] at h0
        have hprev := ihr (fun i => u i.castSucc) (fun k => by
          simpa only [Fin.castSucc_succ] using hint k.castSucc)
        exact hstep.trans (by simpa only [Fin.castSucc_zero] using hprev)
    have hint_right : IntervalIntegrable f volume (u (Fin.last (n + 1))) (u (Fin.last n).castSucc) := by
      have h0 := hint (Fin.last n)
      rwa [Fin.succ_last] at h0
    have hadd := intervalIntegral.integral_add_adjacent_intervals hint_right hint_left
    rw [add_comm] at hadd
    exact hadd

/-- Ascending list of primes in `[w, z)`. -/
def primesIcoAsc (w z : ℝ) : List ℕ :=
  (primesIcoList w z).reverse

lemma mem_primesIcoAsc {w z : ℝ} {p : ℕ} :
    p ∈ primesIcoAsc w z ↔ p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z := by
  unfold primesIcoAsc primesIcoList
  rw [List.mem_reverse, List.mem_filter, decide_eq_true_eq, mem_primesLtList]
  tauto

lemma primesIcoAsc_pairwise_lt (w z : ℝ) : (primesIcoAsc w z).Pairwise (· < ·) := by
  unfold primesIcoAsc primesIcoList
  rw [List.pairwise_reverse]
  exact ((primesLtList_pairwise_gt z).filter _).imp fun h => h

lemma primesIcoAsc_nodup (w z : ℝ) : (primesIcoAsc w z).Nodup :=
  (primesIcoAsc_pairwise_lt w z).imp fun h => ne_of_lt h

lemma sum_primesIcoList_eq_fin (w z : ℝ) (h : ℕ → ℝ) :
    ∑ p ∈ (primesIcoList w z).toFinset, h p =
      ∑ i : Fin (primesIcoAsc w z).length, h (primesIcoAsc w z)[i] := by
  have hto : (primesIcoList w z).toFinset = (primesIcoAsc w z).toFinset := by
    ext x; simp [primesIcoAsc]
  rw [hto, List.sum_toFinset _ (primesIcoAsc_nodup w z), ← List.sum_ofFn]
  congr 1
  exact List.ext_getElem (by simp) fun i hi₁ hi₂ => by simp

/-- Log-ratio shift identity: `log (D / p) / log p = log D / log p - 1`. -/
lemma log_div_div_log_eq {D p : ℝ} (hD : 0 < D) (hp1 : 1 < p) :
    Real.log (D / p) / Real.log p = Real.log D / Real.log p - 1 := by
  have hp0 : 0 < p := zero_lt_one.trans hp1
  have hlp : Real.log p ≠ 0 := (Real.log_pos hp1).ne'
  rw [Real.log_div hD.ne' hp0.ne', sub_div, div_self hlp]

/-- Packaged `siftProd` and `log D / log p` sequence data on `[w, z)` when `primesIcoAsc w z`
has length `n + 1`. -/
private lemma primesIcoAsc_siftProd_data {ω : ℕ → ℝ} {K : ℝ} (hω : LinearSieveDensity ω K)
    {D w z : ℝ} (hw2 : 2 ≤ w) (hwz : w ≤ z) (hzD : z < D)
    {n : ℕ} (hm : (primesIcoAsc w z).length = n + 1) :
    ∃ (P u : Fin (n + 2) → ℝ),
      P 0 = siftProd ω w ∧
      P (Fin.last (n + 1)) = siftProd ω z ∧
      u (Fin.last (n + 1)) = Real.log D / Real.log z ∧
      u 0 ≤ Real.log D / Real.log w ∧
      (∀ k : Fin (n + 1), Real.log D / Real.log z < u k.castSucc) ∧
      (∀ k : Fin (n + 1), u k.succ < u k.castSucc) ∧
      (∀ k : Fin (n + 1),
        P k.castSucc ≤ siftProd ω z * ((1 + K / Real.log w) * (u k.castSucc / (Real.log D / Real.log z)))) ∧
      (∀ G : ℝ → ℝ,
        ∑ p ∈ (primesIcoList w z).toFinset, ω p * siftProd ω (p : ℝ) * G (Real.log D / Real.log (p : ℝ) - 1) =
          ∑ k : Fin (n + 1), (P k.castSucc - P k.succ) * G (u k.castSucc - 1)) := by
  have hL_pw := primesIcoAsc_pairwise_lt w z
  have hL_props : ∀ i : Fin (primesIcoAsc w z).length,
      (primesIcoAsc w z)[i].Prime ∧ w ≤ ((primesIcoAsc w z)[i] : ℝ) ∧ ((primesIcoAsc w z)[i] : ℝ) < z :=
    fun i => mem_primesIcoAsc.mp (List.getElem_mem i.2)
  have hlw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlD : 0 < Real.log D := Real.log_pos (by linarith)
  set s := Real.log D / Real.log z with hs_def
  set C := 1 + K / Real.log w with hC_def
  have hfirst : siftProd ω w = siftProd ω ((primesIcoAsc w z)[0]'(by omega) : ℝ) := by
    have h0 : 0 < (primesIcoAsc w z).length := by omega
    have hw_le : w ≤ ((primesIcoAsc w z)[0]'h0 : ℝ) := (hL_props ⟨0, h0⟩).2.1
    rw [siftProd_buchstab ω hw_le]
    have hempty : (primesIcoList w ((primesIcoAsc w z)[0]'h0 : ℝ)).toFinset = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro p hp
      rw [List.mem_toFinset] at hp
      unfold primesIcoList at hp
      rw [List.mem_filter, decide_eq_true_eq, mem_primesLtList] at hp
      have hpL : p ∈ primesIcoAsc w z := mem_primesIcoAsc.mpr
        ⟨hp.1.1, hp.2, lt_trans hp.1.2 (hL_props ⟨0, h0⟩).2.2⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hpL
      have h0le : (primesIcoAsc w z)[0]'h0 ≤ (primesIcoAsc w z)[j]'hj := by
        by_cases hj0 : j = 0
        · subst hj0; exact le_rfl
        · exact le_of_lt ((List.pairwise_iff_getElem.mp hL_pw) 0 j h0 hj (by omega))
      exact not_lt.mpr (by exact_mod_cast h0le : ((primesIcoAsc w z)[0]'h0 : ℝ) ≤ ((primesIcoAsc w z)[j]'hj : ℝ)) hp.1.2
    rw [hempty, Finset.sum_empty, sub_zero]
  have hdrop : ∀ i : Fin (primesIcoAsc w z).length,
      siftProd ω ((primesIcoAsc w z)[i] : ℝ) -
        (if h : i.1 + 1 < (primesIcoAsc w z).length then siftProd ω ((primesIcoAsc w z)[i.1 + 1]'h : ℝ) else siftProd ω z) =
      ω (primesIcoAsc w z)[i] * siftProd ω ((primesIcoAsc w z)[i] : ℝ) := by
    intro i
    split_ifs with hnext
    · have hlt_nat : (primesIcoAsc w z)[i] < (primesIcoAsc w z)[i.1 + 1]'hnext :=
        (List.pairwise_iff_getElem.mp hL_pw) i.1 (i.1 + 1) i.2 hnext (by omega)
      have hsub := siftProd_buchstab ω (by exact_mod_cast hlt_nat.le :
        ((primesIcoAsc w z)[i] : ℝ) ≤ ((primesIcoAsc w z)[i.1 + 1]'hnext : ℝ))
      rw [hsub]
      have hsing : (primesIcoList ((primesIcoAsc w z)[i] : ℝ) ((primesIcoAsc w z)[i.1 + 1]'hnext : ℝ)).toFinset =
          {(primesIcoAsc w z)[i]} := by
        ext p
        rw [List.mem_toFinset, Finset.mem_singleton]
        unfold primesIcoList
        rw [List.mem_filter, decide_eq_true_eq, mem_primesLtList]
        constructor
        · rintro ⟨⟨hpr, hlt⟩, hge⟩
          have hpL : p ∈ primesIcoAsc w z := mem_primesIcoAsc.mpr
            ⟨hpr, le_trans (hL_props i).2.1 hge, lt_trans hlt (hL_props ⟨i.1 + 1, hnext⟩).2.2⟩
          obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hpL
          have hj_ge : i.1 ≤ j := by
            by_contra hltj
            have := (List.pairwise_iff_getElem.mp hL_pw) j i.1 hj i.2 (by omega)
            exact not_lt.mpr hge (by exact_mod_cast this)
          have hj_lt : j < i.1 + 1 := by
            by_contra hgej
            have hle_j : (primesIcoAsc w z)[i.1 + 1]'hnext ≤ (primesIcoAsc w z)[j]'hj := by
              by_cases heq : i.1 + 1 = j
              · subst heq; exact le_rfl
              · exact le_of_lt ((List.pairwise_iff_getElem.mp hL_pw) (i.1 + 1) j hnext hj (by omega))
            exact not_lt.mpr (by exact_mod_cast hle_j) hlt
          have hjeq : j = i.1 := by omega
          subst hjeq; rfl
        · rintro rfl
          exact ⟨⟨(hL_props i).1, by exact_mod_cast hlt_nat⟩, le_rfl⟩
      rw [hsing, Finset.sum_singleton]; ring
    · rw [siftProd_buchstab ω (hL_props i).2.2.le]
      have hsing : (primesIcoList ((primesIcoAsc w z)[i] : ℝ) z).toFinset = {(primesIcoAsc w z)[i]} := by
        ext p
        rw [List.mem_toFinset, Finset.mem_singleton]
        unfold primesIcoList
        rw [List.mem_filter, decide_eq_true_eq, mem_primesLtList]
        constructor
        · rintro ⟨⟨hpr, hlt⟩, hge⟩
          have hpL : p ∈ primesIcoAsc w z := mem_primesIcoAsc.mpr ⟨hpr, le_trans (hL_props i).2.1 hge, hlt⟩
          obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hpL
          have hj_ge : i.1 ≤ j := by
            by_contra hltj
            have := (List.pairwise_iff_getElem.mp hL_pw) j i.1 hj i.2 (by omega)
            exact not_lt.mpr hge (by exact_mod_cast this)
          have hjeq : j = i.1 := by omega
          subst hjeq; rfl
        · rintro rfl
          exact ⟨⟨(hL_props i).1, (hL_props i).2.2⟩, le_rfl⟩
      rw [hsing, Finset.sum_singleton]; ring
  let P : Fin (n + 2) → ℝ := fun k =>
    if hk : k.1 < n + 1 then siftProd ω ((primesIcoAsc w z)[k.1]'(by omega) : ℝ) else siftProd ω z
  let u : Fin (n + 2) → ℝ := fun k =>
    if hk : k.1 < n + 1 then Real.log D / Real.log ((primesIcoAsc w z)[k.1]'(by omega) : ℝ) else s
  have hu_gt : ∀ k : Fin (n + 1), s < u k.castSucc := by
    intro k
    have hk : k.1 < n + 1 := k.2
    have hu_k : u k.castSucc = Real.log D / Real.log ((primesIcoAsc w z)[k.1]'(by omega) : ℝ) := by
      simp only [u, Fin.val_castSucc, hk, ↓reduceDIte]
    rw [hu_k, hs_def]
    have hprop := mem_primesIcoAsc.mp (List.getElem_mem (by omega : k.1 < (primesIcoAsc w z).length))
    have hlp : 0 < Real.log ((primesIcoAsc w z)[k.1]'(by omega) : ℝ) := Real.log_pos (by linarith [hprop.2.1])
    exact div_lt_div_of_pos_left hlD hlp (Real.log_lt_log (by linarith [hprop.2.1]) hprop.2.2)
  refine ⟨P, u, ?_, ?_, ?_, ?_, hu_gt, ?_, ?_, ?_⟩
  · simp only [P, Fin.val_zero, Nat.zero_lt_succ, ↓reduceDIte]; exact hfirst.symm
  · simp [P]
  · simp [u]
  · simp only [u, Fin.val_zero, Nat.zero_lt_succ, ↓reduceDIte]
    have hprop := mem_primesIcoAsc.mp (List.getElem_mem (by omega : 0 < (primesIcoAsc w z).length))
    exact div_le_div_of_nonneg_left hlD.le hlw (Real.log_le_log (by linarith) hprop.2.1)
  · intro k
    have hk : k.1 < n + 1 := k.2
    have hu_k : u k.castSucc = Real.log D / Real.log ((primesIcoAsc w z)[k.1]'(by omega) : ℝ) := by
      simp only [u, Fin.val_castSucc, hk, ↓reduceDIte]
    by_cases hnext : k.1 + 1 < n + 1
    · have hu_next : u k.succ = Real.log D / Real.log ((primesIcoAsc w z)[k.1 + 1]'(by omega) : ℝ) := by
        simp only [u, Fin.val_succ, hnext, ↓reduceDIte]
      rw [hu_k, hu_next]
      have hlt_nat : (primesIcoAsc w z)[k.1]'(by omega) < (primesIcoAsc w z)[k.1 + 1]'(by omega) :=
        (List.pairwise_iff_getElem.mp hL_pw) k.1 (k.1 + 1) (by omega) (by omega) (by omega)
      have hprop := mem_primesIcoAsc.mp (List.getElem_mem (by omega : k.1 < (primesIcoAsc w z).length))
      have hlp : 0 < Real.log ((primesIcoAsc w z)[k.1]'(by omega) : ℝ) := Real.log_pos (by linarith [hprop.2.1])
      exact div_lt_div_of_pos_left hlD hlp
        (Real.log_lt_log (by linarith [hprop.2.1]) (Nat.cast_lt.mpr hlt_nat))
    · have hu_next : u k.succ = s := by simp only [u, Fin.val_succ, hnext, ↓reduceDIte]
      rw [hu_next]
      exact hu_gt k
  · intro k
    have hk : k.1 < n + 1 := k.2
    have hP_k : P k.castSucc = siftProd ω ((primesIcoAsc w z)[k.1]'(by omega) : ℝ) := by
      simp only [P, Fin.val_castSucc, hk, ↓reduceDIte]
    have hu_k : u k.castSucc = Real.log D / Real.log ((primesIcoAsc w z)[k.1]'(by omega) : ℝ) := by
      simp only [u, Fin.val_castSucc, hk, ↓reduceDIte]
    rw [hP_k, hu_k]
    have hprop := mem_primesIcoAsc.mp (List.getElem_mem (by omega : k.1 < (primesIcoAsc w z).length))
    have hp2 : 2 ≤ ((primesIcoAsc w z)[k.1]'(by omega) : ℝ) := le_trans hw2 hprop.2.1
    have hlp : 0 < Real.log ((primesIcoAsc w z)[k.1]'(by omega) : ℝ) := Real.log_pos (by linarith)
    have hrat := siftProd_le_mul_ratio hω hp2 hprop.2.2.le
    have hC_le : 1 + K / Real.log ((primesIcoAsc w z)[k.1]'(by omega) : ℝ) ≤ C := by
      rw [hC_def]; gcongr
      · linarith [hω.K_ge_one]
      · exact hprop.2.1
    have hu_div_s : Real.log D / Real.log ((primesIcoAsc w z)[k.1]'(by omega) : ℝ) / s =
        Real.log z / Real.log ((primesIcoAsc w z)[k.1]'(by omega) : ℝ) := by
      rw [hs_def]; field_simp [hlD.ne', hlz.ne', hlp.ne']
    rw [hu_div_s]
    have hPz := siftProd_pos_of_linearSieve hω z
    have hrat_nn : 0 ≤ Real.log z / Real.log ((primesIcoAsc w z)[k.1]'(by omega) : ℝ) :=
      div_nonneg hlz.le hlp.le
    calc siftProd ω ((primesIcoAsc w z)[k.1]'(by omega) : ℝ)
        ≤ siftProd ω z * ((Real.log z / Real.log ((primesIcoAsc w z)[k.1]'(by omega) : ℝ)) *
            (1 + K / Real.log ((primesIcoAsc w z)[k.1]'(by omega) : ℝ))) := hrat
      _ ≤ siftProd ω z * ((Real.log z / Real.log ((primesIcoAsc w z)[k.1]'(by omega) : ℝ)) * C) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hC_le hrat_nn) hPz.le
      _ = siftProd ω z * (C * (Real.log z / Real.log ((primesIcoAsc w z)[k.1]'(by omega) : ℝ))) := by ring
  · intro G
    rw [sum_primesIcoList_eq_fin]
    refine Finset.sum_nbij' (fun i => ⟨i.1, by omega⟩) (fun k => ⟨k.1, by omega⟩)
      (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _)
      (fun _ _ => rfl) (fun _ _ => rfl) fun i _ => ?_
    have hi : i.1 < n + 1 := by omega
    have hd := hdrop i
    let k : Fin (n + 1) := ⟨i.1, hi⟩
    have hPdiff : P k.castSucc - P k.succ =
        ω (primesIcoAsc w z)[i] * siftProd ω ((primesIcoAsc w z)[i] : ℝ) := by
      simp only [P, k, Fin.val_castSucc, Fin.val_succ, hi, ↓reduceDIte]
      by_cases hnext : i.1 + 1 < n + 1
      · have hnext' : i.1 + 1 < (primesIcoAsc w z).length := by omega
        simp only [hnext, ↓reduceDIte]
        rw [dif_pos hnext'] at hd; exact hd
      · have hnext' : ¬ (i.1 + 1 < (primesIcoAsc w z).length) := by omega
        simp only [hnext, ↓reduceDIte]
        rw [dif_neg hnext'] at hd; exact hd
    have hu_eq : u k.castSucc = Real.log D / Real.log ((primesIcoAsc w z)[i] : ℝ) := by
      simp only [u, k, Fin.val_castSucc, hi, ↓reduceDIte]; rfl
    change ω (primesIcoAsc w z)[i] * siftProd ω ((primesIcoAsc w z)[i] : ℝ) *
        G (Real.log D / Real.log ((primesIcoAsc w z)[i] : ℝ) - 1) =
      (P k.castSucc - P k.succ) * G (u k.castSucc - 1)
    rw [hPdiff, hu_eq]

/-- **General Antitone Summation-by-Parts Lemma**:
For any `hω : LinearSieveDensity ω K`, `2 ≤ w ≤ z < D`, and any nonnegative antitone `G` on `(0, ∞)`:
```
∑_{w ≤ p < z} ω(p) * P(p) * G(log D / log p - 1)
  ≤ P(z) * ( (1 + K / log w) * (1 / s) * ∫_s^{s_w} G(u - 1) du + (K / log w) * G(s - 1) )
```
where `s = log D / log z` and `s_w = log D / log w`. -/
lemma sum_omega_siftProd_mul_antitone_le {ω : ℕ → ℝ} {K : ℝ} (hω : LinearSieveDensity ω K)
    {D w z : ℝ} (hw2 : 2 ≤ w) (hwz : w ≤ z) (hzD : z < D)
    {G : ℝ → ℝ} (hG_nn : ∀ t, 0 < t → 0 ≤ G t) (hG_anti : AntitoneOn G (Set.Ioi 0)) :
    ∑ p ∈ (primesIcoList w z).toFinset,
        ω p * siftProd ω (p : ℝ) * G (Real.log D / Real.log (p : ℝ) - 1) ≤
      siftProd ω z *
        ((1 + K / Real.log w) * (Real.log z / Real.log D) *
            (∫ u in (Real.log D / Real.log z)..(Real.log D / Real.log w), G (u - 1)) +
          (K / Real.log w) * G (Real.log D / Real.log z - 1)) := by
  have hPz : 0 < siftProd ω z := siftProd_pos_of_linearSieve hω z
  have hlw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlD : 0 < Real.log D := Real.log_pos (by linarith)
  have hs_gt1 : 1 < Real.log D / Real.log z := (one_lt_div hlz).mpr (Real.log_lt_log (by linarith) hzD)
  have hs_pos : 0 < Real.log D / Real.log z := zero_lt_one.trans hs_gt1
  have hsw_ge : Real.log D / Real.log z ≤ Real.log D / Real.log w :=
    div_le_div_of_nonneg_left hlD.le hlw (Real.log_le_log (by linarith) hwz)
  set s := Real.log D / Real.log z with hs_def
  set sw := Real.log D / Real.log w with hsw_def
  set C := 1 + K / Real.log w with hC_def
  have hK_nn : 0 ≤ K / Real.log w := div_nonneg (by linarith [hω.K_ge_one]) hlw.le
  have hG_shift_anti : AntitoneOn (fun u => G (u - 1)) (Set.Ioi 1) := by
    intro a ha b hb hab
    exact hG_anti (Set.mem_Ioi.mpr (sub_pos.mpr ha)) (Set.mem_Ioi.mpr (sub_pos.mpr hb)) (by linarith)
  have hint_all : ∀ a b : ℝ, 1 < a → a ≤ b → IntervalIntegrable (fun u => G (u - 1)) volume a b := by
    intro a b ha hab
    exact (hG_shift_anti.mono (by
      rw [Set.uIcc_of_le hab]; intro t ht; exact lt_of_lt_of_le ha ht.1)).intervalIntegrable
  by_cases hm0 : (primesIcoAsc w z).length = 0
  · rw [sum_primesIcoList_eq_fin]
    have hemp : ∑ i : Fin (primesIcoAsc w z).length,
        ω (primesIcoAsc w z)[i] * siftProd ω ((primesIcoAsc w z)[i] : ℝ) *
          G (Real.log D / Real.log ((primesIcoAsc w z)[i] : ℝ) - 1) = 0 :=
      Finset.sum_eq_zero fun i _ => absurd i.2 (by omega)
    rw [hemp]
    have hint_nn : 0 ≤ ∫ u in s..sw, G (u - 1) :=
      intervalIntegral.integral_nonneg hsw_ge fun u hu => hG_nn (u - 1) (by linarith [hu.1])
    have hGs_nn : 0 ≤ G (s - 1) := hG_nn (s - 1) (by linarith)
    have hs_inv_nn : 0 ≤ Real.log z / Real.log D := div_nonneg hlz.le hlD.le
    exact mul_nonneg hPz.le (add_nonneg (mul_nonneg (mul_nonneg (by linarith) hs_inv_nn) hint_nn)
      (mul_nonneg hK_nn hGs_nn))
  · obtain ⟨n, hm⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    obtain ⟨P, u, _, hPm, hum, hu_le_sw, hu_gt_s, hu_dec, hP_bd, hsum_G⟩ :=
      primesIcoAsc_siftProd_data hω hw2 hwz hzD hm
    set g : Fin (n + 1) → ℝ := fun k => G (u k.castSucc - 1)
    have hg_nn : ∀ k : Fin (n + 1), 0 ≤ g k := fun k => hG_nn _ (by linarith [hu_gt_s k])
    have hg_inc : ∀ k : Fin n, g k.castSucc ≤ g k.succ := fun k => by
      have hdec := hu_dec k.castSucc
      rw [← Fin.castSucc_succ] at hdec
      exact hG_anti (Set.mem_Ioi.mpr (by linarith [hu_gt_s k.succ]))
        (Set.mem_Ioi.mpr (by linarith [hu_gt_s k.castSucc])) (by linarith)
    have hg_last_le : g (Fin.last n) ≤ G (s - 1) :=
      hG_anti (Set.mem_Ioi.mpr (by linarith)) (Set.mem_Ioi.mpr (by linarith [hu_gt_s (Fin.last n)]))
        (by linarith [hu_gt_s (Fin.last n)])
    rw [hsum_G G, fin_sum_by_parts n P g, hPm]
    have hstep1 :
        P 0 * g 0 - siftProd ω z * g (Fin.last n) +
          ∑ k : Fin n, P k.succ.castSucc * (g k.succ - g k.castSucc) ≤
        siftProd ω z * (C / s) *
          (u 0 * g 0 - s * g (Fin.last n) +
            ∑ k : Fin n, u k.succ.castSucc * (g k.succ - g k.castSucc)) +
          siftProd ω z * ((C - 1) * g (Fin.last n)) := by
      have h0 : P 0 * g 0 ≤ siftProd ω z * (C * (u 0 / s)) * g 0 :=
        mul_le_mul_of_nonneg_right (hP_bd 0) (hg_nn 0)
      have hsum : ∑ k : Fin n, P k.succ.castSucc * (g k.succ - g k.castSucc) ≤
          ∑ k : Fin n, (siftProd ω z * (C * (u k.succ.castSucc / s))) * (g k.succ - g k.castSucc) :=
        Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_right (hP_bd k.succ) (sub_nonneg.mpr (hg_inc k))
      have hpull : ∑ k : Fin n, (siftProd ω z * (C * (u k.succ.castSucc / s))) * (g k.succ - g k.castSucc) =
          siftProd ω z * (C / s) * ∑ k : Fin n, u k.succ.castSucc * (g k.succ - g k.castSucc) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
      have hfact :
          siftProd ω z * (C * (u 0 / s)) * g 0 - siftProd ω z * g (Fin.last n) +
            siftProd ω z * (C / s) * ∑ k : Fin n, u k.succ.castSucc * (g k.succ - g k.castSucc) =
          siftProd ω z * (C / s) *
            (u 0 * g 0 - s * g (Fin.last n) +
              ∑ k : Fin n, u k.succ.castSucc * (g k.succ - g k.castSucc)) +
            siftProd ω z * ((C - 1) * g (Fin.last n)) := by
        field_simp [hs_pos.ne']; ring
      linarith
    have hu_tel :
        u 0 * g 0 - s * g (Fin.last n) +
          ∑ k : Fin n, u k.succ.castSucc * (g k.succ - g k.castSucc) =
        ∑ k : Fin (n + 1), (u k.castSucc - u k.succ) * g k := by
      rw [hs_def, ← hum, ← fin_sum_by_parts n u g]
    have hu_succ_gt1 : ∀ k : Fin (n + 1), 1 < u k.succ := fun k => by
      by_cases hlast : k = Fin.last n
      · subst hlast; rw [Fin.succ_last, hum]; exact hs_gt1
      · have hlt : k.1 + 1 < n + 1 := by
          have := k.2; have : k.1 ≠ n := fun h => hlast (Fin.ext h); omega
        have heq : k.succ = (⟨k.1 + 1, hlt⟩ : Fin (n + 1)).castSucc := rfl
        rw [heq]; exact lt_trans hs_gt1 (hu_gt_s ⟨k.1 + 1, hlt⟩)
    have hriem : ∑ k : Fin (n + 1), (u k.castSucc - u k.succ) * g k ≤ ∫ t in s..sw, G (t - 1) := by
      have hterm : ∀ k : Fin (n + 1),
          (u k.castSucc - u k.succ) * g k ≤ ∫ t in u k.succ..u k.castSucc, G (t - 1) := by
        intro k
        have hconst : (u k.castSucc - u k.succ) * g k = ∫ _t in u k.succ..u k.castSucc, g k := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
        rw [hconst]
        refine intervalIntegral.integral_mono_on (hu_dec k).le intervalIntegrable_const
          (hint_all _ _ (hu_succ_gt1 k) (hu_dec k).le) fun t ht => ?_
        exact hG_anti (Set.mem_Ioi.mpr (by linarith [ht.1, hu_succ_gt1 k]))
          (Set.mem_Ioi.mpr (by linarith [hu_gt_s k])) (by linarith [ht.2])
      have hsum_int : ∑ k : Fin (n + 1), (∫ t in u k.succ..u k.castSucc, G (t - 1)) =
          ∫ t in s..u 0, G (t - 1) := by
        rw [hs_def, ← hum]
        exact sum_intervalIntegral_antitone_seq (n + 1) u (fun t => G (t - 1))
          fun k => hint_all _ _ (hu_succ_gt1 k) (hu_dec k).le
      have hu0_gt : s < u 0 := by simpa [Fin.castSucc_zero, hs_def] using hu_gt_s 0
      have htail_nn : 0 ≤ ∫ t in u 0..sw, G (t - 1) :=
        intervalIntegral.integral_nonneg hu_le_sw fun t ht =>
          hG_nn (t - 1) (by linarith [ht.1, hu0_gt])
      have hsplit_int := intervalIntegral.integral_add_adjacent_intervals
        (hint_all s (u 0) hs_gt1 hu0_gt.le)
        (hint_all (u 0) sw (lt_trans hs_gt1 hu0_gt) hu_le_sw)
      calc ∑ k : Fin (n + 1), (u k.castSucc - u k.succ) * g k
          ≤ ∑ k : Fin (n + 1), (∫ t in u k.succ..u k.castSucc, G (t - 1)) :=
            Finset.sum_le_sum fun k _ => hterm k
        _ = ∫ t in s..u 0, G (t - 1) := hsum_int
        _ ≤ ∫ t in s..sw, G (t - 1) := by linarith
    have hC_sub : C - 1 = K / Real.log w := by rw [hC_def]; ring
    have hdiv_s : C / s = C * (Real.log z / Real.log D) := by
      rw [hs_def]; field_simp [hlD.ne', hlz.ne']
    have hCs_nn : 0 ≤ siftProd ω z * (C / s) := by
      have : 0 ≤ C := by linarith
      positivity
    calc P 0 * g 0 - siftProd ω z * g (Fin.last n) +
            ∑ k : Fin n, P k.succ.castSucc * (g k.succ - g k.castSucc)
        ≤ siftProd ω z * (C / s) * (∫ t in s..sw, G (t - 1)) +
            siftProd ω z * ((C - 1) * g (Fin.last n)) := by
          rw [hu_tel] at hstep1
          have hmul := mul_le_mul_of_nonneg_left hriem hCs_nn
          linarith
      _ ≤ siftProd ω z * (C / s) * (∫ t in s..sw, G (t - 1)) +
            siftProd ω z * ((K / Real.log w) * G (s - 1)) := by
          rw [hC_sub]; gcongr
      _ = siftProd ω z * (C * (Real.log z / Real.log D) * (∫ t in s..sw, G (t - 1)) +
            (K / Real.log w) * G (s - 1)) := by rw [hdiv_s]; ring

/-- **Master Buchstab–Mertens Lemma (M⁺)** (Upper Sieve `s ≥ 3`):
```
P(w) * F(s_w) - ∑_{w ≤ p < z} ω(p) * P(p) * f(log D / log p - 1)
  ≤ P(z) * (F(s) + (K / log w) * F 3)
```
with ZERO smoothness assumptions beyond `LinearSievePair F f`! -/
lemma master_buchstab_upper {ω : ℕ → ℝ} {K : ℝ} (hω : LinearSieveDensity ω K)
    {F f : ℝ → ℝ} (hFf : LinearSievePair F f)
    {D w z : ℝ} (hw2 : 2 ≤ w) (hwz : w ≤ z) (hz3 : z ^ 3 ≤ D) :
    siftProd ω w * F (Real.log D / Real.log w) -
      ∑ p ∈ (primesIcoList w z).toFinset,
        ω p * siftProd ω (p : ℝ) * f (Real.log D / Real.log (p : ℝ) - 1) ≤
      siftProd ω z * (F (Real.log D / Real.log z) + (K / Real.log w) * F 3) := by
  have hPz : 0 < siftProd ω z := siftProd_pos_of_linearSieve hω z
  have hz2 : 2 ≤ z := hw2.trans hwz
  have hz0 : 0 < z := by linarith
  have hlw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hzD : z < D := by
    have hsq : 4 ≤ z * z := by nlinarith
    have hcube : z ^ 3 = z * z * z := by ring
    nlinarith
  have hlD : 0 < Real.log D := Real.log_pos (by linarith)
  have hs_ge3 : 3 ≤ Real.log D / Real.log z := by
    rw [le_div_iff₀ hlz]
    have hlog3 : 3 * Real.log z = Real.log (z ^ 3) := by rw [Real.log_pow]; ring
    rw [hlog3]
    exact Real.log_le_log (pow_pos hz0 3) hz3
  have hs_pos : 0 < Real.log D / Real.log z := by linarith
  have hsw_ge : Real.log D / Real.log z ≤ Real.log D / Real.log w :=
    div_le_div_of_nonneg_left hlD.le hlw (Real.log_le_log (by linarith) hwz)
  set s := Real.log D / Real.log z with hs_def
  set sw := Real.log D / Real.log w with hsw_def
  set C := 1 + K / Real.log w with hC_def
  have hK_nn : 0 ≤ K / Real.log w := div_nonneg (by linarith [hω.K_ge_one]) hlw.le
  have hC_ge1 : 1 ≤ C := by linarith
  have hF3_pos : 0 < F 3 := lt_of_lt_of_le zero_lt_one (hFf.one_le_F 3 (by norm_num))
  by_cases hm0 : (primesIcoAsc w z).length = 0
  · rw [sum_primesIcoList_eq_fin]
    have hemp : ∑ i : Fin (primesIcoAsc w z).length,
        ω (primesIcoAsc w z)[i] * siftProd ω ((primesIcoAsc w z)[i] : ℝ) *
          f (Real.log D / Real.log ((primesIcoAsc w z)[i] : ℝ) - 1) = 0 :=
      Finset.sum_eq_zero fun i _ => absurd i.2 (by omega)
    rw [hemp, sub_zero]
    have hempty : (primesIcoList w z).toFinset = ∅ := by
      have : (primesIcoList w z).length = 0 := by simpa [primesIcoAsc] using hm0
      rw [List.length_eq_zero_iff] at this; simp [this]
    have hPw_eq : siftProd ω w = siftProd ω z := by
      have hb := siftProd_buchstab ω hwz
      rw [hempty, Finset.sum_empty, sub_zero] at hb; exact hb.symm
    rw [hPw_eq]
    have hF_le : F sw ≤ F s :=
      hFf.F_antitone (Set.mem_Ioi.mpr hs_pos) (Set.mem_Ioi.mpr (lt_of_lt_of_le hs_pos hsw_ge)) hsw_ge
    have hKF_nn : 0 ≤ (K / Real.log w) * F 3 := mul_nonneg hK_nn hF3_pos.le
    nlinarith
  · obtain ⟨n, hm⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    obtain ⟨P, u, hP0, hPm, hum, hu_le_sw, hu_gt_s, hu_dec, hP_bd, hsum_f⟩ :=
      primesIcoAsc_siftProd_data hω hw2 hwz hzD hm
    set fk : Fin (n + 1) → ℝ := fun k => f (u k.castSucc - 1)
    have hu0_gt : s < u 0 := by simpa [Fin.castSucc_zero, hs_def] using hu_gt_s 0
    have hfk_dec : ∀ k : Fin n, fk k.succ ≤ fk k.castSucc := fun k => by
      have hdec := hu_dec k.castSucc
      rw [← Fin.castSucc_succ] at hdec
      exact hFf.f_monotone (Set.mem_Ioi.mpr (by linarith [hu_gt_s k.succ]))
        (Set.mem_Ioi.mpr (by linarith [hu_gt_s k.castSucc])) (by linarith)
    have hfk_nn : ∀ k : Fin (n + 1), 0 ≤ fk k := fun k => hFf.f_nonneg _ (by linarith [hu_gt_s k])
    have hfk_le1 : ∀ k : Fin (n + 1), fk k ≤ 1 := fun k => hFf.f_le_one _ (by linarith [hu_gt_s k])
    rw [hsum_f f, ← hP0, fin_sum_by_parts n P fk, hPm]
    have hF_sw_le : F sw ≤ F (u 0) :=
      hFf.F_antitone (Set.mem_Ioi.mpr (by linarith))
        (Set.mem_Ioi.mpr (by linarith)) hu_le_sw
    have hP0_nn : 0 ≤ P 0 := by rw [hP0]; exact (siftProd_pos_of_linearSieve hω w).le
    have hcoeff0 : 0 ≤ F (u 0) - fk 0 := by
      linarith [hFf.one_le_F (u 0) (by linarith), hfk_le1 0]
    have hstep1 :
        P 0 * F sw - (P 0 * fk 0 - siftProd ω z * fk (Fin.last n) +
            ∑ k : Fin n, P k.succ.castSucc * (fk k.succ - fk k.castSucc)) ≤
        siftProd ω z * (C / s) *
            (u 0 * F (u 0) - (u 0 * fk 0 - s * fk (Fin.last n) +
              ∑ k : Fin n, u k.succ.castSucc * (fk k.succ - fk k.castSucc))) := by
      have h0 : P 0 * (F (u 0) - fk 0) ≤ siftProd ω z * (C * (u 0 / s)) * (F (u 0) - fk 0) :=
        mul_le_mul_of_nonneg_right (hP_bd 0) hcoeff0
      have hsum : ∑ k : Fin n, P k.succ.castSucc * (fk k.castSucc - fk k.succ) ≤
          ∑ k : Fin n, (siftProd ω z * (C * (u k.succ.castSucc / s))) * (fk k.castSucc - fk k.succ) :=
        Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_right (hP_bd k.succ) (sub_nonneg.mpr (hfk_dec k))
      have hneg_sum : -(∑ k : Fin n, P k.succ.castSucc * (fk k.succ - fk k.castSucc)) =
          ∑ k : Fin n, P k.succ.castSucc * (fk k.castSucc - fk k.succ) := by
        rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun k _ => by ring
      have hneg_u : -(∑ k : Fin n, u k.succ.castSucc * (fk k.succ - fk k.castSucc)) =
          ∑ k : Fin n, u k.succ.castSucc * (fk k.castSucc - fk k.succ) := by
        rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun k _ => by ring
      have hpull : ∑ k : Fin n, (siftProd ω z * (C * (u k.succ.castSucc / s))) * (fk k.castSucc - fk k.succ) =
          siftProd ω z * (C / s) * ∑ k : Fin n, u k.succ.castSucc * (fk k.castSucc - fk k.succ) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
      have hdrop : siftProd ω z * fk (Fin.last n) ≤ siftProd ω z * C * fk (Fin.last n) := by
        have h1 := hfk_nn (Fin.last n)
        have h2 : siftProd ω z ≤ siftProd ω z * C := by nlinarith
        exact mul_le_mul_of_nonneg_right h2 h1
      have hcomb :
          siftProd ω z * (C * (u 0 / s)) * (F (u 0) - fk 0) +
            siftProd ω z * (C / s) * ∑ k : Fin n, u k.succ.castSucc * (fk k.castSucc - fk k.succ) +
            siftProd ω z * C * fk (Fin.last n) =
          siftProd ω z * (C / s) *
            (u 0 * F (u 0) - (u 0 * fk 0 - s * fk (Fin.last n) +
              ∑ k : Fin n, u k.succ.castSucc * (fk k.succ - fk k.castSucc))) := by
        rw [← hneg_u]; field_simp [hs_pos.ne']; ring
      have hF_mul : P 0 * F sw ≤ P 0 * F (u 0) := mul_le_mul_of_nonneg_left hF_sw_le hP0_nn
      linarith [h0, hsum, hneg_sum, hpull, hdrop, hcomb, hF_mul]
    have hu_tel :
        u 0 * fk 0 - s * fk (Fin.last n) +
          ∑ k : Fin n, u k.succ.castSucc * (fk k.succ - fk k.castSucc) =
        ∑ k : Fin (n + 1), (u k.castSucc - u k.succ) * fk k := by
      rw [hs_def, ← hum, ← fin_sum_by_parts n u fk]
    have hint_f : ∀ a b : ℝ, 1 < a → a ≤ b → IntervalIntegrable (fun t => f (t - 1)) volume a b := by
      intro a b ha hab
      have hcont : ContinuousOn (fun t => f (t - 1)) (Set.uIcc a b) := by
        rw [Set.uIcc_of_le hab]
        exact hFf.f_cont.comp (continuousOn_id.sub continuousOn_const) fun t ht => by
          change 0 < t - 1; linarith [ht.1]
      exact hcont.intervalIntegrable
    have hu_succ_gt1 : ∀ k : Fin (n + 1), 1 < u k.succ := fun k => by
      by_cases hlast : k = Fin.last n
      · subst hlast; rw [Fin.succ_last, hum]; linarith
      · have hlt : k.1 + 1 < n + 1 := by
          have := k.2; have : k.1 ≠ n := fun h => hlast (Fin.ext h); omega
        have heq : k.succ = (⟨k.1 + 1, hlt⟩ : Fin (n + 1)).castSucc := rfl
        rw [heq]; linarith [hu_gt_s ⟨k.1 + 1, hlt⟩]
    have hriem : ∫ t in s..u 0, f (t - 1) ≤ ∑ k : Fin (n + 1), (u k.castSucc - u k.succ) * fk k := by
      have hterm : ∀ k : Fin (n + 1),
          ∫ t in u k.succ..u k.castSucc, f (t - 1) ≤ (u k.castSucc - u k.succ) * fk k := by
        intro k
        have hconst : (u k.castSucc - u k.succ) * fk k = ∫ _t in u k.succ..u k.castSucc, fk k := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
        rw [hconst]
        refine intervalIntegral.integral_mono_on (hu_dec k).le
          (hint_f _ _ (hu_succ_gt1 k) (hu_dec k).le) intervalIntegrable_const fun t ht => ?_
        exact hFf.f_monotone (Set.mem_Ioi.mpr (by linarith [ht.1, hu_succ_gt1 k]))
          (Set.mem_Ioi.mpr (by linarith [hu_gt_s k])) (by linarith [ht.2])
      have hsum_int : ∑ k : Fin (n + 1), (∫ t in u k.succ..u k.castSucc, f (t - 1)) =
          ∫ t in s..u 0, f (t - 1) := by
        rw [hs_def, ← hum]
        exact sum_intervalIntegral_antitone_seq (n + 1) u (fun t => f (t - 1))
          fun k => hint_f _ _ (hu_succ_gt1 k) (hu_dec k).le
      rw [← hsum_int]
      exact Finset.sum_le_sum fun k _ => hterm k
    have hbuch := hFf.F_buchstab s (u 0) hs_ge3 (hu_gt_s 0).le
    have hFs_le3 : F s ≤ F 3 := hFf.F_antitone (Set.mem_Ioi.mpr (by norm_num))
      (Set.mem_Ioi.mpr hs_pos) hs_ge3
    have hCs_nn : 0 ≤ siftProd ω z * (C / s) := by
      have : 0 ≤ C := by linarith
      positivity
    have hsub_le : u 0 * F (u 0) - ∑ k : Fin (n + 1), (u k.castSucc - u k.succ) * fk k ≤
        u 0 * F (u 0) - ∫ t in s..u 0, f (t - 1) := by linarith
    calc P 0 * F sw - (P 0 * fk 0 - siftProd ω z * fk (Fin.last n) +
            ∑ k : Fin n, P k.succ.castSucc * (fk k.succ - fk k.castSucc))
        ≤ siftProd ω z * (C / s) * (u 0 * F (u 0) - ∫ t in s..u 0, f (t - 1)) := by
          rw [hu_tel] at hstep1
          exact hstep1.trans (mul_le_mul_of_nonneg_left hsub_le hCs_nn)
      _ = siftProd ω z * (C * F s) := by
          have : u 0 * F (u 0) - ∫ t in s..u 0, f (t - 1) = s * F s := by linarith
          rw [this]; field_simp [hs_pos.ne']
      _ ≤ siftProd ω z * (F s + (K / Real.log w) * F 3) := by
          rw [hC_def]
          exact mul_le_mul_of_nonneg_left (by nlinarith) hPz.le

/-- **Master Buchstab–Mertens Lemma (M⁻)** (Lower Sieve `s ≥ 2`):
```
P(z) * (f(s) - (K / log w) * F 1)
  ≤ P(w) * f(s_w) - ∑_{w ≤ p < z} ω(p) * P(p) * F(log D / log p - 1)
```
with ZERO smoothness assumptions beyond `LinearSievePair F f`! -/
lemma master_buchstab_lower {ω : ℕ → ℝ} {K : ℝ} (hω : LinearSieveDensity ω K)
    {F f : ℝ → ℝ} (hFf : LinearSievePair F f)
    {D w z : ℝ} (hw2 : 2 ≤ w) (hwz : w ≤ z) (hz2 : z ^ 2 ≤ D) :
    siftProd ω z * (f (Real.log D / Real.log z) - (K / Real.log w) * F 1) ≤
      siftProd ω w * f (Real.log D / Real.log w) -
        ∑ p ∈ (primesIcoList w z).toFinset,
          ω p * siftProd ω (p : ℝ) * F (Real.log D / Real.log (p : ℝ) - 1) := by
  have hPz : 0 < siftProd ω z := siftProd_pos_of_linearSieve hω z
  have hz2_le : 2 ≤ z := hw2.trans hwz
  have hz0 : 0 < z := by linarith
  have hlw : 0 < Real.log w := Real.log_pos (by linarith)
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hzD : z < D := by
    have : z < z ^ 2 := by nlinarith
    linarith
  have hlD : 0 < Real.log D := Real.log_pos (by linarith)
  have hs_ge2 : 2 ≤ Real.log D / Real.log z := by
    rw [le_div_iff₀ hlz]
    have hlog2 : 2 * Real.log z = Real.log (z ^ 2) := by rw [Real.log_pow]; ring
    rw [hlog2]
    exact Real.log_le_log (pow_pos hz0 2) hz2
  have hs_pos : 0 < Real.log D / Real.log z := by linarith
  have hsw_ge : Real.log D / Real.log z ≤ Real.log D / Real.log w :=
    div_le_div_of_nonneg_left hlD.le hlw (Real.log_le_log (by linarith) hwz)
  set s := Real.log D / Real.log z with hs_def
  set sw := Real.log D / Real.log w with hsw_def
  set C := 1 + K / Real.log w with hC_def
  have hK_nn : 0 ≤ K / Real.log w := div_nonneg (by linarith [hω.K_ge_one]) hlw.le
  have hC_ge1 : 1 ≤ C := by linarith
  have hF1_pos : 0 < F 1 := lt_of_lt_of_le zero_lt_one (hFf.one_le_F 1 zero_lt_one)
  by_cases hm0 : (primesIcoAsc w z).length = 0
  · rw [sum_primesIcoList_eq_fin]
    have hemp : ∑ i : Fin (primesIcoAsc w z).length,
        ω (primesIcoAsc w z)[i] * siftProd ω ((primesIcoAsc w z)[i] : ℝ) *
          F (Real.log D / Real.log ((primesIcoAsc w z)[i] : ℝ) - 1) = 0 :=
      Finset.sum_eq_zero fun i _ => absurd i.2 (by omega)
    rw [hemp, sub_zero]
    have hempty : (primesIcoList w z).toFinset = ∅ := by
      have : (primesIcoList w z).length = 0 := by simpa [primesIcoAsc] using hm0
      rw [List.length_eq_zero_iff] at this; simp [this]
    have hPw_eq : siftProd ω w = siftProd ω z := by
      have hb := siftProd_buchstab ω hwz
      rw [hempty, Finset.sum_empty, sub_zero] at hb; exact hb.symm
    rw [hPw_eq]
    have hf_le : f s ≤ f sw :=
      hFf.f_monotone (Set.mem_Ioi.mpr hs_pos) (Set.mem_Ioi.mpr (lt_of_lt_of_le hs_pos hsw_ge)) hsw_ge
    have hKF_nn : 0 ≤ (K / Real.log w) * F 1 := mul_nonneg hK_nn hF1_pos.le
    nlinarith
  · obtain ⟨n, hm⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    obtain ⟨P, u, hP0, hPm, hum, hu_le_sw, hu_gt_s, hu_dec, hP_bd, hsum_F⟩ :=
      primesIcoAsc_siftProd_data hω hw2 hwz hzD hm
    set Fk : Fin (n + 1) → ℝ := fun k => F (u k.castSucc - 1)
    have hu0_gt : s < u 0 := by simpa [Fin.castSucc_zero, hs_def] using hu_gt_s 0
    have hFk_inc : ∀ k : Fin n, Fk k.castSucc ≤ Fk k.succ := fun k => by
      have hdec := hu_dec k.castSucc
      rw [← Fin.castSucc_succ] at hdec
      exact hFf.F_antitone (Set.mem_Ioi.mpr (by linarith [hu_gt_s k.succ]))
        (Set.mem_Ioi.mpr (by linarith [hu_gt_s k.castSucc])) (by linarith)
    have hFk_last_le : Fk (Fin.last n) ≤ F 1 :=
      hFf.F_antitone (Set.mem_Ioi.mpr zero_lt_one)
        (Set.mem_Ioi.mpr (by linarith [hu_gt_s (Fin.last n)])) (by linarith [hu_gt_s (Fin.last n)])
    rw [hsum_F F, ← hP0, fin_sum_by_parts n P Fk, hPm]
    have hf_le_sw : f (u 0) ≤ f sw :=
      hFf.f_monotone (Set.mem_Ioi.mpr (by linarith))
        (Set.mem_Ioi.mpr (by linarith)) hu_le_sw
    have hP0_nn : 0 ≤ P 0 := by rw [hP0]; exact (siftProd_pos_of_linearSieve hω w).le
    have hcoeff0 : 0 ≤ Fk 0 - f (u 0) := by
      dsimp only [Fk]
      rw [Fin.castSucc_zero]
      linarith [hFf.one_le_F (u 0 - 1) (by linarith),
        hFf.f_le_one (u 0) (by linarith)]
    have hstep1 :
        (P 0 * Fk 0 - siftProd ω z * Fk (Fin.last n) +
            ∑ k : Fin n, P k.succ.castSucc * (Fk k.succ - Fk k.castSucc)) - P 0 * f sw ≤
        siftProd ω z * (C / s) *
            (- u 0 * f (u 0) + (u 0 * Fk 0 - s * Fk (Fin.last n) +
              ∑ k : Fin n, u k.succ.castSucc * (Fk k.succ - Fk k.castSucc))) +
          siftProd ω z * ((C - 1) * Fk (Fin.last n)) := by
      have h0 : P 0 * (Fk 0 - f (u 0)) ≤ siftProd ω z * (C * (u 0 / s)) * (Fk 0 - f (u 0)) :=
        mul_le_mul_of_nonneg_right (hP_bd 0) hcoeff0
      have hsum : ∑ k : Fin n, P k.succ.castSucc * (Fk k.succ - Fk k.castSucc) ≤
          ∑ k : Fin n, (siftProd ω z * (C * (u k.succ.castSucc / s))) * (Fk k.succ - Fk k.castSucc) :=
        Finset.sum_le_sum fun k _ =>
          mul_le_mul_of_nonneg_right (hP_bd k.succ) (sub_nonneg.mpr (hFk_inc k))
      have hpull : ∑ k : Fin n, (siftProd ω z * (C * (u k.succ.castSucc / s))) * (Fk k.succ - Fk k.castSucc) =
          siftProd ω z * (C / s) * ∑ k : Fin n, u k.succ.castSucc * (Fk k.succ - Fk k.castSucc) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
      have hcomb :
          siftProd ω z * (C * (u 0 / s)) * (Fk 0 - f (u 0)) - siftProd ω z * Fk (Fin.last n) +
            siftProd ω z * (C / s) * ∑ k : Fin n, u k.succ.castSucc * (Fk k.succ - Fk k.castSucc) =
          siftProd ω z * (C / s) *
            (- u 0 * f (u 0) + (u 0 * Fk 0 - s * Fk (Fin.last n) +
              ∑ k : Fin n, u k.succ.castSucc * (Fk k.succ - Fk k.castSucc))) +
            siftProd ω z * ((C - 1) * Fk (Fin.last n)) := by
        field_simp [hs_pos.ne']; ring
      have hf_mul : P 0 * f (u 0) ≤ P 0 * f sw := mul_le_mul_of_nonneg_left hf_le_sw hP0_nn
      linarith [h0, hsum, hpull, hcomb, hf_mul]
    have hu_tel :
        u 0 * Fk 0 - s * Fk (Fin.last n) +
          ∑ k : Fin n, u k.succ.castSucc * (Fk k.succ - Fk k.castSucc) =
        ∑ k : Fin (n + 1), (u k.castSucc - u k.succ) * Fk k := by
      rw [hs_def, ← hum, ← fin_sum_by_parts n u Fk]
    have hint_F : ∀ a b : ℝ, 1 < a → a ≤ b → IntervalIntegrable (fun t => F (t - 1)) volume a b := by
      intro a b ha hab
      have hcont : ContinuousOn (fun t => F (t - 1)) (Set.uIcc a b) := by
        rw [Set.uIcc_of_le hab]
        exact hFf.F_cont.comp (continuousOn_id.sub continuousOn_const) fun t ht => by
          change 0 < t - 1; linarith [ht.1]
      exact hcont.intervalIntegrable
    have hu_succ_gt1 : ∀ k : Fin (n + 1), 1 < u k.succ := fun k => by
      by_cases hlast : k = Fin.last n
      · subst hlast; rw [Fin.succ_last, hum]; linarith
      · have hlt : k.1 + 1 < n + 1 := by
          have := k.2; have : k.1 ≠ n := fun h => hlast (Fin.ext h); omega
        have heq : k.succ = (⟨k.1 + 1, hlt⟩ : Fin (n + 1)).castSucc := rfl
        rw [heq]; linarith [hu_gt_s ⟨k.1 + 1, hlt⟩]
    have hriem : ∑ k : Fin (n + 1), (u k.castSucc - u k.succ) * Fk k ≤ ∫ t in s..u 0, F (t - 1) := by
      have hterm : ∀ k : Fin (n + 1),
          (u k.castSucc - u k.succ) * Fk k ≤ ∫ t in u k.succ..u k.castSucc, F (t - 1) := by
        intro k
        have hconst : (u k.castSucc - u k.succ) * Fk k = ∫ _t in u k.succ..u k.castSucc, Fk k := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
        rw [hconst]
        refine intervalIntegral.integral_mono_on (hu_dec k).le intervalIntegrable_const
          (hint_F _ _ (hu_succ_gt1 k) (hu_dec k).le) fun t ht => ?_
        exact hFf.F_antitone (Set.mem_Ioi.mpr (by linarith [ht.1, hu_succ_gt1 k]))
          (Set.mem_Ioi.mpr (by linarith [hu_gt_s k])) (by linarith [ht.2])
      have hsum_int : ∑ k : Fin (n + 1), (∫ t in u k.succ..u k.castSucc, F (t - 1)) =
          ∫ t in s..u 0, F (t - 1) := by
        rw [hs_def, ← hum]
        exact sum_intervalIntegral_antitone_seq (n + 1) u (fun t => F (t - 1))
          fun k => hint_F _ _ (hu_succ_gt1 k) (hu_dec k).le
      rw [← hsum_int]
      exact Finset.sum_le_sum fun k _ => hterm k
    have hbuch := hFf.f_buchstab s (u 0) hs_ge2 (hu_gt_s 0).le
    have hC_sub : C - 1 = K / Real.log w := by rw [hC_def]; ring
    have hfs_nn : 0 ≤ f s := hFf.f_nonneg s hs_pos
    have hCs_nn : 0 ≤ siftProd ω z * (C / s) := by
      have : 0 ≤ C := by linarith
      positivity
    have hadd_le : - u 0 * f (u 0) + ∑ k : Fin (n + 1), (u k.castSucc - u k.succ) * Fk k ≤
        - u 0 * f (u 0) + ∫ t in s..u 0, F (t - 1) := by linarith
    have hupper_neg :
        (P 0 * Fk 0 - siftProd ω z * Fk (Fin.last n) +
            ∑ k : Fin n, P k.succ.castSucc * (Fk k.succ - Fk k.castSucc)) - P 0 * f sw ≤
        siftProd ω z * ((K / Real.log w) * F 1 - f s) := by
      calc (P 0 * Fk 0 - siftProd ω z * Fk (Fin.last n) +
              ∑ k : Fin n, P k.succ.castSucc * (Fk k.succ - Fk k.castSucc)) - P 0 * f sw
          ≤ siftProd ω z * (C / s) * (- u 0 * f (u 0) + ∫ t in s..u 0, F (t - 1)) +
              siftProd ω z * ((C - 1) * Fk (Fin.last n)) := by
            rw [hu_tel] at hstep1
            have hmul := mul_le_mul_of_nonneg_left hadd_le hCs_nn
            linarith
        _ = siftProd ω z * ((C - 1) * Fk (Fin.last n) - C * f s) := by
            have : - u 0 * f (u 0) + ∫ t in s..u 0, F (t - 1) = - (s * f s) := by linarith
            rw [this]; field_simp [hs_pos.ne']; ring
        _ ≤ siftProd ω z * ((K / Real.log w) * F 1 - f s) := by
            rw [hC_sub]
            exact mul_le_mul_of_nonneg_left (by nlinarith) hPz.le
    linarith

/-! ## Section 3: Contraction Barrier Functions `psiPlus β`, `psiMinus β` (`β = 1` and `β = 6/5`) -/

/-- Upper contraction barrier function `Ψ⁺_β(s)`:
equals `(105/100) * (3/s) * exp(-3β)` on `(0, 3]` and `exp(-β s)` on `(3, ∞)`. -/
def psiPlus (β s : ℝ) : ℝ :=
  if s ≤ 3 then (105 / 100 : ℝ) * (3 / s) * Real.exp (-(3 * β)) else Real.exp (-(β * s))

/-- Lower contraction barrier function `Ψ⁻_β(s) = exp(-β s)`. -/
def psiMinus (β s : ℝ) : ℝ :=
  Real.exp (-(β * s))

lemma psiPlus_pos {β s : ℝ} (hs : 0 < s) : 0 < psiPlus β s := by
  unfold psiPlus
  split_ifs <;> positivity

lemma psiMinus_pos (β s : ℝ) : 0 < psiMinus β s := Real.exp_pos _

lemma psiMinus_antitone {β : ℝ} (hβ : 0 ≤ β) : AntitoneOn (psiMinus β) (Set.Ioi 0) := by
  intro a _ b _ hab
  unfold psiMinus
  exact Real.exp_le_exp.mpr (by nlinarith)

lemma psiPlus_antitone {β : ℝ} (hβ : 0 ≤ β) : AntitoneOn (psiPlus β) (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha0 : 0 < a := Set.mem_Ioi.mp ha
  have hb0 : 0 < b := Set.mem_Ioi.mp hb
  unfold psiPlus
  split_ifs with h1 h2 h2
  · have hdiv : 3 / b ≤ 3 / a := div_le_div_of_nonneg_left (by norm_num) ha0 hab
    have hexp : 0 ≤ Real.exp (-(3 * β)) := (Real.exp_pos _).le
    nlinarith
  · linarith
  · have h3a : (1 : ℝ) ≤ 3 / a := (one_le_div ha0).mpr h2
    have hexp : Real.exp (-(β * b)) ≤ Real.exp (-(3 * β)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hexp_pos : 0 < Real.exp (-(3 * β)) := Real.exp_pos _
    nlinarith
  · exact Real.exp_le_exp.mpr (by nlinarith)

/-- Elementary Taylor-based log upper bound: if `x ≤ ∑_{k < 6} r^k / k!` for `r ≥ 0`, then `log x ≤ r`. -/
private lemma log_le_of_le_taylor6 {x r : ℝ} (hx : 0 < x) (hr : 0 ≤ r)
    (h : x ≤ 1 + r + r ^ 2 / 2 + r ^ 3 / 6 + r ^ 4 / 24 + r ^ 5 / 120) :
    Real.log x ≤ r := by
  rw [Real.log_le_iff_le_exp hx]
  have ht := Real.sum_le_exp_of_nonneg hr 6
  have hsum : ∑ i ∈ Finset.range 6, r ^ i / (i.factorial : ℝ) =
      1 + r + r ^ 2 / 2 + r ^ 3 / 6 + r ^ 4 / 24 + r ^ 5 / 120 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  linarith

/-- Elementary negative-exponential upper bound via degree-5 Taylor polynomial. -/
private lemma exp_neg_le_of_taylor6 {r c : ℝ} (hr : 0 ≤ r) (hc : 0 < c)
    (h : 1 ≤ c * (1 + r + r ^ 2 / 2 + r ^ 3 / 6 + r ^ 4 / 24 + r ^ 5 / 120)) :
    Real.exp (-r) ≤ c := by
  have ht := Real.sum_le_exp_of_nonneg hr 6
  have hsum : ∑ i ∈ Finset.range 6, r ^ i / (i.factorial : ℝ) =
      1 + r + r ^ 2 / 2 + r ^ 3 / 6 + r ^ 4 / 24 + r ^ 5 / 120 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at ht
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos r) hc]
  rw [inv_eq_one_div, div_le_iff₀ hc]
  nlinarith

/-- Elementary positive rational exponential upper bound from `e < 2.719`:
if `2.719 ^ p ≤ c ^ q` for `0 < c`, `q ≥ 1`, then `exp (p / q) ≤ c`. -/
private lemma exp_rat_le_of_pow {p q : ℕ} {c : ℝ} (hq : 0 < q) (hc : 0 < c)
    (h : ((2719 : ℝ) / 1000) ^ p ≤ c ^ q) :
    Real.exp ((p : ℝ) / (q : ℝ)) ≤ c := by
  have he : Real.exp 1 ≤ 2719 / 1000 := by linarith [Real.exp_one_lt_d9]
  have hpow : (Real.exp ((p : ℝ) / (q : ℝ))) ^ q ≤ c ^ q := by
    rw [← Real.exp_nat_mul]
    have hmul : (q : ℝ) * ((p : ℝ) / (q : ℝ)) = (p : ℝ) := by
      have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
      field_simp [hq0]
    rw [hmul, show (p : ℝ) = (p : ℕ) * (1 : ℝ) by ring, Real.exp_nat_mul]
    exact le_trans (pow_le_pow_left₀ (Real.exp_pos 1).le he p) h
  exact le_of_pow_le_pow_left₀ hq.ne' hc.le hpow

lemma exp_one_pt_two_lt_four : Real.exp (6 / 5 : ℝ) ≤ 4 := by
  have h := exp_rat_le_of_pow (p := 6) (q := 5) (c := 4) (by norm_num) (by norm_num) (by norm_num)
  simpa using h

lemma psiPlus_sub_one_le {β s : ℝ} (hβ1 : 1 ≤ β) (hβ2 : β ≤ 6 / 5) (hs : 2 ≤ s) :
    psiPlus β (s - 1) ≤ 13 * psiMinus β s := by
  have heβ : Real.exp β ≤ 4 :=
    (Real.exp_le_exp.mpr hβ2).trans exp_one_pt_two_lt_four
  unfold psiPlus psiMinus
  split_ifs with hle
  · have hs1 : 1 ≤ s - 1 := by linarith
    have hdiv : 3 / (s - 1) ≤ 3 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hexp_eq : Real.exp (-(3 * β)) = Real.exp (β * (s - 3)) * Real.exp (-(β * s)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hexp_bd : Real.exp (β * (s - 3)) ≤ Real.exp β :=
      Real.exp_le_exp.mpr (by nlinarith)
    rw [hexp_eq]
    have hpos : 0 < Real.exp (-(β * s)) := Real.exp_pos _
    have h1 : (105 / 100 : ℝ) * (3 / (s - 1)) ≤ 315 / 100 := by nlinarith
    have h2 : Real.exp (β * (s - 3)) ≤ 4 := hexp_bd.trans heβ
    have hprod : (105 / 100 : ℝ) * (3 / (s - 1)) * Real.exp (β * (s - 3)) ≤ 13 := by
      have : (105 / 100 : ℝ) * (3 / (s - 1)) * Real.exp (β * (s - 3)) ≤ (315 / 100) * 4 :=
        mul_le_mul h1 h2 (Real.exp_pos _).le (by norm_num)
      linarith
    calc (105 / 100 : ℝ) * (3 / (s - 1)) * (Real.exp (β * (s - 3)) * Real.exp (-(β * s)))
        = ((105 / 100 : ℝ) * (3 / (s - 1)) * Real.exp (β * (s - 3))) * Real.exp (-(β * s)) := by ring
      _ ≤ 13 * Real.exp (-(β * s)) := mul_le_mul_of_nonneg_right hprod hpos.le
  · have hexp_eq : Real.exp (-(β * (s - 1))) = Real.exp β * Real.exp (-(β * s)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hexp_eq]
    have hpos : 0 < Real.exp (-(β * s)) := Real.exp_pos _
    nlinarith

lemma psiMinus_sub_one_le {β s : ℝ} (hβ2 : β ≤ 6 / 5) (hs : 3 ≤ s) :
    psiMinus β (s - 1) ≤ 4 * psiPlus β s := by
  have heβ : Real.exp β ≤ 4 :=
    (Real.exp_le_exp.mpr hβ2).trans exp_one_pt_two_lt_four
  unfold psiMinus psiPlus
  have hexp_eq : Real.exp (-(β * (s - 1))) = Real.exp β * Real.exp (-(β * s)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp_eq]
  have hpos : 0 < Real.exp (-(β * s)) := Real.exp_pos _
  split_ifs with hle
  · have hs3 : s = 3 := by linarith
    subst hs3
    have : (105 / 100 : ℝ) * (3 / 3) * Real.exp (-(3 * β)) = (105 / 100 : ℝ) * Real.exp (-(β * 3)) := by
      have : (3 : ℝ) * β = β * 3 := mul_comm _ _
      rw [this]; ring
    rw [this]; nlinarith
  · nlinarith

/-- Exact integral of `exp (-β (u - 1))` on `[a, b]`. -/
private lemma integral_exp_neg_shift {β a b : ℝ} (hβ : 0 < β) :
    ∫ u in a..b, Real.exp (-(β * (u - 1))) =
      (Real.exp (-(β * (a - 1))) - Real.exp (-(β * (b - 1)))) / β := by
  have hd : ∀ u ∈ Set.uIcc a b,
      HasDerivAt (fun t : ℝ => -Real.exp (-(β * (t - 1))) / β) (Real.exp (-(β * (u - 1)))) u := by
    intro u _
    have h1 : HasDerivAt (fun t : ℝ => -(β * (t - 1))) (-β) u := by
      have := (((hasDerivAt_id u).sub_const 1).const_mul β).fun_neg
      simpa using this
    have h2 := (h1.exp.fun_neg).div_const β
    refine h2.congr_deriv ?_
    field_simp [hβ.ne']
  have hc : ContinuousOn (fun u : ℝ => Real.exp (-(β * (u - 1)))) (Set.uIcc a b) := by
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable]
  ring

/-- Upper contraction for `s ≥ 3`:
`(1 / s) * ∫_s^{sw} Ψ⁻_β(u - 1) du ≤ (exp β / (3 * β)) * Ψ⁺_β(s)`. -/
lemma psiMinus_integral_contraction {β s sw : ℝ} (hβ : 0 < β) (hs3 : 3 ≤ s) (hsw : s ≤ sw) :
    (1 / s) * (∫ u in s..sw, psiMinus β (u - 1)) ≤ (Real.exp β / (3 * β)) * psiPlus β s := by
  unfold psiMinus
  rw [integral_exp_neg_shift hβ]
  have h1 : (Real.exp (-(β * (s - 1))) - Real.exp (-(β * (sw - 1)))) / β ≤
      Real.exp (-(β * (s - 1))) / β := by
    gcongr; linarith [Real.exp_pos (-(β * (sw - 1)))]
  have h2 : Real.exp (-(β * (s - 1))) = Real.exp β * Real.exp (-(β * s)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 : Real.exp (-(β * s)) ≤ psiPlus β s := by
    unfold psiPlus
    split_ifs with hle
    · have hs_eq : s = 3 := by linarith
      subst hs_eq
      have : (105 / 100 : ℝ) * (3 / 3) * Real.exp (-(3 * β)) = (105 / 100 : ℝ) * Real.exp (-(β * 3)) := by
        have : (3 : ℝ) * β = β * 3 := mul_comm _ _
        rw [this]; ring
      rw [this]; linarith [Real.exp_pos (-(β * 3))]
    · exact le_rfl
  have hs0 : 0 < s := by linarith
  have hinv_le : 1 / s ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hs3
  calc (1 / s) * ((Real.exp (-(β * (s - 1))) - Real.exp (-(β * (sw - 1)))) / β)
      ≤ (1 / s) * (Real.exp (-(β * (s - 1))) / β) := by
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = (1 / s) * (Real.exp β / β) * Real.exp (-(β * s)) := by rw [h2]; ring
    _ ≤ (1 / 3) * (Real.exp β / β) * psiPlus β s := by
        have hnn1 : 0 ≤ Real.exp β / β := by positivity
        have hnn2 : 0 ≤ (1 / 3 : ℝ) * (Real.exp β / β) := by positivity
        calc (1 / s) * (Real.exp β / β) * Real.exp (-(β * s))
            ≤ (1 / 3) * (Real.exp β / β) * Real.exp (-(β * s)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hinv_le hnn1) (Real.exp_pos _).le
          _ ≤ (1 / 3) * (Real.exp β / β) * psiPlus β s :=
              mul_le_mul_of_nonneg_left h3 hnn2
    _ = (Real.exp β / (3 * β)) * psiPlus β s := by ring

/-- Exact upper bound on `(1 / s) * ∫_s^{sw} Ψ⁺_β(u - 1) du` for `2 ≤ s ≤ 4`:
`≤ (exp (-(3β)) / s) * (1 / β + (315 / 100) * log (3 / (s - 1)))`. -/
private lemma psiPlus_integral_bound_Icc {β s sw : ℝ} (hβ : 0 < β)
    (hs2 : 2 ≤ s) (hs4 : s ≤ 4) (hsw : s ≤ sw) :
    (1 / s) * (∫ u in s..sw, psiPlus β (u - 1)) ≤
      (Real.exp (-(3 * β)) / s) * (1 / β + (315 / 100 : ℝ) * Real.log (3 / (s - 1))) := by
  have hs0 : 0 < s := by linarith
  have hint_fn : ∀ a b : ℝ, 1 < a → a ≤ b → IntervalIntegrable (fun u => psiPlus β (u - 1)) volume a b := by
    intro a b ha hab
    have hanti : AntitoneOn (fun u => psiPlus β (u - 1)) (Set.Ioi 1) := fun x hx y hy hxy =>
      psiPlus_antitone hβ.le (Set.mem_Ioi.mpr (by linarith [Set.mem_Ioi.mp hx]))
        (Set.mem_Ioi.mpr (by linarith [Set.mem_Ioi.mp hy])) (by linarith)
    exact (hanti.mono (by rw [Set.uIcc_of_le hab]; intro t ht; exact lt_of_lt_of_le ha ht.1)).intervalIntegrable
  -- Bound `∫_s^{min sw 4} psiPlus β (u - 1) du ≤ (315/100) * exp(-3β) * log(3 / (s - 1))`
  set m := min sw 4 with hm_def
  have hsm : s ≤ m := le_min hsw hs4
  have hm4 : m ≤ 4 := min_le_right sw 4
  have hmsw : m ≤ sw := min_le_left sw 4
  have hpart1 : ∫ u in s..m, psiPlus β (u - 1) ≤
      (315 / 100 : ℝ) * Real.exp (-(3 * β)) * Real.log (3 / (s - 1)) := by
    have heq_on : Set.EqOn (fun u => psiPlus β (u - 1))
        (fun u => ((315 / 100 : ℝ) * Real.exp (-(3 * β))) * (u - 1)⁻¹) (Set.uIcc s m) := by
      rw [Set.uIcc_of_le hsm]
      intro u hu
      have hu3 : u - 1 ≤ 3 := by linarith [hu.2]
      dsimp only
      unfold psiPlus
      rw [if_pos hu3]
      ring
    rw [intervalIntegral.integral_congr heq_on, intervalIntegral.integral_const_mul]
    have hlog_int : ∫ u in s..m, (u - 1)⁻¹ = Real.log ((m - 1) / (s - 1)) := by
      have hd : ∀ u ∈ Set.uIcc s m, HasDerivAt (fun t : ℝ => Real.log (t - 1)) (u - 1)⁻¹ u := by
        intro u hu
        rw [Set.uIcc_of_le hsm] at hu
        have hu1 : u - 1 ≠ 0 := by linarith [hu.1]
        have h := ((hasDerivAt_id u).sub_const 1).log hu1
        simpa [one_div] using h
      have hc : ContinuousOn (fun u : ℝ => (u - 1)⁻¹) (Set.uIcc s m) := by
        rw [Set.uIcc_of_le hsm]
        exact (continuousOn_id.sub continuousOn_const).inv₀ fun u hu => by show u - 1 ≠ 0; linarith [hu.1]
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable,
        ← Real.log_div (by linarith) (by linarith)]
    rw [hlog_int]
    have hlog_le : Real.log ((m - 1) / (s - 1)) ≤ Real.log (3 / (s - 1)) :=
      Real.log_le_log (div_pos (by linarith) (by linarith))
        (div_le_div_of_nonneg_right (by linarith) (by linarith))
    exact mul_le_mul_of_nonneg_left hlog_le (by positivity)
  have hpart2 : ∫ u in m..sw, psiPlus β (u - 1) ≤ Real.exp (-(3 * β)) / β := by
    by_cases h4 : sw ≤ 4
    · have hmeq : m = sw := min_eq_left h4
      rw [hmeq, intervalIntegral.integral_same]
      positivity
    · push Not at h4
      have hmeq : m = 4 := min_eq_right h4.le
      rw [hmeq]
      have hae : ∀ᵐ u ∂volume, u ∈ Set.uIoc 4 sw → psiPlus β (u - 1) = Real.exp (-(β * (u - 1))) := by
        filter_upwards with u hu
        rw [Set.uIoc_of_le h4.le] at hu
        have hu3 : ¬ (u - 1 ≤ 3) := by linarith [hu.1]
        unfold psiPlus; rw [if_neg hu3]
      rw [intervalIntegral.integral_congr_ae hae, integral_exp_neg_shift hβ]
      have : Real.exp (-(β * (4 - 1))) = Real.exp (-(3 * β)) := by congr 1; ring
      rw [this]
      gcongr; linarith [Real.exp_pos (-(β * (sw - 1)))]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hint_fn s m (by linarith) hsm) (hint_fn m sw (by linarith) hmsw)
  calc (1 / s) * (∫ u in s..sw, psiPlus β (u - 1))
      = (1 / s) * ((∫ u in s..m, psiPlus β (u - 1)) + (∫ u in m..sw, psiPlus β (u - 1))) := by
        rw [hsplit]
    _ ≤ (1 / s) * ((315 / 100 : ℝ) * Real.exp (-(3 * β)) * Real.log (3 / (s - 1)) +
          Real.exp (-(3 * β)) / β) := by
        exact mul_le_mul_of_nonneg_left (add_le_add hpart1 hpart2) (by positivity)
    _ = (Real.exp (-(3 * β)) / s) * (1 / β + (315 / 100 : ℝ) * Real.log (3 / (s - 1))) := by ring

/-- Monotonicity of `s ↦ exp(β * (s - 3)) / s` on `[2, 4]` for `β ≥ 1`. -/
private lemma exp_div_id_monotoneOn {β : ℝ} (hβ1 : 1 ≤ β) :
    MonotoneOn (fun s : ℝ => Real.exp (β * (s - 3)) / s) (Set.Icc 2 4) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc 2 4) ?_ ?_ ?_
  · exact (ContinuousOn.div
      (Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn
      continuousOn_id fun s hs => by linarith [hs.1])
  · intro s hs
    rw [interior_Icc] at hs
    have hs0 : s ≠ 0 := by linarith [hs.1]
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (β * (t - 3))) (Real.exp (β * (s - 3)) * β) s := by
      have ha : HasDerivAt (fun t : ℝ => β * (t - 3)) β s := by
        simpa using ((hasDerivAt_id s).sub_const 3).const_mul β
      exact ha.exp
    exact (h1.fun_div (hasDerivAt_id s) hs0).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    have hs0 : 0 < s := by linarith [hs.1]
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (β * (t - 3))) (Real.exp (β * (s - 3)) * β) s := by
      have ha : HasDerivAt (fun t : ℝ => β * (t - 3)) β s := by
        simpa using ((hasDerivAt_id s).sub_const 3).const_mul β
      exact ha.exp
    have hid : HasDerivAt (fun t : ℝ => t) 1 s := hasDerivAt_id s
    have hd := h1.fun_div hid hs0.ne'
    rw [hd.deriv]
    have hnum : 0 ≤ Real.exp (β * (s - 3)) * β * s - Real.exp (β * (s - 3)) * 1 := by
      have : 1 ≤ β * s := by nlinarith [hs.1]
      nlinarith [Real.exp_pos (β * (s - 3))]
    exact div_nonneg hnum (sq_nonneg s)

/-- Subinterval contraction helper on `[a, b] ⊆ [2, 4]`. -/
private lemma contraction_on_subinterval {β a b s E_hi L_hi : ℝ}
    (hβ1 : 1 ≤ β) (ha2 : 2 ≤ a) (hb4 : b ≤ 4) (has : a ≤ s) (hsb : s ≤ b)
    (hE : Real.exp (β * (b - 3)) ≤ E_hi)
    (hL : Real.log (3 / (a - 1)) ≤ L_hi)
    (hcheck : (E_hi / b) * (1 / β + (315 / 100 : ℝ) * L_hi) ≤ 95 / 100) :
    (Real.exp (β * (s - 3)) / s) * (1 / β + (315 / 100 : ℝ) * Real.log (3 / (s - 1))) ≤ 95 / 100 := by
  have h1 : Real.exp (β * (s - 3)) / s ≤ Real.exp (β * (b - 3)) / b :=
    exp_div_id_monotoneOn hβ1 ⟨by linarith, by linarith⟩ ⟨by linarith, hb4⟩ hsb
  have h2 : Real.exp (β * (b - 3)) / b ≤ E_hi / b :=
    div_le_div_of_nonneg_right hE (by linarith)
  have h3 : Real.log (3 / (s - 1)) ≤ Real.log (3 / (a - 1)) :=
    Real.log_le_log (div_pos (by norm_num) (by linarith))
      (div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith))
  have hpos_left : 0 ≤ Real.exp (β * (s - 3)) / s := div_nonneg (Real.exp_pos _).le (by linarith)
  have hpos_right : 0 ≤ 1 / β + (315 / 100 : ℝ) * Real.log (3 / (s - 1)) := by
    have hlog_nn : 0 ≤ Real.log (3 / (s - 1)) :=
      Real.log_nonneg ((one_le_div (by linarith)).mpr (by linarith))
    have : 0 < 1 / β := by positivity
    linarith
  have hprod : (Real.exp (β * (s - 3)) / s) * (1 / β + (315 / 100 : ℝ) * Real.log (3 / (s - 1))) ≤
      (E_hi / b) * (1 / β + (315 / 100 : ℝ) * L_hi) :=
    mul_le_mul (h1.trans h2) (by linarith [h3.trans hL]) hpos_right (by
      have : 0 ≤ Real.exp (β * (b - 3)) / b := div_nonneg (Real.exp_pos _).le (by linarith)
      linarith)
  exact hprod.trans hcheck

/-- Shared log upper bounds at the 8 grid points of `[2, 4]`. -/
private lemma grid_log_bounds :
    Real.log (3 / ((2 : ℝ) - 1)) ≤ 110 / 100 ∧
    Real.log (3 / ((9 / 4 : ℝ) - 1)) ≤ 88 / 100 ∧
    Real.log (3 / ((5 / 2 : ℝ) - 1)) ≤ 70 / 100 ∧
    Real.log (3 / ((11 / 4 : ℝ) - 1)) ≤ 54 / 100 ∧
    Real.log (3 / ((3 : ℝ) - 1)) ≤ 41 / 100 ∧
    Real.log (3 / ((13 / 4 : ℝ) - 1)) ≤ 29 / 100 ∧
    Real.log (3 / ((7 / 2 : ℝ) - 1)) ≤ 19 / 100 ∧
    Real.log (3 / ((15 / 4 : ℝ) - 1)) ≤ 9 / 100 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact log_le_of_le_taylor6 (by norm_num) (by norm_num) (by norm_num)

/-- **Contraction Theorem for `β = 1`**:
- `(1/s) * ∫_s^{sw} Ψ⁻_1(u - 1) du ≤ (95/100) * Ψ⁺_1(s)` for `s ≥ 3`
- `(1/s) * ∫_s^{sw} Ψ⁺_1(u - 1) du ≤ (95/100) * Ψ⁻_1(s)` for `s ≥ 2`. -/
theorem psi_contraction_one :
    (∀ s sw : ℝ, 3 ≤ s → s ≤ sw →
      (1 / s) * (∫ u in s..sw, psiMinus 1 (u - 1)) ≤ (95 / 100 : ℝ) * psiPlus 1 s) ∧
    (∀ s sw : ℝ, 2 ≤ s → s ≤ sw →
      (1 / s) * (∫ u in s..sw, psiPlus 1 (u - 1)) ≤ (95 / 100 : ℝ) * psiMinus 1 s) := by
  constructor
  · intro s sw hs3 hsw
    have h := psiMinus_integral_contraction (β := 1) one_pos hs3 hsw
    have hc : Real.exp 1 / (3 * 1) ≤ 95 / 100 := by linarith [Real.exp_one_lt_d9]
    exact h.trans (mul_le_mul_of_nonneg_right hc (psiPlus_pos (by linarith)).le)
  · intro s sw hs2 hsw
    by_cases hs4 : 4 ≤ s
    · have hae : ∀ᵐ u ∂volume, u ∈ Set.uIoc s sw → psiPlus 1 (u - 1) = Real.exp (-(1 * (u - 1))) := by
        filter_upwards with u hu
        rw [Set.uIoc_of_le hsw] at hu
        unfold psiPlus; rw [if_neg (by linarith [hu.1])]
      rw [intervalIntegral.integral_congr_ae hae, integral_exp_neg_shift one_pos]
      have h1 : (Real.exp (-(1 * (s - 1))) - Real.exp (-(1 * (sw - 1)))) / 1 ≤
          Real.exp 1 * Real.exp (-(1 * s)) := by
        have heq : Real.exp (-(1 * (s - 1))) = Real.exp 1 * Real.exp (-(1 * s)) := by
          rw [← Real.exp_add]; congr 1; ring
        linarith [Real.exp_pos (-(1 * (sw - 1)))]
      have hinv : 1 / s ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hs4
      have hc : (1 / 4 : ℝ) * Real.exp 1 ≤ 95 / 100 := by linarith [Real.exp_one_lt_d9]
      unfold psiMinus
      calc (1 / s) * ((Real.exp (-(1 * (s - 1))) - Real.exp (-(1 * (sw - 1)))) / 1)
          ≤ (1 / s) * (Real.exp 1 * Real.exp (-(1 * s))) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ (1 / 4) * (Real.exp 1 * Real.exp (-(1 * s))) :=
            mul_le_mul_of_nonneg_right hinv (by positivity)
        _ ≤ (95 / 100) * Real.exp (-(1 * s)) := by nlinarith [Real.exp_pos (-(1 * s))]
    · push Not at hs4
      have hbd := psiPlus_integral_bound_Icc (β := 1) one_pos hs2 hs4.le hsw
      have hrew : (Real.exp (-(3 * 1)) / s) * (1 / 1 + (315 / 100 : ℝ) * Real.log (3 / (s - 1))) =
          ((Real.exp (1 * (s - 3)) / s) * (1 / 1 + (315 / 100 : ℝ) * Real.log (3 / (s - 1)))) *
            psiMinus 1 s := by
        unfold psiMinus
        have : Real.exp (-(3 * 1)) = Real.exp (1 * (s - 3)) * Real.exp (-(1 * s)) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [this]; ring
      rw [hrew] at hbd
      refine hbd.trans (mul_le_mul_of_nonneg_right ?_ (psiMinus_pos 1 s).le)
      obtain ⟨hL1, hL2, hL3, hL4, hL5, hL6, hL7, hL8⟩ := grid_log_bounds
      by_cases h1 : s ≤ 9 / 4
      · exact contraction_on_subinterval le_rfl le_rfl (by norm_num) hs2 h1
          (by simpa [show (1 : ℝ) * (9 / 4 - 3) = -(3 / 4 : ℝ) by norm_num] using
            exp_neg_le_of_taylor6 (r := 3 / 4) (c := 475 / 1000) (by norm_num) (by norm_num) (by norm_num))
          hL1 (by norm_num)
      · by_cases h2 : s ≤ 5 / 2
        · exact contraction_on_subinterval le_rfl (by norm_num) (by norm_num) (by linarith) h2
            (by simpa [show (1 : ℝ) * (5 / 2 - 3) = -(1 / 2 : ℝ) by norm_num] using
              exp_neg_le_of_taylor6 (r := 1 / 2) (c := 61 / 100) (by norm_num) (by norm_num) (by norm_num))
            hL2 (by norm_num)
        · by_cases h3 : s ≤ 11 / 4
          · exact contraction_on_subinterval le_rfl (by norm_num) (by norm_num) (by linarith) h3
              (by simpa [show (1 : ℝ) * (11 / 4 - 3) = -(1 / 4 : ℝ) by norm_num] using
                exp_neg_le_of_taylor6 (r := 1 / 4) (c := 78 / 100) (by norm_num) (by norm_num) (by norm_num))
              hL3 (by norm_num)
          · by_cases h4 : s ≤ 3
            · exact contraction_on_subinterval le_rfl (by norm_num) (by norm_num) (by linarith) h4
                (by norm_num : Real.exp ((1 : ℝ) * (3 - 3)) ≤ 1) hL4 (by norm_num)
            · by_cases h5 : s ≤ 13 / 4
              · exact contraction_on_subinterval le_rfl (by norm_num) (by norm_num) (by linarith) h5
                  (by simpa [show (1 : ℝ) * (13 / 4 - 3) = (1 : ℕ) / (4 : ℕ) by norm_num] using
                    exp_rat_le_of_pow (p := 1) (q := 4) (c := 129 / 100) (by norm_num) (by norm_num) (by norm_num))
                  hL5 (by norm_num)
              · by_cases h6 : s ≤ 7 / 2
                · exact contraction_on_subinterval le_rfl (by norm_num) (by norm_num) (by linarith) h6
                    (by simpa [show (1 : ℝ) * (7 / 2 - 3) = (1 : ℕ) / (2 : ℕ) by norm_num] using
                      exp_rat_le_of_pow (p := 1) (q := 2) (c := 165 / 100) (by norm_num) (by norm_num) (by norm_num))
                    hL6 (by norm_num)
                · by_cases h7 : s ≤ 15 / 4
                  · exact contraction_on_subinterval le_rfl (by norm_num) (by norm_num) (by linarith) h7
                      (by simpa [show (1 : ℝ) * (15 / 4 - 3) = (3 : ℕ) / (4 : ℕ) by norm_num] using
                        exp_rat_le_of_pow (p := 3) (q := 4) (c := 212 / 100) (by norm_num) (by norm_num) (by norm_num))
                      hL7 (by norm_num)
                  · exact contraction_on_subinterval le_rfl (by norm_num) le_rfl (by linarith) hs4.le
                      (by simpa [show (1 : ℝ) * (4 - 3) = 1 by norm_num] using
                        (show Real.exp 1 ≤ 272 / 100 by linarith [Real.exp_one_lt_d9]))
                      hL8 (by norm_num)

/-- **Contraction Theorem for `β = 6/5`** (used in Global Fundamental Lemma):
- `(1/s) * ∫_s^{sw} Ψ⁻_{6/5}(u - 1) du ≤ (95/100) * Ψ⁺_{6/5}(s)` for `s ≥ 3`
- `(1/s) * ∫_s^{sw} Ψ⁺_{6/5}(u - 1) du ≤ (95/100) * Ψ⁻_{6/5}(s)` for `s ≥ 2`. -/
theorem psi_contraction_six_fifths :
    (∀ s sw : ℝ, 3 ≤ s → s ≤ sw →
      (1 / s) * (∫ u in s..sw, psiMinus (6 / 5) (u - 1)) ≤ (95 / 100 : ℝ) * psiPlus (6 / 5) s) ∧
    (∀ s sw : ℝ, 2 ≤ s → s ≤ sw →
      (1 / s) * (∫ u in s..sw, psiPlus (6 / 5) (u - 1)) ≤ (95 / 100 : ℝ) * psiMinus (6 / 5) s) := by
  have he65 : Real.exp (6 / 5 : ℝ) ≤ 333 / 100 := by
    simpa using exp_rat_le_of_pow (p := 6) (q := 5) (c := 333 / 100) (by norm_num) (by norm_num) (by norm_num)
  constructor
  · intro s sw hs3 hsw
    have h := psiMinus_integral_contraction (β := 6 / 5) (by norm_num) hs3 hsw
    have hc : Real.exp (6 / 5 : ℝ) / (3 * (6 / 5)) ≤ 95 / 100 := by
      have h1 : (333 / 100 : ℝ) / (3 * (6 / 5)) ≤ 95 / 100 := by norm_num
      have h2 : Real.exp (6 / 5 : ℝ) / (3 * (6 / 5)) ≤ (333 / 100 : ℝ) / (3 * (6 / 5)) :=
        div_le_div_of_nonneg_right he65 (by norm_num)
      linarith
    exact h.trans (mul_le_mul_of_nonneg_right hc (psiPlus_pos (by linarith)).le)
  · intro s sw hs2 hsw
    by_cases hs4 : 4 ≤ s
    · have hae : ∀ᵐ u ∂volume, u ∈ Set.uIoc s sw → psiPlus (6 / 5) (u - 1) = Real.exp (-((6 / 5) * (u - 1))) := by
        filter_upwards with u hu
        rw [Set.uIoc_of_le hsw] at hu
        unfold psiPlus; rw [if_neg (by linarith [hu.1])]
      rw [intervalIntegral.integral_congr_ae hae, integral_exp_neg_shift (by norm_num : (0 : ℝ) < 6 / 5)]
      have h1 : (Real.exp (-((6 / 5 : ℝ) * (s - 1))) - Real.exp (-((6 / 5 : ℝ) * (sw - 1)))) / (6 / 5) ≤
          (Real.exp (6 / 5) / (6 / 5)) * Real.exp (-((6 / 5) * s)) := by
        have heq : Real.exp (-((6 / 5 : ℝ) * (s - 1))) = Real.exp (6 / 5) * Real.exp (-((6 / 5) * s)) := by
          rw [← Real.exp_add]; congr 1; ring
        have hpos := Real.exp_pos (-((6 / 5 : ℝ) * (sw - 1)))
        rw [heq]; linarith
      have hinv : 1 / s ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hs4
      have hc : (1 / 4 : ℝ) * (Real.exp (6 / 5) / (6 / 5)) ≤ 95 / 100 := by linarith
      unfold psiMinus
      calc (1 / s) * ((Real.exp (-((6 / 5 : ℝ) * (s - 1))) - Real.exp (-((6 / 5 : ℝ) * (sw - 1)))) / (6 / 5))
          ≤ (1 / s) * ((Real.exp (6 / 5) / (6 / 5)) * Real.exp (-((6 / 5) * s))) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ (1 / 4) * ((Real.exp (6 / 5) / (6 / 5)) * Real.exp (-((6 / 5) * s))) :=
            mul_le_mul_of_nonneg_right hinv (by positivity)
        _ ≤ (95 / 100) * Real.exp (-((6 / 5) * s)) := by nlinarith [Real.exp_pos (-((6 / 5 : ℝ) * s))]
    · push Not at hs4
      have hbd := psiPlus_integral_bound_Icc (β := 6 / 5) (by norm_num) hs2 hs4.le hsw
      have hrew : (Real.exp (-(3 * (6 / 5 : ℝ))) / s) * (1 / (6 / 5) + (315 / 100 : ℝ) * Real.log (3 / (s - 1))) =
          ((Real.exp ((6 / 5 : ℝ) * (s - 3)) / s) * (1 / (6 / 5) + (315 / 100 : ℝ) * Real.log (3 / (s - 1)))) *
            psiMinus (6 / 5) s := by
        unfold psiMinus
        have : Real.exp (-(3 * (6 / 5 : ℝ))) = Real.exp ((6 / 5 : ℝ) * (s - 3)) * Real.exp (-((6 / 5 : ℝ) * s)) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [this]; ring
      rw [hrew] at hbd
      refine hbd.trans (mul_le_mul_of_nonneg_right ?_ (psiMinus_pos (6 / 5) s).le)
      obtain ⟨hL1, hL2, hL3, hL4, hL5, hL6, hL7, hL8⟩ := grid_log_bounds
      by_cases h1 : s ≤ 9 / 4
      · exact contraction_on_subinterval (by norm_num) le_rfl (by norm_num) hs2 h1
          (by simpa [show (6 / 5 : ℝ) * (9 / 4 - 3) = -(9 / 10 : ℝ) by norm_num] using
            exp_neg_le_of_taylor6 (r := 9 / 10) (c := 41 / 100) (by norm_num) (by norm_num) (by norm_num))
          hL1 (by norm_num)
      · by_cases h2 : s ≤ 5 / 2
        · exact contraction_on_subinterval (by norm_num) (by norm_num) (by norm_num) (by linarith) h2
            (by simpa [show (6 / 5 : ℝ) * (5 / 2 - 3) = -(3 / 5 : ℝ) by norm_num] using
              exp_neg_le_of_taylor6 (r := 3 / 5) (c := 55 / 100) (by norm_num) (by norm_num) (by norm_num))
            hL2 (by norm_num)
        · by_cases h3 : s ≤ 11 / 4
          · exact contraction_on_subinterval (by norm_num) (by norm_num) (by norm_num) (by linarith) h3
              (by simpa [show (6 / 5 : ℝ) * (11 / 4 - 3) = -(3 / 10 : ℝ) by norm_num] using
                exp_neg_le_of_taylor6 (r := 3 / 10) (c := 75 / 100) (by norm_num) (by norm_num) (by norm_num))
              hL3 (by norm_num)
          · by_cases h4 : s ≤ 3
            · exact contraction_on_subinterval (by norm_num) (by norm_num) (by norm_num) (by linarith) h4
                (by norm_num : Real.exp ((6 / 5 : ℝ) * (3 - 3)) ≤ 1) hL4 (by norm_num)
            · by_cases h5 : s ≤ 13 / 4
              · exact contraction_on_subinterval (by norm_num) (by norm_num) (by norm_num) (by linarith) h5
                  (by simpa [show (6 / 5 : ℝ) * (13 / 4 - 3) = (3 : ℕ) / (10 : ℕ) by norm_num] using
                    exp_rat_le_of_pow (p := 3) (q := 10) (c := 136 / 100) (by norm_num) (by norm_num) (by norm_num))
                  hL5 (by norm_num)
              · by_cases h6 : s ≤ 7 / 2
                · exact contraction_on_subinterval (by norm_num) (by norm_num) (by norm_num) (by linarith) h6
                    (by simpa [show (6 / 5 : ℝ) * (7 / 2 - 3) = (3 : ℕ) / (5 : ℕ) by norm_num] using
                      exp_rat_le_of_pow (p := 3) (q := 5) (c := 183 / 100) (by norm_num) (by norm_num) (by norm_num))
                    hL6 (by norm_num)
                · by_cases h7 : s ≤ 15 / 4
                  · exact contraction_on_subinterval (by norm_num) (by norm_num) (by norm_num) (by linarith) h7
                      (by simpa [show (6 / 5 : ℝ) * (15 / 4 - 3) = (9 : ℕ) / (10 : ℕ) by norm_num] using
                        exp_rat_le_of_pow (p := 9) (q := 10) (c := 247 / 100) (by norm_num) (by norm_num) (by norm_num))
                      hL7 (by norm_num)
                  · exact contraction_on_subinterval (by norm_num) (by norm_num) le_rfl (by linarith) hs4.le
                      (by simpa [show (6 / 5 : ℝ) * (4 - 3) = 6 / 5 by norm_num] using he65)
                      hL8 (by norm_num)

/-! ## Section 4: Global Fundamental Lemma & Full Rosser–Iwaniec Linear Sieve (`β = 2`) -/

/-- Strict decrease of `(primesLtList p).length` for any prime `p < z`. -/
private lemma primesLtList_length_lt_of_mem {z : ℝ} {p : ℕ} (hp : p ∈ primesLtList z) :
    (primesLtList (p : ℝ)).length < (primesLtList z).length := by
  rw [← List.toFinset_card_of_nodup (primesLtList_nodup (p : ℝ)),
      ← List.toFinset_card_of_nodup (primesLtList_nodup z)]
  refine Finset.card_lt_card ?_
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨p, List.mem_toFinset.mpr hp, ?_⟩
    rw [List.mem_toFinset, mem_primesLtList]
    intro h; exact lt_irrefl (p : ℝ) h.2
  · intro q hq
    rw [List.mem_toFinset, mem_primesLtList] at hq ⊢
    exact ⟨hq.1, lt_trans hq.2 (mem_primesLtList.mp hp).2⟩

/-- Monotonicity of `(primesLtList z).length` in `z`. -/
private lemma primesLtList_length_mono {w z : ℝ} (hwz : w ≤ z) :
    (primesLtList w).length ≤ (primesLtList z).length := by
  rw [← List.toFinset_card_of_nodup (primesLtList_nodup w),
      ← List.toFinset_card_of_nodup (primesLtList_nodup z)]
  refine Finset.card_le_card fun q hq => ?_
  rw [List.mem_toFinset, mem_primesLtList] at hq ⊢
  exact ⟨hq.1, lt_of_lt_of_le hq.2 hwz⟩

/-- Elementary exponential decay: `∀ c > 0, ∃ B ≥ 4, B * Real.exp (-2 * (B - 1)) ≤ c`. -/
private lemma exists_B_mul_exp_le {c : ℝ} (hc : 0 < c) :
    ∃ B : ℝ, 4 ≤ B ∧ B * Real.exp (-(2 * (B - 1))) ≤ c := by
  set B : ℝ := max 4 (1 / c + 2) with hB_def
  have hB4 : 4 ≤ B := le_max_left _ _
  have hB_ge : 1 / c + 2 ≤ B := le_max_right _ _
  refine ⟨B, hB4, ?_⟩
  have hbm1 : 1 ≤ B - 1 := by linarith
  -- `Real.exp (2 * (B - 1)) ≥ (2 * (B - 1))^2 / 2 = 2 * (B - 1)^2 ≥ B * (B - 1)`
  have ht := Real.sum_le_exp_of_nonneg (show 0 ≤ 2 * (B - 1) by linarith) 3
  have hsum : ∑ i ∈ Finset.range 3, (2 * (B - 1)) ^ i / (i.factorial : ℝ) =
      1 + 2 * (B - 1) + 2 * (B - 1) ^ 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]; ring
  rw [hsum] at ht
  have hge_B : B * (1 / c) ≤ Real.exp (2 * (B - 1)) := by
    have h1 : B ≤ 2 * (B - 1) := by linarith
    have h2 : 1 / c ≤ B - 1 := by linarith
    have h3 : B * (1 / c) ≤ 2 * (B - 1) * (B - 1) :=
      mul_le_mul h1 h2 (by positivity) (by linarith)
    nlinarith
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  have hmul := mul_le_mul_of_nonneg_left hge_B hc.le
  have hcancel : c * (B * (1 / c)) = B := by field_simp [hc.ne']
  linarith

/-- Helper: bound the lower-tail integral `(1 / sw) * ∫_{sw}^{s2} e^{-β(u-1)} du` for `β = 6/5`, `sw ≥ 4`. -/
private lemma tail_exp_bound_six_fifths {C₂ B s s2 : ℝ} (hC₂ : 1 ≤ C₂) (hB : 4 ≤ B)
    (hs2 : 2 ≤ s) (hsw_le : B * s ≤ s2) :
    (C₂ * (1 / (B * s)) * (∫ u in (B * s)..s2, psiPlus (6 / 5) (u - 1)) +
        (C₂ - 1) * psiPlus (6 / 5) (B * s - 1)) ≤
      (8 * C₂) * Real.exp (-(2 * (B - 1))) * Real.exp (-((6 / 5 : ℝ) * s)) := by
  have hBs8 : 8 ≤ B * s := by nlinarith
  have hae : ∀ᵐ u ∂volume, u ∈ Set.uIoc (B * s) s2 →
      psiPlus (6 / 5) (u - 1) = Real.exp (-((6 / 5 : ℝ) * (u - 1))) := by
    filter_upwards with u hu
    rw [Set.uIoc_of_le hsw_le] at hu
    unfold psiPlus; rw [if_neg (by linarith [hu.1])]
  rw [intervalIntegral.integral_congr_ae hae, integral_exp_neg_shift (by norm_num : (0 : ℝ) < 6 / 5)]
  have hpsi_eq : psiPlus (6 / 5) (B * s - 1) = Real.exp (-((6 / 5 : ℝ) * (B * s - 1))) := by
    unfold psiPlus; rw [if_neg (by linarith)]
  rw [hpsi_eq]
  have heq : Real.exp (-((6 / 5 : ℝ) * (B * s - 1))) =
      Real.exp (6 / 5) * Real.exp (-((6 / 5 : ℝ) * (B - 1) * s)) * Real.exp (-((6 / 5 : ℝ) * s)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hint_le : (Real.exp (-((6 / 5 : ℝ) * (B * s - 1))) - Real.exp (-((6 / 5 : ℝ) * (s2 - 1)))) / (6 / 5) ≤
      Real.exp (-((6 / 5 : ℝ) * (B * s - 1))) := by
    have hp1 := Real.exp_pos (-((6 / 5 : ℝ) * (B * s - 1)))
    have hp2 := Real.exp_pos (-((6 / 5 : ℝ) * (s2 - 1)))
    linarith
  have hinv_le1 : 1 / (B * s) ≤ 1 := by rw [div_le_iff₀ (by linarith)]; linarith
  have h1 : C₂ * (1 / (B * s)) *
      ((Real.exp (-((6 / 5 : ℝ) * (B * s - 1))) - Real.exp (-((6 / 5 : ℝ) * (s2 - 1)))) / (6 / 5)) ≤
      C₂ * Real.exp (-((6 / 5 : ℝ) * (B * s - 1))) := by
    calc C₂ * (1 / (B * s)) *
          ((Real.exp (-((6 / 5 : ℝ) * (B * s - 1))) - Real.exp (-((6 / 5 : ℝ) * (s2 - 1)))) / (6 / 5))
        ≤ C₂ * (1 / (B * s)) * Real.exp (-((6 / 5 : ℝ) * (B * s - 1))) :=
          mul_le_mul_of_nonneg_left hint_le (by positivity)
      _ ≤ C₂ * 1 * Real.exp (-((6 / 5 : ℝ) * (B * s - 1))) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hinv_le1 (by linarith)) (Real.exp_pos _).le
      _ = C₂ * Real.exp (-((6 / 5 : ℝ) * (B * s - 1))) := by ring
  have hexp_dec : Real.exp (-((6 / 5 : ℝ) * (B - 1) * s)) ≤ Real.exp (-(2 * (B - 1))) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have he4 : Real.exp (6 / 5 : ℝ) ≤ 4 := exp_one_pt_two_lt_four
  have h2 : (2 * C₂) * Real.exp (-((6 / 5 : ℝ) * (B * s - 1))) ≤
      (8 * C₂) * Real.exp (-(2 * (B - 1))) * Real.exp (-((6 / 5 : ℝ) * s)) := by
    rw [heq]
    have hmul : Real.exp (6 / 5) * Real.exp (-((6 / 5 : ℝ) * (B - 1) * s)) ≤
        4 * Real.exp (-(2 * (B - 1))) :=
      mul_le_mul he4 hexp_dec (Real.exp_pos _).le (by norm_num)
    have hpos1 : 0 ≤ (2 * C₂) := by linarith
    have hpos2 : 0 ≤ Real.exp (-((6 / 5 : ℝ) * s)) := (Real.exp_pos _).le
    calc (2 * C₂) * (Real.exp (6 / 5) * Real.exp (-((6 / 5 : ℝ) * (B - 1) * s)) * Real.exp (-((6 / 5 : ℝ) * s)))
        = (2 * C₂) * (Real.exp (6 / 5) * Real.exp (-((6 / 5 : ℝ) * (B - 1) * s))) * Real.exp (-((6 / 5 : ℝ) * s)) := by ring
      _ ≤ (2 * C₂) * (4 * Real.exp (-(2 * (B - 1)))) * Real.exp (-((6 / 5 : ℝ) * s)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmul hpos1) hpos2
      _ = (8 * C₂) * Real.exp (-(2 * (B - 1))) * Real.exp (-((6 / 5 : ℝ) * s)) := by ring
  have h3 : (C₂ - 1) * Real.exp (-((6 / 5 : ℝ) * (B * s - 1))) ≤
      C₂ * Real.exp (-((6 / 5 : ℝ) * (B * s - 1))) := by
    nlinarith [Real.exp_pos (-((6 / 5 : ℝ) * (B * s - 1)))]
  linarith

/-- **GLOBAL FUNDAMENTAL LEMMA FOR ROSSER (`β = 2`) WEIGHTS**:
For ANY `K ≥ 1`, there exists `M > 0` (depending **ONLY** on `K`) such that for EVERY
`ω` satisfying `LinearSieveDensity ω K`, EVERY `z ≥ 2`, and EVERY `D`:
- If `z ≤ D`: `rosserV ω true D (primesLtList z) - siftProd ω z ≤ M * siftProd ω z * psiPlus (6 / 5) (log D / log z)`
- If `z^2 ≤ D`: `siftProd ω z - rosserV ω false D (primesLtList z) ≤ M * siftProd ω z * psiMinus (6 / 5) (log D / log z)`. -/
theorem fundamental_lemma_rosser (K : ℝ) (hK : 1 ≤ K) :
    ∃ M : ℝ, 0 < M ∧
      ∀ {ω : ℕ → ℝ}, LinearSieveDensity ω K →
        ∀ z D : ℝ, 2 ≤ z →
          (z ≤ D →
            rosserV ω true D (primesLtList z) - siftProd ω z ≤
              M * siftProd ω z * psiPlus (6 / 5) (Real.log D / Real.log z)) ∧
          (z ^ 2 ≤ D →
            siftProd ω z - rosserV ω false D (primesLtList z) ≤
              M * siftProd ω z * psiMinus (6 / 5) (Real.log D / Real.log z)) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set C₂ : ℝ := 1 + K / Real.log 2 with hC₂_def
  have hC₂_ge1 : 1 ≤ C₂ := by
    have : 0 ≤ K / Real.log 2 := div_nonneg (by linarith) hlog2_pos.le
    linarith
  have hC₂_pos : 0 < C₂ := by linarith
  -- Choose `B ≥ 4` so `16 * C₂ * B * exp(-2*(B-1)) ≤ 1 / 1000`
  obtain ⟨B, hB4, hB_bd⟩ := exists_B_mul_exp_le (c := 1 / (16000 * C₂)) (by positivity)
  have hB_tail : 2 * B * (8 * C₂) * Real.exp (-(2 * (B - 1))) ≤ 1 / 1000 := by
    have hmul := mul_le_mul_of_nonneg_left hB_bd (show 0 ≤ 16 * C₂ by positivity)
    have hcancel : 16 * C₂ * (1 / (16000 * C₂)) = 1 / 1000 := by field_simp [hC₂_pos.ne']; norm_num
    linarith
  -- Choose `z₁ ≥ max (2^B) (exp (1000 * B * K))`
  set z₁ : ℝ := max (max ((2 : ℝ) ^ B) (Real.exp (1000 * B * K))) 16 with hz₁_def
  have hz₁_ge16 : 16 ≤ z₁ := le_max_right _ _
  have hz₁_ge2B : (2 : ℝ) ^ B ≤ z₁ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hz₁_geExp : Real.exp (1000 * B * K) ≤ z₁ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hlz₁_pos : 0 < Real.log z₁ := Real.log_pos (by linarith)
  set S_max : ℝ := ((⌊z₁⌋₊ + 3 : ℕ) : ℝ) * Real.log z₁ / Real.log 2 with hSmax_def
  have hSmax_ge3 : 3 ≤ S_max := by
    rw [hSmax_def, le_div_iff₀ hlog2_pos]
    have h1 : (3 : ℝ) ≤ ((⌊z₁⌋₊ + 3 : ℕ) : ℝ) := by push_cast; linarith
    have h2 : Real.log 2 ≤ Real.log z₁ := Real.log_le_log (by norm_num) (by linarith)
    nlinarith
  set U_max : ℝ := (Real.log z₁ / Real.log 2) * C₂ with hUmax_def
  set M : ℝ := max (3000 * Real.exp (18 / 5)) (2 * U_max ^ 2 * Real.exp ((6 / 5) * S_max)) with hM_def
  have hM_pos : 0 < M := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hM_ge1 : 3000 * Real.exp (18 / 5) ≤ M := le_max_left _ _
  have hM_ge2 : 2 * U_max ^ 2 * Real.exp ((6 / 5) * S_max) ≤ M := le_max_right _ _
  refine ⟨M, hM_pos, fun {ω} hω => ?_⟩
  -- Prove by strong induction on `N : ℕ` for all `z ≥ 2` with `(primesLtList z).length ≤ N`
  suffices hInd : ∀ N : ℕ, ∀ z D : ℝ, 2 ≤ z → (primesLtList z).length ≤ N →
      (z ≤ D → rosserV ω true D (primesLtList z) - siftProd ω z ≤
          M * siftProd ω z * psiPlus (6 / 5) (Real.log D / Real.log z)) ∧
      (z ^ 2 ≤ D → siftProd ω z - rosserV ω false D (primesLtList z) ≤
          M * siftProd ω z * psiMinus (6 / 5) (Real.log D / Real.log z)) by
    intro z D hz2
    exact hInd (primesLtList z).length z D hz2 le_rfl
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    -- Helper: prove the `s ≥ 3` (`z^3 ≤ D`) case for `V⁺` for ANY `z ≥ 2` with `(primesLtList z).length ≤ N`
    have hUp_ge3 : ∀ z D : ℝ, 2 ≤ z → (primesLtList z).length ≤ N → z ^ 3 ≤ D →
        rosserV ω true D (primesLtList z) - siftProd ω z ≤
          M * siftProd ω z * Real.exp (-((6 / 5 : ℝ) * (Real.log D / Real.log z))) := by
      intro z D hz2 hlen hz3
      have hPz : 0 < siftProd ω z := siftProd_pos_of_linearSieve hω z
      have hlz : 0 < Real.log z := Real.log_pos (by linarith)
      have hz0 : 0 < z := by linarith
      have hzD : z < D := by
        have hsq : 4 ≤ z * z := by nlinarith
        have hcube : z ^ 3 = z * z * z := by ring
        nlinarith
      have hlD : 0 < Real.log D := Real.log_pos (by linarith)
      set s := Real.log D / Real.log z with hs_def
      have hs3 : 3 ≤ s := by
        rw [hs_def, le_div_iff₀ hlz, show 3 * Real.log z = Real.log (z ^ 3) by rw [Real.log_pow]; ring]
        exact Real.log_le_log (pow_pos hz0 3) hz3
      by_cases hz_small : z < z₁
      · -- Base case `2 ≤ z < z₁`
        by_cases hD_big : z ^ (⌊z⌋₊ + 3) < D
        · rw [rosserV_eq_siftProd_of_large_D ω hz2 hD_big true, sub_self]
          positivity
        · push Not at hD_big
          have hfl_le : ⌊z⌋₊ ≤ ⌊z₁⌋₊ := Nat.floor_mono hz_small.le
          have hs_le : s ≤ S_max := by
            rw [hs_def, hSmax_def]
            have hlD_le : Real.log D ≤ ((⌊z₁⌋₊ + 3 : ℕ) : ℝ) * Real.log z₁ := by
              calc Real.log D ≤ Real.log (z ^ (⌊z⌋₊ + 3)) := Real.log_le_log (by linarith) hD_big
                _ = ((⌊z⌋₊ + 3 : ℕ) : ℝ) * Real.log z := by rw [Real.log_pow]
                _ ≤ ((⌊z₁⌋₊ + 3 : ℕ) : ℝ) * Real.log z₁ := by
                    gcongr
            have hlz_ge : Real.log 2 ≤ Real.log z := Real.log_le_log (by norm_num) hz2
            exact div_le_div₀ (by positivity) hlD_le hlog2_pos hlz_ge
          have htriv : rosserV ω true D (primesLtList z) - siftProd ω z ≤ (siftProd ω z)⁻¹ := by
            have habs := abs_rosserV_le_inv_listSiftProd hω.nonneg hω.lt_one (primesLtList z) true D
            rw [listSiftProd_primesLtList] at habs
            linarith [(abs_le.mp habs).2]
          have hinv_le : (siftProd ω z)⁻¹ ≤ U_max := by
            calc (siftProd ω z)⁻¹ ≤ (Real.log z / Real.log 2) * C₂ := inv_siftProd_le hω hz2
              _ ≤ U_max := by
                  rw [hUmax_def]; gcongr
          have hexp_ge : Real.exp (-((6 / 5 : ℝ) * S_max)) ≤ Real.exp (-((6 / 5 : ℝ) * s)) :=
            Real.exp_le_exp.mpr (by nlinarith)
          have hU_sq : (siftProd ω z)⁻¹ ≤ U_max ^ 2 * siftProd ω z := by
            have h1 : ((siftProd ω z)⁻¹) ^ 2 ≤ U_max ^ 2 :=
              pow_le_pow_left₀ (inv_nonneg.mpr hPz.le) hinv_le 2
            have h2 := mul_le_mul_of_nonneg_right h1 hPz.le
            have h3 : ((siftProd ω z)⁻¹) ^ 2 * siftProd ω z = (siftProd ω z)⁻¹ := by
              field_simp [hPz.ne']
            linarith
          have hM_mul : U_max ^ 2 ≤ M * Real.exp (-((6 / 5 : ℝ) * S_max)) := by
            rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
            have : 0 ≤ U_max ^ 2 * Real.exp ((6 / 5) * S_max) := by positivity
            linarith
          calc rosserV ω true D (primesLtList z) - siftProd ω z
              ≤ (siftProd ω z)⁻¹ := htriv
            _ ≤ U_max ^ 2 * siftProd ω z := hU_sq
            _ ≤ (M * Real.exp (-((6 / 5 : ℝ) * S_max))) * siftProd ω z :=
                mul_le_mul_of_nonneg_right hM_mul hPz.le
            _ ≤ M * siftProd ω z * Real.exp (-((6 / 5 : ℝ) * s)) := by
                have := mul_le_mul_of_nonneg_left hexp_ge (show 0 ≤ M * siftProd ω z by positivity)
                linarith
      · -- Inductive case `z₁ ≤ z`
        push Not at hz_small
        set w : ℝ := z ^ ((1 : ℝ) / B) with hw_def
        have hB_pos : 0 < B := by linarith
        have hw2 : 2 ≤ w := by
          rw [hw_def]
          have h1 : (2 : ℝ) = ((2 : ℝ) ^ B) ^ ((1 : ℝ) / B) := by
            rw [← Real.rpow_mul (by norm_num), mul_one_div_cancel hB_pos.ne', Real.rpow_one]
          rw [h1]
          exact Real.rpow_le_rpow (by positivity) (hz₁_ge2B.trans hz_small) (by positivity)
        have hlw_eq : Real.log w = Real.log z / B := by
          rw [hw_def, Real.log_rpow hz0]; ring
        have hlw_pos : 0 < Real.log w := Real.log_pos (by linarith)
        have hwz : w ≤ z := by
          have : Real.log w ≤ Real.log z := by rw [hlw_eq]; exact div_le_self hlz.le (by linarith)
          exact (Real.log_le_log_iff (by linarith) hz0).mp this
        have hKw_le : K / Real.log w ≤ 1 / 1000 := by
          rw [hlw_eq, div_div_eq_mul_div, div_le_iff₀ hlz]
          have hlogz : 1000 * B * K ≤ Real.log z := by
            have := Real.log_le_log (Real.exp_pos _) (hz₁_geExp.trans hz_small)
            rwa [Real.log_exp] at this
          linarith
        -- Split `Δ⁺(D, z) = Δ⁺(D, w) + ∑_{w ≤ p < z} ω(p) * Δ⁻(D/p, p)`
        rw [rosserDelta_true_buchstab ω hwz hz3]
        -- Also expand `Δ⁺(D, w) = 0 + ∑_{2 ≤ p < w} ω(p) * Δ⁻(D/p, p)` (since `Δ⁺(D, 2) = 0`!)
        have hw3 : w ^ 3 ≤ D := le_trans (pow_le_pow_left₀ (by linarith) hwz 3) hz3
        rw [rosserDelta_true_buchstab ω hw2 hw3]
        have h2zero : rosserV ω true D (primesLtList 2) - siftProd ω 2 = 0 := by
          rw [primesLtList_eq_nil_of_le_two le_rfl, siftProd_two_eq_one]; simp [rosserV]
        rw [h2zero, zero_add]
        -- Apply IH to every prime `p < w` and every prime `p ∈ [w, z)`!
        have hIH_minus : ∀ p : ℕ, p ∈ primesLtList z →
            siftProd ω (p : ℝ) - rosserV ω false (D / (p : ℝ)) (primesLtList (p : ℝ)) ≤
              M * siftProd ω (p : ℝ) * psiMinus (6 / 5) (Real.log D / Real.log (p : ℝ) - 1) := by
          intro p hp
          have hlt_len : (primesLtList (p : ℝ)).length < N :=
            lt_of_lt_of_le (primesLtList_length_lt_of_mem hp) hlen
          obtain ⟨hpr, hpz⟩ := mem_primesLtList.mp hp
          have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpr.two_le
          have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
          have hp2D : (p : ℝ) ^ 2 ≤ D / (p : ℝ) := by
            rw [le_div_iff₀ hp0]
            have h1 : (p : ℝ) ^ 2 * (p : ℝ) = (p : ℝ) ^ 3 := by ring
            rw [h1]
            exact le_trans (pow_le_pow_left₀ hp0.le hpz.le 3) hz3
          have hbound := (ih (primesLtList (p : ℝ)).length hlt_len (p : ℝ) (D / (p : ℝ)) hp2 le_rfl).2 hp2D
          rwa [log_div_div_log_eq (by linarith) (by linarith)] at hbound
        -- Bound the upper sum `∑_{w ≤ p < z}`
        have hsum_hi : ∑ p ∈ (primesIcoList w z).toFinset,
            ω p * (siftProd ω (p : ℝ) - rosserV ω false (D / (p : ℝ)) (primesLtList (p : ℝ))) ≤
            M * (siftProd ω z *
              ((1 + K / Real.log w) * (Real.log z / Real.log D) *
                (∫ u in s..(Real.log D / Real.log w), psiMinus (6 / 5) (u - 1)) +
              (K / Real.log w) * psiMinus (6 / 5) (s - 1))) := by
          have h1 : ∑ p ∈ (primesIcoList w z).toFinset,
              ω p * (siftProd ω (p : ℝ) - rosserV ω false (D / (p : ℝ)) (primesLtList (p : ℝ))) ≤
              M * ∑ p ∈ (primesIcoList w z).toFinset,
                ω p * siftProd ω (p : ℝ) * psiMinus (6 / 5) (Real.log D / Real.log (p : ℝ) - 1) := by
            rw [Finset.mul_sum]
            refine Finset.sum_le_sum fun p hp => ?_
            rw [List.mem_toFinset] at hp
            unfold primesIcoList at hp; rw [List.mem_filter] at hp
            have hbd := hIH_minus p hp.1
            have := hω.nonneg p
            nlinarith
          exact h1.trans (mul_le_mul_of_nonneg_left
            (sum_omega_siftProd_mul_antitone_le hω hw2 hwz hzD
              (fun t _ => (psiMinus_pos _ t).le) (psiMinus_antitone (by norm_num))) hM_pos.le)
        -- Bound the lower sum `∑_{2 ≤ p < w}`
        have hsum_lo : ∑ p ∈ (primesIcoList 2 w).toFinset,
            ω p * (siftProd ω (p : ℝ) - rosserV ω false (D / (p : ℝ)) (primesLtList (p : ℝ))) ≤
            M * (siftProd ω w *
              (C₂ * (Real.log w / Real.log D) *
                (∫ u in (Real.log D / Real.log w)..(Real.log D / Real.log 2), psiMinus (6 / 5) (u - 1)) +
              (C₂ - 1) * psiMinus (6 / 5) (Real.log D / Real.log w - 1))) := by
          have hwD : w < D := lt_of_le_of_lt hwz hzD
          have h1 : ∑ p ∈ (primesIcoList 2 w).toFinset,
              ω p * (siftProd ω (p : ℝ) - rosserV ω false (D / (p : ℝ)) (primesLtList (p : ℝ))) ≤
              M * ∑ p ∈ (primesIcoList 2 w).toFinset,
                ω p * siftProd ω (p : ℝ) * psiMinus (6 / 5) (Real.log D / Real.log (p : ℝ) - 1) := by
            rw [Finset.mul_sum]
            refine Finset.sum_le_sum fun p hp => ?_
            rw [List.mem_toFinset] at hp
            unfold primesIcoList at hp; rw [List.mem_filter] at hp
            have hpz : p ∈ primesLtList z := by
              rw [mem_primesLtList] at *
              exact ⟨hp.1.1, lt_of_lt_of_le hp.1.2 hwz⟩
            have hbd := hIH_minus p hpz
            exact mul_le_mul_of_nonneg_left hbd (hω.nonneg p) |>.trans_eq (by ring)
          have hsbp := sum_omega_siftProd_mul_antitone_le hω le_rfl hw2 hwD
            (fun t _ => (psiMinus_pos _ t).le) (psiMinus_antitone (by norm_num : (0 : ℝ) ≤ 6 / 5))
          have hCsub : K / Real.log 2 = C₂ - 1 := by rw [hC₂_def]; ring
          rw [← hC₂_def, hCsub] at hsbp
          exact h1.trans (mul_le_mul_of_nonneg_left hsbp hM_pos.le)
        -- Combine upper and lower sums!
        have hsw_eq : Real.log D / Real.log w = B * s := by
          rw [hlw_eq, hs_def]; field_simp [hlz.ne', hB_pos.ne']
        have hs_inv_eq : Real.log z / Real.log D = 1 / s := by
          rw [hs_def]; field_simp [hlD.ne', hlz.ne']
        have hsw_inv_eq : Real.log w / Real.log D = 1 / (B * s) := by
          rw [hlw_eq, hs_def]; field_simp [hlD.ne', hlz.ne', hB_pos.ne']
        -- Upper term bound `≤ ((1 + 1/1000) * (95/100) + (1/1000) * 4) * e^{-(6/5)s}`
        have hhi_num :
            (1 + K / Real.log w) * (Real.log z / Real.log D) *
                (∫ u in s..(Real.log D / Real.log w), psiMinus (6 / 5) (u - 1)) +
              (K / Real.log w) * psiMinus (6 / 5) (s - 1) ≤
            (96 / 100 : ℝ) * Real.exp (-((6 / 5 : ℝ) * s)) := by
          rw [hs_inv_eq, hsw_eq]
          have hsw_ge : s ≤ B * s := by nlinarith
          have hint_bd : (1 / s) * (∫ u in s..(B * s), psiMinus (6 / 5) (u - 1)) ≤
              (95 / 100 : ℝ) * Real.exp (-((6 / 5 : ℝ) * s)) := by
            unfold psiMinus
            rw [integral_exp_neg_shift (by norm_num : (0 : ℝ) < 6 / 5)]
            have h1 : (Real.exp (-((6 / 5 : ℝ) * (s - 1))) - Real.exp (-((6 / 5 : ℝ) * (B * s - 1)))) / (6 / 5) ≤
                Real.exp (6 / 5) / (6 / 5) * Real.exp (-((6 / 5 : ℝ) * s)) := by
              have heq : Real.exp (-((6 / 5 : ℝ) * (s - 1))) = Real.exp (6 / 5) * Real.exp (-((6 / 5 : ℝ) * s)) := by
                rw [← Real.exp_add]; congr 1; ring
              have hpos := Real.exp_pos (-((6 / 5 : ℝ) * (B * s - 1)))
              rw [heq]; linarith
            have he65 : Real.exp (6 / 5 : ℝ) ≤ 333 / 100 := by
              simpa using exp_rat_le_of_pow (p := 6) (q := 5) (c := 333 / 100) (by norm_num) (by norm_num) (by norm_num)
            have hinv : 1 / s ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hs3
            have hc : (1 / 3 : ℝ) * (Real.exp (6 / 5) / (6 / 5)) ≤ 95 / 100 := by linarith
            calc (1 / s) * ((Real.exp (-((6 / 5 : ℝ) * (s - 1))) - Real.exp (-((6 / 5 : ℝ) * (B * s - 1)))) / (6 / 5))
                ≤ (1 / s) * (Real.exp (6 / 5) / (6 / 5) * Real.exp (-((6 / 5 : ℝ) * s))) :=
                  mul_le_mul_of_nonneg_left h1 (by positivity)
              _ ≤ (1 / 3) * (Real.exp (6 / 5) / (6 / 5) * Real.exp (-((6 / 5 : ℝ) * s))) :=
                  mul_le_mul_of_nonneg_right hinv (by positivity)
              _ ≤ (95 / 100) * Real.exp (-((6 / 5 : ℝ) * s)) := by nlinarith [Real.exp_pos (-((6 / 5 : ℝ) * s))]
          have hsub1 : psiMinus (6 / 5) (s - 1) ≤ 4 * Real.exp (-((6 / 5 : ℝ) * s)) := by
            unfold psiMinus
            have heq : Real.exp (-((6 / 5 : ℝ) * (s - 1))) = Real.exp (6 / 5) * Real.exp (-((6 / 5 : ℝ) * s)) := by
              rw [← Real.exp_add]; congr 1; ring
            rw [heq]
            exact mul_le_mul_of_nonneg_right exp_one_pt_two_lt_four (Real.exp_pos _).le
          have hKw_nn : 0 ≤ K / Real.log w := div_nonneg (by linarith) hlw_pos.le
          have hp1 : (1 + K / Real.log w) * ((1 / s) * ∫ u in s..(B * s), psiMinus (6 / 5) (u - 1)) ≤
              (1 + 1 / 1000) * ((95 / 100 : ℝ) * Real.exp (-((6 / 5 : ℝ) * s))) := by
            refine mul_le_mul (by linarith) hint_bd ?_ (by norm_num)
            exact mul_nonneg (by positivity)
              (intervalIntegral.integral_nonneg hsw_ge fun _ _ => (psiMinus_pos _ _).le)
          have hp2 : (K / Real.log w) * psiMinus (6 / 5) (s - 1) ≤
              (1 / 1000) * (4 * Real.exp (-((6 / 5 : ℝ) * s))) :=
            mul_le_mul hKw_le hsub1 (psiMinus_pos _ _).le (by norm_num)
          have hreassoc : (1 + K / Real.log w) * (1 / s) * (∫ u in s..(B * s), psiMinus (6 / 5) (u - 1)) =
              (1 + K / Real.log w) * ((1 / s) * ∫ u in s..(B * s), psiMinus (6 / 5) (u - 1)) := by ring
          rw [hreassoc]
          nlinarith [Real.exp_pos (-((6 / 5 : ℝ) * s))]
        -- Lower term bound `≤ (1/1000) * P(z) * e^{-(6/5)s}`
        have hlo_num :
            siftProd ω w *
              (C₂ * (Real.log w / Real.log D) *
                (∫ u in (Real.log D / Real.log w)..(Real.log D / Real.log 2), psiMinus (6 / 5) (u - 1)) +
              (C₂ - 1) * psiMinus (6 / 5) (Real.log D / Real.log w - 1)) ≤
            siftProd ω z * ((1 / 1000 : ℝ) * Real.exp (-((6 / 5 : ℝ) * s))) := by
          rw [hsw_eq, hsw_inv_eq]
          have hsw_le2 : B * s ≤ Real.log D / Real.log 2 := by
            rw [← hsw_eq]
            exact div_le_div_of_nonneg_left hlD.le hlog2_pos (Real.log_le_log (by norm_num) hw2)
          have hPw_le : siftProd ω w ≤ siftProd ω z * (2 * B) := by
            have hr := siftProd_le_mul_ratio hω hw2 hwz
            have hlograt : Real.log z / Real.log w = B := by rw [hlw_eq]; field_simp [hlz.ne', hB_pos.ne']
            rw [hlograt] at hr
            calc siftProd ω w ≤ siftProd ω z * (B * (1 + K / Real.log w)) := hr
              _ ≤ siftProd ω z * (2 * B) :=
                  mul_le_mul_of_nonneg_left (by nlinarith) hPz.le
          have htail_eq :
              C₂ * (1 / (B * s)) * (∫ u in (B * s)..(Real.log D / Real.log 2), psiMinus (6 / 5) (u - 1)) +
                (C₂ - 1) * psiMinus (6 / 5) (B * s - 1) =
              C₂ * (1 / (B * s)) * (∫ u in (B * s)..(Real.log D / Real.log 2), psiPlus (6 / 5) (u - 1)) +
                (C₂ - 1) * psiPlus (6 / 5) (B * s - 1) := by
            have hBs8 : 8 ≤ B * s := by nlinarith
            have heq1 : psiMinus (6 / 5) (B * s - 1) = psiPlus (6 / 5) (B * s - 1) := by
              unfold psiMinus psiPlus; rw [if_neg (by linarith)]
            have hae : ∀ᵐ u ∂volume, u ∈ Set.uIoc (B * s) (Real.log D / Real.log 2) →
                psiMinus (6 / 5) (u - 1) = psiPlus (6 / 5) (u - 1) := by
              filter_upwards with u hu
              rw [Set.uIoc_of_le hsw_le2] at hu
              unfold psiMinus psiPlus; rw [if_neg (by linarith [hu.1])]
            rw [heq1, intervalIntegral.integral_congr_ae hae]
          rw [htail_eq]
          have htail_bd := tail_exp_bound_six_fifths hC₂_ge1 hB4 (by linarith) hsw_le2
          have hBs8 : 8 ≤ B * s := by nlinarith
          have htail_nn : 0 ≤ C₂ * (1 / (B * s)) *
              (∫ u in (B * s)..(Real.log D / Real.log 2), psiPlus (6 / 5) (u - 1)) +
              (C₂ - 1) * psiPlus (6 / 5) (B * s - 1) := by
            have hint_nn : 0 ≤ ∫ u in (B * s)..(Real.log D / Real.log 2), psiPlus (6 / 5) (u - 1) :=
              intervalIntegral.integral_nonneg hsw_le2 fun u hu => (psiPlus_pos (by linarith [hu.1])).le
            have h2 : 0 ≤ (C₂ - 1) * psiPlus (6 / 5) (B * s - 1) :=
              mul_nonneg (by linarith) (psiPlus_pos (by linarith)).le
            have h1 : 0 ≤ C₂ * (1 / (B * s)) * (∫ u in (B * s)..(Real.log D / Real.log 2), psiPlus (6 / 5) (u - 1)) := by
              have : 0 < B * s := by linarith
              positivity
            linarith
          calc siftProd ω w * _
              ≤ (siftProd ω z * (2 * B)) *
                  ((8 * C₂) * Real.exp (-(2 * (B - 1))) * Real.exp (-((6 / 5 : ℝ) * s))) :=
                mul_le_mul hPw_le htail_bd htail_nn (by positivity)
            _ = siftProd ω z * ((2 * B * (8 * C₂) * Real.exp (-(2 * (B - 1)))) * Real.exp (-((6 / 5 : ℝ) * s))) := by ring
            _ ≤ siftProd ω z * ((1 / 1000 : ℝ) * Real.exp (-((6 / 5 : ℝ) * s))) := by
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right hB_tail (Real.exp_pos _).le) hPz.le
        have htotal := add_le_add hsum_lo hsum_hi
        have hcomb :
            M * (siftProd ω z * ((1 / 1000 : ℝ) * Real.exp (-((6 / 5 : ℝ) * s)))) +
              M * (siftProd ω z * ((96 / 100 : ℝ) * Real.exp (-((6 / 5 : ℝ) * s)))) ≤
            M * siftProd ω z * Real.exp (-((6 / 5 : ℝ) * s)) := by
          have : 0 < M * siftProd ω z * Real.exp (-((6 / 5 : ℝ) * s)) := by positivity
          linarith
        have h1 : M * (siftProd ω w * _) ≤ M * (siftProd ω z * ((1 / 1000 : ℝ) * Real.exp (-((6 / 5 : ℝ) * s)))) :=
          mul_le_mul_of_nonneg_left hlo_num hM_pos.le
        have h2 : M * (siftProd ω z * _) ≤ M * (siftProd ω z * ((96 / 100 : ℝ) * Real.exp (-((6 / 5 : ℝ) * s)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hhi_num hPz.le) hM_pos.le
        linarith
    -- Now prove both parts of `ih` for any `z ≥ 2` with `(primesLtList z).length ≤ N`!
    intro z D hz2 hlen
    have hPz : 0 < siftProd ω z := siftProd_pos_of_linearSieve hω z
    have hlz : 0 < Real.log z := Real.log_pos (by linarith)
    have hz0 : 0 < z := by linarith
    constructor
    · -- Part 1: `z ≤ D → V⁺(D, z) - P(z) ≤ M * P(z) * psiPlus (6 / 5) s`
      intro hzD
      by_cases hz3 : z ^ 3 ≤ D
      · have hbd := hUp_ge3 z D hz2 hlen hz3
        have hs3 : 3 ≤ Real.log D / Real.log z := by
          rw [le_div_iff₀ hlz, show 3 * Real.log z = Real.log (z ^ 3) by rw [Real.log_pow]; ring]
          exact Real.log_le_log (pow_pos hz0 3) hz3
        have hpsi_ge : Real.exp (-((6 / 5 : ℝ) * (Real.log D / Real.log z))) ≤
            psiPlus (6 / 5) (Real.log D / Real.log z) := by
          unfold psiPlus
          split_ifs with hle
          · have heq : Real.log D / Real.log z = 3 := by linarith
            rw [heq, show (3 : ℝ) / 3 = 1 by norm_num, mul_one, show (6 / 5 : ℝ) * 3 = 3 * (6 / 5) by ring]
            linarith [Real.exp_pos (-(3 * (6 / 5 : ℝ)))]
          · exact le_rfl
        exact hbd.trans (mul_le_mul_of_nonneg_left hpsi_ge (by positivity))
      · -- `z ≤ D < z ^ 3` (`1 ≤ s < 3`)
        push Not at hz3
        have hs_lt3 : Real.log D / Real.log z < 3 := by
          rw [div_lt_iff₀ hlz, show 3 * Real.log z = Real.log (z ^ 3) by rw [Real.log_pow]; ring]
          exact Real.log_lt_log (by linarith) hz3
        have hs_ge1 : 1 ≤ Real.log D / Real.log z :=
          (one_le_div hlz).mpr (Real.log_le_log hz0 hzD)
        by_cases hz_small : z < z₁
        · -- `2 ≤ z < z₁` and `D < z^3 ≤ z₁^3`
          have hs_le : Real.log D / Real.log z ≤ S_max := by linarith
          have htriv : rosserV ω true D (primesLtList z) - siftProd ω z ≤ (siftProd ω z)⁻¹ := by
            have habs := abs_rosserV_le_inv_listSiftProd hω.nonneg hω.lt_one (primesLtList z) true D
            rw [listSiftProd_primesLtList] at habs
            linarith [(abs_le.mp habs).2]
          have hinv_le : (siftProd ω z)⁻¹ ≤ U_max := by
            calc (siftProd ω z)⁻¹ ≤ (Real.log z / Real.log 2) * C₂ := inv_siftProd_le hω hz2
              _ ≤ U_max := by rw [hUmax_def]; gcongr
          have hU_sq : (siftProd ω z)⁻¹ ≤ U_max ^ 2 * siftProd ω z := by
            have h1 : ((siftProd ω z)⁻¹) ^ 2 ≤ U_max ^ 2 :=
              pow_le_pow_left₀ (inv_nonneg.mpr hPz.le) hinv_le 2
            have h2 := mul_le_mul_of_nonneg_right h1 hPz.le
            have h3 : ((siftProd ω z)⁻¹) ^ 2 * siftProd ω z = (siftProd ω z)⁻¹ := by field_simp [hPz.ne']
            linarith
          have hpsi_ge : Real.exp (-((6 / 5 : ℝ) * S_max)) ≤ psiPlus (6 / 5) (Real.log D / Real.log z) := by
            unfold psiPlus; rw [if_pos hs_lt3.le]
            have h3s : 1 ≤ 3 / (Real.log D / Real.log z) := (one_le_div (by linarith)).mpr hs_lt3.le
            have hexp : Real.exp (-((6 / 5 : ℝ) * S_max)) ≤ Real.exp (-(3 * (6 / 5 : ℝ))) :=
              Real.exp_le_exp.mpr (by linarith)
            nlinarith [Real.exp_pos (-(3 * (6 / 5 : ℝ)))]
          have hM_mul : U_max ^ 2 ≤ M * Real.exp (-((6 / 5 : ℝ) * S_max)) := by
            rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
            have : 0 ≤ U_max ^ 2 * Real.exp ((6 / 5) * S_max) := by positivity
            linarith
          calc rosserV ω true D (primesLtList z) - siftProd ω z
              ≤ U_max ^ 2 * siftProd ω z := htriv.trans hU_sq
            _ ≤ (M * Real.exp (-((6 / 5 : ℝ) * S_max))) * siftProd ω z :=
                mul_le_mul_of_nonneg_right hM_mul hPz.le
            _ ≤ M * siftProd ω z * psiPlus (6 / 5) (Real.log D / Real.log z) := by
                have := mul_le_mul_of_nonneg_left hpsi_ge (show 0 ≤ M * siftProd ω z by positivity)
                linarith
        · -- `z₁ ≤ z` and `z ≤ D < z ^ 3`: reduce to `z' = D ^ (1 / 3)` (which has `s' = 3`)!
          push Not at hz_small
          set z' : ℝ := D ^ ((1 : ℝ) / 3) with hz'_def
          have hD0 : 0 < D := by linarith
          have hz'_cube : z' ^ 3 = D := by
            rw [hz'_def, ← Real.rpow_natCast (D ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul hD0.le]
            norm_num
          have hz'_ge2 : 2 ≤ z' := by
            have h8 : (2 : ℝ) ^ 3 ≤ D := by
              have : (8 : ℝ) ≤ z := by linarith
              linarith
            have hpow : (2 : ℝ) ^ 3 ≤ z' ^ 3 := by rw [hz'_cube]; exact h8
            exact le_of_pow_le_pow_left₀ (by norm_num) (Real.rpow_nonneg hD0.le _) hpow
          have hz'_lt_z : z' < z := by
            have hpow : z' ^ 3 < z ^ 3 := by rw [hz'_cube]; exact hz3
            exact lt_of_pow_lt_pow_left₀ 3 hz0.le hpow
          have hlen' : (primesLtList z').length ≤ N :=
            le_trans (primesLtList_length_mono hz'_lt_z.le) hlen
          have hbd' := hUp_ge3 z' D hz'_ge2 hlen' hz'_cube.le
          have hlogD_pos : 0 < Real.log D := Real.log_pos (by linarith)
          have hlz' : Real.log z' = Real.log D / 3 := by
            rw [hz'_def, Real.log_rpow hD0]; ring
          have hlog3 : Real.log D / Real.log z' = 3 := by
            rw [hlz']; field_simp [hlogD_pos.ne']
          rw [hlog3] at hbd'
          -- `V⁺(D, z) = V⁺(D, z')`
          rw [rosserV_true_eq_of_le_cube ω (by linarith) hz'_lt_z.le hz'_cube.symm.le]
          have hrat := siftProd_le_mul_ratio hω hz'_ge2 hz'_lt_z.le
          have hlograt : Real.log z / Real.log z' = 3 / (Real.log D / Real.log z) := by
            rw [hlz']; field_simp [hlogD_pos.ne', hlz.ne']
          rw [hlograt] at hrat
          have hKz'_le : K / Real.log z' ≤ 1 / 1000 := by
            have hlogD_ge : Real.log z ≤ Real.log D := Real.log_le_log hz0 hzD
            have hlogz_ge : 1000 * B * K ≤ Real.log z := by
              have := Real.log_le_log (Real.exp_pos _) (hz₁_geExp.trans hz_small)
              rwa [Real.log_exp] at this
            rw [hlz', div_div_eq_mul_div, div_le_iff₀ hlogD_pos]
            nlinarith
          have hPz'_le : siftProd ω z' ≤
              siftProd ω z * ((3 / (Real.log D / Real.log z)) * (1 + 1 / 1000)) := by
            have h3s_nn : 0 ≤ 3 / (Real.log D / Real.log z) := by positivity
            calc siftProd ω z'
                ≤ siftProd ω z * ((3 / (Real.log D / Real.log z)) * (1 + K / Real.log z')) := hrat
              _ ≤ siftProd ω z * ((3 / (Real.log D / Real.log z)) * (1 + 1 / 1000)) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) h3s_nn) hPz.le
          have hV'_le : rosserV ω true D (primesLtList z') ≤
              siftProd ω z' * (1 + M * Real.exp (-(18 / 5 : ℝ))) := by
            have : (6 / 5 : ℝ) * 3 = 18 / 5 := by norm_num
            rw [this] at hbd'; linarith
          have h3_le : 3 ≤ (1 / 1000 : ℝ) * M * Real.exp (-(18 / 5 : ℝ)) := by
            rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
            linarith
          have hpsi_eq : psiPlus (6 / 5) (Real.log D / Real.log z) =
              (105 / 100 : ℝ) * (3 / (Real.log D / Real.log z)) * Real.exp (-(18 / 5 : ℝ)) := by
            unfold psiPlus; rw [if_pos hs_lt3.le]; congr 2; norm_num
          rw [hpsi_eq]
          have h3s_ge1 : 1 ≤ 3 / (Real.log D / Real.log z) := (one_le_div (by linarith)).mpr hs_lt3.le
          have h3s_le3 : 3 / (Real.log D / Real.log z) ≤ 3 := by
            rw [div_le_iff₀ (by linarith)]; linarith
          have hfactor : (3 / (Real.log D / Real.log z)) * (1 + 1 / 1000) *
              (1 + M * Real.exp (-(18 / 5 : ℝ))) - 1 ≤
              M * ((105 / 100 : ℝ) * (3 / (Real.log D / Real.log z)) * Real.exp (-(18 / 5 : ℝ))) := by
            have hMe_pos : 0 < M * Real.exp (-(18 / 5 : ℝ)) := by positivity
            nlinarith
          calc rosserV ω true D (primesLtList z') - siftProd ω z
              ≤ siftProd ω z' * (1 + M * Real.exp (-(18 / 5 : ℝ))) - siftProd ω z := by linarith
            _ ≤ siftProd ω z * ((3 / (Real.log D / Real.log z)) * (1 + 1 / 1000)) *
                  (1 + M * Real.exp (-(18 / 5 : ℝ))) - siftProd ω z := by
                have : 0 ≤ 1 + M * Real.exp (-(18 / 5 : ℝ)) := by positivity
                nlinarith
            _ = siftProd ω z * ((3 / (Real.log D / Real.log z)) * (1 + 1 / 1000) *
                  (1 + M * Real.exp (-(18 / 5 : ℝ))) - 1) := by ring
            _ ≤ siftProd ω z * (M * ((105 / 100 : ℝ) * (3 / (Real.log D / Real.log z)) *
                  Real.exp (-(18 / 5 : ℝ)))) := mul_le_mul_of_nonneg_left hfactor hPz.le
            _ = M * siftProd ω z * ((105 / 100 : ℝ) * (3 / (Real.log D / Real.log z)) *
                  Real.exp (-(18 / 5 : ℝ))) := by ring
    · -- Part 2: `z ^ 2 ≤ D → P(z) - V⁻(D, z) ≤ M * P(z) * psiMinus (6 / 5) s`
      intro hz2D
      have hzD : z < D := by nlinarith
      have hlD : 0 < Real.log D := Real.log_pos (by linarith)
      set s := Real.log D / Real.log z with hs_def
      have hs2 : 2 ≤ s := by
        rw [hs_def, le_div_iff₀ hlz, show 2 * Real.log z = Real.log (z ^ 2) by rw [Real.log_pow]; ring]
        exact Real.log_le_log (pow_pos hz0 2) hz2D
      by_cases hz_small : z < z₁
      · by_cases hD_big : z ^ (⌊z⌋₊ + 3) < D
        · rw [rosserV_eq_siftProd_of_large_D ω hz2 hD_big false, sub_self]
          exact mul_nonneg (mul_nonneg hM_pos.le hPz.le) (psiMinus_pos _ _).le
        · push Not at hD_big
          have hfl_le : ⌊z⌋₊ ≤ ⌊z₁⌋₊ := Nat.floor_mono hz_small.le
          have hs_le : s ≤ S_max := by
            rw [hs_def, hSmax_def]
            have hlD_le : Real.log D ≤ ((⌊z₁⌋₊ + 3 : ℕ) : ℝ) * Real.log z₁ := by
              calc Real.log D ≤ Real.log (z ^ (⌊z⌋₊ + 3)) := Real.log_le_log (by linarith) hD_big
                _ = ((⌊z⌋₊ + 3 : ℕ) : ℝ) * Real.log z := by rw [Real.log_pow]
                _ ≤ ((⌊z₁⌋₊ + 3 : ℕ) : ℝ) * Real.log z₁ := by
                    gcongr
            exact div_le_div₀ (by positivity) hlD_le hlog2_pos (Real.log_le_log (by norm_num) hz2)
          have htriv : siftProd ω z - rosserV ω false D (primesLtList z) ≤ 2 * (siftProd ω z)⁻¹ := by
            have habs := abs_rosserV_le_inv_listSiftProd hω.nonneg hω.lt_one (primesLtList z) false D
            rw [listSiftProd_primesLtList] at habs
            have hP_le1 : siftProd ω z ≤ 1 := by
              unfold siftProd
              exact Finset.prod_le_one (fun p _ => (sub_pos.mpr (hω.lt_one p)).le)
                (fun p _ => by linarith [hω.nonneg p])
            have h1_le_inv : 1 ≤ (siftProd ω z)⁻¹ := one_le_inv₀ hPz |>.mpr hP_le1
            linarith [(abs_le.mp habs).1]
          have hinv_le : (siftProd ω z)⁻¹ ≤ U_max := by
            calc (siftProd ω z)⁻¹ ≤ (Real.log z / Real.log 2) * C₂ := inv_siftProd_le hω hz2
              _ ≤ U_max := by rw [hUmax_def]; gcongr
          have hU_sq : 2 * (siftProd ω z)⁻¹ ≤ 2 * U_max ^ 2 * siftProd ω z := by
            have h1 : ((siftProd ω z)⁻¹) ^ 2 ≤ U_max ^ 2 :=
              pow_le_pow_left₀ (inv_nonneg.mpr hPz.le) hinv_le 2
            have h2 := mul_le_mul_of_nonneg_right h1 hPz.le
            have h3 : ((siftProd ω z)⁻¹) ^ 2 * siftProd ω z = (siftProd ω z)⁻¹ := by field_simp [hPz.ne']
            linarith
          have hexp_ge : Real.exp (-((6 / 5 : ℝ) * S_max)) ≤ psiMinus (6 / 5) s :=
            Real.exp_le_exp.mpr (by nlinarith)
          have hM_mul : 2 * U_max ^ 2 ≤ M * Real.exp (-((6 / 5 : ℝ) * S_max)) := by
            rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
            exact hM_ge2
          calc siftProd ω z - rosserV ω false D (primesLtList z)
              ≤ 2 * U_max ^ 2 * siftProd ω z := htriv.trans hU_sq
            _ ≤ (M * Real.exp (-((6 / 5 : ℝ) * S_max))) * siftProd ω z :=
                mul_le_mul_of_nonneg_right hM_mul hPz.le
            _ ≤ M * siftProd ω z * psiMinus (6 / 5) s := by
                have := mul_le_mul_of_nonneg_left hexp_ge (show 0 ≤ M * siftProd ω z by positivity)
                linarith
      · -- Inductive case `z₁ ≤ z`
        push Not at hz_small
        set w : ℝ := z ^ ((1 : ℝ) / B) with hw_def
        have hB_pos : 0 < B := by linarith
        have hw2 : 2 ≤ w := by
          rw [hw_def]
          have h1 : (2 : ℝ) = ((2 : ℝ) ^ B) ^ ((1 : ℝ) / B) := by
            rw [← Real.rpow_mul (by norm_num), mul_one_div_cancel hB_pos.ne', Real.rpow_one]
          rw [h1]
          exact Real.rpow_le_rpow (by positivity) (hz₁_ge2B.trans hz_small) (by positivity)
        have hlw_eq : Real.log w = Real.log z / B := by
          rw [hw_def, Real.log_rpow hz0]; ring
        have hlw_pos : 0 < Real.log w := Real.log_pos (by linarith)
        have hwz : w ≤ z := by
          have : Real.log w ≤ Real.log z := by rw [hlw_eq]; exact div_le_self hlz.le (by linarith)
          exact (Real.log_le_log_iff (by linarith) hz0).mp this
        have hKw_le : K / Real.log w ≤ 1 / 1000 := by
          rw [hlw_eq, div_div_eq_mul_div, div_le_iff₀ hlz]
          have hlogz : 1000 * B * K ≤ Real.log z := by
            have := Real.log_le_log (Real.exp_pos _) (hz₁_geExp.trans hz_small)
            rwa [Real.log_exp] at this
          linarith
        rw [rosserDelta_false_buchstab ω D hwz, rosserDelta_false_buchstab ω D hw2]
        have h2zero : siftProd ω 2 - rosserV ω false D (primesLtList 2) = 0 := by
          rw [primesLtList_eq_nil_of_le_two le_rfl, siftProd_two_eq_one]; simp [rosserV]
        rw [h2zero, zero_add]
        have hIH_plus : ∀ p : ℕ, p ∈ primesLtList z →
            rosserV ω true (D / (p : ℝ)) (primesLtList (p : ℝ)) - siftProd ω (p : ℝ) ≤
              M * siftProd ω (p : ℝ) * psiPlus (6 / 5) (Real.log D / Real.log (p : ℝ) - 1) := by
          intro p hp
          have hlt_len : (primesLtList (p : ℝ)).length < N :=
            lt_of_lt_of_le (primesLtList_length_lt_of_mem hp) hlen
          obtain ⟨hpr, hpz⟩ := mem_primesLtList.mp hp
          have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpr.two_le
          have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
          have hpD : (p : ℝ) ≤ D / (p : ℝ) := by
            rw [le_div_iff₀ hp0]
            have : (p : ℝ) * (p : ℝ) = (p : ℝ) ^ 2 := by ring
            rw [this]
            exact le_trans (pow_le_pow_left₀ hp0.le hpz.le 2) hz2D
          have hbound := (ih (primesLtList (p : ℝ)).length hlt_len (p : ℝ) (D / (p : ℝ)) hp2 le_rfl).1 hpD
          rwa [log_div_div_log_eq (by linarith) (by linarith)] at hbound
        have hsum_hi : ∑ p ∈ (primesIcoList w z).toFinset,
            ω p * (rosserV ω true (D / (p : ℝ)) (primesLtList (p : ℝ)) - siftProd ω (p : ℝ)) ≤
            M * (siftProd ω z *
              ((1 + K / Real.log w) * (Real.log z / Real.log D) *
                (∫ u in s..(Real.log D / Real.log w), psiPlus (6 / 5) (u - 1)) +
              (K / Real.log w) * psiPlus (6 / 5) (s - 1))) := by
          have h1 : ∑ p ∈ (primesIcoList w z).toFinset,
              ω p * (rosserV ω true (D / (p : ℝ)) (primesLtList (p : ℝ)) - siftProd ω (p : ℝ)) ≤
              M * ∑ p ∈ (primesIcoList w z).toFinset,
                ω p * siftProd ω (p : ℝ) * psiPlus (6 / 5) (Real.log D / Real.log (p : ℝ) - 1) := by
            rw [Finset.mul_sum]
            refine Finset.sum_le_sum fun p hp => ?_
            rw [List.mem_toFinset] at hp
            unfold primesIcoList at hp; rw [List.mem_filter] at hp
            have hbd := hIH_plus p hp.1
            have := hω.nonneg p
            nlinarith
          exact h1.trans (mul_le_mul_of_nonneg_left
            (sum_omega_siftProd_mul_antitone_le hω hw2 hwz hzD
              (fun t ht => (psiPlus_pos ht).le) (psiPlus_antitone (by norm_num))) hM_pos.le)
        have hsum_lo : ∑ p ∈ (primesIcoList 2 w).toFinset,
            ω p * (rosserV ω true (D / (p : ℝ)) (primesLtList (p : ℝ)) - siftProd ω (p : ℝ)) ≤
            M * (siftProd ω w *
              (C₂ * (Real.log w / Real.log D) *
                (∫ u in (Real.log D / Real.log w)..(Real.log D / Real.log 2), psiPlus (6 / 5) (u - 1)) +
              (C₂ - 1) * psiPlus (6 / 5) (Real.log D / Real.log w - 1))) := by
          have hwD : w < D := lt_of_le_of_lt hwz hzD
          have h1 : ∑ p ∈ (primesIcoList 2 w).toFinset,
              ω p * (rosserV ω true (D / (p : ℝ)) (primesLtList (p : ℝ)) - siftProd ω (p : ℝ)) ≤
              M * ∑ p ∈ (primesIcoList 2 w).toFinset,
                ω p * siftProd ω (p : ℝ) * psiPlus (6 / 5) (Real.log D / Real.log (p : ℝ) - 1) := by
            rw [Finset.mul_sum]
            refine Finset.sum_le_sum fun p hp => ?_
            rw [List.mem_toFinset] at hp
            unfold primesIcoList at hp; rw [List.mem_filter] at hp
            have hpz : p ∈ primesLtList z := by
              rw [mem_primesLtList] at *
              exact ⟨hp.1.1, lt_of_lt_of_le hp.1.2 hwz⟩
            have hbd := hIH_plus p hpz
            exact mul_le_mul_of_nonneg_left hbd (hω.nonneg p) |>.trans_eq (by ring)
          have hsbp := sum_omega_siftProd_mul_antitone_le hω le_rfl hw2 hwD
            (fun t ht => (psiPlus_pos ht).le) (psiPlus_antitone (by norm_num : (0 : ℝ) ≤ 6 / 5))
          have hCsub : K / Real.log 2 = C₂ - 1 := by rw [hC₂_def]; ring
          rw [← hC₂_def, hCsub] at hsbp
          exact h1.trans (mul_le_mul_of_nonneg_left hsbp hM_pos.le)
        have hsw_eq : Real.log D / Real.log w = B * s := by
          rw [hlw_eq, hs_def]; field_simp [hlz.ne', hB_pos.ne']
        have hs_inv_eq : Real.log z / Real.log D = 1 / s := by
          rw [hs_def]; field_simp [hlD.ne', hlz.ne']
        have hsw_inv_eq : Real.log w / Real.log D = 1 / (B * s) := by
          rw [hlw_eq, hs_def]; field_simp [hlD.ne', hlz.ne', hB_pos.ne']
        have hhi_num :
            (1 + K / Real.log w) * (Real.log z / Real.log D) *
                (∫ u in s..(Real.log D / Real.log w), psiPlus (6 / 5) (u - 1)) +
              (K / Real.log w) * psiPlus (6 / 5) (s - 1) ≤
            (97 / 100 : ℝ) * psiMinus (6 / 5) s := by
          rw [hs_inv_eq, hsw_eq]
          have hsw_ge : s ≤ B * s := by nlinarith
          have hint_bd := psi_contraction_six_fifths.2 s (B * s) hs2 hsw_ge
          have hsub1 := psiPlus_sub_one_le (β := 6 / 5) (by norm_num) le_rfl hs2
          have hp1 : (1 + K / Real.log w) * ((1 / s) * ∫ u in s..(B * s), psiPlus (6 / 5) (u - 1)) ≤
              (1 + 1 / 1000) * ((95 / 100 : ℝ) * psiMinus (6 / 5) s) := by
            refine mul_le_mul (by linarith) hint_bd ?_ (by norm_num)
            exact mul_nonneg (by positivity)
              (intervalIntegral.integral_nonneg hsw_ge fun u hu => (psiPlus_pos (by linarith [hu.1])).le)
          have hp2 : (K / Real.log w) * psiPlus (6 / 5) (s - 1) ≤
              (1 / 1000) * (13 * psiMinus (6 / 5) s) :=
            mul_le_mul hKw_le hsub1 (psiPlus_pos (by linarith)).le (by norm_num)
          have hreassoc : (1 + K / Real.log w) * (1 / s) * (∫ u in s..(B * s), psiPlus (6 / 5) (u - 1)) =
              (1 + K / Real.log w) * ((1 / s) * ∫ u in s..(B * s), psiPlus (6 / 5) (u - 1)) := by ring
          rw [hreassoc]
          nlinarith [psiMinus_pos (6 / 5) s]
        have hlo_num :
            siftProd ω w *
              (C₂ * (Real.log w / Real.log D) *
                (∫ u in (Real.log D / Real.log w)..(Real.log D / Real.log 2), psiPlus (6 / 5) (u - 1)) +
              (C₂ - 1) * psiPlus (6 / 5) (Real.log D / Real.log w - 1)) ≤
            siftProd ω z * ((1 / 1000 : ℝ) * psiMinus (6 / 5) s) := by
          rw [hsw_eq, hsw_inv_eq]
          have hsw_le2 : B * s ≤ Real.log D / Real.log 2 := by
            rw [← hsw_eq]
            exact div_le_div_of_nonneg_left hlD.le hlog2_pos (Real.log_le_log (by norm_num) hw2)
          have hPw_le : siftProd ω w ≤ siftProd ω z * (2 * B) := by
            have hr := siftProd_le_mul_ratio hω hw2 hwz
            have hlograt : Real.log z / Real.log w = B := by rw [hlw_eq]; field_simp [hlz.ne', hB_pos.ne']
            rw [hlograt] at hr
            calc siftProd ω w ≤ siftProd ω z * (B * (1 + K / Real.log w)) := hr
              _ ≤ siftProd ω z * (2 * B) :=
                  mul_le_mul_of_nonneg_left (by nlinarith) hPz.le
          have htail_bd := tail_exp_bound_six_fifths hC₂_ge1 hB4 hs2 hsw_le2
          have hBs8 : 8 ≤ B * s := by nlinarith
          have htail_nn : 0 ≤ C₂ * (1 / (B * s)) *
              (∫ u in (B * s)..(Real.log D / Real.log 2), psiPlus (6 / 5) (u - 1)) +
              (C₂ - 1) * psiPlus (6 / 5) (B * s - 1) := by
            have hint_nn : 0 ≤ ∫ u in (B * s)..(Real.log D / Real.log 2), psiPlus (6 / 5) (u - 1) :=
              intervalIntegral.integral_nonneg hsw_le2 fun u hu => (psiPlus_pos (by linarith [hu.1])).le
            have h2 : 0 ≤ (C₂ - 1) * psiPlus (6 / 5) (B * s - 1) :=
              mul_nonneg (by linarith) (psiPlus_pos (by linarith)).le
            have h1 : 0 ≤ C₂ * (1 / (B * s)) * (∫ u in (B * s)..(Real.log D / Real.log 2), psiPlus (6 / 5) (u - 1)) := by
              have : 0 < B * s := by linarith
              positivity
            linarith
          calc siftProd ω w * _
              ≤ (siftProd ω z * (2 * B)) *
                  ((8 * C₂) * Real.exp (-(2 * (B - 1))) * Real.exp (-((6 / 5 : ℝ) * s))) :=
                mul_le_mul hPw_le htail_bd htail_nn (by positivity)
            _ = siftProd ω z * ((2 * B * (8 * C₂) * Real.exp (-(2 * (B - 1)))) * psiMinus (6 / 5) s) := by
                unfold psiMinus; ring
            _ ≤ siftProd ω z * ((1 / 1000 : ℝ) * psiMinus (6 / 5) s) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right hB_tail (psiMinus_pos _ _).le) hPz.le
        have htotal := add_le_add hsum_lo hsum_hi
        have h1 : M * (siftProd ω w * _) ≤ M * (siftProd ω z * ((1 / 1000 : ℝ) * psiMinus (6 / 5) s)) :=
          mul_le_mul_of_nonneg_left hlo_num hM_pos.le
        have h2 : M * (siftProd ω z * _) ≤ M * (siftProd ω z * ((97 / 100 : ℝ) * psiMinus (6 / 5) s)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hhi_num hPz.le) hM_pos.le
        have hcomb :
            M * (siftProd ω z * ((1 / 1000 : ℝ) * psiMinus (6 / 5) s)) +
              M * (siftProd ω z * ((97 / 100 : ℝ) * psiMinus (6 / 5) s)) ≤
            M * siftProd ω z * psiMinus (6 / 5) s := by
          have : 0 < M * siftProd ω z * psiMinus (6 / 5) s :=
            mul_pos (mul_pos hM_pos hPz) (psiMinus_pos _ _)
          linarith
        linarith

/-- Helper: `psiPlus (6/5) s ≤ psiPlus 1 s` and `psiMinus (6/5) s ≤ psiMinus 1 s` for `s > 0`. -/
private lemma psi_six_fifths_le_one {s : ℝ} (hs : 0 < s) :
    psiPlus (6 / 5) s ≤ psiPlus 1 s ∧ psiMinus (6 / 5) s ≤ psiMinus 1 s := by
  constructor
  · unfold psiPlus
    split_ifs
    · have hexp : Real.exp (-(3 * (6 / 5 : ℝ))) ≤ Real.exp (-(3 * 1)) :=
        Real.exp_le_exp.mpr (by norm_num)
      exact mul_le_mul_of_nonneg_left hexp (by positivity)
    · exact Real.exp_le_exp.mpr (by linarith)
  · unfold psiMinus
    exact Real.exp_le_exp.mpr (by linarith)

/-- Helper: `psiPlus 1 s ≤ 1` for `1 ≤ s` and `psiMinus 1 s ≤ 1` for `0 ≤ s`. -/
private lemma psi_one_le_one {s : ℝ} (hs : 1 ≤ s) :
    psiPlus 1 s ≤ 1 ∧ psiMinus 1 s ≤ 1 := by
  constructor
  · unfold psiPlus
    split_ifs with hle
    · have h3s : 3 / s ≤ 3 := by rw [div_le_iff₀ (by linarith)]; linarith
      have he3 : Real.exp (-(3 * 1 : ℝ)) ≤ 1 / 10 := by
        simpa [show -(3 * 1 : ℝ) = -3 by norm_num] using
          exp_neg_le_of_taylor6 (r := 3) (c := 1 / 10) (by norm_num) (by norm_num) (by norm_num)
      have h1 : (105 / 100 : ℝ) * (3 / s) ≤ 315 / 100 := by linarith
      calc (105 / 100 : ℝ) * (3 / s) * Real.exp (-(3 * 1 : ℝ))
          ≤ (315 / 100) * (1 / 10) := mul_le_mul h1 he3 (Real.exp_pos _).le (by norm_num)
        _ ≤ 1 := by norm_num
    · exact Real.exp_le_one_iff.mpr (by linarith)
  · unfold psiMinus
    exact Real.exp_le_one_iff.mpr (by linarith)

/-- **Core Linear Sieve Main-Term Theorem (Iwaniec's Induction, Uniform in `ω`)**:
For any `K ≥ 1`, any `LinearSievePair F f`, and any `ε > 0`, there exists `z₀ ≥ 2`
(depending **ONLY** on `(K, F, f, ε)`) such that for EVERY `ω` with `LinearSieveDensity ω K`,
EVERY `z ≥ z₀`, and EVERY `D`:
- `z ≤ D → rosserV ω true D (primesLtList z) ≤ siftProd ω z * (F (log D / log z) + ε)`
- `z^2 ≤ D → siftProd ω z * (f (log D / log z) - ε) ≤ rosserV ω false D (primesLtList z)`. -/
theorem linear_sieve_V_bounds {K : ℝ} (hK : 1 ≤ K) {F f : ℝ → ℝ} (hFf : LinearSievePair F f) :
    ∀ ε : ℝ, 0 < ε → ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ {ω : ℕ → ℝ}, LinearSieveDensity ω K →
        ∀ z D : ℝ, z₀ ≤ z →
          (z ≤ D →
            rosserV ω true D (primesLtList z) ≤
              siftProd ω z * (F (Real.log D / Real.log z) + ε)) ∧
          (z ^ 2 ≤ D →
            siftProd ω z * (f (Real.log D / Real.log z) - ε) ≤
              rosserV ω false D (primesLtList z)) := by
  intro ε hε
  obtain ⟨M, hM_pos, hFund⟩ := fundamental_lemma_rosser K hK
  set η : ℝ := ε / 2 with hη_def
  have hη_pos : 0 < η := by positivity
  have hF1_pos : 0 < F 1 := lt_of_lt_of_le zero_lt_one (hFf.one_le_F 1 zero_lt_one)
  have hF3_le1 : F 3 ≤ F 1 :=
    hFf.F_antitone (Set.mem_Ioi.mpr zero_lt_one) (Set.mem_Ioi.mpr (by norm_num)) (by norm_num)
  -- `S₀ ≥ 4` so `M * exp(-(1/5)*S₀) ≤ η` (hence `M * exp(-(6/5)s) ≤ η * exp(-s)` for all `s ≥ S₀`)
  set S₀ : ℝ := max 4 (5 * Real.log (max 1 (M / η)) + 1) with hS₀_def
  have hS₀_ge4 : 4 ≤ S₀ := le_max_left _ _
  have hS₀_bd : ∀ s : ℝ, S₀ ≤ s → M * Real.exp (-((6 / 5 : ℝ) * s)) ≤ η * Real.exp (-s) := by
    intro s hs
    have hlog : Real.log (max 1 (M / η)) ≤ (1 / 5 : ℝ) * s := by
      have : 5 * Real.log (max 1 (M / η)) + 1 ≤ s := le_trans (le_max_right _ _) hs
      linarith
    have hexp_ge : M / η ≤ Real.exp ((1 / 5 : ℝ) * s) :=
      (le_max_right 1 (M / η)).trans ((Real.log_le_iff_le_exp (lt_of_lt_of_le zero_lt_one (le_max_left _ _))).mp hlog)
    have hM_le : M * Real.exp (-((1 / 5 : ℝ) * s)) ≤ η := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
      have h1 := (div_le_iff₀ hη_pos).mp hexp_ge
      linarith
    have hsplit : Real.exp (-((6 / 5 : ℝ) * s)) = Real.exp (-((1 / 5 : ℝ) * s)) * Real.exp (-s) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hsplit, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hM_le (Real.exp_pos _).le
  -- Choose `B ≥ 4` so `2 * B * M * exp(-2*(B-1)) ≤ η / 1000`
  obtain ⟨B, hB4, hB_bd⟩ := exists_B_mul_exp_le (c := η / (2000 * M)) (by positivity)
  have hB_pos : 0 < B := by linarith
  have hB_tail : 2 * B * M * Real.exp (-(2 * (B - 1))) ≤ η / 1000 := by
    have h1 := mul_le_mul_of_nonneg_left hB_bd (show 0 ≤ 2 * M by positivity)
    have h2 : 2 * M * (η / (2000 * M)) = η / 1000 := by field_simp [hM_pos.ne']; norm_num
    linarith
  -- Choose `α > 0` so `B ^ α = 101 / 100`
  set α : ℝ := Real.log (101 / 100 : ℝ) / Real.log B with hα_def
  have hlB_pos : 0 < Real.log B := Real.log_pos (by linarith)
  have hα_pos : 0 < α := div_pos (Real.log_pos (by norm_num)) hlB_pos
  have hB_rpow_α : B ^ α = 101 / 100 := by
    rw [Real.rpow_def_of_pos hB_pos, hα_def, mul_div_cancel₀ _ hlB_pos.ne', Real.exp_log (by norm_num)]
  have h3_rpow_α : (3 : ℝ) ^ α ≤ 101 / 100 := by
    rw [← hB_rpow_α]
    exact Real.rpow_le_rpow (by norm_num) (by linarith) hα_pos.le
  -- Choose `z₁ ≥ max (2^B) 16` so `B * K / log z₁ ≤ 1 / 1000` and `(B * K / log z₁) * F 1 ≤ (η / 1000) * exp(-S₀)`
  set L_req : ℝ := max (1000 * B * K) (1000 * B * K * F 1 * Real.exp S₀ / η) with hLreq_def
  set z₁ : ℝ := max (max ((2 : ℝ) ^ B) (Real.exp L_req)) 16 with hz₁_def
  have hz₁_ge16 : 16 ≤ z₁ := le_max_right _ _
  have hz₁_ge2B : (2 : ℝ) ^ B ≤ z₁ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hz₁_geExp : Real.exp L_req ≤ z₁ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hlz₁_pos : 0 < Real.log z₁ := Real.log_pos (by linarith)
  set C₀ : ℝ := M * (Real.log z₁) ^ α with hC₀_def
  have hC₀_pos : 0 < C₀ := mul_pos hM_pos (Real.rpow_pos_of_pos hlz₁_pos α)
  -- Error envelope function `err(z) := η + C₀ * (log z) ^ (-α)`
  let err : ℝ → ℝ := fun z => η + C₀ * (Real.log z) ^ (-α)
  have herr_pos : ∀ z : ℝ, 2 ≤ z → 0 < err z := fun z hz => by
    have hlz : 0 < Real.log z := Real.log_pos (by linarith)
    exact add_pos hη_pos (mul_pos hC₀_pos (Real.rpow_pos_of_pos hlz _))
  -- Prove the inductive error bound for ALL `ω` with `LinearSieveDensity ω K` and ALL `z ≥ 2`!
  have hMain : ∀ {ω : ℕ → ℝ}, LinearSieveDensity ω K →
      ∀ N : ℕ, ∀ z D : ℝ, 2 ≤ z → (primesLtList z).length ≤ N →
        (z ≤ D →
          rosserV ω true D (primesLtList z) ≤
            siftProd ω z * (F (Real.log D / Real.log z) + err z * psiPlus 1 (Real.log D / Real.log z))) ∧
        (z ^ 2 ≤ D →
          siftProd ω z * (f (Real.log D / Real.log z) - err z * psiMinus 1 (Real.log D / Real.log z)) ≤
            rosserV ω false D (primesLtList z)) := by
    intro ω hω N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      -- Step 1: prove `V⁺` for `z ^ 3 ≤ D` (`s ≥ 3`) for all `z ≥ 2` with `(primesLtList z).length ≤ N`
      have hUp_ge3 : ∀ z D : ℝ, 2 ≤ z → (primesLtList z).length ≤ N → z ^ 3 ≤ D →
          rosserV ω true D (primesLtList z) ≤
            siftProd ω z * (F (Real.log D / Real.log z) + err z * Real.exp (-(Real.log D / Real.log z))) := by
        intro z D hz2 hlen hz3
        have hPz : 0 < siftProd ω z := siftProd_pos_of_linearSieve hω z
        have hlz : 0 < Real.log z := Real.log_pos (by linarith)
        have hz0 : 0 < z := by linarith
        have hzD : z < D := by
          have hsq : 4 ≤ z * z := by nlinarith
          have hcube : z ^ 3 = z * z * z := by ring
          nlinarith
        have hlD : 0 < Real.log D := Real.log_pos (by linarith)
        set s := Real.log D / Real.log z with hs_def
        have hs3 : 3 ≤ s := by
          rw [hs_def, le_div_iff₀ hlz, show 3 * Real.log z = Real.log (z ^ 3) by rw [Real.log_pow]; ring]
          exact Real.log_le_log (pow_pos hz0 3) hz3
        -- Case 0: `S₀ ≤ s` (discharged immediately by Global Fundamental Lemma!)
        by_cases hs_big : S₀ ≤ s
        · have hfl := (hFund hω z D hz2).1 hzD.le
          have hpsi_eq : psiPlus (6 / 5) s = Real.exp (-((6 / 5 : ℝ) * s)) := by
            unfold psiPlus; rw [if_neg (by linarith)]
          rw [← hs_def, hpsi_eq] at hfl
          have hM_le := hS₀_bd s hs_big
          have h1F : 1 ≤ F s := hFf.one_le_F s (by linarith)
          have hη_le : η ≤ err z := by
            dsimp only [err]; linarith [mul_pos hC₀_pos (Real.rpow_pos_of_pos hlz (-α))]
          calc rosserV ω true D (primesLtList z)
              ≤ siftProd ω z + M * siftProd ω z * Real.exp (-((6 / 5 : ℝ) * s)) := by linarith
            _ = siftProd ω z * (1 + M * Real.exp (-((6 / 5 : ℝ) * s))) := by ring
            _ ≤ siftProd ω z * (F s + η * Real.exp (-s)) :=
                mul_le_mul_of_nonneg_left (by linarith) hPz.le
            _ ≤ siftProd ω z * (F s + err z * Real.exp (-s)) :=
                mul_le_mul_of_nonneg_left
                  (by linarith [mul_le_mul_of_nonneg_right hη_le (Real.exp_pos (-s)).le]) hPz.le
        -- Case 1: `z < z₁` (discharged immediately by `C₀ * (log z)^{-α} ≥ M` + Global Fundamental Lemma!)
        · push Not at hs_big
          by_cases hz_small : z < z₁
          · have hfl := (hFund hω z D hz2).1 hzD.le
            have hpsi_eq : psiPlus (6 / 5) s ≤ Real.exp (-s) := by
              unfold psiPlus
              split_ifs with hle
              · have hs_eq : s = 3 := by linarith
                rw [hs_eq, show (3 : ℝ) / 3 = 1 by norm_num, mul_one]
                have : (105 / 100 : ℝ) * Real.exp (-(3 * (6 / 5 : ℝ))) ≤ Real.exp (-3) := by
                  have he : Real.exp (-(3 / 5 : ℝ)) ≤ 55 / 100 :=
                    exp_neg_le_of_taylor6 (r := 3 / 5) (c := 55 / 100) (by norm_num) (by norm_num) (by norm_num)
                  have hsp : Real.exp (-(3 * (6 / 5 : ℝ))) = Real.exp (-(3 / 5 : ℝ)) * Real.exp (-3) := by
                    rw [← Real.exp_add]; congr 1; ring
                  rw [hsp]
                  have : (105 / 100 : ℝ) * Real.exp (-(3 / 5 : ℝ)) ≤ 1 := by linarith
                  calc (105 / 100 : ℝ) * (Real.exp (-(3 / 5 : ℝ)) * Real.exp (-3))
                      = ((105 / 100 : ℝ) * Real.exp (-(3 / 5 : ℝ))) * Real.exp (-3) := by ring
                    _ ≤ 1 * Real.exp (-3) := mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
                    _ = Real.exp (-3) := one_mul _
                exact this
              · exact Real.exp_le_exp.mpr (by linarith)
            have hM_le_err : M ≤ err z := by
              dsimp only [err]
              have hpow_ge : (Real.log z₁) ^ (-α) ≤ (Real.log z) ^ (-α) := by
                rw [Real.rpow_neg hlz₁_pos.le, Real.rpow_neg hlz.le]
                exact inv_anti₀ (Real.rpow_pos_of_pos hlz α)
                  (Real.rpow_le_rpow hlz.le (Real.log_le_log hz0 hz_small.le) hα_pos.le)
              have hC_ge : M ≤ C₀ * (Real.log z) ^ (-α) := by
                have heq : M = C₀ * (Real.log z₁) ^ (-α) := by
                  rw [hC₀_def, mul_assoc, ← Real.rpow_add hlz₁_pos, add_neg_cancel, Real.rpow_zero, mul_one]
                rw [heq]; exact mul_le_mul_of_nonneg_left hpow_ge hC₀_pos.le
              linarith
            have h1F : 1 ≤ F s := hFf.one_le_F s (by linarith)
            calc rosserV ω true D (primesLtList z)
                ≤ siftProd ω z + M * siftProd ω z * psiPlus (6 / 5) s := by rw [← hs_def] at hfl; linarith
              _ ≤ siftProd ω z * (1 + M * Real.exp (-s)) := by
                  have := mul_le_mul_of_nonneg_left hpsi_eq (mul_nonneg hM_pos.le hPz.le)
                  linarith
              _ ≤ siftProd ω z * (F s + err z * Real.exp (-s)) := by
                  have := mul_le_mul_of_nonneg_right hM_le_err (Real.exp_pos (-s)).le
                  exact mul_le_mul_of_nonneg_left (by linarith) hPz.le
          -- Case 2a: `z₁ ≤ z` AND `3 ≤ s < S₀`
          · push Not at hz_small
            set w : ℝ := z ^ ((1 : ℝ) / B) with hw_def
            have hw2 : 2 ≤ w := by
              rw [hw_def]
              have h1 : (2 : ℝ) = ((2 : ℝ) ^ B) ^ ((1 : ℝ) / B) := by
                rw [← Real.rpow_mul (by norm_num), mul_one_div_cancel hB_pos.ne', Real.rpow_one]
              rw [h1]
              exact Real.rpow_le_rpow (by positivity) (hz₁_ge2B.trans hz_small) (by positivity)
            have hlw_eq : Real.log w = Real.log z / B := by rw [hw_def, Real.log_rpow hz0]; ring
            have hlw_pos : 0 < Real.log w := Real.log_pos (by linarith)
            have hwz : w ≤ z := by
              have : Real.log w ≤ Real.log z := by rw [hlw_eq]; exact div_le_self hlz.le (by linarith)
              exact (Real.log_le_log_iff (by linarith) hz0).mp this
            have hlz_ge_Lreq : L_req ≤ Real.log z := by
              have := Real.log_le_log (Real.exp_pos _) (hz₁_geExp.trans hz_small)
              rwa [Real.log_exp] at this
            have hKw_le : K / Real.log w ≤ 1 / 1000 := by
              rw [hlw_eq, div_div_eq_mul_div, div_le_iff₀ hlz]
              have : 1000 * B * K ≤ L_req := le_max_left _ _
              linarith
            have hKw_F1 : (K / Real.log w) * F 1 ≤ (η / 1000) * Real.exp (-S₀) := by
              have hreq : 1000 * B * K * F 1 * Real.exp S₀ / η ≤ Real.log z :=
                le_trans (le_max_right _ _) hlz_ge_Lreq
              have h1 : 1000 * B * K * F 1 * Real.exp S₀ ≤ Real.log z * η :=
                (div_le_iff₀ hη_pos).mp hreq
              rw [hlw_eq, div_div_eq_mul_div, div_mul_eq_mul_div, Real.exp_neg, ← div_eq_mul_inv,
                div_div, div_le_div_iff₀ hlz (mul_pos (by norm_num) (Real.exp_pos S₀))]
              linarith
            -- Coefficient envelope on `[w, z)`: for `p ∈ [w, z)`, `err p ≤ η + (101/100) * C₀ * (log z)^{-α}`
            set E_hi : ℝ := η + (101 / 100 : ℝ) * C₀ * (Real.log z) ^ (-α) with hEhi_def
            have hEhi_pos : 0 < E_hi := add_pos hη_pos (mul_pos (mul_pos (by norm_num) hC₀_pos) (Real.rpow_pos_of_pos hlz _))
            have herr_p_le : ∀ p : ℕ, w ≤ (p : ℝ) → err (p : ℝ) ≤ E_hi := by
              intro p hwp
              dsimp only [err]
              rw [hEhi_def]
              have hlp : Real.log w ≤ Real.log (p : ℝ) := Real.log_le_log (by linarith) hwp
              have hlp_pos : 0 < Real.log (p : ℝ) := lt_of_lt_of_le hlw_pos hlp
              have hpow_le : (Real.log (p : ℝ)) ^ (-α) ≤ (101 / 100 : ℝ) * (Real.log z) ^ (-α) := by
                have h1 : (Real.log (p : ℝ)) ^ (-α) ≤ (Real.log w) ^ (-α) := by
                  rw [Real.rpow_neg hlp_pos.le, Real.rpow_neg hlw_pos.le]
                  exact inv_anti₀ (Real.rpow_pos_of_pos hlw_pos α)
                    (Real.rpow_le_rpow hlw_pos.le hlp hα_pos.le)
                have h2 : (Real.log w) ^ (-α) = (101 / 100 : ℝ) * (Real.log z) ^ (-α) := by
                  rw [hlw_eq, Real.div_rpow hlz.le hB_pos.le, Real.rpow_neg hB_pos.le,
                    div_inv_eq_mul, hB_rpow_α, mul_comm]
                linarith
              have := mul_le_mul_of_nonneg_left hpow_le hC₀_pos.le
              linarith
            -- Apply Buchstab on `[w, z)` for `V⁺`
            rw [rosserV_true_buchstab ω D hwz]
            have hsum_drop_if : ∑ p ∈ (primesIcoList w z).toFinset,
                (if (p : ℝ) ^ 3 < D then ω p * rosserV ω false (D / (p : ℝ)) (primesLtList (p : ℝ)) else 0) =
                ∑ p ∈ (primesIcoList w z).toFinset, ω p * rosserV ω false (D / (p : ℝ)) (primesLtList (p : ℝ)) := by
              refine Finset.sum_congr rfl fun p hp => ?_
              rw [List.mem_toFinset] at hp; unfold primesIcoList at hp; rw [List.mem_filter] at hp
              have hpz : (p : ℝ) < z := (mem_primesLtList.mp hp.1).2
              rw [if_pos (lt_of_lt_of_le (pow_lt_pow_left₀ hpz (Nat.cast_nonneg p) (by norm_num)) hz3)]
            rw [hsum_drop_if]
            -- Lower bound each `V⁻(D/p, p)` by IH
            have hsum_lower :
                ∑ p ∈ (primesIcoList w z).toFinset,
                    ω p * siftProd ω (p : ℝ) * f (Real.log D / Real.log (p : ℝ) - 1) -
                  E_hi * ∑ p ∈ (primesIcoList w z).toFinset,
                    ω p * siftProd ω (p : ℝ) * psiMinus 1 (Real.log D / Real.log (p : ℝ) - 1) ≤
                ∑ p ∈ (primesIcoList w z).toFinset,
                    ω p * rosserV ω false (D / (p : ℝ)) (primesLtList (p : ℝ)) := by
              rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
              refine Finset.sum_le_sum fun p hp => ?_
              rw [List.mem_toFinset] at hp; unfold primesIcoList at hp; rw [List.mem_filter, decide_eq_true_eq] at hp
              have hlt_len : (primesLtList (p : ℝ)).length < N :=
                lt_of_lt_of_le (primesLtList_length_lt_of_mem hp.1) hlen
              obtain ⟨hpr, hpz⟩ := mem_primesLtList.mp hp.1
              have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpr.two_le
              have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
              have hp2D : (p : ℝ) ^ 2 ≤ D / (p : ℝ) := by
                rw [le_div_iff₀ hp0, show (p : ℝ) ^ 2 * (p : ℝ) = (p : ℝ) ^ 3 by ring]
                exact le_trans (pow_le_pow_left₀ hp0.le hpz.le 3) hz3
              have hih := (ih (primesLtList (p : ℝ)).length hlt_len (p : ℝ) (D / (p : ℝ)) hp2 le_rfl).2 hp2D
              rw [log_div_div_log_eq (by linarith) (by linarith)] at hih
              have hep := herr_p_le p hp.2
              have hsub_le : siftProd ω (p : ℝ) * (f (Real.log D / Real.log (p : ℝ) - 1) -
                  E_hi * psiMinus 1 (Real.log D / Real.log (p : ℝ) - 1)) ≤
                  rosserV ω false (D / (p : ℝ)) (primesLtList (p : ℝ)) := by
                have h1 := mul_le_mul_of_nonneg_right hep
                  (psiMinus_pos 1 (Real.log D / Real.log (p : ℝ) - 1)).le
                have h2 := mul_le_mul_of_nonneg_left
                  (sub_le_sub_left h1 (f (Real.log D / Real.log (p : ℝ) - 1)))
                  (siftProd_pos_of_linearSieve hω (p : ℝ)).le
                exact h2.trans hih
              have hmul := mul_le_mul_of_nonneg_left hsub_le (hω.nonneg p)
              linarith
            -- Term 1: Master Lemma `(M⁺)`
            have hT1 : siftProd ω w * F (Real.log D / Real.log w) -
                ∑ p ∈ (primesIcoList w z).toFinset,
                  ω p * siftProd ω (p : ℝ) * f (Real.log D / Real.log (p : ℝ) - 1) ≤
                siftProd ω z * (F s + (η / 1000) * Real.exp (-s)) := by
              have hM := master_buchstab_upper hω hFf hw2 hwz hz3
              have hK_nn : 0 ≤ K / Real.log w := div_nonneg (by linarith) hlw_pos.le
              have hKF3 : (K / Real.log w) * F 3 ≤ (η / 1000) * Real.exp (-s) := by
                calc (K / Real.log w) * F 3
                    ≤ (K / Real.log w) * F 1 := mul_le_mul_of_nonneg_left hF3_le1 hK_nn
                  _ ≤ (η / 1000) * Real.exp (-S₀) := hKw_F1
                  _ ≤ (η / 1000) * Real.exp (-s) :=
                      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
              rw [← hs_def] at hM
              exact hM.trans (mul_le_mul_of_nonneg_left (by linarith) hPz.le)
            -- Term 2: `V⁺(D, w) - P(w) * F(s_w) ≤ P(z) * (η / 1000) * exp(-s)` via Global Fundamental Lemma!
            have hT2 : rosserV ω true D (primesLtList w) - siftProd ω w * F (Real.log D / Real.log w) ≤
                siftProd ω z * ((η / 1000) * Real.exp (-s)) := by
              have hsw_eq : Real.log D / Real.log w = B * s := by
                rw [hlw_eq, hs_def]; field_simp [hlz.ne', hB_pos.ne']
              have hBs8 : 8 ≤ B * s := by nlinarith
              have hfl := (hFund hω w D hw2).1 (le_trans hwz hzD.le)
              rw [hsw_eq] at hfl ⊢
              have hpsi_w : psiPlus (6 / 5) (B * s) = Real.exp (-((6 / 5 : ℝ) * (B * s))) := by
                unfold psiPlus; rw [if_neg (by linarith)]
              rw [hpsi_w] at hfl
              have h1F : 1 ≤ F (B * s) := hFf.one_le_F (B * s) (by linarith)
              have hPw_pos := siftProd_pos_of_linearSieve hω w
              have hPw_le : siftProd ω w ≤ siftProd ω z * (2 * B) := by
                have hr := siftProd_le_mul_ratio hω hw2 hwz
                have hlograt : Real.log z / Real.log w = B := by rw [hlw_eq]; field_simp [hlz.ne', hB_pos.ne']
                rw [hlograt] at hr
                exact hr.trans (mul_le_mul_of_nonneg_left (by nlinarith) hPz.le)
              have hexp_split : Real.exp (-((6 / 5 : ℝ) * (B * s))) ≤
                  Real.exp (-(2 * (B - 1))) * Real.exp (-s) := by
                rw [← Real.exp_add]
                exact Real.exp_le_exp.mpr (by nlinarith)
              calc rosserV ω true D (primesLtList w) - siftProd ω w * F (B * s)
                  ≤ rosserV ω true D (primesLtList w) - siftProd ω w := by
                    have : siftProd ω w ≤ siftProd ω w * F (B * s) :=
                      le_mul_of_one_le_right hPw_pos.le h1F
                    linarith
                _ ≤ M * siftProd ω w * Real.exp (-((6 / 5 : ℝ) * (B * s))) := hfl
                _ ≤ M * (siftProd ω z * (2 * B)) * (Real.exp (-(2 * (B - 1))) * Real.exp (-s)) := by
                    have h1 := mul_le_mul_of_nonneg_left hPw_le hM_pos.le
                    exact mul_le_mul h1 hexp_split (Real.exp_pos _).le (by positivity)
                _ = siftProd ω z * ((2 * B * M * Real.exp (-(2 * (B - 1)))) * Real.exp (-s)) := by ring
                _ ≤ siftProd ω z * ((η / 1000) * Real.exp (-s)) :=
                    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hB_tail (Real.exp_pos _).le) hPz.le
            -- Term 3: `E_hi * ∑_{w ≤ p < z} ω(p) * P(p) * Ψ⁻_1(u_p - 1)`
            have hT3 : E_hi * ∑ p ∈ (primesIcoList w z).toFinset,
                  ω p * siftProd ω (p : ℝ) * psiMinus 1 (Real.log D / Real.log (p : ℝ) - 1) ≤
                siftProd ω z * ((96 / 100 : ℝ) * E_hi * Real.exp (-s)) := by
              have hsbp := sum_omega_siftProd_mul_antitone_le hω hw2 hwz hzD
                (fun t _ => (psiMinus_pos 1 t).le) (psiMinus_antitone zero_le_one)
              have hs_inv : Real.log z / Real.log D = 1 / s := by rw [hs_def]; field_simp [hlD.ne', hlz.ne']
              have hsw_ge : s ≤ Real.log D / Real.log w :=
                div_le_div_of_nonneg_left hlD.le hlw_pos (Real.log_le_log (by linarith) hwz)
              have hcon : (1 / s) * (∫ u in s..(Real.log D / Real.log w), psiMinus 1 (u - 1)) ≤
                  (95 / 100 : ℝ) * Real.exp (-s) := by
                unfold psiMinus
                rw [integral_exp_neg_shift one_pos]
                have h1 : (Real.exp (-(1 * (s - 1))) - Real.exp (-(1 * (Real.log D / Real.log w - 1)))) / 1 ≤
                    Real.exp 1 * Real.exp (-s) := by
                  have heq : Real.exp (-(1 * (s - 1))) = Real.exp 1 * Real.exp (-s) := by
                    rw [← Real.exp_add]; congr 1; ring
                  linarith [Real.exp_pos (-(1 * (Real.log D / Real.log w - 1)))]
                have hinv : 1 / s ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hs3
                have hc : (1 / 3 : ℝ) * Real.exp 1 ≤ 95 / 100 := by linarith [Real.exp_one_lt_d9]
                calc (1 / s) * ((Real.exp (-(1 * (s - 1))) - Real.exp (-(1 * (Real.log D / Real.log w - 1)))) / 1)
                    ≤ (1 / s) * (Real.exp 1 * Real.exp (-s)) := mul_le_mul_of_nonneg_left h1 (by positivity)
                  _ ≤ (1 / 3) * (Real.exp 1 * Real.exp (-s)) := mul_le_mul_of_nonneg_right hinv (by positivity)
                  _ ≤ (95 / 100) * Real.exp (-s) := by
                      have : (1 / 3 : ℝ) * (Real.exp 1 * Real.exp (-s)) = ((1 / 3 : ℝ) * Real.exp 1) * Real.exp (-s) := by ring
                      rw [this]; exact mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
              have hsub1 : psiMinus 1 (s - 1) ≤ 4 * Real.exp (-s) := by
                unfold psiMinus
                have heq : Real.exp (-(1 * (s - 1))) = Real.exp 1 * Real.exp (-s) := by
                  rw [← Real.exp_add]; congr 1; ring
                rw [heq]
                exact mul_le_mul_of_nonneg_right (by linarith [Real.exp_one_lt_d9]) (Real.exp_pos _).le
              have hinner :
                  (1 + K / Real.log w) * (Real.log z / Real.log D) *
                      (∫ u in s..(Real.log D / Real.log w), psiMinus 1 (u - 1)) +
                    (K / Real.log w) * psiMinus 1 (s - 1) ≤
                  (96 / 100 : ℝ) * Real.exp (-s) := by
                rw [hs_inv, mul_assoc]
                have hp1 : (1 + K / Real.log w) * ((1 / s) * ∫ u in s..(Real.log D / Real.log w), psiMinus 1 (u - 1)) ≤
                    (1 + 1 / 1000) * ((95 / 100 : ℝ) * Real.exp (-s)) := by
                  refine mul_le_mul (by linarith) hcon ?_ (by norm_num)
                  exact mul_nonneg (by positivity)
                    (intervalIntegral.integral_nonneg hsw_ge fun _ _ => (psiMinus_pos _ _).le)
                have hp2 : (K / Real.log w) * psiMinus 1 (s - 1) ≤ (1 / 1000) * (4 * Real.exp (-s)) :=
                  mul_le_mul hKw_le hsub1 (psiMinus_pos _ _).le (by norm_num)
                have := Real.exp_pos (-s)
                linarith
              rw [← hs_def] at hsbp
              have h1 := hsbp.trans (mul_le_mul_of_nonneg_left hinner hPz.le)
              have h2 := mul_le_mul_of_nonneg_left h1 hEhi_pos.le
              linarith
            -- Combine T1 + T2 + T3!
            have hE_comb : (η / 1000) + (η / 1000) + (96 / 100 : ℝ) * E_hi ≤ err z := by
              rw [hEhi_def]; dsimp only [err]
              have : 0 ≤ C₀ * (Real.log z) ^ (-α) := mul_nonneg hC₀_pos.le (Real.rpow_nonneg hlz.le _)
              linarith
            have hfinal : siftProd ω z * (F s + (η / 1000) * Real.exp (-s)) +
                siftProd ω z * ((η / 1000) * Real.exp (-s)) +
                siftProd ω z * ((96 / 100 : ℝ) * E_hi * Real.exp (-s)) ≤
                siftProd ω z * (F s + err z * Real.exp (-s)) := by
              have hrew : siftProd ω z * (F s + (η / 1000) * Real.exp (-s)) +
                  siftProd ω z * ((η / 1000) * Real.exp (-s)) +
                  siftProd ω z * ((96 / 100 : ℝ) * E_hi * Real.exp (-s)) =
                  siftProd ω z * (F s + (η / 1000 + η / 1000 + (96 / 100 : ℝ) * E_hi) * Real.exp (-s)) := by ring
              rw [hrew]
              exact mul_le_mul_of_nonneg_left
                (by linarith [mul_le_mul_of_nonneg_right hE_comb (Real.exp_pos (-s)).le]) hPz.le
            linarith
      -- Step 2: prove both parts of `ih` for all `z ≥ 2` with `(primesLtList z).length ≤ N`
      intro z D hz2 hlen
      have hPz : 0 < siftProd ω z := siftProd_pos_of_linearSieve hω z
      have hlz : 0 < Real.log z := Real.log_pos (by linarith)
      have hz0 : 0 < z := by linarith
      constructor
      · -- Upper bound (`z ≤ D`)
        intro hzD
        by_cases hz3 : z ^ 3 ≤ D
        · have hbd := hUp_ge3 z D hz2 hlen hz3
          have hs3 : 3 ≤ Real.log D / Real.log z := by
            rw [le_div_iff₀ hlz, show 3 * Real.log z = Real.log (z ^ 3) by rw [Real.log_pow]; ring]
            exact Real.log_le_log (pow_pos hz0 3) hz3
          have hpsi_ge : Real.exp (-(Real.log D / Real.log z)) ≤ psiPlus 1 (Real.log D / Real.log z) := by
            unfold psiPlus; split_ifs with hle
            · have heq : Real.log D / Real.log z = 3 := by linarith
              rw [heq]; norm_num; linarith [Real.exp_pos (-3 : ℝ)]
            · simp
          exact hbd.trans (mul_le_mul_of_nonneg_left
            (by linarith [mul_le_mul_of_nonneg_left hpsi_ge (herr_pos z hz2).le]) hPz.le)
        · -- `z ≤ D < z ^ 3` (`1 ≤ s < 3`)
          push Not at hz3
          have hs_lt3 : Real.log D / Real.log z < 3 := by
            rw [div_lt_iff₀ hlz, show 3 * Real.log z = Real.log (z ^ 3) by rw [Real.log_pow]; ring]
            exact Real.log_lt_log (by linarith) hz3
          have hs_ge1 : 1 ≤ Real.log D / Real.log z := (one_le_div hlz).mpr (Real.log_le_log hz0 hzD)
          by_cases hz_small : z < z₁
          · -- Discharged by Global Fundamental Lemma + `M ≤ err z`
            have hfl := (hFund hω z D hz2).1 hzD
            have hpsi_le : psiPlus (6 / 5) (Real.log D / Real.log z) ≤ psiPlus 1 (Real.log D / Real.log z) :=
              (psi_six_fifths_le_one (by linarith)).1
            have hM_le_err : M ≤ err z := by
              dsimp only [err]
              have hpow_ge : (Real.log z₁) ^ (-α) ≤ (Real.log z) ^ (-α) := by
                rw [Real.rpow_neg hlz₁_pos.le, Real.rpow_neg hlz.le]
                exact inv_anti₀ (Real.rpow_pos_of_pos hlz α)
                  (Real.rpow_le_rpow hlz.le (Real.log_le_log hz0 hz_small.le) hα_pos.le)
              have hC_ge : M ≤ C₀ * (Real.log z) ^ (-α) := by
                have heq : M = C₀ * (Real.log z₁) ^ (-α) := by
                  rw [hC₀_def, mul_assoc, ← Real.rpow_add hlz₁_pos, add_neg_cancel, Real.rpow_zero, mul_one]
                rw [heq]; exact mul_le_mul_of_nonneg_left hpow_ge hC₀_pos.le
              linarith
            have h1F : 1 ≤ F (Real.log D / Real.log z) := hFf.one_le_F _ (by linarith)
            have h1 : M * psiPlus (6 / 5) (Real.log D / Real.log z) ≤
                err z * psiPlus 1 (Real.log D / Real.log z) :=
              mul_le_mul hM_le_err hpsi_le (psiPlus_pos (by linarith)).le (herr_pos z hz2).le
            have h2 := mul_le_mul_of_nonneg_left (by linarith : 1 + M * psiPlus (6 / 5) (Real.log D / Real.log z) ≤
              F (Real.log D / Real.log z) + err z * psiPlus 1 (Real.log D / Real.log z)) hPz.le
            linarith
          · -- Subcase 2b: `z₁ ≤ z`, `1 ≤ s < 3`, reduce to `z' = D ^ (1 / 3)`!
            push Not at hz_small
            set s := Real.log D / Real.log z with hs_def
            set z' : ℝ := D ^ ((1 : ℝ) / 3) with hz'_def
            have hD0 : 0 < D := by linarith
            have hlD : 0 < Real.log D := Real.log_pos (by linarith)
            have hz'_cube : z' ^ 3 = D := by
              rw [hz'_def, ← Real.rpow_natCast (D ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul hD0.le]
              norm_num
            have hz'_ge2 : 2 ≤ z' := by
              have h8 : (2 : ℝ) ^ 3 ≤ D := by linarith
              exact le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) (Real.rpow_nonneg hD0.le _)
                (by rw [hz'_cube]; exact h8)
            have hz'_lt_z : z' < z := lt_of_pow_lt_pow_left₀ 3 hz0.le (by rw [hz'_cube]; exact hz3)
            have hlen' : (primesLtList z').length ≤ N :=
              le_trans (primesLtList_length_mono hz'_lt_z.le) hlen
            have hbd' := hUp_ge3 z' D hz'_ge2 hlen' hz'_cube.le
            have hlz' : Real.log z' = Real.log D / 3 := by rw [hz'_def, Real.log_rpow hD0]; ring
            have hlz'_pos : 0 < Real.log z' := Real.log_pos (by linarith)
            have hlog3 : Real.log D / Real.log z' = 3 := by rw [hlz']; field_simp [hlD.ne']
            rw [hlog3] at hbd'
            rw [rosserV_true_eq_of_le_cube ω (by linarith) hz'_lt_z.le hz'_cube.symm.le]
            have hrat := siftProd_le_mul_ratio hω hz'_ge2 hz'_lt_z.le
            have hlograt : Real.log z / Real.log z' = 3 / s := by
              rw [hlz', hs_def]; field_simp [hlD.ne', hlz.ne']
            rw [hlograt] at hrat
            have hlz_ge_Lreq : L_req ≤ Real.log z := by
              have := Real.log_le_log (Real.exp_pos _) (hz₁_geExp.trans hz_small)
              rwa [Real.log_exp] at this
            have hlz'_ge : Real.log z / 3 ≤ Real.log z' := by
              rw [hlz']; exact div_le_div_of_nonneg_right (Real.log_le_log hz0 hzD) (by norm_num)
            have hKz'_le : K / Real.log z' ≤ 1 / 1000 := by
              have h1 : 1000 * B * K ≤ Real.log z := le_trans (le_max_left _ _) hlz_ge_Lreq
              rw [div_le_iff₀ hlz'_pos]; nlinarith
            have hKz'_F3 : (K / Real.log z') * F 3 ≤ (η / 1000) * Real.exp (-3) := by
              have hreq : 1000 * B * K * F 1 * Real.exp S₀ / η ≤ Real.log z :=
                le_trans (le_max_right _ _) hlz_ge_Lreq
              have h1 : 1000 * B * K * F 1 * Real.exp S₀ ≤ Real.log z * η :=
                (div_le_iff₀ hη_pos).mp hreq
              have hK_nn : 0 ≤ K / Real.log z' := div_nonneg (by linarith) hlz'_pos.le
              have hF_bd : (K / Real.log z') * F 3 ≤ (K / (Real.log z / 3)) * F 1 := by
                have hdiv : K / Real.log z' ≤ K / (Real.log z / 3) :=
                  div_le_div_of_nonneg_left (by linarith) (by positivity) hlz'_ge
                exact mul_le_mul hdiv hF3_le1 (by linarith [hFf.one_le_F 3 (by norm_num)]) (by positivity)
              have h2 : (K / (Real.log z / 3)) * F 1 ≤ (η / 1000) * Real.exp (-S₀) := by
                rw [div_div_eq_mul_div, div_mul_eq_mul_div, Real.exp_neg, ← div_eq_mul_inv,
                  div_div, div_le_div_iff₀ hlz (mul_pos (by norm_num) (Real.exp_pos S₀))]
                have : 3 * K * F 1 * (1000 * Real.exp S₀) ≤ 1000 * B * K * F 1 * Real.exp S₀ := by
                  have hnn : 0 ≤ 1000 * K * F 1 * Real.exp S₀ := by positivity
                  nlinarith
                linarith
              exact hF_bd.trans (h2.trans (mul_le_mul_of_nonneg_left
                (Real.exp_le_exp.mpr (by linarith)) (by positivity)))
            have herr'_le : err z' ≤ η + (101 / 100 : ℝ) * C₀ * (Real.log z) ^ (-α) := by
              dsimp only [err]
              have hpow1 : (Real.log z') ^ (-α) ≤ (Real.log z / 3) ^ (-α) := by
                rw [Real.rpow_neg hlz'_pos.le, Real.rpow_neg (by positivity)]
                exact inv_anti₀ (Real.rpow_pos_of_pos (by positivity) α)
                  (Real.rpow_le_rpow (by positivity) hlz'_ge hα_pos.le)
              have hpow2 : (Real.log z / 3) ^ (-α) ≤ (101 / 100 : ℝ) * (Real.log z) ^ (-α) := by
                rw [Real.div_rpow hlz.le (by norm_num : (0 : ℝ) ≤ 3),
                  show (3 : ℝ) ^ (-α) = ((3 : ℝ) ^ α)⁻¹ from Real.rpow_neg (by norm_num) α,
                  div_inv_eq_mul, mul_comm]
                exact mul_le_mul_of_nonneg_right h3_rpow_α (Real.rpow_nonneg hlz.le _)
              have := mul_le_mul_of_nonneg_left (hpow1.trans hpow2) hC₀_pos.le
              linarith
            have hFs_eq : (3 / s) * F 3 = F s := by
              have hfc := hFf.F_const_le_three s (by linarith) hs_lt3.le
              field_simp [(by linarith : s ≠ 0)]; linarith
            have hpsi_eq : psiPlus 1 s = (105 / 100 : ℝ) * (3 / s) * Real.exp (-3) := by
              unfold psiPlus; rw [if_pos hs_lt3.le]; norm_num
            rw [hpsi_eq]
            have hcoeff_bd :
                (K / Real.log z') * F 3 + (1 + K / Real.log z') * err z' * Real.exp (-3) ≤
                (105 / 100 : ℝ) * err z * Real.exp (-3) := by
              have h1 : (1 + K / Real.log z') * err z' ≤
                  (1 + 1 / 1000) * (η + (101 / 100 : ℝ) * C₀ * (Real.log z) ^ (-α)) :=
                mul_le_mul (by linarith) herr'_le (herr_pos z' hz'_ge2).le (by norm_num)
              have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-3 : ℝ)).le
              have h3 : (η / 1000) + (1 + 1 / 1000) * (η + (101 / 100 : ℝ) * C₀ * (Real.log z) ^ (-α)) ≤
                  (105 / 100 : ℝ) * err z := by
                dsimp only [err]
                have : 0 ≤ C₀ * (Real.log z) ^ (-α) := mul_nonneg hC₀_pos.le (Real.rpow_nonneg hlz.le _)
                linarith
              have h4 := mul_le_mul_of_nonneg_right h3 (Real.exp_pos (-3 : ℝ)).le
              linarith
            have hF3_nn : 0 ≤ F 3 + err z' * Real.exp (-3) := by
              have := hFf.one_le_F 3 (by norm_num); have := herr_pos z' hz'_ge2; positivity
            calc rosserV ω true D (primesLtList z')
                ≤ siftProd ω z' * (F 3 + err z' * Real.exp (-3)) := hbd'
              _ ≤ (siftProd ω z * ((3 / s) * (1 + K / Real.log z'))) * (F 3 + err z' * Real.exp (-3)) :=
                  mul_le_mul_of_nonneg_right hrat hF3_nn
              _ = siftProd ω z * ((3 / s) * F 3 +
                    (3 / s) * ((K / Real.log z') * F 3 + (1 + K / Real.log z') * err z' * Real.exp (-3))) := by ring
              _ ≤ siftProd ω z * (F s + (3 / s) * ((105 / 100 : ℝ) * err z * Real.exp (-3))) := by
                  rw [hFs_eq]
                  exact mul_le_mul_of_nonneg_left
                    (by linarith [mul_le_mul_of_nonneg_left hcoeff_bd (show (0 : ℝ) ≤ 3 / s by positivity)]) hPz.le
              _ = siftProd ω z * (F s + err z * ((105 / 100 : ℝ) * (3 / s) * Real.exp (-3))) := by ring
      · -- Lower bound (`z ^ 2 ≤ D`)
        intro hz2D
        have hzD : z < D := by nlinarith
        have hlD : 0 < Real.log D := Real.log_pos (by linarith)
        set s := Real.log D / Real.log z with hs_def
        have hs2 : 2 ≤ s := by
          rw [hs_def, le_div_iff₀ hlz, show 2 * Real.log z = Real.log (z ^ 2) by rw [Real.log_pow]; ring]
          exact Real.log_le_log (pow_pos hz0 2) hz2D
        -- Case 0: `S₀ ≤ s`
        by_cases hs_big : S₀ ≤ s
        · have hfl := (hFund hω z D hz2).2 hz2D
          unfold psiMinus at hfl ⊢
          rw [← hs_def] at hfl
          have hM_le := hS₀_bd s hs_big
          have hf1 : f s ≤ 1 := hFf.f_le_one s (by linarith)
          have hη_le : η ≤ err z := by
            dsimp only [err]; linarith [mul_pos hC₀_pos (Real.rpow_pos_of_pos hlz (-α))]
          have hsub : f s - err z * Real.exp (-(1 * s)) ≤ 1 - M * Real.exp (-((6 / 5 : ℝ) * s)) := by
            rw [one_mul]
            have := mul_le_mul_of_nonneg_right hη_le (Real.exp_pos (-s)).le
            linarith
          have h1 := mul_le_mul_of_nonneg_left hsub hPz.le
          linarith
        -- Case 1: `z < z₁`
        · push Not at hs_big
          by_cases hz_small : z < z₁
          · have hfl := (hFund hω z D hz2).2 hz2D
            rw [← hs_def] at hfl
            have hpsi_le : psiMinus (6 / 5) s ≤ psiMinus 1 s := (psi_six_fifths_le_one (by linarith)).2
            have hM_le_err : M ≤ err z := by
              dsimp only [err]
              have hpow_ge : (Real.log z₁) ^ (-α) ≤ (Real.log z) ^ (-α) := by
                rw [Real.rpow_neg hlz₁_pos.le, Real.rpow_neg hlz.le]
                exact inv_anti₀ (Real.rpow_pos_of_pos hlz α)
                  (Real.rpow_le_rpow hlz.le (Real.log_le_log hz0 hz_small.le) hα_pos.le)
              have hC_ge : M ≤ C₀ * (Real.log z) ^ (-α) := by
                have heq : M = C₀ * (Real.log z₁) ^ (-α) := by
                  rw [hC₀_def, mul_assoc, ← Real.rpow_add hlz₁_pos, add_neg_cancel, Real.rpow_zero, mul_one]
                rw [heq]; exact mul_le_mul_of_nonneg_left hpow_ge hC₀_pos.le
              linarith
            have hf1 : f s ≤ 1 := hFf.f_le_one s (by linarith)
            have h1 : M * psiMinus (6 / 5) s ≤ err z * psiMinus 1 s :=
              mul_le_mul hM_le_err hpsi_le (psiMinus_pos _ _).le (herr_pos z hz2).le
            have h2 := mul_le_mul_of_nonneg_left (by linarith : f s - err z * psiMinus 1 s ≤
              1 - M * psiMinus (6 / 5) s) hPz.le
            linarith
          -- Case 2c: `z₁ ≤ z` AND `2 ≤ s < S₀`
          · push Not at hz_small
            set w : ℝ := z ^ ((1 : ℝ) / B) with hw_def
            have hw2 : 2 ≤ w := by
              rw [hw_def]
              have h1 : (2 : ℝ) = ((2 : ℝ) ^ B) ^ ((1 : ℝ) / B) := by
                rw [← Real.rpow_mul (by norm_num), mul_one_div_cancel hB_pos.ne', Real.rpow_one]
              rw [h1]
              exact Real.rpow_le_rpow (by positivity) (hz₁_ge2B.trans hz_small) (by positivity)
            have hlw_eq : Real.log w = Real.log z / B := by rw [hw_def, Real.log_rpow hz0]; ring
            have hlw_pos : 0 < Real.log w := Real.log_pos (by linarith)
            have hwz : w ≤ z := by
              have : Real.log w ≤ Real.log z := by rw [hlw_eq]; exact div_le_self hlz.le (by linarith)
              exact (Real.log_le_log_iff (by linarith) hz0).mp this
            have hlz_ge_Lreq : L_req ≤ Real.log z := by
              have := Real.log_le_log (Real.exp_pos _) (hz₁_geExp.trans hz_small)
              rwa [Real.log_exp] at this
            have hKw_le : K / Real.log w ≤ 1 / 1000 := by
              rw [hlw_eq, div_div_eq_mul_div, div_le_iff₀ hlz]
              have : 1000 * B * K ≤ L_req := le_max_left _ _
              linarith
            have hKw_F1 : (K / Real.log w) * F 1 ≤ (η / 1000) * Real.exp (-S₀) := by
              have hreq : 1000 * B * K * F 1 * Real.exp S₀ / η ≤ Real.log z :=
                le_trans (le_max_right _ _) hlz_ge_Lreq
              have h1 : 1000 * B * K * F 1 * Real.exp S₀ ≤ Real.log z * η :=
                (div_le_iff₀ hη_pos).mp hreq
              rw [hlw_eq, div_div_eq_mul_div, div_mul_eq_mul_div, Real.exp_neg, ← div_eq_mul_inv,
                div_div, div_le_div_iff₀ hlz (mul_pos (by norm_num) (Real.exp_pos S₀))]
              linarith
            set E_hi : ℝ := η + (101 / 100 : ℝ) * C₀ * (Real.log z) ^ (-α) with hEhi_def
            have hEhi_pos : 0 < E_hi := add_pos hη_pos (mul_pos (mul_pos (by norm_num) hC₀_pos) (Real.rpow_pos_of_pos hlz _))
            have herr_p_le : ∀ p : ℕ, w ≤ (p : ℝ) → err (p : ℝ) ≤ E_hi := by
              intro p hwp
              dsimp only [err]; rw [hEhi_def]
              have hlp : Real.log w ≤ Real.log (p : ℝ) := Real.log_le_log (by linarith) hwp
              have hlp_pos : 0 < Real.log (p : ℝ) := lt_of_lt_of_le hlw_pos hlp
              have hpow_le : (Real.log (p : ℝ)) ^ (-α) ≤ (101 / 100 : ℝ) * (Real.log z) ^ (-α) := by
                have h1 : (Real.log (p : ℝ)) ^ (-α) ≤ (Real.log w) ^ (-α) := by
                  rw [Real.rpow_neg hlp_pos.le, Real.rpow_neg hlw_pos.le]
                  exact inv_anti₀ (Real.rpow_pos_of_pos hlw_pos α)
                    (Real.rpow_le_rpow hlw_pos.le hlp hα_pos.le)
                have h2 : (Real.log w) ^ (-α) = (101 / 100 : ℝ) * (Real.log z) ^ (-α) := by
                  rw [hlw_eq, Real.div_rpow hlz.le hB_pos.le, Real.rpow_neg hB_pos.le,
                    div_inv_eq_mul, hB_rpow_α, mul_comm]
                linarith
              have := mul_le_mul_of_nonneg_left hpow_le hC₀_pos.le
              linarith
            rw [rosserV_false_buchstab ω D hwz]
            -- Upper bound each `V⁺(D/p, p)` by IH
            have hsum_upper :
                ∑ p ∈ (primesIcoList w z).toFinset,
                    ω p * rosserV ω true (D / (p : ℝ)) (primesLtList (p : ℝ)) ≤
                ∑ p ∈ (primesIcoList w z).toFinset,
                    ω p * siftProd ω (p : ℝ) * F (Real.log D / Real.log (p : ℝ) - 1) +
                  E_hi * ∑ p ∈ (primesIcoList w z).toFinset,
                    ω p * siftProd ω (p : ℝ) * psiPlus 1 (Real.log D / Real.log (p : ℝ) - 1) := by
              rw [Finset.mul_sum, ← Finset.sum_add_distrib]
              refine Finset.sum_le_sum fun p hp => ?_
              rw [List.mem_toFinset] at hp; unfold primesIcoList at hp; rw [List.mem_filter, decide_eq_true_eq] at hp
              have hlt_len : (primesLtList (p : ℝ)).length < N :=
                lt_of_lt_of_le (primesLtList_length_lt_of_mem hp.1) hlen
              obtain ⟨hpr, hpz⟩ := mem_primesLtList.mp hp.1
              have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpr.two_le
              have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
              have hpD : (p : ℝ) ≤ D / (p : ℝ) := by
                rw [le_div_iff₀ hp0, show (p : ℝ) * (p : ℝ) = (p : ℝ) ^ 2 by ring]
                exact le_trans (pow_le_pow_left₀ hp0.le hpz.le 2) hz2D
              have hih := (ih (primesLtList (p : ℝ)).length hlt_len (p : ℝ) (D / (p : ℝ)) hp2 le_rfl).1 hpD
              rw [log_div_div_log_eq (by linarith) (by linarith)] at hih
              have hep := herr_p_le p hp.2
              have hp_pos_arg : 0 < Real.log D / Real.log (p : ℝ) - 1 := by
                have hlp : 0 < Real.log (p : ℝ) := Real.log_pos (by linarith)
                have hlt : Real.log (p : ℝ) < Real.log D := Real.log_lt_log hp0 (lt_trans hpz hzD)
                have := (one_lt_div hlp).mpr hlt; linarith
              have hadd_le : rosserV ω true (D / (p : ℝ)) (primesLtList (p : ℝ)) ≤
                  siftProd ω (p : ℝ) * (F (Real.log D / Real.log (p : ℝ) - 1) +
                    E_hi * psiPlus 1 (Real.log D / Real.log (p : ℝ) - 1)) := by
                have h1 := mul_le_mul_of_nonneg_right hep (psiPlus_pos (β := 1) hp_pos_arg).le
                exact hih.trans (mul_le_mul_of_nonneg_left (by linarith)
                  (siftProd_pos_of_linearSieve hω (p : ℝ)).le)
              have hmul := mul_le_mul_of_nonneg_left hadd_le (hω.nonneg p)
              linarith
            -- Term 1: Master Lemma `(M⁻)`
            have hT1 : siftProd ω z * (f s - (η / 1000) * psiMinus 1 s) ≤
                siftProd ω w * f (Real.log D / Real.log w) -
                  ∑ p ∈ (primesIcoList w z).toFinset,
                    ω p * siftProd ω (p : ℝ) * F (Real.log D / Real.log (p : ℝ) - 1) := by
              have hM := master_buchstab_lower hω hFf hw2 hwz hz2D
              rw [← hs_def] at hM
              have hKF : (K / Real.log w) * F 1 ≤ (η / 1000) * psiMinus 1 s := by
                unfold psiMinus; rw [one_mul]
                exact hKw_F1.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity))
              exact (mul_le_mul_of_nonneg_left (by linarith) hPz.le).trans hM
            -- Term 2: `P(w) * f(s_w) - V⁻(D, w) ≤ P(z) * (η / 1000) * Ψ⁻_1(s)`
            have hT2 : siftProd ω w * f (Real.log D / Real.log w) - rosserV ω false D (primesLtList w) ≤
                siftProd ω z * ((η / 1000) * psiMinus 1 s) := by
              have hsw_eq : Real.log D / Real.log w = B * s := by
                rw [hlw_eq, hs_def]; field_simp [hlz.ne', hB_pos.ne']
              have hw2D : w ^ 2 ≤ D := le_trans (pow_le_pow_left₀ (by linarith) hwz 2) hz2D
              have hfl := (hFund hω w D hw2).2 hw2D
              rw [hsw_eq] at hfl ⊢
              unfold psiMinus at hfl ⊢
              have hf1 : f (B * s) ≤ 1 := hFf.f_le_one (B * s) (by nlinarith)
              have hPw_pos := siftProd_pos_of_linearSieve hω w
              have hPw_le : siftProd ω w ≤ siftProd ω z * (2 * B) := by
                have hr := siftProd_le_mul_ratio hω hw2 hwz
                have hlograt : Real.log z / Real.log w = B := by rw [hlw_eq]; field_simp [hlz.ne', hB_pos.ne']
                rw [hlograt] at hr
                exact hr.trans (mul_le_mul_of_nonneg_left (by nlinarith) hPz.le)
              have hexp_split : Real.exp (-((6 / 5 : ℝ) * (B * s))) ≤
                  Real.exp (-(2 * (B - 1))) * Real.exp (-(1 * s)) := by
                rw [← Real.exp_add]
                exact Real.exp_le_exp.mpr (by nlinarith)
              calc siftProd ω w * f (B * s) - rosserV ω false D (primesLtList w)
                  ≤ siftProd ω w - rosserV ω false D (primesLtList w) := by
                    have : siftProd ω w * f (B * s) ≤ siftProd ω w :=
                      mul_le_of_le_one_right hPw_pos.le hf1
                    linarith
                _ ≤ M * siftProd ω w * Real.exp (-((6 / 5 : ℝ) * (B * s))) := hfl
                _ ≤ M * (siftProd ω z * (2 * B)) * (Real.exp (-(2 * (B - 1))) * Real.exp (-(1 * s))) := by
                    have h1 := mul_le_mul_of_nonneg_left hPw_le hM_pos.le
                    exact mul_le_mul h1 hexp_split (Real.exp_pos _).le (by positivity)
                _ = siftProd ω z * ((2 * B * M * Real.exp (-(2 * (B - 1)))) * Real.exp (-(1 * s))) := by ring
                _ ≤ siftProd ω z * ((η / 1000) * Real.exp (-(1 * s))) :=
                    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hB_tail (Real.exp_pos _).le) hPz.le
            -- Term 3: `E_hi * ∑_{w ≤ p < z} ω(p) * P(p) * Ψ⁺_1(u_p - 1)`
            have hT3 : E_hi * ∑ p ∈ (primesIcoList w z).toFinset,
                  ω p * siftProd ω (p : ℝ) * psiPlus 1 (Real.log D / Real.log (p : ℝ) - 1) ≤
                siftProd ω z * ((97 / 100 : ℝ) * E_hi * psiMinus 1 s) := by
              have hsbp := sum_omega_siftProd_mul_antitone_le hω hw2 hwz hzD
                (fun t ht => (psiPlus_pos ht).le) (psiPlus_antitone zero_le_one)
              have hs_inv : Real.log z / Real.log D = 1 / s := by rw [hs_def]; field_simp [hlD.ne', hlz.ne']
              have hsw_ge : s ≤ Real.log D / Real.log w :=
                div_le_div_of_nonneg_left hlD.le hlw_pos (Real.log_le_log (by linarith) hwz)
              have hcon := psi_contraction_one.2 s (Real.log D / Real.log w) hs2 hsw_ge
              have hsub1 := psiPlus_sub_one_le (β := 1) le_rfl (by norm_num) hs2
              have hinner :
                  (1 + K / Real.log w) * (Real.log z / Real.log D) *
                      (∫ u in s..(Real.log D / Real.log w), psiPlus 1 (u - 1)) +
                    (K / Real.log w) * psiPlus 1 (s - 1) ≤
                  (97 / 100 : ℝ) * psiMinus 1 s := by
                rw [hs_inv, mul_assoc]
                have hp1 : (1 + K / Real.log w) * ((1 / s) * ∫ u in s..(Real.log D / Real.log w), psiPlus 1 (u - 1)) ≤
                    (1 + 1 / 1000) * ((95 / 100 : ℝ) * psiMinus 1 s) := by
                  refine mul_le_mul (by linarith) hcon ?_ (by norm_num)
                  exact mul_nonneg (by positivity)
                    (intervalIntegral.integral_nonneg hsw_ge fun u hu => (psiPlus_pos (by linarith [hu.1])).le)
                have hp2 : (K / Real.log w) * psiPlus 1 (s - 1) ≤ (1 / 1000) * (13 * psiMinus 1 s) :=
                  mul_le_mul hKw_le hsub1 (psiPlus_pos (by linarith)).le (by norm_num)
                have := psiMinus_pos 1 s
                linarith
              rw [← hs_def] at hsbp
              have h1 := hsbp.trans (mul_le_mul_of_nonneg_left hinner hPz.le)
              have h2 := mul_le_mul_of_nonneg_left h1 hEhi_pos.le
              linarith
            -- Combine T1, T2, T3!
            have hE_comb : (η / 1000) + (η / 1000) + (97 / 100 : ℝ) * E_hi ≤ err z := by
              rw [hEhi_def]; dsimp only [err]
              have : 0 ≤ C₀ * (Real.log z) ^ (-α) := mul_nonneg hC₀_pos.le (Real.rpow_nonneg hlz.le _)
              linarith
            have hfinal : siftProd ω z * (f s - err z * psiMinus 1 s) ≤
                siftProd ω z * (f s - (η / 1000) * psiMinus 1 s) -
                  siftProd ω z * ((η / 1000) * psiMinus 1 s) -
                  siftProd ω z * ((97 / 100 : ℝ) * E_hi * psiMinus 1 s) := by
              have hrew : siftProd ω z * (f s - (η / 1000) * psiMinus 1 s) -
                  siftProd ω z * ((η / 1000) * psiMinus 1 s) -
                  siftProd ω z * ((97 / 100 : ℝ) * E_hi * psiMinus 1 s) =
                  siftProd ω z * (f s - (η / 1000 + η / 1000 + (97 / 100 : ℝ) * E_hi) * psiMinus 1 s) := by ring
              rw [hrew]
              exact mul_le_mul_of_nonneg_left
                (sub_le_sub_left (mul_le_mul_of_nonneg_right hE_comb (psiMinus_pos _ _).le) _) hPz.le
            linarith
  -- Choose `z₀` so that `C₀ * (log z₀) ^ (-α) ≤ η` (hence `err z ≤ 2 * η = ε` for all `z ≥ z₀`)!
  set z₀ : ℝ := max 2 (Real.exp ((C₀ / η) ^ (1 / α))) with hz₀_def
  refine ⟨z₀, le_max_left _ _, fun {ω} hω z D hzz₀ => ?_⟩
  have hz2 : 2 ≤ z := le_trans (le_max_left _ _) hzz₀
  have hPz : 0 < siftProd ω z := siftProd_pos_of_linearSieve hω z
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have herr_le_eps : err z ≤ ε := by
    dsimp only [err]
    have hlz_ge : (C₀ / η) ^ (1 / α) ≤ Real.log z := by
      have := Real.log_le_log (Real.exp_pos _) (le_trans (le_max_right _ _) hzz₀)
      rwa [Real.log_exp] at this
    have hpow : C₀ / η ≤ (Real.log z) ^ α := by
      have h1 := Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) hlz_ge hα_pos.le
      rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hα_pos.ne', Real.rpow_one] at h1
      exact h1
    have hC_le : C₀ * (Real.log z) ^ (-α) ≤ η := by
      rw [Real.rpow_neg hlz.le, ← div_eq_mul_inv, div_le_iff₀ (Real.rpow_pos_of_pos hlz α)]
      have := (div_le_iff₀ hη_pos).mp hpow
      linarith
    linarith
  have hm := hMain hω (primesLtList z).length z D hz2 le_rfl
  constructor
  · intro hzD
    have hs1 : 1 ≤ Real.log D / Real.log z := (one_le_div hlz).mpr (Real.log_le_log (by linarith) hzD)
    have hpsi1 := (psi_one_le_one hs1).1
    have h1 := hm.1 hzD
    have h2 : err z * psiPlus 1 (Real.log D / Real.log z) ≤ ε :=
      calc err z * psiPlus 1 (Real.log D / Real.log z)
          ≤ err z * 1 := mul_le_mul_of_nonneg_left hpsi1 (herr_pos z hz2).le
        _ = err z := mul_one _
        _ ≤ ε := herr_le_eps
    exact h1.trans (mul_le_mul_of_nonneg_left (by linarith) hPz.le)
  · intro hz2D
    have hs2 : 2 ≤ Real.log D / Real.log z := by
      rw [le_div_iff₀ hlz, show 2 * Real.log z = Real.log (z ^ 2) by rw [Real.log_pow]; ring]
      exact Real.log_le_log (pow_pos (by linarith) 2) hz2D
    have hpsi1 := (psi_one_le_one (by linarith)).2
    have h1 := hm.2 hz2D
    have h2 : err z * psiMinus 1 (Real.log D / Real.log z) ≤ ε :=
      calc err z * psiMinus 1 (Real.log D / Real.log z)
          ≤ err z * 1 := mul_le_mul_of_nonneg_left hpsi1 (herr_pos z hz2).le
        _ = err z := mul_one _
        _ ≤ ε := herr_le_eps
    exact (mul_le_mul_of_nonneg_left (by linarith) hPz.le).trans h1

/-- **ROSSER–IWANIEC LINEAR SIEVE UPPER BOUND (`β = 2`)**:
With `z₀ ≥ 2` depending ONLY on `(K, F, f, ε)` (uniform in `ω, A, X, D, z`). -/
theorem linear_sieve_upper {ω : ℕ → ℝ} {K : ℝ} (hω : LinearSieveDensity ω K)
    {F f : ℝ → ℝ} (hFf : LinearSievePair F f) :
    ∀ ε : ℝ, 0 < ε → ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (A : Finset ℕ) (X D z : ℝ), 0 ≤ X → z₀ ≤ z → z ≤ D →
        (siftedCard A z : ℝ) ≤
          X * siftProd ω z * (F (Real.log D / Real.log z) + ε) +
            ∑ d ∈ (Finset.range (⌊D⌋₊ + 1)).filter (fun d : ℕ => Squarefree d ∧ (d : ℝ) < D ∧
              ∀ p ∈ d.primeFactors, (p : ℝ) < z),
              |((A.filter (fun a => d ∣ a)).card : ℝ) - X * multDensity ω d| := by
  intro ε hε
  obtain ⟨z₀, hz₀2, hV⟩ := linear_sieve_V_bounds hω.K_ge_one hFf ε hε
  refine ⟨z₀, hz₀2, fun A X D z hX hzz₀ hzD => ?_⟩
  have hD1 : 1 < D := by linarith
  have hcomb := (siftedCard_rosser_bounds ω A (X := X) hD1 hzD).1
  have hVup := (hV hω z D hzz₀).1 hzD
  have hXmul := mul_le_mul_of_nonneg_left hVup hX
  unfold sieveDivisors at hcomb
  linarith

/-- **ROSSER–IWANIEC LINEAR SIEVE LOWER BOUND (`β = 2`)**:
With `z₀ ≥ 2` depending ONLY on `(K, F, f, ε)` (uniform in `ω, A, X, D, z`). -/
theorem linear_sieve_lower {ω : ℕ → ℝ} {K : ℝ} (hω : LinearSieveDensity ω K)
    {F f : ℝ → ℝ} (hFf : LinearSievePair F f) :
    ∀ ε : ℝ, 0 < ε → ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (A : Finset ℕ) (X D z : ℝ), 0 ≤ X → z₀ ≤ z → z ^ 2 ≤ D →
        X * siftProd ω z * (f (Real.log D / Real.log z) - ε) -
            ∑ d ∈ (Finset.range (⌊D⌋₊ + 1)).filter (fun d : ℕ => Squarefree d ∧ (d : ℝ) < D ∧
              ∀ p ∈ d.primeFactors, (p : ℝ) < z),
              |((A.filter (fun a => d ∣ a)).card : ℝ) - X * multDensity ω d| ≤
          (siftedCard A z : ℝ) := by
  intro ε hε
  obtain ⟨z₀, hz₀2, hV⟩ := linear_sieve_V_bounds hω.K_ge_one hFf ε hε
  refine ⟨z₀, hz₀2, fun A X D z hX hzz₀ hz2D => ?_⟩
  have hz2 : 2 ≤ z := le_trans hz₀2 hzz₀
  have hzD : z ≤ D := by nlinarith
  have hD1 : 1 < D := by linarith
  have hcomb := (siftedCard_rosser_bounds ω A (X := X) hD1 hzD).2
  have hVlo := (hV hω z D hzz₀).2 hz2D
  have hXmul := mul_le_mul_of_nonneg_left hVlo hX
  unfold sieveDivisors at hcomb
  linarith

/-! ## Section 5: Uniform Chen Prime Density & Quantitative Mertens Ratios -/

/-- For `0 ≤ x ≤ 1`, `Real.exp x ≤ 1 + 3 * x`. -/
private lemma exp_le_one_add_three_mul {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1 + 3 * x := by
  have hhalf_pos : 0 < 1 - x / 2 := by linarith
  have h1 : 1 - x / 2 ≤ Real.exp (-(x / 2)) := by
    have := Real.add_one_le_exp (-(x / 2))
    linarith
  have h2 : Real.exp (x / 2) ≤ (1 - x / 2)⁻¹ := by
    rw [Real.exp_neg] at h1
    have hinv := inv_anti₀ hhalf_pos h1
    rwa [inv_inv] at hinv
  have h3 : (1 - x / 2)⁻¹ ≤ 1 + x := by
    rw [inv_le_iff_one_le_mul₀ hhalf_pos]
    nlinarith
  have h4 : Real.exp (x / 2) ≤ 1 + x := h2.trans h3
  have h5 : Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h5]
  have h6 : Real.exp (x / 2) * Real.exp (x / 2) ≤ (1 + x) * (1 + x) :=
    mul_le_mul h4 h4 (Real.exp_pos _).le (by linarith)
  nlinarith

/-- Exact telescoping sum: for `m : ℕ` and `a : ℝ` with `0 < (m : ℝ) - a`:
`∑ k ∈ Finset.Ico m (m + L), 1 / (((k : ℝ) - a + 1) * ((k : ℝ) - a)) = 1 / (m - a) - 1 / (m + L - a)`. -/
private lemma sum_Ico_telescope (m L : ℕ) (a : ℝ) (hma : 0 < (m : ℝ) - a) :
    ∑ k ∈ Finset.Ico m (m + L), (1 : ℝ) / (((k : ℝ) - a + 1) * ((k : ℝ) - a)) =
      1 / ((m : ℝ) - a) - 1 / ((m : ℝ) + (L : ℝ) - a) := by
  induction L with
  | zero => simp
  | succ L ih =>
    have hmem : m + L ∉ Finset.Ico m (m + L) := by simp
    have hset : Finset.Ico m (m + (L + 1)) = insert (m + L) (Finset.Ico m (m + L)) := by
      ext k; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    rw [hset, Finset.sum_insert hmem, ih]
    have h1 : (m : ℝ) + (L : ℝ) - a ≠ 0 := by
      have : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
      linarith
    have h2 : (m : ℝ) + ((L + 1 : ℕ) : ℝ) - a ≠ 0 := by
      have : (0 : ℝ) ≤ ((L + 1 : ℕ) : ℝ) := Nat.cast_nonneg (L + 1)
      linarith
    have h3 : ((m + L : ℕ) : ℝ) - a = (m : ℝ) + (L : ℝ) - a := by push_cast; ring
    have h4 : ((m + L : ℕ) : ℝ) - a + 1 = (m : ℝ) + ((L + 1 : ℕ) : ℝ) - a := by push_cast; ring
    rw [h4, h3]
    field_simp [h1, h2]
    push_cast
    ring

/-- Upper bound for the telescoping sum over `Finset.Icc m n`. -/
private lemma sum_Icc_telescope_le (m n : ℕ) (a : ℝ) (hma : 0 < (m : ℝ) - a) :
    ∑ k ∈ Finset.Icc m n, (1 : ℝ) / (((k : ℝ) - a + 1) * ((k : ℝ) - a)) ≤ 1 / ((m : ℝ) - a) := by
  by_cases hmn : m ≤ n
  · set L := n + 1 - m with hL_def
    have hset : Finset.Icc m n = Finset.Ico m (m + L) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hset, sum_Ico_telescope m L a hma]
    have hpos : 0 ≤ 1 / ((m : ℝ) + (L : ℝ) - a) := by
      have : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
      have : 0 < (m : ℝ) + (L : ℝ) - a := by linarith
      positivity
    linarith
  · have hemp : Finset.Icc m n = ∅ := by
      ext k; simp only [Finset.mem_Icc, Finset.notMem_empty, iff_false]; omega
    rw [hemp, Finset.sum_empty]
    positivity

/-- Finite product lower bound (Weierstrass inequality):
for `0 ≤ a x ≤ 1`, `1 - ∑ x ∈ s, a x ≤ ∏ x ∈ s, (1 - a x)`. -/
private lemma one_sub_sum_le_prod_one_sub {α : Type*} (s : Finset α) (a : α → ℝ)
    (ha : ∀ x ∈ s, 0 ≤ a x ∧ a x ≤ 1) :
    1 - ∑ x ∈ s, a x ≤ ∏ x ∈ s, (1 - a x) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hxs ih =>
    rw [Finset.sum_insert hxs, Finset.prod_insert hxs]
    have hx := ha x (Finset.mem_insert_self x s)
    have hs : ∀ y ∈ s, 0 ≤ a y ∧ a y ≤ 1 := fun y hy => ha y (Finset.mem_insert_of_mem hy)
    have hih := ih hs
    have hsum_nn : 0 ≤ ∑ y ∈ s, a y := Finset.sum_nonneg fun y hy => (hs y hy).1
    have hmul : (1 - a x) * (1 - ∑ y ∈ s, a y) ≤ (1 - a x) * ∏ y ∈ s, (1 - a y) :=
      mul_le_mul_of_nonneg_left hih (by linarith)
    nlinarith

/-- The product of distinct primes dividing `N` divides `N`. -/
private lemma prod_primes_dvd_of_forall {N : ℕ} (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ p ∣ N) :
    (∏ p ∈ s, p) ∣ N := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hps ih =>
    rw [Finset.prod_insert hps]
    have hp := hs p (Finset.mem_insert_self p s)
    have hs' : ∀ q ∈ s, q.Prime ∧ q ∣ N := fun q hq => hs q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      have hne : p ≠ q := fun h => hps (h ▸ hq)
      exact (Nat.coprime_primes hp.1 (hs' q hq).1).mpr hne
    exact hcop.mul_dvd_of_dvd_of_dvd hp.2 (ih hs')

/-- The strict prime Mertens product `∏_{p < x, p prime} (1 - 1/p)`. -/
private def primeMertensLt (x : ℝ) : ℝ :=
  ∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) < x), (1 - (p : ℝ)⁻¹)

private lemma primeMertensLt_pos (x : ℝ) : 0 < primeMertensLt x := by
  unfold primeMertensLt
  refine Finset.prod_pos fun p hp => ?_
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.1.two_le
  have : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
  linarith

/-- Product of reals `≥ 1` is `≥ 1`. -/
private lemma one_le_prod_of_ge_one {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ x ∈ s, 1 ≤ f x) : 1 ≤ ∏ x ∈ s, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hxs ih =>
    rw [Finset.prod_insert hxs]
    have hx := hf x (Finset.mem_insert_self x s)
    have hih := ih fun y hy => hf y (Finset.mem_insert_of_mem hy)
    nlinarith

private lemma mertensProd_le_primeMertensLt {x : ℝ} :
    Stage8MertensTheorems.mertensProd x ≤ primeMertensLt x := by
  unfold Stage8MertensTheorems.mertensProd primeMertensLt
  set S_lt := (Finset.range (⌊x⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) < x)
  set S_le := (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime
  have hsub : S_lt ⊆ S_le := by
    intro p hp
    simp only [S_lt, S_le, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.2.1.one_lt.le, Nat.lt_succ_iff.mp hp.1⟩, hp.2.1⟩
  rw [← Finset.prod_sdiff hsub]
  have h1 : ∏ p ∈ S_le \ S_lt, (1 - (p : ℝ)⁻¹) ≤ 1 := by
    refine Finset.prod_le_one (fun p hp => ?_) (fun p hp => ?_)
    · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2.two_le
      have : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
      linarith
    · have hp0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
      linarith
  have hpos : 0 < ∏ p ∈ S_lt, (1 - (p : ℝ)⁻¹) := primeMertensLt_pos x
  have hmul := mul_le_mul_of_nonneg_right h1 hpos.le
  linarith

private lemma one_sub_inv_mul_primeMertensLt_le_mertensProd {x : ℝ} (hx : 2 ≤ x) :
    (1 - x⁻¹) * primeMertensLt x ≤ Stage8MertensTheorems.mertensProd x := by
  unfold Stage8MertensTheorems.mertensProd primeMertensLt
  set S_lt := (Finset.range (⌊x⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) < x)
  set S_le := (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime
  have hpos : 0 < ∏ p ∈ S_lt, (1 - (p : ℝ)⁻¹) := primeMertensLt_pos x
  by_cases hex : ∃ p₀ ∈ S_le, ¬ (p₀ : ℝ) < x
  · obtain ⟨p₀, hp₀_mem, hp₀_nlt⟩ := hex
    have hp₀_le : (p₀ : ℝ) ≤ x :=
      Nat.le_floor_iff (by linarith : 0 ≤ x) |>.mp (Finset.mem_Icc.mp (Finset.mem_filter.mp hp₀_mem).1).2
    have hp₀_eq : (p₀ : ℝ) = x := le_antisymm hp₀_le (not_lt.mp hp₀_nlt)
    have hnot : p₀ ∉ S_lt := by
      simp only [S_lt, Finset.mem_filter, not_and]; intro _ _; exact hp₀_nlt
    have heq_set : S_le = insert p₀ S_lt := by
      ext p
      simp only [S_le, S_lt, Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
      constructor
      · intro ⟨⟨_, hple⟩, hpr⟩
        have hpr_le : (p : ℝ) ≤ x := (Nat.le_floor_iff (by linarith)).mp hple
        rcases lt_or_eq_of_le hpr_le with hlt | heq
        · exact Or.inr ⟨Nat.lt_succ_of_le hple, hpr, hlt⟩
        · left
          exact Nat.cast_injective (heq.trans hp₀_eq.symm)
      · rintro (rfl | ⟨hplt, hpr, _⟩)
        · have hm := Finset.mem_filter.mp hp₀_mem
          exact ⟨Finset.mem_Icc.mp hm.1, hm.2⟩
        · exact ⟨⟨hpr.one_lt.le, Nat.lt_succ_iff.mp hplt⟩, hpr⟩
    rw [heq_set, Finset.prod_insert hnot, hp₀_eq]
  · push Not at hex
    have heq_set : S_le = S_lt := by
      ext p
      constructor
      · intro hp
        have hlt := hex p hp
        simp only [S_le, S_lt, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hp ⊢
        exact ⟨Nat.lt_succ_of_le hp.1.2, hp.2, hlt⟩
      · intro hp
        simp only [S_le, S_lt, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hp ⊢
        exact ⟨⟨hp.2.1.one_lt.le, Nat.lt_succ_iff.mp hp.1⟩, hp.2.1⟩
    rw [heq_set]
    have hx_inv_nn : 0 ≤ x⁻¹ := by positivity
    have hmul := mul_le_mul_of_nonneg_right (show 1 - x⁻¹ ≤ 1 by linarith) hpos.le
    linarith

/-- Splitting `siftProd ω z / siftProd ω w` into the `[w, z)` prime product for any `ω < 1`. -/
private lemma siftProd_div_eq_prod_ico {ω : ℕ → ℝ} (hlt : ∀ p : ℕ, ω p < 1)
    {w z : ℝ} (hwz : w ≤ z) :
    siftProd ω z / siftProd ω w =
      ∏ p ∈ (Finset.range (⌊z⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z),
        (1 - ω p) := by
  unfold siftProd
  set S_w := (Finset.range (⌊w⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) < w)
  set S_z := (Finset.range (⌊z⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ (p : ℝ) < z)
  set S_wz := (Finset.range (⌊z⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z)
  have hsub : S_w ⊆ S_z := by
    intro p hp
    simp only [S_w, S_z, Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨Nat.lt_succ_of_le (Nat.le_floor (le_trans hp.2.2.le hwz)), hp.2.1, lt_of_lt_of_le hp.2.2 hwz⟩
  have hsdiff : S_z \ S_w = S_wz := by
    ext p
    simp only [S_z, S_w, S_wz, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨hr, hp, hltz⟩, hnot⟩
      refine ⟨hr, hp, ?_, hltz⟩
      by_contra hltw
      push Not at hltw
      exact hnot ⟨Nat.lt_succ_of_le (Nat.le_floor hltw.le), hp, hltw⟩
    · rintro ⟨hr, hp, hwp, hltz⟩
      exact ⟨⟨hr, hp, hltz⟩, fun h => not_lt.mpr hwp h.2.2⟩
  have hPw_pos : 0 < ∏ p ∈ S_w, (1 - ω p) :=
    Finset.prod_pos fun p _ => sub_pos.mpr (hlt p)
  rw [← Finset.prod_sdiff hsub, hsdiff, mul_div_cancel_right₀ _ hPw_pos.ne']

/-- Quantitative two-sided Mertens ratio for prime products over `[w, z)` for sufficiently large `w`. -/
private lemma prime_mertens_ico_two_sided :
    ∃ x₀ K_M : ℝ, 3 ≤ x₀ ∧ 1 ≤ K_M ∧
      ∀ w z : ℝ, x₀ ≤ w → w ≤ z →
        (Real.log w / Real.log z) * (1 - K_M / Real.log w) ≤
          ∏ p ∈ (Finset.range (⌊z⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z),
            (1 - (p : ℝ)⁻¹) ∧
        ∏ p ∈ (Finset.range (⌊z⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z),
            (1 - (p : ℝ)⁻¹) ≤
          (Real.log w / Real.log z) * (1 + K_M / Real.log w) ∧
        ∏ p ∈ (Finset.range (⌊z⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z),
            (1 - (p : ℝ)⁻¹)⁻¹ ≤
          (Real.log z / Real.log w) * (1 + K_M / Real.log w) := by
  obtain ⟨C, hC_pos, hMert⟩ := Stage8MertensTheorems.mertens_third_theorem_quant
  set E : ℝ := Real.exp (-Real.eulerMascheroniConstant) with hE_def
  have hE_pos : 0 < E := Real.exp_pos _
  set A : ℝ := C / E with hA_def
  have hA_pos : 0 < A := div_pos hC_pos hE_pos
  set x₀ : ℝ := max 3 (Real.exp (2 * A)) with hx₀_def
  have hx₀_ge3 : 3 ≤ x₀ := le_max_left _ _
  have hlog_x₀_ge : 2 * A ≤ Real.log x₀ := by
    have h1 := Real.log_le_log (Real.exp_pos _) (le_max_right (3 : ℝ) (Real.exp (2 * A)))
    rwa [Real.log_exp] at h1
  set K_M : ℝ := max 1 (12 * A + 6) with hKM_def
  have hKM_ge1 : 1 ≤ K_M := le_max_left _ _
  refine ⟨x₀, K_M, hx₀_ge3, hKM_ge1, fun w z hwx₀ hwz => ?_⟩
  have hw3 : 3 ≤ w := le_trans hx₀_ge3 hwx₀
  have hz3 : 3 ≤ z := le_trans hw3 hwz
  have hlw_pos : 0 < Real.log w := Real.log_pos (by linarith)
  have hlz_pos : 0 < Real.log z := Real.log_pos (by linarith)
  have hlw_le_hlz : Real.log w ≤ Real.log z := Real.log_le_log (by linarith) hwz
  have hlw_ge_2A : 2 * A ≤ Real.log w :=
    hlog_x₀_ge.trans (Real.log_le_log (by linarith) hwx₀)
  have hMw_pos : 0 < Stage8MertensTheorems.mertensProd w := Stage8MertensTheorems.mertensProd_pos w
  have hMz_pos : 0 < Stage8MertensTheorems.mertensProd z := Stage8MertensTheorems.mertensProd_pos z
  -- Set `a = A / log w ≤ 1/2` and `b = A / log z ≤ a`
  set a : ℝ := A / Real.log w with ha_def
  set b : ℝ := A / Real.log z with hb_def
  have ha_pos : 0 < a := div_pos hA_pos hlw_pos
  have hb_pos : 0 < b := div_pos hA_pos hlz_pos
  have hba : b ≤ a := div_le_div_of_nonneg_left hA_pos.le hlw_pos hlw_le_hlz
  have ha_half : a ≤ 1 / 2 := by
    rw [ha_def, div_le_iff₀ hlw_pos]; linarith
  -- Quantitative Mertens bounds on `log w * M(w)` and `log z * M(z)`
  have hMw_abs : |Real.log w * Stage8MertensTheorems.mertensProd w - E| ≤ E * a := by
    have h := hMert w hw3
    have hEq : C / Real.log w = E * a := by
      rw [ha_def, hA_def]; field_simp [hE_pos.ne', hlw_pos.ne']
    rw [← hEq]; exact h
  have hMz_abs : |Real.log z * Stage8MertensTheorems.mertensProd z - E| ≤ E * b := by
    have h := hMert z hz3
    have hEq : C / Real.log z = E * b := by
      rw [hb_def, hA_def]; field_simp [hE_pos.ne', hlz_pos.ne']
    rw [← hEq]; exact h
  have hMw_lo : E * (1 - a) ≤ Real.log w * Stage8MertensTheorems.mertensProd w := by
    linarith [(abs_le.mp hMw_abs).1]
  have hMw_hi : Real.log w * Stage8MertensTheorems.mertensProd w ≤ E * (1 + a) := by
    linarith [(abs_le.mp hMw_abs).2]
  have hMz_lo : E * (1 - b) ≤ Real.log z * Stage8MertensTheorems.mertensProd z := by
    linarith [(abs_le.mp hMz_abs).1]
  have hMz_hi : Real.log z * Stage8MertensTheorems.mertensProd z ≤ E * (1 + b) := by
    linarith [(abs_le.mp hMz_abs).2]
  -- Ratio bounds on `M(z) / M(w)` and `M(w) / M(z)`
  have hMz_div_Mw_lo :
      (Real.log w / Real.log z) * (1 - 2 * a) ≤
        Stage8MertensTheorems.mertensProd z / Stage8MertensTheorems.mertensProd w := by
    have hrat : (1 - b) / (1 + a) ≤ (Real.log z * Stage8MertensTheorems.mertensProd z) /
        (Real.log w * Stage8MertensTheorems.mertensProd w) := by
      have h1 : (E * (1 - b)) / (E * (1 + a)) ≤
          (Real.log z * Stage8MertensTheorems.mertensProd z) /
          (Real.log w * Stage8MertensTheorems.mertensProd w) :=
        div_le_div₀ (by positivity) hMz_lo (by positivity) hMw_hi
      have h2 : (E * (1 - b)) / (E * (1 + a)) = (1 - b) / (1 + a) := by
        field_simp [hE_pos.ne']
      linarith
    have h12 : 1 - 2 * a ≤ (1 - b) / (1 + a) := by
      rw [le_div_iff₀ (by linarith : 0 < 1 + a)]
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left (h12.trans hrat) (div_nonneg hlw_pos.le hlz_pos.le)
    have hsimp : (Real.log w / Real.log z) *
        ((Real.log z * Stage8MertensTheorems.mertensProd z) /
          (Real.log w * Stage8MertensTheorems.mertensProd w)) =
        Stage8MertensTheorems.mertensProd z / Stage8MertensTheorems.mertensProd w := by
      field_simp [hlw_pos.ne', hlz_pos.ne', hMw_pos.ne']
    linarith
  have hMz_div_Mw_hi :
      Stage8MertensTheorems.mertensProd z / Stage8MertensTheorems.mertensProd w ≤
        (Real.log w / Real.log z) * (1 + 4 * a) := by
    have hrat : (Real.log z * Stage8MertensTheorems.mertensProd z) /
        (Real.log w * Stage8MertensTheorems.mertensProd w) ≤ (1 + b) / (1 - a) := by
      have h1 : (Real.log z * Stage8MertensTheorems.mertensProd z) /
          (Real.log w * Stage8MertensTheorems.mertensProd w) ≤
          (E * (1 + b)) / (E * (1 - a)) :=
        div_le_div₀ (by positivity) hMz_hi (by nlinarith) hMw_lo
      have h2 : (E * (1 + b)) / (E * (1 - a)) = (1 + b) / (1 - a) := by
        field_simp [hE_pos.ne']
      linarith
    have h12 : (1 + b) / (1 - a) ≤ 1 + 4 * a := by
      rw [div_le_iff₀ (by linarith : 0 < 1 - a)]
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left (hrat.trans h12) (div_nonneg hlw_pos.le hlz_pos.le)
    have hsimp : (Real.log w / Real.log z) *
        ((Real.log z * Stage8MertensTheorems.mertensProd z) /
          (Real.log w * Stage8MertensTheorems.mertensProd w)) =
        Stage8MertensTheorems.mertensProd z / Stage8MertensTheorems.mertensProd w := by
      field_simp [hlw_pos.ne', hlz_pos.ne', hMw_pos.ne']
    linarith
  have hMw_div_Mz_hi :
      Stage8MertensTheorems.mertensProd w / Stage8MertensTheorems.mertensProd z ≤
        (Real.log z / Real.log w) * (1 + 4 * a) := by
    have hrat : (Real.log w * Stage8MertensTheorems.mertensProd w) /
        (Real.log z * Stage8MertensTheorems.mertensProd z) ≤ (1 + a) / (1 - b) := by
      have h1 : (Real.log w * Stage8MertensTheorems.mertensProd w) /
          (Real.log z * Stage8MertensTheorems.mertensProd z) ≤
          (E * (1 + a)) / (E * (1 - b)) :=
        div_le_div₀ (by positivity) hMw_hi (by nlinarith) hMz_lo
      have h2 : (E * (1 + a)) / (E * (1 - b)) = (1 + a) / (1 - b) := by
        field_simp [hE_pos.ne']
      linarith
    have h12 : (1 + a) / (1 - b) ≤ 1 + 4 * a := by
      rw [div_le_iff₀ (by linarith : 0 < 1 - b)]
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left (hrat.trans h12) (div_nonneg hlz_pos.le hlw_pos.le)
    have hsimp : (Real.log z / Real.log w) *
        ((Real.log w * Stage8MertensTheorems.mertensProd w) /
          (Real.log z * Stage8MertensTheorems.mertensProd z)) =
        Stage8MertensTheorems.mertensProd w / Stage8MertensTheorems.mertensProd z := by
      field_simp [hlw_pos.ne', hlz_pos.ne', hMz_pos.ne']
    linarith
  -- Bridge from `M(z) / M(w)` to `∏_{w ≤ p < z} (1 - p⁻¹) = primeMertensLt z / primeMertensLt w`
  let ω₁ : ℕ → ℝ := fun p => if p.Prime then (p : ℝ)⁻¹ else 0
  have hω₁_lt : ∀ p : ℕ, ω₁ p < 1 := fun p => by
    dsimp only [ω₁]; split_ifs with hp
    · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
      have : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
      linarith
    · norm_num
  have hP_ico_eq :
      ∏ p ∈ (Finset.range (⌊z⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z),
          (1 - (p : ℝ)⁻¹) =
        primeMertensLt z / primeMertensLt w := by
    have h1 := siftProd_div_eq_prod_ico hω₁_lt hwz
    have hsw : siftProd ω₁ w = primeMertensLt w := by
      unfold siftProd primeMertensLt
      refine Finset.prod_congr rfl fun p hp => ?_
      dsimp only [ω₁]; rw [if_pos (Finset.mem_filter.mp hp).2.1]
    have hsz : siftProd ω₁ z = primeMertensLt z := by
      unfold siftProd primeMertensLt
      refine Finset.prod_congr rfl fun p hp => ?_
      dsimp only [ω₁]; rw [if_pos (Finset.mem_filter.mp hp).2.1]
    have hico :
        ∏ p ∈ (Finset.range (⌊z⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z),
            (1 - ω₁ p) =
          ∏ p ∈ (Finset.range (⌊z⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z),
            (1 - (p : ℝ)⁻¹) := by
      refine Finset.prod_congr rfl fun p hp => ?_
      dsimp only [ω₁]; rw [if_pos (Finset.mem_filter.mp hp).2.1]
    rw [hsw, hsz, hico] at h1
    exact h1.symm
  have hPlt_w_pos : 0 < primeMertensLt w := primeMertensLt_pos w
  have hPlt_z_pos : 0 < primeMertensLt z := primeMertensLt_pos z
  have h1w_pos : 0 < 1 - w⁻¹ := by
    have : w⁻¹ ≤ (3 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hw3
    linarith
  have h1z_pos : 0 < 1 - z⁻¹ := by
    have : z⁻¹ ≤ (3 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hz3
    linarith
  have hlogw_le_w : Real.log w ≤ w := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hwinv_le : w⁻¹ ≤ 1 / Real.log w := by
    rw [one_div]; exact inv_anti₀ hlw_pos hlogw_le_w
  have hzinv_le : z⁻¹ ≤ 1 / Real.log w :=
    (inv_anti₀ (by linarith) hwz).trans hwinv_le
  have hinv_1w_le : (1 - w⁻¹)⁻¹ ≤ 1 + 2 / Real.log w := by
    have h1 : (1 - w⁻¹)⁻¹ ≤ 1 + 2 * w⁻¹ := by
      rw [inv_le_iff_one_le_mul₀ h1w_pos]
      have h3 : w⁻¹ ≤ 1 / 3 := by
        rw [← one_div]; exact one_div_le_one_div_of_le (by norm_num) hw3
      nlinarith [inv_nonneg.mpr (show 0 ≤ w by linarith)]
    have h2 : 2 * w⁻¹ ≤ 2 / Real.log w := by
      have hm := mul_le_mul_of_nonneg_left hwinv_le (by norm_num : (0 : ℝ) ≤ 2)
      rwa [mul_one_div] at hm
    linarith
  have hinv_1z_le : (1 - z⁻¹)⁻¹ ≤ 1 + 2 / Real.log w := by
    have h1 : (1 - z⁻¹)⁻¹ ≤ (1 - w⁻¹)⁻¹ :=
      inv_anti₀ h1w_pos (by linarith [inv_anti₀ (by linarith : (0 : ℝ) < w) hwz])
    exact h1.trans hinv_1w_le
  have hKM_ge : 12 * A + 6 ≤ K_M := le_max_right _ _
  have hlogw_ge1 : 1 ≤ Real.log w := by
    have h3 : (1 : ℝ) < Real.log 3 := by
      have he : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ < Real.log 3 := Real.log_lt_log (Real.exp_pos 1) he
    exact le_trans h3.le (Real.log_le_log (by norm_num) hw3)
  -- Three target inequalities
  have hlo : (Real.log w / Real.log z) * (1 - K_M / Real.log w) ≤
      primeMertensLt z / primeMertensLt w := by
    have h1 : (1 - w⁻¹) * (Stage8MertensTheorems.mertensProd z / Stage8MertensTheorems.mertensProd w) ≤
        primeMertensLt z / primeMertensLt w := by
      have hnum : Stage8MertensTheorems.mertensProd z ≤ primeMertensLt z := mertensProd_le_primeMertensLt
      have hden := one_sub_inv_mul_primeMertensLt_le_mertensProd (by linarith : 2 ≤ w)
      have hdiv : Stage8MertensTheorems.mertensProd z / Stage8MertensTheorems.mertensProd w ≤
          primeMertensLt z / ((1 - w⁻¹) * primeMertensLt w) :=
        div_le_div₀ hPlt_z_pos.le hnum (mul_pos h1w_pos hPlt_w_pos) hden
      have hmul := mul_le_mul_of_nonneg_left hdiv h1w_pos.le
      have hsimp : (1 - w⁻¹) * (primeMertensLt z / ((1 - w⁻¹) * primeMertensLt w)) =
          primeMertensLt z / primeMertensLt w := by
        rw [mul_div_assoc', mul_div_mul_left _ _ h1w_pos.ne']
      linarith
    have h2 : (1 - 1 / Real.log w) * ((Real.log w / Real.log z) * (1 - 2 * a)) ≤
        (1 - w⁻¹) * (Stage8MertensTheorems.mertensProd z / Stage8MertensTheorems.mertensProd w) := by
      have h12 : 1 - 1 / Real.log w ≤ 1 - w⁻¹ := by linarith
      have hnn : 0 ≤ (Real.log w / Real.log z) * (1 - 2 * a) :=
        mul_nonneg (div_nonneg hlw_pos.le hlz_pos.le) (by linarith)
      exact mul_le_mul h12 hMz_div_Mw_lo hnn h1w_pos.le
    have h3 : (1 - K_M / Real.log w) ≤ (1 - 1 / Real.log w) * (1 - 2 * a) := by
      have hprod : (1 - 1 / Real.log w) * (1 - 2 * a) =
          1 - (2 * A + 1) / Real.log w + (2 * a) / Real.log w := by rw [ha_def]; ring
      rw [hprod]
      have hnn : 0 ≤ (2 * a) / Real.log w := by positivity
      have hdiv_le : (2 * A + 1) / Real.log w ≤ K_M / Real.log w :=
        div_le_div_of_nonneg_right (by linarith) hlw_pos.le
      linarith
    have h4 := mul_le_mul_of_nonneg_left h3 (div_nonneg hlw_pos.le hlz_pos.le)
    linarith
  have hhi : primeMertensLt z / primeMertensLt w ≤
      (Real.log w / Real.log z) * (1 + K_M / Real.log w) := by
    have h1 : primeMertensLt z / primeMertensLt w ≤
        (1 - z⁻¹)⁻¹ * (Stage8MertensTheorems.mertensProd z / Stage8MertensTheorems.mertensProd w) := by
      have hnum := one_sub_inv_mul_primeMertensLt_le_mertensProd (by linarith : 2 ≤ z)
      have hden : Stage8MertensTheorems.mertensProd w ≤ primeMertensLt w := mertensProd_le_primeMertensLt
      have hdiv : ((1 - z⁻¹) * primeMertensLt z) / primeMertensLt w ≤
          Stage8MertensTheorems.mertensProd z / Stage8MertensTheorems.mertensProd w :=
        div_le_div₀ hMz_pos.le hnum hMw_pos hden
      have hmul := mul_le_mul_of_nonneg_left hdiv (inv_nonneg.mpr h1z_pos.le)
      have hsimp : (1 - z⁻¹)⁻¹ * (((1 - z⁻¹) * primeMertensLt z) / primeMertensLt w) =
          primeMertensLt z / primeMertensLt w := by
        rw [mul_div_assoc', ← mul_assoc, inv_mul_cancel₀ h1z_pos.ne', one_mul]
      linarith
    have h2 : (1 - z⁻¹)⁻¹ * (Stage8MertensTheorems.mertensProd z / Stage8MertensTheorems.mertensProd w) ≤
        (1 + 2 / Real.log w) * ((Real.log w / Real.log z) * (1 + 4 * a)) :=
      mul_le_mul hinv_1z_le hMz_div_Mw_hi (div_nonneg hMz_pos.le hMw_pos.le) (by positivity)
    have h3 : (1 + 2 / Real.log w) * (1 + 4 * a) ≤ 1 + K_M / Real.log w := by
      have h1_le : (1 : ℝ) / Real.log w ≤ 1 := by
        rw [div_le_one hlw_pos]; exact hlogw_ge1
      have hprod : (1 + 2 / Real.log w) * (1 + 4 * a) =
          1 + (4 * A + 2) / Real.log w + (8 * A / Real.log w) * (1 / Real.log w) := by
        rw [ha_def]; ring
      rw [hprod]
      have hmul : (8 * A / Real.log w) * (1 / Real.log w) ≤ (8 * A / Real.log w) * 1 :=
        mul_le_mul_of_nonneg_left h1_le (by positivity)
      have hsum : (4 * A + 2) / Real.log w + 8 * A / Real.log w = (12 * A + 2) / Real.log w := by ring
      have hdiv_le : (12 * A + 2) / Real.log w ≤ K_M / Real.log w :=
        div_le_div_of_nonneg_right (by linarith) hlw_pos.le
      linarith
    have h4 := mul_le_mul_of_nonneg_left h3 (div_nonneg hlw_pos.le hlz_pos.le)
    linarith
  have hinv : (primeMertensLt z / primeMertensLt w)⁻¹ ≤
      (Real.log z / Real.log w) * (1 + K_M / Real.log w) := by
    rw [inv_div]
    have h1 : primeMertensLt w / primeMertensLt z ≤
        (1 - w⁻¹)⁻¹ * (Stage8MertensTheorems.mertensProd w / Stage8MertensTheorems.mertensProd z) := by
      have hnum := one_sub_inv_mul_primeMertensLt_le_mertensProd (by linarith : 2 ≤ w)
      have hden : Stage8MertensTheorems.mertensProd z ≤ primeMertensLt z := mertensProd_le_primeMertensLt
      have hdiv : ((1 - w⁻¹) * primeMertensLt w) / primeMertensLt z ≤
          Stage8MertensTheorems.mertensProd w / Stage8MertensTheorems.mertensProd z :=
        div_le_div₀ hMw_pos.le hnum hMz_pos hden
      have hmul := mul_le_mul_of_nonneg_left hdiv (inv_nonneg.mpr h1w_pos.le)
      have hsimp : (1 - w⁻¹)⁻¹ * (((1 - w⁻¹) * primeMertensLt w) / primeMertensLt z) =
          primeMertensLt w / primeMertensLt z := by
        rw [mul_div_assoc', ← mul_assoc, inv_mul_cancel₀ h1w_pos.ne', one_mul]
      linarith
    have h2 : (1 - w⁻¹)⁻¹ * (Stage8MertensTheorems.mertensProd w / Stage8MertensTheorems.mertensProd z) ≤
        (1 + 2 / Real.log w) * ((Real.log z / Real.log w) * (1 + 4 * a)) :=
      mul_le_mul hinv_1w_le hMw_div_Mz_hi (div_nonneg hMw_pos.le hMz_pos.le) (by positivity)
    have h3 : (1 + 2 / Real.log w) * (1 + 4 * a) ≤ 1 + K_M / Real.log w := by
      have h1_le : (1 : ℝ) / Real.log w ≤ 1 := by
        rw [div_le_one hlw_pos]; exact hlogw_ge1
      have hprod : (1 + 2 / Real.log w) * (1 + 4 * a) =
          1 + (4 * A + 2) / Real.log w + (8 * A / Real.log w) * (1 / Real.log w) := by
        rw [ha_def]; ring
      rw [hprod]
      have hmul : (8 * A / Real.log w) * (1 / Real.log w) ≤ (8 * A / Real.log w) * 1 :=
        mul_le_mul_of_nonneg_left h1_le (by positivity)
      have hsum : (4 * A + 2) / Real.log w + 8 * A / Real.log w = (12 * A + 2) / Real.log w := by ring
      have hdiv_le : (12 * A + 2) / Real.log w ≤ K_M / Real.log w :=
        div_le_div_of_nonneg_right (by linarith) hlw_pos.le
      linarith
    have h4 := mul_le_mul_of_nonneg_left h3 (div_nonneg hlz_pos.le hlw_pos.le)
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rwa [hP_ico_eq]
  · rwa [hP_ico_eq]
  · rw [Finset.prod_inv_distrib, hP_ico_eq]
    exact hinv

/-- Global prime Mertens upper bound for all `2 ≤ w ≤ z`. -/
private lemma prime_mertens_ico_inv_global :
    ∃ K_p : ℝ, 1 ≤ K_p ∧
      ∀ w z : ℝ, 2 ≤ w → w ≤ z →
        ∏ p ∈ (Finset.range (⌊z⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z),
            (1 - (p : ℝ)⁻¹)⁻¹ ≤
          (Real.log z / Real.log w) * (1 + K_p / Real.log w) := by
  obtain ⟨x₀, K_M, hx₀3, hKM1, hmert⟩ := prime_mertens_ico_two_sided
  have hM0_pos : 0 < Stage8MertensTheorems.mertensProd x₀ := Stage8MertensTheorems.mertensProd_pos x₀
  have hlx₀_pos : 0 < Real.log x₀ := Real.log_pos (by linarith)
  set C_lo : ℝ := (Stage8MertensTheorems.mertensProd x₀)⁻¹ * (1 + K_M / Real.log x₀) * Real.log x₀ with hClo_def
  set K_p : ℝ := max K_M C_lo with hKp_def
  have hKp1 : 1 ≤ K_p := le_trans hKM1 (le_max_left _ _)
  refine ⟨K_p, hKp1, fun w z hw2 hwz => ?_⟩
  have hlw_pos : 0 < Real.log w := Real.log_pos (by linarith)
  have hlz_pos : 0 < Real.log z := Real.log_pos (by linarith)
  -- Helper: any sub-product of `(1 - p⁻¹)⁻¹` for `p < x₀` is `≤ (mertensProd x₀)⁻¹`
  have hsub_le_M0 : ∀ u v : ℝ, 2 ≤ u → u ≤ v → v ≤ x₀ →
      ∏ p ∈ (Finset.range (⌊v⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < v),
          (1 - (p : ℝ)⁻¹)⁻¹ ≤ (Stage8MertensTheorems.mertensProd x₀)⁻¹ := by
    intro u v _hu2 _huv hvx₀
    unfold Stage8MertensTheorems.mertensProd
    rw [← Finset.prod_inv_distrib]
    set S_sm := (Finset.range (⌊v⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ u ≤ (p : ℝ) ∧ (p : ℝ) < v)
    set S_bg := (Finset.Icc 1 ⌊x₀⌋₊).filter Nat.Prime
    have hsub : S_sm ⊆ S_bg := by
      intro p hp
      simp only [S_sm, S_bg, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hp ⊢
      exact ⟨⟨hp.2.1.one_lt.le, Nat.le_floor (le_trans hp.2.2.2.le hvx₀)⟩, hp.2.1⟩
    rw [← Finset.prod_sdiff hsub]
    have h1 : 1 ≤ ∏ p ∈ S_bg \ S_sm, (1 - (p : ℝ)⁻¹)⁻¹ :=
      one_le_prod_of_ge_one _ _ fun p hp => by
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
          exact_mod_cast (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).2.two_le
        have hpos : 0 < 1 - (p : ℝ)⁻¹ := by
          have : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
          linarith
        exact one_le_inv₀ hpos |>.mpr (by linarith [inv_nonneg.mpr (show 0 ≤ (p : ℝ) by positivity)])
    have hsm_nn : 0 ≤ ∏ p ∈ S_sm, (1 - (p : ℝ)⁻¹)⁻¹ :=
      Finset.prod_nonneg fun p hp => by
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.1.two_le
        have : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
        exact inv_nonneg.mpr (by linarith)
    nlinarith
  by_cases hwx₀ : x₀ ≤ w
  · have h := (hmert w z hwx₀ hwz).2.2
    have hK_le : K_M ≤ K_p := le_max_left _ _
    have hmul : (Real.log z / Real.log w) * (1 + K_M / Real.log w) ≤
        (Real.log z / Real.log w) * (1 + K_p / Real.log w) :=
      mul_le_mul_of_nonneg_left
        (by linarith [div_le_div_of_nonneg_right hK_le hlw_pos.le])
        (div_nonneg hlz_pos.le hlw_pos.le)
    exact h.trans hmul
  · push Not at hwx₀
    have hlw_le_lx₀ : Real.log w ≤ Real.log x₀ := Real.log_le_log (by linarith) hwx₀.le
    by_cases hzx₀ : z ≤ x₀
    · have h1 := hsub_le_M0 w z hw2 hwz hzx₀
      have h2 : (Stage8MertensTheorems.mertensProd x₀)⁻¹ ≤ C_lo / Real.log w := by
        rw [hClo_def, le_div_iff₀ hlw_pos]
        have hrat : 1 ≤ (1 + K_M / Real.log x₀) := by linarith [div_nonneg (by linarith : 0 ≤ K_M) hlx₀_pos.le]
        have hM_nn : 0 ≤ (Stage8MertensTheorems.mertensProd x₀)⁻¹ := inv_nonneg.mpr hM0_pos.le
        have hstep1 : (Stage8MertensTheorems.mertensProd x₀)⁻¹ * Real.log w ≤
            (Stage8MertensTheorems.mertensProd x₀)⁻¹ * Real.log x₀ :=
          mul_le_mul_of_nonneg_left hlw_le_lx₀ hM_nn
        have hstep2 : (Stage8MertensTheorems.mertensProd x₀)⁻¹ * Real.log x₀ ≤
            (Stage8MertensTheorems.mertensProd x₀)⁻¹ * (1 + K_M / Real.log x₀) * Real.log x₀ := by
          have := mul_le_mul_of_nonneg_left hrat hM_nn
          have := mul_le_mul_of_nonneg_right this hlx₀_pos.le
          linarith
        linarith
      have h3 : 1 ≤ Real.log z / Real.log w := (one_le_div hlw_pos).mpr (Real.log_le_log (by linarith) hwz)
      have h4 : C_lo / Real.log w ≤ 1 + K_p / Real.log w := by
        have := div_le_div_of_nonneg_right (le_max_right K_M C_lo) hlw_pos.le
        linarith
      have h5 : 1 + K_p / Real.log w ≤ (Real.log z / Real.log w) * (1 + K_p / Real.log w) := by
        have hnn : 0 ≤ 1 + K_p / Real.log w := by positivity
        nlinarith
      exact h1.trans (h2.trans (h4.trans h5))
    · push Not at hzx₀
      -- Split `[w, z) = [w, x₀) ∪ [x₀, z)`
      set S_all := (Finset.range (⌊z⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z)
      set S_lo := (Finset.range (⌊x₀⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < x₀)
      set S_hi := (Finset.range (⌊z⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ x₀ ≤ (p : ℝ) ∧ (p : ℝ) < z)
      have hdisj : Disjoint S_lo S_hi := by
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        simp only [S_lo, S_hi, Finset.mem_filter] at hp1 hp2
        linarith
      have hunion : S_all = S_lo ∪ S_hi := by
        ext p
        simp only [S_all, S_lo, S_hi, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨hr, hp, hwp, hltz⟩
          by_cases hpx : (p : ℝ) < x₀
          · exact Or.inl ⟨Nat.lt_succ_of_le (Nat.le_floor hpx.le), hp, hwp, hpx⟩
          · exact Or.inr ⟨hr, hp, not_lt.mp hpx, hltz⟩
        · rintro (⟨_, hp, hwp, hpx⟩ | ⟨hr, hp, hpx, hltz⟩)
          · exact ⟨Nat.lt_succ_of_le (Nat.le_floor (lt_trans hpx hzx₀).le), hp, hwp, lt_trans hpx hzx₀⟩
          · exact ⟨hr, hp, le_trans hwx₀.le hpx, hltz⟩
      have hsplit : ∏ p ∈ S_all, (1 - (p : ℝ)⁻¹)⁻¹ =
          (∏ p ∈ S_lo, (1 - (p : ℝ)⁻¹)⁻¹) * (∏ p ∈ S_hi, (1 - (p : ℝ)⁻¹)⁻¹) := by
        rw [hunion, Finset.prod_union hdisj]
      change ∏ p ∈ S_all, (1 - (p : ℝ)⁻¹)⁻¹ ≤ _
      rw [hsplit]
      have hlo_bd := hsub_le_M0 w x₀ hw2 hwx₀.le le_rfl
      have hhi_bd := (hmert x₀ z le_rfl hzx₀.le).2.2
      have hhi_nn : 0 ≤ ∏ p ∈ S_hi, (1 - (p : ℝ)⁻¹)⁻¹ :=
        Finset.prod_nonneg fun p hp => by
          have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.1.two_le
          have : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
          exact inv_nonneg.mpr (by linarith)
      have hprod_le := mul_le_mul hlo_bd hhi_bd hhi_nn (inv_nonneg.mpr hM0_pos.le)
      have hrew : (Stage8MertensTheorems.mertensProd x₀)⁻¹ *
          ((Real.log z / Real.log x₀) * (1 + K_M / Real.log x₀)) =
          (Real.log z / Real.log w) * ((C_lo / Real.log w) * (Real.log w / Real.log x₀) ^ 2) := by
        rw [hClo_def]; field_simp [hlw_pos.ne', hlx₀_pos.ne']
      have hsq_le1 : (Real.log w / Real.log x₀) ^ 2 ≤ 1 := by
        have hrat_le1 : Real.log w / Real.log x₀ ≤ 1 := (div_le_one hlx₀_pos).mpr hlw_le_lx₀
        have hrat_nn : 0 ≤ Real.log w / Real.log x₀ := div_nonneg hlw_pos.le hlx₀_pos.le
        nlinarith
      have hClo_nn : 0 ≤ C_lo / Real.log w := by positivity
      have hstep : (C_lo / Real.log w) * (Real.log w / Real.log x₀) ^ 2 ≤ 1 + K_p / Real.log w := by
        have h1 : (C_lo / Real.log w) * (Real.log w / Real.log x₀) ^ 2 ≤ (C_lo / Real.log w) * 1 :=
          mul_le_mul_of_nonneg_left hsq_le1 hClo_nn
        have h2 : C_lo / Real.log w ≤ K_p / Real.log w :=
          div_le_div_of_nonneg_right (le_max_right K_M C_lo) hlw_pos.le
        linarith
      exact hprod_le.trans (by
        rw [hrew]
        exact mul_le_mul_of_nonneg_left hstep (div_nonneg hlz_pos.le hlw_pos.le))

/-- Positivity of the Chen Goldbach sifting product `V(chenPrimeDensity N, z)` for all `N, z`. -/
theorem siftProd_chenPrimeDensity_pos (N : ℕ) (z : ℝ) :
    0 < siftProd (chenPrimeDensity N) z := by
  unfold siftProd
  refine Finset.prod_pos fun p hp => ?_
  unfold chenPrimeDensity
  split_ifs with h
  · have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
      have h2 := h.1.two_le
      have hne := h.2.1
      exact_mod_cast (show 3 ≤ p by omega)
    have h1 : (1 : ℝ) / ((p : ℝ) - 1) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  · norm_num

/-- **UNIFORM CHEN PRIME DENSITY (`LinearSieveDensity`)**:
There exists an ABSOLUTE constant `K ≥ 1` (independent of `N`!) such that
`chenPrimeDensity N` satisfies `LinearSieveDensity (chenPrimeDensity N) K` for EVERY `N : ℕ`. -/
theorem chenPrimeDensity_linearSieve :
    ∃ K : ℝ, ∀ N : ℕ, LinearSieveDensity (chenPrimeDensity N) K := by
  obtain ⟨K_p, hKp1, hMp⟩ := prime_mertens_ico_inv_global
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K : ℝ := K_p + 12 + 12 * K_p / Real.log 2 with hK_def
  have hK1 : 1 ≤ K := by
    have : 0 ≤ 12 * K_p / Real.log 2 := by positivity
    linarith
  refine ⟨K, fun N => ?_⟩
  refine
    { K_ge_one := hK1
      nonneg := fun p => by
        unfold chenPrimeDensity
        split_ifs with h
        · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h.1.two_le
          have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
          positivity
        · exact le_rfl
      lt_one := fun p => by
        unfold chenPrimeDensity
        split_ifs with h
        · have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
            have h2 := h.1.two_le; have hne := h.2.1
            exact_mod_cast (show 3 ≤ p by omega)
          have : (1 : ℝ) / ((p : ℝ) - 1) ≤ 1 / 2 :=
            one_div_le_one_div_of_le (by norm_num) (by linarith)
          linarith
        · norm_num
      support_prime := fun n hn => by
        unfold chenPrimeDensity; rw [if_neg (fun h => hn h.1)]
      mertens_ratio := fun w z hw2 hwz => ?_ }
  set S := (Finset.range (⌊z⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z)
  have hlw_pos : 0 < Real.log w := Real.log_pos (by linarith)
  have hlz_pos : 0 < Real.log z := Real.log_pos (by linarith)
  -- Pointwise comparison: `(1 - chenPrimeDensity N p)⁻¹ ≤ (1 - p⁻¹)⁻¹ * g(p)`
  let g : ℕ → ℝ := fun p => if 3 ≤ p then 1 + 1 / ((p : ℝ) * ((p : ℝ) - 2)) else 1
  have hpt : ∀ p ∈ S, (1 - chenPrimeDensity N p)⁻¹ ≤ (1 - (p : ℝ)⁻¹)⁻¹ * g p := by
    intro p hp
    have hpr : p.Prime := (Finset.mem_filter.mp hp).2.1
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpr.two_le
    have h1p_pos : 0 < 1 - (p : ℝ)⁻¹ := by
      have : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
      linarith
    have h1p_ge1 : 1 ≤ (1 - (p : ℝ)⁻¹)⁻¹ :=
      one_le_inv₀ h1p_pos |>.mpr (by linarith [inv_nonneg.mpr (show 0 ≤ (p : ℝ) by positivity)])
    unfold chenPrimeDensity
    split_ifs with h
    · have hp3_nat : 3 ≤ p := by have := h.1.two_le; have := h.2.1; omega
      have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3_nat
      dsimp only [g]; rw [if_pos hp3_nat]
      have hne0 : (p : ℝ) ≠ 0 := by linarith
      have hne1 : (p : ℝ) - 1 ≠ 0 := by linarith
      have hne2 : (p : ℝ) - 2 ≠ 0 := by linarith
      have heq : (1 - 1 / ((p : ℝ) - 1))⁻¹ =
          (1 - (p : ℝ)⁻¹)⁻¹ * (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))) := by
        have h1 : 1 - 1 / ((p : ℝ) - 1) = ((p : ℝ) - 2) / ((p : ℝ) - 1) := by field_simp [hne1]; ring
        have h2 : 1 - (p : ℝ)⁻¹ = ((p : ℝ) - 1) / (p : ℝ) := by field_simp [hne0]
        rw [h1, h2, inv_div, inv_div]
        field_simp [hne0, hne1, hne2]
        ring
      exact heq.le
    · rw [sub_zero, inv_one]
      have hg1 : 1 ≤ g p := by
        dsimp only [g]; split_ifs with h3
        · have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
          have : 0 ≤ 1 / ((p : ℝ) * ((p : ℝ) - 2)) := by
            have : (0 : ℝ) < (p : ℝ) - 2 := by linarith
            positivity
          linarith
        · exact le_rfl
      nlinarith
  have hprod_split :
      ∏ p ∈ S, (1 - chenPrimeDensity N p)⁻¹ ≤
        (∏ p ∈ S, (1 - (p : ℝ)⁻¹)⁻¹) * (∏ p ∈ S, g p) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun p hp => ?_) hpt
    unfold chenPrimeDensity
    split_ifs with h
    · have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
        have := h.1.two_le; have := h.2.1; exact_mod_cast (show 3 ≤ p by omega)
      have : (1 : ℝ) / ((p : ℝ) - 1) ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      exact inv_nonneg.mpr (by linarith)
    · norm_num
  -- Bound `∏ p ∈ S, g p ≤ 1 + 12 / Real.log w`
  have hg_prod_le : ∏ p ∈ S, g p ≤ 1 + 12 / Real.log w := by
    let h_term : ℕ → ℝ := fun p => if 3 ≤ p then 1 / ((p : ℝ) * ((p : ℝ) - 2)) else 0
    have hstep1 : ∏ p ∈ S, g p ≤ Real.exp (∑ p ∈ S, h_term p) := by
      rw [Real.exp_sum]
      refine Finset.prod_le_prod (fun p _ => ?_) (fun p _ => ?_)
      · dsimp only [g]; split_ifs with h3
        · have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
          have : (0 : ℝ) < (p : ℝ) - 2 := by linarith
          positivity
        · norm_num
      · dsimp only [g, h_term]; split_ifs
        · linarith [Real.add_one_le_exp (1 / ((p : ℝ) * ((p : ℝ) - 2)))]
        · simp
    set m : ℕ := max 3 ⌊w⌋₊ with hm_def
    have hm3 : 3 ≤ m := le_max_left _ _
    have hm_fl : ⌊w⌋₊ ≤ m := le_max_right _ _
    have hsum_le : ∑ p ∈ S, h_term p ≤ 2 / ((m : ℝ) - 1) := by
      have hS3 : ∑ p ∈ S, h_term p ≤
          ∑ k ∈ Finset.Icc m ⌊z⌋₊, (2 : ℝ) * (1 / (((k : ℝ) - 1 + 1) * ((k : ℝ) - 1))) := by
        have h1 : ∑ p ∈ S, h_term p =
            ∑ p ∈ S.filter (fun p => 3 ≤ p), 1 / ((p : ℝ) * ((p : ℝ) - 2)) :=
          (Finset.sum_filter (s := S) (p := fun p => 3 ≤ p)
            (f := fun p => 1 / ((p : ℝ) * ((p : ℝ) - 2)))).symm
        rw [h1]
        have hsub : S.filter (fun p => 3 ≤ p) ⊆ Finset.Icc m ⌊z⌋₊ := by
          intro p hp
          simp only [S, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hp ⊢
          refine ⟨max_le hp.2 (Nat.floor_le_of_le hp.1.2.2.1), Nat.lt_succ_iff.mp hp.1.1⟩
        have h2 : ∑ p ∈ S.filter (fun p => 3 ≤ p), 1 / ((p : ℝ) * ((p : ℝ) - 2)) ≤
            ∑ p ∈ S.filter (fun p => 3 ≤ p), (2 : ℝ) * (1 / (((p : ℝ) - 1 + 1) * ((p : ℝ) - 1))) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2
          have hden1 : 0 < (p : ℝ) * ((p : ℝ) - 2) := by nlinarith
          have hden2 : 0 < ((p : ℝ) - 1 + 1) * ((p : ℝ) - 1) := by nlinarith
          rw [mul_one_div, div_le_div_iff₀ hden1 hden2]
          nlinarith
        exact h2.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun k hk _ => by
          have hk3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_trans hm3 (Finset.mem_Icc.mp hk).1
          have : 0 < ((k : ℝ) - 1 + 1) * ((k : ℝ) - 1) := by nlinarith
          positivity)
      rw [← Finset.mul_sum] at hS3
      have htel := sum_Icc_telescope_le m ⌊z⌋₊ 1 (by
        have : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
        linarith)
      have hmul := mul_le_mul_of_nonneg_left htel (by norm_num : (0 : ℝ) ≤ 2)
      rw [mul_one_div] at hmul
      linarith
    have hsum_nn : 0 ≤ ∑ p ∈ S, h_term p := Finset.sum_nonneg fun p _ => by
      dsimp only [h_term]; split_ifs with h3
      · have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
        have : (0 : ℝ) < (p : ℝ) - 2 := by linarith
        positivity
      · exact le_rfl
    have h2m_le1 : 2 / ((m : ℝ) - 1) ≤ 1 := by
      have hm3' : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
      rw [div_le_one (by linarith)]; linarith
    have h2m_le_4w : 2 / ((m : ℝ) - 1) ≤ 4 / w := by
      by_cases hw4 : w < 4
      · have h1 : 1 ≤ 4 / w := by rw [one_le_div (by linarith)]; linarith
        exact h2m_le1.trans h1
      · push Not at hw4
        have hm_gt : w - 1 < (m : ℝ) :=
          lt_of_lt_of_le (Nat.sub_one_lt_floor w) (by exact_mod_cast hm_fl)
        have hm_sub : w / 2 ≤ (m : ℝ) - 1 := by linarith
        have hpos : 0 < w / 2 := by linarith
        have := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hpos hm_sub
        have hrew : (2 : ℝ) / (w / 2) = 4 / w := by ring
        linarith
    have h4w_le : 4 / w ≤ 4 / Real.log w :=
      div_le_div_of_nonneg_left (by norm_num) hlw_pos
        ((Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith))
    have hexp_le : Real.exp (∑ p ∈ S, h_term p) ≤ 1 + 3 * (∑ p ∈ S, h_term p) :=
      exp_le_one_add_three_mul hsum_nn (hsum_le.trans h2m_le1)
    have h12 : 3 * (4 / Real.log w) = 12 / Real.log w := by ring
    linarith
  -- Multiply the prime Mertens bound and the `g` product bound
  have hMp_bd := hMp w z hw2 hwz
  have hMp_nn : 0 ≤ ∏ p ∈ S, (1 - (p : ℝ)⁻¹)⁻¹ :=
    Finset.prod_nonneg fun p hp => by
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.1.two_le
      have : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
      exact inv_nonneg.mpr (by linarith)
  have hg_nn : 0 ≤ ∏ p ∈ S, g p :=
    Finset.prod_nonneg fun p _ => by
      dsimp only [g]; split_ifs with h3
      · have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
        have : (0 : ℝ) < (p : ℝ) - 2 := by linarith
        positivity
      · norm_num
  have hcomb := mul_le_mul hMp_bd hg_prod_le hg_nn (by positivity)
  have hfac : (1 + K_p / Real.log w) * (1 + 12 / Real.log w) ≤ 1 + K / Real.log w := by
    have hlw_ge2 : Real.log 2 ≤ Real.log w := Real.log_le_log (by norm_num) hw2
    have hinv_le : 1 / Real.log w ≤ 1 / Real.log 2 :=
      one_div_le_one_div_of_le hlog2_pos hlw_ge2
    have hprod : (1 + K_p / Real.log w) * (1 + 12 / Real.log w) =
        1 + (K_p + 12) / Real.log w + (12 * K_p / Real.log w) * (1 / Real.log w) := by ring
    rw [hprod]
    have hcross : (12 * K_p / Real.log w) * (1 / Real.log w) ≤
        (12 * K_p / Real.log w) * (1 / Real.log 2) :=
      mul_le_mul_of_nonneg_left hinv_le (by positivity)
    have hrew : (K_p + 12) / Real.log w + (12 * K_p / Real.log w) * (1 / Real.log 2) =
        K / Real.log w := by rw [hK_def]; ring
    linarith
  have hfinal := mul_le_mul_of_nonneg_left hfac (div_nonneg hlz_pos.le hlw_pos.le)
  have hassoc : (Real.log z / Real.log w) * (1 + K_p / Real.log w) * (1 + 12 / Real.log w) =
      (Real.log z / Real.log w) * ((1 + K_p / Real.log w) * (1 + 12 / Real.log w)) := by ring
  exact hprod_split.trans (hcomb.trans (by linarith))

/-- **UNIFORM CHEN SIFTING-PRODUCT RATIO FOR `w ≥ N^{1/8}`**:
Because at most `8` primes `p ≥ N^{1/8}` can divide `N`, the ratio
`siftProd (chenPrimeDensity N) z / siftProd (chenPrimeDensity N) w` equals
`(Real.log w / Real.log z) * (1 + o(1))` uniformly over ALL `N ≥ N₀` and ALL `N^{1/8} ≤ w ≤ z`. -/
theorem siftProd_chenPrimeDensity_ratio_of_ge_rpow :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ w z : ℝ, (N : ℝ) ^ ((1 : ℝ) / 8) ≤ w → w ≤ z →
        |siftProd (chenPrimeDensity N) z / siftProd (chenPrimeDensity N) w -
            Real.log w / Real.log z| ≤
          ε * (Real.log w / Real.log z) := by
  intro ε hε
  obtain ⟨x₀, K_M, hx₀3, hKM1, hmert⟩ := prime_mertens_ico_two_sided
  set δ : ℝ := min ε 1 with hδ_def
  have hδ_pos : 0 < δ := lt_min hε (by norm_num)
  have hδ_le_ε : δ ≤ ε := min_le_left _ _
  have hδ_le_1 : δ ≤ 1 := min_le_right _ _
  set L₀ : ℝ := (K_M + 48 + 48 * K_M) / δ + 1 with hL₀_def
  set W₀ : ℝ := max (max x₀ 100) (Real.exp L₀) with hW₀_def
  have hW₀_ge_x₀ : x₀ ≤ W₀ := le_trans (le_max_left _ _) (le_max_left _ _)
  have hW₀_ge_100 : 100 ≤ W₀ := le_trans (le_max_right _ _) (le_max_left _ _)
  have hW₀_ge_exp : Real.exp L₀ ≤ W₀ := le_max_right _ _
  set M₀ : ℕ := ⌈W₀⌉₊ with hM₀_def
  set N₀ : ℕ := M₀ ^ 8 + 1 with hN₀_def
  refine ⟨N₀, fun N hN w z hNw hwz => ?_⟩
  have hM₀_ge : W₀ ≤ (M₀ : ℝ) := Nat.le_ceil W₀
  have hN_ge_W₀8 : W₀ ^ 8 ≤ (N : ℝ) := by
    have h1 : W₀ ^ 8 ≤ ((M₀ : ℝ)) ^ 8 := pow_le_pow_left₀ (by linarith) hM₀_ge 8
    have h2 : ((M₀ : ℝ)) ^ 8 ≤ (N : ℝ) := by
      have : M₀ ^ 8 ≤ N := by omega
      exact_mod_cast this
    exact h1.trans h2
  have hN_pos : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℝ) < W₀ ^ 8 := pow_pos (by linarith) 8
    linarith
  have hN_gt1 : (1 : ℝ) < (N : ℝ) := by
    have : (1 : ℝ) < W₀ ^ 8 := one_lt_pow₀ (by linarith) (by norm_num)
    linarith
  have hW₀_le_w : W₀ ≤ w := by
    have h1 : W₀ = (W₀ ^ 8) ^ ((1 : ℝ) / 8) := by
      rw [← Real.rpow_natCast W₀ 8, ← Real.rpow_mul (by linarith : 0 ≤ W₀)]
      norm_num
    have h2 : (W₀ ^ 8) ^ ((1 : ℝ) / 8) ≤ (N : ℝ) ^ ((1 : ℝ) / 8) :=
      Real.rpow_le_rpow (by positivity) hN_ge_W₀8 (by positivity)
    linarith
  have hwx₀ : x₀ ≤ w := le_trans hW₀_ge_x₀ hW₀_le_w
  have hw100 : 100 ≤ w := le_trans hW₀_ge_100 hW₀_le_w
  have hlw_pos : 0 < Real.log w := Real.log_pos (by linarith)
  have hlz_pos : 0 < Real.log z := Real.log_pos (by linarith)
  have hlw_ge_L₀ : L₀ ≤ Real.log w := by
    have h1 := Real.log_le_log (Real.exp_pos _) (hW₀_ge_exp.trans hW₀_le_w)
    rwa [Real.log_exp] at h1
  have hlw_ge1 : 1 ≤ Real.log w := by
    have : 0 ≤ (K_M + 48 + 48 * K_M) / δ := by positivity
    linarith
  have hlogw_le_w : Real.log w ≤ w := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have h1w_le_log : 1 / w ≤ 1 / Real.log w := one_div_le_one_div_of_le hlw_pos hlogw_le_w
  -- Express `siftProd z / siftProd w` as the `[w, z)` product
  have hω_lt : ∀ p : ℕ, chenPrimeDensity N p < 1 := fun p => by
    unfold chenPrimeDensity; split_ifs with h
    · have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
        have := h.1.two_le; have := h.2.1; exact_mod_cast (show 3 ≤ p by omega)
      have : (1 : ℝ) / ((p : ℝ) - 1) ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith
    · norm_num
  rw [siftProd_div_eq_prod_ico hω_lt hwz]
  set S := (Finset.range (⌊z⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ w ≤ (p : ℝ) ∧ (p : ℝ) < z)
  set P_ndiv := S.filter (fun p => ¬ p ∣ N)
  set P_div := S.filter (fun p => p ∣ N)
  -- Factor `∏_{p ∈ S} (1 - chenPrimeDensity N p) = (∏_{p ∈ S} (1 - p⁻¹)) * R_ndiv * R_div`
  set P_mert : ℝ := ∏ p ∈ S, (1 - (p : ℝ)⁻¹)
  set R_ndiv : ℝ := ∏ p ∈ P_ndiv, (1 - 1 / ((p : ℝ) - 1) ^ 2)
  set R_div : ℝ := ∏ p ∈ P_div, (1 - (p : ℝ)⁻¹)⁻¹
  have hfactor : ∏ p ∈ S, (1 - chenPrimeDensity N p) = P_mert * R_ndiv * R_div := by
    have hdisj : Disjoint P_ndiv P_div := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      exact (Finset.mem_filter.mp hp1).2 (Finset.mem_filter.mp hp2).2
    have hunion : S = P_ndiv ∪ P_div := by
      ext p; simp only [P_ndiv, P_div, Finset.mem_union, Finset.mem_filter]; tauto
    have hLHS : ∏ p ∈ S, (1 - chenPrimeDensity N p) =
        (∏ p ∈ P_ndiv, (1 - 1 / ((p : ℝ) - 1))) * (∏ p ∈ P_div, (1 : ℝ)) := by
      rw [hunion, Finset.prod_union hdisj]
      congr 1
      · refine Finset.prod_congr rfl fun p hp => ?_
        have hpS := Finset.mem_filter.mp hp
        have hp_info := (Finset.mem_filter.mp hpS.1).2
        have hp_ne2 : p ≠ 2 := by
          have : (100 : ℝ) ≤ (p : ℝ) := le_trans hw100 hp_info.2.1
          have : 100 ≤ p := by exact_mod_cast this
          omega
        unfold chenPrimeDensity; rw [if_pos ⟨hp_info.1, hp_ne2, hpS.2⟩]
      · refine Finset.prod_congr rfl fun p hp => ?_
        have hpS := Finset.mem_filter.mp hp
        unfold chenPrimeDensity; rw [if_neg (fun h => h.2.2 hpS.2)]; ring
    have hPmert_split : P_mert = (∏ p ∈ P_ndiv, (1 - (p : ℝ)⁻¹)) * (∏ p ∈ P_div, (1 - (p : ℝ)⁻¹)) := by
      dsimp only [P_mert]; rw [hunion, Finset.prod_union hdisj]
    have hndiv_eq : (∏ p ∈ P_ndiv, (1 - (p : ℝ)⁻¹)) * R_ndiv =
        ∏ p ∈ P_ndiv, (1 - 1 / ((p : ℝ) - 1)) := by
      dsimp only [R_ndiv]; rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      have hp_info := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
      have hp100 : (100 : ℝ) ≤ (p : ℝ) := le_trans hw100 hp_info.2.1
      have hne0 : (p : ℝ) ≠ 0 := by linarith
      have hne1 : (p : ℝ) - 1 ≠ 0 := by linarith
      field_simp [hne0, hne1]; ring
    have hdiv_eq : (∏ p ∈ P_div, (1 - (p : ℝ)⁻¹)) * R_div = ∏ p ∈ P_div, (1 : ℝ) := by
      dsimp only [R_div]; rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      have hp_info := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
      have hp100 : (100 : ℝ) ≤ (p : ℝ) := le_trans hw100 hp_info.2.1
      have hne : 1 - (p : ℝ)⁻¹ ≠ 0 := by
        have : (p : ℝ)⁻¹ ≤ (100 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp100
        linarith
      exact mul_inv_cancel₀ hne
    rw [hLHS, hPmert_split]
    calc (∏ p ∈ P_ndiv, (1 - 1 / ((p : ℝ) - 1))) * (∏ p ∈ P_div, (1 : ℝ))
        = ((∏ p ∈ P_ndiv, (1 - (p : ℝ)⁻¹)) * R_ndiv) *
            ((∏ p ∈ P_div, (1 - (p : ℝ)⁻¹)) * R_div) := by rw [hndiv_eq, hdiv_eq]
      _ = (∏ p ∈ P_ndiv, (1 - (p : ℝ)⁻¹)) * (∏ p ∈ P_div, (1 - (p : ℝ)⁻¹)) * R_ndiv * R_div := by ring
  -- Bound `R_ndiv`: `1 - 2 / w ≤ R_ndiv ≤ 1`
  have hR_ndiv_hi : R_ndiv ≤ 1 := by
    refine Finset.prod_le_one (fun p hp => ?_) (fun p _ => ?_)
    · have hp100 : (100 : ℝ) ≤ (p : ℝ) := le_trans hw100 (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.2.1
      have : (1 : ℝ) / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
        rw [div_le_one (by nlinarith)]; nlinarith
      linarith
    · have : (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
      linarith
  have hR_ndiv_lo : 1 - 2 / w ≤ R_ndiv := by
    have hweier : 1 - ∑ p ∈ P_ndiv, 1 / ((p : ℝ) - 1) ^ 2 ≤ R_ndiv := by
      refine one_sub_sum_le_prod_one_sub P_ndiv (fun p => 1 / ((p : ℝ) - 1) ^ 2) fun p hp => ?_
      have hp100 : (100 : ℝ) ≤ (p : ℝ) := le_trans hw100 (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.2.1
      refine ⟨by positivity, ?_⟩
      rw [div_le_one (by nlinarith)]; nlinarith
    have hfl_ge : 100 ≤ ⌊w⌋₊ := Nat.le_floor hw100
    have hsum_le : ∑ p ∈ P_ndiv, 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / ((⌊w⌋₊ : ℝ) - 2) := by
      have hsub : P_ndiv ⊆ Finset.Icc ⌊w⌋₊ ⌊z⌋₊ := by
        intro p hp
        have hpS := (Finset.mem_filter.mp hp).1
        simp only [S, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hpS ⊢
        exact ⟨Nat.floor_le_of_le hpS.2.2.1, Nat.lt_succ_iff.mp hpS.1⟩
      have h1 : ∑ p ∈ P_ndiv, 1 / ((p : ℝ) - 1) ^ 2 ≤
          ∑ p ∈ P_ndiv, 1 / (((p : ℝ) - 2 + 1) * ((p : ℝ) - 2)) := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hp100 : (100 : ℝ) ≤ (p : ℝ) := le_trans hw100 (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.2.1
        exact one_div_le_one_div_of_le (by nlinarith) (by nlinarith)
      have h2 : ∑ p ∈ P_ndiv, (1 : ℝ) / (((p : ℝ) - 2 + 1) * ((p : ℝ) - 2)) ≤
          ∑ k ∈ Finset.Icc ⌊w⌋₊ ⌊z⌋₊, (1 : ℝ) / (((k : ℝ) - 2 + 1) * ((k : ℝ) - 2)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun k hk _ => by
          have hk100 : (100 : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_trans hfl_ge (Finset.mem_Icc.mp hk).1
          have : 0 < ((k : ℝ) - 2 + 1) * ((k : ℝ) - 2) := by nlinarith
          positivity
      have htel := sum_Icc_telescope_le ⌊w⌋₊ ⌊z⌋₊ 2 (by
        have : (100 : ℝ) ≤ (⌊w⌋₊ : ℝ) := by exact_mod_cast hfl_ge
        linarith)
      exact h1.trans (h2.trans htel)
    have hfl_sub : w / 2 ≤ (⌊w⌋₊ : ℝ) - 2 := by
      have := Nat.sub_one_lt_floor w
      linarith
    have hdiv_le : 1 / ((⌊w⌋₊ : ℝ) - 2) ≤ 2 / w := by
      have := one_div_le_one_div_of_le (show 0 < w / 2 by linarith) hfl_sub
      have hrew : (1 : ℝ) / (w / 2) = 2 / w := by ring
      linarith
    linarith
  -- Bound `R_div`: `1 ≤ R_div ≤ 1 + 48 / w` (since `P_div.card ≤ 8`)
  have hR_div_lo : 1 ≤ R_div := by
    refine one_le_prod_of_ge_one P_div _ fun p hp => ?_
    have hp100 : (100 : ℝ) ≤ (p : ℝ) := le_trans hw100 (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.2.1
    have hpos : 0 < 1 - (p : ℝ)⁻¹ := by
      have : (p : ℝ)⁻¹ ≤ (100 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp100
      linarith
    exact one_le_inv₀ hpos |>.mpr (by linarith [inv_nonneg.mpr (show 0 ≤ (p : ℝ) by positivity)])
  have hPdiv_card : P_div.card ≤ 8 := by
    have hdvd : (∏ p ∈ P_div, p) ∣ N :=
      prod_primes_dvd_of_forall P_div fun p hp =>
        ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1, (Finset.mem_filter.mp hp).2⟩
    have hN_pos_nat : 0 < N := by
      have : 1 ≤ N₀ := by omega
      omega
    have hprod_le_N : (∏ p ∈ P_div, (p : ℝ)) ≤ (N : ℝ) := by
      have hnat : ∏ p ∈ P_div, p ≤ N := Nat.le_of_dvd hN_pos_nat hdvd
      rw [← Nat.cast_prod]
      exact_mod_cast hnat
    have hprod_ge : ((N : ℝ) ^ ((1 : ℝ) / 8)) ^ P_div.card ≤ ∏ p ∈ P_div, (p : ℝ) := by
      rw [← Finset.prod_const]
      refine Finset.prod_le_prod (fun _ _ => by positivity) fun p hp => ?_
      exact le_trans hNw (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.2.1
    have hN_eq : ((N : ℝ) ^ ((1 : ℝ) / 8)) ^ 8 = (N : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN_pos.le]; norm_num
    have hpow_le : ((N : ℝ) ^ ((1 : ℝ) / 8)) ^ P_div.card ≤ ((N : ℝ) ^ ((1 : ℝ) / 8)) ^ 8 := by
      rw [hN_eq]; exact hprod_ge.trans hprod_le_N
    have hbase_gt1 : 1 < (N : ℝ) ^ ((1 : ℝ) / 8) :=
      Real.one_lt_rpow hN_gt1 (by norm_num)
    exact (pow_le_pow_iff_right₀ hbase_gt1).mp hpow_le
  have hR_div_hi : R_div ≤ 1 + 48 / w := by
    have h1w_pos : 0 < 1 - w⁻¹ := by
      have : w⁻¹ ≤ (100 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hw100
      linarith
    have h1w_ge1 : 1 ≤ (1 - w⁻¹)⁻¹ :=
      one_le_inv₀ h1w_pos |>.mpr (by linarith [inv_nonneg.mpr (show 0 ≤ w by linarith)])
    have h1 : R_div ≤ ((1 - w⁻¹)⁻¹) ^ P_div.card := by
      rw [← Finset.prod_const]
      refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
      · have hp100 : (100 : ℝ) ≤ (p : ℝ) := le_trans hw100 (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.2.1
        have : (p : ℝ)⁻¹ ≤ (100 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp100
        exact inv_nonneg.mpr (by linarith)
      · have hwp : w ≤ (p : ℝ) := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.2.1
        exact inv_anti₀ h1w_pos (by linarith [inv_anti₀ (by linarith : (0 : ℝ) < w) hwp])
    have h2 : ((1 - w⁻¹)⁻¹) ^ P_div.card ≤ ((1 - w⁻¹)⁻¹) ^ 8 :=
      pow_le_pow_right₀ h1w_ge1 hPdiv_card
    have h3 : (1 - w⁻¹)⁻¹ ≤ 1 + 2 / w := by
      rw [inv_le_iff_one_le_mul₀ h1w_pos]
      have hw_inv : w⁻¹ ≤ 1 / 100 := by
        rw [← one_div]; exact one_div_le_one_div_of_le (by norm_num) hw100
      have hrew : (1 - w⁻¹) * (1 + 2 / w) = 1 + w⁻¹ * (1 - 2 * w⁻¹) := by
        rw [div_eq_mul_inv]; ring
      rw [mul_comm, hrew]; nlinarith [inv_nonneg.mpr (show 0 ≤ w by linarith)]
    have h4 : ((1 - w⁻¹)⁻¹) ^ 8 ≤ Real.exp (16 / w) := by
      have h3e : (1 - w⁻¹)⁻¹ ≤ Real.exp (2 / w) := h3.trans (by linarith [Real.add_one_le_exp (2 / w)])
      calc ((1 - w⁻¹)⁻¹) ^ 8 ≤ (Real.exp (2 / w)) ^ 8 :=
            pow_le_pow_left₀ (by linarith) h3e 8
        _ = Real.exp ((8 : ℕ) * (2 / w)) := (Real.exp_nat_mul (2 / w) 8).symm
        _ = Real.exp (16 / w) := by push_cast; congr 1; ring
    have h5 : Real.exp (16 / w) ≤ 1 + 48 / w := by
      have h16_le1 : 16 / w ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      have := exp_le_one_add_three_mul (by positivity) h16_le1
      have h48 : 3 * (16 / w) = 48 / w := by ring
      linarith
    exact h1.trans (h2.trans (h4.trans h5))
  -- Combine `P_mert`, `R_ndiv`, `R_div`
  have hPmert_lo := (hmert w z hwx₀ hwz).1
  have hPmert_hi := (hmert w z hwx₀ hwz).2.1
  have hPmert_nn : 0 ≤ P_mert := Finset.prod_nonneg fun p hp => by
    have hp100 : (100 : ℝ) ≤ (p : ℝ) := le_trans hw100 (Finset.mem_filter.mp hp).2.2.1
    have : (p : ℝ)⁻¹ ≤ (100 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp100
    linarith
  have hRndiv_nn : 0 ≤ R_ndiv := by
    have : 2 / w ≤ 2 / 100 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hw100
    linarith
  have hbudget : (K_M + 48 + 48 * K_M) / Real.log w ≤ δ := by
    rw [div_le_iff₀ hlw_pos]
    have h1 : (K_M + 48 + 48 * K_M) / δ ≤ Real.log w := by linarith
    have h2 := (div_le_iff₀ hδ_pos).mp h1
    linarith
  have hR_div_log : R_div ≤ 1 + 48 / Real.log w := by
    have : 48 / w ≤ 48 / Real.log w :=
      div_le_div_of_nonneg_left (by norm_num) hlw_pos hlogw_le_w
    linarith
  have hR_ndiv_log : 1 - 48 / Real.log w ≤ R_ndiv := by
    have : 2 / w ≤ 48 / Real.log w := by
      have h1 : 2 / w ≤ 48 / w := div_le_div_of_nonneg_right (by norm_num) (by linarith)
      have h2 : 48 / w ≤ 48 / Real.log w :=
        div_le_div_of_nonneg_left (by norm_num) hlw_pos hlogw_le_w
      exact h1.trans h2
    linarith
  have hrat_pos : 0 < Real.log w / Real.log z := div_pos hlw_pos hlz_pos
  have hupper : P_mert * R_ndiv * R_div ≤ (Real.log w / Real.log z) * (1 + ε) := by
    have h1 : P_mert * R_ndiv * R_div ≤ P_mert * 1 * (1 + 48 / Real.log w) := by
      have h12 : P_mert * R_ndiv ≤ P_mert * 1 := mul_le_mul_of_nonneg_left hR_ndiv_hi hPmert_nn
      exact mul_le_mul h12 hR_div_log (by linarith) (by linarith)
    have h2 : P_mert * 1 * (1 + 48 / Real.log w) ≤
        ((Real.log w / Real.log z) * (1 + K_M / Real.log w)) * (1 + 48 / Real.log w) := by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_right hPmert_hi (by positivity)
    have h3 : (1 + K_M / Real.log w) * (1 + 48 / Real.log w) ≤ 1 + ε := by
      have h1_le : (1 : ℝ) / Real.log w ≤ 1 := by rw [div_le_one hlw_pos]; exact hlw_ge1
      have hprod : (1 + K_M / Real.log w) * (1 + 48 / Real.log w) =
          1 + (K_M + 48) / Real.log w + (48 * K_M / Real.log w) * (1 / Real.log w) := by ring
      rw [hprod]
      have hcross : (48 * K_M / Real.log w) * (1 / Real.log w) ≤ (48 * K_M / Real.log w) * 1 :=
        mul_le_mul_of_nonneg_left h1_le (by positivity)
      have hsum : (K_M + 48) / Real.log w + 48 * K_M / Real.log w =
          (K_M + 48 + 48 * K_M) / Real.log w := by ring
      linarith
    have h4 := mul_le_mul_of_nonneg_left h3 hrat_pos.le
    linarith
  have hlower : (Real.log w / Real.log z) * (1 - ε) ≤ P_mert * R_ndiv * R_div := by
    have hKM_le1 : K_M / Real.log w ≤ 1 := by
      have : K_M / Real.log w ≤ (K_M + 48 + 48 * K_M) / Real.log w :=
        div_le_div_of_nonneg_right (by linarith) hlw_pos.le
      linarith
    have h48_le1 : 48 / Real.log w ≤ 1 := by
      have : 48 / Real.log w ≤ (K_M + 48 + 48 * K_M) / Real.log w :=
        div_le_div_of_nonneg_right (by linarith) hlw_pos.le
      linarith
    have h1 : ((Real.log w / Real.log z) * (1 - K_M / Real.log w)) * (1 - 48 / Real.log w) * 1 ≤
        P_mert * R_ndiv * R_div := by
      have h12 : ((Real.log w / Real.log z) * (1 - K_M / Real.log w)) * (1 - 48 / Real.log w) ≤
          P_mert * R_ndiv :=
        mul_le_mul hPmert_lo hR_ndiv_log (by linarith) hPmert_nn
      exact mul_le_mul h12 hR_div_lo (by norm_num) (mul_nonneg hPmert_nn hRndiv_nn)
    have h2 : 1 - ε ≤ (1 - K_M / Real.log w) * (1 - 48 / Real.log w) := by
      have hprod : (1 - K_M / Real.log w) * (1 - 48 / Real.log w) =
          1 - (K_M + 48) / Real.log w + (K_M / Real.log w) * (48 / Real.log w) := by ring
      rw [hprod]
      have hnn : 0 ≤ (K_M / Real.log w) * (48 / Real.log w) := by positivity
      have hle : (K_M + 48) / Real.log w ≤ (K_M + 48 + 48 * K_M) / Real.log w :=
        div_le_div_of_nonneg_right (by linarith) hlw_pos.le
      linarith
    have h3 := mul_le_mul_of_nonneg_left h2 hrat_pos.le
    linarith
  rw [hfactor, abs_le]
  constructor <;> linarith

end RHDirect.Chen
