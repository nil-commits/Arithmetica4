import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Logic.Equiv.Finset
import Mathlib.Tactic

/-!
# Arithmetica4 Tier A Extension: Probabilistic Method & Extremal Combinatorics Engine

Reusable, general, non-vacuous Tier A theorems in `Arith4Ext.ProbExtremal`:
1. Finite Probability Spaces, Finite Product Spaces, and General Asymmetric & Symmetric
   Lovász Local Lemma (LLL), including the product-space variable-dependency bridge.
2. Chernoff–Hoeffding Exponential Concentration Bounds (Hoeffding's Lemma, general
   bounded Hoeffding upper/lower/two-sided tails, and multiplicative Chernoff
   KL and quadratic upper/lower bounds).
3. Kővári–Sós–Turán Theorem (`ex(m, n; K_{s,t})` and `ex(n; K_{s,t})`) via double
   counting and convexity/Jensen.
4. Dependent Random Choice Lemma (bipartite and `SimpleGraph`, general `r`-tuples and pairs).
5. Probabilistic Crossing Lemma (`e ≥ 4v ⇒ cr ≥ e³ / (64 v²)`), Caro–Wei, Turán's Theorem,
   and Katona–Nemetz–Simonovits / Erdős–Simonovits Hypergraph Averaging & Supersaturation Core.
-/

open scoped BigOperators
open Finset

namespace Arith4Ext.ProbExtremal

/-! ## Section 1: Finite Probability Spaces, Product Spaces, and Lovász Local Lemma -/

/-- A probability distribution on a finite sample space `Ω`. -/
structure FinProbSpace (Ω : Type*) [Fintype Ω] where
  pmf : Ω → ℝ
  pmf_nonneg : ∀ ω, 0 ≤ pmf ω
  pmf_sum_one : ∑ ω : Ω, pmf ω = 1

namespace FinProbSpace

variable {Ω : Type*} [Fintype Ω]

/-- Probability of an event `E : Finset Ω`. -/
def prob (μ : FinProbSpace Ω) (E : Finset Ω) : ℝ :=
  ∑ ω ∈ E, μ.pmf ω

/-- Expectation of a real-valued random variable `X : Ω → ℝ`. -/
def expect (μ : FinProbSpace Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω : Ω, μ.pmf ω * X ω

lemma prob_nonneg (μ : FinProbSpace Ω) (E : Finset Ω) : 0 ≤ μ.prob E :=
  Finset.sum_nonneg fun ω _ => μ.pmf_nonneg ω

lemma prob_empty (μ : FinProbSpace Ω) : μ.prob ∅ = 0 := by
  simp [prob]

lemma prob_univ (μ : FinProbSpace Ω) : μ.prob Finset.univ = 1 :=
  μ.pmf_sum_one

lemma prob_mono (μ : FinProbSpace Ω) {E F : Finset Ω} (h : E ⊆ F) :
    μ.prob E ≤ μ.prob F :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun ω _ _ => μ.pmf_nonneg ω

lemma prob_le_one (μ : FinProbSpace Ω) (E : Finset Ω) : μ.prob E ≤ 1 := by
  calc μ.prob E ≤ μ.prob Finset.univ := μ.prob_mono (Finset.subset_univ E)
    _ = 1 := μ.prob_univ

lemma prob_union_disjoint [DecidableEq Ω] (μ : FinProbSpace Ω) {E F : Finset Ω}
    (h : Disjoint E F) : μ.prob (E ∪ F) = μ.prob E + μ.prob F :=
  Finset.sum_union h

lemma prob_union_le [DecidableEq Ω] (μ : FinProbSpace Ω) (E F : Finset Ω) :
    μ.prob (E ∪ F) ≤ μ.prob E + μ.prob F := by
  have h1 : E ∪ F = E ∪ (F \ E) := (Finset.union_sdiff_self_eq_union).symm
  rw [h1, μ.prob_union_disjoint Finset.disjoint_sdiff]
  linarith [μ.prob_mono (Finset.sdiff_subset (s := F) (t := E))]

lemma prob_sdiff [DecidableEq Ω] (μ : FinProbSpace Ω) {E F : Finset Ω} (h : F ⊆ E) :
    μ.prob (E \ F) = μ.prob E - μ.prob F := by
  have h1 : μ.prob (E \ F) + μ.prob F = μ.prob E := by
    rw [← μ.prob_union_disjoint Finset.sdiff_disjoint, Finset.sdiff_union_of_subset h]
  linarith

lemma nonempty_of_prob_pos (μ : FinProbSpace Ω) {E : Finset Ω} (h : 0 < μ.prob E) :
    E.Nonempty := by
  by_contra hE
  rw [Finset.not_nonempty_iff_eq_empty] at hE
  rw [hE, prob_empty] at h
  exact lt_irrefl 0 h

lemma expect_const (μ : FinProbSpace Ω) (c : ℝ) : μ.expect (fun _ => c) = c := by
  simp only [expect, ← Finset.sum_mul, μ.pmf_sum_one, one_mul]

lemma expect_add (μ : FinProbSpace Ω) (X Y : Ω → ℝ) :
    μ.expect (fun ω => X ω + Y ω) = μ.expect X + μ.expect Y := by
  simp only [expect, mul_add, Finset.sum_add_distrib]

lemma expect_sub (μ : FinProbSpace Ω) (X Y : Ω → ℝ) :
    μ.expect (fun ω => X ω - Y ω) = μ.expect X - μ.expect Y := by
  simp only [expect, mul_sub, Finset.sum_sub_distrib]

lemma expect_neg (μ : FinProbSpace Ω) (X : Ω → ℝ) :
    μ.expect (fun ω => -X ω) = -μ.expect X := by
  simp only [expect, mul_neg, Finset.sum_neg_distrib]

lemma expect_const_mul (μ : FinProbSpace Ω) (c : ℝ) (X : Ω → ℝ) :
    μ.expect (fun ω => c * X ω) = c * μ.expect X := by
  simp only [expect, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  ring

lemma expect_sum {ι : Type*} (μ : FinProbSpace Ω) (s : Finset ι) (X : ι → Ω → ℝ) :
    μ.expect (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, μ.expect (X i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

lemma expect_mono (μ : FinProbSpace Ω) {X Y : Ω → ℝ} (h : ∀ ω, X ω ≤ Y ω) :
    μ.expect X ≤ μ.expect Y :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (μ.pmf_nonneg ω)

lemma expect_nonneg (μ : FinProbSpace Ω) {X : Ω → ℝ} (h : ∀ ω, 0 ≤ X ω) :
    0 ≤ μ.expect X :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (μ.pmf_nonneg ω) (h ω)

lemma expect_indicator [DecidableEq Ω] (μ : FinProbSpace Ω) (E : Finset Ω) :
    μ.expect (fun ω => if ω ∈ E then (1 : ℝ) else 0) = μ.prob E := by
  simp [expect, prob, Finset.sum_ite_mem, Finset.univ_inter]

lemma exists_ge_expect (μ : FinProbSpace Ω) (X : Ω → ℝ) :
    ∃ ω : Ω, μ.expect X ≤ X ω := by
  by_contra h
  push Not at h
  have hex : ∃ ω : Ω, 0 < μ.pmf ω := by
    by_contra hall
    push Not at hall
    have h0 : ∑ ω : Ω, μ.pmf ω = 0 :=
      Finset.sum_eq_zero fun ω _ => le_antisymm (hall ω) (μ.pmf_nonneg ω)
    linarith [μ.pmf_sum_one]
  rcases hex with ⟨ω₀, hω₀⟩
  have h1 : μ.expect X < μ.expect (fun _ => μ.expect X) :=
    Finset.sum_lt_sum
      (fun ω _ => mul_le_mul_of_nonneg_left (le_of_lt (h ω)) (μ.pmf_nonneg ω))
      ⟨ω₀, Finset.mem_univ ω₀, mul_lt_mul_of_pos_left (h ω₀) hω₀⟩
  rw [μ.expect_const] at h1
  exact lt_irrefl _ h1

lemma exists_le_expect (μ : FinProbSpace Ω) (X : Ω → ℝ) :
    ∃ ω : Ω, X ω ≤ μ.expect X := by
  obtain ⟨ω, hω⟩ := μ.exists_ge_expect (fun x => -X x)
  rw [μ.expect_neg] at hω
  exact ⟨ω, by linarith⟩

/-- Uniform probability distribution on a nonempty finite type. -/
noncomputable def uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FinProbSpace Ω where
  pmf := fun _ => (1 : ℝ) / Fintype.card Ω
  pmf_nonneg := fun _ => by positivity
  pmf_sum_one := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    field_simp [hcard]

/-- Bernoulli distribution on `Bool` with success probability `p ∈ [0, 1]`. -/
def bernoulli (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FinProbSpace Bool where
  pmf := fun b => if b then p else 1 - p
  pmf_nonneg := fun b => by cases b <;> simp <;> linarith
  pmf_sum_one := by simp

/-- Independent finite product probability space on `∀ i : ι, α i`. -/
noncomputable def prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (μ : ∀ i, FinProbSpace (α i)) : FinProbSpace (∀ i, α i) where
  pmf := fun ω => ∏ i : ι, (μ i).pmf (ω i)
  pmf_nonneg := fun ω => Finset.prod_nonneg fun i _ => (μ i).pmf_nonneg (ω i)
  pmf_sum_one := by
    rw [← Fintype.prod_sum (fun i x => (μ i).pmf x)]
    exact Finset.prod_eq_one fun i _ => (μ i).pmf_sum_one

/-- Expectation of a product of coordinate-wise functions factors over a product space. -/
theorem expect_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (μ : ∀ i, FinProbSpace (α i)) (f : ∀ i, α i → ℝ) :
    (FinProbSpace.prod μ).expect (fun ω => ∏ i : ι, f i (ω i)) =
      ∏ i : ι, (μ i).expect (f i) := by
  simp only [expect, prod]
  trans ∑ ω : ∀ i, α i, ∏ i : ι, (μ i).pmf (ω i) * f i (ω i)
  · refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Finset.prod_mul_distrib]
  · rw [← Fintype.prod_sum (fun i x => (μ i).pmf x * f i x)]

/-- Expectation of a single coordinate function on a product space equals its marginal expectation. -/
theorem expect_prod_coord {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (μ : ∀ i, FinProbSpace (α i)) (i₀ : ι) (g : α i₀ → ℝ) :
    (FinProbSpace.prod μ).expect (fun ω => g (ω i₀)) = (μ i₀).expect g := by
  classical
  let f : ∀ i, α i → ℝ := fun i x => if h : i = i₀ then g (h ▸ x) else 1
  have hfg : ∀ ω : ∀ i, α i, g (ω i₀) = ∏ i : ι, f i (ω i) := by
    intro ω
    rw [Finset.prod_eq_single i₀]
    · simp [f]
    · intro i _ hi
      simp [f, hi]
    · intro hmem
      exact absurd (Finset.mem_univ i₀) hmem
  have h1 : (FinProbSpace.prod μ).expect (fun ω => g (ω i₀)) =
      (FinProbSpace.prod μ).expect (fun ω => ∏ i : ι, f i (ω i)) := by
    congr 1; ext ω; exact hfg ω
  rw [h1, expect_prod, Finset.prod_eq_single i₀]
  · simp [f]
  · intro i _ hi
    have : f i = fun _ => (1 : ℝ) := by ext x; simp [f, hi]
    rw [this, (μ i).expect_const]
  · intro hmem
    exact absurd (Finset.mem_univ i₀) hmem

/-- Expectation of a sum of coordinate functions on a product space. -/
theorem expect_prod_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (μ : ∀ i, FinProbSpace (α i)) (X : ∀ i, α i → ℝ) :
    (FinProbSpace.prod μ).expect (fun ω => ∑ i : ι, X i (ω i)) =
      ∑ i : ι, (μ i).expect (X i) := by
  rw [expect_sum]
  exact Finset.sum_congr rfl fun i _ => expect_prod_coord μ i (X i)

/-- Markov's inequality on a finite probability space. -/
theorem markov {X : Ω → ℝ} (μ : FinProbSpace Ω) (hX : ∀ ω, 0 ≤ X ω)
    {t : ℝ} [DecidablePred (fun ω => t ≤ X ω)] :
    t * μ.prob (Finset.univ.filter (fun ω => t ≤ X ω)) ≤ μ.expect X := by
  simp only [prob, expect, Finset.mul_sum]
  calc ∑ ω ∈ Finset.univ.filter (fun ω => t ≤ X ω), t * μ.pmf ω
      ≤ ∑ ω ∈ Finset.univ.filter (fun ω => t ≤ X ω), μ.pmf ω * X ω := by
        refine Finset.sum_le_sum fun ω hω => ?_
        have hle : t ≤ X ω := (Finset.mem_filter.mp hω).2
        rw [mul_comm t]
        exact mul_le_mul_of_nonneg_left hle (μ.pmf_nonneg ω)
    _ ≤ ∑ ω : Ω, μ.pmf ω * X ω := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
        intro ω _ _
        exact mul_nonneg (μ.pmf_nonneg ω) (hX ω)

/-- Generic Chernoff MGF upper tail inequality. -/
theorem chernoff_mgf_upper (μ : FinProbSpace Ω) (X : Ω → ℝ) (a : ℝ)
    {t : ℝ} (ht : 0 < t) [DecidablePred (fun ω => a ≤ X ω)] :
    μ.prob (Finset.univ.filter (fun ω => a ≤ X ω)) ≤
      Real.exp (-t * a) * μ.expect (fun ω => Real.exp (t * X ω)) := by
  classical
  have hsub : Finset.univ.filter (fun ω => a ≤ X ω) ⊆
      Finset.univ.filter (fun ω => Real.exp (t * a) ≤ Real.exp (t * X ω)) := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω (le_of_lt ht))
  have hmarkov := μ.markov (X := fun ω => Real.exp (t * X ω))
    (fun ω => le_of_lt (Real.exp_pos _)) (t := Real.exp (t * a))
  have hprob := μ.prob_mono hsub
  have h1 : Real.exp (t * a) * μ.prob (Finset.univ.filter (fun ω => a ≤ X ω)) ≤
      μ.expect (fun ω => Real.exp (t * X ω)) :=
    le_trans (mul_le_mul_of_nonneg_left hprob (le_of_lt (Real.exp_pos _))) hmarkov
  have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt (Real.exp_pos (-t * a)))
  rw [← mul_assoc, ← Real.exp_add] at h2
  have hzero : -t * a + t * a = 0 := by ring
  rw [hzero, Real.exp_zero, one_mul] at h2
  exact h2

/-- Generic Chernoff MGF lower tail inequality (for `t < 0`). -/
theorem chernoff_mgf_lower (μ : FinProbSpace Ω) (X : Ω → ℝ) (a : ℝ)
    {t : ℝ} (ht : t < 0) [DecidablePred (fun ω => X ω ≤ a)] :
    μ.prob (Finset.univ.filter (fun ω => X ω ≤ a)) ≤
      Real.exp (-t * a) * μ.expect (fun ω => Real.exp (t * X ω)) := by
  classical
  have hsub : Finset.univ.filter (fun ω => X ω ≤ a) ⊆
      Finset.univ.filter (fun ω => -a ≤ -X ω) := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    linarith
  have hup := μ.chernoff_mgf_upper (fun ω => -X ω) (-a) (t := -t) (by linarith)
  have heq1 : -(-t) * (-a) = -t * a := by ring
  have heq2 : (fun ω => Real.exp (-t * -X ω)) = (fun ω => Real.exp (t * X ω)) := by
    ext ω; congr 1; ring
  rw [heq1, heq2] at hup
  exact le_trans (μ.prob_mono hsub) hup

/-- An event on a product space depends only on the coordinates in `V`. -/
def DependsOn {κ : Type*} {α : κ → Type*} (E : Finset (∀ k, α k)) (V : Finset κ) : Prop :=
  ∀ ω₁ ω₂, (∀ k ∈ V, ω₁ k = ω₂ k) → (ω₁ ∈ E ↔ ω₂ ∈ E)

/-- Two events depending on disjoint coordinate sets of a product space are independent. -/
theorem prob_prod_inter_of_disjoint_dependsOn
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {α : κ → Type*} [∀ k, Fintype (α k)] [∀ k, DecidableEq (α k)]
    (ν : ∀ k, FinProbSpace (α k))
    {E F : Finset (∀ k, α k)} {V W : Finset κ}
    (hE : DependsOn E V) (hF : DependsOn F W) (hVW : Disjoint V W) :
    (FinProbSpace.prod ν).prob (E ∩ F) =
      (FinProbSpace.prod ν).prob E * (FinProbSpace.prod ν).prob F := by
  classical
  have hne_k : ∀ k : κ, Nonempty (α k) := by
    intro k
    by_contra h
    rw [not_nonempty_iff] at h
    have h0 : ∑ x : α k, (ν k).pmf x = 0 := by simp
    linarith [(ν k).pmf_sum_one]
  let ω₀ : ∀ k, α k := fun k => Classical.choice (hne_k k)
  let eEquiv := Equiv.piEquivPiSubtypeProd (p := fun k : κ => k ∈ V) α
  let combine : (∀ k : {k // k ∈ V}, α k) → (∀ k : {k // k ∉ V}, α k) → (∀ k, α k) :=
    fun x y => eEquiv.symm (x, y)
  have hcomb_mem : ∀ x y (k : κ) (hk : k ∈ V), combine x y k = x ⟨k, hk⟩ := by
    intro x y k hk
    simp [combine, eEquiv, Equiv.piEquivPiSubtypeProd_symm_apply, hk]
  have hcomb_nmem : ∀ x y (k : κ) (hk : k ∉ V), combine x y k = y ⟨k, hk⟩ := by
    intro x y k hk
    simp [combine, eEquiv, Equiv.piEquivPiSubtypeProd_symm_apply, hk]
  let pV : (∀ k : {k // k ∈ V}, α k) → ℝ := fun x => ∏ k : {k // k ∈ V}, (ν k.1).pmf (x k)
  let pVc : (∀ k : {k // k ∉ V}, α k) → ℝ := fun y => ∏ k : {k // k ∉ V}, (ν k.1).pmf (y k)
  have hpmf_split : ∀ x y,
      (FinProbSpace.prod ν).pmf (combine x y) = pV x * pVc y := by
    intro x y
    simp only [prod, pV, pVc]
    rw [← Fintype.prod_subtype_mul_prod_subtype (p := fun k : κ => k ∈ V)]
    congr 1
    · refine Finset.prod_congr (by ext k; simp) fun k _ => ?_
      rw [hcomb_mem x y k.1 k.2]
    · refine Finset.prod_congr (by ext k; simp) fun k _ => ?_
      rw [hcomb_nmem x y k.1 k.2]
  have hpV_sum : ∑ x : ∀ k : {k // k ∈ V}, α k, pV x = 1 := by
    simp only [pV]
    rw [← Fintype.prod_sum (fun (k : {k // k ∈ V}) x => (ν k.1).pmf x)]
    exact Finset.prod_eq_one fun k _ => (ν k.1).pmf_sum_one
  have hpVc_sum : ∑ y : ∀ k : {k // k ∉ V}, α k, pVc y = 1 := by
    simp only [pVc]
    rw [← Fintype.prod_sum (fun (k : {k // k ∉ V}) y => (ν k.1).pmf y)]
    exact Finset.prod_eq_one fun k _ => (ν k.1).pmf_sum_one
  let indE : (∀ k : {k // k ∈ V}, α k) → ℝ :=
    fun x => if combine x (fun k => ω₀ k.1) ∈ E then 1 else 0
  let indF : (∀ k : {k // k ∉ V}, α k) → ℝ :=
    fun y => if combine (fun k => ω₀ k.1) y ∈ F then 1 else 0
  have hindE_eq : ∀ x y, (if combine x y ∈ E then (1 : ℝ) else 0) = indE x := by
    intro x y
    have hiff : combine x y ∈ E ↔ combine x (fun k => ω₀ k.1) ∈ E := by
      apply hE
      intro k hk
      rw [hcomb_mem x y k hk, hcomb_mem x (fun k => ω₀ k.1) k hk]
    simp [indE, hiff]
  have hindF_eq : ∀ x y, (if combine x y ∈ F then (1 : ℝ) else 0) = indF y := by
    intro x y
    have hiff : combine x y ∈ F ↔ combine (fun k => ω₀ k.1) y ∈ F := by
      apply hF
      intro k hkW
      have hkV : k ∉ V := Finset.disjoint_right.mp hVW hkW
      rw [hcomb_nmem x y k hkV, hcomb_nmem (fun k => ω₀ k.1) y k hkV]
    simp [indF, hiff]
  have hprobE : (FinProbSpace.prod ν).prob E = ∑ x, pV x * indE x := by
    rw [← expect_indicator, expect]
    rw [← Equiv.sum_comp eEquiv.symm]
    rw [Fintype.sum_prod_type]
    have h1 : ∀ x, ∑ y, (FinProbSpace.prod ν).pmf (combine x y) *
        (if combine x y ∈ E then (1 : ℝ) else 0) = pV x * indE x := by
      intro x
      calc ∑ y, (FinProbSpace.prod ν).pmf (combine x y) *
              (if combine x y ∈ E then (1 : ℝ) else 0)
          = ∑ y, (pV x * pVc y) * indE x := by
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [hpmf_split x y, hindE_eq x y]
        _ = (pV x * indE x) * ∑ y, pVc y := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun y _ => by ring
        _ = pV x * indE x := by rw [hpVc_sum, mul_one]
    exact Finset.sum_congr rfl fun x _ => h1 x
  have hprobF : (FinProbSpace.prod ν).prob F = ∑ y, pVc y * indF y := by
    rw [← expect_indicator, expect]
    rw [← Equiv.sum_comp eEquiv.symm]
    rw [Fintype.sum_prod_type_right]
    have h1 : ∀ y, ∑ x, (FinProbSpace.prod ν).pmf (combine x y) *
        (if combine x y ∈ F then (1 : ℝ) else 0) = pVc y * indF y := by
      intro y
      calc ∑ x, (FinProbSpace.prod ν).pmf (combine x y) *
              (if combine x y ∈ F then (1 : ℝ) else 0)
          = ∑ x, (pV x * pVc y) * indF y := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [hpmf_split x y, hindF_eq x y]
        _ = (pVc y * indF y) * ∑ x, pV x := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun x _ => by ring
        _ = pVc y * indF y := by rw [hpV_sum, mul_one]
    exact Finset.sum_congr rfl fun y _ => h1 y
  have hprobEF : (FinProbSpace.prod ν).prob (E ∩ F) =
      (∑ x, pV x * indE x) * (∑ y, pVc y * indF y) := by
    rw [← expect_indicator, expect]
    rw [← Equiv.sum_comp eEquiv.symm]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [hpmf_split x y]
    have hindEF : (if combine x y ∈ E ∩ F then (1 : ℝ) else 0) = indE x * indF y := by
      rw [← hindE_eq x y, ← hindF_eq x y]
      by_cases h1 : combine x y ∈ E <;> by_cases h2 : combine x y ∈ F <;>
        simp [Finset.mem_inter, h1, h2]
    rw [hindEF]; ring
  rw [hprobEF, hprobE, hprobF]

end FinProbSpace

/-! ### Lovász Local Lemma (Asymmetric, Symmetric, and Product-Space Variable Model) -/

/-- Event that none of the bad events `A j` (`j ∈ S`) occur. -/
def avoidEvents {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω]
    (A : ι → Finset Ω) (S : Finset ι) : Finset Ω :=
  Finset.univ.filter (fun ω => ∀ j ∈ S, ω ∉ A j)

lemma avoidEvents_empty {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] (A : ι → Finset Ω) :
    avoidEvents A ∅ = Finset.univ := by
  ext ω; simp [avoidEvents]

lemma avoidEvents_anti {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω]
    (A : ι → Finset Ω) {S T : Finset ι} (h : S ⊆ T) :
    avoidEvents A T ⊆ avoidEvents A S := by
  intro ω hω
  simp only [avoidEvents, Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
  exact fun j hj => hω j (h hj)

lemma avoidEvents_insert {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq ι]
    (A : ι → Finset Ω) (i : ι) (S : Finset ι) :
    avoidEvents A (insert i S) = avoidEvents A S \ (A i ∩ avoidEvents A S) := by
  ext ω
  simp only [avoidEvents, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro h
    exact ⟨fun j hj => h j (Or.inr hj), fun ⟨hi, _⟩ => h i (Or.inl rfl) hi⟩
  · rintro ⟨hS, hni⟩ j (rfl | hj)
    · exact fun hi => hni ⟨hi, hS⟩
    · exact hS j hj

lemma dependsOn_avoidEvents
    {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    {α : κ → Type*} [∀ k, Fintype (α k)] [∀ k, DecidableEq (α k)]
    (A : ι → Finset (∀ k, α k)) (vbl : ι → Finset κ)
    (hdep : ∀ i, FinProbSpace.DependsOn (A i) (vbl i))
    (S : Finset ι) :
    FinProbSpace.DependsOn (avoidEvents A S) (S.biUnion vbl) := by
  intro ω₁ ω₂ heq
  simp only [avoidEvents, Finset.mem_filter, Finset.mem_univ, true_and]
  refine forall₂_congr fun j hj => ?_
  have hiff := hdep j ω₁ ω₂ (fun k hk => heq k (Finset.mem_biUnion.mpr ⟨j, hj, hk⟩))
  exact not_congr hiff

/-- **General Finite Asymmetric Lovász Local Lemma (Quantitative Conditional Bound)**:
For any finite probability space `μ`, bad events `A : ι → Finset Ω`, dependency neighborhoods
`Γ : ι → Finset ι` (with `A i` independent of avoiding any `S` disjoint from `insert i (Γ i)`),
and weights `x : ι → ℝ` with `0 ≤ x i < 1` satisfying `P(A i) ≤ x i * ∏_{j ∈ Γ i} (1 - x j)`,
we have `P(A i ∩ avoid(S)) ≤ x i * P(avoid(S))` for every `S` and `i ∉ S`. -/
theorem lll_asymmetric_cond_bound
    {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]
    (μ : FinProbSpace Ω)
    (A : ι → Finset Ω)
    (Γ : ι → Finset ι)
    (x : ι → ℝ)
    (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : ∀ i, x i < 1)
    (hindep : ∀ i (S : Finset ι), i ∉ S → Disjoint S (Γ i) →
      μ.prob (A i ∩ avoidEvents A S) = μ.prob (A i) * μ.prob (avoidEvents A S))
    (hbound : ∀ i, μ.prob (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) :
    ∀ (S : Finset ι) (i : ι), i ∉ S →
      μ.prob (A i ∩ avoidEvents A S) ≤ x i * μ.prob (avoidEvents A S) := by
  intro S
  induction hcard : S.card using Nat.strong_induction_on generalizing S with
  | h k ih =>
    intro i hiS
    set S₁ := S ∩ Γ i
    set S₂ := S \ Γ i
    have hS₂_sub : S₂ ⊆ S := Finset.sdiff_subset
    have hiS₂ : i ∉ S₂ := fun h => hiS (hS₂_sub h)
    have hdisj₂ : Disjoint S₂ (Γ i) := Finset.sdiff_disjoint
    have h1 : μ.prob (A i ∩ avoidEvents A S) ≤ μ.prob (A i) * μ.prob (avoidEvents A S₂) := by
      calc μ.prob (A i ∩ avoidEvents A S)
          ≤ μ.prob (A i ∩ avoidEvents A S₂) :=
            μ.prob_mono (Finset.inter_subset_inter_left (avoidEvents_anti A hS₂_sub))
        _ = μ.prob (A i) * μ.prob (avoidEvents A S₂) := hindep i S₂ hiS₂ hdisj₂
    have hpeel : ∀ (R : Finset ι), R ⊆ S₁ →
        (∏ j ∈ R, (1 - x j)) * μ.prob (avoidEvents A S₂) ≤
          μ.prob (avoidEvents A (R ∪ S₂)) := by
      intro R
      induction R using Finset.induction_on with
      | empty =>
        intro _
        simp
      | @insert j R' hjR' ihR =>
        intro hsub
        have hjS₁ : j ∈ S₁ := hsub (Finset.mem_insert_self j R')
        have hR'_sub : R' ⊆ S₁ := fun z hz => hsub (Finset.mem_insert_of_mem hz)
        have hT_sub : R' ∪ S₂ ⊆ S := by
          intro z hz
          rcases Finset.mem_union.mp hz with hz1 | hz2
          · exact (Finset.mem_inter.mp (hR'_sub hz1)).1
          · exact hS₂_sub hz2
        have hj_not_S₂ : j ∉ S₂ := by
          intro hmem
          exact (Finset.mem_sdiff.mp hmem).2 (Finset.mem_inter.mp hjS₁).2
        have hj_not_T : j ∉ R' ∪ S₂ := by
          simp [hjR', hj_not_S₂]
        have hT_lt : (R' ∪ S₂).card < k := by
          rw [← hcard]
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨hT_sub, fun heq => hj_not_T ?_⟩
          rw [heq]
          exact (Finset.mem_inter.mp hjS₁).1
        have hih_j := ih (R' ∪ S₂).card hT_lt (R' ∪ S₂) rfl j hj_not_T
        have hstep : (1 - x j) * μ.prob (avoidEvents A (R' ∪ S₂)) ≤
            μ.prob (avoidEvents A (insert j (R' ∪ S₂))) := by
          rw [avoidEvents_insert, μ.prob_sdiff Finset.inter_subset_right]
          linarith
        rw [Finset.insert_union, Finset.prod_insert hjR', mul_assoc]
        calc (1 - x j) * ((∏ a ∈ R', (1 - x a)) * μ.prob (avoidEvents A S₂))
            ≤ (1 - x j) * μ.prob (avoidEvents A (R' ∪ S₂)) :=
              mul_le_mul_of_nonneg_left (ihR hR'_sub) (by linarith [hx1 j])
          _ ≤ μ.prob (avoidEvents A (insert j (R' ∪ S₂))) := hstep
    have hS_eq : S₁ ∪ S₂ = S := by
      ext z
      simp only [S₁, S₂, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      tauto
    have h2 : (∏ j ∈ S₁, (1 - x j)) * μ.prob (avoidEvents A S₂) ≤ μ.prob (avoidEvents A S) := by
      simpa [hS_eq] using hpeel S₁ (Subset.refl _)
    have hprod_le : ∏ j ∈ Γ i, (1 - x j) ≤ ∏ j ∈ S₁, (1 - x j) := by
      have hsub : S₁ ⊆ Γ i := Finset.inter_subset_right
      rw [← Finset.prod_sdiff hsub]
      have hle1 : ∏ j ∈ Γ i \ S₁, (1 - x j) ≤ 1 :=
        Finset.prod_le_one (fun j _ => by linarith [hx1 j]) (fun j _ => by linarith [hx0 j])
      have hnonneg : 0 ≤ ∏ j ∈ S₁, (1 - x j) :=
        Finset.prod_nonneg fun j _ => by linarith [hx1 j]
      nlinarith
    calc μ.prob (A i ∩ avoidEvents A S)
        ≤ μ.prob (A i) * μ.prob (avoidEvents A S₂) := h1
      _ ≤ (x i * ∏ j ∈ Γ i, (1 - x j)) * μ.prob (avoidEvents A S₂) :=
          mul_le_mul_of_nonneg_right (hbound i) (μ.prob_nonneg _)
      _ ≤ (x i * ∏ j ∈ S₁, (1 - x j)) * μ.prob (avoidEvents A S₂) := by
          refine mul_le_mul_of_nonneg_right ?_ (μ.prob_nonneg _)
          exact mul_le_mul_of_nonneg_left hprod_le (hx0 i)
      _ = x i * ((∏ j ∈ S₁, (1 - x j)) * μ.prob (avoidEvents A S₂)) := by ring
      _ ≤ x i * μ.prob (avoidEvents A S) := mul_le_mul_of_nonneg_left h2 (hx0 i)

/-- **General Finite Asymmetric Lovász Local Lemma (Probability Lower Bound)**:
Under the asymmetric LLL hypotheses, `∏_{i ∈ S} (1 - x i) ≤ P(avoid(S))` for every `S`,
and in particular `0 < ∏ i, (1 - x i) ≤ P(⋂ i, A_iᶜ)`. -/
theorem lll_asymmetric_prob_ge
    {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]
    (μ : FinProbSpace Ω)
    (A : ι → Finset Ω)
    (Γ : ι → Finset ι)
    (x : ι → ℝ)
    (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : ∀ i, x i < 1)
    (hindep : ∀ i (S : Finset ι), i ∉ S → Disjoint S (Γ i) →
      μ.prob (A i ∩ avoidEvents A S) = μ.prob (A i) * μ.prob (avoidEvents A S))
    (hbound : ∀ i, μ.prob (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j))
    (S : Finset ι) :
    ∏ i ∈ S, (1 - x i) ≤ μ.prob (avoidEvents A S) := by
  have hcond := lll_asymmetric_cond_bound μ A Γ x hx0 hx1 hindep hbound
  induction S using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, avoidEvents_empty, μ.prob_univ]
  | @insert i S' hiS' ih =>
    rw [Finset.prod_insert hiS', avoidEvents_insert, μ.prob_sdiff Finset.inter_subset_right]
    have hci := hcond S' i hiS'
    have h1 : (1 - x i) * μ.prob (avoidEvents A S') ≤
        μ.prob (avoidEvents A S') - μ.prob (A i ∩ avoidEvents A S') := by linarith
    exact le_trans (mul_le_mul_of_nonneg_left ih (by linarith [hx1 i])) h1

/-- **General Finite Asymmetric Lovász Local Lemma (Existence)**:
There exists an outcome `ω : Ω` avoiding every bad event `A i`. -/
theorem lll_asymmetric_exists
    {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]
    (μ : FinProbSpace Ω)
    (A : ι → Finset Ω)
    (Γ : ι → Finset ι)
    (x : ι → ℝ)
    (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : ∀ i, x i < 1)
    (hindep : ∀ i (S : Finset ι), i ∉ S → Disjoint S (Γ i) →
      μ.prob (A i ∩ avoidEvents A S) = μ.prob (A i) * μ.prob (avoidEvents A S))
    (hbound : ∀ i, μ.prob (A i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) :
    ∃ ω : Ω, ∀ i : ι, ω ∉ A i := by
  have hpos : 0 < ∏ i : ι, (1 - x i) :=
    Finset.prod_pos fun i _ => by linarith [hx1 i]
  have hprob := lll_asymmetric_prob_ge μ A Γ x hx0 hx1 hindep hbound Finset.univ
  obtain ⟨ω, hω⟩ := μ.nonempty_of_prob_pos (lt_of_lt_of_le hpos hprob)
  simp only [avoidEvents, Finset.mem_filter, Finset.mem_univ, true_and] at hω
  exact ⟨ω, fun i => hω i trivial⟩

/-- **Symmetric Lovász Local Lemma (`e * p * (d + 1) ≤ 1`)**:
If every bad event has probability `≤ p`, every dependency neighborhood has size `≤ d`,
and `Real.exp 1 * p * (d + 1) ≤ 1`, then there exists `ω : Ω` avoiding all bad events. -/
theorem lll_symmetric_exp
    {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]
    (μ : FinProbSpace Ω)
    (A : ι → Finset Ω)
    (Γ : ι → Finset ι)
    (p : ℝ) (d : ℕ)
    (hdeg : ∀ i, (Γ i).card ≤ d)
    (hp : ∀ i, μ.prob (A i) ≤ p)
    (hindep : ∀ i (S : Finset ι), i ∉ S → Disjoint S (Γ i) →
      μ.prob (A i ∩ avoidEvents A S) = μ.prob (A i) * μ.prob (avoidEvents A S))
    (hep : Real.exp 1 * p * (d + 1 : ℝ) ≤ 1) :
    ∃ ω : Ω, ∀ i : ι, ω ∉ A i := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hp_lt1 : p < 1 := by
      simp only [Nat.cast_zero, zero_add, mul_one] at hep
      have he : (1 : ℝ) < Real.exp 1 := by
        have := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
        linarith
      nlinarith [Real.exp_pos 1]
    refine lll_asymmetric_exists μ A Γ (fun _ => max p 0)
      (fun _ => le_max_right p 0)
      (fun _ => max_lt hp_lt1 (by norm_num))
      hindep ?_
    intro i
    have hΓ : Γ i = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp (hdeg i))
    rw [hΓ, Finset.prod_empty, mul_one]
    exact le_trans (hp i) (le_max_left p 0)
  · let x : ℝ := 1 / (d + 1 : ℝ)
    have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
    have hd1_pos : (0 : ℝ) < d + 1 := by linarith
    have hx0 : 0 ≤ x := by positivity
    have hx1 : x < 1 := by
      dsimp [x]
      rw [div_lt_one hd1_pos]
      linarith
    have h1mx : 1 - x = (d : ℝ) / (d + 1 : ℝ) := by
      dsimp [x]; field_simp [ne_of_gt hd1_pos]; ring
    have hexp_pow : ((d + 1 : ℝ) / d) ^ d ≤ Real.exp 1 := by
      have h1 : (d + 1 : ℝ) / d = 1 + 1 / (d : ℝ) := by
        field_simp [ne_of_gt hd_pos]
      rw [h1]
      calc (1 + 1 / (d : ℝ)) ^ d
          ≤ (Real.exp (1 / (d : ℝ))) ^ d := by
            gcongr
            linarith [Real.add_one_le_exp (1 / (d : ℝ))]
        _ = Real.exp ((d : ℝ) * (1 / (d : ℝ))) := by
            rw [← Real.exp_nat_mul]
        _ = Real.exp 1 := by
            congr 1; field_simp [ne_of_gt hd_pos]
    have hpow_ge : 1 / Real.exp 1 ≤ (1 - x) ^ d := by
      rw [h1mx]
      have hpos_frac : (0 : ℝ) < ((d + 1 : ℝ) / d) ^ d := by positivity
      have hinv : ((d : ℝ) / (d + 1 : ℝ)) ^ d = (((d + 1 : ℝ) / d) ^ d)⁻¹ := by
        rw [← inv_pow, inv_div]
      rw [hinv, one_div]
      exact inv_anti₀ hpos_frac hexp_pow
    refine lll_asymmetric_exists μ A Γ (fun _ => x) (fun _ => hx0) (fun _ => hx1) hindep ?_
    intro i
    rw [Finset.prod_const]
    have hpow_mono : (1 - x) ^ d ≤ (1 - x) ^ (Γ i).card :=
      pow_le_pow_of_le_one (by linarith) (by linarith) (hdeg i)
    have hp_le : p ≤ x * (1 / Real.exp 1) := by
      dsimp [x]
      have he_pos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
      have hden : 0 < Real.exp 1 * (d + 1 : ℝ) := mul_pos he_pos hd1_pos
      have hdiv : p ≤ 1 / (Real.exp 1 * (d + 1 : ℝ)) := (le_div_iff₀ hden).mpr (by linarith)
      calc p ≤ 1 / (Real.exp 1 * (d + 1 : ℝ)) := hdiv
        _ = 1 / (d + 1 : ℝ) * (1 / Real.exp 1) := by
            field_simp [ne_of_gt he_pos, ne_of_gt hd1_pos]
    calc μ.prob (A i) ≤ p := hp i
      _ ≤ x * (1 / Real.exp 1) := hp_le
      _ ≤ x * (1 - x) ^ d := mul_le_mul_of_nonneg_left hpow_ge hx0
      _ ≤ x * (1 - x) ^ (Γ i).card := mul_le_mul_of_nonneg_left hpow_mono hx0

/-- **Symmetric Lovász Local Lemma (`4 * p * d ≤ 1`, `d ≥ 1`)**:
Elementary constant-free corollary of the asymmetric LLL with `x_i = 1 / (2d)`. -/
theorem lll_symmetric_four
    {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]
    (μ : FinProbSpace Ω)
    (A : ι → Finset Ω)
    (Γ : ι → Finset ι)
    (p : ℝ) (d : ℕ) (hd : 1 ≤ d)
    (hdeg : ∀ i, (Γ i).card ≤ d)
    (hp : ∀ i, μ.prob (A i) ≤ p)
    (hindep : ∀ i (S : Finset ι), i ∉ S → Disjoint S (Γ i) →
      μ.prob (A i ∩ avoidEvents A S) = μ.prob (A i) * μ.prob (avoidEvents A S))
    (h4pd : 4 * p * (d : ℝ) ≤ 1) :
    ∃ ω : Ω, ∀ i : ι, ω ∉ A i := by
  let x : ℝ := 1 / (2 * (d : ℝ))
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x < 1 := by
    dsimp [x]
    rw [div_lt_one (by linarith)]
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hbern : (1 : ℝ) / 2 ≤ (1 - x) ^ d := by
    have h := one_add_mul_le_pow (a := -x) (by linarith) d
    have hcalc : 1 + (d : ℝ) * (-x) = 1 / 2 := by
      dsimp [x]; field_simp [ne_of_gt hd_pos]; ring
    rw [← sub_eq_add_neg] at h
    linarith
  refine lll_asymmetric_exists μ A Γ (fun _ => x) (fun _ => hx0) (fun _ => hx1) hindep ?_
  intro i
  rw [Finset.prod_const]
  have hpow_mono : (1 - x) ^ d ≤ (1 - x) ^ (Γ i).card :=
    pow_le_pow_of_le_one (by linarith) (by linarith) (hdeg i)
  have hp_le : p ≤ x * (1 / 2) := by
    dsimp [x]
    have hden : (0 : ℝ) < 4 * d := by linarith
    have hdiv : p ≤ 1 / (4 * (d : ℝ)) := (le_div_iff₀ hden).mpr (by linarith)
    calc p ≤ 1 / (4 * (d : ℝ)) := hdiv
      _ = 1 / (2 * (d : ℝ)) * (1 / 2) := by field_simp [ne_of_gt hd_pos]; ring
  calc μ.prob (A i) ≤ p := hp i
    _ ≤ x * (1 / 2) := hp_le
    _ ≤ x * (1 - x) ^ d := mul_le_mul_of_nonneg_left hbern hx0
    _ ≤ x * (1 - x) ^ (Γ i).card := mul_le_mul_of_nonneg_left hpow_mono hx0

/-- **Variable-Model Asymmetric Lovász Local Lemma on a Finite Product Space**:
When each bad event `A i` depends only on coordinates `vbl i ⊆ κ`, mutual independence from
all events with disjoint variable sets is discharged automatically. -/
theorem lll_product_asymmetric
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    {α : κ → Type*} [∀ k, Fintype (α k)] [∀ k, DecidableEq (α k)]
    (ν : ∀ k, FinProbSpace (α k))
    (A : ι → Finset (∀ k, α k))
    (vbl : ι → Finset κ)
    (hdep : ∀ i, FinProbSpace.DependsOn (A i) (vbl i))
    (x : ι → ℝ)
    (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : ∀ i, x i < 1)
    (hbound : ∀ i, (FinProbSpace.prod ν).prob (A i) ≤
      x i * ∏ j ∈ Finset.univ.filter (fun j => j ≠ i ∧ ¬ Disjoint (vbl i) (vbl j)), (1 - x j)) :
    ∃ ω : ∀ k, α k, ∀ i : ι, ω ∉ A i := by
  let Γ : ι → Finset ι := fun i =>
    Finset.univ.filter (fun j => j ≠ i ∧ ¬ Disjoint (vbl i) (vbl j))
  refine lll_asymmetric_exists (FinProbSpace.prod ν) A Γ x hx0 hx1 ?_ hbound
  intro i S hiS hdisj
  refine FinProbSpace.prob_prod_inter_of_disjoint_dependsOn ν (hdep i)
    (dependsOn_avoidEvents A vbl hdep S) ?_
  rw [Finset.disjoint_biUnion_right]
  intro j hjS
  by_contra hndisj
  have hjne : j ≠ i := fun heq => hiS (heq ▸ hjS)
  have hjΓ : j ∈ Γ i := by
    simp only [Γ, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hjne, hndisj⟩
  exact Finset.disjoint_left.mp hdisj hjS hjΓ

/-- **Variable-Model Symmetric Lovász Local Lemma (`e * p * (d + 1) ≤ 1`) on a Finite Product Space**:
When each bad event `A i` depends only on coordinates `vbl i ⊆ κ`, each `vbl i` intersects at most
`d` other `vbl j` (`j ≠ i`), every `P(A i) ≤ p`, and `e * p * (d + 1) ≤ 1`, then there exists an
outcome `ω` avoiding every bad event `A i`. -/
theorem lll_product_symmetric_exp
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    {α : κ → Type*} [∀ k, Fintype (α k)] [∀ k, DecidableEq (α k)]
    (ν : ∀ k, FinProbSpace (α k))
    (A : ι → Finset (∀ k, α k))
    (vbl : ι → Finset κ)
    (hdep : ∀ i, FinProbSpace.DependsOn (A i) (vbl i))
    (p : ℝ) (d : ℕ)
    (hdeg : ∀ i, (Finset.univ.filter (fun j => j ≠ i ∧ ¬ Disjoint (vbl i) (vbl j))).card ≤ d)
    (hp : ∀ i, (FinProbSpace.prod ν).prob (A i) ≤ p)
    (hep : Real.exp 1 * p * (d + 1 : ℝ) ≤ 1) :
    ∃ ω : ∀ k, α k, ∀ i : ι, ω ∉ A i := by
  let Γ : ι → Finset ι := fun i =>
    Finset.univ.filter (fun j => j ≠ i ∧ ¬ Disjoint (vbl i) (vbl j))
  refine lll_symmetric_exp (FinProbSpace.prod ν) A Γ p d hdeg hp ?_ hep
  intro i S hiS hdisj
  refine FinProbSpace.prob_prod_inter_of_disjoint_dependsOn ν (hdep i)
    (dependsOn_avoidEvents A vbl hdep S) ?_
  rw [Finset.disjoint_biUnion_right]
  intro j hjS
  by_contra hndisj
  have hjne : j ≠ i := fun heq => hiS (heq ▸ hjS)
  have hjΓ : j ∈ Γ i := by
    simp only [Γ, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hjne, hndisj⟩
  exact Finset.disjoint_left.mp hdisj hjS hjΓ


/-! ## Section 2: Chernoff–Hoeffding Exponential Concentration Bounds -/

/-- Analytic core of Hoeffding's Lemma: for `p ∈ [0, 1]` and all `h : ℝ`,
`exp(-p * h) * (1 - p + p * exp h) ≤ exp(h^2 / 8)`. -/
lemma hoeffding_analytic_ineq {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (h : ℝ) :
    Real.exp (-p * h) * (1 - p + p * Real.exp h) ≤ Real.exp (h ^ 2 / 8) := by
  let D : ℝ → ℝ := fun t => 1 - p + p * Real.exp t
  have hD_pos : ∀ t : ℝ, 0 < D t := by
    intro t
    dsimp [D]
    rcases eq_or_lt_of_le hp0 with rfl | hp_pos
    · norm_num
    · have : 0 < p * Real.exp t := mul_pos hp_pos (Real.exp_pos t)
      linarith
  let φ : ℝ → ℝ := fun t => -p * t + Real.log (D t)
  let ψ : ℝ → ℝ := fun t => t ^ 2 / 8 - φ t
  let ψ' : ℝ → ℝ := fun t => t / 4 + p - p * Real.exp t / D t
  have hD_deriv : ∀ t : ℝ, HasDerivAt D (p * Real.exp t) t := by
    intro t
    have h1 := ((Real.hasDerivAt_exp t).const_mul p).const_add (1 - p)
    simpa [D] using h1
  have hψ_deriv : ∀ t : ℝ, HasDerivAt ψ (ψ' t) t := by
    intro t
    have hsq : HasDerivAt (fun x : ℝ => x ^ 2 / 8) (t / 4) t := by
      refine ((hasDerivAt_pow 2 t).div_const (8 : ℝ)).congr_deriv ?_
      norm_num; ring
    have hlin : HasDerivAt (fun x : ℝ => -p * x) (-p) t := by
      simpa using (hasDerivAt_id t).const_mul (-p)
    have hlog : HasDerivAt (fun x : ℝ => Real.log (D x)) (p * Real.exp t / D t) t :=
      (hD_deriv t).log (ne_of_gt (hD_pos t))
    have hφ : HasDerivAt φ (-p + p * Real.exp t / D t) t := hlin.add hlog
    refine (hsq.sub hφ).congr_deriv ?_
    dsimp [ψ']; ring
  have hψ'_deriv : ∀ t : ℝ,
      HasDerivAt ψ' (1 / 4 - p * Real.exp t * (1 - p) / (D t) ^ 2) t := by
    intro t
    have h1 : HasDerivAt (fun x : ℝ => x / 4 + p) (1 / 4) t := by
      simpa using ((hasDerivAt_id t).div_const (4 : ℝ)).add_const p
    have hnum : HasDerivAt (fun x : ℝ => p * Real.exp x) (p * Real.exp t) t :=
      (Real.hasDerivAt_exp t).const_mul p
    have hquot := hnum.div (hD_deriv t) (ne_of_gt (hD_pos t))
    refine (h1.sub hquot).congr_deriv ?_
    have hDn : D t ≠ 0 := ne_of_gt (hD_pos t)
    dsimp [D] at hDn ⊢
    field_simp [hDn]
    ring
  have hψ'_mono : Monotone ψ' := by
    refine monotone_of_deriv_nonneg (fun t => (hψ'_deriv t).differentiableAt) ?_
    intro t
    rw [(hψ'_deriv t).deriv]
    have hD2 : 0 < (D t) ^ 2 := sq_pos_of_pos (hD_pos t)
    rw [sub_nonneg, div_le_iff₀ hD2]
    dsimp [D]
    nlinarith [sq_nonneg ((1 - p) - p * Real.exp t)]
  have hψ'0 : ψ' 0 = 0 := by
    dsimp [ψ', D]
    simp [Real.exp_zero]
  have hψ0 : ψ 0 = 0 := by
    dsimp [ψ, φ, D]
    simp [Real.exp_zero, Real.log_one]
  have hψ_nonneg : 0 ≤ ψ h := by
    rcases le_total 0 h with hh | hh
    · have hmono : MonotoneOn ψ (Set.Ici 0) := by
        refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
          (fun t _ => (hψ_deriv t).continuousAt.continuousWithinAt)
          (fun t _ => (hψ_deriv t).differentiableAt.differentiableWithinAt) ?_
        intro t ht
        rw [(hψ_deriv t).deriv]
        have ht0 : (0 : ℝ) ≤ t := le_of_lt (by simpa [interior_Ici] using ht)
        rw [← hψ'0]
        exact hψ'_mono ht0
      rw [← hψ0]
      exact hmono (le_refl (0 : ℝ)) hh hh
    · have hanti : AntitoneOn ψ (Set.Iic 0) := by
        refine antitoneOn_of_deriv_nonpos (convex_Iic 0)
          (fun t _ => (hψ_deriv t).continuousAt.continuousWithinAt)
          (fun t _ => (hψ_deriv t).differentiableAt.differentiableWithinAt) ?_
        intro t ht
        rw [(hψ_deriv t).deriv]
        have ht0 : t ≤ (0 : ℝ) := le_of_lt (by simpa [interior_Iic] using ht)
        rw [← hψ'0]
        exact hψ'_mono ht0
      rw [← hψ0]
      exact hanti hh (le_refl (0 : ℝ)) hh
  have hφ_le : φ h ≤ h ^ 2 / 8 := by dsimp [ψ] at hψ_nonneg; linarith
  have hexp := Real.exp_le_exp.mpr hφ_le
  dsimp [φ] at hexp
  rw [Real.exp_add, Real.exp_log (hD_pos h)] at hexp
  exact hexp

/-- **Hoeffding's Lemma** on any finite probability space:
If `a ≤ X ω ≤ b` for all `ω`, then for every `t : ℝ`,
`E[exp(t * (X - E[X]))] ≤ exp(t^2 * (b - a)^2 / 8)`. -/
theorem hoeffding_lemma {Ω : Type*} [Fintype Ω]
    (μ : FinProbSpace Ω) (X : Ω → ℝ) (a b : ℝ)
    (hX : ∀ ω, a ≤ X ω ∧ X ω ≤ b) (t : ℝ) :
    μ.expect (fun ω => Real.exp (t * (X ω - μ.expect X))) ≤
      Real.exp (t ^ 2 * (b - a) ^ 2 / 8) := by
  set m := μ.expect X
  have hm_ge : a ≤ m := by
    calc a = μ.expect (fun _ => a) := (μ.expect_const a).symm
      _ ≤ μ.expect X := μ.expect_mono fun ω => (hX ω).1
  have hm_le : m ≤ b := by
    calc μ.expect X ≤ μ.expect (fun _ => b) := μ.expect_mono fun ω => (hX ω).2
      _ = b := μ.expect_const b
  rcases eq_or_lt_of_le (le_trans hm_ge hm_le) with hab | hab
  · have hXm : ∀ ω, X ω = m := fun ω => by linarith [(hX ω).1, (hX ω).2]
    have hconst : (fun ω => Real.exp (t * (X ω - m))) = fun _ => 1 := by
      ext ω; rw [hXm ω, sub_self, mul_zero, Real.exp_zero]
    rw [hconst, μ.expect_const, ← hab, sub_self]
    simp
  · have hba_pos : 0 < b - a := sub_pos.mpr hab
    set a' := a - m
    set b' := b - m
    have hba' : b' - a' = b - a := by ring
    have hconv : ∀ ω, Real.exp (t * (X ω - m)) ≤
        ((b' - (X ω - m)) / (b - a)) * Real.exp (t * a') +
        (((X ω - m) - a') / (b - a)) * Real.exp (t * b') := by
      intro ω
      have w1 : 0 ≤ (b' - (X ω - m)) / (b - a) :=
        div_nonneg (by linarith [(hX ω).2]) (le_of_lt hba_pos)
      have w2 : 0 ≤ ((X ω - m) - a') / (b - a) :=
        div_nonneg (by linarith [(hX ω).1]) (le_of_lt hba_pos)
      have wsum : (b' - (X ω - m)) / (b - a) + ((X ω - m) - a') / (b - a) = 1 := by
        field_simp [ne_of_gt hba_pos]; dsimp [a', b']; ring
      have hcomb : ((b' - (X ω - m)) / (b - a)) * (t * a') +
          (((X ω - m) - a') / (b - a)) * (t * b') = t * (X ω - m) := by
        field_simp [ne_of_gt hba_pos]; dsimp [a', b']; ring
      have hc := convexOn_exp.2 (Set.mem_univ (t * a')) (Set.mem_univ (t * b')) w1 w2 wsum
      simpa [smul_eq_mul, hcomb] using hc
    have hexp_Y : μ.expect (fun ω => X ω - m) = 0 := by
      rw [μ.expect_sub, μ.expect_const, sub_self]
    have hstep1 : μ.expect (fun ω => Real.exp (t * (X ω - m))) ≤
        (b' / (b - a)) * Real.exp (t * a') + (-a' / (b - a)) * Real.exp (t * b') := by
      calc μ.expect (fun ω => Real.exp (t * (X ω - m)))
          ≤ μ.expect (fun ω =>
              ((b' - (X ω - m)) / (b - a)) * Real.exp (t * a') +
              (((X ω - m) - a') / (b - a)) * Real.exp (t * b')) := μ.expect_mono hconv
        _ = (b' / (b - a)) * Real.exp (t * a') + (-a' / (b - a)) * Real.exp (t * b') := by
            have hrew : (fun ω => ((b' - (X ω - m)) / (b - a)) * Real.exp (t * a') +
                (((X ω - m) - a') / (b - a)) * Real.exp (t * b')) =
              (fun ω => ((b' / (b - a)) * Real.exp (t * a') + (-a' / (b - a)) * Real.exp (t * b')) +
                ((Real.exp (t * b') - Real.exp (t * a')) / (b - a)) * (X ω - m)) := by
              ext ω; ring
            rw [hrew, μ.expect_add, μ.expect_const, μ.expect_const_mul, hexp_Y, mul_zero, add_zero]
    set p := -a' / (b - a)
    set h := t * (b - a)
    have hp0 : 0 ≤ p := div_nonneg (by dsimp [a']; linarith) (le_of_lt hba_pos)
    have hp1 : p ≤ 1 := by
      dsimp [p, a']
      rw [div_le_one hba_pos]; linarith
    have h1mp : 1 - p = b' / (b - a) := by
      dsimp [p, a', b']; field_simp [ne_of_gt hba_pos]; ring
    have hta' : t * a' = -p * h := by
      dsimp [p, h]; field_simp [ne_of_gt hba_pos]
    have htb' : t * b' = -p * h + h := by
      dsimp [p, h, a', b']; field_simp [ne_of_gt hba_pos]; ring
    have hrhs : (b' / (b - a)) * Real.exp (t * a') + (-a' / (b - a)) * Real.exp (t * b') =
        Real.exp (-p * h) * (1 - p + p * Real.exp h) := by
      rw [← h1mp, hta', htb', Real.exp_add]
      ring
    have hh2 : h ^ 2 / 8 = t ^ 2 * (b - a) ^ 2 / 8 := by dsimp [h]; ring
    calc μ.expect (fun ω => Real.exp (t * (X ω - m)))
        ≤ (b' / (b - a)) * Real.exp (t * a') + (-a' / (b - a)) * Real.exp (t * b') := hstep1
      _ = Real.exp (-p * h) * (1 - p + p * Real.exp h) := hrhs
      _ ≤ Real.exp (h ^ 2 / 8) := hoeffding_analytic_ineq hp0 hp1 h
      _ = Real.exp (t ^ 2 * (b - a) ^ 2 / 8) := by rw [hh2]

/-- **Hoeffding's Inequality (Upper Tail)** for sums of independent bounded random variables
on a finite product probability space. -/
theorem hoeffding_upper
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (μ : ∀ i, FinProbSpace (α i))
    (X : ∀ i, α i → ℝ) (a b : ι → ℝ)
    (hX : ∀ i x, a i ≤ X i x ∧ X i x ≤ b i)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hV : 0 < ∑ i : ι, (b i - a i) ^ 2) :
    (FinProbSpace.prod μ).prob (Finset.univ.filter (fun ω =>
        ε ≤ (∑ i : ι, X i (ω i)) - ∑ i : ι, (μ i).expect (X i))) ≤
      Real.exp (-2 * ε ^ 2 / ∑ i : ι, (b i - a i) ^ 2) := by
  classical
  set V := ∑ i : ι, (b i - a i) ^ 2
  set E := ∑ i : ι, (μ i).expect (X i)
  rcases eq_or_lt_of_le hε with rfl | hε_pos
  · simp only [sq, mul_zero, zero_div, Real.exp_zero]
    exact (FinProbSpace.prod μ).prob_le_one _
  · set t := 4 * ε / V
    have ht_pos : 0 < t := div_pos (by linarith) hV
    have hmgf := (FinProbSpace.prod μ).chernoff_mgf_upper
      (fun ω => (∑ i : ι, X i (ω i)) - E) ε ht_pos
    have hprod_exp : (FinProbSpace.prod μ).expect
        (fun ω => Real.exp (t * ((∑ i : ι, X i (ω i)) - E))) ≤
        Real.exp (t ^ 2 * V / 8) := by
      have hrew : ∀ ω : ∀ i, α i,
          Real.exp (t * ((∑ i : ι, X i (ω i)) - E)) =
            ∏ i : ι, Real.exp (t * (X i (ω i) - (μ i).expect (X i))) := by
        intro ω
        rw [← Real.exp_sum]
        congr 1
        dsimp [E]
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      simp_rw [hrew]
      rw [FinProbSpace.expect_prod μ (fun i x => Real.exp (t * (X i x - (μ i).expect (X i))))]
      calc ∏ i : ι, (μ i).expect (fun x => Real.exp (t * (X i x - (μ i).expect (X i))))
          ≤ ∏ i : ι, Real.exp (t ^ 2 * (b i - a i) ^ 2 / 8) :=
            Finset.prod_le_prod
              (fun i _ => (μ i).expect_nonneg fun x => le_of_lt (Real.exp_pos _))
              (fun i _ => hoeffding_lemma (μ i) (X i) (a i) (b i) (hX i) t)
        _ = Real.exp (∑ i : ι, t ^ 2 * (b i - a i) ^ 2 / 8) := (Real.exp_sum _ _).symm
        _ = Real.exp (t ^ 2 * V / 8) := by
            congr 1
            dsimp [V]
            rw [Finset.mul_sum, Finset.sum_div]
    have hexp_opt : -t * ε + t ^ 2 * V / 8 = -2 * ε ^ 2 / V := by
      dsimp [t]; field_simp [ne_of_gt hV]; ring
    calc (FinProbSpace.prod μ).prob (Finset.univ.filter (fun ω =>
            ε ≤ (∑ i : ι, X i (ω i)) - E))
        ≤ Real.exp (-t * ε) * (FinProbSpace.prod μ).expect
            (fun ω => Real.exp (t * ((∑ i : ι, X i (ω i)) - E))) := hmgf
      _ ≤ Real.exp (-t * ε) * Real.exp (t ^ 2 * V / 8) :=
          mul_le_mul_of_nonneg_left hprod_exp (le_of_lt (Real.exp_pos _))
      _ = Real.exp (-t * ε + t ^ 2 * V / 8) := (Real.exp_add _ _).symm
      _ = Real.exp (-2 * ε ^ 2 / V) := by rw [hexp_opt]

/-- **Hoeffding's Inequality (Lower Tail)** for sums of independent bounded random variables. -/
theorem hoeffding_lower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (μ : ∀ i, FinProbSpace (α i))
    (X : ∀ i, α i → ℝ) (a b : ι → ℝ)
    (hX : ∀ i x, a i ≤ X i x ∧ X i x ≤ b i)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hV : 0 < ∑ i : ι, (b i - a i) ^ 2) :
    (FinProbSpace.prod μ).prob (Finset.univ.filter (fun ω =>
        (∑ i : ι, X i (ω i)) - ∑ i : ι, (μ i).expect (X i) ≤ -ε)) ≤
      Real.exp (-2 * ε ^ 2 / ∑ i : ι, (b i - a i) ^ 2) := by
  classical
  have hnegX : ∀ i x, -b i ≤ -X i x ∧ -X i x ≤ -a i := fun i x =>
    ⟨neg_le_neg (hX i x).2, neg_le_neg (hX i x).1⟩
  have hVeq : ∑ i : ι, (-a i - -b i) ^ 2 = ∑ i : ι, (b i - a i) ^ 2 :=
    Finset.sum_congr rfl fun i _ => by ring
  have hup := hoeffding_upper μ (fun i x => -X i x) (fun i => -b i) (fun i => -a i)
    hnegX hε (hVeq.symm ▸ hV)
  rw [hVeq] at hup
  refine le_trans ((FinProbSpace.prod μ).prob_mono ?_) hup
  intro ω hω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
  simp only [Finset.sum_neg_distrib, FinProbSpace.expect_neg]
  linarith

/-- **Hoeffding's Inequality (Two-Sided Tail)** for sums of independent bounded random variables. -/
theorem hoeffding_two_sided
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (μ : ∀ i, FinProbSpace (α i))
    (X : ∀ i, α i → ℝ) (a b : ι → ℝ)
    (hX : ∀ i x, a i ≤ X i x ∧ X i x ≤ b i)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hV : 0 < ∑ i : ι, (b i - a i) ^ 2) :
    (FinProbSpace.prod μ).prob (Finset.univ.filter (fun ω =>
        ε ≤ |(∑ i : ι, X i (ω i)) - ∑ i : ι, (μ i).expect (X i)|)) ≤
      2 * Real.exp (-2 * ε ^ 2 / ∑ i : ι, (b i - a i) ^ 2) := by
  classical
  set E := ∑ i : ι, (μ i).expect (X i)
  have hsub : Finset.univ.filter (fun ω : ∀ i, α i => ε ≤ |(∑ i : ι, X i (ω i)) - E|) ⊆
      Finset.univ.filter (fun ω : ∀ i, α i => ε ≤ (∑ i : ι, X i (ω i)) - E) ∪
      Finset.univ.filter (fun ω : ∀ i, α i => (∑ i : ι, X i (ω i)) - E ≤ -ε) := by
    intro ω hω
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    rcases le_abs.mp hω with h1 | h2
    · exact Or.inl h1
    · exact Or.inr (by linarith)
  have hu := hoeffding_upper μ X a b hX hε hV
  have hl := hoeffding_lower μ X a b hX hε hV
  have hunion := (FinProbSpace.prod μ).prob_union_le
    (Finset.univ.filter (fun ω => ε ≤ (∑ i : ι, X i (ω i)) - E))
    (Finset.univ.filter (fun ω => (∑ i : ι, X i (ω i)) - E ≤ -ε))
  linarith [(FinProbSpace.prod μ).prob_mono hsub]

/-! ### Multiplicative Chernoff Bounds for Independent `[0, 1]`-Valued Sums -/

/-- MGF bound for a sum of independent `[0, 1]`-valued random variables:
`E[exp(t * S)] ≤ exp((exp t - 1) * E[S])` for every `t : ℝ`. -/
theorem chernoff_unit_mgf
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (μ : ∀ i, FinProbSpace (α i))
    (X : ∀ i, α i → ℝ)
    (hX : ∀ i x, 0 ≤ X i x ∧ X i x ≤ 1)
    (t : ℝ) :
    (FinProbSpace.prod μ).expect (fun ω => Real.exp (t * ∑ i : ι, X i (ω i))) ≤
      Real.exp ((Real.exp t - 1) * ∑ i : ι, (μ i).expect (X i)) := by
  have hrew : ∀ ω : ∀ i, α i,
      Real.exp (t * ∑ i : ι, X i (ω i)) = ∏ i : ι, Real.exp (t * X i (ω i)) := by
    intro ω
    rw [Finset.mul_sum, Real.exp_sum]
  simp_rw [hrew]
  rw [FinProbSpace.expect_prod μ (fun i x => Real.exp (t * X i x))]
  have hcoord : ∀ i : ι,
      (μ i).expect (fun x => Real.exp (t * X i x)) ≤
        Real.exp ((Real.exp t - 1) * (μ i).expect (X i)) := by
    intro i
    have hpt : ∀ x : α i, Real.exp (t * X i x) ≤ 1 + (Real.exp t - 1) * X i x := by
      intro x
      have hx0 := (hX i x).1
      have hx1 := (hX i x).2
      have hc := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ t)
        (show 0 ≤ 1 - X i x by linarith) hx0 (by ring)
      have hcomb : (1 - X i x) * (0 : ℝ) + X i x * t = t * X i x := by ring
      simp only [smul_eq_mul, hcomb, Real.exp_zero] at hc
      linarith
    calc (μ i).expect (fun x => Real.exp (t * X i x))
        ≤ (μ i).expect (fun x => 1 + (Real.exp t - 1) * X i x) := (μ i).expect_mono hpt
      _ = 1 + (Real.exp t - 1) * (μ i).expect (X i) := by
          rw [(μ i).expect_add, (μ i).expect_const, (μ i).expect_const_mul]
      _ ≤ Real.exp ((Real.exp t - 1) * (μ i).expect (X i)) := by
          linarith [Real.add_one_le_exp ((Real.exp t - 1) * (μ i).expect (X i))]
  calc ∏ i : ι, (μ i).expect (fun x => Real.exp (t * X i x))
      ≤ ∏ i : ι, Real.exp ((Real.exp t - 1) * (μ i).expect (X i)) :=
        Finset.prod_le_prod
          (fun i _ => (μ i).expect_nonneg fun x => le_of_lt (Real.exp_pos _))
          (fun i _ => hcoord i)
    _ = Real.exp (∑ i : ι, (Real.exp t - 1) * (μ i).expect (X i)) := (Real.exp_sum _ _).symm
    _ = Real.exp ((Real.exp t - 1) * ∑ i : ι, (μ i).expect (X i)) := by
        rw [Finset.mul_sum]

/-- Analytic inequality for multiplicative upper Chernoff:
for all `δ ≥ 0`, `δ - (1 + δ) * log(1 + δ) ≤ -δ^2 / (2 + δ)`. -/
lemma chernoff_upper_kl_le {δ : ℝ} (hδ : 0 ≤ δ) :
    δ - (1 + δ) * Real.log (1 + δ) ≤ -(δ ^ 2) / (2 + δ) := by
  let g : ℝ → ℝ := fun x => (1 + x) * Real.log (1 + x) - x - x ^ 2 / (2 + x)
  let g' : ℝ → ℝ := fun x => Real.log (1 + x) - (4 * x + x ^ 2) / (2 + x) ^ 2
  have hg_deriv : ∀ x : ℝ, 0 ≤ x → HasDerivAt g (g' x) x := by
    intro x hx
    have h1x : 0 < 1 + x := by linarith
    have h2x : 0 < 2 + x := by linarith
    have hd1 : HasDerivAt (fun t : ℝ => 1 + t) 1 x := by
      simpa using (hasDerivAt_id x).const_add (1 : ℝ)
    have hdlog : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + x)) x := by
      simpa using hd1.log (ne_of_gt h1x)
    have hdmul : HasDerivAt (fun t : ℝ => (1 + t) * Real.log (1 + t))
        (1 * Real.log (1 + x) + (1 + x) * (1 / (1 + x))) x := hd1.mul hdlog
    have hd2 : HasDerivAt (fun t : ℝ => 2 + t) 1 x := by
      simpa using (hasDerivAt_id x).const_add (2 : ℝ)
    have hdq : HasDerivAt (fun t : ℝ => t ^ 2 / (2 + t))
        ((2 * x * (2 + x) - x ^ 2 * 1) / (2 + x) ^ 2) x := by
      have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
        simpa using hasDerivAt_pow 2 x
      exact hsq.div hd2 (ne_of_gt h2x)
    refine ((hdmul.sub (hasDerivAt_id x)).sub hdq).congr_deriv ?_
    dsimp [g']
    field_simp [ne_of_gt h1x, ne_of_gt h2x]
    ring
  have hg'_deriv : ∀ x : ℝ, 0 ≤ x →
      HasDerivAt g' ((4 * x + 6 * x ^ 2 + x ^ 3) / ((1 + x) * (2 + x) ^ 3)) x := by
    intro x hx
    have h1x : 0 < 1 + x := by linarith
    have h2x : 0 < 2 + x := by linarith
    have hd1 : HasDerivAt (fun t : ℝ => 1 + t) 1 x := by
      simpa using (hasDerivAt_id x).const_add (1 : ℝ)
    have hdlog : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + x)) x := by
      simpa using hd1.log (ne_of_gt h1x)
    have hnum : HasDerivAt (fun t : ℝ => 4 * t + t ^ 2) (4 + 2 * x) x := by
      have h4 : HasDerivAt (fun t : ℝ => 4 * t) 4 x := by
        simpa using (hasDerivAt_id x).const_mul (4 : ℝ)
      have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
        simpa using hasDerivAt_pow 2 x
      exact h4.add hsq
    have hden : HasDerivAt (fun t : ℝ => (2 + t) ^ 2) (2 * (2 + x)) x := by
      have hd2 : HasDerivAt (fun t : ℝ => 2 + t) 1 x := by
        simpa using (hasDerivAt_id x).const_add (2 : ℝ)
      refine (hd2.pow 2).congr_deriv ?_
      norm_num
    have hdq := hnum.div hden (ne_of_gt (sq_pos_of_pos h2x))
    refine (hdlog.sub hdq).congr_deriv ?_
    have h1n : (1 + x) ≠ 0 := ne_of_gt h1x
    have h2n : (2 + x) ≠ 0 := ne_of_gt h2x
    field_simp [h1n, h2n]
    ring
  have hg'_mono : MonotoneOn g' (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x hx => (hg'_deriv x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hg'_deriv x (le_of_lt (by simpa [interior_Ici] using hx))).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := le_of_lt (by simpa [interior_Ici] using hx)
    rw [(hg'_deriv x hx0).deriv]
    positivity
  have hg'0 : g' 0 = 0 := by dsimp [g']; simp [Real.log_one]
  have hg0 : g 0 = 0 := by dsimp [g]; simp [Real.log_one]
  have hg_mono : MonotoneOn g (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x hx => (hg_deriv x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hg_deriv x (le_of_lt (by simpa [interior_Ici] using hx))).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := le_of_lt (by simpa [interior_Ici] using hx)
    rw [(hg_deriv x hx0).deriv, ← hg'0]
    exact hg'_mono (le_refl (0 : ℝ)) hx0 hx0
  have hge : 0 ≤ g δ := by rw [← hg0]; exact hg_mono (le_refl (0 : ℝ)) hδ hδ
  dsimp [g] at hge
  rw [neg_div]
  linarith

/-- Analytic inequality for multiplicative lower Chernoff:
for all `0 ≤ δ < 1`, `-δ - (1 - δ) * log(1 - δ) ≤ -δ^2 / 2`. -/
lemma chernoff_lower_kl_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    -δ - (1 - δ) * Real.log (1 - δ) ≤ -(δ ^ 2) / 2 := by
  let g : ℝ → ℝ := fun x => (1 - x) * Real.log (1 - x) + x - x ^ 2 / 2
  let g' : ℝ → ℝ := fun x => -Real.log (1 - x) - x
  have hg_deriv : ∀ x : ℝ, x < 1 → HasDerivAt g (g' x) x := by
    intro x hx
    have h1x : 0 < 1 - x := by linarith
    have hd1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub (1 : ℝ)
    have hdlog : HasDerivAt (fun t : ℝ => Real.log (1 - t)) (-1 / (1 - x)) x :=
      hd1.log (ne_of_gt h1x)
    have hdmul : HasDerivAt (fun t : ℝ => (1 - t) * Real.log (1 - t))
        ((-1) * Real.log (1 - x) + (1 - x) * (-1 / (1 - x))) x := hd1.mul hdlog
    have hdsq : HasDerivAt (fun t : ℝ => t ^ 2 / 2) x x := by
      refine ((hasDerivAt_pow 2 x).div_const (2 : ℝ)).congr_deriv ?_
      norm_num
    refine ((hdmul.add (hasDerivAt_id x)).sub hdsq).congr_deriv ?_
    dsimp [g']
    field_simp [ne_of_gt h1x]
    ring
  have hg'_deriv : ∀ x : ℝ, x < 1 → HasDerivAt g' (x / (1 - x)) x := by
    intro x hx
    have h1x : 0 < 1 - x := by linarith
    have hd1 : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub (1 : ℝ)
    have hdlog : HasDerivAt (fun t : ℝ => Real.log (1 - t)) (-1 / (1 - x)) x :=
      hd1.log (ne_of_gt h1x)
    refine ((hdlog.neg).sub (hasDerivAt_id x)).congr_deriv ?_
    have h1n : (1 - x) ≠ 0 := ne_of_gt h1x
    field_simp [h1n]
    ring
  have hg'_mono : MonotoneOn g' (Set.Ico 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
      (fun x hx => (hg'_deriv x hx.2).continuousAt.continuousWithinAt)
      (fun x hx => (hg'_deriv x ((by simpa [interior_Ico] using hx : x ∈ Set.Ioo 0 1).2)).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    have hxo : x ∈ Set.Ioo (0 : ℝ) 1 := by simpa [interior_Ico] using hx
    rw [(hg'_deriv x hxo.2).deriv]
    exact div_nonneg (le_of_lt hxo.1) (by linarith [hxo.2])
  have hg'0 : g' 0 = 0 := by dsimp [g']; simp [Real.log_one]
  have hg0 : g 0 = 0 := by dsimp [g]; simp [Real.log_one]
  have hg_mono : MonotoneOn g (Set.Ico 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
      (fun x hx => (hg_deriv x hx.2).continuousAt.continuousWithinAt)
      (fun x hx => (hg_deriv x ((by simpa [interior_Ico] using hx : x ∈ Set.Ioo 0 1).2)).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    have hxo : x ∈ Set.Ioo (0 : ℝ) 1 := by simpa [interior_Ico] using hx
    rw [(hg_deriv x hxo.2).deriv, ← hg'0]
    exact hg'_mono ⟨le_refl 0, by norm_num⟩ ⟨le_of_lt hxo.1, hxo.2⟩ (le_of_lt hxo.1)
  have hge : 0 ≤ g δ := by
    rw [← hg0]
    exact hg_mono ⟨le_refl 0, by norm_num⟩ ⟨hδ0, hδ1⟩ hδ0
  dsimp [g] at hge
  linarith

/-- **Multiplicative Chernoff Upper Tail (Exact KL Form)**:
For independent `[0, 1]`-valued `X i` with `m = ∑ i, E[X i]` and `δ > 0`:
`P(∑ X_i ≥ (1 + δ) m) ≤ exp(m * (δ - (1 + δ) * log(1 + δ)))`. -/
theorem chernoff_upper_kl
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (μ : ∀ i, FinProbSpace (α i))
    (X : ∀ i, α i → ℝ)
    (hX : ∀ i x, 0 ≤ X i x ∧ X i x ≤ 1)
    {δ : ℝ} (hδ : 0 < δ) :
    (FinProbSpace.prod μ).prob (Finset.univ.filter (fun ω =>
        (1 + δ) * (∑ i : ι, (μ i).expect (X i)) ≤ ∑ i : ι, X i (ω i))) ≤
      Real.exp ((∑ i : ι, (μ i).expect (X i)) * (δ - (1 + δ) * Real.log (1 + δ))) := by
  classical
  set m := ∑ i : ι, (μ i).expect (X i)
  have ht_pos : 0 < Real.log (1 + δ) := Real.log_pos (by linarith)
  have hmgf := (FinProbSpace.prod μ).chernoff_mgf_upper
    (fun ω => ∑ i : ι, X i (ω i)) ((1 + δ) * m) ht_pos
  have hunit := chernoff_unit_mgf μ X hX (Real.log (1 + δ))
  rw [Real.exp_log (by linarith : 0 < 1 + δ)] at hunit
  calc (FinProbSpace.prod μ).prob (Finset.univ.filter (fun ω =>
          (1 + δ) * m ≤ ∑ i : ι, X i (ω i)))
      ≤ Real.exp (-Real.log (1 + δ) * ((1 + δ) * m)) *
          (FinProbSpace.prod μ).expect (fun ω => Real.exp (Real.log (1 + δ) * ∑ i : ι, X i (ω i))) := hmgf
    _ ≤ Real.exp (-Real.log (1 + δ) * ((1 + δ) * m)) *
          Real.exp ((1 + δ - 1) * m) :=
        mul_le_mul_of_nonneg_left hunit (le_of_lt (Real.exp_pos _))
    _ = Real.exp (-Real.log (1 + δ) * ((1 + δ) * m) + (1 + δ - 1) * m) := (Real.exp_add _ _).symm
    _ = Real.exp (m * (δ - (1 + δ) * Real.log (1 + δ))) := by congr 1; ring

/-- **Multiplicative Chernoff Upper Tail (Universal Quadratic Form)**:
For independent `[0, 1]`-valued `X i`, `m = ∑ E[X i]`, and ALL `δ ≥ 0`:
`P(∑ X_i ≥ (1 + δ) m) ≤ exp(-δ^2 * m / (2 + δ))`. -/
theorem chernoff_upper_universal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (μ : ∀ i, FinProbSpace (α i))
    (X : ∀ i, α i → ℝ)
    (hX : ∀ i x, 0 ≤ X i x ∧ X i x ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    (FinProbSpace.prod μ).prob (Finset.univ.filter (fun ω =>
        (1 + δ) * (∑ i : ι, (μ i).expect (X i)) ≤ ∑ i : ι, X i (ω i))) ≤
      Real.exp (-(δ ^ 2) * (∑ i : ι, (μ i).expect (X i)) / (2 + δ)) := by
  classical
  set m := ∑ i : ι, (μ i).expect (X i)
  have hm0 : 0 ≤ m := Finset.sum_nonneg fun i _ => (μ i).expect_nonneg fun x => (hX i x).1
  rcases eq_or_lt_of_le hδ with rfl | hδ_pos
  · simp only [sq, mul_zero, neg_zero, zero_mul, zero_div, Real.exp_zero]
    exact (FinProbSpace.prod μ).prob_le_one _
  · refine le_trans (chernoff_upper_kl μ X hX hδ_pos) (Real.exp_le_exp.mpr ?_)
    have hkl := chernoff_upper_kl_le (le_of_lt hδ_pos)
    calc m * (δ - (1 + δ) * Real.log (1 + δ))
        ≤ m * (-(δ ^ 2) / (2 + δ)) := mul_le_mul_of_nonneg_left hkl hm0
      _ = -(δ ^ 2) * m / (2 + δ) := by ring

/-- **Multiplicative Chernoff Upper Tail (Standard `0 ≤ δ ≤ 1` Form)**:
`P(∑ X_i ≥ (1 + δ) m) ≤ exp(-δ^2 * m / 3)`. -/
theorem chernoff_upper
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (μ : ∀ i, FinProbSpace (α i))
    (X : ∀ i, α i → ℝ)
    (hX : ∀ i x, 0 ≤ X i x ∧ X i x ≤ 1)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (FinProbSpace.prod μ).prob (Finset.univ.filter (fun ω =>
        (1 + δ) * (∑ i : ι, (μ i).expect (X i)) ≤ ∑ i : ι, X i (ω i))) ≤
      Real.exp (-(δ ^ 2) * (∑ i : ι, (μ i).expect (X i)) / 3) := by
  classical
  set m := ∑ i : ι, (μ i).expect (X i)
  have hm0 : 0 ≤ m := Finset.sum_nonneg fun i _ => (μ i).expect_nonneg fun x => (hX i x).1
  refine le_trans (chernoff_upper_universal μ X hX hδ0) (Real.exp_le_exp.mpr ?_)
  have h1 : δ ^ 2 * m / 3 ≤ δ ^ 2 * m / (2 + δ) :=
    div_le_div_of_nonneg_left (mul_nonneg (sq_nonneg δ) hm0) (by linarith) (by linarith)
  have h2 : -(δ ^ 2) * m / (2 + δ) = -(δ ^ 2 * m / (2 + δ)) := by ring
  have h3 : -(δ ^ 2) * m / 3 = -(δ ^ 2 * m / 3) := by ring
  change -(δ ^ 2) * m / (2 + δ) ≤ -(δ ^ 2) * m / 3
  linarith

/-- **Multiplicative Chernoff Lower Tail (Exact KL Form)**:
For independent `[0, 1]`-valued `X i`, `m = ∑ E[X i]`, and `0 < δ < 1`:
`P(∑ X_i ≤ (1 - δ) m) ≤ exp(m * (-δ - (1 - δ) * log(1 - δ)))`. -/
theorem chernoff_lower_kl
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (μ : ∀ i, FinProbSpace (α i))
    (X : ∀ i, α i → ℝ)
    (hX : ∀ i x, 0 ≤ X i x ∧ X i x ≤ 1)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (FinProbSpace.prod μ).prob (Finset.univ.filter (fun ω =>
        ∑ i : ι, X i (ω i) ≤ (1 - δ) * (∑ i : ι, (μ i).expect (X i)))) ≤
      Real.exp ((∑ i : ι, (μ i).expect (X i)) * (-δ - (1 - δ) * Real.log (1 - δ))) := by
  classical
  set m := ∑ i : ι, (μ i).expect (X i)
  have ht_neg : Real.log (1 - δ) < 0 := Real.log_neg (by linarith) (by linarith)
  have hmgf := (FinProbSpace.prod μ).chernoff_mgf_lower
    (fun ω => ∑ i : ι, X i (ω i)) ((1 - δ) * m) ht_neg
  have hunit := chernoff_unit_mgf μ X hX (Real.log (1 - δ))
  rw [Real.exp_log (by linarith : 0 < 1 - δ)] at hunit
  calc (FinProbSpace.prod μ).prob (Finset.univ.filter (fun ω =>
          ∑ i : ι, X i (ω i) ≤ (1 - δ) * m))
      ≤ Real.exp (-Real.log (1 - δ) * ((1 - δ) * m)) *
          (FinProbSpace.prod μ).expect (fun ω => Real.exp (Real.log (1 - δ) * ∑ i : ι, X i (ω i))) := hmgf
    _ ≤ Real.exp (-Real.log (1 - δ) * ((1 - δ) * m)) *
          Real.exp ((1 - δ - 1) * m) :=
        mul_le_mul_of_nonneg_left hunit (le_of_lt (Real.exp_pos _))
    _ = Real.exp (-Real.log (1 - δ) * ((1 - δ) * m) + (1 - δ - 1) * m) := (Real.exp_add _ _).symm
    _ = Real.exp (m * (-δ - (1 - δ) * Real.log (1 - δ))) := by congr 1; ring

/-- **Multiplicative Chernoff Lower Tail (Standard `0 ≤ δ ≤ 1` Form)**:
`P(∑ X_i ≤ (1 - δ) m) ≤ exp(-δ^2 * m / 2)`. -/
theorem chernoff_lower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (μ : ∀ i, FinProbSpace (α i))
    (X : ∀ i, α i → ℝ)
    (hX : ∀ i x, 0 ≤ X i x ∧ X i x ≤ 1)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (FinProbSpace.prod μ).prob (Finset.univ.filter (fun ω =>
        ∑ i : ι, X i (ω i) ≤ (1 - δ) * (∑ i : ι, (μ i).expect (X i)))) ≤
      Real.exp (-(δ ^ 2) * (∑ i : ι, (μ i).expect (X i)) / 2) := by
  classical
  set m := ∑ i : ι, (μ i).expect (X i)
  have hm0 : 0 ≤ m := Finset.sum_nonneg fun i _ => (μ i).expect_nonneg fun x => (hX i x).1
  rcases eq_or_lt_of_le hδ0 with rfl | hδ_pos
  · simp only [sq, mul_zero, neg_zero, zero_mul, zero_div, Real.exp_zero]
    exact (FinProbSpace.prod μ).prob_le_one _
  · rcases eq_or_lt_of_le hδ1 with rfl | hδ_lt1
    · -- Case δ = 1: P(S ≤ 0) ≤ E[exp(-t S)] for all t > 0; take t → ∞ or simply t = 1 gives exp((e⁻¹ - 1) m) ≤ exp(-m/2)!
      have hmgf := (FinProbSpace.prod μ).chernoff_mgf_lower
        (fun ω => ∑ i : ι, X i (ω i)) ((1 - 1) * m) (t := -1) (by norm_num)
      have hunit := chernoff_unit_mgf μ X hX (-1)
      have he1 : Real.exp (-1 : ℝ) - 1 ≤ -(1 : ℝ) / 2 := by
        have h2 : (2 : ℝ) ≤ Real.exp 1 := by
          linarith [Real.add_one_le_exp (1 : ℝ)]
        have hinv : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
          rw [Real.exp_neg, one_div]
          exact inv_anti₀ (by norm_num) h2
        linarith
      calc (FinProbSpace.prod μ).prob (Finset.univ.filter (fun ω =>
              ∑ i : ι, X i (ω i) ≤ (1 - 1) * m))
          ≤ Real.exp (-(-1 : ℝ) * ((1 - 1) * m)) *
              (FinProbSpace.prod μ).expect (fun ω => Real.exp ((-1 : ℝ) * ∑ i : ι, X i (ω i))) := hmgf
        _ ≤ 1 * Real.exp ((Real.exp (-1) - 1) * m) := by
            have h0 : -(-1 : ℝ) * ((1 - 1) * m) = 0 := by ring
            rw [h0, Real.exp_zero]
            exact mul_le_mul_of_nonneg_left hunit (by norm_num)
        _ = Real.exp ((Real.exp (-1) - 1) * m) := one_mul _
        _ ≤ Real.exp (-(1 ^ 2) * m / 2) := by
            apply Real.exp_le_exp.mpr
            have hmul := mul_le_mul_of_nonneg_right he1 hm0
            linarith
    · refine le_trans (chernoff_lower_kl μ X hX hδ_pos hδ_lt1) (Real.exp_le_exp.mpr ?_)
      have hkl := chernoff_lower_kl_le (le_of_lt hδ_pos) hδ_lt1
      calc m * (-δ - (1 - δ) * Real.log (1 - δ))
          ≤ m * (-(δ ^ 2) / 2) := mul_le_mul_of_nonneg_left hkl hm0
        _ = -(δ ^ 2) * m / 2 := by ring


/-! ## Section 3: Kővári–Sós–Turán Theorem (`ex(m, n; K_{s,t})` and `ex(n; K_{s,t})`) -/

/-- Product of two nonnegative, monotone, convex functions on a convex subset of `ℝ` is convex. -/
lemma convexOn_mul_of_nonneg_monotone {C : Set ℝ} {f g : ℝ → ℝ}
    (hC : Convex ℝ C)
    (hf0 : ∀ x ∈ C, 0 ≤ f x) (hg0 : ∀ x ∈ C, 0 ≤ g x)
    (hf_mono : MonotoneOn f C) (hg_mono : MonotoneOn g C)
    (hf_conv : ConvexOn ℝ C f) (hg_conv : ConvexOn ℝ C g) :
    ConvexOn ℝ C (fun x => f x * g x) := by
  refine ⟨hC, fun x hx y hy a b ha hb hab => ?_⟩
  have hfx : 0 ≤ f x := hf0 x hx
  have hfy : 0 ≤ f y := hf0 y hy
  have hgx : 0 ≤ g x := hg0 x hx
  have hgy : 0 ≤ g y := hg0 y hy
  have hf_le : f (a • x + b • y) ≤ a * f x + b * f y := by
    simpa [smul_eq_mul] using hf_conv.2 hx hy ha hb hab
  have hg_le : g (a • x + b • y) ≤ a * g x + b * g y := by
    simpa [smul_eq_mul] using hg_conv.2 hx hy ha hb hab
  have hxy_mem : a • x + b • y ∈ C := hC hx hy ha hb hab
  have hprod_le : f (a • x + b • y) * g (a • x + b • y) ≤
      (a * f x + b * f y) * (a * g x + b * g y) :=
    mul_le_mul hf_le hg_le (hg0 _ hxy_mem) (by positivity)
  have hcheb : 0 ≤ (f x - f y) * (g x - g y) := by
    rcases le_total x y with hle | hle
    · have h1 : f x ≤ f y := hf_mono hx hy hle
      have h2 : g x ≤ g y := hg_mono hx hy hle
      nlinarith
    · have h1 : f y ≤ f x := hf_mono hy hx hle
      have h2 : g y ≤ g x := hg_mono hy hx hle
      nlinarith
  have hid : a * (f x * g x) + b * (f y * g y) - (a * f x + b * f y) * (a * g x + b * g y) =
      a * b * ((f x - f y) * (g x - g y)) := by
    have ha' : a - a ^ 2 = a * b := by nlinarith
    have hb' : b - b ^ 2 = a * b := by nlinarith
    calc a * (f x * g x) + b * (f y * g y) - (a * f x + b * f y) * (a * g x + b * g y)
        = (a - a ^ 2) * (f x * g x) + (b - b ^ 2) * (f y * g y) -
            a * b * (f x * g y + f y * g x) := by ring
      _ = a * b * (f x * g x) + a * b * (f y * g y) - a * b * (f x * g y + f y * g x) := by
            rw [ha', hb']
      _ = a * b * ((f x - f y) * (g x - g y)) := by ring
  have hdiff : 0 ≤ a * b * ((f x - f y) * (g x - g y)) := mul_nonneg (mul_nonneg ha hb) hcheb
  simp only [smul_eq_mul] at hprod_le ⊢
  linarith

/-- Extending a function that is nonnegative, monotone, convex on `[c, ∞)` with `f c = 0`
by `0` on `(-∞, c]` produces a globally convex function on `ℝ`. -/
lemma convexOn_zero_left_extension {f : ℝ → ℝ} {c : ℝ}
    (hf0 : ∀ x, c ≤ x → 0 ≤ f x)
    (hfc : f c = 0)
    (hf_mono : MonotoneOn f (Set.Ici c))
    (hf_conv : ConvexOn ℝ (Set.Ici c) f) :
    ConvexOn ℝ Set.univ (fun x => if x ≤ c then 0 else f x) := by
  let g : ℝ → ℝ := fun x => if x ≤ c then 0 else f x
  have hg_nonneg : ∀ x, 0 ≤ g x := by
    intro x; dsimp [g]
    split_ifs with h
    · exact le_refl 0
    · exact hf0 x (le_of_not_ge h)
  have hg_eq_f : ∀ x, c ≤ x → g x = f x := by
    intro x hx; dsimp [g]
    split_ifs with h
    · have hxc : x = c := le_antisymm h hx
      rw [hxc, hfc]
    · rfl
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  change g (a * x + b * y) ≤ a * g x + b * g y
  by_cases hcomb : a * x + b * y ≤ c
  · have h0 : g (a * x + b * y) = 0 := by simp [g, hcomb]
    rw [h0]
    exact add_nonneg (mul_nonneg ha (hg_nonneg x)) (mul_nonneg hb (hg_nonneg y))
  · push Not at hcomb
    let x' := max x c
    let y' := max y c
    have hx' : c ≤ x' := le_max_right x c
    have hy' : c ≤ y' := le_max_right y c
    have hcomb_le : a * x + b * y ≤ a * x' + b * y' :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left x c) ha)
        (mul_le_mul_of_nonneg_left (le_max_left y c) hb)
    have hcomb'_ge : c ≤ a * x' + b * y' := le_trans (le_of_lt hcomb) hcomb_le
    have hgx' : f x' = g x := by
      dsimp [x']
      rcases le_total x c with hxc | hcx
      · rw [max_eq_right hxc, hfc]; simp [g, hxc]
      · rw [max_eq_left hcx, hg_eq_f x hcx]
    have hgy' : f y' = g y := by
      dsimp [y']
      rcases le_total y c with hyc | hcy
      · rw [max_eq_right hyc, hfc]; simp [g, hyc]
      · rw [max_eq_left hcy, hg_eq_f y hcy]
    calc g (a * x + b * y) = f (a * x + b * y) := hg_eq_f _ (le_of_lt hcomb)
      _ ≤ f (a * x' + b * y') := hf_mono (le_of_lt hcomb) hcomb'_ge hcomb_le
      _ ≤ a * f x' + b * f y' := by
          simpa [smul_eq_mul] using hf_conv.2 hx' hy' ha hb hab
      _ = a * g x + b * g y := by rw [hgx', hgy']

/-- Truncated real falling factorial `x(x-1)⋯(x-s+1)` for `x ≥ s - 1`, and `0` below. -/
noncomputable def fallingFactReal (s : ℕ) (x : ℝ) : ℝ :=
  if x ≤ (s : ℝ) - 1 then 0 else ∏ k ∈ Finset.range s, (x - (k : ℝ))

lemma fallingFactReal_natCast (s d : ℕ) (hs : 1 ≤ s) :
    fallingFactReal s (d : ℝ) = ((d.descFactorial s : ℕ) : ℝ) := by
  dsimp [fallingFactReal]
  split_ifs with h
  · have hlt : d < s := by
      have h1 : (d : ℝ) < (s : ℝ) := by linarith
      exact_mod_cast h1
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr hlt, Nat.cast_zero]
  · push Not at h
    have hge : s ≤ d := by
      have h1 : (s - 1 : ℕ) < d := by
        have hcast : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by simpa using Nat.cast_sub (R := ℝ) hs
        rw [← hcast] at h
        exact_mod_cast h
      omega
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hk_lt : k < s := Finset.mem_range.mp hk
    rw [Nat.cast_sub (le_trans (le_of_lt hk_lt) hge)]

lemma convexOn_fallingFactReal (s : ℕ) (hs : 1 ≤ s) :
    ConvexOn ℝ Set.univ (fallingFactReal s) := by
  have hpoly : ∀ n : ℕ,
      (∀ x, (n : ℝ) - 1 ≤ x → 0 ≤ ∏ k ∈ Finset.range n, (x - (k : ℝ))) ∧
      MonotoneOn (fun x => ∏ k ∈ Finset.range n, (x - (k : ℝ))) (Set.Ici ((n : ℝ) - 1)) ∧
      ConvexOn ℝ (Set.Ici ((n : ℝ) - 1)) (fun x => ∏ k ∈ Finset.range n, (x - (k : ℝ))) := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun _ _ => by simp, fun _ _ _ _ _ => by simp, ?_⟩
      simpa using (convexOn_const (1 : ℝ) (convex_Ici ((0 : ℝ) - 1)))
    | succ m ih =>
      rcases ih with ⟨h0, hmono, hconv⟩
      have hsub : Set.Ici (((m + 1 : ℕ) : ℝ) - 1) ⊆ Set.Ici ((m : ℝ) - 1) := by
        intro x hx
        simp only [Set.mem_Ici, Nat.cast_succ] at hx ⊢
        linarith
      have hlin0 : ∀ x ∈ Set.Ici (((m + 1 : ℕ) : ℝ) - 1), 0 ≤ x - (m : ℝ) := by
        intro x hx; simp only [Set.mem_Ici, Nat.cast_succ] at hx; linarith
      have hlin_mono : MonotoneOn (fun x : ℝ => x - (m : ℝ)) (Set.Ici (((m + 1 : ℕ) : ℝ) - 1)) :=
        fun _ _ _ _ hle => sub_le_sub_right hle _
      have hlin_conv : ConvexOn ℝ (Set.Ici (((m + 1 : ℕ) : ℝ) - 1)) (fun x : ℝ => x - (m : ℝ)) := by
        refine ⟨convex_Ici _, fun x _ y _ a b _ _ hab => ?_⟩
        simp only [smul_eq_mul]; nlinarith
      have heq : (fun x : ℝ => ∏ k ∈ Finset.range (m + 1), (x - (k : ℝ))) =
          fun x => (∏ k ∈ Finset.range m, (x - (k : ℝ))) * (x - (m : ℝ)) := by
        ext x; rw [Finset.prod_range_succ]
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        rw [Finset.prod_range_succ]
        exact mul_nonneg (h0 x (hsub hx)) (hlin0 x hx)
      · rw [heq]
        intro x hx y hy hle
        exact mul_le_mul (hmono (hsub hx) (hsub hy) hle) (hlin_mono hx hy hle)
          (hlin0 x hx) (h0 y (hsub hy))
      · rw [heq]
        exact convexOn_mul_of_nonneg_monotone (convex_Ici _)
          (fun x hx => h0 x (hsub hx)) hlin0
          (hmono.mono hsub) hlin_mono
          (hconv.subset hsub (convex_Ici _)) hlin_conv
  rcases hpoly s with ⟨h0, hmono, hconv⟩
  have hzero : ∏ k ∈ Finset.range s, (((s : ℝ) - 1) - (k : ℝ)) = 0 := by
    refine Finset.prod_eq_zero (i := s - 1) (Finset.mem_range.mpr (by omega)) ?_
    rw [Nat.cast_sub hs, Nat.cast_one, sub_self]
  exact convexOn_zero_left_extension h0 hzero hmono hconv

/-- **Bipartite Kővári–Sós–Turán Double-Counting Binomial Bound**:
If a bipartite relation `adj : U → V → Prop` has no `K_{s, t}`, then
`∑ v : V, (deg_U v).choose s ≤ (t - 1) * (card U).choose s`. -/
theorem kst_bipartite_double_count
    {U V : Type*} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
    (adj : U → V → Prop) [DecidableRel adj]
    (s t : ℕ) (ht : 1 ≤ t)
    (hfree : ∀ (A : Finset U) (B : Finset V), A.card = s → B.card = t →
      ∃ u ∈ A, ∃ v ∈ B, ¬ adj u v) :
    ∑ v : V, ((Finset.univ.filter (fun u : U => adj u v)).card).choose s ≤
      (t - 1) * (Fintype.card U).choose s := by
  have hlhs : ∑ v : V, ((Finset.univ.filter (fun u : U => adj u v)).card).choose s =
      ∑ A ∈ Finset.powersetCard s (Finset.univ : Finset U),
        (Finset.univ.filter (fun v : V => ∀ u ∈ A, adj u v)).card := by
    calc ∑ v : V, ((Finset.univ.filter (fun u : U => adj u v)).card).choose s
        = ∑ v : V, (Finset.powersetCard s (Finset.univ.filter (fun u : U => adj u v))).card := by
          refine Finset.sum_congr rfl fun v _ => (Finset.card_powersetCard _ _).symm
      _ = ∑ v : V, ∑ A ∈ Finset.powersetCard s (Finset.univ : Finset U),
            if ∀ u ∈ A, adj u v then 1 else 0 := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [Finset.sum_boole, Nat.cast_id]
          congr 1
          ext A
          simp only [Finset.mem_powersetCard, Finset.mem_filter, Finset.subset_iff,
            Finset.mem_univ, true_and]
          tauto
      _ = ∑ A ∈ Finset.powersetCard s (Finset.univ : Finset U),
            ∑ v : V, if ∀ u ∈ A, adj u v then 1 else 0 := Finset.sum_comm
      _ = ∑ A ∈ Finset.powersetCard s (Finset.univ : Finset U),
            (Finset.univ.filter (fun v : V => ∀ u ∈ A, adj u v)).card := by
          refine Finset.sum_congr rfl fun A _ => ?_
          rw [Finset.sum_boole, Nat.cast_id]
  rw [hlhs]
  have hle : ∀ A ∈ Finset.powersetCard s (Finset.univ : Finset U),
      (Finset.univ.filter (fun v : V => ∀ u ∈ A, adj u v)).card ≤ t - 1 := by
    intro A hA
    have hAcard : A.card = s := (Finset.mem_powersetCard.mp hA).2
    by_contra hgt
    have hge : t ≤ (Finset.univ.filter (fun v : V => ∀ u ∈ A, adj u v)).card := by omega
    obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hge
    obtain ⟨u, huA, v, hvB, hnadj⟩ := hfree A B hAcard hBcard
    have hv := (Finset.mem_filter.mp (hBsub hvB)).2
    exact hnadj (hv u huA)
  calc ∑ A ∈ Finset.powersetCard s (Finset.univ : Finset U),
          (Finset.univ.filter (fun v : V => ∀ u ∈ A, adj u v)).card
      ≤ ∑ _A ∈ Finset.powersetCard s (Finset.univ : Finset U), (t - 1) :=
        Finset.sum_le_sum hle
    _ = (Finset.powersetCard s (Finset.univ : Finset U)).card * (t - 1) := by
        simp [Finset.sum_const]
    _ = (t - 1) * (Fintype.card U).choose s := by
        rw [Finset.card_powersetCard, Finset.card_univ, mul_comm]

/-- **Bipartite Kővári–Sós–Turán Theorem (`ex(m, n; K_{s,t})`)**:
For any `K_{s, t}`-free bipartite graph on `(U, V)` (`s ≥ 1`, `t ≥ 1`), the number of edges
`E = ∑ v : V, |{u ∈ U | adj u v}|` satisfies
`E ≤ (t - 1)^(1/s) * |U| * |V|^(1 - 1/s) + (s - 1) * |V|`. -/
theorem kovari_sos_turan_bipartite
    {U V : Type*} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
    (adj : U → V → Prop) [DecidableRel adj]
    (s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hfree : ∀ (A : Finset U) (B : Finset V), A.card = s → B.card = t →
      ∃ u ∈ A, ∃ v ∈ B, ¬ adj u v) :
    ((∑ v : V, (Finset.univ.filter (fun u : U => adj u v)).card : ℕ) : ℝ) ≤
      ((t - 1 : ℕ) : ℝ) ^ (1 / (s : ℝ)) * (Fintype.card U : ℝ) *
        (Fintype.card V : ℝ) ^ (1 - 1 / (s : ℝ)) +
      ((s - 1 : ℕ) : ℝ) * (Fintype.card V : ℝ) := by
  set m := Fintype.card U
  set n := Fintype.card V
  set E := ∑ v : V, (Finset.univ.filter (fun u : U => adj u v)).card
  have hs_pos : (0 : ℝ) < (s : ℝ) := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hs)
  rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
  · have : IsEmpty V := Fintype.card_eq_zero_iff.mp hn0
    have hE0 : E = 0 := by simp [E]
    rw [hE0, hn0]
    simp only [Nat.cast_zero, mul_zero, add_zero]
    positivity
  · have hn_rpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
    have hsub_s : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by simpa using Nat.cast_sub (R := ℝ) hs
    by_cases hsmall : (E : ℝ) / (n : ℝ) ≤ (s : ℝ) - 1
    · have hE_le : (E : ℝ) ≤ ((s - 1 : ℕ) : ℝ) * (n : ℝ) := by
        rw [hsub_s]
        exact (div_le_iff₀ hn_rpos).mp hsmall
      have hterm_nonneg : 0 ≤ ((t - 1 : ℕ) : ℝ) ^ (1 / (s : ℝ)) * (m : ℝ) *
          (n : ℝ) ^ (1 - 1 / (s : ℝ)) := by positivity
      linarith
    · push Not at hsmall
      -- Apply Jensen to the convex function fallingFactReal s on V
      have hconv := convexOn_fallingFactReal s hs
      have hw_nonneg : ∀ v ∈ (Finset.univ : Finset V), (0 : ℝ) ≤ 1 / (n : ℝ) :=
        fun _ _ => by positivity
      have hw_sum : ∑ _v ∈ (Finset.univ : Finset V), (1 / (n : ℝ)) = 1 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp [ne_of_gt hn_rpos]; rfl
      have hjensen := hconv.map_sum_le hw_nonneg hw_sum (fun _ _ => Set.mem_univ _)
        (p := fun v : V => ((Finset.univ.filter (fun u : U => adj u v)).card : ℝ))
      have havg : ∑ v : V, (1 / (n : ℝ)) •
          ((Finset.univ.filter (fun u : U => adj u v)).card : ℝ) = (E : ℝ) / (n : ℝ) := by
        simp only [smul_eq_mul, ← Finset.mul_sum, E, Nat.cast_sum]
        ring
      rw [havg] at hjensen
      have hrhs_jensen : ∑ v : V, (1 / (n : ℝ)) •
          fallingFactReal s ((Finset.univ.filter (fun u : U => adj u v)).card : ℝ) ≤
          ((t - 1 : ℕ) : ℝ) * (m : ℝ) ^ s / (n : ℝ) := by
        simp only [smul_eq_mul, ← Finset.mul_sum]
        have hdc := kst_bipartite_double_count adj s t ht hfree
        have hdesc_sum : ∑ v : V,
            fallingFactReal s ((Finset.univ.filter (fun u : U => adj u v)).card : ℝ) =
            ((s.factorial * ∑ v : V,
              ((Finset.univ.filter (fun u : U => adj u v)).card).choose s : ℕ) : ℝ) := by
          simp_rw [fallingFactReal_natCast s _ hs, Nat.descFactorial_eq_factorial_mul_choose]
          norm_cast
          rw [← Finset.mul_sum]
        rw [hdesc_sum]
        have hnat_bound : s.factorial * ∑ v : V,
            ((Finset.univ.filter (fun u : U => adj u v)).card).choose s ≤
            (t - 1) * m ^ s := by
          calc s.factorial * ∑ v : V,
                ((Finset.univ.filter (fun u : U => adj u v)).card).choose s
              ≤ s.factorial * ((t - 1) * m.choose s) := Nat.mul_le_mul_left _ hdc
            _ = (t - 1) * (s.factorial * m.choose s) := by ring
            _ = (t - 1) * m.descFactorial s := by rw [← Nat.descFactorial_eq_factorial_mul_choose]
            _ ≤ (t - 1) * m ^ s := Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow m s)
        have hreal_bound : ((s.factorial * ∑ v : V,
            ((Finset.univ.filter (fun u : U => adj u v)).card).choose s : ℕ) : ℝ) ≤
            ((t - 1 : ℕ) : ℝ) * (m : ℝ) ^ s := by
          exact_mod_cast hnat_bound
        calc (1 / (n : ℝ)) * _ ≤ (1 / (n : ℝ)) * (((t - 1 : ℕ) : ℝ) * (m : ℝ) ^ s) :=
              mul_le_mul_of_nonneg_left hreal_bound (by positivity)
          _ = ((t - 1 : ℕ) : ℝ) * (m : ℝ) ^ s / (n : ℝ) := by ring
      have hlow_pow : ((E : ℝ) / (n : ℝ) - ((s : ℝ) - 1)) ^ s ≤
          fallingFactReal s ((E : ℝ) / (n : ℝ)) := by
        dsimp [fallingFactReal]
        rw [if_neg (not_le.mpr hsmall)]
        have hconst : ((E : ℝ) / (n : ℝ) - ((s : ℝ) - 1)) ^ s =
            ∏ _k ∈ Finset.range s, ((E : ℝ) / (n : ℝ) - ((s : ℝ) - 1)) := by
          rw [Finset.prod_const, Finset.card_range]
        rw [hconst]
        refine Finset.prod_le_prod (fun _ _ => by linarith) fun k hk => ?_
        have hk_le : (k : ℝ) ≤ (s : ℝ) - 1 := by
          have hk' : k ≤ s - 1 := Nat.le_sub_one_of_lt (Finset.mem_range.mp hk)
          have hcast : ((k : ℕ) : ℝ) ≤ ((s - 1 : ℕ) : ℝ) := by exact_mod_cast hk'
          linarith [hsub_s]
        linarith
      have hpow_le : ((E : ℝ) / (n : ℝ) - ((s : ℝ) - 1)) ^ s ≤
          ((t - 1 : ℕ) : ℝ) * (m : ℝ) ^ s / (n : ℝ) :=
        le_trans hlow_pow (le_trans hjensen hrhs_jensen)
      have hbase_nonneg : 0 ≤ (E : ℝ) / (n : ℝ) - ((s : ℝ) - 1) := by linarith
      have hrpow := Real.rpow_le_rpow (pow_nonneg hbase_nonneg s) hpow_le
        (show 0 ≤ 1 / (s : ℝ) by positivity)
      have hlhs_rpow : (((E : ℝ) / (n : ℝ) - ((s : ℝ) - 1)) ^ s) ^ (1 / (s : ℝ)) =
          (E : ℝ) / (n : ℝ) - ((s : ℝ) - 1) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hbase_nonneg]
        have : (s : ℝ) * (1 / (s : ℝ)) = 1 := by field_simp [ne_of_gt hs_pos]
        rw [this, Real.rpow_one]
      have hrhs_rpow : (((t - 1 : ℕ) : ℝ) * (m : ℝ) ^ s / (n : ℝ)) ^ (1 / (s : ℝ)) =
          ((t - 1 : ℕ) : ℝ) ^ (1 / (s : ℝ)) * (m : ℝ) / (n : ℝ) ^ (1 / (s : ℝ)) := by
        rw [Real.div_rpow (by positivity) (le_of_lt hn_rpos),
          Real.mul_rpow (by positivity) (by positivity),
          ← Real.rpow_natCast (m : ℝ) s, ← Real.rpow_mul (Nat.cast_nonneg m)]
        have : (s : ℝ) * (1 / (s : ℝ)) = 1 := by field_simp [ne_of_gt hs_pos]
        rw [this, Real.rpow_one]
      rw [hlhs_rpow, hrhs_rpow] at hrpow
      have hmul := mul_le_mul_of_nonneg_right hrpow (le_of_lt hn_rpos)
      have hn_pow : (n : ℝ) / (n : ℝ) ^ (1 / (s : ℝ)) = (n : ℝ) ^ (1 - 1 / (s : ℝ)) := by
        rw [Real.rpow_sub hn_rpos, Real.rpow_one]
      have hlhs_mul : ((E : ℝ) / (n : ℝ) - ((s : ℝ) - 1)) * (n : ℝ) =
          (E : ℝ) - ((s - 1 : ℕ) : ℝ) * (n : ℝ) := by
        rw [hsub_s]; field_simp [ne_of_gt hn_rpos]
      have hrhs_mul : (((t - 1 : ℕ) : ℝ) ^ (1 / (s : ℝ)) * (m : ℝ) / (n : ℝ) ^ (1 / (s : ℝ))) *
          (n : ℝ) = ((t - 1 : ℕ) : ℝ) ^ (1 / (s : ℝ)) * (m : ℝ) * (n : ℝ) ^ (1 - 1 / (s : ℝ)) := by
        rw [← hn_pow]; ring
      rw [hlhs_mul, hrhs_mul] at hmul
      linarith

/-- **Kővári–Sós–Turán Theorem for Simple Graphs (`ex(n; K_{s,t})`)**:
For any `K_{s, t}`-free simple graph `G` on a finite vertex type `V` (`n = |V|`, `s ≥ 1`, `t ≥ 1`),
`e(G) ≤ (1/2) * (t - 1)^(1/s) * n^(2 - 1/s) + ((s - 1)/2) * n`. -/
theorem kovari_sos_turan_simpleGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hfree : ∀ (A B : Finset V), Disjoint A B → A.card = s → B.card = t →
      ∃ u ∈ A, ∃ v ∈ B, ¬ G.Adj u v) :
    (G.edgeFinset.card : ℝ) ≤
      (1 / 2) * ((t - 1 : ℕ) : ℝ) ^ (1 / (s : ℝ)) *
        (Fintype.card V : ℝ) ^ (2 - 1 / (s : ℝ)) +
      ((s - 1 : ℕ) : ℝ) / 2 * (Fintype.card V : ℝ) := by
  set n := Fintype.card V
  have hbip_free : ∀ (A B : Finset V), A.card = s → B.card = t →
      ∃ u ∈ A, ∃ v ∈ B, ¬ G.Adj u v := by
    intro A B hA hB
    by_cases hdisj : Disjoint A B
    · exact hfree A B hdisj hA hB
    · rw [Finset.not_disjoint_iff] at hdisj
      rcases hdisj with ⟨u, huA, huB⟩
      exact ⟨u, huA, u, huB, G.loopless.irrefl u⟩
  have hkst := kovari_sos_turan_bipartite G.Adj s t hs ht hbip_free
  have hsum_deg : ∑ v : V, (Finset.univ.filter (fun u : V => G.Adj u v)).card =
      2 * G.edgeFinset.card := by
    rw [← G.sum_degrees_eq_twice_card_edges]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [SimpleGraph.degree]
    congr 1
    ext u
    simp [SimpleGraph.mem_neighborFinset, SimpleGraph.adj_comm]
  rw [hsum_deg, Nat.cast_mul, Nat.cast_ofNat] at hkst
  rcases Nat.eq_zero_or_pos n with hn0 | hn_pos
  · have : IsEmpty V := Fintype.card_eq_zero_iff.mp hn0
    have he0 : G.edgeFinset.card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro e he
      induction e using Sym2.ind with
      | _ u _ => exact IsEmpty.false u
    rw [he0, hn0]
    simp only [Nat.cast_zero, mul_zero, add_zero]
    positivity
  · have hn_rpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn_pos
    have hpow : (n : ℝ) * (n : ℝ) ^ (1 - 1 / (s : ℝ)) = (n : ℝ) ^ (2 - 1 / (s : ℝ)) := by
      conv_lhs => arg 1; rw [← Real.rpow_one (n : ℝ)]
      rw [← Real.rpow_add hn_rpos]
      congr 1; ring
    have hrew : ((t - 1 : ℕ) : ℝ) ^ (1 / (s : ℝ)) * (n : ℝ) * (n : ℝ) ^ (1 - 1 / (s : ℝ)) =
        ((t - 1 : ℕ) : ℝ) ^ (1 / (s : ℝ)) * (n : ℝ) ^ (2 - 1 / (s : ℝ)) := by
      rw [mul_assoc, hpow]
    rw [hrew] at hkst
    linarith

/-- **Kővári–Sós–Turán Theorem on `SimpleGraph (Fin n)`**: explicit `Fin n` specialization. -/
theorem kovari_sos_turan_fin
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hfree : ∀ (A B : Finset (Fin n)), Disjoint A B → A.card = s → B.card = t →
      ∃ u ∈ A, ∃ v ∈ B, ¬ G.Adj u v) :
    (G.edgeFinset.card : ℝ) ≤
      (1 / 2) * ((t - 1 : ℕ) : ℝ) ^ (1 / (s : ℝ)) * (n : ℝ) ^ (2 - 1 / (s : ℝ)) +
      ((s - 1 : ℕ) : ℝ) / 2 * (n : ℝ) := by
  simpa [Fintype.card_fin] using kovari_sos_turan_simpleGraph G s t hs ht hfree


/-! ## Section 4: Dependent Random Choice Lemma -/

/-- Common neighborhood of a subset `S ⊆ U` in `V` with respect to bipartite relation `adj`. -/
def bipartiteCommonNeighbors
    {U V : Type*} [Fintype V] (adj : U → V → Prop) [DecidableRel adj] (S : Finset U) :
    Finset V :=
  Finset.univ.filter (fun v : V => ∀ u ∈ S, adj u v)

/-- Number of `t`-tuples in `V` all of whose coordinates lie in `W : Finset V` is `W.card ^ t`. -/
lemma card_tuples_in_finset {V : Type*} [Fintype V] [DecidableEq V]
    (W : Finset V) (t : ℕ) :
    (Finset.univ.filter (fun T : Fin t → V => ∀ i : Fin t, T i ∈ W)).card = W.card ^ t := by
  have heq : (Finset.univ.filter (fun T : Fin t → V => ∀ i : Fin t, T i ∈ W)).card =
      Fintype.card {T : Fin t → V // ∀ i : Fin t, T i ∈ W} := by
    rw [Fintype.card_subtype]
  rw [heq]
  let e : {T : Fin t → V // ∀ i : Fin t, T i ∈ W} ≃ (Fin t → {v : V // v ∈ W}) :=
    { toFun := fun T i => ⟨T.1 i, T.2 i⟩
      invFun := fun f => ⟨fun i => (f i).1, fun i => (f i).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]

/-- Power function `x ↦ x ^ t` is convex on `[0, ∞)` for every `t : ℕ`. -/
lemma convexOn_pow_Ici (t : ℕ) : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => x ^ t) := by
  induction t with
  | zero => simpa using convexOn_const (1 : ℝ) (convex_Ici (0 : ℝ))
  | succ k ih =>
    have heq : (fun x : ℝ => x ^ (k + 1)) = fun x => x ^ k * x := by
      ext x; rw [pow_succ]
    rw [heq]
    exact convexOn_mul_of_nonneg_monotone (convex_Ici (0 : ℝ))
      (fun x hx => pow_nonneg hx k) (fun x hx => hx)
      (fun x hx y _ hxy => pow_le_pow_left₀ hx hxy k)
      (fun _ _ _ _ hxy => hxy)
      ih (convexOn_id (convex_Ici (0 : ℝ)))

/-- **Dependent Random Choice Lemma (General Bipartite Form)**:
For a bipartite graph `(U, V, adj)` with `n = |U| > 0`, `m = |V| > 0`, and `e` edges,
if `n * (e / (n * m))^t - (n choose r) * (b / m)^t ≥ a` (`r ≥ 1`), then there exists
`U' : Finset U` with `a ≤ U'.card` such that EVERY `r`-subset `S ⊆ U'` has at least `b`
common neighbors in `V`. -/
theorem dependent_random_choice_bipartite
    {U V : Type*} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
    (hU : Nonempty U) (hV : Nonempty V)
    (adj : U → V → Prop) [DecidableRel adj]
    (t r b : ℕ) (hr : 1 ≤ r) (a : ℝ)
    (hcond : a ≤ (Fintype.card U : ℝ) *
        (((∑ u : U, (Finset.univ.filter (adj u)).card : ℕ) : ℝ) /
          ((Fintype.card U : ℝ) * (Fintype.card V : ℝ))) ^ t -
      ((Fintype.card U).choose r : ℝ) * ((b : ℝ) / (Fintype.card V : ℝ)) ^ t) :
    ∃ U' : Finset U, a ≤ (U'.card : ℝ) ∧
      ∀ S ⊆ U', S.card = r → b ≤ (bipartiteCommonNeighbors adj S).card := by
  classical
  set n := Fintype.card U
  set m := Fintype.card V
  set e := ∑ u : U, (Finset.univ.filter (adj u)).card
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have : Nonempty (Fin t → V) := ⟨fun _ => Classical.choice hV⟩
  let μ := FinProbSpace.uniform (Fin t → V)
  let A : (Fin t → V) → Finset U := fun T =>
    Finset.univ.filter (fun u : U => ∀ i : Fin t, adj u (T i))
  let bad : Finset (Finset U) :=
    (Finset.powersetCard r (Finset.univ : Finset U)).filter
      (fun S => (bipartiteCommonNeighbors adj S).card < b)
  let Y : (Fin t → V) → ℕ := fun T => (bad.filter (fun S => S ⊆ A T)).card
  -- Step 1: Lower bound E[|A(T)|] via double counting + Jensen on x^t
  have hsumA : ∑ T : Fin t → V, (A T).card =
      ∑ u : U, ((Finset.univ.filter (adj u)).card) ^ t := by
    calc ∑ T : Fin t → V, (A T).card
        = ∑ T : Fin t → V, ∑ u : U, if ∀ i : Fin t, adj u (T i) then 1 else 0 := by
          refine Finset.sum_congr rfl fun T _ => ?_
          rw [Finset.sum_boole, Nat.cast_id]
      _ = ∑ u : U, ∑ T : Fin t → V, if ∀ i : Fin t, adj u (T i) then 1 else 0 := Finset.sum_comm
      _ = ∑ u : U, (Finset.univ.filter (fun T : Fin t → V =>
            ∀ i : Fin t, T i ∈ Finset.univ.filter (adj u))).card := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Finset.sum_boole, Nat.cast_id]
          congr 1; ext T; simp
      _ = ∑ u : U, ((Finset.univ.filter (adj u)).card) ^ t := by
          refine Finset.sum_congr rfl fun u _ => card_tuples_in_finset _ t
  have hEA : (n : ℝ) * ((e : ℝ) / ((n : ℝ) * (m : ℝ))) ^ t ≤
      μ.expect (fun T => ((A T).card : ℝ)) := by
    have hcard_mt : (Fintype.card (Fin t → V) : ℝ) = (m : ℝ) ^ t := by
      rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    have hconv := convexOn_pow_Ici t
    have hw_nonneg : ∀ _u ∈ (Finset.univ : Finset U), (0 : ℝ) ≤ 1 / (n : ℝ) :=
      fun _ _ => by positivity
    have hw_sum : ∑ _u ∈ (Finset.univ : Finset U), (1 / (n : ℝ)) = 1 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp [ne_of_gt hn_pos]; rfl
    have hjensen := hconv.map_sum_le hw_nonneg hw_sum
      (fun u _ => show (0 : ℝ) ≤ ((Finset.univ.filter (adj u)).card : ℝ) from Nat.cast_nonneg _)
    have havg : ∑ u : U, (1 / (n : ℝ)) • ((Finset.univ.filter (adj u)).card : ℝ) =
        (e : ℝ) / (n : ℝ) := by
      simp only [smul_eq_mul, ← Finset.mul_sum, e, Nat.cast_sum]
      ring
    rw [havg] at hjensen
    have hsum_pow : (n : ℝ) * ((e : ℝ) / (n : ℝ)) ^ t ≤
        ∑ u : U, ((Finset.univ.filter (adj u)).card : ℝ) ^ t := by
      simp only [smul_eq_mul, ← Finset.mul_sum] at hjensen
      have hmul := mul_le_mul_of_nonneg_left hjensen (le_of_lt hn_pos)
      rw [← mul_assoc, mul_one_div_cancel (ne_of_gt hn_pos), one_mul] at hmul
      exact hmul
    have hEA_eq : μ.expect (fun T => ((A T).card : ℝ)) =
        (∑ u : U, ((Finset.univ.filter (adj u)).card : ℝ) ^ t) / (m : ℝ) ^ t := by
      dsimp only [FinProbSpace.expect, μ, FinProbSpace.uniform]
      rw [hcard_mt, ← Finset.mul_sum]
      have hcast : ∑ T : Fin t → V, ((A T).card : ℝ) =
          ∑ u : U, ((Finset.univ.filter (adj u)).card : ℝ) ^ t := by
        exact_mod_cast hsumA
      rw [hcast, one_div_mul_eq_div]
    rw [hEA_eq]
    have hpow_div : (n : ℝ) * ((e : ℝ) / ((n : ℝ) * (m : ℝ))) ^ t =
        ((n : ℝ) * ((e : ℝ) / (n : ℝ)) ^ t) / (m : ℝ) ^ t := by
      have : (e : ℝ) / ((n : ℝ) * (m : ℝ)) = ((e : ℝ) / (n : ℝ)) / (m : ℝ) := by
        field_simp [ne_of_gt hn_pos, ne_of_gt hm_pos]
      rw [this, div_pow]; ring
    rw [hpow_div]
    exact div_le_div_of_nonneg_right hsum_pow (by positivity)
  -- Step 2: Upper bound E[Y(T)]
  have hsumY : ∑ T : Fin t → V, Y T ≤ n.choose r * b ^ t := by
    have hY_eq : ∑ T : Fin t → V, Y T =
        ∑ S ∈ bad, ((bipartiteCommonNeighbors adj S).card) ^ t := by
      calc ∑ T : Fin t → V, Y T
          = ∑ T : Fin t → V, ∑ S ∈ bad, if S ⊆ A T then 1 else 0 := by
            refine Finset.sum_congr rfl fun T _ => ?_
            rw [Finset.sum_boole, Nat.cast_id]
        _ = ∑ S ∈ bad, ∑ T : Fin t → V, if S ⊆ A T then 1 else 0 := Finset.sum_comm
        _ = ∑ S ∈ bad, (Finset.univ.filter (fun T : Fin t → V =>
              ∀ i : Fin t, T i ∈ bipartiteCommonNeighbors adj S)).card := by
            refine Finset.sum_congr rfl fun S _ => ?_
            rw [Finset.sum_boole, Nat.cast_id]
            congr 1; ext T
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.subset_iff,
              A, bipartiteCommonNeighbors]
            exact ⟨fun h i u hu => h hu i, fun h u hu i => h i u hu⟩
        _ = ∑ S ∈ bad, ((bipartiteCommonNeighbors adj S).card) ^ t := by
            refine Finset.sum_congr rfl fun S _ => card_tuples_in_finset _ t
    rw [hY_eq]
    calc ∑ S ∈ bad, ((bipartiteCommonNeighbors adj S).card) ^ t
        ≤ ∑ _S ∈ bad, b ^ t := by
          refine Finset.sum_le_sum fun S hS => ?_
          have hlt : (bipartiteCommonNeighbors adj S).card < b := (Finset.mem_filter.mp hS).2
          exact Nat.pow_le_pow_left (le_of_lt hlt) t
      _ = bad.card * b ^ t := by simp [Finset.sum_const]
      _ ≤ n.choose r * b ^ t := by
          refine Nat.mul_le_mul_right _ ?_
          calc bad.card ≤ (Finset.powersetCard r (Finset.univ : Finset U)).card :=
                Finset.card_filter_le _ _
            _ = n.choose r := by rw [Finset.card_powersetCard, Finset.card_univ]
  have hEY : μ.expect (fun T => (Y T : ℝ)) ≤ (n.choose r : ℝ) * ((b : ℝ) / (m : ℝ)) ^ t := by
    have hcard_mt : (Fintype.card (Fin t → V) : ℝ) = (m : ℝ) ^ t := by
      rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    simp only [FinProbSpace.expect, μ, FinProbSpace.uniform, hcard_mt, ← Finset.mul_sum]
    have hreal : ∑ T : Fin t → V, (Y T : ℝ) ≤ (n.choose r : ℝ) * (b : ℝ) ^ t := by
      exact_mod_cast hsumY
    calc (1 / (m : ℝ) ^ t) * ∑ T : Fin t → V, (Y T : ℝ)
        ≤ (1 / (m : ℝ) ^ t) * ((n.choose r : ℝ) * (b : ℝ) ^ t) :=
          mul_le_mul_of_nonneg_left hreal (by positivity)
      _ = (n.choose r : ℝ) * ((b : ℝ) / (m : ℝ)) ^ t := by rw [div_pow]; ring
  -- Step 3: Probabilistic method + alteration (delete one vertex per bad r-subset in A(T₀))
  have hEdiff : a ≤ μ.expect (fun T => ((A T).card : ℝ) - (Y T : ℝ)) := by
    rw [μ.expect_sub]
    linarith
  obtain ⟨T₀, hT₀⟩ := μ.exists_ge_expect (fun T => ((A T).card : ℝ) - (Y T : ℝ))
  have hT₀_ge : a ≤ ((A T₀).card : ℝ) - (Y T₀ : ℝ) := le_trans hEdiff hT₀
  let badIn := bad.filter (fun S => S ⊆ A T₀)
  have hbad_ne : ∀ S ∈ badIn, S.Nonempty := by
    intro S hS
    have hcard_r : S.card = r :=
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1).2
    exact Finset.card_pos.mp (by omega)
  let rep : Finset U → U := fun S =>
    if h : S.Nonempty then Classical.choose h else Classical.choice hU
  have hrep_mem : ∀ S ∈ badIn, rep S ∈ S := by
    intro S hS
    have hne := hbad_ne S hS
    simp only [rep, dif_pos hne]
    exact Classical.choose_spec hne
  let D : Finset U := badIn.image rep
  let U' : Finset U := A T₀ \ D
  refine ⟨U', ?_, ?_⟩
  · have hD_le : D.card ≤ Y T₀ := Finset.card_image_le
    have hU'_ge : (A T₀).card - D.card ≤ U'.card := Finset.le_card_sdiff D (A T₀)
    have hcast_le : ((A T₀).card : ℝ) - (Y T₀ : ℝ) ≤ (U'.card : ℝ) := by
      have h1 : (A T₀).card ≤ U'.card + Y T₀ := by omega
      have h2 : ((A T₀).card : ℝ) ≤ (U'.card : ℝ) + (Y T₀ : ℝ) := by exact_mod_cast h1
      linarith
    exact le_trans hT₀_ge hcast_le
  · intro S hSU' hScard
    by_contra hlt
    push Not at hlt
    have hS_bad : S ∈ bad := by
      simp only [bad, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
      exact ⟨hScard, hlt⟩
    have hS_in : S ∈ badIn := by
      simp only [badIn, Finset.mem_filter]
      exact ⟨hS_bad, Finset.Subset.trans hSU' Finset.sdiff_subset⟩
    have hrep_in_S : rep S ∈ S := hrep_mem S hS_in
    have hrep_in_D : rep S ∈ D := Finset.mem_image.mpr ⟨S, hS_in, rfl⟩
    exact (Finset.mem_sdiff.mp (hSU' hrep_in_S)).2 hrep_in_D

/-- **Dependent Random Choice Lemma (`SimpleGraph`, General `r`-Subsets)**:
For a `SimpleGraph V` on `n = |V| > 0` vertices with `e = G.edgeFinset.card` edges,
if `n * (2e / n^2)^t - (n choose r) * (b / n)^t ≥ a` (`r ≥ 1`), then there exists
`U' : Finset V` with `a ≤ U'.card` such that EVERY `r`-subset `S ⊆ U'` has at least `b`
common neighbors in `G`. -/
theorem dependent_random_choice_simpleGraph
    {V : Type*} [Fintype V] [DecidableEq V] (hV : Nonempty V)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t r b : ℕ) (hr : 1 ≤ r) (a : ℝ)
    (hcond : a ≤ (Fintype.card V : ℝ) *
        ((2 * (G.edgeFinset.card : ℝ)) / ((Fintype.card V : ℝ) * (Fintype.card V : ℝ))) ^ t -
      ((Fintype.card V).choose r : ℝ) * ((b : ℝ) / (Fintype.card V : ℝ)) ^ t) :
    ∃ U' : Finset V, a ≤ (U'.card : ℝ) ∧
      ∀ S ⊆ U', S.card = r → b ≤ (Finset.univ.filter (fun v : V => ∀ u ∈ S, G.Adj u v)).card := by
  have hsum : ∑ u : V, (Finset.univ.filter (G.Adj u)).card = 2 * G.edgeFinset.card := by
    rw [← G.sum_degrees_eq_twice_card_edges]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [SimpleGraph.degree]
    congr 1; ext v; simp [SimpleGraph.mem_neighborFinset]
  have hcond' : a ≤ (Fintype.card V : ℝ) *
      (((∑ u : V, (Finset.univ.filter (G.Adj u)).card : ℕ) : ℝ) /
        ((Fintype.card V : ℝ) * (Fintype.card V : ℝ))) ^ t -
    ((Fintype.card V).choose r : ℝ) * ((b : ℝ) / (Fintype.card V : ℝ)) ^ t := by
    rw [hsum, Nat.cast_mul, Nat.cast_ofNat]
    exact hcond
  obtain ⟨U', hU'card, hU'⟩ := dependent_random_choice_bipartite hV hV G.Adj t r b hr a hcond'
  refine ⟨U', hU'card, fun S hS hSc => ?_⟩
  convert hU' S hS hSc using 2
  ext v; simp [bipartiteCommonNeighbors]

/-- **Dependent Random Choice Lemma (`SimpleGraph`, Pairs `r = 2` Specialization)**:
Existence of a large subset `U' ⊆ V` in which every pair of distinct vertices has at least `b`
common neighbors. -/
theorem dependent_random_choice_pairs
    {V : Type*} [Fintype V] [DecidableEq V] (hV : Nonempty V)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (t b : ℕ) (a : ℝ)
    (hcond : a ≤ (Fintype.card V : ℝ) *
        ((2 * (G.edgeFinset.card : ℝ)) / ((Fintype.card V : ℝ) * (Fintype.card V : ℝ))) ^ t -
      ((Fintype.card V).choose 2 : ℝ) * ((b : ℝ) / (Fintype.card V : ℝ)) ^ t) :
    ∃ U' : Finset V, a ≤ (U'.card : ℝ) ∧
      ∀ u ∈ U', ∀ v ∈ U', u ≠ v →
        b ≤ (Finset.univ.filter (fun w : V => G.Adj u w ∧ G.Adj v w)).card := by
  obtain ⟨U', hU'card, hU'⟩ := dependent_random_choice_simpleGraph hV G t 2 b (by omega) a hcond
  refine ⟨U', hU'card, fun u hu v hv huv => ?_⟩
  have hsub : ({u, v} : Finset V) ⊆ U' := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hcard : ({u, v} : Finset V).card = 2 := Finset.card_pair huv
  have hcn := hU' {u, v} hsub hcard
  convert hcn using 2
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  exact ⟨fun ⟨h1, h2⟩ x hx => by rcases hx with rfl | rfl <;> assumption,
    fun h => ⟨h u (Or.inl rfl), h v (Or.inr rfl)⟩⟩


/-! ## Section 5: Probabilistic Crossing Lemma, Caro–Wei, Turán, & Hypergraph Supersaturation -/

/-! ### 5A. Probabilistic Crossing Lemma (`e ≥ 4v ⇒ cr ≥ e³ / (64 v²)`) -/

/-- A proper (crossing-minimal / straight-line) topological drawing of a finite simple graph `G`
in the plane, represented by its finite set of crossing edge-pairs:
1. Every crossing `c ∈ crossings` is an unordered pair `s(e₁, e₂)` of vertex-disjoint edges of `G`.
2. Every crossing-free subset `F` of edges supported on a vertex set `S` obeys Euler's planar
   bound `|F| ≤ 3 * |S|`. -/
structure ProperGraphDrawing {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  crossings : Finset (Sym2 (Sym2 V))
  crossings_edges : ∀ c ∈ crossings, ∃ e₁ ∈ G.edgeFinset, ∃ e₂ ∈ G.edgeFinset,
    c = s(e₁, e₂) ∧ ∀ u : V, u ∈ e₁ → u ∉ e₂
  planar_bound : ∀ (S : Finset V) (F : Finset (Sym2 V)),
    F ⊆ G.edgeFinset →
    (∀ e ∈ F, ∀ u ∈ e, u ∈ S) →
    (∀ e₁ ∈ F, ∀ e₂ ∈ F, s(e₁, e₂) ∉ crossings) →
    F.card ≤ 3 * S.card

/-- Non-vacuity witness: every planar graph with `|E(G)| ≤ 3|S|` on every subset `S`
(in particular `⊥ : SimpleGraph V`) admits a `ProperGraphDrawing` with `0` crossings. -/
def ProperGraphDrawing.ofBot {V : Type*} [Fintype V] [DecidableEq V] :
    ProperGraphDrawing (⊥ : SimpleGraph V) where
  crossings := ∅
  crossings_edges := fun _ hc => absurd hc (Finset.notMem_empty _)
  planar_bound := fun _ F hF _ _ => by
    have hFe : F = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun e he => by
      have hmem := hF he
      simp [SimpleGraph.mem_edgeFinset] at hmem
    rw [hFe, Finset.card_empty]
    exact Nat.zero_le _

/-- Deleting one edge from each crossing pair yields the linear crossing bound on every
induced subgraph `G[S]`: `|E(G[S])| ≤ 3 |S| + cr(G[S])`. -/
theorem ProperGraphDrawing.induced_linear_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (D : ProperGraphDrawing G) (S : Finset V) :
    (G.edgeFinset.filter (fun e => ∀ u ∈ e, u ∈ S)).card ≤
      3 * S.card + (D.crossings.filter (fun c => ∀ e ∈ c, ∀ u ∈ e, u ∈ S)).card := by
  have hgen : ∀ (k : ℕ) (F : Finset (Sym2 V)),
      F ⊆ G.edgeFinset →
      (∀ e ∈ F, ∀ u ∈ e, u ∈ S) →
      (D.crossings.filter (fun c => ∀ e ∈ c, e ∈ F)).card = k →
      F.card ≤ 3 * S.card + k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro F hFG hFS hk
      rcases Nat.eq_zero_or_pos k with rfl | hk_pos
      · rw [add_zero]
        refine D.planar_bound S F hFG hFS fun e₁ he₁ e₂ he₂ hcross => ?_
        have hmem : s(e₁, e₂) ∈ D.crossings.filter (fun c => ∀ e ∈ c, e ∈ F) := by
          rw [Finset.mem_filter]
          refine ⟨hcross, fun e he => ?_⟩
          rw [Sym2.mem_iff] at he
          rcases he with rfl | rfl <;> assumption
        have hpos : 0 < (D.crossings.filter (fun c => ∀ e ∈ c, e ∈ F)).card :=
          Finset.card_pos.mpr ⟨s(e₁, e₂), hmem⟩
        omega
      · have hne : (D.crossings.filter (fun c => ∀ e ∈ c, e ∈ F)).Nonempty :=
          Finset.card_pos.mp (hk.symm ▸ hk_pos)
        rcases hne with ⟨c, hc⟩
        rw [Finset.mem_filter] at hc
        rcases D.crossings_edges c hc.1 with ⟨e₁, _, e₂, _, rfl, _⟩
        have he₁F : e₁ ∈ F := hc.2 e₁ (Sym2.mem_mk_left e₁ e₂)
        let F' := F.erase e₁
        have hF'sub : F' ⊆ F := Finset.erase_subset e₁ F
        have hcross_lt : (D.crossings.filter (fun c => ∀ e ∈ c, e ∈ F')).card < k := by
          rw [← hk]
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_subset_ne]
          refine ⟨fun x hx => ?_, fun heq => ?_⟩
          · rw [Finset.mem_filter] at hx ⊢
            exact ⟨hx.1, fun e he => hF'sub (hx.2 e he)⟩
          · have hcin : s(e₁, e₂) ∈ D.crossings.filter (fun c => ∀ e ∈ c, e ∈ F') := by
              rw [heq, Finset.mem_filter]
              exact hc
            have he₁F' : e₁ ∈ F' := (Finset.mem_filter.mp hcin).2 e₁ (Sym2.mem_mk_left e₁ e₂)
            exact (Finset.notMem_erase e₁ F) he₁F'
        have hih := ih _ hcross_lt F' (Finset.Subset.trans hF'sub hFG)
          (fun e he => hFS e (hF'sub he)) rfl
        have hcardF : F'.card + 1 = F.card := Finset.card_erase_add_one he₁F
        omega
  have hfilter_eq : D.crossings.filter
      (fun c => ∀ e ∈ c, e ∈ G.edgeFinset.filter (fun e => ∀ u ∈ e, u ∈ S)) =
      D.crossings.filter (fun c => ∀ e ∈ c, ∀ u ∈ e, u ∈ S) := by
    ext c
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hc, h⟩
      exact ⟨hc, fun e he => (h e he).2⟩
    · rintro ⟨hc, h⟩
      refine ⟨hc, fun e he => ⟨?_, h e he⟩⟩
      rcases D.crossings_edges c hc with ⟨e₁, he₁, e₂, he₂, rfl, _⟩
      rw [Sym2.mem_iff] at he
      rcases he with rfl | rfl <;> assumption
  have := hgen _ (G.edgeFinset.filter (fun e => ∀ u ∈ e, u ∈ S))
    (Finset.filter_subset _ _) (fun e he => (Finset.mem_filter.mp he).2) rfl
  rwa [hfilter_eq] at this

/-- Under i.i.d. `Bernoulli(p)` vertex sampling on `V`, the probability that all vertices in
`A : Finset V` are sampled is `p ^ A.card`. -/
lemma expect_bernoulli_subset_indicator
    {V : Type*} [Fintype V] [DecidableEq V]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (A : Finset V) :
    (FinProbSpace.prod (fun _ : V => FinProbSpace.bernoulli p hp0 hp1)).expect
      (fun ω => if ∀ u ∈ A, ω u = true then (1 : ℝ) else 0) = p ^ A.card := by
  let f : ∀ _u : V, Bool → ℝ := fun u b => if u ∈ A then (if b = true then 1 else 0) else 1
  have hprod_eq : ∀ ω : V → Bool,
      (if ∀ u ∈ A, ω u = true then (1 : ℝ) else 0) = ∏ u : V, f u (ω u) := by
    intro ω
    by_cases hA : ∀ u ∈ A, ω u = true
    · rw [if_pos hA]
      symm
      refine Finset.prod_eq_one fun u _ => ?_
      dsimp [f]
      split_ifs with hu hω
      · rfl
      · exact absurd (hA u hu) hω
      · rfl
    · rw [if_neg hA]
      push Not at hA
      rcases hA with ⟨u₀, hu₀A, hu₀f⟩
      symm
      refine Finset.prod_eq_zero (Finset.mem_univ u₀) ?_
      simp [f, hu₀A, hu₀f]
  simp_rw [hprod_eq]
  rw [FinProbSpace.expect_prod (fun _ : V => FinProbSpace.bernoulli p hp0 hp1) f]
  have hcoord : ∀ u : V,
      (FinProbSpace.bernoulli p hp0 hp1).expect (f u) = if u ∈ A then p else 1 := by
    intro u
    by_cases hu : u ∈ A
    · simp [FinProbSpace.expect, FinProbSpace.bernoulli, f, hu]
    · simp [FinProbSpace.expect, FinProbSpace.bernoulli, f, hu]
  simp_rw [hcoord, Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

/-- **Probabilistic Crossing Lemma (Ajtai–Chvátal–Newborn–Szemerédi / Leighton)**:
For any finite simple graph `G` on `v = |V|` vertices with `e = |E(G)|` edges satisfying
`4 * v ≤ e` and `0 < e`, EVERY proper drawing `D` of `G` has at least `e^3 / (64 * v^2)` crossings. -/
theorem crossing_lemma
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ProperGraphDrawing G)
    (he_pos : 0 < G.edgeFinset.card)
    (hdense : 4 * Fintype.card V ≤ G.edgeFinset.card) :
    (G.edgeFinset.card : ℝ) ^ 3 / (64 * (Fintype.card V : ℝ) ^ 2) ≤ (D.crossings.card : ℝ) := by
  set v := Fintype.card V
  set e := G.edgeFinset.card
  set cr := D.crossings.card
  have hv_pos : 0 < v := by
    by_contra hv0
    have hzero : v = 0 := Nat.eq_zero_of_not_pos hv0
    have : IsEmpty V := Fintype.card_eq_zero_iff.mp hzero
    have he0 : e = 0 := by
      dsimp [e]
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro ed _
      induction ed using Sym2.ind with
      | _ u _ => exact IsEmpty.false u
    omega
  have hv_rpos : (0 : ℝ) < (v : ℝ) := Nat.cast_pos.mpr hv_pos
  have he_rpos : (0 : ℝ) < (e : ℝ) := Nat.cast_pos.mpr he_pos
  set p : ℝ := 4 * (v : ℝ) / (e : ℝ)
  have hp_pos : 0 < p := div_pos (by linarith) he_rpos
  have hp0 : 0 ≤ p := le_of_lt hp_pos
  have hp1 : p ≤ 1 := by
    dsimp [p]
    rw [div_le_one he_rpos]
    exact_mod_cast hdense
  let μ := FinProbSpace.prod (fun _ : V => FinProbSpace.bernoulli p hp0 hp1)
  let S : (V → Bool) → Finset V := fun ω => Finset.univ.filter (fun u : V => ω u = true)
  -- Pointwise induced linear bound for every outcome ω
  have hpt : ∀ ω : V → Bool,
      ((G.edgeFinset.filter (fun ed => ∀ u ∈ ed, u ∈ S ω)).card : ℝ) -
        3 * ((S ω).card : ℝ) ≤
      ((D.crossings.filter (fun c => ∀ ed ∈ c, ∀ u ∈ ed, u ∈ S ω)).card : ℝ) := by
    intro ω
    have hnat := D.induced_linear_bound (S ω)
    have hcast : ((G.edgeFinset.filter (fun ed => ∀ u ∈ ed, u ∈ S ω)).card : ℝ) ≤
        3 * ((S ω).card : ℝ) +
          ((D.crossings.filter (fun c => ∀ ed ∈ c, ∀ u ∈ ed, u ∈ S ω)).card : ℝ) := by
      exact_mod_cast hnat
    linarith
  -- Compute E[|S|] = p * v
  have hES : μ.expect (fun ω => ((S ω).card : ℝ)) = p * (v : ℝ) := by
    have hrew : ∀ ω : V → Bool, ((S ω).card : ℝ) =
        ∑ u : V, if ∀ x ∈ ({u} : Finset V), ω x = true then (1 : ℝ) else 0 := by
      intro ω
      simp [S, Finset.sum_boole]
    simp_rw [hrew]
    rw [μ.expect_sum]
    have hterm : ∀ u : V,
        μ.expect (fun ω => if ∀ x ∈ ({u} : Finset V), ω x = true then (1 : ℝ) else 0) = p := by
      intro u
      simpa using expect_bernoulli_subset_indicator hp0 hp1 ({u} : Finset V)
    simp_rw [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  -- Compute E[|E(G[S])|] = p^2 * e
  have hEE : μ.expect (fun ω => ((G.edgeFinset.filter (fun ed => ∀ u ∈ ed, u ∈ S ω)).card : ℝ)) =
      p ^ 2 * (e : ℝ) := by
    have hrew : ∀ ω : V → Bool,
        ((G.edgeFinset.filter (fun ed => ∀ u ∈ ed, u ∈ S ω)).card : ℝ) =
        ∑ ed ∈ G.edgeFinset, if ∀ u ∈ ed, ω u = true then (1 : ℝ) else 0 := by
      intro ω
      rw [Finset.sum_boole]
      congr 2; ext ed; simp [S]
    simp_rw [hrew]
    rw [μ.expect_sum]
    have hterm : ∀ ed ∈ G.edgeFinset,
        μ.expect (fun ω => if ∀ u ∈ ed, ω u = true then (1 : ℝ) else 0) = p ^ 2 := by
      intro ed hed
      induction ed using Sym2.ind with
      | _ x y =>
        have hxy : x ≠ y := G.ne_of_adj (SimpleGraph.mem_edgeFinset.mp hed)
        have hpair : ∀ ω : V → Bool,
            (if ∀ u ∈ s(x, y), ω u = true then (1 : ℝ) else 0) =
            (if ∀ u ∈ ({x, y} : Finset V), ω u = true then (1 : ℝ) else 0) := by
          intro ω; congr 1
          simp only [Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton]
        simp_rw [hpair]
        rw [expect_bernoulli_subset_indicator hp0 hp1 ({x, y} : Finset V), Finset.card_pair hxy]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    ring
  -- Compute E[cr(G[S])] = p^4 * cr
  have hEC : μ.expect (fun ω =>
      ((D.crossings.filter (fun c => ∀ ed ∈ c, ∀ u ∈ ed, u ∈ S ω)).card : ℝ)) =
      p ^ 4 * (cr : ℝ) := by
    have hrew : ∀ ω : V → Bool,
        ((D.crossings.filter (fun c => ∀ ed ∈ c, ∀ u ∈ ed, u ∈ S ω)).card : ℝ) =
        ∑ c ∈ D.crossings, if ∀ ed ∈ c, ∀ u ∈ ed, ω u = true then (1 : ℝ) else 0 := by
      intro ω
      rw [Finset.sum_boole]
      congr 2; ext c; simp [S]
    simp_rw [hrew]
    rw [μ.expect_sum]
    have hterm : ∀ c ∈ D.crossings,
        μ.expect (fun ω => if ∀ ed ∈ c, ∀ u ∈ ed, ω u = true then (1 : ℝ) else 0) = p ^ 4 := by
      intro c hc
      rcases D.crossings_edges c hc with ⟨e₁, he₁, e₂, he₂, rfl, hdisj⟩
      induction e₁ using Sym2.ind with
      | _ x₁ y₁ =>
        induction e₂ using Sym2.ind with
        | _ x₂ y₂ =>
          have h12 : x₁ ≠ y₁ := G.ne_of_adj (SimpleGraph.mem_edgeFinset.mp he₁)
          have h34 : x₂ ≠ y₂ := G.ne_of_adj (SimpleGraph.mem_edgeFinset.mp he₂)
          have hdisj_fin : Disjoint ({x₁, y₁} : Finset V) ({x₂, y₂} : Finset V) := by
            rw [Finset.disjoint_left]
            intro u hu1 hu2
            have hu1' : u ∈ s(x₁, y₁) := by
              rw [Sym2.mem_iff]; simpa using hu1
            have hu2' : u ∈ s(x₂, y₂) := by
              rw [Sym2.mem_iff]; simpa using hu2
            exact hdisj u hu1' hu2'
          have hcard4 : (({x₁, y₁} : Finset V) ∪ {x₂, y₂}).card = 4 := by
            rw [Finset.card_union_of_disjoint hdisj_fin, Finset.card_pair h12, Finset.card_pair h34]
          have hquad : ∀ ω : V → Bool,
              (if ∀ ed ∈ s(s(x₁, y₁), s(x₂, y₂)), ∀ u ∈ ed, ω u = true then (1 : ℝ) else 0) =
              (if ∀ u ∈ (({x₁, y₁} : Finset V) ∪ {x₂, y₂}), ω u = true then (1 : ℝ) else 0) := by
            intro ω
            have hiff : (∀ ed ∈ s(s(x₁, y₁), s(x₂, y₂)), ∀ u ∈ ed, ω u = true) ↔
                (∀ u ∈ (({x₁, y₁} : Finset V) ∪ {x₂, y₂}), ω u = true) := by
              constructor
              · intro h u hu
                rcases Finset.mem_union.mp hu with hu1 | hu2
                · exact h s(x₁, y₁) (Sym2.mem_mk_left _ _) u (by rw [Sym2.mem_iff]; simpa using hu1)
                · exact h s(x₂, y₂) (Sym2.mem_mk_right _ _) u (by rw [Sym2.mem_iff]; simpa using hu2)
              · intro h ed hed u hu
                rw [Sym2.mem_iff] at hed
                rcases hed with rfl | rfl
                · exact h u (Finset.mem_union_left _ (by rw [Sym2.mem_iff] at hu; simpa using hu))
                · exact h u (Finset.mem_union_right _ (by rw [Sym2.mem_iff] at hu; simpa using hu))
            exact if_congr hiff rfl rfl
          simp_rw [hquad]
          rw [expect_bernoulli_subset_indicator hp0 hp1 (({x₁, y₁} : Finset V) ∪ {x₂, y₂}), hcard4]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    ring
  -- Combine expectations and plug in p = 4v / e
  have hexp_ineq : p ^ 2 * (e : ℝ) - 3 * (p * (v : ℝ)) ≤ p ^ 4 * (cr : ℝ) := by
    have h1 := μ.expect_mono hpt
    rw [μ.expect_sub, μ.expect_const_mul, hEE, hES, hEC] at h1
    exact h1
  have hp4_pos : 0 < p ^ 4 := pow_pos hp_pos 4
  have hcr_ge : (p ^ 2 * (e : ℝ) - 3 * (p * (v : ℝ))) / p ^ 4 ≤ (cr : ℝ) :=
    (div_le_iff₀ hp4_pos).mpr (by linarith)
  have halg : (p ^ 2 * (e : ℝ) - 3 * (p * (v : ℝ))) / p ^ 4 =
      (e : ℝ) ^ 3 / (64 * (v : ℝ) ^ 2) := by
    dsimp [p]
    field_simp [ne_of_gt hv_rpos, ne_of_gt he_rpos]
    ring
  linarith


/-! ### 5B. Caro–Wei Theorem and Turán's Theorem -/

/-- **Caro–Wei Theorem** (induced subset form):
Every finite subset `U` of vertices of a `SimpleGraph V` contains an independent set `I ⊆ U`
with `|I| ≥ ∑ v ∈ U, 1 / (deg_U(v) + 1)`. -/
theorem caro_wei_subset
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) :
    ∃ I ⊆ U, (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) ∧
      ∑ v ∈ U, (1 : ℝ) / (((U.filter (G.Adj v)).card : ℝ) + 1) ≤ (I.card : ℝ) := by
  induction hcard : U.card using Nat.strong_induction_on generalizing U with
  | h k ih =>
    rcases U.eq_empty_or_nonempty with rfl | hUne
    · exact ⟨∅, Finset.Subset.refl _, fun _ h => absurd h (Finset.notMem_empty _), by simp⟩
    · obtain ⟨v₀, hv₀U, hv₀min⟩ :=
        Finset.exists_min_image U (fun v => (U.filter (G.Adj v)).card) hUne
      set N₀ := U.filter (G.Adj v₀)
      set S := insert v₀ N₀
      set U' := U \ S
      have hS_sub : S ⊆ U := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxN
        · exact hv₀U
        · exact (Finset.mem_filter.mp hxN).1
      have hv₀_not_N₀ : v₀ ∉ N₀ := by
        intro hmem
        exact G.loopless.irrefl v₀ (Finset.mem_filter.mp hmem).2
      have hS_card : S.card = N₀.card + 1 := Finset.card_insert_of_notMem hv₀_not_N₀
      have hU'_lt : U'.card < k := by
        rw [← hcard]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨Finset.sdiff_subset, fun heq => ?_⟩
        have : v₀ ∈ U' := heq.symm ▸ hv₀U
        exact (Finset.mem_sdiff.mp this).2 (Finset.mem_insert_self v₀ N₀)
      obtain ⟨I', hI'sub, hI'indep, hI'sum⟩ := ih U'.card hU'_lt U' rfl
      refine ⟨insert v₀ I', ?_, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxI'
        · exact hv₀U
        · exact Finset.sdiff_subset (hI'sub hxI')
      · intro u hu v hv
        rcases Finset.mem_insert.mp hu with rfl | huI' <;>
          rcases Finset.mem_insert.mp hv with rfl | hvI'
        · exact G.loopless.irrefl _
        · intro hadj
          have hvU : v ∈ U := Finset.sdiff_subset (hI'sub hvI')
          have hvS : v ∈ S := Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hvU, hadj⟩)
          exact (Finset.mem_sdiff.mp (hI'sub hvI')).2 hvS
        · intro hadj
          have huU : u ∈ U := Finset.sdiff_subset (hI'sub huI')
          have huS : u ∈ S := Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨huU, (G.adj_comm _ _).mp hadj⟩)
          exact (Finset.mem_sdiff.mp (hI'sub huI')).2 huS
        · exact hI'indep u huI' v hvI'
      · have hv₀_not_I' : v₀ ∉ I' := fun h =>
          (Finset.mem_sdiff.mp (hI'sub h)).2 (Finset.mem_insert_self v₀ N₀)
        have hI_card : ((insert v₀ I').card : ℝ) = (I'.card : ℝ) + 1 := by
          rw [Finset.card_insert_of_notMem hv₀_not_I', Nat.cast_add, Nat.cast_one]
        rw [hI_card]
        have hU_eq : U = S ∪ U' := (Finset.union_sdiff_of_subset hS_sub).symm
        have hdisj : Disjoint S U' := Finset.disjoint_sdiff
        have hsplit : ∑ v ∈ U, (1 : ℝ) / (((U.filter (G.Adj v)).card : ℝ) + 1) =
            ∑ v ∈ S, (1 : ℝ) / (((U.filter (G.Adj v)).card : ℝ) + 1) +
            ∑ v ∈ U', (1 : ℝ) / (((U.filter (G.Adj v)).card : ℝ) + 1) := by
          rw [← Finset.sum_union hdisj, ← hU_eq]
        rw [hsplit]
        have hN0_pos : (0 : ℝ) < (N₀.card : ℝ) + 1 :=
          add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one
        have hsumS : ∑ v ∈ S, (1 : ℝ) / (((U.filter (G.Adj v)).card : ℝ) + 1) ≤ 1 := by
          calc ∑ v ∈ S, (1 : ℝ) / (((U.filter (G.Adj v)).card : ℝ) + 1)
              ≤ ∑ _v ∈ S, (1 : ℝ) / ((N₀.card : ℝ) + 1) := by
                refine Finset.sum_le_sum fun v hvS => ?_
                have hmin : N₀.card ≤ (U.filter (G.Adj v)).card := hv₀min v (hS_sub hvS)
                have hcast : (N₀.card : ℝ) + 1 ≤ ((U.filter (G.Adj v)).card : ℝ) + 1 := by
                  exact_mod_cast Nat.add_le_add_right hmin 1
                exact one_div_le_one_div_of_le hN0_pos hcast
            _ = (S.card : ℝ) * ((1 : ℝ) / ((N₀.card : ℝ) + 1)) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ = 1 := by
                rw [hS_card, Nat.cast_add, Nat.cast_one]
                exact mul_one_div_cancel (ne_of_gt hN0_pos)
        have hsumU' : ∑ v ∈ U', (1 : ℝ) / (((U.filter (G.Adj v)).card : ℝ) + 1) ≤
            ∑ v ∈ U', (1 : ℝ) / (((U'.filter (G.Adj v)).card : ℝ) + 1) := by
          refine Finset.sum_le_sum fun v _ => ?_
          have hsub : U'.filter (G.Adj v) ⊆ U.filter (G.Adj v) :=
            Finset.filter_subset_filter _ Finset.sdiff_subset
          have hle : ((U'.filter (G.Adj v)).card : ℝ) + 1 ≤
              ((U.filter (G.Adj v)).card : ℝ) + 1 := by
            exact_mod_cast Nat.add_le_add_right (Finset.card_le_card hsub) 1
          exact one_div_le_one_div_of_le
            (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one) hle
        linarith

/-- **Caro–Wei Theorem**:
Every finite simple graph `G` has an independent set `I` of size at least `∑ v, 1 / (deg v + 1)`. -/
theorem caro_wei
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ I : Finset V, (∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) ∧
      ∑ v : V, (1 : ℝ) / ((G.degree v : ℝ) + 1) ≤ (I.card : ℝ) := by
  obtain ⟨I, _, hindep, hsum⟩ := caro_wei_subset G Finset.univ
  refine ⟨I, hindep, ?_⟩
  have heq : ∀ v : V, (Finset.univ.filter (G.Adj v)).card = G.degree v := by
    intro v; rw [SimpleGraph.degree]; congr 1; ext u; simp [SimpleGraph.mem_neighborFinset]
  simpa [heq] using hsum

/-- Elementary Cauchy–Schwarz / AM–HM inequality:
for positive `a : V → ℝ`, `(|V|)^2 ≤ (∑ v, a v) * (∑ v, 1 / a v)`. -/
lemma sq_card_le_sum_mul_sum_inv {V : Type*} [Fintype V]
    (a : V → ℝ) (ha : ∀ v, 0 < a v) :
    (Fintype.card V : ℝ) ^ 2 ≤ (∑ v : V, a v) * (∑ v : V, 1 / a v) := by
  have hnonneg : 0 ≤ ∑ u : V, ∑ v : V, (a u - a v) ^ 2 / (a u * a v) :=
    Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ =>
      div_nonneg (sq_nonneg _) (le_of_lt (mul_pos (ha u) (ha v)))
  have hid : ∑ u : V, ∑ v : V, (a u - a v) ^ 2 / (a u * a v) =
      2 * ((∑ u : V, a u) * (∑ v : V, 1 / a v) - (Fintype.card V : ℝ) ^ 2) := by
    have hterm : ∀ u v : V,
        (a u - a v) ^ 2 / (a u * a v) = a u * (1 / a v) + a v * (1 / a u) - 2 := by
      intro u v
      have hu : a u ≠ 0 := ne_of_gt (ha u)
      have hv : a v ≠ 0 := ne_of_gt (ha v)
      field_simp [hu, hv]; ring
    simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have h1 : ∑ u : V, ∑ v : V, a u * (1 / a v) = (∑ u : V, a u) * (∑ v : V, 1 / a v) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun u _ => (Finset.mul_sum _ _ _).symm
    have h2 : ∑ u : V, ∑ v : V, a v * (1 / a u) = (∑ u : V, a u) * (∑ v : V, 1 / a v) := by
      rw [Finset.sum_comm]
      exact h1
    have h3 : ∑ _u : V, ∑ _v : V, (2 : ℝ) = 2 * (Fintype.card V : ℝ) ^ 2 := by
      simp [Finset.sum_const, Finset.card_univ]; ring
    rw [h1, h2, h3]; ring
  linarith

/-- **Turán's Theorem**:
If `G : SimpleGraph V` has no `(r + 1)`-clique (`r ≥ 1`), then
`e(G) ≤ (1 - 1 / r) * |V|^2 / 2`. -/
theorem turan_theorem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (hr : 1 ≤ r)
    (hfree : ∀ C : Finset V, C.card = r + 1 → ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ ¬ G.Adj u v) :
    (G.edgeFinset.card : ℝ) ≤ (1 - 1 / (r : ℝ)) * (Fintype.card V : ℝ) ^ 2 / 2 := by
  set n := Fintype.card V
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hr)
  obtain ⟨I, hIindep, hIsum⟩ := caro_wei (Gᶜ)
  -- An independent set in Gᶜ is a clique in G, so |I| ≤ r
  have hI_le : I.card ≤ r := by
    by_contra hgt
    have hge : r + 1 ≤ I.card := by omega
    obtain ⟨C, hCsub, hCcard⟩ := Finset.exists_subset_card_eq hge
    obtain ⟨u, huC, v, hvC, huv, hnadj⟩ := hfree C hCcard
    exact hIindep u (hCsub huC) v (hCsub hvC) ⟨huv, hnadj⟩
  -- For every v, Gᶜ.degree v + 1 = n - G.degree v > 0
  have hdeg_comp : ∀ v : V, (Gᶜ.degree v : ℝ) + 1 = (n : ℝ) - (G.degree v : ℝ) := by
    intro v
    have hpart : (Finset.univ.filter (fun u : V => G.Adj v u)).card +
        (Finset.univ.filter (fun u : V => ¬ G.Adj v u)).card = n := by
      have hdisj : Disjoint (Finset.univ.filter (fun u : V => G.Adj v u))
          (Finset.univ.filter (fun u : V => ¬ G.Adj v u)) := by
        rw [Finset.disjoint_left]
        intro u h1 h2
        exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
      have hunion : Finset.univ.filter (fun u : V => G.Adj v u) ∪
          Finset.univ.filter (fun u : V => ¬ G.Adj v u) = Finset.univ := by
        ext u; simp [em]
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ]
    have h1 : (Finset.univ.filter (fun u : V => G.Adj v u)).card = G.degree v := by
      rw [SimpleGraph.degree]; congr 1; ext u; simp [SimpleGraph.mem_neighborFinset]
    have h2 : (Finset.univ.filter (fun u : V => ¬ G.Adj v u)).card = Gᶜ.degree v + 1 := by
      have hset : Finset.univ.filter (fun u : V => ¬ G.Adj v u) =
          insert v (Gᶜ.neighborFinset v) := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          SimpleGraph.mem_neighborFinset, SimpleGraph.compl_adj]
        constructor
        · intro h
          by_cases huv : u = v
          · exact Or.inl huv
          · exact Or.inr ⟨Ne.symm huv, h⟩
        · rintro (rfl | ⟨_, h⟩)
          · exact G.loopless.irrefl u
          · exact h
      have hv_not : v ∉ Gᶜ.neighborFinset v := by
        simp [SimpleGraph.mem_neighborFinset]
      rw [hset, Finset.card_insert_of_notMem hv_not, SimpleGraph.degree]
    have hnat : G.degree v + (Gᶜ.degree v + 1) = n := by omega
    have hcast : (G.degree v : ℝ) + ((Gᶜ.degree v : ℝ) + 1) = (n : ℝ) := by exact_mod_cast hnat
    linarith
  have ha_pos : ∀ v : V, 0 < (n : ℝ) - (G.degree v : ℝ) := by
    intro v; rw [← hdeg_comp v]; positivity
  have hinv_le : ∑ v : V, (1 : ℝ) / ((n : ℝ) - (G.degree v : ℝ)) ≤ (r : ℝ) := by
    calc ∑ v : V, (1 : ℝ) / ((n : ℝ) - (G.degree v : ℝ))
        = ∑ v : V, (1 : ℝ) / ((Gᶜ.degree v : ℝ) + 1) :=
          Finset.sum_congr rfl fun v _ => by rw [hdeg_comp v]
      _ ≤ (I.card : ℝ) := hIsum
      _ ≤ (r : ℝ) := by exact_mod_cast hI_le
  have hcs := sq_card_le_sum_mul_sum_inv (fun v : V => (n : ℝ) - (G.degree v : ℝ)) ha_pos
  have hsum_a : ∑ v : V, ((n : ℝ) - (G.degree v : ℝ)) =
      (n : ℝ) ^ 2 - 2 * (G.edgeFinset.card : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hdeg_sum : ∑ v : V, (G.degree v : ℝ) = 2 * (G.edgeFinset.card : ℝ) := by
      exact_mod_cast G.sum_degrees_eq_twice_card_edges
    rw [hdeg_sum]; ring
  have hsum_a_nonneg : 0 ≤ ∑ v : V, ((n : ℝ) - (G.degree v : ℝ)) :=
    Finset.sum_nonneg fun v _ => le_of_lt (ha_pos v)
  have hmain : (n : ℝ) ^ 2 ≤ ((n : ℝ) ^ 2 - 2 * (G.edgeFinset.card : ℝ)) * (r : ℝ) := by
    rw [← hsum_a]
    exact le_trans hcs (mul_le_mul_of_nonneg_left hinv_le hsum_a_nonneg)
  have hdiv : (n : ℝ) ^ 2 / (r : ℝ) ≤ (n : ℝ) ^ 2 - 2 * (G.edgeFinset.card : ℝ) :=
    (div_le_iff₀ hr_pos).mpr hmain
  have hrew : (1 - 1 / (r : ℝ)) * (n : ℝ) ^ 2 / 2 = ((n : ℝ) ^ 2 - (n : ℝ) ^ 2 / (r : ℝ)) / 2 := by
    ring
  rw [hrew]
  linarith


/-! ### 5C. Katona–Nemetz–Simonovits Hypergraph Averaging & Erdős–Simonovits Supersaturation -/

/-- Exact binomial double-counting identity:
for `k ≤ m ≤ n`, `n.choose k * (n - k).choose (m - k) = n.choose m * m.choose k`. -/
lemma choose_mul_choose_sub {n m k : ℕ} (hkm : k ≤ m) (_hmn : m ≤ n) :
    n.choose k * (n - k).choose (m - k) = n.choose m * m.choose k :=
  (Nat.choose_mul (n := n) hkm).symm

/-- Number of `m`-subsets of `V` containing a fixed `k`-subset `e ⊆ V` is `(card V - k).choose (m - k)`. -/
lemma card_powersetCard_superset {V : Type*} [Fintype V] [DecidableEq V]
    {e : Finset V} {k m : ℕ} (he : e.card = k) (hkm : k ≤ m) :
    ((Finset.powersetCard m (Finset.univ : Finset V)).filter (fun S => e ⊆ S)).card =
      (Fintype.card V - k).choose (m - k) := by
  have hcompl_card : (Finset.univ \ e).card = Fintype.card V - k := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ e), Finset.card_univ, he]
  rw [← hcompl_card, ← Finset.card_powersetCard]
  refine Finset.card_bij (fun S _ => S \ e) ?_ ?_ ?_
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and] at hS ⊢
    refine ⟨fun x hx => Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, (Finset.mem_sdiff.mp hx).2⟩, ?_⟩
    rw [Finset.card_sdiff_of_subset hS.2, hS.1, he]
  · intro S₁ hS₁ S₂ hS₂ heq
    have h1 := (Finset.mem_filter.mp hS₁).2
    have h2 := (Finset.mem_filter.mp hS₂).2
    calc S₁ = S₁ \ e ∪ e := (Finset.sdiff_union_of_subset h1).symm
      _ = S₂ \ e ∪ e := by rw [heq]
      _ = S₂ := Finset.sdiff_union_of_subset h2
  · intro T hT
    simp only [Finset.mem_powersetCard] at hT
    refine ⟨T ∪ e, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
      have hdisj : Disjoint T e := by
        rw [Finset.disjoint_left]
        intro x hxT
        exact (Finset.mem_sdiff.mp (hT.1 hxT)).2
      refine ⟨?_, Finset.subset_union_right⟩
      rw [Finset.card_union_of_disjoint hdisj, hT.2, he]
      omega
    · have hdisj : Disjoint T e := by
        rw [Finset.disjoint_left]
        intro x hxT
        exact (Finset.mem_sdiff.mp (hT.1 hxT)).2
      exact Finset.union_sdiff_cancel_right hdisj

/-- **Katona–Nemetz–Simonovits (KNS) Hypergraph Averaging Identity**:
For any `k`-uniform hypergraph `H` on `V` (`n = |V|`) and `k ≤ m`:
`∑_{S ∈ (V choose m)} |H[S]| = (n - k).choose (m - k) * |H|`. -/
theorem hypergraph_averaging_identity
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : Finset (Finset V)) (k m : ℕ)
    (hunif : ∀ e ∈ H, e.card = k) (hkm : k ≤ m) :
    ∑ S ∈ Finset.powersetCard m (Finset.univ : Finset V), (H.filter (fun e => e ⊆ S)).card =
      (Fintype.card V - k).choose (m - k) * H.card := by
  calc ∑ S ∈ Finset.powersetCard m (Finset.univ : Finset V), (H.filter (fun e => e ⊆ S)).card
      = ∑ S ∈ Finset.powersetCard m (Finset.univ : Finset V),
          ∑ e ∈ H, if e ⊆ S then 1 else 0 := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [Finset.sum_boole, Nat.cast_id]
    _ = ∑ e ∈ H, ∑ S ∈ Finset.powersetCard m (Finset.univ : Finset V),
          if e ⊆ S then 1 else 0 := Finset.sum_comm
    _ = ∑ e ∈ H, ((Finset.powersetCard m (Finset.univ : Finset V)).filter (fun S => e ⊆ S)).card := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.sum_boole, Nat.cast_id]
    _ = ∑ _e ∈ H, (Fintype.card V - k).choose (m - k) :=
        Finset.sum_congr rfl fun e he => card_powersetCard_superset (hunif e he) hkm
    _ = (Fintype.card V - k).choose (m - k) * H.card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **KNS Normalized Hypergraph Density Averaging**:
The average edge density of a `k`-uniform hypergraph `H` over all `m`-element induced
sub-hypergraphs (`k ≤ m ≤ |V|`) equals the global edge density `|H| / C(|V|, k)`. -/
theorem hypergraph_density_averaging
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : Finset (Finset V)) (k m : ℕ)
    (hunif : ∀ e ∈ H, e.card = k) (hkm : k ≤ m) (hmn : m ≤ Fintype.card V) :
    ((Fintype.card V).choose m : ℝ)⁻¹ *
      ∑ S ∈ Finset.powersetCard m (Finset.univ : Finset V),
        ((H.filter (fun e => e ⊆ S)).card : ℝ) / (m.choose k : ℝ) =
      (H.card : ℝ) / ((Fintype.card V).choose k : ℝ) := by
  set n := Fintype.card V
  have hcmk_pos : (0 : ℝ) < (m.choose k : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos hkm)
  have hcnm_pos : (0 : ℝ) < (n.choose m : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos hmn)
  have hcnk_pos : (0 : ℝ) < (n.choose k : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos (le_trans hkm hmn))
  have hid := hypergraph_averaging_identity H k m hunif hkm
  have hsum : ∑ S ∈ Finset.powersetCard m (Finset.univ : Finset V),
      ((H.filter (fun e => e ⊆ S)).card : ℝ) =
      (((n - k).choose (m - k) : ℕ) : ℝ) * (H.card : ℝ) := by
    exact_mod_cast hid
  have hbinom : (n.choose k : ℝ) * (((n - k).choose (m - k) : ℕ) : ℝ) =
      (n.choose m : ℝ) * (m.choose k : ℝ) := by
    exact_mod_cast choose_mul_choose_sub hkm hmn
  rw [← Finset.sum_div, hsum]
  field_simp [ne_of_gt hcmk_pos, ne_of_gt hcnm_pos, ne_of_gt hcnk_pos]
  calc (((n - k).choose (m - k) : ℕ) : ℝ) * (H.card : ℝ) * (n.choose k : ℝ)
      = (H.card : ℝ) * ((n.choose k : ℝ) * (((n - k).choose (m - k) : ℕ) : ℝ)) := by ring
    _ = (H.card : ℝ) * ((n.choose m : ℝ) * (m.choose k : ℝ)) := by rw [hbinom]
    _ = (n.choose m : ℝ) * (H.card : ℝ) * (m.choose k : ℝ) := by ring

/-- **Erdős–Simonovits Supersaturation Core (Rich `m`-Subsets)**:
If a `k`-uniform hypergraph `H` on `V` (`n = |V|`, `k ≤ m ≤ n`) has edge count at least
`(t / C(m, k) + ε) * C(n, k)` (with `t ≤ C(m, k)`, `ε ≥ 0`), then at least `ε * C(n, m)`
subsets `S ⊆ V` of size `m` induce strictly more than `t` hyperedges of `H`. -/
theorem hypergraph_supersaturation_rich_subsets
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : Finset (Finset V)) (k m t : ℕ) (ε : ℝ)
    (hunif : ∀ e ∈ H, e.card = k) (hkm : k ≤ m) (hmn : m ≤ Fintype.card V)
    (hdense : ((t : ℝ) / (m.choose k : ℝ) + ε) * ((Fintype.card V).choose k : ℝ) ≤ (H.card : ℝ)) :
    ε * ((Fintype.card V).choose m : ℝ) ≤
      (((Finset.powersetCard m (Finset.univ : Finset V)).filter
        (fun S => t < (H.filter (fun e => e ⊆ S)).card)).card : ℝ) := by
  set n := Fintype.card V
  set P := Finset.powersetCard m (Finset.univ : Finset V)
  set R := P.filter (fun S => t < (H.filter (fun e => e ⊆ S)).card)
  have hPcard : P.card = n.choose m := by simp [P, n]
  have hcmk_pos : (0 : ℝ) < (m.choose k : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos hkm)
  have hid := hypergraph_averaging_identity H k m hunif hkm
  have hbinom : (n.choose k : ℝ) * (((n - k).choose (m - k) : ℕ) : ℝ) =
      (n.choose m : ℝ) * (m.choose k : ℝ) := by
    exact_mod_cast choose_mul_choose_sub hkm hmn
  -- Lower bound on ∑_{S ∈ P} |H[S]| from KNS averaging + density hypothesis
  have hlow : (t : ℝ) * (n.choose m : ℝ) + ε * (m.choose k : ℝ) * (n.choose m : ℝ) ≤
      ∑ S ∈ P, ((H.filter (fun e => e ⊆ S)).card : ℝ) := by
    have hsum : ∑ S ∈ P, ((H.filter (fun e => e ⊆ S)).card : ℝ) =
        (((n - k).choose (m - k) : ℕ) : ℝ) * (H.card : ℝ) := by
      exact_mod_cast hid
    rw [hsum]
    have hmul := mul_le_mul_of_nonneg_left hdense (Nat.cast_nonneg ((n - k).choose (m - k)))
    have halg : (((n - k).choose (m - k) : ℕ) : ℝ) *
        (((t : ℝ) / (m.choose k : ℝ) + ε) * (n.choose k : ℝ)) =
        (t : ℝ) * (n.choose m : ℝ) + ε * (m.choose k : ℝ) * (n.choose m : ℝ) := by
      have h1 : (((n - k).choose (m - k) : ℕ) : ℝ) * (n.choose k : ℝ) =
          (n.choose m : ℝ) * (m.choose k : ℝ) := by linarith
      calc (((n - k).choose (m - k) : ℕ) : ℝ) *
              (((t : ℝ) / (m.choose k : ℝ) + ε) * (n.choose k : ℝ))
          = ((t : ℝ) / (m.choose k : ℝ) + ε) *
              ((((n - k).choose (m - k) : ℕ) : ℝ) * (n.choose k : ℝ)) := by ring
        _ = ((t : ℝ) / (m.choose k : ℝ) + ε) * ((n.choose m : ℝ) * (m.choose k : ℝ)) := by rw [h1]
        _ = (t : ℝ) * (n.choose m : ℝ) + ε * (m.choose k : ℝ) * (n.choose m : ℝ) := by
            field_simp [ne_of_gt hcmk_pos]
    linarith
  -- Upper bound on ∑_{S ∈ P} |H[S]| by splitting P into R and P \ R
  have hup : ∑ S ∈ P, ((H.filter (fun e => e ⊆ S)).card : ℝ) ≤
      (R.card : ℝ) * ((m.choose k : ℝ) - (t : ℝ)) + (t : ℝ) * (n.choose m : ℝ) := by
    have hRsub : R ⊆ P := Finset.filter_subset _ _
    have hsplit : ∑ S ∈ P, ((H.filter (fun e => e ⊆ S)).card : ℝ) =
        ∑ S ∈ R, ((H.filter (fun e => e ⊆ S)).card : ℝ) +
        ∑ S ∈ P \ R, ((H.filter (fun e => e ⊆ S)).card : ℝ) := by
      rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hRsub]
    rw [hsplit]
    have hR_ub : ∑ S ∈ R, ((H.filter (fun e => e ⊆ S)).card : ℝ) ≤
        (R.card : ℝ) * (m.choose k : ℝ) := by
      calc ∑ S ∈ R, ((H.filter (fun e => e ⊆ S)).card : ℝ)
          ≤ ∑ _S ∈ R, (m.choose k : ℝ) := by
            refine Finset.sum_le_sum fun S hS => ?_
            have hSP : S ∈ P := hRsub hS
            have hScard : S.card = m := (Finset.mem_powersetCard.mp hSP).2
            have hsub : H.filter (fun e => e ⊆ S) ⊆ Finset.powersetCard k S := by
              intro e he
              rw [Finset.mem_filter] at he
              exact Finset.mem_powersetCard.mpr ⟨he.2, hunif e he.1⟩
            have hcard : (H.filter (fun e => e ⊆ S)).card ≤ m.choose k := by
              calc (H.filter (fun e => e ⊆ S)).card
                  ≤ (Finset.powersetCard k S).card := Finset.card_le_card hsub
                _ = m.choose k := by rw [Finset.card_powersetCard, hScard]
            exact_mod_cast hcard
        _ = (R.card : ℝ) * (m.choose k : ℝ) := by simp [Finset.sum_const]
    have hPR_ub : ∑ S ∈ P \ R, ((H.filter (fun e => e ⊆ S)).card : ℝ) ≤
        ((P \ R).card : ℝ) * (t : ℝ) := by
      calc ∑ S ∈ P \ R, ((H.filter (fun e => e ⊆ S)).card : ℝ)
          ≤ ∑ _S ∈ P \ R, (t : ℝ) := by
            refine Finset.sum_le_sum fun S hS => ?_
            rw [Finset.mem_sdiff] at hS
            have hnot : ¬ (t < (H.filter (fun e => e ⊆ S)).card) := fun hlt =>
              hS.2 (Finset.mem_filter.mpr ⟨hS.1, hlt⟩)
            exact_mod_cast Nat.le_of_not_lt hnot
        _ = ((P \ R).card : ℝ) * (t : ℝ) := by simp [Finset.sum_const]
    have hcard_sdiff : ((P \ R).card : ℝ) = (n.choose m : ℝ) - (R.card : ℝ) := by
      have h1 : (P \ R).card + R.card = P.card := Finset.card_sdiff_add_card_eq_card hRsub
      have h2 : ((P \ R).card : ℝ) + (R.card : ℝ) = (n.choose m : ℝ) := by
        rw [← hPcard]; exact_mod_cast h1
      linarith
    rw [hcard_sdiff] at hPR_ub
    linarith
  have hmain : ε * (m.choose k : ℝ) * (n.choose m : ℝ) ≤
      (R.card : ℝ) * ((m.choose k : ℝ) - (t : ℝ)) := by linarith
  have hle_mk : (R.card : ℝ) * ((m.choose k : ℝ) - (t : ℝ)) ≤
      (R.card : ℝ) * (m.choose k : ℝ) := by
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    have : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
    linarith
  have hfinal : ε * (n.choose m : ℝ) * (m.choose k : ℝ) ≤ (R.card : ℝ) * (m.choose k : ℝ) := by
    linarith
  exact le_of_mul_le_mul_right hfinal hcmk_pos

/-- **Erdős–Simonovits Supersaturation Core (Many `v`-Vertex Copies)**:
Under the supersaturation density hypothesis above, if every `m`-subset `S` with `|H[S]| > t`
contains at least one `v`-vertex copy `C ∈ Copies` (`v ≤ m`), then
`ε / C(m, v) * C(n, v) ≤ |Copies|`. -/
theorem hypergraph_supersaturation_copies
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : Finset (Finset V)) (Copies : Finset (Finset V))
    (k m v t : ℕ) (ε : ℝ)
    (hunif : ∀ e ∈ H, e.card = k) (hkm : k ≤ m) (hvm : v ≤ m) (hmn : m ≤ Fintype.card V)
    (hC_unif : ∀ C ∈ Copies, C.card = v)
    (hcontain : ∀ S ∈ Finset.powersetCard m (Finset.univ : Finset V),
      t < (H.filter (fun e => e ⊆ S)).card → ∃ C ∈ Copies, C ⊆ S)
    (hdense : ((t : ℝ) / (m.choose k : ℝ) + ε) * ((Fintype.card V).choose k : ℝ) ≤ (H.card : ℝ)) :
    ε / (m.choose v : ℝ) * ((Fintype.card V).choose v : ℝ) ≤ (Copies.card : ℝ) := by
  set n := Fintype.card V
  set P := Finset.powersetCard m (Finset.univ : Finset V)
  set R := P.filter (fun S => t < (H.filter (fun e => e ⊆ S)).card)
  have hR_ge := hypergraph_supersaturation_rich_subsets H k m t ε hunif hkm hmn hdense
  -- Double count pairs (S ∈ R, C ∈ Copies) with C ⊆ S
  have hcount : R.card ≤ (n - v).choose (m - v) * Copies.card := by
    calc R.card
        = ∑ _S ∈ R, 1 := by simp [Finset.sum_const]
      _ ≤ ∑ S ∈ R, (Copies.filter (fun C => C ⊆ S)).card := by
          refine Finset.sum_le_sum fun S hS => ?_
          rw [Finset.mem_filter] at hS
          obtain ⟨C, hCC, hCS⟩ := hcontain S hS.1 hS.2
          exact Finset.card_pos.mpr ⟨C, Finset.mem_filter.mpr ⟨hCC, hCS⟩⟩
      _ ≤ ∑ S ∈ P, (Copies.filter (fun C => C ⊆ S)).card :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = (n - v).choose (m - v) * Copies.card :=
          hypergraph_averaging_identity Copies v m hC_unif hvm
  have hcount_r : (R.card : ℝ) ≤ (((n - v).choose (m - v) : ℕ) : ℝ) * (Copies.card : ℝ) := by
    exact_mod_cast hcount
  have hbinom_v : (n.choose v : ℝ) * (((n - v).choose (m - v) : ℕ) : ℝ) =
      (n.choose m : ℝ) * (m.choose v : ℝ) := by
    exact_mod_cast choose_mul_choose_sub hvm hmn
  have hcmv_pos : (0 : ℝ) < (m.choose v : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos hvm)
  have hcnmv_pos : (0 : ℝ) < (((n - v).choose (m - v) : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos (Nat.sub_le_sub_right hmn v))
  have h1 : ε * (n.choose m : ℝ) ≤ (((n - v).choose (m - v) : ℕ) : ℝ) * (Copies.card : ℝ) :=
    le_trans hR_ge hcount_r
  have h2 : ε / (m.choose v : ℝ) * (n.choose v : ℝ) * (((n - v).choose (m - v) : ℕ) : ℝ) ≤
      (Copies.card : ℝ) * (((n - v).choose (m - v) : ℕ) : ℝ) := by
    have hlhs : ε / (m.choose v : ℝ) * (n.choose v : ℝ) * (((n - v).choose (m - v) : ℕ) : ℝ) =
        ε * (n.choose m : ℝ) := by
      calc ε / (m.choose v : ℝ) * (n.choose v : ℝ) * (((n - v).choose (m - v) : ℕ) : ℝ)
          = ε / (m.choose v : ℝ) * ((n.choose v : ℝ) * (((n - v).choose (m - v) : ℕ) : ℝ)) := by
              ring
        _ = ε / (m.choose v : ℝ) * ((n.choose m : ℝ) * (m.choose v : ℝ)) := by rw [hbinom_v]
        _ = ε * (n.choose m : ℝ) := by field_simp [ne_of_gt hcmv_pos]
    linarith
  exact le_of_mul_le_mul_right h2 hcnmv_pos

/-- **Turán Graph `K_{r+1}` Supersaturation Theorem**:
Combines `turan_theorem` and `hypergraph_supersaturation_copies`:
if a simple graph `G` on `n = |V|` vertices (`r ≥ 1`, `r + 1 ≤ m ≤ n`) has at least
`((1 - 1/r) * m / (m - 1) + ε) * C(n, 2)` edges, then `G` contains at least
`ε / C(m, r + 1) * C(n, r + 1)` cliques of size `r + 1`. -/
theorem graph_clique_supersaturation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r m : ℕ) (hr : 1 ≤ r) (hrm : r + 1 ≤ m) (hmn : m ≤ Fintype.card V)
    (ε : ℝ)
    (hdense : ((1 - 1 / (r : ℝ)) * (m : ℝ) / ((m : ℝ) - 1) + ε) *
        ((Fintype.card V).choose 2 : ℝ) ≤ (G.edgeFinset.card : ℝ)) :
    ε / (m.choose (r + 1) : ℝ) * ((Fintype.card V).choose (r + 1) : ℝ) ≤
      (((Finset.powersetCard (r + 1) (Finset.univ : Finset V)).filter
        (fun C => ∀ u ∈ C, ∀ v ∈ C, u ≠ v → G.Adj u v)).card : ℝ) := by
  -- View G as a 2-uniform hypergraph H on V
  let H : Finset (Finset V) :=
    (Finset.powersetCard 2 (Finset.univ : Finset V)).filter
      (fun e => ∀ u ∈ e, ∀ v ∈ e, u ≠ v → G.Adj u v)
  let Copies : Finset (Finset V) :=
    (Finset.powersetCard (r + 1) (Finset.univ : Finset V)).filter
      (fun C => ∀ u ∈ C, ∀ v ∈ C, u ≠ v → G.Adj u v)
  have hH_card : H.card = G.edgeFinset.card := by
    symm
    refine Finset.card_bij (fun ed _ => ed.toFinset) ?_ ?_ ?_
    · intro ed hed
      induction ed using Sym2.ind with
      | _ x y =>
        have hadj : G.Adj x y := SimpleGraph.mem_edgeFinset.mp hed
        have hxy : x ≠ y := G.ne_of_adj hadj
        have hto : s(x, y).toFinset = {x, y} := by
          ext u; simp [Sym2.mem_toFinset, Sym2.mem_iff]
        rw [hto]
        simp only [H, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
        refine ⟨Finset.card_pair hxy, fun u hu v hv huv => ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
        rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
        · exact absurd rfl huv
        · exact hadj
        · exact (G.adj_comm _ _).mp hadj
        · exact absurd rfl huv
    · intro ed₁ _ ed₂ _ heq
      induction ed₁ using Sym2.ind with
      | _ x₁ y₁ =>
        induction ed₂ using Sym2.ind with
        | _ x₂ y₂ =>
          have h1 : x₁ ∈ s(x₂, y₂) := Sym2.mem_toFinset.mp (heq ▸ Sym2.mem_toFinset.mpr (Sym2.mem_mk_left _ _))
          have h2 : y₁ ∈ s(x₂, y₂) := Sym2.mem_toFinset.mp (heq ▸ Sym2.mem_toFinset.mpr (Sym2.mem_mk_right _ _))
          have h3 : x₂ ∈ s(x₁, y₁) := Sym2.mem_toFinset.mp (heq.symm ▸ Sym2.mem_toFinset.mpr (Sym2.mem_mk_left _ _))
          have h4 : y₂ ∈ s(x₁, y₁) := Sym2.mem_toFinset.mp (heq.symm ▸ Sym2.mem_toFinset.mpr (Sym2.mem_mk_right _ _))
          rw [Sym2.mem_iff] at h1 h2 h3 h4
          rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
          · rcases h4 with rfl | rfl <;> rfl
          · rfl
          · exact Sym2.eq_swap
          · rcases h3 with rfl | rfl <;> rfl
    · intro e he
      have hcard2 : e.card = 2 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2
      rcases Finset.card_eq_two.mp hcard2 with ⟨x, y, hxy, rfl⟩
      have hadj : G.Adj x y := (Finset.mem_filter.mp he).2 x
        (Finset.mem_insert_self x {y}) y (Finset.mem_insert_of_mem (Finset.mem_singleton_self y)) hxy
      refine ⟨s(x, y), SimpleGraph.mem_edgeFinset.mpr hadj, ?_⟩
      ext u; simp [Sym2.mem_toFinset, Sym2.mem_iff]
  set t := Nat.floor ((1 - 1 / (r : ℝ)) * (m : ℝ) ^ 2 / 2)
  have hm2 : 2 ≤ m := by omega
  have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hr)
  have hm_r : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
  have hm1_pos : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  have hcm2 : (m.choose 2 : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
    have hnat : 2 * m.choose 2 = m * (m - 1) := by
      rw [Nat.choose_two_right]
      have hdiv : 2 ∣ m * (m - 1) := Nat.even_mul_pred_self m |>.two_dvd
      exact Nat.mul_div_cancel' hdiv
    have hcast : 2 * (m.choose 2 : ℝ) = (m : ℝ) * ((m : ℝ) - 1) := by
      have hsub : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
        simpa using Nat.cast_sub (R := ℝ) (show 1 ≤ m by omega)
      rw [← hsub]
      exact_mod_cast hnat
    linarith
  have ht_le_real : (t : ℝ) ≤ (1 - 1 / (r : ℝ)) * (m : ℝ) ^ 2 / 2 :=
    Nat.floor_le (by
      have h1 : 1 / (r : ℝ) ≤ 1 := by rw [div_le_one hr_pos]; exact_mod_cast hr
      have : 0 ≤ 1 - 1 / (r : ℝ) := by linarith
      positivity)
  have hdense' : ((t : ℝ) / (m.choose 2 : ℝ) + ε) * ((Fintype.card V).choose 2 : ℝ) ≤ (H.card : ℝ) := by
    rw [hH_card]
    have hcm2_pos : (0 : ℝ) < (m.choose 2 : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos hm2)
    have hfrac_le : (t : ℝ) / (m.choose 2 : ℝ) ≤ (1 - 1 / (r : ℝ)) * (m : ℝ) / ((m : ℝ) - 1) := by
      calc (t : ℝ) / (m.choose 2 : ℝ)
          ≤ ((1 - 1 / (r : ℝ)) * (m : ℝ) ^ 2 / 2) / (m.choose 2 : ℝ) :=
            div_le_div_of_nonneg_right ht_le_real (le_of_lt hcm2_pos)
        _ = (1 - 1 / (r : ℝ)) * (m : ℝ) / ((m : ℝ) - 1) := by
            rw [hcm2]
            field_simp [ne_of_gt (show (0 : ℝ) < (m : ℝ) by linarith), ne_of_gt hm1_pos]
    refine le_trans ?_ hdense
    exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  -- Every m-subset S with |H[S]| > t contains an (r+1)-clique (by turan_theorem on G.induce S!)
  have hcontain : ∀ S ∈ Finset.powersetCard m (Finset.univ : Finset V),
      t < (H.filter (fun e => e ⊆ S)).card → ∃ C ∈ Copies, C ⊆ S := by
    intro S hSP hgt
    have hScard : S.card = m := (Finset.mem_powersetCard.mp hSP).2
    let GS : SimpleGraph S := G.induce (S : Set V)
    have hGS_edges : GS.edgeFinset.card = (H.filter (fun e => e ⊆ S)).card := by
      -- Map each edge of GS (on subtype S) to its 2-element image finset in H[S]
      refine Finset.card_bij (fun ed _ => ed.toFinset.map ⟨Subtype.val, Subtype.val_injective⟩)
        ?_ ?_ ?_
      · intro ed hed
        induction ed using Sym2.ind with
        | _ x y =>
          have hadj : G.Adj x.1 y.1 := SimpleGraph.mem_edgeFinset.mp hed
          have hxy : x ≠ y := fun h => G.loopless.irrefl x.1 (h ▸ hadj)
          have hxy1 : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
          have hmap : s(x, y).toFinset.map ⟨Subtype.val, Subtype.val_injective⟩ = {x.1, y.1} := by
            ext u
            simp only [Finset.mem_map, Sym2.mem_toFinset, Sym2.mem_iff, Function.Embedding.coeFn_mk,
              Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨a, rfl | rfl, rfl⟩ <;> [exact Or.inl rfl; exact Or.inr rfl]
            · rintro (hux | huy)
              · exact ⟨x, Or.inl rfl, hux.symm⟩
              · exact ⟨y, Or.inr rfl, huy.symm⟩
          rw [hmap]
          simp only [H, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
          refine ⟨⟨Finset.card_pair hxy1, fun u hu v hv huv => ?_⟩, ?_⟩
          · simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
            rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
            · exact absurd rfl huv
            · exact hadj
            · exact (G.adj_comm _ _).mp hadj
            · exact absurd rfl huv
          · intro u hu
            simp only [Finset.mem_insert, Finset.mem_singleton] at hu
            rcases hu with rfl | rfl
            · exact x.2
            · exact y.2
      · intro ed₁ _ ed₂ _ heq
        have heq_to : ed₁.toFinset = ed₂.toFinset :=
          Finset.map_injective ⟨Subtype.val, Subtype.val_injective⟩ heq
        induction ed₁ using Sym2.ind with
        | _ x₁ y₁ =>
          induction ed₂ using Sym2.ind with
          | _ x₂ y₂ =>
            have h1 : x₁ ∈ s(x₂, y₂) := Sym2.mem_toFinset.mp (heq_to ▸ Sym2.mem_toFinset.mpr (Sym2.mem_mk_left _ _))
            have h2 : y₁ ∈ s(x₂, y₂) := Sym2.mem_toFinset.mp (heq_to ▸ Sym2.mem_toFinset.mpr (Sym2.mem_mk_right _ _))
            have h3 : x₂ ∈ s(x₁, y₁) := Sym2.mem_toFinset.mp (heq_to.symm ▸ Sym2.mem_toFinset.mpr (Sym2.mem_mk_left _ _))
            have h4 : y₂ ∈ s(x₁, y₁) := Sym2.mem_toFinset.mp (heq_to.symm ▸ Sym2.mem_toFinset.mpr (Sym2.mem_mk_right _ _))
            rw [Sym2.mem_iff] at h1 h2 h3 h4
            rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
            · rcases h4 with rfl | rfl <;> rfl
            · rfl
            · exact Sym2.eq_swap
            · rcases h3 with rfl | rfl <;> rfl
      · intro e he
        rw [Finset.mem_filter] at he
        have heH := he.1
        have heS := he.2
        have hcard2 : e.card = 2 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp heH).1).2
        rcases Finset.card_eq_two.mp hcard2 with ⟨x, y, hxy, rfl⟩
        have hxS : x ∈ S := heS (Finset.mem_insert_self x {y})
        have hyS : y ∈ S := heS (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))
        have hadj : G.Adj x y := (Finset.mem_filter.mp heH).2 x
          (Finset.mem_insert_self x {y}) y (Finset.mem_insert_of_mem (Finset.mem_singleton_self y)) hxy
        refine ⟨s(⟨x, hxS⟩, ⟨y, hyS⟩), SimpleGraph.mem_edgeFinset.mpr hadj, ?_⟩
        ext u
        simp only [Finset.mem_map, Sym2.mem_toFinset, Sym2.mem_iff, Function.Embedding.coeFn_mk,
          Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨a, rfl | rfl, rfl⟩ <;> [exact Or.inl rfl; exact Or.inr rfl]
        · rintro (hux | huy)
          · exact ⟨⟨x, hxS⟩, Or.inl rfl, hux.symm⟩
          · exact ⟨⟨y, hyS⟩, Or.inr rfl, huy.symm⟩
    by_contra hno
    push Not at hno
    have hfree_GS : ∀ C : Finset S, C.card = r + 1 →
        ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ ¬ GS.Adj u v := by
      intro C hCcard
      by_contra hclq
      push Not at hclq
      let C' : Finset V := C.map ⟨Subtype.val, Subtype.val_injective⟩
      have hC'sub : C' ⊆ S := by
        intro u hu
        rcases Finset.mem_map.mp hu with ⟨a, _, rfl⟩
        exact a.2
      have hC'mem : C' ∈ Copies := by
        simp only [Copies, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
        refine ⟨by simp [C', hCcard], fun u hu v hv huv => ?_⟩
        rcases Finset.mem_map.mp hu with ⟨a, ha, rfl⟩
        rcases Finset.mem_map.mp hv with ⟨b, hb, rfl⟩
        exact hclq a ha b hb (fun h => huv (congrArg Subtype.val h))
      exact hno C' hC'mem hC'sub
    have hturan := turan_theorem GS r hr hfree_GS
    rw [Fintype.card_coe, hScard, hGS_edges] at hturan
    have hfloor : (H.filter (fun e => e ⊆ S)).card ≤ t :=
      Nat.le_floor (by exact_mod_cast hturan)
    omega
  exact hypergraph_supersaturation_copies H Copies 2 m (r + 1) t ε
    (fun e he => (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2)
    hm2 hrm hmn
    (fun C hC => (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hC).1).2)
    hcontain hdense'

end Arith4Ext.ProbExtremal
