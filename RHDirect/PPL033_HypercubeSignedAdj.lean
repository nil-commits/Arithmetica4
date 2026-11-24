import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# PPL 033 — Erdős Problem #86 · Hypercube `Q_n` `C₄`-Free Signed-Adjacency Identity & Density Bounds

**Status (Honest Labeling):** This file formalizes a **verified original partial/structural theorem**
toward Erdős Problem #86 (`ex(Q_n, C_4) ≤ (1/2 + o(1)) n 2^{n-1}`), discovered during the PPL 033
campaign. It does **NOT** claim or constitute a resolution of the full Erdős #86 conjecture
(which remains open, with best unconditional asymptotic upper bound `≈ 0.60318 · n 2^{n-1}` due to
Baber 2012).

## Summary of Verified Results

Let `Q_n = hypercube n` be the `n`-dimensional hypercube on `Cube n := Fin n → Bool` (two vertices
adjacent iff they differ in exactly one coordinate), and let `G ≤ Q_n` be a simple subgraph.
A 2-face (2-dimensional subcube / 4-cycle) of `Q_n` is canonically represented by `(v, i, j)` with
`i < j`, `v i = false`, and `v j = false`. Let:
- `N0 G`: number of 2-faces of `Q_n` containing **0** edges of `G` (empty 4-cycles),
- `N2o G`: number of 2-faces of `Q_n` containing **2 opposite (parallel)** edges of `G` (and neither
  of the other 2 edges),
- `N4 G`: number of 2-faces of `Q_n` containing **all 4** edges of `G`.

We prove directly on native Mathlib (`SimpleGraph`, `Fintype`, `Finset`, `Fin n → Bool`):

1. **Hypercube `C₄`-Freeness Characterization (`isC4Free_iff_N4_eq_zero`):**
   For `G ≤ Q_n`, `G` contains no 4-cycle of 4 pairwise distinct vertices iff `N4 G = 0`.
2. **Exact General Signed-Adjacency Identity (`hypercube_signed_adj_identity`):**
   For every subgraph `G ≤ Q_n`:
   `∑ v, (2 * deg_G(v) - n)^2 = n * 2^n + 8 * N0 G + 8 * N4 G - 8 * N2o G` (in `ℤ`).
3. **Exact `C₄`-Free Signed-Adjacency Identity (`hypercube_c4free_signed_adj_identity`,
   `hypercube_c4free_signed_adj_identity_real`):**
   For every `C₄`-free subgraph `G ≤ Q_n`:
   `∑ v, (2 * deg_G(v) - n)^2 = n * 2^n + 8 * N0 G - 8 * N2o G` (in `ℤ` and cast to `ℝ`).
4. **Unconditional Density Corollary for `N0 G ≤ N2o G` (`hypercube_c4free_edge_bound_of_N0_le_N2o`):**
   Whenever `G ≤ Q_n` is `C₄`-free and `N0 G ≤ N2o G` (in particular, whenever `N0 G = 0`, i.e.,
   every empty-4-cycle-free / odd-square `C₄`-free subgraph, `hypercube_c4free_edge_bound_of_no_empty_face`):
   `|E(G)| ≤ (1 / 2 + 1 / (2 * √n)) * n * 2^{n-1}`.
5. **Unconditional General `2/3` Corollary (`hypercube_c4free_edge_bound_two_thirds_nat`,
   `hypercube_c4free_edge_bound_two_thirds`):**
   For EVERY `C₄`-free subgraph `G ≤ Q_n` (no face-count hypothesis):
   `6 * |E(G)| ≤ (2 * n + 1) * 2^n` (exact for `n = 1, 2, 3, 4` giving `1, 3, 9, 24`), and for `n ≥ 1`,
   `|E(G)| ≤ (2 / 3 + 1 / (3 * n)) * n * 2^{n-1}`.
-/

namespace PPL033_HypercubeSignedAdj

open scoped BigOperators
open Finset

/-! ## Section 1: Hypercube `Q_n` and Coordinate Flips -/

/-- Vertex type of the `n`-dimensional hypercube `Q_n`. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- Flip coordinate `i` of a hypercube vertex `v`. -/
def flip {n : ℕ} (v : Cube n) (i : Fin n) : Cube n :=
  Function.update v i (!v i)

@[simp]
lemma flip_apply_self {n : ℕ} (v : Cube n) (i : Fin n) :
    flip v i i = !v i := by
  simp [flip]

@[simp]
lemma flip_apply_ne {n : ℕ} (v : Cube n) {i j : Fin n} (h : j ≠ i) :
    flip v i j = v j := by
  simp [flip, h]

@[simp]
lemma flip_involutive {n : ℕ} (v : Cube n) (i : Fin n) :
    flip (flip v i) i = v := by
  ext k
  by_cases h : k = i
  · subst h; simp [flip]
  · simp [flip, h]

lemma flip_ne_self {n : ℕ} (v : Cube n) (i : Fin n) :
    flip v i ≠ v := by
  intro h
  have hi := congr_fun h i
  simp [flip] at hi

lemma flip_comm {n : ℕ} (v : Cube n) (i j : Fin n) :
    flip (flip v i) j = flip (flip v j) i := by
  ext k
  by_cases hki : k = i
  · subst hki
    by_cases hij : k = j
    · subst hij; simp
    · simp [flip, hij, Ne.symm hij]
  · by_cases hkj : k = j
    · subst hkj; simp [flip, hki, Ne.symm hki]
    · simp [flip, hki, hkj]

lemma flip_eq_flip_iff {n : ℕ} (v : Cube n) (i j : Fin n) :
    flip v i = flip v j ↔ i = j := by
  constructor
  · intro h
    by_contra hij
    have hi := congr_fun h i
    simp [flip, hij] at hi
  · rintro rfl; rfl

lemma flip_inj {n : ℕ} (i : Fin n) : Function.Injective (fun v : Cube n => flip v i) := by
  intro u v h
  have := congr_arg (fun w => flip w i) h
  simpa using this

lemma flip_eq_iff {n : ℕ} (v w : Cube n) (i : Fin n) :
    flip v i = w ↔ v = flip w i := by
  constructor
  · rintro rfl; simp
  · rintro rfl; simp

/-- The `n`-dimensional hypercube graph `Q_n` on `Fin n → Bool`:
two vertices are adjacent iff they differ in exactly one coordinate. -/
def hypercube (n : ℕ) : SimpleGraph (Cube n) where
  Adj u v := ∃ i : Fin n, v = flip u i
  symm := ⟨fun u v h => by
    rcases h with ⟨i, rfl⟩
    exact ⟨i, (flip_involutive u i).symm⟩⟩
  loopless := ⟨fun u h => by
    rcases h with ⟨i, hi⟩
    exact flip_ne_self u i hi.symm⟩

/-- A simple graph `G` is `C₄`-free if it contains no 4-cycle of 4 pairwise distinct vertices.
(Since `G` is loopless, `G.Adj a b`, `G.Adj b c`, `G.Adj c d`, `G.Adj d a` together with
`a ≠ c` and `b ≠ d` automatically imply all 6 pairwise distinctness inequalities.) -/
def IsC4Free {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ a b c d : V,
    a ≠ c → b ≠ d →
    G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a

/-- Equivalence with explicit 6-inequality pairwise distinctness. -/
lemma isC4Free_iff_pairwise_ne {V : Type*} (G : SimpleGraph V) :
    IsC4Free G ↔
      ∀ a b c d : V,
        a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
        G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a := by
  constructor
  · intro h a b c d _ hac _ _ hbd _ hab hbc hcd
    exact h a b c d hac hbd hab hbc hcd
  · intro h a b c d hac hbd hab hbc hcd hda
    exact h a b c d
      (G.ne_of_adj hab) hac (G.ne_of_adj hda).symm
      (G.ne_of_adj hbc) hbd (G.ne_of_adj hcd)
      hab hbc hcd hda

lemma card_cube (n : ℕ) : Fintype.card (Cube n) = 2 ^ n := by
  simp [Cube]

/-! ## Section 2: Degree Representation on Subgraphs `G ≤ Q_n` -/

lemma degree_eq_card_flip {n : ℕ} {G : SimpleGraph (Cube n)} [DecidableRel G.Adj]
    (hG : G ≤ hypercube n) (v : Cube n) :
    G.degree v = (Finset.univ.filter (fun i : Fin n => G.Adj v (flip v i))).card := by
  rw [← G.card_neighborFinset_eq_degree]
  symm
  refine Finset.card_bij (fun i _ => flip v i) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact (G.mem_neighborFinset v (flip v i)).mpr hi
  · intro i₁ _ i₂ _ h
    exact (flip_eq_flip_iff v i₁ i₂).mp h
  · intro w hw
    have hadj : G.Adj v w := (G.mem_neighborFinset v w).mp hw
    obtain ⟨i, rfl⟩ := hG hadj
    exact ⟨i, by simp [hadj], rfl⟩

/-! ## Section 3: 2-Faces (Squares) of `Q_n` and Face Counts `N0`, `N2o`, `N4` -/

/-- Canonical finite set of 2-faces (2-dimensional subcubes) of `Q_n`, represented by triples
`(v, i, j)` with `i < j`, `v i = false`, and `v j = false`.
The 4 vertices of the 2-face are `v`, `flip v i`, `flip v j`, and `flip (flip v i) j`. -/
def faces (n : ℕ) : Finset (Cube n × Fin n × Fin n) :=
  Finset.univ.filter (fun f => f.2.1 < f.2.2 ∧ f.1 f.2.1 = false ∧ f.1 f.2.2 = false)

/-- A 2-face `f = (v, i, j)` has 0 edges in `G` (an empty 4-cycle). -/
def isEmptyFace {n : ℕ} (G : SimpleGraph (Cube n)) (f : Cube n × Fin n × Fin n) : Prop :=
  ¬ G.Adj f.1 (flip f.1 f.2.1) ∧
  ¬ G.Adj (flip f.1 f.2.2) (flip (flip f.1 f.2.2) f.2.1) ∧
  ¬ G.Adj f.1 (flip f.1 f.2.2) ∧
  ¬ G.Adj (flip f.1 f.2.1) (flip (flip f.1 f.2.1) f.2.2)

/-- A 2-face `f = (v, i, j)` has 2 opposite (parallel) edges in `G` and neither of the other 2. -/
def isOppTwoFace {n : ℕ} (G : SimpleGraph (Cube n)) (f : Cube n × Fin n × Fin n) : Prop :=
  (G.Adj f.1 (flip f.1 f.2.1) ∧
    G.Adj (flip f.1 f.2.2) (flip (flip f.1 f.2.2) f.2.1) ∧
    ¬ G.Adj f.1 (flip f.1 f.2.2) ∧
    ¬ G.Adj (flip f.1 f.2.1) (flip (flip f.1 f.2.1) f.2.2)) ∨
  (¬ G.Adj f.1 (flip f.1 f.2.1) ∧
    ¬ G.Adj (flip f.1 f.2.2) (flip (flip f.1 f.2.2) f.2.1) ∧
    G.Adj f.1 (flip f.1 f.2.2) ∧
    G.Adj (flip f.1 f.2.1) (flip (flip f.1 f.2.1) f.2.2))

/-- A 2-face `f = (v, i, j)` has all 4 edges in `G` (forms a `C₄` in `G`). -/
def isFullFace {n : ℕ} (G : SimpleGraph (Cube n)) (f : Cube n × Fin n × Fin n) : Prop :=
  G.Adj f.1 (flip f.1 f.2.1) ∧
  G.Adj (flip f.1 f.2.2) (flip (flip f.1 f.2.2) f.2.1) ∧
  G.Adj f.1 (flip f.1 f.2.2) ∧
  G.Adj (flip f.1 f.2.1) (flip (flip f.1 f.2.1) f.2.2)

instance instDecidablePredIsEmptyFace {n : ℕ} (G : SimpleGraph (Cube n)) [DecidableRel G.Adj] :
    DecidablePred (isEmptyFace G) := fun _ => by
  unfold isEmptyFace; infer_instance

instance instDecidablePredIsOppTwoFace {n : ℕ} (G : SimpleGraph (Cube n)) [DecidableRel G.Adj] :
    DecidablePred (isOppTwoFace G) := fun _ => by
  unfold isOppTwoFace; infer_instance

instance instDecidablePredIsFullFace {n : ℕ} (G : SimpleGraph (Cube n)) [DecidableRel G.Adj] :
    DecidablePred (isFullFace G) := fun _ => by
  unfold isFullFace; infer_instance

/-- Number of empty 2-faces (0 edges in `G`) of `Q_n`. -/
def N0 {n : ℕ} (G : SimpleGraph (Cube n)) [DecidableRel G.Adj] : ℕ :=
  ((faces n).filter (isEmptyFace G)).card

/-- Number of 2-faces of `Q_n` containing exactly 2 opposite (parallel) edges of `G`. -/
def N2o {n : ℕ} (G : SimpleGraph (Cube n)) [DecidableRel G.Adj] : ℕ :=
  ((faces n).filter (isOppTwoFace G)).card

/-- Number of full 2-faces (all 4 edges in `G`) of `Q_n`. -/
def N4 {n : ℕ} (G : SimpleGraph (Cube n)) [DecidableRel G.Adj] : ℕ :=
  ((faces n).filter (isFullFace G)).card

/-- Number of edges of `G` contained in a 2-face `f = (v, i, j)`. -/
def faceEdgeCount {n : ℕ} (G : SimpleGraph (Cube n)) [DecidableRel G.Adj]
    (f : Cube n × Fin n × Fin n) : ℕ :=
  (if G.Adj f.1 (flip f.1 f.2.1) then 1 else 0) +
  (if G.Adj (flip f.1 f.2.2) (flip (flip f.1 f.2.2) f.2.1) then 1 else 0) +
  (if G.Adj f.1 (flip f.1 f.2.2) then 1 else 0) +
  (if G.Adj (flip f.1 f.2.1) (flip (flip f.1 f.2.1) f.2.2) then 1 else 0)

lemma not_isFullFace_of_isC4Free {n : ℕ} {G : SimpleGraph (Cube n)}
    (hC4 : IsC4Free G) {f : Cube n × Fin n × Fin n} (hf : f ∈ faces n) :
    ¬ isFullFace G f := by
  rcases f with ⟨v, i, j⟩
  simp only [faces, Finset.mem_filter, Finset.mem_univ, true_and] at hf
  rcases hf with ⟨hij, _, _⟩
  rintro ⟨h1, h2, h3, h4⟩
  have hij_ne : i ≠ j := ne_of_lt hij
  have hac : v ≠ flip (flip v i) j := by
    intro h
    have hi := congr_fun h i
    simp [flip, hij_ne] at hi
  have hbd : flip v i ≠ flip v j := by
    intro h
    exact hij_ne ((flip_eq_flip_iff v i j).mp h)
  have hcd : G.Adj (flip (flip v i) j) (flip v j) := by
    rw [flip_comm]
    exact (G.adj_comm _ _).mp h2
  have hda : G.Adj (flip v j) v := (G.adj_comm _ _).mp h3
  exact hC4 v (flip v i) (flip (flip v i) j) (flip v j) hac hbd h1 h4 hcd hda

lemma N4_eq_zero_of_isC4Free {n : ℕ} {G : SimpleGraph (Cube n)} [DecidableRel G.Adj]
    (hC4 : IsC4Free G) : N4 G = 0 := by
  unfold N4
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro f hf
  exact not_isFullFace_of_isC4Free hC4 hf

/-- Helper: if a 4-cycle on vertices `v, flip v i, flip (flip v i) j, flip v j` with `i < j`
exists in `G`, then the canonical basepoint of this 2-face yields a full face in `faces n`. -/
private lemma exists_fullFace_of_square {n : ℕ} {G : SimpleGraph (Cube n)}
    {v : Cube n} {i j : Fin n} (hij : i < j)
    (h1 : G.Adj v (flip v i))
    (h2 : G.Adj (flip v j) (flip (flip v j) i))
    (h3 : G.Adj v (flip v j))
    (h4 : G.Adj (flip v i) (flip (flip v i) j)) :
    ∃ f ∈ faces n, isFullFace G f := by
  have hji : j ≠ i := ne_of_gt hij
  have hij_ne : i ≠ j := ne_of_lt hij
  by_cases hvi : v i = false
  · by_cases hvj : v j = false
    · refine ⟨(v, i, j), by simp [faces, hij, hvi, hvj], ⟨h1, h2, h3, h4⟩⟩
    · have hvj' : v j = true := by cases h : v j <;> simp_all
      refine ⟨(flip v j, i, j), ?_, ?_⟩
      · simp [faces, hij, hvi, hvj', hij_ne]
      · refine ⟨h2, ?_, ?_, ?_⟩
        · simpa [flip_involutive] using h1
        · simpa [flip_involutive] using (G.adj_comm _ _).mp h3
        · rw [flip_comm]
          simpa [flip_involutive] using (G.adj_comm _ _).mp h4
  · have hvi' : v i = true := by cases h : v i <;> simp_all
    by_cases hvj : v j = false
    · refine ⟨(flip v i, i, j), ?_, ?_⟩
      · simp [faces, hij, hvi', hvj, hji]
      · refine ⟨?_, ?_, h4, ?_⟩
        · simpa [flip_involutive] using (G.adj_comm _ _).mp h1
        · rw [flip_comm]
          simpa [flip_involutive] using (G.adj_comm _ _).mp h2
        · simpa [flip_involutive] using h3
    · have hvj' : v j = true := by cases h : v j <;> simp_all
      refine ⟨(flip (flip v i) j, i, j), ?_, ?_⟩
      · simp [faces, hij, hvi', hvj', hij_ne, hji]
      · refine ⟨?_, ?_, ?_, ?_⟩
        · rw [flip_comm (flip v i) j i, flip_involutive, flip_comm]
          exact (G.adj_comm _ _).mp h2
        · rw [flip_involutive, flip_involutive]
          exact (G.adj_comm _ _).mp h1
        · rw [flip_involutive]
          exact (G.adj_comm _ _).mp h4
        · rw [flip_comm (flip v i) j i, flip_involutive, flip_involutive]
          exact (G.adj_comm _ _).mp h3

/-- For any subgraph `G ≤ Q_n`, `G` is `C₄`-free iff it has no full 2-face (`N4 G = 0`). -/
theorem isC4Free_iff_N4_eq_zero {n : ℕ} {G : SimpleGraph (Cube n)} [DecidableRel G.Adj]
    (hG : G ≤ hypercube n) :
    IsC4Free G ↔ N4 G = 0 := by
  constructor
  · exact N4_eq_zero_of_isC4Free
  · intro hN4 a b c d hac hbd hab hbc hcd hda
    obtain ⟨i, rfl⟩ := hG hab
    obtain ⟨j, rfl⟩ := hG hbc
    obtain ⟨k, rfl⟩ := hG hcd
    obtain ⟨l, hl⟩ := hG hda
    have hij_ne : i ≠ j := by
      rintro rfl
      exact hac (flip_involutive a i).symm
    have hd_eq : flip (flip (flip a i) j) k = flip a l := (flip_eq_iff _ _ l).mp hl.symm
    have hc_eq : flip (flip a i) j = flip (flip a l) k := by
      have := congr_arg (fun w => flip w k) hd_eq
      simpa using this
    have hi_in : i = l ∨ i = k := by
      by_contra h
      push Not at h
      have h1 := congr_fun hc_eq i
      simp [flip, hij_ne, h.1, h.2] at h1
    have hj_in : j = l ∨ j = k := by
      by_contra h
      push Not at h
      have h1 := congr_fun hc_eq j
      simp [flip, hij_ne.symm, h.1, h.2] at h1
    have hl_ne_i : l ≠ i := by
      rintro rfl
      exact hbd hd_eq.symm
    have hli : i = k := by
      rcases hi_in with rfl | h
      · exact absurd rfl hl_ne_i
      · exact h
    have hlj : j = l := by
      rcases hj_in with h | h
      · exact h
      · exact absurd (h.trans hli.symm) hij_ne.symm
    subst hli; subst hlj
    have h1 : G.Adj a (flip a i) := hab
    have h4 : G.Adj (flip a i) (flip (flip a i) j) := hbc
    have h2 : G.Adj (flip a j) (flip (flip a j) i) := by
      have : G.Adj (flip (flip a j) i) (flip a j) := by
        rw [← flip_comm]
        simpa [hd_eq] using hcd
      exact (G.adj_comm _ _).mp this
    have h3 : G.Adj a (flip a j) := by
      simpa [hd_eq] using (G.adj_comm _ _).mp hda
    have hex : ∃ f ∈ faces n, isFullFace G f := by
      rcases lt_or_gt_of_ne hij_ne with hij | hji
      · exact exists_fullFace_of_square hij h1 h2 h3 h4
      · exact exists_fullFace_of_square hji h3 h4 h1 h2
    rcases hex with ⟨f, hf, hfull⟩
    have hpos : 0 < N4 G := Finset.card_pos.mpr ⟨f, Finset.mem_filter.mpr ⟨hf, hfull⟩⟩
    omega

/-! ## Section 4: 4-Corner Partitioning of `Q_n` and Exact Signed-Adjacency Identity -/

/-- Signed adjacency weight `y(v, i) ∈ {-1, +1}` of the `Q_n`-edge `(v, flip v i)` in `G`. -/
def y {n : ℕ} (G : SimpleGraph (Cube n)) [DecidableRel G.Adj] (v : Cube n) (i : Fin n) : ℤ :=
  if G.Adj v (flip v i) then 1 else -1

lemma y_sq {n : ℕ} (G : SimpleGraph (Cube n)) [DecidableRel G.Adj] (v : Cube n) (i : Fin n) :
    y G v i * y G v i = 1 := by
  unfold y
  split_ifs <;> norm_num

lemma y_flip_self {n : ℕ} (G : SimpleGraph (Cube n)) [DecidableRel G.Adj] (v : Cube n) (i : Fin n) :
    y G (flip v i) i = y G v i := by
  simp only [y, flip_involutive, G.adj_comm]

lemma sum_y_eq_two_deg_sub_n {n : ℕ} {G : SimpleGraph (Cube n)} [DecidableRel G.Adj]
    (hG : G ≤ hypercube n) (v : Cube n) :
    ∑ i : Fin n, y G v i = 2 * (G.degree v : ℤ) - (n : ℤ) := by
  have hy : ∀ i : Fin n, y G v i = (if G.Adj v (flip v i) then (2 : ℤ) else 0) - 1 := by
    intro i; unfold y; split_ifs <;> norm_num
  simp_rw [hy, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    degree_eq_card_flip hG v]
  ring

/-- Partition `Cube n` into the 4 corners of all 2-faces with fixed directions `i ≠ j`. -/
lemma sum_cube_eq_sum_four_corners {n : ℕ} {M : Type*} [AddCommMonoid M]
    {i j : Fin n} (hij : i ≠ j) (g : Cube n → M) :
    ∑ v : Cube n, g v =
      ∑ v ∈ Finset.univ.filter (fun v : Cube n => v i = false ∧ v j = false),
        (g v + g (flip v i) + g (flip v j) + g (flip (flip v i) j)) := by
  let S00 := Finset.univ.filter (fun v : Cube n => v i = false ∧ v j = false)
  let S10 := Finset.univ.filter (fun v : Cube n => v i = true ∧ v j = false)
  let S01 := Finset.univ.filter (fun v : Cube n => v i = false ∧ v j = true)
  let S11 := Finset.univ.filter (fun v : Cube n => v i = true ∧ v j = true)
  have hpart :
      ∑ v : Cube n, g v =
        (∑ v ∈ S00, g v) + (∑ v ∈ S10, g v) + (∑ v ∈ S01, g v) + (∑ v ∈ S11, g v) := by
    have hsplit1 :
        ∑ v : Cube n, g v =
          (∑ v ∈ Finset.univ.filter (fun v : Cube n => v i = false), g v) +
          (∑ v ∈ Finset.univ.filter (fun v : Cube n => v i = true), g v) := by
      have := (Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Cube n))
        (fun v : Cube n => v i = false) g).symm
      convert this using 2
      congr 1; ext v; cases v i <;> simp
    have hsplit2 :
        ∑ v ∈ Finset.univ.filter (fun v : Cube n => v i = false), g v =
          (∑ v ∈ S00, g v) + (∑ v ∈ S01, g v) := by
      have h := (Finset.sum_filter_add_sum_filter_not
        (Finset.univ.filter (fun v : Cube n => v i = false))
        (fun v : Cube n => v j = false) g).symm
      have hf1 : (Finset.univ.filter (fun v : Cube n => v i = false)).filter
          (fun v : Cube n => v j = false) = S00 := by
        ext v; simp [S00]
      have hf2 : (Finset.univ.filter (fun v : Cube n => v i = false)).filter
          (fun v : Cube n => ¬ v j = false) = S01 := by
        ext v; cases v j <;> simp [S01]
      rw [hf1, hf2] at h
      exact h
    have hsplit3 :
        ∑ v ∈ Finset.univ.filter (fun v : Cube n => v i = true), g v =
          (∑ v ∈ S10, g v) + (∑ v ∈ S11, g v) := by
      have h := (Finset.sum_filter_add_sum_filter_not
        (Finset.univ.filter (fun v : Cube n => v i = true))
        (fun v : Cube n => v j = false) g).symm
      have hf1 : (Finset.univ.filter (fun v : Cube n => v i = true)).filter
          (fun v : Cube n => v j = false) = S10 := by
        ext v; simp [S10]
      have hf2 : (Finset.univ.filter (fun v : Cube n => v i = true)).filter
          (fun v : Cube n => ¬ v j = false) = S11 := by
        ext v; cases v j <;> simp [S11]
      rw [hf1, hf2] at h
      exact h
    rw [hsplit1, hsplit2, hsplit3]
    simp only [add_assoc]
    ac_rfl
  have h10 : ∑ v ∈ S10, g v = ∑ v ∈ S00, g (flip v i) := by
    symm
    refine Finset.sum_bij (fun v _ => flip v i) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro v hv
      simp only [S00, S10, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact ⟨by simp [hv.1], by simp [flip_apply_ne v hij.symm, hv.2]⟩
    · intro u _ v _ h; exact flip_inj i h
    · intro w hw
      simp only [S10, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      refine ⟨flip w i, ?_, by simp⟩
      simp only [S00, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by simp [hw.1], by simp [flip_apply_ne w hij.symm, hw.2]⟩
  have h01 : ∑ v ∈ S01, g v = ∑ v ∈ S00, g (flip v j) := by
    symm
    refine Finset.sum_bij (fun v _ => flip v j) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro v hv
      simp only [S00, S01, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact ⟨by simp [flip_apply_ne v hij, hv.1], by simp [hv.2]⟩
    · intro u _ v _ h; exact flip_inj j h
    · intro w hw
      simp only [S01, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      refine ⟨flip w j, ?_, by simp⟩
      simp only [S00, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by simp [flip_apply_ne w hij, hw.1], by simp [hw.2]⟩
  have h11 : ∑ v ∈ S11, g v = ∑ v ∈ S00, g (flip (flip v i) j) := by
    symm
    refine Finset.sum_bij (fun v _ => flip (flip v i) j) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro v hv
      simp only [S00, S11, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact ⟨by simp [flip_apply_ne _ hij, hv.1], by simp [flip_apply_ne _ hij.symm, hv.2]⟩
    · intro u _ v _ h; exact flip_inj i (flip_inj j h)
    · intro w hw
      simp only [S11, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      refine ⟨flip (flip w j) i, ?_, ?_⟩
      · simp only [S00, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨by simp [flip_apply_ne _ hij, hw.1], by simp [flip_apply_ne _ hij.symm, hw.2]⟩
      · rw [flip_involutive, flip_involutive]
  rw [hpart, h10, h01, h11]
  simp only [S00, Finset.sum_add_distrib]

/-- Symmetric double sum over `Fin n × Fin n` splits into diagonal plus twice upper-triangular. -/
lemma sum_fin_pair_symm {n : ℕ} (f : Fin n → Fin n → ℤ)
    (hsymm : ∀ i j, f i j = f j i) :
    ∑ i : Fin n, ∑ j : Fin n, f i j =
      (∑ i : Fin n, f i i) +
      2 * ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), f i j := by
  have h1 : ∀ i : Fin n,
      ∑ j : Fin n, f i j =
        f i i +
        (∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), f i j) +
        (∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i), f i j) := by
    intro i
    have hne :
        ∑ j : Fin n, f i j =
          f i i + ∑ j ∈ Finset.univ.filter (fun j : Fin n => j ≠ i), f i j := by
      have := (Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin n))
        (fun j : Fin n => j = i) (f i)).symm
      rw [this]
      congr 1
      have : Finset.univ.filter (fun j : Fin n => j = i) = {i} := by ext j; simp
      rw [this, Finset.sum_singleton]
    rw [hne]
    have hlt :
        ∑ j ∈ Finset.univ.filter (fun j : Fin n => j ≠ i), f i j =
          (∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), f i j) +
          (∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i), f i j) := by
      have h := (Finset.sum_filter_add_sum_filter_not
        (Finset.univ.filter (fun j : Fin n => j ≠ i))
        (fun j : Fin n => i < j) (f i)).symm
      have hf1 : (Finset.univ.filter (fun j : Fin n => j ≠ i)).filter
          (fun j : Fin n => i < j) = Finset.univ.filter (fun j : Fin n => i < j) := by
        ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => h.2, fun h => ⟨ne_of_gt h, h⟩⟩
      have hf2 : (Finset.univ.filter (fun j : Fin n => j ≠ i)).filter
          (fun j : Fin n => ¬ i < j) = Finset.univ.filter (fun j : Fin n => j < i) := by
        ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
        exact ⟨fun ⟨hne', hle⟩ => lt_of_le_of_ne hle hne', fun h => ⟨ne_of_lt h, le_of_lt h⟩⟩
      rw [hf1, hf2] at h
      exact h
    rw [hlt]; ring
  simp_rw [h1, Finset.sum_add_distrib]
  have hswap :
      ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => j < i), f i j =
      ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), f i j := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    split_ifs <;> simp [hsymm]
  rw [hswap]; ring

/-- Reindexing nested sums over `i < j` and `v i = false ∧ v j = false` as a sum over `faces n`. -/
lemma sum_faces_eq_nested {n : ℕ} {M : Type*} [AddCommMonoid M]
    (h : Cube n × Fin n × Fin n → M) :
    ∑ f ∈ faces n, h f =
      ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
        ∑ v ∈ Finset.univ.filter (fun v : Cube n => v i = false ∧ v j = false), h (v, i, j) := by
  unfold faces
  rw [Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases hij : i < j
  · simp [hij, Finset.sum_filter]
  · simp [hij]

/-- Exact signed contribution of a single 2-face `(v, i, j)` to `2 * ∑_u y(u, i) y(u, j)`. -/
lemma face_signed_contrib {n : ℕ} (G : SimpleGraph (Cube n)) [DecidableRel G.Adj]
    (v : Cube n) (i j : Fin n) :
    2 * (y G v i + y G (flip v j) i) * (y G v j + y G (flip v i) j) =
      (if isEmptyFace G (v, i, j) then (8 : ℤ) else 0) +
      (if isFullFace G (v, i, j) then (8 : ℤ) else 0) -
      (if isOppTwoFace G (v, i, j) then (8 : ℤ) else 0) := by
  unfold y isEmptyFace isFullFace isOppTwoFace
  by_cases h1 : G.Adj v (flip v i) <;>
  by_cases h2 : G.Adj (flip v j) (flip (flip v j) i) <;>
  by_cases h3 : G.Adj v (flip v j) <;>
  by_cases h4 : G.Adj (flip v i) (flip (flip v i) j) <;>
  simp [h1, h2, h3, h4]

/-- **Exact General Signed-Adjacency Identity on `Q_n`:**
For EVERY subgraph `G ≤ Q_n` (even without assuming `C₄`-freeness):
`∑ v : Cube n, (2 * deg_G(v) - n)^2 = n * 2^n + 8 * N0 G + 8 * N4 G - 8 * N2o G`. -/
theorem hypercube_signed_adj_identity {n : ℕ} (G : SimpleGraph (Cube n)) [DecidableRel G.Adj]
    (hG : G ≤ hypercube n) :
    ∑ v : Cube n, (2 * (G.degree v : ℤ) - (n : ℤ)) ^ 2 =
      (n : ℤ) * 2 ^ n + 8 * (N0 G : ℤ) + 8 * (N4 G : ℤ) - 8 * (N2o G : ℤ) := by
  have h1 :
      ∑ v : Cube n, (2 * (G.degree v : ℤ) - (n : ℤ)) ^ 2 =
        ∑ i : Fin n, ∑ j : Fin n, ∑ v : Cube n, y G v i * y G v j := by
    simp_rw [← sum_y_eq_two_deg_sub_n hG, sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_comm]
  rw [h1]
  rw [sum_fin_pair_symm (fun i j => ∑ v : Cube n, y G v i * y G v j)
    (fun i j => Finset.sum_congr rfl (fun v _ => mul_comm _ _))]
  have hdiag :
      ∑ i : Fin n, ∑ v : Cube n, y G v i * y G v i = (n : ℤ) * 2 ^ n := by
    simp_rw [y_sq, Finset.sum_const, Finset.card_univ, card_cube, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
    norm_cast
  have hoff :
      2 * ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
          ∑ v : Cube n, y G v i * y G v j =
        8 * (N0 G : ℤ) + 8 * (N4 G : ℤ) - 8 * (N2o G : ℤ) := by
    have hinner :
        ∀ i : Fin n, ∀ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
          ∑ v : Cube n, y G v i * y G v j =
            ∑ v ∈ Finset.univ.filter (fun v : Cube n => v i = false ∧ v j = false),
              (y G v i + y G (flip v j) i) * (y G v j + y G (flip v i) j) := by
      intro i j hj
      have hij : i ≠ j := ne_of_lt (Finset.mem_filter.mp hj).2
      rw [sum_cube_eq_sum_four_corners hij (fun v => y G v i * y G v j)]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      have h_vi_i : y G (flip v i) i = y G v i := y_flip_self G v i
      have h_vj_j : y G (flip v j) j = y G v j := y_flip_self G v j
      have h_vij_i : y G (flip (flip v i) j) i = y G (flip v j) i := by
        rw [flip_comm, y_flip_self]
      have h_vij_j : y G (flip (flip v i) j) j = y G (flip v i) j := y_flip_self G (flip v i) j
      rw [h_vi_i, h_vj_j, h_vij_i, h_vij_j]
      ring
    calc
      2 * ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
            ∑ v : Cube n, y G v i * y G v j
          = ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
              ∑ v ∈ Finset.univ.filter (fun v : Cube n => v i = false ∧ v j = false),
                2 * (y G v i + y G (flip v j) i) * (y G v j + y G (flip v i) j) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun j hj => ?_)
            rw [hinner i j hj, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun v _ => by ring)
      _ = ∑ f ∈ faces n,
            2 * (y G f.1 f.2.1 + y G (flip f.1 f.2.2) f.2.1) *
              (y G f.1 f.2.2 + y G (flip f.1 f.2.1) f.2.2) := by
            rw [sum_faces_eq_nested]
      _ = ∑ f ∈ faces n,
            ((if isEmptyFace G f then (8 : ℤ) else 0) +
             (if isFullFace G f then (8 : ℤ) else 0) -
             (if isOppTwoFace G f then (8 : ℤ) else 0)) := by
            refine Finset.sum_congr rfl (fun f _ => face_signed_contrib G f.1 f.2.1 f.2.2)
      _ = 8 * (N0 G : ℤ) + 8 * (N4 G : ℤ) - 8 * (N2o G : ℤ) := by
            simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite,
              Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, N0, N4, N2o]
            ring
  rw [hdiag, hoff]
  ring

/-- **Main Structural Theorem 1 (`hypercube_c4free_signed_adj_identity`, in `ℤ`):**
For every `C₄`-free subgraph `G ≤ Q_n`:
`∑ v : Cube n, (2 * deg_G(v) - n)^2 = n * 2^n + 8 * N0 G - 8 * N2o G`. -/
theorem hypercube_c4free_signed_adj_identity {n : ℕ}
    (G : SimpleGraph (Cube n)) [DecidableRel G.Adj]
    (hG : G ≤ hypercube n) (hC4 : IsC4Free G) :
    ∑ v : Cube n, (2 * (G.degree v : ℤ) - (n : ℤ)) ^ 2 =
      (n : ℤ) * 2 ^ n + 8 * (N0 G : ℤ) - 8 * (N2o G : ℤ) := by
  have h := hypercube_signed_adj_identity G hG
  rw [N4_eq_zero_of_isC4Free hC4] at h
  simpa using h

/-- Real-valued version of `hypercube_c4free_signed_adj_identity`. -/
theorem hypercube_c4free_signed_adj_identity_real {n : ℕ}
    (G : SimpleGraph (Cube n)) [DecidableRel G.Adj]
    (hG : G ≤ hypercube n) (hC4 : IsC4Free G) :
    ∑ v : Cube n, (2 * (G.degree v : ℝ) - (n : ℝ)) ^ 2 =
      (n : ℝ) * (2 : ℝ) ^ n + 8 * (N0 G : ℝ) - 8 * (N2o G : ℝ) := by
  have h := hypercube_c4free_signed_adj_identity G hG hC4
  exact_mod_cast h

/-! ## Section 5: Cauchy–Schwarz & Unconditional Density Corollary for `N0 G ≤ N2o G` -/

/-- Self-contained discrete Cauchy–Schwarz over `ℤ`:
`(∑ x ∈ s, f x)^2 ≤ |s| * ∑ x ∈ s, (f x)^2`. -/
lemma sq_sum_le_card_mul_sum_sq_int {α : Type*} (s : Finset α) (f : α → ℤ) :
    (∑ x ∈ s, f x) ^ 2 ≤ (s.card : ℤ) * ∑ x ∈ s, (f x) ^ 2 := by
  have hnonneg : 0 ≤ ∑ x ∈ s, ∑ y ∈ s, (f x - f y) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hexp :
      ∑ x ∈ s, ∑ y ∈ s, (f x - f y) ^ 2 =
        2 * ((s.card : ℤ) * ∑ x ∈ s, (f x) ^ 2 - (∑ x ∈ s, f x) ^ 2) := by
    have h1 : ∀ x y : α, (f x - f y) ^ 2 = (f x) ^ 2 - 2 * (f x * f y) + (f y) ^ 2 := by
      intro x y; ring
    simp_rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, ← Finset.sum_mul, sq]
    ring
  linarith

lemma sum_two_deg_sub_n {n : ℕ} (G : SimpleGraph (Cube n)) [DecidableRel G.Adj] :
    ∑ v : Cube n, (2 * (G.degree v : ℤ) - (n : ℤ)) =
      4 * (G.edgeFinset.card : ℤ) - (n : ℤ) * 2 ^ n := by
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    card_cube, nsmul_eq_mul]
  have hhand : (∑ v : Cube n, (G.degree v : ℤ)) = 2 * (G.edgeFinset.card : ℤ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  rw [hhand]
  norm_cast
  ring

/-- Exact Cauchy–Schwarz bound on the edge imbalance `4 |E(G)| - n 2^n` for any `C₄`-free
subgraph `G ≤ Q_n` in terms of `N0 G - N2o G`. -/
lemma hypercube_c4free_cs_edge_bound {n : ℕ}
    (G : SimpleGraph (Cube n)) [DecidableRel G.Adj]
    (hG : G ≤ hypercube n) (hC4 : IsC4Free G) :
    (4 * (G.edgeFinset.card : ℤ) - (n : ℤ) * 2 ^ n) ^ 2 ≤
      (2 : ℤ) ^ n * ((n : ℤ) * 2 ^ n + 8 * (N0 G : ℤ) - 8 * (N2o G : ℤ)) := by
  have hCS := sq_sum_le_card_mul_sum_sq_int (Finset.univ : Finset (Cube n))
    (fun v => 2 * (G.degree v : ℤ) - (n : ℤ))
  rw [sum_two_deg_sub_n G, Finset.card_univ, card_cube,
    hypercube_c4free_signed_adj_identity G hG hC4] at hCS
  exact_mod_cast hCS

/-- Integer square form of the `N0 G ≤ N2o G` density bound (valid for all `n : ℕ`). -/
theorem hypercube_c4free_sq_edge_bound_of_N0_le_N2o {n : ℕ}
    (G : SimpleGraph (Cube n)) [DecidableRel G.Adj]
    (hG : G ≤ hypercube n) (hC4 : IsC4Free G) (hN : N0 G ≤ N2o G) :
    (4 * (G.edgeFinset.card : ℤ) - (n : ℤ) * 2 ^ n) ^ 2 ≤ (n : ℤ) * ((2 : ℤ) ^ n) ^ 2 := by
  have hCS := hypercube_c4free_cs_edge_bound G hG hC4
  have hN' : (N0 G : ℤ) ≤ (N2o G : ℤ) := Nat.cast_le.mpr hN
  have h2pos : (0 : ℤ) ≤ (2 : ℤ) ^ n := by positivity
  have hstep :
      (2 : ℤ) ^ n * ((n : ℤ) * 2 ^ n + 8 * (N0 G : ℤ) - 8 * (N2o G : ℤ)) ≤
        (2 : ℤ) ^ n * ((n : ℤ) * 2 ^ n) := by
    apply mul_le_mul_of_nonneg_left _ h2pos
    linarith
  have heq : (2 : ℤ) ^ n * ((n : ℤ) * 2 ^ n) = (n : ℤ) * ((2 : ℤ) ^ n) ^ 2 := by ring
  linarith

/-- **Main Structural Theorem 2 (`hypercube_c4free_edge_bound_of_N0_le_N2o`):**
Whenever `G ≤ Q_n` is `C₄`-free and `N0 G ≤ N2o G`,
`|E(G)| ≤ (1 / 2 + 1 / (2 * √n)) * n * 2^{n - 1}`.
(Holds unconditionally for all `n : ℕ`; at `n = 0`, both sides equal `0`.) -/
theorem hypercube_c4free_edge_bound_of_N0_le_N2o {n : ℕ}
    (G : SimpleGraph (Cube n)) [DecidableRel G.Adj]
    (hG : G ≤ hypercube n) (hC4 : IsC4Free G) (hN : N0 G ≤ N2o G) :
    (G.edgeFinset.card : ℝ) ≤
      (1 / 2 + 1 / (2 * Real.sqrt (n : ℝ))) * (n : ℝ) * (2 : ℝ) ^ (n - 1) := by
  have hsqZ := hypercube_c4free_sq_edge_bound_of_N0_le_N2o G hG hC4 hN
  have hsqR :
      (4 * (G.edgeFinset.card : ℝ) - (n : ℝ) * (2 : ℝ) ^ n) ^ 2 ≤
        (n : ℝ) * ((2 : ℝ) ^ n) ^ 2 := by
    exact_mod_cast hsqZ
  cases n with
  | zero =>
    simp only [Nat.cast_zero, pow_zero, zero_mul, sub_zero, mul_one, mul_zero] at hsqR ⊢
    have hE0 : (G.edgeFinset.card : ℝ) = 0 := by nlinarith
    linarith
  | succ m =>
    have hk_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    have hsqrt_pos : 0 < Real.sqrt ((m + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hk_pos
    have hsqrt_sq : Real.sqrt ((m + 1 : ℕ) : ℝ) ^ 2 = ((m + 1 : ℕ) : ℝ) :=
      Real.sq_sqrt (le_of_lt hk_pos)
    have hr_nonneg : 0 ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (m + 1) := by positivity
    have hlin :
        4 * (G.edgeFinset.card : ℝ) - ((m + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (m + 1) ≤
          Real.sqrt ((m + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (m + 1) := by
      by_contra hlt
      push Not at hlt
      have : (Real.sqrt ((m + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (m + 1)) ^ 2 <
          (4 * (G.edgeFinset.card : ℝ) - ((m + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (m + 1)) ^ 2 := by
        nlinarith
      have hr2 : (Real.sqrt ((m + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (m + 1)) ^ 2 =
          ((m + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (m + 1)) ^ 2 := by
        calc
          (Real.sqrt ((m + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (m + 1)) ^ 2
              = Real.sqrt ((m + 1 : ℕ) : ℝ) ^ 2 * ((2 : ℝ) ^ (m + 1)) ^ 2 := by ring
          _ = ((m + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ (m + 1)) ^ 2 := by rw [hsqrt_sq]
      linarith
    have hpow : (2 : ℝ) ^ (m + 1) = 2 * (2 : ℝ) ^ m := by
      rw [pow_succ, mul_comm]
    have hsqrt_div : ((m + 1 : ℕ) : ℝ) / Real.sqrt ((m + 1 : ℕ) : ℝ) =
        Real.sqrt ((m + 1 : ℕ) : ℝ) := by
      rw [div_eq_iff (ne_of_gt hsqrt_pos)]
      linarith [Real.mul_self_sqrt (le_of_lt hk_pos)]
    have hrhs :
        (1 / 2 + 1 / (2 * Real.sqrt ((m + 1 : ℕ) : ℝ))) * ((m + 1 : ℕ) : ℝ) *
            (2 : ℝ) ^ ((m + 1) - 1) =
          (((m + 1 : ℕ) : ℝ) + Real.sqrt ((m + 1 : ℕ) : ℝ)) * (2 : ℝ) ^ (m + 1) / 4 := by
      rw [Nat.add_sub_cancel, hpow]
      have : (1 / 2 + 1 / (2 * Real.sqrt ((m + 1 : ℕ) : ℝ))) * ((m + 1 : ℕ) : ℝ) * (2 : ℝ) ^ m =
          (((m + 1 : ℕ) : ℝ) / 2 + (((m + 1 : ℕ) : ℝ) / Real.sqrt ((m + 1 : ℕ) : ℝ)) / 2) *
            (2 : ℝ) ^ m := by
        ring
      rw [this, hsqrt_div]
      ring
    rw [hrhs]
    linarith

/-- Immediate corollary for empty-4-cycle-free (in particular, odd-square) `C₄`-free subgraphs
of `Q_n` (`N0 G = 0`). -/
theorem hypercube_c4free_edge_bound_of_no_empty_face {n : ℕ}
    (G : SimpleGraph (Cube n)) [DecidableRel G.Adj]
    (hG : G ≤ hypercube n) (hC4 : IsC4Free G) (hN0 : N0 G = 0) :
    (G.edgeFinset.card : ℝ) ≤
      (1 / 2 + 1 / (2 * Real.sqrt (n : ℝ))) * (n : ℝ) * (2 : ℝ) ^ (n - 1) :=
  hypercube_c4free_edge_bound_of_N0_le_N2o G hG hC4 (by omega)

/-! ## Section 6: Face-Edge Double Counting & Unconditional General `2/3` Corollary -/

/-- Exact total count of 2-faces in `Q_n`: `8 * |faces n| = n * (n - 1) * 2^n` (in `ℤ`). -/
lemma eight_mul_card_faces {n : ℕ} :
    8 * ((faces n).card : ℤ) = (n : ℤ) * ((n : ℤ) - 1) * (2 : ℤ) ^ n := by
  have hS00 : ∀ i j : Fin n, i ≠ j →
      4 * ((Finset.univ.filter (fun v : Cube n => v i = false ∧ v j = false)).card : ℤ) =
        (2 : ℤ) ^ n := by
    intro i j hij
    have h := sum_cube_eq_sum_four_corners hij (fun _ : Cube n => (1 : ℤ))
    simp only [Finset.sum_const, Finset.card_univ, card_cube, nsmul_eq_mul, mul_one] at h
    have h4 : (1 : ℤ) + 1 + 1 + 1 = 4 := by norm_num
    rw [h4] at h
    have h2 : ((2 ^ n : ℕ) : ℤ) = (2 : ℤ) ^ n := by norm_cast
    linarith
  have hpairs :
      2 * (∑ i : Fin n, ((Finset.univ.filter (fun j : Fin n => i < j)).card : ℤ)) =
        (n : ℤ) * ((n : ℤ) - 1) := by
    have hsym := sum_fin_pair_symm (fun i j : Fin n => if i = j then (0 : ℤ) else 1)
      (fun i j => by by_cases h : i = j <;> simp [h, eq_comm])
    have hlhs :
        ∑ i : Fin n, ∑ j : Fin n, (if i = j then (0 : ℤ) else 1) =
          (n : ℤ) * ((n : ℤ) - 1) := by
      have hsub : ∀ i j : Fin n,
          (if i = j then (0 : ℤ) else 1) = 1 - (if i = j then (1 : ℤ) else 0) := by
        intro i j; split_ifs <;> norm_num
      simp_rw [hsub, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
      have hdiag : ∀ i : Fin n, ∑ j : Fin n, (if i = j then (1 : ℤ) else 0) = 1 := by
        intro i; simp
      simp_rw [hdiag, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      ring
    have hdiag0 : ∑ i : Fin n, (if i = i then (0 : ℤ) else 1) = 0 := by simp
    have hup :
        ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
            (if i = j then (0 : ℤ) else 1) =
          ∑ i : Fin n, ((Finset.univ.filter (fun j : Fin n => i < j)).card : ℤ) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have : ∀ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
          (if i = j then (0 : ℤ) else 1) = 1 := by
        intro j hj
        have hij : i ≠ j := ne_of_lt (Finset.mem_filter.mp hj).2
        simp [hij]
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one]
    linarith
  have h4faces :
      4 * ((faces n).card : ℤ) =
        (∑ i : Fin n, ((Finset.univ.filter (fun j : Fin n => i < j)).card : ℤ)) * (2 : ℤ) ^ n := by
    have h := sum_faces_eq_nested (n := n) (fun _ => (4 : ℤ))
    simp only [Finset.sum_const, nsmul_eq_mul] at h
    rw [Finset.sum_mul]
    calc
      4 * ((faces n).card : ℤ) = ((faces n).card : ℤ) * 4 := by ring
      _ = ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
            ((Finset.univ.filter (fun v : Cube n => v i = false ∧ v j = false)).card : ℤ) * 4 := h
      _ = ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j), (2 : ℤ) ^ n := by
            refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j hj => ?_))
            have hij : i ≠ j := ne_of_lt (Finset.mem_filter.mp hj).2
            linarith [hS00 i j hij]
      _ = ∑ i : Fin n, ((Finset.univ.filter (fun j : Fin n => i < j)).card : ℤ) * (2 : ℤ) ^ n := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            simp [Finset.sum_const]
  calc
    8 * ((faces n).card : ℤ) = 2 * (4 * ((faces n).card : ℤ)) := by ring
    _ = (2 * ∑ i : Fin n, ((Finset.univ.filter (fun j : Fin n => i < j)).card : ℤ)) *
          (2 : ℤ) ^ n := by rw [h4faces]; ring
    _ = (n : ℤ) * ((n : ℤ) - 1) * (2 : ℤ) ^ n := by rw [hpairs]

/-- Face-edge incidence double counting on `Q_n`: every edge of `G` belongs to exactly `n - 1`
2-faces, so `∑ f ∈ faces n, faceEdgeCount G f = (n - 1) * |E(G)|` (in `ℤ`). -/
lemma sum_faceEdgeCount {n : ℕ} (G : SimpleGraph (Cube n)) [DecidableRel G.Adj]
    (hG : G ≤ hypercube n) :
    ∑ f ∈ faces n, (faceEdgeCount G f : ℤ) = ((n : ℤ) - 1) * (G.edgeFinset.card : ℤ) := by
  let e : Cube n → Fin n → ℤ := fun u d => if G.Adj u (flip u d) then 1 else 0
  have he_flip : ∀ u : Cube n, ∀ d : Fin n, e (flip u d) d = e u d := by
    intro u d; simp only [e, flip_involutive, G.adj_comm]
  let degDir : Fin n → ℤ := fun d => ∑ u : Cube n, e u d
  have hsum_degDir : ∑ d : Fin n, degDir d = 2 * (G.edgeFinset.card : ℤ) := by
    have h1 : ∑ d : Fin n, degDir d = ∑ u : Cube n, (G.degree u : ℤ) := by
      simp only [degDir]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      simp only [e, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
        nsmul_eq_mul, mul_one, degree_eq_card_flip hG u]
    rw [h1]
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have h2faces :
      2 * ∑ f ∈ faces n, (faceEdgeCount G f : ℤ) =
        ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
          (degDir i + degDir j) := by
    rw [Finset.mul_sum, sum_faces_eq_nested]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j hj => ?_))
    have hij : i ≠ j := ne_of_lt (Finset.mem_filter.mp hj).2
    have h4 :
        ∑ u : Cube n, (e u i + e u j) =
          ∑ v ∈ Finset.univ.filter (fun v : Cube n => v i = false ∧ v j = false),
            2 * (faceEdgeCount G (v, i, j) : ℤ) := by
      rw [sum_cube_eq_sum_four_corners hij (fun u => e u i + e u j)]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      have h_vi_i : e (flip v i) i = e v i := he_flip v i
      have h_vj_j : e (flip v j) j = e v j := he_flip v j
      have h_vij_i : e (flip (flip v i) j) i = e (flip v j) i := by
        rw [flip_comm, he_flip]
      have h_vij_j : e (flip (flip v i) j) j = e (flip v i) j := he_flip (flip v i) j
      rw [h_vi_i, h_vj_j, h_vij_i, h_vij_j]
      unfold faceEdgeCount
      simp only [e, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      ring
    rw [← h4, Finset.sum_add_distrib]
  have hsym := sum_fin_pair_symm
    (fun i j : Fin n => if i = j then (0 : ℤ) else degDir i + degDir j)
    (fun i j => by by_cases h : i = j <;> simp [h, eq_comm, add_comm])
  have hlhs :
      ∑ i : Fin n, ∑ j : Fin n, (if i = j then (0 : ℤ) else degDir i + degDir j) =
        2 * ((n : ℤ) - 1) * ∑ d : Fin n, degDir d := by
    have hsub : ∀ i j : Fin n,
        (if i = j then (0 : ℤ) else degDir i + degDir j) =
          (degDir i + degDir j) - (if i = j then degDir i + degDir j else 0) := by
      intro i j; split_ifs <;> ring
    simp_rw [hsub, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hdiag : ∀ i : Fin n,
        ∑ j : Fin n, (if i = j then degDir i + degDir j else 0) = 2 * degDir i := by
      intro i
      have : ∀ j : Fin n, (if i = j then degDir i + degDir j else 0) =
          if i = j then 2 * degDir i else 0 := by
        intro j; split_ifs with h
        · subst h; ring
        · rfl
      simp_rw [this]
      simp
    simp_rw [hdiag, ← Finset.mul_sum]
    ring
  have hdiag0 : ∑ i : Fin n, (if i = i then (0 : ℤ) else degDir i + degDir i) = 0 := by simp
  have hup :
      ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
          (if i = j then (0 : ℤ) else degDir i + degDir j) =
        ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
          (degDir i + degDir j) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j hj => ?_))
    have hij : i ≠ j := ne_of_lt (Finset.mem_filter.mp hj).2
    simp [hij]
  rw [hsum_degDir] at hlhs
  linarith

/-- Pointwise face inequality on any non-full 2-face `f`:
`3 · 1[empty] + 1[opp-2] + faceEdgeCount(f) ≤ 3`. -/
lemma face_linear_bound_of_not_full {n : ℕ} (G : SimpleGraph (Cube n)) [DecidableRel G.Adj]
    {f : Cube n × Fin n × Fin n} (hnot : ¬ isFullFace G f) :
    3 * (if isEmptyFace G f then (1 : ℤ) else 0) +
      (if isOppTwoFace G f then (1 : ℤ) else 0) +
      (faceEdgeCount G f : ℤ) ≤ 3 := by
  unfold isFullFace at hnot
  unfold isEmptyFace isOppTwoFace faceEdgeCount
  by_cases h1 : G.Adj f.1 (flip f.1 f.2.1) <;>
  by_cases h2 : G.Adj (flip f.1 f.2.2) (flip (flip f.1 f.2.2) f.2.1) <;>
  by_cases h3 : G.Adj f.1 (flip f.1 f.2.2) <;>
  by_cases h4 : G.Adj (flip f.1 f.2.1) (flip (flip f.1 f.2.1) f.2.2) <;>
  simp_all

/-- Global face-edge inequality for any `C₄`-free subgraph `G ≤ Q_n`:
`3 * N0 G + N2o G + (n - 1) * |E(G)| ≤ 3 * |faces n|` (in `ℤ`). -/
lemma hypercube_c4free_face_edge_ineq {n : ℕ}
    (G : SimpleGraph (Cube n)) [DecidableRel G.Adj]
    (hG : G ≤ hypercube n) (hC4 : IsC4Free G) :
    3 * (N0 G : ℤ) + (N2o G : ℤ) + ((n : ℤ) - 1) * (G.edgeFinset.card : ℤ) ≤
      3 * ((faces n).card : ℤ) := by
  have hsum :
      ∑ f ∈ faces n,
        (3 * (if isEmptyFace G f then (1 : ℤ) else 0) +
         (if isOppTwoFace G f then (1 : ℤ) else 0) +
         (faceEdgeCount G f : ℤ)) ≤
      ∑ _f ∈ faces n, (3 : ℤ) := by
    refine Finset.sum_le_sum (fun f hf => ?_)
    exact face_linear_bound_of_not_full G (not_isFullFace_of_isC4Free hC4 hf)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero,
    add_zero, Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  rw [sum_faceEdgeCount G hG] at hsum
  unfold N0 N2o
  linarith

/-- **Main Structural Theorem 3a (`hypercube_c4free_edge_bound_two_thirds_nat`):**
Unconditional general upper bound for EVERY `C₄`-free subgraph `G ≤ Q_n` (all `n : ℕ`):
`6 * |E(G)| ≤ (2 * n + 1) * 2^n`.
(Notice this yields `|E(G)| ≤ 1, 3, 9, 24` for `n = 1, 2, 3, 4`, matching `ex(Q_n, C_4)` exactly!) -/
theorem hypercube_c4free_edge_bound_two_thirds_nat {n : ℕ}
    (G : SimpleGraph (Cube n)) [DecidableRel G.Adj]
    (hG : G ≤ hypercube n) (hC4 : IsC4Free G) :
    6 * G.edgeFinset.card ≤ (2 * n + 1) * 2 ^ n := by
  by_cases hE0 : G.edgeFinset.card = 0
  · rw [hE0]; omega
  · have hEpos : (0 : ℤ) < (G.edgeFinset.card : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hE0
    have hCS := hypercube_c4free_cs_edge_bound G hG hC4
    have hFE := hypercube_c4free_face_edge_ineq G hG hC4
    have hF := eight_mul_card_faces (n := n)
    have hN2o_nonneg : (0 : ℤ) ≤ (N2o G : ℤ) := Nat.cast_nonneg _
    have h2pos : (0 : ℤ) ≤ (2 : ℤ) ^ n := by positivity
    have h24 :
        24 * (N0 G : ℤ) - 24 * (N2o G : ℤ) ≤
          3 * (n : ℤ) * ((n : ℤ) - 1) * (2 : ℤ) ^ n - 8 * ((n : ℤ) - 1) * (G.edgeFinset.card : ℤ) := by
      linarith
    have hmul :
        (2 : ℤ) ^ n * (3 * (n : ℤ) * (2 : ℤ) ^ n + 24 * (N0 G : ℤ) - 24 * (N2o G : ℤ)) ≤
          (2 : ℤ) ^ n * (3 * (n : ℤ) * (2 : ℤ) ^ n +
            (3 * (n : ℤ) * ((n : ℤ) - 1) * (2 : ℤ) ^ n -
              8 * ((n : ℤ) - 1) * (G.edgeFinset.card : ℤ))) := by
      apply mul_le_mul_of_nonneg_left _ h2pos
      linarith
    have hquad :
        3 * (4 * (G.edgeFinset.card : ℤ) - (n : ℤ) * (2 : ℤ) ^ n) ^ 2 ≤
          (2 : ℤ) ^ n * (3 * (n : ℤ) ^ 2 * (2 : ℤ) ^ n -
            8 * ((n : ℤ) - 1) * (G.edgeFinset.card : ℤ)) := by
      have h1 :
          3 * ((2 : ℤ) ^ n * ((n : ℤ) * (2 : ℤ) ^ n + 8 * (N0 G : ℤ) - 8 * (N2o G : ℤ))) =
            (2 : ℤ) ^ n * (3 * (n : ℤ) * (2 : ℤ) ^ n + 24 * (N0 G : ℤ) - 24 * (N2o G : ℤ)) := by
        ring
      have h2 :
          (2 : ℤ) ^ n * (3 * (n : ℤ) * (2 : ℤ) ^ n +
            (3 * (n : ℤ) * ((n : ℤ) - 1) * (2 : ℤ) ^ n -
              8 * ((n : ℤ) - 1) * (G.edgeFinset.card : ℤ))) =
            (2 : ℤ) ^ n * (3 * (n : ℤ) ^ 2 * (2 : ℤ) ^ n -
              8 * ((n : ℤ) - 1) * (G.edgeFinset.card : ℤ)) := by
        ring
      linarith
    have hexpand :
        3 * (4 * (G.edgeFinset.card : ℤ) - (n : ℤ) * (2 : ℤ) ^ n) ^ 2 -
          (2 : ℤ) ^ n * (3 * (n : ℤ) ^ 2 * (2 : ℤ) ^ n -
            8 * ((n : ℤ) - 1) * (G.edgeFinset.card : ℤ)) =
        48 * (G.edgeFinset.card : ℤ) ^ 2 -
          8 * (2 * (n : ℤ) + 1) * (2 : ℤ) ^ n * (G.edgeFinset.card : ℤ) := by
      ring
    have hcancel :
        48 * (G.edgeFinset.card : ℤ) ^ 2 ≤
          8 * (2 * (n : ℤ) + 1) * (2 : ℤ) ^ n * (G.edgeFinset.card : ℤ) := by
      linarith
    have hZ : 6 * (G.edgeFinset.card : ℤ) ≤ (2 * (n : ℤ) + 1) * (2 : ℤ) ^ n := by
      by_contra hlt
      push Not at hlt
      have hpos8 : (0 : ℤ) < 8 * (G.edgeFinset.card : ℤ) := by linarith
      have hgt :
          8 * (G.edgeFinset.card : ℤ) * ((2 * (n : ℤ) + 1) * (2 : ℤ) ^ n) <
            8 * (G.edgeFinset.card : ℤ) * (6 * (G.edgeFinset.card : ℤ)) :=
        mul_lt_mul_of_pos_left hlt hpos8
      have hr1 :
          8 * (G.edgeFinset.card : ℤ) * ((2 * (n : ℤ) + 1) * (2 : ℤ) ^ n) =
            8 * (2 * (n : ℤ) + 1) * (2 : ℤ) ^ n * (G.edgeFinset.card : ℤ) := by
        ring
      have hr2 :
          8 * (G.edgeFinset.card : ℤ) * (6 * (G.edgeFinset.card : ℤ)) =
            48 * (G.edgeFinset.card : ℤ) ^ 2 := by
        ring
      linarith
    exact_mod_cast hZ

/-- **Main Structural Theorem 3b (`hypercube_c4free_edge_bound_two_thirds`):**
Unconditional asymptotic `2/3` density upper bound for EVERY `C₄`-free subgraph `G ≤ Q_n`
(`n ≥ 1`):
`|E(G)| ≤ (2 / 3 + 1 / (3 * n)) * n * 2^{n - 1}`. -/
theorem hypercube_c4free_edge_bound_two_thirds {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Cube n)) [DecidableRel G.Adj]
    (hG : G ≤ hypercube n) (hC4 : IsC4Free G) :
    (G.edgeFinset.card : ℝ) ≤
      (2 / 3 + 1 / (3 * (n : ℝ))) * (n : ℝ) * (2 : ℝ) ^ (n - 1) := by
  have hnat := hypercube_c4free_edge_bound_two_thirds_nat G hG hC4
  have hR : 6 * (G.edgeFinset.card : ℝ) ≤ (2 * (n : ℝ) + 1) * (2 : ℝ) ^ n := by
    exact_mod_cast hnat
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
  have hpow : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
    cases n with
    | zero => omega
    | succ m => simp [pow_succ, mul_comm]
  have hrhs :
      (2 / 3 + 1 / (3 * (n : ℝ))) * (n : ℝ) * (2 : ℝ) ^ (n - 1) =
        (2 * (n : ℝ) + 1) * (2 : ℝ) ^ n / 6 := by
    rw [hpow]
    field_simp [hn_ne]
    ring
  rw [hrhs]
  linarith

end PPL033_HypercubeSignedAdj
