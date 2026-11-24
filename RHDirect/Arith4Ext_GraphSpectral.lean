/-
Copyright (c) 2026 Arithmetica4 Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Arith4Ext.GraphSpectral: Spectral Graph Theory & Expander Engine

Reusable Tier A `Arithmetica4` library module built from scratch on targeted Mathlib imports,
providing spectral graph theory and expander inequalities in `namespace Arith4Ext.GraphSpectral`:

1. **Adjacency Matrix Hermitian & Trace Identities (`Section 1`):**
   - `adjMatrix_isHermitian`: `(G.adjMatrix ℝ).IsHermitian`.
   - `adjMatrix_trace_zero`, `adjMatrix_sum_eigenvalues_zero`: trace `0` and `∑ λ_i = 0`.
   - `adjMatrix_trace_sq`, `adjMatrix_sum_sq_eigenvalues`: `Tr(A^2) = ∑ λ_i^2 = 2 |E(G)|`.
   - `adjMatrix_trace_cube`, `adjMatrix_sum_cube_eigenvalues`: `Tr(A^3) = ∑ λ_i^3 = 6 #triangles(G)`.
   - `hermitian_dotProduct_eq_sum_eigenvalues`, `hermitian_rayleigh_bounds`,
     `adjMatrix_rayleigh_bounds`: spectral quadratic form expansion and Rayleigh quotient bounds.

2. **Expander Mixing Lemma (`Section 2`):**
   - `regular_exists_deg_eigenvalue`, `regular_min_eigenvalue_neg`: `d` is an eigenvalue of a
     `d`-regular graph on `Fin n` (`0 < n`), and `λ_min < 0` when `0 < d`.
   - `expander_mixing_of_orth_bound`, `expander_mixing_lemma`: for every `d`-regular graph with
     nontrivial eigenvalues bounded by `|λ_i| ≤ λ`,
     `|e(S, T) - (d / n) * |S| * |T|| ≤ λ * √(|S| * |T|)`.

3. **Hoffman's Ratio Bound (`Section 3`):**
   - `hoffman_ratio_bound`, `hoffman_ratio_bound_inf`: for every `d`-regular graph (`0 < n`, `0 < d`)
     and independent set `S`, `|S| ≤ n * (-λ_min) / (d - λ_min)`.

4. **Spectral Edge-Expansion / Easy Cheeger Inequality (`Section 4`):**
   - `cheeger_edge_expansion`: for every `d`-regular graph and `S : Finset (Fin n)`,
     `e(S, Sᶜ) ≥ ((d - λ₂) / n) * |S| * (n - |S|)`.

All public declarations use strictly pure-Mathlib signatures (`0` custom public types or proxies).
-/

namespace Arith4Ext.GraphSpectral

open scoped Matrix BigOperators

/-! ## Section 1: Adjacency Matrix Hermitian Structure, Trace Identities & Rayleigh Bounds -/

section HermitianAndTraces

/-- The real adjacency matrix of a finite simple graph is Hermitian. -/
theorem adjMatrix_isHermitian {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (G.adjMatrix ℝ).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, G.adj_comm]

/-- Trace of the real adjacency matrix is `0`. -/
theorem adjMatrix_trace_zero {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (G.adjMatrix ℝ).trace = 0 :=
  SimpleGraph.trace_adjMatrix ℝ G

/-- The sum of all adjacency eigenvalues of a finite simple graph is `0`. -/
theorem adjMatrix_sum_eigenvalues_zero {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hA : (G.adjMatrix ℝ).IsHermitian) :
    ∑ i : Fin n, hA.eigenvalues i = 0 := by
  have htr := hA.trace_eq_sum_eigenvalues
  rw [adjMatrix_trace_zero G] at htr
  simpa using htr.symm

private lemma hermitian_trace_sq {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    (A * A).trace = ∑ i : Fin n, (hA.eigenvalues i) ^ 2 := by
  let U : Matrix (Fin n) (Fin n) ℝ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have hspec : A = U * D * star U := by
    simpa [U, D, Unitary.conjStarAlgAut_apply] using hA.spectral_theorem
  have hU : star U * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hAA : A * A = U * (D * D) * star U := by
    calc A * A
        = (U * D * star U) * (U * D * star U) := by rw [hspec]
      _ = U * D * (star U * U) * D * star U := by simp only [Matrix.mul_assoc]
      _ = U * (D * D) * star U := by rw [hU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have htr : (U * (D * D) * star U).trace = (D * D).trace := by
    rw [Matrix.trace_mul_comm (U * (D * D)) (star U), ← Matrix.mul_assoc, hU, Matrix.one_mul]
  rw [hAA, htr]
  simp [D, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, sq]

private lemma hermitian_trace_cube {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    (A * A * A).trace = ∑ i : Fin n, (hA.eigenvalues i) ^ 3 := by
  let U : Matrix (Fin n) (Fin n) ℝ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have hspec : A = U * D * star U := by
    simpa [U, D, Unitary.conjStarAlgAut_apply] using hA.spectral_theorem
  have hU : star U * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hAAA : A * A * A = U * (D * D * D) * star U := by
    calc A * A * A
        = (U * D * star U) * (U * D * star U) * (U * D * star U) := by rw [hspec]
      _ = U * D * (star U * U) * D * (star U * U) * D * star U := by simp only [Matrix.mul_assoc]
      _ = U * (D * D * D) * star U := by
          rw [hU]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
  have htr : (U * (D * D * D) * star U).trace = (D * D * D).trace := by
    rw [Matrix.trace_mul_comm (U * (D * D * D)) (star U), ← Matrix.mul_assoc, hU, Matrix.one_mul]
  rw [hAAA, htr]
  simp [D, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, pow_succ]

/-- `Tr(A^2) = 2 * |E(G)|` for the real adjacency matrix `A` of `G`. -/
theorem adjMatrix_trace_sq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ((G.adjMatrix ℝ) * (G.adjMatrix ℝ)).trace = 2 * (G.edgeFinset.card : ℝ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  have hrow : ∀ u : Fin n,
      (∑ v : Fin n, G.adjMatrix ℝ u v * G.adjMatrix ℝ v u) = (G.degree u : ℝ) := by
    intro u
    have hdeg : (G.neighborFinset u).card = G.degree u := G.card_neighborFinset_eq_degree u
    calc ∑ v : Fin n, G.adjMatrix ℝ u v * G.adjMatrix ℝ v u
        = ∑ v : Fin n, if G.Adj u v then (1 : ℝ) else 0 := by
            refine Finset.sum_congr rfl fun v _ => ?_
            by_cases hadj : G.Adj u v
            · simp [hadj, hadj.symm]
            · simp [hadj]
      _ = ((Finset.univ.filter (fun v => G.Adj u v)).card : ℝ) := by
            simp [Finset.sum_boole]
      _ = ((G.neighborFinset u).card : ℝ) := by
            congr 2
            ext v
            simp [SimpleGraph.mem_neighborFinset]
      _ = (G.degree u : ℝ) := by rw [hdeg]
  simp_rw [hrow]
  have hsum : ∑ u : Fin n, G.degree u = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  exact_mod_cast hsum

/-- The sum of squares of adjacency eigenvalues equals `2 * |E(G)|`. -/
theorem adjMatrix_sum_sq_eigenvalues {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hA : (G.adjMatrix ℝ).IsHermitian) :
    ∑ i : Fin n, (hA.eigenvalues i) ^ 2 = 2 * (G.edgeFinset.card : ℝ) := by
  rw [← hermitian_trace_sq hA, adjMatrix_trace_sq G]

private lemma card_triangle_ordered_triples {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (Finset.univ.filter (fun p : Fin n × Fin n × Fin n =>
        G.Adj p.1 p.2.1 ∧ G.Adj p.2.1 p.2.2 ∧ G.Adj p.2.2 p.1)).card =
      6 * (G.cliqueFinset 3).card := by
  let triples := Finset.univ.filter (fun p : Fin n × Fin n × Fin n =>
    G.Adj p.1 p.2.1 ∧ G.Adj p.2.1 p.2.2 ∧ G.Adj p.2.2 p.1)
  let mkSet : Fin n × Fin n × Fin n → Finset (Fin n) := fun p => {p.1, p.2.1, p.2.2}
  have himg : ∀ p ∈ triples, mkSet p ∈ G.cliqueFinset 3 := by
    intro ⟨u, v, w⟩ hp
    simp only [triples, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rcases hp with ⟨huv, hvw, hwu⟩
    have hne_uv : u ≠ v := G.ne_of_adj huv
    have hne_vw : v ≠ w := G.ne_of_adj hvw
    have hne_wu : w ≠ u := G.ne_of_adj hwu
    rw [SimpleGraph.mem_cliqueFinset_iff]
    refine ⟨?_, ?_⟩
    · intro x hx y hy hxy
      dsimp only [mkSet] at hx hy
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      all_goals
        first
        | exact absurd rfl hxy
        | exact huv
        | exact huv.symm
        | exact hvw
        | exact hvw.symm
        | exact hwu
        | exact hwu.symm
    · have hcard : ({u, v, w} : Finset (Fin n)).card = 3 := by
        rw [Finset.card_insert_of_notMem, Finset.card_pair hne_vw]
        simp [hne_uv, hne_wu.symm]
      exact hcard
  have hfiber : ∀ t ∈ G.cliqueFinset 3,
      (triples.filter (fun p => mkSet p = t)).card = 6 := by
    intro t ht
    rw [SimpleGraph.mem_cliqueFinset_iff] at ht
    rcases ht with ⟨ht_clq, ht_card⟩
    rcases Finset.card_eq_three.mp ht_card with ⟨a, b, c, hab, hac, hbc, rfl⟩
    have hab_adj : G.Adj a b := ht_clq (by simp) (by simp) hab
    have hac_adj : G.Adj a c := ht_clq (by simp) (by simp) hac
    have hbc_adj : G.Adj b c := ht_clq (by simp) (by simp) hbc
    let six : Finset (Fin n × Fin n × Fin n) :=
      {(a, b, c), (a, c, b), (b, a, c), (b, c, a), (c, a, b), (c, b, a)}
    have hEq : triples.filter (fun p => mkSet p = {a, b, c}) = six := by
      ext ⟨u, v, w⟩
      simp only [Finset.mem_filter, triples, Finset.mem_univ, true_and, six,
        Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨huv, hvw, hwu⟩, hset⟩
        have hu : u ∈ ({a, b, c} : Finset (Fin n)) := hset ▸ by simp [mkSet]
        have hv : v ∈ ({a, b, c} : Finset (Fin n)) := hset ▸ by simp [mkSet]
        have hw : w ∈ ({a, b, c} : Finset (Fin n)) := hset ▸ by simp [mkSet]
        have hne_uv : u ≠ v := G.ne_of_adj huv
        have hne_vw : v ≠ w := G.ne_of_adj hvw
        have hne_wu : w ≠ u := G.ne_of_adj hwu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv hw
        rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
          rcases hw with rfl | rfl | rfl
        all_goals
          first
          | exact absurd rfl hne_uv
          | exact absurd rfl hne_vw
          | exact absurd rfl hne_wu
          | simp
      · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
          ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
        · refine ⟨⟨hab_adj, hbc_adj, hac_adj.symm⟩, ?_⟩
          ext x; simp [mkSet]
        · refine ⟨⟨hac_adj, hbc_adj.symm, hab_adj.symm⟩, ?_⟩
          ext x; simp [mkSet]; tauto
        · refine ⟨⟨hab_adj.symm, hac_adj, hbc_adj.symm⟩, ?_⟩
          ext x; simp [mkSet]; tauto
        · refine ⟨⟨hbc_adj, hac_adj.symm, hab_adj⟩, ?_⟩
          ext x; simp [mkSet]; tauto
        · refine ⟨⟨hac_adj.symm, hab_adj, hbc_adj⟩, ?_⟩
          ext x; simp [mkSet]; tauto
        · refine ⟨⟨hbc_adj.symm, hab_adj.symm, hac_adj⟩, ?_⟩
          ext x; simp [mkSet]; tauto
    rw [hEq]
    have hc1 : (a, b, c) ∉ ({(a, c, b), (b, a, c), (b, c, a), (c, a, b), (c, b, a)} :
        Finset (Fin n × Fin n × Fin n)) := by
      simp [hab, hac, hbc, hab.symm, hac.symm]
    have hc2 : (a, c, b) ∉ ({(b, a, c), (b, c, a), (c, a, b), (c, b, a)} :
        Finset (Fin n × Fin n × Fin n)) := by
      simp [hab, hbc, hab.symm, hac.symm, hbc.symm]
    have hc3 : (b, a, c) ∉ ({(b, c, a), (c, a, b), (c, b, a)} :
        Finset (Fin n × Fin n × Fin n)) := by
      simp [hab, hac, hbc, hac.symm, hbc.symm]
    have hc4 : (b, c, a) ∉ ({(c, a, b), (c, b, a)} : Finset (Fin n × Fin n × Fin n)) := by
      simp [hab, hbc]
    have hc5 : (c, a, b) ∉ ({(c, b, a)} : Finset (Fin n × Fin n × Fin n)) := by
      simp [hab]
    dsimp only [six]
    rw [Finset.card_insert_of_notMem hc1, Finset.card_insert_of_notMem hc2,
        Finset.card_insert_of_notMem hc3, Finset.card_insert_of_notMem hc4,
        Finset.card_insert_of_notMem hc5, Finset.card_singleton]
  calc triples.card
      = ∑ t ∈ G.cliqueFinset 3, (triples.filter (fun p => mkSet p = t)).card :=
          Finset.card_eq_sum_card_fiberwise himg
    _ = ∑ _t ∈ G.cliqueFinset 3, 6 := Finset.sum_congr rfl hfiber
    _ = 6 * (G.cliqueFinset 3).card := by simp [mul_comm]

/-- `Tr(A^3) = 6 * #triangles(G)` for the real adjacency matrix `A` of `G`. -/
theorem adjMatrix_trace_cube {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ((G.adjMatrix ℝ) * (G.adjMatrix ℝ) * (G.adjMatrix ℝ)).trace =
      6 * ((G.cliqueFinset 3).card : ℝ) := by
  have htr : ((G.adjMatrix ℝ) * (G.adjMatrix ℝ) * (G.adjMatrix ℝ)).trace =
      ∑ u : Fin n, ∑ v : Fin n, ∑ w : Fin n,
        G.adjMatrix ℝ u v * G.adjMatrix ℝ v w * G.adjMatrix ℝ w u := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
  rw [htr]
  have hterm : (∑ u : Fin n, ∑ v : Fin n, ∑ w : Fin n,
        G.adjMatrix ℝ u v * G.adjMatrix ℝ v w * G.adjMatrix ℝ w u) =
      ∑ p : Fin n × Fin n × Fin n,
        if G.Adj p.1 p.2.1 ∧ G.Adj p.2.1 p.2.2 ∧ G.Adj p.2.2 p.1 then (1 : ℝ) else 0 := by
    symm
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ =>
      Finset.sum_congr rfl fun w _ => ?_
    by_cases huv : G.Adj u v <;> by_cases hvw : G.Adj v w <;> by_cases hwu : G.Adj w u <;>
      simp [huv, hvw, hwu]
  rw [hterm, Finset.sum_boole]
  have hcard := card_triangle_ordered_triples G
  exact_mod_cast hcard

/-- The sum of cubes of adjacency eigenvalues equals `6 * #triangles(G)`. -/
theorem adjMatrix_sum_cube_eigenvalues {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hA : (G.adjMatrix ℝ).IsHermitian) :
    ∑ i : Fin n, (hA.eigenvalues i) ^ 3 = 6 * ((G.cliqueFinset 3).card : ℝ) := by
  rw [← hermitian_trace_cube hA, adjMatrix_trace_cube G]

private lemma hermitian_transpose_eq {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    Aᵀ = A := by
  ext r c
  simpa [Matrix.conjTranspose_apply, Matrix.transpose_apply] using
    (congrFun (congrFun hA.eq c) r).symm

private lemma hermitian_inner_mulVec {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (hA.eigenvectorBasis i) (WithLp.toLp 2 (A.mulVec x.ofLp)) =
      hA.eigenvalues i * inner ℝ (hA.eigenvectorBasis i) x := by
  let b := hA.eigenvectorBasis
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial]
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
      hermitian_transpose_eq hA, hA.mulVec_eigenvectorBasis i, smul_dotProduct, smul_eq_mul]
  congr 1
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

/-- Spectral expansion of the quadratic form `x ⬝ᵥ A x` in the orthonormal eigenbasis of a
real Hermitian matrix `A`. -/
theorem hermitian_dotProduct_eq_sum_eigenvalues {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (x : EuclideanSpace ℝ (Fin n)) :
    x.ofLp ⬝ᵥ A.mulVec x.ofLp =
      ∑ i : Fin n, hA.eigenvalues i * (inner ℝ (hA.eigenvectorBasis i) x) ^ 2 := by
  let b := hA.eigenvectorBasis
  let Ax : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (A.mulVec x.ofLp)
  have hinner_x_Ax : x.ofLp ⬝ᵥ A.mulVec x.ofLp = inner ℝ x Ax := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [Ax, dotProduct_comm]
  rw [hinner_x_Ax, ← b.sum_inner_mul_inner x Ax]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hermitian_inner_mulVec hA i x, real_inner_comm x (b i)]
  ring

/-- Variational Rayleigh quotient bounds for any real Hermitian matrix `A`. -/
theorem hermitian_rayleigh_bounds {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) {lamMin lamMax : ℝ}
    (hmin : ∀ i : Fin n, lamMin ≤ hA.eigenvalues i)
    (hmax : ∀ i : Fin n, hA.eigenvalues i ≤ lamMax)
    (x : EuclideanSpace ℝ (Fin n)) :
    lamMin * ‖x‖ ^ 2 ≤ x.ofLp ⬝ᵥ A.mulVec x.ofLp ∧
      x.ofLp ⬝ᵥ A.mulVec x.ofLp ≤ lamMax * ‖x‖ ^ 2 := by
  let b := hA.eigenvectorBasis
  have hnorm : ∑ i : Fin n, (inner ℝ (b i) x) ^ 2 = ‖x‖ ^ 2 := by
    simpa [Real.norm_eq_abs, sq_abs] using b.sum_sq_norm_inner_right x
  rw [hermitian_dotProduct_eq_sum_eigenvalues hA x]
  constructor
  · calc lamMin * ‖x‖ ^ 2
        = ∑ i : Fin n, lamMin * (inner ℝ (b i) x) ^ 2 := by rw [← Finset.mul_sum, hnorm]
      _ ≤ ∑ i : Fin n, hA.eigenvalues i * (inner ℝ (b i) x) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact mul_le_mul_of_nonneg_right (hmin i) (sq_nonneg _)
  · calc ∑ i : Fin n, hA.eigenvalues i * (inner ℝ (b i) x) ^ 2
        ≤ ∑ i : Fin n, lamMax * (inner ℝ (b i) x) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact mul_le_mul_of_nonneg_right (hmax i) (sq_nonneg _)
      _ = lamMax * ‖x‖ ^ 2 := by rw [← Finset.mul_sum, hnorm]

/-- Rayleigh quotient bounds specialized to `G.adjMatrix ℝ` on a nonempty vertex set (`0 < n`),
expressed directly with the minimum and maximum eigenvalues `Finset.univ.inf'` / `Finset.univ.sup'`. -/
theorem adjMatrix_rayleigh_bounds {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian)
    (x : EuclideanSpace ℝ (Fin n)) :
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    Finset.univ.inf' Finset.univ_nonempty hA.eigenvalues * ‖x‖ ^ 2 ≤
        x.ofLp ⬝ᵥ (G.adjMatrix ℝ).mulVec x.ofLp ∧
      x.ofLp ⬝ᵥ (G.adjMatrix ℝ).mulVec x.ofLp ≤
        Finset.univ.sup' Finset.univ_nonempty hA.eigenvalues * ‖x‖ ^ 2 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact hermitian_rayleigh_bounds hA
    (fun i => Finset.inf'_le hA.eigenvalues (Finset.mem_univ i))
    (fun i => Finset.le_sup' hA.eigenvalues (Finset.mem_univ i)) x

end HermitianAndTraces

/-! ## Section 2: Regularity Eigenvector Decomposition & Expander Mixing Lemma -/

section RegularAndMixing

private def onesVec (n : ℕ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun _ => (1 : ℝ))

private def indVec {n : ℕ} (S : Finset (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun v => if v ∈ S then (1 : ℝ) else 0)

private lemma adjMatrix_mulVec_ones_of_regular {n d : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hreg : G.IsRegularOfDegree d) :
    (G.adjMatrix ℝ).mulVec (onesVec n).ofLp = (d : ℝ) • (onesVec n).ofLp := by
  ext u
  simp only [Matrix.mulVec, dotProduct, onesVec, Pi.smul_apply, smul_eq_mul, mul_one]
  have hrow : (∑ v : Fin n, G.adjMatrix ℝ u v) = (G.degree u : ℝ) := by
    calc ∑ v : Fin n, G.adjMatrix ℝ u v
        = ∑ v : Fin n, if G.Adj u v then (1 : ℝ) else 0 := by
            refine Finset.sum_congr rfl fun v _ => by simp
      _ = ((Finset.univ.filter (fun v => G.Adj u v)).card : ℝ) := by simp [Finset.sum_boole]
      _ = ((G.neighborFinset u).card : ℝ) := by
            congr 2; ext v; simp [SimpleGraph.mem_neighborFinset]
      _ = (G.degree u : ℝ) := by rw [G.card_neighborFinset_eq_degree u]
  rw [hrow, hreg.degree_eq u]

private lemma inner_ones_ones (n : ℕ) :
    inner ℝ (onesVec n) (onesVec n) = (n : ℝ) := by
  rw [PiLp.inner_apply]
  simp [onesVec]

private lemma norm_sq_ones (n : ℕ) : ‖onesVec n‖ ^ 2 = (n : ℝ) := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [onesVec]

private lemma inner_ones_ind {n : ℕ} (S : Finset (Fin n)) :
    inner ℝ (onesVec n) (indVec S) = (S.card : ℝ) := by
  rw [PiLp.inner_apply]
  simp [onesVec, indVec]

private lemma norm_sq_ind {n : ℕ} (S : Finset (Fin n)) :
    ‖indVec S‖ ^ 2 = (S.card : ℝ) := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [indVec]

private lemma ind_dotProduct_adjMatrix_ind {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S T : Finset (Fin n)) :
    (indVec S).ofLp ⬝ᵥ (G.adjMatrix ℝ).mulVec (indVec T).ofLp =
      (((S ×ˢ T).filter (fun p => G.Adj p.1 p.2)).card : ℝ) := by
  have hsum : (indVec S).ofLp ⬝ᵥ (G.adjMatrix ℝ).mulVec (indVec T).ofLp =
      ∑ u : Fin n, ∑ v : Fin n,
        if u ∈ S ∧ v ∈ T ∧ G.Adj u v then (1 : ℝ) else 0 := by
    simp only [dotProduct, Matrix.mulVec, indVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    by_cases hu : u ∈ S <;> by_cases hv : v ∈ T <;> by_cases hadj : G.Adj u v <;>
      simp [hu, hv, hadj]
  rw [hsum, ← Fintype.sum_prod_type']
  have hfilt : (∑ p : Fin n × Fin n, if p.1 ∈ S ∧ p.2 ∈ T ∧ G.Adj p.1 p.2 then (1 : ℝ) else 0) =
      (((S ×ˢ T).filter (fun p => G.Adj p.1 p.2)).card : ℝ) := by
    rw [Finset.sum_boole]
    congr 2
    ext ⟨u, v⟩
    simp [Finset.mem_product, and_assoc]
  exact hfilt

private lemma herm_dotProduct_comm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (x y : EuclideanSpace ℝ (Fin n)) :
    x.ofLp ⬝ᵥ A.mulVec y.ofLp = y.ofLp ⬝ᵥ A.mulVec x.ofLp := by
  calc x.ofLp ⬝ᵥ A.mulVec y.ofLp
      = A.mulVec y.ofLp ⬝ᵥ x.ofLp := dotProduct_comm _ _
    _ = y.ofLp ⬝ᵥ Aᵀ.mulVec x.ofLp := by rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    _ = y.ofLp ⬝ᵥ A.mulVec x.ofLp := by rw [hermitian_transpose_eq hA]

private lemma orth_decomp_quadratic {n d : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian) (hreg : G.IsRegularOfDegree d)
    (S T : Finset (Fin n)) :
    let xpar : EuclideanSpace ℝ (Fin n) := ((S.card : ℝ) / n) • onesVec n
    let ypar : EuclideanSpace ℝ (Fin n) := ((T.card : ℝ) / n) • onesVec n
    let xperp : EuclideanSpace ℝ (Fin n) := indVec S - xpar
    let yperp : EuclideanSpace ℝ (Fin n) := indVec T - ypar
    inner ℝ (onesVec n) xperp = 0 ∧
      inner ℝ (onesVec n) yperp = 0 ∧
      ‖xperp‖ ^ 2 = (S.card : ℝ) - (S.card : ℝ) ^ 2 / n ∧
      ‖yperp‖ ^ 2 = (T.card : ℝ) - (T.card : ℝ) ^ 2 / n ∧
      (indVec S).ofLp ⬝ᵥ (G.adjMatrix ℝ).mulVec (indVec T).ofLp -
          ((d : ℝ) / n) * S.card * T.card =
        xperp.ofLp ⬝ᵥ (G.adjMatrix ℝ).mulVec yperp.ofLp := by
  intro xpar ypar xperp yperp
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hxperp_orth : inner ℝ (onesVec n) xperp = 0 := by
    dsimp only [xperp, xpar]
    rw [inner_sub_right, inner_smul_right, inner_ones_ind, inner_ones_ones]
    field_simp [hn0]
    ring
  have hyperp_orth : inner ℝ (onesVec n) yperp = 0 := by
    dsimp only [yperp, ypar]
    rw [inner_sub_right, inner_smul_right, inner_ones_ind, inner_ones_ones]
    field_simp [hn0]
    ring
  have hx_norm : ‖xperp‖ ^ 2 = (S.card : ℝ) - (S.card : ℝ) ^ 2 / n := by
    have hsplit : indVec S = xpar + xperp := (add_sub_cancel xpar (indVec S)).symm
    have horth : inner ℝ xpar xperp = 0 := by
      dsimp only [xpar]
      rw [real_inner_smul_left, hxperp_orth, mul_zero]
    have hpyth : ‖indVec S‖ ^ 2 = ‖xpar‖ ^ 2 + ‖xperp‖ ^ 2 := by
      rw [hsplit, norm_add_sq_real, horth]
      ring
    have hxpar_sq : ‖xpar‖ ^ 2 = (S.card : ℝ) ^ 2 / n := by
      dsimp only [xpar]
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_sq_ones, div_pow,
          div_mul_eq_mul_div, sq (n : ℝ), mul_div_mul_right _ _ hn0]
    rw [norm_sq_ind, hxpar_sq] at hpyth
    linarith
  have hy_norm : ‖yperp‖ ^ 2 = (T.card : ℝ) - (T.card : ℝ) ^ 2 / n := by
    have hsplit : indVec T = ypar + yperp := (add_sub_cancel ypar (indVec T)).symm
    have horth : inner ℝ ypar yperp = 0 := by
      dsimp only [ypar]
      rw [real_inner_smul_left, hyperp_orth, mul_zero]
    have hpyth : ‖indVec T‖ ^ 2 = ‖ypar‖ ^ 2 + ‖yperp‖ ^ 2 := by
      rw [hsplit, norm_add_sq_real, horth]
      ring
    have hypar_sq : ‖ypar‖ ^ 2 = (T.card : ℝ) ^ 2 / n := by
      dsimp only [ypar]
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_sq_ones, div_pow,
          div_mul_eq_mul_div, sq (n : ℝ), mul_div_mul_right _ _ hn0]
    rw [norm_sq_ind, hypar_sq] at hpyth
    linarith
  have hA_ones : (G.adjMatrix ℝ).mulVec (onesVec n).ofLp = (d : ℝ) • (onesVec n).ofLp :=
    adjMatrix_mulVec_ones_of_regular G hreg
  have hA_xpar : (G.adjMatrix ℝ).mulVec xpar.ofLp = (d : ℝ) • xpar.ofLp := by
    dsimp only [xpar]
    rw [WithLp.ofLp_smul, Matrix.mulVec_smul, hA_ones, smul_comm]
  have hA_ypar : (G.adjMatrix ℝ).mulVec ypar.ofLp = (d : ℝ) • ypar.ofLp := by
    dsimp only [ypar]
    rw [WithLp.ofLp_smul, Matrix.mulVec_smul, hA_ones, smul_comm]
  have hxpar_yperp : xpar.ofLp ⬝ᵥ (G.adjMatrix ℝ).mulVec yperp.ofLp = 0 := by
    rw [herm_dotProduct_comm hA, hA_xpar, dotProduct_smul, smul_eq_mul]
    have hdot0 : yperp.ofLp ⬝ᵥ xpar.ofLp = inner ℝ xpar yperp := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    rw [hdot0]
    have h0 : inner ℝ xpar yperp = 0 := by
      dsimp only [xpar]; rw [real_inner_smul_left, hyperp_orth, mul_zero]
    rw [h0, mul_zero]
  have hxperp_ypar : xperp.ofLp ⬝ᵥ (G.adjMatrix ℝ).mulVec ypar.ofLp = 0 := by
    rw [hA_ypar, dotProduct_smul, smul_eq_mul]
    have hdot0 : xperp.ofLp ⬝ᵥ ypar.ofLp = inner ℝ ypar xperp := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    rw [hdot0]
    have h0 : inner ℝ ypar xperp = 0 := by
      dsimp only [ypar]; rw [real_inner_smul_left, hxperp_orth, mul_zero]
    rw [h0, mul_zero]
  have hxpar_ypar : xpar.ofLp ⬝ᵥ (G.adjMatrix ℝ).mulVec ypar.ofLp =
      ((d : ℝ) / n) * S.card * T.card := by
    rw [hA_ypar, dotProduct_smul, smul_eq_mul]
    have hdot : xpar.ofLp ⬝ᵥ ypar.ofLp = inner ℝ ypar xpar := by
      rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    rw [hdot]
    dsimp only [xpar, ypar]
    rw [real_inner_smul_left, inner_smul_right, inner_ones_ones]
    field_simp [hn0]
  have hexp : (indVec S).ofLp ⬝ᵥ (G.adjMatrix ℝ).mulVec (indVec T).ofLp =
      xpar.ofLp ⬝ᵥ (G.adjMatrix ℝ).mulVec ypar.ofLp +
        xpar.ofLp ⬝ᵥ (G.adjMatrix ℝ).mulVec yperp.ofLp +
        xperp.ofLp ⬝ᵥ (G.adjMatrix ℝ).mulVec ypar.ofLp +
        xperp.ofLp ⬝ᵥ (G.adjMatrix ℝ).mulVec yperp.ofLp := by
    have hs : (indVec S).ofLp = xpar.ofLp + xperp.ofLp := by
      simp [xperp, WithLp.ofLp_sub]
    have ht : (indVec T).ofLp = ypar.ofLp + yperp.ofLp := by
      simp [yperp, WithLp.ofLp_sub]
    rw [hs, ht, Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct]
    ring
  refine ⟨hxperp_orth, hyperp_orth, hx_norm, hy_norm, ?_⟩
  rw [hexp, hxpar_ypar, hxpar_yperp, hxperp_ypar]
  ring

private lemma hermitian_bilinear_eq_sum_eigenvalues {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (x y : EuclideanSpace ℝ (Fin n)) :
    x.ofLp ⬝ᵥ A.mulVec y.ofLp =
      ∑ i : Fin n, hA.eigenvalues i * inner ℝ (hA.eigenvectorBasis i) x *
        inner ℝ (hA.eigenvectorBasis i) y := by
  let b := hA.eigenvectorBasis
  let Ay : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (A.mulVec y.ofLp)
  have hinner : x.ofLp ⬝ᵥ A.mulVec y.ofLp = inner ℝ x Ay := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [Ay, dotProduct_comm]
  rw [hinner, ← b.sum_inner_mul_inner x Ay]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hermitian_inner_mulVec hA i y, real_inner_comm x (b i)]
  ring

private lemma regular_eigenbasis_ones_relation {n d : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian) (hreg : G.IsRegularOfDegree d)
    (i : Fin n) :
    hA.eigenvalues i * inner ℝ (hA.eigenvectorBasis i) (onesVec n) =
      (d : ℝ) * inner ℝ (hA.eigenvectorBasis i) (onesVec n) := by
  let b := hA.eigenvectorBasis
  have hA_ones : (G.adjMatrix ℝ).mulVec (onesVec n).ofLp = (d : ℝ) • (onesVec n).ofLp :=
    adjMatrix_mulVec_ones_of_regular G hreg
  calc hA.eigenvalues i * inner ℝ (b i) (onesVec n)
      = hA.eigenvalues i * ((onesVec n).ofLp ⬝ᵥ (b i).ofLp) := by
          rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    _ = (onesVec n).ofLp ⬝ᵥ (hA.eigenvalues i • (b i).ofLp) := by
          rw [dotProduct_smul, smul_eq_mul]
    _ = (onesVec n).ofLp ⬝ᵥ (G.adjMatrix ℝ).mulVec (b i).ofLp := by
          rw [hA.mulVec_eigenvectorBasis i]
    _ = (b i).ofLp ⬝ᵥ (G.adjMatrix ℝ).mulVec (onesVec n).ofLp :=
          herm_dotProduct_comm hA (onesVec n) (b i)
    _ = (b i).ofLp ⬝ᵥ ((d : ℝ) • (onesVec n).ofLp) := by rw [hA_ones]
    _ = (d : ℝ) * inner ℝ (b i) (onesVec n) := by
          rw [dotProduct_smul, smul_eq_mul, EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
              dotProduct_comm]

/-- Any `d`-regular graph on `Fin n` (`0 < n`) admits `d` as an adjacency eigenvalue. -/
theorem regular_exists_deg_eigenvalue {n d : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian) (hreg : G.IsRegularOfDegree d) :
    ∃ i₀ : Fin n, hA.eigenvalues i₀ = (d : ℝ) := by
  by_contra hnone
  push Not at hnone
  have horth : ∀ i : Fin n, inner ℝ (hA.eigenvectorBasis i) (onesVec n) = 0 := by
    intro i
    have hrel := regular_eigenbasis_ones_relation G hA hreg i
    have hmul : (hA.eigenvalues i - (d : ℝ)) * inner ℝ (hA.eigenvectorBasis i) (onesVec n) = 0 := by
      linarith
    rcases mul_eq_zero.mp hmul with hdiff | h0
    · exact absurd (sub_eq_zero.mp hdiff) (hnone i)
    · exact h0
  have hnorm := hA.eigenvectorBasis.sum_sq_norm_inner_right (onesVec n)
  simp only [horth, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero] at hnorm
  have hsq : ‖onesVec n‖ ^ 2 = (n : ℝ) := norm_sq_ones n
  rw [← hnorm] at hsq
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  exact hn0 hsq.symm

/-- Every `d`-regular graph with `0 < n` and `0 < d` has a strictly negative minimum eigenvalue. -/
theorem regular_min_eigenvalue_neg {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian)
    (hreg : G.IsRegularOfDegree d) :
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    Finset.univ.inf' Finset.univ_nonempty hA.eigenvalues < 0 := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i₀, hi₀⟩ := regular_exists_deg_eigenvalue hn G hA hreg
  have hsum := adjMatrix_sum_eigenvalues_zero G hA
  by_contra hge
  rw [not_lt] at hge
  have hnonneg : ∀ i : Fin n, 0 ≤ hA.eigenvalues i := fun i =>
    le_trans hge (Finset.inf'_le hA.eigenvalues (Finset.mem_univ i))
  have hle : hA.eigenvalues i₀ ≤ ∑ i : Fin n, hA.eigenvalues i :=
    Finset.single_le_sum (fun i _ => hnonneg i) (Finset.mem_univ i₀)
  rw [hi₀, hsum] at hle
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  linarith

private lemma orth_component_vanishes_if_unique_deg {n d : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian)
    (hreg : G.IsRegularOfDegree d) {i₀ : Fin n} (_hi₀ : hA.eigenvalues i₀ = (d : ℝ))
    (huniq : ∀ i : Fin n, i ≠ i₀ → hA.eigenvalues i ≠ (d : ℝ))
    {x : EuclideanSpace ℝ (Fin n)} (hx : inner ℝ (onesVec n) x = 0) :
    inner ℝ (hA.eigenvectorBasis i₀) x = 0 := by
  let b := hA.eigenvectorBasis
  have horth_other : ∀ i : Fin n, i ≠ i₀ → inner ℝ (b i) (onesVec n) = 0 := by
    intro i hi
    have hrel := regular_eigenbasis_ones_relation G hA hreg i
    have hmul : (hA.eigenvalues i - (d : ℝ)) * inner ℝ (b i) (onesVec n) = 0 := by linarith
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr (huniq i hi))
  have h1_eq : onesVec n = inner ℝ (b i₀) (onesVec n) • b i₀ := by
    have hrepr := b.sum_repr (onesVec n)
    have hsplit : ∑ i : Fin n, (b.repr (onesVec n)).ofLp i • b i =
        (b.repr (onesVec n)).ofLp i₀ • b i₀ := by
      refine Finset.sum_eq_single i₀ (fun i _ hi => ?_) (fun h => absurd (Finset.mem_univ i₀) h)
      rw [b.repr_apply_apply, horth_other i hi, zero_smul]
    rw [hsplit, b.repr_apply_apply] at hrepr
    exact hrepr.symm
  have hc0 : inner ℝ (b i₀) (onesVec n) ≠ 0 := by
    intro hc
    have hzero : onesVec n = 0 := by rw [h1_eq, hc, zero_smul]
    have hsq := norm_sq_ones n
    rw [hzero, norm_zero, zero_pow (by norm_num)] at hsq
    exact (Nat.cast_ne_zero.mpr hn.ne') hsq.symm
  have hinner' : inner ℝ (b i₀) (onesVec n) * inner ℝ (b i₀) x = 0 := by
    calc inner ℝ (b i₀) (onesVec n) * inner ℝ (b i₀) x
        = inner ℝ (inner ℝ (b i₀) (onesVec n) • b i₀) x := by rw [real_inner_smul_left]
      _ = inner ℝ (onesVec n) x := by rw [← h1_eq]
      _ = 0 := hx
  exact (mul_eq_zero.mp hinner').resolve_left hc0

private lemma orth_rayleigh_upper_of_lambda2 {n d : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian) (hreg : G.IsRegularOfDegree d)
    {i₀ : Fin n} (hi₀ : hA.eigenvalues i₀ = (d : ℝ)) {lam2 : ℝ}
    (hlam2 : ∀ i : Fin n, i ≠ i₀ → hA.eigenvalues i ≤ lam2)
    {x : EuclideanSpace ℝ (Fin n)} (hx : inner ℝ (onesVec n) x = 0) :
    x.ofLp ⬝ᵥ (G.adjMatrix ℝ).mulVec x.ofLp ≤ lam2 * ‖x‖ ^ 2 := by
  let b := hA.eigenvectorBasis
  have hnorm : ∑ i : Fin n, (inner ℝ (b i) x) ^ 2 = ‖x‖ ^ 2 := by
    simpa [Real.norm_eq_abs, sq_abs] using b.sum_sq_norm_inner_right x
  rw [hermitian_dotProduct_eq_sum_eigenvalues hA x]
  by_cases hmult : ∃ i₁ : Fin n, i₁ ≠ i₀ ∧ hA.eigenvalues i₁ = (d : ℝ)
  · rcases hmult with ⟨i₁, hi₁_ne, hi₁_eq⟩
    have hd_le : (d : ℝ) ≤ lam2 := hi₁_eq ▸ hlam2 i₁ hi₁_ne
    have hall : ∀ i : Fin n, hA.eigenvalues i ≤ lam2 := fun i =>
      if hi : i = i₀ then hi ▸ hi₀.symm ▸ hd_le else hlam2 i hi
    calc ∑ i : Fin n, hA.eigenvalues i * (inner ℝ (b i) x) ^ 2
        ≤ ∑ i : Fin n, lam2 * (inner ℝ (b i) x) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hall i) (sq_nonneg _)
      _ = lam2 * ‖x‖ ^ 2 := by rw [← Finset.mul_sum, hnorm]
  · push Not at hmult
    have hx0 : inner ℝ (b i₀) x = 0 :=
      orth_component_vanishes_if_unique_deg hn G hA hreg hi₀ hmult hx
    calc ∑ i : Fin n, hA.eigenvalues i * (inner ℝ (b i) x) ^ 2
        ≤ ∑ i : Fin n, lam2 * (inner ℝ (b i) x) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          by_cases hi : i = i₀
          · subst hi; simp [hx0]
          · exact mul_le_mul_of_nonneg_right (hlam2 i hi) (sq_nonneg _)
      _ = lam2 * ‖x‖ ^ 2 := by rw [← Finset.mul_sum, hnorm]

private lemma orth_bilinear_abs_bound {n d : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian) (hreg : G.IsRegularOfDegree d)
    {i₀ : Fin n} (hi₀ : hA.eigenvalues i₀ = (d : ℝ)) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlam : ∀ i : Fin n, i ≠ i₀ → |hA.eigenvalues i| ≤ lam)
    {x y : EuclideanSpace ℝ (Fin n)} (hx : inner ℝ (onesVec n) x = 0)
    (_hy : inner ℝ (onesVec n) y = 0) :
    |x.ofLp ⬝ᵥ (G.adjMatrix ℝ).mulVec y.ofLp| ≤ lam * (‖x‖ * ‖y‖) := by
  let b := hA.eigenvectorBasis
  have hnorm_x : ∑ i : Fin n, (inner ℝ (b i) x) ^ 2 = ‖x‖ ^ 2 := by
    simpa [Real.norm_eq_abs, sq_abs] using b.sum_sq_norm_inner_right x
  have hnorm_y : ∑ i : Fin n, (inner ℝ (b i) y) ^ 2 = ‖y‖ ^ 2 := by
    simpa [Real.norm_eq_abs, sq_abs] using b.sum_sq_norm_inner_right y
  have hterm_le : ∀ i : Fin n,
      |hA.eigenvalues i * inner ℝ (b i) x * inner ℝ (b i) y| ≤
        lam * (|inner ℝ (b i) x| * |inner ℝ (b i) y|) := by
    by_cases hmult : ∃ i₁ : Fin n, i₁ ≠ i₀ ∧ hA.eigenvalues i₁ = (d : ℝ)
    · rcases hmult with ⟨i₁, hi₁_ne, hi₁_eq⟩
      have hd_le : |(d : ℝ)| ≤ lam := hi₁_eq ▸ hlam i₁ hi₁_ne
      have hall : ∀ i : Fin n, |hA.eigenvalues i| ≤ lam := fun i =>
        if hi : i = i₀ then hi ▸ hi₀.symm ▸ hd_le else hlam i hi
      intro i
      rw [abs_mul, abs_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_right (hall i) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    · push Not at hmult
      have hx0 : inner ℝ (b i₀) x = 0 :=
        orth_component_vanishes_if_unique_deg hn G hA hreg hi₀ hmult hx
      intro i
      by_cases hi : i = i₀
      · subst hi; simp [hx0]
      · rw [abs_mul, abs_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_right (hlam i hi) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hcs_sq : (∑ i : Fin n, |inner ℝ (b i) x| * |inner ℝ (b i) y|) ^ 2 ≤
      (‖x‖ * ‖y‖) ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
      (fun i => |inner ℝ (b i) x|) (fun i => |inner ℝ (b i) y|)
    simpa [sq_abs, hnorm_x, hnorm_y, mul_pow] using hcs
  have hcs : ∑ i : Fin n, |inner ℝ (b i) x| * |inner ℝ (b i) y| ≤ ‖x‖ * ‖y‖ := by
    have hnonneg_lhs : 0 ≤ ∑ i : Fin n, |inner ℝ (b i) x| * |inner ℝ (b i) y| :=
      Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hnonneg_rhs : 0 ≤ ‖x‖ * ‖y‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    rw [← abs_of_nonneg hnonneg_lhs, ← abs_of_nonneg hnonneg_rhs]
    exact sq_le_sq.mp hcs_sq
  rw [hermitian_bilinear_eq_sum_eigenvalues hA x y]
  calc |∑ i : Fin n, hA.eigenvalues i * inner ℝ (b i) x * inner ℝ (b i) y|
      ≤ ∑ i : Fin n, |hA.eigenvalues i * inner ℝ (b i) x * inner ℝ (b i) y| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, lam * (|inner ℝ (b i) x| * |inner ℝ (b i) y|) :=
          Finset.sum_le_sum fun i _ => hterm_le i
    _ = lam * ∑ i : Fin n, |inner ℝ (b i) x| * |inner ℝ (b i) y| := by rw [Finset.mul_sum]
    _ ≤ lam * (‖x‖ * ‖y‖) := mul_le_mul_of_nonneg_left hcs hlam0

/-- Direct Rayleigh-subspace form of the **Expander Mixing Lemma**: if every vector orthogonal
to the all-ones vector satisfies `|x ⬝ᵥ A y| ≤ λ ‖x‖ ‖y‖` (for `0 ≤ λ`), then for all
`S, T : Finset (Fin n)`, `|e(S, T) - (d / n) * |S| * |T|| ≤ λ * √(|S| * |T|)`. -/
theorem expander_mixing_of_orth_bound {n d : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian) (hreg : G.IsRegularOfDegree d)
    {lam : ℝ} (hlam0 : 0 ≤ lam)
    (horth : ∀ x y : EuclideanSpace ℝ (Fin n),
      inner ℝ (WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ))) x = 0 →
      inner ℝ (WithLp.toLp 2 (fun _ : Fin n => (1 : ℝ))) y = 0 →
      |x.ofLp ⬝ᵥ (G.adjMatrix ℝ).mulVec y.ofLp| ≤ lam * (‖x‖ * ‖y‖))
    (S T : Finset (Fin n)) :
    |(((S ×ˢ T).filter (fun p => G.Adj p.1 p.2)).card : ℝ) -
        ((d : ℝ) / n) * S.card * T.card| ≤
      lam * Real.sqrt ((S.card : ℝ) * T.card) := by
  have hdec := orth_decomp_quadratic hn G hA hreg S T
  rcases hdec with ⟨hx_orth, hy_orth, hx_sq, hy_sq, hdiff⟩
  rw [← ind_dotProduct_adjMatrix_ind G S T, hdiff]
  have hxy : ‖indVec S - ((S.card : ℝ) / n) • onesVec n‖ *
        ‖indVec T - ((T.card : ℝ) / n) • onesVec n‖ ≤
      Real.sqrt ((S.card : ℝ) * T.card) := by
    have hx_le : ‖indVec S - ((S.card : ℝ) / n) • onesVec n‖ ≤ Real.sqrt (S.card : ℝ) := by
      refine Real.le_sqrt_of_sq_le ?_
      rw [hx_sq]
      exact sub_le_self _ (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    have hy_le : ‖indVec T - ((T.card : ℝ) / n) • onesVec n‖ ≤ Real.sqrt (T.card : ℝ) := by
      refine Real.le_sqrt_of_sq_le ?_
      rw [hy_sq]
      exact sub_le_self _ (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    calc ‖indVec S - ((S.card : ℝ) / n) • onesVec n‖ *
            ‖indVec T - ((T.card : ℝ) / n) • onesVec n‖
        ≤ Real.sqrt (S.card : ℝ) * Real.sqrt (T.card : ℝ) :=
            mul_le_mul hx_le hy_le (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.sqrt ((S.card : ℝ) * T.card) := (Real.sqrt_mul (Nat.cast_nonneg _) _).symm
  calc |((indVec S - ((S.card : ℝ) / n) • onesVec n).ofLp ⬝ᵥ
          (G.adjMatrix ℝ).mulVec (indVec T - ((T.card : ℝ) / n) • onesVec n).ofLp)|
      ≤ lam * (‖indVec S - ((S.card : ℝ) / n) • onesVec n‖ *
            ‖indVec T - ((T.card : ℝ) / n) • onesVec n‖) :=
          horth _ _ hx_orth hy_orth
    _ ≤ lam * Real.sqrt ((S.card : ℝ) * T.card) := mul_le_mul_of_nonneg_left hxy hlam0

/-- **Expander Mixing Lemma**: for any `d`-regular graph on `Fin n` with `hA : (G.adjMatrix ℝ).IsHermitian`,
`hA.eigenvalues i₀ = d`, and all other eigenvalues satisfying `|hA.eigenvalues i| ≤ λ` (`0 ≤ λ`),
`|e(S, T) - (d / n) * |S| * |T|| ≤ λ * √(|S| * |T|)` for all `S, T : Finset (Fin n)`. -/
theorem expander_mixing_lemma {n d : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hA : (G.adjMatrix ℝ).IsHermitian) (hreg : G.IsRegularOfDegree d)
    (i₀ : Fin n) (hi₀ : hA.eigenvalues i₀ = (d : ℝ)) {lam : ℝ} (hlam0 : 0 ≤ lam)
    (hlam : ∀ i : Fin n, i ≠ i₀ → |hA.eigenvalues i| ≤ lam)
    (S T : Finset (Fin n)) :
    |(((S ×ˢ T).filter (fun p => G.Adj p.1 p.2)).card : ℝ) -
        ((d : ℝ) / n) * S.card * T.card| ≤
      lam * Real.sqrt ((S.card : ℝ) * T.card) :=
  expander_mixing_of_orth_bound i₀.pos G hA hreg hlam0
    (fun _ _ hx hy => orth_bilinear_abs_bound i₀.pos G hA hreg hi₀ hlam0 hlam hx hy) S T

end RegularAndMixing

/-! ## Section 3: Hoffman's Ratio Bound -/

section Hoffman

/-- **Hoffman's Ratio Bound**: for any `d`-regular graph on `Fin n` (`0 < n`, `0 < d`),
any independent set `S : Finset (Fin n)`, and any spectral lower bound `λ_min < 0`
(`∀ i, λ_min ≤ hA.eigenvalues i`), `|S| ≤ n * (-λ_min) / (d - λ_min)`. -/
theorem hoffman_ratio_bound {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian)
    (hreg : G.IsRegularOfDegree d) {lamMin : ℝ} (hlam_neg : lamMin < 0)
    (hlam_le : ∀ i : Fin n, lamMin ≤ hA.eigenvalues i)
    (S : Finset (Fin n)) (hS : ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v) :
    (S.card : ℝ) ≤ (n : ℝ) * (-lamMin) / ((d : ℝ) - lamMin) := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hd_pos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hden_pos : (0 : ℝ) < (d : ℝ) - lamMin := by linarith
  by_cases hS0 : S.card = 0
  · simp only [hS0, Nat.cast_zero]
    exact div_nonneg (mul_nonneg hn_pos.le (by linarith)) hden_pos.le
  have hS_pos : (0 : ℝ) < S.card := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hS0)
  have hdec := orth_decomp_quadratic hn G hA hreg S S
  rcases hdec with ⟨_, _, hx_sq, _, hdiff⟩
  have hquad0 : (indVec S).ofLp ⬝ᵥ (G.adjMatrix ℝ).mulVec (indVec S).ofLp = 0 := by
    rw [ind_dotProduct_adjMatrix_ind]
    have hempty : (S ×ˢ S).filter (fun p => G.Adj p.1 p.2) = ∅ := by
      ext ⟨u, v⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.notMem_empty, iff_false, not_and]
      intro ⟨hu, hv⟩
      exact hS u hu v hv
    simp [hempty]
  rw [hquad0, zero_sub] at hdiff
  have hray : lamMin * ((S.card : ℝ) - (S.card : ℝ) ^ 2 / n) ≤
      -((d : ℝ) / n) * S.card * S.card := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hr := (@hermitian_rayleigh_bounds n (G.adjMatrix ℝ) hA lamMin
      (Finset.univ.sup' Finset.univ_nonempty hA.eigenvalues) hlam_le
      (fun i => Finset.le_sup' hA.eigenvalues (Finset.mem_univ i))
      (indVec S - ((S.card : ℝ) / n) • onesVec n)).1
    rw [hx_sq, ← hdiff] at hr
    linarith
  have hmul : (S.card : ℝ) * ((d : ℝ) * S.card + lamMin * (n - S.card)) ≤ 0 := by
    have h1 : lamMin * (n * S.card - S.card ^ 2) ≤ -(d : ℝ) * S.card ^ 2 := by
      have h2 := mul_le_mul_of_nonneg_right hray hn_pos.le
      have hn0 : (n : ℝ) ≠ 0 := hn_pos.ne'
      field_simp [hn0] at h2 ⊢
      linarith
    linarith
  have hlin : (d : ℝ) * S.card + lamMin * (n - S.card) ≤ 0 :=
    nonpos_of_mul_nonpos_right hmul hS_pos
  have hbound : (S.card : ℝ) * ((d : ℝ) - lamMin) ≤ (n : ℝ) * (-lamMin) := by linarith
  exact (le_div_iff₀ hden_pos).mpr hbound

/-- **Hoffman's Ratio Bound** expressed directly with the minimum eigenvalue
`λ_min = Finset.univ.inf' Finset.univ_nonempty hA.eigenvalues` (which is automatically negative
when `0 < n` and `0 < d`). -/
theorem hoffman_ratio_bound_inf {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian)
    (hreg : G.IsRegularOfDegree d) (S : Finset (Fin n))
    (hS : ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v) :
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    let lamMin := Finset.univ.inf' Finset.univ_nonempty hA.eigenvalues
    (S.card : ℝ) ≤ (n : ℝ) * (-lamMin) / ((d : ℝ) - lamMin) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact hoffman_ratio_bound hn hd G hA hreg
    (regular_min_eigenvalue_neg hn hd G hA hreg)
    (fun i => Finset.inf'_le hA.eigenvalues (Finset.mem_univ i)) S hS

end Hoffman

/-! ## Section 4: Spectral Edge-Expansion (Easy Cheeger Inequality) -/

section Cheeger

/-- **Spectral Edge-Expansion (Easy Cheeger Inequality)**: for any `d`-regular graph on `Fin n`
with `hA.eigenvalues i₀ = d` and all other eigenvalues bounded above by `λ₂`, every vertex subset
`S : Finset (Fin n)` satisfies `e(S, Sᶜ) ≥ ((d - λ₂) / n) * |S| * (n - |S|)`. -/
theorem cheeger_edge_expansion {n d : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hA : (G.adjMatrix ℝ).IsHermitian) (hreg : G.IsRegularOfDegree d)
    (i₀ : Fin n) (hi₀ : hA.eigenvalues i₀ = (d : ℝ)) {lam2 : ℝ}
    (hlam2 : ∀ i : Fin n, i ≠ i₀ → hA.eigenvalues i ≤ lam2)
    (S : Finset (Fin n)) :
    ((((S ×ˢ Sᶜ).filter (fun p => G.Adj p.1 p.2)).card : ℝ)) ≥
      (((d : ℝ) - lam2) / n) * S.card * ((n : ℝ) - S.card) := by
  have hn : 0 < n := i₀.pos
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hsplit_edges :
      (((S ×ˢ S).filter (fun p => G.Adj p.1 p.2)).card : ℝ) +
        (((S ×ˢ Sᶜ).filter (fun p => G.Adj p.1 p.2)).card : ℝ) =
      (d : ℝ) * S.card := by
    have hdisj : Disjoint ((S ×ˢ S).filter (fun p => G.Adj p.1 p.2))
        ((S ×ˢ Sᶜ).filter (fun p => G.Adj p.1 p.2)) := by
      rw [Finset.disjoint_left]
      intro ⟨u, v⟩ h1 h2
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_compl] at h1 h2
      exact h2.1.2 h1.1.2
    have hunion :
        ((S ×ˢ S).filter (fun p => G.Adj p.1 p.2)) ∪
          ((S ×ˢ Sᶜ).filter (fun p => G.Adj p.1 p.2)) =
        (S ×ˢ Finset.univ).filter (fun p => G.Adj p.1 p.2) := by
      ext ⟨u, v⟩
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_product, Finset.mem_compl,
        Finset.mem_univ, and_true]
      tauto
    have hcard_sum :
        ((S ×ˢ S).filter (fun p => G.Adj p.1 p.2)).card +
          ((S ×ˢ Sᶜ).filter (fun p => G.Adj p.1 p.2)).card =
        ((S ×ˢ Finset.univ).filter (fun p => G.Adj p.1 p.2)).card := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    have hcard_deg :
        ((S ×ˢ Finset.univ).filter (fun p => G.Adj p.1 p.2)).card = d * S.card := by
      have hbi : ((S ×ˢ Finset.univ).filter (fun p => G.Adj p.1 p.2)).card =
          ∑ u ∈ S, (G.neighborFinset u).card := by
        rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := S) (by
          intro ⟨u, v⟩ hp
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hp
          exact hp.1.1)]
        refine Finset.sum_congr rfl fun u hu => ?_
        have himg : ((S ×ˢ Finset.univ).filter (fun p => G.Adj p.1 p.2)).filter (fun p => p.1 = u) =
            (G.neighborFinset u).map ⟨fun v => (u, v), fun _ _ h => congrArg Prod.snd h⟩ := by
          ext ⟨x, y⟩
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
            Finset.mem_map, SimpleGraph.mem_neighborFinset]
          constructor
          · rintro ⟨⟨_, hadj⟩, rfl⟩
            exact ⟨y, hadj, rfl⟩
          · rintro ⟨v, hadj, hv⟩
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hv
            exact ⟨⟨hu, hadj⟩, rfl⟩
        rw [himg, Finset.card_map]
      rw [hbi]
      simp_rw [G.card_neighborFinset_eq_degree, hreg.degree_eq]
      simp [mul_comm]
    exact_mod_cast hcard_sum.trans hcard_deg
  have hdec := orth_decomp_quadratic hn G hA hreg S S
  rcases hdec with ⟨hx_orth, _, hx_sq, _, hdiff⟩
  have hray : (indVec S).ofLp ⬝ᵥ (G.adjMatrix ℝ).mulVec (indVec S).ofLp -
        ((d : ℝ) / n) * S.card * S.card ≤
      lam2 * ((S.card : ℝ) - (S.card : ℝ) ^ 2 / n) := by
    have hr := orth_rayleigh_upper_of_lambda2 hn G hA hreg hi₀ hlam2 hx_orth
    rw [← hdiff, hx_sq] at hr
    exact hr
  rw [ind_dotProduct_adjMatrix_ind] at hray
  have hcut : (((S ×ˢ Sᶜ).filter (fun p => G.Adj p.1 p.2)).card : ℝ) ≥
      (d : ℝ) * S.card - (((d : ℝ) / n) * S.card * S.card +
        lam2 * ((S.card : ℝ) - (S.card : ℝ) ^ 2 / n)) := by linarith
  have halg : (d : ℝ) * S.card - (((d : ℝ) / n) * S.card * S.card +
        lam2 * ((S.card : ℝ) - (S.card : ℝ) ^ 2 / n)) =
      (((d : ℝ) - lam2) / n) * S.card * ((n : ℝ) - S.card) := by
    field_simp [hn0]
    ring
  linarith

end Cheeger

end Arith4Ext.GraphSpectral
