# Krenn–Gu Conjecture (`PPL 007`): Literature Status & Verified Experimental Barriers

## 1. Late-2026 Literature Status & Repo Scope

- **Full conjecture over $\mathbb{C}$:** Krenn et al. (`arXiv:2611.26300`, Nov 19, 2026) already credit **Rishi Rajasekaran** with a Lean-verified proof of the full Krenn–Gu conjecture ($D \le 2$ for all even $N \ge 6$) over $\mathbb{C}$, even though `google-deepmind/formal-conjectures` (`main` at `FormalConjectures/Paper/MonochromaticQuantumGraph.lean`) still tags `eqSystem8_no_solution_d3`, `eqSystem10_no_solution_d7`–`d3`, and `eqSystem12..16_no_solution_d3` as `@[category research open]`.
- **Our verified contribution (`RHDirect/PPL007_WorldRecord.lean`):** Stands independently as a verified, solver-free **general commutative integral-domain theorem** (`ppl007_world_record_domain`, `_complex`, `_real`): for **all even $N \ge 10$**, **$D \le N - 3$** over *every* commutative integral domain $K$ (including positive characteristic, ahead of `KitaKen1`'s $D \le N - 2$ and `(10, 8)` domain theorem, and generalizing `KitaKen1`'s `(10, 8)` solver-free algebraic framework via general Bogdanov's lemma `exists_mixed_matching_general`).

---

## 2. Target 1 — `(N = 8, D = 3)` over $\mathbb{C}$: Phase 1–2 SAT + Nullstellensatz & Analytic-Jacobian LM Check

### 2.1 Phase 1–2 Support-SAT + Exact $\mathbb{Z}/\mathbb{Q}$ Nullstellensatz (`krenn_gu_phase2.py`)
- **Validation Gates:**
  - `Witness4_d3`: PASS (`0` false refutations).
  - `(6, 3)` over $\mathbb{C}$: all `8 / 8` $S_6 \times S_3$ monochromatic matching-skeleton orbits (`3,375 / 3,375` triples) proved `UNSAT_PROVED` in `121.01s`.
- **`(8, 3)` run (`31` orbits, `240s` cap/orbit, `544.63s` total wall time):**
  - `0 / 31` orbits closed (`10` `TIMEOUT` across `337,785` triples; `21` `SURVIVING_SUPPORT` across `819,840` triples with dense supports `|S| \in [124, 144]`).
  - Phase 3 / high-degree Macaulay elimination on `(8, 3)` was **intentionally not started**.

### 2.2 Analytic-Jacobian Levenberg–Marquardt Check (`check_8x3_gn.py`)
- Tested all **21 surviving `(8, 3)` supports** from Phase 2 with exact Cauchy–Riemann analytic Jacobians (`jacobian_selftest_max_err = 1.225e-8`), running `168` total restarts (`8` per support, `mono_weight ∈ {1.0, 50.0}`, total wall time `52.22s`).
- **Outcome:** **0 / 21 supports converged** to a genuine complex solution (`EqSystemN 8 3`).
  - Global minimum unweighted $L_\infty$ residual: **`1.074714e-03`** (`orbit 12`, `L_2 = 1.351810e-03`, `best_mono_linf = 1.247e-04`, `|S| = 132`, `6,561` active equations).
  - Across all 21 supports, `best_linf` ranged from **`1.0747e-03`** to **`7.7511e-02`**.
  - Every trajectory drove a subset of active variables toward `0` (`min |z| ∈ [1.78e-268, 1.07e-29]`, `max |z| ∈ [3.33, 12.97]`) while still hitting a hard residual wall $\ge 1.07 \times 10^{-3}$.

---

## 3. Target 2 — `(N = 10, D = 7)` / General $D = N - 3$ (`2` Exceptions per Vertex): Verified Structural Barriers

Probed whether the solver-free algebraic proof of [PPL007_WorldRecord.lean](../RHDirect/PPL007_WorldRecord.lean) ($D = N - 2$, `1` exception/vertex) or `KitaKen1`'s `(6, 4)` support-only LRAT framework extends directly to `D = N - 3` (`2` exceptions/vertex).

### 3.1 What Transfers Cleanly to $D = N - 3$
1. **Full-column & 2-exception decomposition (free):** `QuantumCR.fullColumnsAt_of_eqSystem_domain` already holds for all even $N \ge 4, D \ge 3$, giving each vertex $D$ injective full-column anchors and `2` exceptional neighbors (`G_mut` has maximum degree $\le 2$: isolated vertices, paths $P_k$, and cycles $C_k$; `106` global decompositions on $N = 10$).
2. **Local impure-color bounds (independent of $D$):**
   - *Type 0 (`0` mutual, `2` one-way rows $r_1, r_2$):* $\le 2$ impure colors outside $\{r_1, r_2\}$ (confirmed over $\mathbb{F}_2$ even when $r_1 = r_2$).
   - *Type 1 (`1` mutual + `1` one-way row $r_2$):* rank-1 `pencil_three` transfers verbatim on rows $i \ne r_2$.
   - *Type 2 (`2` mutual edges):* $\le 4$ impure colors total at a single vertex (confirmed over $\mathbb{F}_2$ for both $D = 5$ and $D = 7$, even with single-support columns enforced).
3. **Clean-color finish still closes:** Given just **`k = 3` clean diagonal matchings** + arbitrary mutual matrices $M_e$ on `2`-regular $G_{\mathrm{mut}}$ (`C_4+C_4`, `C_8`, `C_3+C_5` at $N = 8$; `C_4+C_6`, `C_{10}`, `C_5+C_5` at $N = 10$), exact CEGAR gives `UNSAT` over both $\mathbb{F}_2$ (`0.7s–3.3s` total) and $\mathbb{F}_3$ (`0.70s–1.07s` per topology).

### 3.2 Two Verified Mathematical Obstructions
1. **Pure support-only SAT (`KitaKen1 (6, 4)` method) fails for $D = N - 3$ ($N \ge 8$):**
   - At `(6, 4)` ($N - D = 2$), $G_{\mathrm{mut}}$ has max degree `1` ($\le 1$ perfect matching in $G_{\mathrm{mut}}$), and anchor-normalized support-SAT (`N_S(\iota) \ne 1`) proves **UNSAT in `0.75s`**.
   - At `(8, 5)` and `(10, 7)` ($N - D = 3$), a `2`-regular $G_{\mathrm{mut}}$ such as $C_4 \sqcup C_4$ ($N = 8$) or $C_4 \sqcup C_6$ ($N = 10$) contains **4 perfect matchings inside $G_{\mathrm{mut}}$ alone**, guaranteeing $N_S(\iota) \ge 4$ whenever mutual edges are active. Consequently, pure support rules ($N_S \ne 1$) survive (`(8, 5)` survives in `6.17s`, `188` active edges; `(10, 7)` survives in `4.10s`, `411` active edges) and cannot refute `(8, 5)` or `(10, 7)`.
2. **Global `Bset`-size counting (`PPL007_WorldRecord.lean` method) breaks at $D = N - 3$:**
   - Because $|E(G_{\mathrm{mut}})|$ can reach $N$ (vs. $N/2$ at $D = N - 2$), local bad colors no longer force $D - |B_{\mathrm{set}}| \ge 3$.
   - Even enforcing **exact 2-step slice factorization** ($C_1, C_2, R_c$ expanded to second-step neighbors $v_1, v_2$) + **exact anchor reciprocity** + shared $s_e(c)$ at every vertex over $\mathbb{F}_2$, all three `2`-regular `(8, 5)` topologies (`C_4+C_4`, `C_8`, `C_3+C_5`) still achieve **`max |Bset| = 5/5`** (`0` globally clean colors, `1.93s` total), and a single coupled $C_4$ at $D = 7$ already achieves **`max |bad(C_4)| = 7/7`**.
   - Meanwhile, full exact nonlinear $\mathbb{F}_2$ CEGAR on `(8, 5)` with `C_4+C_4` / `C_8` timed out at `20s` (`~1,100–1,186` equations) without refuting, confirming that extending the **integral-domain** bound to $D = N - 3$ requires a genuinely new global invariant beyond 2-step slices and global `Bset` counting.
