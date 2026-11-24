# `Arithmetica4` Tier A Library Extensions (`RHDirect/Arith4Ext_*`)

All **22** extension modules below (`58,382` lines total) are written **100% from scratch** on targeted Mathlib imports (zero monolithic `import Mathlib`, zero Tier C imports), compiled fresh from source on Lean `v4.33.1`, verified with official **`leanchecker` (`PASS`)**, and exhaustively checked via **`Lean.collectAxioms`** across every constant (`⊆ {propext, Classical.choice, Quot.sound}`).

---

## Verified `Arith4Ext_*` Tier A Modules (`22` Modules)

### 1. [`RHDirect/Arith4Ext_AdditiveFourier.lean`](../RHDirect/Arith4Ext_AdditiveFourier.lean) (`2,400` L)
- **Namespace:** `Arith4Ext.AdditiveFourier`
- **API Highlights:**
  1. **Ruzsa Calculus (`AddCommGroup`):** `ruzsa_triangle_inequality`, `_add`, `_sum`, `ruzsa_covering_lemma`, `_real`, `_sub`.
  2. **Petridis & Plünnecke–Ruzsa:** genuine Minkowski `iterSum`, `petridis_lemma`, `petridis_iterated_sumset`, `pluennecke_ruzsa`, `pluennecke_ruzsa_sum`.
  3. **Additive Energy & BSG:** `addRep`, `subRep`, `addEnergy`, `addEnergy_eq_sum_sq_addRep`, `cauchy_schwarz_addEnergy`, Sudakov–Szemerédi–Vu `bipartite_paths_of_length_three`, `balog_szemeredi_gowers`, `balog_szemeredi_gowers_single`.
  4. **Discrete Fourier (`AddChar G ℂ` & `ZMod N`) + Roth Bohr Increment:** `sum_addChar_eq_zero_of_ne_one`, `addChar_orthogonality`, `charTransform_convG`, `eZMod`, `dft`, `dft_inversion`, `plancherel_zmod`, `parseval_zmod`, `addEnergy_eq_dft_fourth_moment`, `largeSpectrum_card_le`, `threeAPCount_eq_dft`, `roth_large_fourier_coeff`, `bohrSet`, `roth_bohr_density_increment`.

### 2. [`RHDirect/Arith4Ext_AlgebraicMethod.lean`](../RHDirect/Arith4Ext_AlgebraicMethod.lean) (`1,531` L)
- **Namespace:** `Arith4Ext.AlgebraicMethod`
- **API Highlights:**
  1. **Combinatorial Nullstellensatz:** `combinatorial_nullstellensatz_fin`, `combinatorial_nullstellensatz`.
  2. **Restricted / Modular Sumsets:** `cauchy_davenport`, `erdos_heilbronn` (`ZMod p`).
  3. **Polynomial Zeros & Linear Rank:** `schwartz_zippel`, `chevalley_warning`, `chevalley_warning_nonzero_root`, `babai_frankl_triangular`, `oddtown_bound`.

### 3. [`RHDirect/Arith4Ext_AnalyticNT.lean`](../RHDirect/Arith4Ext_AnalyticNT.lean) (`4,178` L)
- **Namespace:** `Arith4Ext.AnalyticNT`
- **API Highlights:**
  1. **Abel / Partial Summation (`ℝ` & `ℂ`):** discrete `abel_summation_Icc`, `norm_sum_mul_le_abel` / `_antitone` / `_monotone`, and integral `abel_summation_integral_Icc_real` / `_complex`.
  2. **Dirichlet Hyperbola & Divisor Moments:** `dirichlet_hyperbola_identity` / `_sqrt`, `sum_divisors_card_sub_mul_log_le` (`|∑_{n≤N} d(n) - N log N| ≤ 3N`), `divisors_card_le_two_sqrt`, `sum_divisors_card_pow_le`.
  3. **Weyl Differencing & Van der Corput `A`-Process:** `norm_sum_e_linear_Ico_le`, `weyl_differencing_Ico`, `van_der_corput_A_process_Ico`, `weyl_quadratic_diff_bound`.
  4. **Dirichlet & Fejér Kernels:** `dirichletKernel_eq_sin_div_sin`, `integral_dirichletKernel`, `fejerKernel_nonneg`, `fejerKernel_eq_sin_sq_div`, `integral_fejerKernel`, `sum_fejerKernel_roots`, `fejerKernel_tail_le`.
  5. **Explicit Chebyshev & Mertens I–III:** `chebyshevTheta_le_two_log_two_mul`, `centralBinom_chebyshev_lower`, `primePi_le_explicit` / `_ge_explicit`, `primeLogRecipSum_bounds`, `primeRecipSum_bounds`, `eulerProdPartial_bounds`.

### 4. [`RHDirect/Arith4Ext_AutomataCombinatorics.lean`](../RHDirect/Arith4Ext_AutomataCombinatorics.lean) (`880` L)
- **Namespace:** `Arith4Ext.AutomataCombinatorics`
- **API Highlights:**
  1. **Fine–Wilf Periodicity:** `HasPeriod`, `hasPeriod_iff_getElem`, `hasPeriod_mul`, `hasPeriod_drop`, `hasPeriod_take`, `fine_wilf`, `fine_wilf_tight`.
  2. **Lyndon–Schützenberger & Primitive Roots:** `lyndon_schutzenberger_comm`, `IsPrimitive`, `primitive_root_exists`, `primitive_root_unique`, `lyndon_schutzenberger_power_comm`.
  3. **Myhill–Nerode & NFA Determinization:** `myhill_nerode_fooling_set`, `no_small_dfa_of_fooling_set`, `nfa_determinization_dfa`, `sep_le_two_pow_nsep`.
  4. **Automata Closure & Products:** `prodDFA`, `dfa_inter_closure`, `dfa_union_closure`, `dfa_symmDiff_closure`, `complDFA`, `dfa_compl_closure`, `revNFA`, `nfa_reversal_closure`, `dfa_reversal_closure`.
  5. **Pumping Lemmas:** `dfa_pumping_lemma`, `dfa_unary_lcm_pump`, `dfa_unary_block_lcm_eq`.

### 5. [`RHDirect/Arith4Ext_CircleMethod.lean`](../RHDirect/Arith4Ext_CircleMethod.lean) (`3,617` L)
- **Namespace:** `Arith4Ext.CircleMethod` (builds on `RHDirect.Arith4Ext_SieveCharacters`)
- **API Highlights:**
  1. **Circle Method Orthogonality & Major/Minor Split:** `e`, `expSum`, `repCount`, `integral_e_int`, `circle_method_repCount_eq_integral`, `parseval_expSum`, `circle_method_major_minor_split`, `minor_arc_Linfty_L2_bound_parseval`.
  2. **Ramanujan Sums & Odd-Goldbach Ternary Singular Series:** `ramanujanSum`, `ternarySingularTerm`, `ternaryLocalFactor`, `ramanujanSum_holder`, `ramanujanSum_orthogonality`, `summable_ternarySingularTerm`, `ternarySingularSeries_ge_one`.
  3. **Weyl Quadratic, Hua `L⁴` & Bilinear Minor-Arc Bounds:** `weylQuadSum`, `vinogradov_minRecipDist_sum`, `weyl_quadratic_bound`, `hua_L4_bound`, `bilinear_minor_arc_bound`, `typeI_minor_arc_bound`, `vaughan_expSum_decomp`.
  4. **Schnirelmann Density & Mann (1942):** `schnirelmannDensity`, `mann_theorem`, `schnirelmann_density_add_ge`, `schnirelmann_basis_theorem`.

### 6. [`RHDirect/Arith4Ext_ConvexOptDuality.lean`](../RHDirect/Arith4Ext_ConvexOptDuality.lean) (`1,934` L)
- **Namespace:** `Arith4Ext.ConvexOptDuality`
- **API Highlights:**
  1. **Hyperplane Separation & Farkas' Lemma:** `hyperplane_separation_closed_convex`, `hyperplane_separation_cone`, `farkas_lemma`, `farkas_lemma_nonneg_le`, `farkas_lemma_le`.
  2. **LP Duality & Complementary Slackness:** `lp_weak_duality`, `lp_complementary_slackness`, `lp_strong_duality`.
  3. **Von Neumann Minimax (1928) & Birkhoff–von Neumann (1946):** `von_neumann_minimax_saddle`, `von_neumann_minimax_value`, `birkhoff_hall_permutation`, `birkhoff_von_neumann`.
  4. **König–Egerváry, Mirsky & Dilworth:** `konig_egervary_weak`, `konig_egervary`, `mirsky_theorem`, `dilworth_weak`, `dilworth_theorem`.

### 7. [`RHDirect/Arith4Ext_EntropyCoding.lean`](../RHDirect/Arith4Ext_EntropyCoding.lean) (`2,445` L)
- **Namespace:** `Arith4Ext.EntropyCoding`
- **API Highlights:**
  1. **Shannon Entropy, KL & Pinsker:** `shannonEntropy`, `klDiv`, `tvDist`, `condEntropy`, `mutualInfo`, `gibbs_inequality`, `pinsker_inequality`, `shannonEntropy_chain_rule`, `shannonEntropy_subadditive`, `condEntropy_pair_le`.
  2. **Shearer's Lemma, Han's Inequality & Loomis–Whitney:** `shearer_entropy_lemma`, `hans_inequality`, `shearer_projection_card`, `loomis_whitney_inequality`.
  3. **Kraft–McMillan & Binary Entropy:** `kraft_mcmillan_inequality`, `kraft_exists_prefix_free`, `shannon_source_coding_lower_bound`, `sum_choose_le_two_rpow_binEntropy2`.
  4. **Classical Coding & General `𝔽_p` MacWilliams:** `singleton_bound`, `hamming_sphere_packing_bound`, `gilbert_varshamov_bound`, `plotkin_bound`, `card_mul_card_dualCode`, `macwilliams_identity`, `macwilliams_identity_binary`.

### 8. [`RHDirect/Arith4Ext_GeneratingFunctions.lean`](../RHDirect/Arith4Ext_GeneratingFunctions.lean) (`4,943` L)
- **Namespaces:** `Arith4Ext.GeneratingFunctions`, `IntPartition`
- **API Highlights:**
  1. **Formal Power Series & Recurrences:** `psDeriv` calculus, `catalanSeq_closed_form`, `catalanGF_eq`, `eq_catalanGF_of_quad_eq`, Fibonacci & general linear recurrences.
  2. **Integer Partitions:** Euler's `euler_distinct_eq_odd_partitions`, pentagonal number theorem (`partitionGF_mul_pentagonalPS`, `partitionCount_pentagonal_recurrence`), `partitionCount_mul_eq_divisor_sum`, `erdos_partition_upper_bound` (`p(n) ≤ exp(π √(2n/3))`).
  3. **Non-Asymptotic Stirling / Robbins & `q`-Binomial:** `robbins_ratio_bounds`, `stirling_robbins_two_sided`, `stirling_factorial_bounds`, `qBinom_eval_theorem`, `qBinom_chu_vandermonde`.

### 9. [`RHDirect/Arith4Ext_GeometryIncidence.lean`](../RHDirect/Arith4Ext_GeometryIncidence.lean) (`7,132` L)
- **Namespace:** `Arith4Ext.GeometryIncidence`
- **API Highlights:**
  1. **Plane Primitives & Sylvester–Gallai:** `sylvester_gallai`, `sylvester_gallai_pair`.
  2. **Topology-Free `SlabWiring` Crossing Lemmas:** `slabWiring_crossing_lemma`, `multigraph_slabWiring_crossing_lemma`, `xMonotone_multi_to_slabWiring`.
  3. **Szemerédi–Trotter & Beck's Theorem:** `szemeredi_trotter` (`I ≤ 4|P|^{2/3}|L|^{2/3} + 4|P| + |L|`), `k_rich_lines_bound`, `k_rich_incidences_bound`, `beck_theorem`.
  4. **Unit & Distinct Distances:** `congruent_circle_incidences_le`, `unit_distances_le` (`≤ 18 n^{4/3}`), Székely `pinned_distinct_distances_ge` & `distinct_distances_ge` (`≥ n^{4/5}/10000`).

### 10. [`RHDirect/Arith4Ext_GraphSpectral.lean`](../RHDirect/Arith4Ext_GraphSpectral.lean) (`925` L)
- **Namespace:** `Arith4Ext.GraphSpectral`
- **API Highlights:**
  1. **Hermitian Adjacency, Trace Formulas & Rayleigh Bounds:** `adjMatrix_isHermitian`, `adjMatrix_trace_zero`, `adjMatrix_sum_eigenvalues_zero`, `adjMatrix_trace_sq`, `adjMatrix_sum_sq_eigenvalues`, `adjMatrix_trace_cube`, `adjMatrix_sum_cube_eigenvalues`, `hermitian_dotProduct_eq_sum_eigenvalues`, `hermitian_rayleigh_bounds`, `adjMatrix_rayleigh_bounds`.
  2. **Regularity & Expander Mixing Lemma:** `regular_exists_deg_eigenvalue`, `regular_min_eigenvalue_neg`, `expander_mixing_of_orth_bound`, `expander_mixing_lemma`.
  3. **Hoffman Ratio Bound & Cheeger Edge-Expansion:** `hoffman_ratio_bound`, `hoffman_ratio_bound_inf`, `cheeger_edge_expansion`.

### 11. [`RHDirect/Arith4Ext_LargeSieveDiophantine.lean`](../RHDirect/Arith4Ext_LargeSieveDiophantine.lean) (`3,206` L)
- **Namespace:** `Arith4Ext.LargeSieveDiophantine`
- **API Highlights:**
  1. **Large Sieve & Farey:** `distToInt`, `WellSpaced`, `eChar`, `gallagher_sobolev_sq`, `large_sieve_gallagher`, `large_sieve_gallagher_nat`, `farey_wellSpaced`, `large_sieve_farey`.
  2. **Geometry of Numbers (`Fin d → ℝ` / `ℤ^d`):** `blichfeldt_lattice`, `minkowski_convex_body`, `minkowski_convex_body_compact`, `discrete_blichfeldt_grid`.
  3. **Dirichlet Diophantine Approximation:** `dirichlet_simultaneous_nat`, `dirichlet_simultaneous_real`, `dirichlet_approx_1d_infinitely_many`.
  4. **Weyl Equidistribution & Fejér Approximation:** `EquidistributedMod1`, `fejer_trig_approx`, `weyl_criterion`, `irrational_rotation_equidistributed`, `kronecker_dense_fract`.
  5. **Liouville Irrationality Measure & Transcendence:** `two_le_natDegree_of_irrational_aeval_zero`, `liouville_int_poly`, `liouville_algebraic_irrational`, `transcendental_of_liouville_approx`.

### 12. [`RHDirect/Arith4Ext_MatroidsPosets.lean`](../RHDirect/Arith4Ext_MatroidsPosets.lean) (`2,516` L)
- **Namespace:** `Arith4Ext.MatroidsPosets`
- **API Highlights:**
  1. **Finite Matroids & Submodularity:** `exists_basis_extension`, `rank_submodular`, `circuit_elimination`, `strong_basis_exchange`.
  2. **Greedy & Matroid Intersection:** `matroid_greedy_exists`, `matroid_greedy_optimal`, `matroid_greedy_local_exchange_optimal`, Rado Hall-matroid & `edmonds_matroid_intersection`.
  3. **Poset Möbius Inversion & Rota Cross-Cut:** `mobiusFn_sum_left`, `mobiusFn_sum_right`, `poset_mobius_inversion_left`, `poset_mobius_inversion_right`, `rota_crosscut_theorem`, `boolean_lattice_mobius`, `divisor_lattice_mobius`.

### 13. [`RHDirect/Arith4Ext_MeasureConvex.lean`](../RHDirect/Arith4Ext_MeasureConvex.lean) (`1,174` L)
- **Namespace:** `Arith4Ext.MeasureConvex`
- **API Highlights:**
  1. **Carathéodory, Hull Diameter, Radon & Helly:** `caratheodory_finrank`, `caratheodory_fin`, `caratheodory_euclidean`, `convexHull_diam_bound`, `radon_lemma`, `radon_lemma_fin`, `helly_theorem`, `helly_theorem_fin`, `helly_theorem_euclidean`.
  2. **Loomis–Whitney Projections:** `loomis_whitney_2d`, `loomis_whitney_fin`, `loomis_whitney_rpow`, `loomis_whitney_3d`.
  3. **Steinhaus Difference-Set Theorem:** `steinhaus_pos_volume_shift`, `steinhaus_finite`, `steinhaus`, `steinhaus_ball`.
  4. **1D Brunn–Minkowski & Discrete Sumsets:** `discrete_sumset_int`, `discrete_sumset_real`, `brunn_minkowski_1d_compact`, `brunn_minkowski_1d`, `brunn_minkowski_1d_sub`, `brunn_minkowski_intervals`.

### 14. [`RHDirect/Arith4Ext_PolyInterpolation.lean`](../RHDirect/Arith4Ext_PolyInterpolation.lean) (`1,322` L)
- **Namespace:** `Arith4Ext.PolyInterpolation`
- **API Highlights:**
  1. **Lagrange Interpolation & Vandermonde:** `lagrangeBasis`, `lagrangeInterp`, `lagrangeInterp_unique`, `lagrangeInterp_reproduce`, `sum_lagrangeBasis_eq_one`, `vandermonde_linear_indep`.
  2. **Chebyshev `T_n` & Minimax Extremality:** `chebyshevT_eval_cos`, `chebyshevT_abs_le_one`, `monicChebyshevT_monic`, `chebyshevT_roots_card`, `chebyshev_minimax_monic`, `chebyshev_minimax_general`.
  3. **Bernstein Approximation:** `bernsteinPoly_id`, `bernsteinPoly_sq`, `bernsteinPoly_variance`, `bernsteinPoly_abs_sub_le_popoviciu`, `bernsteinPoly_lipschitz_rate`, `bernsteinPoly_tendsto_uniformlyOn`.
  4. **Lebesgue Quasi-Optimality:** `lebesgueFunction_ge_one`, `lebesgue_pointwise_bound`, `lebesgue_quasi_optimal_uniform`, `lebesgue_quasi_optimal_Icc`.

### 15. [`RHDirect/Arith4Ext_ProbExtremal.lean`](../RHDirect/Arith4Ext_ProbExtremal.lean) (`3,030` L)
- **Namespace:** `Arith4Ext.ProbExtremal`
- **API Highlights:**
  1. **Finite Probability & Lovász Local Lemma:** `FinProbSpace`, `prob`, `expect`, `prod`, `DependsOn`, `lll_asymmetric_prob_ge`, `lll_asymmetric_exists`, `lll_symmetric_exp`, `lll_symmetric_four`, `lll_product_asymmetric`, `lll_product_symmetric_exp`.
  2. **Chernoff–Hoeffding Concentration:** `hoeffding_lemma`, `hoeffding_upper`, `hoeffding_lower`, `hoeffding_two_sided`, `chernoff_upper_kl`, `chernoff_upper_universal`, `chernoff_upper`, `chernoff_lower_kl`, `chernoff_lower`.
  3. **Kővári–Sós–Turán & Dependent Random Choice:** `kovari_sos_turan_bipartite`, `kovari_sos_turan_simpleGraph`, `kovari_sos_turan_fin`, `dependent_random_choice_bipartite`, `dependent_random_choice_simpleGraph`, `dependent_random_choice_pairs`.
  4. **Crossing Lemma, Caro–Wei, Turán & Supersaturation:** `ProperGraphDrawing`, `crossing_lemma`, `caro_wei`, `turan_theorem`, `hypergraph_density_averaging`, `hypergraph_supersaturation_copies`, `graph_clique_supersaturation`.

### 16. [`RHDirect/Arith4Ext_QuantumLinearAlgebra.lean`](../RHDirect/Arith4Ext_QuantumLinearAlgebra.lean) (`1,401` L)
- **Namespace:** `Arith4Ext.QuantumLinearAlgebra`
- **API Highlights:**
  1. **Gram Matrices, Welch & Gerzon Bounds:** `cInner`, `cNormSq`, `gramMatrix`, `rankOne`, `frameOp`, `rInner`, `welch_frame_potential_bound`, `welch_etf_iff_frameOp_eq`, `welch_bound`, `gerzon_complex_bound` (`m ≤ d²`), `gerzon_real_bound` (`m ≤ d(d+1)/2`).
  2. **Matrix Positivity & Trace Inequalities:** `hsInner`, `hadamard`, `hsInner_cauchy_schwarz`, `isHermitian_eq_sum_rankOne`, `posSemidef_hadamard`, `trace_mul_nonneg_of_posSemidef`, `trace_mul_le_trace_mul_trace_of_posSemidef`.
  3. **Kronecker Product, Partial Transpose & Peres–Horodecki:** `kronecker`, `partialTranspose`, `partialTranspose_involutive`, `partialTranspose_trace`, `partialTranspose_kronecker`, `posSemidef_kronecker`, `peres_horodecki_separable_ppt`.
  4. **Weyl–Heisenberg Operators (`ZMod d`):** `weylOmega`, `weylShift`, `weylClock`, `weylDisplace`, `weylShift_unitary`, `weylClock_unitary`, `weyl_commutation`, `weylDisplace_unitary`, `weylDisplace_trace_ortho`.

### 17. [`RHDirect/Arith4Ext_RamseyCombinatorics.lean`](../RHDirect/Arith4Ext_RamseyCombinatorics.lean) (`2,068` L)
- **Namespace:** `Arith4Ext.RamseyCombinatorics`
- **API Highlights:**
  1. **Finite & Multicolor Ramsey:** `ramsey_two_color_finset`, `ramsey_two_color`, `ramsey_two_color_graph`, `ramsey_multicolor`, `ramsey_uniform_three_finset`, `ramsey_erdos_lower_binom`, `ramsey_erdos_lower`.
  2. **Schur, Erdős–Szekeres & Happy Ending:** `schur_theorem`, `erdos_szekeres_monotone`, `erdos_szekeres_monotone_tight`, `erdos_szekeres_happy_ending`.
  3. **Hales–Jewett & Van der Waerden:** `hales_jewett_theorem`, `van_der_waerden_theorem`.

### 18. [`RHDirect/Arith4Ext_SetSystemsCorrelation.lean`](../RHDirect/Arith4Ext_SetSystemsCorrelation.lean) (`1,568` L)
- **Namespace:** `Arith4Ext.SetSystemsCorrelation`
- **API Highlights:**
  1. **Bollobás Set-Pairs, LYM & Sperner:** `bollobas_set_pairs`, `bollobas_set_pairs_uniform`, `lym_inequality`, `choose_le_choose_half`, `sperner_theorem`.
  2. **Erdős–Ko–Rado & Sauer–Shelah:** `erdos_ko_rado`, `sauer_shelah`.
  3. **Ahlswede–Daykin, Harris–Kleitman–FKG & Marica–Schönheim:** `ahlswede_daykin_four_functions`, `harris_kleitman_fkg`, `harris_kleitman_upsets`, `kleitman_down_down`, `marica_schonheim`.

### 19. [`RHDirect/Arith4Ext_SieveCharacters.lean`](../RHDirect/Arith4Ext_SieveCharacters.lean) (`4,209` L)
- **Namespace:** `Arith4Ext.SieveCharacters`
- **API Highlights:**
  1. **Selberg Upper-Bound Sieve & Brun–Titchmarsh:** `selberg_quadratic_diagonalization`, `abs_selbergWeight_le_one`, `selbergQuadForm_opt`, `selbergQuadForm_ge_inv_G`, `selberg_fundamental_bound`, `selberg_upper_bound_sieve`, `selberg_coprime_interval_bound`, `selberg_primes_in_interval_bound`, `brun_titchmarsh_interval`.
  2. **Gauss Sum Norm & Pólya–Vinogradov (`MulChar (ZMod q) ℂ`):** `sum_zmodAddChar`, `norm_sq_dirichletGaussSum_eq`, `norm_dirichletGaussSum_eq_sqrt`, `polya_vinogradov`, `polya_vinogradov_of_ne_one`.
  3. **Turán–Kubilius & Hardy–Ramanujan Normal Order:** `turan_kubilius_additive`, `turan_kubilius_additive_simple`, `turan_kubilius_strongly_additive`, `hardy_ramanujan_omega_variance`, `hardy_ramanujan_normal_order_tail`.
  4. **Vaughan's Identity:** `vaughan_convolution_identity`, `vaughan_identity_pointwise`, `vaughan_bilinear_sum`.

### 20. [`RHDirect/Arith4Ext_SzemerediRegularity.lean`](../RHDirect/Arith4Ext_SzemerediRegularity.lean) (`3,071` L)
- **Namespace:** `Arith4Ext.SzemerediRegularity` (zero Mathlib Regularity imports)
- **API Highlights:**
  1. **Energy-Increment & Regularity Core:** `edgeCount`, `edgeDensity`, `IsEpsRegular`, `IsPartitionOf`, `partEnergy`, `pair_energy_refinement_eq`, `pair_energy_increment_of_witness`, `exists_venn_partition`, `exists_slicing`, `equipartition_chop_energy`, `szemeredi_refinement_step`, `szemeredi_regularity_lemma`.
  2. **Triangle Counting & Removal:** `triCount`, `triangle_counting_lemma`, `orderedTriCount`, `triangle_removal_lemma`.
  3. **Ruzsa–Szemerédi, Roth & Corners:** `ruzsa_szemeredi_unique_triangle`, `IsInducedMatching`, `ruzsa_szemeredi_induced_matching`, `roth_three_ap_via_removal`, `corners_theorem_via_removal`.

### 21. [`RHDirect/Arith4Ext_TopologicalComb.lean`](../RHDirect/Arith4Ext_TopologicalComb.lean) (`3,022` L)
- **Namespace:** `Arith4Ext.TopologicalComb`
- **API Highlights:**
  1. **Simplicial & Fixed-Point Theorems:** `sperner_lemma`, `sperner_lemma_exists`, `brouwer_fixed_point_simplex`.
  2. **Ky Fan, Tucker & Discrete Borsuk–Ulam:** `ky_fan_lemma`, `tucker_lemma_combinatorial`, `tucker_lemma_linf`, `discrete_borsuk_ulam`.
  3. **Lovász's Kneser Graph Chromatic Number:** `kneser_coloring_exists`, `kneser_no_coloring_lt`, `kneser_chromatic_number` (`χ(KG(n, k)) = n - 2k + 2`).

### 22. [`RHDirect/Arith4Ext_ZetaLFunctions.lean`](../RHDirect/Arith4Ext_ZetaLFunctions.lean) (`1,810` L)
- **Namespace:** `Arith4Ext.ZetaLFunctions`
- **API Highlights:**
  1. **Dirichlet Series & Euler Products:** `lseries_summable_of_bounded`, `lseries_convolution_mul`, `lseries_zeta_eq_riemannZeta`, `riemannZeta_eulerProduct_tprod_eq`, `dirichletLFunction_eulerProduct_tprod_eq`, `inv_riemannZeta_eq_lseries_moebius`, `neg_deriv_riemannZeta_div_eq_lseries_vonMangoldt`, `neg_deriv_dirichletLFunction_div_eq_lseries_vonMangoldt`.
  2. **Mertens `Re s = 1` Non-Vanishing:** `mertens_zeta_inequality`, `mertens_dirichletLFunction_inequality`, `riemannZeta_ne_zero_on_re_one`, `dirichletLFunction_one_ne_zero`, `dirichletLFunction_ne_zero_of_one_le_re`.
  3. **Complex Analysis & Effective Perron:** `hadamard_three_circles`, `jensen_blaschke_product_bound`, `jensen_zero_count_bound`, `perron_vertical_integral_one`, `perron_vertical_integral_bound`, `perron_truncated_formula`, `perron_truncated_formula_half_int`.
