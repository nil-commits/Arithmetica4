import RHDirect.DworkZetaW3j

/-! Axiom audit for the P3 campaign (W0 + W1).
Every declaration below must print exactly `[propext, Classical.choice, Quot.sound]`. -/

#print axioms RHDirect.HasseWeil.eq_of_derivative_eq_mul
#print axioms RHDirect.HasseWeil.expSeries_add
#print axioms RHDirect.HasseWeil.expSeries_neg
#print axioms RHDirect.HasseWeil.geom_mul_one_add_X
#print axioms RHDirect.HasseWeil.deriv_logOf
#print axioms RHDirect.HasseWeil.expSeries_logOf
#print axioms RHDirect.HasseWeil.expSeries_sum
#print axioms RHDirect.HasseWeil.zetaFinite_eq_prod_inv
#print axioms RHDirect.HasseWeil.zetaFinite_mul_prod_eq_one
-- W1
#print axioms RHDirect.HasseWeil.derivative_prod
#print axioms RHDirect.HasseWeil.expSeries_eq_inv_of_derivative
#print axioms RHDirect.HasseWeil.coeff_orbitTerm
#print axioms RHDirect.HasseWeil.fixedCount_eq_sum
#print axioms RHDirect.HasseWeil.derivative_zetaLog_eq_sum
#print axioms RHDirect.HasseWeil.zetaFinite_eq_prod_inv_fixed
#print axioms RHDirect.HasseWeil.zetaFinite_mul_prod_fixed_eq_one
-- W2
#print axioms RHDirect.HasseWeil.eval_map_apply
#print axioms RHDirect.HasseWeil.rootPerm_fixed_iff
#print axioms RHDirect.HasseWeil.rootPerm_pow_apply
#print axioms RHDirect.HasseWeil.fixedCount_rootPerm
#print axioms RHDirect.HasseWeil.zetaFinite_rootPerm_eq
#print axioms RHDirect.HasseWeil.zetaFinite_rootPerm_mul_eq_one
-- W3
#print axioms RHDirect.HasseWeil.natCard_fixedPoints
#print axioms RHDirect.HasseWeil.sumCongr_pow_apply_inl
#print axioms RHDirect.HasseWeil.fixedCount_sumCongr
#print axioms RHDirect.HasseWeil.zetaLog_sumCongr
#print axioms RHDirect.HasseWeil.zetaFinite_sumCongr
#print axioms RHDirect.HasseWeil.zetaFinite_sumCongr_three
-- W3a / W3b
#print axioms RHDirect.HasseWeil.frobenius_bijective
#print axioms RHDirect.HasseWeil.frobeniusAut_apply
#print axioms RHDirect.HasseWeil.frobeniusAut_pow_apply
#print axioms RHDirect.HasseWeil.frobeniusAut_algebraMap_zmod
#print axioms RHDirect.HasseWeil.map_frobeniusAut_map_algebraMap
#print axioms RHDirect.HasseWeil.frobeniusAut_pow_fixed_iff_isRoot
#print axioms RHDirect.HasseWeil.natCard_fixed_eq
-- W3b'
#print axioms RHDirect.HasseWeil.frobeniusAut_pow_card_eq_id
#print axioms RHDirect.HasseWeil.natCard_fixed_eq_pow_of_card
#print axioms RHDirect.HasseWeil.galoisField_frobeniusAut_pow
#print axioms RHDirect.HasseWeil.galoisField_natCard_fixed
-- Route B (W3b'-allgemein)
#print axioms RHDirect.HasseWeil.X_pow_sub_X_dvd_X_pow_pow_sub_X
#print axioms RHDirect.HasseWeil.separable_X_pow_pow_sub_X
#print axioms RHDirect.HasseWeil.splits_X_pow_pow_sub_X
#print axioms RHDirect.HasseWeil.natCard_roots_eq_pow
#print axioms RHDirect.HasseWeil.natCard_fixed_eq_pow_of_dvd
-- W3d
#print axioms RHDirect.HasseWeil.one_sub_mul_geomSeq
#print axioms RHDirect.HasseWeil.geomSeq_eq_inv
#print axioms RHDirect.HasseWeil.derivative_logSeries
#print axioms RHDirect.HasseWeil.logSeries_eq_neg_logOf
#print axioms RHDirect.HasseWeil.expSeries_logSeries
#print axioms RHDirect.HasseWeil.zetaSeq_add
#print axioms RHDirect.HasseWeil.zeta_affine_line
#print axioms RHDirect.HasseWeil.zeta_projective_line
#print axioms RHDirect.HasseWeil.zeta_mult_group
#print axioms RHDirect.HasseWeil.zeta_projective_line_den
#print axioms RHDirect.HasseWeil.zeta_mult_group_den
-- W3e
#print axioms RHDirect.HasseWeil.card_affineLine
#print axioms RHDirect.HasseWeil.card_multGroup
#print axioms RHDirect.HasseWeil.card_projLine
#print axioms RHDirect.HasseWeil.pointCount_projLine
#print axioms RHDirect.HasseWeil.pointCount_projLine_rat
#print axioms RHDirect.HasseWeil.zeta_of_projLine
-- W3f
#print axioms RHDirect.HasseWeil.zetaSeq_const_mul_pow
#print axioms RHDirect.HasseWeil.zetaSeq_sum
#print axioms RHDirect.HasseWeil.card_projSpace
#print axioms RHDirect.HasseWeil.pointCount_projSpace
#print axioms RHDirect.HasseWeil.zeta_projectiveSpace
#print axioms RHDirect.HasseWeil.zeta_projectiveSpace_den
-- W3g
#print axioms RHDirect.HasseWeil.card_fixSubfield
#print axioms RHDirect.HasseWeil.exists_subfield_card
#print axioms RHDirect.HasseWeil.fixSubfield_mono
-- W3h
#print axioms RHDirect.HasseWeil.projSpaceScheme
#print axioms RHDirect.HasseWeil.projLineScheme
-- W3i
#print axioms RHDirect.HasseWeil.galoisField_embed
#print axioms RHDirect.HasseWeil.galoisField_card_dvd_embed
-- W3j
#print axioms RHDirect.HasseWeil.geomSeq_inv
#print axioms RHDirect.HasseWeil.zetaSeq_lefschetz
#print axioms RHDirect.HasseWeil.zeta_elliptic_shape
#print axioms RHDirect.HasseWeil.zeta_elliptic_den
