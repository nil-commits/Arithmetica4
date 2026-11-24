/-
Axiom audit probe for the lattice-smoothing campaign (wave 1).
Compiled on the campaign VM; every `#print axioms` line must show only
`[propext, Classical.choice, Quot.sound]` (or a subset).
-/
import RHDirect.LatticeSmoothing

open RHDirect.LatticeSmoothing

#print axioms RHDirect.LatticeSmoothing.rhoPunct_le_of_sqrt_n_div_lt
#print axioms RHDirect.LatticeSmoothing.eta_le_sqrt_n_div_lambda1
#print axioms RHDirect.LatticeSmoothing.eta_le_of_rhoPunct_le
#print axioms RHDirect.LatticeSmoothing.rhoPunct_eq_rho_sub_one
#print axioms RHDirect.LatticeSmoothing.summable_rhoPunct
