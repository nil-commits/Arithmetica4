import Lean
import MathlibRHSpec
import RHDirect.Main

/-!
# Isolated Mathlib-Only RH / GRH Comparator (`comparator` / `con-leche --compare` style)

Verifies two independent guarantees in the Lean 4 kernel:
1. **Kernel Definitional Equality (`rfl`)**: Every one of the 5 headline target propositions in
   `RHDirect.Interfaces` / `RHDirect.Main` is definitionally identical (`rfl`) to the
   isolated pure-Mathlib statement in `MathlibRHSpec` (which imports ZERO `RHDirect` modules),
   and every Stage 1 / Stage 2 / Stage 3 headline theorem in `RHDirect.Main` directly inhabits
   the corresponding `MathlibRHSpec` proposition.
2. **Metaprogramming `isDefEq` + Import Isolation + Axiom Audit**: Confirms that
   `MathlibRHSpec`'s import graph has zero `RHDirect.*` modules, that `Meta.isDefEq` holds for
   all 5 pairs, and that all Stage 1 / Stage 2 / Stage 3 headline theorems depend strictly on
   `{propext, Classical.choice, Quot.sound}` (zero `ofReduceBool`, `trustCompiler`, `sorryAx`,
   or custom axioms).
-/

namespace MathlibRHCompare

open MathlibRHSpec RHDirect

/-! ## 1. Kernel `rfl` Definitional Equality Against Pure-Mathlib Spec -/

theorem defeq_riemannHypothesis :
    RiemannHypothesis = SpecRiemannHypothesis := rfl

theorem defeq_riemannZetaZerosOnLine :
    RiemannZetaZerosOnLine = SpecRiemannZetaZerosOnLine := rfl

theorem defeq_dirichletLNonvanishingRightOfHalf :
    DirichletLNonvanishingRightOfHalf = SpecDirichletLNonvanishingRightOfHalf := rfl

theorem defeq_dirichletLZerosOnLine :
    DirichletLZerosOnLine = SpecDirichletLZerosOnLine := rfl

theorem defeq_primitiveDirichletLZerosOnLine :
    PrimitiveDirichletLZerosOnLine = SpecPrimitiveDirichletLZerosOnLine := rfl

/-! ## 2. Direct Type-Compatibility of `RHDirect.Main` Stage 1 / 2 / 3 Headline Theorems -/

theorem stage1_rh_matches_spec {S : SelmerSystem} {D_aut : AutomorphicDomain}
    (I : RHDirectMinimalInputs S D_aut) : SpecRiemannHypothesis :=
  RHDirect.riemannHypothesis I

theorem stage1_zeta_matches_spec {S : SelmerSystem} {D_aut : AutomorphicDomain}
    (I : RHDirectMinimalInputs S D_aut) : SpecRiemannZetaZerosOnLine :=
  RHDirect.riemannZeta_eq_zero_re I

theorem stage1_dirichlet_right_matches_spec {S : SelmerSystem} {D_aut : AutomorphicDomain}
    (I : RHDirectMinimalInputs S D_aut) : SpecDirichletLNonvanishingRightOfHalf :=
  RHDirect.LFunction_ne_zero_of_half_lt_re I

theorem stage1_dirichlet_line_matches_spec {S : SelmerSystem} {D_aut : AutomorphicDomain}
    (I : RHDirectMinimalInputs S D_aut) : SpecDirichletLZerosOnLine :=
  RHDirect.LFunction_eq_zero_re I

theorem stage1_prim_line_matches_spec {S : SelmerSystem} {D_aut : AutomorphicDomain}
    (I : RHDirectMinimalInputs S D_aut) : SpecPrimitiveDirichletLZerosOnLine :=
  RHDirect.LFunction_eq_zero_re_of_isPrimitive I

theorem stage2_rh_matches_spec {S : SelmerSystem} (I : Stage2DischargedInputs S) :
    SpecRiemannHypothesis :=
  RHDirect.riemannHypothesis_of_stage2 I

theorem stage2_zeta_matches_spec {S : SelmerSystem} (I : Stage2DischargedInputs S) :
    SpecRiemannZetaZerosOnLine :=
  RHDirect.riemannZeta_eq_zero_re_of_stage2 I

theorem stage2_dirichlet_right_matches_spec {S : SelmerSystem} (I : Stage2DischargedInputs S) :
    SpecDirichletLNonvanishingRightOfHalf :=
  RHDirect.LFunction_ne_zero_of_half_lt_re_of_stage2 I

theorem stage2_dirichlet_line_matches_spec {S : SelmerSystem} (I : Stage2DischargedInputs S) :
    SpecDirichletLZerosOnLine :=
  RHDirect.LFunction_eq_zero_re_of_stage2 I

theorem stage2_prim_line_matches_spec {S : SelmerSystem} (I : Stage2DischargedInputs S) :
    SpecPrimitiveDirichletLZerosOnLine :=
  RHDirect.LFunction_eq_zero_re_of_isPrimitive_of_stage2 I

theorem stage3_rh_matches_spec {S : SelmerSystem} (I : Stage3UnifiedInputs S) :
    SpecRiemannHypothesis :=
  RHDirect.riemannHypothesis_of_stage3 I

theorem stage3_zeta_matches_spec {S : SelmerSystem} (I : Stage3UnifiedInputs S) :
    SpecRiemannZetaZerosOnLine :=
  RHDirect.riemannZeta_eq_zero_re_of_stage3 I

theorem stage3_dirichlet_right_matches_spec {S : SelmerSystem} (I : Stage3UnifiedInputs S) :
    SpecDirichletLNonvanishingRightOfHalf :=
  RHDirect.LFunction_ne_zero_of_half_lt_re_of_stage3 I

theorem stage3_dirichlet_line_matches_spec {S : SelmerSystem} (I : Stage3UnifiedInputs S) :
    SpecDirichletLZerosOnLine :=
  RHDirect.LFunction_eq_zero_re_of_stage3 I

theorem stage3_prim_line_matches_spec {S : SelmerSystem} (I : Stage3UnifiedInputs S) :
    SpecPrimitiveDirichletLZerosOnLine :=
  RHDirect.LFunction_eq_zero_re_of_isPrimitive_of_stage3 I

/-! ## 3. Unconditional Equivalence Pack Match Against Pure-Mathlib Spec -/

theorem unconditional_rh_pack_matches_spec :
    (SpecRiemannHypothesis ↔ SpecRiemannZetaZerosOnLine) ∧
    (SpecDirichletLNonvanishingRightOfHalf ↔ SpecDirichletLZerosOnLine) ∧
    (SpecDirichletLZerosOnLine ↔ SpecPrimitiveDirichletLZerosOnLine) :=
  ⟨RHDirect.main_rh_equivalence_pack.1,
   RHDirect.main_grh_equivalence_pack.2.1,
   RHDirect.main_grh_equivalence_pack.2.2.1⟩

/-! ## 4. Executable `MetaM` Verification (`isDefEq`, Import Isolation & Strict Axiom Gate) -/

open Lean Meta in
def runCompareChecks : MetaM Unit := do
  let env ← getEnv
  -- 4a. Check MathlibRHSpec has ZERO RHDirect imports
  let specModIdx? := env.getModuleIdx? `MathlibRHSpec
  match specModIdx? with
  | none => throwError "MathlibRHSpec module not found in environment"
  | some idx =>
    let modData := env.header.moduleData[idx.toNat]!
    for imp in modData.imports do
      if imp.module.toString.startsWith "RHDirect" then
        throwError s!"ISOLATION VIOLATION: MathlibRHSpec imports {imp.module}"
  -- 4b. Check Meta.isDefEq on all 5 statement pairs
  let pairs : List (Name × Name) := [
    (`RiemannHypothesis, `MathlibRHSpec.SpecRiemannHypothesis),
    (`RiemannZetaZerosOnLine, `MathlibRHSpec.SpecRiemannZetaZerosOnLine),
    (`DirichletLNonvanishingRightOfHalf, `MathlibRHSpec.SpecDirichletLNonvanishingRightOfHalf),
    (`DirichletLZerosOnLine, `MathlibRHSpec.SpecDirichletLZerosOnLine),
    (`PrimitiveDirichletLZerosOnLine, `MathlibRHSpec.SpecPrimitiveDirichletLZerosOnLine)
  ]
  for (lhs, rhs) in pairs do
    let ok ← isDefEq (mkConst lhs) (mkConst rhs)
    if !ok then
      throwError s!"DEFEQ FAILURE: {lhs} != {rhs}"
  -- 4c. Check strict axioms on all 15 Stage 1/2/3 headline theorems + equivalence pack
  let allowed : Std.HashSet Name :=
    Std.HashSet.ofList [`propext, `Classical.choice, `Quot.sound]
  let targets : List Name := [
    `RHDirect.riemannHypothesis,
    `RHDirect.riemannZeta_eq_zero_re,
    `RHDirect.LFunction_ne_zero_of_half_lt_re,
    `RHDirect.LFunction_eq_zero_re,
    `RHDirect.LFunction_eq_zero_re_of_isPrimitive,
    `RHDirect.riemannHypothesis_of_stage2,
    `RHDirect.riemannZeta_eq_zero_re_of_stage2,
    `RHDirect.LFunction_ne_zero_of_half_lt_re_of_stage2,
    `RHDirect.LFunction_eq_zero_re_of_stage2,
    `RHDirect.LFunction_eq_zero_re_of_isPrimitive_of_stage2,
    `RHDirect.riemannHypothesis_of_stage3,
    `RHDirect.riemannZeta_eq_zero_re_of_stage3,
    `RHDirect.LFunction_ne_zero_of_half_lt_re_of_stage3,
    `RHDirect.LFunction_eq_zero_re_of_stage3,
    `RHDirect.LFunction_eq_zero_re_of_isPrimitive_of_stage3,
    `MathlibRHCompare.unconditional_rh_pack_matches_spec
  ]
  for nm in targets do
    let axs ← Lean.collectAxioms nm
    for ax in axs do
      if !allowed.contains ax then
        throwError s!"BANNED AXIOM in {nm}: {ax}"
  IO.println "[COMPARATOR] PASS: MathlibRHSpec has 0 RHDirect imports"
  IO.println "[COMPARATOR] PASS: 5/5 headline statements are kernel-defEq (`rfl` + `Meta.isDefEq`)"
  IO.println "[COMPARATOR] PASS: 16/16 Stage 1/2/3 headline theorems + pack strictly in {propext, Classical.choice, Quot.sound}"

run_meta runCompareChecks

end MathlibRHCompare
