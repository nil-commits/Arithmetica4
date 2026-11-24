import Lean
import Lean.Util.CollectAxioms

/-!
Trustless verification helper: loads the compiled environments of `Challenge` and `Solution`
separately and verifies that:
1. `Challenge` imports ONLY upstream Mathlib / Lean / Init / Batteries / Std modules
   (zero `RHDirect`, `PrimeGaps`, `MaynardDock`, or `Solution` imports).
2. Every target theorem exists in both environments as a `thmInfo`.
3. Its universe parameters and type `Expr` in `Solution` are syntactically identical to those
   in `Challenge`.
4. Its transitive axiom dependencies in `Solution` are strictly a subset of
   `{propext, Classical.choice, Quot.sound}` (rejecting `sorryAx`, `Lean.ofReduceBool`,
   `Lean.trustCompiler`, and any custom axiom).
-/

open Lean

def targetTheorems : List Name :=
  [ `vinogradov_three_primes
  , `chen_theorem
  , `linnik_theorem
  , `unconditional_prime_gap_le_246
  , `bounded_prime_gaps_246_unconditional
  , `frequently_consecutive_prime_gap_le_246
  , `maynard_tao_m_tuples
  , `dwork_rationality
  , `gauss_class_number_problem
  , `hasse_minkowski_general
  , `hilbert_class_field_artin
  , `siegel_l1_lower_bound
  , `bochner_negative_weight_vanishing
  ]

def permittedAxioms : List Name :=
  [ `propext
  , `Classical.choice
  , `Quot.sound
  ]

def allowedChallengePrefixes : List String :=
  [ "Init", "Lean", "Std", "Batteries", "Qq", "Aesop", "ProofWidgets",
    "ImportGraph", "LeanSearchClient", "Plausible", "Cli", "Mathlib", "Challenge" ]

def isAllowedChallengeImport (modName : Name) : Bool :=
  let s := modName.toString
  allowedChallengePrefixes.any fun p => s == p || s.startsWith (p ++ ".")

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let envC ← importModules #[{ module := `Challenge }] {} (trustLevel := 0)
  for modData in envC.header.moduleData do
    for imp in modData.imports do
      if !isAllowedChallengeImport imp.module then
        throw <| IO.userError s!"Disallowed import in Challenge transitive closure: {imp.module}"
  IO.println "OK Challenge import isolation: 0 project/custom imports (pure Mathlib only)"

  let envS ← importModules #[{ module := `Solution }] {} (trustLevel := 0)
  for name in targetTheorems do
    let some infoC := envC.find? name
      | throw <| IO.userError s!"Challenge missing theorem: {name}"
    let some infoS := envS.find? name
      | throw <| IO.userError s!"Solution missing theorem: {name}"
    match infoC, infoS with
    | .thmInfo tC, .thmInfo tS =>
      if tC.levelParams != tS.levelParams then
        throw <| IO.userError s!"Level params mismatch for {name}: {tC.levelParams} vs {tS.levelParams}"
      if tC.type != tS.type then
        throw <| IO.userError s!"Type mismatch for {name}!"
      let (axioms, _) ← Core.CoreM.toIO (Lean.collectAxioms name)
        { fileName := "<verify_challenge>", fileMap := default }
        { env := envS }
      let bad := axioms.toList.filter (fun ax => !permittedAxioms.contains ax)
      if !bad.isEmpty then
        throw <| IO.userError s!"Disallowed axioms for {name}: {bad}"
      IO.println s!"OK {name}: exact type match, axioms = {axioms.toList}"
    | _, _ =>
      throw <| IO.userError s!"Expected theorem info for {name}"
  IO.println s!"ALL {targetTheorems.length} CHALLENGE THEOREMS VERIFIED."
