import Lean

/-!
# Exhaustive Lean 4 Metaprogramming Kernel Auditor (`audit_oleans_meta.lean`)

Runs via `lean --run scripts/audit_oleans_meta.lean <module1> <module2> ...` directly against
compiled `.olean`s on `LEAN_PATH`.

Performs all three release-gate kernel checks in a single loaded `Environment`:
1. **Gate 1 (Exhaustive Kernel Axiom Audit)**:
   - Walks EVERY declaration in EVERY `RHDirect.*` module loaded in the environment (memoized
     transitive constant-dependency axiom collector) AND verifies key witness & Stage 11
     declarations directly via `Lean.CollectAxioms.collect`.
   - Asserts strictly `axioms ⊆ {propext, Classical.choice, Quot.sound}` and counts
     `Lean.ofReduceBool`, `Lean.trustCompiler`, `sorryAx`, and custom axioms.
2. **Gate 2 (Elaborated-Type & Genuine Mathlib Dependency Inspector)**:
   - For Stage 7–11 headline theorems and all loaded `RHDirect.Stage11*` modules, extracts
     kernel-elaborated type expressions, checks transitive Mathlib constant dependencies
     (`riemannZeta`, `DirichletCharacter`, `LSeries`, `ArithmeticFunction.vonMangoldt`,
     `UpperHalfPlane`, `Padic`, `PadicInt`, `ModularForm`, `CuspForm`, etc.) and `RHDirect`
     contract links (`Stage3UnifiedInputs`, `Stage3ThetaSiegelFiberWitness`,
     `UnifiedPatchingWindowSupply`, `Stage2GaloisCoreInputs`, `Stage2IwasawaTwoTower`,
     `Stage2RamifiedPrimes`, `BostSlopeFiber`, `WinDatum`, `VWin`, `SelmerSystem`,
     `MinimalLocalLanglands`, `RiemannHypothesis`).
3. **Gate 3 (Kernel Expression DAG Node & Term-Weight Metrics)**:
   - Counts declarations, theorem declarations, and total expression DAG nodes across every
     `RHDirect.*` module's `ConstantInfo` (`type` + `value`) for exact `bytes/LoC` and
     `nodes/LoC` outlier reporting.
-/

open Lean

structure AxiomCache where
  axioms : Std.HashMap Name (Array Name) := {}

/-- Official Lean 4.33.1 `Lean.collectAxioms` evaluated directly against an `Environment`. -/
def collectAxiomsOfficial (env : Environment) (nm : Name) : Array Name :=
  letI : MonadEnv (ReaderM Environment) :=
    { getEnv := read, modifyEnv := fun _ => pure () }
  (Lean.collectAxioms (m := ReaderM Environment) nm).run env

/-- Memoized transitive axiom collector matching `Lean.collectAxioms` semantics across 100k+ decls. -/
partial def collectAxiomsMemo (env : Environment) (nm : Name)
    (cache : Std.HashMap Name (Array Name)) :
    Array Name × Std.HashMap Name (Array Name) :=
  match cache[nm]? with
  | some axs => (axs, cache)
  | none =>
    match env.find? nm with
    | none => (#[], cache.insert nm #[])
    | some ci =>
      match ci with
      | .axiomInfo _ =>
        let res := #[nm]
        (res, cache.insert nm res)
      | _ =>
        let deps : NameSet := Id.run do
          let mut d : NameSet := {}
          d := ci.type.foldConsts d (fun c s => s.insert c)
          match ci.value? (allowOpaque := true) with
          | some v => d := v.foldConsts d (fun c s => s.insert c)
          | none => pure ()
          match ci with
          | .recInfo ri =>
            for r in ri.rules do
              d := r.rhs.foldConsts d (fun c s => s.insert c)
          | _ => pure ()
          return d
        let cache0 := cache.insert nm #[] -- guard cycles
        let (acc, cache1) := deps.foldl (init := (({} : NameSet), cache0)) fun (s, c) dep =>
          let (dAxs, c') := collectAxiomsMemo env dep c
          let s' := dAxs.foldl (init := s) fun acc a => acc.insert a
          (s', c')
        let res := acc.toArray
        (res, cache1.insert nm res)

/-- Count expression tree nodes with pointer/struct-equality DAG memoization per expression. -/
partial def countExprNodes (e : Expr) : Nat :=
  let rec go (e : Expr) (seen : Std.HashSet Expr) : Nat × Std.HashSet Expr :=
    if seen.contains e then (0, seen)
    else
      let seen := seen.insert e
      match e with
      | .app f a =>
        let (nf, s1) := go f seen
        let (na, s2) := go a s1
        (1 + nf + na, s2)
      | .lam _ t b _ =>
        let (nt, s1) := go t seen
        let (nb, s2) := go b s1
        (1 + nt + nb, s2)
      | .forallE _ t b _ =>
        let (nt, s1) := go t seen
        let (nb, s2) := go b s1
        (1 + nt + nb, s2)
      | .letE _ t v b _ =>
        let (nt, s1) := go t seen
        let (nv, s2) := go v s1
        let (nb, s3) := go b s2
        (1 + nt + nv + nb, s3)
      | .mdata _ b =>
        let (nb, s1) := go b seen
        (1 + nb, s1)
      | .proj _ _ b =>
        let (nb, s1) := go b seen
        (1 + nb, s1)
      | _ => (1, seen)
  (go e {}).1

def allowedAxioms : Std.HashSet Name :=
  Std.HashSet.ofList [`propext, `Classical.choice, `Quot.sound]

def mathlibAnchors : Array (String × Name) := #[
  ("RiemannHypothesis", `RiemannHypothesis),
  ("riemannZeta", `riemannZeta),
  ("DirichletCharacter", `DirichletCharacter),
  ("DirichletCharacter.LFunction", `DirichletCharacter.LFunction),
  ("LSeries", `LSeries),
  ("vonMangoldt", `ArithmeticFunction.vonMangoldt),
  ("UpperHalfPlane", `UpperHalfPlane),
  ("Padic", `Padic),
  ("PadicInt", `PadicInt),
  ("ModularForm", `ModularForm),
  ("CuspForm", `CuspForm),
  ("Chebyshev.psi", `Chebyshev.psi),
  ("ZLattice.covolume", `ZLattice.covolume),
  ("NumberField.discr", `NumberField.discr),
  ("Nat.primeCounting", `Nat.primeCounting),
  ("bernoulli", `bernoulli),
  ("padicValNat", `padicValNat)
]

def contractAnchors : Array (String × Name) := #[
  ("Stage3UnifiedInputs", `RHDirect.Stage3UnifiedInputs),
  ("Stage3ThetaSiegelFiberWitness", `RHDirect.Stage3ThetaSiegelBridge.Stage3ThetaSiegelFiberWitness),
  ("Stage3ThetaSiegelCoreInputs", `RHDirect.Stage3ThetaSiegelBridge.Stage3ThetaSiegelCoreInputs),
  ("UnifiedPatchingWindowSupply", `RHDirect.Stage3PatchingUnification.UnifiedPatchingWindowSupply),
  ("Stage2GaloisCoreInputs", `RHDirect.Stage2GaloisWire.Stage2GaloisCoreInputs),
  ("Stage2ThetaCoreInputs", `RHDirect.Stage2ThetaWire.Stage2ThetaCoreInputs),
  ("Stage2IwasawaTwoTower", `RHDirect.Stage2IwasawaTwoTower.IwasawaTwoTowerBound),
  ("Stage2RamifiedPrimes", `RHDirect.Stage2RamifiedPrimes.RamifiedPrimeRealization),
  ("LinnikAPInterval", `RHDirect.Stage2PrimePairs.LinnikAPInterval),
  ("BostSlopeFiber", `RHDirect.SlopeInequality.BostSlopeFiber),
  ("WinDatum", `RHDirect.ThetaSlopeEngine.WinDatum),
  ("VWin", `RHDirect.VWin),
  ("SelmerSystem", `RHDirect.SelmerSystem),
  ("MinimalLocalLanglands", `RHDirect.MinimalLocalLanglands),
  ("TaylorWilesCongruenceDatum", `RHDirect.Stage3PatchingUnification.TaylorWilesCongruenceDatum),
  ("GaloisModularityContract", `RHDirect.GaloisModularityContract),
  ("ThetaSlopeContract", `RHDirect.ThetaSlopeContract),
  ("AllLevelsWindowBound", `RHDirect.AllLevelsWindowBound)
]

def hasSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

def isUserDecl (nm : Name) : Bool :=
  let s := nm.toString
  !nm.isInternal && !nm.isInternalDetail &&
  !hasSubstr s "._proof_" &&
  !hasSubstr s "._match_" &&
  !hasSubstr s "._cstage" &&
  !hasSubstr s ".match_" &&
  !hasSubstr s ".eq_" &&
  !hasSubstr s ".rec" &&
  !hasSubstr s ".casesOn" &&
  !hasSubstr s ".noConfusion" &&
  !hasSubstr s ".below" &&
  !hasSubstr s ".brecOn" &&
  !hasSubstr s ".sizeOf_spec" &&
  !hasSubstr s ".injEq" &&
  !hasSubstr s ".ctorIdx"

def collectTransitiveDepsBounded (env : Environment) (roots : Array Name) (maxSteps : Nat := 12000) :
    Std.HashSet Name := Id.run do
  let mut visited : Std.HashSet Name := {}
  let mut queue : Array Name := roots
  let mut idx : Nat := 0
  while idx < queue.size && visited.size < maxSteps do
    let nm := queue[idx]!
    idx := idx + 1
    if !visited.contains nm then
      visited := visited.insert nm
      if let some ci := env.find? nm then
        let mut nexts : NameSet := {}
        nexts := ci.type.foldConsts nexts (fun c s => s.insert c)
        if let some v := ci.value? (allowOpaque := true) then
          nexts := v.foldConsts nexts (fun c s => s.insert c)
        for dep in nexts do
          if !visited.contains dep then
            queue := queue.push dep
  return visited

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  if args.isEmpty then
    IO.eprintln "Usage: lean --run scripts/audit_oleans_meta.lean <Module1> [Module2 ...]"
    return 1
  let imports : Array Import := args.toArray.map fun m => { module := m.toName }
  let env ← importModules imports {} (trustLevel := 0)

  -- Collect all RHDirect.* module indices
  let mut rhMods : Array (Nat × Name) := #[]
  for i in [:env.header.moduleNames.size] do
    let mn := env.header.moduleNames[i]!
    if mn.toString.startsWith "RHDirect" then
      rhMods := rhMods.push (i, mn)
  rhMods := rhMods.qsort (fun a b => a.2.toString < b.2.toString)

  IO.println s!"AUDIT_META_LOADED_MODULES={rhMods.size}"

  -- GATE 1: Exhaustive kernel axiom audit across EVERY declaration in EVERY RHDirect.* module
  let mut cache : Std.HashMap Name (Array Name) := {}
  let mut totalDecls : Nat := 0
  let mut totalUserDecls : Nat := 0
  let mut totalTheorems : Nat := 0
  let mut cntOfReduceBool : Nat := 0
  let mut cntTrustCompiler : Nat := 0
  let mut cntSorryAx : Nat := 0
  let mut cntCustomAxiom : Nat := 0
  let mut violations : Array String := #[]
  let mut modStats : Array (Name × Nat × Nat × Nat × Nat × Nat) := #[]

  for (modIdx, modName) in rhMods do
    let mdata := env.header.moduleData[modIdx]!
    let mut mDecls : Nat := 0
    let mut mUserDecls : Nat := 0
    let mut mTheorems : Nat := 0
    let mut mTypeNodes : Nat := 0
    let mut mValNodes : Nat := 0
    for nm in mdata.constNames do
      mDecls := mDecls + 1
      totalDecls := totalDecls + 1
      if isUserDecl nm then
        mUserDecls := mUserDecls + 1
        totalUserDecls := totalUserDecls + 1
      if let some ci := env.find? nm then
        if let .thmInfo _ := ci then
          mTheorems := mTheorems + 1
          totalTheorems := totalTheorems + 1
        mTypeNodes := mTypeNodes + countExprNodes ci.type
        if let some v := ci.value? (allowOpaque := true) then
          mValNodes := mValNodes + countExprNodes v
      let (axs, cache') := collectAxiomsMemo env nm cache
      cache := cache'
      for ax in axs do
        if !allowedAxioms.contains ax then
          if ax == `Lean.ofReduceBool then cntOfReduceBool := cntOfReduceBool + 1
          else if ax == `Lean.trustCompiler then cntTrustCompiler := cntTrustCompiler + 1
          else if ax == `sorryAx then cntSorryAx := cntSorryAx + 1
          else cntCustomAxiom := cntCustomAxiom + 1
          if violations.size < 50 then
            violations := violations.push s!"{modName}::{nm} -> {ax}"
    modStats := modStats.push (modName, mDecls, mUserDecls, mTheorems, mTypeNodes, mValNodes)

  -- Spot-verify key witnesses & ALL declarations of Stage11LocalLanglandsGL2 using official Lean.CollectAxioms.collect
  let officialSpotTargets : Array Name := #[
    `RHDirect.riemannHypothesis,
    `RHDirect.riemannHypothesis_of_stage2,
    `RHDirect.riemannHypothesis_of_stage3,
    `RHDirect.Stage8IwasawaWeierstrass.irregular_prime_37_bernoulli32,
    `RHDirect.Stage11FerreroWashington.irregular_prime_37_mu_zero_lambda_eq_one,
    `RHDirect.Stage11FerreroWashington.irregular_prime_37_layerQuot_exact_growth,
    `RHDirect.Stage11StickelbergerRamified.analyticHMinus_twentythree,
    `RHDirect.Stage11LocalLanglandsGL2.llcGL2,
    `RHDirect.Stage11LocalLanglandsGL2.minimalLocalLanglands_gl2_primes,
    `RHDirect.Stage11LocalLanglandsGL2.delta12_LSeries_eq_tprod_llcGL2
  ]
  let mut spotChecked : Nat := 0
  let mut spotViolations : Nat := 0
  for nm in officialSpotTargets do
    if env.find? nm |>.isSome then
      spotChecked := spotChecked + 1
      let axs := collectAxiomsOfficial env nm
      for ax in axs do
        if !allowedAxioms.contains ax then
          spotViolations := spotViolations + 1
          violations := violations.push s!"OFFICIAL_COLLECT::{nm} -> {ax}"
  -- Also run official Lean.collectAxioms on EVERY declaration in Stage11LocalLanglandsGL2
  let mut llcOfficialCount : Nat := 0
  if let some idx := env.getModuleIdx? `RHDirect.Stage11LocalLanglandsGL2 then
    let mdata := env.header.moduleData[idx.toNat]!
    for nm in mdata.constNames do
      llcOfficialCount := llcOfficialCount + 1
      let axs := collectAxiomsOfficial env nm
      for ax in axs do
        if !allowedAxioms.contains ax then
          spotViolations := spotViolations + 1
          violations := violations.push s!"OFFICIAL_LLC::{nm} -> {ax}"

  IO.println "=== GATE1_AXIOM_SUMMARY ==="
  IO.println s!"TOTAL_MODULES={rhMods.size}"
  IO.println s!"TOTAL_CONSTANTS={totalDecls}"
  IO.println s!"TOTAL_USER_DECLS={totalUserDecls}"
  IO.println s!"TOTAL_THEOREMS={totalTheorems}"
  IO.println s!"OFFICIAL_SPOT_CHECKED={spotChecked}"
  IO.println s!"OFFICIAL_LLC_GL2_CONSTANTS={llcOfficialCount}"
  IO.println s!"BANNED_ofReduceBool={cntOfReduceBool}"
  IO.println s!"BANNED_trustCompiler={cntTrustCompiler}"
  IO.println s!"BANNED_sorryAx={cntSorryAx}"
  IO.println s!"BANNED_customAxiom={cntCustomAxiom}"
  IO.println s!"TOTAL_VIOLATIONS={violations.size}"
  for v in violations do
    IO.println s!"VIOLATION: {v}"

  -- GATE 2: Elaborated-Type & Mathlib / Contract Dependency Audit
  IO.println "=== GATE2_STAGE11_GROUNDING ==="
  for (modIdx, modName) in rhMods do
    if modName.toString.startsWith "RHDirect.Stage11" then
      let mdata := env.header.moduleData[modIdx]!
      let userConsts := mdata.constNames.filter isUserDecl
      -- Collect direct constants referenced in types & values of this module
      let mut directConsts : Std.HashSet Name := {}
      for nm in userConsts do
        if let some ci := env.find? nm then
          directConsts := ci.type.foldConsts directConsts (fun c s => s.insert c)
          if let some v := ci.value? (allowOpaque := true) then
            directConsts := v.foldConsts directConsts (fun c s => s.insert c)
      -- Also collect transitive closure up to 8000 steps from all user constants
      let transConsts := collectTransitiveDepsBounded env userConsts 8000
      let mut mathlibHits : Array String := #[]
      for (lbl, cname) in mathlibAnchors do
        if directConsts.contains cname then
          mathlibHits := mathlibHits.push (lbl ++ "*")
        else if transConsts.contains cname then
          mathlibHits := mathlibHits.push lbl
      let mut contractHits : Array String := #[]
      for (lbl, cname) in contractAnchors do
        if directConsts.contains cname then
          contractHits := contractHits.push (lbl ++ "*")
        else if transConsts.contains cname then
          contractHits := contractHits.push lbl
      let mStr := String.intercalate "," mathlibHits.toList
      let cStr := String.intercalate "," contractHits.toList
      IO.println s!"S11_GROUND|{modName}|{mdata.constNames.size}|{userConsts.size}|MATHLIB:[{mStr}]|CONTRACTS:[{cStr}]"

  -- GATE 2b: Kernel-Elaborated Types of Headline Theorems across Stages 7-11
  IO.println "=== GATE2_HEADLINE_TYPES ==="
  let headlineDecls : Array Name := #[
    `RHDirect.riemannHypothesis_of_stage3,
    `RHDirect.LFunction_eq_zero_re_of_stage3,
    `RHDirect.main_stage7_pnt_primeCountAP_asymp,
    `RHDirect.main_stage7_kubotaLeopoldtZeta_eval_nat,
    `RHDirect.main_stage7_riemannHypothesis_iff_psi_and_theta_sqrt_eps,
    `RHDirect.Stage8IwasawaWeierstrass.irregular_prime_37_bernoulli32,
    `RHDirect.main_stage9_gauss_classNumber_problem_unconditional,
    `RHDirect.main_stage9_delta_eq_euler_product_24,
    `RHDirect.main_stage10_siegel_walfisz_pi,
    `RHDirect.main_stage10_liCriterion_unconditional,
    `RHDirect.main_stage10_minkowski_second_theorem_upper,
    `RHDirect.main_stage10_S24_eigenPlus_LSeries_eulerProduct,
    `RHDirect.Stage11LocalLanglandsGL2.llcGL2,
    `RHDirect.Stage11LocalLanglandsGL2.delta12_LSeries_eq_tprod_llcGL2,
    `RHDirect.Stage11LocalLanglandsGL2.minimalLocalLanglands_gl2_primes,
    `RHDirect.Stage11BostDworkSqueeze.stage11_thetaSlopeContract,
    `RHDirect.Stage11RallisMassFiber.stage11_rallis_mass_and_gram_frame_discharge,
    `RHDirect.Stage11StickelbergerRamified.analyticHMinus_twentythree,
    `RHDirect.Stage11StickelbergerRamified.discharges_unified_ramified_branch_of_stickelberger,
    `RHDirect.Stage11FerreroWashington.irregular_prime_37_mu_zero_lambda_eq_one,
    `RHDirect.Stage11FerreroWashington.irregular_prime_37_layerQuot_exact_growth,
    `RHDirect.Stage11ConcretePatching.S24_congruencePatchingRealization,
    `RHDirect.Stage11EulerSystemSelmer.galoisModularityContract_of_eulerSystemSupply,
    `RHDirect.Stage11GaloisModularityBridge.stage11_galoisModularityContract,
    `RHDirect.Stage11MoriwakiCovolume.stage3_fiber_covolume_and_small_sections,
    `RHDirect.Stage11DefiniteUnitaryChain.chain_hermitian_minkowski_bost_bridge,
    `RHDirect.Stage11Sym2AdjointL.S24_petersson_congruence_denominator,
    `RHDirect.Stage11Sym2AdjointL.delta12_sym2L_master,
    `RHDirect.Stage11DoublingRallis.E8_global_doubling_euler_product,
    `RHDirect.Stage11IharaLevelRaising.stage11_ihara_level_raising_master,
    `RHDirect.Stage11HermitianCurvature.modularForm_eq_zero_of_weight_neg,
    `RHDirect.Stage11BaseChangeTrace.concrete_solvablePrimeStepBaseChange_unconditional,
    `RHDirect.Stage11BesselWaveSchur.stage11_besselWaveSchur_master_bundle,
    `RHDirect.Stage11SecondMomentFrame.twisted_box_zero_free_and_mean_square_transfer,
    `RHDirect.Stage11LinnikBridge.linnikAPInterval_of_dh_and_logfree
  ]
  for nm in headlineDecls do
    if let some ci := env.find? nm then
      let (axs, _) := collectAxiomsMemo env nm cache
      let typeConsts := ci.type.foldConsts ({} : NameSet) (fun c s => s.insert c)
      let mut mHits : Array String := #[]
      for (lbl, cname) in mathlibAnchors do
        if typeConsts.contains cname then mHits := mHits.push lbl
      let mut cHits : Array String := #[]
      for (lbl, cname) in contractAnchors do
        if typeConsts.contains cname then cHits := cHits.push lbl
      let axStr := String.intercalate "," (axs.toList.map Name.toString)
      let tNodes := countExprNodes ci.type
      let vNodes := match ci.value? (allowOpaque := true) with | some v => countExprNodes v | none => 0
      IO.println s!"HEADLINE|{nm}|AXIOMS:[{axStr}]|TYPE_NODES={tNodes}|VAL_NODES={vNodes}|TYPE_MATHLIB:[{String.intercalate "," mHits.toList}]|TYPE_CONTRACTS:[{String.intercalate "," cHits.toList}]"
    else
      IO.println s!"HEADLINE|{nm}|MISSING"

  -- GATE 3: Per-module declaration & DAG node table
  IO.println "=== GATE3_MODULE_DAG_STATS ==="
  for (modName, mDecls, mUserDecls, mTheorems, mTypeNodes, mValNodes) in modStats do
    IO.println s!"MOD_DAG|{modName}|{mDecls}|{mUserDecls}|{mTheorems}|{mTypeNodes}|{mValNodes}"

  return if violations.isEmpty && spotViolations == 0 then 0 else 2
