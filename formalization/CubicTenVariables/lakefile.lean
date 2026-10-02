import Lake
open Lake DSL Lean
package CubicTenVariables where
  leanOptions := #[⟨`autoImplicit, false⟩]
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.26.0"
require HessianTheorem11 from "../HessianTheorem11"
require TranslatedDepthSeven from "../TranslatedDepthSeven"
@[default_target]
lean_lib CubicTenVariables where
  -- The checked public root and its transitive imports. New modules are
  -- added to the root only after their individual proof checks succeed.
  globs := #[.one `CubicTenVariables]

/- Plan the complete workspace import DAG, then request artifact jobs only
for ready modules whose dependencies have completed. A single FetchM store
retains normal Lake trace checks across every batch. -/

private structure BoundedBuildNode where
  mod : Lake.Module
  dependencies : Array Name

private partial def boundedBuildVisit
    (mod : Lake.Module) (active done : NameSet)
    (ordered : Array BoundedBuildNode) :
    FetchM (NameSet × Array BoundedBuildNode) := do
  if done.contains mod.name then
    return (done, ordered)
  if active.contains mod.name then
    error s!"Import cycle while planning bounded build: {mod.name}"
  let active := active.insert mod.name
  let mut done := done
  let mut ordered := ordered
  let mut dependencies : Array Name := #[]
  let mut seen : NameSet := {}
  for dep in (← (← mod.imports.fetch).await) do
    unless seen.contains dep.name do
      seen := seen.insert dep.name
      dependencies := dependencies.push dep.name
      let result ← boundedBuildVisit dep active done ordered
      done := result.1
      ordered := result.2
  return (done.insert mod.name, ordered.push ⟨mod, dependencies⟩)

script boundedCheck args do
  unless args.isEmpty do
    IO.eprintln "boundedCheck takes no arguments; it always checks all three public roots"
    return 1
  let configured ← IO.getEnv "CUBIC_BUILD_JOBS"
  let some maxJobs := (configured.getD "2").toNat?
    | IO.eprintln "CUBIC_BUILD_JOBS must be an integer from 1 to 3"
      return 1
  unless 1 ≤ maxJobs ∧ maxJobs ≤ 3 do
    IO.eprintln "CUBIC_BUILD_JOBS must be an integer from 1 to 3"
    return 1
  let ws ← getWorkspace
  ws.runFetchM (do
    let rootNames : Array Name :=
      #[`CubicTenVariables, `HessianTheorem11, `TranslatedDepthSeven]
    let mut done : NameSet := {}
    let mut ordered : Array BoundedBuildNode := #[]
    for name in rootNames do
      let some mod ← findModule? name
        | error s!"Missing public root module: {name}"
      let result ← boundedBuildVisit mod {} done ordered
      done := result.1
      ordered := result.2
    let mut modules : NameMap Lake.Module := {}
    let mut remaining : NameMap Nat := {}
    let mut children : NameMap (Array Name) := {}
    let mut ready : Array Name := #[]
    for node in ordered do
      modules := modules.insert node.mod.name node.mod
      remaining := remaining.insert node.mod.name node.dependencies.size
      if node.dependencies.isEmpty then
        ready := ready.push node.mod.name
      for dep in node.dependencies do
        children := children.insert dep
          ((children.find? dep).getD #[] |>.push node.mod.name)
    logInfo s!"Bounded build: {ordered.size} workspace modules; at most {maxJobs} independent module compilations at once."
    let mut checked := 0
    let mut front := 0
    let mut nextReport := 100
    while checked < ordered.size do
      if front == ready.size then
        error "Internal bounded-build error: no ready module remains"
      let stop := min (front + maxJobs) ready.size
      let mut batch : Array Name := #[]
      let mut jobs : Array OpaqueJob := #[]
      for i in [front:stop] do
        let some name := ready[i]?
          | error "Internal bounded-build ready-queue indexing error"
        let some mod := modules.find? name
          | error s!"Internal bounded-build missing module: {name}"
        batch := batch.push name
        jobs := jobs.push (← mod.leanArts.fetch).toOpaque
      discard <| (Job.mixArray jobs).await
      front := stop
      checked := checked + batch.size
      for name in batch do
        for child in (children.find? name).getD #[] do
          let some count := remaining.find? child
            | error s!"Internal bounded-build missing dependency count: {child}"
          if count == 0 then
            error s!"Internal bounded-build dependency count underflow: {child}"
          let count := count - 1
          remaining := remaining.insert child count
          if count == 0 then
            ready := ready.push child
      if checked ≥ nextReport || checked == ordered.size then
        logInfo s!"Bounded build: checked {checked}/{ordered.size} modules."
        nextReport := checked + 100
  ) {trustHash := false}
  return 0
