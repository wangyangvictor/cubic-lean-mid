import CubicTenVariables
import HessianTheorem11
import TranslatedDepthSeven
import Lean.Util.CollectAxioms

/-!
Run from `formalization/CubicTenVariables`, after building all three public roots:

    lake build CubicTenVariables HessianTheorem11 TranslatedDepthSeven
    lake env lean PublicationAudit.lean

This audit checks the actual imported declarations, including private declarations
and declarations outside project namespaces when their defining module belongs to
the project. It follows types and proof/definition bodies transitively, allowing
only Lean's `propext`, `Classical.choice`, and `Quot.sound` axioms. It also rejects
any custom axiom declared in a project module, even if no theorem uses it.

The five literature propositions below are explicit hypotheses, not Lean axioms.
Checking their axiom footprints does not prove those propositions or establish
that their mathematical definitions and literature references are correct.
This is an audit using Lean's own environment, not an independent kernel checker.
-/

set_option autoImplicit false

namespace PublicationAudit

/-- An exact type check against the literal Diophantine conclusion, including
the order and number of literature premises. No equivalence is asserted between
the premises and the conclusion. The zero polynomial is intentionally included. -/
example :
    CubicTenVariables.Literature.ProjectiveMicrolocalCertificate →
    CubicTenVariables.Literature.SmoothCubicWeil →
    CubicTenVariables.Literature.ProperHyperplaneWeightDichotomy →
    CubicTenVariables.Literature.AffinePlaneCurveWeil →
    CubicTenVariables.Literature.CubicSurfaceZetaFactorBounds →
    ∀ (n : ℕ), 10 ≤ n → ∀ F : MvPolynomial (Fin n) ℚ,
      F.IsHomogeneous 3 →
        ∃ x : Fin n → ℚ, x ≠ 0 ∧ MvPolynomial.eval x F = 0 :=
  @CubicTenVariables.Theorem11ReducedZetaInternalCurves.main

example : CubicTenVariables.HypersurfaceTheorem ↔ CubicTenVariables.MainTheorem :=
  CubicTenVariables.hypersurface_iff_main

example : CubicTenVariables.MainTheorem ↔ CubicTenVariables.IntegerTenVariableTheorem :=
  CubicTenVariables.main_iff_integerTen

example : CubicTenVariables.MainTheorem ↔ CubicTenVariables.SymmetricTenVariableTheorem :=
  CubicTenVariables.main_iff_symmetricTen

open Lean in
run_cmd do
  let env ← getEnv
  let roots : Array Name := #[`CubicTenVariables, `HessianTheorem11, `TranslatedDepthSeven]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let isProject := fun name => roots.any (fun root => root.isPrefixOf name)
  for root in roots do
    unless env.header.moduleNames.contains root do
      throwError "Public root was not imported: {root}"
  let projectModules := env.header.moduleNames.filter isProject
  let mut cubicTheorems := 0
  let mut hessianTheorems := 0
  let mut translatedTheorems := 0
  let mut otherTheorems := 0
  let mut declarations := 0
  let mut state : CollectAxioms.State := {}
  for (name, info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => env.mainModule
    if isProject name || isProject owner then
      declarations := declarations + 1
      match info with
      | .axiomInfo _ => throwError "Custom project axiom: {name} (module {owner})"
      | .thmInfo _ =>
        if (`CubicTenVariables).isPrefixOf name then
          cubicTheorems := cubicTheorems + 1
        else if (`HessianTheorem11).isPrefixOf name then
          hessianTheorems := hessianTheorems + 1
        else if (`TranslatedDepthSeven).isPrefixOf name then
          translatedTheorems := translatedTheorems + 1
        else
          otherTheorems := otherTheorems + 1
      | _ => pure ()
      -- Reuse the visited set; every newly reached dependency is still inspected.
      let (_, next) := ((CollectAxioms.collect name).run env).run state
      state := next
      for ax in state.axioms do
        unless allowed.contains ax do
          throwError "Unapproved axiom {ax} reachable from {name} (module {owner})"
  unless cubicTheorems > 0 && hessianTheorems > 0 && translatedTheorems > 0 do
    throwError "A public namespace contained no theorems; audit coverage is incomplete"
  logInfo m!"PUBLICATION AUDIT PASSED: {projectModules.size} imported project modules; {declarations} project declarations checked."
  logInfo m!"Theorems: {cubicTheorems} CubicTenVariables, {hessianTheorems} HessianTheorem11, {translatedTheorems} TranslatedDepthSeven, {otherTheorems} private/other-namespace project theorems."
  logInfo m!"Transitive axiom union: {state.axioms}"
  logInfo "Literal main signature checked: five explicit literature premises imply a nonzero rational zero for every homogeneous rational cubic in n >= 10 variables. The premises remain assumptions."

#print axioms CubicTenVariables.Theorem11ReducedZetaInternalCurves.main

end PublicationAudit
