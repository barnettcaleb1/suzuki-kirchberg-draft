import Suzuki
import Lean.Util.CollectAxioms

/- Audit every exported declaration in the project namespace, including generated
structure fields and instances. This audits dependencies, not claim coverage. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let entries := (env.constants.toList.filter fun (name, _) =>
    (`Suzuki).isPrefixOf name).toArray.qsort (fun a b => Name.quickLt a.1 b.1)
  for (name, info) in entries do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
        throwError "Disallowed axiom {ax} in {name}"
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .axiomInfo _ => "axiom"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .inductInfo _ => "inductive"
      | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient"
    let row := Json.mkObj [
      ("name", toJson name.toString),
      ("kind", toJson kind),
      ("axioms", toJson (axioms.toList.map Name.toString))]
    liftIO <| IO.println row.compress
