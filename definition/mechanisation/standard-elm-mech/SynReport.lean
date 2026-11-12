/-
  Writes ../syntactic-report.json (plan step 8): for every program written in the source syntax,
  whether it meets the AST-decidable restrictions, whether it is a program (its main module
  declares `main`) or a module tested alone, and the restrictions it breaks. Run from this
  project's folder: `lake exe syn-report`.
-/
import StandardElmMech.Generated.SrcAll
import StandardElmMech.Src.SynCommand
import Lean

open StandardElm StandardElm.Src Lean

def main : IO UInt32 := do
  let mut rows : Array Json := #[]
  let mut ok := 0
  let mut bad := 0
  for (_, progs) in srcShards do
    for (name, p) in progs do
      let hasMain := decide (SProgram.HasMain p)
      let meets := if hasMain then decide (SynOK p) else decide (ModulesSynOK p)
      if meets then ok := ok + 1 else bad := bad + 1
      let breaks := (moduleRules.filter fun (r, _) => !(p.modules.all (moduleDecider r))).map (·.2) ++
        (programRules.filter fun (r, _) => !(programDecider r p) && (hasMain || r != "ProgramMain")).map (·.2)
      rows := rows.push (Json.mkObj [
        ("project", Json.str p.project), ("name", Json.str name), ("synOK", Json.bool meets),
        ("program", Json.bool hasMain),
        ("breaks", Json.arr (breaks.map fun s => Json.str ("res:" ++ s.replace "_" "-")).toArray)])
  let summary := s!"{ok + bad} programs: {ok} meet the AST-decidable restrictions, {bad} do not."
  IO.FS.writeFile "../syntactic-report.json"
    ((Json.mkObj [("summary", Json.str summary), ("programs", Json.arr rows)]).pretty ++ "\n")
  IO.println summary
  return 0
