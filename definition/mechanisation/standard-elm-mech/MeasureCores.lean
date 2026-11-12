/-
  `lake exe measure-cores` (plan step 11, milestone (a), "Tests gained"): evaluates
  `Stat.coreRefutes Stat.Btest s_X` (compiled) on every compile-error test of step 7's classes
  `inference` and `fixity-inference`, and on every compile-success test as a sanity check (no
  program that compiles may be refuted: a refutation there is a bug, reported). Writes
  `../cores-report.json` with the result per test and prints the totals.

  A test is `refuted` when unification of its first module's constraints fails (so
  `not_legal_of_coreRefutes` proves `¬ LegalProgram Btest s_X`); `unsolved` when unification
  succeeds; `no-core` when `coreGen` gives no constraints (imports that do not elaborate, no
  body, type declarations or ports: not supported at milestone (a)); `outOfFuel` never expected.
-/
import Lean.Data.Json
import StandardElmMech.Generated.SrcAll
import StandardElmMech.Stat.Complete.CoreComplete
import StandardElmMech.Stat.TestBasis

open StandardElm StandardElm.Src StandardElm.Stat StandardElm.Stat.Complete
open Lean (Json)

def jsonStr (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c =>
    if c == '"' then "\\\"" else if c == '\\' then "\\\\" else if c == '\n' then "\\n"
    else if c.toNat < 32 then " " else c.toString) ++ "\""

/-- Why `coreGen` gives no constraints, or the outcome of unification. -/
def coreResult (B : SBasis) (sp : SProgram) : String × Nat :=
  match (Src.deriveProgram (Src.canonOrder sp)).modules with
  | m :: _ =>
    match coreGen B m with
    | some cs =>
      if cs.length > coreLimit then ("too large", cs.length) else
      match unifyCs cs with
      | .fail => ("refuted", cs.length)
      | .ok _ => ("unsolved", cs.length)
      | .outOfFuel => ("outOfFuel", cs.length)
    | none =>
      match importCtx B m.imports, m.body with
      | none, _ => ("no-core: imports", 0)
      | _, none => ("no-core: no body", 0)
      | _, _ => ("no-core: type declarations or ports", 0)
  | [] => ("no-core: no module", 0)

def strField (j : Json) (k : String) : String :=
  match j.getObjValAs? String k with
  | .ok s => s
  | .error _ => ""

def main : IO UInt32 := do
  let srcByKey : List ((String × String) × SProgram) :=
    srcShards.flatMap fun (_, ps) => ps.map fun (n, p) => ((p.project, n), p)
  let txt ← IO.FS.readFile "../static-classification.json"
  let j ← match Json.parse txt with
    | .ok j => pure j
    | .error e => throw (IO.userError e)
  let errs := match j.getObjValAs? (Array Json) "compileError" with
    | .ok a => a.toList
    | .error _ => []
  let succs := match j.getObjValAs? (Array Json) "compileSuccess" with
    | .ok a => a.toList
    | .error _ => []
  let inf := errs.filter fun e => strField e "class" == "inference" || strField e "class" == "fixity-inference"
  let mut entries : Array String := #[]
  let mut refuted := 0
  let mut total := 0
  let mut missing : Array String := #[]
  let mut byResult : List (String × Nat) := []
  for e in inf do
    let project := strField e "project"
    let name := strField e "name"
    match srcByKey.lookup (project, name) with
    | none => missing := missing.push s!"{project}/{name}"
    | some sp =>
      total := total + 1
      if (← IO.getEnv "CORES_TRACE").isSome then
        IO.eprintln s!"{project}/{name}"
        (← IO.getStderr).flush
      let t0 ← IO.monoMsNow
      let refutes := coreRefutes Btest sp
      let (res, n) := coreResult Btest sp
      let t1 ← IO.monoMsNow
      if refutes then refuted := refuted + 1
      if refutes != (res == "refuted") then IO.println s!"INCONSISTENT {project}/{name}"
      byResult := match byResult.lookup res with
        | some k => (res, k + 1) :: byResult.filter (·.1 != res)
        | none => (res, 1) :: byResult
      entries := entries.push ("  {\"project\": " ++ jsonStr project ++ ", \"name\": " ++ jsonStr name ++
        ", \"class\": " ++ jsonStr (strField e "class") ++ ", \"rule\": " ++ jsonStr (strField e "rule") ++
        ", \"refuted\": " ++ toString refutes ++ ", \"result\": " ++ jsonStr res ++
        ", \"constraints\": " ++ toString n ++ ", \"ms\": " ++ toString (t1 - t0) ++ "}")
  -- Sanity: no compile-success test is refuted.
  let mut succTotal := 0
  let mut succRefuted : Array String := #[]
  for e in succs do
    let project := strField e "project"
    let name := strField e "name"
    match srcByKey.lookup (project, name) with
    | none => pure ()
    | some sp =>
      succTotal := succTotal + 1
      if (← IO.getEnv "CORES_TRACE").isSome then
        IO.eprintln s!"success {project}/{name}"
        (← IO.getStderr).flush
      if coreRefutes Btest sp then succRefuted := succRefuted.push s!"{project}/{name}"
  IO.println s!"Cores (milestone (a)): {refuted} of {total} inference/fixity-inference tests refuted"
  for (r, k) in byResult.reverse do
    IO.println s!"  {r}: {k}"
  if !missing.isEmpty then IO.println s!"not found in the source syntax: {missing.toList}"
  IO.println s!"Sanity: {succRefuted.size} of {succTotal} compile-success tests refuted (must be 0)"
  for n in succRefuted do IO.println s!"  BUG: refuted a compile-success test: {n}"
  let json := "{\n\"refuted\": " ++ toString refuted ++ ",\n\"total\": " ++ toString total ++
    ",\n\"compileSuccessChecked\": " ++ toString succTotal ++
    ",\n\"compileSuccessRefuted\": [" ++ ", ".intercalate (succRefuted.toList.map jsonStr) ++ "]" ++
    ",\n\"tests\": [\n" ++ ",\n".intercalate entries.toList ++ "\n]\n}\n"
  IO.FS.writeFile "../cores-report.json" json
  return (if succRefuted.isEmpty then 0 else 1)
