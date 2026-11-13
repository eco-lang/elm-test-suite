/-
  `lake exe measure-w` (plan step 11, milestone (f), "Tests gained"): runs module- and program-level
  W (`Complete.MW.inferProgramW`, compiled) on every compile-error test of step 7's refused classes
  and on every compile-success test. Prints, for the compile-error tests no earlier decider refuses,
  whether W refutes them (`MW.wRefutes`: the first module fails), and for the compile-success tests
  how many W elaborates (`ok`) and how many it refutes (must be 0). Writes `../w-report.json`.
-/
import Lean.Data.Json
import StandardElmMech.Generated.SrcAll
import StandardElmMech.Stat.Complete.Discharge
import StandardElmMech.Stat.RefuseAll
import StandardElmMech.Stat.TestBasis

open StandardElm StandardElm.Src StandardElm.Stat StandardElm.Stat.Complete
open Lean (Json)

def strField (j : Json) (k : String) : String :=
  match j.getObjValAs? String k with
  | .ok s => s
  | .error _ => ""

def mresName : MW.MRes → String
  | .ok _ => "ok"
  | .fail => "fail"
  | .unsupported => "unsupported"
  | .outOfFuel => "outOfFuel"
  | .internal => "internal"

/-- The outcome of W on each module of a program, in order, until the first that is not `ok`. -/
def perModule (B : SBasis) : List BModule → List String
  | [] => []
  | m :: ms =>
    match MW.inferModuleW MW.wFuel B m with
    | .ok a =>
      match a.result B with
      | some (B', _) => "ok" :: perModule (B.plus B') ms
      | none => ["ok-but-no-result"]
    | r => [mresName r]

/-- Why W gives a module no derivation (the step that stops it). -/
def why (B : SBasis) (m : BModule) : String :=
  match importCtx B m.imports with
  | none => "imports"
  | some C =>
    match m.body with
    | none => "no body"
    | some d =>
      let tyOK : Option Ctx :=
        match (MW.splitBody d).1 with
        | none => some C
        | some (db, tbs) =>
          match MW.typesW C db tbs with
          | some (TE, VE) => some (C.oplusE ⟨[], TE, VE⟩)
          | none => none
      match tyOK with
      | none =>
        match (MW.splitBody d).1 with
        | some (db, tbs) =>
          match MW.solveTypes C db tbs with
          | none => "types: solveTypes"
          | some (TE, VE) => if checkTypes C TE VE db tbs then "types: not ordered" else "types: checkTypes"
        | none => "types"
      | some C1 =>
        match (MW.splitBody d).2 with
        | none => "types only"
        | some r =>
          match MW.bodyExp r with
          | none => "body shape (port?)"
          | some e => if MW.rootOKB C1 then
              match WE.inferExpWD MW.wFuel C1 e with
              | .ok _ => "exp ok"
              | .fail => "exp fail"
              | .unsupported => "exp unsupported"
              | .outOfFuel => "exp outOfFuel"
              | .internal => "exp internal"
            else "root context"

def refusersPre : List (String × (SBasis → SProgram → Bool)) :=
  [("imports", importsFailB), ("scope", scopeFailB), ("further", furtherFailB), ("types", typesFailB),
   ("main", mainFailB), ("core", Complete.coreRefutes)]

/-- `--probe NAME STAGE`: run W on one program up to a stage (exp, check, names), to find where
    its time and memory go. -/
def probe (name : String) (stage : String) : IO UInt32 := do
  let srcByKey : List (String × SProgram) :=
    srcShards.flatMap fun (_, ps) => ps.map fun (n, p) => (n, p)
  match srcByKey.lookup name with
  | none => IO.println s!"no program {name}"; return 1
  | some sp =>
    let B := Btest
    match (deriveProgram (canonOrder sp)).modules with
    | [m] =>
      match importCtx B m.imports, m.body with
      | some C, some d =>
        match MW.typesPart C (MW.splitBody d).1, (MW.splitBody d).2 with
        | some (at?, C1), some r =>
          match MW.bodyExp r with
          | some e =>
            let t0 ← IO.monoMsNow
            match WE.inferExpWD MW.wFuel C1 e with
            | .ok ae =>
              let t1 ← IO.monoMsNow
              IO.println s!"exp ok [{t1 - t0} ms]"
              if stage == "exp" then return 0
              match MW.unLet r ae with
              | some av =>
                let a : AModule := ⟨m.header, m.imports, MW.joinBody at? (some av)⟩
                let c := checkModule B a
                let t2 ← IO.monoMsNow
                IO.println s!"check {c} [{t2 - t1} ms]"
                if stage == "check" then return 0
                let n := MW.namesB B a
                let t3 ← IO.monoMsNow
                IO.println s!"names {n} [{t3 - t2} ms]"
                return 0
              | none => IO.println "unLet none"; return 1
            | _ => IO.println "exp not ok"; return 1
          | none => IO.println "no body exp"; return 1
        | _, _ => IO.println "types or no values"; return 1
      | _, _ => IO.println "imports or no body"; return 1
    | _ => IO.println "several modules"; return 1

/-- `--times`: the time of the compiled check `wCheck` (W and the conditions of Chapter 9) on every
    program with a legality theorem, slowest first: a proxy for the kernel's cost (milestone (g)). -/
def times : IO UInt32 := do
  let txt ← IO.FS.readFile "../static-classification.json"
  let j ← match Json.parse txt with
    | .ok j => pure j
    | .error e => throw (IO.userError e)
  let succs := match j.getObjValAs? (Array Json) "compileSuccess" with
    | .ok a => a.toList
    | .error _ => []
  let srcByKey : List ((String × String) × SProgram) :=
    srcShards.flatMap fun (_, ps) => ps.map fun (n, p) => ((p.project, n), p)
  let mut rows : Array (Nat × String × Bool) := #[]
  for e in succs do
    let project := strField e "project"
    let name := strField e "name"
    if !["B0", "harness", "library", "helper"].contains (strField e "basis") then continue
    if name == "CompilerIssue2281LongLineListTest" then continue
    match srcByKey.lookup (project, name) with
    | none => pure ()
    | some sp =>
      let t0 ← IO.monoNanosNow
      let ok := wCheck Btest sp none
      let t1 ← IO.monoNanosNow
      rows := rows.push ((t1 - t0) / 1000, s!"{project}/{name}", ok)
  let sorted := rows.qsort (fun a b => a.1 > b.1)
  for (us, k, ok) in sorted.toList do IO.println s!"{us} {k} {ok}"
  return 0

def main (args : List String) : IO UInt32 := do
  if let "--probe" :: name :: stage :: _ := args then return (← probe name stage)
  if args.contains "--times" then return (← times)
  let onlyErr := args.contains "--errors"
  let noErr := args.contains "--heavy" || args.contains "--success"
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
  let refused := ["syntactic", "further", "static-deterministic", "inference", "fixity-inference"]
  let B := Btest
  let mut entries : Array Json := #[]
  let mut nNew := 0
  let mut nOpen := 0
  for e in errs do
    let project := strField e "project"
    let name := strField e "name"
    let cls := strField e "class"
    if noErr || !refused.contains cls || cls == "syntactic" then continue
    match srcByKey.lookup (project, name) with
    | none => pure ()
    | some sp =>
      if (← IO.getEnv "W_TRACE").isSome then
        IO.println s!"error {project}/{name}"
        (← IO.getStdout).flush
      let pre := refusersPre.find? (fun (_, d) => d B sp)
      match pre with
      | some _ => pure ()
      | none =>
        let ms := (deriveProgram (canonOrder sp)).modules
        let t0 ← IO.monoMsNow
        let r := MW.wRefutes B sp
        let t1 ← IO.monoMsNow
        let w := match ms with
          | m :: _ => why B m
          | [] => "no module"
        if r then nNew := nNew + 1 else nOpen := nOpen + 1
        (← IO.getStdout).flush
        IO.println s!"  {if r then "REFUTED" else "open   "} {project}/{name} ({cls}, {ms.length} modules): {w} [{t1 - t0} ms] {perModule B ms}"
        entries := entries.push (Json.mkObj [("test", Json.str s!"{project}/{name}"), ("class", Json.str cls),
          ("refuted", Json.bool r), ("why", Json.str w), ("ms", Json.num (t1 - t0))])
  IO.println s!"Compile-error tests no earlier decider refuses: {nNew} refuted by W, {nOpen} not"
  if onlyErr then return 0
  let heavy := ["elm/CompilerIssue2281LongLineListTest", "elm/WideClosureArity300Test", "elm/WideCtorMixedTest",
    "elm/WideRecord600Test", "elm/WideRecord1100Test", "elm/WideRecordDecoder26Test", "elm/WideRecordDecoder30Test",
    "elm/WideRecordDecoder70Test", "elm/WideRecordDecoder300Test"]
  let onlyHeavy := args.contains "--heavy"
  let mut nAll := 0
  let mut nSucc := 0
  let mut nOk := 0
  let mut nFail : Array String := #[]
  let mut others : Array (String × String) := #[]
  let mut byWhy : List (String × Nat) := []
  let mut notRun : Array String := #[]
  for e in succs do
    let project := strField e "project"
    let name := strField e "name"
    let basis := strField e "basis"
    if onlyHeavy && !heavy.contains s!"{project}/{name}" then continue
    if args.contains "--light" && heavy.contains s!"{project}/{name}" then continue
    -- W does not finish within the memory budget on a list literal of 22,000 elements (milestone (g))
    if !args.contains "--with-2281" && name == "CompilerIssue2281LongLineListTest" then
      notRun := notRun.push s!"{project}/{name}"
      continue
    match srcByKey.lookup (project, name) with
    | none => pure ()
    | some sp =>
      nAll := nAll + 1
      if !["B0", "harness", "library", "helper"].contains basis then
        if MW.wRefutes B sp then nFail := nFail.push s!"{project}/{name}"
        continue
      nSucc := nSucc + 1
      let ms := (deriveProgram (canonOrder sp)).modules
      if (← IO.getEnv "W_TRACE").isSome then
        IO.println s!"success {project}/{name}"
        (← IO.getStdout).flush
      if MW.wRefutes B sp then nFail := nFail.push s!"{project}/{name}"
      match MW.inferProgramW MW.wFuel B ms with
      | .ok _ => nOk := nOk + 1
      | _ =>
        let pm := perModule B ms
        let w := match (ms.zip pm).find? (fun (_, s) => s != "ok") with
          | some (m, s) => s!"{s}: {why (B) m}"
          | none => "?"
        others := others.push (s!"{project}/{name}", s!"{pm} {w}")
        let k := (w.splitOn " [").headD w
        byWhy := match byWhy.lookup k with
          | some c => (k, c + 1) :: byWhy.filter (·.1 != k)
          | none => (k, 1) :: byWhy
  IO.println s!"Compile-success tests: {nAll} checked for refutation, W refutes {nFail.size} (must be 0); {nSucc} with a legality theorem's basis, W ok on {nOk}; not run: {notRun.toList}"
  for n in nFail do IO.println s!"  BUG: W refutes a compile-success test: {n}"
  for (k, c) in byWhy do IO.println s!"  not ok: {c}: {k}"
  for (k, w) in others.toList.take 80 do IO.println s!"    {k}: {w}"
  IO.FS.writeFile "../w-report.json" ((Json.mkObj [("errors", Json.arr entries),
    ("compileSuccess", Json.num nSucc), ("ok", Json.num nOk), ("notRun", Json.arr (notRun.map Json.str)),
    ("refutedCompileSuccess", Json.arr (nFail.map Json.str)),
    ("notOk", Json.arr (others.map fun (k, w) => Json.mkObj [("test", Json.str k), ("why", Json.str w)]))]).pretty ++ "\n")
  return (if nFail.isEmpty then 0 else 1)
