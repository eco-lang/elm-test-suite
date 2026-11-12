/-
  Runs every test program, in module form (plan step 3), through the evaluator of Chapter 7's
  rules, with both choices of a member of APPLY, and compares, for each check, the value its label
  has in the log of the program's evaluation with the value the test expects (its CHECK line). A
  check that expects no value agrees when the program has no meaning (it stops at Debug.todo).
  Writes ../example-run.md (a table per shard and a summary) and ../example-run.json (one entry
  per check, with the name of the program's theorem, `#mod_program_theorems`), relative to this
  project's folder, where `lake exe run-examples` is run.
-/
import StandardElmMech.AllPrograms
import StandardElmMech.Theorems
import StandardElmMech.WorkerTheorems
import StandardElmMech.Prog.T1
import Lean

open StandardElm Lean

def fuel : Nat := 100000

/-- The label of a row: a CHECK-NOT line's label is its text without the final colon. -/
def rowLabel (ck : Check) : String :=
  if ck.line == .not_ then (ck.text.dropEndWhile (· == ':')).toString else ck.label

/-- The value of a row: a CHECK-NOT line expects the label never to be logged. -/
def rowExpected (ck : Check) : String :=
  if ck.line == .not_ then "(no value)" else ck.expected

/-- The values a line has in the log of one evaluation of the program: for a regular expression,
    the printed lines of the log it matches; otherwise the shown value of each entry with the line's
    label; or what the evaluation came to when there is none. -/
def lineValues (ck : Check) (r : Res Val) : List String :=
  let found : List String :=
    if ck.isRegex then
      match Rx.parse ck.regexSource with
      | some rx => (r.log.map fun e => renderLog [e]).filter (rx.search ·) |>.map (·.dropEndWhile (· == '\n') |>.toString)
      | none => []
    else (r.log.filter (·.1 == rowLabel ck)).map (showElm ·.2)
  if ck.line == .not_ then
    match r.out with
    | .stuck => ["(no meaning)"]
    | _ => if found.isEmpty then ["(not logged)"] else found
  else match found, r.out with
    | [], .stuck => ["(no meaning)"]
    | [], .outOfFuel => ["(out of fuel)"]
    | [], _ => ["(not logged)"]
    | vs, _ => vs

/-- Does the line hold of one evaluation? A label line: the label is logged; a regular expression:
    it matches the printed log; a CHECK-NOT: the program has no meaning. -/
def lineHolds (ck : Check) (r : Res Val) : Bool :=
  if ck.line == .not_ then (match r.out with | .stuck => true | _ => false)
  else if ck.isRegex then (match Rx.parse ck.regexSource with
    | some rx => rx.search (renderLog r.log)
    | none => false)
  else if ck.labelOnly then r.log.any (·.1 == ck.label)
  else (lineValues ck r).contains ck.expected

def kindName : CheckKind → String
  | .unknown => "unknown" | .int => "int" | .float => "float" | .string => "string"
  | .char => "char" | .data => "data" | .function => "function"

def projectOf (p : Program) : String :=
  match (p.source.splitOn "/") with
  | "tests" :: proj :: _ => proj
  | _ => ""

structure Row where
  shard : String
  program : String
  project : String
  label : String
  expected : String
  kind : String
  values : List String
  status : String
  theorem_ : Option String
  proof : Option String
  skipped : Option String

def runShard (name : String) (ps : List Program) : List Row := Id.run do
  let mut rows : Array Row := #[]
  for p in ps do
    let mods := p.modules
    let res0 := Mod.evProgram (.const false) fuel (Mod.Btest []) mods 0
    let res1 := Mod.evProgram (.const true) fuel (Mod.Btest []) mods 0
    for ck in p.checks do
      -- the distinct values of the line in the logs, oracle false first
      let vs0 := lineValues ck res0
      let vs1 := lineValues ck res1
      let vs := (vs0 ++ vs1).eraseDups
      let ok := lineHolds ck res0 || lineHolds ck res1
      let status :=
        if !ok then "DIVERGENCE"
        else if !p.meaning && ck.line != .not_ then "agree (partial log)"
        else if vs0 == vs1 then "agree" else "agree (member of the set)"
      -- a program with no meaning has one theorem, NoMeaning; the values it logs before it stops
      -- are shown, but no theorem states them (step 6 states what such a program prints)
      let (thm, proof, skipped) :=
        if !p.meaning && ck.line != .not_ then (none, none, some "partial-log")
        else (some s!"t_{p.project}_{p.name}", some (if p.proofNative then "native" else "kernel"), none)
      rows := rows.push {
        shard := name, program := p.name, project := projectOf p, label := rowLabel ck,
        expected := rowExpected ck, kind := kindName ck.kind,
        values := vs, status := status,
        theorem_ := thm, proof := proof, skipped := skipped }
  return rows.toList

/-- The rows of the worker tests (plan step 5): each check against the log of the scheduler's run
    under the test's host (`Prog.runWorker`), whose theorem `#worker_theorems` states. -/
def runWorkerShard (name : String) (ws : List Prog.WorkerTest) : List Row := Id.run do
  let mut rows : Array Row := #[]
  for w in ws do
    let p := w.prog
    let run := Prog.runWorker w
    let lg := (run.map (·.1)).getD []
    for ck in p.checks do
      let found : List String :=
        if ck.isRegex then
          match Rx.parse ck.regexSource with
          | some rx => (lg.map fun e => renderLog [e]).filter (rx.search ·) |>.map (·.dropEndWhile (· == '\n') |>.toString)
          | none => []
        else (lg.filter (·.1 == rowLabel ck)).map (showElm ·.2)
      let vs := if run.isNone then ["(does not start)"] else if found.isEmpty then ["(not logged)"] else found
      let ok :=
        if ck.line == .not_ then run.isSome && found.isEmpty
        else if ck.isRegex then (match Rx.parse ck.regexSource with
          | some rx => rx.search (renderLog lg)
          | none => false)
        else if ck.labelOnly then lg.any (·.1 == ck.label)
        else found.contains ck.expected
      rows := rows.push {
        shard := name, program := p.name, project := projectOf p, label := rowLabel ck,
        expected := rowExpected ck, kind := kindName ck.kind,
        values := vs, status := if ok then "agree" else "DIVERGENCE",
        theorem_ := some s!"t_{p.project}_{p.name}", proof := some (if w.proofNative then "native" else "kernel"),
        skipped := none }
    -- a CHECK-NOT proved by hand (plan step 6): this run's printed log has no entry with the pattern
    for pat in w.checkNots do
      let hits := lg.filter fun e => Prog.containsStr pat (Prog.renderEntry e)
      rows := rows.push {
        shard := name, program := p.name, project := projectOf p, label := pat,
        expected := "(no value)", kind := "unknown",
        values := if hits.isEmpty then ["(not logged)"] else hits.map Prog.renderEntry,
        status := if run.isSome && hits.isEmpty then "agree" else "DIVERGENCE",
        theorem_ := some s!"t_{p.project}_{p.name}", proof := some "native", skipped := none }
  return rows.toList

def cell (s : String) : String := s.replace "|" "\\|"

def rowJson (r : Row) : Json :=
  Json.mkObj [
    ("shard", Json.str r.shard), ("program", Json.str r.program), ("project", Json.str r.project),
    ("label", Json.str r.label), ("expected", Json.str r.expected), ("kind", Json.str r.kind),
    ("definition", Json.arr (r.values.map Json.str).toArray), ("status", Json.str r.status),
    ("theorem", match r.theorem_ with | some t => Json.str t | none => Json.null),
    ("proof", match r.proof with | some t => Json.str t | none => Json.null),
    ("skipped", match r.skipped with | some s => Json.str s | none => Json.null)]

def main : IO UInt32 := do
  let shardSizes := exampleShards.map (fun (n, ps) => (n, ps.length)) ++
    generatedWorkerShards.map (fun (n, ws) => (n, ws.length))
  let rows := exampleShards.flatMap (fun (n, ps) => runShard n ps) ++
    generatedWorkerShards.flatMap fun (n, ws) => runWorkerShard n ws
  let total := rows.length
  let agree := (rows.filter fun r => r.status.startsWith "agree").length
  let diverge := total - agree
  let kernelChecks := (rows.filter fun r => r.proof == some "kernel").length
  let nativeChecks := (rows.filter fun r => r.proof == some "native").length
  let programTheorems := allPrograms.length + generatedWorkers.length
  let mut md := "# Standard Elm mechanisation: example run\n\n"
  md := md ++ s!"Programs: {programTheorems} ({generatedWorkers.length} workers), in {shardSizes.length} shards; checks: {total}.\n"
  for (n, size) in shardSizes do
    md := md ++ s!"\n## {n}\n\n| Program | Label | Expected (CHECK) | Definition | Status | Theorem |\n|---|---|---|---|---|---|\n"
    for r in rows.filter (·.shard == n) do
      md := md ++ s!"| {cell r.program} | {cell r.label} | {cell r.expected} | {cell (" or ".intercalate r.values)} | {r.status} | {r.theorem_.getD ""}{if r.proof == some "native" then " (native)" else ""} |\n"
    let shardRows := rows.filter (·.shard == n)
    md := md ++ s!"\n{n}: {size} programs, {shardRows.length} checks, {(shardRows.filter fun r => r.status.startsWith "agree").length} agree.\n"
  let summary := s!"Total: {total} checks, {agree} agree, {diverge} diverge (0 known); {kernelChecks} checks by decide +kernel, {nativeChecks} by native_decide, in {programTheorems} program theorems."
  md := md ++ s!"\n{summary}\n"
  IO.FS.writeFile "../example-run.md" md
  let json := Json.mkObj [
    ("total", Json.mkObj [("checks", toJson total), ("agree", toJson agree), ("diverge", toJson diverge),
      ("theorems", toJson kernelChecks), ("kernelChecks", toJson kernelChecks),
      ("nativeChecks", toJson nativeChecks), ("programTheorems", toJson programTheorems)]),
    ("checks", Json.arr (rows.map rowJson).toArray)]
  IO.FS.writeFile "../example-run.json" (json.pretty ++ "\n")
  IO.println summary
  for r in rows.filter (fun r => !r.status.startsWith "agree") do
    IO.println s!"  {r.status}: {r.program}: {r.label}: expected {r.expected}, definition {" or ".intercalate r.values}"
  return 0
