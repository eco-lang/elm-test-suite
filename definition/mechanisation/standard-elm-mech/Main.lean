/-
  Runs every example through the evaluator, with both choices of a member of
  APPLY, and compares the definition's value with the value the test expects
  (its CHECK line). Writes ../example-run.md (a table per shard and a summary)
  and ../example-run.json (one entry per check, with the name of the theorem
  `#kernel_checks` made for it, if any), relative to this project's folder,
  where `lake exe run-examples` is run.
-/
import StandardElmMech.AllPrograms
import StandardElmMech.Theorems
import Lean

open StandardElm Lean

def fuel : Nat := 100000

def showResult : Option Val → String
  | some v => showElm v
  | none => "(no value)"

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
  skipped : Option String

def runShard (name : String) (ps : List Program) : List Row := Id.run do
  let mut rows : Array Row := #[]
  let mut k := 0
  for p in ps do
    for ck in p.checks do
      let e := p.phrase ck
      let r0 := showResult (evExp false fuel p.env e)
      let r1 := showResult (evExp true fuel p.env e)
      let ok := ck.expected == r0 || ck.expected == r1
      let status :=
        if ok then (if r0 == r1 then "agree" else "agree (member of the set)")
        else if knownDiv.contains (p.name, ck.label) then "DIVERGENCE (known)"
        else "DIVERGENCE"
      let (thm, skipped) :=
        match kernelCheck? p ck with
        | some _ => (some s!"kc_{name}_{k}", none)
        | none =>
          if knownDiv.contains (p.name, ck.label) then (none, some "divergence")
          else if p.native then (none, some "native")
          else if ck.kind == CheckKind.float || (ck.kind == CheckKind.unknown && floatValued p ck) then (none, some "float")
          else (none, some "value")
      if thm.isSome then k := k + 1
      rows := rows.push {
        shard := name, program := p.name, project := projectOf p, label := ck.label,
        expected := ck.expected, kind := kindName ck.kind,
        values := if r0 == r1 then [r0] else [r0, r1], status := status,
        theorem_ := thm, skipped := skipped }
  return rows.toList

def cell (s : String) : String := s.replace "|" "\\|"

def rowJson (r : Row) : Json :=
  Json.mkObj [
    ("shard", Json.str r.shard), ("program", Json.str r.program), ("project", Json.str r.project),
    ("label", Json.str r.label), ("expected", Json.str r.expected), ("kind", Json.str r.kind),
    ("definition", Json.arr (r.values.map Json.str).toArray), ("status", Json.str r.status),
    ("theorem", match r.theorem_ with | some t => Json.str t | none => Json.null),
    ("skipped", match r.skipped with | some s => Json.str s | none => Json.null)]

def main : IO UInt32 := do
  let rows := exampleShards.flatMap fun (n, ps) => runShard n ps
  let total := rows.length
  let agree := (rows.filter fun r => r.status.startsWith "agree").length
  let known := (rows.filter fun r => r.status == "DIVERGENCE (known)").length
  let diverge := total - agree
  let theorems := (rows.filter fun r => r.theorem_.isSome).length
  let mut md := "# Standard Elm mechanisation: example run\n\n"
  md := md ++ s!"Programs: {allPrograms.length}, in {exampleShards.length} shards; checks: {total}.\n"
  for (n, ps) in exampleShards do
    md := md ++ s!"\n## {n}\n\n| Program | Label | Expected (CHECK) | Definition | Status | Theorem |\n|---|---|---|---|---|---|\n"
    for r in rows.filter (·.shard == n) do
      md := md ++ s!"| {cell r.program} | {cell r.label} | {cell r.expected} | {cell (" or ".intercalate r.values)} | {r.status} | {r.theorem_.getD ""} |\n"
    let shardRows := rows.filter (·.shard == n)
    md := md ++ s!"\n{n}: {ps.length} programs, {shardRows.length} checks, {(shardRows.filter fun r => r.status.startsWith "agree").length} agree.\n"
  md := md ++ s!"\nTotal: {total} checks, {agree} agree, {diverge} diverge ({known} known); {theorems} theorems by decide +kernel.\n"
  IO.FS.writeFile "../example-run.md" md
  let json := Json.mkObj [
    ("total", Json.mkObj [("checks", toJson total), ("agree", toJson agree), ("diverge", toJson diverge), ("theorems", toJson theorems)]),
    ("checks", Json.arr (rows.map rowJson).toArray)]
  IO.FS.writeFile "../example-run.json" (json.pretty ++ "\n")
  IO.println s!"Total: {total} checks, {agree} agree, {diverge} diverge ({known} known); {theorems} theorems by decide +kernel."
  for r in rows.filter (fun r => !r.status.startsWith "agree") do
    IO.println s!"  {r.status}: {r.program}: {r.label}: expected {r.expected}, definition {" or ".intercalate r.values}"
  return 0
