/-
  `lake exe compare-e2e` (plan step 10): for every program translated today, the reduced program
  that Lean computes from its source syntax (`Stat.endToEnd Stat.Btest s_X`: derived forms,
  inference, checker, specialisation, erasure) against the reduced part of the translator's program
  (`g_X.reduced`, or `w_X.reduced` for a worker). Prints the totals and, for each difference or
  error, the test and its first difference; writes `../e2e-report.json` with the result per test.
  "Agree" means equal reduced programs: no normalisation is applied to either side.
-/
import StandardElmMech.AllPrograms
import StandardElmMech.Generated.SrcAll
import StandardElmMech.Stat.EndToEnd
import StandardElmMech.Stat.TestBasis

open StandardElm StandardElm.Src

def oneLine (f : Std.Format) : String := f.pretty 1000000

/-- The context of the first difference of two strings: up to 80 characters before it and 160
    after. -/
def firstDiff (a b : String) : String × String :=
  let common := ((a.toList.zip b.toList).takeWhile fun (x, y) => x == y).length
  let cut (s : String) : String :=
    let pre := if common > 80 then "…" else ""
    pre ++ String.ofList ((s.toList.drop (common - 80)).take 240)
  (cut a, cut b)

def topItems : Mod.TopDec → List Mod.TopDec
  | .seq a b => topItems a ++ topItems b
  | d => [d]

def topName : Mod.TopDec → String
  | .val vb => "value group " ++ toString (vb.map (·.1))
  | .type _ => "custom types"
  | .alias tb => "alias " ++ tb.tycon
  | .port x _ _ => "port " ++ x
  | .seq _ _ => "seq"

/-- The first difference of two reduced programs, described. -/
def describe (exp got : Mod.Reduced) : String := Id.run do
  if exp.kind != got.kind then
    return s!"kind: expected {repr exp.kind}, got {repr got.kind}"
  if exp.flagsType != got.flagsType then
    return s!"flags type: expected {oneLine (repr exp.flagsType)}, got {oneLine (repr got.flagsType)}"
  if exp.modules.length != got.modules.length then
    return s!"{exp.modules.length} modules expected, {got.modules.length} computed"
  for (me, mg) in exp.modules.zip got.modules do
    let name := me.header.modid
    if me.header != mg.header then
      let (x, y) := firstDiff (oneLine (repr me.header)) (oneLine (repr mg.header))
      return s!"module {name}, header:\n    expected {x}\n    got      {y}"
    if me.imports != mg.imports then
      let (x, y) := firstDiff (oneLine (repr me.imports)) (oneLine (repr mg.imports))
      return s!"module {name}, imports:\n    expected {x}\n    got      {y}"
    let ie := topItems me.body
    let ig := topItems mg.body
    for (de, dg) in ie.zip ig do
      if de != dg then
        let (x, y) := firstDiff (oneLine (repr de)) (oneLine (repr dg))
        return s!"module {name}, {topName de} (computed: {topName dg}):\n    expected {x}\n    got      {y}"
    if ie.length != ig.length then
      return s!"module {name}: {ie.length} declarations expected, {ig.length} computed"
  if exp.ports != got.ports then
    return "ports"
  return "equal?"


def jsonStr (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c =>
    if c == '"' then "\\\"" else if c == '\\' then "\\\\" else if c == '\n' then "\\n"
    else if c.toNat < 32 then " " else c.toString) ++ "\""

def main : IO UInt32 := do
  let srcByKey : List ((String × String) × SProgram) :=
    srcShards.flatMap fun (_, ps) => ps.map fun (n, p) => ((p.project, n), p)
  let views : List (Program × Mod.Reduced) := allPrograms.map fun p => (p, p.reduced)
  let workers : List (Program × Mod.Reduced) := generatedWorkers.map fun w => (w.prog, w.reduced)
  let mut total := 0
  let mut agree := 0
  let mut differ := 0
  let mut errors := 0
  let mut missing : Array String := #[]
  let mut entries : Array String := #[]
  for (p, expected) in views ++ workers do
    let project := match p.source.splitOn "/" with
      | "tests" :: proj :: _ => proj
      | _ => ""
    match srcByKey.lookup (project, p.name) with
    | none => missing := missing.push p.name
    | some s =>
      total := total + 1
      let t0 ← IO.monoMsNow
      let r := Stat.endToEnd Stat.Btest s
      let (res, detail) := match r with
        | .ok got =>
          if got == expected then ("agree", "")
          else ("differ", describe expected got)
        | .error e => ("error", oneLine (repr e))
      let t1 ← IO.monoMsNow
      if res == "agree" then agree := agree + 1
      else if res == "differ" then
        differ := differ + 1
        IO.println s!"DIFFER {project}/{p.name}: {detail}"
      else
        errors := errors + 1
        IO.println s!"ERROR {project}/{p.name}: {detail}"
      entries := entries.push ("  {\"project\": " ++ jsonStr project ++ ", \"name\": " ++ jsonStr p.name ++
        ", \"result\": " ++ jsonStr res ++ ", \"ms\": " ++ toString (t1 - t0) ++
        (if detail.isEmpty then "" else ", \"detail\": " ++ jsonStr detail) ++ "}")
  IO.println s!"End to end: {total} programs; {agree} agree; {differ} differ; {errors} errors"
  if !missing.isEmpty then IO.println s!"not found in the source syntax: {missing.toList}"
  IO.FS.writeFile "../e2e-report.json" ("[\n" ++ ",\n".intercalate entries.toList ++ "\n]\n")
  return (if differ == 0 && errors == 0 then 0 else 1)
