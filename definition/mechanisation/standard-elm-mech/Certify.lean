/-
  `lake exe certify` (plan step 9, section 13): runs the inference of Stat/Infer.lean, compiled,
  over every program step 7 classes as a compile-success test with basis B0, harness, library or
  helper, and writes the per-test theorems to `StandardElmMech/Certs/`:

  - `Contexts<nn>.lean`: the context of each distinct list of imports of a one-module program, as
    a literal, with the lemma that the imports give it (`ctx_<k>_eq`, by the kernel);
  - `<Project><nn>.lean`: for each program W and the checks accept that the translator does not
    translate, the theorem `legal_<project>_<Test>`, proved by the kernel running W (plan step 11,
    milestone (g)) and the checks;
  - `Refusals<nn>.lean`: the refusal theorems `refuse_<project>_<Test>`;
  - `EndToEnd<nn>.lean`: for each translated test, `wcheck_X` (W's derivation checked, with the
    reduced program the translator wrote), and from it `legal_X`, `mean_X` and `ident_X`, all without
    hypothesis; and step 10's `spec_X` (Lean's pipeline, with step 9's inference, gives the reduced
    program);
  - `CertsAll.lean`, importing them.

  A program the inference or a check refuses gets no theorem and is listed in the report
  (`../static-report.json`). `--check` compares the files instead of writing them. Run from this
  project's folder.
-/
import StandardElmMech.Generated.SrcAll
import StandardElmMech.Stat.Legal
import StandardElmMech.Stat.TestBasis
import StandardElmMech.Stat.CertPrint
import StandardElmMech.Stat.RefuseAll
import StandardElmMech.Stat.Pipeline
import StandardElmMech.Stat.ModuleStep
import StandardElmMech.Stat.Complete.Discharge
import StandardElmMech.AllPrograms
import StandardElmMech.WorkerTheorems
import Lean

open StandardElm StandardElm.Src StandardElm.Stat Lean

def certsDir : String := "StandardElmMech/Certs/"
def shardSize : Nat := 40
def ctxPerFile : Nat := 8

def upperCamel (s : String) : String :=
  "".intercalate ((s.splitOn "-").map fun w => w.capitalize)

def ident (s : String) : String := s.replace "-" "_"

def pad2 (n : Nat) : String := if n < 10 then "0" ++ toString n else toString n

def ctxFile (i : Nat) : String := "Contexts" ++ pad2 (i / ctxPerFile + 1)

/-- The programs whose `spec_` theorem (step 10's pipeline, step 9's inference) breaks the memory
    budget when the kernel runs it (conventions, "Memory budget": above 6.5 GB of resident set for the
    one `lean` process, measured one theorem per process on 2026-11-12). Their `spec_` theorems are
    proved by `native_decide` and tagged `[native]`: the Lean compiler joins the trusted base for them. -/
def staticBudgetNative : List String :=
  ["elm/CompilerIssue2281LongLineListTest",   -- above 8 GB
   "elm/WideClosureArity300Test",             -- above 8 GB
   "elm/WideCtorMixedTest",                   -- above 8 GB
   "elm/WideRecord600Test",                   -- above 8 GB
   "elm/WideRecord1100Test",                  -- above 8 GB
   "elm/WideRecordDecoder26Test",             -- 6.85 GB
   "elm/WideRecordDecoder30Test",             -- above 8 GB
   "elm/WideRecordDecoder70Test",             -- above 8 GB
   "elm/WideRecordDecoder300Test",            -- above 8 GB
   "elm/WideRecord40Test"]                    -- 6.31 GB alone, 6.63 GB in its shard (2026-11-13)

/-- The programs whose W check (`Stat.wCheck`: W, Chapter 9's conditions, the further restrictions and,
    for a translated test, the reduced program; plan step 11, milestone (g)) breaks the memory budget
    when the kernel runs it, measured one theorem per process (2026-11-13, `/usr/bin/time -v`, maximum
    resident set; the 52 programs whose compiled check is slowest were measured one by one, the others
    through their shard's build), with a margin: above 6.3 GB, since a shard holds 40 such theorems. Their
    `wcheck_`/`legal_` theorems, and the `ident_` and `mean_` theorems that use them, are proved by
    `native_decide` and tagged `[native]`. -/
def wBudgetNative : List String :=
  ["elm/WideClosureArity300Test",             -- above 6.5 GB (killed)
   "elm/WideCtorMixedTest",                   -- above 6.5 GB (killed)
   "elm/WideRecord600Test",                   -- above 6.5 GB (killed)
   "elm/WideRecord1100Test",                  -- above 6.5 GB (killed)
   "elm/WideRecordDecoder26Test",             -- above 6.5 GB (killed)
   "elm/WideRecordDecoder30Test",             -- above 6.5 GB (killed)
   "elm/WideRecordDecoder70Test",             -- above 6.5 GB (killed)
   "elm/WideRecordDecoder300Test",            -- above 6.5 GB (killed)
   "elm/WideRecord40Test",                    -- above 6.5 GB (killed)
   "elm/WideClosureSat26Test",                -- 7.52 GB
   "elm/WideRecord33Test",                    -- 7.20 GB
   "elm/CombinatorListStringTest",            -- 6.80 GB
   "elm/AppendTypeSplitTest",                 -- 6.69 GB
   "elm/FloatEdgeTest",                       -- 6.47 GB
   "elm/WideCtorField24Test"]                 -- 6.37 GB

/-- Programs W does not elaborate in reasonable time even compiled: their `legal_` theorem keeps step
    9's form, under D11 (`InferPrincipalFor`), tagged `[principal]`. -/
def wSkip : List String := ["elm/CompilerIssue2281LongLineListTest"]

/-- The refusal deciders, in the order they are tried: the lemma that turns the decider's `true`
    into `¬ LegalProgram`, and the decider (Stat/RefuseAll.lean). -/
def refusers : List (String × (SBasis → SProgram → Bool)) :=
  [("Stat.not_legal_of_imports", importsFailB),
   ("Stat.not_legal_of_scopeFailB", scopeFailB),
   ("Stat.not_legal_of_furtherFailB", furtherFailB),
   ("Stat.not_legal_of_typesFailB", typesFailB),
   ("Stat.not_legal_of_mainFailB", mainFailB),
   ("Stat.not_legal_of_coreRefutes", Complete.coreRefutes),   -- step 11, milestone (a)
   ("Stat.not_legal_of_wRefutes Stat.Btest_inv", Complete.MW.wRefutes),   -- step 11, milestone (f)
   ("Stat.not_legal_of_wMainVar_test", wMainVarB)]   -- step 11, milestone (g): A96's flags

/-- The compile-error classes of step 7 that this step refuses. -/
def refusedClasses : List String := ["syntactic", "further", "static-deterministic", "inference", "fixity-inference"]

/-- Why a program gets no theorem. -/
def diagnose1 (B : SBasis) (C : Ctx) (sp : SProgram) (m : BModule) : String :=
  if !decSynOK sp then "syntactic restrictions" else
  match inferModuleIn B C m with
  | .error e => s!"inference: {e}"
  | .ok a =>
    match a.resultIn B C with
    | none => "the certificate does not check"
    | some (B', E) =>
      if !furtherModInB B E a then "further restrictions"
      else if !portsDisjointB B B' then "port names"
      else if (mainTy E).isNone then "type of main"
      else "unknown"

def diagnoseN (B : SBasis) (sp : SProgram) : String :=
  if !decSynOK sp then "syntactic restrictions" else
  match inferProgram B (deriveProgram (canonOrder sp)) with
  | .error e => s!"inference: {e}"
  | .ok _ => "a check of a module or of main"

structure Out where
  path : String
  body : String

def header : String := "/- Generated by `lake exe certify` (Certify.lean, plan step 9). Do not edit. -/\n"

/-- Why W gives a program no theorem. -/
def diagnoseW (B : SBasis) (sp : SProgram) : String :=
  if !decSynOK sp then "syntactic restrictions" else
  match Complete.MW.inferProgramW Complete.MW.wFuel B (deriveProgram (canonOrder sp)).modules with
  | .ok _ => "a check of Chapter 9 or a further restriction"
  | .fail => "W fails"
  | .other => "W gives no derivation"

/-- A translated test, as the manifest describes it. -/
structure Transl where
  gdef : String
  gshard : String
  kind : String
  lean : String
  hasNots : Bool
  sdef : String
  sshard : String

def main (args : List String) : IO UInt32 := do
  let check := args.contains "--check"
  let cls ← IO.FS.readFile "../static-classification.json"
  let j ← IO.ofExcept (Json.parse cls)
  let cs ← IO.ofExcept (j.getObjValAs? (Array Json) "compileSuccess")
  let mut basisOf : Std.HashMap String String := {}
  for t in cs do
    let p := (t.getObjValAs? String "project").toOption.getD ""
    let n := (t.getObjValAs? String "name").toOption.getD ""
    let b := (t.getObjValAs? String "basis").toOption.getD ""
    basisOf := basisOf.insert (p ++ "/" ++ n) b
  -- the translated tests (step 10)
  let man ← IO.FS.readFile "../translation-manifest.json"
  let mj ← IO.ofExcept (Json.parse man)
  let mts ← IO.ofExcept (mj.getObjValAs? (Array Json) "tests")
  let mut translOf : Std.HashMap String Transl := {}
  for t in mts do
    if (t.getObjValAs? String "status").toOption != some "translated" then continue
    let p := (t.getObjValAs? String "project").toOption.getD ""
    let n := (t.getObjValAs? String "name").toOption.getD ""
    let src := (t.getObjVal? "src").toOption.getD Json.null
    let hasNots := match t.getObjValAs? (Array Json) "checkNots" with
      | .ok a => !a.isEmpty
      | .error _ => false
    let tr : Transl := ⟨(t.getObjValAs? String "def").toOption.getD "", (t.getObjValAs? String "shard").toOption.getD "",
      (t.getObjValAs? String "kind").toOption.getD "view", (t.getObjValAs? String "lean").toOption.getD "", hasNots,
      (src.getObjValAs? String "def").toOption.getD "", (src.getObjValAs? String "shard").toOption.getD ""⟩
    if tr.sdef != "" then translOf := translOf.insert (p ++ "/" ++ n) tr
  let B := Btest
  let mut ctxs : Array (List BImport × Ctx) := #[]
  -- per project: (source shard, theorem text) for each program with a theorem
  let mut thms : Array (String × String × String) := #[]
  let mut failed : Array (String × String) := #[]
  let mut nOne := 0
  let mut nMany := 0
  let mut natives : Array String := #[]
  let mut conditional : Array String := #[]
  let mut ctxOfKey : Std.HashMap String Nat := {}
  let mut legalKeys : Std.HashSet String := {}
  -- the legal translated tests whose W check names the reduced program (their theorems are in the
  -- end-to-end files)
  let mut wE2E : Std.HashSet String := {}
  -- per test (project/name): its theorems, for the site
  let mut perTest : Std.HashMap String (List (String × Json)) := {}
  for (shard, progs) in srcShards do
    for (name, sp) in progs do
      let key := sp.project ++ "/" ++ name
      match basisOf.get? key with
      | some b =>
        if ["B0", "harness", "library", "helper"].contains b then
          let p := deriveProgram (canonOrder sp)
          let def_ := s!"s_{ident sp.project}_{name}"
          let thm := s!"legal_{ident sp.project}_{name}"
          let native := wBudgetNative.contains key
          let tac := if native then "(by native_decide)" else "(by decide +kernel)"
          let tags := if native then "[parse] [harness] [params] [native]" else "[parse] [harness] [params]"
          let doc := s!"/-- tests/{sp.project}/src/{name}.elm {tags} -/\n"
          -- the context of a one-module program, for step 10's pipeline (`endToEnd_of_ctx`)
          let ctxIdx? ← match p.modules with
            | [m] =>
              match importCtx B m.imports with
              | some C =>
                match ctxs.findIdx? (·.1 == m.imports) with
                | some i => pure (some i)
                | none => do
                  ctxs := ctxs.push (m.imports, C)
                  pure (some (ctxs.size - 1))
              | none => pure none
            | _ => pure none
          if wSkip.contains key then
            -- step 9's form, under D11
            let tagsC := "[parse] [harness] [principal] [params] [native]"
            let stmt := s!"theorem {thm} :\n    Stat.InferPrincipalFor Stat.Btest (Src.deriveProgram (Src.canonOrder {def_})) →\n    Stat.LegalProgram Stat.Btest {def_} :=\n"
            match p.modules, ctxIdx? with
            | [m], some idx =>
              let C := ctxs[idx]!.2
              if legal1B B m.imports C sp then
                nOne := nOne + 1
                ctxOfKey := ctxOfKey.insert key idx
                legalKeys := legalKeys.insert key
                conditional := conditional.push key
                natives := natives.push key
                perTest := perTest.insert key [("legal", Json.str thm), ("native", Json.bool true), ("conditional", Json.bool true)]
                thms := thms.push (sp.project, shard,
                  s!"/-- tests/{sp.project}/src/{name}.elm {tagsC} -/\n" ++ stmt ++ s!"  Stat.legal_of_infer1 ctx_{idx}_eq (by native_decide)\n")
              else failed := failed.push (key, diagnose1 B C sp m)
            | _, _ => failed := failed.push (key, "W is not run on it, and it is not a one-module program")
            continue
          if let some idx := ctxIdx? then ctxOfKey := ctxOfKey.insert key idx
          -- a translated test: W's check names the reduced program step 10's pipeline gives
          let e2e? : Option Mod.Reduced := match translOf.get? key with
            | some _ => match endToEnd B sp with
              | .ok r => if wCheck B sp (some r) then some r else none
              | .error _ => none
            | none => none
          if e2e?.isSome then
            if p.modules.length == 1 then nOne := nOne + 1 else nMany := nMany + 1
            legalKeys := legalKeys.insert key
            wE2E := wE2E.insert key
            if native then natives := natives.push key
          else if wCheck B sp none then
            if p.modules.length == 1 then nOne := nOne + 1 else nMany := nMany + 1
            legalKeys := legalKeys.insert key
            perTest := perTest.insert key [("legal", Json.str thm), ("native", Json.bool native)]
            thms := thms.push (sp.project, shard,
              doc ++ s!"theorem {thm} : Stat.LegalProgram Stat.Btest {def_} :=\n  Stat.legal_of_W (q := none) {tac}\n")
            if native then natives := natives.push key
          else failed := failed.push (key, diagnoseW B sp)
      | none => pure ()
  -- the context files
  let mut outs : Array Out := #[]
  let nCtxFiles := (ctxs.size + ctxPerFile - 1) / ctxPerFile
  for f in [0:nCtxFiles] do
    let mut body := header ++ "import StandardElmMech.Stat.Legal\nimport StandardElmMech.Stat.TestBasis\n\n" ++
      "namespace StandardElm\nopen StandardElm.Stat\nset_option maxRecDepth 100000\n\n"
    for i in [f * ctxPerFile : min ctxs.size ((f + 1) * ctxPerFile)] do
      let (imps, C) := ctxs[i]!
      body := body ++ s!"/-- The imports of a program, after the default ones. -/\ndef imps_{i} : List Src.BImport := {Print.imports imps}\n\n" ++
        s!"/-- The context these imports give (r:sm-module), in Btest. -/\ndef ctx_{i} : Stat.Ctx := {Print.ctx C}\n\n" ++
        s!"theorem ctx_{i}_eq : Stat.importCtx Stat.Btest imps_{i} = some ctx_{i} := by decide +kernel\n\n"
    outs := outs.push ⟨certsDir ++ ctxFile (f * ctxPerFile) ++ ".lean", body ++ "end StandardElm\n"⟩
  -- the theorem files, by project, shardSize theorems each
  let projects := (thms.toList.map (·.1)).eraseDups
  let mut certFiles : Array String := #[]
  -- Each theorem file imports the one before it, so that a build checks them one at a time and
  -- the summed memory of concurrent `lean` processes stays within the budget (conventions).
  for proj in projects do
    let ofProj := (thms.toList.filter (·.1 == proj))
    let chunks := (List.range ((ofProj.length + shardSize - 1) / shardSize)).map fun i => (ofProj.drop (i * shardSize)).take shardSize
    for i in [0:chunks.length] do
      let chunk := chunks[i]!
      let fname := upperCamel proj ++ pad2 (i + 1)
      let srcImports := (chunk.map (·.2.1)).eraseDups
      let prev := match certFiles.back? with
        | some f => s!"import StandardElmMech.Certs.{f}\n"
        | none => ""
      let body := header ++ prev ++ String.join (srcImports.map fun s => s!"import StandardElmMech.Generated.{s}\n") ++
        String.join ((List.range nCtxFiles).map fun f => s!"import StandardElmMech.Certs.{ctxFile (f * ctxPerFile)}\n") ++
        "import StandardElmMech.Stat.Complete.Discharge\n" ++
        "\n/-! The programs of this file are legal (plan step 9): each theorem runs W (plan step 11, milestone\n" ++
        "    (g), whose derivation is principal) and the checks in the kernel (or, tagged [native], compiled).\n" ++
        "    A theorem tagged [principal] is step 9's, under the hypothesis that the inference's derivation is\n" ++
        "    principal (D11). -/\n\n" ++
        "namespace StandardElm\nset_option maxRecDepth 100000\n\n" ++
        "\n".intercalate (chunk.map (·.2.2)) ++ "\nend StandardElm\n"
      outs := outs.push ⟨certsDir ++ fname ++ ".lean", body⟩
      certFiles := certFiles.push fname
  -- the refusals (milestone 9d)
  let ce ← IO.ofExcept (j.getObjValAs? (Array Json) "compileError")
  let mut progOf : Std.HashMap String (String × SProgram) := {}
  for (shard, progs) in srcShards do
    for (name, sp) in progs do
      progOf := progOf.insert (sp.project ++ "/" ++ name) (shard, sp)
  let mut refusals : Array (String × String) := #[]   -- (source shard, theorem text)
  let mut refuseFailed : Array (String × String) := #[]
  let mut refusedBy : Std.HashMap String Nat := {}
  for t in ce do
    let p := (t.getObjValAs? String "project").toOption.getD ""
    let n := (t.getObjValAs? String "name").toOption.getD ""
    let c := (t.getObjValAs? String "class").toOption.getD ""
    if refusedClasses.contains c then
      let key := p ++ "/" ++ n
      match progOf.get? key with
      | none => refuseFailed := refuseFailed.push (key, "not among the parsed programs")
      | some (shard, sp) =>
        let def_ := s!"s_{ident sp.project}_{n}"
        let doc := s!"/-- tests/{sp.project}/src/{n}.elm ({c}) [parse] [harness] [params] -/\n"
        let stmt := s!"theorem refuse_{ident sp.project}_{n} : ¬ Stat.LegalProgram Stat.Btest {def_} :=\n"
        if c == "syntactic" then
          -- step 8's theorem `nosyn_X` is about the set of modules (`¬ SynOKSet`, or `¬ ModulesSynOKSet`
          -- for a text without `main`) when the program fails as a set, else about its canonical order
          let hasMain := decide (sp.HasMain)
          let asSet := decide (SetFails sp) || decide (TwoCycle sp)
          let one := sp.modules.length == 1
          let lem? : Option String :=
            if asSet then some (if hasMain then "Stat.not_legal_of_syn" else "Stat.not_legal_of_modsyn")
            else if one then some (if hasMain then "Stat.not_legal_of_syn_one rfl" else "Stat.not_legal_of_modsyn_one rfl")
            else none
          match lem? with
          | some lem =>
            refusals := refusals.push (shard, doc ++ stmt ++ s!"  {lem} nosyn_{ident sp.project}_{n}\n")
            perTest := perTest.insert key [("refuse", Json.str s!"refuse_{ident sp.project}_{n}")]
            let k := (lem.splitOn " ").headD lem
            refusedBy := refusedBy.insert k ((refusedBy.getD k 0) + 1)
          | none =>
            refuseFailed := refuseFailed.push (key, "step 8 refuses the canonical order of its modules only, and it has several")
        else
          match refusers.find? (fun (_, d) => d B sp) with
          | some (lem, _) =>
            refusals := refusals.push (shard, doc ++ stmt ++ s!"  {lem} (by decide +kernel)\n")
            perTest := perTest.insert key [("refuse", Json.str s!"refuse_{ident sp.project}_{n}")]
            refusedBy := refusedBy.insert lem ((refusedBy.getD lem 0) + 1)
          | none => refuseFailed := refuseFailed.push (key, s!"no decider refuses it ({c})")
  let refChunks := (List.range ((refusals.size + shardSize - 1) / shardSize)).map fun i => (refusals.toList.drop (i * shardSize)).take shardSize
  for i in [0:refChunks.length] do
    let chunk := refChunks[i]!
    let fname := "Refusals" ++ pad2 (i + 1)
    let prev := match certFiles.back? with
      | some f => s!"import StandardElmMech.Certs.{f}\n"
      | none => ""
    let srcImports := (chunk.map (·.1)).eraseDups
    let body := header ++ prev ++ String.join (srcImports.map fun s => s!"import StandardElmMech.Generated.{s}\n") ++
      "import StandardElmMech.Generated.SynAll\nimport StandardElmMech.Stat.RefuseAll\nimport StandardElmMech.Stat.TestBasis\n" ++
      "\n/-! The programs of this file are not legal (plan step 9, milestone 9d): each theorem holds of\n" ++
      "    every derivation, so it needs no hypothesis about principality. -/\n\n" ++
      "namespace StandardElm\nset_option maxRecDepth 100000\n\n" ++
      "\n".intercalate (chunk.map (·.2)) ++ "\nend StandardElm\n"
    outs := outs.push ⟨certsDir ++ fname ++ ".lean", body⟩
    certFiles := certFiles.push fname
  -- step 10: the end-to-end theorems of the translated tests, after every legality theorem, one
  -- shard at a time (each imports the one before), so that a build stays within the memory budget
  let mut e2e : Array (List String × String) := #[]   -- (imports, theorem texts)
  let mut nSpec := 0
  let mut nMean := 0
  let mut nIdent := 0
  let mut nSpecNative := 0
  let mut e2eSkipped : Array (String × String) := #[]
  -- whether Part I's theorem t_X is native, decided as the commands that write it decide
  -- (`Program.proofNative`, Theorems.lean; `Prog.WorkerTest.taggedNative`, WorkerTheorems.lean)
  let mut tNativeOf : Std.HashMap String Bool := {}
  -- Part I spells the project `elm_core`, the manifest `elm-core`
  let keyOf (proj name : String) : String := proj.replace "_" "-" ++ "/" ++ name
  for p in allPrograms do tNativeOf := tNativeOf.insert (keyOf p.project p.name) p.proofNative
  for w in generatedWorkers do tNativeOf := tNativeOf.insert (keyOf w.prog.project w.prog.name) w.taggedNative
  for t in mts do
    if (t.getObjValAs? String "status").toOption != some "translated" then continue
    let p := (t.getObjValAs? String "project").toOption.getD ""
    let n := (t.getObjValAs? String "name").toOption.getD ""
    let key := p ++ "/" ++ n
    let gdef := (t.getObjValAs? String "def").toOption.getD ""
    let gshard := (t.getObjValAs? String "shard").toOption.getD ""
    let kind := (t.getObjValAs? String "kind").toOption.getD "view"
    let lean := (t.getObjValAs? String "lean").toOption.getD ""
    let hasNots := match t.getObjValAs? (Array Json) "checkNots" with
      | .ok a => !a.isEmpty
      | .error _ => false
    let src := (t.getObjVal? "src").toOption.getD Json.null
    let sdef := (src.getObjValAs? String "def").toOption.getD ""
    let sshard := (src.getObjValAs? String "shard").toOption.getD ""
    let suffix := (gdef.drop 2).toString
    if sdef == "" || !legalKeys.contains key then
      e2eSkipped := e2eSkipped.push (key, "no legality theorem")
      continue
    -- a worker's reduced part is its `Prog.WorkerTest`'s (flags type, kind), `w_X`; a view's is `g_X`'s
    let rdef := if kind == "view" then gdef else "w_" ++ suffix
    let native := staticBudgetNative.contains key
    let wNative := wBudgetNative.contains key
    let base := "[parse] [harness] [params]"
    let tags := if native then base ++ " [native]" else base
    let wTags := if wNative then base ++ " [native]" else base
    let proof := if native then "by native_decide"
      else match ctxOfKey.get? key with
        | some k => s!"Stat.endToEnd_of_ctx ctx_{k}_eq (by decide +kernel)"
        | none => "by decide +kernel"
    if native then nSpecNative := nSpecNative + 1
    let spec := s!"/-- tests/{p}/src/{n}.elm: Lean's elaboration, specialisation and erasure give the translator's reduced program {tags} -/\n" ++
      s!"theorem spec_{suffix} : Stat.endToEnd Stat.Btest {sdef} = .ok {rdef}.reduced :=\n  {proof}\n"
    nSpec := nSpec + 1
    let meaning := (lean.splitOn "meaning := false").length ≤ 1
    -- mean_ uses wcheck_ and Part I's t_: native when either is
    let tNative := tNativeOf.getD key ((t.getObjValAs? Bool "native").toOption.getD false)
    let inW := wE2E.contains key
    let cond := if inW then "" else "(h : Stat.D11For Stat.Btest (Stat.bareOf " ++ sdef ++ ")) "
    let condTag := if inW then "" else " [principal]"
    let wtac := if wNative then "by native_decide" else "by decide +kernel"
    let wcheck := if !inW then "" else
      s!"\n/-- tests/{p}/src/{n}.elm: W's derivation of the program (plan step 11, principal) passes Chapter 9's conditions and the further restrictions, and specialisation and erasure give the translator's reduced program {wTags} -/\n" ++
      s!"theorem wcheck_{suffix} : Stat.wCheck Stat.Btest {sdef} (some {rdef}.reduced) = true :=\n  {wtac}\n" ++
      s!"\n/-- tests/{p}/src/{n}.elm {wTags} -/\n" ++
      s!"theorem legal_{suffix} : Stat.LegalProgram Stat.Btest {sdef} :=\n  Stat.legal_of_W wcheck_{suffix}\n"
    let meanTags := (if wNative || tNative || !inW then base ++ " [native]" else base) ++ condTag
    let mean := if !meaning then "" else
      let tv := if kind == "view" then s!"Stat.value_of_viewChecks t_{suffix}"
        else
          let th := if hasNots then s!"t_{suffix}.1" else s!"t_{suffix}"
          s!"by obtain ⟨v, hv⟩ := Stat.value_of_holds {th}; exact ⟨v, hv⟩"
      let pf := if inW then s!"  Stat.programSem_of_wCheck wcheck_{suffix} ({tv})\n"
        else s!"  Stat.programSem_of_legal h spec_{suffix} legal_{suffix} ({tv})\n"
      s!"\n/-- tests/{p}/src/{n}.elm: r:p-program with both premises, in the test basis {meanTags} -/\n" ++
      s!"theorem mean_{suffix} {cond}:\n    ∃ τ PE v, Stat.ProgramSem Stat.Btest (Stat.bareOf {sdef}) (τ, PE, v) :=\n" ++ pf
    if meaning then nMean := nMean + 1
    let identTags := (if wNative || !inW then base ++ " [native]" else base) ++ condTag
    let identPf := if inW then s!"  Stat.ident_of_wCheck wcheck_{suffix}\n"
      else s!"  Stat.ident_of_spec' (by decide +kernel) h spec_{suffix}\n"
    let ident := s!"\n/-- tests/{p}/src/{n}.elm: the specialisation of the program is unique, and is the reduced program the translator wrote {identTags} -/\n" ++
      s!"theorem ident_{suffix} {cond}:\n    ∀ r, Stat.SpecOf Stat.Btest (Stat.bareOf {sdef}) r → r = {rdef}.reduced :=\n" ++ identPf
    nIdent := nIdent + 1
    if !inW then conditional := conditional.push key
    let prevT := perTest.getD key []
    let prevNative := match prevT.lookup "native" with
      | some (Json.bool b) => b
      | _ => false
    perTest := perTest.insert key ((prevT.filter (·.1 != "native")) ++
      (if inW then [("legal", Json.str s!"legal_{suffix}"), ("wcheck", Json.str s!"wcheck_{suffix}")] else []) ++
      [("spec", Json.str s!"spec_{suffix}"), ("mean", if meaning then Json.str s!"mean_{suffix}" else Json.null), ("ident", Json.str s!"ident_{suffix}"),
       ("native", Json.bool (prevNative || native || tNative || (inW && wNative)))])
    e2e := e2e.push ([s!"StandardElmMech.Generated.{gshard}", s!"StandardElmMech.Generated.Checks{gshard}",
      s!"StandardElmMech.Generated.{sshard}"], wcheck ++ "\n" ++ spec ++ mean ++ ident)
  let mut e2eFiles : Array String := #[]
  let e2eChunks := (List.range ((e2e.size + shardSize - 1) / shardSize)).map fun i => (e2e.toList.drop (i * shardSize)).take shardSize
  for i in [0:e2eChunks.length] do
    let chunk := e2eChunks[i]!
    let fname := "EndToEnd" ++ pad2 (i + 1)
    let prev := match e2eFiles.back? with
      | some f => s!"import StandardElmMech.Certs.{f}\n"
      | none => (String.join (certFiles.toList.map fun f => s!"import StandardElmMech.Certs.{f}\n"))
    let imps := (chunk.flatMap (·.1)).eraseDups
    let body := header ++ prev ++ String.join (imps.map fun m => s!"import {m}\n") ++
      "import StandardElmMech.Stat.Pipeline\nimport StandardElmMech.Stat.ModuleStep\nimport StandardElmMech.Stat.Complete.Discharge\n" ++
      "\n/-! Plan steps 10 and 11: for each translated test, W's derivation of the program (principal,\n" ++
      "    plan step 11) passes the checks and gives the reduced program the translator wrote (`wcheck_`), so\n" ++
      "    the program is legal (`legal_`), its specialisation is that program (`ident_`), and it has a meaning\n" ++
      "    by r:p-program with both premises (`mean_`), without hypothesis; and Lean's pipeline with step 9's\n" ++
      "    inference gives the same reduced program (`spec_`). -/\n\n" ++
      "namespace StandardElm\nset_option maxRecDepth 100000\n\n" ++
      "\n".intercalate (chunk.map (·.2)) ++ "\nend StandardElm\n"
    outs := outs.push ⟨certsDir ++ fname ++ ".lean", body⟩
    e2eFiles := e2eFiles.push fname
  certFiles := certFiles ++ e2eFiles
  outs := outs.push ⟨certsDir ++ "CertsAll.lean", header ++
    String.join (certFiles.toList.map fun f => s!"import StandardElmMech.Certs.{f}\n")⟩
  -- report
  let refuseSummary := s!"refused: {refusals.size} ({", ".intercalate (refusedBy.toList.map fun (l, k) => s!"{l} {k}")}), {refuseFailed.size} not refused"
  let e2eSummary := s!"end to end: {nSpec} spec_ theorems ({nSpecNative} by native_decide), {nMean} mean_ theorems, {nIdent} ident_ theorems, {e2eSkipped.size} translated tests skipped"
  let summary := s!"static semantics: {nOne + nMany} legal ({nOne} of one module, {nMany} of several), {failed.size} without a theorem, {ctxs.size} contexts, {natives.size} by native_decide, {conditional.size} conditional on D11"
  let report := Json.mkObj [
    ("generatedBy", Json.str "lake exe certify (Certify.lean)"),
    ("summary", Json.str summary),
    ("legal", Json.num (nOne + nMany)),
    ("contexts", Json.num ctxs.size),
    ("native", Json.arr (natives.map Json.str)),
    ("specNative", Json.arr ((staticBudgetNative.filter fun k => legalKeys.contains k && translOf.contains k).toArray.map Json.str)),
    ("conditional", Json.arr (conditional.toList.eraseDups.toArray.map Json.str)),
    ("refused", Json.num refusals.size),
    ("tests", Json.mkObj ((perTest.toList.toArray.qsort (fun a b => a.1 < b.1)).toList.map fun (k, fs) => (k, Json.mkObj fs))),
    ("endToEnd", Json.str e2eSummary),
    ("refusedSummary", Json.str refuseSummary),
    ("notRefused", Json.arr (refuseFailed.map fun (k, r) => Json.mkObj [("test", Json.str k), ("reason", Json.str r)])),
    ("failed", Json.arr (failed.map fun (k, r) => Json.mkObj [("test", Json.str k), ("reason", Json.str r)]))]
  outs := outs.push ⟨"../static-report.json", report.pretty ++ "\n"⟩
  IO.println summary
  IO.println refuseSummary
  IO.println e2eSummary
  for (k, r) in e2eSkipped.toList do IO.println s!"  end to end skipped: {k}: {r}"
  for (k, r) in refuseFailed.toList do IO.println s!"  not refused: {k}: {r}"
  for (k, r) in failed.toList.take 50 do IO.println s!"  {k}: {r}"
  -- shards an earlier run wrote that this one does not (`<Name><nn>.lean`): removed
  let written := outs.map (·.path)
  let mut extra : Array String := #[]
  for e in (← (System.FilePath.mk certsDir).readDir) do
    let n := e.fileName
    let cs := n.toList
    let stem := cs.take (cs.length - 5)
    if n.endsWith ".lean" && stem.length ≥ 2 && (stem.drop (stem.length - 2)).all Char.isDigit &&
        !written.contains (certsDir ++ n) then
      extra := extra.push (certsDir ++ n)
  if check then
    let mut stale := extra.size
    for o in outs do
      let cur ← (IO.FS.readFile o.path).toBaseIO
      match cur with
      | .ok s => if s != o.body then stale := stale + 1
      | .error _ => stale := stale + 1
    if stale == 0 then IO.println "Certs/ is up to date." else IO.println s!"{stale} files would change; run `lake exe certify`."
    return (if stale == 0 then 0 else 1)
  else
    IO.FS.createDirAll certsDir
    for o in outs do IO.FS.writeFile o.path o.body
    for f in extra do IO.FS.removeFile f
    IO.println s!"written: {outs.size} files, removed: {extra.size}"
    return 0
