/-
  `lake exe certify` (plan step 9, section 13): runs the inference (W, compiled) over every program
  step 7 classes as a compile-success test with basis B0, harness, library or helper, and writes the
  per-test theorems to `StandardElmMech/Certs/`:

  - `Ctx_<name>.lean`: the context of one list of imports of a one-module program, as a literal, with
    the lemma that the imports give it (`ctx_<name>_eq`, by the kernel); `<name>` is a hash of the
    printed imports, so the file depends on them only. The W checks of the programs with those imports
    read it (`Stat.wCheck_of_ctx`), so the kernel computes each context once, not once per test;
  - `Legal_<Project>_<Bucket>.lean`: for each program W and the checks accept that the translator does
    not translate, the theorem `legal_<project>_<Test>`, proved by the kernel running W (plan step 11,
    milestone (g)) and the checks;
  - `Refusals_<Project>_<Bucket>.lean`: the refusal theorems `refuse_<project>_<Test>`;
  - `EndToEnd_<Project>_<Bucket>.lean`: for each translated test, `wcheck_X` (W's derivation checked,
    with the reduced program the translator wrote: the one run of the inference and the
    specialisation in the kernel), and from it, all without hypothesis, `legal_X`, `spec_X` (Lean's
    pipeline with W gives the reduced program), `mean_X` and `ident_X`;
  - `CertsAll.lean`, importing them.

  The shards (plan step 11, after milestone (g)): a test's file is fixed by its name (`bucketOf`: the
  alphabetical bucket of `project/Test` in a fixed list of bounds), so adding or removing a test
  changes only its own file; and no shard imports another, each importing only the Generated and Stat
  modules its theorems need, so that Lake rebuilds only the shards whose text or imports change and can
  check several at once. `scripts/verify.sh` bounds how many (`LEAN_NUM_THREADS`, conventions, "Memory
  budget").

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
def generatedDir : String := "StandardElmMech/Generated/"

def upperCamel (s : String) : String :=
  "".intercalate ((s.splitOn "-").map fun w => w.capitalize)

def ident (s : String) : String := s.replace "-" "_"

/-! ## The shards -/

/-- The bounds of the alphabetical buckets of the end-to-end files, as keys `project/Test` (in the
    order of `String`, by code point: `elm-core/` before `elm/`). A test belongs to the bucket of the
    last bound that is not after its key (`bucketOf`), and the bucket's file is named after its bound:
    `elm/CaseF` gives `EndToEnd_Elm_CaseF.lean`, `elm/` gives `EndToEnd_Elm.lean`. The bounds are fixed:
    adding or removing a test changes its own bucket's file only. A bucket that grows too large (in
    time or memory) is split by adding a bound, which changes that bucket's file and adds one.
    Chosen on 2026-11-13 for shards of similar kernel time, each within the memory budget (the
    largest resident set of one shard's `lean` process at most 6.3 GB); `elm/Ap` and `elm/CombinatorL`
    hold one test each, AppendTypeSplitTest (6.04 GB alone) and CombinatorListStringTest (6.19 GB),
    so that no other theorem adds to their peak. -/
def e2eBounds : List String :=
  ["elm-core/", "elm-core/CompareI", "elm-core/CoreIssue115", "elm-core/FloatD", "elm-core/FloatSu",
   "elm-core/NotEqualBoolP", "elm-core/StandardA42", "elm-core/TaskOnErrorS",
   "elm/", "elm/Ap", "elm/As", "elm/CaseF", "elm/CaseS", "elm/CharU", "elm/CombinatorL", "elm/CombinatorP",
   "elm/CombinatorSP", "elm/CompilerIssue22",
   "elm/CovTailRecPairParameters", "elm/EmbeddedNo", "elm/Fli", "elm/ImportE", "elm/InfixPrecO",
   "elm/LetN", "elm/LetNumberLo", "elm/Li", "elm/M", "elm/PartialAppCh", "elm/PortEchoN",
   "elm/RecordAccessorFunctionT", "elm/SingleCtorPairBoolF", "elm/StandardL", "elm/TailRecT"]

/-- The bounds of the files of `legal_` theorems of the programs the translator does not translate.
    The four largest programs, whose W check `native_decide` runs in Lean's interpreter (about 15
    minutes together, 2026-11-13), have a file each, so that a build checks them at once. -/
def legalBounds : List String :=
  ["elm-core/", "elm/", "elm/P", "elm/W", "elm/WideRecord1", "elm/WideRecord6", "elm/WideRecordD",
   "elm/WideRecordG"]

/-- The bounds of the files of refusals. -/
def refuseBounds : List String :=
  ["elm-core/", "elm/", "elm/CompilerIssue208", "elm/L", "elm/TypeMismatchArgumentT", "elm/TypeMismatchFu",
   "elm/TypeMismatchNumberPipedIntoN", "elm/TypeMismatchSelfAppliedArgumentAgainstARigidV",
   "elm/TypeMismatchUpdateV"]

/-- The bucket of a key: the last bound that is not after it, or the first bound. -/
def bucketOf (bounds : List String) (key : String) : String :=
  (bounds.filter fun b => decide (b ≤ key)).getLast?.getD (bounds.headD "")

/-- The module name of a bucket's file: `EndToEnd` and `elm/CaseF` give `EndToEnd_Elm_CaseF`. -/
def shardName (kind bound : String) : String :=
  match bound.splitOn "/" with
  | [proj, pre] => kind ++ "_" ++ upperCamel proj ++ (if pre.isEmpty then "" else "_" ++ pre)
  | _ => kind

/-- The programs whose `spec_` theorem about step 10's pipeline with step 9's inference
    (`Stat.endToEnd`) breaks the memory budget when the kernel runs it (conventions, "Memory budget":
    above 6.5 GB of resident set for the one `lean` process, measured one theorem per process on
    2026-11-12). Since 2026-11-13 a translated test's `spec_` is about the pipeline with W and follows
    from its `wcheck_`; this list is used only for a translated test whose W check does not name the
    reduced program (none today), whose `spec_` keeps step 10's form, proved by `native_decide` and
    tagged `[native]`. -/
def staticBudgetNative : List String :=
  ["elm/WideClosureArity300Test",             -- above 8 GB
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
    through their shard's build), with a margin: above 6.3 GB. Their `wcheck_`/`legal_` theorems, and the
    `spec_`, `ident_` and `mean_` theorems that use them, are proved by `native_decide` (the `wcheck_`
    or `legal_` theorem) and tagged `[native]`. Since the W check reads the context of the imports
    from `Certs/Ctx_*.lean` (`Stat.wCheck_of_ctx`), four programs of the first list are back within the
    budget and checked by the kernel (one theorem per process, 2026-11-13): WideCtorField24Test 5.71 GB,
    FloatEdgeTest 5.82 GB, AppendTypeSplitTest 6.04 GB, CombinatorListStringTest 6.19 GB (each a one-module
    program whose imports give a context, so the check always reads it). The others still break it with
    the context given (WideRecord33Test 6.59 GB, WideClosureSat26Test 6.91 GB, the rest killed at 6.5 GB). -/
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
   "elm/WideRecord33Test"]                    -- 7.20 GB

/-- Programs W does not elaborate in reasonable time even compiled: their `legal_` theorem keeps step
    9's form, under D11 (`InferPrincipalFor`), tagged `[principal]`. None since 2026-11-13: the only one,
    CompilerIssue2281LongLineListTest (a list literal of 22,000 elements on one line), tests a
    compiler's column limit, which the book does not speak of, and is no longer tagged `elm-spec`. -/
def wSkip : List String := []

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

/-- FNV-1a (32 bits) of a string, in eight hex digits: the name of the context of a list of imports. -/
def hashName (s : String) : String :=
  let h : UInt32 := s.toUTF8.foldl (fun h b => (h ^^^ b.toUInt32) * 16777619) 2166136261
  let d := String.ofList (Nat.toDigits 16 h.toNat)
  "".pushn '0' (8 - d.length) ++ d

/-- A theorem (or several) of one test, for a shard: the test's key, the modules the text needs, and
    the text. -/
structure Entry where
  key : String
  imports : List String
  text : String

/-- The shard files of one kind: the entries grouped by bucket, each file importing the union of its
    entries' modules (sorted), its theorems in the order of their keys. -/
def shardFiles (kind : String) (bounds : List String) (doc : String) (es : Array Entry) : List (String × String) :=
  let sorted := es.qsort (fun a b => a.key < b.key)
  let names := (sorted.toList.map fun e => shardName kind (bucketOf bounds e.key)).eraseDups
  names.map fun n =>
    let of := sorted.toList.filter fun e => shardName kind (bucketOf bounds e.key) == n
    let imps := ((of.flatMap (·.imports)).eraseDups.toArray.qsort (· < ·)).toList
    (n, header ++ String.join (imps.map fun m => s!"import {m}\n") ++ "\n" ++ doc ++ "\n" ++
      "namespace StandardElm\nset_option maxRecDepth 100000\n\n" ++
      "\n".intercalate (of.map (·.text)) ++ "\nend StandardElm\n")

/-- The Syn shard (`Generated/Syn<Bucket>.lean`, whose `#syn_theorems` states `nosyn_X`) of each source
    shard, from the Syn shards' imports. -/
def synShardOf : IO (Std.HashMap String String) := do
  let mut m : Std.HashMap String String := {}
  for e in (← (System.FilePath.mk generatedDir).readDir) do
    let n := e.fileName
    if !(n.startsWith "Syn" && n.endsWith ".lean") || n == "SynAll.lean" then continue
    let stem := n.replace ".lean" ""
    for l in (← IO.FS.readFile e.path).splitOn "\n" do
      if l.startsWith "import StandardElmMech.Generated.Src" then
        m := m.insert (l.replace "import StandardElmMech.Generated." "") stem
  return m

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
  let mut translated : Std.HashSet String := {}
  for t in mts do
    if (t.getObjValAs? String "status").toOption != some "translated" then continue
    let p := (t.getObjValAs? String "project").toOption.getD ""
    let n := (t.getObjValAs? String "name").toOption.getD ""
    let src := (t.getObjVal? "src").toOption.getD Json.null
    if (src.getObjValAs? String "def").toOption.getD "" != "" then translated := translated.insert (p ++ "/" ++ n)
  let B := Btest
  let discharge := "StandardElmMech.Stat.Complete.Discharge"
  let mut legals : Array Entry := #[]
  let mut failed : Array (String × String) := #[]
  let mut nOne := 0
  let mut nMany := 0
  let mut natives : Array String := #[]
  let mut conditional : Array String := #[]
  let mut legalKeys : Std.HashSet String := {}
  -- the legal translated tests whose W check names the reduced program the pipeline with W gives
  -- (their theorems are in the end-to-end files)
  let mut wE2E : Std.HashSet String := {}
  -- per test (project/name): its theorems, for the site
  let mut perTest : Std.HashMap String (List (String × Json)) := {}
  -- the contexts of the imports of one-module programs, by name (`hashName` of the printed imports),
  -- each in its own file `Certs/Ctx_<name>.lean`: a test's W check reads its context from there
  -- (`wCheck_of_ctx`), so the kernel does not compute it per test
  let mut ctxs : Std.HashMap String (List BImport × Ctx) := {}
  -- per test whose W check reads a context: the context's name
  let mut ctxOfKey : Std.HashMap String String := {}
  for (shard, progs) in srcShards do
    for (name, sp) in progs do
      let key := sp.project ++ "/" ++ name
      match basisOf.get? key with
      | some b =>
        if ["B0", "harness", "library", "helper"].contains b then
          let p := deriveProgram (canonOrder sp)
          let def_ := s!"s_{ident sp.project}_{name}"
          let suffix := s!"{ident sp.project}_{name}"
          let thm := s!"legal_{suffix}"
          let native := wBudgetNative.contains key
          let tac := if native then "(by native_decide)" else "(by decide +kernel)"
          let tags := if native then "[parse] [harness] [params] [native]" else "[parse] [harness] [params]"
          let doc := s!"/-- tests/{sp.project}/src/{name}.elm {tags} -/\n"
          let srcImp := s!"StandardElmMech.Generated.{shard}"
          -- the program's context, when it has one module whose imports give one
          let ctx? : Option (String × List BImport × Ctx) := match p.modules with
            | [m] => (importCtx B m.imports).map fun C => (hashName (Print.imports m.imports), m.imports, C)
            | _ => none
          if let some (h, imps, C) := ctx? then
            match ctxs.get? h with
            | some (imps', _) =>
              if imps' != imps then
                IO.eprintln s!"two lists of imports have the context name {h}: change hashName"
                return 1
            | none => ctxs := ctxs.insert h (imps, C)
          if wSkip.contains key then
            -- step 9's form, under D11, with the context of the program's imports
            let tagsC := "[parse] [harness] [principal] [params] [native]"
            let stmt := s!"theorem {thm} :\n    Stat.InferPrincipalFor Stat.Btest (Src.deriveProgram (Src.canonOrder {def_})) →\n    Stat.LegalProgram Stat.Btest {def_} :=\n"
            match p.modules, ctx? with
            | [m], some (h, _, C) =>
                if legal1B B m.imports C sp then
                  nOne := nOne + 1
                  legalKeys := legalKeys.insert key
                  conditional := conditional.push key
                  natives := natives.push key
                  perTest := perTest.insert key [("legal", Json.str thm), ("native", Json.bool true), ("conditional", Json.bool true)]
                  legals := legals.push ⟨key, [srcImp, discharge, s!"StandardElmMech.Certs.Ctx_{h}"],
                    s!"/-- tests/{sp.project}/src/{name}.elm {tagsC} -/\n" ++ stmt ++ s!"  Stat.legal_of_infer1 ctx_{h}_eq (by native_decide)\n"⟩
                else failed := failed.push (key, diagnose1 B C sp m)
            | [_], none => failed := failed.push (key, "the imports give no context")
            | _, _ => failed := failed.push (key, "W is not run on it, and it is not a one-module program")
            continue
          -- a translated test: W's check names the reduced program the pipeline with W gives
          let r? : Option Mod.Reduced :=
            if translated.contains key then
              match endToEndW B sp with
              | .ok r => some r
              | .error _ => none
            else none
          -- the W check reads the program's context when the check with it given succeeds (compiled;
          -- `wCheck_of_ctx` makes it the check, so the check is not run again)
          let viaIn : Bool := if native then false else
            match ctx? with
            | some (_, imps, C) => wCheckIn B imps C sp r?
            | none => false
          let e2e? : Option Mod.Reduced := match r? with
            | some r => if viaIn || wCheck B sp (some r) then some r else none
            | none => none
          let viaCtx? : Option String := if viaIn then ctx?.map (·.1) else none
          if let some h := viaCtx? then ctxOfKey := ctxOfKey.insert key h
          if e2e?.isSome then
            if p.modules.length == 1 then nOne := nOne + 1 else nMany := nMany + 1
            legalKeys := legalKeys.insert key
            wE2E := wE2E.insert key
            if native then natives := natives.push key
          else if (r?.isNone && viaIn) || wCheck B sp none then
            if p.modules.length == 1 then nOne := nOne + 1 else nMany := nMany + 1
            legalKeys := legalKeys.insert key
            perTest := perTest.insert key [("legal", Json.str thm), ("native", Json.bool native)]
            let (pf, imps) := match viaCtx? with
              | some h => (s!"(Stat.wCheck_of_ctx ctx_{h}_eq (by decide +kernel))", [s!"StandardElmMech.Certs.Ctx_{h}"])
              | none => (tac, [])
            legals := legals.push ⟨key, [srcImp, discharge] ++ imps,
              doc ++ s!"theorem {thm} : Stat.LegalProgram Stat.Btest {def_} :=\n  Stat.legal_of_W (q := none) {pf}\n"⟩
            if native then natives := natives.push key
          else failed := failed.push (key, diagnoseW B sp)
      | none => pure ()
  let mut outs : Array Out := #[]
  let mut certFiles : Array String := #[]
  -- the context files (only those a theorem reads)
  let used := (ctxOfKey.toList.map (·.2)).eraseDups ++ (if wSkip.isEmpty then [] else ctxs.toList.map (·.1))
  for (h, imps, C) in (ctxs.toList.filter (fun (h, _) => used.contains h)).toArray.qsort (fun a b => a.1 < b.1) do
    let n := s!"Ctx_{h}"
    outs := outs.push ⟨certsDir ++ n ++ ".lean", header ++ "import StandardElmMech.Stat.Legal\nimport StandardElmMech.Stat.TestBasis\n\n" ++
      "namespace StandardElm\nopen StandardElm.Stat\nset_option maxRecDepth 100000\n\n" ++
      s!"/-- The imports of a program, after the default ones. -/\ndef imps_{h} : List Src.BImport := {Print.imports imps}\n\n" ++
      s!"/-- The context these imports give (r:sm-module), in Btest. -/\ndef ctx_{h} : Stat.Ctx := {Print.ctx C}\n\n" ++
      s!"theorem ctx_{h}_eq : Stat.importCtx Stat.Btest imps_{h} = some ctx_{h} := by decide +kernel\n\n" ++
      "end StandardElm\n"⟩
    certFiles := certFiles.push n
  for (n, body) in shardFiles "Legal" legalBounds
      ("/-! The programs of this file are legal (plan step 9): each theorem runs W (plan step 11, milestone\n" ++
       "    (g), whose derivation is principal) and the checks in the kernel (or, tagged [native], compiled).\n" ++
       "    A theorem tagged [principal] is step 9's, under the hypothesis that the inference's derivation is\n" ++
       "    principal (D11). -/\n") legals do
    outs := outs.push ⟨certsDir ++ n ++ ".lean", body⟩
    certFiles := certFiles.push n
  -- the refusals (milestone 9d)
  let ce ← IO.ofExcept (j.getObjValAs? (Array Json) "compileError")
  let mut progOf : Std.HashMap String (String × SProgram) := {}
  for (shard, progs) in srcShards do
    for (name, sp) in progs do
      progOf := progOf.insert (sp.project ++ "/" ++ name) (shard, sp)
  let synOf ← synShardOf
  let refuseBase := ["StandardElmMech.Stat.RefuseAll", "StandardElmMech.Stat.TestBasis", discharge]
  let mut refusals : Array Entry := #[]
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
        let srcImp := s!"StandardElmMech.Generated.{shard}"
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
            let synImp := match synOf.get? shard with
              | some s => s!"StandardElmMech.Generated.{s}"
              | none => "StandardElmMech.Generated.SynAll"
            refusals := refusals.push ⟨key, srcImp :: synImp :: refuseBase, doc ++ stmt ++ s!"  {lem} nosyn_{ident sp.project}_{n}\n"⟩
            perTest := perTest.insert key [("refuse", Json.str s!"refuse_{ident sp.project}_{n}")]
            let k := (lem.splitOn " ").headD lem
            refusedBy := refusedBy.insert k ((refusedBy.getD k 0) + 1)
          | none =>
            refuseFailed := refuseFailed.push (key, "step 8 refuses the canonical order of its modules only, and it has several")
        else
          match refusers.find? (fun (_, d) => d B sp) with
          | some (lem, _) =>
            refusals := refusals.push ⟨key, srcImp :: refuseBase, doc ++ stmt ++ s!"  {lem} (by decide +kernel)\n"⟩
            perTest := perTest.insert key [("refuse", Json.str s!"refuse_{ident sp.project}_{n}")]
            refusedBy := refusedBy.insert lem ((refusedBy.getD lem 0) + 1)
          | none => refuseFailed := refuseFailed.push (key, s!"no decider refuses it ({c})")
  for (n, body) in shardFiles "Refusals" refuseBounds
      ("/-! The programs of this file are not legal (plan step 9, milestone 9d): each theorem holds of\n" ++
       "    every derivation, so it needs no hypothesis about principality. -/\n") refusals do
    outs := outs.push ⟨certsDir ++ n ++ ".lean", body⟩
    certFiles := certFiles.push n
  -- steps 10 and 11: the end-to-end theorems of the translated tests
  let mut e2e : Array Entry := #[]
  let mut nSpec := 0
  let mut nMean := 0
  let mut nIdent := 0
  let mut nSpecNative := 0
  let mut nSpecOfNative := 0
  let mut specNative : Array String := #[]
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
    let wNative := wBudgetNative.contains key
    let base := "[parse] [harness] [params]"
    let wTags := if wNative then base ++ " [native]" else base
    let inW := wE2E.contains key
    -- spec_: with W, from wcheck_ (no second run of the inference); otherwise step 10's form, the
    -- kernel running step 9's pipeline (under D11 for ident_ and mean_)
    let native := !inW && staticBudgetNative.contains key
    let specTags := if (inW && wNative) || native then base ++ " [native]" else base
    if native then nSpecNative := nSpecNative + 1
    if inW && wNative then nSpecOfNative := nSpecOfNative + 1
    if (inW && wNative) || native then specNative := specNative.push key
    let spec := if inW then
        s!"/-- tests/{p}/src/{n}.elm: Lean's pipeline with W (derived forms, W, the checks, specialisation and erasure) gives the translator's reduced program {specTags} -/\n" ++
        s!"theorem spec_{suffix} : Stat.endToEndW Stat.Btest {sdef} = .ok {rdef}.reduced :=\n  Stat.endToEndW_of_wCheck wcheck_{suffix}\n"
      else
        s!"/-- tests/{p}/src/{n}.elm: Lean's elaboration (step 9's inference), specialisation and erasure give the translator's reduced program {specTags} -/\n" ++
        s!"theorem spec_{suffix} : Stat.endToEnd Stat.Btest {sdef} = .ok {rdef}.reduced :=\n  {if native then "by native_decide" else "by decide +kernel"}\n"
    nSpec := nSpec + 1
    let meaning := (lean.splitOn "meaning := false").length ≤ 1
    -- mean_ uses wcheck_ and Part I's t_: native when either is
    let tNative := tNativeOf.getD key ((t.getObjValAs? Bool "native").toOption.getD false)
    let cond := if inW then "" else "(h : Stat.D11For Stat.Btest (Stat.bareOf " ++ sdef ++ ")) "
    let condTag := if inW then "" else " [principal]"
    let ctxH? := ctxOfKey.get? key
    let wtac := if wNative then "by native_decide" else match ctxH? with
      | some h => s!"Stat.wCheck_of_ctx ctx_{h}_eq (by decide +kernel)"
      | none => "by decide +kernel"
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
    e2e := e2e.push ⟨key, [s!"StandardElmMech.Generated.{gshard}", s!"StandardElmMech.Generated.Checks{gshard}",
      s!"StandardElmMech.Generated.{sshard}", discharge] ++ (match ctxH? with
        | some h => if inW then [s!"StandardElmMech.Certs.Ctx_{h}"] else []
        | none => []), wcheck ++ "\n" ++ spec ++ mean ++ ident⟩
  for (n, body) in shardFiles "EndToEnd" e2eBounds
      ("/-! Plan steps 10 and 11: for each translated test, W's derivation of the program (principal,\n" ++
       "    plan step 11) passes the checks and gives the reduced program the translator wrote (`wcheck_`: the\n" ++
       "    one run of the inference and the specialisation in the kernel), so the program is legal (`legal_`),\n" ++
       "    Lean's pipeline with W gives that program (`spec_`), its specialisation is that program (`ident_`),\n" ++
       "    and it has a meaning by r:p-program with both premises (`mean_`), without hypothesis. -/\n") e2e do
    outs := outs.push ⟨certsDir ++ n ++ ".lean", body⟩
    certFiles := certFiles.push n
  outs := outs.push ⟨certsDir ++ "CertsAll.lean", header ++
    String.join (certFiles.toList.map fun f => s!"import StandardElmMech.Certs.{f}\n")⟩
  -- report
  let refuseSummary := s!"refused: {refusals.size} ({", ".intercalate (refusedBy.toList.map fun (l, k) => s!"{l} {k}")}), {refuseFailed.size} not refused"
  let e2eSummary := s!"end to end: {nSpec} spec_ theorems ({nSpecNative} by native_decide, {nSpecOfNative} from a wcheck_ by native_decide), {nMean} mean_ theorems, {nIdent} ident_ theorems, {e2eSkipped.size} translated tests skipped"
  let summary := s!"static semantics: {nOne + nMany} legal ({nOne} of one module, {nMany} of several), {failed.size} without a theorem, {natives.size} by native_decide, {conditional.size} conditional on D11"
  let shardSummary := s!"shards: {certFiles.size} ({(certFiles.filter (·.startsWith "Ctx_")).size} Ctx_, {(certFiles.filter (·.startsWith "Legal_")).size} Legal_, {(certFiles.filter (·.startsWith "Refusals_")).size} Refusals_, {(certFiles.filter (·.startsWith "EndToEnd_")).size} EndToEnd_); no shard imports another but for the Ctx_ files of its tests' imports"
  let report := Json.mkObj [
    ("generatedBy", Json.str "lake exe certify (Certify.lean)"),
    ("summary", Json.str summary),
    ("legal", Json.num (nOne + nMany)),
    ("native", Json.arr (natives.map Json.str)),
    ("specNative", Json.arr ((specNative.qsort (· < ·)).map Json.str)),
    ("conditional", Json.arr (conditional.toList.eraseDups.toArray.map Json.str)),
    ("refused", Json.num refusals.size),
    ("tests", Json.mkObj ((perTest.toList.toArray.qsort (fun a b => a.1 < b.1)).toList.map fun (k, fs) => (k, Json.mkObj fs))),
    ("endToEnd", Json.str e2eSummary),
    ("refusedSummary", Json.str refuseSummary),
    ("shards", Json.str shardSummary),
    ("notRefused", Json.arr (refuseFailed.map fun (k, r) => Json.mkObj [("test", Json.str k), ("reason", Json.str r)])),
    ("failed", Json.arr (failed.map fun (k, r) => Json.mkObj [("test", Json.str k), ("reason", Json.str r)]))]
  outs := outs.push ⟨"../static-report.json", report.pretty ++ "\n"⟩
  IO.println summary
  IO.println refuseSummary
  IO.println e2eSummary
  IO.println shardSummary
  for (k, r) in e2eSkipped.toList do IO.println s!"  end to end skipped: {k}: {r}"
  for (k, r) in refuseFailed.toList do IO.println s!"  not refused: {k}: {r}"
  for (k, r) in failed.toList.take 50 do IO.println s!"  {k}: {r}"
  -- files an earlier run wrote that this one does not (any file of Certs/ that starts with the
  -- header): removed
  let written := outs.map (·.path)
  let mut extra : Array String := #[]
  for e in (← (System.FilePath.mk certsDir).readDir) do
    let n := e.fileName
    if n.endsWith ".lean" && !written.contains (certsDir ++ n) then
      if (← IO.FS.readFile e.path).startsWith header then extra := extra.push (certsDir ++ n)
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
    -- a file whose text is unchanged is not written again, so that its time stamp stays
    let mut changed := 0
    for o in outs do
      let cur ← (IO.FS.readFile o.path).toBaseIO
      let same := match cur with
        | .ok s => s == o.body
        | .error _ => false
      if !same then
        IO.FS.writeFile o.path o.body
        changed := changed + 1
    for f in extra do IO.FS.removeFile f
    IO.println s!"files: {outs.size} ({changed} written, the others unchanged), removed: {extra.size}"
    return 0
