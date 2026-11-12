/-
  A Standard Definition of Elm? Mechanisation: the per-test theorems of the syntactic restrictions,
  plan step 8. `#syn_theorems srcShards` evaluates, for every written program, whether it meets the
  AST-decidable restrictions, and adds a theorem the kernel checks:

  * `syn_<project>_<Test> : Src.SynOKSet s_<project>_<Test>` when it meets them (the program as
    written, the set of its modules: the canonical sequence is a witness);
  * `nosyn_<project>_<Test> : ¬ Src.SynOKSet s_<project>_<Test>` when it does not, whatever the
    order of its modules (Src/SynSet.lean: a module restriction, res:modules-program, an import
    of no module, or two modules importing each other), and `nosyn_<project>_<Test>_<slug>` for
    each restriction the canonical sequence breaks;
  * for a text whose main module declares no `main` (a module tested alone), the same with
    `Src.ModulesSynOKSet`, every restriction but res:program-main.

  Each by `decide +kernel`. Every theorem trusts the parser ([parse]): the source syntax is
  elm-syntax's tree.
-/
import Lean
import StandardElmMech.Src.Restrictions
import StandardElmMech.Src.SynSet

namespace StandardElm.Src
open Lean Elab Command

/-- The module restrictions: Lean name and the slug of its label. -/
def moduleRules : List (String × String) :=
  [("RowLabelsDistinct", "core_row_labels_distinct"), ("RecordUpdateForm", "core_record_update_form"),
   ("BindingSiteDistinct", "core_binding_site_distinct"), ("NoShadowing", "core_no_shadowing"),
   ("NoFloatPattern", "core_no_float_pattern"), ("LetRecursion", "core_let_recursion"),
   ("PortsInPortModule", "modules_ports"), ("ImportAlias", "modules_import_alias"),
   ("BasicsQualifier", "modules_basics_qualifier"), ("NoOperatorExposing", "modules_no_operator_exposing"),
   ("HeaderExposing", "modules_header_exposing"), ("ExposingDistinct", "modules_exposing_distinct"),
   ("NoTopPattern", "modules_no_top_pattern"), ("ValuesDistinct", "modules_values_distinct"),
   ("TypesDistinct", "modules_types_distinct"), ("ConstructorsDistinct", "modules_constructors_distinct"),
   ("TopNoShadowing", "modules_no_shadowing"), ("TyVarSeqDistinct", "modules_tyvarseq_distinct"),
   ("CustomTypeTyVars", "modules_custom_type_tyvars"), ("AliasTyVars", "modules_alias_tyvars"),
   ("AliasNotRecursive", "modules_alias_not_recursive"), ("ValueRecursion", "modules_value_recursion")]

def moduleDecider : String → SModule → Bool
  | "RowLabelsDistinct", m => decide (RowLabelsDistinct m)
  | "RecordUpdateForm", m => decide (RecordUpdateForm m)
  | "BindingSiteDistinct", m => decide (BindingSiteDistinct m)
  | "NoShadowing", m => decide (NoShadowing m)
  | "NoFloatPattern", m => decide (NoFloatPattern m)
  | "LetRecursion", m => decide (LetRecursion m)
  | "PortsInPortModule", m => decide (PortsInPortModule m)
  | "ImportAlias", m => decide (ImportAlias m)
  | "BasicsQualifier", m => decide (BasicsQualifier m)
  | "NoOperatorExposing", m => decide (NoOperatorExposing m)
  | "HeaderExposing", m => decide (HeaderExposing m)
  | "ExposingDistinct", m => decide (ExposingDistinct m)
  | "NoTopPattern", m => decide (NoTopPattern m)
  | "ValuesDistinct", m => decide (ValuesDistinct m)
  | "TypesDistinct", m => decide (TypesDistinct m)
  | "ConstructorsDistinct", m => decide (ConstructorsDistinct m)
  | "TopNoShadowing", m => decide (TopNoShadowing m)
  | "TyVarSeqDistinct", m => decide (TyVarSeqDistinct m)
  | "CustomTypeTyVars", m => decide (CustomTypeTyVars m)
  | "AliasTyVars", m => decide (AliasTyVars m)
  | "AliasNotRecursive", m => decide (AliasNotRecursive m)
  | "ValueRecursion", m => decide (ValueRecursion m)
  | _, _ => true

/-- The program restrictions. -/
def programRules : List (String × String) :=
  [("ModulesProgram", "modules_program"), ("ModulesDistinct", "program_modules_distinct"),
   ("ImportOrder", "program_import_order"), ("ModulesReachable", "program_modules_reachable"),
   ("ProgramMain", "program_main")]

def programDecider : String → SProgram → Bool
  | "ModulesProgram", p => decide (ModulesProgram p)
  | "ModulesDistinct", p => decide (ModulesDistinct p)
  | "ImportOrder", p => decide (ImportOrder p)
  | "ModulesReachable", p => decide (ModulesReachable p)
  | "ProgramMain", p => decide (ProgramMain p)
  | _, _ => true

/-- Programs whose theorems the kernel does not check in reasonable time and depth (the tests of a
    compiler's limits: a record of 1100 fields, a list literal of thousands of elements, a closure
    of 300 parameters), proved by `native_decide` (2026-11-11: the kernel overflowed its recursion
    depth on them). -/
def synNative : List String :=
  ["CompilerIssue2281LongLineListTest", "WideClosureArity300Test", "WideRecord1100Test",
   "WideRecord600Test", "WideRecordDecoder300Test"]

elab "#syn_theorems " shardsId:ident : command => do
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo shardsId
  let shards ← liftTermElabM <| unsafe Meta.evalExpr (List (String × List (String × SProgram)))
    (← liftTermElabM <| Meta.inferType (mkConst c)) (mkConst c)
  let mut good : Nat := 0
  let mut bad : Nat := 0
  let mut modulesOnly : Nat := 0
  let mut sequenceOnly : Array String := #[]
  for (_, progs) in shards do
    for (name, p) in progs do
      let proj := p.project.replace "-" "_"
      let defn := s!"s_{proj}_{name}"
      let hasMain := decide (SProgram.HasMain p)
      if !hasMain then modulesOnly := modulesOnly + 1
      let stmt := if hasMain then "Src.SynOKSet" else "Src.ModulesSynOKSet"
      let ok := if hasMain then decide (SynOK p) else decide (ModulesSynOK p)
      let nat := synNative.contains name
      let tac := if nat then "native_decide" else "decide +kernel"
      let tag := if nat then " [native]" else ""
      let doc := s!"set_option maxRecDepth 100000 in\n/-- {name}: the AST-decidable restrictions [parse]{tag} -/\n"
      let mut cmds : Array String := #[]
      if ok then
        good := good + 1
        let lemma := if hasMain then "Src.synOKSet_of_synOK" else "Src.modulesSynOKSet_of"
        cmds := cmds.push s!"{doc}theorem syn_{proj}_{name} : {stmt} {defn} := {lemma} (of_decide_eq_true (by {tac}))"
      else
        bad := bad + 1
        let pre := if hasMain then "Src.notSynOKSet" else "Src.notModulesSynOKSet"
        if decide (SetFails p) then
          cmds := cmds.push s!"{doc}theorem nosyn_{proj}_{name} : ¬ {stmt} {defn} := {pre}_of_setFails (of_decide_eq_true (by {tac}))"
        else if decide (TwoCycle p) then
          cmds := cmds.push s!"{doc}theorem nosyn_{proj}_{name} : ¬ {stmt} {defn} := {pre}_of_twoCycle (of_decide_eq_true (by {tac}))"
        else
          -- only the canonical sequence is refused here
          sequenceOnly := sequenceOnly.push name
          let seqStmt := if hasMain then "Src.SynOK" else "Src.ModulesSynOK"
          cmds := cmds.push s!"{doc}theorem nosyn_{proj}_{name} : ¬ {seqStmt} {defn} := of_decide_eq_false (by {tac})"
        for (r, slug) in moduleRules do
          if !(p.modules.all (moduleDecider r)) then
            cmds := cmds.push s!"set_option maxRecDepth 100000 in\n/-- {name} breaks res:{slug.replace "_" "-"} [parse]{tag} -/\ntheorem nosyn_{proj}_{name}_{slug} : ¬ Src.Holds Src.{r} {defn} := of_decide_eq_false (by {tac})"
        for (r, slug) in programRules do
          if !(programDecider r p) && (hasMain || r != "ProgramMain") then
            cmds := cmds.push s!"set_option maxRecDepth 100000 in\n/-- {name} breaks res:{slug.replace "_" "-"} [parse]{tag} -/\ntheorem nosyn_{proj}_{name}_{slug} : ¬ Src.{r} {defn} := of_decide_eq_false (by {tac})"
      for stx in cmds do
        match Parser.runParserCategory (← getEnv) `command stx with
        | .ok cmd => elabCommand cmd
        | .error err => throwError "#syn_theorems: {name}: {err}"
  logInfo m!"#syn_theorems: {good + bad} programs: {good} meet the AST-decidable restrictions, {bad} do not ({modulesOnly} are modules without main); refused as sequences only: {sequenceOnly.toList}"

end StandardElm.Src
