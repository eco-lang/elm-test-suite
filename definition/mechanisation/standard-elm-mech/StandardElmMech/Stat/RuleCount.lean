/-
  A Standard Definition of Elm? Mechanisation: the static rules against the book, plan step 9
  (section 4 and 5). `#check_static_rules` reads the `\defnrule` labels of static-core.tex,
  static-modules.tex and programs.tex, and fails unless every label `r:s-…`, `r:sm-…` and
  `r:p-stat-…` has a relation constructor of the same name (with `_` for `-` and `:`), and every
  such constructor a label; `r_sm_topdec_seq_types` is the one exception, a second constructor
  for rule r:sm-topdec-seq (Modules.lean). Expected: 45 + 20 + 3 constructors for 45 + 19 + 3
  labels.
-/
import Lean
import StandardElmMech.Stat.Program

namespace StandardElm.Stat
open Lean Elab Command

/-- The rule labels `\defnrule[<prefix>…]` of a chapter. -/
def ruleLabels (text pre : String) : List String :=
  ((text.splitOn "\\defnrule[").drop 1).filterMap fun chunk =>
    let lbl := (chunk.splitOn "]").headD ""
    if lbl.startsWith pre then some lbl else none

def staticRelations : List Name :=
  [``ElTy, ``ElTyRow, ``ElAtPat, ``ElPatRow, ``ElPat, ``ElAtExp, ``ElExpRow, ``ElExp, ``ElMatch, ``ElMRule,
   ``ElDec, ``ElValBind, ``ElItem, ``ElExpList, ``ElImports, ``ElHeader, ``ElConBind, ``ElDatBind,
   ``ElTypBind, ``ElTopDec, ``ElModule, ``ElProgram]

elab "#check_static_rules" : command => do
  let env ← getEnv
  let mut ctors : List String := []
  for n in staticRelations do
    match env.find? n with
    | some (.inductInfo ii) => ctors := ctors ++ ii.ctors.map fun c => c.getString!
    | _ => throwError "#check_static_rules: {n} is not an inductive relation"
  let rules := ctors.filter fun c => c.startsWith "r_"
  let read (f : String) : CommandElabM String := do
    let r ← (IO.FS.readFile s!"../../tex/{f}").toBaseIO
    match r with
    | .ok t => pure t
    | .error e => throwError "#check_static_rules: cannot read {f}: {e}"
  let core ← read "static-core.tex"
  let mods ← read "static-modules.tex"
  let progs ← read "programs.tex"
  let labels := ruleLabels core "r:s-" ++ ruleLabels mods "r:sm-" ++ ruleLabels progs "r:p-stat-"
  let toCtor (l : String) := (l.replace ":" "_").replace "-" "_"
  let missing := labels.filter fun l => !(rules.contains (toCtor l))
  let extra := rules.filter fun c => !(labels.map toCtor).contains c && c != "r_sm_topdec_seq_types"
  unless missing.isEmpty && extra.isEmpty do
    throwError "#check_static_rules: labels without a constructor {missing}, constructors without a label {extra}"
  let count (p : String) := (rules.filter (·.startsWith p)).length
  let nS := count "r_s_"
  let nSM := count "r_sm_"
  let nP := count "r_p_stat_"
  unless nS = 45 ∧ nSM = 20 ∧ nP = 3 do
    throwError "#check_static_rules: {nS} + {nSM} + {nP} constructors, expected 45 + 20 + 3"
  logInfo m!"#check_static_rules: {labels.length} labels, {rules.length} constructors ({nS} + {nSM} + {nP}) agree"

#check_static_rules

end StandardElm.Stat
