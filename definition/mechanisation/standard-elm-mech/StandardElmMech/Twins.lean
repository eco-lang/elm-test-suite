/-
  A Standard Definition of Elm? Mechanisation: the check that each logged relation of RulesL.lean is
  the book's relation of Rules.lean with a log (plan decision D4).

  `#check_twins R RL` fails unless RL has exactly the constructors of R, in the same order, each
  named as R's with `_l` appended, each with the same sequence of premises that are relations of
  the two blocks (compared with the trailing `L` removed), and RL has one more index than R. It is
  run for the 17 pairs of Chapter 6, the 4 of Chapter 7, the 2 of Chapter 8 and the 3 of Chapter 9
  below, so that the build fails if a rule of the book and its logged twin
  drift apart.
-/
import Lean
import StandardElmMech.RulesL
import StandardElmMech.Mod.RulesL
import StandardElmMech.Eff.Messages
import StandardElmMech.Prog.Rules

open Lean Meta Elab Command

namespace StandardElm.Twins

/-- The names of the relations of both blocks, without namespace, and with the `L` of the logged
    ones removed. -/
def relBase (n : Name) : Option String :=
  let s := n.getString!
  let book := ["EvalAtExp", "EvalExpRow", "EvalExp", "AppVal", "EvalMatch", "EvalMRule", "EvalDec",
    "EvalValBind", "MatchAtPat", "MatchPatRow", "MatchPat", "EvalExpOpt", "EvalExpRowOpt",
    "EvalValBindOpt", "MatchPatOpt", "MatchPatRowOpt", "MatchAtPats",
    -- Chapter 7 and Chapter 9's dynamic rules for modules (Mod/Rules.lean)
    "EvalForces", "EvalTopDec", "EvalModule", "EvalProgram",
    "EvalExpItem", "EvalExpItems", "EvalExpList", "EvalExpListOpt", "EvalHeader", "EvalImports",
    "EvalConBind", "EvalConBindOpt", "EvalDatBind", "EvalDatBindOpt", "EvalTypBind",
    -- Chapter 8's relations that can log (Eff/Task.lean, Eff/Messages.lean)
    "TaskRed", "Recv",
    -- Chapter 9's start and transitions (Prog/Rules.lean)
    "Start", "Step", "AcceptMsgs"]
  if book.contains s then some s
  else if s.endsWith "L" && book.contains (s.dropEnd 1).toString then some (s.dropEnd 1).toString
  else none

/-- The relation premises of a constructor's type, as base names, in order. -/
def premiseHeads (ty : Expr) : MetaM (List String) :=
  forallTelescopeReducing ty fun xs _ => do
    let mut out : List String := []
    for x in xs do
      let t ← inferType x
      if let some c := t.getAppFn.constName? then
        if let some b := relBase c then out := out ++ [b]
    return out

end StandardElm.Twins

open StandardElm.Twins in
elab "#check_twins " r:ident l:ident : command => liftTermElabM do
  let rn ← realizeGlobalConstNoOverloadWithInfo r
  let ln ← realizeGlobalConstNoOverloadWithInfo l
  let some (.inductInfo ri) := (← getEnv).find? rn | throwError "{rn} is not an inductive"
  let some (.inductInfo li) := (← getEnv).find? ln | throwError "{ln} is not an inductive"
  unless li.numIndices = ri.numIndices + 1 do
    throwError "{ln} has {li.numIndices} indices, {rn} has {ri.numIndices}: the log must be the one more"
  unless ri.ctors.length = li.ctors.length do
    throwError "{rn} has {ri.ctors.length} constructors, {ln} has {li.ctors.length}"
  for (rc, lc) in ri.ctors.zip li.ctors do
    unless lc.getString! = rc.getString! ++ "_l" do
      throwError "{lc} should be named {rc.getString!}_l"
    let rt := (← getConstInfo rc).type
    let lt := (← getConstInfo lc).type
    let rp ← premiseHeads rt
    let lp ← premiseHeads lt
    unless rp = lp do
      throwError "{rc} has relation premises {rp}, {lc} has {lp}"
  logInfo m!"#check_twins {rn} {ln}: {ri.ctors.length} constructors agree"

namespace StandardElm

#check_twins EvalAtExp EvalAtExpL
#check_twins EvalExpRow EvalExpRowL
#check_twins EvalExp EvalExpL
#check_twins AppVal AppValL
#check_twins EvalMatch EvalMatchL
#check_twins EvalMRule EvalMRuleL
#check_twins EvalDec EvalDecL
#check_twins EvalValBind EvalValBindL
#check_twins MatchAtPat MatchAtPatL
#check_twins MatchPatRow MatchPatRowL
#check_twins MatchPat MatchPatL
#check_twins EvalExpOpt EvalExpOptL
#check_twins EvalExpRowOpt EvalExpRowOptL
#check_twins EvalValBindOpt EvalValBindOptL
#check_twins MatchPatOpt MatchPatOptL
#check_twins MatchPatRowOpt MatchPatRowOptL
#check_twins MatchAtPats MatchAtPatsL

-- Chapter 7: the four relations whose derivations can log (Mod/RulesL.lean)
#check_twins Mod.EvalForces Mod.EvalForcesL
#check_twins Mod.EvalTopDec Mod.EvalTopDecL
#check_twins Mod.EvalModule Mod.EvalModuleL
#check_twins Mod.EvalProgram Mod.EvalProgramL

-- Chapter 8: task reduction and messages (Enc and Dec log nothing and have no twins, D4)
#check_twins Eff.TaskRed Eff.TaskRedL
#check_twins Eff.Recv Eff.RecvL

-- Chapter 9: the start, the transitions and the messages of an accepted value
#check_twins Prog.Start Prog.StartL
#check_twins Prog.Step Prog.StepL
#check_twins Prog.AcceptMsgs Prog.AcceptMsgsL

end StandardElm
