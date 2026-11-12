/-
  A Standard Definition of Elm? Mechanisation: the theorems of the worker tests (plan step 5).

  `#worker_theorems w1 w2 ...` emits, for each worker test `w` (Prog/Worker.lean), the theorem
  `t_<project>_<Name> : ({ w with checks := [...] } : Prog.WorkerTest).Holds`: some execution the
  book allows, under the test's host, has a log that meets every check of the test (D9). It is
  proved by `Prog.holds_of_run` from a run of the scheduler, by `decide +kernel`, or by
  `native_decide` when the program uses a value only the C library computes (a float), prints a
  value with Debug.toString, or has a statement about its printed log; such a theorem is tagged
  `[native]`. The command first runs the test by the compiled evaluator, so a test whose run does
  not meet its checks is an error that names it.
-/
import Lean
import StandardElmMech.Theorems
import StandardElmMech.Prog.Worker
import StandardElmMech.Prog.Invariant

namespace StandardElm
open StandardElm.D

/-- Whether a worker test's theorem is proved by `native_decide`, or rests on a hand theorem that is
    (the CHECK-NOT theorems decide the printed log entries natively). -/
def Prog.WorkerTest.proofNative (w : Prog.WorkerTest) : Bool :=
  w.prog.proofNative

def Prog.WorkerTest.taggedNative (w : Prog.WorkerTest) : Bool :=
  w.proofNative || !w.checkNots.isEmpty

open Lean Elab Command in
elab "#worker_theorems " ws:ident* : command => do
  let mut kernel : Nat := 0
  let mut native : Nat := 0
  let mut checks : Nat := 0
  for wi in ws do
    let w ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo wi
    let t ← liftTermElabM <| unsafe Meta.evalExpr Prog.WorkerTest (mkConst ``StandardElm.Prog.WorkerTest) (mkConst w)
    let p := t.prog
    checks := checks + p.checks.length
    let nat := t.proofNative
    let tac := if nat then "native_decide" else "decide +kernel"
    if t.taggedNative then native := native + 1 else kernel := kernel + 1
    let tag := if t.taggedNative then " [native]" else ""
    let doc := s!"set_option maxRecDepth 2048 in\n/-- {p.source}/{p.name}.elm [parse] [elab] [harness] [params]{tag} -/\n"
    match toLogChecks p.checks with
    | none => throwError "#worker_theorems: {p.name}: a check whose value cannot be stated"
    | some cs =>
      if !({ t with checks := cs } : Prog.WorkerTest).checkB then
        throwError "#worker_theorems: {p.name}: the scheduler's run does not meet the checks"
      let csL := ", ".intercalate (cs.map LogCheck.toLean)
      let holds := s!"(\{ {w} with checks := [{csL}] } : Prog.WorkerTest).Holds"
      let stx :=
        if t.checkNots.isEmpty then
          s!"{doc}theorem t_{p.project}_{p.name} : {holds} :=\n  Prog.holds_of_run (by {tac})"
        else
          -- the CHECK-NOT lines: the hand theorem `Prog.Inv.<Test>.checkNot` (plan step 6)
          let nots := " ∧ ".intercalate (t.checkNots.map fun pat => s!"{w}.HoldsNot {repr pat}")
          s!"{doc}theorem t_{p.project}_{p.name} : {holds} ∧ {nots} :=\n  ⟨Prog.holds_of_run (by {tac}), Prog.Inv.{p.name}.checkNot⟩"
      match Parser.runParserCategory (← getEnv) `command stx with
      | .ok cmd => withRef wi <| elabCommand cmd
      | .error err => throwError "#worker_theorems: {p.name}: {err}"
  let total := kernel + native
  logInfo m!"#worker_theorems: {total} theorems ({kernel} kernel, {native} native), {checks} checks"

end StandardElm
