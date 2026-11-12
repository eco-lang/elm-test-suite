/-
  A Standard Definition of Elm? Mechanisation: finding T1, plan step 6.

  StandardA81SleepBeyond32BitsTest forbids the line `the long sleep ended` (CHECK-NOT): a process
  sleeps 3e9 ms, another sleeps 200 ms and then kills the first. The book does not require that:
  r:p-wait lets any time pass, so an execution may wait 3e9 ms at the point where the default
  scheduler waits 200 ms; then both sleeps are due, the long sleep's process takes its action and
  logs before the kill is dispatched. The run is the default scheduler's with one override, a wait
  of 3e9 ms at iteration 6, found by tracing the scheduler; `runWorker_sound` makes it an execution
  the book allows. So step 5 states only the test's positive check, and this omission is a finding,
  not a gap.
-/
import StandardElmMech.Prog.Worker
import StandardElmMech.Generated.Worker01

namespace StandardElm.Prog
open StandardElm StandardElm.Eff

set_option maxRecDepth 8192

/-- The test with the override. -/
def t1Worker : WorkerTest :=
  { w_elm_core_StandardA81SleepBeyond32BitsTest with
    sched := { overrides := [(6, .wait 3000000000)] } }

def t1Check : Bool :=
  match runWorker t1Worker with
  | some (lg, _) => lg.any (·.1 == "the long sleep ended")
  | none => false

theorem t1Check_true : t1Check = true := by decide +kernel

/-- Finding T1: r:p-wait lets 3e9 ms pass before the 200 ms sleep's action is taken; then the long
    sleep's action is ready, and the process logs before it is killed. -/
theorem t1_a81_long_sleep_may_end :
    ∃ j lg, WorkerExec (Mod.Btest []) w_elm_core_StandardA81SleepBeyond32BitsTest.prog.modules .unit j .none lg ∧
      ∃ e ∈ lg, e.1 = "the long sleep ended" := by
  have h := t1Check_true
  unfold t1Check at h
  split at h
  · rename_i lg res hr
    have hx := runWorker_sound hr
    have e1 : t1Worker.prog = w_elm_core_StandardA81SleepBeyond32BitsTest.prog := rfl
    have e2 : t1Worker.flagsType = .unit := rfl
    have e3 : t1Worker.host = .none := rfl
    rw [e1, e2, e3] at hx
    refine ⟨t1Worker.flags, lg, hx, ?_⟩
    obtain ⟨e, he, hl⟩ := List.any_eq_true.mp h
    exact ⟨e, he, by simpa using hl⟩
  · cases h

end StandardElm.Prog
