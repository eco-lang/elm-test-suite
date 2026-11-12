/-
  A Standard Definition of Elm? Mechanisation: worker tests, plan step 5.

  A worker test is a program whose `main` is a worker, with its flags type and flags (absent flags
  are null, A72), a host and the scheduler's configuration, and its checks as statements about the
  log of an execution (D9). `WorkerTest.Holds` states, existentially, that some execution the book
  allows under the test's host has a log meeting every check. `runWorker` evaluates the program's
  modules, starts it and runs the scheduler; `holds_of_run` proves the statement from a run whose
  log meets the checks, so a worker theorem is `decide +kernel` (or `native_decide`) on `checkB`.
-/
import StandardElmMech.Prog.Sched
import StandardElmMech.Mod.Program

namespace StandardElm.Prog
open StandardElm StandardElm.Eff

/-- The start of a program, by the evaluator: the flags value, init applied to it, the dispatch of
    its command (in the order of `lo`), and subscriptions applied to the model. -/
def startFn (PE : PortEnv) (τ1 : PTy) (j : BVal) (r : List (String × Val)) (lo : LeafOrder) (o : Oracle)
    (fuel : Nat) (k : Nat) : Option (Config × List Nat × Log × Nat) :=
  match field r "init", field r "subscriptions" with
  | some fi, some fs =>
    let v1? : Option Val := if τ1 = .unit then some .unit else dec τ1 j
    match v1? with
    | some v1 =>
      match appVal o fuel fi v1 k with
      | ⟨.value (.tuple v cm none), l1, k1⟩ =>
        match flat cm with
        | some cs =>
          match dispatchFn 0 [] (qInit PE) (lo.apply cs) with
          | some (P, Q, ns) =>
            match appVal o fuel fs v k1 with
            | ⟨.value sb, l2, k2⟩ => some (⟨0, v, [], P, sb, Q, []⟩, ns, l1 ++ l2, k2)
            | _ => none
          | none => none
        | none => none
      | _ => none
    | none => none
  | _, _ => none

theorem startFn_sound {PE : PortEnv} {τ1 : PTy} {j : BVal} {r : List (String × Val)} {lo : LeafOrder}
    {o : Oracle} {fuel k : Nat} {K : Config} {ns : List Nat} {l : Log} {k' : Nat}
    (h : startFn PE τ1 j r lo o fuel k = some (K, ns, l, k')) : StartL PE τ1 j r K l := by
  unfold startFn at h
  split at h
  · rename_i fi fs hfi hfs
    simp only at h
    split at h
    · rename_i v1 hv1
      have hflags : FlagsVal τ1 j v1 := by
        by_cases hu : τ1 = .unit
        · simp only [hu, ite_true, Option.some.injEq] at hv1; exact Or.inl ⟨hu, hv1.symm⟩
        · simp only [hu, ite_false] at hv1; exact Or.inr ⟨hu, (dec_iff τ1 j v1).mpr hv1⟩
      split at h
      · rename_i v cm l1 k1 h1
        split at h
        · rename_i cs hf
          split at h
          · rename_i P Q ns' hd
            split at h
            · rename_i sb l2 k2 h2
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, -, rfl, -⟩ := h
              exact .r_p_init_l PE τ1 j r fi fs v1 v cm cs _ P Q [] sb l1 l2 hfi hfs hflags
                (appVal_sound_l h1) hf (lo.perm cs) (dispatchFn_sound hd) (appVal_sound_l h2)
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- A worker test. -/
structure WorkerTest where
  prog : Program
  flagsType : PTy
  flags : BVal := .null
  host : Host := .none
  sched : SchedConfig := {}
  fuel : Nat := 5000
  /-- The patterns of the test's CHECK-NOT lines proved by hand (plan step 6). -/
  checkNots : List String := []
  checks : List LogCheck

/-- D9 for a worker: some execution the book allows, under the test's host, has a log that meets
    every check. -/
def WorkerTest.Holds (w : WorkerTest) : Prop :=
  ∃ lg, WorkerExec (Mod.Btest []) w.prog.modules w.flagsType w.flags w.host lg ∧
    ∀ ck ∈ w.checks, LogCheck.Holds lg ck

/-- The fuel of each evaluation (Theorems.lean's). -/
def workerFuel : Nat := 100000

/-- Evaluate the modules, start the program and run the scheduler: the log, and the run. -/
def runWorker (w : WorkerTest) : Option (Log × RunResult) :=
  let ms := w.prog.modules
  match Mod.evProgram (.const false) workerFuel (Mod.Btest []) ms 0 with
  | ⟨.value (.prog r), lm, k1⟩ =>
    match startFn (portEnv ms) w.flagsType w.flags r w.sched.leafOrder (.const false) workerFuel k1 with
    | some (K0, ns, ls, k2) =>
      let c : Ctx := ⟨portEnv ms, r, w.host, w.sched, workerFuel⟩
      let st0 : SchedState := ⟨K0, [], ns, [], .const false, k2, 0⟩
      let res := run c w.fuel st0 []
      some (lm ++ ls ++ res.path.log, res)
    | none => none
  | _ => none

def WorkerTest.checkB (w : WorkerTest) : Bool :=
  match runWorker w with
  | some (lg, _) => w.checks.all (fun ck => ck.check lg)
  | none => false

theorem runWorker_sound {w : WorkerTest} {lg : Log} {res : RunResult} (h : runWorker w = some (lg, res)) :
    WorkerExec (Mod.Btest []) w.prog.modules w.flagsType w.flags w.host lg := by
  unfold runWorker at h
  simp only at h
  split at h
  · rename_i r lm k1 he
    split at h
    · rename_i K0 ns ls k2 hs
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hx := run_sound ⟨portEnv w.prog.modules, r, w.host, w.sched, workerFuel⟩ K0 [] w.fuel
        ⟨K0, [], ns, [], .const false, k2, 0⟩ [] (.nil _ _) rfl
      exact ⟨r, lm, K0, ls, _, _, Mod.evProgram_sound_l he, startFn_sound hs, hx, rfl⟩
    · cases h
  · cases h

/-- A run whose log meets every check proves the worker's statement. -/
theorem holds_of_run {w : WorkerTest} (h : w.checkB = true) : w.Holds := by
  unfold WorkerTest.checkB at h
  split at h
  · rename_i lg res hr
    exact ⟨lg, runWorker_sound hr, fun ck hm => LogCheck.check_sound (List.all_eq_true.mp h ck hm)⟩
  · cases h

end StandardElm.Prog
