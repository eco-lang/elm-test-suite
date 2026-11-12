/-
  A Standard Definition of Elm? Mechanisation: small kernel theorems about Chapter 8, plan step 4's
  acceptance examples. Each evaluates a phrase in the environment a module that imports Task sees
  (the default imports and `import Task`), by the oracle evaluator, and states the result through
  the evaluator's soundness, or reduces the resulting task with `stepTaskL`.
-/
import StandardElmMech.Mod.ME0
import StandardElmMech.Eff.Task
import StandardElmMech.Eff.Flat

namespace StandardElm.Eff
open StandardElm StandardElm.D StandardElm.Mod

/-- The environment of a module that imports Task: E0, the default imports, and the qualifier
    Task. -/
def E_ex : Env := (E0base.plusEnv E_default).plus [("Task", .mk [] VE_TaskIface)] []

def exFuel : Nat := 100000

/-- The value of a phrase in E_ex, by the evaluator with the constant oracle false. -/
def exValue (e : Exp) : Option Val :=
  match evExp (.const false) exFuel E_ex e 0 with
  | ⟨.value v, _, _⟩ => some v
  | _ => none

theorem exValue_sound {e : Exp} {v : Val} (h : exValue e = some v) : EvalExp E_ex e v := by
  unfold exValue at h
  split at h
  · rename_i w l k hr; cases h; exact evExp_sound (by rw [hr])
  · cases h

/-- Reduce a task by `stepTaskL` (no spawn, fresh identifier 0) until an outcome, at most n steps. -/
def iterateTask : Nat → Val → Option Val
  | 0, _ => none
  | n + 1, t =>
    if t.isOutcome then some t
    else match stepTaskL (.const false) exFuel 0 t 0 with
      | ⟨.value (_, t'), _, _⟩ => iterateTask n t'
      | _ => none

mutual
  /-- Equality of first-order values (no closures, basic values or environments), decided
      structurally; false wherever it cannot decide. -/
  def eqFO : Val → Val → Bool
    | .unit, .unit => true
    | .sv a, .sv b => decide (a = b)
    | .con c as, .con d bs => decide (c = d) && eqFOList as bs
    | .tuple a b none, .tuple a' b' none => eqFO a a' && eqFO b b'
    | .succeed a, .succeed b => eqFO a b
    | .fail a, .fail b => eqFO a b
    | .pid m, .pid n => decide (m = n)
    | _, _ => false
  def eqFOList : List Val → List Val → Bool
    | [], [] => true
    | a :: as, b :: bs => eqFO a b && eqFOList as bs
    | _, _ => false
end

theorem eqFO_sound_all : ∀ (a b : Val), eqFO a b = true → a = b := by
  apply eqFO.induct (motive_2 := fun as bs => eqFOList as bs = true → as = bs)
  all_goals intros
  all_goals simp_all [eqFO, eqFOList]

theorem eqFO_sound {a b : Val} (h : eqFO a b = true) : a = b := eqFO_sound_all a b h

/-- A computed value is the expected one. -/
def optEq (o : Option Val) (w : Val) : Bool :=
  match o with
  | some v => eqFO v w
  | none => false

theorem optEq_sound {o : Option Val} {w : Val} (h : optEq o w = true) : o = some w := by
  cases o with
  | none => simp [optEq] at h
  | some v => simp only [optEq] at h; rw [eqFO_sound h]

def isTaskLeaf : Val → Bool
  | .leaf .task _ => true
  | _ => false

/-- Task.perform identity (Task.succeed 1) evaluates to a task leaf command. -/
theorem ex_perform :
    ∃ w, EvalExp E_ex (ap (qv "Task" "perform") [v "identity", ap (qv "Task" "succeed") [i 1]]) w ∧
      ∃ t, w = .leaf .task t := by
  have h : (exValue (ap (qv "Task" "perform") [v "identity", ap (qv "Task" "succeed") [i 1]])).map isTaskLeaf
      = some true := by decide +kernel
  cases hv : exValue (ap (qv "Task" "perform") [v "identity", ap (qv "Task" "succeed") [i 1]]) with
  | none => simp [hv] at h
  | some w =>
    simp only [hv, Option.map_some, Option.some.injEq] at h
    refine ⟨w, exValue_sound hv, ?_⟩
    cases w <;> simp [isTaskLeaf] at h
    rename_i m t; cases m <;> simp at h
    exact ⟨t, rfl⟩

/-- The task of Task.sequence [Task.succeed 1, ..., Task.succeed k]. -/
def seqTask (k : Nat) : Option Val :=
  exValue (ap (qv "Task" "sequence") [listE ((List.range k).map fun (j : Nat) => ap (qv "Task" "succeed") [i ((j : Int) + 1)])])

/-- Task.sequence of six succeeding tasks reduces to succeed [1, ..., 6]; six elements exercise
    foldrHelper's unrolling by four and its recursion. -/
theorem ex_sequence :
    (seqTask 6 >>= iterateTask 200) = some (.succeed (Val.ofList ((List.range 6).map fun (j : Nat) => Val.int ((j : Int) + 1)))) :=
  optEq_sound (by decide +kernel)

/-- Task.attempt identity (Task.fail 3) is a task leaf whose task succeeds with Err 3. -/
theorem ex_attempt_err :
    (match exValue (ap (qv "Task" "attempt") [v "identity", ap (qv "Task" "fail") [i 3]]) with
      | some (.leaf .task t) => iterateTask 50 t
      | _ => none) = some (.succeed (.con conErr [.int 3])) :=
  optEq_sound (by decide +kernel)

/-- Cmd.batch [Cmd.none, Cmd.none] flattens to the empty multiset. -/
theorem ex_flat_none :
    (exValue (ap (qv "Cmd" "batch") [listE [qv "Cmd" "none", qv "Cmd" "none"]]) >>= flat) = some [] := by
  have h : (exValue (ap (qv "Cmd" "batch") [listE [qv "Cmd" "none", qv "Cmd" "none"]]) >>= flat).map List.isEmpty
      = some true := by decide +kernel
  cases hf : (exValue (ap (qv "Cmd" "batch") [listE [qv "Cmd" "none", qv "Cmd" "none"]]) >>= flat) with
  | none => simp [hf] at h
  | some cs => simp [hf] at h; simp [h]

end StandardElm.Eff
