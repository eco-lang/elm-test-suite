# Step 5: Chapter 9 (execution) and the worker tests

Part of [the plan](../lean-full-definition.md); follows [conventions.md](conventions.md). Status:
specified 2026-11-11, not started.

Book references are to `definition/tex/programs.tex` (Chapter 9) unless another file is named.
`StandardElmMech/` is `definition/mechanisation/standard-elm-mech/StandardElmMech/`.

## Goal

Encode the dynamic half of Chapter 9 that steps 2 and 3 have not (they encode `r:p-dyn-module`,
`r:p-dyn-main` and `r:p-program`'s dynamic premise): configurations
(`fig:programs-objects`), dispatch (4 rules), the start of a program with `Flags_τ` (1 rule,
absent flags `null`, A72), and the transitions (12 rules), each rule one constructor; their
logged twins (D4); the host as a relation and executions as a relation; the log of an execution;
traces and the meaning `Tr(program, j)`; a scheduler with explicit choices and a default strategy
that models Elm/JS, whose run is proved to be an execution; the worker check statements
(existential, D9); the guarantees of A86; and the rulings A62, A77, A79, A80 and A81 as theorems.
The translator writes worker programs with their flags, host and choices.

Gains: the 34 worker tests with positive checks, and the positive check of
StandardA81SleepBeyond32BitsTest (35 tests, 116 checks).

Conformance (`sec:programs-behaviour`, second paragraph) is **out of scope**: it is a relation
between the definition and an implementation, and the mechanisation has no model of an
implementation. Traces and `Tr` are in scope (they are defined objects of the book, and cheap).

## Prerequisites

From step 4 (`StandardElm`, `StandardElm.Eff`): `BVal`, `tupleTy`, `Val`'s
effect constructors (`succeed`, `fail`, `andThen`, `onError`, `prim`, `pid`, `leaf`, `bv`),
`Prim`, `Mgr`, `platPrims`, `platMgrs`, `Action`, `Out`, `TaskRed`, `TaskRedL`, `stepTaskL` (+
sound), `Enc`, `Dec`, `dec` (+ `dec_iff`), `flat`, `leafCore`, `Input`, `Recv`, `RecvL`,
`recvL` (+ sound), `recvNone` (+ sound), `ME0_Task`, `ME0_Process`.

From step 2 ([step-02-modules.md](step-02-modules.md)): `PTy` (`Eff/PTy.lean`), `Val.batch`,
`Val.mapE`, `Val.prog`, `BasVal.platformWorker`, `Val.toList?`, `Mod.Dir` (`out`, `inn`), the
module syntax (`Module` with `body : TopDec`, and `TopDec.port (x : Var) (d : Dir) (τ : PTy)`,
`TopDec.seq`), `Btest`, and the program evaluation with logs:

```lean
inductive EvalProgramL : Basis → List Module → Val → Log → Prop     -- r:p-dyn-module, r:p-dyn-main
inductive EvalProgram  : Basis → List Module → Val → Prop
theorem EvalProgramL.forget : EvalProgramL B p v l → EvalProgram B p v
def evProgram (o : Oracle) (n : Nat) (B : Basis) : List Module → Nat → Res Val
theorem evProgram_sound_l : evProgram o n B p k = ⟨.value v, l, k'⟩ → EvalProgramL B p v l
theorem evProgram_unique_l : evProgram o n B p k = ⟨.value v, l, k⟩ → ∀ v' l', EvalProgramL B p v' l' → v' = v ∧ l' = l
```

From step 1 ([step-01-core-foundations.md](step-01-core-foundations.md)): `Log`, `Oracle`
(`Nat → Bool`, read at an index `k` threaded through the evaluator), `Oracle.const`, `Outcome`,
`Res` (`out`, `log`, `next`), `AppValL` with forget and lift, the logged evaluator
`appVal (o : Oracle) : Nat → Val → Val → Nat → Res Val` with `appVal_sound`, and, for the A62
example only, D1's non-derivability lemma at `appVal`:

```lean
/-- Stuck without reading a choice (the index comes back unchanged): no derivation exists. -/
theorem appVal_noValue_of_stuck : appVal o n f v k = ⟨.stuck, l, k⟩ → ¬ ∃ w, AppVal f v w
```

Also from step 1 (`Checks.lean`), the check statements about a log (D9):

```lean
inductive EntryPat where | entry (label : String) (x : Expect) | label (label : String)
inductive LogCheck where
  | has (p : EntryPat)          -- CHECK, and CHECK-DAG read as CHECK
  | run (ps : List EntryPat)    -- a CHECK followed by CHECK-NEXT lines: consecutive entries
  | printed (r : Rx)            -- {{regex}}, or CHECK-SAME [native]
def LogCheck.Holds (l : Log) : LogCheck → Prop
def LogCheck.check (l : Log) : LogCheck → Bool
theorem LogCheck.check_sound : LogCheck.check l c = true → LogCheck.Holds l c
```

From step 3 ([step-03-module-form.md](step-03-module-form.md)): `ModProgram` (`name`, `source`,
`native`, `modules`, `checks : List CheckLine`, `meaning`), the conversion `toLogChecks` of
`CheckLine`s into `LogCheck`s (run at generation), the generator command `#mod_program_theorems`
in `Theorems.lean` (the model for this step's `#worker_theorems`), and the translator's
module-form path, which refuses a program whose `main` has type `Program` with `effects:worker`.
`ModProgram` carries neither the port environment nor the flags type; this step computes the first
from the modules (`portEnv`) and adds the second in `WorkerTest`.

## Lean definitions

### Files

| File | Namespace | Contents |
|------|-----------|----------|
| `Prog/Objects.lean` | `StandardElm.Prog` | `Proc`, `PEntry`, `Procs`, `OutQ`, `Config`, `Event`, `qInit`, helpers |
| `Prog/Dispatch.lean` | `StandardElm.Prog` | `Dispatch` (4 rules), `freshPid`, `dispatchFn` + soundness |
| `Prog/Rules.lean` | `StandardElm.Prog` | `FlagsVal`, `Start`, `Step`, `AcceptMsgs`, `PlatStep` and logged twins `StartL`, `StepL`, `AcceptMsgsL`, forget and lift |
| `Prog/Exec.lean` | `StandardElm.Prog` | `Host`, `HostAllows`, `Exec`, `ExecL`, `WorkerExec`, `trace`, `Tr` |
| `Prog/Sched.lean` | `StandardElm.Prog` | `Choice`, `LeafOrder`, `SchedConfig`, `SchedState`, `defaultChoice`, `doChoice`, `startFn`, `run` + soundness |
| `Prog/Worker.lean` | `StandardElm.Prog` | `WorkerTest`, `WorkerTest.Holds`, `runWorker`, `holds_of_run` |
| `Prog/Guarantees.lean` | `StandardElm.Prog` | the A86 theorems |
| `Prog/Rulings.lean` | `StandardElm.Prog` | A62, A77, A79, A80, A81, and the A66 example |
| `Generated/Worker01.lean`, `Generated/ChecksWorker01.lean` | `StandardElm` | the 35 worker tests, written by the translator |

No file imports `Lean`. `StandardElmMech.lean` imports them all.

### Objects of execution (`Prog/Objects.lean`, `fig:programs-objects`)

```lean
namespace StandardElm.Prog
open StandardElm.Eff

/-- PE as the dynamic semantics reads it: each port name with its direction and payload type
    (Chapter 7's reduced syntax records them; [elab]). Port names are distinct (A84). -/
abbrev PortEnv := List (String × Mod.Dir × PTy)
/-- The ports of a program: the `port` top-level declarations of its modules, in order. -/
def portEnv : List Mod.Module → PortEnv          -- collects TopDec.port x d τ through TopDec.seq

/-- Time: milliseconds, a non-negative rational (D6). Non-negativity is an invariant: the start
    is at 0 and r:p-wait adds d > 0. -/
abbrev Time := Rat

/-- A live process: its task, the time of its latest step (or start), and its origin: the leaf
    command whose task it performs, or `none` for spawned. -/
structure Proc where
  task   : Val
  time   : Time
  origin : Option Val
inductive PEntry where | live (p : Proc) | ended

abbrev Procs   := List (Nat × PEntry)        -- ProcId -fin-> Proc, an association list
abbrev OutQ    := List (String × List BVal)  -- Var -fin-> BVal*
abbrev Pending := List Val                   -- H: a multiset, as a list (no rule reads its order)

/-- K = (s, v, M, P, sb, Q, H). -/
structure Config where
  time    : Time
  model   : Val
  msgs    : List Val
  procs   : Procs
  subs    : Val
  outq    : OutQ
  pending : Pending

/-- Event (fig:programs-objects): In(p, j), Out(p, j), an action, wait d. The platform's events
    are absent (the empty platform, [params]). -/
inductive Event where
  | inn  (p : String) (j : BVal)
  | out  (p : String) (j : BVal)
  | act  (a : Action)
  | wait (d : Time)

def Procs.get (P : Procs) (n : Nat) : Option PEntry := fmLookup P n
def Procs.set (P : Procs) (n : Nat) (e : PEntry) : Procs := fmPlus P [(n, e)]
def OutQ.get (Q : OutQ) (p : String) : List BVal := (fmLookup Q p).getD []

/-- Q_init: an empty queue for every outgoing port of PE. -/
def qInit (PE : PortEnv) : OutQ := PE.filterMap fun (p, d, _) => if d = .out then some (p, []) else none

/-- r(lab) for the record of a program value. -/
def field (r : List (String × Val)) (l : String) : Option Val := fmLookup r l

/-- The condition of r:p-proc-sleep: if v' is a finite float, s ≥ s' + max(0, v'). -/
def SleepReady (s s' : Time) (v' : Val) : Prop :=
  ∀ x q, v' = .sv (.float x) → floatToRat? x = some q → s' + (if q < 0 then 0 else q) ≤ s
```

### Dispatch (`Prog/Dispatch.lean`, `sec:programs-dispatch`)

```lean
/-- s, P, Q, H ⊢ L ⇒ (P', Q', H'). `c ∈ Leaf(m, v)` is `leafCore c = some (m, v)`. -/
inductive Dispatch : Time → Procs → OutQ → Pending → List Val → Procs → OutQ → Pending → Prop where
  /-- r:p-disp-empty -/
  | r_p_disp_empty (s P Q H) : Dispatch s P Q H [] P Q H
  /-- r:p-disp-task -/
  | r_p_disp_task (s P Q H c tk n L P' Q' H') :
      leafCore c = some (.task, tk) → n ∉ fmDom P →
      Dispatch s (P.set n (.live ⟨tk, s, some c⟩)) Q H L P' Q' H' →
      Dispatch s P Q H (c :: L) P' Q' H'
  /-- r:p-disp-out -/
  | r_p_disp_out (s P Q H c p j js L P' Q' H') :
      leafCore c = some (.out p, .bv j) → fmLookup Q p = some js →
      Dispatch s P (fmPlus Q [(p, js ++ [j])]) H L P' Q' H' →
      Dispatch s P Q H (c :: L) P' Q' H'
  /-- r:p-disp-plat: m ∈ Mgr_plat, empty here, so never applicable ([params]) -/
  | r_p_disp_plat (s P Q H c m v L P' Q' H') :
      leafCore c = some (m, v) → m ∈ platMgrs →
      Dispatch s P Q (H ++ [c]) L P' Q' H' →
      Dispatch s P Q H (c :: L) P' Q' H'

/-- A process identifier never used: one more than the largest in P. -/
def freshPid (P : Procs) : Nat := P.foldl (fun m (n, _) => max m n) 0 + 1
theorem freshPid_fresh : freshPid P ∉ fmDom P

/-- Dispatch a sequence, giving fresh identifiers in order; returns the new identifiers in the
    order created. `none` if a leaf is of no manager this program has (an unknown port). -/
def dispatchFn (s : Time) : Procs → OutQ → List Val → Option (Procs × OutQ × List Nat)
theorem dispatchFn_sound : dispatchFn s P Q L = some (P', Q', ns) → Dispatch s P Q H L P' Q' H
```

Dispatch has no application premise, so it has no logged twin (see step 4, issue 2).

### Start and transitions (`Prog/Rules.lean`, `sec:programs-dispatch`, `sec:programs-transitions`)

```lean
/-- Flags_τ(j) = v: () at the unit type, Dec_τ(j) otherwise (A77). -/
def FlagsVal (τ : PTy) (j : BVal) (v : Val) : Prop :=
  (τ = .unit ∧ v = .unit) ∨ (τ ≠ .unit ∧ Dec τ j v)

/-- PE, τ1, j ⊢ prog r ⇒ K (r:p-init). -/
inductive Start : PortEnv → PTy → BVal → List (String × Val) → Config → Prop where
  /-- r:p-init -/
  | r_p_init (PE τ1 j r fi fs v1 v cm cs L P Q H sb) :
      field r "init" = some fi → field r "subscriptions" = some fs →
      FlagsVal τ1 j v1 → AppVal fi v1 (.tuple v cm none) →
      flat cm = some cs → L.Perm cs → Dispatch 0 [] (qInit PE) [] L P Q H →
      AppVal fs v sb →
      Start PE τ1 j r ⟨0, v, [], P, sb, Q, H⟩

/-- Platform steps: the empty platform has none ([params]). -/
inductive PlatStep : Config → Option Event → Config → Prop

/-- The messages of an accepted incoming value, one list per leaf of the enumeration
    (premise of r:p-in-accept): a message, or none when no rule gives one. -/
inductive AcceptMsgs : List Val → Input → List Val → Prop where
  | seq_nil (x) : AcceptMsgs [] x []
  | seq_recv (c cs x v ms) : Recv c x v → AcceptMsgs cs x ms → AcceptMsgs (c :: cs) x (v :: ms)
  | seq_none (c cs x ms) : (¬ ∃ v, Recv c x v) → AcceptMsgs cs x ms → AcceptMsgs (c :: cs) x ms

/-- K →[ℓ] K' (sec:programs-transitions), for the program value prog r with port environment
    PE. One constructor per rule. -/
inductive Step (PE : PortEnv) (r : List (String × Val)) : Config → Option Event → Config → Prop where
  /-- r:p-update -/
  | r_p_update (s v v1 M P sb Q H fu fs v2 v' cm cs L P' Q' H' sb') :
      field r "update" = some fu → field r "subscriptions" = some fs →
      AppVal fu v1 v2 → AppVal v2 v (.tuple v' cm none) →
      flat cm = some cs → L.Perm cs → Dispatch s P Q H L P' Q' H' →
      AppVal fs v' sb' →
      Step PE r ⟨s, v, v1 :: M, P, sb, Q, H⟩ none ⟨s, v', M, P', sb', Q', H'⟩
  /-- r:p-proc-step: silent, or labelled by an action of a platform primitive -/
  | r_p_proc_step (s v M P sb Q H n tk s' o a tk') :
      P.get n = some (.live ⟨tk, s', o⟩) → TaskRed tk a tk' →
      (∀ x, a = some x → x.prim ∈ platPrims) →
      Step PE r ⟨s, v, M, P, sb, Q, H⟩ (a.map .act) ⟨s, v, M, P.set n (.live ⟨tk', s, o⟩), sb, Q, H⟩
  /-- r:p-proc-sleep -/
  | r_p_proc_sleep (s v M P sb Q H n tk s' o tk' v' t'') :
      P.get n = some (.live ⟨tk, s', o⟩) → TaskRed tk (some ⟨.sleep, [v'], t''⟩) tk' →
      SleepReady s s' v' →
      Step PE r ⟨s, v, M, P, sb, Q, H⟩ (some (.act ⟨.sleep, [v'], t''⟩))
        ⟨s, v, M, P.set n (.live ⟨tk', s, o⟩), sb, Q, H⟩
  /-- r:p-proc-spawn -/
  | r_p_proc_spawn (s v M P sb Q H n tk s' o tk' t0 n') :
      P.get n = some (.live ⟨tk, s', o⟩) → TaskRed tk (some ⟨.spawn, [t0], .succeed (.pid n')⟩) tk' →
      n' ∉ fmDom P →
      Step PE r ⟨s, v, M, P, sb, Q, H⟩ (some (.act ⟨.spawn, [t0], .succeed (.pid n')⟩))
        ⟨s, v, M, (P.set n (.live ⟨tk', s, o⟩)).set n' (.live ⟨t0, s, none⟩), sb, Q, H⟩
  /-- r:p-proc-kill: (P + {pid' ↦ ended}) + {pid ↦ (tk', s, orig)}; a self-kill keeps the
      second modification (A90) -/
  | r_p_proc_kill (s v M P sb Q H n tk s' o tk' n' t'') :
      P.get n = some (.live ⟨tk, s', o⟩) → TaskRed tk (some ⟨.kill, [.pid n'], t''⟩) tk' →
      Step PE r ⟨s, v, M, P, sb, Q, H⟩ (some (.act ⟨.kill, [.pid n'], t''⟩))
        ⟨s, v, M, (P.set n' .ended).set n (.live ⟨tk', s, o⟩), sb, Q, H⟩
  /-- r:p-proc-message -/
  | r_p_proc_message (s v M P sb Q H n v' s' c v'') :
      P.get n = some (.live ⟨.succeed v', s', some c⟩) → Recv c (.val v') v'' →
      Step PE r ⟨s, v, M, P, sb, Q, H⟩ none ⟨s, v, M ++ [v''], P.set n .ended, sb, Q, H⟩
  /-- r:p-proc-end -/
  | r_p_proc_end (s v M P sb Q H n tk s' o) :
      P.get n = some (.live ⟨tk, s', o⟩) →
      ((∃ v', tk = .fail v') ∨ (∃ v', tk = .succeed v' ∧ o = none)) →
      Step PE r ⟨s, v, M, P, sb, Q, H⟩ none ⟨s, v, M, P.set n .ended, sb, Q, H⟩
  /-- r:p-in-accept -/
  | r_p_in_accept (s v M P sb Q H p τ j v' cs L Ms) :
      fmLookup PE p = some (.inn, τ) → Dec τ j v' →
      flat sb = some cs → L.Perm cs → AcceptMsgs L (.port p j) Ms →
      Step PE r ⟨s, v, M, P, sb, Q, H⟩ (some (.inn p j)) ⟨s, v, M ++ Ms, P, sb, Q, H⟩
  /-- r:p-in-reject -/
  | r_p_in_reject (K p τ j) :
      fmLookup PE p = some (.inn, τ) → (¬ ∃ v, Dec τ j v) → Step PE r K (some (.inn p j)) K
  /-- r:p-out -/
  | r_p_out (s v M P sb Q H p j J) :
      fmLookup Q p = some (j :: J) →
      Step PE r ⟨s, v, M, P, sb, Q, H⟩ (some (.out p j)) ⟨s, v, M, P, sb, fmPlus Q [(p, J)], H⟩
  /-- r:p-wait -/
  | r_p_wait (s v M P sb Q H d) : 0 < d →
      Step PE r ⟨s, v, M, P, sb, Q, H⟩ (some (.wait d)) ⟨s + d, v, M, P, sb, Q, H⟩
  /-- r:p-platform -/
  | r_p_platform (K a K') : PlatStep K a K' → Step PE r K a K'
```

Notes on faithfulness:

- In `r_p_in_accept`, `AcceptMsgs` produces `M_1 ⋯ M_n` with each `M_i` one message or none,
  exactly as the rule's premise "for 1 ≤ i ≤ n: c_i, receiving (p, j), gives M_i, or M_i = ε and
  no message", and `L` is the enumeration of the multiset `Flat(sb)`.
- `r_p_proc_step`'s option is written as the side condition "if a is present, its primitive is a
  platform primitive"; with `platPrims = []` this admits silent steps only.
- `H` is a list: the book's multiset is the list up to `Perm`. Only `r:p-disp-plat` and the
  platform steps touch it, and with the empty platform it stays `[]`.

Logged twins (D4), constructors suffixed `_l`, one more index `Log`:

```lean
inductive StartL : PortEnv → PTy → BVal → List (String × Val) → Config → Log → Prop
  -- r_p_init_l: AppValL fi v1 (...) l1 → ... → AppValL fs v sb l2 → StartL ... (l1 ++ l2)
inductive AcceptMsgsL : List Val → Input → List Val → Log → Prop
  -- seq_recv_l: RecvL c x v l → AcceptMsgsL cs x ms ls → AcceptMsgsL (c :: cs) x (v :: ms) (l ++ ls)
inductive StepL (PE) (r) : Config → Option Event → Config → Log → Prop
  -- r_p_update_l: logs l1 (update v1), l2 (v2 v), l3 (subscriptions v'), log l1 ++ l2 ++ l3
  -- r_p_proc_step_l, _sleep_l, _spawn_l, _kill_l: the log of TaskRedL
  -- r_p_proc_message_l: the log of RecvL
  -- r_p_in_accept_l: AcceptMsgsL's log (its Dec premise has no log, plan D4)
  -- r_p_proc_end_l, r_p_in_reject_l, r_p_out_l, r_p_wait_l, r_p_platform_l: []
```

The premise order is the order in which the rule writes its premises (D4). `AcceptMsgsL` logs the
leaves in the order of the enumeration `L`.

### Host, executions, logs, traces (`Prog/Exec.lean`)

```lean
/-- The host model. `any` is the book's: the host may send any value on any incoming port at
    any time (r:p-in-accept, r:p-in-reject). `none` sends nothing. `echo o i` is the test
    runner's launcher (runner/run.js, `launcher`): every value delivered on o is sent back on i,
    in order, and nothing else is sent. -/
inductive Host where
  | any
  | none
  | echo (outPort inPort : String)

/-- The host state is the list of values delivered on the echo's outgoing port and not yet sent
    back. `HostAllows h hs ℓ hs'`: with host h in state hs, the event ℓ may happen, leaving hs'. -/
inductive HostAllows : Host → List BVal → Option Event → List BVal → Prop where
  | any (hs a) : HostAllows .any hs a hs
  | silent (h hs) : HostAllows h hs none hs
  | act (h hs x) : HostAllows h hs (some (.act x)) hs
  | wait (h hs d) : HostAllows h hs (some (.wait d)) hs
  | out_none (hs p j) : HostAllows .none hs (some (.out p j)) hs
  | out_echo (o i hs j) : HostAllows (.echo o i) hs (some (.out o j)) (hs ++ [j])
  | out_other (o i p hs j) : p ≠ o → HostAllows (.echo o i) hs (some (.out p j)) hs
  | in_echo (o i j hs) : HostAllows (.echo o i) (j :: hs) (some (.inn i j)) hs

/-- An execution path: each step's event, log and resulting configuration. -/
abbrev PathL := List (Option Event × Log × Config)
abbrev Path  := List (Option Event × Config)

inductive ExecL (PE) (r) (h : Host) : Config → List BVal → PathL → List BVal → Prop where
  | nil (K hs) : ExecL PE r h K hs [] hs
  | cons (K hs a l K' hs' π hs'') :
      StepL PE r K a K' l → HostAllows h hs a hs' → ExecL PE r h K' hs' π hs'' →
      ExecL PE r h K hs ((a, l, K') :: π) hs''

inductive Exec (PE) (r) (h : Host) : Config → List BVal → Path → List BVal → Prop
  -- the same with Step and without logs

def PathL.log (π : PathL) : Log := (π.map (·.2.1)).join
def PathL.forgetLog (π : PathL) : Path := π.map fun (a, _, K) => (a, K)

/-- The executions of a worker program (its modules ms, flags type τ1) with flags j under host
    h, in basis B, with their logs: the log of the evaluation of the modules, then of the start,
    then of each step (D9; review G1-9). -/
def WorkerExec (B : Mod.Basis) (ms : List Mod.Module) (τ1 : PTy) (j : BVal) (h : Host) (lg : Log) : Prop :=
  ∃ r lm K0 ls π hs, Mod.EvalProgramL B ms (.prog r) lm ∧ StartL (portEnv ms) τ1 j r K0 ls ∧
    ExecL (portEnv ms) r h K0 [] π hs ∧ lg = lm ++ ls ++ π.log

/-- Observable events (sec:programs-behaviour): In, Out, wait, and actions of platform
    primitives; the actions of sleep, spawn and kill are not observable. -/
def Event.observable : Event → Bool
  | .inn .. | .out .. | .wait _ => true
  | .act x => decide (x.prim ∈ platPrims)
def trace (π : Path) : List Event := π.filterMap fun (a, _) => a.filter Event.observable

/-- Tr(program, j): the traces of the executions with flags j. The book's executions are those
    of `Host.any`. -/
def Tr (B : Mod.Basis) (ms : List Mod.Module) (τ1 : PTy) (j : BVal) (tr : List Event) : Prop :=
  ∃ r K0 π hs, Mod.EvalProgram B ms (.prog r) ∧ Start (portEnv ms) τ1 j r K0 ∧
    Exec (portEnv ms) r .any K0 [] π hs ∧ trace π = tr
```

### Scheduler (`Prog/Sched.lean`)

The scheduler is a deterministic function that builds one execution. Its choices are explicit;
a default strategy models Elm/JS (Appendix E, `appendix-implementation.tex`,
`sec:appendix-implementation-platform`), and a test may override any choice by its index.

```lean
/-- Order of the leaves of one command or subscription when it is dispatched or receives a
    value. `reversed` is Elm/JS's and eco's (Appendix E, "The Order of Commands": a manager
    receives the commands of a batch in reverse order; several subscriptions to one port receive
    a value last first). -/
inductive LeafOrder where | listed | reversed

inductive Choice where
  | update               -- r:p-update on the head message
  | proc (n : Nat)       -- the next transition of process n (step, sleep, spawn, kill, message, end)
  | out (p : String)     -- r:p-out on port p
  | inn                  -- the echo host sends back its oldest pending value (r:p-in-accept/-reject)
  | wait (d : Rat)       -- r:p-wait
  | wake                 -- bookkeeping: move processes whose sleep is due into the run queue
  | stop

structure SchedConfig where
  leafOrder : LeafOrder := .reversed
  overrides : List (Nat × Choice) := []    -- (scheduler iteration index, choice)

structure Ctx where
  PE   : PortEnv
  r    : List (String × Val)
  host : Host
  cfg  : SchedConfig
  fuelEval : Nat := fuelT                  -- fuel of each application (Theorems.lean's 100000)

structure SchedState where
  K        : Config
  hs       : List BVal                    -- host state
  rq       : List Nat                     -- run queue, FIFO
  sleepers : List (Nat × Option Rat)      -- processes blocked at a sleep, with their deadline
                                          -- (none: a non-finite delay, due at once)
  oracle   : Oracle                       -- Oracle.const false by default ("oracle false")
  next     : Nat                          -- the oracle index, threaded through every application
  idx      : Nat

/-- One transition, as the scheduler took it. -/
structure Taken where
  ev  : Option Event
  log : Log
  K'  : Config
  hs' : List BVal
```

The default strategy, in priority order:

```lean
def defaultChoice (c : Ctx) (st : SchedState) : Choice :=
  -- 1. immediate echo: the echo host sends back what it has received
  if c.host matches .echo .. && !st.hs.isEmpty then .inn
  -- 2. deliver outgoing values, ports in the order of PE
  else match st.K.outq.find? (fun (_, js) => !js.isEmpty) with
  | some (p, _) => .out p
  | none =>
  -- 3. handle the oldest message (Elm/JS runs update as soon as a message is sent to the app)
  if !st.K.msgs.isEmpty then .update
  -- 4. run the process at the head of the FIFO run queue
  else match st.rq with
  | n :: _ => .proc n
  | [] =>
  -- 5. a sleeping process whose deadline has come joins the run queue
  if st.sleepers.any (fun (_, d) => d.all (· ≤ st.K.time)) then .wake
  -- 6. let time pass to the earliest deadline
  else match minDeadline st.sleepers with
  | some D => .wait (D - st.K.time)
  -- 7. nothing can happen without the host or the platform: stop
  | none => .stop
```

`doChoice c st ch : Outcome (Option Taken × SchedState)` performs the choice. For each choice:

| Choice | Precondition (else `stuck`) | Transition (rule) | Run queue and sleepers afterwards |
|--------|----------------------------|-------------------|-----------------------------------|
| `update` | `msgs = v1 :: M`; the three applications have values (`appVal`), `flat cm = some cs` | `r:p-update` with `L = order cs`, fresh identifiers by `dispatchFn` | new processes appended in creation order |
| `proc n`, task `succeed v`, origin `some c` | `recvL c (.val v)` has a value | `r:p-proc-message` | `n` removed |
| `proc n`, task `fail v`, or `succeed v` with origin `none` | | `r:p-proc-end` | `n` removed |
| `proc n`, silent reduction by `stepTaskL` | | `r:p-proc-step` | `n` stays at the head (a process runs until it waits, as in both implementations, Appendix E "Processes") |
| `proc n`, reduction labelled `sleep [x]`, ready (`SleepReady`) | | `r:p-proc-sleep` | `n` moved to the back |
| `proc n`, labelled `sleep [x]`, not ready | | none (bookkeeping) | `n` moved to `sleepers` with deadline `s' + max(0, q)` |
| `proc n`, labelled `spawn [t0]`, outcome `pid (freshPid P)` | | `r:p-proc-spawn` | child appended, then `n` moved to the back (Elm/JS enqueues the child, then resumes the parent) |
| `proc n`, labelled `kill [pid n']` | | `r:p-proc-kill` | `n'` removed from both lists; `n` moved to the back |
| `out p` | `Q(p) = j :: J` | `r:p-out`; host state by `HostAllows` | unchanged |
| `inn` | host `echo o i`, `hs = j :: rest`, `PE(i) = (in, τ)` | `r:p-in-accept` (if `dec τ j = some _`; messages by `recvL` per leaf of `order (flat sb)`, `recvNone` giving none) or `r:p-in-reject` | unchanged |
| `wait d` | `0 < d` | `r:p-wait` | unchanged |
| `wake` | | none | due sleepers appended to the run queue, by deadline then identifier |
| `stop` | | none | the run ends |

`order` is `id` for `listed` and `List.reverse` for `reversed`. After every transition the run
queue and the sleepers are filtered to identifiers whose entry in `P` is live.

```lean
def startFn (PE : PortEnv) (τ1 : PTy) (j : BVal) (r : List (String × Val)) (lo : LeafOrder)
    (o : Oracle) (k : Nat) : Res (Config × List Nat)

inductive RunStatus where | quiescent | outOfFuel | stuck
structure RunResult where
  path   : PathL
  hs     : List BVal
  status : RunStatus

/-- Run at most n scheduler iterations. An override at the current index replaces the default. -/
def run (c : Ctx) : Nat → SchedState → PathL → RunResult
```

### Worker tests (`Prog/Worker.lean`)

```lean
structure WorkerTest where
  prog      : Mod.ModProgram                 -- step 3's: modules, checks, native
  flagsType : PTy                            -- τ1, from main's type ([elab])
  flags     : BVal := .null                  -- absent flags are null (A72)
  host   : Host := .none
  sched  : SchedConfig := {}
  fuel   : Nat := 5000                      -- scheduler iterations
  checks : List LogCheck

/-- D9 for a worker: some execution the book allows, under the test's host, has a log that
    satisfies every check (existential: the book allows what the test expects). -/
def WorkerTest.Holds (w : WorkerTest) : Prop :=
  ∃ lg, WorkerExec (Btest []) w.prog.modules w.flagsType w.flags w.host lg ∧
    ∀ ck ∈ w.checks, LogCheck.Holds lg ck

def runWorker (w : WorkerTest) : Option (Log × RunResult)
  -- evProgram (.const false) fuelT (Btest []) w.prog.modules 0; main's value must be `.prog r`;
  -- startFn (portEnv w.prog.modules) w.flagsType w.flags r; run; the log lm ++ ls ++ res.path.log

def WorkerTest.checkB (w : WorkerTest) : Bool :=
  match runWorker w with
  | some (lg, _) => w.checks.all (LogCheck.check lg)
  | none => false
```

## Theorems

### Logged and book relations

```lean
theorem StepL.forget : StepL PE r K a K' l → Step PE r K a K'
theorem Step.lift    : Step PE r K a K' → ∃ l, StepL PE r K a K' l
theorem StartL.forget : StartL PE τ j r K l → Start PE τ j r K      -- and Start.lift
theorem ExecL.forget : ExecL PE r h K hs π hs' → Exec PE r h K hs π.forgetLog hs'
theorem Exec.lift    : Exec PE r h K hs π hs' → ∃ πl, ExecL PE r h K hs πl hs' ∧ πl.forgetLog = π
```

Method: `cases` on the step, using step 1's `AppValL.forget`/`AppVal.lift` and step 4's
`TaskRedL`, `RecvL` forget/lift; `AcceptMsgsL` by induction; executions by induction on
the path. The parity test gains `Start/StartL`, `Step/StepL`, `AcceptMsgs/AcceptMsgsL`.

### Soundness of the scheduler

```lean
theorem dispatchFn_sound : dispatchFn s P Q L = some (P', Q', ns) → Dispatch s P Q H L P' Q' H
theorem startFn_sound : (startFn PE τ j r lo o k).out = .value (K, ns) → StartL PE τ j r K (startFn PE τ j r lo o k).log
theorem doChoice_sound : doChoice c st ch = .value (some t, st') →
    StepL c.PE c.r st.K t.ev t.K' t.log ∧ HostAllows c.host st.hs t.ev t.hs' ∧
    st'.K = t.K' ∧ st'.hs = t.hs'
theorem doChoice_bookkeeping : doChoice c st ch = .value (none, st') → st'.K = st.K ∧ st'.hs = st.hs
theorem run_sound : run c n st [] = res → ExecL c.PE c.r c.host st.K st.hs res.path res.hs
theorem runWorker_sound : runWorker w = some (lg, res) →
    WorkerExec (Btest []) w.prog.modules w.flagsType w.flags w.host lg
theorem holds_of_run : w.checkB = true → w.Holds
```

Method: `doChoice_sound` case by case on the choice, each case assembling the rule's constructor
from `appVal_sound`, `stepTaskL_sound`, `recvL_sound`, `recvNone_sound` (for `seq_none`),
`dec_iff`, `dispatchFn_sound`, `freshPid_fresh`, and `List.perm_reverse` (for `L.Perm cs` with
`L = cs.reverse`). `run_sound` by induction on the fuel with an accumulator lemma (the path built
so far, reversed, is an execution from the initial configuration to the current one).
`holds_of_run`: `runWorker_sound` and `LogCheck.check_sound`. The status of the run does not
matter: every finite prefix of transitions is an execution (`sec:programs-behaviour`).

### Traces

```lean
theorem tr_prefix : Tr B ms τ1 j tr → tr' <+: tr → Tr B ms τ1 j tr'
theorem tr_nil : (∃ r K0, Mod.EvalProgram B ms (.prog r) ∧ Start (portEnv ms) τ1 j r K0) → Tr B ms τ1 j []
theorem tr_empty_iff_no_start : (∀ tr, ¬ Tr B ms τ1 j tr) ↔
    ¬ ∃ r K0, Mod.EvalProgram B ms (.prog r) ∧ Start (portEnv ms) τ1 j r K0
```

Method: truncate the path at the shortest prefix whose trace is `tr'` (induction on the path,
`trace` of a prefix is a prefix of `trace`).

### The guarantees of A86 (`sec:programs-execution`, the property after the transition rules)

```lean
/-- Messages are handled one at a time, by r:p-update, in queue order, each update applying
    update to the model of the previous one; every other step keeps the model and only appends
    to the queue. The commands of an update are dispatched in its step. -/
theorem a86_step (h : Step PE r K a K') :
    (K'.model = K.model ∧ ∃ ms, K'.msgs = K.msgs ++ ms) ∨
    (a = none ∧ ∃ v1 fu v2 cm cs L, K.msgs = v1 :: K'.msgs ∧ field r "update" = some fu ∧
       AppVal fu v1 v2 ∧ AppVal v2 K.model (.tuple K'.model cm none) ∧
       flat cm = some cs ∧ L.Perm cs ∧
       Dispatch K.time K.procs K.outq K.pending L K'.procs K'.outq K'.pending)

/-- The values of each outgoing port are delivered in the order in which they joined its queue:
    over any execution, what is delivered on p, followed by what remains queued, is what was
    queued at the start followed by what each step appended, in step order. -/
theorem a86_out_fifo (h : Exec PE r hst K hs π hs') (p : String) :
    outsOn p π ++ (lastConfig K π).outq.get p = K.outq.get p ++ appendedOn p K π
```

where `outsOn p π` lists the `j` of the events `Out(p, j)` of `π` in order, `lastConfig K π` is the
final configuration, and `appendedOn p K π` concatenates, for each step from `K_i` to `K_{i+1}`
not labelled `Out(p, _)`, the suffix `(K_{i+1}.outq.get p).drop (K_i.outq.get p).length`.

Method: `a86_step` by `cases` on `Step` (the platform case is empty; the dispatch case by a lemma
`dispatch_msgs_model`, dispatch touches neither). `a86_out_fifo` by induction on the path, with
the per-step lemma

```lean
theorem step_outq (h : Step PE r K a K') (p : String) :
    (a = some (.out p (K.outq.get p).head!) ∧ K.outq.get p = (K.outq.get p).head! :: K'.outq.get p) ∨
    (∀ j, a ≠ some (.out p j)) ∧ ∃ new, K'.outq.get p = K.outq.get p ++ new
```

(dispatch appends by `r:p-disp-out`; `r:p-out` on another port leaves `p`'s queue).

"Apart from these ... interleave in every way the rules allow" is a statement that there are no
further guarantees; it is not a theorem. It is illustrated by `a66_batch_order_open` below.

### Rulings

```lean
-- A62: an update with no result ends message handling; other steps go on.
theorem a62_no_update (hK : K.msgs = v1 :: M) (hfu : field r "update" = some fu)
    (hno : ¬ ∃ v2 w, AppVal fu v1 v2 ∧ AppVal v2 K.model w) (h : Exec PE r hst K hs π hs') :
    ∀ K' ∈ π.map (·.2), K'.model = K.model ∧ ∃ ms, K'.msgs = K.msgs ++ ms
theorem a62_wait_continues : ∀ K, ∃ K', Step PE r K (some (.wait 1)) K'
/-- A concrete program whose update is \_ _ -> Debug.todo "stop": no update step exists. -/
theorem a62_example : ¬ ∃ v2 w, AppVal a62Update (.con a62Msg []) v2 ∧ AppVal v2 .unit w

-- A77: unit flags accept every boundary value; a unit port only null.
theorem a77_flags_unit (j : BVal) : FlagsVal .unit j .unit
theorem a77_port_unit : Dec .unit j v ↔ j = .null ∧ v = .unit
theorem a77_start_any_flags : Start PE .unit j r K ↔ Start PE .unit j' r K

-- A72: absent flags are null; with Maybe flags the program starts with Nothing.
theorem a72_maybe_null : FlagsVal (.maybe τ) .null (.con conNothing [])

-- A79: a failing process ends, whatever its origin, and nothing else happens.
theorem a79_fail_ends (hp : K.procs.get n = some (.live ⟨.fail v, s', o⟩)) :
    Step PE r K none { K with procs := K.procs.set n .ended }
theorem a79_spawned_succeed_ends (hp : K.procs.get n = some (.live ⟨.succeed v, s', none⟩)) :
    Step PE r K none { K with procs := K.procs.set n .ended }
theorem a79_nothing_else (h : Step PE r K a K') (h1 : K.procs.get n = some (.live ⟨t, s', none⟩))
    (h2 : K'.procs.get n = some .ended) : K'.msgs = K.msgs ∧ K'.model = K.model

-- A80: killing an ended process changes nothing but the killer's own entry.
theorem a80_kill_ended (h : Step PE r K (some (.act ⟨.kill, [.pid n'], t⟩)) K')
    (hk : K.procs.get n' = some .ended) :
    ∃ n, ∀ q, q ≠ n → K'.procs.get q = K.procs.get q

-- A81: the sleep action is no sooner than max(0, d) after the process reached the sleep;
-- no upper bound; no condition for a non-finite delay.
theorem a81_lower (h : Step PE r K (some (.act ⟨.sleep, [.sv (.float x)], t⟩)) K')
    (hq : floatToRat? x = some q) :
    ∃ n tk s' o, K.procs.get n = some (.live ⟨tk, s', o⟩) ∧ s' + (if q < 0 then 0 else q) ≤ K.time
theorem a81_any_later (hp : K.procs.get n = some (.live ⟨tk, s', o⟩))
    (hr : TaskRed tk (some ⟨.sleep, [.sv (.float x)], t⟩) tk') (hq : floatToRat? x = some q)
    (d : Rat) (hd : 0 < d) (hge : s' + (if q < 0 then 0 else q) ≤ K.time + d) :
    ∃ K1 K2, Step PE r K (some (.wait d)) K1 ∧ Step PE r K1 (some (.act ⟨.sleep, [.sv (.float x)], t⟩)) K2
theorem a81_nonfinite (hp : K.procs.get n = some (.live ⟨tk, s', o⟩))
    (hr : TaskRed tk (some ⟨.sleep, [.sv (.float x)], t⟩) tk') (hq : floatToRat? x = none) :
    ∃ K', Step PE r K (some (.act ⟨.sleep, [.sv (.float x)], t⟩)) K'

-- A66 (the "no other guarantee" of A86, illustrated): the program
--   init _ = ((), Cmd.batch [out 1, out 2]) with port out : Int -> Cmd msg
-- has executions delivering 1 then 2, and 2 then 1.
theorem a66_batch_order_open :
    (∃ π hs, ExecL a66PE a66r .none a66K0 [] π hs ∧ outsOn "out" π.forgetLog = [.num 1, .num 2]) ∧
    (∃ π hs, ExecL a66PE a66r .none a66K0 [] π hs ∧ outsOn "out" π.forgetLog = [.num 2, .num 1])
```

Methods. `a62_no_update`: induction on the execution with `a86_step`; the update disjunct
contradicts `hno` (the model is unchanged by every other step, so the head message and model are
still `v1` and `K.model`). `a62_example`: `appVal_noValue_of_stuck` with a kernel computation
of `appVal (.const false) fuelT a62Update m 0` reaching `Debug.todo`, then the same for the
closure it returns, with the index unchanged. `a77_*`: unfold `FlagsVal`, `dec_iff`. `a79_*`, `a80_kill_ended`:
constructors and `cases` on `Step` (proc-message needs origin `some`; dispatch only adds fresh
identifiers, lemma `dispatch_preserves_existing`); `a80` from the lemma
`fmLookup ((P.set n' .ended).set n e) q = fmLookup P q` when `q ≠ n` and `P.get n' = some .ended`
(for `q = n'` the entry is `ended` before and after). `a81_*`: the rules directly
(`r_p_wait`, then `r_p_proc_sleep` with `SleepReady` from `hge`). `a66_batch_order_open`: two runs
of the scheduler with `leafOrder := .listed` and `.reversed`, decided by the kernel, and
`run_sound`.

## Translator changes

All in `definition/tools/src/Translate/`; each with unit tests in
`definition/tools/tests/TranslateTest.elm`.

1. **Directives** (`Directives.elm`). `-- FLAGS:` no longer maps to the refusal `effects`. Its
   text is parsed by a new module `Translate/Json.elm`: an RFC 8259 parser over the raw string
   that never converts a number to an Elm `Float` (Elm's numbers are binary64, inexact for large
   integers and decimals). A number is kept as its parts, giving `jnum m e` with `m` and `e`
   written as decimal digit strings: `42` → `jnum 42 0`; `-1.5e3` → `jnum (-15) 2`; `0.1` →
   `jnum 1 (-1)`; `-0` → `jnum 0 0` (A88: no sign). Leading zeros of `m` are dropped. Objects are
   written through `BVal.mkObj` (so a duplicate key's last value wins and keys are sorted by
   the Lean side), arrays as `.arr [...]`, strings with Lean escapes. Absent flags are written
   `.null` (A72), whatever the launcher does (it passes `undefined`; the test's page says so).
2. **Worker programs** (`Convert.elm`, `Infer.elm`, `Basis.elm`). Step 3's refusal
   `effects:worker` is lifted for programs whose `main` has type `Program τ1 τ2 τ3`, and the
   refusal `effects` for the qualified names of `Task`, `Process`, `Cmd`, `Sub` and `Platform`
   (resolved through `ME0`, which has `Task` and `Process` from step 4). `Basis.elm` gains the static
   interfaces of Appendix C (`appendix-static-basis.tex`, Figures `fig:static-basis-platform`,
   `fig:static-basis-task`, `fig:static-basis-effects`): the type names `Cmd` (1), `Sub` (1),
   `Task` (2, also `Platform.Task`), `Process.Id` (0, also `Platform.ProcessId`), `Program` (3),
   and the schemes of `Platform.worker`, `Cmd.none`, `Cmd.batch`, `Cmd.map`, `Sub.none`,
   `Sub.batch`, `Sub.map`, `Task.succeed`, `fail`, `andThen`, `onError`, `map` to `map5`,
   `sequence`, `mapError`, `perform`, `attempt`, `Process.spawn`, `sleep`, `kill`, each checked
   by hand against the figure and dated in the module's docstring as today's entries are. Infer
   gives `main`'s type; the flags type τ1 must be a payload type (`fig:static-modules-port`), or
   the test is refused `construct:flags-type`. τ1 is written as a `PTy` with record fields sorted
   by label. Number specialisation is unchanged (`Process.sleep 300` makes `300` a Float
   constant, `intF 300`).
3. **The program kind.** `ModProgram.kind` is `.worker` for `Program`, `.view` for `Html`.
4. **The host.** `host := .echo "echoOut" "echoIn"` when the program declares an outgoing port
   `echoOut` and an incoming port `echoIn` and refers to both outside their declarations (the
   launcher installs the echo only when `app.ports.echoOut && app.ports.echoIn`, and Elm/JS omits
   an unreferenced port from `app.ports`); otherwise `.none`.
5. **Checks.** As step 3's log checks (D9). `CHECK-NOT` lines stay refused (`checks:check-not`)
   until step 6, except StandardA81SleepBeyond32BitsTest, whose `CHECK-NOT: the long sleep ended`
   is dropped by a list `checkNotsNotRequired` in `Directives.elm`, with the reason "finding T1:
   r:p-wait lets the long sleep end before the kill; not required by the book".
6. **Choices.** A new data file `definition/mechanisation/worker-choices.json`, initially `{}`,
   read by the translator:

   ```json
   {
     "elm-core/SomeTest": {
       "leafOrder": "reversed",
       "fuel": 5000,
       "overrides": [ { "at": 12, "choice": { "wait": "3000000000" } },
                      { "at": 13, "choice": { "proc": 2 } } ]
     }
   }
   ```

   A choice is `"update"`, `"in"`, `"wake"`, `"stop"`, `{"proc": n}`, `{"out": "port"}` or
   `{"wait": "<decimal>"}` (a decimal string, written as `jnum`). No step-5 test is expected to
   need an entry; one is added only when the default strategy fails a test's checks, with a
   comment in the step's report saying why.
7. **Output.** Workers go to their own shard, `Generated/Worker01.lean` (35 programs, at most 40),
   and `Generated/ChecksWorker01.lean`. For each:

   ```lean
   /-- tests/elm/src/PortEchoTest.elm -/
   def g_elm_PortEchoTest : Mod.ModProgram := { ... }   -- step 3's format, unchanged
   def w_elm_PortEchoTest : Prog.WorkerTest where
     prog      := g_elm_PortEchoTest
     flagsType := .unit
     flags     := .null
     host      := .echo "echoOut" "echoIn"
     checks    := [ .has (.entry "PortEchoTest got" (.int 42)), .has (.entry "PortEchoTest done" (.str "ok")) ]
   def workers01 : List Prog.WorkerTest := [w_elm_PortEchoTest, ...]
   ```

   The Checks shard runs a new generator command, `#worker_theorems workers01`, defined in
   `Theorems.lean` beside step 3's `#mod_program_theorems` and written the same way: for each
   `WorkerTest` it emits

   ```lean
   /-- tests/elm/src/PortEchoTest.elm  [parse] [elab] [harness] [params] -/
   theorem t_elm_PortEchoTest : w_elm_PortEchoTest.Holds :=
     Prog.holds_of_run (by decide +kernel)
   ```

   or `(by native_decide)` (and the tag `[native]`) for a test marked native. The checks are
   written literally (as step 3 writes them), by step 3's `toLogChecks`.
8. **Kernel or native.** A worker test is native when the existing rule marks it (`Specialise.elm`,
   `nativeValues`: it uses `Debug.toString` or a C-library float function) or when it is listed in
   a new list `kernelTooLarge` in `Specialise.elm` (initially empty; filled only from a measured
   breach of the memory budget, each entry dated with its peak). By the existing rule five are
   native: ProcessSpawnKillHalfTest, ProcessSpawnRecursiveTest, ProcessYieldThrashingTest,
   TaskOnErrorCascadeTest, TimerEffectTest (all use `Debug.toString`). The other 30 are expected
   to be kernel theorems.
9. **Manifest.** Entries gain `kind` (`"view"` or `"worker"`), `host` (`"none"` or `"echo"`),
   `flags` (the JSON text or `null`), `native` (Boolean), and for the A81 test
   `dropped: ["CHECK-NOT: the long sleep ended (finding T1)"]`.
10. **run-examples** (`Main.lean`). For each worker test, run `runWorker` (compiled), print the
    run's status and, for each check, whether `check` holds of the log; count them in `N` and
    report a failing check as a divergence.

## Tests gained

35 tests (34 with all their checks, one with its positive check only), 116 checks
(`CHECK` and `CHECK-DAG` lines). `CHECK-DAG` is read as `CHECK` (D9).

`tests/elm/src` (19): CoreIssue1141UnusedPortCallBreaksSubscriptionTest, FlagsRecordTest,
ListLiteralDebugLogKindTest, NoImportsTest, OutgoingPortTuple3KeepsRunningTest,
OutgoingPortTuple3Test, PortAliasEchoTest, PortEchoBoolTest, PortEchoFloatTest,
PortEchoListIntTest, PortEchoMaybeIntTest, PortEchoNestedTest, PortEchoStringTest, PortEchoTest,
PortEchoTuple2Test, PortEchoTuple3Test, PortEchoUnitTest, StandardA72AbsentFlagsTest,
StandardA88PortNegativeZeroTest.

`tests/elm-core/src` (16): CmdMapComposeTest, CoreIssue1110PortDeclarationOrderTest,
CoreIssue1154PortSubscribedWithCmdTest, CoreIssue955KillProcessTwiceTest,
ProcessPrimitiveOutcomeTest, ProcessSpawnKillHalfTest, ProcessSpawnRecursiveTest,
ProcessSpawnedFailureEndsTest, ProcessYieldThrashingTest, StandardA81SleepBeyond32BitsTest
(positive check only), TaskAttemptErrorTest, TaskOnErrorCascadeTest, TaskOnErrorInnerTest,
TaskPerformValueTest, TaskSucceedAsArgTest, TimerEffectTest.

Two of these need no transition: ListLiteralDebugLogKindTest logs while its top-level value
`report` is evaluated (the module log), and NoImportsTest logs in `init` (the start log). Their
theorems hold with the empty path.

Not gained, as the plan says: PortEchoArrayStringTest, PortEchoJsonValueTest,
StandardA92BytesPortTest (library values), CoreIssue1123NestedCmdBatchStackOverflowTest (size,
finding T2).

## Acceptance

Commands as in [conventions.md](conventions.md). Expected, relative to the counts after step 4:

- Translator: `elm-spec tests: 939, translated: T + 35`, where T is the count after step 3 (575 if
  steps 2 and 3 delivered their 49); afterwards no test is refused `effects`: the four workers
  not gained are refused for their library values (`basis:*` or `import:*`) or their size
  (`construct:large-computation`), and the three `CHECK-NOT` workers of step 6 stay refused
  `checks:check-not`; `--check` reports the translations up to date; `elm-test` passes
  with the new unit tests (Json numerals: `42`, `-0`, `1e300`, `-1.5e3`, `0.1`,
  `123456789012345678901`; object key order; flags type of FlagsRecordTest; host detection of
  PortEchoTest and OutgoingPortTuple3Test).
- `lake build`: no `sorry`, no new warnings.
- `lake exe run-examples`: `N + 116` checks, all agreeing, 0 diverging; `K + 30` theorems by
  `decide +kernel`, and 5 more native theorems (fewer kernel and more native only for tests named
  in `kernelTooLarge`, each listed in the report).
- `scripts/check-axioms.lean`: the 30 kernel worker theorems and every theorem of this step's hand
  files use only the three standard axioms; the 5 native ones also `Lean.ofReduceBool` (and
  `Lean.trustCompiler` where the toolchain adds it).
- Parity test: `Start/StartL` (1), `Step/StepL` (12), `AcceptMsgs/AcceptMsgsL`.
- The theorems of this specification exist and are proved: forget/lift, `doChoice_sound`,
  `run_sound`, `runWorker_sound`, `holds_of_run`, `tr_prefix`, `tr_nil`, `a86_step`,
  `a86_out_fifo`, the A62, A72, A77, A79, A80, A81 theorems and `a66_batch_order_open`.
- Memory: the clean build within the budget; `ChecksWorker01.lean` measured on its own (peak
  reported).
- `pnpm test:all` and `node runner/check-baseline.js` unchanged.
- Site: rule pages of the 17 rules `r:p-disp-*`, `r:p-init` and the transitions link to their
  constructors (`r_p_<slug>`); the test pages of the 35 tests show their theorems with the trust
  tags `[parse] [elab] [harness] [params]` (and `[native]` for the five), and the A81 test's page
  says its `CHECK-NOT` is not stated (finding T1). Link audit 0 problems.
- Reports: mechanisation report update (counts, the 5 native, any override used), README (Files
  table rows for the eight new files, the count "N of the 939 today"), the preface sentence, the
  plan's status line.

## Risks and fallbacks

- **Kernel cost of whole runs.** A worker theorem evaluates the program's modules, the Task texts
  and every step of a run in the kernel. ProcessSpawnKillHalfTest and ProcessYieldThrashingTest
  are the largest (both native already). If a kernel worker theorem breaks the budget, it moves to
  `kernelTooLarge` (native only), never to a larger shard.
- **The default strategy fails a test.** The checks are existential and only ask for presence of
  log entries (one `CHECK-NEXT` in step 6), so any execution reaching quiescence logs the same
  entries for every test above; a failure means a bug in the scheduler or the translation, or a
  test that needs a particular interleaving. In the last case an override is added to
  `worker-choices.json` and reported.
- **Fuel.** 5000 scheduler iterations by default; TimerEffectTest needs about 60, the spawn tests a
  few hundred. A run that ends `outOfFuel` still yields an execution (its prefix), so the
  theorem can hold; the check fails only if the needed entry comes later, and the fuel is raised
  per test in `worker-choices.json`.
- **Step 3's program format.** If step 3 does not carry the flags type and ports in `ModProgram`,
  they are added there (it is translator work that step 3 already does for port views).

## Issues with the plan

*Disposition (2026-11-11): each issue below has been answered in [the plan](../lean-full-definition.md), section "Issues the specifications raised, and their disposition", either by a change to the plan or as settled here. Where this section and the plan differ, the plan wins.*

1. **The default order of a batch.** The brief for this specification (and review item G1-7 of
   `part1.md`) asks for "batch leaves in list order" as modelling Elm/JS, "as Appendix E records".
   Appendix E (`appendix-implementation.tex`, "The Order of Commands") records the opposite: Elm/JS
   and eco give a manager the commands of a batch in reverse order, and several subscriptions to
   one port receive a value last first. The plan file itself fixes no order. This specification
   makes the order a field of `SchedConfig` with default `reversed`, because the default strategy
   is meant to model Elm/JS; `listed` is available per test. No test gained here depends on the
   order (every check is presence of an entry), so either default gives the same theorems.
2. **Conformance.** The plan's goal mentions traces (from the previous draft, review G1-16) but
   not conformance. Conformance is a relation between the book and an implementation and has no
   Lean object here; it is declared out of scope above. Traces and `Tr` are in scope.
3. **Native tests.** The plan counts 35 tests for this step without saying how they are proved.
   Under the translator's existing rule (`Debug.toString` is native because the string is the
   implementation's and float printing is native), five are `native_decide` only. Debug.toString
   of an Int could be computed by the kernel; changing the rule is out of this step's scope and
   would change the existing view tests too.
4. **`HostAllows` needs a state.** The plan describes the echo host as "Out(echoOut, j) then
   In(echoIn, j)", and review F-21 proposed `HostAllows : HostModel → Label → Config → Prop`. Whether
   an `In` is allowed depends on the earlier `Out` events, not on the configuration (the queue
   `Q(echoOut)` is emptied by `r:p-out`), so the relation carries the host's own state, the list of
   values awaiting their echo. Followed in substance; the signature differs.

## Progress

**2026-11-11: done.**

- Lean: `Prog/Objects.lean`, `Prog/Dispatch.lean` (`dispatchFn_sound`), `Prog/Rules.lean` (`Start`,
  `Step` with 12 constructors, `AcceptMsgs`, their logged twins, forget and lift; the twin check
  covers all three), `Prog/Exec.lean` (`Host`, `HostAllows` with the host's own state, issue 4,
  `ExecL`, `Exec`, `WorkerExec`, `trace`, `Tr`, `tr_nil`, `tr_prefix`, `tr_empty_iff_no_start`),
  `Prog/Sched.lean` (`doChoice_sound`, `run_sound`; leaf order `reversed` by default, issue 1),
  `Prog/Worker.lean` (`startFn_sound`, `runWorker_sound`, `holds_of_run`), `Prog/Guarantees.lean`
  (`a86_step`, `step_outq`, `dispatch_outq`, `a86_out_fifo`) and `Prog/Rulings.lean` (`a62_no_update`,
  `a62_wait_continues`, `a62_example`, `a77_flags_unit`, `a77_port_unit`, `a77_start_any_flags`,
  `a72_maybe_null`, `a79_fail_ends`, `a79_spawned_succeed_ends`, `dispatch_preserves_existing`,
  `a79_nothing_else`, `a80_kill_ended`, `a81_lower`, `a81_any_later`, `a81_nonfinite`,
  `a66_batch_order_open`). The A62 and A66 programs are written in the notation of the
  generated tests and evaluated by the evaluator; their facts are decided by the kernel.
- Translator: `Translate/Json.elm` (exact numbers), `Translate/Choices.elm` (`worker-choices.json`,
  `{}`), the worker kind, flags and flags type, the echo host, `Directives.checkNotsNotRequired`,
  manifest fields `kind`, `native`, `host`, `flags`, `dropped`; Json.Encode and Json.Decode are
  library modules (their values refused `basis:*`), not effect modules. 107 unit tests.
- The 35 tests, 116 checks: 30 kernel theorems, 5 native (the five the specification names). The
  shard `Worker01` and `ChecksWorker01` (2.3 GB, 18 s). run-examples: 1,701 checks, 0 diverging.
- Two harness bugs fixed: `showStr` escapes as Elm/JS's `_Debug_addSlashes` does, and
  `Expect.parse` reads `\n`, `\t`, `\r`, `\v` and `\0` back (PortEchoStringTest failed before);
  `BVal.mkObj` sorts by insertion (`insertByKey`), as the kernel does not reduce `mergeSort`
  (FlagsRecordTest failed to reduce before).
- Site: 126 rules counted; theorems that name `r_p_*` link to their rule pages; worker test pages
  say the flags, the host, the trust tags and what is not stated. Link audit 0 problems.

Differences from this specification:
- `#worker_theorems` is in a file of its own, `WorkerTheorems.lean`, not `Theorems.lean`, so that
  the view shards do not import Chapter 9; it takes the worker tests by name, as
  `#mod_program_theorems` takes programs, and first runs each test with the compiled evaluator,
  so a run that misses a check is an error naming the test. The theorem states
  `({ w with checks := [...] } : Prog.WorkerTest).Holds`, the checks written literally.
- `kernelTooLarge` (empty) is in `Pipeline.elm`, where the test's name is known, beside
  `largeComputations`, to which CoreIssue1123NestedCmdBatchStackOverflowTest was added.
- The worker shard's list is `shard_Worker01`, and `All.lean` gains `generatedWorkerShards` and
  `generatedWorkers`.

