/-
  A Standard Definition of Elm? Mechanisation: the objects of execution (programs.tex, Figure
  fig:programs-objects), plan step 5.

  A configuration K = (s, v, M, P, sb, Q, H): the time, the model, the queue of messages, the
  processes, the subscriptions, the queues of outgoing ports and the pending platform commands.
  Finite maps are association lists; the multiset H is a list (no rule reads its order). The
  events are the host's In and Out, actions and waiting; the platform's events are absent (the
  empty platform, [params]).
-/
import StandardElmMech.Mod.Syntax
import StandardElmMech.Eff.Task

namespace StandardElm.Prog
open StandardElm StandardElm.Eff

/-- PE as the dynamic semantics reads it: each port name with its direction and payload type
    (Chapter 7's reduced syntax records them; [elab]). Port names are distinct (A84). -/
abbrev PortEnv := List (String × Mod.Dir × PTy)

/-- The ports a top-level declaration declares, in order. -/
def topDecPorts : Mod.TopDec → PortEnv
  | .port x d τ => [(x, d, τ)]
  | .seq a b => topDecPorts a ++ topDecPorts b
  | _ => []

/-- The ports of a program: the `port` top-level declarations of its modules, in order. -/
def portEnv (ms : List Mod.Module) : PortEnv := ms.flatMap fun m => topDecPorts m.body

/-- Time: milliseconds, a non-negative rational (D6). Non-negativity is an invariant: the start is
    at 0 and r:p-wait adds d > 0. -/
abbrev Time := Rat

/-- A live process: its task, the time of its latest step (or start), and its origin: the leaf
    command whose task it performs, or `none` for a spawned process. -/
structure Proc where
  task : Val
  time : Time
  origin : Option Val
  deriving Inhabited

inductive PEntry where
  | live (p : Proc)
  | ended
  deriving Inhabited

/-- ProcId -fin-> Proc, an association list (ProcId = Nat). -/
abbrev Procs := List (Nat × PEntry)
/-- Var -fin-> BVal*: the queue of each outgoing port. -/
abbrev OutQ := List (String × List BVal)
/-- H: the pending platform commands, a multiset as a list. -/
abbrev Pending := List Val

/-- K = (s, v, M, P, sb, Q, H). -/
structure Config where
  time : Time
  model : Val
  msgs : List Val
  procs : Procs
  subs : Val
  outq : OutQ
  pending : Pending
  deriving Inhabited

/-- Event (fig:programs-objects): In(p, j), Out(p, j), an action, wait d. -/
inductive Event where
  | inn (p : String) (j : BVal)
  | out (p : String) (j : BVal)
  | act (a : Action)
  | wait (d : Time)
  deriving Inhabited

/-- A lookup in a finite map with natural-number keys (process identifiers). -/
def natLookup {β : Type} : List (Nat × β) → Nat → Option β
  | [], _ => none
  | (k, v) :: rest, n => if k == n then some v else natLookup rest n

/-- f + {n ↦ e}: the binding of n replaced, the others kept. -/
def natSet {β : Type} (f : List (Nat × β)) (n : Nat) (e : β) : List (Nat × β) :=
  (n, e) :: f.filter (·.1 != n)

def Procs.get (P : Procs) (n : Nat) : Option PEntry := natLookup P n
def Procs.set (P : Procs) (n : Nat) (e : PEntry) : Procs := natSet P n e
def Procs.dom (P : Procs) : List Nat := P.map (·.1)

def OutQ.get (Q : OutQ) (p : String) : List BVal := (fmLookup Q p).getD []

/-- Q_init: an empty queue for every outgoing port of PE. -/
def qInit (PE : PortEnv) : OutQ :=
  PE.filterMap fun (p, d, _) => if d = .out then some (p, []) else none

/-- r(lab) for the record of a program value. -/
def field (r : List (String × Val)) (l : String) : Option Val := fmLookup r l

/-- The condition of r:p-proc-sleep: if v' is a finite float, s ≥ s' + max(0, v'). -/
def SleepReady (s s' : Time) (v' : Val) : Prop :=
  ∀ x q, v' = .sv (.float x) → floatToRat? x = some q → s' + (if q < 0 then 0 else q) ≤ s

theorem natLookup_natSet_self {β : Type} (f : List (Nat × β)) (n : Nat) (e : β) :
    natLookup (natSet f n e) n = some e := by
  simp [natSet, natLookup]

theorem natLookup_filter_ne {β : Type} : ∀ (f : List (Nat × β)) (n q : Nat), q ≠ n →
    natLookup (f.filter (·.1 != n)) q = natLookup f q
  | [], _, _, _ => rfl
  | (k, v) :: rest, n, q, h => by
    by_cases hk : k = n
    · subst hk
      have : (k == q) = false := by simpa using Ne.symm h
      simp [natLookup, this, natLookup_filter_ne rest k q h]
    · have hk' : (k != n) = true := by simpa using hk
      simp only [List.filter_cons, hk', ite_true, natLookup]
      split
      · rfl
      · exact natLookup_filter_ne rest n q h

theorem natLookup_natSet_other {β : Type} (f : List (Nat × β)) (n q : Nat) (e : β) (h : q ≠ n) :
    natLookup (natSet f n e) q = natLookup f q := by
  have hn : (n == q) = false := by simpa using Ne.symm h
  simp only [natSet, natLookup, hn]
  exact natLookup_filter_ne f n q h

end StandardElm.Prog
