/-
  A Standard Definition of Elm? Mechanisation: hosts, executions, their logs, and traces
  (programs.tex, sec:programs-execution and sec:programs-behaviour), plan step 5.

  An execution is a sequence of transitions from a start configuration, each allowed by the host.
  `Host.any` is the book's (the host may send any value on any incoming port at any time); `none`
  sends nothing; `echo o i` is the test runner's launcher, which sends back on i, in order, every
  value delivered on o. The host carries its own state: the values delivered on o and not yet
  sent back. The log of a worker's execution is the log of the evaluation of its modules, then of
  its start, then of each step (D9). Tr(program, j) is the set of traces of the executions under
  `Host.any`.
-/
import StandardElmMech.Prog.Rules
import StandardElmMech.Mod.RulesL

namespace StandardElm.Prog
open StandardElm StandardElm.Eff

/-- The host model. -/
inductive Host where
  | any
  | none
  | echo (outPort inPort : String)
  deriving Inhabited

/-- With host h in state hs, the event ℓ may happen, leaving hs'. -/
inductive HostAllows : Host → List BVal → Option Event → List BVal → Prop where
  | any (hs : List BVal) (a : Option Event) : HostAllows .any hs a hs
  | silent (h : Host) (hs : List BVal) : HostAllows h hs none hs
  | act (h : Host) (hs : List BVal) (x : Action) : HostAllows h hs (some (.act x)) hs
  | wait (h : Host) (hs : List BVal) (d : Time) : HostAllows h hs (some (.wait d)) hs
  | out_none (hs : List BVal) (p : String) (j : BVal) : HostAllows .none hs (some (.out p j)) hs
  | out_echo (o i : String) (hs : List BVal) (j : BVal) : HostAllows (.echo o i) hs (some (.out o j)) (hs ++ [j])
  | out_other (o i p : String) (hs : List BVal) (j : BVal) : p ≠ o →
      HostAllows (.echo o i) hs (some (.out p j)) hs
  | in_echo (o i : String) (j : BVal) (hs : List BVal) : HostAllows (.echo o i) (j :: hs) (some (.inn i j)) hs

/-- An execution path: each step's event, log and resulting configuration. -/
abbrev PathL := List (Option Event × Log × Config)
abbrev Path := List (Option Event × Config)

/-- An execution with logs, under host h, from K with host state hs to host state hs''. -/
inductive ExecL (PE : PortEnv) (r : List (String × Val)) (h : Host) :
    Config → List BVal → PathL → List BVal → Prop where
  | nil (K : Config) (hs : List BVal) : ExecL PE r h K hs [] hs
  | cons (K : Config) (hs : List BVal) (a : Option Event) (l : Log) (K' : Config) (hs' : List BVal)
      (π : PathL) (hs'' : List BVal) :
      StepL PE r K a K' l → HostAllows h hs a hs' → ExecL PE r h K' hs' π hs'' →
      ExecL PE r h K hs ((a, l, K') :: π) hs''

/-- An execution, without logs. -/
inductive Exec (PE : PortEnv) (r : List (String × Val)) (h : Host) :
    Config → List BVal → Path → List BVal → Prop where
  | nil (K : Config) (hs : List BVal) : Exec PE r h K hs [] hs
  | cons (K : Config) (hs : List BVal) (a : Option Event) (K' : Config) (hs' : List BVal)
      (π : Path) (hs'' : List BVal) :
      Step PE r K a K' → HostAllows h hs a hs' → Exec PE r h K' hs' π hs'' →
      Exec PE r h K hs ((a, K') :: π) hs''

def PathL.log (π : PathL) : Log := (π.map (·.2.1)).flatten
def PathL.forgetLog (π : PathL) : Path := π.map fun (a, _, K) => (a, K)

theorem ExecL.forget {PE : PortEnv} {r : List (String × Val)} {h : Host} :
    ∀ {K hs π hs'}, ExecL PE r h K hs π hs' → Exec PE r h K hs π.forgetLog hs'
  | _, _, _, _, .nil K hs => .nil K hs
  | _, _, _, _, .cons _ _ _ _ _ _ _ _ hst hh hπ => .cons _ _ _ _ _ _ _ hst.forget hh hπ.forget

theorem Exec.lift {PE : PortEnv} {r : List (String × Val)} {h : Host} :
    ∀ {K hs π hs'}, Exec PE r h K hs π hs' → ∃ πl, ExecL PE r h K hs πl hs' ∧ πl.forgetLog = π
  | _, _, _, _, .nil K hs => ⟨[], .nil K hs, rfl⟩
  | _, _, _, _, .cons _ _ a K' _ _ _ hst hh hπ =>
    let ⟨l, hst'⟩ := Step.lift hst
    let ⟨πl, hπ', he⟩ := Exec.lift hπ
    ⟨(a, l, K') :: πl, .cons _ _ _ _ _ _ _ _ hst' hh hπ', by simp [PathL.forgetLog] at he ⊢; exact he⟩

/-- The executions of a worker program (its modules ms, flags type τ1) with flags j under host h,
    in basis B, with their logs: the log of the evaluation of the modules, then of the start, then
    of each step (D9). -/
def WorkerExec (B : Mod.Basis) (ms : List Mod.Module) (τ1 : PTy) (j : BVal) (h : Host) (lg : Log) : Prop :=
  ∃ r lm K0 ls π hs, Mod.EvalProgramL B ms (.prog r) lm ∧ StartL (portEnv ms) τ1 j r K0 ls ∧
    ExecL (portEnv ms) r h K0 [] π hs ∧ lg = lm ++ ls ++ π.log

/-- Observable events (sec:programs-behaviour): In, Out, wait, and actions of platform
    primitives; the actions of sleep, spawn and kill are not observable. -/
def Event.observable : Event → Bool
  | .inn .. | .out .. | .wait _ => true
  | .act x => decide (x.prim ∈ platPrims)

def trace (π : Path) : List Event := π.filterMap fun (a, _) => a.filter Event.observable

/-- Tr(program, j): the traces of the executions with flags j under the book's host. -/
def Tr (B : Mod.Basis) (ms : List Mod.Module) (τ1 : PTy) (j : BVal) (tr : List Event) : Prop :=
  ∃ r K0 π hs, Mod.EvalProgram B ms (.prog r) ∧ Start (portEnv ms) τ1 j r K0 ∧
    Exec (portEnv ms) r .any K0 [] π hs ∧ trace π = tr

/-- With the book's host, an execution with no step has the empty trace: a program that starts
    has the empty trace. -/
theorem tr_nil {B : Mod.Basis} {ms : List Mod.Module} {τ1 : PTy} {j : BVal}
    (h : ∃ r K0, Mod.EvalProgram B ms (.prog r) ∧ Start (portEnv ms) τ1 j r K0) : Tr B ms τ1 j [] := by
  obtain ⟨r, K0, he, hs⟩ := h
  exact ⟨r, K0, [], [], he, hs, .nil _ _, rfl⟩

/-- A program has no trace exactly when it does not start. -/
theorem tr_empty_iff_no_start {B : Mod.Basis} {ms : List Mod.Module} {τ1 : PTy} {j : BVal} :
    (∀ tr, ¬ Tr B ms τ1 j tr) ↔ ¬ ∃ r K0, Mod.EvalProgram B ms (.prog r) ∧ Start (portEnv ms) τ1 j r K0 := by
  constructor
  · intro h hs; exact h [] (tr_nil hs)
  · rintro h tr ⟨r, K0, π, hs, he, hst, _, _⟩; exact h ⟨r, K0, he, hst⟩

/-- Every prefix of an execution under the book's host is an execution. -/
theorem exec_take {PE : PortEnv} {r : List (String × Val)} :
    ∀ (n : Nat) {K hs π hs'}, Exec PE r .any K hs π hs' → ∃ hs'', Exec PE r .any K hs (π.take n) hs''
  | 0, _, _, _, _, _ => ⟨_, .nil _ _⟩
  | _, _, _, _, _, .nil K hs => ⟨hs, by simp; exact .nil K hs⟩
  | n + 1, _, _, _, _, .cons _ _ _ _ _ _ _ hst hh hπ =>
    let ⟨hs'', h'⟩ := exec_take n hπ
    ⟨hs'', by simp only [List.take_succ_cons]; exact .cons _ _ _ _ _ _ _ hst hh h'⟩

theorem trace_take_prefix : ∀ (π : Path) (tr' : List Event), tr' <+: trace π →
    ∃ n, trace (π.take n) = tr'
  | [], tr', h => ⟨0, by simp [trace] at h ⊢; exact h⟩
  | (a, K) :: π, tr', h => by
    cases ha : a.filter Event.observable with
    | none =>
      have hπ : trace ((a, K) :: π) = trace π := by simp [trace, ha]
      rw [hπ] at h
      obtain ⟨n, hn⟩ := trace_take_prefix π tr' h
      refine ⟨n + 1, ?_⟩
      simp only [List.take_succ_cons, trace, List.filterMap_cons, ha] at hn ⊢
      exact hn
    | some e =>
      have hπ : trace ((a, K) :: π) = e :: trace π := by simp [trace, ha]
      rw [hπ] at h
      cases tr' with
      | nil => exact ⟨0, by simp [trace]⟩
      | cons e' tr'' =>
        rw [List.cons_prefix_cons] at h
        obtain ⟨rfl, h'⟩ := h
        obtain ⟨n, hn⟩ := trace_take_prefix π tr'' h'
        refine ⟨n + 1, ?_⟩
        simp only [List.take_succ_cons, trace, List.filterMap_cons, ha] at hn ⊢
        rw [hn]

/-- Tr is closed under prefixes (sec:programs-behaviour: every finite prefix of transitions is an
    execution). -/
theorem tr_prefix {B : Mod.Basis} {ms : List Mod.Module} {τ1 : PTy} {j : BVal} {tr tr' : List Event}
    (h : Tr B ms τ1 j tr) (hp : tr' <+: tr) : Tr B ms τ1 j tr' := by
  obtain ⟨r, K0, π, hs, he, hst, hx, rfl⟩ := h
  obtain ⟨n, hn⟩ := trace_take_prefix π tr' hp
  obtain ⟨hs'', hx'⟩ := exec_take n hx
  exact ⟨r, K0, π.take n, hs'', he, hst, hx', hn⟩

end StandardElm.Prog
