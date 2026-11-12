/-
  A Standard Definition of Elm? Mechanisation: statements about every execution (CHECK-NOT), plan
  step 6.

  A CHECK-NOT line forbids a pattern anywhere in the output; each log entry prints as Elm/JS's
  Debug.log prints it (`label: value`, `renderEntry`). `WorkerTest.HoldsNot w pat`: for every flags
  value and every execution the book allows under the test's host, with every derivation of its
  steps, no entry of the log prints with the pattern (D9, D1). It is proved by a per-test invariant
  (`TestInv`): a predicate on configurations and host states, true after the start, closed under
  every transition under the host relation, and implying that each step's log is free of the
  pattern (`TestInv.sound`).

  The per-test proofs need non-derivability facts: that an application, a task step or a message
  has only the value and log the evaluator computes, when the evaluator reads no choice
  (`appVal_unique_l`, `stepTaskL_unique`, `recvL_unique`, from D1's completeness), and structural
  inversions of dispatch and of permutations. Values have no decidable equality (Lean's Float), so
  the concrete values a proof names are projections of the evaluator's own results, and each fact
  about them is a Boolean check decided by the kernel with a lemma that turns it into an equation
  (`Res.eq_get`, `tupleSnd_eq`, `leafArg_eq`, ...).
-/
import StandardElmMech.Prog.Worker

namespace StandardElm.Prog
open StandardElm StandardElm.Eff

/-! ## The statement -/

/-- An entry as Debug.log prints it. -/
def renderEntry (e : String × Val) : String := e.1 ++ ": " ++ showElm e.2

/-- p occurs in s as a contiguous sublist (structural, so the kernel reduces it). -/
def isInfixList : List Char → List Char → Bool
  | p, [] => p.isEmpty
  | p, c :: s => p.isPrefixOf (c :: s) || isInfixList p s

/-- pat occurs in s. -/
def containsStr (pat s : String) : Bool := isInfixList pat.toList s.toList

/-- No entry of the log prints with the pattern. -/
def NoMatch (pat : String) (lg : Log) : Prop := ∀ e ∈ lg, containsStr pat (renderEntry e) = false

/-- CHECK-NOT pat: for every flags value and every execution under the test's host, with every
    derivation of its steps, no log entry prints with pat (D9, D1). -/
def WorkerTest.HoldsNot (w : WorkerTest) (pat : String) : Prop :=
  ∀ j lg, WorkerExec (Mod.Btest []) w.prog.modules w.flagsType j w.host lg → NoMatch pat lg

theorem noMatch_nil (pat : String) : NoMatch pat [] := fun _ h => by simp at h

theorem noMatch_append {pat : String} {l1 l2 : Log} (h1 : NoMatch pat l1) (h2 : NoMatch pat l2) :
    NoMatch pat (l1 ++ l2) := by
  intro e he
  rcases List.mem_append.mp he with h | h
  · exact h1 e h
  · exact h2 e h

/-- A decider of `NoMatch`, for concrete logs. -/
def noMatchB (pat : String) (lg : Log) : Bool := lg.all fun e => !containsStr pat (renderEntry e)

theorem noMatch_of_B {pat : String} {lg : Log} (h : noMatchB pat lg = true) : NoMatch pat lg := by
  intro e he
  have := List.all_eq_true.mp h e he
  simpa using this

theorem PathL.log_cons (a : Option Event) (l : Log) (K : Config) (π : PathL) :
    PathL.log ((a, l, K) :: π) = l ++ PathL.log π := by
  simp [PathL.log]

/-! ## Invariants -/

/-- A per-test invariant: main's record r0, a predicate I on configurations and host states,
    and the three obligations. -/
structure TestInv (w : WorkerTest) (pat : String) where
  r0 : List (String × Val)
  I : Config → List BVal → Prop
  prog_ok : ∀ v lm, Mod.EvalProgramL (Mod.Btest []) w.prog.modules v lm → v = .prog r0 ∧ NoMatch pat lm
  start_ok : ∀ j K0 ls, StartL (portEnv w.prog.modules) w.flagsType j r0 K0 ls → I K0 [] ∧ NoMatch pat ls
  step_ok : ∀ K hs a K' l hs', I K hs → StepL (portEnv w.prog.modules) r0 K a K' l →
    HostAllows w.host hs a hs' → I K' hs' ∧ NoMatch pat l

theorem TestInv.exec {w : WorkerTest} {pat : String} (T : TestInv w pat) :
    ∀ {K hs π hs'}, ExecL (portEnv w.prog.modules) T.r0 w.host K hs π hs' → T.I K hs →
      NoMatch pat π.log := by
  intro K hs π hs' h
  induction h with
  | nil => intro _; exact noMatch_nil pat
  | cons K hs a l K' hs' π hs'' hst hh _ ih =>
    intro hI
    obtain ⟨hI', hl⟩ := T.step_ok K hs a K' l hs' hI hst hh
    rw [PathL.log_cons]
    exact noMatch_append hl (ih hI')

theorem TestInv.sound {w : WorkerTest} {pat : String} (T : TestInv w pat) : w.HoldsNot pat := by
  intro j lg ⟨r, lm, K0, ls, π, hs, he, hst, hx, hlg⟩
  obtain ⟨hr, hlm⟩ := T.prog_ok _ _ he
  cases hr
  obtain ⟨hI, hls⟩ := T.start_ok j K0 ls hst
  subst hlg
  exact noMatch_append (noMatch_append hlm hls) (T.exec hx hI)

/-- Under the book's host the host state never changes. -/
theorem ExecL.toAny {PE : PortEnv} {r : List (String × Val)} {h : Host} :
    ∀ {K hs π hs'} (hs0 : List BVal), ExecL PE r h K hs π hs' → ExecL PE r .any K hs0 π hs0
  | _, _, _, _, hs0, .nil K _ => .nil K hs0
  | _, _, _, _, hs0, .cons _ _ _ _ _ _ _ _ hst _ hπ => .cons _ _ _ _ _ _ _ _ hst (.any _ _) (ExecL.toAny hs0 hπ)

/-- An invariant proved for the book's host (`Host.any`) holds under every host. -/
theorem holdsNot_any {w : WorkerTest} {pat : String} (T : TestInv { w with host := .any } pat) :
    w.HoldsNot pat := by
  intro j lg ⟨r, lm, K0, ls, π, hs, he, hst, hx, hlg⟩
  exact T.sound j lg ⟨r, lm, K0, ls, π, [], he, hst, ExecL.toAny [] hx, hlg⟩

/-! ## Results of the evaluator, checked by the kernel -/

/-- The result is a value and the index is k. -/
def _root_.StandardElm.Res.isAt {α : Type} (r : Res α) (k : Nat) : Bool :=
  match r with
  | ⟨.value _, _, k'⟩ => k' == k
  | _ => false

def _root_.StandardElm.Res.get {α : Type} [Inhabited α] (r : Res α) : α :=
  match r.out with
  | .value v => v
  | _ => default

theorem _root_.StandardElm.Res.eq_get {α : Type} [Inhabited α] {r : Res α} {k : Nat} (h : r.isAt k = true) :
    r = ⟨.value r.get, r.log, k⟩ := by
  obtain ⟨out, l, k'⟩ := r
  cases out <;> simp [Res.isAt] at h
  subst h; rfl

/-- The application's only value and log (D1). -/
theorem appValL_det {o : Oracle} {n : Nat} {f v : Val} (h : (appVal o n f v 0).isAt 0 = true) :
    ∀ w l, AppValL f v w l → w = (appVal o n f v 0).get ∧ l = (appVal o n f v 0).log :=
  appVal_unique_l (Res.eq_get h)

/-- The task step's only action, task and log, when it spawns nothing (D1). -/
theorem taskRedL_det {o : Oracle} {n fr : Nat} {tk : Val} (h : (stepTaskL o n fr tk 0).isAt 0 = true)
    (hs : ∀ x, (stepTaskL o n fr tk 0).get.1 = some x → x.prim ≠ .spawn) :
    ∀ a t l, TaskRedL tk a t l → a = (stepTaskL o n fr tk 0).get.1 ∧ t = (stepTaskL o n fr tk 0).get.2 ∧
      l = (stepTaskL o n fr tk 0).log := by
  intro a t l d
  have he := Res.eq_get h
  exact stepTaskL_unique (a := (stepTaskL o n fr tk 0).get.1) (t := (stepTaskL o n fr tk 0).get.2)
    (he.trans (by simp)) hs a t l d

/-- The message's only value and log (D1). -/
theorem recvL_det {o : Oracle} {n : Nat} {c : Val} {x : Input} (h : (recvL o n c x 0).isAt 0 = true) :
    ∀ v l, RecvL c x v l → v = (recvL o n c x 0).get ∧ l = (recvL o n c x 0).log :=
  recvL_unique (Res.eq_get h)

/-! ## Shapes of values, checked by the kernel -/

def tupleSnd : Val → Val
  | .tuple _ b _ => b
  | _ => .unit

def tupleFst : Val → Val
  | .tuple a _ _ => a
  | _ => .unit

/-- `(a, b)` with no third component. -/
def isPair : Val → Bool
  | .tuple _ _ none => true
  | _ => false

theorem pair_eq {v : Val} (h : isPair v = true) : v = .tuple (tupleFst v) (tupleSnd v) none := by
  cases v <;> simp_all [isPair, tupleFst, tupleSnd]
  rename_i c; cases c <;> simp_all

def isUnit : Val → Bool
  | .unit => true
  | _ => false

theorem unit_eq {v : Val} (h : isUnit v = true) : v = .unit := by
  cases v <;> simp_all [isUnit]

def leafArg : Val → Val
  | .leaf _ t => t
  | _ => .unit

def isTaskLeaf : Val → Bool
  | .leaf .task _ => true
  | _ => false

theorem taskLeaf_eq {v : Val} (h : isTaskLeaf v = true) : v = .leaf .task (leafArg v) := by
  cases v <;> simp_all [isTaskLeaf, leafArg]
  rename_i m _; cases m <;> simp_all

def succArg : Val → Val
  | .succeed v => v
  | _ => .unit

def isSucceed : Val → Bool
  | .succeed _ => true
  | _ => false

theorem succeed_eq {v : Val} (h : isSucceed v = true) : v = .succeed (succArg v) := by
  cases v <;> simp_all [isSucceed, succArg]

def progRec : Val → List (String × Val)
  | .prog r => r
  | _ => []

def isProg : Val → Bool
  | .prog _ => true
  | _ => false

theorem prog_eq {v : Val} (h : isProg v = true) : v = .prog (progRec v) := by
  cases v <;> simp_all [isProg, progRec]

/-- flat v is the empty sequence. -/
def flatEmpty (v : Val) : Bool :=
  match flat v with
  | some [] => true
  | _ => false

theorem flat_empty {v : Val} (h : flatEmpty v = true) : flat v = some [] := by
  unfold flatEmpty at h
  split at h <;> simp_all

theorem opt_eq_getD {α : Type} {o : Option α} (d : α) (h : o.isSome = true) : o = some (o.getD d) := by
  cases o <;> simp_all

/-- A process table with one entry n. -/
def Single (P : Procs) (n : Nat) : Prop := ∀ q, q ≠ n → P.get q = none

theorem single_get {P : Procs} {n q : Nat} {e : PEntry} (hs : Single P n) (h : P.get q = some e) : q = n :=
  Classical.byContradiction fun hq => by rw [hs q hq] at h; cases h

theorem single_set {P : Procs} {n : Nat} (e : PEntry) (hs : Single P n) : Single (P.set n e) n :=
  fun q hq => by simp only [Procs.get, Procs.set] at hs ⊢; rw [natLookup_natSet_other _ _ _ _ hq]; exact hs q hq

theorem set_get_self (P : Procs) (n : Nat) (e : PEntry) : (P.set n e).get n = some e :=
  natLookup_natSet_self P n e

theorem single_init (n : Nat) (e : PEntry) : Single (Procs.set [] n e) n :=
  single_set e (fun _ _ => rfl)

theorem recvL_task_inv {tk v w : Val} {l : Log} (h : RecvL (.leaf .task tk) (.val v) w l) : w = v ∧ l = [] := by
  cases h; exact ⟨rfl, rfl⟩

/-- A live process whose task is not an outcome neither sends a message nor ends. -/
theorem notOutcome_ne_succeed {t v : Val} (h : t.isOutcome = false) : t ≠ .succeed v := by
  intro he; subst he; simp [Val.isOutcome] at h

theorem notOutcome_ne_fail {t v : Val} (h : t.isOutcome = false) : t ≠ .fail v := by
  intro he; subst he; simp [Val.isOutcome] at h

def isLeaf : Val → Bool
  | .leaf _ _ => true
  | _ => false

theorem flat_leaf {v : Val} (h : isLeaf v = true) : flat v = some [v] := by
  cases v <;> simp_all [isLeaf, flat]

/-- The flattening of v is two leaves. -/
def flat2 (v : Val) : Option (Val × Val) :=
  match flat v with
  | some [a, b] => some (a, b)
  | _ => none

theorem flat_two {v : Val} (h : (flat2 v).isSome = true) :
    flat v = some [((flat2 v).getD (.unit, .unit)).1, ((flat2 v).getD (.unit, .unit)).2] := by
  unfold flat2 at h ⊢
  split at h <;> simp_all

/-- c is an out leaf of port p carrying j. -/
def outLeafIs (c : Val) (p : String) (j : BVal) : Bool :=
  match leafCore c with
  | some (.out p', .bv j') => p' == p && j' == j
  | _ => false

theorem outLeaf_eq {c : Val} {p : String} {j : BVal} (h : outLeafIs c p j = true) :
    leafCore c = some (.out p, .bv j) := by
  unfold outLeafIs at h
  split at h
  · rename_i p' j' he
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact he
  · cases h

/-! ## Inversions -/

theorem perm_nil' {L : List Val} (h : L.Perm []) : L = [] := List.Perm.eq_nil h

theorem perm_one {α : Type} {L : List α} {c : α} (h : L.Perm [c]) : L = [c] :=
  List.perm_singleton.mp h

theorem perm_two {α : Type} {L : List α} {c c' : α} (h : L.Perm [c, c']) : L = [c, c'] ∨ L = [c', c] := by
  have hl : L.length = 2 := by simpa using h.length_eq
  match L, hl with
  | [a, b], _ =>
    have hm : ∀ x, x ∈ [a, b] ↔ x ∈ [c, c'] := fun x => h.mem_iff
    by_cases hac : a = c
    · subst hac
      have : [b].Perm [c'] := (List.perm_cons a).mp h
      left; rw [List.perm_singleton.mp this]
    · have ha : a = c' := by
        have := (hm a).mp (by simp)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at this
        exact this.resolve_left hac
      subst ha
      have h2 : [a, b].Perm [a, c] := h.trans (List.Perm.swap a c [])
      have : [b].Perm [c] := (List.perm_cons a).mp h2
      right; rw [List.perm_singleton.mp this]

theorem dispatch_nil {s : Time} {P : Procs} {Q : OutQ} {H : Pending} {P' : Procs} {Q' : OutQ}
    {H' : Pending} (h : Dispatch s P Q H [] P' Q' H') : P' = P ∧ Q' = Q ∧ H' = H := by
  cases h; exact ⟨rfl, rfl, rfl⟩

theorem dispatch_task1 {s : Time} {P : Procs} {Q : OutQ} {H : Pending} {c tk : Val} {P' : Procs}
    {Q' : OutQ} {H' : Pending} (hc : leafCore c = some (.task, tk))
    (h : Dispatch s P Q H [c] P' Q' H') :
    ∃ n, n ∉ P.dom ∧ P' = P.set n (.live ⟨tk, s, some c⟩) ∧ Q' = Q ∧ H' = H := by
  cases h with
  | r_p_disp_task _ _ _ _ tk' n _ _ _ _ hc' hn hd =>
    rw [hc] at hc'; cases hc'
    obtain ⟨rfl, rfl, rfl⟩ := dispatch_nil hd
    exact ⟨n, hn, rfl, rfl, rfl⟩
  | r_p_disp_out _ _ _ _ _ _ _ _ _ _ _ hc' _ _ => rw [hc] at hc'; cases hc'
  | r_p_disp_plat _ _ _ _ _ _ _ _ _ _ _ hm _ => simp [platMgrs] at hm

/-- The value an out leaf carries. -/
def outValue (c : Val) : Option BVal :=
  match leafCore c with
  | some (.out _, .bv j) => some j
  | _ => none

theorem outValue_of {c : Val} {p : String} {j : BVal} (h : leafCore c = some (.out p, .bv j)) :
    outValue c = some j := by
  simp [outValue, h]

/-- Dispatching out leaves of one port p, whose queue is the only one, appends their values. -/
theorem dispatch_outs {s : Time} {p : String} : ∀ {L : List Val} {P : Procs} {js : List BVal}
    {H : Pending} {P' : Procs} {Q' : OutQ} {H' : Pending},
    (∀ c ∈ L, ∃ j, leafCore c = some (.out p, .bv j)) →
    Dispatch s P [(p, js)] H L P' Q' H' → P' = P ∧ H' = H ∧ Q' = [(p, js ++ L.filterMap outValue)]
  | [], P, js, H, P', Q', H', _, h => by
    obtain ⟨rfl, rfl, rfl⟩ := dispatch_nil h
    simp
  | c :: L, P, js, H, P', Q', H', hL, h => by
    obtain ⟨j0, hj0⟩ := hL c (by simp)
    cases h with
    | r_p_disp_task _ _ _ _ _ _ _ _ _ _ hc _ _ => rw [hj0] at hc; cases hc
    | r_p_disp_out _ _ _ _ p' j js' _ _ _ _ hc hq hd =>
      rw [hj0] at hc; cases hc
      simp only [fmLookup, beq_self_eq_true, ite_true, Option.some.injEq] at hq
      subst hq
      have hfm : fmPlus [(p, js)] [(p, js ++ [j0])] = [(p, js ++ [j0])] := by simp [fmPlus]
      rw [hfm] at hd
      obtain ⟨h1, h2, h3⟩ := dispatch_outs (fun c' hc' => hL c' (List.mem_cons_of_mem _ hc')) hd
      refine ⟨h1, h2, ?_⟩
      rw [h3]
      simp [outValue, hj0]
    | r_p_disp_plat _ _ _ _ _ _ _ _ _ _ _ hm _ => simp [platMgrs] at hm

/-- The echo host sends back on i only the oldest value it holds. -/
theorem hostAllows_echo_in {o i p : String} {hs hs' : List BVal} {j : BVal}
    (h : HostAllows (.echo o i) hs (some (.inn p j)) hs') : p = i ∧ hs = j :: hs' := by
  cases h; exact ⟨rfl, rfl⟩

/-- A value delivered on o joins the echo host's state; on another port, nothing changes. -/
theorem hostAllows_echo_out {o i p : String} {hs hs' : List BVal} {j : BVal}
    (h : HostAllows (.echo o i) hs (some (.out p j)) hs') : (p = o ∧ hs' = hs ++ [j]) ∨ hs' = hs := by
  cases h
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr rfl

/-- Other events leave the host's state. -/
theorem hostAllows_other {h : Host} {hs hs' : List BVal} {a : Option Event}
    (hn : ∀ p j, a ≠ some (.inn p j)) (ho : ∀ p j, a ≠ some (.out p j)) (hh : HostAllows h hs a hs') :
    hs' = hs := by
  cases hh with
  | out_echo => exact absurd rfl (ho _ _)
  | in_echo => exact absurd rfl (hn _ _)
  | _ => rfl

/-- The messages of one subscription c that receives x as the evaluator computes, with no choice. -/
theorem acceptMsgsL_one {o : Oracle} {n : Nat} {c : Val} {x : Input}
    (h : (recvL o n c x 0).isAt 0 = true) {Ms : List Val} {l : Log} (d : AcceptMsgsL [c] x Ms l) :
    Ms = [(recvL o n c x 0).get] ∧ l = (recvL o n c x 0).log := by
  have he := Res.eq_get h
  cases d with
  | seq_recv_l _ _ _ v ms l1 ls hr hrest =>
    obtain ⟨rfl, rfl⟩ := recvL_det h v l1 hr
    cases hrest
    simp
  | seq_none_l _ _ _ ms ls hno _ =>
    exact absurd ⟨_, (recvL_sound c he).forget⟩ hno

theorem platStep_empty {K K' : Config} {a : Option Event} : ¬ PlatStep K a K' := fun h => nomatch h

end StandardElm.Prog
