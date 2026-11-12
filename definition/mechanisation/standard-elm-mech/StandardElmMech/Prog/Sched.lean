/-
  A Standard Definition of Elm? Mechanisation: a scheduler that builds one execution, plan step 5.

  The scheduler is a function with explicit choices; a default strategy models Elm/JS (Appendix E,
  sec:appendix-implementation-platform): deliver what the echo host sends back, deliver outgoing
  values, handle the oldest message, run the process at the head of a FIFO run queue (a process
  runs until it waits), wake sleepers whose deadline has come, let time pass to the earliest
  deadline, and stop. Each transition it takes is a transition of the book (`doChoice_sound`), so a
  run is an execution (`run_sound`), whatever its status: every finite prefix of transitions is an
  execution (sec:programs-behaviour).
-/
import StandardElmMech.Prog.Exec

namespace StandardElm.Prog
open StandardElm StandardElm.Eff

/-- Order of the leaves of one command or subscription when it is dispatched or receives a value.
    `reversed` is Elm/JS's and eco's (Appendix E, "The Order of Commands"). -/
inductive LeafOrder where
  | listed
  | reversed
  deriving Inhabited, DecidableEq

def LeafOrder.apply : LeafOrder → List Val → List Val
  | .listed, cs => cs
  | .reversed, cs => cs.reverse

theorem LeafOrder.perm (lo : LeafOrder) (cs : List Val) : (lo.apply cs).Perm cs := by
  cases lo
  · exact List.Perm.refl cs
  · exact List.reverse_perm cs

inductive Choice where
  | update
  | proc (n : Nat)
  | out (p : String)
  | inn
  | wait (d : Rat)
  | wake
  | stop
  deriving Inhabited

structure SchedConfig where
  leafOrder : LeafOrder := .reversed
  overrides : List (Nat × Choice) := []
  deriving Inhabited

structure Ctx where
  PE : PortEnv
  r : List (String × Val)
  host : Host
  cfg : SchedConfig
  fuelEval : Nat := 100000

structure SchedState where
  K : Config
  hs : List BVal
  rq : List Nat
  sleepers : List (Nat × Option Rat)
  oracle : Oracle
  next : Nat
  idx : Nat

/-- One transition, as the scheduler took it. -/
structure Taken where
  ev : Option Event
  log : Log
  K' : Config
  hs' : List BVal

/-- The result of one choice: a transition, a change of the scheduler's own state only, or no
    progress. -/
inductive ChoiceOut where
  | trans (t : Taken) (st' : SchedState)
  | keep (st' : SchedState)
  | stuck

/-! ## Helpers, each with its soundness -/

/-- The condition of r:p-proc-sleep, decided. -/
def sleepReadyB (s s' : Time) (v' : Val) : Bool :=
  match v' with
  | .sv (.float x) =>
    match floatToRat? x with
    | some q => decide (s' + (if q < 0 then 0 else q) ≤ s)
    | none => true
  | _ => true

theorem sleepReadyB_sound {s s' : Time} {v' : Val} (h : sleepReadyB s s' v' = true) : SleepReady s s' v' := by
  intro x q hv hq
  subst hv
  simp only [sleepReadyB, hq, decide_eq_true_eq] at h
  exact h

/-- The deadline of a sleep that is not yet due: s' + max(0, q) for a finite float, none
    (due at once) otherwise. -/
def sleepDeadline (s' : Time) (v' : Val) : Option Rat :=
  match v' with
  | .sv (.float x) => (floatToRat? x).map fun q => s' + (if q < 0 then 0 else q)
  | _ => none

/-- The messages of an accepted value: for each leaf, its message by `recvL`, or none when
    `recvNone` says no rule gives one. -/
def acceptFn (o : Oracle) (fuel : Nat) (x : Input) : List Val → Nat → Option (List Val × Log × Nat)
  | [], k => some ([], [], k)
  | c :: cs, k =>
    if recvNone c x then acceptFn o fuel x cs k
    else match recvL o fuel c x k with
      | ⟨.value v, l, k'⟩ => (acceptFn o fuel x cs k').map fun (ms, ls, k'') => (v :: ms, l ++ ls, k'')
      | _ => none

theorem acceptFn_sound {o : Oracle} {fuel : Nat} {x : Input} : ∀ {L : List Val} {k : Nat}
    {ms : List Val} {ls : Log} {k' : Nat}, acceptFn o fuel x L k = some (ms, ls, k') → AcceptMsgsL L x ms ls
  | [], k, ms, ls, k', h => by
    simp only [acceptFn, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    exact .seq_nil_l x
  | c :: cs, k, ms, ls, k', h => by
    simp only [acceptFn] at h
    split at h
    · rename_i hn
      exact .seq_none_l c cs x ms ls (recvNone_sound hn) (acceptFn_sound h)
    · split at h
      · rename_i v l k1 hr
        cases ha : acceptFn o fuel x cs k1 with
        | none => simp [ha] at h
        | some t =>
          obtain ⟨ms1, ls1, k2⟩ := t
          simp only [ha, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, -⟩ := h
          exact .seq_recv_l c cs x v ms1 l ls1 (recvL_sound c hr) (acceptFn_sound ha)
      · cases h

/-- The host state after an event the scheduler takes, and whether the host allows it. -/
def hostAfter (h : Host) (hs : List BVal) : Option Event → Option (List BVal)
  | none => some hs
  | some (.act _) => some hs
  | some (.wait _) => some hs
  | some (.out p j) =>
    match h with
    | .any => some hs
    | .none => some hs
    | .echo o _ => if p = o then some (hs ++ [j]) else some hs
  | some (.inn p j) =>
    match h with
    | .any => some hs
    | .none => none
    | .echo _ i =>
      match hs with
      | j' :: rest => if p = i ∧ j = j' then some rest else none
      | [] => none

theorem hostAfter_sound {h : Host} {hs : List BVal} {a : Option Event} {hs' : List BVal}
    (e : hostAfter h hs a = some hs') : HostAllows h hs a hs' := by
  cases h with
  | any =>
    cases a with
    | none => simp [hostAfter] at e; subst e; exact .any _ _
    | some ev => cases ev <;> simp [hostAfter] at e <;> subst e <;> exact .any _ _
  | none =>
    cases a with
    | none => simp [hostAfter] at e; subst e; exact .silent _ _
    | some ev =>
      cases ev with
      | inn => simp [hostAfter] at e
      | out p j => simp [hostAfter] at e; subst e; exact .out_none _ _ _
      | act x => simp [hostAfter] at e; subst e; exact .act _ _ _
      | wait d => simp [hostAfter] at e; subst e; exact .wait _ _ _
  | echo o i =>
    cases a with
    | none => simp [hostAfter] at e; subst e; exact .silent _ _
    | some ev =>
      cases ev with
      | inn p j =>
        cases hs with
        | nil => simp [hostAfter] at e
        | cons j' rest =>
          simp only [hostAfter] at e
          split at e
          · rename_i hc; obtain ⟨rfl, rfl⟩ := hc; cases e; exact .in_echo _ _ _ _
          · cases e
      | out p j =>
        simp only [hostAfter] at e
        split at e
        · rename_i hp; subst hp; cases e; exact .out_echo _ _ _ _
        · rename_i hp; cases e; exact .out_other _ _ _ _ _ hp
      | act x => simp [hostAfter] at e; subst e; exact .act _ _ _
      | wait d => simp [hostAfter] at e; subst e; exact .wait _ _ _

/-- Keep only the identifiers whose process is live. -/
def isLive (P : Procs) (n : Nat) : Bool :=
  match P.get n with
  | some (.live _) => true
  | _ => false

def SchedState.tidy (st : SchedState) : SchedState :=
  { st with rq := st.rq.filter (isLive st.K.procs), sleepers := st.sleepers.filter fun (n, _) => isLive st.K.procs n }

/-! ## The choices -/

/-- r:p-update on the head message. -/
def doUpdate (c : Ctx) (st : SchedState) : ChoiceOut :=
  match st.K.msgs, field c.r "update", field c.r "subscriptions" with
  | v1 :: M, some fu, some fs =>
    match appVal st.oracle c.fuelEval fu v1 st.next with
    | ⟨.value v2, l1, k1⟩ =>
      match appVal st.oracle c.fuelEval v2 st.K.model k1 with
      | ⟨.value (.tuple v' cm none), l2, k2⟩ =>
        match flat cm with
        | some cs =>
          match dispatchFn st.K.time st.K.procs st.K.outq (c.cfg.leafOrder.apply cs) with
          | some (P', Q', ns) =>
            match appVal st.oracle c.fuelEval fs v' k2 with
            | ⟨.value sb', l3, k3⟩ =>
              let K' : Config := ⟨st.K.time, v', M, P', sb', Q', st.K.pending⟩
              .trans ⟨none, l1 ++ l2 ++ l3, K', st.hs⟩
                (SchedState.tidy { st with K := K', next := k3, rq := st.rq ++ ns })
            | _ => .stuck
          | none => .stuck
        | none => .stuck
      | _ => .stuck
    | _ => .stuck
  | _, _, _ => .stuck

/-- The transitions of process n by a step of its task: silent, a sleep (or, not yet due, a move
    to the sleepers), a spawn, a kill. -/
def procTask (c : Ctx) (st : SchedState) (n : Nat) (tk : Val) (s' : Time) (o : Option Val) : ChoiceOut :=
  match stepTaskL st.oracle c.fuelEval (freshPid st.K.procs) tk st.next with
  | ⟨.value (none, tk'), l, k'⟩ =>
    let K' : Config := { st.K with procs := st.K.procs.set n (.live ⟨tk', st.K.time, o⟩) }
    .trans ⟨none, l, K', st.hs⟩ (SchedState.tidy { st with K := K', next := k' })
  | ⟨.value (some ⟨.sleep, [v'], t''⟩, tk'), l, k'⟩ =>
    if sleepReadyB st.K.time s' v' then
      let K' : Config := { st.K with procs := st.K.procs.set n (.live ⟨tk', st.K.time, o⟩) }
      .trans ⟨some (.act ⟨.sleep, [v'], t''⟩), l, K', st.hs⟩
        (SchedState.tidy { st with K := K', next := k', rq := st.rq.filter (· != n) ++ [n] })
    else .keep { st with rq := st.rq.filter (· != n), sleepers := st.sleepers ++ [(n, sleepDeadline s' v')] }
  | ⟨.value (some ⟨.spawn, [t0], .succeed (.pid n')⟩, tk'), l, k'⟩ =>
    if n' ∉ st.K.procs.dom then
      let K' : Config :=
        { st.K with procs := (st.K.procs.set n (.live ⟨tk', st.K.time, o⟩)).set n' (.live ⟨t0, st.K.time, none⟩) }
      .trans ⟨some (.act ⟨.spawn, [t0], .succeed (.pid n')⟩), l, K', st.hs⟩
        (SchedState.tidy { st with K := K', next := k', rq := st.rq.filter (· != n) ++ [n', n] })
    else .stuck
  | ⟨.value (some ⟨.kill, [.pid n'], t''⟩, tk'), l, k'⟩ =>
    let K' : Config := { st.K with procs := (st.K.procs.set n' .ended).set n (.live ⟨tk', st.K.time, o⟩) }
    .trans ⟨some (.act ⟨.kill, [.pid n'], t''⟩), l, K', st.hs⟩
      (SchedState.tidy { st with K := K', next := k', rq := st.rq.filter (· != n) ++ [n] })
  | _ => .stuck

/-- A process whose task is an outcome: its message (task leaf of origin c) or its end. -/
def procOutcome (c : Ctx) (st : SchedState) (n : Nat) (tk : Val) (o : Option Val) : ChoiceOut :=
  match tk, o with
  | .succeed v', some cl =>
    match recvL st.oracle c.fuelEval cl (.val v') st.next with
    | ⟨.value v'', l, k'⟩ =>
      let K' : Config := { st.K with msgs := st.K.msgs ++ [v''], procs := st.K.procs.set n .ended }
      .trans ⟨none, l, K', st.hs⟩ (SchedState.tidy { st with K := K', next := k' })
    | _ => .stuck
  | .succeed _, none =>
    let K' : Config := { st.K with procs := st.K.procs.set n .ended }
    .trans ⟨none, [], K', st.hs⟩ (SchedState.tidy { st with K := K' })
  | .fail _, _ =>
    let K' : Config := { st.K with procs := st.K.procs.set n .ended }
    .trans ⟨none, [], K', st.hs⟩ (SchedState.tidy { st with K := K' })
  | _, _ => .stuck

/-- The next transition of process n. -/
def doProc (c : Ctx) (st : SchedState) (n : Nat) : ChoiceOut :=
  match st.K.procs.get n with
  | some (.live ⟨tk, s', o⟩) => if tk.isOutcome then procOutcome c st n tk o else procTask c st n tk s' o
  | _ => .stuck

/-- r:p-out on port p. -/
def doOut (c : Ctx) (st : SchedState) (p : String) : ChoiceOut :=
  match fmLookup st.K.outq p with
  | some (j :: J) =>
    match hostAfter c.host st.hs (some (.out p j)) with
    | some hs' =>
      let K' : Config := { st.K with outq := fmPlus st.K.outq [(p, J)] }
      .trans ⟨some (.out p j), [], K', hs'⟩ { st with K := K', hs := hs' }
    | none => .stuck
  | _ => .stuck

/-- The echo host sends back its oldest pending value: r:p-in-accept or r:p-in-reject. -/
def doInn (c : Ctx) (st : SchedState) : ChoiceOut :=
  match c.host, st.hs with
  | .echo _ i, j :: _ =>
    match fmLookup c.PE i, hostAfter c.host st.hs (some (.inn i j)) with
    | some (.inn, τ), some hs' =>
      match dec τ j with
      | some _ =>
        match flat st.K.subs with
        | some cs =>
          match acceptFn st.oracle c.fuelEval (.port i j) (c.cfg.leafOrder.apply cs) st.next with
          | some (Ms, l, k') =>
            let K' : Config := { st.K with msgs := st.K.msgs ++ Ms }
            .trans ⟨some (.inn i j), l, K', hs'⟩ { st with K := K', hs := hs', next := k' }
          | none => .stuck
        | none => .stuck
      | none => .trans ⟨some (.inn i j), [], st.K, hs'⟩ { st with hs := hs' }
    | _, _ => .stuck
  | _, _ => .stuck

/-- r:p-wait. -/
def doWait (c : Ctx) (st : SchedState) (d : Rat) : ChoiceOut :=
  if 0 < d then
    match hostAfter c.host st.hs (some (.wait d)) with
    | some hs' =>
      let K' : Config := { st.K with time := st.K.time + d }
      .trans ⟨some (.wait d), [], K', hs'⟩ { st with K := K', hs := hs' }
    | none => .stuck
  else .stuck

/-- Bookkeeping: the sleepers whose deadline has come join the run queue. -/
def doWake (st : SchedState) : ChoiceOut :=
  let due := st.sleepers.filter fun (_, d) => d.all (· ≤ st.K.time)
  .keep { st with rq := st.rq ++ due.map (·.1), sleepers := st.sleepers.filter fun (_, d) => !(d.all (· ≤ st.K.time)) }

def doChoice (c : Ctx) (st : SchedState) : Choice → ChoiceOut
  | .update => doUpdate c st
  | .proc n => doProc c st n
  | .out p => doOut c st p
  | .inn => doInn c st
  | .wait d => doWait c st d
  | .wake => doWake st
  | .stop => .stuck

/-- The earliest deadline of the sleepers (a non-finite one counts as now). -/
def minDeadline (now : Rat) (sl : List (Nat × Option Rat)) : Option Rat :=
  sl.foldl (fun acc (_, d) =>
    let d' := d.getD now
    match acc with
    | some a => some (if d' < a then d' else a)
    | none => some d') none

/-- The default strategy, in priority order. -/
def defaultChoice (c : Ctx) (st : SchedState) : Choice :=
  if (match c.host with | .echo .. => true | _ => false) && !st.hs.isEmpty then .inn
  else match st.K.outq.find? (fun (_, js) => !js.isEmpty) with
  | some (p, _) => .out p
  | none =>
    if !st.K.msgs.isEmpty then .update
    else match st.rq with
    | n :: _ => .proc n
    | [] =>
      if st.sleepers.any (fun (_, d) => d.all (· ≤ st.K.time)) then .wake
      else match minDeadline st.K.time st.sleepers with
      | some D => if st.K.time < D then .wait (D - st.K.time) else .wake
      | none => .stop

inductive RunStatus where
  | quiescent
  | outOfFuel
  | stuck
  deriving Inhabited, DecidableEq

structure RunResult where
  path : PathL
  hs : List BVal
  status : RunStatus

/-- Run at most n scheduler iterations, appending each transition to the path. An override at the
    current index replaces the default choice. -/
def run (c : Ctx) : Nat → SchedState → PathL → RunResult
  | 0, st, acc => ⟨acc, st.hs, .outOfFuel⟩
  | n + 1, st, acc =>
    let ch := match fmLookupNat c.cfg.overrides st.idx with
      | some ch => ch
      | none => defaultChoice c st
    match ch with
    | .stop => ⟨acc, st.hs, .quiescent⟩
    | ch =>
      match doChoice c st ch with
      | .trans t st' => run c n { st' with idx := st.idx + 1 } (acc ++ [(t.ev, t.log, t.K')])
      | .keep st' => run c n { st' with K := st.K, hs := st.hs, idx := st.idx + 1 } acc
      | .stuck => ⟨acc, st.hs, .stuck⟩
where
  fmLookupNat (l : List (Nat × Choice)) (k : Nat) : Option Choice :=
    match l with
    | [] => none
    | (k', ch) :: rest => if k' == k then some ch else fmLookupNat rest k

/-! ## Soundness -/

/-- What a transition the scheduler takes must be: a logged transition of the book, allowed by
    the host, to the state the scheduler moves to. -/
def TransOK (c : Ctx) (st : SchedState) (t : Taken) (st' : SchedState) : Prop :=
  StepL c.PE c.r st.K t.ev t.K' t.log ∧ HostAllows c.host st.hs t.ev t.hs' ∧ st'.K = t.K' ∧ st'.hs = t.hs'

theorem stepTaskL_sound_eq {o : Oracle} {n fr : Nat} {tk : Val} {k : Nat} {a : Option Action} {tk' : Val}
    {l : Log} {k' : Nat} (h : stepTaskL o n fr tk k = ⟨.value (a, tk'), l, k'⟩) : TaskRedL tk a tk' l := by
  have := stepTaskL_sound (o := o) (n := n) (fr := fr) (tk := tk) (k := k) (a := a) (tk' := tk') (by rw [h])
  rw [h] at this; exact this

theorem doUpdate_sound {c : Ctx} {st : SchedState} {t : Taken} {st' : SchedState}
    (h : doUpdate c st = .trans t st') : TransOK c st t st' := by
  rcases hK : st.K with ⟨s, v, M0, P, sb, Q, H⟩
  unfold doUpdate at h
  simp only [hK] at h
  split at h
  · rename_i v1 M fu fs hfu hfs
    split at h
    · rename_i v2 l1 k1 h1
      split at h
      · rename_i v' cm l2 k2 h2
        split at h
        · rename_i cs hf
          split at h
          · rename_i P' Q' ns hd
            split at h
            · rename_i sb' l3 k3 h3
              simp only [ChoiceOut.trans.injEq] at h; obtain ⟨rfl, rfl⟩ := h
              refine ⟨?_, .silent _ _, rfl, rfl⟩
              show StepL c.PE c.r st.K _ _ _; rw [hK]
              exact .r_p_update_l s v v1 M P sb Q H fu fs v2 v' cm cs _ P' Q' H sb' l1 l2 l3 hfu hfs
                (appVal_sound_l h1) (appVal_sound_l h2) hf (c.cfg.leafOrder.perm cs) (dispatchFn_sound hd)
                (appVal_sound_l h3)
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

theorem procTask_sound {c : Ctx} {st : SchedState} {n : Nat} {tk : Val} {s' : Time} {o : Option Val}
    {t : Taken} {st' : SchedState} (hp : st.K.procs.get n = some (.live ⟨tk, s', o⟩))
    (h : procTask c st n tk s' o = .trans t st') : TransOK c st t st' := by
  rcases hK : st.K with ⟨s, v, M, P, sb, Q, H⟩
  rw [hK] at hp; simp only at hp
  unfold procTask at h
  simp only [hK] at h
  split at h
  · rename_i tk' l k' hs
    simp only [ChoiceOut.trans.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, .silent _ _, rfl, rfl⟩
    show StepL c.PE c.r st.K _ _ _; rw [hK]
    exact .r_p_proc_step_l s v M P sb Q H n tk s' o none tk' l hp (stepTaskL_sound_eq hs) (by simp)
  · rename_i v' t'' tk' l k' hs
    split at h
    · rename_i hr
      simp only [ChoiceOut.trans.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, .act _ _ _, rfl, rfl⟩
      show StepL c.PE c.r st.K _ _ _; rw [hK]
      exact .r_p_proc_sleep_l s v M P sb Q H n tk s' o tk' v' t'' l hp (stepTaskL_sound_eq hs)
        (sleepReadyB_sound hr)
    · cases h
  · rename_i t0 n' tk' l k' hs
    split at h
    · rename_i hn
      simp only [ChoiceOut.trans.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, .act _ _ _, rfl, rfl⟩
      show StepL c.PE c.r st.K _ _ _; rw [hK]
      exact .r_p_proc_spawn_l s v M P sb Q H n tk s' o tk' t0 n' l hp (stepTaskL_sound_eq hs) hn
    · cases h
  · rename_i n' t'' tk' l k' hs
    simp only [ChoiceOut.trans.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, .act _ _ _, rfl, rfl⟩
    show StepL c.PE c.r st.K _ _ _; rw [hK]
    exact .r_p_proc_kill_l s v M P sb Q H n tk s' o tk' n' t'' l hp (stepTaskL_sound_eq hs)
  · cases h

theorem procOutcome_sound {c : Ctx} {st : SchedState} {n : Nat} {tk : Val} {s' : Time} {o : Option Val}
    {t : Taken} {st' : SchedState} (hp : st.K.procs.get n = some (.live ⟨tk, s', o⟩))
    (h : procOutcome c st n tk o = .trans t st') : TransOK c st t st' := by
  rcases hK : st.K with ⟨s, v, M, P, sb, Q, H⟩
  rw [hK] at hp; simp only at hp
  unfold procOutcome at h
  simp only [hK] at h
  split at h
  · rename_i v' cl
    split at h
    · rename_i v'' l k' hr
      simp only [ChoiceOut.trans.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, .silent _ _, rfl, rfl⟩
      show StepL c.PE c.r st.K _ _ _; rw [hK]
      exact .r_p_proc_message_l s v M P sb Q H n v' s' cl v'' l hp (recvL_sound cl hr)
    · cases h
  · rename_i v'
    simp only [ChoiceOut.trans.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, .silent _ _, rfl, rfl⟩
    show StepL c.PE c.r st.K _ _ _; rw [hK]
    exact .r_p_proc_end_l s v M P sb Q H n _ s' none hp (Or.inr ⟨v', rfl, rfl⟩)
  · rename_i o' v'
    simp only [ChoiceOut.trans.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, .silent _ _, rfl, rfl⟩
    show StepL c.PE c.r st.K _ _ _; rw [hK]
    exact .r_p_proc_end_l s v M P sb Q H n _ s' o hp (Or.inl ⟨v', rfl⟩)
  · cases h

theorem doProc_sound {c : Ctx} {st : SchedState} {n : Nat} {t : Taken} {st' : SchedState}
    (h : doProc c st n = .trans t st') : TransOK c st t st' := by
  unfold doProc at h
  split at h
  · rename_i tk s' o hp
    split at h
    · exact procOutcome_sound hp h
    · exact procTask_sound hp h
  · cases h

theorem doOut_sound {c : Ctx} {st : SchedState} {p : String} {t : Taken} {st' : SchedState}
    (h : doOut c st p = .trans t st') : TransOK c st t st' := by
  rcases hK : st.K with ⟨s, v, M, P, sb, Q, H⟩
  unfold doOut at h
  simp only [hK] at h
  split at h
  · rename_i j J hq
    split at h
    · rename_i hs' hh
      simp only [ChoiceOut.trans.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, hostAfter_sound hh, rfl, rfl⟩
      show StepL c.PE c.r st.K _ _ _; rw [hK]
      exact .r_p_out_l s v M P sb Q H p j J hq
    · cases h
  · cases h

theorem doInn_sound {c : Ctx} {st : SchedState} {t : Taken} {st' : SchedState}
    (h : doInn c st = .trans t st') : TransOK c st t st' := by
  rcases hK : st.K with ⟨s, v, M, P, sb, Q, H⟩
  unfold doInn at h
  simp only [hK] at h
  split at h
  · rename_i _ _ o i j rest hhost hhs
    split at h
    · rename_i _ _ τ hs' hpe hh
      split at h
      · rename_i v' hd
        split at h
        · rename_i cs hf
          split at h
          · rename_i Ms l k' ha
            simp only [ChoiceOut.trans.injEq] at h; obtain ⟨rfl, rfl⟩ := h
            refine ⟨?_, hostAfter_sound hh, rfl, rfl⟩
            show StepL c.PE c.r st.K _ _ _; rw [hK]
            exact .r_p_in_accept_l s v M P sb Q H i τ j v' cs _ Ms l hpe ((dec_iff τ j v').mpr hd) hf
              (c.cfg.leafOrder.perm cs) (acceptFn_sound ha)
          · cases h
        · cases h
      · rename_i hd
        simp only [ChoiceOut.trans.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        refine ⟨?_, hostAfter_sound hh, rfl, rfl⟩
        show StepL c.PE c.r st.K _ _ _; rw [hK]
        exact .r_p_in_reject_l _ i τ j hpe (fun ⟨w, hw⟩ => by rw [dec_iff] at hw; rw [hw] at hd; cases hd)
    · cases h
  · cases h

theorem doWait_sound {c : Ctx} {st : SchedState} {d : Rat} {t : Taken} {st' : SchedState}
    (h : doWait c st d = .trans t st') : TransOK c st t st' := by
  rcases hK : st.K with ⟨s, v, M, P, sb, Q, H⟩
  unfold doWait at h
  simp only [hK] at h
  split at h
  · rename_i hd
    split at h
    · rename_i hs' hh
      simp only [ChoiceOut.trans.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, hostAfter_sound hh, rfl, rfl⟩
      show StepL c.PE c.r st.K _ _ _; rw [hK]
      exact .r_p_wait_l s v M P sb Q H d hd
    · cases h
  · cases h

theorem doChoice_sound {c : Ctx} {st : SchedState} {ch : Choice} {t : Taken} {st' : SchedState}
    (h : doChoice c st ch = .trans t st') : TransOK c st t st' := by
  cases ch with
  | update => exact doUpdate_sound h
  | proc n => exact doProc_sound h
  | out p => exact doOut_sound h
  | inn => exact doInn_sound h
  | wait d => exact doWait_sound h
  | wake => simp [doChoice, doWake] at h
  | stop => simp [doChoice] at h

/-- The configuration a path ends in, from K. -/
def lastConfig (K : Config) (π : PathL) : Config := π.foldl (fun _ x => x.2.2) K

theorem lastConfig_append (K : Config) (π : PathL) (x : Option Event × Log × Config) :
    lastConfig K (π ++ [x]) = x.2.2 := by
  simp [lastConfig, List.foldl_append]

theorem ExecL.append {PE : PortEnv} {r : List (String × Val)} {h : Host} :
    ∀ {K hs π1 hs1}, ExecL PE r h K hs π1 hs1 → ∀ {π2 hs2}, ExecL PE r h (lastConfig K π1) hs1 π2 hs2 →
      ExecL PE r h K hs (π1 ++ π2) hs2
  | _, _, _, _, .nil K hs, _, _, h2 => by simpa [lastConfig] using h2
  | _, _, _, _, .cons K hs a l K' hs' π hs'' hst hh hπ, _, _, h2 => by
    simp only [List.cons_append]
    refine .cons _ _ _ _ _ _ _ _ hst hh (ExecL.append hπ ?_)
    simpa [lastConfig] using h2

/-- A run is an execution: the transitions the scheduler takes, from where it started. -/
theorem run_sound (c : Ctx) (K0 : Config) (hs0 : List BVal) : ∀ (n : Nat) (st : SchedState) (acc : PathL),
    ExecL c.PE c.r c.host K0 hs0 acc st.hs → lastConfig K0 acc = st.K →
    ExecL c.PE c.r c.host K0 hs0 (run c n st acc).path (run c n st acc).hs
  | 0, st, acc, hx, _ => by simpa [run] using hx
  | n + 1, st, acc, hx, hl => by
    unfold run
    simp only
    split
    · simpa using hx
    · split
      · rename_i t st' hd
        have ⟨hst, hh, hK, hhs⟩ := doChoice_sound hd
        apply run_sound c K0 hs0 n
        · simp only
          rw [hhs]
          refine ExecL.append hx ?_
          rw [hl]
          exact .cons _ _ _ _ _ _ _ _ hst hh (.nil _ _)
        · simp only [lastConfig_append]; exact hK.symm
      · apply run_sound c K0 hs0 n
        · simpa using hx
        · simpa using hl
      · simpa using hx

end StandardElm.Prog
