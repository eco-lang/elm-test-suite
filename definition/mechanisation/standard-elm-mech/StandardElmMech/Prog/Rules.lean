/-
  A Standard Definition of Elm? Mechanisation: the start of a program and its transitions
  (programs.tex, sec:programs-dispatch and sec:programs-transitions), plan step 5.

  `Start` is r:p-init (with Flags_τ, A72 and A77); `Step` the 12 transition rules, one constructor
  each; `AcceptMsgs` the messages of an accepted incoming value (r:p-in-accept's premise). Their
  logged twins (`StartL`, `StepL`, `AcceptMsgsL`, plan decision D4) take the logs of their
  application, task-reduction and reception premises, in the order the rules write them.
-/
import StandardElmMech.Prog.Dispatch
import StandardElmMech.Eff.Messages

namespace StandardElm.Prog
open StandardElm StandardElm.Eff

/-- Flags_τ(j) = v: () at the unit type, Dec_τ(j) otherwise (A77). -/
def FlagsVal (τ : PTy) (j : BVal) (v : Val) : Prop :=
  (τ = .unit ∧ v = .unit) ∨ (τ ≠ .unit ∧ Eff.Dec τ j v)

/-- PE, τ1, j ⊢ prog r ⇒ K. -/
inductive Start : PortEnv → PTy → BVal → List (String × Val) → Config → Prop where
  /-- r:p-init -/
  | r_p_init (PE : PortEnv) (τ1 : PTy) (j : BVal) (r : List (String × Val)) (fi fs v1 v cm : Val)
      (cs L : List Val) (P : Procs) (Q : OutQ) (H : Pending) (sb : Val) :
      field r "init" = some fi → field r "subscriptions" = some fs →
      FlagsVal τ1 j v1 → AppVal fi v1 (.tuple v cm none) →
      flat cm = some cs → L.Perm cs → Dispatch 0 [] (qInit PE) [] L P Q H →
      AppVal fs v sb →
      Start PE τ1 j r ⟨0, v, [], P, sb, Q, H⟩

/-- The logged twin of `Start` (D4). -/
inductive StartL : PortEnv → PTy → BVal → List (String × Val) → Config → Log → Prop where
  /-- r:p-init -/
  | r_p_init_l (PE : PortEnv) (τ1 : PTy) (j : BVal) (r : List (String × Val)) (fi fs v1 v cm : Val)
      (cs L : List Val) (P : Procs) (Q : OutQ) (H : Pending) (sb : Val) (l1 l2 : Log) :
      field r "init" = some fi → field r "subscriptions" = some fs →
      FlagsVal τ1 j v1 → AppValL fi v1 (.tuple v cm none) l1 →
      flat cm = some cs → L.Perm cs → Dispatch 0 [] (qInit PE) [] L P Q H →
      AppValL fs v sb l2 →
      StartL PE τ1 j r ⟨0, v, [], P, sb, Q, H⟩ (l1 ++ l2)

/-- Platform steps: the empty platform has none ([params]). -/
inductive PlatStep : Config → Option Event → Config → Prop

/-- The messages of an accepted incoming value, one per leaf of the enumeration that gives one
    (premise of r:p-in-accept). -/
inductive AcceptMsgs : List Val → Input → List Val → Prop where
  | seq_nil (x : Input) : AcceptMsgs [] x []
  | seq_recv (c : Val) (cs : List Val) (x : Input) (v : Val) (ms : List Val) :
      Recv c x v → AcceptMsgs cs x ms → AcceptMsgs (c :: cs) x (v :: ms)
  | seq_none (c : Val) (cs : List Val) (x : Input) (ms : List Val) :
      (¬ ∃ v, Recv c x v) → AcceptMsgs cs x ms → AcceptMsgs (c :: cs) x ms

/-- The logged twin of `AcceptMsgs`: the logs of the leaves in the order of the enumeration. -/
inductive AcceptMsgsL : List Val → Input → List Val → Log → Prop where
  | seq_nil_l (x : Input) : AcceptMsgsL [] x [] []
  | seq_recv_l (c : Val) (cs : List Val) (x : Input) (v : Val) (ms : List Val) (l ls : Log) :
      RecvL c x v l → AcceptMsgsL cs x ms ls → AcceptMsgsL (c :: cs) x (v :: ms) (l ++ ls)
  | seq_none_l (c : Val) (cs : List Val) (x : Input) (ms : List Val) (ls : Log) :
      (¬ ∃ v, Recv c x v) → AcceptMsgsL cs x ms ls → AcceptMsgsL (c :: cs) x ms ls

/-- K →[ℓ] K' for the program value prog r with port environment PE. -/
inductive Step (PE : PortEnv) (r : List (String × Val)) : Config → Option Event → Config → Prop where
  /-- r:p-update -/
  | r_p_update (s : Time) (v v1 : Val) (M : List Val) (P : Procs) (sb : Val) (Q : OutQ) (H : Pending)
      (fu fs v2 v' cm : Val) (cs L : List Val) (P' : Procs) (Q' : OutQ) (H' : Pending) (sb' : Val) :
      field r "update" = some fu → field r "subscriptions" = some fs →
      AppVal fu v1 v2 → AppVal v2 v (.tuple v' cm none) →
      flat cm = some cs → L.Perm cs → Dispatch s P Q H L P' Q' H' →
      AppVal fs v' sb' →
      Step PE r ⟨s, v, v1 :: M, P, sb, Q, H⟩ none ⟨s, v', M, P', sb', Q', H'⟩
  /-- r:p-proc-step: silent, or labelled by an action of a platform primitive -/
  | r_p_proc_step (s : Time) (v : Val) (M : List Val) (P : Procs) (sb : Val) (Q : OutQ) (H : Pending)
      (n : Nat) (tk : Val) (s' : Time) (o : Option Val) (a : Option Action) (tk' : Val) :
      P.get n = some (.live ⟨tk, s', o⟩) → TaskRed tk a tk' →
      (∀ x, a = some x → x.prim ∈ platPrims) →
      Step PE r ⟨s, v, M, P, sb, Q, H⟩ (a.map .act) ⟨s, v, M, P.set n (.live ⟨tk', s, o⟩), sb, Q, H⟩
  /-- r:p-proc-sleep -/
  | r_p_proc_sleep (s : Time) (v : Val) (M : List Val) (P : Procs) (sb : Val) (Q : OutQ) (H : Pending)
      (n : Nat) (tk : Val) (s' : Time) (o : Option Val) (tk' v' t'' : Val) :
      P.get n = some (.live ⟨tk, s', o⟩) → TaskRed tk (some ⟨.sleep, [v'], t''⟩) tk' →
      SleepReady s s' v' →
      Step PE r ⟨s, v, M, P, sb, Q, H⟩ (some (.act ⟨.sleep, [v'], t''⟩))
        ⟨s, v, M, P.set n (.live ⟨tk', s, o⟩), sb, Q, H⟩
  /-- r:p-proc-spawn -/
  | r_p_proc_spawn (s : Time) (v : Val) (M : List Val) (P : Procs) (sb : Val) (Q : OutQ) (H : Pending)
      (n : Nat) (tk : Val) (s' : Time) (o : Option Val) (tk' t0 : Val) (n' : Nat) :
      P.get n = some (.live ⟨tk, s', o⟩) → TaskRed tk (some ⟨.spawn, [t0], .succeed (.pid n')⟩) tk' →
      n' ∉ P.dom →
      Step PE r ⟨s, v, M, P, sb, Q, H⟩ (some (.act ⟨.spawn, [t0], .succeed (.pid n')⟩))
        ⟨s, v, M, (P.set n (.live ⟨tk', s, o⟩)).set n' (.live ⟨t0, s, none⟩), sb, Q, H⟩
  /-- r:p-proc-kill: (P + {pid' ↦ ended}) + {pid ↦ (tk', s, orig)}; a self-kill keeps the second
      modification (A90) -/
  | r_p_proc_kill (s : Time) (v : Val) (M : List Val) (P : Procs) (sb : Val) (Q : OutQ) (H : Pending)
      (n : Nat) (tk : Val) (s' : Time) (o : Option Val) (tk' : Val) (n' : Nat) (t'' : Val) :
      P.get n = some (.live ⟨tk, s', o⟩) → TaskRed tk (some ⟨.kill, [.pid n'], t''⟩) tk' →
      Step PE r ⟨s, v, M, P, sb, Q, H⟩ (some (.act ⟨.kill, [.pid n'], t''⟩))
        ⟨s, v, M, (P.set n' .ended).set n (.live ⟨tk', s, o⟩), sb, Q, H⟩
  /-- r:p-proc-message -/
  | r_p_proc_message (s : Time) (v : Val) (M : List Val) (P : Procs) (sb : Val) (Q : OutQ) (H : Pending)
      (n : Nat) (v' : Val) (s' : Time) (c v'' : Val) :
      P.get n = some (.live ⟨.succeed v', s', some c⟩) → Recv c (.val v') v'' →
      Step PE r ⟨s, v, M, P, sb, Q, H⟩ none ⟨s, v, M ++ [v''], P.set n .ended, sb, Q, H⟩
  /-- r:p-proc-end -/
  | r_p_proc_end (s : Time) (v : Val) (M : List Val) (P : Procs) (sb : Val) (Q : OutQ) (H : Pending)
      (n : Nat) (tk : Val) (s' : Time) (o : Option Val) :
      P.get n = some (.live ⟨tk, s', o⟩) →
      ((∃ v', tk = .fail v') ∨ (∃ v', tk = .succeed v' ∧ o = none)) →
      Step PE r ⟨s, v, M, P, sb, Q, H⟩ none ⟨s, v, M, P.set n .ended, sb, Q, H⟩
  /-- r:p-in-accept -/
  | r_p_in_accept (s : Time) (v : Val) (M : List Val) (P : Procs) (sb : Val) (Q : OutQ) (H : Pending)
      (p : String) (τ : PTy) (j : BVal) (v' : Val) (cs L Ms : List Val) :
      fmLookup PE p = some (.inn, τ) → Eff.Dec τ j v' →
      flat sb = some cs → L.Perm cs → AcceptMsgs L (.port p j) Ms →
      Step PE r ⟨s, v, M, P, sb, Q, H⟩ (some (.inn p j)) ⟨s, v, M ++ Ms, P, sb, Q, H⟩
  /-- r:p-in-reject -/
  | r_p_in_reject (K : Config) (p : String) (τ : PTy) (j : BVal) :
      fmLookup PE p = some (.inn, τ) → (¬ ∃ v, Eff.Dec τ j v) → Step PE r K (some (.inn p j)) K
  /-- r:p-out -/
  | r_p_out (s : Time) (v : Val) (M : List Val) (P : Procs) (sb : Val) (Q : OutQ) (H : Pending)
      (p : String) (j : BVal) (J : List BVal) :
      fmLookup Q p = some (j :: J) →
      Step PE r ⟨s, v, M, P, sb, Q, H⟩ (some (.out p j)) ⟨s, v, M, P, sb, fmPlus Q [(p, J)], H⟩
  /-- r:p-wait -/
  | r_p_wait (s : Time) (v : Val) (M : List Val) (P : Procs) (sb : Val) (Q : OutQ) (H : Pending)
      (d : Time) : 0 < d →
      Step PE r ⟨s, v, M, P, sb, Q, H⟩ (some (.wait d)) ⟨s + d, v, M, P, sb, Q, H⟩
  /-- r:p-platform -/
  | r_p_platform (K : Config) (a : Option Event) (K' : Config) : PlatStep K a K' → Step PE r K a K'

/-- The logged twin of `Step` (D4). -/
inductive StepL (PE : PortEnv) (r : List (String × Val)) : Config → Option Event → Config → Log → Prop where
  /-- r:p-update -/
  | r_p_update_l (s : Time) (v v1 : Val) (M : List Val) (P : Procs) (sb : Val) (Q : OutQ) (H : Pending)
      (fu fs v2 v' cm : Val) (cs L : List Val) (P' : Procs) (Q' : OutQ) (H' : Pending) (sb' : Val)
      (l1 l2 l3 : Log) :
      field r "update" = some fu → field r "subscriptions" = some fs →
      AppValL fu v1 v2 l1 → AppValL v2 v (.tuple v' cm none) l2 →
      flat cm = some cs → L.Perm cs → Dispatch s P Q H L P' Q' H' →
      AppValL fs v' sb' l3 →
      StepL PE r ⟨s, v, v1 :: M, P, sb, Q, H⟩ none ⟨s, v', M, P', sb', Q', H'⟩ (l1 ++ l2 ++ l3)
  /-- r:p-proc-step -/
  | r_p_proc_step_l (s : Time) (v : Val) (M : List Val) (P : Procs) (sb : Val) (Q : OutQ) (H : Pending)
      (n : Nat) (tk : Val) (s' : Time) (o : Option Val) (a : Option Action) (tk' : Val) (l : Log) :
      P.get n = some (.live ⟨tk, s', o⟩) → TaskRedL tk a tk' l →
      (∀ x, a = some x → x.prim ∈ platPrims) →
      StepL PE r ⟨s, v, M, P, sb, Q, H⟩ (a.map .act) ⟨s, v, M, P.set n (.live ⟨tk', s, o⟩), sb, Q, H⟩ l
  /-- r:p-proc-sleep -/
  | r_p_proc_sleep_l (s : Time) (v : Val) (M : List Val) (P : Procs) (sb : Val) (Q : OutQ) (H : Pending)
      (n : Nat) (tk : Val) (s' : Time) (o : Option Val) (tk' v' t'' : Val) (l : Log) :
      P.get n = some (.live ⟨tk, s', o⟩) → TaskRedL tk (some ⟨.sleep, [v'], t''⟩) tk' l →
      SleepReady s s' v' →
      StepL PE r ⟨s, v, M, P, sb, Q, H⟩ (some (.act ⟨.sleep, [v'], t''⟩))
        ⟨s, v, M, P.set n (.live ⟨tk', s, o⟩), sb, Q, H⟩ l
  /-- r:p-proc-spawn -/
  | r_p_proc_spawn_l (s : Time) (v : Val) (M : List Val) (P : Procs) (sb : Val) (Q : OutQ) (H : Pending)
      (n : Nat) (tk : Val) (s' : Time) (o : Option Val) (tk' t0 : Val) (n' : Nat) (l : Log) :
      P.get n = some (.live ⟨tk, s', o⟩) → TaskRedL tk (some ⟨.spawn, [t0], .succeed (.pid n')⟩) tk' l →
      n' ∉ P.dom →
      StepL PE r ⟨s, v, M, P, sb, Q, H⟩ (some (.act ⟨.spawn, [t0], .succeed (.pid n')⟩))
        ⟨s, v, M, (P.set n (.live ⟨tk', s, o⟩)).set n' (.live ⟨t0, s, none⟩), sb, Q, H⟩ l
  /-- r:p-proc-kill -/
  | r_p_proc_kill_l (s : Time) (v : Val) (M : List Val) (P : Procs) (sb : Val) (Q : OutQ) (H : Pending)
      (n : Nat) (tk : Val) (s' : Time) (o : Option Val) (tk' : Val) (n' : Nat) (t'' : Val) (l : Log) :
      P.get n = some (.live ⟨tk, s', o⟩) → TaskRedL tk (some ⟨.kill, [.pid n'], t''⟩) tk' l →
      StepL PE r ⟨s, v, M, P, sb, Q, H⟩ (some (.act ⟨.kill, [.pid n'], t''⟩))
        ⟨s, v, M, (P.set n' .ended).set n (.live ⟨tk', s, o⟩), sb, Q, H⟩ l
  /-- r:p-proc-message -/
  | r_p_proc_message_l (s : Time) (v : Val) (M : List Val) (P : Procs) (sb : Val) (Q : OutQ) (H : Pending)
      (n : Nat) (v' : Val) (s' : Time) (c v'' : Val) (l : Log) :
      P.get n = some (.live ⟨.succeed v', s', some c⟩) → RecvL c (.val v') v'' l →
      StepL PE r ⟨s, v, M, P, sb, Q, H⟩ none ⟨s, v, M ++ [v''], P.set n .ended, sb, Q, H⟩ l
  /-- r:p-proc-end -/
  | r_p_proc_end_l (s : Time) (v : Val) (M : List Val) (P : Procs) (sb : Val) (Q : OutQ) (H : Pending)
      (n : Nat) (tk : Val) (s' : Time) (o : Option Val) :
      P.get n = some (.live ⟨tk, s', o⟩) →
      ((∃ v', tk = .fail v') ∨ (∃ v', tk = .succeed v' ∧ o = none)) →
      StepL PE r ⟨s, v, M, P, sb, Q, H⟩ none ⟨s, v, M, P.set n .ended, sb, Q, H⟩ []
  /-- r:p-in-accept -/
  | r_p_in_accept_l (s : Time) (v : Val) (M : List Val) (P : Procs) (sb : Val) (Q : OutQ) (H : Pending)
      (p : String) (τ : PTy) (j : BVal) (v' : Val) (cs L Ms : List Val) (l : Log) :
      fmLookup PE p = some (.inn, τ) → Eff.Dec τ j v' →
      flat sb = some cs → L.Perm cs → AcceptMsgsL L (.port p j) Ms l →
      StepL PE r ⟨s, v, M, P, sb, Q, H⟩ (some (.inn p j)) ⟨s, v, M ++ Ms, P, sb, Q, H⟩ l
  /-- r:p-in-reject -/
  | r_p_in_reject_l (K : Config) (p : String) (τ : PTy) (j : BVal) :
      fmLookup PE p = some (.inn, τ) → (¬ ∃ v, Eff.Dec τ j v) → StepL PE r K (some (.inn p j)) K []
  /-- r:p-out -/
  | r_p_out_l (s : Time) (v : Val) (M : List Val) (P : Procs) (sb : Val) (Q : OutQ) (H : Pending)
      (p : String) (j : BVal) (J : List BVal) :
      fmLookup Q p = some (j :: J) →
      StepL PE r ⟨s, v, M, P, sb, Q, H⟩ (some (.out p j)) ⟨s, v, M, P, sb, fmPlus Q [(p, J)], H⟩ []
  /-- r:p-wait -/
  | r_p_wait_l (s : Time) (v : Val) (M : List Val) (P : Procs) (sb : Val) (Q : OutQ) (H : Pending)
      (d : Time) : 0 < d →
      StepL PE r ⟨s, v, M, P, sb, Q, H⟩ (some (.wait d)) ⟨s + d, v, M, P, sb, Q, H⟩ []
  /-- r:p-platform -/
  | r_p_platform_l (K : Config) (a : Option Event) (K' : Config) : PlatStep K a K' → StepL PE r K a K' []

/-! ## The logged relations are the book's with a log -/

theorem StartL.forget : ∀ {PE τ j r K l}, StartL PE τ j r K l → Start PE τ j r K
  | _, _, _, _, _, _, .r_p_init_l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 =>
    .r_p_init _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4.forget h5 h6 h7 h8.forget

theorem Start.lift : ∀ {PE τ j r K}, Start PE τ j r K → ∃ l, StartL PE τ j r K l
  | _, _, _, _, _, .r_p_init _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 =>
    let ⟨l1, h4'⟩ := AppVal.lift h4
    let ⟨l2, h8'⟩ := AppVal.lift h8
    ⟨l1 ++ l2, .r_p_init_l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4' h5 h6 h7 h8'⟩

theorem AcceptMsgsL.forget : ∀ {L x Ms l}, AcceptMsgsL L x Ms l → AcceptMsgs L x Ms
  | _, _, _, _, .seq_nil_l x => .seq_nil x
  | _, _, _, _, .seq_recv_l _ _ _ _ _ _ _ h hs => .seq_recv _ _ _ _ _ h.forget hs.forget
  | _, _, _, _, .seq_none_l _ _ _ _ _ h hs => .seq_none _ _ _ _ h hs.forget

theorem AcceptMsgs.lift : ∀ {L x Ms}, AcceptMsgs L x Ms → ∃ l, AcceptMsgsL L x Ms l
  | _, _, _, .seq_nil x => ⟨[], .seq_nil_l x⟩
  | _, _, _, .seq_recv _ _ _ _ _ h hs =>
    let ⟨l, h'⟩ := Recv.lift h
    let ⟨ls, hs'⟩ := AcceptMsgs.lift hs
    ⟨l ++ ls, .seq_recv_l _ _ _ _ _ _ _ h' hs'⟩
  | _, _, _, .seq_none _ _ _ _ h hs =>
    let ⟨ls, hs'⟩ := AcceptMsgs.lift hs
    ⟨ls, .seq_none_l _ _ _ _ _ h hs'⟩

theorem StepL.forget {PE : PortEnv} {r : List (String × Val)} :
    ∀ {K a K' l}, StepL PE r K a K' l → Step PE r K a K'
  | _, _, _, _, .r_p_update_l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 =>
    .r_p_update _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3.forget h4.forget h5 h6 h7 h8.forget
  | _, _, _, _, .r_p_proc_step_l _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
    .r_p_proc_step _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2.forget h3
  | _, _, _, _, .r_p_proc_sleep_l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
    .r_p_proc_sleep _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2.forget h3
  | _, _, _, _, .r_p_proc_spawn_l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
    .r_p_proc_spawn _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2.forget h3
  | _, _, _, _, .r_p_proc_kill_l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 =>
    .r_p_proc_kill _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2.forget
  | _, _, _, _, .r_p_proc_message_l _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 =>
    .r_p_proc_message _ _ _ _ _ _ _ _ _ _ _ _ h1 h2.forget
  | _, _, _, _, .r_p_proc_end_l _ _ _ _ _ _ _ _ _ _ _ h1 h2 => .r_p_proc_end _ _ _ _ _ _ _ _ _ _ _ h1 h2
  | _, _, _, _, .r_p_in_accept_l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
    .r_p_in_accept _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5.forget
  | _, _, _, _, .r_p_in_reject_l _ _ _ _ h1 h2 => .r_p_in_reject _ _ _ _ h1 h2
  | _, _, _, _, .r_p_out_l _ _ _ _ _ _ _ _ _ _ h1 => .r_p_out _ _ _ _ _ _ _ _ _ _ h1
  | _, _, _, _, .r_p_wait_l _ _ _ _ _ _ _ _ h1 => .r_p_wait _ _ _ _ _ _ _ _ h1
  | _, _, _, _, .r_p_platform_l _ _ _ h1 => .r_p_platform _ _ _ h1

theorem Step.lift {PE : PortEnv} {r : List (String × Val)} :
    ∀ {K a K'}, Step PE r K a K' → ∃ l, StepL PE r K a K' l
  | _, _, _, .r_p_update _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 =>
    let ⟨l1, h3'⟩ := AppVal.lift h3
    let ⟨l2, h4'⟩ := AppVal.lift h4
    let ⟨l3, h8'⟩ := AppVal.lift h8
    ⟨l1 ++ l2 ++ l3, .r_p_update_l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3' h4' h5 h6 h7 h8'⟩
  | _, _, _, .r_p_proc_step _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
    let ⟨l, h2'⟩ := TaskRed.lift h2; ⟨l, .r_p_proc_step_l _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2' h3⟩
  | _, _, _, .r_p_proc_sleep _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
    let ⟨l, h2'⟩ := TaskRed.lift h2; ⟨l, .r_p_proc_sleep_l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2' h3⟩
  | _, _, _, .r_p_proc_spawn _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 =>
    let ⟨l, h2'⟩ := TaskRed.lift h2; ⟨l, .r_p_proc_spawn_l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2' h3⟩
  | _, _, _, .r_p_proc_kill _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 =>
    let ⟨l, h2'⟩ := TaskRed.lift h2; ⟨l, .r_p_proc_kill_l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2'⟩
  | _, _, _, .r_p_proc_message _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 =>
    let ⟨l, h2'⟩ := Recv.lift h2; ⟨l, .r_p_proc_message_l _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2'⟩
  | _, _, _, .r_p_proc_end _ _ _ _ _ _ _ _ _ _ _ h1 h2 => ⟨[], .r_p_proc_end_l _ _ _ _ _ _ _ _ _ _ _ h1 h2⟩
  | _, _, _, .r_p_in_accept _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 =>
    let ⟨l, h5'⟩ := AcceptMsgs.lift h5; ⟨l, .r_p_in_accept_l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5'⟩
  | _, _, _, .r_p_in_reject _ _ _ _ h1 h2 => ⟨[], .r_p_in_reject_l _ _ _ _ h1 h2⟩
  | _, _, _, .r_p_out _ _ _ _ _ _ _ _ _ _ h1 => ⟨[], .r_p_out_l _ _ _ _ _ _ _ _ _ _ h1⟩
  | _, _, _, .r_p_wait _ _ _ _ _ _ _ _ h1 => ⟨[], .r_p_wait_l _ _ _ _ _ _ _ _ h1⟩
  | _, _, _, .r_p_platform _ _ _ h1 => ⟨[], .r_p_platform_l _ _ _ h1⟩

end StandardElm.Prog
