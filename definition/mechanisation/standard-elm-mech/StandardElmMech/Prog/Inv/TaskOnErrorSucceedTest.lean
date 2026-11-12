/-
  A Standard Definition of Elm? Mechanisation: TaskOnErrorSucceedTest's CHECK-NOT, plan step 6.

  `CHECK-NOT: handler called`, under every host (the program has no port). The program's task is
  T1 = andThen(C, onError(Hd, succeed 1)); r:e-task-onerror-succeed reduces the inner onError to
  succeed 1 without applying the handler Hd (the only rule that applies Hd, r:e-task-onerror-fail,
  needs a failing task), so the process runs T1, T2, T3 = succeed (Got 1), sends Got 1, and the
  update logs `result: 1`. The invariant: model (), subscriptions none, no port queue, no pending
  platform command, one process n, and one of five shapes (the process at T1, T2 or T3 with no
  message; ended with the message Got 1; ended with no message).
-/
import StandardElmMech.Prog.Invariant
import StandardElmMech.Generated.Worker01

namespace StandardElm.Prog.Inv.TaskOnErrorSucceedTest
open StandardElm StandardElm.Prog StandardElm.Eff

-- the program's terms are large; elaborating equations about them nests deeply
set_option maxRecDepth 8192

abbrev w : WorkerTest := w_elm_core_TaskOnErrorSucceedTest
def ms : List Mod.Module := w.prog.modules
def PE : PortEnv := portEnv ms
abbrev o : Oracle := .const false
abbrev N : Nat := workerFuel
abbrev pat : String := "handler called"

/-! ## The values, as the evaluator computes them -/

def progRes : Res Val := Mod.evProgram o N (Mod.Btest []) ms 0
def r0 : List (String × Val) := progRec progRes.get
def FI : Val := (field r0 "init").getD .unit
def FU : Val := (field r0 "update").getD .unit
def FS : Val := (field r0 "subscriptions").getD .unit
def initRes : Res Val := appVal o N FI .unit 0
def C : Val := tupleSnd initRes.get
def T1 : Val := leafArg C
def step1 : Res (Option Action × Val) := stepTaskL o N 0 T1 0
def T2 : Val := step1.get.2
def step2 : Res (Option Action × Val) := stepTaskL o N 0 T2 0
def T3 : Val := step2.get.2
def m : Val := succArg T3
def subsRes : Res Val := appVal o N FS .unit 0
def SB : Val := subsRes.get
def upd1 : Res Val := appVal o N FU m 0
def U : Val := upd1.get
def upd2 : Res Val := appVal o N U .unit 0
def CM2 : Val := tupleSnd upd2.get

/-- Every fact about the values that the proof uses, decided by the kernel. -/
def facts : Bool :=
  progRes.isAt 0 && progRes.log.isEmpty && isProg progRes.get &&
  (field r0 "init").isSome && (field r0 "update").isSome && (field r0 "subscriptions").isSome &&
  PE.isEmpty &&
  initRes.isAt 0 && initRes.log.isEmpty && isPair initRes.get && isUnit (tupleFst initRes.get) &&
  isTaskLeaf C &&
  step1.isAt 0 && step1.get.1.isNone && step1.log.isEmpty && !T1.isOutcome &&
  step2.isAt 0 && step2.get.1.isNone && step2.log.isEmpty && !T2.isOutcome &&
  isSucceed T3 &&
  subsRes.isAt 0 && subsRes.log.isEmpty &&
  upd1.isAt 0 && upd1.log.isEmpty &&
  upd2.isAt 0 && isPair upd2.get && isUnit (tupleFst upd2.get) && flatEmpty CM2

theorem facts_true : facts = true := by decide +kernel

/-- The update's log, printed as Debug.log prints it, does not contain the pattern. The printer
    (`showElm`) is defined by well-founded recursion, which the kernel does not unfold, so this is
    decided by `native_decide`. [native] -/
theorem upd2_log : NoMatch pat upd2.log := noMatch_of_B (by native_decide)

structure Facts : Prop where
  prog_at : progRes.isAt 0 = true
  prog_log : progRes.log = []
  prog_is : isProg progRes.get = true
  init_some : (field r0 "init").isSome = true
  update_some : (field r0 "update").isSome = true
  subs_some : (field r0 "subscriptions").isSome = true
  pe : PE = []
  init_at : initRes.isAt 0 = true
  init_log : initRes.log = []
  init_pair : isPair initRes.get = true
  init_unit : isUnit (tupleFst initRes.get) = true
  c_leaf : isTaskLeaf C = true
  s1_at : step1.isAt 0 = true
  s1_silent : step1.get.1 = none
  s1_log : step1.log = []
  t1_no : T1.isOutcome = false
  s2_at : step2.isAt 0 = true
  s2_silent : step2.get.1 = none
  s2_log : step2.log = []
  t2_no : T2.isOutcome = false
  t3_succ : isSucceed T3 = true
  subs_at : subsRes.isAt 0 = true
  subs_log : subsRes.log = []
  u1_at : upd1.isAt 0 = true
  u1_log : upd1.log = []
  u2_at : upd2.isAt 0 = true
  u2_pair : isPair upd2.get = true
  u2_unit : isUnit (tupleFst upd2.get) = true
  cm2_empty : flatEmpty CM2 = true

theorem f (h : facts = true) : Facts := by
  simp only [facts, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff, Option.isNone_iff_eq_none] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩, a12⟩, a13⟩, a14⟩,
    a15⟩, a16⟩, a17⟩, a18⟩, a19⟩, a20⟩, a21⟩, a22⟩, a23⟩, a24⟩, a25⟩, a26⟩, a27⟩, a28⟩, a29⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20,
    a21, a22, a23, a24, a25, a26, a27, a28, a29⟩

/-! ## The equations they give -/

section
variable (h : facts = true)
include h

theorem prog_eval : progRes = ⟨.value (.prog r0), [], 0⟩ := by
  have F := f h
  rw [Res.eq_get F.prog_at, F.prog_log]
  congr 2
  exact prog_eq F.prog_is

theorem hFI : field r0 "init" = some FI := opt_eq_getD _ (f h).init_some
theorem hFU : field r0 "update" = some FU := opt_eq_getD _ (f h).update_some
theorem hFS : field r0 "subscriptions" = some FS := opt_eq_getD _ (f h).subs_some
theorem hPE : PE = [] := (f h).pe

theorem hC : C = .leaf .task T1 := taskLeaf_eq (f h).c_leaf

theorem init_det : ∀ w l, AppValL FI .unit w l → w = .tuple .unit C none ∧ l = [] := by
  have F := f h
  intro w l d
  obtain ⟨rfl, rfl⟩ := appValL_det F.init_at w l d
  refine ⟨?_, F.init_log⟩
  change initRes.get = _
  rw [pair_eq F.init_pair, unit_eq F.init_unit]; rfl

theorem T1_det : ∀ a t l, TaskRedL T1 a t l → a = none ∧ t = T2 ∧ l = [] := by
  have F := f h
  intro a t l d
  obtain ⟨rfl, rfl, rfl⟩ := taskRedL_det F.s1_at
    (by change ∀ x, step1.get.1 = some x → _; rw [F.s1_silent]; intro x hx; cases hx) a t l d
  exact ⟨F.s1_silent, rfl, F.s1_log⟩

theorem T1_no : T1.isOutcome = false := (f h).t1_no

theorem T2_det : ∀ a t l, TaskRedL T2 a t l → a = none ∧ t = T3 ∧ l = [] := by
  have F := f h
  intro a t l d
  obtain ⟨rfl, rfl, rfl⟩ := taskRedL_det F.s2_at
    (by change ∀ x, step2.get.1 = some x → _; rw [F.s2_silent]; intro x hx; cases hx) a t l d
  exact ⟨F.s2_silent, rfl, F.s2_log⟩

theorem T2_no : T2.isOutcome = false := (f h).t2_no

theorem hT3 : T3 = .succeed m := succeed_eq (f h).t3_succ

theorem subs_det : ∀ w l, AppValL FS .unit w l → w = SB ∧ l = [] := by
  have F := f h
  intro w l d
  exact ⟨(appValL_det F.subs_at w l d).1, (appValL_det F.subs_at w l d).2.trans F.subs_log⟩

theorem upd1_det : ∀ w l, AppValL FU m w l → w = U ∧ l = [] := by
  have F := f h
  intro w l d
  exact ⟨(appValL_det F.u1_at w l d).1, (appValL_det F.u1_at w l d).2.trans F.u1_log⟩

theorem upd2_det : ∀ w l, AppValL U .unit w l → w = .tuple .unit CM2 none ∧ l = upd2.log := by
  have F := f h
  intro w l d
  obtain ⟨rfl, rfl⟩ := appValL_det F.u2_at w l d
  refine ⟨?_, rfl⟩
  change upd2.get = _
  rw [pair_eq F.u2_pair, unit_eq F.u2_unit]; rfl

theorem hCM2 : flat CM2 = some [] := flat_empty (f h).cm2_empty

end

/-! ## The invariant -/

/-- One process n, in one of five shapes. -/
def Shape (P : Procs) (M : List Val) (n : Nat) : Prop :=
  (∃ s', P.get n = some (.live ⟨T1, s', some C⟩) ∧ M = []) ∨
  (∃ s', P.get n = some (.live ⟨T2, s', some C⟩) ∧ M = []) ∨
  (∃ s', P.get n = some (.live ⟨T3, s', some C⟩) ∧ M = []) ∨
  (P.get n = some .ended ∧ M = [m]) ∨
  (P.get n = some .ended ∧ M = [])

def I (K : Config) (_ : List BVal) : Prop :=
  K.model = .unit ∧ K.subs = SB ∧ K.outq = [] ∧ K.pending = [] ∧ ∃ n, Single K.procs n ∧ Shape K.procs K.msgs n

theorem start_ok (h : facts = true) (j : BVal) (K0 : Config) (ls : Log)
    (hs : StartL PE .unit j r0 K0 ls) : I K0 [] ∧ NoMatch pat ls := by
  cases hs with
  | r_p_init_l fi fs v1 v cm cs L P Q H sb l1 l2 hfi hfs hfl ha1 hfl2 hp hd ha2 =>
    obtain rfl := Option.some.inj (hfi.symm.trans (hFI h))
    obtain rfl := Option.some.inj (hfs.symm.trans (hFS h))
    have hv1 : v1 = .unit := by
      rcases hfl with ⟨-, rfl⟩ | ⟨hne, -⟩
      · rfl
      · exact absurd rfl hne
    subst hv1
    obtain ⟨he, rfl⟩ := init_det h _ _ ha1
    simp only [Val.tuple.injEq] at he
    obtain ⟨rfl, rfl, -⟩ := he
    rw [hC h] at hfl2
    simp only [flat, Option.some.injEq] at hfl2
    subst hfl2
    have hL := perm_one hp
    subst hL
    obtain ⟨n, -, rfl, rfl, rfl⟩ := dispatch_task1 (c := .leaf .task T1) (tk := T1) rfl hd
    obtain ⟨rfl, rfl⟩ := subs_det h _ _ ha2
    refine ⟨⟨rfl, rfl, by rw [hPE h]; rfl, rfl, n, single_init n _, ?_⟩, noMatch_nil pat⟩
    left
    exact ⟨0, by rw [hC h]; exact set_get_self _ _ _, rfl⟩

/-- Every transition keeps the invariant and logs nothing with the pattern. [native] (the printed
    form of the update's log entry) -/
theorem step_ok (h : facts = true) (K : Config) (hs : List BVal) (a : Option Event) (K' : Config)
    (l : Log) (hs' : List BVal) (hI : I K hs) (hst : StepL PE r0 K a K' l) :
    I K' hs' ∧ NoMatch pat l := by
  obtain ⟨hv, hsb, hq, hH, n, hsing, hsh⟩ := hI
  cases hst with
  | r_p_update_l s v v1 M P sb Q H fu fs v2 v' cm cs L P' Q' H' sb' l1 l2 l3 hfu hfs ha1 ha2 hfl hp hd ha3 =>
    simp only at hv hsb hq hH hsh
    subst hv hsb hq hH
    obtain rfl := Option.some.inj (hfu.symm.trans (hFU h))
    obtain rfl := Option.some.inj (hfs.symm.trans (hFS h))
    -- the head message is m (shape d)
    rcases hsh with ⟨_, _, hM⟩ | ⟨_, _, hM⟩ | ⟨_, _, hM⟩ | ⟨hP, hM⟩ | ⟨_, hM⟩ <;>
      simp only [List.cons.injEq, reduceCtorEq] at hM
    obtain ⟨rfl, rfl⟩ := hM
    obtain ⟨rfl, rfl⟩ := upd1_det h _ _ ha1
    obtain ⟨he, rfl⟩ := upd2_det h _ _ ha2
    simp only [Val.tuple.injEq] at he
    obtain ⟨rfl, rfl, -⟩ := he
    rw [hCM2 h] at hfl; cases hfl
    have := perm_nil' hp; subst this
    obtain ⟨rfl, rfl, rfl⟩ := dispatch_nil hd
    obtain ⟨rfl, rfl⟩ := subs_det h _ _ ha3
    refine ⟨⟨rfl, rfl, rfl, rfl, n, hsing, .inr (.inr (.inr (.inr ⟨hP, rfl⟩)))⟩, ?_⟩
    simpa using upd2_log
  | r_p_proc_step_l s v M P sb Q H n0 tk s' o0 a tk' l hp hr hpl =>
    simp only at hv hsb hq hH hsh hsing
    subst hv hsb hq hH
    have hn := single_get hsing hp; subst hn
    rcases hsh with ⟨s1, hP, hM⟩ | ⟨s1, hP, hM⟩ | ⟨s1, hP, hM⟩ | ⟨hP, hM⟩ | ⟨hP, hM⟩ <;>
      rw [hP] at hp <;> simp only [Option.some.injEq, PEntry.live.injEq, Proc.mk.injEq, reduceCtorEq] at hp
    · obtain ⟨rfl, -, rfl⟩ := hp
      obtain ⟨rfl, rfl, rfl⟩ := T1_det h _ _ _ hr
      exact ⟨⟨rfl, rfl, rfl, rfl, n0, single_set _ hsing, .inr (.inl ⟨s, set_get_self _ _ _, hM⟩)⟩, noMatch_nil pat⟩
    · obtain ⟨rfl, -, rfl⟩ := hp
      obtain ⟨rfl, rfl, rfl⟩ := T2_det h _ _ _ hr
      exact ⟨⟨rfl, rfl, rfl, rfl, n0, single_set _ hsing, .inr (.inr (.inl ⟨s, set_get_self _ _ _, hM⟩))⟩, noMatch_nil pat⟩
    · obtain ⟨rfl, -, rfl⟩ := hp
      have := hr.not_outcome; rw [hT3 h] at this; simp [Val.isOutcome] at this
  | r_p_proc_sleep_l s v M P sb Q H n0 tk s' o0 tk' v0 t0 l hp hr _ =>
    simp only at hsh hsing
    have hn := single_get hsing hp; subst hn
    rcases hsh with ⟨s1, hP, hM⟩ | ⟨s1, hP, hM⟩ | ⟨s1, hP, hM⟩ | ⟨hP, hM⟩ | ⟨hP, hM⟩ <;>
      rw [hP] at hp <;> simp only [Option.some.injEq, PEntry.live.injEq, Proc.mk.injEq, reduceCtorEq] at hp
    · obtain ⟨rfl, -, rfl⟩ := hp; cases (T1_det h _ _ _ hr).1
    · obtain ⟨rfl, -, rfl⟩ := hp; cases (T2_det h _ _ _ hr).1
    · obtain ⟨rfl, -, rfl⟩ := hp
      have := hr.not_outcome; rw [hT3 h] at this; simp [Val.isOutcome] at this
  | r_p_proc_spawn_l s v M P sb Q H n0 tk s' o0 tk' t0 n' l hp hr _ =>
    simp only at hsh hsing
    have hn := single_get hsing hp; subst hn
    rcases hsh with ⟨s1, hP, hM⟩ | ⟨s1, hP, hM⟩ | ⟨s1, hP, hM⟩ | ⟨hP, hM⟩ | ⟨hP, hM⟩ <;>
      rw [hP] at hp <;> simp only [Option.some.injEq, PEntry.live.injEq, Proc.mk.injEq, reduceCtorEq] at hp
    · obtain ⟨rfl, -, rfl⟩ := hp; cases (T1_det h _ _ _ hr).1
    · obtain ⟨rfl, -, rfl⟩ := hp; cases (T2_det h _ _ _ hr).1
    · obtain ⟨rfl, -, rfl⟩ := hp
      have := hr.not_outcome; rw [hT3 h] at this; simp [Val.isOutcome] at this
  | r_p_proc_kill_l s v M P sb Q H n0 tk s' o0 tk' n' t0 l hp hr =>
    simp only at hsh hsing
    have hn := single_get hsing hp; subst hn
    rcases hsh with ⟨s1, hP, hM⟩ | ⟨s1, hP, hM⟩ | ⟨s1, hP, hM⟩ | ⟨hP, hM⟩ | ⟨hP, hM⟩ <;>
      rw [hP] at hp <;> simp only [Option.some.injEq, PEntry.live.injEq, Proc.mk.injEq, reduceCtorEq] at hp
    · obtain ⟨rfl, -, rfl⟩ := hp; cases (T1_det h _ _ _ hr).1
    · obtain ⟨rfl, -, rfl⟩ := hp; cases (T2_det h _ _ _ hr).1
    · obtain ⟨rfl, -, rfl⟩ := hp
      have := hr.not_outcome; rw [hT3 h] at this; simp [Val.isOutcome] at this
  | r_p_proc_message_l s v M P sb Q H n0 v' s' c v'' l hp hr =>
    simp only at hv hsb hq hH hsh hsing
    subst hv hsb hq hH
    have hn := single_get hsing hp; subst hn
    rcases hsh with ⟨s1, hP, hM⟩ | ⟨s1, hP, hM⟩ | ⟨s1, hP, hM⟩ | ⟨hP, hM⟩ | ⟨hP, hM⟩ <;>
      rw [hP] at hp <;> simp only [Option.some.injEq, PEntry.live.injEq, Proc.mk.injEq, reduceCtorEq] at hp
    · exact absurd hp.1 (notOutcome_ne_succeed (T1_no h))
    · exact absurd hp.1 (notOutcome_ne_succeed (T2_no h))
    · obtain ⟨h1, -, h3⟩ := hp
      rw [hT3 h] at h1; cases h1; cases h3
      rw [hC h] at hr
      obtain ⟨rfl, rfl⟩ := recvL_task_inv hr
      subst hM
      exact ⟨⟨rfl, rfl, rfl, rfl, n0, single_set _ hsing, .inr (.inr (.inr (.inl ⟨set_get_self _ _ _, rfl⟩)))⟩,
        noMatch_nil pat⟩
  | r_p_proc_end_l s v M P sb Q H n0 tk s' o0 hp hend =>
    simp only at hsh hsing
    have hn := single_get hsing hp; subst hn
    rcases hsh with ⟨s1, hP, hM⟩ | ⟨s1, hP, hM⟩ | ⟨s1, hP, hM⟩ | ⟨hP, hM⟩ | ⟨hP, hM⟩ <;>
      rw [hP] at hp <;> simp only [Option.some.injEq, PEntry.live.injEq, Proc.mk.injEq, reduceCtorEq] at hp
    · obtain ⟨rfl, -, rfl⟩ := hp
      rcases hend with ⟨v', he⟩ | ⟨v', he, -⟩
      · exact absurd he (notOutcome_ne_fail (T1_no h))
      · exact absurd he (notOutcome_ne_succeed (T1_no h))
    · obtain ⟨rfl, -, rfl⟩ := hp
      rcases hend with ⟨v', he⟩ | ⟨v', he, -⟩
      · exact absurd he (notOutcome_ne_fail (T2_no h))
      · exact absurd he (notOutcome_ne_succeed (T2_no h))
    · obtain ⟨rfl, -, rfl⟩ := hp
      rcases hend with ⟨v', he⟩ | ⟨v', -, he⟩
      · rw [hT3 h] at he; cases he
      · cases he
  | r_p_in_accept_l _ _ _ _ _ _ _ p τ _ _ _ _ _ _ hpe =>
    rw [hPE h] at hpe; cases hpe
  | r_p_in_reject_l _ p τ _ hpe => rw [hPE h] at hpe; cases hpe
  | r_p_out_l s v M P sb Q H p j J hq' =>
    simp only at hq; subst hq; cases hq'
  | r_p_wait_l s v M P sb Q H d _ =>
    exact ⟨⟨hv, hsb, hq, hH, n, hsing, hsh⟩, noMatch_nil pat⟩
  | r_p_platform_l _ _ _ hp => exact absurd hp platStep_empty

/-- The invariant, under the book's host. -/
def inv : TestInv { w with host := .any } pat where
  r0 := r0
  I := I
  prog_ok := fun v lm d => by
    obtain ⟨rfl, rfl⟩ := Mod.evProgram_unique_l (prog_eval facts_true) v lm d
    exact ⟨rfl, noMatch_nil pat⟩
  start_ok := fun j K0 ls hs => start_ok facts_true j K0 ls hs
  step_ok := fun K hs a K' l hs' hI hst _ => step_ok facts_true K hs a K' l hs' hI hst

/-- CHECK-NOT `handler called`: no execution the book allows, under any host, logs it. [native]
    (the printed form of the one log entry, `upd2_log`) -/
theorem checkNot : w_elm_core_TaskOnErrorSucceedTest.HoldsNot "handler called" := holdsNot_any inv

end StandardElm.Prog.Inv.TaskOnErrorSucceedTest
