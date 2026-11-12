/-
  A Standard Definition of Elm? Mechanisation: StandardA88PortNonFiniteTest's CHECK-NOT, plan
  step 6.

  `CHECK-NOT: Just`, under the test runner's echo host. init starts a process T1 that sleeps 10 ms
  and then sends Start; the update for Start sends NaN and +∞ on echoOut (type Float), which encode
  as null (A88, r:e-enc-float-null); the host sends each back on echoIn (type Maybe Float), where
  null decodes as Nothing, so each is received as `Got Nothing`, whose update logs `got: Nothing`.
  The invariant: model (), subscription S, no pending platform command, the queue of echoOut and the
  host's state hold only null, every queued message is Start or `Got Nothing`, and one process, at
  T1, T2 or T3 or ended.

  The echo host is needed: the book's host may send 1.5, which decodes as `Just 1.5`.
-/
import StandardElmMech.Prog.Invariant
import StandardElmMech.Generated.Worker01

namespace StandardElm.Prog.Inv.StandardA88PortNonFiniteTest
open StandardElm StandardElm.Prog StandardElm.Eff

set_option maxRecDepth 8192

abbrev w : WorkerTest := w_elm_StandardA88PortNonFiniteTest
def ms : List Mod.Module := w.prog.modules
def PE : PortEnv := portEnv ms
abbrev o : Oracle := .const false
abbrev N : Nat := workerFuel
abbrev pat : String := "Just"

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
def start : Val := succArg T3
def subsRes : Res Val := appVal o N FS .unit 0
def S : Val := subsRes.get
def recvRes : Res Val := recvL o N S (.port "echoIn" .null) 0
def g : Val := recvRes.get
def uS1 : Res Val := appVal o N FU start 0
def uS2 : Res Val := appVal o N uS1.get .unit 0
def CMS : Val := tupleSnd uS2.get
def d1 : Val := ((flat2 CMS).getD (.unit, .unit)).1
def d2 : Val := ((flat2 CMS).getD (.unit, .unit)).2
def uG1 : Res Val := appVal o N FU g 0
def uG2 : Res Val := appVal o N uG1.get .unit 0
def CMG : Val := tupleSnd uG2.get

/-- The first step's action is a sleep. -/
def sleepStep : Bool :=
  match step1.get.1 with
  | some x => x.prim == .sleep
  | none => false

def facts : Bool :=
  progRes.isAt 0 && progRes.log.isEmpty && isProg progRes.get &&
  (field r0 "init").isSome && (field r0 "update").isSome && (field r0 "subscriptions").isSome &&
  decide (PE = [("echoOut", .out, .float), ("echoIn", .inn, .maybe .float)]) &&
  initRes.isAt 0 && initRes.log.isEmpty && isPair initRes.get && isUnit (tupleFst initRes.get) &&
  isTaskLeaf C &&
  step1.isAt 0 && sleepStep && step1.log.isEmpty && !T1.isOutcome &&
  step2.isAt 0 && step2.get.1.isNone && step2.log.isEmpty && !T2.isOutcome &&
  isSucceed T3 &&
  subsRes.isAt 0 && subsRes.log.isEmpty && isLeaf S &&
  recvRes.isAt 0 && recvRes.log.isEmpty &&
  uS1.isAt 0 && uS1.log.isEmpty && uS2.isAt 0 && uS2.log.isEmpty && isPair uS2.get &&
  isUnit (tupleFst uS2.get) && (flat2 CMS).isSome && outLeafIs d1 "echoOut" .null &&
  outLeafIs d2 "echoOut" .null &&
  uG1.isAt 0 && uG1.log.isEmpty && uG2.isAt 0 && isPair uG2.get && isUnit (tupleFst uG2.get) &&
  flatEmpty CMG

theorem facts_true : facts = true := by decide +kernel

/-- The update's log for `Got Nothing`, printed, does not contain the pattern. [native] (the
    printer is defined by well-founded recursion, which the kernel does not unfold) -/
theorem uG2_log : NoMatch pat uG2.log := noMatch_of_B (by native_decide)

structure Facts : Prop where
  prog_at : progRes.isAt 0 = true
  prog_log : progRes.log = []
  prog_is : isProg progRes.get = true
  init_some : (field r0 "init").isSome = true
  update_some : (field r0 "update").isSome = true
  subs_some : (field r0 "subscriptions").isSome = true
  pe : PE = [("echoOut", .out, .float), ("echoIn", .inn, .maybe .float)]
  init_at : initRes.isAt 0 = true
  init_log : initRes.log = []
  init_pair : isPair initRes.get = true
  init_unit : isUnit (tupleFst initRes.get) = true
  c_leaf : isTaskLeaf C = true
  s1_at : step1.isAt 0 = true
  s1_sleep : sleepStep = true
  s1_log : step1.log = []
  t1_no : T1.isOutcome = false
  s2_at : step2.isAt 0 = true
  s2_silent : step2.get.1 = none
  s2_log : step2.log = []
  t2_no : T2.isOutcome = false
  t3_succ : isSucceed T3 = true
  subs_at : subsRes.isAt 0 = true
  subs_log : subsRes.log = []
  s_leaf : isLeaf S = true
  recv_at : recvRes.isAt 0 = true
  recv_log : recvRes.log = []
  us1_at : uS1.isAt 0 = true
  us1_log : uS1.log = []
  us2_at : uS2.isAt 0 = true
  us2_log : uS2.log = []
  us2_pair : isPair uS2.get = true
  us2_unit : isUnit (tupleFst uS2.get) = true
  cms_two : (flat2 CMS).isSome = true
  d1_out : outLeafIs d1 "echoOut" .null = true
  d2_out : outLeafIs d2 "echoOut" .null = true
  ug1_at : uG1.isAt 0 = true
  ug1_log : uG1.log = []
  ug2_at : uG2.isAt 0 = true
  ug2_pair : isPair uG2.get = true
  ug2_unit : isUnit (tupleFst uG2.get) = true
  cmg_empty : flatEmpty CMG = true

theorem f (h : facts = true) : Facts := by
  simp only [facts, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.isEmpty_iff,
    Option.isNone_iff_eq_none] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩,
    a11⟩, a12⟩, a13⟩, a14⟩, a15⟩, a16⟩, a17⟩, a18⟩, a19⟩, a20⟩, a21⟩, a22⟩, a23⟩, a24⟩, a25⟩,
    a26⟩, a27⟩, a28⟩, a29⟩, a30⟩, a31⟩, a32⟩, a33⟩, a34⟩, a35⟩, a36⟩, a37⟩, a38⟩, a39⟩, a40⟩, a41⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20,
    a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37, a38, a39,
    a40, a41⟩

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

theorem hPE_in {p : String} {τ : PTy} (hp : fmLookup PE p = some (.inn, τ)) :
    p = "echoIn" ∧ τ = .maybe .float := by
  rw [(f h).pe] at hp
  simp only [fmLookup] at hp
  split at hp
  · cases hp
  · split at hp
    · rename_i he; simp at he hp; exact ⟨he.symm, hp.symm⟩
    · cases hp

theorem hQ0 : qInit PE = [("echoOut", [])] := by rw [(f h).pe]; rfl

theorem init_det : ∀ w l, AppValL FI .unit w l → w = .tuple .unit C none ∧ l = [] := by
  have F := f h
  intro w l d
  obtain ⟨rfl, rfl⟩ := appValL_det F.init_at w l d
  refine ⟨?_, F.init_log⟩
  change initRes.get = _
  rw [pair_eq F.init_pair, unit_eq F.init_unit]; rfl

theorem hC : C = .leaf .task T1 := taskLeaf_eq (f h).c_leaf

theorem sleep_of : ∃ x, step1.get.1 = some x ∧ x.prim = .sleep := by
  have := (f h).s1_sleep
  unfold sleepStep at this
  split at this
  · rename_i x hx; exact ⟨x, hx, by simpa using this⟩
  · cases this

theorem T1_det : ∀ a t l, TaskRedL T1 a t l → a = step1.get.1 ∧ t = T2 ∧ l = [] := by
  have F := f h
  obtain ⟨x, hx, hp⟩ := sleep_of h
  intro a t l d
  obtain ⟨rfl, rfl, rfl⟩ := taskRedL_det F.s1_at
    (by change ∀ y, step1.get.1 = some y → _; rw [hx]; intro y hy; cases hy; rw [hp]; decide) a t l d
  exact ⟨rfl, rfl, F.s1_log⟩

theorem T1_sleep {a : Option Action} {t : Val} {l : Log} (d : TaskRedL T1 a t l) :
    ∃ x, a = some x ∧ x.prim = .sleep := by
  obtain ⟨x, hx, hp⟩ := sleep_of h
  exact ⟨x, (T1_det h _ _ _ d).1.trans hx, hp⟩

theorem T1_no : T1.isOutcome = false := (f h).t1_no

theorem T2_det : ∀ a t l, TaskRedL T2 a t l → a = none ∧ t = T3 ∧ l = [] := by
  have F := f h
  intro a t l d
  obtain ⟨rfl, rfl, rfl⟩ := taskRedL_det F.s2_at
    (by change ∀ x, step2.get.1 = some x → _; rw [F.s2_silent]; intro x hx; cases hx) a t l d
  exact ⟨F.s2_silent, rfl, F.s2_log⟩

theorem T2_no : T2.isOutcome = false := (f h).t2_no

theorem hT3 : T3 = .succeed start := succeed_eq (f h).t3_succ

theorem subs_det : ∀ w l, AppValL FS .unit w l → w = S ∧ l = [] := by
  have F := f h
  intro w l d
  exact ⟨(appValL_det F.subs_at w l d).1, (appValL_det F.subs_at w l d).2.trans F.subs_log⟩

theorem hS : flat S = some [S] := flat_leaf (f h).s_leaf

theorem accept_ok {Ms : List Val} {l : Log} (d : AcceptMsgsL [S] (.port "echoIn" .null) Ms l) :
    Ms = [g] ∧ l = [] := by
  obtain ⟨rfl, rfl⟩ := acceptMsgsL_one (f h).recv_at d
  exact ⟨rfl, (f h).recv_log⟩

theorem uS1_det : ∀ w l, AppValL FU start w l → w = uS1.get ∧ l = [] := by
  have F := f h
  intro w l d
  exact ⟨(appValL_det F.us1_at w l d).1, (appValL_det F.us1_at w l d).2.trans F.us1_log⟩

theorem uS2_det : ∀ w l, AppValL uS1.get .unit w l → w = .tuple .unit CMS none ∧ l = [] := by
  have F := f h
  intro w l d
  obtain ⟨rfl, rfl⟩ := appValL_det F.us2_at w l d
  refine ⟨?_, F.us2_log⟩
  change uS2.get = _
  rw [pair_eq F.us2_pair, unit_eq F.us2_unit]; rfl

theorem hCMS : flat CMS = some [d1, d2] := flat_two (f h).cms_two
theorem hd1 : leafCore d1 = some (.out "echoOut", .bv .null) := outLeaf_eq (f h).d1_out
theorem hd2 : leafCore d2 = some (.out "echoOut", .bv .null) := outLeaf_eq (f h).d2_out

theorem uG1_det : ∀ w l, AppValL FU g w l → w = uG1.get ∧ l = [] := by
  have F := f h
  intro w l d
  exact ⟨(appValL_det F.ug1_at w l d).1, (appValL_det F.ug1_at w l d).2.trans F.ug1_log⟩

theorem uG2_det : ∀ w l, AppValL uG1.get .unit w l → w = .tuple .unit CMG none ∧ l = uG2.log := by
  have F := f h
  intro w l d
  obtain ⟨rfl, rfl⟩ := appValL_det F.ug2_at w l d
  refine ⟨?_, rfl⟩
  change uG2.get = _
  rw [pair_eq F.ug2_pair, unit_eq F.ug2_unit]; rfl

theorem hCMG : flat CMG = some [] := flat_empty (f h).cmg_empty

end

/-! ## The invariant -/

/-- The process's entry. -/
def Entry (e : PEntry) : Prop :=
  (∃ s', e = .live ⟨T1, s', some C⟩) ∨ (∃ s', e = .live ⟨T2, s', some C⟩) ∨
  (∃ s', e = .live ⟨T3, s', some C⟩) ∨ e = .ended

def I (K : Config) (hs : List BVal) : Prop :=
  K.model = .unit ∧ K.subs = S ∧ K.pending = [] ∧
  (∃ js, K.outq = [("echoOut", js)] ∧ ∀ j ∈ js, j = .null) ∧ (∀ j ∈ hs, j = .null) ∧
  (∀ v ∈ K.msgs, v = start ∨ v = g) ∧
  ∃ n e, Single K.procs n ∧ K.procs.get n = some e ∧ Entry e

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
    refine ⟨⟨rfl, rfl, rfl, ⟨[], by rw [hQ0 h], by simp⟩, by simp, by simp, n, _, single_init n _,
      set_get_self _ _ _, .inl ⟨0, by rw [hC h]⟩⟩, noMatch_nil pat⟩

/-- Every transition keeps the invariant and logs nothing with the pattern. [native] (the printed
    form of the update's log entry) -/
theorem step_ok (h : facts = true) (K : Config) (hs : List BVal) (a : Option Event) (K' : Config)
    (l : Log) (hs' : List BVal) (hI : I K hs) (hst : StepL PE r0 K a K' l)
    (hh : HostAllows (.echo "echoOut" "echoIn") hs a hs') : I K' hs' ∧ NoMatch pat l := by
  obtain ⟨hv, hsb, hH, ⟨js, hq, hjs⟩, hhs, hM, n, e, hsing, hPn, hE⟩ := hI
  cases hst with
  | r_p_update_l s v v1 M P sb Q H fu fs v2 v' cm cs L P' Q' H' sb' l1 l2 l3 hfu hfs ha1 ha2 hfl hp hd ha3 =>
    simp only at hv hsb hq hH hM hsing hPn
    subst hv hsb hq hH
    obtain rfl := Option.some.inj (hfu.symm.trans (hFU h))
    obtain rfl := Option.some.inj (hfs.symm.trans (hFS h))
    have hs'eq := hostAllows_other (by simp) (by simp) hh
    subst hs'eq
    have hMt : ∀ v ∈ M, v = start ∨ v = g := fun v hv => hM v (by simp [hv])
    rcases hM v1 (by simp) with rfl | rfl
    · -- Start: the update sends NaN and +∞, both null
      obtain ⟨rfl, rfl⟩ := uS1_det h _ _ ha1
      obtain ⟨he, rfl⟩ := uS2_det h _ _ ha2
      simp only [Val.tuple.injEq] at he
      obtain ⟨rfl, rfl, -⟩ := he
      rw [hCMS h] at hfl; cases hfl
      have hL : ∀ c ∈ L, ∃ j, leafCore c = some (.out "echoOut", .bv j) := by
        intro c hc
        rcases List.mem_cons.mp (hp.mem_iff.mp hc) with rfl | hc
        · exact ⟨_, hd1 h⟩
        · simp at hc; subst hc; exact ⟨_, hd2 h⟩
      obtain ⟨rfl, rfl, rfl⟩ := dispatch_outs hL hd
      obtain ⟨rfl, rfl⟩ := subs_det h _ _ ha3
      refine ⟨⟨rfl, rfl, rfl, ⟨_, rfl, ?_⟩, hhs, hMt, n, e, hsing, hPn, hE⟩, by simpa using noMatch_nil pat⟩
      intro j hj
      rcases List.mem_append.mp hj with hj | hj
      · exact hjs j hj
      · rcases perm_two hp with rfl | rfl <;>
          simp [outValue_of (hd1 h), outValue_of (hd2 h)] at hj <;> exact hj
    · -- Got Nothing: the update logs it
      obtain ⟨rfl, rfl⟩ := uG1_det h _ _ ha1
      obtain ⟨he, rfl⟩ := uG2_det h _ _ ha2
      simp only [Val.tuple.injEq] at he
      obtain ⟨rfl, rfl, -⟩ := he
      rw [hCMG h] at hfl; cases hfl
      have := perm_nil' hp; subst this
      obtain ⟨rfl, rfl, rfl⟩ := dispatch_nil hd
      obtain ⟨rfl, rfl⟩ := subs_det h _ _ ha3
      exact ⟨⟨rfl, rfl, rfl, ⟨js, rfl, hjs⟩, hhs, hMt, n, e, hsing, hPn, hE⟩, by simpa using uG2_log⟩
  | r_p_proc_step_l s v M P sb Q H n0 tk s' o0 a tk' l hp hr hpl =>
    simp only at hsing hPn
    have hn := single_get hsing hp; subst hn
    rw [hPn] at hp; cases hp
    rcases hE with ⟨s1, he⟩ | ⟨s1, he⟩ | ⟨s1, he⟩ | he <;> simp only [PEntry.live.injEq, Proc.mk.injEq, reduceCtorEq] at he
    · obtain ⟨rfl, -, rfl⟩ := he
      obtain ⟨x, rfl, -⟩ := T1_sleep h hr
      exact absurd (hpl x rfl) (by simp [platPrims])
    · obtain ⟨rfl, -, rfl⟩ := he
      obtain ⟨rfl, rfl, rfl⟩ := T2_det h _ _ _ hr
      have hs'eq := hostAllows_other (by simp) (by simp) hh
      subst hs'eq
      exact ⟨⟨hv, hsb, hH, ⟨js, hq, hjs⟩, hhs, hM, n0, _, single_set _ hsing, set_get_self _ _ _,
        .inr (.inr (.inl ⟨s, rfl⟩))⟩, noMatch_nil pat⟩
    · obtain ⟨rfl, -, rfl⟩ := he
      have := hr.not_outcome; rw [hT3 h] at this; simp [Val.isOutcome] at this
  | r_p_proc_sleep_l s v M P sb Q H n0 tk s' o0 tk' v0 t0 l hp hr _ =>
    simp only at hsing hPn
    have hn := single_get hsing hp; subst hn
    rw [hPn] at hp; cases hp
    rcases hE with ⟨s1, he⟩ | ⟨s1, he⟩ | ⟨s1, he⟩ | he <;> simp only [PEntry.live.injEq, Proc.mk.injEq, reduceCtorEq] at he
    · obtain ⟨rfl, -, rfl⟩ := he
      obtain ⟨-, rfl, rfl⟩ := T1_det h _ _ _ hr
      have hs'eq := hostAllows_other (by simp) (by simp) hh
      subst hs'eq
      exact ⟨⟨hv, hsb, hH, ⟨js, hq, hjs⟩, hhs, hM, n0, _, single_set _ hsing, set_get_self _ _ _,
        .inr (.inl ⟨s, rfl⟩)⟩, noMatch_nil pat⟩
    · obtain ⟨rfl, -, rfl⟩ := he; cases (T2_det h _ _ _ hr).1
    · obtain ⟨rfl, -, rfl⟩ := he
      have := hr.not_outcome; rw [hT3 h] at this; simp [Val.isOutcome] at this
  | r_p_proc_spawn_l s v M P sb Q H n0 tk s' o0 tk' t0 n' l hp hr _ =>
    simp only at hsing hPn
    have hn := single_get hsing hp; subst hn
    rw [hPn] at hp; cases hp
    rcases hE with ⟨s1, he⟩ | ⟨s1, he⟩ | ⟨s1, he⟩ | he <;> simp only [PEntry.live.injEq, Proc.mk.injEq, reduceCtorEq] at he
    · obtain ⟨rfl, -, rfl⟩ := he
      obtain ⟨x, hx, hpx⟩ := T1_sleep h hr
      cases hx; cases hpx
    · obtain ⟨rfl, -, rfl⟩ := he; cases (T2_det h _ _ _ hr).1
    · obtain ⟨rfl, -, rfl⟩ := he
      have := hr.not_outcome; rw [hT3 h] at this; simp [Val.isOutcome] at this
  | r_p_proc_kill_l s v M P sb Q H n0 tk s' o0 tk' n' t0 l hp hr =>
    simp only at hsing hPn
    have hn := single_get hsing hp; subst hn
    rw [hPn] at hp; cases hp
    rcases hE with ⟨s1, he⟩ | ⟨s1, he⟩ | ⟨s1, he⟩ | he <;> simp only [PEntry.live.injEq, Proc.mk.injEq, reduceCtorEq] at he
    · obtain ⟨rfl, -, rfl⟩ := he
      obtain ⟨x, hx, hpx⟩ := T1_sleep h hr
      cases hx; cases hpx
    · obtain ⟨rfl, -, rfl⟩ := he; cases (T2_det h _ _ _ hr).1
    · obtain ⟨rfl, -, rfl⟩ := he
      have := hr.not_outcome; rw [hT3 h] at this; simp [Val.isOutcome] at this
  | r_p_proc_message_l s v M P sb Q H n0 v' s' c v'' l hp hr =>
    simp only at hv hsb hq hH hM hsing hPn
    subst hv hsb hq hH
    have hn := single_get hsing hp; subst hn
    rw [hPn] at hp; cases hp
    have hs'eq := hostAllows_other (by simp) (by simp) hh
    subst hs'eq
    rcases hE with ⟨s1, he⟩ | ⟨s1, he⟩ | ⟨s1, he⟩ | he <;> simp only [PEntry.live.injEq, Proc.mk.injEq, reduceCtorEq] at he
    · exact absurd he.1.symm (notOutcome_ne_succeed (T1_no h))
    · exact absurd he.1.symm (notOutcome_ne_succeed (T2_no h))
    · obtain ⟨h1, -, h3⟩ := he
      rw [hT3 h] at h1; cases h1; cases h3
      rw [hC h] at hr
      obtain ⟨rfl, rfl⟩ := recvL_task_inv hr
      refine ⟨⟨rfl, rfl, rfl, ⟨js, rfl, hjs⟩, hhs, ?_, n0, _, single_set _ hsing, set_get_self _ _ _,
        .inr (.inr (.inr rfl))⟩, noMatch_nil pat⟩
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact hM v hv
      · simp at hv; exact .inl hv
  | r_p_proc_end_l s v M P sb Q H n0 tk s' o0 hp hend =>
    simp only at hsing hPn
    have hn := single_get hsing hp; subst hn
    rw [hPn] at hp; cases hp
    rcases hE with ⟨s1, he⟩ | ⟨s1, he⟩ | ⟨s1, he⟩ | he <;> simp only [PEntry.live.injEq, Proc.mk.injEq, reduceCtorEq] at he
    · obtain ⟨rfl, -, rfl⟩ := he
      rcases hend with ⟨v', he⟩ | ⟨v', he, -⟩
      · exact absurd he (notOutcome_ne_fail (T1_no h))
      · exact absurd he (notOutcome_ne_succeed (T1_no h))
    · obtain ⟨rfl, -, rfl⟩ := he
      rcases hend with ⟨v', he⟩ | ⟨v', he, -⟩
      · exact absurd he (notOutcome_ne_fail (T2_no h))
      · exact absurd he (notOutcome_ne_succeed (T2_no h))
    · obtain ⟨rfl, -, rfl⟩ := he
      rcases hend with ⟨v', he⟩ | ⟨v', -, he⟩
      · rw [hT3 h] at he; cases he
      · cases he
  | r_p_in_accept_l s v M P sb Q H p τ j v' cs L Ms l hpe hdec hfl hp hacc =>
    simp only at hv hsb hq hH hM hsing hPn
    subst hv hsb hq hH
    obtain ⟨rfl, rfl⟩ := hPE_in h hpe
    obtain ⟨-, rfl⟩ := hostAllows_echo_in hh
    have hj := hhs j (by simp)
    subst hj
    rw [hS h] at hfl; cases hfl
    have := perm_one hp; subst this
    obtain ⟨rfl, rfl⟩ := accept_ok h hacc
    refine ⟨⟨rfl, rfl, rfl, ⟨js, rfl, hjs⟩, fun j hj => hhs j (by simp [hj]), ?_, n, e, hsing, hPn, hE⟩,
      noMatch_nil pat⟩
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hM v hv
    · simp at hv; exact .inr hv
  | r_p_in_reject_l K p τ j hpe hno =>
    obtain ⟨-, rfl⟩ := hostAllows_echo_in hh
    exact ⟨⟨hv, hsb, hH, ⟨js, hq, hjs⟩, fun j hj => hhs j (by simp [hj]), hM, n, e, hsing, hPn, hE⟩,
      noMatch_nil pat⟩
  | r_p_out_l s v M P sb Q H p j J hq' =>
    simp only at hv hsb hq hH hM hsing hPn
    subst hv hsb hq hH
    simp only [fmLookup] at hq'
    split at hq'
    · rename_i hp
      simp only [beq_iff_eq] at hp
      subst hp
      simp only [Option.some.injEq] at hq'
      subst hq'
      have hfm : fmPlus [("echoOut", j :: J)] [("echoOut", J)] = [("echoOut", J)] := by simp [fmPlus]
      refine ⟨⟨rfl, rfl, rfl, ⟨J, hfm, fun j' hj' => hjs j' (by simp [hj'])⟩, ?_, hM, n, e, hsing, hPn, hE⟩,
        noMatch_nil pat⟩
      rcases hostAllows_echo_out hh with ⟨-, rfl⟩ | rfl
      · intro j' hj'
        rcases List.mem_append.mp hj' with hj' | hj'
        · exact hhs j' hj'
        · simp only [List.mem_singleton] at hj'; rw [hj']; exact hjs _ List.mem_cons_self
      · exact hhs
    · cases hq'
  | r_p_wait_l s v M P sb Q H d _ =>
    have hs'eq := hostAllows_other (by simp) (by simp) hh
    subst hs'eq
    exact ⟨⟨hv, hsb, hH, ⟨js, hq, hjs⟩, hhs, hM, n, e, hsing, hPn, hE⟩, noMatch_nil pat⟩
  | r_p_platform_l _ _ _ hp => exact absurd hp platStep_empty

/-- The invariant, under the echo host. -/
def inv : TestInv w pat where
  r0 := r0
  I := I
  prog_ok := fun v lm d => by
    obtain ⟨rfl, rfl⟩ := Mod.evProgram_unique_l (prog_eval facts_true) v lm d
    exact ⟨rfl, noMatch_nil pat⟩
  start_ok := fun j K0 ls hs => start_ok facts_true j K0 ls hs
  step_ok := fun K hs a K' l hs' hI hst hh => step_ok facts_true K hs a K' l hs' hI hst hh

/-- CHECK-NOT `Just`: no execution the book allows, under the echo host, logs it. [native] (the
    printed form of the log entry `got: Nothing`, `uG2_log`) -/
theorem checkNot : w_elm_StandardA88PortNonFiniteTest.HoldsNot "Just" := inv.sound

end StandardElm.Prog.Inv.StandardA88PortNonFiniteTest
