/-
  A Standard Definition of Elm? Mechanisation: PortIncomingRejectTest's CHECK-NOT, plan step 6.

  `CHECK-NOT: received: null`, under the test runner's echo host. The program sends `Nothing` and
  `Just "ok"` on echoOut (type Maybe String), which go out as null and "ok"; the host sends each
  back on echoIn (type String). null does not decode at String, so r:p-in-reject drops it; "ok" is
  received as `Received "ok"`, whose update logs `received: "ok"`. The invariant: model (),
  subscription S, no process, no pending platform command, the queue of echoOut and the host's
  state hold only null and "ok", and every queued message is `Received "ok"`.

  The echo host is needed: the book's host may send the string "received: null", which is
  received and logged as `received: "received: null"`.
-/
import StandardElmMech.Prog.Invariant
import StandardElmMech.Generated.Worker01

namespace StandardElm.Prog.Inv.PortIncomingRejectTest
open StandardElm StandardElm.Prog StandardElm.Eff

set_option maxRecDepth 8192

abbrev w : WorkerTest := w_elm_PortIncomingRejectTest
def ms : List Mod.Module := w.prog.modules
def PE : PortEnv := portEnv ms
abbrev o : Oracle := .const false
abbrev N : Nat := workerFuel
abbrev pat : String := "received: null"
abbrev ok : BVal := .str "ok"

/-! ## The values, as the evaluator computes them -/

def progRes : Res Val := Mod.evProgram o N (Mod.Btest []) ms 0
def r0 : List (String × Val) := progRec progRes.get
def FI : Val := (field r0 "init").getD .unit
def FU : Val := (field r0 "update").getD .unit
def FS : Val := (field r0 "subscriptions").getD .unit
def initRes : Res Val := appVal o N FI .unit 0
def CM : Val := tupleSnd initRes.get
def c1 : Val := ((flat2 CM).getD (.unit, .unit)).1
def c2 : Val := ((flat2 CM).getD (.unit, .unit)).2
def subsRes : Res Val := appVal o N FS .unit 0
def S : Val := subsRes.get
def recvRes : Res Val := recvL o N S (.port "echoIn" ok) 0
def m : Val := recvRes.get
def upd1 : Res Val := appVal o N FU m 0
def U : Val := upd1.get
def upd2 : Res Val := appVal o N U .unit 0
def CM2 : Val := tupleSnd upd2.get

def facts : Bool :=
  progRes.isAt 0 && progRes.log.isEmpty && isProg progRes.get &&
  (field r0 "init").isSome && (field r0 "update").isSome && (field r0 "subscriptions").isSome &&
  decide (PE = [("echoOut", .out, .maybe .string), ("echoIn", .inn, .string)]) &&
  initRes.isAt 0 && initRes.log.isEmpty && isPair initRes.get && isUnit (tupleFst initRes.get) &&
  (flat2 CM).isSome && outLeafIs c1 "echoOut" .null && outLeafIs c2 "echoOut" ok &&
  subsRes.isAt 0 && subsRes.log.isEmpty && isLeaf S &&
  recvRes.isAt 0 && recvRes.log.isEmpty &&
  upd1.isAt 0 && upd1.log.isEmpty &&
  upd2.isAt 0 && isPair upd2.get && isUnit (tupleFst upd2.get) && flatEmpty CM2 &&
  (dec .string .null).isNone && (dec .string ok).isSome

theorem facts_true : facts = true := by decide +kernel

/-- The update's log, printed as Debug.log prints it, does not contain the pattern. [native]
    (the printer is defined by well-founded recursion, which the kernel does not unfold) -/
theorem upd2_log : NoMatch pat upd2.log := noMatch_of_B (by native_decide)

structure Facts : Prop where
  prog_at : progRes.isAt 0 = true
  prog_log : progRes.log = []
  prog_is : isProg progRes.get = true
  init_some : (field r0 "init").isSome = true
  update_some : (field r0 "update").isSome = true
  subs_some : (field r0 "subscriptions").isSome = true
  pe : PE = [("echoOut", .out, .maybe .string), ("echoIn", .inn, .string)]
  init_at : initRes.isAt 0 = true
  init_log : initRes.log = []
  init_pair : isPair initRes.get = true
  init_unit : isUnit (tupleFst initRes.get) = true
  cm_two : (flat2 CM).isSome = true
  c1_out : outLeafIs c1 "echoOut" .null = true
  c2_out : outLeafIs c2 "echoOut" ok = true
  subs_at : subsRes.isAt 0 = true
  subs_log : subsRes.log = []
  s_leaf : isLeaf S = true
  recv_at : recvRes.isAt 0 = true
  recv_log : recvRes.log = []
  u1_at : upd1.isAt 0 = true
  u1_log : upd1.log = []
  u2_at : upd2.isAt 0 = true
  u2_pair : isPair upd2.get = true
  u2_unit : isUnit (tupleFst upd2.get) = true
  cm2_empty : flatEmpty CM2 = true
  dec_null : (dec .string .null).isNone = true
  dec_ok : (dec .string ok).isSome = true

theorem f (h : facts = true) : Facts := by
  simp only [facts, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩, a12⟩, a13⟩, a14⟩,
    a15⟩, a16⟩, a17⟩, a18⟩, a19⟩, a20⟩, a21⟩, a22⟩, a23⟩, a24⟩, a25⟩, a26⟩, a27⟩ := h
  exact ⟨a1, List.isEmpty_iff.mp a2, a3, a4, a5, a6, a7, a8, List.isEmpty_iff.mp a9, a10, a11, a12, a13,
    a14, a15, List.isEmpty_iff.mp a16, a17, a18, List.isEmpty_iff.mp a19, a20, List.isEmpty_iff.mp a21,
    a22, a23, a24, a25, a26, a27⟩

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

theorem hPE_in {p : String} {τ : PTy} (hp : fmLookup PE p = some (.inn, τ)) : p = "echoIn" ∧ τ = .string := by
  rw [(f h).pe] at hp
  simp only [fmLookup] at hp
  split at hp
  · cases hp
  · split at hp
    · rename_i he; simp at he hp; exact ⟨he.symm, hp.symm⟩
    · cases hp

theorem hQ0 : qInit PE = [("echoOut", [])] := by rw [(f h).pe]; rfl

theorem init_det : ∀ w l, AppValL FI .unit w l → w = .tuple .unit CM none ∧ l = [] := by
  have F := f h
  intro w l d
  obtain ⟨rfl, rfl⟩ := appValL_det F.init_at w l d
  refine ⟨?_, F.init_log⟩
  change initRes.get = _
  rw [pair_eq F.init_pair, unit_eq F.init_unit]; rfl

theorem hCM : flat CM = some [c1, c2] := flat_two (f h).cm_two
theorem hc1 : leafCore c1 = some (.out "echoOut", .bv .null) := outLeaf_eq (f h).c1_out
theorem hc2 : leafCore c2 = some (.out "echoOut", .bv ok) := outLeaf_eq (f h).c2_out

theorem subs_det : ∀ w l, AppValL FS .unit w l → w = S ∧ l = [] := by
  have F := f h
  intro w l d
  exact ⟨(appValL_det F.subs_at w l d).1, (appValL_det F.subs_at w l d).2.trans F.subs_log⟩

theorem hS : flat S = some [S] := flat_leaf (f h).s_leaf

theorem accept_ok {Ms : List Val} {l : Log} (d : AcceptMsgsL [S] (.port "echoIn" ok) Ms l) :
    Ms = [m] ∧ l = [] := by
  obtain ⟨rfl, rfl⟩ := acceptMsgsL_one (f h).recv_at d
  exact ⟨rfl, (f h).recv_log⟩

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

theorem no_dec_null : ¬ ∃ v, Eff.Dec .string .null v := by
  rintro ⟨v, hv⟩
  have := (dec_iff _ _ _).mp hv
  have h2 := (f h).dec_null
  rw [this] at h2; cases h2

theorem dec_ok : ∃ v, Eff.Dec .string ok v := by
  have h2 := (f h).dec_ok
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h2
  exact ⟨v, (dec_iff _ _ _).mpr hv⟩

end

/-! ## The invariant -/

def Good (j : BVal) : Prop := j = .null ∨ j = ok

def I (K : Config) (hs : List BVal) : Prop :=
  K.model = .unit ∧ K.subs = S ∧ (∀ q, K.procs.get q = none) ∧ K.pending = [] ∧
  (∃ js, K.outq = [("echoOut", js)] ∧ ∀ j ∈ js, Good j) ∧ (∀ j ∈ hs, Good j) ∧ ∀ v ∈ K.msgs, v = m

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
    rw [hCM h] at hfl2; cases hfl2
    rw [hQ0 h] at hd
    have hL : ∀ c ∈ L, ∃ j, leafCore c = some (.out "echoOut", .bv j) := by
      intro c hc
      rcases List.mem_cons.mp (hp.mem_iff.mp hc) with rfl | hc
      · exact ⟨_, hc1 h⟩
      · simp at hc; subst hc; exact ⟨_, hc2 h⟩
    obtain ⟨rfl, rfl, rfl⟩ := dispatch_outs hL hd
    obtain ⟨rfl, rfl⟩ := subs_det h _ _ ha2
    refine ⟨⟨rfl, rfl, fun _ => rfl, rfl, ⟨_, rfl, ?_⟩, fun _ hj => by simp at hj, fun _ hv => by simp at hv⟩,
      noMatch_nil pat⟩
    intro j hj
    simp only [List.nil_append] at hj
    rcases perm_two hp with rfl | rfl <;>
      simp [outValue_of (hc1 h), outValue_of (hc2 h)] at hj <;> rcases hj with rfl | rfl <;>
      simp [Good]

/-- Every transition keeps the invariant and logs nothing with the pattern. [native] (the printed
    form of the update's log entry) -/
theorem step_ok (h : facts = true) (K : Config) (hs : List BVal) (a : Option Event) (K' : Config)
    (l : Log) (hs' : List BVal) (hI : I K hs) (hst : StepL PE r0 K a K' l)
    (hh : HostAllows (.echo "echoOut" "echoIn") hs a hs') : I K' hs' ∧ NoMatch pat l := by
  obtain ⟨hv, hsb, hP, hH, ⟨js, hq, hjs⟩, hhs, hM⟩ := hI
  cases hst with
  | r_p_update_l s v v1 M P sb Q H fu fs v2 v' cm cs L P' Q' H' sb' l1 l2 l3 hfu hfs ha1 ha2 hfl hp hd ha3 =>
    simp only at hv hsb hq hH hM hP
    subst hv hsb hq hH
    obtain rfl := Option.some.inj (hfu.symm.trans (hFU h))
    obtain rfl := Option.some.inj (hfs.symm.trans (hFS h))
    have hv1 : v1 = m := hM v1 (by simp)
    subst hv1
    obtain ⟨rfl, rfl⟩ := upd1_det h _ _ ha1
    obtain ⟨he, rfl⟩ := upd2_det h _ _ ha2
    simp only [Val.tuple.injEq] at he
    obtain ⟨rfl, rfl, -⟩ := he
    rw [hCM2 h] at hfl; cases hfl
    have := perm_nil' hp; subst this
    obtain ⟨rfl, rfl, rfl⟩ := dispatch_nil hd
    obtain ⟨rfl, rfl⟩ := subs_det h _ _ ha3
    have hs'eq := hostAllows_other (by simp) (by simp) hh
    subst hs'eq
    refine ⟨⟨rfl, rfl, hP, rfl, ⟨js, rfl, hjs⟩, hhs, fun v hv => hM v (by simp [hv])⟩, ?_⟩
    simpa using upd2_log
  | r_p_proc_step_l _ _ _ P _ _ _ n0 _ _ _ _ _ _ hp _ _ => simp only at hP; rw [hP] at hp; cases hp
  | r_p_proc_sleep_l _ _ _ P _ _ _ n0 _ _ _ _ _ _ _ hp _ _ => simp only at hP; rw [hP] at hp; cases hp
  | r_p_proc_spawn_l _ _ _ P _ _ _ n0 _ _ _ _ _ _ _ hp _ _ => simp only at hP; rw [hP] at hp; cases hp
  | r_p_proc_kill_l _ _ _ P _ _ _ n0 _ _ _ _ _ _ _ hp _ => simp only at hP; rw [hP] at hp; cases hp
  | r_p_proc_message_l _ _ _ P _ _ _ n0 _ _ _ _ _ hp _ => simp only at hP; rw [hP] at hp; cases hp
  | r_p_proc_end_l _ _ _ P _ _ _ n0 _ _ _ hp _ => simp only at hP; rw [hP] at hp; cases hp
  | r_p_in_accept_l s v M P sb Q H p τ j v' cs L Ms l hpe hdec hfl hp hacc =>
    simp only at hv hsb hq hH hM hP
    subst hv hsb hq hH
    obtain ⟨rfl, rfl⟩ := hPE_in h hpe
    obtain ⟨-, rfl⟩ := hostAllows_echo_in hh
    have hj := hhs j (by simp)
    rcases hj with rfl | rfl
    · exact absurd ⟨v', hdec⟩ (no_dec_null h)
    · rw [hS h] at hfl; cases hfl
      have := perm_one hp; subst this
      obtain ⟨rfl, rfl⟩ := accept_ok h hacc
      refine ⟨⟨rfl, rfl, hP, rfl, ⟨js, rfl, hjs⟩, fun j hj => hhs j (by simp [hj]), ?_⟩, noMatch_nil pat⟩
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact hM v hv
      · simpa using hv
  | r_p_in_reject_l K p τ j hpe hno =>
    obtain ⟨-, rfl⟩ := hostAllows_echo_in hh
    exact ⟨⟨hv, hsb, hP, hH, ⟨js, hq, hjs⟩, fun j hj => hhs j (by simp [hj]), hM⟩, noMatch_nil pat⟩
  | r_p_out_l s v M P sb Q H p j J hq' =>
    simp only at hv hsb hq hH hM hP
    subst hv hsb hq hH
    simp only [fmLookup] at hq'
    split at hq'
    · rename_i hp
      simp only [beq_iff_eq] at hp
      subst hp
      simp only [Option.some.injEq] at hq'
      subst hq'
      have hfm : fmPlus [("echoOut", j :: J)] [("echoOut", J)] = [("echoOut", J)] := by simp [fmPlus]
      refine ⟨⟨rfl, rfl, hP, rfl, ⟨J, hfm, fun j' hj' => hjs j' (by simp [hj'])⟩, ?_, hM⟩, noMatch_nil pat⟩
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
    exact ⟨⟨hv, hsb, hP, hH, ⟨js, hq, hjs⟩, hhs, hM⟩, noMatch_nil pat⟩
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

/-- CHECK-NOT `received: null`: no execution the book allows, under the echo host, logs it.
    [native] (the printed form of the one log entry, `upd2_log`) -/
theorem checkNot : w_elm_PortIncomingRejectTest.HoldsNot "received: null" := inv.sound

end StandardElm.Prog.Inv.PortIncomingRejectTest
