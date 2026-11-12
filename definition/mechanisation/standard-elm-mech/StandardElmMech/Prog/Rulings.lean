/-
  A Standard Definition of Elm? Mechanisation: the rulings of Chapter 9 as theorems (A62, A72, A77,
  A79, A80, A81) and an illustration of A66 (the "no other guarantee" of A86), plan step 5.

  The two concrete programs, of A62 and A66, are written in the notation of the generated tests
  (Examples.lean) and evaluated by the evaluator of Chapter 7's rules; their facts are decided by
  the kernel.
-/
import StandardElmMech.Prog.Guarantees
import StandardElmMech.Prog.Worker
import StandardElmMech.Examples

namespace StandardElm.Prog
open StandardElm StandardElm.Eff StandardElm.D

/-! ## A62: an update with no result ends message handling; other steps go on -/

/-- The invariant of an execution in which the head message has no update: the model is K's and
    the queue of messages is B (K's queue, whose head is that message) followed by others. -/
theorem a62_aux {PE : PortEnv} {r : List (String × Val)} {hst : Host} {m fu v1 : Val}
    {B : List Val} (hB : ∃ M, B = v1 :: M) (hfu : field r "update" = some fu)
    (hno : ¬ ∃ v2 w, AppVal fu v1 v2 ∧ AppVal v2 m w) :
    ∀ {K hs π hs'}, Exec PE r hst K hs π hs' → K.model = m → (∃ ms, K.msgs = B ++ ms) →
      ∀ K' ∈ π.map (·.2), K'.model = m ∧ ∃ ms, K'.msgs = B ++ ms := by
  intro K hs π hs' h
  induction h with
  | nil => intro _ _ K' hK'; simp at hK'
  | cons K hs a K1 hs1 π hs'' hst1 _ _ ih =>
    intro hm hq
    have h1 : K1.model = m ∧ ∃ ms, K1.msgs = B ++ ms := by
      rcases a86_step hst1 with ⟨hm1, ms1, hq1⟩ | ⟨_, v1', fu', v2, cm, cs, L, hq1, hf, ha1, ha2, -⟩
      · obtain ⟨ms, hms⟩ := hq
        exact ⟨hm1.trans hm, ms ++ ms1, by rw [hq1, hms, List.append_assoc]⟩
      · exfalso
        obtain ⟨ms, hms⟩ := hq
        obtain ⟨M, rfl⟩ := hB
        rw [hms] at hq1
        simp only [List.cons_append, List.cons.injEq] at hq1
        obtain ⟨h11, -⟩ := hq1
        subst h11
        have hff : fu' = fu := by rw [hf] at hfu; exact Option.some.inj hfu
        subst hff
        rw [hm] at ha2
        exact hno ⟨v2, _, ha1, ha2⟩
    intro K' hK'
    simp only [List.map_cons, List.mem_cons] at hK'
    rcases hK' with rfl | hK'
    · exact h1
    · exact ih h1.1 h1.2 K' hK'

/-- A62: while the head message has no update, no step changes the model, and every queue of
    messages begins with the queue at the start. -/
theorem a62_no_update {PE : PortEnv} {r : List (String × Val)} {hst : Host} {K : Config}
    {hs : List BVal} {π : Path} {hs' : List BVal} {v1 fu : Val} {M : List Val}
    (hK : K.msgs = v1 :: M) (hfu : field r "update" = some fu)
    (hno : ¬ ∃ v2 w, AppVal fu v1 v2 ∧ AppVal v2 K.model w) (h : Exec PE r hst K hs π hs') :
    ∀ K' ∈ π.map (·.2), K'.model = K.model ∧ ∃ ms, K'.msgs = K.msgs ++ ms :=
  a62_aux ⟨M, hK⟩ hfu hno h rfl ⟨[], by simp⟩

/-- A62: other steps go on; time can always pass. -/
theorem a62_wait_continues (PE : PortEnv) (r : List (String × Val)) :
    ∀ K, ∃ K', Step PE r K (some (.wait 1)) K' := by
  rintro ⟨s, v, M, P, sb, Q, H⟩
  exact ⟨_, .r_p_wait s v M P sb Q H 1 (by decide)⟩

/-- The program of A62: `update _ _ = Debug.todo "stop"`. -/
def a62Prog : Program := {
  name := "A62", source := "rulings",
  imports := [⟨"Platform", "Platform", none⟩],
  defs := [
    .fn "main" [] (ap (qv "Platform" "worker") [recE [
      ("init", lams [pw] (tup2 (.atexp .unit) (qv "Cmd" "none"))),
      ("update", lams [pw, pw] (ap (qv "Debug" "todo") [str "stop"])),
      ("subscriptions", lams [pw] (qv "Sub" "none"))]]) ],
  checks := [] }

/-- The record of A62's program value. -/
def a62r : List (String × Val) :=
  match Mod.evProgram (.const false) workerFuel (Mod.Btest []) a62Prog.modules 0 with
  | ⟨.value (.prog r), _, _⟩ => r
  | _ => []

def a62Update : Val := (field a62r "update").getD .unit
def a62Msg : Con := ⟨"Stop", 0⟩

/-- The evaluator's verdict: the first application gives a value without reading a choice, and
    the second is stuck without reading one. -/
def a62B : Bool :=
  match appVal (.const false) workerFuel a62Update (.con a62Msg []) 0 with
  | ⟨.value v2, _, k⟩ =>
    k == 0 && (match appVal (.const false) workerFuel v2 .unit 0 with
      | ⟨.stuck, _, k'⟩ => k' == 0
      | _ => false)
  | _ => false

theorem a62B_true : a62B = true := by decide +kernel

/-- A62, a concrete program: its update has no result, so no update step exists. -/
theorem a62_example : ¬ ∃ v2 w, AppVal a62Update (.con a62Msg []) v2 ∧ AppVal v2 .unit w := by
  have h := a62B_true
  unfold a62B at h
  split at h
  · rename_i v2 l k h1
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    split at h
    · rename_i l' k' h2
      simp only [beq_iff_eq] at h
      subst h
      rintro ⟨v2', w, ha1, ha2⟩
      obtain ⟨l1, ha1'⟩ := AppVal.lift ha1
      obtain ⟨rfl, -⟩ := appVal_unique_l h1 v2' l1 ha1'
      exact appVal_noValue_of_stuck h2 ⟨w, ha2⟩
    · cases h
  · cases h

/-! ## A77 and A72: flags -/

/-- A77: unit flags accept every boundary value. -/
theorem a77_flags_unit (j : BVal) : FlagsVal .unit j .unit := .inl ⟨rfl, rfl⟩

/-- A77: a port of the unit type accepts only null. -/
theorem a77_port_unit (j : BVal) (v : Val) : Eff.Dec .unit j v ↔ j = .null ∧ v = .unit := by
  rw [dec_iff]
  cases j <;> simp [dec] <;> exact eq_comm

theorem flagsVal_unit {j : BVal} {v : Val} : FlagsVal .unit j v ↔ v = .unit := by
  constructor
  · rintro (⟨-, rfl⟩ | ⟨h, -⟩)
    · rfl
    · exact absurd rfl h
  · rintro rfl; exact .inl ⟨rfl, rfl⟩

/-- A77: with unit flags, the start does not depend on the flags. -/
theorem a77_start_any_flags (PE : PortEnv) (j j' : BVal) (r : List (String × Val)) (K : Config) :
    Start PE .unit j r K ↔ Start PE .unit j' r K := by
  constructor <;>
  · intro h
    cases h with
    | r_p_init fi fs v1 v cm cs L P Q H sb h1 h2 h3 h4 h5 h6 h7 h8 =>
      exact .r_p_init _ _ _ _ fi fs v1 v cm cs L P Q H sb h1 h2
        (flagsVal_unit.mpr (flagsVal_unit.mp h3)) h4 h5 h6 h7 h8

/-- A72: absent flags are null; with Maybe flags the program starts with Nothing. -/
theorem a72_maybe_null (τ : PTy) : FlagsVal (.maybe τ) .null (.con conNothing []) :=
  .inr ⟨by simp, (dec_iff _ _ _).mpr (by simp [dec])⟩

/-! ## A79: a failing process ends, whatever its origin, and nothing else happens -/

theorem a79_fail_ends (PE : PortEnv) (r : List (String × Val)) {K : Config} {n : Nat} {v : Val}
    {s' : Time} {o : Option Val} (hp : K.procs.get n = some (.live ⟨.fail v, s', o⟩)) :
    Step PE r K none { K with procs := K.procs.set n .ended } := by
  obtain ⟨s, m, M, P, sb, Q, H⟩ := K
  exact .r_p_proc_end s m M P sb Q H n _ s' o hp (.inl ⟨v, rfl⟩)

theorem a79_spawned_succeed_ends (PE : PortEnv) (r : List (String × Val)) {K : Config} {n : Nat}
    {v : Val} {s' : Time} (hp : K.procs.get n = some (.live ⟨.succeed v, s', none⟩)) :
    Step PE r K none { K with procs := K.procs.set n .ended } := by
  obtain ⟨s, m, M, P, sb, Q, H⟩ := K
  exact .r_p_proc_end s m M P sb Q H n _ s' none hp (.inr ⟨v, rfl, rfl⟩)

theorem natLookup_some_mem {β : Type} : ∀ (f : List (Nat × β)) (n : Nat) (e : β),
    natLookup f n = some e → n ∈ f.map (·.1)
  | [], _, _, h => by simp [natLookup] at h
  | (k, x) :: rest, n, e, h => by
    simp only [natLookup] at h
    split at h
    · rename_i hk; simp at hk; simp [hk]
    · exact List.mem_cons_of_mem _ (natLookup_some_mem rest n e h)

/-- Dispatch only adds processes with fresh identifiers: an existing entry is kept. -/
theorem dispatch_preserves_existing {s : Time} {P : Procs} {Q : OutQ} {H : Pending} {L : List Val}
    {P' : Procs} {Q' : OutQ} {H' : Pending} (h : Dispatch s P Q H L P' Q' H') {n : Nat}
    {e : PEntry} (hn : P.get n = some e) : P'.get n = some e := by
  induction h with
  | r_p_disp_empty => exact hn
  | r_p_disp_task P _ _ _ _ n' _ _ _ _ _ hf _ ih =>
    apply ih
    have hne : n ≠ n' := fun he => hf (he ▸ natLookup_some_mem P n e hn)
    simp only [Procs.get, Procs.set] at hn ⊢
    rw [natLookup_natSet_other _ _ _ _ hne]; exact hn
  | r_p_disp_out _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih hn
  | r_p_disp_plat _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact ih hn

/-- A79: when a process without origin ends, nothing else happens in that step. -/
theorem a79_nothing_else {PE : PortEnv} {r : List (String × Val)} {K K' : Config} {a : Option Event}
    {n : Nat} {t : Val} {s' : Time} (h : Step PE r K a K')
    (h1 : K.procs.get n = some (.live ⟨t, s', none⟩)) (h2 : K'.procs.get n = some .ended) :
    K'.msgs = K.msgs ∧ K'.model = K.model := by
  have hset : ∀ (P : Procs) (n' : Nat) (e : PEntry), n ≠ n' → (P.set n' e).get n = P.get n :=
    fun P n' e hne => natLookup_natSet_other P n' n e hne
  cases h with
  | r_p_update s v v1 M P sb Q H fu fs v2 v' cm cs L P' Q' H' sb' _ _ _ _ _ _ h7 _ =>
    have := dispatch_preserves_existing h7 h1
    simp_all
  | r_p_proc_message _ _ _ P _ _ _ n' _ _ _ _ hp _ =>
    exfalso
    by_cases hne : n = n'
    · subst hne; simp_all
    · simp only at h2; rw [hset P n' _ hne] at h2; simp_all
  | r_p_in_accept => simp_all
  | r_p_platform _ _ _ hp => cases hp
  | _ => simp

/-! ## A80: killing an ended process changes nothing but the killer's own entry -/

theorem a80_kill_ended {PE : PortEnv} {r : List (String × Val)} {K K' : Config} {n' : Nat} {t : Val}
    (h : Step PE r K (some (.act ⟨.kill, [.pid n'], t⟩)) K') (hk : K.procs.get n' = some .ended) :
    ∃ n, ∀ q, q ≠ n → K'.procs.get q = K.procs.get q := by
  generalize hl : some (Event.act ⟨.kill, [.pid n'], t⟩) = lbl at h
  cases h with
  | r_p_proc_step _ _ _ _ _ _ _ _ _ _ _ a _ _ _ h3 =>
    cases a with
    | none => simp at hl
    | some x => exact absurd (h3 x rfl) (by simp [platPrims])
  | r_p_proc_kill _ _ _ P _ _ _ n _ _ _ _ n'' _ _ _ =>
    simp only [Option.some.injEq, Event.act.injEq, Action.mk.injEq, List.cons.injEq, Val.pid.injEq] at hl
    obtain ⟨-, ⟨rfl, -⟩, -⟩ := hl
    refine ⟨n, fun q hq => ?_⟩
    simp only [Procs.get, Procs.set] at hk ⊢
    rw [natLookup_natSet_other _ _ _ _ hq]
    by_cases hq' : q = n'
    · subst hq'; rw [natLookup_natSet_self]; exact hk.symm
    · exact natLookup_natSet_other _ _ _ _ hq'
  | r_p_platform _ _ _ hp => cases hp
  | _ => simp at hl

/-! ## A81: sleep -/

/-- A81: the sleep action is no sooner than max(0, d) after the process reached the sleep. -/
theorem a81_lower {PE : PortEnv} {r : List (String × Val)} {K K' : Config} {x : Float} {t : Val}
    {q : Rat} (h : Step PE r K (some (.act ⟨.sleep, [.sv (.float x)], t⟩)) K')
    (hq : floatToRat? x = some q) :
    ∃ n tk s' o, K.procs.get n = some (.live ⟨tk, s', o⟩) ∧ s' + (if q < 0 then 0 else q) ≤ K.time := by
  generalize hl : some (Event.act ⟨.sleep, [.sv (.float x)], t⟩) = lbl at h
  cases h with
  | r_p_proc_step _ _ _ _ _ _ _ _ _ _ _ a _ _ _ h3 =>
    cases a with
    | none => simp at hl
    | some y => exact absurd (h3 y rfl) (by simp [platPrims])
  | r_p_proc_sleep s _ _ _ _ _ _ n tk s' o _ v' _ hp _ hs =>
    simp only [Option.some.injEq, Event.act.injEq, Action.mk.injEq, List.cons.injEq] at hl
    obtain ⟨-, ⟨rfl, -⟩, -⟩ := hl
    exact ⟨n, tk, s', o, hp, hs x q rfl hq⟩
  | r_p_platform _ _ _ hp => cases hp
  | _ => simp at hl

/-- A81: no upper bound: whenever the sleep is due by some later time, it can happen then. -/
theorem a81_any_later (PE : PortEnv) (r : List (String × Val)) {K : Config} {n : Nat} {tk tk' t : Val}
    {s' : Time} {o : Option Val} {x : Float} {q : Rat}
    (hp : K.procs.get n = some (.live ⟨tk, s', o⟩))
    (hr : TaskRed tk (some ⟨.sleep, [.sv (.float x)], t⟩) tk') (hq : floatToRat? x = some q)
    (d : Rat) (hd : 0 < d) (hge : s' + (if q < 0 then 0 else q) ≤ K.time + d) :
    ∃ K1 K2, Step PE r K (some (.wait d)) K1 ∧ Step PE r K1 (some (.act ⟨.sleep, [.sv (.float x)], t⟩)) K2 := by
  obtain ⟨s, m, M, P, sb, Q, H⟩ := K
  refine ⟨_, _, .r_p_wait s m M P sb Q H d hd, .r_p_proc_sleep _ _ _ _ _ _ _ n tk s' o tk' _ t hp hr ?_⟩
  intro x' q' he hq'
  simp only [Val.sv.injEq, SVal.float.injEq] at he
  subst he
  rw [hq] at hq'; cases hq'
  exact hge

/-- A81: no condition for a non-finite delay. -/
theorem a81_nonfinite (PE : PortEnv) (r : List (String × Val)) {K : Config} {n : Nat} {tk tk' t : Val}
    {s' : Time} {o : Option Val} {x : Float}
    (hp : K.procs.get n = some (.live ⟨tk, s', o⟩))
    (hr : TaskRed tk (some ⟨.sleep, [.sv (.float x)], t⟩) tk') (hq : floatToRat? x = none) :
    ∃ K', Step PE r K (some (.act ⟨.sleep, [.sv (.float x)], t⟩)) K' := by
  obtain ⟨s, m, M, P, sb, Q, H⟩ := K
  refine ⟨_, .r_p_proc_sleep _ _ _ _ _ _ _ n tk s' o tk' _ t hp hr ?_⟩
  intro x' q' he hq'
  simp only [Val.sv.injEq, SVal.float.injEq] at he
  subst he
  rw [hq] at hq'; cases hq'

/-! ## A66: the order of a batch's leaves is open (the "no other guarantee" of A86) -/

/-- The program of A66: `port out : Int -> Cmd msg`, and an update that returns
    `Cmd.batch [out 1, out 2]`. -/
def a66Prog : Program := {
  name := "A66", source := "rulings",
  imports := [⟨"Platform", "Platform", none⟩],
  ports := [("out", .out, .int)],
  defs := [
    .fn "main" [] (ap (qv "Platform" "worker") [recE [
      ("init", lams [pw] (tup2 (.atexp .unit) (qv "Cmd" "none"))),
      ("update", lams [pw, pw] (tup2 (.atexp .unit)
        (ap (qv "Cmd" "batch") [listE [ap (v "out") [i 1], ap (v "out") [i 2]]]))),
      ("subscriptions", lams [pw] (qv "Sub" "none"))]]) ],
  checks := [] }

def a66PE : PortEnv := portEnv a66Prog.modules

def a66r : List (String × Val) :=
  match Mod.evProgram (.const false) workerFuel (Mod.Btest []) a66Prog.modules 0 with
  | ⟨.value (.prog r), _, _⟩ => r
  | _ => []

/-- A configuration with one message waiting and the queue of `out` empty. -/
def a66K0 : Config := ⟨0, .unit, [.unit], [], .unit, qInit a66PE, []⟩

def a66Ctx (lo : LeafOrder) : Ctx := ⟨a66PE, a66r, .none, { leafOrder := lo }, workerFuel⟩
def a66St0 : SchedState := ⟨a66K0, [], [], [], .const false, 0, 0⟩
def a66Run (lo : LeafOrder) : RunResult := run (a66Ctx lo) 20 a66St0 []

theorem a66_listed : outsOn "out" (a66Run .listed).path.forgetLog = [.num 1, .num 2] := by
  decide +kernel

theorem a66_reversed : outsOn "out" (a66Run .reversed).path.forgetLog = [.num 2, .num 1] := by
  decide +kernel

/-- A66: the program has executions delivering 1 then 2, and 2 then 1. -/
theorem a66_batch_order_open :
    (∃ π hs, ExecL a66PE a66r .none a66K0 [] π hs ∧ outsOn "out" π.forgetLog = [.num 1, .num 2]) ∧
    (∃ π hs, ExecL a66PE a66r .none a66K0 [] π hs ∧ outsOn "out" π.forgetLog = [.num 2, .num 1]) :=
  ⟨⟨_, _, run_sound (a66Ctx .listed) a66K0 [] 20 a66St0 [] (.nil _ _) rfl, a66_listed⟩,
   ⟨_, _, run_sound (a66Ctx .reversed) a66K0 [] 20 a66St0 [] (.nil _ _) rfl, a66_reversed⟩⟩

end StandardElm.Prog
