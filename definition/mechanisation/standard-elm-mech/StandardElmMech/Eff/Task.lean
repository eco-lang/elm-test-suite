/-
  A Standard Definition of Elm? Mechanisation: task reduction (effects.tex, sec:effects-tasks, the
  rules r:e-task-*), plan step 4.

  `TaskRed tk a tk'` is the book's tk →[a] tk', `a = none` a silent reduction; `TaskRedL` is its
  logged twin (plan decision D4), whose log is that of the application in r:e-task-andthen-succeed
  and r:e-task-onerror-fail. `focus` and `plug` decompose a task into its frames and its redex;
  `taskRed_iff` shows that a reduction is a reduction of the redex, plugged back, and the book's
  property of task reduction follows (`taskRed_outcome`, `taskRed_kind`, `taskRed_silent_same`,
  `taskRed_none`). `stepTaskL` is the executable step, sound, complete and, where it reads no
  choice of APPLY and spawns nothing, unique.
-/
import StandardElmMech.Determinism

namespace StandardElm.Eff
open StandardElm

/-- An action π(v1 ... vk) → tk (fig:effects-compound): primitive, arguments, outcome. -/
structure Action where
  prim : Prim
  args : List Val
  outcome : Val
  deriving Inhabited

/-- tk ∈ Out(π, v1 ... vk) for the primitives of Process (sec:effects-tasks). The outcome of spawn
    is any process identifier; Chapter 9 chooses a fresh one. -/
inductive Out : Prim → List Val → Val → Prop where
  | sleep (v : Val) : Out .sleep [v] (.succeed .unit)
  | spawn (t : Val) (n : Nat) : Out .spawn [t] (.succeed (.pid n))
  | kill (n : Nat) : Out .kill [.pid n] (.succeed .unit)

/-- tk →[a] tk' (sec:effects-tasks); `none` is a silent reduction. -/
inductive TaskRed : Val → Option Action → Val → Prop where
  /-- r:e-task-andthen-succeed -/
  | r_e_task_andthen_succeed (v v' tk : Val) : AppVal v v' tk → TaskRed (.andThen v (.succeed v')) none tk
  /-- r:e-task-andthen-fail -/
  | r_e_task_andthen_fail (v v' : Val) : TaskRed (.andThen v (.fail v')) none (.fail v')
  /-- r:e-task-onerror-fail -/
  | r_e_task_onerror_fail (v v' tk : Val) : AppVal v v' tk → TaskRed (.onError v (.fail v')) none tk
  /-- r:e-task-onerror-succeed -/
  | r_e_task_onerror_succeed (v v' : Val) : TaskRed (.onError v (.succeed v')) none (.succeed v')
  /-- r:e-task-andthen-inner -/
  | r_e_task_andthen_inner (v tk tk' : Val) (a : Option Action) :
      TaskRed tk a tk' → TaskRed (.andThen v tk) a (.andThen v tk')
  /-- r:e-task-onerror-inner -/
  | r_e_task_onerror_inner (v tk tk' : Val) (a : Option Action) :
      TaskRed tk a tk' → TaskRed (.onError v tk) a (.onError v tk')
  /-- r:e-task-prim -/
  | r_e_task_prim (π : Prim) (vs : List Val) (tk : Val) :
      Out π vs tk → TaskRed (.prim π vs) (some ⟨π, vs, tk⟩) tk

/-- The logged twin of `TaskRed` (D4). -/
inductive TaskRedL : Val → Option Action → Val → Log → Prop where
  /-- r:e-task-andthen-succeed -/
  | r_e_task_andthen_succeed_l (v v' tk : Val) (l : Log) :
      AppValL v v' tk l → TaskRedL (.andThen v (.succeed v')) none tk l
  /-- r:e-task-andthen-fail -/
  | r_e_task_andthen_fail_l (v v' : Val) : TaskRedL (.andThen v (.fail v')) none (.fail v') []
  /-- r:e-task-onerror-fail -/
  | r_e_task_onerror_fail_l (v v' tk : Val) (l : Log) :
      AppValL v v' tk l → TaskRedL (.onError v (.fail v')) none tk l
  /-- r:e-task-onerror-succeed -/
  | r_e_task_onerror_succeed_l (v v' : Val) : TaskRedL (.onError v (.succeed v')) none (.succeed v') []
  /-- r:e-task-andthen-inner -/
  | r_e_task_andthen_inner_l (v tk tk' : Val) (a : Option Action) (l : Log) :
      TaskRedL tk a tk' l → TaskRedL (.andThen v tk) a (.andThen v tk') l
  /-- r:e-task-onerror-inner -/
  | r_e_task_onerror_inner_l (v tk tk' : Val) (a : Option Action) (l : Log) :
      TaskRedL tk a tk' l → TaskRedL (.onError v tk) a (.onError v tk') l
  /-- r:e-task-prim -/
  | r_e_task_prim_l (π : Prim) (vs : List Val) (tk : Val) :
      Out π vs tk → TaskRedL (.prim π vs) (some ⟨π, vs, tk⟩) tk []

theorem TaskRedL.forget : ∀ {tk a tk' l}, TaskRedL tk a tk' l → TaskRed tk a tk'
  | _, _, _, _, .r_e_task_andthen_succeed_l _ _ _ _ h => .r_e_task_andthen_succeed _ _ _ h.forget
  | _, _, _, _, .r_e_task_andthen_fail_l _ _ => .r_e_task_andthen_fail _ _
  | _, _, _, _, .r_e_task_onerror_fail_l _ _ _ _ h => .r_e_task_onerror_fail _ _ _ h.forget
  | _, _, _, _, .r_e_task_onerror_succeed_l _ _ => .r_e_task_onerror_succeed _ _
  | _, _, _, _, .r_e_task_andthen_inner_l _ _ _ _ _ h => .r_e_task_andthen_inner _ _ _ _ h.forget
  | _, _, _, _, .r_e_task_onerror_inner_l _ _ _ _ _ h => .r_e_task_onerror_inner _ _ _ _ h.forget
  | _, _, _, _, .r_e_task_prim_l _ _ _ h => .r_e_task_prim _ _ _ h

theorem TaskRed.lift : ∀ {tk a tk'}, TaskRed tk a tk' → ∃ l, TaskRedL tk a tk' l
  | _, _, _, .r_e_task_andthen_succeed _ _ _ h =>
    let ⟨l, h'⟩ := AppVal.lift h; ⟨l, .r_e_task_andthen_succeed_l _ _ _ _ h'⟩
  | _, _, _, .r_e_task_andthen_fail _ _ => ⟨[], .r_e_task_andthen_fail_l _ _⟩
  | _, _, _, .r_e_task_onerror_fail _ _ _ h =>
    let ⟨l, h'⟩ := AppVal.lift h; ⟨l, .r_e_task_onerror_fail_l _ _ _ _ h'⟩
  | _, _, _, .r_e_task_onerror_succeed _ _ => ⟨[], .r_e_task_onerror_succeed_l _ _⟩
  | _, _, _, .r_e_task_andthen_inner _ _ _ _ h =>
    let ⟨l, h'⟩ := TaskRed.lift h; ⟨l, .r_e_task_andthen_inner_l _ _ _ _ _ h'⟩
  | _, _, _, .r_e_task_onerror_inner _ _ _ _ h =>
    let ⟨l, h'⟩ := TaskRed.lift h; ⟨l, .r_e_task_onerror_inner_l _ _ _ _ _ h'⟩
  | _, _, _, .r_e_task_prim _ _ _ h => ⟨[], .r_e_task_prim_l _ _ _ h⟩

/-! ## The redex of a task -/

/-- A frame of a task: andThen(f, [ ]) or onError(f, [ ]). -/
inductive Frame where
  | andThen (f : Val)
  | onError (f : Val)
  deriving Inhabited

/-- The frames plugged with a task, the innermost frame last: plug [F1, F2] t = F1[F2[t]]. -/
def plug : List Frame → Val → Val
  | [], t => t
  | .andThen f :: fs, t => .andThen f (plug fs t)
  | .onError f :: fs, t => .onError f (plug fs t)

/-- The redex of a task: descend through andThen and onError whose inner task is not an outcome.
    `none` for an outcome and for a value that is not a task. -/
def focus : Val → Option (List Frame × Val)
  | .andThen f t =>
    if t.isOutcome then some ([], .andThen f t)
    else (focus t).map fun (fs, r) => (.andThen f :: fs, r)
  | .onError f t =>
    if t.isOutcome then some ([], .onError f t)
    else (focus t).map fun (fs, r) => (.onError f :: fs, r)
  | .prim π vs => some ([], .prim π vs)
  | _ => none

/-- A reduction of a redex. -/
inductive RedexRed : Val → Option Action → Val → Prop where
  | andThenSucceed (f v t : Val) : AppVal f v t → RedexRed (.andThen f (.succeed v)) none t
  | andThenFail (f v : Val) : RedexRed (.andThen f (.fail v)) none (.fail v)
  | onErrorFail (f v t : Val) : AppVal f v t → RedexRed (.onError f (.fail v)) none t
  | onErrorSucceed (f v : Val) : RedexRed (.onError f (.succeed v)) none (.succeed v)
  | prim (π : Prim) (vs : List Val) (t : Val) : Out π vs t → RedexRed (.prim π vs) (some ⟨π, vs, t⟩) t

/-- An outcome has no reduction. -/
theorem taskRed_outcome {tk : Val} {a : Option Action} {tk' : Val} (h : tk.isOutcome = true) :
    ¬ TaskRed tk a tk' := by
  intro d
  cases d <;> simp [Val.isOutcome] at h

/-- A reduction of the redex, plugged back into the frames, is a reduction of the task. -/
theorem taskRed_of_focus : ∀ (tk : Val) (fs : List Frame) (r r' : Val) (a : Option Action),
    focus tk = some (fs, r) → RedexRed r a r' → TaskRed tk a (plug fs r')
  | .andThen f t, fs, r, r', a, hf, hr => by
    simp only [focus] at hf
    split at hf
    · simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      cases hr with
      | andThenSucceed _ _ _ h => exact .r_e_task_andthen_succeed _ _ _ h
      | andThenFail _ _ => exact .r_e_task_andthen_fail _ _
    · cases hft : focus t with
      | none => simp [hft] at hf
      | some p =>
        obtain ⟨fs', r0⟩ := p
        simp only [hft, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨rfl, rfl⟩ := hf
        exact .r_e_task_andthen_inner _ _ _ _ (taskRed_of_focus t fs' r0 r' a hft hr)
  | .onError f t, fs, r, r', a, hf, hr => by
    simp only [focus] at hf
    split at hf
    · simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      cases hr with
      | onErrorFail _ _ _ h => exact .r_e_task_onerror_fail _ _ _ h
      | onErrorSucceed _ _ => exact .r_e_task_onerror_succeed _ _
    · cases hft : focus t with
      | none => simp [hft] at hf
      | some p =>
        obtain ⟨fs', r0⟩ := p
        simp only [hft, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨rfl, rfl⟩ := hf
        exact .r_e_task_onerror_inner _ _ _ _ (taskRed_of_focus t fs' r0 r' a hft hr)
  | .prim π vs, fs, r, r', a, hf, hr => by
    simp only [focus, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    cases hr with
    | prim _ _ _ h => exact .r_e_task_prim _ _ _ h
  | .unit, _, _, _, _, hf, _ | .sv _, _, _, _, _, hf, _ | .basApp _ _, _, _, _, _, hf, _
  | .con _ _, _, _, _, _, hf, _ | .record _, _, _, _, _, hf, _ | .tuple _ _ _, _, _, _, _, hf, _
  | .closure _ _ _ _, _, _, _, _, hf, _ | .batch _, _, _, _, _, hf, _ | .mapE _ _, _, _, _, _, hf, _
  | .prog _, _, _, _, _, hf, _ | .succeed _, _, _, _, _, hf, _ | .fail _, _, _, _, _, hf, _
  | .pid _, _, _, _, _, hf, _ | .leaf _ _, _, _, _, _, hf, _ | .bv _, _, _, _, _, hf, _ => by
    simp [focus] at hf

/-- A reduction is a reduction of the redex, plugged back into the frames. -/
theorem taskRed_iff {tk : Val} {a : Option Action} {tk' : Val} :
    TaskRed tk a tk' ↔ ∃ fs r r', focus tk = some (fs, r) ∧ RedexRed r a r' ∧ tk' = plug fs r' := by
  constructor
  · intro d
    induction d with
    | r_e_task_andthen_succeed f v t h =>
      exact ⟨[], _, _, by simp [focus, Val.isOutcome], .andThenSucceed f v t h, rfl⟩
    | r_e_task_andthen_fail f v => exact ⟨[], _, _, by simp [focus, Val.isOutcome], .andThenFail f v, rfl⟩
    | r_e_task_onerror_fail f v t h =>
      exact ⟨[], _, _, by simp [focus, Val.isOutcome], .onErrorFail f v t h, rfl⟩
    | r_e_task_onerror_succeed f v =>
      exact ⟨[], _, _, by simp [focus, Val.isOutcome], .onErrorSucceed f v, rfl⟩
    | r_e_task_andthen_inner f t t' a d ih =>
      obtain ⟨fs, r, r', hf, hr, rfl⟩ := ih
      have ho : t.isOutcome = false := by
        cases ht : t.isOutcome
        · rfl
        · exact absurd d (taskRed_outcome ht)
      exact ⟨.andThen f :: fs, r, r', by simp [focus, ho, hf], hr, rfl⟩
    | r_e_task_onerror_inner f t t' a d ih =>
      obtain ⟨fs, r, r', hf, hr, rfl⟩ := ih
      have ho : t.isOutcome = false := by
        cases ht : t.isOutcome
        · rfl
        · exact absurd d (taskRed_outcome ht)
      exact ⟨.onError f :: fs, r, r', by simp [focus, ho, hf], hr, rfl⟩
    | r_e_task_prim π vs t h => exact ⟨[], _, _, by simp [focus], .prim π vs t h, rfl⟩
  · rintro ⟨fs, r, r', hf, hr, rfl⟩
    exact taskRed_of_focus tk fs r r' a hf hr

/-- Two reductions of a task reduce its one redex. -/
theorem taskRed_same_redex {tk : Val} {a1 a2 : Option Action} {t1 t2 : Val}
    (h1 : TaskRed tk a1 t1) (h2 : TaskRed tk a2 t2) :
    ∃ fs r r1 r2, RedexRed r a1 r1 ∧ RedexRed r a2 r2 ∧ t1 = plug fs r1 ∧ t2 = plug fs r2 := by
  obtain ⟨fs1, r1, r1', hf1, hr1, rfl⟩ := taskRed_iff.mp h1
  obtain ⟨fs2, r2, r2', hf2, hr2, rfl⟩ := taskRed_iff.mp h2
  rw [hf1] at hf2
  simp only [Option.some.injEq, Prod.mk.injEq] at hf2
  obtain ⟨rfl, rfl⟩ := hf2
  exact ⟨fs1, r1, r1', r2', hr1, hr2, rfl, rfl⟩

/-- Either every reduction of a task is silent or every one is labelled, by one primitive and one
    argument list (sec:effects-tasks, the property). -/
theorem taskRed_kind {tk : Val} {a1 a2 : Option Action} {t1 t2 : Val}
    (h1 : TaskRed tk a1 t1) (h2 : TaskRed tk a2 t2) :
    (a1 = none ↔ a2 = none) ∧
    ∀ x1 x2, a1 = some x1 → a2 = some x2 → x1.prim = x2.prim ∧ x1.args = x2.args := by
  obtain ⟨fs, r, r1, r2, hr1, hr2, _, _⟩ := taskRed_same_redex h1 h2
  cases hr1 <;> cases hr2 <;> simp

/-- Silent reductions of a task have the same right-hand side, up to the choice of a member of
    APPLY in the application of the redex. -/
theorem taskRed_silent_same {tk t1 t2 : Val} (h1 : TaskRed tk none t1) (h2 : TaskRed tk none t2) :
    t1 = t2 ∨ ∃ fs f v w1 w2, AppVal f v w1 ∧ AppVal f v w2 ∧ t1 = plug fs w1 ∧ t2 = plug fs w2 := by
  obtain ⟨fs, r, r1, r2, hr1, hr2, rfl, rfl⟩ := taskRed_same_redex h1 h2
  cases hr1 with
  | andThenSucceed f v w1 a1 =>
    cases hr2 with
    | andThenSucceed _ _ w2 a2 => exact Or.inr ⟨fs, f, v, r1, r2, a1, a2, rfl, rfl⟩
  | andThenFail => cases hr2; exact Or.inl rfl
  | onErrorFail f v w1 a1 =>
    cases hr2 with
    | onErrorFail _ _ w2 a2 => exact Or.inr ⟨fs, f, v, r1, r2, a1, a2, rfl, rfl⟩
  | onErrorSucceed => cases hr2; exact Or.inl rfl

/-- A well-formed task: every node a task form, every argument of kill a process identifier. -/
inductive WFTask : Val → Prop where
  | succeed (v : Val) : WFTask (.succeed v)
  | fail (v : Val) : WFTask (.fail v)
  | andThen (f t : Val) : WFTask t → WFTask (.andThen f t)
  | onError (f t : Val) : WFTask t → WFTask (.onError f t)
  | sleep (v : Val) : WFTask (.prim .sleep [v])
  | spawn (t : Val) : WFTask (.prim .spawn [t])
  | kill (n : Nat) : WFTask (.prim .kill [.pid n])

/-- A well-formed task that is not an outcome has no reduction only when the application of
    r:e-task-andthen-succeed or r:e-task-onerror-fail at its redex has no result. -/
theorem taskRed_none {tk : Val} (hw : WFTask tk) (ho : tk.isOutcome = false)
    (hn : ∀ a t, ¬ TaskRed tk a t) :
    ∃ fs f v, (focus tk = some (fs, .andThen f (.succeed v)) ∨ focus tk = some (fs, .onError f (.fail v)))
      ∧ ¬ ∃ t, AppVal f v t := by
  induction hw with
  | succeed => simp [Val.isOutcome] at ho
  | fail => simp [Val.isOutcome] at ho
  | andThen f t ht ih =>
    cases hto : t.isOutcome
    · obtain ⟨fs, g, v, hf, hna⟩ := ih hto (fun a t' d => hn a _ (.r_e_task_andthen_inner _ _ _ _ d))
      refine ⟨.andThen f :: fs, g, v, ?_, hna⟩
      rcases hf with hf | hf
      · exact Or.inl (by simp [focus, hto, hf])
      · exact Or.inr (by simp [focus, hto, hf])
    · cases ht with
      | succeed v =>
        refine ⟨[], f, v, Or.inl (by simp [focus, Val.isOutcome]), ?_⟩
        rintro ⟨t', h⟩
        exact hn none t' (.r_e_task_andthen_succeed _ _ _ h)
      | fail v => exact absurd (.r_e_task_andthen_fail f v) (hn none _)
      | _ => simp [Val.isOutcome] at hto
  | onError f t ht ih =>
    cases hto : t.isOutcome
    · obtain ⟨fs, g, v, hf, hna⟩ := ih hto (fun a t' d => hn a _ (.r_e_task_onerror_inner _ _ _ _ d))
      refine ⟨.onError f :: fs, g, v, ?_, hna⟩
      rcases hf with hf | hf
      · exact Or.inl (by simp [focus, hto, hf])
      · exact Or.inr (by simp [focus, hto, hf])
    · cases ht with
      | fail v =>
        refine ⟨[], f, v, Or.inr (by simp [focus, Val.isOutcome]), ?_⟩
        rintro ⟨t', h⟩
        exact hn none t' (.r_e_task_onerror_fail _ _ _ h)
      | succeed v => exact absurd (.r_e_task_onerror_succeed f v) (hn none _)
      | _ => simp [Val.isOutcome] at hto
  | sleep v => exact absurd (.r_e_task_prim _ _ _ (.sleep v)) (hn _ _)
  | spawn t => exact absurd (.r_e_task_prim _ _ _ (.spawn t 0)) (hn _ _)
  | kill n => exact absurd (.r_e_task_prim _ _ _ (.kill n)) (hn _ _)

/-! ## The executable step -/

/-- A result with its value mapped, its log and index kept. -/
def _root_.StandardElm.Res.mapOut {α β : Type} (r : Res α) (f : α → β) : Res β :=
  ⟨match r.out with
    | .value a => .value (f a)
    | .stuck => .stuck
    | .outOfFuel => .outOfFuel, r.log, r.next⟩

/-- One reduction of tk, by the rules' only possible shape at `focus tk`. `fresh` is the process
    identifier a spawn returns. Stuck when tk is an outcome, not a task, a prim whose arguments Out
    does not accept, or when the application has no value; out of fuel when the application runs
    out. -/
def stepTaskL (o : Oracle) (n : Nat) (fresh : Nat) : Val → Nat → Res (Option Action × Val)
  | .andThen f (.succeed v), k => (appVal o n f v k).mapOut fun t => (none, t)
  | .andThen _ (.fail v), k => ⟨.value (none, .fail v), [], k⟩
  | .onError f (.fail v), k => (appVal o n f v k).mapOut fun t => (none, t)
  | .onError _ (.succeed v), k => ⟨.value (none, .succeed v), [], k⟩
  | .andThen f t, k => (stepTaskL o n fresh t k).mapOut fun (a, t') => (a, .andThen f t')
  | .onError f t, k => (stepTaskL o n fresh t k).mapOut fun (a, t') => (a, .onError f t')
  | .prim .sleep [v], k => ⟨.value (some ⟨.sleep, [v], .succeed .unit⟩, .succeed .unit), [], k⟩
  | .prim .spawn [t], k =>
    ⟨.value (some ⟨.spawn, [t], .succeed (.pid fresh)⟩, .succeed (.pid fresh)), [], k⟩
  | .prim .kill [.pid p], k => ⟨.value (some ⟨.kill, [.pid p], .succeed .unit⟩, .succeed .unit), [], k⟩
  | _, k => ⟨.stuck, [], k⟩

theorem mapOut_value {α β : Type} {r : Res α} {f : α → β} {b : β} (h : (r.mapOut f).out = .value b) :
    ∃ a, r.out = .value a ∧ f a = b := by
  rcases r with ⟨out, l, k⟩
  cases out <;> simp [Res.mapOut] at h ⊢
  exact h

theorem appVal_sound_out {o : Oracle} {n : Nat} {f v : Val} {k : Nat} {w : Val}
    (h : (appVal o n f v k).out = .value w) : AppValL f v w (appVal o n f v k).log := by
  rcases hr : appVal o n f v k with ⟨out, l, k'⟩
  rw [hr] at h; simp only at h; subst h
  exact appVal_sound_l hr

/-- Every step of the evaluator is a logged reduction. -/
theorem stepTaskL_sound {o : Oracle} {n fr : Nat} {tk : Val} {k : Nat} {a : Option Action} {tk' : Val}
    (h : (stepTaskL o n fr tk k).out = .value (a, tk')) : TaskRedL tk a tk' (stepTaskL o n fr tk k).log := by
  induction tk, k using stepTaskL.induct generalizing a tk' with
  | case1 f v k =>
    simp only [stepTaskL] at h ⊢
    obtain ⟨t, ht, he⟩ := mapOut_value h
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact .r_e_task_andthen_succeed_l _ _ _ _ (appVal_sound_out ht)
  | case2 f v k =>
    simp only [stepTaskL, Outcome.value.injEq, Prod.mk.injEq] at h ⊢; obtain ⟨rfl, rfl⟩ := h
    exact .r_e_task_andthen_fail_l _ _
  | case3 f v k =>
    simp only [stepTaskL] at h ⊢
    obtain ⟨t, ht, he⟩ := mapOut_value h
    simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    exact .r_e_task_onerror_fail_l _ _ _ _ (appVal_sound_out ht)
  | case4 f v k =>
    simp only [stepTaskL, Outcome.value.injEq, Prod.mk.injEq] at h ⊢; obtain ⟨rfl, rfl⟩ := h
    exact .r_e_task_onerror_succeed_l _ _
  | case5 f t k h1 h2 ih =>
    rw [stepTaskL] at h ⊢
    · obtain ⟨⟨a0, t0⟩, ht, he⟩ := mapOut_value h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      exact .r_e_task_andthen_inner_l _ _ _ _ _ (ih ht)
    all_goals assumption
  | case6 f t k h1 h2 ih =>
    rw [stepTaskL] at h ⊢
    · obtain ⟨⟨a0, t0⟩, ht, he⟩ := mapOut_value h
      simp only [Prod.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      exact .r_e_task_onerror_inner_l _ _ _ _ _ (ih ht)
    all_goals assumption
  | case7 v k =>
    simp only [stepTaskL, Outcome.value.injEq, Prod.mk.injEq] at h ⊢; obtain ⟨rfl, rfl⟩ := h
    exact .r_e_task_prim_l _ _ _ (.sleep v)
  | case8 t k =>
    simp only [stepTaskL, Outcome.value.injEq, Prod.mk.injEq] at h ⊢; obtain ⟨rfl, rfl⟩ := h
    exact .r_e_task_prim_l _ _ _ (.spawn t fr)
  | case9 p k =>
    simp only [stepTaskL, Outcome.value.injEq, Prod.mk.injEq] at h ⊢; obtain ⟨rfl, rfl⟩ := h
    exact .r_e_task_prim_l _ _ _ (.kill p)
  | case10 t k _ _ _ _ _ _ _ _ _ =>
    rw [stepTaskL] at h
    · cases h
    all_goals assumption

/-- A run of an evaluator is complete for a value and log: from some fuel on, every oracle that
    makes the choices L gives them, having read exactly L. -/
def CompleteFor {α : Type} (run : Oracle → Nat → Nat → Res α) (a : α) (l : Log) : Prop :=
  ∃ (L : List Bool) (n : Nat), ∀ o k m, n ≤ m → Agrees o k L → run o m k = ⟨.value a, l, k + L.length⟩

theorem TaskRedL.not_outcome {tk : Val} {a : Option Action} {tk' : Val} {l : Log}
    (d : TaskRedL tk a tk' l) : tk.isOutcome = false := by
  cases h : tk.isOutcome
  · rfl
  · exact absurd d.forget (taskRed_outcome h)

theorem stepTaskL_andThen_inner {o : Oracle} {n fr k : Nat} {f t : Val} (h : t.isOutcome = false) :
    stepTaskL o n fr (.andThen f t) k = (stepTaskL o n fr t k).mapOut fun (a, t') => (a, .andThen f t') := by
  cases t <;> simp_all [stepTaskL, Val.isOutcome]

theorem stepTaskL_onError_inner {o : Oracle} {n fr k : Nat} {f t : Val} (h : t.isOutcome = false) :
    stepTaskL o n fr (.onError f t) k = (stepTaskL o n fr t k).mapOut fun (a, t') => (a, .onError f t') := by
  cases t <;> simp_all [stepTaskL, Val.isOutcome]

/-- Every logged reduction is found by the evaluator, with some choices, fuel and fresh
    identifier (the one the reduction spawns, if it spawns). -/
theorem stepTaskL_complete {tk : Val} {a : Option Action} {tk' : Val} {l : Log}
    (d : TaskRedL tk a tk' l) : ∃ fr, CompleteFor (fun o m k => stepTaskL o m fr tk k) (a, tk') l := by
  induction d with
  | r_e_task_andthen_succeed_l f v t l h =>
    obtain ⟨L, n, c⟩ := AppValL.complete h
    exact ⟨0, L, n, fun o k m hm ha => by simp [stepTaskL, c o k m hm ha, Res.mapOut]⟩
  | r_e_task_andthen_fail_l f v => exact ⟨0, [], 0, fun o k m _ _ => by simp [stepTaskL]⟩
  | r_e_task_onerror_fail_l f v t l h =>
    obtain ⟨L, n, c⟩ := AppValL.complete h
    exact ⟨0, L, n, fun o k m hm ha => by simp [stepTaskL, c o k m hm ha, Res.mapOut]⟩
  | r_e_task_onerror_succeed_l f v => exact ⟨0, [], 0, fun o k m _ _ => by simp [stepTaskL]⟩
  | r_e_task_andthen_inner_l f t t' a l d ih =>
    obtain ⟨fr, L, n, c⟩ := ih
    refine ⟨fr, L, n, fun o k m hm ha => ?_⟩
    have c' := c o k m hm ha
    simp only at c' ⊢
    rw [stepTaskL_andThen_inner d.not_outcome, c']
    rfl
  | r_e_task_onerror_inner_l f t t' a l d ih =>
    obtain ⟨fr, L, n, c⟩ := ih
    refine ⟨fr, L, n, fun o k m hm ha => ?_⟩
    have c' := c o k m hm ha
    simp only at c' ⊢
    rw [stepTaskL_onError_inner d.not_outcome, c']
    rfl
  | r_e_task_prim_l π vs t h =>
    cases h with
    | sleep v => exact ⟨0, [], 0, fun o k m _ _ => by simp [stepTaskL]⟩
    | spawn t n => exact ⟨n, [], 0, fun o k m _ _ => by simp [stepTaskL]⟩
    | kill p => exact ⟨0, [], 0, fun o k m _ _ => by simp [stepTaskL]⟩

/-- When the evaluator reads no choice and the reduction spawns nothing, its step is the only
    one (a spawn's outcome is any identifier, which the rule leaves free). -/
theorem stepTaskL_unique {o : Oracle} {n fr k : Nat} {tk t : Val} {a : Option Action} {l : Log}
    (h : stepTaskL o n fr tk k = ⟨.value (a, t), l, k⟩) (hs : ∀ x, a = some x → x.prim ≠ .spawn) :
    ∀ a' t' l', TaskRedL tk a' t' l' → a' = a ∧ t' = t ∧ l' = l := by
  intro a' t' l' d
  induction d generalizing a t l with
  | r_e_task_andthen_succeed_l f v w l0 hw =>
    simp only [stepTaskL] at h
    rcases hr : appVal o n f v k with ⟨out, l1, k1⟩
    rw [hr] at h
    cases out <;> simp [Res.mapOut] at h
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := h
    obtain ⟨rfl, rfl⟩ := appVal_unique_l hr _ _ hw
    exact ⟨rfl, rfl, rfl⟩
  | r_e_task_andthen_fail_l f v =>
    simp [stepTaskL] at h; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h; exact ⟨rfl, rfl, rfl⟩
  | r_e_task_onerror_fail_l f v w l0 hw =>
    simp only [stepTaskL] at h
    rcases hr : appVal o n f v k with ⟨out, l1, k1⟩
    rw [hr] at h
    cases out <;> simp [Res.mapOut] at h
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := h
    obtain ⟨rfl, rfl⟩ := appVal_unique_l hr _ _ hw
    exact ⟨rfl, rfl, rfl⟩
  | r_e_task_onerror_succeed_l f v =>
    simp [stepTaskL] at h; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h; exact ⟨rfl, rfl, rfl⟩
  | r_e_task_andthen_inner_l f t0 t0' a0 l0 d ih =>
    rw [stepTaskL_andThen_inner d.not_outcome] at h
    rcases hr : stepTaskL o n fr t0 k with ⟨out, l1, k1⟩
    rw [hr] at h
    rcases out with ⟨a1, t1⟩ | _ | _ <;> simp [Res.mapOut] at h
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := h
    obtain ⟨rfl, rfl, rfl⟩ := ih hr hs
    exact ⟨rfl, rfl, rfl⟩
  | r_e_task_onerror_inner_l f t0 t0' a0 l0 d ih =>
    rw [stepTaskL_onError_inner d.not_outcome] at h
    rcases hr : stepTaskL o n fr t0 k with ⟨out, l1, k1⟩
    rw [hr] at h
    rcases out with ⟨a1, t1⟩ | _ | _ <;> simp [Res.mapOut] at h
    obtain ⟨⟨rfl, rfl⟩, rfl, rfl⟩ := h
    obtain ⟨rfl, rfl, rfl⟩ := ih hr hs
    exact ⟨rfl, rfl, rfl⟩
  | r_e_task_prim_l π vs w hout =>
    cases hout with
    | sleep v => simp [stepTaskL] at h; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h; exact ⟨rfl, rfl, rfl⟩
    | spawn t0 m =>
      simp [stepTaskL] at h; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      exact absurd rfl (hs _ rfl)
    | kill p => simp [stepTaskL] at h; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h; exact ⟨rfl, rfl, rfl⟩

end StandardElm.Eff
