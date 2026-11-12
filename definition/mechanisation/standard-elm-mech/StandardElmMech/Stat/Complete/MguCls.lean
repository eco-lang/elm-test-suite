/-
  A Standard Definition of Elm? Mechanisation: classes for the most general unifier, milestone (c)
  of plan step 11 (section 3: meets, class propagation, requirements; lemmas K4, K5, K11).

  On functional substitutions (FSubst.lean): `RespC s` (s respects classes: every variable is
  mapped to an admissible type of its class). Proved here:

  * K4 (`admC_meet`, `admC_of_meet`, `admC_meet_none`): a type is in `Adm κ` and `Adm κ'` iff the
    meet of the classes exists and the type is in `Adm (κ ⊓ κ')`;
  * K5 (`admC_con_iff`, `admC_fn_iff`, `admC_record_iff`, `admC_var_iff`): admissibility of a
    constructed type is the propagation table `clsD` (D(κ, t)) on its arguments; functions and
    records are admissible only for `any`; a variable for the classes above its own;
  * requirements (`reqC`, `reqC_spec`, `reqC_none`): `S τ ∈ Adm κ` iff `S β ∈ Adm κ'` for every
    requirement `(β, κ')` of `τ`, and no `S τ` is admissible when the requirements fail;
  * K11 (`admC_sb`, `respC_comp`): admissibility is stable under substitutions respecting classes,
    and class respect composes.

  (The table `clsD` is milestone (a)'s `Cls.prop` of Classes.lean, restated here because that
  file's module cannot be imported together with FSubst.lean.)
-/
import StandardElmMech.Stat.Complete.Mgu

namespace StandardElm.Stat.Complete
open StandardElm.Stat

/-- `s` respects classes. -/
def RespC (s : FSub) : Prop := ∀ a, Adm a.cls (s a)

/-! ## K5 -/

theorem admC_var_iff {k : Cls} {a : TyVar} : Adm k (.var a) ↔ a.cls.le k = true := by
  constructor
  · intro h
    cases h with
    | any => cases a.cls <;> rfl
    | num_var _ h => rw [h]; rfl
    | comp_var _ h => exact h
    | app_var _ h => exact h
    | capp_var _ h => rw [h]; rfl
  · intro h
    cases k with
    | any => exact .any _
    | num => exact .num_var a (by revert h; cases a.cls <;> simp [Cls.le])
    | comp => exact .comp_var a h
    | app => exact .app_var a h
    | capp => exact .capp_var a (by revert h; cases a.cls <;> simp [Cls.le])

theorem Cls.le_refl' (k : Cls) : k.le k = true := by cases k <;> rfl

theorem admC_self (a : TyVar) : Adm a.cls (.var a) := admC_var_iff.mpr (Cls.le_refl' _)

theorem respC_id : RespC idS := fun a => admC_self a

/-- D(κ, t) of section 3 (κ ≠ any). -/
def clsD (k : Cls) (t : TyName) : Option (List Cls) :=
  match k with
  | .any => none
  | .num => if t = tInt ∨ t = tFloat then some [] else none
  | .comp =>
    if t = tInt ∨ t = tFloat ∨ t = tChar ∨ t = tString then some []
    else if t = tList then some [.comp]
    else if t = tTuple2 then some [.comp, .comp]
    else if t = tTuple3 then some [.comp, .comp, .comp]
    else none
  | .app => if t = tString then some [] else if t = tList then some [.any] else none
  | .capp => if t = tString then some [] else if t = tList then some [.comp] else none

/-- The arguments' classes, pairwise. -/
def ZipAdmC : List Ty → List Cls → Prop
  | [], [] => True
  | x :: xs, k :: ks => Adm k x ∧ ZipAdmC xs ks
  | _, _ => False

theorem admC_con_iff {k : Cls} {as : List Ty} {t : TyName} (hk : k ≠ .any) :
    Adm k (.con as t) ↔ ∃ ks, clsD k t = some ks ∧ ZipAdmC as ks := by
  constructor
  · intro h
    cases h with
    | any => exact absurd rfl hk
    | num_int => exact ⟨[], by decide, trivial⟩
    | num_float => exact ⟨[], by decide, trivial⟩
    | comp_int => exact ⟨[], by decide, trivial⟩
    | comp_float => exact ⟨[], by decide, trivial⟩
    | comp_char => exact ⟨[], by decide, trivial⟩
    | comp_string => exact ⟨[], by decide, trivial⟩
    | comp_list τ h => exact ⟨[.comp], by decide, h, trivial⟩
    | comp_tuple2 τ1 τ2 h1 h2 => exact ⟨[.comp, .comp], by decide, h1, h2, trivial⟩
    | comp_tuple3 τ1 τ2 τ3 h1 h2 h3 => exact ⟨[.comp, .comp, .comp], by decide, h1, h2, h3, trivial⟩
    | app_string => exact ⟨[], by decide, trivial⟩
    | app_list τ => exact ⟨[.any], by decide, .any τ, trivial⟩
    | capp_string => exact ⟨[], by decide, trivial⟩
    | capp_list τ h => exact ⟨[.comp], by decide, h, trivial⟩
  · rintro ⟨ks, hd, hz⟩
    cases k with
    | any => exact absurd rfl hk
    | num =>
      simp only [clsD] at hd
      split at hd
      · rename_i ht; cases hd
        cases as with
        | nil => rcases ht with rfl | rfl; exact .num_int; exact .num_float
        | cons _ _ => exact hz.elim
      · cases hd
    | comp =>
      simp only [clsD] at hd
      split at hd
      · rename_i ht; cases hd
        cases as with
        | nil =>
          rcases ht with rfl | rfl | rfl | rfl
          · exact .comp_int
          · exact .comp_float
          · exact .comp_char
          · exact .comp_string
        | cons _ _ => exact hz.elim
      · split at hd
        · rename_i ht; subst ht; cases hd
          match as, hz with
          | [x], ⟨h1, _⟩ => exact .comp_list x h1
        · split at hd
          · rename_i ht; subst ht; cases hd
            match as, hz with
            | [x, y], ⟨h1, h2, _⟩ => exact .comp_tuple2 x y h1 h2
          · split at hd
            · rename_i ht; subst ht; cases hd
              match as, hz with
              | [x, y, z], ⟨h1, h2, h3, _⟩ => exact .comp_tuple3 x y z h1 h2 h3
            · cases hd
    | app =>
      simp only [clsD] at hd
      split at hd
      · rename_i ht; subst ht; cases hd
        match as, hz with
        | [], _ => exact .app_string
      · split at hd
        · rename_i ht; subst ht; cases hd
          match as, hz with
          | [x], _ => exact .app_list x
        · cases hd
    | capp =>
      simp only [clsD] at hd
      split at hd
      · rename_i ht; subst ht; cases hd
        match as, hz with
        | [], _ => exact .capp_string
      · split at hd
        · rename_i ht; subst ht; cases hd
          match as, hz with
          | [x], ⟨h1, _⟩ => exact .capp_list x h1
        · cases hd

theorem admC_fn_iff {k : Cls} {a b : Ty} : Adm k (.fn a b) ↔ k = .any :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ .any _⟩

theorem admC_record_iff {k : Cls} {ρ : Row} {tl : Option RowVar} : Adm k (.record ρ tl) ↔ k = .any :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ .any _⟩

/-! ## K4 -/

theorem Cls.meet_any_left (k : Cls) : Cls.meet .any k = some k := by cases k <;> rfl
theorem Cls.meet_any_right (k : Cls) : Cls.meet k .any = some k := by cases k <;> rfl

/-- K4, forward: a type in two classes is in their meet. -/
theorem admC_meet {k k' : Cls} {τ : Ty} (h : Adm k τ) (h' : Adm k' τ) :
    ∃ m, Cls.meet k k' = some m ∧ Adm m τ := by
  by_cases hk : k = .any
  · subst hk; exact ⟨k', Cls.meet_any_left k', h'⟩
  by_cases hk' : k' = .any
  · subst hk'; exact ⟨k, Cls.meet_any_right k, h⟩
  cases τ with
  | var a =>
    have h1 := admC_var_iff.mp h
    have h2 := admC_var_iff.mp h'
    cases hm : Cls.meet k k' with
    | none => exact absurd ⟨h1, h2⟩ ((Cls.meet_none k k').mp hm a.cls)
    | some m => exact ⟨m, rfl, admC_var_iff.mpr (((Cls.meet_spec k k' m).mp hm).2.2 _ h1 h2)⟩
  | _ =>
    have h0 := h
    have h0' := h'
    cases h <;> cases h' <;>
      first
      | exact absurd rfl hk
      | exact absurd rfl hk'
      | exact ⟨_, rfl, h0⟩
      | exact ⟨_, rfl, h0'⟩
      | exact ⟨_, rfl, by constructor <;> assumption⟩
      | exact ⟨_, rfl, by constructor⟩

/-- K4, backward. -/
theorem admC_of_meet {k k' m : Cls} {τ : Ty} (hm : Cls.meet k k' = some m) (h : Adm m τ) :
    Adm k τ ∧ Adm k' τ := by
  obtain ⟨h1, h2, _⟩ := (Cls.meet_spec k k' m).mp hm
  exact ⟨adm_mono h1 h, adm_mono h2 h⟩

theorem admC_meet_none {k k' : Cls} {τ : Ty} (hm : Cls.meet k k' = none) (h : Adm k τ) (h' : Adm k' τ) :
    False := by
  obtain ⟨m, e, _⟩ := admC_meet h h'
  rw [hm] at e; cases e

/-! ## Requirements (section 3) -/

mutual
/-- The requirements of `τ` for class `k`: the variables of `τ` with the classes they must have
    for an image of `τ` to be in `Adm k`; `none` when no image is. -/
def reqC : Cls → Ty → Option (List (TyVar × Cls))
  | .any, _ => some []
  | k, .var a => some [(a, k)]
  | k, .con as t =>
    match clsD k t with
    | some ks => reqL ks as
    | none => none
  | _, .fn _ _ => none
  | _, .record _ _ => none
def reqL : List Cls → List Ty → Option (List (TyVar × Cls))
  | [], [] => some []
  | k :: ks, τ :: ts =>
    match reqC k τ, reqL ks ts with
    | some a, some b => some (a ++ b)
    | _, _ => none
  | _, _ => none
end

theorem clsD_any (t : TyName) : clsD .any t = none := rfl

mutual
theorem reqC_spec (s : FSub) : ∀ (k : Cls) (τ : Ty) (ps : List (TyVar × Cls)), reqC k τ = some ps →
    (Adm k (sb s τ) ↔ ∀ p ∈ ps, Adm p.2 (s p.1))
  | .any, τ, ps, h => by
    simp only [reqC, Option.some.injEq] at h; subst h
    exact ⟨fun _ _ hp => absurd hp List.not_mem_nil, fun _ => Adm.any _⟩
  | .num, .var a, ps, h | .comp, .var a, ps, h | .app, .var a, ps, h | .capp, .var a, ps, h => by
    simp only [reqC, Option.some.injEq] at h; subst h
    simp [sb]
  | .num, .fn _ _, _, h | .comp, .fn _ _, _, h | .app, .fn _ _, _, h | .capp, .fn _ _, _, h => by
    simp [reqC] at h
  | .num, .record _ _, _, h | .comp, .record _ _, _, h | .app, .record _ _, _, h
  | .capp, .record _ _, _, h => by simp [reqC] at h
  | .num, .con as t, ps, h | .comp, .con as t, ps, h | .app, .con as t, ps, h
  | .capp, .con as t, ps, h => by
    simp only [reqC] at h
    split at h
    · rename_i ks hks
      simp only [sb]
      rw [admC_con_iff (by decide)]
      constructor
      · rintro ⟨ks', hks', hz⟩
        rw [hks] at hks'; cases hks'
        exact (reqL_spec s ks as ps h).mp hz
      · intro hp
        exact ⟨ks, hks, (reqL_spec s ks as ps h).mpr hp⟩
    · cases h
theorem reqL_spec (s : FSub) : ∀ (ks : List Cls) (as : List Ty) (ps : List (TyVar × Cls)), reqL ks as = some ps →
    (ZipAdmC (sbList s as) ks ↔ ∀ p ∈ ps, Adm p.2 (s p.1))
  | [], [], ps, h => by
    simp only [reqL, Option.some.injEq] at h; subst h
    simp [sbList, ZipAdmC]
  | k :: ks, τ :: ts, ps, h => by
    simp only [reqL] at h
    split at h
    · rename_i a b ha hb
      simp only [Option.some.injEq] at h; subst h
      simp only [sbList, ZipAdmC, List.mem_append]
      rw [reqC_spec s k τ a ha, reqL_spec s ks ts b hb]
      exact ⟨fun ⟨h1, h2⟩ p hp => hp.elim (h1 p) (h2 p), fun h => ⟨fun p hp => h p (.inl hp), fun p hp => h p (.inr hp)⟩⟩
    · cases h
  | [], _ :: _, _, h => by simp [reqL] at h
  | _ :: _, [], _, h => by simp [reqL] at h
end

theorem zipAdmC_length : ∀ {as : List Ty} {ks : List Cls}, ZipAdmC as ks → as.length = ks.length
  | [], [], _ => rfl
  | _ :: as, _ :: ks, ⟨_, h⟩ => by simp [zipAdmC_length h]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

mutual
theorem reqC_none (s : FSub) : ∀ (k : Cls) (τ : Ty), reqC k τ = none → ¬ Adm k (sb s τ)
  | .any, _, h => by simp [reqC] at h
  | .num, .var _, h | .comp, .var _, h | .app, .var _, h | .capp, .var _, h => by simp [reqC] at h
  | .num, .fn _ _, _ | .comp, .fn _ _, _ | .app, .fn _ _, _ | .capp, .fn _ _, _ => by
    simp only [sb, admC_fn_iff]; decide
  | .num, .record _ _, _ | .comp, .record _ _, _ | .app, .record _ _, _ | .capp, .record _ _, _ => by
    simp only [sb, admC_record_iff]; decide
  | .num, .con as t, h | .comp, .con as t, h | .app, .con as t, h | .capp, .con as t, h => by
    simp only [reqC] at h
    simp only [sb]
    rw [admC_con_iff (by decide)]
    rintro ⟨ks, hks, hz⟩
    rw [hks] at h
    exact reqL_none s ks as h hz
theorem reqL_none (s : FSub) : ∀ (ks : List Cls) (as : List Ty), reqL ks as = none → ¬ ZipAdmC (sbList s as) ks
  | [], [], h => by simp [reqL] at h
  | k :: ks, τ :: ts, h => by
    simp only [sbList, ZipAdmC]
    rintro ⟨h1, h2⟩
    simp only [reqL] at h
    cases ha : reqC k τ with
    | none => exact reqC_none s k τ ha h1
    | some a =>
      cases hb : reqL ks ts with
      | none => exact reqL_none s ks ts hb h2
      | some b => rw [ha, hb] at h; cases h
  | [], _ :: _, _ => by simp [sbList, ZipAdmC]
  | _ :: _, [], _ => by simp [sbList, ZipAdmC]
end

mutual
theorem reqC_vars : ∀ (k : Cls) (τ : Ty) (ps : List (TyVar × Cls)), reqC k τ = some ps →
    ∀ p ∈ ps, BVar.ty p.1 ∈ τ.vars
  | .any, _, ps, h => by simp only [reqC, Option.some.injEq] at h; subst h; intro _ h; cases h
  | .num, .var a, ps, h | .comp, .var a, ps, h | .app, .var a, ps, h | .capp, .var a, ps, h => by
    simp only [reqC, Option.some.injEq] at h; subst h; intro p hp
    simp at hp; subst hp; simp [Ty.vars]
  | .num, .fn _ _, _, h | .comp, .fn _ _, _, h | .app, .fn _ _, _, h | .capp, .fn _ _, _, h => by
    simp [reqC] at h
  | .num, .record _ _, _, h | .comp, .record _ _, _, h | .app, .record _ _, _, h
  | .capp, .record _ _, _, h => by simp [reqC] at h
  | .num, .con as t, ps, h | .comp, .con as t, ps, h | .app, .con as t, ps, h
  | .capp, .con as t, ps, h => by
    simp only [reqC] at h
    split at h
    · rename_i ks _; simp only [Ty.vars]; exact reqL_vars ks as ps h
    · cases h
theorem reqL_vars : ∀ (ks : List Cls) (as : List Ty) (ps : List (TyVar × Cls)), reqL ks as = some ps →
    ∀ p ∈ ps, BVar.ty p.1 ∈ Ty.listVars as
  | [], [], ps, h => by simp only [reqL, Option.some.injEq] at h; subst h; intro _ h; cases h
  | k :: ks, τ :: ts, ps, h => by
    simp only [reqL] at h
    split at h
    · rename_i a b ha hb
      simp only [Option.some.injEq] at h; subst h
      intro p hp
      simp only [Ty.listVars, List.mem_append]
      rcases List.mem_append.mp hp with hp | hp
      · exact .inl (reqC_vars k τ a ha p hp)
      · exact .inr (reqL_vars ks ts b hb p hp)
    · cases h
  | [], _ :: _, _, h => by simp [reqL] at h
  | _ :: _, [], _, h => by simp [reqL] at h
end

/-! ## K11 -/

/-- Admissibility is stable under a substitution respecting classes. -/
theorem admC_sb {s : FSub} (hs : RespC s) {k : Cls} {τ : Ty} (h : Adm k τ) : Adm k (sb s τ) := by
  cases hr : reqC k τ with
  | none =>
    exfalso; apply reqC_none idS k τ hr; rw [sb_id]; exact h
  | some ps =>
    rw [reqC_spec s k τ ps hr]
    have h' := (reqC_spec idS k τ ps hr).mp (by rw [sb_id]; exact h)
    intro p hp
    have hv := h' p hp
    simp only [idS] at hv
    obtain ⟨b, c⟩ := p
    have := admC_var_iff.mp hv
    exact adm_mono this (hs b)

theorem respC_comp {s t : FSub} (hs : RespC s) (ht : RespC t) : RespC (comp t s) := fun a =>
  admC_sb ht (hs a)

end StandardElm.Stat.Complete
