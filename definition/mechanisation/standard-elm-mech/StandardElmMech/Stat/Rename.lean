/-
  A Standard Definition of Elm? Mechanisation: renamings of derivations, plan step 10 (Lean
  definitions, "Renamings"; Theorems, "The variables of a group and the invariance lemma"), first
  layer: renamings of types and schemes and what specialisation reads of a type.

  A renaming takes type variables to type variables of the same class, row variables to row
  variables and type names to type names of the same arity, injectively, and is the identity on
  the variables the syntax names and on the type names of the basis. Specialisation reads a type
  only through the order of its type variables (`tyVarsSeq`), whether it is Int or Float or a
  number variable (`resolve`), its payload type (`toPTy`) and the shape of `main`'s scheme
  (`mainKind`); each is invariant (`tyVarsSeq_rename`, `resolve_rename`, `toPTy_rename`,
  `mainKind_rename`).
-/
import StandardElmMech.Stat.Pipeline

namespace StandardElm.Stat

/-! ## Renamings -/

/-- A renaming of a derivation: functions on type variables and on row variables, and a finite map
    on type names (the identity outside its domain). A finite map on variables is a function by
    the coercion below (the identity outside its domain). -/
structure Renaming where
  tv : TyVar → TyVar
  rv : RowVar → RowVar
  tn : List (TyName × TyName)

instance : Coe (List (TyVar × TyVar)) (TyVar → TyVar) := ⟨fun l a => (l.lookup a).getD a⟩
instance : Coe (List (RowVar × RowVar)) (RowVar → RowVar) := ⟨fun l e => (l.lookup e).getD e⟩

def Renaming.tvApply (r : Renaming) (a : TyVar) : TyVar := r.tv a
def Renaming.rvApply (r : Renaming) (e : RowVar) : RowVar := r.rv e
def Renaming.tnApply (r : Renaming) (t : TyName) : TyName := (r.tn.lookup t).getD t

/-- Injective and class-preserving on variables, the identity on the bound variables of canonical
    schemes (`bnd`), and the identity on exactly the type names of the initial basis that
    specialisation and erasure test for (`T0`). Named variables may move: a derivation may use a
    named variable that no annotation of its module binds (finding of step 10, Issues item 8). -/
structure Renaming.WF (r : Renaming) : Prop where
  tv_inj : ∀ a b, r.tvApply a = r.tvApply b → a = b
  tv_cls : ∀ a, (r.tvApply a).cls = a.cls
  tv_bnd : ∀ i c, r.tvApply (.bnd i c) = .bnd i c
  rv_inj : ∀ e e', r.rvApply e = r.rvApply e' → e = e'
  rv_bnd : ∀ i, r.rvApply (.bnd i) = .bnd i
  tn_T0 : ∀ t, ∀ t0 ∈ T0, r.tnApply t = t0 ↔ t = t0

mutual
def Renaming.ty (r : Renaming) : Ty → Ty
  | .var a => .var (r.tvApply a)
  | .record ρ tl => .record (r.row ρ) (tl.map r.rvApply)
  | .fn a b => .fn (r.ty a) (r.ty b)
  | .con as t => .con (r.tys as) (r.tnApply t)
def Renaming.row (r : Renaming) : Row → Row
  | [] => []
  | (l, τ) :: rest => (l, r.ty τ) :: r.row rest
def Renaming.tys (r : Renaming) : List Ty → List Ty
  | [] => []
  | τ :: rest => r.ty τ :: r.tys rest
end

def Renaming.bvar (r : Renaming) : BVar → BVar
  | .ty a => .ty (r.tvApply a)
  | .row e => .row (r.rvApply e)

def Renaming.scheme (r : Renaming) (σ : Scheme) : Scheme := ⟨σ.bound.map r.bvar, r.ty σ.body⟩

/-- The renaming of the assignments of the enclosing copies. -/
def Renaming.numEnv (r : Renaming) (ρ : NumEnv) : NumEnv := ρ.map fun (α, n) => (r.tvApply α, n)

theorem Renaming.tys_eq_map (r : Renaming) : ∀ l : List Ty, r.tys l = l.map r.ty
  | [] => rfl
  | τ :: rest => by simp [Renaming.tys, Renaming.tys_eq_map r rest]

/-! ## The basis names are fixed -/

/-- A name of `T0` is fixed, and nothing else is taken to it. -/
theorem Renaming.tnApply_eq_fixed {r : Renaming} (hr : r.WF) {t0 : TyName} (h0 : t0 ∈ T0) (t : TyName) :
    r.tnApply t = t0 ↔ t = t0 := hr.tn_T0 t t0 h0

theorem Renaming.tnApply_T0 {r : Renaming} (hr : r.WF) {t0 : TyName} (h0 : t0 ∈ T0) : r.tnApply t0 = t0 :=
  (hr.tn_T0 t0 t0 h0).mpr rfl

/-! ## The order of the type variables -/

mutual
theorem tyVarsSeq_rename (r : Renaming) : (τ : Ty) → (r.ty τ).tyVarsSeq = τ.tyVarsSeq.map r.tvApply
  | .var a => by simp [Renaming.ty, Ty.tyVarsSeq]
  | .record ρ tl => by simp only [Renaming.ty, Ty.tyVarsSeq]; exact rowTyVarsSeq_rename r ρ
  | .fn a b => by simp [Renaming.ty, Ty.tyVarsSeq, tyVarsSeq_rename r a, tyVarsSeq_rename r b]
  | .con as t => by simp only [Renaming.ty, Ty.tyVarsSeq]; exact listTyVarsSeq_rename r as
theorem rowTyVarsSeq_rename (r : Renaming) : (ρ : Row) → Ty.rowTyVarsSeq (r.row ρ) = (Ty.rowTyVarsSeq ρ).map r.tvApply
  | [] => rfl
  | (l, τ) :: rest => by
    simp [Renaming.row, Ty.rowTyVarsSeq, tyVarsSeq_rename r τ, rowTyVarsSeq_rename r rest]
theorem listTyVarsSeq_rename (r : Renaming) : (l : List Ty) → Ty.listTyVarsSeq (r.tys l) = (Ty.listTyVarsSeq l).map r.tvApply
  | [] => rfl
  | τ :: rest => by
    simp [Renaming.tys, Ty.listTyVarsSeq, tyVarsSeq_rename r τ, listTyVarsSeq_rename r rest]
end

/-- `dedupFirst` commutes with an injective map. -/
theorem dedupFirst_map {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β)
    (hf : ∀ a b, f a = f b → a = b) : ∀ l : List α, dedupFirst (l.map f) = (dedupFirst l).map f
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, dedupFirst, dedupFirst_map f hf xs, List.cons.injEq, true_and]
    rw [List.filter_map]
    congr 1
    apply List.filter_congr
    intro a _
    simp only [Function.comp_apply]
    exact decide_eq_decide.mpr ⟨fun h e => h (congrArg f e), fun h e => h (hf _ _ e)⟩

/-! ## Int, Float and number variables -/

theorem lookup_map_inj {α β : Type} [BEq α] [LawfulBEq α] (f : α → α) (hf : ∀ a b, f a = f b → a = b) :
    ∀ (l : List (α × β)) (a : α), (l.map fun (x, n) => (f x, n)).lookup (f a) = l.lookup a
  | [], _ => rfl
  | (x, n) :: rest, a => by
    by_cases h : x = a
    · subst h; simp [List.lookup]
    · have h' : f x ≠ f a := fun e => h (hf _ _ e)
      have e1 : (f a == f x) = false := beq_eq_false_iff_ne.mpr (Ne.symm h')
      have e2 : (a == x) = false := beq_eq_false_iff_ne.mpr (Ne.symm h)
      simp only [List.map_cons, List.lookup, e1, e2]
      exact lookup_map_inj f hf rest a

theorem resolve_rename {r : Renaming} (hr : r.WF) (ρ : NumEnv) (τ : Ty) :
    resolve (r.numEnv ρ) (r.ty τ) = resolve ρ τ := by
  have hInt := Renaming.tnApply_eq_fixed hr (t0 := tInt) (by decide)
  have hFloat := Renaming.tnApply_eq_fixed hr (t0 := tFloat) (by decide)
  cases τ with
  | var a =>
    simp only [Renaming.ty, resolve, hr.tv_cls, Renaming.numEnv]
    rw [lookup_map_inj r.tvApply hr.tv_inj ρ a]
  | record ρ' tl => simp [Renaming.ty, resolve]
  | fn a b => simp [Renaming.ty, resolve]
  | con as t =>
    cases as with
    | nil =>
      simp only [Renaming.ty, Renaming.tys, resolve]
      by_cases h1 : t = tInt
      · subst h1; simp [Renaming.tnApply_T0 hr (t0 := tInt) (by decide)]
      · by_cases h2 : t = tFloat
        · subst h2; simp [Renaming.tnApply_T0 hr (t0 := tFloat) (by decide)]
        · have h1' : r.tnApply t ≠ tInt := fun e => h1 (hInt t |>.mp e)
          have h2' : r.tnApply t ≠ tFloat := fun e => h2 (hFloat t |>.mp e)
          simp [h1, h2, h1', h2']
    | cons _ _ => simp [Renaming.ty, Renaming.tys, resolve]

/-! ## Payload types -/

mutual
theorem toPTy_rename {r : Renaming} (hr : r.WF) :
    (τ : Ty) → toPTy (r.ty τ) = toPTy τ
  | .var _ => by simp [Renaming.ty, toPTy]
  | .fn _ _ => by simp [Renaming.ty, toPTy]
  | .record ρ none => by
    simp only [Renaming.ty, Option.map_none, toPTy]
    rw [toPFields_rename hr ρ]
  | .record ρ (some e) => by simp [Renaming.ty, toPTy]
  | .con [] t => by
    simp only [Renaming.ty, Renaming.tys, toPTy]
    have e := fun t0 (h : t0 ∈ T0) => Renaming.tnApply_eq_fixed hr (t0 := t0) h t
    simp only [e tInt (by decide), e tFloat (by decide), e tBool (by decide), e tString (by decide),
      e tBytes (by decide), e tUnit (by decide), e tValue (by decide)]
  | .con [τ] t => by
    simp only [Renaming.ty, Renaming.tys, toPTy]
    have e := fun t0 (h : t0 ∈ T0) => Renaming.tnApply_eq_fixed hr (t0 := t0) h t
    simp only [e tList (by decide), e tMaybe (by decide), e tArray (by decide), toPTy_rename hr τ]
  | .con [τ1, τ2] t => by
    simp only [Renaming.ty, Renaming.tys, toPTy]
    have e := fun t0 (h : t0 ∈ T0) => Renaming.tnApply_eq_fixed hr (t0 := t0) h t
    simp only [e tTuple2 (by decide), toPTy_rename hr τ1, toPTy_rename hr τ2]
  | .con [τ1, τ2, τ3] t => by
    simp only [Renaming.ty, Renaming.tys, toPTy]
    have e := fun t0 (h : t0 ∈ T0) => Renaming.tnApply_eq_fixed hr (t0 := t0) h t
    simp only [e tTuple3 (by decide), toPTy_rename hr τ1, toPTy_rename hr τ2, toPTy_rename hr τ3]
  | .con (_ :: _ :: _ :: _ :: _) _ => by simp [Renaming.ty, Renaming.tys, toPTy]
theorem toPFields_rename {r : Renaming} (hr : r.WF) :
    (ρ : Row) → toPFields (r.row ρ) = toPFields ρ
  | [] => rfl
  | (l, τ) :: rest => by
    simp only [Renaming.row, toPFields]
    rw [toPTy_rename hr τ, toPFields_rename hr rest]
end

/-! ## `Dflt` and the kind of `main` -/

theorem find_map_inj {β : Type} (f : TyVar → TyVar) (g : β → Ty) (hf : ∀ a b, f a = f b → a = b) :
    ∀ (m : List (TyVar × β)) (a : TyVar),
      FMap.find? (m.map fun (x, v) => (f x, g v)) (f a) = (FMap.find? m a).map g
  | [], _ => rfl
  | (x, v) :: rest, a => by
    simp only [List.map_cons, FMap.find?]
    by_cases h : x = a
    · subst h; simp
    · have h' : f x ≠ f a := fun e => h (hf _ _ e)
      simp only [h, h', ↓reduceIte]
      exact find_map_inj f g hf rest a

/-- A substitution on type variables only, renamed: its domain by `r`, its range by `r.ty`. -/
def Renaming.substTy (r : Renaming) (m : List (TyVar × Ty)) : Subst :=
  ⟨m.map fun (a, τ) => (r.tvApply a, r.ty τ), []⟩

mutual
theorem apply_rename {r : Renaming} (hr : r.WF) (m : List (TyVar × Ty)) :
    (τ : Ty) → (r.substTy m).apply (r.ty τ) = (Subst.apply ⟨m, []⟩ τ).map r.ty
  | .var a => by
    simp only [Renaming.ty, Subst.apply, Renaming.substTy, Option.map_some]
    rw [find_map_inj r.tvApply r.ty hr.tv_inj m a]
    cases FMap.find? m a <;> rfl
  | .record ρ none => by
    simp only [Renaming.ty, Option.map_none, Subst.apply]
    rw [applyRow_rename hr m ρ]
    cases Subst.applyRow ⟨m, []⟩ ρ <;> rfl
  | .record ρ (some e) => by
    simp only [Renaming.ty, Option.map_some, Subst.apply]
    rw [applyRow_rename hr m ρ]
    cases Subst.applyRow ⟨m, []⟩ ρ <;> rfl
  | .fn a b => by
    simp only [Renaming.ty, Subst.apply]
    rw [apply_rename hr m a, apply_rename hr m b]
    cases Subst.apply ⟨m, []⟩ a <;> cases Subst.apply ⟨m, []⟩ b <;> rfl
  | .con as t => by
    simp only [Renaming.ty, Subst.apply]
    rw [applyList_rename hr m as]
    cases Subst.applyList ⟨m, []⟩ as <;> rfl
theorem applyRow_rename {r : Renaming} (hr : r.WF) (m : List (TyVar × Ty)) :
    (ρ : Row) → (r.substTy m).applyRow (r.row ρ) = (Subst.applyRow ⟨m, []⟩ ρ).map r.row
  | [] => rfl
  | (l, τ) :: rest => by
    simp only [Renaming.row, Subst.applyRow]
    rw [apply_rename hr m τ, applyRow_rename hr m rest]
    cases Subst.apply ⟨m, []⟩ τ <;> cases Subst.applyRow ⟨m, []⟩ rest <;> rfl
theorem applyList_rename {r : Renaming} (hr : r.WF) (m : List (TyVar × Ty)) :
    (l : List Ty) → (r.substTy m).applyList (r.tys l) = (Subst.applyList ⟨m, []⟩ l).map r.tys
  | [] => rfl
  | τ :: rest => by
    simp only [Renaming.tys, Subst.applyList]
    rw [apply_rename hr m τ, applyList_rename hr m rest]
    cases Subst.apply ⟨m, []⟩ τ <;> cases Subst.applyList ⟨m, []⟩ rest <;> rfl
end

/-- The substitution of `Dflt`. -/
def dfltMap (bound : List BVar) : List (TyVar × Ty) :=
  bound.filterMap fun v => match v with
    | .ty a => if a.cls = .num then some (a, tFloatTy) else none
    | .row _ => none

theorem dflt_eq (σ : Scheme) : dflt σ = (Subst.apply ⟨dfltMap σ.bound, []⟩ σ.body).getD σ.body := rfl

theorem dfltMap_rename {r : Renaming} (hr : r.WF) :
    ∀ bound : List BVar, dfltMap (bound.map r.bvar) = (dfltMap bound).map fun (a, τ) => (r.tvApply a, r.ty τ)
  | [] => rfl
  | v :: rest => by
    have ih := dfltMap_rename hr rest
    have hF : r.ty tFloatTy = tFloatTy := by
      simp [tFloatTy, Renaming.ty, Renaming.tys, Renaming.tnApply_T0 hr (t0 := tFloat) (by decide)]
    cases v with
    | ty a =>
      by_cases hc : a.cls = .num
      · simp only [dfltMap, List.map_cons, Renaming.bvar, List.filterMap_cons, hr.tv_cls, hc, ↓reduceIte] at ih ⊢
        rw [ih, hF]
      · simp only [dfltMap, List.map_cons, Renaming.bvar, List.filterMap_cons, hr.tv_cls, hc, ↓reduceIte] at ih ⊢
        exact ih
    | row e =>
      simp only [dfltMap, List.map_cons, Renaming.bvar, List.filterMap_cons] at ih ⊢
      exact ih

theorem dflt_rename {r : Renaming} (hr : r.WF) (σ : Scheme) :
    dflt (r.scheme σ) = r.ty (dflt σ) := by
  rw [dflt_eq, dflt_eq]
  simp only [Renaming.scheme]
  rw [dfltMap_rename hr σ.bound]
  have := apply_rename hr (dfltMap σ.bound) σ.body
  simp only [Renaming.substTy] at this
  rw [this]
  cases Subst.apply ⟨dfltMap σ.bound, []⟩ σ.body <;> rfl

/-- The view part of `mainKind`. -/
def nodeKind : Ty → Option (Mod.ProgKind × Eff.PTy)
  | .con [_] t => if t = tNode then some (.view, .unit) else none
  | _ => none

theorem mainKind_eq (σ : Scheme) : mainKind σ =
    match σ.body with
    | .con [τ1, _, _] t => if t = tProgram then (toPTy τ1).map (.worker, ·) else nodeKind (dflt σ)
    | _ => nodeKind (dflt σ) := by
  unfold mainKind nodeKind
  rcases σ with ⟨bnd, body⟩
  simp only
  rcases body with _ | _ | _ | ⟨as, t⟩ <;> rfl

theorem nodeKind_rename {r : Renaming} (hr : r.WF) (τ : Ty) :
    nodeKind (r.ty τ) = nodeKind τ := by
  have e := Renaming.tnApply_eq_fixed hr (t0 := tNode) (by decide)
  cases τ with
  | con as t =>
    rcases as with _ | ⟨τ1, _ | ⟨τ2, rest⟩⟩
    · rfl
    · simp only [Renaming.ty, Renaming.tys, nodeKind, e t]
    · rfl
  | _ => rfl

theorem mainKind_rename {r : Renaming} (hr : r.WF) (σ : Scheme) :
    mainKind (r.scheme σ) = mainKind σ := by
  have e := Renaming.tnApply_eq_fixed hr (t0 := tProgram) (by decide)
  rw [mainKind_eq, mainKind_eq, dflt_rename hr, nodeKind_rename hr]
  simp only [Renaming.scheme]
  cases σ.body with
  | con as t =>
    rcases as with _ | ⟨τ1, _ | ⟨τ2, _ | ⟨τ3, _ | ⟨τ4, rest⟩⟩⟩⟩
    · rfl
    · rfl
    · rfl
    · simp only [Renaming.ty, Renaming.tys, e t, toPTy_rename hr τ1]
    · rfl
  | _ => rfl

end StandardElm.Stat
