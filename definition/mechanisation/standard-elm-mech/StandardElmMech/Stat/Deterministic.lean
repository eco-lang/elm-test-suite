/-
  A Standard Definition of Elm? Mechanisation: the deterministic parts of the static semantics as
  functions, plan step 9 (section 10, group 7): type expressions, exposing lists and imports, the
  type declarations of a module given the type names they generate, ports. The checker of
  annotated phrases (Annotated.lean) computes these parts instead of reading them from the
  certificate; each function is proved sound for its relation here, and the converses (the iff
  theorems) are in DeterministicIff.lean.
-/
import StandardElmMech.Stat.Modules

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Src (BTy BTyRow BItem BExpList BImport BConBind BDatBind BTypBind BTopDec BHeader BModule)

/-! ## Type expressions -/

mutual
def elabTy (C : Ctx) : BTy → Option Ty
  | .tyvar a =>
    if BVar.ty (.named a) ∈ C.U then some (.var (.named a))
    else if classOfName a = .any ∧ BVar.row (.named a) ∈ C.U then some (.record [] (some (.named a)))
    else none
  | .record row =>
    match elabTyRowOpt C row with
    | some ρ => some (.record ρ none)
    | none => none
  | .openRecord r row =>
    if classOfName r = .any ∧ BVar.row (.named r) ∈ C.U then
      match elabTyRow C row with
      | some ρ => some (.record ρ (some (.named r)))
      | none => none
    else none
  | .unit => some tUnitTy
  | .tuple t1 t2 t3 =>
    match elabTy C t1, elabTy C t2, elabTyOpt C t3 with
    | some τ1, some τ2, some τ3 => some (tupleTy τ1 τ2 τ3)
    | _, _, _ => none
  | .con c args =>
    match C.lookupTy c, elabTyList C args with
    | some (θ, _), some τs => θ.apply τs
    | _, _ => none
  | .fn t1 t2 =>
    match elabTy C t1, elabTy C t2 with
    | some τ1, some τ2 => some (.fn τ1 τ2)
    | _, _ => none
  | .paren t => elabTy C t
def elabTyRow (C : Ctx) : BTyRow → Option Row
  | .field l t rest =>
    match elabTy C t, elabTyRowOpt C rest with
    | some τ, some ρ => some (Row.modify [(l, τ)] ρ)
    | _, _ => none
def elabTyRowOpt (C : Ctx) : Option BTyRow → Option Row
  | none => some []
  | some row => elabTyRow C row
/-- `some none` for an absent option. -/
def elabTyOpt (C : Ctx) : Option BTy → Option (Option Ty)
  | none => some none
  | some t =>
    match elabTy C t with
    | some τ => some (some τ)
    | none => none
def elabTyList (C : Ctx) : List BTy → Option (List Ty)
  | [] => some []
  | t :: ts =>
    match elabTy C t, elabTyList C ts with
    | some τ, some τs => some (τ :: τs)
    | _, _ => none
end

set_option maxHeartbeats 400000 in
mutual
theorem elabTy_sound (C : Ctx) : (t : BTy) → (τ : Ty) → elabTy C t = some τ → ElTy C t τ
  | .tyvar a, τ, h => by
    unfold elabTy at h
    split at h
    · cases h; exact .r_s_ty_tyvar ‹_›
    · split at h
      · cases h; rename_i hc; exact .r_s_ty_rowvar hc.1 hc.2
      · cases h
  | .record row, τ, h => by
    unfold elabTy at h
    split at h
    · cases h; exact .r_s_ty_record (elabTyRowOpt_sound C row _ ‹_›)
    · cases h
  | .openRecord r row, τ, h => by
    unfold elabTy at h
    split at h
    · rename_i hc
      split at h
      · cases h; exact .r_s_ty_openrecord hc.1 hc.2 (elabTyRow_sound C row _ ‹_›)
      · cases h
    · cases h
  | .unit, τ, h => by unfold elabTy at h; cases h; exact .r_s_ty_unit
  | .tuple t1 t2 t3, τ, h => by
    unfold elabTy at h
    split at h
    · rename_i τ1 τ2 τ3 h1 h2 h3
      cases h
      exact .r_s_ty_tuple (elabTy_sound C t1 _ h1) (elabTy_sound C t2 _ h2) (elabTyOpt_sound C t3 _ h3)
    · cases h
  | .con c args, τ, h => by
    unfold elabTy at h
    split at h
    · rename_i θ VE τs hl hs
      exact .r_s_ty_con hl (elabTyList_sound C args _ hs) h
    · cases h
  | .fn t1 t2, τ, h => by
    unfold elabTy at h
    split at h
    · rename_i τ1 τ2 h1 h2
      cases h
      exact .r_s_ty_fun (elabTy_sound C t1 _ h1) (elabTy_sound C t2 _ h2)
    · cases h
  | .paren t, τ, h => by
    unfold elabTy at h
    exact .r_s_ty_paren (elabTy_sound C t _ h)
theorem elabTyRow_sound (C : Ctx) : (r : BTyRow) → (ρ : Row) → elabTyRow C r = some ρ → ElTyRow C r ρ
  | .field l t rest, ρ, h => by
    unfold elabTyRow at h
    split at h
    · rename_i τ ρ' h1 h2
      cases h
      exact .r_s_tyrow (elabTy_sound C t _ h1) (elabTyRowOpt_sound C rest _ h2)
    · cases h
theorem elabTyRowOpt_sound (C : Ctx) : (r : Option BTyRow) → (ρ : Row) → elabTyRowOpt C r = some ρ → ElTyRowOpt C r ρ
  | none, ρ, h => by unfold elabTyRowOpt at h; cases h; exact .opt_none
  | some r, ρ, h => by unfold elabTyRowOpt at h; exact .opt_some (elabTyRow_sound C r ρ h)
theorem elabTyOpt_sound (C : Ctx) : (t : Option BTy) → (τ : Option Ty) → elabTyOpt C t = some τ → ElTyOpt C t τ
  | none, τ, h => by unfold elabTyOpt at h; cases h; exact .opt_none
  | some t, τ, h => by
    unfold elabTyOpt at h
    split at h
    · cases h; exact .opt_some (elabTy_sound C t _ ‹_›)
    · cases h
theorem elabTyList_sound (C : Ctx) : (ts : List BTy) → (τs : List Ty) → elabTyList C ts = some τs → ElTyList C ts τs
  | [], τs, h => by unfold elabTyList at h; cases h; exact .seq_nil
  | t :: ts, τs, h => by
    unfold elabTyList at h
    split at h
    · rename_i τ τs' h1 h2
      cases h
      exact .seq_cons (elabTy_sound C t _ h1) (elabTyList_sound C ts _ h2)
    · cases h
end

/-! ## Exposing lists and imports -/

def elabItem (mI : ModId × IEnv) : BItem → Option (List SmLongId × List SmLongId)
  | .var x => if x ∈ mI.2.VE.keys then some ([], [⟨none, .val x⟩]) else none
  | .op o => if o ∈ smops mI.1 then some ([], []) else none
  | .ty c =>
    match mI.2.TE.find? c with
    | some (_, VE) => some ([⟨none, .ty c⟩], (ValEnv.ofStatusV VE).keys.map fun k => ⟨none, .val k⟩)
    | none => none
  | .tyAll c =>
    match mI.2.TE.find? c with
    | some (_, VE) =>
      if VE.keys.any (fun k => (VE.find? k).any (·.2 == .c)) then
        some ([⟨none, .ty c⟩], (VE.keys.filter (· ∈ mI.2.VE.keys)).map fun k => ⟨none, .val k⟩)
      else none
    | none => none

def elabItems (mI : ModId × IEnv) : List BItem → Option (List SmLongId × List SmLongId)
  | [] => some ([], [])
  | it :: rest =>
    match elabItem mI it, elabItems mI rest with
    | some (N, N'), some (M, M') => some (unionL N M, unionL N' M')
    | _, _ => none

def elabExpList (mI : ModId × IEnv) : BExpList → Option (List SmLongId × List SmLongId)
  | .all => some ([], unqualified mI.2.dom)
  | .items is => elabItems mI is

def elabImports (B : SBasis) (π : ProvMap) : List BImport → Option ProvMap
  | [] => some π
  | i :: is =>
    match B.ME.find? i.mod with
    | none => none
    | some I =>
      let π1 := π.merge i.mod [] (qualified (i.alias.getD i.mod) I)
      match i.exposing with
      | none => elabImports B π1 is
      | some el =>
        match elabExpList (i.mod, I) el with
        | some (N, N') => elabImports B (π1.merge i.mod N N') is
        | none => none

theorem elabItem_sound (mI : ModId × IEnv) (it : BItem) (NN : List SmLongId × List SmLongId)
    (h : elabItem mI it = some NN) : ElItem mI it NN := by
  obtain ⟨mid, I⟩ := mI
  cases it with
  | var x =>
    by_cases hx : x ∈ I.VE.keys
    · simp only [elabItem, hx, if_true, Option.some.injEq] at h; subst h; exact .r_sm_item_var hx
    · simp [elabItem, hx] at h
  | op o =>
    by_cases ho : o ∈ smops mid
    · simp only [elabItem, ho, if_true, Option.some.injEq] at h; subst h; exact .r_sm_item_op ho
    · simp [elabItem, ho] at h
  | ty c =>
    simp only [elabItem] at h
    split at h
    · rename_i θ VE hf; cases h; exact .r_sm_item_type hf
    · cases h
  | tyAll c =>
    simp only [elabItem] at h
    split at h
    · rename_i θ VE hf
      split at h
      · rename_i hany
        cases h
        refine .r_sm_item_opentype hf ?_
        obtain ⟨k, _, hk⟩ := List.any_eq_true.mp hany
        cases hv : VE.find? k with
        | none => rw [hv] at hk; cases hk
        | some b =>
          rw [hv] at hk
          obtain ⟨σ, st⟩ := b
          simp only [Option.any_some, beq_iff_eq] at hk
          subst hk
          exact ⟨k, σ, hv⟩
      · cases h
    · cases h

theorem elabItems_sound (mI : ModId × IEnv) : (is : List BItem) → (NN : List SmLongId × List SmLongId) →
    elabItems mI is = some NN → ElItemList mI is NN
  | [], NN, h => by simp only [elabItems, Option.some.injEq] at h; subst h; exact .seq_nil
  | it :: rest, NN, h => by
    simp only [elabItems] at h
    split at h
    · rename_i N N' M M' h1 h2
      cases h
      exact .seq_cons (elabItem_sound mI it _ h1) (elabItems_sound mI rest _ h2)
    · cases h

theorem elabExpList_sound (mI : ModId × IEnv) (el : BExpList) (NN : List SmLongId × List SmLongId)
    (h : elabExpList mI el = some NN) : ElExpList mI el NN := by
  obtain ⟨mid, I⟩ := mI
  cases el with
  | all => simp only [elabExpList, Option.some.injEq] at h; subst h; exact .r_sm_explist_all
  | items is => exact .r_sm_explist_items (elabItems_sound _ is NN h)

theorem elabImports_sound (B : SBasis) : (is : List BImport) → (π π' : ProvMap) →
    elabImports B π is = some π' → ElImports B π is π'
  | [], π, π', h => by simp only [elabImports, Option.some.injEq] at h; subst h; exact .r_sm_imports_empty
  | i :: is, π, π', h => by
    simp only [elabImports] at h
    split at h
    · cases h
    · rename_i I hI
      split at h
      · rename_i hex
        have := elabImports_sound B is _ π' h
        refine .r_sm_imports_import (NN := none) hI ?_ ?_
        · rw [hex]; exact .opt_none
        · exact this
      · rename_i el hex
        split at h
        · rename_i N N' hel
          refine .r_sm_imports_import (NN := some (N, N')) hI ?_ (elabImports_sound B is _ π' h)
          rw [hex]; exact .opt_some (elabExpList_sound _ el _ hel)
        · cases h

/-! ## Type declarations, given the type names they generate -/

def elabConBind (C : Ctx) (τ : Ty) : BConBind → Option ValEnv
  | [] => some []
  | (k, tys) :: rest =>
    match elabTyList C tys, elabConBind C τ rest with
    | some τs, some VE => some (FMap.modify [(k, (mono (arrows τs τ), .c))] VE)
    | _, _ => none

theorem elabConBind_sound (C : Ctx) (τ : Ty) : (cb : BConBind) → (VE : ValEnv) →
    elabConBind C τ cb = some VE → ElConBindOpt C τ cb VE
  | [], VE, h => by simp only [elabConBind, Option.some.injEq] at h; subst h; exact .opt_none
  | (k, tys) :: rest, VE, h => by
    simp only [elabConBind] at h
    split at h
    · rename_i τs VE' h1 h2
      cases h
      have hr := elabConBind_sound C τ rest VE' h2
      exact .opt_some (.r_sm_conbind (elabTyList_sound C tys τs h1) hr)
    · cases h

/-- The new names condition of r:sm-topdec-types, as a Boolean. -/
def namesNewB (T : List TyName) (TE : TyEnv) : Bool :=
  TE.vals.all fun s => match s.1.name? with
    | some t => !decide (t ∈ T)
    | none => true

theorem namesNewB_spec (T : List TyName) (TE : TyEnv) (h : namesNewB T TE = true) :
    ∀ s ∈ TE.vals, ∀ t, s.1.name? = some t → t ∉ T := by
  intro s hs t ht
  have := List.all_eq_true.mp h s hs
  rw [ht] at this
  simpa using this

def elabDatBind (C : Ctx) (names : String → Option TyName) : BDatBind → Option (ValEnv × TyEnv)
  | [] => some ([], [])
  | (c, ps, cb) :: rest =>
    match names c with
    | none => none
    | some t =>
      match elabTyList (C.plusU (seqVars ps (conBindExtNames cb))) (ps.map .tyvar), elabDatBind C names rest with
      | some τs, some (VE', TE') =>
        match elabConBind (C.plusU (seqVars ps (conBindExtNames cb))) (.con τs t) cb with
        | some VE =>
          if cb ≠ [] ∧ t.arity = ps.length ∧ (∀ s ∈ TE'.vals, s.1 ≠ t.toFcn) then
            some (FMap.modify (closVE C.tyvars VE) VE', FMap.modify [(c, (t.toFcn, closVE C.tyvars VE))] TE')
          else none
        | none => none
      | _, _ => none

theorem elabDatBind_sound (C : Ctx) (names : String → Option TyName) : (d : BDatBind) → (VE : ValEnv) →
    (TE : TyEnv) → elabDatBind C names d = some (VE, TE) → ElDatBindOpt C d VE TE
  | [], VE, TE, h => by simp only [elabDatBind, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact .opt_none
  | (c, ps, cb) :: rest, VE, TE, h => by
    simp only [elabDatBind] at h
    split at h
    · cases h
    · rename_i t _
      split at h
      · rename_i τs VE' TE' h1 h2
        split at h
        · rename_i VEc h3
          split at h
          · rename_i hc
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hr := elabDatBind_sound C names rest VE' TE' h2
            obtain ⟨hne, har, hdist⟩ := hc
            have hcb := elabConBind_sound _ _ cb VEc h3
            cases cb with
            | nil => exact absurd rfl hne
            | cons kt cbr =>
              cases hcb with
              | opt_some hcb =>
                exact .opt_some (.r_sm_datbind rfl (elabTyList_sound _ _ _ h1) hcb har hr hdist)
          · cases h
        · cases h
      · cases h

def elabTypBind (C : Ctx) (tb : BTypBind) : Option (ValEnv × TyEnv) :=
  match elabTy (C.plusU (seqVars tb.params (bTyExtNames tb.t))) tb.t with
  | none => none
  | some τ =>
    match smlabs tb.t with
    | none => some ([], [(tb.c, (TyFcn.canon ⟨seqVars tb.params (bTyExtNames tb.t), τ⟩, []))])
    | some ls =>
      match τ with
      | .record ρ none =>
        match Row.lookupAll ρ ls with
        | some τs =>
          if ρ.length = ls.length then
            some (closVE C.tyvars [(tb.c, (mono (arrows τs τ), .v))],
              [(tb.c, (TyFcn.canon ⟨seqVars tb.params (bTyExtNames tb.t), τ⟩, closVE C.tyvars [(tb.c, (mono (arrows τs τ), .v))]))])
          else none
        | none => none
      | _ => none

theorem elabTypBind_sound (C : Ctx) (tb : BTypBind) (VE : ValEnv) (TE : TyEnv)
    (h : elabTypBind C tb = some (VE, TE)) : ElTypBind C tb VE TE := by
  unfold elabTypBind at h
  cases hτ : elabTy (C.plusU (seqVars tb.params (bTyExtNames tb.t))) tb.t with
  | none => rw [hτ] at h; cases h
  | some τ =>
    rw [hτ] at h
    simp only at h
    cases hl : smlabs tb.t with
    | none =>
      rw [hl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .r_sm_typbind rfl (elabTy_sound _ _ _ hτ) hl
    | some ls =>
      rw [hl] at h
      simp only at h
      match τ, h with
      | .record ρ none, h =>
        simp only at h
        cases hτs : Row.lookupAll ρ ls with
        | none => rw [hτs] at h; cases h
        | some τs =>
          rw [hτs] at h
          simp only at h
          split at h
          · rename_i hlen
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .r_sm_typbind_record rfl (elabTy_sound _ _ _ hτ) hl rfl hτs hlen rfl
          · cases h
      | .record _ (some _), h => cases h
      | .var _, h => cases h
      | .fn _ _, h => cases h
      | .con _ _, h => cases h

def elabTypBinds (C : Ctx) : List BTypBind → Option (List ValEnv × List TyEnv)
  | [] => some ([], [])
  | tb :: tbs =>
    match elabTypBind C tb, elabTypBinds C tbs with
    | some (VE, TE), some (VEs, TEs) => some (VE :: VEs, TE :: TEs)
    | _, _ => none

theorem elabTypBinds_sound (C : Ctx) : (tbs : List BTypBind) → (VEs : List ValEnv) → (TEs : List TyEnv) →
    elabTypBinds C tbs = some (VEs, TEs) → ElTypBindList C tbs VEs TEs
  | [], VEs, TEs, h => by
    simp only [elabTypBinds, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact .seq_nil
  | tb :: tbs, VEs, TEs, h => by
    simp only [elabTypBinds] at h
    split at h
    · rename_i VE TE VEs' TEs' h1 h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .seq_cons (elabTypBind_sound C tb VE TE h1) (elabTypBinds_sound C tbs VEs' TEs' h2)
    · cases h

/-- The type names a type environment gives its custom types. -/
def namesOf (TE : TyEnv) (c : String) : Option TyName := (TE.find? c).bind fun s => s.1.name?

/-- The premises of r:sm-topdec-types for a given TE and VE, except that TE is closed. -/
def checkTypesFix (C : Ctx) (TE : TyEnv) (VE : ValEnv) (db : Option BDatBind) (tbs : List BTypBind) : Bool :=
  let Cte := C.oplusTE TE
  match db with
  | none =>
    match elabTypBinds Cte tbs with
    | some (VEs, TEs) => decide (tbs ≠ [] ∧ FMap.plusAll TEs = TE ∧ FMap.plusAll VEs = VE)
    | none => false
  | some d =>
    match elabDatBind Cte (namesOf TE) d, elabTypBinds Cte tbs with
    | some (VE', TE'), some (VEs, TEs) =>
      namesNewB C.T TE' && decide (d ≠ [] ∧ FMap.modify TE' (FMap.plusAll TEs) = TE ∧
        FMap.modify VE' (FMap.plusAll VEs) = VE)
    | _, _ => false

/-- The premises of r:sm-topdec-types for a given TE and VE: TE is a fixed point and has no free
    type or row variable (the side condition `tyvars TE = ∅`, erratum of 2026-11-12: without it a
    custom type's constructors may stay open, their variables free in TE because free in TE,
    ModuleStepCounterexample.lean). -/
def checkTypes (C : Ctx) (TE : TyEnv) (VE : ValEnv) (db : Option BDatBind) (tbs : List BTypBind) : Bool :=
  checkTypesFix C TE VE db tbs && (TyEnv.tyvars TE).isEmpty

theorem checkTypes_fix {C : Ctx} {TE : TyEnv} {VE : ValEnv} {db : Option BDatBind} {tbs : List BTypBind}
    (h : checkTypes C TE VE db tbs = true) : checkTypesFix C TE VE db tbs = true := by
  simp only [checkTypes, Bool.and_eq_true] at h; exact h.1

theorem checkTypes_closed {C : Ctx} {TE : TyEnv} {VE : ValEnv} {db : Option BDatBind} {tbs : List BTypBind}
    (h : checkTypes C TE VE db tbs = true) : TyEnv.tyvars TE = [] := by
  simp only [checkTypes, Bool.and_eq_true, List.isEmpty_iff] at h; exact h.2

theorem checkTypesFix_sound (C : Ctx) (TE : TyEnv) (VE : ValEnv) (db : Option BDatBind) (tbs : List BTypBind)
    (h : checkTypesFix C TE VE db tbs = true) : TypesOK (C.oplusTE TE) C db tbs TE VE := by
  unfold checkTypesFix at h
  cases db with
  | none =>
    simp only at h
    split at h
    · rename_i VEs TEs h1
      simp only [decide_eq_true_eq] at h
      obtain ⟨hne, rfl, rfl⟩ := h
      exact .opt_none hne (elabTypBinds_sound _ _ _ _ h1)
    · cases h
  | some d =>
    simp only at h
    split at h
    · rename_i VE' TE' VEs TEs h1 h2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hn, hne, rfl, rfl⟩ := h
      have hd := elabDatBind_sound _ _ d VE' TE' h1
      obtain _ | ⟨d1, ds⟩ := d
      · exact absurd rfl hne
      · cases hd with
        | opt_some hd =>
          exact .opt_some hd (namesNewB_spec _ _ hn) hne (elabTypBinds_sound _ _ _ _ h2)
    · cases h

theorem checkTypes_sound (C : Ctx) (TE : TyEnv) (VE : ValEnv) (db : Option BDatBind) (tbs : List BTypBind)
    (h : checkTypes C TE VE db tbs = true) : TypesOK (C.oplusTE TE) C db tbs TE VE ∧ TyEnv.tyvars TE = [] :=
  ⟨checkTypesFix_sound C TE VE db tbs (checkTypes_fix h), checkTypes_closed h⟩

/-! ## Ports -/

/-- r:sm-topdec-portout and r:sm-topdec-portin, given U. -/
def elabPort (C : Ctx) (x : Var) (ty : BTy) (U : List BVar) : Option (Env × PortEnv) :=
  if newForB U ty C.U then
    match elabTy (C.plusU U) ty with
    | some (.fn τ' (.con [.var α] t)) =>
      if t = tCmd ∧ portB τ' = true then
        some (Env.ofVE [(x, (closScheme C.tyvars (mono (.fn τ' (.con [.var α] t))), .v))], [(x, (.out, τ'))])
      else
        match τ' with
        | .fn τ'' (.var α') =>
          if t = tSub ∧ α' = α ∧ portB τ'' = true then
            some (Env.ofVE [(x, (closScheme C.tyvars (mono (.fn τ' (.con [.var α] t))), .v))], [(x, (.inn, τ''))])
          else none
        | _ => none
    | _ => none
  else none

end StandardElm.Stat
