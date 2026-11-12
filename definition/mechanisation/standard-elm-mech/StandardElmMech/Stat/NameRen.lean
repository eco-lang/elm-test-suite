/-
  A Standard Definition of Elm? Mechanisation: renamings of type names only (plan step 10, the
  transport of derivations across bases, first layer).

  `nr ρ` renames type names by the finite map ρ and leaves every variable alone. When ρ is
  injective, keeps arities and fixes the names of `T0` (`NR ρ`), it is a `Renaming.WF`, and the
  objects the checker computes commute with it: rows, substitutions, instances, admissibility,
  canonical forms, closure, contexts, and the elaboration of type expressions.
-/
import StandardElmMech.Stat.MutualModule

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Src (BTy BTyRow)

/-- A renaming of type names only. -/
def nr (ρ : List (TyName × TyName)) : Renaming := ⟨fun a => a, fun e => e, ρ⟩

/-- Injective, arity-preserving, the identity on `T0`. -/
structure NR (ρ : List (TyName × TyName)) : Prop where
  inj : ∀ t u, (nr ρ).tnApply t = (nr ρ).tnApply u → t = u
  ar : ∀ t, ((nr ρ).tnApply t).arity = t.arity
  t0 : ∀ t ∈ T0, (nr ρ).tnApply t = t

section
variable {ρ : List (TyName × TyName)}

@[simp] theorem nr_tv (a : TyVar) : (nr ρ).tvApply a = a := rfl
@[simp] theorem nr_rv (e : RowVar) : (nr ρ).rvApply e = e := rfl
@[simp] theorem nr_bvar (v : BVar) : (nr ρ).bvar v = v := by cases v <;> rfl
@[simp] theorem nr_bvar_fun : (nr ρ).bvar = fun v => v := funext nr_bvar
@[simp] theorem nr_rv_fun : (nr ρ).rvApply = fun e => e := rfl

theorem NR.wf (h : NR ρ) : (nr ρ).WF :=
  ⟨fun _ _ e => e, fun _ => rfl, fun _ _ => rfl, fun _ _ e => e, fun _ => rfl,
   fun t t0 h0 => ⟨fun e => h.inj _ _ (e.trans (h.t0 t0 h0).symm), fun e => by subst e; exact h.t0 _ h0⟩⟩

theorem NR.fix (h : NR ρ) {t0 : TyName} (h0 : t0 ∈ T0) : (nr ρ).tnApply t0 = t0 := h.t0 t0 h0

theorem NR.beq (h : NR ρ) {t0 : TyName} (h0 : t0 ∈ T0) (t : TyName) :
    ((nr ρ).tnApply t == t0) = (t == t0) := by
  rw [Bool.eq_iff_iff]; simp only [beq_iff_eq]; exact h.wf.tn_T0 t t0 h0

theorem NR.eq (h : NR ρ) {t0 : TyName} (h0 : t0 ∈ T0) (t : TyName) :
    ((nr ρ).tnApply t = t0) = (t = t0) := propext (h.wf.tn_T0 t t0 h0)

/-! ## Types -/

@[simp] theorem nr_ty_var (a : TyVar) : (nr ρ).ty (.var a) = .var a := rfl
@[simp] theorem nr_ty_record (r : Row) (tl : Option RowVar) : (nr ρ).ty (.record r tl) = .record ((nr ρ).row r) tl := by
  simp [Renaming.ty]
@[simp] theorem nr_ty_fn (a b : Ty) : (nr ρ).ty (.fn a b) = .fn ((nr ρ).ty a) ((nr ρ).ty b) := rfl
@[simp] theorem nr_ty_con (as : List Ty) (t : TyName) : (nr ρ).ty (.con as t) = .con (as.map (nr ρ).ty) ((nr ρ).tnApply t) := by
  simp [Renaming.ty, Renaming.tys_eq_map]
@[simp] theorem nr_row_nil : (nr ρ).row [] = [] := rfl
@[simp] theorem nr_row_cons (l : Lab) (τ : Ty) (r : Row) : (nr ρ).row ((l, τ) :: r) = (l, (nr ρ).ty τ) :: (nr ρ).row r := rfl

mutual
theorem nr_ty_inj (h : NR ρ) : (τ τ' : Ty) → (nr ρ).ty τ = (nr ρ).ty τ' → τ = τ'
  | .var a, .var b, e => by simpa using e
  | .record r tl, .record r' tl', e => by
    simp only [nr_ty_record, Ty.record.injEq] at e
    rw [nr_row_inj h r r' e.1, e.2]
  | .fn a b, .fn a' b', e => by
    simp only [nr_ty_fn, Ty.fn.injEq] at e
    rw [nr_ty_inj h a a' e.1, nr_ty_inj h b b' e.2]
  | .con as t, .con as' t', e => by
    simp only [nr_ty_con, Ty.con.injEq] at e
    rw [nr_tys_inj h as as' e.1, h.inj t t' e.2]
  | .var _, .record _ _, e | .var _, .fn _ _, e | .var _, .con _ _, e
  | .record _ _, .var _, e | .record _ _, .fn _ _, e | .record _ _, .con _ _, e
  | .fn _ _, .var _, e | .fn _ _, .record _ _, e | .fn _ _, .con _ _, e
  | .con _ _, .var _, e | .con _ _, .record _ _, e | .con _ _, .fn _ _, e => by simp at e
theorem nr_row_inj (h : NR ρ) : (r r' : Row) → (nr ρ).row r = (nr ρ).row r' → r = r'
  | [], [], _ => rfl
  | (l, τ) :: r, (l', τ') :: r', e => by
    simp only [nr_row_cons, List.cons.injEq, Prod.mk.injEq] at e
    rw [e.1.1, nr_ty_inj h τ τ' e.1.2, nr_row_inj h r r' e.2]
  | [], (_, _) :: _, e | (_, _) :: _, [], e => by simp at e
theorem nr_tys_inj (h : NR ρ) : (l l' : List Ty) → l.map (nr ρ).ty = l'.map (nr ρ).ty → l = l'
  | [], [], _ => rfl
  | τ :: l, τ' :: l', e => by
    simp only [List.map_cons, List.cons.injEq] at e
    rw [nr_ty_inj h τ τ' e.1, nr_tys_inj h l l' e.2]
  | [], _ :: _, e | _ :: _, [], e => by simp at e
end

theorem nr_tys (l : List Ty) : (nr ρ).tys l = l.map (nr ρ).ty := Renaming.tys_eq_map _ l
theorem nr_row_map (r : Row) : (nr ρ).row r = r.map fun p => (p.1, (nr ρ).ty p.2) := Renaming.row_eq_map _ r

theorem nr_fixT0 (h : NR ρ) {t0 : TyName} (h0 : t0 ∈ T0) (as : List Ty) :
    (nr ρ).ty (.con as t0) = .con (as.map (nr ρ).ty) t0 := by simp [h.fix h0]

theorem nr_beq_ty (h : NR ρ) (τ τ' : Ty) : ((nr ρ).ty τ == (nr ρ).ty τ') = (τ == τ') := by
  rw [Bool.eq_iff_iff]; simp only [beq_iff_eq]; exact ⟨nr_ty_inj h τ τ', fun e => e ▸ rfl⟩

theorem nr_dec_ty (h : NR ρ) (τ τ' : Ty) : decide ((nr ρ).ty τ = (nr ρ).ty τ') = decide (τ = τ') :=
  decide_eq_decide.mpr ⟨nr_ty_inj h τ τ', fun e => e ▸ rfl⟩

@[simp] theorem nr_vars (τ : Ty) : ((nr ρ).ty τ).vars = τ.vars := by rw [vars_rename]; simp
@[simp] theorem nr_tyvars (τ : Ty) : ((nr ρ).ty τ).tyvars = τ.tyvars := by simp [Ty.tyvars]
@[simp] theorem nr_scheme_bound (σ : Scheme) : ((nr ρ).scheme σ).bound = σ.bound := by simp [Renaming.scheme]
@[simp] theorem nr_scheme_body (σ : Scheme) : ((nr ρ).scheme σ).body = (nr ρ).ty σ.body := rfl
@[simp] theorem nr_scheme_tyvars (σ : Scheme) : ((nr ρ).scheme σ).tyvars = σ.tyvars := by
  simp [Scheme.tyvars]
@[simp] theorem nr_tyFcn_params (θ : TyFcn) : ((nr ρ).tyFcn θ).params = θ.params := by simp [Renaming.tyFcn]
@[simp] theorem nr_tyFcn_body (θ : TyFcn) : ((nr ρ).tyFcn θ).body = (nr ρ).ty θ.body := rfl

theorem nr_mono (τ : Ty) : (nr ρ).scheme (mono τ) = mono ((nr ρ).ty τ) := rfl

mutual
theorem nr_tynames : (τ : Ty) → ((nr ρ).ty τ).tynames = τ.tynames.map (nr ρ).tnApply
  | .var _ => rfl
  | .record r tl => by simp only [nr_ty_record, Ty.tynames]; exact nr_rowTynames r
  | .fn a b => by simp [Ty.tynames, nr_tynames a, nr_tynames b]
  | .con as t => by
    simp only [nr_ty_con, Ty.tynames, List.map_cons]
    rw [← nr_tys, nr_listTynames as]
theorem nr_rowTynames : (r : Row) → Ty.rowTynames ((nr ρ).row r) = (Ty.rowTynames r).map (nr ρ).tnApply
  | [] => rfl
  | (l, τ) :: rest => by simp [Ty.rowTynames, nr_tynames τ, nr_rowTynames rest]
theorem nr_listTynames : (l : List Ty) → Ty.listTynames ((nr ρ).tys l) = (Ty.listTynames l).map (nr ρ).tnApply
  | [] => rfl
  | τ :: rest => by simp [Renaming.tys, Ty.listTynames, nr_tynames τ, nr_listTynames rest]
end

/-! ## Finite maps whose values are renamed -/

theorem find?_mapV {K V W : Type} [DecidableEq K] (g : V → W) :
    ∀ (f : FMap K V) (k : K), FMap.find? (f.map fun p => (p.1, g p.2)) k = (FMap.find? f k).map g
  | [], _ => rfl
  | (k', v) :: rest, k => by
    simp only [List.map_cons, FMap.find?]
    split <;> simp [find?_mapV g rest k]

theorem keys_mapV {K V W : Type} (g : V → W) (f : FMap K V) :
    FMap.keys (f.map fun p => (p.1, g p.2)) = FMap.keys f := by simp [FMap.keys]

theorem modify_mapV {K V W : Type} [DecidableEq K] (g : V → W) (f f' : FMap K V) :
    FMap.modify (f.map fun p => (p.1, g p.2)) (f'.map fun p => (p.1, g p.2)) =
      (FMap.modify f f').map fun p => (p.1, g p.2) := by
  unfold FMap.modify
  rw [List.map_append, List.filter_map, keys_mapV]
  rfl

theorem foldl_mapV {K V W : Type} [DecidableEq K] (g : V → W) : ∀ (fs : List (FMap K V)) (acc : FMap K V),
    List.foldl FMap.modify (acc.map fun p => (p.1, g p.2)) (fs.map fun f => f.map fun p => (p.1, g p.2)) =
      (List.foldl FMap.modify acc fs).map fun p => (p.1, g p.2)
  | [], _ => rfl
  | f :: fs, acc => by simp only [List.map_cons, List.foldl_cons, modify_mapV, foldl_mapV g fs]

theorem plusAll_mapV {K V W : Type} [DecidableEq K] (g : V → W) (fs : List (FMap K V)) :
    FMap.plusAll (fs.map fun f => f.map fun p => (p.1, g p.2)) = (FMap.plusAll fs).map fun p => (p.1, g p.2) :=
  foldl_mapV g fs []

theorem nr_valEnv_eq (VE : ValEnv) : (nr ρ).valEnv VE = VE.map fun p => (p.1, ((nr ρ).scheme p.2.1, p.2.2)) := rfl
theorem nr_tyEnv_eq (TE : TyEnv) : (nr ρ).tyEnv TE = TE.map fun p => (p.1, ((nr ρ).tyFcn p.2.1, (nr ρ).valEnv p.2.2)) := rfl

theorem nr_valEnv_find (VE : ValEnv) (x : String) :
    FMap.find? ((nr ρ).valEnv VE) x = (FMap.find? VE x).map fun b => ((nr ρ).scheme b.1, b.2) :=
  find?_mapV (fun b : Scheme × IdStatus => ((nr ρ).scheme b.1, b.2)) VE x
theorem nr_tyEnv_find (TE : TyEnv) (c : String) :
    FMap.find? ((nr ρ).tyEnv TE) c = (FMap.find? TE c).map fun s => ((nr ρ).tyFcn s.1, (nr ρ).valEnv s.2) :=
  find?_mapV (fun s : TyStr => ((nr ρ).tyFcn s.1, (nr ρ).valEnv s.2)) TE c
theorem nr_valEnv_modify (f g : ValEnv) :
    FMap.modify ((nr ρ).valEnv f) ((nr ρ).valEnv g) = (nr ρ).valEnv (FMap.modify f g) :=
  modify_mapV (fun b : Scheme × IdStatus => ((nr ρ).scheme b.1, b.2)) f g
theorem nr_tyEnv_modify (f g : TyEnv) :
    FMap.modify ((nr ρ).tyEnv f) ((nr ρ).tyEnv g) = (nr ρ).tyEnv (FMap.modify f g) :=
  modify_mapV (fun s : TyStr => ((nr ρ).tyFcn s.1, (nr ρ).valEnv s.2)) f g
theorem nr_valEnv_plusAll (fs : List ValEnv) :
    FMap.plusAll (fs.map (nr ρ).valEnv) = (nr ρ).valEnv (FMap.plusAll fs) :=
  plusAll_mapV (fun b : Scheme × IdStatus => ((nr ρ).scheme b.1, b.2)) fs
theorem nr_tyEnv_plusAll (fs : List TyEnv) :
    FMap.plusAll (fs.map (nr ρ).tyEnv) = (nr ρ).tyEnv (FMap.plusAll fs) :=
  plusAll_mapV (fun s : TyStr => ((nr ρ).tyFcn s.1, (nr ρ).valEnv s.2)) fs
@[simp] theorem nr_valEnv_keys (VE : ValEnv) : FMap.keys ((nr ρ).valEnv VE) = FMap.keys VE :=
  keys_mapV (fun b : Scheme × IdStatus => ((nr ρ).scheme b.1, b.2)) VE
@[simp] theorem nr_tyEnv_keys (TE : TyEnv) : FMap.keys ((nr ρ).tyEnv TE) = FMap.keys TE :=
  keys_mapV (fun s : TyStr => ((nr ρ).tyFcn s.1, (nr ρ).valEnv s.2)) TE

/-! ## Free variables -/

theorem nr_valEnv_tyvars (h : NR ρ) (VE : ValEnv) : ValEnv.tyvars ((nr ρ).valEnv VE) = ValEnv.tyvars VE := by
  rw [valEnv_tyvars_rename h.wf]; simp

theorem nr_tyFcn_tyvars (θ : TyFcn) : ((nr ρ).tyFcn θ).tyvars = θ.tyvars := by simp [TyFcn.tyvars]

theorem nr_tyEnv_tyvars (h : NR ρ) (TE : TyEnv) : TyEnv.tyvars ((nr ρ).tyEnv TE) = TyEnv.tyvars TE := by
  have := tyvarsBy_rename (r := nr ρ) h.wf (fun s : TyStr => s.1.tyvars ++ ValEnv.tyvars s.2)
    (fun s : TyStr => s.1.tyvars ++ ValEnv.tyvars s.2) (fun s => ((nr ρ).tyFcn s.1, (nr ρ).valEnv s.2))
    (fun s => by simp [nr_tyFcn_tyvars, nr_valEnv_tyvars h]) [] TE
  simpa [TyEnv.tyvars, nr_tyEnv_eq] using this

theorem nr_iEnv_tyvars (h : NR ρ) (I : IEnv) : ((nr ρ).iEnv I).tyvars = I.tyvars := by
  simp [IEnv.tyvars, Renaming.iEnv, nr_tyEnv_tyvars h, nr_valEnv_tyvars h]

theorem nr_env_tyvars (h : NR ρ) (E : Env) : ((nr ρ).env E).tyvars = E.tyvars := by
  unfold Env.tyvars Renaming.env
  simp only [nr_tyEnv_tyvars h, nr_valEnv_tyvars h]
  rw [tyvarsBy_rename h.wf IEnv.tyvars IEnv.tyvars (nr ρ).iEnv (fun I => by simp [nr_iEnv_tyvars h])]
  simp

@[simp] theorem nr_ctx_U (C : Ctx) : ((nr ρ).ctx C).U = C.U := by simp [Renaming.ctx]
@[simp] theorem nr_ctx_T (C : Ctx) : ((nr ρ).ctx C).T = C.T.map (nr ρ).tnApply := rfl
@[simp] theorem nr_ctx_E (C : Ctx) : ((nr ρ).ctx C).E = (nr ρ).env C.E := rfl

theorem nr_ctx_tyvars (h : NR ρ) (C : Ctx) : ((nr ρ).ctx C).tyvars = C.tyvars := by
  simp [Ctx.tyvars, nr_env_tyvars h]

/-! ## Type names of environments -/

theorem nr_valEnv_tynames (VE : ValEnv) : ValEnv.tynames ((nr ρ).valEnv VE) = (ValEnv.tynames VE).map (nr ρ).tnApply := by
  simp [ValEnv.tynames, Renaming.valEnv, List.map_flatMap, List.flatMap_map, Function.comp_def, nr_tynames]

theorem nr_tyEnv_tynames (TE : TyEnv) : TyEnv.tynames ((nr ρ).tyEnv TE) = (TyEnv.tynames TE).map (nr ρ).tnApply := by
  simp [TyEnv.tynames, Renaming.tyEnv, List.map_flatMap, List.flatMap_map, Function.comp_def, nr_tynames,
    nr_valEnv_tynames]

theorem nr_iEnv_tynames (I : IEnv) : ((nr ρ).iEnv I).tynames = I.tynames.map (nr ρ).tnApply := by
  simp [IEnv.tynames, Renaming.iEnv, nr_tyEnv_tynames, nr_valEnv_tynames]

theorem nr_env_tynames (E : Env) : ((nr ρ).env E).tynames = E.tynames.map (nr ρ).tnApply := by
  simp [Env.tynames, Renaming.env, List.map_flatMap, List.flatMap_map, Function.comp_def, nr_iEnv_tynames,
    nr_tyEnv_tynames, nr_valEnv_tynames]

theorem unionL_map_inj {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β)
    (hf : ∀ a b, f a = f b → a = b) (A B : List α) : unionL (A.map f) (B.map f) = (unionL A B).map f := by
  simp only [unionL, List.map_append, diffL_map_inj f hf]

theorem dedupL_map_inj {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β)
    (hf : ∀ a b, f a = f b → a = b) (l : List α) : dedupL (l.map f) = (dedupL l).map f := dedupL_map f hf l

/-! ## Rows -/

theorem nr_modifyF : ∀ (n : Nat) (a b : Row),
    Row.modifyF n ((nr ρ).row a) ((nr ρ).row b) = (nr ρ).row (Row.modifyF n a b)
  | n, [], b => by cases n <;> cases b <;> simp [Row.modifyF, nr_row_map]
  | n, (l, τ) :: rest, [] => by cases n <;> simp [Row.modifyF, nr_row_map]
  | 0, (l, τ) :: rest, (l', τ') :: rest' => by
    simp only [nr_row_cons, Row.modifyF, nr_row_map, List.map_append, List.map_cons]
  | n + 1, (l1, τ1) :: r1, (l2, τ2) :: r2 => by
    simp only [nr_row_cons, Row.modifyF]
    by_cases h1 : l1 = l2
    · simp [h1, nr_modifyF n r1 r2]
    · simp only [h1, ↓reduceIte]
      by_cases h2 : labLt l1 l2 = true
      · simp only [h2, ↓reduceIte, nr_row_cons]
        have := nr_modifyF n r1 ((l2, τ2) :: r2)
        simp only [nr_row_cons] at this
        rw [this]
      · simp only [h2, Bool.false_eq_true, ↓reduceIte, nr_row_cons]
        have := nr_modifyF n ((l1, τ1) :: r1) r2
        simp only [nr_row_cons] at this
        rw [this]

theorem nr_row_length (r : Row) : ((nr ρ).row r).length = r.length := row_length _ r

theorem nr_rowModify (a b : Row) : Row.modify ((nr ρ).row a) ((nr ρ).row b) = (nr ρ).row (Row.modify a b) := by
  simp only [Row.modify, nr_row_length]; exact nr_modifyF _ a b

theorem nr_rowLookup (r : Row) (l : Lab) : Row.lookup ((nr ρ).row r) l = (Row.lookup r l).map (nr ρ).ty := by
  simp only [Row.lookup, nr_row_map]; exact find?_mapV _ r l

theorem nr_rowLookupAll (r : Row) : ∀ ls : List Lab,
    Row.lookupAll ((nr ρ).row r) ls = (Row.lookupAll r ls).map (List.map (nr ρ).ty)
  | [] => rfl
  | l :: ls => by
    simp only [Row.lookupAll, nr_rowLookup, nr_rowLookupAll r ls]
    cases Row.lookup r l <;> cases Row.lookupAll r ls <;> rfl

theorem nr_subB (h : NR ρ) (a b : Row) : Row.subB ((nr ρ).row a) ((nr ρ).row b) = Row.subB a b := by
  simp only [Row.subB, nr_row_map, List.all_map]
  apply List.all_congr rfl
  intro f
  simp only [Function.comp_apply]
  rw [← nr_row_map, nr_rowLookup]
  cases Row.lookup b f.1 with
  | none => rfl
  | some τ =>
    simp only [Option.map_some]
    rw [Bool.eq_iff_iff]; simp only [beq_iff_eq, Option.some.injEq]
    exact ⟨nr_ty_inj h _ _, fun e => e ▸ rfl⟩

/-! ## Substitutions, instances, admissibility -/

theorem nr_bindSubst : ∀ (vs : List BVar) (ts : List Ty),
    bindSubst vs (ts.map (nr ρ).ty) = (bindSubst vs ts).map (nr ρ).subst
  | [], [] => rfl
  | .ty a :: vs, τ :: ts => by
    simp only [List.map_cons, bindSubst, nr_bindSubst vs ts]
    cases bindSubst vs ts <;> rfl
  | .row e :: vs, τ :: ts => by
    cases τ with
    | record r tl =>
      simp only [List.map_cons, nr_ty_record, bindSubst, nr_bindSubst vs ts]
      cases bindSubst vs ts <;> simp [Renaming.subst]
    | var _ => simp [bindSubst]
    | fn _ _ => simp [bindSubst]
    | con _ _ => simp [bindSubst]
  | [], _ :: _ => rfl
  | .ty _ :: _, [] => rfl
  | .row _ :: _, [] => rfl

theorem nr_admComp (h : NR ρ) : (τ : Ty) → admComp ((nr ρ).ty τ) = admComp τ
  | .var _ => rfl
  | .record _ _ => by simp [admComp]
  | .fn _ _ => rfl
  | .con [] t => by
    simp only [nr_ty_con, List.map_nil, admComp]
    rw [h.beq (by decide) t, h.beq (by decide) t, h.beq (by decide) t, h.beq (by decide) t]
  | .con [τ] t => by
    simp only [nr_ty_con, List.map_cons, List.map_nil, admComp]
    rw [h.beq (by decide) t, nr_admComp h τ]
  | .con [τ1, τ2] t => by
    simp only [nr_ty_con, List.map_cons, List.map_nil, admComp]
    rw [h.beq (by decide) t, nr_admComp h τ1, nr_admComp h τ2]
  | .con [τ1, τ2, τ3] t => by
    simp only [nr_ty_con, List.map_cons, List.map_nil, admComp]
    rw [h.beq (by decide) t, nr_admComp h τ1, nr_admComp h τ2, nr_admComp h τ3]
  | .con (_ :: _ :: _ :: _ :: _) _ => by simp [admComp]

theorem nr_tIntTy (h : NR ρ) : (nr ρ).ty tIntTy = tIntTy := by simp [tIntTy, h.fix (t0 := tInt) (by decide)]
theorem nr_tFloatTy (h : NR ρ) : (nr ρ).ty tFloatTy = tFloatTy := by simp [tFloatTy, h.fix (t0 := tFloat) (by decide)]

theorem nr_beq_fixed (h : NR ρ) (τ τ0 : Ty) (h0 : (nr ρ).ty τ0 = τ0) :
    ((nr ρ).ty τ == τ0) = (τ == τ0) := by
  conv => lhs; rw [← h0]
  exact nr_beq_ty h τ τ0

theorem nr_adm (h : NR ρ) (k : Cls) (τ : Ty) : adm k ((nr ρ).ty τ) = adm k τ := by
  cases k with
  | any => rfl
  | comp => exact nr_admComp h τ
  | num =>
    cases τ with
    | var a => rfl
    | record r tl =>
      show ((nr ρ).ty (.record r tl) == tIntTy || (nr ρ).ty (.record r tl) == tFloatTy) =
        (Ty.record r tl == tIntTy || Ty.record r tl == tFloatTy)
      rw [nr_beq_fixed h _ _ (nr_tIntTy h), nr_beq_fixed h _ _ (nr_tFloatTy h)]
    | fn a b =>
      show ((nr ρ).ty (.fn a b) == tIntTy || (nr ρ).ty (.fn a b) == tFloatTy) =
        (Ty.fn a b == tIntTy || Ty.fn a b == tFloatTy)
      rw [nr_beq_fixed h _ _ (nr_tIntTy h), nr_beq_fixed h _ _ (nr_tFloatTy h)]
    | con as t =>
      show ((nr ρ).ty (.con as t) == tIntTy || (nr ρ).ty (.con as t) == tFloatTy) =
        (Ty.con as t == tIntTy || Ty.con as t == tFloatTy)
      rw [nr_beq_fixed h _ _ (nr_tIntTy h), nr_beq_fixed h _ _ (nr_tFloatTy h)]
  | app =>
    rcases τ with _ | _ | _ | ⟨_ | ⟨τ1, _ | ⟨τ2, rest⟩⟩, t⟩
    · rfl
    · simp [adm]
    · rfl
    · simp only [nr_ty_con, List.map_nil, adm]; rw [h.beq (by decide) t]
    · simp only [nr_ty_con, List.map_cons, List.map_nil, adm]; rw [h.beq (by decide) t]
    · simp [adm]
  | capp =>
    rcases τ with _ | _ | _ | ⟨_ | ⟨τ1, _ | ⟨τ2, rest⟩⟩, t⟩
    · rfl
    · simp [adm]
    · rfl
    · simp only [nr_ty_con, List.map_nil, adm]; rw [h.beq (by decide) t]
    · simp only [nr_ty_con, List.map_cons, List.map_nil, adm]; rw [h.beq (by decide) t, nr_admComp h]
    · simp [adm]

theorem nr_respectsB (h : NR ρ) (S : Subst) : ((nr ρ).subst S).respectsB = S.respectsB := by
  simp only [Subst.respectsB, Renaming.subst, List.all_map]
  apply List.all_congr rfl; intro p
  simp [nr_adm h]

theorem nr_apply (h : NR ρ) (S : Subst) (τ : Ty) :
    ((nr ρ).subst S).apply ((nr ρ).ty τ) = (S.apply τ).map (nr ρ).ty := apply_subst_rename h.wf S τ

theorem nr_genAt (h : NR ρ) (σ : Scheme) (ts : List Ty) (τ : Ty) :
    genAt ((nr ρ).scheme σ) (ts.map (nr ρ).ty) ((nr ρ).ty τ) = genAt σ ts τ := by
  unfold genAt
  rw [nr_scheme_bound, nr_bindSubst]
  cases bindSubst σ.bound ts with
  | none => rfl
  | some S =>
    simp only [Option.map_some, nr_respectsB h, nr_scheme_body, nr_apply h]
    congr 1
    cases S.apply σ.body with
    | none => simp
    | some τ' =>
      simp only [Option.map_some, Option.some.injEq]
      exact decide_eq_decide.mpr ⟨nr_ty_inj h _ _, fun e => e ▸ rfl⟩

theorem nr_tyFcn_apply (h : NR ρ) (θ : TyFcn) (ts : List Ty) :
    ((nr ρ).tyFcn θ).apply (ts.map (nr ρ).ty) = (θ.apply ts).map (nr ρ).ty := by
  unfold TyFcn.apply
  rw [nr_tyFcn_params, nr_bindSubst]
  cases bindSubst θ.params ts with
  | none => rfl
  | some S => simp only [Option.map_some, nr_tyFcn_body]; exact nr_apply h S θ.body

/-! ## Canonical forms and closure -/

theorem nr_subst_renumber (k : Bool) : ∀ (i : Nat) (l : List BVar),
    (nr ρ).subst (renumber k i l).1 = (renumber k i l).1
  | _, [] => rfl
  | i, .ty a :: vs => by
    have ih := nr_subst_renumber k (i + 1) vs
    simp only [renumber]
    revert ih
    generalize renumber k (i + 1) vs = p
    obtain ⟨⟨st, sr⟩, bs⟩ := p
    simp only [Renaming.subst, Subst.mk.injEq, List.map_cons]
    intro ih
    simp_all
  | i, .row e :: vs => by
    have ih := nr_subst_renumber k (i + 1) vs
    simp only [renumber]
    revert ih
    generalize renumber k (i + 1) vs = p
    obtain ⟨⟨st, sr⟩, bs⟩ := p
    simp only [Renaming.subst, Subst.mk.injEq, List.map_cons]
    intro ih
    simp_all

theorem nr_canon (h : NR ρ) (σ : Scheme) : Scheme.canon ((nr ρ).scheme σ) = (nr ρ).scheme (Scheme.canon σ) :=
  canon_rename h.wf σ

theorem nr_tyFcn_canon (h : NR ρ) (θ : TyFcn) : TyFcn.canon ((nr ρ).tyFcn θ) = (nr ρ).tyFcn (TyFcn.canon θ) := by
  simp only [TyFcn.canon, nr_tyFcn_params, nr_tyFcn_body]
  have e := nr_apply h (renumber false 0 (dedupL θ.params)).1 θ.body
  rw [nr_subst_renumber] at e
  rw [e]
  simp only [Renaming.tyFcn, nr_bvar_fun, TyFcn.mk.injEq]
  refine ⟨by simp, ?_⟩
  cases Subst.apply (renumber false 0 (dedupL θ.params)).1 θ.body <;> rfl

theorem nr_closScheme (h : NR ρ) (A : List BVar) (σ : Scheme) :
    closScheme A ((nr ρ).scheme σ) = (nr ρ).scheme (closScheme A σ) := by
  unfold closScheme
  rw [← nr_canon h]
  simp [Renaming.scheme, Scheme.tyvars]

theorem nr_closVE (h : NR ρ) (A : List BVar) (VE : ValEnv) :
    closVE A ((nr ρ).valEnv VE) = (nr ρ).valEnv (closVE A VE) := by
  simp [closVE, FMap.mapV, Renaming.valEnv, nr_closScheme h]

theorem nr_closGroup (h : NR ρ) (A : List BVar) (VE : ValEnv) :
    closGroup A ((nr ρ).valEnv VE) = (nr ρ).valEnv (closGroup A VE) :=
  closGroup_rename h.wf (D := fun _ => True) (by simp) VE (by simp)

theorem nr_annScheme (h : NR ρ) (U : List BVar) (τ : Ty) :
    annScheme U ((nr ρ).ty τ) = (nr ρ).scheme (annScheme U τ) := by
  unfold annScheme
  rw [← nr_canon h]
  simp [Renaming.scheme]

/-! ## Contexts -/

theorem nr_lookupVal (C : Ctx) (lv : LongId) :
    ((nr ρ).ctx C).lookupVal lv = (C.lookupVal lv).map fun b => ((nr ρ).scheme b.1, b.2) := by
  simp only [Ctx.lookupVal, Env.lookupVal, nr_ctx_E, Renaming.env]
  split
  · exact nr_valEnv_find _ _
  · rw [find?_mapV]
    cases FMap.find? C.E.QE _ with
    | none => rfl
    | some I => simp only [Option.map_some, Option.bind_some, Renaming.iEnv]; exact nr_valEnv_find _ _

theorem nr_lookupTy (C : Ctx) (lc : LongId) :
    ((nr ρ).ctx C).lookupTy lc = (C.lookupTy lc).map fun s => ((nr ρ).tyFcn s.1, (nr ρ).valEnv s.2) := by
  simp only [Ctx.lookupTy, Env.lookupTy, nr_ctx_E, Renaming.env]
  split
  · exact nr_tyEnv_find _ _
  · rw [find?_mapV]
    cases FMap.find? C.E.QE _ with
    | none => rfl
    | some I => simp only [Option.map_some, Option.bind_some, Renaming.iEnv]; exact nr_tyEnv_find _ _

theorem nr_plusVE (C : Ctx) (VE : ValEnv) : ((nr ρ).ctx C).plusVE ((nr ρ).valEnv VE) = (nr ρ).ctx (C.plusVE VE) := by
  simp [Ctx.plusVE, Renaming.ctx, Renaming.env, Renaming.valEnv]

theorem nr_plusU (C : Ctx) (U : List BVar) : ((nr ρ).ctx C).plusU U = (nr ρ).ctx (C.plusU U) := by
  simp [Ctx.plusU, Renaming.ctx]

theorem nr_env_plus (E E' : Env) : ((nr ρ).env E).plus ((nr ρ).env E') = (nr ρ).env (E.plus E') := by
  simp only [Env.plus, Renaming.env, nr_tyEnv_modify, nr_valEnv_modify]
  rw [modify_mapV]

theorem nr_oplusTE (h : NR ρ) (C : Ctx) (TE : TyEnv) :
    ((nr ρ).ctx C).oplusTE ((nr ρ).tyEnv TE) = (nr ρ).ctx (C.oplusTE TE) := by
  simp only [Ctx.oplusTE, Renaming.ctx, Renaming.env, nr_tyEnv_tynames, unionL_map_inj _ h.inj, nr_tyEnv_modify]

theorem nr_oplusE (h : NR ρ) (C : Ctx) (E : Env) :
    ((nr ρ).ctx C).oplusE ((nr ρ).env E) = (nr ρ).ctx (C.oplusE E) := by
  simp only [Ctx.oplusE, nr_ctx_T, nr_env_tynames, unionL_map_inj _ h.inj, nr_ctx_E, nr_env_plus]
  simp [Renaming.ctx]

/-! ## Type expressions -/

theorem nr_tupleTy (h : NR ρ) (τ1 τ2 : Ty) (τ3 : Option Ty) :
    tupleTy ((nr ρ).ty τ1) ((nr ρ).ty τ2) (τ3.map (nr ρ).ty) = (nr ρ).ty (tupleTy τ1 τ2 τ3) := by
  cases τ3 <;> simp [tupleTy, h.fix (t0 := tTuple2) (by decide), h.fix (t0 := tTuple3) (by decide)]

theorem nr_tUnitTy (h : NR ρ) : (nr ρ).ty tUnitTy = tUnitTy := by simp [tUnitTy, h.fix (t0 := tUnit) (by decide)]
theorem nr_tStringTy (h : NR ρ) : (nr ρ).ty tStringTy = tStringTy := by simp [tStringTy, h.fix (t0 := tString) (by decide)]
theorem nr_tCharTy (h : NR ρ) : (nr ρ).ty tCharTy = tCharTy := by simp [tCharTy, h.fix (t0 := tChar) (by decide)]
theorem nr_listTy (h : NR ρ) (τ : Ty) : (nr ρ).ty (listTy τ) = listTy ((nr ρ).ty τ) := by
  simp [listTy, h.fix (t0 := tList) (by decide)]

mutual
theorem nr_elabTy (h : NR ρ) (C : Ctx) : (t : BTy) → elabTy ((nr ρ).ctx C) t = (elabTy C t).map (nr ρ).ty
  | .tyvar a => by
    simp only [elabTy, nr_ctx_U]
    split
    · rfl
    · split <;> rfl
  | .record row => by
    simp only [elabTy, nr_elabTyRowOpt h C row]
    cases elabTyRowOpt C row <;> rfl
  | .openRecord r row => by
    simp only [elabTy, nr_ctx_U, nr_elabTyRow h C row]
    split
    · cases elabTyRow C row <;> rfl
    · rfl
  | .unit => by simp [elabTy, nr_tUnitTy h]
  | .tuple t1 t2 t3 => by
    simp only [elabTy, nr_elabTy h C t1, nr_elabTy h C t2, nr_elabTyOpt h C t3]
    cases elabTy C t1 <;> cases elabTy C t2 <;> cases elabTyOpt C t3 <;> simp [nr_tupleTy h]
  | .con c args => by
    simp only [elabTy, nr_lookupTy, nr_elabTyList h C args]
    cases C.lookupTy c with
    | none => rfl
    | some s =>
      cases elabTyList C args with
      | none => rfl
      | some τs => exact nr_tyFcn_apply h s.1 τs
  | .fn t1 t2 => by
    simp only [elabTy, nr_elabTy h C t1, nr_elabTy h C t2]
    cases elabTy C t1 <;> cases elabTy C t2 <;> rfl
  | .paren t => by simp only [elabTy]; exact nr_elabTy h C t
theorem nr_elabTyRow (h : NR ρ) (C : Ctx) : (r : BTyRow) → elabTyRow ((nr ρ).ctx C) r = (elabTyRow C r).map (nr ρ).row
  | .field l t rest => by
    simp only [elabTyRow, nr_elabTy h C t, nr_elabTyRowOpt h C rest]
    cases elabTy C t <;> cases elabTyRowOpt C rest <;> simp
    rw [← nr_rowModify]; rfl
theorem nr_elabTyRowOpt (h : NR ρ) (C : Ctx) : (r : Option BTyRow) →
    elabTyRowOpt ((nr ρ).ctx C) r = (elabTyRowOpt C r).map (nr ρ).row
  | none => rfl
  | some r => by simp only [elabTyRowOpt]; exact nr_elabTyRow h C r
theorem nr_elabTyOpt (h : NR ρ) (C : Ctx) : (t : Option BTy) →
    elabTyOpt ((nr ρ).ctx C) t = (elabTyOpt C t).map (Option.map (nr ρ).ty)
  | none => rfl
  | some t => by
    simp only [elabTyOpt, nr_elabTy h C t]
    cases elabTy C t <;> rfl
theorem nr_elabTyList (h : NR ρ) (C : Ctx) : (ts : List BTy) →
    elabTyList ((nr ρ).ctx C) ts = (elabTyList C ts).map (List.map (nr ρ).ty)
  | [] => rfl
  | t :: ts => by
    simp only [elabTyList, nr_elabTy h C t, nr_elabTyList h C ts]
    cases elabTy C t <;> cases elabTyList C ts <;> rfl
end

end

end StandardElm.Stat
