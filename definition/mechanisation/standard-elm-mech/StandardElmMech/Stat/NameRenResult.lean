/-
  A Standard Definition of Elm? Mechanisation: the result of a module in a basis, its nodes and its
  generated names commute with a renaming of type names (plan step 10, transport across bases,
  fourth layer).
-/
import StandardElmMech.Stat.NameRenMod

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Src (BTy BTyRow BItem BExpList BImport BConBind BDatBind BTypBind)

section
variable {ρ : List (TyName × TyName)}

/-! ## Exposing -/

theorem nr_ofStatusV (VE : ValEnv) : ValEnv.ofStatusV ((nr ρ).valEnv VE) = (nr ρ).valEnv (ValEnv.ofStatusV VE) := by
  simp only [ValEnv.ofStatusV, Renaming.valEnv, List.filter_map]
  rfl

theorem nr_iEnv_plus (I I' : IEnv) : ((nr ρ).iEnv I).plus ((nr ρ).iEnv I') = (nr ρ).iEnv (I.plus I') := by
  simp only [IEnv.plus, Renaming.iEnv, nr_tyEnv_modify, nr_valEnv_modify]

theorem nr_exposeItem (E : Env) (it : BItem) :
    exposeItem ((nr ρ).env E) it = (exposeItem E it).map (nr ρ).iEnv := by
  cases it with
  | var x =>
    simp only [exposeItem, Renaming.env, nr_valEnv_find]
    cases FMap.find? E.VE x <;> rfl
  | op _ => rfl
  | ty c =>
    simp only [exposeItem, Renaming.env, nr_tyEnv_find]
    cases FMap.find? E.TE c with
    | none => rfl
    | some s => simp [Renaming.iEnv, Renaming.tyEnv, nr_ofStatusV]
  | tyAll c =>
    simp only [exposeItem, Renaming.env, nr_tyEnv_find]
    cases FMap.find? E.TE c with
    | none => rfl
    | some s => simp [Renaming.iEnv, Renaming.tyEnv]

theorem nr_exposeItems (E : Env) : (is : List BItem) →
    exposeItems ((nr ρ).env E) is = (exposeItems E is).map (nr ρ).iEnv
  | [] => rfl
  | it :: rest => by
    simp only [exposeItems, nr_exposeItem, nr_exposeItems E rest]
    cases exposeItem E it <;> cases exposeItems E rest <;> simp [nr_iEnv_plus]

theorem nr_expose (E : Env) (el : BExpList) : expose ((nr ρ).env E) el = (expose E el).map (nr ρ).iEnv := by
  cases el with
  | all => rfl
  | items is => exact nr_exposeItems E is

/-! ## Imports -/

theorem nr_basis_ME_find (B : SBasis) (m : ModId) :
    FMap.find? ((nr ρ).basis B).ME m = (FMap.find? B.ME m).map (nr ρ).iEnv :=
  find?_mapV (fun I => (nr ρ).iEnv I) B.ME m

theorem nr_iEnv_dom (I : IEnv) : ((nr ρ).iEnv I).dom = I.dom := by simp [IEnv.dom, Renaming.iEnv]

theorem nr_elabItem (m : ModId) (I : IEnv) (it : BItem) : elabItem (m, (nr ρ).iEnv I) it = elabItem (m, I) it := by
  cases it with
  | var x => simp [elabItem, Renaming.iEnv]
  | op _ => rfl
  | ty c =>
    simp only [elabItem, Renaming.iEnv, nr_tyEnv_find]
    cases FMap.find? I.TE c with
    | none => rfl
    | some s => simp [nr_ofStatusV]
  | tyAll c =>
    simp only [elabItem, Renaming.iEnv, nr_tyEnv_find]
    cases FMap.find? I.TE c with
    | none => rfl
    | some s =>
      simp only [Option.map_some, nr_valEnv_keys, nr_valEnv_find]
      congr 2
      apply List.any_congr rfl
      intro k
      cases FMap.find? s.2 k <;> rfl

theorem nr_elabItems (m : ModId) (I : IEnv) : (is : List BItem) →
    elabItems (m, (nr ρ).iEnv I) is = elabItems (m, I) is
  | [] => rfl
  | it :: rest => by simp only [elabItems, nr_elabItem, nr_elabItems m I rest]

theorem nr_elabExpList (m : ModId) (I : IEnv) (el : BExpList) : elabExpList (m, (nr ρ).iEnv I) el = elabExpList (m, I) el := by
  cases el with
  | all => simp [elabExpList, nr_iEnv_dom]
  | items is => exact nr_elabItems m I is

theorem nr_elabImports (B : SBasis) : (is : List BImport) → (π : ProvMap) →
    elabImports ((nr ρ).basis B) π is = elabImports B π is
  | [], _ => rfl
  | i :: is, π => by
    simp only [elabImports, nr_basis_ME_find]
    cases FMap.find? B.ME i.mod with
    | none => rfl
    | some I =>
      simp only [Option.map_some, qualified, nr_iEnv_dom]
      cases i.exposing with
      | none => exact nr_elabImports B is _
      | some el =>
        simp only [nr_elabExpList]
        cases elabExpList (i.mod, I) el with
        | none => rfl
        | some p => exact nr_elabImports B is _

/-- The names of the initial environment E0 are those of T0. -/
theorem nr_E0TE (h : NR ρ) : (nr ρ).tyEnv E0.TE = E0.TE := by
  have := h.fix (t0 := tList) (by decide)
  simp [this, E0, Renaming.tyEnv, Renaming.valEnv, Renaming.tyFcn, Renaming.scheme, h.fix (t0 := tList) (by decide),
    TyName.toFcn]
  all_goals exact this

theorem nr_E0VE (h : NR ρ) : (nr ρ).valEnv E0.VE = E0.VE := by
  have := h.fix (t0 := tList) (by decide)
  simp [this, E0, Renaming.valEnv, Renaming.scheme]

theorem nr_teFind (h : NR ρ) (ME : ModEnv) (m : ModId) (c : String) :
    teFind (ME.map fun p => (p.1, (nr ρ).iEnv p.2)) m c = (teFind ME m c).map fun s => ((nr ρ).tyFcn s.1, (nr ρ).valEnv s.2) := by
  unfold teFind
  rw [find?_mapV (fun I => (nr ρ).iEnv I)]
  have e1 : (((FMap.find? ME m).map (nr ρ).iEnv).map (·.TE)).getD [] = (nr ρ).tyEnv (((FMap.find? ME m).map (·.TE)).getD []) := by
    cases FMap.find? ME m <;> rfl
  rw [e1, nr_tyEnv_find]
  cases FMap.find? (((FMap.find? ME m).map (·.TE)).getD []) c with
  | some _ => rfl
  | none =>
    simp only [Option.map_none, Option.none_or]
    split
    · have e := nr_tyEnv_find (ρ := ρ) E0.TE c
      rw [nr_E0TE h] at e
      rw [← e]
    · rfl

theorem nr_veFind (h : NR ρ) (ME : ModEnv) (m : ModId) (x : String) :
    veFind (ME.map fun p => (p.1, (nr ρ).iEnv p.2)) m x = (veFind ME m x).map fun b => ((nr ρ).scheme b.1, b.2) := by
  unfold veFind
  rw [find?_mapV (fun I => (nr ρ).iEnv I)]
  have e1 : (((FMap.find? ME m).map (nr ρ).iEnv).map (·.VE)).getD [] = (nr ρ).valEnv (((FMap.find? ME m).map (·.VE)).getD []) := by
    cases FMap.find? ME m <;> rfl
  rw [e1, nr_valEnv_find]
  cases FMap.find? (((FMap.find? ME m).map (·.VE)).getD []) x with
  | some _ => rfl
  | none =>
    simp only [Option.map_none, Option.none_or]
    split
    · have e := nr_valEnv_find (ρ := ρ) E0.VE x
      rw [nr_E0VE h] at e
      rw [← e]
    · rfl

theorem nr_addQ (q : ModId) (f g : IEnv → IEnv) (hfg : ∀ I, g ((nr ρ).iEnv I) = (nr ρ).iEnv (f I)) :
    ∀ QE : FMap ModId IEnv, addQ q g (QE.map fun p => (p.1, (nr ρ).iEnv p.2)) = (addQ q f QE).map fun p => (p.1, (nr ρ).iEnv p.2)
  | [] => by
    show [(q, g IEnv.empty)] = [(q, (nr ρ).iEnv (f IEnv.empty))]
    rw [← hfg]; rfl
  | (q', I) :: rest => by
    simp only [List.map_cons, addQ]
    split
    · simp [hfg]
    · simp [nr_addQ q f g hfg rest]

theorem nr_envStep (h : NR ρ) (ME : ModEnv) (p : SmLongId × List ModId) (E : Env) :
    envStep (ME.map fun p => (p.1, (nr ρ).iEnv p.2)) p ((nr ρ).env E) = (nr ρ).env (envStep ME p E) := by
  rcases p with ⟨⟨_ | q, _ | _⟩, _ | ⟨mid, _ | _⟩⟩ <;> simp only [envStep]
  all_goals first
    | rfl
    | (rw [nr_teFind h]; cases teFind ME _ _ <;> simp [Renaming.env, Renaming.tyEnv])
    | (rw [nr_veFind h]; cases veFind ME _ _ <;> simp [Renaming.env, Renaming.valEnv])
    | (simp only [Renaming.env]; rw [nr_addQ q id id (fun _ => rfl)])
  all_goals (apply nr_addQ; intro; rfl)

theorem nr_envOf (h : NR ρ) (ME : ModEnv) : (π : ProvMap) →
    envOf (ME.map fun p => (p.1, (nr ρ).iEnv p.2)) π = (nr ρ).env (envOf ME π)
  | [] => rfl
  | p :: π => by
    simp only [envOf, List.foldr_cons] at *
    have := nr_envOf h ME π
    simp only [envOf] at this
    rw [this, nr_envStep h]

theorem nr_modCtx (h : NR ρ) (B : SBasis) (π : ProvMap) : modCtx ((nr ρ).basis B) π = (nr ρ).ctx (modCtx B π) := by
  simp only [modCtx, Renaming.basis, nr_envOf h]
  simp [Renaming.ctx]

theorem nr_importCtx (h : NR ρ) (B : SBasis) (imps : List BImport) :
    importCtx ((nr ρ).basis B) imps = (importCtx B imps).map (nr ρ).ctx := by
  simp only [importCtx, nr_elabImports]
  cases elabImports B π0 (defaultImports ++ imps) <;> simp [nr_modCtx h]

@[simp] theorem nr_rename_header (a : AModule) : (a.rename (nr ρ)).header = a.header := rfl
@[simp] theorem nr_rename_imports (a : AModule) : (a.rename (nr ρ)).imports = a.imports := rfl
@[simp] theorem nr_rename_body (a : AModule) : (a.rename (nr ρ)).body = a.body.map (nr ρ).topDec := rfl

theorem nr_basis_keys (B : SBasis) : ((nr ρ).basis B).ME.keys = B.ME.keys := by
  simp [Renaming.basis, FMap.keys]

theorem nr_resultIn (h : NR ρ) (B : SBasis) (C : Ctx) (a : AModule) :
    (a.rename (nr ρ)).resultIn ((nr ρ).basis B) ((nr ρ).ctx C) =
      (a.resultIn B C).map fun p => ((nr ρ).basis p.1, (nr ρ).env p.2) := by
  unfold AModule.resultIn
  rw [nr_rename_body, nr_checkTopDecOpt h]
  cases checkTopDecOpt C a.body with
  | none => rfl
  | some p =>
    obtain ⟨E, PE⟩ := p
    simp only [Option.map_some, nr_rename_header, nr_expose]
    cases expose E a.header.exposing with
    | none => rfl
    | some I =>
      simp only [Option.map_some, nr_basis_keys]
      split
      · rfl
      · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
        simp only [Renaming.basis, nr_env_tynames, dedupL_map_inj _ h.inj, diffL_map_inj _ h.inj, List.map_cons,
          List.map_nil]

theorem nr_result (h : NR ρ) (B : SBasis) (a : AModule) :
    (a.rename (nr ρ)).result ((nr ρ).basis B) = (a.result B).map fun p => ((nr ρ).basis p.1, (nr ρ).env p.2) := by
  unfold AModule.result
  rw [nr_rename_imports, nr_importCtx h]
  cases importCtx B a.imports with
  | none => rfl
  | some C => exact nr_resultIn h B C a

theorem nr_checkModule (h : NR ρ) (B : SBasis) (a : AModule) :
    checkModule ((nr ρ).basis B) (a.rename (nr ρ)) = checkModule B a := by
  simp only [checkModule, nr_result h]
  cases a.result B <;> rfl

/-! ## Nodes -/

mutual
theorem renameNames_nr : (τ : Ty) → Ty.renameNames ρ τ = (nr ρ).ty τ
  | .var _ => rfl
  | .record r tl => by simp only [Ty.renameNames, nr_ty_record, renameRow_nr r]
  | .fn a b => by simp only [Ty.renameNames, nr_ty_fn, renameNames_nr a, renameNames_nr b]
  | .con as t => by
    simp only [Ty.renameNames, renameName_eq, renameList_nr as, nr_tys, nr_ty_con]
    rfl
theorem renameRow_nr : (r : Row) → Ty.renameRow ρ r = (nr ρ).row r
  | [] => rfl
  | (l, τ) :: rest => by simp only [Ty.renameRow, renameNames_nr τ, renameRow_nr rest, nr_row_cons]
theorem renameList_nr : (l : List Ty) → Ty.renameList ρ l = (nr ρ).tys l
  | [] => rfl
  | τ :: rest => by simp only [Ty.renameList, renameNames_nr τ, renameList_nr rest, Renaming.tys]
end

/-- A node renamed. -/
theorem node_renameNames (n : Node) :
    n.renameNames ρ = ⟨n.path, n.U, n.tys.map (nr ρ).ty, n.schemes.map (nr ρ).scheme⟩ := by
  simp only [Node.renameNames]
  congr 1
  · exact List.map_congr_left fun τ _ => renameNames_nr τ
  · exact List.map_congr_left fun σ _ => by simp [Renaming.scheme, renameNames_nr]

@[simp] theorem nr_veSchemes (VE : ValEnv) : veSchemes ((nr ρ).valEnv VE) = (veSchemes VE).map (nr ρ).scheme := by
  simp [veSchemes, Renaming.valEnv]

/-- `ns.map (Node.renameNames ρ)`, the nodes renamed. -/
abbrev nrNodes (ρ : List (TyName × TyName)) (ns : List Node) : List Node := ns.map (Node.renameNames ρ)

theorem nrNode_mk (p : List Nat) (U : List BVar) (ts : List Ty) (ss : List Scheme) :
    Node.renameNames ρ ⟨p, U, ts, ss⟩ = ⟨p, U, ts.map (nr ρ).ty, ss.map (nr ρ).scheme⟩ := node_renameNames _

mutual
theorem nr_nodesAtPat (h : NR ρ) (U : List BVar) (path : List Nat) : (p : AAtPat) →
    nodesAtPat U path ((nr ρ).atPat p) = nrNodes ρ (nodesAtPat U path p)
  | .wild τ | .scon _ τ | .var _ τ | .nil τ => by
    simp [Renaming.atPat, nodesAtPat, nrNode_mk, AAtPat.ty, AAtPat.ve, Renaming.valEnv, mono, Renaming.scheme]
  | .con lc inst τ => by
    simp [Renaming.atPat, nodesAtPat, nrNode_mk, AAtPat.ty, AAtPat.ve, nr_tys]
  | .unit => by simp [Renaming.atPat, nodesAtPat, nrNode_mk, AAtPat.ty, AAtPat.ve, nr_tUnitTy h]
  | .tuple p1 p2 p3 => by
    have e1 := nr_atPat_ty h (.tuple p1 p2 p3)
    have e2 := nr_atPat_ve h (.tuple p1 p2 p3)
    simp only [Renaming.atPat, AAtPat.ty] at e1 e2
    simp only [Renaming.atPat, nodesAtPat, List.map_append, List.map_cons, List.map_nil, nrNode_mk,
      nr_nodesPat h, nr_nodesPatOpt h, e2, nr_veSchemes, nr_pat_ty h, nr_patOpt_ty h, nr_tupleTy h]
  | .record row τ => by
    simp only [Renaming.atPat, nodesAtPat, List.map_append, List.map_cons, List.map_nil, nrNode_mk,
      nr_nodesPatRowOpt h, nr_patRowOpt_ve h, nr_veSchemes]
  | .paren p => by
    simp only [Renaming.atPat, nodesAtPat, List.map_append, List.map_cons, List.map_nil, nrNode_mk,
      nr_nodesPat h, nr_pat_ty h, nr_pat_ve h, nr_veSchemes]
theorem nr_nodesPatRow (h : NR ρ) (U : List BVar) (path : List Nat) : (r : APatRow) →
    nodesPatRow U path ((nr ρ).patRow r) = nrNodes ρ (nodesPatRow U path r)
  | .field l τ rest => by
    have e1 := nr_patRow_row (ρ := ρ) (.field l τ rest)
    simp only [Renaming.patRow] at e1
    simp only [Renaming.patRow, nodesPatRow, List.map_append, List.map_cons, List.map_nil, nrNode_mk,
      nr_nodesPatRowOpt h, e1, nr_row_map, List.map_map]
    rfl
theorem nr_nodesPatRowOpt (h : NR ρ) (U : List BVar) (path : List Nat) : (r : Option APatRow) →
    nodesPatRowOpt U path ((nr ρ).patRowOpt r) = nrNodes ρ (nodesPatRowOpt U path r)
  | none => rfl
  | some r => by simp only [Renaming.patRowOpt, nodesPatRowOpt]; exact nr_nodesPatRow h U path r
theorem nr_nodesPat (h : NR ρ) (U : List BVar) (path : List Nat) : (p : APat) →
    nodesPat U path ((nr ρ).pat p) = nrNodes ρ (nodesPat U path p)
  | .atpat a => by
    simp only [Renaming.pat, nodesPat, List.map_append, List.map_cons, List.map_nil, nrNode_mk,
      nr_nodesAtPat h, nr_atPat_ty h, nr_atPat_ve h, nr_veSchemes]
  | .con lc inst args τ => by
    have e2 := nr_pat_ve h (.con lc inst args τ)
    simp only [Renaming.pat, nr_tys] at e2
    simp only [Renaming.pat, nodesPat, List.map_append, List.map_cons, List.map_nil, nrNode_mk,
      nr_nodesAtPats h, e2, nr_veSchemes, nr_tys]
  | .cons p1 p2 => by
    have e2 := nr_pat_ve h (.cons p1 p2)
    simp only [Renaming.pat] at e2
    simp only [Renaming.pat, nodesPat, List.map_append, List.map_cons, List.map_nil, nrNode_mk,
      nr_nodesPat h, e2, nr_veSchemes, nr_pat_ty h, nr_listTy h]
  | .as p x => by
    have e2 := nr_pat_ve h (.as p x)
    simp only [Renaming.pat] at e2
    simp only [Renaming.pat, nodesPat, List.map_append, List.map_cons, List.map_nil, nrNode_mk,
      nr_nodesPat h, e2, nr_veSchemes, nr_pat_ty h]
theorem nr_nodesPatOpt (h : NR ρ) (U : List BVar) (path : List Nat) : (p : Option APat) →
    nodesPatOpt U path ((nr ρ).patOpt p) = nrNodes ρ (nodesPatOpt U path p)
  | none => rfl
  | some p => by simp only [Renaming.patOpt, nodesPatOpt]; exact nr_nodesPat h U path p
theorem nr_nodesAtPats (h : NR ρ) (U : List BVar) (path : List Nat) : (i : Nat) → (ps : List AAtPat) →
    nodesAtPats U path i ((nr ρ).atPats ps) = nrNodes ρ (nodesAtPats U path i ps)
  | _, [] => rfl
  | i, p :: ps => by
    simp only [Renaming.atPats, nodesAtPats, List.map_append, nr_nodesAtPat h, nr_nodesAtPats h U path (i + 1) ps]
end

theorem nr_nodesE_head (C : Ctx) (path : List Nat) (τ : Ty) (ts : List Ty) :
    Node.renameNames ρ ⟨path, C.U, τ :: ts, []⟩ = ⟨path, ((nr ρ).ctx C).U, (nr ρ).ty τ :: ts.map (nr ρ).ty, []⟩ := by
  rw [nrNode_mk]; simp

mutual
theorem nr_nodesAtExp (h : NR ρ) (C : Ctx) (path : List Nat) : (a : AAtExp) →
    nodesAtExp ((nr ρ).ctx C) path ((nr ρ).atExp a) = nrNodes ρ (nodesAtExp C path a)
  | .scon sc τ => by
    simp [Renaming.atExp, nodesAtExp, nrNode_mk, nr_litInst]
  | .var lv inst τ => by simp [Renaming.atExp, nodesAtExp, nrNode_mk, nr_tys]
  | .con lc inst τ => by simp [Renaming.atExp, nodesAtExp, nrNode_mk, nr_tys]
  | .op o inst τ => by simp [Renaming.atExp, nodesAtExp, nrNode_mk, nr_tys]
  | .unit => by simp [Renaming.atExp, nodesAtExp, nrNode_mk, nr_tUnitTy h]
  | .nil τ => by simp [Renaming.atExp, nodesAtExp, nrNode_mk]
  | .tuple e1 e2 e3 => by
    have e := nr_atExp_ty h (.tuple e1 e2 e3)
    simp only [Renaming.atExp] at e
    simp only [Renaming.atExp, nodesAtExp, List.map_append, List.map_cons, List.map_nil, nrNode_mk, nr_ctx_U,
      e, nr_nodesExp h, nr_nodesExpOpt h]
  | .record row => by
    have e := nr_atExp_ty h (.record row)
    simp only [Renaming.atExp] at e
    simp only [Renaming.atExp, nodesAtExp, List.map_append, List.map_cons, List.map_nil, nrNode_mk, nr_ctx_U,
      e, nr_nodesExpRowOpt h]
  | .update x inst τ row => by
    simp only [Renaming.atExp, nodesAtExp, List.map_append, List.map_cons, List.map_nil, nrNode_mk, nr_ctx_U,
      nr_nodesExpRow h, nr_tys]
  | .letE d e => by
    simp only [Renaming.atExp, nodesAtExp, List.map_append, List.map_cons, List.map_nil, nrNode_mk, nr_ctx_U,
      nr_exp_ty h, nr_nodesDec h, nr_dec_result h, nr_plusVE, nr_nodesExp h]
  | .paren e => by
    simp only [Renaming.atExp, nodesAtExp, List.map_append, List.map_cons, List.map_nil, nrNode_mk, nr_ctx_U,
      nr_exp_ty h, nr_nodesExp h]
theorem nr_nodesExpRow (h : NR ρ) (C : Ctx) (path : List Nat) : (r : AExpRow) →
    nodesExpRow ((nr ρ).ctx C) path ((nr ρ).expRow r) = nrNodes ρ (nodesExpRow C path r)
  | .field l e rest => by
    have e1 := nr_expRow_row h (.field l e rest)
    simp only [Renaming.expRow] at e1
    simp only [Renaming.expRow, nodesExpRow, List.map_append, List.map_cons, List.map_nil, nrNode_mk, nr_ctx_U,
      e1, nr_nodesExp h, nr_nodesExpRowOpt h, nr_row_map, List.map_map]
    rfl
theorem nr_nodesExpRowOpt (h : NR ρ) (C : Ctx) (path : List Nat) : (r : Option AExpRow) →
    nodesExpRowOpt ((nr ρ).ctx C) path ((nr ρ).expRowOpt r) = nrNodes ρ (nodesExpRowOpt C path r)
  | none => rfl
  | some r => by simp only [Renaming.expRowOpt, nodesExpRowOpt]; exact nr_nodesExpRow h C path r
theorem nr_nodesExp (h : NR ρ) (C : Ctx) (path : List Nat) : (e : AExp) →
    nodesExp ((nr ρ).ctx C) path ((nr ρ).exp e) = nrNodes ρ (nodesExp C path e)
  | .atexp a => by
    simp only [Renaming.exp, nodesExp, List.map_append, List.map_cons, List.map_nil, nrNode_mk, nr_ctx_U,
      nr_atExp_ty h, nr_nodesAtExp h]
  | .app e a => by
    have e1 := nr_exp_ty h (.app e a)
    simp only [Renaming.exp] at e1
    simp only [Renaming.exp, nodesExp, List.map_append, List.map_cons, List.map_nil, nrNode_mk, nr_ctx_U,
      e1, nr_nodesExp h, nr_nodesAtExp h]
  | .lam p e => by
    have e1 := nr_exp_ty h (.lam p e)
    simp only [Renaming.exp] at e1
    simp only [Renaming.exp, nodesExp, List.map_append, List.map_cons, List.map_nil, nrNode_mk, nr_ctx_U,
      e1, nr_nodesAtPat h, nr_atPat_ve h, nr_plusVE, nr_nodesExp h]
  | .caseE e m => by
    have e1 := nr_exp_ty h (.caseE e m)
    simp only [Renaming.exp] at e1
    simp only [Renaming.exp, nodesExp, List.map_append, List.map_cons, List.map_nil, nrNode_mk, nr_ctx_U,
      e1, nr_nodesExp h, nr_nodesMatch h]
theorem nr_nodesExpOpt (h : NR ρ) (C : Ctx) (path : List Nat) : (e : Option AExp) →
    nodesExpOpt ((nr ρ).ctx C) path ((nr ρ).expOpt e) = nrNodes ρ (nodesExpOpt C path e)
  | none => rfl
  | some e => by simp only [Renaming.expOpt, nodesExpOpt]; exact nr_nodesExp h C path e
theorem nr_nodesMatch (h : NR ρ) (C : Ctx) (path : List Nat) : (m : AMatch) →
    nodesMatch ((nr ρ).ctx C) path ((nr ρ).match_ m) = nrNodes ρ (nodesMatch C path m)
  | .mk (.mk p e) rest => by
    have e1 := nr_mrule_ty h (.mk p e)
    simp only [Renaming.mrule] at e1
    simp only [Renaming.match_, Renaming.mrule, nodesMatch, List.map_append, List.map_cons, List.map_nil, nrNode_mk,
      nr_ctx_U, e1, nr_nodesPat h, nr_pat_ve h, nr_plusVE, nr_nodesExp h, nr_nodesMatchOpt h]
theorem nr_nodesMatchOpt (h : NR ρ) (C : Ctx) (path : List Nat) : (m : Option AMatch) →
    nodesMatchOpt ((nr ρ).ctx C) path ((nr ρ).matchOpt m) = nrNodes ρ (nodesMatchOpt C path m)
  | none => rfl
  | some m => by simp only [Renaming.matchOpt, nodesMatchOpt]; exact nr_nodesMatch h C path m
theorem nr_nodesDec (h : NR ρ) (C : Ctx) (path : List Nat) : (d : ADec) →
    nodesDec ((nr ρ).ctx C) path ((nr ρ).dec d) = nrNodes ρ (nodesDec C path d)
  | .val VE vb => by
    simp only [Renaming.dec, nodesDec, List.map_append, List.map_cons, List.map_nil, nrNode_mk, nr_ctx_U,
      nr_ctx_tyvars h, nr_closGroup h, nr_veSchemes, nr_plusVE, nr_nodesValBind h]
theorem nr_nodesValBind (h : NR ρ) (C : Ctx) (path : List Nat) : (vb : AValBind) →
    nodesValBind ((nr ρ).ctx C) path ((nr ρ).valBind vb) = nrNodes ρ (nodesValBind C path vb)
  | .var x ann τ e rest => by
    have e1 := nr_valBind_ve h (.var x ann τ e rest)
    simp only [Renaming.valBind] at e1
    simp only [Renaming.valBind, nodesValBind, List.map_append, List.map_cons, List.map_nil, nrNode_mk, nr_ctx_U,
      e1, nr_veSchemes, nr_ann_annU, nr_plusU, nr_nodesExp h, nr_nodesValBindOpt h]
  | .pat p e => by
    simp only [Renaming.valBind, nodesValBind, List.map_append, List.map_cons, List.map_nil, nrNode_mk, nr_ctx_U,
      nr_atPat_ty h, nr_atPat_ve h, nr_veSchemes, nr_nodesAtPat h, nr_nodesExp h]
theorem nr_nodesValBindOpt (h : NR ρ) (C : Ctx) (path : List Nat) : (vb : Option AValBind) →
    nodesValBindOpt ((nr ρ).ctx C) path ((nr ρ).valBindOpt vb) = nrNodes ρ (nodesValBindOpt C path vb)
  | none => rfl
  | some vb => by simp only [Renaming.valBindOpt, nodesValBindOpt]; exact nr_nodesValBind h C path vb
end

theorem nr_nodesTopDec (h : NR ρ) : (d : ATopDec) → (C : Ctx) → (path : List Nat) →
    nodesTopDec ((nr ρ).ctx C) path ((nr ρ).topDec d) = nrNodes ρ (nodesTopDec C path d)
  | .value VE vb, C, path => by
    simp only [Renaming.topDec, nodesTopDec, List.map_append, List.map_cons, List.map_nil, nrNode_mk, nr_ctx_U,
      nr_ctx_tyvars h, nr_closGroup h, nr_veSchemes, nr_plusVE, nr_nodesValBind h]
  | .types TE VE db tbs, C, path => by
    simp only [Renaming.topDec, nodesTopDec, List.map_cons, List.map_nil, nrNode_mk, nr_ctx_U, nr_veSchemes]
    simp [Renaming.tyEnv, Renaming.tyFcn]
  | .port x ty U, C, path => by
    simp only [Renaming.topDec, nodesTopDec, nr_bvar_fun, List.map_id', nr_elabPort h]
    cases elabPort C x ty U with
    | none => rfl
    | some p => simp [nrNode_mk, Renaming.portEnv, Renaming.env]
  | .seq a1 a2, C, path => by
    simp only [Renaming.topDec, nodesTopDec, nr_checkTopDec h a1 C]
    cases checkTopDec C a1 with
    | none => rfl
    | some p =>
      obtain ⟨E1, PE1⟩ := p
      simp only [Option.map_some, List.map_append, List.map_cons, List.map_nil, nrNode_mk, nr_ctx_U,
        nr_nodesTopDec h a1, nr_oplusE h, nr_nodesTopDec h a2]

theorem nr_nodesModule (h : NR ρ) (B : SBasis) (a : AModule) :
    nodesModule ((nr ρ).basis B) (a.rename (nr ρ)) = nrNodes ρ (nodesModule B a) := by
  unfold nodesModule
  rw [nr_rename_imports, nr_importCtx h, nr_rename_body]
  cases importCtx B a.imports with
  | none => rfl
  | some C => cases a.body with
    | none => rfl
    | some d => exact nr_nodesTopDec h d C []

/-! ## Generated names -/

theorem nr_custNames (h : NR ρ) : (d : ATopDec) → ((nr ρ).topDec d).custNames = d.custNames.map (nr ρ).tnApply
  | .value _ _ => rfl
  | .types TE VE db tbs => by
    simp only [Renaming.topDec, ATopDec.custNames, nr_namesOf h, List.map_filterMap]
  | .port _ _ _ => rfl
  | .seq a1 a2 => by simp [Renaming.topDec, ATopDec.custNames, nr_custNames h a1, nr_custNames h a2]

theorem nr_genNames (h : NR ρ) (B : SBasis) (a : AModule) :
    genNames ((nr ρ).basis B) (a.rename (nr ρ)) = (genNames B a).map (nr ρ).tnApply := by
  unfold genNames
  rw [nr_rename_body]
  have e : ((a.body.map (nr ρ).topDec).map ATopDec.custNames).getD [] =
      (((a.body.map ATopDec.custNames).getD []).map (nr ρ).tnApply) := by
    cases a.body with
    | none => rfl
    | some d => exact nr_custNames h d
  rw [e, List.filter_map]
  congr 1
  apply List.filter_congr
  intro t _
  simp only [Renaming.basis, Function.comp_apply, List.mem_map]
  congr 2
  exact propext ⟨fun ⟨u, hu, e⟩ => h.inj _ _ e ▸ hu, fun ht => ⟨t, ht, rfl⟩⟩

end

end StandardElm.Stat
