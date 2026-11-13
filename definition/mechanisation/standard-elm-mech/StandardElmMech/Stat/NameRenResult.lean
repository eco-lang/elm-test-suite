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

/-! ## Nodes (the expression level is in NameRenCheck.lean) -/

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
