/-
  A Standard Definition of Elm? Mechanisation: the checker of modules commutes with a renaming of
  type names (plan step 10, transport across bases, third layer): type declarations given their
  names, ports, top-level declarations, exposing, imports, the result of a module in a basis.
-/
import StandardElmMech.Stat.NameRenCheck

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Src (BTy BTyRow BItem BExpList BImport BConBind BDatBind BTypBind)

/-- A port environment renamed. -/
def Renaming.portEnv (r : Renaming) (PE : PortEnv) : PortEnv := PE.map fun p => (p.1, (p.2.1, r.ty p.2.2))

/-- A basis renamed. -/
def Renaming.basis (r : Renaming) (B : SBasis) : SBasis :=
  ⟨B.T.map r.tnApply, B.ME.map (fun p => (p.1, r.iEnv p.2)), r.portEnv B.PE⟩

section
variable {ρ : List (TyName × TyName)}

/-! ## Type functions that are type names -/

theorem nr_natsUpTo_map (k : Nat) :
    (natsUpTo k).map (fun i => (nr ρ).ty (.var (.bnd i .any))) = (natsUpTo k).map fun i => .var (.bnd i .any) := rfl

theorem nr_toFcn (h : NR ρ) (t : TyName) : (nr ρ).tyFcn t.toFcn = ((nr ρ).tnApply t).toFcn := by
  simp only [TyName.toFcn, Renaming.tyFcn, nr_bvar_fun, List.map_id', h.ar t, nr_ty_con, List.map_map]
  rfl

theorem nr_tyFcn_inj (h : NR ρ) (θ θ' : TyFcn) (e : (nr ρ).tyFcn θ = (nr ρ).tyFcn θ') : θ = θ' := by
  rcases θ with ⟨p, b⟩; rcases θ' with ⟨p', b'⟩
  simp only [Renaming.tyFcn, nr_bvar_fun, List.map_id', TyFcn.mk.injEq] at e
  rw [e.1, nr_ty_inj h _ _ e.2]

theorem nr_name? (h : NR ρ) (θ : TyFcn) : ((nr ρ).tyFcn θ).name? = θ.name?.map (nr ρ).tnApply := by
  rcases θ with ⟨p, b⟩
  cases b with
  | con as t =>
    simp only [TyFcn.name?, nr_tyFcn_body, nr_ty_con]
    by_cases e : (⟨p, .con as t⟩ : TyFcn) = t.toFcn
    · rw [if_pos e, ← nr_toFcn h, ← e]; simp
    · rw [if_neg e, if_neg (fun e' => e (nr_tyFcn_inj h _ _ (by rw [nr_toFcn h]; exact e')))]; rfl
  | var _ => rfl
  | record _ _ => simp [TyFcn.name?, Renaming.tyFcn]
  | fn _ _ => rfl

theorem nr_namesOf (h : NR ρ) (TE : TyEnv) (c : String) :
    namesOf ((nr ρ).tyEnv TE) c = (namesOf TE c).map (nr ρ).tnApply := by
  simp only [namesOf, nr_tyEnv_find]
  cases FMap.find? TE c with
  | none => rfl
  | some s => simp [nr_name? h]

theorem nr_tyEnv_inj (h : NR ρ) : (TE TE' : TyEnv) → (nr ρ).tyEnv TE = (nr ρ).tyEnv TE' → TE = TE'
  | [], [], _ => rfl
  | (c, θ, VE) :: r, (c', θ', VE') :: r', e => by
    simp only [Renaming.tyEnv, List.map_cons, List.cons.injEq, Prod.mk.injEq] at e
    rw [e.1.1, nr_tyFcn_inj h _ _ e.1.2.1, nr_valEnv_inj h _ _ e.1.2.2, nr_tyEnv_inj h r r' e.2]
  | [], (_, _, _) :: _, e | (_, _, _) :: _, [], e => by simp [Renaming.tyEnv] at e

theorem nr_tyEnv_dec (h : NR ρ) (TE TE' : TyEnv) :
    decide ((nr ρ).tyEnv TE = (nr ρ).tyEnv TE') = decide (TE = TE') :=
  decide_eq_decide.mpr ⟨nr_tyEnv_inj h _ _, fun e => e ▸ rfl⟩

theorem nr_tyEnv_vals (TE : TyEnv) : FMap.vals ((nr ρ).tyEnv TE) = (FMap.vals TE).map fun s => ((nr ρ).tyFcn s.1, (nr ρ).valEnv s.2) := by
  simp [FMap.vals, Renaming.tyEnv]

/-! ## Type declarations -/

theorem nr_elabConBind (h : NR ρ) (C : Ctx) (τ : Ty) : (cb : BConBind) →
    elabConBind ((nr ρ).ctx C) ((nr ρ).ty τ) cb = (elabConBind C τ cb).map (nr ρ).valEnv
  | [] => rfl
  | (k, tys) :: rest => by
    simp only [elabConBind, nr_elabTyList h, nr_elabConBind h C τ rest]
    cases elabTyList C tys with
    | none => rfl
    | some τs =>
      cases elabConBind C τ rest with
      | none => rfl
      | some VE =>
        simp only [Option.map_some, nr_arrows, ← nr_valEnv_modify]
        rfl

theorem nr_namesNewB (h : NR ρ) (T : List TyName) (TE : TyEnv) :
    namesNewB (T.map (nr ρ).tnApply) ((nr ρ).tyEnv TE) = namesNewB T TE := by
  simp only [namesNewB, nr_tyEnv_vals, List.all_map]
  apply List.all_congr rfl
  intro s
  simp only [Function.comp_apply, nr_name? h]
  cases s.1.name? with
  | none => rfl
  | some t =>
    simp only [Option.map_some]
    rw [decide_eq_decide.mpr (mem_map_inj h.inj)]

theorem nr_seqVars_ctx (C : Ctx) (U : List BVar) : ((nr ρ).ctx C).plusU U = (nr ρ).ctx (C.plusU U) := nr_plusU C U

theorem nr_elabDatBind (h : NR ρ) (C : Ctx) (names : String → Option TyName) : (d : BDatBind) →
    elabDatBind ((nr ρ).ctx C) (fun c => (names c).map (nr ρ).tnApply) d =
      (elabDatBind C names d).map fun p => ((nr ρ).valEnv p.1, (nr ρ).tyEnv p.2)
  | [] => rfl
  | (c, ps, cb) :: rest => by
    simp only [elabDatBind]
    cases hn : names c with
    | none => rfl
    | some t =>
      simp only [Option.map_some, nr_plusU, nr_elabTyList h, nr_elabDatBind h C names rest]
      cases elabTyList (C.plusU (seqVars ps (conBindExtNames cb))) (ps.map BTy.tyvar) with
      | none => rfl
      | some τs =>
        cases elabDatBind C names rest with
        | none => rfl
        | some p =>
          obtain ⟨VE', TE'⟩ := p
          simp only [Option.map_some]
          have e1 := nr_elabConBind h (C.plusU (seqVars ps (conBindExtNames cb))) (.con τs t) cb
          simp only [nr_ty_con, nr_plusU] at e1
          rw [e1]
          cases elabConBind (C.plusU (seqVars ps (conBindExtNames cb))) (.con τs t) cb with
          | none => rfl
          | some VE =>
            simp only [Option.map_some]
            have hc : (cb ≠ [] ∧ ((nr ρ).tnApply t).arity = ps.length ∧
                ∀ s ∈ FMap.vals ((nr ρ).tyEnv TE'), s.1 ≠ ((nr ρ).tnApply t).toFcn) ↔
                (cb ≠ [] ∧ t.arity = ps.length ∧ ∀ s ∈ FMap.vals TE', s.1 ≠ t.toFcn) := by
              rw [h.ar t, nr_tyEnv_vals]
              simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
              constructor
              · rintro ⟨a, b, c⟩; exact ⟨a, b, fun s hs e => c s hs (by rw [e, nr_toFcn h])⟩
              · rintro ⟨a, b, c⟩; exact ⟨a, b, fun s hs e => c s hs (nr_tyFcn_inj h _ _ (by rw [e, nr_toFcn h]))⟩
            by_cases hcond : cb ≠ [] ∧ t.arity = ps.length ∧ ∀ s ∈ FMap.vals TE', s.1 ≠ t.toFcn
            · rw [if_pos (hc.mpr hcond), if_pos hcond]
              simp only [Option.map_some, nr_ctx_tyvars h, nr_closVE h, nr_valEnv_modify, ← nr_toFcn h]
              rw [← nr_tyEnv_modify]
              rfl
            · rw [if_neg (fun e => hcond (hc.mp e)), if_neg hcond]; rfl

theorem nr_elabTypBind (h : NR ρ) (C : Ctx) (tb : BTypBind) :
    elabTypBind ((nr ρ).ctx C) tb = (elabTypBind C tb).map fun p => ((nr ρ).valEnv p.1, (nr ρ).tyEnv p.2) := by
  unfold elabTypBind
  rw [nr_plusU, nr_elabTy h]
  cases elabTy (C.plusU (seqVars tb.params (bTyExtNames tb.t))) tb.t with
  | none => rfl
  | some τ =>
    simp only [Option.map_some]
    have hc : TyFcn.canon ⟨seqVars tb.params (bTyExtNames tb.t), (nr ρ).ty τ⟩ =
        (nr ρ).tyFcn (TyFcn.canon ⟨seqVars tb.params (bTyExtNames tb.t), τ⟩) := by
      rw [← nr_tyFcn_canon h]; simp [Renaming.tyFcn]
    cases smlabs tb.t with
    | none => simp only [Option.map_some, hc]; rfl
    | some ls =>
      simp only
      cases τ with
      | record r tl =>
        cases tl with
        | none =>
          simp only [nr_ty_record, nr_rowLookupAll, nr_row_length]
          cases Row.lookupAll r ls with
          | none => rfl
          | some τs =>
            simp only [Option.map_some]
            split
            · simp only [Option.map_some, nr_ctx_tyvars h]
              have e2 : ([(tb.c, (mono (arrows (τs.map (nr ρ).ty) (Ty.record ((nr ρ).row r) none)), IdStatus.v))] : ValEnv) =
                  (nr ρ).valEnv [(tb.c, (mono (arrows τs (.record r none)), .v))] := by
                show _ = [(tb.c, ((nr ρ).scheme (mono (arrows τs (.record r none))), IdStatus.v))]
                rw [nr_mono, ← nr_arrows, nr_ty_record]
              simp only [nr_ty_record] at hc
              rw [e2, nr_closVE h, hc]
              rfl
            · rfl
        | some _ => simp
      | var _ => rfl
      | fn _ _ => rfl
      | con _ _ => simp

theorem nr_elabTypBinds (h : NR ρ) (C : Ctx) : (tbs : List BTypBind) →
    elabTypBinds ((nr ρ).ctx C) tbs = (elabTypBinds C tbs).map fun p => (p.1.map (nr ρ).valEnv, p.2.map (nr ρ).tyEnv)
  | [] => rfl
  | tb :: tbs => by
    simp only [elabTypBinds, nr_elabTypBind h, nr_elabTypBinds h C tbs]
    cases elabTypBind C tb <;> cases elabTypBinds C tbs <;> rfl

theorem nr_checkTypesFix (h : NR ρ) (C : Ctx) (TE : TyEnv) (VE : ValEnv) (db : Option BDatBind) (tbs : List BTypBind) :
    checkTypesFix ((nr ρ).ctx C) ((nr ρ).tyEnv TE) ((nr ρ).valEnv VE) db tbs = checkTypesFix C TE VE db tbs := by
  unfold checkTypesFix
  simp only [nr_oplusTE h, nr_elabTypBinds h]
  have hn : namesOf ((nr ρ).tyEnv TE) = fun c => (namesOf TE c).map (nr ρ).tnApply := funext (nr_namesOf h TE)
  cases db with
  | none =>
    simp only
    cases elabTypBinds (C.oplusTE TE) tbs with
    | none => rfl
    | some p =>
      obtain ⟨VEs, TEs⟩ := p
      simp only [Option.map_some, nr_tyEnv_plusAll, nr_valEnv_plusAll]
      congr 1
      apply propext
      exact and_congr Iff.rfl (and_congr ⟨nr_tyEnv_inj h _ _, fun e => e ▸ rfl⟩ ⟨nr_valEnv_inj h _ _, fun e => e ▸ rfl⟩)
  | some d =>
    simp only [hn, nr_elabDatBind h]
    cases elabDatBind (C.oplusTE TE) (namesOf TE) d with
    | none => cases elabTypBinds (C.oplusTE TE) tbs <;> rfl
    | some p =>
      obtain ⟨VE', TE'⟩ := p
      cases elabTypBinds (C.oplusTE TE) tbs with
      | none => rfl
      | some q =>
        obtain ⟨VEs, TEs⟩ := q
        simp only [Option.map_some, nr_ctx_T, nr_namesNewB h, nr_tyEnv_plusAll, nr_valEnv_plusAll,
          nr_tyEnv_modify, nr_valEnv_modify]
        congr 1
        apply decide_eq_decide.mpr
        exact and_congr Iff.rfl (and_congr ⟨nr_tyEnv_inj h _ _, fun e => e ▸ rfl⟩ ⟨nr_valEnv_inj h _ _, fun e => e ▸ rfl⟩)

theorem nr_checkTypes (h : NR ρ) (C : Ctx) (TE : TyEnv) (VE : ValEnv) (db : Option BDatBind) (tbs : List BTypBind) :
    checkTypes ((nr ρ).ctx C) ((nr ρ).tyEnv TE) ((nr ρ).valEnv VE) db tbs = checkTypes C TE VE db tbs := by
  simp only [checkTypes, nr_checkTypesFix h, nr_tyEnv_tyvars h]

/-! ## Ports -/

mutual
theorem nr_portB (h : NR ρ) : (τ : Ty) → portB ((nr ρ).ty τ) = portB τ
  | .con [] t => by
    simp only [nr_ty_con, List.map_nil, portB]
    rw [h.beq (by decide) t, h.beq (by decide) t, h.beq (by decide) t, h.beq (by decide) t,
      h.beq (by decide) t, h.beq (by decide) t, h.beq (by decide) t]
  | .con [τ] t => by
    simp only [nr_ty_con, List.map_cons, List.map_nil, portB]
    rw [h.beq (by decide) t, h.beq (by decide) t, h.beq (by decide) t, nr_portB h τ]
  | .con [τ1, τ2] t => by
    simp only [nr_ty_con, List.map_cons, List.map_nil, portB]
    rw [h.beq (by decide) t, nr_portB h τ1, nr_portB h τ2]
  | .con [τ1, τ2, τ3] t => by
    simp only [nr_ty_con, List.map_cons, List.map_nil, portB]
    rw [h.beq (by decide) t, nr_portB h τ1, nr_portB h τ2, nr_portB h τ3]
  | .con (_ :: _ :: _ :: _ :: _) _ => by simp [portB]
  | .record r none => by simp only [nr_ty_record, portB]; exact nr_portRowB h r
  | .record r (some _) => by simp [portB]
  | .var _ => rfl
  | .fn _ _ => rfl
theorem nr_portRowB (h : NR ρ) : (r : Row) → portRowB ((nr ρ).row r) = portRowB r
  | [] => rfl
  | (_, τ) :: rest => by simp only [nr_row_cons, portRowB, nr_portB h τ, nr_portRowB h rest]
end

theorem nr_ofVE (VE : ValEnv) : (nr ρ).env (Env.ofVE VE) = Env.ofVE ((nr ρ).valEnv VE) := rfl

theorem nr_elabPort (h : NR ρ) (C : Ctx) (x : Var) (ty : BTy) (U : List BVar) :
    elabPort ((nr ρ).ctx C) x ty U = (elabPort C x ty U).map fun p => ((nr ρ).env p.1, (nr ρ).portEnv p.2) := by
  unfold elabPort
  simp only [nr_ctx_U, nr_plusU, nr_elabTy h, nr_ctx_tyvars h]
  split
  · cases hel : elabTy (C.plusU U) ty with
    | none => rfl
    | some τ0 =>
      simp only [Option.map_some]
      rcases τ0 with _ | _ | ⟨τ', _ | _ | _ | ⟨_ | ⟨_ | _ | _ | _, _ | _⟩, t⟩⟩ | _ <;> try rfl
      all_goals try simp
      rename_i α
      simp only [nr_ty_fn, nr_ty_con, List.map_cons, List.map_nil, nr_ty_var, h.eq (t0 := tCmd) (by decide),
        h.eq (t0 := tSub) (by decide), nr_portB h]
      by_cases hc : t = tCmd ∧ portB τ' = true
      · rw [if_pos hc, if_pos hc]
        simp only [Option.map_some, hc.1, h.fix (t0 := tCmd) (by decide)]
        rw [show mono (Ty.fn ((nr ρ).ty τ') (Ty.con [Ty.var α] tCmd)) =
          (nr ρ).scheme (mono (Ty.fn τ' (Ty.con [Ty.var α] tCmd))) by
            simp [nr_mono, h.fix (t0 := tCmd) (by decide)], nr_closScheme h]
        rfl
      · rw [if_neg hc, if_neg hc]
        rcases τ' with _ | _ | ⟨τ'', _ | _ | _ | _⟩ | _ <;> try rfl
        all_goals try simp
        rename_i α'
        simp only [nr_ty_fn, nr_ty_var, nr_portB h]
        by_cases hc2 : t = tSub ∧ α' = α ∧ portB τ'' = true
        · rw [if_pos hc2, if_pos hc2]
          simp only [Option.map_some, hc2.1, h.fix (t0 := tSub) (by decide)]
          rw [show mono (Ty.fn (Ty.fn ((nr ρ).ty τ'') (Ty.var α')) (Ty.con [Ty.var α] tSub)) =
            (nr ρ).scheme (mono (Ty.fn (Ty.fn τ'' (Ty.var α')) (Ty.con [Ty.var α] tSub))) by
              simp [nr_mono, h.fix (t0 := tSub) (by decide)], nr_closScheme h]
          rfl
        · rw [if_neg hc2, if_neg hc2]
  · rfl

/-! ## Top-level declarations -/

theorem nr_plusPE (PE PE' : PortEnv) : Env.plusPE ((nr ρ).portEnv PE) ((nr ρ).portEnv PE') = (nr ρ).portEnv (Env.plusPE PE PE') :=
  modify_mapV (fun p : Dir × Ty => (p.1, (nr ρ).ty p.2)) PE PE'

theorem nr_checkTopDec (h : NR ρ) : (d : ATopDec) → (C : Ctx) →
    checkTopDec ((nr ρ).ctx C) ((nr ρ).topDec d) = (checkTopDec C d).map fun p => ((nr ρ).env p.1, (nr ρ).portEnv p.2)
  | .value VE vb, C => by
    simp only [Renaming.topDec, checkTopDec, nr_plusVE, nr_checkValBind h, nr_valBind_ve h, nr_valEnv_dec h]
    split
    · simp only [Option.map_some, nr_ctx_tyvars h, nr_closGroup h, nr_ofVE]; rfl
    · rfl
  | .types TE VE db tbs, C => by
    simp only [Renaming.topDec, checkTopDec, nr_checkTypes h]
    split
    · rfl
    · rfl
  | .port x ty U, C => by
    simp only [Renaming.topDec, checkTopDec, nr_bvar_fun, List.map_id']
    exact nr_elabPort h C x ty U
  | .seq a1 a2, C => by
    simp only [Renaming.topDec, checkTopDec, nr_checkTopDec h a1 C]
    cases checkTopDec C a1 with
    | none => rfl
    | some p =>
      obtain ⟨E1, PE1⟩ := p
      simp only [Option.map_some, nr_oplusE h, nr_checkTopDec h a2]
      cases checkTopDec (C.oplusE E1) a2 with
      | none => rfl
      | some q => simp only [Option.map_some, nr_env_plus, nr_plusPE]

theorem nr_checkTopDecOpt (h : NR ρ) (C : Ctx) (d : Option ATopDec) :
    checkTopDecOpt ((nr ρ).ctx C) (d.map (nr ρ).topDec) =
      (checkTopDecOpt C d).map fun p => ((nr ρ).env p.1, (nr ρ).portEnv p.2) := by
  cases d with
  | none => rfl
  | some d => exact nr_checkTopDec h d C

end

end StandardElm.Stat
