/-
  A Standard Definition of Elm? Mechanisation: the mutual specialisation is invariant under the
  relation of RenameSpec.lean (plan step 10, the mutual statement under `reduceProgram_rename`).
-/
import StandardElmMech.Stat.RenameSpec

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)

/-! ## The members of a group -/

def MembersRel (r : Renaming) (D : BVar → Prop) : List Member → List Member → Prop
  | [], [] => True
  | m :: ms, m' :: ms' => MemberRel r D m m' ∧ MembersRel r D ms ms'
  | _, _ => False

theorem MembersRel.map {r : Renaming} {D : BVar → Prop} {β γ : Type} (f : Member → β) (f' : Member → γ)
    (g : β → γ) (hf : ∀ m m', MemberRel r D m m' → f' m' = g (f m)) :
    ∀ {ms ms' : List Member}, MembersRel r D ms ms' → ms'.map f' = (ms.map f).map g
  | [], [], _ => rfl
  | m :: ms, m' :: ms', h => by
    simp only [List.map_cons, hf m m' h.1, MembersRel.map f f' g hf h.2]
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem MembersRel.append {r : Renaming} {D : BVar → Prop} :
    ∀ {ms ms' ns ns' : List Member}, MembersRel r D ms ms' → MembersRel r D ns ns' →
      MembersRel r D (ms ++ ns) (ms' ++ ns')
  | [], [], _, _, _, h => h
  | _ :: _, _ :: _, _, _, h, h' => ⟨h.1, MembersRel.append h.2 h'⟩
  | [], _ :: _, _, _, h, _ | _ :: _, [], _, _, h, _ => h.elim

theorem AnnRel.isSome {r : Renaming} {D : BVar → Prop} :
    ∀ {ann ann' : Option (Src.BTy × List BVar)}, AnnRel r D ann ann' → ann'.isSome = ann.isSome
  | none, none, _ => rfl
  | some _, some _, _ => rfl
  | none, some _, h | some _, none, h => h.elim

theorem AnnRel.annU {r : Renaming} {D : BVar → Prop} :
    ∀ {ann ann' : Option (Src.BTy × List BVar)}, AnnRel r D ann ann' →
      ∀ v, D v → (v ∈ annU ann ↔ r.bvar v ∈ annU ann')
  | none, none, _ => fun v _ => by show v ∈ ([] : List BVar) ↔ _ ∈ ([] : List BVar); simp
  | some (_, _), some (_, _), h => h
  | none, some _, h | some _, none, h => h.elim

theorem members_pat {r : Renaming} (hr : r.WF) {D : BVar → Prop} {A A' : List BVar}
    (hA : ∀ v, D v → (v ∈ A ↔ r.bvar v ∈ A')) {VEtv : List BVar} (hVE : ∀ v ∈ VEtv, D v) :
    ∀ (l : ValEnv), (∀ q ∈ l, ∀ v ∈ q.2.1.body.vars, D v) →
      MembersRel r D (l.map fun (x, (σ, _)) => memberOf A VEtv x σ.body [] false)
        ((r.valEnv l).map fun (x, (σ, _)) => memberOf A' (VEtv.map r.bvar) x σ.body [] false)
  | [], _ => trivial
  | (x, (σ, st)) :: rest, h => by
    refine ⟨?_, members_pat hr hA hVE rest fun q hq => h q (List.mem_cons_of_mem _ hq)⟩
    exact memberOf_rename hr hA hVE x σ.body (h _ (List.mem_cons_self ..)) (fun _ _ => by simp) false

mutual
theorem members_rename {r : Renaming} (hr : r.WF) {D : BVar → Prop} {A A' : List BVar}
    (hA : ∀ v, D v → (v ∈ A ↔ r.bvar v ∈ A')) {VEtv : List BVar} (hVE : ∀ v ∈ VEtv, D v) :
    (vb : AValBind) → ∀ {vb' : AValBind}, RValBind r D vb vb' →
      MembersRel r D (vb.members A VEtv) (vb'.members A' (VEtv.map r.bvar))
  | .var x ann τ e rest, _, h => by
    cases h with
    | var hann hτ _ hrest =>
      unfold AValBind.members
      refine ⟨?_, ?_⟩
      · rw [hann.isSome]; exact memberOf_rename hr hA hVE x τ hτ hann.annU _
      · exact membersOpt_rename hr hA hVE rest hrest
  | .pat p e, _, h => by
    cases h with
    | pat _ hve hD _ =>
      simp only [AValBind.members, hve]
      exact members_pat hr hA hVE p.ve hD
theorem membersOpt_rename {r : Renaming} (hr : r.WF) {D : BVar → Prop} {A A' : List BVar}
    (hA : ∀ v, D v → (v ∈ A ↔ r.bvar v ∈ A')) {VEtv : List BVar} (hVE : ∀ v ∈ VEtv, D v) :
    (rest : Option AValBind) → ∀ {rest' : Option AValBind}, RValBindOpt r D rest rest' →
      MembersRel r D (match rest with | none => [] | some vb => vb.members A VEtv)
        (match rest' with | none => [] | some vb => vb.members A' (VEtv.map r.bvar))
  | none, _, h => by cases h; trivial
  | some vb, _, h => by cases h with | some h => exact members_rename hr hA hVE vb h
end

theorem MembersRel.bodyD {r : Renaming} {D : BVar → Prop} :
    ∀ {ms ms' : List Member}, MembersRel r D ms ms' → ∀ α ∈ ms.flatMap (·.body.tyVarsSeq), D (.ty α)
  | [], [], _, _, h => by simp at h
  | m :: ms, m' :: ms', h, α, hα => by
    simp only [List.flatMap_cons, List.mem_append] at hα
    rcases hα with hα | hα
    · exact h.1.bodyD _ (mem_vars_of_tyVarsSeq _ hα)
    · exact MembersRel.bodyD h.2 α hα
  | [], _ :: _, h, _, _ | _ :: _, [], h, _, _ => h.elim

theorem MembersRel.flatMap {r : Renaming} {D : BVar → Prop} {β : Type} (f f' : Member → List β) (g : β → β)
    (hf : ∀ m m', MemberRel r D m m' → f' m' = (f m).map g) :
    ∀ {ms ms' : List Member}, MembersRel r D ms ms' → ms'.flatMap f' = (ms.flatMap f).map g
  | [], [], _ => rfl
  | m :: ms, m' :: ms', h => by
    simp only [List.flatMap_cons, List.map_append, hf m m' h.1, MembersRel.flatMap f f' g hf h.2]
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem MembersRel.any_uvars {r : Renaming} {D : BVar → Prop} (α : TyVar) (hα : D (.ty α)) :
    ∀ {ms ms' : List Member}, MembersRel r D ms ms' →
      ms'.any (·.uvars.contains (r.tvApply α)) = ms.any (·.uvars.contains α)
  | [], [], _ => rfl
  | m :: ms, m' :: ms', h => by
    rw [List.any_cons, List.any_cons, MembersRel.any_uvars α hα h.2, contains_eq_decide, contains_eq_decide,
      decide_eq_decide.mpr (h.1.uvars α hα).symm]
  | [], _ :: _, h | _ :: _, [], h => h.elim

theorem numVars_rename {r : Renaming} (hr : r.WF) {D : BVar → Prop} {ms ms' : List Member}
    (h : MembersRel r D ms ms') :
    GroupView.numVars ⟨ms', ms'.flatMap fun m => m.bOut.filterMap BVar.tyVar?⟩ =
      (GroupView.numVars ⟨ms, ms.flatMap fun m => m.bOut.filterMap BVar.tyVar?⟩).map r.tvApply := by
  unfold GroupView.numVars
  simp only
  have hb : ms'.flatMap (·.body.tyVarsSeq) = (ms.flatMap (·.body.tyVarsSeq)).map r.tvApply :=
    MembersRel.flatMap _ _ _ (fun m m' hm => by rw [hm.body, tyVarsSeq_rename]) h
  have hc : (ms'.flatMap fun m => m.bOut.filterMap BVar.tyVar?) =
      (ms.flatMap fun m => m.bOut.filterMap BVar.tyVar?).map r.tvApply :=
    MembersRel.flatMap _ _ _ (fun m m' hm => by
      rw [hm.bOut, List.filterMap_map, List.map_filterMap]
      congr 1; funext v; exact Renaming.tyVar?_bvar r v) h
  rw [hb, hc, dedupFirst_map _ hr.tv_inj, List.filter_map]
  congr 1
  apply List.filter_congr
  intro α hα
  have hD := h.bodyD α (mem_dedupFirst.mp hα)
  simp only [Function.comp_apply, hr.tv_cls, contains_map_inj hr.tv_inj, MembersRel.any_uvars α hD h]

theorem groupView_rename {r : Renaming} (hr : r.WF) {D : BVar → Prop} {A A' : List BVar}
    (hA : ∀ v, D v → (v ∈ A ↔ r.bvar v ∈ A')) {VE : ValEnv} (hD : ∀ p ∈ VE, ∀ v ∈ p.2.1.tyvars, D v)
    {vb vb' : AValBind} (hvb : RValBind r D vb vb') :
    MembersRel r D (groupView A VE vb).members (groupView A' (r.valEnv VE) vb').members ∧
    (groupView A' (r.valEnv VE) vb').numVars = (groupView A VE vb).numVars.map r.tvApply := by
  have hVE : ∀ v ∈ dedupL (ValEnv.tyvars VE), D v := fun v hv => by
    obtain ⟨q, hq, hvq⟩ := mem_valEnv_tyvars (mem_dedupL.mp hv); exact hD q hq v hvq
  have hms := members_rename hr hA hVE vb hvb
  have hVEtv : dedupL (ValEnv.tyvars (r.valEnv VE)) = (dedupL (ValEnv.tyvars VE)).map r.bvar := by
    rw [valEnv_tyvars_rename hr, dedupL_map _ hr.bvar_inj]
  unfold groupView
  simp only [hVEtv]
  exact ⟨hms, numVars_rename hr hms⟩

theorem mkRef_rename (r : Renaming) (g : Nat) (V : List TyVar) (body : Ty) (bv : List BVar) :
    mkRef g (V.map r.tvApply) (r.ty body) (bv.map r.bvar) = r.ref (mkRef g V body bv) := by
  unfold mkRef
  by_cases h : V.isEmpty = true
  · simp [h, Renaming.ref]
  · simp [h, Renaming.ref]

theorem bOutAll_rename {r : Renaming} (hr : r.WF) (V : List TyVar) {m m' : Member} (h : m'.bOut = m.bOut.map r.bvar) :
    m'.bOutAll (V.map r.tvApply) = (m.bOutAll V).map r.bvar := by
  unfold Member.bOutAll
  rw [h, List.map_append, List.filter_map]
  congr 1
  rw [List.map_map, List.map_map]
  congr 1
  apply List.filter_congr
  intro v _
  simp only [Function.comp_apply]
  rw [show (BVar.ty (r.tvApply v)) = r.bvar (.ty v) from rfl, contains_map_inj hr.bvar_inj]

theorem refsOut_rename {r : Renaming} (hr : r.WF) {D : BVar → Prop} (g : Nat) (V : List TyVar)
    {ms ms' : List Member} (h : MembersRel r D ms ms') :
    (ms'.map fun m => (m.x, mkRef g (V.map r.tvApply) m.body (m.bOutAll (V.map r.tvApply)))) =
      r.binds (ms.map fun m => (m.x, mkRef g V m.body (m.bOutAll V))) :=
  MembersRel.map _ _ _ (fun m m' hm => by
    simp only [hm.x, hm.body, bOutAll_rename hr V hm.bOut, mkRef_rename]) h

theorem refsIn_rename (r : Renaming) {D : BVar → Prop} (g : Nat) (V : List TyVar)
    {ms ms' : List Member} (h : MembersRel r D ms ms') :
    (ms'.map fun m => (m.x, mkRef g (V.map r.tvApply) m.body m.bIn)) =
      r.binds (ms.map fun m => (m.x, mkRef g V m.body m.bIn)) :=
  MembersRel.map _ _ _ (fun m m' hm => by simp only [hm.x, hm.body, hm.bIn, mkRef_rename]) h

theorem numEnv_zip (r : Renaming) (V : List TyVar) (a : Assignment) (ρ : NumEnv) :
    (V.map r.tvApply).zip a ++ r.numEnv ρ = r.numEnv (V.zip a ++ ρ) := by
  simp only [Renaming.numEnv, List.map_append, List.zip_map_left]
  rfl

/-! ## The mutual specialisation -/

mutual
theorem specAtExp_rename {r : Renaming} (hr : r.WF) {D : BVar → Prop} :
    (a : AAtExp) → ∀ {a' : AAtExp}, RAtExp r D a a' → ∀ (ρ : NumEnv) {Γ Γ' : Scope} {L L' : Ctx} (g : Nat),
      ScopeRel r Γ Γ' → CtxRel r D L L' → specAtExp (r.numEnv ρ) Γ' L' g a' = specAtExp ρ Γ L g a
  | .scon sc τ, _, h => by
    intro ρ Γ Γ' L L' g hΓ hL; cases h; simp only [specAtExp, specSCon_rename hr]
  | .var lv inst τ, _, h => by
    intro ρ Γ Γ' L L' g hΓ hL; cases h; simp only [specAtExp, specOcc_rename hr hΓ]
  | .con _ _ _, _, h => by intro ρ Γ Γ' L L' g hΓ hL; cases h; rfl
  | .op _ _ _, _, h => by intro ρ Γ Γ' L L' g hΓ hL; cases h; rfl
  | .unit, _, h => by intro ρ Γ Γ' L L' g hΓ hL; cases h; rfl
  | .nil _, _, h => by intro ρ Γ Γ' L L' g hΓ hL; cases h; rfl
  | .tuple e1 e2 e3, _, h => by
    intro ρ Γ Γ' L L' g hΓ hL
    cases h with
    | tuple h1 h2 h3 =>
      simp only [specAtExp, specExp_rename hr e1 h1 ρ g hΓ hL, specExp_rename hr e2 h2 ρ g hΓ hL,
        specExpOpt_rename hr e3 h3 ρ g hΓ hL]
  | .record row, _, h => by
    intro ρ Γ Γ' L L' g hΓ hL
    cases h with
    | record h1 => simp only [specAtExp, specExpRowOpt_rename hr row h1 ρ g hΓ hL]
  | .update x inst τ row, _, h => by
    intro ρ Γ Γ' L L' g hΓ hL
    cases h with
    | update h1 =>
      have := specOcc_rename hr hΓ ρ ⟨none, x⟩ inst
      simp only [specAtExp, this, specExpRow_rename hr row h1 ρ g hΓ hL]
  | .letE (.val VE vb) e, _, h => by
    intro ρ Γ Γ' L L' g hΓ hL
    cases h with
    | letE hD hvb he =>
      rename_i vb' e'
      have hA := hL.tyvars hr
      obtain ⟨hgm, hgV⟩ := groupView_rename hr hA hD hvb
      have hOut := refsOut_rename hr g (groupView L.tyvars VE vb).numVars hgm
      have hIn := refsIn_rename r g (groupView L.tyvars VE vb).numVars hgm
      have hC := closGroup_rename hr hA VE hD
      have hb := specExp_rename hr e he ρ (g + 1)
        (hΓ.push ((groupView L.tyvars VE vb).members.map fun m =>
          (m.x, mkRef g (groupView L.tyvars VE vb).numVars m.body (m.bOutAll (groupView L.tyvars VE vb).numVars))))
        (hL.plusVE (closGroup L.tyvars VE))
      have hvbs : ∀ a, specValBind (r.numEnv ((groupView L.tyvars VE vb).numVars.zip a ++ ρ))
          (Γ'.push (r.binds ((groupView L.tyvars VE vb).members.map fun m =>
            (m.x, mkRef g (groupView L.tyvars VE vb).numVars m.body m.bIn))))
          (L'.plusVE (r.valEnv VE)) (g + 1) a vb' =
          specValBind ((groupView L.tyvars VE vb).numVars.zip a ++ ρ)
          (Γ.push ((groupView L.tyvars VE vb).members.map fun m =>
            (m.x, mkRef g (groupView L.tyvars VE vb).numVars m.body m.bIn)))
          (L.plusVE VE) (g + 1) a vb :=
        fun a => specValBind_rename hr vb hvb _ (g + 1) a (hΓ.push _) (hL.plusVE VE)
      simp only [specAtExp, hgV, hOut, hIn, hC, hb, numEnv_zip, List.length_map, hvbs]
  | .paren e, _, h => by
    intro ρ Γ Γ' L L' g hΓ hL
    cases h with
    | paren h1 => simp only [specAtExp, specExp_rename hr e h1 ρ g hΓ hL]
theorem specExpRow_rename {r : Renaming} (hr : r.WF) {D : BVar → Prop} :
    (row : AExpRow) → ∀ {row' : AExpRow}, RExpRow r D row row' → ∀ (ρ : NumEnv) {Γ Γ' : Scope} {L L' : Ctx} (g : Nat),
      ScopeRel r Γ Γ' → CtxRel r D L L' → specExpRow (r.numEnv ρ) Γ' L' g row' = specExpRow ρ Γ L g row
  | .field l e rest, _, h => by
    intro ρ Γ Γ' L L' g hΓ hL
    cases h with
    | field h1 h2 =>
      simp only [specExpRow, specExp_rename hr e h1 ρ g hΓ hL, specExpRowOpt_rename hr rest h2 ρ g hΓ hL]
theorem specExpRowOpt_rename {r : Renaming} (hr : r.WF) {D : BVar → Prop} :
    (row : Option AExpRow) → ∀ {row' : Option AExpRow}, RExpRowOpt r D row row' → ∀ (ρ : NumEnv) {Γ Γ' : Scope}
      {L L' : Ctx} (g : Nat), ScopeRel r Γ Γ' → CtxRel r D L L' →
      specExpRowOpt (r.numEnv ρ) Γ' L' g row' = specExpRowOpt ρ Γ L g row
  | none, _, h => by intro ρ Γ Γ' L L' g hΓ hL; cases h; rfl
  | some row, _, h => by
    intro ρ Γ Γ' L L' g hΓ hL
    cases h with
    | some h1 => simp only [specExpRowOpt, specExpRow_rename hr row h1 ρ g hΓ hL]
theorem specExp_rename {r : Renaming} (hr : r.WF) {D : BVar → Prop} :
    (e : AExp) → ∀ {e' : AExp}, RExp r D e e' → ∀ (ρ : NumEnv) {Γ Γ' : Scope} {L L' : Ctx} (g : Nat),
      ScopeRel r Γ Γ' → CtxRel r D L L' → specExp (r.numEnv ρ) Γ' L' g e' = specExp ρ Γ L g e
  | .atexp a, _, h => by
    intro ρ Γ Γ' L L' g hΓ hL
    cases h with
    | atexp h1 => simp only [specExp, specAtExp_rename hr a h1 ρ g hΓ hL]
  | .app e a, _, h => by
    intro ρ Γ Γ' L L' g hΓ hL
    cases h with
    | app h1 h2 => simp only [specExp, specExp_rename hr e h1 ρ g hΓ hL, specAtExp_rename hr a h2 ρ g hΓ hL]
  | .lam p e, _, h => by
    intro ρ Γ Γ' L L' g hΓ hL
    cases h with
    | lam hpe hve h1 =>
      simp only [specExp, erAtPat_congr [] p _ hpe, hve,
        specExp_rename hr e h1 ρ g (hΓ.pushPlain p.ve) (hL.plusVE p.ve)]
  | .caseE e m, _, h => by
    intro ρ Γ Γ' L L' g hΓ hL
    cases h with
    | caseE h1 h2 => simp only [specExp, specExp_rename hr e h1 ρ g hΓ hL, specMatch_rename hr m h2 ρ g hΓ hL]
theorem specExpOpt_rename {r : Renaming} (hr : r.WF) {D : BVar → Prop} :
    (e : Option AExp) → ∀ {e' : Option AExp}, RExpOpt r D e e' → ∀ (ρ : NumEnv) {Γ Γ' : Scope} {L L' : Ctx}
      (g : Nat), ScopeRel r Γ Γ' → CtxRel r D L L' → specExpOpt (r.numEnv ρ) Γ' L' g e' = specExpOpt ρ Γ L g e
  | none, _, h => by intro ρ Γ Γ' L L' g hΓ hL; cases h; rfl
  | some e, _, h => by
    intro ρ Γ Γ' L L' g hΓ hL
    cases h with
    | some h1 => simp only [specExpOpt, specExp_rename hr e h1 ρ g hΓ hL]
theorem specMatch_rename {r : Renaming} (hr : r.WF) {D : BVar → Prop} :
    (m : AMatch) → ∀ {m' : AMatch}, RMatch r D m m' → ∀ (ρ : NumEnv) {Γ Γ' : Scope} {L L' : Ctx} (g : Nat),
      ScopeRel r Γ Γ' → CtxRel r D L L' → specMatch (r.numEnv ρ) Γ' L' g m' = specMatch ρ Γ L g m
  | .mk mr rest, _, h => by
    intro ρ Γ Γ' L L' g hΓ hL
    cases h with
    | mk h1 h2 =>
      simp only [specMatch, specMRule_rename hr mr h1 ρ g hΓ hL, specMatchOpt_rename hr rest h2 ρ g hΓ hL]
theorem specMatchOpt_rename {r : Renaming} (hr : r.WF) {D : BVar → Prop} :
    (m : Option AMatch) → ∀ {m' : Option AMatch}, RMatchOpt r D m m' → ∀ (ρ : NumEnv) {Γ Γ' : Scope}
      {L L' : Ctx} (g : Nat), ScopeRel r Γ Γ' → CtxRel r D L L' →
      specMatchOpt (r.numEnv ρ) Γ' L' g m' = specMatchOpt ρ Γ L g m
  | none, _, h => by intro ρ Γ Γ' L L' g hΓ hL; cases h; rfl
  | some m, _, h => by
    intro ρ Γ Γ' L L' g hΓ hL
    cases h with
    | some h1 => simp only [specMatchOpt, specMatch_rename hr m h1 ρ g hΓ hL]
theorem specMRule_rename {r : Renaming} (hr : r.WF) {D : BVar → Prop} :
    (mr : AMRule) → ∀ {mr' : AMRule}, RMRule r D mr mr' → ∀ (ρ : NumEnv) {Γ Γ' : Scope} {L L' : Ctx} (g : Nat),
      ScopeRel r Γ Γ' → CtxRel r D L L' → specMRule (r.numEnv ρ) Γ' L' g mr' = specMRule ρ Γ L g mr
  | .mk p e, _, h => by
    intro ρ Γ Γ' L L' g hΓ hL
    cases h with
    | mk hpe hve h1 =>
      simp only [specMRule, erPat_congr [] p _ hpe, hve,
        specExp_rename hr e h1 ρ g (hΓ.pushPlain p.ve) (hL.plusVE p.ve)]
theorem specValBind_rename {r : Renaming} (hr : r.WF) {D : BVar → Prop} :
    (vb : AValBind) → ∀ {vb' : AValBind}, RValBind r D vb vb' → ∀ (ρ : NumEnv) {Γ Γ' : Scope} {L L' : Ctx}
      (g : Nat) (a : Assignment), ScopeRel r Γ Γ' → CtxRel r D L L' →
      specValBind (r.numEnv ρ) Γ' L' g a vb' = specValBind ρ Γ L g a vb
  | .var x ann τ e rest, _, h => by
    intro ρ Γ Γ' L L' g a hΓ hL
    cases h with
    | var hann _ h1 h2 =>
      simp only [specValBind, specExp_rename hr e h1 ρ g hΓ (hL.plusU hann.annU),
        specValBindOpt_rename hr rest h2 ρ g a hΓ hL]
  | .pat p e, _, h => by
    intro ρ Γ Γ' L L' g a hΓ hL
    cases h with
    | pat hpe _ _ h1 =>
      simp only [specValBind, erAtPat_congr a p _ hpe, specExp_rename hr e h1 ρ g hΓ hL]
theorem specValBindOpt_rename {r : Renaming} (hr : r.WF) {D : BVar → Prop} :
    (vb : Option AValBind) → ∀ {vb' : Option AValBind}, RValBindOpt r D vb vb' → ∀ (ρ : NumEnv) {Γ Γ' : Scope}
      {L L' : Ctx} (g : Nat) (a : Assignment), ScopeRel r Γ Γ' → CtxRel r D L L' →
      specValBindOpt (r.numEnv ρ) Γ' L' g a vb' = specValBindOpt ρ Γ L g a vb
  | none, _, h => by intro ρ Γ Γ' L L' g a hΓ hL; cases h; rfl
  | some vb, _, h => by
    intro ρ Γ Γ' L L' g a hΓ hL
    cases h with
    | some h1 => simp only [specValBindOpt, specValBind_rename hr vb h1 ρ g a hΓ hL]
end

end StandardElm.Stat
