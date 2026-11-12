/-
  A Standard Definition of Elm? Mechanisation: two module derivations that are instances of each
  other, in one basis, have related value declarations (plan step 10, `mutualInstanceMod_renaming`,
  in the form `reduceWith_rename` needs: the relation of RenameSpec.lean on the module's value
  declarations, by one renaming).

  The renaming is built from the substitution `S` of one instance on the variables of the types
  at the nodes that have a partner in the other derivation (`modVars`), extended by
  RenameExtend.lean; the type names are renamed by the instance's bijection between generated
  names, which are new, so none is a name of `T0`.
-/
import StandardElmMech.Stat.MutualWalkExp

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)

/-! ## Type declarations have no value declarations -/

theorem splitShape_types {d1 d2 : Src.BTopDec} (h : splitShape d1 d2 = true) :
    (∃ db tbs, d1 = .types db tbs) ∧ ∃ tbs, d2 = .types none tbs := by
  unfold splitShape at h
  split at h
  · exact ⟨⟨_, _, rfl⟩, _, rfl⟩
  · cases h

theorem values_of_types : ∀ (d : ATopDec) (C : Ctx), (checkTopDec C d).isSome →
    (∃ db tbs, d.erase = .types db tbs) → valuesOnly d.items = []
  | .value _ _, _, _, ⟨_, _, he⟩ => by simp [ATopDec.erase] at he
  | .types _ _ _ _, _, _, _ => rfl
  | .typesSplit a1 a2, C, hc, _ => by
    simp only [checkTopDec] at hc
    split at hc
    · rename_i hs
      obtain ⟨⟨db, tbs, h1⟩, tbs2, h2⟩ := splitShape_types hs
      cases hc1 : checkTopDec C a1 with
      | none => rw [hc1] at hc; cases hc
      | some p =>
        obtain ⟨E1, PE1⟩ := p
        rw [hc1] at hc
        simp only at hc
        cases hc2 : checkTopDec (C.oplusE E1) a2 with
        | none => rw [hc2] at hc; cases hc
        | some _ =>
          simp only [ATopDec.items, valuesOnly, List.filter_append]
          have e1 := values_of_types a1 C (by rw [hc1]; rfl) ⟨_, _, h1⟩
          have e2 := values_of_types a2 (C.oplusE E1) (by rw [hc2]; rfl) ⟨_, _, h2⟩
          simp only [valuesOnly] at e1 e2
          rw [e1, e2]; rfl
    · cases hc
  | .port _ _ _, _, _, ⟨_, _, he⟩ => by simp [ATopDec.erase] at he
  | .seq _ _, _, _, ⟨_, _, he⟩ => by simp [ATopDec.erase] at he

theorem typesSplit_erase {a1 a2 : ATopDec} {C : Ctx} (hc : (checkTopDec C (.typesSplit a1 a2)).isSome) :
    ∃ db tbs, (ATopDec.typesSplit a1 a2).erase = .types db tbs := by
  simp only [checkTopDec] at hc
  split at hc
  · rename_i hs
    obtain ⟨⟨db, tbs, h1⟩, tbs2, h2⟩ := splitShape_types hs
    simp only [ATopDec.erase, h1, h2]
    exact ⟨_, _, rfl⟩
  · cases hc

/-! ## Pairs of node types -/

theorem mapM_pair {f f' : Ty → Option Ty} {g g' : Ty → Ty} :
    ∀ {l l'' : List Ty}, (l.map g).mapM f = some l'' → (l''.map g').mapM f' = some l →
      ∀ x ∈ l, ∃ y ∈ l'', f (g x) = some y ∧ f' (g' y) = some x
  | [], _, _, _, x, hx => by simp at hx
  | a :: as, l'', h, h', x, hx => by
    simp only [List.map_cons, List.mapM_cons] at h
    cases h1 : f (g a) <;> cases h2 : (as.map g).mapM f <;> simp [h1, h2] at h
    rename_i b bs
    subst h
    simp only [List.map_cons, List.mapM_cons] at h'
    cases h3 : f' (g' b) <;> cases h4 : (bs.map g').mapM f' <;> simp [h3, h4] at h'
    obtain ⟨rfl, rfl⟩ := h'
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨b, List.mem_cons_self .., h1, h3⟩
    · obtain ⟨y, hy, e1, e2⟩ := mapM_pair h2 h4 x hx
      exact ⟨y, List.mem_cons_of_mem _ hy, e1, e2⟩

theorem node_pair {S S' : Subst} {ν ν' : List (TyName × TyName)} {n n'' : Node}
    (h : NodeInstance S (n.renameNames ν) n'') (h' : NodeInstance S' (n''.renameNames ν') n) :
    ∀ τ ∈ n.tys, ∃ τ'' ∈ n''.tys, S.apply (Ty.renameNames ν τ) = some τ'' ∧ S'.apply (Ty.renameNames ν' τ'') = some τ :=
  mapM_pair (by simpa [Node.renameNames] using h.2.1) (by simpa [Node.renameNames] using h'.2.1)

theorem var_of_pair {S S' : Subst} {ν ν' : List (TyName × TyName)} {n n'' : Node}
    (h : NodeInstance S (n.renameNames ν) n'') (h' : NodeInstance S' (n''.renameNames ν') n) :
    ∀ τ ∈ n.tys, ∀ v ∈ τ.vars, ∃ τ'' ∈ n''.tys, ∃ w ∈ τ''.vars, S.applyVar v = some w ∧ S'.applyVar w = some v := by
  intro τ hτ v hv
  obtain ⟨τ'', hτ'', e1, e2⟩ := node_pair h h' τ hτ
  obtain ⟨w, hw, h1, h2⟩ := var_corr τ e1 e2 v hv
  exact ⟨τ'', hτ'', w, hw, h1, h2⟩

/-! ## The walk over a module's declarations -/

theorem ItemsRel.append {r : Renaming} {D : BVar → Prop} :
    ∀ {is is' js js' : List TopItem}, ItemsRel r D is is' → ItemsRel r D js js' → ItemsRel r D (is ++ js) (is' ++ js')
  | [], [], _, _, _, h => h
  | _ :: _, _ :: _, _, _, h, h' => ⟨h.1, ItemsRel.append h.2 h'⟩
  | [], _ :: _, _, _, h, _ | _ :: _, [], _, _, h, _ => h.elim

section Walk
variable {S S' : Subst} {ν ν' : List (TyName × TyName)} {r : Renaming} {D : BVar → Prop}

/-- The hypotheses of the walk over two lists of nodes of a module. -/
structure TopHyp (S S' : Subst) (ν ν' : List (TyName × TyName)) (D : BVar → Prop) (ns ns'' : List Node) : Prop where
  ni : ∀ n ∈ ns, ∀ n'' ∈ ns'', n.path = n''.path → NodeInstance S (n.renameNames ν) n''
  ni' : ∀ n'' ∈ ns'', ∀ n ∈ ns, n''.path = n.path → NodeInstance S' (n''.renameNames ν') n
  d : ∀ n ∈ ns, ∀ n'' ∈ ns'', n.path = n''.path → ∀ τ ∈ n.tys, ∀ v ∈ τ.vars, v.isBnd = false →
    ∀ w, S.applyVar v = some w → w.isBnd = false → D v

theorem TopHyp.mono {ns ns'' ms ms'' : List Node} (h : TopHyp S S' ν ν' D ns ns'') (hm : ∀ n ∈ ms, n ∈ ns)
    (hm'' : ∀ n ∈ ms'', n ∈ ns'') : TopHyp S S' ν ν' D ms ms'' :=
  ⟨fun n hn n'' hn'' e => h.ni n (hm n hn) n'' (hm'' n'' hn'') e,
   fun n'' hn'' n hn e => h.ni' n'' (hm'' n'' hn'') n (hm n hn) e,
   fun n hn n'' hn'' e => h.d n (hm n hn) n'' (hm'' n'' hn'') e⟩

/-- Over the nodes of a value declaration, whose types have no `bnd` variable, the hypotheses of
    the walk give those of MutualWalk.lean. -/
theorem TopHyp.rel3 {ns ns'' : List Node} (h : TopHyp S S' ν ν' D ns ns'')
    (hb : ∀ n ∈ ns, ∀ τ ∈ n.tys, ∀ v ∈ τ.vars, v.isBnd = false)
    (hb'' : ∀ n ∈ ns'', ∀ τ ∈ n.tys, ∀ v ∈ τ.vars, v.isBnd = false) : Rel3 S S' ν ν' D ns ns'' := by
  refine ⟨h.ni, h.ni', ?_⟩
  intro n hn n'' hn'' e τ hτ v hv
  obtain ⟨τ'', hτ'', w, hw, h1, _⟩ := var_of_pair (h.ni n hn n'' hn'' e) (h.ni' n'' hn'' n hn e.symm) τ hτ v hv
  exact h.d n hn n'' hn'' e τ hτ v hv (hb n hn τ hτ v hv) w h1 (hb'' n'' hn'' τ'' hτ'' w hw)

theorem walkTop (hw : WalkHyp S S' ν r D) : (d : ATopDec) → ∀ (d'' : ATopDec) (C C'' : Ctx) (path : List Nat),
    d''.erase = d.erase → (checkTopDec C d).isSome → (checkTopDec C'' d'').isSome → d.NoFreeBnd → d''.NoFreeBnd →
    TopHyp S S' ν ν' D (nodesTopDec C path d) (nodesTopDec C'' path d'') →
    ItemsRel r D (valuesOnly d.items) (valuesOnly d''.items)
  | .value VE vb, d'', C, C'', path, he, hc, hc'', hn, hn'', h => by
    cases d'' with
    | value VE'' vb'' =>
      simp [ATopDec.erase] at he
      simp only [checkTopDec] at hc hc''
      split at hc
      · rename_i hcv
        split at hc''
        · rename_i hcv''
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hcv hcv''
          simp only [nodesTopDec, List.cons_append, List.singleton_append] at h
          have h3 := (h.mono (ms := nodesValBind (C.plusVE VE) (path ++ [0]) vb)
            (ms'' := nodesValBind (C''.plusVE VE'') (path ++ [0]) vb'')
            (fun n hn => by simp [hn]) (fun n hn => by simp [hn])).rel3
            (fun n hm τ hτ v hv => hn _ _ n hm τ hτ v hv) (fun n hm τ hτ v hv => hn'' _ _ n hm τ hτ v hv)
          have hvb := walkValBind hw vb vb'' _ _ _ he hcv.1 hcv''.1 h3
          obtain ⟨hVE, hD⟩ := RValBind.ve_rename hw.wf vb hvb
          have : VE'' = r.valEnv VE := by rw [← hcv''.2, hVE, hcv.2]
          subst this
          rw [hcv.2] at hD
          exact ⟨⟨rfl, hD, hvb⟩, trivial⟩
        · cases hc''
      · cases hc
    | typesSplit a1 a2 =>
      obtain ⟨db, tbs, e⟩ := typesSplit_erase hc''
      rw [e] at he; simp [ATopDec.erase] at he
    | types _ _ _ _ | port _ _ _ | seq _ _ => simp [ATopDec.erase] at he
  | .seq a1 a2, d'', C, C'', path, he, hc, hc'', hn, hn'', h => by
    cases d'' with
    | seq b1 b2 =>
      simp [ATopDec.erase] at he
      obtain ⟨he1, he2⟩ := he
      simp only [checkTopDec] at hc hc''
      cases hc1 : checkTopDec C a1 with
      | none => rw [hc1] at hc; cases hc
      | some p =>
        obtain ⟨E1, PE1⟩ := p
        cases hc1'' : checkTopDec C'' b1 with
        | none => rw [hc1''] at hc''; cases hc''
        | some p'' =>
          obtain ⟨E1'', PE1''⟩ := p''
          rw [hc1] at hc; rw [hc1''] at hc''
          simp only at hc hc''
          have hc2 : (checkTopDec (C.oplusE E1) a2).isSome := by
            cases h2 : checkTopDec (C.oplusE E1) a2 <;> rw [h2] at hc <;> simp_all
          have hc2'' : (checkTopDec (C''.oplusE E1'') b2).isSome := by
            cases h2 : checkTopDec (C''.oplusE E1'') b2 <;> rw [h2] at hc'' <;> simp_all
          simp only [nodesTopDec, hc1, hc1'', List.cons_append, List.singleton_append] at h
          simp only [ATopDec.items, valuesOnly, List.filter_append]
          exact ItemsRel.append
            (walkTop hw a1 b1 C C'' (path ++ [0]) he1 (by rw [hc1]; rfl) (by rw [hc1'']; rfl) hn.1 hn''.1
              (h.mono (fun n hn => by simp [hn]) (fun n hn => by simp [hn])))
            (walkTop hw a2 b2 _ _ (path ++ [1]) he2 hc2 hc2'' hn.2 hn''.2
              (h.mono (fun n hn => by simp [hn]) (fun n hn => by simp [hn])))
    | typesSplit b1 b2 =>
      obtain ⟨db, tbs, e⟩ := typesSplit_erase hc''
      rw [e] at he; simp [ATopDec.erase] at he
    | value _ _ | types _ _ _ _ | port _ _ _ => simp [ATopDec.erase] at he
  | .types TE VE db tbs, d'', C, C'', path, he, hc, hc'', _, _, _ => by
    rw [values_of_types _ C hc ⟨_, _, rfl⟩, values_of_types d'' C'' hc'' ⟨_, _, he⟩]; trivial
  | .typesSplit a1 a2, d'', C, C'', path, he, hc, hc'', _, _, _ => by
    obtain ⟨db, tbs, e⟩ := typesSplit_erase hc
    rw [values_of_types _ C hc ⟨_, _, e⟩, values_of_types d'' C'' hc'' ⟨_, _, he.trans e⟩]; trivial
  | .port x ty U, d'', C, C'', path, he, hc, hc'', _, _, _ => by
    cases d'' with
    | port _ _ _ => trivial
    | typesSplit b1 b2 =>
      obtain ⟨db, tbs, e⟩ := typesSplit_erase hc''
      rw [e] at he; simp [ATopDec.erase] at he
    | value _ _ | types _ _ _ _ | seq _ _ => simp [ATopDec.erase] at he

end Walk

/-! ## The renaming of two mutual instances -/

def BVar.rowVar? : BVar → Option RowVar
  | .ty _ => none
  | .row e => some e

/-- The free variables of the types at the nodes of `ns` that have a partner in `ns''`, that `S`
    takes to a free variable. -/
def modVars (S : Subst) (ns ns'' : List Node) : List BVar :=
  (ns.flatMap fun n => if ns''.any (fun n'' => n''.path == n.path) then n.tys.flatMap Ty.vars else []).filter
    fun v => !v.isBnd && (match S.applyVar v with | some w => !w.isBnd | none => false)

theorem mem_modVars {S : Subst} {ns ns'' : List Node} {v : BVar} :
    v ∈ modVars S ns ns'' ↔ (∃ n ∈ ns, (∃ n'' ∈ ns'', n''.path = n.path) ∧ ∃ τ ∈ n.tys, v ∈ τ.vars) ∧
      v.isBnd = false ∧ ∃ w, S.applyVar v = some w ∧ w.isBnd = false := by
  simp only [modVars, List.mem_filter, List.mem_flatMap, Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨⟨n, hn, hv⟩, hb, hw⟩
    split at hv
    · rename_i hp
      obtain ⟨n'', hn'', e⟩ := List.any_eq_true.mp hp
      obtain ⟨τ, hτ, hvτ⟩ := List.mem_flatMap.mp hv
      refine ⟨⟨n, hn, ⟨n'', hn'', by simpa using e⟩, τ, hτ, hvτ⟩, hb, ?_⟩
      split at hw
      · rename_i w hw'; exact ⟨w, hw', by simpa using hw⟩
      · cases hw
    · simp at hv
  · rintro ⟨⟨n, hn, ⟨n'', hn'', e⟩, τ, hτ, hvτ⟩, hb, w, hw, hwb⟩
    refine ⟨⟨n, hn, ?_⟩, hb, by simp [hw, hwb]⟩
    rw [if_pos (List.any_eq_true.mpr ⟨n'', hn'', by simp [e]⟩)]
    exact List.mem_flatMap.mpr ⟨τ, hτ, hvτ⟩

def tvMap (S : Subst) (α : TyVar) : TyVar :=
  match S.applyVar (.ty α) with
  | some (.ty β) => β
  | _ => α

def rvMap (S : Subst) (e : RowVar) : RowVar :=
  match S.applyVar (.row e) with
  | some (.row e') => e'
  | _ => e

def modRenaming (S : Subst) (ns ns'' : List Node) (ν : List (TyName × TyName)) : Renaming :=
  extRenaming ((modVars S ns ns'').filterMap BVar.tyVar?) (tvMap S) ((modVars S ns ns'').filterMap BVar.rowVar?)
    (rvMap S) ν

section Mod
variable {S S' : Subst} {ν ν' : List (TyName × TyName)} {ns ns'' : List Node}

/-- The variables of `modVars` come back. -/
theorem modVars_corr
    (hni : ∀ n ∈ ns, ∀ n'' ∈ ns'', n.path = n''.path → NodeInstance S (n.renameNames ν) n'')
    (hni' : ∀ n'' ∈ ns'', ∀ n ∈ ns, n''.path = n.path → NodeInstance S' (n''.renameNames ν') n) :
    ∀ v ∈ modVars S ns ns'', ∃ w, S.applyVar v = some w ∧ S'.applyVar w = some v ∧ w.isBnd = false ∧ v.isBnd = false := by
  intro v hv
  obtain ⟨⟨n, hn, ⟨n'', hn'', e⟩, τ, hτ, hvτ⟩, hb, w, hw, hwb⟩ := mem_modVars.mp hv
  obtain ⟨_, _, w', _, h1, h2⟩ := var_of_pair (hni n hn n'' hn'' e.symm) (hni' n'' hn'' n hn e) τ hτ v hvτ
  rw [hw] at h1; cases h1
  exact ⟨w, hw, h2, hwb, hb⟩

theorem modRenaming_bvar
    (hni : ∀ n ∈ ns, ∀ n'' ∈ ns'', n.path = n''.path → NodeInstance S (n.renameNames ν) n'')
    (hni' : ∀ n'' ∈ ns'', ∀ n ∈ ns, n''.path = n.path → NodeInstance S' (n''.renameNames ν') n) :
    ∀ v ∈ modVars S ns ns'', S.applyVar v = some ((modRenaming S ns ns'' ν).bvar v) ∧
      S'.applyVar ((modRenaming S ns ns'' ν).bvar v) = some v := by
  intro v hv
  obtain ⟨w, hw, hw', _, _⟩ := modVars_corr hni hni' v hv
  rcases applyVar_kind hw with ⟨a, b, rfl, rfl⟩ | ⟨e, e', rfl, rfl⟩
  · have ha : a ∈ (modVars S ns ns'').filterMap BVar.tyVar? := List.mem_filterMap.mpr ⟨_, hv, rfl⟩
    have : (modRenaming S ns ns'' ν).bvar (.ty a) = .ty b := by
      simp only [Renaming.bvar, modRenaming, extRenaming, Renaming.tvApply, extTv_on _ _ a ha, tvMap, hw]
    rw [this]; exact ⟨hw, hw'⟩
  · have he : e ∈ (modVars S ns ns'').filterMap BVar.rowVar? := List.mem_filterMap.mpr ⟨_, hv, rfl⟩
    have : (modRenaming S ns ns'' ν).bvar (.row e) = .row e' := by
      simp only [Renaming.bvar, modRenaming, extRenaming, Renaming.rvApply, extRv_on _ _ e he, rvMap, hw]
    rw [this]; exact ⟨hw, hw'⟩

theorem modRenaming_wf (hS : S.Respects) (hS' : S'.Respects)
    (hni : ∀ n ∈ ns, ∀ n'' ∈ ns'', n.path = n''.path → NodeInstance S (n.renameNames ν) n'')
    (hni' : ∀ n'' ∈ ns'', ∀ n ∈ ns, n''.path = n.path → NodeInstance S' (n''.renameNames ν') n)
    (hν : ∀ p ∈ ν, p.1 ∉ T0 ∧ p.2 ∉ T0) : (modRenaming S ns ns'' ν).WF := by
  have corr := modVars_corr hni hni'
  have ht : ∀ a ∈ (modVars S ns ns'').filterMap BVar.tyVar?, S.applyVar (.ty a) = some (.ty (tvMap S a)) ∧
      S'.applyVar (.ty (tvMap S a)) = some (.ty a) ∧ (∀ i c, a ≠ .bnd i c) ∧ (∀ i c, tvMap S a ≠ .bnd i c) := by
    intro a ha
    obtain ⟨v, hv, e⟩ := List.mem_filterMap.mp ha
    cases v with
    | row _ => cases e
    | ty a' =>
      cases e
      obtain ⟨w, hw, hw', hwb, hvb⟩ := corr _ hv
      rcases applyVar_kind hw with ⟨_, b, he, rfl⟩ | ⟨_, _, he, _⟩
      · cases he
        have hm : tvMap S a = b := by simp [tvMap, hw]
        rw [hm]
        exact ⟨hw, hw', (fun i c e => by subst e; cases hvb), (fun i c e => by subst e; cases hwb)⟩
      · cases he
  have hr : ∀ e ∈ (modVars S ns ns'').filterMap BVar.rowVar?, S.applyVar (.row e) = some (.row (rvMap S e)) ∧
      S'.applyVar (.row (rvMap S e)) = some (.row e) ∧ (∀ i, e ≠ .bnd i) ∧ (∀ i, rvMap S e ≠ .bnd i) := by
    intro e he
    obtain ⟨v, hv, e'⟩ := List.mem_filterMap.mp he
    cases v with
    | ty _ => cases e'
    | row e0 =>
      cases e'
      obtain ⟨w, hw, hw', hwb, hvb⟩ := corr _ hv
      rcases applyVar_kind hw with ⟨_, _, he, _⟩ | ⟨_, e1, he, rfl⟩
      · cases he
      · cases he
        have hm : rvMap S e = e1 := by simp [rvMap, hw]
        rw [hm]
        exact ⟨hw, hw', (fun i e2 => by subst e2; cases hvb), (fun i e2 => by subst e2; cases hwb)⟩
  apply extRenaming_wf
  · intro a ha b hb e
    have h1 := (ht a ha).2.1
    have h2 := (ht b hb).2.1
    rw [e] at h1; rw [h1] at h2; cases h2; rfl
  · intro a ha
    exact cls_of_corr hS hS' (ht a ha).1 (ht a ha).2.1
  · exact fun a ha => (ht a ha).2.2.1
  · exact fun a ha => (ht a ha).2.2.2
  · intro a ha b hb e
    have h1 := (hr a ha).2.1
    have h2 := (hr b hb).2.1
    rw [e] at h1; rw [h1] at h2; cases h2; rfl
  · exact fun a ha => (hr a ha).2.2.1
  · exact fun a ha => (hr a ha).2.2.2
  · exact hν

theorem modRenaming_walkHyp (hS : S.Respects) (hS' : S'.Respects)
    (hni : ∀ n ∈ ns, ∀ n'' ∈ ns'', n.path = n''.path → NodeInstance S (n.renameNames ν) n'')
    (hni' : ∀ n'' ∈ ns'', ∀ n ∈ ns, n''.path = n.path → NodeInstance S' (n''.renameNames ν') n)
    (hν : ∀ p ∈ ν, p.1 ∉ T0 ∧ p.2 ∉ T0) :
    WalkHyp S S' ν (modRenaming S ns ns'' ν) (· ∈ modVars S ns ns'') := by
  have hb := modRenaming_bvar hni hni'
  exact ⟨modRenaming_wf hS hS' hni hni' hν,
    fun τ hτ => apply_renameNames rfl τ (fun v hv => (hb v (hτ v hv)).1),
    fun v hv => (hb v hv).1, fun v hv => (hb v hv).2⟩

end Mod

/-! ## Two module derivations that are instances of each other -/

theorem genNames_new {B : SBasis} {a : AModule} {t : TyName} (h : t ∈ genNames B a) : t ∉ B.T := by
  unfold genNames at h
  split at h
  · rename_i B' E hr
    unfold AModule.result at hr
    split at hr
    · cases hr
    · unfold AModule.resultIn at hr
      split at hr
      · cases hr
      · split at hr
        · cases hr
        · split at hr
          · cases hr
          · cases hr
            exact (mem_diffL.mp h).2
  · simp at h

theorem nodes_instance {B : SBasis} {a' a : AModule} {ν : List (TyName × TyName)} {S : Subst}
    (h : ∀ n ∈ (nodesModule B a).map (Node.renameNames ν), ∀ n' ∈ nodesModule B a', n.path = n'.path →
      NodeInstance S n n') :
    ∀ n ∈ nodesModule B a, ∀ n' ∈ nodesModule B a', n.path = n'.path → NodeInstance S (n.renameNames ν) n' :=
  fun n hn n' hn' e => h _ (List.mem_map_of_mem hn) n' hn' e

/-- Two derivations of a module, in one basis, each an instance of the other, without `bnd`
    variables at their nodes: their value declarations are related by one renaming. -/
theorem mutualInstanceMod_items {B : SBasis} (hT0 : ∀ t ∈ T0, t ∈ B.T) {a a2 : AModule}
    (hc : checkModule B a = true) (hc2 : checkModule B a2 = true) (hn : a.NoFreeBnd) (hn2 : a2.NoFreeBnd)
    (h1 : InstanceOfMod B a2 a) (h2 : InstanceOfMod B a a2) :
    ∃ (r : Renaming) (D : BVar → Prop), r.WF ∧
      ItemsRel r D (valuesOnly ((a.body.map ATopDec.items).getD [])) (valuesOnly ((a2.body.map ATopDec.items).getD [])) := by
  obtain ⟨he, ν, hbij, S, hRes, _, _, hni⟩ := h1
  obtain ⟨_, ν', _, S', hRes', _, _, hni'⟩ := h2
  have hni1 := nodes_instance hni
  have hni2 := nodes_instance hni'
  have hν : ∀ p ∈ ν, p.1 ∉ T0 ∧ p.2 ∉ T0 := by
    intro p hp
    have e1 : p.1 ∈ genNames B a := (hbij.1 p.1).mp (List.mem_map_of_mem hp)
    have e2 : p.2 ∈ genNames B a2 := (hbij.2.1 p.2).mp (List.mem_map_of_mem hp)
    exact ⟨fun h => genNames_new e1 (hT0 _ h), fun h => genNames_new e2 (hT0 _ h)⟩
  have hw := modRenaming_walkHyp hRes hRes' hni1 (fun x hx y hy e => hni2 x hx y hy e) hν
  refine ⟨_, (· ∈ modVars S (nodesModule B a) (nodesModule B a2)), hw.wf, ?_⟩
  unfold checkModule AModule.result at hc hc2
  have himp : a2.imports = a.imports := congrArg Src.BModule.imports he
  have hbody : a2.body.map ATopDec.erase = a.body.map ATopDec.erase := congrArg Src.BModule.body he
  cases hC : importCtx B a.imports with
  | none => rw [hC] at hc; cases hc
  | some C =>
    have hC2 : importCtx B a2.imports = some C := by rw [himp, hC]
    rw [hC] at hc; rw [hC2] at hc2
    simp only at hc hc2
    have hn1 : nodesModule B a = match a.body with | some d => nodesTopDec C [] d | none => [] := by
      unfold nodesModule; rw [hC]; cases a.body <;> rfl
    have hn3 : nodesModule B a2 = match a2.body with | some d => nodesTopDec C [] d | none => [] := by
      unfold nodesModule; rw [hC2]; cases a2.body <;> rfl
    cases hb : a.body with
    | none =>
      rw [hb] at hbody
      cases hb2 : a2.body with
      | none => trivial
      | some _ => rw [hb2] at hbody; cases hbody
    | some d =>
      rw [hb] at hbody
      cases hb2 : a2.body with
      | none => rw [hb2] at hbody; cases hbody
      | some d2 =>
        rw [hb2] at hbody
        simp only [Option.map_some, Option.some.injEq] at hbody
        have hcd : (checkTopDec C d).isSome := by
          unfold AModule.resultIn at hc; rw [hb] at hc; simp only [checkTopDecOpt] at hc
          cases h : checkTopDec C d <;> rw [h] at hc <;> simp_all
        have hcd2 : (checkTopDec C d2).isSome := by
          unfold AModule.resultIn at hc2; rw [hb2] at hc2; simp only [checkTopDecOpt] at hc2
          cases h : checkTopDec C d2 <;> rw [h] at hc2 <;> simp_all
        rw [hb] at hn1; rw [hb2] at hn3
        simp only [Option.map_some, Option.getD_some]
        apply walkTop (ν' := ν') hw d d2 C C [] hbody hcd hcd2 (hn d hb) (hn2 d2 hb2)
        refine ⟨?_, ?_, ?_⟩
        · intro n hk m hm e
          exact hni1 n (by rw [hn1]; exact hk) m (by rw [hn3]; exact hm) e
        · intro m hm n hk e
          exact hni2 m (by rw [hn3]; exact hm) n (by rw [hn1]; exact hk) e
        · intro n hk m hm e τ hτ v hv hvb w hw' hwb
          exact mem_modVars.mpr ⟨⟨n, by rw [hn1]; exact hk, ⟨m, by rw [hn3]; exact hm, e.symm⟩, τ, hτ, hv⟩,
            hvb, w, hw', hwb⟩

end StandardElm.Stat
