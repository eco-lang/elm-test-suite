/-
  A Standard Definition of Elm? Mechanisation: mutual instances are renamings, second layer (plan
  step 10, `mutualInstanceMod_renaming`): from the clauses of two instances at the nodes of two
  derivations of one phrase, the relation of RenameSpec.lean.

  The walk goes down both annotated phrases together (they erase to the same bare phrase). At each
  pair of corresponding nodes (the same path), the substitution `S` takes the types of one node,
  with its type names renamed, to the other's, and `S'` back; `S` takes each variable of the
  derivation's types (`D`) to the variable the renaming `r` gives it (`WalkHyp`), so every type
  at a node of one is the image by `r` of the type at the other (`tys_rel`), and the U of the two
  nodes agree on `D` (`u_rel`). The value environments of declarations and patterns follow, those
  of declarations by the checker (`vb.ve = VE`).
-/
import StandardElmMech.Stat.MutualInstance

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)

/-! ## Environments -/

theorem Renaming.valEnv_modify (r : Renaming) (f g : ValEnv) :
    r.valEnv (FMap.modify f g) = FMap.modify (r.valEnv f) (r.valEnv g) := by
  unfold FMap.modify Renaming.valEnv
  rw [List.map_append, List.filter_map]
  congr 2
  · apply List.filter_congr; intro p _
    simp only [Function.comp_apply, FMap.keys, List.map_map]
    rfl

theorem Renaming.valEnv_foldl (r : Renaming) : ∀ (fs : List ValEnv) (acc : ValEnv),
    r.valEnv (fs.foldl FMap.modify acc) = (fs.map r.valEnv).foldl FMap.modify (r.valEnv acc)
  | [], _ => rfl
  | f :: fs, acc => by
    simp only [List.foldl_cons, List.map_cons]
    rw [Renaming.valEnv_foldl r fs, Renaming.valEnv_modify]

theorem Renaming.valEnv_plusAll (r : Renaming) (fs : List ValEnv) :
    r.valEnv (FMap.plusAll fs) = FMap.plusAll (fs.map r.valEnv) := by
  unfold FMap.plusAll; rw [Renaming.valEnv_foldl]; rfl

theorem mem_modify {f g : ValEnv} {q : String × Scheme × IdStatus} (h : q ∈ FMap.modify f g) : q ∈ f ∨ q ∈ g := by
  unfold FMap.modify at h
  rcases List.mem_append.mp h with h | h
  · exact .inr h
  · exact .inl (List.mem_filter.mp h).1

theorem mem_foldl_modify : ∀ {fs : List ValEnv} {acc : ValEnv} {q : String × Scheme × IdStatus},
    q ∈ fs.foldl FMap.modify acc → q ∈ acc ∨ ∃ f ∈ fs, q ∈ f
  | [], _, _, h => .inl h
  | f :: fs, acc, q, h => by
    simp only [List.foldl_cons] at h
    rcases mem_foldl_modify h with h | ⟨f', hf', hq⟩
    · rcases mem_modify h with h | h
      · exact .inl h
      · exact .inr ⟨f, List.mem_cons_self .., h⟩
    · exact .inr ⟨f', List.mem_cons_of_mem _ hf', hq⟩

/-! ## The hypotheses of the walk -/

/-- Two node lists related by two instances, the variables of the first's types in `D`. -/
structure Rel3 (S S' : Subst) (ν ν' : List (TyName × TyName)) (D : BVar → Prop) (ns ns'' : List Node) : Prop where
  ni : ∀ n ∈ ns, ∀ n'' ∈ ns'', n.path = n''.path → NodeInstance S (n.renameNames ν) n''
  ni' : ∀ n'' ∈ ns'', ∀ n ∈ ns, n''.path = n.path → NodeInstance S' (n''.renameNames ν') n
  nd : ∀ n ∈ ns, ∀ n'' ∈ ns'', n.path = n''.path → ∀ τ ∈ n.tys, ∀ v ∈ τ.vars, D v

theorem Rel3.mono {S S' : Subst} {ν ν' : List (TyName × TyName)} {D : BVar → Prop} {ns ns'' ms ms'' : List Node}
    (h : Rel3 S S' ν ν' D ns ns'') (hm : ∀ n ∈ ms, n ∈ ns) (hm'' : ∀ n ∈ ms'', n ∈ ns'') : Rel3 S S' ν ν' D ms ms'' :=
  ⟨fun n hn n'' hn'' e => h.ni n (hm n hn) n'' (hm'' n'' hn'') e,
   fun n'' hn'' n hn e => h.ni' n'' (hm'' n'' hn'') n (hm n hn) e,
   fun n hn n'' hn'' e => h.nd n (hm n hn) n'' (hm'' n'' hn'') e⟩

/-- What the walk needs of `S`, `S'` and `r` on `D`. -/
structure WalkHyp (S S' : Subst) (ν : List (TyName × TyName)) (r : Renaming) (D : BVar → Prop) : Prop where
  wf : r.WF
  ty : ∀ τ : Ty, (∀ v ∈ τ.vars, D v) → S.apply (Ty.renameNames ν τ) = some (r.ty τ)
  var : ∀ v, D v → S.applyVar v = some (r.bvar v)
  var' : ∀ v, D v → S'.applyVar (r.bvar v) = some v

theorem mapM_apply_map {S : Subst} {g h : Ty → Ty} :
    ∀ (l : List Ty), (∀ x ∈ l, S.apply (g x) = some (h x)) → (l.map g).mapM S.apply = some (l.map h)
  | [], _ => rfl
  | x :: xs, hx => by
    simp only [List.map_cons, List.mapM_cons, hx x (List.mem_cons_self ..),
      mapM_apply_map xs (fun y hy => hx y (List.mem_cons_of_mem _ hy))]
    rfl

theorem mem_of_mapM {α β : Type} {f : α → Option β} {x : α} {y : β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → x ∈ l → f x = some y → y ∈ l'
  | [], _, _, h, _ => by simp at h
  | a :: as, l', hm, hx, hf => by
    simp only [List.mapM_cons] at hm
    cases h1 : f a <;> cases h2 : as.mapM f <;> simp [h1, h2] at hm
    subst hm
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [h1] at hf; cases hf; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (mem_of_mapM h2 hx hf)

section Walk
variable {S S' : Subst} {ν ν' : List (TyName × TyName)} {r : Renaming} {D : BVar → Prop}

theorem tys_rel (hw : WalkHyp S S' ν r D) {n n'' : Node} (hi : NodeInstance S (n.renameNames ν) n'')
    (hd : ∀ τ ∈ n.tys, ∀ v ∈ τ.vars, D v) : n''.tys = n.tys.map r.ty := by
  have h := hi.2.1
  simp only [Node.renameNames] at h
  rw [mapM_apply_map n.tys (fun x hx => hw.ty x (hd x hx))] at h
  exact (Option.some.inj h).symm

theorem u_rel (hw : WalkHyp S S' ν r D) {n n'' : Node} (hi : NodeInstance S (n.renameNames ν) n'')
    (hi' : NodeInstance S' (n''.renameNames ν') n) : ∀ v, D v → (v ∈ n.U ↔ r.bvar v ∈ n''.U) := by
  intro v hv
  obtain ⟨vs, hm, hs⟩ := hi.1
  obtain ⟨vs', hm', hs'⟩ := hi'.1
  simp only [Node.renameNames] at hm hm'
  constructor
  · intro hu; exact (hs _).mp (mem_of_mapM hm hu (hw.var v hv))
  · intro hu; exact (hs' _).mp (mem_of_mapM hm' hu (hw.var' v hv))

/-- The head node of each list. -/
theorem Rel3.head (h : Rel3 S S' ν ν' D (n :: ns) (n'' :: ns'')) (e : n.path = n''.path) :
    NodeInstance S (n.renameNames ν) n'' ∧ NodeInstance S' (n''.renameNames ν') n ∧
      ∀ τ ∈ n.tys, ∀ v ∈ τ.vars, D v :=
  ⟨h.ni n (List.mem_cons_self ..) n'' (List.mem_cons_self ..) e,
   h.ni' n'' (List.mem_cons_self ..) n (List.mem_cons_self ..) e.symm,
   h.nd n (List.mem_cons_self ..) n'' (List.mem_cons_self ..) e⟩

end Walk

section Walk
variable {S S' : Subst} {ν ν' : List (TyName × TyName)} {r : Renaming} {D : BVar → Prop}

theorem Rel3.head_ty (hw : WalkHyp S S' ν r D) {p : List Nat} {U U'' : List BVar} {τ τ'' : Ty} {ts ts'' : List Ty}
    {s s'' : List Scheme} {ns ns'' : List Node}
    (h : Rel3 S S' ν ν' D (⟨p, U, τ :: ts, s⟩ :: ns) (⟨p, U'', τ'' :: ts'', s''⟩ :: ns'')) :
    τ'' = r.ty τ ∧ ts'' = ts.map r.ty ∧ (∀ v ∈ τ.vars, D v) ∧ (∀ x ∈ ts, ∀ v ∈ x.vars, D v) := by
  obtain ⟨h1, _, h3⟩ := h.head rfl
  have := tys_rel hw h1 h3
  simp only [List.map_cons, List.cons.injEq] at this
  exact ⟨this.1, this.2, h3 τ (List.mem_cons_self ..), fun x hx => h3 x (List.mem_cons_of_mem _ hx)⟩

/-- What the walk gives of a pattern: its type and value environment are the images. -/
def PatOK (r : Renaming) (D : BVar → Prop) (ty ty'' : Ty) (ve ve'' : ValEnv) : Prop :=
  ty'' = r.ty ty ∧ ve'' = r.valEnv ve ∧ ∀ q ∈ ve, ∀ v ∈ q.2.1.body.vars, D v

def VeOK (r : Renaming) (D : BVar → Prop) (ve ve'' : ValEnv) : Prop :=
  ve'' = r.valEnv ve ∧ ∀ q ∈ ve, ∀ v ∈ q.2.1.body.vars, D v

theorem VeOK.modify {ve1 ve1'' ve2 ve2'' : ValEnv} (h1 : VeOK r D ve1 ve1'') (h2 : VeOK r D ve2 ve2'') :
    VeOK r D (FMap.modify ve1 ve2) (FMap.modify ve1'' ve2'') :=
  ⟨by rw [h1.1, h2.1, Renaming.valEnv_modify], fun q hq => by
    rcases mem_modify hq with hq | hq
    · exact h1.2 q hq
    · exact h2.2 q hq⟩

theorem VeOK.nil : VeOK r D [] [] := ⟨rfl, by simp⟩

theorem VeOK.single {x : String} {τ : Ty} (hd : ∀ v ∈ τ.vars, D v) :
    VeOK r D [(x, (mono τ, .v))] [(x, (mono (r.ty τ), .v))] :=
  ⟨rfl, fun q hq => by simp only [List.mem_singleton] at hq; subst hq; exact hd⟩

theorem VeOK.plusAll {l l'' : List ValEnv} (h : l'' = l.map r.valEnv) (hd : ∀ ve ∈ l, ∀ q ∈ ve, ∀ v ∈ q.2.1.body.vars, D v) :
    VeOK r D (FMap.plusAll l) (FMap.plusAll l'') :=
  ⟨by rw [h, Renaming.valEnv_plusAll], fun q hq => by
    unfold FMap.plusAll at hq
    rcases mem_foldl_modify hq with hq | ⟨f, hf, hq⟩
    · simp at hq
    · exact hd f hf q hq⟩

theorem mem_app_l {α : Type} {x : α} {a b : List α} (h : x ∈ a) : x ∈ a ++ b := List.mem_append_left _ h
theorem mem_app_r {α : Type} {x : α} {a b : List α} (h : x ∈ b) : x ∈ a ++ b := List.mem_append_right _ h

mutual
theorem walkAtPat (hw : WalkHyp S S' ν r D) : (p : AAtPat) → ∀ (p'' : AAtPat) (U U'' : List BVar) (path : List Nat),
    p''.erase = p.erase → Rel3 S S' ν ν' D (nodesAtPat U path p) (nodesAtPat U'' path p'') →
    p''.ty = r.ty p.ty ∧ VeOK r D p.ve p''.ve
  | .wild τ, p'', U, U'', path, he, h => by
    cases p'' <;> simp [AAtPat.erase] at he
    simp only [nodesAtPat, AAtPat.ty, AAtPat.ve, List.map_nil, List.append_nil] at h
    exact ⟨(h.head_ty hw).1, VeOK.nil⟩
  | .scon sc τ, p'', U, U'', path, he, h => by
    cases p'' <;> simp [AAtPat.erase] at he
    simp only [nodesAtPat, AAtPat.ty, AAtPat.ve, List.map_nil, List.append_nil] at h
    exact ⟨(h.head_ty hw).1, VeOK.nil⟩
  | .con lc inst τ, p'', U, U'', path, he, h => by
    cases p'' <;> simp [AAtPat.erase] at he
    simp only [nodesAtPat, AAtPat.ty, AAtPat.ve, List.map_nil, List.append_nil] at h
    exact ⟨(h.head_ty hw).1, VeOK.nil⟩
  | .nil τ, p'', U, U'', path, he, h => by
    cases p'' <;> simp [AAtPat.erase] at he
    simp only [nodesAtPat, AAtPat.ty, AAtPat.ve, List.map_nil, List.append_nil] at h
    exact ⟨(h.head_ty hw).1, VeOK.nil⟩
  | .unit, p'', U, U'', path, he, h => by
    cases p'' <;> simp [AAtPat.erase] at he
    simp only [nodesAtPat, AAtPat.ty, AAtPat.ve, List.map_nil, List.append_nil] at h
    exact ⟨(h.head_ty hw).1, VeOK.nil⟩
  | .var x τ, p'', U, U'', path, he, h => by
    cases p'' <;> simp [AAtPat.erase] at he
    subst he
    simp only [nodesAtPat, AAtPat.ty, AAtPat.ve, List.map_cons, List.map_nil, List.cons_append, List.nil_append] at h
    obtain ⟨e1, _, d1, _⟩ := h.head_ty hw
    subst e1
    exact ⟨rfl, VeOK.single d1⟩
  | .tuple p1 p2 p3, p'', U, U'', path, he, h => by
    cases p'' <;> simp [AAtPat.erase] at he
    rename_i q1 q2 q3
    obtain ⟨he1, he2, he3⟩ := he
    simp only [nodesAtPat, List.cons_append, List.singleton_append] at h
    have h1 := walkPat hw p1 q1 U U'' (path ++ [0]) he1
      (h.mono (fun n hn => by simp [mem_app_l, mem_app_r, hn]) (fun n hn => by simp [mem_app_l, mem_app_r, hn]))
    have h2 := walkPat hw p2 q2 U U'' (path ++ [1]) he2
      (h.mono (fun n hn => by simp [mem_app_l, mem_app_r, hn]) (fun n hn => by simp [mem_app_l, mem_app_r, hn]))
    have h3 := walkPatOpt hw p3 q3 U U'' (path ++ [2]) he3
      (h.mono (fun n hn => by simp [mem_app_l, mem_app_r, hn]) (fun n hn => by simp [mem_app_l, mem_app_r, hn]))
    exact ⟨(h.head_ty hw).1, by simp only [AAtPat.ve]; exact (h1.2.modify h2.2).modify h3⟩
  | .record row τ, p'', U, U'', path, he, h => by
    cases p'' <;> simp [AAtPat.erase] at he
    rename_i row'' τ''
    simp only [nodesAtPat, List.cons_append, List.singleton_append] at h
    have h1 := walkPatRowOpt hw row row'' U U'' (path ++ [0]) he
      (h.mono (fun n hn => by simp [hn]) (fun n hn => by simp [hn]))
    exact ⟨(h.head_ty hw).1, by simp only [AAtPat.ve]; exact h1⟩
  | .paren q, p'', U, U'', path, he, h => by
    cases p'' <;> simp [AAtPat.erase] at he
    rename_i q''
    simp only [nodesAtPat, List.cons_append, List.singleton_append] at h
    have h1 := walkPat hw q q'' U U'' (path ++ [0]) he (h.mono (fun n hn => by simp [hn]) (fun n hn => by simp [hn]))
    exact ⟨(h.head_ty hw).1, by simp only [AAtPat.ve]; exact h1.2⟩
theorem walkPatRow (hw : WalkHyp S S' ν r D) : (row : APatRow) → ∀ (row'' : APatRow) (U U'' : List BVar)
    (path : List Nat), row''.erase = row.erase → Rel3 S S' ν ν' D (nodesPatRow U path row) (nodesPatRow U'' path row'') →
    VeOK r D row.ve row''.ve
  | .field l τ rest, row'', U, U'', path, he, h => by
    cases row'' with
    | field l'' τ'' rest'' =>
      simp [APatRow.erase] at he
      obtain ⟨rfl, he2⟩ := he
      simp only [nodesPatRow, List.cons_append, List.singleton_append] at h
      obtain ⟨e1, _, d1, _⟩ := h.head_ty hw
      subst e1
      have h1 := walkPatRowOpt hw rest rest'' U U'' (path ++ [0]) he2
        (h.mono (fun n hn => by simp [hn]) (fun n hn => by simp [hn]))
      simp only [APatRow.ve]
      exact (VeOK.single d1).modify h1
theorem walkPatRowOpt (hw : WalkHyp S S' ν r D) : (row : Option APatRow) → ∀ (row'' : Option APatRow)
    (U U'' : List BVar) (path : List Nat), APatRow.eraseOpt row'' = APatRow.eraseOpt row →
    Rel3 S S' ν ν' D (nodesPatRowOpt U path row) (nodesPatRowOpt U'' path row'') →
    VeOK r D (APatRow.veOpt row) (APatRow.veOpt row'')
  | none, row'', _, _, _, he, _ => by cases row'' <;> simp [APatRow.eraseOpt] at he; exact VeOK.nil
  | some row, row'', U, U'', path, he, h => by
    cases row'' <;> simp [APatRow.eraseOpt] at he
    rename_i row''
    simp only [nodesPatRowOpt] at h
    simp only [APatRow.veOpt]
    exact walkPatRow hw row row'' U U'' path he h
theorem walkPat (hw : WalkHyp S S' ν r D) : (p : APat) → ∀ (p'' : APat) (U U'' : List BVar) (path : List Nat),
    p''.erase = p.erase → Rel3 S S' ν ν' D (nodesPat U path p) (nodesPat U'' path p'') →
    p''.ty = r.ty p.ty ∧ VeOK r D p.ve p''.ve
  | .atpat a, p'', U, U'', path, he, h => by
    cases p'' <;> simp [APat.erase] at he
    rename_i a''
    simp only [nodesPat, List.cons_append, List.singleton_append] at h
    have h1 := walkAtPat hw a a'' U U'' (path ++ [0]) he (h.mono (fun n hn => by simp [hn]) (fun n hn => by simp [hn]))
    exact ⟨(h.head_ty hw).1, by simp only [APat.ve]; exact h1.2⟩
  | .con lc inst args τ, p'', U, U'', path, he, h => by
    cases p'' <;> simp [APat.erase] at he
    rename_i lc'' inst'' args'' τ''
    obtain ⟨rfl, he2⟩ := he
    simp only [nodesPat, List.cons_append, List.singleton_append] at h
    have h1 := walkAtPats hw args args'' U U'' path 0 he2 (h.mono (fun n hn => by simp [hn]) (fun n hn => by simp [hn]))
    exact ⟨(h.head_ty hw).1, by simp only [APat.ve]; exact VeOK.plusAll h1.1 h1.2⟩
  | .cons p1 p2, p'', U, U'', path, he, h => by
    cases p'' <;> simp [APat.erase] at he
    rename_i q1 q2
    obtain ⟨he1, he2⟩ := he
    simp only [nodesPat, List.cons_append, List.singleton_append] at h
    have h1 := walkPat hw p1 q1 U U'' (path ++ [0]) he1
      (h.mono (fun n hn => by simp [mem_app_l, mem_app_r, hn]) (fun n hn => by simp [mem_app_l, mem_app_r, hn]))
    have h2 := walkPat hw p2 q2 U U'' (path ++ [1]) he2
      (h.mono (fun n hn => by simp [mem_app_l, mem_app_r, hn]) (fun n hn => by simp [mem_app_l, mem_app_r, hn]))
    exact ⟨(h.head_ty hw).1, by simp only [APat.ve]; exact h1.2.modify h2.2⟩
  | .as q x, p'', U, U'', path, he, h => by
    cases p'' <;> simp [APat.erase] at he
    rename_i q'' x''
    obtain ⟨he1, rfl⟩ := he
    simp only [nodesPat, List.cons_append, List.singleton_append] at h
    obtain ⟨e1, _, d1, _⟩ := h.head_ty hw
    have h1 := walkPat hw q q'' U U'' (path ++ [0]) he1 (h.mono (fun n hn => by simp [hn]) (fun n hn => by simp [hn]))
    refine ⟨e1, ?_⟩
    simp only [APat.ve, APat.ty] at e1 d1 ⊢
    rw [e1]
    exact h1.2.modify (VeOK.single d1)
theorem walkPatOpt (hw : WalkHyp S S' ν r D) : (p : Option APat) → ∀ (p'' : Option APat) (U U'' : List BVar)
    (path : List Nat), APat.eraseOpt p'' = APat.eraseOpt p → Rel3 S S' ν ν' D (nodesPatOpt U path p) (nodesPatOpt U'' path p'') →
    VeOK r D (APat.veOpt p) (APat.veOpt p'')
  | none, p'', _, _, _, he, _ => by cases p'' <;> simp [APat.eraseOpt] at he; exact VeOK.nil
  | some p, p'', U, U'', path, he, h => by
    cases p'' <;> simp [APat.eraseOpt] at he
    rename_i p''
    simp only [nodesPatOpt] at h
    simp only [APat.veOpt]
    exact (walkPat hw p p'' U U'' path he h).2
theorem walkAtPats (hw : WalkHyp S S' ν r D) : (ps : List AAtPat) → ∀ (ps'' : List AAtPat) (U U'' : List BVar)
    (path : List Nat) (i : Nat), AAtPat.eraseList ps'' = AAtPat.eraseList ps →
    Rel3 S S' ν ν' D (nodesAtPats U path i ps) (nodesAtPats U'' path i ps'') →
    AAtPat.veList ps'' = (AAtPat.veList ps).map r.valEnv ∧ ∀ ve ∈ AAtPat.veList ps, ∀ q ∈ ve, ∀ v ∈ q.2.1.body.vars, D v
  | [], ps'', _, _, _, _, he, _ => by
    cases ps'' <;> simp [AAtPat.eraseList] at he; exact ⟨rfl, by simp [AAtPat.veList]⟩
  | p :: ps, ps'', U, U'', path, i, he, h => by
    cases ps'' <;> simp [AAtPat.eraseList] at he
    rename_i p'' ps''
    obtain ⟨he1, he2⟩ := he
    simp only [nodesAtPats] at h
    have h1 := walkAtPat hw p p'' U U'' (path ++ [i]) he1 (h.mono (fun n hn => by simp [hn]) (fun n hn => by simp [hn]))
    have h2 := walkAtPats hw ps ps'' U U'' path (i + 1) he2 (h.mono (fun n hn => by simp [hn]) (fun n hn => by simp [hn]))
    refine ⟨by simp only [AAtPat.veList, List.map_cons, h1.2.1, h2.1], ?_⟩
    intro ve hve
    simp only [AAtPat.veList, List.mem_cons] at hve
    rcases hve with rfl | hve
    · exact h1.2.2
    · exact h2.2 ve hve
end

end Walk

/-! ## Schemes of value bindings -/

theorem merge_mem {a b c : Row} (h : Row.merge a b = some c) : ∀ x ∈ c, x ∈ a ∨ x ∈ b := by
  unfold Row.merge at h
  generalize a.length + b.length = n at h
  induction n generalizing a b c with
  | zero =>
    cases a <;> cases b <;> simp [Row.mergeF] at h <;> subst h <;> simp
  | succ n ih =>
    cases a with
    | nil => simp [Row.mergeF] at h; subst h; simp
    | cons p1 r1 =>
      cases b with
      | nil => simp [Row.mergeF] at h; subst h; simp
      | cons p2 r2 =>
        obtain ⟨l1, τ1⟩ := p1
        obtain ⟨l2, τ2⟩ := p2
        simp only [Row.mergeF] at h
        split at h
        · cases h
        · split at h
          · cases hm : Row.mergeF n r1 ((l2, τ2) :: r2) <;> rw [hm] at h <;> simp at h
            subst h
            intro x hx
            simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · exact .inl (List.mem_cons_self ..)
            · rcases ih hm x hx with h | h
              · exact .inl (List.mem_cons_of_mem _ h)
              · exact .inr h
          · cases hm : Row.mergeF n ((l1, τ1) :: r1) r2 <;> rw [hm] at h <;> simp at h
            subst h
            intro x hx
            simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · exact .inr (List.mem_cons_self ..)
            · rcases ih hm x hx with h | h
              · exact .inl h
              · exact .inr (List.mem_cons_of_mem _ h)

theorem mem_rowVars {x : BVar} : ∀ {ρ : Row}, x ∈ Ty.rowVars ρ ↔ ∃ p ∈ ρ, x ∈ p.2.vars
  | [] => by simp [Ty.rowVars]
  | (l, τ) :: rest => by
    simp only [Ty.rowVars, List.mem_append, mem_rowVars, List.mem_cons]
    constructor
    · rintro (h | ⟨p, hp, hx⟩)
      · exact ⟨(l, τ), .inl rfl, h⟩
      · exact ⟨p, .inr hp, hx⟩
    · rintro ⟨p, rfl | hp, hx⟩
      · exact .inl hx
      · exact .inr ⟨p, hp, hx⟩

/-- A substitution whose range has only bound variables adds no free variable. -/
def BndRange (S : Subst) : Prop :=
  (∀ p ∈ S.ty, ∀ v ∈ p.2.vars, v.isBnd = true) ∧
  (∀ p ∈ S.row, (∀ v ∈ Ty.rowVars p.2.1, v.isBnd = true) ∧ ∀ e, p.2.2 = some e → (BVar.row e).isBnd = true)

mutual
theorem apply_vars_sub {S : Subst} (hS : BndRange S) :
    (τ : Ty) → ∀ {τ' : Ty}, S.apply τ = some τ' → ∀ v ∈ τ'.vars, v ∈ τ.vars ∨ v.isBnd = true
  | .var a, τ', h, v, hv => by
    simp only [Subst.apply, Option.some.injEq] at h
    subst h
    cases hf : FMap.find? S.ty a with
    | none => simp [hf, Ty.vars] at hv; exact .inl (by simp [Ty.vars, hv])
    | some σ => simp [hf] at hv; exact .inr (hS.1 _ (find?_mem hf) v hv)
  | .record ρ none, τ', h, v, hv => by
    simp only [Subst.apply] at h
    cases h1 : S.applyRow ρ <;> rw [h1] at h <;> simp at h
    subst h
    rcases applyRow_vars_sub hS ρ h1 v (by simpa [Ty.vars] using hv) with h | h
    · exact .inl (by simpa [Ty.vars] using h)
    · exact .inr h
  | .record ρ (some e), τ', h, v, hv => by
    simp only [Subst.apply] at h
    cases h1 : S.applyRow ρ with
    | none => rw [h1] at h; cases h
    | some ρ1 =>
      rw [h1] at h; simp only at h
      cases h2 : FMap.find? S.row e with
      | none =>
        rw [h2] at h; simp only [Option.some.injEq] at h; subst h
        simp only [Ty.vars, List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | rfl
        · rcases applyRow_vars_sub hS ρ h1 v hv with h | h
          · exact .inl (by simp [Ty.vars, h])
          · exact .inr h
        · exact .inl (by simp [Ty.vars])
      | some p =>
        obtain ⟨ρ2, tl⟩ := p
        rw [h2] at h; simp only at h
        cases h3 : Row.merge ρ1 ρ2 with
        | none => rw [h3] at h; cases h
        | some ρ3 =>
          rw [h3] at h; simp only [Option.some.injEq] at h; subst h
          have hb := hS.2 _ (find?_mem h2)
          have hrow : ∀ x ∈ Ty.rowVars ρ3, x ∈ (Ty.record ρ (some e)).vars ∨ x.isBnd = true := by
            intro x hx
            obtain ⟨q, hq, hxq⟩ := mem_rowVars.mp hx
            rcases merge_mem h3 q hq with hq | hq
            · rcases applyRow_vars_sub hS ρ h1 x (mem_rowVars.mpr ⟨q, hq, hxq⟩) with h | h
              · exact .inl (by simp [Ty.vars, h])
              · exact .inr h
            · exact .inr (hb.1 x (mem_rowVars.mpr ⟨q, hq, hxq⟩))
          cases tl with
          | none => exact hrow v (by simpa [Ty.vars] using hv)
          | some e' =>
            simp only [Ty.vars, List.mem_append, List.mem_singleton] at hv
            rcases hv with hv | rfl
            · exact hrow v hv
            · exact .inr (hb.2 e' rfl)
  | .fn a b, τ', h, v, hv => by
    simp only [Subst.apply] at h
    cases h1 : S.apply a <;> cases h2 : S.apply b <;> rw [h1, h2] at h <;> simp at h
    subst h
    simp only [Ty.vars, List.mem_append] at hv ⊢
    rcases hv with hv | hv
    · rcases apply_vars_sub hS a h1 v hv with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · rcases apply_vars_sub hS b h2 v hv with h | h
      · exact .inl (.inr h)
      · exact .inr h
  | .con as t, τ', h, v, hv => by
    simp only [Subst.apply] at h
    cases h1 : S.applyList as <;> rw [h1] at h <;> simp at h
    subst h
    simp only [Ty.vars] at hv ⊢
    exact applyList_vars_sub hS as h1 v hv
theorem applyRow_vars_sub {S : Subst} (hS : BndRange S) :
    (ρ : Row) → ∀ {ρ' : Row}, S.applyRow ρ = some ρ' → ∀ v ∈ Ty.rowVars ρ', v ∈ Ty.rowVars ρ ∨ v.isBnd = true
  | [], ρ', h, v, hv => by simp [Subst.applyRow] at h; subst h; simp [Ty.rowVars] at hv
  | (l, τ) :: rest, ρ', h, v, hv => by
    simp only [Subst.applyRow] at h
    cases h1 : S.apply τ <;> cases h2 : S.applyRow rest <;> rw [h1, h2] at h <;> simp at h
    subst h
    simp only [Ty.rowVars, List.mem_append] at hv ⊢
    rcases hv with hv | hv
    · rcases apply_vars_sub hS τ h1 v hv with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · rcases applyRow_vars_sub hS rest h2 v hv with h | h
      · exact .inl (.inr h)
      · exact .inr h
theorem applyList_vars_sub {S : Subst} (hS : BndRange S) :
    (l : List Ty) → ∀ {l' : List Ty}, S.applyList l = some l' → ∀ v ∈ Ty.listVars l', v ∈ Ty.listVars l ∨ v.isBnd = true
  | [], l', h, v, hv => by simp [Subst.applyList] at h; subst h; simp [Ty.listVars] at hv
  | τ :: rest, l', h, v, hv => by
    simp only [Subst.applyList] at h
    cases h1 : S.apply τ <;> cases h2 : S.applyList rest <;> rw [h1, h2] at h <;> simp at h
    subst h
    simp only [Ty.listVars, List.mem_append] at hv ⊢
    rcases hv with hv | hv
    · rcases apply_vars_sub hS τ h1 v hv with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · rcases applyList_vars_sub hS rest h2 v hv with h | h
      · exact .inl (.inr h)
      · exact .inr h
end

theorem renumber_bndRange : ∀ (k : Bool) (i : Nat) (l : List BVar), BndRange (renumber k i l).1
  | _, _, [] => ⟨by simp [renumber, Subst.id], by simp [renumber, Subst.id]⟩
  | k, i, .ty a :: vs => by
    have ih := renumber_bndRange k (i + 1) vs
    refine ⟨?_, ?_⟩
    · simp only [renumber, List.mem_cons]
      rintro p (rfl | hp) v hv
      · simp [Ty.vars] at hv; subst hv; rfl
      · exact ih.1 p hp v hv
    · simp only [renumber]; exact ih.2
  | k, i, .row e :: vs => by
    have ih := renumber_bndRange k (i + 1) vs
    refine ⟨?_, ?_⟩
    · simp only [renumber]; exact ih.1
    · simp only [renumber, List.mem_cons]
      rintro p (rfl | hp)
      · exact ⟨by simp [Ty.rowVars], fun e' he' => by cases he'; rfl⟩
      · exact ih.2 p hp

theorem canon_tyvars_sub (σ : Scheme) : ∀ v ∈ (Scheme.canon σ).tyvars, v ∈ σ.body.vars := by
  intro v hv
  simp only [Scheme.canon, Scheme.tyvars, mem_diffL] at hv
  obtain ⟨hv, _⟩ := hv
  have hnb : v.isBnd = false := by
    simp only [Ty.tyvars, List.mem_filter] at hv; simpa using hv.2
  have hvv := mem_vars_of_tyvars hv
  cases h : Subst.apply (renumber true 0 (canonVars σ.bound σ.body)).1 σ.body with
  | none => rw [h] at hvv; exact hvv
  | some τ' =>
    rw [h] at hvv
    rcases apply_vars_sub (renumber_bndRange _ _ _) σ.body h v hvv with h' | h'
    · exact h'
    · rw [hnb] at h'; cases h'

theorem scheme_tyvars_sub (σ : Scheme) : ∀ v ∈ σ.tyvars, v ∈ σ.body.vars := fun v hv =>
  mem_vars_of_tyvars (mem_diffL.mp hv).1

theorem canon_congr {b1 b2 : List BVar} {body : Ty} (h : canonVars b1 body = canonVars b2 body) :
    Scheme.canon ⟨b1, body⟩ = Scheme.canon ⟨b2, body⟩ := by
  unfold Scheme.canon; simp only [h]

theorem annScheme_rename {r : Renaming} (hr : r.WF) {D : BVar → Prop} {U U'' : List BVar} {τ : Ty}
    (hτ : ∀ v ∈ τ.vars, D v) (hU : ∀ v, D v → (v ∈ U ↔ r.bvar v ∈ U'')) :
    annScheme U'' (r.ty τ) = r.scheme (annScheme U τ) := by
  unfold annScheme
  rw [← canon_rename hr]
  simp only [Renaming.scheme]
  apply canon_congr
  apply canonVars_congr
  · intro y hy
    rw [vars_rename] at hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    simp only [List.mem_filter, decide_eq_true_eq, vars_rename, mem_map_inj hr.bvar_inj]
    rw [← hU z (hτ z hz)]
  · rw [List.filter_eq_nil_iff.mpr, List.filter_eq_nil_iff.mpr]
    · intro a ha
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
      have : z ∈ τ.vars := by simpa using (List.mem_filter.mp hz).2
      simp [vars_rename, mem_map_inj hr.bvar_inj, this]
    · intro a ha
      have : a ∈ (r.ty τ).vars := by simpa using (List.mem_filter.mp ha).2
      simp [this]

theorem annRel_annU {r : Renaming} {D : BVar → Prop} {ann ann'' : Option (Src.BTy × List BVar)}
    (h : AnnRel r D ann ann'') : ∀ v, D v → (v ∈ annU ann ↔ r.bvar v ∈ annU ann'') := by
  cases ann with
  | none => cases ann'' with
    | none => intro v _; exact ⟨fun h => absurd h List.not_mem_nil, fun h => absurd h List.not_mem_nil⟩
    | some _ => exact h.elim
  | some p => cases ann'' with
    | none => exact h.elim
    | some p'' => obtain ⟨_, _⟩ := p; obtain ⟨_, _⟩ := p''; exact h

theorem AnnRel.isSome_eq {r : Renaming} {D : BVar → Prop} {ann ann'' : Option (Src.BTy × List BVar)}
    (h : AnnRel r D ann ann'') : ann''.isSome = ann.isSome := by
  cases ann <;> cases ann'' <;> first | rfl | exact h.elim

theorem AValBind.ve_var (x : Var) (ann : Option (Src.BTy × List BVar)) (τ : Ty) (e : AExp) (rest : Option AValBind) :
    (AValBind.var x ann τ e rest).ve =
      FMap.modify [(x, (if ann.isSome then annScheme (annU ann) τ else mono τ, .v))] (AValBind.veOpt rest) := by
  cases rest <;> rfl

mutual
theorem RValBind.ve_rename {r : Renaming} (hr : r.WF) {D : BVar → Prop} :
    (vb : AValBind) → ∀ {vb'' : AValBind}, RValBind r D vb vb'' → vb''.ve = r.valEnv vb.ve ∧ ∀ q ∈ vb.ve, ∀ v ∈ q.2.1.tyvars, D v
  | .var x ann τ e rest, _, h => by
    cases h with
    | var hann hτ _ hrest =>
      have hs : (if ann.isSome then annScheme (annU ann) τ else mono τ).tyvars ⊆ τ.vars := by
        intro v hv
        split at hv
        · exact canon_tyvars_sub _ v hv
        · exact scheme_tyvars_sub _ v hv
      have hrr := RValBindOpt.ve_rename hr rest hrest
      rw [AValBind.ve_var, AValBind.ve_var]
      refine ⟨?_, ?_⟩
      · rw [Renaming.valEnv_modify, hrr.1, hann.isSome_eq]
        congr 1
        simp only [Renaming.valEnv, List.map_cons, List.map_nil]
        split
        · rw [annScheme_rename hr hτ (annRel_annU hann)]
        · rfl
      · intro q hq v hv
        rcases mem_modify hq with hq | hq
        · simp only [List.mem_singleton] at hq; subst hq; exact hτ v (hs hv)
        · exact hrr.2 q hq v hv
  | .pat p e, _, h => by
    cases h with
    | pat _ hve hD _ =>
      exact ⟨by simp only [AValBind.ve]; exact hve, fun q hq v hv => hD q hq v (scheme_tyvars_sub _ v hv)⟩
theorem RValBindOpt.ve_rename {r : Renaming} (hr : r.WF) {D : BVar → Prop} :
    (rest : Option AValBind) → ∀ {rest'' : Option AValBind}, RValBindOpt r D rest rest'' →
      AValBind.veOpt rest'' = r.valEnv (AValBind.veOpt rest) ∧ ∀ q ∈ AValBind.veOpt rest, ∀ v ∈ q.2.1.tyvars, D v
  | none, _, h => by cases h; exact ⟨rfl, by simp [AValBind.veOpt]⟩
  | some vb, _, h => by cases h with | some h => exact RValBind.ve_rename hr vb h
end

end StandardElm.Stat
