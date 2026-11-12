/-
  A Standard Definition of Elm? Mechanisation: mutual instances are renamings, third layer (plan
  step 10, `mutualInstanceMod_renaming`): the walk down two derivations of one expression, which
  gives the relation `RAtExp` of RenameSpec.lean (and its companions).
-/
import StandardElmMech.Stat.MutualWalk

namespace StandardElm.Stat
open StandardElm (Var Lab ModId Op LongId)

section Walk
variable {S S' : Subst} {ν ν' : List (TyName × TyName)} {r : Renaming} {D : BVar → Prop}

theorem Rel3.head_U (hw : WalkHyp S S' ν r D) {p : List Nat} {U U'' : List BVar} {ts ts'' : List Ty}
    {s s'' : List Scheme} {ns ns'' : List Node}
    (h : Rel3 S S' ν ν' D (⟨p, U, ts, s⟩ :: ns) (⟨p, U'', ts'', s''⟩ :: ns'')) :
    ∀ v, D v → (v ∈ U ↔ r.bvar v ∈ U'') := by
  obtain ⟨h1, h2, _⟩ := h.head rfl
  exact u_rel hw h1 h2

theorem nodesExp_head (C : Ctx) (path : List Nat) (e : AExp) :
    ∃ ts ns, nodesExp C path e = ⟨path, C.U, ts, []⟩ :: ns := by
  cases e <;> simp only [nodesExp, List.cons_append, List.singleton_append] <;> exact ⟨_, _, rfl⟩

theorem not_mem_U_of_tyvars {C : Ctx} {v : BVar} (h : v ∉ C.tyvars) : v ∉ C.U :=
  fun hu => h (List.mem_append_right _ hu)

theorem annRel_of (hw : WalkHyp S S' ν r D) {C C'' : Ctx} {ann ann'' : Option (Src.BTy × List BVar)} {τ τ'' : Ty}
    (he : ann''.map Prod.fst = ann.map Prod.fst) (hca : checkAnn C ann τ = true) (hca'' : checkAnn C'' ann'' τ'' = true)
    (hCU : ∀ v, D v → (v ∈ C.U ↔ r.bvar v ∈ C''.U))
    (hEU : ∀ v, D v → (v ∈ unionL C.U (annU ann) ↔ r.bvar v ∈ unionL C''.U (annU ann''))) :
    AnnRel r D ann ann'' := by
  cases ann with
  | none => cases ann'' with
    | none => trivial
    | some _ => simp at he
  | some p => cases ann'' with
    | none => simp at he
    | some p'' =>
      obtain ⟨ty, U⟩ := p
      obtain ⟨ty'', U''⟩ := p''
      simp only [checkAnn, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hca hca''
      have d1 := hca.2
      have d2 := hca''.2
      intro v hv
      have e1 := hEU v hv
      have e2 := hCU v hv
      simp only [annU, mem_unionL] at e1
      constructor
      · intro hu
        rcases e1.mp (.inr hu) with h | h
        · exact absurd (e2.mpr h) (not_mem_U_of_tyvars (d1 v hu))
        · exact h
      · intro hu
        rcases e1.mpr (.inr hu) with h | h
        · exact absurd (e2.mp h) (not_mem_U_of_tyvars (d2 _ hu))
        · exact h

mutual
theorem walkAtExp (hw : WalkHyp S S' ν r D) : (a : AAtExp) → ∀ (a'' : AAtExp) (C C'' : Ctx) (path : List Nat),
    a''.erase = a.erase → checkAtExp C a = true → checkAtExp C'' a'' = true →
    Rel3 S S' ν ν' D (nodesAtExp C path a) (nodesAtExp C'' path a'') → RAtExp r D a a''
  | .scon sc τ, a'', C, C'', path, he, _, _, h => by
    cases a'' <;> simp [AAtExp.erase] at he
    subst he
    simp only [nodesAtExp, List.cons_append, List.singleton_append] at h
    obtain ⟨e1, _, _, _⟩ := h.head_ty hw
    subst e1
    exact .scon _ _
  | .var lv inst τ, a'', C, C'', path, he, _, _, h => by
    cases a'' <;> simp [AAtExp.erase] at he
    subst he
    simp only [nodesAtExp, List.cons_append, List.singleton_append] at h
    obtain ⟨_, e2, _, _⟩ := h.head_ty hw
    simp only [List.nil_append] at e2
    rw [e2, ← Renaming.tys_eq_map]
    exact .var _ _ _ _
  | .con lc inst τ, a'', _, _, _, he, _, _, _ => by
    cases a'' <;> simp [AAtExp.erase] at he
    subst he; exact .con _ _ _ _ _
  | .op o inst τ, a'', _, _, _, he, _, _, _ => by
    cases a'' <;> simp [AAtExp.erase] at he
    subst he; exact .op _ _ _ _ _
  | .unit, a'', _, _, _, he, _, _, _ => by
    cases a'' <;> simp [AAtExp.erase] at he
    exact .unit
  | .nil τ, a'', _, _, _, he, _, _, _ => by
    cases a'' <;> simp [AAtExp.erase] at he
    exact .nil _ _
  | .tuple e1 e2 e3, a'', C, C'', path, he, hc, hc'', h => by
    cases a'' <;> simp [AAtExp.erase] at he
    rename_i f1 f2 f3
    obtain ⟨he1, he2, he3⟩ := he
    simp only [checkAtExp, Bool.and_eq_true] at hc hc''
    simp only [nodesAtExp, List.cons_append, List.singleton_append] at h
    exact .tuple
      (walkExp hw e1 f1 C C'' (path ++ [0]) he1 hc.1.1 hc''.1.1 (h.mono (fun n hn => by simp [hn]) (fun n hn => by simp [hn])))
      (walkExp hw e2 f2 C C'' (path ++ [1]) he2 hc.1.2 hc''.1.2 (h.mono (fun n hn => by simp [hn]) (fun n hn => by simp [hn])))
      (walkExpOpt hw e3 f3 C C'' (path ++ [2]) he3 hc.2 hc''.2 (h.mono (fun n hn => by simp [hn]) (fun n hn => by simp [hn])))
  | .record row, a'', C, C'', path, he, hc, hc'', h => by
    cases a'' <;> simp [AAtExp.erase] at he
    rename_i row''
    simp only [checkAtExp] at hc hc''
    simp only [nodesAtExp, List.cons_append, List.singleton_append] at h
    exact .record (walkExpRowOpt hw row row'' C C'' (path ++ [0]) he hc hc'' (h.mono (fun n hn => by simp [hn]) (fun n hn => by simp [hn])))
  | .update x inst τ row, a'', C, C'', path, he, hc, hc'', h => by
    cases a'' <;> simp [AAtExp.erase] at he
    rename_i x'' inst'' τ'' row''
    obtain ⟨rfl, he2⟩ := he
    simp only [checkAtExp, Bool.and_eq_true] at hc hc''
    simp only [nodesAtExp, List.cons_append, List.singleton_append] at h
    obtain ⟨_, e2, _, _⟩ := h.head_ty hw
    simp only [List.nil_append] at e2
    rw [e2, ← Renaming.tys_eq_map]
    exact .update (walkExpRow hw row row'' C C'' (path ++ [0]) he2 hc.1.2 hc''.1.2
      (h.mono (fun n hn => by simp [hn]) (fun n hn => by simp [hn])))
  | .letE (.val VE vb) e, a'', C, C'', path, he, hc, hc'', h => by
    cases a'' <;> simp [AAtExp.erase] at he
    rename_i d'' e''
    cases d'' with
    | val VE'' vb'' =>
      simp [ADec.erase] at he
      obtain ⟨he1, he2⟩ := he
      simp only [checkAtExp, checkDec, Bool.and_eq_true, decide_eq_true_eq] at hc hc''
      obtain ⟨⟨hcv, hve⟩, hce⟩ := hc
      obtain ⟨⟨hcv'', hve''⟩, hce''⟩ := hc''
      have hvb := walkValBind hw vb vb'' (C.plusVE VE) (C''.plusVE VE'') (path ++ [0] ++ [0]) he1 hcv hcv''
        (h.mono (fun n hn => by simp_all [nodesAtExp, nodesDec]) (fun n hn => by simp_all [nodesAtExp, nodesDec]))
      have he' := walkExp hw e e'' _ _ (path ++ [1]) he2 hce hce''
        (h.mono (fun n hn => by simp_all [nodesAtExp, nodesDec]) (fun n hn => by simp_all [nodesAtExp, nodesDec]))
      obtain ⟨hVE, hD⟩ := RValBind.ve_rename hw.wf vb hvb
      have : VE'' = r.valEnv VE := by rw [← hve'', hVE, hve]
      subst this
      rw [hve] at hD
      exact .letE hD hvb he'
  | .paren e, a'', C, C'', path, he, hc, hc'', h => by
    cases a'' <;> simp [AAtExp.erase] at he
    rename_i e''
    simp only [checkAtExp] at hc hc''
    simp only [nodesAtExp, List.cons_append, List.singleton_append] at h
    exact .paren (walkExp hw e e'' C C'' (path ++ [0]) he hc hc'' (h.mono (fun n hn => by simp [hn]) (fun n hn => by simp [hn])))
theorem walkExpRow (hw : WalkHyp S S' ν r D) : (row : AExpRow) → ∀ (row'' : AExpRow) (C C'' : Ctx) (path : List Nat),
    row''.erase = row.erase → checkExpRow C row = true → checkExpRow C'' row'' = true →
    Rel3 S S' ν ν' D (nodesExpRow C path row) (nodesExpRow C'' path row'') → RExpRow r D row row''
  | .field l e rest, row'', C, C'', path, he, hc, hc'', h => by
    cases row'' with
    | field l'' e'' rest'' =>
      simp [AExpRow.erase] at he
      obtain ⟨rfl, he1, he2⟩ := he
      simp only [checkExpRow, Bool.and_eq_true] at hc hc''
      simp only [nodesExpRow, List.cons_append, List.singleton_append] at h
      exact .field
        (walkExp hw e e'' C C'' (path ++ [0]) he1 hc.1 hc''.1 (h.mono (fun n hn => by simp [hn]) (fun n hn => by simp [hn])))
        (walkExpRowOpt hw rest rest'' C C'' (path ++ [1]) he2 hc.2 hc''.2 (h.mono (fun n hn => by simp [hn]) (fun n hn => by simp [hn])))
theorem walkExpRowOpt (hw : WalkHyp S S' ν r D) : (row : Option AExpRow) → ∀ (row'' : Option AExpRow) (C C'' : Ctx)
    (path : List Nat), AExpRow.eraseOpt row'' = AExpRow.eraseOpt row → checkExpRowOpt C row = true →
    checkExpRowOpt C'' row'' = true →
    Rel3 S S' ν ν' D (nodesExpRowOpt C path row) (nodesExpRowOpt C'' path row'') → RExpRowOpt r D row row''
  | none, row'', _, _, _, he, _, _, _ => by cases row'' <;> simp [AExpRow.eraseOpt] at he; exact .none
  | some row, row'', C, C'', path, he, hc, hc'', h => by
    cases row'' <;> simp [AExpRow.eraseOpt] at he
    rename_i row''
    simp only [checkExpRowOpt] at hc hc''
    simp only [nodesExpRowOpt] at h
    exact .some (walkExpRow hw row row'' C C'' path he hc hc'' h)
theorem walkExp (hw : WalkHyp S S' ν r D) : (e : AExp) → ∀ (e'' : AExp) (C C'' : Ctx) (path : List Nat),
    e''.erase = e.erase → checkExp C e = true → checkExp C'' e'' = true →
    Rel3 S S' ν ν' D (nodesExp C path e) (nodesExp C'' path e'') → RExp r D e e''
  | .atexp a, e'', C, C'', path, he, hc, hc'', h => by
    cases e'' <;> simp [AExp.erase] at he
    rename_i a''
    simp only [checkExp] at hc hc''
    simp only [nodesExp, List.cons_append, List.singleton_append] at h
    exact .atexp (walkAtExp hw a a'' C C'' (path ++ [0]) he hc hc'' (h.mono (fun n hn => by simp [hn]) (fun n hn => by simp [hn])))
  | .app e a, e'', C, C'', path, he, hc, hc'', h => by
    cases e'' <;> simp [AExp.erase] at he
    rename_i f a''
    obtain ⟨he1, he2⟩ := he
    simp only [checkExp, Bool.and_eq_true] at hc hc''
    simp only [nodesExp, List.cons_append, List.singleton_append] at h
    exact .app
      (walkExp hw e f C C'' (path ++ [0]) he1 hc.1.1 hc''.1.1 (h.mono (fun n hn => by simp [hn]) (fun n hn => by simp [hn])))
      (walkAtExp hw a a'' C C'' (path ++ [1]) he2 hc.1.2 hc''.1.2 (h.mono (fun n hn => by simp [hn]) (fun n hn => by simp [hn])))
  | .lam p e, e'', C, C'', path, he, hc, hc'', h => by
    cases e'' <;> simp [AExp.erase] at he
    rename_i p'' f
    obtain ⟨he1, he2⟩ := he
    simp only [checkExp, Bool.and_eq_true] at hc hc''
    simp only [nodesExp, List.cons_append, List.singleton_append] at h
    have hp := walkAtPat hw p p'' C.U C''.U (path ++ [0]) he1 (h.mono (fun n hn => by simp [hn]) (fun n hn => by simp [hn]))
    exact .lam he1 hp.2.1
      (walkExp hw e f _ _ (path ++ [1]) he2 hc.2 hc''.2 (h.mono (fun n hn => by simp [hn]) (fun n hn => by simp [hn])))
  | .caseE e m, e'', C, C'', path, he, hc, hc'', h => by
    cases e'' <;> simp [AExp.erase] at he
    rename_i f m''
    obtain ⟨he1, he2⟩ := he
    simp only [checkExp, Bool.and_eq_true] at hc hc''
    simp only [nodesExp, List.cons_append, List.singleton_append] at h
    exact .caseE
      (walkExp hw e f C C'' (path ++ [0]) he1 hc.1.1 hc''.1.1 (h.mono (fun n hn => by simp [hn]) (fun n hn => by simp [hn])))
      (walkMatch hw m m'' C C'' (path ++ [1]) he2 hc.1.2 hc''.1.2 (h.mono (fun n hn => by simp [hn]) (fun n hn => by simp [hn])))
theorem walkExpOpt (hw : WalkHyp S S' ν r D) : (e : Option AExp) → ∀ (e'' : Option AExp) (C C'' : Ctx) (path : List Nat),
    AExp.eraseOpt e'' = AExp.eraseOpt e → checkExpOpt C e = true → checkExpOpt C'' e'' = true →
    Rel3 S S' ν ν' D (nodesExpOpt C path e) (nodesExpOpt C'' path e'') → RExpOpt r D e e''
  | none, e'', _, _, _, he, _, _, _ => by cases e'' <;> simp [AExp.eraseOpt] at he; exact .none
  | some e, e'', C, C'', path, he, hc, hc'', h => by
    cases e'' <;> simp [AExp.eraseOpt] at he
    rename_i e''
    simp only [checkExpOpt] at hc hc''
    simp only [nodesExpOpt] at h
    exact .some (walkExp hw e e'' C C'' path he hc hc'' h)
theorem walkMatch (hw : WalkHyp S S' ν r D) : (m : AMatch) → ∀ (m'' : AMatch) (C C'' : Ctx) (path : List Nat),
    m''.erase = m.erase → checkMatch C m = true → checkMatch C'' m'' = true →
    Rel3 S S' ν ν' D (nodesMatch C path m) (nodesMatch C'' path m'') → RMatch r D m m''
  | .mk (.mk p e) rest, m'', C, C'', path, he, hc, hc'', h => by
    cases m'' with
    | mk mr'' rest'' =>
      cases mr'' with
      | mk p'' e'' =>
        simp [AMatch.erase, AMRule.erase] at he
        obtain ⟨⟨he1, he2⟩, he3⟩ := he
        simp only [checkMatch, checkMRule, Bool.and_eq_true] at hc hc''
        simp only [nodesMatch, List.cons_append, List.singleton_append, List.append_assoc] at h
        have hp := walkPat hw p p'' C.U C''.U (path ++ [0]) he1 (h.mono (fun n hn => by simp [hn]) (fun n hn => by simp [hn]))
        exact .mk (.mk he1 hp.2.1
            (walkExp hw e e'' _ _ (path ++ [1]) he2 hc.1.2 hc''.1.2 (h.mono (fun n hn => by simp [hn]) (fun n hn => by simp [hn]))))
          (walkMatchOpt hw rest rest'' C C'' (path ++ [2]) he3 _ _ hc.2 hc''.2
            (h.mono (fun n hn => by simp [hn]) (fun n hn => by simp [hn])))
theorem walkMatchOpt (hw : WalkHyp S S' ν r D) : (m : Option AMatch) → ∀ (m'' : Option AMatch) (C C'' : Ctx)
    (path : List Nat), AMatch.eraseOpt m'' = AMatch.eraseOpt m → ∀ (τ τ'' : Ty), checkMatchOptAt C τ m = true →
    checkMatchOptAt C'' τ'' m'' = true →
    Rel3 S S' ν ν' D (nodesMatchOpt C path m) (nodesMatchOpt C'' path m'') → RMatchOpt r D m m''
  | none, m'', _, _, _, he, _, _, _, _, _ => by cases m'' <;> simp [AMatch.eraseOpt] at he; exact .none
  | some m, m'', C, C'', path, he, τ, τ'', hc, hc'', h => by
    cases m'' <;> simp [AMatch.eraseOpt] at he
    rename_i m''
    simp only [checkMatchOptAt, Bool.and_eq_true] at hc hc''
    simp only [nodesMatchOpt] at h
    exact .some (walkMatch hw m m'' C C'' path he hc.1 hc''.1 h)
theorem walkValBind (hw : WalkHyp S S' ν r D) : (vb : AValBind) → ∀ (vb'' : AValBind) (C C'' : Ctx) (path : List Nat),
    vb''.erase = vb.erase → checkValBind C vb = true → checkValBind C'' vb'' = true →
    Rel3 S S' ν ν' D (nodesValBind C path vb) (nodesValBind C'' path vb'') → RValBind r D vb vb''
  | .var x ann τ e rest, vb'', C, C'', path, he, hc, hc'', h => by
    cases vb'' <;> simp [AValBind.erase] at he
    rename_i x'' ann'' τ'' e'' rest''
    obtain ⟨rfl, hann, he1, he2⟩ := he
    simp only [checkValBind, Bool.and_eq_true, decide_eq_true_eq] at hc hc''
    obtain ⟨⟨⟨hca, hce⟩, _⟩, hcr⟩ := hc
    obtain ⟨⟨⟨hca'', hce''⟩, _⟩, hcr''⟩ := hc''
    simp only [nodesValBind, List.cons_append, List.singleton_append] at h
    obtain ⟨e1, _, d1, _⟩ := h.head_ty hw
    have hCU := h.head_U hw
    have hsub : Rel3 S S' ν ν' D (nodesExp (C.plusU (annU ann)) (path ++ [0]) e)
        (nodesExp (C''.plusU (annU ann'')) (path ++ [0]) e'') :=
      h.mono (fun n hn => by simp [hn]) (fun n hn => by simp [hn])
    obtain ⟨ts, ns, hn⟩ := nodesExp_head (C.plusU (annU ann)) (path ++ [0]) e
    obtain ⟨ts'', ns'', hn''⟩ := nodesExp_head (C''.plusU (annU ann'')) (path ++ [0]) e''
    have hEU := (hn ▸ hn'' ▸ hsub).head_U hw
    have hAR := annRel_of hw hann hca hca'' hCU hEU
    subst e1
    exact .var hAR d1 (walkExp hw e e'' _ _ (path ++ [0]) he1 hce hce'' hsub)
      (walkValBindOpt hw rest rest'' C C'' (path ++ [1]) he2 hcr hcr'' (h.mono (fun n hn => by simp [hn]) (fun n hn => by simp [hn])))
  | .pat p e, vb'', C, C'', path, he, hc, hc'', h => by
    cases vb'' <;> simp [AValBind.erase] at he
    rename_i p'' e''
    obtain ⟨he1, he2⟩ := he
    simp only [checkValBind, Bool.and_eq_true] at hc hc''
    simp only [nodesValBind, List.cons_append, List.singleton_append] at h
    have hp := walkAtPat hw p p'' C.U C''.U (path ++ [0]) he1 (h.mono (fun n hn => by simp [hn]) (fun n hn => by simp [hn]))
    exact .pat he1 hp.2.1 hp.2.2
      (walkExp hw e e'' C C'' (path ++ [1]) he2 hc.1.2 hc''.1.2 (h.mono (fun n hn => by simp [hn]) (fun n hn => by simp [hn])))
theorem walkValBindOpt (hw : WalkHyp S S' ν r D) : (vb : Option AValBind) → ∀ (vb'' : Option AValBind) (C C'' : Ctx)
    (path : List Nat), AValBind.eraseOpt vb'' = AValBind.eraseOpt vb → checkValBindOpt C vb = true →
    checkValBindOpt C'' vb'' = true →
    Rel3 S S' ν ν' D (nodesValBindOpt C path vb) (nodesValBindOpt C'' path vb'') → RValBindOpt r D vb vb''
  | none, vb'', _, _, _, he, _, _, _ => by cases vb'' <;> simp [AValBind.eraseOpt] at he; exact .none
  | some vb, vb'', C, C'', path, he, hc, hc'', h => by
    cases vb'' <;> simp [AValBind.eraseOpt] at he
    rename_i vb''
    simp only [checkValBindOpt] at hc hc''
    simp only [nodesValBindOpt] at h
    exact .some (walkValBind hw vb vb'' C C'' path he hc hc'' h)
end

end Walk

end StandardElm.Stat
