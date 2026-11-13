/-
  A Standard Definition of Elm? Mechanisation: node correspondence for W on F_e (milestone (e) of
  plan step 11, section 9; WDNodeRelExp.lean for WE.lean's W): the nodes of a checked phrase `x`
  (W's result) and of `T x`, both with the instance lists left out, in contexts related by
  `CtxRelD (SchRelD T)`, correspond one to one (`NRelE`), when the images under `T` of the types
  `x` records are canonical and without `bnd` variables. Changes from milestone (d):

  * the explicit variables of a node are fixed by `T` (they are rigid), in place of one `U` for
    every node; an annotated member's body is in both contexts with its `U'` added
    (`CtxRelD.plusUE`);
  * a declaration's environment holds monotypes and annotated members' schemes `∀U'.τ`, over
    named variables, which `T` fixes (`EntE`, `dec_factsE`); at the declaration node the scheme
    clause of an annotated member is `closE_instAnn`, and the contexts of the `let` body are
    related by `closE_relAnnE` (WENodeRel.lean).
-/
import StandardElmMech.Stat.Complete.WENodeRel

namespace StandardElm.Stat.Complete.WE.WDP
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Stat.Complete
open StandardElm.Stat.Complete.WDP

/-! ## Declarations of W's result -/

theorem annU_named_of_canon {ann : Option (StandardElm.Src.BTy × List BVar)} (h : canonAnnB ann = true) :
    ∀ v ∈ annU ann, v.isNamed = true := by
  intro v hv
  match ann, h, hv with
  | some (ty, U'), h, hv =>
    simp only [canonAnnB, decide_eq_true_eq] at h
    simp only [annU] at hv
    rw [h] at hv
    obtain ⟨s, -, rfl⟩ := mem_newU0 (List.mem_filter.mp hv).1
    exact nameVar_named ty s

theorem valbind_ve_entE2 : ∀ vb : AValBind, AnnOKV vb →
    ∀ q ∈ vb.ve, (∀ w, PEnt (tysValBind w vb) q) ∨ (∀ w, AEnt (tysValBind w vb) q)
  | .var x ann τ e rest, h, q, hq => by
    unfold AnnOKV at h
    unfold AValBind.ve at hq
    rcases mem_modify hq with hq | hq
    · simp only [List.mem_singleton] at hq; subst hq
      by_cases hs : ann.isSome = true
      · exact .inr fun w => ⟨rfl, annU ann, τ, by simp [hs], by simp [tysValBind], h.2.1 hs⟩
      · refine .inl fun w => ⟨by simp [hs, mono], rfl, fun v hv => ⟨τ, by simp [tysValBind], by simpa [hs, mono] using hv⟩⟩
    · cases rest with
      | none => cases hq
      | some vb =>
        rcases valbind_ve_entE2 vb h.2.2 q hq with h' | h'
        · exact .inl fun w => PEnt.mono (fun t ht => by simp [tysValBind, tysValBindOpt, ht]) (h' w)
        · refine .inr fun w => ?_
          obtain ⟨h1, U', τ', h2, h3, h4⟩ := h' w
          exact ⟨h1, U', τ', h2, by simp [tysValBind, tysValBindOpt, h3], h4⟩
  | .pat p e, _, q, hq => by
    simp only [AValBind.ve] at hq
    exact .inl fun w => PEnt.mono (fun t ht => by simp [tysValBind, ht]) (atpat_ve p q hq)

theorem cn_valbind_veE : ∀ vb : AValBind, AnnOKV vb → (∀ τ ∈ tysValBind false vb, cnB τ = true) →
    ∀ q ∈ vb.ve, cnB q.2.1.body = true
  | .var x ann τ e rest, h, hc, q, hq => by
    unfold AnnOKV at h
    unfold AValBind.ve at hq
    rcases mem_modify hq with hq | hq
    · simp only [List.mem_singleton] at hq; subst hq
      have hτ : cnB τ = true := hc τ (by simp [tysValBind])
      simp only
      split
      · exact cnB_annScheme hτ
      · exact hτ
    · cases rest with
      | none => cases hq
      | some vb =>
        exact cn_valbind_veE vb h.2.2 (fun x hx => hc x (by simp [tysValBind, tysValBindOpt, hx])) q hq
  | .pat p e, _, hc, q, hq => by
    simp only [AValBind.ve] at hq
    exact cn_atpat_ve p (fun x hx => hc x (by simp [tysValBind, hx])) q hq

/-- An entry of a declaration's environment in W's result: a monotype (`OkTD`, mapped by `T` to a
    canonical type without `bnd`), or an annotated member's scheme over named variables. -/
def EntE (n : Nat) (T : RSub) (q : String × (Scheme × IdStatus)) : Prop :=
  (q.2.1.bound = [] ∧ OkTD n q.2.1.body ∧ NBτ (rsb T q.2.1.body) ∧ cnB (rsb T q.2.1.body) = true) ∨
    (∃ U' τ, q.2.1 = annScheme U' τ ∧ (∀ v ∈ τ.vars, v.isNamed = true) ∧ cnB τ = true)

theorem dec_factsE {n n0 : Nat} {T : RSub} {C : Ctx} {VE : ValEnv} {vb : AValBind}
    (hfx : FixR (rigidFromD n0) T)
    (hc : checkDec C (.val VE vb) = true) (hok : OkAD n (tysDec true (.val VE vb)))
    (hnb : NBT T (tysDec false (.val VE vb))) :
    AnnOKV vb ∧ ∀ q ∈ VE, EntE n T q := by
  simp only [checkDec, Bool.and_eq_true, decide_eq_true_eq] at hc
  simp only [tysDec, ↓reduceIte, Bool.false_eq_true, List.nil_append] at hok hnb
  have hokv := (OkAD.split hok).2
  have hann := annOKV_of_okAD vb hokv
  refine ⟨hann, fun q hq => ?_⟩
  rw [← hc.2] at hq
  rcases valbind_ve_entE2 vb hann q hq with hP | hA
  · have h1 := hP true
    have h2 := hP false
    refine .inl ⟨h1.1, okT_pentD hokv h1, fun v hv => ?_, ?_⟩
    · obtain ⟨c, hc', hvc⟩ := (mem_vars_rsb T _ v).mp hv
      obtain ⟨τ, h3, h4⟩ := h2.2.2 _ hc'
      exact (hnb τ h3).1 v ((mem_vars_rsb T τ v).mpr ⟨c, h4, hvc⟩)
    · have hq' : (q.1, (rsbScheme T q.2.1, q.2.2)) ∈ (rsbValBind T vb).ve := by
        rw [valbind_ve_rsbE hfx vb hann]; simp only [rsbVE, List.mem_map]; exact ⟨q, hq, rfl⟩
      refine cn_valbind_veE _ (annOKV_rsb hfx vb hann) (fun τ hτ => ?_) _ hq'
      rw [tysValBind_sbD T (fix_bnd0 hfx)] at hτ
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hτ
      exact (hnb x hx).2
  · obtain ⟨-, U', τ, he, hτ, hnam⟩ := hA false
    refine .inr ⟨U', τ, he, hnam, ?_⟩
    have := (hnb τ hτ).2; rwa [rsb_named hfx hnam] at this

/-- A variable `T` fixes, free in a context, is free in a related one. -/
theorem ftv_fixed {n0 : Nat} {T : RSub} {C C' : Ctx} (h : CtxRelD (SchRelD T) (rigidFromD n0) C C')
    (hfx : FixR (rigidFromD n0) T) {v : BVar} (hv : T.img v = vty v) (hb : v.isBnd = false) (hvA : v ∈ C.tyvars) :
    v ∈ C'.tyvars :=
  h.ftv (fun _ _ h => h.1) hfx v hvA v (by rw [hv]; exact mem_tyvars_iff.mpr ⟨by simp [vars_vty], hb⟩)

theorem ctxRelD_monoE {n0 n : Nat} {T : RSub} {C C' : Ctx} {VE : ValEnv}
    (h : CtxRelD (SchRelD T) (rigidFromD n0) C C') (hfx : FixR (rigidFromD n0) T) (hVE : ∀ q ∈ VE, EntE n T q) :
    CtxRelD (SchRelD T) (rigidFromD n0) (C.plusVE VE) (C'.plusVE (rsbVE T VE)) :=
  h.plusVE (VEMatch_entD fun q hq => by
    rcases hVE q hq with ⟨hb, -⟩ | ⟨U', τ, he, hnam, -⟩
    · rw [mono_of_bound hb, rsbScheme_monoD]; exact schRel_monoD _ _
    · rw [he, rsbScheme_ann hfx hnam]; exact schRel_ann hfx hnam)

theorem ctxRelD_closE {n0 n : Nat} {T : RSub} {C C' : Ctx} {VE : ValEnv}
    (h : CtxRelD (SchRelD T) (rigidFromD n0) C C') (hfx : FixR (rigidFromD n0) T) (hcls : RespR T)
    (hVE : ∀ q ∈ VE, EntE n T q) :
    CtxRelD (SchRelD T) (rigidFromD n0) (C.plusVE (closGroup C.tyvars VE))
      (C'.plusVE (closGroup C'.tyvars (rsbVE T VE))) :=
  h.plusVE fun x => by
    rw [find?_closGroup, find?_closGroup, find?_rsbVE]
    cases hf : FMap.find? VE x with
    | none => trivial
    | some p =>
      refine ⟨rfl, ?_⟩
      simp only
      rcases hVE _ (find?_mem hf) with ⟨hb, hok, hnb, -⟩ | ⟨U', τ, he, hnam, -⟩
      · rw [mono_of_bound hb]
        simp only [rsbScheme_monoD]
        exact closE_relD hok hcls (fun w hw _ => h.ftv (fun _ _ h => h.1) hfx w hw) hnb
      · simp only at he
        rw [he, rsbScheme_ann hfx hnam]
        exact closE_relAnnE (annSch_ann hnam) (fun v hv => hfx v (rigidFromD_bnd n0 hv)) (fix_annScheme hfx hnam)
          (fun v hv hb hvA => ftv_fixed h hfx (fix_annScheme hfx hnam v hv) hb hvA)

theorem dec_head_relE {n0 n : Nat} {T : RSub} {C C' : Ctx} {VE : ValEnv} (path : List Nat)
    (hrel : CtxRelD (SchRelD T) (rigidFromD n0) C C') (hfx : FixR (rigidFromD n0) T) (hcls : RespR T)
    (hVE : ∀ q ∈ VE, EntE n T q) :
    NRelE T ⟨path, C.U, [], veSchemes (closGroup C.tyvars VE)⟩
      ⟨path, C'.U, [], veSchemes (closGroup C'.tyvars (rsbVE T VE))⟩ := by
  refine ⟨uFix hfx hrel, rfl, hrel.2.1.symm, rfl, by simp [veSchemes, closGroup_eq, FMap.mapV, rsbVE], fun i h h' => ?_⟩
  have hi : i < VE.length := by simpa [veSchemes, closGroup_eq, FMap.mapV] using h
  simp only [veSchemes, closGroup_eq, FMap.mapV, rsbVE, List.map_map, List.getElem_map, Function.comp]
  have hm : VE[i] ∈ VE := List.getElem_mem hi
  rcases hVE _ hm with ⟨hb, hok, hnb, hcn⟩ | ⟨U', τ, he, hnam, hcn⟩
  · have e : VE[i].2.1 = mono VE[i].2.1.body := mono_of_bound hb
    rw [e, rsbScheme_monoD]
    exact closE_instD hok hcls (fun v hv => hfx v (rigidFromD_bnd n0 hv))
      (fun w hw _ => hrel.ftv (fun _ _ h => h.1) hfx w hw) hnb hcn
  · rw [he, rsbScheme_ann hfx hnam]
    exact closE_instAnn (annSch_ann hnam) (fun v hv => hfx v (rigidFromD_bnd n0 hv)) (fix_annScheme hfx hnam)
      (fun v hv hb hvA => ftv_fixed hrel hfx (fix_annScheme hfx hnam v hv) hb hvA) (cnB_annScheme hcn)

/-! ## Expressions -/

section
variable (T : RSub) (n0 n : Nat) (hfx : FixR (rigidFromD n0) T) (hcls : RespR T)
include hfx hcls

mutual
theorem nodesAtExp_relE : ∀ (x : AAtExp) (C C' : Ctx) (path : List Nat), checkAtExp C x = true →
    CtxRelD (SchRelD T) (rigidFromD n0) C C' → OkAD n (tysAtExp true x) → NBT T (tysAtExp false x) →
    F2 (NRelE T) (nodesAtExp C path (stripAtExp x)) (nodesAtExp C' path (stripAtExp (rsbAtExp T x)))
  | .scon sc τ, C, C', path, hc, hrel, _, _ => .cons (nrelE_mk (uFix hfx hrel) hrel.2.1.symm
      (by simp [rsbAtExp, stripAtExp]) rfl (schOK_nil T)) .nil
  | .var lv inst τ, C, C', path, hc, hrel, _, _ =>
    .cons (nrelE_mk (uFix hfx hrel) hrel.2.1.symm (by simp [rsbAtExp, stripAtExp]) rfl (schOK_nil T)) .nil
  | .con lc inst τ, C, C', path, hc, hrel, _, _ =>
    .cons (nrelE_mk (uFix hfx hrel) hrel.2.1.symm (by simp [rsbAtExp, stripAtExp]) rfl (schOK_nil T)) .nil
  | .op o inst τ, C, C', path, hc, hrel, _, _ =>
    .cons (nrelE_mk (uFix hfx hrel) hrel.2.1.symm (by simp [rsbAtExp, stripAtExp]) rfl (schOK_nil T)) .nil
  | .unit, C, C', path, hc, hrel, _, _ =>
    .cons (nrelE_mk (uFix hfx hrel) hrel.2.1.symm (by simp [rsbAtExp, stripAtExp, tUnitTy, rsb, rsbList]) rfl
      (schOK_nil T)) .nil
  | .nil τ, C, C', path, hc, hrel, _, _ =>
    .cons (nrelE_mk (uFix hfx hrel) hrel.2.1.symm (by simp [rsbAtExp, stripAtExp]) rfl (schOK_nil T)) .nil
  | .tuple e1 e2 e3, C, C', path, hc, hrel, hok, hnb => by
    have hc' := hc
    simp only [checkAtExp, Bool.and_eq_true] at hc
    simp only [tysAtExp] at hok hnb
    obtain ⟨hok12, hok3⟩ := OkAD.split hok; obtain ⟨hok1, hok2⟩ := OkAD.split hok12
    obtain ⟨hnb12, hnb3⟩ := NBT.app hnb; obtain ⟨hnb1, hnb2⟩ := NBT.app hnb12
    exact forall2_append (forall2_append (forall2_append
      (.cons (nrelE_mk (uFix hfx hrel) hrel.2.1.symm (by
          simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]; exact tyS_atexpD (T := T) hc') rfl
          (schOK_nil T)) .nil)
      (nodesExp_relE e1 C C' _ hc.1.1 hrel hok1 hnb1)) (nodesExp_relE e2 C C' _ hc.1.2 hrel hok2 hnb2))
      (nodesExpOpt_relE e3 C C' _ hc.2 hrel hok3 hnb3)
  | .record r, C, C', path, hc, hrel, hok, hnb => by
    have hc' := hc
    simp only [checkAtExp] at hc
    simp only [tysAtExp] at hok hnb
    exact forall2_append (.cons (nrelE_mk (uFix hfx hrel) hrel.2.1.symm (by
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]; exact tyS_atexpD (T := T) hc') rfl
        (schOK_nil T)) .nil)
      (nodesExpRowOpt_relE r C C' _ hc hrel hok hnb)
  | .update x inst τ r, C, C', path, hc, hrel, hok, hnb => by
    simp only [checkAtExp, Bool.and_eq_true] at hc
    simp only [tysAtExp] at hok hnb
    exact forall2_append (.cons (nrelE_mk (uFix hfx hrel) hrel.2.1.symm (by simp [rsbAtExp, stripAtExp]) rfl
        (schOK_nil T)) .nil)
      (nodesExpRow_relE r C C' _ hc.1.2 hrel (OkAD.tail hok) hnb.cons)
  | .letE d e, C, C', path, hc, hrel, hok, hnb => by
    have hc' := hc
    simp only [checkAtExp, Bool.and_eq_true] at hc
    simp only [tysAtExp] at hok hnb
    obtain ⟨hok1, hok2⟩ := OkAD.split hok; obtain ⟨hnb1, hnb2⟩ := NBT.app hnb
    cases d with
    | val VE vb =>
      obtain ⟨-, hVE⟩ := dec_factsE hfx hc.1 hok1 hnb1
      exact forall2_append (forall2_append
        (.cons (nrelE_mk (uFix hfx hrel) hrel.2.1.symm (by
          simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]; exact tyS_atexpD (T := T) hc') rfl
          (schOK_nil T)) .nil)
        (nodesDec_relE (.val VE vb) C C' _ hc.1 hrel hok1 hnb1))
        (nodesExp_relE e _ _ _ hc.2 (ctxRelD_closE hrel hfx hcls hVE) hok2 hnb2)
  | .paren e, C, C', path, hc, hrel, hok, hnb => by
    have hc' := hc
    simp only [checkAtExp] at hc
    simp only [tysAtExp] at hok hnb
    exact forall2_append (.cons (nrelE_mk (uFix hfx hrel) hrel.2.1.symm (by
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]; exact tyS_atexpD (T := T) hc') rfl
        (schOK_nil T)) .nil)
      (nodesExp_relE e C C' _ hc hrel hok hnb)
theorem nodesExpRow_relE : ∀ (r : AExpRow) (C C' : Ctx) (path : List Nat), checkExpRow C r = true →
    CtxRelD (SchRelD T) (rigidFromD n0) C C' → OkAD n (tysExpRow true r) → NBT T (tysExpRow false r) →
    F2 (NRelE T) (nodesExpRow C path (stripExpRow r)) (nodesExpRow C' path (stripExpRow (rsbExpRow T r)))
  | .field l e rest, C, C', path, hc, hrel, hok, hnb => by
    have hc' := hc
    simp only [checkExpRow, Bool.and_eq_true] at hc
    simp only [tysExpRow] at hok hnb
    obtain ⟨hok1, hok2⟩ := OkAD.split hok; obtain ⟨hnb1, hnb2⟩ := NBT.app hnb
    exact forall2_append (forall2_append
      (.cons (nrelE_mk (uFix hfx hrel) hrel.2.1.symm (rowSD (T := T) hc') rfl (schOK_nil T)) .nil)
      (nodesExp_relE e C C' _ hc.1 hrel hok1 hnb1)) (nodesExpRowOpt_relE rest C C' _ hc.2 hrel hok2 hnb2)
theorem nodesExpRowOpt_relE : ∀ (r : Option AExpRow) (C C' : Ctx) (path : List Nat),
    checkExpRowOpt C r = true → CtxRelD (SchRelD T) (rigidFromD n0) C C' → OkAD n (tysExpRowOpt true r) →
    NBT T (tysExpRowOpt false r) →
    F2 (NRelE T) (nodesExpRowOpt C path (stripExpRowOpt r)) (nodesExpRowOpt C' path (stripExpRowOpt (rsbExpRowOpt T r)))
  | none, _, _, _, _, _, _, _ => .nil
  | some r, C, C', path, hc, hrel, hok, hnb => nodesExpRow_relE r C C' path hc hrel hok hnb
theorem nodesExp_relE : ∀ (x : AExp) (C C' : Ctx) (path : List Nat), checkExpS C x = true →
    CtxRelD (SchRelD T) (rigidFromD n0) C C' → OkAD n (tysExp true x) → NBT T (tysExp false x) →
    F2 (NRelE T) (nodesExp C path (stripExp x)) (nodesExp C' path (stripExp (rsbExp T x)))
  | .atexp a, C, C', path, hc, hrel, hok, hnb => by
    have hc' := hc
    simp only [checkExpS] at hc
    simp only [tysExp] at hok hnb
    exact forall2_append (.cons (nrelE_mk (uFix hfx hrel) hrel.2.1.symm (by
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]; exact tyS_expD (T := T) hc') rfl
        (schOK_nil T)) .nil)
      (nodesAtExp_relE a C C' _ hc hrel hok hnb)
  | .app e a, C, C', path, hc, hrel, hok, hnb => by
    have hc' := hc
    simp only [checkExpS, Bool.and_eq_true] at hc
    simp only [tysExp] at hok hnb
    obtain ⟨hok1, hok2⟩ := OkAD.split hok; obtain ⟨hnb1, hnb2⟩ := NBT.app hnb
    exact forall2_append (forall2_append
      (.cons (nrelE_mk (uFix hfx hrel) hrel.2.1.symm (by
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]; exact tyS_expD (T := T) hc') rfl
        (schOK_nil T)) .nil)
      (nodesExp_relE e C C' _ hc.1.1 hrel hok1 hnb1)) (nodesAtExp_relE a C C' _ hc.1.2 hrel hok2 hnb2)
  | .lam p e, C, C', path, hc, hrel, hok, hnb => by
    have hc' := hc
    simp only [checkExpS, Bool.and_eq_true] at hc
    simp only [tysExp] at hok hnb
    obtain ⟨hok1, hok2⟩ := OkAD.split hok; obtain ⟨hnb1, hnb2⟩ := NBT.app hnb
    have hrel' : CtxRelD (SchRelD T) (rigidFromD n0) (C.plusVE (stripAtPat p).ve)
        (C'.plusVE (stripAtPat (rsbAtPat T p)).ve) := by
      rw [rsbAtPat_ve_strip, stripAtPat_ve]
      exact ctxRelD_mono hrel fun q hq => (atpat_ve p q hq).1
    exact forall2_append (forall2_append
      (.cons (nrelE_mk (uFix hfx hrel) hrel.2.1.symm (by
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]; exact tyS_expD (T := T) hc') rfl
        (schOK_nil T)) .nil)
      (nodesAtPat_relE T (uFix hfx hrel) hrel.2.1.symm p _ hnb1.cn))
      (nodesExp_relE e _ _ _ (by rw [stripAtPat_ve]; exact hc.2) hrel' hok2 hnb2)
  | .caseE e m, C, C', path, hc, hrel, hok, hnb => by
    have hc' := hc
    simp only [checkExpS, Bool.and_eq_true] at hc
    simp only [tysExp] at hok hnb
    obtain ⟨hok1, hok2⟩ := OkAD.split hok; obtain ⟨hnb1, hnb2⟩ := NBT.app hnb
    exact forall2_append (forall2_append
      (.cons (nrelE_mk (uFix hfx hrel) hrel.2.1.symm (by
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]; exact tyS_expD (T := T) hc') rfl
        (schOK_nil T)) .nil)
      (nodesExp_relE e C C' _ hc.1.1 hrel hok1 hnb1)) (nodesMatch_relE m C C' _ hc.1.2 hrel hok2 hnb2)
theorem nodesExpOpt_relE : ∀ (x : Option AExp) (C C' : Ctx) (path : List Nat), checkExpOpt C x = true →
    CtxRelD (SchRelD T) (rigidFromD n0) C C' → OkAD n (tysExpOpt true x) → NBT T (tysExpOpt false x) →
    F2 (NRelE T) (nodesExpOpt C path (stripExpOpt x)) (nodesExpOpt C' path (stripExpOpt (rsbExpOpt T x)))
  | none, _, _, _, _, _, _, _ => .nil
  | some e, C, C', path, hc, hrel, hok, hnb => nodesExp_relE e C C' path hc hrel hok hnb
theorem nodesMatch_relE : ∀ (m : AMatch) (C C' : Ctx) (path : List Nat), checkMatch C m = true →
    CtxRelD (SchRelD T) (rigidFromD n0) C C' → OkAD n (tysMatch true m) → NBT T (tysMatch false m) →
    F2 (NRelE T) (nodesMatch C path (stripMatch m)) (nodesMatch C' path (stripMatch (rsbMatch T m)))
  | .mk (.mk p e) rest, C, C', path, hc, hrel, hok, hnb => by
    simp only [checkMatch, Bool.and_eq_true] at hc
    have hc1 := hc.1
    simp only [checkMRule, Bool.and_eq_true] at hc1
    simp only [tysMatch, tysMRule] at hok hnb
    obtain ⟨hok12, hok3⟩ := OkAD.split hok; obtain ⟨hok1, hok2⟩ := OkAD.split hok12
    obtain ⟨hnb12, hnb3⟩ := NBT.app hnb; obtain ⟨hnb1, hnb2⟩ := NBT.app hnb12
    have hrel' : CtxRelD (SchRelD T) (rigidFromD n0) (C.plusVE (stripPat p).ve)
        (C'.plusVE (stripPat (rsbPat T p)).ve) := by
      rw [rsbPat_ve_strip, stripPat_ve]
      exact ctxRelD_mono hrel fun q hq => (pat_ve p q hq).1
    exact forall2_append (forall2_append (forall2_append
      (.cons (nrelE_mk (uFix hfx hrel) hrel.2.1.symm (by
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]; exact tyS_mruleD (T := T) hc.1) rfl
        (schOK_nil T)) .nil)
      (nodesPat_relE T (uFix hfx hrel) hrel.2.1.symm p _ hnb1.cn))
      (nodesExp_relE e _ _ _ (by rw [stripPat_ve]; exact hc1.2) hrel' hok2 hnb2))
      (nodesMatchOpt_relE rest C C' _ (by
        intro m0 hm0; subst hm0
        simp only [checkMatchOptAt, Bool.and_eq_true] at hc; exact hc.2.1) hrel hok3 hnb3)
theorem nodesMatchOpt_relE : ∀ (m : Option AMatch) (C C' : Ctx) (path : List Nat),
    (∀ m0, m = some m0 → checkMatch C m0 = true) →
    CtxRelD (SchRelD T) (rigidFromD n0) C C' → OkAD n (tysMatchOpt true m) → NBT T (tysMatchOpt false m) →
    F2 (NRelE T) (nodesMatchOpt C path (stripMatchOpt m)) (nodesMatchOpt C' path (stripMatchOpt (rsbMatchOpt T m)))
  | none, _, _, _, _, _, _, _ => .nil
  | some m, C, C', path, hc, hrel, hok, hnb => nodesMatch_relE m C C' path (hc m rfl) hrel hok hnb
theorem nodesDec_relE : ∀ (d : ADec) (C C' : Ctx) (path : List Nat), checkDec C d = true →
    CtxRelD (SchRelD T) (rigidFromD n0) C C' → OkAD n (tysDec true d) → NBT T (tysDec false d) →
    F2 (NRelE T) (nodesDec C path (stripDec d)) (nodesDec C' path (stripDec (rsbDec T d)))
  | .val VE vb, C, C', path, hc, hrel, hok, hnb => by
    obtain ⟨-, hVE⟩ := dec_factsE hfx hc hok hnb
    simp only [checkDec, Bool.and_eq_true] at hc
    simp only [tysDec, ↓reduceIte, Bool.false_eq_true, List.nil_append] at hok hnb
    exact forall2_append (.cons (dec_head_relE path hrel hfx hcls hVE) .nil)
      (nodesValBind_relE vb _ _ _ hc.1 (ctxRelD_monoE hrel hfx hVE) (OkAD.split hok).2 hnb)
theorem nodesValBind_relE : ∀ (vb : AValBind) (C C' : Ctx) (path : List Nat), checkValBind C vb = true →
    CtxRelD (SchRelD T) (rigidFromD n0) C C' → OkAD n (tysValBind true vb) → NBT T (tysValBind false vb) →
    F2 (NRelE T) (nodesValBind C path (stripValBind vb)) (nodesValBind C' path (stripValBind (rsbValBind T vb)))
  | .var x ann τ e rest, C, C', path, hc, hrel, hok, hnb => by
    have hann := annOKV_of_okAD _ hok
    have hann' := hann
    unfold AnnOKV at hann'
    have hcnve : ∀ σ ∈ veSchemes (stripValBind (.var x ann τ e rest)).ve, SchOK T σ := by
      rw [stripValBind_ve]
      intro σ hσ
      simp only [veSchemes, List.mem_map] at hσ
      obtain ⟨q, hq, rfl⟩ := hσ
      rcases valbind_ve_entE2 _ hann q hq with hP | hA
      · refine .inl ⟨(hP true).1, ?_⟩
        have hq' : (q.1, (rsbScheme T q.2.1, q.2.2)) ∈ (rsbValBind T (.var x ann τ e rest)).ve := by
          rw [valbind_ve_rsbE hfx _ hann]; simp only [rsbVE, List.mem_map]; exact ⟨q, hq, rfl⟩
        refine cn_valbind_veE _ (annOKV_rsb hfx _ hann) (fun τ' hτ' => ?_) _ hq'
        rw [tysValBind_sbD T (fix_bnd0 hfx)] at hτ'
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hτ'
        exact (hnb y hy).2
      · obtain ⟨-, U', τ', he, hτ', hnam⟩ := hA false
        have hc' := (hnb τ' hτ').2
        rw [rsb_named hfx hnam] at hc'
        exact .inr ⟨by rw [he]; exact fix_annScheme hfx hnam, by rw [he]; exact cnB_annScheme hc'⟩
    have e1 : (stripValBind (rsbValBind T (.var x ann τ e rest))).ve = rsbVE T (stripValBind (.var x ann τ e rest)).ve := by
      rw [stripValBind_ve, stripValBind_ve, valbind_ve_rsbE hfx _ hann]
    simp only [checkValBind, Bool.and_eq_true, decide_eq_true_eq] at hc
    have hcan : canonAnnB ann = true := hann'.1
    have hm1 : annMark true ann τ = [] := by unfold annMark; rw [if_pos ⟨hcan, fun _ hs => hann'.2.1 hs⟩]
    have hm0 : annMark false ann τ = [] := by rw [annMark_false, if_pos hcan]
    simp only [tysValBind, List.cons_append, hm1, hm0, List.nil_append] at hok hnb
    obtain ⟨hok1, hok2⟩ := OkAD.split (OkAD.tail hok); obtain ⟨hnb1, hnb2⟩ := NBT.app hnb.cons
    have hn1 := nodesExp_relE e (C.plusU (annU ann)) (C'.plusU (annU ann)) (path ++ [0]) hc.1.1.2
      (CtxRelD.plusUE hrel (annU_named_of_canon hcan)) hok1 hnb1
    exact forall2_append (forall2_append
      (.cons (nrelE_mk (uFix hfx hrel) hrel.2.1.symm (by simp [stripValBind, rsbValBind])
        (by rw [← veSchemes_rsb]; exact congrArg veSchemes e1) hcnve) .nil) hn1)
      (nodesValBindOpt_relE rest C C' _ hc.2 hrel hok2 hnb2)
  | .pat p e, C, C', path, hc, hrel, hok, hnb => by
    simp only [checkValBind, Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [tysValBind] at hok hnb
    obtain ⟨-, hok2⟩ := OkAD.split hok; obtain ⟨hnb1, hnb2⟩ := NBT.app hnb
    exact forall2_append (forall2_append
      (.cons (nrelE_mk (uFix hfx hrel) hrel.2.1.symm (by simp [stripValBind, rsbValBind, rsbAtPat_ty_strip])
        (by rw [← veSchemes_rsb]; congr 1; exact rsbAtPat_ve_strip T p) (schOK_of_monoCn (monoCn_atpat T p hnb1.cn))) .nil)
      (nodesAtPat_relE T (uFix hfx hrel) hrel.2.1.symm p _ hnb1.cn))
      (nodesExp_relE e C C' _ hc.1.2 hrel hok2 hnb2)
theorem nodesValBindOpt_relE : ∀ (vb : Option AValBind) (C C' : Ctx) (path : List Nat),
    checkValBindOpt C vb = true → CtxRelD (SchRelD T) (rigidFromD n0) C C' → OkAD n (tysValBindOpt true vb) →
    NBT T (tysValBindOpt false vb) →
    F2 (NRelE T) (nodesValBindOpt C path (stripValBindOpt vb)) (nodesValBindOpt C' path (stripValBindOpt (rsbValBindOpt T vb)))
  | none, _, _, _, _, _, _, _ => .nil
  | some vb, C, C', path, hc, hrel, hok, hnb => nodesValBind_relE vb C C' path hc hrel hok hnb
end

end

end StandardElm.Stat.Complete.WE.WDP
