/-
  A Standard Definition of Elm? Mechanisation: node correspondence for expressions with records
  (plan step 11, milestone (d), section 9), WNodeRelExp.lean for substitutions of type and row
  variables: the nodes of a checked phrase `x` (W's result) and of `T x`, both with the instance
  lists left out, in contexts related by `CtxRelD (SchRelD T)`, correspond one to one (`NRelD`),
  when the images under `T` of the types `x` records are canonical and without `bnd` variables
  (`NBT`, which a canonical derivation without free `bnd` variables gives). At a declaration node
  the scheme clause is `closE_instD`.
-/
import StandardElmMech.Stat.Complete.WDNodeRel

namespace StandardElm.Stat.Complete.WDP
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Stat.Complete

/-! ## Types of substituted expressions -/

mutual
theorem rsbAtExp_ty_chk (s : RSub) : ∀ (a : AAtExp) (C : Ctx), checkAtExp C a = true → (rsbAtExp s a).ty = rsb s a.ty
  | .scon _ _, _, _ | .var _ _ _, _, _ | .con _ _ _, _, _ | .op _ _ _, _, _ | .nil _, _, _ | .update _ _ _ _, _, _ => rfl
  | .unit, _, _ => rfl
  | .record r, C, h => by
    simp only [checkAtExp] at h
    simp only [rsbAtExp, AAtExp.ty, rsbExpRowOpt_row_chk s r C h, rsb, RSub.tl, mrg_nil_right]
  | .tuple e1 e2 e3, C, h => by
    simp only [checkAtExp, Bool.and_eq_true] at h
    simp only [rsbAtExp, AAtExp.ty, rsbExp_ty_chk s e1 C h.1.1, rsbExp_ty_chk s e2 C h.1.2,
      rsbExpOpt_ty_chk s e3 C h.2, tupleTy_rsbOpt]
  | .letE d e, C, h => by
    simp only [checkAtExp, Bool.and_eq_true] at h
    simp only [rsbAtExp, AAtExp.ty, rsbExp_ty_chk s e _ h.2]
  | .paren e, C, h => by
    simp only [checkAtExp] at h
    simp only [rsbAtExp, AAtExp.ty, rsbExp_ty_chk s e C h]
theorem rsbExpRow_row_chk (s : RSub) : ∀ (r : AExpRow) (C : Ctx), checkExpRow C r = true →
    (rsbExpRow s r).row = rsbRow s r.row
  | .field l e rest, C, h => by
    simp only [checkExpRow, Bool.and_eq_true] at h
    simp only [rsbExpRow, AExpRow.row, rsbExp_ty_chk s e C h.1, rsbExpRowOpt_row_chk s rest C h.2, rsbRow_modifyD]
    rfl
theorem rsbExpRowOpt_row_chk (s : RSub) : ∀ (r : Option AExpRow) (C : Ctx), checkExpRowOpt C r = true →
    AExpRow.rowOpt (rsbExpRowOpt s r) = rsbRow s (AExpRow.rowOpt r)
  | none, _, _ => rfl
  | some r, C, h => by
    simp only [checkExpRowOpt] at h
    simp only [rsbExpRowOpt, AExpRow.rowOpt, rsbExpRow_row_chk s r C h]
theorem rsbExp_ty_chk (s : RSub) : ∀ (e : AExp) (C : Ctx), checkExpS C e = true → (rsbExp s e).ty = rsb s e.ty
  | .atexp a, C, h => by
    simp only [checkExpS] at h
    simp only [rsbExp, AExp.ty, rsbAtExp_ty_chk s a C h]
  | .app e a, C, h => by
    simp only [checkExpS, Bool.and_eq_true] at h
    obtain ⟨r, hr⟩ := fn_of_match h.2
    simp only [rsbExp, AExp.ty, rsbExp_ty_chk s e C h.1.1, hr, rsb, Ty.cod]
  | .lam p e, C, h => by
    simp only [checkExpS, Bool.and_eq_true] at h
    simp only [rsbExp, AExp.ty, rsbAtPat_tyD, rsbExp_ty_chk s e _ h.2, rsb]
  | .caseE e m, C, h => by
    simp only [checkExpS, Bool.and_eq_true] at h
    obtain ⟨r, hr⟩ := fn_of_match h.2
    simp only [rsbExp, AExp.ty, rsbMatch_ty_chk s m C h.1.2, hr, rsb, Ty.cod]
theorem rsbExpOpt_ty_chk (s : RSub) : ∀ (e : Option AExp) (C : Ctx), checkExpOpt C e = true →
    AExp.tyOpt (rsbExpOpt s e) = rsbOpt s (AExp.tyOpt e)
  | none, _, _ => rfl
  | some e, C, h => by
    simp only [checkExpOpt] at h
    simp only [rsbExpOpt, AExp.tyOpt, rsbExp_ty_chk s e C h, rsbOpt]
theorem rsbMatch_ty_chk (s : RSub) : ∀ (m : AMatch) (C : Ctx), checkMatch C m = true → (rsbMatch s m).ty = rsb s m.ty
  | .mk mr _, C, h => by
    simp only [checkMatch, Bool.and_eq_true] at h
    simp only [rsbMatch, AMatch.ty, rsbMRule_ty_chk s mr C h.1]
theorem rsbMRule_ty_chk (s : RSub) : ∀ (mr : AMRule) (C : Ctx), checkMRule C mr = true → (rsbMRule s mr).ty = rsb s mr.ty
  | .mk p e, C, h => by
    simp only [checkMRule, Bool.and_eq_true] at h
    simp only [rsbMRule, AMRule.ty, rsbPat_tyD, rsbExp_ty_chk s e _ h.2, rsb]
end

theorem tyS_expD {T : RSub} {C : Ctx} {e : AExp} (hc : checkExpS C e = true) :
    (stripExp (rsbExp T e)).ty = rsb T (stripExp e).ty := by rw [stripExp_ty, stripExp_ty, rsbExp_ty_chk T e C hc]
theorem tyS_atexpD {T : RSub} {C : Ctx} {a : AAtExp} (hc : checkAtExp C a = true) :
    (stripAtExp (rsbAtExp T a)).ty = rsb T (stripAtExp a).ty := by
  rw [stripAtExp_ty, stripAtExp_ty, rsbAtExp_ty_chk T a C hc]
theorem tyS_mruleD {T : RSub} {C : Ctx} {mr : AMRule} (hc : checkMRule C mr = true) :
    (stripMRule (rsbMRule T mr)).ty = rsb T (stripMRule mr).ty := by
  rw [stripMRule_ty, stripMRule_ty, rsbMRule_ty_chk T mr C hc]
theorem rowSD {T : RSub} {C : Ctx} {r : AExpRow} (hc : checkExpRow C r = true) :
    (stripExpRow (rsbExpRow T r)).row.map (·.2) = ((stripExpRow r).row.map (·.2)).map (rsb T) := by
  rw [stripExpRow_row, stripExpRow_row, rsbExpRow_row_chk T r C hc, rsbRow_eq]; simp [mapV]

/-! ## Value bindings -/

theorem annNilV_of_okAD {n : Nat} : ∀ vb : AValBind, OkAD n (tysValBind true vb) → AnnNilV vb
  | .var _ ann _ _ rest, h => by
    simp only [tysValBind, List.cons_append] at h
    unfold AnnNilV
    refine ⟨annU_of_okAD fun τ hτ => h τ (by simp [hτ]), ?_⟩
    cases rest with
    | none => trivial
    | some vb => exact annNilV_of_okAD vb fun τ hτ => h τ (by simp [tysValBindOpt, hτ])
  | .pat _ _, _ => trivial

theorem annNilV_rsb (T : RSub) : ∀ vb : AValBind, AnnNilV vb → AnnNilV (rsbValBind T vb)
  | .var _ ann _ _ rest, h => by
    unfold AnnNilV at h ⊢
    refine ⟨h.1, ?_⟩
    cases rest with
    | none => trivial
    | some vb => exact annNilV_rsb T vb h.2
  | .pat _ _, _ => trivial

theorem valbind_ve_rsb (T : RSub) : ∀ vb : AValBind, AnnNilV vb → (rsbValBind T vb).ve = rsbVE T vb.ve
  | .var x ann τ e rest, h => by
    unfold AnnNilV at h
    simp only [rsbValBind]
    unfold AValBind.ve
    rw [rsbVE_modifyD]
    congr 1
    · simp [h.1, annScheme_nil, rsbVE, rsbScheme, mono]
    · cases rest with
      | none => rfl
      | some vb => exact valbind_ve_rsb T vb h.2
  | .pat p e, _ => by simp only [rsbValBind, AValBind.ve, rsbAtPat_veD]

theorem cn_valbind_ve : ∀ vb : AValBind, AnnNilV vb → (∀ τ ∈ tysValBind false vb, cnB τ = true) →
    ∀ q ∈ vb.ve, cnB q.2.1.body = true
  | .var x ann τ e rest, h, hc, q, hq => by
    unfold AnnNilV at h
    unfold AValBind.ve at hq
    simp only [h.1, annScheme_nil] at hq
    rcases mem_modify hq with hq | hq
    · simp only [List.mem_singleton] at hq; subst hq
      split <;> exact hc τ (by simp [tysValBind])
    · cases rest with
      | none => cases hq
      | some vb =>
        exact cn_valbind_ve vb h.2 (fun x hx => hc x (by simp [tysValBind, tysValBindOpt, hx])) q hq
  | .pat p e, _, hc, q, hq => by
    simp only [AValBind.ve] at hq
    exact cn_atpat_ve p (fun x hx => hc x (by simp [tysValBind, hx])) q hq

/-! ## Facts the derivation gives -/

/-- The images under `T` of the recorded types are canonical and without `bnd` variables. -/
def NBT (T : RSub) (l : List Ty) : Prop := ∀ τ ∈ l, NBτ (rsb T τ) ∧ cnB (rsb T τ) = true

theorem NBT.app {T : RSub} {l1 l2 : List Ty} (h : NBT T (l1 ++ l2)) : NBT T l1 ∧ NBT T l2 :=
  ⟨fun τ hτ => h τ (List.mem_append_left _ hτ), fun τ hτ => h τ (List.mem_append_right _ hτ)⟩
theorem NBT.cons {T : RSub} {τ : Ty} {l : List Ty} (h : NBT T (τ :: l)) : NBT T l := fun x hx => h x (.tail _ hx)
theorem NBT.cn {T : RSub} {l : List Ty} (h : NBT T l) : CnT T l := fun τ hτ => (h τ hτ).2

theorem OkAD.split {n : Nat} {l1 l2 : List Ty} (h : OkAD n (l1 ++ l2)) : OkAD n l1 ∧ OkAD n l2 :=
  ⟨fun τ hτ => h τ (List.mem_append_left _ hτ), fun τ hτ => h τ (List.mem_append_right _ hτ)⟩
theorem OkAD.tail {n : Nat} {τ : Ty} {l : List Ty} (h : OkAD n (τ :: l)) : OkAD n l := fun x hx => h x (.tail _ hx)

/-- The value environment of a checked declaration of W's result: monotypes, `OkTD`, mapped by
    `T` to canonical types without `bnd`. -/
theorem dec_factsD {n n0 : Nat} {T : RSub} {C : Ctx} {VE : ValEnv} {vb : AValBind}
    (hfx : FixR (rigidFromD n0) T)
    (hc : checkDec C (.val VE vb) = true) (hok : OkAD n (tysDec true (.val VE vb)))
    (hnb : NBT T (tysDec false (.val VE vb))) :
    AnnNilV vb ∧ ∀ q ∈ VE, q.2.1.bound = [] ∧ OkTD n q.2.1.body ∧ NBτ (rsb T q.2.1.body) ∧
      cnB (rsb T q.2.1.body) = true := by
  simp only [checkDec, Bool.and_eq_true, decide_eq_true_eq] at hc
  simp only [tysDec, ↓reduceIte, Bool.false_eq_true, List.nil_append] at hok hnb
  have hokv := (OkAD.split hok).2
  have hann := annNilV_of_okAD vb hokv
  refine ⟨hann, fun q hq => ?_⟩
  rw [← hc.2] at hq
  have h1 := valbind_ve_pent true vb hann q hq
  have h2 := valbind_ve_pent false vb hann q hq
  refine ⟨h1.1, okT_pentD hokv h1, fun v hv => ?_, ?_⟩
  · obtain ⟨c, hc', hvc⟩ := (mem_vars_rsb T _ v).mp hv
    obtain ⟨τ, h3, h4⟩ := h2.2.2 _ hc'
    exact (hnb τ h3).1 v ((mem_vars_rsb T τ v).mpr ⟨c, h4, hvc⟩)
  · have hq' : (q.1, (rsbScheme T q.2.1, q.2.2)) ∈ (rsbValBind T vb).ve := by
      rw [valbind_ve_rsb T vb hann]; simp only [rsbVE, List.mem_map]; exact ⟨q, hq, rfl⟩
    refine cn_valbind_ve _ (annNilV_rsb T vb hann) (fun τ hτ => ?_) _ hq'
    rw [tysValBind_sbD false T (fix_bnd0 hfx)] at hτ
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hτ
    exact (hnb x hx).2

theorem ctxRelD_mono {n0 : Nat} {T : RSub} {C C' : Ctx} {VE : ValEnv}
    (h : CtxRelD (SchRelD T) (rigidFromD n0) C C') (hm : ∀ q ∈ VE, q.2.1.bound = []) :
    CtxRelD (SchRelD T) (rigidFromD n0) (C.plusVE VE) (C'.plusVE (rsbVE T VE)) :=
  h.plusVE (VEMatch_monoD hm)

theorem mono_of_bound {σ : Scheme} (h : σ.bound = []) : σ = mono σ.body := by cases σ; simp_all [mono]

theorem ctxRelD_clos {n0 n : Nat} {T : RSub} {C C' : Ctx} {VE : ValEnv}
    (h : CtxRelD (SchRelD T) (rigidFromD n0) C C') (hfx : FixR (rigidFromD n0) T) (hcls : RespR T)
    (hVE : ∀ q ∈ VE, q.2.1.bound = [] ∧ OkTD n q.2.1.body ∧ NBτ (rsb T q.2.1.body) ∧ cnB (rsb T q.2.1.body) = true) :
    CtxRelD (SchRelD T) (rigidFromD n0) (C.plusVE (closGroup C.tyvars VE))
      (C'.plusVE (closGroup C'.tyvars (rsbVE T VE))) :=
  h.plusVE fun x => by
    rw [find?_closGroup, find?_closGroup, find?_rsbVE]
    cases hf : FMap.find? VE x with
    | none => trivial
    | some p =>
      obtain ⟨hb, hok, hnb, -⟩ := hVE _ (find?_mem hf)
      refine ⟨rfl, ?_⟩
      simp only
      rw [mono_of_bound hb]
      simp only [rsbScheme_monoD]
      exact closE_relD hok hcls (fun w hw _ => h.ftv (fun _ _ h => h.1) hfx w hw) hnb

theorem dec_head_relD {n0 n : Nat} {T : RSub} {U0 : List BVar} {C C' : Ctx} {VE : ValEnv} (path : List Nat)
    (hU : C.U = U0) (hU' : C'.U = U0) (hrel : CtxRelD (SchRelD T) (rigidFromD n0) C C')
    (hfx : FixR (rigidFromD n0) T) (hcls : RespR T)
    (hVE : ∀ q ∈ VE, q.2.1.bound = [] ∧ OkTD n q.2.1.body ∧ NBτ (rsb T q.2.1.body) ∧ cnB (rsb T q.2.1.body) = true) :
    NRelD T U0 ⟨path, C.U, [], veSchemes (closGroup C.tyvars VE)⟩
      ⟨path, C'.U, [], veSchemes (closGroup C'.tyvars (rsbVE T VE))⟩ := by
  refine ⟨hU, rfl, by rw [hU, hU'], rfl, by simp [veSchemes, closGroup_eq, FMap.mapV, rsbVE], fun i h h' => ?_⟩
  have hi : i < VE.length := by simpa [veSchemes, closGroup_eq, FMap.mapV] using h
  simp only [veSchemes, closGroup_eq, FMap.mapV, rsbVE, List.map_map, List.getElem_map, Function.comp]
  have hm : VE[i] ∈ VE := List.getElem_mem hi
  obtain ⟨hb, hok, hnb, hcn⟩ := hVE _ hm
  have e : VE[i].2.1 = mono VE[i].2.1.body := mono_of_bound hb
  rw [e, rsbScheme_monoD]
  exact closE_instD hok hcls (fun v hv => hfx v (rigidFromD_bnd n0 hv))
    (fun w hw _ => hrel.ftv (fun _ _ h => h.1) hfx w hw) hnb hcn

theorem nodesAtPat_relD' (T : RSub) {U U' U0 : List BVar} (hU : U = U0) (hU' : U' = U0) (p : AAtPat)
    (path : List Nat) (hcn : CnT T (tysAtPat p)) :
    F2 (NRelD T U0) (nodesAtPat U path (stripAtPat p)) (nodesAtPat U' path (stripAtPat (rsbAtPat T p))) := by
  subst hU hU'; exact nodesAtPat_relD T _ p path hcn

theorem nodesPat_relD' (T : RSub) {U U' U0 : List BVar} (hU : U = U0) (hU' : U' = U0) (p : APat)
    (path : List Nat) (hcn : CnT T (tysPat p)) :
    F2 (NRelD T U0) (nodesPat U path (stripPat p)) (nodesPat U' path (stripPat (rsbPat T p))) := by
  subst hU hU'; exact nodesPat_relD T _ p path hcn

/-! ## Expressions -/

section
variable (T : RSub) (n0 n : Nat) (U0 : List BVar) (hfx : FixR (rigidFromD n0) T) (hcls : RespR T)
include hfx hcls

mutual
theorem nodesAtExp_relD : ∀ (x : AAtExp) (C C' : Ctx) (path : List Nat), C.U = U0 → checkAtExp C x = true →
    CtxRelD (SchRelD T) (rigidFromD n0) C C' → OkAD n (tysAtExp true x) → NBT T (tysAtExp false x) →
    F2 (NRelD T U0) (nodesAtExp C path (stripAtExp x)) (nodesAtExp C' path (stripAtExp (rsbAtExp T x)))
  | .scon sc τ, C, C', path, hU, hc, hrel, _, _ => .cons (nrelD_mk hU (hrel.2.1.symm.trans hU)
      (by simp [rsbAtExp, stripAtExp]) rfl (monoCn_nil T)) .nil
  | .var lv inst τ, C, C', path, hU, hc, hrel, _, _ =>
    .cons (nrelD_mk hU (hrel.2.1.symm.trans hU) (by simp [rsbAtExp, stripAtExp]) rfl (monoCn_nil T)) .nil
  | .con lc inst τ, C, C', path, hU, hc, hrel, _, _ =>
    .cons (nrelD_mk hU (hrel.2.1.symm.trans hU) (by simp [rsbAtExp, stripAtExp]) rfl (monoCn_nil T)) .nil
  | .op o inst τ, C, C', path, hU, hc, hrel, _, _ =>
    .cons (nrelD_mk hU (hrel.2.1.symm.trans hU) (by simp [rsbAtExp, stripAtExp]) rfl (monoCn_nil T)) .nil
  | .unit, C, C', path, hU, hc, hrel, _, _ =>
    .cons (nrelD_mk hU (hrel.2.1.symm.trans hU) (by simp [rsbAtExp, stripAtExp, tUnitTy, rsb, rsbList]) rfl
      (monoCn_nil T)) .nil
  | .nil τ, C, C', path, hU, hc, hrel, _, _ =>
    .cons (nrelD_mk hU (hrel.2.1.symm.trans hU) (by simp [rsbAtExp, stripAtExp]) rfl (monoCn_nil T)) .nil
  | .tuple e1 e2 e3, C, C', path, hU, hc, hrel, hok, hnb => by
    have hc' := hc
    simp only [checkAtExp, Bool.and_eq_true] at hc
    simp only [tysAtExp] at hok hnb
    obtain ⟨hok12, hok3⟩ := OkAD.split hok; obtain ⟨hok1, hok2⟩ := OkAD.split hok12
    obtain ⟨hnb12, hnb3⟩ := NBT.app hnb; obtain ⟨hnb1, hnb2⟩ := NBT.app hnb12
    exact forall2_append (forall2_append (forall2_append
      (.cons (nrelD_mk hU (hrel.2.1.symm.trans hU) (by
          simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]; exact tyS_atexpD (T := T) hc') rfl
          (monoCn_nil T)) .nil)
      (nodesExp_relD e1 C C' _ hU hc.1.1 hrel hok1 hnb1)) (nodesExp_relD e2 C C' _ hU hc.1.2 hrel hok2 hnb2))
      (nodesExpOpt_relD e3 C C' _ hU hc.2 hrel hok3 hnb3)
  | .record r, C, C', path, hU, hc, hrel, hok, hnb => by
    have hc' := hc
    simp only [checkAtExp] at hc
    simp only [tysAtExp] at hok hnb
    exact forall2_append (.cons (nrelD_mk hU (hrel.2.1.symm.trans hU) (by
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]; exact tyS_atexpD (T := T) hc') rfl
        (monoCn_nil T)) .nil)
      (nodesExpRowOpt_relD r C C' _ hU hc hrel hok hnb)
  | .update x inst τ r, C, C', path, hU, hc, hrel, hok, hnb => by
    simp only [checkAtExp, Bool.and_eq_true] at hc
    simp only [tysAtExp] at hok hnb
    exact forall2_append (.cons (nrelD_mk hU (hrel.2.1.symm.trans hU) (by simp [rsbAtExp, stripAtExp]) rfl
        (monoCn_nil T)) .nil)
      (nodesExpRow_relD r C C' _ hU hc.1.2 hrel (OkAD.tail hok) hnb.cons)
  | .letE d e, C, C', path, hU, hc, hrel, hok, hnb => by
    have hc' := hc
    simp only [checkAtExp, Bool.and_eq_true] at hc
    simp only [tysAtExp] at hok hnb
    obtain ⟨hok1, hok2⟩ := OkAD.split hok; obtain ⟨hnb1, hnb2⟩ := NBT.app hnb
    cases d with
    | val VE vb =>
      obtain ⟨-, hVE⟩ := dec_factsD hfx hc.1 hok1 hnb1
      exact forall2_append (forall2_append
        (.cons (nrelD_mk hU (hrel.2.1.symm.trans hU) (by
          simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]; exact tyS_atexpD (T := T) hc') rfl
          (monoCn_nil T)) .nil)
        (nodesDec_relD (.val VE vb) C C' _ hU hc.1 hrel hok1 hnb1))
        (nodesExp_relD e _ _ _ hU hc.2 (ctxRelD_clos hrel hfx hcls hVE) hok2 hnb2)
  | .paren e, C, C', path, hU, hc, hrel, hok, hnb => by
    have hc' := hc
    simp only [checkAtExp] at hc
    simp only [tysAtExp] at hok hnb
    exact forall2_append (.cons (nrelD_mk hU (hrel.2.1.symm.trans hU) (by
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]; exact tyS_atexpD (T := T) hc') rfl
        (monoCn_nil T)) .nil)
      (nodesExp_relD e C C' _ hU hc hrel hok hnb)
theorem nodesExpRow_relD : ∀ (r : AExpRow) (C C' : Ctx) (path : List Nat), C.U = U0 → checkExpRow C r = true →
    CtxRelD (SchRelD T) (rigidFromD n0) C C' → OkAD n (tysExpRow true r) → NBT T (tysExpRow false r) →
    F2 (NRelD T U0) (nodesExpRow C path (stripExpRow r)) (nodesExpRow C' path (stripExpRow (rsbExpRow T r)))
  | .field l e rest, C, C', path, hU, hc, hrel, hok, hnb => by
    have hc' := hc
    simp only [checkExpRow, Bool.and_eq_true] at hc
    simp only [tysExpRow] at hok hnb
    obtain ⟨hok1, hok2⟩ := OkAD.split hok; obtain ⟨hnb1, hnb2⟩ := NBT.app hnb
    exact forall2_append (forall2_append
      (.cons (nrelD_mk hU (hrel.2.1.symm.trans hU) (rowSD (T := T) hc') rfl (monoCn_nil T)) .nil)
      (nodesExp_relD e C C' _ hU hc.1 hrel hok1 hnb1)) (nodesExpRowOpt_relD rest C C' _ hU hc.2 hrel hok2 hnb2)
theorem nodesExpRowOpt_relD : ∀ (r : Option AExpRow) (C C' : Ctx) (path : List Nat), C.U = U0 →
    checkExpRowOpt C r = true → CtxRelD (SchRelD T) (rigidFromD n0) C C' → OkAD n (tysExpRowOpt true r) →
    NBT T (tysExpRowOpt false r) →
    F2 (NRelD T U0) (nodesExpRowOpt C path (stripExpRowOpt r)) (nodesExpRowOpt C' path (stripExpRowOpt (rsbExpRowOpt T r)))
  | none, _, _, _, _, _, _, _, _ => .nil
  | some r, C, C', path, hU, hc, hrel, hok, hnb => nodesExpRow_relD r C C' path hU hc hrel hok hnb
theorem nodesExp_relD : ∀ (x : AExp) (C C' : Ctx) (path : List Nat), C.U = U0 → checkExpS C x = true →
    CtxRelD (SchRelD T) (rigidFromD n0) C C' → OkAD n (tysExp true x) → NBT T (tysExp false x) →
    F2 (NRelD T U0) (nodesExp C path (stripExp x)) (nodesExp C' path (stripExp (rsbExp T x)))
  | .atexp a, C, C', path, hU, hc, hrel, hok, hnb => by
    have hc' := hc
    simp only [checkExpS] at hc
    simp only [tysExp] at hok hnb
    exact forall2_append (.cons (nrelD_mk hU (hrel.2.1.symm.trans hU) (by
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]; exact tyS_expD (T := T) hc') rfl
        (monoCn_nil T)) .nil)
      (nodesAtExp_relD a C C' _ hU hc hrel hok hnb)
  | .app e a, C, C', path, hU, hc, hrel, hok, hnb => by
    have hc' := hc
    simp only [checkExpS, Bool.and_eq_true] at hc
    simp only [tysExp] at hok hnb
    obtain ⟨hok1, hok2⟩ := OkAD.split hok; obtain ⟨hnb1, hnb2⟩ := NBT.app hnb
    exact forall2_append (forall2_append
      (.cons (nrelD_mk hU (hrel.2.1.symm.trans hU) (by
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]; exact tyS_expD (T := T) hc') rfl
        (monoCn_nil T)) .nil)
      (nodesExp_relD e C C' _ hU hc.1.1 hrel hok1 hnb1)) (nodesAtExp_relD a C C' _ hU hc.1.2 hrel hok2 hnb2)
  | .lam p e, C, C', path, hU, hc, hrel, hok, hnb => by
    have hc' := hc
    simp only [checkExpS, Bool.and_eq_true] at hc
    simp only [tysExp] at hok hnb
    obtain ⟨hok1, hok2⟩ := OkAD.split hok; obtain ⟨hnb1, hnb2⟩ := NBT.app hnb
    have hrel' : CtxRelD (SchRelD T) (rigidFromD n0) (C.plusVE (stripAtPat p).ve)
        (C'.plusVE (stripAtPat (rsbAtPat T p)).ve) := by
      rw [rsbAtPat_ve_strip, stripAtPat_ve]
      exact ctxRelD_mono hrel fun q hq => (atpat_ve p q hq).1
    exact forall2_append (forall2_append
      (.cons (nrelD_mk hU (hrel.2.1.symm.trans hU) (by
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]; exact tyS_expD (T := T) hc') rfl
        (monoCn_nil T)) .nil)
      (nodesAtPat_relD' T hU (hrel.2.1.symm.trans hU) p _ hnb1.cn))
      (nodesExp_relD e _ _ _ hU (by rw [stripAtPat_ve]; exact hc.2) hrel' hok2 hnb2)
  | .caseE e m, C, C', path, hU, hc, hrel, hok, hnb => by
    have hc' := hc
    simp only [checkExpS, Bool.and_eq_true] at hc
    simp only [tysExp] at hok hnb
    obtain ⟨hok1, hok2⟩ := OkAD.split hok; obtain ⟨hnb1, hnb2⟩ := NBT.app hnb
    exact forall2_append (forall2_append
      (.cons (nrelD_mk hU (hrel.2.1.symm.trans hU) (by
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]; exact tyS_expD (T := T) hc') rfl
        (monoCn_nil T)) .nil)
      (nodesExp_relD e C C' _ hU hc.1.1 hrel hok1 hnb1)) (nodesMatch_relD m C C' _ hU hc.1.2 hrel hok2 hnb2)
theorem nodesExpOpt_relD : ∀ (x : Option AExp) (C C' : Ctx) (path : List Nat), C.U = U0 → checkExpOpt C x = true →
    CtxRelD (SchRelD T) (rigidFromD n0) C C' → OkAD n (tysExpOpt true x) → NBT T (tysExpOpt false x) →
    F2 (NRelD T U0) (nodesExpOpt C path (stripExpOpt x)) (nodesExpOpt C' path (stripExpOpt (rsbExpOpt T x)))
  | none, _, _, _, _, _, _, _, _ => .nil
  | some e, C, C', path, hU, hc, hrel, hok, hnb => nodesExp_relD e C C' path hU hc hrel hok hnb
theorem nodesMatch_relD : ∀ (m : AMatch) (C C' : Ctx) (path : List Nat), C.U = U0 → checkMatch C m = true →
    CtxRelD (SchRelD T) (rigidFromD n0) C C' → OkAD n (tysMatch true m) → NBT T (tysMatch false m) →
    F2 (NRelD T U0) (nodesMatch C path (stripMatch m)) (nodesMatch C' path (stripMatch (rsbMatch T m)))
  | .mk (.mk p e) rest, C, C', path, hU, hc, hrel, hok, hnb => by
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
      (.cons (nrelD_mk hU (hrel.2.1.symm.trans hU) (by
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]; exact tyS_mruleD (T := T) hc.1) rfl
        (monoCn_nil T)) .nil)
      (nodesPat_relD' T hU (hrel.2.1.symm.trans hU) p _ hnb1.cn))
      (nodesExp_relD e _ _ _ hU (by rw [stripPat_ve]; exact hc1.2) hrel' hok2 hnb2))
      (nodesMatchOpt_relD rest C C' _ hU (by
        intro m0 hm0; subst hm0
        simp only [checkMatchOptAt, Bool.and_eq_true] at hc; exact hc.2.1) hrel hok3 hnb3)
theorem nodesMatchOpt_relD : ∀ (m : Option AMatch) (C C' : Ctx) (path : List Nat), C.U = U0 →
    (∀ m0, m = some m0 → checkMatch C m0 = true) →
    CtxRelD (SchRelD T) (rigidFromD n0) C C' → OkAD n (tysMatchOpt true m) → NBT T (tysMatchOpt false m) →
    F2 (NRelD T U0) (nodesMatchOpt C path (stripMatchOpt m)) (nodesMatchOpt C' path (stripMatchOpt (rsbMatchOpt T m)))
  | none, _, _, _, _, _, _, _, _ => .nil
  | some m, C, C', path, hU, hc, hrel, hok, hnb => nodesMatch_relD m C C' path hU (hc m rfl) hrel hok hnb
theorem nodesDec_relD : ∀ (d : ADec) (C C' : Ctx) (path : List Nat), C.U = U0 → checkDec C d = true →
    CtxRelD (SchRelD T) (rigidFromD n0) C C' → OkAD n (tysDec true d) → NBT T (tysDec false d) →
    F2 (NRelD T U0) (nodesDec C path (stripDec d)) (nodesDec C' path (stripDec (rsbDec T d)))
  | .val VE vb, C, C', path, hU, hc, hrel, hok, hnb => by
    obtain ⟨-, hVE⟩ := dec_factsD hfx hc hok hnb
    have hc' := hc
    simp only [checkDec, Bool.and_eq_true] at hc
    simp only [tysDec, ↓reduceIte, Bool.false_eq_true, List.nil_append] at hok hnb
    exact forall2_append (.cons (dec_head_relD path hU (hrel.2.1.symm.trans hU) hrel hfx hcls hVE) .nil)
      (nodesValBind_relD vb _ _ _ hU hc.1 (ctxRelD_mono hrel fun q hq => (hVE q hq).1) (OkAD.split hok).2 hnb)
theorem nodesValBind_relD : ∀ (vb : AValBind) (C C' : Ctx) (path : List Nat), C.U = U0 → checkValBind C vb = true →
    CtxRelD (SchRelD T) (rigidFromD n0) C C' → OkAD n (tysValBind true vb) → NBT T (tysValBind false vb) →
    F2 (NRelD T U0) (nodesValBind C path (stripValBind vb)) (nodesValBind C' path (stripValBind (rsbValBind T vb)))
  | .var x ann τ e rest, C, C', path, hU, hc, hrel, hok, hnb => by
    have hann := annNilV_of_okAD _ hok
    have hann' := hann
    unfold AnnNilV at hann'
    have hcnve : MonoCn T (veSchemes (stripValBind (.var x ann τ e rest)).ve) := by
      rw [stripValBind_ve]
      refine monoCn_of_ve (fun q hq => (valbind_ve_pent true _ hann q hq).1) fun q hq => ?_
      rw [← valbind_ve_rsb T _ hann] at hq
      refine cn_valbind_ve _ (annNilV_rsb T _ hann) (fun τ' hτ' => ?_) q hq
      rw [tysValBind_sbD false T (fix_bnd0 hfx)] at hτ'
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hτ'
      exact (hnb y hy).2
    simp only [checkValBind, Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [tysValBind, List.cons_append, annMark, hann'.1, ↓reduceIte, List.nil_append] at hok hnb
    obtain ⟨hok1, hok2⟩ := OkAD.split (OkAD.tail hok); obtain ⟨hnb1, hnb2⟩ := NBT.app hnb.cons
    have hce : checkExpS C e = true := by have := hc.1.1.2; rwa [hann'.1, plusU_nil] at this
    have e1 : (stripValBind (rsbValBind T (.var x ann τ e rest))).ve = rsbVE T (stripValBind (.var x ann τ e rest)).ve := by
      rw [stripValBind_ve, stripValBind_ve, valbind_ve_rsb T _ hann]
    have hn1 := nodesExp_relD e C C' (path ++ [0]) hU hce hrel hok1 hnb1
    rw [← plusU_nil C, ← plusU_nil C', ← hann'.1] at hn1
    exact forall2_append (forall2_append
      (.cons (nrelD_mk hU (hrel.2.1.symm.trans hU) (by simp [stripValBind, rsbValBind])
        (by rw [← veSchemes_rsb]; congr 1) hcnve) .nil) hn1)
      (nodesValBindOpt_relD rest C C' _ hU hc.2 hrel hok2 hnb2)
  | .pat p e, C, C', path, hU, hc, hrel, hok, hnb => by
    simp only [checkValBind, Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [tysValBind] at hok hnb
    obtain ⟨-, hok2⟩ := OkAD.split hok; obtain ⟨hnb1, hnb2⟩ := NBT.app hnb
    exact forall2_append (forall2_append
      (.cons (nrelD_mk hU (hrel.2.1.symm.trans hU) (by simp [stripValBind, rsbValBind, rsbAtPat_ty_strip])
        (by rw [← veSchemes_rsb]; congr 1; exact rsbAtPat_ve_strip T p) (monoCn_atpat T p hnb1.cn)) .nil)
      (nodesAtPat_relD' T hU (hrel.2.1.symm.trans hU) p _ hnb1.cn))
      (nodesExp_relD e C C' _ hU hc.1.2 hrel hok2 hnb2)
theorem nodesValBindOpt_relD : ∀ (vb : Option AValBind) (C C' : Ctx) (path : List Nat), C.U = U0 →
    checkValBindOpt C vb = true → CtxRelD (SchRelD T) (rigidFromD n0) C C' → OkAD n (tysValBindOpt true vb) →
    NBT T (tysValBindOpt false vb) →
    F2 (NRelD T U0) (nodesValBindOpt C path (stripValBindOpt vb)) (nodesValBindOpt C' path (stripValBindOpt (rsbValBindOpt T vb)))
  | none, _, _, _, _, _, _, _, _ => .nil
  | some vb, C, C', path, hU, hc, hrel, hok, hnb => nodesValBind_relD vb C C' path hU hc hrel hok hnb
end

end

end StandardElm.Stat.Complete.WDP
