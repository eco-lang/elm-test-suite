/-
  A Standard Definition of Elm? Mechanisation: node correspondence for expressions (plan step 11,
  milestone (b), section 9): the nodes of a checked phrase `x` (W's result) and of `T x`, both with
  the instance lists left out, in contexts `C` and `C'` such that the free variables of `T C` are
  free in `C'`, correspond one to one (`NRel`).
-/
import StandardElmMech.Stat.Complete.WNodeRel

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat

def NBm (T : FSub) (l : List Ty) : Prop := ∀ τ ∈ l, NBτ (sb T τ)

theorem NBm.app {T : FSub} {l1 l2 : List Ty} (h : NBm T (l1 ++ l2)) : NBm T l1 ∧ NBm T l2 :=
  ⟨fun τ hτ => h τ (List.mem_append_left _ hτ), fun τ hτ => h τ (List.mem_append_right _ hτ)⟩
theorem NBm.cons {T : FSub} {τ : Ty} {l : List Ty} (h : NBm T (τ :: l)) : NBm T l := fun x hx => h x (.tail _ hx)

theorem OkA.split {n : Nat} {l1 l2 : List Ty} (h : OkA n (l1 ++ l2)) : OkA n l1 ∧ OkA n l2 :=
  ⟨fun τ hτ => h τ (List.mem_append_left _ hτ), fun τ hτ => h τ (List.mem_append_right _ hτ)⟩
theorem OkA.tail {n : Nat} {τ : Ty} {l : List Ty} (h : OkA n (τ :: l)) : OkA n l := fun x hx => h x (.tail _ hx)

/-- The value environment of a checked declaration of W's result: monotypes, `OkT`, mapped by `T`
    to types without `bnd`. -/
theorem dec_facts {n : Nat} {T : FSub} {C : Ctx} {VE : ValEnv} {vb : AValBind}
    (hc : checkDec C (.val VE vb) = true) (hok : OkA n (tysDec true (.val VE vb)))
    (hnb : NBm T (tysDec false (.val VE vb))) :
    AnnNilV vb ∧ ∀ q ∈ VE, q.2.1.bound = [] ∧ OkT n q.2.1.body ∧ NBτ (sb T q.2.1.body) := by
  simp only [checkDec, Bool.and_eq_true, decide_eq_true_eq] at hc
  simp only [tysDec, ↓reduceIte, Bool.false_eq_true, List.nil_append] at hok hnb
  have hokv := (OkA.split hok).2
  have hann := annNilV_of_okA vb hokv
  refine ⟨hann, fun q hq => ?_⟩
  rw [← hc.2] at hq
  have h1 := valbind_ve_pent true vb hann q hq
  have h2 := valbind_ve_pent false vb hann q hq
  refine ⟨h1.1, okT_pent hokv h1, fun v hv => ?_⟩
  obtain ⟨c, hc', hvc⟩ := (vars_sb T _ v hv).resolve_left (by
    rintro ⟨e, rfl, he⟩
    obtain ⟨τ, h3, h4⟩ := h1.2.2 _ he
    obtain ⟨_, h5, _⟩ := hokv τ h3 _ h4; cases h5)
  obtain ⟨τ, h3, h4⟩ := h2.2.2 _ hc'
  exact hnb τ h3 v (vars_sb_of T τ c v h4 hvc)

theorem ctxRel_ftv_mono {n0 : Nat} {T : FSub} {C C' : Ctx} {VE : ValEnv}
    (h : CtxRel (FtvRel T) (rigidFrom n0) C C') (hm : ∀ q ∈ VE, q.2.1.bound = []) :
    CtxRel (FtvRel T) (rigidFrom n0) (C.plusVE VE) (C'.plusVE (sbVE T VE)) :=
  h.plusVE fun x => by
    have := VEMatch_mono (s := T) hm x
    revert this
    cases FMap.find? VE x <;> cases FMap.find? (sbVE T VE) x <;> simp only [OptRel, imp_self]
    exact fun ⟨e, hs⟩ => ⟨e, hs.1⟩

theorem ctxRel_ftv_clos {n0 n : Nat} {T : FSub} {C C' : Ctx} {VE : ValEnv}
    (h : CtxRel (FtvRel T) (rigidFrom n0) C C') (hfx : FixesR (rigidFrom n0) T)
    (hVE : ∀ q ∈ VE, q.2.1.bound = [] ∧ OkT n q.2.1.body ∧ NBτ (sb T q.2.1.body)) :
    CtxRel (FtvRel T) (rigidFrom n0) (C.plusVE (closGroup C.tyvars VE))
      (C'.plusVE (closGroup C'.tyvars (sbVE T VE))) :=
  h.plusVE fun x => by
    rw [find?_closGroup, find?_closGroup, find?_sbVE]
    cases hf : FMap.find? VE x with
    | none => trivial
    | some p =>
      obtain ⟨hb, hok, hnb⟩ := hVE _ (find?_mem hf)
      refine ⟨rfl, ?_⟩
      simp only
      have : p.1 = mono p.1.body := by obtain ⟨σ, _⟩ := p; cases σ; simp_all [mono]
      rw [this, sbScheme_mono]
      exact (closE_rel hok (fun a ha _ => h.ftv (fun _ _ h => h) hfx a ha) hnb).1

theorem litInst_sb (T : FSub) (sc : StandardElm.Src.SLit) (τ : Ty) : litInst sc (sb T τ) = (litInst sc τ).map (sb T) := by
  cases sc <;> rfl

theorem nodesAtPat_rel' (T : FSub) {U U' U0 : List BVar} (hU : U = U0) (hU' : U' = U0) (p : AAtPat)
    (path : List Nat) : F2 (NRel T U0) (nodesAtPat U path (stripAtPat p)) (nodesAtPat U' path (stripAtPat (sbAtPat T p))) := by
  subst hU hU'; exact nodesAtPat_rel T _ p path

theorem nodesPat_rel' (T : FSub) {U U' U0 : List BVar} (hU : U = U0) (hU' : U' = U0) (p : APat)
    (path : List Nat) : F2 (NRel T U0) (nodesPat U path (stripPat p)) (nodesPat U' path (stripPat (sbPat T p))) := by
  subst hU hU'; exact nodesPat_rel T _ p path

theorem dec_head_rel {n0 n : Nat} {T : FSub} {U0 : List BVar} {C C' : Ctx} {VE : ValEnv} (path : List Nat)
    (hU : C.U = U0) (hU' : C'.U = U0) (hrel : CtxRel (FtvRel T) (rigidFrom n0) C C')
    (hfx : FixesR (rigidFrom n0) T) (hcls : ∀ a, T a ≠ .var a → a.cls = .any)
    (hVE : ∀ q ∈ VE, q.2.1.bound = [] ∧ OkT n q.2.1.body ∧ NBτ (sb T q.2.1.body)) :
    NRel T U0 ⟨path, C.U, [], veSchemes (closGroup C.tyvars VE)⟩
      ⟨path, C'.U, [], veSchemes (closGroup C'.tyvars (sbVE T VE))⟩ := by
  refine ⟨hU, rfl, by rw [hU, hU'], rfl, by simp [veSchemes, closGroup_eq, FMap.mapV, sbVE], fun i h h' t hg => ?_⟩
  have hi : i < VE.length := by simpa [veSchemes, closGroup_eq, FMap.mapV] using h
  simp only [veSchemes, closGroup_eq, FMap.mapV, sbVE, List.map_map, List.getElem_map, Function.comp] at hg ⊢
  have hm : VE[i] ∈ VE := List.getElem_mem hi
  obtain ⟨hb, hok, hnb⟩ := hVE _ hm
  have : VE[i].2.1 = mono VE[i].2.1.body := by
    generalize VE[i] = q at hb ⊢; obtain ⟨_, σ, _⟩ := q; cases σ; simp_all [mono]
  rw [this] at hg ⊢
  rw [sbScheme_mono] at hg
  exact closE_inst hok (fun a ha _ => hrel.ftv (fun _ _ h => h) hfx a ha) hnb (fun i c => hfx _ rfl) hcls t hg

theorem tyS_exp {T : FSub} {C : Ctx} {e : AExp} (hc : checkExp C e = true) :
    (stripExp (sbExp T e)).ty = sb T (stripExp e).ty := by rw [stripExp_ty, stripExp_ty, sbExp_ty_chk T e C hc]
theorem tyS_atexp {T : FSub} {C : Ctx} {a : AAtExp} (hc : checkAtExp C a = true) :
    (stripAtExp (sbAtExp T a)).ty = sb T (stripAtExp a).ty := by rw [stripAtExp_ty, stripAtExp_ty, sbAtExp_ty_chk T a C hc]
theorem tyS_match {T : FSub} {C : Ctx} {m : AMatch} (hc : checkMatch C m = true) :
    (stripMatch (sbMatch T m)).ty = sb T (stripMatch m).ty := by rw [stripMatch_ty, stripMatch_ty, sbMatch_ty_chk T m C hc]
theorem tyS_mrule {T : FSub} {C : Ctx} {mr : AMRule} (hc : checkMRule C mr = true) :
    (stripMRule (sbMRule T mr)).ty = sb T (stripMRule mr).ty := by rw [stripMRule_ty, stripMRule_ty, sbMRule_ty_chk T mr C hc]
theorem rowS {T : FSub} {C : Ctx} {r : AExpRow} (hc : checkExpRow C r = true) :
    (stripExpRow (sbExpRow T r)).row.map (·.2) = ((stripExpRow r).row.map (·.2)).map (sb T) := by
  rw [stripExpRow_row, stripExpRow_row, sbExpRow_row_chk T r C hc, sbRow_eq]; simp

section
variable (T : FSub) (n0 n : Nat) (U0 : List BVar) (hfx : FixesR (rigidFrom n0) T)
  (hcls : ∀ a, T a ≠ .var a → a.cls = .any)
include hfx hcls

mutual
theorem nodesAtExp_rel : ∀ (x : AAtExp) (C C' : Ctx) (path : List Nat), C.U = U0 → checkAtExp C x = true →
    CtxRel (FtvRel T) (rigidFrom n0) C C' → OkA n (tysAtExp true x) → NBm T (tysAtExp false x) →
    F2 (NRel T U0) (nodesAtExp C path (stripAtExp x)) (nodesAtExp C' path (stripAtExp (sbAtExp T x)))
  | .scon sc τ, C, C', path, hU, hc, hrel, _, _ => .cons (nrel_mk hU (hrel.2.1.symm.trans hU)
      (by simp [sbAtExp, stripAtExp, litInst_sb]) rfl) .nil
  | .var lv inst τ, C, C', path, hU, hc, hrel, _, _ => .cons (nrel_mk hU (hrel.2.1.symm.trans hU) (by simp) rfl) .nil
  | .con lc inst τ, C, C', path, hU, hc, hrel, _, _ => .cons (nrel_mk hU (hrel.2.1.symm.trans hU) (by simp) rfl) .nil
  | .op o inst τ, C, C', path, hU, hc, hrel, _, _ => .cons (nrel_mk hU (hrel.2.1.symm.trans hU) (by simp) rfl) .nil
  | .unit, C, C', path, hU, hc, hrel, _, _ =>
    .cons (nrel_mk hU (hrel.2.1.symm.trans hU) (by simp [tUnitTy, sb, sbList]) rfl) .nil
  | .nil τ, C, C', path, hU, hc, hrel, _, _ => .cons (nrel_mk hU (hrel.2.1.symm.trans hU) (by simp) rfl) .nil
  | .tuple e1 e2 e3, C, C', path, hU, hc, hrel, hok, hnb => by
    have hc' := hc
    simp only [checkAtExp, Bool.and_eq_true] at hc
    simp only [tysAtExp] at hok hnb
    obtain ⟨hok12, hok3⟩ := OkA.split hok; obtain ⟨hok1, hok2⟩ := OkA.split hok12
    obtain ⟨hnb12, hnb3⟩ := NBm.app hnb; obtain ⟨hnb1, hnb2⟩ := NBm.app hnb12
    exact forall2_append (forall2_append (forall2_append
      (.cons (nrel_mk hU (hrel.2.1.symm.trans hU) (by simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]; exact tyS_atexp (T := T) hc') rfl) .nil)
      (nodesExp_rel e1 C C' _ hU hc.1.1 hrel hok1 hnb1)) (nodesExp_rel e2 C C' _ hU hc.1.2 hrel hok2 hnb2))
      (nodesExpOpt_rel e3 C C' _ hU hc.2 hrel hok3 hnb3)
  | .record r, C, C', path, hU, hc, hrel, hok, hnb => by
    have hc' := hc
    simp only [checkAtExp] at hc
    simp only [tysAtExp] at hok hnb
    exact forall2_append (.cons (nrel_mk hU (hrel.2.1.symm.trans hU) (by simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]; exact tyS_atexp (T := T) hc') rfl) .nil)
      (nodesExpRowOpt_rel r C C' _ hU hc hrel hok hnb)
  | .update x inst τ r, C, C', path, hU, hc, hrel, hok, hnb => by
    simp only [checkAtExp, Bool.and_eq_true] at hc
    simp only [tysAtExp] at hok hnb
    exact forall2_append (.cons (nrel_mk hU (hrel.2.1.symm.trans hU) (by simp) rfl) .nil)
      (nodesExpRow_rel r C C' _ hU hc.1.2 hrel hok.tail hnb.cons)
  | .letE d e, C, C', path, hU, hc, hrel, hok, hnb => by
    have hc' := hc
    simp only [checkAtExp, Bool.and_eq_true] at hc
    simp only [tysAtExp] at hok hnb
    obtain ⟨hok1, hok2⟩ := OkA.split hok; obtain ⟨hnb1, hnb2⟩ := NBm.app hnb
    cases d with
    | val VE vb =>
      obtain ⟨-, hVE⟩ := dec_facts hc.1 hok1 hnb1
      exact forall2_append (forall2_append
        (.cons (nrel_mk hU (hrel.2.1.symm.trans hU) (by simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]; exact tyS_atexp (T := T) hc') rfl) .nil)
        (nodesDec_rel (.val VE vb) C C' _ hU hc.1 hrel hok1 hnb1))
        (nodesExp_rel e _ _ _ hU hc.2 (ctxRel_ftv_clos hrel hfx hVE) hok2 hnb2)
  | .paren e, C, C', path, hU, hc, hrel, hok, hnb => by
    have hc' := hc
    simp only [checkAtExp] at hc
    simp only [tysAtExp] at hok hnb
    exact forall2_append (.cons (nrel_mk hU (hrel.2.1.symm.trans hU) (by simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]; exact tyS_atexp (T := T) hc') rfl) .nil)
      (nodesExp_rel e C C' _ hU hc hrel hok hnb)
theorem nodesExpRow_rel : ∀ (r : AExpRow) (C C' : Ctx) (path : List Nat), C.U = U0 → checkExpRow C r = true →
    CtxRel (FtvRel T) (rigidFrom n0) C C' → OkA n (tysExpRow true r) → NBm T (tysExpRow false r) →
    F2 (NRel T U0) (nodesExpRow C path (stripExpRow r)) (nodesExpRow C' path (stripExpRow (sbExpRow T r)))
  | .field l e rest, C, C', path, hU, hc, hrel, hok, hnb => by
    have hc' := hc
    simp only [checkExpRow, Bool.and_eq_true] at hc
    simp only [tysExpRow] at hok hnb
    obtain ⟨hok1, hok2⟩ := OkA.split hok; obtain ⟨hnb1, hnb2⟩ := NBm.app hnb
    exact forall2_append (forall2_append
      (.cons (nrel_mk hU (hrel.2.1.symm.trans hU) (rowS (T := T) hc') rfl) .nil)
      (nodesExp_rel e C C' _ hU hc.1 hrel hok1 hnb1)) (nodesExpRowOpt_rel rest C C' _ hU hc.2 hrel hok2 hnb2)
theorem nodesExpRowOpt_rel : ∀ (r : Option AExpRow) (C C' : Ctx) (path : List Nat), C.U = U0 →
    checkExpRowOpt C r = true → CtxRel (FtvRel T) (rigidFrom n0) C C' → OkA n (tysExpRowOpt true r) →
    NBm T (tysExpRowOpt false r) →
    F2 (NRel T U0) (nodesExpRowOpt C path (stripExpRowOpt r)) (nodesExpRowOpt C' path (stripExpRowOpt (sbExpRowOpt T r)))
  | none, _, _, _, _, _, _, _, _ => .nil
  | some r, C, C', path, hU, hc, hrel, hok, hnb => nodesExpRow_rel r C C' path hU hc hrel hok hnb
theorem nodesExp_rel : ∀ (x : AExp) (C C' : Ctx) (path : List Nat), C.U = U0 → checkExp C x = true →
    CtxRel (FtvRel T) (rigidFrom n0) C C' → OkA n (tysExp true x) → NBm T (tysExp false x) →
    F2 (NRel T U0) (nodesExp C path (stripExp x)) (nodesExp C' path (stripExp (sbExp T x)))
  | .atexp a, C, C', path, hU, hc, hrel, hok, hnb => by
    have hc' := hc
    simp only [checkExp] at hc
    simp only [tysExp] at hok hnb
    exact forall2_append (.cons (nrel_mk hU (hrel.2.1.symm.trans hU) (by simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]; exact tyS_exp (T := T) hc') rfl) .nil)
      (nodesAtExp_rel a C C' _ hU hc hrel hok hnb)
  | .app e a, C, C', path, hU, hc, hrel, hok, hnb => by
    have hc' := hc
    simp only [checkExp, Bool.and_eq_true] at hc
    simp only [tysExp] at hok hnb
    obtain ⟨hok1, hok2⟩ := OkA.split hok; obtain ⟨hnb1, hnb2⟩ := NBm.app hnb
    exact forall2_append (forall2_append
      (.cons (nrel_mk hU (hrel.2.1.symm.trans hU) (by simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]; exact tyS_exp (T := T) hc') rfl) .nil)
      (nodesExp_rel e C C' _ hU hc.1.1 hrel hok1 hnb1)) (nodesAtExp_rel a C C' _ hU hc.1.2 hrel hok2 hnb2)
  | .lam p e, C, C', path, hU, hc, hrel, hok, hnb => by
    have hc' := hc
    simp only [checkExp, Bool.and_eq_true] at hc
    simp only [tysExp] at hok hnb
    obtain ⟨hok1, hok2⟩ := OkA.split hok; obtain ⟨-, hnb2⟩ := NBm.app hnb
    have hrel' : CtxRel (FtvRel T) (rigidFrom n0) (C.plusVE (stripAtPat p).ve)
        (C'.plusVE (stripAtPat (sbAtPat T p)).ve) := by
      rw [sbAtPat_ve_strip, stripAtPat_ve]
      exact ctxRel_ftv_mono hrel fun q hq => (atpat_ve p q hq).1
    exact forall2_append (forall2_append
      (.cons (nrel_mk hU (hrel.2.1.symm.trans hU) (by simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]; exact tyS_exp (T := T) hc') rfl) .nil)
      (nodesAtPat_rel' T hU (hrel.2.1.symm.trans hU) p _))
      (nodesExp_rel e _ _ _ hU (by rw [stripAtPat_ve]; exact hc.2) hrel' hok2 hnb2)
  | .caseE e m, C, C', path, hU, hc, hrel, hok, hnb => by
    have hc' := hc
    simp only [checkExp, Bool.and_eq_true] at hc
    simp only [tysExp] at hok hnb
    obtain ⟨hok1, hok2⟩ := OkA.split hok; obtain ⟨hnb1, hnb2⟩ := NBm.app hnb
    exact forall2_append (forall2_append
      (.cons (nrel_mk hU (hrel.2.1.symm.trans hU) (by simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]; exact tyS_exp (T := T) hc') rfl) .nil)
      (nodesExp_rel e C C' _ hU hc.1.1 hrel hok1 hnb1)) (nodesMatch_rel m C C' _ hU hc.1.2 hrel hok2 hnb2)
theorem nodesExpOpt_rel : ∀ (x : Option AExp) (C C' : Ctx) (path : List Nat), C.U = U0 → checkExpOpt C x = true →
    CtxRel (FtvRel T) (rigidFrom n0) C C' → OkA n (tysExpOpt true x) → NBm T (tysExpOpt false x) →
    F2 (NRel T U0) (nodesExpOpt C path (stripExpOpt x)) (nodesExpOpt C' path (stripExpOpt (sbExpOpt T x)))
  | none, _, _, _, _, _, _, _, _ => .nil
  | some e, C, C', path, hU, hc, hrel, hok, hnb => nodesExp_rel e C C' path hU hc hrel hok hnb
theorem nodesMatch_rel : ∀ (m : AMatch) (C C' : Ctx) (path : List Nat), C.U = U0 → checkMatch C m = true →
    CtxRel (FtvRel T) (rigidFrom n0) C C' → OkA n (tysMatch true m) → NBm T (tysMatch false m) →
    F2 (NRel T U0) (nodesMatch C path (stripMatch m)) (nodesMatch C' path (stripMatch (sbMatch T m)))
  | .mk (.mk p e) rest, C, C', path, hU, hc, hrel, hok, hnb => by
    simp only [checkMatch, Bool.and_eq_true] at hc
    have hc1 := hc.1
    simp only [checkMRule, Bool.and_eq_true] at hc1
    simp only [tysMatch, tysMRule] at hok hnb
    obtain ⟨hok12, hok3⟩ := OkA.split hok; obtain ⟨hok1, hok2⟩ := OkA.split hok12
    obtain ⟨hnb12, hnb3⟩ := NBm.app hnb; obtain ⟨-, hnb2⟩ := NBm.app hnb12
    have hrel' : CtxRel (FtvRel T) (rigidFrom n0) (C.plusVE (stripPat p).ve)
        (C'.plusVE (stripPat (sbPat T p)).ve) := by
      rw [sbPat_ve_strip, stripPat_ve]
      exact ctxRel_ftv_mono hrel fun q hq => (pat_ve p q hq).1
    exact forall2_append (forall2_append (forall2_append
      (.cons (nrel_mk hU (hrel.2.1.symm.trans hU) (by simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]; exact tyS_mrule (T := T) hc.1) rfl) .nil)
      (nodesPat_rel' T hU (hrel.2.1.symm.trans hU) p _))
      (nodesExp_rel e _ _ _ hU (by rw [stripPat_ve]; exact hc1.2) hrel' hok2 hnb2))
      (nodesMatchOpt_rel rest C C' _ hU (by
        intro m0 hm0; subst hm0
        simp only [checkMatchOptAt, Bool.and_eq_true] at hc; exact hc.2.1) hrel hok3 hnb3)
theorem nodesMatchOpt_rel : ∀ (m : Option AMatch) (C C' : Ctx) (path : List Nat), C.U = U0 →
    (∀ m0, m = some m0 → checkMatch C m0 = true) →
    CtxRel (FtvRel T) (rigidFrom n0) C C' → OkA n (tysMatchOpt true m) → NBm T (tysMatchOpt false m) →
    F2 (NRel T U0) (nodesMatchOpt C path (stripMatchOpt m)) (nodesMatchOpt C' path (stripMatchOpt (sbMatchOpt T m)))
  | none, _, _, _, _, _, _, _, _ => .nil
  | some m, C, C', path, hU, hc, hrel, hok, hnb => nodesMatch_rel m C C' path hU (hc m rfl) hrel hok hnb
theorem nodesDec_rel : ∀ (d : ADec) (C C' : Ctx) (path : List Nat), C.U = U0 → checkDec C d = true →
    CtxRel (FtvRel T) (rigidFrom n0) C C' → OkA n (tysDec true d) → NBm T (tysDec false d) →
    F2 (NRel T U0) (nodesDec C path (stripDec d)) (nodesDec C' path (stripDec (sbDec T d)))
  | .val VE vb, C, C', path, hU, hc, hrel, hok, hnb => by
    obtain ⟨-, hVE⟩ := dec_facts hc hok hnb
    have hc' := hc
    simp only [checkDec, Bool.and_eq_true] at hc
    simp only [tysDec, ↓reduceIte, Bool.false_eq_true, List.nil_append] at hok hnb
    exact forall2_append (.cons (dec_head_rel path hU (hrel.2.1.symm.trans hU) hrel hfx hcls hVE) .nil)
      (nodesValBind_rel vb _ _ _ hU hc.1 (ctxRel_ftv_mono hrel fun q hq => (hVE q hq).1) (OkA.split hok).2 hnb)
theorem nodesValBind_rel : ∀ (vb : AValBind) (C C' : Ctx) (path : List Nat), C.U = U0 → checkValBind C vb = true →
    CtxRel (FtvRel T) (rigidFrom n0) C C' → OkA n (tysValBind true vb) → NBm T (tysValBind false vb) →
    F2 (NRel T U0) (nodesValBind C path (stripValBind vb)) (nodesValBind C' path (stripValBind (sbValBind T vb)))
  | .var x ann τ e rest, C, C', path, hU, hc, hrel, hok, hnb => by
    have hann := annNilV_of_okA _ hok
    have hann' := hann
    unfold AnnNilV at hann'
    simp only [checkValBind, Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [tysValBind, List.cons_append, annMark, hann'.1, ↓reduceIte, List.nil_append] at hok hnb
    obtain ⟨hok1, hok2⟩ := OkA.split hok.tail; obtain ⟨hnb1, hnb2⟩ := NBm.app hnb.cons
    have hce : checkExp C e = true := by have := hc.1.1.2; rwa [hann'.1, plusU_nil] at this
    have e1 : (stripValBind (sbValBind T (.var x ann τ e rest))).ve = sbVE T (stripValBind (.var x ann τ e rest)).ve := by
      rw [stripValBind_ve, stripValBind_ve, valbind_ve_sb T _ hann]
    have hn1 := nodesExp_rel e C C' (path ++ [0]) hU hce hrel hok1 hnb1
    rw [← plusU_nil C, ← plusU_nil C', ← hann'.1] at hn1
    exact forall2_append (forall2_append
      (.cons (nrel_mk hU (hrel.2.1.symm.trans hU) (by simp [stripValBind, sbValBind])
        (by rw [← veSchemes_sb]; congr 1)) .nil) hn1)
      (nodesValBindOpt_rel rest C C' _ hU hc.2 hrel hok2 hnb2)
  | .pat p e, C, C', path, hU, hc, hrel, hok, hnb => by
    simp only [checkValBind, Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [tysValBind] at hok hnb
    obtain ⟨-, hok2⟩ := OkA.split hok; obtain ⟨-, hnb2⟩ := NBm.app hnb
    exact forall2_append (forall2_append
      (.cons (nrel_mk hU (hrel.2.1.symm.trans hU) (by simp [sbAtPat_ty_strip])
        (by rw [← veSchemes_sb]; congr 1; exact sbAtPat_ve_strip T p)) .nil)
      (nodesAtPat_rel' T hU (hrel.2.1.symm.trans hU) p _))
      (nodesExp_rel e C C' _ hU hc.1.2 hrel hok2 hnb2)
theorem nodesValBindOpt_rel : ∀ (vb : Option AValBind) (C C' : Ctx) (path : List Nat), C.U = U0 →
    checkValBindOpt C vb = true → CtxRel (FtvRel T) (rigidFrom n0) C C' → OkA n (tysValBindOpt true vb) →
    NBm T (tysValBindOpt false vb) →
    F2 (NRel T U0) (nodesValBindOpt C path (stripValBindOpt vb)) (nodesValBindOpt C' path (stripValBindOpt (sbValBindOpt T vb)))
  | none, _, _, _, _, _, _, _, _ => .nil
  | some vb, C, C', path, hU, hc, hrel, hok, hnb => nodesValBind_rel vb C C' path hU hc hrel hok hnb
end

end

end StandardElm.Stat.Complete
