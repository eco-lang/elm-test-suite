/-
  A Standard Definition of Elm? Mechanisation: completeness of `coreGen` on expressions,
  declarations and groups, plan step 11, milestone (a). For a checked annotated phrase, a
  generator context that simulates the checker's context (`Sim`), and the valuation that reads
  the derivation's types at the phrase's nodes, the phrase's constraints hold and its term
  evaluates to its type (normalised). By structural induction on the annotated phrase, following
  `checkExpS`.
-/
import StandardElmMech.Stat.Complete.CorePat

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat

variable {ν : Val} {f : TyName → TyName}

/-! ## The members of a group -/

theorem checkAnn_elab {C : Ctx} {ty : Src.BTy} {U' : List BVar} {τ : Ty} (h : checkAnn C (some (ty, U')) τ = true) :
    elabTy (C.plusU U') ty = some τ := by
  simp only [checkAnn, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.2

mutual
theorem gVBEnv_rel {C0 : Ctx} : (vb : AValBind) → ∀ {C : Ctx} {p : Path}, TySim f C C0 →
    checkValBind C vb = true → (∀ q, ν (q.reverse ++ p) = rdValBind vb q) → RelL ν (gVBEnv C0 p vb.erase) vb.ve
  | .var x ann τ e rest, C, p, hL, h, hr => by
    simp only [checkValBind, Bool.and_eq_true] at h
    obtain ⟨⟨⟨ha, _⟩, _⟩, hrest⟩ := h
    have hm : GOK ν (memberInfo C0 p (ann.map Prod.fst))
        (if ann.isSome = true then annScheme (annU ann) τ else mono τ) := by
      cases ann with
      | none =>
        simp only [Option.map_none, memberInfo, Option.isSome_none, Bool.false_eq_true, ite_false]
        exact gok_mono_mv ((slot hr (0)))
      | some a =>
        obtain ⟨ty, U'⟩ := a
        simp only [Option.map_some, memberInfo, Option.isSome_some, ite_true, annU]
        split
        · rename_i r hr'
          have ht : annT C0 ty = some (ofTy r) := by simp [annT, hr']
          split
          · rename_i hc
            exact gok_ann U' (annT_ok (hL.same (C' := C.plusU U') (fun _ => rfl)) (checkAnn_elab ha) ht) hc
          · split
            · rename_i hgood
              obtain ⟨e, hgt⟩ := annR_ok (hL.same (C' := C.plusU U') (fun _ => rfl)) (checkAnn_elab ha) hr'
              subst e
              exact gok_tmpl (instOf_canon _ τ) (hgt hgood)
            · exact gok_ann_shape U' (annT_ok (hL.same (C' := C.plusU U') (fun _ => rfl)) (checkAnn_elab ha) ht)
        · trivial
    cases rest with
    | none =>
      simp only [AValBind.erase, AValBind.eraseOpt, gVBEnv, gVBEnvOpt, AValBind.ve]
      exact RelL.modify (RelL.single hm) RelL.nil
    | some vb =>
      simp only [checkValBindOpt] at hrest
      simp only [AValBind.erase, AValBind.eraseOpt, gVBEnv, gVBEnvOpt, AValBind.ve]
      exact RelL.modify (RelL.single hm) (gVBEnv_rel vb hL hrest (child 2 hr (fun q => rfl)))
  | .pat q0 e, C, p, hL, h, hr => by
    simp only [AValBind.erase, gVBEnv, AValBind.ve]
    exact penvAt_rel q0 (child 0 hr (fun q => rfl))
end

theorem groupSol_holds {cs : List Con} (h : Holds ν cs) : Holds ν (groupSol cs) := by
  unfold groupSol
  split
  · split
    · rename_i st hu; exact unifyCs_ok hu ν h
    · exact Holds.nil
  · exact Holds.nil

/-! ## Literals and operators -/

theorem litT_ok {sc : Src.SLit} {τ : Ty} {p : Path} (h : genAt (typeOf sc) (litInst sc τ) τ = true)
    (hr : ν (0 :: p) = hN τ) : Holds ν (litT sc p).2 ∧ (litT sc p).1.ev ν = hN τ := by
  cases sc with
  | int n =>
    refine ⟨Holds.cons.mpr ⟨?_, Holds.nil⟩, hr⟩
    simp only [Con.holds, T.ev, hr]
    exact adm_hN (adm_num_of_lit h)
  | float m e => rw [genAt_mono h]; exact ⟨Holds.nil, by simp only [litT, ev_ofTy, hN_tFloatTy]⟩
  | char c => rw [genAt_mono h]; exact ⟨Holds.nil, by simp only [litT, ev_ofTy, hN_tCharTy]⟩
  | str s => rw [genAt_mono h]; exact ⟨Holds.nil, by simp only [litT, ev_ofTy, hN_tStringTy]⟩

/-! ## Expressions -/

mutual
theorem gAtExp_ok : (a : AAtExp) → ∀ {C : Ctx} {Γ : GCtx} {p : Path}, Sim ν f Γ C → checkAtExp C a = true →
    (∀ q, ν (q.reverse ++ p) = rdAtExp a q) → Holds ν (gAtExp Γ p a.erase).2 ∧ (gAtExp Γ p a.erase).1.ev ν = hN a.ty
  | .scon sc τ, C, Γ, p, _, h, hr => by
    simp only [checkAtExp] at h
    simp only [AAtExp.erase, gAtExp, AAtExp.ty]
    exact litT_ok h ((slot hr (0)))
  | .var lv inst τ, C, Γ, p, hS, h, hr => by
    simp only [checkAtExp] at h
    obtain ⟨σ, is, hl, hg⟩ := lookGen h
    exact occT_ok hS hl hg hr
  | .con lc inst τ, C, Γ, p, hS, h, hr => by
    simp only [checkAtExp] at h
    obtain ⟨σ, is, hl, hg⟩ := lookGen h
    exact occT_ok hS hl hg hr
  | .op o inst τ, C, Γ, p, hS, h, hr => by
    simp only [checkAtExp] at h
    simp only [AAtExp.erase, gAtExp, AAtExp.ty]
    cases ho : OTstat o with
    | none => rw [ho] at h; cases h
    | some σs =>
      obtain ⟨σ, is⟩ := σs
      rw [ho] at h
      simp only at h ⊢
      exact schT_ok h hr
  | .unit, _, _, _, _, _, _ => ⟨Holds.nil, by simp only [AAtExp.erase, gAtExp, AAtExp.ty, ev_ofTy, hN_tUnitTy]⟩
  | .tuple e1 e2 e3, C, Γ, p, hS, h, hr => by
    simp only [checkAtExp, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨c1, v1⟩ := gExp_ok e1 hS h1 (child 0 hr (fun q => rfl))
    obtain ⟨c2, v2⟩ := gExp_ok e2 hS h2 (child 1 hr (fun q => rfl))
    obtain ⟨c3, v3⟩ := gExpOpt_ok e3 hS h3 (child 2 hr (fun q => rfl))
    simp only [AAtExp.erase, gAtExp, AAtExp.ty]
    generalize gExp Γ (0 :: p) e1.erase = r1 at c1 v1 ⊢
    generalize gExp Γ (1 :: p) e2.erase = r2 at c2 v2 ⊢
    generalize gExpOpt Γ (2 :: p) (AExp.eraseOpt e3) = r3 at c3 v3 ⊢
    obtain ⟨t1, cs1⟩ := r1
    obtain ⟨t2, cs2⟩ := r2
    obtain ⟨t3, cs3⟩ := r3
    simp only at c1 v1 c2 v2 c3 v3 ⊢
    refine ⟨Holds.append.mpr ⟨Holds.append.mpr ⟨c1, c2⟩, c3⟩, ?_⟩
    rw [ev_tupleT, v1, v2, v3, hN_tupleTy]
  | .nil τ, C, Γ, p, _, h, hr => by
    simp only [checkAtExp] at h
    obtain ⟨τ0, rfl⟩ := isListTy_spec h
    refine ⟨Holds.nil, ?_⟩
    simp only [AAtExp.erase, gAtExp, AAtExp.ty, T.ev, T.evList, (slot hr (0)), hN_listTy]
    rfl
  | .record row, C, Γ, p, hS, h, hr => by
    simp only [checkAtExp] at h
    obtain ⟨c, v⟩ := gExpRowOpt_ok row hS h (child 0 hr (fun q => rfl))
    simp only [AAtExp.erase, gAtExp, AAtExp.ty]
    generalize gExpRowOpt Γ (0 :: p) (AExpRow.eraseOpt row) = r at c v ⊢
    obtain ⟨rr, cs⟩ := r
    simp only at c v ⊢
    refine ⟨c, ?_⟩
    simp only [T.ev, v, hN]
    rfl
  | .update x inst τ row, C, Γ, p, hS, h, hr => by
    simp only [checkAtExp, Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, hrec⟩, h3⟩, hsub⟩ := h
    obtain ⟨σ, is, hl, hg⟩ := lookGen h1
    obtain ⟨c0, v0⟩ := occT_ok hS hl hg (child 0 hr (fun q => rfl))
    obtain ⟨c1, v1⟩ := gExpRow_ok row hS h3 (child 1 hr (fun q => rfl))
    simp only [AAtExp.erase, gAtExp, AAtExp.ty]
    generalize occT Γ ⟨none, x⟩ (0 :: p) = r0 at c0 v0 ⊢
    generalize gExpRow Γ (1 :: p) row.erase = r1 at c1 v1 ⊢
    obtain ⟨tx, cs0⟩ := r0
    obtain ⟨rr, cs1⟩ := r1
    simp only at c0 v0 c1 v1 ⊢
    exact ⟨Holds.append.mpr ⟨Holds.append.mpr ⟨c0, c1⟩, has_ok tx rr _ τ v0 v1 (sub_of_subB hrec hsub)⟩, v0⟩
  | .letE d e, C, Γ, p, hS, h, hr => by
    simp only [checkAtExp, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨c0, v0⟩ := gDec_ok d hS h1 (child 0 hr (fun q => rfl))
    simp only [AAtExp.erase, gAtExp, AAtExp.ty]
    generalize gDec Γ (0 :: p) d.erase = r0 at c0 v0 ⊢
    obtain ⟨L, cs0⟩ := r0
    simp only at c0 v0 ⊢
    obtain ⟨c1, v1⟩ := gExp_ok e (Sim.plusVE hS v0) h2 (child 1 hr (fun q => rfl))
    generalize gExp (Γ.add L) (1 :: p) e.erase = r1 at c1 v1 ⊢
    obtain ⟨t, cs1⟩ := r1
    simp only at c1 v1 ⊢
    exact ⟨Holds.append.mpr ⟨c0, c1⟩, v1⟩
  | .paren e, C, Γ, p, hS, h, hr => by
    simp only [checkAtExp] at h
    simp only [AAtExp.erase, gAtExp, AAtExp.ty]
    exact gExp_ok e hS h (child 0 hr (fun q => rfl))
theorem gExpRow_ok : (r : AExpRow) → ∀ {C : Ctx} {Γ : GCtx} {p : Path}, Sim ν f Γ C → checkExpRow C r = true →
    (∀ q, ν (q.reverse ++ p) = rdExpRow r q) → Holds ν (gExpRow Γ p r.erase).2 ∧ T.evRow ν (gExpRow Γ p r.erase).1 = hNRow r.row
  | .field l e rest, C, Γ, p, hS, h, hr => by
    simp only [checkExpRow, Bool.and_eq_true] at h
    obtain ⟨c1, v1⟩ := gExp_ok e hS h.1 (child 0 hr (fun q => rfl))
    obtain ⟨c2, v2⟩ := gExpRowOpt_ok rest hS h.2 (child 1 hr (fun q => rfl))
    simp only [AExpRow.erase, gExpRow, AExpRow.row]
    generalize gExp Γ (0 :: p) e.erase = r1 at c1 v1 ⊢
    generalize gExpRowOpt Γ (1 :: p) (AExpRow.eraseOpt rest) = r2 at c2 v2 ⊢
    obtain ⟨t, cs1⟩ := r1
    obtain ⟨rr, cs2⟩ := r2
    simp only at c1 v1 c2 v2 ⊢
    refine ⟨Holds.append.mpr ⟨c1, c2⟩, ?_⟩
    rw [evRow_rmod, v2, hNRow_modify, modify_eq_rmod]
    simp only [T.evRow, hNRow, v1]
theorem gExpRowOpt_ok : (r : Option AExpRow) → ∀ {C : Ctx} {Γ : GCtx} {p : Path}, Sim ν f Γ C →
    checkExpRowOpt C r = true → (∀ q, ν (q.reverse ++ p) = rdExpRowOpt r q) →
    Holds ν (gExpRowOpt Γ p (AExpRow.eraseOpt r)).2 ∧
      T.evRow ν (gExpRowOpt Γ p (AExpRow.eraseOpt r)).1 = hNRow (AExpRow.rowOpt r)
  | none, _, _, _, _, _, _ => ⟨Holds.nil, rfl⟩
  | some r, C, Γ, p, hS, h, hr => by
    simp only [checkExpRowOpt] at h
    simp only [AExpRow.eraseOpt, gExpRowOpt, AExpRow.rowOpt]
    exact gExpRow_ok r hS h hr
theorem gExp_ok : (a : AExp) → ∀ {C : Ctx} {Γ : GCtx} {p : Path}, Sim ν f Γ C → checkExpS C a = true →
    (∀ q, ν (q.reverse ++ p) = rdExp a q) → Holds ν (gExp Γ p a.erase).2 ∧ (gExp Γ p a.erase).1.ev ν = hN a.ty
  | .atexp a, C, Γ, p, hS, h, hr => by
    simp only [checkExpS] at h
    simp only [AExp.erase, gExp, AExp.ty]
    exact gAtExp_ok a hS h (child 0 hr (fun q => rfl))
  | .app e a, C, Γ, p, hS, h, hr => by
    simp only [checkExpS, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨τ, hτ⟩ := fn_of_match h3
    obtain ⟨c1, v1⟩ := gExp_ok e hS h1 (child 0 hr (fun q => rfl))
    obtain ⟨c2, v2⟩ := gAtExp_ok a hS h2 (child 1 hr (fun q => rfl))
    have h2' : ν (2 :: p) = hN τ := by rw [(slot hr (2))]; show hN (AExp.ty e).cod = _; rw [hτ]; rfl
    simp only [AExp.erase, gExp, AExp.ty, hτ, Ty.cod]
    generalize gExp Γ (0 :: p) e.erase = r1 at c1 v1 ⊢
    generalize gAtExp Γ (1 :: p) a.erase = r2 at c2 v2 ⊢
    obtain ⟨te, cs1⟩ := r1
    obtain ⟨ta, cs2⟩ := r2
    simp only at c1 v1 c2 v2 ⊢
    refine ⟨Holds.append.mpr ⟨Holds.append.mpr ⟨c1, c2⟩, Holds.cons.mpr ⟨?_, Holds.nil⟩⟩, h2'⟩
    simp only [Con.holds, T.ev, v1, v2, hτ, h2']
    rfl
  | .lam q0 e, C, Γ, p, hS, h, hr => by
    simp only [checkExpS, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨c1, v1⟩ := gAtPat_ok hS q0 h1 (child 0 hr (fun q => rfl))
    have hR := penvAt_rel q0 (child 0 hr (fun q => rfl))
    obtain ⟨c2, v2⟩ := gExp_ok e (Sim.plusVE hS hR) h2 (child 1 hr (fun q => rfl))
    simp only [AExp.erase, gExp, AExp.ty]
    generalize gAtPat Γ (0 :: p) q0.erase = r1 at c1 v1 ⊢
    generalize gExp (Γ.add (penvAt (0 :: p) q0.erase)) (1 :: p) e.erase = r2 at c2 v2 ⊢
    obtain ⟨tq, cs1⟩ := r1
    obtain ⟨te, cs2⟩ := r2
    simp only at c1 v1 c2 v2 ⊢
    exact ⟨Holds.append.mpr ⟨c1, c2⟩, by simp only [T.ev, v1, v2, hN]⟩
  | .caseE e m, C, Γ, p, hS, h, hr => by
    simp only [checkExpS, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨τ, hτ⟩ := fn_of_match h3
    obtain ⟨c1, v1⟩ := gExp_ok e hS h1 (child 0 hr (fun q => rfl))
    obtain ⟨c2, v2⟩ := gMatch_ok m hS h2 (child 1 hr (fun q => rfl))
    have h2' : ν (2 :: p) = hN τ := by rw [(slot hr (2))]; show hN (AMatch.ty m).cod = _; rw [hτ]; rfl
    simp only [AExp.erase, gExp, AExp.ty, hτ, Ty.cod]
    generalize gExp Γ (0 :: p) e.erase = r1 at c1 v1 ⊢
    generalize gMatch Γ (1 :: p) m.erase = r2 at c2 v2 ⊢
    obtain ⟨te, cs1⟩ := r1
    obtain ⟨tm, cs2⟩ := r2
    simp only at c1 v1 c2 v2 ⊢
    refine ⟨Holds.append.mpr ⟨Holds.append.mpr ⟨c1, c2⟩, Holds.cons.mpr ⟨?_, Holds.nil⟩⟩, h2'⟩
    simp only [Con.holds, T.ev, v1, v2, hτ, h2']
    rfl
theorem gExpOpt_ok : (a : Option AExp) → ∀ {C : Ctx} {Γ : GCtx} {p : Path}, Sim ν f Γ C → checkExpOpt C a = true →
    (∀ q, ν (q.reverse ++ p) = rdExpOpt a q) →
    Holds ν (gExpOpt Γ p (AExp.eraseOpt a)).2 ∧ (gExpOpt Γ p (AExp.eraseOpt a)).1.map (T.ev ν) = (AExp.tyOpt a).map hN
  | none, _, _, _, _, _, _ => ⟨Holds.nil, rfl⟩
  | some a, C, Γ, p, hS, h, hr => by
    simp only [checkExpOpt] at h
    obtain ⟨c, v⟩ := gExp_ok a hS h hr
    simp only [AExp.eraseOpt, gExpOpt, AExp.tyOpt]
    generalize gExp Γ p a.erase = r at c v ⊢
    obtain ⟨t, cs⟩ := r
    simp only at c v ⊢
    exact ⟨c, by simp only [Option.map_some, v]⟩
theorem gMatch_ok : (m : AMatch) → ∀ {C : Ctx} {Γ : GCtx} {p : Path}, Sim ν f Γ C → checkMatch C m = true →
    (∀ q, ν (q.reverse ++ p) = rdMatch m q) → Holds ν (gMatch Γ p m.erase).2 ∧ (gMatch Γ p m.erase).1.ev ν = hN m.ty
  | .mk mr rest, C, Γ, p, hS, h, hr => by
    simp only [checkMatch, Bool.and_eq_true] at h
    obtain ⟨c1, v1⟩ := gMRule_ok mr hS h.1 (child 0 hr (fun q => rfl))
    obtain ⟨c2, v2⟩ := gMatchOpt_ok rest hS h.2 (child 1 hr (fun q => rfl))
    simp only [AMatch.erase, gMatch, AMatch.ty]
    generalize gMRule Γ (0 :: p) mr.erase = r1 at c1 v1 ⊢
    generalize gMatchOpt Γ (1 :: p) (AMatch.eraseOpt rest) = r2 at c2 v2 ⊢
    obtain ⟨t, cs1⟩ := r1
    obtain ⟨t', cs2⟩ := r2
    simp only at c1 v1 c2 v2 ⊢
    cases t' with
    | none => exact ⟨Holds.append.mpr ⟨c1, c2⟩, v1⟩
    | some t' =>
      simp only
      refine ⟨Holds.append.mpr ⟨Holds.append.mpr ⟨c1, c2⟩, Holds.cons.mpr ⟨?_, Holds.nil⟩⟩, v1⟩
      simp only [Con.holds, v2 t' rfl, v1]
theorem gMatchOpt_ok : (m : Option AMatch) → ∀ {C : Ctx} {Γ : GCtx} {p : Path} {τ : Ty}, Sim ν f Γ C →
    checkMatchOptAt C τ m = true → (∀ q, ν (q.reverse ++ p) = rdMatchOpt m q) →
    Holds ν (gMatchOpt Γ p (AMatch.eraseOpt m)).2 ∧
      ∀ t', (gMatchOpt Γ p (AMatch.eraseOpt m)).1 = some t' → t'.ev ν = hN τ
  | none, _, _, _, _, _, _, _ => ⟨Holds.nil, fun _ h => by cases h⟩
  | some m, C, Γ, p, τ, hS, h, hr => by
    simp only [checkMatchOptAt, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨c, v⟩ := gMatch_ok m hS h.1 hr
    simp only [AMatch.eraseOpt, gMatchOpt]
    generalize gMatch Γ p m.erase = r at c v ⊢
    obtain ⟨t, cs⟩ := r
    simp only at c v ⊢
    refine ⟨c, fun t' ht' => ?_⟩
    cases ht'
    rw [v, h.2]
theorem gMRule_ok : (mr : AMRule) → ∀ {C : Ctx} {Γ : GCtx} {p : Path}, Sim ν f Γ C → checkMRule C mr = true →
    (∀ q, ν (q.reverse ++ p) = rdMRule mr q) → Holds ν (gMRule Γ p mr.erase).2 ∧ (gMRule Γ p mr.erase).1.ev ν = hN mr.ty
  | .mk q0 e, C, Γ, p, hS, h, hr => by
    simp only [checkMRule, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨c1, v1⟩ := gPat_ok hS q0 h1 (child 0 hr (fun q => rfl))
    have hR := penv_rel q0 (child 0 hr (fun q => rfl))
    obtain ⟨c2, v2⟩ := gExp_ok e (Sim.plusVE hS hR) h2 (child 1 hr (fun q => rfl))
    simp only [AMRule.erase, gMRule, AMRule.ty]
    generalize gPat Γ (0 :: p) q0.erase = r1 at c1 v1 ⊢
    generalize gExp (Γ.add (penv (0 :: p) q0.erase)) (1 :: p) e.erase = r2 at c2 v2 ⊢
    obtain ⟨tq, cs1⟩ := r1
    obtain ⟨te, cs2⟩ := r2
    simp only at c1 v1 c2 v2 ⊢
    exact ⟨Holds.append.mpr ⟨c1, c2⟩, by simp only [T.ev, v1, v2, hN]⟩
theorem gDec_ok : (d : ADec) → ∀ {C : Ctx} {Γ : GCtx} {p : Path}, Sim ν f Γ C → checkDec C d = true →
    (∀ q, ν (q.reverse ++ p) = rdDec d q) → Holds ν (gDec Γ p d.erase).2 ∧ RelL ν (gDec Γ p d.erase).1 (d.result C)
  | .val VE vb, C, Γ, p, hS, h, hr => by
    simp only [checkDec, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    have hrv := child 0 hr (fun q => rfl)
    have hR : RelL ν (gVBEnv Γ.A (0 :: p) vb.erase) VE :=
      h2 ▸ gVBEnv_rel vb (C := C.plusVE VE) (hS.ty.same (C' := C.plusVE VE) (fun _ => rfl)) h1 hrv
    have c := gValBind_ok vb (Sim.plusVE hS hR) h1 hrv
    simp only [ADec.erase, gDec, ADec.result]
    exact ⟨c, RelL.close _ (groupSol_holds c) hR⟩
theorem gValBind_ok : (vb : AValBind) → ∀ {C : Ctx} {Γ : GCtx} {p : Path}, Sim ν f Γ C → checkValBind C vb = true →
    (∀ q, ν (q.reverse ++ p) = rdValBind vb q) → Holds ν (gValBind Γ p vb.erase)
  | .var x ann τ e rest, C, Γ, p, hS, h, hr => by
    simp only [checkValBind, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨ha, h1⟩, he⟩, hrest⟩ := h
    obtain ⟨c1, v1⟩ := gExp_ok e (Sim.plusU hS (annU ann)) h1 (child 1 hr (fun q => rfl))
    have c3 := gValBindOpt_ok rest hS hrest (child 2 hr (fun q => rfl))
    simp only [AValBind.erase, gValBind]
    generalize gExp Γ (1 :: p) e.erase = r1 at c1 v1 ⊢
    obtain ⟨te, cs1⟩ := r1
    simp only at c1 v1 ⊢
    refine Holds.append.mpr ⟨Holds.append.mpr ⟨Holds.append.mpr ⟨c1, Holds.cons.mpr ⟨?_, Holds.nil⟩⟩, ?_⟩, c3⟩
    · simp only [Con.holds, T.ev, v1, he, (slot hr (0))]
      rfl
    · cases ann with
      | none => exact Holds.nil
      | some a =>
        obtain ⟨ty, U'⟩ := a
        simp only [Option.map_some, annCs]
        split
        · rename_i t ht
          refine Holds.cons.mpr ⟨?_, Holds.nil⟩
          simp only [Con.holds, T.ev, (slot hr (0))]
          rw [annT_ok (hS.ty.same (C' := C.plusU U') (fun _ => rfl)) (checkAnn_elab ha) ht]
          rfl
        · exact Holds.nil
  | .pat q0 e, C, Γ, p, hS, h, hr => by
    simp only [checkValBind, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨c1, v1⟩ := gAtPat_ok hS q0 h1 (child 0 hr (fun q => rfl))
    obtain ⟨c2, v2⟩ := gExp_ok e hS h2 (child 1 hr (fun q => rfl))
    simp only [AValBind.erase, gValBind]
    generalize gAtPat Γ (0 :: p) q0.erase = r1 at c1 v1 ⊢
    generalize gExp Γ (1 :: p) e.erase = r2 at c2 v2 ⊢
    obtain ⟨tq, cs1⟩ := r1
    obtain ⟨te, cs2⟩ := r2
    simp only at c1 v1 c2 v2 ⊢
    refine Holds.append.mpr ⟨Holds.append.mpr ⟨c1, c2⟩, Holds.cons.mpr ⟨?_, Holds.nil⟩⟩
    simp only [Con.holds, v1, v2, h3]
theorem gValBindOpt_ok : (vb : Option AValBind) → ∀ {C : Ctx} {Γ : GCtx} {p : Path}, Sim ν f Γ C →
    checkValBindOpt C vb = true → (∀ q, ν (q.reverse ++ p) = rdValBindOpt vb q) →
    Holds ν (gValBindOpt Γ p (AValBind.eraseOpt vb))
  | none, _, _, _, _, _, _ => Holds.nil
  | some vb, C, Γ, p, hS, h, hr => by
    simp only [checkValBindOpt] at h
    simp only [AValBind.eraseOpt, gValBindOpt]
    exact gValBind_ok vb hS h hr
end

end StandardElm.Stat.Complete
