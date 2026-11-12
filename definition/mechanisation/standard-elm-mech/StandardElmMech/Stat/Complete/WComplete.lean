/-
  A Standard Definition of Elm? Mechanisation: the main induction L11 of plan step 11 (milestone
  (b), section 8), for expressions, matches, declarations and groups.

  For every state satisfying the invariant, every `S'` fixing the rigid variables and absorbing
  W's substitution, and every derivation `a'` of the phrase in a context no more general than
  `S'` applied to W's (`Pre`): W does not fail, and if it returns `(τ, a)` then an extension `T`
  of `S'` to the variables W created fixes the rigid variables, absorbs W's new substitution, and
  maps `τ` to the derivation's type and `a` to `a'` with the instance lists left out
  (`stripExp (sbExp T a) = stripExp a'`). Cases as in section 8: constants and occurrences (L2,
  `outP_instantiate`); application, `case` and matches (L9, `outP_unifyW`); abstraction and rules
  (L8, patterns); `let` (L3 then L4, `let_pre`); groups (monomorphic within the group: the
  entries, then the members, `unify` per member); pattern bindings.
-/
import StandardElmMech.Stat.Complete.WCompleteAux

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BAtPat BPat BAtExp BExp BMatch BMRule BDec BValBind)

/-! ## Conclusions -/

def AEPost (n0 : Nat) (st : WSt) (S' : FSub) (a' : AAtExp) (r : Ty × AAtExp) (st' : WSt) : Prop :=
  st.n ≤ st'.n ∧ SInv n0 st' ∧ OkT st'.n r.1 ∧ OkA st'.n (tysAtExp true r.2) ∧
    ∃ T, Found n0 S' st.n st' T ∧ sb T r.1 = a'.ty ∧ stripAtExp (sbAtExp T r.2) = stripAtExp a'

def EPost (n0 : Nat) (st : WSt) (S' : FSub) (a' : AExp) (r : Ty × AExp) (st' : WSt) : Prop :=
  st.n ≤ st'.n ∧ SInv n0 st' ∧ OkT st'.n r.1 ∧ OkA st'.n (tysExp true r.2) ∧
    ∃ T, Found n0 S' st.n st' T ∧ sb T r.1 = a'.ty ∧ stripExp (sbExp T r.2) = stripExp a'

def EOptPost (n0 : Nat) (st : WSt) (S' : FSub) (a' : Option AExp) (r : Option Ty × Option AExp) (st' : WSt) : Prop :=
  st.n ≤ st'.n ∧ SInv n0 st' ∧ (∀ τ, r.1 = some τ → OkT st'.n τ) ∧ OkA st'.n (tysExpOpt true r.2) ∧
    ∃ T, Found n0 S' st.n st' T ∧ sbOpt T r.1 = AExp.tyOpt a' ∧ stripExpOpt (sbExpOpt T r.2) = stripExpOpt a'

def MPost (n0 : Nat) (st : WSt) (S' : FSub) (m' : AMatch) (r : Ty × AMatch) (st' : WSt) : Prop :=
  st.n ≤ st'.n ∧ SInv n0 st' ∧ OkT st'.n r.1 ∧ OkA st'.n (tysMatch true r.2) ∧
    ∃ T, Found n0 S' st.n st' T ∧ sb T r.1 = m'.ty ∧ stripMatch (sbMatch T r.2) = stripMatch m'

def MOptPost (n0 : Nat) (st : WSt) (S' : FSub) (m' : Option AMatch) (r : Option AMatch) (st' : WSt) : Prop :=
  st.n ≤ st'.n ∧ SInv n0 st' ∧ OkA st'.n (tysMatchOpt true r) ∧
    ∃ T, Found n0 S' st.n st' T ∧ stripMatchOpt (sbMatchOpt T r) = stripMatchOpt m'

def MRPost (n0 : Nat) (st : WSt) (S' : FSub) (mr' : AMRule) (r : Ty × AMRule) (st' : WSt) : Prop :=
  st.n ≤ st'.n ∧ SInv n0 st' ∧ OkT st'.n r.1 ∧ OkA st'.n (tysMRule true r.2) ∧
    ∃ T, Found n0 S' st.n st' T ∧ sb T r.1 = mr'.ty ∧ stripMRule (sbMRule T r.2) = stripMRule mr'

def _root_.StandardElm.Stat.ADec.env : ADec → ValEnv
  | .val VE _ => VE

def DPost (n0 : Nat) (st : WSt) (S' : FSub) (d' : ADec) (ad : ADec) (st' : WSt) : Prop :=
  st.n ≤ st'.n ∧ SInv n0 st' ∧ OkA st'.n (tysDec true ad) ∧
    (∀ q ∈ ad.env, q.2.1.bound = [] ∧ OkT st'.n q.2.1.body) ∧
    ∃ T, Found n0 S' st.n st' T ∧ stripDec (sbDec T ad) = stripDec d' ∧ ∀ q ∈ ad.env, NBτ (sb T q.2.1.body)

def VBPost (n0 : Nat) (st : WSt) (S' : FSub) (vb' : AValBind) (r : AValBind) (st' : WSt) : Prop :=
  st.n ≤ st'.n ∧ SInv n0 st' ∧ OkA st'.n (tysValBind true r) ∧
    ∃ T, Found n0 S' st.n st' T ∧ stripValBind (sbValBind T r) = stripValBind vb'

def VBOptPost (n0 : Nat) (st : WSt) (S' : FSub) (vb' : Option AValBind) (r : Option AValBind) (st' : WSt) : Prop :=
  st.n ≤ st'.n ∧ SInv n0 st' ∧ OkA st'.n (tysValBindOpt true r) ∧
    ∃ T, Found n0 S' st.n st' T ∧ stripValBindOpt (sbValBindOpt T r) = stripValBindOpt vb'

/-! ## Helpers -/

theorem pent_schW {n : Nat} {l : List Ty} (hl : OkA n l) {q : String × (Scheme × IdStatus)} (h : PEnt l q) :
    SchW n q.2.1 := by
  have : q.2.1 = mono q.2.1.body := by obtain ⟨_, σ, _⟩ := q; cases σ; simp_all [PEnt, mono]
  rw [this]
  refine SchW_mono_scheme fun v hv => ?_
  obtain ⟨τ, h1, h2⟩ := h.2.2 v hv
  exact hl τ h1 v h2

theorem nb_of_pent {l : List Ty} (hl : NB l) {q : String × (Scheme × IdStatus)} (h : PEnt l q) : NBτ q.2.1.body :=
  fun v hv => by obtain ⟨τ, h1, h2⟩ := h.2.2 v hv; exact hl τ h1 v h2

theorem okT_pent {n : Nat} {l : List Ty} (hl : OkA n l) {q : String × (Scheme × IdStatus)} (h : PEnt l q) :
    OkT n q.2.1.body := fun v hv => by obtain ⟨τ, h1, h2⟩ := h.2.2 v hv; exact hl τ h1 v h2

/-- The environment of a pattern under `T` is the derivation's. -/
theorem pat_ve_eq {T : FSub} {ap p' : AAtPat} (h : stripAtPat (sbAtPat T ap) = stripAtPat p') :
    p'.ve = sbVE T ap.ve := by
  rw [← stripAtPat_ve p', ← h, stripAtPat_ve, sbAtPat_ve]

theorem pat_ve_eq' {T : FSub} {ap p' : APat} (h : stripPat (sbPat T ap) = stripPat p') :
    p'.ve = sbVE T ap.ve := by
  rw [← stripPat_ve p', ← h, stripPat_ve, sbPat_ve]

theorem atpat_ty_eq {T : FSub} {ap p' : AAtPat} (h : stripAtPat (sbAtPat T ap) = stripAtPat p') :
    sb T ap.ty = p'.ty := by
  rw [← sbAtPat_ty, ← stripAtPat_ty, h, stripAtPat_ty]

theorem pat_ty_eq {T : FSub} {ap p' : APat} (h : stripPat (sbPat T ap) = stripPat p') :
    sb T ap.ty = p'.ty := by
  rw [← sbPat_ty, ← stripPat_ty, h, stripPat_ty]

/-- The body of an abstraction or a rule: W's context with the pattern's environment, against
    the derivation's. -/
theorem pre_pat {n0 : Nat} {C C' : Ctx} {S' T : FSub} {st st1 : WSt} {VE : ValEnv} {l : List Ty}
    (hp : Pre n0 C C' S' st) (hn : st.n ≤ st1.n) (hi1 : SInv n0 st1) (hF : Found n0 S' st.n st1 T)
    (hVE : ∀ q ∈ VE, PEnt l q) (hl : OkA st1.n l) :
    Pre n0 (C.plusVE VE) (C'.plusVE (sbVE T VE)) T st1 :=
  ⟨hi1, (hp.ctxW.mono hn).plusVE fun q hq => pent_schW hl (hVE q hq),
    (hp.rel.congr hp.ctxW hF.agree).plusVE (VEMatch_mono fun q hq => (hVE q hq).1), hF.fix, hF.abs⟩

theorem esRel_mem {S : FSub} : ∀ (es : List (Option (BTy × List BVar) × Ty)) (vb' : AValBind),
    EsRel S es vb' → ∀ e ∈ es, sb S e.2 ∈ tysValBind false vb'
  | (ann, τ) :: es, .var _ ann' τ' _ rest, h, e, he => by
    unfold EsRel at h
    obtain ⟨-, h2, h3⟩ := h
    rcases List.mem_cons.mp he with rfl | he
    · simp [tysValBind, h2, annMark]
    · cases rest with
      | none => simp only at h3; subst h3; cases he
      | some vb =>
        have := esRel_mem es vb h3 e he
        simp [tysValBind, tysValBindOpt, this, annMark]
  | [], _, h, _, he => by cases he
  | _ :: _, .pat _ _, h, _, _ => by simp [EsRel] at h

def EsRelOpt (S : FSub) (es : List (Option (BTy × List BVar) × Ty)) : Option AValBind → Prop
  | none => es = []
  | some vb => EsRel S es vb

theorem okT_closed {n : Nat} {τ : Ty} (h : τ.vars = []) : OkT n τ := OkT_of_vars_nil h

theorem sb_closed {s : FSub} {τ : Ty} (h : τ.vars = []) : sb s τ = τ :=
  sb_eq_self_iff.mpr fun a ha => by rw [h] at ha; cases ha

/-! ## The main induction -/

mutual
theorem wAtExp_complete (fuel n0 : Nat) : ∀ (a : BAtExp) (C C' : Ctx) (S' : FSub) (st : WSt) (a' : AAtExp),
    Pre n0 C C' S' st → checkAtExp C' a' = true → a'.erase = a → NB (tysAtExp false a') →
    OutP (AEPost n0 st S' a') (wAtExp fuel (rigidFrom n0) C a st)
  | .scon sc, C, C', S', st, a', hp, hc, he, _ => by
    cases a' with
    | scon sc' τ' =>
      simp only [AAtExp.erase, BAtExp.scon.injEq] at he; subst he
      simp only [checkAtExp] at hc
      have hpost : ∀ τ0 : Ty, τ0.vars = [] → τ' = τ0 →
          OutP (AEPost n0 st S' (.scon sc' τ')) ((pure (τ0, AAtExp.scon sc' τ0) : WM (Ty × AAtExp)) st) := fun τ0 hv e =>
        outP_pure ⟨Nat.le_refl _, hp.inv, okT_closed hv, OkA.cons (okT_closed hv) OkA.nil, S', Found.refl hp,
          by simp [sb_closed hv, e, AAtExp.ty], by simp [sbAtExp, stripAtExp, sb_closed hv, e]⟩
      cases sc' with
      | int k => simp only [wAtExp]; trivial
      | float m e => simp only [wAtExp]; exact hpost _ rfl (genAt_mono hc)
      | char c => simp only [wAtExp]; exact hpost _ rfl (genAt_mono hc)
      | str s => simp only [wAtExp]; exact hpost _ rfl (genAt_mono hc)
    | _ => simp [AAtExp.erase] at he
  | .var lv, C, C', S', st, a', hp, hc, he, _ => by
    cases a' with
    | var lv' inst τ' =>
      simp only [AAtExp.erase, BAtExp.var.injEq] at he; subst he
      simp only [checkAtExp] at hc
      split at hc
      · rename_i σ' s' hlk
        obtain ⟨σ, hσ, hrel⟩ := hp.rel.lookup hp.fix (rigid_bnd n0) hlk
        simp only [wAtExp, hσ]
        refine outP_instantiate hp.inv (hp.ctxW _ _ _ hσ) hp.fix hp.abs
          (fun hab => hrel.2 hab _ (gen_of_genAt hc)) ?_
        intro ts τ st1 T hle _ hi1 hok _ hfx hab hag hcl hτ
        exact outP_pure ⟨hle, hi1, hok, OkA.cons hok OkA.nil, T, ⟨hfx, hab, hag, hcl⟩, hτ, by
          simp [sbAtExp, stripAtExp, hτ]⟩
      · cases hc
    | _ => simp [AAtExp.erase] at he
  | .con lc, C, C', S', st, a', hp, hc, he, _ => by
    cases a' with
    | con lc' inst τ' =>
      simp only [AAtExp.erase, BAtExp.con.injEq] at he; subst he
      simp only [checkAtExp] at hc
      split at hc
      · rename_i σ' s' hlk
        obtain ⟨σ, hσ, hrel⟩ := hp.rel.lookup hp.fix (rigid_bnd n0) hlk
        simp only [wAtExp, hσ]
        refine outP_instantiate hp.inv (hp.ctxW _ _ _ hσ) hp.fix hp.abs
          (fun hab => hrel.2 hab _ (gen_of_genAt hc)) ?_
        intro ts τ st1 T hle _ hi1 hok _ hfx hab hag hcl hτ
        exact outP_pure ⟨hle, hi1, hok, OkA.cons hok OkA.nil, T, ⟨hfx, hab, hag, hcl⟩, hτ, by
          simp [sbAtExp, stripAtExp, hτ]⟩
      · cases hc
    | _ => simp [AAtExp.erase] at he
  | .op o, C, C', S', st, a', hp, hc, he, _ => by
    cases a' with
    | op o' inst τ' =>
      simp only [AAtExp.erase, BAtExp.op.injEq] at he; subst he
      simp only [checkAtExp] at hc
      split at hc
      · rename_i σ s' hlk
        simp only [wAtExp, hlk]
        refine outP_instantiate hp.inv (otstat_schW hlk _) hp.fix hp.abs
          (fun hab => (otstat_rel hlk S').2 hab _ (gen_of_genAt hc)) ?_
        intro ts τ st1 T hle _ hi1 hok _ hfx hab hag hcl hτ
        exact outP_pure ⟨hle, hi1, hok, OkA.cons hok OkA.nil, T, ⟨hfx, hab, hag, hcl⟩, hτ, by
          simp [sbAtExp, stripAtExp, hτ]⟩
      · cases hc
    | _ => simp [AAtExp.erase] at he
  | .unit, C, C', S', st, a', hp, _, he, _ => by
    cases a' with
    | unit =>
      simp only [wAtExp]
      exact outP_pure ⟨Nat.le_refl _, hp.inv, okT_closed rfl, OkA.nil, S', Found.refl hp, rfl, rfl⟩
    | _ => simp [AAtExp.erase] at he
  | .nil, C, C', S', st, a', hp, hc, he, _ => by
    cases a' with
    | nil τ' =>
      simp only [checkAtExp] at hc
      obtain ⟨t, rfl⟩ := isListTy_spec hc
      simp only [wAtExp]
      refine outP_freshV (outP_pure ⟨Nat.le_succ _, hp.inv.fresh, OkT_list okT_fresh,
        OkA.cons (OkT_list okT_fresh) OkA.nil, ext1 S' st.n t, found_ext1 hp t, ?_, ?_⟩)
      · simp [AAtExp.ty, listTy_sb, sb, ext1_self]
      · simp [sbAtExp, stripAtExp, listTy_sb, sb, ext1_self]
    | _ => simp [AAtExp.erase] at he
  | .record _, C, C', S', st, a', hp, _, _, _ => by simp only [wAtExp]; trivial
  | .update _ _, C, C', S', st, a', hp, _, _, _ => by simp only [wAtExp]; trivial
  | .tuple e1 e2 e3, C, C', S', st, a', hp, hc, he, hnb => by
    cases a' with
    | tuple q1 q2 q3 =>
      simp only [AAtExp.erase, BAtExp.tuple.injEq] at he; obtain ⟨rfl, rfl, rfl⟩ := he
      simp only [checkAtExp, Bool.and_eq_true] at hc; obtain ⟨⟨hc1, hc2⟩, hc3⟩ := hc
      simp only [tysAtExp] at hnb; obtain ⟨hnb12, hnb3⟩ := NB.app hnb; obtain ⟨hnb1, hnb2⟩ := NB.app hnb12
      simp only [wAtExp]
      refine outP_bind (wExp_complete fuel n0 _ C C' S' st q1 hp hc1 rfl hnb1) ?_
      rintro ⟨τ1, a1⟩ st1 ⟨hn1, hi1, hok1, hokA1, T1, hF1, hty1, hs1⟩
      have hp1 := hp.next hi1 hn1 hF1
      refine outP_bind (wExp_complete fuel n0 _ C C' T1 st1 q2 hp1 hc2 rfl hnb2) ?_
      rintro ⟨τ2, a2⟩ st2 ⟨hn2, hi2, hok2, hokA2, T2, hF2, hty2, hs2⟩
      have hp2 := hp1.next hi2 hn2 hF2
      refine outP_bind (wExpOpt_complete fuel n0 _ C C' T2 st2 q3 hp2 hc3 rfl hnb3) ?_
      rintro ⟨τ3, a3⟩ st3 ⟨hn3, hi3, hok3, hokA3, T3, hF3, hty3, hs3⟩
      dsimp only at *
      refine outP_pure ⟨by omega, hi3, OkT_tuple (hok1.mono (by omega)) (hok2.mono hn3) hok3,
        ((hokA1.mono (by omega)).app (hokA2.mono hn3)).app hokA3, T3,
        (hF1.trans hF2 hn1).trans hF3 (by omega), ?_, ?_⟩
      · simp only [tupleTy_sb, AAtExp.ty, hty3]
        rw [hF3.sb_eq hok2, hty2, (hF2.trans hF3 hn2).sb_eq hok1, hty1]
      · simp only [sbAtExp, stripAtExp] at hs1 hs2 hs3 ⊢
        rw [hs3, sbExp_congr a2 (hF3.agreeOn hokA2), hs2,
          sbExp_congr a1 ((hF2.trans hF3 hn2).agreeOn hokA1), hs1]
    | _ => simp [AAtExp.erase] at he
  | .letE d e, C, C', S', st, a', hp, hc, he, hnb => by
    cases a' with
    | letE d' e' =>
      simp only [AAtExp.erase, BAtExp.letE.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      simp only [checkAtExp, Bool.and_eq_true] at hc; obtain ⟨hc1, hc2⟩ := hc
      simp only [tysAtExp] at hnb; obtain ⟨hnb1, hnb2⟩ := NB.app hnb
      simp only [wAtExp]
      refine outP_bind (wDec_complete fuel n0 _ C C' S' st d' hp hc1 rfl hnb1) ?_
      rintro ad st1 ⟨hn1, hi1, hokA1, henv, T1, hF1, hs1, hnbe⟩
      refine outP_getθ ?_
      cases ad with
      | val VE0 avb =>
        cases d' with
        | val VE' vb' =>
          simp only [sbDec, stripDec, ADec.val.injEq] at hs1
          simp only [ADec.result] at hc2
          simp only [ADec.env] at henv hnbe
          have hpre := let_pre hp hn1 hi1 hF1 (fun q hq => ⟨(henv q hq).1, (henv q hq).2, hnbe q hq⟩) hs1.1.symm
          refine outP_bind (wExp_complete fuel n0 _ _ _ T1 st1 e' hpre hc2 rfl hnb2) ?_
          rintro ⟨τ, ae⟩ st2 ⟨hn2, hi2, hok2, hokA2, T2, hF2, hty2, hs2⟩
          refine outP_pure ⟨by omega, hi2, hok2, (hokA1.mono hn2).app hokA2, T2, hF1.trans hF2 hn1, hty2, ?_⟩
          simp only [sbAtExp, stripAtExp] at hs2 ⊢
          rw [hs2, sbDec_congr _ (hF2.agreeOn hokA1)]
          simp only [sbDec, stripDec, hs1.1, hs1.2]
    | _ => simp [AAtExp.erase] at he
  | .paren e, C, C', S', st, a', hp, hc, he, hnb => by
    cases a' with
    | paren e' =>
      simp only [AAtExp.erase, BAtExp.paren.injEq] at he; subst he
      simp only [checkAtExp] at hc
      simp only [tysAtExp] at hnb
      simp only [wAtExp]
      refine outP_bind (wExp_complete fuel n0 _ C C' S' st e' hp hc rfl hnb) ?_
      rintro ⟨τ, ae⟩ st1 ⟨hn1, hi1, hok1, hokA1, T1, hF1, hty1, hs1⟩
      exact outP_pure ⟨hn1, hi1, hok1, hokA1, T1, hF1, hty1, by simp only [sbAtExp, stripAtExp, hs1]⟩
    | _ => simp [AAtExp.erase] at he
theorem wExp_complete (fuel n0 : Nat) : ∀ (e : BExp) (C C' : Ctx) (S' : FSub) (st : WSt) (a' : AExp),
    Pre n0 C C' S' st → checkExp C' a' = true → a'.erase = e → NB (tysExp false a') →
    OutP (EPost n0 st S' a') (wExp fuel (rigidFrom n0) C e st)
  | .atexp a, C, C', S', st, a', hp, hc, he, hnb => by
    cases a' with
    | atexp a'' =>
      simp only [AExp.erase, BExp.atexp.injEq] at he; subst he
      simp only [checkExp] at hc
      simp only [tysExp] at hnb
      simp only [wExp]
      refine outP_bind (wAtExp_complete fuel n0 _ C C' S' st a'' hp hc rfl hnb) ?_
      rintro ⟨τ, aa⟩ st1 ⟨hn1, hi1, hok1, hokA1, T1, hF1, hty1, hs1⟩
      exact outP_pure ⟨hn1, hi1, hok1, hokA1, T1, hF1, hty1, by simp only [sbExp, stripExp, hs1]⟩
    | _ => simp [AExp.erase] at he
  | .app e a, C, C', S', st, a', hp, hc, he, hnb => by
    cases a' with
    | app e' a'' =>
      simp only [AExp.erase, BExp.app.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      simp only [checkExp, Bool.and_eq_true] at hc; obtain ⟨⟨hc1, hc2⟩, hc3⟩ := hc
      obtain ⟨r, hr⟩ := fn_of_match hc3
      simp only [tysExp] at hnb; obtain ⟨hnb1, hnb2⟩ := NB.app hnb
      simp only [wExp]
      refine outP_bind (wExp_complete fuel n0 _ C C' S' st e' hp hc1 rfl hnb1) ?_
      rintro ⟨τ1, ae⟩ st1 ⟨hn1, hi1, hok1, hokA1, T1, hF1, hty1, hs1⟩
      have hp1 := hp.next hi1 hn1 hF1
      refine outP_bind (wAtExp_complete fuel n0 _ C C' T1 st1 a'' hp1 hc2 rfl hnb2) ?_
      rintro ⟨τ2, aa⟩ st2 ⟨hn2, hi2, hok2, hokA2, T2, hF2, hty2, hs2⟩
      have hp2 := hp1.next hi2 hn2 hF2
      dsimp only at *
      refine outP_freshV ?_
      have hF3 := found_ext1 hp2 r
      refine outP_unifyW hi2.fresh ((hok1.mono hn2).mono (Nat.le_succ _))
        (OkT_fn (hok2.mono (Nat.le_succ _)) okT_fresh) hF3.fix hF3.abs ?_ fun st4 hn4 hi4 hab4 => ?_
      · rw [hF3.sb_eq (hok1.mono hn2), hF2.sb_eq hok1, hty1, hr]
        simp only [sb, ext1_self, hF3.sb_eq hok2, hty2]
      · refine outP_pure ⟨by simp only [hn4]; omega, hi4, by rw [hn4]; exact okT_fresh,
          by rw [hn4]; exact ((hokA1.mono hn2).app hokA2).mono (Nat.le_succ _), ext1 T2 st2.n r,
          (hF1.trans hF2 hn1).trans ⟨hF3.fix, hab4, hF3.agree, hF3.cls⟩ (by omega), ?_, ?_⟩
        · simp [sb, ext1_self, AExp.ty, hr, Ty.cod]
        · simp only [sbExp, stripExp] at hs1 hs2 ⊢
          rw [sbAtExp_congr aa (hF3.agreeOn hokA2), hs2, sbExp_congr ae (hF3.agreeOn (hokA1.mono hn2)),
            sbExp_congr ae (hF2.agreeOn hokA1), hs1]
    | _ => simp [AExp.erase] at he
  | .lam p e, C, C', S', st, a', hp, hc, he, hnb => by
    cases a' with
    | lam p' e' =>
      simp only [AExp.erase, BExp.lam.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      simp only [checkExp, Bool.and_eq_true] at hc; obtain ⟨hc1, hc2⟩ := hc
      simp only [tysExp] at hnb; obtain ⟨hnb1, hnb2⟩ := NB.app hnb
      simp only [wExp]
      refine outP_bind (wAtPat_complete fuel n0 _ C C' C' S' st p' hp (lkC_refl C') hc1 rfl hnb1) ?_
      rintro ⟨τp, ap⟩ st1 ⟨hn1, hi1, hok1, hty1, hokA1, T1, hF1, hs1⟩
      dsimp only at *
      have hve := pat_ve_eq hs1
      have hpre := pre_pat hp hn1 hi1 hF1 (atpat_ve ap) hokA1
      rw [← hve] at hpre
      refine outP_bind (wExp_complete fuel n0 _ _ _ T1 st1 e' hpre hc2 rfl hnb2) ?_
      rintro ⟨τe, ae⟩ st2 ⟨hn2, hi2, hok2, hokA2, T2, hF2, hty2, hs2⟩
      dsimp only at *
      refine outP_pure ⟨by omega, hi2, OkT_fn (hok1.mono hn2) hok2, (hokA1.mono hn2).app hokA2, T2,
        hF1.trans hF2 hn1, ?_, ?_⟩
      · show Ty.fn (sb T2 τp) (sb T2 τe) = Ty.fn p'.ty e'.ty
        rw [hF2.sb_eq hok1, hty2, ← hty1, atpat_ty_eq hs1]
      · simp only [sbExp, stripExp] at hs2 ⊢
        rw [hs2, sbAtPat_congr ap (hF2.agreeOn hokA1), hs1]
    | _ => simp [AExp.erase] at he
  | .caseE e m, C, C', S', st, a', hp, hc, he, hnb => by
    cases a' with
    | caseE e' m' =>
      simp only [AExp.erase, BExp.caseE.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      simp only [checkExp, Bool.and_eq_true] at hc; obtain ⟨⟨hc1, hc2⟩, hc3⟩ := hc
      obtain ⟨r, hr⟩ := fn_of_match hc3
      simp only [tysExp] at hnb; obtain ⟨hnb1, hnb2⟩ := NB.app hnb
      simp only [wExp]
      refine outP_bind (wExp_complete fuel n0 _ C C' S' st e' hp hc1 rfl hnb1) ?_
      rintro ⟨τe, ae⟩ st1 ⟨hn1, hi1, hok1, hokA1, T1, hF1, hty1, hs1⟩
      have hp1 := hp.next hi1 hn1 hF1
      refine outP_bind (wMatch_complete fuel n0 _ C C' T1 st1 m' hp1 hc2 rfl hnb2) ?_
      rintro ⟨τm, am⟩ st2 ⟨hn2, hi2, hok2, hokA2, T2, hF2, hty2, hs2⟩
      have hp2 := hp1.next hi2 hn2 hF2
      dsimp only at *
      refine outP_freshV ?_
      have hF3 := found_ext1 hp2 r
      refine outP_unifyW hi2.fresh (hok2.mono (Nat.le_succ _))
        (OkT_fn ((hok1.mono hn2).mono (Nat.le_succ _)) okT_fresh) hF3.fix hF3.abs ?_ fun st4 hn4 hi4 hab4 => ?_
      · rw [hF3.sb_eq hok2, hty2, hr]
        simp only [sb, ext1_self, hF3.sb_eq (hok1.mono hn2), hF2.sb_eq hok1, hty1]
      · refine outP_pure ⟨by simp only [hn4]; omega, hi4, by rw [hn4]; exact okT_fresh,
          by rw [hn4]; exact ((hokA1.mono hn2).app hokA2).mono (Nat.le_succ _), ext1 T2 st2.n r,
          (hF1.trans hF2 hn1).trans ⟨hF3.fix, hab4, hF3.agree, hF3.cls⟩ (by omega), ?_, ?_⟩
        · simp [sb, ext1_self, AExp.ty, hr, Ty.cod]
        · simp only [sbExp, stripExp] at hs1 hs2 ⊢
          rw [sbMatch_congr am (hF3.agreeOn hokA2), hs2, sbExp_congr ae (hF3.agreeOn (hokA1.mono hn2)),
            sbExp_congr ae (hF2.agreeOn hokA1), hs1]
    | _ => simp [AExp.erase] at he
theorem wExpOpt_complete (fuel n0 : Nat) : ∀ (e : Option BExp) (C C' : Ctx) (S' : FSub) (st : WSt)
    (a' : Option AExp), Pre n0 C C' S' st → checkExpOpt C' a' = true → AExp.eraseOpt a' = e →
    NB (tysExpOpt false a') → OutP (EOptPost n0 st S' a') (wExpOpt fuel (rigidFrom n0) C e st)
  | none, C, C', S', st, a', hp, _, he, _ => by
    cases a' with
    | none =>
      simp only [wExpOpt]
      exact outP_pure ⟨Nat.le_refl _, hp.inv, (fun _ h => by cases h), OkA.nil, S', Found.refl hp, rfl, rfl⟩
    | some _ => simp [AExp.eraseOpt] at he
  | some e, C, C', S', st, a', hp, hc, he, hnb => by
    cases a' with
    | some e' =>
      simp only [AExp.eraseOpt, Option.some.injEq] at he; subst he
      simp only [checkExpOpt] at hc
      simp only [tysExpOpt] at hnb
      simp only [wExpOpt]
      refine outP_bind (wExp_complete fuel n0 _ C C' S' st e' hp hc rfl hnb) ?_
      rintro ⟨τ, ae⟩ st1 ⟨hn1, hi1, hok1, hokA1, T1, hF1, hty1, hs1⟩
      exact outP_pure ⟨hn1, hi1, (fun _ h => by cases h; exact hok1), hokA1, T1, hF1,
        by simp [sbOpt, AExp.tyOpt, hty1], by simp only [sbExpOpt, stripExpOpt, hs1]⟩
    | none => simp [AExp.eraseOpt] at he
theorem wMatch_complete (fuel n0 : Nat) : ∀ (m : BMatch) (C C' : Ctx) (S' : FSub) (st : WSt) (m' : AMatch),
    Pre n0 C C' S' st → checkMatch C' m' = true → m'.erase = m → NB (tysMatch false m') →
    OutP (MPost n0 st S' m') (wMatch fuel (rigidFrom n0) C m st)
  | .mk mr rest, C, C', S', st, m', hp, hc, he, hnb => by
    cases m' with
    | mk mr' rest' =>
      simp only [AMatch.erase, BMatch.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      simp only [checkMatch, Bool.and_eq_true] at hc; obtain ⟨hc1, hc2⟩ := hc
      simp only [tysMatch] at hnb; obtain ⟨hnb1, hnb2⟩ := NB.app hnb
      simp only [wMatch]
      refine outP_bind (wMRule_complete fuel n0 _ C C' S' st mr' hp hc1 rfl hnb1) ?_
      rintro ⟨τ, amr⟩ st1 ⟨hn1, hi1, hok1, hokA1, T1, hF1, hty1, hs1⟩
      have hp1 := hp.next hi1 hn1 hF1
      refine outP_bind (wMatchOpt_complete fuel n0 _ C C' T1 st1 τ mr'.ty rest' hp1 hok1 hty1 hc2 rfl hnb2) ?_
      rintro ar st2 ⟨hn2, hi2, hokA2, T2, hF2, hs2⟩
      dsimp only at *
      refine outP_pure ⟨by omega, hi2, hok1.mono hn2, (hokA1.mono hn2).app hokA2, T2, hF1.trans hF2 hn1, ?_, ?_⟩
      · simp only [AMatch.ty, hF2.sb_eq hok1, hty1]
      · simp only [sbMatch, stripMatch] at hs2 ⊢
        rw [hs2, sbMRule_congr amr (hF2.agreeOn hokA1), hs1]
theorem wMatchOpt_complete (fuel n0 : Nat) : ∀ (m : Option BMatch) (C C' : Ctx) (S' : FSub) (st : WSt) (τ τ' : Ty)
    (m' : Option AMatch), Pre n0 C C' S' st → OkT st.n τ → sb S' τ = τ' → checkMatchOptAt C' τ' m' = true →
    AMatch.eraseOpt m' = m → NB (tysMatchOpt false m') →
    OutP (MOptPost n0 st S' m') (wMatchOpt fuel (rigidFrom n0) C τ m st)
  | none, C, C', S', st, τ, τ', m', hp, _, _, _, he, _ => by
    cases m' with
    | none => simp only [wMatchOpt]; exact outP_pure ⟨Nat.le_refl _, hp.inv, OkA.nil, S', Found.refl hp, rfl⟩
    | some _ => simp [AMatch.eraseOpt] at he
  | some m, C, C', S', st, τ, τ', m', hp, hok, hτ, hc, he, hnb => by
    cases m' with
    | some m'' =>
      simp only [AMatch.eraseOpt, Option.some.injEq] at he; subst he
      simp only [checkMatchOptAt, Bool.and_eq_true, decide_eq_true_eq] at hc; obtain ⟨hc1, hc2⟩ := hc
      simp only [tysMatchOpt] at hnb
      simp only [wMatchOpt]
      refine outP_bind (wMatch_complete fuel n0 _ C C' S' st m'' hp hc1 rfl hnb) ?_
      rintro ⟨τm, am⟩ st1 ⟨hn1, hi1, hok1, hokA1, T1, hF1, hty1, hs1⟩
      dsimp only at *
      refine outP_unifyW hi1 hok1 (hok.mono hn1) hF1.fix hF1.abs (by rw [hty1, hF1.sb_eq hok, hτ, hc2])
        fun st2 hn2 hi2 hab2 => ?_
      exact outP_pure ⟨by omega, hi2, by rw [hn2]; exact hokA1, T1, hF1.trans ⟨hF1.fix, hab2, fun _ _ => rfl, fun _ h => absurd rfl h⟩ hn1,
        by simp only [sbMatchOpt, stripMatchOpt, hs1]⟩
    | none => simp [AMatch.eraseOpt] at he
theorem wMRule_complete (fuel n0 : Nat) : ∀ (mr : BMRule) (C C' : Ctx) (S' : FSub) (st : WSt) (mr' : AMRule),
    Pre n0 C C' S' st → checkMRule C' mr' = true → mr'.erase = mr → NB (tysMRule false mr') →
    OutP (MRPost n0 st S' mr') (wMRule fuel (rigidFrom n0) C mr st)
  | .mk p e, C, C', S', st, mr', hp, hc, he, hnb => by
    cases mr' with
    | mk p' e' =>
      simp only [AMRule.erase, BMRule.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      simp only [checkMRule, Bool.and_eq_true] at hc; obtain ⟨hc1, hc2⟩ := hc
      simp only [tysMRule] at hnb; obtain ⟨hnb1, hnb2⟩ := NB.app hnb
      simp only [wMRule]
      refine outP_bind (wPat_complete fuel n0 _ C C' C' S' st p' hp (lkC_refl C') hc1 rfl hnb1) ?_
      rintro ⟨τp, ap⟩ st1 ⟨hn1, hi1, hok1, hty1, hokA1, T1, hF1, hs1⟩
      dsimp only at *
      have hve := pat_ve_eq' hs1
      have hpre := pre_pat hp hn1 hi1 hF1 (pat_ve ap) hokA1
      rw [← hve] at hpre
      refine outP_bind (wExp_complete fuel n0 _ _ _ T1 st1 e' hpre hc2 rfl hnb2) ?_
      rintro ⟨τe, ae⟩ st2 ⟨hn2, hi2, hok2, hokA2, T2, hF2, hty2, hs2⟩
      dsimp only at *
      refine outP_pure ⟨by omega, hi2, OkT_fn (hok1.mono hn2) hok2, (hokA1.mono hn2).app hokA2, T2,
        hF1.trans hF2 hn1, ?_, ?_⟩
      · show Ty.fn (sb T2 τp) (sb T2 τe) = Ty.fn p'.ty e'.ty
        rw [hF2.sb_eq hok1, hty2, ← hty1, pat_ty_eq hs1]
      · simp only [sbMRule, stripMRule] at hs2 ⊢
        rw [hs2, sbPat_congr ap (hF2.agreeOn hokA1), hs1]
theorem wDec_complete (fuel n0 : Nat) : ∀ (d : BDec) (C C' : Ctx) (S' : FSub) (st : WSt) (d' : ADec),
    Pre n0 C C' S' st → checkDec C' d' = true → d'.erase = d → NB (tysDec false d') →
    OutP (DPost n0 st S' d') (wDec fuel (rigidFrom n0) C d st)
  | .val (.pat p e), C, C', S', st, d', hp, hc, he, hnb => by
    cases d' with
    | val VE' vb' =>
      cases vb' with
      | pat p' e' =>
        simp only [ADec.erase, AValBind.erase, BDec.val.injEq, BValBind.pat.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        simp only [checkDec, checkValBind, Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨⟨⟨hc1, hc2⟩, hc3⟩, hc4⟩ := hc
        simp only [AValBind.ve] at hc4; subst hc4
        simp only [tysDec, Bool.false_eq_true, ↓reduceIte, List.nil_append, tysValBind] at hnb
        obtain ⟨hnb1, hnb2⟩ := NB.app hnb
        simp only [wDec]
        refine outP_bind (wAtPat_complete fuel n0 _ C C' (C'.plusVE p'.ve) S' st p' hp
          (lkC_plusVE fun q hq => (atpat_ve p' q hq).2.1) hc1 rfl hnb1) ?_
        rintro ⟨τp, ap⟩ st1 ⟨hn1, hi1, hok1, hty1, hokA1, T1, hF1, hs1⟩
        dsimp only at *
        have hve := pat_ve_eq hs1
        have hpre := pre_pat hp hn1 hi1 hF1 (atpat_ve ap) hokA1
        rw [← hve] at hpre
        refine outP_bind (wExp_complete fuel n0 _ _ _ T1 st1 e' hpre hc2 rfl hnb2) ?_
        rintro ⟨τe, ae⟩ st2 ⟨hn2, hi2, hok2, hokA2, T2, hF2, hty2, hs2⟩
        dsimp only at *
        refine outP_unifyW hi2 hok2 (hok1.mono hn2) hF2.fix hF2.abs
          (by rw [hty2, hc3, hF2.sb_eq hok1, ← hty1, atpat_ty_eq hs1]) fun st3 hn3 hi3 hab3 => ?_
        have hokVE : OkA st1.n (veBodies ap.ve) := fun τ hτ => by
          simp only [veBodies, List.mem_map] at hτ
          obtain ⟨q, hq, rfl⟩ := hτ
          exact okT_pent hokA1 (atpat_ve ap q hq)
        refine outP_pure ⟨by omega, hi3, ?_, ?_, T2, (hF1.trans hF2 hn1).trans ⟨hF2.fix, hab3, fun _ _ => rfl, fun _ h => absurd rfl h⟩
          (by omega), ?_, ?_⟩
        · simp only [tysDec, ↓reduceIte, tysValBind]
          rw [hn3]
          exact (hokVE.mono hn2).app ((hokA1.mono hn2).app hokA2)
        · intro q hq
          simp only [ADec.env] at hq
          exact ⟨(atpat_ve ap q hq).1, by rw [hn3]; exact (okT_pent hokA1 (atpat_ve ap q hq)).mono hn2⟩
        · simp only [sbDec, stripDec, sbValBind, stripValBind] at hs2 ⊢
          rw [sbVE_congr (hF2.agreeOn hokVE), sbAtPat_congr ap (hF2.agreeOn hokA1), hs1, hs2, hve]
        · intro q hq
          simp only [ADec.env] at hq
          have hq' : (q.1, (sbScheme T1 q.2.1, q.2.2)) ∈ p'.ve := by
            rw [hve]; simp only [sbVE, List.mem_map]; exact ⟨q, hq, rfl⟩
          have := nb_of_pent hnb1 (atpat_ve p' _ hq')
          simp only [sbScheme] at this
          rw [hF2.sb_eq (okT_pent hokA1 (atpat_ve ap q hq))]; exact this
      | var => simp [ADec.erase, AValBind.erase] at he
  | .val (.var x ann e rest), C, C', S', st, d', hp, hc, he, hnb => by
    cases d' with
    | val VE' vb' =>
      simp only [ADec.erase, BDec.val.injEq] at he
      simp only [checkDec, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hc1, hc2⟩ := hc
      simp only [tysDec, Bool.false_eq_true, ↓reduceIte, List.nil_append] at hnb
      simp only [wDec]
      have hU : (C'.plusVE VE').U = C.U := by simp [Ctx.plusVE, hp.rel.2.1]
      have hT : ∀ lc, (C'.plusVE VE').lookupTy lc = C.lookupTy lc := fun lc => by
        simp [Ctx.plusVE, Ctx.lookupTy, Env.lookupTy, hp.rel.2.2.1, hp.rel.2.2.2.1]
      refine outP_bind (groupEntries_complete hU hT _ st S' vb' hp.inv hp.fix hp.abs (annChk_of_check vb' hc1) he) ?_
      rintro es st1 ⟨hθ1, hn1, hi1, hes, S1, hF1, hrel1⟩
      have hVE' : VE' = sbVE S1 (groupVE (.var x ann e rest) es) := by
        rw [← hc2, groupVE_rel _ es vb' hrel1 he (fun e he => (hes e he).2)]
      have hmono := groupVE_mono (.var x ann e rest) es (fun e he => (hes e he).2)
      have hokVE : OkA st1.n (veBodies (groupVE (.var x ann e rest) es)) := fun τ hτ => by
        simp only [veBodies, List.mem_map] at hτ
        obtain ⟨q, hq, rfl⟩ := hτ
        obtain ⟨-, -, e0, he0, h⟩ := hmono q hq
        rw [h]; exact (hes e0 he0).1
      have hpre : Pre n0 (C.plusVE (groupVE (.var x ann e rest) es)) (C'.plusVE VE') S1 st1 := by
        rw [hVE']
        refine ⟨hi1, (hp.ctxW.mono hn1).plusVE fun q hq => ?_,
          (hp.rel.congr hp.ctxW hF1.agree).plusVE (VEMatch_mono fun q hq => (hmono q hq).1), hF1.fix, hF1.abs⟩
        have : q.2.1 = mono q.2.1.body := by
          have hb := (hmono q hq).1
          revert hb; obtain ⟨_, ⟨b, body⟩, _⟩ := q; intro hb; simp only at hb; subst hb; rfl
        rw [this]
        exact SchW_mono_scheme (hokVE _ (by simp only [veBodies, List.mem_map]; exact ⟨q, hq, rfl⟩))
      refine outP_bind (wMembers_complete fuel n0 _ _ _ S1 st1 es vb' hpre hc1 he hnb hrel1 hes) ?_
      rintro avb st2 ⟨hn2, hi2, hokA2, T2, hF2, hs2⟩
      refine outP_pure ⟨by omega, hi2, (hokVE.mono hn2).app hokA2, ?_, T2, hF1.trans hF2 hn1, ?_, ?_⟩
      · intro q hq
        simp only [ADec.env] at hq
        obtain ⟨hb, -, e0, he0, h⟩ := hmono q hq
        exact ⟨hb, by rw [h]; exact (hes e0 he0).1.mono hn2⟩
      · simp only [sbDec, stripDec] at hs2 ⊢
        rw [hs2, sbVE_congr (hF2.agreeOn hokVE), ← hVE']
      · intro q hq
        simp only [ADec.env] at hq
        obtain ⟨-, -, e0, he0, h⟩ := hmono q hq
        rw [h, hF2.sb_eq (hes e0 he0).1]
        exact hnb _ (esRel_mem es vb' hrel1 e0 he0)
theorem wMembers_complete (fuel n0 : Nat) : ∀ (vb : BValBind) (Cg Cg' : Ctx) (S' : FSub) (st : WSt)
    (es : List (Option (BTy × List BVar) × Ty)) (vb' : AValBind),
    Pre n0 Cg Cg' S' st → checkValBind Cg' vb' = true → vb'.erase = vb → NB (tysValBind false vb') →
    EsRel S' es vb' → (∀ e ∈ es, OkT st.n e.2 ∧ annU e.1 = []) →
    OutP (VBPost n0 st S' vb') (wMembers fuel (rigidFrom n0) Cg vb es st)
  | .pat _ _, Cg, Cg', S', st, es, vb', _, _, _, _, _, _ => by
    simp only [wMembers]; trivial
  | .var x ann e rest, Cg, Cg', S', st, [], vb', _, _, _, _, hrel, _ => by
    simp only [wMembers]; trivial
  | .var x ann e rest, Cg, Cg', S', st, (an, τx) :: es, vb', hp, hc, he, hnb, hrel, hes => by
    cases vb' with
    | var x' ann' τ' e' rest' =>
      simp only [AValBind.erase, BValBind.var.injEq] at he; obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      unfold EsRel at hrel
      obtain ⟨rfl, hτx, hrest⟩ := hrel
      have hann : annU an = [] := (hes _ (.head _)).2
      have hokx : OkT st.n τx := (hes _ (.head _)).1
      simp only [checkValBind, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨-, hc2⟩, hc3⟩, hc4⟩ := hc
      rw [hann, plusU_nil] at hc2
      simp only [tysValBind, List.cons_append, annMark, List.nil_append] at hnb
      obtain ⟨-, hnb⟩ := NB.cons hnb
      obtain ⟨hnb1, hnb2⟩ := NB.app hnb
      simp only [wMembers, hann, plusU_nil]
      refine outP_bind (wExp_complete fuel n0 _ Cg Cg' S' st e' hp hc2 rfl hnb1) ?_
      rintro ⟨τe, ae⟩ st1 ⟨hn1, hi1, hok1, hokA1, T1, hF1, hty1, hs1⟩
      dsimp only at *
      refine outP_unifyW hi1 hok1 (hokx.mono hn1) hF1.fix hF1.abs (by rw [hty1, hc3, hF1.sb_eq hokx, hτx])
        fun st2 hn2 hi2 hab2 => ?_
      have hF1' : Found n0 S' st.n st2 T1 := hF1.trans ⟨hF1.fix, hab2, fun _ _ => rfl, fun _ h => absurd rfl h⟩ hn1
      have hp2 : Pre n0 Cg Cg' T1 st2 := hp.next hi2 (by omega) hF1'
      have hrest' : EsRelOpt T1 es rest' := by
        cases rest' with
        | none => exact hrest
        | some vb => exact EsRel.congr hF1.agree es vb (fun e he => (hes e (.tail _ he)).1) hrest
      refine outP_bind (wMembersOpt_complete fuel n0 _ Cg Cg' T1 st2 es rest' hp2 hc4 rfl hnb2 hrest'
        (fun e he => ⟨((hes e (.tail _ he)).1.mono hn1).mono (by omega), (hes e (.tail _ he)).2⟩)) ?_
      rintro ar st3 ⟨hn3, hi3, hokA3, T3, hF3, hs3⟩
      refine outP_pure ⟨by omega, hi3, ?_, T3, hF1'.trans hF3 (by omega), ?_⟩
      · simp only [tysValBind, List.cons_append, annMark, hann, ↓reduceIte, List.nil_append]
        exact OkA.cons ((hokx.mono hn1).mono (by omega)) (((hokA1.mono (by omega))).app hokA3)
      · simp only [sbValBind, stripValBind] at hs3 ⊢
        rw [hs3, sbExp_congr ae (hF3.agreeOn (hokA1.mono (by omega))), hs1, hF3.sb_eq ((hokx.mono hn1).mono (by omega)),
          hF1.sb_eq hokx, hτx]
    | pat _ _ => simp [AValBind.erase] at he
theorem wMembersOpt_complete (fuel n0 : Nat) : ∀ (vb : Option BValBind) (Cg Cg' : Ctx) (S' : FSub) (st : WSt)
    (es : List (Option (BTy × List BVar) × Ty)) (vb' : Option AValBind),
    Pre n0 Cg Cg' S' st → checkValBindOpt Cg' vb' = true → AValBind.eraseOpt vb' = vb →
    NB (tysValBindOpt false vb') →
    EsRelOpt S' es vb' → (∀ e ∈ es, OkT st.n e.2 ∧ annU e.1 = []) →
    OutP (VBOptPost n0 st S' vb') (wMembersOpt fuel (rigidFrom n0) Cg vb es st)
  | none, Cg, Cg', S', st, es, vb', hp, _, he, _, _, _ => by
    cases vb' with
    | none => simp only [wMembersOpt]; exact outP_pure ⟨Nat.le_refl _, hp.inv, OkA.nil, S', Found.refl hp, rfl⟩
    | some _ => simp [AValBind.eraseOpt] at he
  | some vb, Cg, Cg', S', st, es, vb', hp, hc, he, hnb, hrel, hes => by
    cases vb' with
    | some vb'' =>
      simp only [AValBind.eraseOpt, Option.some.injEq] at he; subst he
      simp only [checkValBindOpt] at hc
      simp only [tysValBindOpt] at hnb
      simp only [wMembersOpt]
      refine outP_bind (wMembers_complete fuel n0 _ Cg Cg' S' st es vb'' hp hc rfl hnb
        (by simpa [EsRelOpt] using hrel) hes) ?_
      rintro avb st1 ⟨hn1, hi1, hokA1, T1, hF1, hs1⟩
      exact outP_pure ⟨hn1, hi1, hokA1, T1, hF1, by simp only [sbValBindOpt, stripValBindOpt, hs1]⟩
    | none => simp [AValBind.eraseOpt] at he
end

end StandardElm.Stat.Complete
