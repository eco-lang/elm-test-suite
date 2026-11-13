/-
  A Standard Definition of Elm? Mechanisation: the main induction L11 of plan step 11 with
  records and rows (milestone (d), section 8; WComplete.lean for `inferExpWD`), for expressions,
  record rows, matches, declarations and groups.

  For every state satisfying the invariant, every `S'` fixing the rigid variables, respecting
  classes and absorbing W's substitution, and every derivation `a'` (without `bnd` variables,
  with canonical types: `NBD`) of the phrase in a context no more general than `S'` applied to
  W's (`PreD`): W does not fail, and if it returns `(τ, a)` then an extension `T` of `S'` to the
  variables W created fixes the rigid variables, absorbs W's new substitution, and maps `τ` to
  the derivation's type and `a` to `a'` with the instance lists left out. The record cases: a
  record expression's row is its fields' (`wExpRow_completeD`); an update `{ x | row }`
  instantiates `x`'s scheme and unifies it with `⟨row | ε⟩`, `ε` fresh, which `T` maps to the
  fields of the derivation's record type the update does not mention (`mrg_onlyL_eq`).
-/
import StandardElmMech.Stat.Complete.WDCompleteAux
import StandardElmMech.Stat.Complete.WComplete

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BAtPat BPat BAtExp BExpRow BExp BMatch BMRule BDec BValBind)

/-! ## Conclusions -/

def AEPostD (n0 : Nat) (st : WDSt) (S' : RSub) (a' : AAtExp) (r : Ty × AAtExp) (st' : WDSt) : Prop :=
  st.n ≤ st'.n ∧ SInvD n0 st' ∧ OkTD st'.n r.1 ∧ OkAD st'.n (tysAtExp true r.2) ∧
    ∃ T, FoundD n0 S' st.n st' T ∧ rsb T r.1 = a'.ty ∧ stripAtExp (rsbAtExp T r.2) = stripAtExp a'

def EPostD (n0 : Nat) (st : WDSt) (S' : RSub) (a' : AExp) (r : Ty × AExp) (st' : WDSt) : Prop :=
  st.n ≤ st'.n ∧ SInvD n0 st' ∧ OkTD st'.n r.1 ∧ OkAD st'.n (tysExp true r.2) ∧
    ∃ T, FoundD n0 S' st.n st' T ∧ rsb T r.1 = a'.ty ∧ stripExp (rsbExp T r.2) = stripExp a'

def EOptPostD (n0 : Nat) (st : WDSt) (S' : RSub) (a' : Option AExp) (r : Option Ty × Option AExp) (st' : WDSt) : Prop :=
  st.n ≤ st'.n ∧ SInvD n0 st' ∧ (∀ τ, r.1 = some τ → OkTD st'.n τ) ∧ OkAD st'.n (tysExpOpt true r.2) ∧
    ∃ T, FoundD n0 S' st.n st' T ∧ rsbOpt T r.1 = AExp.tyOpt a' ∧ stripExpOpt (rsbExpOpt T r.2) = stripExpOpt a'

def ERPostD (n0 : Nat) (st : WDSt) (S' : RSub) (r' : AExpRow) (r : Row × AExpRow) (st' : WDSt) : Prop :=
  st.n ≤ st'.n ∧ SInvD n0 st' ∧ (∀ p ∈ r.1, OkTD st'.n p.2) ∧ OkAD st'.n (tysExpRow true r.2) ∧
    ∃ T, FoundD n0 S' st.n st' T ∧ rsbRow T r.1 = r'.row ∧ stripExpRow (rsbExpRow T r.2) = stripExpRow r'

def EROptPostD (n0 : Nat) (st : WDSt) (S' : RSub) (r' : Option AExpRow) (r : Row × Option AExpRow) (st' : WDSt) : Prop :=
  st.n ≤ st'.n ∧ SInvD n0 st' ∧ (∀ p ∈ r.1, OkTD st'.n p.2) ∧ OkAD st'.n (tysExpRowOpt true r.2) ∧
    ∃ T, FoundD n0 S' st.n st' T ∧ rsbRow T r.1 = AExpRow.rowOpt r' ∧
      stripExpRowOpt (rsbExpRowOpt T r.2) = stripExpRowOpt r'

def MPostD (n0 : Nat) (st : WDSt) (S' : RSub) (m' : AMatch) (r : Ty × AMatch) (st' : WDSt) : Prop :=
  st.n ≤ st'.n ∧ SInvD n0 st' ∧ OkTD st'.n r.1 ∧ OkAD st'.n (tysMatch true r.2) ∧
    ∃ T, FoundD n0 S' st.n st' T ∧ rsb T r.1 = m'.ty ∧ stripMatch (rsbMatch T r.2) = stripMatch m'

def MOptPostD (n0 : Nat) (st : WDSt) (S' : RSub) (m' : Option AMatch) (r : Option AMatch) (st' : WDSt) : Prop :=
  st.n ≤ st'.n ∧ SInvD n0 st' ∧ OkAD st'.n (tysMatchOpt true r) ∧
    ∃ T, FoundD n0 S' st.n st' T ∧ stripMatchOpt (rsbMatchOpt T r) = stripMatchOpt m'

def MRPostD (n0 : Nat) (st : WDSt) (S' : RSub) (mr' : AMRule) (r : Ty × AMRule) (st' : WDSt) : Prop :=
  st.n ≤ st'.n ∧ SInvD n0 st' ∧ OkTD st'.n r.1 ∧ OkAD st'.n (tysMRule true r.2) ∧
    ∃ T, FoundD n0 S' st.n st' T ∧ rsb T r.1 = mr'.ty ∧ stripMRule (rsbMRule T r.2) = stripMRule mr'

def DPostD (n0 : Nat) (st : WDSt) (S' : RSub) (d' : ADec) (ad : ADec) (st' : WDSt) : Prop :=
  st.n ≤ st'.n ∧ SInvD n0 st' ∧ OkAD st'.n (tysDec true ad) ∧
    (∀ q ∈ ad.env, q.2.1.bound = [] ∧ OkTD st'.n q.2.1.body) ∧
    ∃ T, FoundD n0 S' st.n st' T ∧ stripDec (rsbDec T ad) = stripDec d' ∧ ∀ q ∈ ad.env, NBτ (rsb T q.2.1.body)

def VBPostD (n0 : Nat) (st : WDSt) (S' : RSub) (vb' : AValBind) (r : AValBind) (st' : WDSt) : Prop :=
  st.n ≤ st'.n ∧ SInvD n0 st' ∧ OkAD st'.n (tysValBind true r) ∧
    ∃ T, FoundD n0 S' st.n st' T ∧ stripValBind (rsbValBind T r) = stripValBind vb'

def VBOptPostD (n0 : Nat) (st : WDSt) (S' : RSub) (vb' : Option AValBind) (r : Option AValBind) (st' : WDSt) : Prop :=
  st.n ≤ st'.n ∧ SInvD n0 st' ∧ OkAD st'.n (tysValBindOpt true r) ∧
    ∃ T, FoundD n0 S' st.n st' T ∧ stripValBindOpt (rsbValBindOpt T r) = stripValBindOpt vb'

/-! ## Helpers -/

/-- An instance of an integer constant's scheme is a number type. -/
theorem pent_schWD {n : Nat} {l : List Ty} (hl : OkAD n l) {q : String × (Scheme × IdStatus)} (h : PEnt l q) :
    SchWD n q.2.1 := by
  have : q.2.1 = mono q.2.1.body := by obtain ⟨_, σ, _⟩ := q; cases σ; simp_all [PEnt, mono]
  rw [this]
  refine SchW_mono_schemeD fun v hv => ?_
  obtain ⟨τ, h1, h2⟩ := h.2.2 v hv
  exact hl τ h1 v h2

theorem nb_of_pentD {l : List Ty} (hl : NBD l) {q : String × (Scheme × IdStatus)} (h : PEnt l q) : NBτ q.2.1.body :=
  fun v hv => by obtain ⟨τ, h1, h2⟩ := h.2.2 v hv; exact (hl τ h1).1 v h2

theorem okT_pentD {n : Nat} {l : List Ty} (hl : OkAD n l) {q : String × (Scheme × IdStatus)} (h : PEnt l q) :
    OkTD n q.2.1.body := fun v hv => by obtain ⟨τ, h1, h2⟩ := h.2.2 v hv; exact hl τ h1 v h2

/-- The environment of a pattern under `T` is the derivation's. -/
theorem pat_ve_eqD {T : RSub} {ap p' : AAtPat} (h : stripAtPat (rsbAtPat T ap) = stripAtPat p') :
    p'.ve = rsbVE T ap.ve := by
  rw [← stripAtPat_ve p', ← h, stripAtPat_ve, rsbAtPat_veD]

theorem pat_ve_eq'D {T : RSub} {ap p' : APat} (h : stripPat (rsbPat T ap) = stripPat p') :
    p'.ve = rsbVE T ap.ve := by
  rw [← stripPat_ve p', ← h, stripPat_ve, rsbPat_veD]

theorem atpat_ty_eqD {T : RSub} {ap p' : AAtPat} (h : stripAtPat (rsbAtPat T ap) = stripAtPat p') :
    rsb T ap.ty = p'.ty := by
  rw [← rsbAtPat_tyD, ← stripAtPat_ty, h, stripAtPat_ty]

theorem pat_ty_eqD {T : RSub} {ap p' : APat} (h : stripPat (rsbPat T ap) = stripPat p') :
    rsb T ap.ty = p'.ty := by
  rw [← rsbPat_tyD, ← stripPat_ty, h, stripPat_ty]

/-- The body of an abstraction or a rule: W's context with the pattern's environment, against
    the derivation's. -/
theorem pre_patD {n0 : Nat} {C C' : Ctx} {S' T : RSub} {st st1 : WDSt} {VE : ValEnv} {l : List Ty}
    (hp : PreD n0 C C' S' st) (hn : st.n ≤ st1.n) (hi1 : SInvD n0 st1) (hF : FoundD n0 S' st.n st1 T)
    (hVE : ∀ q ∈ VE, PEnt l q) (hl : OkAD st1.n l) :
    PreD n0 (C.plusVE VE) (C'.plusVE (rsbVE T VE)) T st1 :=
  ⟨hi1, (hp.ctxW.mono hn).plusVE fun q hq => pent_schWD hl (hVE q hq),
    (hp.rel.congr hp.ctxW hF.agree).plusVE (VEMatch_monoD fun q hq => (hVE q hq).1), hF.fix, hF.abs,
    hF.resp hp.resp⟩

theorem esRel_memD {S : RSub} : ∀ (es : List (Option (BTy × List BVar) × Ty)) (vb' : AValBind),
    EsRelD S es vb' → ∀ e ∈ es, rsb S e.2 ∈ tysValBind false vb'
  | (ann, τ) :: es, .var _ ann' τ' _ rest, h, e, he => by
    unfold EsRelD at h
    obtain ⟨-, h2, h3⟩ := h
    rcases List.mem_cons.mp he with rfl | he
    · simp [tysValBind, h2, annMark]
    · cases rest with
      | none => simp only at h3; subst h3; cases he
      | some vb =>
        have := esRel_memD es vb h3 e he
        simp [tysValBind, tysValBindOpt, this, annMark]
  | [], _, h, _, he => by cases he
  | _ :: _, .pat _ _, h, _, _ => by simp [EsRelD] at h

def EsRelOptD (S : RSub) (es : List (Option (BTy × List BVar) × Ty)) : Option AValBind → Prop
  | none => es = []
  | some vb => EsRelD S es vb

theorem okT_closedD {n : Nat} {τ : Ty} (h : τ.vars = []) : OkTD n τ := OkT_of_vars_nilD h

theorem rsb_closedD {s : RSub} {τ : Ty} (h : τ.vars = []) : rsb s τ = τ :=
  rsb_eq_self fun w hw => by rw [h] at hw; cases hw

/-! ## The main induction -/

mutual
theorem wAtExp_completeD (fuel n0 : Nat) : ∀ (a : BAtExp) (C C' : Ctx) (S' : RSub) (st : WDSt) (a' : AAtExp),
    PreD n0 C C' S' st → checkAtExp C' a' = true → a'.erase = a → NBD (tysAtExp false a') →
    OutPD (AEPostD n0 st S' a') (wdAtExp fuel (rigidFromD n0) C a st)
  | .scon sc, C, C', S', st, a', hp, hc, he, _ => by
    cases a' with
    | scon sc' τ' =>
      simp only [AAtExp.erase, BAtExp.scon.injEq] at he; subst he
      simp only [checkAtExp] at hc
      have hpost : ∀ τ0 : Ty, τ0.vars = [] → τ' = τ0 →
          OutPD (AEPostD n0 st S' (.scon sc' τ')) ((pure (τ0, AAtExp.scon sc' τ0) : WDM (Ty × AAtExp)) st) := fun τ0 hv e =>
        outP_pureD ⟨Nat.le_refl _, hp.inv, okT_closedD hv, OkAD.cons (okT_closedD hv) OkAD.nil, S', FoundD.refl hp,
          by simp [rsb_closedD hv, e, AAtExp.ty], by simp [rsbAtExp, stripAtExp, rsb_closedD hv, e]⟩
      cases sc' with
      | int k =>
        simp only [wdAtExp]
        have hnum : Adm .num τ' := adm_int_gen (gen_of_genAt hc)
        refine outP_freshCD (outP_pureD ⟨Nat.le_succ _, hp.inv.fresh, okT_freshCD, OkAD.cons okT_freshCD OkAD.nil,
          ext1CD S' st.n .num τ', found_ext1CD hp hnum, ?_, ?_⟩)
        · simp [rsb, ext1C_selfD, AAtExp.ty]
        · simp [rsbAtExp, stripAtExp, rsb, ext1C_selfD]
      | float m e => simp only [wdAtExp]; exact hpost _ rfl (genAt_monoW hc)
      | char c => simp only [wdAtExp]; exact hpost _ rfl (genAt_monoW hc)
      | str s => simp only [wdAtExp]; exact hpost _ rfl (genAt_monoW hc)
    | _ => simp [AAtExp.erase] at he
  | .var lv, C, C', S', st, a', hp, hc, he, _ => by
    cases a' with
    | var lv' inst τ' =>
      simp only [AAtExp.erase, BAtExp.var.injEq] at he; subst he
      simp only [checkAtExp] at hc
      split at hc
      · rename_i σ' s' hlk
        obtain ⟨σ, hσ, hrel⟩ := hp.rel.lookup hp.fix (rigid_bndD n0) hlk
        simp only [wdAtExp, hσ]
        refine outP_instantiateD hp.inv (hp.ctxW _ _ _ hσ) hp.fix hp.abs
          (hrel.2 _ (gen_of_genAt hc)) ?_
        intro ts τ st1 T hle _ hi1 hok _ hfx hab hag hcl hτ
        exact outP_pureD ⟨hle, hi1, hok, OkAD.cons hok OkAD.nil, T, ⟨hfx, hab, hag, hcl⟩, hτ, by
          simp [rsbAtExp, stripAtExp, hτ]⟩
      · cases hc
    | _ => simp [AAtExp.erase] at he
  | .con lc, C, C', S', st, a', hp, hc, he, _ => by
    cases a' with
    | con lc' inst τ' =>
      simp only [AAtExp.erase, BAtExp.con.injEq] at he; subst he
      simp only [checkAtExp] at hc
      split at hc
      · rename_i σ' s' hlk
        obtain ⟨σ, hσ, hrel⟩ := hp.rel.lookup hp.fix (rigid_bndD n0) hlk
        simp only [wdAtExp, hσ]
        refine outP_instantiateD hp.inv (hp.ctxW _ _ _ hσ) hp.fix hp.abs
          (hrel.2 _ (gen_of_genAt hc)) ?_
        intro ts τ st1 T hle _ hi1 hok _ hfx hab hag hcl hτ
        exact outP_pureD ⟨hle, hi1, hok, OkAD.cons hok OkAD.nil, T, ⟨hfx, hab, hag, hcl⟩, hτ, by
          simp [rsbAtExp, stripAtExp, hτ]⟩
      · cases hc
    | _ => simp [AAtExp.erase] at he
  | .op o, C, C', S', st, a', hp, hc, he, _ => by
    cases a' with
    | op o' inst τ' =>
      simp only [AAtExp.erase, BAtExp.op.injEq] at he; subst he
      simp only [checkAtExp] at hc
      split at hc
      · rename_i σ s' hlk
        simp only [wdAtExp, hlk]
        refine outP_instantiateD hp.inv (otstat_schWD hlk _) hp.fix hp.abs
          ((otstat_relD hlk S').2 _ (gen_of_genAt hc)) ?_
        intro ts τ st1 T hle _ hi1 hok _ hfx hab hag hcl hτ
        exact outP_pureD ⟨hle, hi1, hok, OkAD.cons hok OkAD.nil, T, ⟨hfx, hab, hag, hcl⟩, hτ, by
          simp [rsbAtExp, stripAtExp, hτ]⟩
      · cases hc
    | _ => simp [AAtExp.erase] at he
  | .unit, C, C', S', st, a', hp, _, he, _ => by
    cases a' with
    | unit =>
      simp only [wdAtExp]
      exact outP_pureD ⟨Nat.le_refl _, hp.inv, okT_closedD rfl, OkAD.nil, S', FoundD.refl hp, rfl, rfl⟩
    | _ => simp [AAtExp.erase] at he
  | .nil, C, C', S', st, a', hp, hc, he, _ => by
    cases a' with
    | nil τ' =>
      simp only [checkAtExp] at hc
      obtain ⟨t, rfl⟩ := isListTy_spec hc
      simp only [wdAtExp]
      refine outP_freshVD (outP_pureD ⟨Nat.le_succ _, hp.inv.fresh, OkT_listD okT_freshD,
        OkAD.cons (OkT_listD okT_freshD) OkAD.nil, ext1D S' st.n t, found_ext1D hp t, ?_, ?_⟩)
      · simp [AAtExp.ty, listTy_sbD, rsb, ext1C_selfD]
      · simp [rsbAtExp, stripAtExp, listTy_sbD, rsb, ext1C_selfD]
    | _ => simp [AAtExp.erase] at he
  | .record row, C, C', S', st, a', hp, hc, he, hnb => by
    cases a' with
    | record row' =>
      simp only [AAtExp.erase, BAtExp.record.injEq] at he; subst he
      simp only [checkAtExp] at hc
      simp only [tysAtExp] at hnb
      simp only [wdAtExp]
      refine outP_bindD (wExpRowOpt_completeD fuel n0 _ C C' S' st row' hp hc rfl hnb) ?_
      rintro ⟨ρ, ar⟩ st1 ⟨hn1, hi1, hokρ, hokA1, T1, hF1, hρ, hs1⟩
      refine outP_pureD ⟨hn1, hi1, OkT_recordD hokρ (fun v hv => by simp [tailVars] at hv), hokA1, T1, hF1, ?_,
        by simp only [rsbAtExp, stripAtExp, hs1]⟩
      simp only at hρ ⊢
      rw [rsb_record]; simp only [RSub.rx, RSub.tl, mrg_nil_right, hρ, AAtExp.ty]
    | _ => simp [AAtExp.erase] at he
  | .update x row, C, C', S', st, a', hp, hc, he, hnb => by
    cases a' with
    | update x' inst τ' row' =>
      simp only [AAtExp.erase, BAtExp.update.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      simp only [checkAtExp, Bool.and_eq_true] at hc
      obtain ⟨⟨⟨hc1, hrec⟩, hc2⟩, hsub⟩ := hc
      split at hc1
      · rename_i σ' s' hlk
        obtain ⟨σ, hσ, hrel⟩ := hp.rel.lookup hp.fix (rigid_bndD n0) hlk
        obtain ⟨ρ', tl', rfl⟩ := isRecordTy_spec hrec
        simp only [recordRow, Row.subB_iff] at hsub
        simp only [tysAtExp] at hnb
        obtain ⟨hnbτ, hnbr⟩ := NBD.cons hnb
        have hcnτ : CnRow ρ' := cnB_record.mp (hnbτ.cn _ (.head _))
        have hcnr : CnRow row'.row := cn_exprow_row row' hnbr.cn
        simp only [wdAtExp, hσ]
        refine outP_instantiateD hp.inv (hp.ctxW _ _ _ hσ) hp.fix hp.abs (hrel.2 _ (gen_of_genAt hc1)) ?_
        intro ts τ st1 T hle _ hi1 hok _ hfx hab hag hcl hτ
        have hF1 : FoundD n0 S' st.n st1 T := ⟨hfx, hab, hag, hcl⟩
        have hp1 := hp.next hi1 hle hF1
        refine outP_bindD (wExpRow_completeD fuel n0 _ C C' T st1 row' hp1 hc2 rfl hnbr) ?_
        rintro ⟨ρ, ar⟩ st2 ⟨hn2, hi2, hokρ, hokA2, T2, hF2, hρ, hs2⟩
        dsimp only at hρ hs2 hokρ hokA2
        refine outP_freshRowD ?_
        have hF3 := found_extR hi2 hF2.fix hF2.abs (onlyL ρ' row'.row, tl')
        have hF123 := (hF1.trans hF2 hle).trans hF3 (by omega)
        have hokρ' : OkTD (st2.n + 1) (.record ρ (some (.fresh st2.n))) := by
          refine OkT_recordD (fun p hp' => (hokρ p hp').mono (Nat.le_succ _)) ?_
          intro v hv
          simp only [tailVars, List.mem_singleton] at hv; subst hv
          exact ⟨rfl, by simp [newB]⟩
        have e1 : rsb (extR T2 (.fresh st2.n) (onlyL ρ' row'.row, tl')) τ = .record ρ' tl' := by
          rw [hF3.sb_eq (hok.mono hn2), hF2.sb_eq hok, hτ]
        have e2 : rsbRow (extR T2 (.fresh st2.n) (onlyL ρ' row'.row, tl')) ρ = row'.row := by
          have : rsbRow (extR T2 (.fresh st2.n) (onlyL ρ' row'.row, tl')) ρ = rsbRow T2 ρ := by
            rw [rsbRow_eq, rsbRow_eq]
            exact List.map_congr_left fun p hp' => by rw [hF3.sb_eq (hokρ p hp')]
          rw [this, hρ]
        refine outP_unifyWD hi2.fresh ((hok.mono hn2).mono (Nat.le_succ _)) hokρ' hF3.fix (hF123.resp hp.resp) hF3.abs
          (by rw [e1, rsb_record_extR, e2, mrg_onlyL_eq hcnr.1 hcnτ.1 hsub]) (by rw [e1]; exact hnbτ.cn _ (.head _))
          fun st4 T4 hn4 hi4 ag4 fx4 r4 hab4 => ?_
        dsimp only at hn4 ag4
        have hF4 : FoundD n0 (extR T2 (.fresh st2.n) (onlyL ρ' row'.row, tl')) (st2.n + 1) st4 T4 :=
          FoundD.ofUnify fx4 hab4 ag4 r4
        refine outP_pureD ⟨by omega, hi4, ((hok.mono hn2).mono (Nat.le_succ _)).mono hn4,
          OkAD.cons (((hok.mono hn2).mono (Nat.le_succ _)).mono hn4) ((hokA2.mono (Nat.le_succ _)).mono hn4), T4,
          hF123.trans hF4 (by omega), ?_, ?_⟩
        · rw [hF4.sb_eq ((hok.mono hn2).mono (Nat.le_succ _)), e1]; rfl
        · simp only [rsbAtExp, stripAtExp]
          rw [hF4.sb_eq ((hok.mono hn2).mono (Nat.le_succ _)), e1,
            rsbExpRow_congrD ar (hF4.agreeOn (hokA2.mono (Nat.le_succ _))),
            rsbExpRow_congrD ar (hF3.agreeOn hokA2), hs2]
      · cases hc1
    | _ => simp [AAtExp.erase] at he
  | .tuple e1 e2 e3, C, C', S', st, a', hp, hc, he, hnb => by
    cases a' with
    | tuple q1 q2 q3 =>
      simp only [AAtExp.erase, BAtExp.tuple.injEq] at he; obtain ⟨rfl, rfl, rfl⟩ := he
      simp only [checkAtExp, Bool.and_eq_true] at hc; obtain ⟨⟨hc1, hc2⟩, hc3⟩ := hc
      simp only [tysAtExp] at hnb; obtain ⟨hnb12, hnb3⟩ := NBD.app hnb; obtain ⟨hnb1, hnb2⟩ := NBD.app hnb12
      simp only [wdAtExp]
      refine outP_bindD (wExp_completeD fuel n0 _ C C' S' st q1 hp hc1 rfl hnb1) ?_
      rintro ⟨τ1, a1⟩ st1 ⟨hn1, hi1, hok1, hokA1, T1, hF1, hty1, hs1⟩
      have hp1 := hp.next hi1 hn1 hF1
      refine outP_bindD (wExp_completeD fuel n0 _ C C' T1 st1 q2 hp1 hc2 rfl hnb2) ?_
      rintro ⟨τ2, a2⟩ st2 ⟨hn2, hi2, hok2, hokA2, T2, hF2, hty2, hs2⟩
      have hp2 := hp1.next hi2 hn2 hF2
      refine outP_bindD (wExpOpt_completeD fuel n0 _ C C' T2 st2 q3 hp2 hc3 rfl hnb3) ?_
      rintro ⟨τ3, a3⟩ st3 ⟨hn3, hi3, hok3, hokA3, T3, hF3, hty3, hs3⟩
      dsimp only at *
      refine outP_pureD ⟨by omega, hi3, OkT_tupleD (hok1.mono (by omega)) (hok2.mono hn3) hok3,
        ((hokA1.mono (by omega)).app (hokA2.mono hn3)).app hokA3, T3,
        (hF1.trans hF2 hn1).trans hF3 (by omega), ?_, ?_⟩
      · simp only [tupleTy_sbD, AAtExp.ty, hty3]
        rw [hF3.sb_eq hok2, hty2, (hF2.trans hF3 hn2).sb_eq hok1, hty1]
      · simp only [rsbAtExp, stripAtExp] at hs1 hs2 hs3 ⊢
        rw [hs3, rsbExp_congrD a2 (hF3.agreeOn hokA2), hs2,
          rsbExp_congrD a1 ((hF2.trans hF3 hn2).agreeOn hokA1), hs1]
    | _ => simp [AAtExp.erase] at he
  | .letE d e, C, C', S', st, a', hp, hc, he, hnb => by
    cases a' with
    | letE d' e' =>
      simp only [AAtExp.erase, BAtExp.letE.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      simp only [checkAtExp, Bool.and_eq_true] at hc; obtain ⟨hc1, hc2⟩ := hc
      simp only [tysAtExp] at hnb; obtain ⟨hnb1, hnb2⟩ := NBD.app hnb
      simp only [wdAtExp]
      refine outP_bindD (wDec_completeD fuel n0 _ C C' S' st d' hp hc1 rfl hnb1) ?_
      rintro ad st1 ⟨hn1, hi1, hokA1, henv, T1, hF1, hs1, hnbe⟩
      refine outP_getθD ?_
      cases ad with
      | val VE0 avb =>
        cases d' with
        | val VE' vb' =>
          simp only [rsbDec, stripDec, ADec.val.injEq] at hs1
          simp only [ADec.result] at hc2
          simp only [ADec.env] at henv hnbe
          have hpre := let_preD hp hn1 hi1 hF1 (fun q hq => ⟨(henv q hq).1, (henv q hq).2, hnbe q hq⟩) hs1.1.symm
          refine outP_bindD (wExp_completeD fuel n0 _ _ _ T1 st1 e' hpre hc2 rfl hnb2) ?_
          rintro ⟨τ, ae⟩ st2 ⟨hn2, hi2, hok2, hokA2, T2, hF2, hty2, hs2⟩
          refine outP_pureD ⟨by omega, hi2, hok2, (hokA1.mono hn2).app hokA2, T2, hF1.trans hF2 hn1, hty2, ?_⟩
          simp only [rsbAtExp, stripAtExp] at hs2 ⊢
          rw [hs2, rsbDec_congrD _ (hF2.agreeOn hokA1)]
          simp only [rsbDec, stripDec, hs1.1, hs1.2]
    | _ => simp [AAtExp.erase] at he
  | .paren e, C, C', S', st, a', hp, hc, he, hnb => by
    cases a' with
    | paren e' =>
      simp only [AAtExp.erase, BAtExp.paren.injEq] at he; subst he
      simp only [checkAtExp] at hc
      simp only [tysAtExp] at hnb
      simp only [wdAtExp]
      refine outP_bindD (wExp_completeD fuel n0 _ C C' S' st e' hp hc rfl hnb) ?_
      rintro ⟨τ, ae⟩ st1 ⟨hn1, hi1, hok1, hokA1, T1, hF1, hty1, hs1⟩
      exact outP_pureD ⟨hn1, hi1, hok1, hokA1, T1, hF1, hty1, by simp only [rsbAtExp, stripAtExp, hs1]⟩
    | _ => simp [AAtExp.erase] at he
theorem wExpRow_completeD (fuel n0 : Nat) : ∀ (r : BExpRow) (C C' : Ctx) (S' : RSub) (st : WDSt) (r' : AExpRow),
    PreD n0 C C' S' st → checkExpRow C' r' = true → r'.erase = r → NBD (tysExpRow false r') →
    OutPD (ERPostD n0 st S' r') (wdExpRow fuel (rigidFromD n0) C r st)
  | .field l e rest, C, C', S', st, r', hp, hc, he, hnb => by
    cases r' with
    | field l' e' rest' =>
      simp only [AExpRow.erase, BExpRow.field.injEq] at he; obtain ⟨rfl, rfl, rfl⟩ := he
      simp only [checkExpRow, Bool.and_eq_true] at hc; obtain ⟨hc1, hc2⟩ := hc
      simp only [tysExpRow] at hnb; obtain ⟨hnb1, hnb2⟩ := NBD.app hnb
      simp only [wdExpRow]
      refine outP_bindD (wExp_completeD fuel n0 _ C C' S' st e' hp hc1 rfl hnb1) ?_
      rintro ⟨τ, ae⟩ st1 ⟨hn1, hi1, hok1, hokA1, T1, hF1, hty1, hs1⟩
      refine outP_bindD (wExpRowOpt_completeD fuel n0 _ C C' T1 st1 rest' (hp.next hi1 hn1 hF1) hc2 rfl hnb2) ?_
      rintro ⟨ρ, ar⟩ st2 ⟨hn2, hi2, hokρ, hokA2, T2, hF2, hρ, hs2⟩
      dsimp only at *
      refine outP_pureD ⟨by omega, hi2, ?_, (hokA1.mono hn2).app hokA2, T2, hF1.trans hF2 hn1, ?_, ?_⟩
      · intro p hp'
        rcases mem_modify1 hp' with rfl | hp'
        · exact hok1.mono hn2
        · exact hokρ p hp'
      · simp only [AExpRow.row]
        rw [rsbRow_modifyD, hρ]
        simp only [rsbRow, hF2.sb_eq hok1, hty1]
      · simp only [rsbExpRow, stripExpRow] at hs1 hs2 ⊢
        rw [hs2, rsbExp_congrD ae (hF2.agreeOn hokA1), hs1]
theorem wExpRowOpt_completeD (fuel n0 : Nat) : ∀ (r : Option BExpRow) (C C' : Ctx) (S' : RSub) (st : WDSt)
    (r' : Option AExpRow), PreD n0 C C' S' st → checkExpRowOpt C' r' = true → AExpRow.eraseOpt r' = r →
    NBD (tysExpRowOpt false r') → OutPD (EROptPostD n0 st S' r') (wdExpRowOpt fuel (rigidFromD n0) C r st)
  | none, C, C', S', st, r', hp, _, he, _ => by
    cases r' with
    | none =>
      simp only [wdExpRowOpt]
      exact outP_pureD ⟨Nat.le_refl _, hp.inv, (fun _ h => by cases h), OkAD.nil, S', FoundD.refl hp, rfl, rfl⟩
    | some _ => simp [AExpRow.eraseOpt] at he
  | some r, C, C', S', st, r', hp, hc, he, hnb => by
    cases r' with
    | some r'' =>
      simp only [AExpRow.eraseOpt, Option.some.injEq] at he; subst he
      simp only [checkExpRowOpt] at hc
      simp only [tysExpRowOpt] at hnb
      simp only [wdExpRowOpt]
      refine outP_bindD (wExpRow_completeD fuel n0 _ C C' S' st r'' hp hc rfl hnb) ?_
      rintro ⟨ρ, ar⟩ st1 ⟨hn1, hi1, hokρ, hokA1, T1, hF1, hρ, hs1⟩
      exact outP_pureD ⟨hn1, hi1, hokρ, hokA1, T1, hF1, hρ, by simp only [rsbExpRowOpt, stripExpRowOpt, hs1]⟩
    | none => simp [AExpRow.eraseOpt] at he
theorem wExp_completeD (fuel n0 : Nat) : ∀ (e : BExp) (C C' : Ctx) (S' : RSub) (st : WDSt) (a' : AExp),
    PreD n0 C C' S' st → checkExpS C' a' = true → a'.erase = e → NBD (tysExp false a') →
    OutPD (EPostD n0 st S' a') (wdExp fuel (rigidFromD n0) C e st)
  | .atexp a, C, C', S', st, a', hp, hc, he, hnb => by
    cases a' with
    | atexp a'' =>
      simp only [AExp.erase, BExp.atexp.injEq] at he; subst he
      simp only [checkExpS] at hc
      simp only [tysExp] at hnb
      simp only [wdExp]
      refine outP_bindD (wAtExp_completeD fuel n0 _ C C' S' st a'' hp hc rfl hnb) ?_
      rintro ⟨τ, aa⟩ st1 ⟨hn1, hi1, hok1, hokA1, T1, hF1, hty1, hs1⟩
      exact outP_pureD ⟨hn1, hi1, hok1, hokA1, T1, hF1, hty1, by simp only [rsbExp, stripExp, hs1]⟩
    | _ => simp [AExp.erase] at he
  | .app e a, C, C', S', st, a', hp, hc, he, hnb => by
    cases a' with
    | app e' a'' =>
      simp only [AExp.erase, BExp.app.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      simp only [checkExpS, Bool.and_eq_true] at hc; obtain ⟨⟨hc1, hc2⟩, hc3⟩ := hc
      obtain ⟨r, hr⟩ := fn_of_match hc3
      simp only [tysExp] at hnb; obtain ⟨hnb1, hnb2⟩ := NBD.app hnb
      simp only [wdExp]
      refine outP_bindD (wExp_completeD fuel n0 _ C C' S' st e' hp hc1 rfl hnb1) ?_
      rintro ⟨τ1, ae⟩ st1 ⟨hn1, hi1, hok1, hokA1, T1, hF1, hty1, hs1⟩
      have hp1 := hp.next hi1 hn1 hF1
      refine outP_bindD (wAtExp_completeD fuel n0 _ C C' T1 st1 a'' hp1 hc2 rfl hnb2) ?_
      rintro ⟨τ2, aa⟩ st2 ⟨hn2, hi2, hok2, hokA2, T2, hF2, hty2, hs2⟩
      have hp2 := hp1.next hi2 hn2 hF2
      dsimp only at *
      refine outP_freshVD ?_
      have hF3 := found_ext1D hp2 r
      have hF123 := (hF1.trans hF2 hn1).trans hF3 (by omega)
      refine outP_unifyWD hi2.fresh ((hok1.mono hn2).mono (Nat.le_succ _))
        (OkT_fnD (hok2.mono (Nat.le_succ _)) okT_freshD) hF3.fix (hF123.resp hp.resp) hF3.abs ?_
        (by rw [hF3.sb_eq (hok1.mono hn2), hF2.sb_eq hok1, hty1]; exact cn_exp_ty e' hnb1.cn)
        fun st4 T4 hn4 hi4 ag4 fx4 r4 hab4 => ?_
      · rw [hF3.sb_eq (hok1.mono hn2), hF2.sb_eq hok1, hty1, hr]
        simp only [rsb, ext1C_selfD, hF3.sb_eq hok2, hty2]
      · dsimp only at hn4 ag4
        have hF4 : FoundD n0 (ext1D T2 st2.n r) (st2.n + 1) st4 T4 := FoundD.ofUnify fx4 hab4 ag4 r4
        refine outP_pureD ⟨by omega, hi4, okT_freshD.mono hn4,
          (((hokA1.mono hn2).app hokA2).mono (Nat.le_succ _)).mono hn4, T4,
          hF123.trans hF4 (by omega), ?_, ?_⟩
        · rw [hF4.sb_eq okT_freshD]; simp [rsb, ext1C_selfD, AExp.ty, hr, Ty.cod]
        · simp only [rsbExp, stripExp] at hs1 hs2 ⊢
          rw [rsbAtExp_congrD aa (hF4.agreeOn (hokA2.mono (Nat.le_succ _))),
            rsbExp_congrD ae (hF4.agreeOn ((hokA1.mono hn2).mono (Nat.le_succ _))),
            rsbAtExp_congrD aa (hF3.agreeOn hokA2), hs2, rsbExp_congrD ae (hF3.agreeOn (hokA1.mono hn2)),
            rsbExp_congrD ae (hF2.agreeOn hokA1), hs1]
    | _ => simp [AExp.erase] at he
  | .lam p e, C, C', S', st, a', hp, hc, he, hnb => by
    cases a' with
    | lam p' e' =>
      simp only [AExp.erase, BExp.lam.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      simp only [checkExpS, Bool.and_eq_true] at hc; obtain ⟨hc1, hc2⟩ := hc
      simp only [tysExp] at hnb; obtain ⟨hnb1, hnb2⟩ := NBD.app hnb
      simp only [wdExp]
      refine outP_bindD (wAtPat_completeD fuel n0 _ C C' C' S' st p' hp (lkC_refl C') hc1 rfl hnb1) ?_
      rintro ⟨τp, ap⟩ st1 ⟨hn1, hi1, hok1, hty1, hokA1, T1, hF1, hs1⟩
      dsimp only at *
      have hve := pat_ve_eqD hs1
      have hpre := pre_patD hp hn1 hi1 hF1 (atpat_ve ap) hokA1
      rw [← hve] at hpre
      refine outP_bindD (wExp_completeD fuel n0 _ _ _ T1 st1 e' hpre hc2 rfl hnb2) ?_
      rintro ⟨τe, ae⟩ st2 ⟨hn2, hi2, hok2, hokA2, T2, hF2, hty2, hs2⟩
      dsimp only at *
      refine outP_pureD ⟨by omega, hi2, OkT_fnD (hok1.mono hn2) hok2, (hokA1.mono hn2).app hokA2, T2,
        hF1.trans hF2 hn1, ?_, ?_⟩
      · show Ty.fn (rsb T2 τp) (rsb T2 τe) = Ty.fn p'.ty e'.ty
        rw [hF2.sb_eq hok1, hty2, ← hty1, atpat_ty_eqD hs1]
      · simp only [rsbExp, stripExp] at hs2 ⊢
        rw [hs2, rsbAtPat_congrD ap (hF2.agreeOn hokA1), hs1]
    | _ => simp [AExp.erase] at he
  | .caseE e m, C, C', S', st, a', hp, hc, he, hnb => by
    cases a' with
    | caseE e' m' =>
      simp only [AExp.erase, BExp.caseE.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      simp only [checkExpS, Bool.and_eq_true] at hc; obtain ⟨⟨hc1, hc2⟩, hc3⟩ := hc
      obtain ⟨r, hr⟩ := fn_of_match hc3
      simp only [tysExp] at hnb; obtain ⟨hnb1, hnb2⟩ := NBD.app hnb
      simp only [wdExp]
      refine outP_bindD (wExp_completeD fuel n0 _ C C' S' st e' hp hc1 rfl hnb1) ?_
      rintro ⟨τe, ae⟩ st1 ⟨hn1, hi1, hok1, hokA1, T1, hF1, hty1, hs1⟩
      have hp1 := hp.next hi1 hn1 hF1
      refine outP_bindD (wMatch_completeD fuel n0 _ C C' T1 st1 m' hp1 hc2 rfl hnb2) ?_
      rintro ⟨τm, am⟩ st2 ⟨hn2, hi2, hok2, hokA2, T2, hF2, hty2, hs2⟩
      have hp2 := hp1.next hi2 hn2 hF2
      dsimp only at *
      refine outP_freshVD ?_
      have hF3 := found_ext1D hp2 r
      have hF123 := (hF1.trans hF2 hn1).trans hF3 (by omega)
      refine outP_unifyWD hi2.fresh (hok2.mono (Nat.le_succ _))
        (OkT_fnD ((hok1.mono hn2).mono (Nat.le_succ _)) okT_freshD) hF3.fix (hF123.resp hp.resp) hF3.abs ?_
        (by rw [hF3.sb_eq hok2, hty2]; exact cn_match_ty m' hnb2.cn)
        fun st4 T4 hn4 hi4 ag4 fx4 r4 hab4 => ?_
      · rw [hF3.sb_eq hok2, hty2, hr]
        simp only [rsb, ext1C_selfD, hF3.sb_eq (hok1.mono hn2), hF2.sb_eq hok1, hty1]
      · dsimp only at hn4 ag4
        have hF4 : FoundD n0 (ext1D T2 st2.n r) (st2.n + 1) st4 T4 := FoundD.ofUnify fx4 hab4 ag4 r4
        refine outP_pureD ⟨by omega, hi4, okT_freshD.mono hn4,
          (((hokA1.mono hn2).app hokA2).mono (Nat.le_succ _)).mono hn4, T4,
          hF123.trans hF4 (by omega), ?_, ?_⟩
        · rw [hF4.sb_eq okT_freshD]; simp [rsb, ext1C_selfD, AExp.ty, hr, Ty.cod]
        · simp only [rsbExp, stripExp] at hs1 hs2 ⊢
          rw [rsbMatch_congrD am (hF4.agreeOn (hokA2.mono (Nat.le_succ _))),
            rsbExp_congrD ae (hF4.agreeOn ((hokA1.mono hn2).mono (Nat.le_succ _))),
            rsbMatch_congrD am (hF3.agreeOn hokA2), hs2, rsbExp_congrD ae (hF3.agreeOn (hokA1.mono hn2)),
            rsbExp_congrD ae (hF2.agreeOn hokA1), hs1]
    | _ => simp [AExp.erase] at he
theorem wExpOpt_completeD (fuel n0 : Nat) : ∀ (e : Option BExp) (C C' : Ctx) (S' : RSub) (st : WDSt)
    (a' : Option AExp), PreD n0 C C' S' st → checkExpOpt C' a' = true → AExp.eraseOpt a' = e →
    NBD (tysExpOpt false a') → OutPD (EOptPostD n0 st S' a') (wdExpOpt fuel (rigidFromD n0) C e st)
  | none, C, C', S', st, a', hp, _, he, _ => by
    cases a' with
    | none =>
      simp only [wdExpOpt]
      exact outP_pureD ⟨Nat.le_refl _, hp.inv, (fun _ h => by cases h), OkAD.nil, S', FoundD.refl hp, rfl, rfl⟩
    | some _ => simp [AExp.eraseOpt] at he
  | some e, C, C', S', st, a', hp, hc, he, hnb => by
    cases a' with
    | some e' =>
      simp only [AExp.eraseOpt, Option.some.injEq] at he; subst he
      simp only [checkExpOpt] at hc
      simp only [tysExpOpt] at hnb
      simp only [wdExpOpt]
      refine outP_bindD (wExp_completeD fuel n0 _ C C' S' st e' hp hc rfl hnb) ?_
      rintro ⟨τ, ae⟩ st1 ⟨hn1, hi1, hok1, hokA1, T1, hF1, hty1, hs1⟩
      exact outP_pureD ⟨hn1, hi1, (fun _ h => by cases h; exact hok1), hokA1, T1, hF1,
        by simp [rsbOpt, AExp.tyOpt, hty1], by simp only [rsbExpOpt, stripExpOpt, hs1]⟩
    | none => simp [AExp.eraseOpt] at he
theorem wMatch_completeD (fuel n0 : Nat) : ∀ (m : BMatch) (C C' : Ctx) (S' : RSub) (st : WDSt) (m' : AMatch),
    PreD n0 C C' S' st → checkMatch C' m' = true → m'.erase = m → NBD (tysMatch false m') →
    OutPD (MPostD n0 st S' m') (wdMatch fuel (rigidFromD n0) C m st)
  | .mk mr rest, C, C', S', st, m', hp, hc, he, hnb => by
    cases m' with
    | mk mr' rest' =>
      simp only [AMatch.erase, BMatch.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      simp only [checkMatch, Bool.and_eq_true] at hc; obtain ⟨hc1, hc2⟩ := hc
      simp only [tysMatch] at hnb; obtain ⟨hnb1, hnb2⟩ := NBD.app hnb
      simp only [wdMatch]
      refine outP_bindD (wMRule_completeD fuel n0 _ C C' S' st mr' hp hc1 rfl hnb1) ?_
      rintro ⟨τ, amr⟩ st1 ⟨hn1, hi1, hok1, hokA1, T1, hF1, hty1, hs1⟩
      have hp1 := hp.next hi1 hn1 hF1
      refine outP_bindD (wMatchOpt_completeD fuel n0 _ C C' T1 st1 τ mr'.ty rest' hp1 hok1 hty1 hc2 rfl hnb2) ?_
      rintro ar st2 ⟨hn2, hi2, hokA2, T2, hF2, hs2⟩
      dsimp only at *
      refine outP_pureD ⟨by omega, hi2, hok1.mono hn2, (hokA1.mono hn2).app hokA2, T2, hF1.trans hF2 hn1, ?_, ?_⟩
      · simp only [AMatch.ty, hF2.sb_eq hok1, hty1]
      · simp only [rsbMatch, stripMatch] at hs2 ⊢
        rw [hs2, rsbMRule_congrD amr (hF2.agreeOn hokA1), hs1]
theorem wMatchOpt_completeD (fuel n0 : Nat) : ∀ (m : Option BMatch) (C C' : Ctx) (S' : RSub) (st : WDSt) (τ τ' : Ty)
    (m' : Option AMatch), PreD n0 C C' S' st → OkTD st.n τ → rsb S' τ = τ' → checkMatchOptAt C' τ' m' = true →
    AMatch.eraseOpt m' = m → NBD (tysMatchOpt false m') →
    OutPD (MOptPostD n0 st S' m') (wdMatchOpt fuel (rigidFromD n0) C τ m st)
  | none, C, C', S', st, τ, τ', m', hp, _, _, _, he, _ => by
    cases m' with
    | none => simp only [wdMatchOpt]; exact outP_pureD ⟨Nat.le_refl _, hp.inv, OkAD.nil, S', FoundD.refl hp, rfl⟩
    | some _ => simp [AMatch.eraseOpt] at he
  | some m, C, C', S', st, τ, τ', m', hp, hok, hτ, hc, he, hnb => by
    cases m' with
    | some m'' =>
      simp only [AMatch.eraseOpt, Option.some.injEq] at he; subst he
      simp only [checkMatchOptAt, Bool.and_eq_true, decide_eq_true_eq] at hc; obtain ⟨hc1, hc2⟩ := hc
      simp only [tysMatchOpt] at hnb
      simp only [wdMatchOpt]
      refine outP_bindD (wMatch_completeD fuel n0 _ C C' S' st m'' hp hc1 rfl hnb) ?_
      rintro ⟨τm, am⟩ st1 ⟨hn1, hi1, hok1, hokA1, T1, hF1, hty1, hs1⟩
      dsimp only at *
      refine outP_unifyWD hi1 hok1 (hok.mono hn1) hF1.fix (hF1.resp hp.resp) hF1.abs
        (by rw [hty1, hF1.sb_eq hok, hτ, hc2]) (by rw [hty1]; exact cn_match_ty m'' hnb.cn)
        fun st2 T2 hn2 hi2 ag2 fx2 r2 hab2 => ?_
      have hF2 : FoundD n0 T1 st1.n st2 T2 := FoundD.ofUnify fx2 hab2 ag2 r2
      exact outP_pureD ⟨by omega, hi2, hokA1.mono hn2, T2, hF1.trans hF2 hn1,
        by simp only [rsbMatchOpt, stripMatchOpt]; rw [rsbMatch_congrD am (hF2.agreeOn hokA1), hs1]⟩
    | none => simp [AMatch.eraseOpt] at he
theorem wMRule_completeD (fuel n0 : Nat) : ∀ (mr : BMRule) (C C' : Ctx) (S' : RSub) (st : WDSt) (mr' : AMRule),
    PreD n0 C C' S' st → checkMRule C' mr' = true → mr'.erase = mr → NBD (tysMRule false mr') →
    OutPD (MRPostD n0 st S' mr') (wdMRule fuel (rigidFromD n0) C mr st)
  | .mk p e, C, C', S', st, mr', hp, hc, he, hnb => by
    cases mr' with
    | mk p' e' =>
      simp only [AMRule.erase, BMRule.mk.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      simp only [checkMRule, Bool.and_eq_true] at hc; obtain ⟨hc1, hc2⟩ := hc
      simp only [tysMRule] at hnb; obtain ⟨hnb1, hnb2⟩ := NBD.app hnb
      simp only [wdMRule]
      refine outP_bindD (wPat_completeD fuel n0 _ C C' C' S' st p' hp (lkC_refl C') hc1 rfl hnb1) ?_
      rintro ⟨τp, ap⟩ st1 ⟨hn1, hi1, hok1, hty1, hokA1, T1, hF1, hs1⟩
      dsimp only at *
      have hve := pat_ve_eq'D hs1
      have hpre := pre_patD hp hn1 hi1 hF1 (pat_ve ap) hokA1
      rw [← hve] at hpre
      refine outP_bindD (wExp_completeD fuel n0 _ _ _ T1 st1 e' hpre hc2 rfl hnb2) ?_
      rintro ⟨τe, ae⟩ st2 ⟨hn2, hi2, hok2, hokA2, T2, hF2, hty2, hs2⟩
      dsimp only at *
      refine outP_pureD ⟨by omega, hi2, OkT_fnD (hok1.mono hn2) hok2, (hokA1.mono hn2).app hokA2, T2,
        hF1.trans hF2 hn1, ?_, ?_⟩
      · show Ty.fn (rsb T2 τp) (rsb T2 τe) = Ty.fn p'.ty e'.ty
        rw [hF2.sb_eq hok1, hty2, ← hty1, pat_ty_eqD hs1]
      · simp only [rsbMRule, stripMRule] at hs2 ⊢
        rw [hs2, rsbPat_congrD ap (hF2.agreeOn hokA1), hs1]
theorem wDec_completeD (fuel n0 : Nat) : ∀ (d : BDec) (C C' : Ctx) (S' : RSub) (st : WDSt) (d' : ADec),
    PreD n0 C C' S' st → checkDec C' d' = true → d'.erase = d → NBD (tysDec false d') →
    OutPD (DPostD n0 st S' d') (wdDec fuel (rigidFromD n0) C d st)
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
        obtain ⟨hnb1, hnb2⟩ := NBD.app hnb
        simp only [wdDec]
        refine outP_bindD (wAtPat_completeD fuel n0 _ C C' (C'.plusVE p'.ve) S' st p' hp
          (lkC_plusVE fun q hq => (atpat_ve p' q hq).2.1) hc1 rfl hnb1) ?_
        rintro ⟨τp, ap⟩ st1 ⟨hn1, hi1, hok1, hty1, hokA1, T1, hF1, hs1⟩
        dsimp only at *
        by_cases hsh : (ap.ve.all fun q => !conBound C q.1) = true
        rotate_left
        · rw [if_neg hsh]; exact outP_unsupportedD
        rw [if_pos hsh]
        have hve := pat_ve_eqD hs1
        have hpre := pre_patD hp hn1 hi1 hF1 (atpat_ve ap) hokA1
        rw [← hve] at hpre
        refine outP_bindD (wExp_completeD fuel n0 _ _ _ T1 st1 e' hpre hc2 rfl hnb2) ?_
        rintro ⟨τe, ae⟩ st2 ⟨hn2, hi2, hok2, hokA2, T2, hF2, hty2, hs2⟩
        dsimp only at *
        have hF12 := hF1.trans hF2 hn1
        refine outP_unifyWD hi2 hok2 (hok1.mono hn2) hF2.fix (hF12.resp hp.resp) hF2.abs
          (by rw [hty2, hc3, hF2.sb_eq hok1, ← hty1, atpat_ty_eqD hs1]) (by rw [hty2]; exact cn_exp_ty e' hnb2.cn)
          fun st3 T3 hn3 hi3 ag3 fx3 r3 hab3 => ?_
        have hF3 : FoundD n0 T2 st2.n st3 T3 := FoundD.ofUnify fx3 hab3 ag3 r3
        have hokVE : OkAD st1.n (veBodies ap.ve) := fun τ hτ => by
          simp only [veBodies, List.mem_map] at hτ
          obtain ⟨q, hq, rfl⟩ := hτ
          exact okT_pentD hokA1 (atpat_ve ap q hq)
        refine outP_pureD ⟨by omega, hi3, ?_, ?_, T3, hF12.trans hF3 (by omega), ?_, ?_⟩
        · simp only [tysDec, ↓reduceIte, tysValBind]
          exact ((hokVE.mono hn2).app ((hokA1.mono hn2).app hokA2)).mono hn3
        · intro q hq
          simp only [ADec.env] at hq
          exact ⟨(atpat_ve ap q hq).1, ((okT_pentD hokA1 (atpat_ve ap q hq)).mono hn2).mono hn3⟩
        · simp only [rsbDec, stripDec, rsbValBind, stripValBind] at hs2 ⊢
          rw [rsbVE_congrD (hF3.agreeOn (hokVE.mono hn2)), rsbAtPat_congrD ap (hF3.agreeOn (hokA1.mono hn2)),
            rsbExp_congrD ae (hF3.agreeOn hokA2),
            rsbVE_congrD (hF2.agreeOn hokVE), rsbAtPat_congrD ap (hF2.agreeOn hokA1), hs1, hs2, hve]
        · intro q hq
          simp only [ADec.env] at hq
          have hq' : (q.1, (rsbScheme T1 q.2.1, q.2.2)) ∈ p'.ve := by
            rw [hve]; simp only [rsbVE, List.mem_map]; exact ⟨q, hq, rfl⟩
          have := nb_of_pentD hnb1 (atpat_ve p' _ hq')
          simp only [rsbScheme] at this
          rw [hF3.sb_eq ((okT_pentD hokA1 (atpat_ve ap q hq)).mono hn2), hF2.sb_eq (okT_pentD hokA1 (atpat_ve ap q hq))]
          exact this
      | var => simp [ADec.erase, AValBind.erase] at he
  | .val (.var x ann e rest), C, C', S', st, d', hp, hc, he, hnb => by
    cases d' with
    | val VE' vb' =>
      simp only [ADec.erase, BDec.val.injEq] at he
      simp only [checkDec, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hc1, hc2⟩ := hc
      simp only [tysDec, Bool.false_eq_true, ↓reduceIte, List.nil_append] at hnb
      simp only [wdDec]
      have hU : (C'.plusVE VE').U = C.U := by simp [Ctx.plusVE, hp.rel.2.1]
      have hT : ∀ lc, (C'.plusVE VE').lookupTy lc = C.lookupTy lc := fun lc => by
        simp [Ctx.plusVE, Ctx.lookupTy, Env.lookupTy, hp.rel.2.2.1, hp.rel.2.2.2.1]
      refine outP_bindD (groupEntries_completeD hU hT _ st S' vb' hp.inv hp.fix hp.abs (annChk_of_check vb' hc1) he) ?_
      rintro es st1 ⟨hθ1, hn1, hi1, hes, S1, hF1, hrel1⟩
      have hVE' : VE' = rsbVE S1 (groupVE (.var x ann e rest) es) := by
        rw [← hc2, groupVE_relD _ es vb' hrel1 he (fun e he => (hes e he).2)]
      have hmono := groupVE_monoD (.var x ann e rest) es (fun e he => (hes e he).2)
      have hokVE : OkAD st1.n (veBodies (groupVE (.var x ann e rest) es)) := fun τ hτ => by
        simp only [veBodies, List.mem_map] at hτ
        obtain ⟨q, hq, rfl⟩ := hτ
        obtain ⟨-, -, e0, he0, h⟩ := hmono q hq
        rw [h]; exact (hes e0 he0).1
      have hpre : PreD n0 (C.plusVE (groupVE (.var x ann e rest) es)) (C'.plusVE VE') S1 st1 := by
        rw [hVE']
        refine ⟨hi1, (hp.ctxW.mono hn1).plusVE fun q hq => ?_,
          (hp.rel.congr hp.ctxW hF1.agree).plusVE (VEMatch_monoD fun q hq => (hmono q hq).1), hF1.fix, hF1.abs,
          hF1.resp hp.resp⟩
        have : q.2.1 = mono q.2.1.body := by
          have hb := (hmono q hq).1
          revert hb; obtain ⟨_, ⟨b, body⟩, _⟩ := q; intro hb; simp only at hb; subst hb; rfl
        rw [this]
        exact SchW_mono_schemeD (hokVE _ (by simp only [veBodies, List.mem_map]; exact ⟨q, hq, rfl⟩))
      refine outP_bindD (wMembers_completeD fuel n0 _ _ _ S1 st1 es vb' hpre hc1 he hnb hrel1 hes) ?_
      rintro avb st2 ⟨hn2, hi2, hokA2, T2, hF2, hs2⟩
      refine outP_pureD ⟨by omega, hi2, (hokVE.mono hn2).app hokA2, ?_, T2, hF1.trans hF2 hn1, ?_, ?_⟩
      · intro q hq
        simp only [ADec.env] at hq
        obtain ⟨hb, -, e0, he0, h⟩ := hmono q hq
        exact ⟨hb, by rw [h]; exact (hes e0 he0).1.mono hn2⟩
      · simp only [rsbDec, stripDec] at hs2 ⊢
        rw [hs2, rsbVE_congrD (hF2.agreeOn hokVE), ← hVE']
      · intro q hq
        simp only [ADec.env] at hq
        obtain ⟨-, -, e0, he0, h⟩ := hmono q hq
        rw [h, hF2.sb_eq (hes e0 he0).1]
        exact (hnb _ (esRel_memD es vb' hrel1 e0 he0)).1
theorem wMembers_completeD (fuel n0 : Nat) : ∀ (vb : BValBind) (Cg Cg' : Ctx) (S' : RSub) (st : WDSt)
    (es : List (Option (BTy × List BVar) × Ty)) (vb' : AValBind),
    PreD n0 Cg Cg' S' st → checkValBind Cg' vb' = true → vb'.erase = vb → NBD (tysValBind false vb') →
    EsRelD S' es vb' → (∀ e ∈ es, OkTD st.n e.2 ∧ annU e.1 = []) →
    OutPD (VBPostD n0 st S' vb') (wdMembers fuel (rigidFromD n0) Cg vb es st)
  | .pat _ _, Cg, Cg', S', st, es, vb', _, _, _, _, _, _ => by
    simp only [wdMembers]; trivial
  | .var x ann e rest, Cg, Cg', S', st, [], vb', _, _, _, _, hrel, _ => by
    simp only [wdMembers]; trivial
  | .var x ann e rest, Cg, Cg', S', st, (an, τx) :: es, vb', hp, hc, he, hnb, hrel, hes => by
    cases vb' with
    | var x' ann' τ' e' rest' =>
      simp only [AValBind.erase, BValBind.var.injEq] at he; obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      unfold EsRelD at hrel
      obtain ⟨rfl, hτx, hrest⟩ := hrel
      have hann : annU an = [] := (hes _ (.head _)).2
      have hokx : OkTD st.n τx := (hes _ (.head _)).1
      simp only [checkValBind, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨-, hc2⟩, hc3⟩, hc4⟩ := hc
      rw [hann, plusU_nil] at hc2
      simp only [tysValBind, List.cons_append, annMark, List.nil_append] at hnb
      obtain ⟨-, hnb⟩ := NBD.cons hnb
      obtain ⟨hnb1, hnb2⟩ := NBD.app hnb
      simp only [wdMembers, hann, plusU_nil]
      refine outP_bindD (wExp_completeD fuel n0 _ Cg Cg' S' st e' hp hc2 rfl hnb1) ?_
      rintro ⟨τe, ae⟩ st1 ⟨hn1, hi1, hok1, hokA1, T1, hF1, hty1, hs1⟩
      dsimp only at *
      refine outP_unifyWD hi1 hok1 (hokx.mono hn1) hF1.fix (hF1.resp hp.resp) hF1.abs
        (by rw [hty1, hc3, hF1.sb_eq hokx, hτx]) (by rw [hty1]; exact cn_exp_ty e' hnb1.cn)
        fun st2 T2 hn2 hi2 ag2 fx2 r2 hab2 => ?_
      have hF2 : FoundD n0 T1 st1.n st2 T2 := FoundD.ofUnify fx2 hab2 ag2 r2
      have hF1' : FoundD n0 S' st.n st2 T2 := hF1.trans hF2 hn1
      have hp2 : PreD n0 Cg Cg' T2 st2 := hp.next hi2 (by omega) hF1'
      have hrest' : EsRelOptD T2 es rest' := by
        cases rest' with
        | none => exact hrest
        | some vb => exact EsRelD.congr hF1'.agree es vb (fun e he => (hes e (.tail _ he)).1) hrest
      refine outP_bindD (wMembersOpt_completeD fuel n0 _ Cg Cg' T2 st2 es rest' hp2 hc4 rfl hnb2 hrest'
        (fun e he => ⟨((hes e (.tail _ he)).1.mono hn1).mono (by omega), (hes e (.tail _ he)).2⟩)) ?_
      rintro ar st3 ⟨hn3, hi3, hokA3, T3, hF3, hs3⟩
      refine outP_pureD ⟨by omega, hi3, ?_, T3, hF1'.trans hF3 (by omega), ?_⟩
      · simp only [tysValBind, List.cons_append, annMark, hann, ↓reduceIte, List.nil_append]
        exact OkAD.cons ((hokx.mono hn1).mono (by omega)) (((hokA1.mono (by omega))).app hokA3)
      · simp only [rsbValBind, stripValBind] at hs3 ⊢
        rw [hs3, rsbExp_congrD ae (hF3.agreeOn (hokA1.mono (by omega))), rsbExp_congrD ae (hF2.agreeOn hokA1), hs1,
          hF3.sb_eq ((hokx.mono hn1).mono (by omega)), hF2.sb_eq (hokx.mono hn1), hF1.sb_eq hokx, hτx]
    | pat _ _ => simp [AValBind.erase] at he
theorem wMembersOpt_completeD (fuel n0 : Nat) : ∀ (vb : Option BValBind) (Cg Cg' : Ctx) (S' : RSub) (st : WDSt)
    (es : List (Option (BTy × List BVar) × Ty)) (vb' : Option AValBind),
    PreD n0 Cg Cg' S' st → checkValBindOpt Cg' vb' = true → AValBind.eraseOpt vb' = vb →
    NBD (tysValBindOpt false vb') →
    EsRelOptD S' es vb' → (∀ e ∈ es, OkTD st.n e.2 ∧ annU e.1 = []) →
    OutPD (VBOptPostD n0 st S' vb') (wdMembersOpt fuel (rigidFromD n0) Cg vb es st)
  | none, Cg, Cg', S', st, es, vb', hp, _, he, _, _, _ => by
    cases vb' with
    | none => simp only [wdMembersOpt]; exact outP_pureD ⟨Nat.le_refl _, hp.inv, OkAD.nil, S', FoundD.refl hp, rfl⟩
    | some _ => simp [AValBind.eraseOpt] at he
  | some vb, Cg, Cg', S', st, es, vb', hp, hc, he, hnb, hrel, hes => by
    cases vb' with
    | some vb'' =>
      simp only [AValBind.eraseOpt, Option.some.injEq] at he; subst he
      simp only [checkValBindOpt] at hc
      simp only [tysValBindOpt] at hnb
      simp only [wdMembersOpt]
      refine outP_bindD (wMembers_completeD fuel n0 _ Cg Cg' S' st es vb'' hp hc rfl hnb
        (by simpa [EsRelOptD] using hrel) hes) ?_
      rintro avb st1 ⟨hn1, hi1, hokA1, T1, hF1, hs1⟩
      exact outP_pureD ⟨hn1, hi1, hokA1, T1, hF1, by simp only [rsbValBindOpt, stripValBindOpt, hs1]⟩
    | none => simp [AValBind.eraseOpt] at he
end

end StandardElm.Stat.Complete
