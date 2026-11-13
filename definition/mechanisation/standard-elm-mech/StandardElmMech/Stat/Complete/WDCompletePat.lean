/-
  A Standard Definition of Elm? Mechanisation: the main induction L11 of plan step 11 with
  records and rows (milestone (d), section 8) for patterns (L8): W does not fail on a pattern that
  has a derivation (without `bnd` variables, with canonical types), and the derivation is an
  instance of what W returns (with the instance lists left out). WCompletePat.lean for
  `inferExpWD`, with the record pattern: its fields are fresh type variables and its tail a
  fresh row variable, mapped to the fields the derivation's record type has and the pattern
  lacks (`mrg_onlyL_eq`).

  The hypotheses of a call (`PreD`): W's state is good (`SInvD`), W's context holds schemes W can
  hold (`CtxWD`), the derivation's context `C'` is no more general than `S'` applied to W's
  (`CtxRelD (SchRelD S')`), and `S'` fixes the rigid variables, absorbs W's substitution and
  respects classes. The conclusion (`FoundD`): an extension `T` of `S'` to the variables W
  created, still fixing the rigid variables and absorbing the new substitution, that maps W's
  phrase to the derivation's.
-/
import StandardElmMech.Stat.Complete.WDRows
import StandardElmMech.Stat.Complete.WCompletePat

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BAtPat BPat BPatRow)

/-! ## Hypotheses and conclusions of a call -/

def OkAD (n : Nat) (l : List Ty) : Prop := ∀ τ ∈ l, OkTD n τ

theorem OkAD.mono {n m : Nat} (h : n ≤ m) {l : List Ty} (hl : OkAD n l) : OkAD m l := fun τ hτ => (hl τ hτ).mono h
theorem OkAD.app {n : Nat} {l1 l2 : List Ty} (h1 : OkAD n l1) (h2 : OkAD n l2) : OkAD n (l1 ++ l2) := fun τ hτ => by
  rcases List.mem_append.mp hτ with h | h
  · exact h1 τ h
  · exact h2 τ h
theorem OkAD.cons {n : Nat} {τ : Ty} {l : List Ty} (h1 : OkTD n τ) (h2 : OkAD n l) : OkAD n (τ :: l) := fun x hx => by
  rcases List.mem_cons.mp hx with rfl | h
  · exact h1
  · exact h2 x h
theorem OkAD.nil {n : Nat} : OkAD n [] := fun _ h => by cases h

structure FoundD (n0 : Nat) (S' : RSub) (n : Nat) (st' : WDSt) (T : RSub) : Prop where
  fix : FixR (rigidFromD n0) T
  abs : AbsR T st'.θ
  agree : ∀ v, newB n v = false → T.img v = S'.img v
  /-- Where `T` differs from `S'` on a type variable, it maps it to an admissible type of its
      class. -/
  cls : ∀ a, T.t a ≠ S'.t a → Adm a.cls (T.t a)

structure PreD (n0 : Nat) (C C' : Ctx) (S' : RSub) (st : WDSt) : Prop where
  inv : SInvD n0 st
  ctxW : CtxWD st.n C
  rel : CtxRelD (SchRelD S') (rigidFromD n0) C C'
  fix : FixR (rigidFromD n0) S'
  abs : AbsR S' st.θ
  resp : RespR S'

theorem FoundD.resp {n0 n : Nat} {S' T : RSub} {st : WDSt} (h : FoundD n0 S' n st T) (hS : RespR S') : RespR T :=
  fun a => by
    by_cases e : T.t a = S'.t a
    · rw [e]; exact hS a
    · exact h.cls a e

theorem FoundD.refl {n0 : Nat} {C C' : Ctx} {S' : RSub} {st : WDSt} (hp : PreD n0 C C' S' st) :
    FoundD n0 S' st.n st S' := ⟨hp.fix, hp.abs, fun _ _ => rfl, fun _ h => absurd rfl h⟩

theorem FoundD.trans {n0 n n1 : Nat} {S' T1 T2 : RSub} {st1 st2 : WDSt} (h1 : FoundD n0 S' n st1 T1)
    (h2 : FoundD n0 T1 n1 st2 T2) (hn : n ≤ n1) : FoundD n0 S' n st2 T2 :=
  ⟨h2.fix, h2.abs, fun v hv => (h2.agree v (newB_mono hn hv)).trans (h1.agree v hv), fun a ha => by
    by_cases e : T2.t a = T1.t a
    · rw [e] at ha ⊢; exact h1.cls a ha
    · exact h2.cls a e⟩

theorem FoundD.sb_eq {n0 n : Nat} {S' T : RSub} {st : WDSt} (h : FoundD n0 S' n st T) {τ : Ty} (hτ : OkTD n τ) :
    rsb T τ = rsb S' τ := rsb_agreeD hτ.old h.agree

theorem FoundD.agreeOn {n0 n : Nat} {S' T : RSub} {st : WDSt} (h : FoundD n0 S' n st T) {l : List Ty}
    (hl : OkAD n l) : AgreeOnD T S' l := fun τ hτ => h.sb_eq (hl τ hτ)

theorem schRel_congrD {n : Nat} {σ σ' : Scheme} {S T : RSub} (hσ : SchWD n σ)
    (hT : ∀ v, newB n v = false → T.img v = S.img v) (h : SchRelD S σ σ') : SchRelD T σ σ' := by
  have free : ∀ w ∈ σ.body.vars, w ∉ σ.bound → T.img w = S.img w := fun w hw hb => hT w (hσ.2 w hw hb).2
  refine ⟨fun w hw v hv => ?_, fun τ hg => ?_⟩
  · have hw' : w ∈ σ.body.vars ∧ w ∉ σ.bound := by
      simp only [Scheme.tyvars, diffL, Ty.tyvars, List.mem_filter, Bool.not_eq_true',
        decide_eq_false_iff_not] at hw
      exact ⟨hw.1.1, hw.2⟩
    rw [free w hw'.1 hw'.2] at hv; exact h.1 w hw v hv
  · obtain ⟨g, hga, hg'⟩ := h.2 τ hg
    refine ⟨g, hga, hg'.trans (rsb_congr _ fun w hw => ?_)⟩
    rw [extS_img, extS_img]
    split
    · rfl
    · rename_i hb; exact (free w hw hb).symm

theorem CtxRelD.congr {n n0 : Nat} {C C' : Ctx} {S T : RSub} (h : CtxRelD (SchRelD S) (rigidFromD n0) C C')
    (hC : CtxWD n C) (hT : ∀ v, newB n v = false → T.img v = S.img v) : CtxRelD (SchRelD T) (rigidFromD n0) C C' :=
  h.mono fun x σ st σ' hf hs => schRel_congrD (hC ⟨none, x⟩ σ st (by simpa [Ctx.lookupVal, Env.lookupVal] using hf)) hT hs

theorem PreD.next {n0 : Nat} {C C' : Ctx} {S' T : RSub} {st st' : WDSt} (hp : PreD n0 C C' S' st)
    (hi : SInvD n0 st') (hn : st.n ≤ st'.n) (hF : FoundD n0 S' st.n st' T) : PreD n0 C C' T st' :=
  ⟨hi, hp.ctxW.mono hn, hp.rel.congr hp.ctxW hF.agree, hF.fix, hF.abs, hF.resp hp.resp⟩

theorem rigid_bndD (n0 : Nat) : ∀ v : BVar, v.isBnd = true → rigidFromD n0 v = true := fun _ h => rigidFromD_bnd n0 h

/-- `S'` with the fresh type variable `n` of class `c` mapped to `τ'`. -/
def ext1CD (S' : RSub) (n : Nat) (c : Cls) (τ' : Ty) : RSub := ⟨fun d => if d = .fresh n c then τ' else S'.t d, S'.r⟩

theorem ext1CD_agree (S' : RSub) (n : Nat) (c : Cls) (τ' : Ty) :
    ∀ v, newB n v = false → (ext1CD S' n c τ').img v = S'.img v := fun v hv => by
  cases v with
  | ty a => simp only [RSub.img, ext1CD]; rw [if_neg]; rintro rfl; simp [newB, TyVar.isNew] at hv
  | row e => rfl

theorem found_ext1CD' {n0 : Nat} {S' : RSub} {st : WDSt} (hi : SInvD n0 st) (hfx : FixR (rigidFromD n0) S')
    (hab : AbsR S' st.θ) {c : Cls} {τ' : Ty}
    (hadm : Adm c τ') : FoundD n0 S' st.n { st with n := st.n + 1 } (ext1CD S' st.n c τ') := by
  obtain ⟨h1, h2⟩ := agree_okD hi.le hi.good hfx hab (ext1CD_agree S' st.n c τ')
  refine ⟨h1, h2, ext1CD_agree S' st.n c τ', fun a ha => ?_⟩
  simp only [ext1CD] at ha ⊢
  split at ha
  · rename_i e; subst e; rw [if_pos rfl]; exact hadm
  · exact absurd rfl ha

theorem found_ext1CD {n0 : Nat} {C C' : Ctx} {S' : RSub} {st : WDSt} (hp : PreD n0 C C' S' st) {c : Cls} {τ' : Ty}
    (hadm : Adm c τ') : FoundD n0 S' st.n { st with n := st.n + 1 } (ext1CD S' st.n c τ') :=
  found_ext1CD' hp.inv hp.fix hp.abs hadm

theorem ext1C_selfD (S' : RSub) (n : Nat) (c : Cls) (τ' : Ty) : (ext1CD S' n c τ').t (.fresh n c) = τ' := by
  simp [ext1CD]

/-- `S'` with the fresh type variable `n` (class any) mapped to `τ'`. -/
abbrev ext1D (S' : RSub) (n : Nat) (τ' : Ty) : RSub := ext1CD S' n .any τ'

theorem found_ext1D {n0 : Nat} {C C' : Ctx} {S' : RSub} {st : WDSt} (hp : PreD n0 C C' S' st) (τ' : Ty) :
    FoundD n0 S' st.n { st with n := st.n + 1 } (ext1D S' st.n τ') := found_ext1CD hp (Adm.any _)

theorem ext1_selfD (S' : RSub) (n : Nat) (τ' : Ty) : (ext1D S' n τ').t (.fresh n .any) = τ' := ext1C_selfD _ _ _ _

theorem okT_freshCD {st : WDSt} {c : Cls} : OkTD (st.n + 1) (.var (.fresh st.n c)) :=
  OkT_varD rfl (by simp [newB, TyVar.isNew])

theorem okT_freshD {st : WDSt} : OkTD (st.n + 1) (.var (.fresh st.n .any)) := okT_freshCD

theorem extR_agreeD (S' : RSub) (n : Nat) (q : Row × Option RowVar) :
    ∀ v, newB n v = false → (extR S' (.fresh n) q).img v = S'.img v := fun v hv => by
  cases v with
  | ty a => rfl
  | row e => simp only [RSub.img, extR]; rw [if_neg]; rintro rfl; simp [newB] at hv

/-- `S'` with the fresh row variable `n` mapped to `⟨ρ | tl⟩`. -/
theorem found_extR {n0 : Nat} {S' : RSub} {st : WDSt} (hi : SInvD n0 st) (hfx : FixR (rigidFromD n0) S')
    (hab : AbsR S' st.θ) (q : Row × Option RowVar) :
    FoundD n0 S' st.n { st with n := st.n + 1 } (extR S' (.fresh st.n) q) := by
  obtain ⟨h1, h2⟩ := agree_okD hi.le hi.good hfx hab (extR_agreeD S' st.n q)
  exact ⟨h1, h2, extR_agreeD S' st.n q, fun a ha => absurd rfl ha⟩

/-! ## Constructors in patterns -/

theorem rsb_conD {s : RSub} {τ : Ty} {as : List Ty} {t : TyName} (h : rsb s τ = .con as t) :
    (∃ us, τ = .con us t) ∨ ∃ a, τ = .var a := by
  cases τ with
  | var a => exact .inr ⟨a, rfl⟩
  | con us t' => simp only [rsb, Ty.con.injEq] at h; exact .inl ⟨us, by rw [h.2]⟩
  | fn _ _ => simp [rsb] at h
  | record _ _ => simp [rsb] at h

theorem peel_rsbD {s : RSub} : ∀ (k : Nat) (τ : Ty) (τs : List Ty) (r : Ty), peel k τ = some (τs, r) →
    τs.length = k ∧ rsb s τ = arrows (rsbList s τs) (rsb s r)
  | 0, τ, τs, r, h => by simp only [peel, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp [arrows, rsbList]
  | k + 1, .fn a b, τs, r, h => by
    simp only [peel] at h
    cases hp : peel k b with
    | none => rw [hp] at h; cases h
    | some p =>
      rw [hp] at h
      obtain ⟨as, r'⟩ := p
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h1, h2⟩ := peel_rsbD (s := s) k b as r' hp
      simp [h1, rsb, h2, arrows, rsbList]
  | k + 1, .var _, _, _, h => by simp [peel] at h
  | k + 1, .con _ _, _, _, h => by simp [peel] at h
  | k + 1, .record _ _, _, _, h => by simp [peel] at h

theorem peel_varsD : ∀ (k : Nat) (τ : Ty) (τs : List Ty) (r : Ty), peel k τ = some (τs, r) →
    τ = arrows τs r
  | 0, τ, τs, r, h => by simp only [peel, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
  | k + 1, .fn a b, τs, r, h => by
    simp only [peel] at h
    cases hp : peel k b with
    | none => rw [hp] at h; cases h
    | some p =>
      rw [hp] at h
      obtain ⟨as, r'⟩ := p
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      rw [peel_varsD k b as r' hp]; rfl
  | k + 1, .var _, _, _, h => by simp [peel] at h
  | k + 1, .con _ _, _, _, h => by simp [peel] at h
  | k + 1, .record _ _, _, _, h => by simp [peel] at h

theorem peel_none_neD {s : RSub} : ∀ (k : Nat) (τ : Ty) (l : List Ty) (τ' : Ty), peel k τ = none →
    peelStuckVar k τ = false → l.length = k → rsb s τ ≠ arrows l τ'
  | 0, _, _, _, h, _, _, _ => by simp [peel] at h
  | k + 1, .fn a b, l, τ', h, hs, hl, e => by
    simp only [peel] at h
    cases hp : peel k b with
    | some _ => rw [hp] at h; cases h
    | none =>
      cases l with
      | nil => cases hl
      | cons x l =>
        simp only [rsb, arrows, Ty.fn.injEq] at e
        exact peel_none_neD k b l τ' hp (by simpa [peelStuckVar] using hs) (by simpa using hl) e.2
  | k + 1, .var _, _, _, _, hs, _, _ => by simp [peelStuckVar] at hs
  | k + 1, .con _ _, l, _, _, _, hl, e => by
    cases l with
    | nil => cases hl
    | cons _ _ => simp [rsb, arrows] at e
  | k + 1, .record _ _, l, _, _, _, hl, e => by
    cases l with
    | nil => cases hl
    | cons _ _ => simp [rsb, arrows] at e

theorem rsbAtPats_mapD (s : RSub) : ∀ l : List AAtPat, rsbAtPats s l = l.map (rsbAtPat s)
  | [] => rfl
  | a :: l => by simp [rsbAtPats, rsbAtPats_mapD s l]

/-- The conclusion of a `unify` step for the main induction. -/
theorem FoundD.ofUnify {n0 n : Nat} {T T' : RSub} {st' : WDSt} (fx : FixR (rigidFromD n0) T')
    (ab : AbsR T' st'.θ) (ag : ∀ v, newB n v = false → T'.img v = T.img v) (r : RespR T') :
    FoundD n0 T n st' T' := ⟨fx, ab, ag, fun a _ => r a⟩

/-- `unifyArgs`: if `T` unifies the two lists, with canonical images, it does not fail, and a
    `T'` agreeing with `T` on the old variables absorbs the result. -/
theorem outP_unifyArgsD {fuel n0 : Nat} : ∀ (l1 l2 : List Ty) (st : WDSt) (T : RSub), SInvD n0 st →
    (∀ x ∈ l1, OkTD st.n x) → (∀ x ∈ l2, OkTD st.n x) → FixR (rigidFromD n0) T → RespR T → AbsR T st.θ →
    rsbList T l1 = rsbList T l2 → (∀ x ∈ l1, cnB (rsb T x) = true) →
    OutPD (fun _ st' => st.n ≤ st'.n ∧ SInvD n0 st' ∧ ∃ T', FoundD n0 T st.n st' T' ∧ RespR T')
      (unifyArgsD fuel (rigidFromD n0) l1 l2 st)
  | [], [], st, T, hi, _, _, hT, hr, ha, _, _ => ⟨Nat.le_refl _, hi, T, ⟨hT, ha, fun _ _ => rfl, fun _ h => absurd rfl h⟩, hr⟩
  | t :: l1, u :: l2, st, T, hi, h1, h2, hT, hr, ha, he, hc => by
    simp only [rsbList, List.cons.injEq] at he
    simp only [unifyArgsD]
    refine outP_unifyWD hi (h1 t (.head _)) (h2 u (.head _)) hT hr ha he.1 (hc t (.head _))
      fun st' T' hn hi' ag fx r ha' => ?_
    have hF : FoundD n0 T st.n st' T' := FoundD.ofUnify fx ha' ag r
    have e2 : rsbList T' l1 = rsbList T' l2 := by
      rw [rsbList_eq, rsbList_eq, List.map_congr_left (fun x hx => hF.sb_eq (h1 x (.tail _ hx))),
        List.map_congr_left (fun x hx => hF.sb_eq (h2 x (.tail _ hx))), ← rsbList_eq, ← rsbList_eq]
      exact he.2
    refine outP_monoD (outP_unifyArgsD l1 l2 st' T' hi' (fun x hx => (h1 x (.tail _ hx)).mono hn)
      (fun x hx => (h2 x (.tail _ hx)).mono hn) fx r ha' e2
      (fun x hx => by rw [hF.sb_eq (h1 x (.tail _ hx))]; exact hc x (.tail _ hx)))
      fun _ st'' ⟨e, hi'', T'', hF'', r''⟩ => ⟨Nat.le_trans hn e, hi'', T'', hF.trans hF'' hn, r''⟩
  | [], _ :: _, _, _, _, _, _, _, _, _, he, _ => by simp [rsbList] at he
  | _ :: _, [], _, _, _, _, _, _, _, _, he, _ => by simp [rsbList] at he

/-! ## Record patterns -/

theorem rsbRow_rowOpt (s : RSub) : ∀ r : Option APatRow, rsbRow s (APatRow.rowOpt r) = APatRow.rowOpt (rsbPatRowOpt s r)
  | none => rfl
  | some (.field l τ rest) => by
    simp only [APatRow.rowOpt, APatRow.row, rsbPatRowOpt, rsbPatRow, rsbRow_modifyD, rsbRow, rsbRow_rowOpt s rest]

theorem isRecordTy_spec {τ : Ty} (h : isRecordTy τ = true) : ∃ ρ tl, τ = .record ρ tl := by
  cases τ with
  | record ρ tl => exact ⟨ρ, tl, rfl⟩
  | _ => simp [isRecordTy] at h

theorem rsb_record_extR (T1 : RSub) (n : Nat) (q : Row × Option RowVar) (ρ : Row) :
    rsb (extR T1 (.fresh n) q) (.record ρ (some (.fresh n))) = .record (mrg (rsbRow (extR T1 (.fresh n) q) ρ) q.1) q.2 := by
  simp [rsb, RSub.tl, extR]

def RPost (n0 : Nat) (st : WDSt) (S' : RSub) (r' : APatRow) (r : APatRow) (st' : WDSt) : Prop :=
  st.n ≤ st'.n ∧ SInvD n0 st' ∧ OkAD st'.n (tysPatRow r) ∧ ∃ T, FoundD n0 S' st.n st' T ∧ rsbPatRow T r = r'

def ROptPost (n0 : Nat) (st : WDSt) (S' : RSub) (r' : Option APatRow) (r : Option APatRow) (st' : WDSt) : Prop :=
  st.n ≤ st'.n ∧ SInvD n0 st' ∧ OkAD st'.n (tysPatRowOpt r) ∧ ∃ T, FoundD n0 S' st.n st' T ∧ rsbPatRowOpt T r = r'

mutual
/-- The fields of a record pattern: fresh type variables, mapped to the derivation's. -/
theorem wdPatRow_complete (fuel n0 : Nat) : ∀ (r : BPatRow) (st : WDSt) (S' : RSub) (r' : APatRow),
    SInvD n0 st → FixR (rigidFromD n0) S' → AbsR S' st.θ → r'.erase = r →
    OutPD (RPost n0 st S' r') (wdPatRow fuel (rigidFromD n0) r st)
  | .field l rest, st, S', .field l' τ' rest', hi, hfx, hab, he => by
    simp only [APatRow.erase, BPatRow.field.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    simp only [wdPatRow]
    refine outP_freshVD ?_
    have hF0 : FoundD n0 S' st.n { st with n := st.n + 1 } (ext1D S' st.n τ') := found_ext1CD' hi hfx hab (Adm.any _)
    have f1 := hF0.fix
    have f2 := hF0.abs
    refine outP_bindD (wdPatRowOpt_complete fuel n0 _ _ (ext1D S' st.n τ') rest' hi.fresh f1 f2 rfl) ?_
    rintro ar st1 ⟨hn1, hi1, hokA1, T1, hF1, hr1⟩
    refine outP_pureD ⟨by simp at hn1 ⊢; omega, hi1, OkAD.cons (okT_freshD.mono hn1) hokA1, T1,
      hF0.trans hF1 (Nat.le_succ _), ?_⟩
    simp only [rsbPatRow, hr1]
    congr 1
    rw [show rsb T1 (.var (.fresh st.n .any)) = rsb (ext1D S' st.n τ') (.var (.fresh st.n .any)) from
      hF1.sb_eq okT_freshD]
    exact ext1_selfD S' st.n τ'
theorem wdPatRowOpt_complete (fuel n0 : Nat) : ∀ (r : Option BPatRow) (st : WDSt) (S' : RSub) (r' : Option APatRow),
    SInvD n0 st → FixR (rigidFromD n0) S' → AbsR S' st.θ → APatRow.eraseOpt r' = r →
    OutPD (ROptPost n0 st S' r') (wdPatRowOpt fuel (rigidFromD n0) r st)
  | none, st, S', r', hi, hfx, hab, he => by
    cases r' with
    | none =>
      simp only [wdPatRowOpt]
      exact outP_pureD ⟨Nat.le_refl _, hi, OkAD.nil, S', ⟨hfx, hab, fun _ _ => rfl, fun _ h => absurd rfl h⟩, rfl⟩
    | some _ => simp [APatRow.eraseOpt] at he
  | some r, st, S', r', hi, hfx, hab, he => by
    cases r' with
    | some q =>
      simp only [APatRow.eraseOpt, Option.some.injEq] at he; subst he
      simp only [wdPatRowOpt]
      refine outP_bindD (wdPatRow_complete fuel n0 _ st S' q hi hfx hab rfl) ?_
      rintro a st1 ⟨hn1, hi1, hokA1, T1, hF1, hr1⟩
      exact outP_pureD ⟨hn1, hi1, hokA1, T1, hF1, by simp only [rsbPatRowOpt, hr1]⟩
    | none => simp [APatRow.eraseOpt] at he
end

/-! ## Patterns -/

theorem mem_tysAtPats {q : AAtPat} {τ : Ty} : ∀ {l : List AAtPat}, q ∈ l → τ ∈ tysAtPat q → τ ∈ tysAtPats l
  | _ :: _, hq, hτ => by
    simp only [tysAtPats, List.mem_append]
    rcases List.mem_cons.mp hq with rfl | hq
    · exact .inl hτ
    · exact .inr (mem_tysAtPats hq hτ)



def APPostD (n0 : Nat) (st : WDSt) (S' : RSub) (p' : AAtPat) (r : Ty × AAtPat) (st' : WDSt) : Prop :=
  st.n ≤ st'.n ∧ SInvD n0 st' ∧ OkTD st'.n r.1 ∧ r.2.ty = r.1 ∧ OkAD st'.n (tysAtPat r.2) ∧
    ∃ T, FoundD n0 S' st.n st' T ∧ stripAtPat (rsbAtPat T r.2) = stripAtPat p'

def PPostD (n0 : Nat) (st : WDSt) (S' : RSub) (p' : APat) (r : Ty × APat) (st' : WDSt) : Prop :=
  st.n ≤ st'.n ∧ SInvD n0 st' ∧ OkTD st'.n r.1 ∧ r.2.ty = r.1 ∧ OkAD st'.n (tysPat r.2) ∧
    ∃ T, FoundD n0 S' st.n st' T ∧ stripPat (rsbPat T r.2) = stripPat p'

def POptPostD (n0 : Nat) (st : WDSt) (S' : RSub) (p' : Option APat) (r : Option Ty × Option APat) (st' : WDSt) : Prop :=
  st.n ≤ st'.n ∧ SInvD n0 st' ∧ (∀ τ, r.1 = some τ → OkTD st'.n τ) ∧ APat.tyOpt r.2 = r.1 ∧
    OkAD st'.n (tysPatOpt r.2) ∧ ∃ T, FoundD n0 S' st.n st' T ∧ stripPatOpt (rsbPatOpt T r.2) = stripPatOpt p'

def PsPostD (n0 : Nat) (st : WDSt) (S' : RSub) (ps' : List AAtPat) (r : List (Ty × AAtPat)) (st' : WDSt) : Prop :=
  st.n ≤ st'.n ∧ SInvD n0 st' ∧ (∀ q ∈ r, OkTD st'.n q.1 ∧ q.2.ty = q.1) ∧ OkAD st'.n (tysAtPats (r.map (·.2))) ∧
    ∃ T, FoundD n0 S' st.n st' T ∧ stripAtPats (rsbAtPats T (r.map (·.2))) = stripAtPats ps'

mutual
theorem wAtPat_completeD (fuel n0 : Nat) : ∀ (p : BAtPat) (C C' C'' : Ctx) (S' : RSub) (st : WDSt) (p' : AAtPat),
    PreD n0 C C' S' st → LkC C'' C' → checkAtPat C'' p' = true → p'.erase = p → NBD (tysAtPat p') →
    OutPD (APPostD n0 st S' p') (wdAtPat fuel (rigidFromD n0) C p st)
  | .wild, C, C', C'', S', st, p', hp, _, _, he, _ => by
    cases p' with
    | wild τ' =>
      simp only [wdAtPat]
      refine outP_freshVD (outP_pureD ⟨Nat.le_succ _, hp.inv.fresh, okT_freshD, rfl,
        OkAD.cons okT_freshD OkAD.nil, ext1D S' st.n τ', found_ext1D hp τ', ?_⟩)
      simp [rsbAtPat, stripAtPat, rsb, ext1CD]
    | _ => simp [AAtPat.erase] at he
  | .var x, C, C', C'', S', st, p', hp, _, _, he, _ => by
    cases p' with
    | var x' τ' =>
      simp only [AAtPat.erase, BAtPat.var.injEq] at he; subst he
      simp only [wdAtPat]
      refine outP_freshVD (outP_pureD ⟨Nat.le_succ _, hp.inv.fresh, okT_freshD, rfl,
        OkAD.cons okT_freshD OkAD.nil, ext1D S' st.n τ', found_ext1D hp τ', ?_⟩)
      simp [rsbAtPat, stripAtPat, rsb, ext1CD]
    | _ => simp [AAtPat.erase] at he
  | .scon sc, C, C', C'', S', st, p', hp, _, hc, he, _ => by
    cases p' with
    | scon sc' τ' =>
      simp only [AAtPat.erase, BAtPat.scon.injEq] at he; subst he
      simp only [checkAtPat, Bool.and_eq_true, decide_eq_true_eq] at hc
      have hty := scon_pat_ty hc.1 hc.2
      have hpost : ∀ τ0 : Ty, τ0.vars = [] → τ' = τ0 →
          APPostD n0 st S' (.scon sc' τ') (τ0, .scon sc' τ0) st := fun τ0 hv e =>
        ⟨Nat.le_refl _, hp.inv, OkT_of_vars_nilD hv, rfl, OkAD.cons (OkT_of_vars_nilD hv) OkAD.nil, S',
          FoundD.refl hp, by
            simp only [rsbAtPat, stripAtPat, e]; congr 1; exact rsb_eq_self fun w hw => by rw [hv] at hw; cases hw⟩
      cases sc' with
      | int k => simp only [wdAtPat]; exact hpost _ rfl hty
      | char c => simp only [wdAtPat]; exact hpost _ rfl hty
      | str s => simp only [wdAtPat]; exact hpost _ rfl hty
      | float m e =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc.2 with h | h | h <;> rw [hty] at h <;> cases h
    | _ => simp [AAtPat.erase] at he
  | .con lc, C, C', C'', S', st, p', hp, hl, hc, he, _ => by
    cases p' with
    | con lc' inst τ' =>
      simp only [AAtPat.erase, BAtPat.con.injEq] at he; subst he
      simp only [checkAtPat] at hc
      split at hc
      · rename_i σ' hlk
        simp only [Bool.and_eq_true] at hc
        obtain ⟨σ, hσ, hrel⟩ := hp.rel.lookup hp.fix (rigid_bndD n0) (hl _ _ hlk)
        have hgen := gen_of_genAt hc.1
        obtain ⟨us, t, rfl⟩ := isConTy_spec hc.2
        simp only [wdAtPat, hσ]
        refine outP_instantiateD hp.inv (hp.ctxW _ _ _ hσ) hp.fix hp.abs (hrel.2 _ hgen) ?_
        intro ts τ st' T hle _ hi' hok _ hfx hab hag hcl hτ
        rcases rsb_conD hτ with ⟨us', rfl⟩ | ⟨a, rfl⟩
        · exact ⟨hle, hi', hok, rfl, OkAD.cons hok OkAD.nil, T, ⟨hfx, hab, hag, hcl⟩, by simp [rsbAtPat, stripAtPat, hτ]⟩
        · trivial
      · cases hc
    | _ => simp [AAtPat.erase] at he
  | .unit, C, C', C'', S', st, p', hp, _, _, he, _ => by
    cases p' with
    | unit => simp only [wdAtPat]; exact ⟨Nat.le_refl _, hp.inv, OkT_of_vars_nilD rfl, rfl, OkAD.nil, S', FoundD.refl hp, rfl⟩
    | _ => simp [AAtPat.erase] at he
  | .nil, C, C', C'', S', st, p', hp, _, hc, he, _ => by
    cases p' with
    | nil τ' =>
      simp only [checkAtPat] at hc
      obtain ⟨t, rfl⟩ := isListTy_spec hc
      simp only [wdAtPat]
      refine outP_freshVD (outP_pureD ⟨Nat.le_succ _, hp.inv.fresh, OkT_listD okT_freshD, rfl,
        OkAD.cons (OkT_listD okT_freshD) OkAD.nil, ext1D S' st.n t, found_ext1D hp t, ?_⟩)
      simp [rsbAtPat, stripAtPat, listTy_sbD, rsb, ext1CD]
    | _ => simp [AAtPat.erase] at he
  | .record row, C, C', C'', S', st, p', hp, _, hc, he, hnb => by
    cases p' with
    | record row' τ' =>
      simp only [AAtPat.erase, BAtPat.record.injEq] at he; subst he
      simp only [checkAtPat, Bool.and_eq_true] at hc
      obtain ⟨⟨-, hrec⟩, hsub⟩ := hc
      obtain ⟨ρ', tl', rfl⟩ := isRecordTy_spec hrec
      simp only [recordRow, Row.subB_iff] at hsub
      simp only [tysAtPat] at hnb
      obtain ⟨hnbτ, hnbr⟩ := NBD.cons hnb
      have hcnτ : CnRow ρ' := cnB_record.mp (hnbτ.cn _ (.head _))
      have hcnr : CnRow (APatRow.rowOpt row') := cn_patrowopt_row row' hnbr.cn
      simp only [wdAtPat]
      refine outP_bindD (wdPatRowOpt_complete fuel n0 _ st S' row' hp.inv hp.fix hp.abs rfl) ?_
      rintro ar st1 ⟨hn1, hi1, hokA1, T1, hF1, hr1⟩
      refine outP_freshRowD (outP_pureD ?_)
      have hF2 := found_extR hi1 hF1.fix hF1.abs (onlyL ρ' (APatRow.rowOpt row'), tl')
      have hokτ : OkTD (st1.n + 1) (.record (APatRow.rowOpt ar) (some (.fresh st1.n))) := by
        refine OkT_recordD (fun p hp' => (hokA1 _ (mem_rowOpt_tys hp')).mono (Nat.le_succ _)) ?_
        intro v hv
        simp only [tailVars, List.mem_singleton] at hv; subst hv
        exact ⟨rfl, by simp [newB]⟩
      refine ⟨by simp; omega, hi1.fresh, hokτ, rfl, OkAD.cons hokτ (hokA1.mono (Nat.le_succ _)),
        extR T1 (.fresh st1.n) (onlyL ρ' (APatRow.rowOpt row'), tl'), hF1.trans hF2 hn1, ?_⟩
      have hrow : rsbPatRowOpt (extR T1 (.fresh st1.n) (onlyL ρ' (APatRow.rowOpt row'), tl')) ar = row' := by
        rw [rsbPatRowOpt_congrD ar (hF2.agreeOn hokA1), hr1]
      simp only [rsbAtPat, stripAtPat, hrow]
      congr 1
      rw [rsb_record_extR, rsbRow_rowOpt, hrow, mrg_onlyL_eq hcnr.1 hcnτ.1 hsub]
    | _ => simp [AAtPat.erase] at he
  | .tuple p1 p2 p3, C, C', C'', S', st, p', hp, hl, hc, he, hnb => by
    cases p' with
    | tuple q1 q2 q3 =>
      simp only [AAtPat.erase, BAtPat.tuple.injEq] at he; obtain ⟨rfl, rfl, rfl⟩ := he
      simp only [checkAtPat, Bool.and_eq_true] at hc; obtain ⟨⟨hc1, hc2⟩, hc3⟩ := hc
      simp only [tysAtPat] at hnb; obtain ⟨hnb12, hnb3⟩ := NBD.app hnb; obtain ⟨hnb1, hnb2⟩ := NBD.app hnb12
      simp only [wdAtPat]
      refine outP_bindD (wPat_completeD fuel n0 _ C C' C'' S' st q1 hp hl hc1 rfl hnb1) ?_
      rintro ⟨τ1, a1⟩ st1 ⟨hn1, hi1, hok1, hty1, hokA1, T1, hF1, hs1⟩
      refine outP_bindD (wPat_completeD fuel n0 _ C C' C'' T1 st1 q2 (hp.next hi1 hn1 hF1) hl hc2 rfl hnb2) ?_
      rintro ⟨τ2, a2⟩ st2 ⟨hn2, hi2, hok2, hty2, hokA2, T2, hF2, hs2⟩
      refine outP_bindD (wPatOpt_completeD fuel n0 _ C C' C'' T2 st2 q3 ((hp.next hi1 hn1 hF1).next hi2 hn2 hF2)
        hl hc3 rfl hnb3) ?_
      rintro ⟨τ3, a3⟩ st3 ⟨hn3, hi3, hok3, hty3, hokA3, T3, hF3, hs3⟩
      refine outP_pureD ⟨by omega, hi3, OkT_tupleD ((hok1.mono (by omega))) (hok2.mono hn3) hok3, ?_, ?_,
        T3, (hF1.trans hF2 hn1).trans hF3 (by omega), ?_⟩
      · simp only [AAtPat.ty, hty1, hty2, hty3]
      · simp only [tysAtPat]
        exact ((hokA1.mono (by omega)).app (hokA2.mono hn3)).app hokA3
      · simp only [rsbAtPat, stripAtPat] at hs1 hs2 hs3 ⊢
        rw [hs3, rsbPat_congrD a2 ((hF3.agreeOn hokA2)), hs2,
          rsbPat_congrD a1 (((hF2.trans hF3 hn2).agreeOn hokA1)), hs1]
    | _ => simp [AAtPat.erase] at he
  | .paren p, C, C', C'', S', st, p', hp, hl, hc, he, hnb => by
    cases p' with
    | paren q =>
      simp only [AAtPat.erase, BAtPat.paren.injEq] at he; subst he
      simp only [checkAtPat] at hc
      simp only [tysAtPat] at hnb
      simp only [wdAtPat]
      refine outP_bindD (wPat_completeD fuel n0 _ C C' C'' S' st q hp hl hc rfl hnb) ?_
      rintro ⟨τ, a⟩ st1 ⟨hn1, hi1, hok1, hty1, hokA1, T1, hF1, hs1⟩
      exact outP_pureD ⟨hn1, hi1, hok1, hty1, hokA1, T1, hF1, by simp only [rsbAtPat, stripAtPat, hs1]⟩
    | _ => simp [AAtPat.erase] at he
theorem wPat_completeD (fuel n0 : Nat) : ∀ (p : BPat) (C C' C'' : Ctx) (S' : RSub) (st : WDSt) (p' : APat),
    PreD n0 C C' S' st → LkC C'' C' → checkPat C'' p' = true → p'.erase = p → NBD (tysPat p') →
    OutPD (PPostD n0 st S' p') (wdPat fuel (rigidFromD n0) C p st)
  | .atpat a, C, C', C'', S', st, p', hp, hl, hc, he, hnb => by
    cases p' with
    | atpat q =>
      simp only [APat.erase, BPat.atpat.injEq] at he; subst he
      simp only [checkPat] at hc
      simp only [tysPat] at hnb
      simp only [wdPat]
      refine outP_bindD (wAtPat_completeD fuel n0 _ C C' C'' S' st q hp hl hc rfl hnb) ?_
      rintro ⟨τ, a⟩ st1 ⟨hn1, hi1, hok1, hty1, hokA1, T1, hF1, hs1⟩
      exact outP_pureD ⟨hn1, hi1, hok1, hty1, hokA1, T1, hF1, by simp only [rsbPat, stripPat, hs1]⟩
    | _ => simp [APat.erase] at he
  | .con lc args, C, C', C'', S', st, p', hp, hl, hc, he, hnb => by
    cases p' with
    | con lc' inst args' τ' =>
      simp only [APat.erase, BPat.con.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      simp only [checkPat, Bool.and_eq_true] at hc
      obtain ⟨hc1, hc2⟩ := hc
      split at hc1
      · rename_i σ' hlk
        simp only [Bool.and_eq_true] at hc1
        obtain ⟨σ, hσ, hrel⟩ := hp.rel.lookup hp.fix (rigid_bndD n0) (hl _ _ hlk)
        have hgen := gen_of_genAt hc1.1
        obtain ⟨us, t, rfl⟩ := isConTy_spec hc1.2
        simp only [tysPat] at hnb; obtain ⟨-, hnbA⟩ := NBD.cons hnb
        simp only [wdPat, hσ]
        refine outP_instantiateD hp.inv (hp.ctxW _ _ _ hσ) hp.fix hp.abs (hrel.2 _ hgen) ?_
        intro ts τb st0 T0 hle0 _ hi0 hok0 _ hfx0 hab0 hag0 hcl0 hτ0
        have hF0 : FoundD n0 S' st.n st0 T0 := ⟨hfx0, hab0, hag0, hcl0⟩
        have hlen : (AAtPat.tyList args').length = (AAtPat.eraseList args').length := by
          rw [tyList_eq_map, List.length_map, eraseList_length]
        cases hpe : peel (AAtPat.eraseList args').length τb with
        | some pr =>
          obtain ⟨τs, r⟩ := pr
          obtain ⟨hl1, hl2⟩ := peel_rsbD (s := T0) _ _ _ _ hpe
          rw [hτ0] at hl2
          obtain ⟨hargs, hr⟩ := arrows_inj (by rw [rsbList_length, hl1, hlen]) hl2
          simp only
          cases r with
          | con us' t' =>
            simp only [rsb, Ty.con.injEq] at hr; obtain ⟨hus, rfl⟩ := hr
            have hokτs : ∀ x ∈ τs, OkTD st0.n x := fun x hx v hv =>
              hok0 v (by
                rw [peel_varsD _ _ _ _ hpe]
                exact arrows_vars_left hx hv)
            have hokr : OkTD st0.n (.con us' t) := fun v hv =>
              hok0 v (by
                rw [peel_varsD _ _ _ _ hpe]; exact arrows_vars_right hv)
            refine outP_bindD (wAtPats_completeD fuel n0 _ C C' C'' T0 st0 args'
              (hp.next hi0 hle0 hF0) hl hc2 rfl hnbA) ?_
            rintro ps st1 ⟨hn1, hi1, hps1, hokA1, T1, hF1, hs1⟩
            -- the argument types under T1 are those of the derivation
            have e1 : rsbList T1 (ps.map (·.1)) = AAtPat.tyList args' := by
                rw [tyList_eq_map, ← stripAtPats_tys args', ← hs1, stripAtPats_tys, rsbList_eq,
                  rsbAtPats_mapD]
                simp only [List.map_map]
                apply List.map_congr_left
                intro q hq
                simp only [Function.comp, rsbAtPat_tyD, (hps1 q hq).2]
            have htys : rsbList T1 (ps.map (·.1)) = rsbList T1 τs := by
              rw [e1, hargs, rsbList_eq, rsbList_eq]
              apply List.map_congr_left
              intro x hx
              exact (hF1.sb_eq (hokτs x hx)).symm
            simp only [bind]
            refine outP_bindD (outP_unifyArgsD (fuel := fuel) _ _ st1 T1 hi1 (fun x hx => by
                obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx; exact (hps1 q hq).1)
              (fun x hx => (hokτs x hx).mono hn1) hF1.fix ((hF0.trans hF1 hle0).resp hp.resp) hF1.abs htys
              (fun x hx => by
                have hm : rsb T1 x ∈ rsbList T1 (ps.map (·.1)) := by rw [rsbList_eq]; exact List.mem_map_of_mem hx
                rw [e1, tyList_eq_map] at hm
                obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hm
                rw [← hqe]
                exact cn_atpat_ty q fun τ hτ => hnbA.cn τ (mem_tysAtPats hq hτ))) ?_
            rintro _ st2 ⟨hn2, hi2, T2, hF2, -⟩
            refine outP_pureD ⟨by omega, hi2, (hokr.mono hn1).mono hn2, rfl,
              OkAD.cons ((hokr.mono hn1).mono hn2) (hokA1.mono hn2), T2,
              (hF0.trans hF1 hle0).trans hF2 (by omega), ?_⟩
            simp only [rsbPat, stripPat]
            rw [rsbAtPats_congrD _ (hF2.agreeOn hokA1), hF2.sb_eq (hokr.mono hn1)]
            simp only [hs1, rsb]
            congr 1
            rw [hus]
            exact congrArg (Ty.con · _) (by
              rw [rsbList_eq, rsbList_eq]; apply List.map_congr_left; intro x hx
              exact hF1.sb_eq (fun v hv => hokr v (by simp only [Ty.vars]; exact mem_listVarsR.mpr ⟨x, hx, hv⟩)))
          | var _ => simp only; trivial
          | fn _ _ => simp only [rsb] at hr; cases hr
          | record _ _ => simp only [rsb] at hr; cases hr
        | none =>
          simp only
          split
          · trivial
          · rename_i hs
            exact absurd hτ0 (peel_none_neD _ τb _ _ hpe (by simpa using hs) (by rw [hlen]))
      · cases hc1
    | _ => simp [APat.erase] at he
  | .cons p1 p2, C, C', C'', S', st, p', hp, hl, hc, he, hnb => by
    cases p' with
    | cons q1 q2 =>
      simp only [APat.erase, BPat.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      simp only [checkPat, Bool.and_eq_true, decide_eq_true_eq] at hc; obtain ⟨⟨hc1, hc2⟩, hc3⟩ := hc
      simp only [tysPat] at hnb; obtain ⟨hnb1, hnb2⟩ := NBD.app hnb
      simp only [wdPat]
      refine outP_bindD (wPat_completeD fuel n0 _ C C' C'' S' st q1 hp hl hc1 rfl hnb1) ?_
      rintro ⟨τ1, a1⟩ st1 ⟨hn1, hi1, hok1, hty1, hokA1, T1, hF1, hs1⟩
      refine outP_bindD (wPat_completeD fuel n0 _ C C' C'' T1 st1 q2 (hp.next hi1 hn1 hF1) hl hc2 rfl hnb2) ?_
      rintro ⟨τ2, a2⟩ st2 ⟨hn2, hi2, hok2, hty2, hokA2, T2, hF2, hs2⟩
      dsimp only at hok1 hty1 hokA1 hs1 hok2 hty2 hokA2 hs2
      have e1 : rsb T2 τ1 = q1.ty := by
        rw [hF2.sb_eq hok1, ← hty1, ← rsbPat_tyD, ← stripPat_ty, hs1, stripPat_ty]
      have e2 : rsb T2 τ2 = q2.ty := by rw [← hty2, ← rsbPat_tyD, ← stripPat_ty, hs2, stripPat_ty]
      simp only
      have hF12 := hF1.trans hF2 hn1
      refine outP_unifyWD hi2 hok2 (OkT_listD (hok1.mono hn2)) hF2.fix (hF12.resp hp.resp) hF2.abs
        (by rw [e2, listTy_sbD, e1, hc3]) (by rw [e2]; exact cn_pat_ty q2 hnb2.cn) fun st3 T3 hn3 hi3 ag3 fx3 r3 hab3 => ?_
      have hF3 : FoundD n0 T2 st2.n st3 T3 := FoundD.ofUnify fx3 hab3 ag3 r3
      refine outP_pureD ⟨by omega, hi3, OkT_listD ((hok1.mono hn2).mono hn3), by simp [APat.ty, hty1], ?_,
        T3, hF12.trans hF3 (by omega), ?_⟩
      · simp only [tysPat]; exact ((hokA1.mono hn2).app hokA2).mono hn3
      · simp only [rsbPat, stripPat] at hs1 hs2 ⊢
        rw [rsbPat_congrD a2 (hF3.agreeOn hokA2), rsbPat_congrD a1 (hF3.agreeOn (hokA1.mono hn2)), hs2,
          rsbPat_congrD a1 (hF2.agreeOn hokA1), hs1]
    | _ => simp [APat.erase] at he
  | .as p x, C, C', C'', S', st, p', hp, hl, hc, he, hnb => by
    cases p' with
    | as q x' =>
      simp only [APat.erase, BPat.as.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      simp only [checkPat] at hc
      simp only [tysPat] at hnb
      simp only [wdPat]
      refine outP_bindD (wPat_completeD fuel n0 _ C C' C'' S' st q hp hl hc rfl hnb) ?_
      rintro ⟨τ, a⟩ st1 ⟨hn1, hi1, hok1, hty1, hokA1, T1, hF1, hs1⟩
      exact outP_pureD ⟨hn1, hi1, hok1, hty1, hokA1, T1, hF1, by simp only [rsbPat, stripPat, hs1]⟩
    | _ => simp [APat.erase] at he
theorem wPatOpt_completeD (fuel n0 : Nat) : ∀ (p : Option BPat) (C C' C'' : Ctx) (S' : RSub) (st : WDSt)
    (p' : Option APat), PreD n0 C C' S' st → LkC C'' C' → checkPatOpt C'' p' = true → APat.eraseOpt p' = p →
    NBD (tysPatOpt p') → OutPD (POptPostD n0 st S' p') (wdPatOpt fuel (rigidFromD n0) C p st)
  | none, C, C', C'', S', st, p', hp, _, _, he, _ => by
    cases p' with
    | none =>
      simp only [wdPatOpt]
      exact outP_pureD ⟨Nat.le_refl _, hp.inv, (fun _ h => by cases h), rfl, OkAD.nil, S', FoundD.refl hp, rfl⟩
    | some _ => simp [APat.eraseOpt] at he
  | some p, C, C', C'', S', st, p', hp, hl, hc, he, hnb => by
    cases p' with
    | some q =>
      simp only [APat.eraseOpt, Option.some.injEq] at he; subst he
      simp only [checkPatOpt] at hc
      simp only [tysPatOpt] at hnb
      simp only [wdPatOpt]
      refine outP_bindD (wPat_completeD fuel n0 _ C C' C'' S' st q hp hl hc rfl hnb) ?_
      rintro ⟨τ, a⟩ st1 ⟨hn1, hi1, hok1, hty1, hokA1, T1, hF1, hs1⟩
      exact outP_pureD ⟨hn1, hi1, (fun _ h => by cases h; exact hok1), (by simp [APat.tyOpt, hty1]), hokA1, T1, hF1,
        by simp only [rsbPatOpt, stripPatOpt, hs1]⟩
    | none => simp [APat.eraseOpt] at he
theorem wAtPats_completeD (fuel n0 : Nat) : ∀ (ps : List BAtPat) (C C' C'' : Ctx) (S' : RSub) (st : WDSt)
    (ps' : List AAtPat), PreD n0 C C' S' st → LkC C'' C' → checkAtPatList C'' ps' = true →
    AAtPat.eraseList ps' = ps → NBD (tysAtPats ps') → OutPD (PsPostD n0 st S' ps') (wdAtPats fuel (rigidFromD n0) C ps st)
  | [], C, C', C'', S', st, ps', hp, _, _, he, _ => by
    cases ps' with
    | nil => simp only [wdAtPats]; exact outP_pureD ⟨Nat.le_refl _, hp.inv, (fun _ h => by cases h), OkAD.nil, S', FoundD.refl hp, rfl⟩
    | cons _ _ => simp [AAtPat.eraseList] at he
  | p :: ps, C, C', C'', S', st, ps', hp, hl, hc, he, hnb => by
    cases ps' with
    | cons q qs =>
      simp only [AAtPat.eraseList, List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      simp only [checkAtPatList, Bool.and_eq_true] at hc
      simp only [tysAtPats] at hnb; obtain ⟨hnb1, hnb2⟩ := NBD.app hnb
      simp only [wdAtPats]
      refine outP_bindD (wAtPat_completeD fuel n0 _ C C' C'' S' st q hp hl hc.1 rfl hnb1) ?_
      rintro ⟨τ, a⟩ st1 ⟨hn1, hi1, hok1, hty1, hokA1, T1, hF1, hs1⟩
      refine outP_bindD (wAtPats_completeD fuel n0 _ C C' C'' T1 st1 qs (hp.next hi1 hn1 hF1) hl hc.2 rfl hnb2) ?_
      rintro rs st2 ⟨hn2, hi2, hrs, hokA2, T2, hF2, hs2⟩
      refine outP_pureD ⟨by omega, hi2, ?_, ?_, T2, hF1.trans hF2 hn1, ?_⟩
      · intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact ⟨hok1.mono hn2, hty1⟩
        · exact hrs r hr
      · simp only [List.map_cons, tysAtPats]; exact (hokA1.mono hn2).app hokA2
      · simp only [List.map_cons, rsbAtPats, stripAtPats] at hs2 ⊢
        rw [hs2, rsbAtPat_congrD a (hF2.agreeOn hokA1), hs1]
    | nil => simp [AAtPat.eraseList] at he
end

end StandardElm.Stat.Complete
