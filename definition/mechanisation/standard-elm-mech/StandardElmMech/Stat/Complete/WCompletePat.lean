/-
  A Standard Definition of Elm? Mechanisation: the main induction L11 of plan step 11 (milestone
  (b), section 8) for patterns (L8): W does not fail on a pattern that has a derivation, and the
  derivation is an instance of what W returns (with the instance lists left out).

  The hypotheses of a call (`Pre`): W's state is good (`SInv`), W's context holds schemes W can
  hold (`CtxW`), the derivation's context `C'` is no more general than `S'` applied to W's
  (`CtxRel (SchRel S')`), and `S'` fixes the rigid variables and absorbs W's substitution. The
  conclusion (`Found`): an extension `T` of `S'` to the variables W created, still fixing the
  rigid variables and absorbing the new substitution, that maps W's phrase to the derivation's.
-/
import StandardElmMech.Stat.Complete.WUnify

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BAtPat BPat)

/-! ## Hypotheses and conclusions of a call -/

def OkA (n : Nat) (l : List Ty) : Prop := ∀ τ ∈ l, OkT n τ
def NB (l : List Ty) : Prop := ∀ τ ∈ l, ∀ v ∈ τ.vars, v.isBnd = false

theorem OkA.mono {n m : Nat} (h : n ≤ m) {l : List Ty} (hl : OkA n l) : OkA m l := fun τ hτ => (hl τ hτ).mono h
theorem OkA.app {n : Nat} {l1 l2 : List Ty} (h1 : OkA n l1) (h2 : OkA n l2) : OkA n (l1 ++ l2) := fun τ hτ => by
  rcases List.mem_append.mp hτ with h | h
  · exact h1 τ h
  · exact h2 τ h
theorem OkA.cons {n : Nat} {τ : Ty} {l : List Ty} (h1 : OkT n τ) (h2 : OkA n l) : OkA n (τ :: l) := fun x hx => by
  rcases List.mem_cons.mp hx with rfl | h
  · exact h1
  · exact h2 x h
theorem OkA.nil {n : Nat} : OkA n [] := fun _ h => by cases h

theorem NB.app {l1 l2 : List Ty} (h : NB (l1 ++ l2)) : NB l1 ∧ NB l2 :=
  ⟨fun τ hτ => h τ (List.mem_append_left _ hτ), fun τ hτ => h τ (List.mem_append_right _ hτ)⟩
theorem NB.cons {τ : Ty} {l : List Ty} (h : NB (τ :: l)) : NB [τ] ∧ NB l :=
  ⟨fun x hx => h x (by simp at hx; simp [hx]), fun x hx => h x (.tail _ hx)⟩

structure Found (n0 : Nat) (S' : FSub) (n : Nat) (st' : WSt) (T : FSub) : Prop where
  fix : FixesR (rigidFrom n0) T
  abs : Absorbs T (lk st'.θ)
  agree : ∀ a, a.isNew n = false → T a = S' a
  /-- Where `T` differs from `S'`, it maps a variable to an admissible type of its class. -/
  cls : ∀ a, T a ≠ S' a → Adm a.cls (T a)

structure Pre (n0 : Nat) (C C' : Ctx) (S' : FSub) (st : WSt) : Prop where
  inv : SInv n0 st
  ctxW : CtxW st.n C
  rel : CtxRel (SchRel S') (rigidFrom n0) C C'
  fix : FixesR (rigidFrom n0) S'
  abs : Absorbs S' (lk st.θ)
  resp : RespC S'

theorem Found.resp {n0 n : Nat} {S' T : FSub} {st : WSt} (h : Found n0 S' n st T) (hS : RespC S') : RespC T :=
  fun a => by
    by_cases e : T a = S' a
    · rw [e]; exact hS a
    · exact h.cls a e

theorem Found.refl {n0 : Nat} {C C' : Ctx} {S' : FSub} {st : WSt} (hp : Pre n0 C C' S' st) :
    Found n0 S' st.n st S' := ⟨hp.fix, hp.abs, fun _ _ => rfl, fun _ h => absurd rfl h⟩

theorem Found.trans {n0 n n1 : Nat} {S' T1 T2 : FSub} {st1 st2 : WSt} (h1 : Found n0 S' n st1 T1)
    (h2 : Found n0 T1 n1 st2 T2) (hn : n ≤ n1) : Found n0 S' n st2 T2 :=
  ⟨h2.fix, h2.abs, fun a ha => (h2.agree a (isNew_mono hn ha)).trans (h1.agree a ha), fun a ha => by
    by_cases e : T2 a = T1 a
    · rw [e] at ha ⊢; exact h1.cls a ha
    · exact h2.cls a e⟩

theorem Found.sb_eq {n0 n : Nat} {S' T : FSub} {st : WSt} (h : Found n0 S' n st T) {τ : Ty} (hτ : OkT n τ) :
    sb T τ = sb S' τ := sb_agree hτ h.agree

theorem Found.agreeOn {n0 n : Nat} {S' T : FSub} {st : WSt} (h : Found n0 S' n st T) {l : List Ty}
    (hl : OkA n l) : AgreeOn T S' l := fun τ hτ => h.sb_eq (hl τ hτ)

theorem schRel_congr {n : Nat} {σ σ' : Scheme} {S T : FSub} (hσ : SchW n σ)
    (hT : ∀ a, a.isNew n = false → T a = S a) (h : SchRel S σ σ') : SchRel T σ σ' := by
  have free : ∀ a, BVar.ty a ∈ σ.body.vars → BVar.ty a ∉ σ.bound → T a = S a := fun a ha hb => by
    obtain ⟨b, e, -, h2⟩ := hσ.2 _ ha hb; injection e with e; subst e; exact hT _ h2
  refine ⟨fun a ha v hv => ?_, fun hab τ hg => ?_⟩
  · have ha' : BVar.ty a ∈ σ.body.vars ∧ BVar.ty a ∉ σ.bound := by
      simp only [Scheme.tyvars, diffL, Ty.tyvars, List.mem_filter, Bool.not_eq_true',
        decide_eq_false_iff_not] at ha
      exact ⟨ha.1.1, ha.2⟩
    rw [free a ha'.1 ha'.2] at hv; exact h.1 a ha v hv
  · obtain ⟨g, hga, hg'⟩ := h.2 hab τ hg
    refine ⟨g, hga, hg'.trans (sb_congr _ fun a ha => ?_)⟩
    simp only [ext]
    split
    · rfl
    · rename_i hb; exact (free a ha hb).symm

theorem CtxRel.congr {n n0 : Nat} {C C' : Ctx} {S T : FSub} (h : CtxRel (SchRel S) (rigidFrom n0) C C')
    (hC : CtxW n C) (hT : ∀ a, a.isNew n = false → T a = S a) : CtxRel (SchRel T) (rigidFrom n0) C C' :=
  h.mono fun x σ st σ' hf hs => schRel_congr (hC ⟨none, x⟩ σ st (by simpa [Ctx.lookupVal, Env.lookupVal] using hf)) hT hs

theorem Pre.next {n0 : Nat} {C C' : Ctx} {S' T : FSub} {st st' : WSt} (hp : Pre n0 C C' S' st)
    (hi : SInv n0 st') (hn : st.n ≤ st'.n) (hF : Found n0 S' st.n st' T) : Pre n0 C C' T st' :=
  ⟨hi, hp.ctxW.mono hn, hp.rel.congr hp.ctxW hF.agree, hF.fix, hF.abs, hF.resp hp.resp⟩

/-- `S'` with the fresh variable `n` mapped to `τ'`. -/
def ext1 (S' : FSub) (n : Nat) (τ' : Ty) : FSub := fun c => if c = .fresh n .any then τ' else S' c

theorem found_ext1 {n0 : Nat} {C C' : Ctx} {S' : FSub} {st : WSt} (hp : Pre n0 C C' S' st) (τ' : Ty) :
    Found n0 S' st.n { st with n := st.n + 1 } (ext1 S' st.n τ') := by
  have hag : ∀ a, a.isNew st.n = false → ext1 S' st.n τ' a = S' a := fun a ha => by
    simp only [ext1]; rw [if_neg]; rintro rfl; simp [TyVar.isNew] at ha
  obtain ⟨h1, h2⟩ := agree_ok hp.inv.le hp.inv.ok hp.fix hp.abs hag
  refine ⟨h1, h2, hag, fun a ha => ?_⟩
  simp only [ext1] at ha
  split at ha
  · rename_i e; subst e; exact Adm.any _
  · exact absurd rfl ha

/-- `S'` with the fresh variable `n` of class `c` mapped to `τ'`. -/
def ext1C (S' : FSub) (n : Nat) (c : Cls) (τ' : Ty) : FSub := fun d => if d = .fresh n c then τ' else S' d

theorem found_ext1C {n0 : Nat} {C C' : Ctx} {S' : FSub} {st : WSt} (hp : Pre n0 C C' S' st) {c : Cls} {τ' : Ty}
    (hadm : Adm c τ') : Found n0 S' st.n { st with n := st.n + 1 } (ext1C S' st.n c τ') := by
  have hag : ∀ a, a.isNew st.n = false → ext1C S' st.n c τ' a = S' a := fun a ha => by
    simp only [ext1C]; rw [if_neg]; rintro rfl; simp [TyVar.isNew] at ha
  obtain ⟨h1, h2⟩ := agree_ok hp.inv.le hp.inv.ok hp.fix hp.abs hag
  refine ⟨h1, h2, hag, fun a ha => ?_⟩
  simp only [ext1C] at ha ⊢
  split at ha
  · rename_i e; subst e; rw [if_pos rfl]; exact hadm
  · exact absurd rfl ha

theorem ext1C_self (S' : FSub) (n : Nat) (c : Cls) (τ' : Ty) : ext1C S' n c τ' (.fresh n c) = τ' := by
  simp [ext1C]

theorem okT_freshC {st : WSt} {c : Cls} : OkT (st.n + 1) (.var (.fresh st.n c)) :=
  OkT_var rfl (isNew_fresh_lt (by omega))

theorem ext1_self (S' : FSub) (n : Nat) (τ' : Ty) : ext1 S' n τ' (.fresh n .any) = τ' := by simp [ext1]

theorem okT_fresh {st : WSt} : OkT (st.n + 1) (.var (.fresh st.n .any)) := OkT_var rfl (isNew_fresh_lt (by omega))

/-! ## Constants and constructors in patterns -/

theorem genAt_monoW {τ0 τ : Ty} (h : genAt (mono τ0) [] τ = true) : τ = τ0 := by
  simp only [genAt, mono, bindSubst, apply_idF, Bool.and_eq_true, decide_eq_true_eq, Option.some.injEq] at h
  exact h.2.symm

theorem scon_pat_ty {sc : StandardElm.Src.SLit} {τ : Ty} (h1 : genAt (typeOf sc) (litInst sc τ) τ = true)
    (h2 : τ ∈ [tIntTy, tCharTy, tStringTy]) :
    τ = (match sc with | .int _ => tIntTy | .char _ => tCharTy | .str _ => tStringTy | .float _ _ => tFloatTy) := by
  cases sc with
  | int k =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
    rcases h2 with rfl | rfl | rfl
    · rfl
    · exact absurd h1 (by simp only [typeOf, litInst]; decide)
    · exact absurd h1 (by simp only [typeOf, litInst]; decide)
  | char c => exact genAt_monoW h1
  | str s => exact genAt_monoW h1
  | float m e => exact genAt_monoW h1

theorem sb_con {s : FSub} {τ : Ty} {as : List Ty} {t : TyName} (h : sb s τ = .con as t) :
    (∃ us, τ = .con us t) ∨ ∃ a, τ = .var a := by
  cases τ with
  | var a => exact .inr ⟨a, rfl⟩
  | con us t' => simp only [sb, Ty.con.injEq] at h; exact .inl ⟨us, by rw [h.2]⟩
  | fn _ _ => simp [sb] at h
  | record _ _ => simp [sb] at h

theorem peel_sb {s : FSub} : ∀ (k : Nat) (τ : Ty) (τs : List Ty) (r : Ty), peel k τ = some (τs, r) →
    τs.length = k ∧ sb s τ = arrows (sbList s τs) (sb s r)
  | 0, τ, τs, r, h => by simp only [peel, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp [arrows, sbList]
  | k + 1, .fn a b, τs, r, h => by
    simp only [peel] at h
    cases hp : peel k b with
    | none => rw [hp] at h; cases h
    | some p =>
      rw [hp] at h
      obtain ⟨as, r'⟩ := p
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      obtain ⟨h1, h2⟩ := peel_sb (s := s) k b as r' hp
      simp [h1, sb, h2, arrows, sbList]
  | k + 1, .var _, _, _, h => by simp [peel] at h
  | k + 1, .con _ _, _, _, h => by simp [peel] at h
  | k + 1, .record _ _, _, _, h => by simp [peel] at h

theorem arrows_inj : ∀ {l1 l2 : List Ty} {τ1 τ2 : Ty}, l1.length = l2.length → arrows l1 τ1 = arrows l2 τ2 →
    l1 = l2 ∧ τ1 = τ2
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | a :: l1, b :: l2, _, _, hl, h => by
    simp only [arrows, Ty.fn.injEq] at h
    obtain ⟨h1, h2⟩ := arrows_inj (by simpa using hl) h.2
    exact ⟨by rw [h.1, h1], h2⟩

theorem peel_none_ne {s : FSub} : ∀ (k : Nat) (τ : Ty) (l : List Ty) (τ' : Ty), peel k τ = none →
    peelStuckVar k τ = false → l.length = k → sb s τ ≠ arrows l τ'
  | 0, _, _, _, h, _, _, _ => by simp [peel] at h
  | k + 1, .fn a b, l, τ', h, hs, hl, e => by
    simp only [peel] at h
    cases hp : peel k b with
    | some _ => rw [hp] at h; cases h
    | none =>
      cases l with
      | nil => cases hl
      | cons x l =>
        simp only [sb, arrows, Ty.fn.injEq] at e
        exact peel_none_ne k b l τ' hp (by simpa [peelStuckVar] using hs) (by simpa using hl) e.2
  | k + 1, .var _, _, _, _, hs, _, _ => by simp [peelStuckVar] at hs
  | k + 1, .con _ _, l, _, _, _, hl, e => by
    cases l with
    | nil => cases hl
    | cons _ _ => simp [sb, arrows] at e
  | k + 1, .record _ _, l, _, _, _, hl, e => by
    cases l with
    | nil => cases hl
    | cons _ _ => simp [sb, arrows] at e

theorem eraseList_length : ∀ (l : List AAtPat), (AAtPat.eraseList l).length = l.length
  | [] => rfl
  | _ :: l => by simp [AAtPat.eraseList, eraseList_length l]

theorem tyList_eq_map : ∀ (l : List AAtPat), AAtPat.tyList l = l.map AAtPat.ty
  | [] => rfl
  | a :: l => by simp [AAtPat.tyList, tyList_eq_map l]

theorem arrows_vars_left {v : BVar} {x r : Ty} : ∀ {τs : List Ty}, x ∈ τs → v ∈ x.vars → v ∈ (arrows τs r).vars
  | _ :: _, hx, hv => by
    simp only [arrows, Ty.vars, List.mem_append]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact .inl hv
    · exact .inr (arrows_vars_left hx hv)

theorem arrows_vars_right {v : BVar} {r : Ty} : ∀ {τs : List Ty}, v ∈ r.vars → v ∈ (arrows τs r).vars
  | [], hv => hv
  | _ :: _, hv => by simp only [arrows, Ty.vars, List.mem_append]; exact .inr (arrows_vars_right hv)

theorem stripAtPats_tys : ∀ l : List AAtPat, (stripAtPats l).map AAtPat.ty = l.map AAtPat.ty
  | [] => rfl
  | a :: l => by simp [stripAtPats, stripAtPat_ty, stripAtPats_tys l]

theorem sbAtPats_map (s : FSub) : ∀ l : List AAtPat, sbAtPats s l = l.map (sbAtPat s)
  | [] => rfl
  | a :: l => by simp [sbAtPats, sbAtPats_map s l]

/-- The conclusion of a `unify` step for the main induction. -/
theorem Found.ofUnify {n0 n : Nat} {T T' : FSub} {st' : WSt} (fx : FixesR (rigidFrom n0) T')
    (ab : Absorbs T' (lk st'.θ)) (ag : ∀ a, a.isNew n = false → T' a = T a) (r : RespC T') :
    Found n0 T n st' T' := ⟨fx, ab, ag, fun a _ => r a⟩

/-- `unifyArgs`: if `T` unifies the two lists, it does not fail, and a `T'` agreeing with `T` on
    the old variables absorbs the result. -/
theorem outP_unifyArgs {fuel n0 : Nat} : ∀ (l1 l2 : List Ty) (st : WSt) (T : FSub), SInv n0 st →
    (∀ x ∈ l1, OkT st.n x) → (∀ x ∈ l2, OkT st.n x) → FixesR (rigidFrom n0) T → RespC T → Absorbs T (lk st.θ) →
    sbList T l1 = sbList T l2 →
    OutP (fun _ st' => st.n ≤ st'.n ∧ SInv n0 st' ∧ ∃ T', Found n0 T st.n st' T' ∧ RespC T')
      (unifyArgs fuel (rigidFrom n0) l1 l2 st)
  | [], [], st, T, hi, _, _, hT, hr, ha, _ => ⟨Nat.le_refl _, hi, T, ⟨hT, ha, fun _ _ => rfl, fun _ h => absurd rfl h⟩, hr⟩
  | t :: l1, u :: l2, st, T, hi, h1, h2, hT, hr, ha, he => by
    simp only [sbList, List.cons.injEq] at he
    simp only [unifyArgs]
    refine outP_unifyW hi (h1 t (.head _)) (h2 u (.head _)) hT hr ha he.1 fun st' T' hn hi' ag fx r ha' => ?_
    have hF : Found n0 T st.n st' T' := Found.ofUnify fx ha' ag r
    have e2 : sbList T' l1 = sbList T' l2 := by
      rw [sbList_eq, sbList_eq, List.map_congr_left (fun x hx => hF.sb_eq (h1 x (.tail _ hx))),
        List.map_congr_left (fun x hx => hF.sb_eq (h2 x (.tail _ hx))), ← sbList_eq, ← sbList_eq]
      exact he.2
    refine outP_mono (outP_unifyArgs l1 l2 st' T' hi' (fun x hx => (h1 x (.tail _ hx)).mono hn)
      (fun x hx => (h2 x (.tail _ hx)).mono hn) fx r ha' e2) fun _ st'' ⟨e, hi'', T'', hF'', r''⟩ =>
        ⟨Nat.le_trans hn e, hi'', T'', hF.trans hF'' hn, r''⟩
  | [], _ :: _, _, _, _, _, _, _, _, _, he => by simp [sbList] at he
  | _ :: _, [], _, _, _, _, _, _, _, _, he => by simp [sbList] at he

/-! ## Patterns -/

/-- The derivation's context for a pattern finds a constructor only where `C'` does (it may add
    variables, of status v). -/
def LkC (C'' C' : Ctx) : Prop := ∀ lv σ', C''.lookupVal lv = some (σ', .c) → C'.lookupVal lv = some (σ', .c)

def APPost (n0 : Nat) (st : WSt) (S' : FSub) (p' : AAtPat) (r : Ty × AAtPat) (st' : WSt) : Prop :=
  st.n ≤ st'.n ∧ SInv n0 st' ∧ OkT st'.n r.1 ∧ r.2.ty = r.1 ∧ OkA st'.n (tysAtPat r.2) ∧
    ∃ T, Found n0 S' st.n st' T ∧ stripAtPat (sbAtPat T r.2) = stripAtPat p'

def PPost (n0 : Nat) (st : WSt) (S' : FSub) (p' : APat) (r : Ty × APat) (st' : WSt) : Prop :=
  st.n ≤ st'.n ∧ SInv n0 st' ∧ OkT st'.n r.1 ∧ r.2.ty = r.1 ∧ OkA st'.n (tysPat r.2) ∧
    ∃ T, Found n0 S' st.n st' T ∧ stripPat (sbPat T r.2) = stripPat p'

def POptPost (n0 : Nat) (st : WSt) (S' : FSub) (p' : Option APat) (r : Option Ty × Option APat) (st' : WSt) : Prop :=
  st.n ≤ st'.n ∧ SInv n0 st' ∧ (∀ τ, r.1 = some τ → OkT st'.n τ) ∧ APat.tyOpt r.2 = r.1 ∧
    OkA st'.n (tysPatOpt r.2) ∧ ∃ T, Found n0 S' st.n st' T ∧ stripPatOpt (sbPatOpt T r.2) = stripPatOpt p'

def PsPost (n0 : Nat) (st : WSt) (S' : FSub) (ps' : List AAtPat) (r : List (Ty × AAtPat)) (st' : WSt) : Prop :=
  st.n ≤ st'.n ∧ SInv n0 st' ∧ (∀ q ∈ r, OkT st'.n q.1 ∧ q.2.ty = q.1) ∧ OkA st'.n (tysAtPats (r.map (·.2))) ∧
    ∃ T, Found n0 S' st.n st' T ∧ stripAtPats (sbAtPats T (r.map (·.2))) = stripAtPats ps'

mutual
theorem wAtPat_complete (fuel n0 : Nat) : ∀ (p : BAtPat) (C C' C'' : Ctx) (S' : FSub) (st : WSt) (p' : AAtPat),
    Pre n0 C C' S' st → LkC C'' C' → checkAtPat C'' p' = true → p'.erase = p → NB (tysAtPat p') →
    OutP (APPost n0 st S' p') (wAtPat fuel (rigidFrom n0) C p st)
  | .wild, C, C', C'', S', st, p', hp, _, _, he, _ => by
    cases p' with
    | wild τ' =>
      simp only [wAtPat]
      refine outP_freshV (outP_pure ⟨Nat.le_succ _, hp.inv.fresh, okT_fresh, rfl,
        OkA.cons okT_fresh OkA.nil, ext1 S' st.n τ', found_ext1 hp τ', ?_⟩)
      simp [sbAtPat, stripAtPat, sb, ext1_self]
    | _ => simp [AAtPat.erase] at he
  | .var x, C, C', C'', S', st, p', hp, _, _, he, _ => by
    cases p' with
    | var x' τ' =>
      simp only [AAtPat.erase, BAtPat.var.injEq] at he; subst he
      simp only [wAtPat]
      refine outP_freshV (outP_pure ⟨Nat.le_succ _, hp.inv.fresh, okT_fresh, rfl,
        OkA.cons okT_fresh OkA.nil, ext1 S' st.n τ', found_ext1 hp τ', ?_⟩)
      simp [sbAtPat, stripAtPat, sb, ext1_self]
    | _ => simp [AAtPat.erase] at he
  | .scon sc, C, C', C'', S', st, p', hp, _, hc, he, _ => by
    cases p' with
    | scon sc' τ' =>
      simp only [AAtPat.erase, BAtPat.scon.injEq] at he; subst he
      simp only [checkAtPat, Bool.and_eq_true, decide_eq_true_eq] at hc
      have hty := scon_pat_ty hc.1 hc.2
      have hpost : ∀ τ0 : Ty, τ0.vars = [] → τ' = τ0 →
          APPost n0 st S' (.scon sc' τ') (τ0, .scon sc' τ0) st := fun τ0 hv e =>
        ⟨Nat.le_refl _, hp.inv, OkT_of_vars_nil hv, rfl, OkA.cons (OkT_of_vars_nil hv) OkA.nil, S',
          Found.refl hp, by
            simp only [sbAtPat, stripAtPat, e]; congr 1; exact sb_eq_self_iff.mpr (fun a ha => by rw [hv] at ha; cases ha)⟩
      cases sc' with
      | int k => simp only [wAtPat]; exact hpost _ rfl hty
      | char c => simp only [wAtPat]; exact hpost _ rfl hty
      | str s => simp only [wAtPat]; exact hpost _ rfl hty
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
        obtain ⟨σ, hσ, hrel⟩ := hp.rel.lookup hp.fix (fun _ _ => rfl) (hl _ _ hlk)
        have hgen := gen_of_genAt hc.1
        obtain ⟨us, t, rfl⟩ := isConTy_spec hc.2
        simp only [wAtPat, hσ]
        refine outP_instantiate hp.inv (hp.ctxW _ _ _ hσ) hp.fix hp.abs (fun hab => hrel.2 hab _ hgen) ?_
        intro ts τ st' T hle _ hi' hok _ hfx hab hag hcl hτ
        rcases sb_con hτ with ⟨us', rfl⟩ | ⟨a, rfl⟩
        · exact ⟨hle, hi', hok, rfl, OkA.cons hok OkA.nil, T, ⟨hfx, hab, hag, hcl⟩, by simp [sbAtPat, stripAtPat, hτ]⟩
        · trivial
      · cases hc
    | _ => simp [AAtPat.erase] at he
  | .unit, C, C', C'', S', st, p', hp, _, _, he, _ => by
    cases p' with
    | unit => simp only [wAtPat]; exact ⟨Nat.le_refl _, hp.inv, OkT_of_vars_nil rfl, rfl, OkA.nil, S', Found.refl hp, rfl⟩
    | _ => simp [AAtPat.erase] at he
  | .nil, C, C', C'', S', st, p', hp, _, hc, he, _ => by
    cases p' with
    | nil τ' =>
      simp only [checkAtPat] at hc
      obtain ⟨t, rfl⟩ := isListTy_spec hc
      simp only [wAtPat]
      refine outP_freshV (outP_pure ⟨Nat.le_succ _, hp.inv.fresh, OkT_list okT_fresh, rfl,
        OkA.cons (OkT_list okT_fresh) OkA.nil, ext1 S' st.n t, found_ext1 hp t, ?_⟩)
      simp [sbAtPat, stripAtPat, listTy_sb, sb, ext1_self]
    | _ => simp [AAtPat.erase] at he
  | .record _, C, C', C'', S', st, p', hp, _, _, he, _ => by simp only [wAtPat]; trivial
  | .tuple p1 p2 p3, C, C', C'', S', st, p', hp, hl, hc, he, hnb => by
    cases p' with
    | tuple q1 q2 q3 =>
      simp only [AAtPat.erase, BAtPat.tuple.injEq] at he; obtain ⟨rfl, rfl, rfl⟩ := he
      simp only [checkAtPat, Bool.and_eq_true] at hc; obtain ⟨⟨hc1, hc2⟩, hc3⟩ := hc
      simp only [tysAtPat] at hnb; obtain ⟨hnb12, hnb3⟩ := NB.app hnb; obtain ⟨hnb1, hnb2⟩ := NB.app hnb12
      simp only [wAtPat]
      refine outP_bind (wPat_complete fuel n0 _ C C' C'' S' st q1 hp hl hc1 rfl hnb1) ?_
      rintro ⟨τ1, a1⟩ st1 ⟨hn1, hi1, hok1, hty1, hokA1, T1, hF1, hs1⟩
      refine outP_bind (wPat_complete fuel n0 _ C C' C'' T1 st1 q2 (hp.next hi1 hn1 hF1) hl hc2 rfl hnb2) ?_
      rintro ⟨τ2, a2⟩ st2 ⟨hn2, hi2, hok2, hty2, hokA2, T2, hF2, hs2⟩
      refine outP_bind (wPatOpt_complete fuel n0 _ C C' C'' T2 st2 q3 ((hp.next hi1 hn1 hF1).next hi2 hn2 hF2)
        hl hc3 rfl hnb3) ?_
      rintro ⟨τ3, a3⟩ st3 ⟨hn3, hi3, hok3, hty3, hokA3, T3, hF3, hs3⟩
      refine outP_pure ⟨by omega, hi3, OkT_tuple ((hok1.mono (by omega))) (hok2.mono hn3) hok3, ?_, ?_,
        T3, (hF1.trans hF2 hn1).trans hF3 (by omega), ?_⟩
      · simp only [AAtPat.ty, hty1, hty2, hty3]
      · simp only [tysAtPat]
        exact ((hokA1.mono (by omega)).app (hokA2.mono hn3)).app hokA3
      · simp only [sbAtPat, stripAtPat] at hs1 hs2 hs3 ⊢
        rw [hs3, sbPat_congr a2 ((hF3.agreeOn hokA2)), hs2,
          sbPat_congr a1 (((hF2.trans hF3 hn2).agreeOn hokA1)), hs1]
    | _ => simp [AAtPat.erase] at he
  | .paren p, C, C', C'', S', st, p', hp, hl, hc, he, hnb => by
    cases p' with
    | paren q =>
      simp only [AAtPat.erase, BAtPat.paren.injEq] at he; subst he
      simp only [checkAtPat] at hc
      simp only [tysAtPat] at hnb
      simp only [wAtPat]
      refine outP_bind (wPat_complete fuel n0 _ C C' C'' S' st q hp hl hc rfl hnb) ?_
      rintro ⟨τ, a⟩ st1 ⟨hn1, hi1, hok1, hty1, hokA1, T1, hF1, hs1⟩
      exact outP_pure ⟨hn1, hi1, hok1, hty1, hokA1, T1, hF1, by simp only [sbAtPat, stripAtPat, hs1]⟩
    | _ => simp [AAtPat.erase] at he
theorem wPat_complete (fuel n0 : Nat) : ∀ (p : BPat) (C C' C'' : Ctx) (S' : FSub) (st : WSt) (p' : APat),
    Pre n0 C C' S' st → LkC C'' C' → checkPat C'' p' = true → p'.erase = p → NB (tysPat p') →
    OutP (PPost n0 st S' p') (wPat fuel (rigidFrom n0) C p st)
  | .atpat a, C, C', C'', S', st, p', hp, hl, hc, he, hnb => by
    cases p' with
    | atpat q =>
      simp only [APat.erase, BPat.atpat.injEq] at he; subst he
      simp only [checkPat] at hc
      simp only [tysPat] at hnb
      simp only [wPat]
      refine outP_bind (wAtPat_complete fuel n0 _ C C' C'' S' st q hp hl hc rfl hnb) ?_
      rintro ⟨τ, a⟩ st1 ⟨hn1, hi1, hok1, hty1, hokA1, T1, hF1, hs1⟩
      exact outP_pure ⟨hn1, hi1, hok1, hty1, hokA1, T1, hF1, by simp only [sbPat, stripPat, hs1]⟩
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
        obtain ⟨σ, hσ, hrel⟩ := hp.rel.lookup hp.fix (fun _ _ => rfl) (hl _ _ hlk)
        have hgen := gen_of_genAt hc1.1
        obtain ⟨us, t, rfl⟩ := isConTy_spec hc1.2
        simp only [tysPat] at hnb; obtain ⟨-, hnbA⟩ := NB.cons hnb
        simp only [wPat, hσ]
        refine outP_instantiate hp.inv (hp.ctxW _ _ _ hσ) hp.fix hp.abs (fun hab => hrel.2 hab _ hgen) ?_
        intro ts τb st0 T0 hle0 _ hi0 hok0 _ hfx0 hab0 hag0 hcl0 hτ0
        have hF0 : Found n0 S' st.n st0 T0 := ⟨hfx0, hab0, hag0, hcl0⟩
        have hlen : (AAtPat.tyList args').length = (AAtPat.eraseList args').length := by
          rw [tyList_eq_map, List.length_map, eraseList_length]
        cases hpe : peel (AAtPat.eraseList args').length τb with
        | some pr =>
          obtain ⟨τs, r⟩ := pr
          obtain ⟨hl1, hl2⟩ := peel_sb (s := T0) _ _ _ _ hpe
          rw [hτ0] at hl2
          obtain ⟨hargs, hr⟩ := arrows_inj (by rw [sbList_length, hl1, hlen]) hl2
          simp only
          cases r with
          | con us' t' =>
            simp only [sb, Ty.con.injEq] at hr; obtain ⟨hus, rfl⟩ := hr
            have hokτs : ∀ x ∈ τs, OkT st0.n x := fun x hx v hv =>
              hok0 v (by
                have := (peel_sb (s := idS) _ _ _ _ hpe).2
                rw [sb_id, sbList_id] at this; rw [this]
                exact arrows_vars_left hx hv)
            have hokr : OkT st0.n (.con us' t) := fun v hv =>
              hok0 v (by
                have := (peel_sb (s := idS) _ _ _ _ hpe).2
                rw [sb_id, sbList_id, sb_id] at this; rw [this]; exact arrows_vars_right hv)
            refine outP_bind (wAtPats_complete fuel n0 _ C C' C'' T0 st0 args'
              (hp.next hi0 hle0 hF0) hl hc2 rfl hnbA) ?_
            rintro ps st1 ⟨hn1, hi1, hps1, hokA1, T1, hF1, hs1⟩
            -- the argument types under T1 are those of the derivation
            have htys : sbList T1 (ps.map (·.1)) = sbList T1 τs := by
              have e1 : sbList T1 (ps.map (·.1)) = AAtPat.tyList args' := by
                rw [tyList_eq_map, ← stripAtPats_tys args', ← hs1, stripAtPats_tys, sbList_eq,
                  sbAtPats_map]
                simp only [List.map_map]
                apply List.map_congr_left
                intro q hq
                simp only [Function.comp, sbAtPat_ty, (hps1 q hq).2]
              rw [e1, hargs, sbList_eq, sbList_eq]
              apply List.map_congr_left
              intro x hx
              exact (hF1.sb_eq (hokτs x hx)).symm
            simp only [bind]
            refine outP_bind (outP_unifyArgs (fuel := fuel) _ _ st1 T1 hi1 (fun x hx => by
                obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx; exact (hps1 q hq).1)
              (fun x hx => (hokτs x hx).mono hn1) hF1.fix ((hF0.trans hF1 hle0).resp hp.resp) hF1.abs htys) ?_
            rintro _ st2 ⟨hn2, hi2, T2, hF2, -⟩
            refine outP_pure ⟨by omega, hi2, (hokr.mono hn1).mono hn2, rfl,
              OkA.cons ((hokr.mono hn1).mono hn2) (hokA1.mono hn2), T2,
              (hF0.trans hF1 hle0).trans hF2 (by omega), ?_⟩
            simp only [sbPat, stripPat]
            rw [sbAtPats_congr _ (hF2.agreeOn hokA1), hF2.sb_eq (hokr.mono hn1)]
            simp only [hs1, sb]
            congr 1
            rw [hus]
            exact congrArg (Ty.con · _) (by
              rw [sbList_eq, sbList_eq]; apply List.map_congr_left; intro x hx
              exact hF1.sb_eq (fun v hv => hokr v (by simp only [Ty.vars]; exact uStep_next.listVars_of_mem hx hv)))
          | var _ => simp only; trivial
          | fn _ _ => simp only [sb] at hr; cases hr
          | record _ _ => simp only [sb] at hr; cases hr
        | none =>
          simp only
          split
          · trivial
          · rename_i hs
            exact absurd hτ0 (peel_none_ne _ τb _ _ hpe (by simpa using hs) (by rw [hlen]))
      · cases hc1
    | _ => simp [APat.erase] at he
  | .cons p1 p2, C, C', C'', S', st, p', hp, hl, hc, he, hnb => by
    cases p' with
    | cons q1 q2 =>
      simp only [APat.erase, BPat.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      simp only [checkPat, Bool.and_eq_true, decide_eq_true_eq] at hc; obtain ⟨⟨hc1, hc2⟩, hc3⟩ := hc
      simp only [tysPat] at hnb; obtain ⟨hnb1, hnb2⟩ := NB.app hnb
      simp only [wPat]
      refine outP_bind (wPat_complete fuel n0 _ C C' C'' S' st q1 hp hl hc1 rfl hnb1) ?_
      rintro ⟨τ1, a1⟩ st1 ⟨hn1, hi1, hok1, hty1, hokA1, T1, hF1, hs1⟩
      refine outP_bind (wPat_complete fuel n0 _ C C' C'' T1 st1 q2 (hp.next hi1 hn1 hF1) hl hc2 rfl hnb2) ?_
      rintro ⟨τ2, a2⟩ st2 ⟨hn2, hi2, hok2, hty2, hokA2, T2, hF2, hs2⟩
      dsimp only at hok1 hty1 hokA1 hs1 hok2 hty2 hokA2 hs2
      have e1 : sb T2 τ1 = q1.ty := by
        rw [hF2.sb_eq hok1, ← hty1, ← sbPat_ty, ← stripPat_ty, hs1, stripPat_ty]
      have e2 : sb T2 τ2 = q2.ty := by rw [← hty2, ← sbPat_ty, ← stripPat_ty, hs2, stripPat_ty]
      simp only
      have hF12 := hF1.trans hF2 hn1
      refine outP_unifyW hi2 hok2 (OkT_list (hok1.mono hn2)) hF2.fix (hF12.resp hp.resp) hF2.abs
        (by rw [e2, listTy_sb, e1, hc3]) fun st3 T3 hn3 hi3 ag3 fx3 r3 hab3 => ?_
      have hF3 : Found n0 T2 st2.n st3 T3 := Found.ofUnify fx3 hab3 ag3 r3
      refine outP_pure ⟨by omega, hi3, OkT_list ((hok1.mono hn2).mono hn3), by simp [APat.ty, hty1], ?_,
        T3, hF12.trans hF3 (by omega), ?_⟩
      · simp only [tysPat]; exact ((hokA1.mono hn2).app hokA2).mono hn3
      · simp only [sbPat, stripPat] at hs1 hs2 ⊢
        rw [sbPat_congr a2 (hF3.agreeOn hokA2), sbPat_congr a1 (hF3.agreeOn (hokA1.mono hn2)), hs2,
          sbPat_congr a1 (hF2.agreeOn hokA1), hs1]
    | _ => simp [APat.erase] at he
  | .as p x, C, C', C'', S', st, p', hp, hl, hc, he, hnb => by
    cases p' with
    | as q x' =>
      simp only [APat.erase, BPat.as.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      simp only [checkPat] at hc
      simp only [tysPat] at hnb
      simp only [wPat]
      refine outP_bind (wPat_complete fuel n0 _ C C' C'' S' st q hp hl hc rfl hnb) ?_
      rintro ⟨τ, a⟩ st1 ⟨hn1, hi1, hok1, hty1, hokA1, T1, hF1, hs1⟩
      exact outP_pure ⟨hn1, hi1, hok1, hty1, hokA1, T1, hF1, by simp only [sbPat, stripPat, hs1]⟩
    | _ => simp [APat.erase] at he
theorem wPatOpt_complete (fuel n0 : Nat) : ∀ (p : Option BPat) (C C' C'' : Ctx) (S' : FSub) (st : WSt)
    (p' : Option APat), Pre n0 C C' S' st → LkC C'' C' → checkPatOpt C'' p' = true → APat.eraseOpt p' = p →
    NB (tysPatOpt p') → OutP (POptPost n0 st S' p') (wPatOpt fuel (rigidFrom n0) C p st)
  | none, C, C', C'', S', st, p', hp, _, _, he, _ => by
    cases p' with
    | none =>
      simp only [wPatOpt]
      exact outP_pure ⟨Nat.le_refl _, hp.inv, (fun _ h => by cases h), rfl, OkA.nil, S', Found.refl hp, rfl⟩
    | some _ => simp [APat.eraseOpt] at he
  | some p, C, C', C'', S', st, p', hp, hl, hc, he, hnb => by
    cases p' with
    | some q =>
      simp only [APat.eraseOpt, Option.some.injEq] at he; subst he
      simp only [checkPatOpt] at hc
      simp only [tysPatOpt] at hnb
      simp only [wPatOpt]
      refine outP_bind (wPat_complete fuel n0 _ C C' C'' S' st q hp hl hc rfl hnb) ?_
      rintro ⟨τ, a⟩ st1 ⟨hn1, hi1, hok1, hty1, hokA1, T1, hF1, hs1⟩
      exact outP_pure ⟨hn1, hi1, (fun _ h => by cases h; exact hok1), (by simp [APat.tyOpt, hty1]), hokA1, T1, hF1,
        by simp only [sbPatOpt, stripPatOpt, hs1]⟩
    | none => simp [APat.eraseOpt] at he
theorem wAtPats_complete (fuel n0 : Nat) : ∀ (ps : List BAtPat) (C C' C'' : Ctx) (S' : FSub) (st : WSt)
    (ps' : List AAtPat), Pre n0 C C' S' st → LkC C'' C' → checkAtPatList C'' ps' = true →
    AAtPat.eraseList ps' = ps → NB (tysAtPats ps') → OutP (PsPost n0 st S' ps') (wAtPats fuel (rigidFrom n0) C ps st)
  | [], C, C', C'', S', st, ps', hp, _, _, he, _ => by
    cases ps' with
    | nil => simp only [wAtPats]; exact outP_pure ⟨Nat.le_refl _, hp.inv, (fun _ h => by cases h), OkA.nil, S', Found.refl hp, rfl⟩
    | cons _ _ => simp [AAtPat.eraseList] at he
  | p :: ps, C, C', C'', S', st, ps', hp, hl, hc, he, hnb => by
    cases ps' with
    | cons q qs =>
      simp only [AAtPat.eraseList, List.cons.injEq] at he; obtain ⟨rfl, rfl⟩ := he
      simp only [checkAtPatList, Bool.and_eq_true] at hc
      simp only [tysAtPats] at hnb; obtain ⟨hnb1, hnb2⟩ := NB.app hnb
      simp only [wAtPats]
      refine outP_bind (wAtPat_complete fuel n0 _ C C' C'' S' st q hp hl hc.1 rfl hnb1) ?_
      rintro ⟨τ, a⟩ st1 ⟨hn1, hi1, hok1, hty1, hokA1, T1, hF1, hs1⟩
      refine outP_bind (wAtPats_complete fuel n0 _ C C' C'' T1 st1 qs (hp.next hi1 hn1 hF1) hl hc.2 rfl hnb2) ?_
      rintro rs st2 ⟨hn2, hi2, hrs, hokA2, T2, hF2, hs2⟩
      refine outP_pure ⟨by omega, hi2, ?_, ?_, T2, hF1.trans hF2 hn1, ?_⟩
      · intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact ⟨hok1.mono hn2, hty1⟩
        · exact hrs r hr
      · simp only [List.map_cons, tysAtPats]; exact (hokA1.mono hn2).app hokA2
      · simp only [List.map_cons, sbAtPats, stripAtPats] at hs2 ⊢
        rw [hs2, sbAtPat_congr a (hF2.agreeOn hokA1), hs1]
    | nil => simp [AAtPat.eraseList] at he
end

end StandardElm.Stat.Complete
