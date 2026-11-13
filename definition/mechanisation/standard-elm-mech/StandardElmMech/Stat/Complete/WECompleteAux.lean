/-
  A Standard Definition of Elm? Mechanisation: the group entries of W for F_e (milestone (e) of plan
  step 11; WDCompleteAux.lean for WE.lean's W).

  * `newU_of_canon`: a derivation's annotation that carries W's variables (`canonAnnB`) and is
    new for its type (`NewFor`, step 9's checker) has exactly W's `U'`.
  * The scheme of an annotated member, `annScheme U' τ` with `τ` over named variables: its bound
    variables are `bnd`, its body has only `bnd` and named variables (`annScheme_vars`), so every
    substitution of the induction fixes it.
  * `groupEntries_completeD`: W's entries against a derivation's members (an annotated member's
    type is the derivation's, unchanged).
  * `groupVE_relD`, `groupVE_entD`: the environment W gives a group is the derivation's, under the
    substitution found; its entries are monotypes or annotated schemes.
-/
import StandardElmMech.Stat.Complete.WEPhrase
import StandardElmMech.Stat.Complete.WDCompleteAux

namespace StandardElm.Stat.Complete
namespace WE
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BTy BAtPat BPat BValBind)

/-! ## W's explicit variables -/

theorem newU_named {CU : List BVar} {ty : BTy} : ∀ v ∈ newU CU ty, v.isNamed = true := by
  intro v hv
  obtain ⟨s, -, rfl⟩ := mem_newU0 (List.mem_filter.mp hv).1
  exact nameVar_named ty s

theorem filter_self_mem {α : Type} [DecidableEq α] (p : α → Bool) (l : List α) :
    l.filter p = l.filter (fun v => decide (v ∈ l.filter p)) :=
  List.filter_congr fun v hv => by simp [List.mem_filter, hv]

/-- W's annotations carry W's variables. -/
theorem canon_newU (CU : List BVar) (ty : BTy) : canonAnnB (some (ty, newU CU ty)) = true := by
  simp only [canonAnnB, decide_eq_true_eq]; exact filter_self_mem _ _

/-- A derivation's annotation with W's variables, new for its type, has W's `U'`. -/
theorem newU_of_canon {ty : BTy} {U' CU : List BVar} (hcan : canonAnnB (some (ty, U')) = true)
    (hnew : NewFor U' ty CU) : U' = newU CU ty := by
  simp only [canonAnnB, decide_eq_true_eq] at hcan
  rw [hcan]
  unfold newU
  apply List.filter_congr
  intro v hv
  obtain ⟨s, hs, rfl⟩ := mem_newU0 hv
  rw [name?_nameVar]
  simp only
  by_cases hU : nameVar ty s ∈ U'
  · have hsU : s ∈ namesU U' := mem_namesU.mpr ⟨_, hU, name?_nameVar ty s⟩
    have := ((hnew.2.1 s).mp hsU).2
    simp [hU, this]
  · by_cases hc : s ∈ namesU CU
    · simp [hU, hc]
    · exfalso
      obtain ⟨w, hw, hws⟩ := mem_namesU.mp ((hnew.2.1 s).mpr ⟨hs, hc⟩)
      have hw' : w ∈ newU0 ty := by
        rw [hcan] at hw; exact (List.mem_filter.mp hw).1
      obtain ⟨s', -, rfl⟩ := mem_newU0 hw'
      rw [name?_nameVar, Option.some.injEq] at hws
      subst hws
      exact hU hw

/-! ## The scheme of an annotated member -/

theorem annScheme_eq (U' : List BVar) (τ : Ty) :
    annScheme U' τ = ⟨(renumber true 0 (canonVars (U'.filter fun v => decide (v ∈ τ.vars)) τ)).2,
      rsb (renumber true 0 (canonVars (U'.filter fun v => decide (v ∈ τ.vars)) τ)).1.toR τ⟩ := by
  unfold annScheme; exact canon_eqD _ _

/-- The body of an annotated member's scheme: `bnd` variables of its bound list and variables of
    the annotation's type. -/
theorem annScheme_vars {U' : List BVar} {τ : Ty} :
    ∀ v ∈ (annScheme U' τ).body.vars, (v.isBnd = true ∧ v ∈ (annScheme U' τ).bound) ∨ v ∈ τ.vars := by
  intro v hv
  rw [annScheme_eq] at hv ⊢
  obtain ⟨c, hc, hvc⟩ := (mem_vars_rsb _ τ v).mp hv
  rw [renumber_img] at hvc
  split at hvc
  · rename_i hm
    rw [vars_vty, List.mem_singleton] at hvc; subst hvc
    exact .inl ⟨bndV_isBnd _ _, renumber_mem 0 _ c hm⟩
  · rw [vars_vty, List.mem_singleton] at hvc; subst hvc; exact .inr hc

theorem annScheme_bound {U' : List BVar} {τ : Ty} : ∀ v ∈ (annScheme U' τ).bound, v.isBnd = true := by
  intro v hv
  rw [annScheme_eq] at hv
  obtain ⟨j, hj, rfl⟩ := renumber_bound 0 _ v hv
  exact bndV_isBnd _ _

/-- An annotated member's scheme is one W can hold. -/
theorem schWD_ann {n : Nat} {U' : List BVar} {τ : Ty} (hτ : ∀ v ∈ τ.vars, v.isNamed = true) :
    SchWD n (annScheme U' τ) := by
  refine ⟨annScheme_bound, fun v hv hb => ?_⟩
  rcases annScheme_vars v hv with h | h
  · exact absurd h.2 hb
  · have := hτ v h
    rcases v with ((_ | _ | _) | (_ | _ | _)) <;> simp_all [BVar.isNamed, BVar.isBnd, newB, TyVar.isNew]

/-- Every variable of an annotated member's scheme is `bnd` or named. -/
theorem annScheme_BN {U' : List BVar} {τ : Ty} (hτ : ∀ v ∈ τ.vars, v.isNamed = true) :
    ∀ v ∈ (annScheme U' τ).body.vars, BN v = true := by
  intro v hv
  rcases annScheme_vars v hv with h | h
  · simp [BN, h.1]
  · simp [BN, hτ v h]

theorem img_BN {n0 : Nat} {S : RSub} (hS : FixR (rigidFromD n0) S) {v : BVar} (hv : BN v = true) : S.img v = vty v := by
  refine hS v ?_
  rcases v with ((_ | _ | _) | (_ | _ | _)) <;> simp_all [BN, BVar.isNamed, BVar.isBnd, rigidFromD]

theorem rsb_named {n0 : Nat} {S : RSub} (hS : FixR (rigidFromD n0) S) {τ : Ty} (hτ : ∀ v ∈ τ.vars, v.isNamed = true) :
    rsb S τ = τ := rsb_eq_self fun w hw => img_BN hS (by simp [BN, hτ w hw])

theorem rsbScheme_ann {n0 : Nat} {S : RSub} (hS : FixR (rigidFromD n0) S) {U' : List BVar} {τ : Ty}
    (hτ : ∀ v ∈ τ.vars, v.isNamed = true) : rsbScheme S (annScheme U' τ) = annScheme U' τ := by
  simp only [rsbScheme]
  rw [rsb_eq_self fun w hw => img_BN hS (annScheme_BN hτ w hw)]

theorem schRel_ann {n0 : Nat} {S : RSub} (hS : FixR (rigidFromD n0) S) {U' : List BVar} {τ : Ty}
    (hτ : ∀ v ∈ τ.vars, v.isNamed = true) : SchRelD S (annScheme U' τ) (annScheme U' τ) :=
  schRel_reflD fun w hw _ => img_BN hS (annScheme_BN hτ w hw)

/-! ## Groups -/

/-- What W knows of an entry: an annotated member's explicit variables are W's, its type is over
    named variables, explicit in the context or new. -/
def EntOK (C : Ctx) (e : Option (BTy × List BVar) × Ty) : Prop :=
  match e.1 with
  | none => True
  | some (ty, U') => U' = newU C.U ty ∧ ∀ v ∈ e.2.vars, v.isNamed = true ∧ (decide (v ∈ C.U) || decide (v ∈ U')) = true

/-- The annotations of a chain carry W's variables. -/
def AnnCanV : AValBind → Prop
  | .var _ ann _ _ rest => canonAnnB ann = true ∧ (match rest with
      | none => True
      | some vb => AnnCanV vb)
  | .pat _ _ => True

theorem annCanV_of_nbd : ∀ vb : AValBind, NBD (tysValBind false vb) → AnnCanV vb
  | .var _ ann _ _ rest, h => by
    simp only [tysValBind, List.cons_append] at h
    obtain ⟨-, h⟩ := NBD.cons h
    obtain ⟨h12, h3⟩ := NBD.app h
    obtain ⟨h1, -⟩ := NBD.app h12
    unfold AnnCanV
    refine ⟨?_, ?_⟩
    · simp only [annMark_false] at h1
      split at h1
      · assumption
      · have := (h1 _ (.head _)).1 (.row (.bnd 0)) (by simp [annSentinel, Ty.vars, Ty.rowVars])
        simp [BVar.isBnd] at this
    · cases rest with
      | none => trivial
      | some vb => exact annCanV_of_nbd vb (by simpa [tysValBindOpt] using h3)
  | .pat _ _, _ => trivial

def GEPostD (n0 : Nat) (C : Ctx) (st : WDSt) (S' : RSub) (vb' : AValBind) (es : List (Option (BTy × List BVar) × Ty))
    (st' : WDSt) : Prop :=
  st'.θ = st.θ ∧ st.n ≤ st'.n ∧ SInvD n0 st' ∧ (∀ e ∈ es, OkTD st'.n e.2 ∧ EntOK C e) ∧
    ∃ S1, FoundD n0 S' st.n st' S1 ∧ EsRelD S1 es vb'

theorem okT_named {n : Nat} {τ : Ty} (h : ∀ v ∈ τ.vars, v.isNamed = true) : OkTD n τ := fun v hv => by
  have := h v hv
  rcases v with ((_ | _ | _) | (_ | _ | _)) <;> simp_all [BVar.isNamed, BVar.isBnd, newB, TyVar.isNew]

theorem groupEntries_completeD {n0 : Nat} {C C2 : Ctx}
    (hU : C2.U = C.U) (hT : ∀ lc, C2.lookupTy lc = C.lookupTy lc) :
    ∀ (vb : BValBind) (st : WDSt) (S' : RSub) (vb' : AValBind), SInvD n0 st → FixR (rigidFromD n0) S' →
      AbsR S' st.θ → AnnChk C2 vb' → AnnCanV vb' → vb'.erase = vb →
      OutPD (GEPostD n0 C st S' vb') (groupEntriesD C vb st)
  | .pat _ _, _, _, _, _, _, _, _, _, _ => by simp only [groupEntriesD]; trivial
  | .var x ann e rest, st, S', vb', hi, hfx, hab, hck, hcan, he => by
    cases vb' with
    | var x' ann' τ' e' rest' =>
      simp only [AValBind.erase, BValBind.var.injEq] at he
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      unfold AnnChk at hck
      obtain ⟨hck1, hck2⟩ := hck
      unfold AnnCanV at hcan
      obtain ⟨hcan1, hcan2⟩ := hcan
      -- the rest of the chain, after the first entry
      have hrest : ∀ (en : Option (BTy × List BVar) × Ty) (st1 : WDSt) (S1 : RSub), st1.θ = st.θ →
          st.n ≤ st1.n → SInvD n0 st1 → OkTD st1.n en.2 → EntOK C en → FoundD n0 S' st.n st1 S1 →
          en.1 = ann' → rsb S1 en.2 = τ' →
          OutPD (GEPostD n0 C st S' (.var x' ann' τ' e' rest'))
            ((do
              let es ← match AValBind.eraseOpt rest' with
                | none => pure []
                | some vb => groupEntriesD C vb
              pure (en :: es)) st1) := by
        intro en st1 S1 hθ1 hn1 hi1 hok1 hann1 hF1 hen1 hen2
        cases rest' with
        | none =>
          simp only [AValBind.eraseOpt]
          refine outP_bindD (outP_pureD (P := fun r st' => r = [] ∧ st' = st1) ⟨rfl, rfl⟩) ?_
          rintro _ _ ⟨rfl, rfl⟩
          refine outP_pureD ⟨hθ1, hn1, hi1, ?_, S1, hF1, hen1, hen2, rfl⟩
          intro e he; simp only [List.mem_singleton] at he; subst he; exact ⟨hok1, hann1⟩
        | some vb =>
          simp only [AValBind.eraseOpt]
          refine outP_bindD (groupEntries_completeD hU hT _ st1 S1 vb hi1 hF1.fix hF1.abs hck2 hcan2 rfl) ?_
          rintro es st2 ⟨hθ2, hn2, hi2, hes, S2, hF2, hrel⟩
          refine outP_pureD ⟨hθ2.trans hθ1, by omega, hi2, ?_, S2, hF1.trans hF2 hn1, hen1, ?_, hrel⟩
          · intro e he
            rcases List.mem_cons.mp he with rfl | he
            · exact ⟨hok1.mono hn2, hann1⟩
            · exact hes e he
          · rw [hF2.sb_eq hok1, hen2]
      cases ann' with
      | none =>
        simp only [groupEntriesD, Option.map_none]
        refine outP_freshVD ?_
        refine outP_bindD (Q := fun r st' => r = ((none : Option (BTy × List BVar)), Ty.var (.fresh st.n .any)) ∧
          st' = { st with n := st.n + 1 }) (outP_pureD ⟨rfl, rfl⟩) ?_
        rintro _ _ ⟨rfl, rfl⟩
        exact hrest _ _ _ rfl (Nat.le_succ _) hi.fresh okT_freshD trivial (found_ext1CD' hi hfx hab (Adm.any τ')) rfl
          (by simp [rsb, ext1CD])
      | some p =>
        obtain ⟨ty, U'⟩ := p
        simp only [groupEntriesD, Option.map_some]
        simp only [checkAnn, Bool.and_eq_true, decide_eq_true_eq] at hck1
        obtain ⟨⟨hnew, hel⟩, -⟩ := hck1
        have hnew' := newFor_of_newForB hnew
        rw [hU] at hnew'
        have hU' : U' = newU C.U ty := newU_of_canon hcan1 hnew'
        subst hU'
        split
        · have hel' : elabTy (C.plusU (newU C.U ty)) ty = some τ' := by
            rw [← hel, elabTy_congrW (C1 := C.plusU (newU C.U ty)) (C2 := C2.plusU (newU C.U ty))]
            · simp [Ctx.plusU, hU]
            · intro lc; exact (hT lc).symm
          rw [hel']
          simp only
          split
          · rename_i hv
            simp only [List.all_eq_true, Bool.and_eq_true] at hv
            have hnam : ∀ v ∈ τ'.vars, v.isNamed = true := fun v hv' => (hv v hv').1
            refine outP_bindD (outP_pureD (P := fun r st' => r = (some (ty, newU C.U ty), τ') ∧ st' = st) ⟨rfl, rfl⟩) ?_
            rintro _ _ ⟨rfl, rfl⟩
            exact hrest _ _ _ rfl (Nat.le_refl _) hi (okT_named hnam) ⟨rfl, fun v hv' => hv v hv'⟩
              ⟨hfx, hab, fun _ _ => rfl, fun _ h => absurd rfl h⟩ rfl (rsb_named hfx hnam)
          · simp only [bind, WDM.bind, wdUnsupported]; trivial
        · simp only [bind, WDM.bind, wdUnsupported]; trivial
    | pat _ _ => simp [AValBind.erase] at he

theorem entOK_named {C : Ctx} {e : Option (BTy × List BVar) × Ty} (h : EntOK C e) (hs : e.1.isSome = true) :
    ∀ v ∈ e.2.vars, v.isNamed = true := by
  obtain ⟨a, τ⟩ := e
  cases a with
  | none => cases hs
  | some p => obtain ⟨ty, U'⟩ := p; exact fun v hv => (h.2 v hv).1

/-- The value environment W gives a group, mapped by `S`, is the derivation's. -/
theorem groupVE_relD {n0 : Nat} {C : Ctx} {S : RSub} (hS : FixR (rigidFromD n0) S) :
    ∀ (vb : BValBind) (es : List (Option (BTy × List BVar) × Ty)) (vb' : AValBind),
    EsRelD S es vb' → vb'.erase = vb → (∀ e ∈ es, EntOK C e) → rsbVE S (groupVE vb es) = vb'.ve
  | .var x ann e rest, (an, τ) :: es, .var x' ann' τ' e' rest', h, he, hann => by
    simp only [AValBind.erase, BValBind.var.injEq] at he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := he
    unfold EsRelD at h
    obtain ⟨rfl, h2, h3⟩ := h
    have ha : EntOK C (an, τ) := hann _ (.head _)
    unfold groupVE AValBind.ve
    rw [rsbVE_modifyD]
    congr 1
    · simp only [rsbVE, List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq, and_true, true_and]
      split
      · rename_i hs
        have hn := entOK_named ha hs
        rw [← h2, rsb_named hS hn, rsbScheme_ann hS hn]
      · rw [← h2]; simp [rsbScheme, mono]
    · cases rest' with
      | none => simp only [AValBind.eraseOpt]; rfl
      | some vb =>
        simp only [AValBind.eraseOpt]
        exact groupVE_relD hS _ es vb h3 rfl (fun e he => hann e (.tail _ he))
  | .var _ _ _ _, [], _, h, _, _ => by cases ‹AValBind› <;> simp [EsRelD] at h
  | .var _ _ _ _, _ :: _, .pat _ _, h, _, _ => by simp [EsRelD] at h
  | .pat _ _, _, vb', h, he, _ => by
    cases vb' with
    | var => simp [AValBind.erase] at he
    | pat => cases ‹List _› <;> simp [EsRelD] at h

/-- The entries of a group's environment: monotypes of unannotated members, the schemes of
    annotated ones. -/
theorem groupVE_entD {C : Ctx} : ∀ (vb : BValBind) (es : List (Option (BTy × List BVar) × Ty)), (∀ e ∈ es, EntOK C e) →
    ∀ q ∈ groupVE vb es, q.2.2 = .v ∧ ∃ e ∈ es,
      (e.1 = none ∧ q.2.1 = mono e.2) ∨ (e.1.isSome = true ∧ q.2.1 = annScheme (annU e.1) e.2)
  | .var x ann e rest, (an, τ) :: es, hann, q, hq => by
    unfold groupVE at hq
    rcases mem_modify hq with hq | hq
    · simp only [List.mem_singleton] at hq; subst hq
      refine ⟨rfl, (an, τ), .head _, ?_⟩
      cases an with
      | none => exact .inl ⟨rfl, by simp⟩
      | some p => exact .inr ⟨rfl, by simp⟩
    · cases rest with
      | none => cases hq
      | some vb =>
        obtain ⟨h1, e', he', h3⟩ := groupVE_entD vb es (fun e he => hann e (.tail _ he)) q hq
        exact ⟨h1, e', .tail _ he', h3⟩
  | .var _ _ _ _, [], _, q, hq => by simp [groupVE] at hq
  | .pat _ _, _, _, q, hq => by simp [groupVE] at hq

/-! ## The closure of an annotated member (A93) -/

/-- A scheme of an annotated member in a context: bound variables `bnd`, every `bnd` variable of
    the body bound, every other variable of the body named and explicit in the context. -/
def AnnSchC (C : Ctx) (σ : Scheme) : Prop :=
  (∀ v ∈ σ.bound, v.isBnd = true) ∧ (∀ v ∈ σ.body.vars, v.isBnd = true → v ∈ σ.bound) ∧
    ∀ v ∈ σ.body.vars, v.isBnd = false → v.isNamed = true ∧ v ∈ C.U

theorem annSchC_ann {C : Ctx} {e : Option (BTy × List BVar) × Ty} (h : EntOK C e) (hs : e.1.isSome = true) :
    AnnSchC C (annScheme (annU e.1) e.2) := by
  obtain ⟨a, τ⟩ := e
  cases a with
  | none => cases hs
  | some p =>
    obtain ⟨ty, U'⟩ := p
    obtain ⟨-, hτ⟩ := h
    simp only [annU] at hτ ⊢
    refine ⟨annScheme_bound, fun v hv hb => ?_, fun v hv hb => ?_⟩
    · rcases annScheme_vars v hv with h | h
      · exact h.2
      · have := (hτ v h).1
        rcases v with ((_ | _ | _) | (_ | _ | _)) <;> simp_all [BVar.isNamed, BVar.isBnd]
    · rw [annScheme_eq] at hv
      obtain ⟨c, hc, hvc⟩ := (mem_vars_rsb _ τ v).mp hv
      rw [renumber_img] at hvc
      split at hvc
      · rw [vars_vty, List.mem_singleton] at hvc; subst hvc; rw [bndV_isBnd] at hb; cases hb
      · rename_i hm
        rw [vars_vty, List.mem_singleton] at hvc; subst hvc
        obtain ⟨h1, h2⟩ := hτ v hc
        refine ⟨h1, ?_⟩
        simp only [Bool.or_eq_true, decide_eq_true_eq] at h2
        rcases h2 with h2 | h2
        · exact h2
        · exfalso; apply hm
          rw [mem_canonVars_iff hc]
          exact List.mem_filter.mpr ⟨h2, by simp [hc]⟩

theorem closB_not_memAnn {A : List BVar} {VE : ValEnv} {σ : Scheme} {v : BVar} (hv : v ∈ A) (hb : v ∉ σ.bound) :
    v ∉ closB A VE σ := by
  simp only [closB, List.mem_append, diffL, List.mem_filter, mem_dedupL, decide_eq_false_iff_not, Bool.not_eq_true',
    not_or, not_and, decide_eq_true_eq]
  exact ⟨⟨hb, fun _ h => h hv⟩, fun h => absurd hv h.2.2⟩

theorem mem_closB_bound {A : List BVar} {VE : ValEnv} {σ : Scheme} {v : BVar} (h : v ∈ σ.bound) : v ∈ closB A VE σ := by
  simp only [closB, List.mem_append]; exact .inl (.inl h)

/-- The closures W and the derivation give an annotated member: every instance of the
    derivation's is one of W's (the extra `num` variables of A93 are vacuous on both sides). -/
theorem closE_relAnn {A A' : List BVar} {VE VE' : ValEnv} {σ : Scheme} {T : RSub} (hTadm : RespR T)
    (hb : ∀ v ∈ σ.bound, v.isBnd = true) (hbody : ∀ v ∈ σ.body.vars, v.isBnd = true → v ∈ σ.bound)
    (hfix : ∀ v ∈ σ.body.vars, v.isBnd = false → T.img v = vty v ∧ v ∈ A ∧ v ∈ A') :
    SchRelD T (closE A VE σ) (closE A' VE' σ) := by
  unfold closE
  rw [canon_eqD, canon_eqD]
  generalize hcv0 : canonVars (closB A VE σ) σ.body = cv0
  generalize hcv1 : canonVars (closB A' VE' σ) σ.body = cv1
  have hR0 := renumber_img 0 cv0
  have hR1 := renumber_img 0 cv1
  have nb : ∀ c ∈ σ.body.vars, c.isBnd = false → c ∉ cv0 ∧ c ∉ cv1 := by
    intro c hc hcb
    have hcs : c ∉ σ.bound := fun h => by rw [hb c h] at hcb; cases hcb
    obtain ⟨-, h0, h1⟩ := hfix c hc hcb
    refine ⟨fun hm => ?_, fun hm => ?_⟩
    · rw [← hcv0] at hm; exact closB_not_memAnn h0 hcs (mem_canonVars hm)
    · rw [← hcv1] at hm; exact closB_not_memAnn h1 hcs (mem_canonVars hm)
  have bd : ∀ c ∈ σ.body.vars, c.isBnd = true → c ∈ cv0 := by
    intro c hc hcb
    rw [← hcv0, mem_canonVars_iff hc]; exact mem_closB_bound (hbody c hc hcb)
  refine ⟨?_, ?_⟩
  · -- FtvRelD
    intro w hw v hv
    simp only [Scheme.tyvars, diffL, List.mem_filter, mem_tyvars_iff, Bool.not_eq_true',
      decide_eq_false_iff_not] at hw ⊢
    obtain ⟨⟨hw1, hw2⟩, -⟩ := hw
    obtain ⟨c, hc, hwc⟩ := (mem_vars_rsb _ _ w).mp hw1
    rw [hR0] at hwc
    split at hwc
    · rw [vars_vty, List.mem_singleton] at hwc; subst hwc; rw [bndV_isBnd] at hw2; cases hw2
    · rw [vars_vty, List.mem_singleton] at hwc; subst hwc
      obtain ⟨hT, -, -⟩ := hfix w hc hw2
      obtain ⟨hv1, hv2⟩ := mem_tyvars_iff.mp hv
      rw [hT, vars_vty, List.mem_singleton] at hv1; subst hv1
      refine ⟨⟨(mem_vars_rsb _ _ v).mpr ⟨v, hc, ?_⟩, hv2⟩, ?_⟩
      · rw [hR1, if_neg (nb v hc hv2).2, vars_vty]; exact List.mem_singleton_self _
      · intro hb'
        obtain ⟨j, hj, hx⟩ := renumber_bound 0 cv1 v hb'
        rw [hx, bndV_isBnd] at hv2; cases hv2
  · intro t hg
    obtain ⟨g2, hr2, hout2, rfl⟩ := gen_rsb hg
    simp only at hout2 ⊢
    have hRN1 : RespR (renumber true 0 cv1).1.toR := respR_toR (renumber_respectsC 0 cv1)
    let h : RSub := rcomp g2 (renumber true 0 cv1).1.toR
    have hh : RespR h := respR_rcomp hRN1 hr2
    have hpost : ∀ c ∈ σ.body.vars, c.isBnd = false → h.img c = vty c := by
      intro c hc hcb
      simp only [h, img_rcomp]
      rw [hR1, if_neg (nb c hc hcb).2, rsb_vty]
      exact hout2 c fun hb' => by
        obtain ⟨j, hj, hx⟩ := renumber_bound 0 cv1 c hb'
        rw [hx, bndV_isBnd] at hcb; cases hcb
    let f : BVar → Ty := fun b => match pickB cv0 b with
      | some v => h.img v
      | none => vty b
    have hf : ∀ e, ∃ ρ tl, f (.row e) = .record ρ tl := fun e => by
      simp only [f]; split
      · rename_i v hv
        cases v with
        | row e' => exact img_row_record h e'
        | ty a =>
          exfalso
          rcases e with (_ | _ | j) <;> simp only [pickB, reduceCtorEq] at hv
          split at hv <;> cases hv
      · exact ⟨[], some e, rfl⟩
    have hT : ∀ w, (ofImg f).img w = f w := ofImg_img hf
    refine ⟨ofImg f, fun a ha => ?_, ?_⟩
    · obtain ⟨v, hv, hp, hk, hk'⟩ := pickB_bound ha
      show Adm a.cls (f (.ty a))
      simp only [f, hp]
      cases v with
      | ty b =>
        obtain ⟨j, hj⟩ := hk b rfl
        injection hj with hj; subst hj
        exact hh b
      | row e => obtain ⟨j, hj⟩ := hk' e rfl; cases hj
    · rw [rsb_rsb, rsb_rsb]
      apply rsb_congr
      intro c hc
      simp only [img_rcomp]
      rw [hR0]
      split
      · rename_i hm
        rw [rsb_vty, extS_img, if_pos (renumber_mem 0 cv0 c hm), hT]
        simp only [f, pickB_inst hm, h, img_rcomp]
      · rename_i hm
        have hcb : c.isBnd = false := by
          cases e : c.isBnd
          · rfl
          · exact absurd (bd c hc e) hm
        rw [rsb_vty, extS_img, if_neg, (hfix c hc hcb).1]
        · have := hpost c hc hcb; simp only [h, img_rcomp] at this; exact this
        · intro hb'
          obtain ⟨j, hj, hx⟩ := renumber_bound 0 cv0 c hb'
          rw [hx, bndV_isBnd] at hcb; cases hcb

/-- The closure of an annotated member is a scheme W can hold. -/
theorem closE_schWDAnn {A : List BVar} {VE : ValEnv} {σ : Scheme} {n : Nat}
    (hb : ∀ v ∈ σ.bound, v.isBnd = true) (hbody : ∀ v ∈ σ.body.vars, v.isBnd = true → v ∈ σ.bound)
    (hnam : ∀ v ∈ σ.body.vars, v.isBnd = false → newB n v = false) :
    SchWD n (closE A VE σ) := by
  unfold closE
  rw [canon_eqD]
  refine ⟨fun v hv => by obtain ⟨j, hj, hx⟩ := renumber_bound 0 _ v hv; rw [hx]; exact bndV_isBnd _ _, fun v hv hvb => ?_⟩
  obtain ⟨c, hc, hv'⟩ := (mem_vars_rsb _ _ v).mp hv
  rw [renumber_img] at hv'
  split at hv'
  · rename_i hm
    rw [vars_vty, List.mem_singleton] at hv'; subst hv'
    exact absurd (renumber_mem 0 _ c hm) hvb
  · rename_i hm
    rw [vars_vty, List.mem_singleton] at hv'; subst hv'
    have hcb : v.isBnd = false := by
      cases e : v.isBnd
      · rfl
      · exact absurd ((mem_canonVars_iff hc).mpr (mem_closB_bound (hbody v hc e))) hm
    exact ⟨hcb, hnam v hc hcb⟩

/-- The context of a `let` body in W, against the derivation's: the group's entries are
    monotypes or annotated members' schemes. -/
theorem let_preD {n0 : Nat} {C C' : Ctx} {S' T1 : RSub} {st st1 : WDSt} {VE0 VE' : ValEnv}
    (hp : PreD n0 C C' S' st) (hn : st.n ≤ st1.n) (hi1 : SInvD n0 st1) (hF : FoundD n0 S' st.n st1 T1)
    (hVE0 : ∀ q ∈ VE0, (q.2.1.bound = [] ∧ OkTD st1.n q.2.1.body ∧ NBτ (rsb T1 q.2.1.body)) ∨ AnnSchC C q.2.1)
    (hVE' : VE' = rsbVE T1 VE0) :
    PreD n0 (C.plusVE (closGroup (ctxRsb (toRS st1.θ) C).tyvars (rsbVE (toRS st1.θ) VE0)))
      (C'.plusVE (closGroup C'.tyvars VE')) T1 st1 := by
  have hC1 : CtxWD st1.n C := hp.ctxW.mono hn
  have hrel1 := hp.rel.congr hp.ctxW hF.agree
  have hmono : ∀ σ : Scheme, σ.bound = [] → σ = mono σ.body := fun σ h => by cases σ; simp_all [mono]
  have hfixN : ∀ (s : RSub), FixR (rigidFromD n0) s → ∀ σ : Scheme, AnnSchC C σ → rsbScheme s σ = σ := by
    intro s hs σ ha
    simp only [rsbScheme]
    rw [rsb_eq_self fun w hw => ?_]
    refine img_BN hs ?_
    cases e : w.isBnd
    · simp [BN, (ha.2.2 w hw e).1]
    · simp [BN, e]
  have hθfix : FixR (rigidFromD n0) (toRS st1.θ) := fun v hv => goodR_fix hi1.good hv
  have hUA : ∀ v, v ∈ C.U → v ∈ (ctxRsb (toRS st1.θ) C).tyvars ∧ v ∈ C'.tyvars := fun v hv =>
    ⟨mem_ctx_tyvars.mpr (.inl (by simp [restTv, ctxRsb, hv])),
     mem_ctx_tyvars.mpr (.inl (by simp [restTv, ← hp.rel.2.1, hv]))⟩
  refine ⟨hi1, hC1.plusVE fun q hq => ?_, hrel1.plusVE fun x => ?_, hF.fix, hF.abs, hF.resp hp.resp⟩
  · -- the closures are schemes W can hold
    simp only [closGroup_eq, FMap.mapV, List.mem_map] at hq
    obtain ⟨r, hr, rfl⟩ := hq
    simp only [rsbVE, List.mem_map] at hr
    obtain ⟨p, hp', rfl⟩ := hr
    rcases hVE0 p hp' with ⟨hb, hok, hnb⟩ | ha
    · simp only
      rw [hmono p.2.1 hb]
      exact closE_schWD (okT_theta hi1 hok hF.fix hF.abs hnb)
    · simp only
      rw [hfixN _ hθfix _ ha]
      exact closE_schWDAnn ha.1 ha.2.1 fun v hv hvb => by
        have := (ha.2.2 v hv hvb).1
        rcases v with ((_ | _ | _) | (_ | _ | _)) <;> simp_all [BVar.isNamed, BVar.isBnd, newB, TyVar.isNew]
  · rw [find?_closGroup, find?_closGroup, find?_rsbVE, hVE', find?_rsbVE]
    cases hf : FMap.find? VE0 x with
    | none => trivial
    | some p =>
      refine ⟨rfl, ?_⟩
      rcases hVE0 _ (find?_mem hf) with ⟨hb, hok, hnb⟩ | ha
      · simp only
        rw [hmono p.1 hb]
        simp only [rsbScheme_monoD]
        rw [show rsb T1 p.1.body = rsb T1 (rsb (toRS st1.θ) p.1.body) from (absorbs_compD hF.abs _).symm]
        refine closE_relD (okT_theta hi1 hok hF.fix hF.abs hnb) (hF.resp hp.resp)
          (fun w hw _ => ctxSb_ftvD hrel1 hC1 hF.fix hF.abs hi1.good w hw) ?_
        rw [absorbs_compD hF.abs]; exact hnb
      · simp only
        rw [hfixN _ hθfix _ ha, hfixN _ hF.fix _ ha]
        refine closE_relAnn (hF.resp hp.resp) ha.1 ha.2.1 fun v hv hvb => ?_
        obtain ⟨h1, h2⟩ := ha.2.2 v hv hvb
        exact ⟨img_BN hF.fix (by simp [BN, h1]), hUA v h2⟩

/-! ## Contexts of a group's members -/

/-- A member's body is inferred with its explicit variables added to `U` on both sides. -/
theorem PreD.plusUE {n0 : Nat} {C C' : Ctx} {S' : RSub} {st : WDSt} (hp : PreD n0 C C' S' st) {U' : List BVar}
    (hU' : ∀ v ∈ U', v.isNamed = true) : PreD n0 (C.plusU U') (C'.plusU U') S' st := by
  obtain ⟨hi, hw, ⟨h1, h2, h3, h4, h5, h6⟩, hfx, hab, hr⟩ := hp
  refine ⟨hi, fun lv σ st h => hw lv σ st h, ⟨h1, by simp [Ctx.plusU, h2], h3, h4, h5, fun v hv => ?_⟩, hfx, hab, hr⟩
  simp only [restTv, Ctx.plusU, List.mem_append, unionL, diffL, List.mem_filter] at hv
  rcases hv with (h | h) | (h | ⟨h, -⟩)
  · exact h6 v (by simp [restTv, h])
  · exact h6 v (by simp [restTv, h])
  · exact h6 v (by simp [restTv, h])
  · have := hU' v h
    rcases v with ((_ | _ | _) | (_ | _ | _)) <;> simp_all [BVar.isNamed, rigidFromD]

theorem VEMatch_entD {s : RSub} {VE : ValEnv} (h : ∀ q ∈ VE, SchRelD s q.2.1 (rsbScheme s q.2.1)) :
    VEMatch (SchRelD s) VE (rsbVE s VE) := by
  intro x
  rw [find?_rsbVE]
  cases hf : FMap.find? VE x with
  | none => trivial
  | some p => exact ⟨rfl, h _ (find?_mem hf)⟩

theorem okAD_schTys_ann {n : Nat} {U' : List BVar} {τ : Ty} (hτ : ∀ v ∈ τ.vars, v.isNamed = true) :
    OkAD n (schTys (annScheme U' τ)) := by
  unfold schTys
  split
  · rename_i hb
    intro t ht
    simp only [List.mem_singleton] at ht; subst ht
    intro v hv
    rcases annScheme_vars v hv with h | h
    · rw [hb] at h; cases h.2
    · exact okT_named hτ v (by simpa using h)
  · intro t ht
    simp only [List.mem_map, List.mem_filter, Bool.not_eq_true'] at ht
    obtain ⟨v, ⟨hv, hbn⟩, rfl⟩ := ht
    rw [annScheme_BN hτ v hv] at hbn; cases hbn

theorem canon_of_entOK {C : Ctx} {e : Option (BTy × List BVar) × Ty} (h : EntOK C e) : canonAnnB e.1 = true := by
  obtain ⟨a, τ⟩ := e
  cases a with
  | none => rfl
  | some p => obtain ⟨ty, U'⟩ := p; obtain ⟨rfl, -⟩ := h; exact canon_newU _ _

theorem annU_named_of_entOK {C : Ctx} {e : Option (BTy × List BVar) × Ty} (h : EntOK C e) :
    ∀ v ∈ annU e.1, v.isNamed = true := by
  obtain ⟨a, τ⟩ := e
  cases a with
  | none => intro v hv; cases hv
  | some p => obtain ⟨ty, U'⟩ := p; obtain ⟨rfl, -⟩ := h; exact newU_named

/-- A member's annotation, checked in the derivation. -/
theorem annChk_mem {S : RSub} {C : Ctx} : ∀ (es : List (Option (BTy × List BVar) × Ty)) (vb' : AValBind),
    EsRelD S es vb' → AnnChk C vb' → ∀ e ∈ es, ∃ τ, checkAnn C e.1 τ = true
  | (ann, τ) :: es, .var _ ann' τ' _ rest, h, hc, e, he => by
    obtain ⟨rfl, -, h3⟩ := h
    unfold AnnChk at hc
    obtain ⟨hc1, hc2⟩ := hc
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨τ', hc1⟩
    · cases rest with
      | none => simp only at h3; subst h3; cases he
      | some vb => exact annChk_mem es vb h3 hc2 e he
  | [], _, _, _, _, he => by cases he
  | _ :: _, .pat _ _, h, _, _, _ => by simp [EsRelD] at h

end WE

end StandardElm.Stat.Complete
