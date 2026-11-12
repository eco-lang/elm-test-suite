/-
  A Standard Definition of Elm? Mechanisation: completeness of `coreGen` for derivations and the
  refusal theorem of milestone (a), plan step 11 ("Theorems", "Constraint generation").

  `coreGen_complete`: every derivation of the module (an annotated module that `checkModule`
  accepts) solves the constraints `coreGen` generates, under the valuation read off it (`rdTop`).
  With `unifyCs_fail` (Unify.lean): when unification fails, the first module has no derivation, so
  the program is not legal (`not_legal_of_coreRefutes`, through Refusals.lean's
  `not_legal_of_noDeriv`). No principality hypothesis is involved.

  Type declarations: a local constructor (of a custom type, or of a record alias) has in every
  derivation the closure of the type its declaration elaborates to, which the abstract context
  elaborates up to the collapse of type names (`gDat_rel`, `aliases_rel`); its template describes
  every instance (CoreTmpl.lean). When a local type has the name of an imported one, the imports'
  context agrees with the abstract one except at the local names (`InvW`), which only the type
  declarations at the head of the body read (`gTop_shadow`); after them the agreement is full.
-/
import StandardElmMech.Stat.Complete.CoreExp

namespace StandardElm.Stat.Complete
open StandardElm (Var Lab ModId Op LongId)
open StandardElm.Stat
open StandardElm.Src (BModule)

variable {ν : Val}

theorem RelL.append_modify {L1 L2 : FMap Var GInfo} {V1 V2 : ValEnv} (h1 : RelL ν L1 V1) (h2 : RelL ν L2 V2) :
    RelL ν (L2 ++ L1) (FMap.modify V1 V2) := by
  intro x
  rw [FMap.find?_append, FMap.find?_modify]
  exact RelOpt.or (h2 x) (h1 x)

/-! ## Keys -/

theorem mem_keys_modify {K V : Type} [DecidableEq K] {f g : FMap K V} {x : K} (h : x ∈ (FMap.modify f g).keys) :
    x ∈ f.keys ∨ x ∈ g.keys := by
  unfold FMap.modify FMap.keys at h
  simp only [List.map_append, List.mem_append] at h
  rcases h with h | h
  · exact .inr h
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
    exact .inl (List.mem_map.mpr ⟨p, (List.mem_filter.mp hp).1, rfl⟩)

theorem mem_keys_plusAll {K V : Type} [DecidableEq K] {x : K} : ∀ (Ls : List (FMap K V)) (acc : FMap K V),
    x ∈ (Ls.foldl FMap.modify acc).keys → x ∈ acc.keys ∨ ∃ L ∈ Ls, x ∈ L.keys
  | [], _, h => .inl h
  | L :: Ls, acc, h => by
    rcases mem_keys_plusAll Ls (FMap.modify acc L) h with h | ⟨L', hL', h⟩
    · rcases mem_keys_modify h with h | h
      · exact .inl h
      · exact .inr ⟨L, List.mem_cons_self, h⟩
    · exact .inr ⟨L', List.mem_cons_of_mem _ hL', h⟩

/-! ## Local constructors -/

theorem mapTy_arrows (f : TyName → TyName) (τ : Ty) : ∀ τs : List Ty,
    RTypes.mapTy f (arrows τs τ) = arrows (RTypes.mapTys f τs) (RTypes.mapTy f τ)
  | [] => rfl
  | a :: as => by simp only [arrows, RTypes.mapTy, RTypes.mapTys, mapTy_arrows f τ as]

theorem closVE_modify (X : List BVar) (a b : ValEnv) :
    closVE X (FMap.modify a b) = FMap.modify (closVE X a) (closVE X b) := by
  simp only [closVE, FMap.mapV, FMap.modify, List.map_append, FMap.keys, List.map_map]
  congr 1
  rw [List.filter_map]
  congr 1

theorem gok_con {f : TyName → TyName} (hg : ∀ t, gN (f t) = gN t) (X : List BVar) (B : Ty) :
    GOK ν (conInfo (RTypes.mapTy f B)) (closScheme X (mono B)) := by
  unfold conInfo
  rw [goodTmpl_mapTy, hN_mapTy hg]
  split
  · rename_i hgood
    exact gok_tmpl (instOf_canon _ B) hgood
  · trivial

section cons
variable {f : TyName → TyName} (hfix : RTypes.FixesBuiltins f) (hg : ∀ t, gN (f t) = gN t)
include hfix hg

theorem gConBind_rel {C' A' : Ctx} (hL : ∀ lc, RTypes.LookSim f C' A' lc) (hU : RTypes.UEq C'.U A'.U)
    (X : List BVar) (τ : Ty) : ∀ (cb : Src.BConBind) (VEc : ValEnv), elabConBind C' τ cb = some VEc →
    RelL ν (gConBind A' (some (RTypes.mapTy f τ)) cb) (closVE X VEc)
  | [], VEc, h => by
    simp only [elabConBind, Option.some.injEq] at h
    subst h
    exact RelL.nil
  | (k, tys) :: rest, VEc, h => by
    simp only [elabConBind] at h
    split at h
    · rename_i τs VE' h1 h2
      simp only [Option.some.injEq] at h
      subst h
      have hs := RTypes.elabTyList_sim f hfix C' A' hU tys τs (fun lc _ => hL lc) h1
      rw [closVE_modify]
      simp only [gConBind, hs]
      refine RelL.modify ?_ (gConBind_rel hL hU X τ rest VE' h2)
      simp only [closVE, FMap.mapV, List.map_cons, List.map_nil]
      refine RelL.single ?_
      rw [← mapTy_arrows]
      exact gok_con hg X _
    · cases h

theorem gDat_rel {Cte A : Ctx} (hL : ∀ lc, RTypes.LookSim f Cte A lc) (hU : RTypes.UEq Cte.U A.U)
    {names : String → Option TyName} : ∀ (d : Src.BDatBind) (VE' : ValEnv) (TE' : TyEnv),
    elabDatBind Cte names d = some (VE', TE') →
    (∀ x ∈ d, ∀ t, names x.1 = some t → f t = ⟨RTypes.Did, t.arity⟩) → RelL ν (gDat A d) VE'
  | [], VE', TE', h, _ => by
    simp only [elabDatBind, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact RelL.nil
  | (c, ps, cb) :: rest, VE', TE', h, hn => by
    simp only [elabDatBind] at h
    split at h
    · cases h
    · rename_i t ht
      split at h
      · rename_i τs VE'' TE'' h1 h2
        split at h
        · rename_i VEc h3
          split at h
          · rename_i hc
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hU' := hU.plusU (seqVars ps (conBindExtNames cb))
            have hL' : ∀ lc, RTypes.LookSim f (Cte.plusU (seqVars ps (conBindExtNames cb)))
                (A.plusU (seqVars ps (conBindExtNames cb))) lc := fun lc => RTypes.lookSim_plusU _ _ (hL lc)
            have hs := RTypes.elabTyList_sim f hfix _ _ hU' (ps.map .tyvar) τs (fun lc _ => hL' lc) h1
            have hft : f t = ⟨RTypes.Did, t.arity⟩ := hn (c, ps, cb) List.mem_cons_self t ht
            have hmap : RTypes.mapTy f (.con τs t) = .con (RTypes.mapTys f τs) ⟨RTypes.Did, ps.length⟩ := by
              simp only [RTypes.mapTy, hft, hc.2.1]
            simp only [gDat, hs, Option.map_some]
            rw [← hmap]
            exact RelL.modify (gConBind_rel hfix hg hL' hU' _ _ cb VEc h3)
              (gDat_rel hL hU rest VE'' TE'' h2 (fun x hx => hn x (List.mem_cons_of_mem _ hx)))
          · cases h
        · cases h
      · cases h

end cons

theorem lookupAll_mapRow (f : TyName → TyName) (ρ : Row) : ∀ ls : List Lab,
    Row.lookupAll (RTypes.mapRow f ρ) ls = (Row.lookupAll ρ ls).map (RTypes.mapTys f)
  | [] => rfl
  | l :: ls => by
    have hl : Row.lookup (RTypes.mapRow f ρ) l = (Row.lookup ρ l).map (RTypes.mapTy f) := by
      simp only [Row.lookup, RTypes.mapRow_eq]; exact find?_map_val _ l ρ
    simp only [Row.lookupAll, hl, lookupAll_mapRow f ρ ls]
    cases Row.lookup ρ l <;> cases Row.lookupAll ρ ls <;> rfl

theorem alias_rel {f : TyName → TyName} (hfix : RTypes.FixesBuiltins f) (hg : ∀ t, gN (f t) = gN t)
    {Cte A : Ctx} (hL : ∀ lc, RTypes.LookSim f Cte A lc) (hU : RTypes.UEq Cte.U A.U) (tb : Src.BTypBind)
    {VE1 : ValEnv} {TE1 : TyEnv} (h : elabTypBind Cte tb = some (VE1, TE1)) : RelL ν (aliasL A tb) VE1 := by
  unfold elabTypBind at h
  cases he : elabTy (Cte.plusU (seqVars tb.params (bTyExtNames tb.t))) tb.t with
  | none => rw [he] at h; cases h
  | some τ =>
    rw [he] at h
    simp only at h
    have hs := RTypes.elabTy_sim f hfix _ (A.plusU (seqVars tb.params (bTyExtNames tb.t)))
      (hU.plusU _) tb.t τ (fun lc _ => RTypes.lookSim_plusU _ _ (hL lc)) he
    unfold aliasL
    cases hl : smlabs tb.t with
    | none =>
      rw [hl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact RelL.nil
    | some ls =>
      rw [hl] at h
      simp only at h
      match τ, h, hs with
      | .record ρ none, h, hs =>
        simp only at h
        cases hτs : Row.lookupAll ρ ls with
        | none => rw [hτs] at h; cases h
        | some τs =>
          rw [hτs] at h
          simp only at h
          split at h
          · rename_i hlen
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            simp only [hs, RTypes.mapTy, lookupAll_mapRow, hτs, Option.map_some]
            have hlen' : (RTypes.mapRow f ρ).length = ls.length := by
              rw [RTypes.mapRow_eq, List.length_map]; exact hlen
            simp only [hlen', ite_true, closVE, FMap.mapV, List.map_cons, List.map_nil]
            refine RelL.single ?_
            have e : arrows (RTypes.mapTys f τs) (.record (RTypes.mapRow f ρ) none) =
                RTypes.mapTy f (arrows τs (.record ρ none)) := by
              rw [mapTy_arrows]; rfl
            rw [e]
            exact gok_con hg _ _
          · cases h
      | .record _ (some _), h, _ => cases h
      | .var _, h, _ => cases h
      | .fn _ _, h, _ => cases h
      | .con _ _, h, _ => cases h

theorem aliases_rel {f : TyName → TyName} (hfix : RTypes.FixesBuiltins f) (hg : ∀ t, gN (f t) = gN t)
    {Cte A : Ctx} (hL : ∀ lc, RTypes.LookSim f Cte A lc) (hU : RTypes.UEq Cte.U A.U) :
    ∀ (tbs : List Src.BTypBind) (VEs : List ValEnv) (TEs : List TyEnv), elabTypBinds Cte tbs = some (VEs, TEs) →
    RelLs ν (tbs.map (aliasL A)) VEs
  | [], VEs, TEs, h => by
    simp only [elabTypBinds, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; trivial
  | tb :: tbs, VEs, TEs, h => by
    simp only [elabTypBinds] at h
    split at h
    · rename_i VE1 TE1 VEs' TEs' h1 h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨alias_rel hfix hg hL hU tb h1, aliases_rel hfix hg hL hU tbs VEs' TEs' h2⟩
    · cases h

theorem keys_typBindsTE {C : Ctx} : ∀ (tbs : List Src.BTypBind) (VEs : List ValEnv) (TEs : List TyEnv),
    elabTypBinds C tbs = some (VEs, TEs) → ∀ TE ∈ TEs, ∀ x ∈ TE.keys, x ∈ tbs.map (·.c)
  | [], VEs, TEs, h, TE, hTE, x, _ => by
    simp only [elabTypBinds, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; cases hTE
  | tb :: tbs, VEs, TEs, h, TE, hTE, x, hx => by
    simp only [elabTypBinds] at h
    split at h
    · rename_i VE1 TE1 VEs' TEs' h1 h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rcases List.mem_cons.mp hTE with e | hTE
      · subst e
        obtain ⟨τ, X, _, e2⟩ := RTypes.typBind_shape C tb VE1 TE h1
        subst e2
        simp [FMap.keys] at hx; subst hx; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (keys_typBindsTE tbs VEs' TEs' h2 TE hTE x hx)
    · cases h

/-- The values a type declaration binds stand for the generator's entries. -/
theorem gTypes_rel {B : SBasis} {f : TyName → TyName} (hcol : RTypes.Col B f) (hg : ∀ t, gN (f t) = gN t)
    {A : Ctx} (hAU : A.U = []) {C : Ctx} {TE : TyEnv} {VE : ValEnv}
    (hL : ∀ lc, RTypes.LookSim f (C.oplusTE TE) A lc) (hCU : C.U = []) (hTC : ∀ t, t ∈ B.T → t ∈ C.T)
    {db : Option Src.BDatBind} {tbs : List Src.BTypBind}
    (hnd : (((db.getD []).map (·.1)) ++ tbs.map (·.c)).Nodup)
    (h : checkTypes C TE VE db tbs = true) : RelL ν (gTypes A db tbs) VE := by
  have hU : RTypes.UEq (C.oplusTE TE).U A.U := by
    simp only [Ctx.oplusTE, hCU, hAU]; exact RTypes.uEq_refl _
  have hweak : ∀ (VEs : List ValEnv) (TEs : List TyEnv), elabTypBinds (C.oplusTE TE) tbs = some (VEs, TEs) →
      RelL ν (FMap.plusAll (tbs.map (aliasL A))) (FMap.plusAll VEs) :=
    fun VEs TEs hb => RelL.plusAll (aliases_rel hcol.builtins hg hL hU tbs VEs TEs hb)
  have hfx := checkTypes_fix h
  unfold checkTypesFix at hfx
  cases db with
  | none =>
    simp only at hfx
    split at hfx
    · rename_i VEs TEs hb
      simp only [decide_eq_true_eq] at hfx
      obtain ⟨_, _, rfl⟩ := hfx
      exact hweak VEs TEs hb
    · cases hfx
  | some d =>
    simp only at hfx
    split at hfx
    · rename_i VE' TE' VEs TEs hd hb
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hfx
      obtain ⟨hnew, _, hTE, rfl⟩ := hfx
      have hnd' := List.nodup_append.mp (by simpa using hnd : ((d.map (·.1)) ++ tbs.map (·.c)).Nodup)
      have hfacts := RTypes.datBind_facts _ _ d VE' TE' hd hnd'.1
      have hn : ∀ x ∈ d, ∀ t, namesOf TE x.1 = some t → f t = ⟨RTypes.Did, t.arity⟩ := by
        intro x hx t ht
        obtain ⟨t', VEt, ht1, _, _⟩ := hfacts.2 x hx
        have hxa : x.1 ∉ tbs.map (·.c) := fun hm => hnd'.2.2 x.1 (List.mem_map.mpr ⟨x, hx, rfl⟩) x.1 hm rfl
        have hp0 : FMap.find? (FMap.plusAll TEs) x.1 = none := by
          cases hf : FMap.find? (FMap.plusAll TEs) x.1 with
          | none => rfl
          | some v =>
            exfalso
            have hk : x.1 ∈ (FMap.plusAll TEs).keys := (FMap.find?_isSome_iff _ _).mp (by rw [hf]; rfl)
            rcases mem_keys_plusAll TEs [] hk with h' | ⟨L, hL', h'⟩
            · simp [FMap.keys] at h'
            · exact hxa (keys_typBindsTE tbs VEs TEs hb L hL' x.1 h')
        have hfind : FMap.find? TE x.1 = some (t'.toFcn, VEt) := by
          rw [← hTE, FMap.find?_modify, hp0, Option.none_or, ht1]
        simp only [namesOf, hfind, Option.bind_some, RTypes.name?_toFcn, Option.some.injEq] at ht
        subst ht
        have htT : t' ∉ C.T := namesNewB_spec C.T TE' hnew _ (RTypes.find?_mem_vals _ _ TE' ht1) t'
          (RTypes.name?_toFcn t')
        exact hcol.out t' (fun hb' => htT (hTC t' hb'))
      exact RelL.modify (gDat_rel hcol.builtins hg hL hU d VE' TE' hd hn) (hweak VEs TEs hb)
    · cases hfx

/-- After a type declaration, the abstract context simulates the derivation's. -/
theorem types_look {B : SBasis} {f : TyName → TyName} (hcol : RTypes.Col B f) {A : Ctx} (hAU : A.U = [])
    {C : Ctx} (hI : RTypes.Inv B f A C) {TE : TyEnv} {VE : ValEnv} {db : Option Src.BDatBind}
    {tbs : List Src.BTypBind} (hp : RTypes.preserves A (.types db tbs) = true)
    (h : checkTypes C TE VE db tbs = true) :
    (∀ lc, RTypes.LookSim f (C.oplusTE TE) A lc) ∧ (((db.getD []).map (·.1)) ++ tbs.map (·.c)).Nodup := by
  simp only [RTypes.preserves, RTypes.typesNodeOK, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨⟨hnd, hcu⟩, hord⟩, hall⟩ := hp
  have hl := RTypes.types_leaf hcol hAU (post := []) hI (by simpa using hnd) hcu (by simpa using hord)
    (by simp [hall]) h
  exact ⟨hl.2.2.1, by simpa using hnd⟩

/-! ## Local types named like imported ones (ruling A98) -/

/-- The invariant of a context against the abstract context, except at the unqualified names N
    (the module's own types, which the abstract context gives their local meaning). -/
structure InvW (B : SBasis) (f : TyName → TyName) (A C : Ctx) (N : List String) : Prop where
  look : ∀ lc : LongId, (lc.qual.isSome = true ∨ lc.id ∉ N) → RTypes.LookSim f C A lc
  U : C.U = []
  T : ∀ t, t ∈ B.T → t ∈ C.T

theorem inv_base_w (B : SBasis) (f : TyName → TyName) (C0 : Ctx) (L : TyEnv) (N : List String) (hU : C0.U = [])
    (hT : C0.T = B.T) (hN : ∀ c ∈ L.keys, c ∈ N) : InvW B f (RTypes.absCtx f C0 L) C0 N := by
  refine ⟨?_, hU, fun t ht => hT ▸ ht⟩
  rintro ⟨q, c⟩ hq θ VE hl
  cases q with
  | none =>
    have hcN : c ∉ N := by simpa using hq
    rw [RTypes.lookupTy_none] at hl
    refine ⟨[], ?_⟩
    simp only [RTypes.absCtx, Ctx.lookupTy, Env.lookupTy, FMap.find?_modify]
    have hn : FMap.find? L c = none := by
      cases hc : FMap.find? L c with
      | none => rfl
      | some v =>
        exfalso
        exact hcN (hN c ((FMap.find?_isSome_iff L c).mp (by rw [hc]; rfl)))
    rw [hn]
    simp only [RTypes.baseTE, Option.none_or]
    rw [RTypes.find?_map_snd (RTypes.mapStr f) c C0.E.TE, hl]
    rfl
  | some m =>
    rw [RTypes.lookupTy_some] at hl
    refine ⟨[], ?_⟩
    simp only [RTypes.absCtx, Ctx.lookupTy, Env.lookupTy, RTypes.baseQE]
    rw [RTypes.find?_map_snd (fun I : IEnv => (⟨I.TE.map (fun q => (q.1, RTypes.mapStr f q.2)), []⟩ : IEnv)) m C0.E.QE]
    cases hm : FMap.find? C0.E.QE m with
    | none => rw [hm] at hl; cases hl
    | some I =>
      rw [hm] at hl
      simp only [Option.bind_some, Option.map_some] at hl ⊢
      rw [RTypes.find?_map_snd (RTypes.mapStr f) c I.TE, hl]
      rfl

section shadow
set_option linter.unusedSectionVars false
variable {B : SBasis} {f : TyName → TyName} (hcol : RTypes.Col B f) {A : Ctx} (hAU : A.U = [])
include hcol hAU

theorem leaf_core_w {C : Ctx} {N : List String} (hI : InvW B f A C N) {TE TE' : TyEnv} {seg post : List Src.BTypBind}
    {VEs : List ValEnv} {TEs : List TyEnv}
    (hb : elabTypBinds (C.oplusTE TE) seg = some (VEs, TEs))
    (hfind : ∀ c, FMap.find? TE c = (FMap.find? (FMap.plusAll TEs) c).or (FMap.find? TE' c))
    (hTE' : ∀ c θ VEc, FMap.find? TE' c = some (θ, VEc) →
      ∃ VE'', A.lookupTy ⟨none, c⟩ = some (RTypes.mapFcn f θ, VE''))
    (hfall : ∀ c, c ∉ seg.map (·.c) → FMap.find? TE' c = none → c ∉ N)
    (hnd : (seg.map (·.c)).Nodup) (hord : RTypes.aliasOrderB (seg ++ post) = true)
    (hH : RTypes.aliasesRefuted A (seg ++ post) = true ∨ RTypes.aliasesAllOK A (seg ++ post) = true) :
    ∀ lc, RTypes.LookSim f (C.oplusTE TE) A lc := by
  have hfold := RTypes.typBinds_fold (C.oplusTE TE) seg VEs TEs [] hb hnd
  refine (RTypes.aliases_inner hcol hAU (Cte := C.oplusTE TE) hI.U post seg ?_ ?_ hord hH).2.2
  · rintro ⟨q, c⟩ hlc
    cases q with
    | some m =>
      intro θ VE h
      rw [RTypes.lookupTy_oplusTE_some] at h
      exact hI.look _ (.inl rfl) θ VE h
    | none =>
      have hn : c ∉ seg.map (·.c) := by
        rcases hlc with h | h
        · cases h
        · exact h
      intro θ VE h
      rw [RTypes.lookupTy_oplusTE_none, hfind] at h
      have hp : FMap.find? (FMap.plusAll TEs) c = none := by
        unfold FMap.plusAll; rw [hfold.1 c hn]; rfl
      rw [hp, Option.none_or] at h
      cases h' : FMap.find? TE' c with
      | some s =>
        rw [h'] at h
        simp only [Option.some_or, Option.some.injEq] at h
        subst h
        exact hTE' c θ VE h'
      | none =>
        rw [h', Option.none_or] at h
        exact hI.look _ (.inr (hfall c hn h')) θ VE h
  · intro tb htb
    obtain ⟨τ, X, hτ, hf⟩ := hfold.2 tb htb
    refine ⟨τ, X, hτ, ?_⟩
    rw [RTypes.lookupTy_oplusTE_none, hfind]
    unfold FMap.plusAll
    rw [hf]
    rfl

/-- `types_look` when the context gives the local names their imported meaning. -/
theorem types_look_w {C : Ctx} {TE : TyEnv} {VE : ValEnv} {db : Option Src.BDatBind} {tbs : List Src.BTypBind}
    (hI : InvW B f A C (((db.getD []).map (·.1)) ++ tbs.map (·.c)))
    (hp : RTypes.preserves A (.types db tbs) = true) (h : checkTypes C TE VE db tbs = true) :
    (∀ lc, RTypes.LookSim f (C.oplusTE TE) A lc) ∧ (((db.getD []).map (·.1)) ++ tbs.map (·.c)).Nodup := by
  simp only [RTypes.preserves, RTypes.typesNodeOK, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨⟨hnd, hcu⟩, hord⟩, hall⟩ := hp
  have hnd' := List.nodup_append.mp hnd
  refine ⟨?_, hnd⟩
  replace h := checkTypes_fix h
  unfold checkTypesFix at h
  cases db with
  | none =>
    simp only at h
    split at h
    · rename_i VEs TEs hb
      simp only [decide_eq_true_eq] at h
      obtain ⟨_, rfl, _⟩ := h
      exact leaf_core_w hcol hAU (post := []) (TE' := []) hI hb (fun c => by simp [FMap.find?])
        (fun c θ VEc h => by cases h) (fun c hc _ => by simpa using hc) hnd'.2.1 (by simpa using hord)
        (by simp [hall])
    · cases h
  | some d =>
    simp only at h
    split at h
    · rename_i VE' TE' VEs TEs hd hb
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hnew, _, hTE, _⟩ := h
      have hdn : (d.map (·.1)).Nodup := by simpa using hnd'.1
      have hfacts := RTypes.datBind_facts _ _ d VE' TE' hd hdn
      have hTE' : ∀ c θ VEc, FMap.find? TE' c = some (θ, VEc) →
          ∃ VE'', A.lookupTy ⟨none, c⟩ = some (RTypes.mapFcn f θ, VE'') := by
        intro c θ VEc hc
        have hcm : c ∈ d.map (·.1) := by
          by_cases hn : c ∈ d.map (·.1)
          · exact hn
          · rw [hfacts.1 c hn] at hc; cases hc
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hcm
        obtain ⟨t, VEt, ht1, ht2, _⟩ := hfacts.2 x hx
        rw [ht1] at hc
        simp only [Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        have htT : t ∉ C.T := namesNewB_spec C.T TE' hnew _ (RTypes.find?_mem_vals _ _ TE' ht1) t (RTypes.name?_toFcn t)
        have hft : f t = ⟨RTypes.Did, t.arity⟩ := hcol.out t (fun hb => htT (hI.T t hb))
        have hcx := List.all_eq_true.mp hcu x (by simpa using hx)
        simp only [decide_eq_true_eq] at hcx
        cases hA : A.lookupTy ⟨none, x.1⟩ with
        | none => rw [hA] at hcx; cases hcx
        | some s =>
          rw [hA] at hcx
          simp only [Option.map_some, Option.some.injEq] at hcx
          refine ⟨s.2, ?_⟩
          rw [RTypes.toFcn_map f t (by rw [hft]), hft, ht2, ← hcx]
      have hfind : ∀ c, FMap.find? TE c = (FMap.find? (FMap.plusAll TEs) c).or (FMap.find? TE' c) := by
        intro c; rw [← hTE, FMap.find?_modify]
      have hfall : ∀ c, c ∉ tbs.map (·.c) → FMap.find? TE' c = none →
          c ∉ ((some d).getD []).map (·.1) ++ tbs.map (·.c) := by
        intro c hc hn hm
        rcases List.mem_append.mp hm with hm | hm
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
          obtain ⟨t, VEt, ht1, _⟩ := hfacts.2 x (by simpa using hx)
          rw [hn] at ht1; cases ht1
        · exact hc hm
      exact leaf_core_w hcol hAU (post := []) hI hb hfind hTE' hfall hnd'.2.1 (by simpa using hord)
        (by simp [hall])
    · cases h

end shadow

theorem aliasesAbs_keys (f : TyName → TyName) (C0 : Ctx) : ∀ (L : TyEnv) (tbs : List Src.BTypBind),
    ∀ c ∈ (RTypes.aliasesAbs f C0 L tbs).keys, c ∈ L.keys ∨ c ∈ tbs.map (·.c)
  | L, [], c, hc => .inl hc
  | L, tb :: rest, c, hc => by
    simp only [RTypes.aliasesAbs] at hc
    split at hc
    · rcases aliasesAbs_keys f C0 _ rest c hc with h | h
      · simp only [FMap.keys, List.map_append, List.mem_append, List.map_cons, List.map_nil,
          List.mem_singleton] at h
        rcases h with h | rfl
        · exact .inl h
        · exact .inr List.mem_cons_self
      · exact .inr (List.mem_cons_of_mem _ h)
    · rcases aliasesAbs_keys f C0 L rest c hc with h | h
      · exact .inl h
      · exact .inr (List.mem_cons_of_mem _ h)

theorem localTE_keys (f : TyName → TyName) (C0 : Ctx) (body : Option Src.BTopDec) :
    ∀ c ∈ (RTypes.localTE f C0 body).keys,
      c ∈ (((RTypes.typesPhrase body).1.getD []).map (·.1)) ++ (RTypes.typesPhrase body).2.map (·.c) := by
  intro c hc
  unfold RTypes.localTE at hc
  rcases aliasesAbs_keys f C0 _ _ c hc with h | h
  · refine List.mem_append_left _ ?_
    cases hp : (RTypes.typesPhrase body).1 with
    | none => rw [hp] at h; simp [RTypes.customsAbs, FMap.keys] at h
    | some d =>
      rw [hp] at h
      simpa [RTypes.customsAbs, FMap.keys, List.map_map, Function.comp_def] using h
  · exact List.mem_append_right _ h

/-! ## Modules -/

section top
variable {B : SBasis} (hcol : RTypes.Col B (RTypes.fcol B.T)) (hg : ∀ t, gN (RTypes.fcol B.T t) = gN t)
  {A : Ctx} (hAU : A.U = [])
include hcol hg hAU

theorem gTop_ok : (a : ATopDec) → ∀ {C : Ctx} {Γ : GCtx} {p : Path} {E : Env} {PE : PortEnv}
    {L : FMap Var GInfo} {cs : List Con}, Γ.A = A → Sim ν (RTypes.fcol B.T) Γ C → RTypes.Inv B (RTypes.fcol B.T) A C →
    RTypes.preserves A a.erase = true → checkTopDec C a = some (E, PE) →
    gTop Γ p a.erase = some (L, cs) → (∀ q, ν (q.reverse ++ p) = rdTop a q) →
    Holds ν cs ∧ RelL ν L E.VE ∧ E.QE = []
  | .value VE vb, C, Γ, p, E, PE, L, cs, _, hS, _, _, h, hgt, hr => by
    simp only [checkTopDec] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨h1, h2⟩ := hc
      simp only [ATopDec.erase, gTop, Option.some.injEq, Prod.mk.injEq] at hgt
      obtain ⟨rfl, rfl⟩ := hgt
      have hrv := child 0 hr (fun q => rfl)
      have hR : RelL ν (gVBEnv Γ.A (0 :: p) vb.erase) VE :=
        h2 ▸ gVBEnv_rel vb (C := C.plusVE VE) (hS.ty.same (C' := C.plusVE VE) (fun _ => rfl)) h1 hrv
      have hc := gValBind_ok vb (Sim.plusVE hS hR) h1 hrv
      exact ⟨hc, RelL.close _ (groupSol_holds hc) hR, rfl⟩
    · cases h
  | .types TE VE db tbs, C, Γ, p, E, PE, L, cs, hA, _, hI, hp, h, hgt, _ => by
    simp only [ATopDec.erase] at hp
    simp only [checkTopDec] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [ATopDec.erase, gTop, Option.some.injEq, Prod.mk.injEq] at hgt
      obtain ⟨rfl, rfl⟩ := hgt
      rw [hA]
      obtain ⟨hL, hnd⟩ := types_look hcol hAU hI hp hc
      exact ⟨Holds.nil, gTypes_rel hcol hg hAU hL hI.U hI.T hnd hc, rfl⟩
    · cases h
  | .port x ty U, C, Γ, p, E, PE, L, cs, _, _, _, _, h, hgt, _ => by
    obtain ⟨_, _, s, PE', hr⟩ := RTypes.elabPort_shape h
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    simp only [ATopDec.erase, gTop, Option.some.injEq, Prod.mk.injEq] at hgt
    obtain ⟨rfl, rfl⟩ := hgt
    exact ⟨Holds.nil, RelL.single (g := .weak) (σ := s.1) (s := s.2) trivial, rfl⟩
  | .seq a1 a2, C, Γ, p, E, PE, L, cs, hA, hS, hI, hp, h, hgt, hr => by
    simp only [ATopDec.erase, RTypes.preserves, Bool.and_eq_true] at hp
    simp only [checkTopDec] at h
    cases h1 : checkTopDec C a1 with
    | none => rw [h1] at h; cases h
    | some r1 =>
      obtain ⟨E1, PE1⟩ := r1
      rw [h1] at h
      simp only at h
      cases h2 : checkTopDec (C.oplusE E1) a2 with
      | none => rw [h2] at h; cases h
      | some r2 =>
        obtain ⟨E2, PE2⟩ := r2
        rw [h2] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [ATopDec.erase, gTop] at hgt
        cases g1 : gTop Γ (0 :: p) a1.erase with
        | none => rw [g1] at hgt; cases hgt
        | some s1 =>
          obtain ⟨L1, c1⟩ := s1
          rw [g1] at hgt
          simp only at hgt
          cases g2 : gTop (Γ.add L1) (1 :: p) a2.erase with
          | none => rw [g2] at hgt; cases hgt
          | some s2 =>
            obtain ⟨L2, c2⟩ := s2
            rw [g2] at hgt
            simp only [Option.some.injEq, Prod.mk.injEq] at hgt
            obtain ⟨rfl, rfl⟩ := hgt
            obtain ⟨hc1, hR1, hQ1⟩ := gTop_ok a1 hA hS hI hp.1 h1 g1 (child 0 hr (fun q => rfl))
            have hI1 := RTypes.pres hcol hAU a1 C E1 PE1 hI hp.1 h1
            have hS1 : Sim ν (RTypes.fcol B.T) (Γ.add L1) (C.oplusE E1) :=
              Sim.oplusE hS hR1 hQ1 ⟨fun lc => hA ▸ hI1.look lc, hcol.builtins, hg⟩
            obtain ⟨hc2, hR2, hQ2⟩ := gTop_ok a2 (Γ := Γ.add L1) hA hS1 hI1 hp.2 h2 g2 (child 1 hr (fun q => rfl))
            refine ⟨Holds.append.mpr ⟨hc1, hc2⟩, RelL.append_modify hR1 hR2, ?_⟩
            simp [Env.plus, hQ1, hQ2, FMap.modify]

end top

theorem gN_fcol {B : SBasis} (h : T0.all (· ∈ B.T) = true) : ∀ t, gN (RTypes.fcol B.T t) = gN t := by
  intro t
  unfold RTypes.fcol
  by_cases ht : t ∈ B.T
  · simp [ht]
  · have h0 : t ∉ T0 := fun hm => ht (by have := List.all_eq_true.mp h t hm; simpa using this)
    have hD : (⟨RTypes.Did, t.arity⟩ : TyName) ∉ T0 := by
      intro hm; simp [T0, RTypes.Did, tInt, tFloat, tChar, tString, tUnit, tList, tTuple2, tTuple3, tBool, tOrder,
        tNever, tMaybe, tResult, tArray, tBytes, tValue, tCmd, tSub, tTask, tProcessId, tProgram, tNode] at hm
    simp only [ht, ite_false, gN, h0, hD]

/-- A body that starts with its type declarations, whose local names may be imported ones: the
    declarations give the abstract context's meaning to every name after them. -/
theorem gTop_shadow {B : SBasis} {C0 : Ctx} (hcol : RTypes.Col B (RTypes.fcol B.T))
    (hg : ∀ t, gN (RTypes.fcol B.T t) = gN t) (hU : C0.U = []) (hTT : C0.T = B.T) {d : Src.BTopDec}
    (hst : startsTypes d = true) (hpres : RTypes.preserves (absOf B C0 d) d = true) (ad : ATopDec)
    (had : ad.erase = d) {E : Env} {PE : PortEnv} (hchk : checkTopDec C0 ad = some (E, PE)) {L : FMap Var GInfo}
    {cs : List Con} (hgt : gTop ⟨[], C0, absOf B C0 d⟩ [] d = some (L, cs)) :
    Holds (fun r => rdTop ad r.reverse) cs := by
  have hAU : (absOf B C0 d).U = [] := rfl
  have hr0 : ∀ q, (fun r => rdTop ad r.reverse) (q.reverse ++ []) = rdTop ad q := fun q => by simp
  have hIW := inv_base_w B (RTypes.fcol B.T) C0 (RTypes.localTE (RTypes.fcol B.T) C0 (some d)) _ hU hTT
    (localTE_keys _ C0 (some d))
  cases ad with
  | types TE VE db tbs =>
    simp only [ATopDec.erase] at had
    subst had
    simp only [gTop, Option.some.injEq, Prod.mk.injEq] at hgt
    obtain ⟨_, rfl⟩ := hgt
    exact Holds.nil
  | seq a1 a2 =>
    cases a1 with
    | types TE VE db tbs =>
      simp only [ATopDec.erase] at had
      subst had
      simp only [RTypes.preserves, Bool.and_eq_true] at hpres
      simp only [checkTopDec] at hchk
      by_cases hct : checkTypes C0 TE VE db tbs = true
      · simp only [hct, ite_true] at hchk
        cases h2 : checkTopDec (C0.oplusE ⟨[], TE, VE⟩) a2 with
        | none => rw [h2] at hchk; cases hchk
        | some r2 =>
          simp only [gTop] at hgt
          cases g2 : gTop (GCtx.add ⟨[], C0, absOf B C0 (.seq (.types db tbs) a2.erase)⟩
              (gTypes (absOf B C0 (.seq (.types db tbs) a2.erase)) db tbs)) [1] a2.erase with
          | none => rw [g2] at hgt; cases hgt
          | some s2 =>
            obtain ⟨L2, c2⟩ := s2
            rw [g2] at hgt
            simp only [Option.some.injEq, Prod.mk.injEq] at hgt
            obtain ⟨rfl, rfl⟩ := hgt
            have hIW' := hIW
            simp only [RTypes.typesPhrase] at hIW'
            obtain ⟨hL, hnd⟩ := types_look_w hcol hAU hIW'
              (by simp only [RTypes.preserves, Bool.and_eq_true]; exact hpres.1) hct
            have hR := gTypes_rel (ν := fun r => rdTop (.seq (.types TE VE db tbs) a2) r.reverse) hcol hg hAU hL hU
              (fun t ht => hTT ▸ ht) hnd hct
            have hI1 : RTypes.Inv B (RTypes.fcol B.T) (absOf B C0 (.seq (.types db tbs) a2.erase))
                (C0.oplusE ⟨[], TE, VE⟩) :=
              ⟨fun lc => RTypes.lookSim_of_same (RTypes.sameTy_oplusE_types C0 TE VE) (hL lc), hU,
                fun t ht => RTypes.T_oplusE C0 _ t (hTT ▸ ht)⟩
            have hS1 := Sim.oplusEV (Γ := ⟨[], C0, absOf B C0 (.seq (.types db tbs) a2.erase)⟩)
              (valSim_base C0 _) hR rfl ⟨hI1.look, hcol.builtins, hg⟩
            exact (gTop_ok hcol hg hAU a2 rfl hS1 hI1 hpres.2 h2 g2
              (fun q => by simp [rdTop])).1
      · simp only [hct] at hchk; cases hchk
    | value _ _ | port _ _ _ | seq _ _ =>
      simp only [ATopDec.erase] at had
      subst had
      simp [startsTypes] at hst
  | value _ _ | port _ _ _ =>
    simp only [ATopDec.erase] at had
    subst had
    simp [startsTypes] at hst

/-- Completeness of generation: every derivation of the module solves the constraints. -/
theorem coreGen_complete {B : SBasis} {m : BModule} {cs : List Con} (h : coreGen B m = some cs)
    (a : AModule) (he : a.erase = m) (hc : checkModule B a = true) : ∃ ν, Holds ν cs := by
  unfold coreGen at h
  split at h
  · rename_i C0 d hC hd
    split at h
    · rename_i hok
      simp only [typesOK, Bool.and_eq_true, Bool.or_eq_true] at hok
      obtain ⟨⟨⟨hfix, hT0⟩, hun⟩, hpres⟩ := hok
      obtain ⟨⟨L, cs'⟩, hgt, e⟩ := Option.map_eq_some_iff.mp h
      simp only at e
      subst e
      have hC' : importCtx B a.imports = some C0 := by rw [RTypes.imports_erase he]; exact hC
      unfold checkModule at hc
      rw [AModule.result_of_ctx hC'] at hc
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hc
      obtain ⟨PE', hchk⟩ := RTypes.resultIn_check (B' := r.1) (E := r.2) hr
      obtain ⟨ad, hb, had⟩ := RTypes.body_erase he hd
      rw [hb] at hchk
      simp only [checkTopDecOpt] at hchk
      obtain ⟨hU, hTT⟩ := RTypes.importCtx_UT hC
      have hcol := RTypes.col_fcol B hfix
      have hg := gN_fcol hT0
      rcases hun with hun | hst
      · have hI := RTypes.inv_base B (RTypes.fcol B.T) C0 _ hU hTT hun
        have hS : Sim (fun r => rdTop ad r.reverse) (RTypes.fcol B.T) ⟨[], C0, absOf B C0 d⟩ C0 :=
          Sim.base C0 _ ⟨hI.look, hcol.builtins, hg⟩
        exact ⟨fun r => rdTop ad r.reverse, (gTop_ok hcol hg (A := absOf B C0 d) rfl ad rfl hS hI
          (by rw [had]; exact hpres) hchk (by rw [had]; exact hgt) (fun q => by simp)).1⟩
      · exact ⟨_, gTop_shadow hcol hg hU hTT hst hpres ad had hchk hgt⟩
    · cases h
  · cases h
/-- If unification of the first module's constraints fails, the module has no derivation. -/
theorem noDeriv_of_core {B : SBasis} {m : BModule} {cs : List Con} (h : coreGen B m = some cs)
    (hu : unifyCs cs = .fail) : NoDeriv B m := by
  intro a he
  cases hc : checkModule B a with
  | false => rfl
  | true =>
    obtain ⟨ν, hh⟩ := coreGen_complete h a he hc
    exact absurd hh (unifyCs_fail hu ν)

end StandardElm.Stat.Complete

namespace StandardElm.Stat
open StandardElm.Stat.Complete

/-- The refusal theorem of milestone (a): unconditional (no principality hypothesis). -/
theorem not_legal_of_coreRefutes {B : SBasis} {sp : Src.SProgram} (h : coreRefutes B sp = true) :
    ¬ LegalProgram B sp := by
  unfold coreRefutes at h
  split at h
  · rename_i m rest hms
    split at h
    · rename_i cs hg
      have hu : unifyCs cs = .fail := by
        simp only [Bool.and_eq_true] at h
        revert h; cases unifyCs cs <;> simp [UOutcome.isFail]
      exact not_legal_of_noDeriv hms (noDeriv_of_core hg hu)
    · cases h
  · cases h

end StandardElm.Stat
